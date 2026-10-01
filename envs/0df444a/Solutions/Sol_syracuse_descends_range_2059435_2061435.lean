-- Prove2me | solution 1 for syracuse_descends_range_2059435_2061435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:35.680053+00:00
-- url     : https://prove2.me/submissions/d5dbf397-1364-4005-ae38-a2f22ad271b5

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

theorem B2316865 : Blo 2059435 2316865 := bbase (se 2 (by rfl) ⟨868824, by rfl⟩ : syracuseStep 2316865 = 1737649) (by norm_num)
theorem B3089153 : Blo 2059435 3089153 := bstep (se 2 (by rfl) ⟨1158432, by rfl⟩ : syracuseStep 3089153 = 2316865) B2316865
theorem B2059435 : Blo 2059435 2059435 := bstep (se 1 (by rfl) ⟨1544576, by rfl⟩ : syracuseStep 2059435 = 3089153) B3089153
theorem B5212957 : Blo 2059435 5212957 := bbase (se 3 (by rfl) ⟨977429, by rfl⟩ : syracuseStep 5212957 = 1954859) (by norm_num)
theorem B6950609 : Blo 2059435 6950609 := bstep (se 2 (by rfl) ⟨2606478, by rfl⟩ : syracuseStep 6950609 = 5212957) B5212957
theorem B4633739 : Blo 2059435 4633739 := bstep (se 1 (by rfl) ⟨3475304, by rfl⟩ : syracuseStep 4633739 = 6950609) B6950609
theorem B3089159 : Blo 2059435 3089159 := bstep (se 1 (by rfl) ⟨2316869, by rfl⟩ : syracuseStep 3089159 = 4633739) B4633739
theorem B2059439 : Blo 2059435 2059439 := bstep (se 1 (by rfl) ⟨1544579, by rfl⟩ : syracuseStep 2059439 = 3089159) B3089159
theorem B3089165 : Blo 2059435 3089165 := bbase (se 3 (by rfl) ⟨579218, by rfl⟩ : syracuseStep 3089165 = 1158437) (by norm_num)
theorem B2059443 : Blo 2059435 2059443 := bstep (se 1 (by rfl) ⟨1544582, by rfl⟩ : syracuseStep 2059443 = 3089165) B3089165
theorem B4633757 : Blo 2059435 4633757 := bbase (se 3 (by rfl) ⟨868829, by rfl⟩ : syracuseStep 4633757 = 1737659) (by norm_num)
theorem B3089171 : Blo 2059435 3089171 := bstep (se 1 (by rfl) ⟨2316878, by rfl⟩ : syracuseStep 3089171 = 4633757) B4633757
theorem B2059447 : Blo 2059435 2059447 := bstep (se 1 (by rfl) ⟨1544585, by rfl⟩ : syracuseStep 2059447 = 3089171) B3089171
theorem B3475325 : Blo 2059435 3475325 := bbase (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) (by norm_num)
theorem B2316883 : Blo 2059435 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B3089177 : Blo 2059435 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B2059451 : Blo 2059435 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B6597701 : Blo 2059435 6597701 := bbase (se 4 (by rfl) ⟨618534, by rfl⟩ : syracuseStep 6597701 = 1237069) (by norm_num)
theorem B4398467 : Blo 2059435 4398467 := bstep (se 1 (by rfl) ⟨3298850, by rfl⟩ : syracuseStep 4398467 = 6597701) B6597701
theorem B11729245 : Blo 2059435 11729245 := bstep (se 3 (by rfl) ⟨2199233, by rfl⟩ : syracuseStep 11729245 = 4398467) B4398467
theorem B15638993 : Blo 2059435 15638993 := bstep (se 2 (by rfl) ⟨5864622, by rfl⟩ : syracuseStep 15638993 = 11729245) B11729245
theorem B10425995 : Blo 2059435 10425995 := bstep (se 1 (by rfl) ⟨7819496, by rfl⟩ : syracuseStep 10425995 = 15638993) B15638993
theorem B6950663 : Blo 2059435 6950663 := bstep (se 1 (by rfl) ⟨5212997, by rfl⟩ : syracuseStep 6950663 = 10425995) B10425995
theorem B4633775 : Blo 2059435 4633775 := bstep (se 1 (by rfl) ⟨3475331, by rfl⟩ : syracuseStep 4633775 = 6950663) B6950663
theorem B3089183 : Blo 2059435 3089183 := bstep (se 1 (by rfl) ⟨2316887, by rfl⟩ : syracuseStep 3089183 = 4633775) B4633775
theorem B2059455 : Blo 2059435 2059455 := bstep (se 1 (by rfl) ⟨1544591, by rfl⟩ : syracuseStep 2059455 = 3089183) B3089183
theorem B3089189 : Blo 2059435 3089189 := bbase (se 4 (by rfl) ⟨289611, by rfl⟩ : syracuseStep 3089189 = 579223) (by norm_num)
theorem B2059459 : Blo 2059435 2059459 := bstep (se 1 (by rfl) ⟨1544594, by rfl⟩ : syracuseStep 2059459 = 3089189) B3089189
theorem B2606509 : Blo 2059435 2606509 := bbase (se 3 (by rfl) ⟨488720, by rfl⟩ : syracuseStep 2606509 = 977441) (by norm_num)
theorem B3475345 : Blo 2059435 3475345 := bstep (se 2 (by rfl) ⟨1303254, by rfl⟩ : syracuseStep 3475345 = 2606509) B2606509
theorem B4633793 : Blo 2059435 4633793 := bstep (se 2 (by rfl) ⟨1737672, by rfl⟩ : syracuseStep 4633793 = 3475345) B3475345
theorem B3089195 : Blo 2059435 3089195 := bstep (se 1 (by rfl) ⟨2316896, by rfl⟩ : syracuseStep 3089195 = 4633793) B4633793
theorem B2059463 : Blo 2059435 2059463 := bstep (se 1 (by rfl) ⟨1544597, by rfl⟩ : syracuseStep 2059463 = 3089195) B3089195
theorem B2316901 : Blo 2059435 2316901 := bbase (se 4 (by rfl) ⟨217209, by rfl⟩ : syracuseStep 2316901 = 434419) (by norm_num)
theorem B3089201 : Blo 2059435 3089201 := bstep (se 2 (by rfl) ⟨1158450, by rfl⟩ : syracuseStep 3089201 = 2316901) B2316901
theorem B2059467 : Blo 2059435 2059467 := bstep (se 1 (by rfl) ⟨1544600, by rfl⟩ : syracuseStep 2059467 = 3089201) B3089201
theorem B3298877 : Blo 2059435 3298877 := bbase (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) (by norm_num)
theorem B2199251 : Blo 2059435 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B5864669 : Blo 2059435 5864669 := bstep (se 3 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 5864669 = 2199251) B2199251
theorem B3909779 : Blo 2059435 3909779 := bstep (se 1 (by rfl) ⟨2932334, by rfl⟩ : syracuseStep 3909779 = 5864669) B5864669
theorem B2606519 : Blo 2059435 2606519 := bstep (se 1 (by rfl) ⟨1954889, by rfl⟩ : syracuseStep 2606519 = 3909779) B3909779
theorem B6950717 : Blo 2059435 6950717 := bstep (se 3 (by rfl) ⟨1303259, by rfl⟩ : syracuseStep 6950717 = 2606519) B2606519
theorem B4633811 : Blo 2059435 4633811 := bstep (se 1 (by rfl) ⟨3475358, by rfl⟩ : syracuseStep 4633811 = 6950717) B6950717
theorem B3089207 : Blo 2059435 3089207 := bstep (se 1 (by rfl) ⟨2316905, by rfl⟩ : syracuseStep 3089207 = 4633811) B4633811
theorem B2059471 : Blo 2059435 2059471 := bstep (se 1 (by rfl) ⟨1544603, by rfl⟩ : syracuseStep 2059471 = 3089207) B3089207
theorem B3089213 : Blo 2059435 3089213 := bbase (se 3 (by rfl) ⟨579227, by rfl⟩ : syracuseStep 3089213 = 1158455) (by norm_num)
theorem B2059475 : Blo 2059435 2059475 := bstep (se 1 (by rfl) ⟨1544606, by rfl⟩ : syracuseStep 2059475 = 3089213) B3089213
theorem B4633829 : Blo 2059435 4633829 := bbase (se 4 (by rfl) ⟨434421, by rfl⟩ : syracuseStep 4633829 = 868843) (by norm_num)
theorem B3089219 : Blo 2059435 3089219 := bstep (se 1 (by rfl) ⟨2316914, by rfl⟩ : syracuseStep 3089219 = 4633829) B4633829
theorem B2059479 : Blo 2059435 2059479 := bstep (se 1 (by rfl) ⟨1544609, by rfl⟩ : syracuseStep 2059479 = 3089219) B3089219
theorem B5213069 : Blo 2059435 5213069 := bbase (se 3 (by rfl) ⟨977450, by rfl⟩ : syracuseStep 5213069 = 1954901) (by norm_num)
theorem B3475379 : Blo 2059435 3475379 := bstep (se 1 (by rfl) ⟨2606534, by rfl⟩ : syracuseStep 3475379 = 5213069) B5213069
theorem B2316919 : Blo 2059435 2316919 := bstep (se 1 (by rfl) ⟨1737689, by rfl⟩ : syracuseStep 2316919 = 3475379) B3475379
theorem B3089225 : Blo 2059435 3089225 := bstep (se 2 (by rfl) ⟨1158459, by rfl⟩ : syracuseStep 3089225 = 2316919) B2316919
theorem B2059483 : Blo 2059435 2059483 := bstep (se 1 (by rfl) ⟨1544612, by rfl⟩ : syracuseStep 2059483 = 3089225) B3089225
theorem B2932357 : Blo 2059435 2932357 := bbase (se 4 (by rfl) ⟨274908, by rfl⟩ : syracuseStep 2932357 = 549817) (by norm_num)
theorem B3909809 : Blo 2059435 3909809 := bstep (se 2 (by rfl) ⟨1466178, by rfl⟩ : syracuseStep 3909809 = 2932357) B2932357
theorem B10426157 : Blo 2059435 10426157 := bstep (se 3 (by rfl) ⟨1954904, by rfl⟩ : syracuseStep 10426157 = 3909809) B3909809
theorem B6950771 : Blo 2059435 6950771 := bstep (se 1 (by rfl) ⟨5213078, by rfl⟩ : syracuseStep 6950771 = 10426157) B10426157
theorem B4633847 : Blo 2059435 4633847 := bstep (se 1 (by rfl) ⟨3475385, by rfl⟩ : syracuseStep 4633847 = 6950771) B6950771
theorem B3089231 : Blo 2059435 3089231 := bstep (se 1 (by rfl) ⟨2316923, by rfl⟩ : syracuseStep 3089231 = 4633847) B4633847
theorem B2059487 : Blo 2059435 2059487 := bstep (se 1 (by rfl) ⟨1544615, by rfl⟩ : syracuseStep 2059487 = 3089231) B3089231
theorem B3089237 : Blo 2059435 3089237 := bbase (se 9 (by rfl) ⟨9050, by rfl⟩ : syracuseStep 3089237 = 18101) (by norm_num)
theorem B2059491 : Blo 2059435 2059491 := bstep (se 1 (by rfl) ⟨1544618, by rfl⟩ : syracuseStep 2059491 = 3089237) B3089237
theorem B4948373 : Blo 2059435 4948373 := bbase (se 6 (by rfl) ⟨115977, by rfl⟩ : syracuseStep 4948373 = 231955) (by norm_num)
theorem B3298915 : Blo 2059435 3298915 := bstep (se 1 (by rfl) ⟨2474186, by rfl⟩ : syracuseStep 3298915 = 4948373) B4948373
theorem B4398553 : Blo 2059435 4398553 := bstep (se 2 (by rfl) ⟨1649457, by rfl⟩ : syracuseStep 4398553 = 3298915) B3298915
theorem B5864737 : Blo 2059435 5864737 := bstep (se 2 (by rfl) ⟨2199276, by rfl⟩ : syracuseStep 5864737 = 4398553) B4398553
theorem B7819649 : Blo 2059435 7819649 := bstep (se 2 (by rfl) ⟨2932368, by rfl⟩ : syracuseStep 7819649 = 5864737) B5864737
theorem B5213099 : Blo 2059435 5213099 := bstep (se 1 (by rfl) ⟨3909824, by rfl⟩ : syracuseStep 5213099 = 7819649) B7819649
theorem B3475399 : Blo 2059435 3475399 := bstep (se 1 (by rfl) ⟨2606549, by rfl⟩ : syracuseStep 3475399 = 5213099) B5213099
theorem B4633865 : Blo 2059435 4633865 := bstep (se 2 (by rfl) ⟨1737699, by rfl⟩ : syracuseStep 4633865 = 3475399) B3475399
theorem B3089243 : Blo 2059435 3089243 := bstep (se 1 (by rfl) ⟨2316932, by rfl⟩ : syracuseStep 3089243 = 4633865) B4633865
theorem B2059495 : Blo 2059435 2059495 := bstep (se 1 (by rfl) ⟨1544621, by rfl⟩ : syracuseStep 2059495 = 3089243) B3089243
theorem B2316937 : Blo 2059435 2316937 := bbase (se 2 (by rfl) ⟨868851, by rfl⟩ : syracuseStep 2316937 = 1737703) (by norm_num)
theorem B3089249 : Blo 2059435 3089249 := bstep (se 2 (by rfl) ⟨1158468, by rfl⟩ : syracuseStep 3089249 = 2316937) B2316937
theorem B2059499 : Blo 2059435 2059499 := bstep (se 1 (by rfl) ⟨1544624, by rfl⟩ : syracuseStep 2059499 = 3089249) B3089249
theorem B2542169 : Blo 2059435 2542169 := bbase (se 2 (by rfl) ⟨953313, by rfl⟩ : syracuseStep 2542169 = 1906627) (by norm_num)
theorem B6779117 : Blo 2059435 6779117 := bstep (se 3 (by rfl) ⟨1271084, by rfl⟩ : syracuseStep 6779117 = 2542169) B2542169
theorem B4519411 : Blo 2059435 4519411 := bstep (se 1 (by rfl) ⟨3389558, by rfl⟩ : syracuseStep 4519411 = 6779117) B6779117
theorem B24103525 : Blo 2059435 24103525 := bstep (se 4 (by rfl) ⟨2259705, by rfl⟩ : syracuseStep 24103525 = 4519411) B4519411
theorem B514208533 : Blo 2059435 514208533 := bstep (se 6 (by rfl) ⟨12051762, by rfl⟩ : syracuseStep 514208533 = 24103525) B24103525
theorem B685611377 : Blo 2059435 685611377 := bstep (se 2 (by rfl) ⟨257104266, by rfl⟩ : syracuseStep 685611377 = 514208533) B514208533
theorem B457074251 : Blo 2059435 457074251 := bstep (se 1 (by rfl) ⟨342805688, by rfl⟩ : syracuseStep 457074251 = 685611377) B685611377
theorem B304716167 : Blo 2059435 304716167 := bstep (se 1 (by rfl) ⟨228537125, by rfl⟩ : syracuseStep 304716167 = 457074251) B457074251
theorem B203144111 : Blo 2059435 203144111 := bstep (se 1 (by rfl) ⟨152358083, by rfl⟩ : syracuseStep 203144111 = 304716167) B304716167
theorem B135429407 : Blo 2059435 135429407 := bstep (se 1 (by rfl) ⟨101572055, by rfl⟩ : syracuseStep 135429407 = 203144111) B203144111
theorem B90286271 : Blo 2059435 90286271 := bstep (se 1 (by rfl) ⟨67714703, by rfl⟩ : syracuseStep 90286271 = 135429407) B135429407
theorem B60190847 : Blo 2059435 60190847 := bstep (se 1 (by rfl) ⟨45143135, by rfl⟩ : syracuseStep 60190847 = 90286271) B90286271
theorem B40127231 : Blo 2059435 40127231 := bstep (se 1 (by rfl) ⟨30095423, by rfl⟩ : syracuseStep 40127231 = 60190847) B60190847
theorem B26751487 : Blo 2059435 26751487 := bstep (se 1 (by rfl) ⟨20063615, by rfl⟩ : syracuseStep 26751487 = 40127231) B40127231
theorem B35668649 : Blo 2059435 35668649 := bstep (se 2 (by rfl) ⟨13375743, by rfl⟩ : syracuseStep 35668649 = 26751487) B26751487
theorem B23779099 : Blo 2059435 23779099 := bstep (se 1 (by rfl) ⟨17834324, by rfl⟩ : syracuseStep 23779099 = 35668649) B35668649
theorem B126821861 : Blo 2059435 126821861 := bstep (se 4 (by rfl) ⟨11889549, by rfl⟩ : syracuseStep 126821861 = 23779099) B23779099
theorem B84547907 : Blo 2059435 84547907 := bstep (se 1 (by rfl) ⟨63410930, by rfl⟩ : syracuseStep 84547907 = 126821861) B126821861
theorem B56365271 : Blo 2059435 56365271 := bstep (se 1 (by rfl) ⟨42273953, by rfl⟩ : syracuseStep 56365271 = 84547907) B84547907
theorem B37576847 : Blo 2059435 37576847 := bstep (se 1 (by rfl) ⟨28182635, by rfl⟩ : syracuseStep 37576847 = 56365271) B56365271
theorem B25051231 : Blo 2059435 25051231 := bstep (se 1 (by rfl) ⟨18788423, by rfl⟩ : syracuseStep 25051231 = 37576847) B37576847
theorem B33401641 : Blo 2059435 33401641 := bstep (se 2 (by rfl) ⟨12525615, by rfl⟩ : syracuseStep 33401641 = 25051231) B25051231
theorem B44535521 : Blo 2059435 44535521 := bstep (se 2 (by rfl) ⟨16700820, by rfl⟩ : syracuseStep 44535521 = 33401641) B33401641
theorem B29690347 : Blo 2059435 29690347 := bstep (se 1 (by rfl) ⟨22267760, by rfl⟩ : syracuseStep 29690347 = 44535521) B44535521
theorem B39587129 : Blo 2059435 39587129 := bstep (se 2 (by rfl) ⟨14845173, by rfl⟩ : syracuseStep 39587129 = 29690347) B29690347
theorem B26391419 : Blo 2059435 26391419 := bstep (se 1 (by rfl) ⟨19793564, by rfl⟩ : syracuseStep 26391419 = 39587129) B39587129
theorem B17594279 : Blo 2059435 17594279 := bstep (se 1 (by rfl) ⟨13195709, by rfl⟩ : syracuseStep 17594279 = 26391419) B26391419
theorem B11729519 : Blo 2059435 11729519 := bstep (se 1 (by rfl) ⟨8797139, by rfl⟩ : syracuseStep 11729519 = 17594279) B17594279
theorem B7819679 : Blo 2059435 7819679 := bstep (se 1 (by rfl) ⟨5864759, by rfl⟩ : syracuseStep 7819679 = 11729519) B11729519
theorem B5213119 : Blo 2059435 5213119 := bstep (se 1 (by rfl) ⟨3909839, by rfl⟩ : syracuseStep 5213119 = 7819679) B7819679
theorem B6950825 : Blo 2059435 6950825 := bstep (se 2 (by rfl) ⟨2606559, by rfl⟩ : syracuseStep 6950825 = 5213119) B5213119
theorem B4633883 : Blo 2059435 4633883 := bstep (se 1 (by rfl) ⟨3475412, by rfl⟩ : syracuseStep 4633883 = 6950825) B6950825
theorem B3089255 : Blo 2059435 3089255 := bstep (se 1 (by rfl) ⟨2316941, by rfl⟩ : syracuseStep 3089255 = 4633883) B4633883
theorem B2059503 : Blo 2059435 2059503 := bstep (se 1 (by rfl) ⟨1544627, by rfl⟩ : syracuseStep 2059503 = 3089255) B3089255
theorem B3089261 : Blo 2059435 3089261 := bbase (se 3 (by rfl) ⟨579236, by rfl⟩ : syracuseStep 3089261 = 1158473) (by norm_num)
theorem B2059507 : Blo 2059435 2059507 := bstep (se 1 (by rfl) ⟨1544630, by rfl⟩ : syracuseStep 2059507 = 3089261) B3089261
theorem B4633901 : Blo 2059435 4633901 := bbase (se 3 (by rfl) ⟨868856, by rfl⟩ : syracuseStep 4633901 = 1737713) (by norm_num)
theorem B3089267 : Blo 2059435 3089267 := bstep (se 1 (by rfl) ⟨2316950, by rfl⟩ : syracuseStep 3089267 = 4633901) B4633901
theorem B2059511 : Blo 2059435 2059511 := bstep (se 1 (by rfl) ⟨1544633, by rfl⟩ : syracuseStep 2059511 = 3089267) B3089267
theorem B13375829 : Blo 2059435 13375829 := bbase (se 10 (by rfl) ⟨19593, by rfl⟩ : syracuseStep 13375829 = 39187) (by norm_num)
theorem B8917219 : Blo 2059435 8917219 := bstep (se 1 (by rfl) ⟨6687914, by rfl⟩ : syracuseStep 8917219 = 13375829) B13375829
theorem B47558501 : Blo 2059435 47558501 := bstep (se 4 (by rfl) ⟨4458609, by rfl⟩ : syracuseStep 47558501 = 8917219) B8917219
theorem B31705667 : Blo 2059435 31705667 := bstep (se 1 (by rfl) ⟨23779250, by rfl⟩ : syracuseStep 31705667 = 47558501) B47558501
theorem B21137111 : Blo 2059435 21137111 := bstep (se 1 (by rfl) ⟨15852833, by rfl⟩ : syracuseStep 21137111 = 31705667) B31705667
theorem B14091407 : Blo 2059435 14091407 := bstep (se 1 (by rfl) ⟨10568555, by rfl⟩ : syracuseStep 14091407 = 21137111) B21137111
theorem B9394271 : Blo 2059435 9394271 := bstep (se 1 (by rfl) ⟨7045703, by rfl⟩ : syracuseStep 9394271 = 14091407) B14091407
theorem B6262847 : Blo 2059435 6262847 := bstep (se 1 (by rfl) ⟨4697135, by rfl⟩ : syracuseStep 6262847 = 9394271) B9394271
theorem B4175231 : Blo 2059435 4175231 := bstep (se 1 (by rfl) ⟨3131423, by rfl⟩ : syracuseStep 4175231 = 6262847) B6262847
theorem B11133949 : Blo 2059435 11133949 := bstep (se 3 (by rfl) ⟨2087615, by rfl⟩ : syracuseStep 11133949 = 4175231) B4175231
theorem B14845265 : Blo 2059435 14845265 := bstep (se 2 (by rfl) ⟨5566974, by rfl⟩ : syracuseStep 14845265 = 11133949) B11133949
theorem B9896843 : Blo 2059435 9896843 := bstep (se 1 (by rfl) ⟨7422632, by rfl⟩ : syracuseStep 9896843 = 14845265) B14845265
theorem B6597895 : Blo 2059435 6597895 := bstep (se 1 (by rfl) ⟨4948421, by rfl⟩ : syracuseStep 6597895 = 9896843) B9896843
theorem B8797193 : Blo 2059435 8797193 := bstep (se 2 (by rfl) ⟨3298947, by rfl⟩ : syracuseStep 8797193 = 6597895) B6597895
theorem B5864795 : Blo 2059435 5864795 := bstep (se 1 (by rfl) ⟨4398596, by rfl⟩ : syracuseStep 5864795 = 8797193) B8797193
theorem B3909863 : Blo 2059435 3909863 := bstep (se 1 (by rfl) ⟨2932397, by rfl⟩ : syracuseStep 3909863 = 5864795) B5864795
theorem B2606575 : Blo 2059435 2606575 := bstep (se 1 (by rfl) ⟨1954931, by rfl⟩ : syracuseStep 2606575 = 3909863) B3909863
theorem B3475433 : Blo 2059435 3475433 := bstep (se 2 (by rfl) ⟨1303287, by rfl⟩ : syracuseStep 3475433 = 2606575) B2606575
theorem B2316955 : Blo 2059435 2316955 := bstep (se 1 (by rfl) ⟨1737716, by rfl⟩ : syracuseStep 2316955 = 3475433) B3475433
theorem B3089273 : Blo 2059435 3089273 := bstep (se 2 (by rfl) ⟨1158477, by rfl⟩ : syracuseStep 3089273 = 2316955) B2316955
theorem B2059515 : Blo 2059435 2059515 := bstep (se 1 (by rfl) ⟨1544636, by rfl⟩ : syracuseStep 2059515 = 3089273) B3089273
theorem B19793717 : Blo 2059435 19793717 := bbase (se 5 (by rfl) ⟨927830, by rfl⟩ : syracuseStep 19793717 = 1855661) (by norm_num)
theorem B13195811 : Blo 2059435 13195811 := bstep (se 1 (by rfl) ⟨9896858, by rfl⟩ : syracuseStep 13195811 = 19793717) B19793717
theorem B35188829 : Blo 2059435 35188829 := bstep (se 3 (by rfl) ⟨6597905, by rfl⟩ : syracuseStep 35188829 = 13195811) B13195811
theorem B23459219 : Blo 2059435 23459219 := bstep (se 1 (by rfl) ⟨17594414, by rfl⟩ : syracuseStep 23459219 = 35188829) B35188829
theorem B15639479 : Blo 2059435 15639479 := bstep (se 1 (by rfl) ⟨11729609, by rfl⟩ : syracuseStep 15639479 = 23459219) B23459219
theorem B10426319 : Blo 2059435 10426319 := bstep (se 1 (by rfl) ⟨7819739, by rfl⟩ : syracuseStep 10426319 = 15639479) B15639479
theorem B6950879 : Blo 2059435 6950879 := bstep (se 1 (by rfl) ⟨5213159, by rfl⟩ : syracuseStep 6950879 = 10426319) B10426319
theorem B4633919 : Blo 2059435 4633919 := bstep (se 1 (by rfl) ⟨3475439, by rfl⟩ : syracuseStep 4633919 = 6950879) B6950879
theorem B3089279 : Blo 2059435 3089279 := bstep (se 1 (by rfl) ⟨2316959, by rfl⟩ : syracuseStep 3089279 = 4633919) B4633919
theorem B2059519 : Blo 2059435 2059519 := bstep (se 1 (by rfl) ⟨1544639, by rfl⟩ : syracuseStep 2059519 = 3089279) B3089279
theorem B3089285 : Blo 2059435 3089285 := bbase (se 4 (by rfl) ⟨289620, by rfl⟩ : syracuseStep 3089285 = 579241) (by norm_num)
theorem B2059523 : Blo 2059435 2059523 := bstep (se 1 (by rfl) ⟨1544642, by rfl⟩ : syracuseStep 2059523 = 3089285) B3089285
theorem B3475453 : Blo 2059435 3475453 := bbase (se 3 (by rfl) ⟨651647, by rfl⟩ : syracuseStep 3475453 = 1303295) (by norm_num)
theorem B4633937 : Blo 2059435 4633937 := bstep (se 2 (by rfl) ⟨1737726, by rfl⟩ : syracuseStep 4633937 = 3475453) B3475453
theorem B3089291 : Blo 2059435 3089291 := bstep (se 1 (by rfl) ⟨2316968, by rfl⟩ : syracuseStep 3089291 = 4633937) B4633937
theorem B2059527 : Blo 2059435 2059527 := bstep (se 1 (by rfl) ⟨1544645, by rfl⟩ : syracuseStep 2059527 = 3089291) B3089291
theorem B2316973 : Blo 2059435 2316973 := bbase (se 3 (by rfl) ⟨434432, by rfl⟩ : syracuseStep 2316973 = 868865) (by norm_num)
theorem B3089297 : Blo 2059435 3089297 := bstep (se 2 (by rfl) ⟨1158486, by rfl⟩ : syracuseStep 3089297 = 2316973) B2316973
theorem B2059531 : Blo 2059435 2059531 := bstep (se 1 (by rfl) ⟨1544648, by rfl⟩ : syracuseStep 2059531 = 3089297) B3089297
theorem B6950933 : Blo 2059435 6950933 := bbase (se 6 (by rfl) ⟨162912, by rfl⟩ : syracuseStep 6950933 = 325825) (by norm_num)
theorem B4633955 : Blo 2059435 4633955 := bstep (se 1 (by rfl) ⟨3475466, by rfl⟩ : syracuseStep 4633955 = 6950933) B6950933
theorem B3089303 : Blo 2059435 3089303 := bstep (se 1 (by rfl) ⟨2316977, by rfl⟩ : syracuseStep 3089303 = 4633955) B4633955
theorem B2059535 : Blo 2059435 2059535 := bstep (se 1 (by rfl) ⟨1544651, by rfl⟩ : syracuseStep 2059535 = 3089303) B3089303
theorem B3089309 : Blo 2059435 3089309 := bbase (se 3 (by rfl) ⟨579245, by rfl⟩ : syracuseStep 3089309 = 1158491) (by norm_num)
theorem B2059539 : Blo 2059435 2059539 := bstep (se 1 (by rfl) ⟨1544654, by rfl⟩ : syracuseStep 2059539 = 3089309) B3089309
theorem B4633973 : Blo 2059435 4633973 := bbase (se 5 (by rfl) ⟨217217, by rfl⟩ : syracuseStep 4633973 = 434435) (by norm_num)
theorem B3089315 : Blo 2059435 3089315 := bstep (se 1 (by rfl) ⟨2316986, by rfl⟩ : syracuseStep 3089315 = 4633973) B4633973
theorem B2059543 : Blo 2059435 2059543 := bstep (se 1 (by rfl) ⟨1544657, by rfl⟩ : syracuseStep 2059543 = 3089315) B3089315
theorem B14845493 : Blo 2059435 14845493 := bbase (se 5 (by rfl) ⟨695882, by rfl⟩ : syracuseStep 14845493 = 1391765) (by norm_num)
theorem B9896995 : Blo 2059435 9896995 := bstep (se 1 (by rfl) ⟨7422746, by rfl⟩ : syracuseStep 9896995 = 14845493) B14845493
theorem B13195993 : Blo 2059435 13195993 := bstep (se 2 (by rfl) ⟨4948497, by rfl⟩ : syracuseStep 13195993 = 9896995) B9896995
theorem B17594657 : Blo 2059435 17594657 := bstep (se 2 (by rfl) ⟨6597996, by rfl⟩ : syracuseStep 17594657 = 13195993) B13195993
theorem B11729771 : Blo 2059435 11729771 := bstep (se 1 (by rfl) ⟨8797328, by rfl⟩ : syracuseStep 11729771 = 17594657) B17594657
theorem B7819847 : Blo 2059435 7819847 := bstep (se 1 (by rfl) ⟨5864885, by rfl⟩ : syracuseStep 7819847 = 11729771) B11729771
theorem B5213231 : Blo 2059435 5213231 := bstep (se 1 (by rfl) ⟨3909923, by rfl⟩ : syracuseStep 5213231 = 7819847) B7819847
theorem B3475487 : Blo 2059435 3475487 := bstep (se 1 (by rfl) ⟨2606615, by rfl⟩ : syracuseStep 3475487 = 5213231) B5213231
theorem B2316991 : Blo 2059435 2316991 := bstep (se 1 (by rfl) ⟨1737743, by rfl⟩ : syracuseStep 2316991 = 3475487) B3475487
theorem B3089321 : Blo 2059435 3089321 := bstep (se 2 (by rfl) ⟨1158495, by rfl⟩ : syracuseStep 3089321 = 2316991) B2316991
theorem B2059547 : Blo 2059435 2059547 := bstep (se 1 (by rfl) ⟨1544660, by rfl⟩ : syracuseStep 2059547 = 3089321) B3089321
theorem B7819861 : Blo 2059435 7819861 := bbase (se 8 (by rfl) ⟨45819, by rfl⟩ : syracuseStep 7819861 = 91639) (by norm_num)
theorem B10426481 : Blo 2059435 10426481 := bstep (se 2 (by rfl) ⟨3909930, by rfl⟩ : syracuseStep 10426481 = 7819861) B7819861
theorem B6950987 : Blo 2059435 6950987 := bstep (se 1 (by rfl) ⟨5213240, by rfl⟩ : syracuseStep 6950987 = 10426481) B10426481
theorem B4633991 : Blo 2059435 4633991 := bstep (se 1 (by rfl) ⟨3475493, by rfl⟩ : syracuseStep 4633991 = 6950987) B6950987
theorem B3089327 : Blo 2059435 3089327 := bstep (se 1 (by rfl) ⟨2316995, by rfl⟩ : syracuseStep 3089327 = 4633991) B4633991
theorem B2059551 : Blo 2059435 2059551 := bstep (se 1 (by rfl) ⟨1544663, by rfl⟩ : syracuseStep 2059551 = 3089327) B3089327
theorem B3089333 : Blo 2059435 3089333 := bbase (se 5 (by rfl) ⟨144812, by rfl⟩ : syracuseStep 3089333 = 289625) (by norm_num)
theorem B2059555 : Blo 2059435 2059555 := bstep (se 1 (by rfl) ⟨1544666, by rfl⟩ : syracuseStep 2059555 = 3089333) B3089333
theorem B5213261 : Blo 2059435 5213261 := bbase (se 3 (by rfl) ⟨977486, by rfl⟩ : syracuseStep 5213261 = 1954973) (by norm_num)
theorem B3475507 : Blo 2059435 3475507 := bstep (se 1 (by rfl) ⟨2606630, by rfl⟩ : syracuseStep 3475507 = 5213261) B5213261
theorem B4634009 : Blo 2059435 4634009 := bstep (se 2 (by rfl) ⟨1737753, by rfl⟩ : syracuseStep 4634009 = 3475507) B3475507
theorem B3089339 : Blo 2059435 3089339 := bstep (se 1 (by rfl) ⟨2317004, by rfl⟩ : syracuseStep 3089339 = 4634009) B4634009
theorem B2059559 : Blo 2059435 2059559 := bstep (se 1 (by rfl) ⟨1544669, by rfl⟩ : syracuseStep 2059559 = 3089339) B3089339
theorem B2317009 : Blo 2059435 2317009 := bbase (se 2 (by rfl) ⟨868878, by rfl⟩ : syracuseStep 2317009 = 1737757) (by norm_num)
theorem B3089345 : Blo 2059435 3089345 := bstep (se 2 (by rfl) ⟨1158504, by rfl⟩ : syracuseStep 3089345 = 2317009) B2317009
theorem B2059563 : Blo 2059435 2059563 := bstep (se 1 (by rfl) ⟨1544672, by rfl⟩ : syracuseStep 2059563 = 3089345) B3089345
theorem B2474273 : Blo 2059435 2474273 := bbase (se 2 (by rfl) ⟨927852, by rfl⟩ : syracuseStep 2474273 = 1855705) (by norm_num)
theorem B6598061 : Blo 2059435 6598061 := bstep (se 3 (by rfl) ⟨1237136, by rfl⟩ : syracuseStep 6598061 = 2474273) B2474273
theorem B4398707 : Blo 2059435 4398707 := bstep (se 1 (by rfl) ⟨3299030, by rfl⟩ : syracuseStep 4398707 = 6598061) B6598061
theorem B2932471 : Blo 2059435 2932471 := bstep (se 1 (by rfl) ⟨2199353, by rfl⟩ : syracuseStep 2932471 = 4398707) B4398707
theorem B3909961 : Blo 2059435 3909961 := bstep (se 2 (by rfl) ⟨1466235, by rfl⟩ : syracuseStep 3909961 = 2932471) B2932471
theorem B5213281 : Blo 2059435 5213281 := bstep (se 2 (by rfl) ⟨1954980, by rfl⟩ : syracuseStep 5213281 = 3909961) B3909961
theorem B6951041 : Blo 2059435 6951041 := bstep (se 2 (by rfl) ⟨2606640, by rfl⟩ : syracuseStep 6951041 = 5213281) B5213281
theorem B4634027 : Blo 2059435 4634027 := bstep (se 1 (by rfl) ⟨3475520, by rfl⟩ : syracuseStep 4634027 = 6951041) B6951041
theorem B3089351 : Blo 2059435 3089351 := bstep (se 1 (by rfl) ⟨2317013, by rfl⟩ : syracuseStep 3089351 = 4634027) B4634027
theorem B2059567 : Blo 2059435 2059567 := bstep (se 1 (by rfl) ⟨1544675, by rfl⟩ : syracuseStep 2059567 = 3089351) B3089351
theorem B3089357 : Blo 2059435 3089357 := bbase (se 3 (by rfl) ⟨579254, by rfl⟩ : syracuseStep 3089357 = 1158509) (by norm_num)
theorem B2059571 : Blo 2059435 2059571 := bstep (se 1 (by rfl) ⟨1544678, by rfl⟩ : syracuseStep 2059571 = 3089357) B3089357
theorem B4634045 : Blo 2059435 4634045 := bbase (se 3 (by rfl) ⟨868883, by rfl⟩ : syracuseStep 4634045 = 1737767) (by norm_num)
theorem B3089363 : Blo 2059435 3089363 := bstep (se 1 (by rfl) ⟨2317022, by rfl⟩ : syracuseStep 3089363 = 4634045) B4634045
theorem B2059575 : Blo 2059435 2059575 := bstep (se 1 (by rfl) ⟨1544681, by rfl⟩ : syracuseStep 2059575 = 3089363) B3089363
theorem B3475541 : Blo 2059435 3475541 := bbase (se 8 (by rfl) ⟨20364, by rfl⟩ : syracuseStep 3475541 = 40729) (by norm_num)
theorem B2317027 : Blo 2059435 2317027 := bstep (se 1 (by rfl) ⟨1737770, by rfl⟩ : syracuseStep 2317027 = 3475541) B3475541
theorem B3089369 : Blo 2059435 3089369 := bstep (se 2 (by rfl) ⟨1158513, by rfl⟩ : syracuseStep 3089369 = 2317027) B2317027
theorem B2059579 : Blo 2059435 2059579 := bstep (se 1 (by rfl) ⟨1544684, by rfl⟩ : syracuseStep 2059579 = 3089369) B3089369
theorem B2642225 : Blo 2059435 2642225 := bbase (se 2 (by rfl) ⟨990834, by rfl⟩ : syracuseStep 2642225 = 1981669) (by norm_num)
theorem B28183733 : Blo 2059435 28183733 := bstep (se 5 (by rfl) ⟨1321112, by rfl⟩ : syracuseStep 28183733 = 2642225) B2642225
theorem B18789155 : Blo 2059435 18789155 := bstep (se 1 (by rfl) ⟨14091866, by rfl⟩ : syracuseStep 18789155 = 28183733) B28183733
theorem B12526103 : Blo 2059435 12526103 := bstep (se 1 (by rfl) ⟨9394577, by rfl⟩ : syracuseStep 12526103 = 18789155) B18789155
theorem B33402941 : Blo 2059435 33402941 := bstep (se 3 (by rfl) ⟨6263051, by rfl⟩ : syracuseStep 33402941 = 12526103) B12526103
theorem B22268627 : Blo 2059435 22268627 := bstep (se 1 (by rfl) ⟨16701470, by rfl⟩ : syracuseStep 22268627 = 33402941) B33402941
theorem B14845751 : Blo 2059435 14845751 := bstep (se 1 (by rfl) ⟨11134313, by rfl⟩ : syracuseStep 14845751 = 22268627) B22268627
theorem B9897167 : Blo 2059435 9897167 := bstep (se 1 (by rfl) ⟨7422875, by rfl⟩ : syracuseStep 9897167 = 14845751) B14845751
theorem B6598111 : Blo 2059435 6598111 := bstep (se 1 (by rfl) ⟨4948583, by rfl⟩ : syracuseStep 6598111 = 9897167) B9897167
theorem B8797481 : Blo 2059435 8797481 := bstep (se 2 (by rfl) ⟨3299055, by rfl⟩ : syracuseStep 8797481 = 6598111) B6598111
theorem B5864987 : Blo 2059435 5864987 := bstep (se 1 (by rfl) ⟨4398740, by rfl⟩ : syracuseStep 5864987 = 8797481) B8797481
theorem B15639965 : Blo 2059435 15639965 := bstep (se 3 (by rfl) ⟨2932493, by rfl⟩ : syracuseStep 15639965 = 5864987) B5864987
theorem B10426643 : Blo 2059435 10426643 := bstep (se 1 (by rfl) ⟨7819982, by rfl⟩ : syracuseStep 10426643 = 15639965) B15639965
theorem B6951095 : Blo 2059435 6951095 := bstep (se 1 (by rfl) ⟨5213321, by rfl⟩ : syracuseStep 6951095 = 10426643) B10426643
theorem B4634063 : Blo 2059435 4634063 := bstep (se 1 (by rfl) ⟨3475547, by rfl⟩ : syracuseStep 4634063 = 6951095) B6951095
theorem B3089375 : Blo 2059435 3089375 := bstep (se 1 (by rfl) ⟨2317031, by rfl⟩ : syracuseStep 3089375 = 4634063) B4634063
theorem B2059583 : Blo 2059435 2059583 := bstep (se 1 (by rfl) ⟨1544687, by rfl⟩ : syracuseStep 2059583 = 3089375) B3089375
theorem B3089381 : Blo 2059435 3089381 := bbase (se 4 (by rfl) ⟨289629, by rfl⟩ : syracuseStep 3089381 = 579259) (by norm_num)
theorem B2059587 : Blo 2059435 2059587 := bstep (se 1 (by rfl) ⟨1544690, by rfl⟩ : syracuseStep 2059587 = 3089381) B3089381
theorem B3299069 : Blo 2059435 3299069 := bbase (se 3 (by rfl) ⟨618575, by rfl⟩ : syracuseStep 3299069 = 1237151) (by norm_num)
theorem B8797517 : Blo 2059435 8797517 := bstep (se 3 (by rfl) ⟨1649534, by rfl⟩ : syracuseStep 8797517 = 3299069) B3299069
theorem B5865011 : Blo 2059435 5865011 := bstep (se 1 (by rfl) ⟨4398758, by rfl⟩ : syracuseStep 5865011 = 8797517) B8797517
theorem B3910007 : Blo 2059435 3910007 := bstep (se 1 (by rfl) ⟨2932505, by rfl⟩ : syracuseStep 3910007 = 5865011) B5865011
theorem B2606671 : Blo 2059435 2606671 := bstep (se 1 (by rfl) ⟨1955003, by rfl⟩ : syracuseStep 2606671 = 3910007) B3910007
theorem B3475561 : Blo 2059435 3475561 := bstep (se 2 (by rfl) ⟨1303335, by rfl⟩ : syracuseStep 3475561 = 2606671) B2606671
theorem B4634081 : Blo 2059435 4634081 := bstep (se 2 (by rfl) ⟨1737780, by rfl⟩ : syracuseStep 4634081 = 3475561) B3475561
theorem B3089387 : Blo 2059435 3089387 := bstep (se 1 (by rfl) ⟨2317040, by rfl⟩ : syracuseStep 3089387 = 4634081) B4634081
theorem B2059591 : Blo 2059435 2059591 := bstep (se 1 (by rfl) ⟨1544693, by rfl⟩ : syracuseStep 2059591 = 3089387) B3089387
theorem B2317045 : Blo 2059435 2317045 := bbase (se 5 (by rfl) ⟨108611, by rfl⟩ : syracuseStep 2317045 = 217223) (by norm_num)
theorem B3089393 : Blo 2059435 3089393 := bstep (se 2 (by rfl) ⟨1158522, by rfl⟩ : syracuseStep 3089393 = 2317045) B2317045
theorem B2059595 : Blo 2059435 2059595 := bstep (se 1 (by rfl) ⟨1544696, by rfl⟩ : syracuseStep 2059595 = 3089393) B3089393
theorem B2606681 : Blo 2059435 2606681 := bbase (se 2 (by rfl) ⟨977505, by rfl⟩ : syracuseStep 2606681 = 1955011) (by norm_num)
theorem B6951149 : Blo 2059435 6951149 := bstep (se 3 (by rfl) ⟨1303340, by rfl⟩ : syracuseStep 6951149 = 2606681) B2606681
theorem B4634099 : Blo 2059435 4634099 := bstep (se 1 (by rfl) ⟨3475574, by rfl⟩ : syracuseStep 4634099 = 6951149) B6951149
theorem B3089399 : Blo 2059435 3089399 := bstep (se 1 (by rfl) ⟨2317049, by rfl⟩ : syracuseStep 3089399 = 4634099) B4634099
theorem B2059599 : Blo 2059435 2059599 := bstep (se 1 (by rfl) ⟨1544699, by rfl⟩ : syracuseStep 2059599 = 3089399) B3089399
theorem B3089405 : Blo 2059435 3089405 := bbase (se 3 (by rfl) ⟨579263, by rfl⟩ : syracuseStep 3089405 = 1158527) (by norm_num)
theorem B2059603 : Blo 2059435 2059603 := bstep (se 1 (by rfl) ⟨1544702, by rfl⟩ : syracuseStep 2059603 = 3089405) B3089405
theorem B4634117 : Blo 2059435 4634117 := bbase (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) (by norm_num)
theorem B3089411 : Blo 2059435 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B2059607 : Blo 2059435 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B3910045 : Blo 2059435 3910045 := bbase (se 3 (by rfl) ⟨733133, by rfl⟩ : syracuseStep 3910045 = 1466267) (by norm_num)
theorem B5213393 : Blo 2059435 5213393 := bstep (se 2 (by rfl) ⟨1955022, by rfl⟩ : syracuseStep 5213393 = 3910045) B3910045
theorem B3475595 : Blo 2059435 3475595 := bstep (se 1 (by rfl) ⟨2606696, by rfl⟩ : syracuseStep 3475595 = 5213393) B5213393
theorem B2317063 : Blo 2059435 2317063 := bstep (se 1 (by rfl) ⟨1737797, by rfl⟩ : syracuseStep 2317063 = 3475595) B3475595
theorem B3089417 : Blo 2059435 3089417 := bstep (se 2 (by rfl) ⟨1158531, by rfl⟩ : syracuseStep 3089417 = 2317063) B2317063
theorem B2059611 : Blo 2059435 2059611 := bstep (se 1 (by rfl) ⟨1544708, by rfl⟩ : syracuseStep 2059611 = 3089417) B3089417
theorem B10426805 : Blo 2059435 10426805 := bbase (se 5 (by rfl) ⟨488756, by rfl⟩ : syracuseStep 10426805 = 977513) (by norm_num)
theorem B6951203 : Blo 2059435 6951203 := bstep (se 1 (by rfl) ⟨5213402, by rfl⟩ : syracuseStep 6951203 = 10426805) B10426805
theorem B4634135 : Blo 2059435 4634135 := bstep (se 1 (by rfl) ⟨3475601, by rfl⟩ : syracuseStep 4634135 = 6951203) B6951203
theorem B3089423 : Blo 2059435 3089423 := bstep (se 1 (by rfl) ⟨2317067, by rfl⟩ : syracuseStep 3089423 = 4634135) B4634135
theorem B2059615 : Blo 2059435 2059615 := bstep (se 1 (by rfl) ⟨1544711, by rfl⟩ : syracuseStep 2059615 = 3089423) B3089423
theorem B3089429 : Blo 2059435 3089429 := bbase (se 6 (by rfl) ⟨72408, by rfl⟩ : syracuseStep 3089429 = 144817) (by norm_num)
theorem B2059619 : Blo 2059435 2059619 := bstep (se 1 (by rfl) ⟨1544714, by rfl⟩ : syracuseStep 2059619 = 3089429) B3089429
theorem B5016197 : Blo 2059435 5016197 := bbase (se 4 (by rfl) ⟨470268, by rfl⟩ : syracuseStep 5016197 = 940537) (by norm_num)
theorem B3344131 : Blo 2059435 3344131 := bstep (se 1 (by rfl) ⟨2508098, by rfl⟩ : syracuseStep 3344131 = 5016197) B5016197
theorem B17835365 : Blo 2059435 17835365 := bstep (se 4 (by rfl) ⟨1672065, by rfl⟩ : syracuseStep 17835365 = 3344131) B3344131
theorem B11890243 : Blo 2059435 11890243 := bstep (se 1 (by rfl) ⟨8917682, by rfl⟩ : syracuseStep 11890243 = 17835365) B17835365
theorem B63414629 : Blo 2059435 63414629 := bstep (se 4 (by rfl) ⟨5945121, by rfl⟩ : syracuseStep 63414629 = 11890243) B11890243
theorem B42276419 : Blo 2059435 42276419 := bstep (se 1 (by rfl) ⟨31707314, by rfl⟩ : syracuseStep 42276419 = 63414629) B63414629
theorem B28184279 : Blo 2059435 28184279 := bstep (se 1 (by rfl) ⟨21138209, by rfl⟩ : syracuseStep 28184279 = 42276419) B42276419
theorem B75158077 : Blo 2059435 75158077 := bstep (se 3 (by rfl) ⟨14092139, by rfl⟩ : syracuseStep 75158077 = 28184279) B28184279
theorem B100210769 : Blo 2059435 100210769 := bstep (se 2 (by rfl) ⟨37579038, by rfl⟩ : syracuseStep 100210769 = 75158077) B75158077
theorem B66807179 : Blo 2059435 66807179 := bstep (se 1 (by rfl) ⟨50105384, by rfl⟩ : syracuseStep 66807179 = 100210769) B100210769
theorem B44538119 : Blo 2059435 44538119 := bstep (se 1 (by rfl) ⟨33403589, by rfl⟩ : syracuseStep 44538119 = 66807179) B66807179
theorem B29692079 : Blo 2059435 29692079 := bstep (se 1 (by rfl) ⟨22269059, by rfl⟩ : syracuseStep 29692079 = 44538119) B44538119
theorem B19794719 : Blo 2059435 19794719 := bstep (se 1 (by rfl) ⟨14846039, by rfl⟩ : syracuseStep 19794719 = 29692079) B29692079
theorem B13196479 : Blo 2059435 13196479 := bstep (se 1 (by rfl) ⟨9897359, by rfl⟩ : syracuseStep 13196479 = 19794719) B19794719
theorem B17595305 : Blo 2059435 17595305 := bstep (se 2 (by rfl) ⟨6598239, by rfl⟩ : syracuseStep 17595305 = 13196479) B13196479
theorem B11730203 : Blo 2059435 11730203 := bstep (se 1 (by rfl) ⟨8797652, by rfl⟩ : syracuseStep 11730203 = 17595305) B17595305
theorem B7820135 : Blo 2059435 7820135 := bstep (se 1 (by rfl) ⟨5865101, by rfl⟩ : syracuseStep 7820135 = 11730203) B11730203
theorem B5213423 : Blo 2059435 5213423 := bstep (se 1 (by rfl) ⟨3910067, by rfl⟩ : syracuseStep 5213423 = 7820135) B7820135
theorem B3475615 : Blo 2059435 3475615 := bstep (se 1 (by rfl) ⟨2606711, by rfl⟩ : syracuseStep 3475615 = 5213423) B5213423
theorem B4634153 : Blo 2059435 4634153 := bstep (se 2 (by rfl) ⟨1737807, by rfl⟩ : syracuseStep 4634153 = 3475615) B3475615
theorem B3089435 : Blo 2059435 3089435 := bstep (se 1 (by rfl) ⟨2317076, by rfl⟩ : syracuseStep 3089435 = 4634153) B4634153
theorem B2059623 : Blo 2059435 2059623 := bstep (se 1 (by rfl) ⟨1544717, by rfl⟩ : syracuseStep 2059623 = 3089435) B3089435
theorem B2317081 : Blo 2059435 2317081 := bbase (se 2 (by rfl) ⟨868905, by rfl⟩ : syracuseStep 2317081 = 1737811) (by norm_num)
theorem B3089441 : Blo 2059435 3089441 := bstep (se 2 (by rfl) ⟨1158540, by rfl⟩ : syracuseStep 3089441 = 2317081) B2317081
theorem B2059627 : Blo 2059435 2059627 := bstep (se 1 (by rfl) ⟨1544720, by rfl⟩ : syracuseStep 2059627 = 3089441) B3089441
theorem B7820165 : Blo 2059435 7820165 := bbase (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) (by norm_num)
theorem B5213443 : Blo 2059435 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B6951257 : Blo 2059435 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B4634171 : Blo 2059435 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B3089447 : Blo 2059435 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B2059631 : Blo 2059435 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B3089453 : Blo 2059435 3089453 := bbase (se 3 (by rfl) ⟨579272, by rfl⟩ : syracuseStep 3089453 = 1158545) (by norm_num)
theorem B2059635 : Blo 2059435 2059635 := bstep (se 1 (by rfl) ⟨1544726, by rfl⟩ : syracuseStep 2059635 = 3089453) B3089453
theorem B4634189 : Blo 2059435 4634189 := bbase (se 3 (by rfl) ⟨868910, by rfl⟩ : syracuseStep 4634189 = 1737821) (by norm_num)
theorem B3089459 : Blo 2059435 3089459 := bstep (se 1 (by rfl) ⟨2317094, by rfl⟩ : syracuseStep 3089459 = 4634189) B4634189
theorem B2059639 : Blo 2059435 2059639 := bstep (se 1 (by rfl) ⟨1544729, by rfl⟩ : syracuseStep 2059639 = 3089459) B3089459
theorem B2606737 : Blo 2059435 2606737 := bbase (se 2 (by rfl) ⟨977526, by rfl⟩ : syracuseStep 2606737 = 1955053) (by norm_num)
theorem B3475649 : Blo 2059435 3475649 := bstep (se 2 (by rfl) ⟨1303368, by rfl⟩ : syracuseStep 3475649 = 2606737) B2606737
theorem B2317099 : Blo 2059435 2317099 := bstep (se 1 (by rfl) ⟨1737824, by rfl⟩ : syracuseStep 2317099 = 3475649) B3475649
theorem B3089465 : Blo 2059435 3089465 := bstep (se 2 (by rfl) ⟨1158549, by rfl⟩ : syracuseStep 3089465 = 2317099) B2317099
theorem B2059643 : Blo 2059435 2059643 := bstep (se 1 (by rfl) ⟨1544732, by rfl⟩ : syracuseStep 2059643 = 3089465) B3089465
theorem B4398877 : Blo 2059435 4398877 := bbase (se 3 (by rfl) ⟨824789, by rfl⟩ : syracuseStep 4398877 = 1649579) (by norm_num)
theorem B23460677 : Blo 2059435 23460677 := bstep (se 4 (by rfl) ⟨2199438, by rfl⟩ : syracuseStep 23460677 = 4398877) B4398877
theorem B15640451 : Blo 2059435 15640451 := bstep (se 1 (by rfl) ⟨11730338, by rfl⟩ : syracuseStep 15640451 = 23460677) B23460677
theorem B10426967 : Blo 2059435 10426967 := bstep (se 1 (by rfl) ⟨7820225, by rfl⟩ : syracuseStep 10426967 = 15640451) B15640451
theorem B6951311 : Blo 2059435 6951311 := bstep (se 1 (by rfl) ⟨5213483, by rfl⟩ : syracuseStep 6951311 = 10426967) B10426967
theorem B4634207 : Blo 2059435 4634207 := bstep (se 1 (by rfl) ⟨3475655, by rfl⟩ : syracuseStep 4634207 = 6951311) B6951311
theorem B3089471 : Blo 2059435 3089471 := bstep (se 1 (by rfl) ⟨2317103, by rfl⟩ : syracuseStep 3089471 = 4634207) B4634207
theorem B2059647 : Blo 2059435 2059647 := bstep (se 1 (by rfl) ⟨1544735, by rfl⟩ : syracuseStep 2059647 = 3089471) B3089471
theorem B3089477 : Blo 2059435 3089477 := bbase (se 4 (by rfl) ⟨289638, by rfl⟩ : syracuseStep 3089477 = 579277) (by norm_num)
theorem B2059651 : Blo 2059435 2059651 := bstep (se 1 (by rfl) ⟨1544738, by rfl⟩ : syracuseStep 2059651 = 3089477) B3089477
theorem B3475669 : Blo 2059435 3475669 := bbase (se 7 (by rfl) ⟨40730, by rfl⟩ : syracuseStep 3475669 = 81461) (by norm_num)
theorem B4634225 : Blo 2059435 4634225 := bstep (se 2 (by rfl) ⟨1737834, by rfl⟩ : syracuseStep 4634225 = 3475669) B3475669
theorem B3089483 : Blo 2059435 3089483 := bstep (se 1 (by rfl) ⟨2317112, by rfl⟩ : syracuseStep 3089483 = 4634225) B4634225
theorem B2059655 : Blo 2059435 2059655 := bstep (se 1 (by rfl) ⟨1544741, by rfl⟩ : syracuseStep 2059655 = 3089483) B3089483
theorem B2317117 : Blo 2059435 2317117 := bbase (se 3 (by rfl) ⟨434459, by rfl⟩ : syracuseStep 2317117 = 868919) (by norm_num)
theorem B3089489 : Blo 2059435 3089489 := bstep (se 2 (by rfl) ⟨1158558, by rfl⟩ : syracuseStep 3089489 = 2317117) B2317117
theorem B2059659 : Blo 2059435 2059659 := bstep (se 1 (by rfl) ⟨1544744, by rfl⟩ : syracuseStep 2059659 = 3089489) B3089489
theorem B6951365 : Blo 2059435 6951365 := bbase (se 4 (by rfl) ⟨651690, by rfl⟩ : syracuseStep 6951365 = 1303381) (by norm_num)
theorem B4634243 : Blo 2059435 4634243 := bstep (se 1 (by rfl) ⟨3475682, by rfl⟩ : syracuseStep 4634243 = 6951365) B6951365
theorem B3089495 : Blo 2059435 3089495 := bstep (se 1 (by rfl) ⟨2317121, by rfl⟩ : syracuseStep 3089495 = 4634243) B4634243
theorem B2059663 : Blo 2059435 2059663 := bstep (se 1 (by rfl) ⟨1544747, by rfl⟩ : syracuseStep 2059663 = 3089495) B3089495
theorem B3089501 : Blo 2059435 3089501 := bbase (se 3 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 3089501 = 1158563) (by norm_num)
theorem B2059667 : Blo 2059435 2059667 := bstep (se 1 (by rfl) ⟨1544750, by rfl⟩ : syracuseStep 2059667 = 3089501) B3089501
theorem B4634261 : Blo 2059435 4634261 := bbase (se 6 (by rfl) ⟨108615, by rfl⟩ : syracuseStep 4634261 = 217231) (by norm_num)
theorem B3089507 : Blo 2059435 3089507 := bstep (se 1 (by rfl) ⟨2317130, by rfl⟩ : syracuseStep 3089507 = 4634261) B4634261
theorem B2059671 : Blo 2059435 2059671 := bstep (se 1 (by rfl) ⟨1544753, by rfl⟩ : syracuseStep 2059671 = 3089507) B3089507
theorem B2199469 : Blo 2059435 2199469 := bbase (se 3 (by rfl) ⟨412400, by rfl⟩ : syracuseStep 2199469 = 824801) (by norm_num)
theorem B2932625 : Blo 2059435 2932625 := bstep (se 2 (by rfl) ⟨1099734, by rfl⟩ : syracuseStep 2932625 = 2199469) B2199469
theorem B7820333 : Blo 2059435 7820333 := bstep (se 3 (by rfl) ⟨1466312, by rfl⟩ : syracuseStep 7820333 = 2932625) B2932625
theorem B5213555 : Blo 2059435 5213555 := bstep (se 1 (by rfl) ⟨3910166, by rfl⟩ : syracuseStep 5213555 = 7820333) B7820333
theorem B3475703 : Blo 2059435 3475703 := bstep (se 1 (by rfl) ⟨2606777, by rfl⟩ : syracuseStep 3475703 = 5213555) B5213555
theorem B2317135 : Blo 2059435 2317135 := bstep (se 1 (by rfl) ⟨1737851, by rfl⟩ : syracuseStep 2317135 = 3475703) B3475703
theorem B3089513 : Blo 2059435 3089513 := bstep (se 2 (by rfl) ⟨1158567, by rfl⟩ : syracuseStep 3089513 = 2317135) B2317135
theorem B2059675 : Blo 2059435 2059675 := bstep (se 1 (by rfl) ⟨1544756, by rfl⟩ : syracuseStep 2059675 = 3089513) B3089513
theorem B4697509 : Blo 2059435 4697509 := bbase (se 4 (by rfl) ⟨440391, by rfl⟩ : syracuseStep 4697509 = 880783) (by norm_num)
theorem B6263345 : Blo 2059435 6263345 := bstep (se 2 (by rfl) ⟨2348754, by rfl⟩ : syracuseStep 6263345 = 4697509) B4697509
theorem B4175563 : Blo 2059435 4175563 := bstep (se 1 (by rfl) ⟨3131672, by rfl⟩ : syracuseStep 4175563 = 6263345) B6263345
theorem B5567417 : Blo 2059435 5567417 := bstep (se 2 (by rfl) ⟨2087781, by rfl⟩ : syracuseStep 5567417 = 4175563) B4175563
theorem B3711611 : Blo 2059435 3711611 := bstep (se 1 (by rfl) ⟨2783708, by rfl⟩ : syracuseStep 3711611 = 5567417) B5567417
theorem B2474407 : Blo 2059435 2474407 := bstep (se 1 (by rfl) ⟨1855805, by rfl⟩ : syracuseStep 2474407 = 3711611) B3711611
theorem B13196837 : Blo 2059435 13196837 := bstep (se 4 (by rfl) ⟨1237203, by rfl⟩ : syracuseStep 13196837 = 2474407) B2474407
theorem B8797891 : Blo 2059435 8797891 := bstep (se 1 (by rfl) ⟨6598418, by rfl⟩ : syracuseStep 8797891 = 13196837) B13196837
theorem B11730521 : Blo 2059435 11730521 := bstep (se 2 (by rfl) ⟨4398945, by rfl⟩ : syracuseStep 11730521 = 8797891) B8797891
theorem B7820347 : Blo 2059435 7820347 := bstep (se 1 (by rfl) ⟨5865260, by rfl⟩ : syracuseStep 7820347 = 11730521) B11730521
theorem B10427129 : Blo 2059435 10427129 := bstep (se 2 (by rfl) ⟨3910173, by rfl⟩ : syracuseStep 10427129 = 7820347) B7820347
theorem B6951419 : Blo 2059435 6951419 := bstep (se 1 (by rfl) ⟨5213564, by rfl⟩ : syracuseStep 6951419 = 10427129) B10427129
theorem B4634279 : Blo 2059435 4634279 := bstep (se 1 (by rfl) ⟨3475709, by rfl⟩ : syracuseStep 4634279 = 6951419) B6951419
theorem B3089519 : Blo 2059435 3089519 := bstep (se 1 (by rfl) ⟨2317139, by rfl⟩ : syracuseStep 3089519 = 4634279) B4634279
theorem B2059679 : Blo 2059435 2059679 := bstep (se 1 (by rfl) ⟨1544759, by rfl⟩ : syracuseStep 2059679 = 3089519) B3089519
theorem B3089525 : Blo 2059435 3089525 := bbase (se 5 (by rfl) ⟨144821, by rfl⟩ : syracuseStep 3089525 = 289643) (by norm_num)
theorem B2059683 : Blo 2059435 2059683 := bstep (se 1 (by rfl) ⟨1544762, by rfl⟩ : syracuseStep 2059683 = 3089525) B3089525
theorem B3910189 : Blo 2059435 3910189 := bbase (se 3 (by rfl) ⟨733160, by rfl⟩ : syracuseStep 3910189 = 1466321) (by norm_num)
theorem B5213585 : Blo 2059435 5213585 := bstep (se 2 (by rfl) ⟨1955094, by rfl⟩ : syracuseStep 5213585 = 3910189) B3910189
theorem B3475723 : Blo 2059435 3475723 := bstep (se 1 (by rfl) ⟨2606792, by rfl⟩ : syracuseStep 3475723 = 5213585) B5213585
theorem B4634297 : Blo 2059435 4634297 := bstep (se 2 (by rfl) ⟨1737861, by rfl⟩ : syracuseStep 4634297 = 3475723) B3475723
theorem B3089531 : Blo 2059435 3089531 := bstep (se 1 (by rfl) ⟨2317148, by rfl⟩ : syracuseStep 3089531 = 4634297) B4634297
theorem B2059687 : Blo 2059435 2059687 := bstep (se 1 (by rfl) ⟨1544765, by rfl⟩ : syracuseStep 2059687 = 3089531) B3089531
theorem B2317153 : Blo 2059435 2317153 := bbase (se 2 (by rfl) ⟨868932, by rfl⟩ : syracuseStep 2317153 = 1737865) (by norm_num)
theorem B3089537 : Blo 2059435 3089537 := bstep (se 2 (by rfl) ⟨1158576, by rfl⟩ : syracuseStep 3089537 = 2317153) B2317153
theorem B2059691 : Blo 2059435 2059691 := bstep (se 1 (by rfl) ⟨1544768, by rfl⟩ : syracuseStep 2059691 = 3089537) B3089537
theorem B5213605 : Blo 2059435 5213605 := bbase (se 4 (by rfl) ⟨488775, by rfl⟩ : syracuseStep 5213605 = 977551) (by norm_num)
theorem B6951473 : Blo 2059435 6951473 := bstep (se 2 (by rfl) ⟨2606802, by rfl⟩ : syracuseStep 6951473 = 5213605) B5213605
theorem B4634315 : Blo 2059435 4634315 := bstep (se 1 (by rfl) ⟨3475736, by rfl⟩ : syracuseStep 4634315 = 6951473) B6951473
theorem B3089543 : Blo 2059435 3089543 := bstep (se 1 (by rfl) ⟨2317157, by rfl⟩ : syracuseStep 3089543 = 4634315) B4634315
theorem B2059695 : Blo 2059435 2059695 := bstep (se 1 (by rfl) ⟨1544771, by rfl⟩ : syracuseStep 2059695 = 3089543) B3089543
theorem B3089549 : Blo 2059435 3089549 := bbase (se 3 (by rfl) ⟨579290, by rfl⟩ : syracuseStep 3089549 = 1158581) (by norm_num)
theorem B2059699 : Blo 2059435 2059699 := bstep (se 1 (by rfl) ⟨1544774, by rfl⟩ : syracuseStep 2059699 = 3089549) B3089549
theorem B4634333 : Blo 2059435 4634333 := bbase (se 3 (by rfl) ⟨868937, by rfl⟩ : syracuseStep 4634333 = 1737875) (by norm_num)
theorem B3089555 : Blo 2059435 3089555 := bstep (se 1 (by rfl) ⟨2317166, by rfl⟩ : syracuseStep 3089555 = 4634333) B4634333
theorem B2059703 : Blo 2059435 2059703 := bstep (se 1 (by rfl) ⟨1544777, by rfl⟩ : syracuseStep 2059703 = 3089555) B3089555
theorem B3475757 : Blo 2059435 3475757 := bbase (se 3 (by rfl) ⟨651704, by rfl⟩ : syracuseStep 3475757 = 1303409) (by norm_num)
theorem B2317171 : Blo 2059435 2317171 := bstep (se 1 (by rfl) ⟨1737878, by rfl⟩ : syracuseStep 2317171 = 3475757) B3475757
theorem B3089561 : Blo 2059435 3089561 := bstep (se 2 (by rfl) ⟨1158585, by rfl⟩ : syracuseStep 3089561 = 2317171) B2317171
theorem B2059707 : Blo 2059435 2059707 := bstep (se 1 (by rfl) ⟨1544780, by rfl⟩ : syracuseStep 2059707 = 3089561) B3089561
theorem B39591125 : Blo 2059435 39591125 := bbase (se 7 (by rfl) ⟨463958, by rfl⟩ : syracuseStep 39591125 = 927917) (by norm_num)
theorem B26394083 : Blo 2059435 26394083 := bstep (se 1 (by rfl) ⟨19795562, by rfl⟩ : syracuseStep 26394083 = 39591125) B39591125
theorem B17596055 : Blo 2059435 17596055 := bstep (se 1 (by rfl) ⟨13197041, by rfl⟩ : syracuseStep 17596055 = 26394083) B26394083
theorem B11730703 : Blo 2059435 11730703 := bstep (se 1 (by rfl) ⟨8798027, by rfl⟩ : syracuseStep 11730703 = 17596055) B17596055
theorem B15640937 : Blo 2059435 15640937 := bstep (se 2 (by rfl) ⟨5865351, by rfl⟩ : syracuseStep 15640937 = 11730703) B11730703
theorem B10427291 : Blo 2059435 10427291 := bstep (se 1 (by rfl) ⟨7820468, by rfl⟩ : syracuseStep 10427291 = 15640937) B15640937
theorem B6951527 : Blo 2059435 6951527 := bstep (se 1 (by rfl) ⟨5213645, by rfl⟩ : syracuseStep 6951527 = 10427291) B10427291
theorem B4634351 : Blo 2059435 4634351 := bstep (se 1 (by rfl) ⟨3475763, by rfl⟩ : syracuseStep 4634351 = 6951527) B6951527
theorem B3089567 : Blo 2059435 3089567 := bstep (se 1 (by rfl) ⟨2317175, by rfl⟩ : syracuseStep 3089567 = 4634351) B4634351
theorem B2059711 : Blo 2059435 2059711 := bstep (se 1 (by rfl) ⟨1544783, by rfl⟩ : syracuseStep 2059711 = 3089567) B3089567
theorem B3089573 : Blo 2059435 3089573 := bbase (se 4 (by rfl) ⟨289647, by rfl⟩ : syracuseStep 3089573 = 579295) (by norm_num)
theorem B2059715 : Blo 2059435 2059715 := bstep (se 1 (by rfl) ⟨1544786, by rfl⟩ : syracuseStep 2059715 = 3089573) B3089573
theorem B2606833 : Blo 2059435 2606833 := bbase (se 2 (by rfl) ⟨977562, by rfl⟩ : syracuseStep 2606833 = 1955125) (by norm_num)
theorem B3475777 : Blo 2059435 3475777 := bstep (se 2 (by rfl) ⟨1303416, by rfl⟩ : syracuseStep 3475777 = 2606833) B2606833
theorem B4634369 : Blo 2059435 4634369 := bstep (se 2 (by rfl) ⟨1737888, by rfl⟩ : syracuseStep 4634369 = 3475777) B3475777
theorem B3089579 : Blo 2059435 3089579 := bstep (se 1 (by rfl) ⟨2317184, by rfl⟩ : syracuseStep 3089579 = 4634369) B4634369
theorem B2059719 : Blo 2059435 2059719 := bstep (se 1 (by rfl) ⟨1544789, by rfl⟩ : syracuseStep 2059719 = 3089579) B3089579
theorem B2317189 : Blo 2059435 2317189 := bbase (se 4 (by rfl) ⟨217236, by rfl⟩ : syracuseStep 2317189 = 434473) (by norm_num)
theorem B3089585 : Blo 2059435 3089585 := bstep (se 2 (by rfl) ⟨1158594, by rfl⟩ : syracuseStep 3089585 = 2317189) B2317189
theorem B2059723 : Blo 2059435 2059723 := bstep (se 1 (by rfl) ⟨1544792, by rfl⟩ : syracuseStep 2059723 = 3089585) B3089585
theorem B7423397 : Blo 2059435 7423397 := bbase (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) (by norm_num)
theorem B4948931 : Blo 2059435 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B3299287 : Blo 2059435 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B4399049 : Blo 2059435 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B2932699 : Blo 2059435 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B3910265 : Blo 2059435 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B2606843 : Blo 2059435 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B6951581 : Blo 2059435 6951581 := bstep (se 3 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 6951581 = 2606843) B2606843
theorem B4634387 : Blo 2059435 4634387 := bstep (se 1 (by rfl) ⟨3475790, by rfl⟩ : syracuseStep 4634387 = 6951581) B6951581
theorem B3089591 : Blo 2059435 3089591 := bstep (se 1 (by rfl) ⟨2317193, by rfl⟩ : syracuseStep 3089591 = 4634387) B4634387
theorem B2059727 : Blo 2059435 2059727 := bstep (se 1 (by rfl) ⟨1544795, by rfl⟩ : syracuseStep 2059727 = 3089591) B3089591
theorem B3089597 : Blo 2059435 3089597 := bbase (se 3 (by rfl) ⟨579299, by rfl⟩ : syracuseStep 3089597 = 1158599) (by norm_num)
theorem B2059731 : Blo 2059435 2059731 := bstep (se 1 (by rfl) ⟨1544798, by rfl⟩ : syracuseStep 2059731 = 3089597) B3089597
theorem B4634405 : Blo 2059435 4634405 := bbase (se 4 (by rfl) ⟨434475, by rfl⟩ : syracuseStep 4634405 = 868951) (by norm_num)
theorem B3089603 : Blo 2059435 3089603 := bstep (se 1 (by rfl) ⟨2317202, by rfl⟩ : syracuseStep 3089603 = 4634405) B4634405
theorem B2059735 : Blo 2059435 2059735 := bstep (se 1 (by rfl) ⟨1544801, by rfl⟩ : syracuseStep 2059735 = 3089603) B3089603
theorem B5213717 : Blo 2059435 5213717 := bbase (se 6 (by rfl) ⟨122196, by rfl⟩ : syracuseStep 5213717 = 244393) (by norm_num)
theorem B3475811 : Blo 2059435 3475811 := bstep (se 1 (by rfl) ⟨2606858, by rfl⟩ : syracuseStep 3475811 = 5213717) B5213717
theorem B2317207 : Blo 2059435 2317207 := bstep (se 1 (by rfl) ⟨1737905, by rfl⟩ : syracuseStep 2317207 = 3475811) B3475811
theorem B3089609 : Blo 2059435 3089609 := bstep (se 2 (by rfl) ⟨1158603, by rfl⟩ : syracuseStep 3089609 = 2317207) B2317207
theorem B2059739 : Blo 2059435 2059739 := bstep (se 1 (by rfl) ⟨1544804, by rfl⟩ : syracuseStep 2059739 = 3089609) B3089609
theorem B8798165 : Blo 2059435 8798165 := bbase (se 7 (by rfl) ⟨103103, by rfl⟩ : syracuseStep 8798165 = 206207) (by norm_num)
theorem B5865443 : Blo 2059435 5865443 := bstep (se 1 (by rfl) ⟨4399082, by rfl⟩ : syracuseStep 5865443 = 8798165) B8798165
theorem B3910295 : Blo 2059435 3910295 := bstep (se 1 (by rfl) ⟨2932721, by rfl⟩ : syracuseStep 3910295 = 5865443) B5865443
theorem B10427453 : Blo 2059435 10427453 := bstep (se 3 (by rfl) ⟨1955147, by rfl⟩ : syracuseStep 10427453 = 3910295) B3910295
theorem B6951635 : Blo 2059435 6951635 := bstep (se 1 (by rfl) ⟨5213726, by rfl⟩ : syracuseStep 6951635 = 10427453) B10427453
theorem B4634423 : Blo 2059435 4634423 := bstep (se 1 (by rfl) ⟨3475817, by rfl⟩ : syracuseStep 4634423 = 6951635) B6951635
theorem B3089615 : Blo 2059435 3089615 := bstep (se 1 (by rfl) ⟨2317211, by rfl⟩ : syracuseStep 3089615 = 4634423) B4634423
theorem B2059743 : Blo 2059435 2059743 := bstep (se 1 (by rfl) ⟨1544807, by rfl⟩ : syracuseStep 2059743 = 3089615) B3089615
theorem B3089621 : Blo 2059435 3089621 := bbase (se 7 (by rfl) ⟨36206, by rfl⟩ : syracuseStep 3089621 = 72413) (by norm_num)
theorem B2059747 : Blo 2059435 2059747 := bstep (se 1 (by rfl) ⟨1544810, by rfl⟩ : syracuseStep 2059747 = 3089621) B3089621
theorem B2932733 : Blo 2059435 2932733 := bbase (se 3 (by rfl) ⟨549887, by rfl⟩ : syracuseStep 2932733 = 1099775) (by norm_num)
theorem B7820621 : Blo 2059435 7820621 := bstep (se 3 (by rfl) ⟨1466366, by rfl⟩ : syracuseStep 7820621 = 2932733) B2932733
theorem B5213747 : Blo 2059435 5213747 := bstep (se 1 (by rfl) ⟨3910310, by rfl⟩ : syracuseStep 5213747 = 7820621) B7820621
theorem B3475831 : Blo 2059435 3475831 := bstep (se 1 (by rfl) ⟨2606873, by rfl⟩ : syracuseStep 3475831 = 5213747) B5213747
theorem B4634441 : Blo 2059435 4634441 := bstep (se 2 (by rfl) ⟨1737915, by rfl⟩ : syracuseStep 4634441 = 3475831) B3475831
theorem B3089627 : Blo 2059435 3089627 := bstep (se 1 (by rfl) ⟨2317220, by rfl⟩ : syracuseStep 3089627 = 4634441) B4634441
theorem B2059751 : Blo 2059435 2059751 := bstep (se 1 (by rfl) ⟨1544813, by rfl⟩ : syracuseStep 2059751 = 3089627) B3089627
theorem B2317225 : Blo 2059435 2317225 := bbase (se 2 (by rfl) ⟨868959, by rfl⟩ : syracuseStep 2317225 = 1737919) (by norm_num)
theorem B3089633 : Blo 2059435 3089633 := bstep (se 2 (by rfl) ⟨1158612, by rfl⟩ : syracuseStep 3089633 = 2317225) B2317225
theorem B2059755 : Blo 2059435 2059755 := bstep (se 1 (by rfl) ⟨1544816, by rfl⟩ : syracuseStep 2059755 = 3089633) B3089633
theorem B4175725 : Blo 2059435 4175725 := bbase (se 3 (by rfl) ⟨782948, by rfl⟩ : syracuseStep 4175725 = 1565897) (by norm_num)
theorem B5567633 : Blo 2059435 5567633 := bstep (se 2 (by rfl) ⟨2087862, by rfl⟩ : syracuseStep 5567633 = 4175725) B4175725
theorem B3711755 : Blo 2059435 3711755 := bstep (se 1 (by rfl) ⟨2783816, by rfl⟩ : syracuseStep 3711755 = 5567633) B5567633
theorem B9898013 : Blo 2059435 9898013 := bstep (se 3 (by rfl) ⟨1855877, by rfl⟩ : syracuseStep 9898013 = 3711755) B3711755
theorem B6598675 : Blo 2059435 6598675 := bstep (se 1 (by rfl) ⟨4949006, by rfl⟩ : syracuseStep 6598675 = 9898013) B9898013
theorem B8798233 : Blo 2059435 8798233 := bstep (se 2 (by rfl) ⟨3299337, by rfl⟩ : syracuseStep 8798233 = 6598675) B6598675
theorem B11730977 : Blo 2059435 11730977 := bstep (se 2 (by rfl) ⟨4399116, by rfl⟩ : syracuseStep 11730977 = 8798233) B8798233
theorem B7820651 : Blo 2059435 7820651 := bstep (se 1 (by rfl) ⟨5865488, by rfl⟩ : syracuseStep 7820651 = 11730977) B11730977
theorem B5213767 : Blo 2059435 5213767 := bstep (se 1 (by rfl) ⟨3910325, by rfl⟩ : syracuseStep 5213767 = 7820651) B7820651
theorem B6951689 : Blo 2059435 6951689 := bstep (se 2 (by rfl) ⟨2606883, by rfl⟩ : syracuseStep 6951689 = 5213767) B5213767
theorem B4634459 : Blo 2059435 4634459 := bstep (se 1 (by rfl) ⟨3475844, by rfl⟩ : syracuseStep 4634459 = 6951689) B6951689
theorem B3089639 : Blo 2059435 3089639 := bstep (se 1 (by rfl) ⟨2317229, by rfl⟩ : syracuseStep 3089639 = 4634459) B4634459
theorem B2059759 : Blo 2059435 2059759 := bstep (se 1 (by rfl) ⟨1544819, by rfl⟩ : syracuseStep 2059759 = 3089639) B3089639
theorem B3089645 : Blo 2059435 3089645 := bbase (se 3 (by rfl) ⟨579308, by rfl⟩ : syracuseStep 3089645 = 1158617) (by norm_num)
theorem B2059763 : Blo 2059435 2059763 := bstep (se 1 (by rfl) ⟨1544822, by rfl⟩ : syracuseStep 2059763 = 3089645) B3089645
theorem B4634477 : Blo 2059435 4634477 := bbase (se 3 (by rfl) ⟨868964, by rfl⟩ : syracuseStep 4634477 = 1737929) (by norm_num)
theorem B3089651 : Blo 2059435 3089651 := bstep (se 1 (by rfl) ⟨2317238, by rfl⟩ : syracuseStep 3089651 = 4634477) B4634477
theorem B2059767 : Blo 2059435 2059767 := bstep (se 1 (by rfl) ⟨1544825, by rfl⟩ : syracuseStep 2059767 = 3089651) B3089651
theorem B3910349 : Blo 2059435 3910349 := bbase (se 3 (by rfl) ⟨733190, by rfl⟩ : syracuseStep 3910349 = 1466381) (by norm_num)
theorem B2606899 : Blo 2059435 2606899 := bstep (se 1 (by rfl) ⟨1955174, by rfl⟩ : syracuseStep 2606899 = 3910349) B3910349
theorem B3475865 : Blo 2059435 3475865 := bstep (se 2 (by rfl) ⟨1303449, by rfl⟩ : syracuseStep 3475865 = 2606899) B2606899
theorem B2317243 : Blo 2059435 2317243 := bstep (se 1 (by rfl) ⟨1737932, by rfl⟩ : syracuseStep 2317243 = 3475865) B3475865
theorem B3089657 : Blo 2059435 3089657 := bstep (se 2 (by rfl) ⟨1158621, by rfl⟩ : syracuseStep 3089657 = 2317243) B2317243
theorem B2059771 : Blo 2059435 2059771 := bstep (se 1 (by rfl) ⟨1544828, by rfl⟩ : syracuseStep 2059771 = 3089657) B3089657
theorem B6688757 : Blo 2059435 6688757 := bbase (se 5 (by rfl) ⟨313535, by rfl⟩ : syracuseStep 6688757 = 627071) (by norm_num)
theorem B17836685 : Blo 2059435 17836685 := bstep (se 3 (by rfl) ⟨3344378, by rfl⟩ : syracuseStep 17836685 = 6688757) B6688757
theorem B11891123 : Blo 2059435 11891123 := bstep (se 1 (by rfl) ⟨8918342, by rfl⟩ : syracuseStep 11891123 = 17836685) B17836685
theorem B7927415 : Blo 2059435 7927415 := bstep (se 1 (by rfl) ⟨5945561, by rfl⟩ : syracuseStep 7927415 = 11891123) B11891123
theorem B5284943 : Blo 2059435 5284943 := bstep (se 1 (by rfl) ⟨3963707, by rfl⟩ : syracuseStep 5284943 = 7927415) B7927415
theorem B3523295 : Blo 2059435 3523295 := bstep (se 1 (by rfl) ⟨2642471, by rfl⟩ : syracuseStep 3523295 = 5284943) B5284943
theorem B9395453 : Blo 2059435 9395453 := bstep (se 3 (by rfl) ⟨1761647, by rfl⟩ : syracuseStep 9395453 = 3523295) B3523295
theorem B6263635 : Blo 2059435 6263635 := bstep (se 1 (by rfl) ⟨4697726, by rfl⟩ : syracuseStep 6263635 = 9395453) B9395453
theorem B8351513 : Blo 2059435 8351513 := bstep (se 2 (by rfl) ⟨3131817, by rfl⟩ : syracuseStep 8351513 = 6263635) B6263635
theorem B5567675 : Blo 2059435 5567675 := bstep (se 1 (by rfl) ⟨4175756, by rfl⟩ : syracuseStep 5567675 = 8351513) B8351513
theorem B14847133 : Blo 2059435 14847133 := bstep (se 3 (by rfl) ⟨2783837, by rfl⟩ : syracuseStep 14847133 = 5567675) B5567675
theorem B19796177 : Blo 2059435 19796177 := bstep (se 2 (by rfl) ⟨7423566, by rfl⟩ : syracuseStep 19796177 = 14847133) B14847133
theorem B52789805 : Blo 2059435 52789805 := bstep (se 3 (by rfl) ⟨9898088, by rfl⟩ : syracuseStep 52789805 = 19796177) B19796177
theorem B35193203 : Blo 2059435 35193203 := bstep (se 1 (by rfl) ⟨26394902, by rfl⟩ : syracuseStep 35193203 = 52789805) B52789805
theorem B23462135 : Blo 2059435 23462135 := bstep (se 1 (by rfl) ⟨17596601, by rfl⟩ : syracuseStep 23462135 = 35193203) B35193203
theorem B15641423 : Blo 2059435 15641423 := bstep (se 1 (by rfl) ⟨11731067, by rfl⟩ : syracuseStep 15641423 = 23462135) B23462135
theorem B10427615 : Blo 2059435 10427615 := bstep (se 1 (by rfl) ⟨7820711, by rfl⟩ : syracuseStep 10427615 = 15641423) B15641423
theorem B6951743 : Blo 2059435 6951743 := bstep (se 1 (by rfl) ⟨5213807, by rfl⟩ : syracuseStep 6951743 = 10427615) B10427615
theorem B4634495 : Blo 2059435 4634495 := bstep (se 1 (by rfl) ⟨3475871, by rfl⟩ : syracuseStep 4634495 = 6951743) B6951743
theorem B3089663 : Blo 2059435 3089663 := bstep (se 1 (by rfl) ⟨2317247, by rfl⟩ : syracuseStep 3089663 = 4634495) B4634495
theorem B2059775 : Blo 2059435 2059775 := bstep (se 1 (by rfl) ⟨1544831, by rfl⟩ : syracuseStep 2059775 = 3089663) B3089663
theorem B3089669 : Blo 2059435 3089669 := bbase (se 4 (by rfl) ⟨289656, by rfl⟩ : syracuseStep 3089669 = 579313) (by norm_num)
theorem B2059779 : Blo 2059435 2059779 := bstep (se 1 (by rfl) ⟨1544834, by rfl⟩ : syracuseStep 2059779 = 3089669) B3089669
theorem B3475885 : Blo 2059435 3475885 := bbase (se 3 (by rfl) ⟨651728, by rfl⟩ : syracuseStep 3475885 = 1303457) (by norm_num)
theorem B4634513 : Blo 2059435 4634513 := bstep (se 2 (by rfl) ⟨1737942, by rfl⟩ : syracuseStep 4634513 = 3475885) B3475885
theorem B3089675 : Blo 2059435 3089675 := bstep (se 1 (by rfl) ⟨2317256, by rfl⟩ : syracuseStep 3089675 = 4634513) B4634513
theorem B2059783 : Blo 2059435 2059783 := bstep (se 1 (by rfl) ⟨1544837, by rfl⟩ : syracuseStep 2059783 = 3089675) B3089675
theorem B2317261 : Blo 2059435 2317261 := bbase (se 3 (by rfl) ⟨434486, by rfl⟩ : syracuseStep 2317261 = 868973) (by norm_num)
theorem B3089681 : Blo 2059435 3089681 := bstep (se 2 (by rfl) ⟨1158630, by rfl⟩ : syracuseStep 3089681 = 2317261) B2317261
theorem B2059787 : Blo 2059435 2059787 := bstep (se 1 (by rfl) ⟨1544840, by rfl⟩ : syracuseStep 2059787 = 3089681) B3089681
theorem B6951797 : Blo 2059435 6951797 := bbase (se 5 (by rfl) ⟨325865, by rfl⟩ : syracuseStep 6951797 = 651731) (by norm_num)
theorem B4634531 : Blo 2059435 4634531 := bstep (se 1 (by rfl) ⟨3475898, by rfl⟩ : syracuseStep 4634531 = 6951797) B6951797
theorem B3089687 : Blo 2059435 3089687 := bstep (se 1 (by rfl) ⟨2317265, by rfl⟩ : syracuseStep 3089687 = 4634531) B4634531
theorem B2059791 : Blo 2059435 2059791 := bstep (se 1 (by rfl) ⟨1544843, by rfl⟩ : syracuseStep 2059791 = 3089687) B3089687
theorem B3089693 : Blo 2059435 3089693 := bbase (se 3 (by rfl) ⟨579317, by rfl⟩ : syracuseStep 3089693 = 1158635) (by norm_num)
theorem B2059795 : Blo 2059435 2059795 := bstep (se 1 (by rfl) ⟨1544846, by rfl⟩ : syracuseStep 2059795 = 3089693) B3089693
theorem B4634549 : Blo 2059435 4634549 := bbase (se 5 (by rfl) ⟨217244, by rfl⟩ : syracuseStep 4634549 = 434489) (by norm_num)
theorem B3089699 : Blo 2059435 3089699 := bstep (se 1 (by rfl) ⟨2317274, by rfl⟩ : syracuseStep 3089699 = 4634549) B4634549
theorem B2059799 : Blo 2059435 2059799 := bstep (se 1 (by rfl) ⟨1544849, by rfl⟩ : syracuseStep 2059799 = 3089699) B3089699
theorem B2229617 : Blo 2059435 2229617 := bbase (se 2 (by rfl) ⟨836106, by rfl⟩ : syracuseStep 2229617 = 1672213) (by norm_num)
theorem B5945645 : Blo 2059435 5945645 := bstep (se 3 (by rfl) ⟨1114808, by rfl⟩ : syracuseStep 5945645 = 2229617) B2229617
theorem B3963763 : Blo 2059435 3963763 := bstep (se 1 (by rfl) ⟨2972822, by rfl⟩ : syracuseStep 3963763 = 5945645) B5945645
theorem B5285017 : Blo 2059435 5285017 := bstep (se 2 (by rfl) ⟨1981881, by rfl⟩ : syracuseStep 5285017 = 3963763) B3963763
theorem B7046689 : Blo 2059435 7046689 := bstep (se 2 (by rfl) ⟨2642508, by rfl⟩ : syracuseStep 7046689 = 5285017) B5285017
theorem B9395585 : Blo 2059435 9395585 := bstep (se 2 (by rfl) ⟨3523344, by rfl⟩ : syracuseStep 9395585 = 7046689) B7046689
theorem B6263723 : Blo 2059435 6263723 := bstep (se 1 (by rfl) ⟨4697792, by rfl⟩ : syracuseStep 6263723 = 9395585) B9395585
theorem B4175815 : Blo 2059435 4175815 := bstep (se 1 (by rfl) ⟨3131861, by rfl⟩ : syracuseStep 4175815 = 6263723) B6263723
theorem B5567753 : Blo 2059435 5567753 := bstep (se 2 (by rfl) ⟨2087907, by rfl⟩ : syracuseStep 5567753 = 4175815) B4175815
theorem B3711835 : Blo 2059435 3711835 := bstep (se 1 (by rfl) ⟨2783876, by rfl⟩ : syracuseStep 3711835 = 5567753) B5567753
theorem B4949113 : Blo 2059435 4949113 := bstep (se 2 (by rfl) ⟨1855917, by rfl⟩ : syracuseStep 4949113 = 3711835) B3711835
theorem B6598817 : Blo 2059435 6598817 := bstep (se 2 (by rfl) ⟨2474556, by rfl⟩ : syracuseStep 6598817 = 4949113) B4949113
theorem B4399211 : Blo 2059435 4399211 := bstep (se 1 (by rfl) ⟨3299408, by rfl⟩ : syracuseStep 4399211 = 6598817) B6598817
theorem B11731229 : Blo 2059435 11731229 := bstep (se 3 (by rfl) ⟨2199605, by rfl⟩ : syracuseStep 11731229 = 4399211) B4399211
theorem B7820819 : Blo 2059435 7820819 := bstep (se 1 (by rfl) ⟨5865614, by rfl⟩ : syracuseStep 7820819 = 11731229) B11731229
theorem B5213879 : Blo 2059435 5213879 := bstep (se 1 (by rfl) ⟨3910409, by rfl⟩ : syracuseStep 5213879 = 7820819) B7820819
theorem B3475919 : Blo 2059435 3475919 := bstep (se 1 (by rfl) ⟨2606939, by rfl⟩ : syracuseStep 3475919 = 5213879) B5213879
theorem B2317279 : Blo 2059435 2317279 := bstep (se 1 (by rfl) ⟨1737959, by rfl⟩ : syracuseStep 2317279 = 3475919) B3475919
theorem B3089705 : Blo 2059435 3089705 := bstep (se 2 (by rfl) ⟨1158639, by rfl⟩ : syracuseStep 3089705 = 2317279) B2317279
theorem B2059803 : Blo 2059435 2059803 := bstep (se 1 (by rfl) ⟨1544852, by rfl⟩ : syracuseStep 2059803 = 3089705) B3089705
theorem B2474561 : Blo 2059435 2474561 := bbase (se 2 (by rfl) ⟨927960, by rfl⟩ : syracuseStep 2474561 = 1855921) (by norm_num)
theorem B6598829 : Blo 2059435 6598829 := bstep (se 3 (by rfl) ⟨1237280, by rfl⟩ : syracuseStep 6598829 = 2474561) B2474561
theorem B4399219 : Blo 2059435 4399219 := bstep (se 1 (by rfl) ⟨3299414, by rfl⟩ : syracuseStep 4399219 = 6598829) B6598829
theorem B5865625 : Blo 2059435 5865625 := bstep (se 2 (by rfl) ⟨2199609, by rfl⟩ : syracuseStep 5865625 = 4399219) B4399219
theorem B7820833 : Blo 2059435 7820833 := bstep (se 2 (by rfl) ⟨2932812, by rfl⟩ : syracuseStep 7820833 = 5865625) B5865625
theorem B10427777 : Blo 2059435 10427777 := bstep (se 2 (by rfl) ⟨3910416, by rfl⟩ : syracuseStep 10427777 = 7820833) B7820833
theorem B6951851 : Blo 2059435 6951851 := bstep (se 1 (by rfl) ⟨5213888, by rfl⟩ : syracuseStep 6951851 = 10427777) B10427777
theorem B4634567 : Blo 2059435 4634567 := bstep (se 1 (by rfl) ⟨3475925, by rfl⟩ : syracuseStep 4634567 = 6951851) B6951851
theorem B3089711 : Blo 2059435 3089711 := bstep (se 1 (by rfl) ⟨2317283, by rfl⟩ : syracuseStep 3089711 = 4634567) B4634567
theorem B2059807 : Blo 2059435 2059807 := bstep (se 1 (by rfl) ⟨1544855, by rfl⟩ : syracuseStep 2059807 = 3089711) B3089711
theorem B3089717 : Blo 2059435 3089717 := bbase (se 5 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 3089717 = 289661) (by norm_num)
theorem B2059811 : Blo 2059435 2059811 := bstep (se 1 (by rfl) ⟨1544858, by rfl⟩ : syracuseStep 2059811 = 3089717) B3089717
theorem B5213909 : Blo 2059435 5213909 := bbase (se 7 (by rfl) ⟨61100, by rfl⟩ : syracuseStep 5213909 = 122201) (by norm_num)
theorem B3475939 : Blo 2059435 3475939 := bstep (se 1 (by rfl) ⟨2606954, by rfl⟩ : syracuseStep 3475939 = 5213909) B5213909
theorem B4634585 : Blo 2059435 4634585 := bstep (se 2 (by rfl) ⟨1737969, by rfl⟩ : syracuseStep 4634585 = 3475939) B3475939
theorem B3089723 : Blo 2059435 3089723 := bstep (se 1 (by rfl) ⟨2317292, by rfl⟩ : syracuseStep 3089723 = 4634585) B4634585
theorem B2059815 : Blo 2059435 2059815 := bstep (se 1 (by rfl) ⟨1544861, by rfl⟩ : syracuseStep 2059815 = 3089723) B3089723
theorem B2317297 : Blo 2059435 2317297 := bbase (se 2 (by rfl) ⟨868986, by rfl⟩ : syracuseStep 2317297 = 1737973) (by norm_num)
theorem B3089729 : Blo 2059435 3089729 := bstep (se 2 (by rfl) ⟨1158648, by rfl⟩ : syracuseStep 3089729 = 2317297) B2317297
theorem B2059819 : Blo 2059435 2059819 := bstep (se 1 (by rfl) ⟨1544864, by rfl⟩ : syracuseStep 2059819 = 3089729) B3089729
theorem B23782805 : Blo 2059435 23782805 := bbase (se 6 (by rfl) ⟨557409, by rfl⟩ : syracuseStep 23782805 = 1114819) (by norm_num)
theorem B15855203 : Blo 2059435 15855203 := bstep (se 1 (by rfl) ⟨11891402, by rfl⟩ : syracuseStep 15855203 = 23782805) B23782805
theorem B10570135 : Blo 2059435 10570135 := bstep (se 1 (by rfl) ⟨7927601, by rfl⟩ : syracuseStep 10570135 = 15855203) B15855203
theorem B14093513 : Blo 2059435 14093513 := bstep (se 2 (by rfl) ⟨5285067, by rfl⟩ : syracuseStep 14093513 = 10570135) B10570135
theorem B9395675 : Blo 2059435 9395675 := bstep (se 1 (by rfl) ⟨7046756, by rfl⟩ : syracuseStep 9395675 = 14093513) B14093513
theorem B6263783 : Blo 2059435 6263783 := bstep (se 1 (by rfl) ⟨4697837, by rfl⟩ : syracuseStep 6263783 = 9395675) B9395675
theorem B4175855 : Blo 2059435 4175855 := bstep (se 1 (by rfl) ⟨3131891, by rfl⟩ : syracuseStep 4175855 = 6263783) B6263783
theorem B2783903 : Blo 2059435 2783903 := bstep (se 1 (by rfl) ⟨2087927, by rfl⟩ : syracuseStep 2783903 = 4175855) B4175855
theorem B7423741 : Blo 2059435 7423741 := bstep (se 3 (by rfl) ⟨1391951, by rfl⟩ : syracuseStep 7423741 = 2783903) B2783903
theorem B9898321 : Blo 2059435 9898321 := bstep (se 2 (by rfl) ⟨3711870, by rfl⟩ : syracuseStep 9898321 = 7423741) B7423741
theorem B13197761 : Blo 2059435 13197761 := bstep (se 2 (by rfl) ⟨4949160, by rfl⟩ : syracuseStep 13197761 = 9898321) B9898321
theorem B8798507 : Blo 2059435 8798507 := bstep (se 1 (by rfl) ⟨6598880, by rfl⟩ : syracuseStep 8798507 = 13197761) B13197761
theorem B5865671 : Blo 2059435 5865671 := bstep (se 1 (by rfl) ⟨4399253, by rfl⟩ : syracuseStep 5865671 = 8798507) B8798507
theorem B3910447 : Blo 2059435 3910447 := bstep (se 1 (by rfl) ⟨2932835, by rfl⟩ : syracuseStep 3910447 = 5865671) B5865671
theorem B5213929 : Blo 2059435 5213929 := bstep (se 2 (by rfl) ⟨1955223, by rfl⟩ : syracuseStep 5213929 = 3910447) B3910447
theorem B6951905 : Blo 2059435 6951905 := bstep (se 2 (by rfl) ⟨2606964, by rfl⟩ : syracuseStep 6951905 = 5213929) B5213929
theorem B4634603 : Blo 2059435 4634603 := bstep (se 1 (by rfl) ⟨3475952, by rfl⟩ : syracuseStep 4634603 = 6951905) B6951905
theorem B3089735 : Blo 2059435 3089735 := bstep (se 1 (by rfl) ⟨2317301, by rfl⟩ : syracuseStep 3089735 = 4634603) B4634603
theorem B2059823 : Blo 2059435 2059823 := bstep (se 1 (by rfl) ⟨1544867, by rfl⟩ : syracuseStep 2059823 = 3089735) B3089735
theorem B3089741 : Blo 2059435 3089741 := bbase (se 3 (by rfl) ⟨579326, by rfl⟩ : syracuseStep 3089741 = 1158653) (by norm_num)
theorem B2059827 : Blo 2059435 2059827 := bstep (se 1 (by rfl) ⟨1544870, by rfl⟩ : syracuseStep 2059827 = 3089741) B3089741
theorem B4634621 : Blo 2059435 4634621 := bbase (se 3 (by rfl) ⟨868991, by rfl⟩ : syracuseStep 4634621 = 1737983) (by norm_num)
theorem B3089747 : Blo 2059435 3089747 := bstep (se 1 (by rfl) ⟨2317310, by rfl⟩ : syracuseStep 3089747 = 4634621) B4634621
theorem B2059831 : Blo 2059435 2059831 := bstep (se 1 (by rfl) ⟨1544873, by rfl⟩ : syracuseStep 2059831 = 3089747) B3089747
theorem B3475973 : Blo 2059435 3475973 := bbase (se 4 (by rfl) ⟨325872, by rfl⟩ : syracuseStep 3475973 = 651745) (by norm_num)
theorem B2317315 : Blo 2059435 2317315 := bstep (se 1 (by rfl) ⟨1737986, by rfl⟩ : syracuseStep 2317315 = 3475973) B3475973
theorem B3089753 : Blo 2059435 3089753 := bstep (se 2 (by rfl) ⟨1158657, by rfl⟩ : syracuseStep 3089753 = 2317315) B2317315
theorem B2059835 : Blo 2059435 2059835 := bstep (se 1 (by rfl) ⟨1544876, by rfl⟩ : syracuseStep 2059835 = 3089753) B3089753
theorem B15641909 : Blo 2059435 15641909 := bbase (se 5 (by rfl) ⟨733214, by rfl⟩ : syracuseStep 15641909 = 1466429) (by norm_num)
theorem B10427939 : Blo 2059435 10427939 := bstep (se 1 (by rfl) ⟨7820954, by rfl⟩ : syracuseStep 10427939 = 15641909) B15641909
theorem B6951959 : Blo 2059435 6951959 := bstep (se 1 (by rfl) ⟨5213969, by rfl⟩ : syracuseStep 6951959 = 10427939) B10427939
theorem B4634639 : Blo 2059435 4634639 := bstep (se 1 (by rfl) ⟨3475979, by rfl⟩ : syracuseStep 4634639 = 6951959) B6951959
theorem B3089759 : Blo 2059435 3089759 := bstep (se 1 (by rfl) ⟨2317319, by rfl⟩ : syracuseStep 3089759 = 4634639) B4634639
theorem B2059839 : Blo 2059435 2059839 := bstep (se 1 (by rfl) ⟨1544879, by rfl⟩ : syracuseStep 2059839 = 3089759) B3089759
theorem B3089765 : Blo 2059435 3089765 := bbase (se 4 (by rfl) ⟨289665, by rfl⟩ : syracuseStep 3089765 = 579331) (by norm_num)
theorem B2059843 : Blo 2059435 2059843 := bstep (se 1 (by rfl) ⟨1544882, by rfl⟩ : syracuseStep 2059843 = 3089765) B3089765
theorem B3910493 : Blo 2059435 3910493 := bbase (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) (by norm_num)
theorem B2606995 : Blo 2059435 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B3475993 : Blo 2059435 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B4634657 : Blo 2059435 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B3089771 : Blo 2059435 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B2059847 : Blo 2059435 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B2317333 : Blo 2059435 2317333 := bbase (se 6 (by rfl) ⟨54312, by rfl⟩ : syracuseStep 2317333 = 108625) (by norm_num)
theorem B3089777 : Blo 2059435 3089777 := bstep (se 2 (by rfl) ⟨1158666, by rfl⟩ : syracuseStep 3089777 = 2317333) B2317333
theorem B2059851 : Blo 2059435 2059851 := bstep (se 1 (by rfl) ⟨1544888, by rfl⟩ : syracuseStep 2059851 = 3089777) B3089777
theorem B2607005 : Blo 2059435 2607005 := bbase (se 3 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 2607005 = 977627) (by norm_num)
theorem B6952013 : Blo 2059435 6952013 := bstep (se 3 (by rfl) ⟨1303502, by rfl⟩ : syracuseStep 6952013 = 2607005) B2607005
theorem B4634675 : Blo 2059435 4634675 := bstep (se 1 (by rfl) ⟨3476006, by rfl⟩ : syracuseStep 4634675 = 6952013) B6952013
theorem B3089783 : Blo 2059435 3089783 := bstep (se 1 (by rfl) ⟨2317337, by rfl⟩ : syracuseStep 3089783 = 4634675) B4634675
theorem B2059855 : Blo 2059435 2059855 := bstep (se 1 (by rfl) ⟨1544891, by rfl⟩ : syracuseStep 2059855 = 3089783) B3089783
theorem B3089789 : Blo 2059435 3089789 := bbase (se 3 (by rfl) ⟨579335, by rfl⟩ : syracuseStep 3089789 = 1158671) (by norm_num)
theorem B2059859 : Blo 2059435 2059859 := bstep (se 1 (by rfl) ⟨1544894, by rfl⟩ : syracuseStep 2059859 = 3089789) B3089789
theorem B4634693 : Blo 2059435 4634693 := bbase (se 4 (by rfl) ⟨434502, by rfl⟩ : syracuseStep 4634693 = 869005) (by norm_num)
theorem B3089795 : Blo 2059435 3089795 := bstep (se 1 (by rfl) ⟨2317346, by rfl⟩ : syracuseStep 3089795 = 4634693) B4634693
theorem B2059863 : Blo 2059435 2059863 := bstep (se 1 (by rfl) ⟨1544897, by rfl⟩ : syracuseStep 2059863 = 3089795) B3089795
theorem B5865797 : Blo 2059435 5865797 := bbase (se 4 (by rfl) ⟨549918, by rfl⟩ : syracuseStep 5865797 = 1099837) (by norm_num)
theorem B3910531 : Blo 2059435 3910531 := bstep (se 1 (by rfl) ⟨2932898, by rfl⟩ : syracuseStep 3910531 = 5865797) B5865797
theorem B5214041 : Blo 2059435 5214041 := bstep (se 2 (by rfl) ⟨1955265, by rfl⟩ : syracuseStep 5214041 = 3910531) B3910531
theorem B3476027 : Blo 2059435 3476027 := bstep (se 1 (by rfl) ⟨2607020, by rfl⟩ : syracuseStep 3476027 = 5214041) B5214041
theorem B2317351 : Blo 2059435 2317351 := bstep (se 1 (by rfl) ⟨1738013, by rfl⟩ : syracuseStep 2317351 = 3476027) B3476027
theorem B3089801 : Blo 2059435 3089801 := bstep (se 2 (by rfl) ⟨1158675, by rfl⟩ : syracuseStep 3089801 = 2317351) B2317351
theorem B2059867 : Blo 2059435 2059867 := bstep (se 1 (by rfl) ⟨1544900, by rfl⟩ : syracuseStep 2059867 = 3089801) B3089801
theorem B10428101 : Blo 2059435 10428101 := bbase (se 4 (by rfl) ⟨977634, by rfl⟩ : syracuseStep 10428101 = 1955269) (by norm_num)
theorem B6952067 : Blo 2059435 6952067 := bstep (se 1 (by rfl) ⟨5214050, by rfl⟩ : syracuseStep 6952067 = 10428101) B10428101
theorem B4634711 : Blo 2059435 4634711 := bstep (se 1 (by rfl) ⟨3476033, by rfl⟩ : syracuseStep 4634711 = 6952067) B6952067
theorem B3089807 : Blo 2059435 3089807 := bstep (se 1 (by rfl) ⟨2317355, by rfl⟩ : syracuseStep 3089807 = 4634711) B4634711
theorem B2059871 : Blo 2059435 2059871 := bstep (se 1 (by rfl) ⟨1544903, by rfl⟩ : syracuseStep 2059871 = 3089807) B3089807
theorem B3089813 : Blo 2059435 3089813 := bbase (se 6 (by rfl) ⟨72417, by rfl⟩ : syracuseStep 3089813 = 144835) (by norm_num)
theorem B2059875 : Blo 2059435 2059875 := bstep (se 1 (by rfl) ⟨1544906, by rfl⟩ : syracuseStep 2059875 = 3089813) B3089813
theorem B4399373 : Blo 2059435 4399373 := bbase (se 3 (by rfl) ⟨824882, by rfl⟩ : syracuseStep 4399373 = 1649765) (by norm_num)
theorem B11731661 : Blo 2059435 11731661 := bstep (se 3 (by rfl) ⟨2199686, by rfl⟩ : syracuseStep 11731661 = 4399373) B4399373
theorem B7821107 : Blo 2059435 7821107 := bstep (se 1 (by rfl) ⟨5865830, by rfl⟩ : syracuseStep 7821107 = 11731661) B11731661
theorem B5214071 : Blo 2059435 5214071 := bstep (se 1 (by rfl) ⟨3910553, by rfl⟩ : syracuseStep 5214071 = 7821107) B7821107
theorem B3476047 : Blo 2059435 3476047 := bstep (se 1 (by rfl) ⟨2607035, by rfl⟩ : syracuseStep 3476047 = 5214071) B5214071
theorem B4634729 : Blo 2059435 4634729 := bstep (se 2 (by rfl) ⟨1738023, by rfl⟩ : syracuseStep 4634729 = 3476047) B3476047
theorem B3089819 : Blo 2059435 3089819 := bstep (se 1 (by rfl) ⟨2317364, by rfl⟩ : syracuseStep 3089819 = 4634729) B4634729
theorem B2059879 : Blo 2059435 2059879 := bstep (se 1 (by rfl) ⟨1544909, by rfl⟩ : syracuseStep 2059879 = 3089819) B3089819
theorem B2317369 : Blo 2059435 2317369 := bbase (se 2 (by rfl) ⟨869013, by rfl⟩ : syracuseStep 2317369 = 1738027) (by norm_num)
theorem B3089825 : Blo 2059435 3089825 := bstep (se 2 (by rfl) ⟨1158684, by rfl⟩ : syracuseStep 3089825 = 2317369) B2317369
theorem B2059883 : Blo 2059435 2059883 := bstep (se 1 (by rfl) ⟨1544912, by rfl⟩ : syracuseStep 2059883 = 3089825) B3089825
theorem B7423973 : Blo 2059435 7423973 := bbase (se 4 (by rfl) ⟨695997, by rfl⟩ : syracuseStep 7423973 = 1391995) (by norm_num)
theorem B4949315 : Blo 2059435 4949315 := bstep (se 1 (by rfl) ⟨3711986, by rfl⟩ : syracuseStep 4949315 = 7423973) B7423973
theorem B3299543 : Blo 2059435 3299543 := bstep (se 1 (by rfl) ⟨2474657, by rfl⟩ : syracuseStep 3299543 = 4949315) B4949315
theorem B2199695 : Blo 2059435 2199695 := bstep (se 1 (by rfl) ⟨1649771, by rfl⟩ : syracuseStep 2199695 = 3299543) B3299543
theorem B5865853 : Blo 2059435 5865853 := bstep (se 3 (by rfl) ⟨1099847, by rfl⟩ : syracuseStep 5865853 = 2199695) B2199695
theorem B7821137 : Blo 2059435 7821137 := bstep (se 2 (by rfl) ⟨2932926, by rfl⟩ : syracuseStep 7821137 = 5865853) B5865853
theorem B5214091 : Blo 2059435 5214091 := bstep (se 1 (by rfl) ⟨3910568, by rfl⟩ : syracuseStep 5214091 = 7821137) B7821137
theorem B6952121 : Blo 2059435 6952121 := bstep (se 2 (by rfl) ⟨2607045, by rfl⟩ : syracuseStep 6952121 = 5214091) B5214091
theorem B4634747 : Blo 2059435 4634747 := bstep (se 1 (by rfl) ⟨3476060, by rfl⟩ : syracuseStep 4634747 = 6952121) B6952121
theorem B3089831 : Blo 2059435 3089831 := bstep (se 1 (by rfl) ⟨2317373, by rfl⟩ : syracuseStep 3089831 = 4634747) B4634747
theorem B2059887 : Blo 2059435 2059887 := bstep (se 1 (by rfl) ⟨1544915, by rfl⟩ : syracuseStep 2059887 = 3089831) B3089831
theorem B3089837 : Blo 2059435 3089837 := bbase (se 3 (by rfl) ⟨579344, by rfl⟩ : syracuseStep 3089837 = 1158689) (by norm_num)
theorem B2059891 : Blo 2059435 2059891 := bstep (se 1 (by rfl) ⟨1544918, by rfl⟩ : syracuseStep 2059891 = 3089837) B3089837
theorem B4634765 : Blo 2059435 4634765 := bbase (se 3 (by rfl) ⟨869018, by rfl⟩ : syracuseStep 4634765 = 1738037) (by norm_num)
theorem B3089843 : Blo 2059435 3089843 := bstep (se 1 (by rfl) ⟨2317382, by rfl⟩ : syracuseStep 3089843 = 4634765) B4634765
theorem B2059895 : Blo 2059435 2059895 := bstep (se 1 (by rfl) ⟨1544921, by rfl⟩ : syracuseStep 2059895 = 3089843) B3089843
theorem B2607061 : Blo 2059435 2607061 := bbase (se 7 (by rfl) ⟨30551, by rfl⟩ : syracuseStep 2607061 = 61103) (by norm_num)
theorem B3476081 : Blo 2059435 3476081 := bstep (se 2 (by rfl) ⟨1303530, by rfl⟩ : syracuseStep 3476081 = 2607061) B2607061
theorem B2317387 : Blo 2059435 2317387 := bstep (se 1 (by rfl) ⟨1738040, by rfl⟩ : syracuseStep 2317387 = 3476081) B3476081
theorem B3089849 : Blo 2059435 3089849 := bstep (se 2 (by rfl) ⟨1158693, by rfl⟩ : syracuseStep 3089849 = 2317387) B2317387
theorem B2059899 : Blo 2059435 2059899 := bstep (se 1 (by rfl) ⟨1544924, by rfl⟩ : syracuseStep 2059899 = 3089849) B3089849
theorem B5085325 : Blo 2059435 5085325 := bbase (se 3 (by rfl) ⟨953498, by rfl⟩ : syracuseStep 5085325 = 1906997) (by norm_num)
theorem B6780433 : Blo 2059435 6780433 := bstep (se 2 (by rfl) ⟨2542662, by rfl⟩ : syracuseStep 6780433 = 5085325) B5085325
theorem B9040577 : Blo 2059435 9040577 := bstep (se 2 (by rfl) ⟨3390216, by rfl⟩ : syracuseStep 9040577 = 6780433) B6780433
theorem B24108205 : Blo 2059435 24108205 := bstep (se 3 (by rfl) ⟨4520288, by rfl⟩ : syracuseStep 24108205 = 9040577) B9040577
theorem B32144273 : Blo 2059435 32144273 := bstep (se 2 (by rfl) ⟨12054102, by rfl⟩ : syracuseStep 32144273 = 24108205) B24108205
theorem B21429515 : Blo 2059435 21429515 := bstep (se 1 (by rfl) ⟨16072136, by rfl⟩ : syracuseStep 21429515 = 32144273) B32144273
theorem B14286343 : Blo 2059435 14286343 := bstep (se 1 (by rfl) ⟨10714757, by rfl⟩ : syracuseStep 14286343 = 21429515) B21429515
theorem B19048457 : Blo 2059435 19048457 := bstep (se 2 (by rfl) ⟨7143171, by rfl⟩ : syracuseStep 19048457 = 14286343) B14286343
theorem B50795885 : Blo 2059435 50795885 := bstep (se 3 (by rfl) ⟨9524228, by rfl⟩ : syracuseStep 50795885 = 19048457) B19048457
theorem B33863923 : Blo 2059435 33863923 := bstep (se 1 (by rfl) ⟨25397942, by rfl⟩ : syracuseStep 33863923 = 50795885) B50795885
theorem B45151897 : Blo 2059435 45151897 := bstep (se 2 (by rfl) ⟨16931961, by rfl⟩ : syracuseStep 45151897 = 33863923) B33863923
theorem B60202529 : Blo 2059435 60202529 := bstep (se 2 (by rfl) ⟨22575948, by rfl⟩ : syracuseStep 60202529 = 45151897) B45151897
theorem B40135019 : Blo 2059435 40135019 := bstep (se 1 (by rfl) ⟨30101264, by rfl⟩ : syracuseStep 40135019 = 60202529) B60202529
theorem B428106869 : Blo 2059435 428106869 := bstep (se 5 (by rfl) ⟨20067509, by rfl⟩ : syracuseStep 428106869 = 40135019) B40135019
theorem B285404579 : Blo 2059435 285404579 := bstep (se 1 (by rfl) ⟨214053434, by rfl⟩ : syracuseStep 285404579 = 428106869) B428106869
theorem B190269719 : Blo 2059435 190269719 := bstep (se 1 (by rfl) ⟨142702289, by rfl⟩ : syracuseStep 190269719 = 285404579) B285404579
theorem B126846479 : Blo 2059435 126846479 := bstep (se 1 (by rfl) ⟨95134859, by rfl⟩ : syracuseStep 126846479 = 190269719) B190269719
theorem B84564319 : Blo 2059435 84564319 := bstep (se 1 (by rfl) ⟨63423239, by rfl⟩ : syracuseStep 84564319 = 126846479) B126846479
theorem B112752425 : Blo 2059435 112752425 := bstep (se 2 (by rfl) ⟨42282159, by rfl⟩ : syracuseStep 112752425 = 84564319) B84564319
theorem B300673133 : Blo 2059435 300673133 := bstep (se 3 (by rfl) ⟨56376212, by rfl⟩ : syracuseStep 300673133 = 112752425) B112752425
theorem B200448755 : Blo 2059435 200448755 := bstep (se 1 (by rfl) ⟨150336566, by rfl⟩ : syracuseStep 200448755 = 300673133) B300673133
theorem B133632503 : Blo 2059435 133632503 := bstep (se 1 (by rfl) ⟨100224377, by rfl⟩ : syracuseStep 133632503 = 200448755) B200448755
theorem B89088335 : Blo 2059435 89088335 := bstep (se 1 (by rfl) ⟨66816251, by rfl⟩ : syracuseStep 89088335 = 133632503) B133632503
theorem B59392223 : Blo 2059435 59392223 := bstep (se 1 (by rfl) ⟨44544167, by rfl⟩ : syracuseStep 59392223 = 89088335) B89088335
theorem B39594815 : Blo 2059435 39594815 := bstep (se 1 (by rfl) ⟨29696111, by rfl⟩ : syracuseStep 39594815 = 59392223) B59392223
theorem B26396543 : Blo 2059435 26396543 := bstep (se 1 (by rfl) ⟨19797407, by rfl⟩ : syracuseStep 26396543 = 39594815) B39594815
theorem B17597695 : Blo 2059435 17597695 := bstep (se 1 (by rfl) ⟨13198271, by rfl⟩ : syracuseStep 17597695 = 26396543) B26396543
theorem B23463593 : Blo 2059435 23463593 := bstep (se 2 (by rfl) ⟨8798847, by rfl⟩ : syracuseStep 23463593 = 17597695) B17597695
theorem B15642395 : Blo 2059435 15642395 := bstep (se 1 (by rfl) ⟨11731796, by rfl⟩ : syracuseStep 15642395 = 23463593) B23463593
theorem B10428263 : Blo 2059435 10428263 := bstep (se 1 (by rfl) ⟨7821197, by rfl⟩ : syracuseStep 10428263 = 15642395) B15642395
theorem B6952175 : Blo 2059435 6952175 := bstep (se 1 (by rfl) ⟨5214131, by rfl⟩ : syracuseStep 6952175 = 10428263) B10428263
theorem B4634783 : Blo 2059435 4634783 := bstep (se 1 (by rfl) ⟨3476087, by rfl⟩ : syracuseStep 4634783 = 6952175) B6952175
theorem B3089855 : Blo 2059435 3089855 := bstep (se 1 (by rfl) ⟨2317391, by rfl⟩ : syracuseStep 3089855 = 4634783) B4634783
theorem B2059903 : Blo 2059435 2059903 := bstep (se 1 (by rfl) ⟨1544927, by rfl⟩ : syracuseStep 2059903 = 3089855) B3089855
theorem B3089861 : Blo 2059435 3089861 := bbase (se 4 (by rfl) ⟨289674, by rfl⟩ : syracuseStep 3089861 = 579349) (by norm_num)
theorem B2059907 : Blo 2059435 2059907 := bstep (se 1 (by rfl) ⟨1544930, by rfl⟩ : syracuseStep 2059907 = 3089861) B3089861
theorem B3476101 : Blo 2059435 3476101 := bbase (se 4 (by rfl) ⟨325884, by rfl⟩ : syracuseStep 3476101 = 651769) (by norm_num)
theorem B4634801 : Blo 2059435 4634801 := bstep (se 2 (by rfl) ⟨1738050, by rfl⟩ : syracuseStep 4634801 = 3476101) B3476101
theorem B3089867 : Blo 2059435 3089867 := bstep (se 1 (by rfl) ⟨2317400, by rfl⟩ : syracuseStep 3089867 = 4634801) B4634801
theorem B2059911 : Blo 2059435 2059911 := bstep (se 1 (by rfl) ⟨1544933, by rfl⟩ : syracuseStep 2059911 = 3089867) B3089867
theorem B2317405 : Blo 2059435 2317405 := bbase (se 3 (by rfl) ⟨434513, by rfl⟩ : syracuseStep 2317405 = 869027) (by norm_num)
theorem B3089873 : Blo 2059435 3089873 := bstep (se 2 (by rfl) ⟨1158702, by rfl⟩ : syracuseStep 3089873 = 2317405) B2317405
theorem B2059915 : Blo 2059435 2059915 := bstep (se 1 (by rfl) ⟨1544936, by rfl⟩ : syracuseStep 2059915 = 3089873) B3089873
theorem B6952229 : Blo 2059435 6952229 := bbase (se 4 (by rfl) ⟨651771, by rfl⟩ : syracuseStep 6952229 = 1303543) (by norm_num)
theorem B4634819 : Blo 2059435 4634819 := bstep (se 1 (by rfl) ⟨3476114, by rfl⟩ : syracuseStep 4634819 = 6952229) B6952229
theorem B3089879 : Blo 2059435 3089879 := bstep (se 1 (by rfl) ⟨2317409, by rfl⟩ : syracuseStep 3089879 = 4634819) B4634819
theorem B2059919 : Blo 2059435 2059919 := bstep (se 1 (by rfl) ⟨1544939, by rfl⟩ : syracuseStep 2059919 = 3089879) B3089879
theorem B3089885 : Blo 2059435 3089885 := bbase (se 3 (by rfl) ⟨579353, by rfl⟩ : syracuseStep 3089885 = 1158707) (by norm_num)
theorem B2059923 : Blo 2059435 2059923 := bstep (se 1 (by rfl) ⟨1544942, by rfl⟩ : syracuseStep 2059923 = 3089885) B3089885
theorem B4634837 : Blo 2059435 4634837 := bbase (se 7 (by rfl) ⟨54314, by rfl⟩ : syracuseStep 4634837 = 108629) (by norm_num)
theorem B3089891 : Blo 2059435 3089891 := bstep (se 1 (by rfl) ⟨2317418, by rfl⟩ : syracuseStep 3089891 = 4634837) B4634837
theorem B2059927 : Blo 2059435 2059927 := bstep (se 1 (by rfl) ⟨1544945, by rfl⟩ : syracuseStep 2059927 = 3089891) B3089891
theorem B2088037 : Blo 2059435 2088037 := bbase (se 4 (by rfl) ⟨195753, by rfl⟩ : syracuseStep 2088037 = 391507) (by norm_num)
theorem B11136197 : Blo 2059435 11136197 := bstep (se 4 (by rfl) ⟨1044018, by rfl⟩ : syracuseStep 11136197 = 2088037) B2088037
theorem B7424131 : Blo 2059435 7424131 := bstep (se 1 (by rfl) ⟨5568098, by rfl⟩ : syracuseStep 7424131 = 11136197) B11136197
theorem B9898841 : Blo 2059435 9898841 := bstep (se 2 (by rfl) ⟨3712065, by rfl⟩ : syracuseStep 9898841 = 7424131) B7424131
theorem B6599227 : Blo 2059435 6599227 := bstep (se 1 (by rfl) ⟨4949420, by rfl⟩ : syracuseStep 6599227 = 9898841) B9898841
theorem B8798969 : Blo 2059435 8798969 := bstep (se 2 (by rfl) ⟨3299613, by rfl⟩ : syracuseStep 8798969 = 6599227) B6599227
theorem B5865979 : Blo 2059435 5865979 := bstep (se 1 (by rfl) ⟨4399484, by rfl⟩ : syracuseStep 5865979 = 8798969) B8798969
theorem B7821305 : Blo 2059435 7821305 := bstep (se 2 (by rfl) ⟨2932989, by rfl⟩ : syracuseStep 7821305 = 5865979) B5865979
theorem B5214203 : Blo 2059435 5214203 := bstep (se 1 (by rfl) ⟨3910652, by rfl⟩ : syracuseStep 5214203 = 7821305) B7821305
theorem B3476135 : Blo 2059435 3476135 := bstep (se 1 (by rfl) ⟨2607101, by rfl⟩ : syracuseStep 3476135 = 5214203) B5214203
theorem B2317423 : Blo 2059435 2317423 := bstep (se 1 (by rfl) ⟨1738067, by rfl⟩ : syracuseStep 2317423 = 3476135) B3476135
theorem B3089897 : Blo 2059435 3089897 := bstep (se 2 (by rfl) ⟨1158711, by rfl⟩ : syracuseStep 3089897 = 2317423) B2317423
theorem B2059931 : Blo 2059435 2059931 := bstep (se 1 (by rfl) ⟨1544948, by rfl⟩ : syracuseStep 2059931 = 3089897) B3089897
theorem B4949429 : Blo 2059435 4949429 := bbase (se 5 (by rfl) ⟨232004, by rfl⟩ : syracuseStep 4949429 = 464009) (by norm_num)
theorem B13198477 : Blo 2059435 13198477 := bstep (se 3 (by rfl) ⟨2474714, by rfl⟩ : syracuseStep 13198477 = 4949429) B4949429
theorem B17597969 : Blo 2059435 17597969 := bstep (se 2 (by rfl) ⟨6599238, by rfl⟩ : syracuseStep 17597969 = 13198477) B13198477
theorem B11731979 : Blo 2059435 11731979 := bstep (se 1 (by rfl) ⟨8798984, by rfl⟩ : syracuseStep 11731979 = 17597969) B17597969
theorem B7821319 : Blo 2059435 7821319 := bstep (se 1 (by rfl) ⟨5865989, by rfl⟩ : syracuseStep 7821319 = 11731979) B11731979
theorem B10428425 : Blo 2059435 10428425 := bstep (se 2 (by rfl) ⟨3910659, by rfl⟩ : syracuseStep 10428425 = 7821319) B7821319
theorem B6952283 : Blo 2059435 6952283 := bstep (se 1 (by rfl) ⟨5214212, by rfl⟩ : syracuseStep 6952283 = 10428425) B10428425
theorem B4634855 : Blo 2059435 4634855 := bstep (se 1 (by rfl) ⟨3476141, by rfl⟩ : syracuseStep 4634855 = 6952283) B6952283
theorem B3089903 : Blo 2059435 3089903 := bstep (se 1 (by rfl) ⟨2317427, by rfl⟩ : syracuseStep 3089903 = 4634855) B4634855
theorem B2059935 : Blo 2059435 2059935 := bstep (se 1 (by rfl) ⟨1544951, by rfl⟩ : syracuseStep 2059935 = 3089903) B3089903
theorem B3089909 : Blo 2059435 3089909 := bbase (se 5 (by rfl) ⟨144839, by rfl⟩ : syracuseStep 3089909 = 289679) (by norm_num)
theorem B2059939 : Blo 2059435 2059939 := bstep (se 1 (by rfl) ⟨1544954, by rfl⟩ : syracuseStep 2059939 = 3089909) B3089909
theorem B2474725 : Blo 2059435 2474725 := bbase (se 4 (by rfl) ⟨232005, by rfl⟩ : syracuseStep 2474725 = 464011) (by norm_num)
theorem B3299633 : Blo 2059435 3299633 := bstep (se 2 (by rfl) ⟨1237362, by rfl⟩ : syracuseStep 3299633 = 2474725) B2474725
theorem B2199755 : Blo 2059435 2199755 := bstep (se 1 (by rfl) ⟨1649816, by rfl⟩ : syracuseStep 2199755 = 3299633) B3299633
theorem B5866013 : Blo 2059435 5866013 := bstep (se 3 (by rfl) ⟨1099877, by rfl⟩ : syracuseStep 5866013 = 2199755) B2199755
theorem B3910675 : Blo 2059435 3910675 := bstep (se 1 (by rfl) ⟨2933006, by rfl⟩ : syracuseStep 3910675 = 5866013) B5866013
theorem B5214233 : Blo 2059435 5214233 := bstep (se 2 (by rfl) ⟨1955337, by rfl⟩ : syracuseStep 5214233 = 3910675) B3910675
theorem B3476155 : Blo 2059435 3476155 := bstep (se 1 (by rfl) ⟨2607116, by rfl⟩ : syracuseStep 3476155 = 5214233) B5214233
theorem B4634873 : Blo 2059435 4634873 := bstep (se 2 (by rfl) ⟨1738077, by rfl⟩ : syracuseStep 4634873 = 3476155) B3476155
theorem B3089915 : Blo 2059435 3089915 := bstep (se 1 (by rfl) ⟨2317436, by rfl⟩ : syracuseStep 3089915 = 4634873) B4634873
theorem B2059943 : Blo 2059435 2059943 := bstep (se 1 (by rfl) ⟨1544957, by rfl⟩ : syracuseStep 2059943 = 3089915) B3089915
theorem B2317441 : Blo 2059435 2317441 := bbase (se 2 (by rfl) ⟨869040, by rfl⟩ : syracuseStep 2317441 = 1738081) (by norm_num)
theorem B3089921 : Blo 2059435 3089921 := bstep (se 2 (by rfl) ⟨1158720, by rfl⟩ : syracuseStep 3089921 = 2317441) B2317441
theorem B2059947 : Blo 2059435 2059947 := bstep (se 1 (by rfl) ⟨1544960, by rfl⟩ : syracuseStep 2059947 = 3089921) B3089921
theorem B5214253 : Blo 2059435 5214253 := bbase (se 3 (by rfl) ⟨977672, by rfl⟩ : syracuseStep 5214253 = 1955345) (by norm_num)
theorem B6952337 : Blo 2059435 6952337 := bstep (se 2 (by rfl) ⟨2607126, by rfl⟩ : syracuseStep 6952337 = 5214253) B5214253
theorem B4634891 : Blo 2059435 4634891 := bstep (se 1 (by rfl) ⟨3476168, by rfl⟩ : syracuseStep 4634891 = 6952337) B6952337
theorem B3089927 : Blo 2059435 3089927 := bstep (se 1 (by rfl) ⟨2317445, by rfl⟩ : syracuseStep 3089927 = 4634891) B4634891
theorem B2059951 : Blo 2059435 2059951 := bstep (se 1 (by rfl) ⟨1544963, by rfl⟩ : syracuseStep 2059951 = 3089927) B3089927
theorem B3089933 : Blo 2059435 3089933 := bbase (se 3 (by rfl) ⟨579362, by rfl⟩ : syracuseStep 3089933 = 1158725) (by norm_num)
theorem B2059955 : Blo 2059435 2059955 := bstep (se 1 (by rfl) ⟨1544966, by rfl⟩ : syracuseStep 2059955 = 3089933) B3089933
theorem B4634909 : Blo 2059435 4634909 := bbase (se 3 (by rfl) ⟨869045, by rfl⟩ : syracuseStep 4634909 = 1738091) (by norm_num)
theorem B3089939 : Blo 2059435 3089939 := bstep (se 1 (by rfl) ⟨2317454, by rfl⟩ : syracuseStep 3089939 = 4634909) B4634909
theorem B2059959 : Blo 2059435 2059959 := bstep (se 1 (by rfl) ⟨1544969, by rfl⟩ : syracuseStep 2059959 = 3089939) B3089939
theorem B3476189 : Blo 2059435 3476189 := bbase (se 3 (by rfl) ⟨651785, by rfl⟩ : syracuseStep 3476189 = 1303571) (by norm_num)
theorem B2317459 : Blo 2059435 2317459 := bstep (se 1 (by rfl) ⟨1738094, by rfl⟩ : syracuseStep 2317459 = 3476189) B3476189
theorem B3089945 : Blo 2059435 3089945 := bstep (se 2 (by rfl) ⟨1158729, by rfl⟩ : syracuseStep 3089945 = 2317459) B2317459
theorem B2059963 : Blo 2059435 2059963 := bstep (se 1 (by rfl) ⟨1544972, by rfl⟩ : syracuseStep 2059963 = 3089945) B3089945
theorem B2474753 : Blo 2059435 2474753 := bbase (se 2 (by rfl) ⟨928032, by rfl⟩ : syracuseStep 2474753 = 1856065) (by norm_num)
theorem B6599341 : Blo 2059435 6599341 := bstep (se 3 (by rfl) ⟨1237376, by rfl⟩ : syracuseStep 6599341 = 2474753) B2474753
theorem B8799121 : Blo 2059435 8799121 := bstep (se 2 (by rfl) ⟨3299670, by rfl⟩ : syracuseStep 8799121 = 6599341) B6599341
theorem B11732161 : Blo 2059435 11732161 := bstep (se 2 (by rfl) ⟨4399560, by rfl⟩ : syracuseStep 11732161 = 8799121) B8799121
theorem B15642881 : Blo 2059435 15642881 := bstep (se 2 (by rfl) ⟨5866080, by rfl⟩ : syracuseStep 15642881 = 11732161) B11732161
theorem B10428587 : Blo 2059435 10428587 := bstep (se 1 (by rfl) ⟨7821440, by rfl⟩ : syracuseStep 10428587 = 15642881) B15642881
theorem B6952391 : Blo 2059435 6952391 := bstep (se 1 (by rfl) ⟨5214293, by rfl⟩ : syracuseStep 6952391 = 10428587) B10428587
theorem B4634927 : Blo 2059435 4634927 := bstep (se 1 (by rfl) ⟨3476195, by rfl⟩ : syracuseStep 4634927 = 6952391) B6952391
theorem B3089951 : Blo 2059435 3089951 := bstep (se 1 (by rfl) ⟨2317463, by rfl⟩ : syracuseStep 3089951 = 4634927) B4634927
theorem B2059967 : Blo 2059435 2059967 := bstep (se 1 (by rfl) ⟨1544975, by rfl⟩ : syracuseStep 2059967 = 3089951) B3089951
theorem B3089957 : Blo 2059435 3089957 := bbase (se 4 (by rfl) ⟨289683, by rfl⟩ : syracuseStep 3089957 = 579367) (by norm_num)
theorem B2059971 : Blo 2059435 2059971 := bstep (se 1 (by rfl) ⟨1544978, by rfl⟩ : syracuseStep 2059971 = 3089957) B3089957
theorem B2607157 : Blo 2059435 2607157 := bbase (se 5 (by rfl) ⟨122210, by rfl⟩ : syracuseStep 2607157 = 244421) (by norm_num)
theorem B3476209 : Blo 2059435 3476209 := bstep (se 2 (by rfl) ⟨1303578, by rfl⟩ : syracuseStep 3476209 = 2607157) B2607157
theorem B4634945 : Blo 2059435 4634945 := bstep (se 2 (by rfl) ⟨1738104, by rfl⟩ : syracuseStep 4634945 = 3476209) B3476209
theorem B3089963 : Blo 2059435 3089963 := bstep (se 1 (by rfl) ⟨2317472, by rfl⟩ : syracuseStep 3089963 = 4634945) B4634945
theorem B2059975 : Blo 2059435 2059975 := bstep (se 1 (by rfl) ⟨1544981, by rfl⟩ : syracuseStep 2059975 = 3089963) B3089963
theorem B2317477 : Blo 2059435 2317477 := bbase (se 4 (by rfl) ⟨217263, by rfl⟩ : syracuseStep 2317477 = 434527) (by norm_num)
theorem B3089969 : Blo 2059435 3089969 := bstep (se 2 (by rfl) ⟨1158738, by rfl⟩ : syracuseStep 3089969 = 2317477) B2317477
theorem B2059979 : Blo 2059435 2059979 := bstep (se 1 (by rfl) ⟨1544984, by rfl⟩ : syracuseStep 2059979 = 3089969) B3089969
theorem B3344717 : Blo 2059435 3344717 := bbase (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) (by norm_num)
theorem B2229811 : Blo 2059435 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B47569301 : Blo 2059435 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B31712867 : Blo 2059435 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B21141911 : Blo 2059435 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B14094607 : Blo 2059435 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B18792809 : Blo 2059435 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B12528539 : Blo 2059435 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B8352359 : Blo 2059435 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B5568239 : Blo 2059435 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B3712159 : Blo 2059435 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B19798181 : Blo 2059435 19798181 := bstep (se 4 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 19798181 = 3712159) B3712159
theorem B13198787 : Blo 2059435 13198787 := bstep (se 1 (by rfl) ⟨9899090, by rfl⟩ : syracuseStep 13198787 = 19798181) B19798181
theorem B8799191 : Blo 2059435 8799191 := bstep (se 1 (by rfl) ⟨6599393, by rfl⟩ : syracuseStep 8799191 = 13198787) B13198787
theorem B5866127 : Blo 2059435 5866127 := bstep (se 1 (by rfl) ⟨4399595, by rfl⟩ : syracuseStep 5866127 = 8799191) B8799191
theorem B3910751 : Blo 2059435 3910751 := bstep (se 1 (by rfl) ⟨2933063, by rfl⟩ : syracuseStep 3910751 = 5866127) B5866127
theorem B2607167 : Blo 2059435 2607167 := bstep (se 1 (by rfl) ⟨1955375, by rfl⟩ : syracuseStep 2607167 = 3910751) B3910751
theorem B6952445 : Blo 2059435 6952445 := bstep (se 3 (by rfl) ⟨1303583, by rfl⟩ : syracuseStep 6952445 = 2607167) B2607167
theorem B4634963 : Blo 2059435 4634963 := bstep (se 1 (by rfl) ⟨3476222, by rfl⟩ : syracuseStep 4634963 = 6952445) B6952445
theorem B3089975 : Blo 2059435 3089975 := bstep (se 1 (by rfl) ⟨2317481, by rfl⟩ : syracuseStep 3089975 = 4634963) B4634963
theorem B2059983 : Blo 2059435 2059983 := bstep (se 1 (by rfl) ⟨1544987, by rfl⟩ : syracuseStep 2059983 = 3089975) B3089975
theorem B3089981 : Blo 2059435 3089981 := bbase (se 3 (by rfl) ⟨579371, by rfl⟩ : syracuseStep 3089981 = 1158743) (by norm_num)
theorem B2059987 : Blo 2059435 2059987 := bstep (se 1 (by rfl) ⟨1544990, by rfl⟩ : syracuseStep 2059987 = 3089981) B3089981
theorem B4634981 : Blo 2059435 4634981 := bbase (se 4 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 4634981 = 869059) (by norm_num)
theorem B3089987 : Blo 2059435 3089987 := bstep (se 1 (by rfl) ⟨2317490, by rfl⟩ : syracuseStep 3089987 = 4634981) B4634981
theorem B2059991 : Blo 2059435 2059991 := bstep (se 1 (by rfl) ⟨1544993, by rfl⟩ : syracuseStep 2059991 = 3089987) B3089987
theorem B5214365 : Blo 2059435 5214365 := bbase (se 3 (by rfl) ⟨977693, by rfl⟩ : syracuseStep 5214365 = 1955387) (by norm_num)
theorem B3476243 : Blo 2059435 3476243 := bstep (se 1 (by rfl) ⟨2607182, by rfl⟩ : syracuseStep 3476243 = 5214365) B5214365
theorem B2317495 : Blo 2059435 2317495 := bstep (se 1 (by rfl) ⟨1738121, by rfl⟩ : syracuseStep 2317495 = 3476243) B3476243
theorem B3089993 : Blo 2059435 3089993 := bstep (se 2 (by rfl) ⟨1158747, by rfl⟩ : syracuseStep 3089993 = 2317495) B2317495
theorem B2059995 : Blo 2059435 2059995 := bstep (se 1 (by rfl) ⟨1544996, by rfl⟩ : syracuseStep 2059995 = 3089993) B3089993
theorem B3910781 : Blo 2059435 3910781 := bbase (se 3 (by rfl) ⟨733271, by rfl⟩ : syracuseStep 3910781 = 1466543) (by norm_num)
theorem B10428749 : Blo 2059435 10428749 := bstep (se 3 (by rfl) ⟨1955390, by rfl⟩ : syracuseStep 10428749 = 3910781) B3910781
theorem B6952499 : Blo 2059435 6952499 := bstep (se 1 (by rfl) ⟨5214374, by rfl⟩ : syracuseStep 6952499 = 10428749) B10428749
theorem B4634999 : Blo 2059435 4634999 := bstep (se 1 (by rfl) ⟨3476249, by rfl⟩ : syracuseStep 4634999 = 6952499) B6952499
theorem B3089999 : Blo 2059435 3089999 := bstep (se 1 (by rfl) ⟨2317499, by rfl⟩ : syracuseStep 3089999 = 4634999) B4634999
theorem B2059999 : Blo 2059435 2059999 := bstep (se 1 (by rfl) ⟨1544999, by rfl⟩ : syracuseStep 2059999 = 3089999) B3089999
theorem B3090005 : Blo 2059435 3090005 := bbase (se 8 (by rfl) ⟨18105, by rfl⟩ : syracuseStep 3090005 = 36211) (by norm_num)
theorem B2060003 : Blo 2059435 2060003 := bstep (se 1 (by rfl) ⟨1545002, by rfl⟩ : syracuseStep 2060003 = 3090005) B3090005
theorem B7424405 : Blo 2059435 7424405 := bbase (se 6 (by rfl) ⟨174009, by rfl⟩ : syracuseStep 7424405 = 348019) (by norm_num)
theorem B4949603 : Blo 2059435 4949603 := bstep (se 1 (by rfl) ⟨3712202, by rfl⟩ : syracuseStep 4949603 = 7424405) B7424405
theorem B3299735 : Blo 2059435 3299735 := bstep (se 1 (by rfl) ⟨2474801, by rfl⟩ : syracuseStep 3299735 = 4949603) B4949603
theorem B8799293 : Blo 2059435 8799293 := bstep (se 3 (by rfl) ⟨1649867, by rfl⟩ : syracuseStep 8799293 = 3299735) B3299735
theorem B5866195 : Blo 2059435 5866195 := bstep (se 1 (by rfl) ⟨4399646, by rfl⟩ : syracuseStep 5866195 = 8799293) B8799293
theorem B7821593 : Blo 2059435 7821593 := bstep (se 2 (by rfl) ⟨2933097, by rfl⟩ : syracuseStep 7821593 = 5866195) B5866195
theorem B5214395 : Blo 2059435 5214395 := bstep (se 1 (by rfl) ⟨3910796, by rfl⟩ : syracuseStep 5214395 = 7821593) B7821593
theorem B3476263 : Blo 2059435 3476263 := bstep (se 1 (by rfl) ⟨2607197, by rfl⟩ : syracuseStep 3476263 = 5214395) B5214395
theorem B4635017 : Blo 2059435 4635017 := bstep (se 2 (by rfl) ⟨1738131, by rfl⟩ : syracuseStep 4635017 = 3476263) B3476263
theorem B3090011 : Blo 2059435 3090011 := bstep (se 1 (by rfl) ⟨2317508, by rfl⟩ : syracuseStep 3090011 = 4635017) B4635017
theorem B2060007 : Blo 2059435 2060007 := bstep (se 1 (by rfl) ⟨1545005, by rfl⟩ : syracuseStep 2060007 = 3090011) B3090011
theorem B2317513 : Blo 2059435 2317513 := bbase (se 2 (by rfl) ⟨869067, by rfl⟩ : syracuseStep 2317513 = 1738135) (by norm_num)
theorem B3090017 : Blo 2059435 3090017 := bstep (se 2 (by rfl) ⟨1158756, by rfl⟩ : syracuseStep 3090017 = 2317513) B2317513
theorem B2060011 : Blo 2059435 2060011 := bstep (se 1 (by rfl) ⟨1545008, by rfl⟩ : syracuseStep 2060011 = 3090017) B3090017
theorem B3262141 : Blo 2059435 3262141 := bbase (se 3 (by rfl) ⟨611651, by rfl⟩ : syracuseStep 3262141 = 1223303) (by norm_num)
theorem B4349521 : Blo 2059435 4349521 := bstep (se 2 (by rfl) ⟨1631070, by rfl⟩ : syracuseStep 4349521 = 3262141) B3262141
theorem B5799361 : Blo 2059435 5799361 := bstep (se 2 (by rfl) ⟨2174760, by rfl⟩ : syracuseStep 5799361 = 4349521) B4349521
theorem B7732481 : Blo 2059435 7732481 := bstep (se 2 (by rfl) ⟨2899680, by rfl⟩ : syracuseStep 7732481 = 5799361) B5799361
theorem B20619949 : Blo 2059435 20619949 := bstep (se 3 (by rfl) ⟨3866240, by rfl⟩ : syracuseStep 20619949 = 7732481) B7732481
theorem B27493265 : Blo 2059435 27493265 := bstep (se 2 (by rfl) ⟨10309974, by rfl⟩ : syracuseStep 27493265 = 20619949) B20619949
theorem B18328843 : Blo 2059435 18328843 := bstep (se 1 (by rfl) ⟨13746632, by rfl⟩ : syracuseStep 18328843 = 27493265) B27493265
theorem B24438457 : Blo 2059435 24438457 := bstep (se 2 (by rfl) ⟨9164421, by rfl⟩ : syracuseStep 24438457 = 18328843) B18328843
theorem B32584609 : Blo 2059435 32584609 := bstep (se 2 (by rfl) ⟨12219228, by rfl⟩ : syracuseStep 32584609 = 24438457) B24438457
theorem B43446145 : Blo 2059435 43446145 := bstep (se 2 (by rfl) ⟨16292304, by rfl⟩ : syracuseStep 43446145 = 32584609) B32584609
theorem B57928193 : Blo 2059435 57928193 := bstep (se 2 (by rfl) ⟨21723072, by rfl⟩ : syracuseStep 57928193 = 43446145) B43446145
theorem B38618795 : Blo 2059435 38618795 := bstep (se 1 (by rfl) ⟨28964096, by rfl⟩ : syracuseStep 38618795 = 57928193) B57928193
theorem B25745863 : Blo 2059435 25745863 := bstep (se 1 (by rfl) ⟨19309397, by rfl⟩ : syracuseStep 25745863 = 38618795) B38618795
theorem B34327817 : Blo 2059435 34327817 := bstep (se 2 (by rfl) ⟨12872931, by rfl⟩ : syracuseStep 34327817 = 25745863) B25745863
theorem B22885211 : Blo 2059435 22885211 := bstep (se 1 (by rfl) ⟨17163908, by rfl⟩ : syracuseStep 22885211 = 34327817) B34327817
theorem B61027229 : Blo 2059435 61027229 := bstep (se 3 (by rfl) ⟨11442605, by rfl⟩ : syracuseStep 61027229 = 22885211) B22885211
theorem B162739277 : Blo 2059435 162739277 := bstep (se 3 (by rfl) ⟨30513614, by rfl⟩ : syracuseStep 162739277 = 61027229) B61027229
theorem B108492851 : Blo 2059435 108492851 := bstep (se 1 (by rfl) ⟨81369638, by rfl⟩ : syracuseStep 108492851 = 162739277) B162739277
theorem B72328567 : Blo 2059435 72328567 := bstep (se 1 (by rfl) ⟨54246425, by rfl⟩ : syracuseStep 72328567 = 108492851) B108492851
theorem B96438089 : Blo 2059435 96438089 := bstep (se 2 (by rfl) ⟨36164283, by rfl⟩ : syracuseStep 96438089 = 72328567) B72328567
theorem B64292059 : Blo 2059435 64292059 := bstep (se 1 (by rfl) ⟨48219044, by rfl⟩ : syracuseStep 64292059 = 96438089) B96438089
theorem B342890981 : Blo 2059435 342890981 := bstep (se 4 (by rfl) ⟨32146029, by rfl⟩ : syracuseStep 342890981 = 64292059) B64292059
theorem B228593987 : Blo 2059435 228593987 := bstep (se 1 (by rfl) ⟨171445490, by rfl⟩ : syracuseStep 228593987 = 342890981) B342890981
theorem B152395991 : Blo 2059435 152395991 := bstep (se 1 (by rfl) ⟨114296993, by rfl⟩ : syracuseStep 152395991 = 228593987) B228593987
theorem B101597327 : Blo 2059435 101597327 := bstep (se 1 (by rfl) ⟨76197995, by rfl⟩ : syracuseStep 101597327 = 152395991) B152395991
theorem B67731551 : Blo 2059435 67731551 := bstep (se 1 (by rfl) ⟨50798663, by rfl⟩ : syracuseStep 67731551 = 101597327) B101597327
theorem B45154367 : Blo 2059435 45154367 := bstep (se 1 (by rfl) ⟨33865775, by rfl⟩ : syracuseStep 45154367 = 67731551) B67731551
theorem B30102911 : Blo 2059435 30102911 := bstep (se 1 (by rfl) ⟨22577183, by rfl⟩ : syracuseStep 30102911 = 45154367) B45154367
theorem B20068607 : Blo 2059435 20068607 := bstep (se 1 (by rfl) ⟨15051455, by rfl⟩ : syracuseStep 20068607 = 30102911) B30102911
theorem B53516285 : Blo 2059435 53516285 := bstep (se 3 (by rfl) ⟨10034303, by rfl⟩ : syracuseStep 53516285 = 20068607) B20068607
theorem B35677523 : Blo 2059435 35677523 := bstep (se 1 (by rfl) ⟨26758142, by rfl⟩ : syracuseStep 35677523 = 53516285) B53516285
theorem B23785015 : Blo 2059435 23785015 := bstep (se 1 (by rfl) ⟨17838761, by rfl⟩ : syracuseStep 23785015 = 35677523) B35677523
theorem B31713353 : Blo 2059435 31713353 := bstep (se 2 (by rfl) ⟨11892507, by rfl⟩ : syracuseStep 31713353 = 23785015) B23785015
theorem B21142235 : Blo 2059435 21142235 := bstep (se 1 (by rfl) ⟨15856676, by rfl⟩ : syracuseStep 21142235 = 31713353) B31713353
theorem B14094823 : Blo 2059435 14094823 := bstep (se 1 (by rfl) ⟨10571117, by rfl⟩ : syracuseStep 14094823 = 21142235) B21142235
theorem B18793097 : Blo 2059435 18793097 := bstep (se 2 (by rfl) ⟨7047411, by rfl⟩ : syracuseStep 18793097 = 14094823) B14094823
theorem B12528731 : Blo 2059435 12528731 := bstep (se 1 (by rfl) ⟨9396548, by rfl⟩ : syracuseStep 12528731 = 18793097) B18793097
theorem B8352487 : Blo 2059435 8352487 := bstep (se 1 (by rfl) ⟨6264365, by rfl⟩ : syracuseStep 8352487 = 12528731) B12528731
theorem B11136649 : Blo 2059435 11136649 := bstep (se 2 (by rfl) ⟨4176243, by rfl⟩ : syracuseStep 11136649 = 8352487) B8352487
theorem B14848865 : Blo 2059435 14848865 := bstep (se 2 (by rfl) ⟨5568324, by rfl⟩ : syracuseStep 14848865 = 11136649) B11136649
theorem B9899243 : Blo 2059435 9899243 := bstep (se 1 (by rfl) ⟨7424432, by rfl⟩ : syracuseStep 9899243 = 14848865) B14848865
theorem B6599495 : Blo 2059435 6599495 := bstep (se 1 (by rfl) ⟨4949621, by rfl⟩ : syracuseStep 6599495 = 9899243) B9899243
theorem B17598653 : Blo 2059435 17598653 := bstep (se 3 (by rfl) ⟨3299747, by rfl⟩ : syracuseStep 17598653 = 6599495) B6599495
theorem B11732435 : Blo 2059435 11732435 := bstep (se 1 (by rfl) ⟨8799326, by rfl⟩ : syracuseStep 11732435 = 17598653) B17598653
theorem B7821623 : Blo 2059435 7821623 := bstep (se 1 (by rfl) ⟨5866217, by rfl⟩ : syracuseStep 7821623 = 11732435) B11732435
theorem B5214415 : Blo 2059435 5214415 := bstep (se 1 (by rfl) ⟨3910811, by rfl⟩ : syracuseStep 5214415 = 7821623) B7821623
theorem B6952553 : Blo 2059435 6952553 := bstep (se 2 (by rfl) ⟨2607207, by rfl⟩ : syracuseStep 6952553 = 5214415) B5214415
theorem B4635035 : Blo 2059435 4635035 := bstep (se 1 (by rfl) ⟨3476276, by rfl⟩ : syracuseStep 4635035 = 6952553) B6952553
theorem B3090023 : Blo 2059435 3090023 := bstep (se 1 (by rfl) ⟨2317517, by rfl⟩ : syracuseStep 3090023 = 4635035) B4635035
theorem B2060015 : Blo 2059435 2060015 := bstep (se 1 (by rfl) ⟨1545011, by rfl⟩ : syracuseStep 2060015 = 3090023) B3090023
theorem B3090029 : Blo 2059435 3090029 := bbase (se 3 (by rfl) ⟨579380, by rfl⟩ : syracuseStep 3090029 = 1158761) (by norm_num)
theorem B2060019 : Blo 2059435 2060019 := bstep (se 1 (by rfl) ⟨1545014, by rfl⟩ : syracuseStep 2060019 = 3090029) B3090029
theorem B4635053 : Blo 2059435 4635053 := bbase (se 3 (by rfl) ⟨869072, by rfl⟩ : syracuseStep 4635053 = 1738145) (by norm_num)
theorem B3090035 : Blo 2059435 3090035 := bstep (se 1 (by rfl) ⟨2317526, by rfl⟩ : syracuseStep 3090035 = 4635053) B4635053
theorem B2060023 : Blo 2059435 2060023 := bstep (se 1 (by rfl) ⟨1545017, by rfl⟩ : syracuseStep 2060023 = 3090035) B3090035
theorem B2199845 : Blo 2059435 2199845 := bbase (se 4 (by rfl) ⟨206235, by rfl⟩ : syracuseStep 2199845 = 412471) (by norm_num)
theorem B5866253 : Blo 2059435 5866253 := bstep (se 3 (by rfl) ⟨1099922, by rfl⟩ : syracuseStep 5866253 = 2199845) B2199845
theorem B3910835 : Blo 2059435 3910835 := bstep (se 1 (by rfl) ⟨2933126, by rfl⟩ : syracuseStep 3910835 = 5866253) B5866253
theorem B2607223 : Blo 2059435 2607223 := bstep (se 1 (by rfl) ⟨1955417, by rfl⟩ : syracuseStep 2607223 = 3910835) B3910835
theorem B3476297 : Blo 2059435 3476297 := bstep (se 2 (by rfl) ⟨1303611, by rfl⟩ : syracuseStep 3476297 = 2607223) B2607223
theorem B2317531 : Blo 2059435 2317531 := bstep (se 1 (by rfl) ⟨1738148, by rfl⟩ : syracuseStep 2317531 = 3476297) B3476297
theorem B3090041 : Blo 2059435 3090041 := bstep (se 2 (by rfl) ⟨1158765, by rfl⟩ : syracuseStep 3090041 = 2317531) B2317531
theorem B2060027 : Blo 2059435 2060027 := bstep (se 1 (by rfl) ⟨1545020, by rfl⟩ : syracuseStep 2060027 = 3090041) B3090041
theorem B3762893 : Blo 2059435 3762893 := bbase (se 3 (by rfl) ⟨705542, by rfl⟩ : syracuseStep 3762893 = 1411085) (by norm_num)
theorem B10034381 : Blo 2059435 10034381 := bstep (se 3 (by rfl) ⟨1881446, by rfl⟩ : syracuseStep 10034381 = 3762893) B3762893
theorem B6689587 : Blo 2059435 6689587 := bstep (se 1 (by rfl) ⟨5017190, by rfl⟩ : syracuseStep 6689587 = 10034381) B10034381
theorem B8919449 : Blo 2059435 8919449 := bstep (se 2 (by rfl) ⟨3344793, by rfl⟩ : syracuseStep 8919449 = 6689587) B6689587
theorem B5946299 : Blo 2059435 5946299 := bstep (se 1 (by rfl) ⟨4459724, by rfl⟩ : syracuseStep 5946299 = 8919449) B8919449
theorem B3964199 : Blo 2059435 3964199 := bstep (se 1 (by rfl) ⟨2973149, by rfl⟩ : syracuseStep 3964199 = 5946299) B5946299
theorem B10571197 : Blo 2059435 10571197 := bstep (se 3 (by rfl) ⟨1982099, by rfl⟩ : syracuseStep 10571197 = 3964199) B3964199
theorem B14094929 : Blo 2059435 14094929 := bstep (se 2 (by rfl) ⟨5285598, by rfl⟩ : syracuseStep 14094929 = 10571197) B10571197
theorem B37586477 : Blo 2059435 37586477 := bstep (se 3 (by rfl) ⟨7047464, by rfl⟩ : syracuseStep 37586477 = 14094929) B14094929
theorem B100230605 : Blo 2059435 100230605 := bstep (se 3 (by rfl) ⟨18793238, by rfl⟩ : syracuseStep 100230605 = 37586477) B37586477
theorem B66820403 : Blo 2059435 66820403 := bstep (se 1 (by rfl) ⟨50115302, by rfl⟩ : syracuseStep 66820403 = 100230605) B100230605
theorem B44546935 : Blo 2059435 44546935 := bstep (se 1 (by rfl) ⟨33410201, by rfl⟩ : syracuseStep 44546935 = 66820403) B66820403
theorem B59395913 : Blo 2059435 59395913 := bstep (se 2 (by rfl) ⟨22273467, by rfl⟩ : syracuseStep 59395913 = 44546935) B44546935
theorem B39597275 : Blo 2059435 39597275 := bstep (se 1 (by rfl) ⟨29697956, by rfl⟩ : syracuseStep 39597275 = 59395913) B59395913
theorem B26398183 : Blo 2059435 26398183 := bstep (se 1 (by rfl) ⟨19798637, by rfl⟩ : syracuseStep 26398183 = 39597275) B39597275
theorem B35197577 : Blo 2059435 35197577 := bstep (se 2 (by rfl) ⟨13199091, by rfl⟩ : syracuseStep 35197577 = 26398183) B26398183
theorem B23465051 : Blo 2059435 23465051 := bstep (se 1 (by rfl) ⟨17598788, by rfl⟩ : syracuseStep 23465051 = 35197577) B35197577
theorem B15643367 : Blo 2059435 15643367 := bstep (se 1 (by rfl) ⟨11732525, by rfl⟩ : syracuseStep 15643367 = 23465051) B23465051
theorem B10428911 : Blo 2059435 10428911 := bstep (se 1 (by rfl) ⟨7821683, by rfl⟩ : syracuseStep 10428911 = 15643367) B15643367
theorem B6952607 : Blo 2059435 6952607 := bstep (se 1 (by rfl) ⟨5214455, by rfl⟩ : syracuseStep 6952607 = 10428911) B10428911
theorem B4635071 : Blo 2059435 4635071 := bstep (se 1 (by rfl) ⟨3476303, by rfl⟩ : syracuseStep 4635071 = 6952607) B6952607
theorem B3090047 : Blo 2059435 3090047 := bstep (se 1 (by rfl) ⟨2317535, by rfl⟩ : syracuseStep 3090047 = 4635071) B4635071
theorem B2060031 : Blo 2059435 2060031 := bstep (se 1 (by rfl) ⟨1545023, by rfl⟩ : syracuseStep 2060031 = 3090047) B3090047
theorem B3090053 : Blo 2059435 3090053 := bbase (se 4 (by rfl) ⟨289692, by rfl⟩ : syracuseStep 3090053 = 579385) (by norm_num)
theorem B2060035 : Blo 2059435 2060035 := bstep (se 1 (by rfl) ⟨1545026, by rfl⟩ : syracuseStep 2060035 = 3090053) B3090053
theorem B3476317 : Blo 2059435 3476317 := bbase (se 3 (by rfl) ⟨651809, by rfl⟩ : syracuseStep 3476317 = 1303619) (by norm_num)
theorem B4635089 : Blo 2059435 4635089 := bstep (se 2 (by rfl) ⟨1738158, by rfl⟩ : syracuseStep 4635089 = 3476317) B3476317
theorem B3090059 : Blo 2059435 3090059 := bstep (se 1 (by rfl) ⟨2317544, by rfl⟩ : syracuseStep 3090059 = 4635089) B4635089
theorem B2060039 : Blo 2059435 2060039 := bstep (se 1 (by rfl) ⟨1545029, by rfl⟩ : syracuseStep 2060039 = 3090059) B3090059
theorem B2317549 : Blo 2059435 2317549 := bbase (se 3 (by rfl) ⟨434540, by rfl⟩ : syracuseStep 2317549 = 869081) (by norm_num)
theorem B3090065 : Blo 2059435 3090065 := bstep (se 2 (by rfl) ⟨1158774, by rfl⟩ : syracuseStep 3090065 = 2317549) B2317549
theorem B2060043 : Blo 2059435 2060043 := bstep (se 1 (by rfl) ⟨1545032, by rfl⟩ : syracuseStep 2060043 = 3090065) B3090065
theorem B6952661 : Blo 2059435 6952661 := bbase (se 7 (by rfl) ⟨81476, by rfl⟩ : syracuseStep 6952661 = 162953) (by norm_num)
theorem B4635107 : Blo 2059435 4635107 := bstep (se 1 (by rfl) ⟨3476330, by rfl⟩ : syracuseStep 4635107 = 6952661) B6952661
theorem B3090071 : Blo 2059435 3090071 := bstep (se 1 (by rfl) ⟨2317553, by rfl⟩ : syracuseStep 3090071 = 4635107) B4635107
theorem B2060047 : Blo 2059435 2060047 := bstep (se 1 (by rfl) ⟨1545035, by rfl⟩ : syracuseStep 2060047 = 3090071) B3090071
theorem B3090077 : Blo 2059435 3090077 := bbase (se 3 (by rfl) ⟨579389, by rfl⟩ : syracuseStep 3090077 = 1158779) (by norm_num)
theorem B2060051 : Blo 2059435 2060051 := bstep (se 1 (by rfl) ⟨1545038, by rfl⟩ : syracuseStep 2060051 = 3090077) B3090077
theorem B4635125 : Blo 2059435 4635125 := bbase (se 5 (by rfl) ⟨217271, by rfl⟩ : syracuseStep 4635125 = 434543) (by norm_num)
theorem B3090083 : Blo 2059435 3090083 := bstep (se 1 (by rfl) ⟨2317562, by rfl⟩ : syracuseStep 3090083 = 4635125) B4635125
theorem B2060055 : Blo 2059435 2060055 := bstep (se 1 (by rfl) ⟨1545041, by rfl⟩ : syracuseStep 2060055 = 3090083) B3090083
theorem B5357789 : Blo 2059435 5357789 := bbase (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) (by norm_num)
theorem B3571859 : Blo 2059435 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B2381239 : Blo 2059435 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B3174985 : Blo 2059435 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B4233313 : Blo 2059435 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B5644417 : Blo 2059435 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B7525889 : Blo 2059435 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B5017259 : Blo 2059435 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B3344839 : Blo 2059435 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B71356565 : Blo 2059435 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B190284173 : Blo 2059435 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B126856115 : Blo 2059435 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B84570743 : Blo 2059435 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B56380495 : Blo 2059435 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B75173993 : Blo 2059435 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B50115995 : Blo 2059435 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B33410663 : Blo 2059435 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B22273775 : Blo 2059435 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B14849183 : Blo 2059435 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B39597821 : Blo 2059435 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B26398547 : Blo 2059435 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B17599031 : Blo 2059435 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B11732687 : Blo 2059435 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B7821791 : Blo 2059435 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B5214527 : Blo 2059435 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B3476351 : Blo 2059435 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B2317567 : Blo 2059435 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B3090089 : Blo 2059435 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B2060059 : Blo 2059435 2060059 := bstep (se 1 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 2060059 = 3090089) B3090089
theorem B2474869 : Blo 2059435 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B3299825 : Blo 2059435 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B2199883 : Blo 2059435 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B2933177 : Blo 2059435 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B7821805 : Blo 2059435 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B10429073 : Blo 2059435 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B6952715 : Blo 2059435 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B4635143 : Blo 2059435 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B3090095 : Blo 2059435 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B2060063 : Blo 2059435 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B3090101 : Blo 2059435 3090101 := bbase (se 5 (by rfl) ⟨144848, by rfl⟩ : syracuseStep 3090101 = 289697) (by norm_num)
theorem B2060067 : Blo 2059435 2060067 := bstep (se 1 (by rfl) ⟨1545050, by rfl⟩ : syracuseStep 2060067 = 3090101) B3090101
theorem B5214557 : Blo 2059435 5214557 := bbase (se 3 (by rfl) ⟨977729, by rfl⟩ : syracuseStep 5214557 = 1955459) (by norm_num)
theorem B3476371 : Blo 2059435 3476371 := bstep (se 1 (by rfl) ⟨2607278, by rfl⟩ : syracuseStep 3476371 = 5214557) B5214557
theorem B4635161 : Blo 2059435 4635161 := bstep (se 2 (by rfl) ⟨1738185, by rfl⟩ : syracuseStep 4635161 = 3476371) B3476371
theorem B3090107 : Blo 2059435 3090107 := bstep (se 1 (by rfl) ⟨2317580, by rfl⟩ : syracuseStep 3090107 = 4635161) B4635161
theorem B2060071 : Blo 2059435 2060071 := bstep (se 1 (by rfl) ⟨1545053, by rfl⟩ : syracuseStep 2060071 = 3090107) B3090107
theorem B2317585 : Blo 2059435 2317585 := bbase (se 2 (by rfl) ⟨869094, by rfl⟩ : syracuseStep 2317585 = 1738189) (by norm_num)
theorem B3090113 : Blo 2059435 3090113 := bstep (se 2 (by rfl) ⟨1158792, by rfl⟩ : syracuseStep 3090113 = 2317585) B2317585
theorem B2060075 : Blo 2059435 2060075 := bstep (se 1 (by rfl) ⟨1545056, by rfl⟩ : syracuseStep 2060075 = 3090113) B3090113
theorem B3910933 : Blo 2059435 3910933 := bbase (se 6 (by rfl) ⟨91662, by rfl⟩ : syracuseStep 3910933 = 183325) (by norm_num)
theorem B5214577 : Blo 2059435 5214577 := bstep (se 2 (by rfl) ⟨1955466, by rfl⟩ : syracuseStep 5214577 = 3910933) B3910933
theorem B6952769 : Blo 2059435 6952769 := bstep (se 2 (by rfl) ⟨2607288, by rfl⟩ : syracuseStep 6952769 = 5214577) B5214577
theorem B4635179 : Blo 2059435 4635179 := bstep (se 1 (by rfl) ⟨3476384, by rfl⟩ : syracuseStep 4635179 = 6952769) B6952769
theorem B3090119 : Blo 2059435 3090119 := bstep (se 1 (by rfl) ⟨2317589, by rfl⟩ : syracuseStep 3090119 = 4635179) B4635179
theorem B2060079 : Blo 2059435 2060079 := bstep (se 1 (by rfl) ⟨1545059, by rfl⟩ : syracuseStep 2060079 = 3090119) B3090119
theorem B3090125 : Blo 2059435 3090125 := bbase (se 3 (by rfl) ⟨579398, by rfl⟩ : syracuseStep 3090125 = 1158797) (by norm_num)
theorem B2060083 : Blo 2059435 2060083 := bstep (se 1 (by rfl) ⟨1545062, by rfl⟩ : syracuseStep 2060083 = 3090125) B3090125
theorem B4635197 : Blo 2059435 4635197 := bbase (se 3 (by rfl) ⟨869099, by rfl⟩ : syracuseStep 4635197 = 1738199) (by norm_num)
theorem B3090131 : Blo 2059435 3090131 := bstep (se 1 (by rfl) ⟨2317598, by rfl⟩ : syracuseStep 3090131 = 4635197) B4635197
theorem B2060087 : Blo 2059435 2060087 := bstep (se 1 (by rfl) ⟨1545065, by rfl⟩ : syracuseStep 2060087 = 3090131) B3090131
theorem B3476405 : Blo 2059435 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B2317603 : Blo 2059435 2317603 := bstep (se 1 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 2317603 = 3476405) B3476405
theorem B3090137 : Blo 2059435 3090137 := bstep (se 2 (by rfl) ⟨1158801, by rfl⟩ : syracuseStep 3090137 = 2317603) B2317603
theorem B2060091 : Blo 2059435 2060091 := bstep (se 1 (by rfl) ⟨1545068, by rfl⟩ : syracuseStep 2060091 = 3090137) B3090137
theorem B2199917 : Blo 2059435 2199917 := bbase (se 3 (by rfl) ⟨412484, by rfl⟩ : syracuseStep 2199917 = 824969) (by norm_num)
theorem B5866445 : Blo 2059435 5866445 := bstep (se 3 (by rfl) ⟨1099958, by rfl⟩ : syracuseStep 5866445 = 2199917) B2199917
theorem B15643853 : Blo 2059435 15643853 := bstep (se 3 (by rfl) ⟨2933222, by rfl⟩ : syracuseStep 15643853 = 5866445) B5866445
theorem B10429235 : Blo 2059435 10429235 := bstep (se 1 (by rfl) ⟨7821926, by rfl⟩ : syracuseStep 10429235 = 15643853) B15643853
theorem B6952823 : Blo 2059435 6952823 := bstep (se 1 (by rfl) ⟨5214617, by rfl⟩ : syracuseStep 6952823 = 10429235) B10429235
theorem B4635215 : Blo 2059435 4635215 := bstep (se 1 (by rfl) ⟨3476411, by rfl⟩ : syracuseStep 4635215 = 6952823) B6952823
theorem B3090143 : Blo 2059435 3090143 := bstep (se 1 (by rfl) ⟨2317607, by rfl⟩ : syracuseStep 3090143 = 4635215) B4635215
theorem B2060095 : Blo 2059435 2060095 := bstep (se 1 (by rfl) ⟨1545071, by rfl⟩ : syracuseStep 2060095 = 3090143) B3090143
theorem B3090149 : Blo 2059435 3090149 := bbase (se 4 (by rfl) ⟨289701, by rfl⟩ : syracuseStep 3090149 = 579403) (by norm_num)
theorem B2060099 : Blo 2059435 2060099 := bstep (se 1 (by rfl) ⟨1545074, by rfl⟩ : syracuseStep 2060099 = 3090149) B3090149
theorem B5866469 : Blo 2059435 5866469 := bbase (se 4 (by rfl) ⟨549981, by rfl⟩ : syracuseStep 5866469 = 1099963) (by norm_num)
theorem B3910979 : Blo 2059435 3910979 := bstep (se 1 (by rfl) ⟨2933234, by rfl⟩ : syracuseStep 3910979 = 5866469) B5866469
theorem B2607319 : Blo 2059435 2607319 := bstep (se 1 (by rfl) ⟨1955489, by rfl⟩ : syracuseStep 2607319 = 3910979) B3910979
theorem B3476425 : Blo 2059435 3476425 := bstep (se 2 (by rfl) ⟨1303659, by rfl⟩ : syracuseStep 3476425 = 2607319) B2607319
theorem B4635233 : Blo 2059435 4635233 := bstep (se 2 (by rfl) ⟨1738212, by rfl⟩ : syracuseStep 4635233 = 3476425) B3476425
theorem B3090155 : Blo 2059435 3090155 := bstep (se 1 (by rfl) ⟨2317616, by rfl⟩ : syracuseStep 3090155 = 4635233) B4635233
theorem B2060103 : Blo 2059435 2060103 := bstep (se 1 (by rfl) ⟨1545077, by rfl⟩ : syracuseStep 2060103 = 3090155) B3090155
theorem B2317621 : Blo 2059435 2317621 := bbase (se 5 (by rfl) ⟨108638, by rfl⟩ : syracuseStep 2317621 = 217277) (by norm_num)
theorem B3090161 : Blo 2059435 3090161 := bstep (se 2 (by rfl) ⟨1158810, by rfl⟩ : syracuseStep 3090161 = 2317621) B2317621
theorem B2060107 : Blo 2059435 2060107 := bstep (se 1 (by rfl) ⟨1545080, by rfl⟩ : syracuseStep 2060107 = 3090161) B3090161
theorem B2607329 : Blo 2059435 2607329 := bbase (se 2 (by rfl) ⟨977748, by rfl⟩ : syracuseStep 2607329 = 1955497) (by norm_num)
theorem B6952877 : Blo 2059435 6952877 := bstep (se 3 (by rfl) ⟨1303664, by rfl⟩ : syracuseStep 6952877 = 2607329) B2607329
theorem B4635251 : Blo 2059435 4635251 := bstep (se 1 (by rfl) ⟨3476438, by rfl⟩ : syracuseStep 4635251 = 6952877) B6952877
theorem B3090167 : Blo 2059435 3090167 := bstep (se 1 (by rfl) ⟨2317625, by rfl⟩ : syracuseStep 3090167 = 4635251) B4635251
theorem B2060111 : Blo 2059435 2060111 := bstep (se 1 (by rfl) ⟨1545083, by rfl⟩ : syracuseStep 2060111 = 3090167) B3090167
theorem B3090173 : Blo 2059435 3090173 := bbase (se 3 (by rfl) ⟨579407, by rfl⟩ : syracuseStep 3090173 = 1158815) (by norm_num)
theorem B2060115 : Blo 2059435 2060115 := bstep (se 1 (by rfl) ⟨1545086, by rfl⟩ : syracuseStep 2060115 = 3090173) B3090173
theorem B4635269 : Blo 2059435 4635269 := bbase (se 4 (by rfl) ⟨434556, by rfl⟩ : syracuseStep 4635269 = 869113) (by norm_num)
theorem B3090179 : Blo 2059435 3090179 := bstep (se 1 (by rfl) ⟨2317634, by rfl⟩ : syracuseStep 3090179 = 4635269) B4635269
theorem B2060119 : Blo 2059435 2060119 := bstep (se 1 (by rfl) ⟨1545089, by rfl⟩ : syracuseStep 2060119 = 3090179) B3090179
theorem B9899765 : Blo 2059435 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B6599843 : Blo 2059435 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B4399895 : Blo 2059435 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B2933263 : Blo 2059435 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B3911017 : Blo 2059435 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B5214689 : Blo 2059435 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B3476459 : Blo 2059435 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B2317639 : Blo 2059435 2317639 := bstep (se 1 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 2317639 = 3476459) B3476459
theorem B3090185 : Blo 2059435 3090185 := bstep (se 2 (by rfl) ⟨1158819, by rfl⟩ : syracuseStep 3090185 = 2317639) B2317639
theorem B2060123 : Blo 2059435 2060123 := bstep (se 1 (by rfl) ⟨1545092, by rfl⟩ : syracuseStep 2060123 = 3090185) B3090185
theorem B10429397 : Blo 2059435 10429397 := bbase (se 7 (by rfl) ⟨122219, by rfl⟩ : syracuseStep 10429397 = 244439) (by norm_num)
theorem B6952931 : Blo 2059435 6952931 := bstep (se 1 (by rfl) ⟨5214698, by rfl⟩ : syracuseStep 6952931 = 10429397) B10429397
theorem B4635287 : Blo 2059435 4635287 := bstep (se 1 (by rfl) ⟨3476465, by rfl⟩ : syracuseStep 4635287 = 6952931) B6952931
theorem B3090191 : Blo 2059435 3090191 := bstep (se 1 (by rfl) ⟨2317643, by rfl⟩ : syracuseStep 3090191 = 4635287) B4635287
theorem B2060127 : Blo 2059435 2060127 := bstep (se 1 (by rfl) ⟨1545095, by rfl⟩ : syracuseStep 2060127 = 3090191) B3090191
theorem B3090197 : Blo 2059435 3090197 := bbase (se 6 (by rfl) ⟨72426, by rfl⟩ : syracuseStep 3090197 = 144853) (by norm_num)
theorem B2060131 : Blo 2059435 2060131 := bstep (se 1 (by rfl) ⟨1545098, by rfl⟩ : syracuseStep 2060131 = 3090197) B3090197
theorem B2542949 : Blo 2059435 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B27124789 : Blo 2059435 27124789 := bstep (se 5 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 27124789 = 2542949) B2542949
theorem B36166385 : Blo 2059435 36166385 := bstep (se 2 (by rfl) ⟨13562394, by rfl⟩ : syracuseStep 36166385 = 27124789) B27124789
theorem B96443693 : Blo 2059435 96443693 := bstep (se 3 (by rfl) ⟨18083192, by rfl⟩ : syracuseStep 96443693 = 36166385) B36166385
theorem B64295795 : Blo 2059435 64295795 := bstep (se 1 (by rfl) ⟨48221846, by rfl⟩ : syracuseStep 64295795 = 96443693) B96443693
theorem B42863863 : Blo 2059435 42863863 := bstep (se 1 (by rfl) ⟨32147897, by rfl⟩ : syracuseStep 42863863 = 64295795) B64295795
theorem B57151817 : Blo 2059435 57151817 := bstep (se 2 (by rfl) ⟨21431931, by rfl⟩ : syracuseStep 57151817 = 42863863) B42863863
theorem B38101211 : Blo 2059435 38101211 := bstep (se 1 (by rfl) ⟨28575908, by rfl⟩ : syracuseStep 38101211 = 57151817) B57151817
theorem B25400807 : Blo 2059435 25400807 := bstep (se 1 (by rfl) ⟨19050605, by rfl⟩ : syracuseStep 25400807 = 38101211) B38101211
theorem B16933871 : Blo 2059435 16933871 := bstep (se 1 (by rfl) ⟨12700403, by rfl⟩ : syracuseStep 16933871 = 25400807) B25400807
theorem B45156989 : Blo 2059435 45156989 := bstep (se 3 (by rfl) ⟨8466935, by rfl⟩ : syracuseStep 45156989 = 16933871) B16933871
theorem B30104659 : Blo 2059435 30104659 := bstep (se 1 (by rfl) ⟨22578494, by rfl⟩ : syracuseStep 30104659 = 45156989) B45156989
theorem B40139545 : Blo 2059435 40139545 := bstep (se 2 (by rfl) ⟨15052329, by rfl⟩ : syracuseStep 40139545 = 30104659) B30104659
theorem B53519393 : Blo 2059435 53519393 := bstep (se 2 (by rfl) ⟨20069772, by rfl⟩ : syracuseStep 53519393 = 40139545) B40139545
theorem B142718381 : Blo 2059435 142718381 := bstep (se 3 (by rfl) ⟨26759696, by rfl⟩ : syracuseStep 142718381 = 53519393) B53519393
theorem B95145587 : Blo 2059435 95145587 := bstep (se 1 (by rfl) ⟨71359190, by rfl⟩ : syracuseStep 95145587 = 142718381) B142718381
theorem B63430391 : Blo 2059435 63430391 := bstep (se 1 (by rfl) ⟨47572793, by rfl⟩ : syracuseStep 63430391 = 95145587) B95145587
theorem B42286927 : Blo 2059435 42286927 := bstep (se 1 (by rfl) ⟨31715195, by rfl⟩ : syracuseStep 42286927 = 63430391) B63430391
theorem B56382569 : Blo 2059435 56382569 := bstep (se 2 (by rfl) ⟨21143463, by rfl⟩ : syracuseStep 56382569 = 42286927) B42286927
theorem B37588379 : Blo 2059435 37588379 := bstep (se 1 (by rfl) ⟨28191284, by rfl⟩ : syracuseStep 37588379 = 56382569) B56382569
theorem B100235677 : Blo 2059435 100235677 := bstep (se 3 (by rfl) ⟨18794189, by rfl⟩ : syracuseStep 100235677 = 37588379) B37588379
theorem B133647569 : Blo 2059435 133647569 := bstep (se 2 (by rfl) ⟨50117838, by rfl⟩ : syracuseStep 133647569 = 100235677) B100235677
theorem B89098379 : Blo 2059435 89098379 := bstep (se 1 (by rfl) ⟨66823784, by rfl⟩ : syracuseStep 89098379 = 133647569) B133647569
theorem B59398919 : Blo 2059435 59398919 := bstep (se 1 (by rfl) ⟨44549189, by rfl⟩ : syracuseStep 59398919 = 89098379) B89098379
theorem B39599279 : Blo 2059435 39599279 := bstep (se 1 (by rfl) ⟨29699459, by rfl⟩ : syracuseStep 39599279 = 59398919) B59398919
theorem B26399519 : Blo 2059435 26399519 := bstep (se 1 (by rfl) ⟨19799639, by rfl⟩ : syracuseStep 26399519 = 39599279) B39599279
theorem B17599679 : Blo 2059435 17599679 := bstep (se 1 (by rfl) ⟨13199759, by rfl⟩ : syracuseStep 17599679 = 26399519) B26399519
theorem B11733119 : Blo 2059435 11733119 := bstep (se 1 (by rfl) ⟨8799839, by rfl⟩ : syracuseStep 11733119 = 17599679) B17599679
theorem B7822079 : Blo 2059435 7822079 := bstep (se 1 (by rfl) ⟨5866559, by rfl⟩ : syracuseStep 7822079 = 11733119) B11733119
theorem B5214719 : Blo 2059435 5214719 := bstep (se 1 (by rfl) ⟨3911039, by rfl⟩ : syracuseStep 5214719 = 7822079) B7822079
theorem B3476479 : Blo 2059435 3476479 := bstep (se 1 (by rfl) ⟨2607359, by rfl⟩ : syracuseStep 3476479 = 5214719) B5214719
theorem B4635305 : Blo 2059435 4635305 := bstep (se 2 (by rfl) ⟨1738239, by rfl⟩ : syracuseStep 4635305 = 3476479) B3476479
theorem B3090203 : Blo 2059435 3090203 := bstep (se 1 (by rfl) ⟨2317652, by rfl⟩ : syracuseStep 3090203 = 4635305) B4635305
theorem B2060135 : Blo 2059435 2060135 := bstep (se 1 (by rfl) ⟨1545101, by rfl⟩ : syracuseStep 2060135 = 3090203) B3090203
theorem B2317657 : Blo 2059435 2317657 := bbase (se 2 (by rfl) ⟨869121, by rfl⟩ : syracuseStep 2317657 = 1738243) (by norm_num)
theorem B3090209 : Blo 2059435 3090209 := bstep (se 2 (by rfl) ⟨1158828, by rfl⟩ : syracuseStep 3090209 = 2317657) B2317657
theorem B2060139 : Blo 2059435 2060139 := bstep (se 1 (by rfl) ⟨1545104, by rfl⟩ : syracuseStep 2060139 = 3090209) B3090209
theorem B2474965 : Blo 2059435 2474965 := bbase (se 7 (by rfl) ⟨29003, by rfl⟩ : syracuseStep 2474965 = 58007) (by norm_num)
theorem B3299953 : Blo 2059435 3299953 := bstep (se 2 (by rfl) ⟨1237482, by rfl⟩ : syracuseStep 3299953 = 2474965) B2474965
theorem B4399937 : Blo 2059435 4399937 := bstep (se 2 (by rfl) ⟨1649976, by rfl⟩ : syracuseStep 4399937 = 3299953) B3299953
theorem B2933291 : Blo 2059435 2933291 := bstep (se 1 (by rfl) ⟨2199968, by rfl⟩ : syracuseStep 2933291 = 4399937) B4399937
theorem B7822109 : Blo 2059435 7822109 := bstep (se 3 (by rfl) ⟨1466645, by rfl⟩ : syracuseStep 7822109 = 2933291) B2933291
theorem B5214739 : Blo 2059435 5214739 := bstep (se 1 (by rfl) ⟨3911054, by rfl⟩ : syracuseStep 5214739 = 7822109) B7822109
theorem B6952985 : Blo 2059435 6952985 := bstep (se 2 (by rfl) ⟨2607369, by rfl⟩ : syracuseStep 6952985 = 5214739) B5214739
theorem B4635323 : Blo 2059435 4635323 := bstep (se 1 (by rfl) ⟨3476492, by rfl⟩ : syracuseStep 4635323 = 6952985) B6952985
theorem B3090215 : Blo 2059435 3090215 := bstep (se 1 (by rfl) ⟨2317661, by rfl⟩ : syracuseStep 3090215 = 4635323) B4635323
theorem B2060143 : Blo 2059435 2060143 := bstep (se 1 (by rfl) ⟨1545107, by rfl⟩ : syracuseStep 2060143 = 3090215) B3090215
theorem B3090221 : Blo 2059435 3090221 := bbase (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) (by norm_num)
theorem B2060147 : Blo 2059435 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B4635341 : Blo 2059435 4635341 := bbase (se 3 (by rfl) ⟨869126, by rfl⟩ : syracuseStep 4635341 = 1738253) (by norm_num)
theorem B3090227 : Blo 2059435 3090227 := bstep (se 1 (by rfl) ⟨2317670, by rfl⟩ : syracuseStep 3090227 = 4635341) B4635341
theorem B2060151 : Blo 2059435 2060151 := bstep (se 1 (by rfl) ⟨1545113, by rfl⟩ : syracuseStep 2060151 = 3090227) B3090227
theorem B2607385 : Blo 2059435 2607385 := bbase (se 2 (by rfl) ⟨977769, by rfl⟩ : syracuseStep 2607385 = 1955539) (by norm_num)
theorem B3476513 : Blo 2059435 3476513 := bstep (se 2 (by rfl) ⟨1303692, by rfl⟩ : syracuseStep 3476513 = 2607385) B2607385
theorem B2317675 : Blo 2059435 2317675 := bstep (se 1 (by rfl) ⟨1738256, by rfl⟩ : syracuseStep 2317675 = 3476513) B3476513
theorem B3090233 : Blo 2059435 3090233 := bstep (se 2 (by rfl) ⟨1158837, by rfl⟩ : syracuseStep 3090233 = 2317675) B2317675
theorem B2060155 : Blo 2059435 2060155 := bstep (se 1 (by rfl) ⟨1545116, by rfl⟩ : syracuseStep 2060155 = 3090233) B3090233
theorem B8799941 : Blo 2059435 8799941 := bbase (se 4 (by rfl) ⟨824994, by rfl⟩ : syracuseStep 8799941 = 1649989) (by norm_num)
theorem B23466509 : Blo 2059435 23466509 := bstep (se 3 (by rfl) ⟨4399970, by rfl⟩ : syracuseStep 23466509 = 8799941) B8799941
theorem B15644339 : Blo 2059435 15644339 := bstep (se 1 (by rfl) ⟨11733254, by rfl⟩ : syracuseStep 15644339 = 23466509) B23466509
theorem B10429559 : Blo 2059435 10429559 := bstep (se 1 (by rfl) ⟨7822169, by rfl⟩ : syracuseStep 10429559 = 15644339) B15644339
theorem B6953039 : Blo 2059435 6953039 := bstep (se 1 (by rfl) ⟨5214779, by rfl⟩ : syracuseStep 6953039 = 10429559) B10429559
theorem B4635359 : Blo 2059435 4635359 := bstep (se 1 (by rfl) ⟨3476519, by rfl⟩ : syracuseStep 4635359 = 6953039) B6953039
theorem B3090239 : Blo 2059435 3090239 := bstep (se 1 (by rfl) ⟨2317679, by rfl⟩ : syracuseStep 3090239 = 4635359) B4635359
theorem B2060159 : Blo 2059435 2060159 := bstep (se 1 (by rfl) ⟨1545119, by rfl⟩ : syracuseStep 2060159 = 3090239) B3090239
theorem B3090245 : Blo 2059435 3090245 := bbase (se 4 (by rfl) ⟨289710, by rfl⟩ : syracuseStep 3090245 = 579421) (by norm_num)
theorem B2060163 : Blo 2059435 2060163 := bstep (se 1 (by rfl) ⟨1545122, by rfl⟩ : syracuseStep 2060163 = 3090245) B3090245
theorem B3476533 : Blo 2059435 3476533 := bbase (se 5 (by rfl) ⟨162962, by rfl⟩ : syracuseStep 3476533 = 325925) (by norm_num)
theorem B4635377 : Blo 2059435 4635377 := bstep (se 2 (by rfl) ⟨1738266, by rfl⟩ : syracuseStep 4635377 = 3476533) B3476533
theorem B3090251 : Blo 2059435 3090251 := bstep (se 1 (by rfl) ⟨2317688, by rfl⟩ : syracuseStep 3090251 = 4635377) B4635377
theorem B2060167 : Blo 2059435 2060167 := bstep (se 1 (by rfl) ⟨1545125, by rfl⟩ : syracuseStep 2060167 = 3090251) B3090251
theorem B2317693 : Blo 2059435 2317693 := bbase (se 3 (by rfl) ⟨434567, by rfl⟩ : syracuseStep 2317693 = 869135) (by norm_num)
theorem B3090257 : Blo 2059435 3090257 := bstep (se 2 (by rfl) ⟨1158846, by rfl⟩ : syracuseStep 3090257 = 2317693) B2317693
theorem B2060171 : Blo 2059435 2060171 := bstep (se 1 (by rfl) ⟨1545128, by rfl⟩ : syracuseStep 2060171 = 3090257) B3090257
theorem B6953093 : Blo 2059435 6953093 := bbase (se 4 (by rfl) ⟨651852, by rfl⟩ : syracuseStep 6953093 = 1303705) (by norm_num)
theorem B4635395 : Blo 2059435 4635395 := bstep (se 1 (by rfl) ⟨3476546, by rfl⟩ : syracuseStep 4635395 = 6953093) B6953093
theorem B3090263 : Blo 2059435 3090263 := bstep (se 1 (by rfl) ⟨2317697, by rfl⟩ : syracuseStep 3090263 = 4635395) B4635395
theorem B2060175 : Blo 2059435 2060175 := bstep (se 1 (by rfl) ⟨1545131, by rfl⟩ : syracuseStep 2060175 = 3090263) B3090263
theorem B3090269 : Blo 2059435 3090269 := bbase (se 3 (by rfl) ⟨579425, by rfl⟩ : syracuseStep 3090269 = 1158851) (by norm_num)
theorem B2060179 : Blo 2059435 2060179 := bstep (se 1 (by rfl) ⟨1545134, by rfl⟩ : syracuseStep 2060179 = 3090269) B3090269
theorem B4635413 : Blo 2059435 4635413 := bbase (se 6 (by rfl) ⟨108642, by rfl⟩ : syracuseStep 4635413 = 217285) (by norm_num)
theorem B3090275 : Blo 2059435 3090275 := bstep (se 1 (by rfl) ⟨2317706, by rfl⟩ : syracuseStep 3090275 = 4635413) B4635413
theorem B2060183 : Blo 2059435 2060183 := bstep (se 1 (by rfl) ⟨1545137, by rfl⟩ : syracuseStep 2060183 = 3090275) B3090275
theorem B7822277 : Blo 2059435 7822277 := bbase (se 4 (by rfl) ⟨733338, by rfl⟩ : syracuseStep 7822277 = 1466677) (by norm_num)
theorem B5214851 : Blo 2059435 5214851 := bstep (se 1 (by rfl) ⟨3911138, by rfl⟩ : syracuseStep 5214851 = 7822277) B7822277
theorem B3476567 : Blo 2059435 3476567 := bstep (se 1 (by rfl) ⟨2607425, by rfl⟩ : syracuseStep 3476567 = 5214851) B5214851
theorem B2317711 : Blo 2059435 2317711 := bstep (se 1 (by rfl) ⟨1738283, by rfl⟩ : syracuseStep 2317711 = 3476567) B3476567
theorem B3090281 : Blo 2059435 3090281 := bstep (se 2 (by rfl) ⟨1158855, by rfl⟩ : syracuseStep 3090281 = 2317711) B2317711
theorem B2060187 : Blo 2059435 2060187 := bstep (se 1 (by rfl) ⟨1545140, by rfl⟩ : syracuseStep 2060187 = 3090281) B3090281
theorem B6264901 : Blo 2059435 6264901 := bbase (se 4 (by rfl) ⟨587334, by rfl⟩ : syracuseStep 6264901 = 1174669) (by norm_num)
theorem B8353201 : Blo 2059435 8353201 := bstep (se 2 (by rfl) ⟨3132450, by rfl⟩ : syracuseStep 8353201 = 6264901) B6264901
theorem B11137601 : Blo 2059435 11137601 := bstep (se 2 (by rfl) ⟨4176600, by rfl⟩ : syracuseStep 11137601 = 8353201) B8353201
theorem B7425067 : Blo 2059435 7425067 := bstep (se 1 (by rfl) ⟨5568800, by rfl⟩ : syracuseStep 7425067 = 11137601) B11137601
theorem B9900089 : Blo 2059435 9900089 := bstep (se 2 (by rfl) ⟨3712533, by rfl⟩ : syracuseStep 9900089 = 7425067) B7425067
theorem B6600059 : Blo 2059435 6600059 := bstep (se 1 (by rfl) ⟨4950044, by rfl⟩ : syracuseStep 6600059 = 9900089) B9900089
theorem B4400039 : Blo 2059435 4400039 := bstep (se 1 (by rfl) ⟨3300029, by rfl⟩ : syracuseStep 4400039 = 6600059) B6600059
theorem B11733437 : Blo 2059435 11733437 := bstep (se 3 (by rfl) ⟨2200019, by rfl⟩ : syracuseStep 11733437 = 4400039) B4400039
theorem B7822291 : Blo 2059435 7822291 := bstep (se 1 (by rfl) ⟨5866718, by rfl⟩ : syracuseStep 7822291 = 11733437) B11733437
theorem B10429721 : Blo 2059435 10429721 := bstep (se 2 (by rfl) ⟨3911145, by rfl⟩ : syracuseStep 10429721 = 7822291) B7822291
theorem B6953147 : Blo 2059435 6953147 := bstep (se 1 (by rfl) ⟨5214860, by rfl⟩ : syracuseStep 6953147 = 10429721) B10429721
theorem B4635431 : Blo 2059435 4635431 := bstep (se 1 (by rfl) ⟨3476573, by rfl⟩ : syracuseStep 4635431 = 6953147) B6953147
theorem B3090287 : Blo 2059435 3090287 := bstep (se 1 (by rfl) ⟨2317715, by rfl⟩ : syracuseStep 3090287 = 4635431) B4635431
theorem B2060191 : Blo 2059435 2060191 := bstep (se 1 (by rfl) ⟨1545143, by rfl⟩ : syracuseStep 2060191 = 3090287) B3090287
theorem B3090293 : Blo 2059435 3090293 := bbase (se 5 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 3090293 = 289715) (by norm_num)
theorem B2060195 : Blo 2059435 2060195 := bstep (se 1 (by rfl) ⟨1545146, by rfl⟩ : syracuseStep 2060195 = 3090293) B3090293
theorem B3712549 : Blo 2059435 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B4950065 : Blo 2059435 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B3300043 : Blo 2059435 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B4400057 : Blo 2059435 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B2933371 : Blo 2059435 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B3911161 : Blo 2059435 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B5214881 : Blo 2059435 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B3476587 : Blo 2059435 3476587 := bstep (se 1 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 3476587 = 5214881) B5214881
theorem B4635449 : Blo 2059435 4635449 := bstep (se 2 (by rfl) ⟨1738293, by rfl⟩ : syracuseStep 4635449 = 3476587) B3476587
theorem B3090299 : Blo 2059435 3090299 := bstep (se 1 (by rfl) ⟨2317724, by rfl⟩ : syracuseStep 3090299 = 4635449) B4635449
theorem B2060199 : Blo 2059435 2060199 := bstep (se 1 (by rfl) ⟨1545149, by rfl⟩ : syracuseStep 2060199 = 3090299) B3090299
theorem B2317729 : Blo 2059435 2317729 := bbase (se 2 (by rfl) ⟨869148, by rfl⟩ : syracuseStep 2317729 = 1738297) (by norm_num)
theorem B3090305 : Blo 2059435 3090305 := bstep (se 2 (by rfl) ⟨1158864, by rfl⟩ : syracuseStep 3090305 = 2317729) B2317729
theorem B2060203 : Blo 2059435 2060203 := bstep (se 1 (by rfl) ⟨1545152, by rfl⟩ : syracuseStep 2060203 = 3090305) B3090305
theorem B5214901 : Blo 2059435 5214901 := bbase (se 5 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 5214901 = 488897) (by norm_num)
theorem B6953201 : Blo 2059435 6953201 := bstep (se 2 (by rfl) ⟨2607450, by rfl⟩ : syracuseStep 6953201 = 5214901) B5214901
theorem B4635467 : Blo 2059435 4635467 := bstep (se 1 (by rfl) ⟨3476600, by rfl⟩ : syracuseStep 4635467 = 6953201) B6953201
theorem B3090311 : Blo 2059435 3090311 := bstep (se 1 (by rfl) ⟨2317733, by rfl⟩ : syracuseStep 3090311 = 4635467) B4635467
theorem B2060207 : Blo 2059435 2060207 := bstep (se 1 (by rfl) ⟨1545155, by rfl⟩ : syracuseStep 2060207 = 3090311) B3090311
theorem B3090317 : Blo 2059435 3090317 := bbase (se 3 (by rfl) ⟨579434, by rfl⟩ : syracuseStep 3090317 = 1158869) (by norm_num)
theorem B2060211 : Blo 2059435 2060211 := bstep (se 1 (by rfl) ⟨1545158, by rfl⟩ : syracuseStep 2060211 = 3090317) B3090317
theorem B4635485 : Blo 2059435 4635485 := bbase (se 3 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 4635485 = 1738307) (by norm_num)
theorem B3090323 : Blo 2059435 3090323 := bstep (se 1 (by rfl) ⟨2317742, by rfl⟩ : syracuseStep 3090323 = 4635485) B4635485
theorem B2060215 : Blo 2059435 2060215 := bstep (se 1 (by rfl) ⟨1545161, by rfl⟩ : syracuseStep 2060215 = 3090323) B3090323
theorem B3476621 : Blo 2059435 3476621 := bbase (se 3 (by rfl) ⟨651866, by rfl⟩ : syracuseStep 3476621 = 1303733) (by norm_num)
theorem B2317747 : Blo 2059435 2317747 := bstep (se 1 (by rfl) ⟨1738310, by rfl⟩ : syracuseStep 2317747 = 3476621) B3476621
theorem B3090329 : Blo 2059435 3090329 := bstep (se 2 (by rfl) ⟨1158873, by rfl⟩ : syracuseStep 3090329 = 2317747) B2317747
theorem B2060219 : Blo 2059435 2060219 := bstep (se 1 (by rfl) ⟨1545164, by rfl⟩ : syracuseStep 2060219 = 3090329) B3090329
theorem B4698749 : Blo 2059435 4698749 := bbase (se 3 (by rfl) ⟨881015, by rfl⟩ : syracuseStep 4698749 = 1762031) (by norm_num)
theorem B12529997 : Blo 2059435 12529997 := bstep (se 3 (by rfl) ⟨2349374, by rfl⟩ : syracuseStep 12529997 = 4698749) B4698749
theorem B8353331 : Blo 2059435 8353331 := bstep (se 1 (by rfl) ⟨6264998, by rfl⟩ : syracuseStep 8353331 = 12529997) B12529997
theorem B5568887 : Blo 2059435 5568887 := bstep (se 1 (by rfl) ⟨4176665, by rfl⟩ : syracuseStep 5568887 = 8353331) B8353331
theorem B3712591 : Blo 2059435 3712591 := bstep (se 1 (by rfl) ⟨2784443, by rfl⟩ : syracuseStep 3712591 = 5568887) B5568887
theorem B4950121 : Blo 2059435 4950121 := bstep (se 2 (by rfl) ⟨1856295, by rfl⟩ : syracuseStep 4950121 = 3712591) B3712591
theorem B6600161 : Blo 2059435 6600161 := bstep (se 2 (by rfl) ⟨2475060, by rfl⟩ : syracuseStep 6600161 = 4950121) B4950121
theorem B17600429 : Blo 2059435 17600429 := bstep (se 3 (by rfl) ⟨3300080, by rfl⟩ : syracuseStep 17600429 = 6600161) B6600161
theorem B11733619 : Blo 2059435 11733619 := bstep (se 1 (by rfl) ⟨8800214, by rfl⟩ : syracuseStep 11733619 = 17600429) B17600429
theorem B15644825 : Blo 2059435 15644825 := bstep (se 2 (by rfl) ⟨5866809, by rfl⟩ : syracuseStep 15644825 = 11733619) B11733619
theorem B10429883 : Blo 2059435 10429883 := bstep (se 1 (by rfl) ⟨7822412, by rfl⟩ : syracuseStep 10429883 = 15644825) B15644825
theorem B6953255 : Blo 2059435 6953255 := bstep (se 1 (by rfl) ⟨5214941, by rfl⟩ : syracuseStep 6953255 = 10429883) B10429883
theorem B4635503 : Blo 2059435 4635503 := bstep (se 1 (by rfl) ⟨3476627, by rfl⟩ : syracuseStep 4635503 = 6953255) B6953255
theorem B3090335 : Blo 2059435 3090335 := bstep (se 1 (by rfl) ⟨2317751, by rfl⟩ : syracuseStep 3090335 = 4635503) B4635503
theorem B2060223 : Blo 2059435 2060223 := bstep (se 1 (by rfl) ⟨1545167, by rfl⟩ : syracuseStep 2060223 = 3090335) B3090335
theorem B3090341 : Blo 2059435 3090341 := bbase (se 4 (by rfl) ⟨289719, by rfl⟩ : syracuseStep 3090341 = 579439) (by norm_num)
theorem B2060227 : Blo 2059435 2060227 := bstep (se 1 (by rfl) ⟨1545170, by rfl⟩ : syracuseStep 2060227 = 3090341) B3090341
theorem B2607481 : Blo 2059435 2607481 := bbase (se 2 (by rfl) ⟨977805, by rfl⟩ : syracuseStep 2607481 = 1955611) (by norm_num)
theorem B3476641 : Blo 2059435 3476641 := bstep (se 2 (by rfl) ⟨1303740, by rfl⟩ : syracuseStep 3476641 = 2607481) B2607481
theorem B4635521 : Blo 2059435 4635521 := bstep (se 2 (by rfl) ⟨1738320, by rfl⟩ : syracuseStep 4635521 = 3476641) B3476641
theorem B3090347 : Blo 2059435 3090347 := bstep (se 1 (by rfl) ⟨2317760, by rfl⟩ : syracuseStep 3090347 = 4635521) B4635521
theorem B2060231 : Blo 2059435 2060231 := bstep (se 1 (by rfl) ⟨1545173, by rfl⟩ : syracuseStep 2060231 = 3090347) B3090347
theorem B2317765 : Blo 2059435 2317765 := bbase (se 4 (by rfl) ⟨217290, by rfl⟩ : syracuseStep 2317765 = 434581) (by norm_num)
theorem B3090353 : Blo 2059435 3090353 := bstep (se 2 (by rfl) ⟨1158882, by rfl⟩ : syracuseStep 3090353 = 2317765) B2317765
theorem B2060235 : Blo 2059435 2060235 := bstep (se 1 (by rfl) ⟨1545176, by rfl⟩ : syracuseStep 2060235 = 3090353) B3090353
theorem B3911237 : Blo 2059435 3911237 := bbase (se 4 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 3911237 = 733357) (by norm_num)
theorem B2607491 : Blo 2059435 2607491 := bstep (se 1 (by rfl) ⟨1955618, by rfl⟩ : syracuseStep 2607491 = 3911237) B3911237
theorem B6953309 : Blo 2059435 6953309 := bstep (se 3 (by rfl) ⟨1303745, by rfl⟩ : syracuseStep 6953309 = 2607491) B2607491
theorem B4635539 : Blo 2059435 4635539 := bstep (se 1 (by rfl) ⟨3476654, by rfl⟩ : syracuseStep 4635539 = 6953309) B6953309
theorem B3090359 : Blo 2059435 3090359 := bstep (se 1 (by rfl) ⟨2317769, by rfl⟩ : syracuseStep 3090359 = 4635539) B4635539
theorem B2060239 : Blo 2059435 2060239 := bstep (se 1 (by rfl) ⟨1545179, by rfl⟩ : syracuseStep 2060239 = 3090359) B3090359
theorem B3090365 : Blo 2059435 3090365 := bbase (se 3 (by rfl) ⟨579443, by rfl⟩ : syracuseStep 3090365 = 1158887) (by norm_num)
theorem B2060243 : Blo 2059435 2060243 := bstep (se 1 (by rfl) ⟨1545182, by rfl⟩ : syracuseStep 2060243 = 3090365) B3090365
theorem B4635557 : Blo 2059435 4635557 := bbase (se 4 (by rfl) ⟨434583, by rfl⟩ : syracuseStep 4635557 = 869167) (by norm_num)
theorem B3090371 : Blo 2059435 3090371 := bstep (se 1 (by rfl) ⟨2317778, by rfl⟩ : syracuseStep 3090371 = 4635557) B4635557
theorem B2060247 : Blo 2059435 2060247 := bstep (se 1 (by rfl) ⟨1545185, by rfl⟩ : syracuseStep 2060247 = 3090371) B3090371
theorem B5215013 : Blo 2059435 5215013 := bbase (se 4 (by rfl) ⟨488907, by rfl⟩ : syracuseStep 5215013 = 977815) (by norm_num)
theorem B3476675 : Blo 2059435 3476675 := bstep (se 1 (by rfl) ⟨2607506, by rfl⟩ : syracuseStep 3476675 = 5215013) B5215013
theorem B2317783 : Blo 2059435 2317783 := bstep (se 1 (by rfl) ⟨1738337, by rfl⟩ : syracuseStep 2317783 = 3476675) B3476675
theorem B3090377 : Blo 2059435 3090377 := bstep (se 2 (by rfl) ⟨1158891, by rfl⟩ : syracuseStep 3090377 = 2317783) B2317783
theorem B2060251 : Blo 2059435 2060251 := bstep (se 1 (by rfl) ⟨1545188, by rfl⟩ : syracuseStep 2060251 = 3090377) B3090377
theorem B5866901 : Blo 2059435 5866901 := bbase (se 6 (by rfl) ⟨137505, by rfl⟩ : syracuseStep 5866901 = 275011) (by norm_num)
theorem B3911267 : Blo 2059435 3911267 := bstep (se 1 (by rfl) ⟨2933450, by rfl⟩ : syracuseStep 3911267 = 5866901) B5866901
theorem B10430045 : Blo 2059435 10430045 := bstep (se 3 (by rfl) ⟨1955633, by rfl⟩ : syracuseStep 10430045 = 3911267) B3911267
theorem B6953363 : Blo 2059435 6953363 := bstep (se 1 (by rfl) ⟨5215022, by rfl⟩ : syracuseStep 6953363 = 10430045) B10430045
theorem B4635575 : Blo 2059435 4635575 := bstep (se 1 (by rfl) ⟨3476681, by rfl⟩ : syracuseStep 4635575 = 6953363) B6953363
theorem B3090383 : Blo 2059435 3090383 := bstep (se 1 (by rfl) ⟨2317787, by rfl⟩ : syracuseStep 3090383 = 4635575) B4635575
theorem B2060255 : Blo 2059435 2060255 := bstep (se 1 (by rfl) ⟨1545191, by rfl⟩ : syracuseStep 2060255 = 3090383) B3090383
theorem B3090389 : Blo 2059435 3090389 := bbase (se 7 (by rfl) ⟨36215, by rfl⟩ : syracuseStep 3090389 = 72431) (by norm_num)
theorem B2060259 : Blo 2059435 2060259 := bstep (se 1 (by rfl) ⟨1545194, by rfl⟩ : syracuseStep 2060259 = 3090389) B3090389
theorem B7822565 : Blo 2059435 7822565 := bbase (se 4 (by rfl) ⟨733365, by rfl⟩ : syracuseStep 7822565 = 1466731) (by norm_num)
theorem B5215043 : Blo 2059435 5215043 := bstep (se 1 (by rfl) ⟨3911282, by rfl⟩ : syracuseStep 5215043 = 7822565) B7822565
theorem B3476695 : Blo 2059435 3476695 := bstep (se 1 (by rfl) ⟨2607521, by rfl⟩ : syracuseStep 3476695 = 5215043) B5215043
theorem B4635593 : Blo 2059435 4635593 := bstep (se 2 (by rfl) ⟨1738347, by rfl⟩ : syracuseStep 4635593 = 3476695) B3476695
theorem B3090395 : Blo 2059435 3090395 := bstep (se 1 (by rfl) ⟨2317796, by rfl⟩ : syracuseStep 3090395 = 4635593) B4635593
theorem B2060263 : Blo 2059435 2060263 := bstep (se 1 (by rfl) ⟨1545197, by rfl⟩ : syracuseStep 2060263 = 3090395) B3090395
theorem B2317801 : Blo 2059435 2317801 := bbase (se 2 (by rfl) ⟨869175, by rfl⟩ : syracuseStep 2317801 = 1738351) (by norm_num)
theorem B3090401 : Blo 2059435 3090401 := bstep (se 2 (by rfl) ⟨1158900, by rfl⟩ : syracuseStep 3090401 = 2317801) B2317801
theorem B2060267 : Blo 2059435 2060267 := bstep (se 1 (by rfl) ⟨1545200, by rfl⟩ : syracuseStep 2060267 = 3090401) B3090401
theorem B2200105 : Blo 2059435 2200105 := bbase (se 2 (by rfl) ⟨825039, by rfl⟩ : syracuseStep 2200105 = 1650079) (by norm_num)
theorem B11733893 : Blo 2059435 11733893 := bstep (se 4 (by rfl) ⟨1100052, by rfl⟩ : syracuseStep 11733893 = 2200105) B2200105
theorem B7822595 : Blo 2059435 7822595 := bstep (se 1 (by rfl) ⟨5866946, by rfl⟩ : syracuseStep 7822595 = 11733893) B11733893
theorem B5215063 : Blo 2059435 5215063 := bstep (se 1 (by rfl) ⟨3911297, by rfl⟩ : syracuseStep 5215063 = 7822595) B7822595
theorem B6953417 : Blo 2059435 6953417 := bstep (se 2 (by rfl) ⟨2607531, by rfl⟩ : syracuseStep 6953417 = 5215063) B5215063
theorem B4635611 : Blo 2059435 4635611 := bstep (se 1 (by rfl) ⟨3476708, by rfl⟩ : syracuseStep 4635611 = 6953417) B6953417
theorem B3090407 : Blo 2059435 3090407 := bstep (se 1 (by rfl) ⟨2317805, by rfl⟩ : syracuseStep 3090407 = 4635611) B4635611
theorem B2060271 : Blo 2059435 2060271 := bstep (se 1 (by rfl) ⟨1545203, by rfl⟩ : syracuseStep 2060271 = 3090407) B3090407
theorem B3090413 : Blo 2059435 3090413 := bbase (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) (by norm_num)
theorem B2060275 : Blo 2059435 2060275 := bstep (se 1 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 2060275 = 3090413) B3090413
theorem B4635629 : Blo 2059435 4635629 := bbase (se 3 (by rfl) ⟨869180, by rfl⟩ : syracuseStep 4635629 = 1738361) (by norm_num)
theorem B3090419 : Blo 2059435 3090419 := bstep (se 1 (by rfl) ⟨2317814, by rfl⟩ : syracuseStep 3090419 = 4635629) B4635629
theorem B2060279 : Blo 2059435 2060279 := bstep (se 1 (by rfl) ⟨1545209, by rfl⟩ : syracuseStep 2060279 = 3090419) B3090419
theorem B4400237 : Blo 2059435 4400237 := bbase (se 3 (by rfl) ⟨825044, by rfl⟩ : syracuseStep 4400237 = 1650089) (by norm_num)
theorem B2933491 : Blo 2059435 2933491 := bstep (se 1 (by rfl) ⟨2200118, by rfl⟩ : syracuseStep 2933491 = 4400237) B4400237
theorem B3911321 : Blo 2059435 3911321 := bstep (se 2 (by rfl) ⟨1466745, by rfl⟩ : syracuseStep 3911321 = 2933491) B2933491
theorem B2607547 : Blo 2059435 2607547 := bstep (se 1 (by rfl) ⟨1955660, by rfl⟩ : syracuseStep 2607547 = 3911321) B3911321
theorem B3476729 : Blo 2059435 3476729 := bstep (se 2 (by rfl) ⟨1303773, by rfl⟩ : syracuseStep 3476729 = 2607547) B2607547
theorem B2317819 : Blo 2059435 2317819 := bstep (se 1 (by rfl) ⟨1738364, by rfl⟩ : syracuseStep 2317819 = 3476729) B3476729
theorem B3090425 : Blo 2059435 3090425 := bstep (se 2 (by rfl) ⟨1158909, by rfl⟩ : syracuseStep 3090425 = 2317819) B2317819
theorem B2060283 : Blo 2059435 2060283 := bstep (se 1 (by rfl) ⟨1545212, by rfl⟩ : syracuseStep 2060283 = 3090425) B3090425
theorem B5959477 : Blo 2059435 5959477 := bbase (se 5 (by rfl) ⟨279350, by rfl⟩ : syracuseStep 5959477 = 558701) (by norm_num)
theorem B31783877 : Blo 2059435 31783877 := bstep (se 4 (by rfl) ⟨2979738, by rfl⟩ : syracuseStep 31783877 = 5959477) B5959477
theorem B21189251 : Blo 2059435 21189251 := bstep (se 1 (by rfl) ⟨15891938, by rfl⟩ : syracuseStep 21189251 = 31783877) B31783877
theorem B14126167 : Blo 2059435 14126167 := bstep (se 1 (by rfl) ⟨10594625, by rfl⟩ : syracuseStep 14126167 = 21189251) B21189251
theorem B18834889 : Blo 2059435 18834889 := bstep (se 2 (by rfl) ⟨7063083, by rfl⟩ : syracuseStep 18834889 = 14126167) B14126167
theorem B25113185 : Blo 2059435 25113185 := bstep (se 2 (by rfl) ⟨9417444, by rfl⟩ : syracuseStep 25113185 = 18834889) B18834889
theorem B16742123 : Blo 2059435 16742123 := bstep (se 1 (by rfl) ⟨12556592, by rfl⟩ : syracuseStep 16742123 = 25113185) B25113185
theorem B11161415 : Blo 2059435 11161415 := bstep (se 1 (by rfl) ⟨8371061, by rfl⟩ : syracuseStep 11161415 = 16742123) B16742123
theorem B29763773 : Blo 2059435 29763773 := bstep (se 3 (by rfl) ⟨5580707, by rfl⟩ : syracuseStep 29763773 = 11161415) B11161415
theorem B19842515 : Blo 2059435 19842515 := bstep (se 1 (by rfl) ⟨14881886, by rfl⟩ : syracuseStep 19842515 = 29763773) B29763773
theorem B13228343 : Blo 2059435 13228343 := bstep (se 1 (by rfl) ⟨9921257, by rfl⟩ : syracuseStep 13228343 = 19842515) B19842515
theorem B8818895 : Blo 2059435 8818895 := bstep (se 1 (by rfl) ⟨6614171, by rfl⟩ : syracuseStep 8818895 = 13228343) B13228343
theorem B23517053 : Blo 2059435 23517053 := bstep (se 3 (by rfl) ⟨4409447, by rfl⟩ : syracuseStep 23517053 = 8818895) B8818895
theorem B15678035 : Blo 2059435 15678035 := bstep (se 1 (by rfl) ⟨11758526, by rfl⟩ : syracuseStep 15678035 = 23517053) B23517053
theorem B10452023 : Blo 2059435 10452023 := bstep (se 1 (by rfl) ⟨7839017, by rfl⟩ : syracuseStep 10452023 = 15678035) B15678035
theorem B6968015 : Blo 2059435 6968015 := bstep (se 1 (by rfl) ⟨5226011, by rfl⟩ : syracuseStep 6968015 = 10452023) B10452023
theorem B4645343 : Blo 2059435 4645343 := bstep (se 1 (by rfl) ⟨3484007, by rfl⟩ : syracuseStep 4645343 = 6968015) B6968015
theorem B3096895 : Blo 2059435 3096895 := bstep (se 1 (by rfl) ⟨2322671, by rfl⟩ : syracuseStep 3096895 = 4645343) B4645343
theorem B4129193 : Blo 2059435 4129193 := bstep (se 2 (by rfl) ⟨1548447, by rfl⟩ : syracuseStep 4129193 = 3096895) B3096895
theorem B2752795 : Blo 2059435 2752795 := bstep (se 1 (by rfl) ⟨2064596, by rfl⟩ : syracuseStep 2752795 = 4129193) B4129193
theorem B3670393 : Blo 2059435 3670393 := bstep (se 2 (by rfl) ⟨1376397, by rfl⟩ : syracuseStep 3670393 = 2752795) B2752795
theorem B4893857 : Blo 2059435 4893857 := bstep (se 2 (by rfl) ⟨1835196, by rfl⟩ : syracuseStep 4893857 = 3670393) B3670393
theorem B3262571 : Blo 2059435 3262571 := bstep (se 1 (by rfl) ⟨2446928, by rfl⟩ : syracuseStep 3262571 = 4893857) B4893857
theorem B2175047 : Blo 2059435 2175047 := bstep (se 1 (by rfl) ⟨1631285, by rfl⟩ : syracuseStep 2175047 = 3262571) B3262571
theorem B23200501 : Blo 2059435 23200501 := bstep (se 5 (by rfl) ⟨1087523, by rfl⟩ : syracuseStep 23200501 = 2175047) B2175047
theorem B30934001 : Blo 2059435 30934001 := bstep (se 2 (by rfl) ⟨11600250, by rfl⟩ : syracuseStep 30934001 = 23200501) B23200501
theorem B82490669 : Blo 2059435 82490669 := bstep (se 3 (by rfl) ⟨15467000, by rfl⟩ : syracuseStep 82490669 = 30934001) B30934001
theorem B54993779 : Blo 2059435 54993779 := bstep (se 1 (by rfl) ⟨41245334, by rfl⟩ : syracuseStep 54993779 = 82490669) B82490669
theorem B36662519 : Blo 2059435 36662519 := bstep (se 1 (by rfl) ⟨27496889, by rfl⟩ : syracuseStep 36662519 = 54993779) B54993779
theorem B24441679 : Blo 2059435 24441679 := bstep (se 1 (by rfl) ⟨18331259, by rfl⟩ : syracuseStep 24441679 = 36662519) B36662519
theorem B32588905 : Blo 2059435 32588905 := bstep (se 2 (by rfl) ⟨12220839, by rfl⟩ : syracuseStep 32588905 = 24441679) B24441679
theorem B43451873 : Blo 2059435 43451873 := bstep (se 2 (by rfl) ⟨16294452, by rfl⟩ : syracuseStep 43451873 = 32588905) B32588905
theorem B28967915 : Blo 2059435 28967915 := bstep (se 1 (by rfl) ⟨21725936, by rfl⟩ : syracuseStep 28967915 = 43451873) B43451873
theorem B19311943 : Blo 2059435 19311943 := bstep (se 1 (by rfl) ⟨14483957, by rfl⟩ : syracuseStep 19311943 = 28967915) B28967915
theorem B25749257 : Blo 2059435 25749257 := bstep (se 2 (by rfl) ⟨9655971, by rfl⟩ : syracuseStep 25749257 = 19311943) B19311943
theorem B68664685 : Blo 2059435 68664685 := bstep (se 3 (by rfl) ⟨12874628, by rfl⟩ : syracuseStep 68664685 = 25749257) B25749257
theorem B91552913 : Blo 2059435 91552913 := bstep (se 2 (by rfl) ⟨34332342, by rfl⟩ : syracuseStep 91552913 = 68664685) B68664685
theorem B61035275 : Blo 2059435 61035275 := bstep (se 1 (by rfl) ⟨45776456, by rfl⟩ : syracuseStep 61035275 = 91552913) B91552913
theorem B40690183 : Blo 2059435 40690183 := bstep (se 1 (by rfl) ⟨30517637, by rfl⟩ : syracuseStep 40690183 = 61035275) B61035275
theorem B54253577 : Blo 2059435 54253577 := bstep (se 2 (by rfl) ⟨20345091, by rfl⟩ : syracuseStep 54253577 = 40690183) B40690183
theorem B36169051 : Blo 2059435 36169051 := bstep (se 1 (by rfl) ⟨27126788, by rfl⟩ : syracuseStep 36169051 = 54253577) B54253577
theorem B48225401 : Blo 2059435 48225401 := bstep (se 2 (by rfl) ⟨18084525, by rfl⟩ : syracuseStep 48225401 = 36169051) B36169051
theorem B32150267 : Blo 2059435 32150267 := bstep (se 1 (by rfl) ⟨24112700, by rfl⟩ : syracuseStep 32150267 = 48225401) B48225401
theorem B21433511 : Blo 2059435 21433511 := bstep (se 1 (by rfl) ⟨16075133, by rfl⟩ : syracuseStep 21433511 = 32150267) B32150267
theorem B14289007 : Blo 2059435 14289007 := bstep (se 1 (by rfl) ⟨10716755, by rfl⟩ : syracuseStep 14289007 = 21433511) B21433511
theorem B19052009 : Blo 2059435 19052009 := bstep (se 2 (by rfl) ⟨7144503, by rfl⟩ : syracuseStep 19052009 = 14289007) B14289007
theorem B12701339 : Blo 2059435 12701339 := bstep (se 1 (by rfl) ⟨9526004, by rfl⟩ : syracuseStep 12701339 = 19052009) B19052009
theorem B8467559 : Blo 2059435 8467559 := bstep (se 1 (by rfl) ⟨6350669, by rfl⟩ : syracuseStep 8467559 = 12701339) B12701339
theorem B90320629 : Blo 2059435 90320629 := bstep (se 5 (by rfl) ⟨4233779, by rfl⟩ : syracuseStep 90320629 = 8467559) B8467559
theorem B120427505 : Blo 2059435 120427505 := bstep (se 2 (by rfl) ⟨45160314, by rfl⟩ : syracuseStep 120427505 = 90320629) B90320629
theorem B80285003 : Blo 2059435 80285003 := bstep (se 1 (by rfl) ⟨60213752, by rfl⟩ : syracuseStep 80285003 = 120427505) B120427505
theorem B53523335 : Blo 2059435 53523335 := bstep (se 1 (by rfl) ⟨40142501, by rfl⟩ : syracuseStep 53523335 = 80285003) B80285003
theorem B35682223 : Blo 2059435 35682223 := bstep (se 1 (by rfl) ⟨26761667, by rfl⟩ : syracuseStep 35682223 = 53523335) B53523335
theorem B47576297 : Blo 2059435 47576297 := bstep (se 2 (by rfl) ⟨17841111, by rfl⟩ : syracuseStep 47576297 = 35682223) B35682223
theorem B31717531 : Blo 2059435 31717531 := bstep (se 1 (by rfl) ⟨23788148, by rfl⟩ : syracuseStep 31717531 = 47576297) B47576297
theorem B42290041 : Blo 2059435 42290041 := bstep (se 2 (by rfl) ⟨15858765, by rfl⟩ : syracuseStep 42290041 = 31717531) B31717531
theorem B56386721 : Blo 2059435 56386721 := bstep (se 2 (by rfl) ⟨21145020, by rfl⟩ : syracuseStep 56386721 = 42290041) B42290041
theorem B37591147 : Blo 2059435 37591147 := bstep (se 1 (by rfl) ⟨28193360, by rfl⟩ : syracuseStep 37591147 = 56386721) B56386721
theorem B200486117 : Blo 2059435 200486117 := bstep (se 4 (by rfl) ⟨18795573, by rfl⟩ : syracuseStep 200486117 = 37591147) B37591147
theorem B133657411 : Blo 2059435 133657411 := bstep (se 1 (by rfl) ⟨100243058, by rfl⟩ : syracuseStep 133657411 = 200486117) B200486117
theorem B178209881 : Blo 2059435 178209881 := bstep (se 2 (by rfl) ⟨66828705, by rfl⟩ : syracuseStep 178209881 = 133657411) B133657411
theorem B118806587 : Blo 2059435 118806587 := bstep (se 1 (by rfl) ⟨89104940, by rfl⟩ : syracuseStep 118806587 = 178209881) B178209881
theorem B79204391 : Blo 2059435 79204391 := bstep (se 1 (by rfl) ⟨59403293, by rfl⟩ : syracuseStep 79204391 = 118806587) B118806587
theorem B52802927 : Blo 2059435 52802927 := bstep (se 1 (by rfl) ⟨39602195, by rfl⟩ : syracuseStep 52802927 = 79204391) B79204391
theorem B35201951 : Blo 2059435 35201951 := bstep (se 1 (by rfl) ⟨26401463, by rfl⟩ : syracuseStep 35201951 = 52802927) B52802927
theorem B23467967 : Blo 2059435 23467967 := bstep (se 1 (by rfl) ⟨17600975, by rfl⟩ : syracuseStep 23467967 = 35201951) B35201951
theorem B15645311 : Blo 2059435 15645311 := bstep (se 1 (by rfl) ⟨11733983, by rfl⟩ : syracuseStep 15645311 = 23467967) B23467967
theorem B10430207 : Blo 2059435 10430207 := bstep (se 1 (by rfl) ⟨7822655, by rfl⟩ : syracuseStep 10430207 = 15645311) B15645311
theorem B6953471 : Blo 2059435 6953471 := bstep (se 1 (by rfl) ⟨5215103, by rfl⟩ : syracuseStep 6953471 = 10430207) B10430207
theorem B4635647 : Blo 2059435 4635647 := bstep (se 1 (by rfl) ⟨3476735, by rfl⟩ : syracuseStep 4635647 = 6953471) B6953471
theorem B3090431 : Blo 2059435 3090431 := bstep (se 1 (by rfl) ⟨2317823, by rfl⟩ : syracuseStep 3090431 = 4635647) B4635647
theorem B2060287 : Blo 2059435 2060287 := bstep (se 1 (by rfl) ⟨1545215, by rfl⟩ : syracuseStep 2060287 = 3090431) B3090431
theorem B3090437 : Blo 2059435 3090437 := bbase (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) (by norm_num)
theorem B2060291 : Blo 2059435 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B3476749 : Blo 2059435 3476749 := bbase (se 3 (by rfl) ⟨651890, by rfl⟩ : syracuseStep 3476749 = 1303781) (by norm_num)
theorem B4635665 : Blo 2059435 4635665 := bstep (se 2 (by rfl) ⟨1738374, by rfl⟩ : syracuseStep 4635665 = 3476749) B3476749
theorem B3090443 : Blo 2059435 3090443 := bstep (se 1 (by rfl) ⟨2317832, by rfl⟩ : syracuseStep 3090443 = 4635665) B4635665
theorem B2060295 : Blo 2059435 2060295 := bstep (se 1 (by rfl) ⟨1545221, by rfl⟩ : syracuseStep 2060295 = 3090443) B3090443
theorem B2317837 : Blo 2059435 2317837 := bbase (se 3 (by rfl) ⟨434594, by rfl⟩ : syracuseStep 2317837 = 869189) (by norm_num)
theorem B3090449 : Blo 2059435 3090449 := bstep (se 2 (by rfl) ⟨1158918, by rfl⟩ : syracuseStep 3090449 = 2317837) B2317837
theorem B2060299 : Blo 2059435 2060299 := bstep (se 1 (by rfl) ⟨1545224, by rfl⟩ : syracuseStep 2060299 = 3090449) B3090449
theorem B6953525 : Blo 2059435 6953525 := bbase (se 5 (by rfl) ⟨325946, by rfl⟩ : syracuseStep 6953525 = 651893) (by norm_num)
theorem B4635683 : Blo 2059435 4635683 := bstep (se 1 (by rfl) ⟨3476762, by rfl⟩ : syracuseStep 4635683 = 6953525) B6953525
theorem B3090455 : Blo 2059435 3090455 := bstep (se 1 (by rfl) ⟨2317841, by rfl⟩ : syracuseStep 3090455 = 4635683) B4635683
theorem B2060303 : Blo 2059435 2060303 := bstep (se 1 (by rfl) ⟨1545227, by rfl⟩ : syracuseStep 2060303 = 3090455) B3090455
theorem B3090461 : Blo 2059435 3090461 := bbase (se 3 (by rfl) ⟨579461, by rfl⟩ : syracuseStep 3090461 = 1158923) (by norm_num)
theorem B2060307 : Blo 2059435 2060307 := bstep (se 1 (by rfl) ⟨1545230, by rfl⟩ : syracuseStep 2060307 = 3090461) B3090461
theorem B4635701 : Blo 2059435 4635701 := bbase (se 5 (by rfl) ⟨217298, by rfl⟩ : syracuseStep 4635701 = 434597) (by norm_num)
theorem B3090467 : Blo 2059435 3090467 := bstep (se 1 (by rfl) ⟨2317850, by rfl⟩ : syracuseStep 3090467 = 4635701) B4635701
theorem B2060311 : Blo 2059435 2060311 := bstep (se 1 (by rfl) ⟨1545233, by rfl⟩ : syracuseStep 2060311 = 3090467) B3090467
theorem B9290821 : Blo 2059435 9290821 := bbase (se 4 (by rfl) ⟨871014, by rfl⟩ : syracuseStep 9290821 = 1742029) (by norm_num)
theorem B12387761 : Blo 2059435 12387761 := bstep (se 2 (by rfl) ⟨4645410, by rfl⟩ : syracuseStep 12387761 = 9290821) B9290821
theorem B8258507 : Blo 2059435 8258507 := bstep (se 1 (by rfl) ⟨6193880, by rfl⟩ : syracuseStep 8258507 = 12387761) B12387761
theorem B5505671 : Blo 2059435 5505671 := bstep (se 1 (by rfl) ⟨4129253, by rfl⟩ : syracuseStep 5505671 = 8258507) B8258507
theorem B3670447 : Blo 2059435 3670447 := bstep (se 1 (by rfl) ⟨2752835, by rfl⟩ : syracuseStep 3670447 = 5505671) B5505671
theorem B4893929 : Blo 2059435 4893929 := bstep (se 2 (by rfl) ⟨1835223, by rfl⟩ : syracuseStep 4893929 = 3670447) B3670447
theorem B3262619 : Blo 2059435 3262619 := bstep (se 1 (by rfl) ⟨2446964, by rfl⟩ : syracuseStep 3262619 = 4893929) B4893929
theorem B8700317 : Blo 2059435 8700317 := bstep (se 3 (by rfl) ⟨1631309, by rfl⟩ : syracuseStep 8700317 = 3262619) B3262619
theorem B5800211 : Blo 2059435 5800211 := bstep (se 1 (by rfl) ⟨4350158, by rfl⟩ : syracuseStep 5800211 = 8700317) B8700317
theorem B3866807 : Blo 2059435 3866807 := bstep (se 1 (by rfl) ⟨2900105, by rfl⟩ : syracuseStep 3866807 = 5800211) B5800211
theorem B2577871 : Blo 2059435 2577871 := bstep (se 1 (by rfl) ⟨1933403, by rfl⟩ : syracuseStep 2577871 = 3866807) B3866807
theorem B3437161 : Blo 2059435 3437161 := bstep (se 2 (by rfl) ⟨1288935, by rfl⟩ : syracuseStep 3437161 = 2577871) B2577871
theorem B18331525 : Blo 2059435 18331525 := bstep (se 4 (by rfl) ⟨1718580, by rfl⟩ : syracuseStep 18331525 = 3437161) B3437161
theorem B24442033 : Blo 2059435 24442033 := bstep (se 2 (by rfl) ⟨9165762, by rfl⟩ : syracuseStep 24442033 = 18331525) B18331525
theorem B32589377 : Blo 2059435 32589377 := bstep (se 2 (by rfl) ⟨12221016, by rfl⟩ : syracuseStep 32589377 = 24442033) B24442033
theorem B21726251 : Blo 2059435 21726251 := bstep (se 1 (by rfl) ⟨16294688, by rfl⟩ : syracuseStep 21726251 = 32589377) B32589377
theorem B14484167 : Blo 2059435 14484167 := bstep (se 1 (by rfl) ⟨10863125, by rfl⟩ : syracuseStep 14484167 = 21726251) B21726251
theorem B9656111 : Blo 2059435 9656111 := bstep (se 1 (by rfl) ⟨7242083, by rfl⟩ : syracuseStep 9656111 = 14484167) B14484167
theorem B6437407 : Blo 2059435 6437407 := bstep (se 1 (by rfl) ⟨4828055, by rfl⟩ : syracuseStep 6437407 = 9656111) B9656111
theorem B8583209 : Blo 2059435 8583209 := bstep (se 2 (by rfl) ⟨3218703, by rfl⟩ : syracuseStep 8583209 = 6437407) B6437407
theorem B5722139 : Blo 2059435 5722139 := bstep (se 1 (by rfl) ⟨4291604, by rfl⟩ : syracuseStep 5722139 = 8583209) B8583209
theorem B3814759 : Blo 2059435 3814759 := bstep (se 1 (by rfl) ⟨2861069, by rfl⟩ : syracuseStep 3814759 = 5722139) B5722139
theorem B20345381 : Blo 2059435 20345381 := bstep (se 4 (by rfl) ⟨1907379, by rfl⟩ : syracuseStep 20345381 = 3814759) B3814759
theorem B13563587 : Blo 2059435 13563587 := bstep (se 1 (by rfl) ⟨10172690, by rfl⟩ : syracuseStep 13563587 = 20345381) B20345381
theorem B9042391 : Blo 2059435 9042391 := bstep (se 1 (by rfl) ⟨6781793, by rfl⟩ : syracuseStep 9042391 = 13563587) B13563587
theorem B12056521 : Blo 2059435 12056521 := bstep (se 2 (by rfl) ⟨4521195, by rfl⟩ : syracuseStep 12056521 = 9042391) B9042391
theorem B16075361 : Blo 2059435 16075361 := bstep (se 2 (by rfl) ⟨6028260, by rfl⟩ : syracuseStep 16075361 = 12056521) B12056521
theorem B10716907 : Blo 2059435 10716907 := bstep (se 1 (by rfl) ⟨8037680, by rfl⟩ : syracuseStep 10716907 = 16075361) B16075361
theorem B14289209 : Blo 2059435 14289209 := bstep (se 2 (by rfl) ⟨5358453, by rfl⟩ : syracuseStep 14289209 = 10716907) B10716907
theorem B9526139 : Blo 2059435 9526139 := bstep (se 1 (by rfl) ⟨7144604, by rfl⟩ : syracuseStep 9526139 = 14289209) B14289209
theorem B6350759 : Blo 2059435 6350759 := bstep (se 1 (by rfl) ⟨4763069, by rfl⟩ : syracuseStep 6350759 = 9526139) B9526139
theorem B67741429 : Blo 2059435 67741429 := bstep (se 5 (by rfl) ⟨3175379, by rfl⟩ : syracuseStep 67741429 = 6350759) B6350759
theorem B90321905 : Blo 2059435 90321905 := bstep (se 2 (by rfl) ⟨33870714, by rfl⟩ : syracuseStep 90321905 = 67741429) B67741429
theorem B60214603 : Blo 2059435 60214603 := bstep (se 1 (by rfl) ⟨45160952, by rfl⟩ : syracuseStep 60214603 = 90321905) B90321905
theorem B80286137 : Blo 2059435 80286137 := bstep (se 2 (by rfl) ⟨30107301, by rfl⟩ : syracuseStep 80286137 = 60214603) B60214603
theorem B53524091 : Blo 2059435 53524091 := bstep (se 1 (by rfl) ⟨40143068, by rfl⟩ : syracuseStep 53524091 = 80286137) B80286137
theorem B35682727 : Blo 2059435 35682727 := bstep (se 1 (by rfl) ⟨26762045, by rfl⟩ : syracuseStep 35682727 = 53524091) B53524091
theorem B47576969 : Blo 2059435 47576969 := bstep (se 2 (by rfl) ⟨17841363, by rfl⟩ : syracuseStep 47576969 = 35682727) B35682727
theorem B31717979 : Blo 2059435 31717979 := bstep (se 1 (by rfl) ⟨23788484, by rfl⟩ : syracuseStep 31717979 = 47576969) B47576969
theorem B21145319 : Blo 2059435 21145319 := bstep (se 1 (by rfl) ⟨15858989, by rfl⟩ : syracuseStep 21145319 = 31717979) B31717979
theorem B14096879 : Blo 2059435 14096879 := bstep (se 1 (by rfl) ⟨10572659, by rfl⟩ : syracuseStep 14096879 = 21145319) B21145319
theorem B9397919 : Blo 2059435 9397919 := bstep (se 1 (by rfl) ⟨7048439, by rfl⟩ : syracuseStep 9397919 = 14096879) B14096879
theorem B6265279 : Blo 2059435 6265279 := bstep (se 1 (by rfl) ⟨4698959, by rfl⟩ : syracuseStep 6265279 = 9397919) B9397919
theorem B8353705 : Blo 2059435 8353705 := bstep (se 2 (by rfl) ⟨3132639, by rfl⟩ : syracuseStep 8353705 = 6265279) B6265279
theorem B11138273 : Blo 2059435 11138273 := bstep (se 2 (by rfl) ⟨4176852, by rfl⟩ : syracuseStep 11138273 = 8353705) B8353705
theorem B7425515 : Blo 2059435 7425515 := bstep (se 1 (by rfl) ⟨5569136, by rfl⟩ : syracuseStep 7425515 = 11138273) B11138273
theorem B4950343 : Blo 2059435 4950343 := bstep (se 1 (by rfl) ⟨3712757, by rfl⟩ : syracuseStep 4950343 = 7425515) B7425515
theorem B6600457 : Blo 2059435 6600457 := bstep (se 2 (by rfl) ⟨2475171, by rfl⟩ : syracuseStep 6600457 = 4950343) B4950343
theorem B8800609 : Blo 2059435 8800609 := bstep (se 2 (by rfl) ⟨3300228, by rfl⟩ : syracuseStep 8800609 = 6600457) B6600457
theorem B11734145 : Blo 2059435 11734145 := bstep (se 2 (by rfl) ⟨4400304, by rfl⟩ : syracuseStep 11734145 = 8800609) B8800609
theorem B7822763 : Blo 2059435 7822763 := bstep (se 1 (by rfl) ⟨5867072, by rfl⟩ : syracuseStep 7822763 = 11734145) B11734145
theorem B5215175 : Blo 2059435 5215175 := bstep (se 1 (by rfl) ⟨3911381, by rfl⟩ : syracuseStep 5215175 = 7822763) B7822763
theorem B3476783 : Blo 2059435 3476783 := bstep (se 1 (by rfl) ⟨2607587, by rfl⟩ : syracuseStep 3476783 = 5215175) B5215175
theorem B2317855 : Blo 2059435 2317855 := bstep (se 1 (by rfl) ⟨1738391, by rfl⟩ : syracuseStep 2317855 = 3476783) B3476783
theorem B3090473 : Blo 2059435 3090473 := bstep (se 2 (by rfl) ⟨1158927, by rfl⟩ : syracuseStep 3090473 = 2317855) B2317855
theorem B2060315 : Blo 2059435 2060315 := bstep (se 1 (by rfl) ⟨1545236, by rfl⟩ : syracuseStep 2060315 = 3090473) B3090473
theorem B6600469 : Blo 2059435 6600469 := bbase (se 6 (by rfl) ⟨154698, by rfl⟩ : syracuseStep 6600469 = 309397) (by norm_num)
theorem B8800625 : Blo 2059435 8800625 := bstep (se 2 (by rfl) ⟨3300234, by rfl⟩ : syracuseStep 8800625 = 6600469) B6600469
theorem B5867083 : Blo 2059435 5867083 := bstep (se 1 (by rfl) ⟨4400312, by rfl⟩ : syracuseStep 5867083 = 8800625) B8800625
theorem B7822777 : Blo 2059435 7822777 := bstep (se 2 (by rfl) ⟨2933541, by rfl⟩ : syracuseStep 7822777 = 5867083) B5867083
theorem B10430369 : Blo 2059435 10430369 := bstep (se 2 (by rfl) ⟨3911388, by rfl⟩ : syracuseStep 10430369 = 7822777) B7822777
theorem B6953579 : Blo 2059435 6953579 := bstep (se 1 (by rfl) ⟨5215184, by rfl⟩ : syracuseStep 6953579 = 10430369) B10430369
theorem B4635719 : Blo 2059435 4635719 := bstep (se 1 (by rfl) ⟨3476789, by rfl⟩ : syracuseStep 4635719 = 6953579) B6953579
theorem B3090479 : Blo 2059435 3090479 := bstep (se 1 (by rfl) ⟨2317859, by rfl⟩ : syracuseStep 3090479 = 4635719) B4635719
theorem B2060319 : Blo 2059435 2060319 := bstep (se 1 (by rfl) ⟨1545239, by rfl⟩ : syracuseStep 2060319 = 3090479) B3090479
theorem B3090485 : Blo 2059435 3090485 := bbase (se 5 (by rfl) ⟨144866, by rfl⟩ : syracuseStep 3090485 = 289733) (by norm_num)
theorem B2060323 : Blo 2059435 2060323 := bstep (se 1 (by rfl) ⟨1545242, by rfl⟩ : syracuseStep 2060323 = 3090485) B3090485
theorem B5215205 : Blo 2059435 5215205 := bbase (se 4 (by rfl) ⟨488925, by rfl⟩ : syracuseStep 5215205 = 977851) (by norm_num)
theorem B3476803 : Blo 2059435 3476803 := bstep (se 1 (by rfl) ⟨2607602, by rfl⟩ : syracuseStep 3476803 = 5215205) B5215205
theorem B4635737 : Blo 2059435 4635737 := bstep (se 2 (by rfl) ⟨1738401, by rfl⟩ : syracuseStep 4635737 = 3476803) B3476803
theorem B3090491 : Blo 2059435 3090491 := bstep (se 1 (by rfl) ⟨2317868, by rfl⟩ : syracuseStep 3090491 = 4635737) B4635737
theorem B2060327 : Blo 2059435 2060327 := bstep (se 1 (by rfl) ⟨1545245, by rfl⟩ : syracuseStep 2060327 = 3090491) B3090491
theorem B2317873 : Blo 2059435 2317873 := bbase (se 2 (by rfl) ⟨869202, by rfl⟩ : syracuseStep 2317873 = 1738405) (by norm_num)
theorem B3090497 : Blo 2059435 3090497 := bstep (se 2 (by rfl) ⟨1158936, by rfl⟩ : syracuseStep 3090497 = 2317873) B2317873
theorem B2060331 : Blo 2059435 2060331 := bstep (se 1 (by rfl) ⟨1545248, by rfl⟩ : syracuseStep 2060331 = 3090497) B3090497
theorem B4176893 : Blo 2059435 4176893 := bbase (se 3 (by rfl) ⟨783167, by rfl⟩ : syracuseStep 4176893 = 1566335) (by norm_num)
theorem B11138381 : Blo 2059435 11138381 := bstep (se 3 (by rfl) ⟨2088446, by rfl⟩ : syracuseStep 11138381 = 4176893) B4176893
theorem B7425587 : Blo 2059435 7425587 := bstep (se 1 (by rfl) ⟨5569190, by rfl⟩ : syracuseStep 7425587 = 11138381) B11138381
theorem B4950391 : Blo 2059435 4950391 := bstep (se 1 (by rfl) ⟨3712793, by rfl⟩ : syracuseStep 4950391 = 7425587) B7425587
theorem B6600521 : Blo 2059435 6600521 := bstep (se 2 (by rfl) ⟨2475195, by rfl⟩ : syracuseStep 6600521 = 4950391) B4950391
theorem B4400347 : Blo 2059435 4400347 := bstep (se 1 (by rfl) ⟨3300260, by rfl⟩ : syracuseStep 4400347 = 6600521) B6600521
theorem B5867129 : Blo 2059435 5867129 := bstep (se 2 (by rfl) ⟨2200173, by rfl⟩ : syracuseStep 5867129 = 4400347) B4400347
theorem B3911419 : Blo 2059435 3911419 := bstep (se 1 (by rfl) ⟨2933564, by rfl⟩ : syracuseStep 3911419 = 5867129) B5867129
theorem B5215225 : Blo 2059435 5215225 := bstep (se 2 (by rfl) ⟨1955709, by rfl⟩ : syracuseStep 5215225 = 3911419) B3911419
theorem B6953633 : Blo 2059435 6953633 := bstep (se 2 (by rfl) ⟨2607612, by rfl⟩ : syracuseStep 6953633 = 5215225) B5215225
theorem B4635755 : Blo 2059435 4635755 := bstep (se 1 (by rfl) ⟨3476816, by rfl⟩ : syracuseStep 4635755 = 6953633) B6953633
theorem B3090503 : Blo 2059435 3090503 := bstep (se 1 (by rfl) ⟨2317877, by rfl⟩ : syracuseStep 3090503 = 4635755) B4635755
theorem B2060335 : Blo 2059435 2060335 := bstep (se 1 (by rfl) ⟨1545251, by rfl⟩ : syracuseStep 2060335 = 3090503) B3090503
theorem B3090509 : Blo 2059435 3090509 := bbase (se 3 (by rfl) ⟨579470, by rfl⟩ : syracuseStep 3090509 = 1158941) (by norm_num)
theorem B2060339 : Blo 2059435 2060339 := bstep (se 1 (by rfl) ⟨1545254, by rfl⟩ : syracuseStep 2060339 = 3090509) B3090509
theorem B4635773 : Blo 2059435 4635773 := bbase (se 3 (by rfl) ⟨869207, by rfl⟩ : syracuseStep 4635773 = 1738415) (by norm_num)
theorem B3090515 : Blo 2059435 3090515 := bstep (se 1 (by rfl) ⟨2317886, by rfl⟩ : syracuseStep 3090515 = 4635773) B4635773
theorem B2060343 : Blo 2059435 2060343 := bstep (se 1 (by rfl) ⟨1545257, by rfl⟩ : syracuseStep 2060343 = 3090515) B3090515
theorem B3476837 : Blo 2059435 3476837 := bbase (se 4 (by rfl) ⟨325953, by rfl⟩ : syracuseStep 3476837 = 651907) (by norm_num)
theorem B2317891 : Blo 2059435 2317891 := bstep (se 1 (by rfl) ⟨1738418, by rfl⟩ : syracuseStep 2317891 = 3476837) B3476837
theorem B3090521 : Blo 2059435 3090521 := bstep (se 2 (by rfl) ⟨1158945, by rfl⟩ : syracuseStep 3090521 = 2317891) B2317891
theorem B2060347 : Blo 2059435 2060347 := bstep (se 1 (by rfl) ⟨1545260, by rfl⟩ : syracuseStep 2060347 = 3090521) B3090521
theorem B4400381 : Blo 2059435 4400381 := bbase (se 3 (by rfl) ⟨825071, by rfl⟩ : syracuseStep 4400381 = 1650143) (by norm_num)
theorem B2933587 : Blo 2059435 2933587 := bstep (se 1 (by rfl) ⟨2200190, by rfl⟩ : syracuseStep 2933587 = 4400381) B4400381
theorem B15645797 : Blo 2059435 15645797 := bstep (se 4 (by rfl) ⟨1466793, by rfl⟩ : syracuseStep 15645797 = 2933587) B2933587
theorem B10430531 : Blo 2059435 10430531 := bstep (se 1 (by rfl) ⟨7822898, by rfl⟩ : syracuseStep 10430531 = 15645797) B15645797
theorem B6953687 : Blo 2059435 6953687 := bstep (se 1 (by rfl) ⟨5215265, by rfl⟩ : syracuseStep 6953687 = 10430531) B10430531
theorem B4635791 : Blo 2059435 4635791 := bstep (se 1 (by rfl) ⟨3476843, by rfl⟩ : syracuseStep 4635791 = 6953687) B6953687
theorem B3090527 : Blo 2059435 3090527 := bstep (se 1 (by rfl) ⟨2317895, by rfl⟩ : syracuseStep 3090527 = 4635791) B4635791
theorem B2060351 : Blo 2059435 2060351 := bstep (se 1 (by rfl) ⟨1545263, by rfl⟩ : syracuseStep 2060351 = 3090527) B3090527
theorem B3090533 : Blo 2059435 3090533 := bbase (se 4 (by rfl) ⟨289737, by rfl⟩ : syracuseStep 3090533 = 579475) (by norm_num)
theorem B2060355 : Blo 2059435 2060355 := bstep (se 1 (by rfl) ⟨1545266, by rfl⟩ : syracuseStep 2060355 = 3090533) B3090533
theorem B14851349 : Blo 2059435 14851349 := bbase (se 6 (by rfl) ⟨348078, by rfl⟩ : syracuseStep 14851349 = 696157) (by norm_num)
theorem B9900899 : Blo 2059435 9900899 := bstep (se 1 (by rfl) ⟨7425674, by rfl⟩ : syracuseStep 9900899 = 14851349) B14851349
theorem B6600599 : Blo 2059435 6600599 := bstep (se 1 (by rfl) ⟨4950449, by rfl⟩ : syracuseStep 6600599 = 9900899) B9900899
theorem B4400399 : Blo 2059435 4400399 := bstep (se 1 (by rfl) ⟨3300299, by rfl⟩ : syracuseStep 4400399 = 6600599) B6600599
theorem B2933599 : Blo 2059435 2933599 := bstep (se 1 (by rfl) ⟨2200199, by rfl⟩ : syracuseStep 2933599 = 4400399) B4400399
theorem B3911465 : Blo 2059435 3911465 := bstep (se 2 (by rfl) ⟨1466799, by rfl⟩ : syracuseStep 3911465 = 2933599) B2933599
theorem B2607643 : Blo 2059435 2607643 := bstep (se 1 (by rfl) ⟨1955732, by rfl⟩ : syracuseStep 2607643 = 3911465) B3911465
theorem B3476857 : Blo 2059435 3476857 := bstep (se 2 (by rfl) ⟨1303821, by rfl⟩ : syracuseStep 3476857 = 2607643) B2607643
theorem B4635809 : Blo 2059435 4635809 := bstep (se 2 (by rfl) ⟨1738428, by rfl⟩ : syracuseStep 4635809 = 3476857) B3476857
theorem B3090539 : Blo 2059435 3090539 := bstep (se 1 (by rfl) ⟨2317904, by rfl⟩ : syracuseStep 3090539 = 4635809) B4635809
theorem B2060359 : Blo 2059435 2060359 := bstep (se 1 (by rfl) ⟨1545269, by rfl⟩ : syracuseStep 2060359 = 3090539) B3090539
theorem B2317909 : Blo 2059435 2317909 := bbase (se 8 (by rfl) ⟨13581, by rfl⟩ : syracuseStep 2317909 = 27163) (by norm_num)
theorem B3090545 : Blo 2059435 3090545 := bstep (se 2 (by rfl) ⟨1158954, by rfl⟩ : syracuseStep 3090545 = 2317909) B2317909
theorem B2060363 : Blo 2059435 2060363 := bstep (se 1 (by rfl) ⟨1545272, by rfl⟩ : syracuseStep 2060363 = 3090545) B3090545
theorem B2607653 : Blo 2059435 2607653 := bbase (se 4 (by rfl) ⟨244467, by rfl⟩ : syracuseStep 2607653 = 488935) (by norm_num)
theorem B6953741 : Blo 2059435 6953741 := bstep (se 3 (by rfl) ⟨1303826, by rfl⟩ : syracuseStep 6953741 = 2607653) B2607653
theorem B4635827 : Blo 2059435 4635827 := bstep (se 1 (by rfl) ⟨3476870, by rfl⟩ : syracuseStep 4635827 = 6953741) B6953741
theorem B3090551 : Blo 2059435 3090551 := bstep (se 1 (by rfl) ⟨2317913, by rfl⟩ : syracuseStep 3090551 = 4635827) B4635827
theorem B2060367 : Blo 2059435 2060367 := bstep (se 1 (by rfl) ⟨1545275, by rfl⟩ : syracuseStep 2060367 = 3090551) B3090551
theorem B3090557 : Blo 2059435 3090557 := bbase (se 3 (by rfl) ⟨579479, by rfl⟩ : syracuseStep 3090557 = 1158959) (by norm_num)
theorem B2060371 : Blo 2059435 2060371 := bstep (se 1 (by rfl) ⟨1545278, by rfl⟩ : syracuseStep 2060371 = 3090557) B3090557
theorem B4635845 : Blo 2059435 4635845 := bbase (se 4 (by rfl) ⟨434610, by rfl⟩ : syracuseStep 4635845 = 869221) (by norm_num)
theorem B3090563 : Blo 2059435 3090563 := bstep (se 1 (by rfl) ⟨2317922, by rfl⟩ : syracuseStep 3090563 = 4635845) B4635845
theorem B2060375 : Blo 2059435 2060375 := bstep (se 1 (by rfl) ⟨1545281, by rfl⟩ : syracuseStep 2060375 = 3090563) B3090563
theorem B9398213 : Blo 2059435 9398213 := bbase (se 4 (by rfl) ⟨881082, by rfl⟩ : syracuseStep 9398213 = 1762165) (by norm_num)
theorem B6265475 : Blo 2059435 6265475 := bstep (se 1 (by rfl) ⟨4699106, by rfl⟩ : syracuseStep 6265475 = 9398213) B9398213
theorem B4176983 : Blo 2059435 4176983 := bstep (se 1 (by rfl) ⟨3132737, by rfl⟩ : syracuseStep 4176983 = 6265475) B6265475
theorem B2784655 : Blo 2059435 2784655 := bstep (se 1 (by rfl) ⟨2088491, by rfl⟩ : syracuseStep 2784655 = 4176983) B4176983
theorem B3712873 : Blo 2059435 3712873 := bstep (se 2 (by rfl) ⟨1392327, by rfl⟩ : syracuseStep 3712873 = 2784655) B2784655
theorem B4950497 : Blo 2059435 4950497 := bstep (se 2 (by rfl) ⟨1856436, by rfl⟩ : syracuseStep 4950497 = 3712873) B3712873
theorem B13201325 : Blo 2059435 13201325 := bstep (se 3 (by rfl) ⟨2475248, by rfl⟩ : syracuseStep 13201325 = 4950497) B4950497
theorem B8800883 : Blo 2059435 8800883 := bstep (se 1 (by rfl) ⟨6600662, by rfl⟩ : syracuseStep 8800883 = 13201325) B13201325
theorem B5867255 : Blo 2059435 5867255 := bstep (se 1 (by rfl) ⟨4400441, by rfl⟩ : syracuseStep 5867255 = 8800883) B8800883
theorem B3911503 : Blo 2059435 3911503 := bstep (se 1 (by rfl) ⟨2933627, by rfl⟩ : syracuseStep 3911503 = 5867255) B5867255
theorem B5215337 : Blo 2059435 5215337 := bstep (se 2 (by rfl) ⟨1955751, by rfl⟩ : syracuseStep 5215337 = 3911503) B3911503
theorem B3476891 : Blo 2059435 3476891 := bstep (se 1 (by rfl) ⟨2607668, by rfl⟩ : syracuseStep 3476891 = 5215337) B5215337
theorem B2317927 : Blo 2059435 2317927 := bstep (se 1 (by rfl) ⟨1738445, by rfl⟩ : syracuseStep 2317927 = 3476891) B3476891
theorem B3090569 : Blo 2059435 3090569 := bstep (se 2 (by rfl) ⟨1158963, by rfl⟩ : syracuseStep 3090569 = 2317927) B2317927
theorem B2060379 : Blo 2059435 2060379 := bstep (se 1 (by rfl) ⟨1545284, by rfl⟩ : syracuseStep 2060379 = 3090569) B3090569
theorem B10430693 : Blo 2059435 10430693 := bbase (se 4 (by rfl) ⟨977877, by rfl⟩ : syracuseStep 10430693 = 1955755) (by norm_num)
theorem B6953795 : Blo 2059435 6953795 := bstep (se 1 (by rfl) ⟨5215346, by rfl⟩ : syracuseStep 6953795 = 10430693) B10430693
theorem B4635863 : Blo 2059435 4635863 := bstep (se 1 (by rfl) ⟨3476897, by rfl⟩ : syracuseStep 4635863 = 6953795) B6953795
theorem B3090575 : Blo 2059435 3090575 := bstep (se 1 (by rfl) ⟨2317931, by rfl⟩ : syracuseStep 3090575 = 4635863) B4635863
theorem B2060383 : Blo 2059435 2060383 := bstep (se 1 (by rfl) ⟨1545287, by rfl⟩ : syracuseStep 2060383 = 3090575) B3090575
theorem B3090581 : Blo 2059435 3090581 := bbase (se 6 (by rfl) ⟨72435, by rfl⟩ : syracuseStep 3090581 = 144871) (by norm_num)
theorem B2060387 : Blo 2059435 2060387 := bstep (se 1 (by rfl) ⟨1545290, by rfl⟩ : syracuseStep 2060387 = 3090581) B3090581
theorem B8800933 : Blo 2059435 8800933 := bbase (se 4 (by rfl) ⟨825087, by rfl⟩ : syracuseStep 8800933 = 1650175) (by norm_num)
theorem B11734577 : Blo 2059435 11734577 := bstep (se 2 (by rfl) ⟨4400466, by rfl⟩ : syracuseStep 11734577 = 8800933) B8800933
theorem B7823051 : Blo 2059435 7823051 := bstep (se 1 (by rfl) ⟨5867288, by rfl⟩ : syracuseStep 7823051 = 11734577) B11734577
theorem B5215367 : Blo 2059435 5215367 := bstep (se 1 (by rfl) ⟨3911525, by rfl⟩ : syracuseStep 5215367 = 7823051) B7823051
theorem B3476911 : Blo 2059435 3476911 := bstep (se 1 (by rfl) ⟨2607683, by rfl⟩ : syracuseStep 3476911 = 5215367) B5215367
theorem B4635881 : Blo 2059435 4635881 := bstep (se 2 (by rfl) ⟨1738455, by rfl⟩ : syracuseStep 4635881 = 3476911) B3476911
theorem B3090587 : Blo 2059435 3090587 := bstep (se 1 (by rfl) ⟨2317940, by rfl⟩ : syracuseStep 3090587 = 4635881) B4635881
theorem B2060391 : Blo 2059435 2060391 := bstep (se 1 (by rfl) ⟨1545293, by rfl⟩ : syracuseStep 2060391 = 3090587) B3090587
theorem B2317945 : Blo 2059435 2317945 := bbase (se 2 (by rfl) ⟨869229, by rfl⟩ : syracuseStep 2317945 = 1738459) (by norm_num)
theorem B3090593 : Blo 2059435 3090593 := bstep (se 2 (by rfl) ⟨1158972, by rfl⟩ : syracuseStep 3090593 = 2317945) B2317945
theorem B2060395 : Blo 2059435 2060395 := bstep (se 1 (by rfl) ⟨1545296, by rfl⟩ : syracuseStep 2060395 = 3090593) B3090593
theorem B15859637 : Blo 2059435 15859637 := bbase (se 5 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 15859637 = 1486841) (by norm_num)
theorem B10573091 : Blo 2059435 10573091 := bstep (se 1 (by rfl) ⟨7929818, by rfl⟩ : syracuseStep 10573091 = 15859637) B15859637
theorem B7048727 : Blo 2059435 7048727 := bstep (se 1 (by rfl) ⟨5286545, by rfl⟩ : syracuseStep 7048727 = 10573091) B10573091
theorem B4699151 : Blo 2059435 4699151 := bstep (se 1 (by rfl) ⟨3524363, by rfl⟩ : syracuseStep 4699151 = 7048727) B7048727
theorem B3132767 : Blo 2059435 3132767 := bstep (se 1 (by rfl) ⟨2349575, by rfl⟩ : syracuseStep 3132767 = 4699151) B4699151
theorem B2088511 : Blo 2059435 2088511 := bstep (se 1 (by rfl) ⟨1566383, by rfl⟩ : syracuseStep 2088511 = 3132767) B3132767
theorem B11138725 : Blo 2059435 11138725 := bstep (se 4 (by rfl) ⟨1044255, by rfl⟩ : syracuseStep 11138725 = 2088511) B2088511
theorem B14851633 : Blo 2059435 14851633 := bstep (se 2 (by rfl) ⟨5569362, by rfl⟩ : syracuseStep 14851633 = 11138725) B11138725
theorem B19802177 : Blo 2059435 19802177 := bstep (se 2 (by rfl) ⟨7425816, by rfl⟩ : syracuseStep 19802177 = 14851633) B14851633
theorem B13201451 : Blo 2059435 13201451 := bstep (se 1 (by rfl) ⟨9901088, by rfl⟩ : syracuseStep 13201451 = 19802177) B19802177
theorem B8800967 : Blo 2059435 8800967 := bstep (se 1 (by rfl) ⟨6600725, by rfl⟩ : syracuseStep 8800967 = 13201451) B13201451
theorem B5867311 : Blo 2059435 5867311 := bstep (se 1 (by rfl) ⟨4400483, by rfl⟩ : syracuseStep 5867311 = 8800967) B8800967
theorem B7823081 : Blo 2059435 7823081 := bstep (se 2 (by rfl) ⟨2933655, by rfl⟩ : syracuseStep 7823081 = 5867311) B5867311
theorem B5215387 : Blo 2059435 5215387 := bstep (se 1 (by rfl) ⟨3911540, by rfl⟩ : syracuseStep 5215387 = 7823081) B7823081
theorem B6953849 : Blo 2059435 6953849 := bstep (se 2 (by rfl) ⟨2607693, by rfl⟩ : syracuseStep 6953849 = 5215387) B5215387
theorem B4635899 : Blo 2059435 4635899 := bstep (se 1 (by rfl) ⟨3476924, by rfl⟩ : syracuseStep 4635899 = 6953849) B6953849
theorem B3090599 : Blo 2059435 3090599 := bstep (se 1 (by rfl) ⟨2317949, by rfl⟩ : syracuseStep 3090599 = 4635899) B4635899
theorem B2060399 : Blo 2059435 2060399 := bstep (se 1 (by rfl) ⟨1545299, by rfl⟩ : syracuseStep 2060399 = 3090599) B3090599
theorem B3090605 : Blo 2059435 3090605 := bbase (se 3 (by rfl) ⟨579488, by rfl⟩ : syracuseStep 3090605 = 1158977) (by norm_num)
theorem B2060403 : Blo 2059435 2060403 := bstep (se 1 (by rfl) ⟨1545302, by rfl⟩ : syracuseStep 2060403 = 3090605) B3090605
theorem B4635917 : Blo 2059435 4635917 := bbase (se 3 (by rfl) ⟨869234, by rfl⟩ : syracuseStep 4635917 = 1738469) (by norm_num)
theorem B3090611 : Blo 2059435 3090611 := bstep (se 1 (by rfl) ⟨2317958, by rfl⟩ : syracuseStep 3090611 = 4635917) B4635917
theorem B2060407 : Blo 2059435 2060407 := bstep (se 1 (by rfl) ⟨1545305, by rfl⟩ : syracuseStep 2060407 = 3090611) B3090611
theorem B2607709 : Blo 2059435 2607709 := bbase (se 3 (by rfl) ⟨488945, by rfl⟩ : syracuseStep 2607709 = 977891) (by norm_num)
theorem B3476945 : Blo 2059435 3476945 := bstep (se 2 (by rfl) ⟨1303854, by rfl⟩ : syracuseStep 3476945 = 2607709) B2607709
theorem B2317963 : Blo 2059435 2317963 := bstep (se 1 (by rfl) ⟨1738472, by rfl⟩ : syracuseStep 2317963 = 3476945) B3476945
theorem B3090617 : Blo 2059435 3090617 := bstep (se 2 (by rfl) ⟨1158981, by rfl⟩ : syracuseStep 3090617 = 2317963) B2317963
theorem B2060411 : Blo 2059435 2060411 := bstep (se 1 (by rfl) ⟨1545308, by rfl⟩ : syracuseStep 2060411 = 3090617) B3090617
theorem B17602069 : Blo 2059435 17602069 := bbase (se 6 (by rfl) ⟨412548, by rfl⟩ : syracuseStep 17602069 = 825097) (by norm_num)
theorem B23469425 : Blo 2059435 23469425 := bstep (se 2 (by rfl) ⟨8801034, by rfl⟩ : syracuseStep 23469425 = 17602069) B17602069
theorem B15646283 : Blo 2059435 15646283 := bstep (se 1 (by rfl) ⟨11734712, by rfl⟩ : syracuseStep 15646283 = 23469425) B23469425
theorem B10430855 : Blo 2059435 10430855 := bstep (se 1 (by rfl) ⟨7823141, by rfl⟩ : syracuseStep 10430855 = 15646283) B15646283
theorem B6953903 : Blo 2059435 6953903 := bstep (se 1 (by rfl) ⟨5215427, by rfl⟩ : syracuseStep 6953903 = 10430855) B10430855
theorem B4635935 : Blo 2059435 4635935 := bstep (se 1 (by rfl) ⟨3476951, by rfl⟩ : syracuseStep 4635935 = 6953903) B6953903
theorem B3090623 : Blo 2059435 3090623 := bstep (se 1 (by rfl) ⟨2317967, by rfl⟩ : syracuseStep 3090623 = 4635935) B4635935
theorem B2060415 : Blo 2059435 2060415 := bstep (se 1 (by rfl) ⟨1545311, by rfl⟩ : syracuseStep 2060415 = 3090623) B3090623
theorem B3090629 : Blo 2059435 3090629 := bbase (se 4 (by rfl) ⟨289746, by rfl⟩ : syracuseStep 3090629 = 579493) (by norm_num)
theorem B2060419 : Blo 2059435 2060419 := bstep (se 1 (by rfl) ⟨1545314, by rfl⟩ : syracuseStep 2060419 = 3090629) B3090629
theorem B3476965 : Blo 2059435 3476965 := bbase (se 4 (by rfl) ⟨325965, by rfl⟩ : syracuseStep 3476965 = 651931) (by norm_num)
theorem B4635953 : Blo 2059435 4635953 := bstep (se 2 (by rfl) ⟨1738482, by rfl⟩ : syracuseStep 4635953 = 3476965) B3476965
theorem B3090635 : Blo 2059435 3090635 := bstep (se 1 (by rfl) ⟨2317976, by rfl⟩ : syracuseStep 3090635 = 4635953) B4635953
theorem B2060423 : Blo 2059435 2060423 := bstep (se 1 (by rfl) ⟨1545317, by rfl⟩ : syracuseStep 2060423 = 3090635) B3090635
theorem B2317981 : Blo 2059435 2317981 := bbase (se 3 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 2317981 = 869243) (by norm_num)
theorem B3090641 : Blo 2059435 3090641 := bstep (se 2 (by rfl) ⟨1158990, by rfl⟩ : syracuseStep 3090641 = 2317981) B2317981
theorem B2060427 : Blo 2059435 2060427 := bstep (se 1 (by rfl) ⟨1545320, by rfl⟩ : syracuseStep 2060427 = 3090641) B3090641
theorem B6953957 : Blo 2059435 6953957 := bbase (se 4 (by rfl) ⟨651933, by rfl⟩ : syracuseStep 6953957 = 1303867) (by norm_num)
theorem B4635971 : Blo 2059435 4635971 := bstep (se 1 (by rfl) ⟨3476978, by rfl⟩ : syracuseStep 4635971 = 6953957) B6953957
theorem B3090647 : Blo 2059435 3090647 := bstep (se 1 (by rfl) ⟨2317985, by rfl⟩ : syracuseStep 3090647 = 4635971) B4635971
theorem B2060431 : Blo 2059435 2060431 := bstep (se 1 (by rfl) ⟨1545323, by rfl⟩ : syracuseStep 2060431 = 3090647) B3090647
theorem B3090653 : Blo 2059435 3090653 := bbase (se 3 (by rfl) ⟨579497, by rfl⟩ : syracuseStep 3090653 = 1158995) (by norm_num)
theorem B2060435 : Blo 2059435 2060435 := bstep (se 1 (by rfl) ⟨1545326, by rfl⟩ : syracuseStep 2060435 = 3090653) B3090653
theorem B4635989 : Blo 2059435 4635989 := bbase (se 11 (by rfl) ⟨3395, by rfl⟩ : syracuseStep 4635989 = 6791) (by norm_num)
theorem B3090659 : Blo 2059435 3090659 := bstep (se 1 (by rfl) ⟨2317994, by rfl⟩ : syracuseStep 3090659 = 4635989) B4635989
theorem B2060439 : Blo 2059435 2060439 := bstep (se 1 (by rfl) ⟨1545329, by rfl⟩ : syracuseStep 2060439 = 3090659) B3090659
theorem B2200289 : Blo 2059435 2200289 := bbase (se 2 (by rfl) ⟨825108, by rfl⟩ : syracuseStep 2200289 = 1650217) (by norm_num)
theorem B5867437 : Blo 2059435 5867437 := bstep (se 3 (by rfl) ⟨1100144, by rfl⟩ : syracuseStep 5867437 = 2200289) B2200289
theorem B7823249 : Blo 2059435 7823249 := bstep (se 2 (by rfl) ⟨2933718, by rfl⟩ : syracuseStep 7823249 = 5867437) B5867437
theorem B5215499 : Blo 2059435 5215499 := bstep (se 1 (by rfl) ⟨3911624, by rfl⟩ : syracuseStep 5215499 = 7823249) B7823249
theorem B3476999 : Blo 2059435 3476999 := bstep (se 1 (by rfl) ⟨2607749, by rfl⟩ : syracuseStep 3476999 = 5215499) B5215499
theorem B2317999 : Blo 2059435 2317999 := bstep (se 1 (by rfl) ⟨1738499, by rfl⟩ : syracuseStep 2317999 = 3476999) B3476999
theorem B3090665 : Blo 2059435 3090665 := bstep (se 2 (by rfl) ⟨1158999, by rfl⟩ : syracuseStep 3090665 = 2317999) B2317999
theorem B2060443 : Blo 2059435 2060443 := bstep (se 1 (by rfl) ⟨1545332, by rfl⟩ : syracuseStep 2060443 = 3090665) B3090665
theorem B4234109 : Blo 2059435 4234109 := bbase (se 3 (by rfl) ⟨793895, by rfl⟩ : syracuseStep 4234109 = 1587791) (by norm_num)
theorem B11290957 : Blo 2059435 11290957 := bstep (se 3 (by rfl) ⟨2117054, by rfl⟩ : syracuseStep 11290957 = 4234109) B4234109
theorem B60218437 : Blo 2059435 60218437 := bstep (se 4 (by rfl) ⟨5645478, by rfl⟩ : syracuseStep 60218437 = 11290957) B11290957
theorem B80291249 : Blo 2059435 80291249 := bstep (se 2 (by rfl) ⟨30109218, by rfl⟩ : syracuseStep 80291249 = 60218437) B60218437
theorem B53527499 : Blo 2059435 53527499 := bstep (se 1 (by rfl) ⟨40145624, by rfl⟩ : syracuseStep 53527499 = 80291249) B80291249
theorem B35684999 : Blo 2059435 35684999 := bstep (se 1 (by rfl) ⟨26763749, by rfl⟩ : syracuseStep 35684999 = 53527499) B53527499
theorem B23789999 : Blo 2059435 23789999 := bstep (se 1 (by rfl) ⟨17842499, by rfl⟩ : syracuseStep 23789999 = 35684999) B35684999
theorem B15859999 : Blo 2059435 15859999 := bstep (se 1 (by rfl) ⟨11894999, by rfl⟩ : syracuseStep 15859999 = 23789999) B23789999
theorem B21146665 : Blo 2059435 21146665 := bstep (se 2 (by rfl) ⟨7929999, by rfl⟩ : syracuseStep 21146665 = 15859999) B15859999
theorem B28195553 : Blo 2059435 28195553 := bstep (se 2 (by rfl) ⟨10573332, by rfl⟩ : syracuseStep 28195553 = 21146665) B21146665
theorem B18797035 : Blo 2059435 18797035 := bstep (se 1 (by rfl) ⟨14097776, by rfl⟩ : syracuseStep 18797035 = 28195553) B28195553
theorem B25062713 : Blo 2059435 25062713 := bstep (se 2 (by rfl) ⟨9398517, by rfl⟩ : syracuseStep 25062713 = 18797035) B18797035
theorem B16708475 : Blo 2059435 16708475 := bstep (se 1 (by rfl) ⟨12531356, by rfl⟩ : syracuseStep 16708475 = 25062713) B25062713
theorem B44555933 : Blo 2059435 44555933 := bstep (se 3 (by rfl) ⟨8354237, by rfl⟩ : syracuseStep 44555933 = 16708475) B16708475
theorem B29703955 : Blo 2059435 29703955 := bstep (se 1 (by rfl) ⟨22277966, by rfl⟩ : syracuseStep 29703955 = 44555933) B44555933
theorem B39605273 : Blo 2059435 39605273 := bstep (se 2 (by rfl) ⟨14851977, by rfl⟩ : syracuseStep 39605273 = 29703955) B29703955
theorem B26403515 : Blo 2059435 26403515 := bstep (se 1 (by rfl) ⟨19802636, by rfl⟩ : syracuseStep 26403515 = 39605273) B39605273
theorem B17602343 : Blo 2059435 17602343 := bstep (se 1 (by rfl) ⟨13201757, by rfl⟩ : syracuseStep 17602343 = 26403515) B26403515
theorem B11734895 : Blo 2059435 11734895 := bstep (se 1 (by rfl) ⟨8801171, by rfl⟩ : syracuseStep 11734895 = 17602343) B17602343
theorem B7823263 : Blo 2059435 7823263 := bstep (se 1 (by rfl) ⟨5867447, by rfl⟩ : syracuseStep 7823263 = 11734895) B11734895
theorem B10431017 : Blo 2059435 10431017 := bstep (se 2 (by rfl) ⟨3911631, by rfl⟩ : syracuseStep 10431017 = 7823263) B7823263
theorem B6954011 : Blo 2059435 6954011 := bstep (se 1 (by rfl) ⟨5215508, by rfl⟩ : syracuseStep 6954011 = 10431017) B10431017
theorem B4636007 : Blo 2059435 4636007 := bstep (se 1 (by rfl) ⟨3477005, by rfl⟩ : syracuseStep 4636007 = 6954011) B6954011
theorem B3090671 : Blo 2059435 3090671 := bstep (se 1 (by rfl) ⟨2318003, by rfl⟩ : syracuseStep 3090671 = 4636007) B4636007
theorem B2060447 : Blo 2059435 2060447 := bstep (se 1 (by rfl) ⟨1545335, by rfl⟩ : syracuseStep 2060447 = 3090671) B3090671
theorem B3090677 : Blo 2059435 3090677 := bbase (se 5 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 3090677 = 289751) (by norm_num)
theorem B2060451 : Blo 2059435 2060451 := bstep (se 1 (by rfl) ⟨1545338, by rfl⟩ : syracuseStep 2060451 = 3090677) B3090677
theorem B11139029 : Blo 2059435 11139029 := bbase (se 7 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 11139029 = 261071) (by norm_num)
theorem B7426019 : Blo 2059435 7426019 := bstep (se 1 (by rfl) ⟨5569514, by rfl⟩ : syracuseStep 7426019 = 11139029) B11139029
theorem B19802717 : Blo 2059435 19802717 := bstep (se 3 (by rfl) ⟨3713009, by rfl⟩ : syracuseStep 19802717 = 7426019) B7426019
theorem B13201811 : Blo 2059435 13201811 := bstep (se 1 (by rfl) ⟨9901358, by rfl⟩ : syracuseStep 13201811 = 19802717) B19802717
theorem B8801207 : Blo 2059435 8801207 := bstep (se 1 (by rfl) ⟨6600905, by rfl⟩ : syracuseStep 8801207 = 13201811) B13201811
theorem B5867471 : Blo 2059435 5867471 := bstep (se 1 (by rfl) ⟨4400603, by rfl⟩ : syracuseStep 5867471 = 8801207) B8801207
theorem B3911647 : Blo 2059435 3911647 := bstep (se 1 (by rfl) ⟨2933735, by rfl⟩ : syracuseStep 3911647 = 5867471) B5867471
theorem B5215529 : Blo 2059435 5215529 := bstep (se 2 (by rfl) ⟨1955823, by rfl⟩ : syracuseStep 5215529 = 3911647) B3911647
theorem B3477019 : Blo 2059435 3477019 := bstep (se 1 (by rfl) ⟨2607764, by rfl⟩ : syracuseStep 3477019 = 5215529) B5215529
theorem B4636025 : Blo 2059435 4636025 := bstep (se 2 (by rfl) ⟨1738509, by rfl⟩ : syracuseStep 4636025 = 3477019) B3477019
theorem B3090683 : Blo 2059435 3090683 := bstep (se 1 (by rfl) ⟨2318012, by rfl⟩ : syracuseStep 3090683 = 4636025) B4636025
theorem B2060455 : Blo 2059435 2060455 := bstep (se 1 (by rfl) ⟨1545341, by rfl⟩ : syracuseStep 2060455 = 3090683) B3090683
theorem B2318017 : Blo 2059435 2318017 := bbase (se 2 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 2318017 = 1738513) (by norm_num)
theorem B3090689 : Blo 2059435 3090689 := bstep (se 2 (by rfl) ⟨1159008, by rfl⟩ : syracuseStep 3090689 = 2318017) B2318017
theorem B2060459 : Blo 2059435 2060459 := bstep (se 1 (by rfl) ⟨1545344, by rfl⟩ : syracuseStep 2060459 = 3090689) B3090689
theorem B5215549 : Blo 2059435 5215549 := bbase (se 3 (by rfl) ⟨977915, by rfl⟩ : syracuseStep 5215549 = 1955831) (by norm_num)
theorem B6954065 : Blo 2059435 6954065 := bstep (se 2 (by rfl) ⟨2607774, by rfl⟩ : syracuseStep 6954065 = 5215549) B5215549
theorem B4636043 : Blo 2059435 4636043 := bstep (se 1 (by rfl) ⟨3477032, by rfl⟩ : syracuseStep 4636043 = 6954065) B6954065
theorem B3090695 : Blo 2059435 3090695 := bstep (se 1 (by rfl) ⟨2318021, by rfl⟩ : syracuseStep 3090695 = 4636043) B4636043
theorem B2060463 : Blo 2059435 2060463 := bstep (se 1 (by rfl) ⟨1545347, by rfl⟩ : syracuseStep 2060463 = 3090695) B3090695
theorem B3090701 : Blo 2059435 3090701 := bbase (se 3 (by rfl) ⟨579506, by rfl⟩ : syracuseStep 3090701 = 1159013) (by norm_num)
theorem B2060467 : Blo 2059435 2060467 := bstep (se 1 (by rfl) ⟨1545350, by rfl⟩ : syracuseStep 2060467 = 3090701) B3090701
theorem B4636061 : Blo 2059435 4636061 := bbase (se 3 (by rfl) ⟨869261, by rfl⟩ : syracuseStep 4636061 = 1738523) (by norm_num)
theorem B3090707 : Blo 2059435 3090707 := bstep (se 1 (by rfl) ⟨2318030, by rfl⟩ : syracuseStep 3090707 = 4636061) B4636061
theorem B2060471 : Blo 2059435 2060471 := bstep (se 1 (by rfl) ⟨1545353, by rfl⟩ : syracuseStep 2060471 = 3090707) B3090707
theorem B3477053 : Blo 2059435 3477053 := bbase (se 3 (by rfl) ⟨651947, by rfl⟩ : syracuseStep 3477053 = 1303895) (by norm_num)
theorem B2318035 : Blo 2059435 2318035 := bstep (se 1 (by rfl) ⟨1738526, by rfl⟩ : syracuseStep 2318035 = 3477053) B3477053
theorem B3090713 : Blo 2059435 3090713 := bstep (se 2 (by rfl) ⟨1159017, by rfl⟩ : syracuseStep 3090713 = 2318035) B2318035
theorem B2060475 : Blo 2059435 2060475 := bstep (se 1 (by rfl) ⟨1545356, by rfl⟩ : syracuseStep 2060475 = 3090713) B3090713
theorem B3713053 : Blo 2059435 3713053 := bbase (se 3 (by rfl) ⟨696197, by rfl⟩ : syracuseStep 3713053 = 1392395) (by norm_num)
theorem B4950737 : Blo 2059435 4950737 := bstep (se 2 (by rfl) ⟨1856526, by rfl⟩ : syracuseStep 4950737 = 3713053) B3713053
theorem B3300491 : Blo 2059435 3300491 := bstep (se 1 (by rfl) ⟨2475368, by rfl⟩ : syracuseStep 3300491 = 4950737) B4950737
theorem B2200327 : Blo 2059435 2200327 := bstep (se 1 (by rfl) ⟨1650245, by rfl⟩ : syracuseStep 2200327 = 3300491) B3300491
theorem B11735077 : Blo 2059435 11735077 := bstep (se 4 (by rfl) ⟨1100163, by rfl⟩ : syracuseStep 11735077 = 2200327) B2200327
theorem B15646769 : Blo 2059435 15646769 := bstep (se 2 (by rfl) ⟨5867538, by rfl⟩ : syracuseStep 15646769 = 11735077) B11735077
theorem B10431179 : Blo 2059435 10431179 := bstep (se 1 (by rfl) ⟨7823384, by rfl⟩ : syracuseStep 10431179 = 15646769) B15646769
theorem B6954119 : Blo 2059435 6954119 := bstep (se 1 (by rfl) ⟨5215589, by rfl⟩ : syracuseStep 6954119 = 10431179) B10431179
theorem B4636079 : Blo 2059435 4636079 := bstep (se 1 (by rfl) ⟨3477059, by rfl⟩ : syracuseStep 4636079 = 6954119) B6954119
theorem B3090719 : Blo 2059435 3090719 := bstep (se 1 (by rfl) ⟨2318039, by rfl⟩ : syracuseStep 3090719 = 4636079) B4636079
theorem B2060479 : Blo 2059435 2060479 := bstep (se 1 (by rfl) ⟨1545359, by rfl⟩ : syracuseStep 2060479 = 3090719) B3090719
theorem B3090725 : Blo 2059435 3090725 := bbase (se 4 (by rfl) ⟨289755, by rfl⟩ : syracuseStep 3090725 = 579511) (by norm_num)
theorem B2060483 : Blo 2059435 2060483 := bstep (se 1 (by rfl) ⟨1545362, by rfl⟩ : syracuseStep 2060483 = 3090725) B3090725
theorem B2607805 : Blo 2059435 2607805 := bbase (se 3 (by rfl) ⟨488963, by rfl⟩ : syracuseStep 2607805 = 977927) (by norm_num)
theorem B3477073 : Blo 2059435 3477073 := bstep (se 2 (by rfl) ⟨1303902, by rfl⟩ : syracuseStep 3477073 = 2607805) B2607805
theorem B4636097 : Blo 2059435 4636097 := bstep (se 2 (by rfl) ⟨1738536, by rfl⟩ : syracuseStep 4636097 = 3477073) B3477073
theorem B3090731 : Blo 2059435 3090731 := bstep (se 1 (by rfl) ⟨2318048, by rfl⟩ : syracuseStep 3090731 = 4636097) B4636097
theorem B2060487 : Blo 2059435 2060487 := bstep (se 1 (by rfl) ⟨1545365, by rfl⟩ : syracuseStep 2060487 = 3090731) B3090731
theorem B2318053 : Blo 2059435 2318053 := bbase (se 4 (by rfl) ⟨217317, by rfl⟩ : syracuseStep 2318053 = 434635) (by norm_num)
theorem B3090737 : Blo 2059435 3090737 := bstep (se 2 (by rfl) ⟨1159026, by rfl⟩ : syracuseStep 3090737 = 2318053) B2318053
theorem B2060491 : Blo 2059435 2060491 := bstep (se 1 (by rfl) ⟨1545368, by rfl⟩ : syracuseStep 2060491 = 3090737) B3090737
theorem B3300517 : Blo 2059435 3300517 := bbase (se 4 (by rfl) ⟨309423, by rfl⟩ : syracuseStep 3300517 = 618847) (by norm_num)
theorem B4400689 : Blo 2059435 4400689 := bstep (se 2 (by rfl) ⟨1650258, by rfl⟩ : syracuseStep 4400689 = 3300517) B3300517
theorem B5867585 : Blo 2059435 5867585 := bstep (se 2 (by rfl) ⟨2200344, by rfl⟩ : syracuseStep 5867585 = 4400689) B4400689
theorem B3911723 : Blo 2059435 3911723 := bstep (se 1 (by rfl) ⟨2933792, by rfl⟩ : syracuseStep 3911723 = 5867585) B5867585
theorem B2607815 : Blo 2059435 2607815 := bstep (se 1 (by rfl) ⟨1955861, by rfl⟩ : syracuseStep 2607815 = 3911723) B3911723
theorem B6954173 : Blo 2059435 6954173 := bstep (se 3 (by rfl) ⟨1303907, by rfl⟩ : syracuseStep 6954173 = 2607815) B2607815
theorem B4636115 : Blo 2059435 4636115 := bstep (se 1 (by rfl) ⟨3477086, by rfl⟩ : syracuseStep 4636115 = 6954173) B6954173
theorem B3090743 : Blo 2059435 3090743 := bstep (se 1 (by rfl) ⟨2318057, by rfl⟩ : syracuseStep 3090743 = 4636115) B4636115
theorem B2060495 : Blo 2059435 2060495 := bstep (se 1 (by rfl) ⟨1545371, by rfl⟩ : syracuseStep 2060495 = 3090743) B3090743
theorem B3090749 : Blo 2059435 3090749 := bbase (se 3 (by rfl) ⟨579515, by rfl⟩ : syracuseStep 3090749 = 1159031) (by norm_num)
theorem B2060499 : Blo 2059435 2060499 := bstep (se 1 (by rfl) ⟨1545374, by rfl⟩ : syracuseStep 2060499 = 3090749) B3090749
theorem B4636133 : Blo 2059435 4636133 := bbase (se 4 (by rfl) ⟨434637, by rfl⟩ : syracuseStep 4636133 = 869275) (by norm_num)
theorem B3090755 : Blo 2059435 3090755 := bstep (se 1 (by rfl) ⟨2318066, by rfl⟩ : syracuseStep 3090755 = 4636133) B4636133
theorem B2060503 : Blo 2059435 2060503 := bstep (se 1 (by rfl) ⟨1545377, by rfl⟩ : syracuseStep 2060503 = 3090755) B3090755
theorem B5215661 : Blo 2059435 5215661 := bbase (se 3 (by rfl) ⟨977936, by rfl⟩ : syracuseStep 5215661 = 1955873) (by norm_num)
theorem B3477107 : Blo 2059435 3477107 := bstep (se 1 (by rfl) ⟨2607830, by rfl⟩ : syracuseStep 3477107 = 5215661) B5215661
theorem B2318071 : Blo 2059435 2318071 := bstep (se 1 (by rfl) ⟨1738553, by rfl⟩ : syracuseStep 2318071 = 3477107) B3477107
theorem B3090761 : Blo 2059435 3090761 := bstep (se 2 (by rfl) ⟨1159035, by rfl⟩ : syracuseStep 3090761 = 2318071) B2318071
theorem B2060507 : Blo 2059435 2060507 := bstep (se 1 (by rfl) ⟨1545380, by rfl⟩ : syracuseStep 2060507 = 3090761) B3090761
theorem B8354501 : Blo 2059435 8354501 := bbase (se 4 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 8354501 = 1566469) (by norm_num)
theorem B5569667 : Blo 2059435 5569667 := bstep (se 1 (by rfl) ⟨4177250, by rfl⟩ : syracuseStep 5569667 = 8354501) B8354501
theorem B3713111 : Blo 2059435 3713111 := bstep (se 1 (by rfl) ⟨2784833, by rfl⟩ : syracuseStep 3713111 = 5569667) B5569667
theorem B2475407 : Blo 2059435 2475407 := bstep (se 1 (by rfl) ⟨1856555, by rfl⟩ : syracuseStep 2475407 = 3713111) B3713111
theorem B6601085 : Blo 2059435 6601085 := bstep (se 3 (by rfl) ⟨1237703, by rfl⟩ : syracuseStep 6601085 = 2475407) B2475407
theorem B4400723 : Blo 2059435 4400723 := bstep (se 1 (by rfl) ⟨3300542, by rfl⟩ : syracuseStep 4400723 = 6601085) B6601085
theorem B2933815 : Blo 2059435 2933815 := bstep (se 1 (by rfl) ⟨2200361, by rfl⟩ : syracuseStep 2933815 = 4400723) B4400723
theorem B3911753 : Blo 2059435 3911753 := bstep (se 2 (by rfl) ⟨1466907, by rfl⟩ : syracuseStep 3911753 = 2933815) B2933815
theorem B10431341 : Blo 2059435 10431341 := bstep (se 3 (by rfl) ⟨1955876, by rfl⟩ : syracuseStep 10431341 = 3911753) B3911753
theorem B6954227 : Blo 2059435 6954227 := bstep (se 1 (by rfl) ⟨5215670, by rfl⟩ : syracuseStep 6954227 = 10431341) B10431341
theorem B4636151 : Blo 2059435 4636151 := bstep (se 1 (by rfl) ⟨3477113, by rfl⟩ : syracuseStep 4636151 = 6954227) B6954227
theorem B3090767 : Blo 2059435 3090767 := bstep (se 1 (by rfl) ⟨2318075, by rfl⟩ : syracuseStep 3090767 = 4636151) B4636151
theorem B2060511 : Blo 2059435 2060511 := bstep (se 1 (by rfl) ⟨1545383, by rfl⟩ : syracuseStep 2060511 = 3090767) B3090767
theorem B3090773 : Blo 2059435 3090773 := bbase (se 10 (by rfl) ⟨4527, by rfl⟩ : syracuseStep 3090773 = 9055) (by norm_num)
theorem B2060515 : Blo 2059435 2060515 := bstep (se 1 (by rfl) ⟨1545386, by rfl⟩ : syracuseStep 2060515 = 3090773) B3090773
theorem B5867653 : Blo 2059435 5867653 := bbase (se 4 (by rfl) ⟨550092, by rfl⟩ : syracuseStep 5867653 = 1100185) (by norm_num)
theorem B7823537 : Blo 2059435 7823537 := bstep (se 2 (by rfl) ⟨2933826, by rfl⟩ : syracuseStep 7823537 = 5867653) B5867653
theorem B5215691 : Blo 2059435 5215691 := bstep (se 1 (by rfl) ⟨3911768, by rfl⟩ : syracuseStep 5215691 = 7823537) B7823537
theorem B3477127 : Blo 2059435 3477127 := bstep (se 1 (by rfl) ⟨2607845, by rfl⟩ : syracuseStep 3477127 = 5215691) B5215691
theorem B4636169 : Blo 2059435 4636169 := bstep (se 2 (by rfl) ⟨1738563, by rfl⟩ : syracuseStep 4636169 = 3477127) B3477127
theorem B3090779 : Blo 2059435 3090779 := bstep (se 1 (by rfl) ⟨2318084, by rfl⟩ : syracuseStep 3090779 = 4636169) B4636169
theorem B2060519 : Blo 2059435 2060519 := bstep (se 1 (by rfl) ⟨1545389, by rfl⟩ : syracuseStep 2060519 = 3090779) B3090779
theorem B2318089 : Blo 2059435 2318089 := bbase (se 2 (by rfl) ⟨869283, by rfl⟩ : syracuseStep 2318089 = 1738567) (by norm_num)
theorem B3090785 : Blo 2059435 3090785 := bstep (se 2 (by rfl) ⟨1159044, by rfl⟩ : syracuseStep 3090785 = 2318089) B2318089
theorem B2060523 : Blo 2059435 2060523 := bstep (se 1 (by rfl) ⟨1545392, by rfl⟩ : syracuseStep 2060523 = 3090785) B3090785
theorem B2349721 : Blo 2059435 2349721 := bbase (se 2 (by rfl) ⟨881145, by rfl⟩ : syracuseStep 2349721 = 1762291) (by norm_num)
theorem B3132961 : Blo 2059435 3132961 := bstep (se 2 (by rfl) ⟨1174860, by rfl⟩ : syracuseStep 3132961 = 2349721) B2349721
theorem B16709125 : Blo 2059435 16709125 := bstep (se 4 (by rfl) ⟨1566480, by rfl⟩ : syracuseStep 16709125 = 3132961) B3132961
theorem B22278833 : Blo 2059435 22278833 := bstep (se 2 (by rfl) ⟨8354562, by rfl⟩ : syracuseStep 22278833 = 16709125) B16709125
theorem B14852555 : Blo 2059435 14852555 := bstep (se 1 (by rfl) ⟨11139416, by rfl⟩ : syracuseStep 14852555 = 22278833) B22278833
theorem B9901703 : Blo 2059435 9901703 := bstep (se 1 (by rfl) ⟨7426277, by rfl⟩ : syracuseStep 9901703 = 14852555) B14852555
theorem B26404541 : Blo 2059435 26404541 := bstep (se 3 (by rfl) ⟨4950851, by rfl⟩ : syracuseStep 26404541 = 9901703) B9901703
theorem B17603027 : Blo 2059435 17603027 := bstep (se 1 (by rfl) ⟨13202270, by rfl⟩ : syracuseStep 17603027 = 26404541) B26404541
theorem B11735351 : Blo 2059435 11735351 := bstep (se 1 (by rfl) ⟨8801513, by rfl⟩ : syracuseStep 11735351 = 17603027) B17603027
theorem B7823567 : Blo 2059435 7823567 := bstep (se 1 (by rfl) ⟨5867675, by rfl⟩ : syracuseStep 7823567 = 11735351) B11735351
theorem B5215711 : Blo 2059435 5215711 := bstep (se 1 (by rfl) ⟨3911783, by rfl⟩ : syracuseStep 5215711 = 7823567) B7823567
theorem B6954281 : Blo 2059435 6954281 := bstep (se 2 (by rfl) ⟨2607855, by rfl⟩ : syracuseStep 6954281 = 5215711) B5215711
theorem B4636187 : Blo 2059435 4636187 := bstep (se 1 (by rfl) ⟨3477140, by rfl⟩ : syracuseStep 4636187 = 6954281) B6954281
theorem B3090791 : Blo 2059435 3090791 := bstep (se 1 (by rfl) ⟨2318093, by rfl⟩ : syracuseStep 3090791 = 4636187) B4636187
theorem B2060527 : Blo 2059435 2060527 := bstep (se 1 (by rfl) ⟨1545395, by rfl⟩ : syracuseStep 2060527 = 3090791) B3090791
theorem B3090797 : Blo 2059435 3090797 := bbase (se 3 (by rfl) ⟨579524, by rfl⟩ : syracuseStep 3090797 = 1159049) (by norm_num)
theorem B2060531 : Blo 2059435 2060531 := bstep (se 1 (by rfl) ⟨1545398, by rfl⟩ : syracuseStep 2060531 = 3090797) B3090797
theorem B4636205 : Blo 2059435 4636205 := bbase (se 3 (by rfl) ⟨869288, by rfl⟩ : syracuseStep 4636205 = 1738577) (by norm_num)
theorem B3090803 : Blo 2059435 3090803 := bstep (se 1 (by rfl) ⟨2318102, by rfl⟩ : syracuseStep 3090803 = 4636205) B4636205
theorem B2060535 : Blo 2059435 2060535 := bstep (se 1 (by rfl) ⟨1545401, by rfl⟩ : syracuseStep 2060535 = 3090803) B3090803
theorem B33418453 : Blo 2059435 33418453 := bbase (se 7 (by rfl) ⟨391622, by rfl⟩ : syracuseStep 33418453 = 783245) (by norm_num)
theorem B44557937 : Blo 2059435 44557937 := bstep (se 2 (by rfl) ⟨16709226, by rfl⟩ : syracuseStep 44557937 = 33418453) B33418453
theorem B29705291 : Blo 2059435 29705291 := bstep (se 1 (by rfl) ⟨22278968, by rfl⟩ : syracuseStep 29705291 = 44557937) B44557937
theorem B19803527 : Blo 2059435 19803527 := bstep (se 1 (by rfl) ⟨14852645, by rfl⟩ : syracuseStep 19803527 = 29705291) B29705291
theorem B13202351 : Blo 2059435 13202351 := bstep (se 1 (by rfl) ⟨9901763, by rfl⟩ : syracuseStep 13202351 = 19803527) B19803527
theorem B8801567 : Blo 2059435 8801567 := bstep (se 1 (by rfl) ⟨6601175, by rfl⟩ : syracuseStep 8801567 = 13202351) B13202351
theorem B5867711 : Blo 2059435 5867711 := bstep (se 1 (by rfl) ⟨4400783, by rfl⟩ : syracuseStep 5867711 = 8801567) B8801567
theorem B3911807 : Blo 2059435 3911807 := bstep (se 1 (by rfl) ⟨2933855, by rfl⟩ : syracuseStep 3911807 = 5867711) B5867711
theorem B2607871 : Blo 2059435 2607871 := bstep (se 1 (by rfl) ⟨1955903, by rfl⟩ : syracuseStep 2607871 = 3911807) B3911807
theorem B3477161 : Blo 2059435 3477161 := bstep (se 2 (by rfl) ⟨1303935, by rfl⟩ : syracuseStep 3477161 = 2607871) B2607871
theorem B2318107 : Blo 2059435 2318107 := bstep (se 1 (by rfl) ⟨1738580, by rfl⟩ : syracuseStep 2318107 = 3477161) B3477161
theorem B3090809 : Blo 2059435 3090809 := bstep (se 2 (by rfl) ⟨1159053, by rfl⟩ : syracuseStep 3090809 = 2318107) B2318107
theorem B2060539 : Blo 2059435 2060539 := bstep (se 1 (by rfl) ⟨1545404, by rfl⟩ : syracuseStep 2060539 = 3090809) B3090809
theorem B2475445 : Blo 2059435 2475445 := bbase (se 5 (by rfl) ⟨116036, by rfl⟩ : syracuseStep 2475445 = 232073) (by norm_num)
theorem B3300593 : Blo 2059435 3300593 := bstep (se 2 (by rfl) ⟨1237722, by rfl⟩ : syracuseStep 3300593 = 2475445) B2475445
theorem B35206325 : Blo 2059435 35206325 := bstep (se 5 (by rfl) ⟨1650296, by rfl⟩ : syracuseStep 35206325 = 3300593) B3300593
theorem B23470883 : Blo 2059435 23470883 := bstep (se 1 (by rfl) ⟨17603162, by rfl⟩ : syracuseStep 23470883 = 35206325) B35206325
theorem B15647255 : Blo 2059435 15647255 := bstep (se 1 (by rfl) ⟨11735441, by rfl⟩ : syracuseStep 15647255 = 23470883) B23470883
theorem B10431503 : Blo 2059435 10431503 := bstep (se 1 (by rfl) ⟨7823627, by rfl⟩ : syracuseStep 10431503 = 15647255) B15647255
theorem B6954335 : Blo 2059435 6954335 := bstep (se 1 (by rfl) ⟨5215751, by rfl⟩ : syracuseStep 6954335 = 10431503) B10431503
theorem B4636223 : Blo 2059435 4636223 := bstep (se 1 (by rfl) ⟨3477167, by rfl⟩ : syracuseStep 4636223 = 6954335) B6954335
theorem B3090815 : Blo 2059435 3090815 := bstep (se 1 (by rfl) ⟨2318111, by rfl⟩ : syracuseStep 3090815 = 4636223) B4636223
theorem B2060543 : Blo 2059435 2060543 := bstep (se 1 (by rfl) ⟨1545407, by rfl⟩ : syracuseStep 2060543 = 3090815) B3090815
theorem B3090821 : Blo 2059435 3090821 := bbase (se 4 (by rfl) ⟨289764, by rfl⟩ : syracuseStep 3090821 = 579529) (by norm_num)
theorem B2060547 : Blo 2059435 2060547 := bstep (se 1 (by rfl) ⟨1545410, by rfl⟩ : syracuseStep 2060547 = 3090821) B3090821
theorem B3477181 : Blo 2059435 3477181 := bbase (se 3 (by rfl) ⟨651971, by rfl⟩ : syracuseStep 3477181 = 1303943) (by norm_num)
theorem B4636241 : Blo 2059435 4636241 := bstep (se 2 (by rfl) ⟨1738590, by rfl⟩ : syracuseStep 4636241 = 3477181) B3477181
theorem B3090827 : Blo 2059435 3090827 := bstep (se 1 (by rfl) ⟨2318120, by rfl⟩ : syracuseStep 3090827 = 4636241) B4636241
theorem B2060551 : Blo 2059435 2060551 := bstep (se 1 (by rfl) ⟨1545413, by rfl⟩ : syracuseStep 2060551 = 3090827) B3090827
theorem B2318125 : Blo 2059435 2318125 := bbase (se 3 (by rfl) ⟨434648, by rfl⟩ : syracuseStep 2318125 = 869297) (by norm_num)
theorem B3090833 : Blo 2059435 3090833 := bstep (se 2 (by rfl) ⟨1159062, by rfl⟩ : syracuseStep 3090833 = 2318125) B2318125
theorem B2060555 : Blo 2059435 2060555 := bstep (se 1 (by rfl) ⟨1545416, by rfl⟩ : syracuseStep 2060555 = 3090833) B3090833
theorem B6954389 : Blo 2059435 6954389 := bbase (se 6 (by rfl) ⟨162993, by rfl⟩ : syracuseStep 6954389 = 325987) (by norm_num)
theorem B4636259 : Blo 2059435 4636259 := bstep (se 1 (by rfl) ⟨3477194, by rfl⟩ : syracuseStep 4636259 = 6954389) B6954389
theorem B3090839 : Blo 2059435 3090839 := bstep (se 1 (by rfl) ⟨2318129, by rfl⟩ : syracuseStep 3090839 = 4636259) B4636259
theorem B2060559 : Blo 2059435 2060559 := bstep (se 1 (by rfl) ⟨1545419, by rfl⟩ : syracuseStep 2060559 = 3090839) B3090839
theorem B3090845 : Blo 2059435 3090845 := bbase (se 3 (by rfl) ⟨579533, by rfl⟩ : syracuseStep 3090845 = 1159067) (by norm_num)
theorem B2060563 : Blo 2059435 2060563 := bstep (se 1 (by rfl) ⟨1545422, by rfl⟩ : syracuseStep 2060563 = 3090845) B3090845
theorem B4636277 : Blo 2059435 4636277 := bbase (se 5 (by rfl) ⟨217325, by rfl⟩ : syracuseStep 4636277 = 434651) (by norm_num)
theorem B3090851 : Blo 2059435 3090851 := bstep (se 1 (by rfl) ⟨2318138, by rfl⟩ : syracuseStep 3090851 = 4636277) B4636277
theorem B2060567 : Blo 2059435 2060567 := bstep (se 1 (by rfl) ⟨1545425, by rfl⟩ : syracuseStep 2060567 = 3090851) B3090851
theorem B5569829 : Blo 2059435 5569829 := bbase (se 4 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 5569829 = 1044343) (by norm_num)
theorem B3713219 : Blo 2059435 3713219 := bstep (se 1 (by rfl) ⟨2784914, by rfl⟩ : syracuseStep 3713219 = 5569829) B5569829
theorem B2475479 : Blo 2059435 2475479 := bstep (se 1 (by rfl) ⟨1856609, by rfl⟩ : syracuseStep 2475479 = 3713219) B3713219
theorem B6601277 : Blo 2059435 6601277 := bstep (se 3 (by rfl) ⟨1237739, by rfl⟩ : syracuseStep 6601277 = 2475479) B2475479
theorem B17603405 : Blo 2059435 17603405 := bstep (se 3 (by rfl) ⟨3300638, by rfl⟩ : syracuseStep 17603405 = 6601277) B6601277
theorem B11735603 : Blo 2059435 11735603 := bstep (se 1 (by rfl) ⟨8801702, by rfl⟩ : syracuseStep 11735603 = 17603405) B17603405
theorem B7823735 : Blo 2059435 7823735 := bstep (se 1 (by rfl) ⟨5867801, by rfl⟩ : syracuseStep 7823735 = 11735603) B11735603
theorem B5215823 : Blo 2059435 5215823 := bstep (se 1 (by rfl) ⟨3911867, by rfl⟩ : syracuseStep 5215823 = 7823735) B7823735
theorem B3477215 : Blo 2059435 3477215 := bstep (se 1 (by rfl) ⟨2607911, by rfl⟩ : syracuseStep 3477215 = 5215823) B5215823
theorem B2318143 : Blo 2059435 2318143 := bstep (se 1 (by rfl) ⟨1738607, by rfl⟩ : syracuseStep 2318143 = 3477215) B3477215
theorem B3090857 : Blo 2059435 3090857 := bstep (se 2 (by rfl) ⟨1159071, by rfl⟩ : syracuseStep 3090857 = 2318143) B2318143
theorem B2060571 : Blo 2059435 2060571 := bstep (se 1 (by rfl) ⟨1545428, by rfl⟩ : syracuseStep 2060571 = 3090857) B3090857
theorem B7823749 : Blo 2059435 7823749 := bbase (se 4 (by rfl) ⟨733476, by rfl⟩ : syracuseStep 7823749 = 1466953) (by norm_num)
theorem B10431665 : Blo 2059435 10431665 := bstep (se 2 (by rfl) ⟨3911874, by rfl⟩ : syracuseStep 10431665 = 7823749) B7823749
theorem B6954443 : Blo 2059435 6954443 := bstep (se 1 (by rfl) ⟨5215832, by rfl⟩ : syracuseStep 6954443 = 10431665) B10431665
theorem B4636295 : Blo 2059435 4636295 := bstep (se 1 (by rfl) ⟨3477221, by rfl⟩ : syracuseStep 4636295 = 6954443) B6954443
theorem B3090863 : Blo 2059435 3090863 := bstep (se 1 (by rfl) ⟨2318147, by rfl⟩ : syracuseStep 3090863 = 4636295) B4636295
theorem B2060575 : Blo 2059435 2060575 := bstep (se 1 (by rfl) ⟨1545431, by rfl⟩ : syracuseStep 2060575 = 3090863) B3090863
theorem B3090869 : Blo 2059435 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B2060579 : Blo 2059435 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B5215853 : Blo 2059435 5215853 := bbase (se 3 (by rfl) ⟨977972, by rfl⟩ : syracuseStep 5215853 = 1955945) (by norm_num)
theorem B3477235 : Blo 2059435 3477235 := bstep (se 1 (by rfl) ⟨2607926, by rfl⟩ : syracuseStep 3477235 = 5215853) B5215853
theorem B4636313 : Blo 2059435 4636313 := bstep (se 2 (by rfl) ⟨1738617, by rfl⟩ : syracuseStep 4636313 = 3477235) B3477235
theorem B3090875 : Blo 2059435 3090875 := bstep (se 1 (by rfl) ⟨2318156, by rfl⟩ : syracuseStep 3090875 = 4636313) B4636313
theorem B2060583 : Blo 2059435 2060583 := bstep (se 1 (by rfl) ⟨1545437, by rfl⟩ : syracuseStep 2060583 = 3090875) B3090875
theorem B2318161 : Blo 2059435 2318161 := bbase (se 2 (by rfl) ⟨869310, by rfl⟩ : syracuseStep 2318161 = 1738621) (by norm_num)
theorem B3090881 : Blo 2059435 3090881 := bstep (se 2 (by rfl) ⟨1159080, by rfl⟩ : syracuseStep 3090881 = 2318161) B2318161
theorem B2060587 : Blo 2059435 2060587 := bstep (se 1 (by rfl) ⟨1545440, by rfl⟩ : syracuseStep 2060587 = 3090881) B3090881
theorem B20074229 : Blo 2059435 20074229 := bbase (se 5 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 20074229 = 1881959) (by norm_num)
theorem B13382819 : Blo 2059435 13382819 := bstep (se 1 (by rfl) ⟨10037114, by rfl⟩ : syracuseStep 13382819 = 20074229) B20074229
theorem B8921879 : Blo 2059435 8921879 := bstep (se 1 (by rfl) ⟨6691409, by rfl⟩ : syracuseStep 8921879 = 13382819) B13382819
theorem B5947919 : Blo 2059435 5947919 := bstep (se 1 (by rfl) ⟨4460939, by rfl⟩ : syracuseStep 5947919 = 8921879) B8921879
theorem B3965279 : Blo 2059435 3965279 := bstep (se 1 (by rfl) ⟨2973959, by rfl⟩ : syracuseStep 3965279 = 5947919) B5947919
theorem B10574077 : Blo 2059435 10574077 := bstep (se 3 (by rfl) ⟨1982639, by rfl⟩ : syracuseStep 10574077 = 3965279) B3965279
theorem B14098769 : Blo 2059435 14098769 := bstep (se 2 (by rfl) ⟨5287038, by rfl⟩ : syracuseStep 14098769 = 10574077) B10574077
theorem B9399179 : Blo 2059435 9399179 := bstep (se 1 (by rfl) ⟨7049384, by rfl⟩ : syracuseStep 9399179 = 14098769) B14098769
theorem B25064477 : Blo 2059435 25064477 := bstep (se 3 (by rfl) ⟨4699589, by rfl⟩ : syracuseStep 25064477 = 9399179) B9399179
theorem B16709651 : Blo 2059435 16709651 := bstep (se 1 (by rfl) ⟨12532238, by rfl⟩ : syracuseStep 16709651 = 25064477) B25064477
theorem B11139767 : Blo 2059435 11139767 := bstep (se 1 (by rfl) ⟨8354825, by rfl⟩ : syracuseStep 11139767 = 16709651) B16709651
theorem B7426511 : Blo 2059435 7426511 := bstep (se 1 (by rfl) ⟨5569883, by rfl⟩ : syracuseStep 7426511 = 11139767) B11139767
theorem B4951007 : Blo 2059435 4951007 := bstep (se 1 (by rfl) ⟨3713255, by rfl⟩ : syracuseStep 4951007 = 7426511) B7426511
theorem B3300671 : Blo 2059435 3300671 := bstep (se 1 (by rfl) ⟨2475503, by rfl⟩ : syracuseStep 3300671 = 4951007) B4951007
theorem B2200447 : Blo 2059435 2200447 := bstep (se 1 (by rfl) ⟨1650335, by rfl⟩ : syracuseStep 2200447 = 3300671) B3300671
theorem B2933929 : Blo 2059435 2933929 := bstep (se 2 (by rfl) ⟨1100223, by rfl⟩ : syracuseStep 2933929 = 2200447) B2200447
theorem B3911905 : Blo 2059435 3911905 := bstep (se 2 (by rfl) ⟨1466964, by rfl⟩ : syracuseStep 3911905 = 2933929) B2933929
theorem B5215873 : Blo 2059435 5215873 := bstep (se 2 (by rfl) ⟨1955952, by rfl⟩ : syracuseStep 5215873 = 3911905) B3911905
theorem B6954497 : Blo 2059435 6954497 := bstep (se 2 (by rfl) ⟨2607936, by rfl⟩ : syracuseStep 6954497 = 5215873) B5215873
theorem B4636331 : Blo 2059435 4636331 := bstep (se 1 (by rfl) ⟨3477248, by rfl⟩ : syracuseStep 4636331 = 6954497) B6954497
theorem B3090887 : Blo 2059435 3090887 := bstep (se 1 (by rfl) ⟨2318165, by rfl⟩ : syracuseStep 3090887 = 4636331) B4636331
theorem B2060591 : Blo 2059435 2060591 := bstep (se 1 (by rfl) ⟨1545443, by rfl⟩ : syracuseStep 2060591 = 3090887) B3090887
theorem B3090893 : Blo 2059435 3090893 := bbase (se 3 (by rfl) ⟨579542, by rfl⟩ : syracuseStep 3090893 = 1159085) (by norm_num)
theorem B2060595 : Blo 2059435 2060595 := bstep (se 1 (by rfl) ⟨1545446, by rfl⟩ : syracuseStep 2060595 = 3090893) B3090893
theorem B4636349 : Blo 2059435 4636349 := bbase (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) (by norm_num)
theorem B3090899 : Blo 2059435 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B2060599 : Blo 2059435 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B3477269 : Blo 2059435 3477269 := bbase (se 6 (by rfl) ⟨81498, by rfl⟩ : syracuseStep 3477269 = 162997) (by norm_num)
theorem B2318179 : Blo 2059435 2318179 := bstep (se 1 (by rfl) ⟨1738634, by rfl⟩ : syracuseStep 2318179 = 3477269) B3477269
theorem B3090905 : Blo 2059435 3090905 := bstep (se 2 (by rfl) ⟨1159089, by rfl⟩ : syracuseStep 3090905 = 2318179) B2318179
theorem B2060603 : Blo 2059435 2060603 := bstep (se 1 (by rfl) ⟨1545452, by rfl⟩ : syracuseStep 2060603 = 3090905) B3090905
theorem B6266165 : Blo 2059435 6266165 := bbase (se 5 (by rfl) ⟨293726, by rfl⟩ : syracuseStep 6266165 = 587453) (by norm_num)
theorem B66839093 : Blo 2059435 66839093 := bstep (se 5 (by rfl) ⟨3133082, by rfl⟩ : syracuseStep 66839093 = 6266165) B6266165
theorem B44559395 : Blo 2059435 44559395 := bstep (se 1 (by rfl) ⟨33419546, by rfl⟩ : syracuseStep 44559395 = 66839093) B66839093
theorem B29706263 : Blo 2059435 29706263 := bstep (se 1 (by rfl) ⟨22279697, by rfl⟩ : syracuseStep 29706263 = 44559395) B44559395
theorem B19804175 : Blo 2059435 19804175 := bstep (se 1 (by rfl) ⟨14853131, by rfl⟩ : syracuseStep 19804175 = 29706263) B29706263
theorem B13202783 : Blo 2059435 13202783 := bstep (se 1 (by rfl) ⟨9902087, by rfl⟩ : syracuseStep 13202783 = 19804175) B19804175
theorem B8801855 : Blo 2059435 8801855 := bstep (se 1 (by rfl) ⟨6601391, by rfl⟩ : syracuseStep 8801855 = 13202783) B13202783
theorem B5867903 : Blo 2059435 5867903 := bstep (se 1 (by rfl) ⟨4400927, by rfl⟩ : syracuseStep 5867903 = 8801855) B8801855
theorem B15647741 : Blo 2059435 15647741 := bstep (se 3 (by rfl) ⟨2933951, by rfl⟩ : syracuseStep 15647741 = 5867903) B5867903
theorem B10431827 : Blo 2059435 10431827 := bstep (se 1 (by rfl) ⟨7823870, by rfl⟩ : syracuseStep 10431827 = 15647741) B15647741
theorem B6954551 : Blo 2059435 6954551 := bstep (se 1 (by rfl) ⟨5215913, by rfl⟩ : syracuseStep 6954551 = 10431827) B10431827
theorem B4636367 : Blo 2059435 4636367 := bstep (se 1 (by rfl) ⟨3477275, by rfl⟩ : syracuseStep 4636367 = 6954551) B6954551
theorem B3090911 : Blo 2059435 3090911 := bstep (se 1 (by rfl) ⟨2318183, by rfl⟩ : syracuseStep 3090911 = 4636367) B4636367
theorem B2060607 : Blo 2059435 2060607 := bstep (se 1 (by rfl) ⟨1545455, by rfl⟩ : syracuseStep 2060607 = 3090911) B3090911
theorem B3090917 : Blo 2059435 3090917 := bbase (se 4 (by rfl) ⟨289773, by rfl⟩ : syracuseStep 3090917 = 579547) (by norm_num)
theorem B2060611 : Blo 2059435 2060611 := bstep (se 1 (by rfl) ⟨1545458, by rfl⟩ : syracuseStep 2060611 = 3090917) B3090917
theorem B13202837 : Blo 2059435 13202837 := bbase (se 6 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 13202837 = 618883) (by norm_num)
theorem B8801891 : Blo 2059435 8801891 := bstep (se 1 (by rfl) ⟨6601418, by rfl⟩ : syracuseStep 8801891 = 13202837) B13202837
theorem B5867927 : Blo 2059435 5867927 := bstep (se 1 (by rfl) ⟨4400945, by rfl⟩ : syracuseStep 5867927 = 8801891) B8801891
theorem B3911951 : Blo 2059435 3911951 := bstep (se 1 (by rfl) ⟨2933963, by rfl⟩ : syracuseStep 3911951 = 5867927) B5867927
theorem B2607967 : Blo 2059435 2607967 := bstep (se 1 (by rfl) ⟨1955975, by rfl⟩ : syracuseStep 2607967 = 3911951) B3911951
theorem B3477289 : Blo 2059435 3477289 := bstep (se 2 (by rfl) ⟨1303983, by rfl⟩ : syracuseStep 3477289 = 2607967) B2607967
theorem B4636385 : Blo 2059435 4636385 := bstep (se 2 (by rfl) ⟨1738644, by rfl⟩ : syracuseStep 4636385 = 3477289) B3477289
theorem B3090923 : Blo 2059435 3090923 := bstep (se 1 (by rfl) ⟨2318192, by rfl⟩ : syracuseStep 3090923 = 4636385) B4636385
theorem B2060615 : Blo 2059435 2060615 := bstep (se 1 (by rfl) ⟨1545461, by rfl⟩ : syracuseStep 2060615 = 3090923) B3090923
theorem B2318197 : Blo 2059435 2318197 := bbase (se 5 (by rfl) ⟨108665, by rfl⟩ : syracuseStep 2318197 = 217331) (by norm_num)
theorem B3090929 : Blo 2059435 3090929 := bstep (se 2 (by rfl) ⟨1159098, by rfl⟩ : syracuseStep 3090929 = 2318197) B2318197
theorem B2060619 : Blo 2059435 2060619 := bstep (se 1 (by rfl) ⟨1545464, by rfl⟩ : syracuseStep 2060619 = 3090929) B3090929
theorem B2607977 : Blo 2059435 2607977 := bbase (se 2 (by rfl) ⟨977991, by rfl⟩ : syracuseStep 2607977 = 1955983) (by norm_num)
theorem B6954605 : Blo 2059435 6954605 := bstep (se 3 (by rfl) ⟨1303988, by rfl⟩ : syracuseStep 6954605 = 2607977) B2607977
theorem B4636403 : Blo 2059435 4636403 := bstep (se 1 (by rfl) ⟨3477302, by rfl⟩ : syracuseStep 4636403 = 6954605) B6954605
theorem B3090935 : Blo 2059435 3090935 := bstep (se 1 (by rfl) ⟨2318201, by rfl⟩ : syracuseStep 3090935 = 4636403) B4636403
theorem B2060623 : Blo 2059435 2060623 := bstep (se 1 (by rfl) ⟨1545467, by rfl⟩ : syracuseStep 2060623 = 3090935) B3090935
theorem B3090941 : Blo 2059435 3090941 := bbase (se 3 (by rfl) ⟨579551, by rfl⟩ : syracuseStep 3090941 = 1159103) (by norm_num)
theorem B2060627 : Blo 2059435 2060627 := bstep (se 1 (by rfl) ⟨1545470, by rfl⟩ : syracuseStep 2060627 = 3090941) B3090941
theorem B4636421 : Blo 2059435 4636421 := bbase (se 4 (by rfl) ⟨434664, by rfl⟩ : syracuseStep 4636421 = 869329) (by norm_num)
theorem B3090947 : Blo 2059435 3090947 := bstep (se 1 (by rfl) ⟨2318210, by rfl⟩ : syracuseStep 3090947 = 4636421) B4636421
theorem B2060631 : Blo 2059435 2060631 := bstep (se 1 (by rfl) ⟨1545473, by rfl⟩ : syracuseStep 2060631 = 3090947) B3090947
theorem B3911989 : Blo 2059435 3911989 := bbase (se 5 (by rfl) ⟨183374, by rfl⟩ : syracuseStep 3911989 = 366749) (by norm_num)
theorem B5215985 : Blo 2059435 5215985 := bstep (se 2 (by rfl) ⟨1955994, by rfl⟩ : syracuseStep 5215985 = 3911989) B3911989
theorem B3477323 : Blo 2059435 3477323 := bstep (se 1 (by rfl) ⟨2607992, by rfl⟩ : syracuseStep 3477323 = 5215985) B5215985
theorem B2318215 : Blo 2059435 2318215 := bstep (se 1 (by rfl) ⟨1738661, by rfl⟩ : syracuseStep 2318215 = 3477323) B3477323
theorem B3090953 : Blo 2059435 3090953 := bstep (se 2 (by rfl) ⟨1159107, by rfl⟩ : syracuseStep 3090953 = 2318215) B2318215
theorem B2060635 : Blo 2059435 2060635 := bstep (se 1 (by rfl) ⟨1545476, by rfl⟩ : syracuseStep 2060635 = 3090953) B3090953
theorem B10431989 : Blo 2059435 10431989 := bbase (se 5 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 10431989 = 977999) (by norm_num)
theorem B6954659 : Blo 2059435 6954659 := bstep (se 1 (by rfl) ⟨5215994, by rfl⟩ : syracuseStep 6954659 = 10431989) B10431989
theorem B4636439 : Blo 2059435 4636439 := bstep (se 1 (by rfl) ⟨3477329, by rfl⟩ : syracuseStep 4636439 = 6954659) B6954659
theorem B3090959 : Blo 2059435 3090959 := bstep (se 1 (by rfl) ⟨2318219, by rfl⟩ : syracuseStep 3090959 = 4636439) B4636439
theorem B2060639 : Blo 2059435 2060639 := bstep (se 1 (by rfl) ⟨1545479, by rfl⟩ : syracuseStep 2060639 = 3090959) B3090959
theorem B3090965 : Blo 2059435 3090965 := bbase (se 6 (by rfl) ⟨72444, by rfl⟩ : syracuseStep 3090965 = 144889) (by norm_num)
theorem B2060643 : Blo 2059435 2060643 := bstep (se 1 (by rfl) ⟨1545482, by rfl⟩ : syracuseStep 2060643 = 3090965) B3090965
theorem B17604053 : Blo 2059435 17604053 := bbase (se 7 (by rfl) ⟨206297, by rfl⟩ : syracuseStep 17604053 = 412595) (by norm_num)
theorem B11736035 : Blo 2059435 11736035 := bstep (se 1 (by rfl) ⟨8802026, by rfl⟩ : syracuseStep 11736035 = 17604053) B17604053
theorem B7824023 : Blo 2059435 7824023 := bstep (se 1 (by rfl) ⟨5868017, by rfl⟩ : syracuseStep 7824023 = 11736035) B11736035
theorem B5216015 : Blo 2059435 5216015 := bstep (se 1 (by rfl) ⟨3912011, by rfl⟩ : syracuseStep 5216015 = 7824023) B7824023
theorem B3477343 : Blo 2059435 3477343 := bstep (se 1 (by rfl) ⟨2608007, by rfl⟩ : syracuseStep 3477343 = 5216015) B5216015
theorem B4636457 : Blo 2059435 4636457 := bstep (se 2 (by rfl) ⟨1738671, by rfl⟩ : syracuseStep 4636457 = 3477343) B3477343
theorem B3090971 : Blo 2059435 3090971 := bstep (se 1 (by rfl) ⟨2318228, by rfl⟩ : syracuseStep 3090971 = 4636457) B4636457
theorem B2060647 : Blo 2059435 2060647 := bstep (se 1 (by rfl) ⟨1545485, by rfl⟩ : syracuseStep 2060647 = 3090971) B3090971
theorem B2318233 : Blo 2059435 2318233 := bbase (se 2 (by rfl) ⟨869337, by rfl⟩ : syracuseStep 2318233 = 1738675) (by norm_num)
theorem B3090977 : Blo 2059435 3090977 := bstep (se 2 (by rfl) ⟨1159116, by rfl⟩ : syracuseStep 3090977 = 2318233) B2318233
theorem B2060651 : Blo 2059435 2060651 := bstep (se 1 (by rfl) ⟨1545488, by rfl⟩ : syracuseStep 2060651 = 3090977) B3090977
theorem B7824053 : Blo 2059435 7824053 := bbase (se 5 (by rfl) ⟨366752, by rfl⟩ : syracuseStep 7824053 = 733505) (by norm_num)
theorem B5216035 : Blo 2059435 5216035 := bstep (se 1 (by rfl) ⟨3912026, by rfl⟩ : syracuseStep 5216035 = 7824053) B7824053
theorem B6954713 : Blo 2059435 6954713 := bstep (se 2 (by rfl) ⟨2608017, by rfl⟩ : syracuseStep 6954713 = 5216035) B5216035
theorem B4636475 : Blo 2059435 4636475 := bstep (se 1 (by rfl) ⟨3477356, by rfl⟩ : syracuseStep 4636475 = 6954713) B6954713
theorem B3090983 : Blo 2059435 3090983 := bstep (se 1 (by rfl) ⟨2318237, by rfl⟩ : syracuseStep 3090983 = 4636475) B4636475
theorem B2060655 : Blo 2059435 2060655 := bstep (se 1 (by rfl) ⟨1545491, by rfl⟩ : syracuseStep 2060655 = 3090983) B3090983
theorem B3090989 : Blo 2059435 3090989 := bbase (se 3 (by rfl) ⟨579560, by rfl⟩ : syracuseStep 3090989 = 1159121) (by norm_num)
theorem B2060659 : Blo 2059435 2060659 := bstep (se 1 (by rfl) ⟨1545494, by rfl⟩ : syracuseStep 2060659 = 3090989) B3090989
theorem B4636493 : Blo 2059435 4636493 := bbase (se 3 (by rfl) ⟨869342, by rfl⟩ : syracuseStep 4636493 = 1738685) (by norm_num)
theorem B3090995 : Blo 2059435 3090995 := bstep (se 1 (by rfl) ⟨2318246, by rfl⟩ : syracuseStep 3090995 = 4636493) B4636493
theorem B2060663 : Blo 2059435 2060663 := bstep (se 1 (by rfl) ⟨1545497, by rfl⟩ : syracuseStep 2060663 = 3090995) B3090995
theorem B2608033 : Blo 2059435 2608033 := bbase (se 2 (by rfl) ⟨978012, by rfl⟩ : syracuseStep 2608033 = 1956025) (by norm_num)
theorem B3477377 : Blo 2059435 3477377 := bstep (se 2 (by rfl) ⟨1304016, by rfl⟩ : syracuseStep 3477377 = 2608033) B2608033
theorem B2318251 : Blo 2059435 2318251 := bstep (se 1 (by rfl) ⟨1738688, by rfl⟩ : syracuseStep 2318251 = 3477377) B3477377
theorem B3091001 : Blo 2059435 3091001 := bstep (se 2 (by rfl) ⟨1159125, by rfl⟩ : syracuseStep 3091001 = 2318251) B2318251
theorem B2060667 : Blo 2059435 2060667 := bstep (se 1 (by rfl) ⟨1545500, by rfl⟩ : syracuseStep 2060667 = 3091001) B3091001
theorem B23472341 : Blo 2059435 23472341 := bbase (se 7 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 23472341 = 550133) (by norm_num)
theorem B15648227 : Blo 2059435 15648227 := bstep (se 1 (by rfl) ⟨11736170, by rfl⟩ : syracuseStep 15648227 = 23472341) B23472341
theorem B10432151 : Blo 2059435 10432151 := bstep (se 1 (by rfl) ⟨7824113, by rfl⟩ : syracuseStep 10432151 = 15648227) B15648227
theorem B6954767 : Blo 2059435 6954767 := bstep (se 1 (by rfl) ⟨5216075, by rfl⟩ : syracuseStep 6954767 = 10432151) B10432151
theorem B4636511 : Blo 2059435 4636511 := bstep (se 1 (by rfl) ⟨3477383, by rfl⟩ : syracuseStep 4636511 = 6954767) B6954767
theorem B3091007 : Blo 2059435 3091007 := bstep (se 1 (by rfl) ⟨2318255, by rfl⟩ : syracuseStep 3091007 = 4636511) B4636511
theorem B2060671 : Blo 2059435 2060671 := bstep (se 1 (by rfl) ⟨1545503, by rfl⟩ : syracuseStep 2060671 = 3091007) B3091007
theorem B3091013 : Blo 2059435 3091013 := bbase (se 4 (by rfl) ⟨289782, by rfl⟩ : syracuseStep 3091013 = 579565) (by norm_num)
theorem B2060675 : Blo 2059435 2060675 := bstep (se 1 (by rfl) ⟨1545506, by rfl⟩ : syracuseStep 2060675 = 3091013) B3091013
theorem B3477397 : Blo 2059435 3477397 := bbase (se 6 (by rfl) ⟨81501, by rfl⟩ : syracuseStep 3477397 = 163003) (by norm_num)
theorem B4636529 : Blo 2059435 4636529 := bstep (se 2 (by rfl) ⟨1738698, by rfl⟩ : syracuseStep 4636529 = 3477397) B3477397
theorem B3091019 : Blo 2059435 3091019 := bstep (se 1 (by rfl) ⟨2318264, by rfl⟩ : syracuseStep 3091019 = 4636529) B4636529
theorem B2060679 : Blo 2059435 2060679 := bstep (se 1 (by rfl) ⟨1545509, by rfl⟩ : syracuseStep 2060679 = 3091019) B3091019
theorem B2318269 : Blo 2059435 2318269 := bbase (se 3 (by rfl) ⟨434675, by rfl⟩ : syracuseStep 2318269 = 869351) (by norm_num)
theorem B3091025 : Blo 2059435 3091025 := bstep (se 2 (by rfl) ⟨1159134, by rfl⟩ : syracuseStep 3091025 = 2318269) B2318269
theorem B2060683 : Blo 2059435 2060683 := bstep (se 1 (by rfl) ⟨1545512, by rfl⟩ : syracuseStep 2060683 = 3091025) B3091025
theorem B6954821 : Blo 2059435 6954821 := bbase (se 4 (by rfl) ⟨652014, by rfl⟩ : syracuseStep 6954821 = 1304029) (by norm_num)
theorem B4636547 : Blo 2059435 4636547 := bstep (se 1 (by rfl) ⟨3477410, by rfl⟩ : syracuseStep 4636547 = 6954821) B6954821
theorem B3091031 : Blo 2059435 3091031 := bstep (se 1 (by rfl) ⟨2318273, by rfl⟩ : syracuseStep 3091031 = 4636547) B4636547
theorem B2060687 : Blo 2059435 2060687 := bstep (se 1 (by rfl) ⟨1545515, by rfl⟩ : syracuseStep 2060687 = 3091031) B3091031
theorem B3091037 : Blo 2059435 3091037 := bbase (se 3 (by rfl) ⟨579569, by rfl⟩ : syracuseStep 3091037 = 1159139) (by norm_num)
theorem B2060691 : Blo 2059435 2060691 := bstep (se 1 (by rfl) ⟨1545518, by rfl⟩ : syracuseStep 2060691 = 3091037) B3091037
theorem B4636565 : Blo 2059435 4636565 := bbase (se 6 (by rfl) ⟨108669, by rfl⟩ : syracuseStep 4636565 = 217339) (by norm_num)
theorem B3091043 : Blo 2059435 3091043 := bstep (se 1 (by rfl) ⟨2318282, by rfl⟩ : syracuseStep 3091043 = 4636565) B4636565
theorem B2060695 : Blo 2059435 2060695 := bstep (se 1 (by rfl) ⟨1545521, by rfl⟩ : syracuseStep 2060695 = 3091043) B3091043
theorem B4401125 : Blo 2059435 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B2934083 : Blo 2059435 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B7824221 : Blo 2059435 7824221 := bstep (se 3 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 7824221 = 2934083) B2934083
theorem B5216147 : Blo 2059435 5216147 := bstep (se 1 (by rfl) ⟨3912110, by rfl⟩ : syracuseStep 5216147 = 7824221) B7824221
theorem B3477431 : Blo 2059435 3477431 := bstep (se 1 (by rfl) ⟨2608073, by rfl⟩ : syracuseStep 3477431 = 5216147) B5216147
theorem B2318287 : Blo 2059435 2318287 := bstep (se 1 (by rfl) ⟨1738715, by rfl⟩ : syracuseStep 2318287 = 3477431) B3477431
theorem B3091049 : Blo 2059435 3091049 := bstep (se 2 (by rfl) ⟨1159143, by rfl⟩ : syracuseStep 3091049 = 2318287) B2318287
theorem B2060699 : Blo 2059435 2060699 := bstep (se 1 (by rfl) ⟨1545524, by rfl⟩ : syracuseStep 2060699 = 3091049) B3091049
theorem B9902549 : Blo 2059435 9902549 := bbase (se 7 (by rfl) ⟨116045, by rfl⟩ : syracuseStep 9902549 = 232091) (by norm_num)
theorem B6601699 : Blo 2059435 6601699 := bstep (se 1 (by rfl) ⟨4951274, by rfl⟩ : syracuseStep 6601699 = 9902549) B9902549
theorem B8802265 : Blo 2059435 8802265 := bstep (se 2 (by rfl) ⟨3300849, by rfl⟩ : syracuseStep 8802265 = 6601699) B6601699
theorem B11736353 : Blo 2059435 11736353 := bstep (se 2 (by rfl) ⟨4401132, by rfl⟩ : syracuseStep 11736353 = 8802265) B8802265
theorem B7824235 : Blo 2059435 7824235 := bstep (se 1 (by rfl) ⟨5868176, by rfl⟩ : syracuseStep 7824235 = 11736353) B11736353
theorem B10432313 : Blo 2059435 10432313 := bstep (se 2 (by rfl) ⟨3912117, by rfl⟩ : syracuseStep 10432313 = 7824235) B7824235
theorem B6954875 : Blo 2059435 6954875 := bstep (se 1 (by rfl) ⟨5216156, by rfl⟩ : syracuseStep 6954875 = 10432313) B10432313
theorem B4636583 : Blo 2059435 4636583 := bstep (se 1 (by rfl) ⟨3477437, by rfl⟩ : syracuseStep 4636583 = 6954875) B6954875
theorem B3091055 : Blo 2059435 3091055 := bstep (se 1 (by rfl) ⟨2318291, by rfl⟩ : syracuseStep 3091055 = 4636583) B4636583
theorem B2060703 : Blo 2059435 2060703 := bstep (se 1 (by rfl) ⟨1545527, by rfl⟩ : syracuseStep 2060703 = 3091055) B3091055
theorem B3091061 : Blo 2059435 3091061 := bbase (se 5 (by rfl) ⟨144893, by rfl⟩ : syracuseStep 3091061 = 289787) (by norm_num)
theorem B2060707 : Blo 2059435 2060707 := bstep (se 1 (by rfl) ⟨1545530, by rfl⟩ : syracuseStep 2060707 = 3091061) B3091061
theorem B3912133 : Blo 2059435 3912133 := bbase (se 4 (by rfl) ⟨366762, by rfl⟩ : syracuseStep 3912133 = 733525) (by norm_num)
theorem B5216177 : Blo 2059435 5216177 := bstep (se 2 (by rfl) ⟨1956066, by rfl⟩ : syracuseStep 5216177 = 3912133) B3912133
theorem B3477451 : Blo 2059435 3477451 := bstep (se 1 (by rfl) ⟨2608088, by rfl⟩ : syracuseStep 3477451 = 5216177) B5216177
theorem B4636601 : Blo 2059435 4636601 := bstep (se 2 (by rfl) ⟨1738725, by rfl⟩ : syracuseStep 4636601 = 3477451) B3477451
theorem B3091067 : Blo 2059435 3091067 := bstep (se 1 (by rfl) ⟨2318300, by rfl⟩ : syracuseStep 3091067 = 4636601) B4636601
theorem B2060711 : Blo 2059435 2060711 := bstep (se 1 (by rfl) ⟨1545533, by rfl⟩ : syracuseStep 2060711 = 3091067) B3091067
theorem B2318305 : Blo 2059435 2318305 := bbase (se 2 (by rfl) ⟨869364, by rfl⟩ : syracuseStep 2318305 = 1738729) (by norm_num)
theorem B3091073 : Blo 2059435 3091073 := bstep (se 2 (by rfl) ⟨1159152, by rfl⟩ : syracuseStep 3091073 = 2318305) B2318305
theorem B2060715 : Blo 2059435 2060715 := bstep (se 1 (by rfl) ⟨1545536, by rfl⟩ : syracuseStep 2060715 = 3091073) B3091073
theorem B5216197 : Blo 2059435 5216197 := bbase (se 4 (by rfl) ⟨489018, by rfl⟩ : syracuseStep 5216197 = 978037) (by norm_num)
theorem B6954929 : Blo 2059435 6954929 := bstep (se 2 (by rfl) ⟨2608098, by rfl⟩ : syracuseStep 6954929 = 5216197) B5216197
theorem B4636619 : Blo 2059435 4636619 := bstep (se 1 (by rfl) ⟨3477464, by rfl⟩ : syracuseStep 4636619 = 6954929) B6954929
theorem B3091079 : Blo 2059435 3091079 := bstep (se 1 (by rfl) ⟨2318309, by rfl⟩ : syracuseStep 3091079 = 4636619) B4636619
theorem B2060719 : Blo 2059435 2060719 := bstep (se 1 (by rfl) ⟨1545539, by rfl⟩ : syracuseStep 2060719 = 3091079) B3091079
theorem B3091085 : Blo 2059435 3091085 := bbase (se 3 (by rfl) ⟨579578, by rfl⟩ : syracuseStep 3091085 = 1159157) (by norm_num)
theorem B2060723 : Blo 2059435 2060723 := bstep (se 1 (by rfl) ⟨1545542, by rfl⟩ : syracuseStep 2060723 = 3091085) B3091085
theorem B4636637 : Blo 2059435 4636637 := bbase (se 3 (by rfl) ⟨869369, by rfl⟩ : syracuseStep 4636637 = 1738739) (by norm_num)
theorem B3091091 : Blo 2059435 3091091 := bstep (se 1 (by rfl) ⟨2318318, by rfl⟩ : syracuseStep 3091091 = 4636637) B4636637
theorem B2060727 : Blo 2059435 2060727 := bstep (se 1 (by rfl) ⟨1545545, by rfl⟩ : syracuseStep 2060727 = 3091091) B3091091
theorem B3477485 : Blo 2059435 3477485 := bbase (se 3 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 3477485 = 1304057) (by norm_num)
theorem B2318323 : Blo 2059435 2318323 := bstep (se 1 (by rfl) ⟨1738742, by rfl⟩ : syracuseStep 2318323 = 3477485) B3477485
theorem B3091097 : Blo 2059435 3091097 := bstep (se 2 (by rfl) ⟨1159161, by rfl⟩ : syracuseStep 3091097 = 2318323) B2318323
theorem B2060731 : Blo 2059435 2060731 := bstep (se 1 (by rfl) ⟨1545548, by rfl⟩ : syracuseStep 2060731 = 3091097) B3091097
theorem B2230625 : Blo 2059435 2230625 := bbase (se 2 (by rfl) ⟨836484, by rfl⟩ : syracuseStep 2230625 = 1672969) (by norm_num)
theorem B5948333 : Blo 2059435 5948333 := bstep (se 3 (by rfl) ⟨1115312, by rfl⟩ : syracuseStep 5948333 = 2230625) B2230625
theorem B3965555 : Blo 2059435 3965555 := bstep (se 1 (by rfl) ⟨2974166, by rfl⟩ : syracuseStep 3965555 = 5948333) B5948333
theorem B10574813 : Blo 2059435 10574813 := bstep (se 3 (by rfl) ⟨1982777, by rfl⟩ : syracuseStep 10574813 = 3965555) B3965555
theorem B7049875 : Blo 2059435 7049875 := bstep (se 1 (by rfl) ⟨5287406, by rfl⟩ : syracuseStep 7049875 = 10574813) B10574813
theorem B9399833 : Blo 2059435 9399833 := bstep (se 2 (by rfl) ⟨3524937, by rfl⟩ : syracuseStep 9399833 = 7049875) B7049875
theorem B6266555 : Blo 2059435 6266555 := bstep (se 1 (by rfl) ⟨4699916, by rfl⟩ : syracuseStep 6266555 = 9399833) B9399833
theorem B4177703 : Blo 2059435 4177703 := bstep (se 1 (by rfl) ⟨3133277, by rfl⟩ : syracuseStep 4177703 = 6266555) B6266555
theorem B11140541 : Blo 2059435 11140541 := bstep (se 3 (by rfl) ⟨2088851, by rfl⟩ : syracuseStep 11140541 = 4177703) B4177703
theorem B7427027 : Blo 2059435 7427027 := bstep (se 1 (by rfl) ⟨5570270, by rfl⟩ : syracuseStep 7427027 = 11140541) B11140541
theorem B4951351 : Blo 2059435 4951351 := bstep (se 1 (by rfl) ⟨3713513, by rfl⟩ : syracuseStep 4951351 = 7427027) B7427027
theorem B26407205 : Blo 2059435 26407205 := bstep (se 4 (by rfl) ⟨2475675, by rfl⟩ : syracuseStep 26407205 = 4951351) B4951351
theorem B17604803 : Blo 2059435 17604803 := bstep (se 1 (by rfl) ⟨13203602, by rfl⟩ : syracuseStep 17604803 = 26407205) B26407205
theorem B11736535 : Blo 2059435 11736535 := bstep (se 1 (by rfl) ⟨8802401, by rfl⟩ : syracuseStep 11736535 = 17604803) B17604803
theorem B15648713 : Blo 2059435 15648713 := bstep (se 2 (by rfl) ⟨5868267, by rfl⟩ : syracuseStep 15648713 = 11736535) B11736535
theorem B10432475 : Blo 2059435 10432475 := bstep (se 1 (by rfl) ⟨7824356, by rfl⟩ : syracuseStep 10432475 = 15648713) B15648713
theorem B6954983 : Blo 2059435 6954983 := bstep (se 1 (by rfl) ⟨5216237, by rfl⟩ : syracuseStep 6954983 = 10432475) B10432475
theorem B4636655 : Blo 2059435 4636655 := bstep (se 1 (by rfl) ⟨3477491, by rfl⟩ : syracuseStep 4636655 = 6954983) B6954983
theorem B3091103 : Blo 2059435 3091103 := bstep (se 1 (by rfl) ⟨2318327, by rfl⟩ : syracuseStep 3091103 = 4636655) B4636655
theorem B2060735 : Blo 2059435 2060735 := bstep (se 1 (by rfl) ⟨1545551, by rfl⟩ : syracuseStep 2060735 = 3091103) B3091103
theorem B3091109 : Blo 2059435 3091109 := bbase (se 4 (by rfl) ⟨289791, by rfl⟩ : syracuseStep 3091109 = 579583) (by norm_num)
theorem B2060739 : Blo 2059435 2060739 := bstep (se 1 (by rfl) ⟨1545554, by rfl⟩ : syracuseStep 2060739 = 3091109) B3091109
theorem B2608129 : Blo 2059435 2608129 := bbase (se 2 (by rfl) ⟨978048, by rfl⟩ : syracuseStep 2608129 = 1956097) (by norm_num)
theorem B3477505 : Blo 2059435 3477505 := bstep (se 2 (by rfl) ⟨1304064, by rfl⟩ : syracuseStep 3477505 = 2608129) B2608129
theorem B4636673 : Blo 2059435 4636673 := bstep (se 2 (by rfl) ⟨1738752, by rfl⟩ : syracuseStep 4636673 = 3477505) B3477505
theorem B3091115 : Blo 2059435 3091115 := bstep (se 1 (by rfl) ⟨2318336, by rfl⟩ : syracuseStep 3091115 = 4636673) B4636673
theorem B2060743 : Blo 2059435 2060743 := bstep (se 1 (by rfl) ⟨1545557, by rfl⟩ : syracuseStep 2060743 = 3091115) B3091115
theorem B2318341 : Blo 2059435 2318341 := bbase (se 4 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 2318341 = 434689) (by norm_num)
theorem B3091121 : Blo 2059435 3091121 := bstep (se 2 (by rfl) ⟨1159170, by rfl⟩ : syracuseStep 3091121 = 2318341) B2318341
theorem B2060747 : Blo 2059435 2060747 := bstep (se 1 (by rfl) ⟨1545560, by rfl⟩ : syracuseStep 2060747 = 3091121) B3091121
theorem B2934157 : Blo 2059435 2934157 := bbase (se 3 (by rfl) ⟨550154, by rfl⟩ : syracuseStep 2934157 = 1100309) (by norm_num)
theorem B3912209 : Blo 2059435 3912209 := bstep (se 2 (by rfl) ⟨1467078, by rfl⟩ : syracuseStep 3912209 = 2934157) B2934157
theorem B2608139 : Blo 2059435 2608139 := bstep (se 1 (by rfl) ⟨1956104, by rfl⟩ : syracuseStep 2608139 = 3912209) B3912209
theorem B6955037 : Blo 2059435 6955037 := bstep (se 3 (by rfl) ⟨1304069, by rfl⟩ : syracuseStep 6955037 = 2608139) B2608139
theorem B4636691 : Blo 2059435 4636691 := bstep (se 1 (by rfl) ⟨3477518, by rfl⟩ : syracuseStep 4636691 = 6955037) B6955037
theorem B3091127 : Blo 2059435 3091127 := bstep (se 1 (by rfl) ⟨2318345, by rfl⟩ : syracuseStep 3091127 = 4636691) B4636691
theorem B2060751 : Blo 2059435 2060751 := bstep (se 1 (by rfl) ⟨1545563, by rfl⟩ : syracuseStep 2060751 = 3091127) B3091127
theorem B3091133 : Blo 2059435 3091133 := bbase (se 3 (by rfl) ⟨579587, by rfl⟩ : syracuseStep 3091133 = 1159175) (by norm_num)
theorem B2060755 : Blo 2059435 2060755 := bstep (se 1 (by rfl) ⟨1545566, by rfl⟩ : syracuseStep 2060755 = 3091133) B3091133
theorem B4636709 : Blo 2059435 4636709 := bbase (se 4 (by rfl) ⟨434691, by rfl⟩ : syracuseStep 4636709 = 869383) (by norm_num)
theorem B3091139 : Blo 2059435 3091139 := bstep (se 1 (by rfl) ⟨2318354, by rfl⟩ : syracuseStep 3091139 = 4636709) B4636709
theorem B2060759 : Blo 2059435 2060759 := bstep (se 1 (by rfl) ⟨1545569, by rfl⟩ : syracuseStep 2060759 = 3091139) B3091139
theorem B5216309 : Blo 2059435 5216309 := bbase (se 5 (by rfl) ⟨244514, by rfl⟩ : syracuseStep 5216309 = 489029) (by norm_num)
theorem B3477539 : Blo 2059435 3477539 := bstep (se 1 (by rfl) ⟨2608154, by rfl⟩ : syracuseStep 3477539 = 5216309) B5216309
theorem B2318359 : Blo 2059435 2318359 := bstep (se 1 (by rfl) ⟨1738769, by rfl⟩ : syracuseStep 2318359 = 3477539) B3477539
theorem B3091145 : Blo 2059435 3091145 := bstep (se 2 (by rfl) ⟨1159179, by rfl⟩ : syracuseStep 3091145 = 2318359) B2318359
theorem B2060763 : Blo 2059435 2060763 := bstep (se 1 (by rfl) ⟨1545572, by rfl⟩ : syracuseStep 2060763 = 3091145) B3091145
theorem B3176077 : Blo 2059435 3176077 := bbase (se 3 (by rfl) ⟨595514, by rfl⟩ : syracuseStep 3176077 = 1191029) (by norm_num)
theorem B4234769 : Blo 2059435 4234769 := bstep (se 2 (by rfl) ⟨1588038, by rfl⟩ : syracuseStep 4234769 = 3176077) B3176077
theorem B2823179 : Blo 2059435 2823179 := bstep (se 1 (by rfl) ⟨2117384, by rfl⟩ : syracuseStep 2823179 = 4234769) B4234769
theorem B7528477 : Blo 2059435 7528477 := bstep (se 3 (by rfl) ⟨1411589, by rfl⟩ : syracuseStep 7528477 = 2823179) B2823179
theorem B10037969 : Blo 2059435 10037969 := bstep (se 2 (by rfl) ⟨3764238, by rfl⟩ : syracuseStep 10037969 = 7528477) B7528477
theorem B6691979 : Blo 2059435 6691979 := bstep (se 1 (by rfl) ⟨5018984, by rfl⟩ : syracuseStep 6691979 = 10037969) B10037969
theorem B4461319 : Blo 2059435 4461319 := bstep (se 1 (by rfl) ⟨3345989, by rfl⟩ : syracuseStep 4461319 = 6691979) B6691979
theorem B5948425 : Blo 2059435 5948425 := bstep (se 2 (by rfl) ⟨2230659, by rfl⟩ : syracuseStep 5948425 = 4461319) B4461319
theorem B7931233 : Blo 2059435 7931233 := bstep (se 2 (by rfl) ⟨2974212, by rfl⟩ : syracuseStep 7931233 = 5948425) B5948425
theorem B10574977 : Blo 2059435 10574977 := bstep (se 2 (by rfl) ⟨3965616, by rfl⟩ : syracuseStep 10574977 = 7931233) B7931233
theorem B14099969 : Blo 2059435 14099969 := bstep (se 2 (by rfl) ⟨5287488, by rfl⟩ : syracuseStep 14099969 = 10574977) B10574977
theorem B9399979 : Blo 2059435 9399979 := bstep (se 1 (by rfl) ⟨7049984, by rfl⟩ : syracuseStep 9399979 = 14099969) B14099969
theorem B12533305 : Blo 2059435 12533305 := bstep (se 2 (by rfl) ⟨4699989, by rfl⟩ : syracuseStep 12533305 = 9399979) B9399979
theorem B16711073 : Blo 2059435 16711073 := bstep (se 2 (by rfl) ⟨6266652, by rfl⟩ : syracuseStep 16711073 = 12533305) B12533305
theorem B11140715 : Blo 2059435 11140715 := bstep (se 1 (by rfl) ⟨8355536, by rfl⟩ : syracuseStep 11140715 = 16711073) B16711073
theorem B7427143 : Blo 2059435 7427143 := bstep (se 1 (by rfl) ⟨5570357, by rfl⟩ : syracuseStep 7427143 = 11140715) B11140715
theorem B9902857 : Blo 2059435 9902857 := bstep (se 2 (by rfl) ⟨3713571, by rfl⟩ : syracuseStep 9902857 = 7427143) B7427143
theorem B13203809 : Blo 2059435 13203809 := bstep (se 2 (by rfl) ⟨4951428, by rfl⟩ : syracuseStep 13203809 = 9902857) B9902857
theorem B8802539 : Blo 2059435 8802539 := bstep (se 1 (by rfl) ⟨6601904, by rfl⟩ : syracuseStep 8802539 = 13203809) B13203809
theorem B5868359 : Blo 2059435 5868359 := bstep (se 1 (by rfl) ⟨4401269, by rfl⟩ : syracuseStep 5868359 = 8802539) B8802539
theorem B3912239 : Blo 2059435 3912239 := bstep (se 1 (by rfl) ⟨2934179, by rfl⟩ : syracuseStep 3912239 = 5868359) B5868359
theorem B10432637 : Blo 2059435 10432637 := bstep (se 3 (by rfl) ⟨1956119, by rfl⟩ : syracuseStep 10432637 = 3912239) B3912239
theorem B6955091 : Blo 2059435 6955091 := bstep (se 1 (by rfl) ⟨5216318, by rfl⟩ : syracuseStep 6955091 = 10432637) B10432637
theorem B4636727 : Blo 2059435 4636727 := bstep (se 1 (by rfl) ⟨3477545, by rfl⟩ : syracuseStep 4636727 = 6955091) B6955091
theorem B3091151 : Blo 2059435 3091151 := bstep (se 1 (by rfl) ⟨2318363, by rfl⟩ : syracuseStep 3091151 = 4636727) B4636727
theorem B2060767 : Blo 2059435 2060767 := bstep (se 1 (by rfl) ⟨1545575, by rfl⟩ : syracuseStep 2060767 = 3091151) B3091151
theorem B3091157 : Blo 2059435 3091157 := bbase (se 7 (by rfl) ⟨36224, by rfl⟩ : syracuseStep 3091157 = 72449) (by norm_num)
theorem B2060771 : Blo 2059435 2060771 := bstep (se 1 (by rfl) ⟨1545578, by rfl⟩ : syracuseStep 2060771 = 3091157) B3091157
theorem B7427173 : Blo 2059435 7427173 := bbase (se 4 (by rfl) ⟨696297, by rfl⟩ : syracuseStep 7427173 = 1392595) (by norm_num)
theorem B9902897 : Blo 2059435 9902897 := bstep (se 2 (by rfl) ⟨3713586, by rfl⟩ : syracuseStep 9902897 = 7427173) B7427173
theorem B6601931 : Blo 2059435 6601931 := bstep (se 1 (by rfl) ⟨4951448, by rfl⟩ : syracuseStep 6601931 = 9902897) B9902897
theorem B4401287 : Blo 2059435 4401287 := bstep (se 1 (by rfl) ⟨3300965, by rfl⟩ : syracuseStep 4401287 = 6601931) B6601931
theorem B2934191 : Blo 2059435 2934191 := bstep (se 1 (by rfl) ⟨2200643, by rfl⟩ : syracuseStep 2934191 = 4401287) B4401287
theorem B7824509 : Blo 2059435 7824509 := bstep (se 3 (by rfl) ⟨1467095, by rfl⟩ : syracuseStep 7824509 = 2934191) B2934191
theorem B5216339 : Blo 2059435 5216339 := bstep (se 1 (by rfl) ⟨3912254, by rfl⟩ : syracuseStep 5216339 = 7824509) B7824509
theorem B3477559 : Blo 2059435 3477559 := bstep (se 1 (by rfl) ⟨2608169, by rfl⟩ : syracuseStep 3477559 = 5216339) B5216339
theorem B4636745 : Blo 2059435 4636745 := bstep (se 2 (by rfl) ⟨1738779, by rfl⟩ : syracuseStep 4636745 = 3477559) B3477559
theorem B3091163 : Blo 2059435 3091163 := bstep (se 1 (by rfl) ⟨2318372, by rfl⟩ : syracuseStep 3091163 = 4636745) B4636745
theorem B2060775 : Blo 2059435 2060775 := bstep (se 1 (by rfl) ⟨1545581, by rfl⟩ : syracuseStep 2060775 = 3091163) B3091163
theorem B2318377 : Blo 2059435 2318377 := bbase (se 2 (by rfl) ⟨869391, by rfl⟩ : syracuseStep 2318377 = 1738783) (by norm_num)
theorem B3091169 : Blo 2059435 3091169 := bstep (se 2 (by rfl) ⟨1159188, by rfl⟩ : syracuseStep 3091169 = 2318377) B2318377
theorem B2060779 : Blo 2059435 2060779 := bstep (se 1 (by rfl) ⟨1545584, by rfl⟩ : syracuseStep 2060779 = 3091169) B3091169
theorem B3176101 : Blo 2059435 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B16939205 : Blo 2059435 16939205 := bstep (se 4 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 16939205 = 3176101) B3176101
theorem B11292803 : Blo 2059435 11292803 := bstep (se 1 (by rfl) ⟨8469602, by rfl⟩ : syracuseStep 11292803 = 16939205) B16939205
theorem B7528535 : Blo 2059435 7528535 := bstep (se 1 (by rfl) ⟨5646401, by rfl⟩ : syracuseStep 7528535 = 11292803) B11292803
theorem B5019023 : Blo 2059435 5019023 := bstep (se 1 (by rfl) ⟨3764267, by rfl⟩ : syracuseStep 5019023 = 7528535) B7528535
theorem B13384061 : Blo 2059435 13384061 := bstep (se 3 (by rfl) ⟨2509511, by rfl⟩ : syracuseStep 13384061 = 5019023) B5019023
theorem B8922707 : Blo 2059435 8922707 := bstep (se 1 (by rfl) ⟨6692030, by rfl⟩ : syracuseStep 8922707 = 13384061) B13384061
theorem B5948471 : Blo 2059435 5948471 := bstep (se 1 (by rfl) ⟨4461353, by rfl⟩ : syracuseStep 5948471 = 8922707) B8922707
theorem B3965647 : Blo 2059435 3965647 := bstep (se 1 (by rfl) ⟨2974235, by rfl⟩ : syracuseStep 3965647 = 5948471) B5948471
theorem B5287529 : Blo 2059435 5287529 := bstep (se 2 (by rfl) ⟨1982823, by rfl⟩ : syracuseStep 5287529 = 3965647) B3965647
theorem B14100077 : Blo 2059435 14100077 := bstep (se 3 (by rfl) ⟨2643764, by rfl⟩ : syracuseStep 14100077 = 5287529) B5287529
theorem B9400051 : Blo 2059435 9400051 := bstep (se 1 (by rfl) ⟨7050038, by rfl⟩ : syracuseStep 9400051 = 14100077) B14100077
theorem B12533401 : Blo 2059435 12533401 := bstep (se 2 (by rfl) ⟨4700025, by rfl⟩ : syracuseStep 12533401 = 9400051) B9400051
theorem B16711201 : Blo 2059435 16711201 := bstep (se 2 (by rfl) ⟨6266700, by rfl⟩ : syracuseStep 16711201 = 12533401) B12533401
theorem B22281601 : Blo 2059435 22281601 := bstep (se 2 (by rfl) ⟨8355600, by rfl⟩ : syracuseStep 22281601 = 16711201) B16711201
theorem B29708801 : Blo 2059435 29708801 := bstep (se 2 (by rfl) ⟨11140800, by rfl⟩ : syracuseStep 29708801 = 22281601) B22281601
theorem B19805867 : Blo 2059435 19805867 := bstep (se 1 (by rfl) ⟨14854400, by rfl⟩ : syracuseStep 19805867 = 29708801) B29708801
theorem B13203911 : Blo 2059435 13203911 := bstep (se 1 (by rfl) ⟨9902933, by rfl⟩ : syracuseStep 13203911 = 19805867) B19805867
theorem B8802607 : Blo 2059435 8802607 := bstep (se 1 (by rfl) ⟨6601955, by rfl⟩ : syracuseStep 8802607 = 13203911) B13203911
theorem B11736809 : Blo 2059435 11736809 := bstep (se 2 (by rfl) ⟨4401303, by rfl⟩ : syracuseStep 11736809 = 8802607) B8802607
theorem B7824539 : Blo 2059435 7824539 := bstep (se 1 (by rfl) ⟨5868404, by rfl⟩ : syracuseStep 7824539 = 11736809) B11736809
theorem B5216359 : Blo 2059435 5216359 := bstep (se 1 (by rfl) ⟨3912269, by rfl⟩ : syracuseStep 5216359 = 7824539) B7824539
theorem B6955145 : Blo 2059435 6955145 := bstep (se 2 (by rfl) ⟨2608179, by rfl⟩ : syracuseStep 6955145 = 5216359) B5216359
theorem B4636763 : Blo 2059435 4636763 := bstep (se 1 (by rfl) ⟨3477572, by rfl⟩ : syracuseStep 4636763 = 6955145) B6955145
theorem B3091175 : Blo 2059435 3091175 := bstep (se 1 (by rfl) ⟨2318381, by rfl⟩ : syracuseStep 3091175 = 4636763) B4636763
theorem B2060783 : Blo 2059435 2060783 := bstep (se 1 (by rfl) ⟨1545587, by rfl⟩ : syracuseStep 2060783 = 3091175) B3091175
theorem B3091181 : Blo 2059435 3091181 := bbase (se 3 (by rfl) ⟨579596, by rfl⟩ : syracuseStep 3091181 = 1159193) (by norm_num)
theorem B2060787 : Blo 2059435 2060787 := bstep (se 1 (by rfl) ⟨1545590, by rfl⟩ : syracuseStep 2060787 = 3091181) B3091181
theorem B4636781 : Blo 2059435 4636781 := bbase (se 3 (by rfl) ⟨869396, by rfl⟩ : syracuseStep 4636781 = 1738793) (by norm_num)
theorem B3091187 : Blo 2059435 3091187 := bstep (se 1 (by rfl) ⟨2318390, by rfl⟩ : syracuseStep 3091187 = 4636781) B4636781
theorem B2060791 : Blo 2059435 2060791 := bstep (se 1 (by rfl) ⟨1545593, by rfl⟩ : syracuseStep 2060791 = 3091187) B3091187
theorem B3912293 : Blo 2059435 3912293 := bbase (se 4 (by rfl) ⟨366777, by rfl⟩ : syracuseStep 3912293 = 733555) (by norm_num)
theorem B2608195 : Blo 2059435 2608195 := bstep (se 1 (by rfl) ⟨1956146, by rfl⟩ : syracuseStep 2608195 = 3912293) B3912293
theorem B3477593 : Blo 2059435 3477593 := bstep (se 2 (by rfl) ⟨1304097, by rfl⟩ : syracuseStep 3477593 = 2608195) B2608195
theorem B2318395 : Blo 2059435 2318395 := bstep (se 1 (by rfl) ⟨1738796, by rfl⟩ : syracuseStep 2318395 = 3477593) B3477593
theorem B3091193 : Blo 2059435 3091193 := bstep (se 2 (by rfl) ⟨1159197, by rfl⟩ : syracuseStep 3091193 = 2318395) B2318395
theorem B2060795 : Blo 2059435 2060795 := bstep (se 1 (by rfl) ⟨1545596, by rfl⟩ : syracuseStep 2060795 = 3091193) B3091193
theorem B4461389 : Blo 2059435 4461389 := bbase (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) (by norm_num)
theorem B2974259 : Blo 2059435 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B7931357 : Blo 2059435 7931357 := bstep (se 3 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 7931357 = 2974259) B2974259
theorem B5287571 : Blo 2059435 5287571 := bstep (se 1 (by rfl) ⟨3965678, by rfl⟩ : syracuseStep 5287571 = 7931357) B7931357
theorem B3525047 : Blo 2059435 3525047 := bstep (se 1 (by rfl) ⟨2643785, by rfl⟩ : syracuseStep 3525047 = 5287571) B5287571
theorem B2350031 : Blo 2059435 2350031 := bstep (se 1 (by rfl) ⟨1762523, by rfl⟩ : syracuseStep 2350031 = 3525047) B3525047
theorem B6266749 : Blo 2059435 6266749 := bstep (se 3 (by rfl) ⟨1175015, by rfl⟩ : syracuseStep 6266749 = 2350031) B2350031
theorem B8355665 : Blo 2059435 8355665 := bstep (se 2 (by rfl) ⟨3133374, by rfl⟩ : syracuseStep 8355665 = 6266749) B6266749
theorem B5570443 : Blo 2059435 5570443 := bstep (se 1 (by rfl) ⟨4177832, by rfl⟩ : syracuseStep 5570443 = 8355665) B8355665
theorem B7427257 : Blo 2059435 7427257 := bstep (se 2 (by rfl) ⟨2785221, by rfl⟩ : syracuseStep 7427257 = 5570443) B5570443
theorem B39612037 : Blo 2059435 39612037 := bstep (se 4 (by rfl) ⟨3713628, by rfl⟩ : syracuseStep 39612037 = 7427257) B7427257
theorem B52816049 : Blo 2059435 52816049 := bstep (se 2 (by rfl) ⟨19806018, by rfl⟩ : syracuseStep 52816049 = 39612037) B39612037
theorem B35210699 : Blo 2059435 35210699 := bstep (se 1 (by rfl) ⟨26408024, by rfl⟩ : syracuseStep 35210699 = 52816049) B52816049
theorem B23473799 : Blo 2059435 23473799 := bstep (se 1 (by rfl) ⟨17605349, by rfl⟩ : syracuseStep 23473799 = 35210699) B35210699
theorem B15649199 : Blo 2059435 15649199 := bstep (se 1 (by rfl) ⟨11736899, by rfl⟩ : syracuseStep 15649199 = 23473799) B23473799
theorem B10432799 : Blo 2059435 10432799 := bstep (se 1 (by rfl) ⟨7824599, by rfl⟩ : syracuseStep 10432799 = 15649199) B15649199
theorem B6955199 : Blo 2059435 6955199 := bstep (se 1 (by rfl) ⟨5216399, by rfl⟩ : syracuseStep 6955199 = 10432799) B10432799
theorem B4636799 : Blo 2059435 4636799 := bstep (se 1 (by rfl) ⟨3477599, by rfl⟩ : syracuseStep 4636799 = 6955199) B6955199
theorem B3091199 : Blo 2059435 3091199 := bstep (se 1 (by rfl) ⟨2318399, by rfl⟩ : syracuseStep 3091199 = 4636799) B4636799
theorem B2060799 : Blo 2059435 2060799 := bstep (se 1 (by rfl) ⟨1545599, by rfl⟩ : syracuseStep 2060799 = 3091199) B3091199
theorem B3091205 : Blo 2059435 3091205 := bbase (se 4 (by rfl) ⟨289800, by rfl⟩ : syracuseStep 3091205 = 579601) (by norm_num)
theorem B2060803 : Blo 2059435 2060803 := bstep (se 1 (by rfl) ⟨1545602, by rfl⟩ : syracuseStep 2060803 = 3091205) B3091205
theorem B3477613 : Blo 2059435 3477613 := bbase (se 3 (by rfl) ⟨652052, by rfl⟩ : syracuseStep 3477613 = 1304105) (by norm_num)
theorem B4636817 : Blo 2059435 4636817 := bstep (se 2 (by rfl) ⟨1738806, by rfl⟩ : syracuseStep 4636817 = 3477613) B3477613
theorem B3091211 : Blo 2059435 3091211 := bstep (se 1 (by rfl) ⟨2318408, by rfl⟩ : syracuseStep 3091211 = 4636817) B4636817
theorem B2060807 : Blo 2059435 2060807 := bstep (se 1 (by rfl) ⟨1545605, by rfl⟩ : syracuseStep 2060807 = 3091211) B3091211
theorem B2318413 : Blo 2059435 2318413 := bbase (se 3 (by rfl) ⟨434702, by rfl⟩ : syracuseStep 2318413 = 869405) (by norm_num)
theorem B3091217 : Blo 2059435 3091217 := bstep (se 2 (by rfl) ⟨1159206, by rfl⟩ : syracuseStep 3091217 = 2318413) B2318413
theorem B2060811 : Blo 2059435 2060811 := bstep (se 1 (by rfl) ⟨1545608, by rfl⟩ : syracuseStep 2060811 = 3091217) B3091217
theorem B6955253 : Blo 2059435 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B4636835 : Blo 2059435 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B3091223 : Blo 2059435 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B2060815 : Blo 2059435 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B3091229 : Blo 2059435 3091229 := bbase (se 3 (by rfl) ⟨579605, by rfl⟩ : syracuseStep 3091229 = 1159211) (by norm_num)
theorem B2060819 : Blo 2059435 2060819 := bstep (se 1 (by rfl) ⟨1545614, by rfl⟩ : syracuseStep 2060819 = 3091229) B3091229
theorem B4636853 : Blo 2059435 4636853 := bbase (se 5 (by rfl) ⟨217352, by rfl⟩ : syracuseStep 4636853 = 434705) (by norm_num)
theorem B3091235 : Blo 2059435 3091235 := bstep (se 1 (by rfl) ⟨2318426, by rfl⟩ : syracuseStep 3091235 = 4636853) B4636853
theorem B2060823 : Blo 2059435 2060823 := bstep (se 1 (by rfl) ⟨1545617, by rfl⟩ : syracuseStep 2060823 = 3091235) B3091235
theorem B2785261 : Blo 2059435 2785261 := bbase (se 3 (by rfl) ⟨522236, by rfl⟩ : syracuseStep 2785261 = 1044473) (by norm_num)
theorem B3713681 : Blo 2059435 3713681 := bstep (se 2 (by rfl) ⟨1392630, by rfl⟩ : syracuseStep 3713681 = 2785261) B2785261
theorem B2475787 : Blo 2059435 2475787 := bstep (se 1 (by rfl) ⟨1856840, by rfl⟩ : syracuseStep 2475787 = 3713681) B3713681
theorem B3301049 : Blo 2059435 3301049 := bstep (se 2 (by rfl) ⟨1237893, by rfl⟩ : syracuseStep 3301049 = 2475787) B2475787
theorem B2200699 : Blo 2059435 2200699 := bstep (se 1 (by rfl) ⟨1650524, by rfl⟩ : syracuseStep 2200699 = 3301049) B3301049
theorem B11737061 : Blo 2059435 11737061 := bstep (se 4 (by rfl) ⟨1100349, by rfl⟩ : syracuseStep 11737061 = 2200699) B2200699
theorem B7824707 : Blo 2059435 7824707 := bstep (se 1 (by rfl) ⟨5868530, by rfl⟩ : syracuseStep 7824707 = 11737061) B11737061
theorem B5216471 : Blo 2059435 5216471 := bstep (se 1 (by rfl) ⟨3912353, by rfl⟩ : syracuseStep 5216471 = 7824707) B7824707
theorem B3477647 : Blo 2059435 3477647 := bstep (se 1 (by rfl) ⟨2608235, by rfl⟩ : syracuseStep 3477647 = 5216471) B5216471
theorem B2318431 : Blo 2059435 2318431 := bstep (se 1 (by rfl) ⟨1738823, by rfl⟩ : syracuseStep 2318431 = 3477647) B3477647
theorem B3091241 : Blo 2059435 3091241 := bstep (se 2 (by rfl) ⟨1159215, by rfl⟩ : syracuseStep 3091241 = 2318431) B2318431
theorem B2060827 : Blo 2059435 2060827 := bstep (se 1 (by rfl) ⟨1545620, by rfl⟩ : syracuseStep 2060827 = 3091241) B3091241
theorem B2230729 : Blo 2059435 2230729 := bbase (se 2 (by rfl) ⟨836523, by rfl⟩ : syracuseStep 2230729 = 1673047) (by norm_num)
theorem B11897221 : Blo 2059435 11897221 := bstep (se 4 (by rfl) ⟨1115364, by rfl⟩ : syracuseStep 11897221 = 2230729) B2230729
theorem B15862961 : Blo 2059435 15862961 := bstep (se 2 (by rfl) ⟨5948610, by rfl⟩ : syracuseStep 15862961 = 11897221) B11897221
theorem B10575307 : Blo 2059435 10575307 := bstep (se 1 (by rfl) ⟨7931480, by rfl⟩ : syracuseStep 10575307 = 15862961) B15862961
theorem B14100409 : Blo 2059435 14100409 := bstep (se 2 (by rfl) ⟨5287653, by rfl⟩ : syracuseStep 14100409 = 10575307) B10575307
theorem B18800545 : Blo 2059435 18800545 := bstep (se 2 (by rfl) ⟨7050204, by rfl⟩ : syracuseStep 18800545 = 14100409) B14100409
theorem B25067393 : Blo 2059435 25067393 := bstep (se 2 (by rfl) ⟨9400272, by rfl⟩ : syracuseStep 25067393 = 18800545) B18800545
theorem B16711595 : Blo 2059435 16711595 := bstep (se 1 (by rfl) ⟨12533696, by rfl⟩ : syracuseStep 16711595 = 25067393) B25067393
theorem B11141063 : Blo 2059435 11141063 := bstep (se 1 (by rfl) ⟨8355797, by rfl⟩ : syracuseStep 11141063 = 16711595) B16711595
theorem B7427375 : Blo 2059435 7427375 := bstep (se 1 (by rfl) ⟨5570531, by rfl⟩ : syracuseStep 7427375 = 11141063) B11141063
theorem B4951583 : Blo 2059435 4951583 := bstep (se 1 (by rfl) ⟨3713687, by rfl⟩ : syracuseStep 4951583 = 7427375) B7427375
theorem B3301055 : Blo 2059435 3301055 := bstep (se 1 (by rfl) ⟨2475791, by rfl⟩ : syracuseStep 3301055 = 4951583) B4951583
theorem B2200703 : Blo 2059435 2200703 := bstep (se 1 (by rfl) ⟨1650527, by rfl⟩ : syracuseStep 2200703 = 3301055) B3301055
theorem B5868541 : Blo 2059435 5868541 := bstep (se 3 (by rfl) ⟨1100351, by rfl⟩ : syracuseStep 5868541 = 2200703) B2200703
theorem B7824721 : Blo 2059435 7824721 := bstep (se 2 (by rfl) ⟨2934270, by rfl⟩ : syracuseStep 7824721 = 5868541) B5868541
theorem B10432961 : Blo 2059435 10432961 := bstep (se 2 (by rfl) ⟨3912360, by rfl⟩ : syracuseStep 10432961 = 7824721) B7824721
theorem B6955307 : Blo 2059435 6955307 := bstep (se 1 (by rfl) ⟨5216480, by rfl⟩ : syracuseStep 6955307 = 10432961) B10432961
theorem B4636871 : Blo 2059435 4636871 := bstep (se 1 (by rfl) ⟨3477653, by rfl⟩ : syracuseStep 4636871 = 6955307) B6955307
theorem B3091247 : Blo 2059435 3091247 := bstep (se 1 (by rfl) ⟨2318435, by rfl⟩ : syracuseStep 3091247 = 4636871) B4636871
theorem B2060831 : Blo 2059435 2060831 := bstep (se 1 (by rfl) ⟨1545623, by rfl⟩ : syracuseStep 2060831 = 3091247) B3091247
theorem B3091253 : Blo 2059435 3091253 := bbase (se 5 (by rfl) ⟨144902, by rfl⟩ : syracuseStep 3091253 = 289805) (by norm_num)
theorem B2060835 : Blo 2059435 2060835 := bstep (se 1 (by rfl) ⟨1545626, by rfl⟩ : syracuseStep 2060835 = 3091253) B3091253
theorem B5216501 : Blo 2059435 5216501 := bbase (se 5 (by rfl) ⟨244523, by rfl⟩ : syracuseStep 5216501 = 489047) (by norm_num)
theorem B3477667 : Blo 2059435 3477667 := bstep (se 1 (by rfl) ⟨2608250, by rfl⟩ : syracuseStep 3477667 = 5216501) B5216501
theorem B4636889 : Blo 2059435 4636889 := bstep (se 2 (by rfl) ⟨1738833, by rfl⟩ : syracuseStep 4636889 = 3477667) B3477667
theorem B3091259 : Blo 2059435 3091259 := bstep (se 1 (by rfl) ⟨2318444, by rfl⟩ : syracuseStep 3091259 = 4636889) B4636889
theorem B2060839 : Blo 2059435 2060839 := bstep (se 1 (by rfl) ⟨1545629, by rfl⟩ : syracuseStep 2060839 = 3091259) B3091259
theorem B2318449 : Blo 2059435 2318449 := bbase (se 2 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 2318449 = 1738837) (by norm_num)
theorem B3091265 : Blo 2059435 3091265 := bstep (se 2 (by rfl) ⟨1159224, by rfl⟩ : syracuseStep 3091265 = 2318449) B2318449
theorem B2060843 : Blo 2059435 2060843 := bstep (se 1 (by rfl) ⟨1545632, by rfl⟩ : syracuseStep 2060843 = 3091265) B3091265
theorem B4951621 : Blo 2059435 4951621 := bbase (se 4 (by rfl) ⟨464214, by rfl⟩ : syracuseStep 4951621 = 928429) (by norm_num)
theorem B6602161 : Blo 2059435 6602161 := bstep (se 2 (by rfl) ⟨2475810, by rfl⟩ : syracuseStep 6602161 = 4951621) B4951621
theorem B8802881 : Blo 2059435 8802881 := bstep (se 2 (by rfl) ⟨3301080, by rfl⟩ : syracuseStep 8802881 = 6602161) B6602161
theorem B5868587 : Blo 2059435 5868587 := bstep (se 1 (by rfl) ⟨4401440, by rfl⟩ : syracuseStep 5868587 = 8802881) B8802881
theorem B3912391 : Blo 2059435 3912391 := bstep (se 1 (by rfl) ⟨2934293, by rfl⟩ : syracuseStep 3912391 = 5868587) B5868587
theorem B5216521 : Blo 2059435 5216521 := bstep (se 2 (by rfl) ⟨1956195, by rfl⟩ : syracuseStep 5216521 = 3912391) B3912391
theorem B6955361 : Blo 2059435 6955361 := bstep (se 2 (by rfl) ⟨2608260, by rfl⟩ : syracuseStep 6955361 = 5216521) B5216521
theorem B4636907 : Blo 2059435 4636907 := bstep (se 1 (by rfl) ⟨3477680, by rfl⟩ : syracuseStep 4636907 = 6955361) B6955361
theorem B3091271 : Blo 2059435 3091271 := bstep (se 1 (by rfl) ⟨2318453, by rfl⟩ : syracuseStep 3091271 = 4636907) B4636907
theorem B2060847 : Blo 2059435 2060847 := bstep (se 1 (by rfl) ⟨1545635, by rfl⟩ : syracuseStep 2060847 = 3091271) B3091271
theorem B3091277 : Blo 2059435 3091277 := bbase (se 3 (by rfl) ⟨579614, by rfl⟩ : syracuseStep 3091277 = 1159229) (by norm_num)
theorem B2060851 : Blo 2059435 2060851 := bstep (se 1 (by rfl) ⟨1545638, by rfl⟩ : syracuseStep 2060851 = 3091277) B3091277
theorem B4636925 : Blo 2059435 4636925 := bbase (se 3 (by rfl) ⟨869423, by rfl⟩ : syracuseStep 4636925 = 1738847) (by norm_num)
theorem B3091283 : Blo 2059435 3091283 := bstep (se 1 (by rfl) ⟨2318462, by rfl⟩ : syracuseStep 3091283 = 4636925) B4636925
theorem B2060855 : Blo 2059435 2060855 := bstep (se 1 (by rfl) ⟨1545641, by rfl⟩ : syracuseStep 2060855 = 3091283) B3091283
theorem B3477701 : Blo 2059435 3477701 := bbase (se 4 (by rfl) ⟨326034, by rfl⟩ : syracuseStep 3477701 = 652069) (by norm_num)
theorem B2318467 : Blo 2059435 2318467 := bstep (se 1 (by rfl) ⟨1738850, by rfl⟩ : syracuseStep 2318467 = 3477701) B3477701
theorem B3091289 : Blo 2059435 3091289 := bstep (se 2 (by rfl) ⟨1159233, by rfl⟩ : syracuseStep 3091289 = 2318467) B2318467
theorem B2060859 : Blo 2059435 2060859 := bstep (se 1 (by rfl) ⟨1545644, by rfl⟩ : syracuseStep 2060859 = 3091289) B3091289
theorem B15649685 : Blo 2059435 15649685 := bbase (se 6 (by rfl) ⟨366789, by rfl⟩ : syracuseStep 15649685 = 733579) (by norm_num)
theorem B10433123 : Blo 2059435 10433123 := bstep (se 1 (by rfl) ⟨7824842, by rfl⟩ : syracuseStep 10433123 = 15649685) B15649685
theorem B6955415 : Blo 2059435 6955415 := bstep (se 1 (by rfl) ⟨5216561, by rfl⟩ : syracuseStep 6955415 = 10433123) B10433123
theorem B4636943 : Blo 2059435 4636943 := bstep (se 1 (by rfl) ⟨3477707, by rfl⟩ : syracuseStep 4636943 = 6955415) B6955415
theorem B3091295 : Blo 2059435 3091295 := bstep (se 1 (by rfl) ⟨2318471, by rfl⟩ : syracuseStep 3091295 = 4636943) B4636943
theorem B2060863 : Blo 2059435 2060863 := bstep (se 1 (by rfl) ⟨1545647, by rfl⟩ : syracuseStep 2060863 = 3091295) B3091295
theorem B3091301 : Blo 2059435 3091301 := bbase (se 4 (by rfl) ⟨289809, by rfl⟩ : syracuseStep 3091301 = 579619) (by norm_num)
theorem B2060867 : Blo 2059435 2060867 := bstep (se 1 (by rfl) ⟨1545650, by rfl⟩ : syracuseStep 2060867 = 3091301) B3091301
theorem B3912437 : Blo 2059435 3912437 := bbase (se 5 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 3912437 = 366791) (by norm_num)
theorem B2608291 : Blo 2059435 2608291 := bstep (se 1 (by rfl) ⟨1956218, by rfl⟩ : syracuseStep 2608291 = 3912437) B3912437
theorem B3477721 : Blo 2059435 3477721 := bstep (se 2 (by rfl) ⟨1304145, by rfl⟩ : syracuseStep 3477721 = 2608291) B2608291
theorem B4636961 : Blo 2059435 4636961 := bstep (se 2 (by rfl) ⟨1738860, by rfl⟩ : syracuseStep 4636961 = 3477721) B3477721
theorem B3091307 : Blo 2059435 3091307 := bstep (se 1 (by rfl) ⟨2318480, by rfl⟩ : syracuseStep 3091307 = 4636961) B4636961
theorem B2060871 : Blo 2059435 2060871 := bstep (se 1 (by rfl) ⟨1545653, by rfl⟩ : syracuseStep 2060871 = 3091307) B3091307
theorem B2318485 : Blo 2059435 2318485 := bbase (se 6 (by rfl) ⟨54339, by rfl⟩ : syracuseStep 2318485 = 108679) (by norm_num)
theorem B3091313 : Blo 2059435 3091313 := bstep (se 2 (by rfl) ⟨1159242, by rfl⟩ : syracuseStep 3091313 = 2318485) B2318485
theorem B2060875 : Blo 2059435 2060875 := bstep (se 1 (by rfl) ⟨1545656, by rfl⟩ : syracuseStep 2060875 = 3091313) B3091313
theorem B2608301 : Blo 2059435 2608301 := bbase (se 3 (by rfl) ⟨489056, by rfl⟩ : syracuseStep 2608301 = 978113) (by norm_num)
theorem B6955469 : Blo 2059435 6955469 := bstep (se 3 (by rfl) ⟨1304150, by rfl⟩ : syracuseStep 6955469 = 2608301) B2608301
theorem B4636979 : Blo 2059435 4636979 := bstep (se 1 (by rfl) ⟨3477734, by rfl⟩ : syracuseStep 4636979 = 6955469) B6955469
theorem B3091319 : Blo 2059435 3091319 := bstep (se 1 (by rfl) ⟨2318489, by rfl⟩ : syracuseStep 3091319 = 4636979) B4636979
theorem B2060879 : Blo 2059435 2060879 := bstep (se 1 (by rfl) ⟨1545659, by rfl⟩ : syracuseStep 2060879 = 3091319) B3091319
theorem B3091325 : Blo 2059435 3091325 := bbase (se 3 (by rfl) ⟨579623, by rfl⟩ : syracuseStep 3091325 = 1159247) (by norm_num)
theorem B2060883 : Blo 2059435 2060883 := bstep (se 1 (by rfl) ⟨1545662, by rfl⟩ : syracuseStep 2060883 = 3091325) B3091325
theorem B4636997 : Blo 2059435 4636997 := bbase (se 4 (by rfl) ⟨434718, by rfl⟩ : syracuseStep 4636997 = 869437) (by norm_num)
theorem B3091331 : Blo 2059435 3091331 := bstep (se 1 (by rfl) ⟨2318498, by rfl⟩ : syracuseStep 3091331 = 4636997) B4636997
theorem B2060887 : Blo 2059435 2060887 := bstep (se 1 (by rfl) ⟨1545665, by rfl⟩ : syracuseStep 2060887 = 3091331) B3091331
theorem B3525205 : Blo 2059435 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B4700273 : Blo 2059435 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B50136245 : Blo 2059435 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B33424163 : Blo 2059435 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B22282775 : Blo 2059435 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B14855183 : Blo 2059435 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B9903455 : Blo 2059435 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B6602303 : Blo 2059435 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B4401535 : Blo 2059435 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B5868713 : Blo 2059435 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B3912475 : Blo 2059435 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B5216633 : Blo 2059435 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B3477755 : Blo 2059435 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B2318503 : Blo 2059435 2318503 := bstep (se 1 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 2318503 = 3477755) B3477755
theorem B3091337 : Blo 2059435 3091337 := bstep (se 2 (by rfl) ⟨1159251, by rfl⟩ : syracuseStep 3091337 = 2318503) B2318503
theorem B2060891 : Blo 2059435 2060891 := bstep (se 1 (by rfl) ⟨1545668, by rfl⟩ : syracuseStep 2060891 = 3091337) B3091337
theorem B10433285 : Blo 2059435 10433285 := bbase (se 4 (by rfl) ⟨978120, by rfl⟩ : syracuseStep 10433285 = 1956241) (by norm_num)
theorem B6955523 : Blo 2059435 6955523 := bstep (se 1 (by rfl) ⟨5216642, by rfl⟩ : syracuseStep 6955523 = 10433285) B10433285
theorem B4637015 : Blo 2059435 4637015 := bstep (se 1 (by rfl) ⟨3477761, by rfl⟩ : syracuseStep 4637015 = 6955523) B6955523
theorem B3091343 : Blo 2059435 3091343 := bstep (se 1 (by rfl) ⟨2318507, by rfl⟩ : syracuseStep 3091343 = 4637015) B4637015
theorem B2060895 : Blo 2059435 2060895 := bstep (se 1 (by rfl) ⟨1545671, by rfl⟩ : syracuseStep 2060895 = 3091343) B3091343
theorem B3091349 : Blo 2059435 3091349 := bbase (se 6 (by rfl) ⟨72453, by rfl⟩ : syracuseStep 3091349 = 144907) (by norm_num)
theorem B2060899 : Blo 2059435 2060899 := bstep (se 1 (by rfl) ⟨1545674, by rfl⟩ : syracuseStep 2060899 = 3091349) B3091349
theorem B11737493 : Blo 2059435 11737493 := bbase (se 6 (by rfl) ⟨275097, by rfl⟩ : syracuseStep 11737493 = 550195) (by norm_num)
theorem B7824995 : Blo 2059435 7824995 := bstep (se 1 (by rfl) ⟨5868746, by rfl⟩ : syracuseStep 7824995 = 11737493) B11737493
theorem B5216663 : Blo 2059435 5216663 := bstep (se 1 (by rfl) ⟨3912497, by rfl⟩ : syracuseStep 5216663 = 7824995) B7824995
theorem B3477775 : Blo 2059435 3477775 := bstep (se 1 (by rfl) ⟨2608331, by rfl⟩ : syracuseStep 3477775 = 5216663) B5216663
theorem B4637033 : Blo 2059435 4637033 := bstep (se 2 (by rfl) ⟨1738887, by rfl⟩ : syracuseStep 4637033 = 3477775) B3477775
theorem B3091355 : Blo 2059435 3091355 := bstep (se 1 (by rfl) ⟨2318516, by rfl⟩ : syracuseStep 3091355 = 4637033) B4637033
theorem B2060903 : Blo 2059435 2060903 := bstep (se 1 (by rfl) ⟨1545677, by rfl⟩ : syracuseStep 2060903 = 3091355) B3091355
theorem B2318521 : Blo 2059435 2318521 := bbase (se 2 (by rfl) ⟨869445, by rfl⟩ : syracuseStep 2318521 = 1738891) (by norm_num)
theorem B3091361 : Blo 2059435 3091361 := bstep (se 2 (by rfl) ⟨1159260, by rfl⟩ : syracuseStep 3091361 = 2318521) B2318521
theorem B2060907 : Blo 2059435 2060907 := bstep (se 1 (by rfl) ⟨1545680, by rfl⟩ : syracuseStep 2060907 = 3091361) B3091361
theorem B2974421 : Blo 2059435 2974421 := bbase (se 7 (by rfl) ⟨34856, by rfl⟩ : syracuseStep 2974421 = 69713) (by norm_num)
theorem B7931789 : Blo 2059435 7931789 := bstep (se 3 (by rfl) ⟨1487210, by rfl⟩ : syracuseStep 7931789 = 2974421) B2974421
theorem B5287859 : Blo 2059435 5287859 := bstep (se 1 (by rfl) ⟨3965894, by rfl⟩ : syracuseStep 5287859 = 7931789) B7931789
theorem B3525239 : Blo 2059435 3525239 := bstep (se 1 (by rfl) ⟨2643929, by rfl⟩ : syracuseStep 3525239 = 5287859) B5287859
theorem B9400637 : Blo 2059435 9400637 := bstep (se 3 (by rfl) ⟨1762619, by rfl⟩ : syracuseStep 9400637 = 3525239) B3525239
theorem B25068365 : Blo 2059435 25068365 := bstep (se 3 (by rfl) ⟨4700318, by rfl⟩ : syracuseStep 25068365 = 9400637) B9400637
theorem B16712243 : Blo 2059435 16712243 := bstep (se 1 (by rfl) ⟨12534182, by rfl⟩ : syracuseStep 16712243 = 25068365) B25068365
theorem B11141495 : Blo 2059435 11141495 := bstep (se 1 (by rfl) ⟨8356121, by rfl⟩ : syracuseStep 11141495 = 16712243) B16712243
theorem B7427663 : Blo 2059435 7427663 := bstep (se 1 (by rfl) ⟨5570747, by rfl⟩ : syracuseStep 7427663 = 11141495) B11141495
theorem B4951775 : Blo 2059435 4951775 := bstep (se 1 (by rfl) ⟨3713831, by rfl⟩ : syracuseStep 4951775 = 7427663) B7427663
theorem B3301183 : Blo 2059435 3301183 := bstep (se 1 (by rfl) ⟨2475887, by rfl⟩ : syracuseStep 3301183 = 4951775) B4951775
theorem B4401577 : Blo 2059435 4401577 := bstep (se 2 (by rfl) ⟨1650591, by rfl⟩ : syracuseStep 4401577 = 3301183) B3301183
theorem B5868769 : Blo 2059435 5868769 := bstep (se 2 (by rfl) ⟨2200788, by rfl⟩ : syracuseStep 5868769 = 4401577) B4401577
theorem B7825025 : Blo 2059435 7825025 := bstep (se 2 (by rfl) ⟨2934384, by rfl⟩ : syracuseStep 7825025 = 5868769) B5868769
theorem B5216683 : Blo 2059435 5216683 := bstep (se 1 (by rfl) ⟨3912512, by rfl⟩ : syracuseStep 5216683 = 7825025) B7825025
theorem B6955577 : Blo 2059435 6955577 := bstep (se 2 (by rfl) ⟨2608341, by rfl⟩ : syracuseStep 6955577 = 5216683) B5216683
theorem B4637051 : Blo 2059435 4637051 := bstep (se 1 (by rfl) ⟨3477788, by rfl⟩ : syracuseStep 4637051 = 6955577) B6955577
theorem B3091367 : Blo 2059435 3091367 := bstep (se 1 (by rfl) ⟨2318525, by rfl⟩ : syracuseStep 3091367 = 4637051) B4637051
theorem B2060911 : Blo 2059435 2060911 := bstep (se 1 (by rfl) ⟨1545683, by rfl⟩ : syracuseStep 2060911 = 3091367) B3091367
theorem B3091373 : Blo 2059435 3091373 := bbase (se 3 (by rfl) ⟨579632, by rfl⟩ : syracuseStep 3091373 = 1159265) (by norm_num)
theorem B2060915 : Blo 2059435 2060915 := bstep (se 1 (by rfl) ⟨1545686, by rfl⟩ : syracuseStep 2060915 = 3091373) B3091373
theorem B4637069 : Blo 2059435 4637069 := bbase (se 3 (by rfl) ⟨869450, by rfl⟩ : syracuseStep 4637069 = 1738901) (by norm_num)
theorem B3091379 : Blo 2059435 3091379 := bstep (se 1 (by rfl) ⟨2318534, by rfl⟩ : syracuseStep 3091379 = 4637069) B4637069
theorem B2060919 : Blo 2059435 2060919 := bstep (se 1 (by rfl) ⟨1545689, by rfl⟩ : syracuseStep 2060919 = 3091379) B3091379
theorem B2608357 : Blo 2059435 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B3477809 : Blo 2059435 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B2318539 : Blo 2059435 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B3091385 : Blo 2059435 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B2060923 : Blo 2059435 2060923 := bstep (se 1 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 2060923 = 3091385) B3091385
theorem B5570789 : Blo 2059435 5570789 := bbase (se 4 (by rfl) ⟨522261, by rfl⟩ : syracuseStep 5570789 = 1044523) (by norm_num)
theorem B14855437 : Blo 2059435 14855437 := bstep (se 3 (by rfl) ⟨2785394, by rfl⟩ : syracuseStep 14855437 = 5570789) B5570789
theorem B19807249 : Blo 2059435 19807249 := bstep (se 2 (by rfl) ⟨7427718, by rfl⟩ : syracuseStep 19807249 = 14855437) B14855437
theorem B26409665 : Blo 2059435 26409665 := bstep (se 2 (by rfl) ⟨9903624, by rfl⟩ : syracuseStep 26409665 = 19807249) B19807249
theorem B17606443 : Blo 2059435 17606443 := bstep (se 1 (by rfl) ⟨13204832, by rfl⟩ : syracuseStep 17606443 = 26409665) B26409665
theorem B23475257 : Blo 2059435 23475257 := bstep (se 2 (by rfl) ⟨8803221, by rfl⟩ : syracuseStep 23475257 = 17606443) B17606443
theorem B15650171 : Blo 2059435 15650171 := bstep (se 1 (by rfl) ⟨11737628, by rfl⟩ : syracuseStep 15650171 = 23475257) B23475257
theorem B10433447 : Blo 2059435 10433447 := bstep (se 1 (by rfl) ⟨7825085, by rfl⟩ : syracuseStep 10433447 = 15650171) B15650171
theorem B6955631 : Blo 2059435 6955631 := bstep (se 1 (by rfl) ⟨5216723, by rfl⟩ : syracuseStep 6955631 = 10433447) B10433447
theorem B4637087 : Blo 2059435 4637087 := bstep (se 1 (by rfl) ⟨3477815, by rfl⟩ : syracuseStep 4637087 = 6955631) B6955631
theorem B3091391 : Blo 2059435 3091391 := bstep (se 1 (by rfl) ⟨2318543, by rfl⟩ : syracuseStep 3091391 = 4637087) B4637087
theorem B2060927 : Blo 2059435 2060927 := bstep (se 1 (by rfl) ⟨1545695, by rfl⟩ : syracuseStep 2060927 = 3091391) B3091391
theorem B3091397 : Blo 2059435 3091397 := bbase (se 4 (by rfl) ⟨289818, by rfl⟩ : syracuseStep 3091397 = 579637) (by norm_num)
theorem B2060931 : Blo 2059435 2060931 := bstep (se 1 (by rfl) ⟨1545698, by rfl⟩ : syracuseStep 2060931 = 3091397) B3091397
theorem B3477829 : Blo 2059435 3477829 := bbase (se 4 (by rfl) ⟨326046, by rfl⟩ : syracuseStep 3477829 = 652093) (by norm_num)
theorem B4637105 : Blo 2059435 4637105 := bstep (se 2 (by rfl) ⟨1738914, by rfl⟩ : syracuseStep 4637105 = 3477829) B3477829
theorem B3091403 : Blo 2059435 3091403 := bstep (se 1 (by rfl) ⟨2318552, by rfl⟩ : syracuseStep 3091403 = 4637105) B4637105
theorem B2060935 : Blo 2059435 2060935 := bstep (se 1 (by rfl) ⟨1545701, by rfl⟩ : syracuseStep 2060935 = 3091403) B3091403
theorem B2318557 : Blo 2059435 2318557 := bbase (se 3 (by rfl) ⟨434729, by rfl⟩ : syracuseStep 2318557 = 869459) (by norm_num)
theorem B3091409 : Blo 2059435 3091409 := bstep (se 2 (by rfl) ⟨1159278, by rfl⟩ : syracuseStep 3091409 = 2318557) B2318557
theorem B2060939 : Blo 2059435 2060939 := bstep (se 1 (by rfl) ⟨1545704, by rfl⟩ : syracuseStep 2060939 = 3091409) B3091409
theorem B6955685 : Blo 2059435 6955685 := bbase (se 4 (by rfl) ⟨652095, by rfl⟩ : syracuseStep 6955685 = 1304191) (by norm_num)
theorem B4637123 : Blo 2059435 4637123 := bstep (se 1 (by rfl) ⟨3477842, by rfl⟩ : syracuseStep 4637123 = 6955685) B6955685
theorem B3091415 : Blo 2059435 3091415 := bstep (se 1 (by rfl) ⟨2318561, by rfl⟩ : syracuseStep 3091415 = 4637123) B4637123
theorem B2060943 : Blo 2059435 2060943 := bstep (se 1 (by rfl) ⟨1545707, by rfl⟩ : syracuseStep 2060943 = 3091415) B3091415
theorem B3091421 : Blo 2059435 3091421 := bbase (se 3 (by rfl) ⟨579641, by rfl⟩ : syracuseStep 3091421 = 1159283) (by norm_num)
theorem B2060947 : Blo 2059435 2060947 := bstep (se 1 (by rfl) ⟨1545710, by rfl⟩ : syracuseStep 2060947 = 3091421) B3091421
theorem B4637141 : Blo 2059435 4637141 := bbase (se 7 (by rfl) ⟨54341, by rfl⟩ : syracuseStep 4637141 = 108683) (by norm_num)
theorem B3091427 : Blo 2059435 3091427 := bstep (se 1 (by rfl) ⟨2318570, by rfl⟩ : syracuseStep 3091427 = 4637141) B4637141
theorem B2060951 : Blo 2059435 2060951 := bstep (se 1 (by rfl) ⟨1545713, by rfl⟩ : syracuseStep 2060951 = 3091427) B3091427
theorem B3133613 : Blo 2059435 3133613 := bbase (se 3 (by rfl) ⟨587552, by rfl⟩ : syracuseStep 3133613 = 1175105) (by norm_num)
theorem B2089075 : Blo 2059435 2089075 := bstep (se 1 (by rfl) ⟨1566806, by rfl⟩ : syracuseStep 2089075 = 3133613) B3133613
theorem B2785433 : Blo 2059435 2785433 := bstep (se 2 (by rfl) ⟨1044537, by rfl⟩ : syracuseStep 2785433 = 2089075) B2089075
theorem B29711285 : Blo 2059435 29711285 := bstep (se 5 (by rfl) ⟨1392716, by rfl⟩ : syracuseStep 29711285 = 2785433) B2785433
theorem B19807523 : Blo 2059435 19807523 := bstep (se 1 (by rfl) ⟨14855642, by rfl⟩ : syracuseStep 19807523 = 29711285) B29711285
theorem B13205015 : Blo 2059435 13205015 := bstep (se 1 (by rfl) ⟨9903761, by rfl⟩ : syracuseStep 13205015 = 19807523) B19807523
theorem B8803343 : Blo 2059435 8803343 := bstep (se 1 (by rfl) ⟨6602507, by rfl⟩ : syracuseStep 8803343 = 13205015) B13205015
theorem B5868895 : Blo 2059435 5868895 := bstep (se 1 (by rfl) ⟨4401671, by rfl⟩ : syracuseStep 5868895 = 8803343) B8803343
theorem B7825193 : Blo 2059435 7825193 := bstep (se 2 (by rfl) ⟨2934447, by rfl⟩ : syracuseStep 7825193 = 5868895) B5868895
theorem B5216795 : Blo 2059435 5216795 := bstep (se 1 (by rfl) ⟨3912596, by rfl⟩ : syracuseStep 5216795 = 7825193) B7825193
theorem B3477863 : Blo 2059435 3477863 := bstep (se 1 (by rfl) ⟨2608397, by rfl⟩ : syracuseStep 3477863 = 5216795) B5216795
theorem B2318575 : Blo 2059435 2318575 := bstep (se 1 (by rfl) ⟨1738931, by rfl⟩ : syracuseStep 2318575 = 3477863) B3477863
theorem B3091433 : Blo 2059435 3091433 := bstep (se 2 (by rfl) ⟨1159287, by rfl⟩ : syracuseStep 3091433 = 2318575) B2318575
theorem B2060955 : Blo 2059435 2060955 := bstep (se 1 (by rfl) ⟨1545716, by rfl⟩ : syracuseStep 2060955 = 3091433) B3091433
theorem B14855669 : Blo 2059435 14855669 := bbase (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) (by norm_num)
theorem B9903779 : Blo 2059435 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B6602519 : Blo 2059435 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B17606717 : Blo 2059435 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B11737811 : Blo 2059435 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B7825207 : Blo 2059435 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B10433609 : Blo 2059435 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B6955739 : Blo 2059435 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B4637159 : Blo 2059435 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B3091439 : Blo 2059435 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B2060959 : Blo 2059435 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B3091445 : Blo 2059435 3091445 := bbase (se 5 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 3091445 = 289823) (by norm_num)
theorem B2060963 : Blo 2059435 2060963 := bstep (se 1 (by rfl) ⟨1545722, by rfl⟩ : syracuseStep 2060963 = 3091445) B3091445
theorem B3713933 : Blo 2059435 3713933 := bbase (se 3 (by rfl) ⟨696362, by rfl⟩ : syracuseStep 3713933 = 1392725) (by norm_num)
theorem B2475955 : Blo 2059435 2475955 := bstep (se 1 (by rfl) ⟨1856966, by rfl⟩ : syracuseStep 2475955 = 3713933) B3713933
theorem B3301273 : Blo 2059435 3301273 := bstep (se 2 (by rfl) ⟨1237977, by rfl⟩ : syracuseStep 3301273 = 2475955) B2475955
theorem B4401697 : Blo 2059435 4401697 := bstep (se 2 (by rfl) ⟨1650636, by rfl⟩ : syracuseStep 4401697 = 3301273) B3301273
theorem B5868929 : Blo 2059435 5868929 := bstep (se 2 (by rfl) ⟨2200848, by rfl⟩ : syracuseStep 5868929 = 4401697) B4401697
theorem B3912619 : Blo 2059435 3912619 := bstep (se 1 (by rfl) ⟨2934464, by rfl⟩ : syracuseStep 3912619 = 5868929) B5868929
theorem B5216825 : Blo 2059435 5216825 := bstep (se 2 (by rfl) ⟨1956309, by rfl⟩ : syracuseStep 5216825 = 3912619) B3912619
theorem B3477883 : Blo 2059435 3477883 := bstep (se 1 (by rfl) ⟨2608412, by rfl⟩ : syracuseStep 3477883 = 5216825) B5216825
theorem B4637177 : Blo 2059435 4637177 := bstep (se 2 (by rfl) ⟨1738941, by rfl⟩ : syracuseStep 4637177 = 3477883) B3477883
theorem B3091451 : Blo 2059435 3091451 := bstep (se 1 (by rfl) ⟨2318588, by rfl⟩ : syracuseStep 3091451 = 4637177) B4637177
theorem B2060967 : Blo 2059435 2060967 := bstep (se 1 (by rfl) ⟨1545725, by rfl⟩ : syracuseStep 2060967 = 3091451) B3091451
theorem B2318593 : Blo 2059435 2318593 := bbase (se 2 (by rfl) ⟨869472, by rfl⟩ : syracuseStep 2318593 = 1738945) (by norm_num)
theorem B3091457 : Blo 2059435 3091457 := bstep (se 2 (by rfl) ⟨1159296, by rfl⟩ : syracuseStep 3091457 = 2318593) B2318593
theorem B2060971 : Blo 2059435 2060971 := bstep (se 1 (by rfl) ⟨1545728, by rfl⟩ : syracuseStep 2060971 = 3091457) B3091457
theorem B5216845 : Blo 2059435 5216845 := bbase (se 3 (by rfl) ⟨978158, by rfl⟩ : syracuseStep 5216845 = 1956317) (by norm_num)
theorem B6955793 : Blo 2059435 6955793 := bstep (se 2 (by rfl) ⟨2608422, by rfl⟩ : syracuseStep 6955793 = 5216845) B5216845
theorem B4637195 : Blo 2059435 4637195 := bstep (se 1 (by rfl) ⟨3477896, by rfl⟩ : syracuseStep 4637195 = 6955793) B6955793
theorem B3091463 : Blo 2059435 3091463 := bstep (se 1 (by rfl) ⟨2318597, by rfl⟩ : syracuseStep 3091463 = 4637195) B4637195
theorem B2060975 : Blo 2059435 2060975 := bstep (se 1 (by rfl) ⟨1545731, by rfl⟩ : syracuseStep 2060975 = 3091463) B3091463
theorem B3091469 : Blo 2059435 3091469 := bbase (se 3 (by rfl) ⟨579650, by rfl⟩ : syracuseStep 3091469 = 1159301) (by norm_num)
theorem B2060979 : Blo 2059435 2060979 := bstep (se 1 (by rfl) ⟨1545734, by rfl⟩ : syracuseStep 2060979 = 3091469) B3091469
theorem B4637213 : Blo 2059435 4637213 := bbase (se 3 (by rfl) ⟨869477, by rfl⟩ : syracuseStep 4637213 = 1738955) (by norm_num)
theorem B3091475 : Blo 2059435 3091475 := bstep (se 1 (by rfl) ⟨2318606, by rfl⟩ : syracuseStep 3091475 = 4637213) B4637213
theorem B2060983 : Blo 2059435 2060983 := bstep (se 1 (by rfl) ⟨1545737, by rfl⟩ : syracuseStep 2060983 = 3091475) B3091475
theorem B3477917 : Blo 2059435 3477917 := bbase (se 3 (by rfl) ⟨652109, by rfl⟩ : syracuseStep 3477917 = 1304219) (by norm_num)
theorem B2318611 : Blo 2059435 2318611 := bstep (se 1 (by rfl) ⟨1738958, by rfl⟩ : syracuseStep 2318611 = 3477917) B3477917
theorem B3091481 : Blo 2059435 3091481 := bstep (se 2 (by rfl) ⟨1159305, by rfl⟩ : syracuseStep 3091481 = 2318611) B2318611
theorem B2060987 : Blo 2059435 2060987 := bstep (se 1 (by rfl) ⟨1545740, by rfl⟩ : syracuseStep 2060987 = 3091481) B3091481
theorem B10720421 : Blo 2059435 10720421 := bbase (se 4 (by rfl) ⟨1005039, by rfl⟩ : syracuseStep 10720421 = 2010079) (by norm_num)
theorem B7146947 : Blo 2059435 7146947 := bstep (se 1 (by rfl) ⟨5360210, by rfl⟩ : syracuseStep 7146947 = 10720421) B10720421
theorem B4764631 : Blo 2059435 4764631 := bstep (se 1 (by rfl) ⟨3573473, by rfl⟩ : syracuseStep 4764631 = 7146947) B7146947
theorem B6352841 : Blo 2059435 6352841 := bstep (se 2 (by rfl) ⟨2382315, by rfl⟩ : syracuseStep 6352841 = 4764631) B4764631
theorem B16940909 : Blo 2059435 16940909 := bstep (se 3 (by rfl) ⟨3176420, by rfl⟩ : syracuseStep 16940909 = 6352841) B6352841
theorem B11293939 : Blo 2059435 11293939 := bstep (se 1 (by rfl) ⟨8470454, by rfl⟩ : syracuseStep 11293939 = 16940909) B16940909
theorem B15058585 : Blo 2059435 15058585 := bstep (se 2 (by rfl) ⟨5646969, by rfl⟩ : syracuseStep 15058585 = 11293939) B11293939
theorem B20078113 : Blo 2059435 20078113 := bstep (se 2 (by rfl) ⟨7529292, by rfl⟩ : syracuseStep 20078113 = 15058585) B15058585
theorem B26770817 : Blo 2059435 26770817 := bstep (se 2 (by rfl) ⟨10039056, by rfl⟩ : syracuseStep 26770817 = 20078113) B20078113
theorem B17847211 : Blo 2059435 17847211 := bstep (se 1 (by rfl) ⟨13385408, by rfl⟩ : syracuseStep 17847211 = 26770817) B26770817
theorem B23796281 : Blo 2059435 23796281 := bstep (se 2 (by rfl) ⟨8923605, by rfl⟩ : syracuseStep 23796281 = 17847211) B17847211
theorem B15864187 : Blo 2059435 15864187 := bstep (se 1 (by rfl) ⟨11898140, by rfl⟩ : syracuseStep 15864187 = 23796281) B23796281
theorem B21152249 : Blo 2059435 21152249 := bstep (se 2 (by rfl) ⟨7932093, by rfl⟩ : syracuseStep 21152249 = 15864187) B15864187
theorem B14101499 : Blo 2059435 14101499 := bstep (se 1 (by rfl) ⟨10576124, by rfl⟩ : syracuseStep 14101499 = 21152249) B21152249
theorem B37603997 : Blo 2059435 37603997 := bstep (se 3 (by rfl) ⟨7050749, by rfl⟩ : syracuseStep 37603997 = 14101499) B14101499
theorem B25069331 : Blo 2059435 25069331 := bstep (se 1 (by rfl) ⟨18801998, by rfl⟩ : syracuseStep 25069331 = 37603997) B37603997
theorem B16712887 : Blo 2059435 16712887 := bstep (se 1 (by rfl) ⟨12534665, by rfl⟩ : syracuseStep 16712887 = 25069331) B25069331
theorem B22283849 : Blo 2059435 22283849 := bstep (se 2 (by rfl) ⟨8356443, by rfl⟩ : syracuseStep 22283849 = 16712887) B16712887
theorem B14855899 : Blo 2059435 14855899 := bstep (se 1 (by rfl) ⟨11141924, by rfl⟩ : syracuseStep 14855899 = 22283849) B22283849
theorem B19807865 : Blo 2059435 19807865 := bstep (se 2 (by rfl) ⟨7427949, by rfl⟩ : syracuseStep 19807865 = 14855899) B14855899
theorem B13205243 : Blo 2059435 13205243 := bstep (se 1 (by rfl) ⟨9903932, by rfl⟩ : syracuseStep 13205243 = 19807865) B19807865
theorem B8803495 : Blo 2059435 8803495 := bstep (se 1 (by rfl) ⟨6602621, by rfl⟩ : syracuseStep 8803495 = 13205243) B13205243
theorem B11737993 : Blo 2059435 11737993 := bstep (se 2 (by rfl) ⟨4401747, by rfl⟩ : syracuseStep 11737993 = 8803495) B8803495
theorem B15650657 : Blo 2059435 15650657 := bstep (se 2 (by rfl) ⟨5868996, by rfl⟩ : syracuseStep 15650657 = 11737993) B11737993
theorem B10433771 : Blo 2059435 10433771 := bstep (se 1 (by rfl) ⟨7825328, by rfl⟩ : syracuseStep 10433771 = 15650657) B15650657
theorem B6955847 : Blo 2059435 6955847 := bstep (se 1 (by rfl) ⟨5216885, by rfl⟩ : syracuseStep 6955847 = 10433771) B10433771
theorem B4637231 : Blo 2059435 4637231 := bstep (se 1 (by rfl) ⟨3477923, by rfl⟩ : syracuseStep 4637231 = 6955847) B6955847
theorem B3091487 : Blo 2059435 3091487 := bstep (se 1 (by rfl) ⟨2318615, by rfl⟩ : syracuseStep 3091487 = 4637231) B4637231
theorem B2060991 : Blo 2059435 2060991 := bstep (se 1 (by rfl) ⟨1545743, by rfl⟩ : syracuseStep 2060991 = 3091487) B3091487
theorem B3091493 : Blo 2059435 3091493 := bbase (se 4 (by rfl) ⟨289827, by rfl⟩ : syracuseStep 3091493 = 579655) (by norm_num)
theorem B2060995 : Blo 2059435 2060995 := bstep (se 1 (by rfl) ⟨1545746, by rfl⟩ : syracuseStep 2060995 = 3091493) B3091493
theorem B2608453 : Blo 2059435 2608453 := bbase (se 4 (by rfl) ⟨244542, by rfl⟩ : syracuseStep 2608453 = 489085) (by norm_num)
theorem B3477937 : Blo 2059435 3477937 := bstep (se 2 (by rfl) ⟨1304226, by rfl⟩ : syracuseStep 3477937 = 2608453) B2608453
theorem B4637249 : Blo 2059435 4637249 := bstep (se 2 (by rfl) ⟨1738968, by rfl⟩ : syracuseStep 4637249 = 3477937) B3477937
theorem B3091499 : Blo 2059435 3091499 := bstep (se 1 (by rfl) ⟨2318624, by rfl⟩ : syracuseStep 3091499 = 4637249) B4637249
theorem B2060999 : Blo 2059435 2060999 := bstep (se 1 (by rfl) ⟨1545749, by rfl⟩ : syracuseStep 2060999 = 3091499) B3091499
theorem B2318629 : Blo 2059435 2318629 := bbase (se 4 (by rfl) ⟨217371, by rfl⟩ : syracuseStep 2318629 = 434743) (by norm_num)
theorem B3091505 : Blo 2059435 3091505 := bstep (se 2 (by rfl) ⟨1159314, by rfl⟩ : syracuseStep 3091505 = 2318629) B2318629
theorem B2061003 : Blo 2059435 2061003 := bstep (se 1 (by rfl) ⟨1545752, by rfl⟩ : syracuseStep 2061003 = 3091505) B3091505
theorem B3714005 : Blo 2059435 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B2476003 : Blo 2059435 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B3301337 : Blo 2059435 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B8803565 : Blo 2059435 8803565 := bstep (se 3 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 8803565 = 3301337) B3301337
theorem B5869043 : Blo 2059435 5869043 := bstep (se 1 (by rfl) ⟨4401782, by rfl⟩ : syracuseStep 5869043 = 8803565) B8803565
theorem B3912695 : Blo 2059435 3912695 := bstep (se 1 (by rfl) ⟨2934521, by rfl⟩ : syracuseStep 3912695 = 5869043) B5869043
theorem B2608463 : Blo 2059435 2608463 := bstep (se 1 (by rfl) ⟨1956347, by rfl⟩ : syracuseStep 2608463 = 3912695) B3912695
theorem B6955901 : Blo 2059435 6955901 := bstep (se 3 (by rfl) ⟨1304231, by rfl⟩ : syracuseStep 6955901 = 2608463) B2608463
theorem B4637267 : Blo 2059435 4637267 := bstep (se 1 (by rfl) ⟨3477950, by rfl⟩ : syracuseStep 4637267 = 6955901) B6955901
theorem B3091511 : Blo 2059435 3091511 := bstep (se 1 (by rfl) ⟨2318633, by rfl⟩ : syracuseStep 3091511 = 4637267) B4637267
theorem B2061007 : Blo 2059435 2061007 := bstep (se 1 (by rfl) ⟨1545755, by rfl⟩ : syracuseStep 2061007 = 3091511) B3091511
theorem B3091517 : Blo 2059435 3091517 := bbase (se 3 (by rfl) ⟨579659, by rfl⟩ : syracuseStep 3091517 = 1159319) (by norm_num)
theorem B2061011 : Blo 2059435 2061011 := bstep (se 1 (by rfl) ⟨1545758, by rfl⟩ : syracuseStep 2061011 = 3091517) B3091517
theorem B4637285 : Blo 2059435 4637285 := bbase (se 4 (by rfl) ⟨434745, by rfl⟩ : syracuseStep 4637285 = 869491) (by norm_num)
theorem B3091523 : Blo 2059435 3091523 := bstep (se 1 (by rfl) ⟨2318642, by rfl⟩ : syracuseStep 3091523 = 4637285) B4637285
theorem B2061015 : Blo 2059435 2061015 := bstep (se 1 (by rfl) ⟨1545761, by rfl⟩ : syracuseStep 2061015 = 3091523) B3091523
theorem B5216957 : Blo 2059435 5216957 := bbase (se 3 (by rfl) ⟨978179, by rfl⟩ : syracuseStep 5216957 = 1956359) (by norm_num)
theorem B3477971 : Blo 2059435 3477971 := bstep (se 1 (by rfl) ⟨2608478, by rfl⟩ : syracuseStep 3477971 = 5216957) B5216957
theorem B2318647 : Blo 2059435 2318647 := bstep (se 1 (by rfl) ⟨1738985, by rfl⟩ : syracuseStep 2318647 = 3477971) B3477971
theorem B3091529 : Blo 2059435 3091529 := bstep (se 2 (by rfl) ⟨1159323, by rfl⟩ : syracuseStep 3091529 = 2318647) B2318647
theorem B2061019 : Blo 2059435 2061019 := bstep (se 1 (by rfl) ⟨1545764, by rfl⟩ : syracuseStep 2061019 = 3091529) B3091529
theorem B3912725 : Blo 2059435 3912725 := bbase (se 6 (by rfl) ⟨91704, by rfl⟩ : syracuseStep 3912725 = 183409) (by norm_num)
theorem B10433933 : Blo 2059435 10433933 := bstep (se 3 (by rfl) ⟨1956362, by rfl⟩ : syracuseStep 10433933 = 3912725) B3912725
theorem B6955955 : Blo 2059435 6955955 := bstep (se 1 (by rfl) ⟨5216966, by rfl⟩ : syracuseStep 6955955 = 10433933) B10433933
theorem B4637303 : Blo 2059435 4637303 := bstep (se 1 (by rfl) ⟨3477977, by rfl⟩ : syracuseStep 4637303 = 6955955) B6955955
theorem B3091535 : Blo 2059435 3091535 := bstep (se 1 (by rfl) ⟨2318651, by rfl⟩ : syracuseStep 3091535 = 4637303) B4637303
theorem B2061023 : Blo 2059435 2061023 := bstep (se 1 (by rfl) ⟨1545767, by rfl⟩ : syracuseStep 2061023 = 3091535) B3091535
theorem B3091541 : Blo 2059435 3091541 := bbase (se 8 (by rfl) ⟨18114, by rfl⟩ : syracuseStep 3091541 = 36229) (by norm_num)
theorem B2061027 : Blo 2059435 2061027 := bstep (se 1 (by rfl) ⟨1545770, by rfl⟩ : syracuseStep 2061027 = 3091541) B3091541
theorem B18091061 : Blo 2059435 18091061 := bbase (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) (by norm_num)
theorem B12060707 : Blo 2059435 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B128647541 : Blo 2059435 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B85765027 : Blo 2059435 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B114353369 : Blo 2059435 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B76235579 : Blo 2059435 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B50823719 : Blo 2059435 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B33882479 : Blo 2059435 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B22588319 : Blo 2059435 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B15058879 : Blo 2059435 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B80314021 : Blo 2059435 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B428341445 : Blo 2059435 428341445 := bstep (se 4 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 428341445 = 80314021) B80314021
theorem B285560963 : Blo 2059435 285560963 := bstep (se 1 (by rfl) ⟨214170722, by rfl⟩ : syracuseStep 285560963 = 428341445) B428341445
theorem B190373975 : Blo 2059435 190373975 := bstep (se 1 (by rfl) ⟨142780481, by rfl⟩ : syracuseStep 190373975 = 285560963) B285560963
theorem B126915983 : Blo 2059435 126915983 := bstep (se 1 (by rfl) ⟨95186987, by rfl⟩ : syracuseStep 126915983 = 190373975) B190373975
theorem B84610655 : Blo 2059435 84610655 := bstep (se 1 (by rfl) ⟨63457991, by rfl⟩ : syracuseStep 84610655 = 126915983) B126915983
theorem B56407103 : Blo 2059435 56407103 := bstep (se 1 (by rfl) ⟨42305327, by rfl⟩ : syracuseStep 56407103 = 84610655) B84610655
theorem B37604735 : Blo 2059435 37604735 := bstep (se 1 (by rfl) ⟨28203551, by rfl⟩ : syracuseStep 37604735 = 56407103) B56407103
theorem B25069823 : Blo 2059435 25069823 := bstep (se 1 (by rfl) ⟨18802367, by rfl⟩ : syracuseStep 25069823 = 37604735) B37604735
theorem B16713215 : Blo 2059435 16713215 := bstep (se 1 (by rfl) ⟨12534911, by rfl⟩ : syracuseStep 16713215 = 25069823) B25069823
theorem B11142143 : Blo 2059435 11142143 := bstep (se 1 (by rfl) ⟨8356607, by rfl⟩ : syracuseStep 11142143 = 16713215) B16713215
theorem B7428095 : Blo 2059435 7428095 := bstep (se 1 (by rfl) ⟨5571071, by rfl⟩ : syracuseStep 7428095 = 11142143) B11142143
theorem B4952063 : Blo 2059435 4952063 := bstep (se 1 (by rfl) ⟨3714047, by rfl⟩ : syracuseStep 4952063 = 7428095) B7428095
theorem B13205501 : Blo 2059435 13205501 := bstep (se 3 (by rfl) ⟨2476031, by rfl⟩ : syracuseStep 13205501 = 4952063) B4952063
theorem B8803667 : Blo 2059435 8803667 := bstep (se 1 (by rfl) ⟨6602750, by rfl⟩ : syracuseStep 8803667 = 13205501) B13205501
theorem B5869111 : Blo 2059435 5869111 := bstep (se 1 (by rfl) ⟨4401833, by rfl⟩ : syracuseStep 5869111 = 8803667) B8803667
theorem B7825481 : Blo 2059435 7825481 := bstep (se 2 (by rfl) ⟨2934555, by rfl⟩ : syracuseStep 7825481 = 5869111) B5869111
theorem B5216987 : Blo 2059435 5216987 := bstep (se 1 (by rfl) ⟨3912740, by rfl⟩ : syracuseStep 5216987 = 7825481) B7825481
theorem B3477991 : Blo 2059435 3477991 := bstep (se 1 (by rfl) ⟨2608493, by rfl⟩ : syracuseStep 3477991 = 5216987) B5216987
theorem B4637321 : Blo 2059435 4637321 := bstep (se 2 (by rfl) ⟨1738995, by rfl⟩ : syracuseStep 4637321 = 3477991) B3477991
theorem B3091547 : Blo 2059435 3091547 := bstep (se 1 (by rfl) ⟨2318660, by rfl⟩ : syracuseStep 3091547 = 4637321) B4637321
theorem B2061031 : Blo 2059435 2061031 := bstep (se 1 (by rfl) ⟨1545773, by rfl⟩ : syracuseStep 2061031 = 3091547) B3091547
theorem B2318665 : Blo 2059435 2318665 := bbase (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) (by norm_num)
theorem B3091553 : Blo 2059435 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B2061035 : Blo 2059435 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B8923813 : Blo 2059435 8923813 := bbase (se 4 (by rfl) ⟨836607, by rfl⟩ : syracuseStep 8923813 = 1673215) (by norm_num)
theorem B47593669 : Blo 2059435 47593669 := bstep (se 4 (by rfl) ⟨4461906, by rfl⟩ : syracuseStep 47593669 = 8923813) B8923813
theorem B63458225 : Blo 2059435 63458225 := bstep (se 2 (by rfl) ⟨23796834, by rfl⟩ : syracuseStep 63458225 = 47593669) B47593669
theorem B42305483 : Blo 2059435 42305483 := bstep (se 1 (by rfl) ⟨31729112, by rfl⟩ : syracuseStep 42305483 = 63458225) B63458225
theorem B28203655 : Blo 2059435 28203655 := bstep (se 1 (by rfl) ⟨21152741, by rfl⟩ : syracuseStep 28203655 = 42305483) B42305483
theorem B37604873 : Blo 2059435 37604873 := bstep (se 2 (by rfl) ⟨14101827, by rfl⟩ : syracuseStep 37604873 = 28203655) B28203655
theorem B25069915 : Blo 2059435 25069915 := bstep (se 1 (by rfl) ⟨18802436, by rfl⟩ : syracuseStep 25069915 = 37604873) B37604873
theorem B33426553 : Blo 2059435 33426553 := bstep (se 2 (by rfl) ⟨12534957, by rfl⟩ : syracuseStep 33426553 = 25069915) B25069915
theorem B44568737 : Blo 2059435 44568737 := bstep (se 2 (by rfl) ⟨16713276, by rfl⟩ : syracuseStep 44568737 = 33426553) B33426553
theorem B29712491 : Blo 2059435 29712491 := bstep (se 1 (by rfl) ⟨22284368, by rfl⟩ : syracuseStep 29712491 = 44568737) B44568737
theorem B19808327 : Blo 2059435 19808327 := bstep (se 1 (by rfl) ⟨14856245, by rfl⟩ : syracuseStep 19808327 = 29712491) B29712491
theorem B13205551 : Blo 2059435 13205551 := bstep (se 1 (by rfl) ⟨9904163, by rfl⟩ : syracuseStep 13205551 = 19808327) B19808327
theorem B17607401 : Blo 2059435 17607401 := bstep (se 2 (by rfl) ⟨6602775, by rfl⟩ : syracuseStep 17607401 = 13205551) B13205551
theorem B11738267 : Blo 2059435 11738267 := bstep (se 1 (by rfl) ⟨8803700, by rfl⟩ : syracuseStep 11738267 = 17607401) B17607401
theorem B7825511 : Blo 2059435 7825511 := bstep (se 1 (by rfl) ⟨5869133, by rfl⟩ : syracuseStep 7825511 = 11738267) B11738267
theorem B5217007 : Blo 2059435 5217007 := bstep (se 1 (by rfl) ⟨3912755, by rfl⟩ : syracuseStep 5217007 = 7825511) B7825511
theorem B6956009 : Blo 2059435 6956009 := bstep (se 2 (by rfl) ⟨2608503, by rfl⟩ : syracuseStep 6956009 = 5217007) B5217007
theorem B4637339 : Blo 2059435 4637339 := bstep (se 1 (by rfl) ⟨3478004, by rfl⟩ : syracuseStep 4637339 = 6956009) B6956009
theorem B3091559 : Blo 2059435 3091559 := bstep (se 1 (by rfl) ⟨2318669, by rfl⟩ : syracuseStep 3091559 = 4637339) B4637339
theorem B2061039 : Blo 2059435 2061039 := bstep (se 1 (by rfl) ⟨1545779, by rfl⟩ : syracuseStep 2061039 = 3091559) B3091559
theorem B3091565 : Blo 2059435 3091565 := bbase (se 3 (by rfl) ⟨579668, by rfl⟩ : syracuseStep 3091565 = 1159337) (by norm_num)
theorem B2061043 : Blo 2059435 2061043 := bstep (se 1 (by rfl) ⟨1545782, by rfl⟩ : syracuseStep 2061043 = 3091565) B3091565
theorem B4637357 : Blo 2059435 4637357 := bbase (se 3 (by rfl) ⟨869504, by rfl⟩ : syracuseStep 4637357 = 1739009) (by norm_num)
theorem B3091571 : Blo 2059435 3091571 := bstep (se 1 (by rfl) ⟨2318678, by rfl⟩ : syracuseStep 3091571 = 4637357) B4637357
theorem B2061047 : Blo 2059435 2061047 := bstep (se 1 (by rfl) ⟨1545785, by rfl⟩ : syracuseStep 2061047 = 3091571) B3091571
theorem B4401877 : Blo 2059435 4401877 := bbase (se 7 (by rfl) ⟨51584, by rfl⟩ : syracuseStep 4401877 = 103169) (by norm_num)
theorem B5869169 : Blo 2059435 5869169 := bstep (se 2 (by rfl) ⟨2200938, by rfl⟩ : syracuseStep 5869169 = 4401877) B4401877
theorem B3912779 : Blo 2059435 3912779 := bstep (se 1 (by rfl) ⟨2934584, by rfl⟩ : syracuseStep 3912779 = 5869169) B5869169
theorem B2608519 : Blo 2059435 2608519 := bstep (se 1 (by rfl) ⟨1956389, by rfl⟩ : syracuseStep 2608519 = 3912779) B3912779
theorem B3478025 : Blo 2059435 3478025 := bstep (se 2 (by rfl) ⟨1304259, by rfl⟩ : syracuseStep 3478025 = 2608519) B2608519
theorem B2318683 : Blo 2059435 2318683 := bstep (se 1 (by rfl) ⟨1739012, by rfl⟩ : syracuseStep 2318683 = 3478025) B3478025
theorem B3091577 : Blo 2059435 3091577 := bstep (se 2 (by rfl) ⟨1159341, by rfl⟩ : syracuseStep 3091577 = 2318683) B2318683
theorem B2061051 : Blo 2059435 2061051 := bstep (se 1 (by rfl) ⟨1545788, by rfl⟩ : syracuseStep 2061051 = 3091577) B3091577
theorem B9659573 : Blo 2059435 9659573 := bbase (se 5 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 9659573 = 905585) (by norm_num)
theorem B6439715 : Blo 2059435 6439715 := bstep (se 1 (by rfl) ⟨4829786, by rfl⟩ : syracuseStep 6439715 = 9659573) B9659573
theorem B4293143 : Blo 2059435 4293143 := bstep (se 1 (by rfl) ⟨3219857, by rfl⟩ : syracuseStep 4293143 = 6439715) B6439715
theorem B45793525 : Blo 2059435 45793525 := bstep (se 5 (by rfl) ⟨2146571, by rfl⟩ : syracuseStep 45793525 = 4293143) B4293143
theorem B61058033 : Blo 2059435 61058033 := bstep (se 2 (by rfl) ⟨22896762, by rfl⟩ : syracuseStep 61058033 = 45793525) B45793525
theorem B40705355 : Blo 2059435 40705355 := bstep (se 1 (by rfl) ⟨30529016, by rfl⟩ : syracuseStep 40705355 = 61058033) B61058033
theorem B108547613 : Blo 2059435 108547613 := bstep (se 3 (by rfl) ⟨20352677, by rfl⟩ : syracuseStep 108547613 = 40705355) B40705355
theorem B72365075 : Blo 2059435 72365075 := bstep (se 1 (by rfl) ⟨54273806, by rfl⟩ : syracuseStep 72365075 = 108547613) B108547613
theorem B48243383 : Blo 2059435 48243383 := bstep (se 1 (by rfl) ⟨36182537, by rfl⟩ : syracuseStep 48243383 = 72365075) B72365075
theorem B32162255 : Blo 2059435 32162255 := bstep (se 1 (by rfl) ⟨24121691, by rfl⟩ : syracuseStep 32162255 = 48243383) B48243383
theorem B21441503 : Blo 2059435 21441503 := bstep (se 1 (by rfl) ⟨16081127, by rfl⟩ : syracuseStep 21441503 = 32162255) B32162255
theorem B14294335 : Blo 2059435 14294335 := bstep (se 1 (by rfl) ⟨10720751, by rfl⟩ : syracuseStep 14294335 = 21441503) B21441503
theorem B19059113 : Blo 2059435 19059113 := bstep (se 2 (by rfl) ⟨7147167, by rfl⟩ : syracuseStep 19059113 = 14294335) B14294335
theorem B12706075 : Blo 2059435 12706075 := bstep (se 1 (by rfl) ⟨9529556, by rfl⟩ : syracuseStep 12706075 = 19059113) B19059113
theorem B16941433 : Blo 2059435 16941433 := bstep (se 2 (by rfl) ⟨6353037, by rfl⟩ : syracuseStep 16941433 = 12706075) B12706075
theorem B22588577 : Blo 2059435 22588577 := bstep (se 2 (by rfl) ⟨8470716, by rfl⟩ : syracuseStep 22588577 = 16941433) B16941433
theorem B15059051 : Blo 2059435 15059051 := bstep (se 1 (by rfl) ⟨11294288, by rfl⟩ : syracuseStep 15059051 = 22588577) B22588577
theorem B10039367 : Blo 2059435 10039367 := bstep (se 1 (by rfl) ⟨7529525, by rfl⟩ : syracuseStep 10039367 = 15059051) B15059051
theorem B6692911 : Blo 2059435 6692911 := bstep (se 1 (by rfl) ⟨5019683, by rfl⟩ : syracuseStep 6692911 = 10039367) B10039367
theorem B142782101 : Blo 2059435 142782101 := bstep (se 6 (by rfl) ⟨3346455, by rfl⟩ : syracuseStep 142782101 = 6692911) B6692911
theorem B95188067 : Blo 2059435 95188067 := bstep (se 1 (by rfl) ⟨71391050, by rfl⟩ : syracuseStep 95188067 = 142782101) B142782101
theorem B63458711 : Blo 2059435 63458711 := bstep (se 1 (by rfl) ⟨47594033, by rfl⟩ : syracuseStep 63458711 = 95188067) B95188067
theorem B42305807 : Blo 2059435 42305807 := bstep (se 1 (by rfl) ⟨31729355, by rfl⟩ : syracuseStep 42305807 = 63458711) B63458711
theorem B28203871 : Blo 2059435 28203871 := bstep (se 1 (by rfl) ⟨21152903, by rfl⟩ : syracuseStep 28203871 = 42305807) B42305807
theorem B37605161 : Blo 2059435 37605161 := bstep (se 2 (by rfl) ⟨14101935, by rfl⟩ : syracuseStep 37605161 = 28203871) B28203871
theorem B100280429 : Blo 2059435 100280429 := bstep (se 3 (by rfl) ⟨18802580, by rfl⟩ : syracuseStep 100280429 = 37605161) B37605161
theorem B66853619 : Blo 2059435 66853619 := bstep (se 1 (by rfl) ⟨50140214, by rfl⟩ : syracuseStep 66853619 = 100280429) B100280429
theorem B44569079 : Blo 2059435 44569079 := bstep (se 1 (by rfl) ⟨33426809, by rfl⟩ : syracuseStep 44569079 = 66853619) B66853619
theorem B29712719 : Blo 2059435 29712719 := bstep (se 1 (by rfl) ⟨22284539, by rfl⟩ : syracuseStep 29712719 = 44569079) B44569079
theorem B19808479 : Blo 2059435 19808479 := bstep (se 1 (by rfl) ⟨14856359, by rfl⟩ : syracuseStep 19808479 = 29712719) B29712719
theorem B26411305 : Blo 2059435 26411305 := bstep (se 2 (by rfl) ⟨9904239, by rfl⟩ : syracuseStep 26411305 = 19808479) B19808479
theorem B35215073 : Blo 2059435 35215073 := bstep (se 2 (by rfl) ⟨13205652, by rfl⟩ : syracuseStep 35215073 = 26411305) B26411305
theorem B23476715 : Blo 2059435 23476715 := bstep (se 1 (by rfl) ⟨17607536, by rfl⟩ : syracuseStep 23476715 = 35215073) B35215073
theorem B15651143 : Blo 2059435 15651143 := bstep (se 1 (by rfl) ⟨11738357, by rfl⟩ : syracuseStep 15651143 = 23476715) B23476715
theorem B10434095 : Blo 2059435 10434095 := bstep (se 1 (by rfl) ⟨7825571, by rfl⟩ : syracuseStep 10434095 = 15651143) B15651143
theorem B6956063 : Blo 2059435 6956063 := bstep (se 1 (by rfl) ⟨5217047, by rfl⟩ : syracuseStep 6956063 = 10434095) B10434095
theorem B4637375 : Blo 2059435 4637375 := bstep (se 1 (by rfl) ⟨3478031, by rfl⟩ : syracuseStep 4637375 = 6956063) B6956063
theorem B3091583 : Blo 2059435 3091583 := bstep (se 1 (by rfl) ⟨2318687, by rfl⟩ : syracuseStep 3091583 = 4637375) B4637375
theorem B2061055 : Blo 2059435 2061055 := bstep (se 1 (by rfl) ⟨1545791, by rfl⟩ : syracuseStep 2061055 = 3091583) B3091583
theorem B3091589 : Blo 2059435 3091589 := bbase (se 4 (by rfl) ⟨289836, by rfl⟩ : syracuseStep 3091589 = 579673) (by norm_num)
theorem B2061059 : Blo 2059435 2061059 := bstep (se 1 (by rfl) ⟨1545794, by rfl⟩ : syracuseStep 2061059 = 3091589) B3091589
theorem B3478045 : Blo 2059435 3478045 := bbase (se 3 (by rfl) ⟨652133, by rfl⟩ : syracuseStep 3478045 = 1304267) (by norm_num)
theorem B4637393 : Blo 2059435 4637393 := bstep (se 2 (by rfl) ⟨1739022, by rfl⟩ : syracuseStep 4637393 = 3478045) B3478045
theorem B3091595 : Blo 2059435 3091595 := bstep (se 1 (by rfl) ⟨2318696, by rfl⟩ : syracuseStep 3091595 = 4637393) B4637393
theorem B2061063 : Blo 2059435 2061063 := bstep (se 1 (by rfl) ⟨1545797, by rfl⟩ : syracuseStep 2061063 = 3091595) B3091595
theorem B2318701 : Blo 2059435 2318701 := bbase (se 3 (by rfl) ⟨434756, by rfl⟩ : syracuseStep 2318701 = 869513) (by norm_num)
theorem B3091601 : Blo 2059435 3091601 := bstep (se 2 (by rfl) ⟨1159350, by rfl⟩ : syracuseStep 3091601 = 2318701) B2318701
theorem B2061067 : Blo 2059435 2061067 := bstep (se 1 (by rfl) ⟨1545800, by rfl⟩ : syracuseStep 2061067 = 3091601) B3091601
theorem B6956117 : Blo 2059435 6956117 := bbase (se 8 (by rfl) ⟨40758, by rfl⟩ : syracuseStep 6956117 = 81517) (by norm_num)
theorem B4637411 : Blo 2059435 4637411 := bstep (se 1 (by rfl) ⟨3478058, by rfl⟩ : syracuseStep 4637411 = 6956117) B6956117
theorem B3091607 : Blo 2059435 3091607 := bstep (se 1 (by rfl) ⟨2318705, by rfl⟩ : syracuseStep 3091607 = 4637411) B4637411
theorem B2061071 : Blo 2059435 2061071 := bstep (se 1 (by rfl) ⟨1545803, by rfl⟩ : syracuseStep 2061071 = 3091607) B3091607
theorem B3091613 : Blo 2059435 3091613 := bbase (se 3 (by rfl) ⟨579677, by rfl⟩ : syracuseStep 3091613 = 1159355) (by norm_num)
theorem B2061075 : Blo 2059435 2061075 := bstep (se 1 (by rfl) ⟨1545806, by rfl⟩ : syracuseStep 2061075 = 3091613) B3091613
theorem B4637429 : Blo 2059435 4637429 := bbase (se 5 (by rfl) ⟨217379, by rfl⟩ : syracuseStep 4637429 = 434759) (by norm_num)
theorem B3091619 : Blo 2059435 3091619 := bstep (se 1 (by rfl) ⟨2318714, by rfl⟩ : syracuseStep 3091619 = 4637429) B4637429
theorem B2061079 : Blo 2059435 2061079 := bstep (se 1 (by rfl) ⟨1545809, by rfl⟩ : syracuseStep 2061079 = 3091619) B3091619
theorem B26411669 : Blo 2059435 26411669 := bbase (se 6 (by rfl) ⟨619023, by rfl⟩ : syracuseStep 26411669 = 1238047) (by norm_num)
theorem B17607779 : Blo 2059435 17607779 := bstep (se 1 (by rfl) ⟨13205834, by rfl⟩ : syracuseStep 17607779 = 26411669) B26411669
theorem B11738519 : Blo 2059435 11738519 := bstep (se 1 (by rfl) ⟨8803889, by rfl⟩ : syracuseStep 11738519 = 17607779) B17607779
theorem B7825679 : Blo 2059435 7825679 := bstep (se 1 (by rfl) ⟨5869259, by rfl⟩ : syracuseStep 7825679 = 11738519) B11738519
theorem B5217119 : Blo 2059435 5217119 := bstep (se 1 (by rfl) ⟨3912839, by rfl⟩ : syracuseStep 5217119 = 7825679) B7825679
theorem B3478079 : Blo 2059435 3478079 := bstep (se 1 (by rfl) ⟨2608559, by rfl⟩ : syracuseStep 3478079 = 5217119) B5217119
theorem B2318719 : Blo 2059435 2318719 := bstep (se 1 (by rfl) ⟨1739039, by rfl⟩ : syracuseStep 2318719 = 3478079) B3478079
theorem B3091625 : Blo 2059435 3091625 := bstep (se 2 (by rfl) ⟨1159359, by rfl⟩ : syracuseStep 3091625 = 2318719) B2318719
theorem B2061083 : Blo 2059435 2061083 := bstep (se 1 (by rfl) ⟨1545812, by rfl⟩ : syracuseStep 2061083 = 3091625) B3091625
theorem B3714149 : Blo 2059435 3714149 := bbase (se 4 (by rfl) ⟨348201, by rfl⟩ : syracuseStep 3714149 = 696403) (by norm_num)
theorem B2476099 : Blo 2059435 2476099 := bstep (se 1 (by rfl) ⟨1857074, by rfl⟩ : syracuseStep 2476099 = 3714149) B3714149
theorem B3301465 : Blo 2059435 3301465 := bstep (se 2 (by rfl) ⟨1238049, by rfl⟩ : syracuseStep 3301465 = 2476099) B2476099
theorem B4401953 : Blo 2059435 4401953 := bstep (se 2 (by rfl) ⟨1650732, by rfl⟩ : syracuseStep 4401953 = 3301465) B3301465
theorem B2934635 : Blo 2059435 2934635 := bstep (se 1 (by rfl) ⟨2200976, by rfl⟩ : syracuseStep 2934635 = 4401953) B4401953
theorem B7825693 : Blo 2059435 7825693 := bstep (se 3 (by rfl) ⟨1467317, by rfl⟩ : syracuseStep 7825693 = 2934635) B2934635
theorem B10434257 : Blo 2059435 10434257 := bstep (se 2 (by rfl) ⟨3912846, by rfl⟩ : syracuseStep 10434257 = 7825693) B7825693
theorem B6956171 : Blo 2059435 6956171 := bstep (se 1 (by rfl) ⟨5217128, by rfl⟩ : syracuseStep 6956171 = 10434257) B10434257
theorem B4637447 : Blo 2059435 4637447 := bstep (se 1 (by rfl) ⟨3478085, by rfl⟩ : syracuseStep 4637447 = 6956171) B6956171
theorem B3091631 : Blo 2059435 3091631 := bstep (se 1 (by rfl) ⟨2318723, by rfl⟩ : syracuseStep 3091631 = 4637447) B4637447
theorem B2061087 : Blo 2059435 2061087 := bstep (se 1 (by rfl) ⟨1545815, by rfl⟩ : syracuseStep 2061087 = 3091631) B3091631
theorem B3091637 : Blo 2059435 3091637 := bbase (se 5 (by rfl) ⟨144920, by rfl⟩ : syracuseStep 3091637 = 289841) (by norm_num)
theorem B2061091 : Blo 2059435 2061091 := bstep (se 1 (by rfl) ⟨1545818, by rfl⟩ : syracuseStep 2061091 = 3091637) B3091637
theorem B5217149 : Blo 2059435 5217149 := bbase (se 3 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 5217149 = 1956431) (by norm_num)
theorem B3478099 : Blo 2059435 3478099 := bstep (se 1 (by rfl) ⟨2608574, by rfl⟩ : syracuseStep 3478099 = 5217149) B5217149
theorem B4637465 : Blo 2059435 4637465 := bstep (se 2 (by rfl) ⟨1739049, by rfl⟩ : syracuseStep 4637465 = 3478099) B3478099
theorem B3091643 : Blo 2059435 3091643 := bstep (se 1 (by rfl) ⟨2318732, by rfl⟩ : syracuseStep 3091643 = 4637465) B4637465
theorem B2061095 : Blo 2059435 2061095 := bstep (se 1 (by rfl) ⟨1545821, by rfl⟩ : syracuseStep 2061095 = 3091643) B3091643
theorem B2318737 : Blo 2059435 2318737 := bbase (se 2 (by rfl) ⟨869526, by rfl⟩ : syracuseStep 2318737 = 1739053) (by norm_num)
theorem B3091649 : Blo 2059435 3091649 := bstep (se 2 (by rfl) ⟨1159368, by rfl⟩ : syracuseStep 3091649 = 2318737) B2318737
theorem B2061099 : Blo 2059435 2061099 := bstep (se 1 (by rfl) ⟨1545824, by rfl⟩ : syracuseStep 2061099 = 3091649) B3091649
theorem B3912877 : Blo 2059435 3912877 := bbase (se 3 (by rfl) ⟨733664, by rfl⟩ : syracuseStep 3912877 = 1467329) (by norm_num)
theorem B5217169 : Blo 2059435 5217169 := bstep (se 2 (by rfl) ⟨1956438, by rfl⟩ : syracuseStep 5217169 = 3912877) B3912877
theorem B6956225 : Blo 2059435 6956225 := bstep (se 2 (by rfl) ⟨2608584, by rfl⟩ : syracuseStep 6956225 = 5217169) B5217169
theorem B4637483 : Blo 2059435 4637483 := bstep (se 1 (by rfl) ⟨3478112, by rfl⟩ : syracuseStep 4637483 = 6956225) B6956225
theorem B3091655 : Blo 2059435 3091655 := bstep (se 1 (by rfl) ⟨2318741, by rfl⟩ : syracuseStep 3091655 = 4637483) B4637483
theorem B2061103 : Blo 2059435 2061103 := bstep (se 1 (by rfl) ⟨1545827, by rfl⟩ : syracuseStep 2061103 = 3091655) B3091655
theorem B3091661 : Blo 2059435 3091661 := bbase (se 3 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 3091661 = 1159373) (by norm_num)
theorem B2061107 : Blo 2059435 2061107 := bstep (se 1 (by rfl) ⟨1545830, by rfl⟩ : syracuseStep 2061107 = 3091661) B3091661
theorem B4637501 : Blo 2059435 4637501 := bbase (se 3 (by rfl) ⟨869531, by rfl⟩ : syracuseStep 4637501 = 1739063) (by norm_num)
theorem B3091667 : Blo 2059435 3091667 := bstep (se 1 (by rfl) ⟨2318750, by rfl⟩ : syracuseStep 3091667 = 4637501) B4637501
theorem B2061111 : Blo 2059435 2061111 := bstep (se 1 (by rfl) ⟨1545833, by rfl⟩ : syracuseStep 2061111 = 3091667) B3091667
theorem B3478133 : Blo 2059435 3478133 := bbase (se 5 (by rfl) ⟨163037, by rfl⟩ : syracuseStep 3478133 = 326075) (by norm_num)
theorem B2318755 : Blo 2059435 2318755 := bstep (se 1 (by rfl) ⟨1739066, by rfl⟩ : syracuseStep 2318755 = 3478133) B3478133
theorem B3091673 : Blo 2059435 3091673 := bstep (se 2 (by rfl) ⟨1159377, by rfl⟩ : syracuseStep 3091673 = 2318755) B2318755
theorem B2061115 : Blo 2059435 2061115 := bstep (se 1 (by rfl) ⟨1545836, by rfl⟩ : syracuseStep 2061115 = 3091673) B3091673
theorem B4402021 : Blo 2059435 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B5869361 : Blo 2059435 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B15651629 : Blo 2059435 15651629 := bstep (se 3 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 15651629 = 5869361) B5869361
theorem B10434419 : Blo 2059435 10434419 := bstep (se 1 (by rfl) ⟨7825814, by rfl⟩ : syracuseStep 10434419 = 15651629) B15651629
theorem B6956279 : Blo 2059435 6956279 := bstep (se 1 (by rfl) ⟨5217209, by rfl⟩ : syracuseStep 6956279 = 10434419) B10434419
theorem B4637519 : Blo 2059435 4637519 := bstep (se 1 (by rfl) ⟨3478139, by rfl⟩ : syracuseStep 4637519 = 6956279) B6956279
theorem B3091679 : Blo 2059435 3091679 := bstep (se 1 (by rfl) ⟨2318759, by rfl⟩ : syracuseStep 3091679 = 4637519) B4637519
theorem B2061119 : Blo 2059435 2061119 := bstep (se 1 (by rfl) ⟨1545839, by rfl⟩ : syracuseStep 2061119 = 3091679) B3091679
theorem B3091685 : Blo 2059435 3091685 := bbase (se 4 (by rfl) ⟨289845, by rfl⟩ : syracuseStep 3091685 = 579691) (by norm_num)
theorem B2061123 : Blo 2059435 2061123 := bstep (se 1 (by rfl) ⟨1545842, by rfl⟩ : syracuseStep 2061123 = 3091685) B3091685
theorem B3714221 : Blo 2059435 3714221 := bbase (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) (by norm_num)
theorem B9904589 : Blo 2059435 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B6603059 : Blo 2059435 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B4402039 : Blo 2059435 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B5869385 : Blo 2059435 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B3912923 : Blo 2059435 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B2608615 : Blo 2059435 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B3478153 : Blo 2059435 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B4637537 : Blo 2059435 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B3091691 : Blo 2059435 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B2061127 : Blo 2059435 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B2318773 : Blo 2059435 2318773 := bbase (se 5 (by rfl) ⟨108692, by rfl⟩ : syracuseStep 2318773 = 217385) (by norm_num)
theorem B3091697 : Blo 2059435 3091697 := bstep (se 2 (by rfl) ⟨1159386, by rfl⟩ : syracuseStep 3091697 = 2318773) B2318773
theorem B2061131 : Blo 2059435 2061131 := bstep (se 1 (by rfl) ⟨1545848, by rfl⟩ : syracuseStep 2061131 = 3091697) B3091697
theorem B2608625 : Blo 2059435 2608625 := bbase (se 2 (by rfl) ⟨978234, by rfl⟩ : syracuseStep 2608625 = 1956469) (by norm_num)
theorem B6956333 : Blo 2059435 6956333 := bstep (se 3 (by rfl) ⟨1304312, by rfl⟩ : syracuseStep 6956333 = 2608625) B2608625
theorem B4637555 : Blo 2059435 4637555 := bstep (se 1 (by rfl) ⟨3478166, by rfl⟩ : syracuseStep 4637555 = 6956333) B6956333
theorem B3091703 : Blo 2059435 3091703 := bstep (se 1 (by rfl) ⟨2318777, by rfl⟩ : syracuseStep 3091703 = 4637555) B4637555
theorem B2061135 : Blo 2059435 2061135 := bstep (se 1 (by rfl) ⟨1545851, by rfl⟩ : syracuseStep 2061135 = 3091703) B3091703
theorem B3091709 : Blo 2059435 3091709 := bbase (se 3 (by rfl) ⟨579695, by rfl⟩ : syracuseStep 3091709 = 1159391) (by norm_num)
theorem B2061139 : Blo 2059435 2061139 := bstep (se 1 (by rfl) ⟨1545854, by rfl⟩ : syracuseStep 2061139 = 3091709) B3091709
theorem B4637573 : Blo 2059435 4637573 := bbase (se 4 (by rfl) ⟨434772, by rfl⟩ : syracuseStep 4637573 = 869545) (by norm_num)
theorem B3091715 : Blo 2059435 3091715 := bstep (se 1 (by rfl) ⟨2318786, by rfl⟩ : syracuseStep 3091715 = 4637573) B4637573
theorem B2061143 : Blo 2059435 2061143 := bstep (se 1 (by rfl) ⟨1545857, by rfl⟩ : syracuseStep 2061143 = 3091715) B3091715
theorem B2201041 : Blo 2059435 2201041 := bbase (se 2 (by rfl) ⟨825390, by rfl⟩ : syracuseStep 2201041 = 1650781) (by norm_num)
theorem B2934721 : Blo 2059435 2934721 := bstep (se 2 (by rfl) ⟨1100520, by rfl⟩ : syracuseStep 2934721 = 2201041) B2201041
theorem B3912961 : Blo 2059435 3912961 := bstep (se 2 (by rfl) ⟨1467360, by rfl⟩ : syracuseStep 3912961 = 2934721) B2934721
theorem B5217281 : Blo 2059435 5217281 := bstep (se 2 (by rfl) ⟨1956480, by rfl⟩ : syracuseStep 5217281 = 3912961) B3912961
theorem B3478187 : Blo 2059435 3478187 := bstep (se 1 (by rfl) ⟨2608640, by rfl⟩ : syracuseStep 3478187 = 5217281) B5217281
theorem B2318791 : Blo 2059435 2318791 := bstep (se 1 (by rfl) ⟨1739093, by rfl⟩ : syracuseStep 2318791 = 3478187) B3478187
theorem B3091721 : Blo 2059435 3091721 := bstep (se 2 (by rfl) ⟨1159395, by rfl⟩ : syracuseStep 3091721 = 2318791) B2318791
theorem B2061147 : Blo 2059435 2061147 := bstep (se 1 (by rfl) ⟨1545860, by rfl⟩ : syracuseStep 2061147 = 3091721) B3091721
theorem B10434581 : Blo 2059435 10434581 := bbase (se 6 (by rfl) ⟨244560, by rfl⟩ : syracuseStep 10434581 = 489121) (by norm_num)
theorem B6956387 : Blo 2059435 6956387 := bstep (se 1 (by rfl) ⟨5217290, by rfl⟩ : syracuseStep 6956387 = 10434581) B10434581
theorem B4637591 : Blo 2059435 4637591 := bstep (se 1 (by rfl) ⟨3478193, by rfl⟩ : syracuseStep 4637591 = 6956387) B6956387
theorem B3091727 : Blo 2059435 3091727 := bstep (se 1 (by rfl) ⟨2318795, by rfl⟩ : syracuseStep 3091727 = 4637591) B4637591
theorem B2061151 : Blo 2059435 2061151 := bstep (se 1 (by rfl) ⟨1545863, by rfl⟩ : syracuseStep 2061151 = 3091727) B3091727
theorem B3091733 : Blo 2059435 3091733 := bbase (se 6 (by rfl) ⟨72462, by rfl⟩ : syracuseStep 3091733 = 144925) (by norm_num)
theorem B2061155 : Blo 2059435 2061155 := bstep (se 1 (by rfl) ⟨1545866, by rfl⟩ : syracuseStep 2061155 = 3091733) B3091733
theorem B33428501 : Blo 2059435 33428501 := bbase (se 6 (by rfl) ⟨783480, by rfl⟩ : syracuseStep 33428501 = 1566961) (by norm_num)
theorem B22285667 : Blo 2059435 22285667 := bstep (se 1 (by rfl) ⟨16714250, by rfl⟩ : syracuseStep 22285667 = 33428501) B33428501
theorem B14857111 : Blo 2059435 14857111 := bstep (se 1 (by rfl) ⟨11142833, by rfl⟩ : syracuseStep 14857111 = 22285667) B22285667
theorem B19809481 : Blo 2059435 19809481 := bstep (se 2 (by rfl) ⟨7428555, by rfl⟩ : syracuseStep 19809481 = 14857111) B14857111
theorem B26412641 : Blo 2059435 26412641 := bstep (se 2 (by rfl) ⟨9904740, by rfl⟩ : syracuseStep 26412641 = 19809481) B19809481
theorem B17608427 : Blo 2059435 17608427 := bstep (se 1 (by rfl) ⟨13206320, by rfl⟩ : syracuseStep 17608427 = 26412641) B26412641
theorem B11738951 : Blo 2059435 11738951 := bstep (se 1 (by rfl) ⟨8804213, by rfl⟩ : syracuseStep 11738951 = 17608427) B17608427
theorem B7825967 : Blo 2059435 7825967 := bstep (se 1 (by rfl) ⟨5869475, by rfl⟩ : syracuseStep 7825967 = 11738951) B11738951
theorem B5217311 : Blo 2059435 5217311 := bstep (se 1 (by rfl) ⟨3912983, by rfl⟩ : syracuseStep 5217311 = 7825967) B7825967
theorem B3478207 : Blo 2059435 3478207 := bstep (se 1 (by rfl) ⟨2608655, by rfl⟩ : syracuseStep 3478207 = 5217311) B5217311
theorem B4637609 : Blo 2059435 4637609 := bstep (se 2 (by rfl) ⟨1739103, by rfl⟩ : syracuseStep 4637609 = 3478207) B3478207
theorem B3091739 : Blo 2059435 3091739 := bstep (se 1 (by rfl) ⟨2318804, by rfl⟩ : syracuseStep 3091739 = 4637609) B4637609
theorem B2061159 : Blo 2059435 2061159 := bstep (se 1 (by rfl) ⟨1545869, by rfl⟩ : syracuseStep 2061159 = 3091739) B3091739
theorem B2318809 : Blo 2059435 2318809 := bbase (se 2 (by rfl) ⟨869553, by rfl⟩ : syracuseStep 2318809 = 1739107) (by norm_num)
theorem B3091745 : Blo 2059435 3091745 := bstep (se 2 (by rfl) ⟨1159404, by rfl⟩ : syracuseStep 3091745 = 2318809) B2318809
theorem B2061163 : Blo 2059435 2061163 := bstep (se 1 (by rfl) ⟨1545872, by rfl⟩ : syracuseStep 2061163 = 3091745) B3091745
theorem B2934749 : Blo 2059435 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B7825997 : Blo 2059435 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B5217331 : Blo 2059435 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B6956441 : Blo 2059435 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B4637627 : Blo 2059435 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B3091751 : Blo 2059435 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B2061167 : Blo 2059435 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B3091757 : Blo 2059435 3091757 := bbase (se 3 (by rfl) ⟨579704, by rfl⟩ : syracuseStep 3091757 = 1159409) (by norm_num)
theorem B2061171 : Blo 2059435 2061171 := bstep (se 1 (by rfl) ⟨1545878, by rfl⟩ : syracuseStep 2061171 = 3091757) B3091757
theorem B4637645 : Blo 2059435 4637645 := bbase (se 3 (by rfl) ⟨869558, by rfl⟩ : syracuseStep 4637645 = 1739117) (by norm_num)
theorem B3091763 : Blo 2059435 3091763 := bstep (se 1 (by rfl) ⟨2318822, by rfl⟩ : syracuseStep 3091763 = 4637645) B4637645
theorem B2061175 : Blo 2059435 2061175 := bstep (se 1 (by rfl) ⟨1545881, by rfl⟩ : syracuseStep 2061175 = 3091763) B3091763
theorem B2608681 : Blo 2059435 2608681 := bbase (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) (by norm_num)
theorem B3478241 : Blo 2059435 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B2318827 : Blo 2059435 2318827 := bstep (se 1 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 2318827 = 3478241) B3478241
theorem B3091769 : Blo 2059435 3091769 := bstep (se 2 (by rfl) ⟨1159413, by rfl⟩ : syracuseStep 3091769 = 2318827) B2318827
theorem B2061179 : Blo 2059435 2061179 := bstep (se 1 (by rfl) ⟨1545884, by rfl⟩ : syracuseStep 2061179 = 3091769) B3091769
theorem B2350469 : Blo 2059435 2350469 := bbase (se 4 (by rfl) ⟨220356, by rfl⟩ : syracuseStep 2350469 = 440713) (by norm_num)
theorem B6267917 : Blo 2059435 6267917 := bstep (se 3 (by rfl) ⟨1175234, by rfl⟩ : syracuseStep 6267917 = 2350469) B2350469
theorem B4178611 : Blo 2059435 4178611 := bstep (se 1 (by rfl) ⟨3133958, by rfl⟩ : syracuseStep 4178611 = 6267917) B6267917
theorem B22285925 : Blo 2059435 22285925 := bstep (se 4 (by rfl) ⟨2089305, by rfl⟩ : syracuseStep 22285925 = 4178611) B4178611
theorem B14857283 : Blo 2059435 14857283 := bstep (se 1 (by rfl) ⟨11142962, by rfl⟩ : syracuseStep 14857283 = 22285925) B22285925
theorem B9904855 : Blo 2059435 9904855 := bstep (se 1 (by rfl) ⟨7428641, by rfl⟩ : syracuseStep 9904855 = 14857283) B14857283
theorem B13206473 : Blo 2059435 13206473 := bstep (se 2 (by rfl) ⟨4952427, by rfl⟩ : syracuseStep 13206473 = 9904855) B9904855
theorem B8804315 : Blo 2059435 8804315 := bstep (se 1 (by rfl) ⟨6603236, by rfl⟩ : syracuseStep 8804315 = 13206473) B13206473
theorem B23478173 : Blo 2059435 23478173 := bstep (se 3 (by rfl) ⟨4402157, by rfl⟩ : syracuseStep 23478173 = 8804315) B8804315
theorem B15652115 : Blo 2059435 15652115 := bstep (se 1 (by rfl) ⟨11739086, by rfl⟩ : syracuseStep 15652115 = 23478173) B23478173
theorem B10434743 : Blo 2059435 10434743 := bstep (se 1 (by rfl) ⟨7826057, by rfl⟩ : syracuseStep 10434743 = 15652115) B15652115
theorem B6956495 : Blo 2059435 6956495 := bstep (se 1 (by rfl) ⟨5217371, by rfl⟩ : syracuseStep 6956495 = 10434743) B10434743
theorem B4637663 : Blo 2059435 4637663 := bstep (se 1 (by rfl) ⟨3478247, by rfl⟩ : syracuseStep 4637663 = 6956495) B6956495
theorem B3091775 : Blo 2059435 3091775 := bstep (se 1 (by rfl) ⟨2318831, by rfl⟩ : syracuseStep 3091775 = 4637663) B4637663
theorem B2061183 : Blo 2059435 2061183 := bstep (se 1 (by rfl) ⟨1545887, by rfl⟩ : syracuseStep 2061183 = 3091775) B3091775
theorem B3091781 : Blo 2059435 3091781 := bbase (se 4 (by rfl) ⟨289854, by rfl⟩ : syracuseStep 3091781 = 579709) (by norm_num)
theorem B2061187 : Blo 2059435 2061187 := bstep (se 1 (by rfl) ⟨1545890, by rfl⟩ : syracuseStep 2061187 = 3091781) B3091781
theorem B3478261 : Blo 2059435 3478261 := bbase (se 5 (by rfl) ⟨163043, by rfl⟩ : syracuseStep 3478261 = 326087) (by norm_num)
theorem B4637681 : Blo 2059435 4637681 := bstep (se 2 (by rfl) ⟨1739130, by rfl⟩ : syracuseStep 4637681 = 3478261) B3478261
theorem B3091787 : Blo 2059435 3091787 := bstep (se 1 (by rfl) ⟨2318840, by rfl⟩ : syracuseStep 3091787 = 4637681) B4637681
theorem B2061191 : Blo 2059435 2061191 := bstep (se 1 (by rfl) ⟨1545893, by rfl⟩ : syracuseStep 2061191 = 3091787) B3091787
theorem B2318845 : Blo 2059435 2318845 := bbase (se 3 (by rfl) ⟨434783, by rfl⟩ : syracuseStep 2318845 = 869567) (by norm_num)
theorem B3091793 : Blo 2059435 3091793 := bstep (se 2 (by rfl) ⟨1159422, by rfl⟩ : syracuseStep 3091793 = 2318845) B2318845
theorem B2061195 : Blo 2059435 2061195 := bstep (se 1 (by rfl) ⟨1545896, by rfl⟩ : syracuseStep 2061195 = 3091793) B3091793
theorem B6956549 : Blo 2059435 6956549 := bbase (se 4 (by rfl) ⟨652176, by rfl⟩ : syracuseStep 6956549 = 1304353) (by norm_num)
theorem B4637699 : Blo 2059435 4637699 := bstep (se 1 (by rfl) ⟨3478274, by rfl⟩ : syracuseStep 4637699 = 6956549) B6956549
theorem B3091799 : Blo 2059435 3091799 := bstep (se 1 (by rfl) ⟨2318849, by rfl⟩ : syracuseStep 3091799 = 4637699) B4637699
theorem B2061199 : Blo 2059435 2061199 := bstep (se 1 (by rfl) ⟨1545899, by rfl⟩ : syracuseStep 2061199 = 3091799) B3091799
theorem B3091805 : Blo 2059435 3091805 := bbase (se 3 (by rfl) ⟨579713, by rfl⟩ : syracuseStep 3091805 = 1159427) (by norm_num)
theorem B2061203 : Blo 2059435 2061203 := bstep (se 1 (by rfl) ⟨1545902, by rfl⟩ : syracuseStep 2061203 = 3091805) B3091805
theorem B4637717 : Blo 2059435 4637717 := bbase (se 6 (by rfl) ⟨108696, by rfl⟩ : syracuseStep 4637717 = 217393) (by norm_num)
theorem B3091811 : Blo 2059435 3091811 := bstep (se 1 (by rfl) ⟨2318858, by rfl⟩ : syracuseStep 3091811 = 4637717) B4637717
theorem B2061207 : Blo 2059435 2061207 := bstep (se 1 (by rfl) ⟨1545905, by rfl⟩ : syracuseStep 2061207 = 3091811) B3091811
theorem B7826165 : Blo 2059435 7826165 := bbase (se 5 (by rfl) ⟨366851, by rfl⟩ : syracuseStep 7826165 = 733703) (by norm_num)
theorem B5217443 : Blo 2059435 5217443 := bstep (se 1 (by rfl) ⟨3913082, by rfl⟩ : syracuseStep 5217443 = 7826165) B7826165
theorem B3478295 : Blo 2059435 3478295 := bstep (se 1 (by rfl) ⟨2608721, by rfl⟩ : syracuseStep 3478295 = 5217443) B5217443
theorem B2318863 : Blo 2059435 2318863 := bstep (se 1 (by rfl) ⟨1739147, by rfl⟩ : syracuseStep 2318863 = 3478295) B3478295
theorem B3091817 : Blo 2059435 3091817 := bstep (se 2 (by rfl) ⟨1159431, by rfl⟩ : syracuseStep 3091817 = 2318863) B2318863
theorem B2061211 : Blo 2059435 2061211 := bstep (se 1 (by rfl) ⟨1545908, by rfl⟩ : syracuseStep 2061211 = 3091817) B3091817
theorem B2201113 : Blo 2059435 2201113 := bbase (se 2 (by rfl) ⟨825417, by rfl⟩ : syracuseStep 2201113 = 1650835) (by norm_num)
theorem B11739269 : Blo 2059435 11739269 := bstep (se 4 (by rfl) ⟨1100556, by rfl⟩ : syracuseStep 11739269 = 2201113) B2201113
theorem B7826179 : Blo 2059435 7826179 := bstep (se 1 (by rfl) ⟨5869634, by rfl⟩ : syracuseStep 7826179 = 11739269) B11739269
theorem B10434905 : Blo 2059435 10434905 := bstep (se 2 (by rfl) ⟨3913089, by rfl⟩ : syracuseStep 10434905 = 7826179) B7826179
theorem B6956603 : Blo 2059435 6956603 := bstep (se 1 (by rfl) ⟨5217452, by rfl⟩ : syracuseStep 6956603 = 10434905) B10434905
theorem B4637735 : Blo 2059435 4637735 := bstep (se 1 (by rfl) ⟨3478301, by rfl⟩ : syracuseStep 4637735 = 6956603) B6956603
theorem B3091823 : Blo 2059435 3091823 := bstep (se 1 (by rfl) ⟨2318867, by rfl⟩ : syracuseStep 3091823 = 4637735) B4637735
theorem B2061215 : Blo 2059435 2061215 := bstep (se 1 (by rfl) ⟨1545911, by rfl⟩ : syracuseStep 2061215 = 3091823) B3091823
theorem B3091829 : Blo 2059435 3091829 := bbase (se 5 (by rfl) ⟨144929, by rfl⟩ : syracuseStep 3091829 = 289859) (by norm_num)
theorem B2061219 : Blo 2059435 2061219 := bstep (se 1 (by rfl) ⟨1545914, by rfl⟩ : syracuseStep 2061219 = 3091829) B3091829
theorem B2934829 : Blo 2059435 2934829 := bbase (se 3 (by rfl) ⟨550280, by rfl⟩ : syracuseStep 2934829 = 1100561) (by norm_num)
theorem B3913105 : Blo 2059435 3913105 := bstep (se 2 (by rfl) ⟨1467414, by rfl⟩ : syracuseStep 3913105 = 2934829) B2934829
theorem B5217473 : Blo 2059435 5217473 := bstep (se 2 (by rfl) ⟨1956552, by rfl⟩ : syracuseStep 5217473 = 3913105) B3913105
theorem B3478315 : Blo 2059435 3478315 := bstep (se 1 (by rfl) ⟨2608736, by rfl⟩ : syracuseStep 3478315 = 5217473) B5217473
theorem B4637753 : Blo 2059435 4637753 := bstep (se 2 (by rfl) ⟨1739157, by rfl⟩ : syracuseStep 4637753 = 3478315) B3478315
theorem B3091835 : Blo 2059435 3091835 := bstep (se 1 (by rfl) ⟨2318876, by rfl⟩ : syracuseStep 3091835 = 4637753) B4637753
theorem B2061223 : Blo 2059435 2061223 := bstep (se 1 (by rfl) ⟨1545917, by rfl⟩ : syracuseStep 2061223 = 3091835) B3091835
theorem B2318881 : Blo 2059435 2318881 := bbase (se 2 (by rfl) ⟨869580, by rfl⟩ : syracuseStep 2318881 = 1739161) (by norm_num)
theorem B3091841 : Blo 2059435 3091841 := bstep (se 2 (by rfl) ⟨1159440, by rfl⟩ : syracuseStep 3091841 = 2318881) B2318881
theorem B2061227 : Blo 2059435 2061227 := bstep (se 1 (by rfl) ⟨1545920, by rfl⟩ : syracuseStep 2061227 = 3091841) B3091841
theorem B5217493 : Blo 2059435 5217493 := bbase (se 7 (by rfl) ⟨61142, by rfl⟩ : syracuseStep 5217493 = 122285) (by norm_num)
theorem B6956657 : Blo 2059435 6956657 := bstep (se 2 (by rfl) ⟨2608746, by rfl⟩ : syracuseStep 6956657 = 5217493) B5217493
theorem B4637771 : Blo 2059435 4637771 := bstep (se 1 (by rfl) ⟨3478328, by rfl⟩ : syracuseStep 4637771 = 6956657) B6956657
theorem B3091847 : Blo 2059435 3091847 := bstep (se 1 (by rfl) ⟨2318885, by rfl⟩ : syracuseStep 3091847 = 4637771) B4637771
theorem B2061231 : Blo 2059435 2061231 := bstep (se 1 (by rfl) ⟨1545923, by rfl⟩ : syracuseStep 2061231 = 3091847) B3091847
theorem B3091853 : Blo 2059435 3091853 := bbase (se 3 (by rfl) ⟨579722, by rfl⟩ : syracuseStep 3091853 = 1159445) (by norm_num)
theorem B2061235 : Blo 2059435 2061235 := bstep (se 1 (by rfl) ⟨1545926, by rfl⟩ : syracuseStep 2061235 = 3091853) B3091853
theorem B4637789 : Blo 2059435 4637789 := bbase (se 3 (by rfl) ⟨869585, by rfl⟩ : syracuseStep 4637789 = 1739171) (by norm_num)
theorem B3091859 : Blo 2059435 3091859 := bstep (se 1 (by rfl) ⟨2318894, by rfl⟩ : syracuseStep 3091859 = 4637789) B4637789
theorem B2061239 : Blo 2059435 2061239 := bstep (se 1 (by rfl) ⟨1545929, by rfl⟩ : syracuseStep 2061239 = 3091859) B3091859
theorem B3478349 : Blo 2059435 3478349 := bbase (se 3 (by rfl) ⟨652190, by rfl⟩ : syracuseStep 3478349 = 1304381) (by norm_num)
theorem B2318899 : Blo 2059435 2318899 := bstep (se 1 (by rfl) ⟨1739174, by rfl⟩ : syracuseStep 2318899 = 3478349) B3478349
theorem B3091865 : Blo 2059435 3091865 := bstep (se 2 (by rfl) ⟨1159449, by rfl⟩ : syracuseStep 3091865 = 2318899) B2318899
theorem B2061243 : Blo 2059435 2061243 := bstep (se 1 (by rfl) ⟨1545932, by rfl⟩ : syracuseStep 2061243 = 3091865) B3091865
theorem B19810325 : Blo 2059435 19810325 := bbase (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) (by norm_num)
theorem B13206883 : Blo 2059435 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B17609177 : Blo 2059435 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B11739451 : Blo 2059435 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B15652601 : Blo 2059435 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B10435067 : Blo 2059435 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B6956711 : Blo 2059435 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B4637807 : Blo 2059435 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B3091871 : Blo 2059435 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B2061247 : Blo 2059435 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B3091877 : Blo 2059435 3091877 := bbase (se 4 (by rfl) ⟨289863, by rfl⟩ : syracuseStep 3091877 = 579727) (by norm_num)
theorem B2061251 : Blo 2059435 2061251 := bstep (se 1 (by rfl) ⟨1545938, by rfl⟩ : syracuseStep 2061251 = 3091877) B3091877
theorem B2608777 : Blo 2059435 2608777 := bbase (se 2 (by rfl) ⟨978291, by rfl⟩ : syracuseStep 2608777 = 1956583) (by norm_num)
theorem B3478369 : Blo 2059435 3478369 := bstep (se 2 (by rfl) ⟨1304388, by rfl⟩ : syracuseStep 3478369 = 2608777) B2608777
theorem B4637825 : Blo 2059435 4637825 := bstep (se 2 (by rfl) ⟨1739184, by rfl⟩ : syracuseStep 4637825 = 3478369) B3478369
theorem B3091883 : Blo 2059435 3091883 := bstep (se 1 (by rfl) ⟨2318912, by rfl⟩ : syracuseStep 3091883 = 4637825) B4637825
theorem B2061255 : Blo 2059435 2061255 := bstep (se 1 (by rfl) ⟨1545941, by rfl⟩ : syracuseStep 2061255 = 3091883) B3091883
theorem B2318917 : Blo 2059435 2318917 := bbase (se 4 (by rfl) ⟨217398, by rfl⟩ : syracuseStep 2318917 = 434797) (by norm_num)
theorem B3091889 : Blo 2059435 3091889 := bstep (se 2 (by rfl) ⟨1159458, by rfl⟩ : syracuseStep 3091889 = 2318917) B2318917
theorem B2061259 : Blo 2059435 2061259 := bstep (se 1 (by rfl) ⟨1545944, by rfl⟩ : syracuseStep 2061259 = 3091889) B3091889
theorem B3913181 : Blo 2059435 3913181 := bbase (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) (by norm_num)
theorem B2608787 : Blo 2059435 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B6956765 : Blo 2059435 6956765 := bstep (se 3 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 6956765 = 2608787) B2608787
theorem B4637843 : Blo 2059435 4637843 := bstep (se 1 (by rfl) ⟨3478382, by rfl⟩ : syracuseStep 4637843 = 6956765) B6956765
theorem B3091895 : Blo 2059435 3091895 := bstep (se 1 (by rfl) ⟨2318921, by rfl⟩ : syracuseStep 3091895 = 4637843) B4637843
theorem B2061263 : Blo 2059435 2061263 := bstep (se 1 (by rfl) ⟨1545947, by rfl⟩ : syracuseStep 2061263 = 3091895) B3091895
theorem B3091901 : Blo 2059435 3091901 := bbase (se 3 (by rfl) ⟨579731, by rfl⟩ : syracuseStep 3091901 = 1159463) (by norm_num)
theorem B2061267 : Blo 2059435 2061267 := bstep (se 1 (by rfl) ⟨1545950, by rfl⟩ : syracuseStep 2061267 = 3091901) B3091901
theorem B4637861 : Blo 2059435 4637861 := bbase (se 4 (by rfl) ⟨434799, by rfl⟩ : syracuseStep 4637861 = 869599) (by norm_num)
theorem B3091907 : Blo 2059435 3091907 := bstep (se 1 (by rfl) ⟨2318930, by rfl⟩ : syracuseStep 3091907 = 4637861) B4637861
theorem B2061271 : Blo 2059435 2061271 := bstep (se 1 (by rfl) ⟨1545953, by rfl⟩ : syracuseStep 2061271 = 3091907) B3091907
theorem B5217605 : Blo 2059435 5217605 := bbase (se 4 (by rfl) ⟨489150, by rfl⟩ : syracuseStep 5217605 = 978301) (by norm_num)
theorem B3478403 : Blo 2059435 3478403 := bstep (se 1 (by rfl) ⟨2608802, by rfl⟩ : syracuseStep 3478403 = 5217605) B5217605
theorem B2318935 : Blo 2059435 2318935 := bstep (se 1 (by rfl) ⟨1739201, by rfl⟩ : syracuseStep 2318935 = 3478403) B3478403
theorem B3091913 : Blo 2059435 3091913 := bstep (se 2 (by rfl) ⟨1159467, by rfl⟩ : syracuseStep 3091913 = 2318935) B2318935
theorem B2061275 : Blo 2059435 2061275 := bstep (se 1 (by rfl) ⟨1545956, by rfl⟩ : syracuseStep 2061275 = 3091913) B3091913
theorem B3525869 : Blo 2059435 3525869 := bbase (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) (by norm_num)
theorem B9402317 : Blo 2059435 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B6268211 : Blo 2059435 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B4178807 : Blo 2059435 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B2785871 : Blo 2059435 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B7428989 : Blo 2059435 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B4952659 : Blo 2059435 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B6603545 : Blo 2059435 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B4402363 : Blo 2059435 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B5869817 : Blo 2059435 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B3913211 : Blo 2059435 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B10435229 : Blo 2059435 10435229 := bstep (se 3 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 10435229 = 3913211) B3913211
theorem B6956819 : Blo 2059435 6956819 := bstep (se 1 (by rfl) ⟨5217614, by rfl⟩ : syracuseStep 6956819 = 10435229) B10435229
theorem B4637879 : Blo 2059435 4637879 := bstep (se 1 (by rfl) ⟨3478409, by rfl⟩ : syracuseStep 4637879 = 6956819) B6956819
theorem B3091919 : Blo 2059435 3091919 := bstep (se 1 (by rfl) ⟨2318939, by rfl⟩ : syracuseStep 3091919 = 4637879) B4637879
theorem B2061279 : Blo 2059435 2061279 := bstep (se 1 (by rfl) ⟨1545959, by rfl⟩ : syracuseStep 2061279 = 3091919) B3091919
theorem B3091925 : Blo 2059435 3091925 := bbase (se 7 (by rfl) ⟨36233, by rfl⟩ : syracuseStep 3091925 = 72467) (by norm_num)
theorem B2061283 : Blo 2059435 2061283 := bstep (se 1 (by rfl) ⟨1545962, by rfl⟩ : syracuseStep 2061283 = 3091925) B3091925
theorem B7826453 : Blo 2059435 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B5217635 : Blo 2059435 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B3478423 : Blo 2059435 3478423 := bstep (se 1 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 3478423 = 5217635) B5217635
theorem B4637897 : Blo 2059435 4637897 := bstep (se 2 (by rfl) ⟨1739211, by rfl⟩ : syracuseStep 4637897 = 3478423) B3478423
theorem B3091931 : Blo 2059435 3091931 := bstep (se 1 (by rfl) ⟨2318948, by rfl⟩ : syracuseStep 3091931 = 4637897) B4637897
theorem B2061287 : Blo 2059435 2061287 := bstep (se 1 (by rfl) ⟨1545965, by rfl⟩ : syracuseStep 2061287 = 3091931) B3091931
theorem B2318953 : Blo 2059435 2318953 := bbase (se 2 (by rfl) ⟨869607, by rfl⟩ : syracuseStep 2318953 = 1739215) (by norm_num)
theorem B3091937 : Blo 2059435 3091937 := bstep (se 2 (by rfl) ⟨1159476, by rfl⟩ : syracuseStep 3091937 = 2318953) B2318953
theorem B2061291 : Blo 2059435 2061291 := bstep (se 1 (by rfl) ⟨1545968, by rfl⟩ : syracuseStep 2061291 = 3091937) B3091937
theorem B4402397 : Blo 2059435 4402397 := bbase (se 3 (by rfl) ⟨825449, by rfl⟩ : syracuseStep 4402397 = 1650899) (by norm_num)
theorem B11739725 : Blo 2059435 11739725 := bstep (se 3 (by rfl) ⟨2201198, by rfl⟩ : syracuseStep 11739725 = 4402397) B4402397
theorem B7826483 : Blo 2059435 7826483 := bstep (se 1 (by rfl) ⟨5869862, by rfl⟩ : syracuseStep 7826483 = 11739725) B11739725
theorem B5217655 : Blo 2059435 5217655 := bstep (se 1 (by rfl) ⟨3913241, by rfl⟩ : syracuseStep 5217655 = 7826483) B7826483
theorem B6956873 : Blo 2059435 6956873 := bstep (se 2 (by rfl) ⟨2608827, by rfl⟩ : syracuseStep 6956873 = 5217655) B5217655
theorem B4637915 : Blo 2059435 4637915 := bstep (se 1 (by rfl) ⟨3478436, by rfl⟩ : syracuseStep 4637915 = 6956873) B6956873
theorem B3091943 : Blo 2059435 3091943 := bstep (se 1 (by rfl) ⟨2318957, by rfl⟩ : syracuseStep 3091943 = 4637915) B4637915
theorem B2061295 : Blo 2059435 2061295 := bstep (se 1 (by rfl) ⟨1545971, by rfl⟩ : syracuseStep 2061295 = 3091943) B3091943
theorem B3091949 : Blo 2059435 3091949 := bbase (se 3 (by rfl) ⟨579740, by rfl⟩ : syracuseStep 3091949 = 1159481) (by norm_num)
theorem B2061299 : Blo 2059435 2061299 := bstep (se 1 (by rfl) ⟨1545974, by rfl⟩ : syracuseStep 2061299 = 3091949) B3091949
theorem B4637933 : Blo 2059435 4637933 := bbase (se 3 (by rfl) ⟨869612, by rfl⟩ : syracuseStep 4637933 = 1739225) (by norm_num)
theorem B3091955 : Blo 2059435 3091955 := bstep (se 1 (by rfl) ⟨2318966, by rfl⟩ : syracuseStep 3091955 = 4637933) B4637933
theorem B2061303 : Blo 2059435 2061303 := bstep (se 1 (by rfl) ⟨1545977, by rfl⟩ : syracuseStep 2061303 = 3091955) B3091955
theorem B2934949 : Blo 2059435 2934949 := bbase (se 4 (by rfl) ⟨275151, by rfl⟩ : syracuseStep 2934949 = 550303) (by norm_num)
theorem B3913265 : Blo 2059435 3913265 := bstep (se 2 (by rfl) ⟨1467474, by rfl⟩ : syracuseStep 3913265 = 2934949) B2934949
theorem B2608843 : Blo 2059435 2608843 := bstep (se 1 (by rfl) ⟨1956632, by rfl⟩ : syracuseStep 2608843 = 3913265) B3913265
theorem B3478457 : Blo 2059435 3478457 := bstep (se 2 (by rfl) ⟨1304421, by rfl⟩ : syracuseStep 3478457 = 2608843) B2608843
theorem B2318971 : Blo 2059435 2318971 := bstep (se 1 (by rfl) ⟨1739228, by rfl⟩ : syracuseStep 2318971 = 3478457) B3478457
theorem B3091961 : Blo 2059435 3091961 := bstep (se 2 (by rfl) ⟨1159485, by rfl⟩ : syracuseStep 3091961 = 2318971) B2318971
theorem B2061307 : Blo 2059435 2061307 := bstep (se 1 (by rfl) ⟨1545980, by rfl⟩ : syracuseStep 2061307 = 3091961) B3091961
theorem B4701229 : Blo 2059435 4701229 := bbase (se 3 (by rfl) ⟨881480, by rfl⟩ : syracuseStep 4701229 = 1762961) (by norm_num)
theorem B25073221 : Blo 2059435 25073221 := bstep (se 4 (by rfl) ⟨2350614, by rfl⟩ : syracuseStep 25073221 = 4701229) B4701229
theorem B33430961 : Blo 2059435 33430961 := bstep (se 2 (by rfl) ⟨12536610, by rfl⟩ : syracuseStep 33430961 = 25073221) B25073221
theorem B22287307 : Blo 2059435 22287307 := bstep (se 1 (by rfl) ⟨16715480, by rfl⟩ : syracuseStep 22287307 = 33430961) B33430961
theorem B29716409 : Blo 2059435 29716409 := bstep (se 2 (by rfl) ⟨11143653, by rfl⟩ : syracuseStep 29716409 = 22287307) B22287307
theorem B79243757 : Blo 2059435 79243757 := bstep (se 3 (by rfl) ⟨14858204, by rfl⟩ : syracuseStep 79243757 = 29716409) B29716409
theorem B52829171 : Blo 2059435 52829171 := bstep (se 1 (by rfl) ⟨39621878, by rfl⟩ : syracuseStep 52829171 = 79243757) B79243757
theorem B35219447 : Blo 2059435 35219447 := bstep (se 1 (by rfl) ⟨26414585, by rfl⟩ : syracuseStep 35219447 = 52829171) B52829171
theorem B23479631 : Blo 2059435 23479631 := bstep (se 1 (by rfl) ⟨17609723, by rfl⟩ : syracuseStep 23479631 = 35219447) B35219447
theorem B15653087 : Blo 2059435 15653087 := bstep (se 1 (by rfl) ⟨11739815, by rfl⟩ : syracuseStep 15653087 = 23479631) B23479631
theorem B10435391 : Blo 2059435 10435391 := bstep (se 1 (by rfl) ⟨7826543, by rfl⟩ : syracuseStep 10435391 = 15653087) B15653087
theorem B6956927 : Blo 2059435 6956927 := bstep (se 1 (by rfl) ⟨5217695, by rfl⟩ : syracuseStep 6956927 = 10435391) B10435391
theorem B4637951 : Blo 2059435 4637951 := bstep (se 1 (by rfl) ⟨3478463, by rfl⟩ : syracuseStep 4637951 = 6956927) B6956927
theorem B3091967 : Blo 2059435 3091967 := bstep (se 1 (by rfl) ⟨2318975, by rfl⟩ : syracuseStep 3091967 = 4637951) B4637951
theorem B2061311 : Blo 2059435 2061311 := bstep (se 1 (by rfl) ⟨1545983, by rfl⟩ : syracuseStep 2061311 = 3091967) B3091967
theorem B3091973 : Blo 2059435 3091973 := bbase (se 4 (by rfl) ⟨289872, by rfl⟩ : syracuseStep 3091973 = 579745) (by norm_num)
theorem B2061315 : Blo 2059435 2061315 := bstep (se 1 (by rfl) ⟨1545986, by rfl⟩ : syracuseStep 2061315 = 3091973) B3091973
theorem B3478477 : Blo 2059435 3478477 := bbase (se 3 (by rfl) ⟨652214, by rfl⟩ : syracuseStep 3478477 = 1304429) (by norm_num)
theorem B4637969 : Blo 2059435 4637969 := bstep (se 2 (by rfl) ⟨1739238, by rfl⟩ : syracuseStep 4637969 = 3478477) B3478477
theorem B3091979 : Blo 2059435 3091979 := bstep (se 1 (by rfl) ⟨2318984, by rfl⟩ : syracuseStep 3091979 = 4637969) B4637969
theorem B2061319 : Blo 2059435 2061319 := bstep (se 1 (by rfl) ⟨1545989, by rfl⟩ : syracuseStep 2061319 = 3091979) B3091979
theorem B2318989 : Blo 2059435 2318989 := bbase (se 3 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 2318989 = 869621) (by norm_num)
theorem B3091985 : Blo 2059435 3091985 := bstep (se 2 (by rfl) ⟨1159494, by rfl⟩ : syracuseStep 3091985 = 2318989) B2318989
theorem B2061323 : Blo 2059435 2061323 := bstep (se 1 (by rfl) ⟨1545992, by rfl⟩ : syracuseStep 2061323 = 3091985) B3091985
theorem B6956981 : Blo 2059435 6956981 := bbase (se 5 (by rfl) ⟨326108, by rfl⟩ : syracuseStep 6956981 = 652217) (by norm_num)
theorem B4637987 : Blo 2059435 4637987 := bstep (se 1 (by rfl) ⟨3478490, by rfl⟩ : syracuseStep 4637987 = 6956981) B6956981
theorem B3091991 : Blo 2059435 3091991 := bstep (se 1 (by rfl) ⟨2318993, by rfl⟩ : syracuseStep 3091991 = 4637987) B4637987
theorem B2061327 : Blo 2059435 2061327 := bstep (se 1 (by rfl) ⟨1545995, by rfl⟩ : syracuseStep 2061327 = 3091991) B3091991
theorem B3091997 : Blo 2059435 3091997 := bbase (se 3 (by rfl) ⟨579749, by rfl⟩ : syracuseStep 3091997 = 1159499) (by norm_num)
theorem B2061331 : Blo 2059435 2061331 := bstep (se 1 (by rfl) ⟨1545998, by rfl⟩ : syracuseStep 2061331 = 3091997) B3091997
theorem B4638005 : Blo 2059435 4638005 := bbase (se 5 (by rfl) ⟨217406, by rfl⟩ : syracuseStep 4638005 = 434813) (by norm_num)
theorem B3092003 : Blo 2059435 3092003 := bstep (se 1 (by rfl) ⟨2319002, by rfl⟩ : syracuseStep 3092003 = 4638005) B4638005
theorem B2061335 : Blo 2059435 2061335 := bstep (se 1 (by rfl) ⟨1546001, by rfl⟩ : syracuseStep 2061335 = 3092003) B3092003
theorem B7429205 : Blo 2059435 7429205 := bbase (se 8 (by rfl) ⟨43530, by rfl⟩ : syracuseStep 7429205 = 87061) (by norm_num)
theorem B19811213 : Blo 2059435 19811213 := bstep (se 3 (by rfl) ⟨3714602, by rfl⟩ : syracuseStep 19811213 = 7429205) B7429205
theorem B13207475 : Blo 2059435 13207475 := bstep (se 1 (by rfl) ⟨9905606, by rfl⟩ : syracuseStep 13207475 = 19811213) B19811213
theorem B8804983 : Blo 2059435 8804983 := bstep (se 1 (by rfl) ⟨6603737, by rfl⟩ : syracuseStep 8804983 = 13207475) B13207475
theorem B11739977 : Blo 2059435 11739977 := bstep (se 2 (by rfl) ⟨4402491, by rfl⟩ : syracuseStep 11739977 = 8804983) B8804983
theorem B7826651 : Blo 2059435 7826651 := bstep (se 1 (by rfl) ⟨5869988, by rfl⟩ : syracuseStep 7826651 = 11739977) B11739977
theorem B5217767 : Blo 2059435 5217767 := bstep (se 1 (by rfl) ⟨3913325, by rfl⟩ : syracuseStep 5217767 = 7826651) B7826651
theorem B3478511 : Blo 2059435 3478511 := bstep (se 1 (by rfl) ⟨2608883, by rfl⟩ : syracuseStep 3478511 = 5217767) B5217767
theorem B2319007 : Blo 2059435 2319007 := bstep (se 1 (by rfl) ⟨1739255, by rfl⟩ : syracuseStep 2319007 = 3478511) B3478511
theorem B3092009 : Blo 2059435 3092009 := bstep (se 2 (by rfl) ⟨1159503, by rfl⟩ : syracuseStep 3092009 = 2319007) B2319007
theorem B2061339 : Blo 2059435 2061339 := bstep (se 1 (by rfl) ⟨1546004, by rfl⟩ : syracuseStep 2061339 = 3092009) B3092009
theorem B2785957 : Blo 2059435 2785957 := bbase (se 4 (by rfl) ⟨261183, by rfl⟩ : syracuseStep 2785957 = 522367) (by norm_num)
theorem B14858437 : Blo 2059435 14858437 := bstep (se 4 (by rfl) ⟨1392978, by rfl⟩ : syracuseStep 14858437 = 2785957) B2785957
theorem B19811249 : Blo 2059435 19811249 := bstep (se 2 (by rfl) ⟨7429218, by rfl⟩ : syracuseStep 19811249 = 14858437) B14858437
theorem B13207499 : Blo 2059435 13207499 := bstep (se 1 (by rfl) ⟨9905624, by rfl⟩ : syracuseStep 13207499 = 19811249) B19811249
theorem B8804999 : Blo 2059435 8804999 := bstep (se 1 (by rfl) ⟨6603749, by rfl⟩ : syracuseStep 8804999 = 13207499) B13207499
theorem B5869999 : Blo 2059435 5869999 := bstep (se 1 (by rfl) ⟨4402499, by rfl⟩ : syracuseStep 5869999 = 8804999) B8804999
theorem B7826665 : Blo 2059435 7826665 := bstep (se 2 (by rfl) ⟨2934999, by rfl⟩ : syracuseStep 7826665 = 5869999) B5869999
theorem B10435553 : Blo 2059435 10435553 := bstep (se 2 (by rfl) ⟨3913332, by rfl⟩ : syracuseStep 10435553 = 7826665) B7826665
theorem B6957035 : Blo 2059435 6957035 := bstep (se 1 (by rfl) ⟨5217776, by rfl⟩ : syracuseStep 6957035 = 10435553) B10435553
theorem B4638023 : Blo 2059435 4638023 := bstep (se 1 (by rfl) ⟨3478517, by rfl⟩ : syracuseStep 4638023 = 6957035) B6957035
theorem B3092015 : Blo 2059435 3092015 := bstep (se 1 (by rfl) ⟨2319011, by rfl⟩ : syracuseStep 3092015 = 4638023) B4638023
theorem B2061343 : Blo 2059435 2061343 := bstep (se 1 (by rfl) ⟨1546007, by rfl⟩ : syracuseStep 2061343 = 3092015) B3092015
theorem B3092021 : Blo 2059435 3092021 := bbase (se 5 (by rfl) ⟨144938, by rfl⟩ : syracuseStep 3092021 = 289877) (by norm_num)
theorem B2061347 : Blo 2059435 2061347 := bstep (se 1 (by rfl) ⟨1546010, by rfl⟩ : syracuseStep 2061347 = 3092021) B3092021
theorem B5217797 : Blo 2059435 5217797 := bbase (se 4 (by rfl) ⟨489168, by rfl⟩ : syracuseStep 5217797 = 978337) (by norm_num)
theorem B3478531 : Blo 2059435 3478531 := bstep (se 1 (by rfl) ⟨2608898, by rfl⟩ : syracuseStep 3478531 = 5217797) B5217797
theorem B4638041 : Blo 2059435 4638041 := bstep (se 2 (by rfl) ⟨1739265, by rfl⟩ : syracuseStep 4638041 = 3478531) B3478531
theorem B3092027 : Blo 2059435 3092027 := bstep (se 1 (by rfl) ⟨2319020, by rfl⟩ : syracuseStep 3092027 = 4638041) B4638041
theorem B2061351 : Blo 2059435 2061351 := bstep (se 1 (by rfl) ⟨1546013, by rfl⟩ : syracuseStep 2061351 = 3092027) B3092027
theorem B2319025 : Blo 2059435 2319025 := bbase (se 2 (by rfl) ⟨869634, by rfl⟩ : syracuseStep 2319025 = 1739269) (by norm_num)
theorem B3092033 : Blo 2059435 3092033 := bstep (se 2 (by rfl) ⟨1159512, by rfl⟩ : syracuseStep 3092033 = 2319025) B2319025
theorem B2061355 : Blo 2059435 2061355 := bstep (se 1 (by rfl) ⟨1546016, by rfl⟩ : syracuseStep 2061355 = 3092033) B3092033
theorem B3301901 : Blo 2059435 3301901 := bbase (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) (by norm_num)
theorem B2201267 : Blo 2059435 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B5870045 : Blo 2059435 5870045 := bstep (se 3 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 5870045 = 2201267) B2201267
theorem B3913363 : Blo 2059435 3913363 := bstep (se 1 (by rfl) ⟨2935022, by rfl⟩ : syracuseStep 3913363 = 5870045) B5870045
theorem B5217817 : Blo 2059435 5217817 := bstep (se 2 (by rfl) ⟨1956681, by rfl⟩ : syracuseStep 5217817 = 3913363) B3913363
theorem B6957089 : Blo 2059435 6957089 := bstep (se 2 (by rfl) ⟨2608908, by rfl⟩ : syracuseStep 6957089 = 5217817) B5217817
theorem B4638059 : Blo 2059435 4638059 := bstep (se 1 (by rfl) ⟨3478544, by rfl⟩ : syracuseStep 4638059 = 6957089) B6957089
theorem B3092039 : Blo 2059435 3092039 := bstep (se 1 (by rfl) ⟨2319029, by rfl⟩ : syracuseStep 3092039 = 4638059) B4638059
theorem B2061359 : Blo 2059435 2061359 := bstep (se 1 (by rfl) ⟨1546019, by rfl⟩ : syracuseStep 2061359 = 3092039) B3092039
theorem B3092045 : Blo 2059435 3092045 := bbase (se 3 (by rfl) ⟨579758, by rfl⟩ : syracuseStep 3092045 = 1159517) (by norm_num)
theorem B2061363 : Blo 2059435 2061363 := bstep (se 1 (by rfl) ⟨1546022, by rfl⟩ : syracuseStep 2061363 = 3092045) B3092045
theorem B4638077 : Blo 2059435 4638077 := bbase (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) (by norm_num)
theorem B3092051 : Blo 2059435 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B2061367 : Blo 2059435 2061367 := bstep (se 1 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 2061367 = 3092051) B3092051
theorem B3478565 : Blo 2059435 3478565 := bbase (se 4 (by rfl) ⟨326115, by rfl⟩ : syracuseStep 3478565 = 652231) (by norm_num)
theorem B2319043 : Blo 2059435 2319043 := bstep (se 1 (by rfl) ⟨1739282, by rfl⟩ : syracuseStep 2319043 = 3478565) B3478565
theorem B3092057 : Blo 2059435 3092057 := bstep (se 2 (by rfl) ⟨1159521, by rfl⟩ : syracuseStep 3092057 = 2319043) B2319043
theorem B2061371 : Blo 2059435 2061371 := bstep (se 1 (by rfl) ⟨1546028, by rfl⟩ : syracuseStep 2061371 = 3092057) B3092057
theorem B2935045 : Blo 2059435 2935045 := bbase (se 4 (by rfl) ⟨275160, by rfl⟩ : syracuseStep 2935045 = 550321) (by norm_num)
theorem B15653573 : Blo 2059435 15653573 := bstep (se 4 (by rfl) ⟨1467522, by rfl⟩ : syracuseStep 15653573 = 2935045) B2935045
theorem B10435715 : Blo 2059435 10435715 := bstep (se 1 (by rfl) ⟨7826786, by rfl⟩ : syracuseStep 10435715 = 15653573) B15653573
theorem B6957143 : Blo 2059435 6957143 := bstep (se 1 (by rfl) ⟨5217857, by rfl⟩ : syracuseStep 6957143 = 10435715) B10435715
theorem B4638095 : Blo 2059435 4638095 := bstep (se 1 (by rfl) ⟨3478571, by rfl⟩ : syracuseStep 4638095 = 6957143) B6957143
theorem B3092063 : Blo 2059435 3092063 := bstep (se 1 (by rfl) ⟨2319047, by rfl⟩ : syracuseStep 3092063 = 4638095) B4638095
theorem B2061375 : Blo 2059435 2061375 := bstep (se 1 (by rfl) ⟨1546031, by rfl⟩ : syracuseStep 2061375 = 3092063) B3092063
theorem B3092069 : Blo 2059435 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B2061379 : Blo 2059435 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B2201293 : Blo 2059435 2201293 := bbase (se 3 (by rfl) ⟨412742, by rfl⟩ : syracuseStep 2201293 = 825485) (by norm_num)
theorem B2935057 : Blo 2059435 2935057 := bstep (se 2 (by rfl) ⟨1100646, by rfl⟩ : syracuseStep 2935057 = 2201293) B2201293
theorem B3913409 : Blo 2059435 3913409 := bstep (se 2 (by rfl) ⟨1467528, by rfl⟩ : syracuseStep 3913409 = 2935057) B2935057
theorem B2608939 : Blo 2059435 2608939 := bstep (se 1 (by rfl) ⟨1956704, by rfl⟩ : syracuseStep 2608939 = 3913409) B3913409
theorem B3478585 : Blo 2059435 3478585 := bstep (se 2 (by rfl) ⟨1304469, by rfl⟩ : syracuseStep 3478585 = 2608939) B2608939
theorem B4638113 : Blo 2059435 4638113 := bstep (se 2 (by rfl) ⟨1739292, by rfl⟩ : syracuseStep 4638113 = 3478585) B3478585
theorem B3092075 : Blo 2059435 3092075 := bstep (se 1 (by rfl) ⟨2319056, by rfl⟩ : syracuseStep 3092075 = 4638113) B4638113
theorem B2061383 : Blo 2059435 2061383 := bstep (se 1 (by rfl) ⟨1546037, by rfl⟩ : syracuseStep 2061383 = 3092075) B3092075
theorem B2319061 : Blo 2059435 2319061 := bbase (se 7 (by rfl) ⟨27176, by rfl⟩ : syracuseStep 2319061 = 54353) (by norm_num)
theorem B3092081 : Blo 2059435 3092081 := bstep (se 2 (by rfl) ⟨1159530, by rfl⟩ : syracuseStep 3092081 = 2319061) B2319061
theorem B2061387 : Blo 2059435 2061387 := bstep (se 1 (by rfl) ⟨1546040, by rfl⟩ : syracuseStep 2061387 = 3092081) B3092081
theorem B2608949 : Blo 2059435 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B6957197 : Blo 2059435 6957197 := bstep (se 3 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 6957197 = 2608949) B2608949
theorem B4638131 : Blo 2059435 4638131 := bstep (se 1 (by rfl) ⟨3478598, by rfl⟩ : syracuseStep 4638131 = 6957197) B6957197
theorem B3092087 : Blo 2059435 3092087 := bstep (se 1 (by rfl) ⟨2319065, by rfl⟩ : syracuseStep 3092087 = 4638131) B4638131
theorem B2061391 : Blo 2059435 2061391 := bstep (se 1 (by rfl) ⟨1546043, by rfl⟩ : syracuseStep 2061391 = 3092087) B3092087
theorem B3092093 : Blo 2059435 3092093 := bbase (se 3 (by rfl) ⟨579767, by rfl⟩ : syracuseStep 3092093 = 1159535) (by norm_num)
theorem B2061395 : Blo 2059435 2061395 := bstep (se 1 (by rfl) ⟨1546046, by rfl⟩ : syracuseStep 2061395 = 3092093) B3092093
theorem B4638149 : Blo 2059435 4638149 := bbase (se 4 (by rfl) ⟨434826, by rfl⟩ : syracuseStep 4638149 = 869653) (by norm_num)
theorem B3092099 : Blo 2059435 3092099 := bstep (se 1 (by rfl) ⟨2319074, by rfl⟩ : syracuseStep 3092099 = 4638149) B4638149
theorem B2061399 : Blo 2059435 2061399 := bstep (se 1 (by rfl) ⟨1546049, by rfl⟩ : syracuseStep 2061399 = 3092099) B3092099
theorem B4236077 : Blo 2059435 4236077 := bbase (se 3 (by rfl) ⟨794264, by rfl⟩ : syracuseStep 4236077 = 1588529) (by norm_num)
theorem B11296205 : Blo 2059435 11296205 := bstep (se 3 (by rfl) ⟨2118038, by rfl⟩ : syracuseStep 11296205 = 4236077) B4236077
theorem B7530803 : Blo 2059435 7530803 := bstep (se 1 (by rfl) ⟨5648102, by rfl⟩ : syracuseStep 7530803 = 11296205) B11296205
theorem B5020535 : Blo 2059435 5020535 := bstep (se 1 (by rfl) ⟨3765401, by rfl⟩ : syracuseStep 5020535 = 7530803) B7530803
theorem B3347023 : Blo 2059435 3347023 := bstep (se 1 (by rfl) ⟨2510267, by rfl⟩ : syracuseStep 3347023 = 5020535) B5020535
theorem B4462697 : Blo 2059435 4462697 := bstep (se 2 (by rfl) ⟨1673511, by rfl⟩ : syracuseStep 4462697 = 3347023) B3347023
theorem B2975131 : Blo 2059435 2975131 := bstep (se 1 (by rfl) ⟨2231348, by rfl⟩ : syracuseStep 2975131 = 4462697) B4462697
theorem B3966841 : Blo 2059435 3966841 := bstep (se 2 (by rfl) ⟨1487565, by rfl⟩ : syracuseStep 3966841 = 2975131) B2975131
theorem B5289121 : Blo 2059435 5289121 := bstep (se 2 (by rfl) ⟨1983420, by rfl⟩ : syracuseStep 5289121 = 3966841) B3966841
theorem B28208645 : Blo 2059435 28208645 := bstep (se 4 (by rfl) ⟨2644560, by rfl⟩ : syracuseStep 28208645 = 5289121) B5289121
theorem B18805763 : Blo 2059435 18805763 := bstep (se 1 (by rfl) ⟨14104322, by rfl⟩ : syracuseStep 18805763 = 28208645) B28208645
theorem B12537175 : Blo 2059435 12537175 := bstep (se 1 (by rfl) ⟨9402881, by rfl⟩ : syracuseStep 12537175 = 18805763) B18805763
theorem B16716233 : Blo 2059435 16716233 := bstep (se 2 (by rfl) ⟨6268587, by rfl⟩ : syracuseStep 16716233 = 12537175) B12537175
theorem B11144155 : Blo 2059435 11144155 := bstep (se 1 (by rfl) ⟨8358116, by rfl⟩ : syracuseStep 11144155 = 16716233) B16716233
theorem B14858873 : Blo 2059435 14858873 := bstep (se 2 (by rfl) ⟨5572077, by rfl⟩ : syracuseStep 14858873 = 11144155) B11144155
theorem B9905915 : Blo 2059435 9905915 := bstep (se 1 (by rfl) ⟨7429436, by rfl⟩ : syracuseStep 9905915 = 14858873) B14858873
theorem B6603943 : Blo 2059435 6603943 := bstep (se 1 (by rfl) ⟨4952957, by rfl⟩ : syracuseStep 6603943 = 9905915) B9905915
theorem B8805257 : Blo 2059435 8805257 := bstep (se 2 (by rfl) ⟨3301971, by rfl⟩ : syracuseStep 8805257 = 6603943) B6603943
theorem B5870171 : Blo 2059435 5870171 := bstep (se 1 (by rfl) ⟨4402628, by rfl⟩ : syracuseStep 5870171 = 8805257) B8805257
theorem B3913447 : Blo 2059435 3913447 := bstep (se 1 (by rfl) ⟨2935085, by rfl⟩ : syracuseStep 3913447 = 5870171) B5870171
theorem B5217929 : Blo 2059435 5217929 := bstep (se 2 (by rfl) ⟨1956723, by rfl⟩ : syracuseStep 5217929 = 3913447) B3913447
theorem B3478619 : Blo 2059435 3478619 := bstep (se 1 (by rfl) ⟨2608964, by rfl⟩ : syracuseStep 3478619 = 5217929) B5217929
theorem B2319079 : Blo 2059435 2319079 := bstep (se 1 (by rfl) ⟨1739309, by rfl⟩ : syracuseStep 2319079 = 3478619) B3478619
theorem B3092105 : Blo 2059435 3092105 := bstep (se 2 (by rfl) ⟨1159539, by rfl⟩ : syracuseStep 3092105 = 2319079) B2319079
theorem B2061403 : Blo 2059435 2061403 := bstep (se 1 (by rfl) ⟨1546052, by rfl⟩ : syracuseStep 2061403 = 3092105) B3092105
theorem B10435877 : Blo 2059435 10435877 := bbase (se 4 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 10435877 = 1956727) (by norm_num)
theorem B6957251 : Blo 2059435 6957251 := bstep (se 1 (by rfl) ⟨5217938, by rfl⟩ : syracuseStep 6957251 = 10435877) B10435877
theorem B4638167 : Blo 2059435 4638167 := bstep (se 1 (by rfl) ⟨3478625, by rfl⟩ : syracuseStep 4638167 = 6957251) B6957251
theorem B3092111 : Blo 2059435 3092111 := bstep (se 1 (by rfl) ⟨2319083, by rfl⟩ : syracuseStep 3092111 = 4638167) B4638167
theorem B2061407 : Blo 2059435 2061407 := bstep (se 1 (by rfl) ⟨1546055, by rfl⟩ : syracuseStep 2061407 = 3092111) B3092111
theorem B3092117 : Blo 2059435 3092117 := bbase (se 6 (by rfl) ⟨72471, by rfl⟩ : syracuseStep 3092117 = 144943) (by norm_num)
theorem B2061411 : Blo 2059435 2061411 := bstep (se 1 (by rfl) ⟨1546058, by rfl⟩ : syracuseStep 2061411 = 3092117) B3092117
theorem B2089541 : Blo 2059435 2089541 := bbase (se 4 (by rfl) ⟨195894, by rfl⟩ : syracuseStep 2089541 = 391789) (by norm_num)
theorem B5572109 : Blo 2059435 5572109 := bstep (se 3 (by rfl) ⟨1044770, by rfl⟩ : syracuseStep 5572109 = 2089541) B2089541
theorem B14858957 : Blo 2059435 14858957 := bstep (se 3 (by rfl) ⟨2786054, by rfl⟩ : syracuseStep 14858957 = 5572109) B5572109
theorem B9905971 : Blo 2059435 9905971 := bstep (se 1 (by rfl) ⟨7429478, by rfl⟩ : syracuseStep 9905971 = 14858957) B14858957
theorem B13207961 : Blo 2059435 13207961 := bstep (se 2 (by rfl) ⟨4952985, by rfl⟩ : syracuseStep 13207961 = 9905971) B9905971
theorem B8805307 : Blo 2059435 8805307 := bstep (se 1 (by rfl) ⟨6603980, by rfl⟩ : syracuseStep 8805307 = 13207961) B13207961
theorem B11740409 : Blo 2059435 11740409 := bstep (se 2 (by rfl) ⟨4402653, by rfl⟩ : syracuseStep 11740409 = 8805307) B8805307
theorem B7826939 : Blo 2059435 7826939 := bstep (se 1 (by rfl) ⟨5870204, by rfl⟩ : syracuseStep 7826939 = 11740409) B11740409
theorem B5217959 : Blo 2059435 5217959 := bstep (se 1 (by rfl) ⟨3913469, by rfl⟩ : syracuseStep 5217959 = 7826939) B7826939
theorem B3478639 : Blo 2059435 3478639 := bstep (se 1 (by rfl) ⟨2608979, by rfl⟩ : syracuseStep 3478639 = 5217959) B5217959
theorem B4638185 : Blo 2059435 4638185 := bstep (se 2 (by rfl) ⟨1739319, by rfl⟩ : syracuseStep 4638185 = 3478639) B3478639
theorem B3092123 : Blo 2059435 3092123 := bstep (se 1 (by rfl) ⟨2319092, by rfl⟩ : syracuseStep 3092123 = 4638185) B4638185
theorem B2061415 : Blo 2059435 2061415 := bstep (se 1 (by rfl) ⟨1546061, by rfl⟩ : syracuseStep 2061415 = 3092123) B3092123
theorem B2319097 : Blo 2059435 2319097 := bbase (se 2 (by rfl) ⟨869661, by rfl⟩ : syracuseStep 2319097 = 1739323) (by norm_num)
theorem B3092129 : Blo 2059435 3092129 := bstep (se 2 (by rfl) ⟨1159548, by rfl⟩ : syracuseStep 3092129 = 2319097) B2319097
theorem B2061419 : Blo 2059435 2061419 := bstep (se 1 (by rfl) ⟨1546064, by rfl⟩ : syracuseStep 2061419 = 3092129) B3092129
theorem B4953005 : Blo 2059435 4953005 := bbase (se 3 (by rfl) ⟨928688, by rfl⟩ : syracuseStep 4953005 = 1857377) (by norm_num)
theorem B3302003 : Blo 2059435 3302003 := bstep (se 1 (by rfl) ⟨2476502, by rfl⟩ : syracuseStep 3302003 = 4953005) B4953005
theorem B8805341 : Blo 2059435 8805341 := bstep (se 3 (by rfl) ⟨1651001, by rfl⟩ : syracuseStep 8805341 = 3302003) B3302003
theorem B5870227 : Blo 2059435 5870227 := bstep (se 1 (by rfl) ⟨4402670, by rfl⟩ : syracuseStep 5870227 = 8805341) B8805341
theorem B7826969 : Blo 2059435 7826969 := bstep (se 2 (by rfl) ⟨2935113, by rfl⟩ : syracuseStep 7826969 = 5870227) B5870227
theorem B5217979 : Blo 2059435 5217979 := bstep (se 1 (by rfl) ⟨3913484, by rfl⟩ : syracuseStep 5217979 = 7826969) B7826969
theorem B6957305 : Blo 2059435 6957305 := bstep (se 2 (by rfl) ⟨2608989, by rfl⟩ : syracuseStep 6957305 = 5217979) B5217979
theorem B4638203 : Blo 2059435 4638203 := bstep (se 1 (by rfl) ⟨3478652, by rfl⟩ : syracuseStep 4638203 = 6957305) B6957305
theorem B3092135 : Blo 2059435 3092135 := bstep (se 1 (by rfl) ⟨2319101, by rfl⟩ : syracuseStep 3092135 = 4638203) B4638203
theorem B2061423 : Blo 2059435 2061423 := bstep (se 1 (by rfl) ⟨1546067, by rfl⟩ : syracuseStep 2061423 = 3092135) B3092135
theorem B3092141 : Blo 2059435 3092141 := bbase (se 3 (by rfl) ⟨579776, by rfl⟩ : syracuseStep 3092141 = 1159553) (by norm_num)
theorem B2061427 : Blo 2059435 2061427 := bstep (se 1 (by rfl) ⟨1546070, by rfl⟩ : syracuseStep 2061427 = 3092141) B3092141
theorem B4638221 : Blo 2059435 4638221 := bbase (se 3 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 4638221 = 1739333) (by norm_num)
theorem B3092147 : Blo 2059435 3092147 := bstep (se 1 (by rfl) ⟨2319110, by rfl⟩ : syracuseStep 3092147 = 4638221) B4638221
theorem B2061431 : Blo 2059435 2061431 := bstep (se 1 (by rfl) ⟨1546073, by rfl⟩ : syracuseStep 2061431 = 3092147) B3092147
theorem B2609005 : Blo 2059435 2609005 := bbase (se 3 (by rfl) ⟨489188, by rfl⟩ : syracuseStep 2609005 = 978377) (by norm_num)
theorem B3478673 : Blo 2059435 3478673 := bstep (se 2 (by rfl) ⟨1304502, by rfl⟩ : syracuseStep 3478673 = 2609005) B2609005
theorem B2319115 : Blo 2059435 2319115 := bstep (se 1 (by rfl) ⟨1739336, by rfl⟩ : syracuseStep 2319115 = 3478673) B3478673
theorem B3092153 : Blo 2059435 3092153 := bstep (se 2 (by rfl) ⟨1159557, by rfl⟩ : syracuseStep 3092153 = 2319115) B2319115
theorem B2061435 : Blo 2059435 2061435 := bstep (se 1 (by rfl) ⟨1546076, by rfl⟩ : syracuseStep 2061435 = 3092153) B3092153
theorem C0 (j : ℕ) (h1 : 514858 ≤ j) (h2 : j ≤ 515358) : Blo 2059435 (4 * j + 3) := by
  interval_cases j
  · exact B2059435
  · exact B2059439
  · exact B2059443
  · exact B2059447
  · exact B2059451
  · exact B2059455
  · exact B2059459
  · exact B2059463
  · exact B2059467
  · exact B2059471
  · exact B2059475
  · exact B2059479
  · exact B2059483
  · exact B2059487
  · exact B2059491
  · exact B2059495
  · exact B2059499
  · exact B2059503
  · exact B2059507
  · exact B2059511
  · exact B2059515
  · exact B2059519
  · exact B2059523
  · exact B2059527
  · exact B2059531
  · exact B2059535
  · exact B2059539
  · exact B2059543
  · exact B2059547
  · exact B2059551
  · exact B2059555
  · exact B2059559
  · exact B2059563
  · exact B2059567
  · exact B2059571
  · exact B2059575
  · exact B2059579
  · exact B2059583
  · exact B2059587
  · exact B2059591
  · exact B2059595
  · exact B2059599
  · exact B2059603
  · exact B2059607
  · exact B2059611
  · exact B2059615
  · exact B2059619
  · exact B2059623
  · exact B2059627
  · exact B2059631
  · exact B2059635
  · exact B2059639
  · exact B2059643
  · exact B2059647
  · exact B2059651
  · exact B2059655
  · exact B2059659
  · exact B2059663
  · exact B2059667
  · exact B2059671
  · exact B2059675
  · exact B2059679
  · exact B2059683
  · exact B2059687
  · exact B2059691
  · exact B2059695
  · exact B2059699
  · exact B2059703
  · exact B2059707
  · exact B2059711
  · exact B2059715
  · exact B2059719
  · exact B2059723
  · exact B2059727
  · exact B2059731
  · exact B2059735
  · exact B2059739
  · exact B2059743
  · exact B2059747
  · exact B2059751
  · exact B2059755
  · exact B2059759
  · exact B2059763
  · exact B2059767
  · exact B2059771
  · exact B2059775
  · exact B2059779
  · exact B2059783
  · exact B2059787
  · exact B2059791
  · exact B2059795
  · exact B2059799
  · exact B2059803
  · exact B2059807
  · exact B2059811
  · exact B2059815
  · exact B2059819
  · exact B2059823
  · exact B2059827
  · exact B2059831
  · exact B2059835
  · exact B2059839
  · exact B2059843
  · exact B2059847
  · exact B2059851
  · exact B2059855
  · exact B2059859
  · exact B2059863
  · exact B2059867
  · exact B2059871
  · exact B2059875
  · exact B2059879
  · exact B2059883
  · exact B2059887
  · exact B2059891
  · exact B2059895
  · exact B2059899
  · exact B2059903
  · exact B2059907
  · exact B2059911
  · exact B2059915
  · exact B2059919
  · exact B2059923
  · exact B2059927
  · exact B2059931
  · exact B2059935
  · exact B2059939
  · exact B2059943
  · exact B2059947
  · exact B2059951
  · exact B2059955
  · exact B2059959
  · exact B2059963
  · exact B2059967
  · exact B2059971
  · exact B2059975
  · exact B2059979
  · exact B2059983
  · exact B2059987
  · exact B2059991
  · exact B2059995
  · exact B2059999
  · exact B2060003
  · exact B2060007
  · exact B2060011
  · exact B2060015
  · exact B2060019
  · exact B2060023
  · exact B2060027
  · exact B2060031
  · exact B2060035
  · exact B2060039
  · exact B2060043
  · exact B2060047
  · exact B2060051
  · exact B2060055
  · exact B2060059
  · exact B2060063
  · exact B2060067
  · exact B2060071
  · exact B2060075
  · exact B2060079
  · exact B2060083
  · exact B2060087
  · exact B2060091
  · exact B2060095
  · exact B2060099
  · exact B2060103
  · exact B2060107
  · exact B2060111
  · exact B2060115
  · exact B2060119
  · exact B2060123
  · exact B2060127
  · exact B2060131
  · exact B2060135
  · exact B2060139
  · exact B2060143
  · exact B2060147
  · exact B2060151
  · exact B2060155
  · exact B2060159
  · exact B2060163
  · exact B2060167
  · exact B2060171
  · exact B2060175
  · exact B2060179
  · exact B2060183
  · exact B2060187
  · exact B2060191
  · exact B2060195
  · exact B2060199
  · exact B2060203
  · exact B2060207
  · exact B2060211
  · exact B2060215
  · exact B2060219
  · exact B2060223
  · exact B2060227
  · exact B2060231
  · exact B2060235
  · exact B2060239
  · exact B2060243
  · exact B2060247
  · exact B2060251
  · exact B2060255
  · exact B2060259
  · exact B2060263
  · exact B2060267
  · exact B2060271
  · exact B2060275
  · exact B2060279
  · exact B2060283
  · exact B2060287
  · exact B2060291
  · exact B2060295
  · exact B2060299
  · exact B2060303
  · exact B2060307
  · exact B2060311
  · exact B2060315
  · exact B2060319
  · exact B2060323
  · exact B2060327
  · exact B2060331
  · exact B2060335
  · exact B2060339
  · exact B2060343
  · exact B2060347
  · exact B2060351
  · exact B2060355
  · exact B2060359
  · exact B2060363
  · exact B2060367
  · exact B2060371
  · exact B2060375
  · exact B2060379
  · exact B2060383
  · exact B2060387
  · exact B2060391
  · exact B2060395
  · exact B2060399
  · exact B2060403
  · exact B2060407
  · exact B2060411
  · exact B2060415
  · exact B2060419
  · exact B2060423
  · exact B2060427
  · exact B2060431
  · exact B2060435
  · exact B2060439
  · exact B2060443
  · exact B2060447
  · exact B2060451
  · exact B2060455
  · exact B2060459
  · exact B2060463
  · exact B2060467
  · exact B2060471
  · exact B2060475
  · exact B2060479
  · exact B2060483
  · exact B2060487
  · exact B2060491
  · exact B2060495
  · exact B2060499
  · exact B2060503
  · exact B2060507
  · exact B2060511
  · exact B2060515
  · exact B2060519
  · exact B2060523
  · exact B2060527
  · exact B2060531
  · exact B2060535
  · exact B2060539
  · exact B2060543
  · exact B2060547
  · exact B2060551
  · exact B2060555
  · exact B2060559
  · exact B2060563
  · exact B2060567
  · exact B2060571
  · exact B2060575
  · exact B2060579
  · exact B2060583
  · exact B2060587
  · exact B2060591
  · exact B2060595
  · exact B2060599
  · exact B2060603
  · exact B2060607
  · exact B2060611
  · exact B2060615
  · exact B2060619
  · exact B2060623
  · exact B2060627
  · exact B2060631
  · exact B2060635
  · exact B2060639
  · exact B2060643
  · exact B2060647
  · exact B2060651
  · exact B2060655
  · exact B2060659
  · exact B2060663
  · exact B2060667
  · exact B2060671
  · exact B2060675
  · exact B2060679
  · exact B2060683
  · exact B2060687
  · exact B2060691
  · exact B2060695
  · exact B2060699
  · exact B2060703
  · exact B2060707
  · exact B2060711
  · exact B2060715
  · exact B2060719
  · exact B2060723
  · exact B2060727
  · exact B2060731
  · exact B2060735
  · exact B2060739
  · exact B2060743
  · exact B2060747
  · exact B2060751
  · exact B2060755
  · exact B2060759
  · exact B2060763
  · exact B2060767
  · exact B2060771
  · exact B2060775
  · exact B2060779
  · exact B2060783
  · exact B2060787
  · exact B2060791
  · exact B2060795
  · exact B2060799
  · exact B2060803
  · exact B2060807
  · exact B2060811
  · exact B2060815
  · exact B2060819
  · exact B2060823
  · exact B2060827
  · exact B2060831
  · exact B2060835
  · exact B2060839
  · exact B2060843
  · exact B2060847
  · exact B2060851
  · exact B2060855
  · exact B2060859
  · exact B2060863
  · exact B2060867
  · exact B2060871
  · exact B2060875
  · exact B2060879
  · exact B2060883
  · exact B2060887
  · exact B2060891
  · exact B2060895
  · exact B2060899
  · exact B2060903
  · exact B2060907
  · exact B2060911
  · exact B2060915
  · exact B2060919
  · exact B2060923
  · exact B2060927
  · exact B2060931
  · exact B2060935
  · exact B2060939
  · exact B2060943
  · exact B2060947
  · exact B2060951
  · exact B2060955
  · exact B2060959
  · exact B2060963
  · exact B2060967
  · exact B2060971
  · exact B2060975
  · exact B2060979
  · exact B2060983
  · exact B2060987
  · exact B2060991
  · exact B2060995
  · exact B2060999
  · exact B2061003
  · exact B2061007
  · exact B2061011
  · exact B2061015
  · exact B2061019
  · exact B2061023
  · exact B2061027
  · exact B2061031
  · exact B2061035
  · exact B2061039
  · exact B2061043
  · exact B2061047
  · exact B2061051
  · exact B2061055
  · exact B2061059
  · exact B2061063
  · exact B2061067
  · exact B2061071
  · exact B2061075
  · exact B2061079
  · exact B2061083
  · exact B2061087
  · exact B2061091
  · exact B2061095
  · exact B2061099
  · exact B2061103
  · exact B2061107
  · exact B2061111
  · exact B2061115
  · exact B2061119
  · exact B2061123
  · exact B2061127
  · exact B2061131
  · exact B2061135
  · exact B2061139
  · exact B2061143
  · exact B2061147
  · exact B2061151
  · exact B2061155
  · exact B2061159
  · exact B2061163
  · exact B2061167
  · exact B2061171
  · exact B2061175
  · exact B2061179
  · exact B2061183
  · exact B2061187
  · exact B2061191
  · exact B2061195
  · exact B2061199
  · exact B2061203
  · exact B2061207
  · exact B2061211
  · exact B2061215
  · exact B2061219
  · exact B2061223
  · exact B2061227
  · exact B2061231
  · exact B2061235
  · exact B2061239
  · exact B2061243
  · exact B2061247
  · exact B2061251
  · exact B2061255
  · exact B2061259
  · exact B2061263
  · exact B2061267
  · exact B2061271
  · exact B2061275
  · exact B2061279
  · exact B2061283
  · exact B2061287
  · exact B2061291
  · exact B2061295
  · exact B2061299
  · exact B2061303
  · exact B2061307
  · exact B2061311
  · exact B2061315
  · exact B2061319
  · exact B2061323
  · exact B2061327
  · exact B2061331
  · exact B2061335
  · exact B2061339
  · exact B2061343
  · exact B2061347
  · exact B2061351
  · exact B2061355
  · exact B2061359
  · exact B2061363
  · exact B2061367
  · exact B2061371
  · exact B2061375
  · exact B2061379
  · exact B2061383
  · exact B2061387
  · exact B2061391
  · exact B2061395
  · exact B2061399
  · exact B2061403
  · exact B2061407
  · exact B2061411
  · exact B2061415
  · exact B2061419
  · exact B2061423
  · exact B2061427
  · exact B2061431
  · exact B2061435
theorem solution (m : ℕ) (hlo : 2059435 ≤ m) (hhi : m ≤ 2061435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 514858 ≤ j := by omega
    have hj2 : j ≤ 515358 := by omega
    have hb : Blo 2059435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
