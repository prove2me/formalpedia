-- Prove2me | solution 1 for syracuse_descends_range_2159435_2161435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:36.034063+00:00
-- url     : https://prove2.me/submissions/0f5f9689-b624-4268-ac27-e492b5844c98

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

theorem B2429365 : Blo 2159435 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B3239153 : Blo 2159435 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B2159435 : Blo 2159435 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem B2733041 : Blo 2159435 2733041 := bbase (se 2 (by rfl) ⟨1024890, by rfl⟩ : syracuseStep 2733041 = 2049781) (by norm_num)
theorem B7288109 : Blo 2159435 7288109 := bstep (se 3 (by rfl) ⟨1366520, by rfl⟩ : syracuseStep 7288109 = 2733041) B2733041
theorem B4858739 : Blo 2159435 4858739 := bstep (se 1 (by rfl) ⟨3644054, by rfl⟩ : syracuseStep 4858739 = 7288109) B7288109
theorem B3239159 : Blo 2159435 3239159 := bstep (se 1 (by rfl) ⟨2429369, by rfl⟩ : syracuseStep 3239159 = 4858739) B4858739
theorem B2159439 : Blo 2159435 2159439 := bstep (se 1 (by rfl) ⟨1619579, by rfl⟩ : syracuseStep 2159439 = 3239159) B3239159
theorem B3239165 : Blo 2159435 3239165 := bbase (se 3 (by rfl) ⟨607343, by rfl⟩ : syracuseStep 3239165 = 1214687) (by norm_num)
theorem B2159443 : Blo 2159435 2159443 := bstep (se 1 (by rfl) ⟨1619582, by rfl⟩ : syracuseStep 2159443 = 3239165) B3239165
theorem B4858757 : Blo 2159435 4858757 := bbase (se 4 (by rfl) ⟨455508, by rfl⟩ : syracuseStep 4858757 = 911017) (by norm_num)
theorem B3239171 : Blo 2159435 3239171 := bstep (se 1 (by rfl) ⟨2429378, by rfl⟩ : syracuseStep 3239171 = 4858757) B4858757
theorem B2159447 : Blo 2159435 2159447 := bstep (se 1 (by rfl) ⟨1619585, by rfl⟩ : syracuseStep 2159447 = 3239171) B3239171
theorem B2306017 : Blo 2159435 2306017 := bbase (se 2 (by rfl) ⟨864756, by rfl⟩ : syracuseStep 2306017 = 1729513) (by norm_num)
theorem B3074689 : Blo 2159435 3074689 := bstep (se 2 (by rfl) ⟨1153008, by rfl⟩ : syracuseStep 3074689 = 2306017) B2306017
theorem B4099585 : Blo 2159435 4099585 := bstep (se 2 (by rfl) ⟨1537344, by rfl⟩ : syracuseStep 4099585 = 3074689) B3074689
theorem B5466113 : Blo 2159435 5466113 := bstep (se 2 (by rfl) ⟨2049792, by rfl⟩ : syracuseStep 5466113 = 4099585) B4099585
theorem B3644075 : Blo 2159435 3644075 := bstep (se 1 (by rfl) ⟨2733056, by rfl⟩ : syracuseStep 3644075 = 5466113) B5466113
theorem B2429383 : Blo 2159435 2429383 := bstep (se 1 (by rfl) ⟨1822037, by rfl⟩ : syracuseStep 2429383 = 3644075) B3644075
theorem B3239177 : Blo 2159435 3239177 := bstep (se 2 (by rfl) ⟨1214691, by rfl⟩ : syracuseStep 3239177 = 2429383) B2429383
theorem B2159451 : Blo 2159435 2159451 := bstep (se 1 (by rfl) ⟨1619588, by rfl⟩ : syracuseStep 2159451 = 3239177) B3239177
theorem B10932245 : Blo 2159435 10932245 := bbase (se 6 (by rfl) ⟨256224, by rfl⟩ : syracuseStep 10932245 = 512449) (by norm_num)
theorem B7288163 : Blo 2159435 7288163 := bstep (se 1 (by rfl) ⟨5466122, by rfl⟩ : syracuseStep 7288163 = 10932245) B10932245
theorem B4858775 : Blo 2159435 4858775 := bstep (se 1 (by rfl) ⟨3644081, by rfl⟩ : syracuseStep 4858775 = 7288163) B7288163
theorem B3239183 : Blo 2159435 3239183 := bstep (se 1 (by rfl) ⟨2429387, by rfl⟩ : syracuseStep 3239183 = 4858775) B4858775
theorem B2159455 : Blo 2159435 2159455 := bstep (se 1 (by rfl) ⟨1619591, by rfl⟩ : syracuseStep 2159455 = 3239183) B3239183
theorem B3239189 : Blo 2159435 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B2159459 : Blo 2159435 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B4377853 : Blo 2159435 4377853 := bbase (se 3 (by rfl) ⟨820847, by rfl⟩ : syracuseStep 4377853 = 1641695) (by norm_num)
theorem B23348549 : Blo 2159435 23348549 := bstep (se 4 (by rfl) ⟨2188926, by rfl⟩ : syracuseStep 23348549 = 4377853) B4377853
theorem B15565699 : Blo 2159435 15565699 := bstep (se 1 (by rfl) ⟨11674274, by rfl⟩ : syracuseStep 15565699 = 23348549) B23348549
theorem B20754265 : Blo 2159435 20754265 := bstep (se 2 (by rfl) ⟨7782849, by rfl⟩ : syracuseStep 20754265 = 15565699) B15565699
theorem B27672353 : Blo 2159435 27672353 := bstep (se 2 (by rfl) ⟨10377132, by rfl⟩ : syracuseStep 27672353 = 20754265) B20754265
theorem B18448235 : Blo 2159435 18448235 := bstep (se 1 (by rfl) ⟨13836176, by rfl⟩ : syracuseStep 18448235 = 27672353) B27672353
theorem B12298823 : Blo 2159435 12298823 := bstep (se 1 (by rfl) ⟨9224117, by rfl⟩ : syracuseStep 12298823 = 18448235) B18448235
theorem B8199215 : Blo 2159435 8199215 := bstep (se 1 (by rfl) ⟨6149411, by rfl⟩ : syracuseStep 8199215 = 12298823) B12298823
theorem B5466143 : Blo 2159435 5466143 := bstep (se 1 (by rfl) ⟨4099607, by rfl⟩ : syracuseStep 5466143 = 8199215) B8199215
theorem B3644095 : Blo 2159435 3644095 := bstep (se 1 (by rfl) ⟨2733071, by rfl⟩ : syracuseStep 3644095 = 5466143) B5466143
theorem B4858793 : Blo 2159435 4858793 := bstep (se 2 (by rfl) ⟨1822047, by rfl⟩ : syracuseStep 4858793 = 3644095) B3644095
theorem B3239195 : Blo 2159435 3239195 := bstep (se 1 (by rfl) ⟨2429396, by rfl⟩ : syracuseStep 3239195 = 4858793) B4858793
theorem B2159463 : Blo 2159435 2159463 := bstep (se 1 (by rfl) ⟨1619597, by rfl⟩ : syracuseStep 2159463 = 3239195) B3239195
theorem B2429401 : Blo 2159435 2429401 := bbase (se 2 (by rfl) ⟨911025, by rfl⟩ : syracuseStep 2429401 = 1822051) (by norm_num)
theorem B3239201 : Blo 2159435 3239201 := bstep (se 2 (by rfl) ⟨1214700, by rfl⟩ : syracuseStep 3239201 = 2429401) B2429401
theorem B2159467 : Blo 2159435 2159467 := bstep (se 1 (by rfl) ⟨1619600, by rfl⟩ : syracuseStep 2159467 = 3239201) B3239201
theorem B3074717 : Blo 2159435 3074717 := bbase (se 3 (by rfl) ⟨576509, by rfl⟩ : syracuseStep 3074717 = 1153019) (by norm_num)
theorem B8199245 : Blo 2159435 8199245 := bstep (se 3 (by rfl) ⟨1537358, by rfl⟩ : syracuseStep 8199245 = 3074717) B3074717
theorem B5466163 : Blo 2159435 5466163 := bstep (se 1 (by rfl) ⟨4099622, by rfl⟩ : syracuseStep 5466163 = 8199245) B8199245
theorem B7288217 : Blo 2159435 7288217 := bstep (se 2 (by rfl) ⟨2733081, by rfl⟩ : syracuseStep 7288217 = 5466163) B5466163
theorem B4858811 : Blo 2159435 4858811 := bstep (se 1 (by rfl) ⟨3644108, by rfl⟩ : syracuseStep 4858811 = 7288217) B7288217
theorem B3239207 : Blo 2159435 3239207 := bstep (se 1 (by rfl) ⟨2429405, by rfl⟩ : syracuseStep 3239207 = 4858811) B4858811
theorem B2159471 : Blo 2159435 2159471 := bstep (se 1 (by rfl) ⟨1619603, by rfl⟩ : syracuseStep 2159471 = 3239207) B3239207
theorem B3239213 : Blo 2159435 3239213 := bbase (se 3 (by rfl) ⟨607352, by rfl⟩ : syracuseStep 3239213 = 1214705) (by norm_num)
theorem B2159475 : Blo 2159435 2159475 := bstep (se 1 (by rfl) ⟨1619606, by rfl⟩ : syracuseStep 2159475 = 3239213) B3239213
theorem B4858829 : Blo 2159435 4858829 := bbase (se 3 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 4858829 = 1822061) (by norm_num)
theorem B3239219 : Blo 2159435 3239219 := bstep (se 1 (by rfl) ⟨2429414, by rfl⟩ : syracuseStep 3239219 = 4858829) B4858829
theorem B2159479 : Blo 2159435 2159479 := bstep (se 1 (by rfl) ⟨1619609, by rfl⟩ : syracuseStep 2159479 = 3239219) B3239219
theorem B2733097 : Blo 2159435 2733097 := bbase (se 2 (by rfl) ⟨1024911, by rfl⟩ : syracuseStep 2733097 = 2049823) (by norm_num)
theorem B3644129 : Blo 2159435 3644129 := bstep (se 2 (by rfl) ⟨1366548, by rfl⟩ : syracuseStep 3644129 = 2733097) B2733097
theorem B2429419 : Blo 2159435 2429419 := bstep (se 1 (by rfl) ⟨1822064, by rfl⟩ : syracuseStep 2429419 = 3644129) B3644129
theorem B3239225 : Blo 2159435 3239225 := bstep (se 2 (by rfl) ⟨1214709, by rfl⟩ : syracuseStep 3239225 = 2429419) B2429419
theorem B2159483 : Blo 2159435 2159483 := bstep (se 1 (by rfl) ⟨1619612, by rfl⟩ : syracuseStep 2159483 = 3239225) B3239225
theorem B7996757 : Blo 2159435 7996757 := bbase (se 12 (by rfl) ⟨2928, by rfl⟩ : syracuseStep 7996757 = 5857) (by norm_num)
theorem B85298741 : Blo 2159435 85298741 := bstep (se 5 (by rfl) ⟨3998378, by rfl⟩ : syracuseStep 85298741 = 7996757) B7996757
theorem B56865827 : Blo 2159435 56865827 := bstep (se 1 (by rfl) ⟨42649370, by rfl⟩ : syracuseStep 56865827 = 85298741) B85298741
theorem B37910551 : Blo 2159435 37910551 := bstep (se 1 (by rfl) ⟨28432913, by rfl⟩ : syracuseStep 37910551 = 56865827) B56865827
theorem B50547401 : Blo 2159435 50547401 := bstep (se 2 (by rfl) ⟨18955275, by rfl⟩ : syracuseStep 50547401 = 37910551) B37910551
theorem B33698267 : Blo 2159435 33698267 := bstep (se 1 (by rfl) ⟨25273700, by rfl⟩ : syracuseStep 33698267 = 50547401) B50547401
theorem B22465511 : Blo 2159435 22465511 := bstep (se 1 (by rfl) ⟨16849133, by rfl⟩ : syracuseStep 22465511 = 33698267) B33698267
theorem B14977007 : Blo 2159435 14977007 := bstep (se 1 (by rfl) ⟨11232755, by rfl⟩ : syracuseStep 14977007 = 22465511) B22465511
theorem B9984671 : Blo 2159435 9984671 := bstep (se 1 (by rfl) ⟨7488503, by rfl⟩ : syracuseStep 9984671 = 14977007) B14977007
theorem B6656447 : Blo 2159435 6656447 := bstep (se 1 (by rfl) ⟨4992335, by rfl⟩ : syracuseStep 6656447 = 9984671) B9984671
theorem B4437631 : Blo 2159435 4437631 := bstep (se 1 (by rfl) ⟨3328223, by rfl⟩ : syracuseStep 4437631 = 6656447) B6656447
theorem B23667365 : Blo 2159435 23667365 := bstep (se 4 (by rfl) ⟨2218815, by rfl⟩ : syracuseStep 23667365 = 4437631) B4437631
theorem B15778243 : Blo 2159435 15778243 := bstep (se 1 (by rfl) ⟨11833682, by rfl⟩ : syracuseStep 15778243 = 23667365) B23667365
theorem B21037657 : Blo 2159435 21037657 := bstep (se 2 (by rfl) ⟨7889121, by rfl⟩ : syracuseStep 21037657 = 15778243) B15778243
theorem B28050209 : Blo 2159435 28050209 := bstep (se 2 (by rfl) ⟨10518828, by rfl⟩ : syracuseStep 28050209 = 21037657) B21037657
theorem B18700139 : Blo 2159435 18700139 := bstep (se 1 (by rfl) ⟨14025104, by rfl⟩ : syracuseStep 18700139 = 28050209) B28050209
theorem B12466759 : Blo 2159435 12466759 := bstep (se 1 (by rfl) ⟨9350069, by rfl⟩ : syracuseStep 12466759 = 18700139) B18700139
theorem B16622345 : Blo 2159435 16622345 := bstep (se 2 (by rfl) ⟨6233379, by rfl⟩ : syracuseStep 16622345 = 12466759) B12466759
theorem B44326253 : Blo 2159435 44326253 := bstep (se 3 (by rfl) ⟨8311172, by rfl⟩ : syracuseStep 44326253 = 16622345) B16622345
theorem B29550835 : Blo 2159435 29550835 := bstep (se 1 (by rfl) ⟨22163126, by rfl⟩ : syracuseStep 29550835 = 44326253) B44326253
theorem B39401113 : Blo 2159435 39401113 := bstep (se 2 (by rfl) ⟨14775417, by rfl⟩ : syracuseStep 39401113 = 29550835) B29550835
theorem B52534817 : Blo 2159435 52534817 := bstep (se 2 (by rfl) ⟨19700556, by rfl⟩ : syracuseStep 52534817 = 39401113) B39401113
theorem B35023211 : Blo 2159435 35023211 := bstep (se 1 (by rfl) ⟨26267408, by rfl⟩ : syracuseStep 35023211 = 52534817) B52534817
theorem B23348807 : Blo 2159435 23348807 := bstep (se 1 (by rfl) ⟨17511605, by rfl⟩ : syracuseStep 23348807 = 35023211) B35023211
theorem B15565871 : Blo 2159435 15565871 := bstep (se 1 (by rfl) ⟨11674403, by rfl⟩ : syracuseStep 15565871 = 23348807) B23348807
theorem B10377247 : Blo 2159435 10377247 := bstep (se 1 (by rfl) ⟨7782935, by rfl⟩ : syracuseStep 10377247 = 15565871) B15565871
theorem B13836329 : Blo 2159435 13836329 := bstep (se 2 (by rfl) ⟨5188623, by rfl⟩ : syracuseStep 13836329 = 10377247) B10377247
theorem B9224219 : Blo 2159435 9224219 := bstep (se 1 (by rfl) ⟨6918164, by rfl⟩ : syracuseStep 9224219 = 13836329) B13836329
theorem B24597917 : Blo 2159435 24597917 := bstep (se 3 (by rfl) ⟨4612109, by rfl⟩ : syracuseStep 24597917 = 9224219) B9224219
theorem B16398611 : Blo 2159435 16398611 := bstep (se 1 (by rfl) ⟨12298958, by rfl⟩ : syracuseStep 16398611 = 24597917) B24597917
theorem B10932407 : Blo 2159435 10932407 := bstep (se 1 (by rfl) ⟨8199305, by rfl⟩ : syracuseStep 10932407 = 16398611) B16398611
theorem B7288271 : Blo 2159435 7288271 := bstep (se 1 (by rfl) ⟨5466203, by rfl⟩ : syracuseStep 7288271 = 10932407) B10932407
theorem B4858847 : Blo 2159435 4858847 := bstep (se 1 (by rfl) ⟨3644135, by rfl⟩ : syracuseStep 4858847 = 7288271) B7288271
theorem B3239231 : Blo 2159435 3239231 := bstep (se 1 (by rfl) ⟨2429423, by rfl⟩ : syracuseStep 3239231 = 4858847) B4858847
theorem B2159487 : Blo 2159435 2159487 := bstep (se 1 (by rfl) ⟨1619615, by rfl⟩ : syracuseStep 2159487 = 3239231) B3239231
theorem B3239237 : Blo 2159435 3239237 := bbase (se 4 (by rfl) ⟨303678, by rfl⟩ : syracuseStep 3239237 = 607357) (by norm_num)
theorem B2159491 : Blo 2159435 2159491 := bstep (se 1 (by rfl) ⟨1619618, by rfl⟩ : syracuseStep 2159491 = 3239237) B3239237
theorem B3644149 : Blo 2159435 3644149 := bbase (se 5 (by rfl) ⟨170819, by rfl⟩ : syracuseStep 3644149 = 341639) (by norm_num)
theorem B4858865 : Blo 2159435 4858865 := bstep (se 2 (by rfl) ⟨1822074, by rfl⟩ : syracuseStep 4858865 = 3644149) B3644149
theorem B3239243 : Blo 2159435 3239243 := bstep (se 1 (by rfl) ⟨2429432, by rfl⟩ : syracuseStep 3239243 = 4858865) B4858865
theorem B2159495 : Blo 2159435 2159495 := bstep (se 1 (by rfl) ⟨1619621, by rfl⟩ : syracuseStep 2159495 = 3239243) B3239243
theorem B2429437 : Blo 2159435 2429437 := bbase (se 3 (by rfl) ⟨455519, by rfl⟩ : syracuseStep 2429437 = 911039) (by norm_num)
theorem B3239249 : Blo 2159435 3239249 := bstep (se 2 (by rfl) ⟨1214718, by rfl⟩ : syracuseStep 3239249 = 2429437) B2429437
theorem B2159499 : Blo 2159435 2159499 := bstep (se 1 (by rfl) ⟨1619624, by rfl⟩ : syracuseStep 2159499 = 3239249) B3239249
theorem B7288325 : Blo 2159435 7288325 := bbase (se 4 (by rfl) ⟨683280, by rfl⟩ : syracuseStep 7288325 = 1366561) (by norm_num)
theorem B4858883 : Blo 2159435 4858883 := bstep (se 1 (by rfl) ⟨3644162, by rfl⟩ : syracuseStep 4858883 = 7288325) B7288325
theorem B3239255 : Blo 2159435 3239255 := bstep (se 1 (by rfl) ⟨2429441, by rfl⟩ : syracuseStep 3239255 = 4858883) B4858883
theorem B2159503 : Blo 2159435 2159503 := bstep (se 1 (by rfl) ⟨1619627, by rfl⟩ : syracuseStep 2159503 = 3239255) B3239255
theorem B3239261 : Blo 2159435 3239261 := bbase (se 3 (by rfl) ⟨607361, by rfl⟩ : syracuseStep 3239261 = 1214723) (by norm_num)
theorem B2159507 : Blo 2159435 2159507 := bstep (se 1 (by rfl) ⟨1619630, by rfl⟩ : syracuseStep 2159507 = 3239261) B3239261
theorem B4858901 : Blo 2159435 4858901 := bbase (se 6 (by rfl) ⟨113880, by rfl⟩ : syracuseStep 4858901 = 227761) (by norm_num)
theorem B3239267 : Blo 2159435 3239267 := bstep (se 1 (by rfl) ⟨2429450, by rfl⟩ : syracuseStep 3239267 = 4858901) B4858901
theorem B2159511 : Blo 2159435 2159511 := bstep (se 1 (by rfl) ⟨1619633, by rfl⟩ : syracuseStep 2159511 = 3239267) B3239267
theorem B8199413 : Blo 2159435 8199413 := bbase (se 5 (by rfl) ⟨384347, by rfl⟩ : syracuseStep 8199413 = 768695) (by norm_num)
theorem B5466275 : Blo 2159435 5466275 := bstep (se 1 (by rfl) ⟨4099706, by rfl⟩ : syracuseStep 5466275 = 8199413) B8199413
theorem B3644183 : Blo 2159435 3644183 := bstep (se 1 (by rfl) ⟨2733137, by rfl⟩ : syracuseStep 3644183 = 5466275) B5466275
theorem B2429455 : Blo 2159435 2429455 := bstep (se 1 (by rfl) ⟨1822091, by rfl⟩ : syracuseStep 2429455 = 3644183) B3644183
theorem B3239273 : Blo 2159435 3239273 := bstep (se 2 (by rfl) ⟨1214727, by rfl⟩ : syracuseStep 3239273 = 2429455) B2429455
theorem B2159515 : Blo 2159435 2159515 := bstep (se 1 (by rfl) ⟨1619636, by rfl⟩ : syracuseStep 2159515 = 3239273) B3239273
theorem B2306089 : Blo 2159435 2306089 := bbase (se 2 (by rfl) ⟨864783, by rfl⟩ : syracuseStep 2306089 = 1729567) (by norm_num)
theorem B12299141 : Blo 2159435 12299141 := bstep (se 4 (by rfl) ⟨1153044, by rfl⟩ : syracuseStep 12299141 = 2306089) B2306089
theorem B8199427 : Blo 2159435 8199427 := bstep (se 1 (by rfl) ⟨6149570, by rfl⟩ : syracuseStep 8199427 = 12299141) B12299141
theorem B10932569 : Blo 2159435 10932569 := bstep (se 2 (by rfl) ⟨4099713, by rfl⟩ : syracuseStep 10932569 = 8199427) B8199427
theorem B7288379 : Blo 2159435 7288379 := bstep (se 1 (by rfl) ⟨5466284, by rfl⟩ : syracuseStep 7288379 = 10932569) B10932569
theorem B4858919 : Blo 2159435 4858919 := bstep (se 1 (by rfl) ⟨3644189, by rfl⟩ : syracuseStep 4858919 = 7288379) B7288379
theorem B3239279 : Blo 2159435 3239279 := bstep (se 1 (by rfl) ⟨2429459, by rfl⟩ : syracuseStep 3239279 = 4858919) B4858919
theorem B2159519 : Blo 2159435 2159519 := bstep (se 1 (by rfl) ⟨1619639, by rfl⟩ : syracuseStep 2159519 = 3239279) B3239279
theorem B3239285 : Blo 2159435 3239285 := bbase (se 5 (by rfl) ⟨151841, by rfl⟩ : syracuseStep 3239285 = 303683) (by norm_num)
theorem B2159523 : Blo 2159435 2159523 := bstep (se 1 (by rfl) ⟨1619642, by rfl⟩ : syracuseStep 2159523 = 3239285) B3239285
theorem B3074797 : Blo 2159435 3074797 := bbase (se 3 (by rfl) ⟨576524, by rfl⟩ : syracuseStep 3074797 = 1153049) (by norm_num)
theorem B4099729 : Blo 2159435 4099729 := bstep (se 2 (by rfl) ⟨1537398, by rfl⟩ : syracuseStep 4099729 = 3074797) B3074797
theorem B5466305 : Blo 2159435 5466305 := bstep (se 2 (by rfl) ⟨2049864, by rfl⟩ : syracuseStep 5466305 = 4099729) B4099729
theorem B3644203 : Blo 2159435 3644203 := bstep (se 1 (by rfl) ⟨2733152, by rfl⟩ : syracuseStep 3644203 = 5466305) B5466305
theorem B4858937 : Blo 2159435 4858937 := bstep (se 2 (by rfl) ⟨1822101, by rfl⟩ : syracuseStep 4858937 = 3644203) B3644203
theorem B3239291 : Blo 2159435 3239291 := bstep (se 1 (by rfl) ⟨2429468, by rfl⟩ : syracuseStep 3239291 = 4858937) B4858937
theorem B2159527 : Blo 2159435 2159527 := bstep (se 1 (by rfl) ⟨1619645, by rfl⟩ : syracuseStep 2159527 = 3239291) B3239291
theorem B2429473 : Blo 2159435 2429473 := bbase (se 2 (by rfl) ⟨911052, by rfl⟩ : syracuseStep 2429473 = 1822105) (by norm_num)
theorem B3239297 : Blo 2159435 3239297 := bstep (se 2 (by rfl) ⟨1214736, by rfl⟩ : syracuseStep 3239297 = 2429473) B2429473
theorem B2159531 : Blo 2159435 2159531 := bstep (se 1 (by rfl) ⟨1619648, by rfl⟩ : syracuseStep 2159531 = 3239297) B3239297
theorem B5466325 : Blo 2159435 5466325 := bbase (se 7 (by rfl) ⟨64058, by rfl⟩ : syracuseStep 5466325 = 128117) (by norm_num)
theorem B7288433 : Blo 2159435 7288433 := bstep (se 2 (by rfl) ⟨2733162, by rfl⟩ : syracuseStep 7288433 = 5466325) B5466325
theorem B4858955 : Blo 2159435 4858955 := bstep (se 1 (by rfl) ⟨3644216, by rfl⟩ : syracuseStep 4858955 = 7288433) B7288433
theorem B3239303 : Blo 2159435 3239303 := bstep (se 1 (by rfl) ⟨2429477, by rfl⟩ : syracuseStep 3239303 = 4858955) B4858955
theorem B2159535 : Blo 2159435 2159535 := bstep (se 1 (by rfl) ⟨1619651, by rfl⟩ : syracuseStep 2159535 = 3239303) B3239303
theorem B3239309 : Blo 2159435 3239309 := bbase (se 3 (by rfl) ⟨607370, by rfl⟩ : syracuseStep 3239309 = 1214741) (by norm_num)
theorem B2159539 : Blo 2159435 2159539 := bstep (se 1 (by rfl) ⟨1619654, by rfl⟩ : syracuseStep 2159539 = 3239309) B3239309
theorem B4858973 : Blo 2159435 4858973 := bbase (se 3 (by rfl) ⟨911057, by rfl⟩ : syracuseStep 4858973 = 1822115) (by norm_num)
theorem B3239315 : Blo 2159435 3239315 := bstep (se 1 (by rfl) ⟨2429486, by rfl⟩ : syracuseStep 3239315 = 4858973) B4858973
theorem B2159543 : Blo 2159435 2159543 := bstep (se 1 (by rfl) ⟨1619657, by rfl⟩ : syracuseStep 2159543 = 3239315) B3239315
theorem B3644237 : Blo 2159435 3644237 := bbase (se 3 (by rfl) ⟨683294, by rfl⟩ : syracuseStep 3644237 = 1366589) (by norm_num)
theorem B2429491 : Blo 2159435 2429491 := bstep (se 1 (by rfl) ⟨1822118, by rfl⟩ : syracuseStep 2429491 = 3644237) B3644237
theorem B3239321 : Blo 2159435 3239321 := bstep (se 2 (by rfl) ⟨1214745, by rfl⟩ : syracuseStep 3239321 = 2429491) B2429491
theorem B2159547 : Blo 2159435 2159547 := bstep (se 1 (by rfl) ⟨1619660, by rfl⟩ : syracuseStep 2159547 = 3239321) B3239321
theorem B44327573 : Blo 2159435 44327573 := bbase (se 6 (by rfl) ⟨1038927, by rfl⟩ : syracuseStep 44327573 = 2077855) (by norm_num)
theorem B29551715 : Blo 2159435 29551715 := bstep (se 1 (by rfl) ⟨22163786, by rfl⟩ : syracuseStep 29551715 = 44327573) B44327573
theorem B19701143 : Blo 2159435 19701143 := bstep (se 1 (by rfl) ⟨14775857, by rfl⟩ : syracuseStep 19701143 = 29551715) B29551715
theorem B13134095 : Blo 2159435 13134095 := bstep (se 1 (by rfl) ⟨9850571, by rfl⟩ : syracuseStep 13134095 = 19701143) B19701143
theorem B8756063 : Blo 2159435 8756063 := bstep (se 1 (by rfl) ⟨6567047, by rfl⟩ : syracuseStep 8756063 = 13134095) B13134095
theorem B5837375 : Blo 2159435 5837375 := bstep (se 1 (by rfl) ⟨4378031, by rfl⟩ : syracuseStep 5837375 = 8756063) B8756063
theorem B3891583 : Blo 2159435 3891583 := bstep (se 1 (by rfl) ⟨2918687, by rfl⟩ : syracuseStep 3891583 = 5837375) B5837375
theorem B20755109 : Blo 2159435 20755109 := bstep (se 4 (by rfl) ⟨1945791, by rfl⟩ : syracuseStep 20755109 = 3891583) B3891583
theorem B13836739 : Blo 2159435 13836739 := bstep (se 1 (by rfl) ⟨10377554, by rfl⟩ : syracuseStep 13836739 = 20755109) B20755109
theorem B18448985 : Blo 2159435 18448985 := bstep (se 2 (by rfl) ⟨6918369, by rfl⟩ : syracuseStep 18448985 = 13836739) B13836739
theorem B12299323 : Blo 2159435 12299323 := bstep (se 1 (by rfl) ⟨9224492, by rfl⟩ : syracuseStep 12299323 = 18448985) B18448985
theorem B16399097 : Blo 2159435 16399097 := bstep (se 2 (by rfl) ⟨6149661, by rfl⟩ : syracuseStep 16399097 = 12299323) B12299323
theorem B10932731 : Blo 2159435 10932731 := bstep (se 1 (by rfl) ⟨8199548, by rfl⟩ : syracuseStep 10932731 = 16399097) B16399097
theorem B7288487 : Blo 2159435 7288487 := bstep (se 1 (by rfl) ⟨5466365, by rfl⟩ : syracuseStep 7288487 = 10932731) B10932731
theorem B4858991 : Blo 2159435 4858991 := bstep (se 1 (by rfl) ⟨3644243, by rfl⟩ : syracuseStep 4858991 = 7288487) B7288487
theorem B3239327 : Blo 2159435 3239327 := bstep (se 1 (by rfl) ⟨2429495, by rfl⟩ : syracuseStep 3239327 = 4858991) B4858991
theorem B2159551 : Blo 2159435 2159551 := bstep (se 1 (by rfl) ⟨1619663, by rfl⟩ : syracuseStep 2159551 = 3239327) B3239327
theorem B3239333 : Blo 2159435 3239333 := bbase (se 4 (by rfl) ⟨303687, by rfl⟩ : syracuseStep 3239333 = 607375) (by norm_num)
theorem B2159555 : Blo 2159435 2159555 := bstep (se 1 (by rfl) ⟨1619666, by rfl⟩ : syracuseStep 2159555 = 3239333) B3239333
theorem B2733193 : Blo 2159435 2733193 := bbase (se 2 (by rfl) ⟨1024947, by rfl⟩ : syracuseStep 2733193 = 2049895) (by norm_num)
theorem B3644257 : Blo 2159435 3644257 := bstep (se 2 (by rfl) ⟨1366596, by rfl⟩ : syracuseStep 3644257 = 2733193) B2733193
theorem B4859009 : Blo 2159435 4859009 := bstep (se 2 (by rfl) ⟨1822128, by rfl⟩ : syracuseStep 4859009 = 3644257) B3644257
theorem B3239339 : Blo 2159435 3239339 := bstep (se 1 (by rfl) ⟨2429504, by rfl⟩ : syracuseStep 3239339 = 4859009) B4859009
theorem B2159559 : Blo 2159435 2159559 := bstep (se 1 (by rfl) ⟨1619669, by rfl⟩ : syracuseStep 2159559 = 3239339) B3239339
theorem B2429509 : Blo 2159435 2429509 := bbase (se 4 (by rfl) ⟨227766, by rfl⟩ : syracuseStep 2429509 = 455533) (by norm_num)
theorem B3239345 : Blo 2159435 3239345 := bstep (se 2 (by rfl) ⟨1214754, by rfl⟩ : syracuseStep 3239345 = 2429509) B2429509
theorem B2159563 : Blo 2159435 2159563 := bstep (se 1 (by rfl) ⟨1619672, by rfl⟩ : syracuseStep 2159563 = 3239345) B3239345
theorem B4099805 : Blo 2159435 4099805 := bbase (se 3 (by rfl) ⟨768713, by rfl⟩ : syracuseStep 4099805 = 1537427) (by norm_num)
theorem B2733203 : Blo 2159435 2733203 := bstep (se 1 (by rfl) ⟨2049902, by rfl⟩ : syracuseStep 2733203 = 4099805) B4099805
theorem B7288541 : Blo 2159435 7288541 := bstep (se 3 (by rfl) ⟨1366601, by rfl⟩ : syracuseStep 7288541 = 2733203) B2733203
theorem B4859027 : Blo 2159435 4859027 := bstep (se 1 (by rfl) ⟨3644270, by rfl⟩ : syracuseStep 4859027 = 7288541) B7288541
theorem B3239351 : Blo 2159435 3239351 := bstep (se 1 (by rfl) ⟨2429513, by rfl⟩ : syracuseStep 3239351 = 4859027) B4859027
theorem B2159567 : Blo 2159435 2159567 := bstep (se 1 (by rfl) ⟨1619675, by rfl⟩ : syracuseStep 2159567 = 3239351) B3239351
theorem B3239357 : Blo 2159435 3239357 := bbase (se 3 (by rfl) ⟨607379, by rfl⟩ : syracuseStep 3239357 = 1214759) (by norm_num)
theorem B2159571 : Blo 2159435 2159571 := bstep (se 1 (by rfl) ⟨1619678, by rfl⟩ : syracuseStep 2159571 = 3239357) B3239357
theorem B4859045 : Blo 2159435 4859045 := bbase (se 4 (by rfl) ⟨455535, by rfl⟩ : syracuseStep 4859045 = 911071) (by norm_num)
theorem B3239363 : Blo 2159435 3239363 := bstep (se 1 (by rfl) ⟨2429522, by rfl⟩ : syracuseStep 3239363 = 4859045) B4859045
theorem B2159575 : Blo 2159435 2159575 := bstep (se 1 (by rfl) ⟨1619681, by rfl⟩ : syracuseStep 2159575 = 3239363) B3239363
theorem B5466437 : Blo 2159435 5466437 := bbase (se 4 (by rfl) ⟨512478, by rfl⟩ : syracuseStep 5466437 = 1024957) (by norm_num)
theorem B3644291 : Blo 2159435 3644291 := bstep (se 1 (by rfl) ⟨2733218, by rfl⟩ : syracuseStep 3644291 = 5466437) B5466437
theorem B2429527 : Blo 2159435 2429527 := bstep (se 1 (by rfl) ⟨1822145, by rfl⟩ : syracuseStep 2429527 = 3644291) B3644291
theorem B3239369 : Blo 2159435 3239369 := bstep (se 2 (by rfl) ⟨1214763, by rfl⟩ : syracuseStep 3239369 = 2429527) B2429527
theorem B2159579 : Blo 2159435 2159579 := bstep (se 1 (by rfl) ⟨1619684, by rfl⟩ : syracuseStep 2159579 = 3239369) B3239369
theorem B3283573 : Blo 2159435 3283573 := bbase (se 5 (by rfl) ⟨153917, by rfl⟩ : syracuseStep 3283573 = 307835) (by norm_num)
theorem B4378097 : Blo 2159435 4378097 := bstep (se 2 (by rfl) ⟨1641786, by rfl⟩ : syracuseStep 4378097 = 3283573) B3283573
theorem B11674925 : Blo 2159435 11674925 := bstep (se 3 (by rfl) ⟨2189048, by rfl⟩ : syracuseStep 11674925 = 4378097) B4378097
theorem B7783283 : Blo 2159435 7783283 := bstep (se 1 (by rfl) ⟨5837462, by rfl⟩ : syracuseStep 7783283 = 11674925) B11674925
theorem B5188855 : Blo 2159435 5188855 := bstep (se 1 (by rfl) ⟨3891641, by rfl⟩ : syracuseStep 5188855 = 7783283) B7783283
theorem B6918473 : Blo 2159435 6918473 := bstep (se 2 (by rfl) ⟨2594427, by rfl⟩ : syracuseStep 6918473 = 5188855) B5188855
theorem B4612315 : Blo 2159435 4612315 := bstep (se 1 (by rfl) ⟨3459236, by rfl⟩ : syracuseStep 4612315 = 6918473) B6918473
theorem B6149753 : Blo 2159435 6149753 := bstep (se 2 (by rfl) ⟨2306157, by rfl⟩ : syracuseStep 6149753 = 4612315) B4612315
theorem B4099835 : Blo 2159435 4099835 := bstep (se 1 (by rfl) ⟨3074876, by rfl⟩ : syracuseStep 4099835 = 6149753) B6149753
theorem B10932893 : Blo 2159435 10932893 := bstep (se 3 (by rfl) ⟨2049917, by rfl⟩ : syracuseStep 10932893 = 4099835) B4099835
theorem B7288595 : Blo 2159435 7288595 := bstep (se 1 (by rfl) ⟨5466446, by rfl⟩ : syracuseStep 7288595 = 10932893) B10932893
theorem B4859063 : Blo 2159435 4859063 := bstep (se 1 (by rfl) ⟨3644297, by rfl⟩ : syracuseStep 4859063 = 7288595) B7288595
theorem B3239375 : Blo 2159435 3239375 := bstep (se 1 (by rfl) ⟨2429531, by rfl⟩ : syracuseStep 3239375 = 4859063) B4859063
theorem B2159583 : Blo 2159435 2159583 := bstep (se 1 (by rfl) ⟨1619687, by rfl⟩ : syracuseStep 2159583 = 3239375) B3239375
theorem B3239381 : Blo 2159435 3239381 := bbase (se 7 (by rfl) ⟨37961, by rfl⟩ : syracuseStep 3239381 = 75923) (by norm_num)
theorem B2159587 : Blo 2159435 2159587 := bstep (se 1 (by rfl) ⟨1619690, by rfl⟩ : syracuseStep 2159587 = 3239381) B3239381
theorem B8199701 : Blo 2159435 8199701 := bbase (se 6 (by rfl) ⟨192180, by rfl⟩ : syracuseStep 8199701 = 384361) (by norm_num)
theorem B5466467 : Blo 2159435 5466467 := bstep (se 1 (by rfl) ⟨4099850, by rfl⟩ : syracuseStep 5466467 = 8199701) B8199701
theorem B3644311 : Blo 2159435 3644311 := bstep (se 1 (by rfl) ⟨2733233, by rfl⟩ : syracuseStep 3644311 = 5466467) B5466467
theorem B4859081 : Blo 2159435 4859081 := bstep (se 2 (by rfl) ⟨1822155, by rfl⟩ : syracuseStep 4859081 = 3644311) B3644311
theorem B3239387 : Blo 2159435 3239387 := bstep (se 1 (by rfl) ⟨2429540, by rfl⟩ : syracuseStep 3239387 = 4859081) B4859081
theorem B2159591 : Blo 2159435 2159591 := bstep (se 1 (by rfl) ⟨1619693, by rfl⟩ : syracuseStep 2159591 = 3239387) B3239387
theorem B2429545 : Blo 2159435 2429545 := bbase (se 2 (by rfl) ⟨911079, by rfl⟩ : syracuseStep 2429545 = 1822159) (by norm_num)
theorem B3239393 : Blo 2159435 3239393 := bstep (se 2 (by rfl) ⟨1214772, by rfl⟩ : syracuseStep 3239393 = 2429545) B2429545
theorem B2159595 : Blo 2159435 2159595 := bstep (se 1 (by rfl) ⟨1619696, by rfl⟩ : syracuseStep 2159595 = 3239393) B3239393
theorem B4612349 : Blo 2159435 4612349 := bbase (se 3 (by rfl) ⟨864815, by rfl⟩ : syracuseStep 4612349 = 1729631) (by norm_num)
theorem B12299597 : Blo 2159435 12299597 := bstep (se 3 (by rfl) ⟨2306174, by rfl⟩ : syracuseStep 12299597 = 4612349) B4612349
theorem B8199731 : Blo 2159435 8199731 := bstep (se 1 (by rfl) ⟨6149798, by rfl⟩ : syracuseStep 8199731 = 12299597) B12299597
theorem B5466487 : Blo 2159435 5466487 := bstep (se 1 (by rfl) ⟨4099865, by rfl⟩ : syracuseStep 5466487 = 8199731) B8199731
theorem B7288649 : Blo 2159435 7288649 := bstep (se 2 (by rfl) ⟨2733243, by rfl⟩ : syracuseStep 7288649 = 5466487) B5466487
theorem B4859099 : Blo 2159435 4859099 := bstep (se 1 (by rfl) ⟨3644324, by rfl⟩ : syracuseStep 4859099 = 7288649) B7288649
theorem B3239399 : Blo 2159435 3239399 := bstep (se 1 (by rfl) ⟨2429549, by rfl⟩ : syracuseStep 3239399 = 4859099) B4859099
theorem B2159599 : Blo 2159435 2159599 := bstep (se 1 (by rfl) ⟨1619699, by rfl⟩ : syracuseStep 2159599 = 3239399) B3239399
theorem B3239405 : Blo 2159435 3239405 := bbase (se 3 (by rfl) ⟨607388, by rfl⟩ : syracuseStep 3239405 = 1214777) (by norm_num)
theorem B2159603 : Blo 2159435 2159603 := bstep (se 1 (by rfl) ⟨1619702, by rfl⟩ : syracuseStep 2159603 = 3239405) B3239405
theorem B4859117 : Blo 2159435 4859117 := bbase (se 3 (by rfl) ⟨911084, by rfl⟩ : syracuseStep 4859117 = 1822169) (by norm_num)
theorem B3239411 : Blo 2159435 3239411 := bstep (se 1 (by rfl) ⟨2429558, by rfl⟩ : syracuseStep 3239411 = 4859117) B4859117
theorem B2159607 : Blo 2159435 2159607 := bstep (se 1 (by rfl) ⟨1619705, by rfl⟩ : syracuseStep 2159607 = 3239411) B3239411
theorem B3074917 : Blo 2159435 3074917 := bbase (se 4 (by rfl) ⟨288273, by rfl⟩ : syracuseStep 3074917 = 576547) (by norm_num)
theorem B4099889 : Blo 2159435 4099889 := bstep (se 2 (by rfl) ⟨1537458, by rfl⟩ : syracuseStep 4099889 = 3074917) B3074917
theorem B2733259 : Blo 2159435 2733259 := bstep (se 1 (by rfl) ⟨2049944, by rfl⟩ : syracuseStep 2733259 = 4099889) B4099889
theorem B3644345 : Blo 2159435 3644345 := bstep (se 2 (by rfl) ⟨1366629, by rfl⟩ : syracuseStep 3644345 = 2733259) B2733259
theorem B2429563 : Blo 2159435 2429563 := bstep (se 1 (by rfl) ⟨1822172, by rfl⟩ : syracuseStep 2429563 = 3644345) B3644345
theorem B3239417 : Blo 2159435 3239417 := bstep (se 2 (by rfl) ⟨1214781, by rfl⟩ : syracuseStep 3239417 = 2429563) B2429563
theorem B2159611 : Blo 2159435 2159611 := bstep (se 1 (by rfl) ⟨1619708, by rfl⟩ : syracuseStep 2159611 = 3239417) B3239417
theorem B3506485 : Blo 2159435 3506485 := bbase (se 5 (by rfl) ⟨164366, by rfl⟩ : syracuseStep 3506485 = 328733) (by norm_num)
theorem B4675313 : Blo 2159435 4675313 := bstep (se 2 (by rfl) ⟨1753242, by rfl⟩ : syracuseStep 4675313 = 3506485) B3506485
theorem B3116875 : Blo 2159435 3116875 := bstep (se 1 (by rfl) ⟨2337656, by rfl⟩ : syracuseStep 3116875 = 4675313) B4675313
theorem B4155833 : Blo 2159435 4155833 := bstep (se 2 (by rfl) ⟨1558437, by rfl⟩ : syracuseStep 4155833 = 3116875) B3116875
theorem B11082221 : Blo 2159435 11082221 := bstep (se 3 (by rfl) ⟨2077916, by rfl⟩ : syracuseStep 11082221 = 4155833) B4155833
theorem B7388147 : Blo 2159435 7388147 := bstep (se 1 (by rfl) ⟨5541110, by rfl⟩ : syracuseStep 7388147 = 11082221) B11082221
theorem B4925431 : Blo 2159435 4925431 := bstep (se 1 (by rfl) ⟨3694073, by rfl⟩ : syracuseStep 4925431 = 7388147) B7388147
theorem B6567241 : Blo 2159435 6567241 := bstep (se 2 (by rfl) ⟨2462715, by rfl⟩ : syracuseStep 6567241 = 4925431) B4925431
theorem B8756321 : Blo 2159435 8756321 := bstep (se 2 (by rfl) ⟨3283620, by rfl⟩ : syracuseStep 8756321 = 6567241) B6567241
theorem B23350189 : Blo 2159435 23350189 := bstep (se 3 (by rfl) ⟨4378160, by rfl⟩ : syracuseStep 23350189 = 8756321) B8756321
theorem B31133585 : Blo 2159435 31133585 := bstep (se 2 (by rfl) ⟨11675094, by rfl⟩ : syracuseStep 31133585 = 23350189) B23350189
theorem B83022893 : Blo 2159435 83022893 := bstep (se 3 (by rfl) ⟨15566792, by rfl⟩ : syracuseStep 83022893 = 31133585) B31133585
theorem B55348595 : Blo 2159435 55348595 := bstep (se 1 (by rfl) ⟨41511446, by rfl⟩ : syracuseStep 55348595 = 83022893) B83022893
theorem B36899063 : Blo 2159435 36899063 := bstep (se 1 (by rfl) ⟨27674297, by rfl⟩ : syracuseStep 36899063 = 55348595) B55348595
theorem B24599375 : Blo 2159435 24599375 := bstep (se 1 (by rfl) ⟨18449531, by rfl⟩ : syracuseStep 24599375 = 36899063) B36899063
theorem B16399583 : Blo 2159435 16399583 := bstep (se 1 (by rfl) ⟨12299687, by rfl⟩ : syracuseStep 16399583 = 24599375) B24599375
theorem B10933055 : Blo 2159435 10933055 := bstep (se 1 (by rfl) ⟨8199791, by rfl⟩ : syracuseStep 10933055 = 16399583) B16399583
theorem B7288703 : Blo 2159435 7288703 := bstep (se 1 (by rfl) ⟨5466527, by rfl⟩ : syracuseStep 7288703 = 10933055) B10933055
theorem B4859135 : Blo 2159435 4859135 := bstep (se 1 (by rfl) ⟨3644351, by rfl⟩ : syracuseStep 4859135 = 7288703) B7288703
theorem B3239423 : Blo 2159435 3239423 := bstep (se 1 (by rfl) ⟨2429567, by rfl⟩ : syracuseStep 3239423 = 4859135) B4859135
theorem B2159615 : Blo 2159435 2159615 := bstep (se 1 (by rfl) ⟨1619711, by rfl⟩ : syracuseStep 2159615 = 3239423) B3239423
theorem B3239429 : Blo 2159435 3239429 := bbase (se 4 (by rfl) ⟨303696, by rfl⟩ : syracuseStep 3239429 = 607393) (by norm_num)
theorem B2159619 : Blo 2159435 2159619 := bstep (se 1 (by rfl) ⟨1619714, by rfl⟩ : syracuseStep 2159619 = 3239429) B3239429
theorem B3644365 : Blo 2159435 3644365 := bbase (se 3 (by rfl) ⟨683318, by rfl⟩ : syracuseStep 3644365 = 1366637) (by norm_num)
theorem B4859153 : Blo 2159435 4859153 := bstep (se 2 (by rfl) ⟨1822182, by rfl⟩ : syracuseStep 4859153 = 3644365) B3644365
theorem B3239435 : Blo 2159435 3239435 := bstep (se 1 (by rfl) ⟨2429576, by rfl⟩ : syracuseStep 3239435 = 4859153) B4859153
theorem B2159623 : Blo 2159435 2159623 := bstep (se 1 (by rfl) ⟨1619717, by rfl⟩ : syracuseStep 2159623 = 3239435) B3239435
theorem B2429581 : Blo 2159435 2429581 := bbase (se 3 (by rfl) ⟨455546, by rfl⟩ : syracuseStep 2429581 = 911093) (by norm_num)
theorem B3239441 : Blo 2159435 3239441 := bstep (se 2 (by rfl) ⟨1214790, by rfl⟩ : syracuseStep 3239441 = 2429581) B2429581
theorem B2159627 : Blo 2159435 2159627 := bstep (se 1 (by rfl) ⟨1619720, by rfl⟩ : syracuseStep 2159627 = 3239441) B3239441
theorem B7288757 : Blo 2159435 7288757 := bbase (se 5 (by rfl) ⟨341660, by rfl⟩ : syracuseStep 7288757 = 683321) (by norm_num)
theorem B4859171 : Blo 2159435 4859171 := bstep (se 1 (by rfl) ⟨3644378, by rfl⟩ : syracuseStep 4859171 = 7288757) B7288757
theorem B3239447 : Blo 2159435 3239447 := bstep (se 1 (by rfl) ⟨2429585, by rfl⟩ : syracuseStep 3239447 = 4859171) B4859171
theorem B2159631 : Blo 2159435 2159631 := bstep (se 1 (by rfl) ⟨1619723, by rfl⟩ : syracuseStep 2159631 = 3239447) B3239447
theorem B3239453 : Blo 2159435 3239453 := bbase (se 3 (by rfl) ⟨607397, by rfl⟩ : syracuseStep 3239453 = 1214795) (by norm_num)
theorem B2159635 : Blo 2159435 2159635 := bstep (se 1 (by rfl) ⟨1619726, by rfl⟩ : syracuseStep 2159635 = 3239453) B3239453
theorem B4859189 : Blo 2159435 4859189 := bbase (se 5 (by rfl) ⟨227774, by rfl⟩ : syracuseStep 4859189 = 455549) (by norm_num)
theorem B3239459 : Blo 2159435 3239459 := bstep (se 1 (by rfl) ⟨2429594, by rfl⟩ : syracuseStep 3239459 = 4859189) B4859189
theorem B2159639 : Blo 2159435 2159639 := bstep (se 1 (by rfl) ⟨1619729, by rfl⟩ : syracuseStep 2159639 = 3239459) B3239459
theorem B8756437 : Blo 2159435 8756437 := bbase (se 7 (by rfl) ⟨102614, by rfl⟩ : syracuseStep 8756437 = 205229) (by norm_num)
theorem B11675249 : Blo 2159435 11675249 := bstep (se 2 (by rfl) ⟨4378218, by rfl⟩ : syracuseStep 11675249 = 8756437) B8756437
theorem B7783499 : Blo 2159435 7783499 := bstep (se 1 (by rfl) ⟨5837624, by rfl⟩ : syracuseStep 7783499 = 11675249) B11675249
theorem B20755997 : Blo 2159435 20755997 := bstep (se 3 (by rfl) ⟨3891749, by rfl⟩ : syracuseStep 20755997 = 7783499) B7783499
theorem B13837331 : Blo 2159435 13837331 := bstep (se 1 (by rfl) ⟨10377998, by rfl⟩ : syracuseStep 13837331 = 20755997) B20755997
theorem B9224887 : Blo 2159435 9224887 := bstep (se 1 (by rfl) ⟨6918665, by rfl⟩ : syracuseStep 9224887 = 13837331) B13837331
theorem B12299849 : Blo 2159435 12299849 := bstep (se 2 (by rfl) ⟨4612443, by rfl⟩ : syracuseStep 12299849 = 9224887) B9224887
theorem B8199899 : Blo 2159435 8199899 := bstep (se 1 (by rfl) ⟨6149924, by rfl⟩ : syracuseStep 8199899 = 12299849) B12299849
theorem B5466599 : Blo 2159435 5466599 := bstep (se 1 (by rfl) ⟨4099949, by rfl⟩ : syracuseStep 5466599 = 8199899) B8199899
theorem B3644399 : Blo 2159435 3644399 := bstep (se 1 (by rfl) ⟨2733299, by rfl⟩ : syracuseStep 3644399 = 5466599) B5466599
theorem B2429599 : Blo 2159435 2429599 := bstep (se 1 (by rfl) ⟨1822199, by rfl⟩ : syracuseStep 2429599 = 3644399) B3644399
theorem B3239465 : Blo 2159435 3239465 := bstep (se 2 (by rfl) ⟨1214799, by rfl⟩ : syracuseStep 3239465 = 2429599) B2429599
theorem B2159643 : Blo 2159435 2159643 := bstep (se 1 (by rfl) ⟨1619732, by rfl⟩ : syracuseStep 2159643 = 3239465) B3239465
theorem B2189113 : Blo 2159435 2189113 := bbase (se 2 (by rfl) ⟨820917, by rfl⟩ : syracuseStep 2189113 = 1641835) (by norm_num)
theorem B11675269 : Blo 2159435 11675269 := bstep (se 4 (by rfl) ⟨1094556, by rfl⟩ : syracuseStep 11675269 = 2189113) B2189113
theorem B15567025 : Blo 2159435 15567025 := bstep (se 2 (by rfl) ⟨5837634, by rfl⟩ : syracuseStep 15567025 = 11675269) B11675269
theorem B20756033 : Blo 2159435 20756033 := bstep (se 2 (by rfl) ⟨7783512, by rfl⟩ : syracuseStep 20756033 = 15567025) B15567025
theorem B13837355 : Blo 2159435 13837355 := bstep (se 1 (by rfl) ⟨10378016, by rfl⟩ : syracuseStep 13837355 = 20756033) B20756033
theorem B9224903 : Blo 2159435 9224903 := bstep (se 1 (by rfl) ⟨6918677, by rfl⟩ : syracuseStep 9224903 = 13837355) B13837355
theorem B6149935 : Blo 2159435 6149935 := bstep (se 1 (by rfl) ⟨4612451, by rfl⟩ : syracuseStep 6149935 = 9224903) B9224903
theorem B8199913 : Blo 2159435 8199913 := bstep (se 2 (by rfl) ⟨3074967, by rfl⟩ : syracuseStep 8199913 = 6149935) B6149935
theorem B10933217 : Blo 2159435 10933217 := bstep (se 2 (by rfl) ⟨4099956, by rfl⟩ : syracuseStep 10933217 = 8199913) B8199913
theorem B7288811 : Blo 2159435 7288811 := bstep (se 1 (by rfl) ⟨5466608, by rfl⟩ : syracuseStep 7288811 = 10933217) B10933217
theorem B4859207 : Blo 2159435 4859207 := bstep (se 1 (by rfl) ⟨3644405, by rfl⟩ : syracuseStep 4859207 = 7288811) B7288811
theorem B3239471 : Blo 2159435 3239471 := bstep (se 1 (by rfl) ⟨2429603, by rfl⟩ : syracuseStep 3239471 = 4859207) B4859207
theorem B2159647 : Blo 2159435 2159647 := bstep (se 1 (by rfl) ⟨1619735, by rfl⟩ : syracuseStep 2159647 = 3239471) B3239471
theorem B3239477 : Blo 2159435 3239477 := bbase (se 5 (by rfl) ⟨151850, by rfl⟩ : syracuseStep 3239477 = 303701) (by norm_num)
theorem B2159651 : Blo 2159435 2159651 := bstep (se 1 (by rfl) ⟨1619738, by rfl⟩ : syracuseStep 2159651 = 3239477) B3239477
theorem B5466629 : Blo 2159435 5466629 := bbase (se 4 (by rfl) ⟨512496, by rfl⟩ : syracuseStep 5466629 = 1024993) (by norm_num)
theorem B3644419 : Blo 2159435 3644419 := bstep (se 1 (by rfl) ⟨2733314, by rfl⟩ : syracuseStep 3644419 = 5466629) B5466629
theorem B4859225 : Blo 2159435 4859225 := bstep (se 2 (by rfl) ⟨1822209, by rfl⟩ : syracuseStep 4859225 = 3644419) B3644419
theorem B3239483 : Blo 2159435 3239483 := bstep (se 1 (by rfl) ⟨2429612, by rfl⟩ : syracuseStep 3239483 = 4859225) B4859225
theorem B2159655 : Blo 2159435 2159655 := bstep (se 1 (by rfl) ⟨1619741, by rfl⟩ : syracuseStep 2159655 = 3239483) B3239483
theorem B2429617 : Blo 2159435 2429617 := bbase (se 2 (by rfl) ⟨911106, by rfl⟩ : syracuseStep 2429617 = 1822213) (by norm_num)
theorem B3239489 : Blo 2159435 3239489 := bstep (se 2 (by rfl) ⟨1214808, by rfl⟩ : syracuseStep 3239489 = 2429617) B2429617
theorem B2159659 : Blo 2159435 2159659 := bstep (se 1 (by rfl) ⟨1619744, by rfl⟩ : syracuseStep 2159659 = 3239489) B3239489
theorem B3459365 : Blo 2159435 3459365 := bbase (se 4 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 3459365 = 648631) (by norm_num)
theorem B2306243 : Blo 2159435 2306243 := bstep (se 1 (by rfl) ⟨1729682, by rfl⟩ : syracuseStep 2306243 = 3459365) B3459365
theorem B6149981 : Blo 2159435 6149981 := bstep (se 3 (by rfl) ⟨1153121, by rfl⟩ : syracuseStep 6149981 = 2306243) B2306243
theorem B4099987 : Blo 2159435 4099987 := bstep (se 1 (by rfl) ⟨3074990, by rfl⟩ : syracuseStep 4099987 = 6149981) B6149981
theorem B5466649 : Blo 2159435 5466649 := bstep (se 2 (by rfl) ⟨2049993, by rfl⟩ : syracuseStep 5466649 = 4099987) B4099987
theorem B7288865 : Blo 2159435 7288865 := bstep (se 2 (by rfl) ⟨2733324, by rfl⟩ : syracuseStep 7288865 = 5466649) B5466649
theorem B4859243 : Blo 2159435 4859243 := bstep (se 1 (by rfl) ⟨3644432, by rfl⟩ : syracuseStep 4859243 = 7288865) B7288865
theorem B3239495 : Blo 2159435 3239495 := bstep (se 1 (by rfl) ⟨2429621, by rfl⟩ : syracuseStep 3239495 = 4859243) B4859243
theorem B2159663 : Blo 2159435 2159663 := bstep (se 1 (by rfl) ⟨1619747, by rfl⟩ : syracuseStep 2159663 = 3239495) B3239495
theorem B3239501 : Blo 2159435 3239501 := bbase (se 3 (by rfl) ⟨607406, by rfl⟩ : syracuseStep 3239501 = 1214813) (by norm_num)
theorem B2159667 : Blo 2159435 2159667 := bstep (se 1 (by rfl) ⟨1619750, by rfl⟩ : syracuseStep 2159667 = 3239501) B3239501
theorem B4859261 : Blo 2159435 4859261 := bbase (se 3 (by rfl) ⟨911111, by rfl⟩ : syracuseStep 4859261 = 1822223) (by norm_num)
theorem B3239507 : Blo 2159435 3239507 := bstep (se 1 (by rfl) ⟨2429630, by rfl⟩ : syracuseStep 3239507 = 4859261) B4859261
theorem B2159671 : Blo 2159435 2159671 := bstep (se 1 (by rfl) ⟨1619753, by rfl⟩ : syracuseStep 2159671 = 3239507) B3239507
theorem B3644453 : Blo 2159435 3644453 := bbase (se 4 (by rfl) ⟨341667, by rfl⟩ : syracuseStep 3644453 = 683335) (by norm_num)
theorem B2429635 : Blo 2159435 2429635 := bstep (se 1 (by rfl) ⟨1822226, by rfl⟩ : syracuseStep 2429635 = 3644453) B3644453
theorem B3239513 : Blo 2159435 3239513 := bstep (se 2 (by rfl) ⟨1214817, by rfl⟩ : syracuseStep 3239513 = 2429635) B2429635
theorem B2159675 : Blo 2159435 2159675 := bstep (se 1 (by rfl) ⟨1619756, by rfl⟩ : syracuseStep 2159675 = 3239513) B3239513
theorem B3075013 : Blo 2159435 3075013 := bbase (se 4 (by rfl) ⟨288282, by rfl⟩ : syracuseStep 3075013 = 576565) (by norm_num)
theorem B16400069 : Blo 2159435 16400069 := bstep (se 4 (by rfl) ⟨1537506, by rfl⟩ : syracuseStep 16400069 = 3075013) B3075013
theorem B10933379 : Blo 2159435 10933379 := bstep (se 1 (by rfl) ⟨8200034, by rfl⟩ : syracuseStep 10933379 = 16400069) B16400069
theorem B7288919 : Blo 2159435 7288919 := bstep (se 1 (by rfl) ⟨5466689, by rfl⟩ : syracuseStep 7288919 = 10933379) B10933379
theorem B4859279 : Blo 2159435 4859279 := bstep (se 1 (by rfl) ⟨3644459, by rfl⟩ : syracuseStep 4859279 = 7288919) B7288919
theorem B3239519 : Blo 2159435 3239519 := bstep (se 1 (by rfl) ⟨2429639, by rfl⟩ : syracuseStep 3239519 = 4859279) B4859279
theorem B2159679 : Blo 2159435 2159679 := bstep (se 1 (by rfl) ⟨1619759, by rfl⟩ : syracuseStep 2159679 = 3239519) B3239519
theorem B3239525 : Blo 2159435 3239525 := bbase (se 4 (by rfl) ⟨303705, by rfl⟩ : syracuseStep 3239525 = 607411) (by norm_num)
theorem B2159683 : Blo 2159435 2159683 := bstep (se 1 (by rfl) ⟨1619762, by rfl⟩ : syracuseStep 2159683 = 3239525) B3239525
theorem B2306269 : Blo 2159435 2306269 := bbase (se 3 (by rfl) ⟨432425, by rfl⟩ : syracuseStep 2306269 = 864851) (by norm_num)
theorem B3075025 : Blo 2159435 3075025 := bstep (se 2 (by rfl) ⟨1153134, by rfl⟩ : syracuseStep 3075025 = 2306269) B2306269
theorem B4100033 : Blo 2159435 4100033 := bstep (se 2 (by rfl) ⟨1537512, by rfl⟩ : syracuseStep 4100033 = 3075025) B3075025
theorem B2733355 : Blo 2159435 2733355 := bstep (se 1 (by rfl) ⟨2050016, by rfl⟩ : syracuseStep 2733355 = 4100033) B4100033
theorem B3644473 : Blo 2159435 3644473 := bstep (se 2 (by rfl) ⟨1366677, by rfl⟩ : syracuseStep 3644473 = 2733355) B2733355
theorem B4859297 : Blo 2159435 4859297 := bstep (se 2 (by rfl) ⟨1822236, by rfl⟩ : syracuseStep 4859297 = 3644473) B3644473
theorem B3239531 : Blo 2159435 3239531 := bstep (se 1 (by rfl) ⟨2429648, by rfl⟩ : syracuseStep 3239531 = 4859297) B4859297
theorem B2159687 : Blo 2159435 2159687 := bstep (se 1 (by rfl) ⟨1619765, by rfl⟩ : syracuseStep 2159687 = 3239531) B3239531
theorem B2429653 : Blo 2159435 2429653 := bbase (se 7 (by rfl) ⟨28472, by rfl⟩ : syracuseStep 2429653 = 56945) (by norm_num)
theorem B3239537 : Blo 2159435 3239537 := bstep (se 2 (by rfl) ⟨1214826, by rfl⟩ : syracuseStep 3239537 = 2429653) B2429653
theorem B2159691 : Blo 2159435 2159691 := bstep (se 1 (by rfl) ⟨1619768, by rfl⟩ : syracuseStep 2159691 = 3239537) B3239537
theorem B2733365 : Blo 2159435 2733365 := bbase (se 5 (by rfl) ⟨128126, by rfl⟩ : syracuseStep 2733365 = 256253) (by norm_num)
theorem B7288973 : Blo 2159435 7288973 := bstep (se 3 (by rfl) ⟨1366682, by rfl⟩ : syracuseStep 7288973 = 2733365) B2733365
theorem B4859315 : Blo 2159435 4859315 := bstep (se 1 (by rfl) ⟨3644486, by rfl⟩ : syracuseStep 4859315 = 7288973) B7288973
theorem B3239543 : Blo 2159435 3239543 := bstep (se 1 (by rfl) ⟨2429657, by rfl⟩ : syracuseStep 3239543 = 4859315) B4859315
theorem B2159695 : Blo 2159435 2159695 := bstep (se 1 (by rfl) ⟨1619771, by rfl⟩ : syracuseStep 2159695 = 3239543) B3239543
theorem B3239549 : Blo 2159435 3239549 := bbase (se 3 (by rfl) ⟨607415, by rfl⟩ : syracuseStep 3239549 = 1214831) (by norm_num)
theorem B2159699 : Blo 2159435 2159699 := bstep (se 1 (by rfl) ⟨1619774, by rfl⟩ : syracuseStep 2159699 = 3239549) B3239549
theorem B4859333 : Blo 2159435 4859333 := bbase (se 4 (by rfl) ⟨455562, by rfl⟩ : syracuseStep 4859333 = 911125) (by norm_num)
theorem B3239555 : Blo 2159435 3239555 := bstep (se 1 (by rfl) ⟨2429666, by rfl⟩ : syracuseStep 3239555 = 4859333) B4859333
theorem B2159703 : Blo 2159435 2159703 := bstep (se 1 (by rfl) ⟨1619777, by rfl⟩ : syracuseStep 2159703 = 3239555) B3239555
theorem B4378349 : Blo 2159435 4378349 := bbase (se 3 (by rfl) ⟨820940, by rfl⟩ : syracuseStep 4378349 = 1641881) (by norm_num)
theorem B2918899 : Blo 2159435 2918899 := bstep (se 1 (by rfl) ⟨2189174, by rfl⟩ : syracuseStep 2918899 = 4378349) B4378349
theorem B15567461 : Blo 2159435 15567461 := bstep (se 4 (by rfl) ⟨1459449, by rfl⟩ : syracuseStep 15567461 = 2918899) B2918899
theorem B10378307 : Blo 2159435 10378307 := bstep (se 1 (by rfl) ⟨7783730, by rfl⟩ : syracuseStep 10378307 = 15567461) B15567461
theorem B6918871 : Blo 2159435 6918871 := bstep (se 1 (by rfl) ⟨5189153, by rfl⟩ : syracuseStep 6918871 = 10378307) B10378307
theorem B9225161 : Blo 2159435 9225161 := bstep (se 2 (by rfl) ⟨3459435, by rfl⟩ : syracuseStep 9225161 = 6918871) B6918871
theorem B6150107 : Blo 2159435 6150107 := bstep (se 1 (by rfl) ⟨4612580, by rfl⟩ : syracuseStep 6150107 = 9225161) B9225161
theorem B4100071 : Blo 2159435 4100071 := bstep (se 1 (by rfl) ⟨3075053, by rfl⟩ : syracuseStep 4100071 = 6150107) B6150107
theorem B5466761 : Blo 2159435 5466761 := bstep (se 2 (by rfl) ⟨2050035, by rfl⟩ : syracuseStep 5466761 = 4100071) B4100071
theorem B3644507 : Blo 2159435 3644507 := bstep (se 1 (by rfl) ⟨2733380, by rfl⟩ : syracuseStep 3644507 = 5466761) B5466761
theorem B2429671 : Blo 2159435 2429671 := bstep (se 1 (by rfl) ⟨1822253, by rfl⟩ : syracuseStep 2429671 = 3644507) B3644507
theorem B3239561 : Blo 2159435 3239561 := bstep (se 2 (by rfl) ⟨1214835, by rfl⟩ : syracuseStep 3239561 = 2429671) B2429671
theorem B2159707 : Blo 2159435 2159707 := bstep (se 1 (by rfl) ⟨1619780, by rfl⟩ : syracuseStep 2159707 = 3239561) B3239561
theorem B10933541 : Blo 2159435 10933541 := bbase (se 4 (by rfl) ⟨1025019, by rfl⟩ : syracuseStep 10933541 = 2050039) (by norm_num)
theorem B7289027 : Blo 2159435 7289027 := bstep (se 1 (by rfl) ⟨5466770, by rfl⟩ : syracuseStep 7289027 = 10933541) B10933541
theorem B4859351 : Blo 2159435 4859351 := bstep (se 1 (by rfl) ⟨3644513, by rfl⟩ : syracuseStep 4859351 = 7289027) B7289027
theorem B3239567 : Blo 2159435 3239567 := bstep (se 1 (by rfl) ⟨2429675, by rfl⟩ : syracuseStep 3239567 = 4859351) B4859351
theorem B2159711 : Blo 2159435 2159711 := bstep (se 1 (by rfl) ⟨1619783, by rfl⟩ : syracuseStep 2159711 = 3239567) B3239567
theorem B3239573 : Blo 2159435 3239573 := bbase (se 6 (by rfl) ⟨75927, by rfl⟩ : syracuseStep 3239573 = 151855) (by norm_num)
theorem B2159715 : Blo 2159435 2159715 := bstep (se 1 (by rfl) ⟨1619786, by rfl⟩ : syracuseStep 2159715 = 3239573) B3239573
theorem B4925669 : Blo 2159435 4925669 := bbase (se 4 (by rfl) ⟨461781, by rfl⟩ : syracuseStep 4925669 = 923563) (by norm_num)
theorem B13135117 : Blo 2159435 13135117 := bstep (se 3 (by rfl) ⟨2462834, by rfl⟩ : syracuseStep 13135117 = 4925669) B4925669
theorem B17513489 : Blo 2159435 17513489 := bstep (se 2 (by rfl) ⟨6567558, by rfl⟩ : syracuseStep 17513489 = 13135117) B13135117
theorem B11675659 : Blo 2159435 11675659 := bstep (se 1 (by rfl) ⟨8756744, by rfl⟩ : syracuseStep 11675659 = 17513489) B17513489
theorem B15567545 : Blo 2159435 15567545 := bstep (se 2 (by rfl) ⟨5837829, by rfl⟩ : syracuseStep 15567545 = 11675659) B11675659
theorem B10378363 : Blo 2159435 10378363 := bstep (se 1 (by rfl) ⟨7783772, by rfl⟩ : syracuseStep 10378363 = 15567545) B15567545
theorem B13837817 : Blo 2159435 13837817 := bstep (se 2 (by rfl) ⟨5189181, by rfl⟩ : syracuseStep 13837817 = 10378363) B10378363
theorem B9225211 : Blo 2159435 9225211 := bstep (se 1 (by rfl) ⟨6918908, by rfl⟩ : syracuseStep 9225211 = 13837817) B13837817
theorem B12300281 : Blo 2159435 12300281 := bstep (se 2 (by rfl) ⟨4612605, by rfl⟩ : syracuseStep 12300281 = 9225211) B9225211
theorem B8200187 : Blo 2159435 8200187 := bstep (se 1 (by rfl) ⟨6150140, by rfl⟩ : syracuseStep 8200187 = 12300281) B12300281
theorem B5466791 : Blo 2159435 5466791 := bstep (se 1 (by rfl) ⟨4100093, by rfl⟩ : syracuseStep 5466791 = 8200187) B8200187
theorem B3644527 : Blo 2159435 3644527 := bstep (se 1 (by rfl) ⟨2733395, by rfl⟩ : syracuseStep 3644527 = 5466791) B5466791
theorem B4859369 : Blo 2159435 4859369 := bstep (se 2 (by rfl) ⟨1822263, by rfl⟩ : syracuseStep 4859369 = 3644527) B3644527
theorem B3239579 : Blo 2159435 3239579 := bstep (se 1 (by rfl) ⟨2429684, by rfl⟩ : syracuseStep 3239579 = 4859369) B4859369
theorem B2159719 : Blo 2159435 2159719 := bstep (se 1 (by rfl) ⟨1619789, by rfl⟩ : syracuseStep 2159719 = 3239579) B3239579
theorem B2429689 : Blo 2159435 2429689 := bbase (se 2 (by rfl) ⟨911133, by rfl⟩ : syracuseStep 2429689 = 1822267) (by norm_num)
theorem B3239585 : Blo 2159435 3239585 := bstep (se 2 (by rfl) ⟨1214844, by rfl⟩ : syracuseStep 3239585 = 2429689) B2429689
theorem B2159723 : Blo 2159435 2159723 := bstep (se 1 (by rfl) ⟨1619792, by rfl⟩ : syracuseStep 2159723 = 3239585) B3239585
theorem B3891901 : Blo 2159435 3891901 := bbase (se 3 (by rfl) ⟨729731, by rfl⟩ : syracuseStep 3891901 = 1459463) (by norm_num)
theorem B5189201 : Blo 2159435 5189201 := bstep (se 2 (by rfl) ⟨1945950, by rfl⟩ : syracuseStep 5189201 = 3891901) B3891901
theorem B3459467 : Blo 2159435 3459467 := bstep (se 1 (by rfl) ⟨2594600, by rfl⟩ : syracuseStep 3459467 = 5189201) B5189201
theorem B9225245 : Blo 2159435 9225245 := bstep (se 3 (by rfl) ⟨1729733, by rfl⟩ : syracuseStep 9225245 = 3459467) B3459467
theorem B6150163 : Blo 2159435 6150163 := bstep (se 1 (by rfl) ⟨4612622, by rfl⟩ : syracuseStep 6150163 = 9225245) B9225245
theorem B8200217 : Blo 2159435 8200217 := bstep (se 2 (by rfl) ⟨3075081, by rfl⟩ : syracuseStep 8200217 = 6150163) B6150163
theorem B5466811 : Blo 2159435 5466811 := bstep (se 1 (by rfl) ⟨4100108, by rfl⟩ : syracuseStep 5466811 = 8200217) B8200217
theorem B7289081 : Blo 2159435 7289081 := bstep (se 2 (by rfl) ⟨2733405, by rfl⟩ : syracuseStep 7289081 = 5466811) B5466811
theorem B4859387 : Blo 2159435 4859387 := bstep (se 1 (by rfl) ⟨3644540, by rfl⟩ : syracuseStep 4859387 = 7289081) B7289081
theorem B3239591 : Blo 2159435 3239591 := bstep (se 1 (by rfl) ⟨2429693, by rfl⟩ : syracuseStep 3239591 = 4859387) B4859387
theorem B2159727 : Blo 2159435 2159727 := bstep (se 1 (by rfl) ⟨1619795, by rfl⟩ : syracuseStep 2159727 = 3239591) B3239591
theorem B3239597 : Blo 2159435 3239597 := bbase (se 3 (by rfl) ⟨607424, by rfl⟩ : syracuseStep 3239597 = 1214849) (by norm_num)
theorem B2159731 : Blo 2159435 2159731 := bstep (se 1 (by rfl) ⟨1619798, by rfl⟩ : syracuseStep 2159731 = 3239597) B3239597
theorem B4859405 : Blo 2159435 4859405 := bbase (se 3 (by rfl) ⟨911138, by rfl⟩ : syracuseStep 4859405 = 1822277) (by norm_num)
theorem B3239603 : Blo 2159435 3239603 := bstep (se 1 (by rfl) ⟨2429702, by rfl⟩ : syracuseStep 3239603 = 4859405) B4859405
theorem B2159735 : Blo 2159435 2159735 := bstep (se 1 (by rfl) ⟨1619801, by rfl⟩ : syracuseStep 2159735 = 3239603) B3239603
theorem B2733421 : Blo 2159435 2733421 := bbase (se 3 (by rfl) ⟨512516, by rfl⟩ : syracuseStep 2733421 = 1025033) (by norm_num)
theorem B3644561 : Blo 2159435 3644561 := bstep (se 2 (by rfl) ⟨1366710, by rfl⟩ : syracuseStep 3644561 = 2733421) B2733421
theorem B2429707 : Blo 2159435 2429707 := bstep (se 1 (by rfl) ⟨1822280, by rfl⟩ : syracuseStep 2429707 = 3644561) B3644561
theorem B3239609 : Blo 2159435 3239609 := bstep (se 2 (by rfl) ⟨1214853, by rfl⟩ : syracuseStep 3239609 = 2429707) B2429707
theorem B2159739 : Blo 2159435 2159739 := bstep (se 1 (by rfl) ⟨1619804, by rfl⟩ : syracuseStep 2159739 = 3239609) B3239609
theorem B4378421 : Blo 2159435 4378421 := bbase (se 5 (by rfl) ⟨205238, by rfl⟩ : syracuseStep 4378421 = 410477) (by norm_num)
theorem B2918947 : Blo 2159435 2918947 := bstep (se 1 (by rfl) ⟨2189210, by rfl⟩ : syracuseStep 2918947 = 4378421) B4378421
theorem B3891929 : Blo 2159435 3891929 := bstep (se 2 (by rfl) ⟨1459473, by rfl⟩ : syracuseStep 3891929 = 2918947) B2918947
theorem B10378477 : Blo 2159435 10378477 := bstep (se 3 (by rfl) ⟨1945964, by rfl⟩ : syracuseStep 10378477 = 3891929) B3891929
theorem B13837969 : Blo 2159435 13837969 := bstep (se 2 (by rfl) ⟨5189238, by rfl⟩ : syracuseStep 13837969 = 10378477) B10378477
theorem B18450625 : Blo 2159435 18450625 := bstep (se 2 (by rfl) ⟨6918984, by rfl⟩ : syracuseStep 18450625 = 13837969) B13837969
theorem B24600833 : Blo 2159435 24600833 := bstep (se 2 (by rfl) ⟨9225312, by rfl⟩ : syracuseStep 24600833 = 18450625) B18450625
theorem B16400555 : Blo 2159435 16400555 := bstep (se 1 (by rfl) ⟨12300416, by rfl⟩ : syracuseStep 16400555 = 24600833) B24600833
theorem B10933703 : Blo 2159435 10933703 := bstep (se 1 (by rfl) ⟨8200277, by rfl⟩ : syracuseStep 10933703 = 16400555) B16400555
theorem B7289135 : Blo 2159435 7289135 := bstep (se 1 (by rfl) ⟨5466851, by rfl⟩ : syracuseStep 7289135 = 10933703) B10933703
theorem B4859423 : Blo 2159435 4859423 := bstep (se 1 (by rfl) ⟨3644567, by rfl⟩ : syracuseStep 4859423 = 7289135) B7289135
theorem B3239615 : Blo 2159435 3239615 := bstep (se 1 (by rfl) ⟨2429711, by rfl⟩ : syracuseStep 3239615 = 4859423) B4859423
theorem B2159743 : Blo 2159435 2159743 := bstep (se 1 (by rfl) ⟨1619807, by rfl⟩ : syracuseStep 2159743 = 3239615) B3239615
theorem B3239621 : Blo 2159435 3239621 := bbase (se 4 (by rfl) ⟨303714, by rfl⟩ : syracuseStep 3239621 = 607429) (by norm_num)
theorem B2159747 : Blo 2159435 2159747 := bstep (se 1 (by rfl) ⟨1619810, by rfl⟩ : syracuseStep 2159747 = 3239621) B3239621
theorem B3644581 : Blo 2159435 3644581 := bbase (se 4 (by rfl) ⟨341679, by rfl⟩ : syracuseStep 3644581 = 683359) (by norm_num)
theorem B4859441 : Blo 2159435 4859441 := bstep (se 2 (by rfl) ⟨1822290, by rfl⟩ : syracuseStep 4859441 = 3644581) B3644581
theorem B3239627 : Blo 2159435 3239627 := bstep (se 1 (by rfl) ⟨2429720, by rfl⟩ : syracuseStep 3239627 = 4859441) B4859441
theorem B2159751 : Blo 2159435 2159751 := bstep (se 1 (by rfl) ⟨1619813, by rfl⟩ : syracuseStep 2159751 = 3239627) B3239627
theorem B2429725 : Blo 2159435 2429725 := bbase (se 3 (by rfl) ⟨455573, by rfl⟩ : syracuseStep 2429725 = 911147) (by norm_num)
theorem B3239633 : Blo 2159435 3239633 := bstep (se 2 (by rfl) ⟨1214862, by rfl⟩ : syracuseStep 3239633 = 2429725) B2429725
theorem B2159755 : Blo 2159435 2159755 := bstep (se 1 (by rfl) ⟨1619816, by rfl⟩ : syracuseStep 2159755 = 3239633) B3239633
theorem B7289189 : Blo 2159435 7289189 := bbase (se 4 (by rfl) ⟨683361, by rfl⟩ : syracuseStep 7289189 = 1366723) (by norm_num)
theorem B4859459 : Blo 2159435 4859459 := bstep (se 1 (by rfl) ⟨3644594, by rfl⟩ : syracuseStep 4859459 = 7289189) B7289189
theorem B3239639 : Blo 2159435 3239639 := bstep (se 1 (by rfl) ⟨2429729, by rfl⟩ : syracuseStep 3239639 = 4859459) B4859459
theorem B2159759 : Blo 2159435 2159759 := bstep (se 1 (by rfl) ⟨1619819, by rfl⟩ : syracuseStep 2159759 = 3239639) B3239639
theorem B3239645 : Blo 2159435 3239645 := bbase (se 3 (by rfl) ⟨607433, by rfl⟩ : syracuseStep 3239645 = 1214867) (by norm_num)
theorem B2159763 : Blo 2159435 2159763 := bstep (se 1 (by rfl) ⟨1619822, by rfl⟩ : syracuseStep 2159763 = 3239645) B3239645
theorem B4859477 : Blo 2159435 4859477 := bbase (se 8 (by rfl) ⟨28473, by rfl⟩ : syracuseStep 4859477 = 56947) (by norm_num)
theorem B3239651 : Blo 2159435 3239651 := bstep (se 1 (by rfl) ⟨2429738, by rfl⟩ : syracuseStep 3239651 = 4859477) B4859477
theorem B2159767 : Blo 2159435 2159767 := bstep (se 1 (by rfl) ⟨1619825, by rfl⟩ : syracuseStep 2159767 = 3239651) B3239651
theorem B4612717 : Blo 2159435 4612717 := bbase (se 3 (by rfl) ⟨864884, by rfl⟩ : syracuseStep 4612717 = 1729769) (by norm_num)
theorem B6150289 : Blo 2159435 6150289 := bstep (se 2 (by rfl) ⟨2306358, by rfl⟩ : syracuseStep 6150289 = 4612717) B4612717
theorem B8200385 : Blo 2159435 8200385 := bstep (se 2 (by rfl) ⟨3075144, by rfl⟩ : syracuseStep 8200385 = 6150289) B6150289
theorem B5466923 : Blo 2159435 5466923 := bstep (se 1 (by rfl) ⟨4100192, by rfl⟩ : syracuseStep 5466923 = 8200385) B8200385
theorem B3644615 : Blo 2159435 3644615 := bstep (se 1 (by rfl) ⟨2733461, by rfl⟩ : syracuseStep 3644615 = 5466923) B5466923
theorem B2429743 : Blo 2159435 2429743 := bstep (se 1 (by rfl) ⟨1822307, by rfl⟩ : syracuseStep 2429743 = 3644615) B3644615
theorem B3239657 : Blo 2159435 3239657 := bstep (se 2 (by rfl) ⟨1214871, by rfl⟩ : syracuseStep 3239657 = 2429743) B2429743
theorem B2159771 : Blo 2159435 2159771 := bstep (se 1 (by rfl) ⟨1619828, by rfl⟩ : syracuseStep 2159771 = 3239657) B3239657
theorem B17513941 : Blo 2159435 17513941 := bbase (se 7 (by rfl) ⟨205241, by rfl⟩ : syracuseStep 17513941 = 410483) (by norm_num)
theorem B23351921 : Blo 2159435 23351921 := bstep (se 2 (by rfl) ⟨8756970, by rfl⟩ : syracuseStep 23351921 = 17513941) B17513941
theorem B15567947 : Blo 2159435 15567947 := bstep (se 1 (by rfl) ⟨11675960, by rfl⟩ : syracuseStep 15567947 = 23351921) B23351921
theorem B10378631 : Blo 2159435 10378631 := bstep (se 1 (by rfl) ⟨7783973, by rfl⟩ : syracuseStep 10378631 = 15567947) B15567947
theorem B27676349 : Blo 2159435 27676349 := bstep (se 3 (by rfl) ⟨5189315, by rfl⟩ : syracuseStep 27676349 = 10378631) B10378631
theorem B18450899 : Blo 2159435 18450899 := bstep (se 1 (by rfl) ⟨13838174, by rfl⟩ : syracuseStep 18450899 = 27676349) B27676349
theorem B12300599 : Blo 2159435 12300599 := bstep (se 1 (by rfl) ⟨9225449, by rfl⟩ : syracuseStep 12300599 = 18450899) B18450899
theorem B8200399 : Blo 2159435 8200399 := bstep (se 1 (by rfl) ⟨6150299, by rfl⟩ : syracuseStep 8200399 = 12300599) B12300599
theorem B10933865 : Blo 2159435 10933865 := bstep (se 2 (by rfl) ⟨4100199, by rfl⟩ : syracuseStep 10933865 = 8200399) B8200399
theorem B7289243 : Blo 2159435 7289243 := bstep (se 1 (by rfl) ⟨5466932, by rfl⟩ : syracuseStep 7289243 = 10933865) B10933865
theorem B4859495 : Blo 2159435 4859495 := bstep (se 1 (by rfl) ⟨3644621, by rfl⟩ : syracuseStep 4859495 = 7289243) B7289243
theorem B3239663 : Blo 2159435 3239663 := bstep (se 1 (by rfl) ⟨2429747, by rfl⟩ : syracuseStep 3239663 = 4859495) B4859495
theorem B2159775 : Blo 2159435 2159775 := bstep (se 1 (by rfl) ⟨1619831, by rfl⟩ : syracuseStep 2159775 = 3239663) B3239663
theorem B3239669 : Blo 2159435 3239669 := bbase (se 5 (by rfl) ⟨151859, by rfl⟩ : syracuseStep 3239669 = 303719) (by norm_num)
theorem B2159779 : Blo 2159435 2159779 := bstep (se 1 (by rfl) ⟨1619834, by rfl⟩ : syracuseStep 2159779 = 3239669) B3239669
theorem B3459557 : Blo 2159435 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B9225485 : Blo 2159435 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B6150323 : Blo 2159435 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4100215 : Blo 2159435 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B5466953 : Blo 2159435 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B3644635 : Blo 2159435 3644635 := bstep (se 1 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 3644635 = 5466953) B5466953
theorem B4859513 : Blo 2159435 4859513 := bstep (se 2 (by rfl) ⟨1822317, by rfl⟩ : syracuseStep 4859513 = 3644635) B3644635
theorem B3239675 : Blo 2159435 3239675 := bstep (se 1 (by rfl) ⟨2429756, by rfl⟩ : syracuseStep 3239675 = 4859513) B4859513
theorem B2159783 : Blo 2159435 2159783 := bstep (se 1 (by rfl) ⟨1619837, by rfl⟩ : syracuseStep 2159783 = 3239675) B3239675
theorem B2429761 : Blo 2159435 2429761 := bbase (se 2 (by rfl) ⟨911160, by rfl⟩ : syracuseStep 2429761 = 1822321) (by norm_num)
theorem B3239681 : Blo 2159435 3239681 := bstep (se 2 (by rfl) ⟨1214880, by rfl⟩ : syracuseStep 3239681 = 2429761) B2429761
theorem B2159787 : Blo 2159435 2159787 := bstep (se 1 (by rfl) ⟨1619840, by rfl⟩ : syracuseStep 2159787 = 3239681) B3239681
theorem B5466973 : Blo 2159435 5466973 := bbase (se 3 (by rfl) ⟨1025057, by rfl⟩ : syracuseStep 5466973 = 2050115) (by norm_num)
theorem B7289297 : Blo 2159435 7289297 := bstep (se 2 (by rfl) ⟨2733486, by rfl⟩ : syracuseStep 7289297 = 5466973) B5466973
theorem B4859531 : Blo 2159435 4859531 := bstep (se 1 (by rfl) ⟨3644648, by rfl⟩ : syracuseStep 4859531 = 7289297) B7289297
theorem B3239687 : Blo 2159435 3239687 := bstep (se 1 (by rfl) ⟨2429765, by rfl⟩ : syracuseStep 3239687 = 4859531) B4859531
theorem B2159791 : Blo 2159435 2159791 := bstep (se 1 (by rfl) ⟨1619843, by rfl⟩ : syracuseStep 2159791 = 3239687) B3239687
theorem B3239693 : Blo 2159435 3239693 := bbase (se 3 (by rfl) ⟨607442, by rfl⟩ : syracuseStep 3239693 = 1214885) (by norm_num)
theorem B2159795 : Blo 2159435 2159795 := bstep (se 1 (by rfl) ⟨1619846, by rfl⟩ : syracuseStep 2159795 = 3239693) B3239693
theorem B4859549 : Blo 2159435 4859549 := bbase (se 3 (by rfl) ⟨911165, by rfl⟩ : syracuseStep 4859549 = 1822331) (by norm_num)
theorem B3239699 : Blo 2159435 3239699 := bstep (se 1 (by rfl) ⟨2429774, by rfl⟩ : syracuseStep 3239699 = 4859549) B4859549
theorem B2159799 : Blo 2159435 2159799 := bstep (se 1 (by rfl) ⟨1619849, by rfl⟩ : syracuseStep 2159799 = 3239699) B3239699
theorem B3644669 : Blo 2159435 3644669 := bbase (se 3 (by rfl) ⟨683375, by rfl⟩ : syracuseStep 3644669 = 1366751) (by norm_num)
theorem B2429779 : Blo 2159435 2429779 := bstep (se 1 (by rfl) ⟨1822334, by rfl⟩ : syracuseStep 2429779 = 3644669) B3644669
theorem B3239705 : Blo 2159435 3239705 := bstep (se 2 (by rfl) ⟨1214889, by rfl⟩ : syracuseStep 3239705 = 2429779) B2429779
theorem B2159803 : Blo 2159435 2159803 := bstep (se 1 (by rfl) ⟨1619852, by rfl⟩ : syracuseStep 2159803 = 3239705) B3239705
theorem B3892045 : Blo 2159435 3892045 := bbase (se 3 (by rfl) ⟨729758, by rfl⟩ : syracuseStep 3892045 = 1459517) (by norm_num)
theorem B5189393 : Blo 2159435 5189393 := bstep (se 2 (by rfl) ⟨1946022, by rfl⟩ : syracuseStep 5189393 = 3892045) B3892045
theorem B3459595 : Blo 2159435 3459595 := bstep (se 1 (by rfl) ⟨2594696, by rfl⟩ : syracuseStep 3459595 = 5189393) B5189393
theorem B4612793 : Blo 2159435 4612793 := bstep (se 2 (by rfl) ⟨1729797, by rfl⟩ : syracuseStep 4612793 = 3459595) B3459595
theorem B12300781 : Blo 2159435 12300781 := bstep (se 3 (by rfl) ⟨2306396, by rfl⟩ : syracuseStep 12300781 = 4612793) B4612793
theorem B16401041 : Blo 2159435 16401041 := bstep (se 2 (by rfl) ⟨6150390, by rfl⟩ : syracuseStep 16401041 = 12300781) B12300781
theorem B10934027 : Blo 2159435 10934027 := bstep (se 1 (by rfl) ⟨8200520, by rfl⟩ : syracuseStep 10934027 = 16401041) B16401041
theorem B7289351 : Blo 2159435 7289351 := bstep (se 1 (by rfl) ⟨5467013, by rfl⟩ : syracuseStep 7289351 = 10934027) B10934027
theorem B4859567 : Blo 2159435 4859567 := bstep (se 1 (by rfl) ⟨3644675, by rfl⟩ : syracuseStep 4859567 = 7289351) B7289351
theorem B3239711 : Blo 2159435 3239711 := bstep (se 1 (by rfl) ⟨2429783, by rfl⟩ : syracuseStep 3239711 = 4859567) B4859567
theorem B2159807 : Blo 2159435 2159807 := bstep (se 1 (by rfl) ⟨1619855, by rfl⟩ : syracuseStep 2159807 = 3239711) B3239711
theorem B3239717 : Blo 2159435 3239717 := bbase (se 4 (by rfl) ⟨303723, by rfl⟩ : syracuseStep 3239717 = 607447) (by norm_num)
theorem B2159811 : Blo 2159435 2159811 := bstep (se 1 (by rfl) ⟨1619858, by rfl⟩ : syracuseStep 2159811 = 3239717) B3239717
theorem B2733517 : Blo 2159435 2733517 := bbase (se 3 (by rfl) ⟨512534, by rfl⟩ : syracuseStep 2733517 = 1025069) (by norm_num)
theorem B3644689 : Blo 2159435 3644689 := bstep (se 2 (by rfl) ⟨1366758, by rfl⟩ : syracuseStep 3644689 = 2733517) B2733517
theorem B4859585 : Blo 2159435 4859585 := bstep (se 2 (by rfl) ⟨1822344, by rfl⟩ : syracuseStep 4859585 = 3644689) B3644689
theorem B3239723 : Blo 2159435 3239723 := bstep (se 1 (by rfl) ⟨2429792, by rfl⟩ : syracuseStep 3239723 = 4859585) B4859585
theorem B2159815 : Blo 2159435 2159815 := bstep (se 1 (by rfl) ⟨1619861, by rfl⟩ : syracuseStep 2159815 = 3239723) B3239723
theorem B2429797 : Blo 2159435 2429797 := bbase (se 4 (by rfl) ⟨227793, by rfl⟩ : syracuseStep 2429797 = 455587) (by norm_num)
theorem B3239729 : Blo 2159435 3239729 := bstep (se 2 (by rfl) ⟨1214898, by rfl⟩ : syracuseStep 3239729 = 2429797) B2429797
theorem B2159819 : Blo 2159435 2159819 := bstep (se 1 (by rfl) ⟨1619864, by rfl⟩ : syracuseStep 2159819 = 3239729) B3239729
theorem B6150437 : Blo 2159435 6150437 := bbase (se 4 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 6150437 = 1153207) (by norm_num)
theorem B4100291 : Blo 2159435 4100291 := bstep (se 1 (by rfl) ⟨3075218, by rfl⟩ : syracuseStep 4100291 = 6150437) B6150437
theorem B2733527 : Blo 2159435 2733527 := bstep (se 1 (by rfl) ⟨2050145, by rfl⟩ : syracuseStep 2733527 = 4100291) B4100291
theorem B7289405 : Blo 2159435 7289405 := bstep (se 3 (by rfl) ⟨1366763, by rfl⟩ : syracuseStep 7289405 = 2733527) B2733527
theorem B4859603 : Blo 2159435 4859603 := bstep (se 1 (by rfl) ⟨3644702, by rfl⟩ : syracuseStep 4859603 = 7289405) B7289405
theorem B3239735 : Blo 2159435 3239735 := bstep (se 1 (by rfl) ⟨2429801, by rfl⟩ : syracuseStep 3239735 = 4859603) B4859603
theorem B2159823 : Blo 2159435 2159823 := bstep (se 1 (by rfl) ⟨1619867, by rfl⟩ : syracuseStep 2159823 = 3239735) B3239735
theorem B3239741 : Blo 2159435 3239741 := bbase (se 3 (by rfl) ⟨607451, by rfl⟩ : syracuseStep 3239741 = 1214903) (by norm_num)
theorem B2159827 : Blo 2159435 2159827 := bstep (se 1 (by rfl) ⟨1619870, by rfl⟩ : syracuseStep 2159827 = 3239741) B3239741
theorem B4859621 : Blo 2159435 4859621 := bbase (se 4 (by rfl) ⟨455589, by rfl⟩ : syracuseStep 4859621 = 911179) (by norm_num)
theorem B3239747 : Blo 2159435 3239747 := bstep (se 1 (by rfl) ⟨2429810, by rfl⟩ : syracuseStep 3239747 = 4859621) B4859621
theorem B2159831 : Blo 2159435 2159831 := bstep (se 1 (by rfl) ⟨1619873, by rfl⟩ : syracuseStep 2159831 = 3239747) B3239747
theorem B5467085 : Blo 2159435 5467085 := bbase (se 3 (by rfl) ⟨1025078, by rfl⟩ : syracuseStep 5467085 = 2050157) (by norm_num)
theorem B3644723 : Blo 2159435 3644723 := bstep (se 1 (by rfl) ⟨2733542, by rfl⟩ : syracuseStep 3644723 = 5467085) B5467085
theorem B2429815 : Blo 2159435 2429815 := bstep (se 1 (by rfl) ⟨1822361, by rfl⟩ : syracuseStep 2429815 = 3644723) B3644723
theorem B3239753 : Blo 2159435 3239753 := bstep (se 2 (by rfl) ⟨1214907, by rfl⟩ : syracuseStep 3239753 = 2429815) B2429815
theorem B2159835 : Blo 2159435 2159835 := bstep (se 1 (by rfl) ⟨1619876, by rfl⟩ : syracuseStep 2159835 = 3239753) B3239753
theorem B26271701 : Blo 2159435 26271701 := bbase (se 7 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 26271701 = 615743) (by norm_num)
theorem B17514467 : Blo 2159435 17514467 := bstep (se 1 (by rfl) ⟨13135850, by rfl⟩ : syracuseStep 17514467 = 26271701) B26271701
theorem B11676311 : Blo 2159435 11676311 := bstep (se 1 (by rfl) ⟨8757233, by rfl⟩ : syracuseStep 11676311 = 17514467) B17514467
theorem B7784207 : Blo 2159435 7784207 := bstep (se 1 (by rfl) ⟨5838155, by rfl⟩ : syracuseStep 7784207 = 11676311) B11676311
theorem B5189471 : Blo 2159435 5189471 := bstep (se 1 (by rfl) ⟨3892103, by rfl⟩ : syracuseStep 5189471 = 7784207) B7784207
theorem B3459647 : Blo 2159435 3459647 := bstep (se 1 (by rfl) ⟨2594735, by rfl⟩ : syracuseStep 3459647 = 5189471) B5189471
theorem B2306431 : Blo 2159435 2306431 := bstep (se 1 (by rfl) ⟨1729823, by rfl⟩ : syracuseStep 2306431 = 3459647) B3459647
theorem B3075241 : Blo 2159435 3075241 := bstep (se 2 (by rfl) ⟨1153215, by rfl⟩ : syracuseStep 3075241 = 2306431) B2306431
theorem B4100321 : Blo 2159435 4100321 := bstep (se 2 (by rfl) ⟨1537620, by rfl⟩ : syracuseStep 4100321 = 3075241) B3075241
theorem B10934189 : Blo 2159435 10934189 := bstep (se 3 (by rfl) ⟨2050160, by rfl⟩ : syracuseStep 10934189 = 4100321) B4100321
theorem B7289459 : Blo 2159435 7289459 := bstep (se 1 (by rfl) ⟨5467094, by rfl⟩ : syracuseStep 7289459 = 10934189) B10934189
theorem B4859639 : Blo 2159435 4859639 := bstep (se 1 (by rfl) ⟨3644729, by rfl⟩ : syracuseStep 4859639 = 7289459) B7289459
theorem B3239759 : Blo 2159435 3239759 := bstep (se 1 (by rfl) ⟨2429819, by rfl⟩ : syracuseStep 3239759 = 4859639) B4859639
theorem B2159839 : Blo 2159435 2159839 := bstep (se 1 (by rfl) ⟨1619879, by rfl⟩ : syracuseStep 2159839 = 3239759) B3239759
theorem B3239765 : Blo 2159435 3239765 := bbase (se 9 (by rfl) ⟨9491, by rfl⟩ : syracuseStep 3239765 = 18983) (by norm_num)
theorem B2159843 : Blo 2159435 2159843 := bstep (se 1 (by rfl) ⟨1619882, by rfl⟩ : syracuseStep 2159843 = 3239765) B3239765
theorem B15568469 : Blo 2159435 15568469 := bbase (se 8 (by rfl) ⟨91221, by rfl⟩ : syracuseStep 15568469 = 182443) (by norm_num)
theorem B10378979 : Blo 2159435 10378979 := bstep (se 1 (by rfl) ⟨7784234, by rfl⟩ : syracuseStep 10378979 = 15568469) B15568469
theorem B6919319 : Blo 2159435 6919319 := bstep (se 1 (by rfl) ⟨5189489, by rfl⟩ : syracuseStep 6919319 = 10378979) B10378979
theorem B4612879 : Blo 2159435 4612879 := bstep (se 1 (by rfl) ⟨3459659, by rfl⟩ : syracuseStep 4612879 = 6919319) B6919319
theorem B6150505 : Blo 2159435 6150505 := bstep (se 2 (by rfl) ⟨2306439, by rfl⟩ : syracuseStep 6150505 = 4612879) B4612879
theorem B8200673 : Blo 2159435 8200673 := bstep (se 2 (by rfl) ⟨3075252, by rfl⟩ : syracuseStep 8200673 = 6150505) B6150505
theorem B5467115 : Blo 2159435 5467115 := bstep (se 1 (by rfl) ⟨4100336, by rfl⟩ : syracuseStep 5467115 = 8200673) B8200673
theorem B3644743 : Blo 2159435 3644743 := bstep (se 1 (by rfl) ⟨2733557, by rfl⟩ : syracuseStep 3644743 = 5467115) B5467115
theorem B4859657 : Blo 2159435 4859657 := bstep (se 2 (by rfl) ⟨1822371, by rfl⟩ : syracuseStep 4859657 = 3644743) B3644743
theorem B3239771 : Blo 2159435 3239771 := bstep (se 1 (by rfl) ⟨2429828, by rfl⟩ : syracuseStep 3239771 = 4859657) B4859657
theorem B2159847 : Blo 2159435 2159847 := bstep (se 1 (by rfl) ⟨1619885, by rfl⟩ : syracuseStep 2159847 = 3239771) B3239771
theorem B2429833 : Blo 2159435 2429833 := bbase (se 2 (by rfl) ⟨911187, by rfl⟩ : syracuseStep 2429833 = 1822375) (by norm_num)
theorem B3239777 : Blo 2159435 3239777 := bstep (se 2 (by rfl) ⟨1214916, by rfl⟩ : syracuseStep 3239777 = 2429833) B2429833
theorem B2159851 : Blo 2159435 2159851 := bstep (se 1 (by rfl) ⟨1619888, by rfl⟩ : syracuseStep 2159851 = 3239777) B3239777
theorem B2958925 : Blo 2159435 2958925 := bbase (se 3 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 2958925 = 1109597) (by norm_num)
theorem B3945233 : Blo 2159435 3945233 := bstep (se 2 (by rfl) ⟨1479462, by rfl⟩ : syracuseStep 3945233 = 2958925) B2958925
theorem B10520621 : Blo 2159435 10520621 := bstep (se 3 (by rfl) ⟨1972616, by rfl⟩ : syracuseStep 10520621 = 3945233) B3945233
theorem B7013747 : Blo 2159435 7013747 := bstep (se 1 (by rfl) ⟨5260310, by rfl⟩ : syracuseStep 7013747 = 10520621) B10520621
theorem B4675831 : Blo 2159435 4675831 := bstep (se 1 (by rfl) ⟨3506873, by rfl⟩ : syracuseStep 4675831 = 7013747) B7013747
theorem B99751061 : Blo 2159435 99751061 := bstep (se 6 (by rfl) ⟨2337915, by rfl⟩ : syracuseStep 99751061 = 4675831) B4675831
theorem B266002829 : Blo 2159435 266002829 := bstep (se 3 (by rfl) ⟨49875530, by rfl⟩ : syracuseStep 266002829 = 99751061) B99751061
theorem B177335219 : Blo 2159435 177335219 := bstep (se 1 (by rfl) ⟨133001414, by rfl⟩ : syracuseStep 177335219 = 266002829) B266002829
theorem B118223479 : Blo 2159435 118223479 := bstep (se 1 (by rfl) ⟨88667609, by rfl⟩ : syracuseStep 118223479 = 177335219) B177335219
theorem B157631305 : Blo 2159435 157631305 := bstep (se 2 (by rfl) ⟨59111739, by rfl⟩ : syracuseStep 157631305 = 118223479) B118223479
theorem B210175073 : Blo 2159435 210175073 := bstep (se 2 (by rfl) ⟨78815652, by rfl⟩ : syracuseStep 210175073 = 157631305) B157631305
theorem B140116715 : Blo 2159435 140116715 := bstep (se 1 (by rfl) ⟨105087536, by rfl⟩ : syracuseStep 140116715 = 210175073) B210175073
theorem B93411143 : Blo 2159435 93411143 := bstep (se 1 (by rfl) ⟨70058357, by rfl⟩ : syracuseStep 93411143 = 140116715) B140116715
theorem B62274095 : Blo 2159435 62274095 := bstep (se 1 (by rfl) ⟨46705571, by rfl⟩ : syracuseStep 62274095 = 93411143) B93411143
theorem B41516063 : Blo 2159435 41516063 := bstep (se 1 (by rfl) ⟨31137047, by rfl⟩ : syracuseStep 41516063 = 62274095) B62274095
theorem B27677375 : Blo 2159435 27677375 := bstep (se 1 (by rfl) ⟨20758031, by rfl⟩ : syracuseStep 27677375 = 41516063) B41516063
theorem B18451583 : Blo 2159435 18451583 := bstep (se 1 (by rfl) ⟨13838687, by rfl⟩ : syracuseStep 18451583 = 27677375) B27677375
theorem B12301055 : Blo 2159435 12301055 := bstep (se 1 (by rfl) ⟨9225791, by rfl⟩ : syracuseStep 12301055 = 18451583) B18451583
theorem B8200703 : Blo 2159435 8200703 := bstep (se 1 (by rfl) ⟨6150527, by rfl⟩ : syracuseStep 8200703 = 12301055) B12301055
theorem B5467135 : Blo 2159435 5467135 := bstep (se 1 (by rfl) ⟨4100351, by rfl⟩ : syracuseStep 5467135 = 8200703) B8200703
theorem B7289513 : Blo 2159435 7289513 := bstep (se 2 (by rfl) ⟨2733567, by rfl⟩ : syracuseStep 7289513 = 5467135) B5467135
theorem B4859675 : Blo 2159435 4859675 := bstep (se 1 (by rfl) ⟨3644756, by rfl⟩ : syracuseStep 4859675 = 7289513) B7289513
theorem B3239783 : Blo 2159435 3239783 := bstep (se 1 (by rfl) ⟨2429837, by rfl⟩ : syracuseStep 3239783 = 4859675) B4859675
theorem B2159855 : Blo 2159435 2159855 := bstep (se 1 (by rfl) ⟨1619891, by rfl⟩ : syracuseStep 2159855 = 3239783) B3239783
theorem B3239789 : Blo 2159435 3239789 := bbase (se 3 (by rfl) ⟨607460, by rfl⟩ : syracuseStep 3239789 = 1214921) (by norm_num)
theorem B2159859 : Blo 2159435 2159859 := bstep (se 1 (by rfl) ⟨1619894, by rfl⟩ : syracuseStep 2159859 = 3239789) B3239789
theorem B4859693 : Blo 2159435 4859693 := bbase (se 3 (by rfl) ⟨911192, by rfl⟩ : syracuseStep 4859693 = 1822385) (by norm_num)
theorem B3239795 : Blo 2159435 3239795 := bstep (se 1 (by rfl) ⟨2429846, by rfl⟩ : syracuseStep 3239795 = 4859693) B4859693
theorem B2159863 : Blo 2159435 2159863 := bstep (se 1 (by rfl) ⟨1619897, by rfl⟩ : syracuseStep 2159863 = 3239795) B3239795
theorem B9225845 : Blo 2159435 9225845 := bbase (se 5 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 9225845 = 864923) (by norm_num)
theorem B6150563 : Blo 2159435 6150563 := bstep (se 1 (by rfl) ⟨4612922, by rfl⟩ : syracuseStep 6150563 = 9225845) B9225845
theorem B4100375 : Blo 2159435 4100375 := bstep (se 1 (by rfl) ⟨3075281, by rfl⟩ : syracuseStep 4100375 = 6150563) B6150563
theorem B2733583 : Blo 2159435 2733583 := bstep (se 1 (by rfl) ⟨2050187, by rfl⟩ : syracuseStep 2733583 = 4100375) B4100375
theorem B3644777 : Blo 2159435 3644777 := bstep (se 2 (by rfl) ⟨1366791, by rfl⟩ : syracuseStep 3644777 = 2733583) B2733583
theorem B2429851 : Blo 2159435 2429851 := bstep (se 1 (by rfl) ⟨1822388, by rfl⟩ : syracuseStep 2429851 = 3644777) B3644777
theorem B3239801 : Blo 2159435 3239801 := bstep (se 2 (by rfl) ⟨1214925, by rfl⟩ : syracuseStep 3239801 = 2429851) B2429851
theorem B2159867 : Blo 2159435 2159867 := bstep (se 1 (by rfl) ⟨1619900, by rfl⟩ : syracuseStep 2159867 = 3239801) B3239801
theorem B2594773 : Blo 2159435 2594773 := bbase (se 7 (by rfl) ⟨30407, by rfl⟩ : syracuseStep 2594773 = 60815) (by norm_num)
theorem B13838789 : Blo 2159435 13838789 := bstep (se 4 (by rfl) ⟨1297386, by rfl⟩ : syracuseStep 13838789 = 2594773) B2594773
theorem B36903437 : Blo 2159435 36903437 := bstep (se 3 (by rfl) ⟨6919394, by rfl⟩ : syracuseStep 36903437 = 13838789) B13838789
theorem B24602291 : Blo 2159435 24602291 := bstep (se 1 (by rfl) ⟨18451718, by rfl⟩ : syracuseStep 24602291 = 36903437) B36903437
theorem B16401527 : Blo 2159435 16401527 := bstep (se 1 (by rfl) ⟨12301145, by rfl⟩ : syracuseStep 16401527 = 24602291) B24602291
theorem B10934351 : Blo 2159435 10934351 := bstep (se 1 (by rfl) ⟨8200763, by rfl⟩ : syracuseStep 10934351 = 16401527) B16401527
theorem B7289567 : Blo 2159435 7289567 := bstep (se 1 (by rfl) ⟨5467175, by rfl⟩ : syracuseStep 7289567 = 10934351) B10934351
theorem B4859711 : Blo 2159435 4859711 := bstep (se 1 (by rfl) ⟨3644783, by rfl⟩ : syracuseStep 4859711 = 7289567) B7289567
theorem B3239807 : Blo 2159435 3239807 := bstep (se 1 (by rfl) ⟨2429855, by rfl⟩ : syracuseStep 3239807 = 4859711) B4859711
theorem B2159871 : Blo 2159435 2159871 := bstep (se 1 (by rfl) ⟨1619903, by rfl⟩ : syracuseStep 2159871 = 3239807) B3239807
theorem B3239813 : Blo 2159435 3239813 := bbase (se 4 (by rfl) ⟨303732, by rfl⟩ : syracuseStep 3239813 = 607465) (by norm_num)
theorem B2159875 : Blo 2159435 2159875 := bstep (se 1 (by rfl) ⟨1619906, by rfl⟩ : syracuseStep 2159875 = 3239813) B3239813
theorem B3644797 : Blo 2159435 3644797 := bbase (se 3 (by rfl) ⟨683399, by rfl⟩ : syracuseStep 3644797 = 1366799) (by norm_num)
theorem B4859729 : Blo 2159435 4859729 := bstep (se 2 (by rfl) ⟨1822398, by rfl⟩ : syracuseStep 4859729 = 3644797) B3644797
theorem B3239819 : Blo 2159435 3239819 := bstep (se 1 (by rfl) ⟨2429864, by rfl⟩ : syracuseStep 3239819 = 4859729) B4859729
theorem B2159879 : Blo 2159435 2159879 := bstep (se 1 (by rfl) ⟨1619909, by rfl⟩ : syracuseStep 2159879 = 3239819) B3239819
theorem B2429869 : Blo 2159435 2429869 := bbase (se 3 (by rfl) ⟨455600, by rfl⟩ : syracuseStep 2429869 = 911201) (by norm_num)
theorem B3239825 : Blo 2159435 3239825 := bstep (se 2 (by rfl) ⟨1214934, by rfl⟩ : syracuseStep 3239825 = 2429869) B2429869
theorem B2159883 : Blo 2159435 2159883 := bstep (se 1 (by rfl) ⟨1619912, by rfl⟩ : syracuseStep 2159883 = 3239825) B3239825
theorem B7289621 : Blo 2159435 7289621 := bbase (se 6 (by rfl) ⟨170850, by rfl⟩ : syracuseStep 7289621 = 341701) (by norm_num)
theorem B4859747 : Blo 2159435 4859747 := bstep (se 1 (by rfl) ⟨3644810, by rfl⟩ : syracuseStep 4859747 = 7289621) B7289621
theorem B3239831 : Blo 2159435 3239831 := bstep (se 1 (by rfl) ⟨2429873, by rfl⟩ : syracuseStep 3239831 = 4859747) B4859747
theorem B2159887 : Blo 2159435 2159887 := bstep (se 1 (by rfl) ⟨1619915, by rfl⟩ : syracuseStep 2159887 = 3239831) B3239831
theorem B3239837 : Blo 2159435 3239837 := bbase (se 3 (by rfl) ⟨607469, by rfl⟩ : syracuseStep 3239837 = 1214939) (by norm_num)
theorem B2159891 : Blo 2159435 2159891 := bstep (se 1 (by rfl) ⟨1619918, by rfl⟩ : syracuseStep 2159891 = 3239837) B3239837
theorem B4859765 : Blo 2159435 4859765 := bbase (se 5 (by rfl) ⟨227801, by rfl⟩ : syracuseStep 4859765 = 455603) (by norm_num)
theorem B3239843 : Blo 2159435 3239843 := bstep (se 1 (by rfl) ⟨2429882, by rfl⟩ : syracuseStep 3239843 = 4859765) B4859765
theorem B2159895 : Blo 2159435 2159895 := bstep (se 1 (by rfl) ⟨1619921, by rfl⟩ : syracuseStep 2159895 = 3239843) B3239843
theorem B3284053 : Blo 2159435 3284053 := bbase (se 8 (by rfl) ⟨19242, by rfl⟩ : syracuseStep 3284053 = 38485) (by norm_num)
theorem B17514949 : Blo 2159435 17514949 := bstep (se 4 (by rfl) ⟨1642026, by rfl⟩ : syracuseStep 17514949 = 3284053) B3284053
theorem B23353265 : Blo 2159435 23353265 := bstep (se 2 (by rfl) ⟨8757474, by rfl⟩ : syracuseStep 23353265 = 17514949) B17514949
theorem B15568843 : Blo 2159435 15568843 := bstep (se 1 (by rfl) ⟨11676632, by rfl⟩ : syracuseStep 15568843 = 23353265) B23353265
theorem B20758457 : Blo 2159435 20758457 := bstep (se 2 (by rfl) ⟨7784421, by rfl⟩ : syracuseStep 20758457 = 15568843) B15568843
theorem B13838971 : Blo 2159435 13838971 := bstep (se 1 (by rfl) ⟨10379228, by rfl⟩ : syracuseStep 13838971 = 20758457) B20758457
theorem B18451961 : Blo 2159435 18451961 := bstep (se 2 (by rfl) ⟨6919485, by rfl⟩ : syracuseStep 18451961 = 13838971) B13838971
theorem B12301307 : Blo 2159435 12301307 := bstep (se 1 (by rfl) ⟨9225980, by rfl⟩ : syracuseStep 12301307 = 18451961) B18451961
theorem B8200871 : Blo 2159435 8200871 := bstep (se 1 (by rfl) ⟨6150653, by rfl⟩ : syracuseStep 8200871 = 12301307) B12301307
theorem B5467247 : Blo 2159435 5467247 := bstep (se 1 (by rfl) ⟨4100435, by rfl⟩ : syracuseStep 5467247 = 8200871) B8200871
theorem B3644831 : Blo 2159435 3644831 := bstep (se 1 (by rfl) ⟨2733623, by rfl⟩ : syracuseStep 3644831 = 5467247) B5467247
theorem B2429887 : Blo 2159435 2429887 := bstep (se 1 (by rfl) ⟨1822415, by rfl⟩ : syracuseStep 2429887 = 3644831) B3644831
theorem B3239849 : Blo 2159435 3239849 := bstep (se 2 (by rfl) ⟨1214943, by rfl⟩ : syracuseStep 3239849 = 2429887) B2429887
theorem B2159899 : Blo 2159435 2159899 := bstep (se 1 (by rfl) ⟨1619924, by rfl⟩ : syracuseStep 2159899 = 3239849) B3239849
theorem B8200885 : Blo 2159435 8200885 := bbase (se 5 (by rfl) ⟨384416, by rfl⟩ : syracuseStep 8200885 = 768833) (by norm_num)
theorem B10934513 : Blo 2159435 10934513 := bstep (se 2 (by rfl) ⟨4100442, by rfl⟩ : syracuseStep 10934513 = 8200885) B8200885
theorem B7289675 : Blo 2159435 7289675 := bstep (se 1 (by rfl) ⟨5467256, by rfl⟩ : syracuseStep 7289675 = 10934513) B10934513
theorem B4859783 : Blo 2159435 4859783 := bstep (se 1 (by rfl) ⟨3644837, by rfl⟩ : syracuseStep 4859783 = 7289675) B7289675
theorem B3239855 : Blo 2159435 3239855 := bstep (se 1 (by rfl) ⟨2429891, by rfl⟩ : syracuseStep 3239855 = 4859783) B4859783
theorem B2159903 : Blo 2159435 2159903 := bstep (se 1 (by rfl) ⟨1619927, by rfl⟩ : syracuseStep 2159903 = 3239855) B3239855
theorem B3239861 : Blo 2159435 3239861 := bbase (se 5 (by rfl) ⟨151868, by rfl⟩ : syracuseStep 3239861 = 303737) (by norm_num)
theorem B2159907 : Blo 2159435 2159907 := bstep (se 1 (by rfl) ⟨1619930, by rfl⟩ : syracuseStep 2159907 = 3239861) B3239861
theorem B5467277 : Blo 2159435 5467277 := bbase (se 3 (by rfl) ⟨1025114, by rfl⟩ : syracuseStep 5467277 = 2050229) (by norm_num)
theorem B3644851 : Blo 2159435 3644851 := bstep (se 1 (by rfl) ⟨2733638, by rfl⟩ : syracuseStep 3644851 = 5467277) B5467277
theorem B4859801 : Blo 2159435 4859801 := bstep (se 2 (by rfl) ⟨1822425, by rfl⟩ : syracuseStep 4859801 = 3644851) B3644851
theorem B3239867 : Blo 2159435 3239867 := bstep (se 1 (by rfl) ⟨2429900, by rfl⟩ : syracuseStep 3239867 = 4859801) B4859801
theorem B2159911 : Blo 2159435 2159911 := bstep (se 1 (by rfl) ⟨1619933, by rfl⟩ : syracuseStep 2159911 = 3239867) B3239867
theorem B2429905 : Blo 2159435 2429905 := bbase (se 2 (by rfl) ⟨911214, by rfl⟩ : syracuseStep 2429905 = 1822429) (by norm_num)
theorem B3239873 : Blo 2159435 3239873 := bstep (se 2 (by rfl) ⟨1214952, by rfl⟩ : syracuseStep 3239873 = 2429905) B2429905
theorem B2159915 : Blo 2159435 2159915 := bstep (se 1 (by rfl) ⟨1619936, by rfl⟩ : syracuseStep 2159915 = 3239873) B3239873
theorem B6234629 : Blo 2159435 6234629 := bbase (se 4 (by rfl) ⟨584496, by rfl⟩ : syracuseStep 6234629 = 1168993) (by norm_num)
theorem B16625677 : Blo 2159435 16625677 := bstep (se 3 (by rfl) ⟨3117314, by rfl⟩ : syracuseStep 16625677 = 6234629) B6234629
theorem B22167569 : Blo 2159435 22167569 := bstep (se 2 (by rfl) ⟨8312838, by rfl⟩ : syracuseStep 22167569 = 16625677) B16625677
theorem B14778379 : Blo 2159435 14778379 := bstep (se 1 (by rfl) ⟨11083784, by rfl⟩ : syracuseStep 14778379 = 22167569) B22167569
theorem B19704505 : Blo 2159435 19704505 := bstep (se 2 (by rfl) ⟨7389189, by rfl⟩ : syracuseStep 19704505 = 14778379) B14778379
theorem B26272673 : Blo 2159435 26272673 := bstep (se 2 (by rfl) ⟨9852252, by rfl⟩ : syracuseStep 26272673 = 19704505) B19704505
theorem B17515115 : Blo 2159435 17515115 := bstep (se 1 (by rfl) ⟨13136336, by rfl⟩ : syracuseStep 17515115 = 26272673) B26272673
theorem B11676743 : Blo 2159435 11676743 := bstep (se 1 (by rfl) ⟨8757557, by rfl⟩ : syracuseStep 11676743 = 17515115) B17515115
theorem B7784495 : Blo 2159435 7784495 := bstep (se 1 (by rfl) ⟨5838371, by rfl⟩ : syracuseStep 7784495 = 11676743) B11676743
theorem B5189663 : Blo 2159435 5189663 := bstep (se 1 (by rfl) ⟨3892247, by rfl⟩ : syracuseStep 5189663 = 7784495) B7784495
theorem B3459775 : Blo 2159435 3459775 := bstep (se 1 (by rfl) ⟨2594831, by rfl⟩ : syracuseStep 3459775 = 5189663) B5189663
theorem B4613033 : Blo 2159435 4613033 := bstep (se 2 (by rfl) ⟨1729887, by rfl⟩ : syracuseStep 4613033 = 3459775) B3459775
theorem B3075355 : Blo 2159435 3075355 := bstep (se 1 (by rfl) ⟨2306516, by rfl⟩ : syracuseStep 3075355 = 4613033) B4613033
theorem B4100473 : Blo 2159435 4100473 := bstep (se 2 (by rfl) ⟨1537677, by rfl⟩ : syracuseStep 4100473 = 3075355) B3075355
theorem B5467297 : Blo 2159435 5467297 := bstep (se 2 (by rfl) ⟨2050236, by rfl⟩ : syracuseStep 5467297 = 4100473) B4100473
theorem B7289729 : Blo 2159435 7289729 := bstep (se 2 (by rfl) ⟨2733648, by rfl⟩ : syracuseStep 7289729 = 5467297) B5467297
theorem B4859819 : Blo 2159435 4859819 := bstep (se 1 (by rfl) ⟨3644864, by rfl⟩ : syracuseStep 4859819 = 7289729) B7289729
theorem B3239879 : Blo 2159435 3239879 := bstep (se 1 (by rfl) ⟨2429909, by rfl⟩ : syracuseStep 3239879 = 4859819) B4859819
theorem B2159919 : Blo 2159435 2159919 := bstep (se 1 (by rfl) ⟨1619939, by rfl⟩ : syracuseStep 2159919 = 3239879) B3239879
theorem B3239885 : Blo 2159435 3239885 := bbase (se 3 (by rfl) ⟨607478, by rfl⟩ : syracuseStep 3239885 = 1214957) (by norm_num)
theorem B2159923 : Blo 2159435 2159923 := bstep (se 1 (by rfl) ⟨1619942, by rfl⟩ : syracuseStep 2159923 = 3239885) B3239885
theorem B4859837 : Blo 2159435 4859837 := bbase (se 3 (by rfl) ⟨911219, by rfl⟩ : syracuseStep 4859837 = 1822439) (by norm_num)
theorem B3239891 : Blo 2159435 3239891 := bstep (se 1 (by rfl) ⟨2429918, by rfl⟩ : syracuseStep 3239891 = 4859837) B4859837
theorem B2159927 : Blo 2159435 2159927 := bstep (se 1 (by rfl) ⟨1619945, by rfl⟩ : syracuseStep 2159927 = 3239891) B3239891
theorem B3644885 : Blo 2159435 3644885 := bbase (se 7 (by rfl) ⟨42713, by rfl⟩ : syracuseStep 3644885 = 85427) (by norm_num)
theorem B2429923 : Blo 2159435 2429923 := bstep (se 1 (by rfl) ⟨1822442, by rfl⟩ : syracuseStep 2429923 = 3644885) B3644885
theorem B3239897 : Blo 2159435 3239897 := bstep (se 2 (by rfl) ⟨1214961, by rfl⟩ : syracuseStep 3239897 = 2429923) B2429923
theorem B2159931 : Blo 2159435 2159931 := bstep (se 1 (by rfl) ⟨1619948, by rfl⟩ : syracuseStep 2159931 = 3239897) B3239897
theorem B9226133 : Blo 2159435 9226133 := bbase (se 6 (by rfl) ⟨216237, by rfl⟩ : syracuseStep 9226133 = 432475) (by norm_num)
theorem B6150755 : Blo 2159435 6150755 := bstep (se 1 (by rfl) ⟨4613066, by rfl⟩ : syracuseStep 6150755 = 9226133) B9226133
theorem B16402013 : Blo 2159435 16402013 := bstep (se 3 (by rfl) ⟨3075377, by rfl⟩ : syracuseStep 16402013 = 6150755) B6150755
theorem B10934675 : Blo 2159435 10934675 := bstep (se 1 (by rfl) ⟨8201006, by rfl⟩ : syracuseStep 10934675 = 16402013) B16402013
theorem B7289783 : Blo 2159435 7289783 := bstep (se 1 (by rfl) ⟨5467337, by rfl⟩ : syracuseStep 7289783 = 10934675) B10934675
theorem B4859855 : Blo 2159435 4859855 := bstep (se 1 (by rfl) ⟨3644891, by rfl⟩ : syracuseStep 4859855 = 7289783) B7289783
theorem B3239903 : Blo 2159435 3239903 := bstep (se 1 (by rfl) ⟨2429927, by rfl⟩ : syracuseStep 3239903 = 4859855) B4859855
theorem B2159935 : Blo 2159435 2159935 := bstep (se 1 (by rfl) ⟨1619951, by rfl⟩ : syracuseStep 2159935 = 3239903) B3239903
theorem B3239909 : Blo 2159435 3239909 := bbase (se 4 (by rfl) ⟨303741, by rfl⟩ : syracuseStep 3239909 = 607483) (by norm_num)
theorem B2159939 : Blo 2159435 2159939 := bstep (se 1 (by rfl) ⟨1619954, by rfl⟩ : syracuseStep 2159939 = 3239909) B3239909
theorem B7784581 : Blo 2159435 7784581 := bbase (se 4 (by rfl) ⟨729804, by rfl⟩ : syracuseStep 7784581 = 1459609) (by norm_num)
theorem B10379441 : Blo 2159435 10379441 := bstep (se 2 (by rfl) ⟨3892290, by rfl⟩ : syracuseStep 10379441 = 7784581) B7784581
theorem B6919627 : Blo 2159435 6919627 := bstep (se 1 (by rfl) ⟨5189720, by rfl⟩ : syracuseStep 6919627 = 10379441) B10379441
theorem B9226169 : Blo 2159435 9226169 := bstep (se 2 (by rfl) ⟨3459813, by rfl⟩ : syracuseStep 9226169 = 6919627) B6919627
theorem B6150779 : Blo 2159435 6150779 := bstep (se 1 (by rfl) ⟨4613084, by rfl⟩ : syracuseStep 6150779 = 9226169) B9226169
theorem B4100519 : Blo 2159435 4100519 := bstep (se 1 (by rfl) ⟨3075389, by rfl⟩ : syracuseStep 4100519 = 6150779) B6150779
theorem B2733679 : Blo 2159435 2733679 := bstep (se 1 (by rfl) ⟨2050259, by rfl⟩ : syracuseStep 2733679 = 4100519) B4100519
theorem B3644905 : Blo 2159435 3644905 := bstep (se 2 (by rfl) ⟨1366839, by rfl⟩ : syracuseStep 3644905 = 2733679) B2733679
theorem B4859873 : Blo 2159435 4859873 := bstep (se 2 (by rfl) ⟨1822452, by rfl⟩ : syracuseStep 4859873 = 3644905) B3644905
theorem B3239915 : Blo 2159435 3239915 := bstep (se 1 (by rfl) ⟨2429936, by rfl⟩ : syracuseStep 3239915 = 4859873) B4859873
theorem B2159943 : Blo 2159435 2159943 := bstep (se 1 (by rfl) ⟨1619957, by rfl⟩ : syracuseStep 2159943 = 3239915) B3239915
theorem B2429941 : Blo 2159435 2429941 := bbase (se 5 (by rfl) ⟨113903, by rfl⟩ : syracuseStep 2429941 = 227807) (by norm_num)
theorem B3239921 : Blo 2159435 3239921 := bstep (se 2 (by rfl) ⟨1214970, by rfl⟩ : syracuseStep 3239921 = 2429941) B2429941
theorem B2159947 : Blo 2159435 2159947 := bstep (se 1 (by rfl) ⟨1619960, by rfl⟩ : syracuseStep 2159947 = 3239921) B3239921
theorem B2733689 : Blo 2159435 2733689 := bbase (se 2 (by rfl) ⟨1025133, by rfl⟩ : syracuseStep 2733689 = 2050267) (by norm_num)
theorem B7289837 : Blo 2159435 7289837 := bstep (se 3 (by rfl) ⟨1366844, by rfl⟩ : syracuseStep 7289837 = 2733689) B2733689
theorem B4859891 : Blo 2159435 4859891 := bstep (se 1 (by rfl) ⟨3644918, by rfl⟩ : syracuseStep 4859891 = 7289837) B7289837
theorem B3239927 : Blo 2159435 3239927 := bstep (se 1 (by rfl) ⟨2429945, by rfl⟩ : syracuseStep 3239927 = 4859891) B4859891
theorem B2159951 : Blo 2159435 2159951 := bstep (se 1 (by rfl) ⟨1619963, by rfl⟩ : syracuseStep 2159951 = 3239927) B3239927
theorem B3239933 : Blo 2159435 3239933 := bbase (se 3 (by rfl) ⟨607487, by rfl⟩ : syracuseStep 3239933 = 1214975) (by norm_num)
theorem B2159955 : Blo 2159435 2159955 := bstep (se 1 (by rfl) ⟨1619966, by rfl⟩ : syracuseStep 2159955 = 3239933) B3239933
theorem B4859909 : Blo 2159435 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B3239939 : Blo 2159435 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B2159959 : Blo 2159435 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B4100557 : Blo 2159435 4100557 := bbase (se 3 (by rfl) ⟨768854, by rfl⟩ : syracuseStep 4100557 = 1537709) (by norm_num)
theorem B5467409 : Blo 2159435 5467409 := bstep (se 2 (by rfl) ⟨2050278, by rfl⟩ : syracuseStep 5467409 = 4100557) B4100557
theorem B3644939 : Blo 2159435 3644939 := bstep (se 1 (by rfl) ⟨2733704, by rfl⟩ : syracuseStep 3644939 = 5467409) B5467409
theorem B2429959 : Blo 2159435 2429959 := bstep (se 1 (by rfl) ⟨1822469, by rfl⟩ : syracuseStep 2429959 = 3644939) B3644939
theorem B3239945 : Blo 2159435 3239945 := bstep (se 2 (by rfl) ⟨1214979, by rfl⟩ : syracuseStep 3239945 = 2429959) B2429959
theorem B2159963 : Blo 2159435 2159963 := bstep (se 1 (by rfl) ⟨1619972, by rfl⟩ : syracuseStep 2159963 = 3239945) B3239945
theorem B10934837 : Blo 2159435 10934837 := bbase (se 5 (by rfl) ⟨512570, by rfl⟩ : syracuseStep 10934837 = 1025141) (by norm_num)
theorem B7289891 : Blo 2159435 7289891 := bstep (se 1 (by rfl) ⟨5467418, by rfl⟩ : syracuseStep 7289891 = 10934837) B10934837
theorem B4859927 : Blo 2159435 4859927 := bstep (se 1 (by rfl) ⟨3644945, by rfl⟩ : syracuseStep 4859927 = 7289891) B7289891
theorem B3239951 : Blo 2159435 3239951 := bstep (se 1 (by rfl) ⟨2429963, by rfl⟩ : syracuseStep 3239951 = 4859927) B4859927
theorem B2159967 : Blo 2159435 2159967 := bstep (se 1 (by rfl) ⟨1619975, by rfl⟩ : syracuseStep 2159967 = 3239951) B3239951
theorem B3239957 : Blo 2159435 3239957 := bbase (se 6 (by rfl) ⟨75936, by rfl⟩ : syracuseStep 3239957 = 151873) (by norm_num)
theorem B2159971 : Blo 2159435 2159971 := bstep (se 1 (by rfl) ⟨1619978, by rfl⟩ : syracuseStep 2159971 = 3239957) B3239957
theorem B4926253 : Blo 2159435 4926253 := bbase (se 3 (by rfl) ⟨923672, by rfl⟩ : syracuseStep 4926253 = 1847345) (by norm_num)
theorem B6568337 : Blo 2159435 6568337 := bstep (se 2 (by rfl) ⟨2463126, by rfl⟩ : syracuseStep 6568337 = 4926253) B4926253
theorem B17515565 : Blo 2159435 17515565 := bstep (se 3 (by rfl) ⟨3284168, by rfl⟩ : syracuseStep 17515565 = 6568337) B6568337
theorem B11677043 : Blo 2159435 11677043 := bstep (se 1 (by rfl) ⟨8757782, by rfl⟩ : syracuseStep 11677043 = 17515565) B17515565
theorem B7784695 : Blo 2159435 7784695 := bstep (se 1 (by rfl) ⟨5838521, by rfl⟩ : syracuseStep 7784695 = 11677043) B11677043
theorem B10379593 : Blo 2159435 10379593 := bstep (se 2 (by rfl) ⟨3892347, by rfl⟩ : syracuseStep 10379593 = 7784695) B7784695
theorem B13839457 : Blo 2159435 13839457 := bstep (se 2 (by rfl) ⟨5189796, by rfl⟩ : syracuseStep 13839457 = 10379593) B10379593
theorem B18452609 : Blo 2159435 18452609 := bstep (se 2 (by rfl) ⟨6919728, by rfl⟩ : syracuseStep 18452609 = 13839457) B13839457
theorem B12301739 : Blo 2159435 12301739 := bstep (se 1 (by rfl) ⟨9226304, by rfl⟩ : syracuseStep 12301739 = 18452609) B18452609
theorem B8201159 : Blo 2159435 8201159 := bstep (se 1 (by rfl) ⟨6150869, by rfl⟩ : syracuseStep 8201159 = 12301739) B12301739
theorem B5467439 : Blo 2159435 5467439 := bstep (se 1 (by rfl) ⟨4100579, by rfl⟩ : syracuseStep 5467439 = 8201159) B8201159
theorem B3644959 : Blo 2159435 3644959 := bstep (se 1 (by rfl) ⟨2733719, by rfl⟩ : syracuseStep 3644959 = 5467439) B5467439
theorem B4859945 : Blo 2159435 4859945 := bstep (se 2 (by rfl) ⟨1822479, by rfl⟩ : syracuseStep 4859945 = 3644959) B3644959
theorem B3239963 : Blo 2159435 3239963 := bstep (se 1 (by rfl) ⟨2429972, by rfl⟩ : syracuseStep 3239963 = 4859945) B4859945
theorem B2159975 : Blo 2159435 2159975 := bstep (se 1 (by rfl) ⟨1619981, by rfl⟩ : syracuseStep 2159975 = 3239963) B3239963
theorem B2429977 : Blo 2159435 2429977 := bbase (se 2 (by rfl) ⟨911241, by rfl⟩ : syracuseStep 2429977 = 1822483) (by norm_num)
theorem B3239969 : Blo 2159435 3239969 := bstep (se 2 (by rfl) ⟨1214988, by rfl⟩ : syracuseStep 3239969 = 2429977) B2429977
theorem B2159979 : Blo 2159435 2159979 := bstep (se 1 (by rfl) ⟨1619984, by rfl⟩ : syracuseStep 2159979 = 3239969) B3239969
theorem B8201189 : Blo 2159435 8201189 := bbase (se 4 (by rfl) ⟨768861, by rfl⟩ : syracuseStep 8201189 = 1537723) (by norm_num)
theorem B5467459 : Blo 2159435 5467459 := bstep (se 1 (by rfl) ⟨4100594, by rfl⟩ : syracuseStep 5467459 = 8201189) B8201189
theorem B7289945 : Blo 2159435 7289945 := bstep (se 2 (by rfl) ⟨2733729, by rfl⟩ : syracuseStep 7289945 = 5467459) B5467459
theorem B4859963 : Blo 2159435 4859963 := bstep (se 1 (by rfl) ⟨3644972, by rfl⟩ : syracuseStep 4859963 = 7289945) B7289945
theorem B3239975 : Blo 2159435 3239975 := bstep (se 1 (by rfl) ⟨2429981, by rfl⟩ : syracuseStep 3239975 = 4859963) B4859963
theorem B2159983 : Blo 2159435 2159983 := bstep (se 1 (by rfl) ⟨1619987, by rfl⟩ : syracuseStep 2159983 = 3239975) B3239975
theorem B3239981 : Blo 2159435 3239981 := bbase (se 3 (by rfl) ⟨607496, by rfl⟩ : syracuseStep 3239981 = 1214993) (by norm_num)
theorem B2159987 : Blo 2159435 2159987 := bstep (se 1 (by rfl) ⟨1619990, by rfl⟩ : syracuseStep 2159987 = 3239981) B3239981
theorem B4859981 : Blo 2159435 4859981 := bbase (se 3 (by rfl) ⟨911246, by rfl⟩ : syracuseStep 4859981 = 1822493) (by norm_num)
theorem B3239987 : Blo 2159435 3239987 := bstep (se 1 (by rfl) ⟨2429990, by rfl⟩ : syracuseStep 3239987 = 4859981) B4859981
theorem B2159991 : Blo 2159435 2159991 := bstep (se 1 (by rfl) ⟨1619993, by rfl⟩ : syracuseStep 2159991 = 3239987) B3239987
theorem B2733745 : Blo 2159435 2733745 := bbase (se 2 (by rfl) ⟨1025154, by rfl⟩ : syracuseStep 2733745 = 2050309) (by norm_num)
theorem B3644993 : Blo 2159435 3644993 := bstep (se 2 (by rfl) ⟨1366872, by rfl⟩ : syracuseStep 3644993 = 2733745) B2733745
theorem B2429995 : Blo 2159435 2429995 := bstep (se 1 (by rfl) ⟨1822496, by rfl⟩ : syracuseStep 2429995 = 3644993) B3644993
theorem B3239993 : Blo 2159435 3239993 := bstep (se 2 (by rfl) ⟨1214997, by rfl⟩ : syracuseStep 3239993 = 2429995) B2429995
theorem B2159995 : Blo 2159435 2159995 := bstep (se 1 (by rfl) ⟨1619996, by rfl⟩ : syracuseStep 2159995 = 3239993) B3239993
theorem B16626293 : Blo 2159435 16626293 := bbase (se 5 (by rfl) ⟨779357, by rfl⟩ : syracuseStep 16626293 = 1558715) (by norm_num)
theorem B11084195 : Blo 2159435 11084195 := bstep (se 1 (by rfl) ⟨8313146, by rfl⟩ : syracuseStep 11084195 = 16626293) B16626293
theorem B7389463 : Blo 2159435 7389463 := bstep (se 1 (by rfl) ⟨5542097, by rfl⟩ : syracuseStep 7389463 = 11084195) B11084195
theorem B9852617 : Blo 2159435 9852617 := bstep (se 2 (by rfl) ⟨3694731, by rfl⟩ : syracuseStep 9852617 = 7389463) B7389463
theorem B6568411 : Blo 2159435 6568411 := bstep (se 1 (by rfl) ⟨4926308, by rfl⟩ : syracuseStep 6568411 = 9852617) B9852617
theorem B8757881 : Blo 2159435 8757881 := bstep (se 2 (by rfl) ⟨3284205, by rfl⟩ : syracuseStep 8757881 = 6568411) B6568411
theorem B5838587 : Blo 2159435 5838587 := bstep (se 1 (by rfl) ⟨4378940, by rfl⟩ : syracuseStep 5838587 = 8757881) B8757881
theorem B3892391 : Blo 2159435 3892391 := bstep (se 1 (by rfl) ⟨2919293, by rfl⟩ : syracuseStep 3892391 = 5838587) B5838587
theorem B2594927 : Blo 2159435 2594927 := bstep (se 1 (by rfl) ⟨1946195, by rfl⟩ : syracuseStep 2594927 = 3892391) B3892391
theorem B6919805 : Blo 2159435 6919805 := bstep (se 3 (by rfl) ⟨1297463, by rfl⟩ : syracuseStep 6919805 = 2594927) B2594927
theorem B4613203 : Blo 2159435 4613203 := bstep (se 1 (by rfl) ⟨3459902, by rfl⟩ : syracuseStep 4613203 = 6919805) B6919805
theorem B24603749 : Blo 2159435 24603749 := bstep (se 4 (by rfl) ⟨2306601, by rfl⟩ : syracuseStep 24603749 = 4613203) B4613203
theorem B16402499 : Blo 2159435 16402499 := bstep (se 1 (by rfl) ⟨12301874, by rfl⟩ : syracuseStep 16402499 = 24603749) B24603749
theorem B10934999 : Blo 2159435 10934999 := bstep (se 1 (by rfl) ⟨8201249, by rfl⟩ : syracuseStep 10934999 = 16402499) B16402499
theorem B7289999 : Blo 2159435 7289999 := bstep (se 1 (by rfl) ⟨5467499, by rfl⟩ : syracuseStep 7289999 = 10934999) B10934999
theorem B4859999 : Blo 2159435 4859999 := bstep (se 1 (by rfl) ⟨3644999, by rfl⟩ : syracuseStep 4859999 = 7289999) B7289999
theorem B3239999 : Blo 2159435 3239999 := bstep (se 1 (by rfl) ⟨2429999, by rfl⟩ : syracuseStep 3239999 = 4859999) B4859999
theorem B2159999 : Blo 2159435 2159999 := bstep (se 1 (by rfl) ⟨1619999, by rfl⟩ : syracuseStep 2159999 = 3239999) B3239999
theorem B3240005 : Blo 2159435 3240005 := bbase (se 4 (by rfl) ⟨303750, by rfl⟩ : syracuseStep 3240005 = 607501) (by norm_num)
theorem B2160003 : Blo 2159435 2160003 := bstep (se 1 (by rfl) ⟨1620002, by rfl⟩ : syracuseStep 2160003 = 3240005) B3240005
theorem B3645013 : Blo 2159435 3645013 := bbase (se 8 (by rfl) ⟨21357, by rfl⟩ : syracuseStep 3645013 = 42715) (by norm_num)
theorem B4860017 : Blo 2159435 4860017 := bstep (se 2 (by rfl) ⟨1822506, by rfl⟩ : syracuseStep 4860017 = 3645013) B3645013
theorem B3240011 : Blo 2159435 3240011 := bstep (se 1 (by rfl) ⟨2430008, by rfl⟩ : syracuseStep 3240011 = 4860017) B4860017
theorem B2160007 : Blo 2159435 2160007 := bstep (se 1 (by rfl) ⟨1620005, by rfl⟩ : syracuseStep 2160007 = 3240011) B3240011
theorem B2430013 : Blo 2159435 2430013 := bbase (se 3 (by rfl) ⟨455627, by rfl⟩ : syracuseStep 2430013 = 911255) (by norm_num)
theorem B3240017 : Blo 2159435 3240017 := bstep (se 2 (by rfl) ⟨1215006, by rfl⟩ : syracuseStep 3240017 = 2430013) B2430013
theorem B2160011 : Blo 2159435 2160011 := bstep (se 1 (by rfl) ⟨1620008, by rfl⟩ : syracuseStep 2160011 = 3240017) B3240017
theorem B7290053 : Blo 2159435 7290053 := bbase (se 4 (by rfl) ⟨683442, by rfl⟩ : syracuseStep 7290053 = 1366885) (by norm_num)
theorem B4860035 : Blo 2159435 4860035 := bstep (se 1 (by rfl) ⟨3645026, by rfl⟩ : syracuseStep 4860035 = 7290053) B7290053
theorem B3240023 : Blo 2159435 3240023 := bstep (se 1 (by rfl) ⟨2430017, by rfl⟩ : syracuseStep 3240023 = 4860035) B4860035
theorem B2160015 : Blo 2159435 2160015 := bstep (se 1 (by rfl) ⟨1620011, by rfl⟩ : syracuseStep 2160015 = 3240023) B3240023
theorem B3240029 : Blo 2159435 3240029 := bbase (se 3 (by rfl) ⟨607505, by rfl⟩ : syracuseStep 3240029 = 1215011) (by norm_num)
theorem B2160019 : Blo 2159435 2160019 := bstep (se 1 (by rfl) ⟨1620014, by rfl⟩ : syracuseStep 2160019 = 3240029) B3240029
theorem B4860053 : Blo 2159435 4860053 := bbase (se 6 (by rfl) ⟨113907, by rfl⟩ : syracuseStep 4860053 = 227815) (by norm_num)
theorem B3240035 : Blo 2159435 3240035 := bstep (se 1 (by rfl) ⟨2430026, by rfl⟩ : syracuseStep 3240035 = 4860053) B4860053
theorem B2160023 : Blo 2159435 2160023 := bstep (se 1 (by rfl) ⟨1620017, by rfl⟩ : syracuseStep 2160023 = 3240035) B3240035
theorem B3075509 : Blo 2159435 3075509 := bbase (se 5 (by rfl) ⟨144164, by rfl⟩ : syracuseStep 3075509 = 288329) (by norm_num)
theorem B8201357 : Blo 2159435 8201357 := bstep (se 3 (by rfl) ⟨1537754, by rfl⟩ : syracuseStep 8201357 = 3075509) B3075509
theorem B5467571 : Blo 2159435 5467571 := bstep (se 1 (by rfl) ⟨4100678, by rfl⟩ : syracuseStep 5467571 = 8201357) B8201357
theorem B3645047 : Blo 2159435 3645047 := bstep (se 1 (by rfl) ⟨2733785, by rfl⟩ : syracuseStep 3645047 = 5467571) B5467571
theorem B2430031 : Blo 2159435 2430031 := bstep (se 1 (by rfl) ⟨1822523, by rfl⟩ : syracuseStep 2430031 = 3645047) B3645047
theorem B3240041 : Blo 2159435 3240041 := bstep (se 2 (by rfl) ⟨1215015, by rfl⟩ : syracuseStep 3240041 = 2430031) B2430031
theorem B2160027 : Blo 2159435 2160027 := bstep (se 1 (by rfl) ⟨1620020, by rfl⟩ : syracuseStep 2160027 = 3240041) B3240041
theorem B13137013 : Blo 2159435 13137013 := bbase (se 5 (by rfl) ⟨615797, by rfl⟩ : syracuseStep 13137013 = 1231595) (by norm_num)
theorem B17516017 : Blo 2159435 17516017 := bstep (se 2 (by rfl) ⟨6568506, by rfl⟩ : syracuseStep 17516017 = 13137013) B13137013
theorem B23354689 : Blo 2159435 23354689 := bstep (se 2 (by rfl) ⟨8758008, by rfl⟩ : syracuseStep 23354689 = 17516017) B17516017
theorem B31139585 : Blo 2159435 31139585 := bstep (se 2 (by rfl) ⟨11677344, by rfl⟩ : syracuseStep 31139585 = 23354689) B23354689
theorem B20759723 : Blo 2159435 20759723 := bstep (se 1 (by rfl) ⟨15569792, by rfl⟩ : syracuseStep 20759723 = 31139585) B31139585
theorem B13839815 : Blo 2159435 13839815 := bstep (se 1 (by rfl) ⟨10379861, by rfl⟩ : syracuseStep 13839815 = 20759723) B20759723
theorem B9226543 : Blo 2159435 9226543 := bstep (se 1 (by rfl) ⟨6919907, by rfl⟩ : syracuseStep 9226543 = 13839815) B13839815
theorem B12302057 : Blo 2159435 12302057 := bstep (se 2 (by rfl) ⟨4613271, by rfl⟩ : syracuseStep 12302057 = 9226543) B9226543
theorem B8201371 : Blo 2159435 8201371 := bstep (se 1 (by rfl) ⟨6151028, by rfl⟩ : syracuseStep 8201371 = 12302057) B12302057
theorem B10935161 : Blo 2159435 10935161 := bstep (se 2 (by rfl) ⟨4100685, by rfl⟩ : syracuseStep 10935161 = 8201371) B8201371
theorem B7290107 : Blo 2159435 7290107 := bstep (se 1 (by rfl) ⟨5467580, by rfl⟩ : syracuseStep 7290107 = 10935161) B10935161
theorem B4860071 : Blo 2159435 4860071 := bstep (se 1 (by rfl) ⟨3645053, by rfl⟩ : syracuseStep 4860071 = 7290107) B7290107
theorem B3240047 : Blo 2159435 3240047 := bstep (se 1 (by rfl) ⟨2430035, by rfl⟩ : syracuseStep 3240047 = 4860071) B4860071
theorem B2160031 : Blo 2159435 2160031 := bstep (se 1 (by rfl) ⟨1620023, by rfl⟩ : syracuseStep 2160031 = 3240047) B3240047
theorem B3240053 : Blo 2159435 3240053 := bbase (se 5 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 3240053 = 303755) (by norm_num)
theorem B2160035 : Blo 2159435 2160035 := bstep (se 1 (by rfl) ⟨1620026, by rfl⟩ : syracuseStep 2160035 = 3240053) B3240053
theorem B4100701 : Blo 2159435 4100701 := bbase (se 3 (by rfl) ⟨768881, by rfl⟩ : syracuseStep 4100701 = 1537763) (by norm_num)
theorem B5467601 : Blo 2159435 5467601 := bstep (se 2 (by rfl) ⟨2050350, by rfl⟩ : syracuseStep 5467601 = 4100701) B4100701
theorem B3645067 : Blo 2159435 3645067 := bstep (se 1 (by rfl) ⟨2733800, by rfl⟩ : syracuseStep 3645067 = 5467601) B5467601
theorem B4860089 : Blo 2159435 4860089 := bstep (se 2 (by rfl) ⟨1822533, by rfl⟩ : syracuseStep 4860089 = 3645067) B3645067
theorem B3240059 : Blo 2159435 3240059 := bstep (se 1 (by rfl) ⟨2430044, by rfl⟩ : syracuseStep 3240059 = 4860089) B4860089
theorem B2160039 : Blo 2159435 2160039 := bstep (se 1 (by rfl) ⟨1620029, by rfl⟩ : syracuseStep 2160039 = 3240059) B3240059
theorem B2430049 : Blo 2159435 2430049 := bbase (se 2 (by rfl) ⟨911268, by rfl⟩ : syracuseStep 2430049 = 1822537) (by norm_num)
theorem B3240065 : Blo 2159435 3240065 := bstep (se 2 (by rfl) ⟨1215024, by rfl⟩ : syracuseStep 3240065 = 2430049) B2430049
theorem B2160043 : Blo 2159435 2160043 := bstep (se 1 (by rfl) ⟨1620032, by rfl⟩ : syracuseStep 2160043 = 3240065) B3240065
theorem B5467621 : Blo 2159435 5467621 := bbase (se 4 (by rfl) ⟨512589, by rfl⟩ : syracuseStep 5467621 = 1025179) (by norm_num)
theorem B7290161 : Blo 2159435 7290161 := bstep (se 2 (by rfl) ⟨2733810, by rfl⟩ : syracuseStep 7290161 = 5467621) B5467621
theorem B4860107 : Blo 2159435 4860107 := bstep (se 1 (by rfl) ⟨3645080, by rfl⟩ : syracuseStep 4860107 = 7290161) B7290161
theorem B3240071 : Blo 2159435 3240071 := bstep (se 1 (by rfl) ⟨2430053, by rfl⟩ : syracuseStep 3240071 = 4860107) B4860107
theorem B2160047 : Blo 2159435 2160047 := bstep (se 1 (by rfl) ⟨1620035, by rfl⟩ : syracuseStep 2160047 = 3240071) B3240071
theorem B3240077 : Blo 2159435 3240077 := bbase (se 3 (by rfl) ⟨607514, by rfl⟩ : syracuseStep 3240077 = 1215029) (by norm_num)
theorem B2160051 : Blo 2159435 2160051 := bstep (se 1 (by rfl) ⟨1620038, by rfl⟩ : syracuseStep 2160051 = 3240077) B3240077
theorem B4860125 : Blo 2159435 4860125 := bbase (se 3 (by rfl) ⟨911273, by rfl⟩ : syracuseStep 4860125 = 1822547) (by norm_num)
theorem B3240083 : Blo 2159435 3240083 := bstep (se 1 (by rfl) ⟨2430062, by rfl⟩ : syracuseStep 3240083 = 4860125) B4860125
theorem B2160055 : Blo 2159435 2160055 := bstep (se 1 (by rfl) ⟨1620041, by rfl⟩ : syracuseStep 2160055 = 3240083) B3240083
theorem B3645101 : Blo 2159435 3645101 := bbase (se 3 (by rfl) ⟨683456, by rfl⟩ : syracuseStep 3645101 = 1366913) (by norm_num)
theorem B2430067 : Blo 2159435 2430067 := bstep (se 1 (by rfl) ⟨1822550, by rfl⟩ : syracuseStep 2430067 = 3645101) B3645101
theorem B3240089 : Blo 2159435 3240089 := bstep (se 2 (by rfl) ⟨1215033, by rfl⟩ : syracuseStep 3240089 = 2430067) B2430067
theorem B2160059 : Blo 2159435 2160059 := bstep (se 1 (by rfl) ⟨1620044, by rfl⟩ : syracuseStep 2160059 = 3240089) B3240089
theorem B3603565 : Blo 2159435 3603565 := bbase (se 3 (by rfl) ⟨675668, by rfl⟩ : syracuseStep 3603565 = 1351337) (by norm_num)
theorem B4804753 : Blo 2159435 4804753 := bstep (se 2 (by rfl) ⟨1801782, by rfl⟩ : syracuseStep 4804753 = 3603565) B3603565
theorem B6406337 : Blo 2159435 6406337 := bstep (se 2 (by rfl) ⟨2402376, by rfl⟩ : syracuseStep 6406337 = 4804753) B4804753
theorem B17083565 : Blo 2159435 17083565 := bstep (se 3 (by rfl) ⟨3203168, by rfl⟩ : syracuseStep 17083565 = 6406337) B6406337
theorem B11389043 : Blo 2159435 11389043 := bstep (se 1 (by rfl) ⟨8541782, by rfl⟩ : syracuseStep 11389043 = 17083565) B17083565
theorem B30370781 : Blo 2159435 30370781 := bstep (se 3 (by rfl) ⟨5694521, by rfl⟩ : syracuseStep 30370781 = 11389043) B11389043
theorem B20247187 : Blo 2159435 20247187 := bstep (se 1 (by rfl) ⟨15185390, by rfl⟩ : syracuseStep 20247187 = 30370781) B30370781
theorem B26996249 : Blo 2159435 26996249 := bstep (se 2 (by rfl) ⟨10123593, by rfl⟩ : syracuseStep 26996249 = 20247187) B20247187
theorem B17997499 : Blo 2159435 17997499 := bstep (se 1 (by rfl) ⟨13498124, by rfl⟩ : syracuseStep 17997499 = 26996249) B26996249
theorem B23996665 : Blo 2159435 23996665 := bstep (se 2 (by rfl) ⟨8998749, by rfl⟩ : syracuseStep 23996665 = 17997499) B17997499
theorem B127982213 : Blo 2159435 127982213 := bstep (se 4 (by rfl) ⟨11998332, by rfl⟩ : syracuseStep 127982213 = 23996665) B23996665
theorem B85321475 : Blo 2159435 85321475 := bstep (se 1 (by rfl) ⟨63991106, by rfl⟩ : syracuseStep 85321475 = 127982213) B127982213
theorem B56880983 : Blo 2159435 56880983 := bstep (se 1 (by rfl) ⟨42660737, by rfl⟩ : syracuseStep 56880983 = 85321475) B85321475
theorem B37920655 : Blo 2159435 37920655 := bstep (se 1 (by rfl) ⟨28440491, by rfl⟩ : syracuseStep 37920655 = 56880983) B56880983
theorem B202243493 : Blo 2159435 202243493 := bstep (se 4 (by rfl) ⟨18960327, by rfl⟩ : syracuseStep 202243493 = 37920655) B37920655
theorem B134828995 : Blo 2159435 134828995 := bstep (se 1 (by rfl) ⟨101121746, by rfl⟩ : syracuseStep 134828995 = 202243493) B202243493
theorem B179771993 : Blo 2159435 179771993 := bstep (se 2 (by rfl) ⟨67414497, by rfl⟩ : syracuseStep 179771993 = 134828995) B134828995
theorem B119847995 : Blo 2159435 119847995 := bstep (se 1 (by rfl) ⟨89885996, by rfl⟩ : syracuseStep 119847995 = 179771993) B179771993
theorem B79898663 : Blo 2159435 79898663 := bstep (se 1 (by rfl) ⟨59923997, by rfl⟩ : syracuseStep 79898663 = 119847995) B119847995
theorem B53265775 : Blo 2159435 53265775 := bstep (se 1 (by rfl) ⟨39949331, by rfl⟩ : syracuseStep 53265775 = 79898663) B79898663
theorem B71021033 : Blo 2159435 71021033 := bstep (se 2 (by rfl) ⟨26632887, by rfl⟩ : syracuseStep 71021033 = 53265775) B53265775
theorem B47347355 : Blo 2159435 47347355 := bstep (se 1 (by rfl) ⟨35510516, by rfl⟩ : syracuseStep 47347355 = 71021033) B71021033
theorem B31564903 : Blo 2159435 31564903 := bstep (se 1 (by rfl) ⟨23673677, by rfl⟩ : syracuseStep 31564903 = 47347355) B47347355
theorem B42086537 : Blo 2159435 42086537 := bstep (se 2 (by rfl) ⟨15782451, by rfl⟩ : syracuseStep 42086537 = 31564903) B31564903
theorem B28057691 : Blo 2159435 28057691 := bstep (se 1 (by rfl) ⟨21043268, by rfl⟩ : syracuseStep 28057691 = 42086537) B42086537
theorem B18705127 : Blo 2159435 18705127 := bstep (se 1 (by rfl) ⟨14028845, by rfl⟩ : syracuseStep 18705127 = 28057691) B28057691
theorem B24940169 : Blo 2159435 24940169 := bstep (se 2 (by rfl) ⟨9352563, by rfl⟩ : syracuseStep 24940169 = 18705127) B18705127
theorem B16626779 : Blo 2159435 16626779 := bstep (se 1 (by rfl) ⟨12470084, by rfl⟩ : syracuseStep 16626779 = 24940169) B24940169
theorem B11084519 : Blo 2159435 11084519 := bstep (se 1 (by rfl) ⟨8313389, by rfl⟩ : syracuseStep 11084519 = 16626779) B16626779
theorem B7389679 : Blo 2159435 7389679 := bstep (se 1 (by rfl) ⟨5542259, by rfl⟩ : syracuseStep 7389679 = 11084519) B11084519
theorem B9852905 : Blo 2159435 9852905 := bstep (se 2 (by rfl) ⟨3694839, by rfl⟩ : syracuseStep 9852905 = 7389679) B7389679
theorem B26274413 : Blo 2159435 26274413 := bstep (se 3 (by rfl) ⟨4926452, by rfl⟩ : syracuseStep 26274413 = 9852905) B9852905
theorem B70065101 : Blo 2159435 70065101 := bstep (se 3 (by rfl) ⟨13137206, by rfl⟩ : syracuseStep 70065101 = 26274413) B26274413
theorem B46710067 : Blo 2159435 46710067 := bstep (se 1 (by rfl) ⟨35032550, by rfl⟩ : syracuseStep 46710067 = 70065101) B70065101
theorem B62280089 : Blo 2159435 62280089 := bstep (se 2 (by rfl) ⟨23355033, by rfl⟩ : syracuseStep 62280089 = 46710067) B46710067
theorem B41520059 : Blo 2159435 41520059 := bstep (se 1 (by rfl) ⟨31140044, by rfl⟩ : syracuseStep 41520059 = 62280089) B62280089
theorem B27680039 : Blo 2159435 27680039 := bstep (se 1 (by rfl) ⟨20760029, by rfl⟩ : syracuseStep 27680039 = 41520059) B41520059
theorem B18453359 : Blo 2159435 18453359 := bstep (se 1 (by rfl) ⟨13840019, by rfl⟩ : syracuseStep 18453359 = 27680039) B27680039
theorem B12302239 : Blo 2159435 12302239 := bstep (se 1 (by rfl) ⟨9226679, by rfl⟩ : syracuseStep 12302239 = 18453359) B18453359
theorem B16402985 : Blo 2159435 16402985 := bstep (se 2 (by rfl) ⟨6151119, by rfl⟩ : syracuseStep 16402985 = 12302239) B12302239
theorem B10935323 : Blo 2159435 10935323 := bstep (se 1 (by rfl) ⟨8201492, by rfl⟩ : syracuseStep 10935323 = 16402985) B16402985
theorem B7290215 : Blo 2159435 7290215 := bstep (se 1 (by rfl) ⟨5467661, by rfl⟩ : syracuseStep 7290215 = 10935323) B10935323
theorem B4860143 : Blo 2159435 4860143 := bstep (se 1 (by rfl) ⟨3645107, by rfl⟩ : syracuseStep 4860143 = 7290215) B7290215
theorem B3240095 : Blo 2159435 3240095 := bstep (se 1 (by rfl) ⟨2430071, by rfl⟩ : syracuseStep 3240095 = 4860143) B4860143
theorem B2160063 : Blo 2159435 2160063 := bstep (se 1 (by rfl) ⟨1620047, by rfl⟩ : syracuseStep 2160063 = 3240095) B3240095
theorem B3240101 : Blo 2159435 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B2160067 : Blo 2159435 2160067 := bstep (se 1 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 2160067 = 3240101) B3240101
theorem B2733841 : Blo 2159435 2733841 := bbase (se 2 (by rfl) ⟨1025190, by rfl⟩ : syracuseStep 2733841 = 2050381) (by norm_num)
theorem B3645121 : Blo 2159435 3645121 := bstep (se 2 (by rfl) ⟨1366920, by rfl⟩ : syracuseStep 3645121 = 2733841) B2733841
theorem B4860161 : Blo 2159435 4860161 := bstep (se 2 (by rfl) ⟨1822560, by rfl⟩ : syracuseStep 4860161 = 3645121) B3645121
theorem B3240107 : Blo 2159435 3240107 := bstep (se 1 (by rfl) ⟨2430080, by rfl⟩ : syracuseStep 3240107 = 4860161) B4860161
theorem B2160071 : Blo 2159435 2160071 := bstep (se 1 (by rfl) ⟨1620053, by rfl⟩ : syracuseStep 2160071 = 3240107) B3240107
theorem B2430085 : Blo 2159435 2430085 := bbase (se 4 (by rfl) ⟨227820, by rfl⟩ : syracuseStep 2430085 = 455641) (by norm_num)
theorem B3240113 : Blo 2159435 3240113 := bstep (se 2 (by rfl) ⟨1215042, by rfl⟩ : syracuseStep 3240113 = 2430085) B2430085
theorem B2160075 : Blo 2159435 2160075 := bstep (se 1 (by rfl) ⟨1620056, by rfl⟩ : syracuseStep 2160075 = 3240113) B3240113
theorem B2496853 : Blo 2159435 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B3329137 : Blo 2159435 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B4438849 : Blo 2159435 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B5918465 : Blo 2159435 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B15782573 : Blo 2159435 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B42086861 : Blo 2159435 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B28057907 : Blo 2159435 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B18705271 : Blo 2159435 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B24940361 : Blo 2159435 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B16626907 : Blo 2159435 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B22169209 : Blo 2159435 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B29558945 : Blo 2159435 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B78823853 : Blo 2159435 78823853 := bstep (se 3 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 78823853 = 29558945) B29558945
theorem B52549235 : Blo 2159435 52549235 := bstep (se 1 (by rfl) ⟨39411926, by rfl⟩ : syracuseStep 52549235 = 78823853) B78823853
theorem B35032823 : Blo 2159435 35032823 := bstep (se 1 (by rfl) ⟨26274617, by rfl⟩ : syracuseStep 35032823 = 52549235) B52549235
theorem B23355215 : Blo 2159435 23355215 := bstep (se 1 (by rfl) ⟨17516411, by rfl⟩ : syracuseStep 23355215 = 35032823) B35032823
theorem B15570143 : Blo 2159435 15570143 := bstep (se 1 (by rfl) ⟨11677607, by rfl⟩ : syracuseStep 15570143 = 23355215) B23355215
theorem B10380095 : Blo 2159435 10380095 := bstep (se 1 (by rfl) ⟨7785071, by rfl⟩ : syracuseStep 10380095 = 15570143) B15570143
theorem B6920063 : Blo 2159435 6920063 := bstep (se 1 (by rfl) ⟨5190047, by rfl⟩ : syracuseStep 6920063 = 10380095) B10380095
theorem B4613375 : Blo 2159435 4613375 := bstep (se 1 (by rfl) ⟨3460031, by rfl⟩ : syracuseStep 4613375 = 6920063) B6920063
theorem B3075583 : Blo 2159435 3075583 := bstep (se 1 (by rfl) ⟨2306687, by rfl⟩ : syracuseStep 3075583 = 4613375) B4613375
theorem B4100777 : Blo 2159435 4100777 := bstep (se 2 (by rfl) ⟨1537791, by rfl⟩ : syracuseStep 4100777 = 3075583) B3075583
theorem B2733851 : Blo 2159435 2733851 := bstep (se 1 (by rfl) ⟨2050388, by rfl⟩ : syracuseStep 2733851 = 4100777) B4100777
theorem B7290269 : Blo 2159435 7290269 := bstep (se 3 (by rfl) ⟨1366925, by rfl⟩ : syracuseStep 7290269 = 2733851) B2733851
theorem B4860179 : Blo 2159435 4860179 := bstep (se 1 (by rfl) ⟨3645134, by rfl⟩ : syracuseStep 4860179 = 7290269) B7290269
theorem B3240119 : Blo 2159435 3240119 := bstep (se 1 (by rfl) ⟨2430089, by rfl⟩ : syracuseStep 3240119 = 4860179) B4860179
theorem B2160079 : Blo 2159435 2160079 := bstep (se 1 (by rfl) ⟨1620059, by rfl⟩ : syracuseStep 2160079 = 3240119) B3240119
theorem B3240125 : Blo 2159435 3240125 := bbase (se 3 (by rfl) ⟨607523, by rfl⟩ : syracuseStep 3240125 = 1215047) (by norm_num)
theorem B2160083 : Blo 2159435 2160083 := bstep (se 1 (by rfl) ⟨1620062, by rfl⟩ : syracuseStep 2160083 = 3240125) B3240125
theorem B4860197 : Blo 2159435 4860197 := bbase (se 4 (by rfl) ⟨455643, by rfl⟩ : syracuseStep 4860197 = 911287) (by norm_num)
theorem B3240131 : Blo 2159435 3240131 := bstep (se 1 (by rfl) ⟨2430098, by rfl⟩ : syracuseStep 3240131 = 4860197) B4860197
theorem B2160087 : Blo 2159435 2160087 := bstep (se 1 (by rfl) ⟨1620065, by rfl⟩ : syracuseStep 2160087 = 3240131) B3240131
theorem B5467733 : Blo 2159435 5467733 := bbase (se 8 (by rfl) ⟨32037, by rfl⟩ : syracuseStep 5467733 = 64075) (by norm_num)
theorem B3645155 : Blo 2159435 3645155 := bstep (se 1 (by rfl) ⟨2733866, by rfl⟩ : syracuseStep 3645155 = 5467733) B5467733
theorem B2430103 : Blo 2159435 2430103 := bstep (se 1 (by rfl) ⟨1822577, by rfl⟩ : syracuseStep 2430103 = 3645155) B3645155
theorem B3240137 : Blo 2159435 3240137 := bstep (se 2 (by rfl) ⟨1215051, by rfl⟩ : syracuseStep 3240137 = 2430103) B2430103
theorem B2160091 : Blo 2159435 2160091 := bstep (se 1 (by rfl) ⟨1620068, by rfl⟩ : syracuseStep 2160091 = 3240137) B3240137
theorem B5190085 : Blo 2159435 5190085 := bbase (se 4 (by rfl) ⟨486570, by rfl⟩ : syracuseStep 5190085 = 973141) (by norm_num)
theorem B6920113 : Blo 2159435 6920113 := bstep (se 2 (by rfl) ⟨2595042, by rfl⟩ : syracuseStep 6920113 = 5190085) B5190085
theorem B9226817 : Blo 2159435 9226817 := bstep (se 2 (by rfl) ⟨3460056, by rfl⟩ : syracuseStep 9226817 = 6920113) B6920113
theorem B6151211 : Blo 2159435 6151211 := bstep (se 1 (by rfl) ⟨4613408, by rfl⟩ : syracuseStep 6151211 = 9226817) B9226817
theorem B4100807 : Blo 2159435 4100807 := bstep (se 1 (by rfl) ⟨3075605, by rfl⟩ : syracuseStep 4100807 = 6151211) B6151211
theorem B10935485 : Blo 2159435 10935485 := bstep (se 3 (by rfl) ⟨2050403, by rfl⟩ : syracuseStep 10935485 = 4100807) B4100807
theorem B7290323 : Blo 2159435 7290323 := bstep (se 1 (by rfl) ⟨5467742, by rfl⟩ : syracuseStep 7290323 = 10935485) B10935485
theorem B4860215 : Blo 2159435 4860215 := bstep (se 1 (by rfl) ⟨3645161, by rfl⟩ : syracuseStep 4860215 = 7290323) B7290323
theorem B3240143 : Blo 2159435 3240143 := bstep (se 1 (by rfl) ⟨2430107, by rfl⟩ : syracuseStep 3240143 = 4860215) B4860215
theorem B2160095 : Blo 2159435 2160095 := bstep (se 1 (by rfl) ⟨1620071, by rfl⟩ : syracuseStep 2160095 = 3240143) B3240143
theorem B3240149 : Blo 2159435 3240149 := bbase (se 7 (by rfl) ⟨37970, by rfl⟩ : syracuseStep 3240149 = 75941) (by norm_num)
theorem B2160099 : Blo 2159435 2160099 := bstep (se 1 (by rfl) ⟨1620074, by rfl⟩ : syracuseStep 2160099 = 3240149) B3240149
theorem B2306713 : Blo 2159435 2306713 := bbase (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) (by norm_num)
theorem B3075617 : Blo 2159435 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B8201645 : Blo 2159435 8201645 := bstep (se 3 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 8201645 = 3075617) B3075617
theorem B5467763 : Blo 2159435 5467763 := bstep (se 1 (by rfl) ⟨4100822, by rfl⟩ : syracuseStep 5467763 = 8201645) B8201645
theorem B3645175 : Blo 2159435 3645175 := bstep (se 1 (by rfl) ⟨2733881, by rfl⟩ : syracuseStep 3645175 = 5467763) B5467763
theorem B4860233 : Blo 2159435 4860233 := bstep (se 2 (by rfl) ⟨1822587, by rfl⟩ : syracuseStep 4860233 = 3645175) B3645175
theorem B3240155 : Blo 2159435 3240155 := bstep (se 1 (by rfl) ⟨2430116, by rfl⟩ : syracuseStep 3240155 = 4860233) B4860233
theorem B2160103 : Blo 2159435 2160103 := bstep (se 1 (by rfl) ⟨1620077, by rfl⟩ : syracuseStep 2160103 = 3240155) B3240155
theorem B2430121 : Blo 2159435 2430121 := bbase (se 2 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 2430121 = 1822591) (by norm_num)
theorem B3240161 : Blo 2159435 3240161 := bstep (se 2 (by rfl) ⟨1215060, by rfl⟩ : syracuseStep 3240161 = 2430121) B2430121
theorem B2160107 : Blo 2159435 2160107 := bstep (se 1 (by rfl) ⟨1620080, by rfl⟩ : syracuseStep 2160107 = 3240161) B3240161
theorem B9226885 : Blo 2159435 9226885 := bbase (se 4 (by rfl) ⟨865020, by rfl⟩ : syracuseStep 9226885 = 1730041) (by norm_num)
theorem B12302513 : Blo 2159435 12302513 := bstep (se 2 (by rfl) ⟨4613442, by rfl⟩ : syracuseStep 12302513 = 9226885) B9226885
theorem B8201675 : Blo 2159435 8201675 := bstep (se 1 (by rfl) ⟨6151256, by rfl⟩ : syracuseStep 8201675 = 12302513) B12302513
theorem B5467783 : Blo 2159435 5467783 := bstep (se 1 (by rfl) ⟨4100837, by rfl⟩ : syracuseStep 5467783 = 8201675) B8201675
theorem B7290377 : Blo 2159435 7290377 := bstep (se 2 (by rfl) ⟨2733891, by rfl⟩ : syracuseStep 7290377 = 5467783) B5467783
theorem B4860251 : Blo 2159435 4860251 := bstep (se 1 (by rfl) ⟨3645188, by rfl⟩ : syracuseStep 4860251 = 7290377) B7290377
theorem B3240167 : Blo 2159435 3240167 := bstep (se 1 (by rfl) ⟨2430125, by rfl⟩ : syracuseStep 3240167 = 4860251) B4860251
theorem B2160111 : Blo 2159435 2160111 := bstep (se 1 (by rfl) ⟨1620083, by rfl⟩ : syracuseStep 2160111 = 3240167) B3240167
theorem B3240173 : Blo 2159435 3240173 := bbase (se 3 (by rfl) ⟨607532, by rfl⟩ : syracuseStep 3240173 = 1215065) (by norm_num)
theorem B2160115 : Blo 2159435 2160115 := bstep (se 1 (by rfl) ⟨1620086, by rfl⟩ : syracuseStep 2160115 = 3240173) B3240173
theorem B4860269 : Blo 2159435 4860269 := bbase (se 3 (by rfl) ⟨911300, by rfl⟩ : syracuseStep 4860269 = 1822601) (by norm_num)
theorem B3240179 : Blo 2159435 3240179 := bstep (se 1 (by rfl) ⟨2430134, by rfl⟩ : syracuseStep 3240179 = 4860269) B4860269
theorem B2160119 : Blo 2159435 2160119 := bstep (se 1 (by rfl) ⟨1620089, by rfl⟩ : syracuseStep 2160119 = 3240179) B3240179
theorem B4100861 : Blo 2159435 4100861 := bbase (se 3 (by rfl) ⟨768911, by rfl⟩ : syracuseStep 4100861 = 1537823) (by norm_num)
theorem B2733907 : Blo 2159435 2733907 := bstep (se 1 (by rfl) ⟨2050430, by rfl⟩ : syracuseStep 2733907 = 4100861) B4100861
theorem B3645209 : Blo 2159435 3645209 := bstep (se 2 (by rfl) ⟨1366953, by rfl⟩ : syracuseStep 3645209 = 2733907) B2733907
theorem B2430139 : Blo 2159435 2430139 := bstep (se 1 (by rfl) ⟨1822604, by rfl⟩ : syracuseStep 2430139 = 3645209) B3645209
theorem B3240185 : Blo 2159435 3240185 := bstep (se 2 (by rfl) ⟨1215069, by rfl⟩ : syracuseStep 3240185 = 2430139) B2430139
theorem B2160123 : Blo 2159435 2160123 := bstep (se 1 (by rfl) ⟨1620092, by rfl⟩ : syracuseStep 2160123 = 3240185) B3240185
theorem B3892621 : Blo 2159435 3892621 := bbase (se 3 (by rfl) ⟨729866, by rfl⟩ : syracuseStep 3892621 = 1459733) (by norm_num)
theorem B5190161 : Blo 2159435 5190161 := bstep (se 2 (by rfl) ⟨1946310, by rfl⟩ : syracuseStep 5190161 = 3892621) B3892621
theorem B55361717 : Blo 2159435 55361717 := bstep (se 5 (by rfl) ⟨2595080, by rfl⟩ : syracuseStep 55361717 = 5190161) B5190161
theorem B36907811 : Blo 2159435 36907811 := bstep (se 1 (by rfl) ⟨27680858, by rfl⟩ : syracuseStep 36907811 = 55361717) B55361717
theorem B24605207 : Blo 2159435 24605207 := bstep (se 1 (by rfl) ⟨18453905, by rfl⟩ : syracuseStep 24605207 = 36907811) B36907811
theorem B16403471 : Blo 2159435 16403471 := bstep (se 1 (by rfl) ⟨12302603, by rfl⟩ : syracuseStep 16403471 = 24605207) B24605207
theorem B10935647 : Blo 2159435 10935647 := bstep (se 1 (by rfl) ⟨8201735, by rfl⟩ : syracuseStep 10935647 = 16403471) B16403471
theorem B7290431 : Blo 2159435 7290431 := bstep (se 1 (by rfl) ⟨5467823, by rfl⟩ : syracuseStep 7290431 = 10935647) B10935647
theorem B4860287 : Blo 2159435 4860287 := bstep (se 1 (by rfl) ⟨3645215, by rfl⟩ : syracuseStep 4860287 = 7290431) B7290431
theorem B3240191 : Blo 2159435 3240191 := bstep (se 1 (by rfl) ⟨2430143, by rfl⟩ : syracuseStep 3240191 = 4860287) B4860287
theorem B2160127 : Blo 2159435 2160127 := bstep (se 1 (by rfl) ⟨1620095, by rfl⟩ : syracuseStep 2160127 = 3240191) B3240191
theorem B3240197 : Blo 2159435 3240197 := bbase (se 4 (by rfl) ⟨303768, by rfl⟩ : syracuseStep 3240197 = 607537) (by norm_num)
theorem B2160131 : Blo 2159435 2160131 := bstep (se 1 (by rfl) ⟨1620098, by rfl⟩ : syracuseStep 2160131 = 3240197) B3240197
theorem B3645229 : Blo 2159435 3645229 := bbase (se 3 (by rfl) ⟨683480, by rfl⟩ : syracuseStep 3645229 = 1366961) (by norm_num)
theorem B4860305 : Blo 2159435 4860305 := bstep (se 2 (by rfl) ⟨1822614, by rfl⟩ : syracuseStep 4860305 = 3645229) B3645229
theorem B3240203 : Blo 2159435 3240203 := bstep (se 1 (by rfl) ⟨2430152, by rfl⟩ : syracuseStep 3240203 = 4860305) B4860305
theorem B2160135 : Blo 2159435 2160135 := bstep (se 1 (by rfl) ⟨1620101, by rfl⟩ : syracuseStep 2160135 = 3240203) B3240203
theorem B2430157 : Blo 2159435 2430157 := bbase (se 3 (by rfl) ⟨455654, by rfl⟩ : syracuseStep 2430157 = 911309) (by norm_num)
theorem B3240209 : Blo 2159435 3240209 := bstep (se 2 (by rfl) ⟨1215078, by rfl⟩ : syracuseStep 3240209 = 2430157) B2430157
theorem B2160139 : Blo 2159435 2160139 := bstep (se 1 (by rfl) ⟨1620104, by rfl⟩ : syracuseStep 2160139 = 3240209) B3240209
theorem B7290485 : Blo 2159435 7290485 := bbase (se 5 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 7290485 = 683483) (by norm_num)
theorem B4860323 : Blo 2159435 4860323 := bstep (se 1 (by rfl) ⟨3645242, by rfl⟩ : syracuseStep 4860323 = 7290485) B7290485
theorem B3240215 : Blo 2159435 3240215 := bstep (se 1 (by rfl) ⟨2430161, by rfl⟩ : syracuseStep 3240215 = 4860323) B4860323
theorem B2160143 : Blo 2159435 2160143 := bstep (se 1 (by rfl) ⟨1620107, by rfl⟩ : syracuseStep 2160143 = 3240215) B3240215
theorem B3240221 : Blo 2159435 3240221 := bbase (se 3 (by rfl) ⟨607541, by rfl⟩ : syracuseStep 3240221 = 1215083) (by norm_num)
theorem B2160147 : Blo 2159435 2160147 := bstep (se 1 (by rfl) ⟨1620110, by rfl⟩ : syracuseStep 2160147 = 3240221) B3240221
theorem B4860341 : Blo 2159435 4860341 := bbase (se 5 (by rfl) ⟨227828, by rfl⟩ : syracuseStep 4860341 = 455657) (by norm_num)
theorem B3240227 : Blo 2159435 3240227 := bstep (se 1 (by rfl) ⟨2430170, by rfl⟩ : syracuseStep 3240227 = 4860341) B4860341
theorem B2160151 : Blo 2159435 2160151 := bstep (se 1 (by rfl) ⟨1620113, by rfl⟩ : syracuseStep 2160151 = 3240227) B3240227
theorem B2189629 : Blo 2159435 2189629 := bbase (se 3 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 2189629 = 821111) (by norm_num)
theorem B2919505 : Blo 2159435 2919505 := bstep (se 2 (by rfl) ⟨1094814, by rfl⟩ : syracuseStep 2919505 = 2189629) B2189629
theorem B3892673 : Blo 2159435 3892673 := bstep (se 2 (by rfl) ⟨1459752, by rfl⟩ : syracuseStep 3892673 = 2919505) B2919505
theorem B2595115 : Blo 2159435 2595115 := bstep (se 1 (by rfl) ⟨1946336, by rfl⟩ : syracuseStep 2595115 = 3892673) B3892673
theorem B3460153 : Blo 2159435 3460153 := bstep (se 2 (by rfl) ⟨1297557, by rfl⟩ : syracuseStep 3460153 = 2595115) B2595115
theorem B4613537 : Blo 2159435 4613537 := bstep (se 2 (by rfl) ⟨1730076, by rfl⟩ : syracuseStep 4613537 = 3460153) B3460153
theorem B12302765 : Blo 2159435 12302765 := bstep (se 3 (by rfl) ⟨2306768, by rfl⟩ : syracuseStep 12302765 = 4613537) B4613537
theorem B8201843 : Blo 2159435 8201843 := bstep (se 1 (by rfl) ⟨6151382, by rfl⟩ : syracuseStep 8201843 = 12302765) B12302765
theorem B5467895 : Blo 2159435 5467895 := bstep (se 1 (by rfl) ⟨4100921, by rfl⟩ : syracuseStep 5467895 = 8201843) B8201843
theorem B3645263 : Blo 2159435 3645263 := bstep (se 1 (by rfl) ⟨2733947, by rfl⟩ : syracuseStep 3645263 = 5467895) B5467895
theorem B2430175 : Blo 2159435 2430175 := bstep (se 1 (by rfl) ⟨1822631, by rfl⟩ : syracuseStep 2430175 = 3645263) B3645263
theorem B3240233 : Blo 2159435 3240233 := bstep (se 2 (by rfl) ⟨1215087, by rfl⟩ : syracuseStep 3240233 = 2430175) B2430175
theorem B2160155 : Blo 2159435 2160155 := bstep (se 1 (by rfl) ⟨1620116, by rfl⟩ : syracuseStep 2160155 = 3240233) B3240233
theorem B3695005 : Blo 2159435 3695005 := bbase (se 3 (by rfl) ⟨692813, by rfl⟩ : syracuseStep 3695005 = 1385627) (by norm_num)
theorem B4926673 : Blo 2159435 4926673 := bstep (se 2 (by rfl) ⟨1847502, by rfl⟩ : syracuseStep 4926673 = 3695005) B3695005
theorem B26275589 : Blo 2159435 26275589 := bstep (se 4 (by rfl) ⟨2463336, by rfl⟩ : syracuseStep 26275589 = 4926673) B4926673
theorem B17517059 : Blo 2159435 17517059 := bstep (se 1 (by rfl) ⟨13137794, by rfl⟩ : syracuseStep 17517059 = 26275589) B26275589
theorem B11678039 : Blo 2159435 11678039 := bstep (se 1 (by rfl) ⟨8758529, by rfl⟩ : syracuseStep 11678039 = 17517059) B17517059
theorem B7785359 : Blo 2159435 7785359 := bstep (se 1 (by rfl) ⟨5839019, by rfl⟩ : syracuseStep 7785359 = 11678039) B11678039
theorem B5190239 : Blo 2159435 5190239 := bstep (se 1 (by rfl) ⟨3892679, by rfl⟩ : syracuseStep 5190239 = 7785359) B7785359
theorem B3460159 : Blo 2159435 3460159 := bstep (se 1 (by rfl) ⟨2595119, by rfl⟩ : syracuseStep 3460159 = 5190239) B5190239
theorem B4613545 : Blo 2159435 4613545 := bstep (se 2 (by rfl) ⟨1730079, by rfl⟩ : syracuseStep 4613545 = 3460159) B3460159
theorem B6151393 : Blo 2159435 6151393 := bstep (se 2 (by rfl) ⟨2306772, by rfl⟩ : syracuseStep 6151393 = 4613545) B4613545
theorem B8201857 : Blo 2159435 8201857 := bstep (se 2 (by rfl) ⟨3075696, by rfl⟩ : syracuseStep 8201857 = 6151393) B6151393
theorem B10935809 : Blo 2159435 10935809 := bstep (se 2 (by rfl) ⟨4100928, by rfl⟩ : syracuseStep 10935809 = 8201857) B8201857
theorem B7290539 : Blo 2159435 7290539 := bstep (se 1 (by rfl) ⟨5467904, by rfl⟩ : syracuseStep 7290539 = 10935809) B10935809
theorem B4860359 : Blo 2159435 4860359 := bstep (se 1 (by rfl) ⟨3645269, by rfl⟩ : syracuseStep 4860359 = 7290539) B7290539
theorem B3240239 : Blo 2159435 3240239 := bstep (se 1 (by rfl) ⟨2430179, by rfl⟩ : syracuseStep 3240239 = 4860359) B4860359
theorem B2160159 : Blo 2159435 2160159 := bstep (se 1 (by rfl) ⟨1620119, by rfl⟩ : syracuseStep 2160159 = 3240239) B3240239
theorem B3240245 : Blo 2159435 3240245 := bbase (se 5 (by rfl) ⟨151886, by rfl⟩ : syracuseStep 3240245 = 303773) (by norm_num)
theorem B2160163 : Blo 2159435 2160163 := bstep (se 1 (by rfl) ⟨1620122, by rfl⟩ : syracuseStep 2160163 = 3240245) B3240245
theorem B5467925 : Blo 2159435 5467925 := bbase (se 6 (by rfl) ⟨128154, by rfl⟩ : syracuseStep 5467925 = 256309) (by norm_num)
theorem B3645283 : Blo 2159435 3645283 := bstep (se 1 (by rfl) ⟨2733962, by rfl⟩ : syracuseStep 3645283 = 5467925) B5467925
theorem B4860377 : Blo 2159435 4860377 := bstep (se 2 (by rfl) ⟨1822641, by rfl⟩ : syracuseStep 4860377 = 3645283) B3645283
theorem B3240251 : Blo 2159435 3240251 := bstep (se 1 (by rfl) ⟨2430188, by rfl⟩ : syracuseStep 3240251 = 4860377) B4860377
theorem B2160167 : Blo 2159435 2160167 := bstep (se 1 (by rfl) ⟨1620125, by rfl⟩ : syracuseStep 2160167 = 3240251) B3240251
theorem B2430193 : Blo 2159435 2430193 := bbase (se 2 (by rfl) ⟨911322, by rfl⟩ : syracuseStep 2430193 = 1822645) (by norm_num)
theorem B3240257 : Blo 2159435 3240257 := bstep (se 2 (by rfl) ⟨1215096, by rfl⟩ : syracuseStep 3240257 = 2430193) B2430193
theorem B2160171 : Blo 2159435 2160171 := bstep (se 1 (by rfl) ⟨1620128, by rfl⟩ : syracuseStep 2160171 = 3240257) B3240257
theorem B20761109 : Blo 2159435 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B13840739 : Blo 2159435 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B9227159 : Blo 2159435 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B6151439 : Blo 2159435 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B4100959 : Blo 2159435 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B5467945 : Blo 2159435 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B7290593 : Blo 2159435 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B4860395 : Blo 2159435 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B3240263 : Blo 2159435 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B2160175 : Blo 2159435 2160175 := bstep (se 1 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 2160175 = 3240263) B3240263
theorem B3240269 : Blo 2159435 3240269 := bbase (se 3 (by rfl) ⟨607550, by rfl⟩ : syracuseStep 3240269 = 1215101) (by norm_num)
theorem B2160179 : Blo 2159435 2160179 := bstep (se 1 (by rfl) ⟨1620134, by rfl⟩ : syracuseStep 2160179 = 3240269) B3240269
theorem B4860413 : Blo 2159435 4860413 := bbase (se 3 (by rfl) ⟨911327, by rfl⟩ : syracuseStep 4860413 = 1822655) (by norm_num)
theorem B3240275 : Blo 2159435 3240275 := bstep (se 1 (by rfl) ⟨2430206, by rfl⟩ : syracuseStep 3240275 = 4860413) B4860413
theorem B2160183 : Blo 2159435 2160183 := bstep (se 1 (by rfl) ⟨1620137, by rfl⟩ : syracuseStep 2160183 = 3240275) B3240275
theorem B3645317 : Blo 2159435 3645317 := bbase (se 4 (by rfl) ⟨341748, by rfl⟩ : syracuseStep 3645317 = 683497) (by norm_num)
theorem B2430211 : Blo 2159435 2430211 := bstep (se 1 (by rfl) ⟨1822658, by rfl⟩ : syracuseStep 2430211 = 3645317) B3645317
theorem B3240281 : Blo 2159435 3240281 := bstep (se 2 (by rfl) ⟨1215105, by rfl⟩ : syracuseStep 3240281 = 2430211) B2430211
theorem B2160187 : Blo 2159435 2160187 := bstep (se 1 (by rfl) ⟨1620140, by rfl⟩ : syracuseStep 2160187 = 3240281) B3240281
theorem B16403957 : Blo 2159435 16403957 := bbase (se 5 (by rfl) ⟨768935, by rfl⟩ : syracuseStep 16403957 = 1537871) (by norm_num)
theorem B10935971 : Blo 2159435 10935971 := bstep (se 1 (by rfl) ⟨8201978, by rfl⟩ : syracuseStep 10935971 = 16403957) B16403957
theorem B7290647 : Blo 2159435 7290647 := bstep (se 1 (by rfl) ⟨5467985, by rfl⟩ : syracuseStep 7290647 = 10935971) B10935971
theorem B4860431 : Blo 2159435 4860431 := bstep (se 1 (by rfl) ⟨3645323, by rfl⟩ : syracuseStep 4860431 = 7290647) B7290647
theorem B3240287 : Blo 2159435 3240287 := bstep (se 1 (by rfl) ⟨2430215, by rfl⟩ : syracuseStep 3240287 = 4860431) B4860431
theorem B2160191 : Blo 2159435 2160191 := bstep (se 1 (by rfl) ⟨1620143, by rfl⟩ : syracuseStep 2160191 = 3240287) B3240287
theorem B3240293 : Blo 2159435 3240293 := bbase (se 4 (by rfl) ⟨303777, by rfl⟩ : syracuseStep 3240293 = 607555) (by norm_num)
theorem B2160195 : Blo 2159435 2160195 := bstep (se 1 (by rfl) ⟨1620146, by rfl⟩ : syracuseStep 2160195 = 3240293) B3240293
theorem B4101005 : Blo 2159435 4101005 := bbase (se 3 (by rfl) ⟨768938, by rfl⟩ : syracuseStep 4101005 = 1537877) (by norm_num)
theorem B2734003 : Blo 2159435 2734003 := bstep (se 1 (by rfl) ⟨2050502, by rfl⟩ : syracuseStep 2734003 = 4101005) B4101005
theorem B3645337 : Blo 2159435 3645337 := bstep (se 2 (by rfl) ⟨1367001, by rfl⟩ : syracuseStep 3645337 = 2734003) B2734003
theorem B4860449 : Blo 2159435 4860449 := bstep (se 2 (by rfl) ⟨1822668, by rfl⟩ : syracuseStep 4860449 = 3645337) B3645337
theorem B3240299 : Blo 2159435 3240299 := bstep (se 1 (by rfl) ⟨2430224, by rfl⟩ : syracuseStep 3240299 = 4860449) B4860449
theorem B2160199 : Blo 2159435 2160199 := bstep (se 1 (by rfl) ⟨1620149, by rfl⟩ : syracuseStep 2160199 = 3240299) B3240299
theorem B2430229 : Blo 2159435 2430229 := bbase (se 6 (by rfl) ⟨56958, by rfl⟩ : syracuseStep 2430229 = 113917) (by norm_num)
theorem B3240305 : Blo 2159435 3240305 := bstep (se 2 (by rfl) ⟨1215114, by rfl⟩ : syracuseStep 3240305 = 2430229) B2430229
theorem B2160203 : Blo 2159435 2160203 := bstep (se 1 (by rfl) ⟨1620152, by rfl⟩ : syracuseStep 2160203 = 3240305) B3240305
theorem B2734013 : Blo 2159435 2734013 := bbase (se 3 (by rfl) ⟨512627, by rfl⟩ : syracuseStep 2734013 = 1025255) (by norm_num)
theorem B7290701 : Blo 2159435 7290701 := bstep (se 3 (by rfl) ⟨1367006, by rfl⟩ : syracuseStep 7290701 = 2734013) B2734013
theorem B4860467 : Blo 2159435 4860467 := bstep (se 1 (by rfl) ⟨3645350, by rfl⟩ : syracuseStep 4860467 = 7290701) B7290701
theorem B3240311 : Blo 2159435 3240311 := bstep (se 1 (by rfl) ⟨2430233, by rfl⟩ : syracuseStep 3240311 = 4860467) B4860467
theorem B2160207 : Blo 2159435 2160207 := bstep (se 1 (by rfl) ⟨1620155, by rfl⟩ : syracuseStep 2160207 = 3240311) B3240311
theorem B3240317 : Blo 2159435 3240317 := bbase (se 3 (by rfl) ⟨607559, by rfl⟩ : syracuseStep 3240317 = 1215119) (by norm_num)
theorem B2160211 : Blo 2159435 2160211 := bstep (se 1 (by rfl) ⟨1620158, by rfl⟩ : syracuseStep 2160211 = 3240317) B3240317
theorem B4860485 : Blo 2159435 4860485 := bbase (se 4 (by rfl) ⟨455670, by rfl⟩ : syracuseStep 4860485 = 911341) (by norm_num)
theorem B3240323 : Blo 2159435 3240323 := bstep (se 1 (by rfl) ⟨2430242, by rfl⟩ : syracuseStep 3240323 = 4860485) B4860485
theorem B2160215 : Blo 2159435 2160215 := bstep (se 1 (by rfl) ⟨1620161, by rfl⟩ : syracuseStep 2160215 = 3240323) B3240323
theorem B2306837 : Blo 2159435 2306837 := bbase (se 6 (by rfl) ⟨54066, by rfl⟩ : syracuseStep 2306837 = 108133) (by norm_num)
theorem B6151565 : Blo 2159435 6151565 := bstep (se 3 (by rfl) ⟨1153418, by rfl⟩ : syracuseStep 6151565 = 2306837) B2306837
theorem B4101043 : Blo 2159435 4101043 := bstep (se 1 (by rfl) ⟨3075782, by rfl⟩ : syracuseStep 4101043 = 6151565) B6151565
theorem B5468057 : Blo 2159435 5468057 := bstep (se 2 (by rfl) ⟨2050521, by rfl⟩ : syracuseStep 5468057 = 4101043) B4101043
theorem B3645371 : Blo 2159435 3645371 := bstep (se 1 (by rfl) ⟨2734028, by rfl⟩ : syracuseStep 3645371 = 5468057) B5468057
theorem B2430247 : Blo 2159435 2430247 := bstep (se 1 (by rfl) ⟨1822685, by rfl⟩ : syracuseStep 2430247 = 3645371) B3645371
theorem B3240329 : Blo 2159435 3240329 := bstep (se 2 (by rfl) ⟨1215123, by rfl⟩ : syracuseStep 3240329 = 2430247) B2430247
theorem B2160219 : Blo 2159435 2160219 := bstep (se 1 (by rfl) ⟨1620164, by rfl⟩ : syracuseStep 2160219 = 3240329) B3240329
theorem B10936133 : Blo 2159435 10936133 := bbase (se 4 (by rfl) ⟨1025262, by rfl⟩ : syracuseStep 10936133 = 2050525) (by norm_num)
theorem B7290755 : Blo 2159435 7290755 := bstep (se 1 (by rfl) ⟨5468066, by rfl⟩ : syracuseStep 7290755 = 10936133) B10936133
theorem B4860503 : Blo 2159435 4860503 := bstep (se 1 (by rfl) ⟨3645377, by rfl⟩ : syracuseStep 4860503 = 7290755) B7290755
theorem B3240335 : Blo 2159435 3240335 := bstep (se 1 (by rfl) ⟨2430251, by rfl⟩ : syracuseStep 3240335 = 4860503) B4860503
theorem B2160223 : Blo 2159435 2160223 := bstep (se 1 (by rfl) ⟨1620167, by rfl⟩ : syracuseStep 2160223 = 3240335) B3240335
theorem B3240341 : Blo 2159435 3240341 := bbase (se 6 (by rfl) ⟨75945, by rfl⟩ : syracuseStep 3240341 = 151891) (by norm_num)
theorem B2160227 : Blo 2159435 2160227 := bstep (se 1 (by rfl) ⟨1620170, by rfl⟩ : syracuseStep 2160227 = 3240341) B3240341
theorem B6920549 : Blo 2159435 6920549 := bbase (se 4 (by rfl) ⟨648801, by rfl⟩ : syracuseStep 6920549 = 1297603) (by norm_num)
theorem B4613699 : Blo 2159435 4613699 := bstep (se 1 (by rfl) ⟨3460274, by rfl⟩ : syracuseStep 4613699 = 6920549) B6920549
theorem B12303197 : Blo 2159435 12303197 := bstep (se 3 (by rfl) ⟨2306849, by rfl⟩ : syracuseStep 12303197 = 4613699) B4613699
theorem B8202131 : Blo 2159435 8202131 := bstep (se 1 (by rfl) ⟨6151598, by rfl⟩ : syracuseStep 8202131 = 12303197) B12303197
theorem B5468087 : Blo 2159435 5468087 := bstep (se 1 (by rfl) ⟨4101065, by rfl⟩ : syracuseStep 5468087 = 8202131) B8202131
theorem B3645391 : Blo 2159435 3645391 := bstep (se 1 (by rfl) ⟨2734043, by rfl⟩ : syracuseStep 3645391 = 5468087) B5468087
theorem B4860521 : Blo 2159435 4860521 := bstep (se 2 (by rfl) ⟨1822695, by rfl⟩ : syracuseStep 4860521 = 3645391) B3645391
theorem B3240347 : Blo 2159435 3240347 := bstep (se 1 (by rfl) ⟨2430260, by rfl⟩ : syracuseStep 3240347 = 4860521) B4860521
theorem B2160231 : Blo 2159435 2160231 := bstep (se 1 (by rfl) ⟨1620173, by rfl⟩ : syracuseStep 2160231 = 3240347) B3240347
theorem B2430265 : Blo 2159435 2430265 := bbase (se 2 (by rfl) ⟨911349, by rfl⟩ : syracuseStep 2430265 = 1822699) (by norm_num)
theorem B3240353 : Blo 2159435 3240353 := bstep (se 2 (by rfl) ⟨1215132, by rfl⟩ : syracuseStep 3240353 = 2430265) B2430265
theorem B2160235 : Blo 2159435 2160235 := bstep (se 1 (by rfl) ⟨1620176, by rfl⟩ : syracuseStep 2160235 = 3240353) B3240353
theorem B6151621 : Blo 2159435 6151621 := bbase (se 4 (by rfl) ⟨576714, by rfl⟩ : syracuseStep 6151621 = 1153429) (by norm_num)
theorem B8202161 : Blo 2159435 8202161 := bstep (se 2 (by rfl) ⟨3075810, by rfl⟩ : syracuseStep 8202161 = 6151621) B6151621
theorem B5468107 : Blo 2159435 5468107 := bstep (se 1 (by rfl) ⟨4101080, by rfl⟩ : syracuseStep 5468107 = 8202161) B8202161
theorem B7290809 : Blo 2159435 7290809 := bstep (se 2 (by rfl) ⟨2734053, by rfl⟩ : syracuseStep 7290809 = 5468107) B5468107
theorem B4860539 : Blo 2159435 4860539 := bstep (se 1 (by rfl) ⟨3645404, by rfl⟩ : syracuseStep 4860539 = 7290809) B7290809
theorem B3240359 : Blo 2159435 3240359 := bstep (se 1 (by rfl) ⟨2430269, by rfl⟩ : syracuseStep 3240359 = 4860539) B4860539
theorem B2160239 : Blo 2159435 2160239 := bstep (se 1 (by rfl) ⟨1620179, by rfl⟩ : syracuseStep 2160239 = 3240359) B3240359
theorem B3240365 : Blo 2159435 3240365 := bbase (se 3 (by rfl) ⟨607568, by rfl⟩ : syracuseStep 3240365 = 1215137) (by norm_num)
theorem B2160243 : Blo 2159435 2160243 := bstep (se 1 (by rfl) ⟨1620182, by rfl⟩ : syracuseStep 2160243 = 3240365) B3240365
theorem B4860557 : Blo 2159435 4860557 := bbase (se 3 (by rfl) ⟨911354, by rfl⟩ : syracuseStep 4860557 = 1822709) (by norm_num)
theorem B3240371 : Blo 2159435 3240371 := bstep (se 1 (by rfl) ⟨2430278, by rfl⟩ : syracuseStep 3240371 = 4860557) B4860557
theorem B2160247 : Blo 2159435 2160247 := bstep (se 1 (by rfl) ⟨1620185, by rfl⟩ : syracuseStep 2160247 = 3240371) B3240371
theorem B2734069 : Blo 2159435 2734069 := bbase (se 5 (by rfl) ⟨128159, by rfl⟩ : syracuseStep 2734069 = 256319) (by norm_num)
theorem B3645425 : Blo 2159435 3645425 := bstep (se 2 (by rfl) ⟨1367034, by rfl⟩ : syracuseStep 3645425 = 2734069) B2734069
theorem B2430283 : Blo 2159435 2430283 := bstep (se 1 (by rfl) ⟨1822712, by rfl⟩ : syracuseStep 2430283 = 3645425) B3645425
theorem B3240377 : Blo 2159435 3240377 := bstep (se 2 (by rfl) ⟨1215141, by rfl⟩ : syracuseStep 3240377 = 2430283) B2430283
theorem B2160251 : Blo 2159435 2160251 := bstep (se 1 (by rfl) ⟨1620188, by rfl⟩ : syracuseStep 2160251 = 3240377) B3240377
theorem B5261285 : Blo 2159435 5261285 := bbase (se 4 (by rfl) ⟨493245, by rfl⟩ : syracuseStep 5261285 = 986491) (by norm_num)
theorem B14030093 : Blo 2159435 14030093 := bstep (se 3 (by rfl) ⟨2630642, by rfl⟩ : syracuseStep 14030093 = 5261285) B5261285
theorem B9353395 : Blo 2159435 9353395 := bstep (se 1 (by rfl) ⟨7015046, by rfl⟩ : syracuseStep 9353395 = 14030093) B14030093
theorem B12471193 : Blo 2159435 12471193 := bstep (se 2 (by rfl) ⟨4676697, by rfl⟩ : syracuseStep 12471193 = 9353395) B9353395
theorem B16628257 : Blo 2159435 16628257 := bstep (se 2 (by rfl) ⟨6235596, by rfl⟩ : syracuseStep 16628257 = 12471193) B12471193
theorem B22171009 : Blo 2159435 22171009 := bstep (se 2 (by rfl) ⟨8314128, by rfl⟩ : syracuseStep 22171009 = 16628257) B16628257
theorem B29561345 : Blo 2159435 29561345 := bstep (se 2 (by rfl) ⟨11085504, by rfl⟩ : syracuseStep 29561345 = 22171009) B22171009
theorem B19707563 : Blo 2159435 19707563 := bstep (se 1 (by rfl) ⟨14780672, by rfl⟩ : syracuseStep 19707563 = 29561345) B29561345
theorem B13138375 : Blo 2159435 13138375 := bstep (se 1 (by rfl) ⟨9853781, by rfl⟩ : syracuseStep 13138375 = 19707563) B19707563
theorem B17517833 : Blo 2159435 17517833 := bstep (se 2 (by rfl) ⟨6569187, by rfl⟩ : syracuseStep 17517833 = 13138375) B13138375
theorem B11678555 : Blo 2159435 11678555 := bstep (se 1 (by rfl) ⟨8758916, by rfl⟩ : syracuseStep 11678555 = 17517833) B17517833
theorem B7785703 : Blo 2159435 7785703 := bstep (se 1 (by rfl) ⟨5839277, by rfl⟩ : syracuseStep 7785703 = 11678555) B11678555
theorem B41523749 : Blo 2159435 41523749 := bstep (se 4 (by rfl) ⟨3892851, by rfl⟩ : syracuseStep 41523749 = 7785703) B7785703
theorem B27682499 : Blo 2159435 27682499 := bstep (se 1 (by rfl) ⟨20761874, by rfl⟩ : syracuseStep 27682499 = 41523749) B41523749
theorem B18454999 : Blo 2159435 18454999 := bstep (se 1 (by rfl) ⟨13841249, by rfl⟩ : syracuseStep 18454999 = 27682499) B27682499
theorem B24606665 : Blo 2159435 24606665 := bstep (se 2 (by rfl) ⟨9227499, by rfl⟩ : syracuseStep 24606665 = 18454999) B18454999
theorem B16404443 : Blo 2159435 16404443 := bstep (se 1 (by rfl) ⟨12303332, by rfl⟩ : syracuseStep 16404443 = 24606665) B24606665
theorem B10936295 : Blo 2159435 10936295 := bstep (se 1 (by rfl) ⟨8202221, by rfl⟩ : syracuseStep 10936295 = 16404443) B16404443
theorem B7290863 : Blo 2159435 7290863 := bstep (se 1 (by rfl) ⟨5468147, by rfl⟩ : syracuseStep 7290863 = 10936295) B10936295
theorem B4860575 : Blo 2159435 4860575 := bstep (se 1 (by rfl) ⟨3645431, by rfl⟩ : syracuseStep 4860575 = 7290863) B7290863
theorem B3240383 : Blo 2159435 3240383 := bstep (se 1 (by rfl) ⟨2430287, by rfl⟩ : syracuseStep 3240383 = 4860575) B4860575
theorem B2160255 : Blo 2159435 2160255 := bstep (se 1 (by rfl) ⟨1620191, by rfl⟩ : syracuseStep 2160255 = 3240383) B3240383
theorem B3240389 : Blo 2159435 3240389 := bbase (se 4 (by rfl) ⟨303786, by rfl⟩ : syracuseStep 3240389 = 607573) (by norm_num)
theorem B2160259 : Blo 2159435 2160259 := bstep (se 1 (by rfl) ⟨1620194, by rfl⟩ : syracuseStep 2160259 = 3240389) B3240389
theorem B3645445 : Blo 2159435 3645445 := bbase (se 4 (by rfl) ⟨341760, by rfl⟩ : syracuseStep 3645445 = 683521) (by norm_num)
theorem B4860593 : Blo 2159435 4860593 := bstep (se 2 (by rfl) ⟨1822722, by rfl⟩ : syracuseStep 4860593 = 3645445) B3645445
theorem B3240395 : Blo 2159435 3240395 := bstep (se 1 (by rfl) ⟨2430296, by rfl⟩ : syracuseStep 3240395 = 4860593) B4860593
theorem B2160263 : Blo 2159435 2160263 := bstep (se 1 (by rfl) ⟨1620197, by rfl⟩ : syracuseStep 2160263 = 3240395) B3240395
theorem B2430301 : Blo 2159435 2430301 := bbase (se 3 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 2430301 = 911363) (by norm_num)
theorem B3240401 : Blo 2159435 3240401 := bstep (se 2 (by rfl) ⟨1215150, by rfl⟩ : syracuseStep 3240401 = 2430301) B2430301
theorem B2160267 : Blo 2159435 2160267 := bstep (se 1 (by rfl) ⟨1620200, by rfl⟩ : syracuseStep 2160267 = 3240401) B3240401
theorem B7290917 : Blo 2159435 7290917 := bbase (se 4 (by rfl) ⟨683523, by rfl⟩ : syracuseStep 7290917 = 1367047) (by norm_num)
theorem B4860611 : Blo 2159435 4860611 := bstep (se 1 (by rfl) ⟨3645458, by rfl⟩ : syracuseStep 4860611 = 7290917) B7290917
theorem B3240407 : Blo 2159435 3240407 := bstep (se 1 (by rfl) ⟨2430305, by rfl⟩ : syracuseStep 3240407 = 4860611) B4860611
theorem B2160271 : Blo 2159435 2160271 := bstep (se 1 (by rfl) ⟨1620203, by rfl⟩ : syracuseStep 2160271 = 3240407) B3240407
theorem B3240413 : Blo 2159435 3240413 := bbase (se 3 (by rfl) ⟨607577, by rfl⟩ : syracuseStep 3240413 = 1215155) (by norm_num)
theorem B2160275 : Blo 2159435 2160275 := bstep (se 1 (by rfl) ⟨1620206, by rfl⟩ : syracuseStep 2160275 = 3240413) B3240413
theorem B4860629 : Blo 2159435 4860629 := bbase (se 7 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 4860629 = 113921) (by norm_num)
theorem B3240419 : Blo 2159435 3240419 := bstep (se 1 (by rfl) ⟨2430314, by rfl⟩ : syracuseStep 3240419 = 4860629) B4860629
theorem B2160279 : Blo 2159435 2160279 := bstep (se 1 (by rfl) ⟨1620209, by rfl⟩ : syracuseStep 2160279 = 3240419) B3240419
theorem B9227621 : Blo 2159435 9227621 := bbase (se 4 (by rfl) ⟨865089, by rfl⟩ : syracuseStep 9227621 = 1730179) (by norm_num)
theorem B6151747 : Blo 2159435 6151747 := bstep (se 1 (by rfl) ⟨4613810, by rfl⟩ : syracuseStep 6151747 = 9227621) B9227621
theorem B8202329 : Blo 2159435 8202329 := bstep (se 2 (by rfl) ⟨3075873, by rfl⟩ : syracuseStep 8202329 = 6151747) B6151747
theorem B5468219 : Blo 2159435 5468219 := bstep (se 1 (by rfl) ⟨4101164, by rfl⟩ : syracuseStep 5468219 = 8202329) B8202329
theorem B3645479 : Blo 2159435 3645479 := bstep (se 1 (by rfl) ⟨2734109, by rfl⟩ : syracuseStep 3645479 = 5468219) B5468219
theorem B2430319 : Blo 2159435 2430319 := bstep (se 1 (by rfl) ⟨1822739, by rfl⟩ : syracuseStep 2430319 = 3645479) B3645479
theorem B3240425 : Blo 2159435 3240425 := bstep (se 2 (by rfl) ⟨1215159, by rfl⟩ : syracuseStep 3240425 = 2430319) B2430319
theorem B2160283 : Blo 2159435 2160283 := bstep (se 1 (by rfl) ⟨1620212, by rfl⟩ : syracuseStep 2160283 = 3240425) B3240425
theorem B2959517 : Blo 2159435 2959517 := bbase (se 3 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 2959517 = 1109819) (by norm_num)
theorem B7892045 : Blo 2159435 7892045 := bstep (se 3 (by rfl) ⟨1479758, by rfl⟩ : syracuseStep 7892045 = 2959517) B2959517
theorem B5261363 : Blo 2159435 5261363 := bstep (se 1 (by rfl) ⟨3946022, by rfl⟩ : syracuseStep 5261363 = 7892045) B7892045
theorem B3507575 : Blo 2159435 3507575 := bstep (se 1 (by rfl) ⟨2630681, by rfl⟩ : syracuseStep 3507575 = 5261363) B5261363
theorem B37414133 : Blo 2159435 37414133 := bstep (se 5 (by rfl) ⟨1753787, by rfl⟩ : syracuseStep 37414133 = 3507575) B3507575
theorem B24942755 : Blo 2159435 24942755 := bstep (se 1 (by rfl) ⟨18707066, by rfl⟩ : syracuseStep 24942755 = 37414133) B37414133
theorem B16628503 : Blo 2159435 16628503 := bstep (se 1 (by rfl) ⟨12471377, by rfl⟩ : syracuseStep 16628503 = 24942755) B24942755
theorem B22171337 : Blo 2159435 22171337 := bstep (se 2 (by rfl) ⟨8314251, by rfl⟩ : syracuseStep 22171337 = 16628503) B16628503
theorem B14780891 : Blo 2159435 14780891 := bstep (se 1 (by rfl) ⟨11085668, by rfl⟩ : syracuseStep 14780891 = 22171337) B22171337
theorem B39415709 : Blo 2159435 39415709 := bstep (se 3 (by rfl) ⟨7390445, by rfl⟩ : syracuseStep 39415709 = 14780891) B14780891
theorem B26277139 : Blo 2159435 26277139 := bstep (se 1 (by rfl) ⟨19707854, by rfl⟩ : syracuseStep 26277139 = 39415709) B39415709
theorem B35036185 : Blo 2159435 35036185 := bstep (se 2 (by rfl) ⟨13138569, by rfl⟩ : syracuseStep 35036185 = 26277139) B26277139
theorem B46714913 : Blo 2159435 46714913 := bstep (se 2 (by rfl) ⟨17518092, by rfl⟩ : syracuseStep 46714913 = 35036185) B35036185
theorem B31143275 : Blo 2159435 31143275 := bstep (se 1 (by rfl) ⟨23357456, by rfl⟩ : syracuseStep 31143275 = 46714913) B46714913
theorem B20762183 : Blo 2159435 20762183 := bstep (se 1 (by rfl) ⟨15571637, by rfl⟩ : syracuseStep 20762183 = 31143275) B31143275
theorem B13841455 : Blo 2159435 13841455 := bstep (se 1 (by rfl) ⟨10381091, by rfl⟩ : syracuseStep 13841455 = 20762183) B20762183
theorem B18455273 : Blo 2159435 18455273 := bstep (se 2 (by rfl) ⟨6920727, by rfl⟩ : syracuseStep 18455273 = 13841455) B13841455
theorem B12303515 : Blo 2159435 12303515 := bstep (se 1 (by rfl) ⟨9227636, by rfl⟩ : syracuseStep 12303515 = 18455273) B18455273
theorem B8202343 : Blo 2159435 8202343 := bstep (se 1 (by rfl) ⟨6151757, by rfl⟩ : syracuseStep 8202343 = 12303515) B12303515
theorem B10936457 : Blo 2159435 10936457 := bstep (se 2 (by rfl) ⟨4101171, by rfl⟩ : syracuseStep 10936457 = 8202343) B8202343
theorem B7290971 : Blo 2159435 7290971 := bstep (se 1 (by rfl) ⟨5468228, by rfl⟩ : syracuseStep 7290971 = 10936457) B10936457
theorem B4860647 : Blo 2159435 4860647 := bstep (se 1 (by rfl) ⟨3645485, by rfl⟩ : syracuseStep 4860647 = 7290971) B7290971
theorem B3240431 : Blo 2159435 3240431 := bstep (se 1 (by rfl) ⟨2430323, by rfl⟩ : syracuseStep 3240431 = 4860647) B4860647
theorem B2160287 : Blo 2159435 2160287 := bstep (se 1 (by rfl) ⟨1620215, by rfl⟩ : syracuseStep 2160287 = 3240431) B3240431
theorem B3240437 : Blo 2159435 3240437 := bbase (se 5 (by rfl) ⟨151895, by rfl⟩ : syracuseStep 3240437 = 303791) (by norm_num)
theorem B2160291 : Blo 2159435 2160291 := bstep (se 1 (by rfl) ⟨1620218, by rfl⟩ : syracuseStep 2160291 = 3240437) B3240437
theorem B6151781 : Blo 2159435 6151781 := bbase (se 4 (by rfl) ⟨576729, by rfl⟩ : syracuseStep 6151781 = 1153459) (by norm_num)
theorem B4101187 : Blo 2159435 4101187 := bstep (se 1 (by rfl) ⟨3075890, by rfl⟩ : syracuseStep 4101187 = 6151781) B6151781
theorem B5468249 : Blo 2159435 5468249 := bstep (se 2 (by rfl) ⟨2050593, by rfl⟩ : syracuseStep 5468249 = 4101187) B4101187
theorem B3645499 : Blo 2159435 3645499 := bstep (se 1 (by rfl) ⟨2734124, by rfl⟩ : syracuseStep 3645499 = 5468249) B5468249
theorem B4860665 : Blo 2159435 4860665 := bstep (se 2 (by rfl) ⟨1822749, by rfl⟩ : syracuseStep 4860665 = 3645499) B3645499
theorem B3240443 : Blo 2159435 3240443 := bstep (se 1 (by rfl) ⟨2430332, by rfl⟩ : syracuseStep 3240443 = 4860665) B4860665
theorem B2160295 : Blo 2159435 2160295 := bstep (se 1 (by rfl) ⟨1620221, by rfl⟩ : syracuseStep 2160295 = 3240443) B3240443
theorem B2430337 : Blo 2159435 2430337 := bbase (se 2 (by rfl) ⟨911376, by rfl⟩ : syracuseStep 2430337 = 1822753) (by norm_num)
theorem B3240449 : Blo 2159435 3240449 := bstep (se 2 (by rfl) ⟨1215168, by rfl⟩ : syracuseStep 3240449 = 2430337) B2430337
theorem B2160299 : Blo 2159435 2160299 := bstep (se 1 (by rfl) ⟨1620224, by rfl⟩ : syracuseStep 2160299 = 3240449) B3240449
theorem B5468269 : Blo 2159435 5468269 := bbase (se 3 (by rfl) ⟨1025300, by rfl⟩ : syracuseStep 5468269 = 2050601) (by norm_num)
theorem B7291025 : Blo 2159435 7291025 := bstep (se 2 (by rfl) ⟨2734134, by rfl⟩ : syracuseStep 7291025 = 5468269) B5468269
theorem B4860683 : Blo 2159435 4860683 := bstep (se 1 (by rfl) ⟨3645512, by rfl⟩ : syracuseStep 4860683 = 7291025) B7291025
theorem B3240455 : Blo 2159435 3240455 := bstep (se 1 (by rfl) ⟨2430341, by rfl⟩ : syracuseStep 3240455 = 4860683) B4860683
theorem B2160303 : Blo 2159435 2160303 := bstep (se 1 (by rfl) ⟨1620227, by rfl⟩ : syracuseStep 2160303 = 3240455) B3240455
theorem B3240461 : Blo 2159435 3240461 := bbase (se 3 (by rfl) ⟨607586, by rfl⟩ : syracuseStep 3240461 = 1215173) (by norm_num)
theorem B2160307 : Blo 2159435 2160307 := bstep (se 1 (by rfl) ⟨1620230, by rfl⟩ : syracuseStep 2160307 = 3240461) B3240461
theorem B4860701 : Blo 2159435 4860701 := bbase (se 3 (by rfl) ⟨911381, by rfl⟩ : syracuseStep 4860701 = 1822763) (by norm_num)
theorem B3240467 : Blo 2159435 3240467 := bstep (se 1 (by rfl) ⟨2430350, by rfl⟩ : syracuseStep 3240467 = 4860701) B4860701
theorem B2160311 : Blo 2159435 2160311 := bstep (se 1 (by rfl) ⟨1620233, by rfl⟩ : syracuseStep 2160311 = 3240467) B3240467
theorem B3645533 : Blo 2159435 3645533 := bbase (se 3 (by rfl) ⟨683537, by rfl⟩ : syracuseStep 3645533 = 1367075) (by norm_num)
theorem B2430355 : Blo 2159435 2430355 := bstep (se 1 (by rfl) ⟨1822766, by rfl⟩ : syracuseStep 2430355 = 3645533) B3645533
theorem B3240473 : Blo 2159435 3240473 := bstep (se 2 (by rfl) ⟨1215177, by rfl⟩ : syracuseStep 3240473 = 2430355) B2430355
theorem B2160315 : Blo 2159435 2160315 := bstep (se 1 (by rfl) ⟨1620236, by rfl⟩ : syracuseStep 2160315 = 3240473) B3240473
theorem B4676837 : Blo 2159435 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B12471565 : Blo 2159435 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B16628753 : Blo 2159435 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B11085835 : Blo 2159435 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B14781113 : Blo 2159435 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B9854075 : Blo 2159435 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B26277533 : Blo 2159435 26277533 := bstep (se 3 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 26277533 = 9854075) B9854075
theorem B17518355 : Blo 2159435 17518355 := bstep (se 1 (by rfl) ⟨13138766, by rfl⟩ : syracuseStep 17518355 = 26277533) B26277533
theorem B11678903 : Blo 2159435 11678903 := bstep (se 1 (by rfl) ⟨8759177, by rfl⟩ : syracuseStep 11678903 = 17518355) B17518355
theorem B7785935 : Blo 2159435 7785935 := bstep (se 1 (by rfl) ⟨5839451, by rfl⟩ : syracuseStep 7785935 = 11678903) B11678903
theorem B5190623 : Blo 2159435 5190623 := bstep (se 1 (by rfl) ⟨3892967, by rfl⟩ : syracuseStep 5190623 = 7785935) B7785935
theorem B3460415 : Blo 2159435 3460415 := bstep (se 1 (by rfl) ⟨2595311, by rfl⟩ : syracuseStep 3460415 = 5190623) B5190623
theorem B9227773 : Blo 2159435 9227773 := bstep (se 3 (by rfl) ⟨1730207, by rfl⟩ : syracuseStep 9227773 = 3460415) B3460415
theorem B12303697 : Blo 2159435 12303697 := bstep (se 2 (by rfl) ⟨4613886, by rfl⟩ : syracuseStep 12303697 = 9227773) B9227773
theorem B16404929 : Blo 2159435 16404929 := bstep (se 2 (by rfl) ⟨6151848, by rfl⟩ : syracuseStep 16404929 = 12303697) B12303697
theorem B10936619 : Blo 2159435 10936619 := bstep (se 1 (by rfl) ⟨8202464, by rfl⟩ : syracuseStep 10936619 = 16404929) B16404929
theorem B7291079 : Blo 2159435 7291079 := bstep (se 1 (by rfl) ⟨5468309, by rfl⟩ : syracuseStep 7291079 = 10936619) B10936619
theorem B4860719 : Blo 2159435 4860719 := bstep (se 1 (by rfl) ⟨3645539, by rfl⟩ : syracuseStep 4860719 = 7291079) B7291079
theorem B3240479 : Blo 2159435 3240479 := bstep (se 1 (by rfl) ⟨2430359, by rfl⟩ : syracuseStep 3240479 = 4860719) B4860719
theorem B2160319 : Blo 2159435 2160319 := bstep (se 1 (by rfl) ⟨1620239, by rfl⟩ : syracuseStep 2160319 = 3240479) B3240479
theorem B3240485 : Blo 2159435 3240485 := bbase (se 4 (by rfl) ⟨303795, by rfl⟩ : syracuseStep 3240485 = 607591) (by norm_num)
theorem B2160323 : Blo 2159435 2160323 := bstep (se 1 (by rfl) ⟨1620242, by rfl⟩ : syracuseStep 2160323 = 3240485) B3240485
theorem B2734165 : Blo 2159435 2734165 := bbase (se 8 (by rfl) ⟨16020, by rfl⟩ : syracuseStep 2734165 = 32041) (by norm_num)
theorem B3645553 : Blo 2159435 3645553 := bstep (se 2 (by rfl) ⟨1367082, by rfl⟩ : syracuseStep 3645553 = 2734165) B2734165
theorem B4860737 : Blo 2159435 4860737 := bstep (se 2 (by rfl) ⟨1822776, by rfl⟩ : syracuseStep 4860737 = 3645553) B3645553
theorem B3240491 : Blo 2159435 3240491 := bstep (se 1 (by rfl) ⟨2430368, by rfl⟩ : syracuseStep 3240491 = 4860737) B4860737
theorem B2160327 : Blo 2159435 2160327 := bstep (se 1 (by rfl) ⟨1620245, by rfl⟩ : syracuseStep 2160327 = 3240491) B3240491
theorem B2430373 : Blo 2159435 2430373 := bbase (se 4 (by rfl) ⟨227847, by rfl⟩ : syracuseStep 2430373 = 455695) (by norm_num)
theorem B3240497 : Blo 2159435 3240497 := bstep (se 2 (by rfl) ⟨1215186, by rfl⟩ : syracuseStep 3240497 = 2430373) B2430373
theorem B2160331 : Blo 2159435 2160331 := bstep (se 1 (by rfl) ⟨1620248, by rfl⟩ : syracuseStep 2160331 = 3240497) B3240497
theorem B3892997 : Blo 2159435 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B2595331 : Blo 2159435 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B13841765 : Blo 2159435 13841765 := bstep (se 4 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 13841765 = 2595331) B2595331
theorem B9227843 : Blo 2159435 9227843 := bstep (se 1 (by rfl) ⟨6920882, by rfl⟩ : syracuseStep 9227843 = 13841765) B13841765
theorem B6151895 : Blo 2159435 6151895 := bstep (se 1 (by rfl) ⟨4613921, by rfl⟩ : syracuseStep 6151895 = 9227843) B9227843
theorem B4101263 : Blo 2159435 4101263 := bstep (se 1 (by rfl) ⟨3075947, by rfl⟩ : syracuseStep 4101263 = 6151895) B6151895
theorem B2734175 : Blo 2159435 2734175 := bstep (se 1 (by rfl) ⟨2050631, by rfl⟩ : syracuseStep 2734175 = 4101263) B4101263
theorem B7291133 : Blo 2159435 7291133 := bstep (se 3 (by rfl) ⟨1367087, by rfl⟩ : syracuseStep 7291133 = 2734175) B2734175
theorem B4860755 : Blo 2159435 4860755 := bstep (se 1 (by rfl) ⟨3645566, by rfl⟩ : syracuseStep 4860755 = 7291133) B7291133
theorem B3240503 : Blo 2159435 3240503 := bstep (se 1 (by rfl) ⟨2430377, by rfl⟩ : syracuseStep 3240503 = 4860755) B4860755
theorem B2160335 : Blo 2159435 2160335 := bstep (se 1 (by rfl) ⟨1620251, by rfl⟩ : syracuseStep 2160335 = 3240503) B3240503
theorem B3240509 : Blo 2159435 3240509 := bbase (se 3 (by rfl) ⟨607595, by rfl⟩ : syracuseStep 3240509 = 1215191) (by norm_num)
theorem B2160339 : Blo 2159435 2160339 := bstep (se 1 (by rfl) ⟨1620254, by rfl⟩ : syracuseStep 2160339 = 3240509) B3240509
theorem B4860773 : Blo 2159435 4860773 := bbase (se 4 (by rfl) ⟨455697, by rfl⟩ : syracuseStep 4860773 = 911395) (by norm_num)
theorem B3240515 : Blo 2159435 3240515 := bstep (se 1 (by rfl) ⟨2430386, by rfl⟩ : syracuseStep 3240515 = 4860773) B4860773
theorem B2160343 : Blo 2159435 2160343 := bstep (se 1 (by rfl) ⟨1620257, by rfl⟩ : syracuseStep 2160343 = 3240515) B3240515
theorem B5468381 : Blo 2159435 5468381 := bbase (se 3 (by rfl) ⟨1025321, by rfl⟩ : syracuseStep 5468381 = 2050643) (by norm_num)
theorem B3645587 : Blo 2159435 3645587 := bstep (se 1 (by rfl) ⟨2734190, by rfl⟩ : syracuseStep 3645587 = 5468381) B5468381
theorem B2430391 : Blo 2159435 2430391 := bstep (se 1 (by rfl) ⟨1822793, by rfl⟩ : syracuseStep 2430391 = 3645587) B3645587
theorem B3240521 : Blo 2159435 3240521 := bstep (se 2 (by rfl) ⟨1215195, by rfl⟩ : syracuseStep 3240521 = 2430391) B2430391
theorem B2160347 : Blo 2159435 2160347 := bstep (se 1 (by rfl) ⟨1620260, by rfl⟩ : syracuseStep 2160347 = 3240521) B3240521
theorem B4101293 : Blo 2159435 4101293 := bbase (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) (by norm_num)
theorem B10936781 : Blo 2159435 10936781 := bstep (se 3 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 10936781 = 4101293) B4101293
theorem B7291187 : Blo 2159435 7291187 := bstep (se 1 (by rfl) ⟨5468390, by rfl⟩ : syracuseStep 7291187 = 10936781) B10936781
theorem B4860791 : Blo 2159435 4860791 := bstep (se 1 (by rfl) ⟨3645593, by rfl⟩ : syracuseStep 4860791 = 7291187) B7291187
theorem B3240527 : Blo 2159435 3240527 := bstep (se 1 (by rfl) ⟨2430395, by rfl⟩ : syracuseStep 3240527 = 4860791) B4860791
theorem B2160351 : Blo 2159435 2160351 := bstep (se 1 (by rfl) ⟨1620263, by rfl⟩ : syracuseStep 2160351 = 3240527) B3240527
theorem B3240533 : Blo 2159435 3240533 := bbase (se 8 (by rfl) ⟨18987, by rfl⟩ : syracuseStep 3240533 = 37975) (by norm_num)
theorem B2160355 : Blo 2159435 2160355 := bstep (se 1 (by rfl) ⟨1620266, by rfl⟩ : syracuseStep 2160355 = 3240533) B3240533
theorem B10523077 : Blo 2159435 10523077 := bbase (se 4 (by rfl) ⟨986538, by rfl⟩ : syracuseStep 10523077 = 1973077) (by norm_num)
theorem B56123077 : Blo 2159435 56123077 := bstep (se 4 (by rfl) ⟨5261538, by rfl⟩ : syracuseStep 56123077 = 10523077) B10523077
theorem B74830769 : Blo 2159435 74830769 := bstep (se 2 (by rfl) ⟨28061538, by rfl⟩ : syracuseStep 74830769 = 56123077) B56123077
theorem B49887179 : Blo 2159435 49887179 := bstep (se 1 (by rfl) ⟨37415384, by rfl⟩ : syracuseStep 49887179 = 74830769) B74830769
theorem B33258119 : Blo 2159435 33258119 := bstep (se 1 (by rfl) ⟨24943589, by rfl⟩ : syracuseStep 33258119 = 49887179) B49887179
theorem B88688317 : Blo 2159435 88688317 := bstep (se 3 (by rfl) ⟨16629059, by rfl⟩ : syracuseStep 88688317 = 33258119) B33258119
theorem B118251089 : Blo 2159435 118251089 := bstep (se 2 (by rfl) ⟨44344158, by rfl⟩ : syracuseStep 118251089 = 88688317) B88688317
theorem B78834059 : Blo 2159435 78834059 := bstep (se 1 (by rfl) ⟨59125544, by rfl⟩ : syracuseStep 78834059 = 118251089) B118251089
theorem B52556039 : Blo 2159435 52556039 := bstep (se 1 (by rfl) ⟨39417029, by rfl⟩ : syracuseStep 52556039 = 78834059) B78834059
theorem B35037359 : Blo 2159435 35037359 := bstep (se 1 (by rfl) ⟨26278019, by rfl⟩ : syracuseStep 35037359 = 52556039) B52556039
theorem B23358239 : Blo 2159435 23358239 := bstep (se 1 (by rfl) ⟨17518679, by rfl⟩ : syracuseStep 23358239 = 35037359) B35037359
theorem B15572159 : Blo 2159435 15572159 := bstep (se 1 (by rfl) ⟨11679119, by rfl⟩ : syracuseStep 15572159 = 23358239) B23358239
theorem B10381439 : Blo 2159435 10381439 := bstep (se 1 (by rfl) ⟨7786079, by rfl⟩ : syracuseStep 10381439 = 15572159) B15572159
theorem B6920959 : Blo 2159435 6920959 := bstep (se 1 (by rfl) ⟨5190719, by rfl⟩ : syracuseStep 6920959 = 10381439) B10381439
theorem B9227945 : Blo 2159435 9227945 := bstep (se 2 (by rfl) ⟨3460479, by rfl⟩ : syracuseStep 9227945 = 6920959) B6920959
theorem B6151963 : Blo 2159435 6151963 := bstep (se 1 (by rfl) ⟨4613972, by rfl⟩ : syracuseStep 6151963 = 9227945) B9227945
theorem B8202617 : Blo 2159435 8202617 := bstep (se 2 (by rfl) ⟨3075981, by rfl⟩ : syracuseStep 8202617 = 6151963) B6151963
theorem B5468411 : Blo 2159435 5468411 := bstep (se 1 (by rfl) ⟨4101308, by rfl⟩ : syracuseStep 5468411 = 8202617) B8202617
theorem B3645607 : Blo 2159435 3645607 := bstep (se 1 (by rfl) ⟨2734205, by rfl⟩ : syracuseStep 3645607 = 5468411) B5468411
theorem B4860809 : Blo 2159435 4860809 := bstep (se 2 (by rfl) ⟨1822803, by rfl⟩ : syracuseStep 4860809 = 3645607) B3645607
theorem B3240539 : Blo 2159435 3240539 := bstep (se 1 (by rfl) ⟨2430404, by rfl⟩ : syracuseStep 3240539 = 4860809) B4860809
theorem B2160359 : Blo 2159435 2160359 := bstep (se 1 (by rfl) ⟨1620269, by rfl⟩ : syracuseStep 2160359 = 3240539) B3240539
theorem B2430409 : Blo 2159435 2430409 := bbase (se 2 (by rfl) ⟨911403, by rfl⟩ : syracuseStep 2430409 = 1822807) (by norm_num)
theorem B3240545 : Blo 2159435 3240545 := bstep (se 2 (by rfl) ⟨1215204, by rfl⟩ : syracuseStep 3240545 = 2430409) B2430409
theorem B2160363 : Blo 2159435 2160363 := bstep (se 1 (by rfl) ⟨1620272, by rfl⟩ : syracuseStep 2160363 = 3240545) B3240545
theorem B18455957 : Blo 2159435 18455957 := bbase (se 6 (by rfl) ⟨432561, by rfl⟩ : syracuseStep 18455957 = 865123) (by norm_num)
theorem B12303971 : Blo 2159435 12303971 := bstep (se 1 (by rfl) ⟨9227978, by rfl⟩ : syracuseStep 12303971 = 18455957) B18455957
theorem B8202647 : Blo 2159435 8202647 := bstep (se 1 (by rfl) ⟨6151985, by rfl⟩ : syracuseStep 8202647 = 12303971) B12303971
theorem B5468431 : Blo 2159435 5468431 := bstep (se 1 (by rfl) ⟨4101323, by rfl⟩ : syracuseStep 5468431 = 8202647) B8202647
theorem B7291241 : Blo 2159435 7291241 := bstep (se 2 (by rfl) ⟨2734215, by rfl⟩ : syracuseStep 7291241 = 5468431) B5468431
theorem B4860827 : Blo 2159435 4860827 := bstep (se 1 (by rfl) ⟨3645620, by rfl⟩ : syracuseStep 4860827 = 7291241) B7291241
theorem B3240551 : Blo 2159435 3240551 := bstep (se 1 (by rfl) ⟨2430413, by rfl⟩ : syracuseStep 3240551 = 4860827) B4860827
theorem B2160367 : Blo 2159435 2160367 := bstep (se 1 (by rfl) ⟨1620275, by rfl⟩ : syracuseStep 2160367 = 3240551) B3240551
theorem B3240557 : Blo 2159435 3240557 := bbase (se 3 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 3240557 = 1215209) (by norm_num)
theorem B2160371 : Blo 2159435 2160371 := bstep (se 1 (by rfl) ⟨1620278, by rfl⟩ : syracuseStep 2160371 = 3240557) B3240557
theorem B4860845 : Blo 2159435 4860845 := bbase (se 3 (by rfl) ⟨911408, by rfl⟩ : syracuseStep 4860845 = 1822817) (by norm_num)
theorem B3240563 : Blo 2159435 3240563 := bstep (se 1 (by rfl) ⟨2430422, by rfl⟩ : syracuseStep 3240563 = 4860845) B4860845
theorem B2160375 : Blo 2159435 2160375 := bstep (se 1 (by rfl) ⟨1620281, by rfl⟩ : syracuseStep 2160375 = 3240563) B3240563
theorem B6152021 : Blo 2159435 6152021 := bbase (se 9 (by rfl) ⟨18023, by rfl⟩ : syracuseStep 6152021 = 36047) (by norm_num)
theorem B4101347 : Blo 2159435 4101347 := bstep (se 1 (by rfl) ⟨3076010, by rfl⟩ : syracuseStep 4101347 = 6152021) B6152021
theorem B2734231 : Blo 2159435 2734231 := bstep (se 1 (by rfl) ⟨2050673, by rfl⟩ : syracuseStep 2734231 = 4101347) B4101347
theorem B3645641 : Blo 2159435 3645641 := bstep (se 2 (by rfl) ⟨1367115, by rfl⟩ : syracuseStep 3645641 = 2734231) B2734231
theorem B2430427 : Blo 2159435 2430427 := bstep (se 1 (by rfl) ⟨1822820, by rfl⟩ : syracuseStep 2430427 = 3645641) B3645641
theorem B3240569 : Blo 2159435 3240569 := bstep (se 2 (by rfl) ⟨1215213, by rfl⟩ : syracuseStep 3240569 = 2430427) B2430427
theorem B2160379 : Blo 2159435 2160379 := bstep (se 1 (by rfl) ⟨1620284, by rfl⟩ : syracuseStep 2160379 = 3240569) B3240569
theorem B3329605 : Blo 2159435 3329605 := bbase (se 4 (by rfl) ⟨312150, by rfl⟩ : syracuseStep 3329605 = 624301) (by norm_num)
theorem B17757893 : Blo 2159435 17757893 := bstep (se 4 (by rfl) ⟨1664802, by rfl⟩ : syracuseStep 17757893 = 3329605) B3329605
theorem B47354381 : Blo 2159435 47354381 := bstep (se 3 (by rfl) ⟨8878946, by rfl⟩ : syracuseStep 47354381 = 17757893) B17757893
theorem B31569587 : Blo 2159435 31569587 := bstep (se 1 (by rfl) ⟨23677190, by rfl⟩ : syracuseStep 31569587 = 47354381) B47354381
theorem B21046391 : Blo 2159435 21046391 := bstep (se 1 (by rfl) ⟨15784793, by rfl⟩ : syracuseStep 21046391 = 31569587) B31569587
theorem B14030927 : Blo 2159435 14030927 := bstep (se 1 (by rfl) ⟨10523195, by rfl⟩ : syracuseStep 14030927 = 21046391) B21046391
theorem B9353951 : Blo 2159435 9353951 := bstep (se 1 (by rfl) ⟨7015463, by rfl⟩ : syracuseStep 9353951 = 14030927) B14030927
theorem B6235967 : Blo 2159435 6235967 := bstep (se 1 (by rfl) ⟨4676975, by rfl⟩ : syracuseStep 6235967 = 9353951) B9353951
theorem B4157311 : Blo 2159435 4157311 := bstep (se 1 (by rfl) ⟨3117983, by rfl⟩ : syracuseStep 4157311 = 6235967) B6235967
theorem B5543081 : Blo 2159435 5543081 := bstep (se 2 (by rfl) ⟨2078655, by rfl⟩ : syracuseStep 5543081 = 4157311) B4157311
theorem B3695387 : Blo 2159435 3695387 := bstep (se 1 (by rfl) ⟨2771540, by rfl⟩ : syracuseStep 3695387 = 5543081) B5543081
theorem B9854365 : Blo 2159435 9854365 := bstep (se 3 (by rfl) ⟨1847693, by rfl⟩ : syracuseStep 9854365 = 3695387) B3695387
theorem B13139153 : Blo 2159435 13139153 := bstep (se 2 (by rfl) ⟨4927182, by rfl⟩ : syracuseStep 13139153 = 9854365) B9854365
theorem B8759435 : Blo 2159435 8759435 := bstep (se 1 (by rfl) ⟨6569576, by rfl⟩ : syracuseStep 8759435 = 13139153) B13139153
theorem B23358493 : Blo 2159435 23358493 := bstep (se 3 (by rfl) ⟨4379717, by rfl⟩ : syracuseStep 23358493 = 8759435) B8759435
theorem B31144657 : Blo 2159435 31144657 := bstep (se 2 (by rfl) ⟨11679246, by rfl⟩ : syracuseStep 31144657 = 23358493) B23358493
theorem B41526209 : Blo 2159435 41526209 := bstep (se 2 (by rfl) ⟨15572328, by rfl⟩ : syracuseStep 41526209 = 31144657) B31144657
theorem B27684139 : Blo 2159435 27684139 := bstep (se 1 (by rfl) ⟨20763104, by rfl⟩ : syracuseStep 27684139 = 41526209) B41526209
theorem B36912185 : Blo 2159435 36912185 := bstep (se 2 (by rfl) ⟨13842069, by rfl⟩ : syracuseStep 36912185 = 27684139) B27684139
theorem B24608123 : Blo 2159435 24608123 := bstep (se 1 (by rfl) ⟨18456092, by rfl⟩ : syracuseStep 24608123 = 36912185) B36912185
theorem B16405415 : Blo 2159435 16405415 := bstep (se 1 (by rfl) ⟨12304061, by rfl⟩ : syracuseStep 16405415 = 24608123) B24608123
theorem B10936943 : Blo 2159435 10936943 := bstep (se 1 (by rfl) ⟨8202707, by rfl⟩ : syracuseStep 10936943 = 16405415) B16405415
theorem B7291295 : Blo 2159435 7291295 := bstep (se 1 (by rfl) ⟨5468471, by rfl⟩ : syracuseStep 7291295 = 10936943) B10936943
theorem B4860863 : Blo 2159435 4860863 := bstep (se 1 (by rfl) ⟨3645647, by rfl⟩ : syracuseStep 4860863 = 7291295) B7291295
theorem B3240575 : Blo 2159435 3240575 := bstep (se 1 (by rfl) ⟨2430431, by rfl⟩ : syracuseStep 3240575 = 4860863) B4860863
theorem B2160383 : Blo 2159435 2160383 := bstep (se 1 (by rfl) ⟨1620287, by rfl⟩ : syracuseStep 2160383 = 3240575) B3240575
theorem B3240581 : Blo 2159435 3240581 := bbase (se 4 (by rfl) ⟨303804, by rfl⟩ : syracuseStep 3240581 = 607609) (by norm_num)
theorem B2160387 : Blo 2159435 2160387 := bstep (se 1 (by rfl) ⟨1620290, by rfl⟩ : syracuseStep 2160387 = 3240581) B3240581
theorem B3645661 : Blo 2159435 3645661 := bbase (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) (by norm_num)
theorem B4860881 : Blo 2159435 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B3240587 : Blo 2159435 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B2160391 : Blo 2159435 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B2430445 : Blo 2159435 2430445 := bbase (se 3 (by rfl) ⟨455708, by rfl⟩ : syracuseStep 2430445 = 911417) (by norm_num)
theorem B3240593 : Blo 2159435 3240593 := bstep (se 2 (by rfl) ⟨1215222, by rfl⟩ : syracuseStep 3240593 = 2430445) B2430445
theorem B2160395 : Blo 2159435 2160395 := bstep (se 1 (by rfl) ⟨1620296, by rfl⟩ : syracuseStep 2160395 = 3240593) B3240593
theorem B7291349 : Blo 2159435 7291349 := bbase (se 7 (by rfl) ⟨85445, by rfl⟩ : syracuseStep 7291349 = 170891) (by norm_num)
theorem B4860899 : Blo 2159435 4860899 := bstep (se 1 (by rfl) ⟨3645674, by rfl⟩ : syracuseStep 4860899 = 7291349) B7291349
theorem B3240599 : Blo 2159435 3240599 := bstep (se 1 (by rfl) ⟨2430449, by rfl⟩ : syracuseStep 3240599 = 4860899) B4860899
theorem B2160399 : Blo 2159435 2160399 := bstep (se 1 (by rfl) ⟨1620299, by rfl⟩ : syracuseStep 2160399 = 3240599) B3240599
theorem B3240605 : Blo 2159435 3240605 := bbase (se 3 (by rfl) ⟨607613, by rfl⟩ : syracuseStep 3240605 = 1215227) (by norm_num)
theorem B2160403 : Blo 2159435 2160403 := bstep (se 1 (by rfl) ⟨1620302, by rfl⟩ : syracuseStep 2160403 = 3240605) B3240605
theorem B4860917 : Blo 2159435 4860917 := bbase (se 5 (by rfl) ⟨227855, by rfl⟩ : syracuseStep 4860917 = 455711) (by norm_num)
theorem B3240611 : Blo 2159435 3240611 := bstep (se 1 (by rfl) ⟨2430458, by rfl⟩ : syracuseStep 3240611 = 4860917) B4860917
theorem B2160407 : Blo 2159435 2160407 := bstep (se 1 (by rfl) ⟨1620305, by rfl⟩ : syracuseStep 2160407 = 3240611) B3240611
theorem B62290133 : Blo 2159435 62290133 := bbase (se 7 (by rfl) ⟨729962, by rfl⟩ : syracuseStep 62290133 = 1459925) (by norm_num)
theorem B41526755 : Blo 2159435 41526755 := bstep (se 1 (by rfl) ⟨31145066, by rfl⟩ : syracuseStep 41526755 = 62290133) B62290133
theorem B27684503 : Blo 2159435 27684503 := bstep (se 1 (by rfl) ⟨20763377, by rfl⟩ : syracuseStep 27684503 = 41526755) B41526755
theorem B18456335 : Blo 2159435 18456335 := bstep (se 1 (by rfl) ⟨13842251, by rfl⟩ : syracuseStep 18456335 = 27684503) B27684503
theorem B12304223 : Blo 2159435 12304223 := bstep (se 1 (by rfl) ⟨9228167, by rfl⟩ : syracuseStep 12304223 = 18456335) B18456335
theorem B8202815 : Blo 2159435 8202815 := bstep (se 1 (by rfl) ⟨6152111, by rfl⟩ : syracuseStep 8202815 = 12304223) B12304223
theorem B5468543 : Blo 2159435 5468543 := bstep (se 1 (by rfl) ⟨4101407, by rfl⟩ : syracuseStep 5468543 = 8202815) B8202815
theorem B3645695 : Blo 2159435 3645695 := bstep (se 1 (by rfl) ⟨2734271, by rfl⟩ : syracuseStep 3645695 = 5468543) B5468543
theorem B2430463 : Blo 2159435 2430463 := bstep (se 1 (by rfl) ⟨1822847, by rfl⟩ : syracuseStep 2430463 = 3645695) B3645695
theorem B3240617 : Blo 2159435 3240617 := bstep (se 2 (by rfl) ⟨1215231, by rfl⟩ : syracuseStep 3240617 = 2430463) B2430463
theorem B2160411 : Blo 2159435 2160411 := bstep (se 1 (by rfl) ⟨1620308, by rfl⟩ : syracuseStep 2160411 = 3240617) B3240617
theorem B3076061 : Blo 2159435 3076061 := bbase (se 3 (by rfl) ⟨576761, by rfl⟩ : syracuseStep 3076061 = 1153523) (by norm_num)
theorem B8202829 : Blo 2159435 8202829 := bstep (se 3 (by rfl) ⟨1538030, by rfl⟩ : syracuseStep 8202829 = 3076061) B3076061
theorem B10937105 : Blo 2159435 10937105 := bstep (se 2 (by rfl) ⟨4101414, by rfl⟩ : syracuseStep 10937105 = 8202829) B8202829
theorem B7291403 : Blo 2159435 7291403 := bstep (se 1 (by rfl) ⟨5468552, by rfl⟩ : syracuseStep 7291403 = 10937105) B10937105
theorem B4860935 : Blo 2159435 4860935 := bstep (se 1 (by rfl) ⟨3645701, by rfl⟩ : syracuseStep 4860935 = 7291403) B7291403
theorem B3240623 : Blo 2159435 3240623 := bstep (se 1 (by rfl) ⟨2430467, by rfl⟩ : syracuseStep 3240623 = 4860935) B4860935
theorem B2160415 : Blo 2159435 2160415 := bstep (se 1 (by rfl) ⟨1620311, by rfl⟩ : syracuseStep 2160415 = 3240623) B3240623
theorem B3240629 : Blo 2159435 3240629 := bbase (se 5 (by rfl) ⟨151904, by rfl⟩ : syracuseStep 3240629 = 303809) (by norm_num)
theorem B2160419 : Blo 2159435 2160419 := bstep (se 1 (by rfl) ⟨1620314, by rfl⟩ : syracuseStep 2160419 = 3240629) B3240629
theorem B5468573 : Blo 2159435 5468573 := bbase (se 3 (by rfl) ⟨1025357, by rfl⟩ : syracuseStep 5468573 = 2050715) (by norm_num)
theorem B3645715 : Blo 2159435 3645715 := bstep (se 1 (by rfl) ⟨2734286, by rfl⟩ : syracuseStep 3645715 = 5468573) B5468573
theorem B4860953 : Blo 2159435 4860953 := bstep (se 2 (by rfl) ⟨1822857, by rfl⟩ : syracuseStep 4860953 = 3645715) B3645715
theorem B3240635 : Blo 2159435 3240635 := bstep (se 1 (by rfl) ⟨2430476, by rfl⟩ : syracuseStep 3240635 = 4860953) B4860953
theorem B2160423 : Blo 2159435 2160423 := bstep (se 1 (by rfl) ⟨1620317, by rfl⟩ : syracuseStep 2160423 = 3240635) B3240635
theorem B2430481 : Blo 2159435 2430481 := bbase (se 2 (by rfl) ⟨911430, by rfl⟩ : syracuseStep 2430481 = 1822861) (by norm_num)
theorem B3240641 : Blo 2159435 3240641 := bstep (se 2 (by rfl) ⟨1215240, by rfl⟩ : syracuseStep 3240641 = 2430481) B2430481
theorem B2160427 : Blo 2159435 2160427 := bstep (se 1 (by rfl) ⟨1620320, by rfl⟩ : syracuseStep 2160427 = 3240641) B3240641
theorem B4101445 : Blo 2159435 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B5468593 : Blo 2159435 5468593 := bstep (se 2 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 5468593 = 4101445) B4101445
theorem B7291457 : Blo 2159435 7291457 := bstep (se 2 (by rfl) ⟨2734296, by rfl⟩ : syracuseStep 7291457 = 5468593) B5468593
theorem B4860971 : Blo 2159435 4860971 := bstep (se 1 (by rfl) ⟨3645728, by rfl⟩ : syracuseStep 4860971 = 7291457) B7291457
theorem B3240647 : Blo 2159435 3240647 := bstep (se 1 (by rfl) ⟨2430485, by rfl⟩ : syracuseStep 3240647 = 4860971) B4860971
theorem B2160431 : Blo 2159435 2160431 := bstep (se 1 (by rfl) ⟨1620323, by rfl⟩ : syracuseStep 2160431 = 3240647) B3240647
theorem B3240653 : Blo 2159435 3240653 := bbase (se 3 (by rfl) ⟨607622, by rfl⟩ : syracuseStep 3240653 = 1215245) (by norm_num)
theorem B2160435 : Blo 2159435 2160435 := bstep (se 1 (by rfl) ⟨1620326, by rfl⟩ : syracuseStep 2160435 = 3240653) B3240653
theorem B4860989 : Blo 2159435 4860989 := bbase (se 3 (by rfl) ⟨911435, by rfl⟩ : syracuseStep 4860989 = 1822871) (by norm_num)
theorem B3240659 : Blo 2159435 3240659 := bstep (se 1 (by rfl) ⟨2430494, by rfl⟩ : syracuseStep 3240659 = 4860989) B4860989
theorem B2160439 : Blo 2159435 2160439 := bstep (se 1 (by rfl) ⟨1620329, by rfl⟩ : syracuseStep 2160439 = 3240659) B3240659
theorem B3645749 : Blo 2159435 3645749 := bbase (se 5 (by rfl) ⟨170894, by rfl⟩ : syracuseStep 3645749 = 341789) (by norm_num)
theorem B2430499 : Blo 2159435 2430499 := bstep (se 1 (by rfl) ⟨1822874, by rfl⟩ : syracuseStep 2430499 = 3645749) B3645749
theorem B3240665 : Blo 2159435 3240665 := bstep (se 2 (by rfl) ⟨1215249, by rfl⟩ : syracuseStep 3240665 = 2430499) B2430499
theorem B2160443 : Blo 2159435 2160443 := bstep (se 1 (by rfl) ⟨1620332, by rfl⟩ : syracuseStep 2160443 = 3240665) B3240665
theorem B6152213 : Blo 2159435 6152213 := bbase (se 6 (by rfl) ⟨144192, by rfl⟩ : syracuseStep 6152213 = 288385) (by norm_num)
theorem B16405901 : Blo 2159435 16405901 := bstep (se 3 (by rfl) ⟨3076106, by rfl⟩ : syracuseStep 16405901 = 6152213) B6152213
theorem B10937267 : Blo 2159435 10937267 := bstep (se 1 (by rfl) ⟨8202950, by rfl⟩ : syracuseStep 10937267 = 16405901) B16405901
theorem B7291511 : Blo 2159435 7291511 := bstep (se 1 (by rfl) ⟨5468633, by rfl⟩ : syracuseStep 7291511 = 10937267) B10937267
theorem B4861007 : Blo 2159435 4861007 := bstep (se 1 (by rfl) ⟨3645755, by rfl⟩ : syracuseStep 4861007 = 7291511) B7291511
theorem B3240671 : Blo 2159435 3240671 := bstep (se 1 (by rfl) ⟨2430503, by rfl⟩ : syracuseStep 3240671 = 4861007) B4861007
theorem B2160447 : Blo 2159435 2160447 := bstep (se 1 (by rfl) ⟨1620335, by rfl⟩ : syracuseStep 2160447 = 3240671) B3240671
theorem B3240677 : Blo 2159435 3240677 := bbase (se 4 (by rfl) ⟨303813, by rfl⟩ : syracuseStep 3240677 = 607627) (by norm_num)
theorem B2160451 : Blo 2159435 2160451 := bstep (se 1 (by rfl) ⟨1620338, by rfl⟩ : syracuseStep 2160451 = 3240677) B3240677
theorem B2307089 : Blo 2159435 2307089 := bbase (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) (by norm_num)
theorem B6152237 : Blo 2159435 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B4101491 : Blo 2159435 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B2734327 : Blo 2159435 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B3645769 : Blo 2159435 3645769 := bstep (se 2 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 3645769 = 2734327) B2734327
theorem B4861025 : Blo 2159435 4861025 := bstep (se 2 (by rfl) ⟨1822884, by rfl⟩ : syracuseStep 4861025 = 3645769) B3645769
theorem B3240683 : Blo 2159435 3240683 := bstep (se 1 (by rfl) ⟨2430512, by rfl⟩ : syracuseStep 3240683 = 4861025) B4861025
theorem B2160455 : Blo 2159435 2160455 := bstep (se 1 (by rfl) ⟨1620341, by rfl⟩ : syracuseStep 2160455 = 3240683) B3240683
theorem B2430517 : Blo 2159435 2430517 := bbase (se 5 (by rfl) ⟨113930, by rfl⟩ : syracuseStep 2430517 = 227861) (by norm_num)
theorem B3240689 : Blo 2159435 3240689 := bstep (se 2 (by rfl) ⟨1215258, by rfl⟩ : syracuseStep 3240689 = 2430517) B2430517
theorem B2160459 : Blo 2159435 2160459 := bstep (se 1 (by rfl) ⟨1620344, by rfl⟩ : syracuseStep 2160459 = 3240689) B3240689
theorem B2734337 : Blo 2159435 2734337 := bbase (se 2 (by rfl) ⟨1025376, by rfl⟩ : syracuseStep 2734337 = 2050753) (by norm_num)
theorem B7291565 : Blo 2159435 7291565 := bstep (se 3 (by rfl) ⟨1367168, by rfl⟩ : syracuseStep 7291565 = 2734337) B2734337
theorem B4861043 : Blo 2159435 4861043 := bstep (se 1 (by rfl) ⟨3645782, by rfl⟩ : syracuseStep 4861043 = 7291565) B7291565
theorem B3240695 : Blo 2159435 3240695 := bstep (se 1 (by rfl) ⟨2430521, by rfl⟩ : syracuseStep 3240695 = 4861043) B4861043
theorem B2160463 : Blo 2159435 2160463 := bstep (se 1 (by rfl) ⟨1620347, by rfl⟩ : syracuseStep 2160463 = 3240695) B3240695
theorem B3240701 : Blo 2159435 3240701 := bbase (se 3 (by rfl) ⟨607631, by rfl⟩ : syracuseStep 3240701 = 1215263) (by norm_num)
theorem B2160467 : Blo 2159435 2160467 := bstep (se 1 (by rfl) ⟨1620350, by rfl⟩ : syracuseStep 2160467 = 3240701) B3240701
theorem B4861061 : Blo 2159435 4861061 := bbase (se 4 (by rfl) ⟨455724, by rfl⟩ : syracuseStep 4861061 = 911449) (by norm_num)
theorem B3240707 : Blo 2159435 3240707 := bstep (se 1 (by rfl) ⟨2430530, by rfl⟩ : syracuseStep 3240707 = 4861061) B4861061
theorem B2160471 : Blo 2159435 2160471 := bstep (se 1 (by rfl) ⟨1620353, by rfl⟩ : syracuseStep 2160471 = 3240707) B3240707
theorem B4614221 : Blo 2159435 4614221 := bbase (se 3 (by rfl) ⟨865166, by rfl⟩ : syracuseStep 4614221 = 1730333) (by norm_num)
theorem B3076147 : Blo 2159435 3076147 := bstep (se 1 (by rfl) ⟨2307110, by rfl⟩ : syracuseStep 3076147 = 4614221) B4614221
theorem B4101529 : Blo 2159435 4101529 := bstep (se 2 (by rfl) ⟨1538073, by rfl⟩ : syracuseStep 4101529 = 3076147) B3076147
theorem B5468705 : Blo 2159435 5468705 := bstep (se 2 (by rfl) ⟨2050764, by rfl⟩ : syracuseStep 5468705 = 4101529) B4101529
theorem B3645803 : Blo 2159435 3645803 := bstep (se 1 (by rfl) ⟨2734352, by rfl⟩ : syracuseStep 3645803 = 5468705) B5468705
theorem B2430535 : Blo 2159435 2430535 := bstep (se 1 (by rfl) ⟨1822901, by rfl⟩ : syracuseStep 2430535 = 3645803) B3645803
theorem B3240713 : Blo 2159435 3240713 := bstep (se 2 (by rfl) ⟨1215267, by rfl⟩ : syracuseStep 3240713 = 2430535) B2430535
theorem B2160475 : Blo 2159435 2160475 := bstep (se 1 (by rfl) ⟨1620356, by rfl⟩ : syracuseStep 2160475 = 3240713) B3240713
theorem B10937429 : Blo 2159435 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B7291619 : Blo 2159435 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4861079 : Blo 2159435 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B3240719 : Blo 2159435 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B2160479 : Blo 2159435 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B3240725 : Blo 2159435 3240725 := bbase (se 6 (by rfl) ⟨75954, by rfl⟩ : syracuseStep 3240725 = 151909) (by norm_num)
theorem B2160483 : Blo 2159435 2160483 := bstep (se 1 (by rfl) ⟨1620362, by rfl⟩ : syracuseStep 2160483 = 3240725) B3240725
theorem B41528213 : Blo 2159435 41528213 := bbase (se 6 (by rfl) ⟨973317, by rfl⟩ : syracuseStep 41528213 = 1946635) (by norm_num)
theorem B27685475 : Blo 2159435 27685475 := bstep (se 1 (by rfl) ⟨20764106, by rfl⟩ : syracuseStep 27685475 = 41528213) B41528213
theorem B18456983 : Blo 2159435 18456983 := bstep (se 1 (by rfl) ⟨13842737, by rfl⟩ : syracuseStep 18456983 = 27685475) B27685475
theorem B12304655 : Blo 2159435 12304655 := bstep (se 1 (by rfl) ⟨9228491, by rfl⟩ : syracuseStep 12304655 = 18456983) B18456983
theorem B8203103 : Blo 2159435 8203103 := bstep (se 1 (by rfl) ⟨6152327, by rfl⟩ : syracuseStep 8203103 = 12304655) B12304655
theorem B5468735 : Blo 2159435 5468735 := bstep (se 1 (by rfl) ⟨4101551, by rfl⟩ : syracuseStep 5468735 = 8203103) B8203103
theorem B3645823 : Blo 2159435 3645823 := bstep (se 1 (by rfl) ⟨2734367, by rfl⟩ : syracuseStep 3645823 = 5468735) B5468735
theorem B4861097 : Blo 2159435 4861097 := bstep (se 2 (by rfl) ⟨1822911, by rfl⟩ : syracuseStep 4861097 = 3645823) B3645823
theorem B3240731 : Blo 2159435 3240731 := bstep (se 1 (by rfl) ⟨2430548, by rfl⟩ : syracuseStep 3240731 = 4861097) B4861097
theorem B2160487 : Blo 2159435 2160487 := bstep (se 1 (by rfl) ⟨1620365, by rfl⟩ : syracuseStep 2160487 = 3240731) B3240731
theorem B2430553 : Blo 2159435 2430553 := bbase (se 2 (by rfl) ⟨911457, by rfl⟩ : syracuseStep 2430553 = 1822915) (by norm_num)
theorem B3240737 : Blo 2159435 3240737 := bstep (se 2 (by rfl) ⟨1215276, by rfl⟩ : syracuseStep 3240737 = 2430553) B2430553
theorem B2160491 : Blo 2159435 2160491 := bstep (se 1 (by rfl) ⟨1620368, by rfl⟩ : syracuseStep 2160491 = 3240737) B3240737
theorem B3893285 : Blo 2159435 3893285 := bbase (se 4 (by rfl) ⟨364995, by rfl⟩ : syracuseStep 3893285 = 729991) (by norm_num)
theorem B10382093 : Blo 2159435 10382093 := bstep (se 3 (by rfl) ⟨1946642, by rfl⟩ : syracuseStep 10382093 = 3893285) B3893285
theorem B6921395 : Blo 2159435 6921395 := bstep (se 1 (by rfl) ⟨5191046, by rfl⟩ : syracuseStep 6921395 = 10382093) B10382093
theorem B4614263 : Blo 2159435 4614263 := bstep (se 1 (by rfl) ⟨3460697, by rfl⟩ : syracuseStep 4614263 = 6921395) B6921395
theorem B3076175 : Blo 2159435 3076175 := bstep (se 1 (by rfl) ⟨2307131, by rfl⟩ : syracuseStep 3076175 = 4614263) B4614263
theorem B8203133 : Blo 2159435 8203133 := bstep (se 3 (by rfl) ⟨1538087, by rfl⟩ : syracuseStep 8203133 = 3076175) B3076175
theorem B5468755 : Blo 2159435 5468755 := bstep (se 1 (by rfl) ⟨4101566, by rfl⟩ : syracuseStep 5468755 = 8203133) B8203133
theorem B7291673 : Blo 2159435 7291673 := bstep (se 2 (by rfl) ⟨2734377, by rfl⟩ : syracuseStep 7291673 = 5468755) B5468755
theorem B4861115 : Blo 2159435 4861115 := bstep (se 1 (by rfl) ⟨3645836, by rfl⟩ : syracuseStep 4861115 = 7291673) B7291673
theorem B3240743 : Blo 2159435 3240743 := bstep (se 1 (by rfl) ⟨2430557, by rfl⟩ : syracuseStep 3240743 = 4861115) B4861115
theorem B2160495 : Blo 2159435 2160495 := bstep (se 1 (by rfl) ⟨1620371, by rfl⟩ : syracuseStep 2160495 = 3240743) B3240743
theorem B3240749 : Blo 2159435 3240749 := bbase (se 3 (by rfl) ⟨607640, by rfl⟩ : syracuseStep 3240749 = 1215281) (by norm_num)
theorem B2160499 : Blo 2159435 2160499 := bstep (se 1 (by rfl) ⟨1620374, by rfl⟩ : syracuseStep 2160499 = 3240749) B3240749
theorem B4861133 : Blo 2159435 4861133 := bbase (se 3 (by rfl) ⟨911462, by rfl⟩ : syracuseStep 4861133 = 1822925) (by norm_num)
theorem B3240755 : Blo 2159435 3240755 := bstep (se 1 (by rfl) ⟨2430566, by rfl⟩ : syracuseStep 3240755 = 4861133) B4861133
theorem B2160503 : Blo 2159435 2160503 := bstep (se 1 (by rfl) ⟨1620377, by rfl⟩ : syracuseStep 2160503 = 3240755) B3240755
theorem B2734393 : Blo 2159435 2734393 := bbase (se 2 (by rfl) ⟨1025397, by rfl⟩ : syracuseStep 2734393 = 2050795) (by norm_num)
theorem B3645857 : Blo 2159435 3645857 := bstep (se 2 (by rfl) ⟨1367196, by rfl⟩ : syracuseStep 3645857 = 2734393) B2734393
theorem B2430571 : Blo 2159435 2430571 := bstep (se 1 (by rfl) ⟨1822928, by rfl⟩ : syracuseStep 2430571 = 3645857) B3645857
theorem B3240761 : Blo 2159435 3240761 := bstep (se 2 (by rfl) ⟨1215285, by rfl⟩ : syracuseStep 3240761 = 2430571) B2430571
theorem B2160507 : Blo 2159435 2160507 := bstep (se 1 (by rfl) ⟨1620380, by rfl⟩ : syracuseStep 2160507 = 3240761) B3240761
theorem B6921445 : Blo 2159435 6921445 := bbase (se 4 (by rfl) ⟨648885, by rfl⟩ : syracuseStep 6921445 = 1297771) (by norm_num)
theorem B9228593 : Blo 2159435 9228593 := bstep (se 2 (by rfl) ⟨3460722, by rfl⟩ : syracuseStep 9228593 = 6921445) B6921445
theorem B24609581 : Blo 2159435 24609581 := bstep (se 3 (by rfl) ⟨4614296, by rfl⟩ : syracuseStep 24609581 = 9228593) B9228593
theorem B16406387 : Blo 2159435 16406387 := bstep (se 1 (by rfl) ⟨12304790, by rfl⟩ : syracuseStep 16406387 = 24609581) B24609581
theorem B10937591 : Blo 2159435 10937591 := bstep (se 1 (by rfl) ⟨8203193, by rfl⟩ : syracuseStep 10937591 = 16406387) B16406387
theorem B7291727 : Blo 2159435 7291727 := bstep (se 1 (by rfl) ⟨5468795, by rfl⟩ : syracuseStep 7291727 = 10937591) B10937591
theorem B4861151 : Blo 2159435 4861151 := bstep (se 1 (by rfl) ⟨3645863, by rfl⟩ : syracuseStep 4861151 = 7291727) B7291727
theorem B3240767 : Blo 2159435 3240767 := bstep (se 1 (by rfl) ⟨2430575, by rfl⟩ : syracuseStep 3240767 = 4861151) B4861151
theorem B2160511 : Blo 2159435 2160511 := bstep (se 1 (by rfl) ⟨1620383, by rfl⟩ : syracuseStep 2160511 = 3240767) B3240767
theorem B3240773 : Blo 2159435 3240773 := bbase (se 4 (by rfl) ⟨303822, by rfl⟩ : syracuseStep 3240773 = 607645) (by norm_num)
theorem B2160515 : Blo 2159435 2160515 := bstep (se 1 (by rfl) ⟨1620386, by rfl⟩ : syracuseStep 2160515 = 3240773) B3240773
theorem B3645877 : Blo 2159435 3645877 := bbase (se 5 (by rfl) ⟨170900, by rfl⟩ : syracuseStep 3645877 = 341801) (by norm_num)
theorem B4861169 : Blo 2159435 4861169 := bstep (se 2 (by rfl) ⟨1822938, by rfl⟩ : syracuseStep 4861169 = 3645877) B3645877
theorem B3240779 : Blo 2159435 3240779 := bstep (se 1 (by rfl) ⟨2430584, by rfl⟩ : syracuseStep 3240779 = 4861169) B4861169
theorem B2160519 : Blo 2159435 2160519 := bstep (se 1 (by rfl) ⟨1620389, by rfl⟩ : syracuseStep 2160519 = 3240779) B3240779
theorem B2430589 : Blo 2159435 2430589 := bbase (se 3 (by rfl) ⟨455735, by rfl⟩ : syracuseStep 2430589 = 911471) (by norm_num)
theorem B3240785 : Blo 2159435 3240785 := bstep (se 2 (by rfl) ⟨1215294, by rfl⟩ : syracuseStep 3240785 = 2430589) B2430589
theorem B2160523 : Blo 2159435 2160523 := bstep (se 1 (by rfl) ⟨1620392, by rfl⟩ : syracuseStep 2160523 = 3240785) B3240785
theorem B7291781 : Blo 2159435 7291781 := bbase (se 4 (by rfl) ⟨683604, by rfl⟩ : syracuseStep 7291781 = 1367209) (by norm_num)
theorem B4861187 : Blo 2159435 4861187 := bstep (se 1 (by rfl) ⟨3645890, by rfl⟩ : syracuseStep 4861187 = 7291781) B7291781
theorem B3240791 : Blo 2159435 3240791 := bstep (se 1 (by rfl) ⟨2430593, by rfl⟩ : syracuseStep 3240791 = 4861187) B4861187
theorem B2160527 : Blo 2159435 2160527 := bstep (se 1 (by rfl) ⟨1620395, by rfl⟩ : syracuseStep 2160527 = 3240791) B3240791
theorem B3240797 : Blo 2159435 3240797 := bbase (se 3 (by rfl) ⟨607649, by rfl⟩ : syracuseStep 3240797 = 1215299) (by norm_num)
theorem B2160531 : Blo 2159435 2160531 := bstep (se 1 (by rfl) ⟨1620398, by rfl⟩ : syracuseStep 2160531 = 3240797) B3240797
theorem B4861205 : Blo 2159435 4861205 := bbase (se 6 (by rfl) ⟨113934, by rfl⟩ : syracuseStep 4861205 = 227869) (by norm_num)
theorem B3240803 : Blo 2159435 3240803 := bstep (se 1 (by rfl) ⟨2430602, by rfl⟩ : syracuseStep 3240803 = 4861205) B4861205
theorem B2160535 : Blo 2159435 2160535 := bstep (se 1 (by rfl) ⟨1620401, by rfl⟩ : syracuseStep 2160535 = 3240803) B3240803
theorem B8203301 : Blo 2159435 8203301 := bbase (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) (by norm_num)
theorem B5468867 : Blo 2159435 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B3645911 : Blo 2159435 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B2430607 : Blo 2159435 2430607 := bstep (se 1 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 2430607 = 3645911) B3645911
theorem B3240809 : Blo 2159435 3240809 := bstep (se 2 (by rfl) ⟨1215303, by rfl⟩ : syracuseStep 3240809 = 2430607) B2430607
theorem B2160539 : Blo 2159435 2160539 := bstep (se 1 (by rfl) ⟨1620404, by rfl⟩ : syracuseStep 2160539 = 3240809) B3240809
theorem B4614365 : Blo 2159435 4614365 := bbase (se 3 (by rfl) ⟨865193, by rfl⟩ : syracuseStep 4614365 = 1730387) (by norm_num)
theorem B12304973 : Blo 2159435 12304973 := bstep (se 3 (by rfl) ⟨2307182, by rfl⟩ : syracuseStep 12304973 = 4614365) B4614365
theorem B8203315 : Blo 2159435 8203315 := bstep (se 1 (by rfl) ⟨6152486, by rfl⟩ : syracuseStep 8203315 = 12304973) B12304973
theorem B10937753 : Blo 2159435 10937753 := bstep (se 2 (by rfl) ⟨4101657, by rfl⟩ : syracuseStep 10937753 = 8203315) B8203315
theorem B7291835 : Blo 2159435 7291835 := bstep (se 1 (by rfl) ⟨5468876, by rfl⟩ : syracuseStep 7291835 = 10937753) B10937753
theorem B4861223 : Blo 2159435 4861223 := bstep (se 1 (by rfl) ⟨3645917, by rfl⟩ : syracuseStep 4861223 = 7291835) B7291835
theorem B3240815 : Blo 2159435 3240815 := bstep (se 1 (by rfl) ⟨2430611, by rfl⟩ : syracuseStep 3240815 = 4861223) B4861223
theorem B2160543 : Blo 2159435 2160543 := bstep (se 1 (by rfl) ⟨1620407, by rfl⟩ : syracuseStep 2160543 = 3240815) B3240815
theorem B3240821 : Blo 2159435 3240821 := bbase (se 5 (by rfl) ⟨151913, by rfl⟩ : syracuseStep 3240821 = 303827) (by norm_num)
theorem B2160547 : Blo 2159435 2160547 := bstep (se 1 (by rfl) ⟨1620410, by rfl⟩ : syracuseStep 2160547 = 3240821) B3240821
theorem B4994797 : Blo 2159435 4994797 := bbase (se 3 (by rfl) ⟨936524, by rfl⟩ : syracuseStep 4994797 = 1873049) (by norm_num)
theorem B6659729 : Blo 2159435 6659729 := bstep (se 2 (by rfl) ⟨2497398, by rfl⟩ : syracuseStep 6659729 = 4994797) B4994797
theorem B4439819 : Blo 2159435 4439819 := bstep (se 1 (by rfl) ⟨3329864, by rfl⟩ : syracuseStep 4439819 = 6659729) B6659729
theorem B11839517 : Blo 2159435 11839517 := bstep (se 3 (by rfl) ⟨2219909, by rfl⟩ : syracuseStep 11839517 = 4439819) B4439819
theorem B7893011 : Blo 2159435 7893011 := bstep (se 1 (by rfl) ⟨5919758, by rfl⟩ : syracuseStep 7893011 = 11839517) B11839517
theorem B21048029 : Blo 2159435 21048029 := bstep (se 3 (by rfl) ⟨3946505, by rfl⟩ : syracuseStep 21048029 = 7893011) B7893011
theorem B14032019 : Blo 2159435 14032019 := bstep (se 1 (by rfl) ⟨10524014, by rfl⟩ : syracuseStep 14032019 = 21048029) B21048029
theorem B9354679 : Blo 2159435 9354679 := bstep (se 1 (by rfl) ⟨7016009, by rfl⟩ : syracuseStep 9354679 = 14032019) B14032019
theorem B49891621 : Blo 2159435 49891621 := bstep (se 4 (by rfl) ⟨4677339, by rfl⟩ : syracuseStep 49891621 = 9354679) B9354679
theorem B66522161 : Blo 2159435 66522161 := bstep (se 2 (by rfl) ⟨24945810, by rfl⟩ : syracuseStep 66522161 = 49891621) B49891621
theorem B44348107 : Blo 2159435 44348107 := bstep (se 1 (by rfl) ⟨33261080, by rfl⟩ : syracuseStep 44348107 = 66522161) B66522161
theorem B59130809 : Blo 2159435 59130809 := bstep (se 2 (by rfl) ⟨22174053, by rfl⟩ : syracuseStep 59130809 = 44348107) B44348107
theorem B39420539 : Blo 2159435 39420539 := bstep (se 1 (by rfl) ⟨29565404, by rfl⟩ : syracuseStep 39420539 = 59130809) B59130809
theorem B26280359 : Blo 2159435 26280359 := bstep (se 1 (by rfl) ⟨19710269, by rfl⟩ : syracuseStep 26280359 = 39420539) B39420539
theorem B17520239 : Blo 2159435 17520239 := bstep (se 1 (by rfl) ⟨13140179, by rfl⟩ : syracuseStep 17520239 = 26280359) B26280359
theorem B11680159 : Blo 2159435 11680159 := bstep (se 1 (by rfl) ⟨8760119, by rfl⟩ : syracuseStep 11680159 = 17520239) B17520239
theorem B15573545 : Blo 2159435 15573545 := bstep (se 2 (by rfl) ⟨5840079, by rfl⟩ : syracuseStep 15573545 = 11680159) B11680159
theorem B10382363 : Blo 2159435 10382363 := bstep (se 1 (by rfl) ⟨7786772, by rfl⟩ : syracuseStep 10382363 = 15573545) B15573545
theorem B6921575 : Blo 2159435 6921575 := bstep (se 1 (by rfl) ⟨5191181, by rfl⟩ : syracuseStep 6921575 = 10382363) B10382363
theorem B4614383 : Blo 2159435 4614383 := bstep (se 1 (by rfl) ⟨3460787, by rfl⟩ : syracuseStep 4614383 = 6921575) B6921575
theorem B3076255 : Blo 2159435 3076255 := bstep (se 1 (by rfl) ⟨2307191, by rfl⟩ : syracuseStep 3076255 = 4614383) B4614383
theorem B4101673 : Blo 2159435 4101673 := bstep (se 2 (by rfl) ⟨1538127, by rfl⟩ : syracuseStep 4101673 = 3076255) B3076255
theorem B5468897 : Blo 2159435 5468897 := bstep (se 2 (by rfl) ⟨2050836, by rfl⟩ : syracuseStep 5468897 = 4101673) B4101673
theorem B3645931 : Blo 2159435 3645931 := bstep (se 1 (by rfl) ⟨2734448, by rfl⟩ : syracuseStep 3645931 = 5468897) B5468897
theorem B4861241 : Blo 2159435 4861241 := bstep (se 2 (by rfl) ⟨1822965, by rfl⟩ : syracuseStep 4861241 = 3645931) B3645931
theorem B3240827 : Blo 2159435 3240827 := bstep (se 1 (by rfl) ⟨2430620, by rfl⟩ : syracuseStep 3240827 = 4861241) B4861241
theorem B2160551 : Blo 2159435 2160551 := bstep (se 1 (by rfl) ⟨1620413, by rfl⟩ : syracuseStep 2160551 = 3240827) B3240827
theorem B2430625 : Blo 2159435 2430625 := bbase (se 2 (by rfl) ⟨911484, by rfl⟩ : syracuseStep 2430625 = 1822969) (by norm_num)
theorem B3240833 : Blo 2159435 3240833 := bstep (se 2 (by rfl) ⟨1215312, by rfl⟩ : syracuseStep 3240833 = 2430625) B2430625
theorem B2160555 : Blo 2159435 2160555 := bstep (se 1 (by rfl) ⟨1620416, by rfl⟩ : syracuseStep 2160555 = 3240833) B3240833
theorem B5468917 : Blo 2159435 5468917 := bbase (se 5 (by rfl) ⟨256355, by rfl⟩ : syracuseStep 5468917 = 512711) (by norm_num)
theorem B7291889 : Blo 2159435 7291889 := bstep (se 2 (by rfl) ⟨2734458, by rfl⟩ : syracuseStep 7291889 = 5468917) B5468917
theorem B4861259 : Blo 2159435 4861259 := bstep (se 1 (by rfl) ⟨3645944, by rfl⟩ : syracuseStep 4861259 = 7291889) B7291889
theorem B3240839 : Blo 2159435 3240839 := bstep (se 1 (by rfl) ⟨2430629, by rfl⟩ : syracuseStep 3240839 = 4861259) B4861259
theorem B2160559 : Blo 2159435 2160559 := bstep (se 1 (by rfl) ⟨1620419, by rfl⟩ : syracuseStep 2160559 = 3240839) B3240839
theorem B3240845 : Blo 2159435 3240845 := bbase (se 3 (by rfl) ⟨607658, by rfl⟩ : syracuseStep 3240845 = 1215317) (by norm_num)
theorem B2160563 : Blo 2159435 2160563 := bstep (se 1 (by rfl) ⟨1620422, by rfl⟩ : syracuseStep 2160563 = 3240845) B3240845
theorem B4861277 : Blo 2159435 4861277 := bbase (se 3 (by rfl) ⟨911489, by rfl⟩ : syracuseStep 4861277 = 1822979) (by norm_num)
theorem B3240851 : Blo 2159435 3240851 := bstep (se 1 (by rfl) ⟨2430638, by rfl⟩ : syracuseStep 3240851 = 4861277) B4861277
theorem B2160567 : Blo 2159435 2160567 := bstep (se 1 (by rfl) ⟨1620425, by rfl⟩ : syracuseStep 2160567 = 3240851) B3240851
theorem B3645965 : Blo 2159435 3645965 := bbase (se 3 (by rfl) ⟨683618, by rfl⟩ : syracuseStep 3645965 = 1367237) (by norm_num)
theorem B2430643 : Blo 2159435 2430643 := bstep (se 1 (by rfl) ⟨1822982, by rfl⟩ : syracuseStep 2430643 = 3645965) B3645965
theorem B3240857 : Blo 2159435 3240857 := bstep (se 2 (by rfl) ⟨1215321, by rfl⟩ : syracuseStep 3240857 = 2430643) B2430643
theorem B2160571 : Blo 2159435 2160571 := bstep (se 1 (by rfl) ⟨1620428, by rfl⟩ : syracuseStep 2160571 = 3240857) B3240857
theorem B3893429 : Blo 2159435 3893429 := bbase (se 5 (by rfl) ⟨182504, by rfl⟩ : syracuseStep 3893429 = 365009) (by norm_num)
theorem B2595619 : Blo 2159435 2595619 := bstep (se 1 (by rfl) ⟨1946714, by rfl⟩ : syracuseStep 2595619 = 3893429) B3893429
theorem B3460825 : Blo 2159435 3460825 := bstep (se 2 (by rfl) ⟨1297809, by rfl⟩ : syracuseStep 3460825 = 2595619) B2595619
theorem B18457733 : Blo 2159435 18457733 := bstep (se 4 (by rfl) ⟨1730412, by rfl⟩ : syracuseStep 18457733 = 3460825) B3460825
theorem B12305155 : Blo 2159435 12305155 := bstep (se 1 (by rfl) ⟨9228866, by rfl⟩ : syracuseStep 12305155 = 18457733) B18457733
theorem B16406873 : Blo 2159435 16406873 := bstep (se 2 (by rfl) ⟨6152577, by rfl⟩ : syracuseStep 16406873 = 12305155) B12305155
theorem B10937915 : Blo 2159435 10937915 := bstep (se 1 (by rfl) ⟨8203436, by rfl⟩ : syracuseStep 10937915 = 16406873) B16406873
theorem B7291943 : Blo 2159435 7291943 := bstep (se 1 (by rfl) ⟨5468957, by rfl⟩ : syracuseStep 7291943 = 10937915) B10937915
theorem B4861295 : Blo 2159435 4861295 := bstep (se 1 (by rfl) ⟨3645971, by rfl⟩ : syracuseStep 4861295 = 7291943) B7291943
theorem B3240863 : Blo 2159435 3240863 := bstep (se 1 (by rfl) ⟨2430647, by rfl⟩ : syracuseStep 3240863 = 4861295) B4861295
theorem B2160575 : Blo 2159435 2160575 := bstep (se 1 (by rfl) ⟨1620431, by rfl⟩ : syracuseStep 2160575 = 3240863) B3240863
theorem B3240869 : Blo 2159435 3240869 := bbase (se 4 (by rfl) ⟨303831, by rfl⟩ : syracuseStep 3240869 = 607663) (by norm_num)
theorem B2160579 : Blo 2159435 2160579 := bstep (se 1 (by rfl) ⟨1620434, by rfl⟩ : syracuseStep 2160579 = 3240869) B3240869
theorem B2734489 : Blo 2159435 2734489 := bbase (se 2 (by rfl) ⟨1025433, by rfl⟩ : syracuseStep 2734489 = 2050867) (by norm_num)
theorem B3645985 : Blo 2159435 3645985 := bstep (se 2 (by rfl) ⟨1367244, by rfl⟩ : syracuseStep 3645985 = 2734489) B2734489
theorem B4861313 : Blo 2159435 4861313 := bstep (se 2 (by rfl) ⟨1822992, by rfl⟩ : syracuseStep 4861313 = 3645985) B3645985
theorem B3240875 : Blo 2159435 3240875 := bstep (se 1 (by rfl) ⟨2430656, by rfl⟩ : syracuseStep 3240875 = 4861313) B4861313
theorem B2160583 : Blo 2159435 2160583 := bstep (se 1 (by rfl) ⟨1620437, by rfl⟩ : syracuseStep 2160583 = 3240875) B3240875
theorem B2430661 : Blo 2159435 2430661 := bbase (se 4 (by rfl) ⟨227874, by rfl⟩ : syracuseStep 2430661 = 455749) (by norm_num)
theorem B3240881 : Blo 2159435 3240881 := bstep (se 2 (by rfl) ⟨1215330, by rfl⟩ : syracuseStep 3240881 = 2430661) B2430661
theorem B2160587 : Blo 2159435 2160587 := bstep (se 1 (by rfl) ⟨1620440, by rfl⟩ : syracuseStep 2160587 = 3240881) B3240881
theorem B4101749 : Blo 2159435 4101749 := bbase (se 5 (by rfl) ⟨192269, by rfl⟩ : syracuseStep 4101749 = 384539) (by norm_num)
theorem B2734499 : Blo 2159435 2734499 := bstep (se 1 (by rfl) ⟨2050874, by rfl⟩ : syracuseStep 2734499 = 4101749) B4101749
theorem B7291997 : Blo 2159435 7291997 := bstep (se 3 (by rfl) ⟨1367249, by rfl⟩ : syracuseStep 7291997 = 2734499) B2734499
theorem B4861331 : Blo 2159435 4861331 := bstep (se 1 (by rfl) ⟨3645998, by rfl⟩ : syracuseStep 4861331 = 7291997) B7291997
theorem B3240887 : Blo 2159435 3240887 := bstep (se 1 (by rfl) ⟨2430665, by rfl⟩ : syracuseStep 3240887 = 4861331) B4861331
theorem B2160591 : Blo 2159435 2160591 := bstep (se 1 (by rfl) ⟨1620443, by rfl⟩ : syracuseStep 2160591 = 3240887) B3240887
theorem B3240893 : Blo 2159435 3240893 := bbase (se 3 (by rfl) ⟨607667, by rfl⟩ : syracuseStep 3240893 = 1215335) (by norm_num)
theorem B2160595 : Blo 2159435 2160595 := bstep (se 1 (by rfl) ⟨1620446, by rfl⟩ : syracuseStep 2160595 = 3240893) B3240893
theorem B4861349 : Blo 2159435 4861349 := bbase (se 4 (by rfl) ⟨455751, by rfl⟩ : syracuseStep 4861349 = 911503) (by norm_num)
theorem B3240899 : Blo 2159435 3240899 := bstep (se 1 (by rfl) ⟨2430674, by rfl⟩ : syracuseStep 3240899 = 4861349) B4861349
theorem B2160599 : Blo 2159435 2160599 := bstep (se 1 (by rfl) ⟨1620449, by rfl⟩ : syracuseStep 2160599 = 3240899) B3240899
theorem B5469029 : Blo 2159435 5469029 := bbase (se 4 (by rfl) ⟨512721, by rfl⟩ : syracuseStep 5469029 = 1025443) (by norm_num)
theorem B3646019 : Blo 2159435 3646019 := bstep (se 1 (by rfl) ⟨2734514, by rfl⟩ : syracuseStep 3646019 = 5469029) B5469029
theorem B2430679 : Blo 2159435 2430679 := bstep (se 1 (by rfl) ⟨1823009, by rfl⟩ : syracuseStep 2430679 = 3646019) B3646019
theorem B3240905 : Blo 2159435 3240905 := bstep (se 2 (by rfl) ⟨1215339, by rfl⟩ : syracuseStep 3240905 = 2430679) B2430679
theorem B2160603 : Blo 2159435 2160603 := bstep (se 1 (by rfl) ⟨1620452, by rfl⟩ : syracuseStep 2160603 = 3240905) B3240905
theorem B3460877 : Blo 2159435 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2307251 : Blo 2159435 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B6152669 : Blo 2159435 6152669 := bstep (se 3 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 6152669 = 2307251) B2307251
theorem B4101779 : Blo 2159435 4101779 := bstep (se 1 (by rfl) ⟨3076334, by rfl⟩ : syracuseStep 4101779 = 6152669) B6152669
theorem B10938077 : Blo 2159435 10938077 := bstep (se 3 (by rfl) ⟨2050889, by rfl⟩ : syracuseStep 10938077 = 4101779) B4101779
theorem B7292051 : Blo 2159435 7292051 := bstep (se 1 (by rfl) ⟨5469038, by rfl⟩ : syracuseStep 7292051 = 10938077) B10938077
theorem B4861367 : Blo 2159435 4861367 := bstep (se 1 (by rfl) ⟨3646025, by rfl⟩ : syracuseStep 4861367 = 7292051) B7292051
theorem B3240911 : Blo 2159435 3240911 := bstep (se 1 (by rfl) ⟨2430683, by rfl⟩ : syracuseStep 3240911 = 4861367) B4861367
theorem B2160607 : Blo 2159435 2160607 := bstep (se 1 (by rfl) ⟨1620455, by rfl⟩ : syracuseStep 2160607 = 3240911) B3240911
theorem B3240917 : Blo 2159435 3240917 := bbase (se 7 (by rfl) ⟨37979, by rfl⟩ : syracuseStep 3240917 = 75959) (by norm_num)
theorem B2160611 : Blo 2159435 2160611 := bstep (se 1 (by rfl) ⟨1620458, by rfl⟩ : syracuseStep 2160611 = 3240917) B3240917
theorem B8203589 : Blo 2159435 8203589 := bbase (se 4 (by rfl) ⟨769086, by rfl⟩ : syracuseStep 8203589 = 1538173) (by norm_num)
theorem B5469059 : Blo 2159435 5469059 := bstep (se 1 (by rfl) ⟨4101794, by rfl⟩ : syracuseStep 5469059 = 8203589) B8203589
theorem B3646039 : Blo 2159435 3646039 := bstep (se 1 (by rfl) ⟨2734529, by rfl⟩ : syracuseStep 3646039 = 5469059) B5469059
theorem B4861385 : Blo 2159435 4861385 := bstep (se 2 (by rfl) ⟨1823019, by rfl⟩ : syracuseStep 4861385 = 3646039) B3646039
theorem B3240923 : Blo 2159435 3240923 := bstep (se 1 (by rfl) ⟨2430692, by rfl⟩ : syracuseStep 3240923 = 4861385) B4861385
theorem B2160615 : Blo 2159435 2160615 := bstep (se 1 (by rfl) ⟨1620461, by rfl⟩ : syracuseStep 2160615 = 3240923) B3240923
theorem B2430697 : Blo 2159435 2430697 := bbase (se 2 (by rfl) ⟨911511, by rfl⟩ : syracuseStep 2430697 = 1823023) (by norm_num)
theorem B3240929 : Blo 2159435 3240929 := bstep (se 2 (by rfl) ⟨1215348, by rfl⟩ : syracuseStep 3240929 = 2430697) B2430697
theorem B2160619 : Blo 2159435 2160619 := bstep (se 1 (by rfl) ⟨1620464, by rfl⟩ : syracuseStep 2160619 = 3240929) B3240929
theorem B12305429 : Blo 2159435 12305429 := bbase (se 6 (by rfl) ⟨288408, by rfl⟩ : syracuseStep 12305429 = 576817) (by norm_num)
theorem B8203619 : Blo 2159435 8203619 := bstep (se 1 (by rfl) ⟨6152714, by rfl⟩ : syracuseStep 8203619 = 12305429) B12305429
theorem B5469079 : Blo 2159435 5469079 := bstep (se 1 (by rfl) ⟨4101809, by rfl⟩ : syracuseStep 5469079 = 8203619) B8203619
theorem B7292105 : Blo 2159435 7292105 := bstep (se 2 (by rfl) ⟨2734539, by rfl⟩ : syracuseStep 7292105 = 5469079) B5469079
theorem B4861403 : Blo 2159435 4861403 := bstep (se 1 (by rfl) ⟨3646052, by rfl⟩ : syracuseStep 4861403 = 7292105) B7292105
theorem B3240935 : Blo 2159435 3240935 := bstep (se 1 (by rfl) ⟨2430701, by rfl⟩ : syracuseStep 3240935 = 4861403) B4861403
theorem B2160623 : Blo 2159435 2160623 := bstep (se 1 (by rfl) ⟨1620467, by rfl⟩ : syracuseStep 2160623 = 3240935) B3240935
theorem B3240941 : Blo 2159435 3240941 := bbase (se 3 (by rfl) ⟨607676, by rfl⟩ : syracuseStep 3240941 = 1215353) (by norm_num)
theorem B2160627 : Blo 2159435 2160627 := bstep (se 1 (by rfl) ⟨1620470, by rfl⟩ : syracuseStep 2160627 = 3240941) B3240941
theorem B4861421 : Blo 2159435 4861421 := bbase (se 3 (by rfl) ⟨911516, by rfl⟩ : syracuseStep 4861421 = 1823033) (by norm_num)
theorem B3240947 : Blo 2159435 3240947 := bstep (se 1 (by rfl) ⟨2430710, by rfl⟩ : syracuseStep 3240947 = 4861421) B4861421
theorem B2160631 : Blo 2159435 2160631 := bstep (se 1 (by rfl) ⟨1620473, by rfl⟩ : syracuseStep 2160631 = 3240947) B3240947
theorem B6921845 : Blo 2159435 6921845 := bbase (se 5 (by rfl) ⟨324461, by rfl⟩ : syracuseStep 6921845 = 648923) (by norm_num)
theorem B4614563 : Blo 2159435 4614563 := bstep (se 1 (by rfl) ⟨3460922, by rfl⟩ : syracuseStep 4614563 = 6921845) B6921845
theorem B3076375 : Blo 2159435 3076375 := bstep (se 1 (by rfl) ⟨2307281, by rfl⟩ : syracuseStep 3076375 = 4614563) B4614563
theorem B4101833 : Blo 2159435 4101833 := bstep (se 2 (by rfl) ⟨1538187, by rfl⟩ : syracuseStep 4101833 = 3076375) B3076375
theorem B2734555 : Blo 2159435 2734555 := bstep (se 1 (by rfl) ⟨2050916, by rfl⟩ : syracuseStep 2734555 = 4101833) B4101833
theorem B3646073 : Blo 2159435 3646073 := bstep (se 2 (by rfl) ⟨1367277, by rfl⟩ : syracuseStep 3646073 = 2734555) B2734555
theorem B2430715 : Blo 2159435 2430715 := bstep (se 1 (by rfl) ⟨1823036, by rfl⟩ : syracuseStep 2430715 = 3646073) B3646073
theorem B3240953 : Blo 2159435 3240953 := bstep (se 2 (by rfl) ⟨1215357, by rfl⟩ : syracuseStep 3240953 = 2430715) B2430715
theorem B2160635 : Blo 2159435 2160635 := bstep (se 1 (by rfl) ⟨1620476, by rfl⟩ : syracuseStep 2160635 = 3240953) B3240953
theorem B2771869 : Blo 2159435 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B3695825 : Blo 2159435 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B2463883 : Blo 2159435 2463883 := bstep (se 1 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 2463883 = 3695825) B3695825
theorem B52562837 : Blo 2159435 52562837 := bstep (se 6 (by rfl) ⟨1231941, by rfl⟩ : syracuseStep 52562837 = 2463883) B2463883
theorem B35041891 : Blo 2159435 35041891 := bstep (se 1 (by rfl) ⟨26281418, by rfl⟩ : syracuseStep 35041891 = 52562837) B52562837
theorem B46722521 : Blo 2159435 46722521 := bstep (se 2 (by rfl) ⟨17520945, by rfl⟩ : syracuseStep 46722521 = 35041891) B35041891
theorem B124593389 : Blo 2159435 124593389 := bstep (se 3 (by rfl) ⟨23361260, by rfl⟩ : syracuseStep 124593389 = 46722521) B46722521
theorem B83062259 : Blo 2159435 83062259 := bstep (se 1 (by rfl) ⟨62296694, by rfl⟩ : syracuseStep 83062259 = 124593389) B124593389
theorem B55374839 : Blo 2159435 55374839 := bstep (se 1 (by rfl) ⟨41531129, by rfl⟩ : syracuseStep 55374839 = 83062259) B83062259
theorem B36916559 : Blo 2159435 36916559 := bstep (se 1 (by rfl) ⟨27687419, by rfl⟩ : syracuseStep 36916559 = 55374839) B55374839
theorem B24611039 : Blo 2159435 24611039 := bstep (se 1 (by rfl) ⟨18458279, by rfl⟩ : syracuseStep 24611039 = 36916559) B36916559
theorem B16407359 : Blo 2159435 16407359 := bstep (se 1 (by rfl) ⟨12305519, by rfl⟩ : syracuseStep 16407359 = 24611039) B24611039
theorem B10938239 : Blo 2159435 10938239 := bstep (se 1 (by rfl) ⟨8203679, by rfl⟩ : syracuseStep 10938239 = 16407359) B16407359
theorem B7292159 : Blo 2159435 7292159 := bstep (se 1 (by rfl) ⟨5469119, by rfl⟩ : syracuseStep 7292159 = 10938239) B10938239
theorem B4861439 : Blo 2159435 4861439 := bstep (se 1 (by rfl) ⟨3646079, by rfl⟩ : syracuseStep 4861439 = 7292159) B7292159
theorem B3240959 : Blo 2159435 3240959 := bstep (se 1 (by rfl) ⟨2430719, by rfl⟩ : syracuseStep 3240959 = 4861439) B4861439
theorem B2160639 : Blo 2159435 2160639 := bstep (se 1 (by rfl) ⟨1620479, by rfl⟩ : syracuseStep 2160639 = 3240959) B3240959
theorem B3240965 : Blo 2159435 3240965 := bbase (se 4 (by rfl) ⟨303840, by rfl⟩ : syracuseStep 3240965 = 607681) (by norm_num)
theorem B2160643 : Blo 2159435 2160643 := bstep (se 1 (by rfl) ⟨1620482, by rfl⟩ : syracuseStep 2160643 = 3240965) B3240965
theorem B3646093 : Blo 2159435 3646093 := bbase (se 3 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 3646093 = 1367285) (by norm_num)
theorem B4861457 : Blo 2159435 4861457 := bstep (se 2 (by rfl) ⟨1823046, by rfl⟩ : syracuseStep 4861457 = 3646093) B3646093
theorem B3240971 : Blo 2159435 3240971 := bstep (se 1 (by rfl) ⟨2430728, by rfl⟩ : syracuseStep 3240971 = 4861457) B4861457
theorem B2160647 : Blo 2159435 2160647 := bstep (se 1 (by rfl) ⟨1620485, by rfl⟩ : syracuseStep 2160647 = 3240971) B3240971
theorem B2430733 : Blo 2159435 2430733 := bbase (se 3 (by rfl) ⟨455762, by rfl⟩ : syracuseStep 2430733 = 911525) (by norm_num)
theorem B3240977 : Blo 2159435 3240977 := bstep (se 2 (by rfl) ⟨1215366, by rfl⟩ : syracuseStep 3240977 = 2430733) B2430733
theorem B2160651 : Blo 2159435 2160651 := bstep (se 1 (by rfl) ⟨1620488, by rfl⟩ : syracuseStep 2160651 = 3240977) B3240977
theorem B7292213 : Blo 2159435 7292213 := bbase (se 5 (by rfl) ⟨341822, by rfl⟩ : syracuseStep 7292213 = 683645) (by norm_num)
theorem B4861475 : Blo 2159435 4861475 := bstep (se 1 (by rfl) ⟨3646106, by rfl⟩ : syracuseStep 4861475 = 7292213) B7292213
theorem B3240983 : Blo 2159435 3240983 := bstep (se 1 (by rfl) ⟨2430737, by rfl⟩ : syracuseStep 3240983 = 4861475) B4861475
theorem B2160655 : Blo 2159435 2160655 := bstep (se 1 (by rfl) ⟨1620491, by rfl⟩ : syracuseStep 2160655 = 3240983) B3240983
theorem B3240989 : Blo 2159435 3240989 := bbase (se 3 (by rfl) ⟨607685, by rfl⟩ : syracuseStep 3240989 = 1215371) (by norm_num)
theorem B2160659 : Blo 2159435 2160659 := bstep (se 1 (by rfl) ⟨1620494, by rfl⟩ : syracuseStep 2160659 = 3240989) B3240989
theorem B4861493 : Blo 2159435 4861493 := bbase (se 5 (by rfl) ⟨227882, by rfl⟩ : syracuseStep 4861493 = 455765) (by norm_num)
theorem B3240995 : Blo 2159435 3240995 := bstep (se 1 (by rfl) ⟨2430746, by rfl⟩ : syracuseStep 3240995 = 4861493) B4861493
theorem B2160663 : Blo 2159435 2160663 := bstep (se 1 (by rfl) ⟨1620497, by rfl⟩ : syracuseStep 2160663 = 3240995) B3240995
theorem B3460973 : Blo 2159435 3460973 := bbase (se 3 (by rfl) ⟨648932, by rfl⟩ : syracuseStep 3460973 = 1297865) (by norm_num)
theorem B9229261 : Blo 2159435 9229261 := bstep (se 3 (by rfl) ⟨1730486, by rfl⟩ : syracuseStep 9229261 = 3460973) B3460973
theorem B12305681 : Blo 2159435 12305681 := bstep (se 2 (by rfl) ⟨4614630, by rfl⟩ : syracuseStep 12305681 = 9229261) B9229261
theorem B8203787 : Blo 2159435 8203787 := bstep (se 1 (by rfl) ⟨6152840, by rfl⟩ : syracuseStep 8203787 = 12305681) B12305681
theorem B5469191 : Blo 2159435 5469191 := bstep (se 1 (by rfl) ⟨4101893, by rfl⟩ : syracuseStep 5469191 = 8203787) B8203787
theorem B3646127 : Blo 2159435 3646127 := bstep (se 1 (by rfl) ⟨2734595, by rfl⟩ : syracuseStep 3646127 = 5469191) B5469191
theorem B2430751 : Blo 2159435 2430751 := bstep (se 1 (by rfl) ⟨1823063, by rfl⟩ : syracuseStep 2430751 = 3646127) B3646127
theorem B3241001 : Blo 2159435 3241001 := bstep (se 2 (by rfl) ⟨1215375, by rfl⟩ : syracuseStep 3241001 = 2430751) B2430751
theorem B2160667 : Blo 2159435 2160667 := bstep (se 1 (by rfl) ⟨1620500, by rfl⟩ : syracuseStep 2160667 = 3241001) B3241001
theorem B5191469 : Blo 2159435 5191469 := bbase (se 3 (by rfl) ⟨973400, by rfl⟩ : syracuseStep 5191469 = 1946801) (by norm_num)
theorem B3460979 : Blo 2159435 3460979 := bstep (se 1 (by rfl) ⟨2595734, by rfl⟩ : syracuseStep 3460979 = 5191469) B5191469
theorem B9229277 : Blo 2159435 9229277 := bstep (se 3 (by rfl) ⟨1730489, by rfl⟩ : syracuseStep 9229277 = 3460979) B3460979
theorem B6152851 : Blo 2159435 6152851 := bstep (se 1 (by rfl) ⟨4614638, by rfl⟩ : syracuseStep 6152851 = 9229277) B9229277
theorem B8203801 : Blo 2159435 8203801 := bstep (se 2 (by rfl) ⟨3076425, by rfl⟩ : syracuseStep 8203801 = 6152851) B6152851
theorem B10938401 : Blo 2159435 10938401 := bstep (se 2 (by rfl) ⟨4101900, by rfl⟩ : syracuseStep 10938401 = 8203801) B8203801
theorem B7292267 : Blo 2159435 7292267 := bstep (se 1 (by rfl) ⟨5469200, by rfl⟩ : syracuseStep 7292267 = 10938401) B10938401
theorem B4861511 : Blo 2159435 4861511 := bstep (se 1 (by rfl) ⟨3646133, by rfl⟩ : syracuseStep 4861511 = 7292267) B7292267
theorem B3241007 : Blo 2159435 3241007 := bstep (se 1 (by rfl) ⟨2430755, by rfl⟩ : syracuseStep 3241007 = 4861511) B4861511
theorem B2160671 : Blo 2159435 2160671 := bstep (se 1 (by rfl) ⟨1620503, by rfl⟩ : syracuseStep 2160671 = 3241007) B3241007
theorem B3241013 : Blo 2159435 3241013 := bbase (se 5 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 3241013 = 303845) (by norm_num)
theorem B2160675 : Blo 2159435 2160675 := bstep (se 1 (by rfl) ⟨1620506, by rfl⟩ : syracuseStep 2160675 = 3241013) B3241013
theorem B5469221 : Blo 2159435 5469221 := bbase (se 4 (by rfl) ⟨512739, by rfl⟩ : syracuseStep 5469221 = 1025479) (by norm_num)
theorem B3646147 : Blo 2159435 3646147 := bstep (se 1 (by rfl) ⟨2734610, by rfl⟩ : syracuseStep 3646147 = 5469221) B5469221
theorem B4861529 : Blo 2159435 4861529 := bstep (se 2 (by rfl) ⟨1823073, by rfl⟩ : syracuseStep 4861529 = 3646147) B3646147
theorem B3241019 : Blo 2159435 3241019 := bstep (se 1 (by rfl) ⟨2430764, by rfl⟩ : syracuseStep 3241019 = 4861529) B4861529
theorem B2160679 : Blo 2159435 2160679 := bstep (se 1 (by rfl) ⟨1620509, by rfl⟩ : syracuseStep 2160679 = 3241019) B3241019
theorem B2430769 : Blo 2159435 2430769 := bbase (se 2 (by rfl) ⟨911538, by rfl⟩ : syracuseStep 2430769 = 1823077) (by norm_num)
theorem B3241025 : Blo 2159435 3241025 := bstep (se 2 (by rfl) ⟨1215384, by rfl⟩ : syracuseStep 3241025 = 2430769) B2430769
theorem B2160683 : Blo 2159435 2160683 := bstep (se 1 (by rfl) ⟨1620512, by rfl⟩ : syracuseStep 2160683 = 3241025) B3241025
theorem B3461005 : Blo 2159435 3461005 := bbase (se 3 (by rfl) ⟨648938, by rfl⟩ : syracuseStep 3461005 = 1297877) (by norm_num)
theorem B4614673 : Blo 2159435 4614673 := bstep (se 2 (by rfl) ⟨1730502, by rfl⟩ : syracuseStep 4614673 = 3461005) B3461005
theorem B6152897 : Blo 2159435 6152897 := bstep (se 2 (by rfl) ⟨2307336, by rfl⟩ : syracuseStep 6152897 = 4614673) B4614673
theorem B4101931 : Blo 2159435 4101931 := bstep (se 1 (by rfl) ⟨3076448, by rfl⟩ : syracuseStep 4101931 = 6152897) B6152897
theorem B5469241 : Blo 2159435 5469241 := bstep (se 2 (by rfl) ⟨2050965, by rfl⟩ : syracuseStep 5469241 = 4101931) B4101931
theorem B7292321 : Blo 2159435 7292321 := bstep (se 2 (by rfl) ⟨2734620, by rfl⟩ : syracuseStep 7292321 = 5469241) B5469241
theorem B4861547 : Blo 2159435 4861547 := bstep (se 1 (by rfl) ⟨3646160, by rfl⟩ : syracuseStep 4861547 = 7292321) B7292321
theorem B3241031 : Blo 2159435 3241031 := bstep (se 1 (by rfl) ⟨2430773, by rfl⟩ : syracuseStep 3241031 = 4861547) B4861547
theorem B2160687 : Blo 2159435 2160687 := bstep (se 1 (by rfl) ⟨1620515, by rfl⟩ : syracuseStep 2160687 = 3241031) B3241031
theorem B3241037 : Blo 2159435 3241037 := bbase (se 3 (by rfl) ⟨607694, by rfl⟩ : syracuseStep 3241037 = 1215389) (by norm_num)
theorem B2160691 : Blo 2159435 2160691 := bstep (se 1 (by rfl) ⟨1620518, by rfl⟩ : syracuseStep 2160691 = 3241037) B3241037
theorem B4861565 : Blo 2159435 4861565 := bbase (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) (by norm_num)
theorem B3241043 : Blo 2159435 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B2160695 : Blo 2159435 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B3646181 : Blo 2159435 3646181 := bbase (se 4 (by rfl) ⟨341829, by rfl⟩ : syracuseStep 3646181 = 683659) (by norm_num)
theorem B2430787 : Blo 2159435 2430787 := bstep (se 1 (by rfl) ⟨1823090, by rfl⟩ : syracuseStep 2430787 = 3646181) B3646181
theorem B3241049 : Blo 2159435 3241049 := bstep (se 2 (by rfl) ⟨1215393, by rfl⟩ : syracuseStep 3241049 = 2430787) B2430787
theorem B2160699 : Blo 2159435 2160699 := bstep (se 1 (by rfl) ⟨1620524, by rfl⟩ : syracuseStep 2160699 = 3241049) B3241049
theorem B2595773 : Blo 2159435 2595773 := bbase (se 3 (by rfl) ⟨486707, by rfl⟩ : syracuseStep 2595773 = 973415) (by norm_num)
theorem B6922061 : Blo 2159435 6922061 := bstep (se 3 (by rfl) ⟨1297886, by rfl⟩ : syracuseStep 6922061 = 2595773) B2595773
theorem B4614707 : Blo 2159435 4614707 := bstep (se 1 (by rfl) ⟨3461030, by rfl⟩ : syracuseStep 4614707 = 6922061) B6922061
theorem B3076471 : Blo 2159435 3076471 := bstep (se 1 (by rfl) ⟨2307353, by rfl⟩ : syracuseStep 3076471 = 4614707) B4614707
theorem B16407845 : Blo 2159435 16407845 := bstep (se 4 (by rfl) ⟨1538235, by rfl⟩ : syracuseStep 16407845 = 3076471) B3076471
theorem B10938563 : Blo 2159435 10938563 := bstep (se 1 (by rfl) ⟨8203922, by rfl⟩ : syracuseStep 10938563 = 16407845) B16407845
theorem B7292375 : Blo 2159435 7292375 := bstep (se 1 (by rfl) ⟨5469281, by rfl⟩ : syracuseStep 7292375 = 10938563) B10938563
theorem B4861583 : Blo 2159435 4861583 := bstep (se 1 (by rfl) ⟨3646187, by rfl⟩ : syracuseStep 4861583 = 7292375) B7292375
theorem B3241055 : Blo 2159435 3241055 := bstep (se 1 (by rfl) ⟨2430791, by rfl⟩ : syracuseStep 3241055 = 4861583) B4861583
theorem B2160703 : Blo 2159435 2160703 := bstep (se 1 (by rfl) ⟨1620527, by rfl⟩ : syracuseStep 2160703 = 3241055) B3241055
theorem B3241061 : Blo 2159435 3241061 := bbase (se 4 (by rfl) ⟨303849, by rfl⟩ : syracuseStep 3241061 = 607699) (by norm_num)
theorem B2160707 : Blo 2159435 2160707 := bstep (se 1 (by rfl) ⟨1620530, by rfl⟩ : syracuseStep 2160707 = 3241061) B3241061
theorem B4614725 : Blo 2159435 4614725 := bbase (se 4 (by rfl) ⟨432630, by rfl⟩ : syracuseStep 4614725 = 865261) (by norm_num)
theorem B3076483 : Blo 2159435 3076483 := bstep (se 1 (by rfl) ⟨2307362, by rfl⟩ : syracuseStep 3076483 = 4614725) B4614725
theorem B4101977 : Blo 2159435 4101977 := bstep (se 2 (by rfl) ⟨1538241, by rfl⟩ : syracuseStep 4101977 = 3076483) B3076483
theorem B2734651 : Blo 2159435 2734651 := bstep (se 1 (by rfl) ⟨2050988, by rfl⟩ : syracuseStep 2734651 = 4101977) B4101977
theorem B3646201 : Blo 2159435 3646201 := bstep (se 2 (by rfl) ⟨1367325, by rfl⟩ : syracuseStep 3646201 = 2734651) B2734651
theorem B4861601 : Blo 2159435 4861601 := bstep (se 2 (by rfl) ⟨1823100, by rfl⟩ : syracuseStep 4861601 = 3646201) B3646201
theorem B3241067 : Blo 2159435 3241067 := bstep (se 1 (by rfl) ⟨2430800, by rfl⟩ : syracuseStep 3241067 = 4861601) B4861601
theorem B2160711 : Blo 2159435 2160711 := bstep (se 1 (by rfl) ⟨1620533, by rfl⟩ : syracuseStep 2160711 = 3241067) B3241067
theorem B2430805 : Blo 2159435 2430805 := bbase (se 9 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 2430805 = 14243) (by norm_num)
theorem B3241073 : Blo 2159435 3241073 := bstep (se 2 (by rfl) ⟨1215402, by rfl⟩ : syracuseStep 3241073 = 2430805) B2430805
theorem B2160715 : Blo 2159435 2160715 := bstep (se 1 (by rfl) ⟨1620536, by rfl⟩ : syracuseStep 2160715 = 3241073) B3241073
theorem B2734661 : Blo 2159435 2734661 := bbase (se 4 (by rfl) ⟨256374, by rfl⟩ : syracuseStep 2734661 = 512749) (by norm_num)
theorem B7292429 : Blo 2159435 7292429 := bstep (se 3 (by rfl) ⟨1367330, by rfl⟩ : syracuseStep 7292429 = 2734661) B2734661
theorem B4861619 : Blo 2159435 4861619 := bstep (se 1 (by rfl) ⟨3646214, by rfl⟩ : syracuseStep 4861619 = 7292429) B7292429
theorem B3241079 : Blo 2159435 3241079 := bstep (se 1 (by rfl) ⟨2430809, by rfl⟩ : syracuseStep 3241079 = 4861619) B4861619
theorem B2160719 : Blo 2159435 2160719 := bstep (se 1 (by rfl) ⟨1620539, by rfl⟩ : syracuseStep 2160719 = 3241079) B3241079
theorem B3241085 : Blo 2159435 3241085 := bbase (se 3 (by rfl) ⟨607703, by rfl⟩ : syracuseStep 3241085 = 1215407) (by norm_num)
theorem B2160723 : Blo 2159435 2160723 := bstep (se 1 (by rfl) ⟨1620542, by rfl⟩ : syracuseStep 2160723 = 3241085) B3241085
theorem B4861637 : Blo 2159435 4861637 := bbase (se 4 (by rfl) ⟨455778, by rfl⟩ : syracuseStep 4861637 = 911557) (by norm_num)
theorem B3241091 : Blo 2159435 3241091 := bstep (se 1 (by rfl) ⟨2430818, by rfl⟩ : syracuseStep 3241091 = 4861637) B4861637
theorem B2160727 : Blo 2159435 2160727 := bstep (se 1 (by rfl) ⟨1620545, by rfl⟩ : syracuseStep 2160727 = 3241091) B3241091
theorem B3556165 : Blo 2159435 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B4741553 : Blo 2159435 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B3161035 : Blo 2159435 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B16858853 : Blo 2159435 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B11239235 : Blo 2159435 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B7492823 : Blo 2159435 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B4995215 : Blo 2159435 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B3330143 : Blo 2159435 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B2220095 : Blo 2159435 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B5920253 : Blo 2159435 5920253 := bstep (se 3 (by rfl) ⟨1110047, by rfl⟩ : syracuseStep 5920253 = 2220095) B2220095
theorem B3946835 : Blo 2159435 3946835 := bstep (se 1 (by rfl) ⟨2960126, by rfl⟩ : syracuseStep 3946835 = 5920253) B5920253
theorem B2631223 : Blo 2159435 2631223 := bstep (se 1 (by rfl) ⟨1973417, by rfl⟩ : syracuseStep 2631223 = 3946835) B3946835
theorem B14033189 : Blo 2159435 14033189 := bstep (se 4 (by rfl) ⟨1315611, by rfl⟩ : syracuseStep 14033189 = 2631223) B2631223
theorem B9355459 : Blo 2159435 9355459 := bstep (se 1 (by rfl) ⟨7016594, by rfl⟩ : syracuseStep 9355459 = 14033189) B14033189
theorem B12473945 : Blo 2159435 12473945 := bstep (se 2 (by rfl) ⟨4677729, by rfl⟩ : syracuseStep 12473945 = 9355459) B9355459
theorem B8315963 : Blo 2159435 8315963 := bstep (se 1 (by rfl) ⟨6236972, by rfl⟩ : syracuseStep 8315963 = 12473945) B12473945
theorem B5543975 : Blo 2159435 5543975 := bstep (se 1 (by rfl) ⟨4157981, by rfl⟩ : syracuseStep 5543975 = 8315963) B8315963
theorem B14783933 : Blo 2159435 14783933 := bstep (se 3 (by rfl) ⟨2771987, by rfl⟩ : syracuseStep 14783933 = 5543975) B5543975
theorem B9855955 : Blo 2159435 9855955 := bstep (se 1 (by rfl) ⟨7391966, by rfl⟩ : syracuseStep 9855955 = 14783933) B14783933
theorem B13141273 : Blo 2159435 13141273 := bstep (se 2 (by rfl) ⟨4927977, by rfl⟩ : syracuseStep 13141273 = 9855955) B9855955
theorem B17521697 : Blo 2159435 17521697 := bstep (se 2 (by rfl) ⟨6570636, by rfl⟩ : syracuseStep 17521697 = 13141273) B13141273
theorem B46724525 : Blo 2159435 46724525 := bstep (se 3 (by rfl) ⟨8760848, by rfl⟩ : syracuseStep 46724525 = 17521697) B17521697
theorem B31149683 : Blo 2159435 31149683 := bstep (se 1 (by rfl) ⟨23362262, by rfl⟩ : syracuseStep 31149683 = 46724525) B46724525
theorem B20766455 : Blo 2159435 20766455 := bstep (se 1 (by rfl) ⟨15574841, by rfl⟩ : syracuseStep 20766455 = 31149683) B31149683
theorem B13844303 : Blo 2159435 13844303 := bstep (se 1 (by rfl) ⟨10383227, by rfl⟩ : syracuseStep 13844303 = 20766455) B20766455
theorem B9229535 : Blo 2159435 9229535 := bstep (se 1 (by rfl) ⟨6922151, by rfl⟩ : syracuseStep 9229535 = 13844303) B13844303
theorem B6153023 : Blo 2159435 6153023 := bstep (se 1 (by rfl) ⟨4614767, by rfl⟩ : syracuseStep 6153023 = 9229535) B9229535
theorem B4102015 : Blo 2159435 4102015 := bstep (se 1 (by rfl) ⟨3076511, by rfl⟩ : syracuseStep 4102015 = 6153023) B6153023
theorem B5469353 : Blo 2159435 5469353 := bstep (se 2 (by rfl) ⟨2051007, by rfl⟩ : syracuseStep 5469353 = 4102015) B4102015
theorem B3646235 : Blo 2159435 3646235 := bstep (se 1 (by rfl) ⟨2734676, by rfl⟩ : syracuseStep 3646235 = 5469353) B5469353
theorem B2430823 : Blo 2159435 2430823 := bstep (se 1 (by rfl) ⟨1823117, by rfl⟩ : syracuseStep 2430823 = 3646235) B3646235
theorem B3241097 : Blo 2159435 3241097 := bstep (se 2 (by rfl) ⟨1215411, by rfl⟩ : syracuseStep 3241097 = 2430823) B2430823
theorem B2160731 : Blo 2159435 2160731 := bstep (se 1 (by rfl) ⟨1620548, by rfl⟩ : syracuseStep 2160731 = 3241097) B3241097
theorem B10938725 : Blo 2159435 10938725 := bbase (se 4 (by rfl) ⟨1025505, by rfl⟩ : syracuseStep 10938725 = 2051011) (by norm_num)
theorem B7292483 : Blo 2159435 7292483 := bstep (se 1 (by rfl) ⟨5469362, by rfl⟩ : syracuseStep 7292483 = 10938725) B10938725
theorem B4861655 : Blo 2159435 4861655 := bstep (se 1 (by rfl) ⟨3646241, by rfl⟩ : syracuseStep 4861655 = 7292483) B7292483
theorem B3241103 : Blo 2159435 3241103 := bstep (se 1 (by rfl) ⟨2430827, by rfl⟩ : syracuseStep 3241103 = 4861655) B4861655
theorem B2160735 : Blo 2159435 2160735 := bstep (se 1 (by rfl) ⟨1620551, by rfl⟩ : syracuseStep 2160735 = 3241103) B3241103
theorem B3241109 : Blo 2159435 3241109 := bbase (se 6 (by rfl) ⟨75963, by rfl⟩ : syracuseStep 3241109 = 151927) (by norm_num)
theorem B2160739 : Blo 2159435 2160739 := bstep (se 1 (by rfl) ⟨1620554, by rfl⟩ : syracuseStep 2160739 = 3241109) B3241109
theorem B2595821 : Blo 2159435 2595821 := bbase (se 3 (by rfl) ⟨486716, by rfl⟩ : syracuseStep 2595821 = 973433) (by norm_num)
theorem B6922189 : Blo 2159435 6922189 := bstep (se 3 (by rfl) ⟨1297910, by rfl⟩ : syracuseStep 6922189 = 2595821) B2595821
theorem B9229585 : Blo 2159435 9229585 := bstep (se 2 (by rfl) ⟨3461094, by rfl⟩ : syracuseStep 9229585 = 6922189) B6922189
theorem B12306113 : Blo 2159435 12306113 := bstep (se 2 (by rfl) ⟨4614792, by rfl⟩ : syracuseStep 12306113 = 9229585) B9229585
theorem B8204075 : Blo 2159435 8204075 := bstep (se 1 (by rfl) ⟨6153056, by rfl⟩ : syracuseStep 8204075 = 12306113) B12306113
theorem B5469383 : Blo 2159435 5469383 := bstep (se 1 (by rfl) ⟨4102037, by rfl⟩ : syracuseStep 5469383 = 8204075) B8204075
theorem B3646255 : Blo 2159435 3646255 := bstep (se 1 (by rfl) ⟨2734691, by rfl⟩ : syracuseStep 3646255 = 5469383) B5469383
theorem B4861673 : Blo 2159435 4861673 := bstep (se 2 (by rfl) ⟨1823127, by rfl⟩ : syracuseStep 4861673 = 3646255) B3646255
theorem B3241115 : Blo 2159435 3241115 := bstep (se 1 (by rfl) ⟨2430836, by rfl⟩ : syracuseStep 3241115 = 4861673) B4861673
theorem B2160743 : Blo 2159435 2160743 := bstep (se 1 (by rfl) ⟨1620557, by rfl⟩ : syracuseStep 2160743 = 3241115) B3241115
theorem B2430841 : Blo 2159435 2430841 := bbase (se 2 (by rfl) ⟨911565, by rfl⟩ : syracuseStep 2430841 = 1823131) (by norm_num)
theorem B3241121 : Blo 2159435 3241121 := bstep (se 2 (by rfl) ⟨1215420, by rfl⟩ : syracuseStep 3241121 = 2430841) B2430841
theorem B2160747 : Blo 2159435 2160747 := bstep (se 1 (by rfl) ⟨1620560, by rfl⟩ : syracuseStep 2160747 = 3241121) B3241121
theorem B5191661 : Blo 2159435 5191661 := bbase (se 3 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 5191661 = 1946873) (by norm_num)
theorem B13844429 : Blo 2159435 13844429 := bstep (se 3 (by rfl) ⟨2595830, by rfl⟩ : syracuseStep 13844429 = 5191661) B5191661
theorem B9229619 : Blo 2159435 9229619 := bstep (se 1 (by rfl) ⟨6922214, by rfl⟩ : syracuseStep 9229619 = 13844429) B13844429
theorem B6153079 : Blo 2159435 6153079 := bstep (se 1 (by rfl) ⟨4614809, by rfl⟩ : syracuseStep 6153079 = 9229619) B9229619
theorem B8204105 : Blo 2159435 8204105 := bstep (se 2 (by rfl) ⟨3076539, by rfl⟩ : syracuseStep 8204105 = 6153079) B6153079
theorem B5469403 : Blo 2159435 5469403 := bstep (se 1 (by rfl) ⟨4102052, by rfl⟩ : syracuseStep 5469403 = 8204105) B8204105
theorem B7292537 : Blo 2159435 7292537 := bstep (se 2 (by rfl) ⟨2734701, by rfl⟩ : syracuseStep 7292537 = 5469403) B5469403
theorem B4861691 : Blo 2159435 4861691 := bstep (se 1 (by rfl) ⟨3646268, by rfl⟩ : syracuseStep 4861691 = 7292537) B7292537
theorem B3241127 : Blo 2159435 3241127 := bstep (se 1 (by rfl) ⟨2430845, by rfl⟩ : syracuseStep 3241127 = 4861691) B4861691
theorem B2160751 : Blo 2159435 2160751 := bstep (se 1 (by rfl) ⟨1620563, by rfl⟩ : syracuseStep 2160751 = 3241127) B3241127
theorem B3241133 : Blo 2159435 3241133 := bbase (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) (by norm_num)
theorem B2160755 : Blo 2159435 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B4861709 : Blo 2159435 4861709 := bbase (se 3 (by rfl) ⟨911570, by rfl⟩ : syracuseStep 4861709 = 1823141) (by norm_num)
theorem B3241139 : Blo 2159435 3241139 := bstep (se 1 (by rfl) ⟨2430854, by rfl⟩ : syracuseStep 3241139 = 4861709) B4861709
theorem B2160759 : Blo 2159435 2160759 := bstep (se 1 (by rfl) ⟨1620569, by rfl⟩ : syracuseStep 2160759 = 3241139) B3241139
theorem B2734717 : Blo 2159435 2734717 := bbase (se 3 (by rfl) ⟨512759, by rfl⟩ : syracuseStep 2734717 = 1025519) (by norm_num)
theorem B3646289 : Blo 2159435 3646289 := bstep (se 2 (by rfl) ⟨1367358, by rfl⟩ : syracuseStep 3646289 = 2734717) B2734717
theorem B2430859 : Blo 2159435 2430859 := bstep (se 1 (by rfl) ⟨1823144, by rfl⟩ : syracuseStep 2430859 = 3646289) B3646289
theorem B3241145 : Blo 2159435 3241145 := bstep (se 2 (by rfl) ⟨1215429, by rfl⟩ : syracuseStep 3241145 = 2430859) B2430859
theorem B2160763 : Blo 2159435 2160763 := bstep (se 1 (by rfl) ⟨1620572, by rfl⟩ : syracuseStep 2160763 = 3241145) B3241145
theorem B3285373 : Blo 2159435 3285373 := bbase (se 3 (by rfl) ⟨616007, by rfl⟩ : syracuseStep 3285373 = 1232015) (by norm_num)
theorem B4380497 : Blo 2159435 4380497 := bstep (se 2 (by rfl) ⟨1642686, by rfl⟩ : syracuseStep 4380497 = 3285373) B3285373
theorem B2920331 : Blo 2159435 2920331 := bstep (se 1 (by rfl) ⟨2190248, by rfl⟩ : syracuseStep 2920331 = 4380497) B4380497
theorem B7787549 : Blo 2159435 7787549 := bstep (se 3 (by rfl) ⟨1460165, by rfl⟩ : syracuseStep 7787549 = 2920331) B2920331
theorem B5191699 : Blo 2159435 5191699 := bstep (se 1 (by rfl) ⟨3893774, by rfl⟩ : syracuseStep 5191699 = 7787549) B7787549
theorem B6922265 : Blo 2159435 6922265 := bstep (se 2 (by rfl) ⟨2595849, by rfl⟩ : syracuseStep 6922265 = 5191699) B5191699
theorem B18459373 : Blo 2159435 18459373 := bstep (se 3 (by rfl) ⟨3461132, by rfl⟩ : syracuseStep 18459373 = 6922265) B6922265
theorem B24612497 : Blo 2159435 24612497 := bstep (se 2 (by rfl) ⟨9229686, by rfl⟩ : syracuseStep 24612497 = 18459373) B18459373
theorem B16408331 : Blo 2159435 16408331 := bstep (se 1 (by rfl) ⟨12306248, by rfl⟩ : syracuseStep 16408331 = 24612497) B24612497
theorem B10938887 : Blo 2159435 10938887 := bstep (se 1 (by rfl) ⟨8204165, by rfl⟩ : syracuseStep 10938887 = 16408331) B16408331
theorem B7292591 : Blo 2159435 7292591 := bstep (se 1 (by rfl) ⟨5469443, by rfl⟩ : syracuseStep 7292591 = 10938887) B10938887
theorem B4861727 : Blo 2159435 4861727 := bstep (se 1 (by rfl) ⟨3646295, by rfl⟩ : syracuseStep 4861727 = 7292591) B7292591
theorem B3241151 : Blo 2159435 3241151 := bstep (se 1 (by rfl) ⟨2430863, by rfl⟩ : syracuseStep 3241151 = 4861727) B4861727
theorem B2160767 : Blo 2159435 2160767 := bstep (se 1 (by rfl) ⟨1620575, by rfl⟩ : syracuseStep 2160767 = 3241151) B3241151
theorem B3241157 : Blo 2159435 3241157 := bbase (se 4 (by rfl) ⟨303858, by rfl⟩ : syracuseStep 3241157 = 607717) (by norm_num)
theorem B2160771 : Blo 2159435 2160771 := bstep (se 1 (by rfl) ⟨1620578, by rfl⟩ : syracuseStep 2160771 = 3241157) B3241157
theorem B3646309 : Blo 2159435 3646309 := bbase (se 4 (by rfl) ⟨341841, by rfl⟩ : syracuseStep 3646309 = 683683) (by norm_num)
theorem B4861745 : Blo 2159435 4861745 := bstep (se 2 (by rfl) ⟨1823154, by rfl⟩ : syracuseStep 4861745 = 3646309) B3646309
theorem B3241163 : Blo 2159435 3241163 := bstep (se 1 (by rfl) ⟨2430872, by rfl⟩ : syracuseStep 3241163 = 4861745) B4861745
theorem B2160775 : Blo 2159435 2160775 := bstep (se 1 (by rfl) ⟨1620581, by rfl⟩ : syracuseStep 2160775 = 3241163) B3241163
theorem B2430877 : Blo 2159435 2430877 := bbase (se 3 (by rfl) ⟨455789, by rfl⟩ : syracuseStep 2430877 = 911579) (by norm_num)
theorem B3241169 : Blo 2159435 3241169 := bstep (se 2 (by rfl) ⟨1215438, by rfl⟩ : syracuseStep 3241169 = 2430877) B2430877
theorem B2160779 : Blo 2159435 2160779 := bstep (se 1 (by rfl) ⟨1620584, by rfl⟩ : syracuseStep 2160779 = 3241169) B3241169
theorem B7292645 : Blo 2159435 7292645 := bbase (se 4 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 7292645 = 1367371) (by norm_num)
theorem B4861763 : Blo 2159435 4861763 := bstep (se 1 (by rfl) ⟨3646322, by rfl⟩ : syracuseStep 4861763 = 7292645) B7292645
theorem B3241175 : Blo 2159435 3241175 := bstep (se 1 (by rfl) ⟨2430881, by rfl⟩ : syracuseStep 3241175 = 4861763) B4861763
theorem B2160783 : Blo 2159435 2160783 := bstep (se 1 (by rfl) ⟨1620587, by rfl⟩ : syracuseStep 2160783 = 3241175) B3241175
theorem B3241181 : Blo 2159435 3241181 := bbase (se 3 (by rfl) ⟨607721, by rfl⟩ : syracuseStep 3241181 = 1215443) (by norm_num)
theorem B2160787 : Blo 2159435 2160787 := bstep (se 1 (by rfl) ⟨1620590, by rfl⟩ : syracuseStep 2160787 = 3241181) B3241181
theorem B4861781 : Blo 2159435 4861781 := bbase (se 9 (by rfl) ⟨14243, by rfl⟩ : syracuseStep 4861781 = 28487) (by norm_num)
theorem B3241187 : Blo 2159435 3241187 := bstep (se 1 (by rfl) ⟨2430890, by rfl⟩ : syracuseStep 3241187 = 4861781) B4861781
theorem B2160791 : Blo 2159435 2160791 := bstep (se 1 (by rfl) ⟨1620593, by rfl⟩ : syracuseStep 2160791 = 3241187) B3241187
theorem B6153205 : Blo 2159435 6153205 := bbase (se 5 (by rfl) ⟨288431, by rfl⟩ : syracuseStep 6153205 = 576863) (by norm_num)
theorem B8204273 : Blo 2159435 8204273 := bstep (se 2 (by rfl) ⟨3076602, by rfl⟩ : syracuseStep 8204273 = 6153205) B6153205
theorem B5469515 : Blo 2159435 5469515 := bstep (se 1 (by rfl) ⟨4102136, by rfl⟩ : syracuseStep 5469515 = 8204273) B8204273
theorem B3646343 : Blo 2159435 3646343 := bstep (se 1 (by rfl) ⟨2734757, by rfl⟩ : syracuseStep 3646343 = 5469515) B5469515
theorem B2430895 : Blo 2159435 2430895 := bstep (se 1 (by rfl) ⟨1823171, by rfl⟩ : syracuseStep 2430895 = 3646343) B3646343
theorem B3241193 : Blo 2159435 3241193 := bstep (se 2 (by rfl) ⟨1215447, by rfl⟩ : syracuseStep 3241193 = 2430895) B2430895
theorem B2160795 : Blo 2159435 2160795 := bstep (se 1 (by rfl) ⟨1620596, by rfl⟩ : syracuseStep 2160795 = 3241193) B3241193
theorem B2667205 : Blo 2159435 2667205 := bbase (se 4 (by rfl) ⟨250050, by rfl⟩ : syracuseStep 2667205 = 500101) (by norm_num)
theorem B3556273 : Blo 2159435 3556273 := bstep (se 2 (by rfl) ⟨1333602, by rfl⟩ : syracuseStep 3556273 = 2667205) B2667205
theorem B4741697 : Blo 2159435 4741697 := bstep (se 2 (by rfl) ⟨1778136, by rfl⟩ : syracuseStep 4741697 = 3556273) B3556273
theorem B12644525 : Blo 2159435 12644525 := bstep (se 3 (by rfl) ⟨2370848, by rfl⟩ : syracuseStep 12644525 = 4741697) B4741697
theorem B8429683 : Blo 2159435 8429683 := bstep (se 1 (by rfl) ⟨6322262, by rfl⟩ : syracuseStep 8429683 = 12644525) B12644525
theorem B11239577 : Blo 2159435 11239577 := bstep (se 2 (by rfl) ⟨4214841, by rfl⟩ : syracuseStep 11239577 = 8429683) B8429683
theorem B7493051 : Blo 2159435 7493051 := bstep (se 1 (by rfl) ⟨5619788, by rfl⟩ : syracuseStep 7493051 = 11239577) B11239577
theorem B4995367 : Blo 2159435 4995367 := bstep (se 1 (by rfl) ⟨3746525, by rfl⟩ : syracuseStep 4995367 = 7493051) B7493051
theorem B106567829 : Blo 2159435 106567829 := bstep (se 6 (by rfl) ⟨2497683, by rfl⟩ : syracuseStep 106567829 = 4995367) B4995367
theorem B71045219 : Blo 2159435 71045219 := bstep (se 1 (by rfl) ⟨53283914, by rfl⟩ : syracuseStep 71045219 = 106567829) B106567829
theorem B189453917 : Blo 2159435 189453917 := bstep (se 3 (by rfl) ⟨35522609, by rfl⟩ : syracuseStep 189453917 = 71045219) B71045219
theorem B505210445 : Blo 2159435 505210445 := bstep (se 3 (by rfl) ⟨94726958, by rfl⟩ : syracuseStep 505210445 = 189453917) B189453917
theorem B336806963 : Blo 2159435 336806963 := bstep (se 1 (by rfl) ⟨252605222, by rfl⟩ : syracuseStep 336806963 = 505210445) B505210445
theorem B224537975 : Blo 2159435 224537975 := bstep (se 1 (by rfl) ⟨168403481, by rfl⟩ : syracuseStep 224537975 = 336806963) B336806963
theorem B149691983 : Blo 2159435 149691983 := bstep (se 1 (by rfl) ⟨112268987, by rfl⟩ : syracuseStep 149691983 = 224537975) B224537975
theorem B399178621 : Blo 2159435 399178621 := bstep (se 3 (by rfl) ⟨74845991, by rfl⟩ : syracuseStep 399178621 = 149691983) B149691983
theorem B532238161 : Blo 2159435 532238161 := bstep (se 2 (by rfl) ⟨199589310, by rfl⟩ : syracuseStep 532238161 = 399178621) B399178621
theorem B709650881 : Blo 2159435 709650881 := bstep (se 2 (by rfl) ⟨266119080, by rfl⟩ : syracuseStep 709650881 = 532238161) B532238161
theorem B473100587 : Blo 2159435 473100587 := bstep (se 1 (by rfl) ⟨354825440, by rfl⟩ : syracuseStep 473100587 = 709650881) B709650881
theorem B315400391 : Blo 2159435 315400391 := bstep (se 1 (by rfl) ⟨236550293, by rfl⟩ : syracuseStep 315400391 = 473100587) B473100587
theorem B210266927 : Blo 2159435 210266927 := bstep (se 1 (by rfl) ⟨157700195, by rfl⟩ : syracuseStep 210266927 = 315400391) B315400391
theorem B140177951 : Blo 2159435 140177951 := bstep (se 1 (by rfl) ⟨105133463, by rfl⟩ : syracuseStep 140177951 = 210266927) B210266927
theorem B93451967 : Blo 2159435 93451967 := bstep (se 1 (by rfl) ⟨70088975, by rfl⟩ : syracuseStep 93451967 = 140177951) B140177951
theorem B62301311 : Blo 2159435 62301311 := bstep (se 1 (by rfl) ⟨46725983, by rfl⟩ : syracuseStep 62301311 = 93451967) B93451967
theorem B41534207 : Blo 2159435 41534207 := bstep (se 1 (by rfl) ⟨31150655, by rfl⟩ : syracuseStep 41534207 = 62301311) B62301311
theorem B27689471 : Blo 2159435 27689471 := bstep (se 1 (by rfl) ⟨20767103, by rfl⟩ : syracuseStep 27689471 = 41534207) B41534207
theorem B18459647 : Blo 2159435 18459647 := bstep (se 1 (by rfl) ⟨13844735, by rfl⟩ : syracuseStep 18459647 = 27689471) B27689471
theorem B12306431 : Blo 2159435 12306431 := bstep (se 1 (by rfl) ⟨9229823, by rfl⟩ : syracuseStep 12306431 = 18459647) B18459647
theorem B8204287 : Blo 2159435 8204287 := bstep (se 1 (by rfl) ⟨6153215, by rfl⟩ : syracuseStep 8204287 = 12306431) B12306431
theorem B10939049 : Blo 2159435 10939049 := bstep (se 2 (by rfl) ⟨4102143, by rfl⟩ : syracuseStep 10939049 = 8204287) B8204287
theorem B7292699 : Blo 2159435 7292699 := bstep (se 1 (by rfl) ⟨5469524, by rfl⟩ : syracuseStep 7292699 = 10939049) B10939049
theorem B4861799 : Blo 2159435 4861799 := bstep (se 1 (by rfl) ⟨3646349, by rfl⟩ : syracuseStep 4861799 = 7292699) B7292699
theorem B3241199 : Blo 2159435 3241199 := bstep (se 1 (by rfl) ⟨2430899, by rfl⟩ : syracuseStep 3241199 = 4861799) B4861799
theorem B2160799 : Blo 2159435 2160799 := bstep (se 1 (by rfl) ⟨1620599, by rfl⟩ : syracuseStep 2160799 = 3241199) B3241199
theorem B3241205 : Blo 2159435 3241205 := bbase (se 5 (by rfl) ⟨151931, by rfl⟩ : syracuseStep 3241205 = 303863) (by norm_num)
theorem B2160803 : Blo 2159435 2160803 := bstep (se 1 (by rfl) ⟨1620602, by rfl⟩ : syracuseStep 2160803 = 3241205) B3241205
theorem B13844789 : Blo 2159435 13844789 := bbase (se 5 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 13844789 = 1297949) (by norm_num)
theorem B9229859 : Blo 2159435 9229859 := bstep (se 1 (by rfl) ⟨6922394, by rfl⟩ : syracuseStep 9229859 = 13844789) B13844789
theorem B6153239 : Blo 2159435 6153239 := bstep (se 1 (by rfl) ⟨4614929, by rfl⟩ : syracuseStep 6153239 = 9229859) B9229859
theorem B4102159 : Blo 2159435 4102159 := bstep (se 1 (by rfl) ⟨3076619, by rfl⟩ : syracuseStep 4102159 = 6153239) B6153239
theorem B5469545 : Blo 2159435 5469545 := bstep (se 2 (by rfl) ⟨2051079, by rfl⟩ : syracuseStep 5469545 = 4102159) B4102159
theorem B3646363 : Blo 2159435 3646363 := bstep (se 1 (by rfl) ⟨2734772, by rfl⟩ : syracuseStep 3646363 = 5469545) B5469545
theorem B4861817 : Blo 2159435 4861817 := bstep (se 2 (by rfl) ⟨1823181, by rfl⟩ : syracuseStep 4861817 = 3646363) B3646363
theorem B3241211 : Blo 2159435 3241211 := bstep (se 1 (by rfl) ⟨2430908, by rfl⟩ : syracuseStep 3241211 = 4861817) B4861817
theorem B2160807 : Blo 2159435 2160807 := bstep (se 1 (by rfl) ⟨1620605, by rfl⟩ : syracuseStep 2160807 = 3241211) B3241211
theorem B2430913 : Blo 2159435 2430913 := bbase (se 2 (by rfl) ⟨911592, by rfl⟩ : syracuseStep 2430913 = 1823185) (by norm_num)
theorem B3241217 : Blo 2159435 3241217 := bstep (se 2 (by rfl) ⟨1215456, by rfl⟩ : syracuseStep 3241217 = 2430913) B2430913
theorem B2160811 : Blo 2159435 2160811 := bstep (se 1 (by rfl) ⟨1620608, by rfl⟩ : syracuseStep 2160811 = 3241217) B3241217
theorem B5469565 : Blo 2159435 5469565 := bbase (se 3 (by rfl) ⟨1025543, by rfl⟩ : syracuseStep 5469565 = 2051087) (by norm_num)
theorem B7292753 : Blo 2159435 7292753 := bstep (se 2 (by rfl) ⟨2734782, by rfl⟩ : syracuseStep 7292753 = 5469565) B5469565
theorem B4861835 : Blo 2159435 4861835 := bstep (se 1 (by rfl) ⟨3646376, by rfl⟩ : syracuseStep 4861835 = 7292753) B7292753
theorem B3241223 : Blo 2159435 3241223 := bstep (se 1 (by rfl) ⟨2430917, by rfl⟩ : syracuseStep 3241223 = 4861835) B4861835
theorem B2160815 : Blo 2159435 2160815 := bstep (se 1 (by rfl) ⟨1620611, by rfl⟩ : syracuseStep 2160815 = 3241223) B3241223
theorem B3241229 : Blo 2159435 3241229 := bbase (se 3 (by rfl) ⟨607730, by rfl⟩ : syracuseStep 3241229 = 1215461) (by norm_num)
theorem B2160819 : Blo 2159435 2160819 := bstep (se 1 (by rfl) ⟨1620614, by rfl⟩ : syracuseStep 2160819 = 3241229) B3241229
theorem B4861853 : Blo 2159435 4861853 := bbase (se 3 (by rfl) ⟨911597, by rfl⟩ : syracuseStep 4861853 = 1823195) (by norm_num)
theorem B3241235 : Blo 2159435 3241235 := bstep (se 1 (by rfl) ⟨2430926, by rfl⟩ : syracuseStep 3241235 = 4861853) B4861853
theorem B2160823 : Blo 2159435 2160823 := bstep (se 1 (by rfl) ⟨1620617, by rfl⟩ : syracuseStep 2160823 = 3241235) B3241235
theorem B3646397 : Blo 2159435 3646397 := bbase (se 3 (by rfl) ⟨683699, by rfl⟩ : syracuseStep 3646397 = 1367399) (by norm_num)
theorem B2430931 : Blo 2159435 2430931 := bstep (se 1 (by rfl) ⟨1823198, by rfl⟩ : syracuseStep 2430931 = 3646397) B3646397
theorem B3241241 : Blo 2159435 3241241 := bstep (se 2 (by rfl) ⟨1215465, by rfl⟩ : syracuseStep 3241241 = 2430931) B2430931
theorem B2160827 : Blo 2159435 2160827 := bstep (se 1 (by rfl) ⟨1620620, by rfl⟩ : syracuseStep 2160827 = 3241241) B3241241
theorem B12306613 : Blo 2159435 12306613 := bbase (se 5 (by rfl) ⟨576872, by rfl⟩ : syracuseStep 12306613 = 1153745) (by norm_num)
theorem B16408817 : Blo 2159435 16408817 := bstep (se 2 (by rfl) ⟨6153306, by rfl⟩ : syracuseStep 16408817 = 12306613) B12306613
theorem B10939211 : Blo 2159435 10939211 := bstep (se 1 (by rfl) ⟨8204408, by rfl⟩ : syracuseStep 10939211 = 16408817) B16408817
theorem B7292807 : Blo 2159435 7292807 := bstep (se 1 (by rfl) ⟨5469605, by rfl⟩ : syracuseStep 7292807 = 10939211) B10939211
theorem B4861871 : Blo 2159435 4861871 := bstep (se 1 (by rfl) ⟨3646403, by rfl⟩ : syracuseStep 4861871 = 7292807) B7292807
theorem B3241247 : Blo 2159435 3241247 := bstep (se 1 (by rfl) ⟨2430935, by rfl⟩ : syracuseStep 3241247 = 4861871) B4861871
theorem B2160831 : Blo 2159435 2160831 := bstep (se 1 (by rfl) ⟨1620623, by rfl⟩ : syracuseStep 2160831 = 3241247) B3241247
theorem B3241253 : Blo 2159435 3241253 := bbase (se 4 (by rfl) ⟨303867, by rfl⟩ : syracuseStep 3241253 = 607735) (by norm_num)
theorem B2160835 : Blo 2159435 2160835 := bstep (se 1 (by rfl) ⟨1620626, by rfl⟩ : syracuseStep 2160835 = 3241253) B3241253
theorem B2734813 : Blo 2159435 2734813 := bbase (se 3 (by rfl) ⟨512777, by rfl⟩ : syracuseStep 2734813 = 1025555) (by norm_num)
theorem B3646417 : Blo 2159435 3646417 := bstep (se 2 (by rfl) ⟨1367406, by rfl⟩ : syracuseStep 3646417 = 2734813) B2734813
theorem B4861889 : Blo 2159435 4861889 := bstep (se 2 (by rfl) ⟨1823208, by rfl⟩ : syracuseStep 4861889 = 3646417) B3646417
theorem B3241259 : Blo 2159435 3241259 := bstep (se 1 (by rfl) ⟨2430944, by rfl⟩ : syracuseStep 3241259 = 4861889) B4861889
theorem B2160839 : Blo 2159435 2160839 := bstep (se 1 (by rfl) ⟨1620629, by rfl⟩ : syracuseStep 2160839 = 3241259) B3241259
theorem B2430949 : Blo 2159435 2430949 := bbase (se 4 (by rfl) ⟨227901, by rfl⟩ : syracuseStep 2430949 = 455803) (by norm_num)
theorem B3241265 : Blo 2159435 3241265 := bstep (se 2 (by rfl) ⟨1215474, by rfl⟩ : syracuseStep 3241265 = 2430949) B2430949
theorem B2160843 : Blo 2159435 2160843 := bstep (se 1 (by rfl) ⟨1620632, by rfl⟩ : syracuseStep 2160843 = 3241265) B3241265
theorem B2960285 : Blo 2159435 2960285 := bbase (se 3 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 2960285 = 1110107) (by norm_num)
theorem B7894093 : Blo 2159435 7894093 := bstep (se 3 (by rfl) ⟨1480142, by rfl⟩ : syracuseStep 7894093 = 2960285) B2960285
theorem B10525457 : Blo 2159435 10525457 := bstep (se 2 (by rfl) ⟨3947046, by rfl⟩ : syracuseStep 10525457 = 7894093) B7894093
theorem B7016971 : Blo 2159435 7016971 := bstep (se 1 (by rfl) ⟨5262728, by rfl⟩ : syracuseStep 7016971 = 10525457) B10525457
theorem B9355961 : Blo 2159435 9355961 := bstep (se 2 (by rfl) ⟨3508485, by rfl⟩ : syracuseStep 9355961 = 7016971) B7016971
theorem B6237307 : Blo 2159435 6237307 := bstep (se 1 (by rfl) ⟨4677980, by rfl⟩ : syracuseStep 6237307 = 9355961) B9355961
theorem B33265637 : Blo 2159435 33265637 := bstep (se 4 (by rfl) ⟨3118653, by rfl⟩ : syracuseStep 33265637 = 6237307) B6237307
theorem B22177091 : Blo 2159435 22177091 := bstep (se 1 (by rfl) ⟨16632818, by rfl⟩ : syracuseStep 22177091 = 33265637) B33265637
theorem B59138909 : Blo 2159435 59138909 := bstep (se 3 (by rfl) ⟨11088545, by rfl⟩ : syracuseStep 59138909 = 22177091) B22177091
theorem B39425939 : Blo 2159435 39425939 := bstep (se 1 (by rfl) ⟨29569454, by rfl⟩ : syracuseStep 39425939 = 59138909) B59138909
theorem B26283959 : Blo 2159435 26283959 := bstep (se 1 (by rfl) ⟨19712969, by rfl⟩ : syracuseStep 26283959 = 39425939) B39425939
theorem B17522639 : Blo 2159435 17522639 := bstep (se 1 (by rfl) ⟨13141979, by rfl⟩ : syracuseStep 17522639 = 26283959) B26283959
theorem B11681759 : Blo 2159435 11681759 := bstep (se 1 (by rfl) ⟨8761319, by rfl⟩ : syracuseStep 11681759 = 17522639) B17522639
theorem B7787839 : Blo 2159435 7787839 := bstep (se 1 (by rfl) ⟨5840879, by rfl⟩ : syracuseStep 7787839 = 11681759) B11681759
theorem B10383785 : Blo 2159435 10383785 := bstep (se 2 (by rfl) ⟨3893919, by rfl⟩ : syracuseStep 10383785 = 7787839) B7787839
theorem B6922523 : Blo 2159435 6922523 := bstep (se 1 (by rfl) ⟨5191892, by rfl⟩ : syracuseStep 6922523 = 10383785) B10383785
theorem B4615015 : Blo 2159435 4615015 := bstep (se 1 (by rfl) ⟨3461261, by rfl⟩ : syracuseStep 4615015 = 6922523) B6922523
theorem B6153353 : Blo 2159435 6153353 := bstep (se 2 (by rfl) ⟨2307507, by rfl⟩ : syracuseStep 6153353 = 4615015) B4615015
theorem B4102235 : Blo 2159435 4102235 := bstep (se 1 (by rfl) ⟨3076676, by rfl⟩ : syracuseStep 4102235 = 6153353) B6153353
theorem B2734823 : Blo 2159435 2734823 := bstep (se 1 (by rfl) ⟨2051117, by rfl⟩ : syracuseStep 2734823 = 4102235) B4102235
theorem B7292861 : Blo 2159435 7292861 := bstep (se 3 (by rfl) ⟨1367411, by rfl⟩ : syracuseStep 7292861 = 2734823) B2734823
theorem B4861907 : Blo 2159435 4861907 := bstep (se 1 (by rfl) ⟨3646430, by rfl⟩ : syracuseStep 4861907 = 7292861) B7292861
theorem B3241271 : Blo 2159435 3241271 := bstep (se 1 (by rfl) ⟨2430953, by rfl⟩ : syracuseStep 3241271 = 4861907) B4861907
theorem B2160847 : Blo 2159435 2160847 := bstep (se 1 (by rfl) ⟨1620635, by rfl⟩ : syracuseStep 2160847 = 3241271) B3241271
theorem B3241277 : Blo 2159435 3241277 := bbase (se 3 (by rfl) ⟨607739, by rfl⟩ : syracuseStep 3241277 = 1215479) (by norm_num)
theorem B2160851 : Blo 2159435 2160851 := bstep (se 1 (by rfl) ⟨1620638, by rfl⟩ : syracuseStep 2160851 = 3241277) B3241277
theorem B4861925 : Blo 2159435 4861925 := bbase (se 4 (by rfl) ⟨455805, by rfl⟩ : syracuseStep 4861925 = 911611) (by norm_num)
theorem B3241283 : Blo 2159435 3241283 := bstep (se 1 (by rfl) ⟨2430962, by rfl⟩ : syracuseStep 3241283 = 4861925) B4861925
theorem B2160855 : Blo 2159435 2160855 := bstep (se 1 (by rfl) ⟨1620641, by rfl⟩ : syracuseStep 2160855 = 3241283) B3241283
theorem B5469677 : Blo 2159435 5469677 := bbase (se 3 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 5469677 = 2051129) (by norm_num)
theorem B3646451 : Blo 2159435 3646451 := bstep (se 1 (by rfl) ⟨2734838, by rfl⟩ : syracuseStep 3646451 = 5469677) B5469677
theorem B2430967 : Blo 2159435 2430967 := bstep (se 1 (by rfl) ⟨1823225, by rfl⟩ : syracuseStep 2430967 = 3646451) B3646451
theorem B3241289 : Blo 2159435 3241289 := bstep (se 2 (by rfl) ⟨1215483, by rfl⟩ : syracuseStep 3241289 = 2430967) B2430967
theorem B2160859 : Blo 2159435 2160859 := bstep (se 1 (by rfl) ⟨1620644, by rfl⟩ : syracuseStep 2160859 = 3241289) B3241289
theorem B4562453 : Blo 2159435 4562453 := bbase (se 6 (by rfl) ⟨106932, by rfl⟩ : syracuseStep 4562453 = 213865) (by norm_num)
theorem B12166541 : Blo 2159435 12166541 := bstep (se 3 (by rfl) ⟨2281226, by rfl⟩ : syracuseStep 12166541 = 4562453) B4562453
theorem B8111027 : Blo 2159435 8111027 := bstep (se 1 (by rfl) ⟨6083270, by rfl⟩ : syracuseStep 8111027 = 12166541) B12166541
theorem B21629405 : Blo 2159435 21629405 := bstep (se 3 (by rfl) ⟨4055513, by rfl⟩ : syracuseStep 21629405 = 8111027) B8111027
theorem B14419603 : Blo 2159435 14419603 := bstep (se 1 (by rfl) ⟨10814702, by rfl⟩ : syracuseStep 14419603 = 21629405) B21629405
theorem B76904549 : Blo 2159435 76904549 := bstep (se 4 (by rfl) ⟨7209801, by rfl⟩ : syracuseStep 76904549 = 14419603) B14419603
theorem B51269699 : Blo 2159435 51269699 := bstep (se 1 (by rfl) ⟨38452274, by rfl⟩ : syracuseStep 51269699 = 76904549) B76904549
theorem B136719197 : Blo 2159435 136719197 := bstep (se 3 (by rfl) ⟨25634849, by rfl⟩ : syracuseStep 136719197 = 51269699) B51269699
theorem B91146131 : Blo 2159435 91146131 := bstep (se 1 (by rfl) ⟨68359598, by rfl⟩ : syracuseStep 91146131 = 136719197) B136719197
theorem B60764087 : Blo 2159435 60764087 := bstep (se 1 (by rfl) ⟨45573065, by rfl⟩ : syracuseStep 60764087 = 91146131) B91146131
theorem B40509391 : Blo 2159435 40509391 := bstep (se 1 (by rfl) ⟨30382043, by rfl⟩ : syracuseStep 40509391 = 60764087) B60764087
theorem B54012521 : Blo 2159435 54012521 := bstep (se 2 (by rfl) ⟨20254695, by rfl⟩ : syracuseStep 54012521 = 40509391) B40509391
theorem B36008347 : Blo 2159435 36008347 := bstep (se 1 (by rfl) ⟨27006260, by rfl⟩ : syracuseStep 36008347 = 54012521) B54012521
theorem B48011129 : Blo 2159435 48011129 := bstep (se 2 (by rfl) ⟨18004173, by rfl⟩ : syracuseStep 48011129 = 36008347) B36008347
theorem B32007419 : Blo 2159435 32007419 := bstep (se 1 (by rfl) ⟨24005564, by rfl⟩ : syracuseStep 32007419 = 48011129) B48011129
theorem B21338279 : Blo 2159435 21338279 := bstep (se 1 (by rfl) ⟨16003709, by rfl⟩ : syracuseStep 21338279 = 32007419) B32007419
theorem B14225519 : Blo 2159435 14225519 := bstep (se 1 (by rfl) ⟨10669139, by rfl⟩ : syracuseStep 14225519 = 21338279) B21338279
theorem B9483679 : Blo 2159435 9483679 := bstep (se 1 (by rfl) ⟨7112759, by rfl⟩ : syracuseStep 9483679 = 14225519) B14225519
theorem B50579621 : Blo 2159435 50579621 := bstep (se 4 (by rfl) ⟨4741839, by rfl⟩ : syracuseStep 50579621 = 9483679) B9483679
theorem B33719747 : Blo 2159435 33719747 := bstep (se 1 (by rfl) ⟨25289810, by rfl⟩ : syracuseStep 33719747 = 50579621) B50579621
theorem B89919325 : Blo 2159435 89919325 := bstep (se 3 (by rfl) ⟨16859873, by rfl⟩ : syracuseStep 89919325 = 33719747) B33719747
theorem B479569733 : Blo 2159435 479569733 := bstep (se 4 (by rfl) ⟨44959662, by rfl⟩ : syracuseStep 479569733 = 89919325) B89919325
theorem B319713155 : Blo 2159435 319713155 := bstep (se 1 (by rfl) ⟨239784866, by rfl⟩ : syracuseStep 319713155 = 479569733) B479569733
theorem B213142103 : Blo 2159435 213142103 := bstep (se 1 (by rfl) ⟨159856577, by rfl⟩ : syracuseStep 213142103 = 319713155) B319713155
theorem B142094735 : Blo 2159435 142094735 := bstep (se 1 (by rfl) ⟨106571051, by rfl⟩ : syracuseStep 142094735 = 213142103) B213142103
theorem B94729823 : Blo 2159435 94729823 := bstep (se 1 (by rfl) ⟨71047367, by rfl⟩ : syracuseStep 94729823 = 142094735) B142094735
theorem B63153215 : Blo 2159435 63153215 := bstep (se 1 (by rfl) ⟨47364911, by rfl⟩ : syracuseStep 63153215 = 94729823) B94729823
theorem B42102143 : Blo 2159435 42102143 := bstep (se 1 (by rfl) ⟨31576607, by rfl⟩ : syracuseStep 42102143 = 63153215) B63153215
theorem B28068095 : Blo 2159435 28068095 := bstep (se 1 (by rfl) ⟨21051071, by rfl⟩ : syracuseStep 28068095 = 42102143) B42102143
theorem B18712063 : Blo 2159435 18712063 := bstep (se 1 (by rfl) ⟨14034047, by rfl⟩ : syracuseStep 18712063 = 28068095) B28068095
theorem B24949417 : Blo 2159435 24949417 := bstep (se 2 (by rfl) ⟨9356031, by rfl⟩ : syracuseStep 24949417 = 18712063) B18712063
theorem B33265889 : Blo 2159435 33265889 := bstep (se 2 (by rfl) ⟨12474708, by rfl⟩ : syracuseStep 33265889 = 24949417) B24949417
theorem B22177259 : Blo 2159435 22177259 := bstep (se 1 (by rfl) ⟨16632944, by rfl⟩ : syracuseStep 22177259 = 33265889) B33265889
theorem B14784839 : Blo 2159435 14784839 := bstep (se 1 (by rfl) ⟨11088629, by rfl⟩ : syracuseStep 14784839 = 22177259) B22177259
theorem B9856559 : Blo 2159435 9856559 := bstep (se 1 (by rfl) ⟨7392419, by rfl⟩ : syracuseStep 9856559 = 14784839) B14784839
theorem B6571039 : Blo 2159435 6571039 := bstep (se 1 (by rfl) ⟨4928279, by rfl⟩ : syracuseStep 6571039 = 9856559) B9856559
theorem B8761385 : Blo 2159435 8761385 := bstep (se 2 (by rfl) ⟨3285519, by rfl⟩ : syracuseStep 8761385 = 6571039) B6571039
theorem B5840923 : Blo 2159435 5840923 := bstep (se 1 (by rfl) ⟨4380692, by rfl⟩ : syracuseStep 5840923 = 8761385) B8761385
theorem B7787897 : Blo 2159435 7787897 := bstep (se 2 (by rfl) ⟨2920461, by rfl⟩ : syracuseStep 7787897 = 5840923) B5840923
theorem B5191931 : Blo 2159435 5191931 := bstep (se 1 (by rfl) ⟨3893948, by rfl⟩ : syracuseStep 5191931 = 7787897) B7787897
theorem B3461287 : Blo 2159435 3461287 := bstep (se 1 (by rfl) ⟨2595965, by rfl⟩ : syracuseStep 3461287 = 5191931) B5191931
theorem B4615049 : Blo 2159435 4615049 := bstep (se 2 (by rfl) ⟨1730643, by rfl⟩ : syracuseStep 4615049 = 3461287) B3461287
theorem B3076699 : Blo 2159435 3076699 := bstep (se 1 (by rfl) ⟨2307524, by rfl⟩ : syracuseStep 3076699 = 4615049) B4615049
theorem B4102265 : Blo 2159435 4102265 := bstep (se 2 (by rfl) ⟨1538349, by rfl⟩ : syracuseStep 4102265 = 3076699) B3076699
theorem B10939373 : Blo 2159435 10939373 := bstep (se 3 (by rfl) ⟨2051132, by rfl⟩ : syracuseStep 10939373 = 4102265) B4102265
theorem B7292915 : Blo 2159435 7292915 := bstep (se 1 (by rfl) ⟨5469686, by rfl⟩ : syracuseStep 7292915 = 10939373) B10939373
theorem B4861943 : Blo 2159435 4861943 := bstep (se 1 (by rfl) ⟨3646457, by rfl⟩ : syracuseStep 4861943 = 7292915) B7292915
theorem B3241295 : Blo 2159435 3241295 := bstep (se 1 (by rfl) ⟨2430971, by rfl⟩ : syracuseStep 3241295 = 4861943) B4861943
theorem B2160863 : Blo 2159435 2160863 := bstep (se 1 (by rfl) ⟨1620647, by rfl⟩ : syracuseStep 2160863 = 3241295) B3241295
theorem B3241301 : Blo 2159435 3241301 := bbase (se 13 (by rfl) ⟨593, by rfl⟩ : syracuseStep 3241301 = 1187) (by norm_num)
theorem B2160867 : Blo 2159435 2160867 := bstep (se 1 (by rfl) ⟨1620650, by rfl⟩ : syracuseStep 2160867 = 3241301) B3241301
theorem B2307533 : Blo 2159435 2307533 := bbase (se 3 (by rfl) ⟨432662, by rfl⟩ : syracuseStep 2307533 = 865325) (by norm_num)
theorem B6153421 : Blo 2159435 6153421 := bstep (se 3 (by rfl) ⟨1153766, by rfl⟩ : syracuseStep 6153421 = 2307533) B2307533
theorem B8204561 : Blo 2159435 8204561 := bstep (se 2 (by rfl) ⟨3076710, by rfl⟩ : syracuseStep 8204561 = 6153421) B6153421
theorem B5469707 : Blo 2159435 5469707 := bstep (se 1 (by rfl) ⟨4102280, by rfl⟩ : syracuseStep 5469707 = 8204561) B8204561
theorem B3646471 : Blo 2159435 3646471 := bstep (se 1 (by rfl) ⟨2734853, by rfl⟩ : syracuseStep 3646471 = 5469707) B5469707
theorem B4861961 : Blo 2159435 4861961 := bstep (se 2 (by rfl) ⟨1823235, by rfl⟩ : syracuseStep 4861961 = 3646471) B3646471
theorem B3241307 : Blo 2159435 3241307 := bstep (se 1 (by rfl) ⟨2430980, by rfl⟩ : syracuseStep 3241307 = 4861961) B4861961
theorem B2160871 : Blo 2159435 2160871 := bstep (se 1 (by rfl) ⟨1620653, by rfl⟩ : syracuseStep 2160871 = 3241307) B3241307
theorem B2430985 : Blo 2159435 2430985 := bbase (se 2 (by rfl) ⟨911619, by rfl⟩ : syracuseStep 2430985 = 1823239) (by norm_num)
theorem B3241313 : Blo 2159435 3241313 := bstep (se 2 (by rfl) ⟨1215492, by rfl⟩ : syracuseStep 3241313 = 2430985) B2430985
theorem B2160875 : Blo 2159435 2160875 := bstep (se 1 (by rfl) ⟨1620656, by rfl⟩ : syracuseStep 2160875 = 3241313) B3241313
theorem B5262805 : Blo 2159435 5262805 := bbase (se 7 (by rfl) ⟨61673, by rfl⟩ : syracuseStep 5262805 = 123347) (by norm_num)
theorem B7017073 : Blo 2159435 7017073 := bstep (se 2 (by rfl) ⟨2631402, by rfl⟩ : syracuseStep 7017073 = 5262805) B5262805
theorem B37424389 : Blo 2159435 37424389 := bstep (se 4 (by rfl) ⟨3508536, by rfl⟩ : syracuseStep 37424389 = 7017073) B7017073
theorem B49899185 : Blo 2159435 49899185 := bstep (se 2 (by rfl) ⟨18712194, by rfl⟩ : syracuseStep 49899185 = 37424389) B37424389
theorem B33266123 : Blo 2159435 33266123 := bstep (se 1 (by rfl) ⟨24949592, by rfl⟩ : syracuseStep 33266123 = 49899185) B49899185
theorem B22177415 : Blo 2159435 22177415 := bstep (se 1 (by rfl) ⟨16633061, by rfl⟩ : syracuseStep 22177415 = 33266123) B33266123
theorem B14784943 : Blo 2159435 14784943 := bstep (se 1 (by rfl) ⟨11088707, by rfl⟩ : syracuseStep 14784943 = 22177415) B22177415
theorem B19713257 : Blo 2159435 19713257 := bstep (se 2 (by rfl) ⟨7392471, by rfl⟩ : syracuseStep 19713257 = 14784943) B14784943
theorem B13142171 : Blo 2159435 13142171 := bstep (se 1 (by rfl) ⟨9856628, by rfl⟩ : syracuseStep 13142171 = 19713257) B19713257
theorem B8761447 : Blo 2159435 8761447 := bstep (se 1 (by rfl) ⟨6571085, by rfl⟩ : syracuseStep 8761447 = 13142171) B13142171
theorem B11681929 : Blo 2159435 11681929 := bstep (se 2 (by rfl) ⟨4380723, by rfl⟩ : syracuseStep 11681929 = 8761447) B8761447
theorem B15575905 : Blo 2159435 15575905 := bstep (se 2 (by rfl) ⟨5840964, by rfl⟩ : syracuseStep 15575905 = 11681929) B11681929
theorem B20767873 : Blo 2159435 20767873 := bstep (se 2 (by rfl) ⟨7787952, by rfl⟩ : syracuseStep 20767873 = 15575905) B15575905
theorem B27690497 : Blo 2159435 27690497 := bstep (se 2 (by rfl) ⟨10383936, by rfl⟩ : syracuseStep 27690497 = 20767873) B20767873
theorem B18460331 : Blo 2159435 18460331 := bstep (se 1 (by rfl) ⟨13845248, by rfl⟩ : syracuseStep 18460331 = 27690497) B27690497
theorem B12306887 : Blo 2159435 12306887 := bstep (se 1 (by rfl) ⟨9230165, by rfl⟩ : syracuseStep 12306887 = 18460331) B18460331
theorem B8204591 : Blo 2159435 8204591 := bstep (se 1 (by rfl) ⟨6153443, by rfl⟩ : syracuseStep 8204591 = 12306887) B12306887
theorem B5469727 : Blo 2159435 5469727 := bstep (se 1 (by rfl) ⟨4102295, by rfl⟩ : syracuseStep 5469727 = 8204591) B8204591
theorem B7292969 : Blo 2159435 7292969 := bstep (se 2 (by rfl) ⟨2734863, by rfl⟩ : syracuseStep 7292969 = 5469727) B5469727
theorem B4861979 : Blo 2159435 4861979 := bstep (se 1 (by rfl) ⟨3646484, by rfl⟩ : syracuseStep 4861979 = 7292969) B7292969
theorem B3241319 : Blo 2159435 3241319 := bstep (se 1 (by rfl) ⟨2430989, by rfl⟩ : syracuseStep 3241319 = 4861979) B4861979
theorem B2160879 : Blo 2159435 2160879 := bstep (se 1 (by rfl) ⟨1620659, by rfl⟩ : syracuseStep 2160879 = 3241319) B3241319
theorem B3241325 : Blo 2159435 3241325 := bbase (se 3 (by rfl) ⟨607748, by rfl⟩ : syracuseStep 3241325 = 1215497) (by norm_num)
theorem B2160883 : Blo 2159435 2160883 := bstep (se 1 (by rfl) ⟨1620662, by rfl⟩ : syracuseStep 2160883 = 3241325) B3241325
theorem B4861997 : Blo 2159435 4861997 := bbase (se 3 (by rfl) ⟨911624, by rfl⟩ : syracuseStep 4861997 = 1823249) (by norm_num)
theorem B3241331 : Blo 2159435 3241331 := bstep (se 1 (by rfl) ⟨2430998, by rfl⟩ : syracuseStep 3241331 = 4861997) B4861997
theorem B2160887 : Blo 2159435 2160887 := bstep (se 1 (by rfl) ⟨1620665, by rfl⟩ : syracuseStep 2160887 = 3241331) B3241331
theorem B27748565 : Blo 2159435 27748565 := bbase (se 7 (by rfl) ⟨325178, by rfl⟩ : syracuseStep 27748565 = 650357) (by norm_num)
theorem B18499043 : Blo 2159435 18499043 := bstep (se 1 (by rfl) ⟨13874282, by rfl⟩ : syracuseStep 18499043 = 27748565) B27748565
theorem B12332695 : Blo 2159435 12332695 := bstep (se 1 (by rfl) ⟨9249521, by rfl⟩ : syracuseStep 12332695 = 18499043) B18499043
theorem B16443593 : Blo 2159435 16443593 := bstep (se 2 (by rfl) ⟨6166347, by rfl⟩ : syracuseStep 16443593 = 12332695) B12332695
theorem B10962395 : Blo 2159435 10962395 := bstep (se 1 (by rfl) ⟨8221796, by rfl⟩ : syracuseStep 10962395 = 16443593) B16443593
theorem B7308263 : Blo 2159435 7308263 := bstep (se 1 (by rfl) ⟨5481197, by rfl⟩ : syracuseStep 7308263 = 10962395) B10962395
theorem B19488701 : Blo 2159435 19488701 := bstep (se 3 (by rfl) ⟨3654131, by rfl⟩ : syracuseStep 19488701 = 7308263) B7308263
theorem B12992467 : Blo 2159435 12992467 := bstep (se 1 (by rfl) ⟨9744350, by rfl⟩ : syracuseStep 12992467 = 19488701) B19488701
theorem B17323289 : Blo 2159435 17323289 := bstep (se 2 (by rfl) ⟨6496233, by rfl⟩ : syracuseStep 17323289 = 12992467) B12992467
theorem B11548859 : Blo 2159435 11548859 := bstep (se 1 (by rfl) ⟨8661644, by rfl⟩ : syracuseStep 11548859 = 17323289) B17323289
theorem B30796957 : Blo 2159435 30796957 := bstep (se 3 (by rfl) ⟨5774429, by rfl⟩ : syracuseStep 30796957 = 11548859) B11548859
theorem B41062609 : Blo 2159435 41062609 := bstep (se 2 (by rfl) ⟨15398478, by rfl⟩ : syracuseStep 41062609 = 30796957) B30796957
theorem B219000581 : Blo 2159435 219000581 := bstep (se 4 (by rfl) ⟨20531304, by rfl⟩ : syracuseStep 219000581 = 41062609) B41062609
theorem B146000387 : Blo 2159435 146000387 := bstep (se 1 (by rfl) ⟨109500290, by rfl⟩ : syracuseStep 146000387 = 219000581) B219000581
theorem B97333591 : Blo 2159435 97333591 := bstep (se 1 (by rfl) ⟨73000193, by rfl⟩ : syracuseStep 97333591 = 146000387) B146000387
theorem B129778121 : Blo 2159435 129778121 := bstep (se 2 (by rfl) ⟨48666795, by rfl⟩ : syracuseStep 129778121 = 97333591) B97333591
theorem B86518747 : Blo 2159435 86518747 := bstep (se 1 (by rfl) ⟨64889060, by rfl⟩ : syracuseStep 86518747 = 129778121) B129778121
theorem B115358329 : Blo 2159435 115358329 := bstep (se 2 (by rfl) ⟨43259373, by rfl⟩ : syracuseStep 115358329 = 86518747) B86518747
theorem B153811105 : Blo 2159435 153811105 := bstep (se 2 (by rfl) ⟨57679164, by rfl⟩ : syracuseStep 153811105 = 115358329) B115358329
theorem B820325893 : Blo 2159435 820325893 := bstep (se 4 (by rfl) ⟨76905552, by rfl⟩ : syracuseStep 820325893 = 153811105) B153811105
theorem B1093767857 : Blo 2159435 1093767857 := bstep (se 2 (by rfl) ⟨410162946, by rfl⟩ : syracuseStep 1093767857 = 820325893) B820325893
theorem B729178571 : Blo 2159435 729178571 := bstep (se 1 (by rfl) ⟨546883928, by rfl⟩ : syracuseStep 729178571 = 1093767857) B1093767857
theorem B1944476189 : Blo 2159435 1944476189 := bstep (se 3 (by rfl) ⟨364589285, by rfl⟩ : syracuseStep 1944476189 = 729178571) B729178571
theorem B1296317459 : Blo 2159435 1296317459 := bstep (se 1 (by rfl) ⟨972238094, by rfl⟩ : syracuseStep 1296317459 = 1944476189) B1944476189
theorem B864211639 : Blo 2159435 864211639 := bstep (se 1 (by rfl) ⟨648158729, by rfl⟩ : syracuseStep 864211639 = 1296317459) B1296317459
theorem B1152282185 : Blo 2159435 1152282185 := bstep (se 2 (by rfl) ⟨432105819, by rfl⟩ : syracuseStep 1152282185 = 864211639) B864211639
theorem B768188123 : Blo 2159435 768188123 := bstep (se 1 (by rfl) ⟨576141092, by rfl⟩ : syracuseStep 768188123 = 1152282185) B1152282185
theorem B512125415 : Blo 2159435 512125415 := bstep (se 1 (by rfl) ⟨384094061, by rfl⟩ : syracuseStep 512125415 = 768188123) B768188123
theorem B341416943 : Blo 2159435 341416943 := bstep (se 1 (by rfl) ⟨256062707, by rfl⟩ : syracuseStep 341416943 = 512125415) B512125415
theorem B227611295 : Blo 2159435 227611295 := bstep (se 1 (by rfl) ⟨170708471, by rfl⟩ : syracuseStep 227611295 = 341416943) B341416943
theorem B151740863 : Blo 2159435 151740863 := bstep (se 1 (by rfl) ⟨113805647, by rfl⟩ : syracuseStep 151740863 = 227611295) B227611295
theorem B101160575 : Blo 2159435 101160575 := bstep (se 1 (by rfl) ⟨75870431, by rfl⟩ : syracuseStep 101160575 = 151740863) B151740863
theorem B67440383 : Blo 2159435 67440383 := bstep (se 1 (by rfl) ⟨50580287, by rfl⟩ : syracuseStep 67440383 = 101160575) B101160575
theorem B44960255 : Blo 2159435 44960255 := bstep (se 1 (by rfl) ⟨33720191, by rfl⟩ : syracuseStep 44960255 = 67440383) B67440383
theorem B29973503 : Blo 2159435 29973503 := bstep (se 1 (by rfl) ⟨22480127, by rfl⟩ : syracuseStep 29973503 = 44960255) B44960255
theorem B19982335 : Blo 2159435 19982335 := bstep (se 1 (by rfl) ⟨14986751, by rfl⟩ : syracuseStep 19982335 = 29973503) B29973503
theorem B26643113 : Blo 2159435 26643113 := bstep (se 2 (by rfl) ⟨9991167, by rfl⟩ : syracuseStep 26643113 = 19982335) B19982335
theorem B17762075 : Blo 2159435 17762075 := bstep (se 1 (by rfl) ⟨13321556, by rfl⟩ : syracuseStep 17762075 = 26643113) B26643113
theorem B11841383 : Blo 2159435 11841383 := bstep (se 1 (by rfl) ⟨8881037, by rfl⟩ : syracuseStep 11841383 = 17762075) B17762075
theorem B7894255 : Blo 2159435 7894255 := bstep (se 1 (by rfl) ⟨5920691, by rfl⟩ : syracuseStep 7894255 = 11841383) B11841383
theorem B10525673 : Blo 2159435 10525673 := bstep (se 2 (by rfl) ⟨3947127, by rfl⟩ : syracuseStep 10525673 = 7894255) B7894255
theorem B7017115 : Blo 2159435 7017115 := bstep (se 1 (by rfl) ⟨5262836, by rfl⟩ : syracuseStep 7017115 = 10525673) B10525673
theorem B9356153 : Blo 2159435 9356153 := bstep (se 2 (by rfl) ⟨3508557, by rfl⟩ : syracuseStep 9356153 = 7017115) B7017115
theorem B24949741 : Blo 2159435 24949741 := bstep (se 3 (by rfl) ⟨4678076, by rfl⟩ : syracuseStep 24949741 = 9356153) B9356153
theorem B33266321 : Blo 2159435 33266321 := bstep (se 2 (by rfl) ⟨12474870, by rfl⟩ : syracuseStep 33266321 = 24949741) B24949741
theorem B22177547 : Blo 2159435 22177547 := bstep (se 1 (by rfl) ⟨16633160, by rfl⟩ : syracuseStep 22177547 = 33266321) B33266321
theorem B14785031 : Blo 2159435 14785031 := bstep (se 1 (by rfl) ⟨11088773, by rfl⟩ : syracuseStep 14785031 = 22177547) B22177547
theorem B9856687 : Blo 2159435 9856687 := bstep (se 1 (by rfl) ⟨7392515, by rfl⟩ : syracuseStep 9856687 = 14785031) B14785031
theorem B13142249 : Blo 2159435 13142249 := bstep (se 2 (by rfl) ⟨4928343, by rfl⟩ : syracuseStep 13142249 = 9856687) B9856687
theorem B8761499 : Blo 2159435 8761499 := bstep (se 1 (by rfl) ⟨6571124, by rfl⟩ : syracuseStep 8761499 = 13142249) B13142249
theorem B5840999 : Blo 2159435 5840999 := bstep (se 1 (by rfl) ⟨4380749, by rfl⟩ : syracuseStep 5840999 = 8761499) B8761499
theorem B3893999 : Blo 2159435 3893999 := bstep (se 1 (by rfl) ⟨2920499, by rfl⟩ : syracuseStep 3893999 = 5840999) B5840999
theorem B10383997 : Blo 2159435 10383997 := bstep (se 3 (by rfl) ⟨1946999, by rfl⟩ : syracuseStep 10383997 = 3893999) B3893999
theorem B13845329 : Blo 2159435 13845329 := bstep (se 2 (by rfl) ⟨5191998, by rfl⟩ : syracuseStep 13845329 = 10383997) B10383997
theorem B9230219 : Blo 2159435 9230219 := bstep (se 1 (by rfl) ⟨6922664, by rfl⟩ : syracuseStep 9230219 = 13845329) B13845329
theorem B6153479 : Blo 2159435 6153479 := bstep (se 1 (by rfl) ⟨4615109, by rfl⟩ : syracuseStep 6153479 = 9230219) B9230219
theorem B4102319 : Blo 2159435 4102319 := bstep (se 1 (by rfl) ⟨3076739, by rfl⟩ : syracuseStep 4102319 = 6153479) B6153479
theorem B2734879 : Blo 2159435 2734879 := bstep (se 1 (by rfl) ⟨2051159, by rfl⟩ : syracuseStep 2734879 = 4102319) B4102319
theorem B3646505 : Blo 2159435 3646505 := bstep (se 2 (by rfl) ⟨1367439, by rfl⟩ : syracuseStep 3646505 = 2734879) B2734879
theorem B2431003 : Blo 2159435 2431003 := bstep (se 1 (by rfl) ⟨1823252, by rfl⟩ : syracuseStep 2431003 = 3646505) B3646505
theorem B3241337 : Blo 2159435 3241337 := bstep (se 2 (by rfl) ⟨1215501, by rfl⟩ : syracuseStep 3241337 = 2431003) B2431003
theorem B2160891 : Blo 2159435 2160891 := bstep (se 1 (by rfl) ⟨1620668, by rfl⟩ : syracuseStep 2160891 = 3241337) B3241337
theorem B3894005 : Blo 2159435 3894005 := bbase (se 5 (by rfl) ⟨182531, by rfl⟩ : syracuseStep 3894005 = 365063) (by norm_num)
theorem B10384013 : Blo 2159435 10384013 := bstep (se 3 (by rfl) ⟨1947002, by rfl⟩ : syracuseStep 10384013 = 3894005) B3894005
theorem B6922675 : Blo 2159435 6922675 := bstep (se 1 (by rfl) ⟨5192006, by rfl⟩ : syracuseStep 6922675 = 10384013) B10384013
theorem B36920933 : Blo 2159435 36920933 := bstep (se 4 (by rfl) ⟨3461337, by rfl⟩ : syracuseStep 36920933 = 6922675) B6922675
theorem B24613955 : Blo 2159435 24613955 := bstep (se 1 (by rfl) ⟨18460466, by rfl⟩ : syracuseStep 24613955 = 36920933) B36920933
theorem B16409303 : Blo 2159435 16409303 := bstep (se 1 (by rfl) ⟨12306977, by rfl⟩ : syracuseStep 16409303 = 24613955) B24613955
theorem B10939535 : Blo 2159435 10939535 := bstep (se 1 (by rfl) ⟨8204651, by rfl⟩ : syracuseStep 10939535 = 16409303) B16409303
theorem B7293023 : Blo 2159435 7293023 := bstep (se 1 (by rfl) ⟨5469767, by rfl⟩ : syracuseStep 7293023 = 10939535) B10939535
theorem B4862015 : Blo 2159435 4862015 := bstep (se 1 (by rfl) ⟨3646511, by rfl⟩ : syracuseStep 4862015 = 7293023) B7293023
theorem B3241343 : Blo 2159435 3241343 := bstep (se 1 (by rfl) ⟨2431007, by rfl⟩ : syracuseStep 3241343 = 4862015) B4862015
theorem B2160895 : Blo 2159435 2160895 := bstep (se 1 (by rfl) ⟨1620671, by rfl⟩ : syracuseStep 2160895 = 3241343) B3241343
theorem B3241349 : Blo 2159435 3241349 := bbase (se 4 (by rfl) ⟨303876, by rfl⟩ : syracuseStep 3241349 = 607753) (by norm_num)
theorem B2160899 : Blo 2159435 2160899 := bstep (se 1 (by rfl) ⟨1620674, by rfl⟩ : syracuseStep 2160899 = 3241349) B3241349
theorem B3646525 : Blo 2159435 3646525 := bbase (se 3 (by rfl) ⟨683723, by rfl⟩ : syracuseStep 3646525 = 1367447) (by norm_num)
theorem B4862033 : Blo 2159435 4862033 := bstep (se 2 (by rfl) ⟨1823262, by rfl⟩ : syracuseStep 4862033 = 3646525) B3646525
theorem B3241355 : Blo 2159435 3241355 := bstep (se 1 (by rfl) ⟨2431016, by rfl⟩ : syracuseStep 3241355 = 4862033) B4862033
theorem B2160903 : Blo 2159435 2160903 := bstep (se 1 (by rfl) ⟨1620677, by rfl⟩ : syracuseStep 2160903 = 3241355) B3241355
theorem B2431021 : Blo 2159435 2431021 := bbase (se 3 (by rfl) ⟨455816, by rfl⟩ : syracuseStep 2431021 = 911633) (by norm_num)
theorem B3241361 : Blo 2159435 3241361 := bstep (se 2 (by rfl) ⟨1215510, by rfl⟩ : syracuseStep 3241361 = 2431021) B2431021
theorem B2160907 : Blo 2159435 2160907 := bstep (se 1 (by rfl) ⟨1620680, by rfl⟩ : syracuseStep 2160907 = 3241361) B3241361
theorem B7293077 : Blo 2159435 7293077 := bbase (se 6 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 7293077 = 341863) (by norm_num)
theorem B4862051 : Blo 2159435 4862051 := bstep (se 1 (by rfl) ⟨3646538, by rfl⟩ : syracuseStep 4862051 = 7293077) B7293077
theorem B3241367 : Blo 2159435 3241367 := bstep (se 1 (by rfl) ⟨2431025, by rfl⟩ : syracuseStep 3241367 = 4862051) B4862051
theorem B2160911 : Blo 2159435 2160911 := bstep (se 1 (by rfl) ⟨1620683, by rfl⟩ : syracuseStep 2160911 = 3241367) B3241367
theorem B3241373 : Blo 2159435 3241373 := bbase (se 3 (by rfl) ⟨607757, by rfl⟩ : syracuseStep 3241373 = 1215515) (by norm_num)
theorem B2160915 : Blo 2159435 2160915 := bstep (se 1 (by rfl) ⟨1620686, by rfl⟩ : syracuseStep 2160915 = 3241373) B3241373
theorem B4862069 : Blo 2159435 4862069 := bbase (se 5 (by rfl) ⟨227909, by rfl⟩ : syracuseStep 4862069 = 455819) (by norm_num)
theorem B3241379 : Blo 2159435 3241379 := bstep (se 1 (by rfl) ⟨2431034, by rfl⟩ : syracuseStep 3241379 = 4862069) B4862069
theorem B2160919 : Blo 2159435 2160919 := bstep (se 1 (by rfl) ⟨1620689, by rfl⟩ : syracuseStep 2160919 = 3241379) B3241379
theorem B3118765 : Blo 2159435 3118765 := bbase (se 3 (by rfl) ⟨584768, by rfl⟩ : syracuseStep 3118765 = 1169537) (by norm_num)
theorem B4158353 : Blo 2159435 4158353 := bstep (se 2 (by rfl) ⟨1559382, by rfl⟩ : syracuseStep 4158353 = 3118765) B3118765
theorem B2772235 : Blo 2159435 2772235 := bstep (se 1 (by rfl) ⟨2079176, by rfl⟩ : syracuseStep 2772235 = 4158353) B4158353
theorem B3696313 : Blo 2159435 3696313 := bstep (se 2 (by rfl) ⟨1386117, by rfl⟩ : syracuseStep 3696313 = 2772235) B2772235
theorem B4928417 : Blo 2159435 4928417 := bstep (se 2 (by rfl) ⟨1848156, by rfl⟩ : syracuseStep 4928417 = 3696313) B3696313
theorem B3285611 : Blo 2159435 3285611 := bstep (se 1 (by rfl) ⟨2464208, by rfl⟩ : syracuseStep 3285611 = 4928417) B4928417
theorem B2190407 : Blo 2159435 2190407 := bstep (se 1 (by rfl) ⟨1642805, by rfl⟩ : syracuseStep 2190407 = 3285611) B3285611
theorem B5841085 : Blo 2159435 5841085 := bstep (se 3 (by rfl) ⟨1095203, by rfl⟩ : syracuseStep 5841085 = 2190407) B2190407
theorem B7788113 : Blo 2159435 7788113 := bstep (se 2 (by rfl) ⟨2920542, by rfl⟩ : syracuseStep 7788113 = 5841085) B5841085
theorem B5192075 : Blo 2159435 5192075 := bstep (se 1 (by rfl) ⟨3894056, by rfl⟩ : syracuseStep 5192075 = 7788113) B7788113
theorem B3461383 : Blo 2159435 3461383 := bstep (se 1 (by rfl) ⟨2596037, by rfl⟩ : syracuseStep 3461383 = 5192075) B5192075
theorem B18460709 : Blo 2159435 18460709 := bstep (se 4 (by rfl) ⟨1730691, by rfl⟩ : syracuseStep 18460709 = 3461383) B3461383
theorem B12307139 : Blo 2159435 12307139 := bstep (se 1 (by rfl) ⟨9230354, by rfl⟩ : syracuseStep 12307139 = 18460709) B18460709
theorem B8204759 : Blo 2159435 8204759 := bstep (se 1 (by rfl) ⟨6153569, by rfl⟩ : syracuseStep 8204759 = 12307139) B12307139
theorem B5469839 : Blo 2159435 5469839 := bstep (se 1 (by rfl) ⟨4102379, by rfl⟩ : syracuseStep 5469839 = 8204759) B8204759
theorem B3646559 : Blo 2159435 3646559 := bstep (se 1 (by rfl) ⟨2734919, by rfl⟩ : syracuseStep 3646559 = 5469839) B5469839
theorem B2431039 : Blo 2159435 2431039 := bstep (se 1 (by rfl) ⟨1823279, by rfl⟩ : syracuseStep 2431039 = 3646559) B3646559
theorem B3241385 : Blo 2159435 3241385 := bstep (se 2 (by rfl) ⟨1215519, by rfl⟩ : syracuseStep 3241385 = 2431039) B2431039
theorem B2160923 : Blo 2159435 2160923 := bstep (se 1 (by rfl) ⟨1620692, by rfl⟩ : syracuseStep 2160923 = 3241385) B3241385
theorem B8204773 : Blo 2159435 8204773 := bbase (se 4 (by rfl) ⟨769197, by rfl⟩ : syracuseStep 8204773 = 1538395) (by norm_num)
theorem B10939697 : Blo 2159435 10939697 := bstep (se 2 (by rfl) ⟨4102386, by rfl⟩ : syracuseStep 10939697 = 8204773) B8204773
theorem B7293131 : Blo 2159435 7293131 := bstep (se 1 (by rfl) ⟨5469848, by rfl⟩ : syracuseStep 7293131 = 10939697) B10939697
theorem B4862087 : Blo 2159435 4862087 := bstep (se 1 (by rfl) ⟨3646565, by rfl⟩ : syracuseStep 4862087 = 7293131) B7293131
theorem B3241391 : Blo 2159435 3241391 := bstep (se 1 (by rfl) ⟨2431043, by rfl⟩ : syracuseStep 3241391 = 4862087) B4862087
theorem B2160927 : Blo 2159435 2160927 := bstep (se 1 (by rfl) ⟨1620695, by rfl⟩ : syracuseStep 2160927 = 3241391) B3241391
theorem B3241397 : Blo 2159435 3241397 := bbase (se 5 (by rfl) ⟨151940, by rfl⟩ : syracuseStep 3241397 = 303881) (by norm_num)
theorem B2160931 : Blo 2159435 2160931 := bstep (se 1 (by rfl) ⟨1620698, by rfl⟩ : syracuseStep 2160931 = 3241397) B3241397
theorem B5469869 : Blo 2159435 5469869 := bbase (se 3 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 5469869 = 2051201) (by norm_num)
theorem B3646579 : Blo 2159435 3646579 := bstep (se 1 (by rfl) ⟨2734934, by rfl⟩ : syracuseStep 3646579 = 5469869) B5469869
theorem B4862105 : Blo 2159435 4862105 := bstep (se 2 (by rfl) ⟨1823289, by rfl⟩ : syracuseStep 4862105 = 3646579) B3646579
theorem B3241403 : Blo 2159435 3241403 := bstep (se 1 (by rfl) ⟨2431052, by rfl⟩ : syracuseStep 3241403 = 4862105) B4862105
theorem B2160935 : Blo 2159435 2160935 := bstep (se 1 (by rfl) ⟨1620701, by rfl⟩ : syracuseStep 2160935 = 3241403) B3241403
theorem B2431057 : Blo 2159435 2431057 := bbase (se 2 (by rfl) ⟨911646, by rfl⟩ : syracuseStep 2431057 = 1823293) (by norm_num)
theorem B3241409 : Blo 2159435 3241409 := bstep (se 2 (by rfl) ⟨1215528, by rfl⟩ : syracuseStep 3241409 = 2431057) B2431057
theorem B2160939 : Blo 2159435 2160939 := bstep (se 1 (by rfl) ⟨1620704, by rfl⟩ : syracuseStep 2160939 = 3241409) B3241409
theorem B3076813 : Blo 2159435 3076813 := bbase (se 3 (by rfl) ⟨576902, by rfl⟩ : syracuseStep 3076813 = 1153805) (by norm_num)
theorem B4102417 : Blo 2159435 4102417 := bstep (se 2 (by rfl) ⟨1538406, by rfl⟩ : syracuseStep 4102417 = 3076813) B3076813
theorem B5469889 : Blo 2159435 5469889 := bstep (se 2 (by rfl) ⟨2051208, by rfl⟩ : syracuseStep 5469889 = 4102417) B4102417
theorem B7293185 : Blo 2159435 7293185 := bstep (se 2 (by rfl) ⟨2734944, by rfl⟩ : syracuseStep 7293185 = 5469889) B5469889
theorem B4862123 : Blo 2159435 4862123 := bstep (se 1 (by rfl) ⟨3646592, by rfl⟩ : syracuseStep 4862123 = 7293185) B7293185
theorem B3241415 : Blo 2159435 3241415 := bstep (se 1 (by rfl) ⟨2431061, by rfl⟩ : syracuseStep 3241415 = 4862123) B4862123
theorem B2160943 : Blo 2159435 2160943 := bstep (se 1 (by rfl) ⟨1620707, by rfl⟩ : syracuseStep 2160943 = 3241415) B3241415
theorem B3241421 : Blo 2159435 3241421 := bbase (se 3 (by rfl) ⟨607766, by rfl⟩ : syracuseStep 3241421 = 1215533) (by norm_num)
theorem B2160947 : Blo 2159435 2160947 := bstep (se 1 (by rfl) ⟨1620710, by rfl⟩ : syracuseStep 2160947 = 3241421) B3241421
theorem B4862141 : Blo 2159435 4862141 := bbase (se 3 (by rfl) ⟨911651, by rfl⟩ : syracuseStep 4862141 = 1823303) (by norm_num)
theorem B3241427 : Blo 2159435 3241427 := bstep (se 1 (by rfl) ⟨2431070, by rfl⟩ : syracuseStep 3241427 = 4862141) B4862141
theorem B2160951 : Blo 2159435 2160951 := bstep (se 1 (by rfl) ⟨1620713, by rfl⟩ : syracuseStep 2160951 = 3241427) B3241427
theorem B3646613 : Blo 2159435 3646613 := bbase (se 6 (by rfl) ⟨85467, by rfl⟩ : syracuseStep 3646613 = 170935) (by norm_num)
theorem B2431075 : Blo 2159435 2431075 := bstep (se 1 (by rfl) ⟨1823306, by rfl⟩ : syracuseStep 2431075 = 3646613) B3646613
theorem B3241433 : Blo 2159435 3241433 := bstep (se 2 (by rfl) ⟨1215537, by rfl⟩ : syracuseStep 3241433 = 2431075) B2431075
theorem B2160955 : Blo 2159435 2160955 := bstep (se 1 (by rfl) ⟨1620716, by rfl⟩ : syracuseStep 2160955 = 3241433) B3241433
theorem B2464249 : Blo 2159435 2464249 := bbase (se 2 (by rfl) ⟨924093, by rfl⟩ : syracuseStep 2464249 = 1848187) (by norm_num)
theorem B3285665 : Blo 2159435 3285665 := bstep (se 2 (by rfl) ⟨1232124, by rfl⟩ : syracuseStep 3285665 = 2464249) B2464249
theorem B2190443 : Blo 2159435 2190443 := bstep (se 1 (by rfl) ⟨1642832, by rfl⟩ : syracuseStep 2190443 = 3285665) B3285665
theorem B5841181 : Blo 2159435 5841181 := bstep (se 3 (by rfl) ⟨1095221, by rfl⟩ : syracuseStep 5841181 = 2190443) B2190443
theorem B7788241 : Blo 2159435 7788241 := bstep (se 2 (by rfl) ⟨2920590, by rfl⟩ : syracuseStep 7788241 = 5841181) B5841181
theorem B10384321 : Blo 2159435 10384321 := bstep (se 2 (by rfl) ⟨3894120, by rfl⟩ : syracuseStep 10384321 = 7788241) B7788241
theorem B13845761 : Blo 2159435 13845761 := bstep (se 2 (by rfl) ⟨5192160, by rfl⟩ : syracuseStep 13845761 = 10384321) B10384321
theorem B9230507 : Blo 2159435 9230507 := bstep (se 1 (by rfl) ⟨6922880, by rfl⟩ : syracuseStep 9230507 = 13845761) B13845761
theorem B6153671 : Blo 2159435 6153671 := bstep (se 1 (by rfl) ⟨4615253, by rfl⟩ : syracuseStep 6153671 = 9230507) B9230507
theorem B16409789 : Blo 2159435 16409789 := bstep (se 3 (by rfl) ⟨3076835, by rfl⟩ : syracuseStep 16409789 = 6153671) B6153671
theorem B10939859 : Blo 2159435 10939859 := bstep (se 1 (by rfl) ⟨8204894, by rfl⟩ : syracuseStep 10939859 = 16409789) B16409789
theorem B7293239 : Blo 2159435 7293239 := bstep (se 1 (by rfl) ⟨5469929, by rfl⟩ : syracuseStep 7293239 = 10939859) B10939859
theorem B4862159 : Blo 2159435 4862159 := bstep (se 1 (by rfl) ⟨3646619, by rfl⟩ : syracuseStep 4862159 = 7293239) B7293239
theorem B3241439 : Blo 2159435 3241439 := bstep (se 1 (by rfl) ⟨2431079, by rfl⟩ : syracuseStep 3241439 = 4862159) B4862159
theorem B2160959 : Blo 2159435 2160959 := bstep (se 1 (by rfl) ⟨1620719, by rfl⟩ : syracuseStep 2160959 = 3241439) B3241439
theorem B3241445 : Blo 2159435 3241445 := bbase (se 4 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 3241445 = 607771) (by norm_num)
theorem B2160963 : Blo 2159435 2160963 := bstep (se 1 (by rfl) ⟨1620722, by rfl⟩ : syracuseStep 2160963 = 3241445) B3241445
theorem B6237653 : Blo 2159435 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B66534965 : Blo 2159435 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B44356643 : Blo 2159435 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B29571095 : Blo 2159435 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B19714063 : Blo 2159435 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B26285417 : Blo 2159435 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B17523611 : Blo 2159435 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B11682407 : Blo 2159435 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B31153085 : Blo 2159435 31153085 := bstep (se 3 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 31153085 = 11682407) B11682407
theorem B20768723 : Blo 2159435 20768723 := bstep (se 1 (by rfl) ⟨15576542, by rfl⟩ : syracuseStep 20768723 = 31153085) B31153085
theorem B13845815 : Blo 2159435 13845815 := bstep (se 1 (by rfl) ⟨10384361, by rfl⟩ : syracuseStep 13845815 = 20768723) B20768723
theorem B9230543 : Blo 2159435 9230543 := bstep (se 1 (by rfl) ⟨6922907, by rfl⟩ : syracuseStep 9230543 = 13845815) B13845815
theorem B6153695 : Blo 2159435 6153695 := bstep (se 1 (by rfl) ⟨4615271, by rfl⟩ : syracuseStep 6153695 = 9230543) B9230543
theorem B4102463 : Blo 2159435 4102463 := bstep (se 1 (by rfl) ⟨3076847, by rfl⟩ : syracuseStep 4102463 = 6153695) B6153695
theorem B2734975 : Blo 2159435 2734975 := bstep (se 1 (by rfl) ⟨2051231, by rfl⟩ : syracuseStep 2734975 = 4102463) B4102463
theorem B3646633 : Blo 2159435 3646633 := bstep (se 2 (by rfl) ⟨1367487, by rfl⟩ : syracuseStep 3646633 = 2734975) B2734975
theorem B4862177 : Blo 2159435 4862177 := bstep (se 2 (by rfl) ⟨1823316, by rfl⟩ : syracuseStep 4862177 = 3646633) B3646633
theorem B3241451 : Blo 2159435 3241451 := bstep (se 1 (by rfl) ⟨2431088, by rfl⟩ : syracuseStep 3241451 = 4862177) B4862177
theorem B2160967 : Blo 2159435 2160967 := bstep (se 1 (by rfl) ⟨1620725, by rfl⟩ : syracuseStep 2160967 = 3241451) B3241451
theorem B2431093 : Blo 2159435 2431093 := bbase (se 5 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 2431093 = 227915) (by norm_num)
theorem B3241457 : Blo 2159435 3241457 := bstep (se 2 (by rfl) ⟨1215546, by rfl⟩ : syracuseStep 3241457 = 2431093) B2431093
theorem B2160971 : Blo 2159435 2160971 := bstep (se 1 (by rfl) ⟨1620728, by rfl⟩ : syracuseStep 2160971 = 3241457) B3241457
theorem B2734985 : Blo 2159435 2734985 := bbase (se 2 (by rfl) ⟨1025619, by rfl⟩ : syracuseStep 2734985 = 2051239) (by norm_num)
theorem B7293293 : Blo 2159435 7293293 := bstep (se 3 (by rfl) ⟨1367492, by rfl⟩ : syracuseStep 7293293 = 2734985) B2734985
theorem B4862195 : Blo 2159435 4862195 := bstep (se 1 (by rfl) ⟨3646646, by rfl⟩ : syracuseStep 4862195 = 7293293) B7293293
theorem B3241463 : Blo 2159435 3241463 := bstep (se 1 (by rfl) ⟨2431097, by rfl⟩ : syracuseStep 3241463 = 4862195) B4862195
theorem B2160975 : Blo 2159435 2160975 := bstep (se 1 (by rfl) ⟨1620731, by rfl⟩ : syracuseStep 2160975 = 3241463) B3241463
theorem B3241469 : Blo 2159435 3241469 := bbase (se 3 (by rfl) ⟨607775, by rfl⟩ : syracuseStep 3241469 = 1215551) (by norm_num)
theorem B2160979 : Blo 2159435 2160979 := bstep (se 1 (by rfl) ⟨1620734, by rfl⟩ : syracuseStep 2160979 = 3241469) B3241469
theorem B4862213 : Blo 2159435 4862213 := bbase (se 4 (by rfl) ⟨455832, by rfl⟩ : syracuseStep 4862213 = 911665) (by norm_num)
theorem B3241475 : Blo 2159435 3241475 := bstep (se 1 (by rfl) ⟨2431106, by rfl⟩ : syracuseStep 3241475 = 4862213) B4862213
theorem B2160983 : Blo 2159435 2160983 := bstep (se 1 (by rfl) ⟨1620737, by rfl⟩ : syracuseStep 2160983 = 3241475) B3241475
theorem B4102501 : Blo 2159435 4102501 := bbase (se 4 (by rfl) ⟨384609, by rfl⟩ : syracuseStep 4102501 = 769219) (by norm_num)
theorem B5470001 : Blo 2159435 5470001 := bstep (se 2 (by rfl) ⟨2051250, by rfl⟩ : syracuseStep 5470001 = 4102501) B4102501
theorem B3646667 : Blo 2159435 3646667 := bstep (se 1 (by rfl) ⟨2735000, by rfl⟩ : syracuseStep 3646667 = 5470001) B5470001
theorem B2431111 : Blo 2159435 2431111 := bstep (se 1 (by rfl) ⟨1823333, by rfl⟩ : syracuseStep 2431111 = 3646667) B3646667
theorem B3241481 : Blo 2159435 3241481 := bstep (se 2 (by rfl) ⟨1215555, by rfl⟩ : syracuseStep 3241481 = 2431111) B2431111
theorem B2160987 : Blo 2159435 2160987 := bstep (se 1 (by rfl) ⟨1620740, by rfl⟩ : syracuseStep 2160987 = 3241481) B3241481
theorem B10940021 : Blo 2159435 10940021 := bbase (se 5 (by rfl) ⟨512813, by rfl⟩ : syracuseStep 10940021 = 1025627) (by norm_num)
theorem B7293347 : Blo 2159435 7293347 := bstep (se 1 (by rfl) ⟨5470010, by rfl⟩ : syracuseStep 7293347 = 10940021) B10940021
theorem B4862231 : Blo 2159435 4862231 := bstep (se 1 (by rfl) ⟨3646673, by rfl⟩ : syracuseStep 4862231 = 7293347) B7293347
theorem B3241487 : Blo 2159435 3241487 := bstep (se 1 (by rfl) ⟨2431115, by rfl⟩ : syracuseStep 3241487 = 4862231) B4862231
theorem B2160991 : Blo 2159435 2160991 := bstep (se 1 (by rfl) ⟨1620743, by rfl⟩ : syracuseStep 2160991 = 3241487) B3241487
theorem B3241493 : Blo 2159435 3241493 := bbase (se 6 (by rfl) ⟨75972, by rfl⟩ : syracuseStep 3241493 = 151945) (by norm_num)
theorem B2160995 : Blo 2159435 2160995 := bstep (se 1 (by rfl) ⟨1620746, by rfl⟩ : syracuseStep 2160995 = 3241493) B3241493
theorem B2920645 : Blo 2159435 2920645 := bbase (se 4 (by rfl) ⟨273810, by rfl⟩ : syracuseStep 2920645 = 547621) (by norm_num)
theorem B3894193 : Blo 2159435 3894193 := bstep (se 2 (by rfl) ⟨1460322, by rfl⟩ : syracuseStep 3894193 = 2920645) B2920645
theorem B5192257 : Blo 2159435 5192257 := bstep (se 2 (by rfl) ⟨1947096, by rfl⟩ : syracuseStep 5192257 = 3894193) B3894193
theorem B6923009 : Blo 2159435 6923009 := bstep (se 2 (by rfl) ⟨2596128, by rfl⟩ : syracuseStep 6923009 = 5192257) B5192257
theorem B18461357 : Blo 2159435 18461357 := bstep (se 3 (by rfl) ⟨3461504, by rfl⟩ : syracuseStep 18461357 = 6923009) B6923009
theorem B12307571 : Blo 2159435 12307571 := bstep (se 1 (by rfl) ⟨9230678, by rfl⟩ : syracuseStep 12307571 = 18461357) B18461357
theorem B8205047 : Blo 2159435 8205047 := bstep (se 1 (by rfl) ⟨6153785, by rfl⟩ : syracuseStep 8205047 = 12307571) B12307571
theorem B5470031 : Blo 2159435 5470031 := bstep (se 1 (by rfl) ⟨4102523, by rfl⟩ : syracuseStep 5470031 = 8205047) B8205047
theorem B3646687 : Blo 2159435 3646687 := bstep (se 1 (by rfl) ⟨2735015, by rfl⟩ : syracuseStep 3646687 = 5470031) B5470031
theorem B4862249 : Blo 2159435 4862249 := bstep (se 2 (by rfl) ⟨1823343, by rfl⟩ : syracuseStep 4862249 = 3646687) B3646687
theorem B3241499 : Blo 2159435 3241499 := bstep (se 1 (by rfl) ⟨2431124, by rfl⟩ : syracuseStep 3241499 = 4862249) B4862249
theorem B2160999 : Blo 2159435 2160999 := bstep (se 1 (by rfl) ⟨1620749, by rfl⟩ : syracuseStep 2160999 = 3241499) B3241499
theorem B2431129 : Blo 2159435 2431129 := bbase (se 2 (by rfl) ⟨911673, by rfl⟩ : syracuseStep 2431129 = 1823347) (by norm_num)
theorem B3241505 : Blo 2159435 3241505 := bstep (se 2 (by rfl) ⟨1215564, by rfl⟩ : syracuseStep 3241505 = 2431129) B2431129
theorem B2161003 : Blo 2159435 2161003 := bstep (se 1 (by rfl) ⟨1620752, by rfl⟩ : syracuseStep 2161003 = 3241505) B3241505
theorem B8205077 : Blo 2159435 8205077 := bbase (se 6 (by rfl) ⟨192306, by rfl⟩ : syracuseStep 8205077 = 384613) (by norm_num)
theorem B5470051 : Blo 2159435 5470051 := bstep (se 1 (by rfl) ⟨4102538, by rfl⟩ : syracuseStep 5470051 = 8205077) B8205077
theorem B7293401 : Blo 2159435 7293401 := bstep (se 2 (by rfl) ⟨2735025, by rfl⟩ : syracuseStep 7293401 = 5470051) B5470051
theorem B4862267 : Blo 2159435 4862267 := bstep (se 1 (by rfl) ⟨3646700, by rfl⟩ : syracuseStep 4862267 = 7293401) B7293401
theorem B3241511 : Blo 2159435 3241511 := bstep (se 1 (by rfl) ⟨2431133, by rfl⟩ : syracuseStep 3241511 = 4862267) B4862267
theorem B2161007 : Blo 2159435 2161007 := bstep (se 1 (by rfl) ⟨1620755, by rfl⟩ : syracuseStep 2161007 = 3241511) B3241511
theorem B3241517 : Blo 2159435 3241517 := bbase (se 3 (by rfl) ⟨607784, by rfl⟩ : syracuseStep 3241517 = 1215569) (by norm_num)
theorem B2161011 : Blo 2159435 2161011 := bstep (se 1 (by rfl) ⟨1620758, by rfl⟩ : syracuseStep 2161011 = 3241517) B3241517
theorem B4862285 : Blo 2159435 4862285 := bbase (se 3 (by rfl) ⟨911678, by rfl⟩ : syracuseStep 4862285 = 1823357) (by norm_num)
theorem B3241523 : Blo 2159435 3241523 := bstep (se 1 (by rfl) ⟨2431142, by rfl⟩ : syracuseStep 3241523 = 4862285) B4862285
theorem B2161015 : Blo 2159435 2161015 := bstep (se 1 (by rfl) ⟨1620761, by rfl⟩ : syracuseStep 2161015 = 3241523) B3241523
theorem B2735041 : Blo 2159435 2735041 := bbase (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) (by norm_num)
theorem B3646721 : Blo 2159435 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B2431147 : Blo 2159435 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B3241529 : Blo 2159435 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B2161019 : Blo 2159435 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B6571525 : Blo 2159435 6571525 := bbase (se 4 (by rfl) ⟨616080, by rfl⟩ : syracuseStep 6571525 = 1232161) (by norm_num)
theorem B8762033 : Blo 2159435 8762033 := bstep (se 2 (by rfl) ⟨3285762, by rfl⟩ : syracuseStep 8762033 = 6571525) B6571525
theorem B5841355 : Blo 2159435 5841355 := bstep (se 1 (by rfl) ⟨4381016, by rfl⟩ : syracuseStep 5841355 = 8762033) B8762033
theorem B7788473 : Blo 2159435 7788473 := bstep (se 2 (by rfl) ⟨2920677, by rfl⟩ : syracuseStep 7788473 = 5841355) B5841355
theorem B5192315 : Blo 2159435 5192315 := bstep (se 1 (by rfl) ⟨3894236, by rfl⟩ : syracuseStep 5192315 = 7788473) B7788473
theorem B3461543 : Blo 2159435 3461543 := bstep (se 1 (by rfl) ⟨2596157, by rfl⟩ : syracuseStep 3461543 = 5192315) B5192315
theorem B2307695 : Blo 2159435 2307695 := bstep (se 1 (by rfl) ⟨1730771, by rfl⟩ : syracuseStep 2307695 = 3461543) B3461543
theorem B24615413 : Blo 2159435 24615413 := bstep (se 5 (by rfl) ⟨1153847, by rfl⟩ : syracuseStep 24615413 = 2307695) B2307695
theorem B16410275 : Blo 2159435 16410275 := bstep (se 1 (by rfl) ⟨12307706, by rfl⟩ : syracuseStep 16410275 = 24615413) B24615413
theorem B10940183 : Blo 2159435 10940183 := bstep (se 1 (by rfl) ⟨8205137, by rfl⟩ : syracuseStep 10940183 = 16410275) B16410275
theorem B7293455 : Blo 2159435 7293455 := bstep (se 1 (by rfl) ⟨5470091, by rfl⟩ : syracuseStep 7293455 = 10940183) B10940183
theorem B4862303 : Blo 2159435 4862303 := bstep (se 1 (by rfl) ⟨3646727, by rfl⟩ : syracuseStep 4862303 = 7293455) B7293455
theorem B3241535 : Blo 2159435 3241535 := bstep (se 1 (by rfl) ⟨2431151, by rfl⟩ : syracuseStep 3241535 = 4862303) B4862303
theorem B2161023 : Blo 2159435 2161023 := bstep (se 1 (by rfl) ⟨1620767, by rfl⟩ : syracuseStep 2161023 = 3241535) B3241535
theorem B3241541 : Blo 2159435 3241541 := bbase (se 4 (by rfl) ⟨303894, by rfl⟩ : syracuseStep 3241541 = 607789) (by norm_num)
theorem B2161027 : Blo 2159435 2161027 := bstep (se 1 (by rfl) ⟨1620770, by rfl⟩ : syracuseStep 2161027 = 3241541) B3241541
theorem B3646741 : Blo 2159435 3646741 := bbase (se 6 (by rfl) ⟨85470, by rfl⟩ : syracuseStep 3646741 = 170941) (by norm_num)
theorem B4862321 : Blo 2159435 4862321 := bstep (se 2 (by rfl) ⟨1823370, by rfl⟩ : syracuseStep 4862321 = 3646741) B3646741
theorem B3241547 : Blo 2159435 3241547 := bstep (se 1 (by rfl) ⟨2431160, by rfl⟩ : syracuseStep 3241547 = 4862321) B4862321
theorem B2161031 : Blo 2159435 2161031 := bstep (se 1 (by rfl) ⟨1620773, by rfl⟩ : syracuseStep 2161031 = 3241547) B3241547
theorem B2431165 : Blo 2159435 2431165 := bbase (se 3 (by rfl) ⟨455843, by rfl⟩ : syracuseStep 2431165 = 911687) (by norm_num)
theorem B3241553 : Blo 2159435 3241553 := bstep (se 2 (by rfl) ⟨1215582, by rfl⟩ : syracuseStep 3241553 = 2431165) B2431165
theorem B2161035 : Blo 2159435 2161035 := bstep (se 1 (by rfl) ⟨1620776, by rfl⟩ : syracuseStep 2161035 = 3241553) B3241553
theorem B7293509 : Blo 2159435 7293509 := bbase (se 4 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 7293509 = 1367533) (by norm_num)
theorem B4862339 : Blo 2159435 4862339 := bstep (se 1 (by rfl) ⟨3646754, by rfl⟩ : syracuseStep 4862339 = 7293509) B7293509
theorem B3241559 : Blo 2159435 3241559 := bstep (se 1 (by rfl) ⟨2431169, by rfl⟩ : syracuseStep 3241559 = 4862339) B4862339
theorem B2161039 : Blo 2159435 2161039 := bstep (se 1 (by rfl) ⟨1620779, by rfl⟩ : syracuseStep 2161039 = 3241559) B3241559
theorem B3241565 : Blo 2159435 3241565 := bbase (se 3 (by rfl) ⟨607793, by rfl⟩ : syracuseStep 3241565 = 1215587) (by norm_num)
theorem B2161043 : Blo 2159435 2161043 := bstep (se 1 (by rfl) ⟨1620782, by rfl⟩ : syracuseStep 2161043 = 3241565) B3241565
theorem B4862357 : Blo 2159435 4862357 := bbase (se 6 (by rfl) ⟨113961, by rfl⟩ : syracuseStep 4862357 = 227923) (by norm_num)
theorem B3241571 : Blo 2159435 3241571 := bstep (se 1 (by rfl) ⟨2431178, by rfl⟩ : syracuseStep 3241571 = 4862357) B4862357
theorem B2161047 : Blo 2159435 2161047 := bstep (se 1 (by rfl) ⟨1620785, by rfl⟩ : syracuseStep 2161047 = 3241571) B3241571
theorem B2631613 : Blo 2159435 2631613 := bbase (se 3 (by rfl) ⟨493427, by rfl⟩ : syracuseStep 2631613 = 986855) (by norm_num)
theorem B3508817 : Blo 2159435 3508817 := bstep (se 2 (by rfl) ⟨1315806, by rfl⟩ : syracuseStep 3508817 = 2631613) B2631613
theorem B9356845 : Blo 2159435 9356845 := bstep (se 3 (by rfl) ⟨1754408, by rfl⟩ : syracuseStep 9356845 = 3508817) B3508817
theorem B12475793 : Blo 2159435 12475793 := bstep (se 2 (by rfl) ⟨4678422, by rfl⟩ : syracuseStep 12475793 = 9356845) B9356845
theorem B33268781 : Blo 2159435 33268781 := bstep (se 3 (by rfl) ⟨6237896, by rfl⟩ : syracuseStep 33268781 = 12475793) B12475793
theorem B22179187 : Blo 2159435 22179187 := bstep (se 1 (by rfl) ⟨16634390, by rfl⟩ : syracuseStep 22179187 = 33268781) B33268781
theorem B29572249 : Blo 2159435 29572249 := bstep (se 2 (by rfl) ⟨11089593, by rfl⟩ : syracuseStep 29572249 = 22179187) B22179187
theorem B39429665 : Blo 2159435 39429665 := bstep (se 2 (by rfl) ⟨14786124, by rfl⟩ : syracuseStep 39429665 = 29572249) B29572249
theorem B26286443 : Blo 2159435 26286443 := bstep (se 1 (by rfl) ⟨19714832, by rfl⟩ : syracuseStep 26286443 = 39429665) B39429665
theorem B17524295 : Blo 2159435 17524295 := bstep (se 1 (by rfl) ⟨13143221, by rfl⟩ : syracuseStep 17524295 = 26286443) B26286443
theorem B11682863 : Blo 2159435 11682863 := bstep (se 1 (by rfl) ⟨8762147, by rfl⟩ : syracuseStep 11682863 = 17524295) B17524295
theorem B7788575 : Blo 2159435 7788575 := bstep (se 1 (by rfl) ⟨5841431, by rfl⟩ : syracuseStep 7788575 = 11682863) B11682863
theorem B5192383 : Blo 2159435 5192383 := bstep (se 1 (by rfl) ⟨3894287, by rfl⟩ : syracuseStep 5192383 = 7788575) B7788575
theorem B6923177 : Blo 2159435 6923177 := bstep (se 2 (by rfl) ⟨2596191, by rfl⟩ : syracuseStep 6923177 = 5192383) B5192383
theorem B4615451 : Blo 2159435 4615451 := bstep (se 1 (by rfl) ⟨3461588, by rfl⟩ : syracuseStep 4615451 = 6923177) B6923177
theorem B3076967 : Blo 2159435 3076967 := bstep (se 1 (by rfl) ⟨2307725, by rfl⟩ : syracuseStep 3076967 = 4615451) B4615451
theorem B8205245 : Blo 2159435 8205245 := bstep (se 3 (by rfl) ⟨1538483, by rfl⟩ : syracuseStep 8205245 = 3076967) B3076967
theorem B5470163 : Blo 2159435 5470163 := bstep (se 1 (by rfl) ⟨4102622, by rfl⟩ : syracuseStep 5470163 = 8205245) B8205245
theorem B3646775 : Blo 2159435 3646775 := bstep (se 1 (by rfl) ⟨2735081, by rfl⟩ : syracuseStep 3646775 = 5470163) B5470163
theorem B2431183 : Blo 2159435 2431183 := bstep (se 1 (by rfl) ⟨1823387, by rfl⟩ : syracuseStep 2431183 = 3646775) B3646775
theorem B3241577 : Blo 2159435 3241577 := bstep (se 2 (by rfl) ⟨1215591, by rfl⟩ : syracuseStep 3241577 = 2431183) B2431183
theorem B2161051 : Blo 2159435 2161051 := bstep (se 1 (by rfl) ⟨1620788, by rfl⟩ : syracuseStep 2161051 = 3241577) B3241577
theorem B9230917 : Blo 2159435 9230917 := bbase (se 4 (by rfl) ⟨865398, by rfl⟩ : syracuseStep 9230917 = 1730797) (by norm_num)
theorem B12307889 : Blo 2159435 12307889 := bstep (se 2 (by rfl) ⟨4615458, by rfl⟩ : syracuseStep 12307889 = 9230917) B9230917
theorem B8205259 : Blo 2159435 8205259 := bstep (se 1 (by rfl) ⟨6153944, by rfl⟩ : syracuseStep 8205259 = 12307889) B12307889
theorem B10940345 : Blo 2159435 10940345 := bstep (se 2 (by rfl) ⟨4102629, by rfl⟩ : syracuseStep 10940345 = 8205259) B8205259
theorem B7293563 : Blo 2159435 7293563 := bstep (se 1 (by rfl) ⟨5470172, by rfl⟩ : syracuseStep 7293563 = 10940345) B10940345
theorem B4862375 : Blo 2159435 4862375 := bstep (se 1 (by rfl) ⟨3646781, by rfl⟩ : syracuseStep 4862375 = 7293563) B7293563
theorem B3241583 : Blo 2159435 3241583 := bstep (se 1 (by rfl) ⟨2431187, by rfl⟩ : syracuseStep 3241583 = 4862375) B4862375
theorem B2161055 : Blo 2159435 2161055 := bstep (se 1 (by rfl) ⟨1620791, by rfl⟩ : syracuseStep 2161055 = 3241583) B3241583
theorem B3241589 : Blo 2159435 3241589 := bbase (se 5 (by rfl) ⟨151949, by rfl⟩ : syracuseStep 3241589 = 303899) (by norm_num)
theorem B2161059 : Blo 2159435 2161059 := bstep (se 1 (by rfl) ⟨1620794, by rfl⟩ : syracuseStep 2161059 = 3241589) B3241589
theorem B4102645 : Blo 2159435 4102645 := bbase (se 5 (by rfl) ⟨192311, by rfl⟩ : syracuseStep 4102645 = 384623) (by norm_num)
theorem B5470193 : Blo 2159435 5470193 := bstep (se 2 (by rfl) ⟨2051322, by rfl⟩ : syracuseStep 5470193 = 4102645) B4102645
theorem B3646795 : Blo 2159435 3646795 := bstep (se 1 (by rfl) ⟨2735096, by rfl⟩ : syracuseStep 3646795 = 5470193) B5470193
theorem B4862393 : Blo 2159435 4862393 := bstep (se 2 (by rfl) ⟨1823397, by rfl⟩ : syracuseStep 4862393 = 3646795) B3646795
theorem B3241595 : Blo 2159435 3241595 := bstep (se 1 (by rfl) ⟨2431196, by rfl⟩ : syracuseStep 3241595 = 4862393) B4862393
theorem B2161063 : Blo 2159435 2161063 := bstep (se 1 (by rfl) ⟨1620797, by rfl⟩ : syracuseStep 2161063 = 3241595) B3241595
theorem B2431201 : Blo 2159435 2431201 := bbase (se 2 (by rfl) ⟨911700, by rfl⟩ : syracuseStep 2431201 = 1823401) (by norm_num)
theorem B3241601 : Blo 2159435 3241601 := bstep (se 2 (by rfl) ⟨1215600, by rfl⟩ : syracuseStep 3241601 = 2431201) B2431201
theorem B2161067 : Blo 2159435 2161067 := bstep (se 1 (by rfl) ⟨1620800, by rfl⟩ : syracuseStep 2161067 = 3241601) B3241601
theorem B5470213 : Blo 2159435 5470213 := bbase (se 4 (by rfl) ⟨512832, by rfl⟩ : syracuseStep 5470213 = 1025665) (by norm_num)
theorem B7293617 : Blo 2159435 7293617 := bstep (se 2 (by rfl) ⟨2735106, by rfl⟩ : syracuseStep 7293617 = 5470213) B5470213
theorem B4862411 : Blo 2159435 4862411 := bstep (se 1 (by rfl) ⟨3646808, by rfl⟩ : syracuseStep 4862411 = 7293617) B7293617
theorem B3241607 : Blo 2159435 3241607 := bstep (se 1 (by rfl) ⟨2431205, by rfl⟩ : syracuseStep 3241607 = 4862411) B4862411
theorem B2161071 : Blo 2159435 2161071 := bstep (se 1 (by rfl) ⟨1620803, by rfl⟩ : syracuseStep 2161071 = 3241607) B3241607
theorem B3241613 : Blo 2159435 3241613 := bbase (se 3 (by rfl) ⟨607802, by rfl⟩ : syracuseStep 3241613 = 1215605) (by norm_num)
theorem B2161075 : Blo 2159435 2161075 := bstep (se 1 (by rfl) ⟨1620806, by rfl⟩ : syracuseStep 2161075 = 3241613) B3241613
theorem B4862429 : Blo 2159435 4862429 := bbase (se 3 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 4862429 = 1823411) (by norm_num)
theorem B3241619 : Blo 2159435 3241619 := bstep (se 1 (by rfl) ⟨2431214, by rfl⟩ : syracuseStep 3241619 = 4862429) B4862429
theorem B2161079 : Blo 2159435 2161079 := bstep (se 1 (by rfl) ⟨1620809, by rfl⟩ : syracuseStep 2161079 = 3241619) B3241619
theorem B3646829 : Blo 2159435 3646829 := bbase (se 3 (by rfl) ⟨683780, by rfl⟩ : syracuseStep 3646829 = 1367561) (by norm_num)
theorem B2431219 : Blo 2159435 2431219 := bstep (se 1 (by rfl) ⟨1823414, by rfl⟩ : syracuseStep 2431219 = 3646829) B3646829
theorem B3241625 : Blo 2159435 3241625 := bstep (se 2 (by rfl) ⟨1215609, by rfl⟩ : syracuseStep 3241625 = 2431219) B2431219
theorem B2161083 : Blo 2159435 2161083 := bstep (se 1 (by rfl) ⟨1620812, by rfl⟩ : syracuseStep 2161083 = 3241625) B3241625
theorem B26286869 : Blo 2159435 26286869 := bbase (se 6 (by rfl) ⟨616098, by rfl⟩ : syracuseStep 26286869 = 1232197) (by norm_num)
theorem B70098317 : Blo 2159435 70098317 := bstep (se 3 (by rfl) ⟨13143434, by rfl⟩ : syracuseStep 70098317 = 26286869) B26286869
theorem B46732211 : Blo 2159435 46732211 := bstep (se 1 (by rfl) ⟨35049158, by rfl⟩ : syracuseStep 46732211 = 70098317) B70098317
theorem B31154807 : Blo 2159435 31154807 := bstep (se 1 (by rfl) ⟨23366105, by rfl⟩ : syracuseStep 31154807 = 46732211) B46732211
theorem B20769871 : Blo 2159435 20769871 := bstep (se 1 (by rfl) ⟨15577403, by rfl⟩ : syracuseStep 20769871 = 31154807) B31154807
theorem B27693161 : Blo 2159435 27693161 := bstep (se 2 (by rfl) ⟨10384935, by rfl⟩ : syracuseStep 27693161 = 20769871) B20769871
theorem B18462107 : Blo 2159435 18462107 := bstep (se 1 (by rfl) ⟨13846580, by rfl⟩ : syracuseStep 18462107 = 27693161) B27693161
theorem B12308071 : Blo 2159435 12308071 := bstep (se 1 (by rfl) ⟨9231053, by rfl⟩ : syracuseStep 12308071 = 18462107) B18462107
theorem B16410761 : Blo 2159435 16410761 := bstep (se 2 (by rfl) ⟨6154035, by rfl⟩ : syracuseStep 16410761 = 12308071) B12308071
theorem B10940507 : Blo 2159435 10940507 := bstep (se 1 (by rfl) ⟨8205380, by rfl⟩ : syracuseStep 10940507 = 16410761) B16410761
theorem B7293671 : Blo 2159435 7293671 := bstep (se 1 (by rfl) ⟨5470253, by rfl⟩ : syracuseStep 7293671 = 10940507) B10940507
theorem B4862447 : Blo 2159435 4862447 := bstep (se 1 (by rfl) ⟨3646835, by rfl⟩ : syracuseStep 4862447 = 7293671) B7293671
theorem B3241631 : Blo 2159435 3241631 := bstep (se 1 (by rfl) ⟨2431223, by rfl⟩ : syracuseStep 3241631 = 4862447) B4862447
theorem B2161087 : Blo 2159435 2161087 := bstep (se 1 (by rfl) ⟨1620815, by rfl⟩ : syracuseStep 2161087 = 3241631) B3241631
theorem B3241637 : Blo 2159435 3241637 := bbase (se 4 (by rfl) ⟨303903, by rfl⟩ : syracuseStep 3241637 = 607807) (by norm_num)
theorem B2161091 : Blo 2159435 2161091 := bstep (se 1 (by rfl) ⟨1620818, by rfl⟩ : syracuseStep 2161091 = 3241637) B3241637
theorem B2735137 : Blo 2159435 2735137 := bbase (se 2 (by rfl) ⟨1025676, by rfl⟩ : syracuseStep 2735137 = 2051353) (by norm_num)
theorem B3646849 : Blo 2159435 3646849 := bstep (se 2 (by rfl) ⟨1367568, by rfl⟩ : syracuseStep 3646849 = 2735137) B2735137
theorem B4862465 : Blo 2159435 4862465 := bstep (se 2 (by rfl) ⟨1823424, by rfl⟩ : syracuseStep 4862465 = 3646849) B3646849
theorem B3241643 : Blo 2159435 3241643 := bstep (se 1 (by rfl) ⟨2431232, by rfl⟩ : syracuseStep 3241643 = 4862465) B4862465
theorem B2161095 : Blo 2159435 2161095 := bstep (se 1 (by rfl) ⟨1620821, by rfl⟩ : syracuseStep 2161095 = 3241643) B3241643
theorem B2431237 : Blo 2159435 2431237 := bbase (se 4 (by rfl) ⟨227928, by rfl⟩ : syracuseStep 2431237 = 455857) (by norm_num)
theorem B3241649 : Blo 2159435 3241649 := bstep (se 2 (by rfl) ⟨1215618, by rfl⟩ : syracuseStep 3241649 = 2431237) B2431237
theorem B2161099 : Blo 2159435 2161099 := bstep (se 1 (by rfl) ⟨1620824, by rfl⟩ : syracuseStep 2161099 = 3241649) B3241649
theorem B2307781 : Blo 2159435 2307781 := bbase (se 4 (by rfl) ⟨216354, by rfl⟩ : syracuseStep 2307781 = 432709) (by norm_num)
theorem B3077041 : Blo 2159435 3077041 := bstep (se 2 (by rfl) ⟨1153890, by rfl⟩ : syracuseStep 3077041 = 2307781) B2307781
theorem B4102721 : Blo 2159435 4102721 := bstep (se 2 (by rfl) ⟨1538520, by rfl⟩ : syracuseStep 4102721 = 3077041) B3077041
theorem B2735147 : Blo 2159435 2735147 := bstep (se 1 (by rfl) ⟨2051360, by rfl⟩ : syracuseStep 2735147 = 4102721) B4102721
theorem B7293725 : Blo 2159435 7293725 := bstep (se 3 (by rfl) ⟨1367573, by rfl⟩ : syracuseStep 7293725 = 2735147) B2735147
theorem B4862483 : Blo 2159435 4862483 := bstep (se 1 (by rfl) ⟨3646862, by rfl⟩ : syracuseStep 4862483 = 7293725) B7293725
theorem B3241655 : Blo 2159435 3241655 := bstep (se 1 (by rfl) ⟨2431241, by rfl⟩ : syracuseStep 3241655 = 4862483) B4862483
theorem B2161103 : Blo 2159435 2161103 := bstep (se 1 (by rfl) ⟨1620827, by rfl⟩ : syracuseStep 2161103 = 3241655) B3241655
theorem B3241661 : Blo 2159435 3241661 := bbase (se 3 (by rfl) ⟨607811, by rfl⟩ : syracuseStep 3241661 = 1215623) (by norm_num)
theorem B2161107 : Blo 2159435 2161107 := bstep (se 1 (by rfl) ⟨1620830, by rfl⟩ : syracuseStep 2161107 = 3241661) B3241661
theorem B4862501 : Blo 2159435 4862501 := bbase (se 4 (by rfl) ⟨455859, by rfl⟩ : syracuseStep 4862501 = 911719) (by norm_num)
theorem B3241667 : Blo 2159435 3241667 := bstep (se 1 (by rfl) ⟨2431250, by rfl⟩ : syracuseStep 3241667 = 4862501) B4862501
theorem B2161111 : Blo 2159435 2161111 := bstep (se 1 (by rfl) ⟨1620833, by rfl⟩ : syracuseStep 2161111 = 3241667) B3241667
theorem B5470325 : Blo 2159435 5470325 := bbase (se 5 (by rfl) ⟨256421, by rfl⟩ : syracuseStep 5470325 = 512843) (by norm_num)
theorem B3646883 : Blo 2159435 3646883 := bstep (se 1 (by rfl) ⟨2735162, by rfl⟩ : syracuseStep 3646883 = 5470325) B5470325
theorem B2431255 : Blo 2159435 2431255 := bstep (se 1 (by rfl) ⟨1823441, by rfl⟩ : syracuseStep 2431255 = 3646883) B3646883
theorem B3241673 : Blo 2159435 3241673 := bstep (se 2 (by rfl) ⟨1215627, by rfl⟩ : syracuseStep 3241673 = 2431255) B2431255
theorem B2161115 : Blo 2159435 2161115 := bstep (se 1 (by rfl) ⟨1620836, by rfl⟩ : syracuseStep 2161115 = 3241673) B3241673
theorem B2339285 : Blo 2159435 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B24952373 : Blo 2159435 24952373 := bstep (se 5 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 24952373 = 2339285) B2339285
theorem B16634915 : Blo 2159435 16634915 := bstep (se 1 (by rfl) ⟨12476186, by rfl⟩ : syracuseStep 16634915 = 24952373) B24952373
theorem B11089943 : Blo 2159435 11089943 := bstep (se 1 (by rfl) ⟨8317457, by rfl⟩ : syracuseStep 11089943 = 16634915) B16634915
theorem B7393295 : Blo 2159435 7393295 := bstep (se 1 (by rfl) ⟨5544971, by rfl⟩ : syracuseStep 7393295 = 11089943) B11089943
theorem B4928863 : Blo 2159435 4928863 := bstep (se 1 (by rfl) ⟨3696647, by rfl⟩ : syracuseStep 4928863 = 7393295) B7393295
theorem B6571817 : Blo 2159435 6571817 := bstep (se 2 (by rfl) ⟨2464431, by rfl⟩ : syracuseStep 6571817 = 4928863) B4928863
theorem B4381211 : Blo 2159435 4381211 := bstep (se 1 (by rfl) ⟨3285908, by rfl⟩ : syracuseStep 4381211 = 6571817) B6571817
theorem B2920807 : Blo 2159435 2920807 := bstep (se 1 (by rfl) ⟨2190605, by rfl⟩ : syracuseStep 2920807 = 4381211) B4381211
theorem B3894409 : Blo 2159435 3894409 := bstep (se 2 (by rfl) ⟨1460403, by rfl⟩ : syracuseStep 3894409 = 2920807) B2920807
theorem B20770181 : Blo 2159435 20770181 := bstep (se 4 (by rfl) ⟨1947204, by rfl⟩ : syracuseStep 20770181 = 3894409) B3894409
theorem B13846787 : Blo 2159435 13846787 := bstep (se 1 (by rfl) ⟨10385090, by rfl⟩ : syracuseStep 13846787 = 20770181) B20770181
theorem B9231191 : Blo 2159435 9231191 := bstep (se 1 (by rfl) ⟨6923393, by rfl⟩ : syracuseStep 9231191 = 13846787) B13846787
theorem B6154127 : Blo 2159435 6154127 := bstep (se 1 (by rfl) ⟨4615595, by rfl⟩ : syracuseStep 6154127 = 9231191) B9231191
theorem B4102751 : Blo 2159435 4102751 := bstep (se 1 (by rfl) ⟨3077063, by rfl⟩ : syracuseStep 4102751 = 6154127) B6154127
theorem B10940669 : Blo 2159435 10940669 := bstep (se 3 (by rfl) ⟨2051375, by rfl⟩ : syracuseStep 10940669 = 4102751) B4102751
theorem B7293779 : Blo 2159435 7293779 := bstep (se 1 (by rfl) ⟨5470334, by rfl⟩ : syracuseStep 7293779 = 10940669) B10940669
theorem B4862519 : Blo 2159435 4862519 := bstep (se 1 (by rfl) ⟨3646889, by rfl⟩ : syracuseStep 4862519 = 7293779) B7293779
theorem B3241679 : Blo 2159435 3241679 := bstep (se 1 (by rfl) ⟨2431259, by rfl⟩ : syracuseStep 3241679 = 4862519) B4862519
theorem B2161119 : Blo 2159435 2161119 := bstep (se 1 (by rfl) ⟨1620839, by rfl⟩ : syracuseStep 2161119 = 3241679) B3241679
theorem B3241685 : Blo 2159435 3241685 := bbase (se 7 (by rfl) ⟨37988, by rfl⟩ : syracuseStep 3241685 = 75977) (by norm_num)
theorem B2161123 : Blo 2159435 2161123 := bstep (se 1 (by rfl) ⟨1620842, by rfl⟩ : syracuseStep 2161123 = 3241685) B3241685
theorem B4615613 : Blo 2159435 4615613 := bbase (se 3 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 4615613 = 1730855) (by norm_num)
theorem B3077075 : Blo 2159435 3077075 := bstep (se 1 (by rfl) ⟨2307806, by rfl⟩ : syracuseStep 3077075 = 4615613) B4615613
theorem B8205533 : Blo 2159435 8205533 := bstep (se 3 (by rfl) ⟨1538537, by rfl⟩ : syracuseStep 8205533 = 3077075) B3077075
theorem B5470355 : Blo 2159435 5470355 := bstep (se 1 (by rfl) ⟨4102766, by rfl⟩ : syracuseStep 5470355 = 8205533) B8205533
theorem B3646903 : Blo 2159435 3646903 := bstep (se 1 (by rfl) ⟨2735177, by rfl⟩ : syracuseStep 3646903 = 5470355) B5470355
theorem B4862537 : Blo 2159435 4862537 := bstep (se 2 (by rfl) ⟨1823451, by rfl⟩ : syracuseStep 4862537 = 3646903) B3646903
theorem B3241691 : Blo 2159435 3241691 := bstep (se 1 (by rfl) ⟨2431268, by rfl⟩ : syracuseStep 3241691 = 4862537) B4862537
theorem B2161127 : Blo 2159435 2161127 := bstep (se 1 (by rfl) ⟨1620845, by rfl⟩ : syracuseStep 2161127 = 3241691) B3241691
theorem B2431273 : Blo 2159435 2431273 := bbase (se 2 (by rfl) ⟨911727, by rfl⟩ : syracuseStep 2431273 = 1823455) (by norm_num)
theorem B3241697 : Blo 2159435 3241697 := bstep (se 2 (by rfl) ⟨1215636, by rfl⟩ : syracuseStep 3241697 = 2431273) B2431273
theorem B2161131 : Blo 2159435 2161131 := bstep (se 1 (by rfl) ⟨1620848, by rfl⟩ : syracuseStep 2161131 = 3241697) B3241697
theorem B35049941 : Blo 2159435 35049941 := bbase (se 7 (by rfl) ⟨410741, by rfl⟩ : syracuseStep 35049941 = 821483) (by norm_num)
theorem B23366627 : Blo 2159435 23366627 := bstep (se 1 (by rfl) ⟨17524970, by rfl⟩ : syracuseStep 23366627 = 35049941) B35049941
theorem B15577751 : Blo 2159435 15577751 := bstep (se 1 (by rfl) ⟨11683313, by rfl⟩ : syracuseStep 15577751 = 23366627) B23366627
theorem B10385167 : Blo 2159435 10385167 := bstep (se 1 (by rfl) ⟨7788875, by rfl⟩ : syracuseStep 10385167 = 15577751) B15577751
theorem B13846889 : Blo 2159435 13846889 := bstep (se 2 (by rfl) ⟨5192583, by rfl⟩ : syracuseStep 13846889 = 10385167) B10385167
theorem B9231259 : Blo 2159435 9231259 := bstep (se 1 (by rfl) ⟨6923444, by rfl⟩ : syracuseStep 9231259 = 13846889) B13846889
theorem B12308345 : Blo 2159435 12308345 := bstep (se 2 (by rfl) ⟨4615629, by rfl⟩ : syracuseStep 12308345 = 9231259) B9231259
theorem B8205563 : Blo 2159435 8205563 := bstep (se 1 (by rfl) ⟨6154172, by rfl⟩ : syracuseStep 8205563 = 12308345) B12308345
theorem B5470375 : Blo 2159435 5470375 := bstep (se 1 (by rfl) ⟨4102781, by rfl⟩ : syracuseStep 5470375 = 8205563) B8205563
theorem B7293833 : Blo 2159435 7293833 := bstep (se 2 (by rfl) ⟨2735187, by rfl⟩ : syracuseStep 7293833 = 5470375) B5470375
theorem B4862555 : Blo 2159435 4862555 := bstep (se 1 (by rfl) ⟨3646916, by rfl⟩ : syracuseStep 4862555 = 7293833) B7293833
theorem B3241703 : Blo 2159435 3241703 := bstep (se 1 (by rfl) ⟨2431277, by rfl⟩ : syracuseStep 3241703 = 4862555) B4862555
theorem B2161135 : Blo 2159435 2161135 := bstep (se 1 (by rfl) ⟨1620851, by rfl⟩ : syracuseStep 2161135 = 3241703) B3241703
theorem B3241709 : Blo 2159435 3241709 := bbase (se 3 (by rfl) ⟨607820, by rfl⟩ : syracuseStep 3241709 = 1215641) (by norm_num)
theorem B2161139 : Blo 2159435 2161139 := bstep (se 1 (by rfl) ⟨1620854, by rfl⟩ : syracuseStep 2161139 = 3241709) B3241709
theorem B4862573 : Blo 2159435 4862573 := bbase (se 3 (by rfl) ⟨911732, by rfl⟩ : syracuseStep 4862573 = 1823465) (by norm_num)
theorem B3241715 : Blo 2159435 3241715 := bstep (se 1 (by rfl) ⟨2431286, by rfl⟩ : syracuseStep 3241715 = 4862573) B4862573
theorem B2161143 : Blo 2159435 2161143 := bstep (se 1 (by rfl) ⟨1620857, by rfl⟩ : syracuseStep 2161143 = 3241715) B3241715
theorem B4102805 : Blo 2159435 4102805 := bbase (se 6 (by rfl) ⟨96159, by rfl⟩ : syracuseStep 4102805 = 192319) (by norm_num)
theorem B2735203 : Blo 2159435 2735203 := bstep (se 1 (by rfl) ⟨2051402, by rfl⟩ : syracuseStep 2735203 = 4102805) B4102805
theorem B3646937 : Blo 2159435 3646937 := bstep (se 2 (by rfl) ⟨1367601, by rfl⟩ : syracuseStep 3646937 = 2735203) B2735203
theorem B2431291 : Blo 2159435 2431291 := bstep (se 1 (by rfl) ⟨1823468, by rfl⟩ : syracuseStep 2431291 = 3646937) B3646937
theorem B3241721 : Blo 2159435 3241721 := bstep (se 2 (by rfl) ⟨1215645, by rfl⟩ : syracuseStep 3241721 = 2431291) B2431291
theorem B2161147 : Blo 2159435 2161147 := bstep (se 1 (by rfl) ⟨1620860, by rfl⟩ : syracuseStep 2161147 = 3241721) B3241721
theorem B44360405 : Blo 2159435 44360405 := bbase (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) (by norm_num)
theorem B29573603 : Blo 2159435 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B19715735 : Blo 2159435 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B52575293 : Blo 2159435 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B35050195 : Blo 2159435 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B46733593 : Blo 2159435 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B62311457 : Blo 2159435 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B41540971 : Blo 2159435 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B55387961 : Blo 2159435 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B36925307 : Blo 2159435 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B24616871 : Blo 2159435 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B16411247 : Blo 2159435 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B10940831 : Blo 2159435 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B7293887 : Blo 2159435 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B4862591 : Blo 2159435 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B3241727 : Blo 2159435 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B2161151 : Blo 2159435 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B3241733 : Blo 2159435 3241733 := bbase (se 4 (by rfl) ⟨303912, by rfl⟩ : syracuseStep 3241733 = 607825) (by norm_num)
theorem B2161155 : Blo 2159435 2161155 := bstep (se 1 (by rfl) ⟨1620866, by rfl⟩ : syracuseStep 2161155 = 3241733) B3241733
theorem B3646957 : Blo 2159435 3646957 := bbase (se 3 (by rfl) ⟨683804, by rfl⟩ : syracuseStep 3646957 = 1367609) (by norm_num)
theorem B4862609 : Blo 2159435 4862609 := bstep (se 2 (by rfl) ⟨1823478, by rfl⟩ : syracuseStep 4862609 = 3646957) B3646957
theorem B3241739 : Blo 2159435 3241739 := bstep (se 1 (by rfl) ⟨2431304, by rfl⟩ : syracuseStep 3241739 = 4862609) B4862609
theorem B2161159 : Blo 2159435 2161159 := bstep (se 1 (by rfl) ⟨1620869, by rfl⟩ : syracuseStep 2161159 = 3241739) B3241739
theorem B2431309 : Blo 2159435 2431309 := bbase (se 3 (by rfl) ⟨455870, by rfl⟩ : syracuseStep 2431309 = 911741) (by norm_num)
theorem B3241745 : Blo 2159435 3241745 := bstep (se 2 (by rfl) ⟨1215654, by rfl⟩ : syracuseStep 3241745 = 2431309) B2431309
theorem B2161163 : Blo 2159435 2161163 := bstep (se 1 (by rfl) ⟨1620872, by rfl⟩ : syracuseStep 2161163 = 3241745) B3241745
theorem B7293941 : Blo 2159435 7293941 := bbase (se 5 (by rfl) ⟨341903, by rfl⟩ : syracuseStep 7293941 = 683807) (by norm_num)
theorem B4862627 : Blo 2159435 4862627 := bstep (se 1 (by rfl) ⟨3646970, by rfl⟩ : syracuseStep 4862627 = 7293941) B7293941
theorem B3241751 : Blo 2159435 3241751 := bstep (se 1 (by rfl) ⟨2431313, by rfl⟩ : syracuseStep 3241751 = 4862627) B4862627
theorem B2161167 : Blo 2159435 2161167 := bstep (se 1 (by rfl) ⟨1620875, by rfl⟩ : syracuseStep 2161167 = 3241751) B3241751
theorem B3241757 : Blo 2159435 3241757 := bbase (se 3 (by rfl) ⟨607829, by rfl⟩ : syracuseStep 3241757 = 1215659) (by norm_num)
theorem B2161171 : Blo 2159435 2161171 := bstep (se 1 (by rfl) ⟨1620878, by rfl⟩ : syracuseStep 2161171 = 3241757) B3241757
theorem B4862645 : Blo 2159435 4862645 := bbase (se 5 (by rfl) ⟨227936, by rfl⟩ : syracuseStep 4862645 = 455873) (by norm_num)
theorem B3241763 : Blo 2159435 3241763 := bstep (se 1 (by rfl) ⟨2431322, by rfl⟩ : syracuseStep 3241763 = 4862645) B4862645
theorem B2161175 : Blo 2159435 2161175 := bstep (se 1 (by rfl) ⟨1620881, by rfl⟩ : syracuseStep 2161175 = 3241763) B3241763
theorem B12308597 : Blo 2159435 12308597 := bbase (se 5 (by rfl) ⟨576965, by rfl⟩ : syracuseStep 12308597 = 1153931) (by norm_num)
theorem B8205731 : Blo 2159435 8205731 := bstep (se 1 (by rfl) ⟨6154298, by rfl⟩ : syracuseStep 8205731 = 12308597) B12308597
theorem B5470487 : Blo 2159435 5470487 := bstep (se 1 (by rfl) ⟨4102865, by rfl⟩ : syracuseStep 5470487 = 8205731) B8205731
theorem B3646991 : Blo 2159435 3646991 := bstep (se 1 (by rfl) ⟨2735243, by rfl⟩ : syracuseStep 3646991 = 5470487) B5470487
theorem B2431327 : Blo 2159435 2431327 := bstep (se 1 (by rfl) ⟨1823495, by rfl⟩ : syracuseStep 2431327 = 3646991) B3646991
theorem B3241769 : Blo 2159435 3241769 := bstep (se 2 (by rfl) ⟨1215663, by rfl⟩ : syracuseStep 3241769 = 2431327) B2431327
theorem B2161179 : Blo 2159435 2161179 := bstep (se 1 (by rfl) ⟨1620884, by rfl⟩ : syracuseStep 2161179 = 3241769) B3241769
theorem B6154309 : Blo 2159435 6154309 := bbase (se 4 (by rfl) ⟨576966, by rfl⟩ : syracuseStep 6154309 = 1153933) (by norm_num)
theorem B8205745 : Blo 2159435 8205745 := bstep (se 2 (by rfl) ⟨3077154, by rfl⟩ : syracuseStep 8205745 = 6154309) B6154309
theorem B10940993 : Blo 2159435 10940993 := bstep (se 2 (by rfl) ⟨4102872, by rfl⟩ : syracuseStep 10940993 = 8205745) B8205745
theorem B7293995 : Blo 2159435 7293995 := bstep (se 1 (by rfl) ⟨5470496, by rfl⟩ : syracuseStep 7293995 = 10940993) B10940993
theorem B4862663 : Blo 2159435 4862663 := bstep (se 1 (by rfl) ⟨3646997, by rfl⟩ : syracuseStep 4862663 = 7293995) B7293995
theorem B3241775 : Blo 2159435 3241775 := bstep (se 1 (by rfl) ⟨2431331, by rfl⟩ : syracuseStep 3241775 = 4862663) B4862663
theorem B2161183 : Blo 2159435 2161183 := bstep (se 1 (by rfl) ⟨1620887, by rfl⟩ : syracuseStep 2161183 = 3241775) B3241775
theorem B3241781 : Blo 2159435 3241781 := bbase (se 5 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 3241781 = 303917) (by norm_num)
theorem B2161187 : Blo 2159435 2161187 := bstep (se 1 (by rfl) ⟨1620890, by rfl⟩ : syracuseStep 2161187 = 3241781) B3241781
theorem B5470517 : Blo 2159435 5470517 := bbase (se 5 (by rfl) ⟨256430, by rfl⟩ : syracuseStep 5470517 = 512861) (by norm_num)
theorem B3647011 : Blo 2159435 3647011 := bstep (se 1 (by rfl) ⟨2735258, by rfl⟩ : syracuseStep 3647011 = 5470517) B5470517
theorem B4862681 : Blo 2159435 4862681 := bstep (se 2 (by rfl) ⟨1823505, by rfl⟩ : syracuseStep 4862681 = 3647011) B3647011
theorem B3241787 : Blo 2159435 3241787 := bstep (se 1 (by rfl) ⟨2431340, by rfl⟩ : syracuseStep 3241787 = 4862681) B4862681
theorem B2161191 : Blo 2159435 2161191 := bstep (se 1 (by rfl) ⟨1620893, by rfl⟩ : syracuseStep 2161191 = 3241787) B3241787
theorem B2431345 : Blo 2159435 2431345 := bbase (se 2 (by rfl) ⟨911754, by rfl⟩ : syracuseStep 2431345 = 1823509) (by norm_num)
theorem B3241793 : Blo 2159435 3241793 := bstep (se 2 (by rfl) ⟨1215672, by rfl⟩ : syracuseStep 3241793 = 2431345) B2431345
theorem B2161195 : Blo 2159435 2161195 := bstep (se 1 (by rfl) ⟨1620896, by rfl⟩ : syracuseStep 2161195 = 3241793) B3241793
theorem B2596369 : Blo 2159435 2596369 := bbase (se 2 (by rfl) ⟨973638, by rfl⟩ : syracuseStep 2596369 = 1947277) (by norm_num)
theorem B3461825 : Blo 2159435 3461825 := bstep (se 2 (by rfl) ⟨1298184, by rfl⟩ : syracuseStep 3461825 = 2596369) B2596369
theorem B9231533 : Blo 2159435 9231533 := bstep (se 3 (by rfl) ⟨1730912, by rfl⟩ : syracuseStep 9231533 = 3461825) B3461825
theorem B6154355 : Blo 2159435 6154355 := bstep (se 1 (by rfl) ⟨4615766, by rfl⟩ : syracuseStep 6154355 = 9231533) B9231533
theorem B4102903 : Blo 2159435 4102903 := bstep (se 1 (by rfl) ⟨3077177, by rfl⟩ : syracuseStep 4102903 = 6154355) B6154355
theorem B5470537 : Blo 2159435 5470537 := bstep (se 2 (by rfl) ⟨2051451, by rfl⟩ : syracuseStep 5470537 = 4102903) B4102903
theorem B7294049 : Blo 2159435 7294049 := bstep (se 2 (by rfl) ⟨2735268, by rfl⟩ : syracuseStep 7294049 = 5470537) B5470537
theorem B4862699 : Blo 2159435 4862699 := bstep (se 1 (by rfl) ⟨3647024, by rfl⟩ : syracuseStep 4862699 = 7294049) B7294049
theorem B3241799 : Blo 2159435 3241799 := bstep (se 1 (by rfl) ⟨2431349, by rfl⟩ : syracuseStep 3241799 = 4862699) B4862699
theorem B2161199 : Blo 2159435 2161199 := bstep (se 1 (by rfl) ⟨1620899, by rfl⟩ : syracuseStep 2161199 = 3241799) B3241799
theorem B3241805 : Blo 2159435 3241805 := bbase (se 3 (by rfl) ⟨607838, by rfl⟩ : syracuseStep 3241805 = 1215677) (by norm_num)
theorem B2161203 : Blo 2159435 2161203 := bstep (se 1 (by rfl) ⟨1620902, by rfl⟩ : syracuseStep 2161203 = 3241805) B3241805
theorem B4862717 : Blo 2159435 4862717 := bbase (se 3 (by rfl) ⟨911759, by rfl⟩ : syracuseStep 4862717 = 1823519) (by norm_num)
theorem B3241811 : Blo 2159435 3241811 := bstep (se 1 (by rfl) ⟨2431358, by rfl⟩ : syracuseStep 3241811 = 4862717) B4862717
theorem B2161207 : Blo 2159435 2161207 := bstep (se 1 (by rfl) ⟨1620905, by rfl⟩ : syracuseStep 2161207 = 3241811) B3241811
theorem B3647045 : Blo 2159435 3647045 := bbase (se 4 (by rfl) ⟨341910, by rfl⟩ : syracuseStep 3647045 = 683821) (by norm_num)
theorem B2431363 : Blo 2159435 2431363 := bstep (se 1 (by rfl) ⟨1823522, by rfl⟩ : syracuseStep 2431363 = 3647045) B3647045
theorem B3241817 : Blo 2159435 3241817 := bstep (se 2 (by rfl) ⟨1215681, by rfl⟩ : syracuseStep 3241817 = 2431363) B2431363
theorem B2161211 : Blo 2159435 2161211 := bstep (se 1 (by rfl) ⟨1620908, by rfl⟩ : syracuseStep 2161211 = 3241817) B3241817
theorem B16411733 : Blo 2159435 16411733 := bbase (se 8 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 16411733 = 192325) (by norm_num)
theorem B10941155 : Blo 2159435 10941155 := bstep (se 1 (by rfl) ⟨8205866, by rfl⟩ : syracuseStep 10941155 = 16411733) B16411733
theorem B7294103 : Blo 2159435 7294103 := bstep (se 1 (by rfl) ⟨5470577, by rfl⟩ : syracuseStep 7294103 = 10941155) B10941155
theorem B4862735 : Blo 2159435 4862735 := bstep (se 1 (by rfl) ⟨3647051, by rfl⟩ : syracuseStep 4862735 = 7294103) B7294103
theorem B3241823 : Blo 2159435 3241823 := bstep (se 1 (by rfl) ⟨2431367, by rfl⟩ : syracuseStep 3241823 = 4862735) B4862735
theorem B2161215 : Blo 2159435 2161215 := bstep (se 1 (by rfl) ⟨1620911, by rfl⟩ : syracuseStep 2161215 = 3241823) B3241823
theorem B3241829 : Blo 2159435 3241829 := bbase (se 4 (by rfl) ⟨303921, by rfl⟩ : syracuseStep 3241829 = 607843) (by norm_num)
theorem B2161219 : Blo 2159435 2161219 := bstep (se 1 (by rfl) ⟨1620914, by rfl⟩ : syracuseStep 2161219 = 3241829) B3241829
theorem B4102949 : Blo 2159435 4102949 := bbase (se 4 (by rfl) ⟨384651, by rfl⟩ : syracuseStep 4102949 = 769303) (by norm_num)
theorem B2735299 : Blo 2159435 2735299 := bstep (se 1 (by rfl) ⟨2051474, by rfl⟩ : syracuseStep 2735299 = 4102949) B4102949
theorem B3647065 : Blo 2159435 3647065 := bstep (se 2 (by rfl) ⟨1367649, by rfl⟩ : syracuseStep 3647065 = 2735299) B2735299
theorem B4862753 : Blo 2159435 4862753 := bstep (se 2 (by rfl) ⟨1823532, by rfl⟩ : syracuseStep 4862753 = 3647065) B3647065
theorem B3241835 : Blo 2159435 3241835 := bstep (se 1 (by rfl) ⟨2431376, by rfl⟩ : syracuseStep 3241835 = 4862753) B4862753
theorem B2161223 : Blo 2159435 2161223 := bstep (se 1 (by rfl) ⟨1620917, by rfl⟩ : syracuseStep 2161223 = 3241835) B3241835
theorem B2431381 : Blo 2159435 2431381 := bbase (se 6 (by rfl) ⟨56985, by rfl⟩ : syracuseStep 2431381 = 113971) (by norm_num)
theorem B3241841 : Blo 2159435 3241841 := bstep (se 2 (by rfl) ⟨1215690, by rfl⟩ : syracuseStep 3241841 = 2431381) B2431381
theorem B2161227 : Blo 2159435 2161227 := bstep (se 1 (by rfl) ⟨1620920, by rfl⟩ : syracuseStep 2161227 = 3241841) B3241841
theorem B2735309 : Blo 2159435 2735309 := bbase (se 3 (by rfl) ⟨512870, by rfl⟩ : syracuseStep 2735309 = 1025741) (by norm_num)
theorem B7294157 : Blo 2159435 7294157 := bstep (se 3 (by rfl) ⟨1367654, by rfl⟩ : syracuseStep 7294157 = 2735309) B2735309
theorem B4862771 : Blo 2159435 4862771 := bstep (se 1 (by rfl) ⟨3647078, by rfl⟩ : syracuseStep 4862771 = 7294157) B7294157
theorem B3241847 : Blo 2159435 3241847 := bstep (se 1 (by rfl) ⟨2431385, by rfl⟩ : syracuseStep 3241847 = 4862771) B4862771
theorem B2161231 : Blo 2159435 2161231 := bstep (se 1 (by rfl) ⟨1620923, by rfl⟩ : syracuseStep 2161231 = 3241847) B3241847
theorem B3241853 : Blo 2159435 3241853 := bbase (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) (by norm_num)
theorem B2161235 : Blo 2159435 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B4862789 : Blo 2159435 4862789 := bbase (se 4 (by rfl) ⟨455886, by rfl⟩ : syracuseStep 4862789 = 911773) (by norm_num)
theorem B3241859 : Blo 2159435 3241859 := bstep (se 1 (by rfl) ⟨2431394, by rfl⟩ : syracuseStep 3241859 = 4862789) B4862789
theorem B2161239 : Blo 2159435 2161239 := bstep (se 1 (by rfl) ⟨1620929, by rfl⟩ : syracuseStep 2161239 = 3241859) B3241859
theorem B4615861 : Blo 2159435 4615861 := bbase (se 5 (by rfl) ⟨216368, by rfl⟩ : syracuseStep 4615861 = 432737) (by norm_num)
theorem B6154481 : Blo 2159435 6154481 := bstep (se 2 (by rfl) ⟨2307930, by rfl⟩ : syracuseStep 6154481 = 4615861) B4615861
theorem B4102987 : Blo 2159435 4102987 := bstep (se 1 (by rfl) ⟨3077240, by rfl⟩ : syracuseStep 4102987 = 6154481) B6154481
theorem B5470649 : Blo 2159435 5470649 := bstep (se 2 (by rfl) ⟨2051493, by rfl⟩ : syracuseStep 5470649 = 4102987) B4102987
theorem B3647099 : Blo 2159435 3647099 := bstep (se 1 (by rfl) ⟨2735324, by rfl⟩ : syracuseStep 3647099 = 5470649) B5470649
theorem B2431399 : Blo 2159435 2431399 := bstep (se 1 (by rfl) ⟨1823549, by rfl⟩ : syracuseStep 2431399 = 3647099) B3647099
theorem B3241865 : Blo 2159435 3241865 := bstep (se 2 (by rfl) ⟨1215699, by rfl⟩ : syracuseStep 3241865 = 2431399) B2431399
theorem B2161243 : Blo 2159435 2161243 := bstep (se 1 (by rfl) ⟨1620932, by rfl⟩ : syracuseStep 2161243 = 3241865) B3241865
theorem B10941317 : Blo 2159435 10941317 := bbase (se 4 (by rfl) ⟨1025748, by rfl⟩ : syracuseStep 10941317 = 2051497) (by norm_num)
theorem B7294211 : Blo 2159435 7294211 := bstep (se 1 (by rfl) ⟨5470658, by rfl⟩ : syracuseStep 7294211 = 10941317) B10941317
theorem B4862807 : Blo 2159435 4862807 := bstep (se 1 (by rfl) ⟨3647105, by rfl⟩ : syracuseStep 4862807 = 7294211) B7294211
theorem B3241871 : Blo 2159435 3241871 := bstep (se 1 (by rfl) ⟨2431403, by rfl⟩ : syracuseStep 3241871 = 4862807) B4862807
theorem B2161247 : Blo 2159435 2161247 := bstep (se 1 (by rfl) ⟨1620935, by rfl⟩ : syracuseStep 2161247 = 3241871) B3241871
theorem B3241877 : Blo 2159435 3241877 := bbase (se 6 (by rfl) ⟨75981, by rfl⟩ : syracuseStep 3241877 = 151963) (by norm_num)
theorem B2161251 : Blo 2159435 2161251 := bstep (se 1 (by rfl) ⟨1620938, by rfl⟩ : syracuseStep 2161251 = 3241877) B3241877
theorem B3509149 : Blo 2159435 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4678865 : Blo 2159435 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3119243 : Blo 2159435 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B8317981 : Blo 2159435 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B44362565 : Blo 2159435 44362565 := bstep (se 4 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 44362565 = 8317981) B8317981
theorem B29575043 : Blo 2159435 29575043 := bstep (se 1 (by rfl) ⟨22181282, by rfl⟩ : syracuseStep 29575043 = 44362565) B44362565
theorem B19716695 : Blo 2159435 19716695 := bstep (se 1 (by rfl) ⟨14787521, by rfl⟩ : syracuseStep 19716695 = 29575043) B29575043
theorem B13144463 : Blo 2159435 13144463 := bstep (se 1 (by rfl) ⟨9858347, by rfl⟩ : syracuseStep 13144463 = 19716695) B19716695
theorem B8762975 : Blo 2159435 8762975 := bstep (se 1 (by rfl) ⟨6572231, by rfl⟩ : syracuseStep 8762975 = 13144463) B13144463
theorem B5841983 : Blo 2159435 5841983 := bstep (se 1 (by rfl) ⟨4381487, by rfl⟩ : syracuseStep 5841983 = 8762975) B8762975
theorem B3894655 : Blo 2159435 3894655 := bstep (se 1 (by rfl) ⟨2920991, by rfl⟩ : syracuseStep 3894655 = 5841983) B5841983
theorem B5192873 : Blo 2159435 5192873 := bstep (se 2 (by rfl) ⟨1947327, by rfl⟩ : syracuseStep 5192873 = 3894655) B3894655
theorem B3461915 : Blo 2159435 3461915 := bstep (se 1 (by rfl) ⟨2596436, by rfl⟩ : syracuseStep 3461915 = 5192873) B5192873
theorem B2307943 : Blo 2159435 2307943 := bstep (se 1 (by rfl) ⟨1730957, by rfl⟩ : syracuseStep 2307943 = 3461915) B3461915
theorem B12309029 : Blo 2159435 12309029 := bstep (se 4 (by rfl) ⟨1153971, by rfl⟩ : syracuseStep 12309029 = 2307943) B2307943
theorem B8206019 : Blo 2159435 8206019 := bstep (se 1 (by rfl) ⟨6154514, by rfl⟩ : syracuseStep 8206019 = 12309029) B12309029
theorem B5470679 : Blo 2159435 5470679 := bstep (se 1 (by rfl) ⟨4103009, by rfl⟩ : syracuseStep 5470679 = 8206019) B8206019
theorem B3647119 : Blo 2159435 3647119 := bstep (se 1 (by rfl) ⟨2735339, by rfl⟩ : syracuseStep 3647119 = 5470679) B5470679
theorem B4862825 : Blo 2159435 4862825 := bstep (se 2 (by rfl) ⟨1823559, by rfl⟩ : syracuseStep 4862825 = 3647119) B3647119
theorem B3241883 : Blo 2159435 3241883 := bstep (se 1 (by rfl) ⟨2431412, by rfl⟩ : syracuseStep 3241883 = 4862825) B4862825
theorem B2161255 : Blo 2159435 2161255 := bstep (se 1 (by rfl) ⟨1620941, by rfl⟩ : syracuseStep 2161255 = 3241883) B3241883
theorem B2431417 : Blo 2159435 2431417 := bbase (se 2 (by rfl) ⟨911781, by rfl⟩ : syracuseStep 2431417 = 1823563) (by norm_num)
theorem B3241889 : Blo 2159435 3241889 := bstep (se 2 (by rfl) ⟨1215708, by rfl⟩ : syracuseStep 3241889 = 2431417) B2431417
theorem B2161259 : Blo 2159435 2161259 := bstep (se 1 (by rfl) ⟨1620944, by rfl⟩ : syracuseStep 2161259 = 3241889) B3241889
theorem B14989333 : Blo 2159435 14989333 := bbase (se 6 (by rfl) ⟨351312, by rfl⟩ : syracuseStep 14989333 = 702625) (by norm_num)
theorem B19985777 : Blo 2159435 19985777 := bstep (se 2 (by rfl) ⟨7494666, by rfl⟩ : syracuseStep 19985777 = 14989333) B14989333
theorem B13323851 : Blo 2159435 13323851 := bstep (se 1 (by rfl) ⟨9992888, by rfl⟩ : syracuseStep 13323851 = 19985777) B19985777
theorem B8882567 : Blo 2159435 8882567 := bstep (se 1 (by rfl) ⟨6661925, by rfl⟩ : syracuseStep 8882567 = 13323851) B13323851
theorem B5921711 : Blo 2159435 5921711 := bstep (se 1 (by rfl) ⟨4441283, by rfl⟩ : syracuseStep 5921711 = 8882567) B8882567
theorem B3947807 : Blo 2159435 3947807 := bstep (se 1 (by rfl) ⟨2960855, by rfl⟩ : syracuseStep 3947807 = 5921711) B5921711
theorem B2631871 : Blo 2159435 2631871 := bstep (se 1 (by rfl) ⟨1973903, by rfl⟩ : syracuseStep 2631871 = 3947807) B3947807
theorem B14036645 : Blo 2159435 14036645 := bstep (se 4 (by rfl) ⟨1315935, by rfl⟩ : syracuseStep 14036645 = 2631871) B2631871
theorem B9357763 : Blo 2159435 9357763 := bstep (se 1 (by rfl) ⟨7018322, by rfl⟩ : syracuseStep 9357763 = 14036645) B14036645
theorem B12477017 : Blo 2159435 12477017 := bstep (se 2 (by rfl) ⟨4678881, by rfl⟩ : syracuseStep 12477017 = 9357763) B9357763
theorem B8318011 : Blo 2159435 8318011 := bstep (se 1 (by rfl) ⟨6238508, by rfl⟩ : syracuseStep 8318011 = 12477017) B12477017
theorem B11090681 : Blo 2159435 11090681 := bstep (se 2 (by rfl) ⟨4159005, by rfl⟩ : syracuseStep 11090681 = 8318011) B8318011
theorem B7393787 : Blo 2159435 7393787 := bstep (se 1 (by rfl) ⟨5545340, by rfl⟩ : syracuseStep 7393787 = 11090681) B11090681
theorem B4929191 : Blo 2159435 4929191 := bstep (se 1 (by rfl) ⟨3696893, by rfl⟩ : syracuseStep 4929191 = 7393787) B7393787
theorem B3286127 : Blo 2159435 3286127 := bstep (se 1 (by rfl) ⟨2464595, by rfl⟩ : syracuseStep 3286127 = 4929191) B4929191
theorem B8763005 : Blo 2159435 8763005 := bstep (se 3 (by rfl) ⟨1643063, by rfl⟩ : syracuseStep 8763005 = 3286127) B3286127
theorem B23368013 : Blo 2159435 23368013 := bstep (se 3 (by rfl) ⟨4381502, by rfl⟩ : syracuseStep 23368013 = 8763005) B8763005
theorem B15578675 : Blo 2159435 15578675 := bstep (se 1 (by rfl) ⟨11684006, by rfl⟩ : syracuseStep 15578675 = 23368013) B23368013
theorem B10385783 : Blo 2159435 10385783 := bstep (se 1 (by rfl) ⟨7789337, by rfl⟩ : syracuseStep 10385783 = 15578675) B15578675
theorem B6923855 : Blo 2159435 6923855 := bstep (se 1 (by rfl) ⟨5192891, by rfl⟩ : syracuseStep 6923855 = 10385783) B10385783
theorem B4615903 : Blo 2159435 4615903 := bstep (se 1 (by rfl) ⟨3461927, by rfl⟩ : syracuseStep 4615903 = 6923855) B6923855
theorem B6154537 : Blo 2159435 6154537 := bstep (se 2 (by rfl) ⟨2307951, by rfl⟩ : syracuseStep 6154537 = 4615903) B4615903
theorem B8206049 : Blo 2159435 8206049 := bstep (se 2 (by rfl) ⟨3077268, by rfl⟩ : syracuseStep 8206049 = 6154537) B6154537
theorem B5470699 : Blo 2159435 5470699 := bstep (se 1 (by rfl) ⟨4103024, by rfl⟩ : syracuseStep 5470699 = 8206049) B8206049
theorem B7294265 : Blo 2159435 7294265 := bstep (se 2 (by rfl) ⟨2735349, by rfl⟩ : syracuseStep 7294265 = 5470699) B5470699
theorem B4862843 : Blo 2159435 4862843 := bstep (se 1 (by rfl) ⟨3647132, by rfl⟩ : syracuseStep 4862843 = 7294265) B7294265
theorem B3241895 : Blo 2159435 3241895 := bstep (se 1 (by rfl) ⟨2431421, by rfl⟩ : syracuseStep 3241895 = 4862843) B4862843
theorem B2161263 : Blo 2159435 2161263 := bstep (se 1 (by rfl) ⟨1620947, by rfl⟩ : syracuseStep 2161263 = 3241895) B3241895
theorem B3241901 : Blo 2159435 3241901 := bbase (se 3 (by rfl) ⟨607856, by rfl⟩ : syracuseStep 3241901 = 1215713) (by norm_num)
theorem B2161267 : Blo 2159435 2161267 := bstep (se 1 (by rfl) ⟨1620950, by rfl⟩ : syracuseStep 2161267 = 3241901) B3241901
theorem B4862861 : Blo 2159435 4862861 := bbase (se 3 (by rfl) ⟨911786, by rfl⟩ : syracuseStep 4862861 = 1823573) (by norm_num)
theorem B3241907 : Blo 2159435 3241907 := bstep (se 1 (by rfl) ⟨2431430, by rfl⟩ : syracuseStep 3241907 = 4862861) B4862861
theorem B2161271 : Blo 2159435 2161271 := bstep (se 1 (by rfl) ⟨1620953, by rfl⟩ : syracuseStep 2161271 = 3241907) B3241907
theorem B2735365 : Blo 2159435 2735365 := bbase (se 4 (by rfl) ⟨256440, by rfl⟩ : syracuseStep 2735365 = 512881) (by norm_num)
theorem B3647153 : Blo 2159435 3647153 := bstep (se 2 (by rfl) ⟨1367682, by rfl⟩ : syracuseStep 3647153 = 2735365) B2735365
theorem B2431435 : Blo 2159435 2431435 := bstep (se 1 (by rfl) ⟨1823576, by rfl⟩ : syracuseStep 2431435 = 3647153) B3647153
theorem B3241913 : Blo 2159435 3241913 := bstep (se 2 (by rfl) ⟨1215717, by rfl⟩ : syracuseStep 3241913 = 2431435) B2431435
theorem B2161275 : Blo 2159435 2161275 := bstep (se 1 (by rfl) ⟨1620956, by rfl⟩ : syracuseStep 2161275 = 3241913) B3241913
theorem B22181525 : Blo 2159435 22181525 := bbase (se 6 (by rfl) ⟨519879, by rfl⟩ : syracuseStep 22181525 = 1039759) (by norm_num)
theorem B14787683 : Blo 2159435 14787683 := bstep (se 1 (by rfl) ⟨11090762, by rfl⟩ : syracuseStep 14787683 = 22181525) B22181525
theorem B9858455 : Blo 2159435 9858455 := bstep (se 1 (by rfl) ⟨7393841, by rfl⟩ : syracuseStep 9858455 = 14787683) B14787683
theorem B6572303 : Blo 2159435 6572303 := bstep (se 1 (by rfl) ⟨4929227, by rfl⟩ : syracuseStep 6572303 = 9858455) B9858455
theorem B4381535 : Blo 2159435 4381535 := bstep (se 1 (by rfl) ⟨3286151, by rfl⟩ : syracuseStep 4381535 = 6572303) B6572303
theorem B2921023 : Blo 2159435 2921023 := bstep (se 1 (by rfl) ⟨2190767, by rfl⟩ : syracuseStep 2921023 = 4381535) B4381535
theorem B3894697 : Blo 2159435 3894697 := bstep (se 2 (by rfl) ⟨1460511, by rfl⟩ : syracuseStep 3894697 = 2921023) B2921023
theorem B5192929 : Blo 2159435 5192929 := bstep (se 2 (by rfl) ⟨1947348, by rfl⟩ : syracuseStep 5192929 = 3894697) B3894697
theorem B27695621 : Blo 2159435 27695621 := bstep (se 4 (by rfl) ⟨2596464, by rfl⟩ : syracuseStep 27695621 = 5192929) B5192929
theorem B18463747 : Blo 2159435 18463747 := bstep (se 1 (by rfl) ⟨13847810, by rfl⟩ : syracuseStep 18463747 = 27695621) B27695621
theorem B24618329 : Blo 2159435 24618329 := bstep (se 2 (by rfl) ⟨9231873, by rfl⟩ : syracuseStep 24618329 = 18463747) B18463747
theorem B16412219 : Blo 2159435 16412219 := bstep (se 1 (by rfl) ⟨12309164, by rfl⟩ : syracuseStep 16412219 = 24618329) B24618329
theorem B10941479 : Blo 2159435 10941479 := bstep (se 1 (by rfl) ⟨8206109, by rfl⟩ : syracuseStep 10941479 = 16412219) B16412219
theorem B7294319 : Blo 2159435 7294319 := bstep (se 1 (by rfl) ⟨5470739, by rfl⟩ : syracuseStep 7294319 = 10941479) B10941479
theorem B4862879 : Blo 2159435 4862879 := bstep (se 1 (by rfl) ⟨3647159, by rfl⟩ : syracuseStep 4862879 = 7294319) B7294319
theorem B3241919 : Blo 2159435 3241919 := bstep (se 1 (by rfl) ⟨2431439, by rfl⟩ : syracuseStep 3241919 = 4862879) B4862879
theorem B2161279 : Blo 2159435 2161279 := bstep (se 1 (by rfl) ⟨1620959, by rfl⟩ : syracuseStep 2161279 = 3241919) B3241919
theorem B3241925 : Blo 2159435 3241925 := bbase (se 4 (by rfl) ⟨303930, by rfl⟩ : syracuseStep 3241925 = 607861) (by norm_num)
theorem B2161283 : Blo 2159435 2161283 := bstep (se 1 (by rfl) ⟨1620962, by rfl⟩ : syracuseStep 2161283 = 3241925) B3241925
theorem B3647173 : Blo 2159435 3647173 := bbase (se 4 (by rfl) ⟨341922, by rfl⟩ : syracuseStep 3647173 = 683845) (by norm_num)
theorem B4862897 : Blo 2159435 4862897 := bstep (se 2 (by rfl) ⟨1823586, by rfl⟩ : syracuseStep 4862897 = 3647173) B3647173
theorem B3241931 : Blo 2159435 3241931 := bstep (se 1 (by rfl) ⟨2431448, by rfl⟩ : syracuseStep 3241931 = 4862897) B4862897
theorem B2161287 : Blo 2159435 2161287 := bstep (se 1 (by rfl) ⟨1620965, by rfl⟩ : syracuseStep 2161287 = 3241931) B3241931
theorem B2431453 : Blo 2159435 2431453 := bbase (se 3 (by rfl) ⟨455897, by rfl⟩ : syracuseStep 2431453 = 911795) (by norm_num)
theorem B3241937 : Blo 2159435 3241937 := bstep (se 2 (by rfl) ⟨1215726, by rfl⟩ : syracuseStep 3241937 = 2431453) B2431453
theorem B2161291 : Blo 2159435 2161291 := bstep (se 1 (by rfl) ⟨1620968, by rfl⟩ : syracuseStep 2161291 = 3241937) B3241937
theorem B7294373 : Blo 2159435 7294373 := bbase (se 4 (by rfl) ⟨683847, by rfl⟩ : syracuseStep 7294373 = 1367695) (by norm_num)
theorem B4862915 : Blo 2159435 4862915 := bstep (se 1 (by rfl) ⟨3647186, by rfl⟩ : syracuseStep 4862915 = 7294373) B7294373
theorem B3241943 : Blo 2159435 3241943 := bstep (se 1 (by rfl) ⟨2431457, by rfl⟩ : syracuseStep 3241943 = 4862915) B4862915
theorem B2161295 : Blo 2159435 2161295 := bstep (se 1 (by rfl) ⟨1620971, by rfl⟩ : syracuseStep 2161295 = 3241943) B3241943
theorem B3241949 : Blo 2159435 3241949 := bbase (se 3 (by rfl) ⟨607865, by rfl⟩ : syracuseStep 3241949 = 1215731) (by norm_num)
theorem B2161299 : Blo 2159435 2161299 := bstep (se 1 (by rfl) ⟨1620974, by rfl⟩ : syracuseStep 2161299 = 3241949) B3241949
theorem B4862933 : Blo 2159435 4862933 := bbase (se 7 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 4862933 = 113975) (by norm_num)
theorem B3241955 : Blo 2159435 3241955 := bstep (se 1 (by rfl) ⟨2431466, by rfl⟩ : syracuseStep 3241955 = 4862933) B4862933
theorem B2161303 : Blo 2159435 2161303 := bstep (se 1 (by rfl) ⟨1620977, by rfl⟩ : syracuseStep 2161303 = 3241955) B3241955
theorem B11684245 : Blo 2159435 11684245 := bbase (se 6 (by rfl) ⟨273849, by rfl⟩ : syracuseStep 11684245 = 547699) (by norm_num)
theorem B15578993 : Blo 2159435 15578993 := bstep (se 2 (by rfl) ⟨5842122, by rfl⟩ : syracuseStep 15578993 = 11684245) B11684245
theorem B10385995 : Blo 2159435 10385995 := bstep (se 1 (by rfl) ⟨7789496, by rfl⟩ : syracuseStep 10385995 = 15578993) B15578993
theorem B13847993 : Blo 2159435 13847993 := bstep (se 2 (by rfl) ⟨5192997, by rfl⟩ : syracuseStep 13847993 = 10385995) B10385995
theorem B9231995 : Blo 2159435 9231995 := bstep (se 1 (by rfl) ⟨6923996, by rfl⟩ : syracuseStep 9231995 = 13847993) B13847993
theorem B6154663 : Blo 2159435 6154663 := bstep (se 1 (by rfl) ⟨4615997, by rfl⟩ : syracuseStep 6154663 = 9231995) B9231995
theorem B8206217 : Blo 2159435 8206217 := bstep (se 2 (by rfl) ⟨3077331, by rfl⟩ : syracuseStep 8206217 = 6154663) B6154663
theorem B5470811 : Blo 2159435 5470811 := bstep (se 1 (by rfl) ⟨4103108, by rfl⟩ : syracuseStep 5470811 = 8206217) B8206217
theorem B3647207 : Blo 2159435 3647207 := bstep (se 1 (by rfl) ⟨2735405, by rfl⟩ : syracuseStep 3647207 = 5470811) B5470811
theorem B2431471 : Blo 2159435 2431471 := bstep (se 1 (by rfl) ⟨1823603, by rfl⟩ : syracuseStep 2431471 = 3647207) B3647207
theorem B3241961 : Blo 2159435 3241961 := bstep (se 2 (by rfl) ⟨1215735, by rfl⟩ : syracuseStep 3241961 = 2431471) B2431471
theorem B2161307 : Blo 2159435 2161307 := bstep (se 1 (by rfl) ⟨1620980, by rfl⟩ : syracuseStep 2161307 = 3241961) B3241961
theorem B18464021 : Blo 2159435 18464021 := bbase (se 6 (by rfl) ⟨432750, by rfl⟩ : syracuseStep 18464021 = 865501) (by norm_num)
theorem B12309347 : Blo 2159435 12309347 := bstep (se 1 (by rfl) ⟨9232010, by rfl⟩ : syracuseStep 12309347 = 18464021) B18464021
theorem B8206231 : Blo 2159435 8206231 := bstep (se 1 (by rfl) ⟨6154673, by rfl⟩ : syracuseStep 8206231 = 12309347) B12309347
theorem B10941641 : Blo 2159435 10941641 := bstep (se 2 (by rfl) ⟨4103115, by rfl⟩ : syracuseStep 10941641 = 8206231) B8206231
theorem B7294427 : Blo 2159435 7294427 := bstep (se 1 (by rfl) ⟨5470820, by rfl⟩ : syracuseStep 7294427 = 10941641) B10941641
theorem B4862951 : Blo 2159435 4862951 := bstep (se 1 (by rfl) ⟨3647213, by rfl⟩ : syracuseStep 4862951 = 7294427) B7294427
theorem B3241967 : Blo 2159435 3241967 := bstep (se 1 (by rfl) ⟨2431475, by rfl⟩ : syracuseStep 3241967 = 4862951) B4862951
theorem B2161311 : Blo 2159435 2161311 := bstep (se 1 (by rfl) ⟨1620983, by rfl⟩ : syracuseStep 2161311 = 3241967) B3241967
theorem B3241973 : Blo 2159435 3241973 := bbase (se 5 (by rfl) ⟨151967, by rfl⟩ : syracuseStep 3241973 = 303935) (by norm_num)
theorem B2161315 : Blo 2159435 2161315 := bstep (se 1 (by rfl) ⟨1620986, by rfl⟩ : syracuseStep 2161315 = 3241973) B3241973
theorem B10386053 : Blo 2159435 10386053 := bbase (se 4 (by rfl) ⟨973692, by rfl⟩ : syracuseStep 10386053 = 1947385) (by norm_num)
theorem B6924035 : Blo 2159435 6924035 := bstep (se 1 (by rfl) ⟨5193026, by rfl⟩ : syracuseStep 6924035 = 10386053) B10386053
theorem B4616023 : Blo 2159435 4616023 := bstep (se 1 (by rfl) ⟨3462017, by rfl⟩ : syracuseStep 4616023 = 6924035) B6924035
theorem B6154697 : Blo 2159435 6154697 := bstep (se 2 (by rfl) ⟨2308011, by rfl⟩ : syracuseStep 6154697 = 4616023) B4616023
theorem B4103131 : Blo 2159435 4103131 := bstep (se 1 (by rfl) ⟨3077348, by rfl⟩ : syracuseStep 4103131 = 6154697) B6154697
theorem B5470841 : Blo 2159435 5470841 := bstep (se 2 (by rfl) ⟨2051565, by rfl⟩ : syracuseStep 5470841 = 4103131) B4103131
theorem B3647227 : Blo 2159435 3647227 := bstep (se 1 (by rfl) ⟨2735420, by rfl⟩ : syracuseStep 3647227 = 5470841) B5470841
theorem B4862969 : Blo 2159435 4862969 := bstep (se 2 (by rfl) ⟨1823613, by rfl⟩ : syracuseStep 4862969 = 3647227) B3647227
theorem B3241979 : Blo 2159435 3241979 := bstep (se 1 (by rfl) ⟨2431484, by rfl⟩ : syracuseStep 3241979 = 4862969) B4862969
theorem B2161319 : Blo 2159435 2161319 := bstep (se 1 (by rfl) ⟨1620989, by rfl⟩ : syracuseStep 2161319 = 3241979) B3241979
theorem B2431489 : Blo 2159435 2431489 := bbase (se 2 (by rfl) ⟨911808, by rfl⟩ : syracuseStep 2431489 = 1823617) (by norm_num)
theorem B3241985 : Blo 2159435 3241985 := bstep (se 2 (by rfl) ⟨1215744, by rfl⟩ : syracuseStep 3241985 = 2431489) B2431489
theorem B2161323 : Blo 2159435 2161323 := bstep (se 1 (by rfl) ⟨1620992, by rfl⟩ : syracuseStep 2161323 = 3241985) B3241985
theorem B5470861 : Blo 2159435 5470861 := bbase (se 3 (by rfl) ⟨1025786, by rfl⟩ : syracuseStep 5470861 = 2051573) (by norm_num)
theorem B7294481 : Blo 2159435 7294481 := bstep (se 2 (by rfl) ⟨2735430, by rfl⟩ : syracuseStep 7294481 = 5470861) B5470861
theorem B4862987 : Blo 2159435 4862987 := bstep (se 1 (by rfl) ⟨3647240, by rfl⟩ : syracuseStep 4862987 = 7294481) B7294481
theorem B3241991 : Blo 2159435 3241991 := bstep (se 1 (by rfl) ⟨2431493, by rfl⟩ : syracuseStep 3241991 = 4862987) B4862987
theorem B2161327 : Blo 2159435 2161327 := bstep (se 1 (by rfl) ⟨1620995, by rfl⟩ : syracuseStep 2161327 = 3241991) B3241991
theorem B3241997 : Blo 2159435 3241997 := bbase (se 3 (by rfl) ⟨607874, by rfl⟩ : syracuseStep 3241997 = 1215749) (by norm_num)
theorem B2161331 : Blo 2159435 2161331 := bstep (se 1 (by rfl) ⟨1620998, by rfl⟩ : syracuseStep 2161331 = 3241997) B3241997
theorem B4863005 : Blo 2159435 4863005 := bbase (se 3 (by rfl) ⟨911813, by rfl⟩ : syracuseStep 4863005 = 1823627) (by norm_num)
theorem B3242003 : Blo 2159435 3242003 := bstep (se 1 (by rfl) ⟨2431502, by rfl⟩ : syracuseStep 3242003 = 4863005) B4863005
theorem B2161335 : Blo 2159435 2161335 := bstep (se 1 (by rfl) ⟨1621001, by rfl⟩ : syracuseStep 2161335 = 3242003) B3242003
theorem B3647261 : Blo 2159435 3647261 := bbase (se 3 (by rfl) ⟨683861, by rfl⟩ : syracuseStep 3647261 = 1367723) (by norm_num)
theorem B2431507 : Blo 2159435 2431507 := bstep (se 1 (by rfl) ⟨1823630, by rfl⟩ : syracuseStep 2431507 = 3647261) B3647261
theorem B3242009 : Blo 2159435 3242009 := bstep (se 2 (by rfl) ⟨1215753, by rfl⟩ : syracuseStep 3242009 = 2431507) B2431507
theorem B2161339 : Blo 2159435 2161339 := bstep (se 1 (by rfl) ⟨1621004, by rfl⟩ : syracuseStep 2161339 = 3242009) B3242009
theorem B4929373 : Blo 2159435 4929373 := bbase (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) (by norm_num)
theorem B6572497 : Blo 2159435 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B8763329 : Blo 2159435 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B5842219 : Blo 2159435 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B7789625 : Blo 2159435 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B5193083 : Blo 2159435 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B13848221 : Blo 2159435 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B9232147 : Blo 2159435 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B12309529 : Blo 2159435 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B16412705 : Blo 2159435 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B10941803 : Blo 2159435 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B7294535 : Blo 2159435 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B4863023 : Blo 2159435 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B3242015 : Blo 2159435 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B2161343 : Blo 2159435 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B3242021 : Blo 2159435 3242021 := bbase (se 4 (by rfl) ⟨303939, by rfl⟩ : syracuseStep 3242021 = 607879) (by norm_num)
theorem B2161347 : Blo 2159435 2161347 := bstep (se 1 (by rfl) ⟨1621010, by rfl⟩ : syracuseStep 2161347 = 3242021) B3242021
theorem B2735461 : Blo 2159435 2735461 := bbase (se 4 (by rfl) ⟨256449, by rfl⟩ : syracuseStep 2735461 = 512899) (by norm_num)
theorem B3647281 : Blo 2159435 3647281 := bstep (se 2 (by rfl) ⟨1367730, by rfl⟩ : syracuseStep 3647281 = 2735461) B2735461
theorem B4863041 : Blo 2159435 4863041 := bstep (se 2 (by rfl) ⟨1823640, by rfl⟩ : syracuseStep 4863041 = 3647281) B3647281
theorem B3242027 : Blo 2159435 3242027 := bstep (se 1 (by rfl) ⟨2431520, by rfl⟩ : syracuseStep 3242027 = 4863041) B4863041
theorem B2161351 : Blo 2159435 2161351 := bstep (se 1 (by rfl) ⟨1621013, by rfl⟩ : syracuseStep 2161351 = 3242027) B3242027
theorem B2431525 : Blo 2159435 2431525 := bbase (se 4 (by rfl) ⟨227955, by rfl⟩ : syracuseStep 2431525 = 455911) (by norm_num)
theorem B3242033 : Blo 2159435 3242033 := bstep (se 2 (by rfl) ⟨1215762, by rfl⟩ : syracuseStep 3242033 = 2431525) B2431525
theorem B2161355 : Blo 2159435 2161355 := bstep (se 1 (by rfl) ⟨1621016, by rfl⟩ : syracuseStep 2161355 = 3242033) B3242033
theorem B10386245 : Blo 2159435 10386245 := bbase (se 4 (by rfl) ⟨973710, by rfl⟩ : syracuseStep 10386245 = 1947421) (by norm_num)
theorem B6924163 : Blo 2159435 6924163 := bstep (se 1 (by rfl) ⟨5193122, by rfl⟩ : syracuseStep 6924163 = 10386245) B10386245
theorem B9232217 : Blo 2159435 9232217 := bstep (se 2 (by rfl) ⟨3462081, by rfl⟩ : syracuseStep 9232217 = 6924163) B6924163
theorem B6154811 : Blo 2159435 6154811 := bstep (se 1 (by rfl) ⟨4616108, by rfl⟩ : syracuseStep 6154811 = 9232217) B9232217
theorem B4103207 : Blo 2159435 4103207 := bstep (se 1 (by rfl) ⟨3077405, by rfl⟩ : syracuseStep 4103207 = 6154811) B6154811
theorem B2735471 : Blo 2159435 2735471 := bstep (se 1 (by rfl) ⟨2051603, by rfl⟩ : syracuseStep 2735471 = 4103207) B4103207
theorem B7294589 : Blo 2159435 7294589 := bstep (se 3 (by rfl) ⟨1367735, by rfl⟩ : syracuseStep 7294589 = 2735471) B2735471
theorem B4863059 : Blo 2159435 4863059 := bstep (se 1 (by rfl) ⟨3647294, by rfl⟩ : syracuseStep 4863059 = 7294589) B7294589
theorem B3242039 : Blo 2159435 3242039 := bstep (se 1 (by rfl) ⟨2431529, by rfl⟩ : syracuseStep 3242039 = 4863059) B4863059
theorem B2161359 : Blo 2159435 2161359 := bstep (se 1 (by rfl) ⟨1621019, by rfl⟩ : syracuseStep 2161359 = 3242039) B3242039
theorem B3242045 : Blo 2159435 3242045 := bbase (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) (by norm_num)
theorem B2161363 : Blo 2159435 2161363 := bstep (se 1 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 2161363 = 3242045) B3242045
theorem B4863077 : Blo 2159435 4863077 := bbase (se 4 (by rfl) ⟨455913, by rfl⟩ : syracuseStep 4863077 = 911827) (by norm_num)
theorem B3242051 : Blo 2159435 3242051 := bstep (se 1 (by rfl) ⟨2431538, by rfl⟩ : syracuseStep 3242051 = 4863077) B4863077
theorem B2161367 : Blo 2159435 2161367 := bstep (se 1 (by rfl) ⟨1621025, by rfl⟩ : syracuseStep 2161367 = 3242051) B3242051
theorem B5470973 : Blo 2159435 5470973 := bbase (se 3 (by rfl) ⟨1025807, by rfl⟩ : syracuseStep 5470973 = 2051615) (by norm_num)
theorem B3647315 : Blo 2159435 3647315 := bstep (se 1 (by rfl) ⟨2735486, by rfl⟩ : syracuseStep 3647315 = 5470973) B5470973
theorem B2431543 : Blo 2159435 2431543 := bstep (se 1 (by rfl) ⟨1823657, by rfl⟩ : syracuseStep 2431543 = 3647315) B3647315
theorem B3242057 : Blo 2159435 3242057 := bstep (se 2 (by rfl) ⟨1215771, by rfl⟩ : syracuseStep 3242057 = 2431543) B2431543
theorem B2161371 : Blo 2159435 2161371 := bstep (se 1 (by rfl) ⟨1621028, by rfl⟩ : syracuseStep 2161371 = 3242057) B3242057
theorem B4103237 : Blo 2159435 4103237 := bbase (se 4 (by rfl) ⟨384678, by rfl⟩ : syracuseStep 4103237 = 769357) (by norm_num)
theorem B10941965 : Blo 2159435 10941965 := bstep (se 3 (by rfl) ⟨2051618, by rfl⟩ : syracuseStep 10941965 = 4103237) B4103237
theorem B7294643 : Blo 2159435 7294643 := bstep (se 1 (by rfl) ⟨5470982, by rfl⟩ : syracuseStep 7294643 = 10941965) B10941965
theorem B4863095 : Blo 2159435 4863095 := bstep (se 1 (by rfl) ⟨3647321, by rfl⟩ : syracuseStep 4863095 = 7294643) B7294643
theorem B3242063 : Blo 2159435 3242063 := bstep (se 1 (by rfl) ⟨2431547, by rfl⟩ : syracuseStep 3242063 = 4863095) B4863095
theorem B2161375 : Blo 2159435 2161375 := bstep (se 1 (by rfl) ⟨1621031, by rfl⟩ : syracuseStep 2161375 = 3242063) B3242063
theorem B3242069 : Blo 2159435 3242069 := bbase (se 8 (by rfl) ⟨18996, by rfl⟩ : syracuseStep 3242069 = 37993) (by norm_num)
theorem B2161379 : Blo 2159435 2161379 := bstep (se 1 (by rfl) ⟨1621034, by rfl⟩ : syracuseStep 2161379 = 3242069) B3242069
theorem B5064893 : Blo 2159435 5064893 := bbase (se 3 (by rfl) ⟨949667, by rfl⟩ : syracuseStep 5064893 = 1899335) (by norm_num)
theorem B3376595 : Blo 2159435 3376595 := bstep (se 1 (by rfl) ⟨2532446, by rfl⟩ : syracuseStep 3376595 = 5064893) B5064893
theorem B2251063 : Blo 2159435 2251063 := bstep (se 1 (by rfl) ⟨1688297, by rfl⟩ : syracuseStep 2251063 = 3376595) B3376595
theorem B3001417 : Blo 2159435 3001417 := bstep (se 2 (by rfl) ⟨1125531, by rfl⟩ : syracuseStep 3001417 = 2251063) B2251063
theorem B16007557 : Blo 2159435 16007557 := bstep (se 4 (by rfl) ⟨1500708, by rfl⟩ : syracuseStep 16007557 = 3001417) B3001417
theorem B21343409 : Blo 2159435 21343409 := bstep (se 2 (by rfl) ⟨8003778, by rfl⟩ : syracuseStep 21343409 = 16007557) B16007557
theorem B14228939 : Blo 2159435 14228939 := bstep (se 1 (by rfl) ⟨10671704, by rfl⟩ : syracuseStep 14228939 = 21343409) B21343409
theorem B9485959 : Blo 2159435 9485959 := bstep (se 1 (by rfl) ⟨7114469, by rfl⟩ : syracuseStep 9485959 = 14228939) B14228939
theorem B12647945 : Blo 2159435 12647945 := bstep (se 2 (by rfl) ⟨4742979, by rfl⟩ : syracuseStep 12647945 = 9485959) B9485959
theorem B33727853 : Blo 2159435 33727853 := bstep (se 3 (by rfl) ⟨6323972, by rfl⟩ : syracuseStep 33727853 = 12647945) B12647945
theorem B22485235 : Blo 2159435 22485235 := bstep (se 1 (by rfl) ⟨16863926, by rfl⟩ : syracuseStep 22485235 = 33727853) B33727853
theorem B29980313 : Blo 2159435 29980313 := bstep (se 2 (by rfl) ⟨11242617, by rfl⟩ : syracuseStep 29980313 = 22485235) B22485235
theorem B19986875 : Blo 2159435 19986875 := bstep (se 1 (by rfl) ⟨14990156, by rfl⟩ : syracuseStep 19986875 = 29980313) B29980313
theorem B13324583 : Blo 2159435 13324583 := bstep (se 1 (by rfl) ⟨9993437, by rfl⟩ : syracuseStep 13324583 = 19986875) B19986875
theorem B8883055 : Blo 2159435 8883055 := bstep (se 1 (by rfl) ⟨6662291, by rfl⟩ : syracuseStep 8883055 = 13324583) B13324583
theorem B11844073 : Blo 2159435 11844073 := bstep (se 2 (by rfl) ⟨4441527, by rfl⟩ : syracuseStep 11844073 = 8883055) B8883055
theorem B15792097 : Blo 2159435 15792097 := bstep (se 2 (by rfl) ⟨5922036, by rfl⟩ : syracuseStep 15792097 = 11844073) B11844073
theorem B21056129 : Blo 2159435 21056129 := bstep (se 2 (by rfl) ⟨7896048, by rfl⟩ : syracuseStep 21056129 = 15792097) B15792097
theorem B14037419 : Blo 2159435 14037419 := bstep (se 1 (by rfl) ⟨10528064, by rfl⟩ : syracuseStep 14037419 = 21056129) B21056129
theorem B37433117 : Blo 2159435 37433117 := bstep (se 3 (by rfl) ⟨7018709, by rfl⟩ : syracuseStep 37433117 = 14037419) B14037419
theorem B99821645 : Blo 2159435 99821645 := bstep (se 3 (by rfl) ⟨18716558, by rfl⟩ : syracuseStep 99821645 = 37433117) B37433117
theorem B66547763 : Blo 2159435 66547763 := bstep (se 1 (by rfl) ⟨49910822, by rfl⟩ : syracuseStep 66547763 = 99821645) B99821645
theorem B44365175 : Blo 2159435 44365175 := bstep (se 1 (by rfl) ⟨33273881, by rfl⟩ : syracuseStep 44365175 = 66547763) B66547763
theorem B29576783 : Blo 2159435 29576783 := bstep (se 1 (by rfl) ⟨22182587, by rfl⟩ : syracuseStep 29576783 = 44365175) B44365175
theorem B78871421 : Blo 2159435 78871421 := bstep (se 3 (by rfl) ⟨14788391, by rfl⟩ : syracuseStep 78871421 = 29576783) B29576783
theorem B52580947 : Blo 2159435 52580947 := bstep (se 1 (by rfl) ⟨39435710, by rfl⟩ : syracuseStep 52580947 = 78871421) B78871421
theorem B70107929 : Blo 2159435 70107929 := bstep (se 2 (by rfl) ⟨26290473, by rfl⟩ : syracuseStep 70107929 = 52580947) B52580947
theorem B46738619 : Blo 2159435 46738619 := bstep (se 1 (by rfl) ⟨35053964, by rfl⟩ : syracuseStep 46738619 = 70107929) B70107929
theorem B31159079 : Blo 2159435 31159079 := bstep (se 1 (by rfl) ⟨23369309, by rfl⟩ : syracuseStep 31159079 = 46738619) B46738619
theorem B20772719 : Blo 2159435 20772719 := bstep (se 1 (by rfl) ⟨15579539, by rfl⟩ : syracuseStep 20772719 = 31159079) B31159079
theorem B13848479 : Blo 2159435 13848479 := bstep (se 1 (by rfl) ⟨10386359, by rfl⟩ : syracuseStep 13848479 = 20772719) B20772719
theorem B9232319 : Blo 2159435 9232319 := bstep (se 1 (by rfl) ⟨6924239, by rfl⟩ : syracuseStep 9232319 = 13848479) B13848479
theorem B6154879 : Blo 2159435 6154879 := bstep (se 1 (by rfl) ⟨4616159, by rfl⟩ : syracuseStep 6154879 = 9232319) B9232319
theorem B8206505 : Blo 2159435 8206505 := bstep (se 2 (by rfl) ⟨3077439, by rfl⟩ : syracuseStep 8206505 = 6154879) B6154879
theorem B5471003 : Blo 2159435 5471003 := bstep (se 1 (by rfl) ⟨4103252, by rfl⟩ : syracuseStep 5471003 = 8206505) B8206505
theorem B3647335 : Blo 2159435 3647335 := bstep (se 1 (by rfl) ⟨2735501, by rfl⟩ : syracuseStep 3647335 = 5471003) B5471003
theorem B4863113 : Blo 2159435 4863113 := bstep (se 2 (by rfl) ⟨1823667, by rfl⟩ : syracuseStep 4863113 = 3647335) B3647335
theorem B3242075 : Blo 2159435 3242075 := bstep (se 1 (by rfl) ⟨2431556, by rfl⟩ : syracuseStep 3242075 = 4863113) B4863113
theorem B2161383 : Blo 2159435 2161383 := bstep (se 1 (by rfl) ⟨1621037, by rfl⟩ : syracuseStep 2161383 = 3242075) B3242075
theorem B2431561 : Blo 2159435 2431561 := bbase (se 2 (by rfl) ⟨911835, by rfl⟩ : syracuseStep 2431561 = 1823671) (by norm_num)
theorem B3242081 : Blo 2159435 3242081 := bstep (se 2 (by rfl) ⟨1215780, by rfl⟩ : syracuseStep 3242081 = 2431561) B2431561
theorem B2161387 : Blo 2159435 2161387 := bstep (se 1 (by rfl) ⟨1621040, by rfl⟩ : syracuseStep 2161387 = 3242081) B3242081
theorem B2190881 : Blo 2159435 2190881 := bbase (se 2 (by rfl) ⟨821580, by rfl⟩ : syracuseStep 2190881 = 1643161) (by norm_num)
theorem B5842349 : Blo 2159435 5842349 := bstep (se 3 (by rfl) ⟨1095440, by rfl⟩ : syracuseStep 5842349 = 2190881) B2190881
theorem B3894899 : Blo 2159435 3894899 := bstep (se 1 (by rfl) ⟨2921174, by rfl⟩ : syracuseStep 3894899 = 5842349) B5842349
theorem B10386397 : Blo 2159435 10386397 := bstep (se 3 (by rfl) ⟨1947449, by rfl⟩ : syracuseStep 10386397 = 3894899) B3894899
theorem B13848529 : Blo 2159435 13848529 := bstep (se 2 (by rfl) ⟨5193198, by rfl⟩ : syracuseStep 13848529 = 10386397) B10386397
theorem B18464705 : Blo 2159435 18464705 := bstep (se 2 (by rfl) ⟨6924264, by rfl⟩ : syracuseStep 18464705 = 13848529) B13848529
theorem B12309803 : Blo 2159435 12309803 := bstep (se 1 (by rfl) ⟨9232352, by rfl⟩ : syracuseStep 12309803 = 18464705) B18464705
theorem B8206535 : Blo 2159435 8206535 := bstep (se 1 (by rfl) ⟨6154901, by rfl⟩ : syracuseStep 8206535 = 12309803) B12309803
theorem B5471023 : Blo 2159435 5471023 := bstep (se 1 (by rfl) ⟨4103267, by rfl⟩ : syracuseStep 5471023 = 8206535) B8206535
theorem B7294697 : Blo 2159435 7294697 := bstep (se 2 (by rfl) ⟨2735511, by rfl⟩ : syracuseStep 7294697 = 5471023) B5471023
theorem B4863131 : Blo 2159435 4863131 := bstep (se 1 (by rfl) ⟨3647348, by rfl⟩ : syracuseStep 4863131 = 7294697) B7294697
theorem B3242087 : Blo 2159435 3242087 := bstep (se 1 (by rfl) ⟨2431565, by rfl⟩ : syracuseStep 3242087 = 4863131) B4863131
theorem B2161391 : Blo 2159435 2161391 := bstep (se 1 (by rfl) ⟨1621043, by rfl⟩ : syracuseStep 2161391 = 3242087) B3242087
theorem B3242093 : Blo 2159435 3242093 := bbase (se 3 (by rfl) ⟨607892, by rfl⟩ : syracuseStep 3242093 = 1215785) (by norm_num)
theorem B2161395 : Blo 2159435 2161395 := bstep (se 1 (by rfl) ⟨1621046, by rfl⟩ : syracuseStep 2161395 = 3242093) B3242093
theorem B4863149 : Blo 2159435 4863149 := bbase (se 3 (by rfl) ⟨911840, by rfl⟩ : syracuseStep 4863149 = 1823681) (by norm_num)
theorem B3242099 : Blo 2159435 3242099 := bstep (se 1 (by rfl) ⟨2431574, by rfl⟩ : syracuseStep 3242099 = 4863149) B4863149
theorem B2161399 : Blo 2159435 2161399 := bstep (se 1 (by rfl) ⟨1621049, by rfl⟩ : syracuseStep 2161399 = 3242099) B3242099
theorem B5193229 : Blo 2159435 5193229 := bbase (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) (by norm_num)
theorem B6924305 : Blo 2159435 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B4616203 : Blo 2159435 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B6154937 : Blo 2159435 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B4103291 : Blo 2159435 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B2735527 : Blo 2159435 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B3647369 : Blo 2159435 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B2431579 : Blo 2159435 2431579 := bstep (se 1 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 2431579 = 3647369) B3647369
theorem B3242105 : Blo 2159435 3242105 := bstep (se 2 (by rfl) ⟨1215789, by rfl⟩ : syracuseStep 3242105 = 2431579) B2431579
theorem B2161403 : Blo 2159435 2161403 := bstep (se 1 (by rfl) ⟨1621052, by rfl⟩ : syracuseStep 2161403 = 3242105) B3242105
theorem B29577109 : Blo 2159435 29577109 := bbase (se 6 (by rfl) ⟨693213, by rfl⟩ : syracuseStep 29577109 = 1386427) (by norm_num)
theorem B39436145 : Blo 2159435 39436145 := bstep (se 2 (by rfl) ⟨14788554, by rfl⟩ : syracuseStep 39436145 = 29577109) B29577109
theorem B26290763 : Blo 2159435 26290763 := bstep (se 1 (by rfl) ⟨19718072, by rfl⟩ : syracuseStep 26290763 = 39436145) B39436145
theorem B17527175 : Blo 2159435 17527175 := bstep (se 1 (by rfl) ⟨13145381, by rfl⟩ : syracuseStep 17527175 = 26290763) B26290763
theorem B11684783 : Blo 2159435 11684783 := bstep (se 1 (by rfl) ⟨8763587, by rfl⟩ : syracuseStep 11684783 = 17527175) B17527175
theorem B7789855 : Blo 2159435 7789855 := bstep (se 1 (by rfl) ⟨5842391, by rfl⟩ : syracuseStep 7789855 = 11684783) B11684783
theorem B10386473 : Blo 2159435 10386473 := bstep (se 2 (by rfl) ⟨3894927, by rfl⟩ : syracuseStep 10386473 = 7789855) B7789855
theorem B27697261 : Blo 2159435 27697261 := bstep (se 3 (by rfl) ⟨5193236, by rfl⟩ : syracuseStep 27697261 = 10386473) B10386473
theorem B36929681 : Blo 2159435 36929681 := bstep (se 2 (by rfl) ⟨13848630, by rfl⟩ : syracuseStep 36929681 = 27697261) B27697261
theorem B24619787 : Blo 2159435 24619787 := bstep (se 1 (by rfl) ⟨18464840, by rfl⟩ : syracuseStep 24619787 = 36929681) B36929681
theorem B16413191 : Blo 2159435 16413191 := bstep (se 1 (by rfl) ⟨12309893, by rfl⟩ : syracuseStep 16413191 = 24619787) B24619787
theorem B10942127 : Blo 2159435 10942127 := bstep (se 1 (by rfl) ⟨8206595, by rfl⟩ : syracuseStep 10942127 = 16413191) B16413191
theorem B7294751 : Blo 2159435 7294751 := bstep (se 1 (by rfl) ⟨5471063, by rfl⟩ : syracuseStep 7294751 = 10942127) B10942127
theorem B4863167 : Blo 2159435 4863167 := bstep (se 1 (by rfl) ⟨3647375, by rfl⟩ : syracuseStep 4863167 = 7294751) B7294751
theorem B3242111 : Blo 2159435 3242111 := bstep (se 1 (by rfl) ⟨2431583, by rfl⟩ : syracuseStep 3242111 = 4863167) B4863167
theorem B2161407 : Blo 2159435 2161407 := bstep (se 1 (by rfl) ⟨1621055, by rfl⟩ : syracuseStep 2161407 = 3242111) B3242111
theorem B3242117 : Blo 2159435 3242117 := bbase (se 4 (by rfl) ⟨303948, by rfl⟩ : syracuseStep 3242117 = 607897) (by norm_num)
theorem B2161411 : Blo 2159435 2161411 := bstep (se 1 (by rfl) ⟨1621058, by rfl⟩ : syracuseStep 2161411 = 3242117) B3242117
theorem B3647389 : Blo 2159435 3647389 := bbase (se 3 (by rfl) ⟨683885, by rfl⟩ : syracuseStep 3647389 = 1367771) (by norm_num)
theorem B4863185 : Blo 2159435 4863185 := bstep (se 2 (by rfl) ⟨1823694, by rfl⟩ : syracuseStep 4863185 = 3647389) B3647389
theorem B3242123 : Blo 2159435 3242123 := bstep (se 1 (by rfl) ⟨2431592, by rfl⟩ : syracuseStep 3242123 = 4863185) B4863185
theorem B2161415 : Blo 2159435 2161415 := bstep (se 1 (by rfl) ⟨1621061, by rfl⟩ : syracuseStep 2161415 = 3242123) B3242123
theorem B2431597 : Blo 2159435 2431597 := bbase (se 3 (by rfl) ⟨455924, by rfl⟩ : syracuseStep 2431597 = 911849) (by norm_num)
theorem B3242129 : Blo 2159435 3242129 := bstep (se 2 (by rfl) ⟨1215798, by rfl⟩ : syracuseStep 3242129 = 2431597) B2431597
theorem B2161419 : Blo 2159435 2161419 := bstep (se 1 (by rfl) ⟨1621064, by rfl⟩ : syracuseStep 2161419 = 3242129) B3242129
theorem B7294805 : Blo 2159435 7294805 := bbase (se 9 (by rfl) ⟨21371, by rfl⟩ : syracuseStep 7294805 = 42743) (by norm_num)
theorem B4863203 : Blo 2159435 4863203 := bstep (se 1 (by rfl) ⟨3647402, by rfl⟩ : syracuseStep 4863203 = 7294805) B7294805
theorem B3242135 : Blo 2159435 3242135 := bstep (se 1 (by rfl) ⟨2431601, by rfl⟩ : syracuseStep 3242135 = 4863203) B4863203
theorem B2161423 : Blo 2159435 2161423 := bstep (se 1 (by rfl) ⟨1621067, by rfl⟩ : syracuseStep 2161423 = 3242135) B3242135
theorem B3242141 : Blo 2159435 3242141 := bbase (se 3 (by rfl) ⟨607901, by rfl⟩ : syracuseStep 3242141 = 1215803) (by norm_num)
theorem B2161427 : Blo 2159435 2161427 := bstep (se 1 (by rfl) ⟨1621070, by rfl⟩ : syracuseStep 2161427 = 3242141) B3242141
theorem B4863221 : Blo 2159435 4863221 := bbase (se 5 (by rfl) ⟨227963, by rfl⟩ : syracuseStep 4863221 = 455927) (by norm_num)
theorem B3242147 : Blo 2159435 3242147 := bstep (se 1 (by rfl) ⟨2431610, by rfl⟩ : syracuseStep 3242147 = 4863221) B4863221
theorem B2161431 : Blo 2159435 2161431 := bstep (se 1 (by rfl) ⟨1621073, by rfl⟩ : syracuseStep 2161431 = 3242147) B3242147
theorem B31159829 : Blo 2159435 31159829 := bbase (se 6 (by rfl) ⟨730308, by rfl⟩ : syracuseStep 31159829 = 1460617) (by norm_num)
theorem B20773219 : Blo 2159435 20773219 := bstep (se 1 (by rfl) ⟨15579914, by rfl⟩ : syracuseStep 20773219 = 31159829) B31159829
theorem B27697625 : Blo 2159435 27697625 := bstep (se 2 (by rfl) ⟨10386609, by rfl⟩ : syracuseStep 27697625 = 20773219) B20773219
theorem B18465083 : Blo 2159435 18465083 := bstep (se 1 (by rfl) ⟨13848812, by rfl⟩ : syracuseStep 18465083 = 27697625) B27697625
theorem B12310055 : Blo 2159435 12310055 := bstep (se 1 (by rfl) ⟨9232541, by rfl⟩ : syracuseStep 12310055 = 18465083) B18465083
theorem B8206703 : Blo 2159435 8206703 := bstep (se 1 (by rfl) ⟨6155027, by rfl⟩ : syracuseStep 8206703 = 12310055) B12310055
theorem B5471135 : Blo 2159435 5471135 := bstep (se 1 (by rfl) ⟨4103351, by rfl⟩ : syracuseStep 5471135 = 8206703) B8206703
theorem B3647423 : Blo 2159435 3647423 := bstep (se 1 (by rfl) ⟨2735567, by rfl⟩ : syracuseStep 3647423 = 5471135) B5471135
theorem B2431615 : Blo 2159435 2431615 := bstep (se 1 (by rfl) ⟨1823711, by rfl⟩ : syracuseStep 2431615 = 3647423) B3647423
theorem B3242153 : Blo 2159435 3242153 := bstep (se 2 (by rfl) ⟨1215807, by rfl⟩ : syracuseStep 3242153 = 2431615) B2431615
theorem B2161435 : Blo 2159435 2161435 := bstep (se 1 (by rfl) ⟨1621076, by rfl⟩ : syracuseStep 2161435 = 3242153) B3242153
theorem C0 (j : ℕ) (h1 : 539858 ≤ j) (h2 : j ≤ 540358) : Blo 2159435 (4 * j + 3) := by
  interval_cases j
  · exact B2159435
  · exact B2159439
  · exact B2159443
  · exact B2159447
  · exact B2159451
  · exact B2159455
  · exact B2159459
  · exact B2159463
  · exact B2159467
  · exact B2159471
  · exact B2159475
  · exact B2159479
  · exact B2159483
  · exact B2159487
  · exact B2159491
  · exact B2159495
  · exact B2159499
  · exact B2159503
  · exact B2159507
  · exact B2159511
  · exact B2159515
  · exact B2159519
  · exact B2159523
  · exact B2159527
  · exact B2159531
  · exact B2159535
  · exact B2159539
  · exact B2159543
  · exact B2159547
  · exact B2159551
  · exact B2159555
  · exact B2159559
  · exact B2159563
  · exact B2159567
  · exact B2159571
  · exact B2159575
  · exact B2159579
  · exact B2159583
  · exact B2159587
  · exact B2159591
  · exact B2159595
  · exact B2159599
  · exact B2159603
  · exact B2159607
  · exact B2159611
  · exact B2159615
  · exact B2159619
  · exact B2159623
  · exact B2159627
  · exact B2159631
  · exact B2159635
  · exact B2159639
  · exact B2159643
  · exact B2159647
  · exact B2159651
  · exact B2159655
  · exact B2159659
  · exact B2159663
  · exact B2159667
  · exact B2159671
  · exact B2159675
  · exact B2159679
  · exact B2159683
  · exact B2159687
  · exact B2159691
  · exact B2159695
  · exact B2159699
  · exact B2159703
  · exact B2159707
  · exact B2159711
  · exact B2159715
  · exact B2159719
  · exact B2159723
  · exact B2159727
  · exact B2159731
  · exact B2159735
  · exact B2159739
  · exact B2159743
  · exact B2159747
  · exact B2159751
  · exact B2159755
  · exact B2159759
  · exact B2159763
  · exact B2159767
  · exact B2159771
  · exact B2159775
  · exact B2159779
  · exact B2159783
  · exact B2159787
  · exact B2159791
  · exact B2159795
  · exact B2159799
  · exact B2159803
  · exact B2159807
  · exact B2159811
  · exact B2159815
  · exact B2159819
  · exact B2159823
  · exact B2159827
  · exact B2159831
  · exact B2159835
  · exact B2159839
  · exact B2159843
  · exact B2159847
  · exact B2159851
  · exact B2159855
  · exact B2159859
  · exact B2159863
  · exact B2159867
  · exact B2159871
  · exact B2159875
  · exact B2159879
  · exact B2159883
  · exact B2159887
  · exact B2159891
  · exact B2159895
  · exact B2159899
  · exact B2159903
  · exact B2159907
  · exact B2159911
  · exact B2159915
  · exact B2159919
  · exact B2159923
  · exact B2159927
  · exact B2159931
  · exact B2159935
  · exact B2159939
  · exact B2159943
  · exact B2159947
  · exact B2159951
  · exact B2159955
  · exact B2159959
  · exact B2159963
  · exact B2159967
  · exact B2159971
  · exact B2159975
  · exact B2159979
  · exact B2159983
  · exact B2159987
  · exact B2159991
  · exact B2159995
  · exact B2159999
  · exact B2160003
  · exact B2160007
  · exact B2160011
  · exact B2160015
  · exact B2160019
  · exact B2160023
  · exact B2160027
  · exact B2160031
  · exact B2160035
  · exact B2160039
  · exact B2160043
  · exact B2160047
  · exact B2160051
  · exact B2160055
  · exact B2160059
  · exact B2160063
  · exact B2160067
  · exact B2160071
  · exact B2160075
  · exact B2160079
  · exact B2160083
  · exact B2160087
  · exact B2160091
  · exact B2160095
  · exact B2160099
  · exact B2160103
  · exact B2160107
  · exact B2160111
  · exact B2160115
  · exact B2160119
  · exact B2160123
  · exact B2160127
  · exact B2160131
  · exact B2160135
  · exact B2160139
  · exact B2160143
  · exact B2160147
  · exact B2160151
  · exact B2160155
  · exact B2160159
  · exact B2160163
  · exact B2160167
  · exact B2160171
  · exact B2160175
  · exact B2160179
  · exact B2160183
  · exact B2160187
  · exact B2160191
  · exact B2160195
  · exact B2160199
  · exact B2160203
  · exact B2160207
  · exact B2160211
  · exact B2160215
  · exact B2160219
  · exact B2160223
  · exact B2160227
  · exact B2160231
  · exact B2160235
  · exact B2160239
  · exact B2160243
  · exact B2160247
  · exact B2160251
  · exact B2160255
  · exact B2160259
  · exact B2160263
  · exact B2160267
  · exact B2160271
  · exact B2160275
  · exact B2160279
  · exact B2160283
  · exact B2160287
  · exact B2160291
  · exact B2160295
  · exact B2160299
  · exact B2160303
  · exact B2160307
  · exact B2160311
  · exact B2160315
  · exact B2160319
  · exact B2160323
  · exact B2160327
  · exact B2160331
  · exact B2160335
  · exact B2160339
  · exact B2160343
  · exact B2160347
  · exact B2160351
  · exact B2160355
  · exact B2160359
  · exact B2160363
  · exact B2160367
  · exact B2160371
  · exact B2160375
  · exact B2160379
  · exact B2160383
  · exact B2160387
  · exact B2160391
  · exact B2160395
  · exact B2160399
  · exact B2160403
  · exact B2160407
  · exact B2160411
  · exact B2160415
  · exact B2160419
  · exact B2160423
  · exact B2160427
  · exact B2160431
  · exact B2160435
  · exact B2160439
  · exact B2160443
  · exact B2160447
  · exact B2160451
  · exact B2160455
  · exact B2160459
  · exact B2160463
  · exact B2160467
  · exact B2160471
  · exact B2160475
  · exact B2160479
  · exact B2160483
  · exact B2160487
  · exact B2160491
  · exact B2160495
  · exact B2160499
  · exact B2160503
  · exact B2160507
  · exact B2160511
  · exact B2160515
  · exact B2160519
  · exact B2160523
  · exact B2160527
  · exact B2160531
  · exact B2160535
  · exact B2160539
  · exact B2160543
  · exact B2160547
  · exact B2160551
  · exact B2160555
  · exact B2160559
  · exact B2160563
  · exact B2160567
  · exact B2160571
  · exact B2160575
  · exact B2160579
  · exact B2160583
  · exact B2160587
  · exact B2160591
  · exact B2160595
  · exact B2160599
  · exact B2160603
  · exact B2160607
  · exact B2160611
  · exact B2160615
  · exact B2160619
  · exact B2160623
  · exact B2160627
  · exact B2160631
  · exact B2160635
  · exact B2160639
  · exact B2160643
  · exact B2160647
  · exact B2160651
  · exact B2160655
  · exact B2160659
  · exact B2160663
  · exact B2160667
  · exact B2160671
  · exact B2160675
  · exact B2160679
  · exact B2160683
  · exact B2160687
  · exact B2160691
  · exact B2160695
  · exact B2160699
  · exact B2160703
  · exact B2160707
  · exact B2160711
  · exact B2160715
  · exact B2160719
  · exact B2160723
  · exact B2160727
  · exact B2160731
  · exact B2160735
  · exact B2160739
  · exact B2160743
  · exact B2160747
  · exact B2160751
  · exact B2160755
  · exact B2160759
  · exact B2160763
  · exact B2160767
  · exact B2160771
  · exact B2160775
  · exact B2160779
  · exact B2160783
  · exact B2160787
  · exact B2160791
  · exact B2160795
  · exact B2160799
  · exact B2160803
  · exact B2160807
  · exact B2160811
  · exact B2160815
  · exact B2160819
  · exact B2160823
  · exact B2160827
  · exact B2160831
  · exact B2160835
  · exact B2160839
  · exact B2160843
  · exact B2160847
  · exact B2160851
  · exact B2160855
  · exact B2160859
  · exact B2160863
  · exact B2160867
  · exact B2160871
  · exact B2160875
  · exact B2160879
  · exact B2160883
  · exact B2160887
  · exact B2160891
  · exact B2160895
  · exact B2160899
  · exact B2160903
  · exact B2160907
  · exact B2160911
  · exact B2160915
  · exact B2160919
  · exact B2160923
  · exact B2160927
  · exact B2160931
  · exact B2160935
  · exact B2160939
  · exact B2160943
  · exact B2160947
  · exact B2160951
  · exact B2160955
  · exact B2160959
  · exact B2160963
  · exact B2160967
  · exact B2160971
  · exact B2160975
  · exact B2160979
  · exact B2160983
  · exact B2160987
  · exact B2160991
  · exact B2160995
  · exact B2160999
  · exact B2161003
  · exact B2161007
  · exact B2161011
  · exact B2161015
  · exact B2161019
  · exact B2161023
  · exact B2161027
  · exact B2161031
  · exact B2161035
  · exact B2161039
  · exact B2161043
  · exact B2161047
  · exact B2161051
  · exact B2161055
  · exact B2161059
  · exact B2161063
  · exact B2161067
  · exact B2161071
  · exact B2161075
  · exact B2161079
  · exact B2161083
  · exact B2161087
  · exact B2161091
  · exact B2161095
  · exact B2161099
  · exact B2161103
  · exact B2161107
  · exact B2161111
  · exact B2161115
  · exact B2161119
  · exact B2161123
  · exact B2161127
  · exact B2161131
  · exact B2161135
  · exact B2161139
  · exact B2161143
  · exact B2161147
  · exact B2161151
  · exact B2161155
  · exact B2161159
  · exact B2161163
  · exact B2161167
  · exact B2161171
  · exact B2161175
  · exact B2161179
  · exact B2161183
  · exact B2161187
  · exact B2161191
  · exact B2161195
  · exact B2161199
  · exact B2161203
  · exact B2161207
  · exact B2161211
  · exact B2161215
  · exact B2161219
  · exact B2161223
  · exact B2161227
  · exact B2161231
  · exact B2161235
  · exact B2161239
  · exact B2161243
  · exact B2161247
  · exact B2161251
  · exact B2161255
  · exact B2161259
  · exact B2161263
  · exact B2161267
  · exact B2161271
  · exact B2161275
  · exact B2161279
  · exact B2161283
  · exact B2161287
  · exact B2161291
  · exact B2161295
  · exact B2161299
  · exact B2161303
  · exact B2161307
  · exact B2161311
  · exact B2161315
  · exact B2161319
  · exact B2161323
  · exact B2161327
  · exact B2161331
  · exact B2161335
  · exact B2161339
  · exact B2161343
  · exact B2161347
  · exact B2161351
  · exact B2161355
  · exact B2161359
  · exact B2161363
  · exact B2161367
  · exact B2161371
  · exact B2161375
  · exact B2161379
  · exact B2161383
  · exact B2161387
  · exact B2161391
  · exact B2161395
  · exact B2161399
  · exact B2161403
  · exact B2161407
  · exact B2161411
  · exact B2161415
  · exact B2161419
  · exact B2161423
  · exact B2161427
  · exact B2161431
  · exact B2161435
theorem solution (m : ℕ) (hlo : 2159435 ≤ m) (hhi : m ≤ 2161435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 539858 ≤ j := by omega
    have hj2 : j ≤ 540358 := by omega
    have hb : Blo 2159435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
