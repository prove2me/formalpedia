-- Prove2me | solution 1 for syracuse_descends_range_2057435_2059435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:33.55306+00:00
-- url     : https://prove2.me/submissions/5ba74a5a-68ad-4a83-9ab4-3ce456bacb28

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

theorem B5207885 : Blo 2057435 5207885 := bbase (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) (by norm_num)
theorem B3471923 : Blo 2057435 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B2314615 : Blo 2057435 2314615 := bstep (se 1 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 2314615 = 3471923) B3471923
theorem B3086153 : Blo 2057435 3086153 := bstep (se 2 (by rfl) ⟨1157307, by rfl⟩ : syracuseStep 3086153 = 2314615) B2314615
theorem B2057435 : Blo 2057435 2057435 := bstep (se 1 (by rfl) ⟨1543076, by rfl⟩ : syracuseStep 2057435 = 3086153) B3086153
theorem B2197081 : Blo 2057435 2197081 := bbase (se 2 (by rfl) ⟨823905, by rfl⟩ : syracuseStep 2197081 = 1647811) (by norm_num)
theorem B2929441 : Blo 2057435 2929441 := bstep (se 2 (by rfl) ⟨1098540, by rfl⟩ : syracuseStep 2929441 = 2197081) B2197081
theorem B3905921 : Blo 2057435 3905921 := bstep (se 2 (by rfl) ⟨1464720, by rfl⟩ : syracuseStep 3905921 = 2929441) B2929441
theorem B10415789 : Blo 2057435 10415789 := bstep (se 3 (by rfl) ⟨1952960, by rfl⟩ : syracuseStep 10415789 = 3905921) B3905921
theorem B6943859 : Blo 2057435 6943859 := bstep (se 1 (by rfl) ⟨5207894, by rfl⟩ : syracuseStep 6943859 = 10415789) B10415789
theorem B4629239 : Blo 2057435 4629239 := bstep (se 1 (by rfl) ⟨3471929, by rfl⟩ : syracuseStep 4629239 = 6943859) B6943859
theorem B3086159 : Blo 2057435 3086159 := bstep (se 1 (by rfl) ⟨2314619, by rfl⟩ : syracuseStep 3086159 = 4629239) B4629239
theorem B2057439 : Blo 2057435 2057439 := bstep (se 1 (by rfl) ⟨1543079, by rfl⟩ : syracuseStep 2057439 = 3086159) B3086159
theorem B3086165 : Blo 2057435 3086165 := bbase (se 9 (by rfl) ⟨9041, by rfl⟩ : syracuseStep 3086165 = 18083) (by norm_num)
theorem B2057443 : Blo 2057435 2057443 := bstep (se 1 (by rfl) ⟨1543082, by rfl⟩ : syracuseStep 2057443 = 3086165) B3086165
theorem B6591269 : Blo 2057435 6591269 := bbase (se 4 (by rfl) ⟨617931, by rfl⟩ : syracuseStep 6591269 = 1235863) (by norm_num)
theorem B4394179 : Blo 2057435 4394179 := bstep (se 1 (by rfl) ⟨3295634, by rfl⟩ : syracuseStep 4394179 = 6591269) B6591269
theorem B5858905 : Blo 2057435 5858905 := bstep (se 2 (by rfl) ⟨2197089, by rfl⟩ : syracuseStep 5858905 = 4394179) B4394179
theorem B7811873 : Blo 2057435 7811873 := bstep (se 2 (by rfl) ⟨2929452, by rfl⟩ : syracuseStep 7811873 = 5858905) B5858905
theorem B5207915 : Blo 2057435 5207915 := bstep (se 1 (by rfl) ⟨3905936, by rfl⟩ : syracuseStep 5207915 = 7811873) B7811873
theorem B3471943 : Blo 2057435 3471943 := bstep (se 1 (by rfl) ⟨2603957, by rfl⟩ : syracuseStep 3471943 = 5207915) B5207915
theorem B4629257 : Blo 2057435 4629257 := bstep (se 2 (by rfl) ⟨1735971, by rfl⟩ : syracuseStep 4629257 = 3471943) B3471943
theorem B3086171 : Blo 2057435 3086171 := bstep (se 1 (by rfl) ⟨2314628, by rfl⟩ : syracuseStep 3086171 = 4629257) B4629257
theorem B2057447 : Blo 2057435 2057447 := bstep (se 1 (by rfl) ⟨1543085, by rfl⟩ : syracuseStep 2057447 = 3086171) B3086171
theorem B2314633 : Blo 2057435 2314633 := bbase (se 2 (by rfl) ⟨867987, by rfl⟩ : syracuseStep 2314633 = 1735975) (by norm_num)
theorem B3086177 : Blo 2057435 3086177 := bstep (se 2 (by rfl) ⟨1157316, by rfl⟩ : syracuseStep 3086177 = 2314633) B2314633
theorem B2057451 : Blo 2057435 2057451 := bstep (se 1 (by rfl) ⟨1543088, by rfl⟩ : syracuseStep 2057451 = 3086177) B3086177
theorem B16684213 : Blo 2057435 16684213 := bbase (se 5 (by rfl) ⟨782072, by rfl⟩ : syracuseStep 16684213 = 1564145) (by norm_num)
theorem B22245617 : Blo 2057435 22245617 := bstep (se 2 (by rfl) ⟨8342106, by rfl⟩ : syracuseStep 22245617 = 16684213) B16684213
theorem B59321645 : Blo 2057435 59321645 := bstep (se 3 (by rfl) ⟨11122808, by rfl⟩ : syracuseStep 59321645 = 22245617) B22245617
theorem B39547763 : Blo 2057435 39547763 := bstep (se 1 (by rfl) ⟨29660822, by rfl⟩ : syracuseStep 39547763 = 59321645) B59321645
theorem B26365175 : Blo 2057435 26365175 := bstep (se 1 (by rfl) ⟨19773881, by rfl⟩ : syracuseStep 26365175 = 39547763) B39547763
theorem B17576783 : Blo 2057435 17576783 := bstep (se 1 (by rfl) ⟨13182587, by rfl⟩ : syracuseStep 17576783 = 26365175) B26365175
theorem B11717855 : Blo 2057435 11717855 := bstep (se 1 (by rfl) ⟨8788391, by rfl⟩ : syracuseStep 11717855 = 17576783) B17576783
theorem B7811903 : Blo 2057435 7811903 := bstep (se 1 (by rfl) ⟨5858927, by rfl⟩ : syracuseStep 7811903 = 11717855) B11717855
theorem B5207935 : Blo 2057435 5207935 := bstep (se 1 (by rfl) ⟨3905951, by rfl⟩ : syracuseStep 5207935 = 7811903) B7811903
theorem B6943913 : Blo 2057435 6943913 := bstep (se 2 (by rfl) ⟨2603967, by rfl⟩ : syracuseStep 6943913 = 5207935) B5207935
theorem B4629275 : Blo 2057435 4629275 := bstep (se 1 (by rfl) ⟨3471956, by rfl⟩ : syracuseStep 4629275 = 6943913) B6943913
theorem B3086183 : Blo 2057435 3086183 := bstep (se 1 (by rfl) ⟨2314637, by rfl⟩ : syracuseStep 3086183 = 4629275) B4629275
theorem B2057455 : Blo 2057435 2057455 := bstep (se 1 (by rfl) ⟨1543091, by rfl⟩ : syracuseStep 2057455 = 3086183) B3086183
theorem B3086189 : Blo 2057435 3086189 := bbase (se 3 (by rfl) ⟨578660, by rfl⟩ : syracuseStep 3086189 = 1157321) (by norm_num)
theorem B2057459 : Blo 2057435 2057459 := bstep (se 1 (by rfl) ⟨1543094, by rfl⟩ : syracuseStep 2057459 = 3086189) B3086189
theorem B4629293 : Blo 2057435 4629293 := bbase (se 3 (by rfl) ⟨867992, by rfl⟩ : syracuseStep 4629293 = 1735985) (by norm_num)
theorem B3086195 : Blo 2057435 3086195 := bstep (se 1 (by rfl) ⟨2314646, by rfl⟩ : syracuseStep 3086195 = 4629293) B4629293
theorem B2057463 : Blo 2057435 2057463 := bstep (se 1 (by rfl) ⟨1543097, by rfl⟩ : syracuseStep 2057463 = 3086195) B3086195
theorem B4943501 : Blo 2057435 4943501 := bbase (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) (by norm_num)
theorem B3295667 : Blo 2057435 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B8788445 : Blo 2057435 8788445 := bstep (se 3 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 8788445 = 3295667) B3295667
theorem B5858963 : Blo 2057435 5858963 := bstep (se 1 (by rfl) ⟨4394222, by rfl⟩ : syracuseStep 5858963 = 8788445) B8788445
theorem B3905975 : Blo 2057435 3905975 := bstep (se 1 (by rfl) ⟨2929481, by rfl⟩ : syracuseStep 3905975 = 5858963) B5858963
theorem B2603983 : Blo 2057435 2603983 := bstep (se 1 (by rfl) ⟨1952987, by rfl⟩ : syracuseStep 2603983 = 3905975) B3905975
theorem B3471977 : Blo 2057435 3471977 := bstep (se 2 (by rfl) ⟨1301991, by rfl⟩ : syracuseStep 3471977 = 2603983) B2603983
theorem B2314651 : Blo 2057435 2314651 := bstep (se 1 (by rfl) ⟨1735988, by rfl⟩ : syracuseStep 2314651 = 3471977) B3471977
theorem B3086201 : Blo 2057435 3086201 := bstep (se 2 (by rfl) ⟨1157325, by rfl⟩ : syracuseStep 3086201 = 2314651) B2314651
theorem B2057467 : Blo 2057435 2057467 := bstep (se 1 (by rfl) ⟨1543100, by rfl⟩ : syracuseStep 2057467 = 3086201) B3086201
theorem B2113997 : Blo 2057435 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B5637325 : Blo 2057435 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B7516433 : Blo 2057435 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B20043821 : Blo 2057435 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B53450189 : Blo 2057435 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B35633459 : Blo 2057435 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B23755639 : Blo 2057435 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B31674185 : Blo 2057435 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B21116123 : Blo 2057435 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B14077415 : Blo 2057435 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B37539773 : Blo 2057435 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B25026515 : Blo 2057435 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B16684343 : Blo 2057435 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B11122895 : Blo 2057435 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B7415263 : Blo 2057435 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B9887017 : Blo 2057435 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B13182689 : Blo 2057435 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B35153837 : Blo 2057435 35153837 := bstep (se 3 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 35153837 = 13182689) B13182689
theorem B23435891 : Blo 2057435 23435891 := bstep (se 1 (by rfl) ⟨17576918, by rfl⟩ : syracuseStep 23435891 = 35153837) B35153837
theorem B15623927 : Blo 2057435 15623927 := bstep (se 1 (by rfl) ⟨11717945, by rfl⟩ : syracuseStep 15623927 = 23435891) B23435891
theorem B10415951 : Blo 2057435 10415951 := bstep (se 1 (by rfl) ⟨7811963, by rfl⟩ : syracuseStep 10415951 = 15623927) B15623927
theorem B6943967 : Blo 2057435 6943967 := bstep (se 1 (by rfl) ⟨5207975, by rfl⟩ : syracuseStep 6943967 = 10415951) B10415951
theorem B4629311 : Blo 2057435 4629311 := bstep (se 1 (by rfl) ⟨3471983, by rfl⟩ : syracuseStep 4629311 = 6943967) B6943967
theorem B3086207 : Blo 2057435 3086207 := bstep (se 1 (by rfl) ⟨2314655, by rfl⟩ : syracuseStep 3086207 = 4629311) B4629311
theorem B2057471 : Blo 2057435 2057471 := bstep (se 1 (by rfl) ⟨1543103, by rfl⟩ : syracuseStep 2057471 = 3086207) B3086207
theorem B3086213 : Blo 2057435 3086213 := bbase (se 4 (by rfl) ⟨289332, by rfl⟩ : syracuseStep 3086213 = 578665) (by norm_num)
theorem B2057475 : Blo 2057435 2057475 := bstep (se 1 (by rfl) ⟨1543106, by rfl⟩ : syracuseStep 2057475 = 3086213) B3086213
theorem B3471997 : Blo 2057435 3471997 := bbase (se 3 (by rfl) ⟨650999, by rfl⟩ : syracuseStep 3471997 = 1301999) (by norm_num)
theorem B4629329 : Blo 2057435 4629329 := bstep (se 2 (by rfl) ⟨1735998, by rfl⟩ : syracuseStep 4629329 = 3471997) B3471997
theorem B3086219 : Blo 2057435 3086219 := bstep (se 1 (by rfl) ⟨2314664, by rfl⟩ : syracuseStep 3086219 = 4629329) B4629329
theorem B2057479 : Blo 2057435 2057479 := bstep (se 1 (by rfl) ⟨1543109, by rfl⟩ : syracuseStep 2057479 = 3086219) B3086219
theorem B2314669 : Blo 2057435 2314669 := bbase (se 3 (by rfl) ⟨434000, by rfl⟩ : syracuseStep 2314669 = 868001) (by norm_num)
theorem B3086225 : Blo 2057435 3086225 := bstep (se 2 (by rfl) ⟨1157334, by rfl⟩ : syracuseStep 3086225 = 2314669) B2314669
theorem B2057483 : Blo 2057435 2057483 := bstep (se 1 (by rfl) ⟨1543112, by rfl⟩ : syracuseStep 2057483 = 3086225) B3086225
theorem B6944021 : Blo 2057435 6944021 := bbase (se 6 (by rfl) ⟨162750, by rfl⟩ : syracuseStep 6944021 = 325501) (by norm_num)
theorem B4629347 : Blo 2057435 4629347 := bstep (se 1 (by rfl) ⟨3472010, by rfl⟩ : syracuseStep 4629347 = 6944021) B6944021
theorem B3086231 : Blo 2057435 3086231 := bstep (se 1 (by rfl) ⟨2314673, by rfl⟩ : syracuseStep 3086231 = 4629347) B4629347
theorem B2057487 : Blo 2057435 2057487 := bstep (se 1 (by rfl) ⟨1543115, by rfl⟩ : syracuseStep 2057487 = 3086231) B3086231
theorem B3086237 : Blo 2057435 3086237 := bbase (se 3 (by rfl) ⟨578669, by rfl⟩ : syracuseStep 3086237 = 1157339) (by norm_num)
theorem B2057491 : Blo 2057435 2057491 := bstep (se 1 (by rfl) ⟨1543118, by rfl⟩ : syracuseStep 2057491 = 3086237) B3086237
theorem B4629365 : Blo 2057435 4629365 := bbase (se 5 (by rfl) ⟨217001, by rfl⟩ : syracuseStep 4629365 = 434003) (by norm_num)
theorem B3086243 : Blo 2057435 3086243 := bstep (se 1 (by rfl) ⟨2314682, by rfl⟩ : syracuseStep 3086243 = 4629365) B4629365
theorem B2057495 : Blo 2057435 2057495 := bstep (se 1 (by rfl) ⟨1543121, by rfl⟩ : syracuseStep 2057495 = 3086243) B3086243
theorem B29661461 : Blo 2057435 29661461 := bbase (se 6 (by rfl) ⟨695190, by rfl⟩ : syracuseStep 29661461 = 1390381) (by norm_num)
theorem B19774307 : Blo 2057435 19774307 := bstep (se 1 (by rfl) ⟨14830730, by rfl⟩ : syracuseStep 19774307 = 29661461) B29661461
theorem B13182871 : Blo 2057435 13182871 := bstep (se 1 (by rfl) ⟨9887153, by rfl⟩ : syracuseStep 13182871 = 19774307) B19774307
theorem B17577161 : Blo 2057435 17577161 := bstep (se 2 (by rfl) ⟨6591435, by rfl⟩ : syracuseStep 17577161 = 13182871) B13182871
theorem B11718107 : Blo 2057435 11718107 := bstep (se 1 (by rfl) ⟨8788580, by rfl⟩ : syracuseStep 11718107 = 17577161) B17577161
theorem B7812071 : Blo 2057435 7812071 := bstep (se 1 (by rfl) ⟨5859053, by rfl⟩ : syracuseStep 7812071 = 11718107) B11718107
theorem B5208047 : Blo 2057435 5208047 := bstep (se 1 (by rfl) ⟨3906035, by rfl⟩ : syracuseStep 5208047 = 7812071) B7812071
theorem B3472031 : Blo 2057435 3472031 := bstep (se 1 (by rfl) ⟨2604023, by rfl⟩ : syracuseStep 3472031 = 5208047) B5208047
theorem B2314687 : Blo 2057435 2314687 := bstep (se 1 (by rfl) ⟨1736015, by rfl⟩ : syracuseStep 2314687 = 3472031) B3472031
theorem B3086249 : Blo 2057435 3086249 := bstep (se 2 (by rfl) ⟨1157343, by rfl⟩ : syracuseStep 3086249 = 2314687) B2314687
theorem B2057499 : Blo 2057435 2057499 := bstep (se 1 (by rfl) ⟨1543124, by rfl⟩ : syracuseStep 2057499 = 3086249) B3086249
theorem B7812085 : Blo 2057435 7812085 := bbase (se 5 (by rfl) ⟨366191, by rfl⟩ : syracuseStep 7812085 = 732383) (by norm_num)
theorem B10416113 : Blo 2057435 10416113 := bstep (se 2 (by rfl) ⟨3906042, by rfl⟩ : syracuseStep 10416113 = 7812085) B7812085
theorem B6944075 : Blo 2057435 6944075 := bstep (se 1 (by rfl) ⟨5208056, by rfl⟩ : syracuseStep 6944075 = 10416113) B10416113
theorem B4629383 : Blo 2057435 4629383 := bstep (se 1 (by rfl) ⟨3472037, by rfl⟩ : syracuseStep 4629383 = 6944075) B6944075
theorem B3086255 : Blo 2057435 3086255 := bstep (se 1 (by rfl) ⟨2314691, by rfl⟩ : syracuseStep 3086255 = 4629383) B4629383
theorem B2057503 : Blo 2057435 2057503 := bstep (se 1 (by rfl) ⟨1543127, by rfl⟩ : syracuseStep 2057503 = 3086255) B3086255
theorem B3086261 : Blo 2057435 3086261 := bbase (se 5 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 3086261 = 289337) (by norm_num)
theorem B2057507 : Blo 2057435 2057507 := bstep (se 1 (by rfl) ⟨1543130, by rfl⟩ : syracuseStep 2057507 = 3086261) B3086261
theorem B5208077 : Blo 2057435 5208077 := bbase (se 3 (by rfl) ⟨976514, by rfl⟩ : syracuseStep 5208077 = 1953029) (by norm_num)
theorem B3472051 : Blo 2057435 3472051 := bstep (se 1 (by rfl) ⟨2604038, by rfl⟩ : syracuseStep 3472051 = 5208077) B5208077
theorem B4629401 : Blo 2057435 4629401 := bstep (se 2 (by rfl) ⟨1736025, by rfl⟩ : syracuseStep 4629401 = 3472051) B3472051
theorem B3086267 : Blo 2057435 3086267 := bstep (se 1 (by rfl) ⟨2314700, by rfl⟩ : syracuseStep 3086267 = 4629401) B4629401
theorem B2057511 : Blo 2057435 2057511 := bstep (se 1 (by rfl) ⟨1543133, by rfl⟩ : syracuseStep 2057511 = 3086267) B3086267
theorem B2314705 : Blo 2057435 2314705 := bbase (se 2 (by rfl) ⟨868014, by rfl⟩ : syracuseStep 2314705 = 1736029) (by norm_num)
theorem B3086273 : Blo 2057435 3086273 := bstep (se 2 (by rfl) ⟨1157352, by rfl⟩ : syracuseStep 3086273 = 2314705) B2314705
theorem B2057515 : Blo 2057435 2057515 := bstep (se 1 (by rfl) ⟨1543136, by rfl⟩ : syracuseStep 2057515 = 3086273) B3086273
theorem B4394333 : Blo 2057435 4394333 := bbase (se 3 (by rfl) ⟨823937, by rfl⟩ : syracuseStep 4394333 = 1647875) (by norm_num)
theorem B2929555 : Blo 2057435 2929555 := bstep (se 1 (by rfl) ⟨2197166, by rfl⟩ : syracuseStep 2929555 = 4394333) B4394333
theorem B3906073 : Blo 2057435 3906073 := bstep (se 2 (by rfl) ⟨1464777, by rfl⟩ : syracuseStep 3906073 = 2929555) B2929555
theorem B5208097 : Blo 2057435 5208097 := bstep (se 2 (by rfl) ⟨1953036, by rfl⟩ : syracuseStep 5208097 = 3906073) B3906073
theorem B6944129 : Blo 2057435 6944129 := bstep (se 2 (by rfl) ⟨2604048, by rfl⟩ : syracuseStep 6944129 = 5208097) B5208097
theorem B4629419 : Blo 2057435 4629419 := bstep (se 1 (by rfl) ⟨3472064, by rfl⟩ : syracuseStep 4629419 = 6944129) B6944129
theorem B3086279 : Blo 2057435 3086279 := bstep (se 1 (by rfl) ⟨2314709, by rfl⟩ : syracuseStep 3086279 = 4629419) B4629419
theorem B2057519 : Blo 2057435 2057519 := bstep (se 1 (by rfl) ⟨1543139, by rfl⟩ : syracuseStep 2057519 = 3086279) B3086279
theorem B3086285 : Blo 2057435 3086285 := bbase (se 3 (by rfl) ⟨578678, by rfl⟩ : syracuseStep 3086285 = 1157357) (by norm_num)
theorem B2057523 : Blo 2057435 2057523 := bstep (se 1 (by rfl) ⟨1543142, by rfl⟩ : syracuseStep 2057523 = 3086285) B3086285
theorem B4629437 : Blo 2057435 4629437 := bbase (se 3 (by rfl) ⟨868019, by rfl⟩ : syracuseStep 4629437 = 1736039) (by norm_num)
theorem B3086291 : Blo 2057435 3086291 := bstep (se 1 (by rfl) ⟨2314718, by rfl⟩ : syracuseStep 3086291 = 4629437) B4629437
theorem B2057527 : Blo 2057435 2057527 := bstep (se 1 (by rfl) ⟨1543145, by rfl⟩ : syracuseStep 2057527 = 3086291) B3086291
theorem B3472085 : Blo 2057435 3472085 := bbase (se 7 (by rfl) ⟨40688, by rfl⟩ : syracuseStep 3472085 = 81377) (by norm_num)
theorem B2314723 : Blo 2057435 2314723 := bstep (se 1 (by rfl) ⟨1736042, by rfl⟩ : syracuseStep 2314723 = 3472085) B3472085
theorem B3086297 : Blo 2057435 3086297 := bstep (se 2 (by rfl) ⟨1157361, by rfl⟩ : syracuseStep 3086297 = 2314723) B2314723
theorem B2057531 : Blo 2057435 2057531 := bstep (se 1 (by rfl) ⟨1543148, by rfl⟩ : syracuseStep 2057531 = 3086297) B3086297
theorem B9385237 : Blo 2057435 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B12513649 : Blo 2057435 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B16684865 : Blo 2057435 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B11123243 : Blo 2057435 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B7415495 : Blo 2057435 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B4943663 : Blo 2057435 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B3295775 : Blo 2057435 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B8788733 : Blo 2057435 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B5859155 : Blo 2057435 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B15624413 : Blo 2057435 15624413 := bstep (se 3 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 15624413 = 5859155) B5859155
theorem B10416275 : Blo 2057435 10416275 := bstep (se 1 (by rfl) ⟨7812206, by rfl⟩ : syracuseStep 10416275 = 15624413) B15624413
theorem B6944183 : Blo 2057435 6944183 := bstep (se 1 (by rfl) ⟨5208137, by rfl⟩ : syracuseStep 6944183 = 10416275) B10416275
theorem B4629455 : Blo 2057435 4629455 := bstep (se 1 (by rfl) ⟨3472091, by rfl⟩ : syracuseStep 4629455 = 6944183) B6944183
theorem B3086303 : Blo 2057435 3086303 := bstep (se 1 (by rfl) ⟨2314727, by rfl⟩ : syracuseStep 3086303 = 4629455) B4629455
theorem B2057535 : Blo 2057435 2057535 := bstep (se 1 (by rfl) ⟨1543151, by rfl⟩ : syracuseStep 2057535 = 3086303) B3086303
theorem B3086309 : Blo 2057435 3086309 := bbase (se 4 (by rfl) ⟨289341, by rfl⟩ : syracuseStep 3086309 = 578683) (by norm_num)
theorem B2057539 : Blo 2057435 2057539 := bstep (se 1 (by rfl) ⟨1543154, by rfl⟩ : syracuseStep 2057539 = 3086309) B3086309
theorem B7415525 : Blo 2057435 7415525 := bbase (se 4 (by rfl) ⟨695205, by rfl⟩ : syracuseStep 7415525 = 1390411) (by norm_num)
theorem B4943683 : Blo 2057435 4943683 := bstep (se 1 (by rfl) ⟨3707762, by rfl⟩ : syracuseStep 4943683 = 7415525) B7415525
theorem B6591577 : Blo 2057435 6591577 := bstep (se 2 (by rfl) ⟨2471841, by rfl⟩ : syracuseStep 6591577 = 4943683) B4943683
theorem B8788769 : Blo 2057435 8788769 := bstep (se 2 (by rfl) ⟨3295788, by rfl⟩ : syracuseStep 8788769 = 6591577) B6591577
theorem B5859179 : Blo 2057435 5859179 := bstep (se 1 (by rfl) ⟨4394384, by rfl⟩ : syracuseStep 5859179 = 8788769) B8788769
theorem B3906119 : Blo 2057435 3906119 := bstep (se 1 (by rfl) ⟨2929589, by rfl⟩ : syracuseStep 3906119 = 5859179) B5859179
theorem B2604079 : Blo 2057435 2604079 := bstep (se 1 (by rfl) ⟨1953059, by rfl⟩ : syracuseStep 2604079 = 3906119) B3906119
theorem B3472105 : Blo 2057435 3472105 := bstep (se 2 (by rfl) ⟨1302039, by rfl⟩ : syracuseStep 3472105 = 2604079) B2604079
theorem B4629473 : Blo 2057435 4629473 := bstep (se 2 (by rfl) ⟨1736052, by rfl⟩ : syracuseStep 4629473 = 3472105) B3472105
theorem B3086315 : Blo 2057435 3086315 := bstep (se 1 (by rfl) ⟨2314736, by rfl⟩ : syracuseStep 3086315 = 4629473) B4629473
theorem B2057543 : Blo 2057435 2057543 := bstep (se 1 (by rfl) ⟨1543157, by rfl⟩ : syracuseStep 2057543 = 3086315) B3086315
theorem B2314741 : Blo 2057435 2314741 := bbase (se 5 (by rfl) ⟨108503, by rfl⟩ : syracuseStep 2314741 = 217007) (by norm_num)
theorem B3086321 : Blo 2057435 3086321 := bstep (se 2 (by rfl) ⟨1157370, by rfl⟩ : syracuseStep 3086321 = 2314741) B2314741
theorem B2057547 : Blo 2057435 2057547 := bstep (se 1 (by rfl) ⟨1543160, by rfl⟩ : syracuseStep 2057547 = 3086321) B3086321
theorem B2604089 : Blo 2057435 2604089 := bbase (se 2 (by rfl) ⟨976533, by rfl⟩ : syracuseStep 2604089 = 1953067) (by norm_num)
theorem B6944237 : Blo 2057435 6944237 := bstep (se 3 (by rfl) ⟨1302044, by rfl⟩ : syracuseStep 6944237 = 2604089) B2604089
theorem B4629491 : Blo 2057435 4629491 := bstep (se 1 (by rfl) ⟨3472118, by rfl⟩ : syracuseStep 4629491 = 6944237) B6944237
theorem B3086327 : Blo 2057435 3086327 := bstep (se 1 (by rfl) ⟨2314745, by rfl⟩ : syracuseStep 3086327 = 4629491) B4629491
theorem B2057551 : Blo 2057435 2057551 := bstep (se 1 (by rfl) ⟨1543163, by rfl⟩ : syracuseStep 2057551 = 3086327) B3086327
theorem B3086333 : Blo 2057435 3086333 := bbase (se 3 (by rfl) ⟨578687, by rfl⟩ : syracuseStep 3086333 = 1157375) (by norm_num)
theorem B2057555 : Blo 2057435 2057555 := bstep (se 1 (by rfl) ⟨1543166, by rfl⟩ : syracuseStep 2057555 = 3086333) B3086333
theorem B4629509 : Blo 2057435 4629509 := bbase (se 4 (by rfl) ⟨434016, by rfl⟩ : syracuseStep 4629509 = 868033) (by norm_num)
theorem B3086339 : Blo 2057435 3086339 := bstep (se 1 (by rfl) ⟨2314754, by rfl⟩ : syracuseStep 3086339 = 4629509) B4629509
theorem B2057559 : Blo 2057435 2057559 := bstep (se 1 (by rfl) ⟨1543169, by rfl⟩ : syracuseStep 2057559 = 3086339) B3086339
theorem B3906157 : Blo 2057435 3906157 := bbase (se 3 (by rfl) ⟨732404, by rfl⟩ : syracuseStep 3906157 = 1464809) (by norm_num)
theorem B5208209 : Blo 2057435 5208209 := bstep (se 2 (by rfl) ⟨1953078, by rfl⟩ : syracuseStep 5208209 = 3906157) B3906157
theorem B3472139 : Blo 2057435 3472139 := bstep (se 1 (by rfl) ⟨2604104, by rfl⟩ : syracuseStep 3472139 = 5208209) B5208209
theorem B2314759 : Blo 2057435 2314759 := bstep (se 1 (by rfl) ⟨1736069, by rfl⟩ : syracuseStep 2314759 = 3472139) B3472139
theorem B3086345 : Blo 2057435 3086345 := bstep (se 2 (by rfl) ⟨1157379, by rfl⟩ : syracuseStep 3086345 = 2314759) B2314759
theorem B2057563 : Blo 2057435 2057563 := bstep (se 1 (by rfl) ⟨1543172, by rfl⟩ : syracuseStep 2057563 = 3086345) B3086345
theorem B10416437 : Blo 2057435 10416437 := bbase (se 5 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 10416437 = 976541) (by norm_num)
theorem B6944291 : Blo 2057435 6944291 := bstep (se 1 (by rfl) ⟨5208218, by rfl⟩ : syracuseStep 6944291 = 10416437) B10416437
theorem B4629527 : Blo 2057435 4629527 := bstep (se 1 (by rfl) ⟨3472145, by rfl⟩ : syracuseStep 4629527 = 6944291) B6944291
theorem B3086351 : Blo 2057435 3086351 := bstep (se 1 (by rfl) ⟨2314763, by rfl⟩ : syracuseStep 3086351 = 4629527) B4629527
theorem B2057567 : Blo 2057435 2057567 := bstep (se 1 (by rfl) ⟨1543175, by rfl⟩ : syracuseStep 2057567 = 3086351) B3086351
theorem B3086357 : Blo 2057435 3086357 := bbase (se 6 (by rfl) ⟨72336, by rfl⟩ : syracuseStep 3086357 = 144673) (by norm_num)
theorem B2057571 : Blo 2057435 2057571 := bstep (se 1 (by rfl) ⟨1543178, by rfl⟩ : syracuseStep 2057571 = 3086357) B3086357
theorem B3519533 : Blo 2057435 3519533 := bbase (se 3 (by rfl) ⟨659912, by rfl⟩ : syracuseStep 3519533 = 1319825) (by norm_num)
theorem B2346355 : Blo 2057435 2346355 := bstep (se 1 (by rfl) ⟨1759766, by rfl⟩ : syracuseStep 2346355 = 3519533) B3519533
theorem B3128473 : Blo 2057435 3128473 := bstep (se 2 (by rfl) ⟨1173177, by rfl⟩ : syracuseStep 3128473 = 2346355) B2346355
theorem B16685189 : Blo 2057435 16685189 := bstep (se 4 (by rfl) ⟨1564236, by rfl⟩ : syracuseStep 16685189 = 3128473) B3128473
theorem B11123459 : Blo 2057435 11123459 := bstep (se 1 (by rfl) ⟨8342594, by rfl⟩ : syracuseStep 11123459 = 16685189) B16685189
theorem B7415639 : Blo 2057435 7415639 := bstep (se 1 (by rfl) ⟨5561729, by rfl⟩ : syracuseStep 7415639 = 11123459) B11123459
theorem B4943759 : Blo 2057435 4943759 := bstep (se 1 (by rfl) ⟨3707819, by rfl⟩ : syracuseStep 4943759 = 7415639) B7415639
theorem B13183357 : Blo 2057435 13183357 := bstep (se 3 (by rfl) ⟨2471879, by rfl⟩ : syracuseStep 13183357 = 4943759) B4943759
theorem B17577809 : Blo 2057435 17577809 := bstep (se 2 (by rfl) ⟨6591678, by rfl⟩ : syracuseStep 17577809 = 13183357) B13183357
theorem B11718539 : Blo 2057435 11718539 := bstep (se 1 (by rfl) ⟨8788904, by rfl⟩ : syracuseStep 11718539 = 17577809) B17577809
theorem B7812359 : Blo 2057435 7812359 := bstep (se 1 (by rfl) ⟨5859269, by rfl⟩ : syracuseStep 7812359 = 11718539) B11718539
theorem B5208239 : Blo 2057435 5208239 := bstep (se 1 (by rfl) ⟨3906179, by rfl⟩ : syracuseStep 5208239 = 7812359) B7812359
theorem B3472159 : Blo 2057435 3472159 := bstep (se 1 (by rfl) ⟨2604119, by rfl⟩ : syracuseStep 3472159 = 5208239) B5208239
theorem B4629545 : Blo 2057435 4629545 := bstep (se 2 (by rfl) ⟨1736079, by rfl⟩ : syracuseStep 4629545 = 3472159) B3472159
theorem B3086363 : Blo 2057435 3086363 := bstep (se 1 (by rfl) ⟨2314772, by rfl⟩ : syracuseStep 3086363 = 4629545) B4629545
theorem B2057575 : Blo 2057435 2057575 := bstep (se 1 (by rfl) ⟨1543181, by rfl⟩ : syracuseStep 2057575 = 3086363) B3086363
theorem B2314777 : Blo 2057435 2314777 := bbase (se 2 (by rfl) ⟨868041, by rfl⟩ : syracuseStep 2314777 = 1736083) (by norm_num)
theorem B3086369 : Blo 2057435 3086369 := bstep (se 2 (by rfl) ⟨1157388, by rfl⟩ : syracuseStep 3086369 = 2314777) B2314777
theorem B2057579 : Blo 2057435 2057579 := bstep (se 1 (by rfl) ⟨1543184, by rfl⟩ : syracuseStep 2057579 = 3086369) B3086369
theorem B7812389 : Blo 2057435 7812389 := bbase (se 4 (by rfl) ⟨732411, by rfl⟩ : syracuseStep 7812389 = 1464823) (by norm_num)
theorem B5208259 : Blo 2057435 5208259 := bstep (se 1 (by rfl) ⟨3906194, by rfl⟩ : syracuseStep 5208259 = 7812389) B7812389
theorem B6944345 : Blo 2057435 6944345 := bstep (se 2 (by rfl) ⟨2604129, by rfl⟩ : syracuseStep 6944345 = 5208259) B5208259
theorem B4629563 : Blo 2057435 4629563 := bstep (se 1 (by rfl) ⟨3472172, by rfl⟩ : syracuseStep 4629563 = 6944345) B6944345
theorem B3086375 : Blo 2057435 3086375 := bstep (se 1 (by rfl) ⟨2314781, by rfl⟩ : syracuseStep 3086375 = 4629563) B4629563
theorem B2057583 : Blo 2057435 2057583 := bstep (se 1 (by rfl) ⟨1543187, by rfl⟩ : syracuseStep 2057583 = 3086375) B3086375
theorem B3086381 : Blo 2057435 3086381 := bbase (se 3 (by rfl) ⟨578696, by rfl⟩ : syracuseStep 3086381 = 1157393) (by norm_num)
theorem B2057587 : Blo 2057435 2057587 := bstep (se 1 (by rfl) ⟨1543190, by rfl⟩ : syracuseStep 2057587 = 3086381) B3086381
theorem B4629581 : Blo 2057435 4629581 := bbase (se 3 (by rfl) ⟨868046, by rfl⟩ : syracuseStep 4629581 = 1736093) (by norm_num)
theorem B3086387 : Blo 2057435 3086387 := bstep (se 1 (by rfl) ⟨2314790, by rfl⟩ : syracuseStep 3086387 = 4629581) B4629581
theorem B2057591 : Blo 2057435 2057591 := bstep (se 1 (by rfl) ⟨1543193, by rfl⟩ : syracuseStep 2057591 = 3086387) B3086387
theorem B2604145 : Blo 2057435 2604145 := bbase (se 2 (by rfl) ⟨976554, by rfl⟩ : syracuseStep 2604145 = 1953109) (by norm_num)
theorem B3472193 : Blo 2057435 3472193 := bstep (se 2 (by rfl) ⟨1302072, by rfl⟩ : syracuseStep 3472193 = 2604145) B2604145
theorem B2314795 : Blo 2057435 2314795 := bstep (se 1 (by rfl) ⟨1736096, by rfl⟩ : syracuseStep 2314795 = 3472193) B3472193
theorem B3086393 : Blo 2057435 3086393 := bstep (se 2 (by rfl) ⟨1157397, by rfl⟩ : syracuseStep 3086393 = 2314795) B2314795
theorem B2057595 : Blo 2057435 2057595 := bstep (se 1 (by rfl) ⟨1543196, by rfl⟩ : syracuseStep 2057595 = 3086393) B3086393
theorem B2085673 : Blo 2057435 2085673 := bbase (se 2 (by rfl) ⟨782127, by rfl⟩ : syracuseStep 2085673 = 1564255) (by norm_num)
theorem B2780897 : Blo 2057435 2780897 := bstep (se 2 (by rfl) ⟨1042836, by rfl⟩ : syracuseStep 2780897 = 2085673) B2085673
theorem B7415725 : Blo 2057435 7415725 := bstep (se 3 (by rfl) ⟨1390448, by rfl⟩ : syracuseStep 7415725 = 2780897) B2780897
theorem B9887633 : Blo 2057435 9887633 := bstep (se 2 (by rfl) ⟨3707862, by rfl⟩ : syracuseStep 9887633 = 7415725) B7415725
theorem B6591755 : Blo 2057435 6591755 := bstep (se 1 (by rfl) ⟨4943816, by rfl⟩ : syracuseStep 6591755 = 9887633) B9887633
theorem B4394503 : Blo 2057435 4394503 := bstep (se 1 (by rfl) ⟨3295877, by rfl⟩ : syracuseStep 4394503 = 6591755) B6591755
theorem B23437349 : Blo 2057435 23437349 := bstep (se 4 (by rfl) ⟨2197251, by rfl⟩ : syracuseStep 23437349 = 4394503) B4394503
theorem B15624899 : Blo 2057435 15624899 := bstep (se 1 (by rfl) ⟨11718674, by rfl⟩ : syracuseStep 15624899 = 23437349) B23437349
theorem B10416599 : Blo 2057435 10416599 := bstep (se 1 (by rfl) ⟨7812449, by rfl⟩ : syracuseStep 10416599 = 15624899) B15624899
theorem B6944399 : Blo 2057435 6944399 := bstep (se 1 (by rfl) ⟨5208299, by rfl⟩ : syracuseStep 6944399 = 10416599) B10416599
theorem B4629599 : Blo 2057435 4629599 := bstep (se 1 (by rfl) ⟨3472199, by rfl⟩ : syracuseStep 4629599 = 6944399) B6944399
theorem B3086399 : Blo 2057435 3086399 := bstep (se 1 (by rfl) ⟨2314799, by rfl⟩ : syracuseStep 3086399 = 4629599) B4629599
theorem B2057599 : Blo 2057435 2057599 := bstep (se 1 (by rfl) ⟨1543199, by rfl⟩ : syracuseStep 2057599 = 3086399) B3086399
theorem B3086405 : Blo 2057435 3086405 := bbase (se 4 (by rfl) ⟨289350, by rfl⟩ : syracuseStep 3086405 = 578701) (by norm_num)
theorem B2057603 : Blo 2057435 2057603 := bstep (se 1 (by rfl) ⟨1543202, by rfl⟩ : syracuseStep 2057603 = 3086405) B3086405
theorem B3472213 : Blo 2057435 3472213 := bbase (se 9 (by rfl) ⟨10172, by rfl⟩ : syracuseStep 3472213 = 20345) (by norm_num)
theorem B4629617 : Blo 2057435 4629617 := bstep (se 2 (by rfl) ⟨1736106, by rfl⟩ : syracuseStep 4629617 = 3472213) B3472213
theorem B3086411 : Blo 2057435 3086411 := bstep (se 1 (by rfl) ⟨2314808, by rfl⟩ : syracuseStep 3086411 = 4629617) B4629617
theorem B2057607 : Blo 2057435 2057607 := bstep (se 1 (by rfl) ⟨1543205, by rfl⟩ : syracuseStep 2057607 = 3086411) B3086411
theorem B2314813 : Blo 2057435 2314813 := bbase (se 3 (by rfl) ⟨434027, by rfl⟩ : syracuseStep 2314813 = 868055) (by norm_num)
theorem B3086417 : Blo 2057435 3086417 := bstep (se 2 (by rfl) ⟨1157406, by rfl⟩ : syracuseStep 3086417 = 2314813) B2314813
theorem B2057611 : Blo 2057435 2057611 := bstep (se 1 (by rfl) ⟨1543208, by rfl⟩ : syracuseStep 2057611 = 3086417) B3086417
theorem B6944453 : Blo 2057435 6944453 := bbase (se 4 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 6944453 = 1302085) (by norm_num)
theorem B4629635 : Blo 2057435 4629635 := bstep (se 1 (by rfl) ⟨3472226, by rfl⟩ : syracuseStep 4629635 = 6944453) B6944453
theorem B3086423 : Blo 2057435 3086423 := bstep (se 1 (by rfl) ⟨2314817, by rfl⟩ : syracuseStep 3086423 = 4629635) B4629635
theorem B2057615 : Blo 2057435 2057615 := bstep (se 1 (by rfl) ⟨1543211, by rfl⟩ : syracuseStep 2057615 = 3086423) B3086423
theorem B3086429 : Blo 2057435 3086429 := bbase (se 3 (by rfl) ⟨578705, by rfl⟩ : syracuseStep 3086429 = 1157411) (by norm_num)
theorem B2057619 : Blo 2057435 2057619 := bstep (se 1 (by rfl) ⟨1543214, by rfl⟩ : syracuseStep 2057619 = 3086429) B3086429
theorem B4629653 : Blo 2057435 4629653 := bbase (se 6 (by rfl) ⟨108507, by rfl⟩ : syracuseStep 4629653 = 217015) (by norm_num)
theorem B3086435 : Blo 2057435 3086435 := bstep (se 1 (by rfl) ⟨2314826, by rfl⟩ : syracuseStep 3086435 = 4629653) B4629653
theorem B2057623 : Blo 2057435 2057623 := bstep (se 1 (by rfl) ⟨1543217, by rfl⟩ : syracuseStep 2057623 = 3086435) B3086435
theorem B2929709 : Blo 2057435 2929709 := bbase (se 3 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 2929709 = 1098641) (by norm_num)
theorem B7812557 : Blo 2057435 7812557 := bstep (se 3 (by rfl) ⟨1464854, by rfl⟩ : syracuseStep 7812557 = 2929709) B2929709
theorem B5208371 : Blo 2057435 5208371 := bstep (se 1 (by rfl) ⟨3906278, by rfl⟩ : syracuseStep 5208371 = 7812557) B7812557
theorem B3472247 : Blo 2057435 3472247 := bstep (se 1 (by rfl) ⟨2604185, by rfl⟩ : syracuseStep 3472247 = 5208371) B5208371
theorem B2314831 : Blo 2057435 2314831 := bstep (se 1 (by rfl) ⟨1736123, by rfl⟩ : syracuseStep 2314831 = 3472247) B3472247
theorem B3086441 : Blo 2057435 3086441 := bstep (se 2 (by rfl) ⟨1157415, by rfl⟩ : syracuseStep 3086441 = 2314831) B2314831
theorem B2057627 : Blo 2057435 2057627 := bstep (se 1 (by rfl) ⟨1543220, by rfl⟩ : syracuseStep 2057627 = 3086441) B3086441
theorem B19775573 : Blo 2057435 19775573 := bbase (se 8 (by rfl) ⟨115872, by rfl⟩ : syracuseStep 19775573 = 231745) (by norm_num)
theorem B13183715 : Blo 2057435 13183715 := bstep (se 1 (by rfl) ⟨9887786, by rfl⟩ : syracuseStep 13183715 = 19775573) B19775573
theorem B8789143 : Blo 2057435 8789143 := bstep (se 1 (by rfl) ⟨6591857, by rfl⟩ : syracuseStep 8789143 = 13183715) B13183715
theorem B11718857 : Blo 2057435 11718857 := bstep (se 2 (by rfl) ⟨4394571, by rfl⟩ : syracuseStep 11718857 = 8789143) B8789143
theorem B7812571 : Blo 2057435 7812571 := bstep (se 1 (by rfl) ⟨5859428, by rfl⟩ : syracuseStep 7812571 = 11718857) B11718857
theorem B10416761 : Blo 2057435 10416761 := bstep (se 2 (by rfl) ⟨3906285, by rfl⟩ : syracuseStep 10416761 = 7812571) B7812571
theorem B6944507 : Blo 2057435 6944507 := bstep (se 1 (by rfl) ⟨5208380, by rfl⟩ : syracuseStep 6944507 = 10416761) B10416761
theorem B4629671 : Blo 2057435 4629671 := bstep (se 1 (by rfl) ⟨3472253, by rfl⟩ : syracuseStep 4629671 = 6944507) B6944507
theorem B3086447 : Blo 2057435 3086447 := bstep (se 1 (by rfl) ⟨2314835, by rfl⟩ : syracuseStep 3086447 = 4629671) B4629671
theorem B2057631 : Blo 2057435 2057631 := bstep (se 1 (by rfl) ⟨1543223, by rfl⟩ : syracuseStep 2057631 = 3086447) B3086447
theorem B3086453 : Blo 2057435 3086453 := bbase (se 5 (by rfl) ⟨144677, by rfl⟩ : syracuseStep 3086453 = 289355) (by norm_num)
theorem B2057635 : Blo 2057435 2057635 := bstep (se 1 (by rfl) ⟨1543226, by rfl⟩ : syracuseStep 2057635 = 3086453) B3086453
theorem B3906301 : Blo 2057435 3906301 := bbase (se 3 (by rfl) ⟨732431, by rfl⟩ : syracuseStep 3906301 = 1464863) (by norm_num)
theorem B5208401 : Blo 2057435 5208401 := bstep (se 2 (by rfl) ⟨1953150, by rfl⟩ : syracuseStep 5208401 = 3906301) B3906301
theorem B3472267 : Blo 2057435 3472267 := bstep (se 1 (by rfl) ⟨2604200, by rfl⟩ : syracuseStep 3472267 = 5208401) B5208401
theorem B4629689 : Blo 2057435 4629689 := bstep (se 2 (by rfl) ⟨1736133, by rfl⟩ : syracuseStep 4629689 = 3472267) B3472267
theorem B3086459 : Blo 2057435 3086459 := bstep (se 1 (by rfl) ⟨2314844, by rfl⟩ : syracuseStep 3086459 = 4629689) B4629689
theorem B2057639 : Blo 2057435 2057639 := bstep (se 1 (by rfl) ⟨1543229, by rfl⟩ : syracuseStep 2057639 = 3086459) B3086459
theorem B2314849 : Blo 2057435 2314849 := bbase (se 2 (by rfl) ⟨868068, by rfl⟩ : syracuseStep 2314849 = 1736137) (by norm_num)
theorem B3086465 : Blo 2057435 3086465 := bstep (se 2 (by rfl) ⟨1157424, by rfl⟩ : syracuseStep 3086465 = 2314849) B2314849
theorem B2057643 : Blo 2057435 2057643 := bstep (se 1 (by rfl) ⟨1543232, by rfl⟩ : syracuseStep 2057643 = 3086465) B3086465
theorem B5208421 : Blo 2057435 5208421 := bbase (se 4 (by rfl) ⟨488289, by rfl⟩ : syracuseStep 5208421 = 976579) (by norm_num)
theorem B6944561 : Blo 2057435 6944561 := bstep (se 2 (by rfl) ⟨2604210, by rfl⟩ : syracuseStep 6944561 = 5208421) B5208421
theorem B4629707 : Blo 2057435 4629707 := bstep (se 1 (by rfl) ⟨3472280, by rfl⟩ : syracuseStep 4629707 = 6944561) B6944561
theorem B3086471 : Blo 2057435 3086471 := bstep (se 1 (by rfl) ⟨2314853, by rfl⟩ : syracuseStep 3086471 = 4629707) B4629707
theorem B2057647 : Blo 2057435 2057647 := bstep (se 1 (by rfl) ⟨1543235, by rfl⟩ : syracuseStep 2057647 = 3086471) B3086471
theorem B3086477 : Blo 2057435 3086477 := bbase (se 3 (by rfl) ⟨578714, by rfl⟩ : syracuseStep 3086477 = 1157429) (by norm_num)
theorem B2057651 : Blo 2057435 2057651 := bstep (se 1 (by rfl) ⟨1543238, by rfl⟩ : syracuseStep 2057651 = 3086477) B3086477
theorem B4629725 : Blo 2057435 4629725 := bbase (se 3 (by rfl) ⟨868073, by rfl⟩ : syracuseStep 4629725 = 1736147) (by norm_num)
theorem B3086483 : Blo 2057435 3086483 := bstep (se 1 (by rfl) ⟨2314862, by rfl⟩ : syracuseStep 3086483 = 4629725) B4629725
theorem B2057655 : Blo 2057435 2057655 := bstep (se 1 (by rfl) ⟨1543241, by rfl⟩ : syracuseStep 2057655 = 3086483) B3086483
theorem B3472301 : Blo 2057435 3472301 := bbase (se 3 (by rfl) ⟨651056, by rfl⟩ : syracuseStep 3472301 = 1302113) (by norm_num)
theorem B2314867 : Blo 2057435 2314867 := bstep (se 1 (by rfl) ⟨1736150, by rfl⟩ : syracuseStep 2314867 = 3472301) B3472301
theorem B3086489 : Blo 2057435 3086489 := bstep (se 2 (by rfl) ⟨1157433, by rfl⟩ : syracuseStep 3086489 = 2314867) B2314867
theorem B2057659 : Blo 2057435 2057659 := bstep (se 1 (by rfl) ⟨1543244, by rfl⟩ : syracuseStep 2057659 = 3086489) B3086489
theorem B133487189 : Blo 2057435 133487189 := bbase (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) (by norm_num)
theorem B88991459 : Blo 2057435 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B59327639 : Blo 2057435 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B39551759 : Blo 2057435 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B26367839 : Blo 2057435 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B17578559 : Blo 2057435 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B11719039 : Blo 2057435 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B15625385 : Blo 2057435 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B10416923 : Blo 2057435 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B6944615 : Blo 2057435 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B4629743 : Blo 2057435 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B3086495 : Blo 2057435 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B2057663 : Blo 2057435 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B3086501 : Blo 2057435 3086501 := bbase (se 4 (by rfl) ⟨289359, by rfl⟩ : syracuseStep 3086501 = 578719) (by norm_num)
theorem B2057667 : Blo 2057435 2057667 := bstep (se 1 (by rfl) ⟨1543250, by rfl⟩ : syracuseStep 2057667 = 3086501) B3086501
theorem B2604241 : Blo 2057435 2604241 := bbase (se 2 (by rfl) ⟨976590, by rfl⟩ : syracuseStep 2604241 = 1953181) (by norm_num)
theorem B3472321 : Blo 2057435 3472321 := bstep (se 2 (by rfl) ⟨1302120, by rfl⟩ : syracuseStep 3472321 = 2604241) B2604241
theorem B4629761 : Blo 2057435 4629761 := bstep (se 2 (by rfl) ⟨1736160, by rfl⟩ : syracuseStep 4629761 = 3472321) B3472321
theorem B3086507 : Blo 2057435 3086507 := bstep (se 1 (by rfl) ⟨2314880, by rfl⟩ : syracuseStep 3086507 = 4629761) B4629761
theorem B2057671 : Blo 2057435 2057671 := bstep (se 1 (by rfl) ⟨1543253, by rfl⟩ : syracuseStep 2057671 = 3086507) B3086507
theorem B2314885 : Blo 2057435 2314885 := bbase (se 4 (by rfl) ⟨217020, by rfl⟩ : syracuseStep 2314885 = 434041) (by norm_num)
theorem B3086513 : Blo 2057435 3086513 := bstep (se 2 (by rfl) ⟨1157442, by rfl⟩ : syracuseStep 3086513 = 2314885) B2314885
theorem B2057675 : Blo 2057435 2057675 := bstep (se 1 (by rfl) ⟨1543256, by rfl⟩ : syracuseStep 2057675 = 3086513) B3086513
theorem B2472005 : Blo 2057435 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B6592013 : Blo 2057435 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B4394675 : Blo 2057435 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B2929783 : Blo 2057435 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B3906377 : Blo 2057435 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B2604251 : Blo 2057435 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B6944669 : Blo 2057435 6944669 := bstep (se 3 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 6944669 = 2604251) B2604251
theorem B4629779 : Blo 2057435 4629779 := bstep (se 1 (by rfl) ⟨3472334, by rfl⟩ : syracuseStep 4629779 = 6944669) B6944669
theorem B3086519 : Blo 2057435 3086519 := bstep (se 1 (by rfl) ⟨2314889, by rfl⟩ : syracuseStep 3086519 = 4629779) B4629779
theorem B2057679 : Blo 2057435 2057679 := bstep (se 1 (by rfl) ⟨1543259, by rfl⟩ : syracuseStep 2057679 = 3086519) B3086519
theorem B3086525 : Blo 2057435 3086525 := bbase (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) (by norm_num)
theorem B2057683 : Blo 2057435 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B4629797 : Blo 2057435 4629797 := bbase (se 4 (by rfl) ⟨434043, by rfl⟩ : syracuseStep 4629797 = 868087) (by norm_num)
theorem B3086531 : Blo 2057435 3086531 := bstep (se 1 (by rfl) ⟨2314898, by rfl⟩ : syracuseStep 3086531 = 4629797) B4629797
theorem B2057687 : Blo 2057435 2057687 := bstep (se 1 (by rfl) ⟨1543265, by rfl⟩ : syracuseStep 2057687 = 3086531) B3086531
theorem B5208533 : Blo 2057435 5208533 := bbase (se 7 (by rfl) ⟨61037, by rfl⟩ : syracuseStep 5208533 = 122075) (by norm_num)
theorem B3472355 : Blo 2057435 3472355 := bstep (se 1 (by rfl) ⟨2604266, by rfl⟩ : syracuseStep 3472355 = 5208533) B5208533
theorem B2314903 : Blo 2057435 2314903 := bstep (se 1 (by rfl) ⟨1736177, by rfl⟩ : syracuseStep 2314903 = 3472355) B3472355
theorem B3086537 : Blo 2057435 3086537 := bstep (se 2 (by rfl) ⟨1157451, by rfl⟩ : syracuseStep 3086537 = 2314903) B2314903
theorem B2057691 : Blo 2057435 2057691 := bstep (se 1 (by rfl) ⟨1543268, by rfl⟩ : syracuseStep 2057691 = 3086537) B3086537
theorem B4454669 : Blo 2057435 4454669 := bbase (se 3 (by rfl) ⟨835250, by rfl⟩ : syracuseStep 4454669 = 1670501) (by norm_num)
theorem B2969779 : Blo 2057435 2969779 := bstep (se 1 (by rfl) ⟨2227334, by rfl⟩ : syracuseStep 2969779 = 4454669) B4454669
theorem B3959705 : Blo 2057435 3959705 := bstep (se 2 (by rfl) ⟨1484889, by rfl⟩ : syracuseStep 3959705 = 2969779) B2969779
theorem B10559213 : Blo 2057435 10559213 := bstep (se 3 (by rfl) ⟨1979852, by rfl⟩ : syracuseStep 10559213 = 3959705) B3959705
theorem B7039475 : Blo 2057435 7039475 := bstep (se 1 (by rfl) ⟨5279606, by rfl⟩ : syracuseStep 7039475 = 10559213) B10559213
theorem B4692983 : Blo 2057435 4692983 := bstep (se 1 (by rfl) ⟨3519737, by rfl⟩ : syracuseStep 4692983 = 7039475) B7039475
theorem B50058485 : Blo 2057435 50058485 := bstep (se 5 (by rfl) ⟨2346491, by rfl⟩ : syracuseStep 50058485 = 4692983) B4692983
theorem B33372323 : Blo 2057435 33372323 := bstep (se 1 (by rfl) ⟨25029242, by rfl⟩ : syracuseStep 33372323 = 50058485) B50058485
theorem B22248215 : Blo 2057435 22248215 := bstep (se 1 (by rfl) ⟨16686161, by rfl⟩ : syracuseStep 22248215 = 33372323) B33372323
theorem B14832143 : Blo 2057435 14832143 := bstep (se 1 (by rfl) ⟨11124107, by rfl⟩ : syracuseStep 14832143 = 22248215) B22248215
theorem B9888095 : Blo 2057435 9888095 := bstep (se 1 (by rfl) ⟨7416071, by rfl⟩ : syracuseStep 9888095 = 14832143) B14832143
theorem B6592063 : Blo 2057435 6592063 := bstep (se 1 (by rfl) ⟨4944047, by rfl⟩ : syracuseStep 6592063 = 9888095) B9888095
theorem B8789417 : Blo 2057435 8789417 := bstep (se 2 (by rfl) ⟨3296031, by rfl⟩ : syracuseStep 8789417 = 6592063) B6592063
theorem B5859611 : Blo 2057435 5859611 := bstep (se 1 (by rfl) ⟨4394708, by rfl⟩ : syracuseStep 5859611 = 8789417) B8789417
theorem B3906407 : Blo 2057435 3906407 := bstep (se 1 (by rfl) ⟨2929805, by rfl⟩ : syracuseStep 3906407 = 5859611) B5859611
theorem B10417085 : Blo 2057435 10417085 := bstep (se 3 (by rfl) ⟨1953203, by rfl⟩ : syracuseStep 10417085 = 3906407) B3906407
theorem B6944723 : Blo 2057435 6944723 := bstep (se 1 (by rfl) ⟨5208542, by rfl⟩ : syracuseStep 6944723 = 10417085) B10417085
theorem B4629815 : Blo 2057435 4629815 := bstep (se 1 (by rfl) ⟨3472361, by rfl⟩ : syracuseStep 4629815 = 6944723) B6944723
theorem B3086543 : Blo 2057435 3086543 := bstep (se 1 (by rfl) ⟨2314907, by rfl⟩ : syracuseStep 3086543 = 4629815) B4629815
theorem B2057695 : Blo 2057435 2057695 := bstep (se 1 (by rfl) ⟨1543271, by rfl⟩ : syracuseStep 2057695 = 3086543) B3086543
theorem B3086549 : Blo 2057435 3086549 := bbase (se 7 (by rfl) ⟨36170, by rfl⟩ : syracuseStep 3086549 = 72341) (by norm_num)
theorem B2057699 : Blo 2057435 2057699 := bstep (se 1 (by rfl) ⟨1543274, by rfl⟩ : syracuseStep 2057699 = 3086549) B3086549
theorem B3296045 : Blo 2057435 3296045 := bbase (se 3 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 3296045 = 1236017) (by norm_num)
theorem B2197363 : Blo 2057435 2197363 := bstep (se 1 (by rfl) ⟨1648022, by rfl⟩ : syracuseStep 2197363 = 3296045) B3296045
theorem B2929817 : Blo 2057435 2929817 := bstep (se 2 (by rfl) ⟨1098681, by rfl⟩ : syracuseStep 2929817 = 2197363) B2197363
theorem B7812845 : Blo 2057435 7812845 := bstep (se 3 (by rfl) ⟨1464908, by rfl⟩ : syracuseStep 7812845 = 2929817) B2929817
theorem B5208563 : Blo 2057435 5208563 := bstep (se 1 (by rfl) ⟨3906422, by rfl⟩ : syracuseStep 5208563 = 7812845) B7812845
theorem B3472375 : Blo 2057435 3472375 := bstep (se 1 (by rfl) ⟨2604281, by rfl⟩ : syracuseStep 3472375 = 5208563) B5208563
theorem B4629833 : Blo 2057435 4629833 := bstep (se 2 (by rfl) ⟨1736187, by rfl⟩ : syracuseStep 4629833 = 3472375) B3472375
theorem B3086555 : Blo 2057435 3086555 := bstep (se 1 (by rfl) ⟨2314916, by rfl⟩ : syracuseStep 3086555 = 4629833) B4629833
theorem B2057703 : Blo 2057435 2057703 := bstep (se 1 (by rfl) ⟨1543277, by rfl⟩ : syracuseStep 2057703 = 3086555) B3086555
theorem B2314921 : Blo 2057435 2314921 := bbase (se 2 (by rfl) ⟨868095, by rfl⟩ : syracuseStep 2314921 = 1736191) (by norm_num)
theorem B3086561 : Blo 2057435 3086561 := bstep (se 2 (by rfl) ⟨1157460, by rfl⟩ : syracuseStep 3086561 = 2314921) B2314921
theorem B2057707 : Blo 2057435 2057707 := bstep (se 1 (by rfl) ⟨1543280, by rfl⟩ : syracuseStep 2057707 = 3086561) B3086561
theorem B7919477 : Blo 2057435 7919477 := bbase (se 5 (by rfl) ⟨371225, by rfl⟩ : syracuseStep 7919477 = 742451) (by norm_num)
theorem B5279651 : Blo 2057435 5279651 := bstep (se 1 (by rfl) ⟨3959738, by rfl⟩ : syracuseStep 5279651 = 7919477) B7919477
theorem B3519767 : Blo 2057435 3519767 := bstep (se 1 (by rfl) ⟨2639825, by rfl⟩ : syracuseStep 3519767 = 5279651) B5279651
theorem B2346511 : Blo 2057435 2346511 := bstep (se 1 (by rfl) ⟨1759883, by rfl⟩ : syracuseStep 2346511 = 3519767) B3519767
theorem B3128681 : Blo 2057435 3128681 := bstep (se 2 (by rfl) ⟨1173255, by rfl⟩ : syracuseStep 3128681 = 2346511) B2346511
theorem B2085787 : Blo 2057435 2085787 := bstep (se 1 (by rfl) ⟨1564340, by rfl⟩ : syracuseStep 2085787 = 3128681) B3128681
theorem B2781049 : Blo 2057435 2781049 := bstep (se 2 (by rfl) ⟨1042893, by rfl⟩ : syracuseStep 2781049 = 2085787) B2085787
theorem B3708065 : Blo 2057435 3708065 := bstep (se 2 (by rfl) ⟨1390524, by rfl⟩ : syracuseStep 3708065 = 2781049) B2781049
theorem B2472043 : Blo 2057435 2472043 := bstep (se 1 (by rfl) ⟨1854032, by rfl⟩ : syracuseStep 2472043 = 3708065) B3708065
theorem B3296057 : Blo 2057435 3296057 := bstep (se 2 (by rfl) ⟨1236021, by rfl⟩ : syracuseStep 3296057 = 2472043) B2472043
theorem B8789485 : Blo 2057435 8789485 := bstep (se 3 (by rfl) ⟨1648028, by rfl⟩ : syracuseStep 8789485 = 3296057) B3296057
theorem B11719313 : Blo 2057435 11719313 := bstep (se 2 (by rfl) ⟨4394742, by rfl⟩ : syracuseStep 11719313 = 8789485) B8789485
theorem B7812875 : Blo 2057435 7812875 := bstep (se 1 (by rfl) ⟨5859656, by rfl⟩ : syracuseStep 7812875 = 11719313) B11719313
theorem B5208583 : Blo 2057435 5208583 := bstep (se 1 (by rfl) ⟨3906437, by rfl⟩ : syracuseStep 5208583 = 7812875) B7812875
theorem B6944777 : Blo 2057435 6944777 := bstep (se 2 (by rfl) ⟨2604291, by rfl⟩ : syracuseStep 6944777 = 5208583) B5208583
theorem B4629851 : Blo 2057435 4629851 := bstep (se 1 (by rfl) ⟨3472388, by rfl⟩ : syracuseStep 4629851 = 6944777) B6944777
theorem B3086567 : Blo 2057435 3086567 := bstep (se 1 (by rfl) ⟨2314925, by rfl⟩ : syracuseStep 3086567 = 4629851) B4629851
theorem B2057711 : Blo 2057435 2057711 := bstep (se 1 (by rfl) ⟨1543283, by rfl⟩ : syracuseStep 2057711 = 3086567) B3086567
theorem B3086573 : Blo 2057435 3086573 := bbase (se 3 (by rfl) ⟨578732, by rfl⟩ : syracuseStep 3086573 = 1157465) (by norm_num)
theorem B2057715 : Blo 2057435 2057715 := bstep (se 1 (by rfl) ⟨1543286, by rfl⟩ : syracuseStep 2057715 = 3086573) B3086573
theorem B4629869 : Blo 2057435 4629869 := bbase (se 3 (by rfl) ⟨868100, by rfl⟩ : syracuseStep 4629869 = 1736201) (by norm_num)
theorem B3086579 : Blo 2057435 3086579 := bstep (se 1 (by rfl) ⟨2314934, by rfl⟩ : syracuseStep 3086579 = 4629869) B4629869
theorem B2057719 : Blo 2057435 2057719 := bstep (se 1 (by rfl) ⟨1543289, by rfl⟩ : syracuseStep 2057719 = 3086579) B3086579
theorem B3906461 : Blo 2057435 3906461 := bbase (se 3 (by rfl) ⟨732461, by rfl⟩ : syracuseStep 3906461 = 1464923) (by norm_num)
theorem B2604307 : Blo 2057435 2604307 := bstep (se 1 (by rfl) ⟨1953230, by rfl⟩ : syracuseStep 2604307 = 3906461) B3906461
theorem B3472409 : Blo 2057435 3472409 := bstep (se 2 (by rfl) ⟨1302153, by rfl⟩ : syracuseStep 3472409 = 2604307) B2604307
theorem B2314939 : Blo 2057435 2314939 := bstep (se 1 (by rfl) ⟨1736204, by rfl⟩ : syracuseStep 2314939 = 3472409) B3472409
theorem B3086585 : Blo 2057435 3086585 := bstep (se 2 (by rfl) ⟨1157469, by rfl⟩ : syracuseStep 3086585 = 2314939) B2314939
theorem B2057723 : Blo 2057435 2057723 := bstep (se 1 (by rfl) ⟨1543292, by rfl⟩ : syracuseStep 2057723 = 3086585) B3086585
theorem B7232981 : Blo 2057435 7232981 := bbase (se 7 (by rfl) ⟨84761, by rfl⟩ : syracuseStep 7232981 = 169523) (by norm_num)
theorem B77151797 : Blo 2057435 77151797 := bstep (se 5 (by rfl) ⟨3616490, by rfl⟩ : syracuseStep 77151797 = 7232981) B7232981
theorem B51434531 : Blo 2057435 51434531 := bstep (se 1 (by rfl) ⟨38575898, by rfl⟩ : syracuseStep 51434531 = 77151797) B77151797
theorem B34289687 : Blo 2057435 34289687 := bstep (se 1 (by rfl) ⟨25717265, by rfl⟩ : syracuseStep 34289687 = 51434531) B51434531
theorem B91439165 : Blo 2057435 91439165 := bstep (se 3 (by rfl) ⟨17144843, by rfl⟩ : syracuseStep 91439165 = 34289687) B34289687
theorem B243837773 : Blo 2057435 243837773 := bstep (se 3 (by rfl) ⟨45719582, by rfl⟩ : syracuseStep 243837773 = 91439165) B91439165
theorem B162558515 : Blo 2057435 162558515 := bstep (se 1 (by rfl) ⟨121918886, by rfl⟩ : syracuseStep 162558515 = 243837773) B243837773
theorem B108372343 : Blo 2057435 108372343 := bstep (se 1 (by rfl) ⟨81279257, by rfl⟩ : syracuseStep 108372343 = 162558515) B162558515
theorem B144496457 : Blo 2057435 144496457 := bstep (se 2 (by rfl) ⟨54186171, by rfl⟩ : syracuseStep 144496457 = 108372343) B108372343
theorem B96330971 : Blo 2057435 96330971 := bstep (se 1 (by rfl) ⟨72248228, by rfl⟩ : syracuseStep 96330971 = 144496457) B144496457
theorem B64220647 : Blo 2057435 64220647 := bstep (se 1 (by rfl) ⟨48165485, by rfl⟩ : syracuseStep 64220647 = 96330971) B96330971
theorem B85627529 : Blo 2057435 85627529 := bstep (se 2 (by rfl) ⟨32110323, by rfl⟩ : syracuseStep 85627529 = 64220647) B64220647
theorem B57085019 : Blo 2057435 57085019 := bstep (se 1 (by rfl) ⟨42813764, by rfl⟩ : syracuseStep 57085019 = 85627529) B85627529
theorem B38056679 : Blo 2057435 38056679 := bstep (se 1 (by rfl) ⟨28542509, by rfl⟩ : syracuseStep 38056679 = 57085019) B57085019
theorem B25371119 : Blo 2057435 25371119 := bstep (se 1 (by rfl) ⟨19028339, by rfl⟩ : syracuseStep 25371119 = 38056679) B38056679
theorem B16914079 : Blo 2057435 16914079 := bstep (se 1 (by rfl) ⟨12685559, by rfl⟩ : syracuseStep 16914079 = 25371119) B25371119
theorem B22552105 : Blo 2057435 22552105 := bstep (se 2 (by rfl) ⟨8457039, by rfl⟩ : syracuseStep 22552105 = 16914079) B16914079
theorem B30069473 : Blo 2057435 30069473 := bstep (se 2 (by rfl) ⟨11276052, by rfl⟩ : syracuseStep 30069473 = 22552105) B22552105
theorem B80185261 : Blo 2057435 80185261 := bstep (se 3 (by rfl) ⟨15034736, by rfl⟩ : syracuseStep 80185261 = 30069473) B30069473
theorem B106913681 : Blo 2057435 106913681 := bstep (se 2 (by rfl) ⟨40092630, by rfl⟩ : syracuseStep 106913681 = 80185261) B80185261
theorem B71275787 : Blo 2057435 71275787 := bstep (se 1 (by rfl) ⟨53456840, by rfl⟩ : syracuseStep 71275787 = 106913681) B106913681
theorem B47517191 : Blo 2057435 47517191 := bstep (se 1 (by rfl) ⟨35637893, by rfl⟩ : syracuseStep 47517191 = 71275787) B71275787
theorem B31678127 : Blo 2057435 31678127 := bstep (se 1 (by rfl) ⟨23758595, by rfl⟩ : syracuseStep 31678127 = 47517191) B47517191
theorem B21118751 : Blo 2057435 21118751 := bstep (se 1 (by rfl) ⟨15839063, by rfl⟩ : syracuseStep 21118751 = 31678127) B31678127
theorem B14079167 : Blo 2057435 14079167 := bstep (se 1 (by rfl) ⟨10559375, by rfl⟩ : syracuseStep 14079167 = 21118751) B21118751
theorem B9386111 : Blo 2057435 9386111 := bstep (se 1 (by rfl) ⟨7039583, by rfl⟩ : syracuseStep 9386111 = 14079167) B14079167
theorem B6257407 : Blo 2057435 6257407 := bstep (se 1 (by rfl) ⟨4693055, by rfl⟩ : syracuseStep 6257407 = 9386111) B9386111
theorem B8343209 : Blo 2057435 8343209 := bstep (se 2 (by rfl) ⟨3128703, by rfl⟩ : syracuseStep 8343209 = 6257407) B6257407
theorem B22248557 : Blo 2057435 22248557 := bstep (se 3 (by rfl) ⟨4171604, by rfl⟩ : syracuseStep 22248557 = 8343209) B8343209
theorem B14832371 : Blo 2057435 14832371 := bstep (se 1 (by rfl) ⟨11124278, by rfl⟩ : syracuseStep 14832371 = 22248557) B22248557
theorem B9888247 : Blo 2057435 9888247 := bstep (se 1 (by rfl) ⟨7416185, by rfl⟩ : syracuseStep 9888247 = 14832371) B14832371
theorem B52737317 : Blo 2057435 52737317 := bstep (se 4 (by rfl) ⟨4944123, by rfl⟩ : syracuseStep 52737317 = 9888247) B9888247
theorem B35158211 : Blo 2057435 35158211 := bstep (se 1 (by rfl) ⟨26368658, by rfl⟩ : syracuseStep 35158211 = 52737317) B52737317
theorem B23438807 : Blo 2057435 23438807 := bstep (se 1 (by rfl) ⟨17579105, by rfl⟩ : syracuseStep 23438807 = 35158211) B35158211
theorem B15625871 : Blo 2057435 15625871 := bstep (se 1 (by rfl) ⟨11719403, by rfl⟩ : syracuseStep 15625871 = 23438807) B23438807
theorem B10417247 : Blo 2057435 10417247 := bstep (se 1 (by rfl) ⟨7812935, by rfl⟩ : syracuseStep 10417247 = 15625871) B15625871
theorem B6944831 : Blo 2057435 6944831 := bstep (se 1 (by rfl) ⟨5208623, by rfl⟩ : syracuseStep 6944831 = 10417247) B10417247
theorem B4629887 : Blo 2057435 4629887 := bstep (se 1 (by rfl) ⟨3472415, by rfl⟩ : syracuseStep 4629887 = 6944831) B6944831
theorem B3086591 : Blo 2057435 3086591 := bstep (se 1 (by rfl) ⟨2314943, by rfl⟩ : syracuseStep 3086591 = 4629887) B4629887
theorem B2057727 : Blo 2057435 2057727 := bstep (se 1 (by rfl) ⟨1543295, by rfl⟩ : syracuseStep 2057727 = 3086591) B3086591
theorem B3086597 : Blo 2057435 3086597 := bbase (se 4 (by rfl) ⟨289368, by rfl⟩ : syracuseStep 3086597 = 578737) (by norm_num)
theorem B2057731 : Blo 2057435 2057731 := bstep (se 1 (by rfl) ⟨1543298, by rfl⟩ : syracuseStep 2057731 = 3086597) B3086597
theorem B3472429 : Blo 2057435 3472429 := bbase (se 3 (by rfl) ⟨651080, by rfl⟩ : syracuseStep 3472429 = 1302161) (by norm_num)
theorem B4629905 : Blo 2057435 4629905 := bstep (se 2 (by rfl) ⟨1736214, by rfl⟩ : syracuseStep 4629905 = 3472429) B3472429
theorem B3086603 : Blo 2057435 3086603 := bstep (se 1 (by rfl) ⟨2314952, by rfl⟩ : syracuseStep 3086603 = 4629905) B4629905
theorem B2057735 : Blo 2057435 2057735 := bstep (se 1 (by rfl) ⟨1543301, by rfl⟩ : syracuseStep 2057735 = 3086603) B3086603
theorem B2314957 : Blo 2057435 2314957 := bbase (se 3 (by rfl) ⟨434054, by rfl⟩ : syracuseStep 2314957 = 868109) (by norm_num)
theorem B3086609 : Blo 2057435 3086609 := bstep (se 2 (by rfl) ⟨1157478, by rfl⟩ : syracuseStep 3086609 = 2314957) B2314957
theorem B2057739 : Blo 2057435 2057739 := bstep (se 1 (by rfl) ⟨1543304, by rfl⟩ : syracuseStep 2057739 = 3086609) B3086609
theorem B6944885 : Blo 2057435 6944885 := bbase (se 5 (by rfl) ⟨325541, by rfl⟩ : syracuseStep 6944885 = 651083) (by norm_num)
theorem B4629923 : Blo 2057435 4629923 := bstep (se 1 (by rfl) ⟨3472442, by rfl⟩ : syracuseStep 4629923 = 6944885) B6944885
theorem B3086615 : Blo 2057435 3086615 := bstep (se 1 (by rfl) ⟨2314961, by rfl⟩ : syracuseStep 3086615 = 4629923) B4629923
theorem B2057743 : Blo 2057435 2057743 := bstep (se 1 (by rfl) ⟨1543307, by rfl⟩ : syracuseStep 2057743 = 3086615) B3086615
theorem B3086621 : Blo 2057435 3086621 := bbase (se 3 (by rfl) ⟨578741, by rfl⟩ : syracuseStep 3086621 = 1157483) (by norm_num)
theorem B2057747 : Blo 2057435 2057747 := bstep (se 1 (by rfl) ⟨1543310, by rfl⟩ : syracuseStep 2057747 = 3086621) B3086621
theorem B4629941 : Blo 2057435 4629941 := bbase (se 5 (by rfl) ⟨217028, by rfl⟩ : syracuseStep 4629941 = 434057) (by norm_num)
theorem B3086627 : Blo 2057435 3086627 := bstep (se 1 (by rfl) ⟨2314970, by rfl⟩ : syracuseStep 3086627 = 4629941) B4629941
theorem B2057751 : Blo 2057435 2057751 := bstep (se 1 (by rfl) ⟨1543313, by rfl⟩ : syracuseStep 2057751 = 3086627) B3086627
theorem B4394837 : Blo 2057435 4394837 := bbase (se 9 (by rfl) ⟨12875, by rfl⟩ : syracuseStep 4394837 = 25751) (by norm_num)
theorem B11719565 : Blo 2057435 11719565 := bstep (se 3 (by rfl) ⟨2197418, by rfl⟩ : syracuseStep 11719565 = 4394837) B4394837
theorem B7813043 : Blo 2057435 7813043 := bstep (se 1 (by rfl) ⟨5859782, by rfl⟩ : syracuseStep 7813043 = 11719565) B11719565
theorem B5208695 : Blo 2057435 5208695 := bstep (se 1 (by rfl) ⟨3906521, by rfl⟩ : syracuseStep 5208695 = 7813043) B7813043
theorem B3472463 : Blo 2057435 3472463 := bstep (se 1 (by rfl) ⟨2604347, by rfl⟩ : syracuseStep 3472463 = 5208695) B5208695
theorem B2314975 : Blo 2057435 2314975 := bstep (se 1 (by rfl) ⟨1736231, by rfl⟩ : syracuseStep 2314975 = 3472463) B3472463
theorem B3086633 : Blo 2057435 3086633 := bstep (se 2 (by rfl) ⟨1157487, by rfl⟩ : syracuseStep 3086633 = 2314975) B2314975
theorem B2057755 : Blo 2057435 2057755 := bstep (se 1 (by rfl) ⟨1543316, by rfl⟩ : syracuseStep 2057755 = 3086633) B3086633
theorem B4394845 : Blo 2057435 4394845 := bbase (se 3 (by rfl) ⟨824033, by rfl⟩ : syracuseStep 4394845 = 1648067) (by norm_num)
theorem B5859793 : Blo 2057435 5859793 := bstep (se 2 (by rfl) ⟨2197422, by rfl⟩ : syracuseStep 5859793 = 4394845) B4394845
theorem B7813057 : Blo 2057435 7813057 := bstep (se 2 (by rfl) ⟨2929896, by rfl⟩ : syracuseStep 7813057 = 5859793) B5859793
theorem B10417409 : Blo 2057435 10417409 := bstep (se 2 (by rfl) ⟨3906528, by rfl⟩ : syracuseStep 10417409 = 7813057) B7813057
theorem B6944939 : Blo 2057435 6944939 := bstep (se 1 (by rfl) ⟨5208704, by rfl⟩ : syracuseStep 6944939 = 10417409) B10417409
theorem B4629959 : Blo 2057435 4629959 := bstep (se 1 (by rfl) ⟨3472469, by rfl⟩ : syracuseStep 4629959 = 6944939) B6944939
theorem B3086639 : Blo 2057435 3086639 := bstep (se 1 (by rfl) ⟨2314979, by rfl⟩ : syracuseStep 3086639 = 4629959) B4629959
theorem B2057759 : Blo 2057435 2057759 := bstep (se 1 (by rfl) ⟨1543319, by rfl⟩ : syracuseStep 2057759 = 3086639) B3086639
theorem B3086645 : Blo 2057435 3086645 := bbase (se 5 (by rfl) ⟨144686, by rfl⟩ : syracuseStep 3086645 = 289373) (by norm_num)
theorem B2057763 : Blo 2057435 2057763 := bstep (se 1 (by rfl) ⟨1543322, by rfl⟩ : syracuseStep 2057763 = 3086645) B3086645
theorem B5208725 : Blo 2057435 5208725 := bbase (se 6 (by rfl) ⟨122079, by rfl⟩ : syracuseStep 5208725 = 244159) (by norm_num)
theorem B3472483 : Blo 2057435 3472483 := bstep (se 1 (by rfl) ⟨2604362, by rfl⟩ : syracuseStep 3472483 = 5208725) B5208725
theorem B4629977 : Blo 2057435 4629977 := bstep (se 2 (by rfl) ⟨1736241, by rfl⟩ : syracuseStep 4629977 = 3472483) B3472483
theorem B3086651 : Blo 2057435 3086651 := bstep (se 1 (by rfl) ⟨2314988, by rfl⟩ : syracuseStep 3086651 = 4629977) B4629977
theorem B2057767 : Blo 2057435 2057767 := bstep (se 1 (by rfl) ⟨1543325, by rfl⟩ : syracuseStep 2057767 = 3086651) B3086651
theorem B2314993 : Blo 2057435 2314993 := bbase (se 2 (by rfl) ⟨868122, by rfl⟩ : syracuseStep 2314993 = 1736245) (by norm_num)
theorem B3086657 : Blo 2057435 3086657 := bstep (se 2 (by rfl) ⟨1157496, by rfl⟩ : syracuseStep 3086657 = 2314993) B2314993
theorem B2057771 : Blo 2057435 2057771 := bstep (se 1 (by rfl) ⟨1543328, by rfl⟩ : syracuseStep 2057771 = 3086657) B3086657
theorem B21407381 : Blo 2057435 21407381 := bbase (se 6 (by rfl) ⟨501735, by rfl⟩ : syracuseStep 21407381 = 1003471) (by norm_num)
theorem B14271587 : Blo 2057435 14271587 := bstep (se 1 (by rfl) ⟨10703690, by rfl⟩ : syracuseStep 14271587 = 21407381) B21407381
theorem B9514391 : Blo 2057435 9514391 := bstep (se 1 (by rfl) ⟨7135793, by rfl⟩ : syracuseStep 9514391 = 14271587) B14271587
theorem B101486837 : Blo 2057435 101486837 := bstep (se 5 (by rfl) ⟨4757195, by rfl⟩ : syracuseStep 101486837 = 9514391) B9514391
theorem B67657891 : Blo 2057435 67657891 := bstep (se 1 (by rfl) ⟨50743418, by rfl⟩ : syracuseStep 67657891 = 101486837) B101486837
theorem B90210521 : Blo 2057435 90210521 := bstep (se 2 (by rfl) ⟨33828945, by rfl⟩ : syracuseStep 90210521 = 67657891) B67657891
theorem B240561389 : Blo 2057435 240561389 := bstep (se 3 (by rfl) ⟨45105260, by rfl⟩ : syracuseStep 240561389 = 90210521) B90210521
theorem B160374259 : Blo 2057435 160374259 := bstep (se 1 (by rfl) ⟨120280694, by rfl⟩ : syracuseStep 160374259 = 240561389) B240561389
theorem B855329381 : Blo 2057435 855329381 := bstep (se 4 (by rfl) ⟨80187129, by rfl⟩ : syracuseStep 855329381 = 160374259) B160374259
theorem B570219587 : Blo 2057435 570219587 := bstep (se 1 (by rfl) ⟨427664690, by rfl⟩ : syracuseStep 570219587 = 855329381) B855329381
theorem B380146391 : Blo 2057435 380146391 := bstep (se 1 (by rfl) ⟨285109793, by rfl⟩ : syracuseStep 380146391 = 570219587) B570219587
theorem B253430927 : Blo 2057435 253430927 := bstep (se 1 (by rfl) ⟨190073195, by rfl⟩ : syracuseStep 253430927 = 380146391) B380146391
theorem B168953951 : Blo 2057435 168953951 := bstep (se 1 (by rfl) ⟨126715463, by rfl⟩ : syracuseStep 168953951 = 253430927) B253430927
theorem B112635967 : Blo 2057435 112635967 := bstep (se 1 (by rfl) ⟨84476975, by rfl⟩ : syracuseStep 112635967 = 168953951) B168953951
theorem B150181289 : Blo 2057435 150181289 := bstep (se 2 (by rfl) ⟨56317983, by rfl⟩ : syracuseStep 150181289 = 112635967) B112635967
theorem B100120859 : Blo 2057435 100120859 := bstep (se 1 (by rfl) ⟨75090644, by rfl⟩ : syracuseStep 100120859 = 150181289) B150181289
theorem B66747239 : Blo 2057435 66747239 := bstep (se 1 (by rfl) ⟨50060429, by rfl⟩ : syracuseStep 66747239 = 100120859) B100120859
theorem B44498159 : Blo 2057435 44498159 := bstep (se 1 (by rfl) ⟨33373619, by rfl⟩ : syracuseStep 44498159 = 66747239) B66747239
theorem B29665439 : Blo 2057435 29665439 := bstep (se 1 (by rfl) ⟨22249079, by rfl⟩ : syracuseStep 29665439 = 44498159) B44498159
theorem B19776959 : Blo 2057435 19776959 := bstep (se 1 (by rfl) ⟨14832719, by rfl⟩ : syracuseStep 19776959 = 29665439) B29665439
theorem B13184639 : Blo 2057435 13184639 := bstep (se 1 (by rfl) ⟨9888479, by rfl⟩ : syracuseStep 13184639 = 19776959) B19776959
theorem B8789759 : Blo 2057435 8789759 := bstep (se 1 (by rfl) ⟨6592319, by rfl⟩ : syracuseStep 8789759 = 13184639) B13184639
theorem B5859839 : Blo 2057435 5859839 := bstep (se 1 (by rfl) ⟨4394879, by rfl⟩ : syracuseStep 5859839 = 8789759) B8789759
theorem B3906559 : Blo 2057435 3906559 := bstep (se 1 (by rfl) ⟨2929919, by rfl⟩ : syracuseStep 3906559 = 5859839) B5859839
theorem B5208745 : Blo 2057435 5208745 := bstep (se 2 (by rfl) ⟨1953279, by rfl⟩ : syracuseStep 5208745 = 3906559) B3906559
theorem B6944993 : Blo 2057435 6944993 := bstep (se 2 (by rfl) ⟨2604372, by rfl⟩ : syracuseStep 6944993 = 5208745) B5208745
theorem B4629995 : Blo 2057435 4629995 := bstep (se 1 (by rfl) ⟨3472496, by rfl⟩ : syracuseStep 4629995 = 6944993) B6944993
theorem B3086663 : Blo 2057435 3086663 := bstep (se 1 (by rfl) ⟨2314997, by rfl⟩ : syracuseStep 3086663 = 4629995) B4629995
theorem B2057775 : Blo 2057435 2057775 := bstep (se 1 (by rfl) ⟨1543331, by rfl⟩ : syracuseStep 2057775 = 3086663) B3086663
theorem B3086669 : Blo 2057435 3086669 := bbase (se 3 (by rfl) ⟨578750, by rfl⟩ : syracuseStep 3086669 = 1157501) (by norm_num)
theorem B2057779 : Blo 2057435 2057779 := bstep (se 1 (by rfl) ⟨1543334, by rfl⟩ : syracuseStep 2057779 = 3086669) B3086669
theorem B4630013 : Blo 2057435 4630013 := bbase (se 3 (by rfl) ⟨868127, by rfl⟩ : syracuseStep 4630013 = 1736255) (by norm_num)
theorem B3086675 : Blo 2057435 3086675 := bstep (se 1 (by rfl) ⟨2315006, by rfl⟩ : syracuseStep 3086675 = 4630013) B4630013
theorem B2057783 : Blo 2057435 2057783 := bstep (se 1 (by rfl) ⟨1543337, by rfl⟩ : syracuseStep 2057783 = 3086675) B3086675
theorem B3472517 : Blo 2057435 3472517 := bbase (se 4 (by rfl) ⟨325548, by rfl⟩ : syracuseStep 3472517 = 651097) (by norm_num)
theorem B2315011 : Blo 2057435 2315011 := bstep (se 1 (by rfl) ⟨1736258, by rfl⟩ : syracuseStep 2315011 = 3472517) B3472517
theorem B3086681 : Blo 2057435 3086681 := bstep (se 2 (by rfl) ⟨1157505, by rfl⟩ : syracuseStep 3086681 = 2315011) B2315011
theorem B2057787 : Blo 2057435 2057787 := bstep (se 1 (by rfl) ⟨1543340, by rfl⟩ : syracuseStep 2057787 = 3086681) B3086681
theorem B15626357 : Blo 2057435 15626357 := bbase (se 5 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 15626357 = 1464971) (by norm_num)
theorem B10417571 : Blo 2057435 10417571 := bstep (se 1 (by rfl) ⟨7813178, by rfl⟩ : syracuseStep 10417571 = 15626357) B15626357
theorem B6945047 : Blo 2057435 6945047 := bstep (se 1 (by rfl) ⟨5208785, by rfl⟩ : syracuseStep 6945047 = 10417571) B10417571
theorem B4630031 : Blo 2057435 4630031 := bstep (se 1 (by rfl) ⟨3472523, by rfl⟩ : syracuseStep 4630031 = 6945047) B6945047
theorem B3086687 : Blo 2057435 3086687 := bstep (se 1 (by rfl) ⟨2315015, by rfl⟩ : syracuseStep 3086687 = 4630031) B4630031
theorem B2057791 : Blo 2057435 2057791 := bstep (se 1 (by rfl) ⟨1543343, by rfl⟩ : syracuseStep 2057791 = 3086687) B3086687
theorem B3086693 : Blo 2057435 3086693 := bbase (se 4 (by rfl) ⟨289377, by rfl⟩ : syracuseStep 3086693 = 578755) (by norm_num)
theorem B2057795 : Blo 2057435 2057795 := bstep (se 1 (by rfl) ⟨1543346, by rfl⟩ : syracuseStep 2057795 = 3086693) B3086693
theorem B3906605 : Blo 2057435 3906605 := bbase (se 3 (by rfl) ⟨732488, by rfl⟩ : syracuseStep 3906605 = 1464977) (by norm_num)
theorem B2604403 : Blo 2057435 2604403 := bstep (se 1 (by rfl) ⟨1953302, by rfl⟩ : syracuseStep 2604403 = 3906605) B3906605
theorem B3472537 : Blo 2057435 3472537 := bstep (se 2 (by rfl) ⟨1302201, by rfl⟩ : syracuseStep 3472537 = 2604403) B2604403
theorem B4630049 : Blo 2057435 4630049 := bstep (se 2 (by rfl) ⟨1736268, by rfl⟩ : syracuseStep 4630049 = 3472537) B3472537
theorem B3086699 : Blo 2057435 3086699 := bstep (se 1 (by rfl) ⟨2315024, by rfl⟩ : syracuseStep 3086699 = 4630049) B4630049
theorem B2057799 : Blo 2057435 2057799 := bstep (se 1 (by rfl) ⟨1543349, by rfl⟩ : syracuseStep 2057799 = 3086699) B3086699
theorem B2315029 : Blo 2057435 2315029 := bbase (se 6 (by rfl) ⟨54258, by rfl⟩ : syracuseStep 2315029 = 108517) (by norm_num)
theorem B3086705 : Blo 2057435 3086705 := bstep (se 2 (by rfl) ⟨1157514, by rfl⟩ : syracuseStep 3086705 = 2315029) B2315029
theorem B2057803 : Blo 2057435 2057803 := bstep (se 1 (by rfl) ⟨1543352, by rfl⟩ : syracuseStep 2057803 = 3086705) B3086705
theorem B2604413 : Blo 2057435 2604413 := bbase (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) (by norm_num)
theorem B6945101 : Blo 2057435 6945101 := bstep (se 3 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 6945101 = 2604413) B2604413
theorem B4630067 : Blo 2057435 4630067 := bstep (se 1 (by rfl) ⟨3472550, by rfl⟩ : syracuseStep 4630067 = 6945101) B6945101
theorem B3086711 : Blo 2057435 3086711 := bstep (se 1 (by rfl) ⟨2315033, by rfl⟩ : syracuseStep 3086711 = 4630067) B4630067
theorem B2057807 : Blo 2057435 2057807 := bstep (se 1 (by rfl) ⟨1543355, by rfl⟩ : syracuseStep 2057807 = 3086711) B3086711
theorem B3086717 : Blo 2057435 3086717 := bbase (se 3 (by rfl) ⟨578759, by rfl⟩ : syracuseStep 3086717 = 1157519) (by norm_num)
theorem B2057811 : Blo 2057435 2057811 := bstep (se 1 (by rfl) ⟨1543358, by rfl⟩ : syracuseStep 2057811 = 3086717) B3086717
theorem B4630085 : Blo 2057435 4630085 := bbase (se 4 (by rfl) ⟨434070, by rfl⟩ : syracuseStep 4630085 = 868141) (by norm_num)
theorem B3086723 : Blo 2057435 3086723 := bstep (se 1 (by rfl) ⟨2315042, by rfl⟩ : syracuseStep 3086723 = 4630085) B4630085
theorem B2057815 : Blo 2057435 2057815 := bstep (se 1 (by rfl) ⟨1543361, by rfl⟩ : syracuseStep 2057815 = 3086723) B3086723
theorem B12515381 : Blo 2057435 12515381 := bbase (se 5 (by rfl) ⟨586658, by rfl⟩ : syracuseStep 12515381 = 1173317) (by norm_num)
theorem B8343587 : Blo 2057435 8343587 := bstep (se 1 (by rfl) ⟨6257690, by rfl⟩ : syracuseStep 8343587 = 12515381) B12515381
theorem B5562391 : Blo 2057435 5562391 := bstep (se 1 (by rfl) ⟨4171793, by rfl⟩ : syracuseStep 5562391 = 8343587) B8343587
theorem B7416521 : Blo 2057435 7416521 := bstep (se 2 (by rfl) ⟨2781195, by rfl⟩ : syracuseStep 7416521 = 5562391) B5562391
theorem B4944347 : Blo 2057435 4944347 := bstep (se 1 (by rfl) ⟨3708260, by rfl⟩ : syracuseStep 4944347 = 7416521) B7416521
theorem B3296231 : Blo 2057435 3296231 := bstep (se 1 (by rfl) ⟨2472173, by rfl⟩ : syracuseStep 3296231 = 4944347) B4944347
theorem B2197487 : Blo 2057435 2197487 := bstep (se 1 (by rfl) ⟨1648115, by rfl⟩ : syracuseStep 2197487 = 3296231) B3296231
theorem B5859965 : Blo 2057435 5859965 := bstep (se 3 (by rfl) ⟨1098743, by rfl⟩ : syracuseStep 5859965 = 2197487) B2197487
theorem B3906643 : Blo 2057435 3906643 := bstep (se 1 (by rfl) ⟨2929982, by rfl⟩ : syracuseStep 3906643 = 5859965) B5859965
theorem B5208857 : Blo 2057435 5208857 := bstep (se 2 (by rfl) ⟨1953321, by rfl⟩ : syracuseStep 5208857 = 3906643) B3906643
theorem B3472571 : Blo 2057435 3472571 := bstep (se 1 (by rfl) ⟨2604428, by rfl⟩ : syracuseStep 3472571 = 5208857) B5208857
theorem B2315047 : Blo 2057435 2315047 := bstep (se 1 (by rfl) ⟨1736285, by rfl⟩ : syracuseStep 2315047 = 3472571) B3472571
theorem B3086729 : Blo 2057435 3086729 := bstep (se 2 (by rfl) ⟨1157523, by rfl⟩ : syracuseStep 3086729 = 2315047) B2315047
theorem B2057819 : Blo 2057435 2057819 := bstep (se 1 (by rfl) ⟨1543364, by rfl⟩ : syracuseStep 2057819 = 3086729) B3086729
theorem B10417733 : Blo 2057435 10417733 := bbase (se 4 (by rfl) ⟨976662, by rfl⟩ : syracuseStep 10417733 = 1953325) (by norm_num)
theorem B6945155 : Blo 2057435 6945155 := bstep (se 1 (by rfl) ⟨5208866, by rfl⟩ : syracuseStep 6945155 = 10417733) B10417733
theorem B4630103 : Blo 2057435 4630103 := bstep (se 1 (by rfl) ⟨3472577, by rfl⟩ : syracuseStep 4630103 = 6945155) B6945155
theorem B3086735 : Blo 2057435 3086735 := bstep (se 1 (by rfl) ⟨2315051, by rfl⟩ : syracuseStep 3086735 = 4630103) B4630103
theorem B2057823 : Blo 2057435 2057823 := bstep (se 1 (by rfl) ⟨1543367, by rfl⟩ : syracuseStep 2057823 = 3086735) B3086735
theorem B3086741 : Blo 2057435 3086741 := bbase (se 6 (by rfl) ⟨72345, by rfl⟩ : syracuseStep 3086741 = 144691) (by norm_num)
theorem B2057827 : Blo 2057435 2057827 := bstep (se 1 (by rfl) ⟨1543370, by rfl⟩ : syracuseStep 2057827 = 3086741) B3086741
theorem B3567997 : Blo 2057435 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B4757329 : Blo 2057435 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B6343105 : Blo 2057435 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B8457473 : Blo 2057435 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B22553261 : Blo 2057435 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B15035507 : Blo 2057435 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B10023671 : Blo 2057435 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B6682447 : Blo 2057435 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B8909929 : Blo 2057435 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B11879905 : Blo 2057435 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B15839873 : Blo 2057435 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B10559915 : Blo 2057435 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B7039943 : Blo 2057435 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B4693295 : Blo 2057435 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B3128863 : Blo 2057435 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B4171817 : Blo 2057435 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B2781211 : Blo 2057435 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B3708281 : Blo 2057435 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B9888749 : Blo 2057435 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B6592499 : Blo 2057435 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B4394999 : Blo 2057435 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B11719997 : Blo 2057435 11719997 := bstep (se 3 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 11719997 = 4394999) B4394999
theorem B7813331 : Blo 2057435 7813331 := bstep (se 1 (by rfl) ⟨5859998, by rfl⟩ : syracuseStep 7813331 = 11719997) B11719997
theorem B5208887 : Blo 2057435 5208887 := bstep (se 1 (by rfl) ⟨3906665, by rfl⟩ : syracuseStep 5208887 = 7813331) B7813331
theorem B3472591 : Blo 2057435 3472591 := bstep (se 1 (by rfl) ⟨2604443, by rfl⟩ : syracuseStep 3472591 = 5208887) B5208887
theorem B4630121 : Blo 2057435 4630121 := bstep (se 2 (by rfl) ⟨1736295, by rfl⟩ : syracuseStep 4630121 = 3472591) B3472591
theorem B3086747 : Blo 2057435 3086747 := bstep (se 1 (by rfl) ⟨2315060, by rfl⟩ : syracuseStep 3086747 = 4630121) B4630121
theorem B2057831 : Blo 2057435 2057831 := bstep (se 1 (by rfl) ⟨1543373, by rfl⟩ : syracuseStep 2057831 = 3086747) B3086747
theorem B2315065 : Blo 2057435 2315065 := bbase (se 2 (by rfl) ⟨868149, by rfl⟩ : syracuseStep 2315065 = 1736299) (by norm_num)
theorem B3086753 : Blo 2057435 3086753 := bstep (se 2 (by rfl) ⟨1157532, by rfl⟩ : syracuseStep 3086753 = 2315065) B2315065
theorem B2057835 : Blo 2057435 2057835 := bstep (se 1 (by rfl) ⟨1543376, by rfl⟩ : syracuseStep 2057835 = 3086753) B3086753
theorem B5860021 : Blo 2057435 5860021 := bbase (se 5 (by rfl) ⟨274688, by rfl⟩ : syracuseStep 5860021 = 549377) (by norm_num)
theorem B7813361 : Blo 2057435 7813361 := bstep (se 2 (by rfl) ⟨2930010, by rfl⟩ : syracuseStep 7813361 = 5860021) B5860021
theorem B5208907 : Blo 2057435 5208907 := bstep (se 1 (by rfl) ⟨3906680, by rfl⟩ : syracuseStep 5208907 = 7813361) B7813361
theorem B6945209 : Blo 2057435 6945209 := bstep (se 2 (by rfl) ⟨2604453, by rfl⟩ : syracuseStep 6945209 = 5208907) B5208907
theorem B4630139 : Blo 2057435 4630139 := bstep (se 1 (by rfl) ⟨3472604, by rfl⟩ : syracuseStep 4630139 = 6945209) B6945209
theorem B3086759 : Blo 2057435 3086759 := bstep (se 1 (by rfl) ⟨2315069, by rfl⟩ : syracuseStep 3086759 = 4630139) B4630139
theorem B2057839 : Blo 2057435 2057839 := bstep (se 1 (by rfl) ⟨1543379, by rfl⟩ : syracuseStep 2057839 = 3086759) B3086759
theorem B3086765 : Blo 2057435 3086765 := bbase (se 3 (by rfl) ⟨578768, by rfl⟩ : syracuseStep 3086765 = 1157537) (by norm_num)
theorem B2057843 : Blo 2057435 2057843 := bstep (se 1 (by rfl) ⟨1543382, by rfl⟩ : syracuseStep 2057843 = 3086765) B3086765
theorem B4630157 : Blo 2057435 4630157 := bbase (se 3 (by rfl) ⟨868154, by rfl⟩ : syracuseStep 4630157 = 1736309) (by norm_num)
theorem B3086771 : Blo 2057435 3086771 := bstep (se 1 (by rfl) ⟨2315078, by rfl⟩ : syracuseStep 3086771 = 4630157) B4630157
theorem B2057847 : Blo 2057435 2057847 := bstep (se 1 (by rfl) ⟨1543385, by rfl⟩ : syracuseStep 2057847 = 3086771) B3086771
theorem B2604469 : Blo 2057435 2604469 := bbase (se 5 (by rfl) ⟨122084, by rfl⟩ : syracuseStep 2604469 = 244169) (by norm_num)
theorem B3472625 : Blo 2057435 3472625 := bstep (se 2 (by rfl) ⟨1302234, by rfl⟩ : syracuseStep 3472625 = 2604469) B2604469
theorem B2315083 : Blo 2057435 2315083 := bstep (se 1 (by rfl) ⟨1736312, by rfl⟩ : syracuseStep 2315083 = 3472625) B3472625
theorem B3086777 : Blo 2057435 3086777 := bstep (se 2 (by rfl) ⟨1157541, by rfl⟩ : syracuseStep 3086777 = 2315083) B2315083
theorem B2057851 : Blo 2057435 2057851 := bstep (se 1 (by rfl) ⟨1543388, by rfl⟩ : syracuseStep 2057851 = 3086777) B3086777
theorem B5952437 : Blo 2057435 5952437 := bbase (se 5 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 5952437 = 558041) (by norm_num)
theorem B3968291 : Blo 2057435 3968291 := bstep (se 1 (by rfl) ⟨2976218, by rfl⟩ : syracuseStep 3968291 = 5952437) B5952437
theorem B10582109 : Blo 2057435 10582109 := bstep (se 3 (by rfl) ⟨1984145, by rfl⟩ : syracuseStep 10582109 = 3968291) B3968291
theorem B7054739 : Blo 2057435 7054739 := bstep (se 1 (by rfl) ⟨5291054, by rfl⟩ : syracuseStep 7054739 = 10582109) B10582109
theorem B4703159 : Blo 2057435 4703159 := bstep (se 1 (by rfl) ⟨3527369, by rfl⟩ : syracuseStep 4703159 = 7054739) B7054739
theorem B3135439 : Blo 2057435 3135439 := bstep (se 1 (by rfl) ⟨2351579, by rfl⟩ : syracuseStep 3135439 = 4703159) B4703159
theorem B4180585 : Blo 2057435 4180585 := bstep (se 2 (by rfl) ⟨1567719, by rfl⟩ : syracuseStep 4180585 = 3135439) B3135439
theorem B356743253 : Blo 2057435 356743253 := bstep (se 8 (by rfl) ⟨2090292, by rfl⟩ : syracuseStep 356743253 = 4180585) B4180585
theorem B237828835 : Blo 2057435 237828835 := bstep (se 1 (by rfl) ⟨178371626, by rfl⟩ : syracuseStep 237828835 = 356743253) B356743253
theorem B317105113 : Blo 2057435 317105113 := bstep (se 2 (by rfl) ⟨118914417, by rfl⟩ : syracuseStep 317105113 = 237828835) B237828835
theorem B422806817 : Blo 2057435 422806817 := bstep (se 2 (by rfl) ⟨158552556, by rfl⟩ : syracuseStep 422806817 = 317105113) B317105113
theorem B281871211 : Blo 2057435 281871211 := bstep (se 1 (by rfl) ⟨211403408, by rfl⟩ : syracuseStep 281871211 = 422806817) B422806817
theorem B375828281 : Blo 2057435 375828281 := bstep (se 2 (by rfl) ⟨140935605, by rfl⟩ : syracuseStep 375828281 = 281871211) B281871211
theorem B250552187 : Blo 2057435 250552187 := bstep (se 1 (by rfl) ⟨187914140, by rfl⟩ : syracuseStep 250552187 = 375828281) B375828281
theorem B167034791 : Blo 2057435 167034791 := bstep (se 1 (by rfl) ⟨125276093, by rfl⟩ : syracuseStep 167034791 = 250552187) B250552187
theorem B111356527 : Blo 2057435 111356527 := bstep (se 1 (by rfl) ⟨83517395, by rfl⟩ : syracuseStep 111356527 = 167034791) B167034791
theorem B148475369 : Blo 2057435 148475369 := bstep (se 2 (by rfl) ⟨55678263, by rfl⟩ : syracuseStep 148475369 = 111356527) B111356527
theorem B98983579 : Blo 2057435 98983579 := bstep (se 1 (by rfl) ⟨74237684, by rfl⟩ : syracuseStep 98983579 = 148475369) B148475369
theorem B131978105 : Blo 2057435 131978105 := bstep (se 2 (by rfl) ⟨49491789, by rfl⟩ : syracuseStep 131978105 = 98983579) B98983579
theorem B87985403 : Blo 2057435 87985403 := bstep (se 1 (by rfl) ⟨65989052, by rfl⟩ : syracuseStep 87985403 = 131978105) B131978105
theorem B58656935 : Blo 2057435 58656935 := bstep (se 1 (by rfl) ⟨43992701, by rfl⟩ : syracuseStep 58656935 = 87985403) B87985403
theorem B39104623 : Blo 2057435 39104623 := bstep (se 1 (by rfl) ⟨29328467, by rfl⟩ : syracuseStep 39104623 = 58656935) B58656935
theorem B52139497 : Blo 2057435 52139497 := bstep (se 2 (by rfl) ⟨19552311, by rfl⟩ : syracuseStep 52139497 = 39104623) B39104623
theorem B69519329 : Blo 2057435 69519329 := bstep (se 2 (by rfl) ⟨26069748, by rfl⟩ : syracuseStep 69519329 = 52139497) B52139497
theorem B46346219 : Blo 2057435 46346219 := bstep (se 1 (by rfl) ⟨34759664, by rfl⟩ : syracuseStep 46346219 = 69519329) B69519329
theorem B30897479 : Blo 2057435 30897479 := bstep (se 1 (by rfl) ⟨23173109, by rfl⟩ : syracuseStep 30897479 = 46346219) B46346219
theorem B20598319 : Blo 2057435 20598319 := bstep (se 1 (by rfl) ⟨15448739, by rfl⟩ : syracuseStep 20598319 = 30897479) B30897479
theorem B109857701 : Blo 2057435 109857701 := bstep (se 4 (by rfl) ⟨10299159, by rfl⟩ : syracuseStep 109857701 = 20598319) B20598319
theorem B73238467 : Blo 2057435 73238467 := bstep (se 1 (by rfl) ⟨54928850, by rfl⟩ : syracuseStep 73238467 = 109857701) B109857701
theorem B97651289 : Blo 2057435 97651289 := bstep (se 2 (by rfl) ⟨36619233, by rfl⟩ : syracuseStep 97651289 = 73238467) B73238467
theorem B260403437 : Blo 2057435 260403437 := bstep (se 3 (by rfl) ⟨48825644, by rfl⟩ : syracuseStep 260403437 = 97651289) B97651289
theorem B173602291 : Blo 2057435 173602291 := bstep (se 1 (by rfl) ⟨130201718, by rfl⟩ : syracuseStep 173602291 = 260403437) B260403437
theorem B231469721 : Blo 2057435 231469721 := bstep (se 2 (by rfl) ⟨86801145, by rfl⟩ : syracuseStep 231469721 = 173602291) B173602291
theorem B154313147 : Blo 2057435 154313147 := bstep (se 1 (by rfl) ⟨115734860, by rfl⟩ : syracuseStep 154313147 = 231469721) B231469721
theorem B102875431 : Blo 2057435 102875431 := bstep (se 1 (by rfl) ⟨77156573, by rfl⟩ : syracuseStep 102875431 = 154313147) B154313147
theorem B137167241 : Blo 2057435 137167241 := bstep (se 2 (by rfl) ⟨51437715, by rfl⟩ : syracuseStep 137167241 = 102875431) B102875431
theorem B365779309 : Blo 2057435 365779309 := bstep (se 3 (by rfl) ⟨68583620, by rfl⟩ : syracuseStep 365779309 = 137167241) B137167241
theorem B487705745 : Blo 2057435 487705745 := bstep (se 2 (by rfl) ⟨182889654, by rfl⟩ : syracuseStep 487705745 = 365779309) B365779309
theorem B325137163 : Blo 2057435 325137163 := bstep (se 1 (by rfl) ⟨243852872, by rfl⟩ : syracuseStep 325137163 = 487705745) B487705745
theorem B433516217 : Blo 2057435 433516217 := bstep (se 2 (by rfl) ⟨162568581, by rfl⟩ : syracuseStep 433516217 = 325137163) B325137163
theorem B4624172981 : Blo 2057435 4624172981 := bstep (se 5 (by rfl) ⟨216758108, by rfl⟩ : syracuseStep 4624172981 = 433516217) B433516217
theorem B3082781987 : Blo 2057435 3082781987 := bstep (se 1 (by rfl) ⟨2312086490, by rfl⟩ : syracuseStep 3082781987 = 4624172981) B4624172981
theorem B2055187991 : Blo 2057435 2055187991 := bstep (se 1 (by rfl) ⟨1541390993, by rfl⟩ : syracuseStep 2055187991 = 3082781987) B3082781987
theorem B1370125327 : Blo 2057435 1370125327 := bstep (se 1 (by rfl) ⟨1027593995, by rfl⟩ : syracuseStep 1370125327 = 2055187991) B2055187991
theorem B1826833769 : Blo 2057435 1826833769 := bstep (se 2 (by rfl) ⟨685062663, by rfl⟩ : syracuseStep 1826833769 = 1370125327) B1370125327
theorem B1217889179 : Blo 2057435 1217889179 := bstep (se 1 (by rfl) ⟨913416884, by rfl⟩ : syracuseStep 1217889179 = 1826833769) B1826833769
theorem B811926119 : Blo 2057435 811926119 := bstep (se 1 (by rfl) ⟨608944589, by rfl⟩ : syracuseStep 811926119 = 1217889179) B1217889179
theorem B541284079 : Blo 2057435 541284079 := bstep (se 1 (by rfl) ⟨405963059, by rfl⟩ : syracuseStep 541284079 = 811926119) B811926119
theorem B721712105 : Blo 2057435 721712105 := bstep (se 2 (by rfl) ⟨270642039, by rfl⟩ : syracuseStep 721712105 = 541284079) B541284079
theorem B481141403 : Blo 2057435 481141403 := bstep (se 1 (by rfl) ⟨360856052, by rfl⟩ : syracuseStep 481141403 = 721712105) B721712105
theorem B320760935 : Blo 2057435 320760935 := bstep (se 1 (by rfl) ⟨240570701, by rfl⟩ : syracuseStep 320760935 = 481141403) B481141403
theorem B213840623 : Blo 2057435 213840623 := bstep (se 1 (by rfl) ⟨160380467, by rfl⟩ : syracuseStep 213840623 = 320760935) B320760935
theorem B142560415 : Blo 2057435 142560415 := bstep (se 1 (by rfl) ⟨106920311, by rfl⟩ : syracuseStep 142560415 = 213840623) B213840623
theorem B190080553 : Blo 2057435 190080553 := bstep (se 2 (by rfl) ⟨71280207, by rfl⟩ : syracuseStep 190080553 = 142560415) B142560415
theorem B253440737 : Blo 2057435 253440737 := bstep (se 2 (by rfl) ⟨95040276, by rfl⟩ : syracuseStep 253440737 = 190080553) B190080553
theorem B168960491 : Blo 2057435 168960491 := bstep (se 1 (by rfl) ⟨126720368, by rfl⟩ : syracuseStep 168960491 = 253440737) B253440737
theorem B112640327 : Blo 2057435 112640327 := bstep (se 1 (by rfl) ⟨84480245, by rfl⟩ : syracuseStep 112640327 = 168960491) B168960491
theorem B75093551 : Blo 2057435 75093551 := bstep (se 1 (by rfl) ⟨56320163, by rfl⟩ : syracuseStep 75093551 = 112640327) B112640327
theorem B50062367 : Blo 2057435 50062367 := bstep (se 1 (by rfl) ⟨37546775, by rfl⟩ : syracuseStep 50062367 = 75093551) B75093551
theorem B33374911 : Blo 2057435 33374911 := bstep (se 1 (by rfl) ⟨25031183, by rfl⟩ : syracuseStep 33374911 = 50062367) B50062367
theorem B44499881 : Blo 2057435 44499881 := bstep (se 2 (by rfl) ⟨16687455, by rfl⟩ : syracuseStep 44499881 = 33374911) B33374911
theorem B29666587 : Blo 2057435 29666587 := bstep (se 1 (by rfl) ⟨22249940, by rfl⟩ : syracuseStep 29666587 = 44499881) B44499881
theorem B39555449 : Blo 2057435 39555449 := bstep (se 2 (by rfl) ⟨14833293, by rfl⟩ : syracuseStep 39555449 = 29666587) B29666587
theorem B26370299 : Blo 2057435 26370299 := bstep (se 1 (by rfl) ⟨19777724, by rfl⟩ : syracuseStep 26370299 = 39555449) B39555449
theorem B17580199 : Blo 2057435 17580199 := bstep (se 1 (by rfl) ⟨13185149, by rfl⟩ : syracuseStep 17580199 = 26370299) B26370299
theorem B23440265 : Blo 2057435 23440265 := bstep (se 2 (by rfl) ⟨8790099, by rfl⟩ : syracuseStep 23440265 = 17580199) B17580199
theorem B15626843 : Blo 2057435 15626843 := bstep (se 1 (by rfl) ⟨11720132, by rfl⟩ : syracuseStep 15626843 = 23440265) B23440265
theorem B10417895 : Blo 2057435 10417895 := bstep (se 1 (by rfl) ⟨7813421, by rfl⟩ : syracuseStep 10417895 = 15626843) B15626843
theorem B6945263 : Blo 2057435 6945263 := bstep (se 1 (by rfl) ⟨5208947, by rfl⟩ : syracuseStep 6945263 = 10417895) B10417895
theorem B4630175 : Blo 2057435 4630175 := bstep (se 1 (by rfl) ⟨3472631, by rfl⟩ : syracuseStep 4630175 = 6945263) B6945263
theorem B3086783 : Blo 2057435 3086783 := bstep (se 1 (by rfl) ⟨2315087, by rfl⟩ : syracuseStep 3086783 = 4630175) B4630175
theorem B2057855 : Blo 2057435 2057855 := bstep (se 1 (by rfl) ⟨1543391, by rfl⟩ : syracuseStep 2057855 = 3086783) B3086783
theorem B3086789 : Blo 2057435 3086789 := bbase (se 4 (by rfl) ⟨289386, by rfl⟩ : syracuseStep 3086789 = 578773) (by norm_num)
theorem B2057859 : Blo 2057435 2057859 := bstep (se 1 (by rfl) ⟨1543394, by rfl⟩ : syracuseStep 2057859 = 3086789) B3086789
theorem B3472645 : Blo 2057435 3472645 := bbase (se 4 (by rfl) ⟨325560, by rfl⟩ : syracuseStep 3472645 = 651121) (by norm_num)
theorem B4630193 : Blo 2057435 4630193 := bstep (se 2 (by rfl) ⟨1736322, by rfl⟩ : syracuseStep 4630193 = 3472645) B3472645
theorem B3086795 : Blo 2057435 3086795 := bstep (se 1 (by rfl) ⟨2315096, by rfl⟩ : syracuseStep 3086795 = 4630193) B4630193
theorem B2057863 : Blo 2057435 2057863 := bstep (se 1 (by rfl) ⟨1543397, by rfl⟩ : syracuseStep 2057863 = 3086795) B3086795
theorem B2315101 : Blo 2057435 2315101 := bbase (se 3 (by rfl) ⟨434081, by rfl⟩ : syracuseStep 2315101 = 868163) (by norm_num)
theorem B3086801 : Blo 2057435 3086801 := bstep (se 2 (by rfl) ⟨1157550, by rfl⟩ : syracuseStep 3086801 = 2315101) B2315101
theorem B2057867 : Blo 2057435 2057867 := bstep (se 1 (by rfl) ⟨1543400, by rfl⟩ : syracuseStep 2057867 = 3086801) B3086801
theorem B6945317 : Blo 2057435 6945317 := bbase (se 4 (by rfl) ⟨651123, by rfl⟩ : syracuseStep 6945317 = 1302247) (by norm_num)
theorem B4630211 : Blo 2057435 4630211 := bstep (se 1 (by rfl) ⟨3472658, by rfl⟩ : syracuseStep 4630211 = 6945317) B6945317
theorem B3086807 : Blo 2057435 3086807 := bstep (se 1 (by rfl) ⟨2315105, by rfl⟩ : syracuseStep 3086807 = 4630211) B4630211
theorem B2057871 : Blo 2057435 2057871 := bstep (se 1 (by rfl) ⟨1543403, by rfl⟩ : syracuseStep 2057871 = 3086807) B3086807
theorem B3086813 : Blo 2057435 3086813 := bbase (se 3 (by rfl) ⟨578777, by rfl⟩ : syracuseStep 3086813 = 1157555) (by norm_num)
theorem B2057875 : Blo 2057435 2057875 := bstep (se 1 (by rfl) ⟨1543406, by rfl⟩ : syracuseStep 2057875 = 3086813) B3086813
theorem B4630229 : Blo 2057435 4630229 := bbase (se 7 (by rfl) ⟨54260, by rfl⟩ : syracuseStep 4630229 = 108521) (by norm_num)
theorem B3086819 : Blo 2057435 3086819 := bstep (se 1 (by rfl) ⟨2315114, by rfl⟩ : syracuseStep 3086819 = 4630229) B4630229
theorem B2057879 : Blo 2057435 2057879 := bstep (se 1 (by rfl) ⟨1543409, by rfl⟩ : syracuseStep 2057879 = 3086819) B3086819
theorem B3296333 : Blo 2057435 3296333 := bbase (se 3 (by rfl) ⟨618062, by rfl⟩ : syracuseStep 3296333 = 1236125) (by norm_num)
theorem B8790221 : Blo 2057435 8790221 := bstep (se 3 (by rfl) ⟨1648166, by rfl⟩ : syracuseStep 8790221 = 3296333) B3296333
theorem B5860147 : Blo 2057435 5860147 := bstep (se 1 (by rfl) ⟨4395110, by rfl⟩ : syracuseStep 5860147 = 8790221) B8790221
theorem B7813529 : Blo 2057435 7813529 := bstep (se 2 (by rfl) ⟨2930073, by rfl⟩ : syracuseStep 7813529 = 5860147) B5860147
theorem B5209019 : Blo 2057435 5209019 := bstep (se 1 (by rfl) ⟨3906764, by rfl⟩ : syracuseStep 5209019 = 7813529) B7813529
theorem B3472679 : Blo 2057435 3472679 := bstep (se 1 (by rfl) ⟨2604509, by rfl⟩ : syracuseStep 3472679 = 5209019) B5209019
theorem B2315119 : Blo 2057435 2315119 := bstep (se 1 (by rfl) ⟨1736339, by rfl⟩ : syracuseStep 2315119 = 3472679) B3472679
theorem B3086825 : Blo 2057435 3086825 := bstep (se 2 (by rfl) ⟨1157559, by rfl⟩ : syracuseStep 3086825 = 2315119) B2315119
theorem B2057883 : Blo 2057435 2057883 := bstep (se 1 (by rfl) ⟨1543412, by rfl⟩ : syracuseStep 2057883 = 3086825) B3086825
theorem B14833525 : Blo 2057435 14833525 := bbase (se 5 (by rfl) ⟨695321, by rfl⟩ : syracuseStep 14833525 = 1390643) (by norm_num)
theorem B19778033 : Blo 2057435 19778033 := bstep (se 2 (by rfl) ⟨7416762, by rfl⟩ : syracuseStep 19778033 = 14833525) B14833525
theorem B13185355 : Blo 2057435 13185355 := bstep (se 1 (by rfl) ⟨9889016, by rfl⟩ : syracuseStep 13185355 = 19778033) B19778033
theorem B17580473 : Blo 2057435 17580473 := bstep (se 2 (by rfl) ⟨6592677, by rfl⟩ : syracuseStep 17580473 = 13185355) B13185355
theorem B11720315 : Blo 2057435 11720315 := bstep (se 1 (by rfl) ⟨8790236, by rfl⟩ : syracuseStep 11720315 = 17580473) B17580473
theorem B7813543 : Blo 2057435 7813543 := bstep (se 1 (by rfl) ⟨5860157, by rfl⟩ : syracuseStep 7813543 = 11720315) B11720315
theorem B10418057 : Blo 2057435 10418057 := bstep (se 2 (by rfl) ⟨3906771, by rfl⟩ : syracuseStep 10418057 = 7813543) B7813543
theorem B6945371 : Blo 2057435 6945371 := bstep (se 1 (by rfl) ⟨5209028, by rfl⟩ : syracuseStep 6945371 = 10418057) B10418057
theorem B4630247 : Blo 2057435 4630247 := bstep (se 1 (by rfl) ⟨3472685, by rfl⟩ : syracuseStep 4630247 = 6945371) B6945371
theorem B3086831 : Blo 2057435 3086831 := bstep (se 1 (by rfl) ⟨2315123, by rfl⟩ : syracuseStep 3086831 = 4630247) B4630247
theorem B2057887 : Blo 2057435 2057887 := bstep (se 1 (by rfl) ⟨1543415, by rfl⟩ : syracuseStep 2057887 = 3086831) B3086831
theorem B3086837 : Blo 2057435 3086837 := bbase (se 5 (by rfl) ⟨144695, by rfl⟩ : syracuseStep 3086837 = 289391) (by norm_num)
theorem B2057891 : Blo 2057435 2057891 := bstep (se 1 (by rfl) ⟨1543418, by rfl⟩ : syracuseStep 2057891 = 3086837) B3086837
theorem B5860181 : Blo 2057435 5860181 := bbase (se 9 (by rfl) ⟨17168, by rfl⟩ : syracuseStep 5860181 = 34337) (by norm_num)
theorem B3906787 : Blo 2057435 3906787 := bstep (se 1 (by rfl) ⟨2930090, by rfl⟩ : syracuseStep 3906787 = 5860181) B5860181
theorem B5209049 : Blo 2057435 5209049 := bstep (se 2 (by rfl) ⟨1953393, by rfl⟩ : syracuseStep 5209049 = 3906787) B3906787
theorem B3472699 : Blo 2057435 3472699 := bstep (se 1 (by rfl) ⟨2604524, by rfl⟩ : syracuseStep 3472699 = 5209049) B5209049
theorem B4630265 : Blo 2057435 4630265 := bstep (se 2 (by rfl) ⟨1736349, by rfl⟩ : syracuseStep 4630265 = 3472699) B3472699
theorem B3086843 : Blo 2057435 3086843 := bstep (se 1 (by rfl) ⟨2315132, by rfl⟩ : syracuseStep 3086843 = 4630265) B4630265
theorem B2057895 : Blo 2057435 2057895 := bstep (se 1 (by rfl) ⟨1543421, by rfl⟩ : syracuseStep 2057895 = 3086843) B3086843
theorem B2315137 : Blo 2057435 2315137 := bbase (se 2 (by rfl) ⟨868176, by rfl⟩ : syracuseStep 2315137 = 1736353) (by norm_num)
theorem B3086849 : Blo 2057435 3086849 := bstep (se 2 (by rfl) ⟨1157568, by rfl⟩ : syracuseStep 3086849 = 2315137) B2315137
theorem B2057899 : Blo 2057435 2057899 := bstep (se 1 (by rfl) ⟨1543424, by rfl⟩ : syracuseStep 2057899 = 3086849) B3086849
theorem B5209069 : Blo 2057435 5209069 := bbase (se 3 (by rfl) ⟨976700, by rfl⟩ : syracuseStep 5209069 = 1953401) (by norm_num)
theorem B6945425 : Blo 2057435 6945425 := bstep (se 2 (by rfl) ⟨2604534, by rfl⟩ : syracuseStep 6945425 = 5209069) B5209069
theorem B4630283 : Blo 2057435 4630283 := bstep (se 1 (by rfl) ⟨3472712, by rfl⟩ : syracuseStep 4630283 = 6945425) B6945425
theorem B3086855 : Blo 2057435 3086855 := bstep (se 1 (by rfl) ⟨2315141, by rfl⟩ : syracuseStep 3086855 = 4630283) B4630283
theorem B2057903 : Blo 2057435 2057903 := bstep (se 1 (by rfl) ⟨1543427, by rfl⟩ : syracuseStep 2057903 = 3086855) B3086855
theorem B3086861 : Blo 2057435 3086861 := bbase (se 3 (by rfl) ⟨578786, by rfl⟩ : syracuseStep 3086861 = 1157573) (by norm_num)
theorem B2057907 : Blo 2057435 2057907 := bstep (se 1 (by rfl) ⟨1543430, by rfl⟩ : syracuseStep 2057907 = 3086861) B3086861
theorem B4630301 : Blo 2057435 4630301 := bbase (se 3 (by rfl) ⟨868181, by rfl⟩ : syracuseStep 4630301 = 1736363) (by norm_num)
theorem B3086867 : Blo 2057435 3086867 := bstep (se 1 (by rfl) ⟨2315150, by rfl⟩ : syracuseStep 3086867 = 4630301) B4630301
theorem B2057911 : Blo 2057435 2057911 := bstep (se 1 (by rfl) ⟨1543433, by rfl⟩ : syracuseStep 2057911 = 3086867) B3086867
theorem B3472733 : Blo 2057435 3472733 := bbase (se 3 (by rfl) ⟨651137, by rfl⟩ : syracuseStep 3472733 = 1302275) (by norm_num)
theorem B2315155 : Blo 2057435 2315155 := bstep (se 1 (by rfl) ⟨1736366, by rfl⟩ : syracuseStep 2315155 = 3472733) B3472733
theorem B3086873 : Blo 2057435 3086873 := bstep (se 2 (by rfl) ⟨1157577, by rfl⟩ : syracuseStep 3086873 = 2315155) B2315155
theorem B2057915 : Blo 2057435 2057915 := bstep (se 1 (by rfl) ⟨1543436, by rfl⟩ : syracuseStep 2057915 = 3086873) B3086873
theorem B8790373 : Blo 2057435 8790373 := bbase (se 4 (by rfl) ⟨824097, by rfl⟩ : syracuseStep 8790373 = 1648195) (by norm_num)
theorem B11720497 : Blo 2057435 11720497 := bstep (se 2 (by rfl) ⟨4395186, by rfl⟩ : syracuseStep 11720497 = 8790373) B8790373
theorem B15627329 : Blo 2057435 15627329 := bstep (se 2 (by rfl) ⟨5860248, by rfl⟩ : syracuseStep 15627329 = 11720497) B11720497
theorem B10418219 : Blo 2057435 10418219 := bstep (se 1 (by rfl) ⟨7813664, by rfl⟩ : syracuseStep 10418219 = 15627329) B15627329
theorem B6945479 : Blo 2057435 6945479 := bstep (se 1 (by rfl) ⟨5209109, by rfl⟩ : syracuseStep 6945479 = 10418219) B10418219
theorem B4630319 : Blo 2057435 4630319 := bstep (se 1 (by rfl) ⟨3472739, by rfl⟩ : syracuseStep 4630319 = 6945479) B6945479
theorem B3086879 : Blo 2057435 3086879 := bstep (se 1 (by rfl) ⟨2315159, by rfl⟩ : syracuseStep 3086879 = 4630319) B4630319
theorem B2057919 : Blo 2057435 2057919 := bstep (se 1 (by rfl) ⟨1543439, by rfl⟩ : syracuseStep 2057919 = 3086879) B3086879
theorem B3086885 : Blo 2057435 3086885 := bbase (se 4 (by rfl) ⟨289395, by rfl⟩ : syracuseStep 3086885 = 578791) (by norm_num)
theorem B2057923 : Blo 2057435 2057923 := bstep (se 1 (by rfl) ⟨1543442, by rfl⟩ : syracuseStep 2057923 = 3086885) B3086885
theorem B2604565 : Blo 2057435 2604565 := bbase (se 6 (by rfl) ⟨61044, by rfl⟩ : syracuseStep 2604565 = 122089) (by norm_num)
theorem B3472753 : Blo 2057435 3472753 := bstep (se 2 (by rfl) ⟨1302282, by rfl⟩ : syracuseStep 3472753 = 2604565) B2604565
theorem B4630337 : Blo 2057435 4630337 := bstep (se 2 (by rfl) ⟨1736376, by rfl⟩ : syracuseStep 4630337 = 3472753) B3472753
theorem B3086891 : Blo 2057435 3086891 := bstep (se 1 (by rfl) ⟨2315168, by rfl⟩ : syracuseStep 3086891 = 4630337) B4630337
theorem B2057927 : Blo 2057435 2057927 := bstep (se 1 (by rfl) ⟨1543445, by rfl⟩ : syracuseStep 2057927 = 3086891) B3086891
theorem B2315173 : Blo 2057435 2315173 := bbase (se 4 (by rfl) ⟨217047, by rfl⟩ : syracuseStep 2315173 = 434095) (by norm_num)
theorem B3086897 : Blo 2057435 3086897 := bstep (se 2 (by rfl) ⟨1157586, by rfl⟩ : syracuseStep 3086897 = 2315173) B2315173
theorem B2057931 : Blo 2057435 2057931 := bstep (se 1 (by rfl) ⟨1543448, by rfl⟩ : syracuseStep 2057931 = 3086897) B3086897
theorem B13732757 : Blo 2057435 13732757 := bbase (se 6 (by rfl) ⟨321861, by rfl⟩ : syracuseStep 13732757 = 643723) (by norm_num)
theorem B9155171 : Blo 2057435 9155171 := bstep (se 1 (by rfl) ⟨6866378, by rfl⟩ : syracuseStep 9155171 = 13732757) B13732757
theorem B24413789 : Blo 2057435 24413789 := bstep (se 3 (by rfl) ⟨4577585, by rfl⟩ : syracuseStep 24413789 = 9155171) B9155171
theorem B65103437 : Blo 2057435 65103437 := bstep (se 3 (by rfl) ⟨12206894, by rfl⟩ : syracuseStep 65103437 = 24413789) B24413789
theorem B43402291 : Blo 2057435 43402291 := bstep (se 1 (by rfl) ⟨32551718, by rfl⟩ : syracuseStep 43402291 = 65103437) B65103437
theorem B231478885 : Blo 2057435 231478885 := bstep (se 4 (by rfl) ⟨21701145, by rfl⟩ : syracuseStep 231478885 = 43402291) B43402291
theorem B308638513 : Blo 2057435 308638513 := bstep (se 2 (by rfl) ⟨115739442, by rfl⟩ : syracuseStep 308638513 = 231478885) B231478885
theorem B411518017 : Blo 2057435 411518017 := bstep (se 2 (by rfl) ⟨154319256, by rfl⟩ : syracuseStep 411518017 = 308638513) B308638513
theorem B548690689 : Blo 2057435 548690689 := bstep (se 2 (by rfl) ⟨205759008, by rfl⟩ : syracuseStep 548690689 = 411518017) B411518017
theorem B731587585 : Blo 2057435 731587585 := bstep (se 2 (by rfl) ⟨274345344, by rfl⟩ : syracuseStep 731587585 = 548690689) B548690689
theorem B975450113 : Blo 2057435 975450113 := bstep (se 2 (by rfl) ⟨365793792, by rfl⟩ : syracuseStep 975450113 = 731587585) B731587585
theorem B650300075 : Blo 2057435 650300075 := bstep (se 1 (by rfl) ⟨487725056, by rfl⟩ : syracuseStep 650300075 = 975450113) B975450113
theorem B433533383 : Blo 2057435 433533383 := bstep (se 1 (by rfl) ⟨325150037, by rfl⟩ : syracuseStep 433533383 = 650300075) B650300075
theorem B289022255 : Blo 2057435 289022255 := bstep (se 1 (by rfl) ⟨216766691, by rfl⟩ : syracuseStep 289022255 = 433533383) B433533383
theorem B192681503 : Blo 2057435 192681503 := bstep (se 1 (by rfl) ⟨144511127, by rfl⟩ : syracuseStep 192681503 = 289022255) B289022255
theorem B128454335 : Blo 2057435 128454335 := bstep (se 1 (by rfl) ⟨96340751, by rfl⟩ : syracuseStep 128454335 = 192681503) B192681503
theorem B85636223 : Blo 2057435 85636223 := bstep (se 1 (by rfl) ⟨64227167, by rfl⟩ : syracuseStep 85636223 = 128454335) B128454335
theorem B57090815 : Blo 2057435 57090815 := bstep (se 1 (by rfl) ⟨42818111, by rfl⟩ : syracuseStep 57090815 = 85636223) B85636223
theorem B38060543 : Blo 2057435 38060543 := bstep (se 1 (by rfl) ⟨28545407, by rfl⟩ : syracuseStep 38060543 = 57090815) B57090815
theorem B25373695 : Blo 2057435 25373695 := bstep (se 1 (by rfl) ⟨19030271, by rfl⟩ : syracuseStep 25373695 = 38060543) B38060543
theorem B33831593 : Blo 2057435 33831593 := bstep (se 2 (by rfl) ⟨12686847, by rfl⟩ : syracuseStep 33831593 = 25373695) B25373695
theorem B22554395 : Blo 2057435 22554395 := bstep (se 1 (by rfl) ⟨16915796, by rfl⟩ : syracuseStep 22554395 = 33831593) B33831593
theorem B15036263 : Blo 2057435 15036263 := bstep (se 1 (by rfl) ⟨11277197, by rfl⟩ : syracuseStep 15036263 = 22554395) B22554395
theorem B10024175 : Blo 2057435 10024175 := bstep (se 1 (by rfl) ⟨7518131, by rfl⟩ : syracuseStep 10024175 = 15036263) B15036263
theorem B26731133 : Blo 2057435 26731133 := bstep (se 3 (by rfl) ⟨5012087, by rfl⟩ : syracuseStep 26731133 = 10024175) B10024175
theorem B17820755 : Blo 2057435 17820755 := bstep (se 1 (by rfl) ⟨13365566, by rfl⟩ : syracuseStep 17820755 = 26731133) B26731133
theorem B11880503 : Blo 2057435 11880503 := bstep (se 1 (by rfl) ⟨8910377, by rfl⟩ : syracuseStep 11880503 = 17820755) B17820755
theorem B7920335 : Blo 2057435 7920335 := bstep (se 1 (by rfl) ⟨5940251, by rfl⟩ : syracuseStep 7920335 = 11880503) B11880503
theorem B5280223 : Blo 2057435 5280223 := bstep (se 1 (by rfl) ⟨3960167, by rfl⟩ : syracuseStep 5280223 = 7920335) B7920335
theorem B7040297 : Blo 2057435 7040297 := bstep (se 2 (by rfl) ⟨2640111, by rfl⟩ : syracuseStep 7040297 = 5280223) B5280223
theorem B18774125 : Blo 2057435 18774125 := bstep (se 3 (by rfl) ⟨3520148, by rfl⟩ : syracuseStep 18774125 = 7040297) B7040297
theorem B12516083 : Blo 2057435 12516083 := bstep (se 1 (by rfl) ⟨9387062, by rfl⟩ : syracuseStep 12516083 = 18774125) B18774125
theorem B8344055 : Blo 2057435 8344055 := bstep (se 1 (by rfl) ⟨6258041, by rfl⟩ : syracuseStep 8344055 = 12516083) B12516083
theorem B5562703 : Blo 2057435 5562703 := bstep (se 1 (by rfl) ⟨4172027, by rfl⟩ : syracuseStep 5562703 = 8344055) B8344055
theorem B7416937 : Blo 2057435 7416937 := bstep (se 2 (by rfl) ⟨2781351, by rfl⟩ : syracuseStep 7416937 = 5562703) B5562703
theorem B9889249 : Blo 2057435 9889249 := bstep (se 2 (by rfl) ⟨3708468, by rfl⟩ : syracuseStep 9889249 = 7416937) B7416937
theorem B13185665 : Blo 2057435 13185665 := bstep (se 2 (by rfl) ⟨4944624, by rfl⟩ : syracuseStep 13185665 = 9889249) B9889249
theorem B8790443 : Blo 2057435 8790443 := bstep (se 1 (by rfl) ⟨6592832, by rfl⟩ : syracuseStep 8790443 = 13185665) B13185665
theorem B5860295 : Blo 2057435 5860295 := bstep (se 1 (by rfl) ⟨4395221, by rfl⟩ : syracuseStep 5860295 = 8790443) B8790443
theorem B3906863 : Blo 2057435 3906863 := bstep (se 1 (by rfl) ⟨2930147, by rfl⟩ : syracuseStep 3906863 = 5860295) B5860295
theorem B2604575 : Blo 2057435 2604575 := bstep (se 1 (by rfl) ⟨1953431, by rfl⟩ : syracuseStep 2604575 = 3906863) B3906863
theorem B6945533 : Blo 2057435 6945533 := bstep (se 3 (by rfl) ⟨1302287, by rfl⟩ : syracuseStep 6945533 = 2604575) B2604575
theorem B4630355 : Blo 2057435 4630355 := bstep (se 1 (by rfl) ⟨3472766, by rfl⟩ : syracuseStep 4630355 = 6945533) B6945533
theorem B3086903 : Blo 2057435 3086903 := bstep (se 1 (by rfl) ⟨2315177, by rfl⟩ : syracuseStep 3086903 = 4630355) B4630355
theorem B2057935 : Blo 2057435 2057935 := bstep (se 1 (by rfl) ⟨1543451, by rfl⟩ : syracuseStep 2057935 = 3086903) B3086903
theorem B3086909 : Blo 2057435 3086909 := bbase (se 3 (by rfl) ⟨578795, by rfl⟩ : syracuseStep 3086909 = 1157591) (by norm_num)
theorem B2057939 : Blo 2057435 2057939 := bstep (se 1 (by rfl) ⟨1543454, by rfl⟩ : syracuseStep 2057939 = 3086909) B3086909
theorem B4630373 : Blo 2057435 4630373 := bbase (se 4 (by rfl) ⟨434097, by rfl⟩ : syracuseStep 4630373 = 868195) (by norm_num)
theorem B3086915 : Blo 2057435 3086915 := bstep (se 1 (by rfl) ⟨2315186, by rfl⟩ : syracuseStep 3086915 = 4630373) B4630373
theorem B2057943 : Blo 2057435 2057943 := bstep (se 1 (by rfl) ⟨1543457, by rfl⟩ : syracuseStep 2057943 = 3086915) B3086915
theorem B5209181 : Blo 2057435 5209181 := bbase (se 3 (by rfl) ⟨976721, by rfl⟩ : syracuseStep 5209181 = 1953443) (by norm_num)
theorem B3472787 : Blo 2057435 3472787 := bstep (se 1 (by rfl) ⟨2604590, by rfl⟩ : syracuseStep 3472787 = 5209181) B5209181
theorem B2315191 : Blo 2057435 2315191 := bstep (se 1 (by rfl) ⟨1736393, by rfl⟩ : syracuseStep 2315191 = 3472787) B3472787
theorem B3086921 : Blo 2057435 3086921 := bstep (se 2 (by rfl) ⟨1157595, by rfl⟩ : syracuseStep 3086921 = 2315191) B2315191
theorem B2057947 : Blo 2057435 2057947 := bstep (se 1 (by rfl) ⟨1543460, by rfl⟩ : syracuseStep 2057947 = 3086921) B3086921
theorem B3906893 : Blo 2057435 3906893 := bbase (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) (by norm_num)
theorem B10418381 : Blo 2057435 10418381 := bstep (se 3 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 10418381 = 3906893) B3906893
theorem B6945587 : Blo 2057435 6945587 := bstep (se 1 (by rfl) ⟨5209190, by rfl⟩ : syracuseStep 6945587 = 10418381) B10418381
theorem B4630391 : Blo 2057435 4630391 := bstep (se 1 (by rfl) ⟨3472793, by rfl⟩ : syracuseStep 4630391 = 6945587) B6945587
theorem B3086927 : Blo 2057435 3086927 := bstep (se 1 (by rfl) ⟨2315195, by rfl⟩ : syracuseStep 3086927 = 4630391) B4630391
theorem B2057951 : Blo 2057435 2057951 := bstep (se 1 (by rfl) ⟨1543463, by rfl⟩ : syracuseStep 2057951 = 3086927) B3086927
theorem B3086933 : Blo 2057435 3086933 := bbase (se 8 (by rfl) ⟨18087, by rfl⟩ : syracuseStep 3086933 = 36175) (by norm_num)
theorem B2057955 : Blo 2057435 2057955 := bstep (se 1 (by rfl) ⟨1543466, by rfl⟩ : syracuseStep 2057955 = 3086933) B3086933
theorem B2472341 : Blo 2057435 2472341 := bbase (se 6 (by rfl) ⟨57945, by rfl⟩ : syracuseStep 2472341 = 115891) (by norm_num)
theorem B6592909 : Blo 2057435 6592909 := bstep (se 3 (by rfl) ⟨1236170, by rfl⟩ : syracuseStep 6592909 = 2472341) B2472341
theorem B8790545 : Blo 2057435 8790545 := bstep (se 2 (by rfl) ⟨3296454, by rfl⟩ : syracuseStep 8790545 = 6592909) B6592909
theorem B5860363 : Blo 2057435 5860363 := bstep (se 1 (by rfl) ⟨4395272, by rfl⟩ : syracuseStep 5860363 = 8790545) B8790545
theorem B7813817 : Blo 2057435 7813817 := bstep (se 2 (by rfl) ⟨2930181, by rfl⟩ : syracuseStep 7813817 = 5860363) B5860363
theorem B5209211 : Blo 2057435 5209211 := bstep (se 1 (by rfl) ⟨3906908, by rfl⟩ : syracuseStep 5209211 = 7813817) B7813817
theorem B3472807 : Blo 2057435 3472807 := bstep (se 1 (by rfl) ⟨2604605, by rfl⟩ : syracuseStep 3472807 = 5209211) B5209211
theorem B4630409 : Blo 2057435 4630409 := bstep (se 2 (by rfl) ⟨1736403, by rfl⟩ : syracuseStep 4630409 = 3472807) B3472807
theorem B3086939 : Blo 2057435 3086939 := bstep (se 1 (by rfl) ⟨2315204, by rfl⟩ : syracuseStep 3086939 = 4630409) B4630409
theorem B2057959 : Blo 2057435 2057959 := bstep (se 1 (by rfl) ⟨1543469, by rfl⟩ : syracuseStep 2057959 = 3086939) B3086939
theorem B2315209 : Blo 2057435 2315209 := bbase (se 2 (by rfl) ⟨868203, by rfl⟩ : syracuseStep 2315209 = 1736407) (by norm_num)
theorem B3086945 : Blo 2057435 3086945 := bstep (se 2 (by rfl) ⟨1157604, by rfl⟩ : syracuseStep 3086945 = 2315209) B2315209
theorem B2057963 : Blo 2057435 2057963 := bstep (se 1 (by rfl) ⟨1543472, by rfl⟩ : syracuseStep 2057963 = 3086945) B3086945
theorem B4944701 : Blo 2057435 4944701 := bbase (se 3 (by rfl) ⟨927131, by rfl⟩ : syracuseStep 4944701 = 1854263) (by norm_num)
theorem B3296467 : Blo 2057435 3296467 := bstep (se 1 (by rfl) ⟨2472350, by rfl⟩ : syracuseStep 3296467 = 4944701) B4944701
theorem B17581157 : Blo 2057435 17581157 := bstep (se 4 (by rfl) ⟨1648233, by rfl⟩ : syracuseStep 17581157 = 3296467) B3296467
theorem B11720771 : Blo 2057435 11720771 := bstep (se 1 (by rfl) ⟨8790578, by rfl⟩ : syracuseStep 11720771 = 17581157) B17581157
theorem B7813847 : Blo 2057435 7813847 := bstep (se 1 (by rfl) ⟨5860385, by rfl⟩ : syracuseStep 7813847 = 11720771) B11720771
theorem B5209231 : Blo 2057435 5209231 := bstep (se 1 (by rfl) ⟨3906923, by rfl⟩ : syracuseStep 5209231 = 7813847) B7813847
theorem B6945641 : Blo 2057435 6945641 := bstep (se 2 (by rfl) ⟨2604615, by rfl⟩ : syracuseStep 6945641 = 5209231) B5209231
theorem B4630427 : Blo 2057435 4630427 := bstep (se 1 (by rfl) ⟨3472820, by rfl⟩ : syracuseStep 4630427 = 6945641) B6945641
theorem B3086951 : Blo 2057435 3086951 := bstep (se 1 (by rfl) ⟨2315213, by rfl⟩ : syracuseStep 3086951 = 4630427) B4630427
theorem B2057967 : Blo 2057435 2057967 := bstep (se 1 (by rfl) ⟨1543475, by rfl⟩ : syracuseStep 2057967 = 3086951) B3086951
theorem B3086957 : Blo 2057435 3086957 := bbase (se 3 (by rfl) ⟨578804, by rfl⟩ : syracuseStep 3086957 = 1157609) (by norm_num)
theorem B2057971 : Blo 2057435 2057971 := bstep (se 1 (by rfl) ⟨1543478, by rfl⟩ : syracuseStep 2057971 = 3086957) B3086957
theorem B4630445 : Blo 2057435 4630445 := bbase (se 3 (by rfl) ⟨868208, by rfl⟩ : syracuseStep 4630445 = 1736417) (by norm_num)
theorem B3086963 : Blo 2057435 3086963 := bstep (se 1 (by rfl) ⟨2315222, by rfl⟩ : syracuseStep 3086963 = 4630445) B4630445
theorem B2057975 : Blo 2057435 2057975 := bstep (se 1 (by rfl) ⟨1543481, by rfl⟩ : syracuseStep 2057975 = 3086963) B3086963
theorem B5860421 : Blo 2057435 5860421 := bbase (se 4 (by rfl) ⟨549414, by rfl⟩ : syracuseStep 5860421 = 1098829) (by norm_num)
theorem B3906947 : Blo 2057435 3906947 := bstep (se 1 (by rfl) ⟨2930210, by rfl⟩ : syracuseStep 3906947 = 5860421) B5860421
theorem B2604631 : Blo 2057435 2604631 := bstep (se 1 (by rfl) ⟨1953473, by rfl⟩ : syracuseStep 2604631 = 3906947) B3906947
theorem B3472841 : Blo 2057435 3472841 := bstep (se 2 (by rfl) ⟨1302315, by rfl⟩ : syracuseStep 3472841 = 2604631) B2604631
theorem B2315227 : Blo 2057435 2315227 := bstep (se 1 (by rfl) ⟨1736420, by rfl⟩ : syracuseStep 2315227 = 3472841) B3472841
theorem B3086969 : Blo 2057435 3086969 := bstep (se 2 (by rfl) ⟨1157613, by rfl⟩ : syracuseStep 3086969 = 2315227) B2315227
theorem B2057979 : Blo 2057435 2057979 := bstep (se 1 (by rfl) ⟨1543484, by rfl⟩ : syracuseStep 2057979 = 3086969) B3086969
theorem B39557909 : Blo 2057435 39557909 := bbase (se 6 (by rfl) ⟨927138, by rfl⟩ : syracuseStep 39557909 = 1854277) (by norm_num)
theorem B26371939 : Blo 2057435 26371939 := bstep (se 1 (by rfl) ⟨19778954, by rfl⟩ : syracuseStep 26371939 = 39557909) B39557909
theorem B35162585 : Blo 2057435 35162585 := bstep (se 2 (by rfl) ⟨13185969, by rfl⟩ : syracuseStep 35162585 = 26371939) B26371939
theorem B23441723 : Blo 2057435 23441723 := bstep (se 1 (by rfl) ⟨17581292, by rfl⟩ : syracuseStep 23441723 = 35162585) B35162585
theorem B15627815 : Blo 2057435 15627815 := bstep (se 1 (by rfl) ⟨11720861, by rfl⟩ : syracuseStep 15627815 = 23441723) B23441723
theorem B10418543 : Blo 2057435 10418543 := bstep (se 1 (by rfl) ⟨7813907, by rfl⟩ : syracuseStep 10418543 = 15627815) B15627815
theorem B6945695 : Blo 2057435 6945695 := bstep (se 1 (by rfl) ⟨5209271, by rfl⟩ : syracuseStep 6945695 = 10418543) B10418543
theorem B4630463 : Blo 2057435 4630463 := bstep (se 1 (by rfl) ⟨3472847, by rfl⟩ : syracuseStep 4630463 = 6945695) B6945695
theorem B3086975 : Blo 2057435 3086975 := bstep (se 1 (by rfl) ⟨2315231, by rfl⟩ : syracuseStep 3086975 = 4630463) B4630463
theorem B2057983 : Blo 2057435 2057983 := bstep (se 1 (by rfl) ⟨1543487, by rfl⟩ : syracuseStep 2057983 = 3086975) B3086975
theorem B3086981 : Blo 2057435 3086981 := bbase (se 4 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 3086981 = 578809) (by norm_num)
theorem B2057987 : Blo 2057435 2057987 := bstep (se 1 (by rfl) ⟨1543490, by rfl⟩ : syracuseStep 2057987 = 3086981) B3086981
theorem B3472861 : Blo 2057435 3472861 := bbase (se 3 (by rfl) ⟨651161, by rfl⟩ : syracuseStep 3472861 = 1302323) (by norm_num)
theorem B4630481 : Blo 2057435 4630481 := bstep (se 2 (by rfl) ⟨1736430, by rfl⟩ : syracuseStep 4630481 = 3472861) B3472861
theorem B3086987 : Blo 2057435 3086987 := bstep (se 1 (by rfl) ⟨2315240, by rfl⟩ : syracuseStep 3086987 = 4630481) B4630481
theorem B2057991 : Blo 2057435 2057991 := bstep (se 1 (by rfl) ⟨1543493, by rfl⟩ : syracuseStep 2057991 = 3086987) B3086987
theorem B2315245 : Blo 2057435 2315245 := bbase (se 3 (by rfl) ⟨434108, by rfl⟩ : syracuseStep 2315245 = 868217) (by norm_num)
theorem B3086993 : Blo 2057435 3086993 := bstep (se 2 (by rfl) ⟨1157622, by rfl⟩ : syracuseStep 3086993 = 2315245) B2315245
theorem B2057995 : Blo 2057435 2057995 := bstep (se 1 (by rfl) ⟨1543496, by rfl⟩ : syracuseStep 2057995 = 3086993) B3086993
theorem B6945749 : Blo 2057435 6945749 := bbase (se 7 (by rfl) ⟨81395, by rfl⟩ : syracuseStep 6945749 = 162791) (by norm_num)
theorem B4630499 : Blo 2057435 4630499 := bstep (se 1 (by rfl) ⟨3472874, by rfl⟩ : syracuseStep 4630499 = 6945749) B6945749
theorem B3086999 : Blo 2057435 3086999 := bstep (se 1 (by rfl) ⟨2315249, by rfl⟩ : syracuseStep 3086999 = 4630499) B4630499
theorem B2057999 : Blo 2057435 2057999 := bstep (se 1 (by rfl) ⟨1543499, by rfl⟩ : syracuseStep 2057999 = 3086999) B3086999
theorem B3087005 : Blo 2057435 3087005 := bbase (se 3 (by rfl) ⟨578813, by rfl⟩ : syracuseStep 3087005 = 1157627) (by norm_num)
theorem B2058003 : Blo 2057435 2058003 := bstep (se 1 (by rfl) ⟨1543502, by rfl⟩ : syracuseStep 2058003 = 3087005) B3087005
theorem B4630517 : Blo 2057435 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B3087011 : Blo 2057435 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B2058007 : Blo 2057435 2058007 := bstep (se 1 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 2058007 = 3087011) B3087011
theorem B5638805 : Blo 2057435 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B3759203 : Blo 2057435 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B10024541 : Blo 2057435 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B106928437 : Blo 2057435 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B142571249 : Blo 2057435 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B95047499 : Blo 2057435 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B63364999 : Blo 2057435 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B84486665 : Blo 2057435 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B56324443 : Blo 2057435 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B75099257 : Blo 2057435 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B50066171 : Blo 2057435 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B33377447 : Blo 2057435 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B89006525 : Blo 2057435 89006525 := bstep (se 3 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 89006525 = 33377447) B33377447
theorem B59337683 : Blo 2057435 59337683 := bstep (se 1 (by rfl) ⟨44503262, by rfl⟩ : syracuseStep 59337683 = 89006525) B89006525
theorem B39558455 : Blo 2057435 39558455 := bstep (se 1 (by rfl) ⟨29668841, by rfl⟩ : syracuseStep 39558455 = 59337683) B59337683
theorem B26372303 : Blo 2057435 26372303 := bstep (se 1 (by rfl) ⟨19779227, by rfl⟩ : syracuseStep 26372303 = 39558455) B39558455
theorem B17581535 : Blo 2057435 17581535 := bstep (se 1 (by rfl) ⟨13186151, by rfl⟩ : syracuseStep 17581535 = 26372303) B26372303
theorem B11721023 : Blo 2057435 11721023 := bstep (se 1 (by rfl) ⟨8790767, by rfl⟩ : syracuseStep 11721023 = 17581535) B17581535
theorem B7814015 : Blo 2057435 7814015 := bstep (se 1 (by rfl) ⟨5860511, by rfl⟩ : syracuseStep 7814015 = 11721023) B11721023
theorem B5209343 : Blo 2057435 5209343 := bstep (se 1 (by rfl) ⟨3907007, by rfl⟩ : syracuseStep 5209343 = 7814015) B7814015
theorem B3472895 : Blo 2057435 3472895 := bstep (se 1 (by rfl) ⟨2604671, by rfl⟩ : syracuseStep 3472895 = 5209343) B5209343
theorem B2315263 : Blo 2057435 2315263 := bstep (se 1 (by rfl) ⟨1736447, by rfl⟩ : syracuseStep 2315263 = 3472895) B3472895
theorem B3087017 : Blo 2057435 3087017 := bstep (se 2 (by rfl) ⟨1157631, by rfl⟩ : syracuseStep 3087017 = 2315263) B2315263
theorem B2058011 : Blo 2057435 2058011 := bstep (se 1 (by rfl) ⟨1543508, by rfl⟩ : syracuseStep 2058011 = 3087017) B3087017
theorem B2930261 : Blo 2057435 2930261 := bbase (se 8 (by rfl) ⟨17169, by rfl⟩ : syracuseStep 2930261 = 34339) (by norm_num)
theorem B7814029 : Blo 2057435 7814029 := bstep (se 3 (by rfl) ⟨1465130, by rfl⟩ : syracuseStep 7814029 = 2930261) B2930261
theorem B10418705 : Blo 2057435 10418705 := bstep (se 2 (by rfl) ⟨3907014, by rfl⟩ : syracuseStep 10418705 = 7814029) B7814029
theorem B6945803 : Blo 2057435 6945803 := bstep (se 1 (by rfl) ⟨5209352, by rfl⟩ : syracuseStep 6945803 = 10418705) B10418705
theorem B4630535 : Blo 2057435 4630535 := bstep (se 1 (by rfl) ⟨3472901, by rfl⟩ : syracuseStep 4630535 = 6945803) B6945803
theorem B3087023 : Blo 2057435 3087023 := bstep (se 1 (by rfl) ⟨2315267, by rfl⟩ : syracuseStep 3087023 = 4630535) B4630535
theorem B2058015 : Blo 2057435 2058015 := bstep (se 1 (by rfl) ⟨1543511, by rfl⟩ : syracuseStep 2058015 = 3087023) B3087023
theorem B3087029 : Blo 2057435 3087029 := bbase (se 5 (by rfl) ⟨144704, by rfl⟩ : syracuseStep 3087029 = 289409) (by norm_num)
theorem B2058019 : Blo 2057435 2058019 := bstep (se 1 (by rfl) ⟨1543514, by rfl⟩ : syracuseStep 2058019 = 3087029) B3087029
theorem B5209373 : Blo 2057435 5209373 := bbase (se 3 (by rfl) ⟨976757, by rfl⟩ : syracuseStep 5209373 = 1953515) (by norm_num)
theorem B3472915 : Blo 2057435 3472915 := bstep (se 1 (by rfl) ⟨2604686, by rfl⟩ : syracuseStep 3472915 = 5209373) B5209373
theorem B4630553 : Blo 2057435 4630553 := bstep (se 2 (by rfl) ⟨1736457, by rfl⟩ : syracuseStep 4630553 = 3472915) B3472915
theorem B3087035 : Blo 2057435 3087035 := bstep (se 1 (by rfl) ⟨2315276, by rfl⟩ : syracuseStep 3087035 = 4630553) B4630553
theorem B2058023 : Blo 2057435 2058023 := bstep (se 1 (by rfl) ⟨1543517, by rfl⟩ : syracuseStep 2058023 = 3087035) B3087035
theorem B2315281 : Blo 2057435 2315281 := bbase (se 2 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 2315281 = 1736461) (by norm_num)
theorem B3087041 : Blo 2057435 3087041 := bstep (se 2 (by rfl) ⟨1157640, by rfl⟩ : syracuseStep 3087041 = 2315281) B2315281
theorem B2058027 : Blo 2057435 2058027 := bstep (se 1 (by rfl) ⟨1543520, by rfl⟩ : syracuseStep 2058027 = 3087041) B3087041
theorem B3907045 : Blo 2057435 3907045 := bbase (se 4 (by rfl) ⟨366285, by rfl⟩ : syracuseStep 3907045 = 732571) (by norm_num)
theorem B5209393 : Blo 2057435 5209393 := bstep (se 2 (by rfl) ⟨1953522, by rfl⟩ : syracuseStep 5209393 = 3907045) B3907045
theorem B6945857 : Blo 2057435 6945857 := bstep (se 2 (by rfl) ⟨2604696, by rfl⟩ : syracuseStep 6945857 = 5209393) B5209393
theorem B4630571 : Blo 2057435 4630571 := bstep (se 1 (by rfl) ⟨3472928, by rfl⟩ : syracuseStep 4630571 = 6945857) B6945857
theorem B3087047 : Blo 2057435 3087047 := bstep (se 1 (by rfl) ⟨2315285, by rfl⟩ : syracuseStep 3087047 = 4630571) B4630571
theorem B2058031 : Blo 2057435 2058031 := bstep (se 1 (by rfl) ⟨1543523, by rfl⟩ : syracuseStep 2058031 = 3087047) B3087047
theorem B3087053 : Blo 2057435 3087053 := bbase (se 3 (by rfl) ⟨578822, by rfl⟩ : syracuseStep 3087053 = 1157645) (by norm_num)
theorem B2058035 : Blo 2057435 2058035 := bstep (se 1 (by rfl) ⟨1543526, by rfl⟩ : syracuseStep 2058035 = 3087053) B3087053
theorem B4630589 : Blo 2057435 4630589 := bbase (se 3 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 4630589 = 1736471) (by norm_num)
theorem B3087059 : Blo 2057435 3087059 := bstep (se 1 (by rfl) ⟨2315294, by rfl⟩ : syracuseStep 3087059 = 4630589) B4630589
theorem B2058039 : Blo 2057435 2058039 := bstep (se 1 (by rfl) ⟨1543529, by rfl⟩ : syracuseStep 2058039 = 3087059) B3087059
theorem B3472949 : Blo 2057435 3472949 := bbase (se 5 (by rfl) ⟨162794, by rfl⟩ : syracuseStep 3472949 = 325589) (by norm_num)
theorem B2315299 : Blo 2057435 2315299 := bstep (se 1 (by rfl) ⟨1736474, by rfl⟩ : syracuseStep 2315299 = 3472949) B3472949
theorem B3087065 : Blo 2057435 3087065 := bstep (se 2 (by rfl) ⟨1157649, by rfl⟩ : syracuseStep 3087065 = 2315299) B2315299
theorem B2058043 : Blo 2057435 2058043 := bstep (se 1 (by rfl) ⟨1543532, by rfl⟩ : syracuseStep 2058043 = 3087065) B3087065
theorem B5860613 : Blo 2057435 5860613 := bbase (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) (by norm_num)
theorem B15628301 : Blo 2057435 15628301 := bstep (se 3 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 15628301 = 5860613) B5860613
theorem B10418867 : Blo 2057435 10418867 := bstep (se 1 (by rfl) ⟨7814150, by rfl⟩ : syracuseStep 10418867 = 15628301) B15628301
theorem B6945911 : Blo 2057435 6945911 := bstep (se 1 (by rfl) ⟨5209433, by rfl⟩ : syracuseStep 6945911 = 10418867) B10418867
theorem B4630607 : Blo 2057435 4630607 := bstep (se 1 (by rfl) ⟨3472955, by rfl⟩ : syracuseStep 4630607 = 6945911) B6945911
theorem B3087071 : Blo 2057435 3087071 := bstep (se 1 (by rfl) ⟨2315303, by rfl⟩ : syracuseStep 3087071 = 4630607) B4630607
theorem B2058047 : Blo 2057435 2058047 := bstep (se 1 (by rfl) ⟨1543535, by rfl⟩ : syracuseStep 2058047 = 3087071) B3087071
theorem B3087077 : Blo 2057435 3087077 := bbase (se 4 (by rfl) ⟨289413, by rfl⟩ : syracuseStep 3087077 = 578827) (by norm_num)
theorem B2058051 : Blo 2057435 2058051 := bstep (se 1 (by rfl) ⟨1543538, by rfl⟩ : syracuseStep 2058051 = 3087077) B3087077
theorem B2472457 : Blo 2057435 2472457 := bbase (se 2 (by rfl) ⟨927171, by rfl⟩ : syracuseStep 2472457 = 1854343) (by norm_num)
theorem B3296609 : Blo 2057435 3296609 := bstep (se 2 (by rfl) ⟨1236228, by rfl⟩ : syracuseStep 3296609 = 2472457) B2472457
theorem B2197739 : Blo 2057435 2197739 := bstep (se 1 (by rfl) ⟨1648304, by rfl⟩ : syracuseStep 2197739 = 3296609) B3296609
theorem B5860637 : Blo 2057435 5860637 := bstep (se 3 (by rfl) ⟨1098869, by rfl⟩ : syracuseStep 5860637 = 2197739) B2197739
theorem B3907091 : Blo 2057435 3907091 := bstep (se 1 (by rfl) ⟨2930318, by rfl⟩ : syracuseStep 3907091 = 5860637) B5860637
theorem B2604727 : Blo 2057435 2604727 := bstep (se 1 (by rfl) ⟨1953545, by rfl⟩ : syracuseStep 2604727 = 3907091) B3907091
theorem B3472969 : Blo 2057435 3472969 := bstep (se 2 (by rfl) ⟨1302363, by rfl⟩ : syracuseStep 3472969 = 2604727) B2604727
theorem B4630625 : Blo 2057435 4630625 := bstep (se 2 (by rfl) ⟨1736484, by rfl⟩ : syracuseStep 4630625 = 3472969) B3472969
theorem B3087083 : Blo 2057435 3087083 := bstep (se 1 (by rfl) ⟨2315312, by rfl⟩ : syracuseStep 3087083 = 4630625) B4630625
theorem B2058055 : Blo 2057435 2058055 := bstep (se 1 (by rfl) ⟨1543541, by rfl⟩ : syracuseStep 2058055 = 3087083) B3087083
theorem B2315317 : Blo 2057435 2315317 := bbase (se 5 (by rfl) ⟨108530, by rfl⟩ : syracuseStep 2315317 = 217061) (by norm_num)
theorem B3087089 : Blo 2057435 3087089 := bstep (se 2 (by rfl) ⟨1157658, by rfl⟩ : syracuseStep 3087089 = 2315317) B2315317
theorem B2058059 : Blo 2057435 2058059 := bstep (se 1 (by rfl) ⟨1543544, by rfl⟩ : syracuseStep 2058059 = 3087089) B3087089
theorem B2604737 : Blo 2057435 2604737 := bbase (se 2 (by rfl) ⟨976776, by rfl⟩ : syracuseStep 2604737 = 1953553) (by norm_num)
theorem B6945965 : Blo 2057435 6945965 := bstep (se 3 (by rfl) ⟨1302368, by rfl⟩ : syracuseStep 6945965 = 2604737) B2604737
theorem B4630643 : Blo 2057435 4630643 := bstep (se 1 (by rfl) ⟨3472982, by rfl⟩ : syracuseStep 4630643 = 6945965) B6945965
theorem B3087095 : Blo 2057435 3087095 := bstep (se 1 (by rfl) ⟨2315321, by rfl⟩ : syracuseStep 3087095 = 4630643) B4630643
theorem B2058063 : Blo 2057435 2058063 := bstep (se 1 (by rfl) ⟨1543547, by rfl⟩ : syracuseStep 2058063 = 3087095) B3087095
theorem B3087101 : Blo 2057435 3087101 := bbase (se 3 (by rfl) ⟨578831, by rfl⟩ : syracuseStep 3087101 = 1157663) (by norm_num)
theorem B2058067 : Blo 2057435 2058067 := bstep (se 1 (by rfl) ⟨1543550, by rfl⟩ : syracuseStep 2058067 = 3087101) B3087101
theorem B4630661 : Blo 2057435 4630661 := bbase (se 4 (by rfl) ⟨434124, by rfl⟩ : syracuseStep 4630661 = 868249) (by norm_num)
theorem B3087107 : Blo 2057435 3087107 := bstep (se 1 (by rfl) ⟨2315330, by rfl⟩ : syracuseStep 3087107 = 4630661) B4630661
theorem B2058071 : Blo 2057435 2058071 := bstep (se 1 (by rfl) ⟨1543553, by rfl⟩ : syracuseStep 2058071 = 3087107) B3087107
theorem B2472481 : Blo 2057435 2472481 := bbase (se 2 (by rfl) ⟨927180, by rfl⟩ : syracuseStep 2472481 = 1854361) (by norm_num)
theorem B3296641 : Blo 2057435 3296641 := bstep (se 2 (by rfl) ⟨1236240, by rfl⟩ : syracuseStep 3296641 = 2472481) B2472481
theorem B4395521 : Blo 2057435 4395521 := bstep (se 2 (by rfl) ⟨1648320, by rfl⟩ : syracuseStep 4395521 = 3296641) B3296641
theorem B2930347 : Blo 2057435 2930347 := bstep (se 1 (by rfl) ⟨2197760, by rfl⟩ : syracuseStep 2930347 = 4395521) B4395521
theorem B3907129 : Blo 2057435 3907129 := bstep (se 2 (by rfl) ⟨1465173, by rfl⟩ : syracuseStep 3907129 = 2930347) B2930347
theorem B5209505 : Blo 2057435 5209505 := bstep (se 2 (by rfl) ⟨1953564, by rfl⟩ : syracuseStep 5209505 = 3907129) B3907129
theorem B3473003 : Blo 2057435 3473003 := bstep (se 1 (by rfl) ⟨2604752, by rfl⟩ : syracuseStep 3473003 = 5209505) B5209505
theorem B2315335 : Blo 2057435 2315335 := bstep (se 1 (by rfl) ⟨1736501, by rfl⟩ : syracuseStep 2315335 = 3473003) B3473003
theorem B3087113 : Blo 2057435 3087113 := bstep (se 2 (by rfl) ⟨1157667, by rfl⟩ : syracuseStep 3087113 = 2315335) B2315335
theorem B2058075 : Blo 2057435 2058075 := bstep (se 1 (by rfl) ⟨1543556, by rfl⟩ : syracuseStep 2058075 = 3087113) B3087113
theorem B10419029 : Blo 2057435 10419029 := bbase (se 9 (by rfl) ⟨30524, by rfl⟩ : syracuseStep 10419029 = 61049) (by norm_num)
theorem B6946019 : Blo 2057435 6946019 := bstep (se 1 (by rfl) ⟨5209514, by rfl⟩ : syracuseStep 6946019 = 10419029) B10419029
theorem B4630679 : Blo 2057435 4630679 := bstep (se 1 (by rfl) ⟨3473009, by rfl⟩ : syracuseStep 4630679 = 6946019) B6946019
theorem B3087119 : Blo 2057435 3087119 := bstep (se 1 (by rfl) ⟨2315339, by rfl⟩ : syracuseStep 3087119 = 4630679) B4630679
theorem B2058079 : Blo 2057435 2058079 := bstep (se 1 (by rfl) ⟨1543559, by rfl⟩ : syracuseStep 2058079 = 3087119) B3087119
theorem B3087125 : Blo 2057435 3087125 := bbase (se 6 (by rfl) ⟨72354, by rfl⟩ : syracuseStep 3087125 = 144709) (by norm_num)
theorem B2058083 : Blo 2057435 2058083 := bstep (se 1 (by rfl) ⟨1543562, by rfl⟩ : syracuseStep 2058083 = 3087125) B3087125
theorem B4757917 : Blo 2057435 4757917 := bbase (se 3 (by rfl) ⟨892109, by rfl⟩ : syracuseStep 4757917 = 1784219) (by norm_num)
theorem B6343889 : Blo 2057435 6343889 := bstep (se 2 (by rfl) ⟨2378958, by rfl⟩ : syracuseStep 6343889 = 4757917) B4757917
theorem B67668149 : Blo 2057435 67668149 := bstep (se 5 (by rfl) ⟨3171944, by rfl⟩ : syracuseStep 67668149 = 6343889) B6343889
theorem B45112099 : Blo 2057435 45112099 := bstep (se 1 (by rfl) ⟨33834074, by rfl⟩ : syracuseStep 45112099 = 67668149) B67668149
theorem B60149465 : Blo 2057435 60149465 := bstep (se 2 (by rfl) ⟨22556049, by rfl⟩ : syracuseStep 60149465 = 45112099) B45112099
theorem B40099643 : Blo 2057435 40099643 := bstep (se 1 (by rfl) ⟨30074732, by rfl⟩ : syracuseStep 40099643 = 60149465) B60149465
theorem B26733095 : Blo 2057435 26733095 := bstep (se 1 (by rfl) ⟨20049821, by rfl⟩ : syracuseStep 26733095 = 40099643) B40099643
theorem B17822063 : Blo 2057435 17822063 := bstep (se 1 (by rfl) ⟨13366547, by rfl⟩ : syracuseStep 17822063 = 26733095) B26733095
theorem B47525501 : Blo 2057435 47525501 := bstep (se 3 (by rfl) ⟨8911031, by rfl⟩ : syracuseStep 47525501 = 17822063) B17822063
theorem B126734669 : Blo 2057435 126734669 := bstep (se 3 (by rfl) ⟨23762750, by rfl⟩ : syracuseStep 126734669 = 47525501) B47525501
theorem B84489779 : Blo 2057435 84489779 := bstep (se 1 (by rfl) ⟨63367334, by rfl⟩ : syracuseStep 84489779 = 126734669) B126734669
theorem B56326519 : Blo 2057435 56326519 := bstep (se 1 (by rfl) ⟨42244889, by rfl⟩ : syracuseStep 56326519 = 84489779) B84489779
theorem B75102025 : Blo 2057435 75102025 := bstep (se 2 (by rfl) ⟨28163259, by rfl⟩ : syracuseStep 75102025 = 56326519) B56326519
theorem B100136033 : Blo 2057435 100136033 := bstep (se 2 (by rfl) ⟨37551012, by rfl⟩ : syracuseStep 100136033 = 75102025) B75102025
theorem B66757355 : Blo 2057435 66757355 := bstep (se 1 (by rfl) ⟨50068016, by rfl⟩ : syracuseStep 66757355 = 100136033) B100136033
theorem B44504903 : Blo 2057435 44504903 := bstep (se 1 (by rfl) ⟨33378677, by rfl⟩ : syracuseStep 44504903 = 66757355) B66757355
theorem B29669935 : Blo 2057435 29669935 := bstep (se 1 (by rfl) ⟨22252451, by rfl⟩ : syracuseStep 29669935 = 44504903) B44504903
theorem B39559913 : Blo 2057435 39559913 := bstep (se 2 (by rfl) ⟨14834967, by rfl⟩ : syracuseStep 39559913 = 29669935) B29669935
theorem B26373275 : Blo 2057435 26373275 := bstep (se 1 (by rfl) ⟨19779956, by rfl⟩ : syracuseStep 26373275 = 39559913) B39559913
theorem B17582183 : Blo 2057435 17582183 := bstep (se 1 (by rfl) ⟨13186637, by rfl⟩ : syracuseStep 17582183 = 26373275) B26373275
theorem B11721455 : Blo 2057435 11721455 := bstep (se 1 (by rfl) ⟨8791091, by rfl⟩ : syracuseStep 11721455 = 17582183) B17582183
theorem B7814303 : Blo 2057435 7814303 := bstep (se 1 (by rfl) ⟨5860727, by rfl⟩ : syracuseStep 7814303 = 11721455) B11721455
theorem B5209535 : Blo 2057435 5209535 := bstep (se 1 (by rfl) ⟨3907151, by rfl⟩ : syracuseStep 5209535 = 7814303) B7814303
theorem B3473023 : Blo 2057435 3473023 := bstep (se 1 (by rfl) ⟨2604767, by rfl⟩ : syracuseStep 3473023 = 5209535) B5209535
theorem B4630697 : Blo 2057435 4630697 := bstep (se 2 (by rfl) ⟨1736511, by rfl⟩ : syracuseStep 4630697 = 3473023) B3473023
theorem B3087131 : Blo 2057435 3087131 := bstep (se 1 (by rfl) ⟨2315348, by rfl⟩ : syracuseStep 3087131 = 4630697) B4630697
theorem B2058087 : Blo 2057435 2058087 := bstep (se 1 (by rfl) ⟨1543565, by rfl⟩ : syracuseStep 2058087 = 3087131) B3087131
theorem B2315353 : Blo 2057435 2315353 := bbase (se 2 (by rfl) ⟨868257, by rfl⟩ : syracuseStep 2315353 = 1736515) (by norm_num)
theorem B3087137 : Blo 2057435 3087137 := bstep (se 2 (by rfl) ⟨1157676, by rfl⟩ : syracuseStep 3087137 = 2315353) B2315353
theorem B2058091 : Blo 2057435 2058091 := bstep (se 1 (by rfl) ⟨1543568, by rfl⟩ : syracuseStep 2058091 = 3087137) B3087137
theorem B3708757 : Blo 2057435 3708757 := bbase (se 9 (by rfl) ⟨10865, by rfl⟩ : syracuseStep 3708757 = 21731) (by norm_num)
theorem B4945009 : Blo 2057435 4945009 := bstep (se 2 (by rfl) ⟨1854378, by rfl⟩ : syracuseStep 4945009 = 3708757) B3708757
theorem B6593345 : Blo 2057435 6593345 := bstep (se 2 (by rfl) ⟨2472504, by rfl⟩ : syracuseStep 6593345 = 4945009) B4945009
theorem B4395563 : Blo 2057435 4395563 := bstep (se 1 (by rfl) ⟨3296672, by rfl⟩ : syracuseStep 4395563 = 6593345) B6593345
theorem B2930375 : Blo 2057435 2930375 := bstep (se 1 (by rfl) ⟨2197781, by rfl⟩ : syracuseStep 2930375 = 4395563) B4395563
theorem B7814333 : Blo 2057435 7814333 := bstep (se 3 (by rfl) ⟨1465187, by rfl⟩ : syracuseStep 7814333 = 2930375) B2930375
theorem B5209555 : Blo 2057435 5209555 := bstep (se 1 (by rfl) ⟨3907166, by rfl⟩ : syracuseStep 5209555 = 7814333) B7814333
theorem B6946073 : Blo 2057435 6946073 := bstep (se 2 (by rfl) ⟨2604777, by rfl⟩ : syracuseStep 6946073 = 5209555) B5209555
theorem B4630715 : Blo 2057435 4630715 := bstep (se 1 (by rfl) ⟨3473036, by rfl⟩ : syracuseStep 4630715 = 6946073) B6946073
theorem B3087143 : Blo 2057435 3087143 := bstep (se 1 (by rfl) ⟨2315357, by rfl⟩ : syracuseStep 3087143 = 4630715) B4630715
theorem B2058095 : Blo 2057435 2058095 := bstep (se 1 (by rfl) ⟨1543571, by rfl⟩ : syracuseStep 2058095 = 3087143) B3087143
theorem B3087149 : Blo 2057435 3087149 := bbase (se 3 (by rfl) ⟨578840, by rfl⟩ : syracuseStep 3087149 = 1157681) (by norm_num)
theorem B2058099 : Blo 2057435 2058099 := bstep (se 1 (by rfl) ⟨1543574, by rfl⟩ : syracuseStep 2058099 = 3087149) B3087149
theorem B4630733 : Blo 2057435 4630733 := bbase (se 3 (by rfl) ⟨868262, by rfl⟩ : syracuseStep 4630733 = 1736525) (by norm_num)
theorem B3087155 : Blo 2057435 3087155 := bstep (se 1 (by rfl) ⟨2315366, by rfl⟩ : syracuseStep 3087155 = 4630733) B4630733
theorem B2058103 : Blo 2057435 2058103 := bstep (se 1 (by rfl) ⟨1543577, by rfl⟩ : syracuseStep 2058103 = 3087155) B3087155
theorem B2604793 : Blo 2057435 2604793 := bbase (se 2 (by rfl) ⟨976797, by rfl⟩ : syracuseStep 2604793 = 1953595) (by norm_num)
theorem B3473057 : Blo 2057435 3473057 := bstep (se 2 (by rfl) ⟨1302396, by rfl⟩ : syracuseStep 3473057 = 2604793) B2604793
theorem B2315371 : Blo 2057435 2315371 := bstep (se 1 (by rfl) ⟨1736528, by rfl⟩ : syracuseStep 2315371 = 3473057) B3473057
theorem B3087161 : Blo 2057435 3087161 := bstep (se 2 (by rfl) ⟨1157685, by rfl⟩ : syracuseStep 3087161 = 2315371) B2315371
theorem B2058107 : Blo 2057435 2058107 := bstep (se 1 (by rfl) ⟨1543580, by rfl⟩ : syracuseStep 2058107 = 3087161) B3087161
theorem B2781589 : Blo 2057435 2781589 := bbase (se 6 (by rfl) ⟨65193, by rfl⟩ : syracuseStep 2781589 = 130387) (by norm_num)
theorem B3708785 : Blo 2057435 3708785 := bstep (se 2 (by rfl) ⟨1390794, by rfl⟩ : syracuseStep 3708785 = 2781589) B2781589
theorem B9890093 : Blo 2057435 9890093 := bstep (se 3 (by rfl) ⟨1854392, by rfl⟩ : syracuseStep 9890093 = 3708785) B3708785
theorem B6593395 : Blo 2057435 6593395 := bstep (se 1 (by rfl) ⟨4945046, by rfl⟩ : syracuseStep 6593395 = 9890093) B9890093
theorem B8791193 : Blo 2057435 8791193 := bstep (se 2 (by rfl) ⟨3296697, by rfl⟩ : syracuseStep 8791193 = 6593395) B6593395
theorem B23443181 : Blo 2057435 23443181 := bstep (se 3 (by rfl) ⟨4395596, by rfl⟩ : syracuseStep 23443181 = 8791193) B8791193
theorem B15628787 : Blo 2057435 15628787 := bstep (se 1 (by rfl) ⟨11721590, by rfl⟩ : syracuseStep 15628787 = 23443181) B23443181
theorem B10419191 : Blo 2057435 10419191 := bstep (se 1 (by rfl) ⟨7814393, by rfl⟩ : syracuseStep 10419191 = 15628787) B15628787
theorem B6946127 : Blo 2057435 6946127 := bstep (se 1 (by rfl) ⟨5209595, by rfl⟩ : syracuseStep 6946127 = 10419191) B10419191
theorem B4630751 : Blo 2057435 4630751 := bstep (se 1 (by rfl) ⟨3473063, by rfl⟩ : syracuseStep 4630751 = 6946127) B6946127
theorem B3087167 : Blo 2057435 3087167 := bstep (se 1 (by rfl) ⟨2315375, by rfl⟩ : syracuseStep 3087167 = 4630751) B4630751
theorem B2058111 : Blo 2057435 2058111 := bstep (se 1 (by rfl) ⟨1543583, by rfl⟩ : syracuseStep 2058111 = 3087167) B3087167
theorem B3087173 : Blo 2057435 3087173 := bbase (se 4 (by rfl) ⟨289422, by rfl⟩ : syracuseStep 3087173 = 578845) (by norm_num)
theorem B2058115 : Blo 2057435 2058115 := bstep (se 1 (by rfl) ⟨1543586, by rfl⟩ : syracuseStep 2058115 = 3087173) B3087173
theorem B3473077 : Blo 2057435 3473077 := bbase (se 5 (by rfl) ⟨162800, by rfl⟩ : syracuseStep 3473077 = 325601) (by norm_num)
theorem B4630769 : Blo 2057435 4630769 := bstep (se 2 (by rfl) ⟨1736538, by rfl⟩ : syracuseStep 4630769 = 3473077) B3473077
theorem B3087179 : Blo 2057435 3087179 := bstep (se 1 (by rfl) ⟨2315384, by rfl⟩ : syracuseStep 3087179 = 4630769) B4630769
theorem B2058119 : Blo 2057435 2058119 := bstep (se 1 (by rfl) ⟨1543589, by rfl⟩ : syracuseStep 2058119 = 3087179) B3087179
theorem B2315389 : Blo 2057435 2315389 := bbase (se 3 (by rfl) ⟨434135, by rfl⟩ : syracuseStep 2315389 = 868271) (by norm_num)
theorem B3087185 : Blo 2057435 3087185 := bstep (se 2 (by rfl) ⟨1157694, by rfl⟩ : syracuseStep 3087185 = 2315389) B2315389
theorem B2058123 : Blo 2057435 2058123 := bstep (se 1 (by rfl) ⟨1543592, by rfl⟩ : syracuseStep 2058123 = 3087185) B3087185
theorem B6946181 : Blo 2057435 6946181 := bbase (se 4 (by rfl) ⟨651204, by rfl⟩ : syracuseStep 6946181 = 1302409) (by norm_num)
theorem B4630787 : Blo 2057435 4630787 := bstep (se 1 (by rfl) ⟨3473090, by rfl⟩ : syracuseStep 4630787 = 6946181) B6946181
theorem B3087191 : Blo 2057435 3087191 := bstep (se 1 (by rfl) ⟨2315393, by rfl⟩ : syracuseStep 3087191 = 4630787) B4630787
theorem B2058127 : Blo 2057435 2058127 := bstep (se 1 (by rfl) ⟨1543595, by rfl⟩ : syracuseStep 2058127 = 3087191) B3087191
theorem B3087197 : Blo 2057435 3087197 := bbase (se 3 (by rfl) ⟨578849, by rfl⟩ : syracuseStep 3087197 = 1157699) (by norm_num)
theorem B2058131 : Blo 2057435 2058131 := bstep (se 1 (by rfl) ⟨1543598, by rfl⟩ : syracuseStep 2058131 = 3087197) B3087197
theorem B4630805 : Blo 2057435 4630805 := bbase (se 6 (by rfl) ⟨108534, by rfl⟩ : syracuseStep 4630805 = 217069) (by norm_num)
theorem B3087203 : Blo 2057435 3087203 := bstep (se 1 (by rfl) ⟨2315402, by rfl⟩ : syracuseStep 3087203 = 4630805) B4630805
theorem B2058135 : Blo 2057435 2058135 := bstep (se 1 (by rfl) ⟨1543601, by rfl⟩ : syracuseStep 2058135 = 3087203) B3087203
theorem B7814501 : Blo 2057435 7814501 := bbase (se 4 (by rfl) ⟨732609, by rfl⟩ : syracuseStep 7814501 = 1465219) (by norm_num)
theorem B5209667 : Blo 2057435 5209667 := bstep (se 1 (by rfl) ⟨3907250, by rfl⟩ : syracuseStep 5209667 = 7814501) B7814501
theorem B3473111 : Blo 2057435 3473111 := bstep (se 1 (by rfl) ⟨2604833, by rfl⟩ : syracuseStep 3473111 = 5209667) B5209667
theorem B2315407 : Blo 2057435 2315407 := bstep (se 1 (by rfl) ⟨1736555, by rfl⟩ : syracuseStep 2315407 = 3473111) B3473111
theorem B3087209 : Blo 2057435 3087209 := bstep (se 2 (by rfl) ⟨1157703, by rfl⟩ : syracuseStep 3087209 = 2315407) B2315407
theorem B2058139 : Blo 2057435 2058139 := bstep (se 1 (by rfl) ⟨1543604, by rfl⟩ : syracuseStep 2058139 = 3087209) B3087209
theorem B3296749 : Blo 2057435 3296749 := bbase (se 3 (by rfl) ⟨618140, by rfl⟩ : syracuseStep 3296749 = 1236281) (by norm_num)
theorem B4395665 : Blo 2057435 4395665 := bstep (se 2 (by rfl) ⟨1648374, by rfl⟩ : syracuseStep 4395665 = 3296749) B3296749
theorem B11721773 : Blo 2057435 11721773 := bstep (se 3 (by rfl) ⟨2197832, by rfl⟩ : syracuseStep 11721773 = 4395665) B4395665
theorem B7814515 : Blo 2057435 7814515 := bstep (se 1 (by rfl) ⟨5860886, by rfl⟩ : syracuseStep 7814515 = 11721773) B11721773
theorem B10419353 : Blo 2057435 10419353 := bstep (se 2 (by rfl) ⟨3907257, by rfl⟩ : syracuseStep 10419353 = 7814515) B7814515
theorem B6946235 : Blo 2057435 6946235 := bstep (se 1 (by rfl) ⟨5209676, by rfl⟩ : syracuseStep 6946235 = 10419353) B10419353
theorem B4630823 : Blo 2057435 4630823 := bstep (se 1 (by rfl) ⟨3473117, by rfl⟩ : syracuseStep 4630823 = 6946235) B6946235
theorem B3087215 : Blo 2057435 3087215 := bstep (se 1 (by rfl) ⟨2315411, by rfl⟩ : syracuseStep 3087215 = 4630823) B4630823
theorem B2058143 : Blo 2057435 2058143 := bstep (se 1 (by rfl) ⟨1543607, by rfl⟩ : syracuseStep 2058143 = 3087215) B3087215
theorem B3087221 : Blo 2057435 3087221 := bbase (se 5 (by rfl) ⟨144713, by rfl⟩ : syracuseStep 3087221 = 289427) (by norm_num)
theorem B2058147 : Blo 2057435 2058147 := bstep (se 1 (by rfl) ⟨1543610, by rfl⟩ : syracuseStep 2058147 = 3087221) B3087221
theorem B6593525 : Blo 2057435 6593525 := bbase (se 5 (by rfl) ⟨309071, by rfl⟩ : syracuseStep 6593525 = 618143) (by norm_num)
theorem B4395683 : Blo 2057435 4395683 := bstep (se 1 (by rfl) ⟨3296762, by rfl⟩ : syracuseStep 4395683 = 6593525) B6593525
theorem B2930455 : Blo 2057435 2930455 := bstep (se 1 (by rfl) ⟨2197841, by rfl⟩ : syracuseStep 2930455 = 4395683) B4395683
theorem B3907273 : Blo 2057435 3907273 := bstep (se 2 (by rfl) ⟨1465227, by rfl⟩ : syracuseStep 3907273 = 2930455) B2930455
theorem B5209697 : Blo 2057435 5209697 := bstep (se 2 (by rfl) ⟨1953636, by rfl⟩ : syracuseStep 5209697 = 3907273) B3907273
theorem B3473131 : Blo 2057435 3473131 := bstep (se 1 (by rfl) ⟨2604848, by rfl⟩ : syracuseStep 3473131 = 5209697) B5209697
theorem B4630841 : Blo 2057435 4630841 := bstep (se 2 (by rfl) ⟨1736565, by rfl⟩ : syracuseStep 4630841 = 3473131) B3473131
theorem B3087227 : Blo 2057435 3087227 := bstep (se 1 (by rfl) ⟨2315420, by rfl⟩ : syracuseStep 3087227 = 4630841) B4630841
theorem B2058151 : Blo 2057435 2058151 := bstep (se 1 (by rfl) ⟨1543613, by rfl⟩ : syracuseStep 2058151 = 3087227) B3087227
theorem B2315425 : Blo 2057435 2315425 := bbase (se 2 (by rfl) ⟨868284, by rfl⟩ : syracuseStep 2315425 = 1736569) (by norm_num)
theorem B3087233 : Blo 2057435 3087233 := bstep (se 2 (by rfl) ⟨1157712, by rfl⟩ : syracuseStep 3087233 = 2315425) B2315425
theorem B2058155 : Blo 2057435 2058155 := bstep (se 1 (by rfl) ⟨1543616, by rfl⟩ : syracuseStep 2058155 = 3087233) B3087233
theorem B5209717 : Blo 2057435 5209717 := bbase (se 5 (by rfl) ⟨244205, by rfl⟩ : syracuseStep 5209717 = 488411) (by norm_num)
theorem B6946289 : Blo 2057435 6946289 := bstep (se 2 (by rfl) ⟨2604858, by rfl⟩ : syracuseStep 6946289 = 5209717) B5209717
theorem B4630859 : Blo 2057435 4630859 := bstep (se 1 (by rfl) ⟨3473144, by rfl⟩ : syracuseStep 4630859 = 6946289) B6946289
theorem B3087239 : Blo 2057435 3087239 := bstep (se 1 (by rfl) ⟨2315429, by rfl⟩ : syracuseStep 3087239 = 4630859) B4630859
theorem B2058159 : Blo 2057435 2058159 := bstep (se 1 (by rfl) ⟨1543619, by rfl⟩ : syracuseStep 2058159 = 3087239) B3087239
theorem B3087245 : Blo 2057435 3087245 := bbase (se 3 (by rfl) ⟨578858, by rfl⟩ : syracuseStep 3087245 = 1157717) (by norm_num)
theorem B2058163 : Blo 2057435 2058163 := bstep (se 1 (by rfl) ⟨1543622, by rfl⟩ : syracuseStep 2058163 = 3087245) B3087245
theorem B4630877 : Blo 2057435 4630877 := bbase (se 3 (by rfl) ⟨868289, by rfl⟩ : syracuseStep 4630877 = 1736579) (by norm_num)
theorem B3087251 : Blo 2057435 3087251 := bstep (se 1 (by rfl) ⟨2315438, by rfl⟩ : syracuseStep 3087251 = 4630877) B4630877
theorem B2058167 : Blo 2057435 2058167 := bstep (se 1 (by rfl) ⟨1543625, by rfl⟩ : syracuseStep 2058167 = 3087251) B3087251
theorem B3473165 : Blo 2057435 3473165 := bbase (se 3 (by rfl) ⟨651218, by rfl⟩ : syracuseStep 3473165 = 1302437) (by norm_num)
theorem B2315443 : Blo 2057435 2315443 := bstep (se 1 (by rfl) ⟨1736582, by rfl⟩ : syracuseStep 2315443 = 3473165) B3473165
theorem B3087257 : Blo 2057435 3087257 := bstep (se 2 (by rfl) ⟨1157721, by rfl⟩ : syracuseStep 3087257 = 2315443) B2315443
theorem B2058171 : Blo 2057435 2058171 := bstep (se 1 (by rfl) ⟨1543628, by rfl⟩ : syracuseStep 2058171 = 3087257) B3087257
theorem B17582933 : Blo 2057435 17582933 := bbase (se 9 (by rfl) ⟨51512, by rfl⟩ : syracuseStep 17582933 = 103025) (by norm_num)
theorem B11721955 : Blo 2057435 11721955 := bstep (se 1 (by rfl) ⟨8791466, by rfl⟩ : syracuseStep 11721955 = 17582933) B17582933
theorem B15629273 : Blo 2057435 15629273 := bstep (se 2 (by rfl) ⟨5860977, by rfl⟩ : syracuseStep 15629273 = 11721955) B11721955
theorem B10419515 : Blo 2057435 10419515 := bstep (se 1 (by rfl) ⟨7814636, by rfl⟩ : syracuseStep 10419515 = 15629273) B15629273
theorem B6946343 : Blo 2057435 6946343 := bstep (se 1 (by rfl) ⟨5209757, by rfl⟩ : syracuseStep 6946343 = 10419515) B10419515
theorem B4630895 : Blo 2057435 4630895 := bstep (se 1 (by rfl) ⟨3473171, by rfl⟩ : syracuseStep 4630895 = 6946343) B6946343
theorem B3087263 : Blo 2057435 3087263 := bstep (se 1 (by rfl) ⟨2315447, by rfl⟩ : syracuseStep 3087263 = 4630895) B4630895
theorem B2058175 : Blo 2057435 2058175 := bstep (se 1 (by rfl) ⟨1543631, by rfl⟩ : syracuseStep 2058175 = 3087263) B3087263
theorem B3087269 : Blo 2057435 3087269 := bbase (se 4 (by rfl) ⟨289431, by rfl⟩ : syracuseStep 3087269 = 578863) (by norm_num)
theorem B2058179 : Blo 2057435 2058179 := bstep (se 1 (by rfl) ⟨1543634, by rfl⟩ : syracuseStep 2058179 = 3087269) B3087269
theorem B2604889 : Blo 2057435 2604889 := bbase (se 2 (by rfl) ⟨976833, by rfl⟩ : syracuseStep 2604889 = 1953667) (by norm_num)
theorem B3473185 : Blo 2057435 3473185 := bstep (se 2 (by rfl) ⟨1302444, by rfl⟩ : syracuseStep 3473185 = 2604889) B2604889
theorem B4630913 : Blo 2057435 4630913 := bstep (se 2 (by rfl) ⟨1736592, by rfl⟩ : syracuseStep 4630913 = 3473185) B3473185
theorem B3087275 : Blo 2057435 3087275 := bstep (se 1 (by rfl) ⟨2315456, by rfl⟩ : syracuseStep 3087275 = 4630913) B4630913
theorem B2058183 : Blo 2057435 2058183 := bstep (se 1 (by rfl) ⟨1543637, by rfl⟩ : syracuseStep 2058183 = 3087275) B3087275
theorem B2315461 : Blo 2057435 2315461 := bbase (se 4 (by rfl) ⟨217074, by rfl⟩ : syracuseStep 2315461 = 434149) (by norm_num)
theorem B3087281 : Blo 2057435 3087281 := bstep (se 2 (by rfl) ⟨1157730, by rfl⟩ : syracuseStep 3087281 = 2315461) B2315461
theorem B2058187 : Blo 2057435 2058187 := bstep (se 1 (by rfl) ⟨1543640, by rfl⟩ : syracuseStep 2058187 = 3087281) B3087281
theorem B3907349 : Blo 2057435 3907349 := bbase (se 6 (by rfl) ⟨91578, by rfl⟩ : syracuseStep 3907349 = 183157) (by norm_num)
theorem B2604899 : Blo 2057435 2604899 := bstep (se 1 (by rfl) ⟨1953674, by rfl⟩ : syracuseStep 2604899 = 3907349) B3907349
theorem B6946397 : Blo 2057435 6946397 := bstep (se 3 (by rfl) ⟨1302449, by rfl⟩ : syracuseStep 6946397 = 2604899) B2604899
theorem B4630931 : Blo 2057435 4630931 := bstep (se 1 (by rfl) ⟨3473198, by rfl⟩ : syracuseStep 4630931 = 6946397) B6946397
theorem B3087287 : Blo 2057435 3087287 := bstep (se 1 (by rfl) ⟨2315465, by rfl⟩ : syracuseStep 3087287 = 4630931) B4630931
theorem B2058191 : Blo 2057435 2058191 := bstep (se 1 (by rfl) ⟨1543643, by rfl⟩ : syracuseStep 2058191 = 3087287) B3087287
theorem B3087293 : Blo 2057435 3087293 := bbase (se 3 (by rfl) ⟨578867, by rfl⟩ : syracuseStep 3087293 = 1157735) (by norm_num)
theorem B2058195 : Blo 2057435 2058195 := bstep (se 1 (by rfl) ⟨1543646, by rfl⟩ : syracuseStep 2058195 = 3087293) B3087293
theorem B4630949 : Blo 2057435 4630949 := bbase (se 4 (by rfl) ⟨434151, by rfl⟩ : syracuseStep 4630949 = 868303) (by norm_num)
theorem B3087299 : Blo 2057435 3087299 := bstep (se 1 (by rfl) ⟨2315474, by rfl⟩ : syracuseStep 3087299 = 4630949) B4630949
theorem B2058199 : Blo 2057435 2058199 := bstep (se 1 (by rfl) ⟨1543649, by rfl⟩ : syracuseStep 2058199 = 3087299) B3087299
theorem B5209829 : Blo 2057435 5209829 := bbase (se 4 (by rfl) ⟨488421, by rfl⟩ : syracuseStep 5209829 = 976843) (by norm_num)
theorem B3473219 : Blo 2057435 3473219 := bstep (se 1 (by rfl) ⟨2604914, by rfl⟩ : syracuseStep 3473219 = 5209829) B5209829
theorem B2315479 : Blo 2057435 2315479 := bstep (se 1 (by rfl) ⟨1736609, by rfl⟩ : syracuseStep 2315479 = 3473219) B3473219
theorem B3087305 : Blo 2057435 3087305 := bstep (se 2 (by rfl) ⟨1157739, by rfl⟩ : syracuseStep 3087305 = 2315479) B2315479
theorem B2058203 : Blo 2057435 2058203 := bstep (se 1 (by rfl) ⟨1543652, by rfl⟩ : syracuseStep 2058203 = 3087305) B3087305
theorem B2197901 : Blo 2057435 2197901 := bbase (se 3 (by rfl) ⟨412106, by rfl⟩ : syracuseStep 2197901 = 824213) (by norm_num)
theorem B5861069 : Blo 2057435 5861069 := bstep (se 3 (by rfl) ⟨1098950, by rfl⟩ : syracuseStep 5861069 = 2197901) B2197901
theorem B3907379 : Blo 2057435 3907379 := bstep (se 1 (by rfl) ⟨2930534, by rfl⟩ : syracuseStep 3907379 = 5861069) B5861069
theorem B10419677 : Blo 2057435 10419677 := bstep (se 3 (by rfl) ⟨1953689, by rfl⟩ : syracuseStep 10419677 = 3907379) B3907379
theorem B6946451 : Blo 2057435 6946451 := bstep (se 1 (by rfl) ⟨5209838, by rfl⟩ : syracuseStep 6946451 = 10419677) B10419677
theorem B4630967 : Blo 2057435 4630967 := bstep (se 1 (by rfl) ⟨3473225, by rfl⟩ : syracuseStep 4630967 = 6946451) B6946451
theorem B3087311 : Blo 2057435 3087311 := bstep (se 1 (by rfl) ⟨2315483, by rfl⟩ : syracuseStep 3087311 = 4630967) B4630967
theorem B2058207 : Blo 2057435 2058207 := bstep (se 1 (by rfl) ⟨1543655, by rfl⟩ : syracuseStep 2058207 = 3087311) B3087311
theorem B3087317 : Blo 2057435 3087317 := bbase (se 7 (by rfl) ⟨36179, by rfl⟩ : syracuseStep 3087317 = 72359) (by norm_num)
theorem B2058211 : Blo 2057435 2058211 := bstep (se 1 (by rfl) ⟨1543658, by rfl⟩ : syracuseStep 2058211 = 3087317) B3087317
theorem B7814789 : Blo 2057435 7814789 := bbase (se 4 (by rfl) ⟨732636, by rfl⟩ : syracuseStep 7814789 = 1465273) (by norm_num)
theorem B5209859 : Blo 2057435 5209859 := bstep (se 1 (by rfl) ⟨3907394, by rfl⟩ : syracuseStep 5209859 = 7814789) B7814789
theorem B3473239 : Blo 2057435 3473239 := bstep (se 1 (by rfl) ⟨2604929, by rfl⟩ : syracuseStep 3473239 = 5209859) B5209859
theorem B4630985 : Blo 2057435 4630985 := bstep (se 2 (by rfl) ⟨1736619, by rfl⟩ : syracuseStep 4630985 = 3473239) B3473239
theorem B3087323 : Blo 2057435 3087323 := bstep (se 1 (by rfl) ⟨2315492, by rfl⟩ : syracuseStep 3087323 = 4630985) B4630985
theorem B2058215 : Blo 2057435 2058215 := bstep (se 1 (by rfl) ⟨1543661, by rfl⟩ : syracuseStep 2058215 = 3087323) B3087323
theorem B2315497 : Blo 2057435 2315497 := bbase (se 2 (by rfl) ⟨868311, by rfl⟩ : syracuseStep 2315497 = 1736623) (by norm_num)
theorem B3087329 : Blo 2057435 3087329 := bstep (se 2 (by rfl) ⟨1157748, by rfl⟩ : syracuseStep 3087329 = 2315497) B2315497
theorem B2058219 : Blo 2057435 2058219 := bstep (se 1 (by rfl) ⟨1543664, by rfl⟩ : syracuseStep 2058219 = 3087329) B3087329
theorem B11722229 : Blo 2057435 11722229 := bbase (se 5 (by rfl) ⟨549479, by rfl⟩ : syracuseStep 11722229 = 1098959) (by norm_num)
theorem B7814819 : Blo 2057435 7814819 := bstep (se 1 (by rfl) ⟨5861114, by rfl⟩ : syracuseStep 7814819 = 11722229) B11722229
theorem B5209879 : Blo 2057435 5209879 := bstep (se 1 (by rfl) ⟨3907409, by rfl⟩ : syracuseStep 5209879 = 7814819) B7814819
theorem B6946505 : Blo 2057435 6946505 := bstep (se 2 (by rfl) ⟨2604939, by rfl⟩ : syracuseStep 6946505 = 5209879) B5209879
theorem B4631003 : Blo 2057435 4631003 := bstep (se 1 (by rfl) ⟨3473252, by rfl⟩ : syracuseStep 4631003 = 6946505) B6946505
theorem B3087335 : Blo 2057435 3087335 := bstep (se 1 (by rfl) ⟨2315501, by rfl⟩ : syracuseStep 3087335 = 4631003) B4631003
theorem B2058223 : Blo 2057435 2058223 := bstep (se 1 (by rfl) ⟨1543667, by rfl⟩ : syracuseStep 2058223 = 3087335) B3087335
theorem B3087341 : Blo 2057435 3087341 := bbase (se 3 (by rfl) ⟨578876, by rfl⟩ : syracuseStep 3087341 = 1157753) (by norm_num)
theorem B2058227 : Blo 2057435 2058227 := bstep (se 1 (by rfl) ⟨1543670, by rfl⟩ : syracuseStep 2058227 = 3087341) B3087341
theorem B4631021 : Blo 2057435 4631021 := bbase (se 3 (by rfl) ⟨868316, by rfl⟩ : syracuseStep 4631021 = 1736633) (by norm_num)
theorem B3087347 : Blo 2057435 3087347 := bstep (se 1 (by rfl) ⟨2315510, by rfl⟩ : syracuseStep 3087347 = 4631021) B4631021
theorem B2058231 : Blo 2057435 2058231 := bstep (se 1 (by rfl) ⟨1543673, by rfl⟩ : syracuseStep 2058231 = 3087347) B3087347
theorem B9890693 : Blo 2057435 9890693 := bbase (se 4 (by rfl) ⟨927252, by rfl⟩ : syracuseStep 9890693 = 1854505) (by norm_num)
theorem B6593795 : Blo 2057435 6593795 := bstep (se 1 (by rfl) ⟨4945346, by rfl⟩ : syracuseStep 6593795 = 9890693) B9890693
theorem B4395863 : Blo 2057435 4395863 := bstep (se 1 (by rfl) ⟨3296897, by rfl⟩ : syracuseStep 4395863 = 6593795) B6593795
theorem B2930575 : Blo 2057435 2930575 := bstep (se 1 (by rfl) ⟨2197931, by rfl⟩ : syracuseStep 2930575 = 4395863) B4395863
theorem B3907433 : Blo 2057435 3907433 := bstep (se 2 (by rfl) ⟨1465287, by rfl⟩ : syracuseStep 3907433 = 2930575) B2930575
theorem B2604955 : Blo 2057435 2604955 := bstep (se 1 (by rfl) ⟨1953716, by rfl⟩ : syracuseStep 2604955 = 3907433) B3907433
theorem B3473273 : Blo 2057435 3473273 := bstep (se 2 (by rfl) ⟨1302477, by rfl⟩ : syracuseStep 3473273 = 2604955) B2604955
theorem B2315515 : Blo 2057435 2315515 := bstep (se 1 (by rfl) ⟨1736636, by rfl⟩ : syracuseStep 2315515 = 3473273) B3473273
theorem B3087353 : Blo 2057435 3087353 := bstep (se 2 (by rfl) ⟨1157757, by rfl⟩ : syracuseStep 3087353 = 2315515) B2315515
theorem B2058235 : Blo 2057435 2058235 := bstep (se 1 (by rfl) ⟨1543676, by rfl⟩ : syracuseStep 2058235 = 3087353) B3087353
theorem B7519237 : Blo 2057435 7519237 := bbase (se 4 (by rfl) ⟨704928, by rfl⟩ : syracuseStep 7519237 = 1409857) (by norm_num)
theorem B40102597 : Blo 2057435 40102597 := bstep (se 4 (by rfl) ⟨3759618, by rfl⟩ : syracuseStep 40102597 = 7519237) B7519237
theorem B53470129 : Blo 2057435 53470129 := bstep (se 2 (by rfl) ⟨20051298, by rfl⟩ : syracuseStep 53470129 = 40102597) B40102597
theorem B71293505 : Blo 2057435 71293505 := bstep (se 2 (by rfl) ⟨26735064, by rfl⟩ : syracuseStep 71293505 = 53470129) B53470129
theorem B190116013 : Blo 2057435 190116013 := bstep (se 3 (by rfl) ⟨35646752, by rfl⟩ : syracuseStep 190116013 = 71293505) B71293505
theorem B253488017 : Blo 2057435 253488017 := bstep (se 2 (by rfl) ⟨95058006, by rfl⟩ : syracuseStep 253488017 = 190116013) B190116013
theorem B168992011 : Blo 2057435 168992011 := bstep (se 1 (by rfl) ⟨126744008, by rfl⟩ : syracuseStep 168992011 = 253488017) B253488017
theorem B225322681 : Blo 2057435 225322681 := bstep (se 2 (by rfl) ⟨84496005, by rfl⟩ : syracuseStep 225322681 = 168992011) B168992011
theorem B300430241 : Blo 2057435 300430241 := bstep (se 2 (by rfl) ⟨112661340, by rfl⟩ : syracuseStep 300430241 = 225322681) B225322681
theorem B200286827 : Blo 2057435 200286827 := bstep (se 1 (by rfl) ⟨150215120, by rfl⟩ : syracuseStep 200286827 = 300430241) B300430241
theorem B133524551 : Blo 2057435 133524551 := bstep (se 1 (by rfl) ⟨100143413, by rfl⟩ : syracuseStep 133524551 = 200286827) B200286827
theorem B89016367 : Blo 2057435 89016367 := bstep (se 1 (by rfl) ⟨66762275, by rfl⟩ : syracuseStep 89016367 = 133524551) B133524551
theorem B118688489 : Blo 2057435 118688489 := bstep (se 2 (by rfl) ⟨44508183, by rfl⟩ : syracuseStep 118688489 = 89016367) B89016367
theorem B79125659 : Blo 2057435 79125659 := bstep (se 1 (by rfl) ⟨59344244, by rfl⟩ : syracuseStep 79125659 = 118688489) B118688489
theorem B52750439 : Blo 2057435 52750439 := bstep (se 1 (by rfl) ⟨39562829, by rfl⟩ : syracuseStep 52750439 = 79125659) B79125659
theorem B35166959 : Blo 2057435 35166959 := bstep (se 1 (by rfl) ⟨26375219, by rfl⟩ : syracuseStep 35166959 = 52750439) B52750439
theorem B23444639 : Blo 2057435 23444639 := bstep (se 1 (by rfl) ⟨17583479, by rfl⟩ : syracuseStep 23444639 = 35166959) B35166959
theorem B15629759 : Blo 2057435 15629759 := bstep (se 1 (by rfl) ⟨11722319, by rfl⟩ : syracuseStep 15629759 = 23444639) B23444639
theorem B10419839 : Blo 2057435 10419839 := bstep (se 1 (by rfl) ⟨7814879, by rfl⟩ : syracuseStep 10419839 = 15629759) B15629759
theorem B6946559 : Blo 2057435 6946559 := bstep (se 1 (by rfl) ⟨5209919, by rfl⟩ : syracuseStep 6946559 = 10419839) B10419839
theorem B4631039 : Blo 2057435 4631039 := bstep (se 1 (by rfl) ⟨3473279, by rfl⟩ : syracuseStep 4631039 = 6946559) B6946559
theorem B3087359 : Blo 2057435 3087359 := bstep (se 1 (by rfl) ⟨2315519, by rfl⟩ : syracuseStep 3087359 = 4631039) B4631039
theorem B2058239 : Blo 2057435 2058239 := bstep (se 1 (by rfl) ⟨1543679, by rfl⟩ : syracuseStep 2058239 = 3087359) B3087359
theorem B3087365 : Blo 2057435 3087365 := bbase (se 4 (by rfl) ⟨289440, by rfl⟩ : syracuseStep 3087365 = 578881) (by norm_num)
theorem B2058243 : Blo 2057435 2058243 := bstep (se 1 (by rfl) ⟨1543682, by rfl⟩ : syracuseStep 2058243 = 3087365) B3087365
theorem B3473293 : Blo 2057435 3473293 := bbase (se 3 (by rfl) ⟨651242, by rfl⟩ : syracuseStep 3473293 = 1302485) (by norm_num)
theorem B4631057 : Blo 2057435 4631057 := bstep (se 2 (by rfl) ⟨1736646, by rfl⟩ : syracuseStep 4631057 = 3473293) B3473293
theorem B3087371 : Blo 2057435 3087371 := bstep (se 1 (by rfl) ⟨2315528, by rfl⟩ : syracuseStep 3087371 = 4631057) B4631057
theorem B2058247 : Blo 2057435 2058247 := bstep (se 1 (by rfl) ⟨1543685, by rfl⟩ : syracuseStep 2058247 = 3087371) B3087371
theorem B2315533 : Blo 2057435 2315533 := bbase (se 3 (by rfl) ⟨434162, by rfl⟩ : syracuseStep 2315533 = 868325) (by norm_num)
theorem B3087377 : Blo 2057435 3087377 := bstep (se 2 (by rfl) ⟨1157766, by rfl⟩ : syracuseStep 3087377 = 2315533) B2315533
theorem B2058251 : Blo 2057435 2058251 := bstep (se 1 (by rfl) ⟨1543688, by rfl⟩ : syracuseStep 2058251 = 3087377) B3087377
theorem B6946613 : Blo 2057435 6946613 := bbase (se 5 (by rfl) ⟨325622, by rfl⟩ : syracuseStep 6946613 = 651245) (by norm_num)
theorem B4631075 : Blo 2057435 4631075 := bstep (se 1 (by rfl) ⟨3473306, by rfl⟩ : syracuseStep 4631075 = 6946613) B6946613
theorem B3087383 : Blo 2057435 3087383 := bstep (se 1 (by rfl) ⟨2315537, by rfl⟩ : syracuseStep 3087383 = 4631075) B4631075
theorem B2058255 : Blo 2057435 2058255 := bstep (se 1 (by rfl) ⟨1543691, by rfl⟩ : syracuseStep 2058255 = 3087383) B3087383
theorem B3087389 : Blo 2057435 3087389 := bbase (se 3 (by rfl) ⟨578885, by rfl⟩ : syracuseStep 3087389 = 1157771) (by norm_num)
theorem B2058259 : Blo 2057435 2058259 := bstep (se 1 (by rfl) ⟨1543694, by rfl⟩ : syracuseStep 2058259 = 3087389) B3087389
theorem B4631093 : Blo 2057435 4631093 := bbase (se 5 (by rfl) ⟨217082, by rfl⟩ : syracuseStep 4631093 = 434165) (by norm_num)
theorem B3087395 : Blo 2057435 3087395 := bstep (se 1 (by rfl) ⟨2315546, by rfl⟩ : syracuseStep 3087395 = 4631093) B4631093
theorem B2058263 : Blo 2057435 2058263 := bstep (se 1 (by rfl) ⟨1543697, by rfl⟩ : syracuseStep 2058263 = 3087395) B3087395
theorem B8791861 : Blo 2057435 8791861 := bbase (se 5 (by rfl) ⟨412118, by rfl⟩ : syracuseStep 8791861 = 824237) (by norm_num)
theorem B11722481 : Blo 2057435 11722481 := bstep (se 2 (by rfl) ⟨4395930, by rfl⟩ : syracuseStep 11722481 = 8791861) B8791861
theorem B7814987 : Blo 2057435 7814987 := bstep (se 1 (by rfl) ⟨5861240, by rfl⟩ : syracuseStep 7814987 = 11722481) B11722481
theorem B5209991 : Blo 2057435 5209991 := bstep (se 1 (by rfl) ⟨3907493, by rfl⟩ : syracuseStep 5209991 = 7814987) B7814987
theorem B3473327 : Blo 2057435 3473327 := bstep (se 1 (by rfl) ⟨2604995, by rfl⟩ : syracuseStep 3473327 = 5209991) B5209991
theorem B2315551 : Blo 2057435 2315551 := bstep (se 1 (by rfl) ⟨1736663, by rfl⟩ : syracuseStep 2315551 = 3473327) B3473327
theorem B3087401 : Blo 2057435 3087401 := bstep (se 2 (by rfl) ⟨1157775, by rfl⟩ : syracuseStep 3087401 = 2315551) B2315551
theorem B2058267 : Blo 2057435 2058267 := bstep (se 1 (by rfl) ⟨1543700, by rfl⟩ : syracuseStep 2058267 = 3087401) B3087401
theorem B8791877 : Blo 2057435 8791877 := bbase (se 4 (by rfl) ⟨824238, by rfl⟩ : syracuseStep 8791877 = 1648477) (by norm_num)
theorem B5861251 : Blo 2057435 5861251 := bstep (se 1 (by rfl) ⟨4395938, by rfl⟩ : syracuseStep 5861251 = 8791877) B8791877
theorem B7815001 : Blo 2057435 7815001 := bstep (se 2 (by rfl) ⟨2930625, by rfl⟩ : syracuseStep 7815001 = 5861251) B5861251
theorem B10420001 : Blo 2057435 10420001 := bstep (se 2 (by rfl) ⟨3907500, by rfl⟩ : syracuseStep 10420001 = 7815001) B7815001
theorem B6946667 : Blo 2057435 6946667 := bstep (se 1 (by rfl) ⟨5210000, by rfl⟩ : syracuseStep 6946667 = 10420001) B10420001
theorem B4631111 : Blo 2057435 4631111 := bstep (se 1 (by rfl) ⟨3473333, by rfl⟩ : syracuseStep 4631111 = 6946667) B6946667
theorem B3087407 : Blo 2057435 3087407 := bstep (se 1 (by rfl) ⟨2315555, by rfl⟩ : syracuseStep 3087407 = 4631111) B4631111
theorem B2058271 : Blo 2057435 2058271 := bstep (se 1 (by rfl) ⟨1543703, by rfl⟩ : syracuseStep 2058271 = 3087407) B3087407
theorem B3087413 : Blo 2057435 3087413 := bbase (se 5 (by rfl) ⟨144722, by rfl⟩ : syracuseStep 3087413 = 289445) (by norm_num)
theorem B2058275 : Blo 2057435 2058275 := bstep (se 1 (by rfl) ⟨1543706, by rfl⟩ : syracuseStep 2058275 = 3087413) B3087413
theorem B5210021 : Blo 2057435 5210021 := bbase (se 4 (by rfl) ⟨488439, by rfl⟩ : syracuseStep 5210021 = 976879) (by norm_num)
theorem B3473347 : Blo 2057435 3473347 := bstep (se 1 (by rfl) ⟨2605010, by rfl⟩ : syracuseStep 3473347 = 5210021) B5210021
theorem B4631129 : Blo 2057435 4631129 := bstep (se 2 (by rfl) ⟨1736673, by rfl⟩ : syracuseStep 4631129 = 3473347) B3473347
theorem B3087419 : Blo 2057435 3087419 := bstep (se 1 (by rfl) ⟨2315564, by rfl⟩ : syracuseStep 3087419 = 4631129) B4631129
theorem B2058279 : Blo 2057435 2058279 := bstep (se 1 (by rfl) ⟨1543709, by rfl⟩ : syracuseStep 2058279 = 3087419) B3087419
theorem B2315569 : Blo 2057435 2315569 := bbase (se 2 (by rfl) ⟨868338, by rfl⟩ : syracuseStep 2315569 = 1736677) (by norm_num)
theorem B3087425 : Blo 2057435 3087425 := bstep (se 2 (by rfl) ⟨1157784, by rfl⟩ : syracuseStep 3087425 = 2315569) B2315569
theorem B2058283 : Blo 2057435 2058283 := bstep (se 1 (by rfl) ⟨1543712, by rfl⟩ : syracuseStep 2058283 = 3087425) B3087425
theorem B4395973 : Blo 2057435 4395973 := bbase (se 4 (by rfl) ⟨412122, by rfl⟩ : syracuseStep 4395973 = 824245) (by norm_num)
theorem B5861297 : Blo 2057435 5861297 := bstep (se 2 (by rfl) ⟨2197986, by rfl⟩ : syracuseStep 5861297 = 4395973) B4395973
theorem B3907531 : Blo 2057435 3907531 := bstep (se 1 (by rfl) ⟨2930648, by rfl⟩ : syracuseStep 3907531 = 5861297) B5861297
theorem B5210041 : Blo 2057435 5210041 := bstep (se 2 (by rfl) ⟨1953765, by rfl⟩ : syracuseStep 5210041 = 3907531) B3907531
theorem B6946721 : Blo 2057435 6946721 := bstep (se 2 (by rfl) ⟨2605020, by rfl⟩ : syracuseStep 6946721 = 5210041) B5210041
theorem B4631147 : Blo 2057435 4631147 := bstep (se 1 (by rfl) ⟨3473360, by rfl⟩ : syracuseStep 4631147 = 6946721) B6946721
theorem B3087431 : Blo 2057435 3087431 := bstep (se 1 (by rfl) ⟨2315573, by rfl⟩ : syracuseStep 3087431 = 4631147) B4631147
theorem B2058287 : Blo 2057435 2058287 := bstep (se 1 (by rfl) ⟨1543715, by rfl⟩ : syracuseStep 2058287 = 3087431) B3087431
theorem B3087437 : Blo 2057435 3087437 := bbase (se 3 (by rfl) ⟨578894, by rfl⟩ : syracuseStep 3087437 = 1157789) (by norm_num)
theorem B2058291 : Blo 2057435 2058291 := bstep (se 1 (by rfl) ⟨1543718, by rfl⟩ : syracuseStep 2058291 = 3087437) B3087437
theorem B4631165 : Blo 2057435 4631165 := bbase (se 3 (by rfl) ⟨868343, by rfl⟩ : syracuseStep 4631165 = 1736687) (by norm_num)
theorem B3087443 : Blo 2057435 3087443 := bstep (se 1 (by rfl) ⟨2315582, by rfl⟩ : syracuseStep 3087443 = 4631165) B4631165
theorem B2058295 : Blo 2057435 2058295 := bstep (se 1 (by rfl) ⟨1543721, by rfl⟩ : syracuseStep 2058295 = 3087443) B3087443
theorem B3473381 : Blo 2057435 3473381 := bbase (se 4 (by rfl) ⟨325629, by rfl⟩ : syracuseStep 3473381 = 651259) (by norm_num)
theorem B2315587 : Blo 2057435 2315587 := bstep (se 1 (by rfl) ⟨1736690, by rfl⟩ : syracuseStep 2315587 = 3473381) B3473381
theorem B3087449 : Blo 2057435 3087449 := bstep (se 2 (by rfl) ⟨1157793, by rfl⟩ : syracuseStep 3087449 = 2315587) B2315587
theorem B2058299 : Blo 2057435 2058299 := bstep (se 1 (by rfl) ⟨1543724, by rfl⟩ : syracuseStep 2058299 = 3087449) B3087449
theorem B16691093 : Blo 2057435 16691093 := bbase (se 6 (by rfl) ⟨391197, by rfl⟩ : syracuseStep 16691093 = 782395) (by norm_num)
theorem B11127395 : Blo 2057435 11127395 := bstep (se 1 (by rfl) ⟨8345546, by rfl⟩ : syracuseStep 11127395 = 16691093) B16691093
theorem B7418263 : Blo 2057435 7418263 := bstep (se 1 (by rfl) ⟨5563697, by rfl⟩ : syracuseStep 7418263 = 11127395) B11127395
theorem B9891017 : Blo 2057435 9891017 := bstep (se 2 (by rfl) ⟨3709131, by rfl⟩ : syracuseStep 9891017 = 7418263) B7418263
theorem B6594011 : Blo 2057435 6594011 := bstep (se 1 (by rfl) ⟨4945508, by rfl⟩ : syracuseStep 6594011 = 9891017) B9891017
theorem B4396007 : Blo 2057435 4396007 := bstep (se 1 (by rfl) ⟨3297005, by rfl⟩ : syracuseStep 4396007 = 6594011) B6594011
theorem B2930671 : Blo 2057435 2930671 := bstep (se 1 (by rfl) ⟨2198003, by rfl⟩ : syracuseStep 2930671 = 4396007) B4396007
theorem B15630245 : Blo 2057435 15630245 := bstep (se 4 (by rfl) ⟨1465335, by rfl⟩ : syracuseStep 15630245 = 2930671) B2930671
theorem B10420163 : Blo 2057435 10420163 := bstep (se 1 (by rfl) ⟨7815122, by rfl⟩ : syracuseStep 10420163 = 15630245) B15630245
theorem B6946775 : Blo 2057435 6946775 := bstep (se 1 (by rfl) ⟨5210081, by rfl⟩ : syracuseStep 6946775 = 10420163) B10420163
theorem B4631183 : Blo 2057435 4631183 := bstep (se 1 (by rfl) ⟨3473387, by rfl⟩ : syracuseStep 4631183 = 6946775) B6946775
theorem B3087455 : Blo 2057435 3087455 := bstep (se 1 (by rfl) ⟨2315591, by rfl⟩ : syracuseStep 3087455 = 4631183) B4631183
theorem B2058303 : Blo 2057435 2058303 := bstep (se 1 (by rfl) ⟨1543727, by rfl⟩ : syracuseStep 2058303 = 3087455) B3087455
theorem B3087461 : Blo 2057435 3087461 := bbase (se 4 (by rfl) ⟨289449, by rfl⟩ : syracuseStep 3087461 = 578899) (by norm_num)
theorem B2058307 : Blo 2057435 2058307 := bstep (se 1 (by rfl) ⟨1543730, by rfl⟩ : syracuseStep 2058307 = 3087461) B3087461
theorem B3960893 : Blo 2057435 3960893 := bbase (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) (by norm_num)
theorem B2640595 : Blo 2057435 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B3520793 : Blo 2057435 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B9388781 : Blo 2057435 9388781 := bstep (se 3 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 9388781 = 3520793) B3520793
theorem B6259187 : Blo 2057435 6259187 := bstep (se 1 (by rfl) ⟨4694390, by rfl⟩ : syracuseStep 6259187 = 9388781) B9388781
theorem B4172791 : Blo 2057435 4172791 := bstep (se 1 (by rfl) ⟨3129593, by rfl⟩ : syracuseStep 4172791 = 6259187) B6259187
theorem B5563721 : Blo 2057435 5563721 := bstep (se 2 (by rfl) ⟨2086395, by rfl⟩ : syracuseStep 5563721 = 4172791) B4172791
theorem B3709147 : Blo 2057435 3709147 := bstep (se 1 (by rfl) ⟨2781860, by rfl⟩ : syracuseStep 3709147 = 5563721) B5563721
theorem B4945529 : Blo 2057435 4945529 := bstep (se 2 (by rfl) ⟨1854573, by rfl⟩ : syracuseStep 4945529 = 3709147) B3709147
theorem B3297019 : Blo 2057435 3297019 := bstep (se 1 (by rfl) ⟨2472764, by rfl⟩ : syracuseStep 3297019 = 4945529) B4945529
theorem B4396025 : Blo 2057435 4396025 := bstep (se 2 (by rfl) ⟨1648509, by rfl⟩ : syracuseStep 4396025 = 3297019) B3297019
theorem B2930683 : Blo 2057435 2930683 := bstep (se 1 (by rfl) ⟨2198012, by rfl⟩ : syracuseStep 2930683 = 4396025) B4396025
theorem B3907577 : Blo 2057435 3907577 := bstep (se 2 (by rfl) ⟨1465341, by rfl⟩ : syracuseStep 3907577 = 2930683) B2930683
theorem B2605051 : Blo 2057435 2605051 := bstep (se 1 (by rfl) ⟨1953788, by rfl⟩ : syracuseStep 2605051 = 3907577) B3907577
theorem B3473401 : Blo 2057435 3473401 := bstep (se 2 (by rfl) ⟨1302525, by rfl⟩ : syracuseStep 3473401 = 2605051) B2605051
theorem B4631201 : Blo 2057435 4631201 := bstep (se 2 (by rfl) ⟨1736700, by rfl⟩ : syracuseStep 4631201 = 3473401) B3473401
theorem B3087467 : Blo 2057435 3087467 := bstep (se 1 (by rfl) ⟨2315600, by rfl⟩ : syracuseStep 3087467 = 4631201) B4631201
theorem B2058311 : Blo 2057435 2058311 := bstep (se 1 (by rfl) ⟨1543733, by rfl⟩ : syracuseStep 2058311 = 3087467) B3087467
theorem B2315605 : Blo 2057435 2315605 := bbase (se 17 (by rfl) ⟨26, by rfl⟩ : syracuseStep 2315605 = 53) (by norm_num)
theorem B3087473 : Blo 2057435 3087473 := bstep (se 2 (by rfl) ⟨1157802, by rfl⟩ : syracuseStep 3087473 = 2315605) B2315605
theorem B2058315 : Blo 2057435 2058315 := bstep (se 1 (by rfl) ⟨1543736, by rfl⟩ : syracuseStep 2058315 = 3087473) B3087473
theorem B2605061 : Blo 2057435 2605061 := bbase (se 4 (by rfl) ⟨244224, by rfl⟩ : syracuseStep 2605061 = 488449) (by norm_num)
theorem B6946829 : Blo 2057435 6946829 := bstep (se 3 (by rfl) ⟨1302530, by rfl⟩ : syracuseStep 6946829 = 2605061) B2605061
theorem B4631219 : Blo 2057435 4631219 := bstep (se 1 (by rfl) ⟨3473414, by rfl⟩ : syracuseStep 4631219 = 6946829) B6946829
theorem B3087479 : Blo 2057435 3087479 := bstep (se 1 (by rfl) ⟨2315609, by rfl⟩ : syracuseStep 3087479 = 4631219) B4631219
theorem B2058319 : Blo 2057435 2058319 := bstep (se 1 (by rfl) ⟨1543739, by rfl⟩ : syracuseStep 2058319 = 3087479) B3087479
theorem B3087485 : Blo 2057435 3087485 := bbase (se 3 (by rfl) ⟨578903, by rfl⟩ : syracuseStep 3087485 = 1157807) (by norm_num)
theorem B2058323 : Blo 2057435 2058323 := bstep (se 1 (by rfl) ⟨1543742, by rfl⟩ : syracuseStep 2058323 = 3087485) B3087485
theorem B4631237 : Blo 2057435 4631237 := bbase (se 4 (by rfl) ⟨434178, by rfl⟩ : syracuseStep 4631237 = 868357) (by norm_num)
theorem B3087491 : Blo 2057435 3087491 := bstep (se 1 (by rfl) ⟨2315618, by rfl⟩ : syracuseStep 3087491 = 4631237) B4631237
theorem B2058327 : Blo 2057435 2058327 := bstep (se 1 (by rfl) ⟨1543745, by rfl⟩ : syracuseStep 2058327 = 3087491) B3087491
theorem B2114881 : Blo 2057435 2114881 := bbase (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) (by norm_num)
theorem B45117461 : Blo 2057435 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B30078307 : Blo 2057435 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B40104409 : Blo 2057435 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B53472545 : Blo 2057435 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B35648363 : Blo 2057435 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B23765575 : Blo 2057435 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B31687433 : Blo 2057435 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B21124955 : Blo 2057435 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B14083303 : Blo 2057435 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B18777737 : Blo 2057435 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B12518491 : Blo 2057435 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B16691321 : Blo 2057435 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B11127547 : Blo 2057435 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B14836729 : Blo 2057435 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B19782305 : Blo 2057435 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B13188203 : Blo 2057435 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B8792135 : Blo 2057435 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B5861423 : Blo 2057435 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B3907615 : Blo 2057435 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B5210153 : Blo 2057435 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B3473435 : Blo 2057435 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B2315623 : Blo 2057435 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B3087497 : Blo 2057435 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B2058331 : Blo 2057435 2058331 := bstep (se 1 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 2058331 = 3087497) B3087497
theorem B10420325 : Blo 2057435 10420325 := bbase (se 4 (by rfl) ⟨976905, by rfl⟩ : syracuseStep 10420325 = 1953811) (by norm_num)
theorem B6946883 : Blo 2057435 6946883 := bstep (se 1 (by rfl) ⟨5210162, by rfl⟩ : syracuseStep 6946883 = 10420325) B10420325
theorem B4631255 : Blo 2057435 4631255 := bstep (se 1 (by rfl) ⟨3473441, by rfl⟩ : syracuseStep 4631255 = 6946883) B6946883
theorem B3087503 : Blo 2057435 3087503 := bstep (se 1 (by rfl) ⟨2315627, by rfl⟩ : syracuseStep 3087503 = 4631255) B4631255
theorem B2058335 : Blo 2057435 2058335 := bstep (se 1 (by rfl) ⟨1543751, by rfl⟩ : syracuseStep 2058335 = 3087503) B3087503
theorem B3087509 : Blo 2057435 3087509 := bbase (se 6 (by rfl) ⟨72363, by rfl⟩ : syracuseStep 3087509 = 144727) (by norm_num)
theorem B2058339 : Blo 2057435 2058339 := bstep (se 1 (by rfl) ⟨1543754, by rfl⟩ : syracuseStep 2058339 = 3087509) B3087509
theorem B18777845 : Blo 2057435 18777845 := bbase (se 5 (by rfl) ⟨880211, by rfl⟩ : syracuseStep 18777845 = 1760423) (by norm_num)
theorem B12518563 : Blo 2057435 12518563 := bstep (se 1 (by rfl) ⟨9388922, by rfl⟩ : syracuseStep 12518563 = 18777845) B18777845
theorem B16691417 : Blo 2057435 16691417 := bstep (se 2 (by rfl) ⟨6259281, by rfl⟩ : syracuseStep 16691417 = 12518563) B12518563
theorem B11127611 : Blo 2057435 11127611 := bstep (se 1 (by rfl) ⟨8345708, by rfl⟩ : syracuseStep 11127611 = 16691417) B16691417
theorem B7418407 : Blo 2057435 7418407 := bstep (se 1 (by rfl) ⟨5563805, by rfl⟩ : syracuseStep 7418407 = 11127611) B11127611
theorem B9891209 : Blo 2057435 9891209 := bstep (se 2 (by rfl) ⟨3709203, by rfl⟩ : syracuseStep 9891209 = 7418407) B7418407
theorem B6594139 : Blo 2057435 6594139 := bstep (se 1 (by rfl) ⟨4945604, by rfl⟩ : syracuseStep 6594139 = 9891209) B9891209
theorem B8792185 : Blo 2057435 8792185 := bstep (se 2 (by rfl) ⟨3297069, by rfl⟩ : syracuseStep 8792185 = 6594139) B6594139
theorem B11722913 : Blo 2057435 11722913 := bstep (se 2 (by rfl) ⟨4396092, by rfl⟩ : syracuseStep 11722913 = 8792185) B8792185
theorem B7815275 : Blo 2057435 7815275 := bstep (se 1 (by rfl) ⟨5861456, by rfl⟩ : syracuseStep 7815275 = 11722913) B11722913
theorem B5210183 : Blo 2057435 5210183 := bstep (se 1 (by rfl) ⟨3907637, by rfl⟩ : syracuseStep 5210183 = 7815275) B7815275
theorem B3473455 : Blo 2057435 3473455 := bstep (se 1 (by rfl) ⟨2605091, by rfl⟩ : syracuseStep 3473455 = 5210183) B5210183
theorem B4631273 : Blo 2057435 4631273 := bstep (se 2 (by rfl) ⟨1736727, by rfl⟩ : syracuseStep 4631273 = 3473455) B3473455
theorem B3087515 : Blo 2057435 3087515 := bstep (se 1 (by rfl) ⟨2315636, by rfl⟩ : syracuseStep 3087515 = 4631273) B4631273
theorem B2058343 : Blo 2057435 2058343 := bstep (se 1 (by rfl) ⟨1543757, by rfl⟩ : syracuseStep 2058343 = 3087515) B3087515
theorem B2315641 : Blo 2057435 2315641 := bbase (se 2 (by rfl) ⟨868365, by rfl⟩ : syracuseStep 2315641 = 1736731) (by norm_num)
theorem B3087521 : Blo 2057435 3087521 := bstep (se 2 (by rfl) ⟨1157820, by rfl⟩ : syracuseStep 3087521 = 2315641) B2315641
theorem B2058347 : Blo 2057435 2058347 := bstep (se 1 (by rfl) ⟨1543760, by rfl⟩ : syracuseStep 2058347 = 3087521) B3087521
theorem B6684133 : Blo 2057435 6684133 := bbase (se 4 (by rfl) ⟨626637, by rfl⟩ : syracuseStep 6684133 = 1253275) (by norm_num)
theorem B8912177 : Blo 2057435 8912177 := bstep (se 2 (by rfl) ⟨3342066, by rfl⟩ : syracuseStep 8912177 = 6684133) B6684133
theorem B5941451 : Blo 2057435 5941451 := bstep (se 1 (by rfl) ⟨4456088, by rfl⟩ : syracuseStep 5941451 = 8912177) B8912177
theorem B15843869 : Blo 2057435 15843869 := bstep (se 3 (by rfl) ⟨2970725, by rfl⟩ : syracuseStep 15843869 = 5941451) B5941451
theorem B10562579 : Blo 2057435 10562579 := bstep (se 1 (by rfl) ⟨7921934, by rfl⟩ : syracuseStep 10562579 = 15843869) B15843869
theorem B7041719 : Blo 2057435 7041719 := bstep (se 1 (by rfl) ⟨5281289, by rfl⟩ : syracuseStep 7041719 = 10562579) B10562579
theorem B4694479 : Blo 2057435 4694479 := bstep (se 1 (by rfl) ⟨3520859, by rfl⟩ : syracuseStep 4694479 = 7041719) B7041719
theorem B25037221 : Blo 2057435 25037221 := bstep (se 4 (by rfl) ⟨2347239, by rfl⟩ : syracuseStep 25037221 = 4694479) B4694479
theorem B33382961 : Blo 2057435 33382961 := bstep (se 2 (by rfl) ⟨12518610, by rfl⟩ : syracuseStep 33382961 = 25037221) B25037221
theorem B22255307 : Blo 2057435 22255307 := bstep (se 1 (by rfl) ⟨16691480, by rfl⟩ : syracuseStep 22255307 = 33382961) B33382961
theorem B14836871 : Blo 2057435 14836871 := bstep (se 1 (by rfl) ⟨11127653, by rfl⟩ : syracuseStep 14836871 = 22255307) B22255307
theorem B9891247 : Blo 2057435 9891247 := bstep (se 1 (by rfl) ⟨7418435, by rfl⟩ : syracuseStep 9891247 = 14836871) B14836871
theorem B13188329 : Blo 2057435 13188329 := bstep (se 2 (by rfl) ⟨4945623, by rfl⟩ : syracuseStep 13188329 = 9891247) B9891247
theorem B8792219 : Blo 2057435 8792219 := bstep (se 1 (by rfl) ⟨6594164, by rfl⟩ : syracuseStep 8792219 = 13188329) B13188329
theorem B5861479 : Blo 2057435 5861479 := bstep (se 1 (by rfl) ⟨4396109, by rfl⟩ : syracuseStep 5861479 = 8792219) B8792219
theorem B7815305 : Blo 2057435 7815305 := bstep (se 2 (by rfl) ⟨2930739, by rfl⟩ : syracuseStep 7815305 = 5861479) B5861479
theorem B5210203 : Blo 2057435 5210203 := bstep (se 1 (by rfl) ⟨3907652, by rfl⟩ : syracuseStep 5210203 = 7815305) B7815305
theorem B6946937 : Blo 2057435 6946937 := bstep (se 2 (by rfl) ⟨2605101, by rfl⟩ : syracuseStep 6946937 = 5210203) B5210203
theorem B4631291 : Blo 2057435 4631291 := bstep (se 1 (by rfl) ⟨3473468, by rfl⟩ : syracuseStep 4631291 = 6946937) B6946937
theorem B3087527 : Blo 2057435 3087527 := bstep (se 1 (by rfl) ⟨2315645, by rfl⟩ : syracuseStep 3087527 = 4631291) B4631291
theorem B2058351 : Blo 2057435 2058351 := bstep (se 1 (by rfl) ⟨1543763, by rfl⟩ : syracuseStep 2058351 = 3087527) B3087527
theorem B3087533 : Blo 2057435 3087533 := bbase (se 3 (by rfl) ⟨578912, by rfl⟩ : syracuseStep 3087533 = 1157825) (by norm_num)
theorem B2058355 : Blo 2057435 2058355 := bstep (se 1 (by rfl) ⟨1543766, by rfl⟩ : syracuseStep 2058355 = 3087533) B3087533
theorem B4631309 : Blo 2057435 4631309 := bbase (se 3 (by rfl) ⟨868370, by rfl⟩ : syracuseStep 4631309 = 1736741) (by norm_num)
theorem B3087539 : Blo 2057435 3087539 := bstep (se 1 (by rfl) ⟨2315654, by rfl⟩ : syracuseStep 3087539 = 4631309) B4631309
theorem B2058359 : Blo 2057435 2058359 := bstep (se 1 (by rfl) ⟨1543769, by rfl⟩ : syracuseStep 2058359 = 3087539) B3087539
theorem B2605117 : Blo 2057435 2605117 := bbase (se 3 (by rfl) ⟨488459, by rfl⟩ : syracuseStep 2605117 = 976919) (by norm_num)
theorem B3473489 : Blo 2057435 3473489 := bstep (se 2 (by rfl) ⟨1302558, by rfl⟩ : syracuseStep 3473489 = 2605117) B2605117
theorem B2315659 : Blo 2057435 2315659 := bstep (se 1 (by rfl) ⟨1736744, by rfl⟩ : syracuseStep 2315659 = 3473489) B3473489
theorem B3087545 : Blo 2057435 3087545 := bstep (se 2 (by rfl) ⟨1157829, by rfl⟩ : syracuseStep 3087545 = 2315659) B2315659
theorem B2058363 : Blo 2057435 2058363 := bstep (se 1 (by rfl) ⟨1543772, by rfl⟩ : syracuseStep 2058363 = 3087545) B3087545
theorem B2640665 : Blo 2057435 2640665 := bbase (se 2 (by rfl) ⟨990249, by rfl⟩ : syracuseStep 2640665 = 1980499) (by norm_num)
theorem B7041773 : Blo 2057435 7041773 := bstep (se 3 (by rfl) ⟨1320332, by rfl⟩ : syracuseStep 7041773 = 2640665) B2640665
theorem B18778061 : Blo 2057435 18778061 := bstep (se 3 (by rfl) ⟨3520886, by rfl⟩ : syracuseStep 18778061 = 7041773) B7041773
theorem B12518707 : Blo 2057435 12518707 := bstep (se 1 (by rfl) ⟨9389030, by rfl⟩ : syracuseStep 12518707 = 18778061) B18778061
theorem B16691609 : Blo 2057435 16691609 := bstep (se 2 (by rfl) ⟨6259353, by rfl⟩ : syracuseStep 16691609 = 12518707) B12518707
theorem B11127739 : Blo 2057435 11127739 := bstep (se 1 (by rfl) ⟨8345804, by rfl⟩ : syracuseStep 11127739 = 16691609) B16691609
theorem B14836985 : Blo 2057435 14836985 := bstep (se 2 (by rfl) ⟨5563869, by rfl⟩ : syracuseStep 14836985 = 11127739) B11127739
theorem B9891323 : Blo 2057435 9891323 := bstep (se 1 (by rfl) ⟨7418492, by rfl⟩ : syracuseStep 9891323 = 14836985) B14836985
theorem B6594215 : Blo 2057435 6594215 := bstep (se 1 (by rfl) ⟨4945661, by rfl⟩ : syracuseStep 6594215 = 9891323) B9891323
theorem B17584573 : Blo 2057435 17584573 := bstep (se 3 (by rfl) ⟨3297107, by rfl⟩ : syracuseStep 17584573 = 6594215) B6594215
theorem B23446097 : Blo 2057435 23446097 := bstep (se 2 (by rfl) ⟨8792286, by rfl⟩ : syracuseStep 23446097 = 17584573) B17584573
theorem B15630731 : Blo 2057435 15630731 := bstep (se 1 (by rfl) ⟨11723048, by rfl⟩ : syracuseStep 15630731 = 23446097) B23446097
theorem B10420487 : Blo 2057435 10420487 := bstep (se 1 (by rfl) ⟨7815365, by rfl⟩ : syracuseStep 10420487 = 15630731) B15630731
theorem B6946991 : Blo 2057435 6946991 := bstep (se 1 (by rfl) ⟨5210243, by rfl⟩ : syracuseStep 6946991 = 10420487) B10420487
theorem B4631327 : Blo 2057435 4631327 := bstep (se 1 (by rfl) ⟨3473495, by rfl⟩ : syracuseStep 4631327 = 6946991) B6946991
theorem B3087551 : Blo 2057435 3087551 := bstep (se 1 (by rfl) ⟨2315663, by rfl⟩ : syracuseStep 3087551 = 4631327) B4631327
theorem B2058367 : Blo 2057435 2058367 := bstep (se 1 (by rfl) ⟨1543775, by rfl⟩ : syracuseStep 2058367 = 3087551) B3087551
theorem B3087557 : Blo 2057435 3087557 := bbase (se 4 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 3087557 = 578917) (by norm_num)
theorem B2058371 : Blo 2057435 2058371 := bstep (se 1 (by rfl) ⟨1543778, by rfl⟩ : syracuseStep 2058371 = 3087557) B3087557
theorem B3473509 : Blo 2057435 3473509 := bbase (se 4 (by rfl) ⟨325641, by rfl⟩ : syracuseStep 3473509 = 651283) (by norm_num)
theorem B4631345 : Blo 2057435 4631345 := bstep (se 2 (by rfl) ⟨1736754, by rfl⟩ : syracuseStep 4631345 = 3473509) B3473509
theorem B3087563 : Blo 2057435 3087563 := bstep (se 1 (by rfl) ⟨2315672, by rfl⟩ : syracuseStep 3087563 = 4631345) B4631345
theorem B2058375 : Blo 2057435 2058375 := bstep (se 1 (by rfl) ⟨1543781, by rfl⟩ : syracuseStep 2058375 = 3087563) B3087563
theorem B2315677 : Blo 2057435 2315677 := bbase (se 3 (by rfl) ⟨434189, by rfl⟩ : syracuseStep 2315677 = 868379) (by norm_num)
theorem B3087569 : Blo 2057435 3087569 := bstep (se 2 (by rfl) ⟨1157838, by rfl⟩ : syracuseStep 3087569 = 2315677) B2315677
theorem B2058379 : Blo 2057435 2058379 := bstep (se 1 (by rfl) ⟨1543784, by rfl⟩ : syracuseStep 2058379 = 3087569) B3087569
theorem B6947045 : Blo 2057435 6947045 := bbase (se 4 (by rfl) ⟨651285, by rfl⟩ : syracuseStep 6947045 = 1302571) (by norm_num)
theorem B4631363 : Blo 2057435 4631363 := bstep (se 1 (by rfl) ⟨3473522, by rfl⟩ : syracuseStep 4631363 = 6947045) B6947045
theorem B3087575 : Blo 2057435 3087575 := bstep (se 1 (by rfl) ⟨2315681, by rfl⟩ : syracuseStep 3087575 = 4631363) B4631363
theorem B2058383 : Blo 2057435 2058383 := bstep (se 1 (by rfl) ⟨1543787, by rfl⟩ : syracuseStep 2058383 = 3087575) B3087575
theorem B3087581 : Blo 2057435 3087581 := bbase (se 3 (by rfl) ⟨578921, by rfl⟩ : syracuseStep 3087581 = 1157843) (by norm_num)
theorem B2058387 : Blo 2057435 2058387 := bstep (se 1 (by rfl) ⟨1543790, by rfl⟩ : syracuseStep 2058387 = 3087581) B3087581
theorem B4631381 : Blo 2057435 4631381 := bbase (se 9 (by rfl) ⟨13568, by rfl⟩ : syracuseStep 4631381 = 27137) (by norm_num)
theorem B3087587 : Blo 2057435 3087587 := bstep (se 1 (by rfl) ⟨2315690, by rfl⟩ : syracuseStep 3087587 = 4631381) B4631381
theorem B2058391 : Blo 2057435 2058391 := bstep (se 1 (by rfl) ⟨1543793, by rfl⟩ : syracuseStep 2058391 = 3087587) B3087587
theorem B5861605 : Blo 2057435 5861605 := bbase (se 4 (by rfl) ⟨549525, by rfl⟩ : syracuseStep 5861605 = 1099051) (by norm_num)
theorem B7815473 : Blo 2057435 7815473 := bstep (se 2 (by rfl) ⟨2930802, by rfl⟩ : syracuseStep 7815473 = 5861605) B5861605
theorem B5210315 : Blo 2057435 5210315 := bstep (se 1 (by rfl) ⟨3907736, by rfl⟩ : syracuseStep 5210315 = 7815473) B7815473
theorem B3473543 : Blo 2057435 3473543 := bstep (se 1 (by rfl) ⟨2605157, by rfl⟩ : syracuseStep 3473543 = 5210315) B5210315
theorem B2315695 : Blo 2057435 2315695 := bstep (se 1 (by rfl) ⟨1736771, by rfl⟩ : syracuseStep 2315695 = 3473543) B3473543
theorem B3087593 : Blo 2057435 3087593 := bstep (se 2 (by rfl) ⟨1157847, by rfl⟩ : syracuseStep 3087593 = 2315695) B2315695
theorem B2058395 : Blo 2057435 2058395 := bstep (se 1 (by rfl) ⟨1543796, by rfl⟩ : syracuseStep 2058395 = 3087593) B3087593
theorem B5426509 : Blo 2057435 5426509 := bbase (se 3 (by rfl) ⟨1017470, by rfl⟩ : syracuseStep 5426509 = 2034941) (by norm_num)
theorem B7235345 : Blo 2057435 7235345 := bstep (se 2 (by rfl) ⟨2713254, by rfl⟩ : syracuseStep 7235345 = 5426509) B5426509
theorem B4823563 : Blo 2057435 4823563 := bstep (se 1 (by rfl) ⟨3617672, by rfl⟩ : syracuseStep 4823563 = 7235345) B7235345
theorem B6431417 : Blo 2057435 6431417 := bstep (se 2 (by rfl) ⟨2411781, by rfl⟩ : syracuseStep 6431417 = 4823563) B4823563
theorem B4287611 : Blo 2057435 4287611 := bstep (se 1 (by rfl) ⟨3215708, by rfl⟩ : syracuseStep 4287611 = 6431417) B6431417
theorem B11433629 : Blo 2057435 11433629 := bstep (se 3 (by rfl) ⟨2143805, by rfl⟩ : syracuseStep 11433629 = 4287611) B4287611
theorem B7622419 : Blo 2057435 7622419 := bstep (se 1 (by rfl) ⟨5716814, by rfl⟩ : syracuseStep 7622419 = 11433629) B11433629
theorem B10163225 : Blo 2057435 10163225 := bstep (se 2 (by rfl) ⟨3811209, by rfl⟩ : syracuseStep 10163225 = 7622419) B7622419
theorem B6775483 : Blo 2057435 6775483 := bstep (se 1 (by rfl) ⟨5081612, by rfl⟩ : syracuseStep 6775483 = 10163225) B10163225
theorem B9033977 : Blo 2057435 9033977 := bstep (se 2 (by rfl) ⟨3387741, by rfl⟩ : syracuseStep 9033977 = 6775483) B6775483
theorem B6022651 : Blo 2057435 6022651 := bstep (se 1 (by rfl) ⟨4516988, by rfl⟩ : syracuseStep 6022651 = 9033977) B9033977
theorem B8030201 : Blo 2057435 8030201 := bstep (se 2 (by rfl) ⟨3011325, by rfl⟩ : syracuseStep 8030201 = 6022651) B6022651
theorem B85655477 : Blo 2057435 85655477 := bstep (se 5 (by rfl) ⟨4015100, by rfl⟩ : syracuseStep 85655477 = 8030201) B8030201
theorem B57103651 : Blo 2057435 57103651 := bstep (se 1 (by rfl) ⟨42827738, by rfl⟩ : syracuseStep 57103651 = 85655477) B85655477
theorem B76138201 : Blo 2057435 76138201 := bstep (se 2 (by rfl) ⟨28551825, by rfl⟩ : syracuseStep 76138201 = 57103651) B57103651
theorem B406070405 : Blo 2057435 406070405 := bstep (se 4 (by rfl) ⟨38069100, by rfl⟩ : syracuseStep 406070405 = 76138201) B76138201
theorem B270713603 : Blo 2057435 270713603 := bstep (se 1 (by rfl) ⟨203035202, by rfl⟩ : syracuseStep 270713603 = 406070405) B406070405
theorem B180475735 : Blo 2057435 180475735 := bstep (se 1 (by rfl) ⟨135356801, by rfl⟩ : syracuseStep 180475735 = 270713603) B270713603
theorem B240634313 : Blo 2057435 240634313 := bstep (se 2 (by rfl) ⟨90237867, by rfl⟩ : syracuseStep 240634313 = 180475735) B180475735
theorem B160422875 : Blo 2057435 160422875 := bstep (se 1 (by rfl) ⟨120317156, by rfl⟩ : syracuseStep 160422875 = 240634313) B240634313
theorem B106948583 : Blo 2057435 106948583 := bstep (se 1 (by rfl) ⟨80211437, by rfl⟩ : syracuseStep 106948583 = 160422875) B160422875
theorem B71299055 : Blo 2057435 71299055 := bstep (se 1 (by rfl) ⟨53474291, by rfl⟩ : syracuseStep 71299055 = 106948583) B106948583
theorem B47532703 : Blo 2057435 47532703 := bstep (se 1 (by rfl) ⟨35649527, by rfl⟩ : syracuseStep 47532703 = 71299055) B71299055
theorem B63376937 : Blo 2057435 63376937 := bstep (se 2 (by rfl) ⟨23766351, by rfl⟩ : syracuseStep 63376937 = 47532703) B47532703
theorem B42251291 : Blo 2057435 42251291 := bstep (se 1 (by rfl) ⟨31688468, by rfl⟩ : syracuseStep 42251291 = 63376937) B63376937
theorem B28167527 : Blo 2057435 28167527 := bstep (se 1 (by rfl) ⟨21125645, by rfl⟩ : syracuseStep 28167527 = 42251291) B42251291
theorem B75113405 : Blo 2057435 75113405 := bstep (se 3 (by rfl) ⟨14083763, by rfl⟩ : syracuseStep 75113405 = 28167527) B28167527
theorem B50075603 : Blo 2057435 50075603 := bstep (se 1 (by rfl) ⟨37556702, by rfl⟩ : syracuseStep 50075603 = 75113405) B75113405
theorem B33383735 : Blo 2057435 33383735 := bstep (se 1 (by rfl) ⟨25037801, by rfl⟩ : syracuseStep 33383735 = 50075603) B50075603
theorem B22255823 : Blo 2057435 22255823 := bstep (se 1 (by rfl) ⟨16691867, by rfl⟩ : syracuseStep 22255823 = 33383735) B33383735
theorem B59348861 : Blo 2057435 59348861 := bstep (se 3 (by rfl) ⟨11127911, by rfl⟩ : syracuseStep 59348861 = 22255823) B22255823
theorem B39565907 : Blo 2057435 39565907 := bstep (se 1 (by rfl) ⟨29674430, by rfl⟩ : syracuseStep 39565907 = 59348861) B59348861
theorem B26377271 : Blo 2057435 26377271 := bstep (se 1 (by rfl) ⟨19782953, by rfl⟩ : syracuseStep 26377271 = 39565907) B39565907
theorem B17584847 : Blo 2057435 17584847 := bstep (se 1 (by rfl) ⟨13188635, by rfl⟩ : syracuseStep 17584847 = 26377271) B26377271
theorem B11723231 : Blo 2057435 11723231 := bstep (se 1 (by rfl) ⟨8792423, by rfl⟩ : syracuseStep 11723231 = 17584847) B17584847
theorem B7815487 : Blo 2057435 7815487 := bstep (se 1 (by rfl) ⟨5861615, by rfl⟩ : syracuseStep 7815487 = 11723231) B11723231
theorem B10420649 : Blo 2057435 10420649 := bstep (se 2 (by rfl) ⟨3907743, by rfl⟩ : syracuseStep 10420649 = 7815487) B7815487
theorem B6947099 : Blo 2057435 6947099 := bstep (se 1 (by rfl) ⟨5210324, by rfl⟩ : syracuseStep 6947099 = 10420649) B10420649
theorem B4631399 : Blo 2057435 4631399 := bstep (se 1 (by rfl) ⟨3473549, by rfl⟩ : syracuseStep 4631399 = 6947099) B6947099
theorem B3087599 : Blo 2057435 3087599 := bstep (se 1 (by rfl) ⟨2315699, by rfl⟩ : syracuseStep 3087599 = 4631399) B4631399
theorem B2058399 : Blo 2057435 2058399 := bstep (se 1 (by rfl) ⟨1543799, by rfl⟩ : syracuseStep 2058399 = 3087599) B3087599
theorem B3087605 : Blo 2057435 3087605 := bbase (se 5 (by rfl) ⟨144731, by rfl⟩ : syracuseStep 3087605 = 289463) (by norm_num)
theorem B2058403 : Blo 2057435 2058403 := bstep (se 1 (by rfl) ⟨1543802, by rfl⟩ : syracuseStep 2058403 = 3087605) B3087605
theorem B6259477 : Blo 2057435 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B8345969 : Blo 2057435 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B5563979 : Blo 2057435 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B3709319 : Blo 2057435 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B9891517 : Blo 2057435 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B13188689 : Blo 2057435 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B8792459 : Blo 2057435 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B5861639 : Blo 2057435 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B3907759 : Blo 2057435 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B5210345 : Blo 2057435 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B3473563 : Blo 2057435 3473563 := bstep (se 1 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 3473563 = 5210345) B5210345
theorem B4631417 : Blo 2057435 4631417 := bstep (se 2 (by rfl) ⟨1736781, by rfl⟩ : syracuseStep 4631417 = 3473563) B3473563
theorem B3087611 : Blo 2057435 3087611 := bstep (se 1 (by rfl) ⟨2315708, by rfl⟩ : syracuseStep 3087611 = 4631417) B4631417
theorem B2058407 : Blo 2057435 2058407 := bstep (se 1 (by rfl) ⟨1543805, by rfl⟩ : syracuseStep 2058407 = 3087611) B3087611
theorem B2315713 : Blo 2057435 2315713 := bbase (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) (by norm_num)
theorem B3087617 : Blo 2057435 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B2058411 : Blo 2057435 2058411 := bstep (se 1 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 2058411 = 3087617) B3087617
theorem B5210365 : Blo 2057435 5210365 := bbase (se 3 (by rfl) ⟨976943, by rfl⟩ : syracuseStep 5210365 = 1953887) (by norm_num)
theorem B6947153 : Blo 2057435 6947153 := bstep (se 2 (by rfl) ⟨2605182, by rfl⟩ : syracuseStep 6947153 = 5210365) B5210365
theorem B4631435 : Blo 2057435 4631435 := bstep (se 1 (by rfl) ⟨3473576, by rfl⟩ : syracuseStep 4631435 = 6947153) B6947153
theorem B3087623 : Blo 2057435 3087623 := bstep (se 1 (by rfl) ⟨2315717, by rfl⟩ : syracuseStep 3087623 = 4631435) B4631435
theorem B2058415 : Blo 2057435 2058415 := bstep (se 1 (by rfl) ⟨1543811, by rfl⟩ : syracuseStep 2058415 = 3087623) B3087623
theorem B3087629 : Blo 2057435 3087629 := bbase (se 3 (by rfl) ⟨578930, by rfl⟩ : syracuseStep 3087629 = 1157861) (by norm_num)
theorem B2058419 : Blo 2057435 2058419 := bstep (se 1 (by rfl) ⟨1543814, by rfl⟩ : syracuseStep 2058419 = 3087629) B3087629
theorem B4631453 : Blo 2057435 4631453 := bbase (se 3 (by rfl) ⟨868397, by rfl⟩ : syracuseStep 4631453 = 1736795) (by norm_num)
theorem B3087635 : Blo 2057435 3087635 := bstep (se 1 (by rfl) ⟨2315726, by rfl⟩ : syracuseStep 3087635 = 4631453) B4631453
theorem B2058423 : Blo 2057435 2058423 := bstep (se 1 (by rfl) ⟨1543817, by rfl⟩ : syracuseStep 2058423 = 3087635) B3087635
theorem B3473597 : Blo 2057435 3473597 := bbase (se 3 (by rfl) ⟨651299, by rfl⟩ : syracuseStep 3473597 = 1302599) (by norm_num)
theorem B2315731 : Blo 2057435 2315731 := bstep (se 1 (by rfl) ⟨1736798, by rfl⟩ : syracuseStep 2315731 = 3473597) B3473597
theorem B3087641 : Blo 2057435 3087641 := bstep (se 2 (by rfl) ⟨1157865, by rfl⟩ : syracuseStep 3087641 = 2315731) B2315731
theorem B2058427 : Blo 2057435 2058427 := bstep (se 1 (by rfl) ⟨1543820, by rfl⟩ : syracuseStep 2058427 = 3087641) B3087641
theorem B11723413 : Blo 2057435 11723413 := bbase (se 6 (by rfl) ⟨274767, by rfl⟩ : syracuseStep 11723413 = 549535) (by norm_num)
theorem B15631217 : Blo 2057435 15631217 := bstep (se 2 (by rfl) ⟨5861706, by rfl⟩ : syracuseStep 15631217 = 11723413) B11723413
theorem B10420811 : Blo 2057435 10420811 := bstep (se 1 (by rfl) ⟨7815608, by rfl⟩ : syracuseStep 10420811 = 15631217) B15631217
theorem B6947207 : Blo 2057435 6947207 := bstep (se 1 (by rfl) ⟨5210405, by rfl⟩ : syracuseStep 6947207 = 10420811) B10420811
theorem B4631471 : Blo 2057435 4631471 := bstep (se 1 (by rfl) ⟨3473603, by rfl⟩ : syracuseStep 4631471 = 6947207) B6947207
theorem B3087647 : Blo 2057435 3087647 := bstep (se 1 (by rfl) ⟨2315735, by rfl⟩ : syracuseStep 3087647 = 4631471) B4631471
theorem B2058431 : Blo 2057435 2058431 := bstep (se 1 (by rfl) ⟨1543823, by rfl⟩ : syracuseStep 2058431 = 3087647) B3087647
theorem B3087653 : Blo 2057435 3087653 := bbase (se 4 (by rfl) ⟨289467, by rfl⟩ : syracuseStep 3087653 = 578935) (by norm_num)
theorem B2058435 : Blo 2057435 2058435 := bstep (se 1 (by rfl) ⟨1543826, by rfl⟩ : syracuseStep 2058435 = 3087653) B3087653
theorem B2605213 : Blo 2057435 2605213 := bbase (se 3 (by rfl) ⟨488477, by rfl⟩ : syracuseStep 2605213 = 976955) (by norm_num)
theorem B3473617 : Blo 2057435 3473617 := bstep (se 2 (by rfl) ⟨1302606, by rfl⟩ : syracuseStep 3473617 = 2605213) B2605213
theorem B4631489 : Blo 2057435 4631489 := bstep (se 2 (by rfl) ⟨1736808, by rfl⟩ : syracuseStep 4631489 = 3473617) B3473617
theorem B3087659 : Blo 2057435 3087659 := bstep (se 1 (by rfl) ⟨2315744, by rfl⟩ : syracuseStep 3087659 = 4631489) B4631489
theorem B2058439 : Blo 2057435 2058439 := bstep (se 1 (by rfl) ⟨1543829, by rfl⟩ : syracuseStep 2058439 = 3087659) B3087659
theorem B2315749 : Blo 2057435 2315749 := bbase (se 4 (by rfl) ⟨217101, by rfl⟩ : syracuseStep 2315749 = 434203) (by norm_num)
theorem B3087665 : Blo 2057435 3087665 := bstep (se 2 (by rfl) ⟨1157874, by rfl⟩ : syracuseStep 3087665 = 2315749) B2315749
theorem B2058443 : Blo 2057435 2058443 := bstep (se 1 (by rfl) ⟨1543832, by rfl⟩ : syracuseStep 2058443 = 3087665) B3087665
theorem B2115001 : Blo 2057435 2115001 := bbase (se 2 (by rfl) ⟨793125, by rfl⟩ : syracuseStep 2115001 = 1586251) (by norm_num)
theorem B11280005 : Blo 2057435 11280005 := bstep (se 4 (by rfl) ⟨1057500, by rfl⟩ : syracuseStep 11280005 = 2115001) B2115001
theorem B7520003 : Blo 2057435 7520003 := bstep (se 1 (by rfl) ⟨5640002, by rfl⟩ : syracuseStep 7520003 = 11280005) B11280005
theorem B5013335 : Blo 2057435 5013335 := bstep (se 1 (by rfl) ⟨3760001, by rfl⟩ : syracuseStep 5013335 = 7520003) B7520003
theorem B3342223 : Blo 2057435 3342223 := bstep (se 1 (by rfl) ⟨2506667, by rfl⟩ : syracuseStep 3342223 = 5013335) B5013335
theorem B4456297 : Blo 2057435 4456297 := bstep (se 2 (by rfl) ⟨1671111, by rfl⟩ : syracuseStep 4456297 = 3342223) B3342223
theorem B5941729 : Blo 2057435 5941729 := bstep (se 2 (by rfl) ⟨2228148, by rfl⟩ : syracuseStep 5941729 = 4456297) B4456297
theorem B7922305 : Blo 2057435 7922305 := bstep (se 2 (by rfl) ⟨2970864, by rfl⟩ : syracuseStep 7922305 = 5941729) B5941729
theorem B42252293 : Blo 2057435 42252293 := bstep (se 4 (by rfl) ⟨3961152, by rfl⟩ : syracuseStep 42252293 = 7922305) B7922305
theorem B28168195 : Blo 2057435 28168195 := bstep (se 1 (by rfl) ⟨21126146, by rfl⟩ : syracuseStep 28168195 = 42252293) B42252293
theorem B37557593 : Blo 2057435 37557593 := bstep (se 2 (by rfl) ⟨14084097, by rfl⟩ : syracuseStep 37557593 = 28168195) B28168195
theorem B25038395 : Blo 2057435 25038395 := bstep (se 1 (by rfl) ⟨18778796, by rfl⟩ : syracuseStep 25038395 = 37557593) B37557593
theorem B16692263 : Blo 2057435 16692263 := bstep (se 1 (by rfl) ⟨12519197, by rfl⟩ : syracuseStep 16692263 = 25038395) B25038395
theorem B11128175 : Blo 2057435 11128175 := bstep (se 1 (by rfl) ⟨8346131, by rfl⟩ : syracuseStep 11128175 = 16692263) B16692263
theorem B7418783 : Blo 2057435 7418783 := bstep (se 1 (by rfl) ⟨5564087, by rfl⟩ : syracuseStep 7418783 = 11128175) B11128175
theorem B4945855 : Blo 2057435 4945855 := bstep (se 1 (by rfl) ⟨3709391, by rfl⟩ : syracuseStep 4945855 = 7418783) B7418783
theorem B6594473 : Blo 2057435 6594473 := bstep (se 2 (by rfl) ⟨2472927, by rfl⟩ : syracuseStep 6594473 = 4945855) B4945855
theorem B4396315 : Blo 2057435 4396315 := bstep (se 1 (by rfl) ⟨3297236, by rfl⟩ : syracuseStep 4396315 = 6594473) B6594473
theorem B5861753 : Blo 2057435 5861753 := bstep (se 2 (by rfl) ⟨2198157, by rfl⟩ : syracuseStep 5861753 = 4396315) B4396315
theorem B3907835 : Blo 2057435 3907835 := bstep (se 1 (by rfl) ⟨2930876, by rfl⟩ : syracuseStep 3907835 = 5861753) B5861753
theorem B2605223 : Blo 2057435 2605223 := bstep (se 1 (by rfl) ⟨1953917, by rfl⟩ : syracuseStep 2605223 = 3907835) B3907835
theorem B6947261 : Blo 2057435 6947261 := bstep (se 3 (by rfl) ⟨1302611, by rfl⟩ : syracuseStep 6947261 = 2605223) B2605223
theorem B4631507 : Blo 2057435 4631507 := bstep (se 1 (by rfl) ⟨3473630, by rfl⟩ : syracuseStep 4631507 = 6947261) B6947261
theorem B3087671 : Blo 2057435 3087671 := bstep (se 1 (by rfl) ⟨2315753, by rfl⟩ : syracuseStep 3087671 = 4631507) B4631507
theorem B2058447 : Blo 2057435 2058447 := bstep (se 1 (by rfl) ⟨1543835, by rfl⟩ : syracuseStep 2058447 = 3087671) B3087671
theorem B3087677 : Blo 2057435 3087677 := bbase (se 3 (by rfl) ⟨578939, by rfl⟩ : syracuseStep 3087677 = 1157879) (by norm_num)
theorem B2058451 : Blo 2057435 2058451 := bstep (se 1 (by rfl) ⟨1543838, by rfl⟩ : syracuseStep 2058451 = 3087677) B3087677
theorem B4631525 : Blo 2057435 4631525 := bbase (se 4 (by rfl) ⟨434205, by rfl⟩ : syracuseStep 4631525 = 868411) (by norm_num)
theorem B3087683 : Blo 2057435 3087683 := bstep (se 1 (by rfl) ⟨2315762, by rfl⟩ : syracuseStep 3087683 = 4631525) B4631525
theorem B2058455 : Blo 2057435 2058455 := bstep (se 1 (by rfl) ⟨1543841, by rfl⟩ : syracuseStep 2058455 = 3087683) B3087683
theorem B5210477 : Blo 2057435 5210477 := bbase (se 3 (by rfl) ⟨976964, by rfl⟩ : syracuseStep 5210477 = 1953929) (by norm_num)
theorem B3473651 : Blo 2057435 3473651 := bstep (se 1 (by rfl) ⟨2605238, by rfl⟩ : syracuseStep 3473651 = 5210477) B5210477
theorem B2315767 : Blo 2057435 2315767 := bstep (se 1 (by rfl) ⟨1736825, by rfl⟩ : syracuseStep 2315767 = 3473651) B3473651
theorem B3087689 : Blo 2057435 3087689 := bstep (se 2 (by rfl) ⟨1157883, by rfl⟩ : syracuseStep 3087689 = 2315767) B2315767
theorem B2058459 : Blo 2057435 2058459 := bstep (se 1 (by rfl) ⟨1543844, by rfl⟩ : syracuseStep 2058459 = 3087689) B3087689
theorem B4396349 : Blo 2057435 4396349 := bbase (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) (by norm_num)
theorem B2930899 : Blo 2057435 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B3907865 : Blo 2057435 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B10420973 : Blo 2057435 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B6947315 : Blo 2057435 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B4631543 : Blo 2057435 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B3087695 : Blo 2057435 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B2058463 : Blo 2057435 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B3087701 : Blo 2057435 3087701 := bbase (se 11 (by rfl) ⟨2261, by rfl⟩ : syracuseStep 3087701 = 4523) (by norm_num)
theorem B2058467 : Blo 2057435 2058467 := bstep (se 1 (by rfl) ⟨1543850, by rfl⟩ : syracuseStep 2058467 = 3087701) B3087701
theorem B7042133 : Blo 2057435 7042133 := bbase (se 8 (by rfl) ⟨41262, by rfl⟩ : syracuseStep 7042133 = 82525) (by norm_num)
theorem B4694755 : Blo 2057435 4694755 := bstep (se 1 (by rfl) ⟨3521066, by rfl⟩ : syracuseStep 4694755 = 7042133) B7042133
theorem B6259673 : Blo 2057435 6259673 := bstep (se 2 (by rfl) ⟨2347377, by rfl⟩ : syracuseStep 6259673 = 4694755) B4694755
theorem B4173115 : Blo 2057435 4173115 := bstep (se 1 (by rfl) ⟨3129836, by rfl⟩ : syracuseStep 4173115 = 6259673) B6259673
theorem B5564153 : Blo 2057435 5564153 := bstep (se 2 (by rfl) ⟨2086557, by rfl⟩ : syracuseStep 5564153 = 4173115) B4173115
theorem B3709435 : Blo 2057435 3709435 := bstep (se 1 (by rfl) ⟨2782076, by rfl⟩ : syracuseStep 3709435 = 5564153) B5564153
theorem B4945913 : Blo 2057435 4945913 := bstep (se 2 (by rfl) ⟨1854717, by rfl⟩ : syracuseStep 4945913 = 3709435) B3709435
theorem B3297275 : Blo 2057435 3297275 := bstep (se 1 (by rfl) ⟨2472956, by rfl⟩ : syracuseStep 3297275 = 4945913) B4945913
theorem B2198183 : Blo 2057435 2198183 := bstep (se 1 (by rfl) ⟨1648637, by rfl⟩ : syracuseStep 2198183 = 3297275) B3297275
theorem B5861821 : Blo 2057435 5861821 := bstep (se 3 (by rfl) ⟨1099091, by rfl⟩ : syracuseStep 5861821 = 2198183) B2198183
theorem B7815761 : Blo 2057435 7815761 := bstep (se 2 (by rfl) ⟨2930910, by rfl⟩ : syracuseStep 7815761 = 5861821) B5861821
theorem B5210507 : Blo 2057435 5210507 := bstep (se 1 (by rfl) ⟨3907880, by rfl⟩ : syracuseStep 5210507 = 7815761) B7815761
theorem B3473671 : Blo 2057435 3473671 := bstep (se 1 (by rfl) ⟨2605253, by rfl⟩ : syracuseStep 3473671 = 5210507) B5210507
theorem B4631561 : Blo 2057435 4631561 := bstep (se 2 (by rfl) ⟨1736835, by rfl⟩ : syracuseStep 4631561 = 3473671) B3473671
theorem B3087707 : Blo 2057435 3087707 := bstep (se 1 (by rfl) ⟨2315780, by rfl⟩ : syracuseStep 3087707 = 4631561) B4631561
theorem B2058471 : Blo 2057435 2058471 := bstep (se 1 (by rfl) ⟨1543853, by rfl⟩ : syracuseStep 2058471 = 3087707) B3087707
theorem B2315785 : Blo 2057435 2315785 := bbase (se 2 (by rfl) ⟨868419, by rfl⟩ : syracuseStep 2315785 = 1736839) (by norm_num)
theorem B3087713 : Blo 2057435 3087713 := bstep (se 2 (by rfl) ⟨1157892, by rfl⟩ : syracuseStep 3087713 = 2315785) B2315785
theorem B2058475 : Blo 2057435 2058475 := bstep (se 1 (by rfl) ⟨1543856, by rfl⟩ : syracuseStep 2058475 = 3087713) B3087713
theorem B2640809 : Blo 2057435 2640809 := bbase (se 2 (by rfl) ⟨990303, by rfl⟩ : syracuseStep 2640809 = 1980607) (by norm_num)
theorem B7042157 : Blo 2057435 7042157 := bstep (se 3 (by rfl) ⟨1320404, by rfl⟩ : syracuseStep 7042157 = 2640809) B2640809
theorem B4694771 : Blo 2057435 4694771 := bstep (se 1 (by rfl) ⟨3521078, by rfl⟩ : syracuseStep 4694771 = 7042157) B7042157
theorem B3129847 : Blo 2057435 3129847 := bstep (se 1 (by rfl) ⟨2347385, by rfl⟩ : syracuseStep 3129847 = 4694771) B4694771
theorem B16692517 : Blo 2057435 16692517 := bstep (se 4 (by rfl) ⟨1564923, by rfl⟩ : syracuseStep 16692517 = 3129847) B3129847
theorem B22256689 : Blo 2057435 22256689 := bstep (se 2 (by rfl) ⟨8346258, by rfl⟩ : syracuseStep 22256689 = 16692517) B16692517
theorem B29675585 : Blo 2057435 29675585 := bstep (se 2 (by rfl) ⟨11128344, by rfl⟩ : syracuseStep 29675585 = 22256689) B22256689
theorem B19783723 : Blo 2057435 19783723 := bstep (se 1 (by rfl) ⟨14837792, by rfl⟩ : syracuseStep 19783723 = 29675585) B29675585
theorem B26378297 : Blo 2057435 26378297 := bstep (se 2 (by rfl) ⟨9891861, by rfl⟩ : syracuseStep 26378297 = 19783723) B19783723
theorem B17585531 : Blo 2057435 17585531 := bstep (se 1 (by rfl) ⟨13189148, by rfl⟩ : syracuseStep 17585531 = 26378297) B26378297
theorem B11723687 : Blo 2057435 11723687 := bstep (se 1 (by rfl) ⟨8792765, by rfl⟩ : syracuseStep 11723687 = 17585531) B17585531
theorem B7815791 : Blo 2057435 7815791 := bstep (se 1 (by rfl) ⟨5861843, by rfl⟩ : syracuseStep 7815791 = 11723687) B11723687
theorem B5210527 : Blo 2057435 5210527 := bstep (se 1 (by rfl) ⟨3907895, by rfl⟩ : syracuseStep 5210527 = 7815791) B7815791
theorem B6947369 : Blo 2057435 6947369 := bstep (se 2 (by rfl) ⟨2605263, by rfl⟩ : syracuseStep 6947369 = 5210527) B5210527
theorem B4631579 : Blo 2057435 4631579 := bstep (se 1 (by rfl) ⟨3473684, by rfl⟩ : syracuseStep 4631579 = 6947369) B6947369
theorem B3087719 : Blo 2057435 3087719 := bstep (se 1 (by rfl) ⟨2315789, by rfl⟩ : syracuseStep 3087719 = 4631579) B4631579
theorem B2058479 : Blo 2057435 2058479 := bstep (se 1 (by rfl) ⟨1543859, by rfl⟩ : syracuseStep 2058479 = 3087719) B3087719
theorem B3087725 : Blo 2057435 3087725 := bbase (se 3 (by rfl) ⟨578948, by rfl⟩ : syracuseStep 3087725 = 1157897) (by norm_num)
theorem B2058483 : Blo 2057435 2058483 := bstep (se 1 (by rfl) ⟨1543862, by rfl⟩ : syracuseStep 2058483 = 3087725) B3087725
theorem B4631597 : Blo 2057435 4631597 := bbase (se 3 (by rfl) ⟨868424, by rfl⟩ : syracuseStep 4631597 = 1736849) (by norm_num)
theorem B3087731 : Blo 2057435 3087731 := bstep (se 1 (by rfl) ⟨2315798, by rfl⟩ : syracuseStep 3087731 = 4631597) B4631597
theorem B2058487 : Blo 2057435 2058487 := bstep (se 1 (by rfl) ⟨1543865, by rfl⟩ : syracuseStep 2058487 = 3087731) B3087731
theorem B10563301 : Blo 2057435 10563301 := bbase (se 4 (by rfl) ⟨990309, by rfl⟩ : syracuseStep 10563301 = 1980619) (by norm_num)
theorem B14084401 : Blo 2057435 14084401 := bstep (se 2 (by rfl) ⟨5281650, by rfl⟩ : syracuseStep 14084401 = 10563301) B10563301
theorem B18779201 : Blo 2057435 18779201 := bstep (se 2 (by rfl) ⟨7042200, by rfl⟩ : syracuseStep 18779201 = 14084401) B14084401
theorem B12519467 : Blo 2057435 12519467 := bstep (se 1 (by rfl) ⟨9389600, by rfl⟩ : syracuseStep 12519467 = 18779201) B18779201
theorem B8346311 : Blo 2057435 8346311 := bstep (se 1 (by rfl) ⟨6259733, by rfl⟩ : syracuseStep 8346311 = 12519467) B12519467
theorem B5564207 : Blo 2057435 5564207 := bstep (se 1 (by rfl) ⟨4173155, by rfl⟩ : syracuseStep 5564207 = 8346311) B8346311
theorem B3709471 : Blo 2057435 3709471 := bstep (se 1 (by rfl) ⟨2782103, by rfl⟩ : syracuseStep 3709471 = 5564207) B5564207
theorem B4945961 : Blo 2057435 4945961 := bstep (se 2 (by rfl) ⟨1854735, by rfl⟩ : syracuseStep 4945961 = 3709471) B3709471
theorem B13189229 : Blo 2057435 13189229 := bstep (se 3 (by rfl) ⟨2472980, by rfl⟩ : syracuseStep 13189229 = 4945961) B4945961
theorem B8792819 : Blo 2057435 8792819 := bstep (se 1 (by rfl) ⟨6594614, by rfl⟩ : syracuseStep 8792819 = 13189229) B13189229
theorem B5861879 : Blo 2057435 5861879 := bstep (se 1 (by rfl) ⟨4396409, by rfl⟩ : syracuseStep 5861879 = 8792819) B8792819
theorem B3907919 : Blo 2057435 3907919 := bstep (se 1 (by rfl) ⟨2930939, by rfl⟩ : syracuseStep 3907919 = 5861879) B5861879
theorem B2605279 : Blo 2057435 2605279 := bstep (se 1 (by rfl) ⟨1953959, by rfl⟩ : syracuseStep 2605279 = 3907919) B3907919
theorem B3473705 : Blo 2057435 3473705 := bstep (se 2 (by rfl) ⟨1302639, by rfl⟩ : syracuseStep 3473705 = 2605279) B2605279
theorem B2315803 : Blo 2057435 2315803 := bstep (se 1 (by rfl) ⟨1736852, by rfl⟩ : syracuseStep 2315803 = 3473705) B3473705
theorem B3087737 : Blo 2057435 3087737 := bstep (se 2 (by rfl) ⟨1157901, by rfl⟩ : syracuseStep 3087737 = 2315803) B2315803
theorem B2058491 : Blo 2057435 2058491 := bstep (se 1 (by rfl) ⟨1543868, by rfl⟩ : syracuseStep 2058491 = 3087737) B3087737
theorem B3709477 : Blo 2057435 3709477 := bbase (se 4 (by rfl) ⟨347763, by rfl⟩ : syracuseStep 3709477 = 695527) (by norm_num)
theorem B4945969 : Blo 2057435 4945969 := bstep (se 2 (by rfl) ⟨1854738, by rfl⟩ : syracuseStep 4945969 = 3709477) B3709477
theorem B6594625 : Blo 2057435 6594625 := bstep (se 2 (by rfl) ⟨2472984, by rfl⟩ : syracuseStep 6594625 = 4945969) B4945969
theorem B35171333 : Blo 2057435 35171333 := bstep (se 4 (by rfl) ⟨3297312, by rfl⟩ : syracuseStep 35171333 = 6594625) B6594625
theorem B23447555 : Blo 2057435 23447555 := bstep (se 1 (by rfl) ⟨17585666, by rfl⟩ : syracuseStep 23447555 = 35171333) B35171333
theorem B15631703 : Blo 2057435 15631703 := bstep (se 1 (by rfl) ⟨11723777, by rfl⟩ : syracuseStep 15631703 = 23447555) B23447555
theorem B10421135 : Blo 2057435 10421135 := bstep (se 1 (by rfl) ⟨7815851, by rfl⟩ : syracuseStep 10421135 = 15631703) B15631703
theorem B6947423 : Blo 2057435 6947423 := bstep (se 1 (by rfl) ⟨5210567, by rfl⟩ : syracuseStep 6947423 = 10421135) B10421135
theorem B4631615 : Blo 2057435 4631615 := bstep (se 1 (by rfl) ⟨3473711, by rfl⟩ : syracuseStep 4631615 = 6947423) B6947423
theorem B3087743 : Blo 2057435 3087743 := bstep (se 1 (by rfl) ⟨2315807, by rfl⟩ : syracuseStep 3087743 = 4631615) B4631615
theorem B2058495 : Blo 2057435 2058495 := bstep (se 1 (by rfl) ⟨1543871, by rfl⟩ : syracuseStep 2058495 = 3087743) B3087743
theorem B3087749 : Blo 2057435 3087749 := bbase (se 4 (by rfl) ⟨289476, by rfl⟩ : syracuseStep 3087749 = 578953) (by norm_num)
theorem B2058499 : Blo 2057435 2058499 := bstep (se 1 (by rfl) ⟨1543874, by rfl⟩ : syracuseStep 2058499 = 3087749) B3087749
theorem B3473725 : Blo 2057435 3473725 := bbase (se 3 (by rfl) ⟨651323, by rfl⟩ : syracuseStep 3473725 = 1302647) (by norm_num)
theorem B4631633 : Blo 2057435 4631633 := bstep (se 2 (by rfl) ⟨1736862, by rfl⟩ : syracuseStep 4631633 = 3473725) B3473725
theorem B3087755 : Blo 2057435 3087755 := bstep (se 1 (by rfl) ⟨2315816, by rfl⟩ : syracuseStep 3087755 = 4631633) B4631633
theorem B2058503 : Blo 2057435 2058503 := bstep (se 1 (by rfl) ⟨1543877, by rfl⟩ : syracuseStep 2058503 = 3087755) B3087755
theorem B2315821 : Blo 2057435 2315821 := bbase (se 3 (by rfl) ⟨434216, by rfl⟩ : syracuseStep 2315821 = 868433) (by norm_num)
theorem B3087761 : Blo 2057435 3087761 := bstep (se 2 (by rfl) ⟨1157910, by rfl⟩ : syracuseStep 3087761 = 2315821) B2315821
theorem B2058507 : Blo 2057435 2058507 := bstep (se 1 (by rfl) ⟨1543880, by rfl⟩ : syracuseStep 2058507 = 3087761) B3087761
theorem B6947477 : Blo 2057435 6947477 := bbase (se 6 (by rfl) ⟨162831, by rfl⟩ : syracuseStep 6947477 = 325663) (by norm_num)
theorem B4631651 : Blo 2057435 4631651 := bstep (se 1 (by rfl) ⟨3473738, by rfl⟩ : syracuseStep 4631651 = 6947477) B6947477
theorem B3087767 : Blo 2057435 3087767 := bstep (se 1 (by rfl) ⟨2315825, by rfl⟩ : syracuseStep 3087767 = 4631651) B4631651
theorem B2058511 : Blo 2057435 2058511 := bstep (se 1 (by rfl) ⟨1543883, by rfl⟩ : syracuseStep 2058511 = 3087767) B3087767
theorem B3087773 : Blo 2057435 3087773 := bbase (se 3 (by rfl) ⟨578957, by rfl⟩ : syracuseStep 3087773 = 1157915) (by norm_num)
theorem B2058515 : Blo 2057435 2058515 := bstep (se 1 (by rfl) ⟨1543886, by rfl⟩ : syracuseStep 2058515 = 3087773) B3087773
theorem B4631669 : Blo 2057435 4631669 := bbase (se 5 (by rfl) ⟨217109, by rfl⟩ : syracuseStep 4631669 = 434219) (by norm_num)
theorem B3087779 : Blo 2057435 3087779 := bstep (se 1 (by rfl) ⟨2315834, by rfl⟩ : syracuseStep 3087779 = 4631669) B4631669
theorem B2058519 : Blo 2057435 2058519 := bstep (se 1 (by rfl) ⟨1543889, by rfl⟩ : syracuseStep 2058519 = 3087779) B3087779
theorem B17585909 : Blo 2057435 17585909 := bbase (se 5 (by rfl) ⟨824339, by rfl⟩ : syracuseStep 17585909 = 1648679) (by norm_num)
theorem B11723939 : Blo 2057435 11723939 := bstep (se 1 (by rfl) ⟨8792954, by rfl⟩ : syracuseStep 11723939 = 17585909) B17585909
theorem B7815959 : Blo 2057435 7815959 := bstep (se 1 (by rfl) ⟨5861969, by rfl⟩ : syracuseStep 7815959 = 11723939) B11723939
theorem B5210639 : Blo 2057435 5210639 := bstep (se 1 (by rfl) ⟨3907979, by rfl⟩ : syracuseStep 5210639 = 7815959) B7815959
theorem B3473759 : Blo 2057435 3473759 := bstep (se 1 (by rfl) ⟨2605319, by rfl⟩ : syracuseStep 3473759 = 5210639) B5210639
theorem B2315839 : Blo 2057435 2315839 := bstep (se 1 (by rfl) ⟨1736879, by rfl⟩ : syracuseStep 2315839 = 3473759) B3473759
theorem B3087785 : Blo 2057435 3087785 := bstep (se 2 (by rfl) ⟨1157919, by rfl⟩ : syracuseStep 3087785 = 2315839) B2315839
theorem B2058523 : Blo 2057435 2058523 := bstep (se 1 (by rfl) ⟨1543892, by rfl⟩ : syracuseStep 2058523 = 3087785) B3087785
theorem B7815973 : Blo 2057435 7815973 := bbase (se 4 (by rfl) ⟨732747, by rfl⟩ : syracuseStep 7815973 = 1465495) (by norm_num)
theorem B10421297 : Blo 2057435 10421297 := bstep (se 2 (by rfl) ⟨3907986, by rfl⟩ : syracuseStep 10421297 = 7815973) B7815973
theorem B6947531 : Blo 2057435 6947531 := bstep (se 1 (by rfl) ⟨5210648, by rfl⟩ : syracuseStep 6947531 = 10421297) B10421297
theorem B4631687 : Blo 2057435 4631687 := bstep (se 1 (by rfl) ⟨3473765, by rfl⟩ : syracuseStep 4631687 = 6947531) B6947531
theorem B3087791 : Blo 2057435 3087791 := bstep (se 1 (by rfl) ⟨2315843, by rfl⟩ : syracuseStep 3087791 = 4631687) B4631687
theorem B2058527 : Blo 2057435 2058527 := bstep (se 1 (by rfl) ⟨1543895, by rfl⟩ : syracuseStep 2058527 = 3087791) B3087791
theorem B3087797 : Blo 2057435 3087797 := bbase (se 5 (by rfl) ⟨144740, by rfl⟩ : syracuseStep 3087797 = 289481) (by norm_num)
theorem B2058531 : Blo 2057435 2058531 := bstep (se 1 (by rfl) ⟨1543898, by rfl⟩ : syracuseStep 2058531 = 3087797) B3087797
theorem B5210669 : Blo 2057435 5210669 := bbase (se 3 (by rfl) ⟨977000, by rfl⟩ : syracuseStep 5210669 = 1954001) (by norm_num)
theorem B3473779 : Blo 2057435 3473779 := bstep (se 1 (by rfl) ⟨2605334, by rfl⟩ : syracuseStep 3473779 = 5210669) B5210669
theorem B4631705 : Blo 2057435 4631705 := bstep (se 2 (by rfl) ⟨1736889, by rfl⟩ : syracuseStep 4631705 = 3473779) B3473779
theorem B3087803 : Blo 2057435 3087803 := bstep (se 1 (by rfl) ⟨2315852, by rfl⟩ : syracuseStep 3087803 = 4631705) B4631705
theorem B2058535 : Blo 2057435 2058535 := bstep (se 1 (by rfl) ⟨1543901, by rfl⟩ : syracuseStep 2058535 = 3087803) B3087803
theorem B2315857 : Blo 2057435 2315857 := bbase (se 2 (by rfl) ⟨868446, by rfl⟩ : syracuseStep 2315857 = 1736893) (by norm_num)
theorem B3087809 : Blo 2057435 3087809 := bstep (se 2 (by rfl) ⟨1157928, by rfl⟩ : syracuseStep 3087809 = 2315857) B2315857
theorem B2058539 : Blo 2057435 2058539 := bstep (se 1 (by rfl) ⟨1543904, by rfl⟩ : syracuseStep 2058539 = 3087809) B3087809
theorem B2931013 : Blo 2057435 2931013 := bbase (se 4 (by rfl) ⟨274782, by rfl⟩ : syracuseStep 2931013 = 549565) (by norm_num)
theorem B3908017 : Blo 2057435 3908017 := bstep (se 2 (by rfl) ⟨1465506, by rfl⟩ : syracuseStep 3908017 = 2931013) B2931013
theorem B5210689 : Blo 2057435 5210689 := bstep (se 2 (by rfl) ⟨1954008, by rfl⟩ : syracuseStep 5210689 = 3908017) B3908017
theorem B6947585 : Blo 2057435 6947585 := bstep (se 2 (by rfl) ⟨2605344, by rfl⟩ : syracuseStep 6947585 = 5210689) B5210689
theorem B4631723 : Blo 2057435 4631723 := bstep (se 1 (by rfl) ⟨3473792, by rfl⟩ : syracuseStep 4631723 = 6947585) B6947585
theorem B3087815 : Blo 2057435 3087815 := bstep (se 1 (by rfl) ⟨2315861, by rfl⟩ : syracuseStep 3087815 = 4631723) B4631723
theorem B2058543 : Blo 2057435 2058543 := bstep (se 1 (by rfl) ⟨1543907, by rfl⟩ : syracuseStep 2058543 = 3087815) B3087815
theorem B3087821 : Blo 2057435 3087821 := bbase (se 3 (by rfl) ⟨578966, by rfl⟩ : syracuseStep 3087821 = 1157933) (by norm_num)
theorem B2058547 : Blo 2057435 2058547 := bstep (se 1 (by rfl) ⟨1543910, by rfl⟩ : syracuseStep 2058547 = 3087821) B3087821
theorem B4631741 : Blo 2057435 4631741 := bbase (se 3 (by rfl) ⟨868451, by rfl⟩ : syracuseStep 4631741 = 1736903) (by norm_num)
theorem B3087827 : Blo 2057435 3087827 := bstep (se 1 (by rfl) ⟨2315870, by rfl⟩ : syracuseStep 3087827 = 4631741) B4631741
theorem B2058551 : Blo 2057435 2058551 := bstep (se 1 (by rfl) ⟨1543913, by rfl⟩ : syracuseStep 2058551 = 3087827) B3087827
theorem B3473813 : Blo 2057435 3473813 := bbase (se 6 (by rfl) ⟨81417, by rfl⟩ : syracuseStep 3473813 = 162835) (by norm_num)
theorem B2315875 : Blo 2057435 2315875 := bstep (se 1 (by rfl) ⟨1736906, by rfl⟩ : syracuseStep 2315875 = 3473813) B3473813
theorem B3087833 : Blo 2057435 3087833 := bstep (se 2 (by rfl) ⟨1157937, by rfl⟩ : syracuseStep 3087833 = 2315875) B2315875
theorem B2058555 : Blo 2057435 2058555 := bstep (se 1 (by rfl) ⟨1543916, by rfl⟩ : syracuseStep 2058555 = 3087833) B3087833
theorem B5564389 : Blo 2057435 5564389 := bbase (se 4 (by rfl) ⟨521661, by rfl⟩ : syracuseStep 5564389 = 1043323) (by norm_num)
theorem B7419185 : Blo 2057435 7419185 := bstep (se 2 (by rfl) ⟨2782194, by rfl⟩ : syracuseStep 7419185 = 5564389) B5564389
theorem B4946123 : Blo 2057435 4946123 := bstep (se 1 (by rfl) ⟨3709592, by rfl⟩ : syracuseStep 4946123 = 7419185) B7419185
theorem B13189661 : Blo 2057435 13189661 := bstep (se 3 (by rfl) ⟨2473061, by rfl⟩ : syracuseStep 13189661 = 4946123) B4946123
theorem B8793107 : Blo 2057435 8793107 := bstep (se 1 (by rfl) ⟨6594830, by rfl⟩ : syracuseStep 8793107 = 13189661) B13189661
theorem B5862071 : Blo 2057435 5862071 := bstep (se 1 (by rfl) ⟨4396553, by rfl⟩ : syracuseStep 5862071 = 8793107) B8793107
theorem B15632189 : Blo 2057435 15632189 := bstep (se 3 (by rfl) ⟨2931035, by rfl⟩ : syracuseStep 15632189 = 5862071) B5862071
theorem B10421459 : Blo 2057435 10421459 := bstep (se 1 (by rfl) ⟨7816094, by rfl⟩ : syracuseStep 10421459 = 15632189) B15632189
theorem B6947639 : Blo 2057435 6947639 := bstep (se 1 (by rfl) ⟨5210729, by rfl⟩ : syracuseStep 6947639 = 10421459) B10421459
theorem B4631759 : Blo 2057435 4631759 := bstep (se 1 (by rfl) ⟨3473819, by rfl⟩ : syracuseStep 4631759 = 6947639) B6947639
theorem B3087839 : Blo 2057435 3087839 := bstep (se 1 (by rfl) ⟨2315879, by rfl⟩ : syracuseStep 3087839 = 4631759) B4631759
theorem B2058559 : Blo 2057435 2058559 := bstep (se 1 (by rfl) ⟨1543919, by rfl⟩ : syracuseStep 2058559 = 3087839) B3087839
theorem B3087845 : Blo 2057435 3087845 := bbase (se 4 (by rfl) ⟨289485, by rfl⟩ : syracuseStep 3087845 = 578971) (by norm_num)
theorem B2058563 : Blo 2057435 2058563 := bstep (se 1 (by rfl) ⟨1543922, by rfl⟩ : syracuseStep 2058563 = 3087845) B3087845
theorem B10027253 : Blo 2057435 10027253 := bbase (se 5 (by rfl) ⟨470027, by rfl⟩ : syracuseStep 10027253 = 940055) (by norm_num)
theorem B26739341 : Blo 2057435 26739341 := bstep (se 3 (by rfl) ⟨5013626, by rfl⟩ : syracuseStep 26739341 = 10027253) B10027253
theorem B17826227 : Blo 2057435 17826227 := bstep (se 1 (by rfl) ⟨13369670, by rfl⟩ : syracuseStep 17826227 = 26739341) B26739341
theorem B11884151 : Blo 2057435 11884151 := bstep (se 1 (by rfl) ⟨8913113, by rfl⟩ : syracuseStep 11884151 = 17826227) B17826227
theorem B7922767 : Blo 2057435 7922767 := bstep (se 1 (by rfl) ⟨5942075, by rfl⟩ : syracuseStep 7922767 = 11884151) B11884151
theorem B10563689 : Blo 2057435 10563689 := bstep (se 2 (by rfl) ⟨3961383, by rfl⟩ : syracuseStep 10563689 = 7922767) B7922767
theorem B7042459 : Blo 2057435 7042459 := bstep (se 1 (by rfl) ⟨5281844, by rfl⟩ : syracuseStep 7042459 = 10563689) B10563689
theorem B9389945 : Blo 2057435 9389945 := bstep (se 2 (by rfl) ⟨3521229, by rfl⟩ : syracuseStep 9389945 = 7042459) B7042459
theorem B25039853 : Blo 2057435 25039853 := bstep (se 3 (by rfl) ⟨4694972, by rfl⟩ : syracuseStep 25039853 = 9389945) B9389945
theorem B16693235 : Blo 2057435 16693235 := bstep (se 1 (by rfl) ⟨12519926, by rfl⟩ : syracuseStep 16693235 = 25039853) B25039853
theorem B11128823 : Blo 2057435 11128823 := bstep (se 1 (by rfl) ⟨8346617, by rfl⟩ : syracuseStep 11128823 = 16693235) B16693235
theorem B7419215 : Blo 2057435 7419215 := bstep (se 1 (by rfl) ⟨5564411, by rfl⟩ : syracuseStep 7419215 = 11128823) B11128823
theorem B19784573 : Blo 2057435 19784573 := bstep (se 3 (by rfl) ⟨3709607, by rfl⟩ : syracuseStep 19784573 = 7419215) B7419215
theorem B13189715 : Blo 2057435 13189715 := bstep (se 1 (by rfl) ⟨9892286, by rfl⟩ : syracuseStep 13189715 = 19784573) B19784573
theorem B8793143 : Blo 2057435 8793143 := bstep (se 1 (by rfl) ⟨6594857, by rfl⟩ : syracuseStep 8793143 = 13189715) B13189715
theorem B5862095 : Blo 2057435 5862095 := bstep (se 1 (by rfl) ⟨4396571, by rfl⟩ : syracuseStep 5862095 = 8793143) B8793143
theorem B3908063 : Blo 2057435 3908063 := bstep (se 1 (by rfl) ⟨2931047, by rfl⟩ : syracuseStep 3908063 = 5862095) B5862095
theorem B2605375 : Blo 2057435 2605375 := bstep (se 1 (by rfl) ⟨1954031, by rfl⟩ : syracuseStep 2605375 = 3908063) B3908063
theorem B3473833 : Blo 2057435 3473833 := bstep (se 2 (by rfl) ⟨1302687, by rfl⟩ : syracuseStep 3473833 = 2605375) B2605375
theorem B4631777 : Blo 2057435 4631777 := bstep (se 2 (by rfl) ⟨1736916, by rfl⟩ : syracuseStep 4631777 = 3473833) B3473833
theorem B3087851 : Blo 2057435 3087851 := bstep (se 1 (by rfl) ⟨2315888, by rfl⟩ : syracuseStep 3087851 = 4631777) B4631777
theorem B2058567 : Blo 2057435 2058567 := bstep (se 1 (by rfl) ⟨1543925, by rfl⟩ : syracuseStep 2058567 = 3087851) B3087851
theorem B2315893 : Blo 2057435 2315893 := bbase (se 5 (by rfl) ⟨108557, by rfl⟩ : syracuseStep 2315893 = 217115) (by norm_num)
theorem B3087857 : Blo 2057435 3087857 := bstep (se 2 (by rfl) ⟨1157946, by rfl⟩ : syracuseStep 3087857 = 2315893) B2315893
theorem B2058571 : Blo 2057435 2058571 := bstep (se 1 (by rfl) ⟨1543928, by rfl⟩ : syracuseStep 2058571 = 3087857) B3087857
theorem B2605385 : Blo 2057435 2605385 := bbase (se 2 (by rfl) ⟨977019, by rfl⟩ : syracuseStep 2605385 = 1954039) (by norm_num)
theorem B6947693 : Blo 2057435 6947693 := bstep (se 3 (by rfl) ⟨1302692, by rfl⟩ : syracuseStep 6947693 = 2605385) B2605385
theorem B4631795 : Blo 2057435 4631795 := bstep (se 1 (by rfl) ⟨3473846, by rfl⟩ : syracuseStep 4631795 = 6947693) B6947693
theorem B3087863 : Blo 2057435 3087863 := bstep (se 1 (by rfl) ⟨2315897, by rfl⟩ : syracuseStep 3087863 = 4631795) B4631795
theorem B2058575 : Blo 2057435 2058575 := bstep (se 1 (by rfl) ⟨1543931, by rfl⟩ : syracuseStep 2058575 = 3087863) B3087863
theorem B3087869 : Blo 2057435 3087869 := bbase (se 3 (by rfl) ⟨578975, by rfl⟩ : syracuseStep 3087869 = 1157951) (by norm_num)
theorem B2058579 : Blo 2057435 2058579 := bstep (se 1 (by rfl) ⟨1543934, by rfl⟩ : syracuseStep 2058579 = 3087869) B3087869
theorem B4631813 : Blo 2057435 4631813 := bbase (se 4 (by rfl) ⟨434232, by rfl⟩ : syracuseStep 4631813 = 868465) (by norm_num)
theorem B3087875 : Blo 2057435 3087875 := bstep (se 1 (by rfl) ⟨2315906, by rfl⟩ : syracuseStep 3087875 = 4631813) B4631813
theorem B2058583 : Blo 2057435 2058583 := bstep (se 1 (by rfl) ⟨1543937, by rfl⟩ : syracuseStep 2058583 = 3087875) B3087875
theorem B3908101 : Blo 2057435 3908101 := bbase (se 4 (by rfl) ⟨366384, by rfl⟩ : syracuseStep 3908101 = 732769) (by norm_num)
theorem B5210801 : Blo 2057435 5210801 := bstep (se 2 (by rfl) ⟨1954050, by rfl⟩ : syracuseStep 5210801 = 3908101) B3908101
theorem B3473867 : Blo 2057435 3473867 := bstep (se 1 (by rfl) ⟨2605400, by rfl⟩ : syracuseStep 3473867 = 5210801) B5210801
theorem B2315911 : Blo 2057435 2315911 := bstep (se 1 (by rfl) ⟨1736933, by rfl⟩ : syracuseStep 2315911 = 3473867) B3473867
theorem B3087881 : Blo 2057435 3087881 := bstep (se 2 (by rfl) ⟨1157955, by rfl⟩ : syracuseStep 3087881 = 2315911) B2315911
theorem B2058587 : Blo 2057435 2058587 := bstep (se 1 (by rfl) ⟨1543940, by rfl⟩ : syracuseStep 2058587 = 3087881) B3087881
theorem B10421621 : Blo 2057435 10421621 := bbase (se 5 (by rfl) ⟨488513, by rfl⟩ : syracuseStep 10421621 = 977027) (by norm_num)
theorem B6947747 : Blo 2057435 6947747 := bstep (se 1 (by rfl) ⟨5210810, by rfl⟩ : syracuseStep 6947747 = 10421621) B10421621
theorem B4631831 : Blo 2057435 4631831 := bstep (se 1 (by rfl) ⟨3473873, by rfl⟩ : syracuseStep 4631831 = 6947747) B6947747
theorem B3087887 : Blo 2057435 3087887 := bstep (se 1 (by rfl) ⟨2315915, by rfl⟩ : syracuseStep 3087887 = 4631831) B4631831
theorem B2058591 : Blo 2057435 2058591 := bstep (se 1 (by rfl) ⟨1543943, by rfl⟩ : syracuseStep 2058591 = 3087887) B3087887
theorem B3087893 : Blo 2057435 3087893 := bbase (se 6 (by rfl) ⟨72372, by rfl⟩ : syracuseStep 3087893 = 144745) (by norm_num)
theorem B2058595 : Blo 2057435 2058595 := bstep (se 1 (by rfl) ⟨1543946, by rfl⟩ : syracuseStep 2058595 = 3087893) B3087893
theorem B4173373 : Blo 2057435 4173373 := bbase (se 3 (by rfl) ⟨782507, by rfl⟩ : syracuseStep 4173373 = 1565015) (by norm_num)
theorem B22257989 : Blo 2057435 22257989 := bstep (se 4 (by rfl) ⟨2086686, by rfl⟩ : syracuseStep 22257989 = 4173373) B4173373
theorem B14838659 : Blo 2057435 14838659 := bstep (se 1 (by rfl) ⟨11128994, by rfl⟩ : syracuseStep 14838659 = 22257989) B22257989
theorem B9892439 : Blo 2057435 9892439 := bstep (se 1 (by rfl) ⟨7419329, by rfl⟩ : syracuseStep 9892439 = 14838659) B14838659
theorem B6594959 : Blo 2057435 6594959 := bstep (se 1 (by rfl) ⟨4946219, by rfl⟩ : syracuseStep 6594959 = 9892439) B9892439
theorem B17586557 : Blo 2057435 17586557 := bstep (se 3 (by rfl) ⟨3297479, by rfl⟩ : syracuseStep 17586557 = 6594959) B6594959
theorem B11724371 : Blo 2057435 11724371 := bstep (se 1 (by rfl) ⟨8793278, by rfl⟩ : syracuseStep 11724371 = 17586557) B17586557
theorem B7816247 : Blo 2057435 7816247 := bstep (se 1 (by rfl) ⟨5862185, by rfl⟩ : syracuseStep 7816247 = 11724371) B11724371
theorem B5210831 : Blo 2057435 5210831 := bstep (se 1 (by rfl) ⟨3908123, by rfl⟩ : syracuseStep 5210831 = 7816247) B7816247
theorem B3473887 : Blo 2057435 3473887 := bstep (se 1 (by rfl) ⟨2605415, by rfl⟩ : syracuseStep 3473887 = 5210831) B5210831
theorem B4631849 : Blo 2057435 4631849 := bstep (se 2 (by rfl) ⟨1736943, by rfl⟩ : syracuseStep 4631849 = 3473887) B3473887
theorem B3087899 : Blo 2057435 3087899 := bstep (se 1 (by rfl) ⟨2315924, by rfl⟩ : syracuseStep 3087899 = 4631849) B4631849
theorem B2058599 : Blo 2057435 2058599 := bstep (se 1 (by rfl) ⟨1543949, by rfl⟩ : syracuseStep 2058599 = 3087899) B3087899
theorem B2315929 : Blo 2057435 2315929 := bbase (se 2 (by rfl) ⟨868473, by rfl⟩ : syracuseStep 2315929 = 1736947) (by norm_num)
theorem B3087905 : Blo 2057435 3087905 := bstep (se 2 (by rfl) ⟨1157964, by rfl⟩ : syracuseStep 3087905 = 2315929) B2315929
theorem B2058603 : Blo 2057435 2058603 := bstep (se 1 (by rfl) ⟨1543952, by rfl⟩ : syracuseStep 2058603 = 3087905) B3087905
theorem B7816277 : Blo 2057435 7816277 := bbase (se 8 (by rfl) ⟨45798, by rfl⟩ : syracuseStep 7816277 = 91597) (by norm_num)
theorem B5210851 : Blo 2057435 5210851 := bstep (se 1 (by rfl) ⟨3908138, by rfl⟩ : syracuseStep 5210851 = 7816277) B7816277
theorem B6947801 : Blo 2057435 6947801 := bstep (se 2 (by rfl) ⟨2605425, by rfl⟩ : syracuseStep 6947801 = 5210851) B5210851
theorem B4631867 : Blo 2057435 4631867 := bstep (se 1 (by rfl) ⟨3473900, by rfl⟩ : syracuseStep 4631867 = 6947801) B6947801
theorem B3087911 : Blo 2057435 3087911 := bstep (se 1 (by rfl) ⟨2315933, by rfl⟩ : syracuseStep 3087911 = 4631867) B4631867
theorem B2058607 : Blo 2057435 2058607 := bstep (se 1 (by rfl) ⟨1543955, by rfl⟩ : syracuseStep 2058607 = 3087911) B3087911
theorem B3087917 : Blo 2057435 3087917 := bbase (se 3 (by rfl) ⟨578984, by rfl⟩ : syracuseStep 3087917 = 1157969) (by norm_num)
theorem B2058611 : Blo 2057435 2058611 := bstep (se 1 (by rfl) ⟨1543958, by rfl⟩ : syracuseStep 2058611 = 3087917) B3087917
theorem B4631885 : Blo 2057435 4631885 := bbase (se 3 (by rfl) ⟨868478, by rfl⟩ : syracuseStep 4631885 = 1736957) (by norm_num)
theorem B3087923 : Blo 2057435 3087923 := bstep (se 1 (by rfl) ⟨2315942, by rfl⟩ : syracuseStep 3087923 = 4631885) B4631885
theorem B2058615 : Blo 2057435 2058615 := bstep (se 1 (by rfl) ⟨1543961, by rfl⟩ : syracuseStep 2058615 = 3087923) B3087923
theorem B2605441 : Blo 2057435 2605441 := bbase (se 2 (by rfl) ⟨977040, by rfl⟩ : syracuseStep 2605441 = 1954081) (by norm_num)
theorem B3473921 : Blo 2057435 3473921 := bstep (se 2 (by rfl) ⟨1302720, by rfl⟩ : syracuseStep 3473921 = 2605441) B2605441
theorem B2315947 : Blo 2057435 2315947 := bstep (se 1 (by rfl) ⟨1736960, by rfl⟩ : syracuseStep 2315947 = 3473921) B3473921
theorem B3087929 : Blo 2057435 3087929 := bstep (se 2 (by rfl) ⟨1157973, by rfl⟩ : syracuseStep 3087929 = 2315947) B2315947
theorem B2058619 : Blo 2057435 2058619 := bstep (se 1 (by rfl) ⟨1543964, by rfl⟩ : syracuseStep 2058619 = 3087929) B3087929
theorem B2198345 : Blo 2057435 2198345 := bbase (se 2 (by rfl) ⟨824379, by rfl⟩ : syracuseStep 2198345 = 1648759) (by norm_num)
theorem B23449013 : Blo 2057435 23449013 := bstep (se 5 (by rfl) ⟨1099172, by rfl⟩ : syracuseStep 23449013 = 2198345) B2198345
theorem B15632675 : Blo 2057435 15632675 := bstep (se 1 (by rfl) ⟨11724506, by rfl⟩ : syracuseStep 15632675 = 23449013) B23449013
theorem B10421783 : Blo 2057435 10421783 := bstep (se 1 (by rfl) ⟨7816337, by rfl⟩ : syracuseStep 10421783 = 15632675) B15632675
theorem B6947855 : Blo 2057435 6947855 := bstep (se 1 (by rfl) ⟨5210891, by rfl⟩ : syracuseStep 6947855 = 10421783) B10421783
theorem B4631903 : Blo 2057435 4631903 := bstep (se 1 (by rfl) ⟨3473927, by rfl⟩ : syracuseStep 4631903 = 6947855) B6947855
theorem B3087935 : Blo 2057435 3087935 := bstep (se 1 (by rfl) ⟨2315951, by rfl⟩ : syracuseStep 3087935 = 4631903) B4631903
theorem B2058623 : Blo 2057435 2058623 := bstep (se 1 (by rfl) ⟨1543967, by rfl⟩ : syracuseStep 2058623 = 3087935) B3087935
theorem B3087941 : Blo 2057435 3087941 := bbase (se 4 (by rfl) ⟨289494, by rfl⟩ : syracuseStep 3087941 = 578989) (by norm_num)
theorem B2058627 : Blo 2057435 2058627 := bstep (se 1 (by rfl) ⟨1543970, by rfl⟩ : syracuseStep 2058627 = 3087941) B3087941
theorem B3473941 : Blo 2057435 3473941 := bbase (se 6 (by rfl) ⟨81420, by rfl⟩ : syracuseStep 3473941 = 162841) (by norm_num)
theorem B4631921 : Blo 2057435 4631921 := bstep (se 2 (by rfl) ⟨1736970, by rfl⟩ : syracuseStep 4631921 = 3473941) B3473941
theorem B3087947 : Blo 2057435 3087947 := bstep (se 1 (by rfl) ⟨2315960, by rfl⟩ : syracuseStep 3087947 = 4631921) B4631921
theorem B2058631 : Blo 2057435 2058631 := bstep (se 1 (by rfl) ⟨1543973, by rfl⟩ : syracuseStep 2058631 = 3087947) B3087947
theorem B2315965 : Blo 2057435 2315965 := bbase (se 3 (by rfl) ⟨434243, by rfl⟩ : syracuseStep 2315965 = 868487) (by norm_num)
theorem B3087953 : Blo 2057435 3087953 := bstep (se 2 (by rfl) ⟨1157982, by rfl⟩ : syracuseStep 3087953 = 2315965) B2315965
theorem B2058635 : Blo 2057435 2058635 := bstep (se 1 (by rfl) ⟨1543976, by rfl⟩ : syracuseStep 2058635 = 3087953) B3087953
theorem B6947909 : Blo 2057435 6947909 := bbase (se 4 (by rfl) ⟨651366, by rfl⟩ : syracuseStep 6947909 = 1302733) (by norm_num)
theorem B4631939 : Blo 2057435 4631939 := bstep (se 1 (by rfl) ⟨3473954, by rfl⟩ : syracuseStep 4631939 = 6947909) B6947909
theorem B3087959 : Blo 2057435 3087959 := bstep (se 1 (by rfl) ⟨2315969, by rfl⟩ : syracuseStep 3087959 = 4631939) B4631939
theorem B2058639 : Blo 2057435 2058639 := bstep (se 1 (by rfl) ⟨1543979, by rfl⟩ : syracuseStep 2058639 = 3087959) B3087959
theorem B3087965 : Blo 2057435 3087965 := bbase (se 3 (by rfl) ⟨578993, by rfl⟩ : syracuseStep 3087965 = 1157987) (by norm_num)
theorem B2058643 : Blo 2057435 2058643 := bstep (se 1 (by rfl) ⟨1543982, by rfl⟩ : syracuseStep 2058643 = 3087965) B3087965
theorem B4631957 : Blo 2057435 4631957 := bbase (se 6 (by rfl) ⟨108561, by rfl⟩ : syracuseStep 4631957 = 217123) (by norm_num)
theorem B3087971 : Blo 2057435 3087971 := bstep (se 1 (by rfl) ⟨2315978, by rfl⟩ : syracuseStep 3087971 = 4631957) B4631957
theorem B2058647 : Blo 2057435 2058647 := bstep (se 1 (by rfl) ⟨1543985, by rfl⟩ : syracuseStep 2058647 = 3087971) B3087971
theorem B6685109 : Blo 2057435 6685109 := bbase (se 5 (by rfl) ⟨313364, by rfl⟩ : syracuseStep 6685109 = 626729) (by norm_num)
theorem B4456739 : Blo 2057435 4456739 := bstep (se 1 (by rfl) ⟨3342554, by rfl⟩ : syracuseStep 4456739 = 6685109) B6685109
theorem B11884637 : Blo 2057435 11884637 := bstep (se 3 (by rfl) ⟨2228369, by rfl⟩ : syracuseStep 11884637 = 4456739) B4456739
theorem B7923091 : Blo 2057435 7923091 := bstep (se 1 (by rfl) ⟨5942318, by rfl⟩ : syracuseStep 7923091 = 11884637) B11884637
theorem B10564121 : Blo 2057435 10564121 := bstep (se 2 (by rfl) ⟨3961545, by rfl⟩ : syracuseStep 10564121 = 7923091) B7923091
theorem B28170989 : Blo 2057435 28170989 := bstep (se 3 (by rfl) ⟨5282060, by rfl⟩ : syracuseStep 28170989 = 10564121) B10564121
theorem B18780659 : Blo 2057435 18780659 := bstep (se 1 (by rfl) ⟨14085494, by rfl⟩ : syracuseStep 18780659 = 28170989) B28170989
theorem B12520439 : Blo 2057435 12520439 := bstep (se 1 (by rfl) ⟨9390329, by rfl⟩ : syracuseStep 12520439 = 18780659) B18780659
theorem B8346959 : Blo 2057435 8346959 := bstep (se 1 (by rfl) ⟨6260219, by rfl⟩ : syracuseStep 8346959 = 12520439) B12520439
theorem B5564639 : Blo 2057435 5564639 := bstep (se 1 (by rfl) ⟨4173479, by rfl⟩ : syracuseStep 5564639 = 8346959) B8346959
theorem B14839037 : Blo 2057435 14839037 := bstep (se 3 (by rfl) ⟨2782319, by rfl⟩ : syracuseStep 14839037 = 5564639) B5564639
theorem B9892691 : Blo 2057435 9892691 := bstep (se 1 (by rfl) ⟨7419518, by rfl⟩ : syracuseStep 9892691 = 14839037) B14839037
theorem B6595127 : Blo 2057435 6595127 := bstep (se 1 (by rfl) ⟨4946345, by rfl⟩ : syracuseStep 6595127 = 9892691) B9892691
theorem B4396751 : Blo 2057435 4396751 := bstep (se 1 (by rfl) ⟨3297563, by rfl⟩ : syracuseStep 4396751 = 6595127) B6595127
theorem B2931167 : Blo 2057435 2931167 := bstep (se 1 (by rfl) ⟨2198375, by rfl⟩ : syracuseStep 2931167 = 4396751) B4396751
theorem B7816445 : Blo 2057435 7816445 := bstep (se 3 (by rfl) ⟨1465583, by rfl⟩ : syracuseStep 7816445 = 2931167) B2931167
theorem B5210963 : Blo 2057435 5210963 := bstep (se 1 (by rfl) ⟨3908222, by rfl⟩ : syracuseStep 5210963 = 7816445) B7816445
theorem B3473975 : Blo 2057435 3473975 := bstep (se 1 (by rfl) ⟨2605481, by rfl⟩ : syracuseStep 3473975 = 5210963) B5210963
theorem B2315983 : Blo 2057435 2315983 := bstep (se 1 (by rfl) ⟨1736987, by rfl⟩ : syracuseStep 2315983 = 3473975) B3473975
theorem B3087977 : Blo 2057435 3087977 := bstep (se 2 (by rfl) ⟨1157991, by rfl⟩ : syracuseStep 3087977 = 2315983) B2315983
theorem B2058651 : Blo 2057435 2058651 := bstep (se 1 (by rfl) ⟨1543988, by rfl⟩ : syracuseStep 2058651 = 3087977) B3087977
theorem B2473177 : Blo 2057435 2473177 := bbase (se 2 (by rfl) ⟨927441, by rfl⟩ : syracuseStep 2473177 = 1854883) (by norm_num)
theorem B3297569 : Blo 2057435 3297569 := bstep (se 2 (by rfl) ⟨1236588, by rfl⟩ : syracuseStep 3297569 = 2473177) B2473177
theorem B8793517 : Blo 2057435 8793517 := bstep (se 3 (by rfl) ⟨1648784, by rfl⟩ : syracuseStep 8793517 = 3297569) B3297569
theorem B11724689 : Blo 2057435 11724689 := bstep (se 2 (by rfl) ⟨4396758, by rfl⟩ : syracuseStep 11724689 = 8793517) B8793517
theorem B7816459 : Blo 2057435 7816459 := bstep (se 1 (by rfl) ⟨5862344, by rfl⟩ : syracuseStep 7816459 = 11724689) B11724689
theorem B10421945 : Blo 2057435 10421945 := bstep (se 2 (by rfl) ⟨3908229, by rfl⟩ : syracuseStep 10421945 = 7816459) B7816459
theorem B6947963 : Blo 2057435 6947963 := bstep (se 1 (by rfl) ⟨5210972, by rfl⟩ : syracuseStep 6947963 = 10421945) B10421945
theorem B4631975 : Blo 2057435 4631975 := bstep (se 1 (by rfl) ⟨3473981, by rfl⟩ : syracuseStep 4631975 = 6947963) B6947963
theorem B3087983 : Blo 2057435 3087983 := bstep (se 1 (by rfl) ⟨2315987, by rfl⟩ : syracuseStep 3087983 = 4631975) B4631975
theorem B2058655 : Blo 2057435 2058655 := bstep (se 1 (by rfl) ⟨1543991, by rfl⟩ : syracuseStep 2058655 = 3087983) B3087983
theorem B3087989 : Blo 2057435 3087989 := bbase (se 5 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 3087989 = 289499) (by norm_num)
theorem B2058659 : Blo 2057435 2058659 := bstep (se 1 (by rfl) ⟨1543994, by rfl⟩ : syracuseStep 2058659 = 3087989) B3087989
theorem B3908245 : Blo 2057435 3908245 := bbase (se 6 (by rfl) ⟨91599, by rfl⟩ : syracuseStep 3908245 = 183199) (by norm_num)
theorem B5210993 : Blo 2057435 5210993 := bstep (se 2 (by rfl) ⟨1954122, by rfl⟩ : syracuseStep 5210993 = 3908245) B3908245
theorem B3473995 : Blo 2057435 3473995 := bstep (se 1 (by rfl) ⟨2605496, by rfl⟩ : syracuseStep 3473995 = 5210993) B5210993
theorem B4631993 : Blo 2057435 4631993 := bstep (se 2 (by rfl) ⟨1736997, by rfl⟩ : syracuseStep 4631993 = 3473995) B3473995
theorem B3087995 : Blo 2057435 3087995 := bstep (se 1 (by rfl) ⟨2315996, by rfl⟩ : syracuseStep 3087995 = 4631993) B4631993
theorem B2058663 : Blo 2057435 2058663 := bstep (se 1 (by rfl) ⟨1543997, by rfl⟩ : syracuseStep 2058663 = 3087995) B3087995
theorem B2316001 : Blo 2057435 2316001 := bbase (se 2 (by rfl) ⟨868500, by rfl⟩ : syracuseStep 2316001 = 1737001) (by norm_num)
theorem B3088001 : Blo 2057435 3088001 := bstep (se 2 (by rfl) ⟨1158000, by rfl⟩ : syracuseStep 3088001 = 2316001) B2316001
theorem B2058667 : Blo 2057435 2058667 := bstep (se 1 (by rfl) ⟨1544000, by rfl⟩ : syracuseStep 2058667 = 3088001) B3088001
theorem B5211013 : Blo 2057435 5211013 := bbase (se 4 (by rfl) ⟨488532, by rfl⟩ : syracuseStep 5211013 = 977065) (by norm_num)
theorem B6948017 : Blo 2057435 6948017 := bstep (se 2 (by rfl) ⟨2605506, by rfl⟩ : syracuseStep 6948017 = 5211013) B5211013
theorem B4632011 : Blo 2057435 4632011 := bstep (se 1 (by rfl) ⟨3474008, by rfl⟩ : syracuseStep 4632011 = 6948017) B6948017
theorem B3088007 : Blo 2057435 3088007 := bstep (se 1 (by rfl) ⟨2316005, by rfl⟩ : syracuseStep 3088007 = 4632011) B4632011
theorem B2058671 : Blo 2057435 2058671 := bstep (se 1 (by rfl) ⟨1544003, by rfl⟩ : syracuseStep 2058671 = 3088007) B3088007
theorem B3088013 : Blo 2057435 3088013 := bbase (se 3 (by rfl) ⟨579002, by rfl⟩ : syracuseStep 3088013 = 1158005) (by norm_num)
theorem B2058675 : Blo 2057435 2058675 := bstep (se 1 (by rfl) ⟨1544006, by rfl⟩ : syracuseStep 2058675 = 3088013) B3088013
theorem B4632029 : Blo 2057435 4632029 := bbase (se 3 (by rfl) ⟨868505, by rfl⟩ : syracuseStep 4632029 = 1737011) (by norm_num)
theorem B3088019 : Blo 2057435 3088019 := bstep (se 1 (by rfl) ⟨2316014, by rfl⟩ : syracuseStep 3088019 = 4632029) B4632029
theorem B2058679 : Blo 2057435 2058679 := bstep (se 1 (by rfl) ⟨1544009, by rfl⟩ : syracuseStep 2058679 = 3088019) B3088019
theorem B3474029 : Blo 2057435 3474029 := bbase (se 3 (by rfl) ⟨651380, by rfl⟩ : syracuseStep 3474029 = 1302761) (by norm_num)
theorem B2316019 : Blo 2057435 2316019 := bstep (se 1 (by rfl) ⟨1737014, by rfl⟩ : syracuseStep 2316019 = 3474029) B3474029
theorem B3088025 : Blo 2057435 3088025 := bstep (se 2 (by rfl) ⟨1158009, by rfl⟩ : syracuseStep 3088025 = 2316019) B2316019
theorem B2058683 : Blo 2057435 2058683 := bstep (se 1 (by rfl) ⟨1544012, by rfl⟩ : syracuseStep 2058683 = 3088025) B3088025
theorem B3961613 : Blo 2057435 3961613 := bbase (se 3 (by rfl) ⟨742802, by rfl⟩ : syracuseStep 3961613 = 1485605) (by norm_num)
theorem B10564301 : Blo 2057435 10564301 := bstep (se 3 (by rfl) ⟨1980806, by rfl⟩ : syracuseStep 10564301 = 3961613) B3961613
theorem B28171469 : Blo 2057435 28171469 := bstep (se 3 (by rfl) ⟨5282150, by rfl⟩ : syracuseStep 28171469 = 10564301) B10564301
theorem B18780979 : Blo 2057435 18780979 := bstep (se 1 (by rfl) ⟨14085734, by rfl⟩ : syracuseStep 18780979 = 28171469) B28171469
theorem B25041305 : Blo 2057435 25041305 := bstep (se 2 (by rfl) ⟨9390489, by rfl⟩ : syracuseStep 25041305 = 18780979) B18780979
theorem B16694203 : Blo 2057435 16694203 := bstep (se 1 (by rfl) ⟨12520652, by rfl⟩ : syracuseStep 16694203 = 25041305) B25041305
theorem B22258937 : Blo 2057435 22258937 := bstep (se 2 (by rfl) ⟨8347101, by rfl⟩ : syracuseStep 22258937 = 16694203) B16694203
theorem B14839291 : Blo 2057435 14839291 := bstep (se 1 (by rfl) ⟨11129468, by rfl⟩ : syracuseStep 14839291 = 22258937) B22258937
theorem B19785721 : Blo 2057435 19785721 := bstep (se 2 (by rfl) ⟨7419645, by rfl⟩ : syracuseStep 19785721 = 14839291) B14839291
theorem B26380961 : Blo 2057435 26380961 := bstep (se 2 (by rfl) ⟨9892860, by rfl⟩ : syracuseStep 26380961 = 19785721) B19785721
theorem B17587307 : Blo 2057435 17587307 := bstep (se 1 (by rfl) ⟨13190480, by rfl⟩ : syracuseStep 17587307 = 26380961) B26380961
theorem B11724871 : Blo 2057435 11724871 := bstep (se 1 (by rfl) ⟨8793653, by rfl⟩ : syracuseStep 11724871 = 17587307) B17587307
theorem B15633161 : Blo 2057435 15633161 := bstep (se 2 (by rfl) ⟨5862435, by rfl⟩ : syracuseStep 15633161 = 11724871) B11724871
theorem B10422107 : Blo 2057435 10422107 := bstep (se 1 (by rfl) ⟨7816580, by rfl⟩ : syracuseStep 10422107 = 15633161) B15633161
theorem B6948071 : Blo 2057435 6948071 := bstep (se 1 (by rfl) ⟨5211053, by rfl⟩ : syracuseStep 6948071 = 10422107) B10422107
theorem B4632047 : Blo 2057435 4632047 := bstep (se 1 (by rfl) ⟨3474035, by rfl⟩ : syracuseStep 4632047 = 6948071) B6948071
theorem B3088031 : Blo 2057435 3088031 := bstep (se 1 (by rfl) ⟨2316023, by rfl⟩ : syracuseStep 3088031 = 4632047) B4632047
theorem B2058687 : Blo 2057435 2058687 := bstep (se 1 (by rfl) ⟨1544015, by rfl⟩ : syracuseStep 2058687 = 3088031) B3088031
theorem B3088037 : Blo 2057435 3088037 := bbase (se 4 (by rfl) ⟨289503, by rfl⟩ : syracuseStep 3088037 = 579007) (by norm_num)
theorem B2058691 : Blo 2057435 2058691 := bstep (se 1 (by rfl) ⟨1544018, by rfl⟩ : syracuseStep 2058691 = 3088037) B3088037
theorem B2605537 : Blo 2057435 2605537 := bbase (se 2 (by rfl) ⟨977076, by rfl⟩ : syracuseStep 2605537 = 1954153) (by norm_num)
theorem B3474049 : Blo 2057435 3474049 := bstep (se 2 (by rfl) ⟨1302768, by rfl⟩ : syracuseStep 3474049 = 2605537) B2605537
theorem B4632065 : Blo 2057435 4632065 := bstep (se 2 (by rfl) ⟨1737024, by rfl⟩ : syracuseStep 4632065 = 3474049) B3474049
theorem B3088043 : Blo 2057435 3088043 := bstep (se 1 (by rfl) ⟨2316032, by rfl⟩ : syracuseStep 3088043 = 4632065) B4632065
theorem B2058695 : Blo 2057435 2058695 := bstep (se 1 (by rfl) ⟨1544021, by rfl⟩ : syracuseStep 2058695 = 3088043) B3088043
theorem B2316037 : Blo 2057435 2316037 := bbase (se 4 (by rfl) ⟨217128, by rfl⟩ : syracuseStep 2316037 = 434257) (by norm_num)
theorem B3088049 : Blo 2057435 3088049 := bstep (se 2 (by rfl) ⟨1158018, by rfl⟩ : syracuseStep 3088049 = 2316037) B2316037
theorem B2058699 : Blo 2057435 2058699 := bstep (se 1 (by rfl) ⟨1544024, by rfl⟩ : syracuseStep 2058699 = 3088049) B3088049
theorem B12520757 : Blo 2057435 12520757 := bbase (se 5 (by rfl) ⟨586910, by rfl⟩ : syracuseStep 12520757 = 1173821) (by norm_num)
theorem B8347171 : Blo 2057435 8347171 := bstep (se 1 (by rfl) ⟨6260378, by rfl⟩ : syracuseStep 8347171 = 12520757) B12520757
theorem B11129561 : Blo 2057435 11129561 := bstep (se 2 (by rfl) ⟨4173585, by rfl⟩ : syracuseStep 11129561 = 8347171) B8347171
theorem B7419707 : Blo 2057435 7419707 := bstep (se 1 (by rfl) ⟨5564780, by rfl⟩ : syracuseStep 7419707 = 11129561) B11129561
theorem B4946471 : Blo 2057435 4946471 := bstep (se 1 (by rfl) ⟨3709853, by rfl⟩ : syracuseStep 4946471 = 7419707) B7419707
theorem B3297647 : Blo 2057435 3297647 := bstep (se 1 (by rfl) ⟨2473235, by rfl⟩ : syracuseStep 3297647 = 4946471) B4946471
theorem B2198431 : Blo 2057435 2198431 := bstep (se 1 (by rfl) ⟨1648823, by rfl⟩ : syracuseStep 2198431 = 3297647) B3297647
theorem B2931241 : Blo 2057435 2931241 := bstep (se 2 (by rfl) ⟨1099215, by rfl⟩ : syracuseStep 2931241 = 2198431) B2198431
theorem B3908321 : Blo 2057435 3908321 := bstep (se 2 (by rfl) ⟨1465620, by rfl⟩ : syracuseStep 3908321 = 2931241) B2931241
theorem B2605547 : Blo 2057435 2605547 := bstep (se 1 (by rfl) ⟨1954160, by rfl⟩ : syracuseStep 2605547 = 3908321) B3908321
theorem B6948125 : Blo 2057435 6948125 := bstep (se 3 (by rfl) ⟨1302773, by rfl⟩ : syracuseStep 6948125 = 2605547) B2605547
theorem B4632083 : Blo 2057435 4632083 := bstep (se 1 (by rfl) ⟨3474062, by rfl⟩ : syracuseStep 4632083 = 6948125) B6948125
theorem B3088055 : Blo 2057435 3088055 := bstep (se 1 (by rfl) ⟨2316041, by rfl⟩ : syracuseStep 3088055 = 4632083) B4632083
theorem B2058703 : Blo 2057435 2058703 := bstep (se 1 (by rfl) ⟨1544027, by rfl⟩ : syracuseStep 2058703 = 3088055) B3088055
theorem B3088061 : Blo 2057435 3088061 := bbase (se 3 (by rfl) ⟨579011, by rfl⟩ : syracuseStep 3088061 = 1158023) (by norm_num)
theorem B2058707 : Blo 2057435 2058707 := bstep (se 1 (by rfl) ⟨1544030, by rfl⟩ : syracuseStep 2058707 = 3088061) B3088061
theorem B4632101 : Blo 2057435 4632101 := bbase (se 4 (by rfl) ⟨434259, by rfl⟩ : syracuseStep 4632101 = 868519) (by norm_num)
theorem B3088067 : Blo 2057435 3088067 := bstep (se 1 (by rfl) ⟨2316050, by rfl⟩ : syracuseStep 3088067 = 4632101) B4632101
theorem B2058711 : Blo 2057435 2058711 := bstep (se 1 (by rfl) ⟨1544033, by rfl⟩ : syracuseStep 2058711 = 3088067) B3088067
theorem B5211125 : Blo 2057435 5211125 := bbase (se 5 (by rfl) ⟨244271, by rfl⟩ : syracuseStep 5211125 = 488543) (by norm_num)
theorem B3474083 : Blo 2057435 3474083 := bstep (se 1 (by rfl) ⟨2605562, by rfl⟩ : syracuseStep 3474083 = 5211125) B5211125
theorem B2316055 : Blo 2057435 2316055 := bstep (se 1 (by rfl) ⟨1737041, by rfl⟩ : syracuseStep 2316055 = 3474083) B3474083
theorem B3088073 : Blo 2057435 3088073 := bstep (se 2 (by rfl) ⟨1158027, by rfl⟩ : syracuseStep 3088073 = 2316055) B2316055
theorem B2058715 : Blo 2057435 2058715 := bstep (se 1 (by rfl) ⟨1544036, by rfl⟩ : syracuseStep 2058715 = 3088073) B3088073
theorem B4456885 : Blo 2057435 4456885 := bbase (se 5 (by rfl) ⟨208916, by rfl⟩ : syracuseStep 4456885 = 417833) (by norm_num)
theorem B5942513 : Blo 2057435 5942513 := bstep (se 2 (by rfl) ⟨2228442, by rfl⟩ : syracuseStep 5942513 = 4456885) B4456885
theorem B3961675 : Blo 2057435 3961675 := bstep (se 1 (by rfl) ⟨2971256, by rfl⟩ : syracuseStep 3961675 = 5942513) B5942513
theorem B5282233 : Blo 2057435 5282233 := bstep (se 2 (by rfl) ⟨1980837, by rfl⟩ : syracuseStep 5282233 = 3961675) B3961675
theorem B28171909 : Blo 2057435 28171909 := bstep (se 4 (by rfl) ⟨2641116, by rfl⟩ : syracuseStep 28171909 = 5282233) B5282233
theorem B37562545 : Blo 2057435 37562545 := bstep (se 2 (by rfl) ⟨14085954, by rfl⟩ : syracuseStep 37562545 = 28171909) B28171909
theorem B50083393 : Blo 2057435 50083393 := bstep (se 2 (by rfl) ⟨18781272, by rfl⟩ : syracuseStep 50083393 = 37562545) B37562545
theorem B66777857 : Blo 2057435 66777857 := bstep (se 2 (by rfl) ⟨25041696, by rfl⟩ : syracuseStep 66777857 = 50083393) B50083393
theorem B44518571 : Blo 2057435 44518571 := bstep (se 1 (by rfl) ⟨33388928, by rfl⟩ : syracuseStep 44518571 = 66777857) B66777857
theorem B29679047 : Blo 2057435 29679047 := bstep (se 1 (by rfl) ⟨22259285, by rfl⟩ : syracuseStep 29679047 = 44518571) B44518571
theorem B19786031 : Blo 2057435 19786031 := bstep (se 1 (by rfl) ⟨14839523, by rfl⟩ : syracuseStep 19786031 = 29679047) B29679047
theorem B13190687 : Blo 2057435 13190687 := bstep (se 1 (by rfl) ⟨9893015, by rfl⟩ : syracuseStep 13190687 = 19786031) B19786031
theorem B8793791 : Blo 2057435 8793791 := bstep (se 1 (by rfl) ⟨6595343, by rfl⟩ : syracuseStep 8793791 = 13190687) B13190687
theorem B5862527 : Blo 2057435 5862527 := bstep (se 1 (by rfl) ⟨4396895, by rfl⟩ : syracuseStep 5862527 = 8793791) B8793791
theorem B3908351 : Blo 2057435 3908351 := bstep (se 1 (by rfl) ⟨2931263, by rfl⟩ : syracuseStep 3908351 = 5862527) B5862527
theorem B10422269 : Blo 2057435 10422269 := bstep (se 3 (by rfl) ⟨1954175, by rfl⟩ : syracuseStep 10422269 = 3908351) B3908351
theorem B6948179 : Blo 2057435 6948179 := bstep (se 1 (by rfl) ⟨5211134, by rfl⟩ : syracuseStep 6948179 = 10422269) B10422269
theorem B4632119 : Blo 2057435 4632119 := bstep (se 1 (by rfl) ⟨3474089, by rfl⟩ : syracuseStep 4632119 = 6948179) B6948179
theorem B3088079 : Blo 2057435 3088079 := bstep (se 1 (by rfl) ⟨2316059, by rfl⟩ : syracuseStep 3088079 = 4632119) B4632119
theorem B2058719 : Blo 2057435 2058719 := bstep (se 1 (by rfl) ⟨1544039, by rfl⟩ : syracuseStep 2058719 = 3088079) B3088079
theorem B3088085 : Blo 2057435 3088085 := bbase (se 7 (by rfl) ⟨36188, by rfl⟩ : syracuseStep 3088085 = 72377) (by norm_num)
theorem B2058723 : Blo 2057435 2058723 := bstep (se 1 (by rfl) ⟨1544042, by rfl⟩ : syracuseStep 2058723 = 3088085) B3088085
theorem B3297685 : Blo 2057435 3297685 := bbase (se 6 (by rfl) ⟨77289, by rfl⟩ : syracuseStep 3297685 = 154579) (by norm_num)
theorem B4396913 : Blo 2057435 4396913 := bstep (se 2 (by rfl) ⟨1648842, by rfl⟩ : syracuseStep 4396913 = 3297685) B3297685
theorem B2931275 : Blo 2057435 2931275 := bstep (se 1 (by rfl) ⟨2198456, by rfl⟩ : syracuseStep 2931275 = 4396913) B4396913
theorem B7816733 : Blo 2057435 7816733 := bstep (se 3 (by rfl) ⟨1465637, by rfl⟩ : syracuseStep 7816733 = 2931275) B2931275
theorem B5211155 : Blo 2057435 5211155 := bstep (se 1 (by rfl) ⟨3908366, by rfl⟩ : syracuseStep 5211155 = 7816733) B7816733
theorem B3474103 : Blo 2057435 3474103 := bstep (se 1 (by rfl) ⟨2605577, by rfl⟩ : syracuseStep 3474103 = 5211155) B5211155
theorem B4632137 : Blo 2057435 4632137 := bstep (se 2 (by rfl) ⟨1737051, by rfl⟩ : syracuseStep 4632137 = 3474103) B3474103
theorem B3088091 : Blo 2057435 3088091 := bstep (se 1 (by rfl) ⟨2316068, by rfl⟩ : syracuseStep 3088091 = 4632137) B4632137
theorem B2058727 : Blo 2057435 2058727 := bstep (se 1 (by rfl) ⟨1544045, by rfl⟩ : syracuseStep 2058727 = 3088091) B3088091
theorem B2316073 : Blo 2057435 2316073 := bbase (se 2 (by rfl) ⟨868527, by rfl⟩ : syracuseStep 2316073 = 1737055) (by norm_num)
theorem B3088097 : Blo 2057435 3088097 := bstep (se 2 (by rfl) ⟨1158036, by rfl⟩ : syracuseStep 3088097 = 2316073) B2316073
theorem B2058731 : Blo 2057435 2058731 := bstep (se 1 (by rfl) ⟨1544048, by rfl⟩ : syracuseStep 2058731 = 3088097) B3088097
theorem B2473273 : Blo 2057435 2473273 := bbase (se 2 (by rfl) ⟨927477, by rfl⟩ : syracuseStep 2473273 = 1854955) (by norm_num)
theorem B13190789 : Blo 2057435 13190789 := bstep (se 4 (by rfl) ⟨1236636, by rfl⟩ : syracuseStep 13190789 = 2473273) B2473273
theorem B8793859 : Blo 2057435 8793859 := bstep (se 1 (by rfl) ⟨6595394, by rfl⟩ : syracuseStep 8793859 = 13190789) B13190789
theorem B11725145 : Blo 2057435 11725145 := bstep (se 2 (by rfl) ⟨4396929, by rfl⟩ : syracuseStep 11725145 = 8793859) B8793859
theorem B7816763 : Blo 2057435 7816763 := bstep (se 1 (by rfl) ⟨5862572, by rfl⟩ : syracuseStep 7816763 = 11725145) B11725145
theorem B5211175 : Blo 2057435 5211175 := bstep (se 1 (by rfl) ⟨3908381, by rfl⟩ : syracuseStep 5211175 = 7816763) B7816763
theorem B6948233 : Blo 2057435 6948233 := bstep (se 2 (by rfl) ⟨2605587, by rfl⟩ : syracuseStep 6948233 = 5211175) B5211175
theorem B4632155 : Blo 2057435 4632155 := bstep (se 1 (by rfl) ⟨3474116, by rfl⟩ : syracuseStep 4632155 = 6948233) B6948233
theorem B3088103 : Blo 2057435 3088103 := bstep (se 1 (by rfl) ⟨2316077, by rfl⟩ : syracuseStep 3088103 = 4632155) B4632155
theorem B2058735 : Blo 2057435 2058735 := bstep (se 1 (by rfl) ⟨1544051, by rfl⟩ : syracuseStep 2058735 = 3088103) B3088103
theorem B3088109 : Blo 2057435 3088109 := bbase (se 3 (by rfl) ⟨579020, by rfl⟩ : syracuseStep 3088109 = 1158041) (by norm_num)
theorem B2058739 : Blo 2057435 2058739 := bstep (se 1 (by rfl) ⟨1544054, by rfl⟩ : syracuseStep 2058739 = 3088109) B3088109
theorem B4632173 : Blo 2057435 4632173 := bbase (se 3 (by rfl) ⟨868532, by rfl⟩ : syracuseStep 4632173 = 1737065) (by norm_num)
theorem B3088115 : Blo 2057435 3088115 := bstep (se 1 (by rfl) ⟨2316086, by rfl⟩ : syracuseStep 3088115 = 4632173) B4632173
theorem B2058743 : Blo 2057435 2058743 := bstep (se 1 (by rfl) ⟨1544057, by rfl⟩ : syracuseStep 2058743 = 3088115) B3088115
theorem B3908405 : Blo 2057435 3908405 := bbase (se 5 (by rfl) ⟨183206, by rfl⟩ : syracuseStep 3908405 = 366413) (by norm_num)
theorem B2605603 : Blo 2057435 2605603 := bstep (se 1 (by rfl) ⟨1954202, by rfl⟩ : syracuseStep 2605603 = 3908405) B3908405
theorem B3474137 : Blo 2057435 3474137 := bstep (se 2 (by rfl) ⟨1302801, by rfl⟩ : syracuseStep 3474137 = 2605603) B2605603
theorem B2316091 : Blo 2057435 2316091 := bstep (se 1 (by rfl) ⟨1737068, by rfl⟩ : syracuseStep 2316091 = 3474137) B3474137
theorem B3088121 : Blo 2057435 3088121 := bstep (se 2 (by rfl) ⟨1158045, by rfl⟩ : syracuseStep 3088121 = 2316091) B2316091
theorem B2058747 : Blo 2057435 2058747 := bstep (se 1 (by rfl) ⟨1544060, by rfl⟩ : syracuseStep 2058747 = 3088121) B3088121
theorem B9648773 : Blo 2057435 9648773 := bbase (se 4 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 9648773 = 1809145) (by norm_num)
theorem B6432515 : Blo 2057435 6432515 := bstep (se 1 (by rfl) ⟨4824386, by rfl⟩ : syracuseStep 6432515 = 9648773) B9648773
theorem B4288343 : Blo 2057435 4288343 := bstep (se 1 (by rfl) ⟨3216257, by rfl⟩ : syracuseStep 4288343 = 6432515) B6432515
theorem B11435581 : Blo 2057435 11435581 := bstep (se 3 (by rfl) ⟨2144171, by rfl⟩ : syracuseStep 11435581 = 4288343) B4288343
theorem B15247441 : Blo 2057435 15247441 := bstep (se 2 (by rfl) ⟨5717790, by rfl⟩ : syracuseStep 15247441 = 11435581) B11435581
theorem B20329921 : Blo 2057435 20329921 := bstep (se 2 (by rfl) ⟨7623720, by rfl⟩ : syracuseStep 20329921 = 15247441) B15247441
theorem B27106561 : Blo 2057435 27106561 := bstep (se 2 (by rfl) ⟨10164960, by rfl⟩ : syracuseStep 27106561 = 20329921) B20329921
theorem B36142081 : Blo 2057435 36142081 := bstep (se 2 (by rfl) ⟨13553280, by rfl⟩ : syracuseStep 36142081 = 27106561) B27106561
theorem B192757765 : Blo 2057435 192757765 := bstep (se 4 (by rfl) ⟨18071040, by rfl⟩ : syracuseStep 192757765 = 36142081) B36142081
theorem B257010353 : Blo 2057435 257010353 := bstep (se 2 (by rfl) ⟨96378882, by rfl⟩ : syracuseStep 257010353 = 192757765) B192757765
theorem B171340235 : Blo 2057435 171340235 := bstep (se 1 (by rfl) ⟨128505176, by rfl⟩ : syracuseStep 171340235 = 257010353) B257010353
theorem B114226823 : Blo 2057435 114226823 := bstep (se 1 (by rfl) ⟨85670117, by rfl⟩ : syracuseStep 114226823 = 171340235) B171340235
theorem B76151215 : Blo 2057435 76151215 := bstep (se 1 (by rfl) ⟨57113411, by rfl⟩ : syracuseStep 76151215 = 114226823) B114226823
theorem B101534953 : Blo 2057435 101534953 := bstep (se 2 (by rfl) ⟨38075607, by rfl⟩ : syracuseStep 101534953 = 76151215) B76151215
theorem B135379937 : Blo 2057435 135379937 := bstep (se 2 (by rfl) ⟨50767476, by rfl⟩ : syracuseStep 135379937 = 101534953) B101534953
theorem B90253291 : Blo 2057435 90253291 := bstep (se 1 (by rfl) ⟨67689968, by rfl⟩ : syracuseStep 90253291 = 135379937) B135379937
theorem B120337721 : Blo 2057435 120337721 := bstep (se 2 (by rfl) ⟨45126645, by rfl⟩ : syracuseStep 120337721 = 90253291) B90253291
theorem B80225147 : Blo 2057435 80225147 := bstep (se 1 (by rfl) ⟨60168860, by rfl⟩ : syracuseStep 80225147 = 120337721) B120337721
theorem B53483431 : Blo 2057435 53483431 := bstep (se 1 (by rfl) ⟨40112573, by rfl⟩ : syracuseStep 53483431 = 80225147) B80225147
theorem B71311241 : Blo 2057435 71311241 := bstep (se 2 (by rfl) ⟨26741715, by rfl⟩ : syracuseStep 71311241 = 53483431) B53483431
theorem B47540827 : Blo 2057435 47540827 := bstep (se 1 (by rfl) ⟨35655620, by rfl⟩ : syracuseStep 47540827 = 71311241) B71311241
theorem B63387769 : Blo 2057435 63387769 := bstep (se 2 (by rfl) ⟨23770413, by rfl⟩ : syracuseStep 63387769 = 47540827) B47540827
theorem B84517025 : Blo 2057435 84517025 := bstep (se 2 (by rfl) ⟨31693884, by rfl⟩ : syracuseStep 84517025 = 63387769) B63387769
theorem B225378733 : Blo 2057435 225378733 := bstep (se 3 (by rfl) ⟨42258512, by rfl⟩ : syracuseStep 225378733 = 84517025) B84517025
theorem B300504977 : Blo 2057435 300504977 := bstep (se 2 (by rfl) ⟨112689366, by rfl⟩ : syracuseStep 300504977 = 225378733) B225378733
theorem B200336651 : Blo 2057435 200336651 := bstep (se 1 (by rfl) ⟨150252488, by rfl⟩ : syracuseStep 200336651 = 300504977) B300504977
theorem B133557767 : Blo 2057435 133557767 := bstep (se 1 (by rfl) ⟨100168325, by rfl⟩ : syracuseStep 133557767 = 200336651) B200336651
theorem B89038511 : Blo 2057435 89038511 := bstep (se 1 (by rfl) ⟨66778883, by rfl⟩ : syracuseStep 89038511 = 133557767) B133557767
theorem B59359007 : Blo 2057435 59359007 := bstep (se 1 (by rfl) ⟨44519255, by rfl⟩ : syracuseStep 59359007 = 89038511) B89038511
theorem B39572671 : Blo 2057435 39572671 := bstep (se 1 (by rfl) ⟨29679503, by rfl⟩ : syracuseStep 39572671 = 59359007) B59359007
theorem B52763561 : Blo 2057435 52763561 := bstep (se 2 (by rfl) ⟨19786335, by rfl⟩ : syracuseStep 52763561 = 39572671) B39572671
theorem B35175707 : Blo 2057435 35175707 := bstep (se 1 (by rfl) ⟨26381780, by rfl⟩ : syracuseStep 35175707 = 52763561) B52763561
theorem B23450471 : Blo 2057435 23450471 := bstep (se 1 (by rfl) ⟨17587853, by rfl⟩ : syracuseStep 23450471 = 35175707) B35175707
theorem B15633647 : Blo 2057435 15633647 := bstep (se 1 (by rfl) ⟨11725235, by rfl⟩ : syracuseStep 15633647 = 23450471) B23450471
theorem B10422431 : Blo 2057435 10422431 := bstep (se 1 (by rfl) ⟨7816823, by rfl⟩ : syracuseStep 10422431 = 15633647) B15633647
theorem B6948287 : Blo 2057435 6948287 := bstep (se 1 (by rfl) ⟨5211215, by rfl⟩ : syracuseStep 6948287 = 10422431) B10422431
theorem B4632191 : Blo 2057435 4632191 := bstep (se 1 (by rfl) ⟨3474143, by rfl⟩ : syracuseStep 4632191 = 6948287) B6948287
theorem B3088127 : Blo 2057435 3088127 := bstep (se 1 (by rfl) ⟨2316095, by rfl⟩ : syracuseStep 3088127 = 4632191) B4632191
theorem B2058751 : Blo 2057435 2058751 := bstep (se 1 (by rfl) ⟨1544063, by rfl⟩ : syracuseStep 2058751 = 3088127) B3088127
theorem B3088133 : Blo 2057435 3088133 := bbase (se 4 (by rfl) ⟨289512, by rfl⟩ : syracuseStep 3088133 = 579025) (by norm_num)
theorem B2058755 : Blo 2057435 2058755 := bstep (se 1 (by rfl) ⟨1544066, by rfl⟩ : syracuseStep 2058755 = 3088133) B3088133
theorem B3474157 : Blo 2057435 3474157 := bbase (se 3 (by rfl) ⟨651404, by rfl⟩ : syracuseStep 3474157 = 1302809) (by norm_num)
theorem B4632209 : Blo 2057435 4632209 := bstep (se 2 (by rfl) ⟨1737078, by rfl⟩ : syracuseStep 4632209 = 3474157) B3474157
theorem B3088139 : Blo 2057435 3088139 := bstep (se 1 (by rfl) ⟨2316104, by rfl⟩ : syracuseStep 3088139 = 4632209) B4632209
theorem B2058759 : Blo 2057435 2058759 := bstep (se 1 (by rfl) ⟨1544069, by rfl⟩ : syracuseStep 2058759 = 3088139) B3088139
theorem B2316109 : Blo 2057435 2316109 := bbase (se 3 (by rfl) ⟨434270, by rfl⟩ : syracuseStep 2316109 = 868541) (by norm_num)
theorem B3088145 : Blo 2057435 3088145 := bstep (se 2 (by rfl) ⟨1158054, by rfl⟩ : syracuseStep 3088145 = 2316109) B2316109
theorem B2058763 : Blo 2057435 2058763 := bstep (se 1 (by rfl) ⟨1544072, by rfl⟩ : syracuseStep 2058763 = 3088145) B3088145
theorem B6948341 : Blo 2057435 6948341 := bbase (se 5 (by rfl) ⟨325703, by rfl⟩ : syracuseStep 6948341 = 651407) (by norm_num)
theorem B4632227 : Blo 2057435 4632227 := bstep (se 1 (by rfl) ⟨3474170, by rfl⟩ : syracuseStep 4632227 = 6948341) B6948341
theorem B3088151 : Blo 2057435 3088151 := bstep (se 1 (by rfl) ⟨2316113, by rfl⟩ : syracuseStep 3088151 = 4632227) B4632227
theorem B2058767 : Blo 2057435 2058767 := bstep (se 1 (by rfl) ⟨1544075, by rfl⟩ : syracuseStep 2058767 = 3088151) B3088151
theorem B3088157 : Blo 2057435 3088157 := bbase (se 3 (by rfl) ⟨579029, by rfl⟩ : syracuseStep 3088157 = 1158059) (by norm_num)
theorem B2058771 : Blo 2057435 2058771 := bstep (se 1 (by rfl) ⟨1544078, by rfl⟩ : syracuseStep 2058771 = 3088157) B3088157
theorem B4632245 : Blo 2057435 4632245 := bbase (se 5 (by rfl) ⟨217136, by rfl⟩ : syracuseStep 4632245 = 434273) (by norm_num)
theorem B3088163 : Blo 2057435 3088163 := bstep (se 1 (by rfl) ⟨2316122, by rfl⟩ : syracuseStep 3088163 = 4632245) B4632245
theorem B2058775 : Blo 2057435 2058775 := bstep (se 1 (by rfl) ⟨1544081, by rfl⟩ : syracuseStep 2058775 = 3088163) B3088163
theorem B11725397 : Blo 2057435 11725397 := bbase (se 8 (by rfl) ⟨68703, by rfl⟩ : syracuseStep 11725397 = 137407) (by norm_num)
theorem B7816931 : Blo 2057435 7816931 := bstep (se 1 (by rfl) ⟨5862698, by rfl⟩ : syracuseStep 7816931 = 11725397) B11725397
theorem B5211287 : Blo 2057435 5211287 := bstep (se 1 (by rfl) ⟨3908465, by rfl⟩ : syracuseStep 5211287 = 7816931) B7816931
theorem B3474191 : Blo 2057435 3474191 := bstep (se 1 (by rfl) ⟨2605643, by rfl⟩ : syracuseStep 3474191 = 5211287) B5211287
theorem B2316127 : Blo 2057435 2316127 := bstep (se 1 (by rfl) ⟨1737095, by rfl⟩ : syracuseStep 2316127 = 3474191) B3474191
theorem B3088169 : Blo 2057435 3088169 := bstep (se 2 (by rfl) ⟨1158063, by rfl⟩ : syracuseStep 3088169 = 2316127) B2316127
theorem B2058779 : Blo 2057435 2058779 := bstep (se 1 (by rfl) ⟨1544084, by rfl⟩ : syracuseStep 2058779 = 3088169) B3088169
theorem B5862709 : Blo 2057435 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B7816945 : Blo 2057435 7816945 := bstep (se 2 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 7816945 = 5862709) B5862709
theorem B10422593 : Blo 2057435 10422593 := bstep (se 2 (by rfl) ⟨3908472, by rfl⟩ : syracuseStep 10422593 = 7816945) B7816945
theorem B6948395 : Blo 2057435 6948395 := bstep (se 1 (by rfl) ⟨5211296, by rfl⟩ : syracuseStep 6948395 = 10422593) B10422593
theorem B4632263 : Blo 2057435 4632263 := bstep (se 1 (by rfl) ⟨3474197, by rfl⟩ : syracuseStep 4632263 = 6948395) B6948395
theorem B3088175 : Blo 2057435 3088175 := bstep (se 1 (by rfl) ⟨2316131, by rfl⟩ : syracuseStep 3088175 = 4632263) B4632263
theorem B2058783 : Blo 2057435 2058783 := bstep (se 1 (by rfl) ⟨1544087, by rfl⟩ : syracuseStep 2058783 = 3088175) B3088175
theorem B3088181 : Blo 2057435 3088181 := bbase (se 5 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 3088181 = 289517) (by norm_num)
theorem B2058787 : Blo 2057435 2058787 := bstep (se 1 (by rfl) ⟨1544090, by rfl⟩ : syracuseStep 2058787 = 3088181) B3088181
theorem B5211317 : Blo 2057435 5211317 := bbase (se 5 (by rfl) ⟨244280, by rfl⟩ : syracuseStep 5211317 = 488561) (by norm_num)
theorem B3474211 : Blo 2057435 3474211 := bstep (se 1 (by rfl) ⟨2605658, by rfl⟩ : syracuseStep 3474211 = 5211317) B5211317
theorem B4632281 : Blo 2057435 4632281 := bstep (se 2 (by rfl) ⟨1737105, by rfl⟩ : syracuseStep 4632281 = 3474211) B3474211
theorem B3088187 : Blo 2057435 3088187 := bstep (se 1 (by rfl) ⟨2316140, by rfl⟩ : syracuseStep 3088187 = 4632281) B4632281
theorem B2058791 : Blo 2057435 2058791 := bstep (se 1 (by rfl) ⟨1544093, by rfl⟩ : syracuseStep 2058791 = 3088187) B3088187
theorem B2316145 : Blo 2057435 2316145 := bbase (se 2 (by rfl) ⟨868554, by rfl⟩ : syracuseStep 2316145 = 1737109) (by norm_num)
theorem B3088193 : Blo 2057435 3088193 := bstep (se 2 (by rfl) ⟨1158072, by rfl⟩ : syracuseStep 3088193 = 2316145) B2316145
theorem B2058795 : Blo 2057435 2058795 := bstep (se 1 (by rfl) ⟨1544096, by rfl⟩ : syracuseStep 2058795 = 3088193) B3088193
theorem B8794133 : Blo 2057435 8794133 := bbase (se 6 (by rfl) ⟨206112, by rfl⟩ : syracuseStep 8794133 = 412225) (by norm_num)
theorem B5862755 : Blo 2057435 5862755 := bstep (se 1 (by rfl) ⟨4397066, by rfl⟩ : syracuseStep 5862755 = 8794133) B8794133
theorem B3908503 : Blo 2057435 3908503 := bstep (se 1 (by rfl) ⟨2931377, by rfl⟩ : syracuseStep 3908503 = 5862755) B5862755
theorem B5211337 : Blo 2057435 5211337 := bstep (se 2 (by rfl) ⟨1954251, by rfl⟩ : syracuseStep 5211337 = 3908503) B3908503
theorem B6948449 : Blo 2057435 6948449 := bstep (se 2 (by rfl) ⟨2605668, by rfl⟩ : syracuseStep 6948449 = 5211337) B5211337
theorem B4632299 : Blo 2057435 4632299 := bstep (se 1 (by rfl) ⟨3474224, by rfl⟩ : syracuseStep 4632299 = 6948449) B6948449
theorem B3088199 : Blo 2057435 3088199 := bstep (se 1 (by rfl) ⟨2316149, by rfl⟩ : syracuseStep 3088199 = 4632299) B4632299
theorem B2058799 : Blo 2057435 2058799 := bstep (se 1 (by rfl) ⟨1544099, by rfl⟩ : syracuseStep 2058799 = 3088199) B3088199
theorem B3088205 : Blo 2057435 3088205 := bbase (se 3 (by rfl) ⟨579038, by rfl⟩ : syracuseStep 3088205 = 1158077) (by norm_num)
theorem B2058803 : Blo 2057435 2058803 := bstep (se 1 (by rfl) ⟨1544102, by rfl⟩ : syracuseStep 2058803 = 3088205) B3088205
theorem B4632317 : Blo 2057435 4632317 := bbase (se 3 (by rfl) ⟨868559, by rfl⟩ : syracuseStep 4632317 = 1737119) (by norm_num)
theorem B3088211 : Blo 2057435 3088211 := bstep (se 1 (by rfl) ⟨2316158, by rfl⟩ : syracuseStep 3088211 = 4632317) B4632317
theorem B2058807 : Blo 2057435 2058807 := bstep (se 1 (by rfl) ⟨1544105, by rfl⟩ : syracuseStep 2058807 = 3088211) B3088211
theorem B3474245 : Blo 2057435 3474245 := bbase (se 4 (by rfl) ⟨325710, by rfl⟩ : syracuseStep 3474245 = 651421) (by norm_num)
theorem B2316163 : Blo 2057435 2316163 := bstep (se 1 (by rfl) ⟨1737122, by rfl⟩ : syracuseStep 2316163 = 3474245) B3474245
theorem B3088217 : Blo 2057435 3088217 := bstep (se 2 (by rfl) ⟨1158081, by rfl⟩ : syracuseStep 3088217 = 2316163) B2316163
theorem B2058811 : Blo 2057435 2058811 := bstep (se 1 (by rfl) ⟨1544108, by rfl⟩ : syracuseStep 2058811 = 3088217) B3088217
theorem B15634133 : Blo 2057435 15634133 := bbase (se 7 (by rfl) ⟨183212, by rfl⟩ : syracuseStep 15634133 = 366425) (by norm_num)
theorem B10422755 : Blo 2057435 10422755 := bstep (se 1 (by rfl) ⟨7817066, by rfl⟩ : syracuseStep 10422755 = 15634133) B15634133
theorem B6948503 : Blo 2057435 6948503 := bstep (se 1 (by rfl) ⟨5211377, by rfl⟩ : syracuseStep 6948503 = 10422755) B10422755
theorem B4632335 : Blo 2057435 4632335 := bstep (se 1 (by rfl) ⟨3474251, by rfl⟩ : syracuseStep 4632335 = 6948503) B6948503
theorem B3088223 : Blo 2057435 3088223 := bstep (se 1 (by rfl) ⟨2316167, by rfl⟩ : syracuseStep 3088223 = 4632335) B4632335
theorem B2058815 : Blo 2057435 2058815 := bstep (se 1 (by rfl) ⟨1544111, by rfl⟩ : syracuseStep 2058815 = 3088223) B3088223
theorem B3088229 : Blo 2057435 3088229 := bbase (se 4 (by rfl) ⟨289521, by rfl⟩ : syracuseStep 3088229 = 579043) (by norm_num)
theorem B2058819 : Blo 2057435 2058819 := bstep (se 1 (by rfl) ⟨1544114, by rfl⟩ : syracuseStep 2058819 = 3088229) B3088229
theorem B3908549 : Blo 2057435 3908549 := bbase (se 4 (by rfl) ⟨366426, by rfl⟩ : syracuseStep 3908549 = 732853) (by norm_num)
theorem B2605699 : Blo 2057435 2605699 := bstep (se 1 (by rfl) ⟨1954274, by rfl⟩ : syracuseStep 2605699 = 3908549) B3908549
theorem B3474265 : Blo 2057435 3474265 := bstep (se 2 (by rfl) ⟨1302849, by rfl⟩ : syracuseStep 3474265 = 2605699) B2605699
theorem B4632353 : Blo 2057435 4632353 := bstep (se 2 (by rfl) ⟨1737132, by rfl⟩ : syracuseStep 4632353 = 3474265) B3474265
theorem B3088235 : Blo 2057435 3088235 := bstep (se 1 (by rfl) ⟨2316176, by rfl⟩ : syracuseStep 3088235 = 4632353) B4632353
theorem B2058823 : Blo 2057435 2058823 := bstep (se 1 (by rfl) ⟨1544117, by rfl⟩ : syracuseStep 2058823 = 3088235) B3088235
theorem B2316181 : Blo 2057435 2316181 := bbase (se 6 (by rfl) ⟨54285, by rfl⟩ : syracuseStep 2316181 = 108571) (by norm_num)
theorem B3088241 : Blo 2057435 3088241 := bstep (se 2 (by rfl) ⟨1158090, by rfl⟩ : syracuseStep 3088241 = 2316181) B2316181
theorem B2058827 : Blo 2057435 2058827 := bstep (se 1 (by rfl) ⟨1544120, by rfl⟩ : syracuseStep 2058827 = 3088241) B3088241
theorem B2605709 : Blo 2057435 2605709 := bbase (se 3 (by rfl) ⟨488570, by rfl⟩ : syracuseStep 2605709 = 977141) (by norm_num)
theorem B6948557 : Blo 2057435 6948557 := bstep (se 3 (by rfl) ⟨1302854, by rfl⟩ : syracuseStep 6948557 = 2605709) B2605709
theorem B4632371 : Blo 2057435 4632371 := bstep (se 1 (by rfl) ⟨3474278, by rfl⟩ : syracuseStep 4632371 = 6948557) B6948557
theorem B3088247 : Blo 2057435 3088247 := bstep (se 1 (by rfl) ⟨2316185, by rfl⟩ : syracuseStep 3088247 = 4632371) B4632371
theorem B2058831 : Blo 2057435 2058831 := bstep (se 1 (by rfl) ⟨1544123, by rfl⟩ : syracuseStep 2058831 = 3088247) B3088247
theorem B3088253 : Blo 2057435 3088253 := bbase (se 3 (by rfl) ⟨579047, by rfl⟩ : syracuseStep 3088253 = 1158095) (by norm_num)
theorem B2058835 : Blo 2057435 2058835 := bstep (se 1 (by rfl) ⟨1544126, by rfl⟩ : syracuseStep 2058835 = 3088253) B3088253
theorem B4632389 : Blo 2057435 4632389 := bbase (se 4 (by rfl) ⟨434286, by rfl⟩ : syracuseStep 4632389 = 868573) (by norm_num)
theorem B3088259 : Blo 2057435 3088259 := bstep (se 1 (by rfl) ⟨2316194, by rfl⟩ : syracuseStep 3088259 = 4632389) B4632389
theorem B2058839 : Blo 2057435 2058839 := bstep (se 1 (by rfl) ⟨1544129, by rfl⟩ : syracuseStep 2058839 = 3088259) B3088259
theorem B4173869 : Blo 2057435 4173869 := bbase (se 3 (by rfl) ⟨782600, by rfl⟩ : syracuseStep 4173869 = 1565201) (by norm_num)
theorem B11130317 : Blo 2057435 11130317 := bstep (se 3 (by rfl) ⟨2086934, by rfl⟩ : syracuseStep 11130317 = 4173869) B4173869
theorem B7420211 : Blo 2057435 7420211 := bstep (se 1 (by rfl) ⟨5565158, by rfl⟩ : syracuseStep 7420211 = 11130317) B11130317
theorem B4946807 : Blo 2057435 4946807 := bstep (se 1 (by rfl) ⟨3710105, by rfl⟩ : syracuseStep 4946807 = 7420211) B7420211
theorem B3297871 : Blo 2057435 3297871 := bstep (se 1 (by rfl) ⟨2473403, by rfl⟩ : syracuseStep 3297871 = 4946807) B4946807
theorem B4397161 : Blo 2057435 4397161 := bstep (se 2 (by rfl) ⟨1648935, by rfl⟩ : syracuseStep 4397161 = 3297871) B3297871
theorem B5862881 : Blo 2057435 5862881 := bstep (se 2 (by rfl) ⟨2198580, by rfl⟩ : syracuseStep 5862881 = 4397161) B4397161
theorem B3908587 : Blo 2057435 3908587 := bstep (se 1 (by rfl) ⟨2931440, by rfl⟩ : syracuseStep 3908587 = 5862881) B5862881
theorem B5211449 : Blo 2057435 5211449 := bstep (se 2 (by rfl) ⟨1954293, by rfl⟩ : syracuseStep 5211449 = 3908587) B3908587
theorem B3474299 : Blo 2057435 3474299 := bstep (se 1 (by rfl) ⟨2605724, by rfl⟩ : syracuseStep 3474299 = 5211449) B5211449
theorem B2316199 : Blo 2057435 2316199 := bstep (se 1 (by rfl) ⟨1737149, by rfl⟩ : syracuseStep 2316199 = 3474299) B3474299
theorem B3088265 : Blo 2057435 3088265 := bstep (se 2 (by rfl) ⟨1158099, by rfl⟩ : syracuseStep 3088265 = 2316199) B2316199
theorem B2058843 : Blo 2057435 2058843 := bstep (se 1 (by rfl) ⟨1544132, by rfl⟩ : syracuseStep 2058843 = 3088265) B3088265
theorem B10422917 : Blo 2057435 10422917 := bbase (se 4 (by rfl) ⟨977148, by rfl⟩ : syracuseStep 10422917 = 1954297) (by norm_num)
theorem B6948611 : Blo 2057435 6948611 := bstep (se 1 (by rfl) ⟨5211458, by rfl⟩ : syracuseStep 6948611 = 10422917) B10422917
theorem B4632407 : Blo 2057435 4632407 := bstep (se 1 (by rfl) ⟨3474305, by rfl⟩ : syracuseStep 4632407 = 6948611) B6948611
theorem B3088271 : Blo 2057435 3088271 := bstep (se 1 (by rfl) ⟨2316203, by rfl⟩ : syracuseStep 3088271 = 4632407) B4632407
theorem B2058847 : Blo 2057435 2058847 := bstep (se 1 (by rfl) ⟨1544135, by rfl⟩ : syracuseStep 2058847 = 3088271) B3088271
theorem B3088277 : Blo 2057435 3088277 := bbase (se 6 (by rfl) ⟨72381, by rfl⟩ : syracuseStep 3088277 = 144763) (by norm_num)
theorem B2058851 : Blo 2057435 2058851 := bstep (se 1 (by rfl) ⟨1544138, by rfl⟩ : syracuseStep 2058851 = 3088277) B3088277
theorem B2198593 : Blo 2057435 2198593 := bbase (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) (by norm_num)
theorem B11725829 : Blo 2057435 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B7817219 : Blo 2057435 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B5211479 : Blo 2057435 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B3474319 : Blo 2057435 3474319 := bstep (se 1 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 3474319 = 5211479) B5211479
theorem B4632425 : Blo 2057435 4632425 := bstep (se 2 (by rfl) ⟨1737159, by rfl⟩ : syracuseStep 4632425 = 3474319) B3474319
theorem B3088283 : Blo 2057435 3088283 := bstep (se 1 (by rfl) ⟨2316212, by rfl⟩ : syracuseStep 3088283 = 4632425) B4632425
theorem B2058855 : Blo 2057435 2058855 := bstep (se 1 (by rfl) ⟨1544141, by rfl⟩ : syracuseStep 2058855 = 3088283) B3088283
theorem B2316217 : Blo 2057435 2316217 := bbase (se 2 (by rfl) ⟨868581, by rfl⟩ : syracuseStep 2316217 = 1737163) (by norm_num)
theorem B3088289 : Blo 2057435 3088289 := bstep (se 2 (by rfl) ⟨1158108, by rfl⟩ : syracuseStep 3088289 = 2316217) B2316217
theorem B2058859 : Blo 2057435 2058859 := bstep (se 1 (by rfl) ⟨1544144, by rfl⟩ : syracuseStep 2058859 = 3088289) B3088289
theorem B3710141 : Blo 2057435 3710141 := bbase (se 3 (by rfl) ⟨695651, by rfl⟩ : syracuseStep 3710141 = 1391303) (by norm_num)
theorem B2473427 : Blo 2057435 2473427 := bstep (se 1 (by rfl) ⟨1855070, by rfl⟩ : syracuseStep 2473427 = 3710141) B3710141
theorem B6595805 : Blo 2057435 6595805 := bstep (se 3 (by rfl) ⟨1236713, by rfl⟩ : syracuseStep 6595805 = 2473427) B2473427
theorem B4397203 : Blo 2057435 4397203 := bstep (se 1 (by rfl) ⟨3297902, by rfl⟩ : syracuseStep 4397203 = 6595805) B6595805
theorem B5862937 : Blo 2057435 5862937 := bstep (se 2 (by rfl) ⟨2198601, by rfl⟩ : syracuseStep 5862937 = 4397203) B4397203
theorem B7817249 : Blo 2057435 7817249 := bstep (se 2 (by rfl) ⟨2931468, by rfl⟩ : syracuseStep 7817249 = 5862937) B5862937
theorem B5211499 : Blo 2057435 5211499 := bstep (se 1 (by rfl) ⟨3908624, by rfl⟩ : syracuseStep 5211499 = 7817249) B7817249
theorem B6948665 : Blo 2057435 6948665 := bstep (se 2 (by rfl) ⟨2605749, by rfl⟩ : syracuseStep 6948665 = 5211499) B5211499
theorem B4632443 : Blo 2057435 4632443 := bstep (se 1 (by rfl) ⟨3474332, by rfl⟩ : syracuseStep 4632443 = 6948665) B6948665
theorem B3088295 : Blo 2057435 3088295 := bstep (se 1 (by rfl) ⟨2316221, by rfl⟩ : syracuseStep 3088295 = 4632443) B4632443
theorem B2058863 : Blo 2057435 2058863 := bstep (se 1 (by rfl) ⟨1544147, by rfl⟩ : syracuseStep 2058863 = 3088295) B3088295
theorem B3088301 : Blo 2057435 3088301 := bbase (se 3 (by rfl) ⟨579056, by rfl⟩ : syracuseStep 3088301 = 1158113) (by norm_num)
theorem B2058867 : Blo 2057435 2058867 := bstep (se 1 (by rfl) ⟨1544150, by rfl⟩ : syracuseStep 2058867 = 3088301) B3088301
theorem B4632461 : Blo 2057435 4632461 := bbase (se 3 (by rfl) ⟨868586, by rfl⟩ : syracuseStep 4632461 = 1737173) (by norm_num)
theorem B3088307 : Blo 2057435 3088307 := bstep (se 1 (by rfl) ⟨2316230, by rfl⟩ : syracuseStep 3088307 = 4632461) B4632461
theorem B2058871 : Blo 2057435 2058871 := bstep (se 1 (by rfl) ⟨1544153, by rfl⟩ : syracuseStep 2058871 = 3088307) B3088307
theorem B2605765 : Blo 2057435 2605765 := bbase (se 4 (by rfl) ⟨244290, by rfl⟩ : syracuseStep 2605765 = 488581) (by norm_num)
theorem B3474353 : Blo 2057435 3474353 := bstep (se 2 (by rfl) ⟨1302882, by rfl⟩ : syracuseStep 3474353 = 2605765) B2605765
theorem B2316235 : Blo 2057435 2316235 := bstep (se 1 (by rfl) ⟨1737176, by rfl⟩ : syracuseStep 2316235 = 3474353) B3474353
theorem B3088313 : Blo 2057435 3088313 := bstep (se 2 (by rfl) ⟨1158117, by rfl⟩ : syracuseStep 3088313 = 2316235) B2316235
theorem B2058875 : Blo 2057435 2058875 := bstep (se 1 (by rfl) ⟨1544156, by rfl⟩ : syracuseStep 2058875 = 3088313) B3088313
theorem B22261013 : Blo 2057435 22261013 := bbase (se 6 (by rfl) ⟨521742, by rfl⟩ : syracuseStep 22261013 = 1043485) (by norm_num)
theorem B14840675 : Blo 2057435 14840675 := bstep (se 1 (by rfl) ⟨11130506, by rfl⟩ : syracuseStep 14840675 = 22261013) B22261013
theorem B9893783 : Blo 2057435 9893783 := bstep (se 1 (by rfl) ⟨7420337, by rfl⟩ : syracuseStep 9893783 = 14840675) B14840675
theorem B26383421 : Blo 2057435 26383421 := bstep (se 3 (by rfl) ⟨4946891, by rfl⟩ : syracuseStep 26383421 = 9893783) B9893783
theorem B17588947 : Blo 2057435 17588947 := bstep (se 1 (by rfl) ⟨13191710, by rfl⟩ : syracuseStep 17588947 = 26383421) B26383421
theorem B23451929 : Blo 2057435 23451929 := bstep (se 2 (by rfl) ⟨8794473, by rfl⟩ : syracuseStep 23451929 = 17588947) B17588947
theorem B15634619 : Blo 2057435 15634619 := bstep (se 1 (by rfl) ⟨11725964, by rfl⟩ : syracuseStep 15634619 = 23451929) B23451929
theorem B10423079 : Blo 2057435 10423079 := bstep (se 1 (by rfl) ⟨7817309, by rfl⟩ : syracuseStep 10423079 = 15634619) B15634619
theorem B6948719 : Blo 2057435 6948719 := bstep (se 1 (by rfl) ⟨5211539, by rfl⟩ : syracuseStep 6948719 = 10423079) B10423079
theorem B4632479 : Blo 2057435 4632479 := bstep (se 1 (by rfl) ⟨3474359, by rfl⟩ : syracuseStep 4632479 = 6948719) B6948719
theorem B3088319 : Blo 2057435 3088319 := bstep (se 1 (by rfl) ⟨2316239, by rfl⟩ : syracuseStep 3088319 = 4632479) B4632479
theorem B2058879 : Blo 2057435 2058879 := bstep (se 1 (by rfl) ⟨1544159, by rfl⟩ : syracuseStep 2058879 = 3088319) B3088319
theorem B3088325 : Blo 2057435 3088325 := bbase (se 4 (by rfl) ⟨289530, by rfl⟩ : syracuseStep 3088325 = 579061) (by norm_num)
theorem B2058883 : Blo 2057435 2058883 := bstep (se 1 (by rfl) ⟨1544162, by rfl⟩ : syracuseStep 2058883 = 3088325) B3088325
theorem B3474373 : Blo 2057435 3474373 := bbase (se 4 (by rfl) ⟨325722, by rfl⟩ : syracuseStep 3474373 = 651445) (by norm_num)
theorem B4632497 : Blo 2057435 4632497 := bstep (se 2 (by rfl) ⟨1737186, by rfl⟩ : syracuseStep 4632497 = 3474373) B3474373
theorem B3088331 : Blo 2057435 3088331 := bstep (se 1 (by rfl) ⟨2316248, by rfl⟩ : syracuseStep 3088331 = 4632497) B4632497
theorem B2058887 : Blo 2057435 2058887 := bstep (se 1 (by rfl) ⟨1544165, by rfl⟩ : syracuseStep 2058887 = 3088331) B3088331
theorem B2316253 : Blo 2057435 2316253 := bbase (se 3 (by rfl) ⟨434297, by rfl⟩ : syracuseStep 2316253 = 868595) (by norm_num)
theorem B3088337 : Blo 2057435 3088337 := bstep (se 2 (by rfl) ⟨1158126, by rfl⟩ : syracuseStep 3088337 = 2316253) B2316253
theorem B2058891 : Blo 2057435 2058891 := bstep (se 1 (by rfl) ⟨1544168, by rfl⟩ : syracuseStep 2058891 = 3088337) B3088337
theorem B6948773 : Blo 2057435 6948773 := bbase (se 4 (by rfl) ⟨651447, by rfl⟩ : syracuseStep 6948773 = 1302895) (by norm_num)
theorem B4632515 : Blo 2057435 4632515 := bstep (se 1 (by rfl) ⟨3474386, by rfl⟩ : syracuseStep 4632515 = 6948773) B6948773
theorem B3088343 : Blo 2057435 3088343 := bstep (se 1 (by rfl) ⟨2316257, by rfl⟩ : syracuseStep 3088343 = 4632515) B4632515
theorem B2058895 : Blo 2057435 2058895 := bstep (se 1 (by rfl) ⟨1544171, by rfl⟩ : syracuseStep 2058895 = 3088343) B3088343
theorem B3088349 : Blo 2057435 3088349 := bbase (se 3 (by rfl) ⟨579065, by rfl⟩ : syracuseStep 3088349 = 1158131) (by norm_num)
theorem B2058899 : Blo 2057435 2058899 := bstep (se 1 (by rfl) ⟨1544174, by rfl⟩ : syracuseStep 2058899 = 3088349) B3088349
theorem B4632533 : Blo 2057435 4632533 := bbase (se 7 (by rfl) ⟨54287, by rfl⟩ : syracuseStep 4632533 = 108575) (by norm_num)
theorem B3088355 : Blo 2057435 3088355 := bstep (se 1 (by rfl) ⟨2316266, by rfl⟩ : syracuseStep 3088355 = 4632533) B4632533
theorem B2058903 : Blo 2057435 2058903 := bstep (se 1 (by rfl) ⟨1544177, by rfl⟩ : syracuseStep 2058903 = 3088355) B3088355
theorem B13191893 : Blo 2057435 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B8794595 : Blo 2057435 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B5863063 : Blo 2057435 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B7817417 : Blo 2057435 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B5211611 : Blo 2057435 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B3474407 : Blo 2057435 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B2316271 : Blo 2057435 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B3088361 : Blo 2057435 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B2058907 : Blo 2057435 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B9519653 : Blo 2057435 9519653 := bbase (se 4 (by rfl) ⟨892467, by rfl⟩ : syracuseStep 9519653 = 1784935) (by norm_num)
theorem B6346435 : Blo 2057435 6346435 := bstep (se 1 (by rfl) ⟨4759826, by rfl⟩ : syracuseStep 6346435 = 9519653) B9519653
theorem B8461913 : Blo 2057435 8461913 := bstep (se 2 (by rfl) ⟨3173217, by rfl⟩ : syracuseStep 8461913 = 6346435) B6346435
theorem B22565101 : Blo 2057435 22565101 := bstep (se 3 (by rfl) ⟨4230956, by rfl⟩ : syracuseStep 22565101 = 8461913) B8461913
theorem B30086801 : Blo 2057435 30086801 := bstep (se 2 (by rfl) ⟨11282550, by rfl⟩ : syracuseStep 30086801 = 22565101) B22565101
theorem B20057867 : Blo 2057435 20057867 := bstep (se 1 (by rfl) ⟨15043400, by rfl⟩ : syracuseStep 20057867 = 30086801) B30086801
theorem B13371911 : Blo 2057435 13371911 := bstep (se 1 (by rfl) ⟨10028933, by rfl⟩ : syracuseStep 13371911 = 20057867) B20057867
theorem B8914607 : Blo 2057435 8914607 := bstep (se 1 (by rfl) ⟨6685955, by rfl⟩ : syracuseStep 8914607 = 13371911) B13371911
theorem B5943071 : Blo 2057435 5943071 := bstep (se 1 (by rfl) ⟨4457303, by rfl⟩ : syracuseStep 5943071 = 8914607) B8914607
theorem B3962047 : Blo 2057435 3962047 := bstep (se 1 (by rfl) ⟨2971535, by rfl⟩ : syracuseStep 3962047 = 5943071) B5943071
theorem B5282729 : Blo 2057435 5282729 := bstep (se 2 (by rfl) ⟨1981023, by rfl⟩ : syracuseStep 5282729 = 3962047) B3962047
theorem B3521819 : Blo 2057435 3521819 := bstep (se 1 (by rfl) ⟨2641364, by rfl⟩ : syracuseStep 3521819 = 5282729) B5282729
theorem B2347879 : Blo 2057435 2347879 := bstep (se 1 (by rfl) ⟨1760909, by rfl⟩ : syracuseStep 2347879 = 3521819) B3521819
theorem B3130505 : Blo 2057435 3130505 := bstep (se 2 (by rfl) ⟨1173939, by rfl⟩ : syracuseStep 3130505 = 2347879) B2347879
theorem B2087003 : Blo 2057435 2087003 := bstep (se 1 (by rfl) ⟨1565252, by rfl⟩ : syracuseStep 2087003 = 3130505) B3130505
theorem B5565341 : Blo 2057435 5565341 := bstep (se 3 (by rfl) ⟨1043501, by rfl⟩ : syracuseStep 5565341 = 2087003) B2087003
theorem B3710227 : Blo 2057435 3710227 := bstep (se 1 (by rfl) ⟨2782670, by rfl⟩ : syracuseStep 3710227 = 5565341) B5565341
theorem B4946969 : Blo 2057435 4946969 := bstep (se 2 (by rfl) ⟨1855113, by rfl⟩ : syracuseStep 4946969 = 3710227) B3710227
theorem B3297979 : Blo 2057435 3297979 := bstep (se 1 (by rfl) ⟨2473484, by rfl⟩ : syracuseStep 3297979 = 4946969) B4946969
theorem B17589221 : Blo 2057435 17589221 := bstep (se 4 (by rfl) ⟨1648989, by rfl⟩ : syracuseStep 17589221 = 3297979) B3297979
theorem B11726147 : Blo 2057435 11726147 := bstep (se 1 (by rfl) ⟨8794610, by rfl⟩ : syracuseStep 11726147 = 17589221) B17589221
theorem B7817431 : Blo 2057435 7817431 := bstep (se 1 (by rfl) ⟨5863073, by rfl⟩ : syracuseStep 7817431 = 11726147) B11726147
theorem B10423241 : Blo 2057435 10423241 := bstep (se 2 (by rfl) ⟨3908715, by rfl⟩ : syracuseStep 10423241 = 7817431) B7817431
theorem B6948827 : Blo 2057435 6948827 := bstep (se 1 (by rfl) ⟨5211620, by rfl⟩ : syracuseStep 6948827 = 10423241) B10423241
theorem B4632551 : Blo 2057435 4632551 := bstep (se 1 (by rfl) ⟨3474413, by rfl⟩ : syracuseStep 4632551 = 6948827) B6948827
theorem B3088367 : Blo 2057435 3088367 := bstep (se 1 (by rfl) ⟨2316275, by rfl⟩ : syracuseStep 3088367 = 4632551) B4632551
theorem B2058911 : Blo 2057435 2058911 := bstep (se 1 (by rfl) ⟨1544183, by rfl⟩ : syracuseStep 2058911 = 3088367) B3088367
theorem B3088373 : Blo 2057435 3088373 := bbase (se 5 (by rfl) ⟨144767, by rfl⟩ : syracuseStep 3088373 = 289535) (by norm_num)
theorem B2058915 : Blo 2057435 2058915 := bstep (se 1 (by rfl) ⟨1544186, by rfl⟩ : syracuseStep 2058915 = 3088373) B3088373
theorem B4946989 : Blo 2057435 4946989 := bbase (se 3 (by rfl) ⟨927560, by rfl⟩ : syracuseStep 4946989 = 1855121) (by norm_num)
theorem B6595985 : Blo 2057435 6595985 := bstep (se 2 (by rfl) ⟨2473494, by rfl⟩ : syracuseStep 6595985 = 4946989) B4946989
theorem B4397323 : Blo 2057435 4397323 := bstep (se 1 (by rfl) ⟨3297992, by rfl⟩ : syracuseStep 4397323 = 6595985) B6595985
theorem B5863097 : Blo 2057435 5863097 := bstep (se 2 (by rfl) ⟨2198661, by rfl⟩ : syracuseStep 5863097 = 4397323) B4397323
theorem B3908731 : Blo 2057435 3908731 := bstep (se 1 (by rfl) ⟨2931548, by rfl⟩ : syracuseStep 3908731 = 5863097) B5863097
theorem B5211641 : Blo 2057435 5211641 := bstep (se 2 (by rfl) ⟨1954365, by rfl⟩ : syracuseStep 5211641 = 3908731) B3908731
theorem B3474427 : Blo 2057435 3474427 := bstep (se 1 (by rfl) ⟨2605820, by rfl⟩ : syracuseStep 3474427 = 5211641) B5211641
theorem B4632569 : Blo 2057435 4632569 := bstep (se 2 (by rfl) ⟨1737213, by rfl⟩ : syracuseStep 4632569 = 3474427) B3474427
theorem B3088379 : Blo 2057435 3088379 := bstep (se 1 (by rfl) ⟨2316284, by rfl⟩ : syracuseStep 3088379 = 4632569) B4632569
theorem B2058919 : Blo 2057435 2058919 := bstep (se 1 (by rfl) ⟨1544189, by rfl⟩ : syracuseStep 2058919 = 3088379) B3088379
theorem B2316289 : Blo 2057435 2316289 := bbase (se 2 (by rfl) ⟨868608, by rfl⟩ : syracuseStep 2316289 = 1737217) (by norm_num)
theorem B3088385 : Blo 2057435 3088385 := bstep (se 2 (by rfl) ⟨1158144, by rfl⟩ : syracuseStep 3088385 = 2316289) B2316289
theorem B2058923 : Blo 2057435 2058923 := bstep (se 1 (by rfl) ⟨1544192, by rfl⟩ : syracuseStep 2058923 = 3088385) B3088385
theorem B5211661 : Blo 2057435 5211661 := bbase (se 3 (by rfl) ⟨977186, by rfl⟩ : syracuseStep 5211661 = 1954373) (by norm_num)
theorem B6948881 : Blo 2057435 6948881 := bstep (se 2 (by rfl) ⟨2605830, by rfl⟩ : syracuseStep 6948881 = 5211661) B5211661
theorem B4632587 : Blo 2057435 4632587 := bstep (se 1 (by rfl) ⟨3474440, by rfl⟩ : syracuseStep 4632587 = 6948881) B6948881
theorem B3088391 : Blo 2057435 3088391 := bstep (se 1 (by rfl) ⟨2316293, by rfl⟩ : syracuseStep 3088391 = 4632587) B4632587
theorem B2058927 : Blo 2057435 2058927 := bstep (se 1 (by rfl) ⟨1544195, by rfl⟩ : syracuseStep 2058927 = 3088391) B3088391
theorem B3088397 : Blo 2057435 3088397 := bbase (se 3 (by rfl) ⟨579074, by rfl⟩ : syracuseStep 3088397 = 1158149) (by norm_num)
theorem B2058931 : Blo 2057435 2058931 := bstep (se 1 (by rfl) ⟨1544198, by rfl⟩ : syracuseStep 2058931 = 3088397) B3088397
theorem B4632605 : Blo 2057435 4632605 := bbase (se 3 (by rfl) ⟨868613, by rfl⟩ : syracuseStep 4632605 = 1737227) (by norm_num)
theorem B3088403 : Blo 2057435 3088403 := bstep (se 1 (by rfl) ⟨2316302, by rfl⟩ : syracuseStep 3088403 = 4632605) B4632605
theorem B2058935 : Blo 2057435 2058935 := bstep (se 1 (by rfl) ⟨1544201, by rfl⟩ : syracuseStep 2058935 = 3088403) B3088403
theorem B3474461 : Blo 2057435 3474461 := bbase (se 3 (by rfl) ⟨651461, by rfl⟩ : syracuseStep 3474461 = 1302923) (by norm_num)
theorem B2316307 : Blo 2057435 2316307 := bstep (se 1 (by rfl) ⟨1737230, by rfl⟩ : syracuseStep 2316307 = 3474461) B3474461
theorem B3088409 : Blo 2057435 3088409 := bstep (se 2 (by rfl) ⟨1158153, by rfl⟩ : syracuseStep 3088409 = 2316307) B2316307
theorem B2058939 : Blo 2057435 2058939 := bstep (se 1 (by rfl) ⟨1544204, by rfl⟩ : syracuseStep 2058939 = 3088409) B3088409
theorem B2641405 : Blo 2057435 2641405 := bbase (se 3 (by rfl) ⟨495263, by rfl⟩ : syracuseStep 2641405 = 990527) (by norm_num)
theorem B3521873 : Blo 2057435 3521873 := bstep (se 2 (by rfl) ⟨1320702, by rfl⟩ : syracuseStep 3521873 = 2641405) B2641405
theorem B2347915 : Blo 2057435 2347915 := bstep (se 1 (by rfl) ⟨1760936, by rfl⟩ : syracuseStep 2347915 = 3521873) B3521873
theorem B3130553 : Blo 2057435 3130553 := bstep (se 2 (by rfl) ⟨1173957, by rfl⟩ : syracuseStep 3130553 = 2347915) B2347915
theorem B2087035 : Blo 2057435 2087035 := bstep (se 1 (by rfl) ⟨1565276, by rfl⟩ : syracuseStep 2087035 = 3130553) B3130553
theorem B11130853 : Blo 2057435 11130853 := bstep (se 4 (by rfl) ⟨1043517, by rfl⟩ : syracuseStep 11130853 = 2087035) B2087035
theorem B14841137 : Blo 2057435 14841137 := bstep (se 2 (by rfl) ⟨5565426, by rfl⟩ : syracuseStep 14841137 = 11130853) B11130853
theorem B9894091 : Blo 2057435 9894091 := bstep (se 1 (by rfl) ⟨7420568, by rfl⟩ : syracuseStep 9894091 = 14841137) B14841137
theorem B13192121 : Blo 2057435 13192121 := bstep (se 2 (by rfl) ⟨4947045, by rfl⟩ : syracuseStep 13192121 = 9894091) B9894091
theorem B8794747 : Blo 2057435 8794747 := bstep (se 1 (by rfl) ⟨6596060, by rfl⟩ : syracuseStep 8794747 = 13192121) B13192121
theorem B11726329 : Blo 2057435 11726329 := bstep (se 2 (by rfl) ⟨4397373, by rfl⟩ : syracuseStep 11726329 = 8794747) B8794747
theorem B15635105 : Blo 2057435 15635105 := bstep (se 2 (by rfl) ⟨5863164, by rfl⟩ : syracuseStep 15635105 = 11726329) B11726329
theorem B10423403 : Blo 2057435 10423403 := bstep (se 1 (by rfl) ⟨7817552, by rfl⟩ : syracuseStep 10423403 = 15635105) B15635105
theorem B6948935 : Blo 2057435 6948935 := bstep (se 1 (by rfl) ⟨5211701, by rfl⟩ : syracuseStep 6948935 = 10423403) B10423403
theorem B4632623 : Blo 2057435 4632623 := bstep (se 1 (by rfl) ⟨3474467, by rfl⟩ : syracuseStep 4632623 = 6948935) B6948935
theorem B3088415 : Blo 2057435 3088415 := bstep (se 1 (by rfl) ⟨2316311, by rfl⟩ : syracuseStep 3088415 = 4632623) B4632623
theorem B2058943 : Blo 2057435 2058943 := bstep (se 1 (by rfl) ⟨1544207, by rfl⟩ : syracuseStep 2058943 = 3088415) B3088415
theorem B3088421 : Blo 2057435 3088421 := bbase (se 4 (by rfl) ⟨289539, by rfl⟩ : syracuseStep 3088421 = 579079) (by norm_num)
theorem B2058947 : Blo 2057435 2058947 := bstep (se 1 (by rfl) ⟨1544210, by rfl⟩ : syracuseStep 2058947 = 3088421) B3088421
theorem B2605861 : Blo 2057435 2605861 := bbase (se 4 (by rfl) ⟨244299, by rfl⟩ : syracuseStep 2605861 = 488599) (by norm_num)
theorem B3474481 : Blo 2057435 3474481 := bstep (se 2 (by rfl) ⟨1302930, by rfl⟩ : syracuseStep 3474481 = 2605861) B2605861
theorem B4632641 : Blo 2057435 4632641 := bstep (se 2 (by rfl) ⟨1737240, by rfl⟩ : syracuseStep 4632641 = 3474481) B3474481
theorem B3088427 : Blo 2057435 3088427 := bstep (se 1 (by rfl) ⟨2316320, by rfl⟩ : syracuseStep 3088427 = 4632641) B4632641
theorem B2058951 : Blo 2057435 2058951 := bstep (se 1 (by rfl) ⟨1544213, by rfl⟩ : syracuseStep 2058951 = 3088427) B3088427
theorem B2316325 : Blo 2057435 2316325 := bbase (se 4 (by rfl) ⟨217155, by rfl⟩ : syracuseStep 2316325 = 434311) (by norm_num)
theorem B3088433 : Blo 2057435 3088433 := bstep (se 2 (by rfl) ⟨1158162, by rfl⟩ : syracuseStep 3088433 = 2316325) B2316325
theorem B2058955 : Blo 2057435 2058955 := bstep (se 1 (by rfl) ⟨1544216, by rfl⟩ : syracuseStep 2058955 = 3088433) B3088433
theorem B4947085 : Blo 2057435 4947085 := bbase (se 3 (by rfl) ⟨927578, by rfl⟩ : syracuseStep 4947085 = 1855157) (by norm_num)
theorem B6596113 : Blo 2057435 6596113 := bstep (se 2 (by rfl) ⟨2473542, by rfl⟩ : syracuseStep 6596113 = 4947085) B4947085
theorem B8794817 : Blo 2057435 8794817 := bstep (se 2 (by rfl) ⟨3298056, by rfl⟩ : syracuseStep 8794817 = 6596113) B6596113
theorem B5863211 : Blo 2057435 5863211 := bstep (se 1 (by rfl) ⟨4397408, by rfl⟩ : syracuseStep 5863211 = 8794817) B8794817
theorem B3908807 : Blo 2057435 3908807 := bstep (se 1 (by rfl) ⟨2931605, by rfl⟩ : syracuseStep 3908807 = 5863211) B5863211
theorem B2605871 : Blo 2057435 2605871 := bstep (se 1 (by rfl) ⟨1954403, by rfl⟩ : syracuseStep 2605871 = 3908807) B3908807
theorem B6948989 : Blo 2057435 6948989 := bstep (se 3 (by rfl) ⟨1302935, by rfl⟩ : syracuseStep 6948989 = 2605871) B2605871
theorem B4632659 : Blo 2057435 4632659 := bstep (se 1 (by rfl) ⟨3474494, by rfl⟩ : syracuseStep 4632659 = 6948989) B6948989
theorem B3088439 : Blo 2057435 3088439 := bstep (se 1 (by rfl) ⟨2316329, by rfl⟩ : syracuseStep 3088439 = 4632659) B4632659
theorem B2058959 : Blo 2057435 2058959 := bstep (se 1 (by rfl) ⟨1544219, by rfl⟩ : syracuseStep 2058959 = 3088439) B3088439
theorem B3088445 : Blo 2057435 3088445 := bbase (se 3 (by rfl) ⟨579083, by rfl⟩ : syracuseStep 3088445 = 1158167) (by norm_num)
theorem B2058963 : Blo 2057435 2058963 := bstep (se 1 (by rfl) ⟨1544222, by rfl⟩ : syracuseStep 2058963 = 3088445) B3088445
theorem B4632677 : Blo 2057435 4632677 := bbase (se 4 (by rfl) ⟨434313, by rfl⟩ : syracuseStep 4632677 = 868627) (by norm_num)
theorem B3088451 : Blo 2057435 3088451 := bstep (se 1 (by rfl) ⟨2316338, by rfl⟩ : syracuseStep 3088451 = 4632677) B4632677
theorem B2058967 : Blo 2057435 2058967 := bstep (se 1 (by rfl) ⟨1544225, by rfl⟩ : syracuseStep 2058967 = 3088451) B3088451
theorem B5211773 : Blo 2057435 5211773 := bbase (se 3 (by rfl) ⟨977207, by rfl⟩ : syracuseStep 5211773 = 1954415) (by norm_num)
theorem B3474515 : Blo 2057435 3474515 := bstep (se 1 (by rfl) ⟨2605886, by rfl⟩ : syracuseStep 3474515 = 5211773) B5211773
theorem B2316343 : Blo 2057435 2316343 := bstep (se 1 (by rfl) ⟨1737257, by rfl⟩ : syracuseStep 2316343 = 3474515) B3474515
theorem B3088457 : Blo 2057435 3088457 := bstep (se 2 (by rfl) ⟨1158171, by rfl⟩ : syracuseStep 3088457 = 2316343) B2316343
theorem B2058971 : Blo 2057435 2058971 := bstep (se 1 (by rfl) ⟨1544228, by rfl⟩ : syracuseStep 2058971 = 3088457) B3088457
theorem B3908837 : Blo 2057435 3908837 := bbase (se 4 (by rfl) ⟨366453, by rfl⟩ : syracuseStep 3908837 = 732907) (by norm_num)
theorem B10423565 : Blo 2057435 10423565 := bstep (se 3 (by rfl) ⟨1954418, by rfl⟩ : syracuseStep 10423565 = 3908837) B3908837
theorem B6949043 : Blo 2057435 6949043 := bstep (se 1 (by rfl) ⟨5211782, by rfl⟩ : syracuseStep 6949043 = 10423565) B10423565
theorem B4632695 : Blo 2057435 4632695 := bstep (se 1 (by rfl) ⟨3474521, by rfl⟩ : syracuseStep 4632695 = 6949043) B6949043
theorem B3088463 : Blo 2057435 3088463 := bstep (se 1 (by rfl) ⟨2316347, by rfl⟩ : syracuseStep 3088463 = 4632695) B4632695
theorem B2058975 : Blo 2057435 2058975 := bstep (se 1 (by rfl) ⟨1544231, by rfl⟩ : syracuseStep 2058975 = 3088463) B3088463
theorem B3088469 : Blo 2057435 3088469 := bbase (se 8 (by rfl) ⟨18096, by rfl⟩ : syracuseStep 3088469 = 36193) (by norm_num)
theorem B2058979 : Blo 2057435 2058979 := bstep (se 1 (by rfl) ⟨1544234, by rfl⟩ : syracuseStep 2058979 = 3088469) B3088469
theorem B21419957 : Blo 2057435 21419957 := bbase (se 5 (by rfl) ⟨1004060, by rfl⟩ : syracuseStep 21419957 = 2008121) (by norm_num)
theorem B14279971 : Blo 2057435 14279971 := bstep (se 1 (by rfl) ⟨10709978, by rfl⟩ : syracuseStep 14279971 = 21419957) B21419957
theorem B19039961 : Blo 2057435 19039961 := bstep (se 2 (by rfl) ⟨7139985, by rfl⟩ : syracuseStep 19039961 = 14279971) B14279971
theorem B12693307 : Blo 2057435 12693307 := bstep (se 1 (by rfl) ⟨9519980, by rfl⟩ : syracuseStep 12693307 = 19039961) B19039961
theorem B16924409 : Blo 2057435 16924409 := bstep (se 2 (by rfl) ⟨6346653, by rfl⟩ : syracuseStep 16924409 = 12693307) B12693307
theorem B11282939 : Blo 2057435 11282939 := bstep (se 1 (by rfl) ⟨8462204, by rfl⟩ : syracuseStep 11282939 = 16924409) B16924409
theorem B7521959 : Blo 2057435 7521959 := bstep (se 1 (by rfl) ⟨5641469, by rfl⟩ : syracuseStep 7521959 = 11282939) B11282939
theorem B5014639 : Blo 2057435 5014639 := bstep (se 1 (by rfl) ⟨3760979, by rfl⟩ : syracuseStep 5014639 = 7521959) B7521959
theorem B26744741 : Blo 2057435 26744741 := bstep (se 4 (by rfl) ⟨2507319, by rfl⟩ : syracuseStep 26744741 = 5014639) B5014639
theorem B17829827 : Blo 2057435 17829827 := bstep (se 1 (by rfl) ⟨13372370, by rfl⟩ : syracuseStep 17829827 = 26744741) B26744741
theorem B11886551 : Blo 2057435 11886551 := bstep (se 1 (by rfl) ⟨8914913, by rfl⟩ : syracuseStep 11886551 = 17829827) B17829827
theorem B7924367 : Blo 2057435 7924367 := bstep (se 1 (by rfl) ⟨5943275, by rfl⟩ : syracuseStep 7924367 = 11886551) B11886551
theorem B5282911 : Blo 2057435 5282911 := bstep (se 1 (by rfl) ⟨3962183, by rfl⟩ : syracuseStep 5282911 = 7924367) B7924367
theorem B28175525 : Blo 2057435 28175525 := bstep (se 4 (by rfl) ⟨2641455, by rfl⟩ : syracuseStep 28175525 = 5282911) B5282911
theorem B18783683 : Blo 2057435 18783683 := bstep (se 1 (by rfl) ⟨14087762, by rfl⟩ : syracuseStep 18783683 = 28175525) B28175525
theorem B12522455 : Blo 2057435 12522455 := bstep (se 1 (by rfl) ⟨9391841, by rfl⟩ : syracuseStep 12522455 = 18783683) B18783683
theorem B8348303 : Blo 2057435 8348303 := bstep (se 1 (by rfl) ⟨6261227, by rfl⟩ : syracuseStep 8348303 = 12522455) B12522455
theorem B22262141 : Blo 2057435 22262141 := bstep (se 3 (by rfl) ⟨4174151, by rfl⟩ : syracuseStep 22262141 = 8348303) B8348303
theorem B14841427 : Blo 2057435 14841427 := bstep (se 1 (by rfl) ⟨11131070, by rfl⟩ : syracuseStep 14841427 = 22262141) B22262141
theorem B19788569 : Blo 2057435 19788569 := bstep (se 2 (by rfl) ⟨7420713, by rfl⟩ : syracuseStep 19788569 = 14841427) B14841427
theorem B13192379 : Blo 2057435 13192379 := bstep (se 1 (by rfl) ⟨9894284, by rfl⟩ : syracuseStep 13192379 = 19788569) B19788569
theorem B8794919 : Blo 2057435 8794919 := bstep (se 1 (by rfl) ⟨6596189, by rfl⟩ : syracuseStep 8794919 = 13192379) B13192379
theorem B5863279 : Blo 2057435 5863279 := bstep (se 1 (by rfl) ⟨4397459, by rfl⟩ : syracuseStep 5863279 = 8794919) B8794919
theorem B7817705 : Blo 2057435 7817705 := bstep (se 2 (by rfl) ⟨2931639, by rfl⟩ : syracuseStep 7817705 = 5863279) B5863279
theorem B5211803 : Blo 2057435 5211803 := bstep (se 1 (by rfl) ⟨3908852, by rfl⟩ : syracuseStep 5211803 = 7817705) B7817705
theorem B3474535 : Blo 2057435 3474535 := bstep (se 1 (by rfl) ⟨2605901, by rfl⟩ : syracuseStep 3474535 = 5211803) B5211803
theorem B4632713 : Blo 2057435 4632713 := bstep (se 2 (by rfl) ⟨1737267, by rfl⟩ : syracuseStep 4632713 = 3474535) B3474535
theorem B3088475 : Blo 2057435 3088475 := bstep (se 1 (by rfl) ⟨2316356, by rfl⟩ : syracuseStep 3088475 = 4632713) B4632713
theorem B2058983 : Blo 2057435 2058983 := bstep (se 1 (by rfl) ⟨1544237, by rfl⟩ : syracuseStep 2058983 = 3088475) B3088475
theorem B2316361 : Blo 2057435 2316361 := bbase (se 2 (by rfl) ⟨868635, by rfl⟩ : syracuseStep 2316361 = 1737271) (by norm_num)
theorem B3088481 : Blo 2057435 3088481 := bstep (se 2 (by rfl) ⟨1158180, by rfl⟩ : syracuseStep 3088481 = 2316361) B2316361
theorem B2058987 : Blo 2057435 2058987 := bstep (se 1 (by rfl) ⟨1544240, by rfl⟩ : syracuseStep 2058987 = 3088481) B3088481
theorem B5565557 : Blo 2057435 5565557 := bbase (se 5 (by rfl) ⟨260885, by rfl⟩ : syracuseStep 5565557 = 521771) (by norm_num)
theorem B3710371 : Blo 2057435 3710371 := bstep (se 1 (by rfl) ⟨2782778, by rfl⟩ : syracuseStep 3710371 = 5565557) B5565557
theorem B4947161 : Blo 2057435 4947161 := bstep (se 2 (by rfl) ⟨1855185, by rfl⟩ : syracuseStep 4947161 = 3710371) B3710371
theorem B13192429 : Blo 2057435 13192429 := bstep (se 3 (by rfl) ⟨2473580, by rfl⟩ : syracuseStep 13192429 = 4947161) B4947161
theorem B17589905 : Blo 2057435 17589905 := bstep (se 2 (by rfl) ⟨6596214, by rfl⟩ : syracuseStep 17589905 = 13192429) B13192429
theorem B11726603 : Blo 2057435 11726603 := bstep (se 1 (by rfl) ⟨8794952, by rfl⟩ : syracuseStep 11726603 = 17589905) B17589905
theorem B7817735 : Blo 2057435 7817735 := bstep (se 1 (by rfl) ⟨5863301, by rfl⟩ : syracuseStep 7817735 = 11726603) B11726603
theorem B5211823 : Blo 2057435 5211823 := bstep (se 1 (by rfl) ⟨3908867, by rfl⟩ : syracuseStep 5211823 = 7817735) B7817735
theorem B6949097 : Blo 2057435 6949097 := bstep (se 2 (by rfl) ⟨2605911, by rfl⟩ : syracuseStep 6949097 = 5211823) B5211823
theorem B4632731 : Blo 2057435 4632731 := bstep (se 1 (by rfl) ⟨3474548, by rfl⟩ : syracuseStep 4632731 = 6949097) B6949097
theorem B3088487 : Blo 2057435 3088487 := bstep (se 1 (by rfl) ⟨2316365, by rfl⟩ : syracuseStep 3088487 = 4632731) B4632731
theorem B2058991 : Blo 2057435 2058991 := bstep (se 1 (by rfl) ⟨1544243, by rfl⟩ : syracuseStep 2058991 = 3088487) B3088487
theorem B3088493 : Blo 2057435 3088493 := bbase (se 3 (by rfl) ⟨579092, by rfl⟩ : syracuseStep 3088493 = 1158185) (by norm_num)
theorem B2058995 : Blo 2057435 2058995 := bstep (se 1 (by rfl) ⟨1544246, by rfl⟩ : syracuseStep 2058995 = 3088493) B3088493
theorem B4632749 : Blo 2057435 4632749 := bbase (se 3 (by rfl) ⟨868640, by rfl⟩ : syracuseStep 4632749 = 1737281) (by norm_num)
theorem B3088499 : Blo 2057435 3088499 := bstep (se 1 (by rfl) ⟨2316374, by rfl⟩ : syracuseStep 3088499 = 4632749) B4632749
theorem B2058999 : Blo 2057435 2058999 := bstep (se 1 (by rfl) ⟨1544249, by rfl⟩ : syracuseStep 2058999 = 3088499) B3088499
theorem B50773717 : Blo 2057435 50773717 := bbase (se 7 (by rfl) ⟨595004, by rfl⟩ : syracuseStep 50773717 = 1190009) (by norm_num)
theorem B67698289 : Blo 2057435 67698289 := bstep (se 2 (by rfl) ⟨25386858, by rfl⟩ : syracuseStep 67698289 = 50773717) B50773717
theorem B90264385 : Blo 2057435 90264385 := bstep (se 2 (by rfl) ⟨33849144, by rfl⟩ : syracuseStep 90264385 = 67698289) B67698289
theorem B120352513 : Blo 2057435 120352513 := bstep (se 2 (by rfl) ⟨45132192, by rfl⟩ : syracuseStep 120352513 = 90264385) B90264385
theorem B160470017 : Blo 2057435 160470017 := bstep (se 2 (by rfl) ⟨60176256, by rfl⟩ : syracuseStep 160470017 = 120352513) B120352513
theorem B106980011 : Blo 2057435 106980011 := bstep (se 1 (by rfl) ⟨80235008, by rfl⟩ : syracuseStep 106980011 = 160470017) B160470017
theorem B71320007 : Blo 2057435 71320007 := bstep (se 1 (by rfl) ⟨53490005, by rfl⟩ : syracuseStep 71320007 = 106980011) B106980011
theorem B47546671 : Blo 2057435 47546671 := bstep (se 1 (by rfl) ⟨35660003, by rfl⟩ : syracuseStep 47546671 = 71320007) B71320007
theorem B63395561 : Blo 2057435 63395561 := bstep (se 2 (by rfl) ⟨23773335, by rfl⟩ : syracuseStep 63395561 = 47546671) B47546671
theorem B42263707 : Blo 2057435 42263707 := bstep (se 1 (by rfl) ⟨31697780, by rfl⟩ : syracuseStep 42263707 = 63395561) B63395561
theorem B56351609 : Blo 2057435 56351609 := bstep (se 2 (by rfl) ⟨21131853, by rfl⟩ : syracuseStep 56351609 = 42263707) B42263707
theorem B37567739 : Blo 2057435 37567739 := bstep (se 1 (by rfl) ⟨28175804, by rfl⟩ : syracuseStep 37567739 = 56351609) B56351609
theorem B25045159 : Blo 2057435 25045159 := bstep (se 1 (by rfl) ⟨18783869, by rfl⟩ : syracuseStep 25045159 = 37567739) B37567739
theorem B33393545 : Blo 2057435 33393545 := bstep (se 2 (by rfl) ⟨12522579, by rfl⟩ : syracuseStep 33393545 = 25045159) B25045159
theorem B22262363 : Blo 2057435 22262363 := bstep (se 1 (by rfl) ⟨16696772, by rfl⟩ : syracuseStep 22262363 = 33393545) B33393545
theorem B14841575 : Blo 2057435 14841575 := bstep (se 1 (by rfl) ⟨11131181, by rfl⟩ : syracuseStep 14841575 = 22262363) B22262363
theorem B9894383 : Blo 2057435 9894383 := bstep (se 1 (by rfl) ⟨7420787, by rfl⟩ : syracuseStep 9894383 = 14841575) B14841575
theorem B6596255 : Blo 2057435 6596255 := bstep (se 1 (by rfl) ⟨4947191, by rfl⟩ : syracuseStep 6596255 = 9894383) B9894383
theorem B4397503 : Blo 2057435 4397503 := bstep (se 1 (by rfl) ⟨3298127, by rfl⟩ : syracuseStep 4397503 = 6596255) B6596255
theorem B5863337 : Blo 2057435 5863337 := bstep (se 2 (by rfl) ⟨2198751, by rfl⟩ : syracuseStep 5863337 = 4397503) B4397503
theorem B3908891 : Blo 2057435 3908891 := bstep (se 1 (by rfl) ⟨2931668, by rfl⟩ : syracuseStep 3908891 = 5863337) B5863337
theorem B2605927 : Blo 2057435 2605927 := bstep (se 1 (by rfl) ⟨1954445, by rfl⟩ : syracuseStep 2605927 = 3908891) B3908891
theorem B3474569 : Blo 2057435 3474569 := bstep (se 2 (by rfl) ⟨1302963, by rfl⟩ : syracuseStep 3474569 = 2605927) B2605927
theorem B2316379 : Blo 2057435 2316379 := bstep (se 1 (by rfl) ⟨1737284, by rfl⟩ : syracuseStep 2316379 = 3474569) B3474569
theorem B3088505 : Blo 2057435 3088505 := bstep (se 2 (by rfl) ⟨1158189, by rfl⟩ : syracuseStep 3088505 = 2316379) B2316379
theorem B2059003 : Blo 2057435 2059003 := bstep (se 1 (by rfl) ⟨1544252, by rfl⟩ : syracuseStep 2059003 = 3088505) B3088505
theorem B2576233 : Blo 2057435 2576233 := bbase (se 2 (by rfl) ⟨966087, by rfl⟩ : syracuseStep 2576233 = 1932175) (by norm_num)
theorem B3434977 : Blo 2057435 3434977 := bstep (se 2 (by rfl) ⟨1288116, by rfl⟩ : syracuseStep 3434977 = 2576233) B2576233
theorem B18319877 : Blo 2057435 18319877 := bstep (se 4 (by rfl) ⟨1717488, by rfl⟩ : syracuseStep 18319877 = 3434977) B3434977
theorem B12213251 : Blo 2057435 12213251 := bstep (se 1 (by rfl) ⟨9159938, by rfl⟩ : syracuseStep 12213251 = 18319877) B18319877
theorem B8142167 : Blo 2057435 8142167 := bstep (se 1 (by rfl) ⟨6106625, by rfl⟩ : syracuseStep 8142167 = 12213251) B12213251
theorem B21712445 : Blo 2057435 21712445 := bstep (se 3 (by rfl) ⟨4071083, by rfl⟩ : syracuseStep 21712445 = 8142167) B8142167
theorem B14474963 : Blo 2057435 14474963 := bstep (se 1 (by rfl) ⟨10856222, by rfl⟩ : syracuseStep 14474963 = 21712445) B21712445
theorem B9649975 : Blo 2057435 9649975 := bstep (se 1 (by rfl) ⟨7237481, by rfl⟩ : syracuseStep 9649975 = 14474963) B14474963
theorem B12866633 : Blo 2057435 12866633 := bstep (se 2 (by rfl) ⟨4824987, by rfl⟩ : syracuseStep 12866633 = 9649975) B9649975
theorem B8577755 : Blo 2057435 8577755 := bstep (se 1 (by rfl) ⟨6433316, by rfl⟩ : syracuseStep 8577755 = 12866633) B12866633
theorem B5718503 : Blo 2057435 5718503 := bstep (se 1 (by rfl) ⟨4288877, by rfl⟩ : syracuseStep 5718503 = 8577755) B8577755
theorem B3812335 : Blo 2057435 3812335 := bstep (se 1 (by rfl) ⟨2859251, by rfl⟩ : syracuseStep 3812335 = 5718503) B5718503
theorem B20332453 : Blo 2057435 20332453 := bstep (se 4 (by rfl) ⟨1906167, by rfl⟩ : syracuseStep 20332453 = 3812335) B3812335
theorem B27109937 : Blo 2057435 27109937 := bstep (se 2 (by rfl) ⟨10166226, by rfl⟩ : syracuseStep 27109937 = 20332453) B20332453
theorem B72293165 : Blo 2057435 72293165 := bstep (se 3 (by rfl) ⟨13554968, by rfl⟩ : syracuseStep 72293165 = 27109937) B27109937
theorem B48195443 : Blo 2057435 48195443 := bstep (se 1 (by rfl) ⟨36146582, by rfl⟩ : syracuseStep 48195443 = 72293165) B72293165
theorem B128521181 : Blo 2057435 128521181 := bstep (se 3 (by rfl) ⟨24097721, by rfl⟩ : syracuseStep 128521181 = 48195443) B48195443
theorem B85680787 : Blo 2057435 85680787 := bstep (se 1 (by rfl) ⟨64260590, by rfl⟩ : syracuseStep 85680787 = 128521181) B128521181
theorem B114241049 : Blo 2057435 114241049 := bstep (se 2 (by rfl) ⟨42840393, by rfl⟩ : syracuseStep 114241049 = 85680787) B85680787
theorem B76160699 : Blo 2057435 76160699 := bstep (se 1 (by rfl) ⟨57120524, by rfl⟩ : syracuseStep 76160699 = 114241049) B114241049
theorem B50773799 : Blo 2057435 50773799 := bstep (se 1 (by rfl) ⟨38080349, by rfl⟩ : syracuseStep 50773799 = 76160699) B76160699
theorem B33849199 : Blo 2057435 33849199 := bstep (se 1 (by rfl) ⟨25386899, by rfl⟩ : syracuseStep 33849199 = 50773799) B50773799
theorem B45132265 : Blo 2057435 45132265 := bstep (se 2 (by rfl) ⟨16924599, by rfl⟩ : syracuseStep 45132265 = 33849199) B33849199
theorem B60176353 : Blo 2057435 60176353 := bstep (se 2 (by rfl) ⟨22566132, by rfl⟩ : syracuseStep 60176353 = 45132265) B45132265
theorem B80235137 : Blo 2057435 80235137 := bstep (se 2 (by rfl) ⟨30088176, by rfl⟩ : syracuseStep 80235137 = 60176353) B60176353
theorem B53490091 : Blo 2057435 53490091 := bstep (se 1 (by rfl) ⟨40117568, by rfl⟩ : syracuseStep 53490091 = 80235137) B80235137
theorem B71320121 : Blo 2057435 71320121 := bstep (se 2 (by rfl) ⟨26745045, by rfl⟩ : syracuseStep 71320121 = 53490091) B53490091
theorem B47546747 : Blo 2057435 47546747 := bstep (se 1 (by rfl) ⟨35660060, by rfl⟩ : syracuseStep 47546747 = 71320121) B71320121
theorem B31697831 : Blo 2057435 31697831 := bstep (se 1 (by rfl) ⟨23773373, by rfl⟩ : syracuseStep 31697831 = 47546747) B47546747
theorem B84527549 : Blo 2057435 84527549 := bstep (se 3 (by rfl) ⟨15848915, by rfl⟩ : syracuseStep 84527549 = 31697831) B31697831
theorem B56351699 : Blo 2057435 56351699 := bstep (se 1 (by rfl) ⟨42263774, by rfl⟩ : syracuseStep 56351699 = 84527549) B84527549
theorem B37567799 : Blo 2057435 37567799 := bstep (se 1 (by rfl) ⟨28175849, by rfl⟩ : syracuseStep 37567799 = 56351699) B56351699
theorem B25045199 : Blo 2057435 25045199 := bstep (se 1 (by rfl) ⟨18783899, by rfl⟩ : syracuseStep 25045199 = 37567799) B37567799
theorem B16696799 : Blo 2057435 16696799 := bstep (se 1 (by rfl) ⟨12522599, by rfl⟩ : syracuseStep 16696799 = 25045199) B25045199
theorem B11131199 : Blo 2057435 11131199 := bstep (se 1 (by rfl) ⟨8348399, by rfl⟩ : syracuseStep 11131199 = 16696799) B16696799
theorem B7420799 : Blo 2057435 7420799 := bstep (se 1 (by rfl) ⟨5565599, by rfl⟩ : syracuseStep 7420799 = 11131199) B11131199
theorem B4947199 : Blo 2057435 4947199 := bstep (se 1 (by rfl) ⟨3710399, by rfl⟩ : syracuseStep 4947199 = 7420799) B7420799
theorem B26385061 : Blo 2057435 26385061 := bstep (se 4 (by rfl) ⟨2473599, by rfl⟩ : syracuseStep 26385061 = 4947199) B4947199
theorem B35180081 : Blo 2057435 35180081 := bstep (se 2 (by rfl) ⟨13192530, by rfl⟩ : syracuseStep 35180081 = 26385061) B26385061
theorem B23453387 : Blo 2057435 23453387 := bstep (se 1 (by rfl) ⟨17590040, by rfl⟩ : syracuseStep 23453387 = 35180081) B35180081
theorem B15635591 : Blo 2057435 15635591 := bstep (se 1 (by rfl) ⟨11726693, by rfl⟩ : syracuseStep 15635591 = 23453387) B23453387
theorem B10423727 : Blo 2057435 10423727 := bstep (se 1 (by rfl) ⟨7817795, by rfl⟩ : syracuseStep 10423727 = 15635591) B15635591
theorem B6949151 : Blo 2057435 6949151 := bstep (se 1 (by rfl) ⟨5211863, by rfl⟩ : syracuseStep 6949151 = 10423727) B10423727
theorem B4632767 : Blo 2057435 4632767 := bstep (se 1 (by rfl) ⟨3474575, by rfl⟩ : syracuseStep 4632767 = 6949151) B6949151
theorem B3088511 : Blo 2057435 3088511 := bstep (se 1 (by rfl) ⟨2316383, by rfl⟩ : syracuseStep 3088511 = 4632767) B4632767
theorem B2059007 : Blo 2057435 2059007 := bstep (se 1 (by rfl) ⟨1544255, by rfl⟩ : syracuseStep 2059007 = 3088511) B3088511
theorem B3088517 : Blo 2057435 3088517 := bbase (se 4 (by rfl) ⟨289548, by rfl⟩ : syracuseStep 3088517 = 579097) (by norm_num)
theorem B2059011 : Blo 2057435 2059011 := bstep (se 1 (by rfl) ⟨1544258, by rfl⟩ : syracuseStep 2059011 = 3088517) B3088517
theorem B3474589 : Blo 2057435 3474589 := bbase (se 3 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 3474589 = 1302971) (by norm_num)
theorem B4632785 : Blo 2057435 4632785 := bstep (se 2 (by rfl) ⟨1737294, by rfl⟩ : syracuseStep 4632785 = 3474589) B3474589
theorem B3088523 : Blo 2057435 3088523 := bstep (se 1 (by rfl) ⟨2316392, by rfl⟩ : syracuseStep 3088523 = 4632785) B4632785
theorem B2059015 : Blo 2057435 2059015 := bstep (se 1 (by rfl) ⟨1544261, by rfl⟩ : syracuseStep 2059015 = 3088523) B3088523
theorem B2316397 : Blo 2057435 2316397 := bbase (se 3 (by rfl) ⟨434324, by rfl⟩ : syracuseStep 2316397 = 868649) (by norm_num)
theorem B3088529 : Blo 2057435 3088529 := bstep (se 2 (by rfl) ⟨1158198, by rfl⟩ : syracuseStep 3088529 = 2316397) B2316397
theorem B2059019 : Blo 2057435 2059019 := bstep (se 1 (by rfl) ⟨1544264, by rfl⟩ : syracuseStep 2059019 = 3088529) B3088529
theorem B6949205 : Blo 2057435 6949205 := bbase (se 10 (by rfl) ⟨10179, by rfl⟩ : syracuseStep 6949205 = 20359) (by norm_num)
theorem B4632803 : Blo 2057435 4632803 := bstep (se 1 (by rfl) ⟨3474602, by rfl⟩ : syracuseStep 4632803 = 6949205) B6949205
theorem B3088535 : Blo 2057435 3088535 := bstep (se 1 (by rfl) ⟨2316401, by rfl⟩ : syracuseStep 3088535 = 4632803) B4632803
theorem B2059023 : Blo 2057435 2059023 := bstep (se 1 (by rfl) ⟨1544267, by rfl⟩ : syracuseStep 2059023 = 3088535) B3088535
theorem B3088541 : Blo 2057435 3088541 := bbase (se 3 (by rfl) ⟨579101, by rfl⟩ : syracuseStep 3088541 = 1158203) (by norm_num)
theorem B2059027 : Blo 2057435 2059027 := bstep (se 1 (by rfl) ⟨1544270, by rfl⟩ : syracuseStep 2059027 = 3088541) B3088541
theorem B4632821 : Blo 2057435 4632821 := bbase (se 5 (by rfl) ⟨217163, by rfl⟩ : syracuseStep 4632821 = 434327) (by norm_num)
theorem B3088547 : Blo 2057435 3088547 := bstep (se 1 (by rfl) ⟨2316410, by rfl⟩ : syracuseStep 3088547 = 4632821) B4632821
theorem B2059031 : Blo 2057435 2059031 := bstep (se 1 (by rfl) ⟨1544273, by rfl⟩ : syracuseStep 2059031 = 3088547) B3088547
theorem B7420901 : Blo 2057435 7420901 := bbase (se 4 (by rfl) ⟨695709, by rfl⟩ : syracuseStep 7420901 = 1391419) (by norm_num)
theorem B19789069 : Blo 2057435 19789069 := bstep (se 3 (by rfl) ⟨3710450, by rfl⟩ : syracuseStep 19789069 = 7420901) B7420901
theorem B26385425 : Blo 2057435 26385425 := bstep (se 2 (by rfl) ⟨9894534, by rfl⟩ : syracuseStep 26385425 = 19789069) B19789069
theorem B17590283 : Blo 2057435 17590283 := bstep (se 1 (by rfl) ⟨13192712, by rfl⟩ : syracuseStep 17590283 = 26385425) B26385425
theorem B11726855 : Blo 2057435 11726855 := bstep (se 1 (by rfl) ⟨8795141, by rfl⟩ : syracuseStep 11726855 = 17590283) B17590283
theorem B7817903 : Blo 2057435 7817903 := bstep (se 1 (by rfl) ⟨5863427, by rfl⟩ : syracuseStep 7817903 = 11726855) B11726855
theorem B5211935 : Blo 2057435 5211935 := bstep (se 1 (by rfl) ⟨3908951, by rfl⟩ : syracuseStep 5211935 = 7817903) B7817903
theorem B3474623 : Blo 2057435 3474623 := bstep (se 1 (by rfl) ⟨2605967, by rfl⟩ : syracuseStep 3474623 = 5211935) B5211935
theorem B2316415 : Blo 2057435 2316415 := bstep (se 1 (by rfl) ⟨1737311, by rfl⟩ : syracuseStep 2316415 = 3474623) B3474623
theorem B3088553 : Blo 2057435 3088553 := bstep (se 2 (by rfl) ⟨1158207, by rfl⟩ : syracuseStep 3088553 = 2316415) B2316415
theorem B2059035 : Blo 2057435 2059035 := bstep (se 1 (by rfl) ⟨1544276, by rfl⟩ : syracuseStep 2059035 = 3088553) B3088553
theorem B4947277 : Blo 2057435 4947277 := bbase (se 3 (by rfl) ⟨927614, by rfl⟩ : syracuseStep 4947277 = 1855229) (by norm_num)
theorem B6596369 : Blo 2057435 6596369 := bstep (se 2 (by rfl) ⟨2473638, by rfl⟩ : syracuseStep 6596369 = 4947277) B4947277
theorem B4397579 : Blo 2057435 4397579 := bstep (se 1 (by rfl) ⟨3298184, by rfl⟩ : syracuseStep 4397579 = 6596369) B6596369
theorem B2931719 : Blo 2057435 2931719 := bstep (se 1 (by rfl) ⟨2198789, by rfl⟩ : syracuseStep 2931719 = 4397579) B4397579
theorem B7817917 : Blo 2057435 7817917 := bstep (se 3 (by rfl) ⟨1465859, by rfl⟩ : syracuseStep 7817917 = 2931719) B2931719
theorem B10423889 : Blo 2057435 10423889 := bstep (se 2 (by rfl) ⟨3908958, by rfl⟩ : syracuseStep 10423889 = 7817917) B7817917
theorem B6949259 : Blo 2057435 6949259 := bstep (se 1 (by rfl) ⟨5211944, by rfl⟩ : syracuseStep 6949259 = 10423889) B10423889
theorem B4632839 : Blo 2057435 4632839 := bstep (se 1 (by rfl) ⟨3474629, by rfl⟩ : syracuseStep 4632839 = 6949259) B6949259
theorem B3088559 : Blo 2057435 3088559 := bstep (se 1 (by rfl) ⟨2316419, by rfl⟩ : syracuseStep 3088559 = 4632839) B4632839
theorem B2059039 : Blo 2057435 2059039 := bstep (se 1 (by rfl) ⟨1544279, by rfl⟩ : syracuseStep 2059039 = 3088559) B3088559
theorem B3088565 : Blo 2057435 3088565 := bbase (se 5 (by rfl) ⟨144776, by rfl⟩ : syracuseStep 3088565 = 289553) (by norm_num)
theorem B2059043 : Blo 2057435 2059043 := bstep (se 1 (by rfl) ⟨1544282, by rfl⟩ : syracuseStep 2059043 = 3088565) B3088565
theorem B5211965 : Blo 2057435 5211965 := bbase (se 3 (by rfl) ⟨977243, by rfl⟩ : syracuseStep 5211965 = 1954487) (by norm_num)
theorem B3474643 : Blo 2057435 3474643 := bstep (se 1 (by rfl) ⟨2605982, by rfl⟩ : syracuseStep 3474643 = 5211965) B5211965
theorem B4632857 : Blo 2057435 4632857 := bstep (se 2 (by rfl) ⟨1737321, by rfl⟩ : syracuseStep 4632857 = 3474643) B3474643
theorem B3088571 : Blo 2057435 3088571 := bstep (se 1 (by rfl) ⟨2316428, by rfl⟩ : syracuseStep 3088571 = 4632857) B4632857
theorem B2059047 : Blo 2057435 2059047 := bstep (se 1 (by rfl) ⟨1544285, by rfl⟩ : syracuseStep 2059047 = 3088571) B3088571
theorem B2316433 : Blo 2057435 2316433 := bbase (se 2 (by rfl) ⟨868662, by rfl⟩ : syracuseStep 2316433 = 1737325) (by norm_num)
theorem B3088577 : Blo 2057435 3088577 := bstep (se 2 (by rfl) ⟨1158216, by rfl⟩ : syracuseStep 3088577 = 2316433) B2316433
theorem B2059051 : Blo 2057435 2059051 := bstep (se 1 (by rfl) ⟨1544288, by rfl⟩ : syracuseStep 2059051 = 3088577) B3088577
theorem B3908989 : Blo 2057435 3908989 := bbase (se 3 (by rfl) ⟨732935, by rfl⟩ : syracuseStep 3908989 = 1465871) (by norm_num)
theorem B5211985 : Blo 2057435 5211985 := bstep (se 2 (by rfl) ⟨1954494, by rfl⟩ : syracuseStep 5211985 = 3908989) B3908989
theorem B6949313 : Blo 2057435 6949313 := bstep (se 2 (by rfl) ⟨2605992, by rfl⟩ : syracuseStep 6949313 = 5211985) B5211985
theorem B4632875 : Blo 2057435 4632875 := bstep (se 1 (by rfl) ⟨3474656, by rfl⟩ : syracuseStep 4632875 = 6949313) B6949313
theorem B3088583 : Blo 2057435 3088583 := bstep (se 1 (by rfl) ⟨2316437, by rfl⟩ : syracuseStep 3088583 = 4632875) B4632875
theorem B2059055 : Blo 2057435 2059055 := bstep (se 1 (by rfl) ⟨1544291, by rfl⟩ : syracuseStep 2059055 = 3088583) B3088583
theorem B3088589 : Blo 2057435 3088589 := bbase (se 3 (by rfl) ⟨579110, by rfl⟩ : syracuseStep 3088589 = 1158221) (by norm_num)
theorem B2059059 : Blo 2057435 2059059 := bstep (se 1 (by rfl) ⟨1544294, by rfl⟩ : syracuseStep 2059059 = 3088589) B3088589
theorem B4632893 : Blo 2057435 4632893 := bbase (se 3 (by rfl) ⟨868667, by rfl⟩ : syracuseStep 4632893 = 1737335) (by norm_num)
theorem B3088595 : Blo 2057435 3088595 := bstep (se 1 (by rfl) ⟨2316446, by rfl⟩ : syracuseStep 3088595 = 4632893) B4632893
theorem B2059063 : Blo 2057435 2059063 := bstep (se 1 (by rfl) ⟨1544297, by rfl⟩ : syracuseStep 2059063 = 3088595) B3088595
theorem B3474677 : Blo 2057435 3474677 := bbase (se 5 (by rfl) ⟨162875, by rfl⟩ : syracuseStep 3474677 = 325751) (by norm_num)
theorem B2316451 : Blo 2057435 2316451 := bstep (se 1 (by rfl) ⟨1737338, by rfl⟩ : syracuseStep 2316451 = 3474677) B3474677
theorem B3088601 : Blo 2057435 3088601 := bstep (se 2 (by rfl) ⟨1158225, by rfl⟩ : syracuseStep 3088601 = 2316451) B2316451
theorem B2059067 : Blo 2057435 2059067 := bstep (se 1 (by rfl) ⟨1544300, by rfl⟩ : syracuseStep 2059067 = 3088601) B3088601
theorem B2087165 : Blo 2057435 2087165 := bbase (se 3 (by rfl) ⟨391343, by rfl⟩ : syracuseStep 2087165 = 782687) (by norm_num)
theorem B5565773 : Blo 2057435 5565773 := bstep (se 3 (by rfl) ⟨1043582, by rfl⟩ : syracuseStep 5565773 = 2087165) B2087165
theorem B14842061 : Blo 2057435 14842061 := bstep (se 3 (by rfl) ⟨2782886, by rfl⟩ : syracuseStep 14842061 = 5565773) B5565773
theorem B9894707 : Blo 2057435 9894707 := bstep (se 1 (by rfl) ⟨7421030, by rfl⟩ : syracuseStep 9894707 = 14842061) B14842061
theorem B6596471 : Blo 2057435 6596471 := bstep (se 1 (by rfl) ⟨4947353, by rfl⟩ : syracuseStep 6596471 = 9894707) B9894707
theorem B4397647 : Blo 2057435 4397647 := bstep (se 1 (by rfl) ⟨3298235, by rfl⟩ : syracuseStep 4397647 = 6596471) B6596471
theorem B5863529 : Blo 2057435 5863529 := bstep (se 2 (by rfl) ⟨2198823, by rfl⟩ : syracuseStep 5863529 = 4397647) B4397647
theorem B15636077 : Blo 2057435 15636077 := bstep (se 3 (by rfl) ⟨2931764, by rfl⟩ : syracuseStep 15636077 = 5863529) B5863529
theorem B10424051 : Blo 2057435 10424051 := bstep (se 1 (by rfl) ⟨7818038, by rfl⟩ : syracuseStep 10424051 = 15636077) B15636077
theorem B6949367 : Blo 2057435 6949367 := bstep (se 1 (by rfl) ⟨5212025, by rfl⟩ : syracuseStep 6949367 = 10424051) B10424051
theorem B4632911 : Blo 2057435 4632911 := bstep (se 1 (by rfl) ⟨3474683, by rfl⟩ : syracuseStep 4632911 = 6949367) B6949367
theorem B3088607 : Blo 2057435 3088607 := bstep (se 1 (by rfl) ⟨2316455, by rfl⟩ : syracuseStep 3088607 = 4632911) B4632911
theorem B2059071 : Blo 2057435 2059071 := bstep (se 1 (by rfl) ⟨1544303, by rfl⟩ : syracuseStep 2059071 = 3088607) B3088607
theorem B3088613 : Blo 2057435 3088613 := bbase (se 4 (by rfl) ⟨289557, by rfl⟩ : syracuseStep 3088613 = 579115) (by norm_num)
theorem B2059075 : Blo 2057435 2059075 := bstep (se 1 (by rfl) ⟨1544306, by rfl⟩ : syracuseStep 2059075 = 3088613) B3088613
theorem B5565797 : Blo 2057435 5565797 := bbase (se 4 (by rfl) ⟨521793, by rfl⟩ : syracuseStep 5565797 = 1043587) (by norm_num)
theorem B3710531 : Blo 2057435 3710531 := bstep (se 1 (by rfl) ⟨2782898, by rfl⟩ : syracuseStep 3710531 = 5565797) B5565797
theorem B2473687 : Blo 2057435 2473687 := bstep (se 1 (by rfl) ⟨1855265, by rfl⟩ : syracuseStep 2473687 = 3710531) B3710531
theorem B3298249 : Blo 2057435 3298249 := bstep (se 2 (by rfl) ⟨1236843, by rfl⟩ : syracuseStep 3298249 = 2473687) B2473687
theorem B4397665 : Blo 2057435 4397665 := bstep (se 2 (by rfl) ⟨1649124, by rfl⟩ : syracuseStep 4397665 = 3298249) B3298249
theorem B5863553 : Blo 2057435 5863553 := bstep (se 2 (by rfl) ⟨2198832, by rfl⟩ : syracuseStep 5863553 = 4397665) B4397665
theorem B3909035 : Blo 2057435 3909035 := bstep (se 1 (by rfl) ⟨2931776, by rfl⟩ : syracuseStep 3909035 = 5863553) B5863553
theorem B2606023 : Blo 2057435 2606023 := bstep (se 1 (by rfl) ⟨1954517, by rfl⟩ : syracuseStep 2606023 = 3909035) B3909035
theorem B3474697 : Blo 2057435 3474697 := bstep (se 2 (by rfl) ⟨1303011, by rfl⟩ : syracuseStep 3474697 = 2606023) B2606023
theorem B4632929 : Blo 2057435 4632929 := bstep (se 2 (by rfl) ⟨1737348, by rfl⟩ : syracuseStep 4632929 = 3474697) B3474697
theorem B3088619 : Blo 2057435 3088619 := bstep (se 1 (by rfl) ⟨2316464, by rfl⟩ : syracuseStep 3088619 = 4632929) B4632929
theorem B2059079 : Blo 2057435 2059079 := bstep (se 1 (by rfl) ⟨1544309, by rfl⟩ : syracuseStep 2059079 = 3088619) B3088619
theorem B2316469 : Blo 2057435 2316469 := bbase (se 5 (by rfl) ⟨108584, by rfl⟩ : syracuseStep 2316469 = 217169) (by norm_num)
theorem B3088625 : Blo 2057435 3088625 := bstep (se 2 (by rfl) ⟨1158234, by rfl⟩ : syracuseStep 3088625 = 2316469) B2316469
theorem B2059083 : Blo 2057435 2059083 := bstep (se 1 (by rfl) ⟨1544312, by rfl⟩ : syracuseStep 2059083 = 3088625) B3088625
theorem B2606033 : Blo 2057435 2606033 := bbase (se 2 (by rfl) ⟨977262, by rfl⟩ : syracuseStep 2606033 = 1954525) (by norm_num)
theorem B6949421 : Blo 2057435 6949421 := bstep (se 3 (by rfl) ⟨1303016, by rfl⟩ : syracuseStep 6949421 = 2606033) B2606033
theorem B4632947 : Blo 2057435 4632947 := bstep (se 1 (by rfl) ⟨3474710, by rfl⟩ : syracuseStep 4632947 = 6949421) B6949421
theorem B3088631 : Blo 2057435 3088631 := bstep (se 1 (by rfl) ⟨2316473, by rfl⟩ : syracuseStep 3088631 = 4632947) B4632947
theorem B2059087 : Blo 2057435 2059087 := bstep (se 1 (by rfl) ⟨1544315, by rfl⟩ : syracuseStep 2059087 = 3088631) B3088631
theorem B3088637 : Blo 2057435 3088637 := bbase (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) (by norm_num)
theorem B2059091 : Blo 2057435 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B4632965 : Blo 2057435 4632965 := bbase (se 4 (by rfl) ⟨434340, by rfl⟩ : syracuseStep 4632965 = 868681) (by norm_num)
theorem B3088643 : Blo 2057435 3088643 := bstep (se 1 (by rfl) ⟨2316482, by rfl⟩ : syracuseStep 3088643 = 4632965) B4632965
theorem B2059095 : Blo 2057435 2059095 := bstep (se 1 (by rfl) ⟨1544321, by rfl⟩ : syracuseStep 2059095 = 3088643) B3088643
theorem B2931805 : Blo 2057435 2931805 := bbase (se 3 (by rfl) ⟨549713, by rfl⟩ : syracuseStep 2931805 = 1099427) (by norm_num)
theorem B3909073 : Blo 2057435 3909073 := bstep (se 2 (by rfl) ⟨1465902, by rfl⟩ : syracuseStep 3909073 = 2931805) B2931805
theorem B5212097 : Blo 2057435 5212097 := bstep (se 2 (by rfl) ⟨1954536, by rfl⟩ : syracuseStep 5212097 = 3909073) B3909073
theorem B3474731 : Blo 2057435 3474731 := bstep (se 1 (by rfl) ⟨2606048, by rfl⟩ : syracuseStep 3474731 = 5212097) B5212097
theorem B2316487 : Blo 2057435 2316487 := bstep (se 1 (by rfl) ⟨1737365, by rfl⟩ : syracuseStep 2316487 = 3474731) B3474731
theorem B3088649 : Blo 2057435 3088649 := bstep (se 2 (by rfl) ⟨1158243, by rfl⟩ : syracuseStep 3088649 = 2316487) B2316487
theorem B2059099 : Blo 2057435 2059099 := bstep (se 1 (by rfl) ⟨1544324, by rfl⟩ : syracuseStep 2059099 = 3088649) B3088649
theorem B10424213 : Blo 2057435 10424213 := bbase (se 6 (by rfl) ⟨244317, by rfl⟩ : syracuseStep 10424213 = 488635) (by norm_num)
theorem B6949475 : Blo 2057435 6949475 := bstep (se 1 (by rfl) ⟨5212106, by rfl⟩ : syracuseStep 6949475 = 10424213) B10424213
theorem B4632983 : Blo 2057435 4632983 := bstep (se 1 (by rfl) ⟨3474737, by rfl⟩ : syracuseStep 4632983 = 6949475) B6949475
theorem B3088655 : Blo 2057435 3088655 := bstep (se 1 (by rfl) ⟨2316491, by rfl⟩ : syracuseStep 3088655 = 4632983) B4632983
theorem B2059103 : Blo 2057435 2059103 := bstep (se 1 (by rfl) ⟨1544327, by rfl⟩ : syracuseStep 2059103 = 3088655) B3088655
theorem B3088661 : Blo 2057435 3088661 := bbase (se 6 (by rfl) ⟨72390, by rfl⟩ : syracuseStep 3088661 = 144781) (by norm_num)
theorem B2059107 : Blo 2057435 2059107 := bstep (se 1 (by rfl) ⟨1544330, by rfl⟩ : syracuseStep 2059107 = 3088661) B3088661
theorem B4696213 : Blo 2057435 4696213 := bbase (se 6 (by rfl) ⟨110067, by rfl⟩ : syracuseStep 4696213 = 220135) (by norm_num)
theorem B6261617 : Blo 2057435 6261617 := bstep (se 2 (by rfl) ⟨2348106, by rfl⟩ : syracuseStep 6261617 = 4696213) B4696213
theorem B4174411 : Blo 2057435 4174411 := bstep (se 1 (by rfl) ⟨3130808, by rfl⟩ : syracuseStep 4174411 = 6261617) B6261617
theorem B5565881 : Blo 2057435 5565881 := bstep (se 2 (by rfl) ⟨2087205, by rfl⟩ : syracuseStep 5565881 = 4174411) B4174411
theorem B14842349 : Blo 2057435 14842349 := bstep (se 3 (by rfl) ⟨2782940, by rfl⟩ : syracuseStep 14842349 = 5565881) B5565881
theorem B9894899 : Blo 2057435 9894899 := bstep (se 1 (by rfl) ⟨7421174, by rfl⟩ : syracuseStep 9894899 = 14842349) B14842349
theorem B26386397 : Blo 2057435 26386397 := bstep (se 3 (by rfl) ⟨4947449, by rfl⟩ : syracuseStep 26386397 = 9894899) B9894899
theorem B17590931 : Blo 2057435 17590931 := bstep (se 1 (by rfl) ⟨13193198, by rfl⟩ : syracuseStep 17590931 = 26386397) B26386397
theorem B11727287 : Blo 2057435 11727287 := bstep (se 1 (by rfl) ⟨8795465, by rfl⟩ : syracuseStep 11727287 = 17590931) B17590931
theorem B7818191 : Blo 2057435 7818191 := bstep (se 1 (by rfl) ⟨5863643, by rfl⟩ : syracuseStep 7818191 = 11727287) B11727287
theorem B5212127 : Blo 2057435 5212127 := bstep (se 1 (by rfl) ⟨3909095, by rfl⟩ : syracuseStep 5212127 = 7818191) B7818191
theorem B3474751 : Blo 2057435 3474751 := bstep (se 1 (by rfl) ⟨2606063, by rfl⟩ : syracuseStep 3474751 = 5212127) B5212127
theorem B4633001 : Blo 2057435 4633001 := bstep (se 2 (by rfl) ⟨1737375, by rfl⟩ : syracuseStep 4633001 = 3474751) B3474751
theorem B3088667 : Blo 2057435 3088667 := bstep (se 1 (by rfl) ⟨2316500, by rfl⟩ : syracuseStep 3088667 = 4633001) B4633001
theorem B2059111 : Blo 2057435 2059111 := bstep (se 1 (by rfl) ⟨1544333, by rfl⟩ : syracuseStep 2059111 = 3088667) B3088667
theorem B2316505 : Blo 2057435 2316505 := bbase (se 2 (by rfl) ⟨868689, by rfl⟩ : syracuseStep 2316505 = 1737379) (by norm_num)
theorem B3088673 : Blo 2057435 3088673 := bstep (se 2 (by rfl) ⟨1158252, by rfl⟩ : syracuseStep 3088673 = 2316505) B2316505
theorem B2059115 : Blo 2057435 2059115 := bstep (se 1 (by rfl) ⟨1544336, by rfl⟩ : syracuseStep 2059115 = 3088673) B3088673
theorem B4174429 : Blo 2057435 4174429 := bbase (se 3 (by rfl) ⟨782705, by rfl⟩ : syracuseStep 4174429 = 1565411) (by norm_num)
theorem B5565905 : Blo 2057435 5565905 := bstep (se 2 (by rfl) ⟨2087214, by rfl⟩ : syracuseStep 5565905 = 4174429) B4174429
theorem B3710603 : Blo 2057435 3710603 := bstep (se 1 (by rfl) ⟨2782952, by rfl⟩ : syracuseStep 3710603 = 5565905) B5565905
theorem B2473735 : Blo 2057435 2473735 := bstep (se 1 (by rfl) ⟨1855301, by rfl⟩ : syracuseStep 2473735 = 3710603) B3710603
theorem B3298313 : Blo 2057435 3298313 := bstep (se 2 (by rfl) ⟨1236867, by rfl⟩ : syracuseStep 3298313 = 2473735) B2473735
theorem B2198875 : Blo 2057435 2198875 := bstep (se 1 (by rfl) ⟨1649156, by rfl⟩ : syracuseStep 2198875 = 3298313) B3298313
theorem B2931833 : Blo 2057435 2931833 := bstep (se 2 (by rfl) ⟨1099437, by rfl⟩ : syracuseStep 2931833 = 2198875) B2198875
theorem B7818221 : Blo 2057435 7818221 := bstep (se 3 (by rfl) ⟨1465916, by rfl⟩ : syracuseStep 7818221 = 2931833) B2931833
theorem B5212147 : Blo 2057435 5212147 := bstep (se 1 (by rfl) ⟨3909110, by rfl⟩ : syracuseStep 5212147 = 7818221) B7818221
theorem B6949529 : Blo 2057435 6949529 := bstep (se 2 (by rfl) ⟨2606073, by rfl⟩ : syracuseStep 6949529 = 5212147) B5212147
theorem B4633019 : Blo 2057435 4633019 := bstep (se 1 (by rfl) ⟨3474764, by rfl⟩ : syracuseStep 4633019 = 6949529) B6949529
theorem B3088679 : Blo 2057435 3088679 := bstep (se 1 (by rfl) ⟨2316509, by rfl⟩ : syracuseStep 3088679 = 4633019) B4633019
theorem B2059119 : Blo 2057435 2059119 := bstep (se 1 (by rfl) ⟨1544339, by rfl⟩ : syracuseStep 2059119 = 3088679) B3088679
theorem B3088685 : Blo 2057435 3088685 := bbase (se 3 (by rfl) ⟨579128, by rfl⟩ : syracuseStep 3088685 = 1158257) (by norm_num)
theorem B2059123 : Blo 2057435 2059123 := bstep (se 1 (by rfl) ⟨1544342, by rfl⟩ : syracuseStep 2059123 = 3088685) B3088685
theorem B4633037 : Blo 2057435 4633037 := bbase (se 3 (by rfl) ⟨868694, by rfl⟩ : syracuseStep 4633037 = 1737389) (by norm_num)
theorem B3088691 : Blo 2057435 3088691 := bstep (se 1 (by rfl) ⟨2316518, by rfl⟩ : syracuseStep 3088691 = 4633037) B4633037
theorem B2059127 : Blo 2057435 2059127 := bstep (se 1 (by rfl) ⟨1544345, by rfl⟩ : syracuseStep 2059127 = 3088691) B3088691
theorem B2606089 : Blo 2057435 2606089 := bbase (se 2 (by rfl) ⟨977283, by rfl⟩ : syracuseStep 2606089 = 1954567) (by norm_num)
theorem B3474785 : Blo 2057435 3474785 := bstep (se 2 (by rfl) ⟨1303044, by rfl⟩ : syracuseStep 3474785 = 2606089) B2606089
theorem B2316523 : Blo 2057435 2316523 := bstep (se 1 (by rfl) ⟨1737392, by rfl⟩ : syracuseStep 2316523 = 3474785) B3474785
theorem B3088697 : Blo 2057435 3088697 := bstep (se 2 (by rfl) ⟨1158261, by rfl⟩ : syracuseStep 3088697 = 2316523) B2316523
theorem B2059131 : Blo 2057435 2059131 := bstep (se 1 (by rfl) ⟨1544348, by rfl⟩ : syracuseStep 2059131 = 3088697) B3088697
theorem B5283301 : Blo 2057435 5283301 := bbase (se 4 (by rfl) ⟨495309, by rfl⟩ : syracuseStep 5283301 = 990619) (by norm_num)
theorem B7044401 : Blo 2057435 7044401 := bstep (se 2 (by rfl) ⟨2641650, by rfl⟩ : syracuseStep 7044401 = 5283301) B5283301
theorem B4696267 : Blo 2057435 4696267 := bstep (se 1 (by rfl) ⟨3522200, by rfl⟩ : syracuseStep 4696267 = 7044401) B7044401
theorem B6261689 : Blo 2057435 6261689 := bstep (se 2 (by rfl) ⟨2348133, by rfl⟩ : syracuseStep 6261689 = 4696267) B4696267
theorem B4174459 : Blo 2057435 4174459 := bstep (se 1 (by rfl) ⟨3130844, by rfl⟩ : syracuseStep 4174459 = 6261689) B6261689
theorem B22263781 : Blo 2057435 22263781 := bstep (se 4 (by rfl) ⟨2087229, by rfl⟩ : syracuseStep 22263781 = 4174459) B4174459
theorem B29685041 : Blo 2057435 29685041 := bstep (se 2 (by rfl) ⟨11131890, by rfl⟩ : syracuseStep 29685041 = 22263781) B22263781
theorem B19790027 : Blo 2057435 19790027 := bstep (se 1 (by rfl) ⟨14842520, by rfl⟩ : syracuseStep 19790027 = 29685041) B29685041
theorem B13193351 : Blo 2057435 13193351 := bstep (se 1 (by rfl) ⟨9895013, by rfl⟩ : syracuseStep 13193351 = 19790027) B19790027
theorem B8795567 : Blo 2057435 8795567 := bstep (se 1 (by rfl) ⟨6596675, by rfl⟩ : syracuseStep 8795567 = 13193351) B13193351
theorem B23454845 : Blo 2057435 23454845 := bstep (se 3 (by rfl) ⟨4397783, by rfl⟩ : syracuseStep 23454845 = 8795567) B8795567
theorem B15636563 : Blo 2057435 15636563 := bstep (se 1 (by rfl) ⟨11727422, by rfl⟩ : syracuseStep 15636563 = 23454845) B23454845
theorem B10424375 : Blo 2057435 10424375 := bstep (se 1 (by rfl) ⟨7818281, by rfl⟩ : syracuseStep 10424375 = 15636563) B15636563
theorem B6949583 : Blo 2057435 6949583 := bstep (se 1 (by rfl) ⟨5212187, by rfl⟩ : syracuseStep 6949583 = 10424375) B10424375
theorem B4633055 : Blo 2057435 4633055 := bstep (se 1 (by rfl) ⟨3474791, by rfl⟩ : syracuseStep 4633055 = 6949583) B6949583
theorem B3088703 : Blo 2057435 3088703 := bstep (se 1 (by rfl) ⟨2316527, by rfl⟩ : syracuseStep 3088703 = 4633055) B4633055
theorem B2059135 : Blo 2057435 2059135 := bstep (se 1 (by rfl) ⟨1544351, by rfl⟩ : syracuseStep 2059135 = 3088703) B3088703
theorem B3088709 : Blo 2057435 3088709 := bbase (se 4 (by rfl) ⟨289566, by rfl⟩ : syracuseStep 3088709 = 579133) (by norm_num)
theorem B2059139 : Blo 2057435 2059139 := bstep (se 1 (by rfl) ⟨1544354, by rfl⟩ : syracuseStep 2059139 = 3088709) B3088709
theorem B3474805 : Blo 2057435 3474805 := bbase (se 5 (by rfl) ⟨162881, by rfl⟩ : syracuseStep 3474805 = 325763) (by norm_num)
theorem B4633073 : Blo 2057435 4633073 := bstep (se 2 (by rfl) ⟨1737402, by rfl⟩ : syracuseStep 4633073 = 3474805) B3474805
theorem B3088715 : Blo 2057435 3088715 := bstep (se 1 (by rfl) ⟨2316536, by rfl⟩ : syracuseStep 3088715 = 4633073) B4633073
theorem B2059143 : Blo 2057435 2059143 := bstep (se 1 (by rfl) ⟨1544357, by rfl⟩ : syracuseStep 2059143 = 3088715) B3088715
theorem B2316541 : Blo 2057435 2316541 := bbase (se 3 (by rfl) ⟨434351, by rfl⟩ : syracuseStep 2316541 = 868703) (by norm_num)
theorem B3088721 : Blo 2057435 3088721 := bstep (se 2 (by rfl) ⟨1158270, by rfl⟩ : syracuseStep 3088721 = 2316541) B2316541
theorem B2059147 : Blo 2057435 2059147 := bstep (se 1 (by rfl) ⟨1544360, by rfl⟩ : syracuseStep 2059147 = 3088721) B3088721
theorem B6949637 : Blo 2057435 6949637 := bbase (se 4 (by rfl) ⟨651528, by rfl⟩ : syracuseStep 6949637 = 1303057) (by norm_num)
theorem B4633091 : Blo 2057435 4633091 := bstep (se 1 (by rfl) ⟨3474818, by rfl⟩ : syracuseStep 4633091 = 6949637) B6949637
theorem B3088727 : Blo 2057435 3088727 := bstep (se 1 (by rfl) ⟨2316545, by rfl⟩ : syracuseStep 3088727 = 4633091) B4633091
theorem B2059151 : Blo 2057435 2059151 := bstep (se 1 (by rfl) ⟨1544363, by rfl⟩ : syracuseStep 2059151 = 3088727) B3088727
theorem B3088733 : Blo 2057435 3088733 := bbase (se 3 (by rfl) ⟨579137, by rfl⟩ : syracuseStep 3088733 = 1158275) (by norm_num)
theorem B2059155 : Blo 2057435 2059155 := bstep (se 1 (by rfl) ⟨1544366, by rfl⟩ : syracuseStep 2059155 = 3088733) B3088733
theorem B4633109 : Blo 2057435 4633109 := bbase (se 6 (by rfl) ⟨108588, by rfl⟩ : syracuseStep 4633109 = 217177) (by norm_num)
theorem B3088739 : Blo 2057435 3088739 := bstep (se 1 (by rfl) ⟨2316554, by rfl⟩ : syracuseStep 3088739 = 4633109) B4633109
theorem B2059159 : Blo 2057435 2059159 := bstep (se 1 (by rfl) ⟨1544369, by rfl⟩ : syracuseStep 2059159 = 3088739) B3088739
theorem B7818389 : Blo 2057435 7818389 := bbase (se 6 (by rfl) ⟨183243, by rfl⟩ : syracuseStep 7818389 = 366487) (by norm_num)
theorem B5212259 : Blo 2057435 5212259 := bstep (se 1 (by rfl) ⟨3909194, by rfl⟩ : syracuseStep 5212259 = 7818389) B7818389
theorem B3474839 : Blo 2057435 3474839 := bstep (se 1 (by rfl) ⟨2606129, by rfl⟩ : syracuseStep 3474839 = 5212259) B5212259
theorem B2316559 : Blo 2057435 2316559 := bstep (se 1 (by rfl) ⟨1737419, by rfl⟩ : syracuseStep 2316559 = 3474839) B3474839
theorem B3088745 : Blo 2057435 3088745 := bstep (se 2 (by rfl) ⟨1158279, by rfl⟩ : syracuseStep 3088745 = 2316559) B2316559
theorem B2059163 : Blo 2057435 2059163 := bstep (se 1 (by rfl) ⟨1544372, by rfl⟩ : syracuseStep 2059163 = 3088745) B3088745
theorem B11727605 : Blo 2057435 11727605 := bbase (se 5 (by rfl) ⟨549731, by rfl⟩ : syracuseStep 11727605 = 1099463) (by norm_num)
theorem B7818403 : Blo 2057435 7818403 := bstep (se 1 (by rfl) ⟨5863802, by rfl⟩ : syracuseStep 7818403 = 11727605) B11727605
theorem B10424537 : Blo 2057435 10424537 := bstep (se 2 (by rfl) ⟨3909201, by rfl⟩ : syracuseStep 10424537 = 7818403) B7818403
theorem B6949691 : Blo 2057435 6949691 := bstep (se 1 (by rfl) ⟨5212268, by rfl⟩ : syracuseStep 6949691 = 10424537) B10424537
theorem B4633127 : Blo 2057435 4633127 := bstep (se 1 (by rfl) ⟨3474845, by rfl⟩ : syracuseStep 4633127 = 6949691) B6949691
theorem B3088751 : Blo 2057435 3088751 := bstep (se 1 (by rfl) ⟨2316563, by rfl⟩ : syracuseStep 3088751 = 4633127) B4633127
theorem B2059167 : Blo 2057435 2059167 := bstep (se 1 (by rfl) ⟨1544375, by rfl⟩ : syracuseStep 2059167 = 3088751) B3088751
theorem B3088757 : Blo 2057435 3088757 := bbase (se 5 (by rfl) ⟨144785, by rfl⟩ : syracuseStep 3088757 = 289571) (by norm_num)
theorem B2059171 : Blo 2057435 2059171 := bstep (se 1 (by rfl) ⟨1544378, by rfl⟩ : syracuseStep 2059171 = 3088757) B3088757
theorem B4947605 : Blo 2057435 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B3298403 : Blo 2057435 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B2198935 : Blo 2057435 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B2931913 : Blo 2057435 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B3909217 : Blo 2057435 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B5212289 : Blo 2057435 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B3474859 : Blo 2057435 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B4633145 : Blo 2057435 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B3088763 : Blo 2057435 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B2059175 : Blo 2057435 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B2316577 : Blo 2057435 2316577 := bbase (se 2 (by rfl) ⟨868716, by rfl⟩ : syracuseStep 2316577 = 1737433) (by norm_num)
theorem B3088769 : Blo 2057435 3088769 := bstep (se 2 (by rfl) ⟨1158288, by rfl⟩ : syracuseStep 3088769 = 2316577) B2316577
theorem B2059179 : Blo 2057435 2059179 := bstep (se 1 (by rfl) ⟨1544384, by rfl⟩ : syracuseStep 2059179 = 3088769) B3088769
theorem B5212309 : Blo 2057435 5212309 := bbase (se 6 (by rfl) ⟨122163, by rfl⟩ : syracuseStep 5212309 = 244327) (by norm_num)
theorem B6949745 : Blo 2057435 6949745 := bstep (se 2 (by rfl) ⟨2606154, by rfl⟩ : syracuseStep 6949745 = 5212309) B5212309
theorem B4633163 : Blo 2057435 4633163 := bstep (se 1 (by rfl) ⟨3474872, by rfl⟩ : syracuseStep 4633163 = 6949745) B6949745
theorem B3088775 : Blo 2057435 3088775 := bstep (se 1 (by rfl) ⟨2316581, by rfl⟩ : syracuseStep 3088775 = 4633163) B4633163
theorem B2059183 : Blo 2057435 2059183 := bstep (se 1 (by rfl) ⟨1544387, by rfl⟩ : syracuseStep 2059183 = 3088775) B3088775
theorem B3088781 : Blo 2057435 3088781 := bbase (se 3 (by rfl) ⟨579146, by rfl⟩ : syracuseStep 3088781 = 1158293) (by norm_num)
theorem B2059187 : Blo 2057435 2059187 := bstep (se 1 (by rfl) ⟨1544390, by rfl⟩ : syracuseStep 2059187 = 3088781) B3088781
theorem B4633181 : Blo 2057435 4633181 := bbase (se 3 (by rfl) ⟨868721, by rfl⟩ : syracuseStep 4633181 = 1737443) (by norm_num)
theorem B3088787 : Blo 2057435 3088787 := bstep (se 1 (by rfl) ⟨2316590, by rfl⟩ : syracuseStep 3088787 = 4633181) B4633181
theorem B2059191 : Blo 2057435 2059191 := bstep (se 1 (by rfl) ⟨1544393, by rfl⟩ : syracuseStep 2059191 = 3088787) B3088787
theorem B3474893 : Blo 2057435 3474893 := bbase (se 3 (by rfl) ⟨651542, by rfl⟩ : syracuseStep 3474893 = 1303085) (by norm_num)
theorem B2316595 : Blo 2057435 2316595 := bstep (se 1 (by rfl) ⟨1737446, by rfl⟩ : syracuseStep 2316595 = 3474893) B3474893
theorem B3088793 : Blo 2057435 3088793 := bstep (se 2 (by rfl) ⟨1158297, by rfl⟩ : syracuseStep 3088793 = 2316595) B2316595
theorem B2059195 : Blo 2057435 2059195 := bstep (se 1 (by rfl) ⟨1544396, by rfl⟩ : syracuseStep 2059195 = 3088793) B3088793
theorem B4174589 : Blo 2057435 4174589 := bbase (se 3 (by rfl) ⟨782735, by rfl⟩ : syracuseStep 4174589 = 1565471) (by norm_num)
theorem B11132237 : Blo 2057435 11132237 := bstep (se 3 (by rfl) ⟨2087294, by rfl⟩ : syracuseStep 11132237 = 4174589) B4174589
theorem B7421491 : Blo 2057435 7421491 := bstep (se 1 (by rfl) ⟨5566118, by rfl⟩ : syracuseStep 7421491 = 11132237) B11132237
theorem B9895321 : Blo 2057435 9895321 := bstep (se 2 (by rfl) ⟨3710745, by rfl⟩ : syracuseStep 9895321 = 7421491) B7421491
theorem B13193761 : Blo 2057435 13193761 := bstep (se 2 (by rfl) ⟨4947660, by rfl⟩ : syracuseStep 13193761 = 9895321) B9895321
theorem B17591681 : Blo 2057435 17591681 := bstep (se 2 (by rfl) ⟨6596880, by rfl⟩ : syracuseStep 17591681 = 13193761) B13193761
theorem B11727787 : Blo 2057435 11727787 := bstep (se 1 (by rfl) ⟨8795840, by rfl⟩ : syracuseStep 11727787 = 17591681) B17591681
theorem B15637049 : Blo 2057435 15637049 := bstep (se 2 (by rfl) ⟨5863893, by rfl⟩ : syracuseStep 15637049 = 11727787) B11727787
theorem B10424699 : Blo 2057435 10424699 := bstep (se 1 (by rfl) ⟨7818524, by rfl⟩ : syracuseStep 10424699 = 15637049) B15637049
theorem B6949799 : Blo 2057435 6949799 := bstep (se 1 (by rfl) ⟨5212349, by rfl⟩ : syracuseStep 6949799 = 10424699) B10424699
theorem B4633199 : Blo 2057435 4633199 := bstep (se 1 (by rfl) ⟨3474899, by rfl⟩ : syracuseStep 4633199 = 6949799) B6949799
theorem B3088799 : Blo 2057435 3088799 := bstep (se 1 (by rfl) ⟨2316599, by rfl⟩ : syracuseStep 3088799 = 4633199) B4633199
theorem B2059199 : Blo 2057435 2059199 := bstep (se 1 (by rfl) ⟨1544399, by rfl⟩ : syracuseStep 2059199 = 3088799) B3088799
theorem B3088805 : Blo 2057435 3088805 := bbase (se 4 (by rfl) ⟨289575, by rfl⟩ : syracuseStep 3088805 = 579151) (by norm_num)
theorem B2059203 : Blo 2057435 2059203 := bstep (se 1 (by rfl) ⟨1544402, by rfl⟩ : syracuseStep 2059203 = 3088805) B3088805
theorem B2606185 : Blo 2057435 2606185 := bbase (se 2 (by rfl) ⟨977319, by rfl⟩ : syracuseStep 2606185 = 1954639) (by norm_num)
theorem B3474913 : Blo 2057435 3474913 := bstep (se 2 (by rfl) ⟨1303092, by rfl⟩ : syracuseStep 3474913 = 2606185) B2606185
theorem B4633217 : Blo 2057435 4633217 := bstep (se 2 (by rfl) ⟨1737456, by rfl⟩ : syracuseStep 4633217 = 3474913) B3474913
theorem B3088811 : Blo 2057435 3088811 := bstep (se 1 (by rfl) ⟨2316608, by rfl⟩ : syracuseStep 3088811 = 4633217) B4633217
theorem B2059207 : Blo 2057435 2059207 := bstep (se 1 (by rfl) ⟨1544405, by rfl⟩ : syracuseStep 2059207 = 3088811) B3088811
theorem B2316613 : Blo 2057435 2316613 := bbase (se 4 (by rfl) ⟨217182, by rfl⟩ : syracuseStep 2316613 = 434365) (by norm_num)
theorem B3088817 : Blo 2057435 3088817 := bstep (se 2 (by rfl) ⟨1158306, by rfl⟩ : syracuseStep 3088817 = 2316613) B2316613
theorem B2059211 : Blo 2057435 2059211 := bstep (se 1 (by rfl) ⟨1544408, by rfl⟩ : syracuseStep 2059211 = 3088817) B3088817
theorem B3909293 : Blo 2057435 3909293 := bbase (se 3 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 3909293 = 1465985) (by norm_num)
theorem B2606195 : Blo 2057435 2606195 := bstep (se 1 (by rfl) ⟨1954646, by rfl⟩ : syracuseStep 2606195 = 3909293) B3909293
theorem B6949853 : Blo 2057435 6949853 := bstep (se 3 (by rfl) ⟨1303097, by rfl⟩ : syracuseStep 6949853 = 2606195) B2606195
theorem B4633235 : Blo 2057435 4633235 := bstep (se 1 (by rfl) ⟨3474926, by rfl⟩ : syracuseStep 4633235 = 6949853) B6949853
theorem B3088823 : Blo 2057435 3088823 := bstep (se 1 (by rfl) ⟨2316617, by rfl⟩ : syracuseStep 3088823 = 4633235) B4633235
theorem B2059215 : Blo 2057435 2059215 := bstep (se 1 (by rfl) ⟨1544411, by rfl⟩ : syracuseStep 2059215 = 3088823) B3088823
theorem B3088829 : Blo 2057435 3088829 := bbase (se 3 (by rfl) ⟨579155, by rfl⟩ : syracuseStep 3088829 = 1158311) (by norm_num)
theorem B2059219 : Blo 2057435 2059219 := bstep (se 1 (by rfl) ⟨1544414, by rfl⟩ : syracuseStep 2059219 = 3088829) B3088829
theorem B4633253 : Blo 2057435 4633253 := bbase (se 4 (by rfl) ⟨434367, by rfl⟩ : syracuseStep 4633253 = 868735) (by norm_num)
theorem B3088835 : Blo 2057435 3088835 := bstep (se 1 (by rfl) ⟨2316626, by rfl⟩ : syracuseStep 3088835 = 4633253) B4633253
theorem B2059223 : Blo 2057435 2059223 := bstep (se 1 (by rfl) ⟨1544417, by rfl⟩ : syracuseStep 2059223 = 3088835) B3088835
theorem B5212421 : Blo 2057435 5212421 := bbase (se 4 (by rfl) ⟨488664, by rfl⟩ : syracuseStep 5212421 = 977329) (by norm_num)
theorem B3474947 : Blo 2057435 3474947 := bstep (se 1 (by rfl) ⟨2606210, by rfl⟩ : syracuseStep 3474947 = 5212421) B5212421
theorem B2316631 : Blo 2057435 2316631 := bstep (se 1 (by rfl) ⟨1737473, by rfl⟩ : syracuseStep 2316631 = 3474947) B3474947
theorem B3088841 : Blo 2057435 3088841 := bstep (se 2 (by rfl) ⟨1158315, by rfl⟩ : syracuseStep 3088841 = 2316631) B2316631
theorem B2059227 : Blo 2057435 2059227 := bstep (se 1 (by rfl) ⟨1544420, by rfl⟩ : syracuseStep 2059227 = 3088841) B3088841
theorem B4397989 : Blo 2057435 4397989 := bbase (se 4 (by rfl) ⟨412311, by rfl⟩ : syracuseStep 4397989 = 824623) (by norm_num)
theorem B5863985 : Blo 2057435 5863985 := bstep (se 2 (by rfl) ⟨2198994, by rfl⟩ : syracuseStep 5863985 = 4397989) B4397989
theorem B3909323 : Blo 2057435 3909323 := bstep (se 1 (by rfl) ⟨2931992, by rfl⟩ : syracuseStep 3909323 = 5863985) B5863985
theorem B10424861 : Blo 2057435 10424861 := bstep (se 3 (by rfl) ⟨1954661, by rfl⟩ : syracuseStep 10424861 = 3909323) B3909323
theorem B6949907 : Blo 2057435 6949907 := bstep (se 1 (by rfl) ⟨5212430, by rfl⟩ : syracuseStep 6949907 = 10424861) B10424861
theorem B4633271 : Blo 2057435 4633271 := bstep (se 1 (by rfl) ⟨3474953, by rfl⟩ : syracuseStep 4633271 = 6949907) B6949907
theorem B3088847 : Blo 2057435 3088847 := bstep (se 1 (by rfl) ⟨2316635, by rfl⟩ : syracuseStep 3088847 = 4633271) B4633271
theorem B2059231 : Blo 2057435 2059231 := bstep (se 1 (by rfl) ⟨1544423, by rfl⟩ : syracuseStep 2059231 = 3088847) B3088847
theorem B3088853 : Blo 2057435 3088853 := bbase (se 7 (by rfl) ⟨36197, by rfl⟩ : syracuseStep 3088853 = 72395) (by norm_num)
theorem B2059235 : Blo 2057435 2059235 := bstep (se 1 (by rfl) ⟨1544426, by rfl⟩ : syracuseStep 2059235 = 3088853) B3088853
theorem B7818677 : Blo 2057435 7818677 := bbase (se 5 (by rfl) ⟨366500, by rfl⟩ : syracuseStep 7818677 = 733001) (by norm_num)
theorem B5212451 : Blo 2057435 5212451 := bstep (se 1 (by rfl) ⟨3909338, by rfl⟩ : syracuseStep 5212451 = 7818677) B7818677
theorem B3474967 : Blo 2057435 3474967 := bstep (se 1 (by rfl) ⟨2606225, by rfl⟩ : syracuseStep 3474967 = 5212451) B5212451
theorem B4633289 : Blo 2057435 4633289 := bstep (se 2 (by rfl) ⟨1737483, by rfl⟩ : syracuseStep 4633289 = 3474967) B3474967
theorem B3088859 : Blo 2057435 3088859 := bstep (se 1 (by rfl) ⟨2316644, by rfl⟩ : syracuseStep 3088859 = 4633289) B4633289
theorem B2059239 : Blo 2057435 2059239 := bstep (se 1 (by rfl) ⟨1544429, by rfl⟩ : syracuseStep 2059239 = 3088859) B3088859
theorem B2316649 : Blo 2057435 2316649 := bbase (se 2 (by rfl) ⟨868743, by rfl⟩ : syracuseStep 2316649 = 1737487) (by norm_num)
theorem B3088865 : Blo 2057435 3088865 := bstep (se 2 (by rfl) ⟨1158324, by rfl⟩ : syracuseStep 3088865 = 2316649) B2316649
theorem B2059243 : Blo 2057435 2059243 := bstep (se 1 (by rfl) ⟨1544432, by rfl⟩ : syracuseStep 2059243 = 3088865) B3088865
theorem B21134357 : Blo 2057435 21134357 := bbase (se 6 (by rfl) ⟨495336, by rfl⟩ : syracuseStep 21134357 = 990673) (by norm_num)
theorem B14089571 : Blo 2057435 14089571 := bstep (se 1 (by rfl) ⟨10567178, by rfl⟩ : syracuseStep 14089571 = 21134357) B21134357
theorem B9393047 : Blo 2057435 9393047 := bstep (se 1 (by rfl) ⟨7044785, by rfl⟩ : syracuseStep 9393047 = 14089571) B14089571
theorem B6262031 : Blo 2057435 6262031 := bstep (se 1 (by rfl) ⟨4696523, by rfl⟩ : syracuseStep 6262031 = 9393047) B9393047
theorem B4174687 : Blo 2057435 4174687 := bstep (se 1 (by rfl) ⟨3131015, by rfl⟩ : syracuseStep 4174687 = 6262031) B6262031
theorem B5566249 : Blo 2057435 5566249 := bstep (se 2 (by rfl) ⟨2087343, by rfl⟩ : syracuseStep 5566249 = 4174687) B4174687
theorem B7421665 : Blo 2057435 7421665 := bstep (se 2 (by rfl) ⟨2783124, by rfl⟩ : syracuseStep 7421665 = 5566249) B5566249
theorem B9895553 : Blo 2057435 9895553 := bstep (se 2 (by rfl) ⟨3710832, by rfl⟩ : syracuseStep 9895553 = 7421665) B7421665
theorem B6597035 : Blo 2057435 6597035 := bstep (se 1 (by rfl) ⟨4947776, by rfl⟩ : syracuseStep 6597035 = 9895553) B9895553
theorem B4398023 : Blo 2057435 4398023 := bstep (se 1 (by rfl) ⟨3298517, by rfl⟩ : syracuseStep 4398023 = 6597035) B6597035
theorem B11728061 : Blo 2057435 11728061 := bstep (se 3 (by rfl) ⟨2199011, by rfl⟩ : syracuseStep 11728061 = 4398023) B4398023
theorem B7818707 : Blo 2057435 7818707 := bstep (se 1 (by rfl) ⟨5864030, by rfl⟩ : syracuseStep 7818707 = 11728061) B11728061
theorem B5212471 : Blo 2057435 5212471 := bstep (se 1 (by rfl) ⟨3909353, by rfl⟩ : syracuseStep 5212471 = 7818707) B7818707
theorem B6949961 : Blo 2057435 6949961 := bstep (se 2 (by rfl) ⟨2606235, by rfl⟩ : syracuseStep 6949961 = 5212471) B5212471
theorem B4633307 : Blo 2057435 4633307 := bstep (se 1 (by rfl) ⟨3474980, by rfl⟩ : syracuseStep 4633307 = 6949961) B6949961
theorem B3088871 : Blo 2057435 3088871 := bstep (se 1 (by rfl) ⟨2316653, by rfl⟩ : syracuseStep 3088871 = 4633307) B4633307
theorem B2059247 : Blo 2057435 2059247 := bstep (se 1 (by rfl) ⟨1544435, by rfl⟩ : syracuseStep 2059247 = 3088871) B3088871
theorem B3088877 : Blo 2057435 3088877 := bbase (se 3 (by rfl) ⟨579164, by rfl⟩ : syracuseStep 3088877 = 1158329) (by norm_num)
theorem B2059251 : Blo 2057435 2059251 := bstep (se 1 (by rfl) ⟨1544438, by rfl⟩ : syracuseStep 2059251 = 3088877) B3088877
theorem B4633325 : Blo 2057435 4633325 := bbase (se 3 (by rfl) ⟨868748, by rfl⟩ : syracuseStep 4633325 = 1737497) (by norm_num)
theorem B3088883 : Blo 2057435 3088883 := bstep (se 1 (by rfl) ⟨2316662, by rfl⟩ : syracuseStep 3088883 = 4633325) B4633325
theorem B2059255 : Blo 2057435 2059255 := bstep (se 1 (by rfl) ⟨1544441, by rfl⟩ : syracuseStep 2059255 = 3088883) B3088883
theorem B2199025 : Blo 2057435 2199025 := bbase (se 2 (by rfl) ⟨824634, by rfl⟩ : syracuseStep 2199025 = 1649269) (by norm_num)
theorem B2932033 : Blo 2057435 2932033 := bstep (se 2 (by rfl) ⟨1099512, by rfl⟩ : syracuseStep 2932033 = 2199025) B2199025
theorem B3909377 : Blo 2057435 3909377 := bstep (se 2 (by rfl) ⟨1466016, by rfl⟩ : syracuseStep 3909377 = 2932033) B2932033
theorem B2606251 : Blo 2057435 2606251 := bstep (se 1 (by rfl) ⟨1954688, by rfl⟩ : syracuseStep 2606251 = 3909377) B3909377
theorem B3475001 : Blo 2057435 3475001 := bstep (se 2 (by rfl) ⟨1303125, by rfl⟩ : syracuseStep 3475001 = 2606251) B2606251
theorem B2316667 : Blo 2057435 2316667 := bstep (se 1 (by rfl) ⟨1737500, by rfl⟩ : syracuseStep 2316667 = 3475001) B3475001
theorem B3088889 : Blo 2057435 3088889 := bstep (se 2 (by rfl) ⟨1158333, by rfl⟩ : syracuseStep 3088889 = 2316667) B2316667
theorem B2059259 : Blo 2057435 2059259 := bstep (se 1 (by rfl) ⟨1544444, by rfl⟩ : syracuseStep 2059259 = 3088889) B3088889
theorem B5283629 : Blo 2057435 5283629 := bbase (se 3 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 5283629 = 1981361) (by norm_num)
theorem B3522419 : Blo 2057435 3522419 := bstep (se 1 (by rfl) ⟨2641814, by rfl⟩ : syracuseStep 3522419 = 5283629) B5283629
theorem B2348279 : Blo 2057435 2348279 := bstep (se 1 (by rfl) ⟨1761209, by rfl⟩ : syracuseStep 2348279 = 3522419) B3522419
theorem B100193237 : Blo 2057435 100193237 := bstep (se 7 (by rfl) ⟨1174139, by rfl⟩ : syracuseStep 100193237 = 2348279) B2348279
theorem B66795491 : Blo 2057435 66795491 := bstep (se 1 (by rfl) ⟨50096618, by rfl⟩ : syracuseStep 66795491 = 100193237) B100193237
theorem B44530327 : Blo 2057435 44530327 := bstep (se 1 (by rfl) ⟨33397745, by rfl⟩ : syracuseStep 44530327 = 66795491) B66795491
theorem B59373769 : Blo 2057435 59373769 := bstep (se 2 (by rfl) ⟨22265163, by rfl⟩ : syracuseStep 59373769 = 44530327) B44530327
theorem B79165025 : Blo 2057435 79165025 := bstep (se 2 (by rfl) ⟨29686884, by rfl⟩ : syracuseStep 79165025 = 59373769) B59373769
theorem B52776683 : Blo 2057435 52776683 := bstep (se 1 (by rfl) ⟨39582512, by rfl⟩ : syracuseStep 52776683 = 79165025) B79165025
theorem B35184455 : Blo 2057435 35184455 := bstep (se 1 (by rfl) ⟨26388341, by rfl⟩ : syracuseStep 35184455 = 52776683) B52776683
theorem B23456303 : Blo 2057435 23456303 := bstep (se 1 (by rfl) ⟨17592227, by rfl⟩ : syracuseStep 23456303 = 35184455) B35184455
theorem B15637535 : Blo 2057435 15637535 := bstep (se 1 (by rfl) ⟨11728151, by rfl⟩ : syracuseStep 15637535 = 23456303) B23456303
theorem B10425023 : Blo 2057435 10425023 := bstep (se 1 (by rfl) ⟨7818767, by rfl⟩ : syracuseStep 10425023 = 15637535) B15637535
theorem B6950015 : Blo 2057435 6950015 := bstep (se 1 (by rfl) ⟨5212511, by rfl⟩ : syracuseStep 6950015 = 10425023) B10425023
theorem B4633343 : Blo 2057435 4633343 := bstep (se 1 (by rfl) ⟨3475007, by rfl⟩ : syracuseStep 4633343 = 6950015) B6950015
theorem B3088895 : Blo 2057435 3088895 := bstep (se 1 (by rfl) ⟨2316671, by rfl⟩ : syracuseStep 3088895 = 4633343) B4633343
theorem B2059263 : Blo 2057435 2059263 := bstep (se 1 (by rfl) ⟨1544447, by rfl⟩ : syracuseStep 2059263 = 3088895) B3088895
theorem B3088901 : Blo 2057435 3088901 := bbase (se 4 (by rfl) ⟨289584, by rfl⟩ : syracuseStep 3088901 = 579169) (by norm_num)
theorem B2059267 : Blo 2057435 2059267 := bstep (se 1 (by rfl) ⟨1544450, by rfl⟩ : syracuseStep 2059267 = 3088901) B3088901
theorem B3475021 : Blo 2057435 3475021 := bbase (se 3 (by rfl) ⟨651566, by rfl⟩ : syracuseStep 3475021 = 1303133) (by norm_num)
theorem B4633361 : Blo 2057435 4633361 := bstep (se 2 (by rfl) ⟨1737510, by rfl⟩ : syracuseStep 4633361 = 3475021) B3475021
theorem B3088907 : Blo 2057435 3088907 := bstep (se 1 (by rfl) ⟨2316680, by rfl⟩ : syracuseStep 3088907 = 4633361) B4633361
theorem B2059271 : Blo 2057435 2059271 := bstep (se 1 (by rfl) ⟨1544453, by rfl⟩ : syracuseStep 2059271 = 3088907) B3088907
theorem B2316685 : Blo 2057435 2316685 := bbase (se 3 (by rfl) ⟨434378, by rfl⟩ : syracuseStep 2316685 = 868757) (by norm_num)
theorem B3088913 : Blo 2057435 3088913 := bstep (se 2 (by rfl) ⟨1158342, by rfl⟩ : syracuseStep 3088913 = 2316685) B2316685
theorem B2059275 : Blo 2057435 2059275 := bstep (se 1 (by rfl) ⟨1544456, by rfl⟩ : syracuseStep 2059275 = 3088913) B3088913
theorem B6950069 : Blo 2057435 6950069 := bbase (se 5 (by rfl) ⟨325784, by rfl⟩ : syracuseStep 6950069 = 651569) (by norm_num)
theorem B4633379 : Blo 2057435 4633379 := bstep (se 1 (by rfl) ⟨3475034, by rfl⟩ : syracuseStep 4633379 = 6950069) B6950069
theorem B3088919 : Blo 2057435 3088919 := bstep (se 1 (by rfl) ⟨2316689, by rfl⟩ : syracuseStep 3088919 = 4633379) B4633379
theorem B2059279 : Blo 2057435 2059279 := bstep (se 1 (by rfl) ⟨1544459, by rfl⟩ : syracuseStep 2059279 = 3088919) B3088919
theorem B3088925 : Blo 2057435 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2059283 : Blo 2057435 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B4633397 : Blo 2057435 4633397 := bbase (se 5 (by rfl) ⟨217190, by rfl⟩ : syracuseStep 4633397 = 434381) (by norm_num)
theorem B3088931 : Blo 2057435 3088931 := bstep (se 1 (by rfl) ⟨2316698, by rfl⟩ : syracuseStep 3088931 = 4633397) B4633397
theorem B2059287 : Blo 2057435 2059287 := bstep (se 1 (by rfl) ⟨1544465, by rfl⟩ : syracuseStep 2059287 = 3088931) B3088931
theorem B9895765 : Blo 2057435 9895765 := bbase (se 9 (by rfl) ⟨28991, by rfl⟩ : syracuseStep 9895765 = 57983) (by norm_num)
theorem B13194353 : Blo 2057435 13194353 := bstep (se 2 (by rfl) ⟨4947882, by rfl⟩ : syracuseStep 13194353 = 9895765) B9895765
theorem B8796235 : Blo 2057435 8796235 := bstep (se 1 (by rfl) ⟨6597176, by rfl⟩ : syracuseStep 8796235 = 13194353) B13194353
theorem B11728313 : Blo 2057435 11728313 := bstep (se 2 (by rfl) ⟨4398117, by rfl⟩ : syracuseStep 11728313 = 8796235) B8796235
theorem B7818875 : Blo 2057435 7818875 := bstep (se 1 (by rfl) ⟨5864156, by rfl⟩ : syracuseStep 7818875 = 11728313) B11728313
theorem B5212583 : Blo 2057435 5212583 := bstep (se 1 (by rfl) ⟨3909437, by rfl⟩ : syracuseStep 5212583 = 7818875) B7818875
theorem B3475055 : Blo 2057435 3475055 := bstep (se 1 (by rfl) ⟨2606291, by rfl⟩ : syracuseStep 3475055 = 5212583) B5212583
theorem B2316703 : Blo 2057435 2316703 := bstep (se 1 (by rfl) ⟨1737527, by rfl⟩ : syracuseStep 2316703 = 3475055) B3475055
theorem B3088937 : Blo 2057435 3088937 := bstep (se 2 (by rfl) ⟨1158351, by rfl⟩ : syracuseStep 3088937 = 2316703) B2316703
theorem B2059291 : Blo 2057435 2059291 := bstep (se 1 (by rfl) ⟨1544468, by rfl⟩ : syracuseStep 2059291 = 3088937) B3088937
theorem B3012637 : Blo 2057435 3012637 := bbase (se 3 (by rfl) ⟨564869, by rfl⟩ : syracuseStep 3012637 = 1129739) (by norm_num)
theorem B4016849 : Blo 2057435 4016849 := bstep (se 2 (by rfl) ⟨1506318, by rfl⟩ : syracuseStep 4016849 = 3012637) B3012637
theorem B10711597 : Blo 2057435 10711597 := bstep (se 3 (by rfl) ⟨2008424, by rfl⟩ : syracuseStep 10711597 = 4016849) B4016849
theorem B14282129 : Blo 2057435 14282129 := bstep (se 2 (by rfl) ⟨5355798, by rfl⟩ : syracuseStep 14282129 = 10711597) B10711597
theorem B38085677 : Blo 2057435 38085677 := bstep (se 3 (by rfl) ⟨7141064, by rfl⟩ : syracuseStep 38085677 = 14282129) B14282129
theorem B25390451 : Blo 2057435 25390451 := bstep (se 1 (by rfl) ⟨19042838, by rfl⟩ : syracuseStep 25390451 = 38085677) B38085677
theorem B16926967 : Blo 2057435 16926967 := bstep (se 1 (by rfl) ⟨12695225, by rfl⟩ : syracuseStep 16926967 = 25390451) B25390451
theorem B22569289 : Blo 2057435 22569289 := bstep (se 2 (by rfl) ⟨8463483, by rfl⟩ : syracuseStep 22569289 = 16926967) B16926967
theorem B481478165 : Blo 2057435 481478165 := bstep (se 6 (by rfl) ⟨11284644, by rfl⟩ : syracuseStep 481478165 = 22569289) B22569289
theorem B320985443 : Blo 2057435 320985443 := bstep (se 1 (by rfl) ⟨240739082, by rfl⟩ : syracuseStep 320985443 = 481478165) B481478165
theorem B213990295 : Blo 2057435 213990295 := bstep (se 1 (by rfl) ⟨160492721, by rfl⟩ : syracuseStep 213990295 = 320985443) B320985443
theorem B285320393 : Blo 2057435 285320393 := bstep (se 2 (by rfl) ⟨106995147, by rfl⟩ : syracuseStep 285320393 = 213990295) B213990295
theorem B190213595 : Blo 2057435 190213595 := bstep (se 1 (by rfl) ⟨142660196, by rfl⟩ : syracuseStep 190213595 = 285320393) B285320393
theorem B126809063 : Blo 2057435 126809063 := bstep (se 1 (by rfl) ⟨95106797, by rfl⟩ : syracuseStep 126809063 = 190213595) B190213595
theorem B84539375 : Blo 2057435 84539375 := bstep (se 1 (by rfl) ⟨63404531, by rfl⟩ : syracuseStep 84539375 = 126809063) B126809063
theorem B56359583 : Blo 2057435 56359583 := bstep (se 1 (by rfl) ⟨42269687, by rfl⟩ : syracuseStep 56359583 = 84539375) B84539375
theorem B37573055 : Blo 2057435 37573055 := bstep (se 1 (by rfl) ⟨28179791, by rfl⟩ : syracuseStep 37573055 = 56359583) B56359583
theorem B25048703 : Blo 2057435 25048703 := bstep (se 1 (by rfl) ⟨18786527, by rfl⟩ : syracuseStep 25048703 = 37573055) B37573055
theorem B16699135 : Blo 2057435 16699135 := bstep (se 1 (by rfl) ⟨12524351, by rfl⟩ : syracuseStep 16699135 = 25048703) B25048703
theorem B22265513 : Blo 2057435 22265513 := bstep (se 2 (by rfl) ⟨8349567, by rfl⟩ : syracuseStep 22265513 = 16699135) B16699135
theorem B14843675 : Blo 2057435 14843675 := bstep (se 1 (by rfl) ⟨11132756, by rfl⟩ : syracuseStep 14843675 = 22265513) B22265513
theorem B9895783 : Blo 2057435 9895783 := bstep (se 1 (by rfl) ⟨7421837, by rfl⟩ : syracuseStep 9895783 = 14843675) B14843675
theorem B13194377 : Blo 2057435 13194377 := bstep (se 2 (by rfl) ⟨4947891, by rfl⟩ : syracuseStep 13194377 = 9895783) B9895783
theorem B8796251 : Blo 2057435 8796251 := bstep (se 1 (by rfl) ⟨6597188, by rfl⟩ : syracuseStep 8796251 = 13194377) B13194377
theorem B5864167 : Blo 2057435 5864167 := bstep (se 1 (by rfl) ⟨4398125, by rfl⟩ : syracuseStep 5864167 = 8796251) B8796251
theorem B7818889 : Blo 2057435 7818889 := bstep (se 2 (by rfl) ⟨2932083, by rfl⟩ : syracuseStep 7818889 = 5864167) B5864167
theorem B10425185 : Blo 2057435 10425185 := bstep (se 2 (by rfl) ⟨3909444, by rfl⟩ : syracuseStep 10425185 = 7818889) B7818889
theorem B6950123 : Blo 2057435 6950123 := bstep (se 1 (by rfl) ⟨5212592, by rfl⟩ : syracuseStep 6950123 = 10425185) B10425185
theorem B4633415 : Blo 2057435 4633415 := bstep (se 1 (by rfl) ⟨3475061, by rfl⟩ : syracuseStep 4633415 = 6950123) B6950123
theorem B3088943 : Blo 2057435 3088943 := bstep (se 1 (by rfl) ⟨2316707, by rfl⟩ : syracuseStep 3088943 = 4633415) B4633415
theorem B2059295 : Blo 2057435 2059295 := bstep (se 1 (by rfl) ⟨1544471, by rfl⟩ : syracuseStep 2059295 = 3088943) B3088943
theorem B3088949 : Blo 2057435 3088949 := bbase (se 5 (by rfl) ⟨144794, by rfl⟩ : syracuseStep 3088949 = 289589) (by norm_num)
theorem B2059299 : Blo 2057435 2059299 := bstep (se 1 (by rfl) ⟨1544474, by rfl⟩ : syracuseStep 2059299 = 3088949) B3088949
theorem B5212613 : Blo 2057435 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B3475075 : Blo 2057435 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B4633433 : Blo 2057435 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B3088955 : Blo 2057435 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B2059303 : Blo 2057435 2059303 := bstep (se 1 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 2059303 = 3088955) B3088955
theorem B2316721 : Blo 2057435 2316721 := bbase (se 2 (by rfl) ⟨868770, by rfl⟩ : syracuseStep 2316721 = 1737541) (by norm_num)
theorem B3088961 : Blo 2057435 3088961 := bstep (se 2 (by rfl) ⟨1158360, by rfl⟩ : syracuseStep 3088961 = 2316721) B2316721
theorem B2059307 : Blo 2057435 2059307 := bstep (se 1 (by rfl) ⟨1544480, by rfl⟩ : syracuseStep 2059307 = 3088961) B3088961
theorem B5864213 : Blo 2057435 5864213 := bbase (se 6 (by rfl) ⟨137442, by rfl⟩ : syracuseStep 5864213 = 274885) (by norm_num)
theorem B3909475 : Blo 2057435 3909475 := bstep (se 1 (by rfl) ⟨2932106, by rfl⟩ : syracuseStep 3909475 = 5864213) B5864213
theorem B5212633 : Blo 2057435 5212633 := bstep (se 2 (by rfl) ⟨1954737, by rfl⟩ : syracuseStep 5212633 = 3909475) B3909475
theorem B6950177 : Blo 2057435 6950177 := bstep (se 2 (by rfl) ⟨2606316, by rfl⟩ : syracuseStep 6950177 = 5212633) B5212633
theorem B4633451 : Blo 2057435 4633451 := bstep (se 1 (by rfl) ⟨3475088, by rfl⟩ : syracuseStep 4633451 = 6950177) B6950177
theorem B3088967 : Blo 2057435 3088967 := bstep (se 1 (by rfl) ⟨2316725, by rfl⟩ : syracuseStep 3088967 = 4633451) B4633451
theorem B2059311 : Blo 2057435 2059311 := bstep (se 1 (by rfl) ⟨1544483, by rfl⟩ : syracuseStep 2059311 = 3088967) B3088967
theorem B3088973 : Blo 2057435 3088973 := bbase (se 3 (by rfl) ⟨579182, by rfl⟩ : syracuseStep 3088973 = 1158365) (by norm_num)
theorem B2059315 : Blo 2057435 2059315 := bstep (se 1 (by rfl) ⟨1544486, by rfl⟩ : syracuseStep 2059315 = 3088973) B3088973
theorem B4633469 : Blo 2057435 4633469 := bbase (se 3 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 4633469 = 1737551) (by norm_num)
theorem B3088979 : Blo 2057435 3088979 := bstep (se 1 (by rfl) ⟨2316734, by rfl⟩ : syracuseStep 3088979 = 4633469) B4633469
theorem B2059319 : Blo 2057435 2059319 := bstep (se 1 (by rfl) ⟨1544489, by rfl⟩ : syracuseStep 2059319 = 3088979) B3088979
theorem B3475109 : Blo 2057435 3475109 := bbase (se 4 (by rfl) ⟨325791, by rfl⟩ : syracuseStep 3475109 = 651583) (by norm_num)
theorem B2316739 : Blo 2057435 2316739 := bstep (se 1 (by rfl) ⟨1737554, by rfl⟩ : syracuseStep 2316739 = 3475109) B3475109
theorem B3088985 : Blo 2057435 3088985 := bstep (se 2 (by rfl) ⟨1158369, by rfl⟩ : syracuseStep 3088985 = 2316739) B2316739
theorem B2059323 : Blo 2057435 2059323 := bstep (se 1 (by rfl) ⟨1544492, by rfl⟩ : syracuseStep 2059323 = 3088985) B3088985
theorem B2199097 : Blo 2057435 2199097 := bbase (se 2 (by rfl) ⟨824661, by rfl⟩ : syracuseStep 2199097 = 1649323) (by norm_num)
theorem B2932129 : Blo 2057435 2932129 := bstep (se 2 (by rfl) ⟨1099548, by rfl⟩ : syracuseStep 2932129 = 2199097) B2199097
theorem B15638021 : Blo 2057435 15638021 := bstep (se 4 (by rfl) ⟨1466064, by rfl⟩ : syracuseStep 15638021 = 2932129) B2932129
theorem B10425347 : Blo 2057435 10425347 := bstep (se 1 (by rfl) ⟨7819010, by rfl⟩ : syracuseStep 10425347 = 15638021) B15638021
theorem B6950231 : Blo 2057435 6950231 := bstep (se 1 (by rfl) ⟨5212673, by rfl⟩ : syracuseStep 6950231 = 10425347) B10425347
theorem B4633487 : Blo 2057435 4633487 := bstep (se 1 (by rfl) ⟨3475115, by rfl⟩ : syracuseStep 4633487 = 6950231) B6950231
theorem B3088991 : Blo 2057435 3088991 := bstep (se 1 (by rfl) ⟨2316743, by rfl⟩ : syracuseStep 3088991 = 4633487) B4633487
theorem B2059327 : Blo 2057435 2059327 := bstep (se 1 (by rfl) ⟨1544495, by rfl⟩ : syracuseStep 2059327 = 3088991) B3088991
theorem B3088997 : Blo 2057435 3088997 := bbase (se 4 (by rfl) ⟨289593, by rfl⟩ : syracuseStep 3088997 = 579187) (by norm_num)
theorem B2059331 : Blo 2057435 2059331 := bstep (se 1 (by rfl) ⟨1544498, by rfl⟩ : syracuseStep 2059331 = 3088997) B3088997
theorem B2932141 : Blo 2057435 2932141 := bbase (se 3 (by rfl) ⟨549776, by rfl⟩ : syracuseStep 2932141 = 1099553) (by norm_num)
theorem B3909521 : Blo 2057435 3909521 := bstep (se 2 (by rfl) ⟨1466070, by rfl⟩ : syracuseStep 3909521 = 2932141) B2932141
theorem B2606347 : Blo 2057435 2606347 := bstep (se 1 (by rfl) ⟨1954760, by rfl⟩ : syracuseStep 2606347 = 3909521) B3909521
theorem B3475129 : Blo 2057435 3475129 := bstep (se 2 (by rfl) ⟨1303173, by rfl⟩ : syracuseStep 3475129 = 2606347) B2606347
theorem B4633505 : Blo 2057435 4633505 := bstep (se 2 (by rfl) ⟨1737564, by rfl⟩ : syracuseStep 4633505 = 3475129) B3475129
theorem B3089003 : Blo 2057435 3089003 := bstep (se 1 (by rfl) ⟨2316752, by rfl⟩ : syracuseStep 3089003 = 4633505) B4633505
theorem B2059335 : Blo 2057435 2059335 := bstep (se 1 (by rfl) ⟨1544501, by rfl⟩ : syracuseStep 2059335 = 3089003) B3089003
theorem B2316757 : Blo 2057435 2316757 := bbase (se 7 (by rfl) ⟨27149, by rfl⟩ : syracuseStep 2316757 = 54299) (by norm_num)
theorem B3089009 : Blo 2057435 3089009 := bstep (se 2 (by rfl) ⟨1158378, by rfl⟩ : syracuseStep 3089009 = 2316757) B2316757
theorem B2059339 : Blo 2057435 2059339 := bstep (se 1 (by rfl) ⟨1544504, by rfl⟩ : syracuseStep 2059339 = 3089009) B3089009
theorem B2606357 : Blo 2057435 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B6950285 : Blo 2057435 6950285 := bstep (se 3 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 6950285 = 2606357) B2606357
theorem B4633523 : Blo 2057435 4633523 := bstep (se 1 (by rfl) ⟨3475142, by rfl⟩ : syracuseStep 4633523 = 6950285) B6950285
theorem B3089015 : Blo 2057435 3089015 := bstep (se 1 (by rfl) ⟨2316761, by rfl⟩ : syracuseStep 3089015 = 4633523) B4633523
theorem B2059343 : Blo 2057435 2059343 := bstep (se 1 (by rfl) ⟨1544507, by rfl⟩ : syracuseStep 2059343 = 3089015) B3089015
theorem B3089021 : Blo 2057435 3089021 := bbase (se 3 (by rfl) ⟨579191, by rfl⟩ : syracuseStep 3089021 = 1158383) (by norm_num)
theorem B2059347 : Blo 2057435 2059347 := bstep (se 1 (by rfl) ⟨1544510, by rfl⟩ : syracuseStep 2059347 = 3089021) B3089021
theorem B4633541 : Blo 2057435 4633541 := bbase (se 4 (by rfl) ⟨434394, by rfl⟩ : syracuseStep 4633541 = 868789) (by norm_num)
theorem B3089027 : Blo 2057435 3089027 := bstep (se 1 (by rfl) ⟨2316770, by rfl⟩ : syracuseStep 3089027 = 4633541) B4633541
theorem B2059351 : Blo 2057435 2059351 := bstep (se 1 (by rfl) ⟨1544513, by rfl⟩ : syracuseStep 2059351 = 3089027) B3089027
theorem B4948037 : Blo 2057435 4948037 := bbase (se 4 (by rfl) ⟨463878, by rfl⟩ : syracuseStep 4948037 = 927757) (by norm_num)
theorem B3298691 : Blo 2057435 3298691 := bstep (se 1 (by rfl) ⟨2474018, by rfl⟩ : syracuseStep 3298691 = 4948037) B4948037
theorem B8796509 : Blo 2057435 8796509 := bstep (se 3 (by rfl) ⟨1649345, by rfl⟩ : syracuseStep 8796509 = 3298691) B3298691
theorem B5864339 : Blo 2057435 5864339 := bstep (se 1 (by rfl) ⟨4398254, by rfl⟩ : syracuseStep 5864339 = 8796509) B8796509
theorem B3909559 : Blo 2057435 3909559 := bstep (se 1 (by rfl) ⟨2932169, by rfl⟩ : syracuseStep 3909559 = 5864339) B5864339
theorem B5212745 : Blo 2057435 5212745 := bstep (se 2 (by rfl) ⟨1954779, by rfl⟩ : syracuseStep 5212745 = 3909559) B3909559
theorem B3475163 : Blo 2057435 3475163 := bstep (se 1 (by rfl) ⟨2606372, by rfl⟩ : syracuseStep 3475163 = 5212745) B5212745
theorem B2316775 : Blo 2057435 2316775 := bstep (se 1 (by rfl) ⟨1737581, by rfl⟩ : syracuseStep 2316775 = 3475163) B3475163
theorem B3089033 : Blo 2057435 3089033 := bstep (se 2 (by rfl) ⟨1158387, by rfl⟩ : syracuseStep 3089033 = 2316775) B2316775
theorem B2059355 : Blo 2057435 2059355 := bstep (se 1 (by rfl) ⟨1544516, by rfl⟩ : syracuseStep 2059355 = 3089033) B3089033
theorem B10425509 : Blo 2057435 10425509 := bbase (se 4 (by rfl) ⟨977391, by rfl⟩ : syracuseStep 10425509 = 1954783) (by norm_num)
theorem B6950339 : Blo 2057435 6950339 := bstep (se 1 (by rfl) ⟨5212754, by rfl⟩ : syracuseStep 6950339 = 10425509) B10425509
theorem B4633559 : Blo 2057435 4633559 := bstep (se 1 (by rfl) ⟨3475169, by rfl⟩ : syracuseStep 4633559 = 6950339) B6950339
theorem B3089039 : Blo 2057435 3089039 := bstep (se 1 (by rfl) ⟨2316779, by rfl⟩ : syracuseStep 3089039 = 4633559) B4633559
theorem B2059359 : Blo 2057435 2059359 := bstep (se 1 (by rfl) ⟨1544519, by rfl⟩ : syracuseStep 2059359 = 3089039) B3089039
theorem B3089045 : Blo 2057435 3089045 := bbase (se 6 (by rfl) ⟨72399, by rfl⟩ : syracuseStep 3089045 = 144799) (by norm_num)
theorem B2059363 : Blo 2057435 2059363 := bstep (se 1 (by rfl) ⟨1544522, by rfl⟩ : syracuseStep 2059363 = 3089045) B3089045
theorem B2087465 : Blo 2057435 2087465 := bbase (se 2 (by rfl) ⟨782799, by rfl⟩ : syracuseStep 2087465 = 1565599) (by norm_num)
theorem B5566573 : Blo 2057435 5566573 := bstep (se 3 (by rfl) ⟨1043732, by rfl⟩ : syracuseStep 5566573 = 2087465) B2087465
theorem B29688389 : Blo 2057435 29688389 := bstep (se 4 (by rfl) ⟨2783286, by rfl⟩ : syracuseStep 29688389 = 5566573) B5566573
theorem B19792259 : Blo 2057435 19792259 := bstep (se 1 (by rfl) ⟨14844194, by rfl⟩ : syracuseStep 19792259 = 29688389) B29688389
theorem B13194839 : Blo 2057435 13194839 := bstep (se 1 (by rfl) ⟨9896129, by rfl⟩ : syracuseStep 13194839 = 19792259) B19792259
theorem B8796559 : Blo 2057435 8796559 := bstep (se 1 (by rfl) ⟨6597419, by rfl⟩ : syracuseStep 8796559 = 13194839) B13194839
theorem B11728745 : Blo 2057435 11728745 := bstep (se 2 (by rfl) ⟨4398279, by rfl⟩ : syracuseStep 11728745 = 8796559) B8796559
theorem B7819163 : Blo 2057435 7819163 := bstep (se 1 (by rfl) ⟨5864372, by rfl⟩ : syracuseStep 7819163 = 11728745) B11728745
theorem B5212775 : Blo 2057435 5212775 := bstep (se 1 (by rfl) ⟨3909581, by rfl⟩ : syracuseStep 5212775 = 7819163) B7819163
theorem B3475183 : Blo 2057435 3475183 := bstep (se 1 (by rfl) ⟨2606387, by rfl⟩ : syracuseStep 3475183 = 5212775) B5212775
theorem B4633577 : Blo 2057435 4633577 := bstep (se 2 (by rfl) ⟨1737591, by rfl⟩ : syracuseStep 4633577 = 3475183) B3475183
theorem B3089051 : Blo 2057435 3089051 := bstep (se 1 (by rfl) ⟨2316788, by rfl⟩ : syracuseStep 3089051 = 4633577) B4633577
theorem B2059367 : Blo 2057435 2059367 := bstep (se 1 (by rfl) ⟨1544525, by rfl⟩ : syracuseStep 2059367 = 3089051) B3089051
theorem B2316793 : Blo 2057435 2316793 := bbase (se 2 (by rfl) ⟨868797, by rfl⟩ : syracuseStep 2316793 = 1737595) (by norm_num)
theorem B3089057 : Blo 2057435 3089057 := bstep (se 2 (by rfl) ⟨1158396, by rfl⟩ : syracuseStep 3089057 = 2316793) B2316793
theorem B2059371 : Blo 2057435 2059371 := bstep (se 1 (by rfl) ⟨1544528, by rfl⟩ : syracuseStep 2059371 = 3089057) B3089057
theorem B6597445 : Blo 2057435 6597445 := bbase (se 4 (by rfl) ⟨618510, by rfl⟩ : syracuseStep 6597445 = 1237021) (by norm_num)
theorem B8796593 : Blo 2057435 8796593 := bstep (se 2 (by rfl) ⟨3298722, by rfl⟩ : syracuseStep 8796593 = 6597445) B6597445
theorem B5864395 : Blo 2057435 5864395 := bstep (se 1 (by rfl) ⟨4398296, by rfl⟩ : syracuseStep 5864395 = 8796593) B8796593
theorem B7819193 : Blo 2057435 7819193 := bstep (se 2 (by rfl) ⟨2932197, by rfl⟩ : syracuseStep 7819193 = 5864395) B5864395
theorem B5212795 : Blo 2057435 5212795 := bstep (se 1 (by rfl) ⟨3909596, by rfl⟩ : syracuseStep 5212795 = 7819193) B7819193
theorem B6950393 : Blo 2057435 6950393 := bstep (se 2 (by rfl) ⟨2606397, by rfl⟩ : syracuseStep 6950393 = 5212795) B5212795
theorem B4633595 : Blo 2057435 4633595 := bstep (se 1 (by rfl) ⟨3475196, by rfl⟩ : syracuseStep 4633595 = 6950393) B6950393
theorem B3089063 : Blo 2057435 3089063 := bstep (se 1 (by rfl) ⟨2316797, by rfl⟩ : syracuseStep 3089063 = 4633595) B4633595
theorem B2059375 : Blo 2057435 2059375 := bstep (se 1 (by rfl) ⟨1544531, by rfl⟩ : syracuseStep 2059375 = 3089063) B3089063
theorem B3089069 : Blo 2057435 3089069 := bbase (se 3 (by rfl) ⟨579200, by rfl⟩ : syracuseStep 3089069 = 1158401) (by norm_num)
theorem B2059379 : Blo 2057435 2059379 := bstep (se 1 (by rfl) ⟨1544534, by rfl⟩ : syracuseStep 2059379 = 3089069) B3089069
theorem B4633613 : Blo 2057435 4633613 := bbase (se 3 (by rfl) ⟨868802, by rfl⟩ : syracuseStep 4633613 = 1737605) (by norm_num)
theorem B3089075 : Blo 2057435 3089075 := bstep (se 1 (by rfl) ⟨2316806, by rfl⟩ : syracuseStep 3089075 = 4633613) B4633613
theorem B2059383 : Blo 2057435 2059383 := bstep (se 1 (by rfl) ⟨1544537, by rfl⟩ : syracuseStep 2059383 = 3089075) B3089075
theorem B2606413 : Blo 2057435 2606413 := bbase (se 3 (by rfl) ⟨488702, by rfl⟩ : syracuseStep 2606413 = 977405) (by norm_num)
theorem B3475217 : Blo 2057435 3475217 := bstep (se 2 (by rfl) ⟨1303206, by rfl⟩ : syracuseStep 3475217 = 2606413) B2606413
theorem B2316811 : Blo 2057435 2316811 := bstep (se 1 (by rfl) ⟨1737608, by rfl⟩ : syracuseStep 2316811 = 3475217) B3475217
theorem B3089081 : Blo 2057435 3089081 := bstep (se 2 (by rfl) ⟨1158405, by rfl⟩ : syracuseStep 3089081 = 2316811) B2316811
theorem B2059387 : Blo 2057435 2059387 := bstep (se 1 (by rfl) ⟨1544540, by rfl⟩ : syracuseStep 2059387 = 3089081) B3089081
theorem B6347909 : Blo 2057435 6347909 := bbase (se 4 (by rfl) ⟨595116, by rfl⟩ : syracuseStep 6347909 = 1190233) (by norm_num)
theorem B16927757 : Blo 2057435 16927757 := bstep (se 3 (by rfl) ⟨3173954, by rfl⟩ : syracuseStep 16927757 = 6347909) B6347909
theorem B11285171 : Blo 2057435 11285171 := bstep (se 1 (by rfl) ⟨8463878, by rfl⟩ : syracuseStep 11285171 = 16927757) B16927757
theorem B7523447 : Blo 2057435 7523447 := bstep (se 1 (by rfl) ⟨5642585, by rfl⟩ : syracuseStep 7523447 = 11285171) B11285171
theorem B20062525 : Blo 2057435 20062525 := bstep (se 3 (by rfl) ⟨3761723, by rfl⟩ : syracuseStep 20062525 = 7523447) B7523447
theorem B26750033 : Blo 2057435 26750033 := bstep (se 2 (by rfl) ⟨10031262, by rfl⟩ : syracuseStep 26750033 = 20062525) B20062525
theorem B17833355 : Blo 2057435 17833355 := bstep (se 1 (by rfl) ⟨13375016, by rfl⟩ : syracuseStep 17833355 = 26750033) B26750033
theorem B11888903 : Blo 2057435 11888903 := bstep (se 1 (by rfl) ⟨8916677, by rfl⟩ : syracuseStep 11888903 = 17833355) B17833355
theorem B7925935 : Blo 2057435 7925935 := bstep (se 1 (by rfl) ⟨5944451, by rfl⟩ : syracuseStep 7925935 = 11888903) B11888903
theorem B10567913 : Blo 2057435 10567913 := bstep (se 2 (by rfl) ⟨3962967, by rfl⟩ : syracuseStep 10567913 = 7925935) B7925935
theorem B112724405 : Blo 2057435 112724405 := bstep (se 5 (by rfl) ⟨5283956, by rfl⟩ : syracuseStep 112724405 = 10567913) B10567913
theorem B75149603 : Blo 2057435 75149603 := bstep (se 1 (by rfl) ⟨56362202, by rfl⟩ : syracuseStep 75149603 = 112724405) B112724405
theorem B50099735 : Blo 2057435 50099735 := bstep (se 1 (by rfl) ⟨37574801, by rfl⟩ : syracuseStep 50099735 = 75149603) B75149603
theorem B33399823 : Blo 2057435 33399823 := bstep (se 1 (by rfl) ⟨25049867, by rfl⟩ : syracuseStep 33399823 = 50099735) B50099735
theorem B44533097 : Blo 2057435 44533097 := bstep (se 2 (by rfl) ⟨16699911, by rfl⟩ : syracuseStep 44533097 = 33399823) B33399823
theorem B29688731 : Blo 2057435 29688731 := bstep (se 1 (by rfl) ⟨22266548, by rfl⟩ : syracuseStep 29688731 = 44533097) B44533097
theorem B19792487 : Blo 2057435 19792487 := bstep (se 1 (by rfl) ⟨14844365, by rfl⟩ : syracuseStep 19792487 = 29688731) B29688731
theorem B13194991 : Blo 2057435 13194991 := bstep (se 1 (by rfl) ⟨9896243, by rfl⟩ : syracuseStep 13194991 = 19792487) B19792487
theorem B17593321 : Blo 2057435 17593321 := bstep (se 2 (by rfl) ⟨6597495, by rfl⟩ : syracuseStep 17593321 = 13194991) B13194991
theorem B23457761 : Blo 2057435 23457761 := bstep (se 2 (by rfl) ⟨8796660, by rfl⟩ : syracuseStep 23457761 = 17593321) B17593321
theorem B15638507 : Blo 2057435 15638507 := bstep (se 1 (by rfl) ⟨11728880, by rfl⟩ : syracuseStep 15638507 = 23457761) B23457761
theorem B10425671 : Blo 2057435 10425671 := bstep (se 1 (by rfl) ⟨7819253, by rfl⟩ : syracuseStep 10425671 = 15638507) B15638507
theorem B6950447 : Blo 2057435 6950447 := bstep (se 1 (by rfl) ⟨5212835, by rfl⟩ : syracuseStep 6950447 = 10425671) B10425671
theorem B4633631 : Blo 2057435 4633631 := bstep (se 1 (by rfl) ⟨3475223, by rfl⟩ : syracuseStep 4633631 = 6950447) B6950447
theorem B3089087 : Blo 2057435 3089087 := bstep (se 1 (by rfl) ⟨2316815, by rfl⟩ : syracuseStep 3089087 = 4633631) B4633631
theorem B2059391 : Blo 2057435 2059391 := bstep (se 1 (by rfl) ⟨1544543, by rfl⟩ : syracuseStep 2059391 = 3089087) B3089087
theorem B3089093 : Blo 2057435 3089093 := bbase (se 4 (by rfl) ⟨289602, by rfl⟩ : syracuseStep 3089093 = 579205) (by norm_num)
theorem B2059395 : Blo 2057435 2059395 := bstep (se 1 (by rfl) ⟨1544546, by rfl⟩ : syracuseStep 2059395 = 3089093) B3089093
theorem B3475237 : Blo 2057435 3475237 := bbase (se 4 (by rfl) ⟨325803, by rfl⟩ : syracuseStep 3475237 = 651607) (by norm_num)
theorem B4633649 : Blo 2057435 4633649 := bstep (se 2 (by rfl) ⟨1737618, by rfl⟩ : syracuseStep 4633649 = 3475237) B3475237
theorem B3089099 : Blo 2057435 3089099 := bstep (se 1 (by rfl) ⟨2316824, by rfl⟩ : syracuseStep 3089099 = 4633649) B4633649
theorem B2059399 : Blo 2057435 2059399 := bstep (se 1 (by rfl) ⟨1544549, by rfl⟩ : syracuseStep 2059399 = 3089099) B3089099
theorem B2316829 : Blo 2057435 2316829 := bbase (se 3 (by rfl) ⟨434405, by rfl⟩ : syracuseStep 2316829 = 868811) (by norm_num)
theorem B3089105 : Blo 2057435 3089105 := bstep (se 2 (by rfl) ⟨1158414, by rfl⟩ : syracuseStep 3089105 = 2316829) B2316829
theorem B2059403 : Blo 2057435 2059403 := bstep (se 1 (by rfl) ⟨1544552, by rfl⟩ : syracuseStep 2059403 = 3089105) B3089105
theorem B6950501 : Blo 2057435 6950501 := bbase (se 4 (by rfl) ⟨651609, by rfl⟩ : syracuseStep 6950501 = 1303219) (by norm_num)
theorem B4633667 : Blo 2057435 4633667 := bstep (se 1 (by rfl) ⟨3475250, by rfl⟩ : syracuseStep 4633667 = 6950501) B6950501
theorem B3089111 : Blo 2057435 3089111 := bstep (se 1 (by rfl) ⟨2316833, by rfl⟩ : syracuseStep 3089111 = 4633667) B4633667
theorem B2059407 : Blo 2057435 2059407 := bstep (se 1 (by rfl) ⟨1544555, by rfl⟩ : syracuseStep 2059407 = 3089111) B3089111
theorem B3089117 : Blo 2057435 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B2059411 : Blo 2057435 2059411 := bstep (se 1 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 2059411 = 3089117) B3089117
theorem B4633685 : Blo 2057435 4633685 := bbase (se 8 (by rfl) ⟨27150, by rfl⟩ : syracuseStep 4633685 = 54301) (by norm_num)
theorem B3089123 : Blo 2057435 3089123 := bstep (se 1 (by rfl) ⟨2316842, by rfl⟩ : syracuseStep 3089123 = 4633685) B4633685
theorem B2059415 : Blo 2057435 2059415 := bstep (se 1 (by rfl) ⟨1544561, by rfl⟩ : syracuseStep 2059415 = 3089123) B3089123
theorem B19303829 : Blo 2057435 19303829 := bbase (se 6 (by rfl) ⟨452433, by rfl⟩ : syracuseStep 19303829 = 904867) (by norm_num)
theorem B12869219 : Blo 2057435 12869219 := bstep (se 1 (by rfl) ⟨9651914, by rfl⟩ : syracuseStep 12869219 = 19303829) B19303829
theorem B8579479 : Blo 2057435 8579479 := bstep (se 1 (by rfl) ⟨6434609, by rfl⟩ : syracuseStep 8579479 = 12869219) B12869219
theorem B11439305 : Blo 2057435 11439305 := bstep (se 2 (by rfl) ⟨4289739, by rfl⟩ : syracuseStep 11439305 = 8579479) B8579479
theorem B7626203 : Blo 2057435 7626203 := bstep (se 1 (by rfl) ⟨5719652, by rfl⟩ : syracuseStep 7626203 = 11439305) B11439305
theorem B5084135 : Blo 2057435 5084135 := bstep (se 1 (by rfl) ⟨3813101, by rfl⟩ : syracuseStep 5084135 = 7626203) B7626203
theorem B3389423 : Blo 2057435 3389423 := bstep (se 1 (by rfl) ⟨2542067, by rfl⟩ : syracuseStep 3389423 = 5084135) B5084135
theorem B9038461 : Blo 2057435 9038461 := bstep (se 3 (by rfl) ⟨1694711, by rfl⟩ : syracuseStep 9038461 = 3389423) B3389423
theorem B12051281 : Blo 2057435 12051281 := bstep (se 2 (by rfl) ⟨4519230, by rfl⟩ : syracuseStep 12051281 = 9038461) B9038461
theorem B32136749 : Blo 2057435 32136749 := bstep (se 3 (by rfl) ⟨6025640, by rfl⟩ : syracuseStep 32136749 = 12051281) B12051281
theorem B21424499 : Blo 2057435 21424499 := bstep (se 1 (by rfl) ⟨16068374, by rfl⟩ : syracuseStep 21424499 = 32136749) B32136749
theorem B14282999 : Blo 2057435 14282999 := bstep (se 1 (by rfl) ⟨10712249, by rfl⟩ : syracuseStep 14282999 = 21424499) B21424499
theorem B9521999 : Blo 2057435 9521999 := bstep (se 1 (by rfl) ⟨7141499, by rfl⟩ : syracuseStep 9521999 = 14282999) B14282999
theorem B6347999 : Blo 2057435 6347999 := bstep (se 1 (by rfl) ⟨4760999, by rfl⟩ : syracuseStep 6347999 = 9521999) B9521999
theorem B4231999 : Blo 2057435 4231999 := bstep (se 1 (by rfl) ⟨3173999, by rfl⟩ : syracuseStep 4231999 = 6347999) B6347999
theorem B5642665 : Blo 2057435 5642665 := bstep (se 2 (by rfl) ⟨2115999, by rfl⟩ : syracuseStep 5642665 = 4231999) B4231999
theorem B120376853 : Blo 2057435 120376853 := bstep (se 6 (by rfl) ⟨2821332, by rfl⟩ : syracuseStep 120376853 = 5642665) B5642665
theorem B80251235 : Blo 2057435 80251235 := bstep (se 1 (by rfl) ⟨60188426, by rfl⟩ : syracuseStep 80251235 = 120376853) B120376853
theorem B53500823 : Blo 2057435 53500823 := bstep (se 1 (by rfl) ⟨40125617, by rfl⟩ : syracuseStep 53500823 = 80251235) B80251235
theorem B35667215 : Blo 2057435 35667215 := bstep (se 1 (by rfl) ⟨26750411, by rfl⟩ : syracuseStep 35667215 = 53500823) B53500823
theorem B23778143 : Blo 2057435 23778143 := bstep (se 1 (by rfl) ⟨17833607, by rfl⟩ : syracuseStep 23778143 = 35667215) B35667215
theorem B15852095 : Blo 2057435 15852095 := bstep (se 1 (by rfl) ⟨11889071, by rfl⟩ : syracuseStep 15852095 = 23778143) B23778143
theorem B10568063 : Blo 2057435 10568063 := bstep (se 1 (by rfl) ⟨7926047, by rfl⟩ : syracuseStep 10568063 = 15852095) B15852095
theorem B7045375 : Blo 2057435 7045375 := bstep (se 1 (by rfl) ⟨5284031, by rfl⟩ : syracuseStep 7045375 = 10568063) B10568063
theorem B9393833 : Blo 2057435 9393833 := bstep (se 2 (by rfl) ⟨3522687, by rfl⟩ : syracuseStep 9393833 = 7045375) B7045375
theorem B6262555 : Blo 2057435 6262555 := bstep (se 1 (by rfl) ⟨4696916, by rfl⟩ : syracuseStep 6262555 = 9393833) B9393833
theorem B8350073 : Blo 2057435 8350073 := bstep (se 2 (by rfl) ⟨3131277, by rfl⟩ : syracuseStep 8350073 = 6262555) B6262555
theorem B5566715 : Blo 2057435 5566715 := bstep (se 1 (by rfl) ⟨4175036, by rfl⟩ : syracuseStep 5566715 = 8350073) B8350073
theorem B3711143 : Blo 2057435 3711143 := bstep (se 1 (by rfl) ⟨2783357, by rfl⟩ : syracuseStep 3711143 = 5566715) B5566715
theorem B9896381 : Blo 2057435 9896381 := bstep (se 3 (by rfl) ⟨1855571, by rfl⟩ : syracuseStep 9896381 = 3711143) B3711143
theorem B6597587 : Blo 2057435 6597587 := bstep (se 1 (by rfl) ⟨4948190, by rfl⟩ : syracuseStep 6597587 = 9896381) B9896381
theorem B4398391 : Blo 2057435 4398391 := bstep (se 1 (by rfl) ⟨3298793, by rfl⟩ : syracuseStep 4398391 = 6597587) B6597587
theorem B5864521 : Blo 2057435 5864521 := bstep (se 2 (by rfl) ⟨2199195, by rfl⟩ : syracuseStep 5864521 = 4398391) B4398391
theorem B7819361 : Blo 2057435 7819361 := bstep (se 2 (by rfl) ⟨2932260, by rfl⟩ : syracuseStep 7819361 = 5864521) B5864521
theorem B5212907 : Blo 2057435 5212907 := bstep (se 1 (by rfl) ⟨3909680, by rfl⟩ : syracuseStep 5212907 = 7819361) B7819361
theorem B3475271 : Blo 2057435 3475271 := bstep (se 1 (by rfl) ⟨2606453, by rfl⟩ : syracuseStep 3475271 = 5212907) B5212907
theorem B2316847 : Blo 2057435 2316847 := bstep (se 1 (by rfl) ⟨1737635, by rfl⟩ : syracuseStep 2316847 = 3475271) B3475271
theorem B3089129 : Blo 2057435 3089129 := bstep (se 2 (by rfl) ⟨1158423, by rfl⟩ : syracuseStep 3089129 = 2316847) B2316847
theorem B2059419 : Blo 2057435 2059419 := bstep (se 1 (by rfl) ⟨1544564, by rfl⟩ : syracuseStep 2059419 = 3089129) B3089129
theorem B3174005 : Blo 2057435 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B8464013 : Blo 2057435 8464013 := bstep (se 3 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 8464013 = 3174005) B3174005
theorem B5642675 : Blo 2057435 5642675 := bstep (se 1 (by rfl) ⟨4232006, by rfl⟩ : syracuseStep 5642675 = 8464013) B8464013
theorem B3761783 : Blo 2057435 3761783 := bstep (se 1 (by rfl) ⟨2821337, by rfl⟩ : syracuseStep 3761783 = 5642675) B5642675
theorem B2507855 : Blo 2057435 2507855 := bstep (se 1 (by rfl) ⟨1880891, by rfl⟩ : syracuseStep 2507855 = 3761783) B3761783
theorem B6687613 : Blo 2057435 6687613 := bstep (se 3 (by rfl) ⟨1253927, by rfl⟩ : syracuseStep 6687613 = 2507855) B2507855
theorem B8916817 : Blo 2057435 8916817 := bstep (se 2 (by rfl) ⟨3343806, by rfl⟩ : syracuseStep 8916817 = 6687613) B6687613
theorem B11889089 : Blo 2057435 11889089 := bstep (se 2 (by rfl) ⟨4458408, by rfl⟩ : syracuseStep 11889089 = 8916817) B8916817
theorem B7926059 : Blo 2057435 7926059 := bstep (se 1 (by rfl) ⟨5944544, by rfl⟩ : syracuseStep 7926059 = 11889089) B11889089
theorem B5284039 : Blo 2057435 5284039 := bstep (se 1 (by rfl) ⟨3963029, by rfl⟩ : syracuseStep 5284039 = 7926059) B7926059
theorem B7045385 : Blo 2057435 7045385 := bstep (se 2 (by rfl) ⟨2642019, by rfl⟩ : syracuseStep 7045385 = 5284039) B5284039
theorem B75150773 : Blo 2057435 75150773 := bstep (se 5 (by rfl) ⟨3522692, by rfl⟩ : syracuseStep 75150773 = 7045385) B7045385
theorem B50100515 : Blo 2057435 50100515 := bstep (se 1 (by rfl) ⟨37575386, by rfl⟩ : syracuseStep 50100515 = 75150773) B75150773
theorem B33400343 : Blo 2057435 33400343 := bstep (se 1 (by rfl) ⟨25050257, by rfl⟩ : syracuseStep 33400343 = 50100515) B50100515
theorem B22266895 : Blo 2057435 22266895 := bstep (se 1 (by rfl) ⟨16700171, by rfl⟩ : syracuseStep 22266895 = 33400343) B33400343
theorem B29689193 : Blo 2057435 29689193 := bstep (se 2 (by rfl) ⟨11133447, by rfl⟩ : syracuseStep 29689193 = 22266895) B22266895
theorem B19792795 : Blo 2057435 19792795 := bstep (se 1 (by rfl) ⟨14844596, by rfl⟩ : syracuseStep 19792795 = 29689193) B29689193
theorem B26390393 : Blo 2057435 26390393 := bstep (se 2 (by rfl) ⟨9896397, by rfl⟩ : syracuseStep 26390393 = 19792795) B19792795
theorem B17593595 : Blo 2057435 17593595 := bstep (se 1 (by rfl) ⟨13195196, by rfl⟩ : syracuseStep 17593595 = 26390393) B26390393
theorem B11729063 : Blo 2057435 11729063 := bstep (se 1 (by rfl) ⟨8796797, by rfl⟩ : syracuseStep 11729063 = 17593595) B17593595
theorem B7819375 : Blo 2057435 7819375 := bstep (se 1 (by rfl) ⟨5864531, by rfl⟩ : syracuseStep 7819375 = 11729063) B11729063
theorem B10425833 : Blo 2057435 10425833 := bstep (se 2 (by rfl) ⟨3909687, by rfl⟩ : syracuseStep 10425833 = 7819375) B7819375
theorem B6950555 : Blo 2057435 6950555 := bstep (se 1 (by rfl) ⟨5212916, by rfl⟩ : syracuseStep 6950555 = 10425833) B10425833
theorem B4633703 : Blo 2057435 4633703 := bstep (se 1 (by rfl) ⟨3475277, by rfl⟩ : syracuseStep 4633703 = 6950555) B6950555
theorem B3089135 : Blo 2057435 3089135 := bstep (se 1 (by rfl) ⟨2316851, by rfl⟩ : syracuseStep 3089135 = 4633703) B4633703
theorem B2059423 : Blo 2057435 2059423 := bstep (se 1 (by rfl) ⟨1544567, by rfl⟩ : syracuseStep 2059423 = 3089135) B3089135
theorem B3089141 : Blo 2057435 3089141 := bbase (se 5 (by rfl) ⟨144803, by rfl⟩ : syracuseStep 3089141 = 289607) (by norm_num)
theorem B2059427 : Blo 2057435 2059427 := bstep (se 1 (by rfl) ⟨1544570, by rfl⟩ : syracuseStep 2059427 = 3089141) B3089141
theorem B2821349 : Blo 2057435 2821349 := bbase (se 4 (by rfl) ⟨264501, by rfl⟩ : syracuseStep 2821349 = 529003) (by norm_num)
theorem B7523597 : Blo 2057435 7523597 := bstep (se 3 (by rfl) ⟨1410674, by rfl⟩ : syracuseStep 7523597 = 2821349) B2821349
theorem B5015731 : Blo 2057435 5015731 := bstep (se 1 (by rfl) ⟨3761798, by rfl⟩ : syracuseStep 5015731 = 7523597) B7523597
theorem B6687641 : Blo 2057435 6687641 := bstep (se 2 (by rfl) ⟨2507865, by rfl⟩ : syracuseStep 6687641 = 5015731) B5015731
theorem B17833709 : Blo 2057435 17833709 := bstep (se 3 (by rfl) ⟨3343820, by rfl⟩ : syracuseStep 17833709 = 6687641) B6687641
theorem B47556557 : Blo 2057435 47556557 := bstep (se 3 (by rfl) ⟨8916854, by rfl⟩ : syracuseStep 47556557 = 17833709) B17833709
theorem B31704371 : Blo 2057435 31704371 := bstep (se 1 (by rfl) ⟨23778278, by rfl⟩ : syracuseStep 31704371 = 47556557) B47556557
theorem B21136247 : Blo 2057435 21136247 := bstep (se 1 (by rfl) ⟨15852185, by rfl⟩ : syracuseStep 21136247 = 31704371) B31704371
theorem B14090831 : Blo 2057435 14090831 := bstep (se 1 (by rfl) ⟨10568123, by rfl⟩ : syracuseStep 14090831 = 21136247) B21136247
theorem B9393887 : Blo 2057435 9393887 := bstep (se 1 (by rfl) ⟨7045415, by rfl⟩ : syracuseStep 9393887 = 14090831) B14090831
theorem B6262591 : Blo 2057435 6262591 := bstep (se 1 (by rfl) ⟨4696943, by rfl⟩ : syracuseStep 6262591 = 9393887) B9393887
theorem B8350121 : Blo 2057435 8350121 := bstep (se 2 (by rfl) ⟨3131295, by rfl⟩ : syracuseStep 8350121 = 6262591) B6262591
theorem B5566747 : Blo 2057435 5566747 := bstep (se 1 (by rfl) ⟨4175060, by rfl⟩ : syracuseStep 5566747 = 8350121) B8350121
theorem B7422329 : Blo 2057435 7422329 := bstep (se 2 (by rfl) ⟨2783373, by rfl⟩ : syracuseStep 7422329 = 5566747) B5566747
theorem B4948219 : Blo 2057435 4948219 := bstep (se 1 (by rfl) ⟨3711164, by rfl⟩ : syracuseStep 4948219 = 7422329) B7422329
theorem B6597625 : Blo 2057435 6597625 := bstep (se 2 (by rfl) ⟨2474109, by rfl⟩ : syracuseStep 6597625 = 4948219) B4948219
theorem B8796833 : Blo 2057435 8796833 := bstep (se 2 (by rfl) ⟨3298812, by rfl⟩ : syracuseStep 8796833 = 6597625) B6597625
theorem B5864555 : Blo 2057435 5864555 := bstep (se 1 (by rfl) ⟨4398416, by rfl⟩ : syracuseStep 5864555 = 8796833) B8796833
theorem B3909703 : Blo 2057435 3909703 := bstep (se 1 (by rfl) ⟨2932277, by rfl⟩ : syracuseStep 3909703 = 5864555) B5864555
theorem B5212937 : Blo 2057435 5212937 := bstep (se 2 (by rfl) ⟨1954851, by rfl⟩ : syracuseStep 5212937 = 3909703) B3909703
theorem B3475291 : Blo 2057435 3475291 := bstep (se 1 (by rfl) ⟨2606468, by rfl⟩ : syracuseStep 3475291 = 5212937) B5212937
theorem B4633721 : Blo 2057435 4633721 := bstep (se 2 (by rfl) ⟨1737645, by rfl⟩ : syracuseStep 4633721 = 3475291) B3475291
theorem B3089147 : Blo 2057435 3089147 := bstep (se 1 (by rfl) ⟨2316860, by rfl⟩ : syracuseStep 3089147 = 4633721) B4633721
theorem B2059431 : Blo 2057435 2059431 := bstep (se 1 (by rfl) ⟨1544573, by rfl⟩ : syracuseStep 2059431 = 3089147) B3089147
theorem B2316865 : Blo 2057435 2316865 := bbase (se 2 (by rfl) ⟨868824, by rfl⟩ : syracuseStep 2316865 = 1737649) (by norm_num)
theorem B3089153 : Blo 2057435 3089153 := bstep (se 2 (by rfl) ⟨1158432, by rfl⟩ : syracuseStep 3089153 = 2316865) B2316865
theorem B2059435 : Blo 2057435 2059435 := bstep (se 1 (by rfl) ⟨1544576, by rfl⟩ : syracuseStep 2059435 = 3089153) B3089153
theorem C0 (j : ℕ) (h1 : 514358 ≤ j) (h2 : j ≤ 514858) : Blo 2057435 (4 * j + 3) := by
  interval_cases j
  · exact B2057435
  · exact B2057439
  · exact B2057443
  · exact B2057447
  · exact B2057451
  · exact B2057455
  · exact B2057459
  · exact B2057463
  · exact B2057467
  · exact B2057471
  · exact B2057475
  · exact B2057479
  · exact B2057483
  · exact B2057487
  · exact B2057491
  · exact B2057495
  · exact B2057499
  · exact B2057503
  · exact B2057507
  · exact B2057511
  · exact B2057515
  · exact B2057519
  · exact B2057523
  · exact B2057527
  · exact B2057531
  · exact B2057535
  · exact B2057539
  · exact B2057543
  · exact B2057547
  · exact B2057551
  · exact B2057555
  · exact B2057559
  · exact B2057563
  · exact B2057567
  · exact B2057571
  · exact B2057575
  · exact B2057579
  · exact B2057583
  · exact B2057587
  · exact B2057591
  · exact B2057595
  · exact B2057599
  · exact B2057603
  · exact B2057607
  · exact B2057611
  · exact B2057615
  · exact B2057619
  · exact B2057623
  · exact B2057627
  · exact B2057631
  · exact B2057635
  · exact B2057639
  · exact B2057643
  · exact B2057647
  · exact B2057651
  · exact B2057655
  · exact B2057659
  · exact B2057663
  · exact B2057667
  · exact B2057671
  · exact B2057675
  · exact B2057679
  · exact B2057683
  · exact B2057687
  · exact B2057691
  · exact B2057695
  · exact B2057699
  · exact B2057703
  · exact B2057707
  · exact B2057711
  · exact B2057715
  · exact B2057719
  · exact B2057723
  · exact B2057727
  · exact B2057731
  · exact B2057735
  · exact B2057739
  · exact B2057743
  · exact B2057747
  · exact B2057751
  · exact B2057755
  · exact B2057759
  · exact B2057763
  · exact B2057767
  · exact B2057771
  · exact B2057775
  · exact B2057779
  · exact B2057783
  · exact B2057787
  · exact B2057791
  · exact B2057795
  · exact B2057799
  · exact B2057803
  · exact B2057807
  · exact B2057811
  · exact B2057815
  · exact B2057819
  · exact B2057823
  · exact B2057827
  · exact B2057831
  · exact B2057835
  · exact B2057839
  · exact B2057843
  · exact B2057847
  · exact B2057851
  · exact B2057855
  · exact B2057859
  · exact B2057863
  · exact B2057867
  · exact B2057871
  · exact B2057875
  · exact B2057879
  · exact B2057883
  · exact B2057887
  · exact B2057891
  · exact B2057895
  · exact B2057899
  · exact B2057903
  · exact B2057907
  · exact B2057911
  · exact B2057915
  · exact B2057919
  · exact B2057923
  · exact B2057927
  · exact B2057931
  · exact B2057935
  · exact B2057939
  · exact B2057943
  · exact B2057947
  · exact B2057951
  · exact B2057955
  · exact B2057959
  · exact B2057963
  · exact B2057967
  · exact B2057971
  · exact B2057975
  · exact B2057979
  · exact B2057983
  · exact B2057987
  · exact B2057991
  · exact B2057995
  · exact B2057999
  · exact B2058003
  · exact B2058007
  · exact B2058011
  · exact B2058015
  · exact B2058019
  · exact B2058023
  · exact B2058027
  · exact B2058031
  · exact B2058035
  · exact B2058039
  · exact B2058043
  · exact B2058047
  · exact B2058051
  · exact B2058055
  · exact B2058059
  · exact B2058063
  · exact B2058067
  · exact B2058071
  · exact B2058075
  · exact B2058079
  · exact B2058083
  · exact B2058087
  · exact B2058091
  · exact B2058095
  · exact B2058099
  · exact B2058103
  · exact B2058107
  · exact B2058111
  · exact B2058115
  · exact B2058119
  · exact B2058123
  · exact B2058127
  · exact B2058131
  · exact B2058135
  · exact B2058139
  · exact B2058143
  · exact B2058147
  · exact B2058151
  · exact B2058155
  · exact B2058159
  · exact B2058163
  · exact B2058167
  · exact B2058171
  · exact B2058175
  · exact B2058179
  · exact B2058183
  · exact B2058187
  · exact B2058191
  · exact B2058195
  · exact B2058199
  · exact B2058203
  · exact B2058207
  · exact B2058211
  · exact B2058215
  · exact B2058219
  · exact B2058223
  · exact B2058227
  · exact B2058231
  · exact B2058235
  · exact B2058239
  · exact B2058243
  · exact B2058247
  · exact B2058251
  · exact B2058255
  · exact B2058259
  · exact B2058263
  · exact B2058267
  · exact B2058271
  · exact B2058275
  · exact B2058279
  · exact B2058283
  · exact B2058287
  · exact B2058291
  · exact B2058295
  · exact B2058299
  · exact B2058303
  · exact B2058307
  · exact B2058311
  · exact B2058315
  · exact B2058319
  · exact B2058323
  · exact B2058327
  · exact B2058331
  · exact B2058335
  · exact B2058339
  · exact B2058343
  · exact B2058347
  · exact B2058351
  · exact B2058355
  · exact B2058359
  · exact B2058363
  · exact B2058367
  · exact B2058371
  · exact B2058375
  · exact B2058379
  · exact B2058383
  · exact B2058387
  · exact B2058391
  · exact B2058395
  · exact B2058399
  · exact B2058403
  · exact B2058407
  · exact B2058411
  · exact B2058415
  · exact B2058419
  · exact B2058423
  · exact B2058427
  · exact B2058431
  · exact B2058435
  · exact B2058439
  · exact B2058443
  · exact B2058447
  · exact B2058451
  · exact B2058455
  · exact B2058459
  · exact B2058463
  · exact B2058467
  · exact B2058471
  · exact B2058475
  · exact B2058479
  · exact B2058483
  · exact B2058487
  · exact B2058491
  · exact B2058495
  · exact B2058499
  · exact B2058503
  · exact B2058507
  · exact B2058511
  · exact B2058515
  · exact B2058519
  · exact B2058523
  · exact B2058527
  · exact B2058531
  · exact B2058535
  · exact B2058539
  · exact B2058543
  · exact B2058547
  · exact B2058551
  · exact B2058555
  · exact B2058559
  · exact B2058563
  · exact B2058567
  · exact B2058571
  · exact B2058575
  · exact B2058579
  · exact B2058583
  · exact B2058587
  · exact B2058591
  · exact B2058595
  · exact B2058599
  · exact B2058603
  · exact B2058607
  · exact B2058611
  · exact B2058615
  · exact B2058619
  · exact B2058623
  · exact B2058627
  · exact B2058631
  · exact B2058635
  · exact B2058639
  · exact B2058643
  · exact B2058647
  · exact B2058651
  · exact B2058655
  · exact B2058659
  · exact B2058663
  · exact B2058667
  · exact B2058671
  · exact B2058675
  · exact B2058679
  · exact B2058683
  · exact B2058687
  · exact B2058691
  · exact B2058695
  · exact B2058699
  · exact B2058703
  · exact B2058707
  · exact B2058711
  · exact B2058715
  · exact B2058719
  · exact B2058723
  · exact B2058727
  · exact B2058731
  · exact B2058735
  · exact B2058739
  · exact B2058743
  · exact B2058747
  · exact B2058751
  · exact B2058755
  · exact B2058759
  · exact B2058763
  · exact B2058767
  · exact B2058771
  · exact B2058775
  · exact B2058779
  · exact B2058783
  · exact B2058787
  · exact B2058791
  · exact B2058795
  · exact B2058799
  · exact B2058803
  · exact B2058807
  · exact B2058811
  · exact B2058815
  · exact B2058819
  · exact B2058823
  · exact B2058827
  · exact B2058831
  · exact B2058835
  · exact B2058839
  · exact B2058843
  · exact B2058847
  · exact B2058851
  · exact B2058855
  · exact B2058859
  · exact B2058863
  · exact B2058867
  · exact B2058871
  · exact B2058875
  · exact B2058879
  · exact B2058883
  · exact B2058887
  · exact B2058891
  · exact B2058895
  · exact B2058899
  · exact B2058903
  · exact B2058907
  · exact B2058911
  · exact B2058915
  · exact B2058919
  · exact B2058923
  · exact B2058927
  · exact B2058931
  · exact B2058935
  · exact B2058939
  · exact B2058943
  · exact B2058947
  · exact B2058951
  · exact B2058955
  · exact B2058959
  · exact B2058963
  · exact B2058967
  · exact B2058971
  · exact B2058975
  · exact B2058979
  · exact B2058983
  · exact B2058987
  · exact B2058991
  · exact B2058995
  · exact B2058999
  · exact B2059003
  · exact B2059007
  · exact B2059011
  · exact B2059015
  · exact B2059019
  · exact B2059023
  · exact B2059027
  · exact B2059031
  · exact B2059035
  · exact B2059039
  · exact B2059043
  · exact B2059047
  · exact B2059051
  · exact B2059055
  · exact B2059059
  · exact B2059063
  · exact B2059067
  · exact B2059071
  · exact B2059075
  · exact B2059079
  · exact B2059083
  · exact B2059087
  · exact B2059091
  · exact B2059095
  · exact B2059099
  · exact B2059103
  · exact B2059107
  · exact B2059111
  · exact B2059115
  · exact B2059119
  · exact B2059123
  · exact B2059127
  · exact B2059131
  · exact B2059135
  · exact B2059139
  · exact B2059143
  · exact B2059147
  · exact B2059151
  · exact B2059155
  · exact B2059159
  · exact B2059163
  · exact B2059167
  · exact B2059171
  · exact B2059175
  · exact B2059179
  · exact B2059183
  · exact B2059187
  · exact B2059191
  · exact B2059195
  · exact B2059199
  · exact B2059203
  · exact B2059207
  · exact B2059211
  · exact B2059215
  · exact B2059219
  · exact B2059223
  · exact B2059227
  · exact B2059231
  · exact B2059235
  · exact B2059239
  · exact B2059243
  · exact B2059247
  · exact B2059251
  · exact B2059255
  · exact B2059259
  · exact B2059263
  · exact B2059267
  · exact B2059271
  · exact B2059275
  · exact B2059279
  · exact B2059283
  · exact B2059287
  · exact B2059291
  · exact B2059295
  · exact B2059299
  · exact B2059303
  · exact B2059307
  · exact B2059311
  · exact B2059315
  · exact B2059319
  · exact B2059323
  · exact B2059327
  · exact B2059331
  · exact B2059335
  · exact B2059339
  · exact B2059343
  · exact B2059347
  · exact B2059351
  · exact B2059355
  · exact B2059359
  · exact B2059363
  · exact B2059367
  · exact B2059371
  · exact B2059375
  · exact B2059379
  · exact B2059383
  · exact B2059387
  · exact B2059391
  · exact B2059395
  · exact B2059399
  · exact B2059403
  · exact B2059407
  · exact B2059411
  · exact B2059415
  · exact B2059419
  · exact B2059423
  · exact B2059427
  · exact B2059431
  · exact B2059435
theorem solution (m : ℕ) (hlo : 2057435 ≤ m) (hhi : m ≤ 2059435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 514358 ≤ j := by omega
    have hj2 : j ≤ 514858 := by omega
    have hb : Blo 2057435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
