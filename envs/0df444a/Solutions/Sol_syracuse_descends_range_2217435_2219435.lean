-- Prove2me | solution 1 for syracuse_descends_range_2217435_2219435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:36.165182+00:00
-- url     : https://prove2.me/submissions/947069fd-5b44-4af5-b38c-02507a917471

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

theorem B5612885 : Blo 2217435 5612885 := bbase (se 12 (by rfl) ⟨2055, by rfl⟩ : syracuseStep 5612885 = 4111) (by norm_num)
theorem B3741923 : Blo 2217435 3741923 := bstep (se 1 (by rfl) ⟨2806442, by rfl⟩ : syracuseStep 3741923 = 5612885) B5612885
theorem B2494615 : Blo 2217435 2494615 := bstep (se 1 (by rfl) ⟨1870961, by rfl⟩ : syracuseStep 2494615 = 3741923) B3741923
theorem B3326153 : Blo 2217435 3326153 := bstep (se 2 (by rfl) ⟨1247307, by rfl⟩ : syracuseStep 3326153 = 2494615) B2494615
theorem B2217435 : Blo 2217435 2217435 := bstep (se 1 (by rfl) ⟨1663076, by rfl⟩ : syracuseStep 2217435 = 3326153) B3326153
theorem B2663933 : Blo 2217435 2663933 := bbase (se 3 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 2663933 = 998975) (by norm_num)
theorem B7103821 : Blo 2217435 7103821 := bstep (se 3 (by rfl) ⟨1331966, by rfl⟩ : syracuseStep 7103821 = 2663933) B2663933
theorem B9471761 : Blo 2217435 9471761 := bstep (se 2 (by rfl) ⟨3551910, by rfl⟩ : syracuseStep 9471761 = 7103821) B7103821
theorem B6314507 : Blo 2217435 6314507 := bstep (se 1 (by rfl) ⟨4735880, by rfl⟩ : syracuseStep 6314507 = 9471761) B9471761
theorem B4209671 : Blo 2217435 4209671 := bstep (se 1 (by rfl) ⟨3157253, by rfl⟩ : syracuseStep 4209671 = 6314507) B6314507
theorem B11225789 : Blo 2217435 11225789 := bstep (se 3 (by rfl) ⟨2104835, by rfl⟩ : syracuseStep 11225789 = 4209671) B4209671
theorem B7483859 : Blo 2217435 7483859 := bstep (se 1 (by rfl) ⟨5612894, by rfl⟩ : syracuseStep 7483859 = 11225789) B11225789
theorem B4989239 : Blo 2217435 4989239 := bstep (se 1 (by rfl) ⟨3741929, by rfl⟩ : syracuseStep 4989239 = 7483859) B7483859
theorem B3326159 : Blo 2217435 3326159 := bstep (se 1 (by rfl) ⟨2494619, by rfl⟩ : syracuseStep 3326159 = 4989239) B4989239
theorem B2217439 : Blo 2217435 2217439 := bstep (se 1 (by rfl) ⟨1663079, by rfl⟩ : syracuseStep 2217439 = 3326159) B3326159
theorem B3326165 : Blo 2217435 3326165 := bbase (se 7 (by rfl) ⟨38978, by rfl⟩ : syracuseStep 3326165 = 77957) (by norm_num)
theorem B2217443 : Blo 2217435 2217443 := bstep (se 1 (by rfl) ⟨1663082, by rfl⟩ : syracuseStep 2217443 = 3326165) B3326165
theorem B2367949 : Blo 2217435 2367949 := bbase (se 3 (by rfl) ⟨443990, by rfl⟩ : syracuseStep 2367949 = 887981) (by norm_num)
theorem B3157265 : Blo 2217435 3157265 := bstep (se 2 (by rfl) ⟨1183974, by rfl⟩ : syracuseStep 3157265 = 2367949) B2367949
theorem B8419373 : Blo 2217435 8419373 := bstep (se 3 (by rfl) ⟨1578632, by rfl⟩ : syracuseStep 8419373 = 3157265) B3157265
theorem B5612915 : Blo 2217435 5612915 := bstep (se 1 (by rfl) ⟨4209686, by rfl⟩ : syracuseStep 5612915 = 8419373) B8419373
theorem B3741943 : Blo 2217435 3741943 := bstep (se 1 (by rfl) ⟨2806457, by rfl⟩ : syracuseStep 3741943 = 5612915) B5612915
theorem B4989257 : Blo 2217435 4989257 := bstep (se 2 (by rfl) ⟨1870971, by rfl⟩ : syracuseStep 4989257 = 3741943) B3741943
theorem B3326171 : Blo 2217435 3326171 := bstep (se 1 (by rfl) ⟨2494628, by rfl⟩ : syracuseStep 3326171 = 4989257) B4989257
theorem B2217447 : Blo 2217435 2217447 := bstep (se 1 (by rfl) ⟨1663085, by rfl⟩ : syracuseStep 2217447 = 3326171) B3326171
theorem B2494633 : Blo 2217435 2494633 := bbase (se 2 (by rfl) ⟨935487, by rfl⟩ : syracuseStep 2494633 = 1870975) (by norm_num)
theorem B3326177 : Blo 2217435 3326177 := bstep (se 2 (by rfl) ⟨1247316, by rfl⟩ : syracuseStep 3326177 = 2494633) B2494633
theorem B2217451 : Blo 2217435 2217451 := bstep (se 1 (by rfl) ⟨1663088, by rfl⟩ : syracuseStep 2217451 = 3326177) B3326177
theorem B9471829 : Blo 2217435 9471829 := bbase (se 9 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 9471829 = 55499) (by norm_num)
theorem B12629105 : Blo 2217435 12629105 := bstep (se 2 (by rfl) ⟨4735914, by rfl⟩ : syracuseStep 12629105 = 9471829) B9471829
theorem B8419403 : Blo 2217435 8419403 := bstep (se 1 (by rfl) ⟨6314552, by rfl⟩ : syracuseStep 8419403 = 12629105) B12629105
theorem B5612935 : Blo 2217435 5612935 := bstep (se 1 (by rfl) ⟨4209701, by rfl⟩ : syracuseStep 5612935 = 8419403) B8419403
theorem B7483913 : Blo 2217435 7483913 := bstep (se 2 (by rfl) ⟨2806467, by rfl⟩ : syracuseStep 7483913 = 5612935) B5612935
theorem B4989275 : Blo 2217435 4989275 := bstep (se 1 (by rfl) ⟨3741956, by rfl⟩ : syracuseStep 4989275 = 7483913) B7483913
theorem B3326183 : Blo 2217435 3326183 := bstep (se 1 (by rfl) ⟨2494637, by rfl⟩ : syracuseStep 3326183 = 4989275) B4989275
theorem B2217455 : Blo 2217435 2217455 := bstep (se 1 (by rfl) ⟨1663091, by rfl⟩ : syracuseStep 2217455 = 3326183) B3326183
theorem B3326189 : Blo 2217435 3326189 := bbase (se 3 (by rfl) ⟨623660, by rfl⟩ : syracuseStep 3326189 = 1247321) (by norm_num)
theorem B2217459 : Blo 2217435 2217459 := bstep (se 1 (by rfl) ⟨1663094, by rfl⟩ : syracuseStep 2217459 = 3326189) B3326189
theorem B4989293 : Blo 2217435 4989293 := bbase (se 3 (by rfl) ⟨935492, by rfl⟩ : syracuseStep 4989293 = 1870985) (by norm_num)
theorem B3326195 : Blo 2217435 3326195 := bstep (se 1 (by rfl) ⟨2494646, by rfl⟩ : syracuseStep 3326195 = 4989293) B4989293
theorem B2217463 : Blo 2217435 2217463 := bstep (se 1 (by rfl) ⟨1663097, by rfl⟩ : syracuseStep 2217463 = 3326195) B3326195
theorem B4209725 : Blo 2217435 4209725 := bbase (se 3 (by rfl) ⟨789323, by rfl⟩ : syracuseStep 4209725 = 1578647) (by norm_num)
theorem B2806483 : Blo 2217435 2806483 := bstep (se 1 (by rfl) ⟨2104862, by rfl⟩ : syracuseStep 2806483 = 4209725) B4209725
theorem B3741977 : Blo 2217435 3741977 := bstep (se 2 (by rfl) ⟨1403241, by rfl⟩ : syracuseStep 3741977 = 2806483) B2806483
theorem B2494651 : Blo 2217435 2494651 := bstep (se 1 (by rfl) ⟨1870988, by rfl⟩ : syracuseStep 2494651 = 3741977) B3741977
theorem B3326201 : Blo 2217435 3326201 := bstep (se 2 (by rfl) ⟨1247325, by rfl⟩ : syracuseStep 3326201 = 2494651) B2494651
theorem B2217467 : Blo 2217435 2217467 := bstep (se 1 (by rfl) ⟨1663100, by rfl⟩ : syracuseStep 2217467 = 3326201) B3326201
theorem B3995957 : Blo 2217435 3995957 := bbase (se 5 (by rfl) ⟨187310, by rfl⟩ : syracuseStep 3995957 = 374621) (by norm_num)
theorem B2663971 : Blo 2217435 2663971 := bstep (se 1 (by rfl) ⟨1997978, by rfl⟩ : syracuseStep 2663971 = 3995957) B3995957
theorem B56831381 : Blo 2217435 56831381 := bstep (se 6 (by rfl) ⟨1331985, by rfl⟩ : syracuseStep 56831381 = 2663971) B2663971
theorem B37887587 : Blo 2217435 37887587 := bstep (se 1 (by rfl) ⟨28415690, by rfl⟩ : syracuseStep 37887587 = 56831381) B56831381
theorem B25258391 : Blo 2217435 25258391 := bstep (se 1 (by rfl) ⟨18943793, by rfl⟩ : syracuseStep 25258391 = 37887587) B37887587
theorem B16838927 : Blo 2217435 16838927 := bstep (se 1 (by rfl) ⟨12629195, by rfl⟩ : syracuseStep 16838927 = 25258391) B25258391
theorem B11225951 : Blo 2217435 11225951 := bstep (se 1 (by rfl) ⟨8419463, by rfl⟩ : syracuseStep 11225951 = 16838927) B16838927
theorem B7483967 : Blo 2217435 7483967 := bstep (se 1 (by rfl) ⟨5612975, by rfl⟩ : syracuseStep 7483967 = 11225951) B11225951
theorem B4989311 : Blo 2217435 4989311 := bstep (se 1 (by rfl) ⟨3741983, by rfl⟩ : syracuseStep 4989311 = 7483967) B7483967
theorem B3326207 : Blo 2217435 3326207 := bstep (se 1 (by rfl) ⟨2494655, by rfl⟩ : syracuseStep 3326207 = 4989311) B4989311
theorem B2217471 : Blo 2217435 2217471 := bstep (se 1 (by rfl) ⟨1663103, by rfl⟩ : syracuseStep 2217471 = 3326207) B3326207
theorem B3326213 : Blo 2217435 3326213 := bbase (se 4 (by rfl) ⟨311832, by rfl⟩ : syracuseStep 3326213 = 623665) (by norm_num)
theorem B2217475 : Blo 2217435 2217475 := bstep (se 1 (by rfl) ⟨1663106, by rfl⟩ : syracuseStep 2217475 = 3326213) B3326213
theorem B3741997 : Blo 2217435 3741997 := bbase (se 3 (by rfl) ⟨701624, by rfl⟩ : syracuseStep 3741997 = 1403249) (by norm_num)
theorem B4989329 : Blo 2217435 4989329 := bstep (se 2 (by rfl) ⟨1870998, by rfl⟩ : syracuseStep 4989329 = 3741997) B3741997
theorem B3326219 : Blo 2217435 3326219 := bstep (se 1 (by rfl) ⟨2494664, by rfl⟩ : syracuseStep 3326219 = 4989329) B4989329
theorem B2217479 : Blo 2217435 2217479 := bstep (se 1 (by rfl) ⟨1663109, by rfl⟩ : syracuseStep 2217479 = 3326219) B3326219
theorem B2494669 : Blo 2217435 2494669 := bbase (se 3 (by rfl) ⟨467750, by rfl⟩ : syracuseStep 2494669 = 935501) (by norm_num)
theorem B3326225 : Blo 2217435 3326225 := bstep (se 2 (by rfl) ⟨1247334, by rfl⟩ : syracuseStep 3326225 = 2494669) B2494669
theorem B2217483 : Blo 2217435 2217483 := bstep (se 1 (by rfl) ⟨1663112, by rfl⟩ : syracuseStep 2217483 = 3326225) B3326225
theorem B7484021 : Blo 2217435 7484021 := bbase (se 5 (by rfl) ⟨350813, by rfl⟩ : syracuseStep 7484021 = 701627) (by norm_num)
theorem B4989347 : Blo 2217435 4989347 := bstep (se 1 (by rfl) ⟨3742010, by rfl⟩ : syracuseStep 4989347 = 7484021) B7484021
theorem B3326231 : Blo 2217435 3326231 := bstep (se 1 (by rfl) ⟨2494673, by rfl⟩ : syracuseStep 3326231 = 4989347) B4989347
theorem B2217487 : Blo 2217435 2217487 := bstep (se 1 (by rfl) ⟨1663115, by rfl⟩ : syracuseStep 2217487 = 3326231) B3326231
theorem B3326237 : Blo 2217435 3326237 := bbase (se 3 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 3326237 = 1247339) (by norm_num)
theorem B2217491 : Blo 2217435 2217491 := bstep (se 1 (by rfl) ⟨1663118, by rfl⟩ : syracuseStep 2217491 = 3326237) B3326237
theorem B4989365 : Blo 2217435 4989365 := bbase (se 5 (by rfl) ⟨233876, by rfl⟩ : syracuseStep 4989365 = 467753) (by norm_num)
theorem B3326243 : Blo 2217435 3326243 := bstep (se 1 (by rfl) ⟨2494682, by rfl⟩ : syracuseStep 3326243 = 4989365) B4989365
theorem B2217495 : Blo 2217435 2217495 := bstep (se 1 (by rfl) ⟨1663121, by rfl⟩ : syracuseStep 2217495 = 3326243) B3326243
theorem B2528725 : Blo 2217435 2528725 := bbase (se 7 (by rfl) ⟨29633, by rfl⟩ : syracuseStep 2528725 = 59267) (by norm_num)
theorem B3371633 : Blo 2217435 3371633 := bstep (se 2 (by rfl) ⟨1264362, by rfl⟩ : syracuseStep 3371633 = 2528725) B2528725
theorem B2247755 : Blo 2217435 2247755 := bstep (se 1 (by rfl) ⟨1685816, by rfl⟩ : syracuseStep 2247755 = 3371633) B3371633
theorem B5994013 : Blo 2217435 5994013 := bstep (se 3 (by rfl) ⟨1123877, by rfl⟩ : syracuseStep 5994013 = 2247755) B2247755
theorem B7992017 : Blo 2217435 7992017 := bstep (se 2 (by rfl) ⟨2997006, by rfl⟩ : syracuseStep 7992017 = 5994013) B5994013
theorem B5328011 : Blo 2217435 5328011 := bstep (se 1 (by rfl) ⟨3996008, by rfl⟩ : syracuseStep 5328011 = 7992017) B7992017
theorem B3552007 : Blo 2217435 3552007 := bstep (se 1 (by rfl) ⟨2664005, by rfl⟩ : syracuseStep 3552007 = 5328011) B5328011
theorem B4736009 : Blo 2217435 4736009 := bstep (se 2 (by rfl) ⟨1776003, by rfl⟩ : syracuseStep 4736009 = 3552007) B3552007
theorem B12629357 : Blo 2217435 12629357 := bstep (se 3 (by rfl) ⟨2368004, by rfl⟩ : syracuseStep 12629357 = 4736009) B4736009
theorem B8419571 : Blo 2217435 8419571 := bstep (se 1 (by rfl) ⟨6314678, by rfl⟩ : syracuseStep 8419571 = 12629357) B12629357
theorem B5613047 : Blo 2217435 5613047 := bstep (se 1 (by rfl) ⟨4209785, by rfl⟩ : syracuseStep 5613047 = 8419571) B8419571
theorem B3742031 : Blo 2217435 3742031 := bstep (se 1 (by rfl) ⟨2806523, by rfl⟩ : syracuseStep 3742031 = 5613047) B5613047
theorem B2494687 : Blo 2217435 2494687 := bstep (se 1 (by rfl) ⟨1871015, by rfl⟩ : syracuseStep 2494687 = 3742031) B3742031
theorem B3326249 : Blo 2217435 3326249 := bstep (se 2 (by rfl) ⟨1247343, by rfl⟩ : syracuseStep 3326249 = 2494687) B2494687
theorem B2217499 : Blo 2217435 2217499 := bstep (se 1 (by rfl) ⟨1663124, by rfl⟩ : syracuseStep 2217499 = 3326249) B3326249
theorem B3552013 : Blo 2217435 3552013 := bbase (se 3 (by rfl) ⟨666002, by rfl⟩ : syracuseStep 3552013 = 1332005) (by norm_num)
theorem B4736017 : Blo 2217435 4736017 := bstep (se 2 (by rfl) ⟨1776006, by rfl⟩ : syracuseStep 4736017 = 3552013) B3552013
theorem B6314689 : Blo 2217435 6314689 := bstep (se 2 (by rfl) ⟨2368008, by rfl⟩ : syracuseStep 6314689 = 4736017) B4736017
theorem B8419585 : Blo 2217435 8419585 := bstep (se 2 (by rfl) ⟨3157344, by rfl⟩ : syracuseStep 8419585 = 6314689) B6314689
theorem B11226113 : Blo 2217435 11226113 := bstep (se 2 (by rfl) ⟨4209792, by rfl⟩ : syracuseStep 11226113 = 8419585) B8419585
theorem B7484075 : Blo 2217435 7484075 := bstep (se 1 (by rfl) ⟨5613056, by rfl⟩ : syracuseStep 7484075 = 11226113) B11226113
theorem B4989383 : Blo 2217435 4989383 := bstep (se 1 (by rfl) ⟨3742037, by rfl⟩ : syracuseStep 4989383 = 7484075) B7484075
theorem B3326255 : Blo 2217435 3326255 := bstep (se 1 (by rfl) ⟨2494691, by rfl⟩ : syracuseStep 3326255 = 4989383) B4989383
theorem B2217503 : Blo 2217435 2217503 := bstep (se 1 (by rfl) ⟨1663127, by rfl⟩ : syracuseStep 2217503 = 3326255) B3326255
theorem B3326261 : Blo 2217435 3326261 := bbase (se 5 (by rfl) ⟨155918, by rfl⟩ : syracuseStep 3326261 = 311837) (by norm_num)
theorem B2217507 : Blo 2217435 2217507 := bstep (se 1 (by rfl) ⟨1663130, by rfl⟩ : syracuseStep 2217507 = 3326261) B3326261
theorem B5613077 : Blo 2217435 5613077 := bbase (se 6 (by rfl) ⟨131556, by rfl⟩ : syracuseStep 5613077 = 263113) (by norm_num)
theorem B3742051 : Blo 2217435 3742051 := bstep (se 1 (by rfl) ⟨2806538, by rfl⟩ : syracuseStep 3742051 = 5613077) B5613077
theorem B4989401 : Blo 2217435 4989401 := bstep (se 2 (by rfl) ⟨1871025, by rfl⟩ : syracuseStep 4989401 = 3742051) B3742051
theorem B3326267 : Blo 2217435 3326267 := bstep (se 1 (by rfl) ⟨2494700, by rfl⟩ : syracuseStep 3326267 = 4989401) B4989401
theorem B2217511 : Blo 2217435 2217511 := bstep (se 1 (by rfl) ⟨1663133, by rfl⟩ : syracuseStep 2217511 = 3326267) B3326267
theorem B2494705 : Blo 2217435 2494705 := bbase (se 2 (by rfl) ⟨935514, by rfl⟩ : syracuseStep 2494705 = 1871029) (by norm_num)
theorem B3326273 : Blo 2217435 3326273 := bstep (se 2 (by rfl) ⟨1247352, by rfl⟩ : syracuseStep 3326273 = 2494705) B2494705
theorem B2217515 : Blo 2217435 2217515 := bstep (se 1 (by rfl) ⟨1663136, by rfl⟩ : syracuseStep 2217515 = 3326273) B3326273
theorem B8211653 : Blo 2217435 8211653 := bbase (se 4 (by rfl) ⟨769842, by rfl⟩ : syracuseStep 8211653 = 1539685) (by norm_num)
theorem B5474435 : Blo 2217435 5474435 := bstep (se 1 (by rfl) ⟨4105826, by rfl⟩ : syracuseStep 5474435 = 8211653) B8211653
theorem B58393973 : Blo 2217435 58393973 := bstep (se 5 (by rfl) ⟨2737217, by rfl⟩ : syracuseStep 58393973 = 5474435) B5474435
theorem B155717261 : Blo 2217435 155717261 := bstep (se 3 (by rfl) ⟨29196986, by rfl⟩ : syracuseStep 155717261 = 58393973) B58393973
theorem B103811507 : Blo 2217435 103811507 := bstep (se 1 (by rfl) ⟨77858630, by rfl⟩ : syracuseStep 103811507 = 155717261) B155717261
theorem B69207671 : Blo 2217435 69207671 := bstep (se 1 (by rfl) ⟨51905753, by rfl⟩ : syracuseStep 69207671 = 103811507) B103811507
theorem B46138447 : Blo 2217435 46138447 := bstep (se 1 (by rfl) ⟨34603835, by rfl⟩ : syracuseStep 46138447 = 69207671) B69207671
theorem B61517929 : Blo 2217435 61517929 := bstep (se 2 (by rfl) ⟨23069223, by rfl⟩ : syracuseStep 61517929 = 46138447) B46138447
theorem B82023905 : Blo 2217435 82023905 := bstep (se 2 (by rfl) ⟨30758964, by rfl⟩ : syracuseStep 82023905 = 61517929) B61517929
theorem B218730413 : Blo 2217435 218730413 := bstep (se 3 (by rfl) ⟨41011952, by rfl⟩ : syracuseStep 218730413 = 82023905) B82023905
theorem B583281101 : Blo 2217435 583281101 := bstep (se 3 (by rfl) ⟨109365206, by rfl⟩ : syracuseStep 583281101 = 218730413) B218730413
theorem B388854067 : Blo 2217435 388854067 := bstep (se 1 (by rfl) ⟨291640550, by rfl⟩ : syracuseStep 388854067 = 583281101) B583281101
theorem B518472089 : Blo 2217435 518472089 := bstep (se 2 (by rfl) ⟨194427033, by rfl⟩ : syracuseStep 518472089 = 388854067) B388854067
theorem B345648059 : Blo 2217435 345648059 := bstep (se 1 (by rfl) ⟨259236044, by rfl⟩ : syracuseStep 345648059 = 518472089) B518472089
theorem B230432039 : Blo 2217435 230432039 := bstep (se 1 (by rfl) ⟨172824029, by rfl⟩ : syracuseStep 230432039 = 345648059) B345648059
theorem B153621359 : Blo 2217435 153621359 := bstep (se 1 (by rfl) ⟨115216019, by rfl⟩ : syracuseStep 153621359 = 230432039) B230432039
theorem B102414239 : Blo 2217435 102414239 := bstep (se 1 (by rfl) ⟨76810679, by rfl⟩ : syracuseStep 102414239 = 153621359) B153621359
theorem B68276159 : Blo 2217435 68276159 := bstep (se 1 (by rfl) ⟨51207119, by rfl⟩ : syracuseStep 68276159 = 102414239) B102414239
theorem B45517439 : Blo 2217435 45517439 := bstep (se 1 (by rfl) ⟨34138079, by rfl⟩ : syracuseStep 45517439 = 68276159) B68276159
theorem B30344959 : Blo 2217435 30344959 := bstep (se 1 (by rfl) ⟨22758719, by rfl⟩ : syracuseStep 30344959 = 45517439) B45517439
theorem B40459945 : Blo 2217435 40459945 := bstep (se 2 (by rfl) ⟨15172479, by rfl⟩ : syracuseStep 40459945 = 30344959) B30344959
theorem B53946593 : Blo 2217435 53946593 := bstep (se 2 (by rfl) ⟨20229972, by rfl⟩ : syracuseStep 53946593 = 40459945) B40459945
theorem B35964395 : Blo 2217435 35964395 := bstep (se 1 (by rfl) ⟨26973296, by rfl⟩ : syracuseStep 35964395 = 53946593) B53946593
theorem B23976263 : Blo 2217435 23976263 := bstep (se 1 (by rfl) ⟨17982197, by rfl⟩ : syracuseStep 23976263 = 35964395) B35964395
theorem B15984175 : Blo 2217435 15984175 := bstep (se 1 (by rfl) ⟨11988131, by rfl⟩ : syracuseStep 15984175 = 23976263) B23976263
theorem B21312233 : Blo 2217435 21312233 := bstep (se 2 (by rfl) ⟨7992087, by rfl⟩ : syracuseStep 21312233 = 15984175) B15984175
theorem B14208155 : Blo 2217435 14208155 := bstep (se 1 (by rfl) ⟨10656116, by rfl⟩ : syracuseStep 14208155 = 21312233) B21312233
theorem B9472103 : Blo 2217435 9472103 := bstep (se 1 (by rfl) ⟨7104077, by rfl⟩ : syracuseStep 9472103 = 14208155) B14208155
theorem B6314735 : Blo 2217435 6314735 := bstep (se 1 (by rfl) ⟨4736051, by rfl⟩ : syracuseStep 6314735 = 9472103) B9472103
theorem B4209823 : Blo 2217435 4209823 := bstep (se 1 (by rfl) ⟨3157367, by rfl⟩ : syracuseStep 4209823 = 6314735) B6314735
theorem B5613097 : Blo 2217435 5613097 := bstep (se 2 (by rfl) ⟨2104911, by rfl⟩ : syracuseStep 5613097 = 4209823) B4209823
theorem B7484129 : Blo 2217435 7484129 := bstep (se 2 (by rfl) ⟨2806548, by rfl⟩ : syracuseStep 7484129 = 5613097) B5613097
theorem B4989419 : Blo 2217435 4989419 := bstep (se 1 (by rfl) ⟨3742064, by rfl⟩ : syracuseStep 4989419 = 7484129) B7484129
theorem B3326279 : Blo 2217435 3326279 := bstep (se 1 (by rfl) ⟨2494709, by rfl⟩ : syracuseStep 3326279 = 4989419) B4989419
theorem B2217519 : Blo 2217435 2217519 := bstep (se 1 (by rfl) ⟨1663139, by rfl⟩ : syracuseStep 2217519 = 3326279) B3326279
theorem B3326285 : Blo 2217435 3326285 := bbase (se 3 (by rfl) ⟨623678, by rfl⟩ : syracuseStep 3326285 = 1247357) (by norm_num)
theorem B2217523 : Blo 2217435 2217523 := bstep (se 1 (by rfl) ⟨1663142, by rfl⟩ : syracuseStep 2217523 = 3326285) B3326285
theorem B4989437 : Blo 2217435 4989437 := bbase (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) (by norm_num)
theorem B3326291 : Blo 2217435 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B2217527 : Blo 2217435 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B3742085 : Blo 2217435 3742085 := bbase (se 4 (by rfl) ⟨350820, by rfl⟩ : syracuseStep 3742085 = 701641) (by norm_num)
theorem B2494723 : Blo 2217435 2494723 := bstep (se 1 (by rfl) ⟨1871042, by rfl⟩ : syracuseStep 2494723 = 3742085) B3742085
theorem B3326297 : Blo 2217435 3326297 := bstep (se 2 (by rfl) ⟨1247361, by rfl⟩ : syracuseStep 3326297 = 2494723) B2494723
theorem B2217531 : Blo 2217435 2217531 := bstep (se 1 (by rfl) ⟨1663148, by rfl⟩ : syracuseStep 2217531 = 3326297) B3326297
theorem B16839413 : Blo 2217435 16839413 := bbase (se 5 (by rfl) ⟨789347, by rfl⟩ : syracuseStep 16839413 = 1578695) (by norm_num)
theorem B11226275 : Blo 2217435 11226275 := bstep (se 1 (by rfl) ⟨8419706, by rfl⟩ : syracuseStep 11226275 = 16839413) B16839413
theorem B7484183 : Blo 2217435 7484183 := bstep (se 1 (by rfl) ⟨5613137, by rfl⟩ : syracuseStep 7484183 = 11226275) B11226275
theorem B4989455 : Blo 2217435 4989455 := bstep (se 1 (by rfl) ⟨3742091, by rfl⟩ : syracuseStep 4989455 = 7484183) B7484183
theorem B3326303 : Blo 2217435 3326303 := bstep (se 1 (by rfl) ⟨2494727, by rfl⟩ : syracuseStep 3326303 = 4989455) B4989455
theorem B2217535 : Blo 2217435 2217535 := bstep (se 1 (by rfl) ⟨1663151, by rfl⟩ : syracuseStep 2217535 = 3326303) B3326303
theorem B3326309 : Blo 2217435 3326309 := bbase (se 4 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 3326309 = 623683) (by norm_num)
theorem B2217539 : Blo 2217435 2217539 := bstep (se 1 (by rfl) ⟨1663154, by rfl⟩ : syracuseStep 2217539 = 3326309) B3326309
theorem B4209869 : Blo 2217435 4209869 := bbase (se 3 (by rfl) ⟨789350, by rfl⟩ : syracuseStep 4209869 = 1578701) (by norm_num)
theorem B2806579 : Blo 2217435 2806579 := bstep (se 1 (by rfl) ⟨2104934, by rfl⟩ : syracuseStep 2806579 = 4209869) B4209869
theorem B3742105 : Blo 2217435 3742105 := bstep (se 2 (by rfl) ⟨1403289, by rfl⟩ : syracuseStep 3742105 = 2806579) B2806579
theorem B4989473 : Blo 2217435 4989473 := bstep (se 2 (by rfl) ⟨1871052, by rfl⟩ : syracuseStep 4989473 = 3742105) B3742105
theorem B3326315 : Blo 2217435 3326315 := bstep (se 1 (by rfl) ⟨2494736, by rfl⟩ : syracuseStep 3326315 = 4989473) B4989473
theorem B2217543 : Blo 2217435 2217543 := bstep (se 1 (by rfl) ⟨1663157, by rfl⟩ : syracuseStep 2217543 = 3326315) B3326315
theorem B2494741 : Blo 2217435 2494741 := bbase (se 6 (by rfl) ⟨58470, by rfl⟩ : syracuseStep 2494741 = 116941) (by norm_num)
theorem B3326321 : Blo 2217435 3326321 := bstep (se 2 (by rfl) ⟨1247370, by rfl⟩ : syracuseStep 3326321 = 2494741) B2494741
theorem B2217547 : Blo 2217435 2217547 := bstep (se 1 (by rfl) ⟨1663160, by rfl⟩ : syracuseStep 2217547 = 3326321) B3326321
theorem B2806589 : Blo 2217435 2806589 := bbase (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) (by norm_num)
theorem B7484237 : Blo 2217435 7484237 := bstep (se 3 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 7484237 = 2806589) B2806589
theorem B4989491 : Blo 2217435 4989491 := bstep (se 1 (by rfl) ⟨3742118, by rfl⟩ : syracuseStep 4989491 = 7484237) B7484237
theorem B3326327 : Blo 2217435 3326327 := bstep (se 1 (by rfl) ⟨2494745, by rfl⟩ : syracuseStep 3326327 = 4989491) B4989491
theorem B2217551 : Blo 2217435 2217551 := bstep (se 1 (by rfl) ⟨1663163, by rfl⟩ : syracuseStep 2217551 = 3326327) B3326327
theorem B3326333 : Blo 2217435 3326333 := bbase (se 3 (by rfl) ⟨623687, by rfl⟩ : syracuseStep 3326333 = 1247375) (by norm_num)
theorem B2217555 : Blo 2217435 2217555 := bstep (se 1 (by rfl) ⟨1663166, by rfl⟩ : syracuseStep 2217555 = 3326333) B3326333
theorem B4989509 : Blo 2217435 4989509 := bbase (se 4 (by rfl) ⟨467766, by rfl⟩ : syracuseStep 4989509 = 935533) (by norm_num)
theorem B3326339 : Blo 2217435 3326339 := bstep (se 1 (by rfl) ⟨2494754, by rfl⟩ : syracuseStep 3326339 = 4989509) B4989509
theorem B2217559 : Blo 2217435 2217559 := bstep (se 1 (by rfl) ⟨1663169, by rfl⟩ : syracuseStep 2217559 = 3326339) B3326339
theorem B2368073 : Blo 2217435 2368073 := bbase (se 2 (by rfl) ⟨888027, by rfl⟩ : syracuseStep 2368073 = 1776055) (by norm_num)
theorem B6314861 : Blo 2217435 6314861 := bstep (se 3 (by rfl) ⟨1184036, by rfl⟩ : syracuseStep 6314861 = 2368073) B2368073
theorem B4209907 : Blo 2217435 4209907 := bstep (se 1 (by rfl) ⟨3157430, by rfl⟩ : syracuseStep 4209907 = 6314861) B6314861
theorem B5613209 : Blo 2217435 5613209 := bstep (se 2 (by rfl) ⟨2104953, by rfl⟩ : syracuseStep 5613209 = 4209907) B4209907
theorem B3742139 : Blo 2217435 3742139 := bstep (se 1 (by rfl) ⟨2806604, by rfl⟩ : syracuseStep 3742139 = 5613209) B5613209
theorem B2494759 : Blo 2217435 2494759 := bstep (se 1 (by rfl) ⟨1871069, by rfl⟩ : syracuseStep 2494759 = 3742139) B3742139
theorem B3326345 : Blo 2217435 3326345 := bstep (se 2 (by rfl) ⟨1247379, by rfl⟩ : syracuseStep 3326345 = 2494759) B2494759
theorem B2217563 : Blo 2217435 2217563 := bstep (se 1 (by rfl) ⟨1663172, by rfl⟩ : syracuseStep 2217563 = 3326345) B3326345
theorem B11226437 : Blo 2217435 11226437 := bbase (se 4 (by rfl) ⟨1052478, by rfl⟩ : syracuseStep 11226437 = 2104957) (by norm_num)
theorem B7484291 : Blo 2217435 7484291 := bstep (se 1 (by rfl) ⟨5613218, by rfl⟩ : syracuseStep 7484291 = 11226437) B11226437
theorem B4989527 : Blo 2217435 4989527 := bstep (se 1 (by rfl) ⟨3742145, by rfl⟩ : syracuseStep 4989527 = 7484291) B7484291
theorem B3326351 : Blo 2217435 3326351 := bstep (se 1 (by rfl) ⟨2494763, by rfl⟩ : syracuseStep 3326351 = 4989527) B4989527
theorem B2217567 : Blo 2217435 2217567 := bstep (se 1 (by rfl) ⟨1663175, by rfl⟩ : syracuseStep 2217567 = 3326351) B3326351
theorem B3326357 : Blo 2217435 3326357 := bbase (se 6 (by rfl) ⟨77961, by rfl⟩ : syracuseStep 3326357 = 155923) (by norm_num)
theorem B2217571 : Blo 2217435 2217571 := bstep (se 1 (by rfl) ⟨1663178, by rfl⟩ : syracuseStep 2217571 = 3326357) B3326357
theorem B2997109 : Blo 2217435 2997109 := bbase (se 5 (by rfl) ⟨140489, by rfl⟩ : syracuseStep 2997109 = 280979) (by norm_num)
theorem B3996145 : Blo 2217435 3996145 := bstep (se 2 (by rfl) ⟨1498554, by rfl⟩ : syracuseStep 3996145 = 2997109) B2997109
theorem B5328193 : Blo 2217435 5328193 := bstep (se 2 (by rfl) ⟨1998072, by rfl⟩ : syracuseStep 5328193 = 3996145) B3996145
theorem B7104257 : Blo 2217435 7104257 := bstep (se 2 (by rfl) ⟨2664096, by rfl⟩ : syracuseStep 7104257 = 5328193) B5328193
theorem B4736171 : Blo 2217435 4736171 := bstep (se 1 (by rfl) ⟨3552128, by rfl⟩ : syracuseStep 4736171 = 7104257) B7104257
theorem B12629789 : Blo 2217435 12629789 := bstep (se 3 (by rfl) ⟨2368085, by rfl⟩ : syracuseStep 12629789 = 4736171) B4736171
theorem B8419859 : Blo 2217435 8419859 := bstep (se 1 (by rfl) ⟨6314894, by rfl⟩ : syracuseStep 8419859 = 12629789) B12629789
theorem B5613239 : Blo 2217435 5613239 := bstep (se 1 (by rfl) ⟨4209929, by rfl⟩ : syracuseStep 5613239 = 8419859) B8419859
theorem B3742159 : Blo 2217435 3742159 := bstep (se 1 (by rfl) ⟨2806619, by rfl⟩ : syracuseStep 3742159 = 5613239) B5613239
theorem B4989545 : Blo 2217435 4989545 := bstep (se 2 (by rfl) ⟨1871079, by rfl⟩ : syracuseStep 4989545 = 3742159) B3742159
theorem B3326363 : Blo 2217435 3326363 := bstep (se 1 (by rfl) ⟨2494772, by rfl⟩ : syracuseStep 3326363 = 4989545) B4989545
theorem B2217575 : Blo 2217435 2217575 := bstep (se 1 (by rfl) ⟨1663181, by rfl⟩ : syracuseStep 2217575 = 3326363) B3326363
theorem B2494777 : Blo 2217435 2494777 := bbase (se 2 (by rfl) ⟨935541, by rfl⟩ : syracuseStep 2494777 = 1871083) (by norm_num)
theorem B3326369 : Blo 2217435 3326369 := bstep (se 2 (by rfl) ⟨1247388, by rfl⟩ : syracuseStep 3326369 = 2494777) B2494777
theorem B2217579 : Blo 2217435 2217579 := bstep (se 1 (by rfl) ⟨1663184, by rfl⟩ : syracuseStep 2217579 = 3326369) B3326369
theorem B6314917 : Blo 2217435 6314917 := bbase (se 4 (by rfl) ⟨592023, by rfl⟩ : syracuseStep 6314917 = 1184047) (by norm_num)
theorem B8419889 : Blo 2217435 8419889 := bstep (se 2 (by rfl) ⟨3157458, by rfl⟩ : syracuseStep 8419889 = 6314917) B6314917
theorem B5613259 : Blo 2217435 5613259 := bstep (se 1 (by rfl) ⟨4209944, by rfl⟩ : syracuseStep 5613259 = 8419889) B8419889
theorem B7484345 : Blo 2217435 7484345 := bstep (se 2 (by rfl) ⟨2806629, by rfl⟩ : syracuseStep 7484345 = 5613259) B5613259
theorem B4989563 : Blo 2217435 4989563 := bstep (se 1 (by rfl) ⟨3742172, by rfl⟩ : syracuseStep 4989563 = 7484345) B7484345
theorem B3326375 : Blo 2217435 3326375 := bstep (se 1 (by rfl) ⟨2494781, by rfl⟩ : syracuseStep 3326375 = 4989563) B4989563
theorem B2217583 : Blo 2217435 2217583 := bstep (se 1 (by rfl) ⟨1663187, by rfl⟩ : syracuseStep 2217583 = 3326375) B3326375
theorem B3326381 : Blo 2217435 3326381 := bbase (se 3 (by rfl) ⟨623696, by rfl⟩ : syracuseStep 3326381 = 1247393) (by norm_num)
theorem B2217587 : Blo 2217435 2217587 := bstep (se 1 (by rfl) ⟨1663190, by rfl⟩ : syracuseStep 2217587 = 3326381) B3326381
theorem B4989581 : Blo 2217435 4989581 := bbase (se 3 (by rfl) ⟨935546, by rfl⟩ : syracuseStep 4989581 = 1871093) (by norm_num)
theorem B3326387 : Blo 2217435 3326387 := bstep (se 1 (by rfl) ⟨2494790, by rfl⟩ : syracuseStep 3326387 = 4989581) B4989581
theorem B2217591 : Blo 2217435 2217591 := bstep (se 1 (by rfl) ⟨1663193, by rfl⟩ : syracuseStep 2217591 = 3326387) B3326387
theorem B2806645 : Blo 2217435 2806645 := bbase (se 5 (by rfl) ⟨131561, by rfl⟩ : syracuseStep 2806645 = 263123) (by norm_num)
theorem B3742193 : Blo 2217435 3742193 := bstep (se 2 (by rfl) ⟨1403322, by rfl⟩ : syracuseStep 3742193 = 2806645) B2806645
theorem B2494795 : Blo 2217435 2494795 := bstep (se 1 (by rfl) ⟨1871096, by rfl⟩ : syracuseStep 2494795 = 3742193) B3742193
theorem B3326393 : Blo 2217435 3326393 := bstep (se 2 (by rfl) ⟨1247397, by rfl⟩ : syracuseStep 3326393 = 2494795) B2494795
theorem B2217595 : Blo 2217435 2217595 := bstep (se 1 (by rfl) ⟨1663196, by rfl⟩ : syracuseStep 2217595 = 3326393) B3326393
theorem B22759541 : Blo 2217435 22759541 := bbase (se 5 (by rfl) ⟨1066853, by rfl⟩ : syracuseStep 22759541 = 2133707) (by norm_num)
theorem B15173027 : Blo 2217435 15173027 := bstep (se 1 (by rfl) ⟨11379770, by rfl⟩ : syracuseStep 15173027 = 22759541) B22759541
theorem B10115351 : Blo 2217435 10115351 := bstep (se 1 (by rfl) ⟨7586513, by rfl⟩ : syracuseStep 10115351 = 15173027) B15173027
theorem B6743567 : Blo 2217435 6743567 := bstep (se 1 (by rfl) ⟨5057675, by rfl⟩ : syracuseStep 6743567 = 10115351) B10115351
theorem B4495711 : Blo 2217435 4495711 := bstep (se 1 (by rfl) ⟨3371783, by rfl⟩ : syracuseStep 4495711 = 6743567) B6743567
theorem B5994281 : Blo 2217435 5994281 := bstep (se 2 (by rfl) ⟨2247855, by rfl⟩ : syracuseStep 5994281 = 4495711) B4495711
theorem B15984749 : Blo 2217435 15984749 := bstep (se 3 (by rfl) ⟨2997140, by rfl⟩ : syracuseStep 15984749 = 5994281) B5994281
theorem B42625997 : Blo 2217435 42625997 := bstep (se 3 (by rfl) ⟨7992374, by rfl⟩ : syracuseStep 42625997 = 15984749) B15984749
theorem B28417331 : Blo 2217435 28417331 := bstep (se 1 (by rfl) ⟨21312998, by rfl⟩ : syracuseStep 28417331 = 42625997) B42625997
theorem B18944887 : Blo 2217435 18944887 := bstep (se 1 (by rfl) ⟨14208665, by rfl⟩ : syracuseStep 18944887 = 28417331) B28417331
theorem B25259849 : Blo 2217435 25259849 := bstep (se 2 (by rfl) ⟨9472443, by rfl⟩ : syracuseStep 25259849 = 18944887) B18944887
theorem B16839899 : Blo 2217435 16839899 := bstep (se 1 (by rfl) ⟨12629924, by rfl⟩ : syracuseStep 16839899 = 25259849) B25259849
theorem B11226599 : Blo 2217435 11226599 := bstep (se 1 (by rfl) ⟨8419949, by rfl⟩ : syracuseStep 11226599 = 16839899) B16839899
theorem B7484399 : Blo 2217435 7484399 := bstep (se 1 (by rfl) ⟨5613299, by rfl⟩ : syracuseStep 7484399 = 11226599) B11226599
theorem B4989599 : Blo 2217435 4989599 := bstep (se 1 (by rfl) ⟨3742199, by rfl⟩ : syracuseStep 4989599 = 7484399) B7484399
theorem B3326399 : Blo 2217435 3326399 := bstep (se 1 (by rfl) ⟨2494799, by rfl⟩ : syracuseStep 3326399 = 4989599) B4989599
theorem B2217599 : Blo 2217435 2217599 := bstep (se 1 (by rfl) ⟨1663199, by rfl⟩ : syracuseStep 2217599 = 3326399) B3326399
theorem B3326405 : Blo 2217435 3326405 := bbase (se 4 (by rfl) ⟨311850, by rfl⟩ : syracuseStep 3326405 = 623701) (by norm_num)
theorem B2217603 : Blo 2217435 2217603 := bstep (se 1 (by rfl) ⟨1663202, by rfl⟩ : syracuseStep 2217603 = 3326405) B3326405
theorem B3742213 : Blo 2217435 3742213 := bbase (se 4 (by rfl) ⟨350832, by rfl⟩ : syracuseStep 3742213 = 701665) (by norm_num)
theorem B4989617 : Blo 2217435 4989617 := bstep (se 2 (by rfl) ⟨1871106, by rfl⟩ : syracuseStep 4989617 = 3742213) B3742213
theorem B3326411 : Blo 2217435 3326411 := bstep (se 1 (by rfl) ⟨2494808, by rfl⟩ : syracuseStep 3326411 = 4989617) B4989617
theorem B2217607 : Blo 2217435 2217607 := bstep (se 1 (by rfl) ⟨1663205, by rfl⟩ : syracuseStep 2217607 = 3326411) B3326411
theorem B2494813 : Blo 2217435 2494813 := bbase (se 3 (by rfl) ⟨467777, by rfl⟩ : syracuseStep 2494813 = 935555) (by norm_num)
theorem B3326417 : Blo 2217435 3326417 := bstep (se 2 (by rfl) ⟨1247406, by rfl⟩ : syracuseStep 3326417 = 2494813) B2494813
theorem B2217611 : Blo 2217435 2217611 := bstep (se 1 (by rfl) ⟨1663208, by rfl⟩ : syracuseStep 2217611 = 3326417) B3326417
theorem B7484453 : Blo 2217435 7484453 := bbase (se 4 (by rfl) ⟨701667, by rfl⟩ : syracuseStep 7484453 = 1403335) (by norm_num)
theorem B4989635 : Blo 2217435 4989635 := bstep (se 1 (by rfl) ⟨3742226, by rfl⟩ : syracuseStep 4989635 = 7484453) B7484453
theorem B3326423 : Blo 2217435 3326423 := bstep (se 1 (by rfl) ⟨2494817, by rfl⟩ : syracuseStep 3326423 = 4989635) B4989635
theorem B2217615 : Blo 2217435 2217615 := bstep (se 1 (by rfl) ⟨1663211, by rfl⟩ : syracuseStep 2217615 = 3326423) B3326423
theorem B3326429 : Blo 2217435 3326429 := bbase (se 3 (by rfl) ⟨623705, by rfl⟩ : syracuseStep 3326429 = 1247411) (by norm_num)
theorem B2217619 : Blo 2217435 2217619 := bstep (se 1 (by rfl) ⟨1663214, by rfl⟩ : syracuseStep 2217619 = 3326429) B3326429
theorem B4989653 : Blo 2217435 4989653 := bbase (se 7 (by rfl) ⟨58472, by rfl⟩ : syracuseStep 4989653 = 116945) (by norm_num)
theorem B3326435 : Blo 2217435 3326435 := bstep (se 1 (by rfl) ⟨2494826, by rfl⟩ : syracuseStep 3326435 = 4989653) B4989653
theorem B2217623 : Blo 2217435 2217623 := bstep (se 1 (by rfl) ⟨1663217, by rfl⟩ : syracuseStep 2217623 = 3326435) B3326435
theorem B9472565 : Blo 2217435 9472565 := bbase (se 5 (by rfl) ⟨444026, by rfl⟩ : syracuseStep 9472565 = 888053) (by norm_num)
theorem B6315043 : Blo 2217435 6315043 := bstep (se 1 (by rfl) ⟨4736282, by rfl⟩ : syracuseStep 6315043 = 9472565) B9472565
theorem B8420057 : Blo 2217435 8420057 := bstep (se 2 (by rfl) ⟨3157521, by rfl⟩ : syracuseStep 8420057 = 6315043) B6315043
theorem B5613371 : Blo 2217435 5613371 := bstep (se 1 (by rfl) ⟨4210028, by rfl⟩ : syracuseStep 5613371 = 8420057) B8420057
theorem B3742247 : Blo 2217435 3742247 := bstep (se 1 (by rfl) ⟨2806685, by rfl⟩ : syracuseStep 3742247 = 5613371) B5613371
theorem B2494831 : Blo 2217435 2494831 := bstep (se 1 (by rfl) ⟨1871123, by rfl⟩ : syracuseStep 2494831 = 3742247) B3742247
theorem B3326441 : Blo 2217435 3326441 := bstep (se 2 (by rfl) ⟨1247415, by rfl⟩ : syracuseStep 3326441 = 2494831) B2494831
theorem B2217627 : Blo 2217435 2217627 := bstep (se 1 (by rfl) ⟨1663220, by rfl⟩ : syracuseStep 2217627 = 3326441) B3326441
theorem B2433205 : Blo 2217435 2433205 := bbase (se 5 (by rfl) ⟨114056, by rfl⟩ : syracuseStep 2433205 = 228113) (by norm_num)
theorem B12977093 : Blo 2217435 12977093 := bstep (se 4 (by rfl) ⟨1216602, by rfl⟩ : syracuseStep 12977093 = 2433205) B2433205
theorem B8651395 : Blo 2217435 8651395 := bstep (se 1 (by rfl) ⟨6488546, by rfl⟩ : syracuseStep 8651395 = 12977093) B12977093
theorem B11535193 : Blo 2217435 11535193 := bstep (se 2 (by rfl) ⟨4325697, by rfl⟩ : syracuseStep 11535193 = 8651395) B8651395
theorem B15380257 : Blo 2217435 15380257 := bstep (se 2 (by rfl) ⟨5767596, by rfl⟩ : syracuseStep 15380257 = 11535193) B11535193
theorem B20507009 : Blo 2217435 20507009 := bstep (se 2 (by rfl) ⟨7690128, by rfl⟩ : syracuseStep 20507009 = 15380257) B15380257
theorem B54685357 : Blo 2217435 54685357 := bstep (se 3 (by rfl) ⟨10253504, by rfl⟩ : syracuseStep 54685357 = 20507009) B20507009
theorem B291655237 : Blo 2217435 291655237 := bstep (se 4 (by rfl) ⟨27342678, by rfl⟩ : syracuseStep 291655237 = 54685357) B54685357
theorem B388873649 : Blo 2217435 388873649 := bstep (se 2 (by rfl) ⟨145827618, by rfl⟩ : syracuseStep 388873649 = 291655237) B291655237
theorem B259249099 : Blo 2217435 259249099 := bstep (se 1 (by rfl) ⟨194436824, by rfl⟩ : syracuseStep 259249099 = 388873649) B388873649
theorem B345665465 : Blo 2217435 345665465 := bstep (se 2 (by rfl) ⟨129624549, by rfl⟩ : syracuseStep 345665465 = 259249099) B259249099
theorem B230443643 : Blo 2217435 230443643 := bstep (se 1 (by rfl) ⟨172832732, by rfl⟩ : syracuseStep 230443643 = 345665465) B345665465
theorem B614516381 : Blo 2217435 614516381 := bstep (se 3 (by rfl) ⟨115221821, by rfl⟩ : syracuseStep 614516381 = 230443643) B230443643
theorem B409677587 : Blo 2217435 409677587 := bstep (se 1 (by rfl) ⟨307258190, by rfl⟩ : syracuseStep 409677587 = 614516381) B614516381
theorem B273118391 : Blo 2217435 273118391 := bstep (se 1 (by rfl) ⟨204838793, by rfl⟩ : syracuseStep 273118391 = 409677587) B409677587
theorem B182078927 : Blo 2217435 182078927 := bstep (se 1 (by rfl) ⟨136559195, by rfl⟩ : syracuseStep 182078927 = 273118391) B273118391
theorem B121385951 : Blo 2217435 121385951 := bstep (se 1 (by rfl) ⟨91039463, by rfl⟩ : syracuseStep 121385951 = 182078927) B182078927
theorem B80923967 : Blo 2217435 80923967 := bstep (se 1 (by rfl) ⟨60692975, by rfl⟩ : syracuseStep 80923967 = 121385951) B121385951
theorem B53949311 : Blo 2217435 53949311 := bstep (se 1 (by rfl) ⟨40461983, by rfl⟩ : syracuseStep 53949311 = 80923967) B80923967
theorem B35966207 : Blo 2217435 35966207 := bstep (se 1 (by rfl) ⟨26974655, by rfl⟩ : syracuseStep 35966207 = 53949311) B53949311
theorem B23977471 : Blo 2217435 23977471 := bstep (se 1 (by rfl) ⟨17983103, by rfl⟩ : syracuseStep 23977471 = 35966207) B35966207
theorem B31969961 : Blo 2217435 31969961 := bstep (se 2 (by rfl) ⟨11988735, by rfl⟩ : syracuseStep 31969961 = 23977471) B23977471
theorem B21313307 : Blo 2217435 21313307 := bstep (se 1 (by rfl) ⟨15984980, by rfl⟩ : syracuseStep 21313307 = 31969961) B31969961
theorem B14208871 : Blo 2217435 14208871 := bstep (se 1 (by rfl) ⟨10656653, by rfl⟩ : syracuseStep 14208871 = 21313307) B21313307
theorem B18945161 : Blo 2217435 18945161 := bstep (se 2 (by rfl) ⟨7104435, by rfl⟩ : syracuseStep 18945161 = 14208871) B14208871
theorem B12630107 : Blo 2217435 12630107 := bstep (se 1 (by rfl) ⟨9472580, by rfl⟩ : syracuseStep 12630107 = 18945161) B18945161
theorem B8420071 : Blo 2217435 8420071 := bstep (se 1 (by rfl) ⟨6315053, by rfl⟩ : syracuseStep 8420071 = 12630107) B12630107
theorem B11226761 : Blo 2217435 11226761 := bstep (se 2 (by rfl) ⟨4210035, by rfl⟩ : syracuseStep 11226761 = 8420071) B8420071
theorem B7484507 : Blo 2217435 7484507 := bstep (se 1 (by rfl) ⟨5613380, by rfl⟩ : syracuseStep 7484507 = 11226761) B11226761
theorem B4989671 : Blo 2217435 4989671 := bstep (se 1 (by rfl) ⟨3742253, by rfl⟩ : syracuseStep 4989671 = 7484507) B7484507
theorem B3326447 : Blo 2217435 3326447 := bstep (se 1 (by rfl) ⟨2494835, by rfl⟩ : syracuseStep 3326447 = 4989671) B4989671
theorem B2217631 : Blo 2217435 2217631 := bstep (se 1 (by rfl) ⟨1663223, by rfl⟩ : syracuseStep 2217631 = 3326447) B3326447
theorem B3326453 : Blo 2217435 3326453 := bbase (se 5 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 3326453 = 311855) (by norm_num)
theorem B2217635 : Blo 2217435 2217635 := bstep (se 1 (by rfl) ⟨1663226, by rfl⟩ : syracuseStep 2217635 = 3326453) B3326453
theorem B6315077 : Blo 2217435 6315077 := bbase (se 4 (by rfl) ⟨592038, by rfl⟩ : syracuseStep 6315077 = 1184077) (by norm_num)
theorem B4210051 : Blo 2217435 4210051 := bstep (se 1 (by rfl) ⟨3157538, by rfl⟩ : syracuseStep 4210051 = 6315077) B6315077
theorem B5613401 : Blo 2217435 5613401 := bstep (se 2 (by rfl) ⟨2105025, by rfl⟩ : syracuseStep 5613401 = 4210051) B4210051
theorem B3742267 : Blo 2217435 3742267 := bstep (se 1 (by rfl) ⟨2806700, by rfl⟩ : syracuseStep 3742267 = 5613401) B5613401
theorem B4989689 : Blo 2217435 4989689 := bstep (se 2 (by rfl) ⟨1871133, by rfl⟩ : syracuseStep 4989689 = 3742267) B3742267
theorem B3326459 : Blo 2217435 3326459 := bstep (se 1 (by rfl) ⟨2494844, by rfl⟩ : syracuseStep 3326459 = 4989689) B4989689
theorem B2217639 : Blo 2217435 2217639 := bstep (se 1 (by rfl) ⟨1663229, by rfl⟩ : syracuseStep 2217639 = 3326459) B3326459
theorem B2494849 : Blo 2217435 2494849 := bbase (se 2 (by rfl) ⟨935568, by rfl⟩ : syracuseStep 2494849 = 1871137) (by norm_num)
theorem B3326465 : Blo 2217435 3326465 := bstep (se 2 (by rfl) ⟨1247424, by rfl⟩ : syracuseStep 3326465 = 2494849) B2494849
theorem B2217643 : Blo 2217435 2217643 := bstep (se 1 (by rfl) ⟨1663232, by rfl⟩ : syracuseStep 2217643 = 3326465) B3326465
theorem B5613421 : Blo 2217435 5613421 := bbase (se 3 (by rfl) ⟨1052516, by rfl⟩ : syracuseStep 5613421 = 2105033) (by norm_num)
theorem B7484561 : Blo 2217435 7484561 := bstep (se 2 (by rfl) ⟨2806710, by rfl⟩ : syracuseStep 7484561 = 5613421) B5613421
theorem B4989707 : Blo 2217435 4989707 := bstep (se 1 (by rfl) ⟨3742280, by rfl⟩ : syracuseStep 4989707 = 7484561) B7484561
theorem B3326471 : Blo 2217435 3326471 := bstep (se 1 (by rfl) ⟨2494853, by rfl⟩ : syracuseStep 3326471 = 4989707) B4989707
theorem B2217647 : Blo 2217435 2217647 := bstep (se 1 (by rfl) ⟨1663235, by rfl⟩ : syracuseStep 2217647 = 3326471) B3326471
theorem B3326477 : Blo 2217435 3326477 := bbase (se 3 (by rfl) ⟨623714, by rfl⟩ : syracuseStep 3326477 = 1247429) (by norm_num)
theorem B2217651 : Blo 2217435 2217651 := bstep (se 1 (by rfl) ⟨1663238, by rfl⟩ : syracuseStep 2217651 = 3326477) B3326477
theorem B4989725 : Blo 2217435 4989725 := bbase (se 3 (by rfl) ⟨935573, by rfl⟩ : syracuseStep 4989725 = 1871147) (by norm_num)
theorem B3326483 : Blo 2217435 3326483 := bstep (se 1 (by rfl) ⟨2494862, by rfl⟩ : syracuseStep 3326483 = 4989725) B4989725
theorem B2217655 : Blo 2217435 2217655 := bstep (se 1 (by rfl) ⟨1663241, by rfl⟩ : syracuseStep 2217655 = 3326483) B3326483
theorem B3742301 : Blo 2217435 3742301 := bbase (se 3 (by rfl) ⟨701681, by rfl⟩ : syracuseStep 3742301 = 1403363) (by norm_num)
theorem B2494867 : Blo 2217435 2494867 := bstep (se 1 (by rfl) ⟨1871150, by rfl⟩ : syracuseStep 2494867 = 3742301) B3742301
theorem B3326489 : Blo 2217435 3326489 := bstep (se 2 (by rfl) ⟨1247433, by rfl⟩ : syracuseStep 3326489 = 2494867) B2494867
theorem B2217659 : Blo 2217435 2217659 := bstep (se 1 (by rfl) ⟨1663244, by rfl⟩ : syracuseStep 2217659 = 3326489) B3326489
theorem B3552269 : Blo 2217435 3552269 := bbase (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) (by norm_num)
theorem B9472717 : Blo 2217435 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B12630289 : Blo 2217435 12630289 := bstep (se 2 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 12630289 = 9472717) B9472717
theorem B16840385 : Blo 2217435 16840385 := bstep (se 2 (by rfl) ⟨6315144, by rfl⟩ : syracuseStep 16840385 = 12630289) B12630289
theorem B11226923 : Blo 2217435 11226923 := bstep (se 1 (by rfl) ⟨8420192, by rfl⟩ : syracuseStep 11226923 = 16840385) B16840385
theorem B7484615 : Blo 2217435 7484615 := bstep (se 1 (by rfl) ⟨5613461, by rfl⟩ : syracuseStep 7484615 = 11226923) B11226923
theorem B4989743 : Blo 2217435 4989743 := bstep (se 1 (by rfl) ⟨3742307, by rfl⟩ : syracuseStep 4989743 = 7484615) B7484615
theorem B3326495 : Blo 2217435 3326495 := bstep (se 1 (by rfl) ⟨2494871, by rfl⟩ : syracuseStep 3326495 = 4989743) B4989743
theorem B2217663 : Blo 2217435 2217663 := bstep (se 1 (by rfl) ⟨1663247, by rfl⟩ : syracuseStep 2217663 = 3326495) B3326495
theorem B3326501 : Blo 2217435 3326501 := bbase (se 4 (by rfl) ⟨311859, by rfl⟩ : syracuseStep 3326501 = 623719) (by norm_num)
theorem B2217667 : Blo 2217435 2217667 := bstep (se 1 (by rfl) ⟨1663250, by rfl⟩ : syracuseStep 2217667 = 3326501) B3326501
theorem B2806741 : Blo 2217435 2806741 := bbase (se 7 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 2806741 = 65783) (by norm_num)
theorem B3742321 : Blo 2217435 3742321 := bstep (se 2 (by rfl) ⟨1403370, by rfl⟩ : syracuseStep 3742321 = 2806741) B2806741
theorem B4989761 : Blo 2217435 4989761 := bstep (se 2 (by rfl) ⟨1871160, by rfl⟩ : syracuseStep 4989761 = 3742321) B3742321
theorem B3326507 : Blo 2217435 3326507 := bstep (se 1 (by rfl) ⟨2494880, by rfl⟩ : syracuseStep 3326507 = 4989761) B4989761
theorem B2217671 : Blo 2217435 2217671 := bstep (se 1 (by rfl) ⟨1663253, by rfl⟩ : syracuseStep 2217671 = 3326507) B3326507
theorem B2494885 : Blo 2217435 2494885 := bbase (se 4 (by rfl) ⟨233895, by rfl⟩ : syracuseStep 2494885 = 467791) (by norm_num)
theorem B3326513 : Blo 2217435 3326513 := bstep (se 2 (by rfl) ⟨1247442, by rfl⟩ : syracuseStep 3326513 = 2494885) B2494885
theorem B2217675 : Blo 2217435 2217675 := bstep (se 1 (by rfl) ⟨1663256, by rfl⟩ : syracuseStep 2217675 = 3326513) B3326513
theorem B8991749 : Blo 2217435 8991749 := bbase (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) (by norm_num)
theorem B5994499 : Blo 2217435 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B7992665 : Blo 2217435 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B5328443 : Blo 2217435 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B14209181 : Blo 2217435 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B9472787 : Blo 2217435 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B6315191 : Blo 2217435 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B4210127 : Blo 2217435 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B2806751 : Blo 2217435 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B7484669 : Blo 2217435 7484669 := bstep (se 3 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 7484669 = 2806751) B2806751
theorem B4989779 : Blo 2217435 4989779 := bstep (se 1 (by rfl) ⟨3742334, by rfl⟩ : syracuseStep 4989779 = 7484669) B7484669
theorem B3326519 : Blo 2217435 3326519 := bstep (se 1 (by rfl) ⟨2494889, by rfl⟩ : syracuseStep 3326519 = 4989779) B4989779
theorem B2217679 : Blo 2217435 2217679 := bstep (se 1 (by rfl) ⟨1663259, by rfl⟩ : syracuseStep 2217679 = 3326519) B3326519
theorem B3326525 : Blo 2217435 3326525 := bbase (se 3 (by rfl) ⟨623723, by rfl⟩ : syracuseStep 3326525 = 1247447) (by norm_num)
theorem B2217683 : Blo 2217435 2217683 := bstep (se 1 (by rfl) ⟨1663262, by rfl⟩ : syracuseStep 2217683 = 3326525) B3326525
theorem B4989797 : Blo 2217435 4989797 := bbase (se 4 (by rfl) ⟨467793, by rfl⟩ : syracuseStep 4989797 = 935587) (by norm_num)
theorem B3326531 : Blo 2217435 3326531 := bstep (se 1 (by rfl) ⟨2494898, by rfl⟩ : syracuseStep 3326531 = 4989797) B4989797
theorem B2217687 : Blo 2217435 2217687 := bstep (se 1 (by rfl) ⟨1663265, by rfl⟩ : syracuseStep 2217687 = 3326531) B3326531
theorem B5613533 : Blo 2217435 5613533 := bbase (se 3 (by rfl) ⟨1052537, by rfl⟩ : syracuseStep 5613533 = 2105075) (by norm_num)
theorem B3742355 : Blo 2217435 3742355 := bstep (se 1 (by rfl) ⟨2806766, by rfl⟩ : syracuseStep 3742355 = 5613533) B5613533
theorem B2494903 : Blo 2217435 2494903 := bstep (se 1 (by rfl) ⟨1871177, by rfl⟩ : syracuseStep 2494903 = 3742355) B3742355
theorem B3326537 : Blo 2217435 3326537 := bstep (se 2 (by rfl) ⟨1247451, by rfl⟩ : syracuseStep 3326537 = 2494903) B2494903
theorem B2217691 : Blo 2217435 2217691 := bstep (se 1 (by rfl) ⟨1663268, by rfl⟩ : syracuseStep 2217691 = 3326537) B3326537
theorem B4210157 : Blo 2217435 4210157 := bbase (se 3 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 4210157 = 1578809) (by norm_num)
theorem B11227085 : Blo 2217435 11227085 := bstep (se 3 (by rfl) ⟨2105078, by rfl⟩ : syracuseStep 11227085 = 4210157) B4210157
theorem B7484723 : Blo 2217435 7484723 := bstep (se 1 (by rfl) ⟨5613542, by rfl⟩ : syracuseStep 7484723 = 11227085) B11227085
theorem B4989815 : Blo 2217435 4989815 := bstep (se 1 (by rfl) ⟨3742361, by rfl⟩ : syracuseStep 4989815 = 7484723) B7484723
theorem B3326543 : Blo 2217435 3326543 := bstep (se 1 (by rfl) ⟨2494907, by rfl⟩ : syracuseStep 3326543 = 4989815) B4989815
theorem B2217695 : Blo 2217435 2217695 := bstep (se 1 (by rfl) ⟨1663271, by rfl⟩ : syracuseStep 2217695 = 3326543) B3326543
theorem B3326549 : Blo 2217435 3326549 := bbase (se 8 (by rfl) ⟨19491, by rfl⟩ : syracuseStep 3326549 = 38983) (by norm_num)
theorem B2217699 : Blo 2217435 2217699 := bstep (se 1 (by rfl) ⟨1663274, by rfl⟩ : syracuseStep 2217699 = 3326549) B3326549
theorem B4050901 : Blo 2217435 4050901 := bbase (se 7 (by rfl) ⟨47471, by rfl⟩ : syracuseStep 4050901 = 94943) (by norm_num)
theorem B21604805 : Blo 2217435 21604805 := bstep (se 4 (by rfl) ⟨2025450, by rfl⟩ : syracuseStep 21604805 = 4050901) B4050901
theorem B14403203 : Blo 2217435 14403203 := bstep (se 1 (by rfl) ⟨10802402, by rfl⟩ : syracuseStep 14403203 = 21604805) B21604805
theorem B9602135 : Blo 2217435 9602135 := bstep (se 1 (by rfl) ⟨7201601, by rfl⟩ : syracuseStep 9602135 = 14403203) B14403203
theorem B6401423 : Blo 2217435 6401423 := bstep (se 1 (by rfl) ⟨4801067, by rfl⟩ : syracuseStep 6401423 = 9602135) B9602135
theorem B4267615 : Blo 2217435 4267615 := bstep (se 1 (by rfl) ⟨3200711, by rfl⟩ : syracuseStep 4267615 = 6401423) B6401423
theorem B5690153 : Blo 2217435 5690153 := bstep (se 2 (by rfl) ⟨2133807, by rfl⟩ : syracuseStep 5690153 = 4267615) B4267615
theorem B3793435 : Blo 2217435 3793435 := bstep (se 1 (by rfl) ⟨2845076, by rfl⟩ : syracuseStep 3793435 = 5690153) B5690153
theorem B20231653 : Blo 2217435 20231653 := bstep (se 4 (by rfl) ⟨1896717, by rfl⟩ : syracuseStep 20231653 = 3793435) B3793435
theorem B26975537 : Blo 2217435 26975537 := bstep (se 2 (by rfl) ⟨10115826, by rfl⟩ : syracuseStep 26975537 = 20231653) B20231653
theorem B17983691 : Blo 2217435 17983691 := bstep (se 1 (by rfl) ⟨13487768, by rfl⟩ : syracuseStep 17983691 = 26975537) B26975537
theorem B11989127 : Blo 2217435 11989127 := bstep (se 1 (by rfl) ⟨8991845, by rfl⟩ : syracuseStep 11989127 = 17983691) B17983691
theorem B7992751 : Blo 2217435 7992751 := bstep (se 1 (by rfl) ⟨5994563, by rfl⟩ : syracuseStep 7992751 = 11989127) B11989127
theorem B10657001 : Blo 2217435 10657001 := bstep (se 2 (by rfl) ⟨3996375, by rfl⟩ : syracuseStep 10657001 = 7992751) B7992751
theorem B7104667 : Blo 2217435 7104667 := bstep (se 1 (by rfl) ⟨5328500, by rfl⟩ : syracuseStep 7104667 = 10657001) B10657001
theorem B9472889 : Blo 2217435 9472889 := bstep (se 2 (by rfl) ⟨3552333, by rfl⟩ : syracuseStep 9472889 = 7104667) B7104667
theorem B6315259 : Blo 2217435 6315259 := bstep (se 1 (by rfl) ⟨4736444, by rfl⟩ : syracuseStep 6315259 = 9472889) B9472889
theorem B8420345 : Blo 2217435 8420345 := bstep (se 2 (by rfl) ⟨3157629, by rfl⟩ : syracuseStep 8420345 = 6315259) B6315259
theorem B5613563 : Blo 2217435 5613563 := bstep (se 1 (by rfl) ⟨4210172, by rfl⟩ : syracuseStep 5613563 = 8420345) B8420345
theorem B3742375 : Blo 2217435 3742375 := bstep (se 1 (by rfl) ⟨2806781, by rfl⟩ : syracuseStep 3742375 = 5613563) B5613563
theorem B4989833 : Blo 2217435 4989833 := bstep (se 2 (by rfl) ⟨1871187, by rfl⟩ : syracuseStep 4989833 = 3742375) B3742375
theorem B3326555 : Blo 2217435 3326555 := bstep (se 1 (by rfl) ⟨2494916, by rfl⟩ : syracuseStep 3326555 = 4989833) B4989833
theorem B2217703 : Blo 2217435 2217703 := bstep (se 1 (by rfl) ⟨1663277, by rfl⟩ : syracuseStep 2217703 = 3326555) B3326555
theorem B2494921 : Blo 2217435 2494921 := bbase (se 2 (by rfl) ⟨935595, by rfl⟩ : syracuseStep 2494921 = 1871191) (by norm_num)
theorem B3326561 : Blo 2217435 3326561 := bstep (se 2 (by rfl) ⟨1247460, by rfl⟩ : syracuseStep 3326561 = 2494921) B2494921
theorem B2217707 : Blo 2217435 2217707 := bstep (se 1 (by rfl) ⟨1663280, by rfl⟩ : syracuseStep 2217707 = 3326561) B3326561
theorem B18945845 : Blo 2217435 18945845 := bbase (se 5 (by rfl) ⟨888086, by rfl⟩ : syracuseStep 18945845 = 1776173) (by norm_num)
theorem B12630563 : Blo 2217435 12630563 := bstep (se 1 (by rfl) ⟨9472922, by rfl⟩ : syracuseStep 12630563 = 18945845) B18945845
theorem B8420375 : Blo 2217435 8420375 := bstep (se 1 (by rfl) ⟨6315281, by rfl⟩ : syracuseStep 8420375 = 12630563) B12630563
theorem B5613583 : Blo 2217435 5613583 := bstep (se 1 (by rfl) ⟨4210187, by rfl⟩ : syracuseStep 5613583 = 8420375) B8420375
theorem B7484777 : Blo 2217435 7484777 := bstep (se 2 (by rfl) ⟨2806791, by rfl⟩ : syracuseStep 7484777 = 5613583) B5613583
theorem B4989851 : Blo 2217435 4989851 := bstep (se 1 (by rfl) ⟨3742388, by rfl⟩ : syracuseStep 4989851 = 7484777) B7484777
theorem B3326567 : Blo 2217435 3326567 := bstep (se 1 (by rfl) ⟨2494925, by rfl⟩ : syracuseStep 3326567 = 4989851) B4989851
theorem B2217711 : Blo 2217435 2217711 := bstep (se 1 (by rfl) ⟨1663283, by rfl⟩ : syracuseStep 2217711 = 3326567) B3326567
theorem B3326573 : Blo 2217435 3326573 := bbase (se 3 (by rfl) ⟨623732, by rfl⟩ : syracuseStep 3326573 = 1247465) (by norm_num)
theorem B2217715 : Blo 2217435 2217715 := bstep (se 1 (by rfl) ⟨1663286, by rfl⟩ : syracuseStep 2217715 = 3326573) B3326573
theorem B4989869 : Blo 2217435 4989869 := bbase (se 3 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 4989869 = 1871201) (by norm_num)
theorem B3326579 : Blo 2217435 3326579 := bstep (se 1 (by rfl) ⟨2494934, by rfl⟩ : syracuseStep 3326579 = 4989869) B4989869
theorem B2217719 : Blo 2217435 2217719 := bstep (se 1 (by rfl) ⟨1663289, by rfl⟩ : syracuseStep 2217719 = 3326579) B3326579
theorem B6315317 : Blo 2217435 6315317 := bbase (se 5 (by rfl) ⟨296030, by rfl⟩ : syracuseStep 6315317 = 592061) (by norm_num)
theorem B4210211 : Blo 2217435 4210211 := bstep (se 1 (by rfl) ⟨3157658, by rfl⟩ : syracuseStep 4210211 = 6315317) B6315317
theorem B2806807 : Blo 2217435 2806807 := bstep (se 1 (by rfl) ⟨2105105, by rfl⟩ : syracuseStep 2806807 = 4210211) B4210211
theorem B3742409 : Blo 2217435 3742409 := bstep (se 2 (by rfl) ⟨1403403, by rfl⟩ : syracuseStep 3742409 = 2806807) B2806807
theorem B2494939 : Blo 2217435 2494939 := bstep (se 1 (by rfl) ⟨1871204, by rfl⟩ : syracuseStep 2494939 = 3742409) B3742409
theorem B3326585 : Blo 2217435 3326585 := bstep (se 2 (by rfl) ⟨1247469, by rfl⟩ : syracuseStep 3326585 = 2494939) B2494939
theorem B2217723 : Blo 2217435 2217723 := bstep (se 1 (by rfl) ⟨1663292, by rfl⟩ : syracuseStep 2217723 = 3326585) B3326585
theorem B5690213 : Blo 2217435 5690213 := bbase (se 4 (by rfl) ⟨533457, by rfl⟩ : syracuseStep 5690213 = 1066915) (by norm_num)
theorem B3793475 : Blo 2217435 3793475 := bstep (se 1 (by rfl) ⟨2845106, by rfl⟩ : syracuseStep 3793475 = 5690213) B5690213
theorem B10115933 : Blo 2217435 10115933 := bstep (se 3 (by rfl) ⟨1896737, by rfl⟩ : syracuseStep 10115933 = 3793475) B3793475
theorem B107903285 : Blo 2217435 107903285 := bstep (se 5 (by rfl) ⟨5057966, by rfl⟩ : syracuseStep 107903285 = 10115933) B10115933
theorem B71935523 : Blo 2217435 71935523 := bstep (se 1 (by rfl) ⟨53951642, by rfl⟩ : syracuseStep 71935523 = 107903285) B107903285
theorem B47957015 : Blo 2217435 47957015 := bstep (se 1 (by rfl) ⟨35967761, by rfl⟩ : syracuseStep 47957015 = 71935523) B71935523
theorem B31971343 : Blo 2217435 31971343 := bstep (se 1 (by rfl) ⟨23978507, by rfl⟩ : syracuseStep 31971343 = 47957015) B47957015
theorem B42628457 : Blo 2217435 42628457 := bstep (se 2 (by rfl) ⟨15985671, by rfl⟩ : syracuseStep 42628457 = 31971343) B31971343
theorem B28418971 : Blo 2217435 28418971 := bstep (se 1 (by rfl) ⟨21314228, by rfl⟩ : syracuseStep 28418971 = 42628457) B42628457
theorem B37891961 : Blo 2217435 37891961 := bstep (se 2 (by rfl) ⟨14209485, by rfl⟩ : syracuseStep 37891961 = 28418971) B28418971
theorem B25261307 : Blo 2217435 25261307 := bstep (se 1 (by rfl) ⟨18945980, by rfl⟩ : syracuseStep 25261307 = 37891961) B37891961
theorem B16840871 : Blo 2217435 16840871 := bstep (se 1 (by rfl) ⟨12630653, by rfl⟩ : syracuseStep 16840871 = 25261307) B25261307
theorem B11227247 : Blo 2217435 11227247 := bstep (se 1 (by rfl) ⟨8420435, by rfl⟩ : syracuseStep 11227247 = 16840871) B16840871
theorem B7484831 : Blo 2217435 7484831 := bstep (se 1 (by rfl) ⟨5613623, by rfl⟩ : syracuseStep 7484831 = 11227247) B11227247
theorem B4989887 : Blo 2217435 4989887 := bstep (se 1 (by rfl) ⟨3742415, by rfl⟩ : syracuseStep 4989887 = 7484831) B7484831
theorem B3326591 : Blo 2217435 3326591 := bstep (se 1 (by rfl) ⟨2494943, by rfl⟩ : syracuseStep 3326591 = 4989887) B4989887
theorem B2217727 : Blo 2217435 2217727 := bstep (se 1 (by rfl) ⟨1663295, by rfl⟩ : syracuseStep 2217727 = 3326591) B3326591
theorem B3326597 : Blo 2217435 3326597 := bbase (se 4 (by rfl) ⟨311868, by rfl⟩ : syracuseStep 3326597 = 623737) (by norm_num)
theorem B2217731 : Blo 2217435 2217731 := bstep (se 1 (by rfl) ⟨1663298, by rfl⟩ : syracuseStep 2217731 = 3326597) B3326597
theorem B3742429 : Blo 2217435 3742429 := bbase (se 3 (by rfl) ⟨701705, by rfl⟩ : syracuseStep 3742429 = 1403411) (by norm_num)
theorem B4989905 : Blo 2217435 4989905 := bstep (se 2 (by rfl) ⟨1871214, by rfl⟩ : syracuseStep 4989905 = 3742429) B3742429
theorem B3326603 : Blo 2217435 3326603 := bstep (se 1 (by rfl) ⟨2494952, by rfl⟩ : syracuseStep 3326603 = 4989905) B4989905
theorem B2217735 : Blo 2217435 2217735 := bstep (se 1 (by rfl) ⟨1663301, by rfl⟩ : syracuseStep 2217735 = 3326603) B3326603
theorem B2494957 : Blo 2217435 2494957 := bbase (se 3 (by rfl) ⟨467804, by rfl⟩ : syracuseStep 2494957 = 935609) (by norm_num)
theorem B3326609 : Blo 2217435 3326609 := bstep (se 2 (by rfl) ⟨1247478, by rfl⟩ : syracuseStep 3326609 = 2494957) B2494957
theorem B2217739 : Blo 2217435 2217739 := bstep (se 1 (by rfl) ⟨1663304, by rfl⟩ : syracuseStep 2217739 = 3326609) B3326609
theorem B7484885 : Blo 2217435 7484885 := bbase (se 7 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 7484885 = 175427) (by norm_num)
theorem B4989923 : Blo 2217435 4989923 := bstep (se 1 (by rfl) ⟨3742442, by rfl⟩ : syracuseStep 4989923 = 7484885) B7484885
theorem B3326615 : Blo 2217435 3326615 := bstep (se 1 (by rfl) ⟨2494961, by rfl⟩ : syracuseStep 3326615 = 4989923) B4989923
theorem B2217743 : Blo 2217435 2217743 := bstep (se 1 (by rfl) ⟨1663307, by rfl⟩ : syracuseStep 2217743 = 3326615) B3326615
theorem B3326621 : Blo 2217435 3326621 := bbase (se 3 (by rfl) ⟨623741, by rfl⟩ : syracuseStep 3326621 = 1247483) (by norm_num)
theorem B2217747 : Blo 2217435 2217747 := bstep (se 1 (by rfl) ⟨1663310, by rfl⟩ : syracuseStep 2217747 = 3326621) B3326621
theorem B4989941 : Blo 2217435 4989941 := bbase (se 5 (by rfl) ⟨233903, by rfl⟩ : syracuseStep 4989941 = 467807) (by norm_num)
theorem B3326627 : Blo 2217435 3326627 := bstep (se 1 (by rfl) ⟨2494970, by rfl⟩ : syracuseStep 3326627 = 4989941) B4989941
theorem B2217751 : Blo 2217435 2217751 := bstep (se 1 (by rfl) ⟨1663313, by rfl⟩ : syracuseStep 2217751 = 3326627) B3326627
theorem B27344213 : Blo 2217435 27344213 := bbase (se 11 (by rfl) ⟨20027, by rfl⟩ : syracuseStep 27344213 = 40055) (by norm_num)
theorem B18229475 : Blo 2217435 18229475 := bstep (se 1 (by rfl) ⟨13672106, by rfl⟩ : syracuseStep 18229475 = 27344213) B27344213
theorem B48611933 : Blo 2217435 48611933 := bstep (se 3 (by rfl) ⟨9114737, by rfl⟩ : syracuseStep 48611933 = 18229475) B18229475
theorem B32407955 : Blo 2217435 32407955 := bstep (se 1 (by rfl) ⟨24305966, by rfl⟩ : syracuseStep 32407955 = 48611933) B48611933
theorem B21605303 : Blo 2217435 21605303 := bstep (se 1 (by rfl) ⟨16203977, by rfl⟩ : syracuseStep 21605303 = 32407955) B32407955
theorem B57614141 : Blo 2217435 57614141 := bstep (se 3 (by rfl) ⟨10802651, by rfl⟩ : syracuseStep 57614141 = 21605303) B21605303
theorem B38409427 : Blo 2217435 38409427 := bstep (se 1 (by rfl) ⟨28807070, by rfl⟩ : syracuseStep 38409427 = 57614141) B57614141
theorem B51212569 : Blo 2217435 51212569 := bstep (se 2 (by rfl) ⟨19204713, by rfl⟩ : syracuseStep 51212569 = 38409427) B38409427
theorem B68283425 : Blo 2217435 68283425 := bstep (se 2 (by rfl) ⟨25606284, by rfl⟩ : syracuseStep 68283425 = 51212569) B51212569
theorem B45522283 : Blo 2217435 45522283 := bstep (se 1 (by rfl) ⟨34141712, by rfl⟩ : syracuseStep 45522283 = 68283425) B68283425
theorem B60696377 : Blo 2217435 60696377 := bstep (se 2 (by rfl) ⟨22761141, by rfl⟩ : syracuseStep 60696377 = 45522283) B45522283
theorem B40464251 : Blo 2217435 40464251 := bstep (se 1 (by rfl) ⟨30348188, by rfl⟩ : syracuseStep 40464251 = 60696377) B60696377
theorem B26976167 : Blo 2217435 26976167 := bstep (se 1 (by rfl) ⟨20232125, by rfl⟩ : syracuseStep 26976167 = 40464251) B40464251
theorem B17984111 : Blo 2217435 17984111 := bstep (se 1 (by rfl) ⟨13488083, by rfl⟩ : syracuseStep 17984111 = 26976167) B26976167
theorem B47957629 : Blo 2217435 47957629 := bstep (se 3 (by rfl) ⟨8992055, by rfl⟩ : syracuseStep 47957629 = 17984111) B17984111
theorem B63943505 : Blo 2217435 63943505 := bstep (se 2 (by rfl) ⟨23978814, by rfl⟩ : syracuseStep 63943505 = 47957629) B47957629
theorem B42629003 : Blo 2217435 42629003 := bstep (se 1 (by rfl) ⟨31971752, by rfl⟩ : syracuseStep 42629003 = 63943505) B63943505
theorem B28419335 : Blo 2217435 28419335 := bstep (se 1 (by rfl) ⟨21314501, by rfl⟩ : syracuseStep 28419335 = 42629003) B42629003
theorem B18946223 : Blo 2217435 18946223 := bstep (se 1 (by rfl) ⟨14209667, by rfl⟩ : syracuseStep 18946223 = 28419335) B28419335
theorem B12630815 : Blo 2217435 12630815 := bstep (se 1 (by rfl) ⟨9473111, by rfl⟩ : syracuseStep 12630815 = 18946223) B18946223
theorem B8420543 : Blo 2217435 8420543 := bstep (se 1 (by rfl) ⟨6315407, by rfl⟩ : syracuseStep 8420543 = 12630815) B12630815
theorem B5613695 : Blo 2217435 5613695 := bstep (se 1 (by rfl) ⟨4210271, by rfl⟩ : syracuseStep 5613695 = 8420543) B8420543
theorem B3742463 : Blo 2217435 3742463 := bstep (se 1 (by rfl) ⟨2806847, by rfl⟩ : syracuseStep 3742463 = 5613695) B5613695
theorem B2494975 : Blo 2217435 2494975 := bstep (se 1 (by rfl) ⟨1871231, by rfl⟩ : syracuseStep 2494975 = 3742463) B3742463
theorem B3326633 : Blo 2217435 3326633 := bstep (se 2 (by rfl) ⟨1247487, by rfl⟩ : syracuseStep 3326633 = 2494975) B2494975
theorem B2217755 : Blo 2217435 2217755 := bstep (se 1 (by rfl) ⟨1663316, by rfl⟩ : syracuseStep 2217755 = 3326633) B3326633
theorem B3157709 : Blo 2217435 3157709 := bbase (se 3 (by rfl) ⟨592070, by rfl⟩ : syracuseStep 3157709 = 1184141) (by norm_num)
theorem B8420557 : Blo 2217435 8420557 := bstep (se 3 (by rfl) ⟨1578854, by rfl⟩ : syracuseStep 8420557 = 3157709) B3157709
theorem B11227409 : Blo 2217435 11227409 := bstep (se 2 (by rfl) ⟨4210278, by rfl⟩ : syracuseStep 11227409 = 8420557) B8420557
theorem B7484939 : Blo 2217435 7484939 := bstep (se 1 (by rfl) ⟨5613704, by rfl⟩ : syracuseStep 7484939 = 11227409) B11227409
theorem B4989959 : Blo 2217435 4989959 := bstep (se 1 (by rfl) ⟨3742469, by rfl⟩ : syracuseStep 4989959 = 7484939) B7484939
theorem B3326639 : Blo 2217435 3326639 := bstep (se 1 (by rfl) ⟨2494979, by rfl⟩ : syracuseStep 3326639 = 4989959) B4989959
theorem B2217759 : Blo 2217435 2217759 := bstep (se 1 (by rfl) ⟨1663319, by rfl⟩ : syracuseStep 2217759 = 3326639) B3326639
theorem B3326645 : Blo 2217435 3326645 := bbase (se 5 (by rfl) ⟨155936, by rfl⟩ : syracuseStep 3326645 = 311873) (by norm_num)
theorem B2217763 : Blo 2217435 2217763 := bstep (se 1 (by rfl) ⟨1663322, by rfl⟩ : syracuseStep 2217763 = 3326645) B3326645
theorem B5613725 : Blo 2217435 5613725 := bbase (se 3 (by rfl) ⟨1052573, by rfl⟩ : syracuseStep 5613725 = 2105147) (by norm_num)
theorem B3742483 : Blo 2217435 3742483 := bstep (se 1 (by rfl) ⟨2806862, by rfl⟩ : syracuseStep 3742483 = 5613725) B5613725
theorem B4989977 : Blo 2217435 4989977 := bstep (se 2 (by rfl) ⟨1871241, by rfl⟩ : syracuseStep 4989977 = 3742483) B3742483
theorem B3326651 : Blo 2217435 3326651 := bstep (se 1 (by rfl) ⟨2494988, by rfl⟩ : syracuseStep 3326651 = 4989977) B4989977
theorem B2217767 : Blo 2217435 2217767 := bstep (se 1 (by rfl) ⟨1663325, by rfl⟩ : syracuseStep 2217767 = 3326651) B3326651
theorem B2494993 : Blo 2217435 2494993 := bbase (se 2 (by rfl) ⟨935622, by rfl⟩ : syracuseStep 2494993 = 1871245) (by norm_num)
theorem B3326657 : Blo 2217435 3326657 := bstep (se 2 (by rfl) ⟨1247496, by rfl⟩ : syracuseStep 3326657 = 2494993) B2494993
theorem B2217771 : Blo 2217435 2217771 := bstep (se 1 (by rfl) ⟨1663328, by rfl⟩ : syracuseStep 2217771 = 3326657) B3326657
theorem B4210309 : Blo 2217435 4210309 := bbase (se 4 (by rfl) ⟨394716, by rfl⟩ : syracuseStep 4210309 = 789433) (by norm_num)
theorem B5613745 : Blo 2217435 5613745 := bstep (se 2 (by rfl) ⟨2105154, by rfl⟩ : syracuseStep 5613745 = 4210309) B4210309
theorem B7484993 : Blo 2217435 7484993 := bstep (se 2 (by rfl) ⟨2806872, by rfl⟩ : syracuseStep 7484993 = 5613745) B5613745
theorem B4989995 : Blo 2217435 4989995 := bstep (se 1 (by rfl) ⟨3742496, by rfl⟩ : syracuseStep 4989995 = 7484993) B7484993
theorem B3326663 : Blo 2217435 3326663 := bstep (se 1 (by rfl) ⟨2494997, by rfl⟩ : syracuseStep 3326663 = 4989995) B4989995
theorem B2217775 : Blo 2217435 2217775 := bstep (se 1 (by rfl) ⟨1663331, by rfl⟩ : syracuseStep 2217775 = 3326663) B3326663
theorem B3326669 : Blo 2217435 3326669 := bbase (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) (by norm_num)
theorem B2217779 : Blo 2217435 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B4990013 : Blo 2217435 4990013 := bbase (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) (by norm_num)
theorem B3326675 : Blo 2217435 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B2217783 : Blo 2217435 2217783 := bstep (se 1 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 2217783 = 3326675) B3326675
theorem B3742517 : Blo 2217435 3742517 := bbase (se 5 (by rfl) ⟨175430, by rfl⟩ : syracuseStep 3742517 = 350861) (by norm_num)
theorem B2495011 : Blo 2217435 2495011 := bstep (se 1 (by rfl) ⟨1871258, by rfl⟩ : syracuseStep 2495011 = 3742517) B3742517
theorem B3326681 : Blo 2217435 3326681 := bstep (se 2 (by rfl) ⟨1247505, by rfl⟩ : syracuseStep 3326681 = 2495011) B2495011
theorem B2217787 : Blo 2217435 2217787 := bstep (se 1 (by rfl) ⟨1663340, by rfl⟩ : syracuseStep 2217787 = 3326681) B3326681
theorem B6315509 : Blo 2217435 6315509 := bbase (se 5 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 6315509 = 592079) (by norm_num)
theorem B16841357 : Blo 2217435 16841357 := bstep (se 3 (by rfl) ⟨3157754, by rfl⟩ : syracuseStep 16841357 = 6315509) B6315509
theorem B11227571 : Blo 2217435 11227571 := bstep (se 1 (by rfl) ⟨8420678, by rfl⟩ : syracuseStep 11227571 = 16841357) B16841357
theorem B7485047 : Blo 2217435 7485047 := bstep (se 1 (by rfl) ⟨5613785, by rfl⟩ : syracuseStep 7485047 = 11227571) B11227571
theorem B4990031 : Blo 2217435 4990031 := bstep (se 1 (by rfl) ⟨3742523, by rfl⟩ : syracuseStep 4990031 = 7485047) B7485047
theorem B3326687 : Blo 2217435 3326687 := bstep (se 1 (by rfl) ⟨2495015, by rfl⟩ : syracuseStep 3326687 = 4990031) B4990031
theorem B2217791 : Blo 2217435 2217791 := bstep (se 1 (by rfl) ⟨1663343, by rfl⟩ : syracuseStep 2217791 = 3326687) B3326687
theorem B3326693 : Blo 2217435 3326693 := bbase (se 4 (by rfl) ⟨311877, by rfl⟩ : syracuseStep 3326693 = 623755) (by norm_num)
theorem B2217795 : Blo 2217435 2217795 := bstep (se 1 (by rfl) ⟨1663346, by rfl⟩ : syracuseStep 2217795 = 3326693) B3326693
theorem B2368325 : Blo 2217435 2368325 := bbase (se 4 (by rfl) ⟨222030, by rfl⟩ : syracuseStep 2368325 = 444061) (by norm_num)
theorem B6315533 : Blo 2217435 6315533 := bstep (se 3 (by rfl) ⟨1184162, by rfl⟩ : syracuseStep 6315533 = 2368325) B2368325
theorem B4210355 : Blo 2217435 4210355 := bstep (se 1 (by rfl) ⟨3157766, by rfl⟩ : syracuseStep 4210355 = 6315533) B6315533
theorem B2806903 : Blo 2217435 2806903 := bstep (se 1 (by rfl) ⟨2105177, by rfl⟩ : syracuseStep 2806903 = 4210355) B4210355
theorem B3742537 : Blo 2217435 3742537 := bstep (se 2 (by rfl) ⟨1403451, by rfl⟩ : syracuseStep 3742537 = 2806903) B2806903
theorem B4990049 : Blo 2217435 4990049 := bstep (se 2 (by rfl) ⟨1871268, by rfl⟩ : syracuseStep 4990049 = 3742537) B3742537
theorem B3326699 : Blo 2217435 3326699 := bstep (se 1 (by rfl) ⟨2495024, by rfl⟩ : syracuseStep 3326699 = 4990049) B4990049
theorem B2217799 : Blo 2217435 2217799 := bstep (se 1 (by rfl) ⟨1663349, by rfl⟩ : syracuseStep 2217799 = 3326699) B3326699
theorem B2495029 : Blo 2217435 2495029 := bbase (se 5 (by rfl) ⟨116954, by rfl⟩ : syracuseStep 2495029 = 233909) (by norm_num)
theorem B3326705 : Blo 2217435 3326705 := bstep (se 2 (by rfl) ⟨1247514, by rfl⟩ : syracuseStep 3326705 = 2495029) B2495029
theorem B2217803 : Blo 2217435 2217803 := bstep (se 1 (by rfl) ⟨1663352, by rfl⟩ : syracuseStep 2217803 = 3326705) B3326705
theorem B2806913 : Blo 2217435 2806913 := bbase (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) (by norm_num)
theorem B7485101 : Blo 2217435 7485101 := bstep (se 3 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 7485101 = 2806913) B2806913
theorem B4990067 : Blo 2217435 4990067 := bstep (se 1 (by rfl) ⟨3742550, by rfl⟩ : syracuseStep 4990067 = 7485101) B7485101
theorem B3326711 : Blo 2217435 3326711 := bstep (se 1 (by rfl) ⟨2495033, by rfl⟩ : syracuseStep 3326711 = 4990067) B4990067
theorem B2217807 : Blo 2217435 2217807 := bstep (se 1 (by rfl) ⟨1663355, by rfl⟩ : syracuseStep 2217807 = 3326711) B3326711
theorem B3326717 : Blo 2217435 3326717 := bbase (se 3 (by rfl) ⟨623759, by rfl⟩ : syracuseStep 3326717 = 1247519) (by norm_num)
theorem B2217811 : Blo 2217435 2217811 := bstep (se 1 (by rfl) ⟨1663358, by rfl⟩ : syracuseStep 2217811 = 3326717) B3326717
theorem B4990085 : Blo 2217435 4990085 := bbase (se 4 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 4990085 = 935641) (by norm_num)
theorem B3326723 : Blo 2217435 3326723 := bstep (se 1 (by rfl) ⟨2495042, by rfl⟩ : syracuseStep 3326723 = 4990085) B4990085
theorem B2217815 : Blo 2217435 2217815 := bstep (se 1 (by rfl) ⟨1663361, by rfl⟩ : syracuseStep 2217815 = 3326723) B3326723
theorem B4736693 : Blo 2217435 4736693 := bbase (se 5 (by rfl) ⟨222032, by rfl⟩ : syracuseStep 4736693 = 444065) (by norm_num)
theorem B3157795 : Blo 2217435 3157795 := bstep (se 1 (by rfl) ⟨2368346, by rfl⟩ : syracuseStep 3157795 = 4736693) B4736693
theorem B4210393 : Blo 2217435 4210393 := bstep (se 2 (by rfl) ⟨1578897, by rfl⟩ : syracuseStep 4210393 = 3157795) B3157795
theorem B5613857 : Blo 2217435 5613857 := bstep (se 2 (by rfl) ⟨2105196, by rfl⟩ : syracuseStep 5613857 = 4210393) B4210393
theorem B3742571 : Blo 2217435 3742571 := bstep (se 1 (by rfl) ⟨2806928, by rfl⟩ : syracuseStep 3742571 = 5613857) B5613857
theorem B2495047 : Blo 2217435 2495047 := bstep (se 1 (by rfl) ⟨1871285, by rfl⟩ : syracuseStep 2495047 = 3742571) B3742571
theorem B3326729 : Blo 2217435 3326729 := bstep (se 2 (by rfl) ⟨1247523, by rfl⟩ : syracuseStep 3326729 = 2495047) B2495047
theorem B2217819 : Blo 2217435 2217819 := bstep (se 1 (by rfl) ⟨1663364, by rfl⟩ : syracuseStep 2217819 = 3326729) B3326729
theorem B11227733 : Blo 2217435 11227733 := bbase (se 8 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 11227733 = 131575) (by norm_num)
theorem B7485155 : Blo 2217435 7485155 := bstep (se 1 (by rfl) ⟨5613866, by rfl⟩ : syracuseStep 7485155 = 11227733) B11227733
theorem B4990103 : Blo 2217435 4990103 := bstep (se 1 (by rfl) ⟨3742577, by rfl⟩ : syracuseStep 4990103 = 7485155) B7485155
theorem B3326735 : Blo 2217435 3326735 := bstep (se 1 (by rfl) ⟨2495051, by rfl⟩ : syracuseStep 3326735 = 4990103) B4990103
theorem B2217823 : Blo 2217435 2217823 := bstep (se 1 (by rfl) ⟨1663367, by rfl⟩ : syracuseStep 2217823 = 3326735) B3326735
theorem B3326741 : Blo 2217435 3326741 := bbase (se 6 (by rfl) ⟨77970, by rfl⟩ : syracuseStep 3326741 = 155941) (by norm_num)
theorem B2217827 : Blo 2217435 2217827 := bstep (se 1 (by rfl) ⟨1663370, by rfl⟩ : syracuseStep 2217827 = 3326741) B3326741
theorem B3897877 : Blo 2217435 3897877 := bbase (se 6 (by rfl) ⟨91356, by rfl⟩ : syracuseStep 3897877 = 182713) (by norm_num)
theorem B5197169 : Blo 2217435 5197169 := bstep (se 2 (by rfl) ⟨1948938, by rfl⟩ : syracuseStep 5197169 = 3897877) B3897877
theorem B13859117 : Blo 2217435 13859117 := bstep (se 3 (by rfl) ⟨2598584, by rfl⟩ : syracuseStep 13859117 = 5197169) B5197169
theorem B9239411 : Blo 2217435 9239411 := bstep (se 1 (by rfl) ⟨6929558, by rfl⟩ : syracuseStep 9239411 = 13859117) B13859117
theorem B24638429 : Blo 2217435 24638429 := bstep (se 3 (by rfl) ⟨4619705, by rfl⟩ : syracuseStep 24638429 = 9239411) B9239411
theorem B65702477 : Blo 2217435 65702477 := bstep (se 3 (by rfl) ⟨12319214, by rfl⟩ : syracuseStep 65702477 = 24638429) B24638429
theorem B43801651 : Blo 2217435 43801651 := bstep (se 1 (by rfl) ⟨32851238, by rfl⟩ : syracuseStep 43801651 = 65702477) B65702477
theorem B58402201 : Blo 2217435 58402201 := bstep (se 2 (by rfl) ⟨21900825, by rfl⟩ : syracuseStep 58402201 = 43801651) B43801651
theorem B77869601 : Blo 2217435 77869601 := bstep (se 2 (by rfl) ⟨29201100, by rfl⟩ : syracuseStep 77869601 = 58402201) B58402201
theorem B51913067 : Blo 2217435 51913067 := bstep (se 1 (by rfl) ⟨38934800, by rfl⟩ : syracuseStep 51913067 = 77869601) B77869601
theorem B138434845 : Blo 2217435 138434845 := bstep (se 3 (by rfl) ⟨25956533, by rfl⟩ : syracuseStep 138434845 = 51913067) B51913067
theorem B184579793 : Blo 2217435 184579793 := bstep (se 2 (by rfl) ⟨69217422, by rfl⟩ : syracuseStep 184579793 = 138434845) B138434845
theorem B123053195 : Blo 2217435 123053195 := bstep (se 1 (by rfl) ⟨92289896, by rfl⟩ : syracuseStep 123053195 = 184579793) B184579793
theorem B82035463 : Blo 2217435 82035463 := bstep (se 1 (by rfl) ⟨61526597, by rfl⟩ : syracuseStep 82035463 = 123053195) B123053195
theorem B109380617 : Blo 2217435 109380617 := bstep (se 2 (by rfl) ⟨41017731, by rfl⟩ : syracuseStep 109380617 = 82035463) B82035463
theorem B72920411 : Blo 2217435 72920411 := bstep (se 1 (by rfl) ⟨54690308, by rfl⟩ : syracuseStep 72920411 = 109380617) B109380617
theorem B48613607 : Blo 2217435 48613607 := bstep (se 1 (by rfl) ⟨36460205, by rfl⟩ : syracuseStep 48613607 = 72920411) B72920411
theorem B32409071 : Blo 2217435 32409071 := bstep (se 1 (by rfl) ⟨24306803, by rfl⟩ : syracuseStep 32409071 = 48613607) B48613607
theorem B21606047 : Blo 2217435 21606047 := bstep (se 1 (by rfl) ⟨16204535, by rfl⟩ : syracuseStep 21606047 = 32409071) B32409071
theorem B14404031 : Blo 2217435 14404031 := bstep (se 1 (by rfl) ⟨10803023, by rfl⟩ : syracuseStep 14404031 = 21606047) B21606047
theorem B9602687 : Blo 2217435 9602687 := bstep (se 1 (by rfl) ⟨7202015, by rfl⟩ : syracuseStep 9602687 = 14404031) B14404031
theorem B6401791 : Blo 2217435 6401791 := bstep (se 1 (by rfl) ⟨4801343, by rfl⟩ : syracuseStep 6401791 = 9602687) B9602687
theorem B8535721 : Blo 2217435 8535721 := bstep (se 2 (by rfl) ⟨3200895, by rfl⟩ : syracuseStep 8535721 = 6401791) B6401791
theorem B11380961 : Blo 2217435 11380961 := bstep (se 2 (by rfl) ⟨4267860, by rfl⟩ : syracuseStep 11380961 = 8535721) B8535721
theorem B7587307 : Blo 2217435 7587307 := bstep (se 1 (by rfl) ⟨5690480, by rfl⟩ : syracuseStep 7587307 = 11380961) B11380961
theorem B10116409 : Blo 2217435 10116409 := bstep (se 2 (by rfl) ⟨3793653, by rfl⟩ : syracuseStep 10116409 = 7587307) B7587307
theorem B13488545 : Blo 2217435 13488545 := bstep (se 2 (by rfl) ⟨5058204, by rfl⟩ : syracuseStep 13488545 = 10116409) B10116409
theorem B35969453 : Blo 2217435 35969453 := bstep (se 3 (by rfl) ⟨6744272, by rfl⟩ : syracuseStep 35969453 = 13488545) B13488545
theorem B23979635 : Blo 2217435 23979635 := bstep (se 1 (by rfl) ⟨17984726, by rfl⟩ : syracuseStep 23979635 = 35969453) B35969453
theorem B15986423 : Blo 2217435 15986423 := bstep (se 1 (by rfl) ⟨11989817, by rfl⟩ : syracuseStep 15986423 = 23979635) B23979635
theorem B42630461 : Blo 2217435 42630461 := bstep (se 3 (by rfl) ⟨7993211, by rfl⟩ : syracuseStep 42630461 = 15986423) B15986423
theorem B28420307 : Blo 2217435 28420307 := bstep (se 1 (by rfl) ⟨21315230, by rfl⟩ : syracuseStep 28420307 = 42630461) B42630461
theorem B18946871 : Blo 2217435 18946871 := bstep (se 1 (by rfl) ⟨14210153, by rfl⟩ : syracuseStep 18946871 = 28420307) B28420307
theorem B12631247 : Blo 2217435 12631247 := bstep (se 1 (by rfl) ⟨9473435, by rfl⟩ : syracuseStep 12631247 = 18946871) B18946871
theorem B8420831 : Blo 2217435 8420831 := bstep (se 1 (by rfl) ⟨6315623, by rfl⟩ : syracuseStep 8420831 = 12631247) B12631247
theorem B5613887 : Blo 2217435 5613887 := bstep (se 1 (by rfl) ⟨4210415, by rfl⟩ : syracuseStep 5613887 = 8420831) B8420831
theorem B3742591 : Blo 2217435 3742591 := bstep (se 1 (by rfl) ⟨2806943, by rfl⟩ : syracuseStep 3742591 = 5613887) B5613887
theorem B4990121 : Blo 2217435 4990121 := bstep (se 2 (by rfl) ⟨1871295, by rfl⟩ : syracuseStep 4990121 = 3742591) B3742591
theorem B3326747 : Blo 2217435 3326747 := bstep (se 1 (by rfl) ⟨2495060, by rfl⟩ : syracuseStep 3326747 = 4990121) B4990121
theorem B2217831 : Blo 2217435 2217831 := bstep (se 1 (by rfl) ⟨1663373, by rfl⟩ : syracuseStep 2217831 = 3326747) B3326747
theorem B2495065 : Blo 2217435 2495065 := bbase (se 2 (by rfl) ⟨935649, by rfl⟩ : syracuseStep 2495065 = 1871299) (by norm_num)
theorem B3326753 : Blo 2217435 3326753 := bstep (se 2 (by rfl) ⟨1247532, by rfl⟩ : syracuseStep 3326753 = 2495065) B2495065
theorem B2217835 : Blo 2217435 2217835 := bstep (se 1 (by rfl) ⟨1663376, by rfl⟩ : syracuseStep 2217835 = 3326753) B3326753
theorem B3372149 : Blo 2217435 3372149 := bbase (se 5 (by rfl) ⟨158069, by rfl⟩ : syracuseStep 3372149 = 316139) (by norm_num)
theorem B8992397 : Blo 2217435 8992397 := bstep (se 3 (by rfl) ⟨1686074, by rfl⟩ : syracuseStep 8992397 = 3372149) B3372149
theorem B23979725 : Blo 2217435 23979725 := bstep (se 3 (by rfl) ⟨4496198, by rfl⟩ : syracuseStep 23979725 = 8992397) B8992397
theorem B15986483 : Blo 2217435 15986483 := bstep (se 1 (by rfl) ⟨11989862, by rfl⟩ : syracuseStep 15986483 = 23979725) B23979725
theorem B10657655 : Blo 2217435 10657655 := bstep (se 1 (by rfl) ⟨7993241, by rfl⟩ : syracuseStep 10657655 = 15986483) B15986483
theorem B7105103 : Blo 2217435 7105103 := bstep (se 1 (by rfl) ⟨5328827, by rfl⟩ : syracuseStep 7105103 = 10657655) B10657655
theorem B4736735 : Blo 2217435 4736735 := bstep (se 1 (by rfl) ⟨3552551, by rfl⟩ : syracuseStep 4736735 = 7105103) B7105103
theorem B3157823 : Blo 2217435 3157823 := bstep (se 1 (by rfl) ⟨2368367, by rfl⟩ : syracuseStep 3157823 = 4736735) B4736735
theorem B8420861 : Blo 2217435 8420861 := bstep (se 3 (by rfl) ⟨1578911, by rfl⟩ : syracuseStep 8420861 = 3157823) B3157823
theorem B5613907 : Blo 2217435 5613907 := bstep (se 1 (by rfl) ⟨4210430, by rfl⟩ : syracuseStep 5613907 = 8420861) B8420861
theorem B7485209 : Blo 2217435 7485209 := bstep (se 2 (by rfl) ⟨2806953, by rfl⟩ : syracuseStep 7485209 = 5613907) B5613907
theorem B4990139 : Blo 2217435 4990139 := bstep (se 1 (by rfl) ⟨3742604, by rfl⟩ : syracuseStep 4990139 = 7485209) B7485209
theorem B3326759 : Blo 2217435 3326759 := bstep (se 1 (by rfl) ⟨2495069, by rfl⟩ : syracuseStep 3326759 = 4990139) B4990139
theorem B2217839 : Blo 2217435 2217839 := bstep (se 1 (by rfl) ⟨1663379, by rfl⟩ : syracuseStep 2217839 = 3326759) B3326759
theorem B3326765 : Blo 2217435 3326765 := bbase (se 3 (by rfl) ⟨623768, by rfl⟩ : syracuseStep 3326765 = 1247537) (by norm_num)
theorem B2217843 : Blo 2217435 2217843 := bstep (se 1 (by rfl) ⟨1663382, by rfl⟩ : syracuseStep 2217843 = 3326765) B3326765
theorem B4990157 : Blo 2217435 4990157 := bbase (se 3 (by rfl) ⟨935654, by rfl⟩ : syracuseStep 4990157 = 1871309) (by norm_num)
theorem B3326771 : Blo 2217435 3326771 := bstep (se 1 (by rfl) ⟨2495078, by rfl⟩ : syracuseStep 3326771 = 4990157) B4990157
theorem B2217847 : Blo 2217435 2217847 := bstep (se 1 (by rfl) ⟨1663385, by rfl⟩ : syracuseStep 2217847 = 3326771) B3326771
theorem B2806969 : Blo 2217435 2806969 := bbase (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) (by norm_num)
theorem B3742625 : Blo 2217435 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B2495083 : Blo 2217435 2495083 := bstep (se 1 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 2495083 = 3742625) B3742625
theorem B3326777 : Blo 2217435 3326777 := bstep (se 2 (by rfl) ⟨1247541, by rfl⟩ : syracuseStep 3326777 = 2495083) B2495083
theorem B2217851 : Blo 2217435 2217851 := bstep (se 1 (by rfl) ⟨1663388, by rfl⟩ : syracuseStep 2217851 = 3326777) B3326777
theorem B8102357 : Blo 2217435 8102357 := bbase (se 7 (by rfl) ⟨94949, by rfl⟩ : syracuseStep 8102357 = 189899) (by norm_num)
theorem B5401571 : Blo 2217435 5401571 := bstep (se 1 (by rfl) ⟨4051178, by rfl⟩ : syracuseStep 5401571 = 8102357) B8102357
theorem B57616757 : Blo 2217435 57616757 := bstep (se 5 (by rfl) ⟨2700785, by rfl⟩ : syracuseStep 57616757 = 5401571) B5401571
theorem B38411171 : Blo 2217435 38411171 := bstep (se 1 (by rfl) ⟨28808378, by rfl⟩ : syracuseStep 38411171 = 57616757) B57616757
theorem B25607447 : Blo 2217435 25607447 := bstep (se 1 (by rfl) ⟨19205585, by rfl⟩ : syracuseStep 25607447 = 38411171) B38411171
theorem B17071631 : Blo 2217435 17071631 := bstep (se 1 (by rfl) ⟨12803723, by rfl⟩ : syracuseStep 17071631 = 25607447) B25607447
theorem B11381087 : Blo 2217435 11381087 := bstep (se 1 (by rfl) ⟨8535815, by rfl⟩ : syracuseStep 11381087 = 17071631) B17071631
theorem B7587391 : Blo 2217435 7587391 := bstep (se 1 (by rfl) ⟨5690543, by rfl⟩ : syracuseStep 7587391 = 11381087) B11381087
theorem B10116521 : Blo 2217435 10116521 := bstep (se 2 (by rfl) ⟨3793695, by rfl⟩ : syracuseStep 10116521 = 7587391) B7587391
theorem B6744347 : Blo 2217435 6744347 := bstep (se 1 (by rfl) ⟨5058260, by rfl⟩ : syracuseStep 6744347 = 10116521) B10116521
theorem B4496231 : Blo 2217435 4496231 := bstep (se 1 (by rfl) ⟨3372173, by rfl⟩ : syracuseStep 4496231 = 6744347) B6744347
theorem B2997487 : Blo 2217435 2997487 := bstep (se 1 (by rfl) ⟨2248115, by rfl⟩ : syracuseStep 2997487 = 4496231) B4496231
theorem B3996649 : Blo 2217435 3996649 := bstep (se 2 (by rfl) ⟨1498743, by rfl⟩ : syracuseStep 3996649 = 2997487) B2997487
theorem B5328865 : Blo 2217435 5328865 := bstep (se 2 (by rfl) ⟨1998324, by rfl⟩ : syracuseStep 5328865 = 3996649) B3996649
theorem B7105153 : Blo 2217435 7105153 := bstep (se 2 (by rfl) ⟨2664432, by rfl⟩ : syracuseStep 7105153 = 5328865) B5328865
theorem B9473537 : Blo 2217435 9473537 := bstep (se 2 (by rfl) ⟨3552576, by rfl⟩ : syracuseStep 9473537 = 7105153) B7105153
theorem B25262765 : Blo 2217435 25262765 := bstep (se 3 (by rfl) ⟨4736768, by rfl⟩ : syracuseStep 25262765 = 9473537) B9473537
theorem B16841843 : Blo 2217435 16841843 := bstep (se 1 (by rfl) ⟨12631382, by rfl⟩ : syracuseStep 16841843 = 25262765) B25262765
theorem B11227895 : Blo 2217435 11227895 := bstep (se 1 (by rfl) ⟨8420921, by rfl⟩ : syracuseStep 11227895 = 16841843) B16841843
theorem B7485263 : Blo 2217435 7485263 := bstep (se 1 (by rfl) ⟨5613947, by rfl⟩ : syracuseStep 7485263 = 11227895) B11227895
theorem B4990175 : Blo 2217435 4990175 := bstep (se 1 (by rfl) ⟨3742631, by rfl⟩ : syracuseStep 4990175 = 7485263) B7485263
theorem B3326783 : Blo 2217435 3326783 := bstep (se 1 (by rfl) ⟨2495087, by rfl⟩ : syracuseStep 3326783 = 4990175) B4990175
theorem B2217855 : Blo 2217435 2217855 := bstep (se 1 (by rfl) ⟨1663391, by rfl⟩ : syracuseStep 2217855 = 3326783) B3326783
theorem B3326789 : Blo 2217435 3326789 := bbase (se 4 (by rfl) ⟨311886, by rfl⟩ : syracuseStep 3326789 = 623773) (by norm_num)
theorem B2217859 : Blo 2217435 2217859 := bstep (se 1 (by rfl) ⟨1663394, by rfl⟩ : syracuseStep 2217859 = 3326789) B3326789
theorem B3742645 : Blo 2217435 3742645 := bbase (se 5 (by rfl) ⟨175436, by rfl⟩ : syracuseStep 3742645 = 350873) (by norm_num)
theorem B4990193 : Blo 2217435 4990193 := bstep (se 2 (by rfl) ⟨1871322, by rfl⟩ : syracuseStep 4990193 = 3742645) B3742645
theorem B3326795 : Blo 2217435 3326795 := bstep (se 1 (by rfl) ⟨2495096, by rfl⟩ : syracuseStep 3326795 = 4990193) B4990193
theorem B2217863 : Blo 2217435 2217863 := bstep (se 1 (by rfl) ⟨1663397, by rfl⟩ : syracuseStep 2217863 = 3326795) B3326795
theorem B2495101 : Blo 2217435 2495101 := bbase (se 3 (by rfl) ⟨467831, by rfl⟩ : syracuseStep 2495101 = 935663) (by norm_num)
theorem B3326801 : Blo 2217435 3326801 := bstep (se 2 (by rfl) ⟨1247550, by rfl⟩ : syracuseStep 3326801 = 2495101) B2495101
theorem B2217867 : Blo 2217435 2217867 := bstep (se 1 (by rfl) ⟨1663400, by rfl⟩ : syracuseStep 2217867 = 3326801) B3326801
theorem B7485317 : Blo 2217435 7485317 := bbase (se 4 (by rfl) ⟨701748, by rfl⟩ : syracuseStep 7485317 = 1403497) (by norm_num)
theorem B4990211 : Blo 2217435 4990211 := bstep (se 1 (by rfl) ⟨3742658, by rfl⟩ : syracuseStep 4990211 = 7485317) B7485317
theorem B3326807 : Blo 2217435 3326807 := bstep (se 1 (by rfl) ⟨2495105, by rfl⟩ : syracuseStep 3326807 = 4990211) B4990211
theorem B2217871 : Blo 2217435 2217871 := bstep (se 1 (by rfl) ⟨1663403, by rfl⟩ : syracuseStep 2217871 = 3326807) B3326807
theorem B3326813 : Blo 2217435 3326813 := bbase (se 3 (by rfl) ⟨623777, by rfl⟩ : syracuseStep 3326813 = 1247555) (by norm_num)
theorem B2217875 : Blo 2217435 2217875 := bstep (se 1 (by rfl) ⟨1663406, by rfl⟩ : syracuseStep 2217875 = 3326813) B3326813
theorem B4990229 : Blo 2217435 4990229 := bbase (se 6 (by rfl) ⟨116958, by rfl⟩ : syracuseStep 4990229 = 233917) (by norm_num)
theorem B3326819 : Blo 2217435 3326819 := bstep (se 1 (by rfl) ⟨2495114, by rfl⟩ : syracuseStep 3326819 = 4990229) B4990229
theorem B2217879 : Blo 2217435 2217879 := bstep (se 1 (by rfl) ⟨1663409, by rfl⟩ : syracuseStep 2217879 = 3326819) B3326819
theorem B8421029 : Blo 2217435 8421029 := bbase (se 4 (by rfl) ⟨789471, by rfl⟩ : syracuseStep 8421029 = 1578943) (by norm_num)
theorem B5614019 : Blo 2217435 5614019 := bstep (se 1 (by rfl) ⟨4210514, by rfl⟩ : syracuseStep 5614019 = 8421029) B8421029
theorem B3742679 : Blo 2217435 3742679 := bstep (se 1 (by rfl) ⟨2807009, by rfl⟩ : syracuseStep 3742679 = 5614019) B5614019
theorem B2495119 : Blo 2217435 2495119 := bstep (se 1 (by rfl) ⟨1871339, by rfl⟩ : syracuseStep 2495119 = 3742679) B3742679
theorem B3326825 : Blo 2217435 3326825 := bstep (se 2 (by rfl) ⟨1247559, by rfl⟩ : syracuseStep 3326825 = 2495119) B2495119
theorem B2217883 : Blo 2217435 2217883 := bstep (se 1 (by rfl) ⟨1663412, by rfl⟩ : syracuseStep 2217883 = 3326825) B3326825
theorem B4736837 : Blo 2217435 4736837 := bbase (se 4 (by rfl) ⟨444078, by rfl⟩ : syracuseStep 4736837 = 888157) (by norm_num)
theorem B12631565 : Blo 2217435 12631565 := bstep (se 3 (by rfl) ⟨2368418, by rfl⟩ : syracuseStep 12631565 = 4736837) B4736837
theorem B8421043 : Blo 2217435 8421043 := bstep (se 1 (by rfl) ⟨6315782, by rfl⟩ : syracuseStep 8421043 = 12631565) B12631565
theorem B11228057 : Blo 2217435 11228057 := bstep (se 2 (by rfl) ⟨4210521, by rfl⟩ : syracuseStep 11228057 = 8421043) B8421043
theorem B7485371 : Blo 2217435 7485371 := bstep (se 1 (by rfl) ⟨5614028, by rfl⟩ : syracuseStep 7485371 = 11228057) B11228057
theorem B4990247 : Blo 2217435 4990247 := bstep (se 1 (by rfl) ⟨3742685, by rfl⟩ : syracuseStep 4990247 = 7485371) B7485371
theorem B3326831 : Blo 2217435 3326831 := bstep (se 1 (by rfl) ⟨2495123, by rfl⟩ : syracuseStep 3326831 = 4990247) B4990247
theorem B2217887 : Blo 2217435 2217887 := bstep (se 1 (by rfl) ⟨1663415, by rfl⟩ : syracuseStep 2217887 = 3326831) B3326831
theorem B3326837 : Blo 2217435 3326837 := bbase (se 5 (by rfl) ⟨155945, by rfl⟩ : syracuseStep 3326837 = 311891) (by norm_num)
theorem B2217891 : Blo 2217435 2217891 := bstep (se 1 (by rfl) ⟨1663418, by rfl⟩ : syracuseStep 2217891 = 3326837) B3326837
theorem B10657925 : Blo 2217435 10657925 := bbase (se 4 (by rfl) ⟨999180, by rfl⟩ : syracuseStep 10657925 = 1998361) (by norm_num)
theorem B7105283 : Blo 2217435 7105283 := bstep (se 1 (by rfl) ⟨5328962, by rfl⟩ : syracuseStep 7105283 = 10657925) B10657925
theorem B4736855 : Blo 2217435 4736855 := bstep (se 1 (by rfl) ⟨3552641, by rfl⟩ : syracuseStep 4736855 = 7105283) B7105283
theorem B3157903 : Blo 2217435 3157903 := bstep (se 1 (by rfl) ⟨2368427, by rfl⟩ : syracuseStep 3157903 = 4736855) B4736855
theorem B4210537 : Blo 2217435 4210537 := bstep (se 2 (by rfl) ⟨1578951, by rfl⟩ : syracuseStep 4210537 = 3157903) B3157903
theorem B5614049 : Blo 2217435 5614049 := bstep (se 2 (by rfl) ⟨2105268, by rfl⟩ : syracuseStep 5614049 = 4210537) B4210537
theorem B3742699 : Blo 2217435 3742699 := bstep (se 1 (by rfl) ⟨2807024, by rfl⟩ : syracuseStep 3742699 = 5614049) B5614049
theorem B4990265 : Blo 2217435 4990265 := bstep (se 2 (by rfl) ⟨1871349, by rfl⟩ : syracuseStep 4990265 = 3742699) B3742699
theorem B3326843 : Blo 2217435 3326843 := bstep (se 1 (by rfl) ⟨2495132, by rfl⟩ : syracuseStep 3326843 = 4990265) B4990265
theorem B2217895 : Blo 2217435 2217895 := bstep (se 1 (by rfl) ⟨1663421, by rfl⟩ : syracuseStep 2217895 = 3326843) B3326843
theorem B2495137 : Blo 2217435 2495137 := bbase (se 2 (by rfl) ⟨935676, by rfl⟩ : syracuseStep 2495137 = 1871353) (by norm_num)
theorem B3326849 : Blo 2217435 3326849 := bstep (se 2 (by rfl) ⟨1247568, by rfl⟩ : syracuseStep 3326849 = 2495137) B2495137
theorem B2217899 : Blo 2217435 2217899 := bstep (se 1 (by rfl) ⟨1663424, by rfl⟩ : syracuseStep 2217899 = 3326849) B3326849
theorem B5614069 : Blo 2217435 5614069 := bbase (se 5 (by rfl) ⟨263159, by rfl⟩ : syracuseStep 5614069 = 526319) (by norm_num)
theorem B7485425 : Blo 2217435 7485425 := bstep (se 2 (by rfl) ⟨2807034, by rfl⟩ : syracuseStep 7485425 = 5614069) B5614069
theorem B4990283 : Blo 2217435 4990283 := bstep (se 1 (by rfl) ⟨3742712, by rfl⟩ : syracuseStep 4990283 = 7485425) B7485425
theorem B3326855 : Blo 2217435 3326855 := bstep (se 1 (by rfl) ⟨2495141, by rfl⟩ : syracuseStep 3326855 = 4990283) B4990283
theorem B2217903 : Blo 2217435 2217903 := bstep (se 1 (by rfl) ⟨1663427, by rfl⟩ : syracuseStep 2217903 = 3326855) B3326855
theorem B3326861 : Blo 2217435 3326861 := bbase (se 3 (by rfl) ⟨623786, by rfl⟩ : syracuseStep 3326861 = 1247573) (by norm_num)
theorem B2217907 : Blo 2217435 2217907 := bstep (se 1 (by rfl) ⟨1663430, by rfl⟩ : syracuseStep 2217907 = 3326861) B3326861
theorem B4990301 : Blo 2217435 4990301 := bbase (se 3 (by rfl) ⟨935681, by rfl⟩ : syracuseStep 4990301 = 1871363) (by norm_num)
theorem B3326867 : Blo 2217435 3326867 := bstep (se 1 (by rfl) ⟨2495150, by rfl⟩ : syracuseStep 3326867 = 4990301) B4990301
theorem B2217911 : Blo 2217435 2217911 := bstep (se 1 (by rfl) ⟨1663433, by rfl⟩ : syracuseStep 2217911 = 3326867) B3326867
theorem B3742733 : Blo 2217435 3742733 := bbase (se 3 (by rfl) ⟨701762, by rfl⟩ : syracuseStep 3742733 = 1403525) (by norm_num)
theorem B2495155 : Blo 2217435 2495155 := bstep (se 1 (by rfl) ⟨1871366, by rfl⟩ : syracuseStep 2495155 = 3742733) B3742733
theorem B3326873 : Blo 2217435 3326873 := bstep (se 2 (by rfl) ⟨1247577, by rfl⟩ : syracuseStep 3326873 = 2495155) B2495155
theorem B2217915 : Blo 2217435 2217915 := bstep (se 1 (by rfl) ⟨1663436, by rfl⟩ : syracuseStep 2217915 = 3326873) B3326873
theorem B3793805 : Blo 2217435 3793805 := bbase (se 3 (by rfl) ⟨711338, by rfl⟩ : syracuseStep 3793805 = 1422677) (by norm_num)
theorem B2529203 : Blo 2217435 2529203 := bstep (se 1 (by rfl) ⟨1896902, by rfl⟩ : syracuseStep 2529203 = 3793805) B3793805
theorem B6744541 : Blo 2217435 6744541 := bstep (se 3 (by rfl) ⟨1264601, by rfl⟩ : syracuseStep 6744541 = 2529203) B2529203
theorem B8992721 : Blo 2217435 8992721 := bstep (se 2 (by rfl) ⟨3372270, by rfl⟩ : syracuseStep 8992721 = 6744541) B6744541
theorem B5995147 : Blo 2217435 5995147 := bstep (se 1 (by rfl) ⟨4496360, by rfl⟩ : syracuseStep 5995147 = 8992721) B8992721
theorem B7993529 : Blo 2217435 7993529 := bstep (se 2 (by rfl) ⟨2997573, by rfl⟩ : syracuseStep 7993529 = 5995147) B5995147
theorem B5329019 : Blo 2217435 5329019 := bstep (se 1 (by rfl) ⟨3996764, by rfl⟩ : syracuseStep 5329019 = 7993529) B7993529
theorem B3552679 : Blo 2217435 3552679 := bstep (se 1 (by rfl) ⟨2664509, by rfl⟩ : syracuseStep 3552679 = 5329019) B5329019
theorem B18947621 : Blo 2217435 18947621 := bstep (se 4 (by rfl) ⟨1776339, by rfl⟩ : syracuseStep 18947621 = 3552679) B3552679
theorem B12631747 : Blo 2217435 12631747 := bstep (se 1 (by rfl) ⟨9473810, by rfl⟩ : syracuseStep 12631747 = 18947621) B18947621
theorem B16842329 : Blo 2217435 16842329 := bstep (se 2 (by rfl) ⟨6315873, by rfl⟩ : syracuseStep 16842329 = 12631747) B12631747
theorem B11228219 : Blo 2217435 11228219 := bstep (se 1 (by rfl) ⟨8421164, by rfl⟩ : syracuseStep 11228219 = 16842329) B16842329
theorem B7485479 : Blo 2217435 7485479 := bstep (se 1 (by rfl) ⟨5614109, by rfl⟩ : syracuseStep 7485479 = 11228219) B11228219
theorem B4990319 : Blo 2217435 4990319 := bstep (se 1 (by rfl) ⟨3742739, by rfl⟩ : syracuseStep 4990319 = 7485479) B7485479
theorem B3326879 : Blo 2217435 3326879 := bstep (se 1 (by rfl) ⟨2495159, by rfl⟩ : syracuseStep 3326879 = 4990319) B4990319
theorem B2217919 : Blo 2217435 2217919 := bstep (se 1 (by rfl) ⟨1663439, by rfl⟩ : syracuseStep 2217919 = 3326879) B3326879
theorem B3326885 : Blo 2217435 3326885 := bbase (se 4 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 3326885 = 623791) (by norm_num)
theorem B2217923 : Blo 2217435 2217923 := bstep (se 1 (by rfl) ⟨1663442, by rfl⟩ : syracuseStep 2217923 = 3326885) B3326885
theorem B2807065 : Blo 2217435 2807065 := bbase (se 2 (by rfl) ⟨1052649, by rfl⟩ : syracuseStep 2807065 = 2105299) (by norm_num)
theorem B3742753 : Blo 2217435 3742753 := bstep (se 2 (by rfl) ⟨1403532, by rfl⟩ : syracuseStep 3742753 = 2807065) B2807065
theorem B4990337 : Blo 2217435 4990337 := bstep (se 2 (by rfl) ⟨1871376, by rfl⟩ : syracuseStep 4990337 = 3742753) B3742753
theorem B3326891 : Blo 2217435 3326891 := bstep (se 1 (by rfl) ⟨2495168, by rfl⟩ : syracuseStep 3326891 = 4990337) B4990337
theorem B2217927 : Blo 2217435 2217927 := bstep (se 1 (by rfl) ⟨1663445, by rfl⟩ : syracuseStep 2217927 = 3326891) B3326891
theorem B2495173 : Blo 2217435 2495173 := bbase (se 4 (by rfl) ⟨233922, by rfl⟩ : syracuseStep 2495173 = 467845) (by norm_num)
theorem B3326897 : Blo 2217435 3326897 := bstep (se 2 (by rfl) ⟨1247586, by rfl⟩ : syracuseStep 3326897 = 2495173) B2495173
theorem B2217931 : Blo 2217435 2217931 := bstep (se 1 (by rfl) ⟨1663448, by rfl⟩ : syracuseStep 2217931 = 3326897) B3326897
theorem B4210613 : Blo 2217435 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B2807075 : Blo 2217435 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B7485533 : Blo 2217435 7485533 := bstep (se 3 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 7485533 = 2807075) B2807075
theorem B4990355 : Blo 2217435 4990355 := bstep (se 1 (by rfl) ⟨3742766, by rfl⟩ : syracuseStep 4990355 = 7485533) B7485533
theorem B3326903 : Blo 2217435 3326903 := bstep (se 1 (by rfl) ⟨2495177, by rfl⟩ : syracuseStep 3326903 = 4990355) B4990355
theorem B2217935 : Blo 2217435 2217935 := bstep (se 1 (by rfl) ⟨1663451, by rfl⟩ : syracuseStep 2217935 = 3326903) B3326903
theorem B3326909 : Blo 2217435 3326909 := bbase (se 3 (by rfl) ⟨623795, by rfl⟩ : syracuseStep 3326909 = 1247591) (by norm_num)
theorem B2217939 : Blo 2217435 2217939 := bstep (se 1 (by rfl) ⟨1663454, by rfl⟩ : syracuseStep 2217939 = 3326909) B3326909
theorem B4990373 : Blo 2217435 4990373 := bbase (se 4 (by rfl) ⟨467847, by rfl⟩ : syracuseStep 4990373 = 935695) (by norm_num)
theorem B3326915 : Blo 2217435 3326915 := bstep (se 1 (by rfl) ⟨2495186, by rfl⟩ : syracuseStep 3326915 = 4990373) B4990373
theorem B2217943 : Blo 2217435 2217943 := bstep (se 1 (by rfl) ⟨1663457, by rfl⟩ : syracuseStep 2217943 = 3326915) B3326915
theorem B5614181 : Blo 2217435 5614181 := bbase (se 4 (by rfl) ⟨526329, by rfl⟩ : syracuseStep 5614181 = 1052659) (by norm_num)
theorem B3742787 : Blo 2217435 3742787 := bstep (se 1 (by rfl) ⟨2807090, by rfl⟩ : syracuseStep 3742787 = 5614181) B5614181
theorem B2495191 : Blo 2217435 2495191 := bstep (se 1 (by rfl) ⟨1871393, by rfl⟩ : syracuseStep 2495191 = 3742787) B3742787
theorem B3326921 : Blo 2217435 3326921 := bstep (se 2 (by rfl) ⟨1247595, by rfl⟩ : syracuseStep 3326921 = 2495191) B2495191
theorem B2217947 : Blo 2217435 2217947 := bstep (se 1 (by rfl) ⟨1663460, by rfl⟩ : syracuseStep 2217947 = 3326921) B3326921
theorem B8992853 : Blo 2217435 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B5995235 : Blo 2217435 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B3996823 : Blo 2217435 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B5329097 : Blo 2217435 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B3552731 : Blo 2217435 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B2368487 : Blo 2217435 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B6315965 : Blo 2217435 6315965 := bstep (se 3 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 6315965 = 2368487) B2368487
theorem B4210643 : Blo 2217435 4210643 := bstep (se 1 (by rfl) ⟨3157982, by rfl⟩ : syracuseStep 4210643 = 6315965) B6315965
theorem B11228381 : Blo 2217435 11228381 := bstep (se 3 (by rfl) ⟨2105321, by rfl⟩ : syracuseStep 11228381 = 4210643) B4210643
theorem B7485587 : Blo 2217435 7485587 := bstep (se 1 (by rfl) ⟨5614190, by rfl⟩ : syracuseStep 7485587 = 11228381) B11228381
theorem B4990391 : Blo 2217435 4990391 := bstep (se 1 (by rfl) ⟨3742793, by rfl⟩ : syracuseStep 4990391 = 7485587) B7485587
theorem B3326927 : Blo 2217435 3326927 := bstep (se 1 (by rfl) ⟨2495195, by rfl⟩ : syracuseStep 3326927 = 4990391) B4990391
theorem B2217951 : Blo 2217435 2217951 := bstep (se 1 (by rfl) ⟨1663463, by rfl⟩ : syracuseStep 2217951 = 3326927) B3326927
theorem B3326933 : Blo 2217435 3326933 := bbase (se 7 (by rfl) ⟨38987, by rfl⟩ : syracuseStep 3326933 = 77975) (by norm_num)
theorem B2217955 : Blo 2217435 2217955 := bstep (se 1 (by rfl) ⟨1663466, by rfl⟩ : syracuseStep 2217955 = 3326933) B3326933
theorem B8421317 : Blo 2217435 8421317 := bbase (se 4 (by rfl) ⟨789498, by rfl⟩ : syracuseStep 8421317 = 1578997) (by norm_num)
theorem B5614211 : Blo 2217435 5614211 := bstep (se 1 (by rfl) ⟨4210658, by rfl⟩ : syracuseStep 5614211 = 8421317) B8421317
theorem B3742807 : Blo 2217435 3742807 := bstep (se 1 (by rfl) ⟨2807105, by rfl⟩ : syracuseStep 3742807 = 5614211) B5614211
theorem B4990409 : Blo 2217435 4990409 := bstep (se 2 (by rfl) ⟨1871403, by rfl⟩ : syracuseStep 4990409 = 3742807) B3742807
theorem B3326939 : Blo 2217435 3326939 := bstep (se 1 (by rfl) ⟨2495204, by rfl⟩ : syracuseStep 3326939 = 4990409) B4990409
theorem B2217959 : Blo 2217435 2217959 := bstep (se 1 (by rfl) ⟨1663469, by rfl⟩ : syracuseStep 2217959 = 3326939) B3326939
theorem B2495209 : Blo 2217435 2495209 := bbase (se 2 (by rfl) ⟨935703, by rfl⟩ : syracuseStep 2495209 = 1871407) (by norm_num)
theorem B3326945 : Blo 2217435 3326945 := bstep (se 2 (by rfl) ⟨1247604, by rfl⟩ : syracuseStep 3326945 = 2495209) B2495209
theorem B2217963 : Blo 2217435 2217963 := bstep (se 1 (by rfl) ⟨1663472, by rfl⟩ : syracuseStep 2217963 = 3326945) B3326945
theorem B12632021 : Blo 2217435 12632021 := bbase (se 7 (by rfl) ⟨148031, by rfl⟩ : syracuseStep 12632021 = 296063) (by norm_num)
theorem B8421347 : Blo 2217435 8421347 := bstep (se 1 (by rfl) ⟨6316010, by rfl⟩ : syracuseStep 8421347 = 12632021) B12632021
theorem B5614231 : Blo 2217435 5614231 := bstep (se 1 (by rfl) ⟨4210673, by rfl⟩ : syracuseStep 5614231 = 8421347) B8421347
theorem B7485641 : Blo 2217435 7485641 := bstep (se 2 (by rfl) ⟨2807115, by rfl⟩ : syracuseStep 7485641 = 5614231) B5614231
theorem B4990427 : Blo 2217435 4990427 := bstep (se 1 (by rfl) ⟨3742820, by rfl⟩ : syracuseStep 4990427 = 7485641) B7485641
theorem B3326951 : Blo 2217435 3326951 := bstep (se 1 (by rfl) ⟨2495213, by rfl⟩ : syracuseStep 3326951 = 4990427) B4990427
theorem B2217967 : Blo 2217435 2217967 := bstep (se 1 (by rfl) ⟨1663475, by rfl⟩ : syracuseStep 2217967 = 3326951) B3326951
theorem B3326957 : Blo 2217435 3326957 := bbase (se 3 (by rfl) ⟨623804, by rfl⟩ : syracuseStep 3326957 = 1247609) (by norm_num)
theorem B2217971 : Blo 2217435 2217971 := bstep (se 1 (by rfl) ⟨1663478, by rfl⟩ : syracuseStep 2217971 = 3326957) B3326957
theorem B4990445 : Blo 2217435 4990445 := bbase (se 3 (by rfl) ⟨935708, by rfl⟩ : syracuseStep 4990445 = 1871417) (by norm_num)
theorem B3326963 : Blo 2217435 3326963 := bstep (se 1 (by rfl) ⟨2495222, by rfl⟩ : syracuseStep 3326963 = 4990445) B4990445
theorem B2217975 : Blo 2217435 2217975 := bstep (se 1 (by rfl) ⟨1663481, by rfl⟩ : syracuseStep 2217975 = 3326963) B3326963
theorem B5329165 : Blo 2217435 5329165 := bbase (se 3 (by rfl) ⟨999218, by rfl⟩ : syracuseStep 5329165 = 1998437) (by norm_num)
theorem B7105553 : Blo 2217435 7105553 := bstep (se 2 (by rfl) ⟨2664582, by rfl⟩ : syracuseStep 7105553 = 5329165) B5329165
theorem B4737035 : Blo 2217435 4737035 := bstep (se 1 (by rfl) ⟨3552776, by rfl⟩ : syracuseStep 4737035 = 7105553) B7105553
theorem B3158023 : Blo 2217435 3158023 := bstep (se 1 (by rfl) ⟨2368517, by rfl⟩ : syracuseStep 3158023 = 4737035) B4737035
theorem B4210697 : Blo 2217435 4210697 := bstep (se 2 (by rfl) ⟨1579011, by rfl⟩ : syracuseStep 4210697 = 3158023) B3158023
theorem B2807131 : Blo 2217435 2807131 := bstep (se 1 (by rfl) ⟨2105348, by rfl⟩ : syracuseStep 2807131 = 4210697) B4210697
theorem B3742841 : Blo 2217435 3742841 := bstep (se 2 (by rfl) ⟨1403565, by rfl⟩ : syracuseStep 3742841 = 2807131) B2807131
theorem B2495227 : Blo 2217435 2495227 := bstep (se 1 (by rfl) ⟨1871420, by rfl⟩ : syracuseStep 2495227 = 3742841) B3742841
theorem B3326969 : Blo 2217435 3326969 := bstep (se 2 (by rfl) ⟨1247613, by rfl⟩ : syracuseStep 3326969 = 2495227) B2495227
theorem B2217979 : Blo 2217435 2217979 := bstep (se 1 (by rfl) ⟨1663484, by rfl⟩ : syracuseStep 2217979 = 3326969) B3326969
theorem B22763477 : Blo 2217435 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B60702605 : Blo 2217435 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B40468403 : Blo 2217435 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B26978935 : Blo 2217435 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B35971913 : Blo 2217435 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B23981275 : Blo 2217435 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B127900133 : Blo 2217435 127900133 := bstep (se 4 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 127900133 = 23981275) B23981275
theorem B85266755 : Blo 2217435 85266755 := bstep (se 1 (by rfl) ⟨63950066, by rfl⟩ : syracuseStep 85266755 = 127900133) B127900133
theorem B56844503 : Blo 2217435 56844503 := bstep (se 1 (by rfl) ⟨42633377, by rfl⟩ : syracuseStep 56844503 = 85266755) B85266755
theorem B37896335 : Blo 2217435 37896335 := bstep (se 1 (by rfl) ⟨28422251, by rfl⟩ : syracuseStep 37896335 = 56844503) B56844503
theorem B25264223 : Blo 2217435 25264223 := bstep (se 1 (by rfl) ⟨18948167, by rfl⟩ : syracuseStep 25264223 = 37896335) B37896335
theorem B16842815 : Blo 2217435 16842815 := bstep (se 1 (by rfl) ⟨12632111, by rfl⟩ : syracuseStep 16842815 = 25264223) B25264223
theorem B11228543 : Blo 2217435 11228543 := bstep (se 1 (by rfl) ⟨8421407, by rfl⟩ : syracuseStep 11228543 = 16842815) B16842815
theorem B7485695 : Blo 2217435 7485695 := bstep (se 1 (by rfl) ⟨5614271, by rfl⟩ : syracuseStep 7485695 = 11228543) B11228543
theorem B4990463 : Blo 2217435 4990463 := bstep (se 1 (by rfl) ⟨3742847, by rfl⟩ : syracuseStep 4990463 = 7485695) B7485695
theorem B3326975 : Blo 2217435 3326975 := bstep (se 1 (by rfl) ⟨2495231, by rfl⟩ : syracuseStep 3326975 = 4990463) B4990463
theorem B2217983 : Blo 2217435 2217983 := bstep (se 1 (by rfl) ⟨1663487, by rfl⟩ : syracuseStep 2217983 = 3326975) B3326975
theorem B3326981 : Blo 2217435 3326981 := bbase (se 4 (by rfl) ⟨311904, by rfl⟩ : syracuseStep 3326981 = 623809) (by norm_num)
theorem B2217987 : Blo 2217435 2217987 := bstep (se 1 (by rfl) ⟨1663490, by rfl⟩ : syracuseStep 2217987 = 3326981) B3326981
theorem B3742861 : Blo 2217435 3742861 := bbase (se 3 (by rfl) ⟨701786, by rfl⟩ : syracuseStep 3742861 = 1403573) (by norm_num)
theorem B4990481 : Blo 2217435 4990481 := bstep (se 2 (by rfl) ⟨1871430, by rfl⟩ : syracuseStep 4990481 = 3742861) B3742861
theorem B3326987 : Blo 2217435 3326987 := bstep (se 1 (by rfl) ⟨2495240, by rfl⟩ : syracuseStep 3326987 = 4990481) B4990481
theorem B2217991 : Blo 2217435 2217991 := bstep (se 1 (by rfl) ⟨1663493, by rfl⟩ : syracuseStep 2217991 = 3326987) B3326987
theorem B2495245 : Blo 2217435 2495245 := bbase (se 3 (by rfl) ⟨467858, by rfl⟩ : syracuseStep 2495245 = 935717) (by norm_num)
theorem B3326993 : Blo 2217435 3326993 := bstep (se 2 (by rfl) ⟨1247622, by rfl⟩ : syracuseStep 3326993 = 2495245) B2495245
theorem B2217995 : Blo 2217435 2217995 := bstep (se 1 (by rfl) ⟨1663496, by rfl⟩ : syracuseStep 2217995 = 3326993) B3326993
theorem B7485749 : Blo 2217435 7485749 := bbase (se 5 (by rfl) ⟨350894, by rfl⟩ : syracuseStep 7485749 = 701789) (by norm_num)
theorem B4990499 : Blo 2217435 4990499 := bstep (se 1 (by rfl) ⟨3742874, by rfl⟩ : syracuseStep 4990499 = 7485749) B7485749
theorem B3326999 : Blo 2217435 3326999 := bstep (se 1 (by rfl) ⟨2495249, by rfl⟩ : syracuseStep 3326999 = 4990499) B4990499
theorem B2217999 : Blo 2217435 2217999 := bstep (se 1 (by rfl) ⟨1663499, by rfl⟩ : syracuseStep 2217999 = 3326999) B3326999
theorem B3327005 : Blo 2217435 3327005 := bbase (se 3 (by rfl) ⟨623813, by rfl⟩ : syracuseStep 3327005 = 1247627) (by norm_num)
theorem B2218003 : Blo 2217435 2218003 := bstep (se 1 (by rfl) ⟨1663502, by rfl⟩ : syracuseStep 2218003 = 3327005) B3327005
theorem B4990517 : Blo 2217435 4990517 := bbase (se 5 (by rfl) ⟨233930, by rfl⟩ : syracuseStep 4990517 = 467861) (by norm_num)
theorem B3327011 : Blo 2217435 3327011 := bstep (se 1 (by rfl) ⟨2495258, by rfl⟩ : syracuseStep 3327011 = 4990517) B4990517
theorem B2218007 : Blo 2217435 2218007 := bstep (se 1 (by rfl) ⟨1663505, by rfl⟩ : syracuseStep 2218007 = 3327011) B3327011
theorem B5995397 : Blo 2217435 5995397 := bbase (se 4 (by rfl) ⟨562068, by rfl⟩ : syracuseStep 5995397 = 1124137) (by norm_num)
theorem B3996931 : Blo 2217435 3996931 := bstep (se 1 (by rfl) ⟨2997698, by rfl⟩ : syracuseStep 3996931 = 5995397) B5995397
theorem B5329241 : Blo 2217435 5329241 := bstep (se 2 (by rfl) ⟨1998465, by rfl⟩ : syracuseStep 5329241 = 3996931) B3996931
theorem B3552827 : Blo 2217435 3552827 := bstep (se 1 (by rfl) ⟨2664620, by rfl⟩ : syracuseStep 3552827 = 5329241) B5329241
theorem B9474205 : Blo 2217435 9474205 := bstep (se 3 (by rfl) ⟨1776413, by rfl⟩ : syracuseStep 9474205 = 3552827) B3552827
theorem B12632273 : Blo 2217435 12632273 := bstep (se 2 (by rfl) ⟨4737102, by rfl⟩ : syracuseStep 12632273 = 9474205) B9474205
theorem B8421515 : Blo 2217435 8421515 := bstep (se 1 (by rfl) ⟨6316136, by rfl⟩ : syracuseStep 8421515 = 12632273) B12632273
theorem B5614343 : Blo 2217435 5614343 := bstep (se 1 (by rfl) ⟨4210757, by rfl⟩ : syracuseStep 5614343 = 8421515) B8421515
theorem B3742895 : Blo 2217435 3742895 := bstep (se 1 (by rfl) ⟨2807171, by rfl⟩ : syracuseStep 3742895 = 5614343) B5614343
theorem B2495263 : Blo 2217435 2495263 := bstep (se 1 (by rfl) ⟨1871447, by rfl⟩ : syracuseStep 2495263 = 3742895) B3742895
theorem B3327017 : Blo 2217435 3327017 := bstep (se 2 (by rfl) ⟨1247631, by rfl⟩ : syracuseStep 3327017 = 2495263) B2495263
theorem B2218011 : Blo 2217435 2218011 := bstep (se 1 (by rfl) ⟨1663508, by rfl⟩ : syracuseStep 2218011 = 3327017) B3327017
theorem B2664625 : Blo 2217435 2664625 := bbase (se 2 (by rfl) ⟨999234, by rfl⟩ : syracuseStep 2664625 = 1998469) (by norm_num)
theorem B3552833 : Blo 2217435 3552833 := bstep (se 2 (by rfl) ⟨1332312, by rfl⟩ : syracuseStep 3552833 = 2664625) B2664625
theorem B9474221 : Blo 2217435 9474221 := bstep (se 3 (by rfl) ⟨1776416, by rfl⟩ : syracuseStep 9474221 = 3552833) B3552833
theorem B6316147 : Blo 2217435 6316147 := bstep (se 1 (by rfl) ⟨4737110, by rfl⟩ : syracuseStep 6316147 = 9474221) B9474221
theorem B8421529 : Blo 2217435 8421529 := bstep (se 2 (by rfl) ⟨3158073, by rfl⟩ : syracuseStep 8421529 = 6316147) B6316147
theorem B11228705 : Blo 2217435 11228705 := bstep (se 2 (by rfl) ⟨4210764, by rfl⟩ : syracuseStep 11228705 = 8421529) B8421529
theorem B7485803 : Blo 2217435 7485803 := bstep (se 1 (by rfl) ⟨5614352, by rfl⟩ : syracuseStep 7485803 = 11228705) B11228705
theorem B4990535 : Blo 2217435 4990535 := bstep (se 1 (by rfl) ⟨3742901, by rfl⟩ : syracuseStep 4990535 = 7485803) B7485803
theorem B3327023 : Blo 2217435 3327023 := bstep (se 1 (by rfl) ⟨2495267, by rfl⟩ : syracuseStep 3327023 = 4990535) B4990535
theorem B2218015 : Blo 2217435 2218015 := bstep (se 1 (by rfl) ⟨1663511, by rfl⟩ : syracuseStep 2218015 = 3327023) B3327023
theorem B3327029 : Blo 2217435 3327029 := bbase (se 5 (by rfl) ⟨155954, by rfl⟩ : syracuseStep 3327029 = 311909) (by norm_num)
theorem B2218019 : Blo 2217435 2218019 := bstep (se 1 (by rfl) ⟨1663514, by rfl⟩ : syracuseStep 2218019 = 3327029) B3327029
theorem B5614373 : Blo 2217435 5614373 := bbase (se 4 (by rfl) ⟨526347, by rfl⟩ : syracuseStep 5614373 = 1052695) (by norm_num)
theorem B3742915 : Blo 2217435 3742915 := bstep (se 1 (by rfl) ⟨2807186, by rfl⟩ : syracuseStep 3742915 = 5614373) B5614373
theorem B4990553 : Blo 2217435 4990553 := bstep (se 2 (by rfl) ⟨1871457, by rfl⟩ : syracuseStep 4990553 = 3742915) B3742915
theorem B3327035 : Blo 2217435 3327035 := bstep (se 1 (by rfl) ⟨2495276, by rfl⟩ : syracuseStep 3327035 = 4990553) B4990553
theorem B2218023 : Blo 2217435 2218023 := bstep (se 1 (by rfl) ⟨1663517, by rfl⟩ : syracuseStep 2218023 = 3327035) B3327035
theorem B2495281 : Blo 2217435 2495281 := bbase (se 2 (by rfl) ⟨935730, by rfl⟩ : syracuseStep 2495281 = 1871461) (by norm_num)
theorem B3327041 : Blo 2217435 3327041 := bstep (se 2 (by rfl) ⟨1247640, by rfl⟩ : syracuseStep 3327041 = 2495281) B2495281
theorem B2218027 : Blo 2217435 2218027 := bstep (se 1 (by rfl) ⟨1663520, by rfl⟩ : syracuseStep 2218027 = 3327041) B3327041
theorem B3793997 : Blo 2217435 3793997 := bbase (se 3 (by rfl) ⟨711374, by rfl⟩ : syracuseStep 3793997 = 1422749) (by norm_num)
theorem B10117325 : Blo 2217435 10117325 := bstep (se 3 (by rfl) ⟨1896998, by rfl⟩ : syracuseStep 10117325 = 3793997) B3793997
theorem B6744883 : Blo 2217435 6744883 := bstep (se 1 (by rfl) ⟨5058662, by rfl⟩ : syracuseStep 6744883 = 10117325) B10117325
theorem B8993177 : Blo 2217435 8993177 := bstep (se 2 (by rfl) ⟨3372441, by rfl⟩ : syracuseStep 8993177 = 6744883) B6744883
theorem B5995451 : Blo 2217435 5995451 := bstep (se 1 (by rfl) ⟨4496588, by rfl⟩ : syracuseStep 5995451 = 8993177) B8993177
theorem B3996967 : Blo 2217435 3996967 := bstep (se 1 (by rfl) ⟨2997725, by rfl⟩ : syracuseStep 3996967 = 5995451) B5995451
theorem B5329289 : Blo 2217435 5329289 := bstep (se 2 (by rfl) ⟨1998483, by rfl⟩ : syracuseStep 5329289 = 3996967) B3996967
theorem B3552859 : Blo 2217435 3552859 := bstep (se 1 (by rfl) ⟨2664644, by rfl⟩ : syracuseStep 3552859 = 5329289) B5329289
theorem B4737145 : Blo 2217435 4737145 := bstep (se 2 (by rfl) ⟨1776429, by rfl⟩ : syracuseStep 4737145 = 3552859) B3552859
theorem B6316193 : Blo 2217435 6316193 := bstep (se 2 (by rfl) ⟨2368572, by rfl⟩ : syracuseStep 6316193 = 4737145) B4737145
theorem B4210795 : Blo 2217435 4210795 := bstep (se 1 (by rfl) ⟨3158096, by rfl⟩ : syracuseStep 4210795 = 6316193) B6316193
theorem B5614393 : Blo 2217435 5614393 := bstep (se 2 (by rfl) ⟨2105397, by rfl⟩ : syracuseStep 5614393 = 4210795) B4210795
theorem B7485857 : Blo 2217435 7485857 := bstep (se 2 (by rfl) ⟨2807196, by rfl⟩ : syracuseStep 7485857 = 5614393) B5614393
theorem B4990571 : Blo 2217435 4990571 := bstep (se 1 (by rfl) ⟨3742928, by rfl⟩ : syracuseStep 4990571 = 7485857) B7485857
theorem B3327047 : Blo 2217435 3327047 := bstep (se 1 (by rfl) ⟨2495285, by rfl⟩ : syracuseStep 3327047 = 4990571) B4990571
theorem B2218031 : Blo 2217435 2218031 := bstep (se 1 (by rfl) ⟨1663523, by rfl⟩ : syracuseStep 2218031 = 3327047) B3327047
theorem B3327053 : Blo 2217435 3327053 := bbase (se 3 (by rfl) ⟨623822, by rfl⟩ : syracuseStep 3327053 = 1247645) (by norm_num)
theorem B2218035 : Blo 2217435 2218035 := bstep (se 1 (by rfl) ⟨1663526, by rfl⟩ : syracuseStep 2218035 = 3327053) B3327053
theorem B4990589 : Blo 2217435 4990589 := bbase (se 3 (by rfl) ⟨935735, by rfl⟩ : syracuseStep 4990589 = 1871471) (by norm_num)
theorem B3327059 : Blo 2217435 3327059 := bstep (se 1 (by rfl) ⟨2495294, by rfl⟩ : syracuseStep 3327059 = 4990589) B4990589
theorem B2218039 : Blo 2217435 2218039 := bstep (se 1 (by rfl) ⟨1663529, by rfl⟩ : syracuseStep 2218039 = 3327059) B3327059
theorem B3742949 : Blo 2217435 3742949 := bbase (se 4 (by rfl) ⟨350901, by rfl⟩ : syracuseStep 3742949 = 701803) (by norm_num)
theorem B2495299 : Blo 2217435 2495299 := bstep (se 1 (by rfl) ⟨1871474, by rfl⟩ : syracuseStep 2495299 = 3742949) B3742949
theorem B3327065 : Blo 2217435 3327065 := bstep (se 2 (by rfl) ⟨1247649, by rfl⟩ : syracuseStep 3327065 = 2495299) B2495299
theorem B2218043 : Blo 2217435 2218043 := bstep (se 1 (by rfl) ⟨1663532, by rfl⟩ : syracuseStep 2218043 = 3327065) B3327065
theorem B2529349 : Blo 2217435 2529349 := bbase (se 4 (by rfl) ⟨237126, by rfl⟩ : syracuseStep 2529349 = 474253) (by norm_num)
theorem B13489861 : Blo 2217435 13489861 := bstep (se 4 (by rfl) ⟨1264674, by rfl⟩ : syracuseStep 13489861 = 2529349) B2529349
theorem B17986481 : Blo 2217435 17986481 := bstep (se 2 (by rfl) ⟨6744930, by rfl⟩ : syracuseStep 17986481 = 13489861) B13489861
theorem B11990987 : Blo 2217435 11990987 := bstep (se 1 (by rfl) ⟨8993240, by rfl⟩ : syracuseStep 11990987 = 17986481) B17986481
theorem B7993991 : Blo 2217435 7993991 := bstep (se 1 (by rfl) ⟨5995493, by rfl⟩ : syracuseStep 7993991 = 11990987) B11990987
theorem B5329327 : Blo 2217435 5329327 := bstep (se 1 (by rfl) ⟨3996995, by rfl⟩ : syracuseStep 5329327 = 7993991) B7993991
theorem B7105769 : Blo 2217435 7105769 := bstep (se 2 (by rfl) ⟨2664663, by rfl⟩ : syracuseStep 7105769 = 5329327) B5329327
theorem B4737179 : Blo 2217435 4737179 := bstep (se 1 (by rfl) ⟨3552884, by rfl⟩ : syracuseStep 4737179 = 7105769) B7105769
theorem B3158119 : Blo 2217435 3158119 := bstep (se 1 (by rfl) ⟨2368589, by rfl⟩ : syracuseStep 3158119 = 4737179) B4737179
theorem B16843301 : Blo 2217435 16843301 := bstep (se 4 (by rfl) ⟨1579059, by rfl⟩ : syracuseStep 16843301 = 3158119) B3158119
theorem B11228867 : Blo 2217435 11228867 := bstep (se 1 (by rfl) ⟨8421650, by rfl⟩ : syracuseStep 11228867 = 16843301) B16843301
theorem B7485911 : Blo 2217435 7485911 := bstep (se 1 (by rfl) ⟨5614433, by rfl⟩ : syracuseStep 7485911 = 11228867) B11228867
theorem B4990607 : Blo 2217435 4990607 := bstep (se 1 (by rfl) ⟨3742955, by rfl⟩ : syracuseStep 4990607 = 7485911) B7485911
theorem B3327071 : Blo 2217435 3327071 := bstep (se 1 (by rfl) ⟨2495303, by rfl⟩ : syracuseStep 3327071 = 4990607) B4990607
theorem B2218047 : Blo 2217435 2218047 := bstep (se 1 (by rfl) ⟨1663535, by rfl⟩ : syracuseStep 2218047 = 3327071) B3327071
theorem B3327077 : Blo 2217435 3327077 := bbase (se 4 (by rfl) ⟨311913, by rfl⟩ : syracuseStep 3327077 = 623827) (by norm_num)
theorem B2218051 : Blo 2217435 2218051 := bstep (se 1 (by rfl) ⟨1663538, by rfl⟩ : syracuseStep 2218051 = 3327077) B3327077
theorem B4737197 : Blo 2217435 4737197 := bbase (se 3 (by rfl) ⟨888224, by rfl⟩ : syracuseStep 4737197 = 1776449) (by norm_num)
theorem B3158131 : Blo 2217435 3158131 := bstep (se 1 (by rfl) ⟨2368598, by rfl⟩ : syracuseStep 3158131 = 4737197) B4737197
theorem B4210841 : Blo 2217435 4210841 := bstep (se 2 (by rfl) ⟨1579065, by rfl⟩ : syracuseStep 4210841 = 3158131) B3158131
theorem B2807227 : Blo 2217435 2807227 := bstep (se 1 (by rfl) ⟨2105420, by rfl⟩ : syracuseStep 2807227 = 4210841) B4210841
theorem B3742969 : Blo 2217435 3742969 := bstep (se 2 (by rfl) ⟨1403613, by rfl⟩ : syracuseStep 3742969 = 2807227) B2807227
theorem B4990625 : Blo 2217435 4990625 := bstep (se 2 (by rfl) ⟨1871484, by rfl⟩ : syracuseStep 4990625 = 3742969) B3742969
theorem B3327083 : Blo 2217435 3327083 := bstep (se 1 (by rfl) ⟨2495312, by rfl⟩ : syracuseStep 3327083 = 4990625) B4990625
theorem B2218055 : Blo 2217435 2218055 := bstep (se 1 (by rfl) ⟨1663541, by rfl⟩ : syracuseStep 2218055 = 3327083) B3327083
theorem B2495317 : Blo 2217435 2495317 := bbase (se 9 (by rfl) ⟨7310, by rfl⟩ : syracuseStep 2495317 = 14621) (by norm_num)
theorem B3327089 : Blo 2217435 3327089 := bstep (se 2 (by rfl) ⟨1247658, by rfl⟩ : syracuseStep 3327089 = 2495317) B2495317
theorem B2218059 : Blo 2217435 2218059 := bstep (se 1 (by rfl) ⟨1663544, by rfl⟩ : syracuseStep 2218059 = 3327089) B3327089
theorem B2807237 : Blo 2217435 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B7485965 : Blo 2217435 7485965 := bstep (se 3 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 7485965 = 2807237) B2807237
theorem B4990643 : Blo 2217435 4990643 := bstep (se 1 (by rfl) ⟨3742982, by rfl⟩ : syracuseStep 4990643 = 7485965) B7485965
theorem B3327095 : Blo 2217435 3327095 := bstep (se 1 (by rfl) ⟨2495321, by rfl⟩ : syracuseStep 3327095 = 4990643) B4990643
theorem B2218063 : Blo 2217435 2218063 := bstep (se 1 (by rfl) ⟨1663547, by rfl⟩ : syracuseStep 2218063 = 3327095) B3327095
theorem B3327101 : Blo 2217435 3327101 := bbase (se 3 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 3327101 = 1247663) (by norm_num)
theorem B2218067 : Blo 2217435 2218067 := bstep (se 1 (by rfl) ⟨1663550, by rfl⟩ : syracuseStep 2218067 = 3327101) B3327101
theorem B4990661 : Blo 2217435 4990661 := bbase (se 4 (by rfl) ⟨467874, by rfl⟩ : syracuseStep 4990661 = 935749) (by norm_num)
theorem B3327107 : Blo 2217435 3327107 := bstep (se 1 (by rfl) ⟨2495330, by rfl⟩ : syracuseStep 3327107 = 4990661) B4990661
theorem B2218071 : Blo 2217435 2218071 := bstep (se 1 (by rfl) ⟨1663553, by rfl⟩ : syracuseStep 2218071 = 3327107) B3327107
theorem B4496677 : Blo 2217435 4496677 := bbase (se 4 (by rfl) ⟨421563, by rfl⟩ : syracuseStep 4496677 = 843127) (by norm_num)
theorem B23982277 : Blo 2217435 23982277 := bstep (se 4 (by rfl) ⟨2248338, by rfl⟩ : syracuseStep 23982277 = 4496677) B4496677
theorem B31976369 : Blo 2217435 31976369 := bstep (se 2 (by rfl) ⟨11991138, by rfl⟩ : syracuseStep 31976369 = 23982277) B23982277
theorem B21317579 : Blo 2217435 21317579 := bstep (se 1 (by rfl) ⟨15988184, by rfl⟩ : syracuseStep 21317579 = 31976369) B31976369
theorem B14211719 : Blo 2217435 14211719 := bstep (se 1 (by rfl) ⟨10658789, by rfl⟩ : syracuseStep 14211719 = 21317579) B21317579
theorem B9474479 : Blo 2217435 9474479 := bstep (se 1 (by rfl) ⟨7105859, by rfl⟩ : syracuseStep 9474479 = 14211719) B14211719
theorem B6316319 : Blo 2217435 6316319 := bstep (se 1 (by rfl) ⟨4737239, by rfl⟩ : syracuseStep 6316319 = 9474479) B9474479
theorem B4210879 : Blo 2217435 4210879 := bstep (se 1 (by rfl) ⟨3158159, by rfl⟩ : syracuseStep 4210879 = 6316319) B6316319
theorem B5614505 : Blo 2217435 5614505 := bstep (se 2 (by rfl) ⟨2105439, by rfl⟩ : syracuseStep 5614505 = 4210879) B4210879
theorem B3743003 : Blo 2217435 3743003 := bstep (se 1 (by rfl) ⟨2807252, by rfl⟩ : syracuseStep 3743003 = 5614505) B5614505
theorem B2495335 : Blo 2217435 2495335 := bstep (se 1 (by rfl) ⟨1871501, by rfl⟩ : syracuseStep 2495335 = 3743003) B3743003
theorem B3327113 : Blo 2217435 3327113 := bstep (se 2 (by rfl) ⟨1247667, by rfl⟩ : syracuseStep 3327113 = 2495335) B2495335
theorem B2218075 : Blo 2217435 2218075 := bstep (se 1 (by rfl) ⟨1663556, by rfl⟩ : syracuseStep 2218075 = 3327113) B3327113
theorem B11229029 : Blo 2217435 11229029 := bbase (se 4 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 11229029 = 2105443) (by norm_num)
theorem B7486019 : Blo 2217435 7486019 := bstep (se 1 (by rfl) ⟨5614514, by rfl⟩ : syracuseStep 7486019 = 11229029) B11229029
theorem B4990679 : Blo 2217435 4990679 := bstep (se 1 (by rfl) ⟨3743009, by rfl⟩ : syracuseStep 4990679 = 7486019) B7486019
theorem B3327119 : Blo 2217435 3327119 := bstep (se 1 (by rfl) ⟨2495339, by rfl⟩ : syracuseStep 3327119 = 4990679) B4990679
theorem B2218079 : Blo 2217435 2218079 := bstep (se 1 (by rfl) ⟨1663559, by rfl⟩ : syracuseStep 2218079 = 3327119) B3327119
theorem B3327125 : Blo 2217435 3327125 := bbase (se 6 (by rfl) ⟨77979, by rfl⟩ : syracuseStep 3327125 = 155959) (by norm_num)
theorem B2218083 : Blo 2217435 2218083 := bstep (se 1 (by rfl) ⟨1663562, by rfl⟩ : syracuseStep 2218083 = 3327125) B3327125
theorem B17986805 : Blo 2217435 17986805 := bbase (se 5 (by rfl) ⟨843131, by rfl⟩ : syracuseStep 17986805 = 1686263) (by norm_num)
theorem B11991203 : Blo 2217435 11991203 := bstep (se 1 (by rfl) ⟨8993402, by rfl⟩ : syracuseStep 11991203 = 17986805) B17986805
theorem B7994135 : Blo 2217435 7994135 := bstep (se 1 (by rfl) ⟨5995601, by rfl⟩ : syracuseStep 7994135 = 11991203) B11991203
theorem B5329423 : Blo 2217435 5329423 := bstep (se 1 (by rfl) ⟨3997067, by rfl⟩ : syracuseStep 5329423 = 7994135) B7994135
theorem B7105897 : Blo 2217435 7105897 := bstep (se 2 (by rfl) ⟨2664711, by rfl⟩ : syracuseStep 7105897 = 5329423) B5329423
theorem B9474529 : Blo 2217435 9474529 := bstep (se 2 (by rfl) ⟨3552948, by rfl⟩ : syracuseStep 9474529 = 7105897) B7105897
theorem B12632705 : Blo 2217435 12632705 := bstep (se 2 (by rfl) ⟨4737264, by rfl⟩ : syracuseStep 12632705 = 9474529) B9474529
theorem B8421803 : Blo 2217435 8421803 := bstep (se 1 (by rfl) ⟨6316352, by rfl⟩ : syracuseStep 8421803 = 12632705) B12632705
theorem B5614535 : Blo 2217435 5614535 := bstep (se 1 (by rfl) ⟨4210901, by rfl⟩ : syracuseStep 5614535 = 8421803) B8421803
theorem B3743023 : Blo 2217435 3743023 := bstep (se 1 (by rfl) ⟨2807267, by rfl⟩ : syracuseStep 3743023 = 5614535) B5614535
theorem B4990697 : Blo 2217435 4990697 := bstep (se 2 (by rfl) ⟨1871511, by rfl⟩ : syracuseStep 4990697 = 3743023) B3743023
theorem B3327131 : Blo 2217435 3327131 := bstep (se 1 (by rfl) ⟨2495348, by rfl⟩ : syracuseStep 3327131 = 4990697) B4990697
theorem B2218087 : Blo 2217435 2218087 := bstep (se 1 (by rfl) ⟨1663565, by rfl⟩ : syracuseStep 2218087 = 3327131) B3327131
theorem B2495353 : Blo 2217435 2495353 := bbase (se 2 (by rfl) ⟨935757, by rfl⟩ : syracuseStep 2495353 = 1871515) (by norm_num)
theorem B3327137 : Blo 2217435 3327137 := bstep (se 2 (by rfl) ⟨1247676, by rfl⟩ : syracuseStep 3327137 = 2495353) B2495353
theorem B2218091 : Blo 2217435 2218091 := bstep (se 1 (by rfl) ⟨1663568, by rfl⟩ : syracuseStep 2218091 = 3327137) B3327137
theorem B2664721 : Blo 2217435 2664721 := bbase (se 2 (by rfl) ⟨999270, by rfl⟩ : syracuseStep 2664721 = 1998541) (by norm_num)
theorem B14211845 : Blo 2217435 14211845 := bstep (se 4 (by rfl) ⟨1332360, by rfl⟩ : syracuseStep 14211845 = 2664721) B2664721
theorem B9474563 : Blo 2217435 9474563 := bstep (se 1 (by rfl) ⟨7105922, by rfl⟩ : syracuseStep 9474563 = 14211845) B14211845
theorem B6316375 : Blo 2217435 6316375 := bstep (se 1 (by rfl) ⟨4737281, by rfl⟩ : syracuseStep 6316375 = 9474563) B9474563
theorem B8421833 : Blo 2217435 8421833 := bstep (se 2 (by rfl) ⟨3158187, by rfl⟩ : syracuseStep 8421833 = 6316375) B6316375
theorem B5614555 : Blo 2217435 5614555 := bstep (se 1 (by rfl) ⟨4210916, by rfl⟩ : syracuseStep 5614555 = 8421833) B8421833
theorem B7486073 : Blo 2217435 7486073 := bstep (se 2 (by rfl) ⟨2807277, by rfl⟩ : syracuseStep 7486073 = 5614555) B5614555
theorem B4990715 : Blo 2217435 4990715 := bstep (se 1 (by rfl) ⟨3743036, by rfl⟩ : syracuseStep 4990715 = 7486073) B7486073
theorem B3327143 : Blo 2217435 3327143 := bstep (se 1 (by rfl) ⟨2495357, by rfl⟩ : syracuseStep 3327143 = 4990715) B4990715
theorem B2218095 : Blo 2217435 2218095 := bstep (se 1 (by rfl) ⟨1663571, by rfl⟩ : syracuseStep 2218095 = 3327143) B3327143
theorem B3327149 : Blo 2217435 3327149 := bbase (se 3 (by rfl) ⟨623840, by rfl⟩ : syracuseStep 3327149 = 1247681) (by norm_num)
theorem B2218099 : Blo 2217435 2218099 := bstep (se 1 (by rfl) ⟨1663574, by rfl⟩ : syracuseStep 2218099 = 3327149) B3327149
theorem B4990733 : Blo 2217435 4990733 := bbase (se 3 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 4990733 = 1871525) (by norm_num)
theorem B3327155 : Blo 2217435 3327155 := bstep (se 1 (by rfl) ⟨2495366, by rfl⟩ : syracuseStep 3327155 = 4990733) B4990733
theorem B2218103 : Blo 2217435 2218103 := bstep (se 1 (by rfl) ⟨1663577, by rfl⟩ : syracuseStep 2218103 = 3327155) B3327155
theorem B2807293 : Blo 2217435 2807293 := bbase (se 3 (by rfl) ⟨526367, by rfl⟩ : syracuseStep 2807293 = 1052735) (by norm_num)
theorem B3743057 : Blo 2217435 3743057 := bstep (se 2 (by rfl) ⟨1403646, by rfl⟩ : syracuseStep 3743057 = 2807293) B2807293
theorem B2495371 : Blo 2217435 2495371 := bstep (se 1 (by rfl) ⟨1871528, by rfl⟩ : syracuseStep 2495371 = 3743057) B3743057
theorem B3327161 : Blo 2217435 3327161 := bstep (se 2 (by rfl) ⟨1247685, by rfl⟩ : syracuseStep 3327161 = 2495371) B2495371
theorem B2218107 : Blo 2217435 2218107 := bstep (se 1 (by rfl) ⟨1663580, by rfl⟩ : syracuseStep 2218107 = 3327161) B3327161
theorem B7105973 : Blo 2217435 7105973 := bbase (se 5 (by rfl) ⟨333092, by rfl⟩ : syracuseStep 7105973 = 666185) (by norm_num)
theorem B18949261 : Blo 2217435 18949261 := bstep (se 3 (by rfl) ⟨3552986, by rfl⟩ : syracuseStep 18949261 = 7105973) B7105973
theorem B25265681 : Blo 2217435 25265681 := bstep (se 2 (by rfl) ⟨9474630, by rfl⟩ : syracuseStep 25265681 = 18949261) B18949261
theorem B16843787 : Blo 2217435 16843787 := bstep (se 1 (by rfl) ⟨12632840, by rfl⟩ : syracuseStep 16843787 = 25265681) B25265681
theorem B11229191 : Blo 2217435 11229191 := bstep (se 1 (by rfl) ⟨8421893, by rfl⟩ : syracuseStep 11229191 = 16843787) B16843787
theorem B7486127 : Blo 2217435 7486127 := bstep (se 1 (by rfl) ⟨5614595, by rfl⟩ : syracuseStep 7486127 = 11229191) B11229191
theorem B4990751 : Blo 2217435 4990751 := bstep (se 1 (by rfl) ⟨3743063, by rfl⟩ : syracuseStep 4990751 = 7486127) B7486127
theorem B3327167 : Blo 2217435 3327167 := bstep (se 1 (by rfl) ⟨2495375, by rfl⟩ : syracuseStep 3327167 = 4990751) B4990751
theorem B2218111 : Blo 2217435 2218111 := bstep (se 1 (by rfl) ⟨1663583, by rfl⟩ : syracuseStep 2218111 = 3327167) B3327167
theorem B3327173 : Blo 2217435 3327173 := bbase (se 4 (by rfl) ⟨311922, by rfl⟩ : syracuseStep 3327173 = 623845) (by norm_num)
theorem B2218115 : Blo 2217435 2218115 := bstep (se 1 (by rfl) ⟨1663586, by rfl⟩ : syracuseStep 2218115 = 3327173) B3327173
theorem B3743077 : Blo 2217435 3743077 := bbase (se 4 (by rfl) ⟨350913, by rfl⟩ : syracuseStep 3743077 = 701827) (by norm_num)
theorem B4990769 : Blo 2217435 4990769 := bstep (se 2 (by rfl) ⟨1871538, by rfl⟩ : syracuseStep 4990769 = 3743077) B3743077
theorem B3327179 : Blo 2217435 3327179 := bstep (se 1 (by rfl) ⟨2495384, by rfl⟩ : syracuseStep 3327179 = 4990769) B4990769
theorem B2218119 : Blo 2217435 2218119 := bstep (se 1 (by rfl) ⟨1663589, by rfl⟩ : syracuseStep 2218119 = 3327179) B3327179
theorem B2495389 : Blo 2217435 2495389 := bbase (se 3 (by rfl) ⟨467885, by rfl⟩ : syracuseStep 2495389 = 935771) (by norm_num)
theorem B3327185 : Blo 2217435 3327185 := bstep (se 2 (by rfl) ⟨1247694, by rfl⟩ : syracuseStep 3327185 = 2495389) B2495389
theorem B2218123 : Blo 2217435 2218123 := bstep (se 1 (by rfl) ⟨1663592, by rfl⟩ : syracuseStep 2218123 = 3327185) B3327185
theorem B7486181 : Blo 2217435 7486181 := bbase (se 4 (by rfl) ⟨701829, by rfl⟩ : syracuseStep 7486181 = 1403659) (by norm_num)
theorem B4990787 : Blo 2217435 4990787 := bstep (se 1 (by rfl) ⟨3743090, by rfl⟩ : syracuseStep 4990787 = 7486181) B7486181
theorem B3327191 : Blo 2217435 3327191 := bstep (se 1 (by rfl) ⟨2495393, by rfl⟩ : syracuseStep 3327191 = 4990787) B4990787
theorem B2218127 : Blo 2217435 2218127 := bstep (se 1 (by rfl) ⟨1663595, by rfl⟩ : syracuseStep 2218127 = 3327191) B3327191
theorem B3327197 : Blo 2217435 3327197 := bbase (se 3 (by rfl) ⟨623849, by rfl⟩ : syracuseStep 3327197 = 1247699) (by norm_num)
theorem B2218131 : Blo 2217435 2218131 := bstep (se 1 (by rfl) ⟨1663598, by rfl⟩ : syracuseStep 2218131 = 3327197) B3327197
theorem B4990805 : Blo 2217435 4990805 := bbase (se 9 (by rfl) ⟨14621, by rfl⟩ : syracuseStep 4990805 = 29243) (by norm_num)
theorem B3327203 : Blo 2217435 3327203 := bstep (se 1 (by rfl) ⟨2495402, by rfl⟩ : syracuseStep 3327203 = 4990805) B4990805
theorem B2218135 : Blo 2217435 2218135 := bstep (se 1 (by rfl) ⟨1663601, by rfl⟩ : syracuseStep 2218135 = 3327203) B3327203
theorem B6316501 : Blo 2217435 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B8422001 : Blo 2217435 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B5614667 : Blo 2217435 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B3743111 : Blo 2217435 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B2495407 : Blo 2217435 2495407 := bstep (se 1 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 2495407 = 3743111) B3743111
theorem B3327209 : Blo 2217435 3327209 := bstep (se 2 (by rfl) ⟨1247703, by rfl⟩ : syracuseStep 3327209 = 2495407) B2495407
theorem B2218139 : Blo 2217435 2218139 := bstep (se 1 (by rfl) ⟨1663604, by rfl⟩ : syracuseStep 2218139 = 3327209) B3327209
theorem B2598949 : Blo 2217435 2598949 := bbase (se 4 (by rfl) ⟨243651, by rfl⟩ : syracuseStep 2598949 = 487303) (by norm_num)
theorem B13861061 : Blo 2217435 13861061 := bstep (se 4 (by rfl) ⟨1299474, by rfl⟩ : syracuseStep 13861061 = 2598949) B2598949
theorem B9240707 : Blo 2217435 9240707 := bstep (se 1 (by rfl) ⟨6930530, by rfl⟩ : syracuseStep 9240707 = 13861061) B13861061
theorem B24641885 : Blo 2217435 24641885 := bstep (se 3 (by rfl) ⟨4620353, by rfl⟩ : syracuseStep 24641885 = 9240707) B9240707
theorem B65711693 : Blo 2217435 65711693 := bstep (se 3 (by rfl) ⟨12320942, by rfl⟩ : syracuseStep 65711693 = 24641885) B24641885
theorem B175231181 : Blo 2217435 175231181 := bstep (se 3 (by rfl) ⟨32855846, by rfl⟩ : syracuseStep 175231181 = 65711693) B65711693
theorem B116820787 : Blo 2217435 116820787 := bstep (se 1 (by rfl) ⟨87615590, by rfl⟩ : syracuseStep 116820787 = 175231181) B175231181
theorem B155761049 : Blo 2217435 155761049 := bstep (se 2 (by rfl) ⟨58410393, by rfl⟩ : syracuseStep 155761049 = 116820787) B116820787
theorem B103840699 : Blo 2217435 103840699 := bstep (se 1 (by rfl) ⟨77880524, by rfl⟩ : syracuseStep 103840699 = 155761049) B155761049
theorem B138454265 : Blo 2217435 138454265 := bstep (se 2 (by rfl) ⟨51920349, by rfl⟩ : syracuseStep 138454265 = 103840699) B103840699
theorem B92302843 : Blo 2217435 92302843 := bstep (se 1 (by rfl) ⟨69227132, by rfl⟩ : syracuseStep 92302843 = 138454265) B138454265
theorem B123070457 : Blo 2217435 123070457 := bstep (se 2 (by rfl) ⟨46151421, by rfl⟩ : syracuseStep 123070457 = 92302843) B92302843
theorem B82046971 : Blo 2217435 82046971 := bstep (se 1 (by rfl) ⟨61535228, by rfl⟩ : syracuseStep 82046971 = 123070457) B123070457
theorem B437583845 : Blo 2217435 437583845 := bstep (se 4 (by rfl) ⟨41023485, by rfl⟩ : syracuseStep 437583845 = 82046971) B82046971
theorem B291722563 : Blo 2217435 291722563 := bstep (se 1 (by rfl) ⟨218791922, by rfl⟩ : syracuseStep 291722563 = 437583845) B437583845
theorem B388963417 : Blo 2217435 388963417 := bstep (se 2 (by rfl) ⟨145861281, by rfl⟩ : syracuseStep 388963417 = 291722563) B291722563
theorem B518617889 : Blo 2217435 518617889 := bstep (se 2 (by rfl) ⟨194481708, by rfl⟩ : syracuseStep 518617889 = 388963417) B388963417
theorem B345745259 : Blo 2217435 345745259 := bstep (se 1 (by rfl) ⟨259308944, by rfl⟩ : syracuseStep 345745259 = 518617889) B518617889
theorem B230496839 : Blo 2217435 230496839 := bstep (se 1 (by rfl) ⟨172872629, by rfl⟩ : syracuseStep 230496839 = 345745259) B345745259
theorem B153664559 : Blo 2217435 153664559 := bstep (se 1 (by rfl) ⟨115248419, by rfl⟩ : syracuseStep 153664559 = 230496839) B230496839
theorem B102443039 : Blo 2217435 102443039 := bstep (se 1 (by rfl) ⟨76832279, by rfl⟩ : syracuseStep 102443039 = 153664559) B153664559
theorem B68295359 : Blo 2217435 68295359 := bstep (se 1 (by rfl) ⟨51221519, by rfl⟩ : syracuseStep 68295359 = 102443039) B102443039
theorem B182120957 : Blo 2217435 182120957 := bstep (se 3 (by rfl) ⟨34147679, by rfl⟩ : syracuseStep 182120957 = 68295359) B68295359
theorem B121413971 : Blo 2217435 121413971 := bstep (se 1 (by rfl) ⟨91060478, by rfl⟩ : syracuseStep 121413971 = 182120957) B182120957
theorem B80942647 : Blo 2217435 80942647 := bstep (se 1 (by rfl) ⟨60706985, by rfl⟩ : syracuseStep 80942647 = 121413971) B121413971
theorem B107923529 : Blo 2217435 107923529 := bstep (se 2 (by rfl) ⟨40471323, by rfl⟩ : syracuseStep 107923529 = 80942647) B80942647
theorem B71949019 : Blo 2217435 71949019 := bstep (se 1 (by rfl) ⟨53961764, by rfl⟩ : syracuseStep 71949019 = 107923529) B107923529
theorem B95932025 : Blo 2217435 95932025 := bstep (se 2 (by rfl) ⟨35974509, by rfl⟩ : syracuseStep 95932025 = 71949019) B71949019
theorem B63954683 : Blo 2217435 63954683 := bstep (se 1 (by rfl) ⟨47966012, by rfl⟩ : syracuseStep 63954683 = 95932025) B95932025
theorem B42636455 : Blo 2217435 42636455 := bstep (se 1 (by rfl) ⟨31977341, by rfl⟩ : syracuseStep 42636455 = 63954683) B63954683
theorem B28424303 : Blo 2217435 28424303 := bstep (se 1 (by rfl) ⟨21318227, by rfl⟩ : syracuseStep 28424303 = 42636455) B42636455
theorem B18949535 : Blo 2217435 18949535 := bstep (se 1 (by rfl) ⟨14212151, by rfl⟩ : syracuseStep 18949535 = 28424303) B28424303
theorem B12633023 : Blo 2217435 12633023 := bstep (se 1 (by rfl) ⟨9474767, by rfl⟩ : syracuseStep 12633023 = 18949535) B18949535
theorem B8422015 : Blo 2217435 8422015 := bstep (se 1 (by rfl) ⟨6316511, by rfl⟩ : syracuseStep 8422015 = 12633023) B12633023
theorem B11229353 : Blo 2217435 11229353 := bstep (se 2 (by rfl) ⟨4211007, by rfl⟩ : syracuseStep 11229353 = 8422015) B8422015
theorem B7486235 : Blo 2217435 7486235 := bstep (se 1 (by rfl) ⟨5614676, by rfl⟩ : syracuseStep 7486235 = 11229353) B11229353
theorem B4990823 : Blo 2217435 4990823 := bstep (se 1 (by rfl) ⟨3743117, by rfl⟩ : syracuseStep 4990823 = 7486235) B7486235
theorem B3327215 : Blo 2217435 3327215 := bstep (se 1 (by rfl) ⟨2495411, by rfl⟩ : syracuseStep 3327215 = 4990823) B4990823
theorem B2218143 : Blo 2217435 2218143 := bstep (se 1 (by rfl) ⟨1663607, by rfl⟩ : syracuseStep 2218143 = 3327215) B3327215
theorem B3327221 : Blo 2217435 3327221 := bbase (se 5 (by rfl) ⟨155963, by rfl⟩ : syracuseStep 3327221 = 311927) (by norm_num)
theorem B2218147 : Blo 2217435 2218147 := bstep (se 1 (by rfl) ⟨1663610, by rfl⟩ : syracuseStep 2218147 = 3327221) B3327221
theorem B5475997 : Blo 2217435 5475997 := bbase (se 3 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 5475997 = 2053499) (by norm_num)
theorem B7301329 : Blo 2217435 7301329 := bstep (se 2 (by rfl) ⟨2737998, by rfl⟩ : syracuseStep 7301329 = 5475997) B5475997
theorem B38940421 : Blo 2217435 38940421 := bstep (se 4 (by rfl) ⟨3650664, by rfl⟩ : syracuseStep 38940421 = 7301329) B7301329
theorem B51920561 : Blo 2217435 51920561 := bstep (se 2 (by rfl) ⟨19470210, by rfl⟩ : syracuseStep 51920561 = 38940421) B38940421
theorem B138454829 : Blo 2217435 138454829 := bstep (se 3 (by rfl) ⟨25960280, by rfl⟩ : syracuseStep 138454829 = 51920561) B51920561
theorem B92303219 : Blo 2217435 92303219 := bstep (se 1 (by rfl) ⟨69227414, by rfl⟩ : syracuseStep 92303219 = 138454829) B138454829
theorem B61535479 : Blo 2217435 61535479 := bstep (se 1 (by rfl) ⟨46151609, by rfl⟩ : syracuseStep 61535479 = 92303219) B92303219
theorem B82047305 : Blo 2217435 82047305 := bstep (se 2 (by rfl) ⟨30767739, by rfl⟩ : syracuseStep 82047305 = 61535479) B61535479
theorem B54698203 : Blo 2217435 54698203 := bstep (se 1 (by rfl) ⟨41023652, by rfl⟩ : syracuseStep 54698203 = 82047305) B82047305
theorem B72930937 : Blo 2217435 72930937 := bstep (se 2 (by rfl) ⟨27349101, by rfl⟩ : syracuseStep 72930937 = 54698203) B54698203
theorem B97241249 : Blo 2217435 97241249 := bstep (se 2 (by rfl) ⟨36465468, by rfl⟩ : syracuseStep 97241249 = 72930937) B72930937
theorem B64827499 : Blo 2217435 64827499 := bstep (se 1 (by rfl) ⟨48620624, by rfl⟩ : syracuseStep 64827499 = 97241249) B97241249
theorem B86436665 : Blo 2217435 86436665 := bstep (se 2 (by rfl) ⟨32413749, by rfl⟩ : syracuseStep 86436665 = 64827499) B64827499
theorem B57624443 : Blo 2217435 57624443 := bstep (se 1 (by rfl) ⟨43218332, by rfl⟩ : syracuseStep 57624443 = 86436665) B86436665
theorem B38416295 : Blo 2217435 38416295 := bstep (se 1 (by rfl) ⟨28812221, by rfl⟩ : syracuseStep 38416295 = 57624443) B57624443
theorem B102443453 : Blo 2217435 102443453 := bstep (se 3 (by rfl) ⟨19208147, by rfl⟩ : syracuseStep 102443453 = 38416295) B38416295
theorem B68295635 : Blo 2217435 68295635 := bstep (se 1 (by rfl) ⟨51221726, by rfl⟩ : syracuseStep 68295635 = 102443453) B102443453
theorem B45530423 : Blo 2217435 45530423 := bstep (se 1 (by rfl) ⟨34147817, by rfl⟩ : syracuseStep 45530423 = 68295635) B68295635
theorem B30353615 : Blo 2217435 30353615 := bstep (se 1 (by rfl) ⟨22765211, by rfl⟩ : syracuseStep 30353615 = 45530423) B45530423
theorem B20235743 : Blo 2217435 20235743 := bstep (se 1 (by rfl) ⟨15176807, by rfl⟩ : syracuseStep 20235743 = 30353615) B30353615
theorem B13490495 : Blo 2217435 13490495 := bstep (se 1 (by rfl) ⟨10117871, by rfl⟩ : syracuseStep 13490495 = 20235743) B20235743
theorem B8993663 : Blo 2217435 8993663 := bstep (se 1 (by rfl) ⟨6745247, by rfl⟩ : syracuseStep 8993663 = 13490495) B13490495
theorem B5995775 : Blo 2217435 5995775 := bstep (se 1 (by rfl) ⟨4496831, by rfl⟩ : syracuseStep 5995775 = 8993663) B8993663
theorem B3997183 : Blo 2217435 3997183 := bstep (se 1 (by rfl) ⟨2997887, by rfl⟩ : syracuseStep 3997183 = 5995775) B5995775
theorem B5329577 : Blo 2217435 5329577 := bstep (se 2 (by rfl) ⟨1998591, by rfl⟩ : syracuseStep 5329577 = 3997183) B3997183
theorem B14212205 : Blo 2217435 14212205 := bstep (se 3 (by rfl) ⟨2664788, by rfl⟩ : syracuseStep 14212205 = 5329577) B5329577
theorem B9474803 : Blo 2217435 9474803 := bstep (se 1 (by rfl) ⟨7106102, by rfl⟩ : syracuseStep 9474803 = 14212205) B14212205
theorem B6316535 : Blo 2217435 6316535 := bstep (se 1 (by rfl) ⟨4737401, by rfl⟩ : syracuseStep 6316535 = 9474803) B9474803
theorem B4211023 : Blo 2217435 4211023 := bstep (se 1 (by rfl) ⟨3158267, by rfl⟩ : syracuseStep 4211023 = 6316535) B6316535
theorem B5614697 : Blo 2217435 5614697 := bstep (se 2 (by rfl) ⟨2105511, by rfl⟩ : syracuseStep 5614697 = 4211023) B4211023
theorem B3743131 : Blo 2217435 3743131 := bstep (se 1 (by rfl) ⟨2807348, by rfl⟩ : syracuseStep 3743131 = 5614697) B5614697
theorem B4990841 : Blo 2217435 4990841 := bstep (se 2 (by rfl) ⟨1871565, by rfl⟩ : syracuseStep 4990841 = 3743131) B3743131
theorem B3327227 : Blo 2217435 3327227 := bstep (se 1 (by rfl) ⟨2495420, by rfl⟩ : syracuseStep 3327227 = 4990841) B4990841
theorem B2218151 : Blo 2217435 2218151 := bstep (se 1 (by rfl) ⟨1663613, by rfl⟩ : syracuseStep 2218151 = 3327227) B3327227
theorem B2495425 : Blo 2217435 2495425 := bbase (se 2 (by rfl) ⟨935784, by rfl⟩ : syracuseStep 2495425 = 1871569) (by norm_num)
theorem B3327233 : Blo 2217435 3327233 := bstep (se 2 (by rfl) ⟨1247712, by rfl⟩ : syracuseStep 3327233 = 2495425) B2495425
theorem B2218155 : Blo 2217435 2218155 := bstep (se 1 (by rfl) ⟨1663616, by rfl⟩ : syracuseStep 2218155 = 3327233) B3327233
theorem B5614717 : Blo 2217435 5614717 := bbase (se 3 (by rfl) ⟨1052759, by rfl⟩ : syracuseStep 5614717 = 2105519) (by norm_num)
theorem B7486289 : Blo 2217435 7486289 := bstep (se 2 (by rfl) ⟨2807358, by rfl⟩ : syracuseStep 7486289 = 5614717) B5614717
theorem B4990859 : Blo 2217435 4990859 := bstep (se 1 (by rfl) ⟨3743144, by rfl⟩ : syracuseStep 4990859 = 7486289) B7486289
theorem B3327239 : Blo 2217435 3327239 := bstep (se 1 (by rfl) ⟨2495429, by rfl⟩ : syracuseStep 3327239 = 4990859) B4990859
theorem B2218159 : Blo 2217435 2218159 := bstep (se 1 (by rfl) ⟨1663619, by rfl⟩ : syracuseStep 2218159 = 3327239) B3327239
theorem B3327245 : Blo 2217435 3327245 := bbase (se 3 (by rfl) ⟨623858, by rfl⟩ : syracuseStep 3327245 = 1247717) (by norm_num)
theorem B2218163 : Blo 2217435 2218163 := bstep (se 1 (by rfl) ⟨1663622, by rfl⟩ : syracuseStep 2218163 = 3327245) B3327245
theorem B4990877 : Blo 2217435 4990877 := bbase (se 3 (by rfl) ⟨935789, by rfl⟩ : syracuseStep 4990877 = 1871579) (by norm_num)
theorem B3327251 : Blo 2217435 3327251 := bstep (se 1 (by rfl) ⟨2495438, by rfl⟩ : syracuseStep 3327251 = 4990877) B4990877
theorem B2218167 : Blo 2217435 2218167 := bstep (se 1 (by rfl) ⟨1663625, by rfl⟩ : syracuseStep 2218167 = 3327251) B3327251
theorem B3743165 : Blo 2217435 3743165 := bbase (se 3 (by rfl) ⟨701843, by rfl⟩ : syracuseStep 3743165 = 1403687) (by norm_num)
theorem B2495443 : Blo 2217435 2495443 := bstep (se 1 (by rfl) ⟨1871582, by rfl⟩ : syracuseStep 2495443 = 3743165) B3743165
theorem B3327257 : Blo 2217435 3327257 := bstep (se 2 (by rfl) ⟨1247721, by rfl⟩ : syracuseStep 3327257 = 2495443) B2495443
theorem B2218171 : Blo 2217435 2218171 := bstep (se 1 (by rfl) ⟨1663628, by rfl⟩ : syracuseStep 2218171 = 3327257) B3327257
theorem B12633205 : Blo 2217435 12633205 := bbase (se 5 (by rfl) ⟨592181, by rfl⟩ : syracuseStep 12633205 = 1184363) (by norm_num)
theorem B16844273 : Blo 2217435 16844273 := bstep (se 2 (by rfl) ⟨6316602, by rfl⟩ : syracuseStep 16844273 = 12633205) B12633205
theorem B11229515 : Blo 2217435 11229515 := bstep (se 1 (by rfl) ⟨8422136, by rfl⟩ : syracuseStep 11229515 = 16844273) B16844273
theorem B7486343 : Blo 2217435 7486343 := bstep (se 1 (by rfl) ⟨5614757, by rfl⟩ : syracuseStep 7486343 = 11229515) B11229515
theorem B4990895 : Blo 2217435 4990895 := bstep (se 1 (by rfl) ⟨3743171, by rfl⟩ : syracuseStep 4990895 = 7486343) B7486343
theorem B3327263 : Blo 2217435 3327263 := bstep (se 1 (by rfl) ⟨2495447, by rfl⟩ : syracuseStep 3327263 = 4990895) B4990895
theorem B2218175 : Blo 2217435 2218175 := bstep (se 1 (by rfl) ⟨1663631, by rfl⟩ : syracuseStep 2218175 = 3327263) B3327263
theorem B3327269 : Blo 2217435 3327269 := bbase (se 4 (by rfl) ⟨311931, by rfl⟩ : syracuseStep 3327269 = 623863) (by norm_num)
theorem B2218179 : Blo 2217435 2218179 := bstep (se 1 (by rfl) ⟨1663634, by rfl⟩ : syracuseStep 2218179 = 3327269) B3327269
theorem B2807389 : Blo 2217435 2807389 := bbase (se 3 (by rfl) ⟨526385, by rfl⟩ : syracuseStep 2807389 = 1052771) (by norm_num)
theorem B3743185 : Blo 2217435 3743185 := bstep (se 2 (by rfl) ⟨1403694, by rfl⟩ : syracuseStep 3743185 = 2807389) B2807389
theorem B4990913 : Blo 2217435 4990913 := bstep (se 2 (by rfl) ⟨1871592, by rfl⟩ : syracuseStep 4990913 = 3743185) B3743185
theorem B3327275 : Blo 2217435 3327275 := bstep (se 1 (by rfl) ⟨2495456, by rfl⟩ : syracuseStep 3327275 = 4990913) B4990913
theorem B2218183 : Blo 2217435 2218183 := bstep (se 1 (by rfl) ⟨1663637, by rfl⟩ : syracuseStep 2218183 = 3327275) B3327275
theorem B2495461 : Blo 2217435 2495461 := bbase (se 4 (by rfl) ⟨233949, by rfl⟩ : syracuseStep 2495461 = 467899) (by norm_num)
theorem B3327281 : Blo 2217435 3327281 := bstep (se 2 (by rfl) ⟨1247730, by rfl⟩ : syracuseStep 3327281 = 2495461) B2495461
theorem B2218187 : Blo 2217435 2218187 := bstep (se 1 (by rfl) ⟨1663640, by rfl⟩ : syracuseStep 2218187 = 3327281) B3327281
theorem B4802125 : Blo 2217435 4802125 := bbase (se 3 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 4802125 = 1800797) (by norm_num)
theorem B6402833 : Blo 2217435 6402833 := bstep (se 2 (by rfl) ⟨2401062, by rfl⟩ : syracuseStep 6402833 = 4802125) B4802125
theorem B4268555 : Blo 2217435 4268555 := bstep (se 1 (by rfl) ⟨3201416, by rfl⟩ : syracuseStep 4268555 = 6402833) B6402833
theorem B2845703 : Blo 2217435 2845703 := bstep (se 1 (by rfl) ⟨2134277, by rfl⟩ : syracuseStep 2845703 = 4268555) B4268555
theorem B7588541 : Blo 2217435 7588541 := bstep (se 3 (by rfl) ⟨1422851, by rfl⟩ : syracuseStep 7588541 = 2845703) B2845703
theorem B5059027 : Blo 2217435 5059027 := bstep (se 1 (by rfl) ⟨3794270, by rfl⟩ : syracuseStep 5059027 = 7588541) B7588541
theorem B6745369 : Blo 2217435 6745369 := bstep (se 2 (by rfl) ⟨2529513, by rfl⟩ : syracuseStep 6745369 = 5059027) B5059027
theorem B8993825 : Blo 2217435 8993825 := bstep (se 2 (by rfl) ⟨3372684, by rfl⟩ : syracuseStep 8993825 = 6745369) B6745369
theorem B5995883 : Blo 2217435 5995883 := bstep (se 1 (by rfl) ⟨4496912, by rfl⟩ : syracuseStep 5995883 = 8993825) B8993825
theorem B15989021 : Blo 2217435 15989021 := bstep (se 3 (by rfl) ⟨2997941, by rfl⟩ : syracuseStep 15989021 = 5995883) B5995883
theorem B10659347 : Blo 2217435 10659347 := bstep (se 1 (by rfl) ⟨7994510, by rfl⟩ : syracuseStep 10659347 = 15989021) B15989021
theorem B7106231 : Blo 2217435 7106231 := bstep (se 1 (by rfl) ⟨5329673, by rfl⟩ : syracuseStep 7106231 = 10659347) B10659347
theorem B4737487 : Blo 2217435 4737487 := bstep (se 1 (by rfl) ⟨3553115, by rfl⟩ : syracuseStep 4737487 = 7106231) B7106231
theorem B6316649 : Blo 2217435 6316649 := bstep (se 2 (by rfl) ⟨2368743, by rfl⟩ : syracuseStep 6316649 = 4737487) B4737487
theorem B4211099 : Blo 2217435 4211099 := bstep (se 1 (by rfl) ⟨3158324, by rfl⟩ : syracuseStep 4211099 = 6316649) B6316649
theorem B2807399 : Blo 2217435 2807399 := bstep (se 1 (by rfl) ⟨2105549, by rfl⟩ : syracuseStep 2807399 = 4211099) B4211099
theorem B7486397 : Blo 2217435 7486397 := bstep (se 3 (by rfl) ⟨1403699, by rfl⟩ : syracuseStep 7486397 = 2807399) B2807399
theorem B4990931 : Blo 2217435 4990931 := bstep (se 1 (by rfl) ⟨3743198, by rfl⟩ : syracuseStep 4990931 = 7486397) B7486397
theorem B3327287 : Blo 2217435 3327287 := bstep (se 1 (by rfl) ⟨2495465, by rfl⟩ : syracuseStep 3327287 = 4990931) B4990931
theorem B2218191 : Blo 2217435 2218191 := bstep (se 1 (by rfl) ⟨1663643, by rfl⟩ : syracuseStep 2218191 = 3327287) B3327287
theorem B3327293 : Blo 2217435 3327293 := bbase (se 3 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 3327293 = 1247735) (by norm_num)
theorem B2218195 : Blo 2217435 2218195 := bstep (se 1 (by rfl) ⟨1663646, by rfl⟩ : syracuseStep 2218195 = 3327293) B3327293
theorem B4990949 : Blo 2217435 4990949 := bbase (se 4 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 4990949 = 935803) (by norm_num)
theorem B3327299 : Blo 2217435 3327299 := bstep (se 1 (by rfl) ⟨2495474, by rfl⟩ : syracuseStep 3327299 = 4990949) B4990949
theorem B2218199 : Blo 2217435 2218199 := bstep (se 1 (by rfl) ⟨1663649, by rfl⟩ : syracuseStep 2218199 = 3327299) B3327299
theorem B5614829 : Blo 2217435 5614829 := bbase (se 3 (by rfl) ⟨1052780, by rfl⟩ : syracuseStep 5614829 = 2105561) (by norm_num)
theorem B3743219 : Blo 2217435 3743219 := bstep (se 1 (by rfl) ⟨2807414, by rfl⟩ : syracuseStep 3743219 = 5614829) B5614829
theorem B2495479 : Blo 2217435 2495479 := bstep (se 1 (by rfl) ⟨1871609, by rfl⟩ : syracuseStep 2495479 = 3743219) B3743219
theorem B3327305 : Blo 2217435 3327305 := bstep (se 2 (by rfl) ⟨1247739, by rfl⟩ : syracuseStep 3327305 = 2495479) B2495479
theorem B2218203 : Blo 2217435 2218203 := bstep (se 1 (by rfl) ⟨1663652, by rfl⟩ : syracuseStep 2218203 = 3327305) B3327305
theorem B3553141 : Blo 2217435 3553141 := bbase (se 5 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 3553141 = 333107) (by norm_num)
theorem B4737521 : Blo 2217435 4737521 := bstep (se 2 (by rfl) ⟨1776570, by rfl⟩ : syracuseStep 4737521 = 3553141) B3553141
theorem B3158347 : Blo 2217435 3158347 := bstep (se 1 (by rfl) ⟨2368760, by rfl⟩ : syracuseStep 3158347 = 4737521) B4737521
theorem B4211129 : Blo 2217435 4211129 := bstep (se 2 (by rfl) ⟨1579173, by rfl⟩ : syracuseStep 4211129 = 3158347) B3158347
theorem B11229677 : Blo 2217435 11229677 := bstep (se 3 (by rfl) ⟨2105564, by rfl⟩ : syracuseStep 11229677 = 4211129) B4211129
theorem B7486451 : Blo 2217435 7486451 := bstep (se 1 (by rfl) ⟨5614838, by rfl⟩ : syracuseStep 7486451 = 11229677) B11229677
theorem B4990967 : Blo 2217435 4990967 := bstep (se 1 (by rfl) ⟨3743225, by rfl⟩ : syracuseStep 4990967 = 7486451) B7486451
theorem B3327311 : Blo 2217435 3327311 := bstep (se 1 (by rfl) ⟨2495483, by rfl⟩ : syracuseStep 3327311 = 4990967) B4990967
theorem B2218207 : Blo 2217435 2218207 := bstep (se 1 (by rfl) ⟨1663655, by rfl⟩ : syracuseStep 2218207 = 3327311) B3327311
theorem B3327317 : Blo 2217435 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B2218211 : Blo 2217435 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B2368769 : Blo 2217435 2368769 := bbase (se 2 (by rfl) ⟨888288, by rfl⟩ : syracuseStep 2368769 = 1776577) (by norm_num)
theorem B6316717 : Blo 2217435 6316717 := bstep (se 3 (by rfl) ⟨1184384, by rfl⟩ : syracuseStep 6316717 = 2368769) B2368769
theorem B8422289 : Blo 2217435 8422289 := bstep (se 2 (by rfl) ⟨3158358, by rfl⟩ : syracuseStep 8422289 = 6316717) B6316717
theorem B5614859 : Blo 2217435 5614859 := bstep (se 1 (by rfl) ⟨4211144, by rfl⟩ : syracuseStep 5614859 = 8422289) B8422289
theorem B3743239 : Blo 2217435 3743239 := bstep (se 1 (by rfl) ⟨2807429, by rfl⟩ : syracuseStep 3743239 = 5614859) B5614859
theorem B4990985 : Blo 2217435 4990985 := bstep (se 2 (by rfl) ⟨1871619, by rfl⟩ : syracuseStep 4990985 = 3743239) B3743239
theorem B3327323 : Blo 2217435 3327323 := bstep (se 1 (by rfl) ⟨2495492, by rfl⟩ : syracuseStep 3327323 = 4990985) B4990985
theorem B2218215 : Blo 2217435 2218215 := bstep (se 1 (by rfl) ⟨1663661, by rfl⟩ : syracuseStep 2218215 = 3327323) B3327323
theorem B2495497 : Blo 2217435 2495497 := bbase (se 2 (by rfl) ⟨935811, by rfl⟩ : syracuseStep 2495497 = 1871623) (by norm_num)
theorem B3327329 : Blo 2217435 3327329 := bstep (se 2 (by rfl) ⟨1247748, by rfl⟩ : syracuseStep 3327329 = 2495497) B2495497
theorem B2218219 : Blo 2217435 2218219 := bstep (se 1 (by rfl) ⟨1663664, by rfl⟩ : syracuseStep 2218219 = 3327329) B3327329
theorem B21318997 : Blo 2217435 21318997 := bbase (se 11 (by rfl) ⟨15614, by rfl⟩ : syracuseStep 21318997 = 31229) (by norm_num)
theorem B28425329 : Blo 2217435 28425329 := bstep (se 2 (by rfl) ⟨10659498, by rfl⟩ : syracuseStep 28425329 = 21318997) B21318997
theorem B18950219 : Blo 2217435 18950219 := bstep (se 1 (by rfl) ⟨14212664, by rfl⟩ : syracuseStep 18950219 = 28425329) B28425329
theorem B12633479 : Blo 2217435 12633479 := bstep (se 1 (by rfl) ⟨9475109, by rfl⟩ : syracuseStep 12633479 = 18950219) B18950219
theorem B8422319 : Blo 2217435 8422319 := bstep (se 1 (by rfl) ⟨6316739, by rfl⟩ : syracuseStep 8422319 = 12633479) B12633479
theorem B5614879 : Blo 2217435 5614879 := bstep (se 1 (by rfl) ⟨4211159, by rfl⟩ : syracuseStep 5614879 = 8422319) B8422319
theorem B7486505 : Blo 2217435 7486505 := bstep (se 2 (by rfl) ⟨2807439, by rfl⟩ : syracuseStep 7486505 = 5614879) B5614879
theorem B4991003 : Blo 2217435 4991003 := bstep (se 1 (by rfl) ⟨3743252, by rfl⟩ : syracuseStep 4991003 = 7486505) B7486505
theorem B3327335 : Blo 2217435 3327335 := bstep (se 1 (by rfl) ⟨2495501, by rfl⟩ : syracuseStep 3327335 = 4991003) B4991003
theorem B2218223 : Blo 2217435 2218223 := bstep (se 1 (by rfl) ⟨1663667, by rfl⟩ : syracuseStep 2218223 = 3327335) B3327335
theorem B3327341 : Blo 2217435 3327341 := bbase (se 3 (by rfl) ⟨623876, by rfl⟩ : syracuseStep 3327341 = 1247753) (by norm_num)
theorem B2218227 : Blo 2217435 2218227 := bstep (se 1 (by rfl) ⟨1663670, by rfl⟩ : syracuseStep 2218227 = 3327341) B3327341
theorem B4991021 : Blo 2217435 4991021 := bbase (se 3 (by rfl) ⟨935816, by rfl⟩ : syracuseStep 4991021 = 1871633) (by norm_num)
theorem B3327347 : Blo 2217435 3327347 := bstep (se 1 (by rfl) ⟨2495510, by rfl⟩ : syracuseStep 3327347 = 4991021) B4991021
theorem B2218231 : Blo 2217435 2218231 := bstep (se 1 (by rfl) ⟨1663673, by rfl⟩ : syracuseStep 2218231 = 3327347) B3327347
theorem B2564077 : Blo 2217435 2564077 := bbase (se 3 (by rfl) ⟨480764, by rfl⟩ : syracuseStep 2564077 = 961529) (by norm_num)
theorem B3418769 : Blo 2217435 3418769 := bstep (se 2 (by rfl) ⟨1282038, by rfl⟩ : syracuseStep 3418769 = 2564077) B2564077
theorem B2279179 : Blo 2217435 2279179 := bstep (se 1 (by rfl) ⟨1709384, by rfl⟩ : syracuseStep 2279179 = 3418769) B3418769
theorem B3038905 : Blo 2217435 3038905 := bstep (se 2 (by rfl) ⟨1139589, by rfl⟩ : syracuseStep 3038905 = 2279179) B2279179
theorem B4051873 : Blo 2217435 4051873 := bstep (se 2 (by rfl) ⟨1519452, by rfl⟩ : syracuseStep 4051873 = 3038905) B3038905
theorem B5402497 : Blo 2217435 5402497 := bstep (se 2 (by rfl) ⟨2025936, by rfl⟩ : syracuseStep 5402497 = 4051873) B4051873
theorem B7203329 : Blo 2217435 7203329 := bstep (se 2 (by rfl) ⟨2701248, by rfl⟩ : syracuseStep 7203329 = 5402497) B5402497
theorem B4802219 : Blo 2217435 4802219 := bstep (se 1 (by rfl) ⟨3601664, by rfl⟩ : syracuseStep 4802219 = 7203329) B7203329
theorem B3201479 : Blo 2217435 3201479 := bstep (se 1 (by rfl) ⟨2401109, by rfl⟩ : syracuseStep 3201479 = 4802219) B4802219
theorem B34149109 : Blo 2217435 34149109 := bstep (se 5 (by rfl) ⟨1600739, by rfl⟩ : syracuseStep 34149109 = 3201479) B3201479
theorem B45532145 : Blo 2217435 45532145 := bstep (se 2 (by rfl) ⟨17074554, by rfl⟩ : syracuseStep 45532145 = 34149109) B34149109
theorem B30354763 : Blo 2217435 30354763 := bstep (se 1 (by rfl) ⟨22766072, by rfl⟩ : syracuseStep 30354763 = 45532145) B45532145
theorem B40473017 : Blo 2217435 40473017 := bstep (se 2 (by rfl) ⟨15177381, by rfl⟩ : syracuseStep 40473017 = 30354763) B30354763
theorem B26982011 : Blo 2217435 26982011 := bstep (se 1 (by rfl) ⟨20236508, by rfl⟩ : syracuseStep 26982011 = 40473017) B40473017
theorem B17988007 : Blo 2217435 17988007 := bstep (se 1 (by rfl) ⟨13491005, by rfl⟩ : syracuseStep 17988007 = 26982011) B26982011
theorem B23984009 : Blo 2217435 23984009 := bstep (se 2 (by rfl) ⟨8994003, by rfl⟩ : syracuseStep 23984009 = 17988007) B17988007
theorem B15989339 : Blo 2217435 15989339 := bstep (se 1 (by rfl) ⟨11992004, by rfl⟩ : syracuseStep 15989339 = 23984009) B23984009
theorem B10659559 : Blo 2217435 10659559 := bstep (se 1 (by rfl) ⟨7994669, by rfl⟩ : syracuseStep 10659559 = 15989339) B15989339
theorem B14212745 : Blo 2217435 14212745 := bstep (se 2 (by rfl) ⟨5329779, by rfl⟩ : syracuseStep 14212745 = 10659559) B10659559
theorem B9475163 : Blo 2217435 9475163 := bstep (se 1 (by rfl) ⟨7106372, by rfl⟩ : syracuseStep 9475163 = 14212745) B14212745
theorem B6316775 : Blo 2217435 6316775 := bstep (se 1 (by rfl) ⟨4737581, by rfl⟩ : syracuseStep 6316775 = 9475163) B9475163
theorem B4211183 : Blo 2217435 4211183 := bstep (se 1 (by rfl) ⟨3158387, by rfl⟩ : syracuseStep 4211183 = 6316775) B6316775
theorem B2807455 : Blo 2217435 2807455 := bstep (se 1 (by rfl) ⟨2105591, by rfl⟩ : syracuseStep 2807455 = 4211183) B4211183
theorem B3743273 : Blo 2217435 3743273 := bstep (se 2 (by rfl) ⟨1403727, by rfl⟩ : syracuseStep 3743273 = 2807455) B2807455
theorem B2495515 : Blo 2217435 2495515 := bstep (se 1 (by rfl) ⟨1871636, by rfl⟩ : syracuseStep 2495515 = 3743273) B3743273
theorem B3327353 : Blo 2217435 3327353 := bstep (se 2 (by rfl) ⟨1247757, by rfl⟩ : syracuseStep 3327353 = 2495515) B2495515
theorem B2218235 : Blo 2217435 2218235 := bstep (se 1 (by rfl) ⟨1663676, by rfl⟩ : syracuseStep 2218235 = 3327353) B3327353
theorem B38417813 : Blo 2217435 38417813 := bbase (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) (by norm_num)
theorem B25611875 : Blo 2217435 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B17074583 : Blo 2217435 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B11383055 : Blo 2217435 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B7588703 : Blo 2217435 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B5059135 : Blo 2217435 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B6745513 : Blo 2217435 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B8994017 : Blo 2217435 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B23984045 : Blo 2217435 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B15989363 : Blo 2217435 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B10659575 : Blo 2217435 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B7106383 : Blo 2217435 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B37900709 : Blo 2217435 37900709 := bstep (se 4 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 37900709 = 7106383) B7106383
theorem B25267139 : Blo 2217435 25267139 := bstep (se 1 (by rfl) ⟨18950354, by rfl⟩ : syracuseStep 25267139 = 37900709) B37900709
theorem B16844759 : Blo 2217435 16844759 := bstep (se 1 (by rfl) ⟨12633569, by rfl⟩ : syracuseStep 16844759 = 25267139) B25267139
theorem B11229839 : Blo 2217435 11229839 := bstep (se 1 (by rfl) ⟨8422379, by rfl⟩ : syracuseStep 11229839 = 16844759) B16844759
theorem B7486559 : Blo 2217435 7486559 := bstep (se 1 (by rfl) ⟨5614919, by rfl⟩ : syracuseStep 7486559 = 11229839) B11229839
theorem B4991039 : Blo 2217435 4991039 := bstep (se 1 (by rfl) ⟨3743279, by rfl⟩ : syracuseStep 4991039 = 7486559) B7486559
theorem B3327359 : Blo 2217435 3327359 := bstep (se 1 (by rfl) ⟨2495519, by rfl⟩ : syracuseStep 3327359 = 4991039) B4991039
theorem B2218239 : Blo 2217435 2218239 := bstep (se 1 (by rfl) ⟨1663679, by rfl⟩ : syracuseStep 2218239 = 3327359) B3327359
theorem B3327365 : Blo 2217435 3327365 := bbase (se 4 (by rfl) ⟨311940, by rfl⟩ : syracuseStep 3327365 = 623881) (by norm_num)
theorem B2218243 : Blo 2217435 2218243 := bstep (se 1 (by rfl) ⟨1663682, by rfl⟩ : syracuseStep 2218243 = 3327365) B3327365
theorem B3743293 : Blo 2217435 3743293 := bbase (se 3 (by rfl) ⟨701867, by rfl⟩ : syracuseStep 3743293 = 1403735) (by norm_num)
theorem B4991057 : Blo 2217435 4991057 := bstep (se 2 (by rfl) ⟨1871646, by rfl⟩ : syracuseStep 4991057 = 3743293) B3743293
theorem B3327371 : Blo 2217435 3327371 := bstep (se 1 (by rfl) ⟨2495528, by rfl⟩ : syracuseStep 3327371 = 4991057) B4991057
theorem B2218247 : Blo 2217435 2218247 := bstep (se 1 (by rfl) ⟨1663685, by rfl⟩ : syracuseStep 2218247 = 3327371) B3327371
theorem B2495533 : Blo 2217435 2495533 := bbase (se 3 (by rfl) ⟨467912, by rfl⟩ : syracuseStep 2495533 = 935825) (by norm_num)
theorem B3327377 : Blo 2217435 3327377 := bstep (se 2 (by rfl) ⟨1247766, by rfl⟩ : syracuseStep 3327377 = 2495533) B2495533
theorem B2218251 : Blo 2217435 2218251 := bstep (se 1 (by rfl) ⟨1663688, by rfl⟩ : syracuseStep 2218251 = 3327377) B3327377
theorem B7486613 : Blo 2217435 7486613 := bbase (se 6 (by rfl) ⟨175467, by rfl⟩ : syracuseStep 7486613 = 350935) (by norm_num)
theorem B4991075 : Blo 2217435 4991075 := bstep (se 1 (by rfl) ⟨3743306, by rfl⟩ : syracuseStep 4991075 = 7486613) B7486613
theorem B3327383 : Blo 2217435 3327383 := bstep (se 1 (by rfl) ⟨2495537, by rfl⟩ : syracuseStep 3327383 = 4991075) B4991075
theorem B2218255 : Blo 2217435 2218255 := bstep (se 1 (by rfl) ⟨1663691, by rfl⟩ : syracuseStep 2218255 = 3327383) B3327383
theorem B3327389 : Blo 2217435 3327389 := bbase (se 3 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 3327389 = 1247771) (by norm_num)
theorem B2218259 : Blo 2217435 2218259 := bstep (se 1 (by rfl) ⟨1663694, by rfl⟩ : syracuseStep 2218259 = 3327389) B3327389
theorem B4991093 : Blo 2217435 4991093 := bbase (se 5 (by rfl) ⟨233957, by rfl⟩ : syracuseStep 4991093 = 467915) (by norm_num)
theorem B3327395 : Blo 2217435 3327395 := bstep (se 1 (by rfl) ⟨2495546, by rfl⟩ : syracuseStep 3327395 = 4991093) B4991093
theorem B2218263 : Blo 2217435 2218263 := bstep (se 1 (by rfl) ⟨1663697, by rfl⟩ : syracuseStep 2218263 = 3327395) B3327395
theorem B3553237 : Blo 2217435 3553237 := bbase (se 7 (by rfl) ⟨41639, by rfl⟩ : syracuseStep 3553237 = 83279) (by norm_num)
theorem B18950597 : Blo 2217435 18950597 := bstep (se 4 (by rfl) ⟨1776618, by rfl⟩ : syracuseStep 18950597 = 3553237) B3553237
theorem B12633731 : Blo 2217435 12633731 := bstep (se 1 (by rfl) ⟨9475298, by rfl⟩ : syracuseStep 12633731 = 18950597) B18950597
theorem B8422487 : Blo 2217435 8422487 := bstep (se 1 (by rfl) ⟨6316865, by rfl⟩ : syracuseStep 8422487 = 12633731) B12633731
theorem B5614991 : Blo 2217435 5614991 := bstep (se 1 (by rfl) ⟨4211243, by rfl⟩ : syracuseStep 5614991 = 8422487) B8422487
theorem B3743327 : Blo 2217435 3743327 := bstep (se 1 (by rfl) ⟨2807495, by rfl⟩ : syracuseStep 3743327 = 5614991) B5614991
theorem B2495551 : Blo 2217435 2495551 := bstep (se 1 (by rfl) ⟨1871663, by rfl⟩ : syracuseStep 2495551 = 3743327) B3743327
theorem B3327401 : Blo 2217435 3327401 := bstep (se 2 (by rfl) ⟨1247775, by rfl⟩ : syracuseStep 3327401 = 2495551) B2495551
theorem B2218267 : Blo 2217435 2218267 := bstep (se 1 (by rfl) ⟨1663700, by rfl⟩ : syracuseStep 2218267 = 3327401) B3327401
theorem B8422501 : Blo 2217435 8422501 := bbase (se 4 (by rfl) ⟨789609, by rfl⟩ : syracuseStep 8422501 = 1579219) (by norm_num)
theorem B11230001 : Blo 2217435 11230001 := bstep (se 2 (by rfl) ⟨4211250, by rfl⟩ : syracuseStep 11230001 = 8422501) B8422501
theorem B7486667 : Blo 2217435 7486667 := bstep (se 1 (by rfl) ⟨5615000, by rfl⟩ : syracuseStep 7486667 = 11230001) B11230001
theorem B4991111 : Blo 2217435 4991111 := bstep (se 1 (by rfl) ⟨3743333, by rfl⟩ : syracuseStep 4991111 = 7486667) B7486667
theorem B3327407 : Blo 2217435 3327407 := bstep (se 1 (by rfl) ⟨2495555, by rfl⟩ : syracuseStep 3327407 = 4991111) B4991111
theorem B2218271 : Blo 2217435 2218271 := bstep (se 1 (by rfl) ⟨1663703, by rfl⟩ : syracuseStep 2218271 = 3327407) B3327407
theorem B3327413 : Blo 2217435 3327413 := bbase (se 5 (by rfl) ⟨155972, by rfl⟩ : syracuseStep 3327413 = 311945) (by norm_num)
theorem B2218275 : Blo 2217435 2218275 := bstep (se 1 (by rfl) ⟨1663706, by rfl⟩ : syracuseStep 2218275 = 3327413) B3327413
theorem B5615021 : Blo 2217435 5615021 := bbase (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) (by norm_num)
theorem B3743347 : Blo 2217435 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B4991129 : Blo 2217435 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B3327419 : Blo 2217435 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B2218279 : Blo 2217435 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B2495569 : Blo 2217435 2495569 := bbase (se 2 (by rfl) ⟨935838, by rfl⟩ : syracuseStep 2495569 = 1871677) (by norm_num)
theorem B3327425 : Blo 2217435 3327425 := bstep (se 2 (by rfl) ⟨1247784, by rfl⟩ : syracuseStep 3327425 = 2495569) B2495569
theorem B2218283 : Blo 2217435 2218283 := bstep (se 1 (by rfl) ⟨1663712, by rfl⟩ : syracuseStep 2218283 = 3327425) B3327425
theorem B3158461 : Blo 2217435 3158461 := bbase (se 3 (by rfl) ⟨592211, by rfl⟩ : syracuseStep 3158461 = 1184423) (by norm_num)
theorem B4211281 : Blo 2217435 4211281 := bstep (se 2 (by rfl) ⟨1579230, by rfl⟩ : syracuseStep 4211281 = 3158461) B3158461
theorem B5615041 : Blo 2217435 5615041 := bstep (se 2 (by rfl) ⟨2105640, by rfl⟩ : syracuseStep 5615041 = 4211281) B4211281
theorem B7486721 : Blo 2217435 7486721 := bstep (se 2 (by rfl) ⟨2807520, by rfl⟩ : syracuseStep 7486721 = 5615041) B5615041
theorem B4991147 : Blo 2217435 4991147 := bstep (se 1 (by rfl) ⟨3743360, by rfl⟩ : syracuseStep 4991147 = 7486721) B7486721
theorem B3327431 : Blo 2217435 3327431 := bstep (se 1 (by rfl) ⟨2495573, by rfl⟩ : syracuseStep 3327431 = 4991147) B4991147
theorem B2218287 : Blo 2217435 2218287 := bstep (se 1 (by rfl) ⟨1663715, by rfl⟩ : syracuseStep 2218287 = 3327431) B3327431
theorem B3327437 : Blo 2217435 3327437 := bbase (se 3 (by rfl) ⟨623894, by rfl⟩ : syracuseStep 3327437 = 1247789) (by norm_num)
theorem B2218291 : Blo 2217435 2218291 := bstep (se 1 (by rfl) ⟨1663718, by rfl⟩ : syracuseStep 2218291 = 3327437) B3327437
theorem B4991165 : Blo 2217435 4991165 := bbase (se 3 (by rfl) ⟨935843, by rfl⟩ : syracuseStep 4991165 = 1871687) (by norm_num)
theorem B3327443 : Blo 2217435 3327443 := bstep (se 1 (by rfl) ⟨2495582, by rfl⟩ : syracuseStep 3327443 = 4991165) B4991165
theorem B2218295 : Blo 2217435 2218295 := bstep (se 1 (by rfl) ⟨1663721, by rfl⟩ : syracuseStep 2218295 = 3327443) B3327443
theorem B3743381 : Blo 2217435 3743381 := bbase (se 6 (by rfl) ⟨87735, by rfl⟩ : syracuseStep 3743381 = 175471) (by norm_num)
theorem B2495587 : Blo 2217435 2495587 := bstep (se 1 (by rfl) ⟨1871690, by rfl⟩ : syracuseStep 2495587 = 3743381) B3743381
theorem B3327449 : Blo 2217435 3327449 := bstep (se 2 (by rfl) ⟨1247793, by rfl⟩ : syracuseStep 3327449 = 2495587) B2495587
theorem B2218299 : Blo 2217435 2218299 := bstep (se 1 (by rfl) ⟨1663724, by rfl⟩ : syracuseStep 2218299 = 3327449) B3327449
theorem B8994277 : Blo 2217435 8994277 := bbase (se 4 (by rfl) ⟨843213, by rfl⟩ : syracuseStep 8994277 = 1686427) (by norm_num)
theorem B11992369 : Blo 2217435 11992369 := bstep (se 2 (by rfl) ⟨4497138, by rfl⟩ : syracuseStep 11992369 = 8994277) B8994277
theorem B15989825 : Blo 2217435 15989825 := bstep (se 2 (by rfl) ⟨5996184, by rfl⟩ : syracuseStep 15989825 = 11992369) B11992369
theorem B10659883 : Blo 2217435 10659883 := bstep (se 1 (by rfl) ⟨7994912, by rfl⟩ : syracuseStep 10659883 = 15989825) B15989825
theorem B14213177 : Blo 2217435 14213177 := bstep (se 2 (by rfl) ⟨5329941, by rfl⟩ : syracuseStep 14213177 = 10659883) B10659883
theorem B9475451 : Blo 2217435 9475451 := bstep (se 1 (by rfl) ⟨7106588, by rfl⟩ : syracuseStep 9475451 = 14213177) B14213177
theorem B6316967 : Blo 2217435 6316967 := bstep (se 1 (by rfl) ⟨4737725, by rfl⟩ : syracuseStep 6316967 = 9475451) B9475451
theorem B16845245 : Blo 2217435 16845245 := bstep (se 3 (by rfl) ⟨3158483, by rfl⟩ : syracuseStep 16845245 = 6316967) B6316967
theorem B11230163 : Blo 2217435 11230163 := bstep (se 1 (by rfl) ⟨8422622, by rfl⟩ : syracuseStep 11230163 = 16845245) B16845245
theorem B7486775 : Blo 2217435 7486775 := bstep (se 1 (by rfl) ⟨5615081, by rfl⟩ : syracuseStep 7486775 = 11230163) B11230163
theorem B4991183 : Blo 2217435 4991183 := bstep (se 1 (by rfl) ⟨3743387, by rfl⟩ : syracuseStep 4991183 = 7486775) B7486775
theorem B3327455 : Blo 2217435 3327455 := bstep (se 1 (by rfl) ⟨2495591, by rfl⟩ : syracuseStep 3327455 = 4991183) B4991183
theorem B2218303 : Blo 2217435 2218303 := bstep (se 1 (by rfl) ⟨1663727, by rfl⟩ : syracuseStep 2218303 = 3327455) B3327455
theorem B3327461 : Blo 2217435 3327461 := bbase (se 4 (by rfl) ⟨311949, by rfl⟩ : syracuseStep 3327461 = 623899) (by norm_num)
theorem B2218307 : Blo 2217435 2218307 := bstep (se 1 (by rfl) ⟨1663730, by rfl⟩ : syracuseStep 2218307 = 3327461) B3327461
theorem B7025621 : Blo 2217435 7025621 := bbase (se 7 (by rfl) ⟨82331, by rfl⟩ : syracuseStep 7025621 = 164663) (by norm_num)
theorem B18734989 : Blo 2217435 18734989 := bstep (se 3 (by rfl) ⟨3512810, by rfl⟩ : syracuseStep 18734989 = 7025621) B7025621
theorem B24979985 : Blo 2217435 24979985 := bstep (se 2 (by rfl) ⟨9367494, by rfl⟩ : syracuseStep 24979985 = 18734989) B18734989
theorem B16653323 : Blo 2217435 16653323 := bstep (se 1 (by rfl) ⟨12489992, by rfl⟩ : syracuseStep 16653323 = 24979985) B24979985
theorem B44408861 : Blo 2217435 44408861 := bstep (se 3 (by rfl) ⟨8326661, by rfl⟩ : syracuseStep 44408861 = 16653323) B16653323
theorem B29605907 : Blo 2217435 29605907 := bstep (se 1 (by rfl) ⟨22204430, by rfl⟩ : syracuseStep 29605907 = 44408861) B44408861
theorem B19737271 : Blo 2217435 19737271 := bstep (se 1 (by rfl) ⟨14802953, by rfl⟩ : syracuseStep 19737271 = 29605907) B29605907
theorem B26316361 : Blo 2217435 26316361 := bstep (se 2 (by rfl) ⟨9868635, by rfl⟩ : syracuseStep 26316361 = 19737271) B19737271
theorem B35088481 : Blo 2217435 35088481 := bstep (se 2 (by rfl) ⟨13158180, by rfl⟩ : syracuseStep 35088481 = 26316361) B26316361
theorem B46784641 : Blo 2217435 46784641 := bstep (se 2 (by rfl) ⟨17544240, by rfl⟩ : syracuseStep 46784641 = 35088481) B35088481
theorem B62379521 : Blo 2217435 62379521 := bstep (se 2 (by rfl) ⟨23392320, by rfl⟩ : syracuseStep 62379521 = 46784641) B46784641
theorem B41586347 : Blo 2217435 41586347 := bstep (se 1 (by rfl) ⟨31189760, by rfl⟩ : syracuseStep 41586347 = 62379521) B62379521
theorem B27724231 : Blo 2217435 27724231 := bstep (se 1 (by rfl) ⟨20793173, by rfl⟩ : syracuseStep 27724231 = 41586347) B41586347
theorem B36965641 : Blo 2217435 36965641 := bstep (se 2 (by rfl) ⟨13862115, by rfl⟩ : syracuseStep 36965641 = 27724231) B27724231
theorem B49287521 : Blo 2217435 49287521 := bstep (se 2 (by rfl) ⟨18482820, by rfl⟩ : syracuseStep 49287521 = 36965641) B36965641
theorem B32858347 : Blo 2217435 32858347 := bstep (se 1 (by rfl) ⟨24643760, by rfl⟩ : syracuseStep 32858347 = 49287521) B49287521
theorem B43811129 : Blo 2217435 43811129 := bstep (se 2 (by rfl) ⟨16429173, by rfl⟩ : syracuseStep 43811129 = 32858347) B32858347
theorem B116829677 : Blo 2217435 116829677 := bstep (se 3 (by rfl) ⟨21905564, by rfl⟩ : syracuseStep 116829677 = 43811129) B43811129
theorem B77886451 : Blo 2217435 77886451 := bstep (se 1 (by rfl) ⟨58414838, by rfl⟩ : syracuseStep 77886451 = 116829677) B116829677
theorem B103848601 : Blo 2217435 103848601 := bstep (se 2 (by rfl) ⟨38943225, by rfl⟩ : syracuseStep 103848601 = 77886451) B77886451
theorem B138464801 : Blo 2217435 138464801 := bstep (se 2 (by rfl) ⟨51924300, by rfl⟩ : syracuseStep 138464801 = 103848601) B103848601
theorem B92309867 : Blo 2217435 92309867 := bstep (se 1 (by rfl) ⟨69232400, by rfl⟩ : syracuseStep 92309867 = 138464801) B138464801
theorem B61539911 : Blo 2217435 61539911 := bstep (se 1 (by rfl) ⟨46154933, by rfl⟩ : syracuseStep 61539911 = 92309867) B92309867
theorem B41026607 : Blo 2217435 41026607 := bstep (se 1 (by rfl) ⟨30769955, by rfl⟩ : syracuseStep 41026607 = 61539911) B61539911
theorem B27351071 : Blo 2217435 27351071 := bstep (se 1 (by rfl) ⟨20513303, by rfl⟩ : syracuseStep 27351071 = 41026607) B41026607
theorem B18234047 : Blo 2217435 18234047 := bstep (se 1 (by rfl) ⟨13675535, by rfl⟩ : syracuseStep 18234047 = 27351071) B27351071
theorem B12156031 : Blo 2217435 12156031 := bstep (se 1 (by rfl) ⟨9117023, by rfl⟩ : syracuseStep 12156031 = 18234047) B18234047
theorem B16208041 : Blo 2217435 16208041 := bstep (se 2 (by rfl) ⟨6078015, by rfl⟩ : syracuseStep 16208041 = 12156031) B12156031
theorem B21610721 : Blo 2217435 21610721 := bstep (se 2 (by rfl) ⟨8104020, by rfl⟩ : syracuseStep 21610721 = 16208041) B16208041
theorem B57628589 : Blo 2217435 57628589 := bstep (se 3 (by rfl) ⟨10805360, by rfl⟩ : syracuseStep 57628589 = 21610721) B21610721
theorem B153676237 : Blo 2217435 153676237 := bstep (se 3 (by rfl) ⟨28814294, by rfl⟩ : syracuseStep 153676237 = 57628589) B57628589
theorem B204901649 : Blo 2217435 204901649 := bstep (se 2 (by rfl) ⟨76838118, by rfl⟩ : syracuseStep 204901649 = 153676237) B153676237
theorem B136601099 : Blo 2217435 136601099 := bstep (se 1 (by rfl) ⟨102450824, by rfl⟩ : syracuseStep 136601099 = 204901649) B204901649
theorem B91067399 : Blo 2217435 91067399 := bstep (se 1 (by rfl) ⟨68300549, by rfl⟩ : syracuseStep 91067399 = 136601099) B136601099
theorem B60711599 : Blo 2217435 60711599 := bstep (se 1 (by rfl) ⟨45533699, by rfl⟩ : syracuseStep 60711599 = 91067399) B91067399
theorem B40474399 : Blo 2217435 40474399 := bstep (se 1 (by rfl) ⟨30355799, by rfl⟩ : syracuseStep 40474399 = 60711599) B60711599
theorem B53965865 : Blo 2217435 53965865 := bstep (se 2 (by rfl) ⟨20237199, by rfl⟩ : syracuseStep 53965865 = 40474399) B40474399
theorem B35977243 : Blo 2217435 35977243 := bstep (se 1 (by rfl) ⟨26982932, by rfl⟩ : syracuseStep 35977243 = 53965865) B53965865
theorem B47969657 : Blo 2217435 47969657 := bstep (se 2 (by rfl) ⟨17988621, by rfl⟩ : syracuseStep 47969657 = 35977243) B35977243
theorem B31979771 : Blo 2217435 31979771 := bstep (se 1 (by rfl) ⟨23984828, by rfl⟩ : syracuseStep 31979771 = 47969657) B47969657
theorem B21319847 : Blo 2217435 21319847 := bstep (se 1 (by rfl) ⟨15989885, by rfl⟩ : syracuseStep 21319847 = 31979771) B31979771
theorem B14213231 : Blo 2217435 14213231 := bstep (se 1 (by rfl) ⟨10659923, by rfl⟩ : syracuseStep 14213231 = 21319847) B21319847
theorem B9475487 : Blo 2217435 9475487 := bstep (se 1 (by rfl) ⟨7106615, by rfl⟩ : syracuseStep 9475487 = 14213231) B14213231
theorem B6316991 : Blo 2217435 6316991 := bstep (se 1 (by rfl) ⟨4737743, by rfl⟩ : syracuseStep 6316991 = 9475487) B9475487
theorem B4211327 : Blo 2217435 4211327 := bstep (se 1 (by rfl) ⟨3158495, by rfl⟩ : syracuseStep 4211327 = 6316991) B6316991
theorem B2807551 : Blo 2217435 2807551 := bstep (se 1 (by rfl) ⟨2105663, by rfl⟩ : syracuseStep 2807551 = 4211327) B4211327
theorem B3743401 : Blo 2217435 3743401 := bstep (se 2 (by rfl) ⟨1403775, by rfl⟩ : syracuseStep 3743401 = 2807551) B2807551
theorem B4991201 : Blo 2217435 4991201 := bstep (se 2 (by rfl) ⟨1871700, by rfl⟩ : syracuseStep 4991201 = 3743401) B3743401
theorem B3327467 : Blo 2217435 3327467 := bstep (se 1 (by rfl) ⟨2495600, by rfl⟩ : syracuseStep 3327467 = 4991201) B4991201
theorem B2218311 : Blo 2217435 2218311 := bstep (se 1 (by rfl) ⟨1663733, by rfl⟩ : syracuseStep 2218311 = 3327467) B3327467
theorem B2495605 : Blo 2217435 2495605 := bbase (se 5 (by rfl) ⟨116981, by rfl⟩ : syracuseStep 2495605 = 233963) (by norm_num)
theorem B3327473 : Blo 2217435 3327473 := bstep (se 2 (by rfl) ⟨1247802, by rfl⟩ : syracuseStep 3327473 = 2495605) B2495605
theorem B2218315 : Blo 2217435 2218315 := bstep (se 1 (by rfl) ⟨1663736, by rfl⟩ : syracuseStep 2218315 = 3327473) B3327473
theorem B2807561 : Blo 2217435 2807561 := bbase (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) (by norm_num)
theorem B7486829 : Blo 2217435 7486829 := bstep (se 3 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 7486829 = 2807561) B2807561
theorem B4991219 : Blo 2217435 4991219 := bstep (se 1 (by rfl) ⟨3743414, by rfl⟩ : syracuseStep 4991219 = 7486829) B7486829
theorem B3327479 : Blo 2217435 3327479 := bstep (se 1 (by rfl) ⟨2495609, by rfl⟩ : syracuseStep 3327479 = 4991219) B4991219
theorem B2218319 : Blo 2217435 2218319 := bstep (se 1 (by rfl) ⟨1663739, by rfl⟩ : syracuseStep 2218319 = 3327479) B3327479
theorem B3327485 : Blo 2217435 3327485 := bbase (se 3 (by rfl) ⟨623903, by rfl⟩ : syracuseStep 3327485 = 1247807) (by norm_num)
theorem B2218323 : Blo 2217435 2218323 := bstep (se 1 (by rfl) ⟨1663742, by rfl⟩ : syracuseStep 2218323 = 3327485) B3327485
theorem B4991237 : Blo 2217435 4991237 := bbase (se 4 (by rfl) ⟨467928, by rfl⟩ : syracuseStep 4991237 = 935857) (by norm_num)
theorem B3327491 : Blo 2217435 3327491 := bstep (se 1 (by rfl) ⟨2495618, by rfl⟩ : syracuseStep 3327491 = 4991237) B4991237
theorem B2218327 : Blo 2217435 2218327 := bstep (se 1 (by rfl) ⟨1663745, by rfl⟩ : syracuseStep 2218327 = 3327491) B3327491
theorem B4211365 : Blo 2217435 4211365 := bbase (se 4 (by rfl) ⟨394815, by rfl⟩ : syracuseStep 4211365 = 789631) (by norm_num)
theorem B5615153 : Blo 2217435 5615153 := bstep (se 2 (by rfl) ⟨2105682, by rfl⟩ : syracuseStep 5615153 = 4211365) B4211365
theorem B3743435 : Blo 2217435 3743435 := bstep (se 1 (by rfl) ⟨2807576, by rfl⟩ : syracuseStep 3743435 = 5615153) B5615153
theorem B2495623 : Blo 2217435 2495623 := bstep (se 1 (by rfl) ⟨1871717, by rfl⟩ : syracuseStep 2495623 = 3743435) B3743435
theorem B3327497 : Blo 2217435 3327497 := bstep (se 2 (by rfl) ⟨1247811, by rfl⟩ : syracuseStep 3327497 = 2495623) B2495623
theorem B2218331 : Blo 2217435 2218331 := bstep (se 1 (by rfl) ⟨1663748, by rfl⟩ : syracuseStep 2218331 = 3327497) B3327497
theorem B11230325 : Blo 2217435 11230325 := bbase (se 5 (by rfl) ⟨526421, by rfl⟩ : syracuseStep 11230325 = 1052843) (by norm_num)
theorem B7486883 : Blo 2217435 7486883 := bstep (se 1 (by rfl) ⟨5615162, by rfl⟩ : syracuseStep 7486883 = 11230325) B11230325
theorem B4991255 : Blo 2217435 4991255 := bstep (se 1 (by rfl) ⟨3743441, by rfl⟩ : syracuseStep 4991255 = 7486883) B7486883
theorem B3327503 : Blo 2217435 3327503 := bstep (se 1 (by rfl) ⟨2495627, by rfl⟩ : syracuseStep 3327503 = 4991255) B4991255
theorem B2218335 : Blo 2217435 2218335 := bstep (se 1 (by rfl) ⟨1663751, by rfl⟩ : syracuseStep 2218335 = 3327503) B3327503
theorem B3327509 : Blo 2217435 3327509 := bbase (se 6 (by rfl) ⟨77988, by rfl⟩ : syracuseStep 3327509 = 155977) (by norm_num)
theorem B2218339 : Blo 2217435 2218339 := bstep (se 1 (by rfl) ⟨1663754, by rfl⟩ : syracuseStep 2218339 = 3327509) B3327509
theorem B4497221 : Blo 2217435 4497221 := bbase (se 4 (by rfl) ⟨421614, by rfl⟩ : syracuseStep 4497221 = 843229) (by norm_num)
theorem B2998147 : Blo 2217435 2998147 := bstep (se 1 (by rfl) ⟨2248610, by rfl⟩ : syracuseStep 2998147 = 4497221) B4497221
theorem B3997529 : Blo 2217435 3997529 := bstep (se 2 (by rfl) ⟨1499073, by rfl⟩ : syracuseStep 3997529 = 2998147) B2998147
theorem B2665019 : Blo 2217435 2665019 := bstep (se 1 (by rfl) ⟨1998764, by rfl⟩ : syracuseStep 2665019 = 3997529) B3997529
theorem B7106717 : Blo 2217435 7106717 := bstep (se 3 (by rfl) ⟨1332509, by rfl⟩ : syracuseStep 7106717 = 2665019) B2665019
theorem B18951245 : Blo 2217435 18951245 := bstep (se 3 (by rfl) ⟨3553358, by rfl⟩ : syracuseStep 18951245 = 7106717) B7106717
theorem B12634163 : Blo 2217435 12634163 := bstep (se 1 (by rfl) ⟨9475622, by rfl⟩ : syracuseStep 12634163 = 18951245) B18951245
theorem B8422775 : Blo 2217435 8422775 := bstep (se 1 (by rfl) ⟨6317081, by rfl⟩ : syracuseStep 8422775 = 12634163) B12634163
theorem B5615183 : Blo 2217435 5615183 := bstep (se 1 (by rfl) ⟨4211387, by rfl⟩ : syracuseStep 5615183 = 8422775) B8422775
theorem B3743455 : Blo 2217435 3743455 := bstep (se 1 (by rfl) ⟨2807591, by rfl⟩ : syracuseStep 3743455 = 5615183) B5615183
theorem B4991273 : Blo 2217435 4991273 := bstep (se 2 (by rfl) ⟨1871727, by rfl⟩ : syracuseStep 4991273 = 3743455) B3743455
theorem B3327515 : Blo 2217435 3327515 := bstep (se 1 (by rfl) ⟨2495636, by rfl⟩ : syracuseStep 3327515 = 4991273) B4991273
theorem B2218343 : Blo 2217435 2218343 := bstep (se 1 (by rfl) ⟨1663757, by rfl⟩ : syracuseStep 2218343 = 3327515) B3327515
theorem B2495641 : Blo 2217435 2495641 := bbase (se 2 (by rfl) ⟨935865, by rfl⟩ : syracuseStep 2495641 = 1871731) (by norm_num)
theorem B3327521 : Blo 2217435 3327521 := bstep (se 2 (by rfl) ⟨1247820, by rfl⟩ : syracuseStep 3327521 = 2495641) B2495641
theorem B2218347 : Blo 2217435 2218347 := bstep (se 1 (by rfl) ⟨1663760, by rfl⟩ : syracuseStep 2218347 = 3327521) B3327521
theorem B8422805 : Blo 2217435 8422805 := bbase (se 6 (by rfl) ⟨197409, by rfl⟩ : syracuseStep 8422805 = 394819) (by norm_num)
theorem B5615203 : Blo 2217435 5615203 := bstep (se 1 (by rfl) ⟨4211402, by rfl⟩ : syracuseStep 5615203 = 8422805) B8422805
theorem B7486937 : Blo 2217435 7486937 := bstep (se 2 (by rfl) ⟨2807601, by rfl⟩ : syracuseStep 7486937 = 5615203) B5615203
theorem B4991291 : Blo 2217435 4991291 := bstep (se 1 (by rfl) ⟨3743468, by rfl⟩ : syracuseStep 4991291 = 7486937) B7486937
theorem B3327527 : Blo 2217435 3327527 := bstep (se 1 (by rfl) ⟨2495645, by rfl⟩ : syracuseStep 3327527 = 4991291) B4991291
theorem B2218351 : Blo 2217435 2218351 := bstep (se 1 (by rfl) ⟨1663763, by rfl⟩ : syracuseStep 2218351 = 3327527) B3327527
theorem B3327533 : Blo 2217435 3327533 := bbase (se 3 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 3327533 = 1247825) (by norm_num)
theorem B2218355 : Blo 2217435 2218355 := bstep (se 1 (by rfl) ⟨1663766, by rfl⟩ : syracuseStep 2218355 = 3327533) B3327533
theorem B4991309 : Blo 2217435 4991309 := bbase (se 3 (by rfl) ⟨935870, by rfl⟩ : syracuseStep 4991309 = 1871741) (by norm_num)
theorem B3327539 : Blo 2217435 3327539 := bstep (se 1 (by rfl) ⟨2495654, by rfl⟩ : syracuseStep 3327539 = 4991309) B4991309
theorem B2218359 : Blo 2217435 2218359 := bstep (se 1 (by rfl) ⟨1663769, by rfl⟩ : syracuseStep 2218359 = 3327539) B3327539
theorem B2807617 : Blo 2217435 2807617 := bbase (se 2 (by rfl) ⟨1052856, by rfl⟩ : syracuseStep 2807617 = 2105713) (by norm_num)
theorem B3743489 : Blo 2217435 3743489 := bstep (se 2 (by rfl) ⟨1403808, by rfl⟩ : syracuseStep 3743489 = 2807617) B2807617
theorem B2495659 : Blo 2217435 2495659 := bstep (se 1 (by rfl) ⟨1871744, by rfl⟩ : syracuseStep 2495659 = 3743489) B3743489
theorem B3327545 : Blo 2217435 3327545 := bstep (se 2 (by rfl) ⟨1247829, by rfl⟩ : syracuseStep 3327545 = 2495659) B2495659
theorem B2218363 : Blo 2217435 2218363 := bstep (se 1 (by rfl) ⟨1663772, by rfl⟩ : syracuseStep 2218363 = 3327545) B3327545
theorem B3553397 : Blo 2217435 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B2368931 : Blo 2217435 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B25268597 : Blo 2217435 25268597 := bstep (se 5 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 25268597 = 2368931) B2368931
theorem B16845731 : Blo 2217435 16845731 := bstep (se 1 (by rfl) ⟨12634298, by rfl⟩ : syracuseStep 16845731 = 25268597) B25268597
theorem B11230487 : Blo 2217435 11230487 := bstep (se 1 (by rfl) ⟨8422865, by rfl⟩ : syracuseStep 11230487 = 16845731) B16845731
theorem B7486991 : Blo 2217435 7486991 := bstep (se 1 (by rfl) ⟨5615243, by rfl⟩ : syracuseStep 7486991 = 11230487) B11230487
theorem B4991327 : Blo 2217435 4991327 := bstep (se 1 (by rfl) ⟨3743495, by rfl⟩ : syracuseStep 4991327 = 7486991) B7486991
theorem B3327551 : Blo 2217435 3327551 := bstep (se 1 (by rfl) ⟨2495663, by rfl⟩ : syracuseStep 3327551 = 4991327) B4991327
theorem B2218367 : Blo 2217435 2218367 := bstep (se 1 (by rfl) ⟨1663775, by rfl⟩ : syracuseStep 2218367 = 3327551) B3327551
theorem B3327557 : Blo 2217435 3327557 := bbase (se 4 (by rfl) ⟨311958, by rfl⟩ : syracuseStep 3327557 = 623917) (by norm_num)
theorem B2218371 : Blo 2217435 2218371 := bstep (se 1 (by rfl) ⟨1663778, by rfl⟩ : syracuseStep 2218371 = 3327557) B3327557
theorem B3743509 : Blo 2217435 3743509 := bbase (se 6 (by rfl) ⟨87738, by rfl⟩ : syracuseStep 3743509 = 175477) (by norm_num)
theorem B4991345 : Blo 2217435 4991345 := bstep (se 2 (by rfl) ⟨1871754, by rfl⟩ : syracuseStep 4991345 = 3743509) B3743509
theorem B3327563 : Blo 2217435 3327563 := bstep (se 1 (by rfl) ⟨2495672, by rfl⟩ : syracuseStep 3327563 = 4991345) B4991345
theorem B2218375 : Blo 2217435 2218375 := bstep (se 1 (by rfl) ⟨1663781, by rfl⟩ : syracuseStep 2218375 = 3327563) B3327563
theorem B2495677 : Blo 2217435 2495677 := bbase (se 3 (by rfl) ⟨467939, by rfl⟩ : syracuseStep 2495677 = 935879) (by norm_num)
theorem B3327569 : Blo 2217435 3327569 := bstep (se 2 (by rfl) ⟨1247838, by rfl⟩ : syracuseStep 3327569 = 2495677) B2495677
theorem B2218379 : Blo 2217435 2218379 := bstep (se 1 (by rfl) ⟨1663784, by rfl⟩ : syracuseStep 2218379 = 3327569) B3327569
theorem B7487045 : Blo 2217435 7487045 := bbase (se 4 (by rfl) ⟨701910, by rfl⟩ : syracuseStep 7487045 = 1403821) (by norm_num)
theorem B4991363 : Blo 2217435 4991363 := bstep (se 1 (by rfl) ⟨3743522, by rfl⟩ : syracuseStep 4991363 = 7487045) B7487045
theorem B3327575 : Blo 2217435 3327575 := bstep (se 1 (by rfl) ⟨2495681, by rfl⟩ : syracuseStep 3327575 = 4991363) B4991363
theorem B2218383 : Blo 2217435 2218383 := bstep (se 1 (by rfl) ⟨1663787, by rfl⟩ : syracuseStep 2218383 = 3327575) B3327575
theorem B3327581 : Blo 2217435 3327581 := bbase (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) (by norm_num)
theorem B2218387 : Blo 2217435 2218387 := bstep (se 1 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 2218387 = 3327581) B3327581
theorem B4991381 : Blo 2217435 4991381 := bbase (se 6 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 4991381 = 233971) (by norm_num)
theorem B3327587 : Blo 2217435 3327587 := bstep (se 1 (by rfl) ⟨2495690, by rfl⟩ : syracuseStep 3327587 = 4991381) B4991381
theorem B2218391 : Blo 2217435 2218391 := bstep (se 1 (by rfl) ⟨1663793, by rfl⟩ : syracuseStep 2218391 = 3327587) B3327587
theorem B7106885 : Blo 2217435 7106885 := bbase (se 4 (by rfl) ⟨666270, by rfl⟩ : syracuseStep 7106885 = 1332541) (by norm_num)
theorem B4737923 : Blo 2217435 4737923 := bstep (se 1 (by rfl) ⟨3553442, by rfl⟩ : syracuseStep 4737923 = 7106885) B7106885
theorem B3158615 : Blo 2217435 3158615 := bstep (se 1 (by rfl) ⟨2368961, by rfl⟩ : syracuseStep 3158615 = 4737923) B4737923
theorem B8422973 : Blo 2217435 8422973 := bstep (se 3 (by rfl) ⟨1579307, by rfl⟩ : syracuseStep 8422973 = 3158615) B3158615
theorem B5615315 : Blo 2217435 5615315 := bstep (se 1 (by rfl) ⟨4211486, by rfl⟩ : syracuseStep 5615315 = 8422973) B8422973
theorem B3743543 : Blo 2217435 3743543 := bstep (se 1 (by rfl) ⟨2807657, by rfl⟩ : syracuseStep 3743543 = 5615315) B5615315
theorem B2495695 : Blo 2217435 2495695 := bstep (se 1 (by rfl) ⟨1871771, by rfl⟩ : syracuseStep 2495695 = 3743543) B3743543
theorem B3327593 : Blo 2217435 3327593 := bstep (se 2 (by rfl) ⟨1247847, by rfl⟩ : syracuseStep 3327593 = 2495695) B2495695
theorem B2218395 : Blo 2217435 2218395 := bstep (se 1 (by rfl) ⟨1663796, by rfl⟩ : syracuseStep 2218395 = 3327593) B3327593
theorem B9475861 : Blo 2217435 9475861 := bbase (se 6 (by rfl) ⟨222090, by rfl⟩ : syracuseStep 9475861 = 444181) (by norm_num)
theorem B12634481 : Blo 2217435 12634481 := bstep (se 2 (by rfl) ⟨4737930, by rfl⟩ : syracuseStep 12634481 = 9475861) B9475861
theorem B8422987 : Blo 2217435 8422987 := bstep (se 1 (by rfl) ⟨6317240, by rfl⟩ : syracuseStep 8422987 = 12634481) B12634481
theorem B11230649 : Blo 2217435 11230649 := bstep (se 2 (by rfl) ⟨4211493, by rfl⟩ : syracuseStep 11230649 = 8422987) B8422987
theorem B7487099 : Blo 2217435 7487099 := bstep (se 1 (by rfl) ⟨5615324, by rfl⟩ : syracuseStep 7487099 = 11230649) B11230649
theorem B4991399 : Blo 2217435 4991399 := bstep (se 1 (by rfl) ⟨3743549, by rfl⟩ : syracuseStep 4991399 = 7487099) B7487099
theorem B3327599 : Blo 2217435 3327599 := bstep (se 1 (by rfl) ⟨2495699, by rfl⟩ : syracuseStep 3327599 = 4991399) B4991399
theorem B2218399 : Blo 2217435 2218399 := bstep (se 1 (by rfl) ⟨1663799, by rfl⟩ : syracuseStep 2218399 = 3327599) B3327599
theorem B3327605 : Blo 2217435 3327605 := bbase (se 5 (by rfl) ⟨155981, by rfl⟩ : syracuseStep 3327605 = 311963) (by norm_num)
theorem B2218403 : Blo 2217435 2218403 := bstep (se 1 (by rfl) ⟨1663802, by rfl⟩ : syracuseStep 2218403 = 3327605) B3327605
theorem B4211509 : Blo 2217435 4211509 := bbase (se 5 (by rfl) ⟨197414, by rfl⟩ : syracuseStep 4211509 = 394829) (by norm_num)
theorem B5615345 : Blo 2217435 5615345 := bstep (se 2 (by rfl) ⟨2105754, by rfl⟩ : syracuseStep 5615345 = 4211509) B4211509
theorem B3743563 : Blo 2217435 3743563 := bstep (se 1 (by rfl) ⟨2807672, by rfl⟩ : syracuseStep 3743563 = 5615345) B5615345
theorem B4991417 : Blo 2217435 4991417 := bstep (se 2 (by rfl) ⟨1871781, by rfl⟩ : syracuseStep 4991417 = 3743563) B3743563
theorem B3327611 : Blo 2217435 3327611 := bstep (se 1 (by rfl) ⟨2495708, by rfl⟩ : syracuseStep 3327611 = 4991417) B4991417
theorem B2218407 : Blo 2217435 2218407 := bstep (se 1 (by rfl) ⟨1663805, by rfl⟩ : syracuseStep 2218407 = 3327611) B3327611
theorem B2495713 : Blo 2217435 2495713 := bbase (se 2 (by rfl) ⟨935892, by rfl⟩ : syracuseStep 2495713 = 1871785) (by norm_num)
theorem B3327617 : Blo 2217435 3327617 := bstep (se 2 (by rfl) ⟨1247856, by rfl⟩ : syracuseStep 3327617 = 2495713) B2495713
theorem B2218411 : Blo 2217435 2218411 := bstep (se 1 (by rfl) ⟨1663808, by rfl⟩ : syracuseStep 2218411 = 3327617) B3327617
theorem B5615365 : Blo 2217435 5615365 := bbase (se 4 (by rfl) ⟨526440, by rfl⟩ : syracuseStep 5615365 = 1052881) (by norm_num)
theorem B7487153 : Blo 2217435 7487153 := bstep (se 2 (by rfl) ⟨2807682, by rfl⟩ : syracuseStep 7487153 = 5615365) B5615365
theorem B4991435 : Blo 2217435 4991435 := bstep (se 1 (by rfl) ⟨3743576, by rfl⟩ : syracuseStep 4991435 = 7487153) B7487153
theorem B3327623 : Blo 2217435 3327623 := bstep (se 1 (by rfl) ⟨2495717, by rfl⟩ : syracuseStep 3327623 = 4991435) B4991435
theorem B2218415 : Blo 2217435 2218415 := bstep (se 1 (by rfl) ⟨1663811, by rfl⟩ : syracuseStep 2218415 = 3327623) B3327623
theorem B3327629 : Blo 2217435 3327629 := bbase (se 3 (by rfl) ⟨623930, by rfl⟩ : syracuseStep 3327629 = 1247861) (by norm_num)
theorem B2218419 : Blo 2217435 2218419 := bstep (se 1 (by rfl) ⟨1663814, by rfl⟩ : syracuseStep 2218419 = 3327629) B3327629
theorem B4991453 : Blo 2217435 4991453 := bbase (se 3 (by rfl) ⟨935897, by rfl⟩ : syracuseStep 4991453 = 1871795) (by norm_num)
theorem B3327635 : Blo 2217435 3327635 := bstep (se 1 (by rfl) ⟨2495726, by rfl⟩ : syracuseStep 3327635 = 4991453) B4991453
theorem B2218423 : Blo 2217435 2218423 := bstep (se 1 (by rfl) ⟨1663817, by rfl⟩ : syracuseStep 2218423 = 3327635) B3327635
theorem B3743597 : Blo 2217435 3743597 := bbase (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) (by norm_num)
theorem B2495731 : Blo 2217435 2495731 := bstep (se 1 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 2495731 = 3743597) B3743597
theorem B3327641 : Blo 2217435 3327641 := bstep (se 2 (by rfl) ⟨1247865, by rfl⟩ : syracuseStep 3327641 = 2495731) B2495731
theorem B2218427 : Blo 2217435 2218427 := bstep (se 1 (by rfl) ⟨1663820, by rfl⟩ : syracuseStep 2218427 = 3327641) B3327641
theorem B4802645 : Blo 2217435 4802645 := bbase (se 8 (by rfl) ⟨28140, by rfl⟩ : syracuseStep 4802645 = 56281) (by norm_num)
theorem B3201763 : Blo 2217435 3201763 := bstep (se 1 (by rfl) ⟨2401322, by rfl⟩ : syracuseStep 3201763 = 4802645) B4802645
theorem B4269017 : Blo 2217435 4269017 := bstep (se 2 (by rfl) ⟨1600881, by rfl⟩ : syracuseStep 4269017 = 3201763) B3201763
theorem B2846011 : Blo 2217435 2846011 := bstep (se 1 (by rfl) ⟨2134508, by rfl⟩ : syracuseStep 2846011 = 4269017) B4269017
theorem B3794681 : Blo 2217435 3794681 := bstep (se 2 (by rfl) ⟨1423005, by rfl⟩ : syracuseStep 3794681 = 2846011) B2846011
theorem B2529787 : Blo 2217435 2529787 := bstep (se 1 (by rfl) ⟨1897340, by rfl⟩ : syracuseStep 2529787 = 3794681) B3794681
theorem B3373049 : Blo 2217435 3373049 := bstep (se 2 (by rfl) ⟨1264893, by rfl⟩ : syracuseStep 3373049 = 2529787) B2529787
theorem B2248699 : Blo 2217435 2248699 := bstep (se 1 (by rfl) ⟨1686524, by rfl⟩ : syracuseStep 2248699 = 3373049) B3373049
theorem B2998265 : Blo 2217435 2998265 := bstep (se 2 (by rfl) ⟨1124349, by rfl⟩ : syracuseStep 2998265 = 2248699) B2248699
theorem B31981493 : Blo 2217435 31981493 := bstep (se 5 (by rfl) ⟨1499132, by rfl⟩ : syracuseStep 31981493 = 2998265) B2998265
theorem B21320995 : Blo 2217435 21320995 := bstep (se 1 (by rfl) ⟨15990746, by rfl⟩ : syracuseStep 21320995 = 31981493) B31981493
theorem B28427993 : Blo 2217435 28427993 := bstep (se 2 (by rfl) ⟨10660497, by rfl⟩ : syracuseStep 28427993 = 21320995) B21320995
theorem B18951995 : Blo 2217435 18951995 := bstep (se 1 (by rfl) ⟨14213996, by rfl⟩ : syracuseStep 18951995 = 28427993) B28427993
theorem B12634663 : Blo 2217435 12634663 := bstep (se 1 (by rfl) ⟨9475997, by rfl⟩ : syracuseStep 12634663 = 18951995) B18951995
theorem B16846217 : Blo 2217435 16846217 := bstep (se 2 (by rfl) ⟨6317331, by rfl⟩ : syracuseStep 16846217 = 12634663) B12634663
theorem B11230811 : Blo 2217435 11230811 := bstep (se 1 (by rfl) ⟨8423108, by rfl⟩ : syracuseStep 11230811 = 16846217) B16846217
theorem B7487207 : Blo 2217435 7487207 := bstep (se 1 (by rfl) ⟨5615405, by rfl⟩ : syracuseStep 7487207 = 11230811) B11230811
theorem B4991471 : Blo 2217435 4991471 := bstep (se 1 (by rfl) ⟨3743603, by rfl⟩ : syracuseStep 4991471 = 7487207) B7487207
theorem B3327647 : Blo 2217435 3327647 := bstep (se 1 (by rfl) ⟨2495735, by rfl⟩ : syracuseStep 3327647 = 4991471) B4991471
theorem B2218431 : Blo 2217435 2218431 := bstep (se 1 (by rfl) ⟨1663823, by rfl⟩ : syracuseStep 2218431 = 3327647) B3327647
theorem B3327653 : Blo 2217435 3327653 := bbase (se 4 (by rfl) ⟨311967, by rfl⟩ : syracuseStep 3327653 = 623935) (by norm_num)
theorem B2218435 : Blo 2217435 2218435 := bstep (se 1 (by rfl) ⟨1663826, by rfl⟩ : syracuseStep 2218435 = 3327653) B3327653
theorem B2807713 : Blo 2217435 2807713 := bbase (se 2 (by rfl) ⟨1052892, by rfl⟩ : syracuseStep 2807713 = 2105785) (by norm_num)
theorem B3743617 : Blo 2217435 3743617 := bstep (se 2 (by rfl) ⟨1403856, by rfl⟩ : syracuseStep 3743617 = 2807713) B2807713
theorem B4991489 : Blo 2217435 4991489 := bstep (se 2 (by rfl) ⟨1871808, by rfl⟩ : syracuseStep 4991489 = 3743617) B3743617
theorem B3327659 : Blo 2217435 3327659 := bstep (se 1 (by rfl) ⟨2495744, by rfl⟩ : syracuseStep 3327659 = 4991489) B4991489
theorem B2218439 : Blo 2217435 2218439 := bstep (se 1 (by rfl) ⟨1663829, by rfl⟩ : syracuseStep 2218439 = 3327659) B3327659
theorem B2495749 : Blo 2217435 2495749 := bbase (se 4 (by rfl) ⟨233976, by rfl⟩ : syracuseStep 2495749 = 467953) (by norm_num)
theorem B3327665 : Blo 2217435 3327665 := bstep (se 2 (by rfl) ⟨1247874, by rfl⟩ : syracuseStep 3327665 = 2495749) B2495749
theorem B2218443 : Blo 2217435 2218443 := bstep (se 1 (by rfl) ⟨1663832, by rfl⟩ : syracuseStep 2218443 = 3327665) B3327665
theorem B2369017 : Blo 2217435 2369017 := bbase (se 2 (by rfl) ⟨888381, by rfl⟩ : syracuseStep 2369017 = 1776763) (by norm_num)
theorem B3158689 : Blo 2217435 3158689 := bstep (se 2 (by rfl) ⟨1184508, by rfl⟩ : syracuseStep 3158689 = 2369017) B2369017
theorem B4211585 : Blo 2217435 4211585 := bstep (se 2 (by rfl) ⟨1579344, by rfl⟩ : syracuseStep 4211585 = 3158689) B3158689
theorem B2807723 : Blo 2217435 2807723 := bstep (se 1 (by rfl) ⟨2105792, by rfl⟩ : syracuseStep 2807723 = 4211585) B4211585
theorem B7487261 : Blo 2217435 7487261 := bstep (se 3 (by rfl) ⟨1403861, by rfl⟩ : syracuseStep 7487261 = 2807723) B2807723
theorem B4991507 : Blo 2217435 4991507 := bstep (se 1 (by rfl) ⟨3743630, by rfl⟩ : syracuseStep 4991507 = 7487261) B7487261
theorem B3327671 : Blo 2217435 3327671 := bstep (se 1 (by rfl) ⟨2495753, by rfl⟩ : syracuseStep 3327671 = 4991507) B4991507
theorem B2218447 : Blo 2217435 2218447 := bstep (se 1 (by rfl) ⟨1663835, by rfl⟩ : syracuseStep 2218447 = 3327671) B3327671
theorem B3327677 : Blo 2217435 3327677 := bbase (se 3 (by rfl) ⟨623939, by rfl⟩ : syracuseStep 3327677 = 1247879) (by norm_num)
theorem B2218451 : Blo 2217435 2218451 := bstep (se 1 (by rfl) ⟨1663838, by rfl⟩ : syracuseStep 2218451 = 3327677) B3327677
theorem B4991525 : Blo 2217435 4991525 := bbase (se 4 (by rfl) ⟨467955, by rfl⟩ : syracuseStep 4991525 = 935911) (by norm_num)
theorem B3327683 : Blo 2217435 3327683 := bstep (se 1 (by rfl) ⟨2495762, by rfl⟩ : syracuseStep 3327683 = 4991525) B4991525
theorem B2218455 : Blo 2217435 2218455 := bstep (se 1 (by rfl) ⟨1663841, by rfl⟩ : syracuseStep 2218455 = 3327683) B3327683
theorem B5615477 : Blo 2217435 5615477 := bbase (se 5 (by rfl) ⟨263225, by rfl⟩ : syracuseStep 5615477 = 526451) (by norm_num)
theorem B3743651 : Blo 2217435 3743651 := bstep (se 1 (by rfl) ⟨2807738, by rfl⟩ : syracuseStep 3743651 = 5615477) B5615477
theorem B2495767 : Blo 2217435 2495767 := bstep (se 1 (by rfl) ⟨1871825, by rfl⟩ : syracuseStep 2495767 = 3743651) B3743651
theorem B3327689 : Blo 2217435 3327689 := bstep (se 2 (by rfl) ⟨1247883, by rfl⟩ : syracuseStep 3327689 = 2495767) B2495767
theorem B2218459 : Blo 2217435 2218459 := bstep (se 1 (by rfl) ⟨1663844, by rfl⟩ : syracuseStep 2218459 = 3327689) B3327689
theorem B7204069 : Blo 2217435 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B9605425 : Blo 2217435 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B12807233 : Blo 2217435 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B8538155 : Blo 2217435 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B5692103 : Blo 2217435 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B3794735 : Blo 2217435 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B10119293 : Blo 2217435 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B6746195 : Blo 2217435 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B4497463 : Blo 2217435 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B23986469 : Blo 2217435 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B15990979 : Blo 2217435 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B21321305 : Blo 2217435 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B14214203 : Blo 2217435 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B9476135 : Blo 2217435 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B6317423 : Blo 2217435 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B4211615 : Blo 2217435 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B11230973 : Blo 2217435 11230973 := bstep (se 3 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 11230973 = 4211615) B4211615
theorem B7487315 : Blo 2217435 7487315 := bstep (se 1 (by rfl) ⟨5615486, by rfl⟩ : syracuseStep 7487315 = 11230973) B11230973
theorem B4991543 : Blo 2217435 4991543 := bstep (se 1 (by rfl) ⟨3743657, by rfl⟩ : syracuseStep 4991543 = 7487315) B7487315
theorem B3327695 : Blo 2217435 3327695 := bstep (se 1 (by rfl) ⟨2495771, by rfl⟩ : syracuseStep 3327695 = 4991543) B4991543
theorem B2218463 : Blo 2217435 2218463 := bstep (se 1 (by rfl) ⟨1663847, by rfl⟩ : syracuseStep 2218463 = 3327695) B3327695
theorem B3327701 : Blo 2217435 3327701 := bbase (se 7 (by rfl) ⟨38996, by rfl⟩ : syracuseStep 3327701 = 77993) (by norm_num)
theorem B2218467 : Blo 2217435 2218467 := bstep (se 1 (by rfl) ⟨1663850, by rfl⟩ : syracuseStep 2218467 = 3327701) B3327701
theorem B4738085 : Blo 2217435 4738085 := bbase (se 4 (by rfl) ⟨444195, by rfl⟩ : syracuseStep 4738085 = 888391) (by norm_num)
theorem B3158723 : Blo 2217435 3158723 := bstep (se 1 (by rfl) ⟨2369042, by rfl⟩ : syracuseStep 3158723 = 4738085) B4738085
theorem B8423261 : Blo 2217435 8423261 := bstep (se 3 (by rfl) ⟨1579361, by rfl⟩ : syracuseStep 8423261 = 3158723) B3158723
theorem B5615507 : Blo 2217435 5615507 := bstep (se 1 (by rfl) ⟨4211630, by rfl⟩ : syracuseStep 5615507 = 8423261) B8423261
theorem B3743671 : Blo 2217435 3743671 := bstep (se 1 (by rfl) ⟨2807753, by rfl⟩ : syracuseStep 3743671 = 5615507) B5615507
theorem B4991561 : Blo 2217435 4991561 := bstep (se 2 (by rfl) ⟨1871835, by rfl⟩ : syracuseStep 4991561 = 3743671) B3743671
theorem B3327707 : Blo 2217435 3327707 := bstep (se 1 (by rfl) ⟨2495780, by rfl⟩ : syracuseStep 3327707 = 4991561) B4991561
theorem B2218471 : Blo 2217435 2218471 := bstep (se 1 (by rfl) ⟨1663853, by rfl⟩ : syracuseStep 2218471 = 3327707) B3327707
theorem B2495785 : Blo 2217435 2495785 := bbase (se 2 (by rfl) ⟨935919, by rfl⟩ : syracuseStep 2495785 = 1871839) (by norm_num)
theorem B3327713 : Blo 2217435 3327713 := bstep (se 2 (by rfl) ⟨1247892, by rfl⟩ : syracuseStep 3327713 = 2495785) B2495785
theorem B2218475 : Blo 2217435 2218475 := bstep (se 1 (by rfl) ⟨1663856, by rfl⟩ : syracuseStep 2218475 = 3327713) B3327713
theorem B2535133 : Blo 2217435 2535133 := bbase (se 3 (by rfl) ⟨475337, by rfl⟩ : syracuseStep 2535133 = 950675) (by norm_num)
theorem B3380177 : Blo 2217435 3380177 := bstep (se 2 (by rfl) ⟨1267566, by rfl⟩ : syracuseStep 3380177 = 2535133) B2535133
theorem B9013805 : Blo 2217435 9013805 := bstep (se 3 (by rfl) ⟨1690088, by rfl⟩ : syracuseStep 9013805 = 3380177) B3380177
theorem B6009203 : Blo 2217435 6009203 := bstep (se 1 (by rfl) ⟨4506902, by rfl⟩ : syracuseStep 6009203 = 9013805) B9013805
theorem B4006135 : Blo 2217435 4006135 := bstep (se 1 (by rfl) ⟨3004601, by rfl⟩ : syracuseStep 4006135 = 6009203) B6009203
theorem B5341513 : Blo 2217435 5341513 := bstep (se 2 (by rfl) ⟨2003067, by rfl⟩ : syracuseStep 5341513 = 4006135) B4006135
theorem B7122017 : Blo 2217435 7122017 := bstep (se 2 (by rfl) ⟨2670756, by rfl⟩ : syracuseStep 7122017 = 5341513) B5341513
theorem B18992045 : Blo 2217435 18992045 := bstep (se 3 (by rfl) ⟨3561008, by rfl⟩ : syracuseStep 18992045 = 7122017) B7122017
theorem B12661363 : Blo 2217435 12661363 := bstep (se 1 (by rfl) ⟨9496022, by rfl⟩ : syracuseStep 12661363 = 18992045) B18992045
theorem B67527269 : Blo 2217435 67527269 := bstep (se 4 (by rfl) ⟨6330681, by rfl⟩ : syracuseStep 67527269 = 12661363) B12661363
theorem B45018179 : Blo 2217435 45018179 := bstep (se 1 (by rfl) ⟨33763634, by rfl⟩ : syracuseStep 45018179 = 67527269) B67527269
theorem B30012119 : Blo 2217435 30012119 := bstep (se 1 (by rfl) ⟨22509089, by rfl⟩ : syracuseStep 30012119 = 45018179) B45018179
theorem B20008079 : Blo 2217435 20008079 := bstep (se 1 (by rfl) ⟨15006059, by rfl⟩ : syracuseStep 20008079 = 30012119) B30012119
theorem B13338719 : Blo 2217435 13338719 := bstep (se 1 (by rfl) ⟨10004039, by rfl⟩ : syracuseStep 13338719 = 20008079) B20008079
theorem B8892479 : Blo 2217435 8892479 := bstep (se 1 (by rfl) ⟨6669359, by rfl⟩ : syracuseStep 8892479 = 13338719) B13338719
theorem B5928319 : Blo 2217435 5928319 := bstep (se 1 (by rfl) ⟨4446239, by rfl⟩ : syracuseStep 5928319 = 8892479) B8892479
theorem B7904425 : Blo 2217435 7904425 := bstep (se 2 (by rfl) ⟨2964159, by rfl⟩ : syracuseStep 7904425 = 5928319) B5928319
theorem B10539233 : Blo 2217435 10539233 := bstep (se 2 (by rfl) ⟨3952212, by rfl⟩ : syracuseStep 10539233 = 7904425) B7904425
theorem B7026155 : Blo 2217435 7026155 := bstep (se 1 (by rfl) ⟨5269616, by rfl⟩ : syracuseStep 7026155 = 10539233) B10539233
theorem B4684103 : Blo 2217435 4684103 := bstep (se 1 (by rfl) ⟨3513077, by rfl⟩ : syracuseStep 4684103 = 7026155) B7026155
theorem B3122735 : Blo 2217435 3122735 := bstep (se 1 (by rfl) ⟨2342051, by rfl⟩ : syracuseStep 3122735 = 4684103) B4684103
theorem B8327293 : Blo 2217435 8327293 := bstep (se 3 (by rfl) ⟨1561367, by rfl⟩ : syracuseStep 8327293 = 3122735) B3122735
theorem B44412229 : Blo 2217435 44412229 := bstep (se 4 (by rfl) ⟨4163646, by rfl⟩ : syracuseStep 44412229 = 8327293) B8327293
theorem B236865221 : Blo 2217435 236865221 := bstep (se 4 (by rfl) ⟨22206114, by rfl⟩ : syracuseStep 236865221 = 44412229) B44412229
theorem B157910147 : Blo 2217435 157910147 := bstep (se 1 (by rfl) ⟨118432610, by rfl⟩ : syracuseStep 157910147 = 236865221) B236865221
theorem B105273431 : Blo 2217435 105273431 := bstep (se 1 (by rfl) ⟨78955073, by rfl⟩ : syracuseStep 105273431 = 157910147) B157910147
theorem B70182287 : Blo 2217435 70182287 := bstep (se 1 (by rfl) ⟨52636715, by rfl⟩ : syracuseStep 70182287 = 105273431) B105273431
theorem B46788191 : Blo 2217435 46788191 := bstep (se 1 (by rfl) ⟨35091143, by rfl⟩ : syracuseStep 46788191 = 70182287) B70182287
theorem B31192127 : Blo 2217435 31192127 := bstep (se 1 (by rfl) ⟨23394095, by rfl⟩ : syracuseStep 31192127 = 46788191) B46788191
theorem B20794751 : Blo 2217435 20794751 := bstep (se 1 (by rfl) ⟨15596063, by rfl⟩ : syracuseStep 20794751 = 31192127) B31192127
theorem B13863167 : Blo 2217435 13863167 := bstep (se 1 (by rfl) ⟨10397375, by rfl⟩ : syracuseStep 13863167 = 20794751) B20794751
theorem B9242111 : Blo 2217435 9242111 := bstep (se 1 (by rfl) ⟨6931583, by rfl⟩ : syracuseStep 9242111 = 13863167) B13863167
theorem B6161407 : Blo 2217435 6161407 := bstep (se 1 (by rfl) ⟨4621055, by rfl⟩ : syracuseStep 6161407 = 9242111) B9242111
theorem B32860837 : Blo 2217435 32860837 := bstep (se 4 (by rfl) ⟨3080703, by rfl⟩ : syracuseStep 32860837 = 6161407) B6161407
theorem B43814449 : Blo 2217435 43814449 := bstep (se 2 (by rfl) ⟨16430418, by rfl⟩ : syracuseStep 43814449 = 32860837) B32860837
theorem B58419265 : Blo 2217435 58419265 := bstep (se 2 (by rfl) ⟨21907224, by rfl⟩ : syracuseStep 58419265 = 43814449) B43814449
theorem B77892353 : Blo 2217435 77892353 := bstep (se 2 (by rfl) ⟨29209632, by rfl⟩ : syracuseStep 77892353 = 58419265) B58419265
theorem B51928235 : Blo 2217435 51928235 := bstep (se 1 (by rfl) ⟨38946176, by rfl⟩ : syracuseStep 51928235 = 77892353) B77892353
theorem B34618823 : Blo 2217435 34618823 := bstep (se 1 (by rfl) ⟨25964117, by rfl⟩ : syracuseStep 34618823 = 51928235) B51928235
theorem B23079215 : Blo 2217435 23079215 := bstep (se 1 (by rfl) ⟨17309411, by rfl⟩ : syracuseStep 23079215 = 34618823) B34618823
theorem B61544573 : Blo 2217435 61544573 := bstep (se 3 (by rfl) ⟨11539607, by rfl⟩ : syracuseStep 61544573 = 23079215) B23079215
theorem B41029715 : Blo 2217435 41029715 := bstep (se 1 (by rfl) ⟨30772286, by rfl⟩ : syracuseStep 41029715 = 61544573) B61544573
theorem B27353143 : Blo 2217435 27353143 := bstep (se 1 (by rfl) ⟨20514857, by rfl⟩ : syracuseStep 27353143 = 41029715) B41029715
theorem B36470857 : Blo 2217435 36470857 := bstep (se 2 (by rfl) ⟨13676571, by rfl⟩ : syracuseStep 36470857 = 27353143) B27353143
theorem B48627809 : Blo 2217435 48627809 := bstep (se 2 (by rfl) ⟨18235428, by rfl⟩ : syracuseStep 48627809 = 36470857) B36470857
theorem B32418539 : Blo 2217435 32418539 := bstep (se 1 (by rfl) ⟨24313904, by rfl⟩ : syracuseStep 32418539 = 48627809) B48627809
theorem B21612359 : Blo 2217435 21612359 := bstep (se 1 (by rfl) ⟨16209269, by rfl⟩ : syracuseStep 21612359 = 32418539) B32418539
theorem B14408239 : Blo 2217435 14408239 := bstep (se 1 (by rfl) ⟨10806179, by rfl⟩ : syracuseStep 14408239 = 21612359) B21612359
theorem B19210985 : Blo 2217435 19210985 := bstep (se 2 (by rfl) ⟨7204119, by rfl⟩ : syracuseStep 19210985 = 14408239) B14408239
theorem B12807323 : Blo 2217435 12807323 := bstep (se 1 (by rfl) ⟨9605492, by rfl⟩ : syracuseStep 12807323 = 19210985) B19210985
theorem B8538215 : Blo 2217435 8538215 := bstep (se 1 (by rfl) ⟨6403661, by rfl⟩ : syracuseStep 8538215 = 12807323) B12807323
theorem B22768573 : Blo 2217435 22768573 := bstep (se 3 (by rfl) ⟨4269107, by rfl⟩ : syracuseStep 22768573 = 8538215) B8538215
theorem B30358097 : Blo 2217435 30358097 := bstep (se 2 (by rfl) ⟨11384286, by rfl⟩ : syracuseStep 30358097 = 22768573) B22768573
theorem B20238731 : Blo 2217435 20238731 := bstep (se 1 (by rfl) ⟨15179048, by rfl⟩ : syracuseStep 20238731 = 30358097) B30358097
theorem B13492487 : Blo 2217435 13492487 := bstep (se 1 (by rfl) ⟨10119365, by rfl⟩ : syracuseStep 13492487 = 20238731) B20238731
theorem B8994991 : Blo 2217435 8994991 := bstep (se 1 (by rfl) ⟨6746243, by rfl⟩ : syracuseStep 8994991 = 13492487) B13492487
theorem B11993321 : Blo 2217435 11993321 := bstep (se 2 (by rfl) ⟨4497495, by rfl⟩ : syracuseStep 11993321 = 8994991) B8994991
theorem B7995547 : Blo 2217435 7995547 := bstep (se 1 (by rfl) ⟨5996660, by rfl⟩ : syracuseStep 7995547 = 11993321) B11993321
theorem B10660729 : Blo 2217435 10660729 := bstep (se 2 (by rfl) ⟨3997773, by rfl⟩ : syracuseStep 10660729 = 7995547) B7995547
theorem B14214305 : Blo 2217435 14214305 := bstep (se 2 (by rfl) ⟨5330364, by rfl⟩ : syracuseStep 14214305 = 10660729) B10660729
theorem B9476203 : Blo 2217435 9476203 := bstep (se 1 (by rfl) ⟨7107152, by rfl⟩ : syracuseStep 9476203 = 14214305) B14214305
theorem B12634937 : Blo 2217435 12634937 := bstep (se 2 (by rfl) ⟨4738101, by rfl⟩ : syracuseStep 12634937 = 9476203) B9476203
theorem B8423291 : Blo 2217435 8423291 := bstep (se 1 (by rfl) ⟨6317468, by rfl⟩ : syracuseStep 8423291 = 12634937) B12634937
theorem B5615527 : Blo 2217435 5615527 := bstep (se 1 (by rfl) ⟨4211645, by rfl⟩ : syracuseStep 5615527 = 8423291) B8423291
theorem B7487369 : Blo 2217435 7487369 := bstep (se 2 (by rfl) ⟨2807763, by rfl⟩ : syracuseStep 7487369 = 5615527) B5615527
theorem B4991579 : Blo 2217435 4991579 := bstep (se 1 (by rfl) ⟨3743684, by rfl⟩ : syracuseStep 4991579 = 7487369) B7487369
theorem B3327719 : Blo 2217435 3327719 := bstep (se 1 (by rfl) ⟨2495789, by rfl⟩ : syracuseStep 3327719 = 4991579) B4991579
theorem B2218479 : Blo 2217435 2218479 := bstep (se 1 (by rfl) ⟨1663859, by rfl⟩ : syracuseStep 2218479 = 3327719) B3327719
theorem B3327725 : Blo 2217435 3327725 := bbase (se 3 (by rfl) ⟨623948, by rfl⟩ : syracuseStep 3327725 = 1247897) (by norm_num)
theorem B2218483 : Blo 2217435 2218483 := bstep (se 1 (by rfl) ⟨1663862, by rfl⟩ : syracuseStep 2218483 = 3327725) B3327725
theorem B4991597 : Blo 2217435 4991597 := bbase (se 3 (by rfl) ⟨935924, by rfl⟩ : syracuseStep 4991597 = 1871849) (by norm_num)
theorem B3327731 : Blo 2217435 3327731 := bstep (se 1 (by rfl) ⟨2495798, by rfl⟩ : syracuseStep 3327731 = 4991597) B4991597
theorem B2218487 : Blo 2217435 2218487 := bstep (se 1 (by rfl) ⟨1663865, by rfl⟩ : syracuseStep 2218487 = 3327731) B3327731
theorem B4211669 : Blo 2217435 4211669 := bbase (se 7 (by rfl) ⟨49355, by rfl⟩ : syracuseStep 4211669 = 98711) (by norm_num)
theorem B2807779 : Blo 2217435 2807779 := bstep (se 1 (by rfl) ⟨2105834, by rfl⟩ : syracuseStep 2807779 = 4211669) B4211669
theorem B3743705 : Blo 2217435 3743705 := bstep (se 2 (by rfl) ⟨1403889, by rfl⟩ : syracuseStep 3743705 = 2807779) B2807779
theorem B2495803 : Blo 2217435 2495803 := bstep (se 1 (by rfl) ⟨1871852, by rfl⟩ : syracuseStep 2495803 = 3743705) B3743705
theorem B3327737 : Blo 2217435 3327737 := bstep (se 2 (by rfl) ⟨1247901, by rfl⟩ : syracuseStep 3327737 = 2495803) B2495803
theorem B2218491 : Blo 2217435 2218491 := bstep (se 1 (by rfl) ⟨1663868, by rfl⟩ : syracuseStep 2218491 = 3327737) B3327737
theorem B12807413 : Blo 2217435 12807413 := bbase (se 5 (by rfl) ⟨600347, by rfl⟩ : syracuseStep 12807413 = 1200695) (by norm_num)
theorem B8538275 : Blo 2217435 8538275 := bstep (se 1 (by rfl) ⟨6403706, by rfl⟩ : syracuseStep 8538275 = 12807413) B12807413
theorem B5692183 : Blo 2217435 5692183 := bstep (se 1 (by rfl) ⟨4269137, by rfl⟩ : syracuseStep 5692183 = 8538275) B8538275
theorem B30358309 : Blo 2217435 30358309 := bstep (se 4 (by rfl) ⟨2846091, by rfl⟩ : syracuseStep 30358309 = 5692183) B5692183
theorem B40477745 : Blo 2217435 40477745 := bstep (se 2 (by rfl) ⟨15179154, by rfl⟩ : syracuseStep 40477745 = 30358309) B30358309
theorem B26985163 : Blo 2217435 26985163 := bstep (se 1 (by rfl) ⟨20238872, by rfl⟩ : syracuseStep 26985163 = 40477745) B40477745
theorem B35980217 : Blo 2217435 35980217 := bstep (se 2 (by rfl) ⟨13492581, by rfl⟩ : syracuseStep 35980217 = 26985163) B26985163
theorem B23986811 : Blo 2217435 23986811 := bstep (se 1 (by rfl) ⟨17990108, by rfl⟩ : syracuseStep 23986811 = 35980217) B35980217
theorem B63964829 : Blo 2217435 63964829 := bstep (se 3 (by rfl) ⟨11993405, by rfl⟩ : syracuseStep 63964829 = 23986811) B23986811
theorem B42643219 : Blo 2217435 42643219 := bstep (se 1 (by rfl) ⟨31982414, by rfl⟩ : syracuseStep 42643219 = 63964829) B63964829
theorem B56857625 : Blo 2217435 56857625 := bstep (se 2 (by rfl) ⟨21321609, by rfl⟩ : syracuseStep 56857625 = 42643219) B42643219
theorem B37905083 : Blo 2217435 37905083 := bstep (se 1 (by rfl) ⟨28428812, by rfl⟩ : syracuseStep 37905083 = 56857625) B56857625
theorem B25270055 : Blo 2217435 25270055 := bstep (se 1 (by rfl) ⟨18952541, by rfl⟩ : syracuseStep 25270055 = 37905083) B37905083
theorem B16846703 : Blo 2217435 16846703 := bstep (se 1 (by rfl) ⟨12635027, by rfl⟩ : syracuseStep 16846703 = 25270055) B25270055
theorem B11231135 : Blo 2217435 11231135 := bstep (se 1 (by rfl) ⟨8423351, by rfl⟩ : syracuseStep 11231135 = 16846703) B16846703
theorem B7487423 : Blo 2217435 7487423 := bstep (se 1 (by rfl) ⟨5615567, by rfl⟩ : syracuseStep 7487423 = 11231135) B11231135
theorem B4991615 : Blo 2217435 4991615 := bstep (se 1 (by rfl) ⟨3743711, by rfl⟩ : syracuseStep 4991615 = 7487423) B7487423
theorem B3327743 : Blo 2217435 3327743 := bstep (se 1 (by rfl) ⟨2495807, by rfl⟩ : syracuseStep 3327743 = 4991615) B4991615
theorem B2218495 : Blo 2217435 2218495 := bstep (se 1 (by rfl) ⟨1663871, by rfl⟩ : syracuseStep 2218495 = 3327743) B3327743
theorem B3327749 : Blo 2217435 3327749 := bbase (se 4 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 3327749 = 623953) (by norm_num)
theorem B2218499 : Blo 2217435 2218499 := bstep (se 1 (by rfl) ⟨1663874, by rfl⟩ : syracuseStep 2218499 = 3327749) B3327749
theorem B3743725 : Blo 2217435 3743725 := bbase (se 3 (by rfl) ⟨701948, by rfl⟩ : syracuseStep 3743725 = 1403897) (by norm_num)
theorem B4991633 : Blo 2217435 4991633 := bstep (se 2 (by rfl) ⟨1871862, by rfl⟩ : syracuseStep 4991633 = 3743725) B3743725
theorem B3327755 : Blo 2217435 3327755 := bstep (se 1 (by rfl) ⟨2495816, by rfl⟩ : syracuseStep 3327755 = 4991633) B4991633
theorem B2218503 : Blo 2217435 2218503 := bstep (se 1 (by rfl) ⟨1663877, by rfl⟩ : syracuseStep 2218503 = 3327755) B3327755
theorem B2495821 : Blo 2217435 2495821 := bbase (se 3 (by rfl) ⟨467966, by rfl⟩ : syracuseStep 2495821 = 935933) (by norm_num)
theorem B3327761 : Blo 2217435 3327761 := bstep (se 2 (by rfl) ⟨1247910, by rfl⟩ : syracuseStep 3327761 = 2495821) B2495821
theorem B2218507 : Blo 2217435 2218507 := bstep (se 1 (by rfl) ⟨1663880, by rfl⟩ : syracuseStep 2218507 = 3327761) B3327761
theorem B7487477 : Blo 2217435 7487477 := bbase (se 5 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 7487477 = 701951) (by norm_num)
theorem B4991651 : Blo 2217435 4991651 := bstep (se 1 (by rfl) ⟨3743738, by rfl⟩ : syracuseStep 4991651 = 7487477) B7487477
theorem B3327767 : Blo 2217435 3327767 := bstep (se 1 (by rfl) ⟨2495825, by rfl⟩ : syracuseStep 3327767 = 4991651) B4991651
theorem B2218511 : Blo 2217435 2218511 := bstep (se 1 (by rfl) ⟨1663883, by rfl⟩ : syracuseStep 2218511 = 3327767) B3327767
theorem B3327773 : Blo 2217435 3327773 := bbase (se 3 (by rfl) ⟨623957, by rfl⟩ : syracuseStep 3327773 = 1247915) (by norm_num)
theorem B2218515 : Blo 2217435 2218515 := bstep (se 1 (by rfl) ⟨1663886, by rfl⟩ : syracuseStep 2218515 = 3327773) B3327773
theorem B4991669 : Blo 2217435 4991669 := bbase (se 5 (by rfl) ⟨233984, by rfl⟩ : syracuseStep 4991669 = 467969) (by norm_num)
theorem B3327779 : Blo 2217435 3327779 := bstep (se 1 (by rfl) ⟨2495834, by rfl⟩ : syracuseStep 3327779 = 4991669) B4991669
theorem B2218519 : Blo 2217435 2218519 := bstep (se 1 (by rfl) ⟨1663889, by rfl⟩ : syracuseStep 2218519 = 3327779) B3327779
theorem B12635189 : Blo 2217435 12635189 := bbase (se 5 (by rfl) ⟨592274, by rfl⟩ : syracuseStep 12635189 = 1184549) (by norm_num)
theorem B8423459 : Blo 2217435 8423459 := bstep (se 1 (by rfl) ⟨6317594, by rfl⟩ : syracuseStep 8423459 = 12635189) B12635189
theorem B5615639 : Blo 2217435 5615639 := bstep (se 1 (by rfl) ⟨4211729, by rfl⟩ : syracuseStep 5615639 = 8423459) B8423459
theorem B3743759 : Blo 2217435 3743759 := bstep (se 1 (by rfl) ⟨2807819, by rfl⟩ : syracuseStep 3743759 = 5615639) B5615639
theorem B2495839 : Blo 2217435 2495839 := bstep (se 1 (by rfl) ⟨1871879, by rfl⟩ : syracuseStep 2495839 = 3743759) B3743759
theorem B3327785 : Blo 2217435 3327785 := bstep (se 2 (by rfl) ⟨1247919, by rfl⟩ : syracuseStep 3327785 = 2495839) B2495839
theorem B2218523 : Blo 2217435 2218523 := bstep (se 1 (by rfl) ⟨1663892, by rfl⟩ : syracuseStep 2218523 = 3327785) B3327785
theorem B6317605 : Blo 2217435 6317605 := bbase (se 4 (by rfl) ⟨592275, by rfl⟩ : syracuseStep 6317605 = 1184551) (by norm_num)
theorem B8423473 : Blo 2217435 8423473 := bstep (se 2 (by rfl) ⟨3158802, by rfl⟩ : syracuseStep 8423473 = 6317605) B6317605
theorem B11231297 : Blo 2217435 11231297 := bstep (se 2 (by rfl) ⟨4211736, by rfl⟩ : syracuseStep 11231297 = 8423473) B8423473
theorem B7487531 : Blo 2217435 7487531 := bstep (se 1 (by rfl) ⟨5615648, by rfl⟩ : syracuseStep 7487531 = 11231297) B11231297
theorem B4991687 : Blo 2217435 4991687 := bstep (se 1 (by rfl) ⟨3743765, by rfl⟩ : syracuseStep 4991687 = 7487531) B7487531
theorem B3327791 : Blo 2217435 3327791 := bstep (se 1 (by rfl) ⟨2495843, by rfl⟩ : syracuseStep 3327791 = 4991687) B4991687
theorem B2218527 : Blo 2217435 2218527 := bstep (se 1 (by rfl) ⟨1663895, by rfl⟩ : syracuseStep 2218527 = 3327791) B3327791
theorem B3327797 : Blo 2217435 3327797 := bbase (se 5 (by rfl) ⟨155990, by rfl⟩ : syracuseStep 3327797 = 311981) (by norm_num)
theorem B2218531 : Blo 2217435 2218531 := bstep (se 1 (by rfl) ⟨1663898, by rfl⟩ : syracuseStep 2218531 = 3327797) B3327797
theorem B5615669 : Blo 2217435 5615669 := bbase (se 5 (by rfl) ⟨263234, by rfl⟩ : syracuseStep 5615669 = 526469) (by norm_num)
theorem B3743779 : Blo 2217435 3743779 := bstep (se 1 (by rfl) ⟨2807834, by rfl⟩ : syracuseStep 3743779 = 5615669) B5615669
theorem B4991705 : Blo 2217435 4991705 := bstep (se 2 (by rfl) ⟨1871889, by rfl⟩ : syracuseStep 4991705 = 3743779) B3743779
theorem B3327803 : Blo 2217435 3327803 := bstep (se 1 (by rfl) ⟨2495852, by rfl⟩ : syracuseStep 3327803 = 4991705) B4991705
theorem B2218535 : Blo 2217435 2218535 := bstep (se 1 (by rfl) ⟨1663901, by rfl⟩ : syracuseStep 2218535 = 3327803) B3327803
theorem B2495857 : Blo 2217435 2495857 := bbase (se 2 (by rfl) ⟨935946, by rfl⟩ : syracuseStep 2495857 = 1871893) (by norm_num)
theorem B3327809 : Blo 2217435 3327809 := bstep (se 2 (by rfl) ⟨1247928, by rfl⟩ : syracuseStep 3327809 = 2495857) B2495857
theorem B2218539 : Blo 2217435 2218539 := bstep (se 1 (by rfl) ⟨1663904, by rfl⟩ : syracuseStep 2218539 = 3327809) B3327809
theorem B2248813 : Blo 2217435 2248813 := bbase (se 3 (by rfl) ⟨421652, by rfl⟩ : syracuseStep 2248813 = 843305) (by norm_num)
theorem B11993669 : Blo 2217435 11993669 := bstep (se 4 (by rfl) ⟨1124406, by rfl⟩ : syracuseStep 11993669 = 2248813) B2248813
theorem B7995779 : Blo 2217435 7995779 := bstep (se 1 (by rfl) ⟨5996834, by rfl⟩ : syracuseStep 7995779 = 11993669) B11993669
theorem B5330519 : Blo 2217435 5330519 := bstep (se 1 (by rfl) ⟨3997889, by rfl⟩ : syracuseStep 5330519 = 7995779) B7995779
theorem B3553679 : Blo 2217435 3553679 := bstep (se 1 (by rfl) ⟨2665259, by rfl⟩ : syracuseStep 3553679 = 5330519) B5330519
theorem B9476477 : Blo 2217435 9476477 := bstep (se 3 (by rfl) ⟨1776839, by rfl⟩ : syracuseStep 9476477 = 3553679) B3553679
theorem B6317651 : Blo 2217435 6317651 := bstep (se 1 (by rfl) ⟨4738238, by rfl⟩ : syracuseStep 6317651 = 9476477) B9476477
theorem B4211767 : Blo 2217435 4211767 := bstep (se 1 (by rfl) ⟨3158825, by rfl⟩ : syracuseStep 4211767 = 6317651) B6317651
theorem B5615689 : Blo 2217435 5615689 := bstep (se 2 (by rfl) ⟨2105883, by rfl⟩ : syracuseStep 5615689 = 4211767) B4211767
theorem B7487585 : Blo 2217435 7487585 := bstep (se 2 (by rfl) ⟨2807844, by rfl⟩ : syracuseStep 7487585 = 5615689) B5615689
theorem B4991723 : Blo 2217435 4991723 := bstep (se 1 (by rfl) ⟨3743792, by rfl⟩ : syracuseStep 4991723 = 7487585) B7487585
theorem B3327815 : Blo 2217435 3327815 := bstep (se 1 (by rfl) ⟨2495861, by rfl⟩ : syracuseStep 3327815 = 4991723) B4991723
theorem B2218543 : Blo 2217435 2218543 := bstep (se 1 (by rfl) ⟨1663907, by rfl⟩ : syracuseStep 2218543 = 3327815) B3327815
theorem B3327821 : Blo 2217435 3327821 := bbase (se 3 (by rfl) ⟨623966, by rfl⟩ : syracuseStep 3327821 = 1247933) (by norm_num)
theorem B2218547 : Blo 2217435 2218547 := bstep (se 1 (by rfl) ⟨1663910, by rfl⟩ : syracuseStep 2218547 = 3327821) B3327821
theorem B4991741 : Blo 2217435 4991741 := bbase (se 3 (by rfl) ⟨935951, by rfl⟩ : syracuseStep 4991741 = 1871903) (by norm_num)
theorem B3327827 : Blo 2217435 3327827 := bstep (se 1 (by rfl) ⟨2495870, by rfl⟩ : syracuseStep 3327827 = 4991741) B4991741
theorem B2218551 : Blo 2217435 2218551 := bstep (se 1 (by rfl) ⟨1663913, by rfl⟩ : syracuseStep 2218551 = 3327827) B3327827
theorem B3743813 : Blo 2217435 3743813 := bbase (se 4 (by rfl) ⟨350982, by rfl⟩ : syracuseStep 3743813 = 701965) (by norm_num)
theorem B2495875 : Blo 2217435 2495875 := bstep (se 1 (by rfl) ⟨1871906, by rfl⟩ : syracuseStep 2495875 = 3743813) B3743813
theorem B3327833 : Blo 2217435 3327833 := bstep (se 2 (by rfl) ⟨1247937, by rfl⟩ : syracuseStep 3327833 = 2495875) B2495875
theorem B2218555 : Blo 2217435 2218555 := bstep (se 1 (by rfl) ⟨1663916, by rfl⟩ : syracuseStep 2218555 = 3327833) B3327833
theorem B16847189 : Blo 2217435 16847189 := bbase (se 10 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 16847189 = 49357) (by norm_num)
theorem B11231459 : Blo 2217435 11231459 := bstep (se 1 (by rfl) ⟨8423594, by rfl⟩ : syracuseStep 11231459 = 16847189) B16847189
theorem B7487639 : Blo 2217435 7487639 := bstep (se 1 (by rfl) ⟨5615729, by rfl⟩ : syracuseStep 7487639 = 11231459) B11231459
theorem B4991759 : Blo 2217435 4991759 := bstep (se 1 (by rfl) ⟨3743819, by rfl⟩ : syracuseStep 4991759 = 7487639) B7487639
theorem B3327839 : Blo 2217435 3327839 := bstep (se 1 (by rfl) ⟨2495879, by rfl⟩ : syracuseStep 3327839 = 4991759) B4991759
theorem B2218559 : Blo 2217435 2218559 := bstep (se 1 (by rfl) ⟨1663919, by rfl⟩ : syracuseStep 2218559 = 3327839) B3327839
theorem B3327845 : Blo 2217435 3327845 := bbase (se 4 (by rfl) ⟨311985, by rfl⟩ : syracuseStep 3327845 = 623971) (by norm_num)
theorem B2218563 : Blo 2217435 2218563 := bstep (se 1 (by rfl) ⟨1663922, by rfl⟩ : syracuseStep 2218563 = 3327845) B3327845
theorem B4211813 : Blo 2217435 4211813 := bbase (se 4 (by rfl) ⟨394857, by rfl⟩ : syracuseStep 4211813 = 789715) (by norm_num)
theorem B2807875 : Blo 2217435 2807875 := bstep (se 1 (by rfl) ⟨2105906, by rfl⟩ : syracuseStep 2807875 = 4211813) B4211813
theorem B3743833 : Blo 2217435 3743833 := bstep (se 2 (by rfl) ⟨1403937, by rfl⟩ : syracuseStep 3743833 = 2807875) B2807875
theorem B4991777 : Blo 2217435 4991777 := bstep (se 2 (by rfl) ⟨1871916, by rfl⟩ : syracuseStep 4991777 = 3743833) B3743833
theorem B3327851 : Blo 2217435 3327851 := bstep (se 1 (by rfl) ⟨2495888, by rfl⟩ : syracuseStep 3327851 = 4991777) B4991777
theorem B2218567 : Blo 2217435 2218567 := bstep (se 1 (by rfl) ⟨1663925, by rfl⟩ : syracuseStep 2218567 = 3327851) B3327851
theorem B2495893 : Blo 2217435 2495893 := bbase (se 6 (by rfl) ⟨58497, by rfl⟩ : syracuseStep 2495893 = 116995) (by norm_num)
theorem B3327857 : Blo 2217435 3327857 := bstep (se 2 (by rfl) ⟨1247946, by rfl⟩ : syracuseStep 3327857 = 2495893) B2495893
theorem B2218571 : Blo 2217435 2218571 := bstep (se 1 (by rfl) ⟨1663928, by rfl⟩ : syracuseStep 2218571 = 3327857) B3327857
theorem B2807885 : Blo 2217435 2807885 := bbase (se 3 (by rfl) ⟨526478, by rfl⟩ : syracuseStep 2807885 = 1052957) (by norm_num)
theorem B7487693 : Blo 2217435 7487693 := bstep (se 3 (by rfl) ⟨1403942, by rfl⟩ : syracuseStep 7487693 = 2807885) B2807885
theorem B4991795 : Blo 2217435 4991795 := bstep (se 1 (by rfl) ⟨3743846, by rfl⟩ : syracuseStep 4991795 = 7487693) B7487693
theorem B3327863 : Blo 2217435 3327863 := bstep (se 1 (by rfl) ⟨2495897, by rfl⟩ : syracuseStep 3327863 = 4991795) B4991795
theorem B2218575 : Blo 2217435 2218575 := bstep (se 1 (by rfl) ⟨1663931, by rfl⟩ : syracuseStep 2218575 = 3327863) B3327863
theorem B3327869 : Blo 2217435 3327869 := bbase (se 3 (by rfl) ⟨623975, by rfl⟩ : syracuseStep 3327869 = 1247951) (by norm_num)
theorem B2218579 : Blo 2217435 2218579 := bstep (se 1 (by rfl) ⟨1663934, by rfl⟩ : syracuseStep 2218579 = 3327869) B3327869
theorem B4991813 : Blo 2217435 4991813 := bbase (se 4 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 4991813 = 935965) (by norm_num)
theorem B3327875 : Blo 2217435 3327875 := bstep (se 1 (by rfl) ⟨2495906, by rfl⟩ : syracuseStep 3327875 = 4991813) B4991813
theorem B2218583 : Blo 2217435 2218583 := bstep (se 1 (by rfl) ⟨1663937, by rfl⟩ : syracuseStep 2218583 = 3327875) B3327875
theorem B4738333 : Blo 2217435 4738333 := bbase (se 3 (by rfl) ⟨888437, by rfl⟩ : syracuseStep 4738333 = 1776875) (by norm_num)
theorem B6317777 : Blo 2217435 6317777 := bstep (se 2 (by rfl) ⟨2369166, by rfl⟩ : syracuseStep 6317777 = 4738333) B4738333
theorem B4211851 : Blo 2217435 4211851 := bstep (se 1 (by rfl) ⟨3158888, by rfl⟩ : syracuseStep 4211851 = 6317777) B6317777
theorem B5615801 : Blo 2217435 5615801 := bstep (se 2 (by rfl) ⟨2105925, by rfl⟩ : syracuseStep 5615801 = 4211851) B4211851
theorem B3743867 : Blo 2217435 3743867 := bstep (se 1 (by rfl) ⟨2807900, by rfl⟩ : syracuseStep 3743867 = 5615801) B5615801
theorem B2495911 : Blo 2217435 2495911 := bstep (se 1 (by rfl) ⟨1871933, by rfl⟩ : syracuseStep 2495911 = 3743867) B3743867
theorem B3327881 : Blo 2217435 3327881 := bstep (se 2 (by rfl) ⟨1247955, by rfl⟩ : syracuseStep 3327881 = 2495911) B2495911
theorem B2218587 : Blo 2217435 2218587 := bstep (se 1 (by rfl) ⟨1663940, by rfl⟩ : syracuseStep 2218587 = 3327881) B3327881
theorem B11231621 : Blo 2217435 11231621 := bbase (se 4 (by rfl) ⟨1052964, by rfl⟩ : syracuseStep 11231621 = 2105929) (by norm_num)
theorem B7487747 : Blo 2217435 7487747 := bstep (se 1 (by rfl) ⟨5615810, by rfl⟩ : syracuseStep 7487747 = 11231621) B11231621
theorem B4991831 : Blo 2217435 4991831 := bstep (se 1 (by rfl) ⟨3743873, by rfl⟩ : syracuseStep 4991831 = 7487747) B7487747
theorem B3327887 : Blo 2217435 3327887 := bstep (se 1 (by rfl) ⟨2495915, by rfl⟩ : syracuseStep 3327887 = 4991831) B4991831
theorem B2218591 : Blo 2217435 2218591 := bstep (se 1 (by rfl) ⟨1663943, by rfl⟩ : syracuseStep 2218591 = 3327887) B3327887
theorem B3327893 : Blo 2217435 3327893 := bbase (se 6 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 3327893 = 155995) (by norm_num)
theorem B2218595 : Blo 2217435 2218595 := bstep (se 1 (by rfl) ⟨1663946, by rfl⟩ : syracuseStep 2218595 = 3327893) B3327893
theorem B4269341 : Blo 2217435 4269341 := bbase (se 3 (by rfl) ⟨800501, by rfl⟩ : syracuseStep 4269341 = 1601003) (by norm_num)
theorem B2846227 : Blo 2217435 2846227 := bstep (se 1 (by rfl) ⟨2134670, by rfl⟩ : syracuseStep 2846227 = 4269341) B4269341
theorem B3794969 : Blo 2217435 3794969 := bstep (se 2 (by rfl) ⟨1423113, by rfl⟩ : syracuseStep 3794969 = 2846227) B2846227
theorem B10119917 : Blo 2217435 10119917 := bstep (se 3 (by rfl) ⟨1897484, by rfl⟩ : syracuseStep 10119917 = 3794969) B3794969
theorem B6746611 : Blo 2217435 6746611 := bstep (se 1 (by rfl) ⟨5059958, by rfl⟩ : syracuseStep 6746611 = 10119917) B10119917
theorem B8995481 : Blo 2217435 8995481 := bstep (se 2 (by rfl) ⟨3373305, by rfl⟩ : syracuseStep 8995481 = 6746611) B6746611
theorem B5996987 : Blo 2217435 5996987 := bstep (se 1 (by rfl) ⟨4497740, by rfl⟩ : syracuseStep 5996987 = 8995481) B8995481
theorem B3997991 : Blo 2217435 3997991 := bstep (se 1 (by rfl) ⟨2998493, by rfl⟩ : syracuseStep 3997991 = 5996987) B5996987
theorem B2665327 : Blo 2217435 2665327 := bstep (se 1 (by rfl) ⟨1998995, by rfl⟩ : syracuseStep 2665327 = 3997991) B3997991
theorem B3553769 : Blo 2217435 3553769 := bstep (se 2 (by rfl) ⟨1332663, by rfl⟩ : syracuseStep 3553769 = 2665327) B2665327
theorem B2369179 : Blo 2217435 2369179 := bstep (se 1 (by rfl) ⟨1776884, by rfl⟩ : syracuseStep 2369179 = 3553769) B3553769
theorem B12635621 : Blo 2217435 12635621 := bstep (se 4 (by rfl) ⟨1184589, by rfl⟩ : syracuseStep 12635621 = 2369179) B2369179
theorem B8423747 : Blo 2217435 8423747 := bstep (se 1 (by rfl) ⟨6317810, by rfl⟩ : syracuseStep 8423747 = 12635621) B12635621
theorem B5615831 : Blo 2217435 5615831 := bstep (se 1 (by rfl) ⟨4211873, by rfl⟩ : syracuseStep 5615831 = 8423747) B8423747
theorem B3743887 : Blo 2217435 3743887 := bstep (se 1 (by rfl) ⟨2807915, by rfl⟩ : syracuseStep 3743887 = 5615831) B5615831
theorem B4991849 : Blo 2217435 4991849 := bstep (se 2 (by rfl) ⟨1871943, by rfl⟩ : syracuseStep 4991849 = 3743887) B3743887
theorem B3327899 : Blo 2217435 3327899 := bstep (se 1 (by rfl) ⟨2495924, by rfl⟩ : syracuseStep 3327899 = 4991849) B4991849
theorem B2218599 : Blo 2217435 2218599 := bstep (se 1 (by rfl) ⟨1663949, by rfl⟩ : syracuseStep 2218599 = 3327899) B3327899
theorem B2495929 : Blo 2217435 2495929 := bbase (se 2 (by rfl) ⟨935973, by rfl⟩ : syracuseStep 2495929 = 1871947) (by norm_num)
theorem B3327905 : Blo 2217435 3327905 := bstep (se 2 (by rfl) ⟨1247964, by rfl⟩ : syracuseStep 3327905 = 2495929) B2495929
theorem B2218603 : Blo 2217435 2218603 := bstep (se 1 (by rfl) ⟨1663952, by rfl⟩ : syracuseStep 2218603 = 3327905) B3327905
theorem B8538709 : Blo 2217435 8538709 := bbase (se 8 (by rfl) ⟨50031, by rfl⟩ : syracuseStep 8538709 = 100063) (by norm_num)
theorem B11384945 : Blo 2217435 11384945 := bstep (se 2 (by rfl) ⟨4269354, by rfl⟩ : syracuseStep 11384945 = 8538709) B8538709
theorem B7589963 : Blo 2217435 7589963 := bstep (se 1 (by rfl) ⟨5692472, by rfl⟩ : syracuseStep 7589963 = 11384945) B11384945
theorem B20239901 : Blo 2217435 20239901 := bstep (se 3 (by rfl) ⟨3794981, by rfl⟩ : syracuseStep 20239901 = 7589963) B7589963
theorem B13493267 : Blo 2217435 13493267 := bstep (se 1 (by rfl) ⟨10119950, by rfl⟩ : syracuseStep 13493267 = 20239901) B20239901
theorem B8995511 : Blo 2217435 8995511 := bstep (se 1 (by rfl) ⟨6746633, by rfl⟩ : syracuseStep 8995511 = 13493267) B13493267
theorem B5997007 : Blo 2217435 5997007 := bstep (se 1 (by rfl) ⟨4497755, by rfl⟩ : syracuseStep 5997007 = 8995511) B8995511
theorem B7996009 : Blo 2217435 7996009 := bstep (se 2 (by rfl) ⟨2998503, by rfl⟩ : syracuseStep 7996009 = 5997007) B5997007
theorem B10661345 : Blo 2217435 10661345 := bstep (se 2 (by rfl) ⟨3998004, by rfl⟩ : syracuseStep 10661345 = 7996009) B7996009
theorem B7107563 : Blo 2217435 7107563 := bstep (se 1 (by rfl) ⟨5330672, by rfl⟩ : syracuseStep 7107563 = 10661345) B10661345
theorem B4738375 : Blo 2217435 4738375 := bstep (se 1 (by rfl) ⟨3553781, by rfl⟩ : syracuseStep 4738375 = 7107563) B7107563
theorem B6317833 : Blo 2217435 6317833 := bstep (se 2 (by rfl) ⟨2369187, by rfl⟩ : syracuseStep 6317833 = 4738375) B4738375
theorem B8423777 : Blo 2217435 8423777 := bstep (se 2 (by rfl) ⟨3158916, by rfl⟩ : syracuseStep 8423777 = 6317833) B6317833
theorem B5615851 : Blo 2217435 5615851 := bstep (se 1 (by rfl) ⟨4211888, by rfl⟩ : syracuseStep 5615851 = 8423777) B8423777
theorem B7487801 : Blo 2217435 7487801 := bstep (se 2 (by rfl) ⟨2807925, by rfl⟩ : syracuseStep 7487801 = 5615851) B5615851
theorem B4991867 : Blo 2217435 4991867 := bstep (se 1 (by rfl) ⟨3743900, by rfl⟩ : syracuseStep 4991867 = 7487801) B7487801
theorem B3327911 : Blo 2217435 3327911 := bstep (se 1 (by rfl) ⟨2495933, by rfl⟩ : syracuseStep 3327911 = 4991867) B4991867
theorem B2218607 : Blo 2217435 2218607 := bstep (se 1 (by rfl) ⟨1663955, by rfl⟩ : syracuseStep 2218607 = 3327911) B3327911
theorem B3327917 : Blo 2217435 3327917 := bbase (se 3 (by rfl) ⟨623984, by rfl⟩ : syracuseStep 3327917 = 1247969) (by norm_num)
theorem B2218611 : Blo 2217435 2218611 := bstep (se 1 (by rfl) ⟨1663958, by rfl⟩ : syracuseStep 2218611 = 3327917) B3327917
theorem B4991885 : Blo 2217435 4991885 := bbase (se 3 (by rfl) ⟨935978, by rfl⟩ : syracuseStep 4991885 = 1871957) (by norm_num)
theorem B3327923 : Blo 2217435 3327923 := bstep (se 1 (by rfl) ⟨2495942, by rfl⟩ : syracuseStep 3327923 = 4991885) B4991885
theorem B2218615 : Blo 2217435 2218615 := bstep (se 1 (by rfl) ⟨1663961, by rfl⟩ : syracuseStep 2218615 = 3327923) B3327923
theorem B2807941 : Blo 2217435 2807941 := bbase (se 4 (by rfl) ⟨263244, by rfl⟩ : syracuseStep 2807941 = 526489) (by norm_num)
theorem B3743921 : Blo 2217435 3743921 := bstep (se 2 (by rfl) ⟨1403970, by rfl⟩ : syracuseStep 3743921 = 2807941) B2807941
theorem B2495947 : Blo 2217435 2495947 := bstep (se 1 (by rfl) ⟨1871960, by rfl⟩ : syracuseStep 2495947 = 3743921) B3743921
theorem B3327929 : Blo 2217435 3327929 := bstep (se 2 (by rfl) ⟨1247973, by rfl⟩ : syracuseStep 3327929 = 2495947) B2495947
theorem B2218619 : Blo 2217435 2218619 := bstep (se 1 (by rfl) ⟨1663964, by rfl⟩ : syracuseStep 2218619 = 3327929) B3327929
theorem B2998525 : Blo 2217435 2998525 := bbase (se 3 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 2998525 = 1124447) (by norm_num)
theorem B3998033 : Blo 2217435 3998033 := bstep (se 2 (by rfl) ⟨1499262, by rfl⟩ : syracuseStep 3998033 = 2998525) B2998525
theorem B2665355 : Blo 2217435 2665355 := bstep (se 1 (by rfl) ⟨1999016, by rfl⟩ : syracuseStep 2665355 = 3998033) B3998033
theorem B28430453 : Blo 2217435 28430453 := bstep (se 5 (by rfl) ⟨1332677, by rfl⟩ : syracuseStep 28430453 = 2665355) B2665355
theorem B18953635 : Blo 2217435 18953635 := bstep (se 1 (by rfl) ⟨14215226, by rfl⟩ : syracuseStep 18953635 = 28430453) B28430453
theorem B25271513 : Blo 2217435 25271513 := bstep (se 2 (by rfl) ⟨9476817, by rfl⟩ : syracuseStep 25271513 = 18953635) B18953635
theorem B16847675 : Blo 2217435 16847675 := bstep (se 1 (by rfl) ⟨12635756, by rfl⟩ : syracuseStep 16847675 = 25271513) B25271513
theorem B11231783 : Blo 2217435 11231783 := bstep (se 1 (by rfl) ⟨8423837, by rfl⟩ : syracuseStep 11231783 = 16847675) B16847675
theorem B7487855 : Blo 2217435 7487855 := bstep (se 1 (by rfl) ⟨5615891, by rfl⟩ : syracuseStep 7487855 = 11231783) B11231783
theorem B4991903 : Blo 2217435 4991903 := bstep (se 1 (by rfl) ⟨3743927, by rfl⟩ : syracuseStep 4991903 = 7487855) B7487855
theorem B3327935 : Blo 2217435 3327935 := bstep (se 1 (by rfl) ⟨2495951, by rfl⟩ : syracuseStep 3327935 = 4991903) B4991903
theorem B2218623 : Blo 2217435 2218623 := bstep (se 1 (by rfl) ⟨1663967, by rfl⟩ : syracuseStep 2218623 = 3327935) B3327935
theorem B3327941 : Blo 2217435 3327941 := bbase (se 4 (by rfl) ⟨311994, by rfl⟩ : syracuseStep 3327941 = 623989) (by norm_num)
theorem B2218627 : Blo 2217435 2218627 := bstep (se 1 (by rfl) ⟨1663970, by rfl⟩ : syracuseStep 2218627 = 3327941) B3327941
theorem B3743941 : Blo 2217435 3743941 := bbase (se 4 (by rfl) ⟨350994, by rfl⟩ : syracuseStep 3743941 = 701989) (by norm_num)
theorem B4991921 : Blo 2217435 4991921 := bstep (se 2 (by rfl) ⟨1871970, by rfl⟩ : syracuseStep 4991921 = 3743941) B3743941
theorem B3327947 : Blo 2217435 3327947 := bstep (se 1 (by rfl) ⟨2495960, by rfl⟩ : syracuseStep 3327947 = 4991921) B4991921
theorem B2218631 : Blo 2217435 2218631 := bstep (se 1 (by rfl) ⟨1663973, by rfl⟩ : syracuseStep 2218631 = 3327947) B3327947
theorem B2495965 : Blo 2217435 2495965 := bbase (se 3 (by rfl) ⟨467993, by rfl⟩ : syracuseStep 2495965 = 935987) (by norm_num)
theorem B3327953 : Blo 2217435 3327953 := bstep (se 2 (by rfl) ⟨1247982, by rfl⟩ : syracuseStep 3327953 = 2495965) B2495965
theorem B2218635 : Blo 2217435 2218635 := bstep (se 1 (by rfl) ⟨1663976, by rfl⟩ : syracuseStep 2218635 = 3327953) B3327953
theorem B7487909 : Blo 2217435 7487909 := bbase (se 4 (by rfl) ⟨701991, by rfl⟩ : syracuseStep 7487909 = 1403983) (by norm_num)
theorem B4991939 : Blo 2217435 4991939 := bstep (se 1 (by rfl) ⟨3743954, by rfl⟩ : syracuseStep 4991939 = 7487909) B7487909
theorem B3327959 : Blo 2217435 3327959 := bstep (se 1 (by rfl) ⟨2495969, by rfl⟩ : syracuseStep 3327959 = 4991939) B4991939
theorem B2218639 : Blo 2217435 2218639 := bstep (se 1 (by rfl) ⟨1663979, by rfl⟩ : syracuseStep 2218639 = 3327959) B3327959
theorem B3327965 : Blo 2217435 3327965 := bbase (se 3 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 3327965 = 1247987) (by norm_num)
theorem B2218643 : Blo 2217435 2218643 := bstep (se 1 (by rfl) ⟨1663982, by rfl⟩ : syracuseStep 2218643 = 3327965) B3327965
theorem B4991957 : Blo 2217435 4991957 := bbase (se 7 (by rfl) ⟨58499, by rfl⟩ : syracuseStep 4991957 = 116999) (by norm_num)
theorem B3327971 : Blo 2217435 3327971 := bstep (se 1 (by rfl) ⟨2495978, by rfl⟩ : syracuseStep 3327971 = 4991957) B4991957
theorem B2218647 : Blo 2217435 2218647 := bstep (se 1 (by rfl) ⟨1663985, by rfl⟩ : syracuseStep 2218647 = 3327971) B3327971
theorem B10661557 : Blo 2217435 10661557 := bbase (se 5 (by rfl) ⟨499760, by rfl⟩ : syracuseStep 10661557 = 999521) (by norm_num)
theorem B14215409 : Blo 2217435 14215409 := bstep (se 2 (by rfl) ⟨5330778, by rfl⟩ : syracuseStep 14215409 = 10661557) B10661557
theorem B9476939 : Blo 2217435 9476939 := bstep (se 1 (by rfl) ⟨7107704, by rfl⟩ : syracuseStep 9476939 = 14215409) B14215409
theorem B6317959 : Blo 2217435 6317959 := bstep (se 1 (by rfl) ⟨4738469, by rfl⟩ : syracuseStep 6317959 = 9476939) B9476939
theorem B8423945 : Blo 2217435 8423945 := bstep (se 2 (by rfl) ⟨3158979, by rfl⟩ : syracuseStep 8423945 = 6317959) B6317959
theorem B5615963 : Blo 2217435 5615963 := bstep (se 1 (by rfl) ⟨4211972, by rfl⟩ : syracuseStep 5615963 = 8423945) B8423945
theorem B3743975 : Blo 2217435 3743975 := bstep (se 1 (by rfl) ⟨2807981, by rfl⟩ : syracuseStep 3743975 = 5615963) B5615963
theorem B2495983 : Blo 2217435 2495983 := bstep (se 1 (by rfl) ⟨1871987, by rfl⟩ : syracuseStep 2495983 = 3743975) B3743975
theorem B3327977 : Blo 2217435 3327977 := bstep (se 2 (by rfl) ⟨1247991, by rfl⟩ : syracuseStep 3327977 = 2495983) B2495983
theorem B2218651 : Blo 2217435 2218651 := bstep (se 1 (by rfl) ⟨1663988, by rfl⟩ : syracuseStep 2218651 = 3327977) B3327977
theorem B18953909 : Blo 2217435 18953909 := bbase (se 5 (by rfl) ⟨888464, by rfl⟩ : syracuseStep 18953909 = 1776929) (by norm_num)
theorem B12635939 : Blo 2217435 12635939 := bstep (se 1 (by rfl) ⟨9476954, by rfl⟩ : syracuseStep 12635939 = 18953909) B18953909
theorem B8423959 : Blo 2217435 8423959 := bstep (se 1 (by rfl) ⟨6317969, by rfl⟩ : syracuseStep 8423959 = 12635939) B12635939
theorem B11231945 : Blo 2217435 11231945 := bstep (se 2 (by rfl) ⟨4211979, by rfl⟩ : syracuseStep 11231945 = 8423959) B8423959
theorem B7487963 : Blo 2217435 7487963 := bstep (se 1 (by rfl) ⟨5615972, by rfl⟩ : syracuseStep 7487963 = 11231945) B11231945
theorem B4991975 : Blo 2217435 4991975 := bstep (se 1 (by rfl) ⟨3743981, by rfl⟩ : syracuseStep 4991975 = 7487963) B7487963
theorem B3327983 : Blo 2217435 3327983 := bstep (se 1 (by rfl) ⟨2495987, by rfl⟩ : syracuseStep 3327983 = 4991975) B4991975
theorem B2218655 : Blo 2217435 2218655 := bstep (se 1 (by rfl) ⟨1663991, by rfl⟩ : syracuseStep 2218655 = 3327983) B3327983
theorem B3327989 : Blo 2217435 3327989 := bbase (se 5 (by rfl) ⟨155999, by rfl⟩ : syracuseStep 3327989 = 311999) (by norm_num)
theorem B2218659 : Blo 2217435 2218659 := bstep (se 1 (by rfl) ⟨1663994, by rfl⟩ : syracuseStep 2218659 = 3327989) B3327989
theorem B4935101 : Blo 2217435 4935101 := bbase (se 3 (by rfl) ⟨925331, by rfl⟩ : syracuseStep 4935101 = 1850663) (by norm_num)
theorem B13160269 : Blo 2217435 13160269 := bstep (se 3 (by rfl) ⟨2467550, by rfl⟩ : syracuseStep 13160269 = 4935101) B4935101
theorem B17547025 : Blo 2217435 17547025 := bstep (se 2 (by rfl) ⟨6580134, by rfl⟩ : syracuseStep 17547025 = 13160269) B13160269
theorem B23396033 : Blo 2217435 23396033 := bstep (se 2 (by rfl) ⟨8773512, by rfl⟩ : syracuseStep 23396033 = 17547025) B17547025
theorem B62389421 : Blo 2217435 62389421 := bstep (se 3 (by rfl) ⟨11698016, by rfl⟩ : syracuseStep 62389421 = 23396033) B23396033
theorem B41592947 : Blo 2217435 41592947 := bstep (se 1 (by rfl) ⟨31194710, by rfl⟩ : syracuseStep 41592947 = 62389421) B62389421
theorem B110914525 : Blo 2217435 110914525 := bstep (se 3 (by rfl) ⟨20796473, by rfl⟩ : syracuseStep 110914525 = 41592947) B41592947
theorem B147886033 : Blo 2217435 147886033 := bstep (se 2 (by rfl) ⟨55457262, by rfl⟩ : syracuseStep 147886033 = 110914525) B110914525
theorem B197181377 : Blo 2217435 197181377 := bstep (se 2 (by rfl) ⟨73943016, by rfl⟩ : syracuseStep 197181377 = 147886033) B147886033
theorem B131454251 : Blo 2217435 131454251 := bstep (se 1 (by rfl) ⟨98590688, by rfl⟩ : syracuseStep 131454251 = 197181377) B197181377
theorem B87636167 : Blo 2217435 87636167 := bstep (se 1 (by rfl) ⟨65727125, by rfl⟩ : syracuseStep 87636167 = 131454251) B131454251
theorem B58424111 : Blo 2217435 58424111 := bstep (se 1 (by rfl) ⟨43818083, by rfl⟩ : syracuseStep 58424111 = 87636167) B87636167
theorem B38949407 : Blo 2217435 38949407 := bstep (se 1 (by rfl) ⟨29212055, by rfl⟩ : syracuseStep 38949407 = 58424111) B58424111
theorem B25966271 : Blo 2217435 25966271 := bstep (se 1 (by rfl) ⟨19474703, by rfl⟩ : syracuseStep 25966271 = 38949407) B38949407
theorem B17310847 : Blo 2217435 17310847 := bstep (se 1 (by rfl) ⟨12983135, by rfl⟩ : syracuseStep 17310847 = 25966271) B25966271
theorem B23081129 : Blo 2217435 23081129 := bstep (se 2 (by rfl) ⟨8655423, by rfl⟩ : syracuseStep 23081129 = 17310847) B17310847
theorem B15387419 : Blo 2217435 15387419 := bstep (se 1 (by rfl) ⟨11540564, by rfl⟩ : syracuseStep 15387419 = 23081129) B23081129
theorem B41033117 : Blo 2217435 41033117 := bstep (se 3 (by rfl) ⟨7693709, by rfl⟩ : syracuseStep 41033117 = 15387419) B15387419
theorem B27355411 : Blo 2217435 27355411 := bstep (se 1 (by rfl) ⟨20516558, by rfl⟩ : syracuseStep 27355411 = 41033117) B41033117
theorem B36473881 : Blo 2217435 36473881 := bstep (se 2 (by rfl) ⟨13677705, by rfl⟩ : syracuseStep 36473881 = 27355411) B27355411
theorem B48631841 : Blo 2217435 48631841 := bstep (se 2 (by rfl) ⟨18236940, by rfl⟩ : syracuseStep 48631841 = 36473881) B36473881
theorem B32421227 : Blo 2217435 32421227 := bstep (se 1 (by rfl) ⟨24315920, by rfl⟩ : syracuseStep 32421227 = 48631841) B48631841
theorem B86456605 : Blo 2217435 86456605 := bstep (se 3 (by rfl) ⟨16210613, by rfl⟩ : syracuseStep 86456605 = 32421227) B32421227
theorem B115275473 : Blo 2217435 115275473 := bstep (se 2 (by rfl) ⟨43228302, by rfl⟩ : syracuseStep 115275473 = 86456605) B86456605
theorem B76850315 : Blo 2217435 76850315 := bstep (se 1 (by rfl) ⟨57637736, by rfl⟩ : syracuseStep 76850315 = 115275473) B115275473
theorem B51233543 : Blo 2217435 51233543 := bstep (se 1 (by rfl) ⟨38425157, by rfl⟩ : syracuseStep 51233543 = 76850315) B76850315
theorem B34155695 : Blo 2217435 34155695 := bstep (se 1 (by rfl) ⟨25616771, by rfl⟩ : syracuseStep 34155695 = 51233543) B51233543
theorem B91081853 : Blo 2217435 91081853 := bstep (se 3 (by rfl) ⟨17077847, by rfl⟩ : syracuseStep 91081853 = 34155695) B34155695
theorem B60721235 : Blo 2217435 60721235 := bstep (se 1 (by rfl) ⟨45540926, by rfl⟩ : syracuseStep 60721235 = 91081853) B91081853
theorem B40480823 : Blo 2217435 40480823 := bstep (se 1 (by rfl) ⟨30360617, by rfl⟩ : syracuseStep 40480823 = 60721235) B60721235
theorem B26987215 : Blo 2217435 26987215 := bstep (se 1 (by rfl) ⟨20240411, by rfl⟩ : syracuseStep 26987215 = 40480823) B40480823
theorem B35982953 : Blo 2217435 35982953 := bstep (se 2 (by rfl) ⟨13493607, by rfl⟩ : syracuseStep 35982953 = 26987215) B26987215
theorem B23988635 : Blo 2217435 23988635 := bstep (se 1 (by rfl) ⟨17991476, by rfl⟩ : syracuseStep 23988635 = 35982953) B35982953
theorem B15992423 : Blo 2217435 15992423 := bstep (se 1 (by rfl) ⟨11994317, by rfl⟩ : syracuseStep 15992423 = 23988635) B23988635
theorem B10661615 : Blo 2217435 10661615 := bstep (se 1 (by rfl) ⟨7996211, by rfl⟩ : syracuseStep 10661615 = 15992423) B15992423
theorem B7107743 : Blo 2217435 7107743 := bstep (se 1 (by rfl) ⟨5330807, by rfl⟩ : syracuseStep 7107743 = 10661615) B10661615
theorem B4738495 : Blo 2217435 4738495 := bstep (se 1 (by rfl) ⟨3553871, by rfl⟩ : syracuseStep 4738495 = 7107743) B7107743
theorem B6317993 : Blo 2217435 6317993 := bstep (se 2 (by rfl) ⟨2369247, by rfl⟩ : syracuseStep 6317993 = 4738495) B4738495
theorem B4211995 : Blo 2217435 4211995 := bstep (se 1 (by rfl) ⟨3158996, by rfl⟩ : syracuseStep 4211995 = 6317993) B6317993
theorem B5615993 : Blo 2217435 5615993 := bstep (se 2 (by rfl) ⟨2105997, by rfl⟩ : syracuseStep 5615993 = 4211995) B4211995
theorem B3743995 : Blo 2217435 3743995 := bstep (se 1 (by rfl) ⟨2807996, by rfl⟩ : syracuseStep 3743995 = 5615993) B5615993
theorem B4991993 : Blo 2217435 4991993 := bstep (se 2 (by rfl) ⟨1871997, by rfl⟩ : syracuseStep 4991993 = 3743995) B3743995
theorem B3327995 : Blo 2217435 3327995 := bstep (se 1 (by rfl) ⟨2495996, by rfl⟩ : syracuseStep 3327995 = 4991993) B4991993
theorem B2218663 : Blo 2217435 2218663 := bstep (se 1 (by rfl) ⟨1663997, by rfl⟩ : syracuseStep 2218663 = 3327995) B3327995
theorem B2496001 : Blo 2217435 2496001 := bbase (se 2 (by rfl) ⟨936000, by rfl⟩ : syracuseStep 2496001 = 1872001) (by norm_num)
theorem B3328001 : Blo 2217435 3328001 := bstep (se 2 (by rfl) ⟨1248000, by rfl⟩ : syracuseStep 3328001 = 2496001) B2496001
theorem B2218667 : Blo 2217435 2218667 := bstep (se 1 (by rfl) ⟨1664000, by rfl⟩ : syracuseStep 2218667 = 3328001) B3328001
theorem B5616013 : Blo 2217435 5616013 := bbase (se 3 (by rfl) ⟨1053002, by rfl⟩ : syracuseStep 5616013 = 2106005) (by norm_num)
theorem B7488017 : Blo 2217435 7488017 := bstep (se 2 (by rfl) ⟨2808006, by rfl⟩ : syracuseStep 7488017 = 5616013) B5616013
theorem B4992011 : Blo 2217435 4992011 := bstep (se 1 (by rfl) ⟨3744008, by rfl⟩ : syracuseStep 4992011 = 7488017) B7488017
theorem B3328007 : Blo 2217435 3328007 := bstep (se 1 (by rfl) ⟨2496005, by rfl⟩ : syracuseStep 3328007 = 4992011) B4992011
theorem B2218671 : Blo 2217435 2218671 := bstep (se 1 (by rfl) ⟨1664003, by rfl⟩ : syracuseStep 2218671 = 3328007) B3328007
theorem B3328013 : Blo 2217435 3328013 := bbase (se 3 (by rfl) ⟨624002, by rfl⟩ : syracuseStep 3328013 = 1248005) (by norm_num)
theorem B2218675 : Blo 2217435 2218675 := bstep (se 1 (by rfl) ⟨1664006, by rfl⟩ : syracuseStep 2218675 = 3328013) B3328013
theorem B4992029 : Blo 2217435 4992029 := bbase (se 3 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 4992029 = 1872011) (by norm_num)
theorem B3328019 : Blo 2217435 3328019 := bstep (se 1 (by rfl) ⟨2496014, by rfl⟩ : syracuseStep 3328019 = 4992029) B4992029
theorem B2218679 : Blo 2217435 2218679 := bstep (se 1 (by rfl) ⟨1664009, by rfl⟩ : syracuseStep 2218679 = 3328019) B3328019
theorem B3744029 : Blo 2217435 3744029 := bbase (se 3 (by rfl) ⟨702005, by rfl⟩ : syracuseStep 3744029 = 1404011) (by norm_num)
theorem B2496019 : Blo 2217435 2496019 := bstep (se 1 (by rfl) ⟨1872014, by rfl⟩ : syracuseStep 2496019 = 3744029) B3744029
theorem B3328025 : Blo 2217435 3328025 := bstep (se 2 (by rfl) ⟨1248009, by rfl⟩ : syracuseStep 3328025 = 2496019) B2496019
theorem B2218683 : Blo 2217435 2218683 := bstep (se 1 (by rfl) ⟨1664012, by rfl⟩ : syracuseStep 2218683 = 3328025) B3328025
theorem B14215637 : Blo 2217435 14215637 := bbase (se 7 (by rfl) ⟨166589, by rfl⟩ : syracuseStep 14215637 = 333179) (by norm_num)
theorem B9477091 : Blo 2217435 9477091 := bstep (se 1 (by rfl) ⟨7107818, by rfl⟩ : syracuseStep 9477091 = 14215637) B14215637
theorem B12636121 : Blo 2217435 12636121 := bstep (se 2 (by rfl) ⟨4738545, by rfl⟩ : syracuseStep 12636121 = 9477091) B9477091
theorem B16848161 : Blo 2217435 16848161 := bstep (se 2 (by rfl) ⟨6318060, by rfl⟩ : syracuseStep 16848161 = 12636121) B12636121
theorem B11232107 : Blo 2217435 11232107 := bstep (se 1 (by rfl) ⟨8424080, by rfl⟩ : syracuseStep 11232107 = 16848161) B16848161
theorem B7488071 : Blo 2217435 7488071 := bstep (se 1 (by rfl) ⟨5616053, by rfl⟩ : syracuseStep 7488071 = 11232107) B11232107
theorem B4992047 : Blo 2217435 4992047 := bstep (se 1 (by rfl) ⟨3744035, by rfl⟩ : syracuseStep 4992047 = 7488071) B7488071
theorem B3328031 : Blo 2217435 3328031 := bstep (se 1 (by rfl) ⟨2496023, by rfl⟩ : syracuseStep 3328031 = 4992047) B4992047
theorem B2218687 : Blo 2217435 2218687 := bstep (se 1 (by rfl) ⟨1664015, by rfl⟩ : syracuseStep 2218687 = 3328031) B3328031
theorem B3328037 : Blo 2217435 3328037 := bbase (se 4 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 3328037 = 624007) (by norm_num)
theorem B2218691 : Blo 2217435 2218691 := bstep (se 1 (by rfl) ⟨1664018, by rfl⟩ : syracuseStep 2218691 = 3328037) B3328037
theorem B2808037 : Blo 2217435 2808037 := bbase (se 4 (by rfl) ⟨263253, by rfl⟩ : syracuseStep 2808037 = 526507) (by norm_num)
theorem B3744049 : Blo 2217435 3744049 := bstep (se 2 (by rfl) ⟨1404018, by rfl⟩ : syracuseStep 3744049 = 2808037) B2808037
theorem B4992065 : Blo 2217435 4992065 := bstep (se 2 (by rfl) ⟨1872024, by rfl⟩ : syracuseStep 4992065 = 3744049) B3744049
theorem B3328043 : Blo 2217435 3328043 := bstep (se 1 (by rfl) ⟨2496032, by rfl⟩ : syracuseStep 3328043 = 4992065) B4992065
theorem B2218695 : Blo 2217435 2218695 := bstep (se 1 (by rfl) ⟨1664021, by rfl⟩ : syracuseStep 2218695 = 3328043) B3328043
theorem B2496037 : Blo 2217435 2496037 := bbase (se 4 (by rfl) ⟨234003, by rfl⟩ : syracuseStep 2496037 = 468007) (by norm_num)
theorem B3328049 : Blo 2217435 3328049 := bstep (se 2 (by rfl) ⟨1248018, by rfl⟩ : syracuseStep 3328049 = 2496037) B2496037
theorem B2218699 : Blo 2217435 2218699 := bstep (se 1 (by rfl) ⟨1664024, by rfl⟩ : syracuseStep 2218699 = 3328049) B3328049
theorem B2530097 : Blo 2217435 2530097 := bbase (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) (by norm_num)
theorem B26987701 : Blo 2217435 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B35983601 : Blo 2217435 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B23989067 : Blo 2217435 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B15992711 : Blo 2217435 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B10661807 : Blo 2217435 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B7107871 : Blo 2217435 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B9477161 : Blo 2217435 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B6318107 : Blo 2217435 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B4212071 : Blo 2217435 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B2808047 : Blo 2217435 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B7488125 : Blo 2217435 7488125 := bstep (se 3 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 7488125 = 2808047) B2808047
theorem B4992083 : Blo 2217435 4992083 := bstep (se 1 (by rfl) ⟨3744062, by rfl⟩ : syracuseStep 4992083 = 7488125) B7488125
theorem B3328055 : Blo 2217435 3328055 := bstep (se 1 (by rfl) ⟨2496041, by rfl⟩ : syracuseStep 3328055 = 4992083) B4992083
theorem B2218703 : Blo 2217435 2218703 := bstep (se 1 (by rfl) ⟨1664027, by rfl⟩ : syracuseStep 2218703 = 3328055) B3328055
theorem B3328061 : Blo 2217435 3328061 := bbase (se 3 (by rfl) ⟨624011, by rfl⟩ : syracuseStep 3328061 = 1248023) (by norm_num)
theorem B2218707 : Blo 2217435 2218707 := bstep (se 1 (by rfl) ⟨1664030, by rfl⟩ : syracuseStep 2218707 = 3328061) B3328061
theorem B4992101 : Blo 2217435 4992101 := bbase (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) (by norm_num)
theorem B3328067 : Blo 2217435 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B2218711 : Blo 2217435 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B5616125 : Blo 2217435 5616125 := bbase (se 3 (by rfl) ⟨1053023, by rfl⟩ : syracuseStep 5616125 = 2106047) (by norm_num)
theorem B3744083 : Blo 2217435 3744083 := bstep (se 1 (by rfl) ⟨2808062, by rfl⟩ : syracuseStep 3744083 = 5616125) B5616125
theorem B2496055 : Blo 2217435 2496055 := bstep (se 1 (by rfl) ⟨1872041, by rfl⟩ : syracuseStep 2496055 = 3744083) B3744083
theorem B3328073 : Blo 2217435 3328073 := bstep (se 2 (by rfl) ⟨1248027, by rfl⟩ : syracuseStep 3328073 = 2496055) B2496055
theorem B2218715 : Blo 2217435 2218715 := bstep (se 1 (by rfl) ⟨1664036, by rfl⟩ : syracuseStep 2218715 = 3328073) B3328073
theorem B4212101 : Blo 2217435 4212101 := bbase (se 4 (by rfl) ⟨394884, by rfl⟩ : syracuseStep 4212101 = 789769) (by norm_num)
theorem B11232269 : Blo 2217435 11232269 := bstep (se 3 (by rfl) ⟨2106050, by rfl⟩ : syracuseStep 11232269 = 4212101) B4212101
theorem B7488179 : Blo 2217435 7488179 := bstep (se 1 (by rfl) ⟨5616134, by rfl⟩ : syracuseStep 7488179 = 11232269) B11232269
theorem B4992119 : Blo 2217435 4992119 := bstep (se 1 (by rfl) ⟨3744089, by rfl⟩ : syracuseStep 4992119 = 7488179) B7488179
theorem B3328079 : Blo 2217435 3328079 := bstep (se 1 (by rfl) ⟨2496059, by rfl⟩ : syracuseStep 3328079 = 4992119) B4992119
theorem B2218719 : Blo 2217435 2218719 := bstep (se 1 (by rfl) ⟨1664039, by rfl⟩ : syracuseStep 2218719 = 3328079) B3328079
theorem B3328085 : Blo 2217435 3328085 := bbase (se 8 (by rfl) ⟨19500, by rfl⟩ : syracuseStep 3328085 = 39001) (by norm_num)
theorem B2218723 : Blo 2217435 2218723 := bstep (se 1 (by rfl) ⟨1664042, by rfl⟩ : syracuseStep 2218723 = 3328085) B3328085
theorem B5692781 : Blo 2217435 5692781 := bbase (se 3 (by rfl) ⟨1067396, by rfl⟩ : syracuseStep 5692781 = 2134793) (by norm_num)
theorem B3795187 : Blo 2217435 3795187 := bstep (se 1 (by rfl) ⟨2846390, by rfl⟩ : syracuseStep 3795187 = 5692781) B5692781
theorem B5060249 : Blo 2217435 5060249 := bstep (se 2 (by rfl) ⟨1897593, by rfl⟩ : syracuseStep 5060249 = 3795187) B3795187
theorem B3373499 : Blo 2217435 3373499 := bstep (se 1 (by rfl) ⟨2530124, by rfl⟩ : syracuseStep 3373499 = 5060249) B5060249
theorem B8995997 : Blo 2217435 8995997 := bstep (se 3 (by rfl) ⟨1686749, by rfl⟩ : syracuseStep 8995997 = 3373499) B3373499
theorem B5997331 : Blo 2217435 5997331 := bstep (se 1 (by rfl) ⟨4497998, by rfl⟩ : syracuseStep 5997331 = 8995997) B8995997
theorem B31985765 : Blo 2217435 31985765 := bstep (se 4 (by rfl) ⟨2998665, by rfl⟩ : syracuseStep 31985765 = 5997331) B5997331
theorem B21323843 : Blo 2217435 21323843 := bstep (se 1 (by rfl) ⟨15992882, by rfl⟩ : syracuseStep 21323843 = 31985765) B31985765
theorem B14215895 : Blo 2217435 14215895 := bstep (se 1 (by rfl) ⟨10661921, by rfl⟩ : syracuseStep 14215895 = 21323843) B21323843
theorem B9477263 : Blo 2217435 9477263 := bstep (se 1 (by rfl) ⟨7107947, by rfl⟩ : syracuseStep 9477263 = 14215895) B14215895
theorem B6318175 : Blo 2217435 6318175 := bstep (se 1 (by rfl) ⟨4738631, by rfl⟩ : syracuseStep 6318175 = 9477263) B9477263
theorem B8424233 : Blo 2217435 8424233 := bstep (se 2 (by rfl) ⟨3159087, by rfl⟩ : syracuseStep 8424233 = 6318175) B6318175
theorem B5616155 : Blo 2217435 5616155 := bstep (se 1 (by rfl) ⟨4212116, by rfl⟩ : syracuseStep 5616155 = 8424233) B8424233
theorem B3744103 : Blo 2217435 3744103 := bstep (se 1 (by rfl) ⟨2808077, by rfl⟩ : syracuseStep 3744103 = 5616155) B5616155
theorem B4992137 : Blo 2217435 4992137 := bstep (se 2 (by rfl) ⟨1872051, by rfl⟩ : syracuseStep 4992137 = 3744103) B3744103
theorem B3328091 : Blo 2217435 3328091 := bstep (se 1 (by rfl) ⟨2496068, by rfl⟩ : syracuseStep 3328091 = 4992137) B4992137
theorem B2218727 : Blo 2217435 2218727 := bstep (se 1 (by rfl) ⟨1664045, by rfl⟩ : syracuseStep 2218727 = 3328091) B3328091
theorem B2496073 : Blo 2217435 2496073 := bbase (se 2 (by rfl) ⟨936027, by rfl⟩ : syracuseStep 2496073 = 1872055) (by norm_num)
theorem B3328097 : Blo 2217435 3328097 := bstep (se 2 (by rfl) ⟨1248036, by rfl⟩ : syracuseStep 3328097 = 2496073) B2496073
theorem B2218731 : Blo 2217435 2218731 := bstep (se 1 (by rfl) ⟨1664048, by rfl⟩ : syracuseStep 2218731 = 3328097) B3328097
theorem B5770469 : Blo 2217435 5770469 := bbase (se 4 (by rfl) ⟨540981, by rfl⟩ : syracuseStep 5770469 = 1081963) (by norm_num)
theorem B3846979 : Blo 2217435 3846979 := bstep (se 1 (by rfl) ⟨2885234, by rfl⟩ : syracuseStep 3846979 = 5770469) B5770469
theorem B20517221 : Blo 2217435 20517221 := bstep (se 4 (by rfl) ⟨1923489, by rfl⟩ : syracuseStep 20517221 = 3846979) B3846979
theorem B54712589 : Blo 2217435 54712589 := bstep (se 3 (by rfl) ⟨10258610, by rfl⟩ : syracuseStep 54712589 = 20517221) B20517221
theorem B583600949 : Blo 2217435 583600949 := bstep (se 5 (by rfl) ⟨27356294, by rfl⟩ : syracuseStep 583600949 = 54712589) B54712589
theorem B389067299 : Blo 2217435 389067299 := bstep (se 1 (by rfl) ⟨291800474, by rfl⟩ : syracuseStep 389067299 = 583600949) B583600949
theorem B259378199 : Blo 2217435 259378199 := bstep (se 1 (by rfl) ⟨194533649, by rfl⟩ : syracuseStep 259378199 = 389067299) B389067299
theorem B172918799 : Blo 2217435 172918799 := bstep (se 1 (by rfl) ⟨129689099, by rfl⟩ : syracuseStep 172918799 = 259378199) B259378199
theorem B115279199 : Blo 2217435 115279199 := bstep (se 1 (by rfl) ⟨86459399, by rfl⟩ : syracuseStep 115279199 = 172918799) B172918799
theorem B76852799 : Blo 2217435 76852799 := bstep (se 1 (by rfl) ⟨57639599, by rfl⟩ : syracuseStep 76852799 = 115279199) B115279199
theorem B51235199 : Blo 2217435 51235199 := bstep (se 1 (by rfl) ⟨38426399, by rfl⟩ : syracuseStep 51235199 = 76852799) B76852799
theorem B34156799 : Blo 2217435 34156799 := bstep (se 1 (by rfl) ⟨25617599, by rfl⟩ : syracuseStep 34156799 = 51235199) B51235199
theorem B22771199 : Blo 2217435 22771199 := bstep (se 1 (by rfl) ⟨17078399, by rfl⟩ : syracuseStep 22771199 = 34156799) B34156799
theorem B15180799 : Blo 2217435 15180799 := bstep (se 1 (by rfl) ⟨11385599, by rfl⟩ : syracuseStep 15180799 = 22771199) B22771199
theorem B20241065 : Blo 2217435 20241065 := bstep (se 2 (by rfl) ⟨7590399, by rfl⟩ : syracuseStep 20241065 = 15180799) B15180799
theorem B13494043 : Blo 2217435 13494043 := bstep (se 1 (by rfl) ⟨10120532, by rfl⟩ : syracuseStep 13494043 = 20241065) B20241065
theorem B17992057 : Blo 2217435 17992057 := bstep (se 2 (by rfl) ⟨6747021, by rfl⟩ : syracuseStep 17992057 = 13494043) B13494043
theorem B23989409 : Blo 2217435 23989409 := bstep (se 2 (by rfl) ⟨8996028, by rfl⟩ : syracuseStep 23989409 = 17992057) B17992057
theorem B15992939 : Blo 2217435 15992939 := bstep (se 1 (by rfl) ⟨11994704, by rfl⟩ : syracuseStep 15992939 = 23989409) B23989409
theorem B10661959 : Blo 2217435 10661959 := bstep (se 1 (by rfl) ⟨7996469, by rfl⟩ : syracuseStep 10661959 = 15992939) B15992939
theorem B14215945 : Blo 2217435 14215945 := bstep (se 2 (by rfl) ⟨5330979, by rfl⟩ : syracuseStep 14215945 = 10661959) B10661959
theorem B18954593 : Blo 2217435 18954593 := bstep (se 2 (by rfl) ⟨7107972, by rfl⟩ : syracuseStep 18954593 = 14215945) B14215945
theorem B12636395 : Blo 2217435 12636395 := bstep (se 1 (by rfl) ⟨9477296, by rfl⟩ : syracuseStep 12636395 = 18954593) B18954593
theorem B8424263 : Blo 2217435 8424263 := bstep (se 1 (by rfl) ⟨6318197, by rfl⟩ : syracuseStep 8424263 = 12636395) B12636395
theorem B5616175 : Blo 2217435 5616175 := bstep (se 1 (by rfl) ⟨4212131, by rfl⟩ : syracuseStep 5616175 = 8424263) B8424263
theorem B7488233 : Blo 2217435 7488233 := bstep (se 2 (by rfl) ⟨2808087, by rfl⟩ : syracuseStep 7488233 = 5616175) B5616175
theorem B4992155 : Blo 2217435 4992155 := bstep (se 1 (by rfl) ⟨3744116, by rfl⟩ : syracuseStep 4992155 = 7488233) B7488233
theorem B3328103 : Blo 2217435 3328103 := bstep (se 1 (by rfl) ⟨2496077, by rfl⟩ : syracuseStep 3328103 = 4992155) B4992155
theorem B2218735 : Blo 2217435 2218735 := bstep (se 1 (by rfl) ⟨1664051, by rfl⟩ : syracuseStep 2218735 = 3328103) B3328103
theorem B3328109 : Blo 2217435 3328109 := bbase (se 3 (by rfl) ⟨624020, by rfl⟩ : syracuseStep 3328109 = 1248041) (by norm_num)
theorem B2218739 : Blo 2217435 2218739 := bstep (se 1 (by rfl) ⟨1664054, by rfl⟩ : syracuseStep 2218739 = 3328109) B3328109
theorem B4992173 : Blo 2217435 4992173 := bbase (se 3 (by rfl) ⟨936032, by rfl⟩ : syracuseStep 4992173 = 1872065) (by norm_num)
theorem B3328115 : Blo 2217435 3328115 := bstep (se 1 (by rfl) ⟨2496086, by rfl⟩ : syracuseStep 3328115 = 4992173) B4992173
theorem B2218743 : Blo 2217435 2218743 := bstep (se 1 (by rfl) ⟨1664057, by rfl⟩ : syracuseStep 2218743 = 3328115) B3328115
theorem B2665505 : Blo 2217435 2665505 := bbase (se 2 (by rfl) ⟨999564, by rfl⟩ : syracuseStep 2665505 = 1999129) (by norm_num)
theorem B7108013 : Blo 2217435 7108013 := bstep (se 3 (by rfl) ⟨1332752, by rfl⟩ : syracuseStep 7108013 = 2665505) B2665505
theorem B4738675 : Blo 2217435 4738675 := bstep (se 1 (by rfl) ⟨3554006, by rfl⟩ : syracuseStep 4738675 = 7108013) B7108013
theorem B6318233 : Blo 2217435 6318233 := bstep (se 2 (by rfl) ⟨2369337, by rfl⟩ : syracuseStep 6318233 = 4738675) B4738675
theorem B4212155 : Blo 2217435 4212155 := bstep (se 1 (by rfl) ⟨3159116, by rfl⟩ : syracuseStep 4212155 = 6318233) B6318233
theorem B2808103 : Blo 2217435 2808103 := bstep (se 1 (by rfl) ⟨2106077, by rfl⟩ : syracuseStep 2808103 = 4212155) B4212155
theorem B3744137 : Blo 2217435 3744137 := bstep (se 2 (by rfl) ⟨1404051, by rfl⟩ : syracuseStep 3744137 = 2808103) B2808103
theorem B2496091 : Blo 2217435 2496091 := bstep (se 1 (by rfl) ⟨1872068, by rfl⟩ : syracuseStep 2496091 = 3744137) B3744137
theorem B3328121 : Blo 2217435 3328121 := bstep (se 2 (by rfl) ⟨1248045, by rfl⟩ : syracuseStep 3328121 = 2496091) B2496091
theorem B2218747 : Blo 2217435 2218747 := bstep (se 1 (by rfl) ⟨1664060, by rfl⟩ : syracuseStep 2218747 = 3328121) B3328121
theorem B2885257 : Blo 2217435 2885257 := bbase (se 2 (by rfl) ⟨1081971, by rfl⟩ : syracuseStep 2885257 = 2163943) (by norm_num)
theorem B3847009 : Blo 2217435 3847009 := bstep (se 2 (by rfl) ⟨1442628, by rfl⟩ : syracuseStep 3847009 = 2885257) B2885257
theorem B5129345 : Blo 2217435 5129345 := bstep (se 2 (by rfl) ⟨1923504, by rfl⟩ : syracuseStep 5129345 = 3847009) B3847009
theorem B3419563 : Blo 2217435 3419563 := bstep (se 1 (by rfl) ⟨2564672, by rfl⟩ : syracuseStep 3419563 = 5129345) B5129345
theorem B4559417 : Blo 2217435 4559417 := bstep (se 2 (by rfl) ⟨1709781, by rfl⟩ : syracuseStep 4559417 = 3419563) B3419563
theorem B3039611 : Blo 2217435 3039611 := bstep (se 1 (by rfl) ⟨2279708, by rfl⟩ : syracuseStep 3039611 = 4559417) B4559417
theorem B32422517 : Blo 2217435 32422517 := bstep (se 5 (by rfl) ⟨1519805, by rfl⟩ : syracuseStep 32422517 = 3039611) B3039611
theorem B21615011 : Blo 2217435 21615011 := bstep (se 1 (by rfl) ⟨16211258, by rfl⟩ : syracuseStep 21615011 = 32422517) B32422517
theorem B14410007 : Blo 2217435 14410007 := bstep (se 1 (by rfl) ⟨10807505, by rfl⟩ : syracuseStep 14410007 = 21615011) B21615011
theorem B9606671 : Blo 2217435 9606671 := bstep (se 1 (by rfl) ⟨7205003, by rfl⟩ : syracuseStep 9606671 = 14410007) B14410007
theorem B6404447 : Blo 2217435 6404447 := bstep (se 1 (by rfl) ⟨4803335, by rfl⟩ : syracuseStep 6404447 = 9606671) B9606671
theorem B17078525 : Blo 2217435 17078525 := bstep (se 3 (by rfl) ⟨3202223, by rfl⟩ : syracuseStep 17078525 = 6404447) B6404447
theorem B11385683 : Blo 2217435 11385683 := bstep (se 1 (by rfl) ⟨8539262, by rfl⟩ : syracuseStep 11385683 = 17078525) B17078525
theorem B7590455 : Blo 2217435 7590455 := bstep (se 1 (by rfl) ⟨5692841, by rfl⟩ : syracuseStep 7590455 = 11385683) B11385683
theorem B5060303 : Blo 2217435 5060303 := bstep (se 1 (by rfl) ⟨3795227, by rfl⟩ : syracuseStep 5060303 = 7590455) B7590455
theorem B3373535 : Blo 2217435 3373535 := bstep (se 1 (by rfl) ⟨2530151, by rfl⟩ : syracuseStep 3373535 = 5060303) B5060303
theorem B8996093 : Blo 2217435 8996093 := bstep (se 3 (by rfl) ⟨1686767, by rfl⟩ : syracuseStep 8996093 = 3373535) B3373535
theorem B5997395 : Blo 2217435 5997395 := bstep (se 1 (by rfl) ⟨4498046, by rfl⟩ : syracuseStep 5997395 = 8996093) B8996093
theorem B15993053 : Blo 2217435 15993053 := bstep (se 3 (by rfl) ⟨2998697, by rfl⟩ : syracuseStep 15993053 = 5997395) B5997395
theorem B10662035 : Blo 2217435 10662035 := bstep (se 1 (by rfl) ⟨7996526, by rfl⟩ : syracuseStep 10662035 = 15993053) B15993053
theorem B28432093 : Blo 2217435 28432093 := bstep (se 3 (by rfl) ⟨5331017, by rfl⟩ : syracuseStep 28432093 = 10662035) B10662035
theorem B37909457 : Blo 2217435 37909457 := bstep (se 2 (by rfl) ⟨14216046, by rfl⟩ : syracuseStep 37909457 = 28432093) B28432093
theorem B25272971 : Blo 2217435 25272971 := bstep (se 1 (by rfl) ⟨18954728, by rfl⟩ : syracuseStep 25272971 = 37909457) B37909457
theorem B16848647 : Blo 2217435 16848647 := bstep (se 1 (by rfl) ⟨12636485, by rfl⟩ : syracuseStep 16848647 = 25272971) B25272971
theorem B11232431 : Blo 2217435 11232431 := bstep (se 1 (by rfl) ⟨8424323, by rfl⟩ : syracuseStep 11232431 = 16848647) B16848647
theorem B7488287 : Blo 2217435 7488287 := bstep (se 1 (by rfl) ⟨5616215, by rfl⟩ : syracuseStep 7488287 = 11232431) B11232431
theorem B4992191 : Blo 2217435 4992191 := bstep (se 1 (by rfl) ⟨3744143, by rfl⟩ : syracuseStep 4992191 = 7488287) B7488287
theorem B3328127 : Blo 2217435 3328127 := bstep (se 1 (by rfl) ⟨2496095, by rfl⟩ : syracuseStep 3328127 = 4992191) B4992191
theorem B2218751 : Blo 2217435 2218751 := bstep (se 1 (by rfl) ⟨1664063, by rfl⟩ : syracuseStep 2218751 = 3328127) B3328127
theorem B3328133 : Blo 2217435 3328133 := bbase (se 4 (by rfl) ⟨312012, by rfl⟩ : syracuseStep 3328133 = 624025) (by norm_num)
theorem B2218755 : Blo 2217435 2218755 := bstep (se 1 (by rfl) ⟨1664066, by rfl⟩ : syracuseStep 2218755 = 3328133) B3328133
theorem B3744157 : Blo 2217435 3744157 := bbase (se 3 (by rfl) ⟨702029, by rfl⟩ : syracuseStep 3744157 = 1404059) (by norm_num)
theorem B4992209 : Blo 2217435 4992209 := bstep (se 2 (by rfl) ⟨1872078, by rfl⟩ : syracuseStep 4992209 = 3744157) B3744157
theorem B3328139 : Blo 2217435 3328139 := bstep (se 1 (by rfl) ⟨2496104, by rfl⟩ : syracuseStep 3328139 = 4992209) B4992209
theorem B2218759 : Blo 2217435 2218759 := bstep (se 1 (by rfl) ⟨1664069, by rfl⟩ : syracuseStep 2218759 = 3328139) B3328139
theorem B2496109 : Blo 2217435 2496109 := bbase (se 3 (by rfl) ⟨468020, by rfl⟩ : syracuseStep 2496109 = 936041) (by norm_num)
theorem B3328145 : Blo 2217435 3328145 := bstep (se 2 (by rfl) ⟨1248054, by rfl⟩ : syracuseStep 3328145 = 2496109) B2496109
theorem B2218763 : Blo 2217435 2218763 := bstep (se 1 (by rfl) ⟨1664072, by rfl⟩ : syracuseStep 2218763 = 3328145) B3328145
theorem B7488341 : Blo 2217435 7488341 := bbase (se 9 (by rfl) ⟨21938, by rfl⟩ : syracuseStep 7488341 = 43877) (by norm_num)
theorem B4992227 : Blo 2217435 4992227 := bstep (se 1 (by rfl) ⟨3744170, by rfl⟩ : syracuseStep 4992227 = 7488341) B7488341
theorem B3328151 : Blo 2217435 3328151 := bstep (se 1 (by rfl) ⟨2496113, by rfl⟩ : syracuseStep 3328151 = 4992227) B4992227
theorem B2218767 : Blo 2217435 2218767 := bstep (se 1 (by rfl) ⟨1664075, by rfl⟩ : syracuseStep 2218767 = 3328151) B3328151
theorem B3328157 : Blo 2217435 3328157 := bbase (se 3 (by rfl) ⟨624029, by rfl⟩ : syracuseStep 3328157 = 1248059) (by norm_num)
theorem B2218771 : Blo 2217435 2218771 := bstep (se 1 (by rfl) ⟨1664078, by rfl⟩ : syracuseStep 2218771 = 3328157) B3328157
theorem B4992245 : Blo 2217435 4992245 := bbase (se 5 (by rfl) ⟨234011, by rfl⟩ : syracuseStep 4992245 = 468023) (by norm_num)
theorem B3328163 : Blo 2217435 3328163 := bstep (se 1 (by rfl) ⟨2496122, by rfl⟩ : syracuseStep 3328163 = 4992245) B4992245
theorem B2218775 : Blo 2217435 2218775 := bstep (se 1 (by rfl) ⟨1664081, by rfl⟩ : syracuseStep 2218775 = 3328163) B3328163
theorem B2279737 : Blo 2217435 2279737 := bbase (se 2 (by rfl) ⟨854901, by rfl⟩ : syracuseStep 2279737 = 1709803) (by norm_num)
theorem B3039649 : Blo 2217435 3039649 := bstep (se 2 (by rfl) ⟨1139868, by rfl⟩ : syracuseStep 3039649 = 2279737) B2279737
theorem B16211461 : Blo 2217435 16211461 := bstep (se 4 (by rfl) ⟨1519824, by rfl⟩ : syracuseStep 16211461 = 3039649) B3039649
theorem B21615281 : Blo 2217435 21615281 := bstep (se 2 (by rfl) ⟨8105730, by rfl⟩ : syracuseStep 21615281 = 16211461) B16211461
theorem B14410187 : Blo 2217435 14410187 := bstep (se 1 (by rfl) ⟨10807640, by rfl⟩ : syracuseStep 14410187 = 21615281) B21615281
theorem B9606791 : Blo 2217435 9606791 := bstep (se 1 (by rfl) ⟨7205093, by rfl⟩ : syracuseStep 9606791 = 14410187) B14410187
theorem B6404527 : Blo 2217435 6404527 := bstep (se 1 (by rfl) ⟨4803395, by rfl⟩ : syracuseStep 6404527 = 9606791) B9606791
theorem B34157477 : Blo 2217435 34157477 := bstep (se 4 (by rfl) ⟨3202263, by rfl⟩ : syracuseStep 34157477 = 6404527) B6404527
theorem B91086605 : Blo 2217435 91086605 := bstep (se 3 (by rfl) ⟨17078738, by rfl⟩ : syracuseStep 91086605 = 34157477) B34157477
theorem B60724403 : Blo 2217435 60724403 := bstep (se 1 (by rfl) ⟨45543302, by rfl⟩ : syracuseStep 60724403 = 91086605) B91086605
theorem B40482935 : Blo 2217435 40482935 := bstep (se 1 (by rfl) ⟨30362201, by rfl⟩ : syracuseStep 40482935 = 60724403) B60724403
theorem B26988623 : Blo 2217435 26988623 := bstep (se 1 (by rfl) ⟨20241467, by rfl⟩ : syracuseStep 26988623 = 40482935) B40482935
theorem B17992415 : Blo 2217435 17992415 := bstep (se 1 (by rfl) ⟨13494311, by rfl⟩ : syracuseStep 17992415 = 26988623) B26988623
theorem B47979773 : Blo 2217435 47979773 := bstep (se 3 (by rfl) ⟨8996207, by rfl⟩ : syracuseStep 47979773 = 17992415) B17992415
theorem B31986515 : Blo 2217435 31986515 := bstep (se 1 (by rfl) ⟨23989886, by rfl⟩ : syracuseStep 31986515 = 47979773) B47979773
theorem B21324343 : Blo 2217435 21324343 := bstep (se 1 (by rfl) ⟨15993257, by rfl⟩ : syracuseStep 21324343 = 31986515) B31986515
theorem B28432457 : Blo 2217435 28432457 := bstep (se 2 (by rfl) ⟨10662171, by rfl⟩ : syracuseStep 28432457 = 21324343) B21324343
theorem B18954971 : Blo 2217435 18954971 := bstep (se 1 (by rfl) ⟨14216228, by rfl⟩ : syracuseStep 18954971 = 28432457) B28432457
theorem B12636647 : Blo 2217435 12636647 := bstep (se 1 (by rfl) ⟨9477485, by rfl⟩ : syracuseStep 12636647 = 18954971) B18954971
theorem B8424431 : Blo 2217435 8424431 := bstep (se 1 (by rfl) ⟨6318323, by rfl⟩ : syracuseStep 8424431 = 12636647) B12636647
theorem B5616287 : Blo 2217435 5616287 := bstep (se 1 (by rfl) ⟨4212215, by rfl⟩ : syracuseStep 5616287 = 8424431) B8424431
theorem B3744191 : Blo 2217435 3744191 := bstep (se 1 (by rfl) ⟨2808143, by rfl⟩ : syracuseStep 3744191 = 5616287) B5616287
theorem B2496127 : Blo 2217435 2496127 := bstep (se 1 (by rfl) ⟨1872095, by rfl⟩ : syracuseStep 2496127 = 3744191) B3744191
theorem B3328169 : Blo 2217435 3328169 := bstep (se 2 (by rfl) ⟨1248063, by rfl⟩ : syracuseStep 3328169 = 2496127) B2496127
theorem B2218779 : Blo 2217435 2218779 := bstep (se 1 (by rfl) ⟨1664084, by rfl⟩ : syracuseStep 2218779 = 3328169) B3328169
theorem B5770597 : Blo 2217435 5770597 := bbase (se 4 (by rfl) ⟨540993, by rfl⟩ : syracuseStep 5770597 = 1081987) (by norm_num)
theorem B7694129 : Blo 2217435 7694129 := bstep (se 2 (by rfl) ⟨2885298, by rfl⟩ : syracuseStep 7694129 = 5770597) B5770597
theorem B5129419 : Blo 2217435 5129419 := bstep (se 1 (by rfl) ⟨3847064, by rfl⟩ : syracuseStep 5129419 = 7694129) B7694129
theorem B6839225 : Blo 2217435 6839225 := bstep (se 2 (by rfl) ⟨2564709, by rfl⟩ : syracuseStep 6839225 = 5129419) B5129419
theorem B4559483 : Blo 2217435 4559483 := bstep (se 1 (by rfl) ⟨3419612, by rfl⟩ : syracuseStep 4559483 = 6839225) B6839225
theorem B3039655 : Blo 2217435 3039655 := bstep (se 1 (by rfl) ⟨2279741, by rfl⟩ : syracuseStep 3039655 = 4559483) B4559483
theorem B4052873 : Blo 2217435 4052873 := bstep (se 2 (by rfl) ⟨1519827, by rfl⟩ : syracuseStep 4052873 = 3039655) B3039655
theorem B10807661 : Blo 2217435 10807661 := bstep (se 3 (by rfl) ⟨2026436, by rfl⟩ : syracuseStep 10807661 = 4052873) B4052873
theorem B7205107 : Blo 2217435 7205107 := bstep (se 1 (by rfl) ⟨5403830, by rfl⟩ : syracuseStep 7205107 = 10807661) B10807661
theorem B9606809 : Blo 2217435 9606809 := bstep (se 2 (by rfl) ⟨3602553, by rfl⟩ : syracuseStep 9606809 = 7205107) B7205107
theorem B25618157 : Blo 2217435 25618157 := bstep (se 3 (by rfl) ⟨4803404, by rfl⟩ : syracuseStep 25618157 = 9606809) B9606809
theorem B17078771 : Blo 2217435 17078771 := bstep (se 1 (by rfl) ⟨12809078, by rfl⟩ : syracuseStep 17078771 = 25618157) B25618157
theorem B11385847 : Blo 2217435 11385847 := bstep (se 1 (by rfl) ⟨8539385, by rfl⟩ : syracuseStep 11385847 = 17078771) B17078771
theorem B15181129 : Blo 2217435 15181129 := bstep (se 2 (by rfl) ⟨5692923, by rfl⟩ : syracuseStep 15181129 = 11385847) B11385847
theorem B20241505 : Blo 2217435 20241505 := bstep (se 2 (by rfl) ⟨7590564, by rfl⟩ : syracuseStep 20241505 = 15181129) B15181129
theorem B26988673 : Blo 2217435 26988673 := bstep (se 2 (by rfl) ⟨10120752, by rfl⟩ : syracuseStep 26988673 = 20241505) B20241505
theorem B35984897 : Blo 2217435 35984897 := bstep (se 2 (by rfl) ⟨13494336, by rfl⟩ : syracuseStep 35984897 = 26988673) B26988673
theorem B23989931 : Blo 2217435 23989931 := bstep (se 1 (by rfl) ⟨17992448, by rfl⟩ : syracuseStep 23989931 = 35984897) B35984897
theorem B15993287 : Blo 2217435 15993287 := bstep (se 1 (by rfl) ⟨11994965, by rfl⟩ : syracuseStep 15993287 = 23989931) B23989931
theorem B10662191 : Blo 2217435 10662191 := bstep (se 1 (by rfl) ⟨7996643, by rfl⟩ : syracuseStep 10662191 = 15993287) B15993287
theorem B7108127 : Blo 2217435 7108127 := bstep (se 1 (by rfl) ⟨5331095, by rfl⟩ : syracuseStep 7108127 = 10662191) B10662191
theorem B4738751 : Blo 2217435 4738751 := bstep (se 1 (by rfl) ⟨3554063, by rfl⟩ : syracuseStep 4738751 = 7108127) B7108127
theorem B3159167 : Blo 2217435 3159167 := bstep (se 1 (by rfl) ⟨2369375, by rfl⟩ : syracuseStep 3159167 = 4738751) B4738751
theorem B8424445 : Blo 2217435 8424445 := bstep (se 3 (by rfl) ⟨1579583, by rfl⟩ : syracuseStep 8424445 = 3159167) B3159167
theorem B11232593 : Blo 2217435 11232593 := bstep (se 2 (by rfl) ⟨4212222, by rfl⟩ : syracuseStep 11232593 = 8424445) B8424445
theorem B7488395 : Blo 2217435 7488395 := bstep (se 1 (by rfl) ⟨5616296, by rfl⟩ : syracuseStep 7488395 = 11232593) B11232593
theorem B4992263 : Blo 2217435 4992263 := bstep (se 1 (by rfl) ⟨3744197, by rfl⟩ : syracuseStep 4992263 = 7488395) B7488395
theorem B3328175 : Blo 2217435 3328175 := bstep (se 1 (by rfl) ⟨2496131, by rfl⟩ : syracuseStep 3328175 = 4992263) B4992263
theorem B2218783 : Blo 2217435 2218783 := bstep (se 1 (by rfl) ⟨1664087, by rfl⟩ : syracuseStep 2218783 = 3328175) B3328175
theorem B3328181 : Blo 2217435 3328181 := bbase (se 5 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 3328181 = 312017) (by norm_num)
theorem B2218787 : Blo 2217435 2218787 := bstep (se 1 (by rfl) ⟨1664090, by rfl⟩ : syracuseStep 2218787 = 3328181) B3328181
theorem B5616317 : Blo 2217435 5616317 := bbase (se 3 (by rfl) ⟨1053059, by rfl⟩ : syracuseStep 5616317 = 2106119) (by norm_num)
theorem B3744211 : Blo 2217435 3744211 := bstep (se 1 (by rfl) ⟨2808158, by rfl⟩ : syracuseStep 3744211 = 5616317) B5616317
theorem B4992281 : Blo 2217435 4992281 := bstep (se 2 (by rfl) ⟨1872105, by rfl⟩ : syracuseStep 4992281 = 3744211) B3744211
theorem B3328187 : Blo 2217435 3328187 := bstep (se 1 (by rfl) ⟨2496140, by rfl⟩ : syracuseStep 3328187 = 4992281) B4992281
theorem B2218791 : Blo 2217435 2218791 := bstep (se 1 (by rfl) ⟨1664093, by rfl⟩ : syracuseStep 2218791 = 3328187) B3328187
theorem B2496145 : Blo 2217435 2496145 := bbase (se 2 (by rfl) ⟨936054, by rfl⟩ : syracuseStep 2496145 = 1872109) (by norm_num)
theorem B3328193 : Blo 2217435 3328193 := bstep (se 2 (by rfl) ⟨1248072, by rfl⟩ : syracuseStep 3328193 = 2496145) B2496145
theorem B2218795 : Blo 2217435 2218795 := bstep (se 1 (by rfl) ⟨1664096, by rfl⟩ : syracuseStep 2218795 = 3328193) B3328193
theorem B4212253 : Blo 2217435 4212253 := bbase (se 3 (by rfl) ⟨789797, by rfl⟩ : syracuseStep 4212253 = 1579595) (by norm_num)
theorem B5616337 : Blo 2217435 5616337 := bstep (se 2 (by rfl) ⟨2106126, by rfl⟩ : syracuseStep 5616337 = 4212253) B4212253
theorem B7488449 : Blo 2217435 7488449 := bstep (se 2 (by rfl) ⟨2808168, by rfl⟩ : syracuseStep 7488449 = 5616337) B5616337
theorem B4992299 : Blo 2217435 4992299 := bstep (se 1 (by rfl) ⟨3744224, by rfl⟩ : syracuseStep 4992299 = 7488449) B7488449
theorem B3328199 : Blo 2217435 3328199 := bstep (se 1 (by rfl) ⟨2496149, by rfl⟩ : syracuseStep 3328199 = 4992299) B4992299
theorem B2218799 : Blo 2217435 2218799 := bstep (se 1 (by rfl) ⟨1664099, by rfl⟩ : syracuseStep 2218799 = 3328199) B3328199
theorem B3328205 : Blo 2217435 3328205 := bbase (se 3 (by rfl) ⟨624038, by rfl⟩ : syracuseStep 3328205 = 1248077) (by norm_num)
theorem B2218803 : Blo 2217435 2218803 := bstep (se 1 (by rfl) ⟨1664102, by rfl⟩ : syracuseStep 2218803 = 3328205) B3328205
theorem B4992317 : Blo 2217435 4992317 := bbase (se 3 (by rfl) ⟨936059, by rfl⟩ : syracuseStep 4992317 = 1872119) (by norm_num)
theorem B3328211 : Blo 2217435 3328211 := bstep (se 1 (by rfl) ⟨2496158, by rfl⟩ : syracuseStep 3328211 = 4992317) B4992317
theorem B2218807 : Blo 2217435 2218807 := bstep (se 1 (by rfl) ⟨1664105, by rfl⟩ : syracuseStep 2218807 = 3328211) B3328211
theorem B3744245 : Blo 2217435 3744245 := bbase (se 5 (by rfl) ⟨175511, by rfl⟩ : syracuseStep 3744245 = 351023) (by norm_num)
theorem B2496163 : Blo 2217435 2496163 := bstep (se 1 (by rfl) ⟨1872122, by rfl⟩ : syracuseStep 2496163 = 3744245) B3744245
theorem B3328217 : Blo 2217435 3328217 := bstep (se 2 (by rfl) ⟨1248081, by rfl⟩ : syracuseStep 3328217 = 2496163) B2496163
theorem B2218811 : Blo 2217435 2218811 := bstep (se 1 (by rfl) ⟨1664108, by rfl⟩ : syracuseStep 2218811 = 3328217) B3328217
theorem B7108229 : Blo 2217435 7108229 := bbase (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) (by norm_num)
theorem B4738819 : Blo 2217435 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B6318425 : Blo 2217435 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B16849133 : Blo 2217435 16849133 := bstep (se 3 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 16849133 = 6318425) B6318425
theorem B11232755 : Blo 2217435 11232755 := bstep (se 1 (by rfl) ⟨8424566, by rfl⟩ : syracuseStep 11232755 = 16849133) B16849133
theorem B7488503 : Blo 2217435 7488503 := bstep (se 1 (by rfl) ⟨5616377, by rfl⟩ : syracuseStep 7488503 = 11232755) B11232755
theorem B4992335 : Blo 2217435 4992335 := bstep (se 1 (by rfl) ⟨3744251, by rfl⟩ : syracuseStep 4992335 = 7488503) B7488503
theorem B3328223 : Blo 2217435 3328223 := bstep (se 1 (by rfl) ⟨2496167, by rfl⟩ : syracuseStep 3328223 = 4992335) B4992335
theorem B2218815 : Blo 2217435 2218815 := bstep (se 1 (by rfl) ⟨1664111, by rfl⟩ : syracuseStep 2218815 = 3328223) B3328223
theorem B3328229 : Blo 2217435 3328229 := bbase (se 4 (by rfl) ⟨312021, by rfl⟩ : syracuseStep 3328229 = 624043) (by norm_num)
theorem B2218819 : Blo 2217435 2218819 := bstep (se 1 (by rfl) ⟨1664114, by rfl⟩ : syracuseStep 2218819 = 3328229) B3328229
theorem B4738837 : Blo 2217435 4738837 := bbase (se 6 (by rfl) ⟨111066, by rfl⟩ : syracuseStep 4738837 = 222133) (by norm_num)
theorem B6318449 : Blo 2217435 6318449 := bstep (se 2 (by rfl) ⟨2369418, by rfl⟩ : syracuseStep 6318449 = 4738837) B4738837
theorem B4212299 : Blo 2217435 4212299 := bstep (se 1 (by rfl) ⟨3159224, by rfl⟩ : syracuseStep 4212299 = 6318449) B6318449
theorem B2808199 : Blo 2217435 2808199 := bstep (se 1 (by rfl) ⟨2106149, by rfl⟩ : syracuseStep 2808199 = 4212299) B4212299
theorem B3744265 : Blo 2217435 3744265 := bstep (se 2 (by rfl) ⟨1404099, by rfl⟩ : syracuseStep 3744265 = 2808199) B2808199
theorem B4992353 : Blo 2217435 4992353 := bstep (se 2 (by rfl) ⟨1872132, by rfl⟩ : syracuseStep 4992353 = 3744265) B3744265
theorem B3328235 : Blo 2217435 3328235 := bstep (se 1 (by rfl) ⟨2496176, by rfl⟩ : syracuseStep 3328235 = 4992353) B4992353
theorem B2218823 : Blo 2217435 2218823 := bstep (se 1 (by rfl) ⟨1664117, by rfl⟩ : syracuseStep 2218823 = 3328235) B3328235
theorem B2496181 : Blo 2217435 2496181 := bbase (se 5 (by rfl) ⟨117008, by rfl⟩ : syracuseStep 2496181 = 234017) (by norm_num)
theorem B3328241 : Blo 2217435 3328241 := bstep (se 2 (by rfl) ⟨1248090, by rfl⟩ : syracuseStep 3328241 = 2496181) B2496181
theorem B2218827 : Blo 2217435 2218827 := bstep (se 1 (by rfl) ⟨1664120, by rfl⟩ : syracuseStep 2218827 = 3328241) B3328241
theorem B2808209 : Blo 2217435 2808209 := bbase (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) (by norm_num)
theorem B7488557 : Blo 2217435 7488557 := bstep (se 3 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 7488557 = 2808209) B2808209
theorem B4992371 : Blo 2217435 4992371 := bstep (se 1 (by rfl) ⟨3744278, by rfl⟩ : syracuseStep 4992371 = 7488557) B7488557
theorem B3328247 : Blo 2217435 3328247 := bstep (se 1 (by rfl) ⟨2496185, by rfl⟩ : syracuseStep 3328247 = 4992371) B4992371
theorem B2218831 : Blo 2217435 2218831 := bstep (se 1 (by rfl) ⟨1664123, by rfl⟩ : syracuseStep 2218831 = 3328247) B3328247
theorem B3328253 : Blo 2217435 3328253 := bbase (se 3 (by rfl) ⟨624047, by rfl⟩ : syracuseStep 3328253 = 1248095) (by norm_num)
theorem B2218835 : Blo 2217435 2218835 := bstep (se 1 (by rfl) ⟨1664126, by rfl⟩ : syracuseStep 2218835 = 3328253) B3328253
theorem B4992389 : Blo 2217435 4992389 := bbase (se 4 (by rfl) ⟨468036, by rfl⟩ : syracuseStep 4992389 = 936073) (by norm_num)
theorem B3328259 : Blo 2217435 3328259 := bstep (se 1 (by rfl) ⟨2496194, by rfl⟩ : syracuseStep 3328259 = 4992389) B4992389
theorem B2218839 : Blo 2217435 2218839 := bstep (se 1 (by rfl) ⟨1664129, by rfl⟩ : syracuseStep 2218839 = 3328259) B3328259
theorem B3159253 : Blo 2217435 3159253 := bbase (se 7 (by rfl) ⟨37022, by rfl⟩ : syracuseStep 3159253 = 74045) (by norm_num)
theorem B4212337 : Blo 2217435 4212337 := bstep (se 2 (by rfl) ⟨1579626, by rfl⟩ : syracuseStep 4212337 = 3159253) B3159253
theorem B5616449 : Blo 2217435 5616449 := bstep (se 2 (by rfl) ⟨2106168, by rfl⟩ : syracuseStep 5616449 = 4212337) B4212337
theorem B3744299 : Blo 2217435 3744299 := bstep (se 1 (by rfl) ⟨2808224, by rfl⟩ : syracuseStep 3744299 = 5616449) B5616449
theorem B2496199 : Blo 2217435 2496199 := bstep (se 1 (by rfl) ⟨1872149, by rfl⟩ : syracuseStep 2496199 = 3744299) B3744299
theorem B3328265 : Blo 2217435 3328265 := bstep (se 2 (by rfl) ⟨1248099, by rfl⟩ : syracuseStep 3328265 = 2496199) B2496199
theorem B2218843 : Blo 2217435 2218843 := bstep (se 1 (by rfl) ⟨1664132, by rfl⟩ : syracuseStep 2218843 = 3328265) B3328265
theorem B11232917 : Blo 2217435 11232917 := bbase (se 6 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 11232917 = 526543) (by norm_num)
theorem B7488611 : Blo 2217435 7488611 := bstep (se 1 (by rfl) ⟨5616458, by rfl⟩ : syracuseStep 7488611 = 11232917) B11232917
theorem B4992407 : Blo 2217435 4992407 := bstep (se 1 (by rfl) ⟨3744305, by rfl⟩ : syracuseStep 4992407 = 7488611) B7488611
theorem B3328271 : Blo 2217435 3328271 := bstep (se 1 (by rfl) ⟨2496203, by rfl⟩ : syracuseStep 3328271 = 4992407) B4992407
theorem B2218847 : Blo 2217435 2218847 := bstep (se 1 (by rfl) ⟨1664135, by rfl⟩ : syracuseStep 2218847 = 3328271) B3328271
theorem B3328277 : Blo 2217435 3328277 := bbase (se 6 (by rfl) ⟨78006, by rfl⟩ : syracuseStep 3328277 = 156013) (by norm_num)
theorem B2218851 : Blo 2217435 2218851 := bstep (se 1 (by rfl) ⟨1664138, by rfl⟩ : syracuseStep 2218851 = 3328277) B3328277
theorem B28433429 : Blo 2217435 28433429 := bbase (se 6 (by rfl) ⟨666408, by rfl⟩ : syracuseStep 28433429 = 1332817) (by norm_num)
theorem B18955619 : Blo 2217435 18955619 := bstep (se 1 (by rfl) ⟨14216714, by rfl⟩ : syracuseStep 18955619 = 28433429) B28433429
theorem B12637079 : Blo 2217435 12637079 := bstep (se 1 (by rfl) ⟨9477809, by rfl⟩ : syracuseStep 12637079 = 18955619) B18955619
theorem B8424719 : Blo 2217435 8424719 := bstep (se 1 (by rfl) ⟨6318539, by rfl⟩ : syracuseStep 8424719 = 12637079) B12637079
theorem B5616479 : Blo 2217435 5616479 := bstep (se 1 (by rfl) ⟨4212359, by rfl⟩ : syracuseStep 5616479 = 8424719) B8424719
theorem B3744319 : Blo 2217435 3744319 := bstep (se 1 (by rfl) ⟨2808239, by rfl⟩ : syracuseStep 3744319 = 5616479) B5616479
theorem B4992425 : Blo 2217435 4992425 := bstep (se 2 (by rfl) ⟨1872159, by rfl⟩ : syracuseStep 4992425 = 3744319) B3744319
theorem B3328283 : Blo 2217435 3328283 := bstep (se 1 (by rfl) ⟨2496212, by rfl⟩ : syracuseStep 3328283 = 4992425) B4992425
theorem B2218855 : Blo 2217435 2218855 := bstep (se 1 (by rfl) ⟨1664141, by rfl⟩ : syracuseStep 2218855 = 3328283) B3328283
theorem B2496217 : Blo 2217435 2496217 := bbase (se 2 (by rfl) ⟨936081, by rfl⟩ : syracuseStep 2496217 = 1872163) (by norm_num)
theorem B3328289 : Blo 2217435 3328289 := bstep (se 2 (by rfl) ⟨1248108, by rfl⟩ : syracuseStep 3328289 = 2496217) B2496217
theorem B2218859 : Blo 2217435 2218859 := bstep (se 1 (by rfl) ⟨1664144, by rfl⟩ : syracuseStep 2218859 = 3328289) B3328289
theorem B2369461 : Blo 2217435 2369461 := bbase (se 5 (by rfl) ⟨111068, by rfl⟩ : syracuseStep 2369461 = 222137) (by norm_num)
theorem B3159281 : Blo 2217435 3159281 := bstep (se 2 (by rfl) ⟨1184730, by rfl⟩ : syracuseStep 3159281 = 2369461) B2369461
theorem B8424749 : Blo 2217435 8424749 := bstep (se 3 (by rfl) ⟨1579640, by rfl⟩ : syracuseStep 8424749 = 3159281) B3159281
theorem B5616499 : Blo 2217435 5616499 := bstep (se 1 (by rfl) ⟨4212374, by rfl⟩ : syracuseStep 5616499 = 8424749) B8424749
theorem B7488665 : Blo 2217435 7488665 := bstep (se 2 (by rfl) ⟨2808249, by rfl⟩ : syracuseStep 7488665 = 5616499) B5616499
theorem B4992443 : Blo 2217435 4992443 := bstep (se 1 (by rfl) ⟨3744332, by rfl⟩ : syracuseStep 4992443 = 7488665) B7488665
theorem B3328295 : Blo 2217435 3328295 := bstep (se 1 (by rfl) ⟨2496221, by rfl⟩ : syracuseStep 3328295 = 4992443) B4992443
theorem B2218863 : Blo 2217435 2218863 := bstep (se 1 (by rfl) ⟨1664147, by rfl⟩ : syracuseStep 2218863 = 3328295) B3328295
theorem B3328301 : Blo 2217435 3328301 := bbase (se 3 (by rfl) ⟨624056, by rfl⟩ : syracuseStep 3328301 = 1248113) (by norm_num)
theorem B2218867 : Blo 2217435 2218867 := bstep (se 1 (by rfl) ⟨1664150, by rfl⟩ : syracuseStep 2218867 = 3328301) B3328301
theorem B4992461 : Blo 2217435 4992461 := bbase (se 3 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 4992461 = 1872173) (by norm_num)
theorem B3328307 : Blo 2217435 3328307 := bstep (se 1 (by rfl) ⟨2496230, by rfl⟩ : syracuseStep 3328307 = 4992461) B4992461
theorem B2218871 : Blo 2217435 2218871 := bstep (se 1 (by rfl) ⟨1664153, by rfl⟩ : syracuseStep 2218871 = 3328307) B3328307
theorem B2808265 : Blo 2217435 2808265 := bbase (se 2 (by rfl) ⟨1053099, by rfl⟩ : syracuseStep 2808265 = 2106199) (by norm_num)
theorem B3744353 : Blo 2217435 3744353 := bstep (se 2 (by rfl) ⟨1404132, by rfl⟩ : syracuseStep 3744353 = 2808265) B2808265
theorem B2496235 : Blo 2217435 2496235 := bstep (se 1 (by rfl) ⟨1872176, by rfl⟩ : syracuseStep 2496235 = 3744353) B3744353
theorem B3328313 : Blo 2217435 3328313 := bstep (se 2 (by rfl) ⟨1248117, by rfl⟩ : syracuseStep 3328313 = 2496235) B2496235
theorem B2218875 : Blo 2217435 2218875 := bstep (se 1 (by rfl) ⟨1664156, by rfl⟩ : syracuseStep 2218875 = 3328313) B3328313
theorem B21325301 : Blo 2217435 21325301 := bbase (se 5 (by rfl) ⟨999623, by rfl⟩ : syracuseStep 21325301 = 1999247) (by norm_num)
theorem B14216867 : Blo 2217435 14216867 := bstep (se 1 (by rfl) ⟨10662650, by rfl⟩ : syracuseStep 14216867 = 21325301) B21325301
theorem B9477911 : Blo 2217435 9477911 := bstep (se 1 (by rfl) ⟨7108433, by rfl⟩ : syracuseStep 9477911 = 14216867) B14216867
theorem B25274429 : Blo 2217435 25274429 := bstep (se 3 (by rfl) ⟨4738955, by rfl⟩ : syracuseStep 25274429 = 9477911) B9477911
theorem B16849619 : Blo 2217435 16849619 := bstep (se 1 (by rfl) ⟨12637214, by rfl⟩ : syracuseStep 16849619 = 25274429) B25274429
theorem B11233079 : Blo 2217435 11233079 := bstep (se 1 (by rfl) ⟨8424809, by rfl⟩ : syracuseStep 11233079 = 16849619) B16849619
theorem B7488719 : Blo 2217435 7488719 := bstep (se 1 (by rfl) ⟨5616539, by rfl⟩ : syracuseStep 7488719 = 11233079) B11233079
theorem B4992479 : Blo 2217435 4992479 := bstep (se 1 (by rfl) ⟨3744359, by rfl⟩ : syracuseStep 4992479 = 7488719) B7488719
theorem B3328319 : Blo 2217435 3328319 := bstep (se 1 (by rfl) ⟨2496239, by rfl⟩ : syracuseStep 3328319 = 4992479) B4992479
theorem B2218879 : Blo 2217435 2218879 := bstep (se 1 (by rfl) ⟨1664159, by rfl⟩ : syracuseStep 2218879 = 3328319) B3328319
theorem B3328325 : Blo 2217435 3328325 := bbase (se 4 (by rfl) ⟨312030, by rfl⟩ : syracuseStep 3328325 = 624061) (by norm_num)
theorem B2218883 : Blo 2217435 2218883 := bstep (se 1 (by rfl) ⟨1664162, by rfl⟩ : syracuseStep 2218883 = 3328325) B3328325
theorem B3744373 : Blo 2217435 3744373 := bbase (se 5 (by rfl) ⟨175517, by rfl⟩ : syracuseStep 3744373 = 351035) (by norm_num)
theorem B4992497 : Blo 2217435 4992497 := bstep (se 2 (by rfl) ⟨1872186, by rfl⟩ : syracuseStep 4992497 = 3744373) B3744373
theorem B3328331 : Blo 2217435 3328331 := bstep (se 1 (by rfl) ⟨2496248, by rfl⟩ : syracuseStep 3328331 = 4992497) B4992497
theorem B2218887 : Blo 2217435 2218887 := bstep (se 1 (by rfl) ⟨1664165, by rfl⟩ : syracuseStep 2218887 = 3328331) B3328331
theorem B2496253 : Blo 2217435 2496253 := bbase (se 3 (by rfl) ⟨468047, by rfl⟩ : syracuseStep 2496253 = 936095) (by norm_num)
theorem B3328337 : Blo 2217435 3328337 := bstep (se 2 (by rfl) ⟨1248126, by rfl⟩ : syracuseStep 3328337 = 2496253) B2496253
theorem B2218891 : Blo 2217435 2218891 := bstep (se 1 (by rfl) ⟨1664168, by rfl⟩ : syracuseStep 2218891 = 3328337) B3328337
theorem B7488773 : Blo 2217435 7488773 := bbase (se 4 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 7488773 = 1404145) (by norm_num)
theorem B4992515 : Blo 2217435 4992515 := bstep (se 1 (by rfl) ⟨3744386, by rfl⟩ : syracuseStep 4992515 = 7488773) B7488773
theorem B3328343 : Blo 2217435 3328343 := bstep (se 1 (by rfl) ⟨2496257, by rfl⟩ : syracuseStep 3328343 = 4992515) B4992515
theorem B2218895 : Blo 2217435 2218895 := bstep (se 1 (by rfl) ⟨1664171, by rfl⟩ : syracuseStep 2218895 = 3328343) B3328343
theorem B3328349 : Blo 2217435 3328349 := bbase (se 3 (by rfl) ⟨624065, by rfl⟩ : syracuseStep 3328349 = 1248131) (by norm_num)
theorem B2218899 : Blo 2217435 2218899 := bstep (se 1 (by rfl) ⟨1664174, by rfl⟩ : syracuseStep 2218899 = 3328349) B3328349
theorem B4992533 : Blo 2217435 4992533 := bbase (se 6 (by rfl) ⟨117012, by rfl⟩ : syracuseStep 4992533 = 234025) (by norm_num)
theorem B3328355 : Blo 2217435 3328355 := bstep (se 1 (by rfl) ⟨2496266, by rfl⟩ : syracuseStep 3328355 = 4992533) B4992533
theorem B2218903 : Blo 2217435 2218903 := bstep (se 1 (by rfl) ⟨1664177, by rfl⟩ : syracuseStep 2218903 = 3328355) B3328355
theorem B8424917 : Blo 2217435 8424917 := bbase (se 7 (by rfl) ⟨98729, by rfl⟩ : syracuseStep 8424917 = 197459) (by norm_num)
theorem B5616611 : Blo 2217435 5616611 := bstep (se 1 (by rfl) ⟨4212458, by rfl⟩ : syracuseStep 5616611 = 8424917) B8424917
theorem B3744407 : Blo 2217435 3744407 := bstep (se 1 (by rfl) ⟨2808305, by rfl⟩ : syracuseStep 3744407 = 5616611) B5616611
theorem B2496271 : Blo 2217435 2496271 := bstep (se 1 (by rfl) ⟨1872203, by rfl⟩ : syracuseStep 2496271 = 3744407) B3744407
theorem B3328361 : Blo 2217435 3328361 := bstep (se 2 (by rfl) ⟨1248135, by rfl⟩ : syracuseStep 3328361 = 2496271) B2496271
theorem B2218907 : Blo 2217435 2218907 := bstep (se 1 (by rfl) ⟨1664180, by rfl⟩ : syracuseStep 2218907 = 3328361) B3328361
theorem B12637397 : Blo 2217435 12637397 := bbase (se 7 (by rfl) ⟨148094, by rfl⟩ : syracuseStep 12637397 = 296189) (by norm_num)
theorem B8424931 : Blo 2217435 8424931 := bstep (se 1 (by rfl) ⟨6318698, by rfl⟩ : syracuseStep 8424931 = 12637397) B12637397
theorem B11233241 : Blo 2217435 11233241 := bstep (se 2 (by rfl) ⟨4212465, by rfl⟩ : syracuseStep 11233241 = 8424931) B8424931
theorem B7488827 : Blo 2217435 7488827 := bstep (se 1 (by rfl) ⟨5616620, by rfl⟩ : syracuseStep 7488827 = 11233241) B11233241
theorem B4992551 : Blo 2217435 4992551 := bstep (se 1 (by rfl) ⟨3744413, by rfl⟩ : syracuseStep 4992551 = 7488827) B7488827
theorem B3328367 : Blo 2217435 3328367 := bstep (se 1 (by rfl) ⟨2496275, by rfl⟩ : syracuseStep 3328367 = 4992551) B4992551
theorem B2218911 : Blo 2217435 2218911 := bstep (se 1 (by rfl) ⟨1664183, by rfl⟩ : syracuseStep 2218911 = 3328367) B3328367
theorem B3328373 : Blo 2217435 3328373 := bbase (se 5 (by rfl) ⟨156017, by rfl⟩ : syracuseStep 3328373 = 312035) (by norm_num)
theorem B2218915 : Blo 2217435 2218915 := bstep (se 1 (by rfl) ⟨1664186, by rfl⟩ : syracuseStep 2218915 = 3328373) B3328373
theorem B2369521 : Blo 2217435 2369521 := bbase (se 2 (by rfl) ⟨888570, by rfl⟩ : syracuseStep 2369521 = 1777141) (by norm_num)
theorem B3159361 : Blo 2217435 3159361 := bstep (se 2 (by rfl) ⟨1184760, by rfl⟩ : syracuseStep 3159361 = 2369521) B2369521
theorem B4212481 : Blo 2217435 4212481 := bstep (se 2 (by rfl) ⟨1579680, by rfl⟩ : syracuseStep 4212481 = 3159361) B3159361
theorem B5616641 : Blo 2217435 5616641 := bstep (se 2 (by rfl) ⟨2106240, by rfl⟩ : syracuseStep 5616641 = 4212481) B4212481
theorem B3744427 : Blo 2217435 3744427 := bstep (se 1 (by rfl) ⟨2808320, by rfl⟩ : syracuseStep 3744427 = 5616641) B5616641
theorem B4992569 : Blo 2217435 4992569 := bstep (se 2 (by rfl) ⟨1872213, by rfl⟩ : syracuseStep 4992569 = 3744427) B3744427
theorem B3328379 : Blo 2217435 3328379 := bstep (se 1 (by rfl) ⟨2496284, by rfl⟩ : syracuseStep 3328379 = 4992569) B4992569
theorem B2218919 : Blo 2217435 2218919 := bstep (se 1 (by rfl) ⟨1664189, by rfl⟩ : syracuseStep 2218919 = 3328379) B3328379
theorem B2496289 : Blo 2217435 2496289 := bbase (se 2 (by rfl) ⟨936108, by rfl⟩ : syracuseStep 2496289 = 1872217) (by norm_num)
theorem B3328385 : Blo 2217435 3328385 := bstep (se 2 (by rfl) ⟨1248144, by rfl⟩ : syracuseStep 3328385 = 2496289) B2496289
theorem B2218923 : Blo 2217435 2218923 := bstep (se 1 (by rfl) ⟨1664192, by rfl⟩ : syracuseStep 2218923 = 3328385) B3328385
theorem B5616661 : Blo 2217435 5616661 := bbase (se 6 (by rfl) ⟨131640, by rfl⟩ : syracuseStep 5616661 = 263281) (by norm_num)
theorem B7488881 : Blo 2217435 7488881 := bstep (se 2 (by rfl) ⟨2808330, by rfl⟩ : syracuseStep 7488881 = 5616661) B5616661
theorem B4992587 : Blo 2217435 4992587 := bstep (se 1 (by rfl) ⟨3744440, by rfl⟩ : syracuseStep 4992587 = 7488881) B7488881
theorem B3328391 : Blo 2217435 3328391 := bstep (se 1 (by rfl) ⟨2496293, by rfl⟩ : syracuseStep 3328391 = 4992587) B4992587
theorem B2218927 : Blo 2217435 2218927 := bstep (se 1 (by rfl) ⟨1664195, by rfl⟩ : syracuseStep 2218927 = 3328391) B3328391
theorem B3328397 : Blo 2217435 3328397 := bbase (se 3 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 3328397 = 1248149) (by norm_num)
theorem B2218931 : Blo 2217435 2218931 := bstep (se 1 (by rfl) ⟨1664198, by rfl⟩ : syracuseStep 2218931 = 3328397) B3328397
theorem B4992605 : Blo 2217435 4992605 := bbase (se 3 (by rfl) ⟨936113, by rfl⟩ : syracuseStep 4992605 = 1872227) (by norm_num)
theorem B3328403 : Blo 2217435 3328403 := bstep (se 1 (by rfl) ⟨2496302, by rfl⟩ : syracuseStep 3328403 = 4992605) B4992605
theorem B2218935 : Blo 2217435 2218935 := bstep (se 1 (by rfl) ⟨1664201, by rfl⟩ : syracuseStep 2218935 = 3328403) B3328403
theorem B3744461 : Blo 2217435 3744461 := bbase (se 3 (by rfl) ⟨702086, by rfl⟩ : syracuseStep 3744461 = 1404173) (by norm_num)
theorem B2496307 : Blo 2217435 2496307 := bstep (se 1 (by rfl) ⟨1872230, by rfl⟩ : syracuseStep 2496307 = 3744461) B3744461
theorem B3328409 : Blo 2217435 3328409 := bstep (se 2 (by rfl) ⟨1248153, by rfl⟩ : syracuseStep 3328409 = 2496307) B2496307
theorem B2218939 : Blo 2217435 2218939 := bstep (se 1 (by rfl) ⟨1664204, by rfl⟩ : syracuseStep 2218939 = 3328409) B3328409
theorem B11995829 : Blo 2217435 11995829 := bbase (se 5 (by rfl) ⟨562304, by rfl⟩ : syracuseStep 11995829 = 1124609) (by norm_num)
theorem B7997219 : Blo 2217435 7997219 := bstep (se 1 (by rfl) ⟨5997914, by rfl⟩ : syracuseStep 7997219 = 11995829) B11995829
theorem B5331479 : Blo 2217435 5331479 := bstep (se 1 (by rfl) ⟨3998609, by rfl⟩ : syracuseStep 5331479 = 7997219) B7997219
theorem B14217277 : Blo 2217435 14217277 := bstep (se 3 (by rfl) ⟨2665739, by rfl⟩ : syracuseStep 14217277 = 5331479) B5331479
theorem B18956369 : Blo 2217435 18956369 := bstep (se 2 (by rfl) ⟨7108638, by rfl⟩ : syracuseStep 18956369 = 14217277) B14217277
theorem B12637579 : Blo 2217435 12637579 := bstep (se 1 (by rfl) ⟨9478184, by rfl⟩ : syracuseStep 12637579 = 18956369) B18956369
theorem B16850105 : Blo 2217435 16850105 := bstep (se 2 (by rfl) ⟨6318789, by rfl⟩ : syracuseStep 16850105 = 12637579) B12637579
theorem B11233403 : Blo 2217435 11233403 := bstep (se 1 (by rfl) ⟨8425052, by rfl⟩ : syracuseStep 11233403 = 16850105) B16850105
theorem B7488935 : Blo 2217435 7488935 := bstep (se 1 (by rfl) ⟨5616701, by rfl⟩ : syracuseStep 7488935 = 11233403) B11233403
theorem B4992623 : Blo 2217435 4992623 := bstep (se 1 (by rfl) ⟨3744467, by rfl⟩ : syracuseStep 4992623 = 7488935) B7488935
theorem B3328415 : Blo 2217435 3328415 := bstep (se 1 (by rfl) ⟨2496311, by rfl⟩ : syracuseStep 3328415 = 4992623) B4992623
theorem B2218943 : Blo 2217435 2218943 := bstep (se 1 (by rfl) ⟨1664207, by rfl⟩ : syracuseStep 2218943 = 3328415) B3328415
theorem B3328421 : Blo 2217435 3328421 := bbase (se 4 (by rfl) ⟨312039, by rfl⟩ : syracuseStep 3328421 = 624079) (by norm_num)
theorem B2218947 : Blo 2217435 2218947 := bstep (se 1 (by rfl) ⟨1664210, by rfl⟩ : syracuseStep 2218947 = 3328421) B3328421
theorem B2808361 : Blo 2217435 2808361 := bbase (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) (by norm_num)
theorem B3744481 : Blo 2217435 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B4992641 : Blo 2217435 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B3328427 : Blo 2217435 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B2218951 : Blo 2217435 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B2496325 : Blo 2217435 2496325 := bbase (se 4 (by rfl) ⟨234030, by rfl⟩ : syracuseStep 2496325 = 468061) (by norm_num)
theorem B3328433 : Blo 2217435 3328433 := bstep (se 2 (by rfl) ⟨1248162, by rfl⟩ : syracuseStep 3328433 = 2496325) B2496325
theorem B2218955 : Blo 2217435 2218955 := bstep (se 1 (by rfl) ⟨1664216, by rfl⟩ : syracuseStep 2218955 = 3328433) B3328433
theorem B4212557 : Blo 2217435 4212557 := bbase (se 3 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 4212557 = 1579709) (by norm_num)
theorem B2808371 : Blo 2217435 2808371 := bstep (se 1 (by rfl) ⟨2106278, by rfl⟩ : syracuseStep 2808371 = 4212557) B4212557
theorem B7488989 : Blo 2217435 7488989 := bstep (se 3 (by rfl) ⟨1404185, by rfl⟩ : syracuseStep 7488989 = 2808371) B2808371
theorem B4992659 : Blo 2217435 4992659 := bstep (se 1 (by rfl) ⟨3744494, by rfl⟩ : syracuseStep 4992659 = 7488989) B7488989
theorem B3328439 : Blo 2217435 3328439 := bstep (se 1 (by rfl) ⟨2496329, by rfl⟩ : syracuseStep 3328439 = 4992659) B4992659
theorem B2218959 : Blo 2217435 2218959 := bstep (se 1 (by rfl) ⟨1664219, by rfl⟩ : syracuseStep 2218959 = 3328439) B3328439
theorem B3328445 : Blo 2217435 3328445 := bbase (se 3 (by rfl) ⟨624083, by rfl⟩ : syracuseStep 3328445 = 1248167) (by norm_num)
theorem B2218963 : Blo 2217435 2218963 := bstep (se 1 (by rfl) ⟨1664222, by rfl⟩ : syracuseStep 2218963 = 3328445) B3328445
theorem B4992677 : Blo 2217435 4992677 := bbase (se 4 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 4992677 = 936127) (by norm_num)
theorem B3328451 : Blo 2217435 3328451 := bstep (se 1 (by rfl) ⟨2496338, by rfl⟩ : syracuseStep 3328451 = 4992677) B4992677
theorem B2218967 : Blo 2217435 2218967 := bstep (se 1 (by rfl) ⟨1664225, by rfl⟩ : syracuseStep 2218967 = 3328451) B3328451
theorem B5616773 : Blo 2217435 5616773 := bbase (se 4 (by rfl) ⟨526572, by rfl⟩ : syracuseStep 5616773 = 1053145) (by norm_num)
theorem B3744515 : Blo 2217435 3744515 := bstep (se 1 (by rfl) ⟨2808386, by rfl⟩ : syracuseStep 3744515 = 5616773) B5616773
theorem B2496343 : Blo 2217435 2496343 := bstep (se 1 (by rfl) ⟨1872257, by rfl⟩ : syracuseStep 2496343 = 3744515) B3744515
theorem B3328457 : Blo 2217435 3328457 := bstep (se 2 (by rfl) ⟨1248171, by rfl⟩ : syracuseStep 3328457 = 2496343) B2496343
theorem B2218971 : Blo 2217435 2218971 := bstep (se 1 (by rfl) ⟨1664228, by rfl⟩ : syracuseStep 2218971 = 3328457) B3328457
theorem B5331557 : Blo 2217435 5331557 := bbase (se 4 (by rfl) ⟨499833, by rfl⟩ : syracuseStep 5331557 = 999667) (by norm_num)
theorem B3554371 : Blo 2217435 3554371 := bstep (se 1 (by rfl) ⟨2665778, by rfl⟩ : syracuseStep 3554371 = 5331557) B5331557
theorem B4739161 : Blo 2217435 4739161 := bstep (se 2 (by rfl) ⟨1777185, by rfl⟩ : syracuseStep 4739161 = 3554371) B3554371
theorem B6318881 : Blo 2217435 6318881 := bstep (se 2 (by rfl) ⟨2369580, by rfl⟩ : syracuseStep 6318881 = 4739161) B4739161
theorem B4212587 : Blo 2217435 4212587 := bstep (se 1 (by rfl) ⟨3159440, by rfl⟩ : syracuseStep 4212587 = 6318881) B6318881
theorem B11233565 : Blo 2217435 11233565 := bstep (se 3 (by rfl) ⟨2106293, by rfl⟩ : syracuseStep 11233565 = 4212587) B4212587
theorem B7489043 : Blo 2217435 7489043 := bstep (se 1 (by rfl) ⟨5616782, by rfl⟩ : syracuseStep 7489043 = 11233565) B11233565
theorem B4992695 : Blo 2217435 4992695 := bstep (se 1 (by rfl) ⟨3744521, by rfl⟩ : syracuseStep 4992695 = 7489043) B7489043
theorem B3328463 : Blo 2217435 3328463 := bstep (se 1 (by rfl) ⟨2496347, by rfl⟩ : syracuseStep 3328463 = 4992695) B4992695
theorem B2218975 : Blo 2217435 2218975 := bstep (se 1 (by rfl) ⟨1664231, by rfl⟩ : syracuseStep 2218975 = 3328463) B3328463
theorem B3328469 : Blo 2217435 3328469 := bbase (se 7 (by rfl) ⟨39005, by rfl⟩ : syracuseStep 3328469 = 78011) (by norm_num)
theorem B2218979 : Blo 2217435 2218979 := bstep (se 1 (by rfl) ⟨1664234, by rfl⟩ : syracuseStep 2218979 = 3328469) B3328469
theorem B8425205 : Blo 2217435 8425205 := bbase (se 5 (by rfl) ⟨394931, by rfl⟩ : syracuseStep 8425205 = 789863) (by norm_num)
theorem B5616803 : Blo 2217435 5616803 := bstep (se 1 (by rfl) ⟨4212602, by rfl⟩ : syracuseStep 5616803 = 8425205) B8425205
theorem B3744535 : Blo 2217435 3744535 := bstep (se 1 (by rfl) ⟨2808401, by rfl⟩ : syracuseStep 3744535 = 5616803) B5616803
theorem B4992713 : Blo 2217435 4992713 := bstep (se 2 (by rfl) ⟨1872267, by rfl⟩ : syracuseStep 4992713 = 3744535) B3744535
theorem B3328475 : Blo 2217435 3328475 := bstep (se 1 (by rfl) ⟨2496356, by rfl⟩ : syracuseStep 3328475 = 4992713) B4992713
theorem B2218983 : Blo 2217435 2218983 := bstep (se 1 (by rfl) ⟨1664237, by rfl⟩ : syracuseStep 2218983 = 3328475) B3328475
theorem B2496361 : Blo 2217435 2496361 := bbase (se 2 (by rfl) ⟨936135, by rfl⟩ : syracuseStep 2496361 = 1872271) (by norm_num)
theorem B3328481 : Blo 2217435 3328481 := bstep (se 2 (by rfl) ⟨1248180, by rfl⟩ : syracuseStep 3328481 = 2496361) B2496361
theorem B2218987 : Blo 2217435 2218987 := bstep (se 1 (by rfl) ⟨1664240, by rfl⟩ : syracuseStep 2218987 = 3328481) B3328481
theorem B3373901 : Blo 2217435 3373901 := bbase (se 3 (by rfl) ⟨632606, by rfl⟩ : syracuseStep 3373901 = 1265213) (by norm_num)
theorem B2249267 : Blo 2217435 2249267 := bstep (se 1 (by rfl) ⟨1686950, by rfl⟩ : syracuseStep 2249267 = 3373901) B3373901
theorem B5998045 : Blo 2217435 5998045 := bstep (se 3 (by rfl) ⟨1124633, by rfl⟩ : syracuseStep 5998045 = 2249267) B2249267
theorem B7997393 : Blo 2217435 7997393 := bstep (se 2 (by rfl) ⟨2999022, by rfl⟩ : syracuseStep 7997393 = 5998045) B5998045
theorem B5331595 : Blo 2217435 5331595 := bstep (se 1 (by rfl) ⟨3998696, by rfl⟩ : syracuseStep 5331595 = 7997393) B7997393
theorem B7108793 : Blo 2217435 7108793 := bstep (se 2 (by rfl) ⟨2665797, by rfl⟩ : syracuseStep 7108793 = 5331595) B5331595
theorem B4739195 : Blo 2217435 4739195 := bstep (se 1 (by rfl) ⟨3554396, by rfl⟩ : syracuseStep 4739195 = 7108793) B7108793
theorem B12637853 : Blo 2217435 12637853 := bstep (se 3 (by rfl) ⟨2369597, by rfl⟩ : syracuseStep 12637853 = 4739195) B4739195
theorem B8425235 : Blo 2217435 8425235 := bstep (se 1 (by rfl) ⟨6318926, by rfl⟩ : syracuseStep 8425235 = 12637853) B12637853
theorem B5616823 : Blo 2217435 5616823 := bstep (se 1 (by rfl) ⟨4212617, by rfl⟩ : syracuseStep 5616823 = 8425235) B8425235
theorem B7489097 : Blo 2217435 7489097 := bstep (se 2 (by rfl) ⟨2808411, by rfl⟩ : syracuseStep 7489097 = 5616823) B5616823
theorem B4992731 : Blo 2217435 4992731 := bstep (se 1 (by rfl) ⟨3744548, by rfl⟩ : syracuseStep 4992731 = 7489097) B7489097
theorem B3328487 : Blo 2217435 3328487 := bstep (se 1 (by rfl) ⟨2496365, by rfl⟩ : syracuseStep 3328487 = 4992731) B4992731
theorem B2218991 : Blo 2217435 2218991 := bstep (se 1 (by rfl) ⟨1664243, by rfl⟩ : syracuseStep 2218991 = 3328487) B3328487
theorem B3328493 : Blo 2217435 3328493 := bbase (se 3 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 3328493 = 1248185) (by norm_num)
theorem B2218995 : Blo 2217435 2218995 := bstep (se 1 (by rfl) ⟨1664246, by rfl⟩ : syracuseStep 2218995 = 3328493) B3328493
theorem B4992749 : Blo 2217435 4992749 := bbase (se 3 (by rfl) ⟨936140, by rfl⟩ : syracuseStep 4992749 = 1872281) (by norm_num)
theorem B3328499 : Blo 2217435 3328499 := bstep (se 1 (by rfl) ⟨2496374, by rfl⟩ : syracuseStep 3328499 = 4992749) B4992749
theorem B2218999 : Blo 2217435 2218999 := bstep (se 1 (by rfl) ⟨1664249, by rfl⟩ : syracuseStep 2218999 = 3328499) B3328499
theorem B2665813 : Blo 2217435 2665813 := bbase (se 11 (by rfl) ⟨1952, by rfl⟩ : syracuseStep 2665813 = 3905) (by norm_num)
theorem B3554417 : Blo 2217435 3554417 := bstep (se 2 (by rfl) ⟨1332906, by rfl⟩ : syracuseStep 3554417 = 2665813) B2665813
theorem B2369611 : Blo 2217435 2369611 := bstep (se 1 (by rfl) ⟨1777208, by rfl⟩ : syracuseStep 2369611 = 3554417) B3554417
theorem B3159481 : Blo 2217435 3159481 := bstep (se 2 (by rfl) ⟨1184805, by rfl⟩ : syracuseStep 3159481 = 2369611) B2369611
theorem B4212641 : Blo 2217435 4212641 := bstep (se 2 (by rfl) ⟨1579740, by rfl⟩ : syracuseStep 4212641 = 3159481) B3159481
theorem B2808427 : Blo 2217435 2808427 := bstep (se 1 (by rfl) ⟨2106320, by rfl⟩ : syracuseStep 2808427 = 4212641) B4212641
theorem B3744569 : Blo 2217435 3744569 := bstep (se 2 (by rfl) ⟨1404213, by rfl⟩ : syracuseStep 3744569 = 2808427) B2808427
theorem B2496379 : Blo 2217435 2496379 := bstep (se 1 (by rfl) ⟨1872284, by rfl⟩ : syracuseStep 2496379 = 3744569) B3744569
theorem B3328505 : Blo 2217435 3328505 := bstep (se 2 (by rfl) ⟨1248189, by rfl⟩ : syracuseStep 3328505 = 2496379) B2496379
theorem B2219003 : Blo 2217435 2219003 := bstep (se 1 (by rfl) ⟨1664252, by rfl⟩ : syracuseStep 2219003 = 3328505) B3328505
theorem B9244309 : Blo 2217435 9244309 := bbase (se 6 (by rfl) ⟨216663, by rfl⟩ : syracuseStep 9244309 = 433327) (by norm_num)
theorem B12325745 : Blo 2217435 12325745 := bstep (se 2 (by rfl) ⟨4622154, by rfl⟩ : syracuseStep 12325745 = 9244309) B9244309
theorem B8217163 : Blo 2217435 8217163 := bstep (se 1 (by rfl) ⟨6162872, by rfl⟩ : syracuseStep 8217163 = 12325745) B12325745
theorem B10956217 : Blo 2217435 10956217 := bstep (se 2 (by rfl) ⟨4108581, by rfl⟩ : syracuseStep 10956217 = 8217163) B8217163
theorem B14608289 : Blo 2217435 14608289 := bstep (se 2 (by rfl) ⟨5478108, by rfl⟩ : syracuseStep 14608289 = 10956217) B10956217
theorem B38955437 : Blo 2217435 38955437 := bstep (se 3 (by rfl) ⟨7304144, by rfl⟩ : syracuseStep 38955437 = 14608289) B14608289
theorem B25970291 : Blo 2217435 25970291 := bstep (se 1 (by rfl) ⟨19477718, by rfl⟩ : syracuseStep 25970291 = 38955437) B38955437
theorem B17313527 : Blo 2217435 17313527 := bstep (se 1 (by rfl) ⟨12985145, by rfl⟩ : syracuseStep 17313527 = 25970291) B25970291
theorem B11542351 : Blo 2217435 11542351 := bstep (se 1 (by rfl) ⟨8656763, by rfl⟩ : syracuseStep 11542351 = 17313527) B17313527
theorem B15389801 : Blo 2217435 15389801 := bstep (se 2 (by rfl) ⟨5771175, by rfl⟩ : syracuseStep 15389801 = 11542351) B11542351
theorem B10259867 : Blo 2217435 10259867 := bstep (se 1 (by rfl) ⟨7694900, by rfl⟩ : syracuseStep 10259867 = 15389801) B15389801
theorem B6839911 : Blo 2217435 6839911 := bstep (se 1 (by rfl) ⟨5129933, by rfl⟩ : syracuseStep 6839911 = 10259867) B10259867
theorem B9119881 : Blo 2217435 9119881 := bstep (se 2 (by rfl) ⟨3419955, by rfl⟩ : syracuseStep 9119881 = 6839911) B6839911
theorem B48639365 : Blo 2217435 48639365 := bstep (se 4 (by rfl) ⟨4559940, by rfl⟩ : syracuseStep 48639365 = 9119881) B9119881
theorem B32426243 : Blo 2217435 32426243 := bstep (se 1 (by rfl) ⟨24319682, by rfl⟩ : syracuseStep 32426243 = 48639365) B48639365
theorem B21617495 : Blo 2217435 21617495 := bstep (se 1 (by rfl) ⟨16213121, by rfl⟩ : syracuseStep 21617495 = 32426243) B32426243
theorem B14411663 : Blo 2217435 14411663 := bstep (se 1 (by rfl) ⟨10808747, by rfl⟩ : syracuseStep 14411663 = 21617495) B21617495
theorem B153724405 : Blo 2217435 153724405 := bstep (se 5 (by rfl) ⟨7205831, by rfl⟩ : syracuseStep 153724405 = 14411663) B14411663
theorem B204965873 : Blo 2217435 204965873 := bstep (se 2 (by rfl) ⟨76862202, by rfl⟩ : syracuseStep 204965873 = 153724405) B153724405
theorem B136643915 : Blo 2217435 136643915 := bstep (se 1 (by rfl) ⟨102482936, by rfl⟩ : syracuseStep 136643915 = 204965873) B204965873
theorem B91095943 : Blo 2217435 91095943 := bstep (se 1 (by rfl) ⟨68321957, by rfl⟩ : syracuseStep 91095943 = 136643915) B136643915
theorem B121461257 : Blo 2217435 121461257 := bstep (se 2 (by rfl) ⟨45547971, by rfl⟩ : syracuseStep 121461257 = 91095943) B91095943
theorem B80974171 : Blo 2217435 80974171 := bstep (se 1 (by rfl) ⟨60730628, by rfl⟩ : syracuseStep 80974171 = 121461257) B121461257
theorem B107965561 : Blo 2217435 107965561 := bstep (se 2 (by rfl) ⟨40487085, by rfl⟩ : syracuseStep 107965561 = 80974171) B80974171
theorem B143954081 : Blo 2217435 143954081 := bstep (se 2 (by rfl) ⟨53982780, by rfl⟩ : syracuseStep 143954081 = 107965561) B107965561
theorem B95969387 : Blo 2217435 95969387 := bstep (se 1 (by rfl) ⟨71977040, by rfl⟩ : syracuseStep 95969387 = 143954081) B143954081
theorem B63979591 : Blo 2217435 63979591 := bstep (se 1 (by rfl) ⟨47984693, by rfl⟩ : syracuseStep 63979591 = 95969387) B95969387
theorem B85306121 : Blo 2217435 85306121 := bstep (se 2 (by rfl) ⟨31989795, by rfl⟩ : syracuseStep 85306121 = 63979591) B63979591
theorem B56870747 : Blo 2217435 56870747 := bstep (se 1 (by rfl) ⟨42653060, by rfl⟩ : syracuseStep 56870747 = 85306121) B85306121
theorem B37913831 : Blo 2217435 37913831 := bstep (se 1 (by rfl) ⟨28435373, by rfl⟩ : syracuseStep 37913831 = 56870747) B56870747
theorem B25275887 : Blo 2217435 25275887 := bstep (se 1 (by rfl) ⟨18956915, by rfl⟩ : syracuseStep 25275887 = 37913831) B37913831
theorem B16850591 : Blo 2217435 16850591 := bstep (se 1 (by rfl) ⟨12637943, by rfl⟩ : syracuseStep 16850591 = 25275887) B25275887
theorem B11233727 : Blo 2217435 11233727 := bstep (se 1 (by rfl) ⟨8425295, by rfl⟩ : syracuseStep 11233727 = 16850591) B16850591
theorem B7489151 : Blo 2217435 7489151 := bstep (se 1 (by rfl) ⟨5616863, by rfl⟩ : syracuseStep 7489151 = 11233727) B11233727
theorem B4992767 : Blo 2217435 4992767 := bstep (se 1 (by rfl) ⟨3744575, by rfl⟩ : syracuseStep 4992767 = 7489151) B7489151
theorem B3328511 : Blo 2217435 3328511 := bstep (se 1 (by rfl) ⟨2496383, by rfl⟩ : syracuseStep 3328511 = 4992767) B4992767
theorem B2219007 : Blo 2217435 2219007 := bstep (se 1 (by rfl) ⟨1664255, by rfl⟩ : syracuseStep 2219007 = 3328511) B3328511
theorem B3328517 : Blo 2217435 3328517 := bbase (se 4 (by rfl) ⟨312048, by rfl⟩ : syracuseStep 3328517 = 624097) (by norm_num)
theorem B2219011 : Blo 2217435 2219011 := bstep (se 1 (by rfl) ⟨1664258, by rfl⟩ : syracuseStep 2219011 = 3328517) B3328517
theorem B3744589 : Blo 2217435 3744589 := bbase (se 3 (by rfl) ⟨702110, by rfl⟩ : syracuseStep 3744589 = 1404221) (by norm_num)
theorem B4992785 : Blo 2217435 4992785 := bstep (se 2 (by rfl) ⟨1872294, by rfl⟩ : syracuseStep 4992785 = 3744589) B3744589
theorem B3328523 : Blo 2217435 3328523 := bstep (se 1 (by rfl) ⟨2496392, by rfl⟩ : syracuseStep 3328523 = 4992785) B4992785
theorem B2219015 : Blo 2217435 2219015 := bstep (se 1 (by rfl) ⟨1664261, by rfl⟩ : syracuseStep 2219015 = 3328523) B3328523
theorem B2496397 : Blo 2217435 2496397 := bbase (se 3 (by rfl) ⟨468074, by rfl⟩ : syracuseStep 2496397 = 936149) (by norm_num)
theorem B3328529 : Blo 2217435 3328529 := bstep (se 2 (by rfl) ⟨1248198, by rfl⟩ : syracuseStep 3328529 = 2496397) B2496397
theorem B2219019 : Blo 2217435 2219019 := bstep (se 1 (by rfl) ⟨1664264, by rfl⟩ : syracuseStep 2219019 = 3328529) B3328529
theorem B7489205 : Blo 2217435 7489205 := bbase (se 5 (by rfl) ⟨351056, by rfl⟩ : syracuseStep 7489205 = 702113) (by norm_num)
theorem B4992803 : Blo 2217435 4992803 := bstep (se 1 (by rfl) ⟨3744602, by rfl⟩ : syracuseStep 4992803 = 7489205) B7489205
theorem B3328535 : Blo 2217435 3328535 := bstep (se 1 (by rfl) ⟨2496401, by rfl⟩ : syracuseStep 3328535 = 4992803) B4992803
theorem B2219023 : Blo 2217435 2219023 := bstep (se 1 (by rfl) ⟨1664267, by rfl⟩ : syracuseStep 2219023 = 3328535) B3328535
theorem B3328541 : Blo 2217435 3328541 := bbase (se 3 (by rfl) ⟨624101, by rfl⟩ : syracuseStep 3328541 = 1248203) (by norm_num)
theorem B2219027 : Blo 2217435 2219027 := bstep (se 1 (by rfl) ⟨1664270, by rfl⟩ : syracuseStep 2219027 = 3328541) B3328541
theorem B4992821 : Blo 2217435 4992821 := bbase (se 5 (by rfl) ⟨234038, by rfl⟩ : syracuseStep 4992821 = 468077) (by norm_num)
theorem B3328547 : Blo 2217435 3328547 := bstep (se 1 (by rfl) ⟨2496410, by rfl⟩ : syracuseStep 3328547 = 4992821) B4992821
theorem B2219031 : Blo 2217435 2219031 := bstep (se 1 (by rfl) ⟨1664273, by rfl⟩ : syracuseStep 2219031 = 3328547) B3328547
theorem B5331701 : Blo 2217435 5331701 := bbase (se 5 (by rfl) ⟨249923, by rfl⟩ : syracuseStep 5331701 = 499847) (by norm_num)
theorem B14217869 : Blo 2217435 14217869 := bstep (se 3 (by rfl) ⟨2665850, by rfl⟩ : syracuseStep 14217869 = 5331701) B5331701
theorem B9478579 : Blo 2217435 9478579 := bstep (se 1 (by rfl) ⟨7108934, by rfl⟩ : syracuseStep 9478579 = 14217869) B14217869
theorem B12638105 : Blo 2217435 12638105 := bstep (se 2 (by rfl) ⟨4739289, by rfl⟩ : syracuseStep 12638105 = 9478579) B9478579
theorem B8425403 : Blo 2217435 8425403 := bstep (se 1 (by rfl) ⟨6319052, by rfl⟩ : syracuseStep 8425403 = 12638105) B12638105
theorem B5616935 : Blo 2217435 5616935 := bstep (se 1 (by rfl) ⟨4212701, by rfl⟩ : syracuseStep 5616935 = 8425403) B8425403
theorem B3744623 : Blo 2217435 3744623 := bstep (se 1 (by rfl) ⟨2808467, by rfl⟩ : syracuseStep 3744623 = 5616935) B5616935
theorem B2496415 : Blo 2217435 2496415 := bstep (se 1 (by rfl) ⟨1872311, by rfl⟩ : syracuseStep 2496415 = 3744623) B3744623
theorem B3328553 : Blo 2217435 3328553 := bstep (se 2 (by rfl) ⟨1248207, by rfl⟩ : syracuseStep 3328553 = 2496415) B2496415
theorem B2219035 : Blo 2217435 2219035 := bstep (se 1 (by rfl) ⟨1664276, by rfl⟩ : syracuseStep 2219035 = 3328553) B3328553
theorem B5693581 : Blo 2217435 5693581 := bbase (se 3 (by rfl) ⟨1067546, by rfl⟩ : syracuseStep 5693581 = 2135093) (by norm_num)
theorem B30365765 : Blo 2217435 30365765 := bstep (se 4 (by rfl) ⟨2846790, by rfl⟩ : syracuseStep 30365765 = 5693581) B5693581
theorem B20243843 : Blo 2217435 20243843 := bstep (se 1 (by rfl) ⟨15182882, by rfl⟩ : syracuseStep 20243843 = 30365765) B30365765
theorem B13495895 : Blo 2217435 13495895 := bstep (se 1 (by rfl) ⟨10121921, by rfl⟩ : syracuseStep 13495895 = 20243843) B20243843
theorem B8997263 : Blo 2217435 8997263 := bstep (se 1 (by rfl) ⟨6747947, by rfl⟩ : syracuseStep 8997263 = 13495895) B13495895
theorem B5998175 : Blo 2217435 5998175 := bstep (se 1 (by rfl) ⟨4498631, by rfl⟩ : syracuseStep 5998175 = 8997263) B8997263
theorem B3998783 : Blo 2217435 3998783 := bstep (se 1 (by rfl) ⟨2999087, by rfl⟩ : syracuseStep 3998783 = 5998175) B5998175
theorem B2665855 : Blo 2217435 2665855 := bstep (se 1 (by rfl) ⟨1999391, by rfl⟩ : syracuseStep 2665855 = 3998783) B3998783
theorem B14217893 : Blo 2217435 14217893 := bstep (se 4 (by rfl) ⟨1332927, by rfl⟩ : syracuseStep 14217893 = 2665855) B2665855
theorem B9478595 : Blo 2217435 9478595 := bstep (se 1 (by rfl) ⟨7108946, by rfl⟩ : syracuseStep 9478595 = 14217893) B14217893
theorem B6319063 : Blo 2217435 6319063 := bstep (se 1 (by rfl) ⟨4739297, by rfl⟩ : syracuseStep 6319063 = 9478595) B9478595
theorem B8425417 : Blo 2217435 8425417 := bstep (se 2 (by rfl) ⟨3159531, by rfl⟩ : syracuseStep 8425417 = 6319063) B6319063
theorem B11233889 : Blo 2217435 11233889 := bstep (se 2 (by rfl) ⟨4212708, by rfl⟩ : syracuseStep 11233889 = 8425417) B8425417
theorem B7489259 : Blo 2217435 7489259 := bstep (se 1 (by rfl) ⟨5616944, by rfl⟩ : syracuseStep 7489259 = 11233889) B11233889
theorem B4992839 : Blo 2217435 4992839 := bstep (se 1 (by rfl) ⟨3744629, by rfl⟩ : syracuseStep 4992839 = 7489259) B7489259
theorem B3328559 : Blo 2217435 3328559 := bstep (se 1 (by rfl) ⟨2496419, by rfl⟩ : syracuseStep 3328559 = 4992839) B4992839
theorem B2219039 : Blo 2217435 2219039 := bstep (se 1 (by rfl) ⟨1664279, by rfl⟩ : syracuseStep 2219039 = 3328559) B3328559
theorem B3328565 : Blo 2217435 3328565 := bbase (se 5 (by rfl) ⟨156026, by rfl⟩ : syracuseStep 3328565 = 312053) (by norm_num)
theorem B2219043 : Blo 2217435 2219043 := bstep (se 1 (by rfl) ⟨1664282, by rfl⟩ : syracuseStep 2219043 = 3328565) B3328565
theorem B5616965 : Blo 2217435 5616965 := bbase (se 4 (by rfl) ⟨526590, by rfl⟩ : syracuseStep 5616965 = 1053181) (by norm_num)
theorem B3744643 : Blo 2217435 3744643 := bstep (se 1 (by rfl) ⟨2808482, by rfl⟩ : syracuseStep 3744643 = 5616965) B5616965
theorem B4992857 : Blo 2217435 4992857 := bstep (se 2 (by rfl) ⟨1872321, by rfl⟩ : syracuseStep 4992857 = 3744643) B3744643
theorem B3328571 : Blo 2217435 3328571 := bstep (se 1 (by rfl) ⟨2496428, by rfl⟩ : syracuseStep 3328571 = 4992857) B4992857
theorem B2219047 : Blo 2217435 2219047 := bstep (se 1 (by rfl) ⟨1664285, by rfl⟩ : syracuseStep 2219047 = 3328571) B3328571
theorem B2496433 : Blo 2217435 2496433 := bbase (se 2 (by rfl) ⟨936162, by rfl⟩ : syracuseStep 2496433 = 1872325) (by norm_num)
theorem B3328577 : Blo 2217435 3328577 := bstep (se 2 (by rfl) ⟨1248216, by rfl⟩ : syracuseStep 3328577 = 2496433) B2496433
theorem B2219051 : Blo 2217435 2219051 := bstep (se 1 (by rfl) ⟨1664288, by rfl⟩ : syracuseStep 2219051 = 3328577) B3328577
theorem B6319109 : Blo 2217435 6319109 := bbase (se 4 (by rfl) ⟨592416, by rfl⟩ : syracuseStep 6319109 = 1184833) (by norm_num)
theorem B4212739 : Blo 2217435 4212739 := bstep (se 1 (by rfl) ⟨3159554, by rfl⟩ : syracuseStep 4212739 = 6319109) B6319109
theorem B5616985 : Blo 2217435 5616985 := bstep (se 2 (by rfl) ⟨2106369, by rfl⟩ : syracuseStep 5616985 = 4212739) B4212739
theorem B7489313 : Blo 2217435 7489313 := bstep (se 2 (by rfl) ⟨2808492, by rfl⟩ : syracuseStep 7489313 = 5616985) B5616985
theorem B4992875 : Blo 2217435 4992875 := bstep (se 1 (by rfl) ⟨3744656, by rfl⟩ : syracuseStep 4992875 = 7489313) B7489313
theorem B3328583 : Blo 2217435 3328583 := bstep (se 1 (by rfl) ⟨2496437, by rfl⟩ : syracuseStep 3328583 = 4992875) B4992875
theorem B2219055 : Blo 2217435 2219055 := bstep (se 1 (by rfl) ⟨1664291, by rfl⟩ : syracuseStep 2219055 = 3328583) B3328583
theorem B3328589 : Blo 2217435 3328589 := bbase (se 3 (by rfl) ⟨624110, by rfl⟩ : syracuseStep 3328589 = 1248221) (by norm_num)
theorem B2219059 : Blo 2217435 2219059 := bstep (se 1 (by rfl) ⟨1664294, by rfl⟩ : syracuseStep 2219059 = 3328589) B3328589
theorem B4992893 : Blo 2217435 4992893 := bbase (se 3 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 4992893 = 1872335) (by norm_num)
theorem B3328595 : Blo 2217435 3328595 := bstep (se 1 (by rfl) ⟨2496446, by rfl⟩ : syracuseStep 3328595 = 4992893) B4992893
theorem B2219063 : Blo 2217435 2219063 := bstep (se 1 (by rfl) ⟨1664297, by rfl⟩ : syracuseStep 2219063 = 3328595) B3328595
theorem B3744677 : Blo 2217435 3744677 := bbase (se 4 (by rfl) ⟨351063, by rfl⟩ : syracuseStep 3744677 = 702127) (by norm_num)
theorem B2496451 : Blo 2217435 2496451 := bstep (se 1 (by rfl) ⟨1872338, by rfl⟩ : syracuseStep 2496451 = 3744677) B3744677
theorem B3328601 : Blo 2217435 3328601 := bstep (se 2 (by rfl) ⟨1248225, by rfl⟩ : syracuseStep 3328601 = 2496451) B2496451
theorem B2219067 : Blo 2217435 2219067 := bstep (se 1 (by rfl) ⟨1664300, by rfl⟩ : syracuseStep 2219067 = 3328601) B3328601
theorem B3554525 : Blo 2217435 3554525 := bbase (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) (by norm_num)
theorem B2369683 : Blo 2217435 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B3159577 : Blo 2217435 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B16851077 : Blo 2217435 16851077 := bstep (se 4 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 16851077 = 3159577) B3159577
theorem B11234051 : Blo 2217435 11234051 := bstep (se 1 (by rfl) ⟨8425538, by rfl⟩ : syracuseStep 11234051 = 16851077) B16851077
theorem B7489367 : Blo 2217435 7489367 := bstep (se 1 (by rfl) ⟨5617025, by rfl⟩ : syracuseStep 7489367 = 11234051) B11234051
theorem B4992911 : Blo 2217435 4992911 := bstep (se 1 (by rfl) ⟨3744683, by rfl⟩ : syracuseStep 4992911 = 7489367) B7489367
theorem B3328607 : Blo 2217435 3328607 := bstep (se 1 (by rfl) ⟨2496455, by rfl⟩ : syracuseStep 3328607 = 4992911) B4992911
theorem B2219071 : Blo 2217435 2219071 := bstep (se 1 (by rfl) ⟨1664303, by rfl⟩ : syracuseStep 2219071 = 3328607) B3328607
theorem B3328613 : Blo 2217435 3328613 := bbase (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) (by norm_num)
theorem B2219075 : Blo 2217435 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B3159589 : Blo 2217435 3159589 := bbase (se 4 (by rfl) ⟨296211, by rfl⟩ : syracuseStep 3159589 = 592423) (by norm_num)
theorem B4212785 : Blo 2217435 4212785 := bstep (se 2 (by rfl) ⟨1579794, by rfl⟩ : syracuseStep 4212785 = 3159589) B3159589
theorem B2808523 : Blo 2217435 2808523 := bstep (se 1 (by rfl) ⟨2106392, by rfl⟩ : syracuseStep 2808523 = 4212785) B4212785
theorem B3744697 : Blo 2217435 3744697 := bstep (se 2 (by rfl) ⟨1404261, by rfl⟩ : syracuseStep 3744697 = 2808523) B2808523
theorem B4992929 : Blo 2217435 4992929 := bstep (se 2 (by rfl) ⟨1872348, by rfl⟩ : syracuseStep 4992929 = 3744697) B3744697
theorem B3328619 : Blo 2217435 3328619 := bstep (se 1 (by rfl) ⟨2496464, by rfl⟩ : syracuseStep 3328619 = 4992929) B4992929
theorem B2219079 : Blo 2217435 2219079 := bstep (se 1 (by rfl) ⟨1664309, by rfl⟩ : syracuseStep 2219079 = 3328619) B3328619
theorem B2496469 : Blo 2217435 2496469 := bbase (se 7 (by rfl) ⟨29255, by rfl⟩ : syracuseStep 2496469 = 58511) (by norm_num)
theorem B3328625 : Blo 2217435 3328625 := bstep (se 2 (by rfl) ⟨1248234, by rfl⟩ : syracuseStep 3328625 = 2496469) B2496469
theorem B2219083 : Blo 2217435 2219083 := bstep (se 1 (by rfl) ⟨1664312, by rfl⟩ : syracuseStep 2219083 = 3328625) B3328625
theorem B2808533 : Blo 2217435 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B7489421 : Blo 2217435 7489421 := bstep (se 3 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 7489421 = 2808533) B2808533
theorem B4992947 : Blo 2217435 4992947 := bstep (se 1 (by rfl) ⟨3744710, by rfl⟩ : syracuseStep 4992947 = 7489421) B7489421
theorem B3328631 : Blo 2217435 3328631 := bstep (se 1 (by rfl) ⟨2496473, by rfl⟩ : syracuseStep 3328631 = 4992947) B4992947
theorem B2219087 : Blo 2217435 2219087 := bstep (se 1 (by rfl) ⟨1664315, by rfl⟩ : syracuseStep 2219087 = 3328631) B3328631
theorem B3328637 : Blo 2217435 3328637 := bbase (se 3 (by rfl) ⟨624119, by rfl⟩ : syracuseStep 3328637 = 1248239) (by norm_num)
theorem B2219091 : Blo 2217435 2219091 := bstep (se 1 (by rfl) ⟨1664318, by rfl⟩ : syracuseStep 2219091 = 3328637) B3328637
theorem B4992965 : Blo 2217435 4992965 := bbase (se 4 (by rfl) ⟨468090, by rfl⟩ : syracuseStep 4992965 = 936181) (by norm_num)
theorem B3328643 : Blo 2217435 3328643 := bstep (se 1 (by rfl) ⟨2496482, by rfl⟩ : syracuseStep 3328643 = 4992965) B4992965
theorem B2219095 : Blo 2217435 2219095 := bstep (se 1 (by rfl) ⟨1664321, by rfl⟩ : syracuseStep 2219095 = 3328643) B3328643
theorem B9478853 : Blo 2217435 9478853 := bbase (se 4 (by rfl) ⟨888642, by rfl⟩ : syracuseStep 9478853 = 1777285) (by norm_num)
theorem B6319235 : Blo 2217435 6319235 := bstep (se 1 (by rfl) ⟨4739426, by rfl⟩ : syracuseStep 6319235 = 9478853) B9478853
theorem B4212823 : Blo 2217435 4212823 := bstep (se 1 (by rfl) ⟨3159617, by rfl⟩ : syracuseStep 4212823 = 6319235) B6319235
theorem B5617097 : Blo 2217435 5617097 := bstep (se 2 (by rfl) ⟨2106411, by rfl⟩ : syracuseStep 5617097 = 4212823) B4212823
theorem B3744731 : Blo 2217435 3744731 := bstep (se 1 (by rfl) ⟨2808548, by rfl⟩ : syracuseStep 3744731 = 5617097) B5617097
theorem B2496487 : Blo 2217435 2496487 := bstep (se 1 (by rfl) ⟨1872365, by rfl⟩ : syracuseStep 2496487 = 3744731) B3744731
theorem B3328649 : Blo 2217435 3328649 := bstep (se 2 (by rfl) ⟨1248243, by rfl⟩ : syracuseStep 3328649 = 2496487) B2496487
theorem B2219099 : Blo 2217435 2219099 := bstep (se 1 (by rfl) ⟨1664324, by rfl⟩ : syracuseStep 2219099 = 3328649) B3328649
theorem B11234213 : Blo 2217435 11234213 := bbase (se 4 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 11234213 = 2106415) (by norm_num)
theorem B7489475 : Blo 2217435 7489475 := bstep (se 1 (by rfl) ⟨5617106, by rfl⟩ : syracuseStep 7489475 = 11234213) B11234213
theorem B4992983 : Blo 2217435 4992983 := bstep (se 1 (by rfl) ⟨3744737, by rfl⟩ : syracuseStep 4992983 = 7489475) B7489475
theorem B3328655 : Blo 2217435 3328655 := bstep (se 1 (by rfl) ⟨2496491, by rfl⟩ : syracuseStep 3328655 = 4992983) B4992983
theorem B2219103 : Blo 2217435 2219103 := bstep (se 1 (by rfl) ⟨1664327, by rfl⟩ : syracuseStep 2219103 = 3328655) B3328655
theorem B3328661 : Blo 2217435 3328661 := bbase (se 6 (by rfl) ⟨78015, by rfl⟩ : syracuseStep 3328661 = 156031) (by norm_num)
theorem B2219107 : Blo 2217435 2219107 := bstep (se 1 (by rfl) ⟨1664330, by rfl⟩ : syracuseStep 2219107 = 3328661) B3328661
theorem B5061125 : Blo 2217435 5061125 := bbase (se 4 (by rfl) ⟨474480, by rfl⟩ : syracuseStep 5061125 = 948961) (by norm_num)
theorem B3374083 : Blo 2217435 3374083 := bstep (se 1 (by rfl) ⟨2530562, by rfl⟩ : syracuseStep 3374083 = 5061125) B5061125
theorem B4498777 : Blo 2217435 4498777 := bstep (se 2 (by rfl) ⟨1687041, by rfl⟩ : syracuseStep 4498777 = 3374083) B3374083
theorem B5998369 : Blo 2217435 5998369 := bstep (se 2 (by rfl) ⟨2249388, by rfl⟩ : syracuseStep 5998369 = 4498777) B4498777
theorem B7997825 : Blo 2217435 7997825 := bstep (se 2 (by rfl) ⟨2999184, by rfl⟩ : syracuseStep 7997825 = 5998369) B5998369
theorem B21327533 : Blo 2217435 21327533 := bstep (se 3 (by rfl) ⟨3998912, by rfl⟩ : syracuseStep 21327533 = 7997825) B7997825
theorem B14218355 : Blo 2217435 14218355 := bstep (se 1 (by rfl) ⟨10663766, by rfl⟩ : syracuseStep 14218355 = 21327533) B21327533
theorem B9478903 : Blo 2217435 9478903 := bstep (se 1 (by rfl) ⟨7109177, by rfl⟩ : syracuseStep 9478903 = 14218355) B14218355
theorem B12638537 : Blo 2217435 12638537 := bstep (se 2 (by rfl) ⟨4739451, by rfl⟩ : syracuseStep 12638537 = 9478903) B9478903
theorem B8425691 : Blo 2217435 8425691 := bstep (se 1 (by rfl) ⟨6319268, by rfl⟩ : syracuseStep 8425691 = 12638537) B12638537
theorem B5617127 : Blo 2217435 5617127 := bstep (se 1 (by rfl) ⟨4212845, by rfl⟩ : syracuseStep 5617127 = 8425691) B8425691
theorem B3744751 : Blo 2217435 3744751 := bstep (se 1 (by rfl) ⟨2808563, by rfl⟩ : syracuseStep 3744751 = 5617127) B5617127
theorem B4993001 : Blo 2217435 4993001 := bstep (se 2 (by rfl) ⟨1872375, by rfl⟩ : syracuseStep 4993001 = 3744751) B3744751
theorem B3328667 : Blo 2217435 3328667 := bstep (se 1 (by rfl) ⟨2496500, by rfl⟩ : syracuseStep 3328667 = 4993001) B4993001
theorem B2219111 : Blo 2217435 2219111 := bstep (se 1 (by rfl) ⟨1664333, by rfl⟩ : syracuseStep 2219111 = 3328667) B3328667
theorem B2496505 : Blo 2217435 2496505 := bbase (se 2 (by rfl) ⟨936189, by rfl⟩ : syracuseStep 2496505 = 1872379) (by norm_num)
theorem B3328673 : Blo 2217435 3328673 := bstep (se 2 (by rfl) ⟨1248252, by rfl⟩ : syracuseStep 3328673 = 2496505) B2496505
theorem B2219115 : Blo 2217435 2219115 := bstep (se 1 (by rfl) ⟨1664336, by rfl⟩ : syracuseStep 2219115 = 3328673) B3328673
theorem B11387573 : Blo 2217435 11387573 := bbase (se 5 (by rfl) ⟨533792, by rfl⟩ : syracuseStep 11387573 = 1067585) (by norm_num)
theorem B7591715 : Blo 2217435 7591715 := bstep (se 1 (by rfl) ⟨5693786, by rfl⟩ : syracuseStep 7591715 = 11387573) B11387573
theorem B5061143 : Blo 2217435 5061143 := bstep (se 1 (by rfl) ⟨3795857, by rfl⟩ : syracuseStep 5061143 = 7591715) B7591715
theorem B13496381 : Blo 2217435 13496381 := bstep (se 3 (by rfl) ⟨2530571, by rfl⟩ : syracuseStep 13496381 = 5061143) B5061143
theorem B8997587 : Blo 2217435 8997587 := bstep (se 1 (by rfl) ⟨6748190, by rfl⟩ : syracuseStep 8997587 = 13496381) B13496381
theorem B5998391 : Blo 2217435 5998391 := bstep (se 1 (by rfl) ⟨4498793, by rfl⟩ : syracuseStep 5998391 = 8997587) B8997587
theorem B3998927 : Blo 2217435 3998927 := bstep (se 1 (by rfl) ⟨2999195, by rfl⟩ : syracuseStep 3998927 = 5998391) B5998391
theorem B10663805 : Blo 2217435 10663805 := bstep (se 3 (by rfl) ⟨1999463, by rfl⟩ : syracuseStep 10663805 = 3998927) B3998927
theorem B7109203 : Blo 2217435 7109203 := bstep (se 1 (by rfl) ⟨5331902, by rfl⟩ : syracuseStep 7109203 = 10663805) B10663805
theorem B9478937 : Blo 2217435 9478937 := bstep (se 2 (by rfl) ⟨3554601, by rfl⟩ : syracuseStep 9478937 = 7109203) B7109203
theorem B6319291 : Blo 2217435 6319291 := bstep (se 1 (by rfl) ⟨4739468, by rfl⟩ : syracuseStep 6319291 = 9478937) B9478937
theorem B8425721 : Blo 2217435 8425721 := bstep (se 2 (by rfl) ⟨3159645, by rfl⟩ : syracuseStep 8425721 = 6319291) B6319291
theorem B5617147 : Blo 2217435 5617147 := bstep (se 1 (by rfl) ⟨4212860, by rfl⟩ : syracuseStep 5617147 = 8425721) B8425721
theorem B7489529 : Blo 2217435 7489529 := bstep (se 2 (by rfl) ⟨2808573, by rfl⟩ : syracuseStep 7489529 = 5617147) B5617147
theorem B4993019 : Blo 2217435 4993019 := bstep (se 1 (by rfl) ⟨3744764, by rfl⟩ : syracuseStep 4993019 = 7489529) B7489529
theorem B3328679 : Blo 2217435 3328679 := bstep (se 1 (by rfl) ⟨2496509, by rfl⟩ : syracuseStep 3328679 = 4993019) B4993019
theorem B2219119 : Blo 2217435 2219119 := bstep (se 1 (by rfl) ⟨1664339, by rfl⟩ : syracuseStep 2219119 = 3328679) B3328679
theorem B3328685 : Blo 2217435 3328685 := bbase (se 3 (by rfl) ⟨624128, by rfl⟩ : syracuseStep 3328685 = 1248257) (by norm_num)
theorem B2219123 : Blo 2217435 2219123 := bstep (se 1 (by rfl) ⟨1664342, by rfl⟩ : syracuseStep 2219123 = 3328685) B3328685
theorem B4993037 : Blo 2217435 4993037 := bbase (se 3 (by rfl) ⟨936194, by rfl⟩ : syracuseStep 4993037 = 1872389) (by norm_num)
theorem B3328691 : Blo 2217435 3328691 := bstep (se 1 (by rfl) ⟨2496518, by rfl⟩ : syracuseStep 3328691 = 4993037) B4993037
theorem B2219127 : Blo 2217435 2219127 := bstep (se 1 (by rfl) ⟨1664345, by rfl⟩ : syracuseStep 2219127 = 3328691) B3328691
theorem B2808589 : Blo 2217435 2808589 := bbase (se 3 (by rfl) ⟨526610, by rfl⟩ : syracuseStep 2808589 = 1053221) (by norm_num)
theorem B3744785 : Blo 2217435 3744785 := bstep (se 2 (by rfl) ⟨1404294, by rfl⟩ : syracuseStep 3744785 = 2808589) B2808589
theorem B2496523 : Blo 2217435 2496523 := bstep (se 1 (by rfl) ⟨1872392, by rfl⟩ : syracuseStep 2496523 = 3744785) B3744785
theorem B3328697 : Blo 2217435 3328697 := bstep (se 2 (by rfl) ⟨1248261, by rfl⟩ : syracuseStep 3328697 = 2496523) B2496523
theorem B2219131 : Blo 2217435 2219131 := bstep (se 1 (by rfl) ⟨1664348, by rfl⟩ : syracuseStep 2219131 = 3328697) B3328697
theorem B8540741 : Blo 2217435 8540741 := bbase (se 4 (by rfl) ⟨800694, by rfl⟩ : syracuseStep 8540741 = 1601389) (by norm_num)
theorem B5693827 : Blo 2217435 5693827 := bstep (se 1 (by rfl) ⟨4270370, by rfl⟩ : syracuseStep 5693827 = 8540741) B8540741
theorem B7591769 : Blo 2217435 7591769 := bstep (se 2 (by rfl) ⟨2846913, by rfl⟩ : syracuseStep 7591769 = 5693827) B5693827
theorem B5061179 : Blo 2217435 5061179 := bstep (se 1 (by rfl) ⟨3795884, by rfl⟩ : syracuseStep 5061179 = 7591769) B7591769
theorem B3374119 : Blo 2217435 3374119 := bstep (se 1 (by rfl) ⟨2530589, by rfl⟩ : syracuseStep 3374119 = 5061179) B5061179
theorem B4498825 : Blo 2217435 4498825 := bstep (se 2 (by rfl) ⟨1687059, by rfl⟩ : syracuseStep 4498825 = 3374119) B3374119
theorem B5998433 : Blo 2217435 5998433 := bstep (se 2 (by rfl) ⟨2249412, by rfl⟩ : syracuseStep 5998433 = 4498825) B4498825
theorem B15995821 : Blo 2217435 15995821 := bstep (se 3 (by rfl) ⟨2999216, by rfl⟩ : syracuseStep 15995821 = 5998433) B5998433
theorem B21327761 : Blo 2217435 21327761 := bstep (se 2 (by rfl) ⟨7997910, by rfl⟩ : syracuseStep 21327761 = 15995821) B15995821
theorem B14218507 : Blo 2217435 14218507 := bstep (se 1 (by rfl) ⟨10663880, by rfl⟩ : syracuseStep 14218507 = 21327761) B21327761
theorem B18958009 : Blo 2217435 18958009 := bstep (se 2 (by rfl) ⟨7109253, by rfl⟩ : syracuseStep 18958009 = 14218507) B14218507
theorem B25277345 : Blo 2217435 25277345 := bstep (se 2 (by rfl) ⟨9479004, by rfl⟩ : syracuseStep 25277345 = 18958009) B18958009
theorem B16851563 : Blo 2217435 16851563 := bstep (se 1 (by rfl) ⟨12638672, by rfl⟩ : syracuseStep 16851563 = 25277345) B25277345
theorem B11234375 : Blo 2217435 11234375 := bstep (se 1 (by rfl) ⟨8425781, by rfl⟩ : syracuseStep 11234375 = 16851563) B16851563
theorem B7489583 : Blo 2217435 7489583 := bstep (se 1 (by rfl) ⟨5617187, by rfl⟩ : syracuseStep 7489583 = 11234375) B11234375
theorem B4993055 : Blo 2217435 4993055 := bstep (se 1 (by rfl) ⟨3744791, by rfl⟩ : syracuseStep 4993055 = 7489583) B7489583
theorem B3328703 : Blo 2217435 3328703 := bstep (se 1 (by rfl) ⟨2496527, by rfl⟩ : syracuseStep 3328703 = 4993055) B4993055
theorem B2219135 : Blo 2217435 2219135 := bstep (se 1 (by rfl) ⟨1664351, by rfl⟩ : syracuseStep 2219135 = 3328703) B3328703
theorem B3328709 : Blo 2217435 3328709 := bbase (se 4 (by rfl) ⟨312066, by rfl⟩ : syracuseStep 3328709 = 624133) (by norm_num)
theorem B2219139 : Blo 2217435 2219139 := bstep (se 1 (by rfl) ⟨1664354, by rfl⟩ : syracuseStep 2219139 = 3328709) B3328709
theorem B3744805 : Blo 2217435 3744805 := bbase (se 4 (by rfl) ⟨351075, by rfl⟩ : syracuseStep 3744805 = 702151) (by norm_num)
theorem B4993073 : Blo 2217435 4993073 := bstep (se 2 (by rfl) ⟨1872402, by rfl⟩ : syracuseStep 4993073 = 3744805) B3744805
theorem B3328715 : Blo 2217435 3328715 := bstep (se 1 (by rfl) ⟨2496536, by rfl⟩ : syracuseStep 3328715 = 4993073) B4993073
theorem B2219143 : Blo 2217435 2219143 := bstep (se 1 (by rfl) ⟨1664357, by rfl⟩ : syracuseStep 2219143 = 3328715) B3328715
theorem B2496541 : Blo 2217435 2496541 := bbase (se 3 (by rfl) ⟨468101, by rfl⟩ : syracuseStep 2496541 = 936203) (by norm_num)
theorem B3328721 : Blo 2217435 3328721 := bstep (se 2 (by rfl) ⟨1248270, by rfl⟩ : syracuseStep 3328721 = 2496541) B2496541
theorem B2219147 : Blo 2217435 2219147 := bstep (se 1 (by rfl) ⟨1664360, by rfl⟩ : syracuseStep 2219147 = 3328721) B3328721
theorem B7489637 : Blo 2217435 7489637 := bbase (se 4 (by rfl) ⟨702153, by rfl⟩ : syracuseStep 7489637 = 1404307) (by norm_num)
theorem B4993091 : Blo 2217435 4993091 := bstep (se 1 (by rfl) ⟨3744818, by rfl⟩ : syracuseStep 4993091 = 7489637) B7489637
theorem B3328727 : Blo 2217435 3328727 := bstep (se 1 (by rfl) ⟨2496545, by rfl⟩ : syracuseStep 3328727 = 4993091) B4993091
theorem B2219151 : Blo 2217435 2219151 := bstep (se 1 (by rfl) ⟨1664363, by rfl⟩ : syracuseStep 2219151 = 3328727) B3328727
theorem B3328733 : Blo 2217435 3328733 := bbase (se 3 (by rfl) ⟨624137, by rfl⟩ : syracuseStep 3328733 = 1248275) (by norm_num)
theorem B2219155 : Blo 2217435 2219155 := bstep (se 1 (by rfl) ⟨1664366, by rfl⟩ : syracuseStep 2219155 = 3328733) B3328733
theorem B4993109 : Blo 2217435 4993109 := bbase (se 8 (by rfl) ⟨29256, by rfl⟩ : syracuseStep 4993109 = 58513) (by norm_num)
theorem B3328739 : Blo 2217435 3328739 := bstep (se 1 (by rfl) ⟨2496554, by rfl⟩ : syracuseStep 3328739 = 4993109) B4993109
theorem B2219159 : Blo 2217435 2219159 := bstep (se 1 (by rfl) ⟨1664369, by rfl⟩ : syracuseStep 2219159 = 3328739) B3328739
theorem B15183733 : Blo 2217435 15183733 := bbase (se 5 (by rfl) ⟨711737, by rfl⟩ : syracuseStep 15183733 = 1423475) (by norm_num)
theorem B20244977 : Blo 2217435 20244977 := bstep (se 2 (by rfl) ⟨7591866, by rfl⟩ : syracuseStep 20244977 = 15183733) B15183733
theorem B13496651 : Blo 2217435 13496651 := bstep (se 1 (by rfl) ⟨10122488, by rfl⟩ : syracuseStep 13496651 = 20244977) B20244977
theorem B8997767 : Blo 2217435 8997767 := bstep (se 1 (by rfl) ⟨6748325, by rfl⟩ : syracuseStep 8997767 = 13496651) B13496651
theorem B5998511 : Blo 2217435 5998511 := bstep (se 1 (by rfl) ⟨4498883, by rfl⟩ : syracuseStep 5998511 = 8997767) B8997767
theorem B3999007 : Blo 2217435 3999007 := bstep (se 1 (by rfl) ⟨2999255, by rfl⟩ : syracuseStep 3999007 = 5998511) B5998511
theorem B5332009 : Blo 2217435 5332009 := bstep (se 2 (by rfl) ⟨1999503, by rfl⟩ : syracuseStep 5332009 = 3999007) B3999007
theorem B7109345 : Blo 2217435 7109345 := bstep (se 2 (by rfl) ⟨2666004, by rfl⟩ : syracuseStep 7109345 = 5332009) B5332009
theorem B4739563 : Blo 2217435 4739563 := bstep (se 1 (by rfl) ⟨3554672, by rfl⟩ : syracuseStep 4739563 = 7109345) B7109345
theorem B6319417 : Blo 2217435 6319417 := bstep (se 2 (by rfl) ⟨2369781, by rfl⟩ : syracuseStep 6319417 = 4739563) B4739563
theorem B8425889 : Blo 2217435 8425889 := bstep (se 2 (by rfl) ⟨3159708, by rfl⟩ : syracuseStep 8425889 = 6319417) B6319417
theorem B5617259 : Blo 2217435 5617259 := bstep (se 1 (by rfl) ⟨4212944, by rfl⟩ : syracuseStep 5617259 = 8425889) B8425889
theorem B3744839 : Blo 2217435 3744839 := bstep (se 1 (by rfl) ⟨2808629, by rfl⟩ : syracuseStep 3744839 = 5617259) B5617259
theorem B2496559 : Blo 2217435 2496559 := bstep (se 1 (by rfl) ⟨1872419, by rfl⟩ : syracuseStep 2496559 = 3744839) B3744839
theorem B3328745 : Blo 2217435 3328745 := bstep (se 2 (by rfl) ⟨1248279, by rfl⟩ : syracuseStep 3328745 = 2496559) B2496559
theorem B2219163 : Blo 2217435 2219163 := bstep (se 1 (by rfl) ⟨1664372, by rfl⟩ : syracuseStep 2219163 = 3328745) B3328745
theorem B3999013 : Blo 2217435 3999013 := bbase (se 4 (by rfl) ⟨374907, by rfl⟩ : syracuseStep 3999013 = 749815) (by norm_num)
theorem B21328069 : Blo 2217435 21328069 := bstep (se 4 (by rfl) ⟨1999506, by rfl⟩ : syracuseStep 21328069 = 3999013) B3999013
theorem B28437425 : Blo 2217435 28437425 := bstep (se 2 (by rfl) ⟨10664034, by rfl⟩ : syracuseStep 28437425 = 21328069) B21328069
theorem B18958283 : Blo 2217435 18958283 := bstep (se 1 (by rfl) ⟨14218712, by rfl⟩ : syracuseStep 18958283 = 28437425) B28437425
theorem B12638855 : Blo 2217435 12638855 := bstep (se 1 (by rfl) ⟨9479141, by rfl⟩ : syracuseStep 12638855 = 18958283) B18958283
theorem B8425903 : Blo 2217435 8425903 := bstep (se 1 (by rfl) ⟨6319427, by rfl⟩ : syracuseStep 8425903 = 12638855) B12638855
theorem B11234537 : Blo 2217435 11234537 := bstep (se 2 (by rfl) ⟨4212951, by rfl⟩ : syracuseStep 11234537 = 8425903) B8425903
theorem B7489691 : Blo 2217435 7489691 := bstep (se 1 (by rfl) ⟨5617268, by rfl⟩ : syracuseStep 7489691 = 11234537) B11234537
theorem B4993127 : Blo 2217435 4993127 := bstep (se 1 (by rfl) ⟨3744845, by rfl⟩ : syracuseStep 4993127 = 7489691) B7489691
theorem B3328751 : Blo 2217435 3328751 := bstep (se 1 (by rfl) ⟨2496563, by rfl⟩ : syracuseStep 3328751 = 4993127) B4993127
theorem B2219167 : Blo 2217435 2219167 := bstep (se 1 (by rfl) ⟨1664375, by rfl⟩ : syracuseStep 2219167 = 3328751) B3328751
theorem B3328757 : Blo 2217435 3328757 := bbase (se 5 (by rfl) ⟨156035, by rfl⟩ : syracuseStep 3328757 = 312071) (by norm_num)
theorem B2219171 : Blo 2217435 2219171 := bstep (se 1 (by rfl) ⟨1664378, by rfl⟩ : syracuseStep 2219171 = 3328757) B3328757
theorem B11387861 : Blo 2217435 11387861 := bbase (se 7 (by rfl) ⟨133451, by rfl⟩ : syracuseStep 11387861 = 266903) (by norm_num)
theorem B7591907 : Blo 2217435 7591907 := bstep (se 1 (by rfl) ⟨5693930, by rfl⟩ : syracuseStep 7591907 = 11387861) B11387861
theorem B5061271 : Blo 2217435 5061271 := bstep (se 1 (by rfl) ⟨3795953, by rfl⟩ : syracuseStep 5061271 = 7591907) B7591907
theorem B6748361 : Blo 2217435 6748361 := bstep (se 2 (by rfl) ⟨2530635, by rfl⟩ : syracuseStep 6748361 = 5061271) B5061271
theorem B4498907 : Blo 2217435 4498907 := bstep (se 1 (by rfl) ⟨3374180, by rfl⟩ : syracuseStep 4498907 = 6748361) B6748361
theorem B11997085 : Blo 2217435 11997085 := bstep (se 3 (by rfl) ⟨2249453, by rfl⟩ : syracuseStep 11997085 = 4498907) B4498907
theorem B15996113 : Blo 2217435 15996113 := bstep (se 2 (by rfl) ⟨5998542, by rfl⟩ : syracuseStep 15996113 = 11997085) B11997085
theorem B10664075 : Blo 2217435 10664075 := bstep (se 1 (by rfl) ⟨7998056, by rfl⟩ : syracuseStep 10664075 = 15996113) B15996113
theorem B7109383 : Blo 2217435 7109383 := bstep (se 1 (by rfl) ⟨5332037, by rfl⟩ : syracuseStep 7109383 = 10664075) B10664075
theorem B9479177 : Blo 2217435 9479177 := bstep (se 2 (by rfl) ⟨3554691, by rfl⟩ : syracuseStep 9479177 = 7109383) B7109383
theorem B6319451 : Blo 2217435 6319451 := bstep (se 1 (by rfl) ⟨4739588, by rfl⟩ : syracuseStep 6319451 = 9479177) B9479177
theorem B4212967 : Blo 2217435 4212967 := bstep (se 1 (by rfl) ⟨3159725, by rfl⟩ : syracuseStep 4212967 = 6319451) B6319451
theorem B5617289 : Blo 2217435 5617289 := bstep (se 2 (by rfl) ⟨2106483, by rfl⟩ : syracuseStep 5617289 = 4212967) B4212967
theorem B3744859 : Blo 2217435 3744859 := bstep (se 1 (by rfl) ⟨2808644, by rfl⟩ : syracuseStep 3744859 = 5617289) B5617289
theorem B4993145 : Blo 2217435 4993145 := bstep (se 2 (by rfl) ⟨1872429, by rfl⟩ : syracuseStep 4993145 = 3744859) B3744859
theorem B3328763 : Blo 2217435 3328763 := bstep (se 1 (by rfl) ⟨2496572, by rfl⟩ : syracuseStep 3328763 = 4993145) B4993145
theorem B2219175 : Blo 2217435 2219175 := bstep (se 1 (by rfl) ⟨1664381, by rfl⟩ : syracuseStep 2219175 = 3328763) B3328763
theorem B2496577 : Blo 2217435 2496577 := bbase (se 2 (by rfl) ⟨936216, by rfl⟩ : syracuseStep 2496577 = 1872433) (by norm_num)
theorem B3328769 : Blo 2217435 3328769 := bstep (se 2 (by rfl) ⟨1248288, by rfl⟩ : syracuseStep 3328769 = 2496577) B2496577
theorem B2219179 : Blo 2217435 2219179 := bstep (se 1 (by rfl) ⟨1664384, by rfl⟩ : syracuseStep 2219179 = 3328769) B3328769
theorem B5617309 : Blo 2217435 5617309 := bbase (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) (by norm_num)
theorem B7489745 : Blo 2217435 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B4993163 : Blo 2217435 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B3328775 : Blo 2217435 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B2219183 : Blo 2217435 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B3328781 : Blo 2217435 3328781 := bbase (se 3 (by rfl) ⟨624146, by rfl⟩ : syracuseStep 3328781 = 1248293) (by norm_num)
theorem B2219187 : Blo 2217435 2219187 := bstep (se 1 (by rfl) ⟨1664390, by rfl⟩ : syracuseStep 2219187 = 3328781) B3328781
theorem B4993181 : Blo 2217435 4993181 := bbase (se 3 (by rfl) ⟨936221, by rfl⟩ : syracuseStep 4993181 = 1872443) (by norm_num)
theorem B3328787 : Blo 2217435 3328787 := bstep (se 1 (by rfl) ⟨2496590, by rfl⟩ : syracuseStep 3328787 = 4993181) B4993181
theorem B2219191 : Blo 2217435 2219191 := bstep (se 1 (by rfl) ⟨1664393, by rfl⟩ : syracuseStep 2219191 = 3328787) B3328787
theorem B3744893 : Blo 2217435 3744893 := bbase (se 3 (by rfl) ⟨702167, by rfl⟩ : syracuseStep 3744893 = 1404335) (by norm_num)
theorem B2496595 : Blo 2217435 2496595 := bstep (se 1 (by rfl) ⟨1872446, by rfl⟩ : syracuseStep 2496595 = 3744893) B3744893
theorem B3328793 : Blo 2217435 3328793 := bstep (se 2 (by rfl) ⟨1248297, by rfl⟩ : syracuseStep 3328793 = 2496595) B2496595
theorem B2219195 : Blo 2217435 2219195 := bstep (se 1 (by rfl) ⟨1664396, by rfl⟩ : syracuseStep 2219195 = 3328793) B3328793
theorem B20245301 : Blo 2217435 20245301 := bbase (se 5 (by rfl) ⟨948998, by rfl⟩ : syracuseStep 20245301 = 1897997) (by norm_num)
theorem B13496867 : Blo 2217435 13496867 := bstep (se 1 (by rfl) ⟨10122650, by rfl⟩ : syracuseStep 13496867 = 20245301) B20245301
theorem B8997911 : Blo 2217435 8997911 := bstep (se 1 (by rfl) ⟨6748433, by rfl⟩ : syracuseStep 8997911 = 13496867) B13496867
theorem B5998607 : Blo 2217435 5998607 := bstep (se 1 (by rfl) ⟨4498955, by rfl⟩ : syracuseStep 5998607 = 8997911) B8997911
theorem B3999071 : Blo 2217435 3999071 := bstep (se 1 (by rfl) ⟨2999303, by rfl⟩ : syracuseStep 3999071 = 5998607) B5998607
theorem B10664189 : Blo 2217435 10664189 := bstep (se 3 (by rfl) ⟨1999535, by rfl⟩ : syracuseStep 10664189 = 3999071) B3999071
theorem B7109459 : Blo 2217435 7109459 := bstep (se 1 (by rfl) ⟨5332094, by rfl⟩ : syracuseStep 7109459 = 10664189) B10664189
theorem B4739639 : Blo 2217435 4739639 := bstep (se 1 (by rfl) ⟨3554729, by rfl⟩ : syracuseStep 4739639 = 7109459) B7109459
theorem B12639037 : Blo 2217435 12639037 := bstep (se 3 (by rfl) ⟨2369819, by rfl⟩ : syracuseStep 12639037 = 4739639) B4739639
theorem B16852049 : Blo 2217435 16852049 := bstep (se 2 (by rfl) ⟨6319518, by rfl⟩ : syracuseStep 16852049 = 12639037) B12639037
theorem B11234699 : Blo 2217435 11234699 := bstep (se 1 (by rfl) ⟨8426024, by rfl⟩ : syracuseStep 11234699 = 16852049) B16852049
theorem B7489799 : Blo 2217435 7489799 := bstep (se 1 (by rfl) ⟨5617349, by rfl⟩ : syracuseStep 7489799 = 11234699) B11234699
theorem B4993199 : Blo 2217435 4993199 := bstep (se 1 (by rfl) ⟨3744899, by rfl⟩ : syracuseStep 4993199 = 7489799) B7489799
theorem B3328799 : Blo 2217435 3328799 := bstep (se 1 (by rfl) ⟨2496599, by rfl⟩ : syracuseStep 3328799 = 4993199) B4993199
theorem B2219199 : Blo 2217435 2219199 := bstep (se 1 (by rfl) ⟨1664399, by rfl⟩ : syracuseStep 2219199 = 3328799) B3328799
theorem B3328805 : Blo 2217435 3328805 := bbase (se 4 (by rfl) ⟨312075, by rfl⟩ : syracuseStep 3328805 = 624151) (by norm_num)
theorem B2219203 : Blo 2217435 2219203 := bstep (se 1 (by rfl) ⟨1664402, by rfl⟩ : syracuseStep 2219203 = 3328805) B3328805
theorem B2808685 : Blo 2217435 2808685 := bbase (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) (by norm_num)
theorem B3744913 : Blo 2217435 3744913 := bstep (se 2 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 3744913 = 2808685) B2808685
theorem B4993217 : Blo 2217435 4993217 := bstep (se 2 (by rfl) ⟨1872456, by rfl⟩ : syracuseStep 4993217 = 3744913) B3744913
theorem B3328811 : Blo 2217435 3328811 := bstep (se 1 (by rfl) ⟨2496608, by rfl⟩ : syracuseStep 3328811 = 4993217) B4993217
theorem B2219207 : Blo 2217435 2219207 := bstep (se 1 (by rfl) ⟨1664405, by rfl⟩ : syracuseStep 2219207 = 3328811) B3328811
theorem B2496613 : Blo 2217435 2496613 := bbase (se 4 (by rfl) ⟨234057, by rfl⟩ : syracuseStep 2496613 = 468115) (by norm_num)
theorem B3328817 : Blo 2217435 3328817 := bstep (se 2 (by rfl) ⟨1248306, by rfl⟩ : syracuseStep 3328817 = 2496613) B2496613
theorem B2219211 : Blo 2217435 2219211 := bstep (se 1 (by rfl) ⟨1664408, by rfl⟩ : syracuseStep 2219211 = 3328817) B3328817
theorem B2369837 : Blo 2217435 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B6319565 : Blo 2217435 6319565 := bstep (se 3 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 6319565 = 2369837) B2369837
theorem B4213043 : Blo 2217435 4213043 := bstep (se 1 (by rfl) ⟨3159782, by rfl⟩ : syracuseStep 4213043 = 6319565) B6319565
theorem B2808695 : Blo 2217435 2808695 := bstep (se 1 (by rfl) ⟨2106521, by rfl⟩ : syracuseStep 2808695 = 4213043) B4213043
theorem B7489853 : Blo 2217435 7489853 := bstep (se 3 (by rfl) ⟨1404347, by rfl⟩ : syracuseStep 7489853 = 2808695) B2808695
theorem B4993235 : Blo 2217435 4993235 := bstep (se 1 (by rfl) ⟨3744926, by rfl⟩ : syracuseStep 4993235 = 7489853) B7489853
theorem B3328823 : Blo 2217435 3328823 := bstep (se 1 (by rfl) ⟨2496617, by rfl⟩ : syracuseStep 3328823 = 4993235) B4993235
theorem B2219215 : Blo 2217435 2219215 := bstep (se 1 (by rfl) ⟨1664411, by rfl⟩ : syracuseStep 2219215 = 3328823) B3328823
theorem B3328829 : Blo 2217435 3328829 := bbase (se 3 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 3328829 = 1248311) (by norm_num)
theorem B2219219 : Blo 2217435 2219219 := bstep (se 1 (by rfl) ⟨1664414, by rfl⟩ : syracuseStep 2219219 = 3328829) B3328829
theorem B4993253 : Blo 2217435 4993253 := bbase (se 4 (by rfl) ⟨468117, by rfl⟩ : syracuseStep 4993253 = 936235) (by norm_num)
theorem B3328835 : Blo 2217435 3328835 := bstep (se 1 (by rfl) ⟨2496626, by rfl⟩ : syracuseStep 3328835 = 4993253) B4993253
theorem B2219223 : Blo 2217435 2219223 := bstep (se 1 (by rfl) ⟨1664417, by rfl⟩ : syracuseStep 2219223 = 3328835) B3328835
theorem B5617421 : Blo 2217435 5617421 := bbase (se 3 (by rfl) ⟨1053266, by rfl⟩ : syracuseStep 5617421 = 2106533) (by norm_num)
theorem B3744947 : Blo 2217435 3744947 := bstep (se 1 (by rfl) ⟨2808710, by rfl⟩ : syracuseStep 3744947 = 5617421) B5617421
theorem B2496631 : Blo 2217435 2496631 := bstep (se 1 (by rfl) ⟨1872473, by rfl⟩ : syracuseStep 2496631 = 3744947) B3744947
theorem B3328841 : Blo 2217435 3328841 := bstep (se 2 (by rfl) ⟨1248315, by rfl⟩ : syracuseStep 3328841 = 2496631) B2496631
theorem B2219227 : Blo 2217435 2219227 := bstep (se 1 (by rfl) ⟨1664420, by rfl⟩ : syracuseStep 2219227 = 3328841) B3328841
theorem B3159805 : Blo 2217435 3159805 := bbase (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) (by norm_num)
theorem B4213073 : Blo 2217435 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B11234861 : Blo 2217435 11234861 := bstep (se 3 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 11234861 = 4213073) B4213073
theorem B7489907 : Blo 2217435 7489907 := bstep (se 1 (by rfl) ⟨5617430, by rfl⟩ : syracuseStep 7489907 = 11234861) B11234861
theorem B4993271 : Blo 2217435 4993271 := bstep (se 1 (by rfl) ⟨3744953, by rfl⟩ : syracuseStep 4993271 = 7489907) B7489907
theorem B3328847 : Blo 2217435 3328847 := bstep (se 1 (by rfl) ⟨2496635, by rfl⟩ : syracuseStep 3328847 = 4993271) B4993271
theorem B2219231 : Blo 2217435 2219231 := bstep (se 1 (by rfl) ⟨1664423, by rfl⟩ : syracuseStep 2219231 = 3328847) B3328847
theorem B3328853 : Blo 2217435 3328853 := bbase (se 9 (by rfl) ⟨9752, by rfl⟩ : syracuseStep 3328853 = 19505) (by norm_num)
theorem B2219235 : Blo 2217435 2219235 := bstep (se 1 (by rfl) ⟨1664426, by rfl⟩ : syracuseStep 2219235 = 3328853) B3328853
theorem B4739725 : Blo 2217435 4739725 := bbase (se 3 (by rfl) ⟨888698, by rfl⟩ : syracuseStep 4739725 = 1777397) (by norm_num)
theorem B6319633 : Blo 2217435 6319633 := bstep (se 2 (by rfl) ⟨2369862, by rfl⟩ : syracuseStep 6319633 = 4739725) B4739725
theorem B8426177 : Blo 2217435 8426177 := bstep (se 2 (by rfl) ⟨3159816, by rfl⟩ : syracuseStep 8426177 = 6319633) B6319633
theorem B5617451 : Blo 2217435 5617451 := bstep (se 1 (by rfl) ⟨4213088, by rfl⟩ : syracuseStep 5617451 = 8426177) B8426177
theorem B3744967 : Blo 2217435 3744967 := bstep (se 1 (by rfl) ⟨2808725, by rfl⟩ : syracuseStep 3744967 = 5617451) B5617451
theorem B4993289 : Blo 2217435 4993289 := bstep (se 2 (by rfl) ⟨1872483, by rfl⟩ : syracuseStep 4993289 = 3744967) B3744967
theorem B3328859 : Blo 2217435 3328859 := bstep (se 1 (by rfl) ⟨2496644, by rfl⟩ : syracuseStep 3328859 = 4993289) B4993289
theorem B2219239 : Blo 2217435 2219239 := bstep (se 1 (by rfl) ⟨1664429, by rfl⟩ : syracuseStep 2219239 = 3328859) B3328859
theorem B2496649 : Blo 2217435 2496649 := bbase (se 2 (by rfl) ⟨936243, by rfl⟩ : syracuseStep 2496649 = 1872487) (by norm_num)
theorem B3328865 : Blo 2217435 3328865 := bstep (se 2 (by rfl) ⟨1248324, by rfl⟩ : syracuseStep 3328865 = 2496649) B2496649
theorem B2219243 : Blo 2217435 2219243 := bstep (se 1 (by rfl) ⟨1664432, by rfl⟩ : syracuseStep 2219243 = 3328865) B3328865
theorem B15996629 : Blo 2217435 15996629 := bbase (se 7 (by rfl) ⟨187460, by rfl⟩ : syracuseStep 15996629 = 374921) (by norm_num)
theorem B42657677 : Blo 2217435 42657677 := bstep (se 3 (by rfl) ⟨7998314, by rfl⟩ : syracuseStep 42657677 = 15996629) B15996629
theorem B28438451 : Blo 2217435 28438451 := bstep (se 1 (by rfl) ⟨21328838, by rfl⟩ : syracuseStep 28438451 = 42657677) B42657677
theorem B18958967 : Blo 2217435 18958967 := bstep (se 1 (by rfl) ⟨14219225, by rfl⟩ : syracuseStep 18958967 = 28438451) B28438451
theorem B12639311 : Blo 2217435 12639311 := bstep (se 1 (by rfl) ⟨9479483, by rfl⟩ : syracuseStep 12639311 = 18958967) B18958967
theorem B8426207 : Blo 2217435 8426207 := bstep (se 1 (by rfl) ⟨6319655, by rfl⟩ : syracuseStep 8426207 = 12639311) B12639311
theorem B5617471 : Blo 2217435 5617471 := bstep (se 1 (by rfl) ⟨4213103, by rfl⟩ : syracuseStep 5617471 = 8426207) B8426207
theorem B7489961 : Blo 2217435 7489961 := bstep (se 2 (by rfl) ⟨2808735, by rfl⟩ : syracuseStep 7489961 = 5617471) B5617471
theorem B4993307 : Blo 2217435 4993307 := bstep (se 1 (by rfl) ⟨3744980, by rfl⟩ : syracuseStep 4993307 = 7489961) B7489961
theorem B3328871 : Blo 2217435 3328871 := bstep (se 1 (by rfl) ⟨2496653, by rfl⟩ : syracuseStep 3328871 = 4993307) B4993307
theorem B2219247 : Blo 2217435 2219247 := bstep (se 1 (by rfl) ⟨1664435, by rfl⟩ : syracuseStep 2219247 = 3328871) B3328871
theorem B3328877 : Blo 2217435 3328877 := bbase (se 3 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 3328877 = 1248329) (by norm_num)
theorem B2219251 : Blo 2217435 2219251 := bstep (se 1 (by rfl) ⟨1664438, by rfl⟩ : syracuseStep 2219251 = 3328877) B3328877
theorem B4993325 : Blo 2217435 4993325 := bbase (se 3 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 4993325 = 1872497) (by norm_num)
theorem B3328883 : Blo 2217435 3328883 := bstep (se 1 (by rfl) ⟨2496662, by rfl⟩ : syracuseStep 3328883 = 4993325) B4993325
theorem B2219255 : Blo 2217435 2219255 := bstep (se 1 (by rfl) ⟨1664441, by rfl⟩ : syracuseStep 2219255 = 3328883) B3328883
theorem B7109653 : Blo 2217435 7109653 := bbase (se 6 (by rfl) ⟨166632, by rfl⟩ : syracuseStep 7109653 = 333265) (by norm_num)
theorem B9479537 : Blo 2217435 9479537 := bstep (se 2 (by rfl) ⟨3554826, by rfl⟩ : syracuseStep 9479537 = 7109653) B7109653
theorem B6319691 : Blo 2217435 6319691 := bstep (se 1 (by rfl) ⟨4739768, by rfl⟩ : syracuseStep 6319691 = 9479537) B9479537
theorem B4213127 : Blo 2217435 4213127 := bstep (se 1 (by rfl) ⟨3159845, by rfl⟩ : syracuseStep 4213127 = 6319691) B6319691
theorem B2808751 : Blo 2217435 2808751 := bstep (se 1 (by rfl) ⟨2106563, by rfl⟩ : syracuseStep 2808751 = 4213127) B4213127
theorem B3745001 : Blo 2217435 3745001 := bstep (se 2 (by rfl) ⟨1404375, by rfl⟩ : syracuseStep 3745001 = 2808751) B2808751
theorem B2496667 : Blo 2217435 2496667 := bstep (se 1 (by rfl) ⟨1872500, by rfl⟩ : syracuseStep 2496667 = 3745001) B3745001
theorem B3328889 : Blo 2217435 3328889 := bstep (se 2 (by rfl) ⟨1248333, by rfl⟩ : syracuseStep 3328889 = 2496667) B2496667
theorem B2219259 : Blo 2217435 2219259 := bstep (se 1 (by rfl) ⟨1664444, by rfl⟩ : syracuseStep 2219259 = 3328889) B3328889
theorem B9608885 : Blo 2217435 9608885 := bbase (se 5 (by rfl) ⟨450416, by rfl⟩ : syracuseStep 9608885 = 900833) (by norm_num)
theorem B6405923 : Blo 2217435 6405923 := bstep (se 1 (by rfl) ⟨4804442, by rfl⟩ : syracuseStep 6405923 = 9608885) B9608885
theorem B17082461 : Blo 2217435 17082461 := bstep (se 3 (by rfl) ⟨3202961, by rfl⟩ : syracuseStep 17082461 = 6405923) B6405923
theorem B45553229 : Blo 2217435 45553229 := bstep (se 3 (by rfl) ⟨8541230, by rfl⟩ : syracuseStep 45553229 = 17082461) B17082461
theorem B30368819 : Blo 2217435 30368819 := bstep (se 1 (by rfl) ⟨22776614, by rfl⟩ : syracuseStep 30368819 = 45553229) B45553229
theorem B20245879 : Blo 2217435 20245879 := bstep (se 1 (by rfl) ⟨15184409, by rfl⟩ : syracuseStep 20245879 = 30368819) B30368819
theorem B107978021 : Blo 2217435 107978021 := bstep (se 4 (by rfl) ⟨10122939, by rfl⟩ : syracuseStep 107978021 = 20245879) B20245879
theorem B71985347 : Blo 2217435 71985347 := bstep (se 1 (by rfl) ⟨53989010, by rfl⟩ : syracuseStep 71985347 = 107978021) B107978021
theorem B47990231 : Blo 2217435 47990231 := bstep (se 1 (by rfl) ⟨35992673, by rfl⟩ : syracuseStep 47990231 = 71985347) B71985347
theorem B31993487 : Blo 2217435 31993487 := bstep (se 1 (by rfl) ⟨23995115, by rfl⟩ : syracuseStep 31993487 = 47990231) B47990231
theorem B21328991 : Blo 2217435 21328991 := bstep (se 1 (by rfl) ⟨15996743, by rfl⟩ : syracuseStep 21328991 = 31993487) B31993487
theorem B14219327 : Blo 2217435 14219327 := bstep (se 1 (by rfl) ⟨10664495, by rfl⟩ : syracuseStep 14219327 = 21328991) B21328991
theorem B37918205 : Blo 2217435 37918205 := bstep (se 3 (by rfl) ⟨7109663, by rfl⟩ : syracuseStep 37918205 = 14219327) B14219327
theorem B25278803 : Blo 2217435 25278803 := bstep (se 1 (by rfl) ⟨18959102, by rfl⟩ : syracuseStep 25278803 = 37918205) B37918205
theorem B16852535 : Blo 2217435 16852535 := bstep (se 1 (by rfl) ⟨12639401, by rfl⟩ : syracuseStep 16852535 = 25278803) B25278803
theorem B11235023 : Blo 2217435 11235023 := bstep (se 1 (by rfl) ⟨8426267, by rfl⟩ : syracuseStep 11235023 = 16852535) B16852535
theorem B7490015 : Blo 2217435 7490015 := bstep (se 1 (by rfl) ⟨5617511, by rfl⟩ : syracuseStep 7490015 = 11235023) B11235023
theorem B4993343 : Blo 2217435 4993343 := bstep (se 1 (by rfl) ⟨3745007, by rfl⟩ : syracuseStep 4993343 = 7490015) B7490015
theorem B3328895 : Blo 2217435 3328895 := bstep (se 1 (by rfl) ⟨2496671, by rfl⟩ : syracuseStep 3328895 = 4993343) B4993343
theorem B2219263 : Blo 2217435 2219263 := bstep (se 1 (by rfl) ⟨1664447, by rfl⟩ : syracuseStep 2219263 = 3328895) B3328895
theorem B3328901 : Blo 2217435 3328901 := bbase (se 4 (by rfl) ⟨312084, by rfl⟩ : syracuseStep 3328901 = 624169) (by norm_num)
theorem B2219267 : Blo 2217435 2219267 := bstep (se 1 (by rfl) ⟨1664450, by rfl⟩ : syracuseStep 2219267 = 3328901) B3328901
theorem B3745021 : Blo 2217435 3745021 := bbase (se 3 (by rfl) ⟨702191, by rfl⟩ : syracuseStep 3745021 = 1404383) (by norm_num)
theorem B4993361 : Blo 2217435 4993361 := bstep (se 2 (by rfl) ⟨1872510, by rfl⟩ : syracuseStep 4993361 = 3745021) B3745021
theorem B3328907 : Blo 2217435 3328907 := bstep (se 1 (by rfl) ⟨2496680, by rfl⟩ : syracuseStep 3328907 = 4993361) B4993361
theorem B2219271 : Blo 2217435 2219271 := bstep (se 1 (by rfl) ⟨1664453, by rfl⟩ : syracuseStep 2219271 = 3328907) B3328907
theorem B2496685 : Blo 2217435 2496685 := bbase (se 3 (by rfl) ⟨468128, by rfl⟩ : syracuseStep 2496685 = 936257) (by norm_num)
theorem B3328913 : Blo 2217435 3328913 := bstep (se 2 (by rfl) ⟨1248342, by rfl⟩ : syracuseStep 3328913 = 2496685) B2496685
theorem B2219275 : Blo 2217435 2219275 := bstep (se 1 (by rfl) ⟨1664456, by rfl⟩ : syracuseStep 2219275 = 3328913) B3328913
theorem B7490069 : Blo 2217435 7490069 := bbase (se 6 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 7490069 = 351097) (by norm_num)
theorem B4993379 : Blo 2217435 4993379 := bstep (se 1 (by rfl) ⟨3745034, by rfl⟩ : syracuseStep 4993379 = 7490069) B7490069
theorem B3328919 : Blo 2217435 3328919 := bstep (se 1 (by rfl) ⟨2496689, by rfl⟩ : syracuseStep 3328919 = 4993379) B4993379
theorem B2219279 : Blo 2217435 2219279 := bstep (se 1 (by rfl) ⟨1664459, by rfl⟩ : syracuseStep 2219279 = 3328919) B3328919
theorem B3328925 : Blo 2217435 3328925 := bbase (se 3 (by rfl) ⟨624173, by rfl⟩ : syracuseStep 3328925 = 1248347) (by norm_num)
theorem B2219283 : Blo 2217435 2219283 := bstep (se 1 (by rfl) ⟨1664462, by rfl⟩ : syracuseStep 2219283 = 3328925) B3328925
theorem B4993397 : Blo 2217435 4993397 := bbase (se 5 (by rfl) ⟨234065, by rfl⟩ : syracuseStep 4993397 = 468131) (by norm_num)
theorem B3328931 : Blo 2217435 3328931 := bstep (se 1 (by rfl) ⟨2496698, by rfl⟩ : syracuseStep 3328931 = 4993397) B4993397
theorem B2219287 : Blo 2217435 2219287 := bstep (se 1 (by rfl) ⟨1664465, by rfl⟩ : syracuseStep 2219287 = 3328931) B3328931
theorem B14219509 : Blo 2217435 14219509 := bbase (se 5 (by rfl) ⟨666539, by rfl⟩ : syracuseStep 14219509 = 1333079) (by norm_num)
theorem B18959345 : Blo 2217435 18959345 := bstep (se 2 (by rfl) ⟨7109754, by rfl⟩ : syracuseStep 18959345 = 14219509) B14219509
theorem B12639563 : Blo 2217435 12639563 := bstep (se 1 (by rfl) ⟨9479672, by rfl⟩ : syracuseStep 12639563 = 18959345) B18959345
theorem B8426375 : Blo 2217435 8426375 := bstep (se 1 (by rfl) ⟨6319781, by rfl⟩ : syracuseStep 8426375 = 12639563) B12639563
theorem B5617583 : Blo 2217435 5617583 := bstep (se 1 (by rfl) ⟨4213187, by rfl⟩ : syracuseStep 5617583 = 8426375) B8426375
theorem B3745055 : Blo 2217435 3745055 := bstep (se 1 (by rfl) ⟨2808791, by rfl⟩ : syracuseStep 3745055 = 5617583) B5617583
theorem B2496703 : Blo 2217435 2496703 := bstep (se 1 (by rfl) ⟨1872527, by rfl⟩ : syracuseStep 2496703 = 3745055) B3745055
theorem B3328937 : Blo 2217435 3328937 := bstep (se 2 (by rfl) ⟨1248351, by rfl⟩ : syracuseStep 3328937 = 2496703) B2496703
theorem B2219291 : Blo 2217435 2219291 := bstep (se 1 (by rfl) ⟨1664468, by rfl⟩ : syracuseStep 2219291 = 3328937) B3328937
theorem B8426389 : Blo 2217435 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B11235185 : Blo 2217435 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B7490123 : Blo 2217435 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B4993415 : Blo 2217435 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B3328943 : Blo 2217435 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B2219295 : Blo 2217435 2219295 := bstep (se 1 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 2219295 = 3328943) B3328943
theorem B3328949 : Blo 2217435 3328949 := bbase (se 5 (by rfl) ⟨156044, by rfl⟩ : syracuseStep 3328949 = 312089) (by norm_num)
theorem B2219299 : Blo 2217435 2219299 := bstep (se 1 (by rfl) ⟨1664474, by rfl⟩ : syracuseStep 2219299 = 3328949) B3328949
theorem B5617613 : Blo 2217435 5617613 := bbase (se 3 (by rfl) ⟨1053302, by rfl⟩ : syracuseStep 5617613 = 2106605) (by norm_num)
theorem B3745075 : Blo 2217435 3745075 := bstep (se 1 (by rfl) ⟨2808806, by rfl⟩ : syracuseStep 3745075 = 5617613) B5617613
theorem B4993433 : Blo 2217435 4993433 := bstep (se 2 (by rfl) ⟨1872537, by rfl⟩ : syracuseStep 4993433 = 3745075) B3745075
theorem B3328955 : Blo 2217435 3328955 := bstep (se 1 (by rfl) ⟨2496716, by rfl⟩ : syracuseStep 3328955 = 4993433) B4993433
theorem B2219303 : Blo 2217435 2219303 := bstep (se 1 (by rfl) ⟨1664477, by rfl⟩ : syracuseStep 2219303 = 3328955) B3328955
theorem B2496721 : Blo 2217435 2496721 := bbase (se 2 (by rfl) ⟨936270, by rfl⟩ : syracuseStep 2496721 = 1872541) (by norm_num)
theorem B3328961 : Blo 2217435 3328961 := bstep (se 2 (by rfl) ⟨1248360, by rfl⟩ : syracuseStep 3328961 = 2496721) B2496721
theorem B2219307 : Blo 2217435 2219307 := bstep (se 1 (by rfl) ⟨1664480, by rfl⟩ : syracuseStep 2219307 = 3328961) B3328961
theorem B11412373 : Blo 2217435 11412373 := bbase (se 6 (by rfl) ⟨267477, by rfl⟩ : syracuseStep 11412373 = 534955) (by norm_num)
theorem B15216497 : Blo 2217435 15216497 := bstep (se 2 (by rfl) ⟨5706186, by rfl⟩ : syracuseStep 15216497 = 11412373) B11412373
theorem B10144331 : Blo 2217435 10144331 := bstep (se 1 (by rfl) ⟨7608248, by rfl⟩ : syracuseStep 10144331 = 15216497) B15216497
theorem B432824789 : Blo 2217435 432824789 := bstep (se 7 (by rfl) ⟨5072165, by rfl⟩ : syracuseStep 432824789 = 10144331) B10144331
theorem B288549859 : Blo 2217435 288549859 := bstep (se 1 (by rfl) ⟨216412394, by rfl⟩ : syracuseStep 288549859 = 432824789) B432824789
theorem B384733145 : Blo 2217435 384733145 := bstep (se 2 (by rfl) ⟨144274929, by rfl⟩ : syracuseStep 384733145 = 288549859) B288549859
theorem B256488763 : Blo 2217435 256488763 := bstep (se 1 (by rfl) ⟨192366572, by rfl⟩ : syracuseStep 256488763 = 384733145) B384733145
theorem B341985017 : Blo 2217435 341985017 := bstep (se 2 (by rfl) ⟨128244381, by rfl⟩ : syracuseStep 341985017 = 256488763) B256488763
theorem B227990011 : Blo 2217435 227990011 := bstep (se 1 (by rfl) ⟨170992508, by rfl⟩ : syracuseStep 227990011 = 341985017) B341985017
theorem B303986681 : Blo 2217435 303986681 := bstep (se 2 (by rfl) ⟨113995005, by rfl⟩ : syracuseStep 303986681 = 227990011) B227990011
theorem B202657787 : Blo 2217435 202657787 := bstep (se 1 (by rfl) ⟨151993340, by rfl⟩ : syracuseStep 202657787 = 303986681) B303986681
theorem B135105191 : Blo 2217435 135105191 := bstep (se 1 (by rfl) ⟨101328893, by rfl⟩ : syracuseStep 135105191 = 202657787) B202657787
theorem B90070127 : Blo 2217435 90070127 := bstep (se 1 (by rfl) ⟨67552595, by rfl⟩ : syracuseStep 90070127 = 135105191) B135105191
theorem B60046751 : Blo 2217435 60046751 := bstep (se 1 (by rfl) ⟨45035063, by rfl⟩ : syracuseStep 60046751 = 90070127) B90070127
theorem B40031167 : Blo 2217435 40031167 := bstep (se 1 (by rfl) ⟨30023375, by rfl⟩ : syracuseStep 40031167 = 60046751) B60046751
theorem B53374889 : Blo 2217435 53374889 := bstep (se 2 (by rfl) ⟨20015583, by rfl⟩ : syracuseStep 53374889 = 40031167) B40031167
theorem B142333037 : Blo 2217435 142333037 := bstep (se 3 (by rfl) ⟨26687444, by rfl⟩ : syracuseStep 142333037 = 53374889) B53374889
theorem B94888691 : Blo 2217435 94888691 := bstep (se 1 (by rfl) ⟨71166518, by rfl⟩ : syracuseStep 94888691 = 142333037) B142333037
theorem B63259127 : Blo 2217435 63259127 := bstep (se 1 (by rfl) ⟨47444345, by rfl⟩ : syracuseStep 63259127 = 94888691) B94888691
theorem B42172751 : Blo 2217435 42172751 := bstep (se 1 (by rfl) ⟨31629563, by rfl⟩ : syracuseStep 42172751 = 63259127) B63259127
theorem B28115167 : Blo 2217435 28115167 := bstep (se 1 (by rfl) ⟨21086375, by rfl⟩ : syracuseStep 28115167 = 42172751) B42172751
theorem B37486889 : Blo 2217435 37486889 := bstep (se 2 (by rfl) ⟨14057583, by rfl⟩ : syracuseStep 37486889 = 28115167) B28115167
theorem B24991259 : Blo 2217435 24991259 := bstep (se 1 (by rfl) ⟨18743444, by rfl⟩ : syracuseStep 24991259 = 37486889) B37486889
theorem B66643357 : Blo 2217435 66643357 := bstep (se 3 (by rfl) ⟨12495629, by rfl⟩ : syracuseStep 66643357 = 24991259) B24991259
theorem B88857809 : Blo 2217435 88857809 := bstep (se 2 (by rfl) ⟨33321678, by rfl⟩ : syracuseStep 88857809 = 66643357) B66643357
theorem B59238539 : Blo 2217435 59238539 := bstep (se 1 (by rfl) ⟨44428904, by rfl⟩ : syracuseStep 59238539 = 88857809) B88857809
theorem B39492359 : Blo 2217435 39492359 := bstep (se 1 (by rfl) ⟨29619269, by rfl⟩ : syracuseStep 39492359 = 59238539) B59238539
theorem B26328239 : Blo 2217435 26328239 := bstep (se 1 (by rfl) ⟨19746179, by rfl⟩ : syracuseStep 26328239 = 39492359) B39492359
theorem B17552159 : Blo 2217435 17552159 := bstep (se 1 (by rfl) ⟨13164119, by rfl⟩ : syracuseStep 17552159 = 26328239) B26328239
theorem B11701439 : Blo 2217435 11701439 := bstep (se 1 (by rfl) ⟨8776079, by rfl⟩ : syracuseStep 11701439 = 17552159) B17552159
theorem B7800959 : Blo 2217435 7800959 := bstep (se 1 (by rfl) ⟨5850719, by rfl⟩ : syracuseStep 7800959 = 11701439) B11701439
theorem B20802557 : Blo 2217435 20802557 := bstep (se 3 (by rfl) ⟨3900479, by rfl⟩ : syracuseStep 20802557 = 7800959) B7800959
theorem B13868371 : Blo 2217435 13868371 := bstep (se 1 (by rfl) ⟨10401278, by rfl⟩ : syracuseStep 13868371 = 20802557) B20802557
theorem B18491161 : Blo 2217435 18491161 := bstep (se 2 (by rfl) ⟨6934185, by rfl⟩ : syracuseStep 18491161 = 13868371) B13868371
theorem B24654881 : Blo 2217435 24654881 := bstep (se 2 (by rfl) ⟨9245580, by rfl⟩ : syracuseStep 24654881 = 18491161) B18491161
theorem B16436587 : Blo 2217435 16436587 := bstep (se 1 (by rfl) ⟨12327440, by rfl⟩ : syracuseStep 16436587 = 24654881) B24654881
theorem B21915449 : Blo 2217435 21915449 := bstep (se 2 (by rfl) ⟨8218293, by rfl⟩ : syracuseStep 21915449 = 16436587) B16436587
theorem B14610299 : Blo 2217435 14610299 := bstep (se 1 (by rfl) ⟨10957724, by rfl⟩ : syracuseStep 14610299 = 21915449) B21915449
theorem B38960797 : Blo 2217435 38960797 := bstep (se 3 (by rfl) ⟨7305149, by rfl⟩ : syracuseStep 38960797 = 14610299) B14610299
theorem B51947729 : Blo 2217435 51947729 := bstep (se 2 (by rfl) ⟨19480398, by rfl⟩ : syracuseStep 51947729 = 38960797) B38960797
theorem B34631819 : Blo 2217435 34631819 := bstep (se 1 (by rfl) ⟨25973864, by rfl⟩ : syracuseStep 34631819 = 51947729) B51947729
theorem B23087879 : Blo 2217435 23087879 := bstep (se 1 (by rfl) ⟨17315909, by rfl⟩ : syracuseStep 23087879 = 34631819) B34631819
theorem B15391919 : Blo 2217435 15391919 := bstep (se 1 (by rfl) ⟨11543939, by rfl⟩ : syracuseStep 15391919 = 23087879) B23087879
theorem B10261279 : Blo 2217435 10261279 := bstep (se 1 (by rfl) ⟨7695959, by rfl⟩ : syracuseStep 10261279 = 15391919) B15391919
theorem B13681705 : Blo 2217435 13681705 := bstep (se 2 (by rfl) ⟨5130639, by rfl⟩ : syracuseStep 13681705 = 10261279) B10261279
theorem B18242273 : Blo 2217435 18242273 := bstep (se 2 (by rfl) ⟨6840852, by rfl⟩ : syracuseStep 18242273 = 13681705) B13681705
theorem B12161515 : Blo 2217435 12161515 := bstep (se 1 (by rfl) ⟨9121136, by rfl⟩ : syracuseStep 12161515 = 18242273) B18242273
theorem B16215353 : Blo 2217435 16215353 := bstep (se 2 (by rfl) ⟨6080757, by rfl⟩ : syracuseStep 16215353 = 12161515) B12161515
theorem B10810235 : Blo 2217435 10810235 := bstep (se 1 (by rfl) ⟨8107676, by rfl⟩ : syracuseStep 10810235 = 16215353) B16215353
theorem B7206823 : Blo 2217435 7206823 := bstep (se 1 (by rfl) ⟨5405117, by rfl⟩ : syracuseStep 7206823 = 10810235) B10810235
theorem B38436389 : Blo 2217435 38436389 := bstep (se 4 (by rfl) ⟨3603411, by rfl⟩ : syracuseStep 38436389 = 7206823) B7206823
theorem B25624259 : Blo 2217435 25624259 := bstep (se 1 (by rfl) ⟨19218194, by rfl⟩ : syracuseStep 25624259 = 38436389) B38436389
theorem B17082839 : Blo 2217435 17082839 := bstep (se 1 (by rfl) ⟨12812129, by rfl⟩ : syracuseStep 17082839 = 25624259) B25624259
theorem B11388559 : Blo 2217435 11388559 := bstep (se 1 (by rfl) ⟨8541419, by rfl⟩ : syracuseStep 11388559 = 17082839) B17082839
theorem B15184745 : Blo 2217435 15184745 := bstep (se 2 (by rfl) ⟨5694279, by rfl⟩ : syracuseStep 15184745 = 11388559) B11388559
theorem B10123163 : Blo 2217435 10123163 := bstep (se 1 (by rfl) ⟨7592372, by rfl⟩ : syracuseStep 10123163 = 15184745) B15184745
theorem B6748775 : Blo 2217435 6748775 := bstep (se 1 (by rfl) ⟨5061581, by rfl⟩ : syracuseStep 6748775 = 10123163) B10123163
theorem B4499183 : Blo 2217435 4499183 := bstep (se 1 (by rfl) ⟨3374387, by rfl⟩ : syracuseStep 4499183 = 6748775) B6748775
theorem B11997821 : Blo 2217435 11997821 := bstep (se 3 (by rfl) ⟨2249591, by rfl⟩ : syracuseStep 11997821 = 4499183) B4499183
theorem B7998547 : Blo 2217435 7998547 := bstep (se 1 (by rfl) ⟨5998910, by rfl⟩ : syracuseStep 7998547 = 11997821) B11997821
theorem B10664729 : Blo 2217435 10664729 := bstep (se 2 (by rfl) ⟨3999273, by rfl⟩ : syracuseStep 10664729 = 7998547) B7998547
theorem B7109819 : Blo 2217435 7109819 := bstep (se 1 (by rfl) ⟨5332364, by rfl⟩ : syracuseStep 7109819 = 10664729) B10664729
theorem B4739879 : Blo 2217435 4739879 := bstep (se 1 (by rfl) ⟨3554909, by rfl⟩ : syracuseStep 4739879 = 7109819) B7109819
theorem B3159919 : Blo 2217435 3159919 := bstep (se 1 (by rfl) ⟨2369939, by rfl⟩ : syracuseStep 3159919 = 4739879) B4739879
theorem B4213225 : Blo 2217435 4213225 := bstep (se 2 (by rfl) ⟨1579959, by rfl⟩ : syracuseStep 4213225 = 3159919) B3159919
theorem B5617633 : Blo 2217435 5617633 := bstep (se 2 (by rfl) ⟨2106612, by rfl⟩ : syracuseStep 5617633 = 4213225) B4213225
theorem B7490177 : Blo 2217435 7490177 := bstep (se 2 (by rfl) ⟨2808816, by rfl⟩ : syracuseStep 7490177 = 5617633) B5617633
theorem B4993451 : Blo 2217435 4993451 := bstep (se 1 (by rfl) ⟨3745088, by rfl⟩ : syracuseStep 4993451 = 7490177) B7490177
theorem B3328967 : Blo 2217435 3328967 := bstep (se 1 (by rfl) ⟨2496725, by rfl⟩ : syracuseStep 3328967 = 4993451) B4993451
theorem B2219311 : Blo 2217435 2219311 := bstep (se 1 (by rfl) ⟨1664483, by rfl⟩ : syracuseStep 2219311 = 3328967) B3328967
theorem B3328973 : Blo 2217435 3328973 := bbase (se 3 (by rfl) ⟨624182, by rfl⟩ : syracuseStep 3328973 = 1248365) (by norm_num)
theorem B2219315 : Blo 2217435 2219315 := bstep (se 1 (by rfl) ⟨1664486, by rfl⟩ : syracuseStep 2219315 = 3328973) B3328973
theorem B4993469 : Blo 2217435 4993469 := bbase (se 3 (by rfl) ⟨936275, by rfl⟩ : syracuseStep 4993469 = 1872551) (by norm_num)
theorem B3328979 : Blo 2217435 3328979 := bstep (se 1 (by rfl) ⟨2496734, by rfl⟩ : syracuseStep 3328979 = 4993469) B4993469
theorem B2219319 : Blo 2217435 2219319 := bstep (se 1 (by rfl) ⟨1664489, by rfl⟩ : syracuseStep 2219319 = 3328979) B3328979
theorem B3745109 : Blo 2217435 3745109 := bbase (se 12 (by rfl) ⟨1371, by rfl⟩ : syracuseStep 3745109 = 2743) (by norm_num)
theorem B2496739 : Blo 2217435 2496739 := bstep (se 1 (by rfl) ⟨1872554, by rfl⟩ : syracuseStep 2496739 = 3745109) B3745109
theorem B3328985 : Blo 2217435 3328985 := bstep (se 2 (by rfl) ⟨1248369, by rfl⟩ : syracuseStep 3328985 = 2496739) B2496739
theorem B2219323 : Blo 2217435 2219323 := bstep (se 1 (by rfl) ⟨1664492, by rfl⟩ : syracuseStep 2219323 = 3328985) B3328985
theorem B2666201 : Blo 2217435 2666201 := bbase (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) (by norm_num)
theorem B7109869 : Blo 2217435 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B9479825 : Blo 2217435 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B6319883 : Blo 2217435 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B16853021 : Blo 2217435 16853021 := bstep (se 3 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 16853021 = 6319883) B6319883
theorem B11235347 : Blo 2217435 11235347 := bstep (se 1 (by rfl) ⟨8426510, by rfl⟩ : syracuseStep 11235347 = 16853021) B16853021
theorem B7490231 : Blo 2217435 7490231 := bstep (se 1 (by rfl) ⟨5617673, by rfl⟩ : syracuseStep 7490231 = 11235347) B11235347
theorem B4993487 : Blo 2217435 4993487 := bstep (se 1 (by rfl) ⟨3745115, by rfl⟩ : syracuseStep 4993487 = 7490231) B7490231
theorem B3328991 : Blo 2217435 3328991 := bstep (se 1 (by rfl) ⟨2496743, by rfl⟩ : syracuseStep 3328991 = 4993487) B4993487
theorem B2219327 : Blo 2217435 2219327 := bstep (se 1 (by rfl) ⟨1664495, by rfl⟩ : syracuseStep 2219327 = 3328991) B3328991
theorem B3328997 : Blo 2217435 3328997 := bbase (se 4 (by rfl) ⟨312093, by rfl⟩ : syracuseStep 3328997 = 624187) (by norm_num)
theorem B2219331 : Blo 2217435 2219331 := bstep (se 1 (by rfl) ⟨1664498, by rfl⟩ : syracuseStep 2219331 = 3328997) B3328997
theorem B9479861 : Blo 2217435 9479861 := bbase (se 5 (by rfl) ⟨444368, by rfl⟩ : syracuseStep 9479861 = 888737) (by norm_num)
theorem B6319907 : Blo 2217435 6319907 := bstep (se 1 (by rfl) ⟨4739930, by rfl⟩ : syracuseStep 6319907 = 9479861) B9479861
theorem B4213271 : Blo 2217435 4213271 := bstep (se 1 (by rfl) ⟨3159953, by rfl⟩ : syracuseStep 4213271 = 6319907) B6319907
theorem B2808847 : Blo 2217435 2808847 := bstep (se 1 (by rfl) ⟨2106635, by rfl⟩ : syracuseStep 2808847 = 4213271) B4213271
theorem B3745129 : Blo 2217435 3745129 := bstep (se 2 (by rfl) ⟨1404423, by rfl⟩ : syracuseStep 3745129 = 2808847) B2808847
theorem B4993505 : Blo 2217435 4993505 := bstep (se 2 (by rfl) ⟨1872564, by rfl⟩ : syracuseStep 4993505 = 3745129) B3745129
theorem B3329003 : Blo 2217435 3329003 := bstep (se 1 (by rfl) ⟨2496752, by rfl⟩ : syracuseStep 3329003 = 4993505) B4993505
theorem B2219335 : Blo 2217435 2219335 := bstep (se 1 (by rfl) ⟨1664501, by rfl⟩ : syracuseStep 2219335 = 3329003) B3329003
theorem B2496757 : Blo 2217435 2496757 := bbase (se 5 (by rfl) ⟨117035, by rfl⟩ : syracuseStep 2496757 = 234071) (by norm_num)
theorem B3329009 : Blo 2217435 3329009 := bstep (se 2 (by rfl) ⟨1248378, by rfl⟩ : syracuseStep 3329009 = 2496757) B2496757
theorem B2219339 : Blo 2217435 2219339 := bstep (se 1 (by rfl) ⟨1664504, by rfl⟩ : syracuseStep 2219339 = 3329009) B3329009
theorem B2808857 : Blo 2217435 2808857 := bbase (se 2 (by rfl) ⟨1053321, by rfl⟩ : syracuseStep 2808857 = 2106643) (by norm_num)
theorem B7490285 : Blo 2217435 7490285 := bstep (se 3 (by rfl) ⟨1404428, by rfl⟩ : syracuseStep 7490285 = 2808857) B2808857
theorem B4993523 : Blo 2217435 4993523 := bstep (se 1 (by rfl) ⟨3745142, by rfl⟩ : syracuseStep 4993523 = 7490285) B7490285
theorem B3329015 : Blo 2217435 3329015 := bstep (se 1 (by rfl) ⟨2496761, by rfl⟩ : syracuseStep 3329015 = 4993523) B4993523
theorem B2219343 : Blo 2217435 2219343 := bstep (se 1 (by rfl) ⟨1664507, by rfl⟩ : syracuseStep 2219343 = 3329015) B3329015
theorem B3329021 : Blo 2217435 3329021 := bbase (se 3 (by rfl) ⟨624191, by rfl⟩ : syracuseStep 3329021 = 1248383) (by norm_num)
theorem B2219347 : Blo 2217435 2219347 := bstep (se 1 (by rfl) ⟨1664510, by rfl⟩ : syracuseStep 2219347 = 3329021) B3329021
theorem B4993541 : Blo 2217435 4993541 := bbase (se 4 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 4993541 = 936289) (by norm_num)
theorem B3329027 : Blo 2217435 3329027 := bstep (se 1 (by rfl) ⟨2496770, by rfl⟩ : syracuseStep 3329027 = 4993541) B4993541
theorem B2219351 : Blo 2217435 2219351 := bstep (se 1 (by rfl) ⟨1664513, by rfl⟩ : syracuseStep 2219351 = 3329027) B3329027
theorem B4213309 : Blo 2217435 4213309 := bbase (se 3 (by rfl) ⟨789995, by rfl⟩ : syracuseStep 4213309 = 1579991) (by norm_num)
theorem B5617745 : Blo 2217435 5617745 := bstep (se 2 (by rfl) ⟨2106654, by rfl⟩ : syracuseStep 5617745 = 4213309) B4213309
theorem B3745163 : Blo 2217435 3745163 := bstep (se 1 (by rfl) ⟨2808872, by rfl⟩ : syracuseStep 3745163 = 5617745) B5617745
theorem B2496775 : Blo 2217435 2496775 := bstep (se 1 (by rfl) ⟨1872581, by rfl⟩ : syracuseStep 2496775 = 3745163) B3745163
theorem B3329033 : Blo 2217435 3329033 := bstep (se 2 (by rfl) ⟨1248387, by rfl⟩ : syracuseStep 3329033 = 2496775) B2496775
theorem B2219355 : Blo 2217435 2219355 := bstep (se 1 (by rfl) ⟨1664516, by rfl⟩ : syracuseStep 2219355 = 3329033) B3329033
theorem B11235509 : Blo 2217435 11235509 := bbase (se 5 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 11235509 = 1053329) (by norm_num)
theorem B7490339 : Blo 2217435 7490339 := bstep (se 1 (by rfl) ⟨5617754, by rfl⟩ : syracuseStep 7490339 = 11235509) B11235509
theorem B4993559 : Blo 2217435 4993559 := bstep (se 1 (by rfl) ⟨3745169, by rfl⟩ : syracuseStep 4993559 = 7490339) B7490339
theorem B3329039 : Blo 2217435 3329039 := bstep (se 1 (by rfl) ⟨2496779, by rfl⟩ : syracuseStep 3329039 = 4993559) B4993559
theorem B2219359 : Blo 2217435 2219359 := bstep (se 1 (by rfl) ⟨1664519, by rfl⟩ : syracuseStep 2219359 = 3329039) B3329039
theorem B3329045 : Blo 2217435 3329045 := bbase (se 6 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 3329045 = 156049) (by norm_num)
theorem B2219363 : Blo 2217435 2219363 := bstep (se 1 (by rfl) ⟨1664522, by rfl⟩ : syracuseStep 2219363 = 3329045) B3329045
theorem B17316341 : Blo 2217435 17316341 := bbase (se 5 (by rfl) ⟨811703, by rfl⟩ : syracuseStep 17316341 = 1623407) (by norm_num)
theorem B11544227 : Blo 2217435 11544227 := bstep (se 1 (by rfl) ⟨8658170, by rfl⟩ : syracuseStep 11544227 = 17316341) B17316341
theorem B7696151 : Blo 2217435 7696151 := bstep (se 1 (by rfl) ⟨5772113, by rfl⟩ : syracuseStep 7696151 = 11544227) B11544227
theorem B5130767 : Blo 2217435 5130767 := bstep (se 1 (by rfl) ⟨3848075, by rfl⟩ : syracuseStep 5130767 = 7696151) B7696151
theorem B3420511 : Blo 2217435 3420511 := bstep (se 1 (by rfl) ⟨2565383, by rfl⟩ : syracuseStep 3420511 = 5130767) B5130767
theorem B72970901 : Blo 2217435 72970901 := bstep (se 6 (by rfl) ⟨1710255, by rfl⟩ : syracuseStep 72970901 = 3420511) B3420511
theorem B48647267 : Blo 2217435 48647267 := bstep (se 1 (by rfl) ⟨36485450, by rfl⟩ : syracuseStep 48647267 = 72970901) B72970901
theorem B32431511 : Blo 2217435 32431511 := bstep (se 1 (by rfl) ⟨24323633, by rfl⟩ : syracuseStep 32431511 = 48647267) B48647267
theorem B21621007 : Blo 2217435 21621007 := bstep (se 1 (by rfl) ⟨16215755, by rfl⟩ : syracuseStep 21621007 = 32431511) B32431511
theorem B28828009 : Blo 2217435 28828009 := bstep (se 2 (by rfl) ⟨10810503, by rfl⟩ : syracuseStep 28828009 = 21621007) B21621007
theorem B38437345 : Blo 2217435 38437345 := bstep (se 2 (by rfl) ⟨14414004, by rfl⟩ : syracuseStep 38437345 = 28828009) B28828009
theorem B51249793 : Blo 2217435 51249793 := bstep (se 2 (by rfl) ⟨19218672, by rfl⟩ : syracuseStep 51249793 = 38437345) B38437345
theorem B68333057 : Blo 2217435 68333057 := bstep (se 2 (by rfl) ⟨25624896, by rfl⟩ : syracuseStep 68333057 = 51249793) B51249793
theorem B45555371 : Blo 2217435 45555371 := bstep (se 1 (by rfl) ⟨34166528, by rfl⟩ : syracuseStep 45555371 = 68333057) B68333057
theorem B30370247 : Blo 2217435 30370247 := bstep (se 1 (by rfl) ⟨22777685, by rfl⟩ : syracuseStep 30370247 = 45555371) B45555371
theorem B20246831 : Blo 2217435 20246831 := bstep (se 1 (by rfl) ⟨15185123, by rfl⟩ : syracuseStep 20246831 = 30370247) B30370247
theorem B13497887 : Blo 2217435 13497887 := bstep (se 1 (by rfl) ⟨10123415, by rfl⟩ : syracuseStep 13497887 = 20246831) B20246831
theorem B35994365 : Blo 2217435 35994365 := bstep (se 3 (by rfl) ⟨6748943, by rfl⟩ : syracuseStep 35994365 = 13497887) B13497887
theorem B23996243 : Blo 2217435 23996243 := bstep (se 1 (by rfl) ⟨17997182, by rfl⟩ : syracuseStep 23996243 = 35994365) B35994365
theorem B15997495 : Blo 2217435 15997495 := bstep (se 1 (by rfl) ⟨11998121, by rfl⟩ : syracuseStep 15997495 = 23996243) B23996243
theorem B21329993 : Blo 2217435 21329993 := bstep (se 2 (by rfl) ⟨7998747, by rfl⟩ : syracuseStep 21329993 = 15997495) B15997495
theorem B14219995 : Blo 2217435 14219995 := bstep (se 1 (by rfl) ⟨10664996, by rfl⟩ : syracuseStep 14219995 = 21329993) B21329993
theorem B18959993 : Blo 2217435 18959993 := bstep (se 2 (by rfl) ⟨7109997, by rfl⟩ : syracuseStep 18959993 = 14219995) B14219995
theorem B12639995 : Blo 2217435 12639995 := bstep (se 1 (by rfl) ⟨9479996, by rfl⟩ : syracuseStep 12639995 = 18959993) B18959993
theorem B8426663 : Blo 2217435 8426663 := bstep (se 1 (by rfl) ⟨6319997, by rfl⟩ : syracuseStep 8426663 = 12639995) B12639995
theorem B5617775 : Blo 2217435 5617775 := bstep (se 1 (by rfl) ⟨4213331, by rfl⟩ : syracuseStep 5617775 = 8426663) B8426663
theorem B3745183 : Blo 2217435 3745183 := bstep (se 1 (by rfl) ⟨2808887, by rfl⟩ : syracuseStep 3745183 = 5617775) B5617775
theorem B4993577 : Blo 2217435 4993577 := bstep (se 2 (by rfl) ⟨1872591, by rfl⟩ : syracuseStep 4993577 = 3745183) B3745183
theorem B3329051 : Blo 2217435 3329051 := bstep (se 1 (by rfl) ⟨2496788, by rfl⟩ : syracuseStep 3329051 = 4993577) B4993577
theorem B2219367 : Blo 2217435 2219367 := bstep (se 1 (by rfl) ⟨1664525, by rfl⟩ : syracuseStep 2219367 = 3329051) B3329051
theorem B2496793 : Blo 2217435 2496793 := bbase (se 2 (by rfl) ⟨936297, by rfl⟩ : syracuseStep 2496793 = 1872595) (by norm_num)
theorem B3329057 : Blo 2217435 3329057 := bstep (se 2 (by rfl) ⟨1248396, by rfl⟩ : syracuseStep 3329057 = 2496793) B2496793
theorem B2219371 : Blo 2217435 2219371 := bstep (se 1 (by rfl) ⟨1664528, by rfl⟩ : syracuseStep 2219371 = 3329057) B3329057
theorem B8426693 : Blo 2217435 8426693 := bbase (se 4 (by rfl) ⟨790002, by rfl⟩ : syracuseStep 8426693 = 1580005) (by norm_num)
theorem B5617795 : Blo 2217435 5617795 := bstep (se 1 (by rfl) ⟨4213346, by rfl⟩ : syracuseStep 5617795 = 8426693) B8426693
theorem B7490393 : Blo 2217435 7490393 := bstep (se 2 (by rfl) ⟨2808897, by rfl⟩ : syracuseStep 7490393 = 5617795) B5617795
theorem B4993595 : Blo 2217435 4993595 := bstep (se 1 (by rfl) ⟨3745196, by rfl⟩ : syracuseStep 4993595 = 7490393) B7490393
theorem B3329063 : Blo 2217435 3329063 := bstep (se 1 (by rfl) ⟨2496797, by rfl⟩ : syracuseStep 3329063 = 4993595) B4993595
theorem B2219375 : Blo 2217435 2219375 := bstep (se 1 (by rfl) ⟨1664531, by rfl⟩ : syracuseStep 2219375 = 3329063) B3329063
theorem B3329069 : Blo 2217435 3329069 := bbase (se 3 (by rfl) ⟨624200, by rfl⟩ : syracuseStep 3329069 = 1248401) (by norm_num)
theorem B2219379 : Blo 2217435 2219379 := bstep (se 1 (by rfl) ⟨1664534, by rfl⟩ : syracuseStep 2219379 = 3329069) B3329069
theorem B4993613 : Blo 2217435 4993613 := bbase (se 3 (by rfl) ⟨936302, by rfl⟩ : syracuseStep 4993613 = 1872605) (by norm_num)
theorem B3329075 : Blo 2217435 3329075 := bstep (se 1 (by rfl) ⟨2496806, by rfl⟩ : syracuseStep 3329075 = 4993613) B4993613
theorem B2219383 : Blo 2217435 2219383 := bstep (se 1 (by rfl) ⟨1664537, by rfl⟩ : syracuseStep 2219383 = 3329075) B3329075
theorem B2808913 : Blo 2217435 2808913 := bbase (se 2 (by rfl) ⟨1053342, by rfl⟩ : syracuseStep 2808913 = 2106685) (by norm_num)
theorem B3745217 : Blo 2217435 3745217 := bstep (se 2 (by rfl) ⟨1404456, by rfl⟩ : syracuseStep 3745217 = 2808913) B2808913
theorem B2496811 : Blo 2217435 2496811 := bstep (se 1 (by rfl) ⟨1872608, by rfl⟩ : syracuseStep 2496811 = 3745217) B3745217
theorem B3329081 : Blo 2217435 3329081 := bstep (se 2 (by rfl) ⟨1248405, by rfl⟩ : syracuseStep 3329081 = 2496811) B2496811
theorem B2219387 : Blo 2217435 2219387 := bstep (se 1 (by rfl) ⟨1664540, by rfl⟩ : syracuseStep 2219387 = 3329081) B3329081
theorem B3555037 : Blo 2217435 3555037 := bbase (se 3 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 3555037 = 1333139) (by norm_num)
theorem B4740049 : Blo 2217435 4740049 := bstep (se 2 (by rfl) ⟨1777518, by rfl⟩ : syracuseStep 4740049 = 3555037) B3555037
theorem B25280261 : Blo 2217435 25280261 := bstep (se 4 (by rfl) ⟨2370024, by rfl⟩ : syracuseStep 25280261 = 4740049) B4740049
theorem B16853507 : Blo 2217435 16853507 := bstep (se 1 (by rfl) ⟨12640130, by rfl⟩ : syracuseStep 16853507 = 25280261) B25280261
theorem B11235671 : Blo 2217435 11235671 := bstep (se 1 (by rfl) ⟨8426753, by rfl⟩ : syracuseStep 11235671 = 16853507) B16853507
theorem B7490447 : Blo 2217435 7490447 := bstep (se 1 (by rfl) ⟨5617835, by rfl⟩ : syracuseStep 7490447 = 11235671) B11235671
theorem B4993631 : Blo 2217435 4993631 := bstep (se 1 (by rfl) ⟨3745223, by rfl⟩ : syracuseStep 4993631 = 7490447) B7490447
theorem B3329087 : Blo 2217435 3329087 := bstep (se 1 (by rfl) ⟨2496815, by rfl⟩ : syracuseStep 3329087 = 4993631) B4993631
theorem B2219391 : Blo 2217435 2219391 := bstep (se 1 (by rfl) ⟨1664543, by rfl⟩ : syracuseStep 2219391 = 3329087) B3329087
theorem B3329093 : Blo 2217435 3329093 := bbase (se 4 (by rfl) ⟨312102, by rfl⟩ : syracuseStep 3329093 = 624205) (by norm_num)
theorem B2219395 : Blo 2217435 2219395 := bstep (se 1 (by rfl) ⟨1664546, by rfl⟩ : syracuseStep 2219395 = 3329093) B3329093
theorem B3745237 : Blo 2217435 3745237 := bbase (se 7 (by rfl) ⟨43889, by rfl⟩ : syracuseStep 3745237 = 87779) (by norm_num)
theorem B4993649 : Blo 2217435 4993649 := bstep (se 2 (by rfl) ⟨1872618, by rfl⟩ : syracuseStep 4993649 = 3745237) B3745237
theorem B3329099 : Blo 2217435 3329099 := bstep (se 1 (by rfl) ⟨2496824, by rfl⟩ : syracuseStep 3329099 = 4993649) B4993649
theorem B2219399 : Blo 2217435 2219399 := bstep (se 1 (by rfl) ⟨1664549, by rfl⟩ : syracuseStep 2219399 = 3329099) B3329099
theorem B2496829 : Blo 2217435 2496829 := bbase (se 3 (by rfl) ⟨468155, by rfl⟩ : syracuseStep 2496829 = 936311) (by norm_num)
theorem B3329105 : Blo 2217435 3329105 := bstep (se 2 (by rfl) ⟨1248414, by rfl⟩ : syracuseStep 3329105 = 2496829) B2496829
theorem B2219403 : Blo 2217435 2219403 := bstep (se 1 (by rfl) ⟨1664552, by rfl⟩ : syracuseStep 2219403 = 3329105) B3329105
theorem B7490501 : Blo 2217435 7490501 := bbase (se 4 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 7490501 = 1404469) (by norm_num)
theorem B4993667 : Blo 2217435 4993667 := bstep (se 1 (by rfl) ⟨3745250, by rfl⟩ : syracuseStep 4993667 = 7490501) B7490501
theorem B3329111 : Blo 2217435 3329111 := bstep (se 1 (by rfl) ⟨2496833, by rfl⟩ : syracuseStep 3329111 = 4993667) B4993667
theorem B2219407 : Blo 2217435 2219407 := bstep (se 1 (by rfl) ⟨1664555, by rfl⟩ : syracuseStep 2219407 = 3329111) B3329111
theorem B3329117 : Blo 2217435 3329117 := bbase (se 3 (by rfl) ⟨624209, by rfl⟩ : syracuseStep 3329117 = 1248419) (by norm_num)
theorem B2219411 : Blo 2217435 2219411 := bstep (se 1 (by rfl) ⟨1664558, by rfl⟩ : syracuseStep 2219411 = 3329117) B3329117
theorem B4993685 : Blo 2217435 4993685 := bbase (se 6 (by rfl) ⟨117039, by rfl⟩ : syracuseStep 4993685 = 234079) (by norm_num)
theorem B3329123 : Blo 2217435 3329123 := bstep (se 1 (by rfl) ⟨2496842, by rfl⟩ : syracuseStep 3329123 = 4993685) B4993685
theorem B2219415 : Blo 2217435 2219415 := bstep (se 1 (by rfl) ⟨1664561, by rfl⟩ : syracuseStep 2219415 = 3329123) B3329123
theorem B3999469 : Blo 2217435 3999469 := bbase (se 3 (by rfl) ⟨749900, by rfl⟩ : syracuseStep 3999469 = 1499801) (by norm_num)
theorem B5332625 : Blo 2217435 5332625 := bstep (se 2 (by rfl) ⟨1999734, by rfl⟩ : syracuseStep 5332625 = 3999469) B3999469
theorem B3555083 : Blo 2217435 3555083 := bstep (se 1 (by rfl) ⟨2666312, by rfl⟩ : syracuseStep 3555083 = 5332625) B5332625
theorem B2370055 : Blo 2217435 2370055 := bstep (se 1 (by rfl) ⟨1777541, by rfl⟩ : syracuseStep 2370055 = 3555083) B3555083
theorem B3160073 : Blo 2217435 3160073 := bstep (se 2 (by rfl) ⟨1185027, by rfl⟩ : syracuseStep 3160073 = 2370055) B2370055
theorem B8426861 : Blo 2217435 8426861 := bstep (se 3 (by rfl) ⟨1580036, by rfl⟩ : syracuseStep 8426861 = 3160073) B3160073
theorem B5617907 : Blo 2217435 5617907 := bstep (se 1 (by rfl) ⟨4213430, by rfl⟩ : syracuseStep 5617907 = 8426861) B8426861
theorem B3745271 : Blo 2217435 3745271 := bstep (se 1 (by rfl) ⟨2808953, by rfl⟩ : syracuseStep 3745271 = 5617907) B5617907
theorem B2496847 : Blo 2217435 2496847 := bstep (se 1 (by rfl) ⟨1872635, by rfl⟩ : syracuseStep 2496847 = 3745271) B3745271
theorem B3329129 : Blo 2217435 3329129 := bstep (se 2 (by rfl) ⟨1248423, by rfl⟩ : syracuseStep 3329129 = 2496847) B2496847
theorem B2219419 : Blo 2217435 2219419 := bstep (se 1 (by rfl) ⟨1664564, by rfl⟩ : syracuseStep 2219419 = 3329129) B3329129
theorem B7998949 : Blo 2217435 7998949 := bbase (se 4 (by rfl) ⟨749901, by rfl⟩ : syracuseStep 7998949 = 1499803) (by norm_num)
theorem B10665265 : Blo 2217435 10665265 := bstep (se 2 (by rfl) ⟨3999474, by rfl⟩ : syracuseStep 10665265 = 7998949) B7998949
theorem B14220353 : Blo 2217435 14220353 := bstep (se 2 (by rfl) ⟨5332632, by rfl⟩ : syracuseStep 14220353 = 10665265) B10665265
theorem B9480235 : Blo 2217435 9480235 := bstep (se 1 (by rfl) ⟨7110176, by rfl⟩ : syracuseStep 9480235 = 14220353) B14220353
theorem B12640313 : Blo 2217435 12640313 := bstep (se 2 (by rfl) ⟨4740117, by rfl⟩ : syracuseStep 12640313 = 9480235) B9480235
theorem B8426875 : Blo 2217435 8426875 := bstep (se 1 (by rfl) ⟨6320156, by rfl⟩ : syracuseStep 8426875 = 12640313) B12640313
theorem B11235833 : Blo 2217435 11235833 := bstep (se 2 (by rfl) ⟨4213437, by rfl⟩ : syracuseStep 11235833 = 8426875) B8426875
theorem B7490555 : Blo 2217435 7490555 := bstep (se 1 (by rfl) ⟨5617916, by rfl⟩ : syracuseStep 7490555 = 11235833) B11235833
theorem B4993703 : Blo 2217435 4993703 := bstep (se 1 (by rfl) ⟨3745277, by rfl⟩ : syracuseStep 4993703 = 7490555) B7490555
theorem B3329135 : Blo 2217435 3329135 := bstep (se 1 (by rfl) ⟨2496851, by rfl⟩ : syracuseStep 3329135 = 4993703) B4993703
theorem B2219423 : Blo 2217435 2219423 := bstep (se 1 (by rfl) ⟨1664567, by rfl⟩ : syracuseStep 2219423 = 3329135) B3329135
theorem B3329141 : Blo 2217435 3329141 := bbase (se 5 (by rfl) ⟨156053, by rfl⟩ : syracuseStep 3329141 = 312107) (by norm_num)
theorem B2219427 : Blo 2217435 2219427 := bstep (se 1 (by rfl) ⟨1664570, by rfl⟩ : syracuseStep 2219427 = 3329141) B3329141
theorem B4213453 : Blo 2217435 4213453 := bbase (se 3 (by rfl) ⟨790022, by rfl⟩ : syracuseStep 4213453 = 1580045) (by norm_num)
theorem B5617937 : Blo 2217435 5617937 := bstep (se 2 (by rfl) ⟨2106726, by rfl⟩ : syracuseStep 5617937 = 4213453) B4213453
theorem B3745291 : Blo 2217435 3745291 := bstep (se 1 (by rfl) ⟨2808968, by rfl⟩ : syracuseStep 3745291 = 5617937) B5617937
theorem B4993721 : Blo 2217435 4993721 := bstep (se 2 (by rfl) ⟨1872645, by rfl⟩ : syracuseStep 4993721 = 3745291) B3745291
theorem B3329147 : Blo 2217435 3329147 := bstep (se 1 (by rfl) ⟨2496860, by rfl⟩ : syracuseStep 3329147 = 4993721) B4993721
theorem B2219431 : Blo 2217435 2219431 := bstep (se 1 (by rfl) ⟨1664573, by rfl⟩ : syracuseStep 2219431 = 3329147) B3329147
theorem B2496865 : Blo 2217435 2496865 := bbase (se 2 (by rfl) ⟨936324, by rfl⟩ : syracuseStep 2496865 = 1872649) (by norm_num)
theorem B3329153 : Blo 2217435 3329153 := bstep (se 2 (by rfl) ⟨1248432, by rfl⟩ : syracuseStep 3329153 = 2496865) B2496865
theorem B2219435 : Blo 2217435 2219435 := bstep (se 1 (by rfl) ⟨1664576, by rfl⟩ : syracuseStep 2219435 = 3329153) B3329153
theorem C0 (j : ℕ) (h1 : 554358 ≤ j) (h2 : j ≤ 554858) : Blo 2217435 (4 * j + 3) := by
  interval_cases j
  · exact B2217435
  · exact B2217439
  · exact B2217443
  · exact B2217447
  · exact B2217451
  · exact B2217455
  · exact B2217459
  · exact B2217463
  · exact B2217467
  · exact B2217471
  · exact B2217475
  · exact B2217479
  · exact B2217483
  · exact B2217487
  · exact B2217491
  · exact B2217495
  · exact B2217499
  · exact B2217503
  · exact B2217507
  · exact B2217511
  · exact B2217515
  · exact B2217519
  · exact B2217523
  · exact B2217527
  · exact B2217531
  · exact B2217535
  · exact B2217539
  · exact B2217543
  · exact B2217547
  · exact B2217551
  · exact B2217555
  · exact B2217559
  · exact B2217563
  · exact B2217567
  · exact B2217571
  · exact B2217575
  · exact B2217579
  · exact B2217583
  · exact B2217587
  · exact B2217591
  · exact B2217595
  · exact B2217599
  · exact B2217603
  · exact B2217607
  · exact B2217611
  · exact B2217615
  · exact B2217619
  · exact B2217623
  · exact B2217627
  · exact B2217631
  · exact B2217635
  · exact B2217639
  · exact B2217643
  · exact B2217647
  · exact B2217651
  · exact B2217655
  · exact B2217659
  · exact B2217663
  · exact B2217667
  · exact B2217671
  · exact B2217675
  · exact B2217679
  · exact B2217683
  · exact B2217687
  · exact B2217691
  · exact B2217695
  · exact B2217699
  · exact B2217703
  · exact B2217707
  · exact B2217711
  · exact B2217715
  · exact B2217719
  · exact B2217723
  · exact B2217727
  · exact B2217731
  · exact B2217735
  · exact B2217739
  · exact B2217743
  · exact B2217747
  · exact B2217751
  · exact B2217755
  · exact B2217759
  · exact B2217763
  · exact B2217767
  · exact B2217771
  · exact B2217775
  · exact B2217779
  · exact B2217783
  · exact B2217787
  · exact B2217791
  · exact B2217795
  · exact B2217799
  · exact B2217803
  · exact B2217807
  · exact B2217811
  · exact B2217815
  · exact B2217819
  · exact B2217823
  · exact B2217827
  · exact B2217831
  · exact B2217835
  · exact B2217839
  · exact B2217843
  · exact B2217847
  · exact B2217851
  · exact B2217855
  · exact B2217859
  · exact B2217863
  · exact B2217867
  · exact B2217871
  · exact B2217875
  · exact B2217879
  · exact B2217883
  · exact B2217887
  · exact B2217891
  · exact B2217895
  · exact B2217899
  · exact B2217903
  · exact B2217907
  · exact B2217911
  · exact B2217915
  · exact B2217919
  · exact B2217923
  · exact B2217927
  · exact B2217931
  · exact B2217935
  · exact B2217939
  · exact B2217943
  · exact B2217947
  · exact B2217951
  · exact B2217955
  · exact B2217959
  · exact B2217963
  · exact B2217967
  · exact B2217971
  · exact B2217975
  · exact B2217979
  · exact B2217983
  · exact B2217987
  · exact B2217991
  · exact B2217995
  · exact B2217999
  · exact B2218003
  · exact B2218007
  · exact B2218011
  · exact B2218015
  · exact B2218019
  · exact B2218023
  · exact B2218027
  · exact B2218031
  · exact B2218035
  · exact B2218039
  · exact B2218043
  · exact B2218047
  · exact B2218051
  · exact B2218055
  · exact B2218059
  · exact B2218063
  · exact B2218067
  · exact B2218071
  · exact B2218075
  · exact B2218079
  · exact B2218083
  · exact B2218087
  · exact B2218091
  · exact B2218095
  · exact B2218099
  · exact B2218103
  · exact B2218107
  · exact B2218111
  · exact B2218115
  · exact B2218119
  · exact B2218123
  · exact B2218127
  · exact B2218131
  · exact B2218135
  · exact B2218139
  · exact B2218143
  · exact B2218147
  · exact B2218151
  · exact B2218155
  · exact B2218159
  · exact B2218163
  · exact B2218167
  · exact B2218171
  · exact B2218175
  · exact B2218179
  · exact B2218183
  · exact B2218187
  · exact B2218191
  · exact B2218195
  · exact B2218199
  · exact B2218203
  · exact B2218207
  · exact B2218211
  · exact B2218215
  · exact B2218219
  · exact B2218223
  · exact B2218227
  · exact B2218231
  · exact B2218235
  · exact B2218239
  · exact B2218243
  · exact B2218247
  · exact B2218251
  · exact B2218255
  · exact B2218259
  · exact B2218263
  · exact B2218267
  · exact B2218271
  · exact B2218275
  · exact B2218279
  · exact B2218283
  · exact B2218287
  · exact B2218291
  · exact B2218295
  · exact B2218299
  · exact B2218303
  · exact B2218307
  · exact B2218311
  · exact B2218315
  · exact B2218319
  · exact B2218323
  · exact B2218327
  · exact B2218331
  · exact B2218335
  · exact B2218339
  · exact B2218343
  · exact B2218347
  · exact B2218351
  · exact B2218355
  · exact B2218359
  · exact B2218363
  · exact B2218367
  · exact B2218371
  · exact B2218375
  · exact B2218379
  · exact B2218383
  · exact B2218387
  · exact B2218391
  · exact B2218395
  · exact B2218399
  · exact B2218403
  · exact B2218407
  · exact B2218411
  · exact B2218415
  · exact B2218419
  · exact B2218423
  · exact B2218427
  · exact B2218431
  · exact B2218435
  · exact B2218439
  · exact B2218443
  · exact B2218447
  · exact B2218451
  · exact B2218455
  · exact B2218459
  · exact B2218463
  · exact B2218467
  · exact B2218471
  · exact B2218475
  · exact B2218479
  · exact B2218483
  · exact B2218487
  · exact B2218491
  · exact B2218495
  · exact B2218499
  · exact B2218503
  · exact B2218507
  · exact B2218511
  · exact B2218515
  · exact B2218519
  · exact B2218523
  · exact B2218527
  · exact B2218531
  · exact B2218535
  · exact B2218539
  · exact B2218543
  · exact B2218547
  · exact B2218551
  · exact B2218555
  · exact B2218559
  · exact B2218563
  · exact B2218567
  · exact B2218571
  · exact B2218575
  · exact B2218579
  · exact B2218583
  · exact B2218587
  · exact B2218591
  · exact B2218595
  · exact B2218599
  · exact B2218603
  · exact B2218607
  · exact B2218611
  · exact B2218615
  · exact B2218619
  · exact B2218623
  · exact B2218627
  · exact B2218631
  · exact B2218635
  · exact B2218639
  · exact B2218643
  · exact B2218647
  · exact B2218651
  · exact B2218655
  · exact B2218659
  · exact B2218663
  · exact B2218667
  · exact B2218671
  · exact B2218675
  · exact B2218679
  · exact B2218683
  · exact B2218687
  · exact B2218691
  · exact B2218695
  · exact B2218699
  · exact B2218703
  · exact B2218707
  · exact B2218711
  · exact B2218715
  · exact B2218719
  · exact B2218723
  · exact B2218727
  · exact B2218731
  · exact B2218735
  · exact B2218739
  · exact B2218743
  · exact B2218747
  · exact B2218751
  · exact B2218755
  · exact B2218759
  · exact B2218763
  · exact B2218767
  · exact B2218771
  · exact B2218775
  · exact B2218779
  · exact B2218783
  · exact B2218787
  · exact B2218791
  · exact B2218795
  · exact B2218799
  · exact B2218803
  · exact B2218807
  · exact B2218811
  · exact B2218815
  · exact B2218819
  · exact B2218823
  · exact B2218827
  · exact B2218831
  · exact B2218835
  · exact B2218839
  · exact B2218843
  · exact B2218847
  · exact B2218851
  · exact B2218855
  · exact B2218859
  · exact B2218863
  · exact B2218867
  · exact B2218871
  · exact B2218875
  · exact B2218879
  · exact B2218883
  · exact B2218887
  · exact B2218891
  · exact B2218895
  · exact B2218899
  · exact B2218903
  · exact B2218907
  · exact B2218911
  · exact B2218915
  · exact B2218919
  · exact B2218923
  · exact B2218927
  · exact B2218931
  · exact B2218935
  · exact B2218939
  · exact B2218943
  · exact B2218947
  · exact B2218951
  · exact B2218955
  · exact B2218959
  · exact B2218963
  · exact B2218967
  · exact B2218971
  · exact B2218975
  · exact B2218979
  · exact B2218983
  · exact B2218987
  · exact B2218991
  · exact B2218995
  · exact B2218999
  · exact B2219003
  · exact B2219007
  · exact B2219011
  · exact B2219015
  · exact B2219019
  · exact B2219023
  · exact B2219027
  · exact B2219031
  · exact B2219035
  · exact B2219039
  · exact B2219043
  · exact B2219047
  · exact B2219051
  · exact B2219055
  · exact B2219059
  · exact B2219063
  · exact B2219067
  · exact B2219071
  · exact B2219075
  · exact B2219079
  · exact B2219083
  · exact B2219087
  · exact B2219091
  · exact B2219095
  · exact B2219099
  · exact B2219103
  · exact B2219107
  · exact B2219111
  · exact B2219115
  · exact B2219119
  · exact B2219123
  · exact B2219127
  · exact B2219131
  · exact B2219135
  · exact B2219139
  · exact B2219143
  · exact B2219147
  · exact B2219151
  · exact B2219155
  · exact B2219159
  · exact B2219163
  · exact B2219167
  · exact B2219171
  · exact B2219175
  · exact B2219179
  · exact B2219183
  · exact B2219187
  · exact B2219191
  · exact B2219195
  · exact B2219199
  · exact B2219203
  · exact B2219207
  · exact B2219211
  · exact B2219215
  · exact B2219219
  · exact B2219223
  · exact B2219227
  · exact B2219231
  · exact B2219235
  · exact B2219239
  · exact B2219243
  · exact B2219247
  · exact B2219251
  · exact B2219255
  · exact B2219259
  · exact B2219263
  · exact B2219267
  · exact B2219271
  · exact B2219275
  · exact B2219279
  · exact B2219283
  · exact B2219287
  · exact B2219291
  · exact B2219295
  · exact B2219299
  · exact B2219303
  · exact B2219307
  · exact B2219311
  · exact B2219315
  · exact B2219319
  · exact B2219323
  · exact B2219327
  · exact B2219331
  · exact B2219335
  · exact B2219339
  · exact B2219343
  · exact B2219347
  · exact B2219351
  · exact B2219355
  · exact B2219359
  · exact B2219363
  · exact B2219367
  · exact B2219371
  · exact B2219375
  · exact B2219379
  · exact B2219383
  · exact B2219387
  · exact B2219391
  · exact B2219395
  · exact B2219399
  · exact B2219403
  · exact B2219407
  · exact B2219411
  · exact B2219415
  · exact B2219419
  · exact B2219423
  · exact B2219427
  · exact B2219431
  · exact B2219435
theorem solution (m : ℕ) (hlo : 2217435 ≤ m) (hhi : m ≤ 2219435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 554358 ≤ j := by omega
    have hj2 : j ≤ 554858 := by omega
    have hb : Blo 2217435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
