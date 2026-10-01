-- Prove2me | solution 1 for syracuse_descends_range_1897435_1899435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:47.985832+00:00
-- url     : https://prove2.me/submissions/dac79245-d74d-40b1-be79-b971d897aac2

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

theorem B4802885 : Blo 1897435 4802885 := bbase (se 4 (by rfl) ⟨450270, by rfl⟩ : syracuseStep 4802885 = 900541) (by norm_num)
theorem B3201923 : Blo 1897435 3201923 := bstep (se 1 (by rfl) ⟨2401442, by rfl⟩ : syracuseStep 3201923 = 4802885) B4802885
theorem B2134615 : Blo 1897435 2134615 := bstep (se 1 (by rfl) ⟨1600961, by rfl⟩ : syracuseStep 2134615 = 3201923) B3201923
theorem B2846153 : Blo 1897435 2846153 := bstep (se 2 (by rfl) ⟨1067307, by rfl⟩ : syracuseStep 2846153 = 2134615) B2134615
theorem B1897435 : Blo 1897435 1897435 := bstep (se 1 (by rfl) ⟨1423076, by rfl⟩ : syracuseStep 1897435 = 2846153) B2846153
theorem B10257749 : Blo 1897435 10257749 := bbase (se 12 (by rfl) ⟨3756, by rfl⟩ : syracuseStep 10257749 = 7513) (by norm_num)
theorem B6838499 : Blo 1897435 6838499 := bstep (se 1 (by rfl) ⟨5128874, by rfl⟩ : syracuseStep 6838499 = 10257749) B10257749
theorem B4558999 : Blo 1897435 4558999 := bstep (se 1 (by rfl) ⟨3419249, by rfl⟩ : syracuseStep 4558999 = 6838499) B6838499
theorem B6078665 : Blo 1897435 6078665 := bstep (se 2 (by rfl) ⟨2279499, by rfl⟩ : syracuseStep 6078665 = 4558999) B4558999
theorem B4052443 : Blo 1897435 4052443 := bstep (se 1 (by rfl) ⟨3039332, by rfl⟩ : syracuseStep 4052443 = 6078665) B6078665
theorem B5403257 : Blo 1897435 5403257 := bstep (se 2 (by rfl) ⟨2026221, by rfl⟩ : syracuseStep 5403257 = 4052443) B4052443
theorem B3602171 : Blo 1897435 3602171 := bstep (se 1 (by rfl) ⟨2701628, by rfl⟩ : syracuseStep 3602171 = 5403257) B5403257
theorem B9605789 : Blo 1897435 9605789 := bstep (se 3 (by rfl) ⟨1801085, by rfl⟩ : syracuseStep 9605789 = 3602171) B3602171
theorem B6403859 : Blo 1897435 6403859 := bstep (se 1 (by rfl) ⟨4802894, by rfl⟩ : syracuseStep 6403859 = 9605789) B9605789
theorem B4269239 : Blo 1897435 4269239 := bstep (se 1 (by rfl) ⟨3201929, by rfl⟩ : syracuseStep 4269239 = 6403859) B6403859
theorem B2846159 : Blo 1897435 2846159 := bstep (se 1 (by rfl) ⟨2134619, by rfl⟩ : syracuseStep 2846159 = 4269239) B4269239
theorem B1897439 : Blo 1897435 1897439 := bstep (se 1 (by rfl) ⟨1423079, by rfl⟩ : syracuseStep 1897439 = 2846159) B2846159
theorem B2846165 : Blo 1897435 2846165 := bbase (se 7 (by rfl) ⟨33353, by rfl⟩ : syracuseStep 2846165 = 66707) (by norm_num)
theorem B1897443 : Blo 1897435 1897443 := bstep (se 1 (by rfl) ⟨1423082, by rfl⟩ : syracuseStep 1897443 = 2846165) B2846165
theorem B7204373 : Blo 1897435 7204373 := bbase (se 6 (by rfl) ⟨168852, by rfl⟩ : syracuseStep 7204373 = 337705) (by norm_num)
theorem B4802915 : Blo 1897435 4802915 := bstep (se 1 (by rfl) ⟨3602186, by rfl⟩ : syracuseStep 4802915 = 7204373) B7204373
theorem B3201943 : Blo 1897435 3201943 := bstep (se 1 (by rfl) ⟨2401457, by rfl⟩ : syracuseStep 3201943 = 4802915) B4802915
theorem B4269257 : Blo 1897435 4269257 := bstep (se 2 (by rfl) ⟨1600971, by rfl⟩ : syracuseStep 4269257 = 3201943) B3201943
theorem B2846171 : Blo 1897435 2846171 := bstep (se 1 (by rfl) ⟨2134628, by rfl⟩ : syracuseStep 2846171 = 4269257) B4269257
theorem B1897447 : Blo 1897435 1897447 := bstep (se 1 (by rfl) ⟨1423085, by rfl⟩ : syracuseStep 1897447 = 2846171) B2846171
theorem B2134633 : Blo 1897435 2134633 := bbase (se 2 (by rfl) ⟨800487, by rfl⟩ : syracuseStep 2134633 = 1600975) (by norm_num)
theorem B2846177 : Blo 1897435 2846177 := bstep (se 2 (by rfl) ⟨1067316, by rfl⟩ : syracuseStep 2846177 = 2134633) B2134633
theorem B1897451 : Blo 1897435 1897451 := bstep (se 1 (by rfl) ⟨1423088, by rfl⟩ : syracuseStep 1897451 = 2846177) B2846177
theorem B4052477 : Blo 1897435 4052477 := bbase (se 3 (by rfl) ⟨759839, by rfl⟩ : syracuseStep 4052477 = 1519679) (by norm_num)
theorem B10806605 : Blo 1897435 10806605 := bstep (se 3 (by rfl) ⟨2026238, by rfl⟩ : syracuseStep 10806605 = 4052477) B4052477
theorem B7204403 : Blo 1897435 7204403 := bstep (se 1 (by rfl) ⟨5403302, by rfl⟩ : syracuseStep 7204403 = 10806605) B10806605
theorem B4802935 : Blo 1897435 4802935 := bstep (se 1 (by rfl) ⟨3602201, by rfl⟩ : syracuseStep 4802935 = 7204403) B7204403
theorem B6403913 : Blo 1897435 6403913 := bstep (se 2 (by rfl) ⟨2401467, by rfl⟩ : syracuseStep 6403913 = 4802935) B4802935
theorem B4269275 : Blo 1897435 4269275 := bstep (se 1 (by rfl) ⟨3201956, by rfl⟩ : syracuseStep 4269275 = 6403913) B6403913
theorem B2846183 : Blo 1897435 2846183 := bstep (se 1 (by rfl) ⟨2134637, by rfl⟩ : syracuseStep 2846183 = 4269275) B4269275
theorem B1897455 : Blo 1897435 1897455 := bstep (se 1 (by rfl) ⟨1423091, by rfl⟩ : syracuseStep 1897455 = 2846183) B2846183
theorem B2846189 : Blo 1897435 2846189 := bbase (se 3 (by rfl) ⟨533660, by rfl⟩ : syracuseStep 2846189 = 1067321) (by norm_num)
theorem B1897459 : Blo 1897435 1897459 := bstep (se 1 (by rfl) ⟨1423094, by rfl⟩ : syracuseStep 1897459 = 2846189) B2846189
theorem B4269293 : Blo 1897435 4269293 := bbase (se 3 (by rfl) ⟨800492, by rfl⟩ : syracuseStep 4269293 = 1600985) (by norm_num)
theorem B2846195 : Blo 1897435 2846195 := bstep (se 1 (by rfl) ⟨2134646, by rfl⟩ : syracuseStep 2846195 = 4269293) B4269293
theorem B1897463 : Blo 1897435 1897463 := bstep (se 1 (by rfl) ⟨1423097, by rfl⟩ : syracuseStep 1897463 = 2846195) B2846195
theorem B2701669 : Blo 1897435 2701669 := bbase (se 4 (by rfl) ⟨253281, by rfl⟩ : syracuseStep 2701669 = 506563) (by norm_num)
theorem B3602225 : Blo 1897435 3602225 := bstep (se 2 (by rfl) ⟨1350834, by rfl⟩ : syracuseStep 3602225 = 2701669) B2701669
theorem B2401483 : Blo 1897435 2401483 := bstep (se 1 (by rfl) ⟨1801112, by rfl⟩ : syracuseStep 2401483 = 3602225) B3602225
theorem B3201977 : Blo 1897435 3201977 := bstep (se 2 (by rfl) ⟨1200741, by rfl⟩ : syracuseStep 3201977 = 2401483) B2401483
theorem B2134651 : Blo 1897435 2134651 := bstep (se 1 (by rfl) ⟨1600988, by rfl⟩ : syracuseStep 2134651 = 3201977) B3201977
theorem B2846201 : Blo 1897435 2846201 := bstep (se 2 (by rfl) ⟨1067325, by rfl⟩ : syracuseStep 2846201 = 2134651) B2134651
theorem B1897467 : Blo 1897435 1897467 := bstep (se 1 (by rfl) ⟨1423100, by rfl⟩ : syracuseStep 1897467 = 2846201) B2846201
theorem B13863829 : Blo 1897435 13863829 := bbase (se 6 (by rfl) ⟨324933, by rfl⟩ : syracuseStep 13863829 = 649867) (by norm_num)
theorem B18485105 : Blo 1897435 18485105 := bstep (se 2 (by rfl) ⟨6931914, by rfl⟩ : syracuseStep 18485105 = 13863829) B13863829
theorem B49293613 : Blo 1897435 49293613 := bstep (se 3 (by rfl) ⟨9242552, by rfl⟩ : syracuseStep 49293613 = 18485105) B18485105
theorem B65724817 : Blo 1897435 65724817 := bstep (se 2 (by rfl) ⟨24646806, by rfl⟩ : syracuseStep 65724817 = 49293613) B49293613
theorem B87633089 : Blo 1897435 87633089 := bstep (se 2 (by rfl) ⟨32862408, by rfl⟩ : syracuseStep 87633089 = 65724817) B65724817
theorem B58422059 : Blo 1897435 58422059 := bstep (se 1 (by rfl) ⟨43816544, by rfl⟩ : syracuseStep 58422059 = 87633089) B87633089
theorem B38948039 : Blo 1897435 38948039 := bstep (se 1 (by rfl) ⟨29211029, by rfl⟩ : syracuseStep 38948039 = 58422059) B58422059
theorem B25965359 : Blo 1897435 25965359 := bstep (se 1 (by rfl) ⟨19474019, by rfl⟩ : syracuseStep 25965359 = 38948039) B38948039
theorem B17310239 : Blo 1897435 17310239 := bstep (se 1 (by rfl) ⟨12982679, by rfl⟩ : syracuseStep 17310239 = 25965359) B25965359
theorem B11540159 : Blo 1897435 11540159 := bstep (se 1 (by rfl) ⟨8655119, by rfl⟩ : syracuseStep 11540159 = 17310239) B17310239
theorem B7693439 : Blo 1897435 7693439 := bstep (se 1 (by rfl) ⟨5770079, by rfl⟩ : syracuseStep 7693439 = 11540159) B11540159
theorem B20515837 : Blo 1897435 20515837 := bstep (se 3 (by rfl) ⟨3846719, by rfl⟩ : syracuseStep 20515837 = 7693439) B7693439
theorem B27354449 : Blo 1897435 27354449 := bstep (se 2 (by rfl) ⟨10257918, by rfl⟩ : syracuseStep 27354449 = 20515837) B20515837
theorem B72945197 : Blo 1897435 72945197 := bstep (se 3 (by rfl) ⟨13677224, by rfl⟩ : syracuseStep 72945197 = 27354449) B27354449
theorem B48630131 : Blo 1897435 48630131 := bstep (se 1 (by rfl) ⟨36472598, by rfl⟩ : syracuseStep 48630131 = 72945197) B72945197
theorem B32420087 : Blo 1897435 32420087 := bstep (se 1 (by rfl) ⟨24315065, by rfl⟩ : syracuseStep 32420087 = 48630131) B48630131
theorem B21613391 : Blo 1897435 21613391 := bstep (se 1 (by rfl) ⟨16210043, by rfl⟩ : syracuseStep 21613391 = 32420087) B32420087
theorem B14408927 : Blo 1897435 14408927 := bstep (se 1 (by rfl) ⟨10806695, by rfl⟩ : syracuseStep 14408927 = 21613391) B21613391
theorem B9605951 : Blo 1897435 9605951 := bstep (se 1 (by rfl) ⟨7204463, by rfl⟩ : syracuseStep 9605951 = 14408927) B14408927
theorem B6403967 : Blo 1897435 6403967 := bstep (se 1 (by rfl) ⟨4802975, by rfl⟩ : syracuseStep 6403967 = 9605951) B9605951
theorem B4269311 : Blo 1897435 4269311 := bstep (se 1 (by rfl) ⟨3201983, by rfl⟩ : syracuseStep 4269311 = 6403967) B6403967
theorem B2846207 : Blo 1897435 2846207 := bstep (se 1 (by rfl) ⟨2134655, by rfl⟩ : syracuseStep 2846207 = 4269311) B4269311
theorem B1897471 : Blo 1897435 1897471 := bstep (se 1 (by rfl) ⟨1423103, by rfl⟩ : syracuseStep 1897471 = 2846207) B2846207
theorem B2846213 : Blo 1897435 2846213 := bbase (se 4 (by rfl) ⟨266832, by rfl⟩ : syracuseStep 2846213 = 533665) (by norm_num)
theorem B1897475 : Blo 1897435 1897475 := bstep (se 1 (by rfl) ⟨1423106, by rfl⟩ : syracuseStep 1897475 = 2846213) B2846213
theorem B3201997 : Blo 1897435 3201997 := bbase (se 3 (by rfl) ⟨600374, by rfl⟩ : syracuseStep 3201997 = 1200749) (by norm_num)
theorem B4269329 : Blo 1897435 4269329 := bstep (se 2 (by rfl) ⟨1600998, by rfl⟩ : syracuseStep 4269329 = 3201997) B3201997
theorem B2846219 : Blo 1897435 2846219 := bstep (se 1 (by rfl) ⟨2134664, by rfl⟩ : syracuseStep 2846219 = 4269329) B4269329
theorem B1897479 : Blo 1897435 1897479 := bstep (se 1 (by rfl) ⟨1423109, by rfl⟩ : syracuseStep 1897479 = 2846219) B2846219
theorem B2134669 : Blo 1897435 2134669 := bbase (se 3 (by rfl) ⟨400250, by rfl⟩ : syracuseStep 2134669 = 800501) (by norm_num)
theorem B2846225 : Blo 1897435 2846225 := bstep (se 2 (by rfl) ⟨1067334, by rfl⟩ : syracuseStep 2846225 = 2134669) B2134669
theorem B1897483 : Blo 1897435 1897483 := bstep (se 1 (by rfl) ⟨1423112, by rfl⟩ : syracuseStep 1897483 = 2846225) B2846225
theorem B6404021 : Blo 1897435 6404021 := bbase (se 5 (by rfl) ⟨300188, by rfl⟩ : syracuseStep 6404021 = 600377) (by norm_num)
theorem B4269347 : Blo 1897435 4269347 := bstep (se 1 (by rfl) ⟨3202010, by rfl⟩ : syracuseStep 4269347 = 6404021) B6404021
theorem B2846231 : Blo 1897435 2846231 := bstep (se 1 (by rfl) ⟨2134673, by rfl⟩ : syracuseStep 2846231 = 4269347) B4269347
theorem B1897487 : Blo 1897435 1897487 := bstep (se 1 (by rfl) ⟨1423115, by rfl⟩ : syracuseStep 1897487 = 2846231) B2846231
theorem B2846237 : Blo 1897435 2846237 := bbase (se 3 (by rfl) ⟨533669, by rfl⟩ : syracuseStep 2846237 = 1067339) (by norm_num)
theorem B1897491 : Blo 1897435 1897491 := bstep (se 1 (by rfl) ⟨1423118, by rfl⟩ : syracuseStep 1897491 = 2846237) B2846237
theorem B4269365 : Blo 1897435 4269365 := bbase (se 5 (by rfl) ⟨200126, by rfl⟩ : syracuseStep 4269365 = 400253) (by norm_num)
theorem B2846243 : Blo 1897435 2846243 := bstep (se 1 (by rfl) ⟨2134682, by rfl⟩ : syracuseStep 2846243 = 4269365) B4269365
theorem B1897495 : Blo 1897435 1897495 := bstep (se 1 (by rfl) ⟨1423121, by rfl⟩ : syracuseStep 1897495 = 2846243) B2846243
theorem B7302869 : Blo 1897435 7302869 := bbase (se 7 (by rfl) ⟨85580, by rfl⟩ : syracuseStep 7302869 = 171161) (by norm_num)
theorem B4868579 : Blo 1897435 4868579 := bstep (se 1 (by rfl) ⟨3651434, by rfl⟩ : syracuseStep 4868579 = 7302869) B7302869
theorem B3245719 : Blo 1897435 3245719 := bstep (se 1 (by rfl) ⟨2434289, by rfl⟩ : syracuseStep 3245719 = 4868579) B4868579
theorem B4327625 : Blo 1897435 4327625 := bstep (se 2 (by rfl) ⟨1622859, by rfl⟩ : syracuseStep 4327625 = 3245719) B3245719
theorem B11540333 : Blo 1897435 11540333 := bstep (se 3 (by rfl) ⟨2163812, by rfl⟩ : syracuseStep 11540333 = 4327625) B4327625
theorem B7693555 : Blo 1897435 7693555 := bstep (se 1 (by rfl) ⟨5770166, by rfl⟩ : syracuseStep 7693555 = 11540333) B11540333
theorem B10258073 : Blo 1897435 10258073 := bstep (se 2 (by rfl) ⟨3846777, by rfl⟩ : syracuseStep 10258073 = 7693555) B7693555
theorem B6838715 : Blo 1897435 6838715 := bstep (se 1 (by rfl) ⟨5129036, by rfl⟩ : syracuseStep 6838715 = 10258073) B10258073
theorem B18236573 : Blo 1897435 18236573 := bstep (se 3 (by rfl) ⟨3419357, by rfl⟩ : syracuseStep 18236573 = 6838715) B6838715
theorem B12157715 : Blo 1897435 12157715 := bstep (se 1 (by rfl) ⟨9118286, by rfl⟩ : syracuseStep 12157715 = 18236573) B18236573
theorem B8105143 : Blo 1897435 8105143 := bstep (se 1 (by rfl) ⟨6078857, by rfl⟩ : syracuseStep 8105143 = 12157715) B12157715
theorem B10806857 : Blo 1897435 10806857 := bstep (se 2 (by rfl) ⟨4052571, by rfl⟩ : syracuseStep 10806857 = 8105143) B8105143
theorem B7204571 : Blo 1897435 7204571 := bstep (se 1 (by rfl) ⟨5403428, by rfl⟩ : syracuseStep 7204571 = 10806857) B10806857
theorem B4803047 : Blo 1897435 4803047 := bstep (se 1 (by rfl) ⟨3602285, by rfl⟩ : syracuseStep 4803047 = 7204571) B7204571
theorem B3202031 : Blo 1897435 3202031 := bstep (se 1 (by rfl) ⟨2401523, by rfl⟩ : syracuseStep 3202031 = 4803047) B4803047
theorem B2134687 : Blo 1897435 2134687 := bstep (se 1 (by rfl) ⟨1601015, by rfl⟩ : syracuseStep 2134687 = 3202031) B3202031
theorem B2846249 : Blo 1897435 2846249 := bstep (se 2 (by rfl) ⟨1067343, by rfl⟩ : syracuseStep 2846249 = 2134687) B2134687
theorem B1897499 : Blo 1897435 1897499 := bstep (se 1 (by rfl) ⟨1423124, by rfl⟩ : syracuseStep 1897499 = 2846249) B2846249
theorem B2163817 : Blo 1897435 2163817 := bbase (se 2 (by rfl) ⟨811431, by rfl⟩ : syracuseStep 2163817 = 1622863) (by norm_num)
theorem B2885089 : Blo 1897435 2885089 := bstep (se 2 (by rfl) ⟨1081908, by rfl⟩ : syracuseStep 2885089 = 2163817) B2163817
theorem B3846785 : Blo 1897435 3846785 := bstep (se 2 (by rfl) ⟨1442544, by rfl⟩ : syracuseStep 3846785 = 2885089) B2885089
theorem B10258093 : Blo 1897435 10258093 := bstep (se 3 (by rfl) ⟨1923392, by rfl⟩ : syracuseStep 10258093 = 3846785) B3846785
theorem B13677457 : Blo 1897435 13677457 := bstep (se 2 (by rfl) ⟨5129046, by rfl⟩ : syracuseStep 13677457 = 10258093) B10258093
theorem B18236609 : Blo 1897435 18236609 := bstep (se 2 (by rfl) ⟨6838728, by rfl⟩ : syracuseStep 18236609 = 13677457) B13677457
theorem B12157739 : Blo 1897435 12157739 := bstep (se 1 (by rfl) ⟨9118304, by rfl⟩ : syracuseStep 12157739 = 18236609) B18236609
theorem B8105159 : Blo 1897435 8105159 := bstep (se 1 (by rfl) ⟨6078869, by rfl⟩ : syracuseStep 8105159 = 12157739) B12157739
theorem B5403439 : Blo 1897435 5403439 := bstep (se 1 (by rfl) ⟨4052579, by rfl⟩ : syracuseStep 5403439 = 8105159) B8105159
theorem B7204585 : Blo 1897435 7204585 := bstep (se 2 (by rfl) ⟨2701719, by rfl⟩ : syracuseStep 7204585 = 5403439) B5403439
theorem B9606113 : Blo 1897435 9606113 := bstep (se 2 (by rfl) ⟨3602292, by rfl⟩ : syracuseStep 9606113 = 7204585) B7204585
theorem B6404075 : Blo 1897435 6404075 := bstep (se 1 (by rfl) ⟨4803056, by rfl⟩ : syracuseStep 6404075 = 9606113) B9606113
theorem B4269383 : Blo 1897435 4269383 := bstep (se 1 (by rfl) ⟨3202037, by rfl⟩ : syracuseStep 4269383 = 6404075) B6404075
theorem B2846255 : Blo 1897435 2846255 := bstep (se 1 (by rfl) ⟨2134691, by rfl⟩ : syracuseStep 2846255 = 4269383) B4269383
theorem B1897503 : Blo 1897435 1897503 := bstep (se 1 (by rfl) ⟨1423127, by rfl⟩ : syracuseStep 1897503 = 2846255) B2846255
theorem B2846261 : Blo 1897435 2846261 := bbase (se 5 (by rfl) ⟨133418, by rfl⟩ : syracuseStep 2846261 = 266837) (by norm_num)
theorem B1897507 : Blo 1897435 1897507 := bstep (se 1 (by rfl) ⟨1423130, by rfl⟩ : syracuseStep 1897507 = 2846261) B2846261
theorem B4803077 : Blo 1897435 4803077 := bbase (se 4 (by rfl) ⟨450288, by rfl⟩ : syracuseStep 4803077 = 900577) (by norm_num)
theorem B3202051 : Blo 1897435 3202051 := bstep (se 1 (by rfl) ⟨2401538, by rfl⟩ : syracuseStep 3202051 = 4803077) B4803077
theorem B4269401 : Blo 1897435 4269401 := bstep (se 2 (by rfl) ⟨1601025, by rfl⟩ : syracuseStep 4269401 = 3202051) B3202051
theorem B2846267 : Blo 1897435 2846267 := bstep (se 1 (by rfl) ⟨2134700, by rfl⟩ : syracuseStep 2846267 = 4269401) B4269401
theorem B1897511 : Blo 1897435 1897511 := bstep (se 1 (by rfl) ⟨1423133, by rfl⟩ : syracuseStep 1897511 = 2846267) B2846267
theorem B2134705 : Blo 1897435 2134705 := bbase (se 2 (by rfl) ⟨800514, by rfl⟩ : syracuseStep 2134705 = 1601029) (by norm_num)
theorem B2846273 : Blo 1897435 2846273 := bstep (se 2 (by rfl) ⟨1067352, by rfl⟩ : syracuseStep 2846273 = 2134705) B2134705
theorem B1897515 : Blo 1897435 1897515 := bstep (se 1 (by rfl) ⟨1423136, by rfl⟩ : syracuseStep 1897515 = 2846273) B2846273
theorem B3039461 : Blo 1897435 3039461 := bbase (se 4 (by rfl) ⟨284949, by rfl⟩ : syracuseStep 3039461 = 569899) (by norm_num)
theorem B2026307 : Blo 1897435 2026307 := bstep (se 1 (by rfl) ⟨1519730, by rfl⟩ : syracuseStep 2026307 = 3039461) B3039461
theorem B5403485 : Blo 1897435 5403485 := bstep (se 3 (by rfl) ⟨1013153, by rfl⟩ : syracuseStep 5403485 = 2026307) B2026307
theorem B3602323 : Blo 1897435 3602323 := bstep (se 1 (by rfl) ⟨2701742, by rfl⟩ : syracuseStep 3602323 = 5403485) B5403485
theorem B4803097 : Blo 1897435 4803097 := bstep (se 2 (by rfl) ⟨1801161, by rfl⟩ : syracuseStep 4803097 = 3602323) B3602323
theorem B6404129 : Blo 1897435 6404129 := bstep (se 2 (by rfl) ⟨2401548, by rfl⟩ : syracuseStep 6404129 = 4803097) B4803097
theorem B4269419 : Blo 1897435 4269419 := bstep (se 1 (by rfl) ⟨3202064, by rfl⟩ : syracuseStep 4269419 = 6404129) B6404129
theorem B2846279 : Blo 1897435 2846279 := bstep (se 1 (by rfl) ⟨2134709, by rfl⟩ : syracuseStep 2846279 = 4269419) B4269419
theorem B1897519 : Blo 1897435 1897519 := bstep (se 1 (by rfl) ⟨1423139, by rfl⟩ : syracuseStep 1897519 = 2846279) B2846279
theorem B2846285 : Blo 1897435 2846285 := bbase (se 3 (by rfl) ⟨533678, by rfl⟩ : syracuseStep 2846285 = 1067357) (by norm_num)
theorem B1897523 : Blo 1897435 1897523 := bstep (se 1 (by rfl) ⟨1423142, by rfl⟩ : syracuseStep 1897523 = 2846285) B2846285
theorem B4269437 : Blo 1897435 4269437 := bbase (se 3 (by rfl) ⟨800519, by rfl⟩ : syracuseStep 4269437 = 1601039) (by norm_num)
theorem B2846291 : Blo 1897435 2846291 := bstep (se 1 (by rfl) ⟨2134718, by rfl⟩ : syracuseStep 2846291 = 4269437) B4269437
theorem B1897527 : Blo 1897435 1897527 := bstep (se 1 (by rfl) ⟨1423145, by rfl⟩ : syracuseStep 1897527 = 2846291) B2846291
theorem B3202085 : Blo 1897435 3202085 := bbase (se 4 (by rfl) ⟨300195, by rfl⟩ : syracuseStep 3202085 = 600391) (by norm_num)
theorem B2134723 : Blo 1897435 2134723 := bstep (se 1 (by rfl) ⟨1601042, by rfl⟩ : syracuseStep 2134723 = 3202085) B3202085
theorem B2846297 : Blo 1897435 2846297 := bstep (se 2 (by rfl) ⟨1067361, by rfl⟩ : syracuseStep 2846297 = 2134723) B2134723
theorem B1897531 : Blo 1897435 1897531 := bstep (se 1 (by rfl) ⟨1423148, by rfl⟩ : syracuseStep 1897531 = 2846297) B2846297
theorem B2701765 : Blo 1897435 2701765 := bbase (se 4 (by rfl) ⟨253290, by rfl⟩ : syracuseStep 2701765 = 506581) (by norm_num)
theorem B14409413 : Blo 1897435 14409413 := bstep (se 4 (by rfl) ⟨1350882, by rfl⟩ : syracuseStep 14409413 = 2701765) B2701765
theorem B9606275 : Blo 1897435 9606275 := bstep (se 1 (by rfl) ⟨7204706, by rfl⟩ : syracuseStep 9606275 = 14409413) B14409413
theorem B6404183 : Blo 1897435 6404183 := bstep (se 1 (by rfl) ⟨4803137, by rfl⟩ : syracuseStep 6404183 = 9606275) B9606275
theorem B4269455 : Blo 1897435 4269455 := bstep (se 1 (by rfl) ⟨3202091, by rfl⟩ : syracuseStep 4269455 = 6404183) B6404183
theorem B2846303 : Blo 1897435 2846303 := bstep (se 1 (by rfl) ⟨2134727, by rfl⟩ : syracuseStep 2846303 = 4269455) B4269455
theorem B1897535 : Blo 1897435 1897535 := bstep (se 1 (by rfl) ⟨1423151, by rfl⟩ : syracuseStep 1897535 = 2846303) B2846303
theorem B2846309 : Blo 1897435 2846309 := bbase (se 4 (by rfl) ⟨266841, by rfl⟩ : syracuseStep 2846309 = 533683) (by norm_num)
theorem B1897539 : Blo 1897435 1897539 := bstep (se 1 (by rfl) ⟨1423154, by rfl⟩ : syracuseStep 1897539 = 2846309) B2846309
theorem B2026333 : Blo 1897435 2026333 := bbase (se 3 (by rfl) ⟨379937, by rfl⟩ : syracuseStep 2026333 = 759875) (by norm_num)
theorem B2701777 : Blo 1897435 2701777 := bstep (se 2 (by rfl) ⟨1013166, by rfl⟩ : syracuseStep 2701777 = 2026333) B2026333
theorem B3602369 : Blo 1897435 3602369 := bstep (se 2 (by rfl) ⟨1350888, by rfl⟩ : syracuseStep 3602369 = 2701777) B2701777
theorem B2401579 : Blo 1897435 2401579 := bstep (se 1 (by rfl) ⟨1801184, by rfl⟩ : syracuseStep 2401579 = 3602369) B3602369
theorem B3202105 : Blo 1897435 3202105 := bstep (se 2 (by rfl) ⟨1200789, by rfl⟩ : syracuseStep 3202105 = 2401579) B2401579
theorem B4269473 : Blo 1897435 4269473 := bstep (se 2 (by rfl) ⟨1601052, by rfl⟩ : syracuseStep 4269473 = 3202105) B3202105
theorem B2846315 : Blo 1897435 2846315 := bstep (se 1 (by rfl) ⟨2134736, by rfl⟩ : syracuseStep 2846315 = 4269473) B4269473
theorem B1897543 : Blo 1897435 1897543 := bstep (se 1 (by rfl) ⟨1423157, by rfl⟩ : syracuseStep 1897543 = 2846315) B2846315
theorem B2134741 : Blo 1897435 2134741 := bbase (se 7 (by rfl) ⟨25016, by rfl⟩ : syracuseStep 2134741 = 50033) (by norm_num)
theorem B2846321 : Blo 1897435 2846321 := bstep (se 2 (by rfl) ⟨1067370, by rfl⟩ : syracuseStep 2846321 = 2134741) B2134741
theorem B1897547 : Blo 1897435 1897547 := bstep (se 1 (by rfl) ⟨1423160, by rfl⟩ : syracuseStep 1897547 = 2846321) B2846321
theorem B2401589 : Blo 1897435 2401589 := bbase (se 5 (by rfl) ⟨112574, by rfl⟩ : syracuseStep 2401589 = 225149) (by norm_num)
theorem B6404237 : Blo 1897435 6404237 := bstep (se 3 (by rfl) ⟨1200794, by rfl⟩ : syracuseStep 6404237 = 2401589) B2401589
theorem B4269491 : Blo 1897435 4269491 := bstep (se 1 (by rfl) ⟨3202118, by rfl⟩ : syracuseStep 4269491 = 6404237) B6404237
theorem B2846327 : Blo 1897435 2846327 := bstep (se 1 (by rfl) ⟨2134745, by rfl⟩ : syracuseStep 2846327 = 4269491) B4269491
theorem B1897551 : Blo 1897435 1897551 := bstep (se 1 (by rfl) ⟨1423163, by rfl⟩ : syracuseStep 1897551 = 2846327) B2846327
theorem B2846333 : Blo 1897435 2846333 := bbase (se 3 (by rfl) ⟨533687, by rfl⟩ : syracuseStep 2846333 = 1067375) (by norm_num)
theorem B1897555 : Blo 1897435 1897555 := bstep (se 1 (by rfl) ⟨1423166, by rfl⟩ : syracuseStep 1897555 = 2846333) B2846333
theorem B4269509 : Blo 1897435 4269509 := bbase (se 4 (by rfl) ⟨400266, by rfl⟩ : syracuseStep 4269509 = 800533) (by norm_num)
theorem B2846339 : Blo 1897435 2846339 := bstep (se 1 (by rfl) ⟨2134754, by rfl⟩ : syracuseStep 2846339 = 4269509) B4269509
theorem B1897559 : Blo 1897435 1897559 := bstep (se 1 (by rfl) ⟨1423169, by rfl⟩ : syracuseStep 1897559 = 2846339) B2846339
theorem B2564605 : Blo 1897435 2564605 := bbase (se 3 (by rfl) ⟨480863, by rfl⟩ : syracuseStep 2564605 = 961727) (by norm_num)
theorem B13677893 : Blo 1897435 13677893 := bstep (se 4 (by rfl) ⟨1282302, by rfl⟩ : syracuseStep 13677893 = 2564605) B2564605
theorem B9118595 : Blo 1897435 9118595 := bstep (se 1 (by rfl) ⟨6838946, by rfl⟩ : syracuseStep 9118595 = 13677893) B13677893
theorem B6079063 : Blo 1897435 6079063 := bstep (se 1 (by rfl) ⟨4559297, by rfl⟩ : syracuseStep 6079063 = 9118595) B9118595
theorem B8105417 : Blo 1897435 8105417 := bstep (se 2 (by rfl) ⟨3039531, by rfl⟩ : syracuseStep 8105417 = 6079063) B6079063
theorem B5403611 : Blo 1897435 5403611 := bstep (se 1 (by rfl) ⟨4052708, by rfl⟩ : syracuseStep 5403611 = 8105417) B8105417
theorem B3602407 : Blo 1897435 3602407 := bstep (se 1 (by rfl) ⟨2701805, by rfl⟩ : syracuseStep 3602407 = 5403611) B5403611
theorem B4803209 : Blo 1897435 4803209 := bstep (se 2 (by rfl) ⟨1801203, by rfl⟩ : syracuseStep 4803209 = 3602407) B3602407
theorem B3202139 : Blo 1897435 3202139 := bstep (se 1 (by rfl) ⟨2401604, by rfl⟩ : syracuseStep 3202139 = 4803209) B4803209
theorem B2134759 : Blo 1897435 2134759 := bstep (se 1 (by rfl) ⟨1601069, by rfl⟩ : syracuseStep 2134759 = 3202139) B3202139
theorem B2846345 : Blo 1897435 2846345 := bstep (se 2 (by rfl) ⟨1067379, by rfl⟩ : syracuseStep 2846345 = 2134759) B2134759
theorem B1897563 : Blo 1897435 1897563 := bstep (se 1 (by rfl) ⟨1423172, by rfl⟩ : syracuseStep 1897563 = 2846345) B2846345
theorem B9606437 : Blo 1897435 9606437 := bbase (se 4 (by rfl) ⟨900603, by rfl⟩ : syracuseStep 9606437 = 1801207) (by norm_num)
theorem B6404291 : Blo 1897435 6404291 := bstep (se 1 (by rfl) ⟨4803218, by rfl⟩ : syracuseStep 6404291 = 9606437) B9606437
theorem B4269527 : Blo 1897435 4269527 := bstep (se 1 (by rfl) ⟨3202145, by rfl⟩ : syracuseStep 4269527 = 6404291) B6404291
theorem B2846351 : Blo 1897435 2846351 := bstep (se 1 (by rfl) ⟨2134763, by rfl⟩ : syracuseStep 2846351 = 4269527) B4269527
theorem B1897567 : Blo 1897435 1897567 := bstep (se 1 (by rfl) ⟨1423175, by rfl⟩ : syracuseStep 1897567 = 2846351) B2846351
theorem B2846357 : Blo 1897435 2846357 := bbase (se 6 (by rfl) ⟨66711, by rfl⟩ : syracuseStep 2846357 = 133423) (by norm_num)
theorem B1897571 : Blo 1897435 1897571 := bstep (se 1 (by rfl) ⟨1423178, by rfl⟩ : syracuseStep 1897571 = 2846357) B2846357
theorem B3651581 : Blo 1897435 3651581 := bbase (se 3 (by rfl) ⟨684671, by rfl⟩ : syracuseStep 3651581 = 1369343) (by norm_num)
theorem B2434387 : Blo 1897435 2434387 := bstep (se 1 (by rfl) ⟨1825790, by rfl⟩ : syracuseStep 2434387 = 3651581) B3651581
theorem B3245849 : Blo 1897435 3245849 := bstep (se 2 (by rfl) ⟨1217193, by rfl⟩ : syracuseStep 3245849 = 2434387) B2434387
theorem B2163899 : Blo 1897435 2163899 := bstep (se 1 (by rfl) ⟨1622924, by rfl⟩ : syracuseStep 2163899 = 3245849) B3245849
theorem B5770397 : Blo 1897435 5770397 := bstep (se 3 (by rfl) ⟨1081949, by rfl⟩ : syracuseStep 5770397 = 2163899) B2163899
theorem B15387725 : Blo 1897435 15387725 := bstep (se 3 (by rfl) ⟨2885198, by rfl⟩ : syracuseStep 15387725 = 5770397) B5770397
theorem B10258483 : Blo 1897435 10258483 := bstep (se 1 (by rfl) ⟨7693862, by rfl⟩ : syracuseStep 10258483 = 15387725) B15387725
theorem B13677977 : Blo 1897435 13677977 := bstep (se 2 (by rfl) ⟨5129241, by rfl⟩ : syracuseStep 13677977 = 10258483) B10258483
theorem B9118651 : Blo 1897435 9118651 := bstep (se 1 (by rfl) ⟨6838988, by rfl⟩ : syracuseStep 9118651 = 13677977) B13677977
theorem B12158201 : Blo 1897435 12158201 := bstep (se 2 (by rfl) ⟨4559325, by rfl⟩ : syracuseStep 12158201 = 9118651) B9118651
theorem B8105467 : Blo 1897435 8105467 := bstep (se 1 (by rfl) ⟨6079100, by rfl⟩ : syracuseStep 8105467 = 12158201) B12158201
theorem B10807289 : Blo 1897435 10807289 := bstep (se 2 (by rfl) ⟨4052733, by rfl⟩ : syracuseStep 10807289 = 8105467) B8105467
theorem B7204859 : Blo 1897435 7204859 := bstep (se 1 (by rfl) ⟨5403644, by rfl⟩ : syracuseStep 7204859 = 10807289) B10807289
theorem B4803239 : Blo 1897435 4803239 := bstep (se 1 (by rfl) ⟨3602429, by rfl⟩ : syracuseStep 4803239 = 7204859) B7204859
theorem B3202159 : Blo 1897435 3202159 := bstep (se 1 (by rfl) ⟨2401619, by rfl⟩ : syracuseStep 3202159 = 4803239) B4803239
theorem B4269545 : Blo 1897435 4269545 := bstep (se 2 (by rfl) ⟨1601079, by rfl⟩ : syracuseStep 4269545 = 3202159) B3202159
theorem B2846363 : Blo 1897435 2846363 := bstep (se 1 (by rfl) ⟨2134772, by rfl⟩ : syracuseStep 2846363 = 4269545) B4269545
theorem B1897575 : Blo 1897435 1897575 := bstep (se 1 (by rfl) ⟨1423181, by rfl⟩ : syracuseStep 1897575 = 2846363) B2846363
theorem B2134777 : Blo 1897435 2134777 := bbase (se 2 (by rfl) ⟨800541, by rfl⟩ : syracuseStep 2134777 = 1601083) (by norm_num)
theorem B2846369 : Blo 1897435 2846369 := bstep (se 2 (by rfl) ⟨1067388, by rfl⟩ : syracuseStep 2846369 = 2134777) B2134777
theorem B1897579 : Blo 1897435 1897579 := bstep (se 1 (by rfl) ⟨1423184, by rfl⟩ : syracuseStep 1897579 = 2846369) B2846369
theorem B3419509 : Blo 1897435 3419509 := bbase (se 5 (by rfl) ⟨160289, by rfl⟩ : syracuseStep 3419509 = 320579) (by norm_num)
theorem B4559345 : Blo 1897435 4559345 := bstep (se 2 (by rfl) ⟨1709754, by rfl⟩ : syracuseStep 4559345 = 3419509) B3419509
theorem B3039563 : Blo 1897435 3039563 := bstep (se 1 (by rfl) ⟨2279672, by rfl⟩ : syracuseStep 3039563 = 4559345) B4559345
theorem B8105501 : Blo 1897435 8105501 := bstep (se 3 (by rfl) ⟨1519781, by rfl⟩ : syracuseStep 8105501 = 3039563) B3039563
theorem B5403667 : Blo 1897435 5403667 := bstep (se 1 (by rfl) ⟨4052750, by rfl⟩ : syracuseStep 5403667 = 8105501) B8105501
theorem B7204889 : Blo 1897435 7204889 := bstep (se 2 (by rfl) ⟨2701833, by rfl⟩ : syracuseStep 7204889 = 5403667) B5403667
theorem B4803259 : Blo 1897435 4803259 := bstep (se 1 (by rfl) ⟨3602444, by rfl⟩ : syracuseStep 4803259 = 7204889) B7204889
theorem B6404345 : Blo 1897435 6404345 := bstep (se 2 (by rfl) ⟨2401629, by rfl⟩ : syracuseStep 6404345 = 4803259) B4803259
theorem B4269563 : Blo 1897435 4269563 := bstep (se 1 (by rfl) ⟨3202172, by rfl⟩ : syracuseStep 4269563 = 6404345) B6404345
theorem B2846375 : Blo 1897435 2846375 := bstep (se 1 (by rfl) ⟨2134781, by rfl⟩ : syracuseStep 2846375 = 4269563) B4269563
theorem B1897583 : Blo 1897435 1897583 := bstep (se 1 (by rfl) ⟨1423187, by rfl⟩ : syracuseStep 1897583 = 2846375) B2846375
theorem B2846381 : Blo 1897435 2846381 := bbase (se 3 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 2846381 = 1067393) (by norm_num)
theorem B1897587 : Blo 1897435 1897587 := bstep (se 1 (by rfl) ⟨1423190, by rfl⟩ : syracuseStep 1897587 = 2846381) B2846381
theorem B4269581 : Blo 1897435 4269581 := bbase (se 3 (by rfl) ⟨800546, by rfl⟩ : syracuseStep 4269581 = 1601093) (by norm_num)
theorem B2846387 : Blo 1897435 2846387 := bstep (se 1 (by rfl) ⟨2134790, by rfl⟩ : syracuseStep 2846387 = 4269581) B4269581
theorem B1897591 : Blo 1897435 1897591 := bstep (se 1 (by rfl) ⟨1423193, by rfl⟩ : syracuseStep 1897591 = 2846387) B2846387
theorem B2401645 : Blo 1897435 2401645 := bbase (se 3 (by rfl) ⟨450308, by rfl⟩ : syracuseStep 2401645 = 900617) (by norm_num)
theorem B3202193 : Blo 1897435 3202193 := bstep (se 2 (by rfl) ⟨1200822, by rfl⟩ : syracuseStep 3202193 = 2401645) B2401645
theorem B2134795 : Blo 1897435 2134795 := bstep (se 1 (by rfl) ⟨1601096, by rfl⟩ : syracuseStep 2134795 = 3202193) B3202193
theorem B2846393 : Blo 1897435 2846393 := bstep (se 2 (by rfl) ⟨1067397, by rfl⟩ : syracuseStep 2846393 = 2134795) B2134795
theorem B1897595 : Blo 1897435 1897595 := bstep (se 1 (by rfl) ⟨1423196, by rfl⟩ : syracuseStep 1897595 = 2846393) B2846393
theorem B2564653 : Blo 1897435 2564653 := bbase (se 3 (by rfl) ⟨480872, by rfl⟩ : syracuseStep 2564653 = 961745) (by norm_num)
theorem B3419537 : Blo 1897435 3419537 := bstep (se 2 (by rfl) ⟨1282326, by rfl⟩ : syracuseStep 3419537 = 2564653) B2564653
theorem B9118765 : Blo 1897435 9118765 := bstep (se 3 (by rfl) ⟨1709768, by rfl⟩ : syracuseStep 9118765 = 3419537) B3419537
theorem B12158353 : Blo 1897435 12158353 := bstep (se 2 (by rfl) ⟨4559382, by rfl⟩ : syracuseStep 12158353 = 9118765) B9118765
theorem B16211137 : Blo 1897435 16211137 := bstep (se 2 (by rfl) ⟨6079176, by rfl⟩ : syracuseStep 16211137 = 12158353) B12158353
theorem B21614849 : Blo 1897435 21614849 := bstep (se 2 (by rfl) ⟨8105568, by rfl⟩ : syracuseStep 21614849 = 16211137) B16211137
theorem B14409899 : Blo 1897435 14409899 := bstep (se 1 (by rfl) ⟨10807424, by rfl⟩ : syracuseStep 14409899 = 21614849) B21614849
theorem B9606599 : Blo 1897435 9606599 := bstep (se 1 (by rfl) ⟨7204949, by rfl⟩ : syracuseStep 9606599 = 14409899) B14409899
theorem B6404399 : Blo 1897435 6404399 := bstep (se 1 (by rfl) ⟨4803299, by rfl⟩ : syracuseStep 6404399 = 9606599) B9606599
theorem B4269599 : Blo 1897435 4269599 := bstep (se 1 (by rfl) ⟨3202199, by rfl⟩ : syracuseStep 4269599 = 6404399) B6404399
theorem B2846399 : Blo 1897435 2846399 := bstep (se 1 (by rfl) ⟨2134799, by rfl⟩ : syracuseStep 2846399 = 4269599) B4269599
theorem B1897599 : Blo 1897435 1897599 := bstep (se 1 (by rfl) ⟨1423199, by rfl⟩ : syracuseStep 1897599 = 2846399) B2846399
theorem B2846405 : Blo 1897435 2846405 := bbase (se 4 (by rfl) ⟨266850, by rfl⟩ : syracuseStep 2846405 = 533701) (by norm_num)
theorem B1897603 : Blo 1897435 1897603 := bstep (se 1 (by rfl) ⟨1423202, by rfl⟩ : syracuseStep 1897603 = 2846405) B2846405
theorem B3202213 : Blo 1897435 3202213 := bbase (se 4 (by rfl) ⟨300207, by rfl⟩ : syracuseStep 3202213 = 600415) (by norm_num)
theorem B4269617 : Blo 1897435 4269617 := bstep (se 2 (by rfl) ⟨1601106, by rfl⟩ : syracuseStep 4269617 = 3202213) B3202213
theorem B2846411 : Blo 1897435 2846411 := bstep (se 1 (by rfl) ⟨2134808, by rfl⟩ : syracuseStep 2846411 = 4269617) B4269617
theorem B1897607 : Blo 1897435 1897607 := bstep (se 1 (by rfl) ⟨1423205, by rfl⟩ : syracuseStep 1897607 = 2846411) B2846411
theorem B2134813 : Blo 1897435 2134813 := bbase (se 3 (by rfl) ⟨400277, by rfl⟩ : syracuseStep 2134813 = 800555) (by norm_num)
theorem B2846417 : Blo 1897435 2846417 := bstep (se 2 (by rfl) ⟨1067406, by rfl⟩ : syracuseStep 2846417 = 2134813) B2134813
theorem B1897611 : Blo 1897435 1897611 := bstep (se 1 (by rfl) ⟨1423208, by rfl⟩ : syracuseStep 1897611 = 2846417) B2846417
theorem B6404453 : Blo 1897435 6404453 := bbase (se 4 (by rfl) ⟨600417, by rfl⟩ : syracuseStep 6404453 = 1200835) (by norm_num)
theorem B4269635 : Blo 1897435 4269635 := bstep (se 1 (by rfl) ⟨3202226, by rfl⟩ : syracuseStep 4269635 = 6404453) B6404453
theorem B2846423 : Blo 1897435 2846423 := bstep (se 1 (by rfl) ⟨2134817, by rfl⟩ : syracuseStep 2846423 = 4269635) B4269635
theorem B1897615 : Blo 1897435 1897615 := bstep (se 1 (by rfl) ⟨1423211, by rfl⟩ : syracuseStep 1897615 = 2846423) B2846423
theorem B2846429 : Blo 1897435 2846429 := bbase (se 3 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 2846429 = 1067411) (by norm_num)
theorem B1897619 : Blo 1897435 1897619 := bstep (se 1 (by rfl) ⟨1423214, by rfl⟩ : syracuseStep 1897619 = 2846429) B2846429
theorem B4269653 : Blo 1897435 4269653 := bbase (se 8 (by rfl) ⟨25017, by rfl⟩ : syracuseStep 4269653 = 50035) (by norm_num)
theorem B2846435 : Blo 1897435 2846435 := bstep (se 1 (by rfl) ⟨2134826, by rfl⟩ : syracuseStep 2846435 = 4269653) B4269653
theorem B1897623 : Blo 1897435 1897623 := bstep (se 1 (by rfl) ⟨1423217, by rfl⟩ : syracuseStep 1897623 = 2846435) B2846435
theorem B4052845 : Blo 1897435 4052845 := bbase (se 3 (by rfl) ⟨759908, by rfl⟩ : syracuseStep 4052845 = 1519817) (by norm_num)
theorem B5403793 : Blo 1897435 5403793 := bstep (se 2 (by rfl) ⟨2026422, by rfl⟩ : syracuseStep 5403793 = 4052845) B4052845
theorem B7205057 : Blo 1897435 7205057 := bstep (se 2 (by rfl) ⟨2701896, by rfl⟩ : syracuseStep 7205057 = 5403793) B5403793
theorem B4803371 : Blo 1897435 4803371 := bstep (se 1 (by rfl) ⟨3602528, by rfl⟩ : syracuseStep 4803371 = 7205057) B7205057
theorem B3202247 : Blo 1897435 3202247 := bstep (se 1 (by rfl) ⟨2401685, by rfl⟩ : syracuseStep 3202247 = 4803371) B4803371
theorem B2134831 : Blo 1897435 2134831 := bstep (se 1 (by rfl) ⟨1601123, by rfl⟩ : syracuseStep 2134831 = 3202247) B3202247
theorem B2846441 : Blo 1897435 2846441 := bstep (se 2 (by rfl) ⟨1067415, by rfl⟩ : syracuseStep 2846441 = 2134831) B2134831
theorem B1897627 : Blo 1897435 1897627 := bstep (se 1 (by rfl) ⟨1423220, by rfl⟩ : syracuseStep 1897627 = 2846441) B2846441
theorem B4327925 : Blo 1897435 4327925 := bbase (se 5 (by rfl) ⟨202871, by rfl⟩ : syracuseStep 4327925 = 405743) (by norm_num)
theorem B11541133 : Blo 1897435 11541133 := bstep (se 3 (by rfl) ⟨2163962, by rfl⟩ : syracuseStep 11541133 = 4327925) B4327925
theorem B15388177 : Blo 1897435 15388177 := bstep (se 2 (by rfl) ⟨5770566, by rfl⟩ : syracuseStep 15388177 = 11541133) B11541133
theorem B20517569 : Blo 1897435 20517569 := bstep (se 2 (by rfl) ⟨7694088, by rfl⟩ : syracuseStep 20517569 = 15388177) B15388177
theorem B13678379 : Blo 1897435 13678379 := bstep (se 1 (by rfl) ⟨10258784, by rfl⟩ : syracuseStep 13678379 = 20517569) B20517569
theorem B9118919 : Blo 1897435 9118919 := bstep (se 1 (by rfl) ⟨6839189, by rfl⟩ : syracuseStep 9118919 = 13678379) B13678379
theorem B24317117 : Blo 1897435 24317117 := bstep (se 3 (by rfl) ⟨4559459, by rfl⟩ : syracuseStep 24317117 = 9118919) B9118919
theorem B16211411 : Blo 1897435 16211411 := bstep (se 1 (by rfl) ⟨12158558, by rfl⟩ : syracuseStep 16211411 = 24317117) B24317117
theorem B10807607 : Blo 1897435 10807607 := bstep (se 1 (by rfl) ⟨8105705, by rfl⟩ : syracuseStep 10807607 = 16211411) B16211411
theorem B7205071 : Blo 1897435 7205071 := bstep (se 1 (by rfl) ⟨5403803, by rfl⟩ : syracuseStep 7205071 = 10807607) B10807607
theorem B9606761 : Blo 1897435 9606761 := bstep (se 2 (by rfl) ⟨3602535, by rfl⟩ : syracuseStep 9606761 = 7205071) B7205071
theorem B6404507 : Blo 1897435 6404507 := bstep (se 1 (by rfl) ⟨4803380, by rfl⟩ : syracuseStep 6404507 = 9606761) B9606761
theorem B4269671 : Blo 1897435 4269671 := bstep (se 1 (by rfl) ⟨3202253, by rfl⟩ : syracuseStep 4269671 = 6404507) B6404507
theorem B2846447 : Blo 1897435 2846447 := bstep (se 1 (by rfl) ⟨2134835, by rfl⟩ : syracuseStep 2846447 = 4269671) B4269671
theorem B1897631 : Blo 1897435 1897631 := bstep (se 1 (by rfl) ⟨1423223, by rfl⟩ : syracuseStep 1897631 = 2846447) B2846447
theorem B2846453 : Blo 1897435 2846453 := bbase (se 5 (by rfl) ⟨133427, by rfl⟩ : syracuseStep 2846453 = 266855) (by norm_num)
theorem B1897635 : Blo 1897435 1897635 := bstep (se 1 (by rfl) ⟨1423226, by rfl⟩ : syracuseStep 1897635 = 2846453) B2846453
theorem B3039653 : Blo 1897435 3039653 := bbase (se 4 (by rfl) ⟨284967, by rfl⟩ : syracuseStep 3039653 = 569935) (by norm_num)
theorem B8105741 : Blo 1897435 8105741 := bstep (se 3 (by rfl) ⟨1519826, by rfl⟩ : syracuseStep 8105741 = 3039653) B3039653
theorem B5403827 : Blo 1897435 5403827 := bstep (se 1 (by rfl) ⟨4052870, by rfl⟩ : syracuseStep 5403827 = 8105741) B8105741
theorem B3602551 : Blo 1897435 3602551 := bstep (se 1 (by rfl) ⟨2701913, by rfl⟩ : syracuseStep 3602551 = 5403827) B5403827
theorem B4803401 : Blo 1897435 4803401 := bstep (se 2 (by rfl) ⟨1801275, by rfl⟩ : syracuseStep 4803401 = 3602551) B3602551
theorem B3202267 : Blo 1897435 3202267 := bstep (se 1 (by rfl) ⟨2401700, by rfl⟩ : syracuseStep 3202267 = 4803401) B4803401
theorem B4269689 : Blo 1897435 4269689 := bstep (se 2 (by rfl) ⟨1601133, by rfl⟩ : syracuseStep 4269689 = 3202267) B3202267
theorem B2846459 : Blo 1897435 2846459 := bstep (se 1 (by rfl) ⟨2134844, by rfl⟩ : syracuseStep 2846459 = 4269689) B4269689
theorem B1897639 : Blo 1897435 1897639 := bstep (se 1 (by rfl) ⟨1423229, by rfl⟩ : syracuseStep 1897639 = 2846459) B2846459
theorem B2134849 : Blo 1897435 2134849 := bbase (se 2 (by rfl) ⟨800568, by rfl⟩ : syracuseStep 2134849 = 1601137) (by norm_num)
theorem B2846465 : Blo 1897435 2846465 := bstep (se 2 (by rfl) ⟨1067424, by rfl⟩ : syracuseStep 2846465 = 2134849) B2134849
theorem B1897643 : Blo 1897435 1897643 := bstep (se 1 (by rfl) ⟨1423232, by rfl⟩ : syracuseStep 1897643 = 2846465) B2846465
theorem B4803421 : Blo 1897435 4803421 := bbase (se 3 (by rfl) ⟨900641, by rfl⟩ : syracuseStep 4803421 = 1801283) (by norm_num)
theorem B6404561 : Blo 1897435 6404561 := bstep (se 2 (by rfl) ⟨2401710, by rfl⟩ : syracuseStep 6404561 = 4803421) B4803421
theorem B4269707 : Blo 1897435 4269707 := bstep (se 1 (by rfl) ⟨3202280, by rfl⟩ : syracuseStep 4269707 = 6404561) B6404561
theorem B2846471 : Blo 1897435 2846471 := bstep (se 1 (by rfl) ⟨2134853, by rfl⟩ : syracuseStep 2846471 = 4269707) B4269707
theorem B1897647 : Blo 1897435 1897647 := bstep (se 1 (by rfl) ⟨1423235, by rfl⟩ : syracuseStep 1897647 = 2846471) B2846471
theorem B2846477 : Blo 1897435 2846477 := bbase (se 3 (by rfl) ⟨533714, by rfl⟩ : syracuseStep 2846477 = 1067429) (by norm_num)
theorem B1897651 : Blo 1897435 1897651 := bstep (se 1 (by rfl) ⟨1423238, by rfl⟩ : syracuseStep 1897651 = 2846477) B2846477
theorem B4269725 : Blo 1897435 4269725 := bbase (se 3 (by rfl) ⟨800573, by rfl⟩ : syracuseStep 4269725 = 1601147) (by norm_num)
theorem B2846483 : Blo 1897435 2846483 := bstep (se 1 (by rfl) ⟨2134862, by rfl⟩ : syracuseStep 2846483 = 4269725) B4269725
theorem B1897655 : Blo 1897435 1897655 := bstep (se 1 (by rfl) ⟨1423241, by rfl⟩ : syracuseStep 1897655 = 2846483) B2846483
theorem B3202301 : Blo 1897435 3202301 := bbase (se 3 (by rfl) ⟨600431, by rfl⟩ : syracuseStep 3202301 = 1200863) (by norm_num)
theorem B2134867 : Blo 1897435 2134867 := bstep (se 1 (by rfl) ⟨1601150, by rfl⟩ : syracuseStep 2134867 = 3202301) B3202301
theorem B2846489 : Blo 1897435 2846489 := bstep (se 2 (by rfl) ⟨1067433, by rfl⟩ : syracuseStep 2846489 = 2134867) B2134867
theorem B1897659 : Blo 1897435 1897659 := bstep (se 1 (by rfl) ⟨1423244, by rfl⟩ : syracuseStep 1897659 = 2846489) B2846489
theorem B3419653 : Blo 1897435 3419653 := bbase (se 4 (by rfl) ⟨320592, by rfl⟩ : syracuseStep 3419653 = 641185) (by norm_num)
theorem B4559537 : Blo 1897435 4559537 := bstep (se 2 (by rfl) ⟨1709826, by rfl⟩ : syracuseStep 4559537 = 3419653) B3419653
theorem B3039691 : Blo 1897435 3039691 := bstep (se 1 (by rfl) ⟨2279768, by rfl⟩ : syracuseStep 3039691 = 4559537) B4559537
theorem B4052921 : Blo 1897435 4052921 := bstep (se 2 (by rfl) ⟨1519845, by rfl⟩ : syracuseStep 4052921 = 3039691) B3039691
theorem B10807789 : Blo 1897435 10807789 := bstep (se 3 (by rfl) ⟨2026460, by rfl⟩ : syracuseStep 10807789 = 4052921) B4052921
theorem B14410385 : Blo 1897435 14410385 := bstep (se 2 (by rfl) ⟨5403894, by rfl⟩ : syracuseStep 14410385 = 10807789) B10807789
theorem B9606923 : Blo 1897435 9606923 := bstep (se 1 (by rfl) ⟨7205192, by rfl⟩ : syracuseStep 9606923 = 14410385) B14410385
theorem B6404615 : Blo 1897435 6404615 := bstep (se 1 (by rfl) ⟨4803461, by rfl⟩ : syracuseStep 6404615 = 9606923) B9606923
theorem B4269743 : Blo 1897435 4269743 := bstep (se 1 (by rfl) ⟨3202307, by rfl⟩ : syracuseStep 4269743 = 6404615) B6404615
theorem B2846495 : Blo 1897435 2846495 := bstep (se 1 (by rfl) ⟨2134871, by rfl⟩ : syracuseStep 2846495 = 4269743) B4269743
theorem B1897663 : Blo 1897435 1897663 := bstep (se 1 (by rfl) ⟨1423247, by rfl⟩ : syracuseStep 1897663 = 2846495) B2846495
theorem B2846501 : Blo 1897435 2846501 := bbase (se 4 (by rfl) ⟨266859, by rfl⟩ : syracuseStep 2846501 = 533719) (by norm_num)
theorem B1897667 : Blo 1897435 1897667 := bstep (se 1 (by rfl) ⟨1423250, by rfl⟩ : syracuseStep 1897667 = 2846501) B2846501
theorem B2401741 : Blo 1897435 2401741 := bbase (se 3 (by rfl) ⟨450326, by rfl⟩ : syracuseStep 2401741 = 900653) (by norm_num)
theorem B3202321 : Blo 1897435 3202321 := bstep (se 2 (by rfl) ⟨1200870, by rfl⟩ : syracuseStep 3202321 = 2401741) B2401741
theorem B4269761 : Blo 1897435 4269761 := bstep (se 2 (by rfl) ⟨1601160, by rfl⟩ : syracuseStep 4269761 = 3202321) B3202321
theorem B2846507 : Blo 1897435 2846507 := bstep (se 1 (by rfl) ⟨2134880, by rfl⟩ : syracuseStep 2846507 = 4269761) B4269761
theorem B1897671 : Blo 1897435 1897671 := bstep (se 1 (by rfl) ⟨1423253, by rfl⟩ : syracuseStep 1897671 = 2846507) B2846507
theorem B2134885 : Blo 1897435 2134885 := bbase (se 4 (by rfl) ⟨200145, by rfl⟩ : syracuseStep 2134885 = 400291) (by norm_num)
theorem B2846513 : Blo 1897435 2846513 := bstep (se 2 (by rfl) ⟨1067442, by rfl⟩ : syracuseStep 2846513 = 2134885) B2134885
theorem B1897675 : Blo 1897435 1897675 := bstep (se 1 (by rfl) ⟨1423256, by rfl⟩ : syracuseStep 1897675 = 2846513) B2846513
theorem B5403941 : Blo 1897435 5403941 := bbase (se 4 (by rfl) ⟨506619, by rfl⟩ : syracuseStep 5403941 = 1013239) (by norm_num)
theorem B3602627 : Blo 1897435 3602627 := bstep (se 1 (by rfl) ⟨2701970, by rfl⟩ : syracuseStep 3602627 = 5403941) B5403941
theorem B2401751 : Blo 1897435 2401751 := bstep (se 1 (by rfl) ⟨1801313, by rfl⟩ : syracuseStep 2401751 = 3602627) B3602627
theorem B6404669 : Blo 1897435 6404669 := bstep (se 3 (by rfl) ⟨1200875, by rfl⟩ : syracuseStep 6404669 = 2401751) B2401751
theorem B4269779 : Blo 1897435 4269779 := bstep (se 1 (by rfl) ⟨3202334, by rfl⟩ : syracuseStep 4269779 = 6404669) B6404669
theorem B2846519 : Blo 1897435 2846519 := bstep (se 1 (by rfl) ⟨2134889, by rfl⟩ : syracuseStep 2846519 = 4269779) B4269779
theorem B1897679 : Blo 1897435 1897679 := bstep (se 1 (by rfl) ⟨1423259, by rfl⟩ : syracuseStep 1897679 = 2846519) B2846519
theorem B2846525 : Blo 1897435 2846525 := bbase (se 3 (by rfl) ⟨533723, by rfl⟩ : syracuseStep 2846525 = 1067447) (by norm_num)
theorem B1897683 : Blo 1897435 1897683 := bstep (se 1 (by rfl) ⟨1423262, by rfl⟩ : syracuseStep 1897683 = 2846525) B2846525
theorem B4269797 : Blo 1897435 4269797 := bbase (se 4 (by rfl) ⟨400293, by rfl⟩ : syracuseStep 4269797 = 800587) (by norm_num)
theorem B2846531 : Blo 1897435 2846531 := bstep (se 1 (by rfl) ⟨2134898, by rfl⟩ : syracuseStep 2846531 = 4269797) B4269797
theorem B1897687 : Blo 1897435 1897687 := bstep (se 1 (by rfl) ⟨1423265, by rfl⟩ : syracuseStep 1897687 = 2846531) B2846531
theorem B4803533 : Blo 1897435 4803533 := bbase (se 3 (by rfl) ⟨900662, by rfl⟩ : syracuseStep 4803533 = 1801325) (by norm_num)
theorem B3202355 : Blo 1897435 3202355 := bstep (se 1 (by rfl) ⟨2401766, by rfl⟩ : syracuseStep 3202355 = 4803533) B4803533
theorem B2134903 : Blo 1897435 2134903 := bstep (se 1 (by rfl) ⟨1601177, by rfl⟩ : syracuseStep 2134903 = 3202355) B3202355
theorem B2846537 : Blo 1897435 2846537 := bstep (se 2 (by rfl) ⟨1067451, by rfl⟩ : syracuseStep 2846537 = 2134903) B2134903
theorem B1897691 : Blo 1897435 1897691 := bstep (se 1 (by rfl) ⟨1423268, by rfl⟩ : syracuseStep 1897691 = 2846537) B2846537
theorem B8774245 : Blo 1897435 8774245 := bbase (se 4 (by rfl) ⟨822585, by rfl⟩ : syracuseStep 8774245 = 1645171) (by norm_num)
theorem B11698993 : Blo 1897435 11698993 := bstep (se 2 (by rfl) ⟨4387122, by rfl⟩ : syracuseStep 11698993 = 8774245) B8774245
theorem B15598657 : Blo 1897435 15598657 := bstep (se 2 (by rfl) ⟨5849496, by rfl⟩ : syracuseStep 15598657 = 11698993) B11698993
theorem B20798209 : Blo 1897435 20798209 := bstep (se 2 (by rfl) ⟨7799328, by rfl⟩ : syracuseStep 20798209 = 15598657) B15598657
theorem B27730945 : Blo 1897435 27730945 := bstep (se 2 (by rfl) ⟨10399104, by rfl⟩ : syracuseStep 27730945 = 20798209) B20798209
theorem B36974593 : Blo 1897435 36974593 := bstep (se 2 (by rfl) ⟨13865472, by rfl⟩ : syracuseStep 36974593 = 27730945) B27730945
theorem B49299457 : Blo 1897435 49299457 := bstep (se 2 (by rfl) ⟨18487296, by rfl⟩ : syracuseStep 49299457 = 36974593) B36974593
theorem B65732609 : Blo 1897435 65732609 := bstep (se 2 (by rfl) ⟨24649728, by rfl⟩ : syracuseStep 65732609 = 49299457) B49299457
theorem B43821739 : Blo 1897435 43821739 := bstep (se 1 (by rfl) ⟨32866304, by rfl⟩ : syracuseStep 43821739 = 65732609) B65732609
theorem B58428985 : Blo 1897435 58428985 := bstep (se 2 (by rfl) ⟨21910869, by rfl⟩ : syracuseStep 58428985 = 43821739) B43821739
theorem B77905313 : Blo 1897435 77905313 := bstep (se 2 (by rfl) ⟨29214492, by rfl⟩ : syracuseStep 77905313 = 58428985) B58428985
theorem B51936875 : Blo 1897435 51936875 := bstep (se 1 (by rfl) ⟨38952656, by rfl⟩ : syracuseStep 51936875 = 77905313) B77905313
theorem B34624583 : Blo 1897435 34624583 := bstep (se 1 (by rfl) ⟨25968437, by rfl⟩ : syracuseStep 34624583 = 51936875) B51936875
theorem B23083055 : Blo 1897435 23083055 := bstep (se 1 (by rfl) ⟨17312291, by rfl⟩ : syracuseStep 23083055 = 34624583) B34624583
theorem B15388703 : Blo 1897435 15388703 := bstep (se 1 (by rfl) ⟨11541527, by rfl⟩ : syracuseStep 15388703 = 23083055) B23083055
theorem B10259135 : Blo 1897435 10259135 := bstep (se 1 (by rfl) ⟨7694351, by rfl⟩ : syracuseStep 10259135 = 15388703) B15388703
theorem B6839423 : Blo 1897435 6839423 := bstep (se 1 (by rfl) ⟨5129567, by rfl⟩ : syracuseStep 6839423 = 10259135) B10259135
theorem B4559615 : Blo 1897435 4559615 := bstep (se 1 (by rfl) ⟨3419711, by rfl⟩ : syracuseStep 4559615 = 6839423) B6839423
theorem B3039743 : Blo 1897435 3039743 := bstep (se 1 (by rfl) ⟨2279807, by rfl⟩ : syracuseStep 3039743 = 4559615) B4559615
theorem B2026495 : Blo 1897435 2026495 := bstep (se 1 (by rfl) ⟨1519871, by rfl⟩ : syracuseStep 2026495 = 3039743) B3039743
theorem B2701993 : Blo 1897435 2701993 := bstep (se 2 (by rfl) ⟨1013247, by rfl⟩ : syracuseStep 2701993 = 2026495) B2026495
theorem B3602657 : Blo 1897435 3602657 := bstep (se 2 (by rfl) ⟨1350996, by rfl⟩ : syracuseStep 3602657 = 2701993) B2701993
theorem B9607085 : Blo 1897435 9607085 := bstep (se 3 (by rfl) ⟨1801328, by rfl⟩ : syracuseStep 9607085 = 3602657) B3602657
theorem B6404723 : Blo 1897435 6404723 := bstep (se 1 (by rfl) ⟨4803542, by rfl⟩ : syracuseStep 6404723 = 9607085) B9607085
theorem B4269815 : Blo 1897435 4269815 := bstep (se 1 (by rfl) ⟨3202361, by rfl⟩ : syracuseStep 4269815 = 6404723) B6404723
theorem B2846543 : Blo 1897435 2846543 := bstep (se 1 (by rfl) ⟨2134907, by rfl⟩ : syracuseStep 2846543 = 4269815) B4269815
theorem B1897695 : Blo 1897435 1897695 := bstep (se 1 (by rfl) ⟨1423271, by rfl⟩ : syracuseStep 1897695 = 2846543) B2846543
theorem B2846549 : Blo 1897435 2846549 := bbase (se 9 (by rfl) ⟨8339, by rfl⟩ : syracuseStep 2846549 = 16679) (by norm_num)
theorem B1897699 : Blo 1897435 1897699 := bstep (se 1 (by rfl) ⟨1423274, by rfl⟩ : syracuseStep 1897699 = 2846549) B2846549
theorem B13678901 : Blo 1897435 13678901 := bbase (se 5 (by rfl) ⟨641198, by rfl⟩ : syracuseStep 13678901 = 1282397) (by norm_num)
theorem B9119267 : Blo 1897435 9119267 := bstep (se 1 (by rfl) ⟨6839450, by rfl⟩ : syracuseStep 9119267 = 13678901) B13678901
theorem B6079511 : Blo 1897435 6079511 := bstep (se 1 (by rfl) ⟨4559633, by rfl⟩ : syracuseStep 6079511 = 9119267) B9119267
theorem B4053007 : Blo 1897435 4053007 := bstep (se 1 (by rfl) ⟨3039755, by rfl⟩ : syracuseStep 4053007 = 6079511) B6079511
theorem B5404009 : Blo 1897435 5404009 := bstep (se 2 (by rfl) ⟨2026503, by rfl⟩ : syracuseStep 5404009 = 4053007) B4053007
theorem B7205345 : Blo 1897435 7205345 := bstep (se 2 (by rfl) ⟨2702004, by rfl⟩ : syracuseStep 7205345 = 5404009) B5404009
theorem B4803563 : Blo 1897435 4803563 := bstep (se 1 (by rfl) ⟨3602672, by rfl⟩ : syracuseStep 4803563 = 7205345) B7205345
theorem B3202375 : Blo 1897435 3202375 := bstep (se 1 (by rfl) ⟨2401781, by rfl⟩ : syracuseStep 3202375 = 4803563) B4803563
theorem B4269833 : Blo 1897435 4269833 := bstep (se 2 (by rfl) ⟨1601187, by rfl⟩ : syracuseStep 4269833 = 3202375) B3202375
theorem B2846555 : Blo 1897435 2846555 := bstep (se 1 (by rfl) ⟨2134916, by rfl⟩ : syracuseStep 2846555 = 4269833) B4269833
theorem B1897703 : Blo 1897435 1897703 := bstep (se 1 (by rfl) ⟨1423277, by rfl⟩ : syracuseStep 1897703 = 2846555) B2846555
theorem B2134921 : Blo 1897435 2134921 := bbase (se 2 (by rfl) ⟨800595, by rfl⟩ : syracuseStep 2134921 = 1601191) (by norm_num)
theorem B2846561 : Blo 1897435 2846561 := bstep (se 2 (by rfl) ⟨1067460, by rfl⟩ : syracuseStep 2846561 = 2134921) B2134921
theorem B1897707 : Blo 1897435 1897707 := bstep (se 1 (by rfl) ⟨1423280, by rfl⟩ : syracuseStep 1897707 = 2846561) B2846561
theorem B3466397 : Blo 1897435 3466397 := bbase (se 3 (by rfl) ⟨649949, by rfl⟩ : syracuseStep 3466397 = 1299899) (by norm_num)
theorem B2310931 : Blo 1897435 2310931 := bstep (se 1 (by rfl) ⟨1733198, by rfl⟩ : syracuseStep 2310931 = 3466397) B3466397
theorem B3081241 : Blo 1897435 3081241 := bstep (se 2 (by rfl) ⟨1155465, by rfl⟩ : syracuseStep 3081241 = 2310931) B2310931
theorem B4108321 : Blo 1897435 4108321 := bstep (se 2 (by rfl) ⟨1540620, by rfl⟩ : syracuseStep 4108321 = 3081241) B3081241
theorem B5477761 : Blo 1897435 5477761 := bstep (se 2 (by rfl) ⟨2054160, by rfl⟩ : syracuseStep 5477761 = 4108321) B4108321
theorem B7303681 : Blo 1897435 7303681 := bstep (se 2 (by rfl) ⟨2738880, by rfl⟩ : syracuseStep 7303681 = 5477761) B5477761
theorem B38952965 : Blo 1897435 38952965 := bstep (se 4 (by rfl) ⟨3651840, by rfl⟩ : syracuseStep 38952965 = 7303681) B7303681
theorem B25968643 : Blo 1897435 25968643 := bstep (se 1 (by rfl) ⟨19476482, by rfl⟩ : syracuseStep 25968643 = 38952965) B38952965
theorem B138499429 : Blo 1897435 138499429 := bstep (se 4 (by rfl) ⟨12984321, by rfl⟩ : syracuseStep 138499429 = 25968643) B25968643
theorem B184665905 : Blo 1897435 184665905 := bstep (se 2 (by rfl) ⟨69249714, by rfl⟩ : syracuseStep 184665905 = 138499429) B138499429
theorem B123110603 : Blo 1897435 123110603 := bstep (se 1 (by rfl) ⟨92332952, by rfl⟩ : syracuseStep 123110603 = 184665905) B184665905
theorem B82073735 : Blo 1897435 82073735 := bstep (se 1 (by rfl) ⟨61555301, by rfl⟩ : syracuseStep 82073735 = 123110603) B123110603
theorem B54715823 : Blo 1897435 54715823 := bstep (se 1 (by rfl) ⟨41036867, by rfl⟩ : syracuseStep 54715823 = 82073735) B82073735
theorem B36477215 : Blo 1897435 36477215 := bstep (se 1 (by rfl) ⟨27357911, by rfl⟩ : syracuseStep 36477215 = 54715823) B54715823
theorem B24318143 : Blo 1897435 24318143 := bstep (se 1 (by rfl) ⟨18238607, by rfl⟩ : syracuseStep 24318143 = 36477215) B36477215
theorem B16212095 : Blo 1897435 16212095 := bstep (se 1 (by rfl) ⟨12159071, by rfl⟩ : syracuseStep 16212095 = 24318143) B24318143
theorem B10808063 : Blo 1897435 10808063 := bstep (se 1 (by rfl) ⟨8106047, by rfl⟩ : syracuseStep 10808063 = 16212095) B16212095
theorem B7205375 : Blo 1897435 7205375 := bstep (se 1 (by rfl) ⟨5404031, by rfl⟩ : syracuseStep 7205375 = 10808063) B10808063
theorem B4803583 : Blo 1897435 4803583 := bstep (se 1 (by rfl) ⟨3602687, by rfl⟩ : syracuseStep 4803583 = 7205375) B7205375
theorem B6404777 : Blo 1897435 6404777 := bstep (se 2 (by rfl) ⟨2401791, by rfl⟩ : syracuseStep 6404777 = 4803583) B4803583
theorem B4269851 : Blo 1897435 4269851 := bstep (se 1 (by rfl) ⟨3202388, by rfl⟩ : syracuseStep 4269851 = 6404777) B6404777
theorem B2846567 : Blo 1897435 2846567 := bstep (se 1 (by rfl) ⟨2134925, by rfl⟩ : syracuseStep 2846567 = 4269851) B4269851
theorem B1897711 : Blo 1897435 1897711 := bstep (se 1 (by rfl) ⟨1423283, by rfl⟩ : syracuseStep 1897711 = 2846567) B2846567
theorem B2846573 : Blo 1897435 2846573 := bbase (se 3 (by rfl) ⟨533732, by rfl⟩ : syracuseStep 2846573 = 1067465) (by norm_num)
theorem B1897715 : Blo 1897435 1897715 := bstep (se 1 (by rfl) ⟨1423286, by rfl⟩ : syracuseStep 1897715 = 2846573) B2846573
theorem B4269869 : Blo 1897435 4269869 := bbase (se 3 (by rfl) ⟨800600, by rfl⟩ : syracuseStep 4269869 = 1601201) (by norm_num)
theorem B2846579 : Blo 1897435 2846579 := bstep (se 1 (by rfl) ⟨2134934, by rfl⟩ : syracuseStep 2846579 = 4269869) B4269869
theorem B1897719 : Blo 1897435 1897719 := bstep (se 1 (by rfl) ⟨1423289, by rfl⟩ : syracuseStep 1897719 = 2846579) B2846579
theorem B8106101 : Blo 1897435 8106101 := bbase (se 5 (by rfl) ⟨379973, by rfl⟩ : syracuseStep 8106101 = 759947) (by norm_num)
theorem B5404067 : Blo 1897435 5404067 := bstep (se 1 (by rfl) ⟨4053050, by rfl⟩ : syracuseStep 5404067 = 8106101) B8106101
theorem B3602711 : Blo 1897435 3602711 := bstep (se 1 (by rfl) ⟨2702033, by rfl⟩ : syracuseStep 3602711 = 5404067) B5404067
theorem B2401807 : Blo 1897435 2401807 := bstep (se 1 (by rfl) ⟨1801355, by rfl⟩ : syracuseStep 2401807 = 3602711) B3602711
theorem B3202409 : Blo 1897435 3202409 := bstep (se 2 (by rfl) ⟨1200903, by rfl⟩ : syracuseStep 3202409 = 2401807) B2401807
theorem B2134939 : Blo 1897435 2134939 := bstep (se 1 (by rfl) ⟨1601204, by rfl⟩ : syracuseStep 2134939 = 3202409) B3202409
theorem B2846585 : Blo 1897435 2846585 := bstep (se 2 (by rfl) ⟨1067469, by rfl⟩ : syracuseStep 2846585 = 2134939) B2134939
theorem B1897723 : Blo 1897435 1897723 := bstep (se 1 (by rfl) ⟨1423292, by rfl⟩ : syracuseStep 1897723 = 2846585) B2846585
theorem B2279845 : Blo 1897435 2279845 := bbase (se 4 (by rfl) ⟨213735, by rfl⟩ : syracuseStep 2279845 = 427471) (by norm_num)
theorem B12159173 : Blo 1897435 12159173 := bstep (se 4 (by rfl) ⟨1139922, by rfl⟩ : syracuseStep 12159173 = 2279845) B2279845
theorem B32424461 : Blo 1897435 32424461 := bstep (se 3 (by rfl) ⟨6079586, by rfl⟩ : syracuseStep 32424461 = 12159173) B12159173
theorem B21616307 : Blo 1897435 21616307 := bstep (se 1 (by rfl) ⟨16212230, by rfl⟩ : syracuseStep 21616307 = 32424461) B32424461
theorem B14410871 : Blo 1897435 14410871 := bstep (se 1 (by rfl) ⟨10808153, by rfl⟩ : syracuseStep 14410871 = 21616307) B21616307
theorem B9607247 : Blo 1897435 9607247 := bstep (se 1 (by rfl) ⟨7205435, by rfl⟩ : syracuseStep 9607247 = 14410871) B14410871
theorem B6404831 : Blo 1897435 6404831 := bstep (se 1 (by rfl) ⟨4803623, by rfl⟩ : syracuseStep 6404831 = 9607247) B9607247
theorem B4269887 : Blo 1897435 4269887 := bstep (se 1 (by rfl) ⟨3202415, by rfl⟩ : syracuseStep 4269887 = 6404831) B6404831
theorem B2846591 : Blo 1897435 2846591 := bstep (se 1 (by rfl) ⟨2134943, by rfl⟩ : syracuseStep 2846591 = 4269887) B4269887
theorem B1897727 : Blo 1897435 1897727 := bstep (se 1 (by rfl) ⟨1423295, by rfl⟩ : syracuseStep 1897727 = 2846591) B2846591
theorem B2846597 : Blo 1897435 2846597 := bbase (se 4 (by rfl) ⟨266868, by rfl⟩ : syracuseStep 2846597 = 533737) (by norm_num)
theorem B1897731 : Blo 1897435 1897731 := bstep (se 1 (by rfl) ⟨1423298, by rfl⟩ : syracuseStep 1897731 = 2846597) B2846597
theorem B3202429 : Blo 1897435 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B4269905 : Blo 1897435 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B2846603 : Blo 1897435 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B1897735 : Blo 1897435 1897735 := bstep (se 1 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 1897735 = 2846603) B2846603
theorem B2134957 : Blo 1897435 2134957 := bbase (se 3 (by rfl) ⟨400304, by rfl⟩ : syracuseStep 2134957 = 800609) (by norm_num)
theorem B2846609 : Blo 1897435 2846609 := bstep (se 2 (by rfl) ⟨1067478, by rfl⟩ : syracuseStep 2846609 = 2134957) B2134957
theorem B1897739 : Blo 1897435 1897739 := bstep (se 1 (by rfl) ⟨1423304, by rfl⟩ : syracuseStep 1897739 = 2846609) B2846609
theorem B6404885 : Blo 1897435 6404885 := bbase (se 6 (by rfl) ⟨150114, by rfl⟩ : syracuseStep 6404885 = 300229) (by norm_num)
theorem B4269923 : Blo 1897435 4269923 := bstep (se 1 (by rfl) ⟨3202442, by rfl⟩ : syracuseStep 4269923 = 6404885) B6404885
theorem B2846615 : Blo 1897435 2846615 := bstep (se 1 (by rfl) ⟨2134961, by rfl⟩ : syracuseStep 2846615 = 4269923) B4269923
theorem B1897743 : Blo 1897435 1897743 := bstep (se 1 (by rfl) ⟨1423307, by rfl⟩ : syracuseStep 1897743 = 2846615) B2846615
theorem B2846621 : Blo 1897435 2846621 := bbase (se 3 (by rfl) ⟨533741, by rfl⟩ : syracuseStep 2846621 = 1067483) (by norm_num)
theorem B1897747 : Blo 1897435 1897747 := bstep (se 1 (by rfl) ⟨1423310, by rfl⟩ : syracuseStep 1897747 = 2846621) B2846621
theorem B4269941 : Blo 1897435 4269941 := bbase (se 5 (by rfl) ⟨200153, by rfl⟩ : syracuseStep 4269941 = 400307) (by norm_num)
theorem B2846627 : Blo 1897435 2846627 := bstep (se 1 (by rfl) ⟨2134970, by rfl⟩ : syracuseStep 2846627 = 4269941) B4269941
theorem B1897751 : Blo 1897435 1897751 := bstep (se 1 (by rfl) ⟨1423313, by rfl⟩ : syracuseStep 1897751 = 2846627) B2846627
theorem B2054209 : Blo 1897435 2054209 := bbase (se 2 (by rfl) ⟨770328, by rfl⟩ : syracuseStep 2054209 = 1540657) (by norm_num)
theorem B2738945 : Blo 1897435 2738945 := bstep (se 2 (by rfl) ⟨1027104, by rfl⟩ : syracuseStep 2738945 = 2054209) B2054209
theorem B7303853 : Blo 1897435 7303853 := bstep (se 3 (by rfl) ⟨1369472, by rfl⟩ : syracuseStep 7303853 = 2738945) B2738945
theorem B4869235 : Blo 1897435 4869235 := bstep (se 1 (by rfl) ⟨3651926, by rfl⟩ : syracuseStep 4869235 = 7303853) B7303853
theorem B6492313 : Blo 1897435 6492313 := bstep (se 2 (by rfl) ⟨2434617, by rfl⟩ : syracuseStep 6492313 = 4869235) B4869235
theorem B8656417 : Blo 1897435 8656417 := bstep (se 2 (by rfl) ⟨3246156, by rfl⟩ : syracuseStep 8656417 = 6492313) B6492313
theorem B11541889 : Blo 1897435 11541889 := bstep (se 2 (by rfl) ⟨4328208, by rfl⟩ : syracuseStep 11541889 = 8656417) B8656417
theorem B15389185 : Blo 1897435 15389185 := bstep (se 2 (by rfl) ⟨5770944, by rfl⟩ : syracuseStep 15389185 = 11541889) B11541889
theorem B20518913 : Blo 1897435 20518913 := bstep (se 2 (by rfl) ⟨7694592, by rfl⟩ : syracuseStep 20518913 = 15389185) B15389185
theorem B13679275 : Blo 1897435 13679275 := bstep (se 1 (by rfl) ⟨10259456, by rfl⟩ : syracuseStep 13679275 = 20518913) B20518913
theorem B18239033 : Blo 1897435 18239033 := bstep (se 2 (by rfl) ⟨6839637, by rfl⟩ : syracuseStep 18239033 = 13679275) B13679275
theorem B12159355 : Blo 1897435 12159355 := bstep (se 1 (by rfl) ⟨9119516, by rfl⟩ : syracuseStep 12159355 = 18239033) B18239033
theorem B16212473 : Blo 1897435 16212473 := bstep (se 2 (by rfl) ⟨6079677, by rfl⟩ : syracuseStep 16212473 = 12159355) B12159355
theorem B10808315 : Blo 1897435 10808315 := bstep (se 1 (by rfl) ⟨8106236, by rfl⟩ : syracuseStep 10808315 = 16212473) B16212473
theorem B7205543 : Blo 1897435 7205543 := bstep (se 1 (by rfl) ⟨5404157, by rfl⟩ : syracuseStep 7205543 = 10808315) B10808315
theorem B4803695 : Blo 1897435 4803695 := bstep (se 1 (by rfl) ⟨3602771, by rfl⟩ : syracuseStep 4803695 = 7205543) B7205543
theorem B3202463 : Blo 1897435 3202463 := bstep (se 1 (by rfl) ⟨2401847, by rfl⟩ : syracuseStep 3202463 = 4803695) B4803695
theorem B2134975 : Blo 1897435 2134975 := bstep (se 1 (by rfl) ⟨1601231, by rfl⟩ : syracuseStep 2134975 = 3202463) B3202463
theorem B2846633 : Blo 1897435 2846633 := bstep (se 2 (by rfl) ⟨1067487, by rfl⟩ : syracuseStep 2846633 = 2134975) B2134975
theorem B1897755 : Blo 1897435 1897755 := bstep (se 1 (by rfl) ⟨1423316, by rfl⟩ : syracuseStep 1897755 = 2846633) B2846633
theorem B7205557 : Blo 1897435 7205557 := bbase (se 5 (by rfl) ⟨337760, by rfl⟩ : syracuseStep 7205557 = 675521) (by norm_num)
theorem B9607409 : Blo 1897435 9607409 := bstep (se 2 (by rfl) ⟨3602778, by rfl⟩ : syracuseStep 9607409 = 7205557) B7205557
theorem B6404939 : Blo 1897435 6404939 := bstep (se 1 (by rfl) ⟨4803704, by rfl⟩ : syracuseStep 6404939 = 9607409) B9607409
theorem B4269959 : Blo 1897435 4269959 := bstep (se 1 (by rfl) ⟨3202469, by rfl⟩ : syracuseStep 4269959 = 6404939) B6404939
theorem B2846639 : Blo 1897435 2846639 := bstep (se 1 (by rfl) ⟨2134979, by rfl⟩ : syracuseStep 2846639 = 4269959) B4269959
theorem B1897759 : Blo 1897435 1897759 := bstep (se 1 (by rfl) ⟨1423319, by rfl⟩ : syracuseStep 1897759 = 2846639) B2846639
theorem B2846645 : Blo 1897435 2846645 := bbase (se 5 (by rfl) ⟨133436, by rfl⟩ : syracuseStep 2846645 = 266873) (by norm_num)
theorem B1897763 : Blo 1897435 1897763 := bstep (se 1 (by rfl) ⟨1423322, by rfl⟩ : syracuseStep 1897763 = 2846645) B2846645
theorem B4803725 : Blo 1897435 4803725 := bbase (se 3 (by rfl) ⟨900698, by rfl⟩ : syracuseStep 4803725 = 1801397) (by norm_num)
theorem B3202483 : Blo 1897435 3202483 := bstep (se 1 (by rfl) ⟨2401862, by rfl⟩ : syracuseStep 3202483 = 4803725) B4803725
theorem B4269977 : Blo 1897435 4269977 := bstep (se 2 (by rfl) ⟨1601241, by rfl⟩ : syracuseStep 4269977 = 3202483) B3202483
theorem B2846651 : Blo 1897435 2846651 := bstep (se 1 (by rfl) ⟨2134988, by rfl⟩ : syracuseStep 2846651 = 4269977) B4269977
theorem B1897767 : Blo 1897435 1897767 := bstep (se 1 (by rfl) ⟨1423325, by rfl⟩ : syracuseStep 1897767 = 2846651) B2846651
theorem B2134993 : Blo 1897435 2134993 := bbase (se 2 (by rfl) ⟨800622, by rfl⟩ : syracuseStep 2134993 = 1601245) (by norm_num)
theorem B2846657 : Blo 1897435 2846657 := bstep (se 2 (by rfl) ⟨1067496, by rfl⟩ : syracuseStep 2846657 = 2134993) B2134993
theorem B1897771 : Blo 1897435 1897771 := bstep (se 1 (by rfl) ⟨1423328, by rfl⟩ : syracuseStep 1897771 = 2846657) B2846657
theorem B9498005 : Blo 1897435 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B6332003 : Blo 1897435 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B4221335 : Blo 1897435 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B11256893 : Blo 1897435 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B7504595 : Blo 1897435 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B5003063 : Blo 1897435 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B3335375 : Blo 1897435 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B8894333 : Blo 1897435 8894333 := bstep (se 3 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 8894333 = 3335375) B3335375
theorem B23718221 : Blo 1897435 23718221 := bstep (se 3 (by rfl) ⟨4447166, by rfl⟩ : syracuseStep 23718221 = 8894333) B8894333
theorem B15812147 : Blo 1897435 15812147 := bstep (se 1 (by rfl) ⟨11859110, by rfl⟩ : syracuseStep 15812147 = 23718221) B23718221
theorem B10541431 : Blo 1897435 10541431 := bstep (se 1 (by rfl) ⟨7906073, by rfl⟩ : syracuseStep 10541431 = 15812147) B15812147
theorem B14055241 : Blo 1897435 14055241 := bstep (se 2 (by rfl) ⟨5270715, by rfl⟩ : syracuseStep 14055241 = 10541431) B10541431
theorem B18740321 : Blo 1897435 18740321 := bstep (se 2 (by rfl) ⟨7027620, by rfl⟩ : syracuseStep 18740321 = 14055241) B14055241
theorem B12493547 : Blo 1897435 12493547 := bstep (se 1 (by rfl) ⟨9370160, by rfl⟩ : syracuseStep 12493547 = 18740321) B18740321
theorem B8329031 : Blo 1897435 8329031 := bstep (se 1 (by rfl) ⟨6246773, by rfl⟩ : syracuseStep 8329031 = 12493547) B12493547
theorem B5552687 : Blo 1897435 5552687 := bstep (se 1 (by rfl) ⟨4164515, by rfl⟩ : syracuseStep 5552687 = 8329031) B8329031
theorem B3701791 : Blo 1897435 3701791 := bstep (se 1 (by rfl) ⟨2776343, by rfl⟩ : syracuseStep 3701791 = 5552687) B5552687
theorem B19742885 : Blo 1897435 19742885 := bstep (se 4 (by rfl) ⟨1850895, by rfl⟩ : syracuseStep 19742885 = 3701791) B3701791
theorem B13161923 : Blo 1897435 13161923 := bstep (se 1 (by rfl) ⟨9871442, by rfl⟩ : syracuseStep 13161923 = 19742885) B19742885
theorem B8774615 : Blo 1897435 8774615 := bstep (se 1 (by rfl) ⟨6580961, by rfl⟩ : syracuseStep 8774615 = 13161923) B13161923
theorem B5849743 : Blo 1897435 5849743 := bstep (se 1 (by rfl) ⟨4387307, by rfl⟩ : syracuseStep 5849743 = 8774615) B8774615
theorem B7799657 : Blo 1897435 7799657 := bstep (se 2 (by rfl) ⟨2924871, by rfl⟩ : syracuseStep 7799657 = 5849743) B5849743
theorem B83196341 : Blo 1897435 83196341 := bstep (se 5 (by rfl) ⟨3899828, by rfl⟩ : syracuseStep 83196341 = 7799657) B7799657
theorem B55464227 : Blo 1897435 55464227 := bstep (se 1 (by rfl) ⟨41598170, by rfl⟩ : syracuseStep 55464227 = 83196341) B83196341
theorem B36976151 : Blo 1897435 36976151 := bstep (se 1 (by rfl) ⟨27732113, by rfl⟩ : syracuseStep 36976151 = 55464227) B55464227
theorem B24650767 : Blo 1897435 24650767 := bstep (se 1 (by rfl) ⟨18488075, by rfl⟩ : syracuseStep 24650767 = 36976151) B36976151
theorem B32867689 : Blo 1897435 32867689 := bstep (se 2 (by rfl) ⟨12325383, by rfl⟩ : syracuseStep 32867689 = 24650767) B24650767
theorem B43823585 : Blo 1897435 43823585 := bstep (se 2 (by rfl) ⟨16433844, by rfl⟩ : syracuseStep 43823585 = 32867689) B32867689
theorem B29215723 : Blo 1897435 29215723 := bstep (se 1 (by rfl) ⟨21911792, by rfl⟩ : syracuseStep 29215723 = 43823585) B43823585
theorem B38954297 : Blo 1897435 38954297 := bstep (se 2 (by rfl) ⟨14607861, by rfl⟩ : syracuseStep 38954297 = 29215723) B29215723
theorem B25969531 : Blo 1897435 25969531 := bstep (se 1 (by rfl) ⟨19477148, by rfl⟩ : syracuseStep 25969531 = 38954297) B38954297
theorem B34626041 : Blo 1897435 34626041 := bstep (se 2 (by rfl) ⟨12984765, by rfl⟩ : syracuseStep 34626041 = 25969531) B25969531
theorem B23084027 : Blo 1897435 23084027 := bstep (se 1 (by rfl) ⟨17313020, by rfl⟩ : syracuseStep 23084027 = 34626041) B34626041
theorem B15389351 : Blo 1897435 15389351 := bstep (se 1 (by rfl) ⟨11542013, by rfl⟩ : syracuseStep 15389351 = 23084027) B23084027
theorem B10259567 : Blo 1897435 10259567 := bstep (se 1 (by rfl) ⟨7694675, by rfl⟩ : syracuseStep 10259567 = 15389351) B15389351
theorem B6839711 : Blo 1897435 6839711 := bstep (se 1 (by rfl) ⟨5129783, by rfl⟩ : syracuseStep 6839711 = 10259567) B10259567
theorem B4559807 : Blo 1897435 4559807 := bstep (se 1 (by rfl) ⟨3419855, by rfl⟩ : syracuseStep 4559807 = 6839711) B6839711
theorem B3039871 : Blo 1897435 3039871 := bstep (se 1 (by rfl) ⟨2279903, by rfl⟩ : syracuseStep 3039871 = 4559807) B4559807
theorem B4053161 : Blo 1897435 4053161 := bstep (se 2 (by rfl) ⟨1519935, by rfl⟩ : syracuseStep 4053161 = 3039871) B3039871
theorem B2702107 : Blo 1897435 2702107 := bstep (se 1 (by rfl) ⟨2026580, by rfl⟩ : syracuseStep 2702107 = 4053161) B4053161
theorem B3602809 : Blo 1897435 3602809 := bstep (se 2 (by rfl) ⟨1351053, by rfl⟩ : syracuseStep 3602809 = 2702107) B2702107
theorem B4803745 : Blo 1897435 4803745 := bstep (se 2 (by rfl) ⟨1801404, by rfl⟩ : syracuseStep 4803745 = 3602809) B3602809
theorem B6404993 : Blo 1897435 6404993 := bstep (se 2 (by rfl) ⟨2401872, by rfl⟩ : syracuseStep 6404993 = 4803745) B4803745
theorem B4269995 : Blo 1897435 4269995 := bstep (se 1 (by rfl) ⟨3202496, by rfl⟩ : syracuseStep 4269995 = 6404993) B6404993
theorem B2846663 : Blo 1897435 2846663 := bstep (se 1 (by rfl) ⟨2134997, by rfl⟩ : syracuseStep 2846663 = 4269995) B4269995
theorem B1897775 : Blo 1897435 1897775 := bstep (se 1 (by rfl) ⟨1423331, by rfl⟩ : syracuseStep 1897775 = 2846663) B2846663
theorem B2846669 : Blo 1897435 2846669 := bbase (se 3 (by rfl) ⟨533750, by rfl⟩ : syracuseStep 2846669 = 1067501) (by norm_num)
theorem B1897779 : Blo 1897435 1897779 := bstep (se 1 (by rfl) ⟨1423334, by rfl⟩ : syracuseStep 1897779 = 2846669) B2846669
theorem B4270013 : Blo 1897435 4270013 := bbase (se 3 (by rfl) ⟨800627, by rfl⟩ : syracuseStep 4270013 = 1601255) (by norm_num)
theorem B2846675 : Blo 1897435 2846675 := bstep (se 1 (by rfl) ⟨2135006, by rfl⟩ : syracuseStep 2846675 = 4270013) B4270013
theorem B1897783 : Blo 1897435 1897783 := bstep (se 1 (by rfl) ⟨1423337, by rfl⟩ : syracuseStep 1897783 = 2846675) B2846675
theorem B3202517 : Blo 1897435 3202517 := bbase (se 7 (by rfl) ⟨37529, by rfl⟩ : syracuseStep 3202517 = 75059) (by norm_num)
theorem B2135011 : Blo 1897435 2135011 := bstep (se 1 (by rfl) ⟨1601258, by rfl⟩ : syracuseStep 2135011 = 3202517) B3202517
theorem B2846681 : Blo 1897435 2846681 := bstep (se 2 (by rfl) ⟨1067505, by rfl⟩ : syracuseStep 2846681 = 2135011) B2135011
theorem B1897787 : Blo 1897435 1897787 := bstep (se 1 (by rfl) ⟨1423340, by rfl⟩ : syracuseStep 1897787 = 2846681) B2846681
theorem B8106389 : Blo 1897435 8106389 := bbase (se 6 (by rfl) ⟨189993, by rfl⟩ : syracuseStep 8106389 = 379987) (by norm_num)
theorem B5404259 : Blo 1897435 5404259 := bstep (se 1 (by rfl) ⟨4053194, by rfl⟩ : syracuseStep 5404259 = 8106389) B8106389
theorem B14411357 : Blo 1897435 14411357 := bstep (se 3 (by rfl) ⟨2702129, by rfl⟩ : syracuseStep 14411357 = 5404259) B5404259
theorem B9607571 : Blo 1897435 9607571 := bstep (se 1 (by rfl) ⟨7205678, by rfl⟩ : syracuseStep 9607571 = 14411357) B14411357
theorem B6405047 : Blo 1897435 6405047 := bstep (se 1 (by rfl) ⟨4803785, by rfl⟩ : syracuseStep 6405047 = 9607571) B9607571
theorem B4270031 : Blo 1897435 4270031 := bstep (se 1 (by rfl) ⟨3202523, by rfl⟩ : syracuseStep 4270031 = 6405047) B6405047
theorem B2846687 : Blo 1897435 2846687 := bstep (se 1 (by rfl) ⟨2135015, by rfl⟩ : syracuseStep 2846687 = 4270031) B4270031
theorem B1897791 : Blo 1897435 1897791 := bstep (se 1 (by rfl) ⟨1423343, by rfl⟩ : syracuseStep 1897791 = 2846687) B2846687
theorem B2846693 : Blo 1897435 2846693 := bbase (se 4 (by rfl) ⟨266877, by rfl⟩ : syracuseStep 2846693 = 533755) (by norm_num)
theorem B1897795 : Blo 1897435 1897795 := bstep (se 1 (by rfl) ⟨1423346, by rfl⟩ : syracuseStep 1897795 = 2846693) B2846693
theorem B6839797 : Blo 1897435 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B9119729 : Blo 1897435 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B6079819 : Blo 1897435 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B8106425 : Blo 1897435 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B5404283 : Blo 1897435 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B3602855 : Blo 1897435 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B2401903 : Blo 1897435 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B3202537 : Blo 1897435 3202537 := bstep (se 2 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 3202537 = 2401903) B2401903
theorem B4270049 : Blo 1897435 4270049 := bstep (se 2 (by rfl) ⟨1601268, by rfl⟩ : syracuseStep 4270049 = 3202537) B3202537
theorem B2846699 : Blo 1897435 2846699 := bstep (se 1 (by rfl) ⟨2135024, by rfl⟩ : syracuseStep 2846699 = 4270049) B4270049
theorem B1897799 : Blo 1897435 1897799 := bstep (se 1 (by rfl) ⟨1423349, by rfl⟩ : syracuseStep 1897799 = 2846699) B2846699
theorem B2135029 : Blo 1897435 2135029 := bbase (se 5 (by rfl) ⟨100079, by rfl⟩ : syracuseStep 2135029 = 200159) (by norm_num)
theorem B2846705 : Blo 1897435 2846705 := bstep (se 2 (by rfl) ⟨1067514, by rfl⟩ : syracuseStep 2846705 = 2135029) B2135029
theorem B1897803 : Blo 1897435 1897803 := bstep (se 1 (by rfl) ⟨1423352, by rfl⟩ : syracuseStep 1897803 = 2846705) B2846705
theorem B2401913 : Blo 1897435 2401913 := bbase (se 2 (by rfl) ⟨900717, by rfl⟩ : syracuseStep 2401913 = 1801435) (by norm_num)
theorem B6405101 : Blo 1897435 6405101 := bstep (se 3 (by rfl) ⟨1200956, by rfl⟩ : syracuseStep 6405101 = 2401913) B2401913
theorem B4270067 : Blo 1897435 4270067 := bstep (se 1 (by rfl) ⟨3202550, by rfl⟩ : syracuseStep 4270067 = 6405101) B6405101
theorem B2846711 : Blo 1897435 2846711 := bstep (se 1 (by rfl) ⟨2135033, by rfl⟩ : syracuseStep 2846711 = 4270067) B4270067
theorem B1897807 : Blo 1897435 1897807 := bstep (se 1 (by rfl) ⟨1423355, by rfl⟩ : syracuseStep 1897807 = 2846711) B2846711
theorem B2846717 : Blo 1897435 2846717 := bbase (se 3 (by rfl) ⟨533759, by rfl⟩ : syracuseStep 2846717 = 1067519) (by norm_num)
theorem B1897811 : Blo 1897435 1897811 := bstep (se 1 (by rfl) ⟨1423358, by rfl⟩ : syracuseStep 1897811 = 2846717) B2846717
theorem B4270085 : Blo 1897435 4270085 := bbase (se 4 (by rfl) ⟨400320, by rfl⟩ : syracuseStep 4270085 = 800641) (by norm_num)
theorem B2846723 : Blo 1897435 2846723 := bstep (se 1 (by rfl) ⟨2135042, by rfl⟩ : syracuseStep 2846723 = 4270085) B4270085
theorem B1897815 : Blo 1897435 1897815 := bstep (se 1 (by rfl) ⟨1423361, by rfl⟩ : syracuseStep 1897815 = 2846723) B2846723
theorem B3602893 : Blo 1897435 3602893 := bbase (se 3 (by rfl) ⟨675542, by rfl⟩ : syracuseStep 3602893 = 1351085) (by norm_num)
theorem B4803857 : Blo 1897435 4803857 := bstep (se 2 (by rfl) ⟨1801446, by rfl⟩ : syracuseStep 4803857 = 3602893) B3602893
theorem B3202571 : Blo 1897435 3202571 := bstep (se 1 (by rfl) ⟨2401928, by rfl⟩ : syracuseStep 3202571 = 4803857) B4803857
theorem B2135047 : Blo 1897435 2135047 := bstep (se 1 (by rfl) ⟨1601285, by rfl⟩ : syracuseStep 2135047 = 3202571) B3202571
theorem B2846729 : Blo 1897435 2846729 := bstep (se 2 (by rfl) ⟨1067523, by rfl⟩ : syracuseStep 2846729 = 2135047) B2135047
theorem B1897819 : Blo 1897435 1897819 := bstep (se 1 (by rfl) ⟨1423364, by rfl⟩ : syracuseStep 1897819 = 2846729) B2846729
theorem B9607733 : Blo 1897435 9607733 := bbase (se 5 (by rfl) ⟨450362, by rfl⟩ : syracuseStep 9607733 = 900725) (by norm_num)
theorem B6405155 : Blo 1897435 6405155 := bstep (se 1 (by rfl) ⟨4803866, by rfl⟩ : syracuseStep 6405155 = 9607733) B9607733
theorem B4270103 : Blo 1897435 4270103 := bstep (se 1 (by rfl) ⟨3202577, by rfl⟩ : syracuseStep 4270103 = 6405155) B6405155
theorem B2846735 : Blo 1897435 2846735 := bstep (se 1 (by rfl) ⟨2135051, by rfl⟩ : syracuseStep 2846735 = 4270103) B4270103
theorem B1897823 : Blo 1897435 1897823 := bstep (se 1 (by rfl) ⟨1423367, by rfl⟩ : syracuseStep 1897823 = 2846735) B2846735
theorem B2846741 : Blo 1897435 2846741 := bbase (se 6 (by rfl) ⟨66720, by rfl⟩ : syracuseStep 2846741 = 133441) (by norm_num)
theorem B1897827 : Blo 1897435 1897827 := bstep (se 1 (by rfl) ⟨1423370, by rfl⟩ : syracuseStep 1897827 = 2846741) B2846741
theorem B9244309 : Blo 1897435 9244309 := bbase (se 6 (by rfl) ⟨216663, by rfl⟩ : syracuseStep 9244309 = 433327) (by norm_num)
theorem B12325745 : Blo 1897435 12325745 := bstep (se 2 (by rfl) ⟨4622154, by rfl⟩ : syracuseStep 12325745 = 9244309) B9244309
theorem B8217163 : Blo 1897435 8217163 := bstep (se 1 (by rfl) ⟨6162872, by rfl⟩ : syracuseStep 8217163 = 12325745) B12325745
theorem B10956217 : Blo 1897435 10956217 := bstep (se 2 (by rfl) ⟨4108581, by rfl⟩ : syracuseStep 10956217 = 8217163) B8217163
theorem B14608289 : Blo 1897435 14608289 := bstep (se 2 (by rfl) ⟨5478108, by rfl⟩ : syracuseStep 14608289 = 10956217) B10956217
theorem B38955437 : Blo 1897435 38955437 := bstep (se 3 (by rfl) ⟨7304144, by rfl⟩ : syracuseStep 38955437 = 14608289) B14608289
theorem B25970291 : Blo 1897435 25970291 := bstep (se 1 (by rfl) ⟨19477718, by rfl⟩ : syracuseStep 25970291 = 38955437) B38955437
theorem B17313527 : Blo 1897435 17313527 := bstep (se 1 (by rfl) ⟨12985145, by rfl⟩ : syracuseStep 17313527 = 25970291) B25970291
theorem B11542351 : Blo 1897435 11542351 := bstep (se 1 (by rfl) ⟨8656763, by rfl⟩ : syracuseStep 11542351 = 17313527) B17313527
theorem B15389801 : Blo 1897435 15389801 := bstep (se 2 (by rfl) ⟨5771175, by rfl⟩ : syracuseStep 15389801 = 11542351) B11542351
theorem B10259867 : Blo 1897435 10259867 := bstep (se 1 (by rfl) ⟨7694900, by rfl⟩ : syracuseStep 10259867 = 15389801) B15389801
theorem B6839911 : Blo 1897435 6839911 := bstep (se 1 (by rfl) ⟨5129933, by rfl⟩ : syracuseStep 6839911 = 10259867) B10259867
theorem B9119881 : Blo 1897435 9119881 := bstep (se 2 (by rfl) ⟨3419955, by rfl⟩ : syracuseStep 9119881 = 6839911) B6839911
theorem B12159841 : Blo 1897435 12159841 := bstep (se 2 (by rfl) ⟨4559940, by rfl⟩ : syracuseStep 12159841 = 9119881) B9119881
theorem B16213121 : Blo 1897435 16213121 := bstep (se 2 (by rfl) ⟨6079920, by rfl⟩ : syracuseStep 16213121 = 12159841) B12159841
theorem B10808747 : Blo 1897435 10808747 := bstep (se 1 (by rfl) ⟨8106560, by rfl⟩ : syracuseStep 10808747 = 16213121) B16213121
theorem B7205831 : Blo 1897435 7205831 := bstep (se 1 (by rfl) ⟨5404373, by rfl⟩ : syracuseStep 7205831 = 10808747) B10808747
theorem B4803887 : Blo 1897435 4803887 := bstep (se 1 (by rfl) ⟨3602915, by rfl⟩ : syracuseStep 4803887 = 7205831) B7205831
theorem B3202591 : Blo 1897435 3202591 := bstep (se 1 (by rfl) ⟨2401943, by rfl⟩ : syracuseStep 3202591 = 4803887) B4803887
theorem B4270121 : Blo 1897435 4270121 := bstep (se 2 (by rfl) ⟨1601295, by rfl⟩ : syracuseStep 4270121 = 3202591) B3202591
theorem B2846747 : Blo 1897435 2846747 := bstep (se 1 (by rfl) ⟨2135060, by rfl⟩ : syracuseStep 2846747 = 4270121) B4270121
theorem B1897831 : Blo 1897435 1897831 := bstep (se 1 (by rfl) ⟨1423373, by rfl⟩ : syracuseStep 1897831 = 2846747) B2846747
theorem B2135065 : Blo 1897435 2135065 := bbase (se 2 (by rfl) ⟨800649, by rfl⟩ : syracuseStep 2135065 = 1601299) (by norm_num)
theorem B2846753 : Blo 1897435 2846753 := bstep (se 2 (by rfl) ⟨1067532, by rfl⟩ : syracuseStep 2846753 = 2135065) B2135065
theorem B1897835 : Blo 1897435 1897835 := bstep (se 1 (by rfl) ⟨1423376, by rfl⟩ : syracuseStep 1897835 = 2846753) B2846753
theorem B7205861 : Blo 1897435 7205861 := bbase (se 4 (by rfl) ⟨675549, by rfl⟩ : syracuseStep 7205861 = 1351099) (by norm_num)
theorem B4803907 : Blo 1897435 4803907 := bstep (se 1 (by rfl) ⟨3602930, by rfl⟩ : syracuseStep 4803907 = 7205861) B7205861
theorem B6405209 : Blo 1897435 6405209 := bstep (se 2 (by rfl) ⟨2401953, by rfl⟩ : syracuseStep 6405209 = 4803907) B4803907
theorem B4270139 : Blo 1897435 4270139 := bstep (se 1 (by rfl) ⟨3202604, by rfl⟩ : syracuseStep 4270139 = 6405209) B6405209
theorem B2846759 : Blo 1897435 2846759 := bstep (se 1 (by rfl) ⟨2135069, by rfl⟩ : syracuseStep 2846759 = 4270139) B4270139
theorem B1897839 : Blo 1897435 1897839 := bstep (se 1 (by rfl) ⟨1423379, by rfl⟩ : syracuseStep 1897839 = 2846759) B2846759
theorem B2846765 : Blo 1897435 2846765 := bbase (se 3 (by rfl) ⟨533768, by rfl⟩ : syracuseStep 2846765 = 1067537) (by norm_num)
theorem B1897843 : Blo 1897435 1897843 := bstep (se 1 (by rfl) ⟨1423382, by rfl⟩ : syracuseStep 1897843 = 2846765) B2846765
theorem B4270157 : Blo 1897435 4270157 := bbase (se 3 (by rfl) ⟨800654, by rfl⟩ : syracuseStep 4270157 = 1601309) (by norm_num)
theorem B2846771 : Blo 1897435 2846771 := bstep (se 1 (by rfl) ⟨2135078, by rfl⟩ : syracuseStep 2846771 = 4270157) B4270157
theorem B1897847 : Blo 1897435 1897847 := bstep (se 1 (by rfl) ⟨1423385, by rfl⟩ : syracuseStep 1897847 = 2846771) B2846771
theorem B2401969 : Blo 1897435 2401969 := bbase (se 2 (by rfl) ⟨900738, by rfl⟩ : syracuseStep 2401969 = 1801477) (by norm_num)
theorem B3202625 : Blo 1897435 3202625 := bstep (se 2 (by rfl) ⟨1200984, by rfl⟩ : syracuseStep 3202625 = 2401969) B2401969
theorem B2135083 : Blo 1897435 2135083 := bstep (se 1 (by rfl) ⟨1601312, by rfl⟩ : syracuseStep 2135083 = 3202625) B3202625
theorem B2846777 : Blo 1897435 2846777 := bstep (se 2 (by rfl) ⟨1067541, by rfl⟩ : syracuseStep 2846777 = 2135083) B2135083
theorem B1897851 : Blo 1897435 1897851 := bstep (se 1 (by rfl) ⟨1423388, by rfl⟩ : syracuseStep 1897851 = 2846777) B2846777
theorem B17313749 : Blo 1897435 17313749 := bbase (se 7 (by rfl) ⟨202895, by rfl⟩ : syracuseStep 17313749 = 405791) (by norm_num)
theorem B11542499 : Blo 1897435 11542499 := bstep (se 1 (by rfl) ⟨8656874, by rfl⟩ : syracuseStep 11542499 = 17313749) B17313749
theorem B7694999 : Blo 1897435 7694999 := bstep (se 1 (by rfl) ⟨5771249, by rfl⟩ : syracuseStep 7694999 = 11542499) B11542499
theorem B5129999 : Blo 1897435 5129999 := bstep (se 1 (by rfl) ⟨3847499, by rfl⟩ : syracuseStep 5129999 = 7694999) B7694999
theorem B3419999 : Blo 1897435 3419999 := bstep (se 1 (by rfl) ⟨2564999, by rfl⟩ : syracuseStep 3419999 = 5129999) B5129999
theorem B2279999 : Blo 1897435 2279999 := bstep (se 1 (by rfl) ⟨1709999, by rfl⟩ : syracuseStep 2279999 = 3419999) B3419999
theorem B6079997 : Blo 1897435 6079997 := bstep (se 3 (by rfl) ⟨1139999, by rfl⟩ : syracuseStep 6079997 = 2279999) B2279999
theorem B4053331 : Blo 1897435 4053331 := bstep (se 1 (by rfl) ⟨3039998, by rfl⟩ : syracuseStep 4053331 = 6079997) B6079997
theorem B21617765 : Blo 1897435 21617765 := bstep (se 4 (by rfl) ⟨2026665, by rfl⟩ : syracuseStep 21617765 = 4053331) B4053331
theorem B14411843 : Blo 1897435 14411843 := bstep (se 1 (by rfl) ⟨10808882, by rfl⟩ : syracuseStep 14411843 = 21617765) B21617765
theorem B9607895 : Blo 1897435 9607895 := bstep (se 1 (by rfl) ⟨7205921, by rfl⟩ : syracuseStep 9607895 = 14411843) B14411843
theorem B6405263 : Blo 1897435 6405263 := bstep (se 1 (by rfl) ⟨4803947, by rfl⟩ : syracuseStep 6405263 = 9607895) B9607895
theorem B4270175 : Blo 1897435 4270175 := bstep (se 1 (by rfl) ⟨3202631, by rfl⟩ : syracuseStep 4270175 = 6405263) B6405263
theorem B2846783 : Blo 1897435 2846783 := bstep (se 1 (by rfl) ⟨2135087, by rfl⟩ : syracuseStep 2846783 = 4270175) B4270175
theorem B1897855 : Blo 1897435 1897855 := bstep (se 1 (by rfl) ⟨1423391, by rfl⟩ : syracuseStep 1897855 = 2846783) B2846783
theorem B2846789 : Blo 1897435 2846789 := bbase (se 4 (by rfl) ⟨266886, by rfl⟩ : syracuseStep 2846789 = 533773) (by norm_num)
theorem B1897859 : Blo 1897435 1897859 := bstep (se 1 (by rfl) ⟨1423394, by rfl⟩ : syracuseStep 1897859 = 2846789) B2846789
theorem B3202645 : Blo 1897435 3202645 := bbase (se 8 (by rfl) ⟨18765, by rfl⟩ : syracuseStep 3202645 = 37531) (by norm_num)
theorem B4270193 : Blo 1897435 4270193 := bstep (se 2 (by rfl) ⟨1601322, by rfl⟩ : syracuseStep 4270193 = 3202645) B3202645
theorem B2846795 : Blo 1897435 2846795 := bstep (se 1 (by rfl) ⟨2135096, by rfl⟩ : syracuseStep 2846795 = 4270193) B4270193
theorem B1897863 : Blo 1897435 1897863 := bstep (se 1 (by rfl) ⟨1423397, by rfl⟩ : syracuseStep 1897863 = 2846795) B2846795
theorem B2135101 : Blo 1897435 2135101 := bbase (se 3 (by rfl) ⟨400331, by rfl⟩ : syracuseStep 2135101 = 800663) (by norm_num)
theorem B2846801 : Blo 1897435 2846801 := bstep (se 2 (by rfl) ⟨1067550, by rfl⟩ : syracuseStep 2846801 = 2135101) B2135101
theorem B1897867 : Blo 1897435 1897867 := bstep (se 1 (by rfl) ⟨1423400, by rfl⟩ : syracuseStep 1897867 = 2846801) B2846801
theorem B6405317 : Blo 1897435 6405317 := bbase (se 4 (by rfl) ⟨600498, by rfl⟩ : syracuseStep 6405317 = 1200997) (by norm_num)
theorem B4270211 : Blo 1897435 4270211 := bstep (se 1 (by rfl) ⟨3202658, by rfl⟩ : syracuseStep 4270211 = 6405317) B6405317
theorem B2846807 : Blo 1897435 2846807 := bstep (se 1 (by rfl) ⟨2135105, by rfl⟩ : syracuseStep 2846807 = 4270211) B4270211
theorem B1897871 : Blo 1897435 1897871 := bstep (se 1 (by rfl) ⟨1423403, by rfl⟩ : syracuseStep 1897871 = 2846807) B2846807
theorem B2846813 : Blo 1897435 2846813 := bbase (se 3 (by rfl) ⟨533777, by rfl⟩ : syracuseStep 2846813 = 1067555) (by norm_num)
theorem B1897875 : Blo 1897435 1897875 := bstep (se 1 (by rfl) ⟨1423406, by rfl⟩ : syracuseStep 1897875 = 2846813) B2846813
theorem B4270229 : Blo 1897435 4270229 := bbase (se 6 (by rfl) ⟨100083, by rfl⟩ : syracuseStep 4270229 = 200167) (by norm_num)
theorem B2846819 : Blo 1897435 2846819 := bstep (se 1 (by rfl) ⟨2135114, by rfl⟩ : syracuseStep 2846819 = 4270229) B4270229
theorem B1897879 : Blo 1897435 1897879 := bstep (se 1 (by rfl) ⟨1423409, by rfl⟩ : syracuseStep 1897879 = 2846819) B2846819
theorem B2702261 : Blo 1897435 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B7206029 : Blo 1897435 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B4804019 : Blo 1897435 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B3202679 : Blo 1897435 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B2135119 : Blo 1897435 2135119 := bstep (se 1 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 2135119 = 3202679) B3202679
theorem B2846825 : Blo 1897435 2846825 := bstep (se 2 (by rfl) ⟨1067559, by rfl⟩ : syracuseStep 2846825 = 2135119) B2135119
theorem B1897883 : Blo 1897435 1897883 := bstep (se 1 (by rfl) ⟨1423412, by rfl⟩ : syracuseStep 1897883 = 2846825) B2846825
theorem B4328509 : Blo 1897435 4328509 := bbase (se 3 (by rfl) ⟨811595, by rfl⟩ : syracuseStep 4328509 = 1623191) (by norm_num)
theorem B5771345 : Blo 1897435 5771345 := bstep (se 2 (by rfl) ⟨2164254, by rfl⟩ : syracuseStep 5771345 = 4328509) B4328509
theorem B15390253 : Blo 1897435 15390253 := bstep (se 3 (by rfl) ⟨2885672, by rfl⟩ : syracuseStep 15390253 = 5771345) B5771345
theorem B20520337 : Blo 1897435 20520337 := bstep (se 2 (by rfl) ⟨7695126, by rfl⟩ : syracuseStep 20520337 = 15390253) B15390253
theorem B27360449 : Blo 1897435 27360449 := bstep (se 2 (by rfl) ⟨10260168, by rfl⟩ : syracuseStep 27360449 = 20520337) B20520337
theorem B18240299 : Blo 1897435 18240299 := bstep (se 1 (by rfl) ⟨13680224, by rfl⟩ : syracuseStep 18240299 = 27360449) B27360449
theorem B12160199 : Blo 1897435 12160199 := bstep (se 1 (by rfl) ⟨9120149, by rfl⟩ : syracuseStep 12160199 = 18240299) B18240299
theorem B8106799 : Blo 1897435 8106799 := bstep (se 1 (by rfl) ⟨6080099, by rfl⟩ : syracuseStep 8106799 = 12160199) B12160199
theorem B10809065 : Blo 1897435 10809065 := bstep (se 2 (by rfl) ⟨4053399, by rfl⟩ : syracuseStep 10809065 = 8106799) B8106799
theorem B7206043 : Blo 1897435 7206043 := bstep (se 1 (by rfl) ⟨5404532, by rfl⟩ : syracuseStep 7206043 = 10809065) B10809065
theorem B9608057 : Blo 1897435 9608057 := bstep (se 2 (by rfl) ⟨3603021, by rfl⟩ : syracuseStep 9608057 = 7206043) B7206043
theorem B6405371 : Blo 1897435 6405371 := bstep (se 1 (by rfl) ⟨4804028, by rfl⟩ : syracuseStep 6405371 = 9608057) B9608057
theorem B4270247 : Blo 1897435 4270247 := bstep (se 1 (by rfl) ⟨3202685, by rfl⟩ : syracuseStep 4270247 = 6405371) B6405371
theorem B2846831 : Blo 1897435 2846831 := bstep (se 1 (by rfl) ⟨2135123, by rfl⟩ : syracuseStep 2846831 = 4270247) B4270247
theorem B1897887 : Blo 1897435 1897887 := bstep (se 1 (by rfl) ⟨1423415, by rfl⟩ : syracuseStep 1897887 = 2846831) B2846831
theorem B2846837 : Blo 1897435 2846837 := bbase (se 5 (by rfl) ⟨133445, by rfl⟩ : syracuseStep 2846837 = 266891) (by norm_num)
theorem B1897891 : Blo 1897435 1897891 := bstep (se 1 (by rfl) ⟨1423418, by rfl⟩ : syracuseStep 1897891 = 2846837) B2846837
theorem B3603037 : Blo 1897435 3603037 := bbase (se 3 (by rfl) ⟨675569, by rfl⟩ : syracuseStep 3603037 = 1351139) (by norm_num)
theorem B4804049 : Blo 1897435 4804049 := bstep (se 2 (by rfl) ⟨1801518, by rfl⟩ : syracuseStep 4804049 = 3603037) B3603037
theorem B3202699 : Blo 1897435 3202699 := bstep (se 1 (by rfl) ⟨2402024, by rfl⟩ : syracuseStep 3202699 = 4804049) B4804049
theorem B4270265 : Blo 1897435 4270265 := bstep (se 2 (by rfl) ⟨1601349, by rfl⟩ : syracuseStep 4270265 = 3202699) B3202699
theorem B2846843 : Blo 1897435 2846843 := bstep (se 1 (by rfl) ⟨2135132, by rfl⟩ : syracuseStep 2846843 = 4270265) B4270265
theorem B1897895 : Blo 1897435 1897895 := bstep (se 1 (by rfl) ⟨1423421, by rfl⟩ : syracuseStep 1897895 = 2846843) B2846843
theorem B2135137 : Blo 1897435 2135137 := bbase (se 2 (by rfl) ⟨800676, by rfl⟩ : syracuseStep 2135137 = 1601353) (by norm_num)
theorem B2846849 : Blo 1897435 2846849 := bstep (se 2 (by rfl) ⟨1067568, by rfl⟩ : syracuseStep 2846849 = 2135137) B2135137
theorem B1897899 : Blo 1897435 1897899 := bstep (se 1 (by rfl) ⟨1423424, by rfl⟩ : syracuseStep 1897899 = 2846849) B2846849
theorem B4804069 : Blo 1897435 4804069 := bbase (se 4 (by rfl) ⟨450381, by rfl⟩ : syracuseStep 4804069 = 900763) (by norm_num)
theorem B6405425 : Blo 1897435 6405425 := bstep (se 2 (by rfl) ⟨2402034, by rfl⟩ : syracuseStep 6405425 = 4804069) B4804069
theorem B4270283 : Blo 1897435 4270283 := bstep (se 1 (by rfl) ⟨3202712, by rfl⟩ : syracuseStep 4270283 = 6405425) B6405425
theorem B2846855 : Blo 1897435 2846855 := bstep (se 1 (by rfl) ⟨2135141, by rfl⟩ : syracuseStep 2846855 = 4270283) B4270283
theorem B1897903 : Blo 1897435 1897903 := bstep (se 1 (by rfl) ⟨1423427, by rfl⟩ : syracuseStep 1897903 = 2846855) B2846855
theorem B2846861 : Blo 1897435 2846861 := bbase (se 3 (by rfl) ⟨533786, by rfl⟩ : syracuseStep 2846861 = 1067573) (by norm_num)
theorem B1897907 : Blo 1897435 1897907 := bstep (se 1 (by rfl) ⟨1423430, by rfl⟩ : syracuseStep 1897907 = 2846861) B2846861
theorem B4270301 : Blo 1897435 4270301 := bbase (se 3 (by rfl) ⟨800681, by rfl⟩ : syracuseStep 4270301 = 1601363) (by norm_num)
theorem B2846867 : Blo 1897435 2846867 := bstep (se 1 (by rfl) ⟨2135150, by rfl⟩ : syracuseStep 2846867 = 4270301) B4270301
theorem B1897911 : Blo 1897435 1897911 := bstep (se 1 (by rfl) ⟨1423433, by rfl⟩ : syracuseStep 1897911 = 2846867) B2846867
theorem B3202733 : Blo 1897435 3202733 := bbase (se 3 (by rfl) ⟨600512, by rfl⟩ : syracuseStep 3202733 = 1201025) (by norm_num)
theorem B2135155 : Blo 1897435 2135155 := bstep (se 1 (by rfl) ⟨1601366, by rfl⟩ : syracuseStep 2135155 = 3202733) B3202733
theorem B2846873 : Blo 1897435 2846873 := bstep (se 2 (by rfl) ⟨1067577, by rfl⟩ : syracuseStep 2846873 = 2135155) B2135155
theorem B1897915 : Blo 1897435 1897915 := bstep (se 1 (by rfl) ⟨1423436, by rfl⟩ : syracuseStep 1897915 = 2846873) B2846873
theorem B6163157 : Blo 1897435 6163157 := bbase (se 7 (by rfl) ⟨72224, by rfl⟩ : syracuseStep 6163157 = 144449) (by norm_num)
theorem B4108771 : Blo 1897435 4108771 := bstep (se 1 (by rfl) ⟨3081578, by rfl⟩ : syracuseStep 4108771 = 6163157) B6163157
theorem B5478361 : Blo 1897435 5478361 := bstep (se 2 (by rfl) ⟨2054385, by rfl⟩ : syracuseStep 5478361 = 4108771) B4108771
theorem B29217925 : Blo 1897435 29217925 := bstep (se 4 (by rfl) ⟨2739180, by rfl⟩ : syracuseStep 29217925 = 5478361) B5478361
theorem B38957233 : Blo 1897435 38957233 := bstep (se 2 (by rfl) ⟨14608962, by rfl⟩ : syracuseStep 38957233 = 29217925) B29217925
theorem B51942977 : Blo 1897435 51942977 := bstep (se 2 (by rfl) ⟨19478616, by rfl⟩ : syracuseStep 51942977 = 38957233) B38957233
theorem B34628651 : Blo 1897435 34628651 := bstep (se 1 (by rfl) ⟨25971488, by rfl⟩ : syracuseStep 34628651 = 51942977) B51942977
theorem B23085767 : Blo 1897435 23085767 := bstep (se 1 (by rfl) ⟨17314325, by rfl⟩ : syracuseStep 23085767 = 34628651) B34628651
theorem B61562045 : Blo 1897435 61562045 := bstep (se 3 (by rfl) ⟨11542883, by rfl⟩ : syracuseStep 61562045 = 23085767) B23085767
theorem B41041363 : Blo 1897435 41041363 := bstep (se 1 (by rfl) ⟨30781022, by rfl⟩ : syracuseStep 41041363 = 61562045) B61562045
theorem B54721817 : Blo 1897435 54721817 := bstep (se 2 (by rfl) ⟨20520681, by rfl⟩ : syracuseStep 54721817 = 41041363) B41041363
theorem B36481211 : Blo 1897435 36481211 := bstep (se 1 (by rfl) ⟨27360908, by rfl⟩ : syracuseStep 36481211 = 54721817) B54721817
theorem B24320807 : Blo 1897435 24320807 := bstep (se 1 (by rfl) ⟨18240605, by rfl⟩ : syracuseStep 24320807 = 36481211) B36481211
theorem B16213871 : Blo 1897435 16213871 := bstep (se 1 (by rfl) ⟨12160403, by rfl⟩ : syracuseStep 16213871 = 24320807) B24320807
theorem B10809247 : Blo 1897435 10809247 := bstep (se 1 (by rfl) ⟨8106935, by rfl⟩ : syracuseStep 10809247 = 16213871) B16213871
theorem B14412329 : Blo 1897435 14412329 := bstep (se 2 (by rfl) ⟨5404623, by rfl⟩ : syracuseStep 14412329 = 10809247) B10809247
theorem B9608219 : Blo 1897435 9608219 := bstep (se 1 (by rfl) ⟨7206164, by rfl⟩ : syracuseStep 9608219 = 14412329) B14412329
theorem B6405479 : Blo 1897435 6405479 := bstep (se 1 (by rfl) ⟨4804109, by rfl⟩ : syracuseStep 6405479 = 9608219) B9608219
theorem B4270319 : Blo 1897435 4270319 := bstep (se 1 (by rfl) ⟨3202739, by rfl⟩ : syracuseStep 4270319 = 6405479) B6405479
theorem B2846879 : Blo 1897435 2846879 := bstep (se 1 (by rfl) ⟨2135159, by rfl⟩ : syracuseStep 2846879 = 4270319) B4270319
theorem B1897919 : Blo 1897435 1897919 := bstep (se 1 (by rfl) ⟨1423439, by rfl⟩ : syracuseStep 1897919 = 2846879) B2846879
theorem B2846885 : Blo 1897435 2846885 := bbase (se 4 (by rfl) ⟨266895, by rfl⟩ : syracuseStep 2846885 = 533791) (by norm_num)
theorem B1897923 : Blo 1897435 1897923 := bstep (se 1 (by rfl) ⟨1423442, by rfl⟩ : syracuseStep 1897923 = 2846885) B2846885
theorem B2402065 : Blo 1897435 2402065 := bbase (se 2 (by rfl) ⟨900774, by rfl⟩ : syracuseStep 2402065 = 1801549) (by norm_num)
theorem B3202753 : Blo 1897435 3202753 := bstep (se 2 (by rfl) ⟨1201032, by rfl⟩ : syracuseStep 3202753 = 2402065) B2402065
theorem B4270337 : Blo 1897435 4270337 := bstep (se 2 (by rfl) ⟨1601376, by rfl⟩ : syracuseStep 4270337 = 3202753) B3202753
theorem B2846891 : Blo 1897435 2846891 := bstep (se 1 (by rfl) ⟨2135168, by rfl⟩ : syracuseStep 2846891 = 4270337) B4270337
theorem B1897927 : Blo 1897435 1897927 := bstep (se 1 (by rfl) ⟨1423445, by rfl⟩ : syracuseStep 1897927 = 2846891) B2846891
theorem B2135173 : Blo 1897435 2135173 := bbase (se 4 (by rfl) ⟨200172, by rfl⟩ : syracuseStep 2135173 = 400345) (by norm_num)
theorem B2846897 : Blo 1897435 2846897 := bstep (se 2 (by rfl) ⟨1067586, by rfl⟩ : syracuseStep 2846897 = 2135173) B2135173
theorem B1897931 : Blo 1897435 1897931 := bstep (se 1 (by rfl) ⟨1423448, by rfl⟩ : syracuseStep 1897931 = 2846897) B2846897
theorem B49305685 : Blo 1897435 49305685 := bbase (se 8 (by rfl) ⟨288900, by rfl⟩ : syracuseStep 49305685 = 577801) (by norm_num)
theorem B65740913 : Blo 1897435 65740913 := bstep (se 2 (by rfl) ⟨24652842, by rfl⟩ : syracuseStep 65740913 = 49305685) B49305685
theorem B43827275 : Blo 1897435 43827275 := bstep (se 1 (by rfl) ⟨32870456, by rfl⟩ : syracuseStep 43827275 = 65740913) B65740913
theorem B116872733 : Blo 1897435 116872733 := bstep (se 3 (by rfl) ⟨21913637, by rfl⟩ : syracuseStep 116872733 = 43827275) B43827275
theorem B77915155 : Blo 1897435 77915155 := bstep (se 1 (by rfl) ⟨58436366, by rfl⟩ : syracuseStep 77915155 = 116872733) B116872733
theorem B103886873 : Blo 1897435 103886873 := bstep (se 2 (by rfl) ⟨38957577, by rfl⟩ : syracuseStep 103886873 = 77915155) B77915155
theorem B69257915 : Blo 1897435 69257915 := bstep (se 1 (by rfl) ⟨51943436, by rfl⟩ : syracuseStep 69257915 = 103886873) B103886873
theorem B46171943 : Blo 1897435 46171943 := bstep (se 1 (by rfl) ⟨34628957, by rfl⟩ : syracuseStep 46171943 = 69257915) B69257915
theorem B30781295 : Blo 1897435 30781295 := bstep (se 1 (by rfl) ⟨23085971, by rfl⟩ : syracuseStep 30781295 = 46171943) B46171943
theorem B20520863 : Blo 1897435 20520863 := bstep (se 1 (by rfl) ⟨15390647, by rfl⟩ : syracuseStep 20520863 = 30781295) B30781295
theorem B13680575 : Blo 1897435 13680575 := bstep (se 1 (by rfl) ⟨10260431, by rfl⟩ : syracuseStep 13680575 = 20520863) B20520863
theorem B9120383 : Blo 1897435 9120383 := bstep (se 1 (by rfl) ⟨6840287, by rfl⟩ : syracuseStep 9120383 = 13680575) B13680575
theorem B6080255 : Blo 1897435 6080255 := bstep (se 1 (by rfl) ⟨4560191, by rfl⟩ : syracuseStep 6080255 = 9120383) B9120383
theorem B4053503 : Blo 1897435 4053503 := bstep (se 1 (by rfl) ⟨3040127, by rfl⟩ : syracuseStep 4053503 = 6080255) B6080255
theorem B2702335 : Blo 1897435 2702335 := bstep (se 1 (by rfl) ⟨2026751, by rfl⟩ : syracuseStep 2702335 = 4053503) B4053503
theorem B3603113 : Blo 1897435 3603113 := bstep (se 2 (by rfl) ⟨1351167, by rfl⟩ : syracuseStep 3603113 = 2702335) B2702335
theorem B2402075 : Blo 1897435 2402075 := bstep (se 1 (by rfl) ⟨1801556, by rfl⟩ : syracuseStep 2402075 = 3603113) B3603113
theorem B6405533 : Blo 1897435 6405533 := bstep (se 3 (by rfl) ⟨1201037, by rfl⟩ : syracuseStep 6405533 = 2402075) B2402075
theorem B4270355 : Blo 1897435 4270355 := bstep (se 1 (by rfl) ⟨3202766, by rfl⟩ : syracuseStep 4270355 = 6405533) B6405533
theorem B2846903 : Blo 1897435 2846903 := bstep (se 1 (by rfl) ⟨2135177, by rfl⟩ : syracuseStep 2846903 = 4270355) B4270355
theorem B1897935 : Blo 1897435 1897935 := bstep (se 1 (by rfl) ⟨1423451, by rfl⟩ : syracuseStep 1897935 = 2846903) B2846903
theorem B2846909 : Blo 1897435 2846909 := bbase (se 3 (by rfl) ⟨533795, by rfl⟩ : syracuseStep 2846909 = 1067591) (by norm_num)
theorem B1897939 : Blo 1897435 1897939 := bstep (se 1 (by rfl) ⟨1423454, by rfl⟩ : syracuseStep 1897939 = 2846909) B2846909
theorem B4270373 : Blo 1897435 4270373 := bbase (se 4 (by rfl) ⟨400347, by rfl⟩ : syracuseStep 4270373 = 800695) (by norm_num)
theorem B2846915 : Blo 1897435 2846915 := bstep (se 1 (by rfl) ⟨2135186, by rfl⟩ : syracuseStep 2846915 = 4270373) B4270373
theorem B1897943 : Blo 1897435 1897943 := bstep (se 1 (by rfl) ⟨1423457, by rfl⟩ : syracuseStep 1897943 = 2846915) B2846915
theorem B4804181 : Blo 1897435 4804181 := bbase (se 8 (by rfl) ⟨28149, by rfl⟩ : syracuseStep 4804181 = 56299) (by norm_num)
theorem B3202787 : Blo 1897435 3202787 := bstep (se 1 (by rfl) ⟨2402090, by rfl⟩ : syracuseStep 3202787 = 4804181) B4804181
theorem B2135191 : Blo 1897435 2135191 := bstep (se 1 (by rfl) ⟨1601393, by rfl⟩ : syracuseStep 2135191 = 3202787) B3202787
theorem B2846921 : Blo 1897435 2846921 := bstep (se 2 (by rfl) ⟨1067595, by rfl⟩ : syracuseStep 2846921 = 2135191) B2135191
theorem B1897947 : Blo 1897435 1897947 := bstep (se 1 (by rfl) ⟨1423460, by rfl⟩ : syracuseStep 1897947 = 2846921) B2846921
theorem B4560229 : Blo 1897435 4560229 := bbase (se 4 (by rfl) ⟨427521, by rfl⟩ : syracuseStep 4560229 = 855043) (by norm_num)
theorem B6080305 : Blo 1897435 6080305 := bstep (se 2 (by rfl) ⟨2280114, by rfl⟩ : syracuseStep 6080305 = 4560229) B4560229
theorem B8107073 : Blo 1897435 8107073 := bstep (se 2 (by rfl) ⟨3040152, by rfl⟩ : syracuseStep 8107073 = 6080305) B6080305
theorem B5404715 : Blo 1897435 5404715 := bstep (se 1 (by rfl) ⟨4053536, by rfl⟩ : syracuseStep 5404715 = 8107073) B8107073
theorem B3603143 : Blo 1897435 3603143 := bstep (se 1 (by rfl) ⟨2702357, by rfl⟩ : syracuseStep 3603143 = 5404715) B5404715
theorem B9608381 : Blo 1897435 9608381 := bstep (se 3 (by rfl) ⟨1801571, by rfl⟩ : syracuseStep 9608381 = 3603143) B3603143
theorem B6405587 : Blo 1897435 6405587 := bstep (se 1 (by rfl) ⟨4804190, by rfl⟩ : syracuseStep 6405587 = 9608381) B9608381
theorem B4270391 : Blo 1897435 4270391 := bstep (se 1 (by rfl) ⟨3202793, by rfl⟩ : syracuseStep 4270391 = 6405587) B6405587
theorem B2846927 : Blo 1897435 2846927 := bstep (se 1 (by rfl) ⟨2135195, by rfl⟩ : syracuseStep 2846927 = 4270391) B4270391
theorem B1897951 : Blo 1897435 1897951 := bstep (se 1 (by rfl) ⟨1423463, by rfl⟩ : syracuseStep 1897951 = 2846927) B2846927
theorem B2846933 : Blo 1897435 2846933 := bbase (se 7 (by rfl) ⟨33362, by rfl⟩ : syracuseStep 2846933 = 66725) (by norm_num)
theorem B1897955 : Blo 1897435 1897955 := bstep (se 1 (by rfl) ⟨1423466, by rfl⟩ : syracuseStep 1897955 = 2846933) B2846933
theorem B2026777 : Blo 1897435 2026777 := bbase (se 2 (by rfl) ⟨760041, by rfl⟩ : syracuseStep 2026777 = 1520083) (by norm_num)
theorem B2702369 : Blo 1897435 2702369 := bstep (se 2 (by rfl) ⟨1013388, by rfl⟩ : syracuseStep 2702369 = 2026777) B2026777
theorem B7206317 : Blo 1897435 7206317 := bstep (se 3 (by rfl) ⟨1351184, by rfl⟩ : syracuseStep 7206317 = 2702369) B2702369
theorem B4804211 : Blo 1897435 4804211 := bstep (se 1 (by rfl) ⟨3603158, by rfl⟩ : syracuseStep 4804211 = 7206317) B7206317
theorem B3202807 : Blo 1897435 3202807 := bstep (se 1 (by rfl) ⟨2402105, by rfl⟩ : syracuseStep 3202807 = 4804211) B4804211
theorem B4270409 : Blo 1897435 4270409 := bstep (se 2 (by rfl) ⟨1601403, by rfl⟩ : syracuseStep 4270409 = 3202807) B3202807
theorem B2846939 : Blo 1897435 2846939 := bstep (se 1 (by rfl) ⟨2135204, by rfl⟩ : syracuseStep 2846939 = 4270409) B4270409
theorem B1897959 : Blo 1897435 1897959 := bstep (se 1 (by rfl) ⟨1423469, by rfl⟩ : syracuseStep 1897959 = 2846939) B2846939
theorem B2135209 : Blo 1897435 2135209 := bbase (se 2 (by rfl) ⟨800703, by rfl⟩ : syracuseStep 2135209 = 1601407) (by norm_num)
theorem B2846945 : Blo 1897435 2846945 := bstep (se 2 (by rfl) ⟨1067604, by rfl⟩ : syracuseStep 2846945 = 2135209) B2135209
theorem B1897963 : Blo 1897435 1897963 := bstep (se 1 (by rfl) ⟨1423472, by rfl⟩ : syracuseStep 1897963 = 2846945) B2846945
theorem B8107141 : Blo 1897435 8107141 := bbase (se 4 (by rfl) ⟨760044, by rfl⟩ : syracuseStep 8107141 = 1520089) (by norm_num)
theorem B10809521 : Blo 1897435 10809521 := bstep (se 2 (by rfl) ⟨4053570, by rfl⟩ : syracuseStep 10809521 = 8107141) B8107141
theorem B7206347 : Blo 1897435 7206347 := bstep (se 1 (by rfl) ⟨5404760, by rfl⟩ : syracuseStep 7206347 = 10809521) B10809521
theorem B4804231 : Blo 1897435 4804231 := bstep (se 1 (by rfl) ⟨3603173, by rfl⟩ : syracuseStep 4804231 = 7206347) B7206347
theorem B6405641 : Blo 1897435 6405641 := bstep (se 2 (by rfl) ⟨2402115, by rfl⟩ : syracuseStep 6405641 = 4804231) B4804231
theorem B4270427 : Blo 1897435 4270427 := bstep (se 1 (by rfl) ⟨3202820, by rfl⟩ : syracuseStep 4270427 = 6405641) B6405641
theorem B2846951 : Blo 1897435 2846951 := bstep (se 1 (by rfl) ⟨2135213, by rfl⟩ : syracuseStep 2846951 = 4270427) B4270427
theorem B1897967 : Blo 1897435 1897967 := bstep (se 1 (by rfl) ⟨1423475, by rfl⟩ : syracuseStep 1897967 = 2846951) B2846951
theorem B2846957 : Blo 1897435 2846957 := bbase (se 3 (by rfl) ⟨533804, by rfl⟩ : syracuseStep 2846957 = 1067609) (by norm_num)
theorem B1897971 : Blo 1897435 1897971 := bstep (se 1 (by rfl) ⟨1423478, by rfl⟩ : syracuseStep 1897971 = 2846957) B2846957
theorem B4270445 : Blo 1897435 4270445 := bbase (se 3 (by rfl) ⟨800708, by rfl⟩ : syracuseStep 4270445 = 1601417) (by norm_num)
theorem B2846963 : Blo 1897435 2846963 := bstep (se 1 (by rfl) ⟨2135222, by rfl⟩ : syracuseStep 2846963 = 4270445) B4270445
theorem B1897975 : Blo 1897435 1897975 := bstep (se 1 (by rfl) ⟨1423481, by rfl⟩ : syracuseStep 1897975 = 2846963) B2846963
theorem B3603197 : Blo 1897435 3603197 := bbase (se 3 (by rfl) ⟨675599, by rfl⟩ : syracuseStep 3603197 = 1351199) (by norm_num)
theorem B2402131 : Blo 1897435 2402131 := bstep (se 1 (by rfl) ⟨1801598, by rfl⟩ : syracuseStep 2402131 = 3603197) B3603197
theorem B3202841 : Blo 1897435 3202841 := bstep (se 2 (by rfl) ⟨1201065, by rfl⟩ : syracuseStep 3202841 = 2402131) B2402131
theorem B2135227 : Blo 1897435 2135227 := bstep (se 1 (by rfl) ⟨1601420, by rfl⟩ : syracuseStep 2135227 = 3202841) B3202841
theorem B2846969 : Blo 1897435 2846969 := bstep (se 2 (by rfl) ⟨1067613, by rfl⟩ : syracuseStep 2846969 = 2135227) B2135227
theorem B1897979 : Blo 1897435 1897979 := bstep (se 1 (by rfl) ⟨1423484, by rfl⟩ : syracuseStep 1897979 = 2846969) B2846969
theorem B3420229 : Blo 1897435 3420229 := bbase (se 4 (by rfl) ⟨320646, by rfl⟩ : syracuseStep 3420229 = 641293) (by norm_num)
theorem B4560305 : Blo 1897435 4560305 := bstep (se 2 (by rfl) ⟨1710114, by rfl⟩ : syracuseStep 4560305 = 3420229) B3420229
theorem B48643253 : Blo 1897435 48643253 := bstep (se 5 (by rfl) ⟨2280152, by rfl⟩ : syracuseStep 48643253 = 4560305) B4560305
theorem B32428835 : Blo 1897435 32428835 := bstep (se 1 (by rfl) ⟨24321626, by rfl⟩ : syracuseStep 32428835 = 48643253) B48643253
theorem B21619223 : Blo 1897435 21619223 := bstep (se 1 (by rfl) ⟨16214417, by rfl⟩ : syracuseStep 21619223 = 32428835) B32428835
theorem B14412815 : Blo 1897435 14412815 := bstep (se 1 (by rfl) ⟨10809611, by rfl⟩ : syracuseStep 14412815 = 21619223) B21619223
theorem B9608543 : Blo 1897435 9608543 := bstep (se 1 (by rfl) ⟨7206407, by rfl⟩ : syracuseStep 9608543 = 14412815) B14412815
theorem B6405695 : Blo 1897435 6405695 := bstep (se 1 (by rfl) ⟨4804271, by rfl⟩ : syracuseStep 6405695 = 9608543) B9608543
theorem B4270463 : Blo 1897435 4270463 := bstep (se 1 (by rfl) ⟨3202847, by rfl⟩ : syracuseStep 4270463 = 6405695) B6405695
theorem B2846975 : Blo 1897435 2846975 := bstep (se 1 (by rfl) ⟨2135231, by rfl⟩ : syracuseStep 2846975 = 4270463) B4270463
theorem B1897983 : Blo 1897435 1897983 := bstep (se 1 (by rfl) ⟨1423487, by rfl⟩ : syracuseStep 1897983 = 2846975) B2846975
theorem B2846981 : Blo 1897435 2846981 := bbase (se 4 (by rfl) ⟨266904, by rfl⟩ : syracuseStep 2846981 = 533809) (by norm_num)
theorem B1897987 : Blo 1897435 1897987 := bstep (se 1 (by rfl) ⟨1423490, by rfl⟩ : syracuseStep 1897987 = 2846981) B2846981
theorem B3202861 : Blo 1897435 3202861 := bbase (se 3 (by rfl) ⟨600536, by rfl⟩ : syracuseStep 3202861 = 1201073) (by norm_num)
theorem B4270481 : Blo 1897435 4270481 := bstep (se 2 (by rfl) ⟨1601430, by rfl⟩ : syracuseStep 4270481 = 3202861) B3202861
theorem B2846987 : Blo 1897435 2846987 := bstep (se 1 (by rfl) ⟨2135240, by rfl⟩ : syracuseStep 2846987 = 4270481) B4270481
theorem B1897991 : Blo 1897435 1897991 := bstep (se 1 (by rfl) ⟨1423493, by rfl⟩ : syracuseStep 1897991 = 2846987) B2846987
theorem B2135245 : Blo 1897435 2135245 := bbase (se 3 (by rfl) ⟨400358, by rfl⟩ : syracuseStep 2135245 = 800717) (by norm_num)
theorem B2846993 : Blo 1897435 2846993 := bstep (se 2 (by rfl) ⟨1067622, by rfl⟩ : syracuseStep 2846993 = 2135245) B2135245
theorem B1897995 : Blo 1897435 1897995 := bstep (se 1 (by rfl) ⟨1423496, by rfl⟩ : syracuseStep 1897995 = 2846993) B2846993
theorem B6405749 : Blo 1897435 6405749 := bbase (se 5 (by rfl) ⟨300269, by rfl⟩ : syracuseStep 6405749 = 600539) (by norm_num)
theorem B4270499 : Blo 1897435 4270499 := bstep (se 1 (by rfl) ⟨3202874, by rfl⟩ : syracuseStep 4270499 = 6405749) B6405749
theorem B2846999 : Blo 1897435 2846999 := bstep (se 1 (by rfl) ⟨2135249, by rfl⟩ : syracuseStep 2846999 = 4270499) B4270499
theorem B1897999 : Blo 1897435 1897999 := bstep (se 1 (by rfl) ⟨1423499, by rfl⟩ : syracuseStep 1897999 = 2846999) B2846999
theorem B2847005 : Blo 1897435 2847005 := bbase (se 3 (by rfl) ⟨533813, by rfl⟩ : syracuseStep 2847005 = 1067627) (by norm_num)
theorem B1898003 : Blo 1897435 1898003 := bstep (se 1 (by rfl) ⟨1423502, by rfl⟩ : syracuseStep 1898003 = 2847005) B2847005
theorem B4270517 : Blo 1897435 4270517 := bbase (se 5 (by rfl) ⟨200180, by rfl⟩ : syracuseStep 4270517 = 400361) (by norm_num)
theorem B2847011 : Blo 1897435 2847011 := bstep (se 1 (by rfl) ⟨2135258, by rfl⟩ : syracuseStep 2847011 = 4270517) B4270517
theorem B1898007 : Blo 1897435 1898007 := bstep (se 1 (by rfl) ⟨1423505, by rfl⟩ : syracuseStep 1898007 = 2847011) B2847011
theorem B4622597 : Blo 1897435 4622597 := bbase (se 4 (by rfl) ⟨433368, by rfl⟩ : syracuseStep 4622597 = 866737) (by norm_num)
theorem B3081731 : Blo 1897435 3081731 := bstep (se 1 (by rfl) ⟨2311298, by rfl⟩ : syracuseStep 3081731 = 4622597) B4622597
theorem B8217949 : Blo 1897435 8217949 := bstep (se 3 (by rfl) ⟨1540865, by rfl⟩ : syracuseStep 8217949 = 3081731) B3081731
theorem B10957265 : Blo 1897435 10957265 := bstep (se 2 (by rfl) ⟨4108974, by rfl⟩ : syracuseStep 10957265 = 8217949) B8217949
theorem B7304843 : Blo 1897435 7304843 := bstep (se 1 (by rfl) ⟨5478632, by rfl⟩ : syracuseStep 7304843 = 10957265) B10957265
theorem B4869895 : Blo 1897435 4869895 := bstep (se 1 (by rfl) ⟨3652421, by rfl⟩ : syracuseStep 4869895 = 7304843) B7304843
theorem B6493193 : Blo 1897435 6493193 := bstep (se 2 (by rfl) ⟨2434947, by rfl⟩ : syracuseStep 6493193 = 4869895) B4869895
theorem B4328795 : Blo 1897435 4328795 := bstep (se 1 (by rfl) ⟨3246596, by rfl⟩ : syracuseStep 4328795 = 6493193) B6493193
theorem B2885863 : Blo 1897435 2885863 := bstep (se 1 (by rfl) ⟨2164397, by rfl⟩ : syracuseStep 2885863 = 4328795) B4328795
theorem B3847817 : Blo 1897435 3847817 := bstep (se 2 (by rfl) ⟨1442931, by rfl⟩ : syracuseStep 3847817 = 2885863) B2885863
theorem B2565211 : Blo 1897435 2565211 := bstep (se 1 (by rfl) ⟨1923908, by rfl⟩ : syracuseStep 2565211 = 3847817) B3847817
theorem B3420281 : Blo 1897435 3420281 := bstep (se 2 (by rfl) ⟨1282605, by rfl⟩ : syracuseStep 3420281 = 2565211) B2565211
theorem B2280187 : Blo 1897435 2280187 := bstep (se 1 (by rfl) ⟨1710140, by rfl⟩ : syracuseStep 2280187 = 3420281) B3420281
theorem B3040249 : Blo 1897435 3040249 := bstep (se 2 (by rfl) ⟨1140093, by rfl⟩ : syracuseStep 3040249 = 2280187) B2280187
theorem B4053665 : Blo 1897435 4053665 := bstep (se 2 (by rfl) ⟨1520124, by rfl⟩ : syracuseStep 4053665 = 3040249) B3040249
theorem B10809773 : Blo 1897435 10809773 := bstep (se 3 (by rfl) ⟨2026832, by rfl⟩ : syracuseStep 10809773 = 4053665) B4053665
theorem B7206515 : Blo 1897435 7206515 := bstep (se 1 (by rfl) ⟨5404886, by rfl⟩ : syracuseStep 7206515 = 10809773) B10809773
theorem B4804343 : Blo 1897435 4804343 := bstep (se 1 (by rfl) ⟨3603257, by rfl⟩ : syracuseStep 4804343 = 7206515) B7206515
theorem B3202895 : Blo 1897435 3202895 := bstep (se 1 (by rfl) ⟨2402171, by rfl⟩ : syracuseStep 3202895 = 4804343) B4804343
theorem B2135263 : Blo 1897435 2135263 := bstep (se 1 (by rfl) ⟨1601447, by rfl⟩ : syracuseStep 2135263 = 3202895) B3202895
theorem B2847017 : Blo 1897435 2847017 := bstep (se 2 (by rfl) ⟨1067631, by rfl⟩ : syracuseStep 2847017 = 2135263) B2135263
theorem B1898011 : Blo 1897435 1898011 := bstep (se 1 (by rfl) ⟨1423508, by rfl⟩ : syracuseStep 1898011 = 2847017) B2847017
theorem B116877653 : Blo 1897435 116877653 := bbase (se 10 (by rfl) ⟨171207, by rfl⟩ : syracuseStep 116877653 = 342415) (by norm_num)
theorem B77918435 : Blo 1897435 77918435 := bstep (se 1 (by rfl) ⟨58438826, by rfl⟩ : syracuseStep 77918435 = 116877653) B116877653
theorem B51945623 : Blo 1897435 51945623 := bstep (se 1 (by rfl) ⟨38959217, by rfl⟩ : syracuseStep 51945623 = 77918435) B77918435
theorem B34630415 : Blo 1897435 34630415 := bstep (se 1 (by rfl) ⟨25972811, by rfl⟩ : syracuseStep 34630415 = 51945623) B51945623
theorem B23086943 : Blo 1897435 23086943 := bstep (se 1 (by rfl) ⟨17315207, by rfl⟩ : syracuseStep 23086943 = 34630415) B34630415
theorem B15391295 : Blo 1897435 15391295 := bstep (se 1 (by rfl) ⟨11543471, by rfl⟩ : syracuseStep 15391295 = 23086943) B23086943
theorem B10260863 : Blo 1897435 10260863 := bstep (se 1 (by rfl) ⟨7695647, by rfl⟩ : syracuseStep 10260863 = 15391295) B15391295
theorem B6840575 : Blo 1897435 6840575 := bstep (se 1 (by rfl) ⟨5130431, by rfl⟩ : syracuseStep 6840575 = 10260863) B10260863
theorem B4560383 : Blo 1897435 4560383 := bstep (se 1 (by rfl) ⟨3420287, by rfl⟩ : syracuseStep 4560383 = 6840575) B6840575
theorem B3040255 : Blo 1897435 3040255 := bstep (se 1 (by rfl) ⟨2280191, by rfl⟩ : syracuseStep 3040255 = 4560383) B4560383
theorem B4053673 : Blo 1897435 4053673 := bstep (se 2 (by rfl) ⟨1520127, by rfl⟩ : syracuseStep 4053673 = 3040255) B3040255
theorem B5404897 : Blo 1897435 5404897 := bstep (se 2 (by rfl) ⟨2026836, by rfl⟩ : syracuseStep 5404897 = 4053673) B4053673
theorem B7206529 : Blo 1897435 7206529 := bstep (se 2 (by rfl) ⟨2702448, by rfl⟩ : syracuseStep 7206529 = 5404897) B5404897
theorem B9608705 : Blo 1897435 9608705 := bstep (se 2 (by rfl) ⟨3603264, by rfl⟩ : syracuseStep 9608705 = 7206529) B7206529
theorem B6405803 : Blo 1897435 6405803 := bstep (se 1 (by rfl) ⟨4804352, by rfl⟩ : syracuseStep 6405803 = 9608705) B9608705
theorem B4270535 : Blo 1897435 4270535 := bstep (se 1 (by rfl) ⟨3202901, by rfl⟩ : syracuseStep 4270535 = 6405803) B6405803
theorem B2847023 : Blo 1897435 2847023 := bstep (se 1 (by rfl) ⟨2135267, by rfl⟩ : syracuseStep 2847023 = 4270535) B4270535
theorem B1898015 : Blo 1897435 1898015 := bstep (se 1 (by rfl) ⟨1423511, by rfl⟩ : syracuseStep 1898015 = 2847023) B2847023
theorem B2847029 : Blo 1897435 2847029 := bbase (se 5 (by rfl) ⟨133454, by rfl⟩ : syracuseStep 2847029 = 266909) (by norm_num)
theorem B1898019 : Blo 1897435 1898019 := bstep (se 1 (by rfl) ⟨1423514, by rfl⟩ : syracuseStep 1898019 = 2847029) B2847029
theorem B4804373 : Blo 1897435 4804373 := bbase (se 6 (by rfl) ⟨112602, by rfl⟩ : syracuseStep 4804373 = 225205) (by norm_num)
theorem B3202915 : Blo 1897435 3202915 := bstep (se 1 (by rfl) ⟨2402186, by rfl⟩ : syracuseStep 3202915 = 4804373) B4804373
theorem B4270553 : Blo 1897435 4270553 := bstep (se 2 (by rfl) ⟨1601457, by rfl⟩ : syracuseStep 4270553 = 3202915) B3202915
theorem B2847035 : Blo 1897435 2847035 := bstep (se 1 (by rfl) ⟨2135276, by rfl⟩ : syracuseStep 2847035 = 4270553) B4270553
theorem B1898023 : Blo 1897435 1898023 := bstep (se 1 (by rfl) ⟨1423517, by rfl⟩ : syracuseStep 1898023 = 2847035) B2847035
theorem B2135281 : Blo 1897435 2135281 := bbase (se 2 (by rfl) ⟨800730, by rfl⟩ : syracuseStep 2135281 = 1601461) (by norm_num)
theorem B2847041 : Blo 1897435 2847041 := bstep (se 2 (by rfl) ⟨1067640, by rfl⟩ : syracuseStep 2847041 = 2135281) B2135281
theorem B1898027 : Blo 1897435 1898027 := bstep (se 1 (by rfl) ⟨1423520, by rfl⟩ : syracuseStep 1898027 = 2847041) B2847041
theorem B18241685 : Blo 1897435 18241685 := bbase (se 6 (by rfl) ⟨427539, by rfl⟩ : syracuseStep 18241685 = 855079) (by norm_num)
theorem B12161123 : Blo 1897435 12161123 := bstep (se 1 (by rfl) ⟨9120842, by rfl⟩ : syracuseStep 12161123 = 18241685) B18241685
theorem B8107415 : Blo 1897435 8107415 := bstep (se 1 (by rfl) ⟨6080561, by rfl⟩ : syracuseStep 8107415 = 12161123) B12161123
theorem B5404943 : Blo 1897435 5404943 := bstep (se 1 (by rfl) ⟨4053707, by rfl⟩ : syracuseStep 5404943 = 8107415) B8107415
theorem B3603295 : Blo 1897435 3603295 := bstep (se 1 (by rfl) ⟨2702471, by rfl⟩ : syracuseStep 3603295 = 5404943) B5404943
theorem B4804393 : Blo 1897435 4804393 := bstep (se 2 (by rfl) ⟨1801647, by rfl⟩ : syracuseStep 4804393 = 3603295) B3603295
theorem B6405857 : Blo 1897435 6405857 := bstep (se 2 (by rfl) ⟨2402196, by rfl⟩ : syracuseStep 6405857 = 4804393) B4804393
theorem B4270571 : Blo 1897435 4270571 := bstep (se 1 (by rfl) ⟨3202928, by rfl⟩ : syracuseStep 4270571 = 6405857) B6405857
theorem B2847047 : Blo 1897435 2847047 := bstep (se 1 (by rfl) ⟨2135285, by rfl⟩ : syracuseStep 2847047 = 4270571) B4270571
theorem B1898031 : Blo 1897435 1898031 := bstep (se 1 (by rfl) ⟨1423523, by rfl⟩ : syracuseStep 1898031 = 2847047) B2847047
theorem B2847053 : Blo 1897435 2847053 := bbase (se 3 (by rfl) ⟨533822, by rfl⟩ : syracuseStep 2847053 = 1067645) (by norm_num)
theorem B1898035 : Blo 1897435 1898035 := bstep (se 1 (by rfl) ⟨1423526, by rfl⟩ : syracuseStep 1898035 = 2847053) B2847053
theorem B4270589 : Blo 1897435 4270589 := bbase (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) (by norm_num)
theorem B2847059 : Blo 1897435 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B1898039 : Blo 1897435 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B3202949 : Blo 1897435 3202949 := bbase (se 4 (by rfl) ⟨300276, by rfl⟩ : syracuseStep 3202949 = 600553) (by norm_num)
theorem B2135299 : Blo 1897435 2135299 := bstep (se 1 (by rfl) ⟨1601474, by rfl⟩ : syracuseStep 2135299 = 3202949) B3202949
theorem B2847065 : Blo 1897435 2847065 := bstep (se 2 (by rfl) ⟨1067649, by rfl⟩ : syracuseStep 2847065 = 2135299) B2135299
theorem B1898043 : Blo 1897435 1898043 := bstep (se 1 (by rfl) ⟨1423532, by rfl⟩ : syracuseStep 1898043 = 2847065) B2847065
theorem B14413301 : Blo 1897435 14413301 := bbase (se 5 (by rfl) ⟨675623, by rfl⟩ : syracuseStep 14413301 = 1351247) (by norm_num)
theorem B9608867 : Blo 1897435 9608867 := bstep (se 1 (by rfl) ⟨7206650, by rfl⟩ : syracuseStep 9608867 = 14413301) B14413301
theorem B6405911 : Blo 1897435 6405911 := bstep (se 1 (by rfl) ⟨4804433, by rfl⟩ : syracuseStep 6405911 = 9608867) B9608867
theorem B4270607 : Blo 1897435 4270607 := bstep (se 1 (by rfl) ⟨3202955, by rfl⟩ : syracuseStep 4270607 = 6405911) B6405911
theorem B2847071 : Blo 1897435 2847071 := bstep (se 1 (by rfl) ⟨2135303, by rfl⟩ : syracuseStep 2847071 = 4270607) B4270607
theorem B1898047 : Blo 1897435 1898047 := bstep (se 1 (by rfl) ⟨1423535, by rfl⟩ : syracuseStep 1898047 = 2847071) B2847071
theorem B2847077 : Blo 1897435 2847077 := bbase (se 4 (by rfl) ⟨266913, by rfl⟩ : syracuseStep 2847077 = 533827) (by norm_num)
theorem B1898051 : Blo 1897435 1898051 := bstep (se 1 (by rfl) ⟨1423538, by rfl⟩ : syracuseStep 1898051 = 2847077) B2847077
theorem B3603341 : Blo 1897435 3603341 := bbase (se 3 (by rfl) ⟨675626, by rfl⟩ : syracuseStep 3603341 = 1351253) (by norm_num)
theorem B2402227 : Blo 1897435 2402227 := bstep (se 1 (by rfl) ⟨1801670, by rfl⟩ : syracuseStep 2402227 = 3603341) B3603341
theorem B3202969 : Blo 1897435 3202969 := bstep (se 2 (by rfl) ⟨1201113, by rfl⟩ : syracuseStep 3202969 = 2402227) B2402227
theorem B4270625 : Blo 1897435 4270625 := bstep (se 2 (by rfl) ⟨1601484, by rfl⟩ : syracuseStep 4270625 = 3202969) B3202969
theorem B2847083 : Blo 1897435 2847083 := bstep (se 1 (by rfl) ⟨2135312, by rfl⟩ : syracuseStep 2847083 = 4270625) B4270625
theorem B1898055 : Blo 1897435 1898055 := bstep (se 1 (by rfl) ⟨1423541, by rfl⟩ : syracuseStep 1898055 = 2847083) B2847083
theorem B2135317 : Blo 1897435 2135317 := bbase (se 6 (by rfl) ⟨50046, by rfl⟩ : syracuseStep 2135317 = 100093) (by norm_num)
theorem B2847089 : Blo 1897435 2847089 := bstep (se 2 (by rfl) ⟨1067658, by rfl⟩ : syracuseStep 2847089 = 2135317) B2135317
theorem B1898059 : Blo 1897435 1898059 := bstep (se 1 (by rfl) ⟨1423544, by rfl⟩ : syracuseStep 1898059 = 2847089) B2847089
theorem B2402237 : Blo 1897435 2402237 := bbase (se 3 (by rfl) ⟨450419, by rfl⟩ : syracuseStep 2402237 = 900839) (by norm_num)
theorem B6405965 : Blo 1897435 6405965 := bstep (se 3 (by rfl) ⟨1201118, by rfl⟩ : syracuseStep 6405965 = 2402237) B2402237
theorem B4270643 : Blo 1897435 4270643 := bstep (se 1 (by rfl) ⟨3202982, by rfl⟩ : syracuseStep 4270643 = 6405965) B6405965
theorem B2847095 : Blo 1897435 2847095 := bstep (se 1 (by rfl) ⟨2135321, by rfl⟩ : syracuseStep 2847095 = 4270643) B4270643
theorem B1898063 : Blo 1897435 1898063 := bstep (se 1 (by rfl) ⟨1423547, by rfl⟩ : syracuseStep 1898063 = 2847095) B2847095
theorem B2847101 : Blo 1897435 2847101 := bbase (se 3 (by rfl) ⟨533831, by rfl⟩ : syracuseStep 2847101 = 1067663) (by norm_num)
theorem B1898067 : Blo 1897435 1898067 := bstep (se 1 (by rfl) ⟨1423550, by rfl⟩ : syracuseStep 1898067 = 2847101) B2847101
theorem B4270661 : Blo 1897435 4270661 := bbase (se 4 (by rfl) ⟨400374, by rfl⟩ : syracuseStep 4270661 = 800749) (by norm_num)
theorem B2847107 : Blo 1897435 2847107 := bstep (se 1 (by rfl) ⟨2135330, by rfl⟩ : syracuseStep 2847107 = 4270661) B4270661
theorem B1898071 : Blo 1897435 1898071 := bstep (se 1 (by rfl) ⟨1423553, by rfl⟩ : syracuseStep 1898071 = 2847107) B2847107
theorem B2026901 : Blo 1897435 2026901 := bbase (se 6 (by rfl) ⟨47505, by rfl⟩ : syracuseStep 2026901 = 95011) (by norm_num)
theorem B5405069 : Blo 1897435 5405069 := bstep (se 3 (by rfl) ⟨1013450, by rfl⟩ : syracuseStep 5405069 = 2026901) B2026901
theorem B3603379 : Blo 1897435 3603379 := bstep (se 1 (by rfl) ⟨2702534, by rfl⟩ : syracuseStep 3603379 = 5405069) B5405069
theorem B4804505 : Blo 1897435 4804505 := bstep (se 2 (by rfl) ⟨1801689, by rfl⟩ : syracuseStep 4804505 = 3603379) B3603379
theorem B3203003 : Blo 1897435 3203003 := bstep (se 1 (by rfl) ⟨2402252, by rfl⟩ : syracuseStep 3203003 = 4804505) B4804505
theorem B2135335 : Blo 1897435 2135335 := bstep (se 1 (by rfl) ⟨1601501, by rfl⟩ : syracuseStep 2135335 = 3203003) B3203003
theorem B2847113 : Blo 1897435 2847113 := bstep (se 2 (by rfl) ⟨1067667, by rfl⟩ : syracuseStep 2847113 = 2135335) B2135335
theorem B1898075 : Blo 1897435 1898075 := bstep (se 1 (by rfl) ⟨1423556, by rfl⟩ : syracuseStep 1898075 = 2847113) B2847113
theorem B9609029 : Blo 1897435 9609029 := bbase (se 4 (by rfl) ⟨900846, by rfl⟩ : syracuseStep 9609029 = 1801693) (by norm_num)
theorem B6406019 : Blo 1897435 6406019 := bstep (se 1 (by rfl) ⟨4804514, by rfl⟩ : syracuseStep 6406019 = 9609029) B9609029
theorem B4270679 : Blo 1897435 4270679 := bstep (se 1 (by rfl) ⟨3203009, by rfl⟩ : syracuseStep 4270679 = 6406019) B6406019
theorem B2847119 : Blo 1897435 2847119 := bstep (se 1 (by rfl) ⟨2135339, by rfl⟩ : syracuseStep 2847119 = 4270679) B4270679
theorem B1898079 : Blo 1897435 1898079 := bstep (se 1 (by rfl) ⟨1423559, by rfl⟩ : syracuseStep 1898079 = 2847119) B2847119
theorem B2847125 : Blo 1897435 2847125 := bbase (se 6 (by rfl) ⟨66729, by rfl⟩ : syracuseStep 2847125 = 133459) (by norm_num)
theorem B1898083 : Blo 1897435 1898083 := bstep (se 1 (by rfl) ⟨1423562, by rfl⟩ : syracuseStep 1898083 = 2847125) B2847125
theorem B6080741 : Blo 1897435 6080741 := bbase (se 4 (by rfl) ⟨570069, by rfl⟩ : syracuseStep 6080741 = 1140139) (by norm_num)
theorem B4053827 : Blo 1897435 4053827 := bstep (se 1 (by rfl) ⟨3040370, by rfl⟩ : syracuseStep 4053827 = 6080741) B6080741
theorem B10810205 : Blo 1897435 10810205 := bstep (se 3 (by rfl) ⟨2026913, by rfl⟩ : syracuseStep 10810205 = 4053827) B4053827
theorem B7206803 : Blo 1897435 7206803 := bstep (se 1 (by rfl) ⟨5405102, by rfl⟩ : syracuseStep 7206803 = 10810205) B10810205
theorem B4804535 : Blo 1897435 4804535 := bstep (se 1 (by rfl) ⟨3603401, by rfl⟩ : syracuseStep 4804535 = 7206803) B7206803
theorem B3203023 : Blo 1897435 3203023 := bstep (se 1 (by rfl) ⟨2402267, by rfl⟩ : syracuseStep 3203023 = 4804535) B4804535
theorem B4270697 : Blo 1897435 4270697 := bstep (se 2 (by rfl) ⟨1601511, by rfl⟩ : syracuseStep 4270697 = 3203023) B3203023
theorem B2847131 : Blo 1897435 2847131 := bstep (se 1 (by rfl) ⟨2135348, by rfl⟩ : syracuseStep 2847131 = 4270697) B4270697
theorem B1898087 : Blo 1897435 1898087 := bstep (se 1 (by rfl) ⟨1423565, by rfl⟩ : syracuseStep 1898087 = 2847131) B2847131
theorem B2135353 : Blo 1897435 2135353 := bbase (se 2 (by rfl) ⟨800757, by rfl⟩ : syracuseStep 2135353 = 1601515) (by norm_num)
theorem B2847137 : Blo 1897435 2847137 := bstep (se 2 (by rfl) ⟨1067676, by rfl⟩ : syracuseStep 2847137 = 2135353) B2135353
theorem B1898091 : Blo 1897435 1898091 := bstep (se 1 (by rfl) ⟨1423568, by rfl⟩ : syracuseStep 1898091 = 2847137) B2847137
theorem B5405125 : Blo 1897435 5405125 := bbase (se 4 (by rfl) ⟨506730, by rfl⟩ : syracuseStep 5405125 = 1013461) (by norm_num)
theorem B7206833 : Blo 1897435 7206833 := bstep (se 2 (by rfl) ⟨2702562, by rfl⟩ : syracuseStep 7206833 = 5405125) B5405125
theorem B4804555 : Blo 1897435 4804555 := bstep (se 1 (by rfl) ⟨3603416, by rfl⟩ : syracuseStep 4804555 = 7206833) B7206833
theorem B6406073 : Blo 1897435 6406073 := bstep (se 2 (by rfl) ⟨2402277, by rfl⟩ : syracuseStep 6406073 = 4804555) B4804555
theorem B4270715 : Blo 1897435 4270715 := bstep (se 1 (by rfl) ⟨3203036, by rfl⟩ : syracuseStep 4270715 = 6406073) B6406073
theorem B2847143 : Blo 1897435 2847143 := bstep (se 1 (by rfl) ⟨2135357, by rfl⟩ : syracuseStep 2847143 = 4270715) B4270715
theorem B1898095 : Blo 1897435 1898095 := bstep (se 1 (by rfl) ⟨1423571, by rfl⟩ : syracuseStep 1898095 = 2847143) B2847143
theorem B2847149 : Blo 1897435 2847149 := bbase (se 3 (by rfl) ⟨533840, by rfl⟩ : syracuseStep 2847149 = 1067681) (by norm_num)
theorem B1898099 : Blo 1897435 1898099 := bstep (se 1 (by rfl) ⟨1423574, by rfl⟩ : syracuseStep 1898099 = 2847149) B2847149
theorem B4270733 : Blo 1897435 4270733 := bbase (se 3 (by rfl) ⟨800762, by rfl⟩ : syracuseStep 4270733 = 1601525) (by norm_num)
theorem B2847155 : Blo 1897435 2847155 := bstep (se 1 (by rfl) ⟨2135366, by rfl⟩ : syracuseStep 2847155 = 4270733) B4270733
theorem B1898103 : Blo 1897435 1898103 := bstep (se 1 (by rfl) ⟨1423577, by rfl⟩ : syracuseStep 1898103 = 2847155) B2847155
theorem B2402293 : Blo 1897435 2402293 := bbase (se 5 (by rfl) ⟨112607, by rfl⟩ : syracuseStep 2402293 = 225215) (by norm_num)
theorem B3203057 : Blo 1897435 3203057 := bstep (se 2 (by rfl) ⟨1201146, by rfl⟩ : syracuseStep 3203057 = 2402293) B2402293
theorem B2135371 : Blo 1897435 2135371 := bstep (se 1 (by rfl) ⟨1601528, by rfl⟩ : syracuseStep 2135371 = 3203057) B3203057
theorem B2847161 : Blo 1897435 2847161 := bstep (se 2 (by rfl) ⟨1067685, by rfl⟩ : syracuseStep 2847161 = 2135371) B2135371
theorem B1898107 : Blo 1897435 1898107 := bstep (se 1 (by rfl) ⟨1423580, by rfl⟩ : syracuseStep 1898107 = 2847161) B2847161
theorem B2886013 : Blo 1897435 2886013 := bbase (se 3 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 2886013 = 1082255) (by norm_num)
theorem B15392069 : Blo 1897435 15392069 := bstep (se 4 (by rfl) ⟨1443006, by rfl⟩ : syracuseStep 15392069 = 2886013) B2886013
theorem B10261379 : Blo 1897435 10261379 := bstep (se 1 (by rfl) ⟨7696034, by rfl⟩ : syracuseStep 10261379 = 15392069) B15392069
theorem B6840919 : Blo 1897435 6840919 := bstep (se 1 (by rfl) ⟨5130689, by rfl⟩ : syracuseStep 6840919 = 10261379) B10261379
theorem B36484901 : Blo 1897435 36484901 := bstep (se 4 (by rfl) ⟨3420459, by rfl⟩ : syracuseStep 36484901 = 6840919) B6840919
theorem B24323267 : Blo 1897435 24323267 := bstep (se 1 (by rfl) ⟨18242450, by rfl⟩ : syracuseStep 24323267 = 36484901) B36484901
theorem B16215511 : Blo 1897435 16215511 := bstep (se 1 (by rfl) ⟨12161633, by rfl⟩ : syracuseStep 16215511 = 24323267) B24323267
theorem B21620681 : Blo 1897435 21620681 := bstep (se 2 (by rfl) ⟨8107755, by rfl⟩ : syracuseStep 21620681 = 16215511) B16215511
theorem B14413787 : Blo 1897435 14413787 := bstep (se 1 (by rfl) ⟨10810340, by rfl⟩ : syracuseStep 14413787 = 21620681) B21620681
theorem B9609191 : Blo 1897435 9609191 := bstep (se 1 (by rfl) ⟨7206893, by rfl⟩ : syracuseStep 9609191 = 14413787) B14413787
theorem B6406127 : Blo 1897435 6406127 := bstep (se 1 (by rfl) ⟨4804595, by rfl⟩ : syracuseStep 6406127 = 9609191) B9609191
theorem B4270751 : Blo 1897435 4270751 := bstep (se 1 (by rfl) ⟨3203063, by rfl⟩ : syracuseStep 4270751 = 6406127) B6406127
theorem B2847167 : Blo 1897435 2847167 := bstep (se 1 (by rfl) ⟨2135375, by rfl⟩ : syracuseStep 2847167 = 4270751) B4270751
theorem B1898111 : Blo 1897435 1898111 := bstep (se 1 (by rfl) ⟨1423583, by rfl⟩ : syracuseStep 1898111 = 2847167) B2847167
theorem B2847173 : Blo 1897435 2847173 := bbase (se 4 (by rfl) ⟨266922, by rfl⟩ : syracuseStep 2847173 = 533845) (by norm_num)
theorem B1898115 : Blo 1897435 1898115 := bstep (se 1 (by rfl) ⟨1423586, by rfl⟩ : syracuseStep 1898115 = 2847173) B2847173
theorem B3203077 : Blo 1897435 3203077 := bbase (se 4 (by rfl) ⟨300288, by rfl⟩ : syracuseStep 3203077 = 600577) (by norm_num)
theorem B4270769 : Blo 1897435 4270769 := bstep (se 2 (by rfl) ⟨1601538, by rfl⟩ : syracuseStep 4270769 = 3203077) B3203077
theorem B2847179 : Blo 1897435 2847179 := bstep (se 1 (by rfl) ⟨2135384, by rfl⟩ : syracuseStep 2847179 = 4270769) B4270769
theorem B1898119 : Blo 1897435 1898119 := bstep (se 1 (by rfl) ⟨1423589, by rfl⟩ : syracuseStep 1898119 = 2847179) B2847179
theorem B2135389 : Blo 1897435 2135389 := bbase (se 3 (by rfl) ⟨400385, by rfl⟩ : syracuseStep 2135389 = 800771) (by norm_num)
theorem B2847185 : Blo 1897435 2847185 := bstep (se 2 (by rfl) ⟨1067694, by rfl⟩ : syracuseStep 2847185 = 2135389) B2135389
theorem B1898123 : Blo 1897435 1898123 := bstep (se 1 (by rfl) ⟨1423592, by rfl⟩ : syracuseStep 1898123 = 2847185) B2847185
theorem B6406181 : Blo 1897435 6406181 := bbase (se 4 (by rfl) ⟨600579, by rfl⟩ : syracuseStep 6406181 = 1201159) (by norm_num)
theorem B4270787 : Blo 1897435 4270787 := bstep (se 1 (by rfl) ⟨3203090, by rfl⟩ : syracuseStep 4270787 = 6406181) B6406181
theorem B2847191 : Blo 1897435 2847191 := bstep (se 1 (by rfl) ⟨2135393, by rfl⟩ : syracuseStep 2847191 = 4270787) B4270787
theorem B1898127 : Blo 1897435 1898127 := bstep (se 1 (by rfl) ⟨1423595, by rfl⟩ : syracuseStep 1898127 = 2847191) B2847191
theorem B2847197 : Blo 1897435 2847197 := bbase (se 3 (by rfl) ⟨533849, by rfl⟩ : syracuseStep 2847197 = 1067699) (by norm_num)
theorem B1898131 : Blo 1897435 1898131 := bstep (se 1 (by rfl) ⟨1423598, by rfl⟩ : syracuseStep 1898131 = 2847197) B2847197
theorem B4270805 : Blo 1897435 4270805 := bbase (se 7 (by rfl) ⟨50048, by rfl⟩ : syracuseStep 4270805 = 100097) (by norm_num)
theorem B2847203 : Blo 1897435 2847203 := bstep (se 1 (by rfl) ⟨2135402, by rfl⟩ : syracuseStep 2847203 = 4270805) B4270805
theorem B1898135 : Blo 1897435 1898135 := bstep (se 1 (by rfl) ⟨1423601, by rfl⟩ : syracuseStep 1898135 = 2847203) B2847203
theorem B8107877 : Blo 1897435 8107877 := bbase (se 4 (by rfl) ⟨760113, by rfl⟩ : syracuseStep 8107877 = 1520227) (by norm_num)
theorem B5405251 : Blo 1897435 5405251 := bstep (se 1 (by rfl) ⟨4053938, by rfl⟩ : syracuseStep 5405251 = 8107877) B8107877
theorem B7207001 : Blo 1897435 7207001 := bstep (se 2 (by rfl) ⟨2702625, by rfl⟩ : syracuseStep 7207001 = 5405251) B5405251
theorem B4804667 : Blo 1897435 4804667 := bstep (se 1 (by rfl) ⟨3603500, by rfl⟩ : syracuseStep 4804667 = 7207001) B7207001
theorem B3203111 : Blo 1897435 3203111 := bstep (se 1 (by rfl) ⟨2402333, by rfl⟩ : syracuseStep 3203111 = 4804667) B4804667
theorem B2135407 : Blo 1897435 2135407 := bstep (se 1 (by rfl) ⟨1601555, by rfl⟩ : syracuseStep 2135407 = 3203111) B3203111
theorem B2847209 : Blo 1897435 2847209 := bstep (se 2 (by rfl) ⟨1067703, by rfl⟩ : syracuseStep 2847209 = 2135407) B2135407
theorem B1898139 : Blo 1897435 1898139 := bstep (se 1 (by rfl) ⟨1423604, by rfl⟩ : syracuseStep 1898139 = 2847209) B2847209
theorem B2311457 : Blo 1897435 2311457 := bbase (se 2 (by rfl) ⟨866796, by rfl⟩ : syracuseStep 2311457 = 1733593) (by norm_num)
theorem B6163885 : Blo 1897435 6163885 := bstep (se 3 (by rfl) ⟨1155728, by rfl⟩ : syracuseStep 6163885 = 2311457) B2311457
theorem B8218513 : Blo 1897435 8218513 := bstep (se 2 (by rfl) ⟨3081942, by rfl⟩ : syracuseStep 8218513 = 6163885) B6163885
theorem B10958017 : Blo 1897435 10958017 := bstep (se 2 (by rfl) ⟨4109256, by rfl⟩ : syracuseStep 10958017 = 8218513) B8218513
theorem B14610689 : Blo 1897435 14610689 := bstep (se 2 (by rfl) ⟨5479008, by rfl⟩ : syracuseStep 14610689 = 10958017) B10958017
theorem B9740459 : Blo 1897435 9740459 := bstep (se 1 (by rfl) ⟨7305344, by rfl⟩ : syracuseStep 9740459 = 14610689) B14610689
theorem B6493639 : Blo 1897435 6493639 := bstep (se 1 (by rfl) ⟨4870229, by rfl⟩ : syracuseStep 6493639 = 9740459) B9740459
theorem B8658185 : Blo 1897435 8658185 := bstep (se 2 (by rfl) ⟨3246819, by rfl⟩ : syracuseStep 8658185 = 6493639) B6493639
theorem B23088493 : Blo 1897435 23088493 := bstep (se 3 (by rfl) ⟨4329092, by rfl⟩ : syracuseStep 23088493 = 8658185) B8658185
theorem B30784657 : Blo 1897435 30784657 := bstep (se 2 (by rfl) ⟨11544246, by rfl⟩ : syracuseStep 30784657 = 23088493) B23088493
theorem B41046209 : Blo 1897435 41046209 := bstep (se 2 (by rfl) ⟨15392328, by rfl⟩ : syracuseStep 41046209 = 30784657) B30784657
theorem B27364139 : Blo 1897435 27364139 := bstep (se 1 (by rfl) ⟨20523104, by rfl⟩ : syracuseStep 27364139 = 41046209) B41046209
theorem B18242759 : Blo 1897435 18242759 := bstep (se 1 (by rfl) ⟨13682069, by rfl⟩ : syracuseStep 18242759 = 27364139) B27364139
theorem B12161839 : Blo 1897435 12161839 := bstep (se 1 (by rfl) ⟨9121379, by rfl⟩ : syracuseStep 12161839 = 18242759) B18242759
theorem B16215785 : Blo 1897435 16215785 := bstep (se 2 (by rfl) ⟨6080919, by rfl⟩ : syracuseStep 16215785 = 12161839) B12161839
theorem B10810523 : Blo 1897435 10810523 := bstep (se 1 (by rfl) ⟨8107892, by rfl⟩ : syracuseStep 10810523 = 16215785) B16215785
theorem B7207015 : Blo 1897435 7207015 := bstep (se 1 (by rfl) ⟨5405261, by rfl⟩ : syracuseStep 7207015 = 10810523) B10810523
theorem B9609353 : Blo 1897435 9609353 := bstep (se 2 (by rfl) ⟨3603507, by rfl⟩ : syracuseStep 9609353 = 7207015) B7207015
theorem B6406235 : Blo 1897435 6406235 := bstep (se 1 (by rfl) ⟨4804676, by rfl⟩ : syracuseStep 6406235 = 9609353) B9609353
theorem B4270823 : Blo 1897435 4270823 := bstep (se 1 (by rfl) ⟨3203117, by rfl⟩ : syracuseStep 4270823 = 6406235) B6406235
theorem B2847215 : Blo 1897435 2847215 := bstep (se 1 (by rfl) ⟨2135411, by rfl⟩ : syracuseStep 2847215 = 4270823) B4270823
theorem B1898143 : Blo 1897435 1898143 := bstep (se 1 (by rfl) ⟨1423607, by rfl⟩ : syracuseStep 1898143 = 2847215) B2847215
theorem B2847221 : Blo 1897435 2847221 := bbase (se 5 (by rfl) ⟨133463, by rfl⟩ : syracuseStep 2847221 = 266927) (by norm_num)
theorem B1898147 : Blo 1897435 1898147 := bstep (se 1 (by rfl) ⟨1423610, by rfl⟩ : syracuseStep 1898147 = 2847221) B2847221
theorem B5405285 : Blo 1897435 5405285 := bbase (se 4 (by rfl) ⟨506745, by rfl⟩ : syracuseStep 5405285 = 1013491) (by norm_num)
theorem B3603523 : Blo 1897435 3603523 := bstep (se 1 (by rfl) ⟨2702642, by rfl⟩ : syracuseStep 3603523 = 5405285) B5405285
theorem B4804697 : Blo 1897435 4804697 := bstep (se 2 (by rfl) ⟨1801761, by rfl⟩ : syracuseStep 4804697 = 3603523) B3603523
theorem B3203131 : Blo 1897435 3203131 := bstep (se 1 (by rfl) ⟨2402348, by rfl⟩ : syracuseStep 3203131 = 4804697) B4804697
theorem B4270841 : Blo 1897435 4270841 := bstep (se 2 (by rfl) ⟨1601565, by rfl⟩ : syracuseStep 4270841 = 3203131) B3203131
theorem B2847227 : Blo 1897435 2847227 := bstep (se 1 (by rfl) ⟨2135420, by rfl⟩ : syracuseStep 2847227 = 4270841) B4270841
theorem B1898151 : Blo 1897435 1898151 := bstep (se 1 (by rfl) ⟨1423613, by rfl⟩ : syracuseStep 1898151 = 2847227) B2847227
theorem B2135425 : Blo 1897435 2135425 := bbase (se 2 (by rfl) ⟨800784, by rfl⟩ : syracuseStep 2135425 = 1601569) (by norm_num)
theorem B2847233 : Blo 1897435 2847233 := bstep (se 2 (by rfl) ⟨1067712, by rfl⟩ : syracuseStep 2847233 = 2135425) B2135425
theorem B1898155 : Blo 1897435 1898155 := bstep (se 1 (by rfl) ⟨1423616, by rfl⟩ : syracuseStep 1898155 = 2847233) B2847233
theorem B4804717 : Blo 1897435 4804717 := bbase (se 3 (by rfl) ⟨900884, by rfl⟩ : syracuseStep 4804717 = 1801769) (by norm_num)
theorem B6406289 : Blo 1897435 6406289 := bstep (se 2 (by rfl) ⟨2402358, by rfl⟩ : syracuseStep 6406289 = 4804717) B4804717
theorem B4270859 : Blo 1897435 4270859 := bstep (se 1 (by rfl) ⟨3203144, by rfl⟩ : syracuseStep 4270859 = 6406289) B6406289
theorem B2847239 : Blo 1897435 2847239 := bstep (se 1 (by rfl) ⟨2135429, by rfl⟩ : syracuseStep 2847239 = 4270859) B4270859
theorem B1898159 : Blo 1897435 1898159 := bstep (se 1 (by rfl) ⟨1423619, by rfl⟩ : syracuseStep 1898159 = 2847239) B2847239
theorem B2847245 : Blo 1897435 2847245 := bbase (se 3 (by rfl) ⟨533858, by rfl⟩ : syracuseStep 2847245 = 1067717) (by norm_num)
theorem B1898163 : Blo 1897435 1898163 := bstep (se 1 (by rfl) ⟨1423622, by rfl⟩ : syracuseStep 1898163 = 2847245) B2847245
theorem B4270877 : Blo 1897435 4270877 := bbase (se 3 (by rfl) ⟨800789, by rfl⟩ : syracuseStep 4270877 = 1601579) (by norm_num)
theorem B2847251 : Blo 1897435 2847251 := bstep (se 1 (by rfl) ⟨2135438, by rfl⟩ : syracuseStep 2847251 = 4270877) B4270877
theorem B1898167 : Blo 1897435 1898167 := bstep (se 1 (by rfl) ⟨1423625, by rfl⟩ : syracuseStep 1898167 = 2847251) B2847251
theorem B3203165 : Blo 1897435 3203165 := bbase (se 3 (by rfl) ⟨600593, by rfl⟩ : syracuseStep 3203165 = 1201187) (by norm_num)
theorem B2135443 : Blo 1897435 2135443 := bstep (se 1 (by rfl) ⟨1601582, by rfl⟩ : syracuseStep 2135443 = 3203165) B3203165
theorem B2847257 : Blo 1897435 2847257 := bstep (se 2 (by rfl) ⟨1067721, by rfl⟩ : syracuseStep 2847257 = 2135443) B2135443
theorem B1898171 : Blo 1897435 1898171 := bstep (se 1 (by rfl) ⟨1423628, by rfl⟩ : syracuseStep 1898171 = 2847257) B2847257
theorem B1950325 : Blo 1897435 1950325 := bbase (se 5 (by rfl) ⟨91421, by rfl⟩ : syracuseStep 1950325 = 182843) (by norm_num)
theorem B10401733 : Blo 1897435 10401733 := bstep (se 4 (by rfl) ⟨975162, by rfl⟩ : syracuseStep 10401733 = 1950325) B1950325
theorem B13868977 : Blo 1897435 13868977 := bstep (se 2 (by rfl) ⟨5200866, by rfl⟩ : syracuseStep 13868977 = 10401733) B10401733
theorem B18491969 : Blo 1897435 18491969 := bstep (se 2 (by rfl) ⟨6934488, by rfl⟩ : syracuseStep 18491969 = 13868977) B13868977
theorem B12327979 : Blo 1897435 12327979 := bstep (se 1 (by rfl) ⟨9245984, by rfl⟩ : syracuseStep 12327979 = 18491969) B18491969
theorem B16437305 : Blo 1897435 16437305 := bstep (se 2 (by rfl) ⟨6163989, by rfl⟩ : syracuseStep 16437305 = 12327979) B12327979
theorem B10958203 : Blo 1897435 10958203 := bstep (se 1 (by rfl) ⟨8218652, by rfl⟩ : syracuseStep 10958203 = 16437305) B16437305
theorem B14610937 : Blo 1897435 14610937 := bstep (se 2 (by rfl) ⟨5479101, by rfl⟩ : syracuseStep 14610937 = 10958203) B10958203
theorem B19481249 : Blo 1897435 19481249 := bstep (se 2 (by rfl) ⟨7305468, by rfl⟩ : syracuseStep 19481249 = 14610937) B14610937
theorem B51949997 : Blo 1897435 51949997 := bstep (se 3 (by rfl) ⟨9740624, by rfl⟩ : syracuseStep 51949997 = 19481249) B19481249
theorem B34633331 : Blo 1897435 34633331 := bstep (se 1 (by rfl) ⟨25974998, by rfl⟩ : syracuseStep 34633331 = 51949997) B51949997
theorem B23088887 : Blo 1897435 23088887 := bstep (se 1 (by rfl) ⟨17316665, by rfl⟩ : syracuseStep 23088887 = 34633331) B34633331
theorem B15392591 : Blo 1897435 15392591 := bstep (se 1 (by rfl) ⟨11544443, by rfl⟩ : syracuseStep 15392591 = 23088887) B23088887
theorem B10261727 : Blo 1897435 10261727 := bstep (se 1 (by rfl) ⟨7696295, by rfl⟩ : syracuseStep 10261727 = 15392591) B15392591
theorem B6841151 : Blo 1897435 6841151 := bstep (se 1 (by rfl) ⟨5130863, by rfl⟩ : syracuseStep 6841151 = 10261727) B10261727
theorem B4560767 : Blo 1897435 4560767 := bstep (se 1 (by rfl) ⟨3420575, by rfl⟩ : syracuseStep 4560767 = 6841151) B6841151
theorem B3040511 : Blo 1897435 3040511 := bstep (se 1 (by rfl) ⟨2280383, by rfl⟩ : syracuseStep 3040511 = 4560767) B4560767
theorem B8108029 : Blo 1897435 8108029 := bstep (se 3 (by rfl) ⟨1520255, by rfl⟩ : syracuseStep 8108029 = 3040511) B3040511
theorem B10810705 : Blo 1897435 10810705 := bstep (se 2 (by rfl) ⟨4054014, by rfl⟩ : syracuseStep 10810705 = 8108029) B8108029
theorem B14414273 : Blo 1897435 14414273 := bstep (se 2 (by rfl) ⟨5405352, by rfl⟩ : syracuseStep 14414273 = 10810705) B10810705
theorem B9609515 : Blo 1897435 9609515 := bstep (se 1 (by rfl) ⟨7207136, by rfl⟩ : syracuseStep 9609515 = 14414273) B14414273
theorem B6406343 : Blo 1897435 6406343 := bstep (se 1 (by rfl) ⟨4804757, by rfl⟩ : syracuseStep 6406343 = 9609515) B9609515
theorem B4270895 : Blo 1897435 4270895 := bstep (se 1 (by rfl) ⟨3203171, by rfl⟩ : syracuseStep 4270895 = 6406343) B6406343
theorem B2847263 : Blo 1897435 2847263 := bstep (se 1 (by rfl) ⟨2135447, by rfl⟩ : syracuseStep 2847263 = 4270895) B4270895
theorem B1898175 : Blo 1897435 1898175 := bstep (se 1 (by rfl) ⟨1423631, by rfl⟩ : syracuseStep 1898175 = 2847263) B2847263
theorem B2847269 : Blo 1897435 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B1898179 : Blo 1897435 1898179 := bstep (se 1 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 1898179 = 2847269) B2847269
theorem B2402389 : Blo 1897435 2402389 := bbase (se 8 (by rfl) ⟨14076, by rfl⟩ : syracuseStep 2402389 = 28153) (by norm_num)
theorem B3203185 : Blo 1897435 3203185 := bstep (se 2 (by rfl) ⟨1201194, by rfl⟩ : syracuseStep 3203185 = 2402389) B2402389
theorem B4270913 : Blo 1897435 4270913 := bstep (se 2 (by rfl) ⟨1601592, by rfl⟩ : syracuseStep 4270913 = 3203185) B3203185
theorem B2847275 : Blo 1897435 2847275 := bstep (se 1 (by rfl) ⟨2135456, by rfl⟩ : syracuseStep 2847275 = 4270913) B4270913
theorem B1898183 : Blo 1897435 1898183 := bstep (se 1 (by rfl) ⟨1423637, by rfl⟩ : syracuseStep 1898183 = 2847275) B2847275
theorem B2135461 : Blo 1897435 2135461 := bbase (se 4 (by rfl) ⟨200199, by rfl⟩ : syracuseStep 2135461 = 400399) (by norm_num)
theorem B2847281 : Blo 1897435 2847281 := bstep (se 2 (by rfl) ⟨1067730, by rfl⟩ : syracuseStep 2847281 = 2135461) B2135461
theorem B1898187 : Blo 1897435 1898187 := bstep (se 1 (by rfl) ⟨1423640, by rfl⟩ : syracuseStep 1898187 = 2847281) B2847281
theorem B3420605 : Blo 1897435 3420605 := bbase (se 3 (by rfl) ⟨641363, by rfl⟩ : syracuseStep 3420605 = 1282727) (by norm_num)
theorem B2280403 : Blo 1897435 2280403 := bstep (se 1 (by rfl) ⟨1710302, by rfl⟩ : syracuseStep 2280403 = 3420605) B3420605
theorem B12162149 : Blo 1897435 12162149 := bstep (se 4 (by rfl) ⟨1140201, by rfl⟩ : syracuseStep 12162149 = 2280403) B2280403
theorem B8108099 : Blo 1897435 8108099 := bstep (se 1 (by rfl) ⟨6081074, by rfl⟩ : syracuseStep 8108099 = 12162149) B12162149
theorem B5405399 : Blo 1897435 5405399 := bstep (se 1 (by rfl) ⟨4054049, by rfl⟩ : syracuseStep 5405399 = 8108099) B8108099
theorem B3603599 : Blo 1897435 3603599 := bstep (se 1 (by rfl) ⟨2702699, by rfl⟩ : syracuseStep 3603599 = 5405399) B5405399
theorem B2402399 : Blo 1897435 2402399 := bstep (se 1 (by rfl) ⟨1801799, by rfl⟩ : syracuseStep 2402399 = 3603599) B3603599
theorem B6406397 : Blo 1897435 6406397 := bstep (se 3 (by rfl) ⟨1201199, by rfl⟩ : syracuseStep 6406397 = 2402399) B2402399
theorem B4270931 : Blo 1897435 4270931 := bstep (se 1 (by rfl) ⟨3203198, by rfl⟩ : syracuseStep 4270931 = 6406397) B6406397
theorem B2847287 : Blo 1897435 2847287 := bstep (se 1 (by rfl) ⟨2135465, by rfl⟩ : syracuseStep 2847287 = 4270931) B4270931
theorem B1898191 : Blo 1897435 1898191 := bstep (se 1 (by rfl) ⟨1423643, by rfl⟩ : syracuseStep 1898191 = 2847287) B2847287
theorem B2847293 : Blo 1897435 2847293 := bbase (se 3 (by rfl) ⟨533867, by rfl⟩ : syracuseStep 2847293 = 1067735) (by norm_num)
theorem B1898195 : Blo 1897435 1898195 := bstep (se 1 (by rfl) ⟨1423646, by rfl⟩ : syracuseStep 1898195 = 2847293) B2847293
theorem B4270949 : Blo 1897435 4270949 := bbase (se 4 (by rfl) ⟨400401, by rfl⟩ : syracuseStep 4270949 = 800803) (by norm_num)
theorem B2847299 : Blo 1897435 2847299 := bstep (se 1 (by rfl) ⟨2135474, by rfl⟩ : syracuseStep 2847299 = 4270949) B4270949
theorem B1898199 : Blo 1897435 1898199 := bstep (se 1 (by rfl) ⟨1423649, by rfl⟩ : syracuseStep 1898199 = 2847299) B2847299
theorem B4804829 : Blo 1897435 4804829 := bbase (se 3 (by rfl) ⟨900905, by rfl⟩ : syracuseStep 4804829 = 1801811) (by norm_num)
theorem B3203219 : Blo 1897435 3203219 := bstep (se 1 (by rfl) ⟨2402414, by rfl⟩ : syracuseStep 3203219 = 4804829) B4804829
theorem B2135479 : Blo 1897435 2135479 := bstep (se 1 (by rfl) ⟨1601609, by rfl⟩ : syracuseStep 2135479 = 3203219) B3203219
theorem B2847305 : Blo 1897435 2847305 := bstep (se 2 (by rfl) ⟨1067739, by rfl⟩ : syracuseStep 2847305 = 2135479) B2135479
theorem B1898203 : Blo 1897435 1898203 := bstep (se 1 (by rfl) ⟨1423652, by rfl⟩ : syracuseStep 1898203 = 2847305) B2847305
theorem B3603629 : Blo 1897435 3603629 := bbase (se 3 (by rfl) ⟨675680, by rfl⟩ : syracuseStep 3603629 = 1351361) (by norm_num)
theorem B9609677 : Blo 1897435 9609677 := bstep (se 3 (by rfl) ⟨1801814, by rfl⟩ : syracuseStep 9609677 = 3603629) B3603629
theorem B6406451 : Blo 1897435 6406451 := bstep (se 1 (by rfl) ⟨4804838, by rfl⟩ : syracuseStep 6406451 = 9609677) B9609677
theorem B4270967 : Blo 1897435 4270967 := bstep (se 1 (by rfl) ⟨3203225, by rfl⟩ : syracuseStep 4270967 = 6406451) B6406451
theorem B2847311 : Blo 1897435 2847311 := bstep (se 1 (by rfl) ⟨2135483, by rfl⟩ : syracuseStep 2847311 = 4270967) B4270967
theorem B1898207 : Blo 1897435 1898207 := bstep (se 1 (by rfl) ⟨1423655, by rfl⟩ : syracuseStep 1898207 = 2847311) B2847311
theorem B2847317 : Blo 1897435 2847317 := bbase (se 8 (by rfl) ⟨16683, by rfl⟩ : syracuseStep 2847317 = 33367) (by norm_num)
theorem B1898211 : Blo 1897435 1898211 := bstep (se 1 (by rfl) ⟨1423658, by rfl⟩ : syracuseStep 1898211 = 2847317) B2847317
theorem B13869269 : Blo 1897435 13869269 := bbase (se 7 (by rfl) ⟨162530, by rfl⟩ : syracuseStep 13869269 = 325061) (by norm_num)
theorem B9246179 : Blo 1897435 9246179 := bstep (se 1 (by rfl) ⟨6934634, by rfl⟩ : syracuseStep 9246179 = 13869269) B13869269
theorem B6164119 : Blo 1897435 6164119 := bstep (se 1 (by rfl) ⟨4623089, by rfl⟩ : syracuseStep 6164119 = 9246179) B9246179
theorem B32875301 : Blo 1897435 32875301 := bstep (se 4 (by rfl) ⟨3082059, by rfl⟩ : syracuseStep 32875301 = 6164119) B6164119
theorem B21916867 : Blo 1897435 21916867 := bstep (se 1 (by rfl) ⟨16437650, by rfl⟩ : syracuseStep 21916867 = 32875301) B32875301
theorem B29222489 : Blo 1897435 29222489 := bstep (se 2 (by rfl) ⟨10958433, by rfl⟩ : syracuseStep 29222489 = 21916867) B21916867
theorem B77926637 : Blo 1897435 77926637 := bstep (se 3 (by rfl) ⟨14611244, by rfl⟩ : syracuseStep 77926637 = 29222489) B29222489
theorem B51951091 : Blo 1897435 51951091 := bstep (se 1 (by rfl) ⟨38963318, by rfl⟩ : syracuseStep 51951091 = 77926637) B77926637
theorem B69268121 : Blo 1897435 69268121 := bstep (se 2 (by rfl) ⟨25975545, by rfl⟩ : syracuseStep 69268121 = 51951091) B51951091
theorem B46178747 : Blo 1897435 46178747 := bstep (se 1 (by rfl) ⟨34634060, by rfl⟩ : syracuseStep 46178747 = 69268121) B69268121
theorem B30785831 : Blo 1897435 30785831 := bstep (se 1 (by rfl) ⟨23089373, by rfl⟩ : syracuseStep 30785831 = 46178747) B46178747
theorem B20523887 : Blo 1897435 20523887 := bstep (se 1 (by rfl) ⟨15392915, by rfl⟩ : syracuseStep 20523887 = 30785831) B30785831
theorem B13682591 : Blo 1897435 13682591 := bstep (se 1 (by rfl) ⟨10261943, by rfl⟩ : syracuseStep 13682591 = 20523887) B20523887
theorem B9121727 : Blo 1897435 9121727 := bstep (se 1 (by rfl) ⟨6841295, by rfl⟩ : syracuseStep 9121727 = 13682591) B13682591
theorem B6081151 : Blo 1897435 6081151 := bstep (se 1 (by rfl) ⟨4560863, by rfl⟩ : syracuseStep 6081151 = 9121727) B9121727
theorem B8108201 : Blo 1897435 8108201 := bstep (se 2 (by rfl) ⟨3040575, by rfl⟩ : syracuseStep 8108201 = 6081151) B6081151
theorem B5405467 : Blo 1897435 5405467 := bstep (se 1 (by rfl) ⟨4054100, by rfl⟩ : syracuseStep 5405467 = 8108201) B8108201
theorem B7207289 : Blo 1897435 7207289 := bstep (se 2 (by rfl) ⟨2702733, by rfl⟩ : syracuseStep 7207289 = 5405467) B5405467
theorem B4804859 : Blo 1897435 4804859 := bstep (se 1 (by rfl) ⟨3603644, by rfl⟩ : syracuseStep 4804859 = 7207289) B7207289
theorem B3203239 : Blo 1897435 3203239 := bstep (se 1 (by rfl) ⟨2402429, by rfl⟩ : syracuseStep 3203239 = 4804859) B4804859
theorem B4270985 : Blo 1897435 4270985 := bstep (se 2 (by rfl) ⟨1601619, by rfl⟩ : syracuseStep 4270985 = 3203239) B3203239
theorem B2847323 : Blo 1897435 2847323 := bstep (se 1 (by rfl) ⟨2135492, by rfl⟩ : syracuseStep 2847323 = 4270985) B4270985
theorem B1898215 : Blo 1897435 1898215 := bstep (se 1 (by rfl) ⟨1423661, by rfl⟩ : syracuseStep 1898215 = 2847323) B2847323
theorem B2135497 : Blo 1897435 2135497 := bbase (se 2 (by rfl) ⟨800811, by rfl⟩ : syracuseStep 2135497 = 1601623) (by norm_num)
theorem B2847329 : Blo 1897435 2847329 := bstep (se 2 (by rfl) ⟨1067748, by rfl⟩ : syracuseStep 2847329 = 2135497) B2135497
theorem B1898219 : Blo 1897435 1898219 := bstep (se 1 (by rfl) ⟨1423664, by rfl⟩ : syracuseStep 1898219 = 2847329) B2847329
theorem B16216469 : Blo 1897435 16216469 := bbase (se 6 (by rfl) ⟨380073, by rfl⟩ : syracuseStep 16216469 = 760147) (by norm_num)
theorem B10810979 : Blo 1897435 10810979 := bstep (se 1 (by rfl) ⟨8108234, by rfl⟩ : syracuseStep 10810979 = 16216469) B16216469
theorem B7207319 : Blo 1897435 7207319 := bstep (se 1 (by rfl) ⟨5405489, by rfl⟩ : syracuseStep 7207319 = 10810979) B10810979
theorem B4804879 : Blo 1897435 4804879 := bstep (se 1 (by rfl) ⟨3603659, by rfl⟩ : syracuseStep 4804879 = 7207319) B7207319
theorem B6406505 : Blo 1897435 6406505 := bstep (se 2 (by rfl) ⟨2402439, by rfl⟩ : syracuseStep 6406505 = 4804879) B4804879
theorem B4271003 : Blo 1897435 4271003 := bstep (se 1 (by rfl) ⟨3203252, by rfl⟩ : syracuseStep 4271003 = 6406505) B6406505
theorem B2847335 : Blo 1897435 2847335 := bstep (se 1 (by rfl) ⟨2135501, by rfl⟩ : syracuseStep 2847335 = 4271003) B4271003
theorem B1898223 : Blo 1897435 1898223 := bstep (se 1 (by rfl) ⟨1423667, by rfl⟩ : syracuseStep 1898223 = 2847335) B2847335
theorem B2847341 : Blo 1897435 2847341 := bbase (se 3 (by rfl) ⟨533876, by rfl⟩ : syracuseStep 2847341 = 1067753) (by norm_num)
theorem B1898227 : Blo 1897435 1898227 := bstep (se 1 (by rfl) ⟨1423670, by rfl⟩ : syracuseStep 1898227 = 2847341) B2847341
theorem B4271021 : Blo 1897435 4271021 := bbase (se 3 (by rfl) ⟨800816, by rfl⟩ : syracuseStep 4271021 = 1601633) (by norm_num)
theorem B2847347 : Blo 1897435 2847347 := bstep (se 1 (by rfl) ⟨2135510, by rfl⟩ : syracuseStep 2847347 = 4271021) B4271021
theorem B1898231 : Blo 1897435 1898231 := bstep (se 1 (by rfl) ⟨1423673, by rfl⟩ : syracuseStep 1898231 = 2847347) B2847347
theorem B5405525 : Blo 1897435 5405525 := bbase (se 9 (by rfl) ⟨15836, by rfl⟩ : syracuseStep 5405525 = 31673) (by norm_num)
theorem B3603683 : Blo 1897435 3603683 := bstep (se 1 (by rfl) ⟨2702762, by rfl⟩ : syracuseStep 3603683 = 5405525) B5405525
theorem B2402455 : Blo 1897435 2402455 := bstep (se 1 (by rfl) ⟨1801841, by rfl⟩ : syracuseStep 2402455 = 3603683) B3603683
theorem B3203273 : Blo 1897435 3203273 := bstep (se 2 (by rfl) ⟨1201227, by rfl⟩ : syracuseStep 3203273 = 2402455) B2402455
theorem B2135515 : Blo 1897435 2135515 := bstep (se 1 (by rfl) ⟨1601636, by rfl⟩ : syracuseStep 2135515 = 3203273) B3203273
theorem B2847353 : Blo 1897435 2847353 := bstep (se 2 (by rfl) ⟨1067757, by rfl⟩ : syracuseStep 2847353 = 2135515) B2135515
theorem B1898235 : Blo 1897435 1898235 := bstep (se 1 (by rfl) ⟨1423676, by rfl⟩ : syracuseStep 1898235 = 2847353) B2847353
theorem B8776757 : Blo 1897435 8776757 := bbase (se 5 (by rfl) ⟨411410, by rfl⟩ : syracuseStep 8776757 = 822821) (by norm_num)
theorem B5851171 : Blo 1897435 5851171 := bstep (se 1 (by rfl) ⟨4388378, by rfl⟩ : syracuseStep 5851171 = 8776757) B8776757
theorem B7801561 : Blo 1897435 7801561 := bstep (se 2 (by rfl) ⟨2925585, by rfl⟩ : syracuseStep 7801561 = 5851171) B5851171
theorem B41608325 : Blo 1897435 41608325 := bstep (se 4 (by rfl) ⟨3900780, by rfl⟩ : syracuseStep 41608325 = 7801561) B7801561
theorem B27738883 : Blo 1897435 27738883 := bstep (se 1 (by rfl) ⟨20804162, by rfl⟩ : syracuseStep 27738883 = 41608325) B41608325
theorem B36985177 : Blo 1897435 36985177 := bstep (se 2 (by rfl) ⟨13869441, by rfl⟩ : syracuseStep 36985177 = 27738883) B27738883
theorem B49313569 : Blo 1897435 49313569 := bstep (se 2 (by rfl) ⟨18492588, by rfl⟩ : syracuseStep 49313569 = 36985177) B36985177
theorem B65751425 : Blo 1897435 65751425 := bstep (se 2 (by rfl) ⟨24656784, by rfl⟩ : syracuseStep 65751425 = 49313569) B49313569
theorem B43834283 : Blo 1897435 43834283 := bstep (se 1 (by rfl) ⟨32875712, by rfl⟩ : syracuseStep 43834283 = 65751425) B65751425
theorem B29222855 : Blo 1897435 29222855 := bstep (se 1 (by rfl) ⟨21917141, by rfl⟩ : syracuseStep 29222855 = 43834283) B43834283
theorem B19481903 : Blo 1897435 19481903 := bstep (se 1 (by rfl) ⟨14611427, by rfl⟩ : syracuseStep 19481903 = 29222855) B29222855
theorem B12987935 : Blo 1897435 12987935 := bstep (se 1 (by rfl) ⟨9740951, by rfl⟩ : syracuseStep 12987935 = 19481903) B19481903
theorem B8658623 : Blo 1897435 8658623 := bstep (se 1 (by rfl) ⟨6493967, by rfl⟩ : syracuseStep 8658623 = 12987935) B12987935
theorem B5772415 : Blo 1897435 5772415 := bstep (se 1 (by rfl) ⟨4329311, by rfl⟩ : syracuseStep 5772415 = 8658623) B8658623
theorem B7696553 : Blo 1897435 7696553 := bstep (se 2 (by rfl) ⟨2886207, by rfl⟩ : syracuseStep 7696553 = 5772415) B5772415
theorem B20524141 : Blo 1897435 20524141 := bstep (se 3 (by rfl) ⟨3848276, by rfl⟩ : syracuseStep 20524141 = 7696553) B7696553
theorem B27365521 : Blo 1897435 27365521 := bstep (se 2 (by rfl) ⟨10262070, by rfl⟩ : syracuseStep 27365521 = 20524141) B20524141
theorem B36487361 : Blo 1897435 36487361 := bstep (se 2 (by rfl) ⟨13682760, by rfl⟩ : syracuseStep 36487361 = 27365521) B27365521
theorem B24324907 : Blo 1897435 24324907 := bstep (se 1 (by rfl) ⟨18243680, by rfl⟩ : syracuseStep 24324907 = 36487361) B36487361
theorem B32433209 : Blo 1897435 32433209 := bstep (se 2 (by rfl) ⟨12162453, by rfl⟩ : syracuseStep 32433209 = 24324907) B24324907
theorem B21622139 : Blo 1897435 21622139 := bstep (se 1 (by rfl) ⟨16216604, by rfl⟩ : syracuseStep 21622139 = 32433209) B32433209
theorem B14414759 : Blo 1897435 14414759 := bstep (se 1 (by rfl) ⟨10811069, by rfl⟩ : syracuseStep 14414759 = 21622139) B21622139
theorem B9609839 : Blo 1897435 9609839 := bstep (se 1 (by rfl) ⟨7207379, by rfl⟩ : syracuseStep 9609839 = 14414759) B14414759
theorem B6406559 : Blo 1897435 6406559 := bstep (se 1 (by rfl) ⟨4804919, by rfl⟩ : syracuseStep 6406559 = 9609839) B9609839
theorem B4271039 : Blo 1897435 4271039 := bstep (se 1 (by rfl) ⟨3203279, by rfl⟩ : syracuseStep 4271039 = 6406559) B6406559
theorem B2847359 : Blo 1897435 2847359 := bstep (se 1 (by rfl) ⟨2135519, by rfl⟩ : syracuseStep 2847359 = 4271039) B4271039
theorem B1898239 : Blo 1897435 1898239 := bstep (se 1 (by rfl) ⟨1423679, by rfl⟩ : syracuseStep 1898239 = 2847359) B2847359
theorem B2847365 : Blo 1897435 2847365 := bbase (se 4 (by rfl) ⟨266940, by rfl⟩ : syracuseStep 2847365 = 533881) (by norm_num)
theorem B1898243 : Blo 1897435 1898243 := bstep (se 1 (by rfl) ⟨1423682, by rfl⟩ : syracuseStep 1898243 = 2847365) B2847365
theorem B3203293 : Blo 1897435 3203293 := bbase (se 3 (by rfl) ⟨600617, by rfl⟩ : syracuseStep 3203293 = 1201235) (by norm_num)
theorem B4271057 : Blo 1897435 4271057 := bstep (se 2 (by rfl) ⟨1601646, by rfl⟩ : syracuseStep 4271057 = 3203293) B3203293
theorem B2847371 : Blo 1897435 2847371 := bstep (se 1 (by rfl) ⟨2135528, by rfl⟩ : syracuseStep 2847371 = 4271057) B4271057
theorem B1898247 : Blo 1897435 1898247 := bstep (se 1 (by rfl) ⟨1423685, by rfl⟩ : syracuseStep 1898247 = 2847371) B2847371
theorem B2135533 : Blo 1897435 2135533 := bbase (se 3 (by rfl) ⟨400412, by rfl⟩ : syracuseStep 2135533 = 800825) (by norm_num)
theorem B2847377 : Blo 1897435 2847377 := bstep (se 2 (by rfl) ⟨1067766, by rfl⟩ : syracuseStep 2847377 = 2135533) B2135533
theorem B1898251 : Blo 1897435 1898251 := bstep (se 1 (by rfl) ⟨1423688, by rfl⟩ : syracuseStep 1898251 = 2847377) B2847377
theorem B6406613 : Blo 1897435 6406613 := bbase (se 7 (by rfl) ⟨75077, by rfl⟩ : syracuseStep 6406613 = 150155) (by norm_num)
theorem B4271075 : Blo 1897435 4271075 := bstep (se 1 (by rfl) ⟨3203306, by rfl⟩ : syracuseStep 4271075 = 6406613) B6406613
theorem B2847383 : Blo 1897435 2847383 := bstep (se 1 (by rfl) ⟨2135537, by rfl⟩ : syracuseStep 2847383 = 4271075) B4271075
theorem B1898255 : Blo 1897435 1898255 := bstep (se 1 (by rfl) ⟨1423691, by rfl⟩ : syracuseStep 1898255 = 2847383) B2847383
theorem B2847389 : Blo 1897435 2847389 := bbase (se 3 (by rfl) ⟨533885, by rfl⟩ : syracuseStep 2847389 = 1067771) (by norm_num)
theorem B1898259 : Blo 1897435 1898259 := bstep (se 1 (by rfl) ⟨1423694, by rfl⟩ : syracuseStep 1898259 = 2847389) B2847389
theorem B4271093 : Blo 1897435 4271093 := bbase (se 5 (by rfl) ⟨200207, by rfl⟩ : syracuseStep 4271093 = 400415) (by norm_num)
theorem B2847395 : Blo 1897435 2847395 := bstep (se 1 (by rfl) ⟨2135546, by rfl⟩ : syracuseStep 2847395 = 4271093) B4271093
theorem B1898263 : Blo 1897435 1898263 := bstep (se 1 (by rfl) ⟨1423697, by rfl⟩ : syracuseStep 1898263 = 2847395) B2847395
theorem B54731861 : Blo 1897435 54731861 := bbase (se 8 (by rfl) ⟨320694, by rfl⟩ : syracuseStep 54731861 = 641389) (by norm_num)
theorem B36487907 : Blo 1897435 36487907 := bstep (se 1 (by rfl) ⟨27365930, by rfl⟩ : syracuseStep 36487907 = 54731861) B54731861
theorem B24325271 : Blo 1897435 24325271 := bstep (se 1 (by rfl) ⟨18243953, by rfl⟩ : syracuseStep 24325271 = 36487907) B36487907
theorem B16216847 : Blo 1897435 16216847 := bstep (se 1 (by rfl) ⟨12162635, by rfl⟩ : syracuseStep 16216847 = 24325271) B24325271
theorem B10811231 : Blo 1897435 10811231 := bstep (se 1 (by rfl) ⟨8108423, by rfl⟩ : syracuseStep 10811231 = 16216847) B16216847
theorem B7207487 : Blo 1897435 7207487 := bstep (se 1 (by rfl) ⟨5405615, by rfl⟩ : syracuseStep 7207487 = 10811231) B10811231
theorem B4804991 : Blo 1897435 4804991 := bstep (se 1 (by rfl) ⟨3603743, by rfl⟩ : syracuseStep 4804991 = 7207487) B7207487
theorem B3203327 : Blo 1897435 3203327 := bstep (se 1 (by rfl) ⟨2402495, by rfl⟩ : syracuseStep 3203327 = 4804991) B4804991
theorem B2135551 : Blo 1897435 2135551 := bstep (se 1 (by rfl) ⟨1601663, by rfl⟩ : syracuseStep 2135551 = 3203327) B3203327
theorem B2847401 : Blo 1897435 2847401 := bstep (se 2 (by rfl) ⟨1067775, by rfl⟩ : syracuseStep 2847401 = 2135551) B2135551
theorem B1898267 : Blo 1897435 1898267 := bstep (se 1 (by rfl) ⟨1423700, by rfl⟩ : syracuseStep 1898267 = 2847401) B2847401
theorem B2702813 : Blo 1897435 2702813 := bbase (se 3 (by rfl) ⟨506777, by rfl⟩ : syracuseStep 2702813 = 1013555) (by norm_num)
theorem B7207501 : Blo 1897435 7207501 := bstep (se 3 (by rfl) ⟨1351406, by rfl⟩ : syracuseStep 7207501 = 2702813) B2702813
theorem B9610001 : Blo 1897435 9610001 := bstep (se 2 (by rfl) ⟨3603750, by rfl⟩ : syracuseStep 9610001 = 7207501) B7207501
theorem B6406667 : Blo 1897435 6406667 := bstep (se 1 (by rfl) ⟨4805000, by rfl⟩ : syracuseStep 6406667 = 9610001) B9610001
theorem B4271111 : Blo 1897435 4271111 := bstep (se 1 (by rfl) ⟨3203333, by rfl⟩ : syracuseStep 4271111 = 6406667) B6406667
theorem B2847407 : Blo 1897435 2847407 := bstep (se 1 (by rfl) ⟨2135555, by rfl⟩ : syracuseStep 2847407 = 4271111) B4271111
theorem B1898271 : Blo 1897435 1898271 := bstep (se 1 (by rfl) ⟨1423703, by rfl⟩ : syracuseStep 1898271 = 2847407) B2847407
theorem B2847413 : Blo 1897435 2847413 := bbase (se 5 (by rfl) ⟨133472, by rfl⟩ : syracuseStep 2847413 = 266945) (by norm_num)
theorem B1898275 : Blo 1897435 1898275 := bstep (se 1 (by rfl) ⟨1423706, by rfl⟩ : syracuseStep 1898275 = 2847413) B2847413
theorem B4805021 : Blo 1897435 4805021 := bbase (se 3 (by rfl) ⟨900941, by rfl⟩ : syracuseStep 4805021 = 1801883) (by norm_num)
theorem B3203347 : Blo 1897435 3203347 := bstep (se 1 (by rfl) ⟨2402510, by rfl⟩ : syracuseStep 3203347 = 4805021) B4805021
theorem B4271129 : Blo 1897435 4271129 := bstep (se 2 (by rfl) ⟨1601673, by rfl⟩ : syracuseStep 4271129 = 3203347) B3203347
theorem B2847419 : Blo 1897435 2847419 := bstep (se 1 (by rfl) ⟨2135564, by rfl⟩ : syracuseStep 2847419 = 4271129) B4271129
theorem B1898279 : Blo 1897435 1898279 := bstep (se 1 (by rfl) ⟨1423709, by rfl⟩ : syracuseStep 1898279 = 2847419) B2847419
theorem B2135569 : Blo 1897435 2135569 := bbase (se 2 (by rfl) ⟨800838, by rfl⟩ : syracuseStep 2135569 = 1601677) (by norm_num)
theorem B2847425 : Blo 1897435 2847425 := bstep (se 2 (by rfl) ⟨1067784, by rfl⟩ : syracuseStep 2847425 = 2135569) B2135569
theorem B1898283 : Blo 1897435 1898283 := bstep (se 1 (by rfl) ⟨1423712, by rfl⟩ : syracuseStep 1898283 = 2847425) B2847425
theorem B3603781 : Blo 1897435 3603781 := bbase (se 4 (by rfl) ⟨337854, by rfl⟩ : syracuseStep 3603781 = 675709) (by norm_num)
theorem B4805041 : Blo 1897435 4805041 := bstep (se 2 (by rfl) ⟨1801890, by rfl⟩ : syracuseStep 4805041 = 3603781) B3603781
theorem B6406721 : Blo 1897435 6406721 := bstep (se 2 (by rfl) ⟨2402520, by rfl⟩ : syracuseStep 6406721 = 4805041) B4805041
theorem B4271147 : Blo 1897435 4271147 := bstep (se 1 (by rfl) ⟨3203360, by rfl⟩ : syracuseStep 4271147 = 6406721) B6406721
theorem B2847431 : Blo 1897435 2847431 := bstep (se 1 (by rfl) ⟨2135573, by rfl⟩ : syracuseStep 2847431 = 4271147) B4271147
theorem B1898287 : Blo 1897435 1898287 := bstep (se 1 (by rfl) ⟨1423715, by rfl⟩ : syracuseStep 1898287 = 2847431) B2847431
theorem B2847437 : Blo 1897435 2847437 := bbase (se 3 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 2847437 = 1067789) (by norm_num)
theorem B1898291 : Blo 1897435 1898291 := bstep (se 1 (by rfl) ⟨1423718, by rfl⟩ : syracuseStep 1898291 = 2847437) B2847437
theorem B4271165 : Blo 1897435 4271165 := bbase (se 3 (by rfl) ⟨800843, by rfl⟩ : syracuseStep 4271165 = 1601687) (by norm_num)
theorem B2847443 : Blo 1897435 2847443 := bstep (se 1 (by rfl) ⟨2135582, by rfl⟩ : syracuseStep 2847443 = 4271165) B4271165
theorem B1898295 : Blo 1897435 1898295 := bstep (se 1 (by rfl) ⟨1423721, by rfl⟩ : syracuseStep 1898295 = 2847443) B2847443
theorem B3203381 : Blo 1897435 3203381 := bbase (se 5 (by rfl) ⟨150158, by rfl⟩ : syracuseStep 3203381 = 300317) (by norm_num)
theorem B2135587 : Blo 1897435 2135587 := bstep (se 1 (by rfl) ⟨1601690, by rfl⟩ : syracuseStep 2135587 = 3203381) B3203381
theorem B2847449 : Blo 1897435 2847449 := bstep (se 2 (by rfl) ⟨1067793, by rfl⟩ : syracuseStep 2847449 = 2135587) B2135587
theorem B1898299 : Blo 1897435 1898299 := bstep (se 1 (by rfl) ⟨1423724, by rfl⟩ : syracuseStep 1898299 = 2847449) B2847449
theorem B5405717 : Blo 1897435 5405717 := bbase (se 6 (by rfl) ⟨126696, by rfl⟩ : syracuseStep 5405717 = 253393) (by norm_num)
theorem B14415245 : Blo 1897435 14415245 := bstep (se 3 (by rfl) ⟨2702858, by rfl⟩ : syracuseStep 14415245 = 5405717) B5405717
theorem B9610163 : Blo 1897435 9610163 := bstep (se 1 (by rfl) ⟨7207622, by rfl⟩ : syracuseStep 9610163 = 14415245) B14415245
theorem B6406775 : Blo 1897435 6406775 := bstep (se 1 (by rfl) ⟨4805081, by rfl⟩ : syracuseStep 6406775 = 9610163) B9610163
theorem B4271183 : Blo 1897435 4271183 := bstep (se 1 (by rfl) ⟨3203387, by rfl⟩ : syracuseStep 4271183 = 6406775) B6406775
theorem B2847455 : Blo 1897435 2847455 := bstep (se 1 (by rfl) ⟨2135591, by rfl⟩ : syracuseStep 2847455 = 4271183) B4271183
theorem B1898303 : Blo 1897435 1898303 := bstep (se 1 (by rfl) ⟨1423727, by rfl⟩ : syracuseStep 1898303 = 2847455) B2847455
theorem B2847461 : Blo 1897435 2847461 := bbase (se 4 (by rfl) ⟨266949, by rfl⟩ : syracuseStep 2847461 = 533899) (by norm_num)
theorem B1898307 : Blo 1897435 1898307 := bstep (se 1 (by rfl) ⟨1423730, by rfl⟩ : syracuseStep 1898307 = 2847461) B2847461
theorem B2027153 : Blo 1897435 2027153 := bbase (se 2 (by rfl) ⟨760182, by rfl⟩ : syracuseStep 2027153 = 1520365) (by norm_num)
theorem B5405741 : Blo 1897435 5405741 := bstep (se 3 (by rfl) ⟨1013576, by rfl⟩ : syracuseStep 5405741 = 2027153) B2027153
theorem B3603827 : Blo 1897435 3603827 := bstep (se 1 (by rfl) ⟨2702870, by rfl⟩ : syracuseStep 3603827 = 5405741) B5405741
theorem B2402551 : Blo 1897435 2402551 := bstep (se 1 (by rfl) ⟨1801913, by rfl⟩ : syracuseStep 2402551 = 3603827) B3603827
theorem B3203401 : Blo 1897435 3203401 := bstep (se 2 (by rfl) ⟨1201275, by rfl⟩ : syracuseStep 3203401 = 2402551) B2402551
theorem B4271201 : Blo 1897435 4271201 := bstep (se 2 (by rfl) ⟨1601700, by rfl⟩ : syracuseStep 4271201 = 3203401) B3203401
theorem B2847467 : Blo 1897435 2847467 := bstep (se 1 (by rfl) ⟨2135600, by rfl⟩ : syracuseStep 2847467 = 4271201) B4271201
theorem B1898311 : Blo 1897435 1898311 := bstep (se 1 (by rfl) ⟨1423733, by rfl⟩ : syracuseStep 1898311 = 2847467) B2847467
theorem B2135605 : Blo 1897435 2135605 := bbase (se 5 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 2135605 = 200213) (by norm_num)
theorem B2847473 : Blo 1897435 2847473 := bstep (se 2 (by rfl) ⟨1067802, by rfl⟩ : syracuseStep 2847473 = 2135605) B2135605
theorem B1898315 : Blo 1897435 1898315 := bstep (se 1 (by rfl) ⟨1423736, by rfl⟩ : syracuseStep 1898315 = 2847473) B2847473
theorem B2402561 : Blo 1897435 2402561 := bbase (se 2 (by rfl) ⟨900960, by rfl⟩ : syracuseStep 2402561 = 1801921) (by norm_num)
theorem B6406829 : Blo 1897435 6406829 := bstep (se 3 (by rfl) ⟨1201280, by rfl⟩ : syracuseStep 6406829 = 2402561) B2402561
theorem B4271219 : Blo 1897435 4271219 := bstep (se 1 (by rfl) ⟨3203414, by rfl⟩ : syracuseStep 4271219 = 6406829) B6406829
theorem B2847479 : Blo 1897435 2847479 := bstep (se 1 (by rfl) ⟨2135609, by rfl⟩ : syracuseStep 2847479 = 4271219) B4271219
theorem B1898319 : Blo 1897435 1898319 := bstep (se 1 (by rfl) ⟨1423739, by rfl⟩ : syracuseStep 1898319 = 2847479) B2847479
theorem B2847485 : Blo 1897435 2847485 := bbase (se 3 (by rfl) ⟨533903, by rfl⟩ : syracuseStep 2847485 = 1067807) (by norm_num)
theorem B1898323 : Blo 1897435 1898323 := bstep (se 1 (by rfl) ⟨1423742, by rfl⟩ : syracuseStep 1898323 = 2847485) B2847485
theorem B4271237 : Blo 1897435 4271237 := bbase (se 4 (by rfl) ⟨400428, by rfl⟩ : syracuseStep 4271237 = 800857) (by norm_num)
theorem B2847491 : Blo 1897435 2847491 := bstep (se 1 (by rfl) ⟨2135618, by rfl⟩ : syracuseStep 2847491 = 4271237) B4271237
theorem B1898327 : Blo 1897435 1898327 := bstep (se 1 (by rfl) ⟨1423745, by rfl⟩ : syracuseStep 1898327 = 2847491) B2847491
theorem B4054349 : Blo 1897435 4054349 := bbase (se 3 (by rfl) ⟨760190, by rfl⟩ : syracuseStep 4054349 = 1520381) (by norm_num)
theorem B2702899 : Blo 1897435 2702899 := bstep (se 1 (by rfl) ⟨2027174, by rfl⟩ : syracuseStep 2702899 = 4054349) B4054349
theorem B3603865 : Blo 1897435 3603865 := bstep (se 2 (by rfl) ⟨1351449, by rfl⟩ : syracuseStep 3603865 = 2702899) B2702899
theorem B4805153 : Blo 1897435 4805153 := bstep (se 2 (by rfl) ⟨1801932, by rfl⟩ : syracuseStep 4805153 = 3603865) B3603865
theorem B3203435 : Blo 1897435 3203435 := bstep (se 1 (by rfl) ⟨2402576, by rfl⟩ : syracuseStep 3203435 = 4805153) B4805153
theorem B2135623 : Blo 1897435 2135623 := bstep (se 1 (by rfl) ⟨1601717, by rfl⟩ : syracuseStep 2135623 = 3203435) B3203435
theorem B2847497 : Blo 1897435 2847497 := bstep (se 2 (by rfl) ⟨1067811, by rfl⟩ : syracuseStep 2847497 = 2135623) B2135623
theorem B1898331 : Blo 1897435 1898331 := bstep (se 1 (by rfl) ⟨1423748, by rfl⟩ : syracuseStep 1898331 = 2847497) B2847497
theorem B9610325 : Blo 1897435 9610325 := bbase (se 8 (by rfl) ⟨56310, by rfl⟩ : syracuseStep 9610325 = 112621) (by norm_num)
theorem B6406883 : Blo 1897435 6406883 := bstep (se 1 (by rfl) ⟨4805162, by rfl⟩ : syracuseStep 6406883 = 9610325) B9610325
theorem B4271255 : Blo 1897435 4271255 := bstep (se 1 (by rfl) ⟨3203441, by rfl⟩ : syracuseStep 4271255 = 6406883) B6406883
theorem B2847503 : Blo 1897435 2847503 := bstep (se 1 (by rfl) ⟨2135627, by rfl⟩ : syracuseStep 2847503 = 4271255) B4271255
theorem B1898335 : Blo 1897435 1898335 := bstep (se 1 (by rfl) ⟨1423751, by rfl⟩ : syracuseStep 1898335 = 2847503) B2847503
theorem B2847509 : Blo 1897435 2847509 := bbase (se 6 (by rfl) ⟨66738, by rfl⟩ : syracuseStep 2847509 = 133477) (by norm_num)
theorem B1898339 : Blo 1897435 1898339 := bstep (se 1 (by rfl) ⟨1423754, by rfl⟩ : syracuseStep 1898339 = 2847509) B2847509
theorem B36489365 : Blo 1897435 36489365 := bbase (se 6 (by rfl) ⟨855219, by rfl⟩ : syracuseStep 36489365 = 1710439) (by norm_num)
theorem B24326243 : Blo 1897435 24326243 := bstep (se 1 (by rfl) ⟨18244682, by rfl⟩ : syracuseStep 24326243 = 36489365) B36489365
theorem B16217495 : Blo 1897435 16217495 := bstep (se 1 (by rfl) ⟨12163121, by rfl⟩ : syracuseStep 16217495 = 24326243) B24326243
theorem B10811663 : Blo 1897435 10811663 := bstep (se 1 (by rfl) ⟨8108747, by rfl⟩ : syracuseStep 10811663 = 16217495) B16217495
theorem B7207775 : Blo 1897435 7207775 := bstep (se 1 (by rfl) ⟨5405831, by rfl⟩ : syracuseStep 7207775 = 10811663) B10811663
theorem B4805183 : Blo 1897435 4805183 := bstep (se 1 (by rfl) ⟨3603887, by rfl⟩ : syracuseStep 4805183 = 7207775) B7207775
theorem B3203455 : Blo 1897435 3203455 := bstep (se 1 (by rfl) ⟨2402591, by rfl⟩ : syracuseStep 3203455 = 4805183) B4805183
theorem B4271273 : Blo 1897435 4271273 := bstep (se 2 (by rfl) ⟨1601727, by rfl⟩ : syracuseStep 4271273 = 3203455) B3203455
theorem B2847515 : Blo 1897435 2847515 := bstep (se 1 (by rfl) ⟨2135636, by rfl⟩ : syracuseStep 2847515 = 4271273) B4271273
theorem B1898343 : Blo 1897435 1898343 := bstep (se 1 (by rfl) ⟨1423757, by rfl⟩ : syracuseStep 1898343 = 2847515) B2847515
theorem B2135641 : Blo 1897435 2135641 := bbase (se 2 (by rfl) ⟨800865, by rfl⟩ : syracuseStep 2135641 = 1601731) (by norm_num)
theorem B2847521 : Blo 1897435 2847521 := bstep (se 2 (by rfl) ⟨1067820, by rfl⟩ : syracuseStep 2847521 = 2135641) B2135641
theorem B1898347 : Blo 1897435 1898347 := bstep (se 1 (by rfl) ⟨1423760, by rfl⟩ : syracuseStep 1898347 = 2847521) B2847521
theorem B3420893 : Blo 1897435 3420893 := bbase (se 3 (by rfl) ⟨641417, by rfl⟩ : syracuseStep 3420893 = 1282835) (by norm_num)
theorem B9122381 : Blo 1897435 9122381 := bstep (se 3 (by rfl) ⟨1710446, by rfl⟩ : syracuseStep 9122381 = 3420893) B3420893
theorem B6081587 : Blo 1897435 6081587 := bstep (se 1 (by rfl) ⟨4561190, by rfl⟩ : syracuseStep 6081587 = 9122381) B9122381
theorem B4054391 : Blo 1897435 4054391 := bstep (se 1 (by rfl) ⟨3040793, by rfl⟩ : syracuseStep 4054391 = 6081587) B6081587
theorem B2702927 : Blo 1897435 2702927 := bstep (se 1 (by rfl) ⟨2027195, by rfl⟩ : syracuseStep 2702927 = 4054391) B4054391
theorem B7207805 : Blo 1897435 7207805 := bstep (se 3 (by rfl) ⟨1351463, by rfl⟩ : syracuseStep 7207805 = 2702927) B2702927
theorem B4805203 : Blo 1897435 4805203 := bstep (se 1 (by rfl) ⟨3603902, by rfl⟩ : syracuseStep 4805203 = 7207805) B7207805
theorem B6406937 : Blo 1897435 6406937 := bstep (se 2 (by rfl) ⟨2402601, by rfl⟩ : syracuseStep 6406937 = 4805203) B4805203
theorem B4271291 : Blo 1897435 4271291 := bstep (se 1 (by rfl) ⟨3203468, by rfl⟩ : syracuseStep 4271291 = 6406937) B6406937
theorem B2847527 : Blo 1897435 2847527 := bstep (se 1 (by rfl) ⟨2135645, by rfl⟩ : syracuseStep 2847527 = 4271291) B4271291
theorem B1898351 : Blo 1897435 1898351 := bstep (se 1 (by rfl) ⟨1423763, by rfl⟩ : syracuseStep 1898351 = 2847527) B2847527
theorem B2847533 : Blo 1897435 2847533 := bbase (se 3 (by rfl) ⟨533912, by rfl⟩ : syracuseStep 2847533 = 1067825) (by norm_num)
theorem B1898355 : Blo 1897435 1898355 := bstep (se 1 (by rfl) ⟨1423766, by rfl⟩ : syracuseStep 1898355 = 2847533) B2847533
theorem B4271309 : Blo 1897435 4271309 := bbase (se 3 (by rfl) ⟨800870, by rfl⟩ : syracuseStep 4271309 = 1601741) (by norm_num)
theorem B2847539 : Blo 1897435 2847539 := bstep (se 1 (by rfl) ⟨2135654, by rfl⟩ : syracuseStep 2847539 = 4271309) B4271309
theorem B1898359 : Blo 1897435 1898359 := bstep (se 1 (by rfl) ⟨1423769, by rfl⟩ : syracuseStep 1898359 = 2847539) B2847539
theorem B2402617 : Blo 1897435 2402617 := bbase (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) (by norm_num)
theorem B3203489 : Blo 1897435 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B2135659 : Blo 1897435 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B2847545 : Blo 1897435 2847545 := bstep (se 2 (by rfl) ⟨1067829, by rfl⟩ : syracuseStep 2847545 = 2135659) B2135659
theorem B1898363 : Blo 1897435 1898363 := bstep (se 1 (by rfl) ⟨1423772, by rfl⟩ : syracuseStep 1898363 = 2847545) B2847545
theorem B6081637 : Blo 1897435 6081637 := bbase (se 4 (by rfl) ⟨570153, by rfl⟩ : syracuseStep 6081637 = 1140307) (by norm_num)
theorem B8108849 : Blo 1897435 8108849 := bstep (se 2 (by rfl) ⟨3040818, by rfl⟩ : syracuseStep 8108849 = 6081637) B6081637
theorem B21623597 : Blo 1897435 21623597 := bstep (se 3 (by rfl) ⟨4054424, by rfl⟩ : syracuseStep 21623597 = 8108849) B8108849
theorem B14415731 : Blo 1897435 14415731 := bstep (se 1 (by rfl) ⟨10811798, by rfl⟩ : syracuseStep 14415731 = 21623597) B21623597
theorem B9610487 : Blo 1897435 9610487 := bstep (se 1 (by rfl) ⟨7207865, by rfl⟩ : syracuseStep 9610487 = 14415731) B14415731
theorem B6406991 : Blo 1897435 6406991 := bstep (se 1 (by rfl) ⟨4805243, by rfl⟩ : syracuseStep 6406991 = 9610487) B9610487
theorem B4271327 : Blo 1897435 4271327 := bstep (se 1 (by rfl) ⟨3203495, by rfl⟩ : syracuseStep 4271327 = 6406991) B6406991
theorem B2847551 : Blo 1897435 2847551 := bstep (se 1 (by rfl) ⟨2135663, by rfl⟩ : syracuseStep 2847551 = 4271327) B4271327
theorem B1898367 : Blo 1897435 1898367 := bstep (se 1 (by rfl) ⟨1423775, by rfl⟩ : syracuseStep 1898367 = 2847551) B2847551
theorem B2847557 : Blo 1897435 2847557 := bbase (se 4 (by rfl) ⟨266958, by rfl⟩ : syracuseStep 2847557 = 533917) (by norm_num)
theorem B1898371 : Blo 1897435 1898371 := bstep (se 1 (by rfl) ⟨1423778, by rfl⟩ : syracuseStep 1898371 = 2847557) B2847557
theorem B3203509 : Blo 1897435 3203509 := bbase (se 5 (by rfl) ⟨150164, by rfl⟩ : syracuseStep 3203509 = 300329) (by norm_num)
theorem B4271345 : Blo 1897435 4271345 := bstep (se 2 (by rfl) ⟨1601754, by rfl⟩ : syracuseStep 4271345 = 3203509) B3203509
theorem B2847563 : Blo 1897435 2847563 := bstep (se 1 (by rfl) ⟨2135672, by rfl⟩ : syracuseStep 2847563 = 4271345) B4271345
theorem B1898375 : Blo 1897435 1898375 := bstep (se 1 (by rfl) ⟨1423781, by rfl⟩ : syracuseStep 1898375 = 2847563) B2847563
theorem B2135677 : Blo 1897435 2135677 := bbase (se 3 (by rfl) ⟨400439, by rfl⟩ : syracuseStep 2135677 = 800879) (by norm_num)
theorem B2847569 : Blo 1897435 2847569 := bstep (se 2 (by rfl) ⟨1067838, by rfl⟩ : syracuseStep 2847569 = 2135677) B2135677
theorem B1898379 : Blo 1897435 1898379 := bstep (se 1 (by rfl) ⟨1423784, by rfl⟩ : syracuseStep 1898379 = 2847569) B2847569
theorem B6407045 : Blo 1897435 6407045 := bbase (se 4 (by rfl) ⟨600660, by rfl⟩ : syracuseStep 6407045 = 1201321) (by norm_num)
theorem B4271363 : Blo 1897435 4271363 := bstep (se 1 (by rfl) ⟨3203522, by rfl⟩ : syracuseStep 4271363 = 6407045) B6407045
theorem B2847575 : Blo 1897435 2847575 := bstep (se 1 (by rfl) ⟨2135681, by rfl⟩ : syracuseStep 2847575 = 4271363) B4271363
theorem B1898383 : Blo 1897435 1898383 := bstep (se 1 (by rfl) ⟨1423787, by rfl⟩ : syracuseStep 1898383 = 2847575) B2847575
theorem B2847581 : Blo 1897435 2847581 := bbase (se 3 (by rfl) ⟨533921, by rfl⟩ : syracuseStep 2847581 = 1067843) (by norm_num)
theorem B1898387 : Blo 1897435 1898387 := bstep (se 1 (by rfl) ⟨1423790, by rfl⟩ : syracuseStep 1898387 = 2847581) B2847581
theorem B4271381 : Blo 1897435 4271381 := bbase (se 6 (by rfl) ⟨100110, by rfl⟩ : syracuseStep 4271381 = 200221) (by norm_num)
theorem B2847587 : Blo 1897435 2847587 := bstep (se 1 (by rfl) ⟨2135690, by rfl⟩ : syracuseStep 2847587 = 4271381) B4271381
theorem B1898391 : Blo 1897435 1898391 := bstep (se 1 (by rfl) ⟨1423793, by rfl⟩ : syracuseStep 1898391 = 2847587) B2847587
theorem B7207973 : Blo 1897435 7207973 := bbase (se 4 (by rfl) ⟨675747, by rfl⟩ : syracuseStep 7207973 = 1351495) (by norm_num)
theorem B4805315 : Blo 1897435 4805315 := bstep (se 1 (by rfl) ⟨3603986, by rfl⟩ : syracuseStep 4805315 = 7207973) B7207973
theorem B3203543 : Blo 1897435 3203543 := bstep (se 1 (by rfl) ⟨2402657, by rfl⟩ : syracuseStep 3203543 = 4805315) B4805315
theorem B2135695 : Blo 1897435 2135695 := bstep (se 1 (by rfl) ⟨1601771, by rfl⟩ : syracuseStep 2135695 = 3203543) B3203543
theorem B2847593 : Blo 1897435 2847593 := bstep (se 2 (by rfl) ⟨1067847, by rfl⟩ : syracuseStep 2847593 = 2135695) B2135695
theorem B1898395 : Blo 1897435 1898395 := bstep (se 1 (by rfl) ⟨1423796, by rfl⟩ : syracuseStep 1898395 = 2847593) B2847593
theorem B4054493 : Blo 1897435 4054493 := bbase (se 3 (by rfl) ⟨760217, by rfl⟩ : syracuseStep 4054493 = 1520435) (by norm_num)
theorem B10811981 : Blo 1897435 10811981 := bstep (se 3 (by rfl) ⟨2027246, by rfl⟩ : syracuseStep 10811981 = 4054493) B4054493
theorem B7207987 : Blo 1897435 7207987 := bstep (se 1 (by rfl) ⟨5405990, by rfl⟩ : syracuseStep 7207987 = 10811981) B10811981
theorem B9610649 : Blo 1897435 9610649 := bstep (se 2 (by rfl) ⟨3603993, by rfl⟩ : syracuseStep 9610649 = 7207987) B7207987
theorem B6407099 : Blo 1897435 6407099 := bstep (se 1 (by rfl) ⟨4805324, by rfl⟩ : syracuseStep 6407099 = 9610649) B9610649
theorem B4271399 : Blo 1897435 4271399 := bstep (se 1 (by rfl) ⟨3203549, by rfl⟩ : syracuseStep 4271399 = 6407099) B6407099
theorem B2847599 : Blo 1897435 2847599 := bstep (se 1 (by rfl) ⟨2135699, by rfl⟩ : syracuseStep 2847599 = 4271399) B4271399
theorem B1898399 : Blo 1897435 1898399 := bstep (se 1 (by rfl) ⟨1423799, by rfl⟩ : syracuseStep 1898399 = 2847599) B2847599
theorem B2847605 : Blo 1897435 2847605 := bbase (se 5 (by rfl) ⟨133481, by rfl⟩ : syracuseStep 2847605 = 266963) (by norm_num)
theorem B1898403 : Blo 1897435 1898403 := bstep (se 1 (by rfl) ⟨1423802, by rfl⟩ : syracuseStep 1898403 = 2847605) B2847605
theorem B3467669 : Blo 1897435 3467669 := bbase (se 6 (by rfl) ⟨81273, by rfl⟩ : syracuseStep 3467669 = 162547) (by norm_num)
theorem B9247117 : Blo 1897435 9247117 := bstep (se 3 (by rfl) ⟨1733834, by rfl⟩ : syracuseStep 9247117 = 3467669) B3467669
theorem B12329489 : Blo 1897435 12329489 := bstep (se 2 (by rfl) ⟨4623558, by rfl⟩ : syracuseStep 12329489 = 9247117) B9247117
theorem B8219659 : Blo 1897435 8219659 := bstep (se 1 (by rfl) ⟨6164744, by rfl⟩ : syracuseStep 8219659 = 12329489) B12329489
theorem B10959545 : Blo 1897435 10959545 := bstep (se 2 (by rfl) ⟨4109829, by rfl⟩ : syracuseStep 10959545 = 8219659) B8219659
theorem B7306363 : Blo 1897435 7306363 := bstep (se 1 (by rfl) ⟨5479772, by rfl⟩ : syracuseStep 7306363 = 10959545) B10959545
theorem B9741817 : Blo 1897435 9741817 := bstep (se 2 (by rfl) ⟨3653181, by rfl⟩ : syracuseStep 9741817 = 7306363) B7306363
theorem B12989089 : Blo 1897435 12989089 := bstep (se 2 (by rfl) ⟨4870908, by rfl⟩ : syracuseStep 12989089 = 9741817) B9741817
theorem B17318785 : Blo 1897435 17318785 := bstep (se 2 (by rfl) ⟨6494544, by rfl⟩ : syracuseStep 17318785 = 12989089) B12989089
theorem B23091713 : Blo 1897435 23091713 := bstep (se 2 (by rfl) ⟨8659392, by rfl⟩ : syracuseStep 23091713 = 17318785) B17318785
theorem B15394475 : Blo 1897435 15394475 := bstep (se 1 (by rfl) ⟨11545856, by rfl⟩ : syracuseStep 15394475 = 23091713) B23091713
theorem B10262983 : Blo 1897435 10262983 := bstep (se 1 (by rfl) ⟨7697237, by rfl⟩ : syracuseStep 10262983 = 15394475) B15394475
theorem B13683977 : Blo 1897435 13683977 := bstep (se 2 (by rfl) ⟨5131491, by rfl⟩ : syracuseStep 13683977 = 10262983) B10262983
theorem B9122651 : Blo 1897435 9122651 := bstep (se 1 (by rfl) ⟨6841988, by rfl⟩ : syracuseStep 9122651 = 13683977) B13683977
theorem B6081767 : Blo 1897435 6081767 := bstep (se 1 (by rfl) ⟨4561325, by rfl⟩ : syracuseStep 6081767 = 9122651) B9122651
theorem B4054511 : Blo 1897435 4054511 := bstep (se 1 (by rfl) ⟨3040883, by rfl⟩ : syracuseStep 4054511 = 6081767) B6081767
theorem B2703007 : Blo 1897435 2703007 := bstep (se 1 (by rfl) ⟨2027255, by rfl⟩ : syracuseStep 2703007 = 4054511) B4054511
theorem B3604009 : Blo 1897435 3604009 := bstep (se 2 (by rfl) ⟨1351503, by rfl⟩ : syracuseStep 3604009 = 2703007) B2703007
theorem B4805345 : Blo 1897435 4805345 := bstep (se 2 (by rfl) ⟨1802004, by rfl⟩ : syracuseStep 4805345 = 3604009) B3604009
theorem B3203563 : Blo 1897435 3203563 := bstep (se 1 (by rfl) ⟨2402672, by rfl⟩ : syracuseStep 3203563 = 4805345) B4805345
theorem B4271417 : Blo 1897435 4271417 := bstep (se 2 (by rfl) ⟨1601781, by rfl⟩ : syracuseStep 4271417 = 3203563) B3203563
theorem B2847611 : Blo 1897435 2847611 := bstep (se 1 (by rfl) ⟨2135708, by rfl⟩ : syracuseStep 2847611 = 4271417) B4271417
theorem B1898407 : Blo 1897435 1898407 := bstep (se 1 (by rfl) ⟨1423805, by rfl⟩ : syracuseStep 1898407 = 2847611) B2847611
theorem B2135713 : Blo 1897435 2135713 := bbase (se 2 (by rfl) ⟨800892, by rfl⟩ : syracuseStep 2135713 = 1601785) (by norm_num)
theorem B2847617 : Blo 1897435 2847617 := bstep (se 2 (by rfl) ⟨1067856, by rfl⟩ : syracuseStep 2847617 = 2135713) B2135713
theorem B1898411 : Blo 1897435 1898411 := bstep (se 1 (by rfl) ⟨1423808, by rfl⟩ : syracuseStep 1898411 = 2847617) B2847617
theorem B4805365 : Blo 1897435 4805365 := bbase (se 5 (by rfl) ⟨225251, by rfl⟩ : syracuseStep 4805365 = 450503) (by norm_num)
theorem B6407153 : Blo 1897435 6407153 := bstep (se 2 (by rfl) ⟨2402682, by rfl⟩ : syracuseStep 6407153 = 4805365) B4805365
theorem B4271435 : Blo 1897435 4271435 := bstep (se 1 (by rfl) ⟨3203576, by rfl⟩ : syracuseStep 4271435 = 6407153) B6407153
theorem B2847623 : Blo 1897435 2847623 := bstep (se 1 (by rfl) ⟨2135717, by rfl⟩ : syracuseStep 2847623 = 4271435) B4271435
theorem B1898415 : Blo 1897435 1898415 := bstep (se 1 (by rfl) ⟨1423811, by rfl⟩ : syracuseStep 1898415 = 2847623) B2847623
theorem B2847629 : Blo 1897435 2847629 := bbase (se 3 (by rfl) ⟨533930, by rfl⟩ : syracuseStep 2847629 = 1067861) (by norm_num)
theorem B1898419 : Blo 1897435 1898419 := bstep (se 1 (by rfl) ⟨1423814, by rfl⟩ : syracuseStep 1898419 = 2847629) B2847629
theorem B4271453 : Blo 1897435 4271453 := bbase (se 3 (by rfl) ⟨800897, by rfl⟩ : syracuseStep 4271453 = 1601795) (by norm_num)
theorem B2847635 : Blo 1897435 2847635 := bstep (se 1 (by rfl) ⟨2135726, by rfl⟩ : syracuseStep 2847635 = 4271453) B4271453
theorem B1898423 : Blo 1897435 1898423 := bstep (se 1 (by rfl) ⟨1423817, by rfl⟩ : syracuseStep 1898423 = 2847635) B2847635
theorem B3203597 : Blo 1897435 3203597 := bbase (se 3 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 3203597 = 1201349) (by norm_num)
theorem B2135731 : Blo 1897435 2135731 := bstep (se 1 (by rfl) ⟨1601798, by rfl⟩ : syracuseStep 2135731 = 3203597) B3203597
theorem B2847641 : Blo 1897435 2847641 := bstep (se 2 (by rfl) ⟨1067865, by rfl⟩ : syracuseStep 2847641 = 2135731) B2135731
theorem B1898427 : Blo 1897435 1898427 := bstep (se 1 (by rfl) ⟨1423820, by rfl⟩ : syracuseStep 1898427 = 2847641) B2847641
theorem B3421037 : Blo 1897435 3421037 := bbase (se 3 (by rfl) ⟨641444, by rfl⟩ : syracuseStep 3421037 = 1282889) (by norm_num)
theorem B2280691 : Blo 1897435 2280691 := bstep (se 1 (by rfl) ⟨1710518, by rfl⟩ : syracuseStep 2280691 = 3421037) B3421037
theorem B3040921 : Blo 1897435 3040921 := bstep (se 2 (by rfl) ⟨1140345, by rfl⟩ : syracuseStep 3040921 = 2280691) B2280691
theorem B16218245 : Blo 1897435 16218245 := bstep (se 4 (by rfl) ⟨1520460, by rfl⟩ : syracuseStep 16218245 = 3040921) B3040921
theorem B10812163 : Blo 1897435 10812163 := bstep (se 1 (by rfl) ⟨8109122, by rfl⟩ : syracuseStep 10812163 = 16218245) B16218245
theorem B14416217 : Blo 1897435 14416217 := bstep (se 2 (by rfl) ⟨5406081, by rfl⟩ : syracuseStep 14416217 = 10812163) B10812163
theorem B9610811 : Blo 1897435 9610811 := bstep (se 1 (by rfl) ⟨7208108, by rfl⟩ : syracuseStep 9610811 = 14416217) B14416217
theorem B6407207 : Blo 1897435 6407207 := bstep (se 1 (by rfl) ⟨4805405, by rfl⟩ : syracuseStep 6407207 = 9610811) B9610811
theorem B4271471 : Blo 1897435 4271471 := bstep (se 1 (by rfl) ⟨3203603, by rfl⟩ : syracuseStep 4271471 = 6407207) B6407207
theorem B2847647 : Blo 1897435 2847647 := bstep (se 1 (by rfl) ⟨2135735, by rfl⟩ : syracuseStep 2847647 = 4271471) B4271471
theorem B1898431 : Blo 1897435 1898431 := bstep (se 1 (by rfl) ⟨1423823, by rfl⟩ : syracuseStep 1898431 = 2847647) B2847647
theorem B2847653 : Blo 1897435 2847653 := bbase (se 4 (by rfl) ⟨266967, by rfl⟩ : syracuseStep 2847653 = 533935) (by norm_num)
theorem B1898435 : Blo 1897435 1898435 := bstep (se 1 (by rfl) ⟨1423826, by rfl⟩ : syracuseStep 1898435 = 2847653) B2847653
theorem B2402713 : Blo 1897435 2402713 := bbase (se 2 (by rfl) ⟨901017, by rfl⟩ : syracuseStep 2402713 = 1802035) (by norm_num)
theorem B3203617 : Blo 1897435 3203617 := bstep (se 2 (by rfl) ⟨1201356, by rfl⟩ : syracuseStep 3203617 = 2402713) B2402713
theorem B4271489 : Blo 1897435 4271489 := bstep (se 2 (by rfl) ⟨1601808, by rfl⟩ : syracuseStep 4271489 = 3203617) B3203617
theorem B2847659 : Blo 1897435 2847659 := bstep (se 1 (by rfl) ⟨2135744, by rfl⟩ : syracuseStep 2847659 = 4271489) B4271489
theorem B1898439 : Blo 1897435 1898439 := bstep (se 1 (by rfl) ⟨1423829, by rfl⟩ : syracuseStep 1898439 = 2847659) B2847659
theorem B2135749 : Blo 1897435 2135749 := bbase (se 4 (by rfl) ⟨200226, by rfl⟩ : syracuseStep 2135749 = 400453) (by norm_num)
theorem B2847665 : Blo 1897435 2847665 := bstep (se 2 (by rfl) ⟨1067874, by rfl⟩ : syracuseStep 2847665 = 2135749) B2135749
theorem B1898443 : Blo 1897435 1898443 := bstep (se 1 (by rfl) ⟨1423832, by rfl⟩ : syracuseStep 1898443 = 2847665) B2847665
theorem B3604085 : Blo 1897435 3604085 := bbase (se 5 (by rfl) ⟨168941, by rfl⟩ : syracuseStep 3604085 = 337883) (by norm_num)
theorem B2402723 : Blo 1897435 2402723 := bstep (se 1 (by rfl) ⟨1802042, by rfl⟩ : syracuseStep 2402723 = 3604085) B3604085
theorem B6407261 : Blo 1897435 6407261 := bstep (se 3 (by rfl) ⟨1201361, by rfl⟩ : syracuseStep 6407261 = 2402723) B2402723
theorem B4271507 : Blo 1897435 4271507 := bstep (se 1 (by rfl) ⟨3203630, by rfl⟩ : syracuseStep 4271507 = 6407261) B6407261
theorem B2847671 : Blo 1897435 2847671 := bstep (se 1 (by rfl) ⟨2135753, by rfl⟩ : syracuseStep 2847671 = 4271507) B4271507
theorem B1898447 : Blo 1897435 1898447 := bstep (se 1 (by rfl) ⟨1423835, by rfl⟩ : syracuseStep 1898447 = 2847671) B2847671
theorem B2847677 : Blo 1897435 2847677 := bbase (se 3 (by rfl) ⟨533939, by rfl⟩ : syracuseStep 2847677 = 1067879) (by norm_num)
theorem B1898451 : Blo 1897435 1898451 := bstep (se 1 (by rfl) ⟨1423838, by rfl⟩ : syracuseStep 1898451 = 2847677) B2847677
theorem B4271525 : Blo 1897435 4271525 := bbase (se 4 (by rfl) ⟨400455, by rfl⟩ : syracuseStep 4271525 = 800911) (by norm_num)
theorem B2847683 : Blo 1897435 2847683 := bstep (se 1 (by rfl) ⟨2135762, by rfl⟩ : syracuseStep 2847683 = 4271525) B4271525
theorem B1898455 : Blo 1897435 1898455 := bstep (se 1 (by rfl) ⟨1423841, by rfl⟩ : syracuseStep 1898455 = 2847683) B2847683
theorem B4805477 : Blo 1897435 4805477 := bbase (se 4 (by rfl) ⟨450513, by rfl⟩ : syracuseStep 4805477 = 901027) (by norm_num)
theorem B3203651 : Blo 1897435 3203651 := bstep (se 1 (by rfl) ⟨2402738, by rfl⟩ : syracuseStep 3203651 = 4805477) B4805477
theorem B2135767 : Blo 1897435 2135767 := bstep (se 1 (by rfl) ⟨1601825, by rfl⟩ : syracuseStep 2135767 = 3203651) B3203651
theorem B2847689 : Blo 1897435 2847689 := bstep (se 2 (by rfl) ⟨1067883, by rfl⟩ : syracuseStep 2847689 = 2135767) B2135767
theorem B1898459 : Blo 1897435 1898459 := bstep (se 1 (by rfl) ⟨1423844, by rfl⟩ : syracuseStep 1898459 = 2847689) B2847689
theorem B3040973 : Blo 1897435 3040973 := bbase (se 3 (by rfl) ⟨570182, by rfl⟩ : syracuseStep 3040973 = 1140365) (by norm_num)
theorem B2027315 : Blo 1897435 2027315 := bstep (se 1 (by rfl) ⟨1520486, by rfl⟩ : syracuseStep 2027315 = 3040973) B3040973
theorem B5406173 : Blo 1897435 5406173 := bstep (se 3 (by rfl) ⟨1013657, by rfl⟩ : syracuseStep 5406173 = 2027315) B2027315
theorem B3604115 : Blo 1897435 3604115 := bstep (se 1 (by rfl) ⟨2703086, by rfl⟩ : syracuseStep 3604115 = 5406173) B5406173
theorem B9610973 : Blo 1897435 9610973 := bstep (se 3 (by rfl) ⟨1802057, by rfl⟩ : syracuseStep 9610973 = 3604115) B3604115
theorem B6407315 : Blo 1897435 6407315 := bstep (se 1 (by rfl) ⟨4805486, by rfl⟩ : syracuseStep 6407315 = 9610973) B9610973
theorem B4271543 : Blo 1897435 4271543 := bstep (se 1 (by rfl) ⟨3203657, by rfl⟩ : syracuseStep 4271543 = 6407315) B6407315
theorem B2847695 : Blo 1897435 2847695 := bstep (se 1 (by rfl) ⟨2135771, by rfl⟩ : syracuseStep 2847695 = 4271543) B4271543
theorem B1898463 : Blo 1897435 1898463 := bstep (se 1 (by rfl) ⟨1423847, by rfl⟩ : syracuseStep 1898463 = 2847695) B2847695
theorem B2847701 : Blo 1897435 2847701 := bbase (se 7 (by rfl) ⟨33371, by rfl⟩ : syracuseStep 2847701 = 66743) (by norm_num)
theorem B1898467 : Blo 1897435 1898467 := bstep (se 1 (by rfl) ⟨1423850, by rfl⟩ : syracuseStep 1898467 = 2847701) B2847701
theorem B7208261 : Blo 1897435 7208261 := bbase (se 4 (by rfl) ⟨675774, by rfl⟩ : syracuseStep 7208261 = 1351549) (by norm_num)
theorem B4805507 : Blo 1897435 4805507 := bstep (se 1 (by rfl) ⟨3604130, by rfl⟩ : syracuseStep 4805507 = 7208261) B7208261
theorem B3203671 : Blo 1897435 3203671 := bstep (se 1 (by rfl) ⟨2402753, by rfl⟩ : syracuseStep 3203671 = 4805507) B4805507
theorem B4271561 : Blo 1897435 4271561 := bstep (se 2 (by rfl) ⟨1601835, by rfl⟩ : syracuseStep 4271561 = 3203671) B3203671
theorem B2847707 : Blo 1897435 2847707 := bstep (se 1 (by rfl) ⟨2135780, by rfl⟩ : syracuseStep 2847707 = 4271561) B4271561
theorem B1898471 : Blo 1897435 1898471 := bstep (se 1 (by rfl) ⟨1423853, by rfl⟩ : syracuseStep 1898471 = 2847707) B2847707
theorem B2135785 : Blo 1897435 2135785 := bbase (se 2 (by rfl) ⟨800919, by rfl⟩ : syracuseStep 2135785 = 1601839) (by norm_num)
theorem B2847713 : Blo 1897435 2847713 := bstep (se 2 (by rfl) ⟨1067892, by rfl⟩ : syracuseStep 2847713 = 2135785) B2135785
theorem B1898475 : Blo 1897435 1898475 := bstep (se 1 (by rfl) ⟨1423856, by rfl⟩ : syracuseStep 1898475 = 2847713) B2847713
theorem B10812437 : Blo 1897435 10812437 := bbase (se 6 (by rfl) ⟨253416, by rfl⟩ : syracuseStep 10812437 = 506833) (by norm_num)
theorem B7208291 : Blo 1897435 7208291 := bstep (se 1 (by rfl) ⟨5406218, by rfl⟩ : syracuseStep 7208291 = 10812437) B10812437
theorem B4805527 : Blo 1897435 4805527 := bstep (se 1 (by rfl) ⟨3604145, by rfl⟩ : syracuseStep 4805527 = 7208291) B7208291
theorem B6407369 : Blo 1897435 6407369 := bstep (se 2 (by rfl) ⟨2402763, by rfl⟩ : syracuseStep 6407369 = 4805527) B4805527
theorem B4271579 : Blo 1897435 4271579 := bstep (se 1 (by rfl) ⟨3203684, by rfl⟩ : syracuseStep 4271579 = 6407369) B6407369
theorem B2847719 : Blo 1897435 2847719 := bstep (se 1 (by rfl) ⟨2135789, by rfl⟩ : syracuseStep 2847719 = 4271579) B4271579
theorem B1898479 : Blo 1897435 1898479 := bstep (se 1 (by rfl) ⟨1423859, by rfl⟩ : syracuseStep 1898479 = 2847719) B2847719
theorem B2847725 : Blo 1897435 2847725 := bbase (se 3 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 2847725 = 1067897) (by norm_num)
theorem B1898483 : Blo 1897435 1898483 := bstep (se 1 (by rfl) ⟨1423862, by rfl⟩ : syracuseStep 1898483 = 2847725) B2847725
theorem B4271597 : Blo 1897435 4271597 := bbase (se 3 (by rfl) ⟨800924, by rfl⟩ : syracuseStep 4271597 = 1601849) (by norm_num)
theorem B2847731 : Blo 1897435 2847731 := bstep (se 1 (by rfl) ⟨2135798, by rfl⟩ : syracuseStep 2847731 = 4271597) B4271597
theorem B1898487 : Blo 1897435 1898487 := bstep (se 1 (by rfl) ⟨1423865, by rfl⟩ : syracuseStep 1898487 = 2847731) B2847731
theorem B6082037 : Blo 1897435 6082037 := bbase (se 5 (by rfl) ⟨285095, by rfl⟩ : syracuseStep 6082037 = 570191) (by norm_num)
theorem B4054691 : Blo 1897435 4054691 := bstep (se 1 (by rfl) ⟨3041018, by rfl⟩ : syracuseStep 4054691 = 6082037) B6082037
theorem B2703127 : Blo 1897435 2703127 := bstep (se 1 (by rfl) ⟨2027345, by rfl⟩ : syracuseStep 2703127 = 4054691) B4054691
theorem B3604169 : Blo 1897435 3604169 := bstep (se 2 (by rfl) ⟨1351563, by rfl⟩ : syracuseStep 3604169 = 2703127) B2703127
theorem B2402779 : Blo 1897435 2402779 := bstep (se 1 (by rfl) ⟨1802084, by rfl⟩ : syracuseStep 2402779 = 3604169) B3604169
theorem B3203705 : Blo 1897435 3203705 := bstep (se 2 (by rfl) ⟨1201389, by rfl⟩ : syracuseStep 3203705 = 2402779) B2402779
theorem B2135803 : Blo 1897435 2135803 := bstep (se 1 (by rfl) ⟨1601852, by rfl⟩ : syracuseStep 2135803 = 3203705) B3203705
theorem B2847737 : Blo 1897435 2847737 := bstep (se 2 (by rfl) ⟨1067901, by rfl⟩ : syracuseStep 2847737 = 2135803) B2135803
theorem B1898491 : Blo 1897435 1898491 := bstep (se 1 (by rfl) ⟨1423868, by rfl⟩ : syracuseStep 1898491 = 2847737) B2847737
theorem B22219157 : Blo 1897435 22219157 := bbase (se 6 (by rfl) ⟨520761, by rfl⟩ : syracuseStep 22219157 = 1041523) (by norm_num)
theorem B59251085 : Blo 1897435 59251085 := bstep (se 3 (by rfl) ⟨11109578, by rfl⟩ : syracuseStep 59251085 = 22219157) B22219157
theorem B39500723 : Blo 1897435 39500723 := bstep (se 1 (by rfl) ⟨29625542, by rfl⟩ : syracuseStep 39500723 = 59251085) B59251085
theorem B105335261 : Blo 1897435 105335261 := bstep (se 3 (by rfl) ⟨19750361, by rfl⟩ : syracuseStep 105335261 = 39500723) B39500723
theorem B70223507 : Blo 1897435 70223507 := bstep (se 1 (by rfl) ⟨52667630, by rfl⟩ : syracuseStep 70223507 = 105335261) B105335261
theorem B46815671 : Blo 1897435 46815671 := bstep (se 1 (by rfl) ⟨35111753, by rfl⟩ : syracuseStep 46815671 = 70223507) B70223507
theorem B31210447 : Blo 1897435 31210447 := bstep (se 1 (by rfl) ⟨23407835, by rfl⟩ : syracuseStep 31210447 = 46815671) B46815671
theorem B41613929 : Blo 1897435 41613929 := bstep (se 2 (by rfl) ⟨15605223, by rfl⟩ : syracuseStep 41613929 = 31210447) B31210447
theorem B27742619 : Blo 1897435 27742619 := bstep (se 1 (by rfl) ⟨20806964, by rfl⟩ : syracuseStep 27742619 = 41613929) B41613929
theorem B73980317 : Blo 1897435 73980317 := bstep (se 3 (by rfl) ⟨13871309, by rfl⟩ : syracuseStep 73980317 = 27742619) B27742619
theorem B49320211 : Blo 1897435 49320211 := bstep (se 1 (by rfl) ⟨36990158, by rfl⟩ : syracuseStep 49320211 = 73980317) B73980317
theorem B65760281 : Blo 1897435 65760281 := bstep (se 2 (by rfl) ⟨24660105, by rfl⟩ : syracuseStep 65760281 = 49320211) B49320211
theorem B43840187 : Blo 1897435 43840187 := bstep (se 1 (by rfl) ⟨32880140, by rfl⟩ : syracuseStep 43840187 = 65760281) B65760281
theorem B29226791 : Blo 1897435 29226791 := bstep (se 1 (by rfl) ⟨21920093, by rfl⟩ : syracuseStep 29226791 = 43840187) B43840187
theorem B77938109 : Blo 1897435 77938109 := bstep (se 3 (by rfl) ⟨14613395, by rfl⟩ : syracuseStep 77938109 = 29226791) B29226791
theorem B51958739 : Blo 1897435 51958739 := bstep (se 1 (by rfl) ⟨38969054, by rfl⟩ : syracuseStep 51958739 = 77938109) B77938109
theorem B34639159 : Blo 1897435 34639159 := bstep (se 1 (by rfl) ⟨25979369, by rfl⟩ : syracuseStep 34639159 = 51958739) B51958739
theorem B46185545 : Blo 1897435 46185545 := bstep (se 2 (by rfl) ⟨17319579, by rfl⟩ : syracuseStep 46185545 = 34639159) B34639159
theorem B30790363 : Blo 1897435 30790363 := bstep (se 1 (by rfl) ⟨23092772, by rfl⟩ : syracuseStep 30790363 = 46185545) B46185545
theorem B41053817 : Blo 1897435 41053817 := bstep (se 2 (by rfl) ⟨15395181, by rfl⟩ : syracuseStep 41053817 = 30790363) B30790363
theorem B109476845 : Blo 1897435 109476845 := bstep (se 3 (by rfl) ⟨20526908, by rfl⟩ : syracuseStep 109476845 = 41053817) B41053817
theorem B72984563 : Blo 1897435 72984563 := bstep (se 1 (by rfl) ⟨54738422, by rfl⟩ : syracuseStep 72984563 = 109476845) B109476845
theorem B48656375 : Blo 1897435 48656375 := bstep (se 1 (by rfl) ⟨36492281, by rfl⟩ : syracuseStep 48656375 = 72984563) B72984563
theorem B32437583 : Blo 1897435 32437583 := bstep (se 1 (by rfl) ⟨24328187, by rfl⟩ : syracuseStep 32437583 = 48656375) B48656375
theorem B21625055 : Blo 1897435 21625055 := bstep (se 1 (by rfl) ⟨16218791, by rfl⟩ : syracuseStep 21625055 = 32437583) B32437583
theorem B14416703 : Blo 1897435 14416703 := bstep (se 1 (by rfl) ⟨10812527, by rfl⟩ : syracuseStep 14416703 = 21625055) B21625055
theorem B9611135 : Blo 1897435 9611135 := bstep (se 1 (by rfl) ⟨7208351, by rfl⟩ : syracuseStep 9611135 = 14416703) B14416703
theorem B6407423 : Blo 1897435 6407423 := bstep (se 1 (by rfl) ⟨4805567, by rfl⟩ : syracuseStep 6407423 = 9611135) B9611135
theorem B4271615 : Blo 1897435 4271615 := bstep (se 1 (by rfl) ⟨3203711, by rfl⟩ : syracuseStep 4271615 = 6407423) B6407423
theorem B2847743 : Blo 1897435 2847743 := bstep (se 1 (by rfl) ⟨2135807, by rfl⟩ : syracuseStep 2847743 = 4271615) B4271615
theorem B1898495 : Blo 1897435 1898495 := bstep (se 1 (by rfl) ⟨1423871, by rfl⟩ : syracuseStep 1898495 = 2847743) B2847743
theorem B2847749 : Blo 1897435 2847749 := bbase (se 4 (by rfl) ⟨266976, by rfl⟩ : syracuseStep 2847749 = 533953) (by norm_num)
theorem B1898499 : Blo 1897435 1898499 := bstep (se 1 (by rfl) ⟨1423874, by rfl⟩ : syracuseStep 1898499 = 2847749) B2847749
theorem B3203725 : Blo 1897435 3203725 := bbase (se 3 (by rfl) ⟨600698, by rfl⟩ : syracuseStep 3203725 = 1201397) (by norm_num)
theorem B4271633 : Blo 1897435 4271633 := bstep (se 2 (by rfl) ⟨1601862, by rfl⟩ : syracuseStep 4271633 = 3203725) B3203725
theorem B2847755 : Blo 1897435 2847755 := bstep (se 1 (by rfl) ⟨2135816, by rfl⟩ : syracuseStep 2847755 = 4271633) B4271633
theorem B1898503 : Blo 1897435 1898503 := bstep (se 1 (by rfl) ⟨1423877, by rfl⟩ : syracuseStep 1898503 = 2847755) B2847755
theorem B2135821 : Blo 1897435 2135821 := bbase (se 3 (by rfl) ⟨400466, by rfl⟩ : syracuseStep 2135821 = 800933) (by norm_num)
theorem B2847761 : Blo 1897435 2847761 := bstep (se 2 (by rfl) ⟨1067910, by rfl⟩ : syracuseStep 2847761 = 2135821) B2135821
theorem B1898507 : Blo 1897435 1898507 := bstep (se 1 (by rfl) ⟨1423880, by rfl⟩ : syracuseStep 1898507 = 2847761) B2847761
theorem B6407477 : Blo 1897435 6407477 := bbase (se 5 (by rfl) ⟨300350, by rfl⟩ : syracuseStep 6407477 = 600701) (by norm_num)
theorem B4271651 : Blo 1897435 4271651 := bstep (se 1 (by rfl) ⟨3203738, by rfl⟩ : syracuseStep 4271651 = 6407477) B6407477
theorem B2847767 : Blo 1897435 2847767 := bstep (se 1 (by rfl) ⟨2135825, by rfl⟩ : syracuseStep 2847767 = 4271651) B4271651
theorem B1898511 : Blo 1897435 1898511 := bstep (se 1 (by rfl) ⟨1423883, by rfl⟩ : syracuseStep 1898511 = 2847767) B2847767
theorem B2847773 : Blo 1897435 2847773 := bbase (se 3 (by rfl) ⟨533957, by rfl⟩ : syracuseStep 2847773 = 1067915) (by norm_num)
theorem B1898515 : Blo 1897435 1898515 := bstep (se 1 (by rfl) ⟨1423886, by rfl⟩ : syracuseStep 1898515 = 2847773) B2847773
theorem B4271669 : Blo 1897435 4271669 := bbase (se 5 (by rfl) ⟨200234, by rfl⟩ : syracuseStep 4271669 = 400469) (by norm_num)
theorem B2847779 : Blo 1897435 2847779 := bstep (se 1 (by rfl) ⟨2135834, by rfl⟩ : syracuseStep 2847779 = 4271669) B4271669
theorem B1898519 : Blo 1897435 1898519 := bstep (se 1 (by rfl) ⟨1423889, by rfl⟩ : syracuseStep 1898519 = 2847779) B2847779
theorem B3041069 : Blo 1897435 3041069 := bbase (se 3 (by rfl) ⟨570200, by rfl⟩ : syracuseStep 3041069 = 1140401) (by norm_num)
theorem B8109517 : Blo 1897435 8109517 := bstep (se 3 (by rfl) ⟨1520534, by rfl⟩ : syracuseStep 8109517 = 3041069) B3041069
theorem B10812689 : Blo 1897435 10812689 := bstep (se 2 (by rfl) ⟨4054758, by rfl⟩ : syracuseStep 10812689 = 8109517) B8109517
theorem B7208459 : Blo 1897435 7208459 := bstep (se 1 (by rfl) ⟨5406344, by rfl⟩ : syracuseStep 7208459 = 10812689) B10812689
theorem B4805639 : Blo 1897435 4805639 := bstep (se 1 (by rfl) ⟨3604229, by rfl⟩ : syracuseStep 4805639 = 7208459) B7208459
theorem B3203759 : Blo 1897435 3203759 := bstep (se 1 (by rfl) ⟨2402819, by rfl⟩ : syracuseStep 3203759 = 4805639) B4805639
theorem B2135839 : Blo 1897435 2135839 := bstep (se 1 (by rfl) ⟨1601879, by rfl⟩ : syracuseStep 2135839 = 3203759) B3203759
theorem B2847785 : Blo 1897435 2847785 := bstep (se 2 (by rfl) ⟨1067919, by rfl⟩ : syracuseStep 2847785 = 2135839) B2135839
theorem B1898523 : Blo 1897435 1898523 := bstep (se 1 (by rfl) ⟨1423892, by rfl⟩ : syracuseStep 1898523 = 2847785) B2847785
theorem B4561613 : Blo 1897435 4561613 := bbase (se 3 (by rfl) ⟨855302, by rfl⟩ : syracuseStep 4561613 = 1710605) (by norm_num)
theorem B3041075 : Blo 1897435 3041075 := bstep (se 1 (by rfl) ⟨2280806, by rfl⟩ : syracuseStep 3041075 = 4561613) B4561613
theorem B8109533 : Blo 1897435 8109533 := bstep (se 3 (by rfl) ⟨1520537, by rfl⟩ : syracuseStep 8109533 = 3041075) B3041075
theorem B5406355 : Blo 1897435 5406355 := bstep (se 1 (by rfl) ⟨4054766, by rfl⟩ : syracuseStep 5406355 = 8109533) B8109533
theorem B7208473 : Blo 1897435 7208473 := bstep (se 2 (by rfl) ⟨2703177, by rfl⟩ : syracuseStep 7208473 = 5406355) B5406355
theorem B9611297 : Blo 1897435 9611297 := bstep (se 2 (by rfl) ⟨3604236, by rfl⟩ : syracuseStep 9611297 = 7208473) B7208473
theorem B6407531 : Blo 1897435 6407531 := bstep (se 1 (by rfl) ⟨4805648, by rfl⟩ : syracuseStep 6407531 = 9611297) B9611297
theorem B4271687 : Blo 1897435 4271687 := bstep (se 1 (by rfl) ⟨3203765, by rfl⟩ : syracuseStep 4271687 = 6407531) B6407531
theorem B2847791 : Blo 1897435 2847791 := bstep (se 1 (by rfl) ⟨2135843, by rfl⟩ : syracuseStep 2847791 = 4271687) B4271687
theorem B1898527 : Blo 1897435 1898527 := bstep (se 1 (by rfl) ⟨1423895, by rfl⟩ : syracuseStep 1898527 = 2847791) B2847791
theorem B2847797 : Blo 1897435 2847797 := bbase (se 5 (by rfl) ⟨133490, by rfl⟩ : syracuseStep 2847797 = 266981) (by norm_num)
theorem B1898531 : Blo 1897435 1898531 := bstep (se 1 (by rfl) ⟨1423898, by rfl⟩ : syracuseStep 1898531 = 2847797) B2847797
theorem B4805669 : Blo 1897435 4805669 := bbase (se 4 (by rfl) ⟨450531, by rfl⟩ : syracuseStep 4805669 = 901063) (by norm_num)
theorem B3203779 : Blo 1897435 3203779 := bstep (se 1 (by rfl) ⟨2402834, by rfl⟩ : syracuseStep 3203779 = 4805669) B4805669
theorem B4271705 : Blo 1897435 4271705 := bstep (se 2 (by rfl) ⟨1601889, by rfl⟩ : syracuseStep 4271705 = 3203779) B3203779
theorem B2847803 : Blo 1897435 2847803 := bstep (se 1 (by rfl) ⟨2135852, by rfl⟩ : syracuseStep 2847803 = 4271705) B4271705
theorem B1898535 : Blo 1897435 1898535 := bstep (se 1 (by rfl) ⟨1423901, by rfl⟩ : syracuseStep 1898535 = 2847803) B2847803
theorem B2135857 : Blo 1897435 2135857 := bbase (se 2 (by rfl) ⟨800946, by rfl⟩ : syracuseStep 2135857 = 1601893) (by norm_num)
theorem B2847809 : Blo 1897435 2847809 := bstep (se 2 (by rfl) ⟨1067928, by rfl⟩ : syracuseStep 2847809 = 2135857) B2135857
theorem B1898539 : Blo 1897435 1898539 := bstep (se 1 (by rfl) ⟨1423904, by rfl⟩ : syracuseStep 1898539 = 2847809) B2847809
theorem B3041101 : Blo 1897435 3041101 := bbase (se 3 (by rfl) ⟨570206, by rfl⟩ : syracuseStep 3041101 = 1140413) (by norm_num)
theorem B4054801 : Blo 1897435 4054801 := bstep (se 2 (by rfl) ⟨1520550, by rfl⟩ : syracuseStep 4054801 = 3041101) B3041101
theorem B5406401 : Blo 1897435 5406401 := bstep (se 2 (by rfl) ⟨2027400, by rfl⟩ : syracuseStep 5406401 = 4054801) B4054801
theorem B3604267 : Blo 1897435 3604267 := bstep (se 1 (by rfl) ⟨2703200, by rfl⟩ : syracuseStep 3604267 = 5406401) B5406401
theorem B4805689 : Blo 1897435 4805689 := bstep (se 2 (by rfl) ⟨1802133, by rfl⟩ : syracuseStep 4805689 = 3604267) B3604267
theorem B6407585 : Blo 1897435 6407585 := bstep (se 2 (by rfl) ⟨2402844, by rfl⟩ : syracuseStep 6407585 = 4805689) B4805689
theorem B4271723 : Blo 1897435 4271723 := bstep (se 1 (by rfl) ⟨3203792, by rfl⟩ : syracuseStep 4271723 = 6407585) B6407585
theorem B2847815 : Blo 1897435 2847815 := bstep (se 1 (by rfl) ⟨2135861, by rfl⟩ : syracuseStep 2847815 = 4271723) B4271723
theorem B1898543 : Blo 1897435 1898543 := bstep (se 1 (by rfl) ⟨1423907, by rfl⟩ : syracuseStep 1898543 = 2847815) B2847815
theorem B2847821 : Blo 1897435 2847821 := bbase (se 3 (by rfl) ⟨533966, by rfl⟩ : syracuseStep 2847821 = 1067933) (by norm_num)
theorem B1898547 : Blo 1897435 1898547 := bstep (se 1 (by rfl) ⟨1423910, by rfl⟩ : syracuseStep 1898547 = 2847821) B2847821
theorem B4271741 : Blo 1897435 4271741 := bbase (se 3 (by rfl) ⟨800951, by rfl⟩ : syracuseStep 4271741 = 1601903) (by norm_num)
theorem B2847827 : Blo 1897435 2847827 := bstep (se 1 (by rfl) ⟨2135870, by rfl⟩ : syracuseStep 2847827 = 4271741) B4271741
theorem B1898551 : Blo 1897435 1898551 := bstep (se 1 (by rfl) ⟨1423913, by rfl⟩ : syracuseStep 1898551 = 2847827) B2847827
theorem B3203813 : Blo 1897435 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B2135875 : Blo 1897435 2135875 := bstep (se 1 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 2135875 = 3203813) B3203813
theorem B2847833 : Blo 1897435 2847833 := bstep (se 2 (by rfl) ⟨1067937, by rfl⟩ : syracuseStep 2847833 = 2135875) B2135875
theorem B1898555 : Blo 1897435 1898555 := bstep (se 1 (by rfl) ⟨1423916, by rfl⟩ : syracuseStep 1898555 = 2847833) B2847833
theorem B2280845 : Blo 1897435 2280845 := bbase (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) (by norm_num)
theorem B6082253 : Blo 1897435 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B4054835 : Blo 1897435 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B2703223 : Blo 1897435 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B14417189 : Blo 1897435 14417189 := bstep (se 4 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 14417189 = 2703223) B2703223
theorem B9611459 : Blo 1897435 9611459 := bstep (se 1 (by rfl) ⟨7208594, by rfl⟩ : syracuseStep 9611459 = 14417189) B14417189
theorem B6407639 : Blo 1897435 6407639 := bstep (se 1 (by rfl) ⟨4805729, by rfl⟩ : syracuseStep 6407639 = 9611459) B9611459
theorem B4271759 : Blo 1897435 4271759 := bstep (se 1 (by rfl) ⟨3203819, by rfl⟩ : syracuseStep 4271759 = 6407639) B6407639
theorem B2847839 : Blo 1897435 2847839 := bstep (se 1 (by rfl) ⟨2135879, by rfl⟩ : syracuseStep 2847839 = 4271759) B4271759
theorem B1898559 : Blo 1897435 1898559 := bstep (se 1 (by rfl) ⟨1423919, by rfl⟩ : syracuseStep 1898559 = 2847839) B2847839
theorem B2847845 : Blo 1897435 2847845 := bbase (se 4 (by rfl) ⟨266985, by rfl⟩ : syracuseStep 2847845 = 533971) (by norm_num)
theorem B1898563 : Blo 1897435 1898563 := bstep (se 1 (by rfl) ⟨1423922, by rfl⟩ : syracuseStep 1898563 = 2847845) B2847845
theorem B4054853 : Blo 1897435 4054853 := bbase (se 4 (by rfl) ⟨380142, by rfl⟩ : syracuseStep 4054853 = 760285) (by norm_num)
theorem B2703235 : Blo 1897435 2703235 := bstep (se 1 (by rfl) ⟨2027426, by rfl⟩ : syracuseStep 2703235 = 4054853) B4054853
theorem B3604313 : Blo 1897435 3604313 := bstep (se 2 (by rfl) ⟨1351617, by rfl⟩ : syracuseStep 3604313 = 2703235) B2703235
theorem B2402875 : Blo 1897435 2402875 := bstep (se 1 (by rfl) ⟨1802156, by rfl⟩ : syracuseStep 2402875 = 3604313) B3604313
theorem B3203833 : Blo 1897435 3203833 := bstep (se 2 (by rfl) ⟨1201437, by rfl⟩ : syracuseStep 3203833 = 2402875) B2402875
theorem B4271777 : Blo 1897435 4271777 := bstep (se 2 (by rfl) ⟨1601916, by rfl⟩ : syracuseStep 4271777 = 3203833) B3203833
theorem B2847851 : Blo 1897435 2847851 := bstep (se 1 (by rfl) ⟨2135888, by rfl⟩ : syracuseStep 2847851 = 4271777) B4271777
theorem B1898567 : Blo 1897435 1898567 := bstep (se 1 (by rfl) ⟨1423925, by rfl⟩ : syracuseStep 1898567 = 2847851) B2847851
theorem B2135893 : Blo 1897435 2135893 := bbase (se 9 (by rfl) ⟨6257, by rfl⟩ : syracuseStep 2135893 = 12515) (by norm_num)
theorem B2847857 : Blo 1897435 2847857 := bstep (se 2 (by rfl) ⟨1067946, by rfl⟩ : syracuseStep 2847857 = 2135893) B2135893
theorem B1898571 : Blo 1897435 1898571 := bstep (se 1 (by rfl) ⟨1423928, by rfl⟩ : syracuseStep 1898571 = 2847857) B2847857
theorem B2402885 : Blo 1897435 2402885 := bbase (se 4 (by rfl) ⟨225270, by rfl⟩ : syracuseStep 2402885 = 450541) (by norm_num)
theorem B6407693 : Blo 1897435 6407693 := bstep (se 3 (by rfl) ⟨1201442, by rfl⟩ : syracuseStep 6407693 = 2402885) B2402885
theorem B4271795 : Blo 1897435 4271795 := bstep (se 1 (by rfl) ⟨3203846, by rfl⟩ : syracuseStep 4271795 = 6407693) B6407693
theorem B2847863 : Blo 1897435 2847863 := bstep (se 1 (by rfl) ⟨2135897, by rfl⟩ : syracuseStep 2847863 = 4271795) B4271795
theorem B1898575 : Blo 1897435 1898575 := bstep (se 1 (by rfl) ⟨1423931, by rfl⟩ : syracuseStep 1898575 = 2847863) B2847863
theorem B2847869 : Blo 1897435 2847869 := bbase (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) (by norm_num)
theorem B1898579 : Blo 1897435 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B4271813 : Blo 1897435 4271813 := bbase (se 4 (by rfl) ⟨400482, by rfl⟩ : syracuseStep 4271813 = 800965) (by norm_num)
theorem B2847875 : Blo 1897435 2847875 := bstep (se 1 (by rfl) ⟨2135906, by rfl⟩ : syracuseStep 2847875 = 4271813) B4271813
theorem B1898583 : Blo 1897435 1898583 := bstep (se 1 (by rfl) ⟨1423937, by rfl⟩ : syracuseStep 1898583 = 2847875) B2847875
theorem B8660213 : Blo 1897435 8660213 := bbase (se 5 (by rfl) ⟨405947, by rfl⟩ : syracuseStep 8660213 = 811895) (by norm_num)
theorem B5773475 : Blo 1897435 5773475 := bstep (se 1 (by rfl) ⟨4330106, by rfl⟩ : syracuseStep 5773475 = 8660213) B8660213
theorem B15395933 : Blo 1897435 15395933 := bstep (se 3 (by rfl) ⟨2886737, by rfl⟩ : syracuseStep 15395933 = 5773475) B5773475
theorem B41055821 : Blo 1897435 41055821 := bstep (se 3 (by rfl) ⟨7697966, by rfl⟩ : syracuseStep 41055821 = 15395933) B15395933
theorem B27370547 : Blo 1897435 27370547 := bstep (se 1 (by rfl) ⟨20527910, by rfl⟩ : syracuseStep 27370547 = 41055821) B41055821
theorem B18247031 : Blo 1897435 18247031 := bstep (se 1 (by rfl) ⟨13685273, by rfl⟩ : syracuseStep 18247031 = 27370547) B27370547
theorem B12164687 : Blo 1897435 12164687 := bstep (se 1 (by rfl) ⟨9123515, by rfl⟩ : syracuseStep 12164687 = 18247031) B18247031
theorem B8109791 : Blo 1897435 8109791 := bstep (se 1 (by rfl) ⟨6082343, by rfl⟩ : syracuseStep 8109791 = 12164687) B12164687
theorem B5406527 : Blo 1897435 5406527 := bstep (se 1 (by rfl) ⟨4054895, by rfl⟩ : syracuseStep 5406527 = 8109791) B8109791
theorem B3604351 : Blo 1897435 3604351 := bstep (se 1 (by rfl) ⟨2703263, by rfl⟩ : syracuseStep 3604351 = 5406527) B5406527
theorem B4805801 : Blo 1897435 4805801 := bstep (se 2 (by rfl) ⟨1802175, by rfl⟩ : syracuseStep 4805801 = 3604351) B3604351
theorem B3203867 : Blo 1897435 3203867 := bstep (se 1 (by rfl) ⟨2402900, by rfl⟩ : syracuseStep 3203867 = 4805801) B4805801
theorem B2135911 : Blo 1897435 2135911 := bstep (se 1 (by rfl) ⟨1601933, by rfl⟩ : syracuseStep 2135911 = 3203867) B3203867
theorem B2847881 : Blo 1897435 2847881 := bstep (se 2 (by rfl) ⟨1067955, by rfl⟩ : syracuseStep 2847881 = 2135911) B2135911
theorem B1898587 : Blo 1897435 1898587 := bstep (se 1 (by rfl) ⟨1423940, by rfl⟩ : syracuseStep 1898587 = 2847881) B2847881
theorem B9611621 : Blo 1897435 9611621 := bbase (se 4 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 9611621 = 1802179) (by norm_num)
theorem B6407747 : Blo 1897435 6407747 := bstep (se 1 (by rfl) ⟨4805810, by rfl⟩ : syracuseStep 6407747 = 9611621) B9611621
theorem B4271831 : Blo 1897435 4271831 := bstep (se 1 (by rfl) ⟨3203873, by rfl⟩ : syracuseStep 4271831 = 6407747) B6407747
theorem B2847887 : Blo 1897435 2847887 := bstep (se 1 (by rfl) ⟨2135915, by rfl⟩ : syracuseStep 2847887 = 4271831) B4271831
theorem B1898591 : Blo 1897435 1898591 := bstep (se 1 (by rfl) ⟨1423943, by rfl⟩ : syracuseStep 1898591 = 2847887) B2847887
theorem B2847893 : Blo 1897435 2847893 := bbase (se 6 (by rfl) ⟨66747, by rfl⟩ : syracuseStep 2847893 = 133495) (by norm_num)
theorem B1898595 : Blo 1897435 1898595 := bstep (se 1 (by rfl) ⟨1423946, by rfl⟩ : syracuseStep 1898595 = 2847893) B2847893
theorem B2280893 : Blo 1897435 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B6082381 : Blo 1897435 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B8109841 : Blo 1897435 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B10813121 : Blo 1897435 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B7208747 : Blo 1897435 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B4805831 : Blo 1897435 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B3203887 : Blo 1897435 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B4271849 : Blo 1897435 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B2847899 : Blo 1897435 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B1898599 : Blo 1897435 1898599 := bstep (se 1 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 1898599 = 2847899) B2847899
theorem B2135929 : Blo 1897435 2135929 := bbase (se 2 (by rfl) ⟨800973, by rfl⟩ : syracuseStep 2135929 = 1601947) (by norm_num)
theorem B2847905 : Blo 1897435 2847905 := bstep (se 2 (by rfl) ⟨1067964, by rfl⟩ : syracuseStep 2847905 = 2135929) B2135929
theorem B1898603 : Blo 1897435 1898603 := bstep (se 1 (by rfl) ⟨1423952, by rfl⟩ : syracuseStep 1898603 = 2847905) B2847905
theorem B4561805 : Blo 1897435 4561805 := bbase (se 3 (by rfl) ⟨855338, by rfl⟩ : syracuseStep 4561805 = 1710677) (by norm_num)
theorem B12164813 : Blo 1897435 12164813 := bstep (se 3 (by rfl) ⟨2280902, by rfl⟩ : syracuseStep 12164813 = 4561805) B4561805
theorem B8109875 : Blo 1897435 8109875 := bstep (se 1 (by rfl) ⟨6082406, by rfl⟩ : syracuseStep 8109875 = 12164813) B12164813
theorem B5406583 : Blo 1897435 5406583 := bstep (se 1 (by rfl) ⟨4054937, by rfl⟩ : syracuseStep 5406583 = 8109875) B8109875
theorem B7208777 : Blo 1897435 7208777 := bstep (se 2 (by rfl) ⟨2703291, by rfl⟩ : syracuseStep 7208777 = 5406583) B5406583
theorem B4805851 : Blo 1897435 4805851 := bstep (se 1 (by rfl) ⟨3604388, by rfl⟩ : syracuseStep 4805851 = 7208777) B7208777
theorem B6407801 : Blo 1897435 6407801 := bstep (se 2 (by rfl) ⟨2402925, by rfl⟩ : syracuseStep 6407801 = 4805851) B4805851
theorem B4271867 : Blo 1897435 4271867 := bstep (se 1 (by rfl) ⟨3203900, by rfl⟩ : syracuseStep 4271867 = 6407801) B6407801
theorem B2847911 : Blo 1897435 2847911 := bstep (se 1 (by rfl) ⟨2135933, by rfl⟩ : syracuseStep 2847911 = 4271867) B4271867
theorem B1898607 : Blo 1897435 1898607 := bstep (se 1 (by rfl) ⟨1423955, by rfl⟩ : syracuseStep 1898607 = 2847911) B2847911
theorem B2847917 : Blo 1897435 2847917 := bbase (se 3 (by rfl) ⟨533984, by rfl⟩ : syracuseStep 2847917 = 1067969) (by norm_num)
theorem B1898611 : Blo 1897435 1898611 := bstep (se 1 (by rfl) ⟨1423958, by rfl⟩ : syracuseStep 1898611 = 2847917) B2847917
theorem B4271885 : Blo 1897435 4271885 := bbase (se 3 (by rfl) ⟨800978, by rfl⟩ : syracuseStep 4271885 = 1601957) (by norm_num)
theorem B2847923 : Blo 1897435 2847923 := bstep (se 1 (by rfl) ⟨2135942, by rfl⟩ : syracuseStep 2847923 = 4271885) B4271885
theorem B1898615 : Blo 1897435 1898615 := bstep (se 1 (by rfl) ⟨1423961, by rfl⟩ : syracuseStep 1898615 = 2847923) B2847923
theorem B2402941 : Blo 1897435 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B3203921 : Blo 1897435 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B2135947 : Blo 1897435 2135947 := bstep (se 1 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 2135947 = 3203921) B3203921
theorem B2847929 : Blo 1897435 2847929 := bstep (se 2 (by rfl) ⟨1067973, by rfl⟩ : syracuseStep 2847929 = 2135947) B2135947
theorem B1898619 : Blo 1897435 1898619 := bstep (se 1 (by rfl) ⟨1423964, by rfl⟩ : syracuseStep 1898619 = 2847929) B2847929
theorem B2566037 : Blo 1897435 2566037 := bbase (se 6 (by rfl) ⟨60141, by rfl⟩ : syracuseStep 2566037 = 120283) (by norm_num)
theorem B6842765 : Blo 1897435 6842765 := bstep (se 3 (by rfl) ⟨1283018, by rfl⟩ : syracuseStep 6842765 = 2566037) B2566037
theorem B4561843 : Blo 1897435 4561843 := bstep (se 1 (by rfl) ⟨3421382, by rfl⟩ : syracuseStep 4561843 = 6842765) B6842765
theorem B6082457 : Blo 1897435 6082457 := bstep (se 2 (by rfl) ⟨2280921, by rfl⟩ : syracuseStep 6082457 = 4561843) B4561843
theorem B16219885 : Blo 1897435 16219885 := bstep (se 3 (by rfl) ⟨3041228, by rfl⟩ : syracuseStep 16219885 = 6082457) B6082457
theorem B21626513 : Blo 1897435 21626513 := bstep (se 2 (by rfl) ⟨8109942, by rfl⟩ : syracuseStep 21626513 = 16219885) B16219885
theorem B14417675 : Blo 1897435 14417675 := bstep (se 1 (by rfl) ⟨10813256, by rfl⟩ : syracuseStep 14417675 = 21626513) B21626513
theorem B9611783 : Blo 1897435 9611783 := bstep (se 1 (by rfl) ⟨7208837, by rfl⟩ : syracuseStep 9611783 = 14417675) B14417675
theorem B6407855 : Blo 1897435 6407855 := bstep (se 1 (by rfl) ⟨4805891, by rfl⟩ : syracuseStep 6407855 = 9611783) B9611783
theorem B4271903 : Blo 1897435 4271903 := bstep (se 1 (by rfl) ⟨3203927, by rfl⟩ : syracuseStep 4271903 = 6407855) B6407855
theorem B2847935 : Blo 1897435 2847935 := bstep (se 1 (by rfl) ⟨2135951, by rfl⟩ : syracuseStep 2847935 = 4271903) B4271903
theorem B1898623 : Blo 1897435 1898623 := bstep (se 1 (by rfl) ⟨1423967, by rfl⟩ : syracuseStep 1898623 = 2847935) B2847935
theorem B2847941 : Blo 1897435 2847941 := bbase (se 4 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 2847941 = 533989) (by norm_num)
theorem B1898627 : Blo 1897435 1898627 := bstep (se 1 (by rfl) ⟨1423970, by rfl⟩ : syracuseStep 1898627 = 2847941) B2847941
theorem B3203941 : Blo 1897435 3203941 := bbase (se 4 (by rfl) ⟨300369, by rfl⟩ : syracuseStep 3203941 = 600739) (by norm_num)
theorem B4271921 : Blo 1897435 4271921 := bstep (se 2 (by rfl) ⟨1601970, by rfl⟩ : syracuseStep 4271921 = 3203941) B3203941
theorem B2847947 : Blo 1897435 2847947 := bstep (se 1 (by rfl) ⟨2135960, by rfl⟩ : syracuseStep 2847947 = 4271921) B4271921
theorem B1898631 : Blo 1897435 1898631 := bstep (se 1 (by rfl) ⟨1423973, by rfl⟩ : syracuseStep 1898631 = 2847947) B2847947
theorem B2135965 : Blo 1897435 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B2847953 : Blo 1897435 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B1898635 : Blo 1897435 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B6407909 : Blo 1897435 6407909 := bbase (se 4 (by rfl) ⟨600741, by rfl⟩ : syracuseStep 6407909 = 1201483) (by norm_num)
theorem B4271939 : Blo 1897435 4271939 := bstep (se 1 (by rfl) ⟨3203954, by rfl⟩ : syracuseStep 4271939 = 6407909) B6407909
theorem B2847959 : Blo 1897435 2847959 := bstep (se 1 (by rfl) ⟨2135969, by rfl⟩ : syracuseStep 2847959 = 4271939) B4271939
theorem B1898639 : Blo 1897435 1898639 := bstep (se 1 (by rfl) ⟨1423979, by rfl⟩ : syracuseStep 1898639 = 2847959) B2847959
theorem B2847965 : Blo 1897435 2847965 := bbase (se 3 (by rfl) ⟨533993, by rfl⟩ : syracuseStep 2847965 = 1067987) (by norm_num)
theorem B1898643 : Blo 1897435 1898643 := bstep (se 1 (by rfl) ⟨1423982, by rfl⟩ : syracuseStep 1898643 = 2847965) B2847965
theorem B4271957 : Blo 1897435 4271957 := bbase (se 9 (by rfl) ⟨12515, by rfl⟩ : syracuseStep 4271957 = 25031) (by norm_num)
theorem B2847971 : Blo 1897435 2847971 := bstep (se 1 (by rfl) ⟨2135978, by rfl⟩ : syracuseStep 2847971 = 4271957) B4271957
theorem B1898647 : Blo 1897435 1898647 := bstep (se 1 (by rfl) ⟨1423985, by rfl⟩ : syracuseStep 1898647 = 2847971) B2847971
theorem B5406709 : Blo 1897435 5406709 := bbase (se 5 (by rfl) ⟨253439, by rfl⟩ : syracuseStep 5406709 = 506879) (by norm_num)
theorem B7208945 : Blo 1897435 7208945 := bstep (se 2 (by rfl) ⟨2703354, by rfl⟩ : syracuseStep 7208945 = 5406709) B5406709
theorem B4805963 : Blo 1897435 4805963 := bstep (se 1 (by rfl) ⟨3604472, by rfl⟩ : syracuseStep 4805963 = 7208945) B7208945
theorem B3203975 : Blo 1897435 3203975 := bstep (se 1 (by rfl) ⟨2402981, by rfl⟩ : syracuseStep 3203975 = 4805963) B4805963
theorem B2135983 : Blo 1897435 2135983 := bstep (se 1 (by rfl) ⟨1601987, by rfl⟩ : syracuseStep 2135983 = 3203975) B3203975
theorem B2847977 : Blo 1897435 2847977 := bstep (se 2 (by rfl) ⟨1067991, by rfl⟩ : syracuseStep 2847977 = 2135983) B2135983
theorem B1898651 : Blo 1897435 1898651 := bstep (se 1 (by rfl) ⟨1423988, by rfl⟩ : syracuseStep 1898651 = 2847977) B2847977
theorem B3515437 : Blo 1897435 3515437 := bbase (se 3 (by rfl) ⟨659144, by rfl⟩ : syracuseStep 3515437 = 1318289) (by norm_num)
theorem B4687249 : Blo 1897435 4687249 := bstep (se 2 (by rfl) ⟨1757718, by rfl⟩ : syracuseStep 4687249 = 3515437) B3515437
theorem B6249665 : Blo 1897435 6249665 := bstep (se 2 (by rfl) ⟨2343624, by rfl⟩ : syracuseStep 6249665 = 4687249) B4687249
theorem B4166443 : Blo 1897435 4166443 := bstep (se 1 (by rfl) ⟨3124832, by rfl⟩ : syracuseStep 4166443 = 6249665) B6249665
theorem B22221029 : Blo 1897435 22221029 := bstep (se 4 (by rfl) ⟨2083221, by rfl⟩ : syracuseStep 22221029 = 4166443) B4166443
theorem B14814019 : Blo 1897435 14814019 := bstep (se 1 (by rfl) ⟨11110514, by rfl⟩ : syracuseStep 14814019 = 22221029) B22221029
theorem B19752025 : Blo 1897435 19752025 := bstep (se 2 (by rfl) ⟨7407009, by rfl⟩ : syracuseStep 19752025 = 14814019) B14814019
theorem B1685506133 : Blo 1897435 1685506133 := bstep (se 8 (by rfl) ⟨9876012, by rfl⟩ : syracuseStep 1685506133 = 19752025) B19752025
theorem B1123670755 : Blo 1897435 1123670755 := bstep (se 1 (by rfl) ⟨842753066, by rfl⟩ : syracuseStep 1123670755 = 1685506133) B1685506133
theorem B1498227673 : Blo 1897435 1498227673 := bstep (se 2 (by rfl) ⟨561835377, by rfl⟩ : syracuseStep 1498227673 = 1123670755) B1123670755
theorem B1997636897 : Blo 1897435 1997636897 := bstep (se 2 (by rfl) ⟨749113836, by rfl⟩ : syracuseStep 1997636897 = 1498227673) B1498227673
theorem B1331757931 : Blo 1897435 1331757931 := bstep (se 1 (by rfl) ⟨998818448, by rfl⟩ : syracuseStep 1331757931 = 1997636897) B1997636897
theorem B1775677241 : Blo 1897435 1775677241 := bstep (se 2 (by rfl) ⟨665878965, by rfl⟩ : syracuseStep 1775677241 = 1331757931) B1331757931
theorem B4735139309 : Blo 1897435 4735139309 := bstep (se 3 (by rfl) ⟨887838620, by rfl⟩ : syracuseStep 4735139309 = 1775677241) B1775677241
theorem B3156759539 : Blo 1897435 3156759539 := bstep (se 1 (by rfl) ⟨2367569654, by rfl⟩ : syracuseStep 3156759539 = 4735139309) B4735139309
theorem B2104506359 : Blo 1897435 2104506359 := bstep (se 1 (by rfl) ⟨1578379769, by rfl⟩ : syracuseStep 2104506359 = 3156759539) B3156759539
theorem B1403004239 : Blo 1897435 1403004239 := bstep (se 1 (by rfl) ⟨1052253179, by rfl⟩ : syracuseStep 1403004239 = 2104506359) B2104506359
theorem B935336159 : Blo 1897435 935336159 := bstep (se 1 (by rfl) ⟨701502119, by rfl⟩ : syracuseStep 935336159 = 1403004239) B1403004239
theorem B623557439 : Blo 1897435 623557439 := bstep (se 1 (by rfl) ⟨467668079, by rfl⟩ : syracuseStep 623557439 = 935336159) B935336159
theorem B415704959 : Blo 1897435 415704959 := bstep (se 1 (by rfl) ⟨311778719, by rfl⟩ : syracuseStep 415704959 = 623557439) B623557439
theorem B277136639 : Blo 1897435 277136639 := bstep (se 1 (by rfl) ⟨207852479, by rfl⟩ : syracuseStep 277136639 = 415704959) B415704959
theorem B184757759 : Blo 1897435 184757759 := bstep (se 1 (by rfl) ⟨138568319, by rfl⟩ : syracuseStep 184757759 = 277136639) B277136639
theorem B123171839 : Blo 1897435 123171839 := bstep (se 1 (by rfl) ⟨92378879, by rfl⟩ : syracuseStep 123171839 = 184757759) B184757759
theorem B82114559 : Blo 1897435 82114559 := bstep (se 1 (by rfl) ⟨61585919, by rfl⟩ : syracuseStep 82114559 = 123171839) B123171839
theorem B54743039 : Blo 1897435 54743039 := bstep (se 1 (by rfl) ⟨41057279, by rfl⟩ : syracuseStep 54743039 = 82114559) B82114559
theorem B36495359 : Blo 1897435 36495359 := bstep (se 1 (by rfl) ⟨27371519, by rfl⟩ : syracuseStep 36495359 = 54743039) B54743039
theorem B24330239 : Blo 1897435 24330239 := bstep (se 1 (by rfl) ⟨18247679, by rfl⟩ : syracuseStep 24330239 = 36495359) B36495359
theorem B16220159 : Blo 1897435 16220159 := bstep (se 1 (by rfl) ⟨12165119, by rfl⟩ : syracuseStep 16220159 = 24330239) B24330239
theorem B10813439 : Blo 1897435 10813439 := bstep (se 1 (by rfl) ⟨8110079, by rfl⟩ : syracuseStep 10813439 = 16220159) B16220159
theorem B7208959 : Blo 1897435 7208959 := bstep (se 1 (by rfl) ⟨5406719, by rfl⟩ : syracuseStep 7208959 = 10813439) B10813439
theorem B9611945 : Blo 1897435 9611945 := bstep (se 2 (by rfl) ⟨3604479, by rfl⟩ : syracuseStep 9611945 = 7208959) B7208959
theorem B6407963 : Blo 1897435 6407963 := bstep (se 1 (by rfl) ⟨4805972, by rfl⟩ : syracuseStep 6407963 = 9611945) B9611945
theorem B4271975 : Blo 1897435 4271975 := bstep (se 1 (by rfl) ⟨3203981, by rfl⟩ : syracuseStep 4271975 = 6407963) B6407963
theorem B2847983 : Blo 1897435 2847983 := bstep (se 1 (by rfl) ⟨2135987, by rfl⟩ : syracuseStep 2847983 = 4271975) B4271975
theorem B1898655 : Blo 1897435 1898655 := bstep (se 1 (by rfl) ⟨1423991, by rfl⟩ : syracuseStep 1898655 = 2847983) B2847983
theorem B2847989 : Blo 1897435 2847989 := bbase (se 5 (by rfl) ⟨133499, by rfl⟩ : syracuseStep 2847989 = 266999) (by norm_num)
theorem B1898659 : Blo 1897435 1898659 := bstep (se 1 (by rfl) ⟨1423994, by rfl⟩ : syracuseStep 1898659 = 2847989) B2847989
theorem B12165173 : Blo 1897435 12165173 := bbase (se 5 (by rfl) ⟨570242, by rfl⟩ : syracuseStep 12165173 = 1140485) (by norm_num)
theorem B8110115 : Blo 1897435 8110115 := bstep (se 1 (by rfl) ⟨6082586, by rfl⟩ : syracuseStep 8110115 = 12165173) B12165173
theorem B5406743 : Blo 1897435 5406743 := bstep (se 1 (by rfl) ⟨4055057, by rfl⟩ : syracuseStep 5406743 = 8110115) B8110115
theorem B3604495 : Blo 1897435 3604495 := bstep (se 1 (by rfl) ⟨2703371, by rfl⟩ : syracuseStep 3604495 = 5406743) B5406743
theorem B4805993 : Blo 1897435 4805993 := bstep (se 2 (by rfl) ⟨1802247, by rfl⟩ : syracuseStep 4805993 = 3604495) B3604495
theorem B3203995 : Blo 1897435 3203995 := bstep (se 1 (by rfl) ⟨2402996, by rfl⟩ : syracuseStep 3203995 = 4805993) B4805993
theorem B4271993 : Blo 1897435 4271993 := bstep (se 2 (by rfl) ⟨1601997, by rfl⟩ : syracuseStep 4271993 = 3203995) B3203995
theorem B2847995 : Blo 1897435 2847995 := bstep (se 1 (by rfl) ⟨2135996, by rfl⟩ : syracuseStep 2847995 = 4271993) B4271993
theorem B1898663 : Blo 1897435 1898663 := bstep (se 1 (by rfl) ⟨1423997, by rfl⟩ : syracuseStep 1898663 = 2847995) B2847995
theorem B2136001 : Blo 1897435 2136001 := bbase (se 2 (by rfl) ⟨801000, by rfl⟩ : syracuseStep 2136001 = 1602001) (by norm_num)
theorem B2848001 : Blo 1897435 2848001 := bstep (se 2 (by rfl) ⟨1068000, by rfl⟩ : syracuseStep 2848001 = 2136001) B2136001
theorem B1898667 : Blo 1897435 1898667 := bstep (se 1 (by rfl) ⟨1424000, by rfl⟩ : syracuseStep 1898667 = 2848001) B2848001
theorem B4806013 : Blo 1897435 4806013 := bbase (se 3 (by rfl) ⟨901127, by rfl⟩ : syracuseStep 4806013 = 1802255) (by norm_num)
theorem B6408017 : Blo 1897435 6408017 := bstep (se 2 (by rfl) ⟨2403006, by rfl⟩ : syracuseStep 6408017 = 4806013) B4806013
theorem B4272011 : Blo 1897435 4272011 := bstep (se 1 (by rfl) ⟨3204008, by rfl⟩ : syracuseStep 4272011 = 6408017) B6408017
theorem B2848007 : Blo 1897435 2848007 := bstep (se 1 (by rfl) ⟨2136005, by rfl⟩ : syracuseStep 2848007 = 4272011) B4272011
theorem B1898671 : Blo 1897435 1898671 := bstep (se 1 (by rfl) ⟨1424003, by rfl⟩ : syracuseStep 1898671 = 2848007) B2848007
theorem B2848013 : Blo 1897435 2848013 := bbase (se 3 (by rfl) ⟨534002, by rfl⟩ : syracuseStep 2848013 = 1068005) (by norm_num)
theorem B1898675 : Blo 1897435 1898675 := bstep (se 1 (by rfl) ⟨1424006, by rfl⟩ : syracuseStep 1898675 = 2848013) B2848013
theorem B4272029 : Blo 1897435 4272029 := bbase (se 3 (by rfl) ⟨801005, by rfl⟩ : syracuseStep 4272029 = 1602011) (by norm_num)
theorem B2848019 : Blo 1897435 2848019 := bstep (se 1 (by rfl) ⟨2136014, by rfl⟩ : syracuseStep 2848019 = 4272029) B4272029
theorem B1898679 : Blo 1897435 1898679 := bstep (se 1 (by rfl) ⟨1424009, by rfl⟩ : syracuseStep 1898679 = 2848019) B2848019
theorem B3204029 : Blo 1897435 3204029 := bbase (se 3 (by rfl) ⟨600755, by rfl⟩ : syracuseStep 3204029 = 1201511) (by norm_num)
theorem B2136019 : Blo 1897435 2136019 := bstep (se 1 (by rfl) ⟨1602014, by rfl⟩ : syracuseStep 2136019 = 3204029) B3204029
theorem B2848025 : Blo 1897435 2848025 := bstep (se 2 (by rfl) ⟨1068009, by rfl⟩ : syracuseStep 2848025 = 2136019) B2136019
theorem B1898683 : Blo 1897435 1898683 := bstep (se 1 (by rfl) ⟨1424012, by rfl⟩ : syracuseStep 1898683 = 2848025) B2848025
theorem B10813621 : Blo 1897435 10813621 := bbase (se 5 (by rfl) ⟨506888, by rfl⟩ : syracuseStep 10813621 = 1013777) (by norm_num)
theorem B14418161 : Blo 1897435 14418161 := bstep (se 2 (by rfl) ⟨5406810, by rfl⟩ : syracuseStep 14418161 = 10813621) B10813621
theorem B9612107 : Blo 1897435 9612107 := bstep (se 1 (by rfl) ⟨7209080, by rfl⟩ : syracuseStep 9612107 = 14418161) B14418161
theorem B6408071 : Blo 1897435 6408071 := bstep (se 1 (by rfl) ⟨4806053, by rfl⟩ : syracuseStep 6408071 = 9612107) B9612107
theorem B4272047 : Blo 1897435 4272047 := bstep (se 1 (by rfl) ⟨3204035, by rfl⟩ : syracuseStep 4272047 = 6408071) B6408071
theorem B2848031 : Blo 1897435 2848031 := bstep (se 1 (by rfl) ⟨2136023, by rfl⟩ : syracuseStep 2848031 = 4272047) B4272047
theorem B1898687 : Blo 1897435 1898687 := bstep (se 1 (by rfl) ⟨1424015, by rfl⟩ : syracuseStep 1898687 = 2848031) B2848031
theorem B2848037 : Blo 1897435 2848037 := bbase (se 4 (by rfl) ⟨267003, by rfl⟩ : syracuseStep 2848037 = 534007) (by norm_num)
theorem B1898691 : Blo 1897435 1898691 := bstep (se 1 (by rfl) ⟨1424018, by rfl⟩ : syracuseStep 1898691 = 2848037) B2848037
theorem B2403037 : Blo 1897435 2403037 := bbase (se 3 (by rfl) ⟨450569, by rfl⟩ : syracuseStep 2403037 = 901139) (by norm_num)
theorem B3204049 : Blo 1897435 3204049 := bstep (se 2 (by rfl) ⟨1201518, by rfl⟩ : syracuseStep 3204049 = 2403037) B2403037
theorem B4272065 : Blo 1897435 4272065 := bstep (se 2 (by rfl) ⟨1602024, by rfl⟩ : syracuseStep 4272065 = 3204049) B3204049
theorem B2848043 : Blo 1897435 2848043 := bstep (se 1 (by rfl) ⟨2136032, by rfl⟩ : syracuseStep 2848043 = 4272065) B4272065
theorem B1898695 : Blo 1897435 1898695 := bstep (se 1 (by rfl) ⟨1424021, by rfl⟩ : syracuseStep 1898695 = 2848043) B2848043
theorem B2136037 : Blo 1897435 2136037 := bbase (se 4 (by rfl) ⟨200253, by rfl⟩ : syracuseStep 2136037 = 400507) (by norm_num)
theorem B2848049 : Blo 1897435 2848049 := bstep (se 2 (by rfl) ⟨1068018, by rfl⟩ : syracuseStep 2848049 = 2136037) B2136037
theorem B1898699 : Blo 1897435 1898699 := bstep (se 1 (by rfl) ⟨1424024, by rfl⟩ : syracuseStep 1898699 = 2848049) B2848049
theorem B6495557 : Blo 1897435 6495557 := bbase (se 4 (by rfl) ⟨608958, by rfl⟩ : syracuseStep 6495557 = 1217917) (by norm_num)
theorem B17321485 : Blo 1897435 17321485 := bstep (se 3 (by rfl) ⟨3247778, by rfl⟩ : syracuseStep 17321485 = 6495557) B6495557
theorem B23095313 : Blo 1897435 23095313 := bstep (se 2 (by rfl) ⟨8660742, by rfl⟩ : syracuseStep 23095313 = 17321485) B17321485
theorem B15396875 : Blo 1897435 15396875 := bstep (se 1 (by rfl) ⟨11547656, by rfl⟩ : syracuseStep 15396875 = 23095313) B23095313
theorem B10264583 : Blo 1897435 10264583 := bstep (se 1 (by rfl) ⟨7698437, by rfl⟩ : syracuseStep 10264583 = 15396875) B15396875
theorem B6843055 : Blo 1897435 6843055 := bstep (se 1 (by rfl) ⟨5132291, by rfl⟩ : syracuseStep 6843055 = 10264583) B10264583
theorem B9124073 : Blo 1897435 9124073 := bstep (se 2 (by rfl) ⟨3421527, by rfl⟩ : syracuseStep 9124073 = 6843055) B6843055
theorem B6082715 : Blo 1897435 6082715 := bstep (se 1 (by rfl) ⟨4562036, by rfl⟩ : syracuseStep 6082715 = 9124073) B9124073
theorem B4055143 : Blo 1897435 4055143 := bstep (se 1 (by rfl) ⟨3041357, by rfl⟩ : syracuseStep 4055143 = 6082715) B6082715
theorem B5406857 : Blo 1897435 5406857 := bstep (se 2 (by rfl) ⟨2027571, by rfl⟩ : syracuseStep 5406857 = 4055143) B4055143
theorem B3604571 : Blo 1897435 3604571 := bstep (se 1 (by rfl) ⟨2703428, by rfl⟩ : syracuseStep 3604571 = 5406857) B5406857
theorem B2403047 : Blo 1897435 2403047 := bstep (se 1 (by rfl) ⟨1802285, by rfl⟩ : syracuseStep 2403047 = 3604571) B3604571
theorem B6408125 : Blo 1897435 6408125 := bstep (se 3 (by rfl) ⟨1201523, by rfl⟩ : syracuseStep 6408125 = 2403047) B2403047
theorem B4272083 : Blo 1897435 4272083 := bstep (se 1 (by rfl) ⟨3204062, by rfl⟩ : syracuseStep 4272083 = 6408125) B6408125
theorem B2848055 : Blo 1897435 2848055 := bstep (se 1 (by rfl) ⟨2136041, by rfl⟩ : syracuseStep 2848055 = 4272083) B4272083
theorem B1898703 : Blo 1897435 1898703 := bstep (se 1 (by rfl) ⟨1424027, by rfl⟩ : syracuseStep 1898703 = 2848055) B2848055
theorem B2848061 : Blo 1897435 2848061 := bbase (se 3 (by rfl) ⟨534011, by rfl⟩ : syracuseStep 2848061 = 1068023) (by norm_num)
theorem B1898707 : Blo 1897435 1898707 := bstep (se 1 (by rfl) ⟨1424030, by rfl⟩ : syracuseStep 1898707 = 2848061) B2848061
theorem B4272101 : Blo 1897435 4272101 := bbase (se 4 (by rfl) ⟨400509, by rfl⟩ : syracuseStep 4272101 = 801019) (by norm_num)
theorem B2848067 : Blo 1897435 2848067 := bstep (se 1 (by rfl) ⟨2136050, by rfl⟩ : syracuseStep 2848067 = 4272101) B4272101
theorem B1898711 : Blo 1897435 1898711 := bstep (se 1 (by rfl) ⟨1424033, by rfl⟩ : syracuseStep 1898711 = 2848067) B2848067
theorem B4806125 : Blo 1897435 4806125 := bbase (se 3 (by rfl) ⟨901148, by rfl⟩ : syracuseStep 4806125 = 1802297) (by norm_num)
theorem B3204083 : Blo 1897435 3204083 := bstep (se 1 (by rfl) ⟨2403062, by rfl⟩ : syracuseStep 3204083 = 4806125) B4806125
theorem B2136055 : Blo 1897435 2136055 := bstep (se 1 (by rfl) ⟨1602041, by rfl⟩ : syracuseStep 2136055 = 3204083) B3204083
theorem B2848073 : Blo 1897435 2848073 := bstep (se 2 (by rfl) ⟨1068027, by rfl⟩ : syracuseStep 2848073 = 2136055) B2136055
theorem B1898715 : Blo 1897435 1898715 := bstep (se 1 (by rfl) ⟨1424036, by rfl⟩ : syracuseStep 1898715 = 2848073) B2848073
theorem B2777725 : Blo 1897435 2777725 := bbase (se 3 (by rfl) ⟨520823, by rfl⟩ : syracuseStep 2777725 = 1041647) (by norm_num)
theorem B14814533 : Blo 1897435 14814533 := bstep (se 4 (by rfl) ⟨1388862, by rfl⟩ : syracuseStep 14814533 = 2777725) B2777725
theorem B39505421 : Blo 1897435 39505421 := bstep (se 3 (by rfl) ⟨7407266, by rfl⟩ : syracuseStep 39505421 = 14814533) B14814533
theorem B26336947 : Blo 1897435 26336947 := bstep (se 1 (by rfl) ⟨19752710, by rfl⟩ : syracuseStep 26336947 = 39505421) B39505421
theorem B35115929 : Blo 1897435 35115929 := bstep (se 2 (by rfl) ⟨13168473, by rfl⟩ : syracuseStep 35115929 = 26336947) B26336947
theorem B23410619 : Blo 1897435 23410619 := bstep (se 1 (by rfl) ⟨17557964, by rfl⟩ : syracuseStep 23410619 = 35115929) B35115929
theorem B15607079 : Blo 1897435 15607079 := bstep (se 1 (by rfl) ⟨11705309, by rfl⟩ : syracuseStep 15607079 = 23410619) B23410619
theorem B10404719 : Blo 1897435 10404719 := bstep (se 1 (by rfl) ⟨7803539, by rfl⟩ : syracuseStep 10404719 = 15607079) B15607079
theorem B6936479 : Blo 1897435 6936479 := bstep (se 1 (by rfl) ⟨5202359, by rfl⟩ : syracuseStep 6936479 = 10404719) B10404719
theorem B4624319 : Blo 1897435 4624319 := bstep (se 1 (by rfl) ⟨3468239, by rfl⟩ : syracuseStep 4624319 = 6936479) B6936479
theorem B3082879 : Blo 1897435 3082879 := bstep (se 1 (by rfl) ⟨2312159, by rfl⟩ : syracuseStep 3082879 = 4624319) B4624319
theorem B16442021 : Blo 1897435 16442021 := bstep (se 4 (by rfl) ⟨1541439, by rfl⟩ : syracuseStep 16442021 = 3082879) B3082879
theorem B10961347 : Blo 1897435 10961347 := bstep (se 1 (by rfl) ⟨8221010, by rfl⟩ : syracuseStep 10961347 = 16442021) B16442021
theorem B14615129 : Blo 1897435 14615129 := bstep (se 2 (by rfl) ⟨5480673, by rfl⟩ : syracuseStep 14615129 = 10961347) B10961347
theorem B9743419 : Blo 1897435 9743419 := bstep (se 1 (by rfl) ⟨7307564, by rfl⟩ : syracuseStep 9743419 = 14615129) B14615129
theorem B12991225 : Blo 1897435 12991225 := bstep (se 2 (by rfl) ⟨4871709, by rfl⟩ : syracuseStep 12991225 = 9743419) B9743419
theorem B17321633 : Blo 1897435 17321633 := bstep (se 2 (by rfl) ⟨6495612, by rfl⟩ : syracuseStep 17321633 = 12991225) B12991225
theorem B11547755 : Blo 1897435 11547755 := bstep (se 1 (by rfl) ⟨8660816, by rfl⟩ : syracuseStep 11547755 = 17321633) B17321633
theorem B7698503 : Blo 1897435 7698503 := bstep (se 1 (by rfl) ⟨5773877, by rfl⟩ : syracuseStep 7698503 = 11547755) B11547755
theorem B5132335 : Blo 1897435 5132335 := bstep (se 1 (by rfl) ⟨3849251, by rfl⟩ : syracuseStep 5132335 = 7698503) B7698503
theorem B6843113 : Blo 1897435 6843113 := bstep (se 2 (by rfl) ⟨2566167, by rfl⟩ : syracuseStep 6843113 = 5132335) B5132335
theorem B4562075 : Blo 1897435 4562075 := bstep (se 1 (by rfl) ⟨3421556, by rfl⟩ : syracuseStep 4562075 = 6843113) B6843113
theorem B3041383 : Blo 1897435 3041383 := bstep (se 1 (by rfl) ⟨2281037, by rfl⟩ : syracuseStep 3041383 = 4562075) B4562075
theorem B4055177 : Blo 1897435 4055177 := bstep (se 2 (by rfl) ⟨1520691, by rfl⟩ : syracuseStep 4055177 = 3041383) B3041383
theorem B2703451 : Blo 1897435 2703451 := bstep (se 1 (by rfl) ⟨2027588, by rfl⟩ : syracuseStep 2703451 = 4055177) B4055177
theorem B3604601 : Blo 1897435 3604601 := bstep (se 2 (by rfl) ⟨1351725, by rfl⟩ : syracuseStep 3604601 = 2703451) B2703451
theorem B9612269 : Blo 1897435 9612269 := bstep (se 3 (by rfl) ⟨1802300, by rfl⟩ : syracuseStep 9612269 = 3604601) B3604601
theorem B6408179 : Blo 1897435 6408179 := bstep (se 1 (by rfl) ⟨4806134, by rfl⟩ : syracuseStep 6408179 = 9612269) B9612269
theorem B4272119 : Blo 1897435 4272119 := bstep (se 1 (by rfl) ⟨3204089, by rfl⟩ : syracuseStep 4272119 = 6408179) B6408179
theorem B2848079 : Blo 1897435 2848079 := bstep (se 1 (by rfl) ⟨2136059, by rfl⟩ : syracuseStep 2848079 = 4272119) B4272119
theorem B1898719 : Blo 1897435 1898719 := bstep (se 1 (by rfl) ⟨1424039, by rfl⟩ : syracuseStep 1898719 = 2848079) B2848079
theorem B2848085 : Blo 1897435 2848085 := bbase (se 13 (by rfl) ⟨521, by rfl⟩ : syracuseStep 2848085 = 1043) (by norm_num)
theorem B1898723 : Blo 1897435 1898723 := bstep (se 1 (by rfl) ⟨1424042, by rfl⟩ : syracuseStep 1898723 = 2848085) B2848085
theorem B2027597 : Blo 1897435 2027597 := bbase (se 3 (by rfl) ⟨380174, by rfl⟩ : syracuseStep 2027597 = 760349) (by norm_num)
theorem B5406925 : Blo 1897435 5406925 := bstep (se 3 (by rfl) ⟨1013798, by rfl⟩ : syracuseStep 5406925 = 2027597) B2027597
theorem B7209233 : Blo 1897435 7209233 := bstep (se 2 (by rfl) ⟨2703462, by rfl⟩ : syracuseStep 7209233 = 5406925) B5406925
theorem B4806155 : Blo 1897435 4806155 := bstep (se 1 (by rfl) ⟨3604616, by rfl⟩ : syracuseStep 4806155 = 7209233) B7209233
theorem B3204103 : Blo 1897435 3204103 := bstep (se 1 (by rfl) ⟨2403077, by rfl⟩ : syracuseStep 3204103 = 4806155) B4806155
theorem B4272137 : Blo 1897435 4272137 := bstep (se 2 (by rfl) ⟨1602051, by rfl⟩ : syracuseStep 4272137 = 3204103) B3204103
theorem B2848091 : Blo 1897435 2848091 := bstep (se 1 (by rfl) ⟨2136068, by rfl⟩ : syracuseStep 2848091 = 4272137) B4272137
theorem B1898727 : Blo 1897435 1898727 := bstep (se 1 (by rfl) ⟨1424045, by rfl⟩ : syracuseStep 1898727 = 2848091) B2848091
theorem B2136073 : Blo 1897435 2136073 := bbase (se 2 (by rfl) ⟨801027, by rfl⟩ : syracuseStep 2136073 = 1602055) (by norm_num)
theorem B2848097 : Blo 1897435 2848097 := bstep (se 2 (by rfl) ⟨1068036, by rfl⟩ : syracuseStep 2848097 = 2136073) B2136073
theorem B1898731 : Blo 1897435 1898731 := bstep (se 1 (by rfl) ⟨1424048, by rfl⟩ : syracuseStep 1898731 = 2848097) B2848097
theorem B7698565 : Blo 1897435 7698565 := bbase (se 4 (by rfl) ⟨721740, by rfl⟩ : syracuseStep 7698565 = 1443481) (by norm_num)
theorem B10264753 : Blo 1897435 10264753 := bstep (se 2 (by rfl) ⟨3849282, by rfl⟩ : syracuseStep 10264753 = 7698565) B7698565
theorem B13686337 : Blo 1897435 13686337 := bstep (se 2 (by rfl) ⟨5132376, by rfl⟩ : syracuseStep 13686337 = 10264753) B10264753
theorem B18248449 : Blo 1897435 18248449 := bstep (se 2 (by rfl) ⟨6843168, by rfl⟩ : syracuseStep 18248449 = 13686337) B13686337
theorem B24331265 : Blo 1897435 24331265 := bstep (se 2 (by rfl) ⟨9124224, by rfl⟩ : syracuseStep 24331265 = 18248449) B18248449
theorem B16220843 : Blo 1897435 16220843 := bstep (se 1 (by rfl) ⟨12165632, by rfl⟩ : syracuseStep 16220843 = 24331265) B24331265
theorem B10813895 : Blo 1897435 10813895 := bstep (se 1 (by rfl) ⟨8110421, by rfl⟩ : syracuseStep 10813895 = 16220843) B16220843
theorem B7209263 : Blo 1897435 7209263 := bstep (se 1 (by rfl) ⟨5406947, by rfl⟩ : syracuseStep 7209263 = 10813895) B10813895
theorem B4806175 : Blo 1897435 4806175 := bstep (se 1 (by rfl) ⟨3604631, by rfl⟩ : syracuseStep 4806175 = 7209263) B7209263
theorem B6408233 : Blo 1897435 6408233 := bstep (se 2 (by rfl) ⟨2403087, by rfl⟩ : syracuseStep 6408233 = 4806175) B4806175
theorem B4272155 : Blo 1897435 4272155 := bstep (se 1 (by rfl) ⟨3204116, by rfl⟩ : syracuseStep 4272155 = 6408233) B6408233
theorem B2848103 : Blo 1897435 2848103 := bstep (se 1 (by rfl) ⟨2136077, by rfl⟩ : syracuseStep 2848103 = 4272155) B4272155
theorem B1898735 : Blo 1897435 1898735 := bstep (se 1 (by rfl) ⟨1424051, by rfl⟩ : syracuseStep 1898735 = 2848103) B2848103
theorem B2848109 : Blo 1897435 2848109 := bbase (se 3 (by rfl) ⟨534020, by rfl⟩ : syracuseStep 2848109 = 1068041) (by norm_num)
theorem B1898739 : Blo 1897435 1898739 := bstep (se 1 (by rfl) ⟨1424054, by rfl⟩ : syracuseStep 1898739 = 2848109) B2848109
theorem B4272173 : Blo 1897435 4272173 := bbase (se 3 (by rfl) ⟨801032, by rfl⟩ : syracuseStep 4272173 = 1602065) (by norm_num)
theorem B2848115 : Blo 1897435 2848115 := bstep (se 1 (by rfl) ⟨2136086, by rfl⟩ : syracuseStep 2848115 = 4272173) B4272173
theorem B1898743 : Blo 1897435 1898743 := bstep (se 1 (by rfl) ⟨1424057, by rfl⟩ : syracuseStep 1898743 = 2848115) B2848115
theorem B3653837 : Blo 1897435 3653837 := bbase (se 3 (by rfl) ⟨685094, by rfl⟩ : syracuseStep 3653837 = 1370189) (by norm_num)
theorem B2435891 : Blo 1897435 2435891 := bstep (se 1 (by rfl) ⟨1826918, by rfl⟩ : syracuseStep 2435891 = 3653837) B3653837
theorem B6495709 : Blo 1897435 6495709 := bstep (se 3 (by rfl) ⟨1217945, by rfl⟩ : syracuseStep 6495709 = 2435891) B2435891
theorem B8660945 : Blo 1897435 8660945 := bstep (se 2 (by rfl) ⟨3247854, by rfl⟩ : syracuseStep 8660945 = 6495709) B6495709
theorem B5773963 : Blo 1897435 5773963 := bstep (se 1 (by rfl) ⟨4330472, by rfl⟩ : syracuseStep 5773963 = 8660945) B8660945
theorem B7698617 : Blo 1897435 7698617 := bstep (se 2 (by rfl) ⟨2886981, by rfl⟩ : syracuseStep 7698617 = 5773963) B5773963
theorem B5132411 : Blo 1897435 5132411 := bstep (se 1 (by rfl) ⟨3849308, by rfl⟩ : syracuseStep 5132411 = 7698617) B7698617
theorem B3421607 : Blo 1897435 3421607 := bstep (se 1 (by rfl) ⟨2566205, by rfl⟩ : syracuseStep 3421607 = 5132411) B5132411
theorem B9124285 : Blo 1897435 9124285 := bstep (se 3 (by rfl) ⟨1710803, by rfl⟩ : syracuseStep 9124285 = 3421607) B3421607
theorem B12165713 : Blo 1897435 12165713 := bstep (se 2 (by rfl) ⟨4562142, by rfl⟩ : syracuseStep 12165713 = 9124285) B9124285
theorem B8110475 : Blo 1897435 8110475 := bstep (se 1 (by rfl) ⟨6082856, by rfl⟩ : syracuseStep 8110475 = 12165713) B12165713
theorem B5406983 : Blo 1897435 5406983 := bstep (se 1 (by rfl) ⟨4055237, by rfl⟩ : syracuseStep 5406983 = 8110475) B8110475
theorem B3604655 : Blo 1897435 3604655 := bstep (se 1 (by rfl) ⟨2703491, by rfl⟩ : syracuseStep 3604655 = 5406983) B5406983
theorem B2403103 : Blo 1897435 2403103 := bstep (se 1 (by rfl) ⟨1802327, by rfl⟩ : syracuseStep 2403103 = 3604655) B3604655
theorem B3204137 : Blo 1897435 3204137 := bstep (se 2 (by rfl) ⟨1201551, by rfl⟩ : syracuseStep 3204137 = 2403103) B2403103
theorem B2136091 : Blo 1897435 2136091 := bstep (se 1 (by rfl) ⟨1602068, by rfl⟩ : syracuseStep 2136091 = 3204137) B3204137
theorem B2848121 : Blo 1897435 2848121 := bstep (se 2 (by rfl) ⟨1068045, by rfl⟩ : syracuseStep 2848121 = 2136091) B2136091
theorem B1898747 : Blo 1897435 1898747 := bstep (se 1 (by rfl) ⟨1424060, by rfl⟩ : syracuseStep 1898747 = 2848121) B2848121
theorem B3421613 : Blo 1897435 3421613 := bbase (se 3 (by rfl) ⟨641552, by rfl⟩ : syracuseStep 3421613 = 1283105) (by norm_num)
theorem B9124301 : Blo 1897435 9124301 := bstep (se 3 (by rfl) ⟨1710806, by rfl⟩ : syracuseStep 9124301 = 3421613) B3421613
theorem B6082867 : Blo 1897435 6082867 := bstep (se 1 (by rfl) ⟨4562150, by rfl⟩ : syracuseStep 6082867 = 9124301) B9124301
theorem B32441957 : Blo 1897435 32441957 := bstep (se 4 (by rfl) ⟨3041433, by rfl⟩ : syracuseStep 32441957 = 6082867) B6082867
theorem B21627971 : Blo 1897435 21627971 := bstep (se 1 (by rfl) ⟨16220978, by rfl⟩ : syracuseStep 21627971 = 32441957) B32441957
theorem B14418647 : Blo 1897435 14418647 := bstep (se 1 (by rfl) ⟨10813985, by rfl⟩ : syracuseStep 14418647 = 21627971) B21627971
theorem B9612431 : Blo 1897435 9612431 := bstep (se 1 (by rfl) ⟨7209323, by rfl⟩ : syracuseStep 9612431 = 14418647) B14418647
theorem B6408287 : Blo 1897435 6408287 := bstep (se 1 (by rfl) ⟨4806215, by rfl⟩ : syracuseStep 6408287 = 9612431) B9612431
theorem B4272191 : Blo 1897435 4272191 := bstep (se 1 (by rfl) ⟨3204143, by rfl⟩ : syracuseStep 4272191 = 6408287) B6408287
theorem B2848127 : Blo 1897435 2848127 := bstep (se 1 (by rfl) ⟨2136095, by rfl⟩ : syracuseStep 2848127 = 4272191) B4272191
theorem B1898751 : Blo 1897435 1898751 := bstep (se 1 (by rfl) ⟨1424063, by rfl⟩ : syracuseStep 1898751 = 2848127) B2848127
theorem B2848133 : Blo 1897435 2848133 := bbase (se 4 (by rfl) ⟨267012, by rfl⟩ : syracuseStep 2848133 = 534025) (by norm_num)
theorem B1898755 : Blo 1897435 1898755 := bstep (se 1 (by rfl) ⟨1424066, by rfl⟩ : syracuseStep 1898755 = 2848133) B2848133
theorem B3204157 : Blo 1897435 3204157 := bbase (se 3 (by rfl) ⟨600779, by rfl⟩ : syracuseStep 3204157 = 1201559) (by norm_num)
theorem B4272209 : Blo 1897435 4272209 := bstep (se 2 (by rfl) ⟨1602078, by rfl⟩ : syracuseStep 4272209 = 3204157) B3204157
theorem B2848139 : Blo 1897435 2848139 := bstep (se 1 (by rfl) ⟨2136104, by rfl⟩ : syracuseStep 2848139 = 4272209) B4272209
theorem B1898759 : Blo 1897435 1898759 := bstep (se 1 (by rfl) ⟨1424069, by rfl⟩ : syracuseStep 1898759 = 2848139) B2848139
theorem B2136109 : Blo 1897435 2136109 := bbase (se 3 (by rfl) ⟨400520, by rfl⟩ : syracuseStep 2136109 = 801041) (by norm_num)
theorem B2848145 : Blo 1897435 2848145 := bstep (se 2 (by rfl) ⟨1068054, by rfl⟩ : syracuseStep 2848145 = 2136109) B2136109
theorem B1898763 : Blo 1897435 1898763 := bstep (se 1 (by rfl) ⟨1424072, by rfl⟩ : syracuseStep 1898763 = 2848145) B2848145
theorem B6408341 : Blo 1897435 6408341 := bbase (se 6 (by rfl) ⟨150195, by rfl⟩ : syracuseStep 6408341 = 300391) (by norm_num)
theorem B4272227 : Blo 1897435 4272227 := bstep (se 1 (by rfl) ⟨3204170, by rfl⟩ : syracuseStep 4272227 = 6408341) B6408341
theorem B2848151 : Blo 1897435 2848151 := bstep (se 1 (by rfl) ⟨2136113, by rfl⟩ : syracuseStep 2848151 = 4272227) B4272227
theorem B1898767 : Blo 1897435 1898767 := bstep (se 1 (by rfl) ⟨1424075, by rfl⟩ : syracuseStep 1898767 = 2848151) B2848151
theorem B2848157 : Blo 1897435 2848157 := bbase (se 3 (by rfl) ⟨534029, by rfl⟩ : syracuseStep 2848157 = 1068059) (by norm_num)
theorem B1898771 : Blo 1897435 1898771 := bstep (se 1 (by rfl) ⟨1424078, by rfl⟩ : syracuseStep 1898771 = 2848157) B2848157
theorem B4272245 : Blo 1897435 4272245 := bbase (se 5 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 4272245 = 400523) (by norm_num)
theorem B2848163 : Blo 1897435 2848163 := bstep (se 1 (by rfl) ⟨2136122, by rfl⟩ : syracuseStep 2848163 = 4272245) B4272245
theorem B1898775 : Blo 1897435 1898775 := bstep (se 1 (by rfl) ⟨1424081, by rfl⟩ : syracuseStep 1898775 = 2848163) B2848163
theorem B3849373 : Blo 1897435 3849373 := bbase (se 3 (by rfl) ⟨721757, by rfl⟩ : syracuseStep 3849373 = 1443515) (by norm_num)
theorem B5132497 : Blo 1897435 5132497 := bstep (se 2 (by rfl) ⟨1924686, by rfl⟩ : syracuseStep 5132497 = 3849373) B3849373
theorem B6843329 : Blo 1897435 6843329 := bstep (se 2 (by rfl) ⟨2566248, by rfl⟩ : syracuseStep 6843329 = 5132497) B5132497
theorem B4562219 : Blo 1897435 4562219 := bstep (se 1 (by rfl) ⟨3421664, by rfl⟩ : syracuseStep 4562219 = 6843329) B6843329
theorem B3041479 : Blo 1897435 3041479 := bstep (se 1 (by rfl) ⟨2281109, by rfl⟩ : syracuseStep 3041479 = 4562219) B4562219
theorem B16221221 : Blo 1897435 16221221 := bstep (se 4 (by rfl) ⟨1520739, by rfl⟩ : syracuseStep 16221221 = 3041479) B3041479
theorem B10814147 : Blo 1897435 10814147 := bstep (se 1 (by rfl) ⟨8110610, by rfl⟩ : syracuseStep 10814147 = 16221221) B16221221
theorem B7209431 : Blo 1897435 7209431 := bstep (se 1 (by rfl) ⟨5407073, by rfl⟩ : syracuseStep 7209431 = 10814147) B10814147
theorem B4806287 : Blo 1897435 4806287 := bstep (se 1 (by rfl) ⟨3604715, by rfl⟩ : syracuseStep 4806287 = 7209431) B7209431
theorem B3204191 : Blo 1897435 3204191 := bstep (se 1 (by rfl) ⟨2403143, by rfl⟩ : syracuseStep 3204191 = 4806287) B4806287
theorem B2136127 : Blo 1897435 2136127 := bstep (se 1 (by rfl) ⟨1602095, by rfl⟩ : syracuseStep 2136127 = 3204191) B3204191
theorem B2848169 : Blo 1897435 2848169 := bstep (se 2 (by rfl) ⟨1068063, by rfl⟩ : syracuseStep 2848169 = 2136127) B2136127
theorem B1898779 : Blo 1897435 1898779 := bstep (se 1 (by rfl) ⟨1424084, by rfl⟩ : syracuseStep 1898779 = 2848169) B2848169
theorem B7209445 : Blo 1897435 7209445 := bbase (se 4 (by rfl) ⟨675885, by rfl⟩ : syracuseStep 7209445 = 1351771) (by norm_num)
theorem B9612593 : Blo 1897435 9612593 := bstep (se 2 (by rfl) ⟨3604722, by rfl⟩ : syracuseStep 9612593 = 7209445) B7209445
theorem B6408395 : Blo 1897435 6408395 := bstep (se 1 (by rfl) ⟨4806296, by rfl⟩ : syracuseStep 6408395 = 9612593) B9612593
theorem B4272263 : Blo 1897435 4272263 := bstep (se 1 (by rfl) ⟨3204197, by rfl⟩ : syracuseStep 4272263 = 6408395) B6408395
theorem B2848175 : Blo 1897435 2848175 := bstep (se 1 (by rfl) ⟨2136131, by rfl⟩ : syracuseStep 2848175 = 4272263) B4272263
theorem B1898783 : Blo 1897435 1898783 := bstep (se 1 (by rfl) ⟨1424087, by rfl⟩ : syracuseStep 1898783 = 2848175) B2848175
theorem B2848181 : Blo 1897435 2848181 := bbase (se 5 (by rfl) ⟨133508, by rfl⟩ : syracuseStep 2848181 = 267017) (by norm_num)
theorem B1898787 : Blo 1897435 1898787 := bstep (se 1 (by rfl) ⟨1424090, by rfl⟩ : syracuseStep 1898787 = 2848181) B2848181
theorem B4806317 : Blo 1897435 4806317 := bbase (se 3 (by rfl) ⟨901184, by rfl⟩ : syracuseStep 4806317 = 1802369) (by norm_num)
theorem B3204211 : Blo 1897435 3204211 := bstep (se 1 (by rfl) ⟨2403158, by rfl⟩ : syracuseStep 3204211 = 4806317) B4806317
theorem B4272281 : Blo 1897435 4272281 := bstep (se 2 (by rfl) ⟨1602105, by rfl⟩ : syracuseStep 4272281 = 3204211) B3204211
theorem B2848187 : Blo 1897435 2848187 := bstep (se 1 (by rfl) ⟨2136140, by rfl⟩ : syracuseStep 2848187 = 4272281) B4272281
theorem B1898791 : Blo 1897435 1898791 := bstep (se 1 (by rfl) ⟨1424093, by rfl⟩ : syracuseStep 1898791 = 2848187) B2848187
theorem B2136145 : Blo 1897435 2136145 := bbase (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) (by norm_num)
theorem B2848193 : Blo 1897435 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B1898795 : Blo 1897435 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B2703565 : Blo 1897435 2703565 := bbase (se 3 (by rfl) ⟨506918, by rfl⟩ : syracuseStep 2703565 = 1013837) (by norm_num)
theorem B3604753 : Blo 1897435 3604753 := bstep (se 2 (by rfl) ⟨1351782, by rfl⟩ : syracuseStep 3604753 = 2703565) B2703565
theorem B4806337 : Blo 1897435 4806337 := bstep (se 2 (by rfl) ⟨1802376, by rfl⟩ : syracuseStep 4806337 = 3604753) B3604753
theorem B6408449 : Blo 1897435 6408449 := bstep (se 2 (by rfl) ⟨2403168, by rfl⟩ : syracuseStep 6408449 = 4806337) B4806337
theorem B4272299 : Blo 1897435 4272299 := bstep (se 1 (by rfl) ⟨3204224, by rfl⟩ : syracuseStep 4272299 = 6408449) B6408449
theorem B2848199 : Blo 1897435 2848199 := bstep (se 1 (by rfl) ⟨2136149, by rfl⟩ : syracuseStep 2848199 = 4272299) B4272299
theorem B1898799 : Blo 1897435 1898799 := bstep (se 1 (by rfl) ⟨1424099, by rfl⟩ : syracuseStep 1898799 = 2848199) B2848199
theorem B2848205 : Blo 1897435 2848205 := bbase (se 3 (by rfl) ⟨534038, by rfl⟩ : syracuseStep 2848205 = 1068077) (by norm_num)
theorem B1898803 : Blo 1897435 1898803 := bstep (se 1 (by rfl) ⟨1424102, by rfl⟩ : syracuseStep 1898803 = 2848205) B2848205
theorem B4272317 : Blo 1897435 4272317 := bbase (se 3 (by rfl) ⟨801059, by rfl⟩ : syracuseStep 4272317 = 1602119) (by norm_num)
theorem B2848211 : Blo 1897435 2848211 := bstep (se 1 (by rfl) ⟨2136158, by rfl⟩ : syracuseStep 2848211 = 4272317) B4272317
theorem B1898807 : Blo 1897435 1898807 := bstep (se 1 (by rfl) ⟨1424105, by rfl⟩ : syracuseStep 1898807 = 2848211) B2848211
theorem B3204245 : Blo 1897435 3204245 := bbase (se 6 (by rfl) ⟨75099, by rfl⟩ : syracuseStep 3204245 = 150199) (by norm_num)
theorem B2136163 : Blo 1897435 2136163 := bstep (se 1 (by rfl) ⟨1602122, by rfl⟩ : syracuseStep 2136163 = 3204245) B3204245
theorem B2848217 : Blo 1897435 2848217 := bstep (se 2 (by rfl) ⟨1068081, by rfl⟩ : syracuseStep 2848217 = 2136163) B2136163
theorem B1898811 : Blo 1897435 1898811 := bstep (se 1 (by rfl) ⟨1424108, by rfl⟩ : syracuseStep 1898811 = 2848217) B2848217
theorem B3849445 : Blo 1897435 3849445 := bbase (se 4 (by rfl) ⟨360885, by rfl⟩ : syracuseStep 3849445 = 721771) (by norm_num)
theorem B5132593 : Blo 1897435 5132593 := bstep (se 2 (by rfl) ⟨1924722, by rfl⟩ : syracuseStep 5132593 = 3849445) B3849445
theorem B6843457 : Blo 1897435 6843457 := bstep (se 2 (by rfl) ⟨2566296, by rfl⟩ : syracuseStep 6843457 = 5132593) B5132593
theorem B9124609 : Blo 1897435 9124609 := bstep (se 2 (by rfl) ⟨3421728, by rfl⟩ : syracuseStep 9124609 = 6843457) B6843457
theorem B12166145 : Blo 1897435 12166145 := bstep (se 2 (by rfl) ⟨4562304, by rfl⟩ : syracuseStep 12166145 = 9124609) B9124609
theorem B8110763 : Blo 1897435 8110763 := bstep (se 1 (by rfl) ⟨6083072, by rfl⟩ : syracuseStep 8110763 = 12166145) B12166145
theorem B5407175 : Blo 1897435 5407175 := bstep (se 1 (by rfl) ⟨4055381, by rfl⟩ : syracuseStep 5407175 = 8110763) B8110763
theorem B14419133 : Blo 1897435 14419133 := bstep (se 3 (by rfl) ⟨2703587, by rfl⟩ : syracuseStep 14419133 = 5407175) B5407175
theorem B9612755 : Blo 1897435 9612755 := bstep (se 1 (by rfl) ⟨7209566, by rfl⟩ : syracuseStep 9612755 = 14419133) B14419133
theorem B6408503 : Blo 1897435 6408503 := bstep (se 1 (by rfl) ⟨4806377, by rfl⟩ : syracuseStep 6408503 = 9612755) B9612755
theorem B4272335 : Blo 1897435 4272335 := bstep (se 1 (by rfl) ⟨3204251, by rfl⟩ : syracuseStep 4272335 = 6408503) B6408503
theorem B2848223 : Blo 1897435 2848223 := bstep (se 1 (by rfl) ⟨2136167, by rfl⟩ : syracuseStep 2848223 = 4272335) B4272335
theorem B1898815 : Blo 1897435 1898815 := bstep (se 1 (by rfl) ⟨1424111, by rfl⟩ : syracuseStep 1898815 = 2848223) B2848223
theorem B2848229 : Blo 1897435 2848229 := bbase (se 4 (by rfl) ⟨267021, by rfl⟩ : syracuseStep 2848229 = 534043) (by norm_num)
theorem B1898819 : Blo 1897435 1898819 := bstep (se 1 (by rfl) ⟨1424114, by rfl⟩ : syracuseStep 1898819 = 2848229) B2848229
theorem B6584597 : Blo 1897435 6584597 := bbase (se 6 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 6584597 = 308653) (by norm_num)
theorem B4389731 : Blo 1897435 4389731 := bstep (se 1 (by rfl) ⟨3292298, by rfl⟩ : syracuseStep 4389731 = 6584597) B6584597
theorem B2926487 : Blo 1897435 2926487 := bstep (se 1 (by rfl) ⟨2194865, by rfl⟩ : syracuseStep 2926487 = 4389731) B4389731
theorem B7803965 : Blo 1897435 7803965 := bstep (se 3 (by rfl) ⟨1463243, by rfl⟩ : syracuseStep 7803965 = 2926487) B2926487
theorem B5202643 : Blo 1897435 5202643 := bstep (se 1 (by rfl) ⟨3901982, by rfl⟩ : syracuseStep 5202643 = 7803965) B7803965
theorem B6936857 : Blo 1897435 6936857 := bstep (se 2 (by rfl) ⟨2601321, by rfl⟩ : syracuseStep 6936857 = 5202643) B5202643
theorem B4624571 : Blo 1897435 4624571 := bstep (se 1 (by rfl) ⟨3468428, by rfl⟩ : syracuseStep 4624571 = 6936857) B6936857
theorem B12332189 : Blo 1897435 12332189 := bstep (se 3 (by rfl) ⟨2312285, by rfl⟩ : syracuseStep 12332189 = 4624571) B4624571
theorem B32885837 : Blo 1897435 32885837 := bstep (se 3 (by rfl) ⟨6166094, by rfl⟩ : syracuseStep 32885837 = 12332189) B12332189
theorem B21923891 : Blo 1897435 21923891 := bstep (se 1 (by rfl) ⟨16442918, by rfl⟩ : syracuseStep 21923891 = 32885837) B32885837
theorem B14615927 : Blo 1897435 14615927 := bstep (se 1 (by rfl) ⟨10961945, by rfl⟩ : syracuseStep 14615927 = 21923891) B21923891
theorem B9743951 : Blo 1897435 9743951 := bstep (se 1 (by rfl) ⟨7307963, by rfl⟩ : syracuseStep 9743951 = 14615927) B14615927
theorem B6495967 : Blo 1897435 6495967 := bstep (se 1 (by rfl) ⟨4871975, by rfl⟩ : syracuseStep 6495967 = 9743951) B9743951
theorem B34645157 : Blo 1897435 34645157 := bstep (se 4 (by rfl) ⟨3247983, by rfl⟩ : syracuseStep 34645157 = 6495967) B6495967
theorem B23096771 : Blo 1897435 23096771 := bstep (se 1 (by rfl) ⟨17322578, by rfl⟩ : syracuseStep 23096771 = 34645157) B34645157
theorem B15397847 : Blo 1897435 15397847 := bstep (se 1 (by rfl) ⟨11548385, by rfl⟩ : syracuseStep 15397847 = 23096771) B23096771
theorem B10265231 : Blo 1897435 10265231 := bstep (se 1 (by rfl) ⟨7698923, by rfl⟩ : syracuseStep 10265231 = 15397847) B15397847
theorem B27373949 : Blo 1897435 27373949 := bstep (se 3 (by rfl) ⟨5132615, by rfl⟩ : syracuseStep 27373949 = 10265231) B10265231
theorem B18249299 : Blo 1897435 18249299 := bstep (se 1 (by rfl) ⟨13686974, by rfl⟩ : syracuseStep 18249299 = 27373949) B27373949
theorem B12166199 : Blo 1897435 12166199 := bstep (se 1 (by rfl) ⟨9124649, by rfl⟩ : syracuseStep 12166199 = 18249299) B18249299
theorem B8110799 : Blo 1897435 8110799 := bstep (se 1 (by rfl) ⟨6083099, by rfl⟩ : syracuseStep 8110799 = 12166199) B12166199
theorem B5407199 : Blo 1897435 5407199 := bstep (se 1 (by rfl) ⟨4055399, by rfl⟩ : syracuseStep 5407199 = 8110799) B8110799
theorem B3604799 : Blo 1897435 3604799 := bstep (se 1 (by rfl) ⟨2703599, by rfl⟩ : syracuseStep 3604799 = 5407199) B5407199
theorem B2403199 : Blo 1897435 2403199 := bstep (se 1 (by rfl) ⟨1802399, by rfl⟩ : syracuseStep 2403199 = 3604799) B3604799
theorem B3204265 : Blo 1897435 3204265 := bstep (se 2 (by rfl) ⟨1201599, by rfl⟩ : syracuseStep 3204265 = 2403199) B2403199
theorem B4272353 : Blo 1897435 4272353 := bstep (se 2 (by rfl) ⟨1602132, by rfl⟩ : syracuseStep 4272353 = 3204265) B3204265
theorem B2848235 : Blo 1897435 2848235 := bstep (se 1 (by rfl) ⟨2136176, by rfl⟩ : syracuseStep 2848235 = 4272353) B4272353
theorem B1898823 : Blo 1897435 1898823 := bstep (se 1 (by rfl) ⟨1424117, by rfl⟩ : syracuseStep 1898823 = 2848235) B2848235
theorem B2136181 : Blo 1897435 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B2848241 : Blo 1897435 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B1898827 : Blo 1897435 1898827 := bstep (se 1 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 1898827 = 2848241) B2848241
theorem B2403209 : Blo 1897435 2403209 := bbase (se 2 (by rfl) ⟨901203, by rfl⟩ : syracuseStep 2403209 = 1802407) (by norm_num)
theorem B6408557 : Blo 1897435 6408557 := bstep (se 3 (by rfl) ⟨1201604, by rfl⟩ : syracuseStep 6408557 = 2403209) B2403209
theorem B4272371 : Blo 1897435 4272371 := bstep (se 1 (by rfl) ⟨3204278, by rfl⟩ : syracuseStep 4272371 = 6408557) B6408557
theorem B2848247 : Blo 1897435 2848247 := bstep (se 1 (by rfl) ⟨2136185, by rfl⟩ : syracuseStep 2848247 = 4272371) B4272371
theorem B1898831 : Blo 1897435 1898831 := bstep (se 1 (by rfl) ⟨1424123, by rfl⟩ : syracuseStep 1898831 = 2848247) B2848247
theorem B2848253 : Blo 1897435 2848253 := bbase (se 3 (by rfl) ⟨534047, by rfl⟩ : syracuseStep 2848253 = 1068095) (by norm_num)
theorem B1898835 : Blo 1897435 1898835 := bstep (se 1 (by rfl) ⟨1424126, by rfl⟩ : syracuseStep 1898835 = 2848253) B2848253
theorem B4272389 : Blo 1897435 4272389 := bbase (se 4 (by rfl) ⟨400536, by rfl⟩ : syracuseStep 4272389 = 801073) (by norm_num)
theorem B2848259 : Blo 1897435 2848259 := bstep (se 1 (by rfl) ⟨2136194, by rfl⟩ : syracuseStep 2848259 = 4272389) B4272389
theorem B1898839 : Blo 1897435 1898839 := bstep (se 1 (by rfl) ⟨1424129, by rfl⟩ : syracuseStep 1898839 = 2848259) B2848259
theorem B3604837 : Blo 1897435 3604837 := bbase (se 4 (by rfl) ⟨337953, by rfl⟩ : syracuseStep 3604837 = 675907) (by norm_num)
theorem B4806449 : Blo 1897435 4806449 := bstep (se 2 (by rfl) ⟨1802418, by rfl⟩ : syracuseStep 4806449 = 3604837) B3604837
theorem B3204299 : Blo 1897435 3204299 := bstep (se 1 (by rfl) ⟨2403224, by rfl⟩ : syracuseStep 3204299 = 4806449) B4806449
theorem B2136199 : Blo 1897435 2136199 := bstep (se 1 (by rfl) ⟨1602149, by rfl⟩ : syracuseStep 2136199 = 3204299) B3204299
theorem B2848265 : Blo 1897435 2848265 := bstep (se 2 (by rfl) ⟨1068099, by rfl⟩ : syracuseStep 2848265 = 2136199) B2136199
theorem B1898843 : Blo 1897435 1898843 := bstep (se 1 (by rfl) ⟨1424132, by rfl⟩ : syracuseStep 1898843 = 2848265) B2848265
theorem B9612917 : Blo 1897435 9612917 := bbase (se 5 (by rfl) ⟨450605, by rfl⟩ : syracuseStep 9612917 = 901211) (by norm_num)
theorem B6408611 : Blo 1897435 6408611 := bstep (se 1 (by rfl) ⟨4806458, by rfl⟩ : syracuseStep 6408611 = 9612917) B9612917
theorem B4272407 : Blo 1897435 4272407 := bstep (se 1 (by rfl) ⟨3204305, by rfl⟩ : syracuseStep 4272407 = 6408611) B6408611
theorem B2848271 : Blo 1897435 2848271 := bstep (se 1 (by rfl) ⟨2136203, by rfl⟩ : syracuseStep 2848271 = 4272407) B4272407
theorem B1898847 : Blo 1897435 1898847 := bstep (se 1 (by rfl) ⟨1424135, by rfl⟩ : syracuseStep 1898847 = 2848271) B2848271
theorem B2848277 : Blo 1897435 2848277 := bbase (se 6 (by rfl) ⟨66756, by rfl⟩ : syracuseStep 2848277 = 133513) (by norm_num)
theorem B1898851 : Blo 1897435 1898851 := bstep (se 1 (by rfl) ⟨1424138, by rfl⟩ : syracuseStep 1898851 = 2848277) B2848277
theorem B1951025 : Blo 1897435 1951025 := bbase (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) (by norm_num)
theorem B5202733 : Blo 1897435 5202733 := bstep (se 3 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 5202733 = 1951025) B1951025
theorem B6936977 : Blo 1897435 6936977 := bstep (se 2 (by rfl) ⟨2601366, by rfl⟩ : syracuseStep 6936977 = 5202733) B5202733
theorem B4624651 : Blo 1897435 4624651 := bstep (se 1 (by rfl) ⟨3468488, by rfl⟩ : syracuseStep 4624651 = 6936977) B6936977
theorem B6166201 : Blo 1897435 6166201 := bstep (se 2 (by rfl) ⟨2312325, by rfl⟩ : syracuseStep 6166201 = 4624651) B4624651
theorem B8221601 : Blo 1897435 8221601 := bstep (se 2 (by rfl) ⟨3083100, by rfl⟩ : syracuseStep 8221601 = 6166201) B6166201
theorem B5481067 : Blo 1897435 5481067 := bstep (se 1 (by rfl) ⟨4110800, by rfl⟩ : syracuseStep 5481067 = 8221601) B8221601
theorem B7308089 : Blo 1897435 7308089 := bstep (se 2 (by rfl) ⟨2740533, by rfl⟩ : syracuseStep 7308089 = 5481067) B5481067
theorem B4872059 : Blo 1897435 4872059 := bstep (se 1 (by rfl) ⟨3654044, by rfl⟩ : syracuseStep 4872059 = 7308089) B7308089
theorem B3248039 : Blo 1897435 3248039 := bstep (se 1 (by rfl) ⟨2436029, by rfl⟩ : syracuseStep 3248039 = 4872059) B4872059
theorem B8661437 : Blo 1897435 8661437 := bstep (se 3 (by rfl) ⟨1624019, by rfl⟩ : syracuseStep 8661437 = 3248039) B3248039
theorem B5774291 : Blo 1897435 5774291 := bstep (se 1 (by rfl) ⟨4330718, by rfl⟩ : syracuseStep 5774291 = 8661437) B8661437
theorem B3849527 : Blo 1897435 3849527 := bstep (se 1 (by rfl) ⟨2887145, by rfl⟩ : syracuseStep 3849527 = 5774291) B5774291
theorem B2566351 : Blo 1897435 2566351 := bstep (se 1 (by rfl) ⟨1924763, by rfl⟩ : syracuseStep 2566351 = 3849527) B3849527
theorem B3421801 : Blo 1897435 3421801 := bstep (se 2 (by rfl) ⟨1283175, by rfl⟩ : syracuseStep 3421801 = 2566351) B2566351
theorem B4562401 : Blo 1897435 4562401 := bstep (se 2 (by rfl) ⟨1710900, by rfl⟩ : syracuseStep 4562401 = 3421801) B3421801
theorem B6083201 : Blo 1897435 6083201 := bstep (se 2 (by rfl) ⟨2281200, by rfl⟩ : syracuseStep 6083201 = 4562401) B4562401
theorem B16221869 : Blo 1897435 16221869 := bstep (se 3 (by rfl) ⟨3041600, by rfl⟩ : syracuseStep 16221869 = 6083201) B6083201
theorem B10814579 : Blo 1897435 10814579 := bstep (se 1 (by rfl) ⟨8110934, by rfl⟩ : syracuseStep 10814579 = 16221869) B16221869
theorem B7209719 : Blo 1897435 7209719 := bstep (se 1 (by rfl) ⟨5407289, by rfl⟩ : syracuseStep 7209719 = 10814579) B10814579
theorem B4806479 : Blo 1897435 4806479 := bstep (se 1 (by rfl) ⟨3604859, by rfl⟩ : syracuseStep 4806479 = 7209719) B7209719
theorem B3204319 : Blo 1897435 3204319 := bstep (se 1 (by rfl) ⟨2403239, by rfl⟩ : syracuseStep 3204319 = 4806479) B4806479
theorem B4272425 : Blo 1897435 4272425 := bstep (se 2 (by rfl) ⟨1602159, by rfl⟩ : syracuseStep 4272425 = 3204319) B3204319
theorem B2848283 : Blo 1897435 2848283 := bstep (se 1 (by rfl) ⟨2136212, by rfl⟩ : syracuseStep 2848283 = 4272425) B4272425
theorem B1898855 : Blo 1897435 1898855 := bstep (se 1 (by rfl) ⟨1424141, by rfl⟩ : syracuseStep 1898855 = 2848283) B2848283
theorem B2136217 : Blo 1897435 2136217 := bbase (se 2 (by rfl) ⟨801081, by rfl⟩ : syracuseStep 2136217 = 1602163) (by norm_num)
theorem B2848289 : Blo 1897435 2848289 := bstep (se 2 (by rfl) ⟨1068108, by rfl⟩ : syracuseStep 2848289 = 2136217) B2136217
theorem B1898859 : Blo 1897435 1898859 := bstep (se 1 (by rfl) ⟨1424144, by rfl⟩ : syracuseStep 1898859 = 2848289) B2848289
theorem B7209749 : Blo 1897435 7209749 := bbase (se 6 (by rfl) ⟨168978, by rfl⟩ : syracuseStep 7209749 = 337957) (by norm_num)
theorem B4806499 : Blo 1897435 4806499 := bstep (se 1 (by rfl) ⟨3604874, by rfl⟩ : syracuseStep 4806499 = 7209749) B7209749
theorem B6408665 : Blo 1897435 6408665 := bstep (se 2 (by rfl) ⟨2403249, by rfl⟩ : syracuseStep 6408665 = 4806499) B4806499
theorem B4272443 : Blo 1897435 4272443 := bstep (se 1 (by rfl) ⟨3204332, by rfl⟩ : syracuseStep 4272443 = 6408665) B6408665
theorem B2848295 : Blo 1897435 2848295 := bstep (se 1 (by rfl) ⟨2136221, by rfl⟩ : syracuseStep 2848295 = 4272443) B4272443
theorem B1898863 : Blo 1897435 1898863 := bstep (se 1 (by rfl) ⟨1424147, by rfl⟩ : syracuseStep 1898863 = 2848295) B2848295
theorem B2848301 : Blo 1897435 2848301 := bbase (se 3 (by rfl) ⟨534056, by rfl⟩ : syracuseStep 2848301 = 1068113) (by norm_num)
theorem B1898867 : Blo 1897435 1898867 := bstep (se 1 (by rfl) ⟨1424150, by rfl⟩ : syracuseStep 1898867 = 2848301) B2848301
theorem B4272461 : Blo 1897435 4272461 := bbase (se 3 (by rfl) ⟨801086, by rfl⟩ : syracuseStep 4272461 = 1602173) (by norm_num)
theorem B2848307 : Blo 1897435 2848307 := bstep (se 1 (by rfl) ⟨2136230, by rfl⟩ : syracuseStep 2848307 = 4272461) B4272461
theorem B1898871 : Blo 1897435 1898871 := bstep (se 1 (by rfl) ⟨1424153, by rfl⟩ : syracuseStep 1898871 = 2848307) B2848307
theorem B2403265 : Blo 1897435 2403265 := bbase (se 2 (by rfl) ⟨901224, by rfl⟩ : syracuseStep 2403265 = 1802449) (by norm_num)
theorem B3204353 : Blo 1897435 3204353 := bstep (se 2 (by rfl) ⟨1201632, by rfl⟩ : syracuseStep 3204353 = 2403265) B2403265
theorem B2136235 : Blo 1897435 2136235 := bstep (se 1 (by rfl) ⟨1602176, by rfl⟩ : syracuseStep 2136235 = 3204353) B3204353
theorem B2848313 : Blo 1897435 2848313 := bstep (se 2 (by rfl) ⟨1068117, by rfl⟩ : syracuseStep 2848313 = 2136235) B2136235
theorem B1898875 : Blo 1897435 1898875 := bstep (se 1 (by rfl) ⟨1424156, by rfl⟩ : syracuseStep 1898875 = 2848313) B2848313
theorem B2926573 : Blo 1897435 2926573 := bbase (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) (by norm_num)
theorem B15608389 : Blo 1897435 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B20811185 : Blo 1897435 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B13874123 : Blo 1897435 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B36997661 : Blo 1897435 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B24665107 : Blo 1897435 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B32886809 : Blo 1897435 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B21924539 : Blo 1897435 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B14616359 : Blo 1897435 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B9744239 : Blo 1897435 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B25984637 : Blo 1897435 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B17323091 : Blo 1897435 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B11548727 : Blo 1897435 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B7699151 : Blo 1897435 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B5132767 : Blo 1897435 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B6843689 : Blo 1897435 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B4562459 : Blo 1897435 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B3041639 : Blo 1897435 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B2027759 : Blo 1897435 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B21629429 : Blo 1897435 21629429 := bstep (se 5 (by rfl) ⟨1013879, by rfl⟩ : syracuseStep 21629429 = 2027759) B2027759
theorem B14419619 : Blo 1897435 14419619 := bstep (se 1 (by rfl) ⟨10814714, by rfl⟩ : syracuseStep 14419619 = 21629429) B21629429
theorem B9613079 : Blo 1897435 9613079 := bstep (se 1 (by rfl) ⟨7209809, by rfl⟩ : syracuseStep 9613079 = 14419619) B14419619
theorem B6408719 : Blo 1897435 6408719 := bstep (se 1 (by rfl) ⟨4806539, by rfl⟩ : syracuseStep 6408719 = 9613079) B9613079
theorem B4272479 : Blo 1897435 4272479 := bstep (se 1 (by rfl) ⟨3204359, by rfl⟩ : syracuseStep 4272479 = 6408719) B6408719
theorem B2848319 : Blo 1897435 2848319 := bstep (se 1 (by rfl) ⟨2136239, by rfl⟩ : syracuseStep 2848319 = 4272479) B4272479
theorem B1898879 : Blo 1897435 1898879 := bstep (se 1 (by rfl) ⟨1424159, by rfl⟩ : syracuseStep 1898879 = 2848319) B2848319
theorem B2848325 : Blo 1897435 2848325 := bbase (se 4 (by rfl) ⟨267030, by rfl⟩ : syracuseStep 2848325 = 534061) (by norm_num)
theorem B1898883 : Blo 1897435 1898883 := bstep (se 1 (by rfl) ⟨1424162, by rfl⟩ : syracuseStep 1898883 = 2848325) B2848325
theorem B3204373 : Blo 1897435 3204373 := bbase (se 6 (by rfl) ⟨75102, by rfl⟩ : syracuseStep 3204373 = 150205) (by norm_num)
theorem B4272497 : Blo 1897435 4272497 := bstep (se 2 (by rfl) ⟨1602186, by rfl⟩ : syracuseStep 4272497 = 3204373) B3204373
theorem B2848331 : Blo 1897435 2848331 := bstep (se 1 (by rfl) ⟨2136248, by rfl⟩ : syracuseStep 2848331 = 4272497) B4272497
theorem B1898887 : Blo 1897435 1898887 := bstep (se 1 (by rfl) ⟨1424165, by rfl⟩ : syracuseStep 1898887 = 2848331) B2848331
theorem B2136253 : Blo 1897435 2136253 := bbase (se 3 (by rfl) ⟨400547, by rfl⟩ : syracuseStep 2136253 = 801095) (by norm_num)
theorem B2848337 : Blo 1897435 2848337 := bstep (se 2 (by rfl) ⟨1068126, by rfl⟩ : syracuseStep 2848337 = 2136253) B2136253
theorem B1898891 : Blo 1897435 1898891 := bstep (se 1 (by rfl) ⟨1424168, by rfl⟩ : syracuseStep 1898891 = 2848337) B2848337
theorem B6408773 : Blo 1897435 6408773 := bbase (se 4 (by rfl) ⟨600822, by rfl⟩ : syracuseStep 6408773 = 1201645) (by norm_num)
theorem B4272515 : Blo 1897435 4272515 := bstep (se 1 (by rfl) ⟨3204386, by rfl⟩ : syracuseStep 4272515 = 6408773) B6408773
theorem B2848343 : Blo 1897435 2848343 := bstep (se 1 (by rfl) ⟨2136257, by rfl⟩ : syracuseStep 2848343 = 4272515) B4272515
theorem B1898895 : Blo 1897435 1898895 := bstep (se 1 (by rfl) ⟨1424171, by rfl⟩ : syracuseStep 1898895 = 2848343) B2848343
theorem B2848349 : Blo 1897435 2848349 := bbase (se 3 (by rfl) ⟨534065, by rfl⟩ : syracuseStep 2848349 = 1068131) (by norm_num)
theorem B1898899 : Blo 1897435 1898899 := bstep (se 1 (by rfl) ⟨1424174, by rfl⟩ : syracuseStep 1898899 = 2848349) B2848349
theorem B4272533 : Blo 1897435 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B2848355 : Blo 1897435 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B1898903 : Blo 1897435 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B4330837 : Blo 1897435 4330837 := bbase (se 14 (by rfl) ⟨396, by rfl⟩ : syracuseStep 4330837 = 793) (by norm_num)
theorem B23097797 : Blo 1897435 23097797 := bstep (se 4 (by rfl) ⟨2165418, by rfl⟩ : syracuseStep 23097797 = 4330837) B4330837
theorem B15398531 : Blo 1897435 15398531 := bstep (se 1 (by rfl) ⟨11548898, by rfl⟩ : syracuseStep 15398531 = 23097797) B23097797
theorem B10265687 : Blo 1897435 10265687 := bstep (se 1 (by rfl) ⟨7699265, by rfl⟩ : syracuseStep 10265687 = 15398531) B15398531
theorem B6843791 : Blo 1897435 6843791 := bstep (se 1 (by rfl) ⟨5132843, by rfl⟩ : syracuseStep 6843791 = 10265687) B10265687
theorem B4562527 : Blo 1897435 4562527 := bstep (se 1 (by rfl) ⟨3421895, by rfl⟩ : syracuseStep 4562527 = 6843791) B6843791
theorem B6083369 : Blo 1897435 6083369 := bstep (se 2 (by rfl) ⟨2281263, by rfl⟩ : syracuseStep 6083369 = 4562527) B4562527
theorem B4055579 : Blo 1897435 4055579 := bstep (se 1 (by rfl) ⟨3041684, by rfl⟩ : syracuseStep 4055579 = 6083369) B6083369
theorem B2703719 : Blo 1897435 2703719 := bstep (se 1 (by rfl) ⟨2027789, by rfl⟩ : syracuseStep 2703719 = 4055579) B4055579
theorem B7209917 : Blo 1897435 7209917 := bstep (se 3 (by rfl) ⟨1351859, by rfl⟩ : syracuseStep 7209917 = 2703719) B2703719
theorem B4806611 : Blo 1897435 4806611 := bstep (se 1 (by rfl) ⟨3604958, by rfl⟩ : syracuseStep 4806611 = 7209917) B7209917
theorem B3204407 : Blo 1897435 3204407 := bstep (se 1 (by rfl) ⟨2403305, by rfl⟩ : syracuseStep 3204407 = 4806611) B4806611
theorem B2136271 : Blo 1897435 2136271 := bstep (se 1 (by rfl) ⟨1602203, by rfl⟩ : syracuseStep 2136271 = 3204407) B3204407
theorem B2848361 : Blo 1897435 2848361 := bstep (se 2 (by rfl) ⟨1068135, by rfl⟩ : syracuseStep 2848361 = 2136271) B2136271
theorem B1898907 : Blo 1897435 1898907 := bstep (se 1 (by rfl) ⟨1424180, by rfl⟩ : syracuseStep 1898907 = 2848361) B2848361
theorem B8111173 : Blo 1897435 8111173 := bbase (se 4 (by rfl) ⟨760422, by rfl⟩ : syracuseStep 8111173 = 1520845) (by norm_num)
theorem B10814897 : Blo 1897435 10814897 := bstep (se 2 (by rfl) ⟨4055586, by rfl⟩ : syracuseStep 10814897 = 8111173) B8111173
theorem B7209931 : Blo 1897435 7209931 := bstep (se 1 (by rfl) ⟨5407448, by rfl⟩ : syracuseStep 7209931 = 10814897) B10814897
theorem B9613241 : Blo 1897435 9613241 := bstep (se 2 (by rfl) ⟨3604965, by rfl⟩ : syracuseStep 9613241 = 7209931) B7209931
theorem B6408827 : Blo 1897435 6408827 := bstep (se 1 (by rfl) ⟨4806620, by rfl⟩ : syracuseStep 6408827 = 9613241) B9613241
theorem B4272551 : Blo 1897435 4272551 := bstep (se 1 (by rfl) ⟨3204413, by rfl⟩ : syracuseStep 4272551 = 6408827) B6408827
theorem B2848367 : Blo 1897435 2848367 := bstep (se 1 (by rfl) ⟨2136275, by rfl⟩ : syracuseStep 2848367 = 4272551) B4272551
theorem B1898911 : Blo 1897435 1898911 := bstep (se 1 (by rfl) ⟨1424183, by rfl⟩ : syracuseStep 1898911 = 2848367) B2848367
theorem B2848373 : Blo 1897435 2848373 := bbase (se 5 (by rfl) ⟨133517, by rfl⟩ : syracuseStep 2848373 = 267035) (by norm_num)
theorem B1898915 : Blo 1897435 1898915 := bstep (se 1 (by rfl) ⟨1424186, by rfl⟩ : syracuseStep 1898915 = 2848373) B2848373
theorem B3604981 : Blo 1897435 3604981 := bbase (se 5 (by rfl) ⟨168983, by rfl⟩ : syracuseStep 3604981 = 337967) (by norm_num)
theorem B4806641 : Blo 1897435 4806641 := bstep (se 2 (by rfl) ⟨1802490, by rfl⟩ : syracuseStep 4806641 = 3604981) B3604981
theorem B3204427 : Blo 1897435 3204427 := bstep (se 1 (by rfl) ⟨2403320, by rfl⟩ : syracuseStep 3204427 = 4806641) B4806641
theorem B4272569 : Blo 1897435 4272569 := bstep (se 2 (by rfl) ⟨1602213, by rfl⟩ : syracuseStep 4272569 = 3204427) B3204427
theorem B2848379 : Blo 1897435 2848379 := bstep (se 1 (by rfl) ⟨2136284, by rfl⟩ : syracuseStep 2848379 = 4272569) B4272569
theorem B1898919 : Blo 1897435 1898919 := bstep (se 1 (by rfl) ⟨1424189, by rfl⟩ : syracuseStep 1898919 = 2848379) B2848379
theorem B2136289 : Blo 1897435 2136289 := bbase (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) (by norm_num)
theorem B2848385 : Blo 1897435 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B1898923 : Blo 1897435 1898923 := bstep (se 1 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 1898923 = 2848385) B2848385
theorem B4806661 : Blo 1897435 4806661 := bbase (se 4 (by rfl) ⟨450624, by rfl⟩ : syracuseStep 4806661 = 901249) (by norm_num)
theorem B6408881 : Blo 1897435 6408881 := bstep (se 2 (by rfl) ⟨2403330, by rfl⟩ : syracuseStep 6408881 = 4806661) B4806661
theorem B4272587 : Blo 1897435 4272587 := bstep (se 1 (by rfl) ⟨3204440, by rfl⟩ : syracuseStep 4272587 = 6408881) B6408881
theorem B2848391 : Blo 1897435 2848391 := bstep (se 1 (by rfl) ⟨2136293, by rfl⟩ : syracuseStep 2848391 = 4272587) B4272587
theorem B1898927 : Blo 1897435 1898927 := bstep (se 1 (by rfl) ⟨1424195, by rfl⟩ : syracuseStep 1898927 = 2848391) B2848391
theorem B2848397 : Blo 1897435 2848397 := bbase (se 3 (by rfl) ⟨534074, by rfl⟩ : syracuseStep 2848397 = 1068149) (by norm_num)
theorem B1898931 : Blo 1897435 1898931 := bstep (se 1 (by rfl) ⟨1424198, by rfl⟩ : syracuseStep 1898931 = 2848397) B2848397
theorem B4272605 : Blo 1897435 4272605 := bbase (se 3 (by rfl) ⟨801113, by rfl⟩ : syracuseStep 4272605 = 1602227) (by norm_num)
theorem B2848403 : Blo 1897435 2848403 := bstep (se 1 (by rfl) ⟨2136302, by rfl⟩ : syracuseStep 2848403 = 4272605) B4272605
theorem B1898935 : Blo 1897435 1898935 := bstep (se 1 (by rfl) ⟨1424201, by rfl⟩ : syracuseStep 1898935 = 2848403) B2848403
theorem B3204461 : Blo 1897435 3204461 := bbase (se 3 (by rfl) ⟨600836, by rfl⟩ : syracuseStep 3204461 = 1201673) (by norm_num)
theorem B2136307 : Blo 1897435 2136307 := bstep (se 1 (by rfl) ⟨1602230, by rfl⟩ : syracuseStep 2136307 = 3204461) B3204461
theorem B2848409 : Blo 1897435 2848409 := bstep (se 2 (by rfl) ⟨1068153, by rfl⟩ : syracuseStep 2848409 = 2136307) B2136307
theorem B1898939 : Blo 1897435 1898939 := bstep (se 1 (by rfl) ⟨1424204, by rfl⟩ : syracuseStep 1898939 = 2848409) B2848409
theorem B18499445 : Blo 1897435 18499445 := bbase (se 5 (by rfl) ⟨867161, by rfl⟩ : syracuseStep 18499445 = 1734323) (by norm_num)
theorem B12332963 : Blo 1897435 12332963 := bstep (se 1 (by rfl) ⟨9249722, by rfl⟩ : syracuseStep 12332963 = 18499445) B18499445
theorem B32887901 : Blo 1897435 32887901 := bstep (se 3 (by rfl) ⟨6166481, by rfl⟩ : syracuseStep 32887901 = 12332963) B12332963
theorem B87701069 : Blo 1897435 87701069 := bstep (se 3 (by rfl) ⟨16443950, by rfl⟩ : syracuseStep 87701069 = 32887901) B32887901
theorem B58467379 : Blo 1897435 58467379 := bstep (se 1 (by rfl) ⟨43850534, by rfl⟩ : syracuseStep 58467379 = 87701069) B87701069
theorem B77956505 : Blo 1897435 77956505 := bstep (se 2 (by rfl) ⟨29233689, by rfl⟩ : syracuseStep 77956505 = 58467379) B58467379
theorem B51971003 : Blo 1897435 51971003 := bstep (se 1 (by rfl) ⟨38978252, by rfl⟩ : syracuseStep 51971003 = 77956505) B77956505
theorem B34647335 : Blo 1897435 34647335 := bstep (se 1 (by rfl) ⟨25985501, by rfl⟩ : syracuseStep 34647335 = 51971003) B51971003
theorem B23098223 : Blo 1897435 23098223 := bstep (se 1 (by rfl) ⟨17323667, by rfl⟩ : syracuseStep 23098223 = 34647335) B34647335
theorem B61595261 : Blo 1897435 61595261 := bstep (se 3 (by rfl) ⟨11549111, by rfl⟩ : syracuseStep 61595261 = 23098223) B23098223
theorem B41063507 : Blo 1897435 41063507 := bstep (se 1 (by rfl) ⟨30797630, by rfl⟩ : syracuseStep 41063507 = 61595261) B61595261
theorem B27375671 : Blo 1897435 27375671 := bstep (se 1 (by rfl) ⟨20531753, by rfl⟩ : syracuseStep 27375671 = 41063507) B41063507
theorem B18250447 : Blo 1897435 18250447 := bstep (se 1 (by rfl) ⟨13687835, by rfl⟩ : syracuseStep 18250447 = 27375671) B27375671
theorem B24333929 : Blo 1897435 24333929 := bstep (se 2 (by rfl) ⟨9125223, by rfl⟩ : syracuseStep 24333929 = 18250447) B18250447
theorem B16222619 : Blo 1897435 16222619 := bstep (se 1 (by rfl) ⟨12166964, by rfl⟩ : syracuseStep 16222619 = 24333929) B24333929
theorem B10815079 : Blo 1897435 10815079 := bstep (se 1 (by rfl) ⟨8111309, by rfl⟩ : syracuseStep 10815079 = 16222619) B16222619
theorem B14420105 : Blo 1897435 14420105 := bstep (se 2 (by rfl) ⟨5407539, by rfl⟩ : syracuseStep 14420105 = 10815079) B10815079
theorem B9613403 : Blo 1897435 9613403 := bstep (se 1 (by rfl) ⟨7210052, by rfl⟩ : syracuseStep 9613403 = 14420105) B14420105
theorem B6408935 : Blo 1897435 6408935 := bstep (se 1 (by rfl) ⟨4806701, by rfl⟩ : syracuseStep 6408935 = 9613403) B9613403
theorem B4272623 : Blo 1897435 4272623 := bstep (se 1 (by rfl) ⟨3204467, by rfl⟩ : syracuseStep 4272623 = 6408935) B6408935
theorem B2848415 : Blo 1897435 2848415 := bstep (se 1 (by rfl) ⟨2136311, by rfl⟩ : syracuseStep 2848415 = 4272623) B4272623
theorem B1898943 : Blo 1897435 1898943 := bstep (se 1 (by rfl) ⟨1424207, by rfl⟩ : syracuseStep 1898943 = 2848415) B2848415
theorem B2848421 : Blo 1897435 2848421 := bbase (se 4 (by rfl) ⟨267039, by rfl⟩ : syracuseStep 2848421 = 534079) (by norm_num)
theorem B1898947 : Blo 1897435 1898947 := bstep (se 1 (by rfl) ⟨1424210, by rfl⟩ : syracuseStep 1898947 = 2848421) B2848421
theorem B2403361 : Blo 1897435 2403361 := bbase (se 2 (by rfl) ⟨901260, by rfl⟩ : syracuseStep 2403361 = 1802521) (by norm_num)
theorem B3204481 : Blo 1897435 3204481 := bstep (se 2 (by rfl) ⟨1201680, by rfl⟩ : syracuseStep 3204481 = 2403361) B2403361
theorem B4272641 : Blo 1897435 4272641 := bstep (se 2 (by rfl) ⟨1602240, by rfl⟩ : syracuseStep 4272641 = 3204481) B3204481
theorem B2848427 : Blo 1897435 2848427 := bstep (se 1 (by rfl) ⟨2136320, by rfl⟩ : syracuseStep 2848427 = 4272641) B4272641
theorem B1898951 : Blo 1897435 1898951 := bstep (se 1 (by rfl) ⟨1424213, by rfl⟩ : syracuseStep 1898951 = 2848427) B2848427
theorem B2136325 : Blo 1897435 2136325 := bbase (se 4 (by rfl) ⟨200280, by rfl⟩ : syracuseStep 2136325 = 400561) (by norm_num)
theorem B2848433 : Blo 1897435 2848433 := bstep (se 2 (by rfl) ⟨1068162, by rfl⟩ : syracuseStep 2848433 = 2136325) B2136325
theorem B1898955 : Blo 1897435 1898955 := bstep (se 1 (by rfl) ⟨1424216, by rfl⟩ : syracuseStep 1898955 = 2848433) B2848433
theorem B2027845 : Blo 1897435 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B2703793 : Blo 1897435 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B3605057 : Blo 1897435 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B2403371 : Blo 1897435 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B6408989 : Blo 1897435 6408989 := bstep (se 3 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 6408989 = 2403371) B2403371
theorem B4272659 : Blo 1897435 4272659 := bstep (se 1 (by rfl) ⟨3204494, by rfl⟩ : syracuseStep 4272659 = 6408989) B6408989
theorem B2848439 : Blo 1897435 2848439 := bstep (se 1 (by rfl) ⟨2136329, by rfl⟩ : syracuseStep 2848439 = 4272659) B4272659
theorem B1898959 : Blo 1897435 1898959 := bstep (se 1 (by rfl) ⟨1424219, by rfl⟩ : syracuseStep 1898959 = 2848439) B2848439
theorem B2848445 : Blo 1897435 2848445 := bbase (se 3 (by rfl) ⟨534083, by rfl⟩ : syracuseStep 2848445 = 1068167) (by norm_num)
theorem B1898963 : Blo 1897435 1898963 := bstep (se 1 (by rfl) ⟨1424222, by rfl⟩ : syracuseStep 1898963 = 2848445) B2848445
theorem B4272677 : Blo 1897435 4272677 := bbase (se 4 (by rfl) ⟨400563, by rfl⟩ : syracuseStep 4272677 = 801127) (by norm_num)
theorem B2848451 : Blo 1897435 2848451 := bstep (se 1 (by rfl) ⟨2136338, by rfl⟩ : syracuseStep 2848451 = 4272677) B4272677
theorem B1898967 : Blo 1897435 1898967 := bstep (se 1 (by rfl) ⟨1424225, by rfl⟩ : syracuseStep 1898967 = 2848451) B2848451
theorem B4806773 : Blo 1897435 4806773 := bbase (se 5 (by rfl) ⟨225317, by rfl⟩ : syracuseStep 4806773 = 450635) (by norm_num)
theorem B3204515 : Blo 1897435 3204515 := bstep (se 1 (by rfl) ⟨2403386, by rfl⟩ : syracuseStep 3204515 = 4806773) B4806773
theorem B2136343 : Blo 1897435 2136343 := bstep (se 1 (by rfl) ⟨1602257, by rfl⟩ : syracuseStep 2136343 = 3204515) B3204515
theorem B2848457 : Blo 1897435 2848457 := bstep (se 2 (by rfl) ⟨1068171, by rfl⟩ : syracuseStep 2848457 = 2136343) B2136343
theorem B1898971 : Blo 1897435 1898971 := bstep (se 1 (by rfl) ⟨1424228, by rfl⟩ : syracuseStep 1898971 = 2848457) B2848457
theorem B1924885 : Blo 1897435 1924885 := bbase (se 6 (by rfl) ⟨45114, by rfl⟩ : syracuseStep 1924885 = 90229) (by norm_num)
theorem B2566513 : Blo 1897435 2566513 := bstep (se 2 (by rfl) ⟨962442, by rfl⟩ : syracuseStep 2566513 = 1924885) B1924885
theorem B3422017 : Blo 1897435 3422017 := bstep (se 2 (by rfl) ⟨1283256, by rfl⟩ : syracuseStep 3422017 = 2566513) B2566513
theorem B18250757 : Blo 1897435 18250757 := bstep (se 4 (by rfl) ⟨1711008, by rfl⟩ : syracuseStep 18250757 = 3422017) B3422017
theorem B12167171 : Blo 1897435 12167171 := bstep (se 1 (by rfl) ⟨9125378, by rfl⟩ : syracuseStep 12167171 = 18250757) B18250757
theorem B8111447 : Blo 1897435 8111447 := bstep (se 1 (by rfl) ⟨6083585, by rfl⟩ : syracuseStep 8111447 = 12167171) B12167171
theorem B5407631 : Blo 1897435 5407631 := bstep (se 1 (by rfl) ⟨4055723, by rfl⟩ : syracuseStep 5407631 = 8111447) B8111447
theorem B3605087 : Blo 1897435 3605087 := bstep (se 1 (by rfl) ⟨2703815, by rfl⟩ : syracuseStep 3605087 = 5407631) B5407631
theorem B9613565 : Blo 1897435 9613565 := bstep (se 3 (by rfl) ⟨1802543, by rfl⟩ : syracuseStep 9613565 = 3605087) B3605087
theorem B6409043 : Blo 1897435 6409043 := bstep (se 1 (by rfl) ⟨4806782, by rfl⟩ : syracuseStep 6409043 = 9613565) B9613565
theorem B4272695 : Blo 1897435 4272695 := bstep (se 1 (by rfl) ⟨3204521, by rfl⟩ : syracuseStep 4272695 = 6409043) B6409043
theorem B2848463 : Blo 1897435 2848463 := bstep (se 1 (by rfl) ⟨2136347, by rfl⟩ : syracuseStep 2848463 = 4272695) B4272695
theorem B1898975 : Blo 1897435 1898975 := bstep (se 1 (by rfl) ⟨1424231, by rfl⟩ : syracuseStep 1898975 = 2848463) B2848463
theorem B2848469 : Blo 1897435 2848469 := bbase (se 7 (by rfl) ⟨33380, by rfl⟩ : syracuseStep 2848469 = 66761) (by norm_num)
theorem B1898979 : Blo 1897435 1898979 := bstep (se 1 (by rfl) ⟨1424234, by rfl⟩ : syracuseStep 1898979 = 2848469) B2848469
theorem B4055741 : Blo 1897435 4055741 := bbase (se 3 (by rfl) ⟨760451, by rfl⟩ : syracuseStep 4055741 = 1520903) (by norm_num)
theorem B2703827 : Blo 1897435 2703827 := bstep (se 1 (by rfl) ⟨2027870, by rfl⟩ : syracuseStep 2703827 = 4055741) B4055741
theorem B7210205 : Blo 1897435 7210205 := bstep (se 3 (by rfl) ⟨1351913, by rfl⟩ : syracuseStep 7210205 = 2703827) B2703827
theorem B4806803 : Blo 1897435 4806803 := bstep (se 1 (by rfl) ⟨3605102, by rfl⟩ : syracuseStep 4806803 = 7210205) B7210205
theorem B3204535 : Blo 1897435 3204535 := bstep (se 1 (by rfl) ⟨2403401, by rfl⟩ : syracuseStep 3204535 = 4806803) B4806803
theorem B4272713 : Blo 1897435 4272713 := bstep (se 2 (by rfl) ⟨1602267, by rfl⟩ : syracuseStep 4272713 = 3204535) B3204535
theorem B2848475 : Blo 1897435 2848475 := bstep (se 1 (by rfl) ⟨2136356, by rfl⟩ : syracuseStep 2848475 = 4272713) B4272713
theorem B1898983 : Blo 1897435 1898983 := bstep (se 1 (by rfl) ⟨1424237, by rfl⟩ : syracuseStep 1898983 = 2848475) B2848475
theorem B2136361 : Blo 1897435 2136361 := bbase (se 2 (by rfl) ⟨801135, by rfl⟩ : syracuseStep 2136361 = 1602271) (by norm_num)
theorem B2848481 : Blo 1897435 2848481 := bstep (se 2 (by rfl) ⟨1068180, by rfl⟩ : syracuseStep 2848481 = 2136361) B2136361
theorem B1898987 : Blo 1897435 1898987 := bstep (se 1 (by rfl) ⟨1424240, by rfl⟩ : syracuseStep 1898987 = 2848481) B2848481
theorem B1951165 : Blo 1897435 1951165 := bbase (se 3 (by rfl) ⟨365843, by rfl⟩ : syracuseStep 1951165 = 731687) (by norm_num)
theorem B2601553 : Blo 1897435 2601553 := bstep (se 2 (by rfl) ⟨975582, by rfl⟩ : syracuseStep 2601553 = 1951165) B1951165
theorem B3468737 : Blo 1897435 3468737 := bstep (se 2 (by rfl) ⟨1300776, by rfl⟩ : syracuseStep 3468737 = 2601553) B2601553
theorem B2312491 : Blo 1897435 2312491 := bstep (se 1 (by rfl) ⟨1734368, by rfl⟩ : syracuseStep 2312491 = 3468737) B3468737
theorem B3083321 : Blo 1897435 3083321 := bstep (se 2 (by rfl) ⟨1156245, by rfl⟩ : syracuseStep 3083321 = 2312491) B2312491
theorem B2055547 : Blo 1897435 2055547 := bstep (se 1 (by rfl) ⟨1541660, by rfl⟩ : syracuseStep 2055547 = 3083321) B3083321
theorem B2740729 : Blo 1897435 2740729 := bstep (se 2 (by rfl) ⟨1027773, by rfl⟩ : syracuseStep 2740729 = 2055547) B2055547
theorem B3654305 : Blo 1897435 3654305 := bstep (se 2 (by rfl) ⟨1370364, by rfl⟩ : syracuseStep 3654305 = 2740729) B2740729
theorem B2436203 : Blo 1897435 2436203 := bstep (se 1 (by rfl) ⟨1827152, by rfl⟩ : syracuseStep 2436203 = 3654305) B3654305
theorem B6496541 : Blo 1897435 6496541 := bstep (se 3 (by rfl) ⟨1218101, by rfl⟩ : syracuseStep 6496541 = 2436203) B2436203
theorem B4331027 : Blo 1897435 4331027 := bstep (se 1 (by rfl) ⟨3248270, by rfl⟩ : syracuseStep 4331027 = 6496541) B6496541
theorem B11549405 : Blo 1897435 11549405 := bstep (se 3 (by rfl) ⟨2165513, by rfl⟩ : syracuseStep 11549405 = 4331027) B4331027
theorem B30798413 : Blo 1897435 30798413 := bstep (se 3 (by rfl) ⟨5774702, by rfl⟩ : syracuseStep 30798413 = 11549405) B11549405
theorem B20532275 : Blo 1897435 20532275 := bstep (se 1 (by rfl) ⟨15399206, by rfl⟩ : syracuseStep 20532275 = 30798413) B30798413
theorem B13688183 : Blo 1897435 13688183 := bstep (se 1 (by rfl) ⟨10266137, by rfl⟩ : syracuseStep 13688183 = 20532275) B20532275
theorem B9125455 : Blo 1897435 9125455 := bstep (se 1 (by rfl) ⟨6844091, by rfl⟩ : syracuseStep 9125455 = 13688183) B13688183
theorem B12167273 : Blo 1897435 12167273 := bstep (se 2 (by rfl) ⟨4562727, by rfl⟩ : syracuseStep 12167273 = 9125455) B9125455
theorem B8111515 : Blo 1897435 8111515 := bstep (se 1 (by rfl) ⟨6083636, by rfl⟩ : syracuseStep 8111515 = 12167273) B12167273
theorem B10815353 : Blo 1897435 10815353 := bstep (se 2 (by rfl) ⟨4055757, by rfl⟩ : syracuseStep 10815353 = 8111515) B8111515
theorem B7210235 : Blo 1897435 7210235 := bstep (se 1 (by rfl) ⟨5407676, by rfl⟩ : syracuseStep 7210235 = 10815353) B10815353
theorem B4806823 : Blo 1897435 4806823 := bstep (se 1 (by rfl) ⟨3605117, by rfl⟩ : syracuseStep 4806823 = 7210235) B7210235
theorem B6409097 : Blo 1897435 6409097 := bstep (se 2 (by rfl) ⟨2403411, by rfl⟩ : syracuseStep 6409097 = 4806823) B4806823
theorem B4272731 : Blo 1897435 4272731 := bstep (se 1 (by rfl) ⟨3204548, by rfl⟩ : syracuseStep 4272731 = 6409097) B6409097
theorem B2848487 : Blo 1897435 2848487 := bstep (se 1 (by rfl) ⟨2136365, by rfl⟩ : syracuseStep 2848487 = 4272731) B4272731
theorem B1898991 : Blo 1897435 1898991 := bstep (se 1 (by rfl) ⟨1424243, by rfl⟩ : syracuseStep 1898991 = 2848487) B2848487
theorem B2848493 : Blo 1897435 2848493 := bbase (se 3 (by rfl) ⟨534092, by rfl⟩ : syracuseStep 2848493 = 1068185) (by norm_num)
theorem B1898995 : Blo 1897435 1898995 := bstep (se 1 (by rfl) ⟨1424246, by rfl⟩ : syracuseStep 1898995 = 2848493) B2848493
theorem B4272749 : Blo 1897435 4272749 := bbase (se 3 (by rfl) ⟨801140, by rfl⟩ : syracuseStep 4272749 = 1602281) (by norm_num)
theorem B2848499 : Blo 1897435 2848499 := bstep (se 1 (by rfl) ⟨2136374, by rfl⟩ : syracuseStep 2848499 = 4272749) B4272749
theorem B1898999 : Blo 1897435 1898999 := bstep (se 1 (by rfl) ⟨1424249, by rfl⟩ : syracuseStep 1898999 = 2848499) B2848499
theorem B3605141 : Blo 1897435 3605141 := bbase (se 6 (by rfl) ⟨84495, by rfl⟩ : syracuseStep 3605141 = 168991) (by norm_num)
theorem B2403427 : Blo 1897435 2403427 := bstep (se 1 (by rfl) ⟨1802570, by rfl⟩ : syracuseStep 2403427 = 3605141) B3605141
theorem B3204569 : Blo 1897435 3204569 := bstep (se 2 (by rfl) ⟨1201713, by rfl⟩ : syracuseStep 3204569 = 2403427) B2403427
theorem B2136379 : Blo 1897435 2136379 := bstep (se 1 (by rfl) ⟨1602284, by rfl⟩ : syracuseStep 2136379 = 3204569) B3204569
theorem B2848505 : Blo 1897435 2848505 := bstep (se 2 (by rfl) ⟨1068189, by rfl⟩ : syracuseStep 2848505 = 2136379) B2136379
theorem B1899003 : Blo 1897435 1899003 := bstep (se 1 (by rfl) ⟨1424252, by rfl⟩ : syracuseStep 1899003 = 2848505) B2848505
theorem B2083609 : Blo 1897435 2083609 := bbase (se 2 (by rfl) ⟨781353, by rfl⟩ : syracuseStep 2083609 = 1562707) (by norm_num)
theorem B2778145 : Blo 1897435 2778145 := bstep (se 2 (by rfl) ⟨1041804, by rfl⟩ : syracuseStep 2778145 = 2083609) B2083609
theorem B14816773 : Blo 1897435 14816773 := bstep (se 4 (by rfl) ⟨1389072, by rfl⟩ : syracuseStep 14816773 = 2778145) B2778145
theorem B79022789 : Blo 1897435 79022789 := bstep (se 4 (by rfl) ⟨7408386, by rfl⟩ : syracuseStep 79022789 = 14816773) B14816773
theorem B52681859 : Blo 1897435 52681859 := bstep (se 1 (by rfl) ⟨39511394, by rfl⟩ : syracuseStep 52681859 = 79022789) B79022789
theorem B35121239 : Blo 1897435 35121239 := bstep (se 1 (by rfl) ⟨26340929, by rfl⟩ : syracuseStep 35121239 = 52681859) B52681859
theorem B23414159 : Blo 1897435 23414159 := bstep (se 1 (by rfl) ⟨17560619, by rfl⟩ : syracuseStep 23414159 = 35121239) B35121239
theorem B15609439 : Blo 1897435 15609439 := bstep (se 1 (by rfl) ⟨11707079, by rfl⟩ : syracuseStep 15609439 = 23414159) B23414159
theorem B20812585 : Blo 1897435 20812585 := bstep (se 2 (by rfl) ⟨7804719, by rfl⟩ : syracuseStep 20812585 = 15609439) B15609439
theorem B27750113 : Blo 1897435 27750113 := bstep (se 2 (by rfl) ⟨10406292, by rfl⟩ : syracuseStep 27750113 = 20812585) B20812585
theorem B18500075 : Blo 1897435 18500075 := bstep (se 1 (by rfl) ⟨13875056, by rfl⟩ : syracuseStep 18500075 = 27750113) B27750113
theorem B12333383 : Blo 1897435 12333383 := bstep (se 1 (by rfl) ⟨9250037, by rfl⟩ : syracuseStep 12333383 = 18500075) B18500075
theorem B8222255 : Blo 1897435 8222255 := bstep (se 1 (by rfl) ⟨6166691, by rfl⟩ : syracuseStep 8222255 = 12333383) B12333383
theorem B5481503 : Blo 1897435 5481503 := bstep (se 1 (by rfl) ⟨4111127, by rfl⟩ : syracuseStep 5481503 = 8222255) B8222255
theorem B3654335 : Blo 1897435 3654335 := bstep (se 1 (by rfl) ⟨2740751, by rfl⟩ : syracuseStep 3654335 = 5481503) B5481503
theorem B2436223 : Blo 1897435 2436223 := bstep (se 1 (by rfl) ⟨1827167, by rfl⟩ : syracuseStep 2436223 = 3654335) B3654335
theorem B3248297 : Blo 1897435 3248297 := bstep (se 2 (by rfl) ⟨1218111, by rfl⟩ : syracuseStep 3248297 = 2436223) B2436223
theorem B34648501 : Blo 1897435 34648501 := bstep (se 5 (by rfl) ⟨1624148, by rfl⟩ : syracuseStep 34648501 = 3248297) B3248297
theorem B46198001 : Blo 1897435 46198001 := bstep (se 2 (by rfl) ⟨17324250, by rfl⟩ : syracuseStep 46198001 = 34648501) B34648501
theorem B30798667 : Blo 1897435 30798667 := bstep (se 1 (by rfl) ⟨23099000, by rfl⟩ : syracuseStep 30798667 = 46198001) B46198001
theorem B41064889 : Blo 1897435 41064889 := bstep (se 2 (by rfl) ⟨15399333, by rfl⟩ : syracuseStep 41064889 = 30798667) B30798667
theorem B54753185 : Blo 1897435 54753185 := bstep (se 2 (by rfl) ⟨20532444, by rfl⟩ : syracuseStep 54753185 = 41064889) B41064889
theorem B36502123 : Blo 1897435 36502123 := bstep (se 1 (by rfl) ⟨27376592, by rfl⟩ : syracuseStep 36502123 = 54753185) B54753185
theorem B48669497 : Blo 1897435 48669497 := bstep (se 2 (by rfl) ⟨18251061, by rfl⟩ : syracuseStep 48669497 = 36502123) B36502123
theorem B32446331 : Blo 1897435 32446331 := bstep (se 1 (by rfl) ⟨24334748, by rfl⟩ : syracuseStep 32446331 = 48669497) B48669497
theorem B21630887 : Blo 1897435 21630887 := bstep (se 1 (by rfl) ⟨16223165, by rfl⟩ : syracuseStep 21630887 = 32446331) B32446331
theorem B14420591 : Blo 1897435 14420591 := bstep (se 1 (by rfl) ⟨10815443, by rfl⟩ : syracuseStep 14420591 = 21630887) B21630887
theorem B9613727 : Blo 1897435 9613727 := bstep (se 1 (by rfl) ⟨7210295, by rfl⟩ : syracuseStep 9613727 = 14420591) B14420591
theorem B6409151 : Blo 1897435 6409151 := bstep (se 1 (by rfl) ⟨4806863, by rfl⟩ : syracuseStep 6409151 = 9613727) B9613727
theorem B4272767 : Blo 1897435 4272767 := bstep (se 1 (by rfl) ⟨3204575, by rfl⟩ : syracuseStep 4272767 = 6409151) B6409151
theorem B2848511 : Blo 1897435 2848511 := bstep (se 1 (by rfl) ⟨2136383, by rfl⟩ : syracuseStep 2848511 = 4272767) B4272767
theorem B1899007 : Blo 1897435 1899007 := bstep (se 1 (by rfl) ⟨1424255, by rfl⟩ : syracuseStep 1899007 = 2848511) B2848511
theorem B2848517 : Blo 1897435 2848517 := bbase (se 4 (by rfl) ⟨267048, by rfl⟩ : syracuseStep 2848517 = 534097) (by norm_num)
theorem B1899011 : Blo 1897435 1899011 := bstep (se 1 (by rfl) ⟨1424258, by rfl⟩ : syracuseStep 1899011 = 2848517) B2848517
theorem B3204589 : Blo 1897435 3204589 := bbase (se 3 (by rfl) ⟨600860, by rfl⟩ : syracuseStep 3204589 = 1201721) (by norm_num)
theorem B4272785 : Blo 1897435 4272785 := bstep (se 2 (by rfl) ⟨1602294, by rfl⟩ : syracuseStep 4272785 = 3204589) B3204589
theorem B2848523 : Blo 1897435 2848523 := bstep (se 1 (by rfl) ⟨2136392, by rfl⟩ : syracuseStep 2848523 = 4272785) B4272785
theorem B1899015 : Blo 1897435 1899015 := bstep (se 1 (by rfl) ⟨1424261, by rfl⟩ : syracuseStep 1899015 = 2848523) B2848523
theorem B2136397 : Blo 1897435 2136397 := bbase (se 3 (by rfl) ⟨400574, by rfl⟩ : syracuseStep 2136397 = 801149) (by norm_num)
theorem B2848529 : Blo 1897435 2848529 := bstep (se 2 (by rfl) ⟨1068198, by rfl⟩ : syracuseStep 2848529 = 2136397) B2136397
theorem B1899019 : Blo 1897435 1899019 := bstep (se 1 (by rfl) ⟨1424264, by rfl⟩ : syracuseStep 1899019 = 2848529) B2848529
theorem B6409205 : Blo 1897435 6409205 := bbase (se 5 (by rfl) ⟨300431, by rfl⟩ : syracuseStep 6409205 = 600863) (by norm_num)
theorem B4272803 : Blo 1897435 4272803 := bstep (se 1 (by rfl) ⟨3204602, by rfl⟩ : syracuseStep 4272803 = 6409205) B6409205
theorem B2848535 : Blo 1897435 2848535 := bstep (se 1 (by rfl) ⟨2136401, by rfl⟩ : syracuseStep 2848535 = 4272803) B4272803
theorem B1899023 : Blo 1897435 1899023 := bstep (se 1 (by rfl) ⟨1424267, by rfl⟩ : syracuseStep 1899023 = 2848535) B2848535
theorem B2848541 : Blo 1897435 2848541 := bbase (se 3 (by rfl) ⟨534101, by rfl⟩ : syracuseStep 2848541 = 1068203) (by norm_num)
theorem B1899027 : Blo 1897435 1899027 := bstep (se 1 (by rfl) ⟨1424270, by rfl⟩ : syracuseStep 1899027 = 2848541) B2848541
theorem B4272821 : Blo 1897435 4272821 := bbase (se 5 (by rfl) ⟨200288, by rfl⟩ : syracuseStep 4272821 = 400577) (by norm_num)
theorem B2848547 : Blo 1897435 2848547 := bstep (se 1 (by rfl) ⟨2136410, by rfl⟩ : syracuseStep 2848547 = 4272821) B4272821
theorem B1899031 : Blo 1897435 1899031 := bstep (se 1 (by rfl) ⟨1424273, by rfl⟩ : syracuseStep 1899031 = 2848547) B2848547
theorem B10815605 : Blo 1897435 10815605 := bbase (se 5 (by rfl) ⟨506981, by rfl⟩ : syracuseStep 10815605 = 1013963) (by norm_num)
theorem B7210403 : Blo 1897435 7210403 := bstep (se 1 (by rfl) ⟨5407802, by rfl⟩ : syracuseStep 7210403 = 10815605) B10815605
theorem B4806935 : Blo 1897435 4806935 := bstep (se 1 (by rfl) ⟨3605201, by rfl⟩ : syracuseStep 4806935 = 7210403) B7210403
theorem B3204623 : Blo 1897435 3204623 := bstep (se 1 (by rfl) ⟨2403467, by rfl⟩ : syracuseStep 3204623 = 4806935) B4806935
theorem B2136415 : Blo 1897435 2136415 := bstep (se 1 (by rfl) ⟨1602311, by rfl⟩ : syracuseStep 2136415 = 3204623) B3204623
theorem B2848553 : Blo 1897435 2848553 := bstep (se 2 (by rfl) ⟨1068207, by rfl⟩ : syracuseStep 2848553 = 2136415) B2136415
theorem B1899035 : Blo 1897435 1899035 := bstep (se 1 (by rfl) ⟨1424276, by rfl⟩ : syracuseStep 1899035 = 2848553) B2848553
theorem B5407813 : Blo 1897435 5407813 := bbase (se 4 (by rfl) ⟨506982, by rfl⟩ : syracuseStep 5407813 = 1013965) (by norm_num)
theorem B7210417 : Blo 1897435 7210417 := bstep (se 2 (by rfl) ⟨2703906, by rfl⟩ : syracuseStep 7210417 = 5407813) B5407813
theorem B9613889 : Blo 1897435 9613889 := bstep (se 2 (by rfl) ⟨3605208, by rfl⟩ : syracuseStep 9613889 = 7210417) B7210417
theorem B6409259 : Blo 1897435 6409259 := bstep (se 1 (by rfl) ⟨4806944, by rfl⟩ : syracuseStep 6409259 = 9613889) B9613889
theorem B4272839 : Blo 1897435 4272839 := bstep (se 1 (by rfl) ⟨3204629, by rfl⟩ : syracuseStep 4272839 = 6409259) B6409259
theorem B2848559 : Blo 1897435 2848559 := bstep (se 1 (by rfl) ⟨2136419, by rfl⟩ : syracuseStep 2848559 = 4272839) B4272839
theorem B1899039 : Blo 1897435 1899039 := bstep (se 1 (by rfl) ⟨1424279, by rfl⟩ : syracuseStep 1899039 = 2848559) B2848559
theorem B2848565 : Blo 1897435 2848565 := bbase (se 5 (by rfl) ⟨133526, by rfl⟩ : syracuseStep 2848565 = 267053) (by norm_num)
theorem B1899043 : Blo 1897435 1899043 := bstep (se 1 (by rfl) ⟨1424282, by rfl⟩ : syracuseStep 1899043 = 2848565) B2848565
theorem B4806965 : Blo 1897435 4806965 := bbase (se 5 (by rfl) ⟨225326, by rfl⟩ : syracuseStep 4806965 = 450653) (by norm_num)
theorem B3204643 : Blo 1897435 3204643 := bstep (se 1 (by rfl) ⟨2403482, by rfl⟩ : syracuseStep 3204643 = 4806965) B4806965
theorem B4272857 : Blo 1897435 4272857 := bstep (se 2 (by rfl) ⟨1602321, by rfl⟩ : syracuseStep 4272857 = 3204643) B3204643
theorem B2848571 : Blo 1897435 2848571 := bstep (se 1 (by rfl) ⟨2136428, by rfl⟩ : syracuseStep 2848571 = 4272857) B4272857
theorem B1899047 : Blo 1897435 1899047 := bstep (se 1 (by rfl) ⟨1424285, by rfl⟩ : syracuseStep 1899047 = 2848571) B2848571
theorem B2136433 : Blo 1897435 2136433 := bbase (se 2 (by rfl) ⟨801162, by rfl⟩ : syracuseStep 2136433 = 1602325) (by norm_num)
theorem B2848577 : Blo 1897435 2848577 := bstep (se 2 (by rfl) ⟨1068216, by rfl⟩ : syracuseStep 2848577 = 2136433) B2136433
theorem B1899051 : Blo 1897435 1899051 := bstep (se 1 (by rfl) ⟨1424288, by rfl⟩ : syracuseStep 1899051 = 2848577) B2848577
theorem B2281441 : Blo 1897435 2281441 := bbase (se 2 (by rfl) ⟨855540, by rfl⟩ : syracuseStep 2281441 = 1711081) (by norm_num)
theorem B3041921 : Blo 1897435 3041921 := bstep (se 2 (by rfl) ⟨1140720, by rfl⟩ : syracuseStep 3041921 = 2281441) B2281441
theorem B8111789 : Blo 1897435 8111789 := bstep (se 3 (by rfl) ⟨1520960, by rfl⟩ : syracuseStep 8111789 = 3041921) B3041921
theorem B5407859 : Blo 1897435 5407859 := bstep (se 1 (by rfl) ⟨4055894, by rfl⟩ : syracuseStep 5407859 = 8111789) B8111789
theorem B3605239 : Blo 1897435 3605239 := bstep (se 1 (by rfl) ⟨2703929, by rfl⟩ : syracuseStep 3605239 = 5407859) B5407859
theorem B4806985 : Blo 1897435 4806985 := bstep (se 2 (by rfl) ⟨1802619, by rfl⟩ : syracuseStep 4806985 = 3605239) B3605239
theorem B6409313 : Blo 1897435 6409313 := bstep (se 2 (by rfl) ⟨2403492, by rfl⟩ : syracuseStep 6409313 = 4806985) B4806985
theorem B4272875 : Blo 1897435 4272875 := bstep (se 1 (by rfl) ⟨3204656, by rfl⟩ : syracuseStep 4272875 = 6409313) B6409313
theorem B2848583 : Blo 1897435 2848583 := bstep (se 1 (by rfl) ⟨2136437, by rfl⟩ : syracuseStep 2848583 = 4272875) B4272875
theorem B1899055 : Blo 1897435 1899055 := bstep (se 1 (by rfl) ⟨1424291, by rfl⟩ : syracuseStep 1899055 = 2848583) B2848583
theorem B2848589 : Blo 1897435 2848589 := bbase (se 3 (by rfl) ⟨534110, by rfl⟩ : syracuseStep 2848589 = 1068221) (by norm_num)
theorem B1899059 : Blo 1897435 1899059 := bstep (se 1 (by rfl) ⟨1424294, by rfl⟩ : syracuseStep 1899059 = 2848589) B2848589
theorem B4272893 : Blo 1897435 4272893 := bbase (se 3 (by rfl) ⟨801167, by rfl⟩ : syracuseStep 4272893 = 1602335) (by norm_num)
theorem B2848595 : Blo 1897435 2848595 := bstep (se 1 (by rfl) ⟨2136446, by rfl⟩ : syracuseStep 2848595 = 4272893) B4272893
theorem B1899063 : Blo 1897435 1899063 := bstep (se 1 (by rfl) ⟨1424297, by rfl⟩ : syracuseStep 1899063 = 2848595) B2848595
theorem B3204677 : Blo 1897435 3204677 := bbase (se 4 (by rfl) ⟨300438, by rfl⟩ : syracuseStep 3204677 = 600877) (by norm_num)
theorem B2136451 : Blo 1897435 2136451 := bstep (se 1 (by rfl) ⟨1602338, by rfl⟩ : syracuseStep 2136451 = 3204677) B3204677
theorem B2848601 : Blo 1897435 2848601 := bstep (se 2 (by rfl) ⟨1068225, by rfl⟩ : syracuseStep 2848601 = 2136451) B2136451
theorem B1899067 : Blo 1897435 1899067 := bstep (se 1 (by rfl) ⟨1424300, by rfl⟩ : syracuseStep 1899067 = 2848601) B2848601
theorem B14421077 : Blo 1897435 14421077 := bbase (se 8 (by rfl) ⟨84498, by rfl⟩ : syracuseStep 14421077 = 168997) (by norm_num)
theorem B9614051 : Blo 1897435 9614051 := bstep (se 1 (by rfl) ⟨7210538, by rfl⟩ : syracuseStep 9614051 = 14421077) B14421077
theorem B6409367 : Blo 1897435 6409367 := bstep (se 1 (by rfl) ⟨4807025, by rfl⟩ : syracuseStep 6409367 = 9614051) B9614051
theorem B4272911 : Blo 1897435 4272911 := bstep (se 1 (by rfl) ⟨3204683, by rfl⟩ : syracuseStep 4272911 = 6409367) B6409367
theorem B2848607 : Blo 1897435 2848607 := bstep (se 1 (by rfl) ⟨2136455, by rfl⟩ : syracuseStep 2848607 = 4272911) B4272911
theorem B1899071 : Blo 1897435 1899071 := bstep (se 1 (by rfl) ⟨1424303, by rfl⟩ : syracuseStep 1899071 = 2848607) B2848607
theorem B2848613 : Blo 1897435 2848613 := bbase (se 4 (by rfl) ⟨267057, by rfl⟩ : syracuseStep 2848613 = 534115) (by norm_num)
theorem B1899075 : Blo 1897435 1899075 := bstep (se 1 (by rfl) ⟨1424306, by rfl⟩ : syracuseStep 1899075 = 2848613) B2848613
theorem B3605285 : Blo 1897435 3605285 := bbase (se 4 (by rfl) ⟨337995, by rfl⟩ : syracuseStep 3605285 = 675991) (by norm_num)
theorem B2403523 : Blo 1897435 2403523 := bstep (se 1 (by rfl) ⟨1802642, by rfl⟩ : syracuseStep 2403523 = 3605285) B3605285
theorem B3204697 : Blo 1897435 3204697 := bstep (se 2 (by rfl) ⟨1201761, by rfl⟩ : syracuseStep 3204697 = 2403523) B2403523
theorem B4272929 : Blo 1897435 4272929 := bstep (se 2 (by rfl) ⟨1602348, by rfl⟩ : syracuseStep 4272929 = 3204697) B3204697
theorem B2848619 : Blo 1897435 2848619 := bstep (se 1 (by rfl) ⟨2136464, by rfl⟩ : syracuseStep 2848619 = 4272929) B4272929
theorem B1899079 : Blo 1897435 1899079 := bstep (se 1 (by rfl) ⟨1424309, by rfl⟩ : syracuseStep 1899079 = 2848619) B2848619
theorem B2136469 : Blo 1897435 2136469 := bbase (se 6 (by rfl) ⟨50073, by rfl⟩ : syracuseStep 2136469 = 100147) (by norm_num)
theorem B2848625 : Blo 1897435 2848625 := bstep (se 2 (by rfl) ⟨1068234, by rfl⟩ : syracuseStep 2848625 = 2136469) B2136469
theorem B1899083 : Blo 1897435 1899083 := bstep (se 1 (by rfl) ⟨1424312, by rfl⟩ : syracuseStep 1899083 = 2848625) B2848625
theorem B2403533 : Blo 1897435 2403533 := bbase (se 3 (by rfl) ⟨450662, by rfl⟩ : syracuseStep 2403533 = 901325) (by norm_num)
theorem B6409421 : Blo 1897435 6409421 := bstep (se 3 (by rfl) ⟨1201766, by rfl⟩ : syracuseStep 6409421 = 2403533) B2403533
theorem B4272947 : Blo 1897435 4272947 := bstep (se 1 (by rfl) ⟨3204710, by rfl⟩ : syracuseStep 4272947 = 6409421) B6409421
theorem B2848631 : Blo 1897435 2848631 := bstep (se 1 (by rfl) ⟨2136473, by rfl⟩ : syracuseStep 2848631 = 4272947) B4272947
theorem B1899087 : Blo 1897435 1899087 := bstep (se 1 (by rfl) ⟨1424315, by rfl⟩ : syracuseStep 1899087 = 2848631) B2848631
theorem B2848637 : Blo 1897435 2848637 := bbase (se 3 (by rfl) ⟨534119, by rfl⟩ : syracuseStep 2848637 = 1068239) (by norm_num)
theorem B1899091 : Blo 1897435 1899091 := bstep (se 1 (by rfl) ⟨1424318, by rfl⟩ : syracuseStep 1899091 = 2848637) B2848637
theorem B4272965 : Blo 1897435 4272965 := bbase (se 4 (by rfl) ⟨400590, by rfl⟩ : syracuseStep 4272965 = 801181) (by norm_num)
theorem B2848643 : Blo 1897435 2848643 := bstep (se 1 (by rfl) ⟨2136482, by rfl⟩ : syracuseStep 2848643 = 4272965) B4272965
theorem B1899095 : Blo 1897435 1899095 := bstep (se 1 (by rfl) ⟨1424321, by rfl⟩ : syracuseStep 1899095 = 2848643) B2848643
theorem B4055989 : Blo 1897435 4055989 := bbase (se 5 (by rfl) ⟨190124, by rfl⟩ : syracuseStep 4055989 = 380249) (by norm_num)
theorem B5407985 : Blo 1897435 5407985 := bstep (se 2 (by rfl) ⟨2027994, by rfl⟩ : syracuseStep 5407985 = 4055989) B4055989
theorem B3605323 : Blo 1897435 3605323 := bstep (se 1 (by rfl) ⟨2703992, by rfl⟩ : syracuseStep 3605323 = 5407985) B5407985
theorem B4807097 : Blo 1897435 4807097 := bstep (se 2 (by rfl) ⟨1802661, by rfl⟩ : syracuseStep 4807097 = 3605323) B3605323
theorem B3204731 : Blo 1897435 3204731 := bstep (se 1 (by rfl) ⟨2403548, by rfl⟩ : syracuseStep 3204731 = 4807097) B4807097
theorem B2136487 : Blo 1897435 2136487 := bstep (se 1 (by rfl) ⟨1602365, by rfl⟩ : syracuseStep 2136487 = 3204731) B3204731
theorem B2848649 : Blo 1897435 2848649 := bstep (se 2 (by rfl) ⟨1068243, by rfl⟩ : syracuseStep 2848649 = 2136487) B2136487
theorem B1899099 : Blo 1897435 1899099 := bstep (se 1 (by rfl) ⟨1424324, by rfl⟩ : syracuseStep 1899099 = 2848649) B2848649
theorem B9614213 : Blo 1897435 9614213 := bbase (se 4 (by rfl) ⟨901332, by rfl⟩ : syracuseStep 9614213 = 1802665) (by norm_num)
theorem B6409475 : Blo 1897435 6409475 := bstep (se 1 (by rfl) ⟨4807106, by rfl⟩ : syracuseStep 6409475 = 9614213) B9614213
theorem B4272983 : Blo 1897435 4272983 := bstep (se 1 (by rfl) ⟨3204737, by rfl⟩ : syracuseStep 4272983 = 6409475) B6409475
theorem B2848655 : Blo 1897435 2848655 := bstep (se 1 (by rfl) ⟨2136491, by rfl⟩ : syracuseStep 2848655 = 4272983) B4272983
theorem B1899103 : Blo 1897435 1899103 := bstep (se 1 (by rfl) ⟨1424327, by rfl⟩ : syracuseStep 1899103 = 2848655) B2848655
theorem B2848661 : Blo 1897435 2848661 := bbase (se 6 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 2848661 = 133531) (by norm_num)
theorem B1899107 : Blo 1897435 1899107 := bstep (se 1 (by rfl) ⟨1424330, by rfl⟩ : syracuseStep 1899107 = 2848661) B2848661
theorem B9634373 : Blo 1897435 9634373 := bbase (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) (by norm_num)
theorem B6422915 : Blo 1897435 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B4281943 : Blo 1897435 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B5709257 : Blo 1897435 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B3806171 : Blo 1897435 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B2537447 : Blo 1897435 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B6766525 : Blo 1897435 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B9022033 : Blo 1897435 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B48117509 : Blo 1897435 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B32078339 : Blo 1897435 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B21385559 : Blo 1897435 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B57028157 : Blo 1897435 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B38018771 : Blo 1897435 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B25345847 : Blo 1897435 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B16897231 : Blo 1897435 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B90118565 : Blo 1897435 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B60079043 : Blo 1897435 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B160210781 : Blo 1897435 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B106807187 : Blo 1897435 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B71204791 : Blo 1897435 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B94939721 : Blo 1897435 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B63293147 : Blo 1897435 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B42195431 : Blo 1897435 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B112521149 : Blo 1897435 112521149 := bstep (se 3 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 112521149 = 42195431) B42195431
theorem B75014099 : Blo 1897435 75014099 := bstep (se 1 (by rfl) ⟨56260574, by rfl⟩ : syracuseStep 75014099 = 112521149) B112521149
theorem B50009399 : Blo 1897435 50009399 := bstep (se 1 (by rfl) ⟨37507049, by rfl⟩ : syracuseStep 50009399 = 75014099) B75014099
theorem B33339599 : Blo 1897435 33339599 := bstep (se 1 (by rfl) ⟨25004699, by rfl⟩ : syracuseStep 33339599 = 50009399) B50009399
theorem B22226399 : Blo 1897435 22226399 := bstep (se 1 (by rfl) ⟨16669799, by rfl⟩ : syracuseStep 22226399 = 33339599) B33339599
theorem B14817599 : Blo 1897435 14817599 := bstep (se 1 (by rfl) ⟨11113199, by rfl⟩ : syracuseStep 14817599 = 22226399) B22226399
theorem B9878399 : Blo 1897435 9878399 := bstep (se 1 (by rfl) ⟨7408799, by rfl⟩ : syracuseStep 9878399 = 14817599) B14817599
theorem B6585599 : Blo 1897435 6585599 := bstep (se 1 (by rfl) ⟨4939199, by rfl⟩ : syracuseStep 6585599 = 9878399) B9878399
theorem B4390399 : Blo 1897435 4390399 := bstep (se 1 (by rfl) ⟨3292799, by rfl⟩ : syracuseStep 4390399 = 6585599) B6585599
theorem B5853865 : Blo 1897435 5853865 := bstep (se 2 (by rfl) ⟨2195199, by rfl⟩ : syracuseStep 5853865 = 4390399) B4390399
theorem B7805153 : Blo 1897435 7805153 := bstep (se 2 (by rfl) ⟨2926932, by rfl⟩ : syracuseStep 7805153 = 5853865) B5853865
theorem B5203435 : Blo 1897435 5203435 := bstep (se 1 (by rfl) ⟨3902576, by rfl⟩ : syracuseStep 5203435 = 7805153) B7805153
theorem B6937913 : Blo 1897435 6937913 := bstep (se 2 (by rfl) ⟨2601717, by rfl⟩ : syracuseStep 6937913 = 5203435) B5203435
theorem B4625275 : Blo 1897435 4625275 := bstep (se 1 (by rfl) ⟨3468956, by rfl⟩ : syracuseStep 4625275 = 6937913) B6937913
theorem B6167033 : Blo 1897435 6167033 := bstep (se 2 (by rfl) ⟨2312637, by rfl⟩ : syracuseStep 6167033 = 4625275) B4625275
theorem B4111355 : Blo 1897435 4111355 := bstep (se 1 (by rfl) ⟨3083516, by rfl⟩ : syracuseStep 4111355 = 6167033) B6167033
theorem B10963613 : Blo 1897435 10963613 := bstep (se 3 (by rfl) ⟨2055677, by rfl⟩ : syracuseStep 10963613 = 4111355) B4111355
theorem B7309075 : Blo 1897435 7309075 := bstep (se 1 (by rfl) ⟨5481806, by rfl⟩ : syracuseStep 7309075 = 10963613) B10963613
theorem B9745433 : Blo 1897435 9745433 := bstep (se 2 (by rfl) ⟨3654537, by rfl⟩ : syracuseStep 9745433 = 7309075) B7309075
theorem B6496955 : Blo 1897435 6496955 := bstep (se 1 (by rfl) ⟨4872716, by rfl⟩ : syracuseStep 6496955 = 9745433) B9745433
theorem B4331303 : Blo 1897435 4331303 := bstep (se 1 (by rfl) ⟨3248477, by rfl⟩ : syracuseStep 4331303 = 6496955) B6496955
theorem B2887535 : Blo 1897435 2887535 := bstep (se 1 (by rfl) ⟨2165651, by rfl⟩ : syracuseStep 2887535 = 4331303) B4331303
theorem B7700093 : Blo 1897435 7700093 := bstep (se 3 (by rfl) ⟨1443767, by rfl⟩ : syracuseStep 7700093 = 2887535) B2887535
theorem B5133395 : Blo 1897435 5133395 := bstep (se 1 (by rfl) ⟨3850046, by rfl⟩ : syracuseStep 5133395 = 7700093) B7700093
theorem B3422263 : Blo 1897435 3422263 := bstep (se 1 (by rfl) ⟨2566697, by rfl⟩ : syracuseStep 3422263 = 5133395) B5133395
theorem B4563017 : Blo 1897435 4563017 := bstep (se 2 (by rfl) ⟨1711131, by rfl⟩ : syracuseStep 4563017 = 3422263) B3422263
theorem B3042011 : Blo 1897435 3042011 := bstep (se 1 (by rfl) ⟨2281508, by rfl⟩ : syracuseStep 3042011 = 4563017) B4563017
theorem B2028007 : Blo 1897435 2028007 := bstep (se 1 (by rfl) ⟨1521005, by rfl⟩ : syracuseStep 2028007 = 3042011) B3042011
theorem B10816037 : Blo 1897435 10816037 := bstep (se 4 (by rfl) ⟨1014003, by rfl⟩ : syracuseStep 10816037 = 2028007) B2028007
theorem B7210691 : Blo 1897435 7210691 := bstep (se 1 (by rfl) ⟨5408018, by rfl⟩ : syracuseStep 7210691 = 10816037) B10816037
theorem B4807127 : Blo 1897435 4807127 := bstep (se 1 (by rfl) ⟨3605345, by rfl⟩ : syracuseStep 4807127 = 7210691) B7210691
theorem B3204751 : Blo 1897435 3204751 := bstep (se 1 (by rfl) ⟨2403563, by rfl⟩ : syracuseStep 3204751 = 4807127) B4807127
theorem B4273001 : Blo 1897435 4273001 := bstep (se 2 (by rfl) ⟨1602375, by rfl⟩ : syracuseStep 4273001 = 3204751) B3204751
theorem B2848667 : Blo 1897435 2848667 := bstep (se 1 (by rfl) ⟨2136500, by rfl⟩ : syracuseStep 2848667 = 4273001) B4273001
theorem B1899111 : Blo 1897435 1899111 := bstep (se 1 (by rfl) ⟨1424333, by rfl⟩ : syracuseStep 1899111 = 2848667) B2848667
theorem B2136505 : Blo 1897435 2136505 := bbase (se 2 (by rfl) ⟨801189, by rfl⟩ : syracuseStep 2136505 = 1602379) (by norm_num)
theorem B2848673 : Blo 1897435 2848673 := bstep (se 2 (by rfl) ⟨1068252, by rfl⟩ : syracuseStep 2848673 = 2136505) B2136505
theorem B1899115 : Blo 1897435 1899115 := bstep (se 1 (by rfl) ⟨1424336, by rfl⟩ : syracuseStep 1899115 = 2848673) B2848673
theorem B14817653 : Blo 1897435 14817653 := bbase (se 5 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 14817653 = 1389155) (by norm_num)
theorem B9878435 : Blo 1897435 9878435 := bstep (se 1 (by rfl) ⟨7408826, by rfl⟩ : syracuseStep 9878435 = 14817653) B14817653
theorem B6585623 : Blo 1897435 6585623 := bstep (se 1 (by rfl) ⟨4939217, by rfl⟩ : syracuseStep 6585623 = 9878435) B9878435
theorem B4390415 : Blo 1897435 4390415 := bstep (se 1 (by rfl) ⟨3292811, by rfl⟩ : syracuseStep 4390415 = 6585623) B6585623
theorem B2926943 : Blo 1897435 2926943 := bstep (se 1 (by rfl) ⟨2195207, by rfl⟩ : syracuseStep 2926943 = 4390415) B4390415
theorem B1951295 : Blo 1897435 1951295 := bstep (se 1 (by rfl) ⟨1463471, by rfl⟩ : syracuseStep 1951295 = 2926943) B2926943
theorem B20813813 : Blo 1897435 20813813 := bstep (se 5 (by rfl) ⟨975647, by rfl⟩ : syracuseStep 20813813 = 1951295) B1951295
theorem B13875875 : Blo 1897435 13875875 := bstep (se 1 (by rfl) ⟨10406906, by rfl⟩ : syracuseStep 13875875 = 20813813) B20813813
theorem B9250583 : Blo 1897435 9250583 := bstep (se 1 (by rfl) ⟨6937937, by rfl⟩ : syracuseStep 9250583 = 13875875) B13875875
theorem B24668221 : Blo 1897435 24668221 := bstep (se 3 (by rfl) ⟨4625291, by rfl⟩ : syracuseStep 24668221 = 9250583) B9250583
theorem B32890961 : Blo 1897435 32890961 := bstep (se 2 (by rfl) ⟨12334110, by rfl⟩ : syracuseStep 32890961 = 24668221) B24668221
theorem B21927307 : Blo 1897435 21927307 := bstep (se 1 (by rfl) ⟨16445480, by rfl⟩ : syracuseStep 21927307 = 32890961) B32890961
theorem B29236409 : Blo 1897435 29236409 := bstep (se 2 (by rfl) ⟨10963653, by rfl⟩ : syracuseStep 29236409 = 21927307) B21927307
theorem B19490939 : Blo 1897435 19490939 := bstep (se 1 (by rfl) ⟨14618204, by rfl⟩ : syracuseStep 19490939 = 29236409) B29236409
theorem B12993959 : Blo 1897435 12993959 := bstep (se 1 (by rfl) ⟨9745469, by rfl⟩ : syracuseStep 12993959 = 19490939) B19490939
theorem B8662639 : Blo 1897435 8662639 := bstep (se 1 (by rfl) ⟨6496979, by rfl⟩ : syracuseStep 8662639 = 12993959) B12993959
theorem B11550185 : Blo 1897435 11550185 := bstep (se 2 (by rfl) ⟨4331319, by rfl⟩ : syracuseStep 11550185 = 8662639) B8662639
theorem B7700123 : Blo 1897435 7700123 := bstep (se 1 (by rfl) ⟨5775092, by rfl⟩ : syracuseStep 7700123 = 11550185) B11550185
theorem B20533661 : Blo 1897435 20533661 := bstep (se 3 (by rfl) ⟨3850061, by rfl⟩ : syracuseStep 20533661 = 7700123) B7700123
theorem B13689107 : Blo 1897435 13689107 := bstep (se 1 (by rfl) ⟨10266830, by rfl⟩ : syracuseStep 13689107 = 20533661) B20533661
theorem B9126071 : Blo 1897435 9126071 := bstep (se 1 (by rfl) ⟨6844553, by rfl⟩ : syracuseStep 9126071 = 13689107) B13689107
theorem B6084047 : Blo 1897435 6084047 := bstep (se 1 (by rfl) ⟨4563035, by rfl⟩ : syracuseStep 6084047 = 9126071) B9126071
theorem B4056031 : Blo 1897435 4056031 := bstep (se 1 (by rfl) ⟨3042023, by rfl⟩ : syracuseStep 4056031 = 6084047) B6084047
theorem B5408041 : Blo 1897435 5408041 := bstep (se 2 (by rfl) ⟨2028015, by rfl⟩ : syracuseStep 5408041 = 4056031) B4056031
theorem B7210721 : Blo 1897435 7210721 := bstep (se 2 (by rfl) ⟨2704020, by rfl⟩ : syracuseStep 7210721 = 5408041) B5408041
theorem B4807147 : Blo 1897435 4807147 := bstep (se 1 (by rfl) ⟨3605360, by rfl⟩ : syracuseStep 4807147 = 7210721) B7210721
theorem B6409529 : Blo 1897435 6409529 := bstep (se 2 (by rfl) ⟨2403573, by rfl⟩ : syracuseStep 6409529 = 4807147) B4807147
theorem B4273019 : Blo 1897435 4273019 := bstep (se 1 (by rfl) ⟨3204764, by rfl⟩ : syracuseStep 4273019 = 6409529) B6409529
theorem B2848679 : Blo 1897435 2848679 := bstep (se 1 (by rfl) ⟨2136509, by rfl⟩ : syracuseStep 2848679 = 4273019) B4273019
theorem B1899119 : Blo 1897435 1899119 := bstep (se 1 (by rfl) ⟨1424339, by rfl⟩ : syracuseStep 1899119 = 2848679) B2848679
theorem B2848685 : Blo 1897435 2848685 := bbase (se 3 (by rfl) ⟨534128, by rfl⟩ : syracuseStep 2848685 = 1068257) (by norm_num)
theorem B1899123 : Blo 1897435 1899123 := bstep (se 1 (by rfl) ⟨1424342, by rfl⟩ : syracuseStep 1899123 = 2848685) B2848685
theorem B4273037 : Blo 1897435 4273037 := bbase (se 3 (by rfl) ⟨801194, by rfl⟩ : syracuseStep 4273037 = 1602389) (by norm_num)
theorem B2848691 : Blo 1897435 2848691 := bstep (se 1 (by rfl) ⟨2136518, by rfl⟩ : syracuseStep 2848691 = 4273037) B4273037
theorem B1899127 : Blo 1897435 1899127 := bstep (se 1 (by rfl) ⟨1424345, by rfl⟩ : syracuseStep 1899127 = 2848691) B2848691
theorem B2403589 : Blo 1897435 2403589 := bbase (se 4 (by rfl) ⟨225336, by rfl⟩ : syracuseStep 2403589 = 450673) (by norm_num)
theorem B3204785 : Blo 1897435 3204785 := bstep (se 2 (by rfl) ⟨1201794, by rfl⟩ : syracuseStep 3204785 = 2403589) B2403589
theorem B2136523 : Blo 1897435 2136523 := bstep (se 1 (by rfl) ⟨1602392, by rfl⟩ : syracuseStep 2136523 = 3204785) B3204785
theorem B2848697 : Blo 1897435 2848697 := bstep (se 2 (by rfl) ⟨1068261, by rfl⟩ : syracuseStep 2848697 = 2136523) B2136523
theorem B1899131 : Blo 1897435 1899131 := bstep (se 1 (by rfl) ⟨1424348, by rfl⟩ : syracuseStep 1899131 = 2848697) B2848697
theorem B4331357 : Blo 1897435 4331357 := bbase (se 3 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 4331357 = 1624259) (by norm_num)
theorem B2887571 : Blo 1897435 2887571 := bstep (se 1 (by rfl) ⟨2165678, by rfl⟩ : syracuseStep 2887571 = 4331357) B4331357
theorem B1925047 : Blo 1897435 1925047 := bstep (se 1 (by rfl) ⟨1443785, by rfl⟩ : syracuseStep 1925047 = 2887571) B2887571
theorem B2566729 : Blo 1897435 2566729 := bstep (se 2 (by rfl) ⟨962523, by rfl⟩ : syracuseStep 2566729 = 1925047) B1925047
theorem B3422305 : Blo 1897435 3422305 := bstep (se 2 (by rfl) ⟨1283364, by rfl⟩ : syracuseStep 3422305 = 2566729) B2566729
theorem B4563073 : Blo 1897435 4563073 := bstep (se 2 (by rfl) ⟨1711152, by rfl⟩ : syracuseStep 4563073 = 3422305) B3422305
theorem B24336389 : Blo 1897435 24336389 := bstep (se 4 (by rfl) ⟨2281536, by rfl⟩ : syracuseStep 24336389 = 4563073) B4563073
theorem B16224259 : Blo 1897435 16224259 := bstep (se 1 (by rfl) ⟨12168194, by rfl⟩ : syracuseStep 16224259 = 24336389) B24336389
theorem B21632345 : Blo 1897435 21632345 := bstep (se 2 (by rfl) ⟨8112129, by rfl⟩ : syracuseStep 21632345 = 16224259) B16224259
theorem B14421563 : Blo 1897435 14421563 := bstep (se 1 (by rfl) ⟨10816172, by rfl⟩ : syracuseStep 14421563 = 21632345) B21632345
theorem B9614375 : Blo 1897435 9614375 := bstep (se 1 (by rfl) ⟨7210781, by rfl⟩ : syracuseStep 9614375 = 14421563) B14421563
theorem B6409583 : Blo 1897435 6409583 := bstep (se 1 (by rfl) ⟨4807187, by rfl⟩ : syracuseStep 6409583 = 9614375) B9614375
theorem B4273055 : Blo 1897435 4273055 := bstep (se 1 (by rfl) ⟨3204791, by rfl⟩ : syracuseStep 4273055 = 6409583) B6409583
theorem B2848703 : Blo 1897435 2848703 := bstep (se 1 (by rfl) ⟨2136527, by rfl⟩ : syracuseStep 2848703 = 4273055) B4273055
theorem B1899135 : Blo 1897435 1899135 := bstep (se 1 (by rfl) ⟨1424351, by rfl⟩ : syracuseStep 1899135 = 2848703) B2848703
theorem B2848709 : Blo 1897435 2848709 := bbase (se 4 (by rfl) ⟨267066, by rfl⟩ : syracuseStep 2848709 = 534133) (by norm_num)
theorem B1899139 : Blo 1897435 1899139 := bstep (se 1 (by rfl) ⟨1424354, by rfl⟩ : syracuseStep 1899139 = 2848709) B2848709
theorem B3204805 : Blo 1897435 3204805 := bbase (se 4 (by rfl) ⟨300450, by rfl⟩ : syracuseStep 3204805 = 600901) (by norm_num)
theorem B4273073 : Blo 1897435 4273073 := bstep (se 2 (by rfl) ⟨1602402, by rfl⟩ : syracuseStep 4273073 = 3204805) B3204805
theorem B2848715 : Blo 1897435 2848715 := bstep (se 1 (by rfl) ⟨2136536, by rfl⟩ : syracuseStep 2848715 = 4273073) B4273073
theorem B1899143 : Blo 1897435 1899143 := bstep (se 1 (by rfl) ⟨1424357, by rfl⟩ : syracuseStep 1899143 = 2848715) B2848715
theorem B2136541 : Blo 1897435 2136541 := bbase (se 3 (by rfl) ⟨400601, by rfl⟩ : syracuseStep 2136541 = 801203) (by norm_num)
theorem B2848721 : Blo 1897435 2848721 := bstep (se 2 (by rfl) ⟨1068270, by rfl⟩ : syracuseStep 2848721 = 2136541) B2136541
theorem B1899147 : Blo 1897435 1899147 := bstep (se 1 (by rfl) ⟨1424360, by rfl⟩ : syracuseStep 1899147 = 2848721) B2848721
theorem B6409637 : Blo 1897435 6409637 := bbase (se 4 (by rfl) ⟨600903, by rfl⟩ : syracuseStep 6409637 = 1201807) (by norm_num)
theorem B4273091 : Blo 1897435 4273091 := bstep (se 1 (by rfl) ⟨3204818, by rfl⟩ : syracuseStep 4273091 = 6409637) B6409637
theorem B2848727 : Blo 1897435 2848727 := bstep (se 1 (by rfl) ⟨2136545, by rfl⟩ : syracuseStep 2848727 = 4273091) B4273091
theorem B1899151 : Blo 1897435 1899151 := bstep (se 1 (by rfl) ⟨1424363, by rfl⟩ : syracuseStep 1899151 = 2848727) B2848727
theorem B2848733 : Blo 1897435 2848733 := bbase (se 3 (by rfl) ⟨534137, by rfl⟩ : syracuseStep 2848733 = 1068275) (by norm_num)
theorem B1899155 : Blo 1897435 1899155 := bstep (se 1 (by rfl) ⟨1424366, by rfl⟩ : syracuseStep 1899155 = 2848733) B2848733
theorem B4273109 : Blo 1897435 4273109 := bbase (se 7 (by rfl) ⟨50075, by rfl⟩ : syracuseStep 4273109 = 100151) (by norm_num)
theorem B2848739 : Blo 1897435 2848739 := bstep (se 1 (by rfl) ⟨2136554, by rfl⟩ : syracuseStep 2848739 = 4273109) B4273109
theorem B1899159 : Blo 1897435 1899159 := bstep (se 1 (by rfl) ⟨1424369, by rfl⟩ : syracuseStep 1899159 = 2848739) B2848739
theorem B8222933 : Blo 1897435 8222933 := bbase (se 7 (by rfl) ⟨96362, by rfl⟩ : syracuseStep 8222933 = 192725) (by norm_num)
theorem B5481955 : Blo 1897435 5481955 := bstep (se 1 (by rfl) ⟨4111466, by rfl⟩ : syracuseStep 5481955 = 8222933) B8222933
theorem B7309273 : Blo 1897435 7309273 := bstep (se 2 (by rfl) ⟨2740977, by rfl⟩ : syracuseStep 7309273 = 5481955) B5481955
theorem B9745697 : Blo 1897435 9745697 := bstep (se 2 (by rfl) ⟨3654636, by rfl⟩ : syracuseStep 9745697 = 7309273) B7309273
theorem B6497131 : Blo 1897435 6497131 := bstep (se 1 (by rfl) ⟨4872848, by rfl⟩ : syracuseStep 6497131 = 9745697) B9745697
theorem B8662841 : Blo 1897435 8662841 := bstep (se 2 (by rfl) ⟨3248565, by rfl⟩ : syracuseStep 8662841 = 6497131) B6497131
theorem B5775227 : Blo 1897435 5775227 := bstep (se 1 (by rfl) ⟨4331420, by rfl⟩ : syracuseStep 5775227 = 8662841) B8662841
theorem B3850151 : Blo 1897435 3850151 := bstep (se 1 (by rfl) ⟨2887613, by rfl⟩ : syracuseStep 3850151 = 5775227) B5775227
theorem B10267069 : Blo 1897435 10267069 := bstep (se 3 (by rfl) ⟨1925075, by rfl⟩ : syracuseStep 10267069 = 3850151) B3850151
theorem B13689425 : Blo 1897435 13689425 := bstep (se 2 (by rfl) ⟨5133534, by rfl⟩ : syracuseStep 13689425 = 10267069) B10267069
theorem B9126283 : Blo 1897435 9126283 := bstep (se 1 (by rfl) ⟨6844712, by rfl⟩ : syracuseStep 9126283 = 13689425) B13689425
theorem B12168377 : Blo 1897435 12168377 := bstep (se 2 (by rfl) ⟨4563141, by rfl⟩ : syracuseStep 12168377 = 9126283) B9126283
theorem B8112251 : Blo 1897435 8112251 := bstep (se 1 (by rfl) ⟨6084188, by rfl⟩ : syracuseStep 8112251 = 12168377) B12168377
theorem B5408167 : Blo 1897435 5408167 := bstep (se 1 (by rfl) ⟨4056125, by rfl⟩ : syracuseStep 5408167 = 8112251) B8112251
theorem B7210889 : Blo 1897435 7210889 := bstep (se 2 (by rfl) ⟨2704083, by rfl⟩ : syracuseStep 7210889 = 5408167) B5408167
theorem B4807259 : Blo 1897435 4807259 := bstep (se 1 (by rfl) ⟨3605444, by rfl⟩ : syracuseStep 4807259 = 7210889) B7210889
theorem B3204839 : Blo 1897435 3204839 := bstep (se 1 (by rfl) ⟨2403629, by rfl⟩ : syracuseStep 3204839 = 4807259) B4807259
theorem B2136559 : Blo 1897435 2136559 := bstep (se 1 (by rfl) ⟨1602419, by rfl⟩ : syracuseStep 2136559 = 3204839) B3204839
theorem B2848745 : Blo 1897435 2848745 := bstep (se 2 (by rfl) ⟨1068279, by rfl⟩ : syracuseStep 2848745 = 2136559) B2136559
theorem B1899163 : Blo 1897435 1899163 := bstep (se 1 (by rfl) ⟨1424372, by rfl⟩ : syracuseStep 1899163 = 2848745) B2848745
theorem B16224533 : Blo 1897435 16224533 := bbase (se 6 (by rfl) ⟨380262, by rfl⟩ : syracuseStep 16224533 = 760525) (by norm_num)
theorem B10816355 : Blo 1897435 10816355 := bstep (se 1 (by rfl) ⟨8112266, by rfl⟩ : syracuseStep 10816355 = 16224533) B16224533
theorem B7210903 : Blo 1897435 7210903 := bstep (se 1 (by rfl) ⟨5408177, by rfl⟩ : syracuseStep 7210903 = 10816355) B10816355
theorem B9614537 : Blo 1897435 9614537 := bstep (se 2 (by rfl) ⟨3605451, by rfl⟩ : syracuseStep 9614537 = 7210903) B7210903
theorem B6409691 : Blo 1897435 6409691 := bstep (se 1 (by rfl) ⟨4807268, by rfl⟩ : syracuseStep 6409691 = 9614537) B9614537
theorem B4273127 : Blo 1897435 4273127 := bstep (se 1 (by rfl) ⟨3204845, by rfl⟩ : syracuseStep 4273127 = 6409691) B6409691
theorem B2848751 : Blo 1897435 2848751 := bstep (se 1 (by rfl) ⟨2136563, by rfl⟩ : syracuseStep 2848751 = 4273127) B4273127
theorem B1899167 : Blo 1897435 1899167 := bstep (se 1 (by rfl) ⟨1424375, by rfl⟩ : syracuseStep 1899167 = 2848751) B2848751
theorem B2848757 : Blo 1897435 2848757 := bbase (se 5 (by rfl) ⟨133535, by rfl⟩ : syracuseStep 2848757 = 267071) (by norm_num)
theorem B1899171 : Blo 1897435 1899171 := bstep (se 1 (by rfl) ⟨1424378, by rfl⟩ : syracuseStep 1899171 = 2848757) B2848757
theorem B9126341 : Blo 1897435 9126341 := bbase (se 4 (by rfl) ⟨855594, by rfl⟩ : syracuseStep 9126341 = 1711189) (by norm_num)
theorem B6084227 : Blo 1897435 6084227 := bstep (se 1 (by rfl) ⟨4563170, by rfl⟩ : syracuseStep 6084227 = 9126341) B9126341
theorem B4056151 : Blo 1897435 4056151 := bstep (se 1 (by rfl) ⟨3042113, by rfl⟩ : syracuseStep 4056151 = 6084227) B6084227
theorem B5408201 : Blo 1897435 5408201 := bstep (se 2 (by rfl) ⟨2028075, by rfl⟩ : syracuseStep 5408201 = 4056151) B4056151
theorem B3605467 : Blo 1897435 3605467 := bstep (se 1 (by rfl) ⟨2704100, by rfl⟩ : syracuseStep 3605467 = 5408201) B5408201
theorem B4807289 : Blo 1897435 4807289 := bstep (se 2 (by rfl) ⟨1802733, by rfl⟩ : syracuseStep 4807289 = 3605467) B3605467
theorem B3204859 : Blo 1897435 3204859 := bstep (se 1 (by rfl) ⟨2403644, by rfl⟩ : syracuseStep 3204859 = 4807289) B4807289
theorem B4273145 : Blo 1897435 4273145 := bstep (se 2 (by rfl) ⟨1602429, by rfl⟩ : syracuseStep 4273145 = 3204859) B3204859
theorem B2848763 : Blo 1897435 2848763 := bstep (se 1 (by rfl) ⟨2136572, by rfl⟩ : syracuseStep 2848763 = 4273145) B4273145
theorem B1899175 : Blo 1897435 1899175 := bstep (se 1 (by rfl) ⟨1424381, by rfl⟩ : syracuseStep 1899175 = 2848763) B2848763
theorem B2136577 : Blo 1897435 2136577 := bbase (se 2 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 2136577 = 1602433) (by norm_num)
theorem B2848769 : Blo 1897435 2848769 := bstep (se 2 (by rfl) ⟨1068288, by rfl⟩ : syracuseStep 2848769 = 2136577) B2136577
theorem B1899179 : Blo 1897435 1899179 := bstep (se 1 (by rfl) ⟨1424384, by rfl⟩ : syracuseStep 1899179 = 2848769) B2848769
theorem B4807309 : Blo 1897435 4807309 := bbase (se 3 (by rfl) ⟨901370, by rfl⟩ : syracuseStep 4807309 = 1802741) (by norm_num)
theorem B6409745 : Blo 1897435 6409745 := bstep (se 2 (by rfl) ⟨2403654, by rfl⟩ : syracuseStep 6409745 = 4807309) B4807309
theorem B4273163 : Blo 1897435 4273163 := bstep (se 1 (by rfl) ⟨3204872, by rfl⟩ : syracuseStep 4273163 = 6409745) B6409745
theorem B2848775 : Blo 1897435 2848775 := bstep (se 1 (by rfl) ⟨2136581, by rfl⟩ : syracuseStep 2848775 = 4273163) B4273163
theorem B1899183 : Blo 1897435 1899183 := bstep (se 1 (by rfl) ⟨1424387, by rfl⟩ : syracuseStep 1899183 = 2848775) B2848775
theorem B2848781 : Blo 1897435 2848781 := bbase (se 3 (by rfl) ⟨534146, by rfl⟩ : syracuseStep 2848781 = 1068293) (by norm_num)
theorem B1899187 : Blo 1897435 1899187 := bstep (se 1 (by rfl) ⟨1424390, by rfl⟩ : syracuseStep 1899187 = 2848781) B2848781
theorem B4273181 : Blo 1897435 4273181 := bbase (se 3 (by rfl) ⟨801221, by rfl⟩ : syracuseStep 4273181 = 1602443) (by norm_num)
theorem B2848787 : Blo 1897435 2848787 := bstep (se 1 (by rfl) ⟨2136590, by rfl⟩ : syracuseStep 2848787 = 4273181) B4273181
theorem B1899191 : Blo 1897435 1899191 := bstep (se 1 (by rfl) ⟨1424393, by rfl⟩ : syracuseStep 1899191 = 2848787) B2848787
theorem B3204893 : Blo 1897435 3204893 := bbase (se 3 (by rfl) ⟨600917, by rfl⟩ : syracuseStep 3204893 = 1201835) (by norm_num)
theorem B2136595 : Blo 1897435 2136595 := bstep (se 1 (by rfl) ⟨1602446, by rfl⟩ : syracuseStep 2136595 = 3204893) B3204893
theorem B2848793 : Blo 1897435 2848793 := bstep (se 2 (by rfl) ⟨1068297, by rfl⟩ : syracuseStep 2848793 = 2136595) B2136595
theorem B1899195 : Blo 1897435 1899195 := bstep (se 1 (by rfl) ⟨1424396, by rfl⟩ : syracuseStep 1899195 = 2848793) B2848793
theorem B5854133 : Blo 1897435 5854133 := bbase (se 5 (by rfl) ⟨274412, by rfl⟩ : syracuseStep 5854133 = 548825) (by norm_num)
theorem B3902755 : Blo 1897435 3902755 := bstep (se 1 (by rfl) ⟨2927066, by rfl⟩ : syracuseStep 3902755 = 5854133) B5854133
theorem B5203673 : Blo 1897435 5203673 := bstep (se 2 (by rfl) ⟨1951377, by rfl⟩ : syracuseStep 5203673 = 3902755) B3902755
theorem B3469115 : Blo 1897435 3469115 := bstep (se 1 (by rfl) ⟨2601836, by rfl⟩ : syracuseStep 3469115 = 5203673) B5203673
theorem B9250973 : Blo 1897435 9250973 := bstep (se 3 (by rfl) ⟨1734557, by rfl⟩ : syracuseStep 9250973 = 3469115) B3469115
theorem B6167315 : Blo 1897435 6167315 := bstep (se 1 (by rfl) ⟨4625486, by rfl⟩ : syracuseStep 6167315 = 9250973) B9250973
theorem B4111543 : Blo 1897435 4111543 := bstep (se 1 (by rfl) ⟨3083657, by rfl⟩ : syracuseStep 4111543 = 6167315) B6167315
theorem B21928229 : Blo 1897435 21928229 := bstep (se 4 (by rfl) ⟨2055771, by rfl⟩ : syracuseStep 21928229 = 4111543) B4111543
theorem B14618819 : Blo 1897435 14618819 := bstep (se 1 (by rfl) ⟨10964114, by rfl⟩ : syracuseStep 14618819 = 21928229) B21928229
theorem B38983517 : Blo 1897435 38983517 := bstep (se 3 (by rfl) ⟨7309409, by rfl⟩ : syracuseStep 38983517 = 14618819) B14618819
theorem B25989011 : Blo 1897435 25989011 := bstep (se 1 (by rfl) ⟨19491758, by rfl⟩ : syracuseStep 25989011 = 38983517) B38983517
theorem B17326007 : Blo 1897435 17326007 := bstep (se 1 (by rfl) ⟨12994505, by rfl⟩ : syracuseStep 17326007 = 25989011) B25989011
theorem B11550671 : Blo 1897435 11550671 := bstep (se 1 (by rfl) ⟨8663003, by rfl⟩ : syracuseStep 11550671 = 17326007) B17326007
theorem B7700447 : Blo 1897435 7700447 := bstep (se 1 (by rfl) ⟨5775335, by rfl⟩ : syracuseStep 7700447 = 11550671) B11550671
theorem B5133631 : Blo 1897435 5133631 := bstep (se 1 (by rfl) ⟨3850223, by rfl⟩ : syracuseStep 5133631 = 7700447) B7700447
theorem B6844841 : Blo 1897435 6844841 := bstep (se 2 (by rfl) ⟨2566815, by rfl⟩ : syracuseStep 6844841 = 5133631) B5133631
theorem B4563227 : Blo 1897435 4563227 := bstep (se 1 (by rfl) ⟨3422420, by rfl⟩ : syracuseStep 4563227 = 6844841) B6844841
theorem B12168605 : Blo 1897435 12168605 := bstep (se 3 (by rfl) ⟨2281613, by rfl⟩ : syracuseStep 12168605 = 4563227) B4563227
theorem B8112403 : Blo 1897435 8112403 := bstep (se 1 (by rfl) ⟨6084302, by rfl⟩ : syracuseStep 8112403 = 12168605) B12168605
theorem B10816537 : Blo 1897435 10816537 := bstep (se 2 (by rfl) ⟨4056201, by rfl⟩ : syracuseStep 10816537 = 8112403) B8112403
theorem B14422049 : Blo 1897435 14422049 := bstep (se 2 (by rfl) ⟨5408268, by rfl⟩ : syracuseStep 14422049 = 10816537) B10816537
theorem B9614699 : Blo 1897435 9614699 := bstep (se 1 (by rfl) ⟨7211024, by rfl⟩ : syracuseStep 9614699 = 14422049) B14422049
theorem B6409799 : Blo 1897435 6409799 := bstep (se 1 (by rfl) ⟨4807349, by rfl⟩ : syracuseStep 6409799 = 9614699) B9614699
theorem B4273199 : Blo 1897435 4273199 := bstep (se 1 (by rfl) ⟨3204899, by rfl⟩ : syracuseStep 4273199 = 6409799) B6409799
theorem B2848799 : Blo 1897435 2848799 := bstep (se 1 (by rfl) ⟨2136599, by rfl⟩ : syracuseStep 2848799 = 4273199) B4273199
theorem B1899199 : Blo 1897435 1899199 := bstep (se 1 (by rfl) ⟨1424399, by rfl⟩ : syracuseStep 1899199 = 2848799) B2848799
theorem B2848805 : Blo 1897435 2848805 := bbase (se 4 (by rfl) ⟨267075, by rfl⟩ : syracuseStep 2848805 = 534151) (by norm_num)
theorem B1899203 : Blo 1897435 1899203 := bstep (se 1 (by rfl) ⟨1424402, by rfl⟩ : syracuseStep 1899203 = 2848805) B2848805
theorem B2403685 : Blo 1897435 2403685 := bbase (se 4 (by rfl) ⟨225345, by rfl⟩ : syracuseStep 2403685 = 450691) (by norm_num)
theorem B3204913 : Blo 1897435 3204913 := bstep (se 2 (by rfl) ⟨1201842, by rfl⟩ : syracuseStep 3204913 = 2403685) B2403685
theorem B4273217 : Blo 1897435 4273217 := bstep (se 2 (by rfl) ⟨1602456, by rfl⟩ : syracuseStep 4273217 = 3204913) B3204913
theorem B2848811 : Blo 1897435 2848811 := bstep (se 1 (by rfl) ⟨2136608, by rfl⟩ : syracuseStep 2848811 = 4273217) B4273217
theorem B1899207 : Blo 1897435 1899207 := bstep (se 1 (by rfl) ⟨1424405, by rfl⟩ : syracuseStep 1899207 = 2848811) B2848811
theorem B2136613 : Blo 1897435 2136613 := bbase (se 4 (by rfl) ⟨200307, by rfl⟩ : syracuseStep 2136613 = 400615) (by norm_num)
theorem B2848817 : Blo 1897435 2848817 := bstep (se 2 (by rfl) ⟨1068306, by rfl⟩ : syracuseStep 2848817 = 2136613) B2136613
theorem B1899211 : Blo 1897435 1899211 := bstep (se 1 (by rfl) ⟨1424408, by rfl⟩ : syracuseStep 1899211 = 2848817) B2848817
theorem B9126533 : Blo 1897435 9126533 := bbase (se 4 (by rfl) ⟨855612, by rfl⟩ : syracuseStep 9126533 = 1711225) (by norm_num)
theorem B6084355 : Blo 1897435 6084355 := bstep (se 1 (by rfl) ⟨4563266, by rfl⟩ : syracuseStep 6084355 = 9126533) B9126533
theorem B8112473 : Blo 1897435 8112473 := bstep (se 2 (by rfl) ⟨3042177, by rfl⟩ : syracuseStep 8112473 = 6084355) B6084355
theorem B5408315 : Blo 1897435 5408315 := bstep (se 1 (by rfl) ⟨4056236, by rfl⟩ : syracuseStep 5408315 = 8112473) B8112473
theorem B3605543 : Blo 1897435 3605543 := bstep (se 1 (by rfl) ⟨2704157, by rfl⟩ : syracuseStep 3605543 = 5408315) B5408315
theorem B2403695 : Blo 1897435 2403695 := bstep (se 1 (by rfl) ⟨1802771, by rfl⟩ : syracuseStep 2403695 = 3605543) B3605543
theorem B6409853 : Blo 1897435 6409853 := bstep (se 3 (by rfl) ⟨1201847, by rfl⟩ : syracuseStep 6409853 = 2403695) B2403695
theorem B4273235 : Blo 1897435 4273235 := bstep (se 1 (by rfl) ⟨3204926, by rfl⟩ : syracuseStep 4273235 = 6409853) B6409853
theorem B2848823 : Blo 1897435 2848823 := bstep (se 1 (by rfl) ⟨2136617, by rfl⟩ : syracuseStep 2848823 = 4273235) B4273235
theorem B1899215 : Blo 1897435 1899215 := bstep (se 1 (by rfl) ⟨1424411, by rfl⟩ : syracuseStep 1899215 = 2848823) B2848823
theorem B2848829 : Blo 1897435 2848829 := bbase (se 3 (by rfl) ⟨534155, by rfl⟩ : syracuseStep 2848829 = 1068311) (by norm_num)
theorem B1899219 : Blo 1897435 1899219 := bstep (se 1 (by rfl) ⟨1424414, by rfl⟩ : syracuseStep 1899219 = 2848829) B2848829
theorem B4273253 : Blo 1897435 4273253 := bbase (se 4 (by rfl) ⟨400617, by rfl⟩ : syracuseStep 4273253 = 801235) (by norm_num)
theorem B2848835 : Blo 1897435 2848835 := bstep (se 1 (by rfl) ⟨2136626, by rfl⟩ : syracuseStep 2848835 = 4273253) B4273253
theorem B1899223 : Blo 1897435 1899223 := bstep (se 1 (by rfl) ⟨1424417, by rfl⟩ : syracuseStep 1899223 = 2848835) B2848835
theorem B4807421 : Blo 1897435 4807421 := bbase (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) (by norm_num)
theorem B3204947 : Blo 1897435 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B2136631 : Blo 1897435 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B2848841 : Blo 1897435 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B1899227 : Blo 1897435 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B3605573 : Blo 1897435 3605573 := bbase (se 4 (by rfl) ⟨338022, by rfl⟩ : syracuseStep 3605573 = 676045) (by norm_num)
theorem B9614861 : Blo 1897435 9614861 := bstep (se 3 (by rfl) ⟨1802786, by rfl⟩ : syracuseStep 9614861 = 3605573) B3605573
theorem B6409907 : Blo 1897435 6409907 := bstep (se 1 (by rfl) ⟨4807430, by rfl⟩ : syracuseStep 6409907 = 9614861) B9614861
theorem B4273271 : Blo 1897435 4273271 := bstep (se 1 (by rfl) ⟨3204953, by rfl⟩ : syracuseStep 4273271 = 6409907) B6409907
theorem B2848847 : Blo 1897435 2848847 := bstep (se 1 (by rfl) ⟨2136635, by rfl⟩ : syracuseStep 2848847 = 4273271) B4273271
theorem B1899231 : Blo 1897435 1899231 := bstep (se 1 (by rfl) ⟨1424423, by rfl⟩ : syracuseStep 1899231 = 2848847) B2848847
theorem B2848853 : Blo 1897435 2848853 := bbase (se 8 (by rfl) ⟨16692, by rfl⟩ : syracuseStep 2848853 = 33385) (by norm_num)
theorem B1899235 : Blo 1897435 1899235 := bstep (se 1 (by rfl) ⟨1424426, by rfl⟩ : syracuseStep 1899235 = 2848853) B2848853
theorem B2286433 : Blo 1897435 2286433 := bbase (se 2 (by rfl) ⟨857412, by rfl⟩ : syracuseStep 2286433 = 1714825) (by norm_num)
theorem B3048577 : Blo 1897435 3048577 := bstep (se 2 (by rfl) ⟨1143216, by rfl⟩ : syracuseStep 3048577 = 2286433) B2286433
theorem B16259077 : Blo 1897435 16259077 := bstep (se 4 (by rfl) ⟨1524288, by rfl⟩ : syracuseStep 16259077 = 3048577) B3048577
theorem B21678769 : Blo 1897435 21678769 := bstep (se 2 (by rfl) ⟨8129538, by rfl⟩ : syracuseStep 21678769 = 16259077) B16259077
theorem B28905025 : Blo 1897435 28905025 := bstep (se 2 (by rfl) ⟨10839384, by rfl⟩ : syracuseStep 28905025 = 21678769) B21678769
theorem B38540033 : Blo 1897435 38540033 := bstep (se 2 (by rfl) ⟨14452512, by rfl⟩ : syracuseStep 38540033 = 28905025) B28905025
theorem B25693355 : Blo 1897435 25693355 := bstep (se 1 (by rfl) ⟨19270016, by rfl⟩ : syracuseStep 25693355 = 38540033) B38540033
theorem B17128903 : Blo 1897435 17128903 := bstep (se 1 (by rfl) ⟨12846677, by rfl⟩ : syracuseStep 17128903 = 25693355) B25693355
theorem B22838537 : Blo 1897435 22838537 := bstep (se 2 (by rfl) ⟨8564451, by rfl⟩ : syracuseStep 22838537 = 17128903) B17128903
theorem B15225691 : Blo 1897435 15225691 := bstep (se 1 (by rfl) ⟨11419268, by rfl⟩ : syracuseStep 15225691 = 22838537) B22838537
theorem B20300921 : Blo 1897435 20300921 := bstep (se 2 (by rfl) ⟨7612845, by rfl⟩ : syracuseStep 20300921 = 15225691) B15225691
theorem B13533947 : Blo 1897435 13533947 := bstep (se 1 (by rfl) ⟨10150460, by rfl⟩ : syracuseStep 13533947 = 20300921) B20300921
theorem B9022631 : Blo 1897435 9022631 := bstep (se 1 (by rfl) ⟨6766973, by rfl⟩ : syracuseStep 9022631 = 13533947) B13533947
theorem B24060349 : Blo 1897435 24060349 := bstep (se 3 (by rfl) ⟨4511315, by rfl⟩ : syracuseStep 24060349 = 9022631) B9022631
theorem B32080465 : Blo 1897435 32080465 := bstep (se 2 (by rfl) ⟨12030174, by rfl⟩ : syracuseStep 32080465 = 24060349) B24060349
theorem B171095813 : Blo 1897435 171095813 := bstep (se 4 (by rfl) ⟨16040232, by rfl⟩ : syracuseStep 171095813 = 32080465) B32080465
theorem B114063875 : Blo 1897435 114063875 := bstep (se 1 (by rfl) ⟨85547906, by rfl⟩ : syracuseStep 114063875 = 171095813) B171095813
theorem B76042583 : Blo 1897435 76042583 := bstep (se 1 (by rfl) ⟨57031937, by rfl⟩ : syracuseStep 76042583 = 114063875) B114063875
theorem B50695055 : Blo 1897435 50695055 := bstep (se 1 (by rfl) ⟨38021291, by rfl⟩ : syracuseStep 50695055 = 76042583) B76042583
theorem B33796703 : Blo 1897435 33796703 := bstep (se 1 (by rfl) ⟨25347527, by rfl⟩ : syracuseStep 33796703 = 50695055) B50695055
theorem B22531135 : Blo 1897435 22531135 := bstep (se 1 (by rfl) ⟨16898351, by rfl⟩ : syracuseStep 22531135 = 33796703) B33796703
theorem B30041513 : Blo 1897435 30041513 := bstep (se 2 (by rfl) ⟨11265567, by rfl⟩ : syracuseStep 30041513 = 22531135) B22531135
theorem B20027675 : Blo 1897435 20027675 := bstep (se 1 (by rfl) ⟨15020756, by rfl⟩ : syracuseStep 20027675 = 30041513) B30041513
theorem B13351783 : Blo 1897435 13351783 := bstep (se 1 (by rfl) ⟨10013837, by rfl⟩ : syracuseStep 13351783 = 20027675) B20027675
theorem B17802377 : Blo 1897435 17802377 := bstep (se 2 (by rfl) ⟨6675891, by rfl⟩ : syracuseStep 17802377 = 13351783) B13351783
theorem B11868251 : Blo 1897435 11868251 := bstep (se 1 (by rfl) ⟨8901188, by rfl⟩ : syracuseStep 11868251 = 17802377) B17802377
theorem B126594677 : Blo 1897435 126594677 := bstep (se 5 (by rfl) ⟨5934125, by rfl⟩ : syracuseStep 126594677 = 11868251) B11868251
theorem B84396451 : Blo 1897435 84396451 := bstep (se 1 (by rfl) ⟨63297338, by rfl⟩ : syracuseStep 84396451 = 126594677) B126594677
theorem B112528601 : Blo 1897435 112528601 := bstep (se 2 (by rfl) ⟨42198225, by rfl⟩ : syracuseStep 112528601 = 84396451) B84396451
theorem B75019067 : Blo 1897435 75019067 := bstep (se 1 (by rfl) ⟨56264300, by rfl⟩ : syracuseStep 75019067 = 112528601) B112528601
theorem B50012711 : Blo 1897435 50012711 := bstep (se 1 (by rfl) ⟨37509533, by rfl⟩ : syracuseStep 50012711 = 75019067) B75019067
theorem B33341807 : Blo 1897435 33341807 := bstep (se 1 (by rfl) ⟨25006355, by rfl⟩ : syracuseStep 33341807 = 50012711) B50012711
theorem B22227871 : Blo 1897435 22227871 := bstep (se 1 (by rfl) ⟨16670903, by rfl⟩ : syracuseStep 22227871 = 33341807) B33341807
theorem B29637161 : Blo 1897435 29637161 := bstep (se 2 (by rfl) ⟨11113935, by rfl⟩ : syracuseStep 29637161 = 22227871) B22227871
theorem B19758107 : Blo 1897435 19758107 := bstep (se 1 (by rfl) ⟨14818580, by rfl⟩ : syracuseStep 19758107 = 29637161) B29637161
theorem B13172071 : Blo 1897435 13172071 := bstep (se 1 (by rfl) ⟨9879053, by rfl⟩ : syracuseStep 13172071 = 19758107) B19758107
theorem B17562761 : Blo 1897435 17562761 := bstep (se 2 (by rfl) ⟨6586035, by rfl⟩ : syracuseStep 17562761 = 13172071) B13172071
theorem B11708507 : Blo 1897435 11708507 := bstep (se 1 (by rfl) ⟨8781380, by rfl⟩ : syracuseStep 11708507 = 17562761) B17562761
theorem B31222685 : Blo 1897435 31222685 := bstep (se 3 (by rfl) ⟨5854253, by rfl⟩ : syracuseStep 31222685 = 11708507) B11708507
theorem B83260493 : Blo 1897435 83260493 := bstep (se 3 (by rfl) ⟨15611342, by rfl⟩ : syracuseStep 83260493 = 31222685) B31222685
theorem B55506995 : Blo 1897435 55506995 := bstep (se 1 (by rfl) ⟨41630246, by rfl⟩ : syracuseStep 55506995 = 83260493) B83260493
theorem B37004663 : Blo 1897435 37004663 := bstep (se 1 (by rfl) ⟨27753497, by rfl⟩ : syracuseStep 37004663 = 55506995) B55506995
theorem B24669775 : Blo 1897435 24669775 := bstep (se 1 (by rfl) ⟨18502331, by rfl⟩ : syracuseStep 24669775 = 37004663) B37004663
theorem B32893033 : Blo 1897435 32893033 := bstep (se 2 (by rfl) ⟨12334887, by rfl⟩ : syracuseStep 32893033 = 24669775) B24669775
theorem B43857377 : Blo 1897435 43857377 := bstep (se 2 (by rfl) ⟨16446516, by rfl⟩ : syracuseStep 43857377 = 32893033) B32893033
theorem B29238251 : Blo 1897435 29238251 := bstep (se 1 (by rfl) ⟨21928688, by rfl⟩ : syracuseStep 29238251 = 43857377) B43857377
theorem B77968669 : Blo 1897435 77968669 := bstep (se 3 (by rfl) ⟨14619125, by rfl⟩ : syracuseStep 77968669 = 29238251) B29238251
theorem B103958225 : Blo 1897435 103958225 := bstep (se 2 (by rfl) ⟨38984334, by rfl⟩ : syracuseStep 103958225 = 77968669) B77968669
theorem B69305483 : Blo 1897435 69305483 := bstep (se 1 (by rfl) ⟨51979112, by rfl⟩ : syracuseStep 69305483 = 103958225) B103958225
theorem B46203655 : Blo 1897435 46203655 := bstep (se 1 (by rfl) ⟨34652741, by rfl⟩ : syracuseStep 46203655 = 69305483) B69305483
theorem B61604873 : Blo 1897435 61604873 := bstep (se 2 (by rfl) ⟨23101827, by rfl⟩ : syracuseStep 61604873 = 46203655) B46203655
theorem B41069915 : Blo 1897435 41069915 := bstep (se 1 (by rfl) ⟨30802436, by rfl⟩ : syracuseStep 41069915 = 61604873) B61604873
theorem B27379943 : Blo 1897435 27379943 := bstep (se 1 (by rfl) ⟨20534957, by rfl⟩ : syracuseStep 27379943 = 41069915) B41069915
theorem B18253295 : Blo 1897435 18253295 := bstep (se 1 (by rfl) ⟨13689971, by rfl⟩ : syracuseStep 18253295 = 27379943) B27379943
theorem B12168863 : Blo 1897435 12168863 := bstep (se 1 (by rfl) ⟨9126647, by rfl⟩ : syracuseStep 12168863 = 18253295) B18253295
theorem B8112575 : Blo 1897435 8112575 := bstep (se 1 (by rfl) ⟨6084431, by rfl⟩ : syracuseStep 8112575 = 12168863) B12168863
theorem B5408383 : Blo 1897435 5408383 := bstep (se 1 (by rfl) ⟨4056287, by rfl⟩ : syracuseStep 5408383 = 8112575) B8112575
theorem B7211177 : Blo 1897435 7211177 := bstep (se 2 (by rfl) ⟨2704191, by rfl⟩ : syracuseStep 7211177 = 5408383) B5408383
theorem B4807451 : Blo 1897435 4807451 := bstep (se 1 (by rfl) ⟨3605588, by rfl⟩ : syracuseStep 4807451 = 7211177) B7211177
theorem B3204967 : Blo 1897435 3204967 := bstep (se 1 (by rfl) ⟨2403725, by rfl⟩ : syracuseStep 3204967 = 4807451) B4807451
theorem B4273289 : Blo 1897435 4273289 := bstep (se 2 (by rfl) ⟨1602483, by rfl⟩ : syracuseStep 4273289 = 3204967) B3204967
theorem B2848859 : Blo 1897435 2848859 := bstep (se 1 (by rfl) ⟨2136644, by rfl⟩ : syracuseStep 2848859 = 4273289) B4273289
theorem B1899239 : Blo 1897435 1899239 := bstep (se 1 (by rfl) ⟨1424429, by rfl⟩ : syracuseStep 1899239 = 2848859) B2848859
theorem B2136649 : Blo 1897435 2136649 := bbase (se 2 (by rfl) ⟨801243, by rfl⟩ : syracuseStep 2136649 = 1602487) (by norm_num)
theorem B2848865 : Blo 1897435 2848865 := bstep (se 2 (by rfl) ⟨1068324, by rfl⟩ : syracuseStep 2848865 = 2136649) B2136649
theorem B1899243 : Blo 1897435 1899243 := bstep (se 1 (by rfl) ⟨1424432, by rfl⟩ : syracuseStep 1899243 = 2848865) B2848865
theorem B2887741 : Blo 1897435 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B3850321 : Blo 1897435 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B5133761 : Blo 1897435 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B3422507 : Blo 1897435 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B9126685 : Blo 1897435 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B12168913 : Blo 1897435 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B16225217 : Blo 1897435 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B10816811 : Blo 1897435 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B7211207 : Blo 1897435 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B4807471 : Blo 1897435 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B6409961 : Blo 1897435 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B4273307 : Blo 1897435 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B2848871 : Blo 1897435 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B1899247 : Blo 1897435 1899247 := bstep (se 1 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 1899247 = 2848871) B2848871
theorem B2848877 : Blo 1897435 2848877 := bbase (se 3 (by rfl) ⟨534164, by rfl⟩ : syracuseStep 2848877 = 1068329) (by norm_num)
theorem B1899251 : Blo 1897435 1899251 := bstep (se 1 (by rfl) ⟨1424438, by rfl⟩ : syracuseStep 1899251 = 2848877) B2848877
theorem B4273325 : Blo 1897435 4273325 := bbase (se 3 (by rfl) ⟨801248, by rfl⟩ : syracuseStep 4273325 = 1602497) (by norm_num)
theorem B2848883 : Blo 1897435 2848883 := bstep (se 1 (by rfl) ⟨2136662, by rfl⟩ : syracuseStep 2848883 = 4273325) B4273325
theorem B1899255 : Blo 1897435 1899255 := bstep (se 1 (by rfl) ⟨1424441, by rfl⟩ : syracuseStep 1899255 = 2848883) B2848883
theorem B4563373 : Blo 1897435 4563373 := bbase (se 3 (by rfl) ⟨855632, by rfl⟩ : syracuseStep 4563373 = 1711265) (by norm_num)
theorem B6084497 : Blo 1897435 6084497 := bstep (se 2 (by rfl) ⟨2281686, by rfl⟩ : syracuseStep 6084497 = 4563373) B4563373
theorem B4056331 : Blo 1897435 4056331 := bstep (se 1 (by rfl) ⟨3042248, by rfl⟩ : syracuseStep 4056331 = 6084497) B6084497
theorem B5408441 : Blo 1897435 5408441 := bstep (se 2 (by rfl) ⟨2028165, by rfl⟩ : syracuseStep 5408441 = 4056331) B4056331
theorem B3605627 : Blo 1897435 3605627 := bstep (se 1 (by rfl) ⟨2704220, by rfl⟩ : syracuseStep 3605627 = 5408441) B5408441
theorem B2403751 : Blo 1897435 2403751 := bstep (se 1 (by rfl) ⟨1802813, by rfl⟩ : syracuseStep 2403751 = 3605627) B3605627
theorem B3205001 : Blo 1897435 3205001 := bstep (se 2 (by rfl) ⟨1201875, by rfl⟩ : syracuseStep 3205001 = 2403751) B2403751
theorem B2136667 : Blo 1897435 2136667 := bstep (se 1 (by rfl) ⟨1602500, by rfl⟩ : syracuseStep 2136667 = 3205001) B3205001
theorem B2848889 : Blo 1897435 2848889 := bstep (se 2 (by rfl) ⟨1068333, by rfl⟩ : syracuseStep 2848889 = 2136667) B2136667
theorem B1899259 : Blo 1897435 1899259 := bstep (se 1 (by rfl) ⟨1424444, by rfl⟩ : syracuseStep 1899259 = 2848889) B2848889
theorem B8781493 : Blo 1897435 8781493 := bbase (se 5 (by rfl) ⟨411632, by rfl⟩ : syracuseStep 8781493 = 823265) (by norm_num)
theorem B11708657 : Blo 1897435 11708657 := bstep (se 2 (by rfl) ⟨4390746, by rfl⟩ : syracuseStep 11708657 = 8781493) B8781493
theorem B7805771 : Blo 1897435 7805771 := bstep (se 1 (by rfl) ⟨5854328, by rfl⟩ : syracuseStep 7805771 = 11708657) B11708657
theorem B5203847 : Blo 1897435 5203847 := bstep (se 1 (by rfl) ⟨3902885, by rfl⟩ : syracuseStep 5203847 = 7805771) B7805771
theorem B13876925 : Blo 1897435 13876925 := bstep (se 3 (by rfl) ⟨2601923, by rfl⟩ : syracuseStep 13876925 = 5203847) B5203847
theorem B37005133 : Blo 1897435 37005133 := bstep (se 3 (by rfl) ⟨6938462, by rfl⟩ : syracuseStep 37005133 = 13876925) B13876925
theorem B49340177 : Blo 1897435 49340177 := bstep (se 2 (by rfl) ⟨18502566, by rfl⟩ : syracuseStep 49340177 = 37005133) B37005133
theorem B32893451 : Blo 1897435 32893451 := bstep (se 1 (by rfl) ⟨24670088, by rfl⟩ : syracuseStep 32893451 = 49340177) B49340177
theorem B21928967 : Blo 1897435 21928967 := bstep (se 1 (by rfl) ⟨16446725, by rfl⟩ : syracuseStep 21928967 = 32893451) B32893451
theorem B14619311 : Blo 1897435 14619311 := bstep (se 1 (by rfl) ⟨10964483, by rfl⟩ : syracuseStep 14619311 = 21928967) B21928967
theorem B9746207 : Blo 1897435 9746207 := bstep (se 1 (by rfl) ⟨7309655, by rfl⟩ : syracuseStep 9746207 = 14619311) B14619311
theorem B6497471 : Blo 1897435 6497471 := bstep (se 1 (by rfl) ⟨4873103, by rfl⟩ : syracuseStep 6497471 = 9746207) B9746207
theorem B4331647 : Blo 1897435 4331647 := bstep (se 1 (by rfl) ⟨3248735, by rfl⟩ : syracuseStep 4331647 = 6497471) B6497471
theorem B23102117 : Blo 1897435 23102117 := bstep (se 4 (by rfl) ⟨2165823, by rfl⟩ : syracuseStep 23102117 = 4331647) B4331647
theorem B15401411 : Blo 1897435 15401411 := bstep (se 1 (by rfl) ⟨11551058, by rfl⟩ : syracuseStep 15401411 = 23102117) B23102117
theorem B10267607 : Blo 1897435 10267607 := bstep (se 1 (by rfl) ⟨7700705, by rfl⟩ : syracuseStep 10267607 = 15401411) B15401411
theorem B6845071 : Blo 1897435 6845071 := bstep (se 1 (by rfl) ⟨5133803, by rfl⟩ : syracuseStep 6845071 = 10267607) B10267607
theorem B9126761 : Blo 1897435 9126761 := bstep (se 2 (by rfl) ⟨3422535, by rfl⟩ : syracuseStep 9126761 = 6845071) B6845071
theorem B24338029 : Blo 1897435 24338029 := bstep (se 3 (by rfl) ⟨4563380, by rfl⟩ : syracuseStep 24338029 = 9126761) B9126761
theorem B32450705 : Blo 1897435 32450705 := bstep (se 2 (by rfl) ⟨12169014, by rfl⟩ : syracuseStep 32450705 = 24338029) B24338029
theorem B21633803 : Blo 1897435 21633803 := bstep (se 1 (by rfl) ⟨16225352, by rfl⟩ : syracuseStep 21633803 = 32450705) B32450705
theorem B14422535 : Blo 1897435 14422535 := bstep (se 1 (by rfl) ⟨10816901, by rfl⟩ : syracuseStep 14422535 = 21633803) B21633803
theorem B9615023 : Blo 1897435 9615023 := bstep (se 1 (by rfl) ⟨7211267, by rfl⟩ : syracuseStep 9615023 = 14422535) B14422535
theorem B6410015 : Blo 1897435 6410015 := bstep (se 1 (by rfl) ⟨4807511, by rfl⟩ : syracuseStep 6410015 = 9615023) B9615023
theorem B4273343 : Blo 1897435 4273343 := bstep (se 1 (by rfl) ⟨3205007, by rfl⟩ : syracuseStep 4273343 = 6410015) B6410015
theorem B2848895 : Blo 1897435 2848895 := bstep (se 1 (by rfl) ⟨2136671, by rfl⟩ : syracuseStep 2848895 = 4273343) B4273343
theorem B1899263 : Blo 1897435 1899263 := bstep (se 1 (by rfl) ⟨1424447, by rfl⟩ : syracuseStep 1899263 = 2848895) B2848895
theorem B2848901 : Blo 1897435 2848901 := bbase (se 4 (by rfl) ⟨267084, by rfl⟩ : syracuseStep 2848901 = 534169) (by norm_num)
theorem B1899267 : Blo 1897435 1899267 := bstep (se 1 (by rfl) ⟨1424450, by rfl⟩ : syracuseStep 1899267 = 2848901) B2848901
theorem B3205021 : Blo 1897435 3205021 := bbase (se 3 (by rfl) ⟨600941, by rfl⟩ : syracuseStep 3205021 = 1201883) (by norm_num)
theorem B4273361 : Blo 1897435 4273361 := bstep (se 2 (by rfl) ⟨1602510, by rfl⟩ : syracuseStep 4273361 = 3205021) B3205021
theorem B2848907 : Blo 1897435 2848907 := bstep (se 1 (by rfl) ⟨2136680, by rfl⟩ : syracuseStep 2848907 = 4273361) B4273361
theorem B1899271 : Blo 1897435 1899271 := bstep (se 1 (by rfl) ⟨1424453, by rfl⟩ : syracuseStep 1899271 = 2848907) B2848907
theorem B2136685 : Blo 1897435 2136685 := bbase (se 3 (by rfl) ⟨400628, by rfl⟩ : syracuseStep 2136685 = 801257) (by norm_num)
theorem B2848913 : Blo 1897435 2848913 := bstep (se 2 (by rfl) ⟨1068342, by rfl⟩ : syracuseStep 2848913 = 2136685) B2136685
theorem B1899275 : Blo 1897435 1899275 := bstep (se 1 (by rfl) ⟨1424456, by rfl⟩ : syracuseStep 1899275 = 2848913) B2848913
theorem B6410069 : Blo 1897435 6410069 := bbase (se 9 (by rfl) ⟨18779, by rfl⟩ : syracuseStep 6410069 = 37559) (by norm_num)
theorem B4273379 : Blo 1897435 4273379 := bstep (se 1 (by rfl) ⟨3205034, by rfl⟩ : syracuseStep 4273379 = 6410069) B6410069
theorem B2848919 : Blo 1897435 2848919 := bstep (se 1 (by rfl) ⟨2136689, by rfl⟩ : syracuseStep 2848919 = 4273379) B4273379
theorem B1899279 : Blo 1897435 1899279 := bstep (se 1 (by rfl) ⟨1424459, by rfl⟩ : syracuseStep 1899279 = 2848919) B2848919
theorem B2848925 : Blo 1897435 2848925 := bbase (se 3 (by rfl) ⟨534173, by rfl⟩ : syracuseStep 2848925 = 1068347) (by norm_num)
theorem B1899283 : Blo 1897435 1899283 := bstep (se 1 (by rfl) ⟨1424462, by rfl⟩ : syracuseStep 1899283 = 2848925) B2848925
theorem B4273397 : Blo 1897435 4273397 := bbase (se 5 (by rfl) ⟨200315, by rfl⟩ : syracuseStep 4273397 = 400631) (by norm_num)
theorem B2848931 : Blo 1897435 2848931 := bstep (se 1 (by rfl) ⟨2136698, by rfl⟩ : syracuseStep 2848931 = 4273397) B4273397
theorem B1899287 : Blo 1897435 1899287 := bstep (se 1 (by rfl) ⟨1424465, by rfl⟩ : syracuseStep 1899287 = 2848931) B2848931
theorem B27380693 : Blo 1897435 27380693 := bbase (se 7 (by rfl) ⟨320867, by rfl⟩ : syracuseStep 27380693 = 641735) (by norm_num)
theorem B18253795 : Blo 1897435 18253795 := bstep (se 1 (by rfl) ⟨13690346, by rfl⟩ : syracuseStep 18253795 = 27380693) B27380693
theorem B24338393 : Blo 1897435 24338393 := bstep (se 2 (by rfl) ⟨9126897, by rfl⟩ : syracuseStep 24338393 = 18253795) B18253795
theorem B16225595 : Blo 1897435 16225595 := bstep (se 1 (by rfl) ⟨12169196, by rfl⟩ : syracuseStep 16225595 = 24338393) B24338393
theorem B10817063 : Blo 1897435 10817063 := bstep (se 1 (by rfl) ⟨8112797, by rfl⟩ : syracuseStep 10817063 = 16225595) B16225595
theorem B7211375 : Blo 1897435 7211375 := bstep (se 1 (by rfl) ⟨5408531, by rfl⟩ : syracuseStep 7211375 = 10817063) B10817063
theorem B4807583 : Blo 1897435 4807583 := bstep (se 1 (by rfl) ⟨3605687, by rfl⟩ : syracuseStep 4807583 = 7211375) B7211375
theorem B3205055 : Blo 1897435 3205055 := bstep (se 1 (by rfl) ⟨2403791, by rfl⟩ : syracuseStep 3205055 = 4807583) B4807583
theorem B2136703 : Blo 1897435 2136703 := bstep (se 1 (by rfl) ⟨1602527, by rfl⟩ : syracuseStep 2136703 = 3205055) B3205055
theorem B2848937 : Blo 1897435 2848937 := bstep (se 2 (by rfl) ⟨1068351, by rfl⟩ : syracuseStep 2848937 = 2136703) B2136703
theorem B1899291 : Blo 1897435 1899291 := bstep (se 1 (by rfl) ⟨1424468, by rfl⟩ : syracuseStep 1899291 = 2848937) B2848937
theorem B9126917 : Blo 1897435 9126917 := bbase (se 4 (by rfl) ⟨855648, by rfl⟩ : syracuseStep 9126917 = 1711297) (by norm_num)
theorem B6084611 : Blo 1897435 6084611 := bstep (se 1 (by rfl) ⟨4563458, by rfl⟩ : syracuseStep 6084611 = 9126917) B9126917
theorem B4056407 : Blo 1897435 4056407 := bstep (se 1 (by rfl) ⟨3042305, by rfl⟩ : syracuseStep 4056407 = 6084611) B6084611
theorem B2704271 : Blo 1897435 2704271 := bstep (se 1 (by rfl) ⟨2028203, by rfl⟩ : syracuseStep 2704271 = 4056407) B4056407
theorem B7211389 : Blo 1897435 7211389 := bstep (se 3 (by rfl) ⟨1352135, by rfl⟩ : syracuseStep 7211389 = 2704271) B2704271
theorem B9615185 : Blo 1897435 9615185 := bstep (se 2 (by rfl) ⟨3605694, by rfl⟩ : syracuseStep 9615185 = 7211389) B7211389
theorem B6410123 : Blo 1897435 6410123 := bstep (se 1 (by rfl) ⟨4807592, by rfl⟩ : syracuseStep 6410123 = 9615185) B9615185
theorem B4273415 : Blo 1897435 4273415 := bstep (se 1 (by rfl) ⟨3205061, by rfl⟩ : syracuseStep 4273415 = 6410123) B6410123
theorem B2848943 : Blo 1897435 2848943 := bstep (se 1 (by rfl) ⟨2136707, by rfl⟩ : syracuseStep 2848943 = 4273415) B4273415
theorem B1899295 : Blo 1897435 1899295 := bstep (se 1 (by rfl) ⟨1424471, by rfl⟩ : syracuseStep 1899295 = 2848943) B2848943
theorem B2848949 : Blo 1897435 2848949 := bbase (se 5 (by rfl) ⟨133544, by rfl⟩ : syracuseStep 2848949 = 267089) (by norm_num)
theorem B1899299 : Blo 1897435 1899299 := bstep (se 1 (by rfl) ⟨1424474, by rfl⟩ : syracuseStep 1899299 = 2848949) B2848949
theorem B4807613 : Blo 1897435 4807613 := bbase (se 3 (by rfl) ⟨901427, by rfl⟩ : syracuseStep 4807613 = 1802855) (by norm_num)
theorem B3205075 : Blo 1897435 3205075 := bstep (se 1 (by rfl) ⟨2403806, by rfl⟩ : syracuseStep 3205075 = 4807613) B4807613
theorem B4273433 : Blo 1897435 4273433 := bstep (se 2 (by rfl) ⟨1602537, by rfl⟩ : syracuseStep 4273433 = 3205075) B3205075
theorem B2848955 : Blo 1897435 2848955 := bstep (se 1 (by rfl) ⟨2136716, by rfl⟩ : syracuseStep 2848955 = 4273433) B4273433
theorem B1899303 : Blo 1897435 1899303 := bstep (se 1 (by rfl) ⟨1424477, by rfl⟩ : syracuseStep 1899303 = 2848955) B2848955
theorem B2136721 : Blo 1897435 2136721 := bbase (se 2 (by rfl) ⟨801270, by rfl⟩ : syracuseStep 2136721 = 1602541) (by norm_num)
theorem B2848961 : Blo 1897435 2848961 := bstep (se 2 (by rfl) ⟨1068360, by rfl⟩ : syracuseStep 2848961 = 2136721) B2136721
theorem B1899307 : Blo 1897435 1899307 := bstep (se 1 (by rfl) ⟨1424480, by rfl⟩ : syracuseStep 1899307 = 2848961) B2848961
theorem B3605725 : Blo 1897435 3605725 := bbase (se 3 (by rfl) ⟨676073, by rfl⟩ : syracuseStep 3605725 = 1352147) (by norm_num)
theorem B4807633 : Blo 1897435 4807633 := bstep (se 2 (by rfl) ⟨1802862, by rfl⟩ : syracuseStep 4807633 = 3605725) B3605725
theorem B6410177 : Blo 1897435 6410177 := bstep (se 2 (by rfl) ⟨2403816, by rfl⟩ : syracuseStep 6410177 = 4807633) B4807633
theorem B4273451 : Blo 1897435 4273451 := bstep (se 1 (by rfl) ⟨3205088, by rfl⟩ : syracuseStep 4273451 = 6410177) B6410177
theorem B2848967 : Blo 1897435 2848967 := bstep (se 1 (by rfl) ⟨2136725, by rfl⟩ : syracuseStep 2848967 = 4273451) B4273451
theorem B1899311 : Blo 1897435 1899311 := bstep (se 1 (by rfl) ⟨1424483, by rfl⟩ : syracuseStep 1899311 = 2848967) B2848967
theorem B2848973 : Blo 1897435 2848973 := bbase (se 3 (by rfl) ⟨534182, by rfl⟩ : syracuseStep 2848973 = 1068365) (by norm_num)
theorem B1899315 : Blo 1897435 1899315 := bstep (se 1 (by rfl) ⟨1424486, by rfl⟩ : syracuseStep 1899315 = 2848973) B2848973
theorem B4273469 : Blo 1897435 4273469 := bbase (se 3 (by rfl) ⟨801275, by rfl⟩ : syracuseStep 4273469 = 1602551) (by norm_num)
theorem B2848979 : Blo 1897435 2848979 := bstep (se 1 (by rfl) ⟨2136734, by rfl⟩ : syracuseStep 2848979 = 4273469) B4273469
theorem B1899319 : Blo 1897435 1899319 := bstep (se 1 (by rfl) ⟨1424489, by rfl⟩ : syracuseStep 1899319 = 2848979) B2848979
theorem B3205109 : Blo 1897435 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B2136739 : Blo 1897435 2136739 := bstep (se 1 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 2136739 = 3205109) B3205109
theorem B2848985 : Blo 1897435 2848985 := bstep (se 2 (by rfl) ⟨1068369, by rfl⟩ : syracuseStep 2848985 = 2136739) B2136739
theorem B1899323 : Blo 1897435 1899323 := bstep (se 1 (by rfl) ⟨1424492, by rfl⟩ : syracuseStep 1899323 = 2848985) B2848985
theorem B2165897 : Blo 1897435 2165897 := bbase (se 2 (by rfl) ⟨812211, by rfl⟩ : syracuseStep 2165897 = 1624423) (by norm_num)
theorem B5775725 : Blo 1897435 5775725 := bstep (se 3 (by rfl) ⟨1082948, by rfl⟩ : syracuseStep 5775725 = 2165897) B2165897
theorem B15401933 : Blo 1897435 15401933 := bstep (se 3 (by rfl) ⟨2887862, by rfl⟩ : syracuseStep 15401933 = 5775725) B5775725
theorem B10267955 : Blo 1897435 10267955 := bstep (se 1 (by rfl) ⟨7700966, by rfl⟩ : syracuseStep 10267955 = 15401933) B15401933
theorem B6845303 : Blo 1897435 6845303 := bstep (se 1 (by rfl) ⟨5133977, by rfl⟩ : syracuseStep 6845303 = 10267955) B10267955
theorem B4563535 : Blo 1897435 4563535 := bstep (se 1 (by rfl) ⟨3422651, by rfl⟩ : syracuseStep 4563535 = 6845303) B6845303
theorem B6084713 : Blo 1897435 6084713 := bstep (se 2 (by rfl) ⟨2281767, by rfl⟩ : syracuseStep 6084713 = 4563535) B4563535
theorem B4056475 : Blo 1897435 4056475 := bstep (se 1 (by rfl) ⟨3042356, by rfl⟩ : syracuseStep 4056475 = 6084713) B6084713
theorem B5408633 : Blo 1897435 5408633 := bstep (se 2 (by rfl) ⟨2028237, by rfl⟩ : syracuseStep 5408633 = 4056475) B4056475
theorem B14423021 : Blo 1897435 14423021 := bstep (se 3 (by rfl) ⟨2704316, by rfl⟩ : syracuseStep 14423021 = 5408633) B5408633
theorem B9615347 : Blo 1897435 9615347 := bstep (se 1 (by rfl) ⟨7211510, by rfl⟩ : syracuseStep 9615347 = 14423021) B14423021
theorem B6410231 : Blo 1897435 6410231 := bstep (se 1 (by rfl) ⟨4807673, by rfl⟩ : syracuseStep 6410231 = 9615347) B9615347
theorem B4273487 : Blo 1897435 4273487 := bstep (se 1 (by rfl) ⟨3205115, by rfl⟩ : syracuseStep 4273487 = 6410231) B6410231
theorem B2848991 : Blo 1897435 2848991 := bstep (se 1 (by rfl) ⟨2136743, by rfl⟩ : syracuseStep 2848991 = 4273487) B4273487
theorem B1899327 : Blo 1897435 1899327 := bstep (se 1 (by rfl) ⟨1424495, by rfl⟩ : syracuseStep 1899327 = 2848991) B2848991
theorem B2848997 : Blo 1897435 2848997 := bbase (se 4 (by rfl) ⟨267093, by rfl⟩ : syracuseStep 2848997 = 534187) (by norm_num)
theorem B1899331 : Blo 1897435 1899331 := bstep (se 1 (by rfl) ⟨1424498, by rfl⟩ : syracuseStep 1899331 = 2848997) B2848997
theorem B4056493 : Blo 1897435 4056493 := bbase (se 3 (by rfl) ⟨760592, by rfl⟩ : syracuseStep 4056493 = 1521185) (by norm_num)
theorem B5408657 : Blo 1897435 5408657 := bstep (se 2 (by rfl) ⟨2028246, by rfl⟩ : syracuseStep 5408657 = 4056493) B4056493
theorem B3605771 : Blo 1897435 3605771 := bstep (se 1 (by rfl) ⟨2704328, by rfl⟩ : syracuseStep 3605771 = 5408657) B5408657
theorem B2403847 : Blo 1897435 2403847 := bstep (se 1 (by rfl) ⟨1802885, by rfl⟩ : syracuseStep 2403847 = 3605771) B3605771
theorem B3205129 : Blo 1897435 3205129 := bstep (se 2 (by rfl) ⟨1201923, by rfl⟩ : syracuseStep 3205129 = 2403847) B2403847
theorem B4273505 : Blo 1897435 4273505 := bstep (se 2 (by rfl) ⟨1602564, by rfl⟩ : syracuseStep 4273505 = 3205129) B3205129
theorem B2849003 : Blo 1897435 2849003 := bstep (se 1 (by rfl) ⟨2136752, by rfl⟩ : syracuseStep 2849003 = 4273505) B4273505
theorem B1899335 : Blo 1897435 1899335 := bstep (se 1 (by rfl) ⟨1424501, by rfl⟩ : syracuseStep 1899335 = 2849003) B2849003
theorem B2136757 : Blo 1897435 2136757 := bbase (se 5 (by rfl) ⟨100160, by rfl⟩ : syracuseStep 2136757 = 200321) (by norm_num)
theorem B2849009 : Blo 1897435 2849009 := bstep (se 2 (by rfl) ⟨1068378, by rfl⟩ : syracuseStep 2849009 = 2136757) B2136757
theorem B1899339 : Blo 1897435 1899339 := bstep (se 1 (by rfl) ⟨1424504, by rfl⟩ : syracuseStep 1899339 = 2849009) B2849009
theorem B2403857 : Blo 1897435 2403857 := bbase (se 2 (by rfl) ⟨901446, by rfl⟩ : syracuseStep 2403857 = 1802893) (by norm_num)
theorem B6410285 : Blo 1897435 6410285 := bstep (se 3 (by rfl) ⟨1201928, by rfl⟩ : syracuseStep 6410285 = 2403857) B2403857
theorem B4273523 : Blo 1897435 4273523 := bstep (se 1 (by rfl) ⟨3205142, by rfl⟩ : syracuseStep 4273523 = 6410285) B6410285
theorem B2849015 : Blo 1897435 2849015 := bstep (se 1 (by rfl) ⟨2136761, by rfl⟩ : syracuseStep 2849015 = 4273523) B4273523
theorem B1899343 : Blo 1897435 1899343 := bstep (se 1 (by rfl) ⟨1424507, by rfl⟩ : syracuseStep 1899343 = 2849015) B2849015
theorem B2849021 : Blo 1897435 2849021 := bbase (se 3 (by rfl) ⟨534191, by rfl⟩ : syracuseStep 2849021 = 1068383) (by norm_num)
theorem B1899347 : Blo 1897435 1899347 := bstep (se 1 (by rfl) ⟨1424510, by rfl⟩ : syracuseStep 1899347 = 2849021) B2849021
theorem B4273541 : Blo 1897435 4273541 := bbase (se 4 (by rfl) ⟨400644, by rfl⟩ : syracuseStep 4273541 = 801289) (by norm_num)
theorem B2849027 : Blo 1897435 2849027 := bstep (se 1 (by rfl) ⟨2136770, by rfl⟩ : syracuseStep 2849027 = 4273541) B4273541
theorem B1899351 : Blo 1897435 1899351 := bstep (se 1 (by rfl) ⟨1424513, by rfl⟩ : syracuseStep 1899351 = 2849027) B2849027
theorem B2704357 : Blo 1897435 2704357 := bbase (se 4 (by rfl) ⟨253533, by rfl⟩ : syracuseStep 2704357 = 507067) (by norm_num)
theorem B3605809 : Blo 1897435 3605809 := bstep (se 2 (by rfl) ⟨1352178, by rfl⟩ : syracuseStep 3605809 = 2704357) B2704357
theorem B4807745 : Blo 1897435 4807745 := bstep (se 2 (by rfl) ⟨1802904, by rfl⟩ : syracuseStep 4807745 = 3605809) B3605809
theorem B3205163 : Blo 1897435 3205163 := bstep (se 1 (by rfl) ⟨2403872, by rfl⟩ : syracuseStep 3205163 = 4807745) B4807745
theorem B2136775 : Blo 1897435 2136775 := bstep (se 1 (by rfl) ⟨1602581, by rfl⟩ : syracuseStep 2136775 = 3205163) B3205163
theorem B2849033 : Blo 1897435 2849033 := bstep (se 2 (by rfl) ⟨1068387, by rfl⟩ : syracuseStep 2849033 = 2136775) B2136775
theorem B1899355 : Blo 1897435 1899355 := bstep (se 1 (by rfl) ⟨1424516, by rfl⟩ : syracuseStep 1899355 = 2849033) B2849033
theorem B9615509 : Blo 1897435 9615509 := bbase (se 6 (by rfl) ⟨225363, by rfl⟩ : syracuseStep 9615509 = 450727) (by norm_num)
theorem B6410339 : Blo 1897435 6410339 := bstep (se 1 (by rfl) ⟨4807754, by rfl⟩ : syracuseStep 6410339 = 9615509) B9615509
theorem B4273559 : Blo 1897435 4273559 := bstep (se 1 (by rfl) ⟨3205169, by rfl⟩ : syracuseStep 4273559 = 6410339) B6410339
theorem B2849039 : Blo 1897435 2849039 := bstep (se 1 (by rfl) ⟨2136779, by rfl⟩ : syracuseStep 2849039 = 4273559) B4273559
theorem B1899359 : Blo 1897435 1899359 := bstep (se 1 (by rfl) ⟨1424519, by rfl⟩ : syracuseStep 1899359 = 2849039) B2849039
theorem B2849045 : Blo 1897435 2849045 := bbase (se 6 (by rfl) ⟨66774, by rfl⟩ : syracuseStep 2849045 = 133549) (by norm_num)
theorem B1899363 : Blo 1897435 1899363 := bstep (se 1 (by rfl) ⟨1424522, by rfl⟩ : syracuseStep 1899363 = 2849045) B2849045
theorem B4331885 : Blo 1897435 4331885 := bbase (se 3 (by rfl) ⟨812228, by rfl⟩ : syracuseStep 4331885 = 1624457) (by norm_num)
theorem B11551693 : Blo 1897435 11551693 := bstep (se 3 (by rfl) ⟨2165942, by rfl⟩ : syracuseStep 11551693 = 4331885) B4331885
theorem B15402257 : Blo 1897435 15402257 := bstep (se 2 (by rfl) ⟨5775846, by rfl⟩ : syracuseStep 15402257 = 11551693) B11551693
theorem B10268171 : Blo 1897435 10268171 := bstep (se 1 (by rfl) ⟨7701128, by rfl⟩ : syracuseStep 10268171 = 15402257) B15402257
theorem B6845447 : Blo 1897435 6845447 := bstep (se 1 (by rfl) ⟨5134085, by rfl⟩ : syracuseStep 6845447 = 10268171) B10268171
theorem B4563631 : Blo 1897435 4563631 := bstep (se 1 (by rfl) ⟨3422723, by rfl⟩ : syracuseStep 4563631 = 6845447) B6845447
theorem B24339365 : Blo 1897435 24339365 := bstep (se 4 (by rfl) ⟨2281815, by rfl⟩ : syracuseStep 24339365 = 4563631) B4563631
theorem B16226243 : Blo 1897435 16226243 := bstep (se 1 (by rfl) ⟨12169682, by rfl⟩ : syracuseStep 16226243 = 24339365) B24339365
theorem B10817495 : Blo 1897435 10817495 := bstep (se 1 (by rfl) ⟨8113121, by rfl⟩ : syracuseStep 10817495 = 16226243) B16226243
theorem B7211663 : Blo 1897435 7211663 := bstep (se 1 (by rfl) ⟨5408747, by rfl⟩ : syracuseStep 7211663 = 10817495) B10817495
theorem B4807775 : Blo 1897435 4807775 := bstep (se 1 (by rfl) ⟨3605831, by rfl⟩ : syracuseStep 4807775 = 7211663) B7211663
theorem B3205183 : Blo 1897435 3205183 := bstep (se 1 (by rfl) ⟨2403887, by rfl⟩ : syracuseStep 3205183 = 4807775) B4807775
theorem B4273577 : Blo 1897435 4273577 := bstep (se 2 (by rfl) ⟨1602591, by rfl⟩ : syracuseStep 4273577 = 3205183) B3205183
theorem B2849051 : Blo 1897435 2849051 := bstep (se 1 (by rfl) ⟨2136788, by rfl⟩ : syracuseStep 2849051 = 4273577) B4273577
theorem B1899367 : Blo 1897435 1899367 := bstep (se 1 (by rfl) ⟨1424525, by rfl⟩ : syracuseStep 1899367 = 2849051) B2849051
theorem B2136793 : Blo 1897435 2136793 := bbase (se 2 (by rfl) ⟨801297, by rfl⟩ : syracuseStep 2136793 = 1602595) (by norm_num)
theorem B2849057 : Blo 1897435 2849057 := bstep (se 2 (by rfl) ⟨1068396, by rfl⟩ : syracuseStep 2849057 = 2136793) B2136793
theorem B1899371 : Blo 1897435 1899371 := bstep (se 1 (by rfl) ⟨1424528, by rfl⟩ : syracuseStep 1899371 = 2849057) B2849057
theorem B2028289 : Blo 1897435 2028289 := bbase (se 2 (by rfl) ⟨760608, by rfl⟩ : syracuseStep 2028289 = 1521217) (by norm_num)
theorem B2704385 : Blo 1897435 2704385 := bstep (se 2 (by rfl) ⟨1014144, by rfl⟩ : syracuseStep 2704385 = 2028289) B2028289
theorem B7211693 : Blo 1897435 7211693 := bstep (se 3 (by rfl) ⟨1352192, by rfl⟩ : syracuseStep 7211693 = 2704385) B2704385
theorem B4807795 : Blo 1897435 4807795 := bstep (se 1 (by rfl) ⟨3605846, by rfl⟩ : syracuseStep 4807795 = 7211693) B7211693
theorem B6410393 : Blo 1897435 6410393 := bstep (se 2 (by rfl) ⟨2403897, by rfl⟩ : syracuseStep 6410393 = 4807795) B4807795
theorem B4273595 : Blo 1897435 4273595 := bstep (se 1 (by rfl) ⟨3205196, by rfl⟩ : syracuseStep 4273595 = 6410393) B6410393
theorem B2849063 : Blo 1897435 2849063 := bstep (se 1 (by rfl) ⟨2136797, by rfl⟩ : syracuseStep 2849063 = 4273595) B4273595
theorem B1899375 : Blo 1897435 1899375 := bstep (se 1 (by rfl) ⟨1424531, by rfl⟩ : syracuseStep 1899375 = 2849063) B2849063
theorem B2849069 : Blo 1897435 2849069 := bbase (se 3 (by rfl) ⟨534200, by rfl⟩ : syracuseStep 2849069 = 1068401) (by norm_num)
theorem B1899379 : Blo 1897435 1899379 := bstep (se 1 (by rfl) ⟨1424534, by rfl⟩ : syracuseStep 1899379 = 2849069) B2849069
theorem B4273613 : Blo 1897435 4273613 := bbase (se 3 (by rfl) ⟨801302, by rfl⟩ : syracuseStep 4273613 = 1602605) (by norm_num)
theorem B2849075 : Blo 1897435 2849075 := bstep (se 1 (by rfl) ⟨2136806, by rfl⟩ : syracuseStep 2849075 = 4273613) B4273613
theorem B1899383 : Blo 1897435 1899383 := bstep (se 1 (by rfl) ⟨1424537, by rfl⟩ : syracuseStep 1899383 = 2849075) B2849075
theorem B2403913 : Blo 1897435 2403913 := bbase (se 2 (by rfl) ⟨901467, by rfl⟩ : syracuseStep 2403913 = 1802935) (by norm_num)
theorem B3205217 : Blo 1897435 3205217 := bstep (se 2 (by rfl) ⟨1201956, by rfl⟩ : syracuseStep 3205217 = 2403913) B2403913
theorem B2136811 : Blo 1897435 2136811 := bstep (se 1 (by rfl) ⟨1602608, by rfl⟩ : syracuseStep 2136811 = 3205217) B3205217
theorem B2849081 : Blo 1897435 2849081 := bstep (se 2 (by rfl) ⟨1068405, by rfl⟩ : syracuseStep 2849081 = 2136811) B2136811
theorem B1899387 : Blo 1897435 1899387 := bstep (se 1 (by rfl) ⟨1424540, by rfl⟩ : syracuseStep 1899387 = 2849081) B2849081
theorem B6497909 : Blo 1897435 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B4331939 : Blo 1897435 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B11551837 : Blo 1897435 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B15402449 : Blo 1897435 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B10268299 : Blo 1897435 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B13691065 : Blo 1897435 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B18254753 : Blo 1897435 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B12169835 : Blo 1897435 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B8113223 : Blo 1897435 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B21635261 : Blo 1897435 21635261 := bstep (se 3 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 21635261 = 8113223) B8113223
theorem B14423507 : Blo 1897435 14423507 := bstep (se 1 (by rfl) ⟨10817630, by rfl⟩ : syracuseStep 14423507 = 21635261) B21635261
theorem B9615671 : Blo 1897435 9615671 := bstep (se 1 (by rfl) ⟨7211753, by rfl⟩ : syracuseStep 9615671 = 14423507) B14423507
theorem B6410447 : Blo 1897435 6410447 := bstep (se 1 (by rfl) ⟨4807835, by rfl⟩ : syracuseStep 6410447 = 9615671) B9615671
theorem B4273631 : Blo 1897435 4273631 := bstep (se 1 (by rfl) ⟨3205223, by rfl⟩ : syracuseStep 4273631 = 6410447) B6410447
theorem B2849087 : Blo 1897435 2849087 := bstep (se 1 (by rfl) ⟨2136815, by rfl⟩ : syracuseStep 2849087 = 4273631) B4273631
theorem B1899391 : Blo 1897435 1899391 := bstep (se 1 (by rfl) ⟨1424543, by rfl⟩ : syracuseStep 1899391 = 2849087) B2849087
theorem B2849093 : Blo 1897435 2849093 := bbase (se 4 (by rfl) ⟨267102, by rfl⟩ : syracuseStep 2849093 = 534205) (by norm_num)
theorem B1899395 : Blo 1897435 1899395 := bstep (se 1 (by rfl) ⟨1424546, by rfl⟩ : syracuseStep 1899395 = 2849093) B2849093
theorem B3205237 : Blo 1897435 3205237 := bbase (se 5 (by rfl) ⟨150245, by rfl⟩ : syracuseStep 3205237 = 300491) (by norm_num)
theorem B4273649 : Blo 1897435 4273649 := bstep (se 2 (by rfl) ⟨1602618, by rfl⟩ : syracuseStep 4273649 = 3205237) B3205237
theorem B2849099 : Blo 1897435 2849099 := bstep (se 1 (by rfl) ⟨2136824, by rfl⟩ : syracuseStep 2849099 = 4273649) B4273649
theorem B1899399 : Blo 1897435 1899399 := bstep (se 1 (by rfl) ⟨1424549, by rfl⟩ : syracuseStep 1899399 = 2849099) B2849099
theorem B2136829 : Blo 1897435 2136829 := bbase (se 3 (by rfl) ⟨400655, by rfl⟩ : syracuseStep 2136829 = 801311) (by norm_num)
theorem B2849105 : Blo 1897435 2849105 := bstep (se 2 (by rfl) ⟨1068414, by rfl⟩ : syracuseStep 2849105 = 2136829) B2136829
theorem B1899403 : Blo 1897435 1899403 := bstep (se 1 (by rfl) ⟨1424552, by rfl⟩ : syracuseStep 1899403 = 2849105) B2849105
theorem B6410501 : Blo 1897435 6410501 := bbase (se 4 (by rfl) ⟨600984, by rfl⟩ : syracuseStep 6410501 = 1201969) (by norm_num)
theorem B4273667 : Blo 1897435 4273667 := bstep (se 1 (by rfl) ⟨3205250, by rfl⟩ : syracuseStep 4273667 = 6410501) B6410501
theorem B2849111 : Blo 1897435 2849111 := bstep (se 1 (by rfl) ⟨2136833, by rfl⟩ : syracuseStep 2849111 = 4273667) B4273667
theorem B1899407 : Blo 1897435 1899407 := bstep (se 1 (by rfl) ⟨1424555, by rfl⟩ : syracuseStep 1899407 = 2849111) B2849111
theorem B2849117 : Blo 1897435 2849117 := bbase (se 3 (by rfl) ⟨534209, by rfl⟩ : syracuseStep 2849117 = 1068419) (by norm_num)
theorem B1899411 : Blo 1897435 1899411 := bstep (se 1 (by rfl) ⟨1424558, by rfl⟩ : syracuseStep 1899411 = 2849117) B2849117
theorem B4273685 : Blo 1897435 4273685 := bbase (se 6 (by rfl) ⟨100164, by rfl⟩ : syracuseStep 4273685 = 200329) (by norm_num)
theorem B2849123 : Blo 1897435 2849123 := bstep (se 1 (by rfl) ⟨2136842, by rfl⟩ : syracuseStep 2849123 = 4273685) B4273685
theorem B1899415 : Blo 1897435 1899415 := bstep (se 1 (by rfl) ⟨1424561, by rfl⟩ : syracuseStep 1899415 = 2849123) B2849123
theorem B7211861 : Blo 1897435 7211861 := bbase (se 9 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 7211861 = 42257) (by norm_num)
theorem B4807907 : Blo 1897435 4807907 := bstep (se 1 (by rfl) ⟨3605930, by rfl⟩ : syracuseStep 4807907 = 7211861) B7211861
theorem B3205271 : Blo 1897435 3205271 := bstep (se 1 (by rfl) ⟨2403953, by rfl⟩ : syracuseStep 3205271 = 4807907) B4807907
theorem B2136847 : Blo 1897435 2136847 := bstep (se 1 (by rfl) ⟨1602635, by rfl⟩ : syracuseStep 2136847 = 3205271) B3205271
theorem B2849129 : Blo 1897435 2849129 := bstep (se 2 (by rfl) ⟨1068423, by rfl⟩ : syracuseStep 2849129 = 2136847) B2136847
theorem B1899419 : Blo 1897435 1899419 := bstep (se 1 (by rfl) ⟨1424564, by rfl⟩ : syracuseStep 1899419 = 2849129) B2849129
theorem B10817813 : Blo 1897435 10817813 := bbase (se 6 (by rfl) ⟨253542, by rfl⟩ : syracuseStep 10817813 = 507085) (by norm_num)
theorem B7211875 : Blo 1897435 7211875 := bstep (se 1 (by rfl) ⟨5408906, by rfl⟩ : syracuseStep 7211875 = 10817813) B10817813
theorem B9615833 : Blo 1897435 9615833 := bstep (se 2 (by rfl) ⟨3605937, by rfl⟩ : syracuseStep 9615833 = 7211875) B7211875
theorem B6410555 : Blo 1897435 6410555 := bstep (se 1 (by rfl) ⟨4807916, by rfl⟩ : syracuseStep 6410555 = 9615833) B9615833
theorem B4273703 : Blo 1897435 4273703 := bstep (se 1 (by rfl) ⟨3205277, by rfl⟩ : syracuseStep 4273703 = 6410555) B6410555
theorem B2849135 : Blo 1897435 2849135 := bstep (se 1 (by rfl) ⟨2136851, by rfl⟩ : syracuseStep 2849135 = 4273703) B4273703
theorem B1899423 : Blo 1897435 1899423 := bstep (se 1 (by rfl) ⟨1424567, by rfl⟩ : syracuseStep 1899423 = 2849135) B2849135
theorem B2849141 : Blo 1897435 2849141 := bbase (se 5 (by rfl) ⟨133553, by rfl⟩ : syracuseStep 2849141 = 267107) (by norm_num)
theorem B1899427 : Blo 1897435 1899427 := bstep (se 1 (by rfl) ⟨1424570, by rfl⟩ : syracuseStep 1899427 = 2849141) B2849141
theorem B2028349 : Blo 1897435 2028349 := bbase (se 3 (by rfl) ⟨380315, by rfl⟩ : syracuseStep 2028349 = 760631) (by norm_num)
theorem B2704465 : Blo 1897435 2704465 := bstep (se 2 (by rfl) ⟨1014174, by rfl⟩ : syracuseStep 2704465 = 2028349) B2028349
theorem B3605953 : Blo 1897435 3605953 := bstep (se 2 (by rfl) ⟨1352232, by rfl⟩ : syracuseStep 3605953 = 2704465) B2704465
theorem B4807937 : Blo 1897435 4807937 := bstep (se 2 (by rfl) ⟨1802976, by rfl⟩ : syracuseStep 4807937 = 3605953) B3605953
theorem B3205291 : Blo 1897435 3205291 := bstep (se 1 (by rfl) ⟨2403968, by rfl⟩ : syracuseStep 3205291 = 4807937) B4807937
theorem B4273721 : Blo 1897435 4273721 := bstep (se 2 (by rfl) ⟨1602645, by rfl⟩ : syracuseStep 4273721 = 3205291) B3205291
theorem B2849147 : Blo 1897435 2849147 := bstep (se 1 (by rfl) ⟨2136860, by rfl⟩ : syracuseStep 2849147 = 4273721) B4273721
theorem B1899431 : Blo 1897435 1899431 := bstep (se 1 (by rfl) ⟨1424573, by rfl⟩ : syracuseStep 1899431 = 2849147) B2849147
theorem B2136865 : Blo 1897435 2136865 := bbase (se 2 (by rfl) ⟨801324, by rfl⟩ : syracuseStep 2136865 = 1602649) (by norm_num)
theorem B2849153 : Blo 1897435 2849153 := bstep (se 2 (by rfl) ⟨1068432, by rfl⟩ : syracuseStep 2849153 = 2136865) B2136865
theorem B1899435 : Blo 1897435 1899435 := bstep (se 1 (by rfl) ⟨1424576, by rfl⟩ : syracuseStep 1899435 = 2849153) B2849153
theorem C0 (j : ℕ) (h1 : 474358 ≤ j) (h2 : j ≤ 474858) : Blo 1897435 (4 * j + 3) := by
  interval_cases j
  · exact B1897435
  · exact B1897439
  · exact B1897443
  · exact B1897447
  · exact B1897451
  · exact B1897455
  · exact B1897459
  · exact B1897463
  · exact B1897467
  · exact B1897471
  · exact B1897475
  · exact B1897479
  · exact B1897483
  · exact B1897487
  · exact B1897491
  · exact B1897495
  · exact B1897499
  · exact B1897503
  · exact B1897507
  · exact B1897511
  · exact B1897515
  · exact B1897519
  · exact B1897523
  · exact B1897527
  · exact B1897531
  · exact B1897535
  · exact B1897539
  · exact B1897543
  · exact B1897547
  · exact B1897551
  · exact B1897555
  · exact B1897559
  · exact B1897563
  · exact B1897567
  · exact B1897571
  · exact B1897575
  · exact B1897579
  · exact B1897583
  · exact B1897587
  · exact B1897591
  · exact B1897595
  · exact B1897599
  · exact B1897603
  · exact B1897607
  · exact B1897611
  · exact B1897615
  · exact B1897619
  · exact B1897623
  · exact B1897627
  · exact B1897631
  · exact B1897635
  · exact B1897639
  · exact B1897643
  · exact B1897647
  · exact B1897651
  · exact B1897655
  · exact B1897659
  · exact B1897663
  · exact B1897667
  · exact B1897671
  · exact B1897675
  · exact B1897679
  · exact B1897683
  · exact B1897687
  · exact B1897691
  · exact B1897695
  · exact B1897699
  · exact B1897703
  · exact B1897707
  · exact B1897711
  · exact B1897715
  · exact B1897719
  · exact B1897723
  · exact B1897727
  · exact B1897731
  · exact B1897735
  · exact B1897739
  · exact B1897743
  · exact B1897747
  · exact B1897751
  · exact B1897755
  · exact B1897759
  · exact B1897763
  · exact B1897767
  · exact B1897771
  · exact B1897775
  · exact B1897779
  · exact B1897783
  · exact B1897787
  · exact B1897791
  · exact B1897795
  · exact B1897799
  · exact B1897803
  · exact B1897807
  · exact B1897811
  · exact B1897815
  · exact B1897819
  · exact B1897823
  · exact B1897827
  · exact B1897831
  · exact B1897835
  · exact B1897839
  · exact B1897843
  · exact B1897847
  · exact B1897851
  · exact B1897855
  · exact B1897859
  · exact B1897863
  · exact B1897867
  · exact B1897871
  · exact B1897875
  · exact B1897879
  · exact B1897883
  · exact B1897887
  · exact B1897891
  · exact B1897895
  · exact B1897899
  · exact B1897903
  · exact B1897907
  · exact B1897911
  · exact B1897915
  · exact B1897919
  · exact B1897923
  · exact B1897927
  · exact B1897931
  · exact B1897935
  · exact B1897939
  · exact B1897943
  · exact B1897947
  · exact B1897951
  · exact B1897955
  · exact B1897959
  · exact B1897963
  · exact B1897967
  · exact B1897971
  · exact B1897975
  · exact B1897979
  · exact B1897983
  · exact B1897987
  · exact B1897991
  · exact B1897995
  · exact B1897999
  · exact B1898003
  · exact B1898007
  · exact B1898011
  · exact B1898015
  · exact B1898019
  · exact B1898023
  · exact B1898027
  · exact B1898031
  · exact B1898035
  · exact B1898039
  · exact B1898043
  · exact B1898047
  · exact B1898051
  · exact B1898055
  · exact B1898059
  · exact B1898063
  · exact B1898067
  · exact B1898071
  · exact B1898075
  · exact B1898079
  · exact B1898083
  · exact B1898087
  · exact B1898091
  · exact B1898095
  · exact B1898099
  · exact B1898103
  · exact B1898107
  · exact B1898111
  · exact B1898115
  · exact B1898119
  · exact B1898123
  · exact B1898127
  · exact B1898131
  · exact B1898135
  · exact B1898139
  · exact B1898143
  · exact B1898147
  · exact B1898151
  · exact B1898155
  · exact B1898159
  · exact B1898163
  · exact B1898167
  · exact B1898171
  · exact B1898175
  · exact B1898179
  · exact B1898183
  · exact B1898187
  · exact B1898191
  · exact B1898195
  · exact B1898199
  · exact B1898203
  · exact B1898207
  · exact B1898211
  · exact B1898215
  · exact B1898219
  · exact B1898223
  · exact B1898227
  · exact B1898231
  · exact B1898235
  · exact B1898239
  · exact B1898243
  · exact B1898247
  · exact B1898251
  · exact B1898255
  · exact B1898259
  · exact B1898263
  · exact B1898267
  · exact B1898271
  · exact B1898275
  · exact B1898279
  · exact B1898283
  · exact B1898287
  · exact B1898291
  · exact B1898295
  · exact B1898299
  · exact B1898303
  · exact B1898307
  · exact B1898311
  · exact B1898315
  · exact B1898319
  · exact B1898323
  · exact B1898327
  · exact B1898331
  · exact B1898335
  · exact B1898339
  · exact B1898343
  · exact B1898347
  · exact B1898351
  · exact B1898355
  · exact B1898359
  · exact B1898363
  · exact B1898367
  · exact B1898371
  · exact B1898375
  · exact B1898379
  · exact B1898383
  · exact B1898387
  · exact B1898391
  · exact B1898395
  · exact B1898399
  · exact B1898403
  · exact B1898407
  · exact B1898411
  · exact B1898415
  · exact B1898419
  · exact B1898423
  · exact B1898427
  · exact B1898431
  · exact B1898435
  · exact B1898439
  · exact B1898443
  · exact B1898447
  · exact B1898451
  · exact B1898455
  · exact B1898459
  · exact B1898463
  · exact B1898467
  · exact B1898471
  · exact B1898475
  · exact B1898479
  · exact B1898483
  · exact B1898487
  · exact B1898491
  · exact B1898495
  · exact B1898499
  · exact B1898503
  · exact B1898507
  · exact B1898511
  · exact B1898515
  · exact B1898519
  · exact B1898523
  · exact B1898527
  · exact B1898531
  · exact B1898535
  · exact B1898539
  · exact B1898543
  · exact B1898547
  · exact B1898551
  · exact B1898555
  · exact B1898559
  · exact B1898563
  · exact B1898567
  · exact B1898571
  · exact B1898575
  · exact B1898579
  · exact B1898583
  · exact B1898587
  · exact B1898591
  · exact B1898595
  · exact B1898599
  · exact B1898603
  · exact B1898607
  · exact B1898611
  · exact B1898615
  · exact B1898619
  · exact B1898623
  · exact B1898627
  · exact B1898631
  · exact B1898635
  · exact B1898639
  · exact B1898643
  · exact B1898647
  · exact B1898651
  · exact B1898655
  · exact B1898659
  · exact B1898663
  · exact B1898667
  · exact B1898671
  · exact B1898675
  · exact B1898679
  · exact B1898683
  · exact B1898687
  · exact B1898691
  · exact B1898695
  · exact B1898699
  · exact B1898703
  · exact B1898707
  · exact B1898711
  · exact B1898715
  · exact B1898719
  · exact B1898723
  · exact B1898727
  · exact B1898731
  · exact B1898735
  · exact B1898739
  · exact B1898743
  · exact B1898747
  · exact B1898751
  · exact B1898755
  · exact B1898759
  · exact B1898763
  · exact B1898767
  · exact B1898771
  · exact B1898775
  · exact B1898779
  · exact B1898783
  · exact B1898787
  · exact B1898791
  · exact B1898795
  · exact B1898799
  · exact B1898803
  · exact B1898807
  · exact B1898811
  · exact B1898815
  · exact B1898819
  · exact B1898823
  · exact B1898827
  · exact B1898831
  · exact B1898835
  · exact B1898839
  · exact B1898843
  · exact B1898847
  · exact B1898851
  · exact B1898855
  · exact B1898859
  · exact B1898863
  · exact B1898867
  · exact B1898871
  · exact B1898875
  · exact B1898879
  · exact B1898883
  · exact B1898887
  · exact B1898891
  · exact B1898895
  · exact B1898899
  · exact B1898903
  · exact B1898907
  · exact B1898911
  · exact B1898915
  · exact B1898919
  · exact B1898923
  · exact B1898927
  · exact B1898931
  · exact B1898935
  · exact B1898939
  · exact B1898943
  · exact B1898947
  · exact B1898951
  · exact B1898955
  · exact B1898959
  · exact B1898963
  · exact B1898967
  · exact B1898971
  · exact B1898975
  · exact B1898979
  · exact B1898983
  · exact B1898987
  · exact B1898991
  · exact B1898995
  · exact B1898999
  · exact B1899003
  · exact B1899007
  · exact B1899011
  · exact B1899015
  · exact B1899019
  · exact B1899023
  · exact B1899027
  · exact B1899031
  · exact B1899035
  · exact B1899039
  · exact B1899043
  · exact B1899047
  · exact B1899051
  · exact B1899055
  · exact B1899059
  · exact B1899063
  · exact B1899067
  · exact B1899071
  · exact B1899075
  · exact B1899079
  · exact B1899083
  · exact B1899087
  · exact B1899091
  · exact B1899095
  · exact B1899099
  · exact B1899103
  · exact B1899107
  · exact B1899111
  · exact B1899115
  · exact B1899119
  · exact B1899123
  · exact B1899127
  · exact B1899131
  · exact B1899135
  · exact B1899139
  · exact B1899143
  · exact B1899147
  · exact B1899151
  · exact B1899155
  · exact B1899159
  · exact B1899163
  · exact B1899167
  · exact B1899171
  · exact B1899175
  · exact B1899179
  · exact B1899183
  · exact B1899187
  · exact B1899191
  · exact B1899195
  · exact B1899199
  · exact B1899203
  · exact B1899207
  · exact B1899211
  · exact B1899215
  · exact B1899219
  · exact B1899223
  · exact B1899227
  · exact B1899231
  · exact B1899235
  · exact B1899239
  · exact B1899243
  · exact B1899247
  · exact B1899251
  · exact B1899255
  · exact B1899259
  · exact B1899263
  · exact B1899267
  · exact B1899271
  · exact B1899275
  · exact B1899279
  · exact B1899283
  · exact B1899287
  · exact B1899291
  · exact B1899295
  · exact B1899299
  · exact B1899303
  · exact B1899307
  · exact B1899311
  · exact B1899315
  · exact B1899319
  · exact B1899323
  · exact B1899327
  · exact B1899331
  · exact B1899335
  · exact B1899339
  · exact B1899343
  · exact B1899347
  · exact B1899351
  · exact B1899355
  · exact B1899359
  · exact B1899363
  · exact B1899367
  · exact B1899371
  · exact B1899375
  · exact B1899379
  · exact B1899383
  · exact B1899387
  · exact B1899391
  · exact B1899395
  · exact B1899399
  · exact B1899403
  · exact B1899407
  · exact B1899411
  · exact B1899415
  · exact B1899419
  · exact B1899423
  · exact B1899427
  · exact B1899431
  · exact B1899435
theorem solution (m : ℕ) (hlo : 1897435 ≤ m) (hhi : m ≤ 1899435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 474358 ≤ j := by omega
    have hj2 : j ≤ 474858 := by omega
    have hb : Blo 1897435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
