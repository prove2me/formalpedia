-- Prove2me | solution 1 for syracuse_descends_range_1905435_1907435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:55.479612+00:00
-- url     : https://prove2.me/submissions/9318dbb2-dba1-49ee-98a4-3932b67f7a8a

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

theorem B6867317 : Blo 1905435 6867317 := bbase (se 5 (by rfl) ⟨321905, by rfl⟩ : syracuseStep 6867317 = 643811) (by norm_num)
theorem B4578211 : Blo 1905435 4578211 := bstep (se 1 (by rfl) ⟨3433658, by rfl⟩ : syracuseStep 4578211 = 6867317) B6867317
theorem B24417125 : Blo 1905435 24417125 := bstep (se 4 (by rfl) ⟨2289105, by rfl⟩ : syracuseStep 24417125 = 4578211) B4578211
theorem B16278083 : Blo 1905435 16278083 := bstep (se 1 (by rfl) ⟨12208562, by rfl⟩ : syracuseStep 16278083 = 24417125) B24417125
theorem B10852055 : Blo 1905435 10852055 := bstep (se 1 (by rfl) ⟨8139041, by rfl⟩ : syracuseStep 10852055 = 16278083) B16278083
theorem B7234703 : Blo 1905435 7234703 := bstep (se 1 (by rfl) ⟨5426027, by rfl⟩ : syracuseStep 7234703 = 10852055) B10852055
theorem B4823135 : Blo 1905435 4823135 := bstep (se 1 (by rfl) ⟨3617351, by rfl⟩ : syracuseStep 4823135 = 7234703) B7234703
theorem B3215423 : Blo 1905435 3215423 := bstep (se 1 (by rfl) ⟨2411567, by rfl⟩ : syracuseStep 3215423 = 4823135) B4823135
theorem B2143615 : Blo 1905435 2143615 := bstep (se 1 (by rfl) ⟨1607711, by rfl⟩ : syracuseStep 2143615 = 3215423) B3215423
theorem B2858153 : Blo 1905435 2858153 := bstep (se 2 (by rfl) ⟨1071807, by rfl⟩ : syracuseStep 2858153 = 2143615) B2143615
theorem B1905435 : Blo 1905435 1905435 := bstep (se 1 (by rfl) ⟨1429076, by rfl⟩ : syracuseStep 1905435 = 2858153) B2858153
theorem B4578221 : Blo 1905435 4578221 := bbase (se 3 (by rfl) ⟨858416, by rfl⟩ : syracuseStep 4578221 = 1716833) (by norm_num)
theorem B3052147 : Blo 1905435 3052147 := bstep (se 1 (by rfl) ⟨2289110, by rfl⟩ : syracuseStep 3052147 = 4578221) B4578221
theorem B4069529 : Blo 1905435 4069529 := bstep (se 2 (by rfl) ⟨1526073, by rfl⟩ : syracuseStep 4069529 = 3052147) B3052147
theorem B2713019 : Blo 1905435 2713019 := bstep (se 1 (by rfl) ⟨2034764, by rfl⟩ : syracuseStep 2713019 = 4069529) B4069529
theorem B7234717 : Blo 1905435 7234717 := bstep (se 3 (by rfl) ⟨1356509, by rfl⟩ : syracuseStep 7234717 = 2713019) B2713019
theorem B9646289 : Blo 1905435 9646289 := bstep (se 2 (by rfl) ⟨3617358, by rfl⟩ : syracuseStep 9646289 = 7234717) B7234717
theorem B6430859 : Blo 1905435 6430859 := bstep (se 1 (by rfl) ⟨4823144, by rfl⟩ : syracuseStep 6430859 = 9646289) B9646289
theorem B4287239 : Blo 1905435 4287239 := bstep (se 1 (by rfl) ⟨3215429, by rfl⟩ : syracuseStep 4287239 = 6430859) B6430859
theorem B2858159 : Blo 1905435 2858159 := bstep (se 1 (by rfl) ⟨2143619, by rfl⟩ : syracuseStep 2858159 = 4287239) B4287239
theorem B1905439 : Blo 1905435 1905439 := bstep (se 1 (by rfl) ⟨1429079, by rfl⟩ : syracuseStep 1905439 = 2858159) B2858159
theorem B2858165 : Blo 1905435 2858165 := bbase (se 5 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 2858165 = 267953) (by norm_num)
theorem B1905443 : Blo 1905435 1905443 := bstep (se 1 (by rfl) ⟨1429082, by rfl⟩ : syracuseStep 1905443 = 2858165) B2858165
theorem B4823165 : Blo 1905435 4823165 := bbase (se 3 (by rfl) ⟨904343, by rfl⟩ : syracuseStep 4823165 = 1808687) (by norm_num)
theorem B3215443 : Blo 1905435 3215443 := bstep (se 1 (by rfl) ⟨2411582, by rfl⟩ : syracuseStep 3215443 = 4823165) B4823165
theorem B4287257 : Blo 1905435 4287257 := bstep (se 2 (by rfl) ⟨1607721, by rfl⟩ : syracuseStep 4287257 = 3215443) B3215443
theorem B2858171 : Blo 1905435 2858171 := bstep (se 1 (by rfl) ⟨2143628, by rfl⟩ : syracuseStep 2858171 = 4287257) B4287257
theorem B1905447 : Blo 1905435 1905447 := bstep (se 1 (by rfl) ⟨1429085, by rfl⟩ : syracuseStep 1905447 = 2858171) B2858171
theorem B2143633 : Blo 1905435 2143633 := bbase (se 2 (by rfl) ⟨803862, by rfl⟩ : syracuseStep 2143633 = 1607725) (by norm_num)
theorem B2858177 : Blo 1905435 2858177 := bstep (se 2 (by rfl) ⟨1071816, by rfl⟩ : syracuseStep 2858177 = 2143633) B2143633
theorem B1905451 : Blo 1905435 1905451 := bstep (se 1 (by rfl) ⟨1429088, by rfl⟩ : syracuseStep 1905451 = 2858177) B2858177
theorem B3617389 : Blo 1905435 3617389 := bbase (se 3 (by rfl) ⟨678260, by rfl⟩ : syracuseStep 3617389 = 1356521) (by norm_num)
theorem B4823185 : Blo 1905435 4823185 := bstep (se 2 (by rfl) ⟨1808694, by rfl⟩ : syracuseStep 4823185 = 3617389) B3617389
theorem B6430913 : Blo 1905435 6430913 := bstep (se 2 (by rfl) ⟨2411592, by rfl⟩ : syracuseStep 6430913 = 4823185) B4823185
theorem B4287275 : Blo 1905435 4287275 := bstep (se 1 (by rfl) ⟨3215456, by rfl⟩ : syracuseStep 4287275 = 6430913) B6430913
theorem B2858183 : Blo 1905435 2858183 := bstep (se 1 (by rfl) ⟨2143637, by rfl⟩ : syracuseStep 2858183 = 4287275) B4287275
theorem B1905455 : Blo 1905435 1905455 := bstep (se 1 (by rfl) ⟨1429091, by rfl⟩ : syracuseStep 1905455 = 2858183) B2858183
theorem B2858189 : Blo 1905435 2858189 := bbase (se 3 (by rfl) ⟨535910, by rfl⟩ : syracuseStep 2858189 = 1071821) (by norm_num)
theorem B1905459 : Blo 1905435 1905459 := bstep (se 1 (by rfl) ⟨1429094, by rfl⟩ : syracuseStep 1905459 = 2858189) B2858189
theorem B4287293 : Blo 1905435 4287293 := bbase (se 3 (by rfl) ⟨803867, by rfl⟩ : syracuseStep 4287293 = 1607735) (by norm_num)
theorem B2858195 : Blo 1905435 2858195 := bstep (se 1 (by rfl) ⟨2143646, by rfl⟩ : syracuseStep 2858195 = 4287293) B4287293
theorem B1905463 : Blo 1905435 1905463 := bstep (se 1 (by rfl) ⟨1429097, by rfl⟩ : syracuseStep 1905463 = 2858195) B2858195
theorem B3215477 : Blo 1905435 3215477 := bbase (se 5 (by rfl) ⟨150725, by rfl⟩ : syracuseStep 3215477 = 301451) (by norm_num)
theorem B2143651 : Blo 1905435 2143651 := bstep (se 1 (by rfl) ⟨1607738, by rfl⟩ : syracuseStep 2143651 = 3215477) B3215477
theorem B2858201 : Blo 1905435 2858201 := bstep (se 2 (by rfl) ⟨1071825, by rfl⟩ : syracuseStep 2858201 = 2143651) B2143651
theorem B1905467 : Blo 1905435 1905467 := bstep (se 1 (by rfl) ⟨1429100, by rfl⟩ : syracuseStep 1905467 = 2858201) B2858201
theorem B4069597 : Blo 1905435 4069597 := bbase (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) (by norm_num)
theorem B5426129 : Blo 1905435 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B14469677 : Blo 1905435 14469677 := bstep (se 3 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 14469677 = 5426129) B5426129
theorem B9646451 : Blo 1905435 9646451 := bstep (se 1 (by rfl) ⟨7234838, by rfl⟩ : syracuseStep 9646451 = 14469677) B14469677
theorem B6430967 : Blo 1905435 6430967 := bstep (se 1 (by rfl) ⟨4823225, by rfl⟩ : syracuseStep 6430967 = 9646451) B9646451
theorem B4287311 : Blo 1905435 4287311 := bstep (se 1 (by rfl) ⟨3215483, by rfl⟩ : syracuseStep 4287311 = 6430967) B6430967
theorem B2858207 : Blo 1905435 2858207 := bstep (se 1 (by rfl) ⟨2143655, by rfl⟩ : syracuseStep 2858207 = 4287311) B4287311
theorem B1905471 : Blo 1905435 1905471 := bstep (se 1 (by rfl) ⟨1429103, by rfl⟩ : syracuseStep 1905471 = 2858207) B2858207
theorem B2858213 : Blo 1905435 2858213 := bbase (se 4 (by rfl) ⟨267957, by rfl⟩ : syracuseStep 2858213 = 535915) (by norm_num)
theorem B1905475 : Blo 1905435 1905475 := bstep (se 1 (by rfl) ⟨1429106, by rfl⟩ : syracuseStep 1905475 = 2858213) B2858213
theorem B3915661 : Blo 1905435 3915661 := bbase (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) (by norm_num)
theorem B5220881 : Blo 1905435 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B3480587 : Blo 1905435 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B2320391 : Blo 1905435 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B6187709 : Blo 1905435 6187709 := bstep (se 3 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 6187709 = 2320391) B2320391
theorem B16500557 : Blo 1905435 16500557 := bstep (se 3 (by rfl) ⟨3093854, by rfl⟩ : syracuseStep 16500557 = 6187709) B6187709
theorem B11000371 : Blo 1905435 11000371 := bstep (se 1 (by rfl) ⟨8250278, by rfl⟩ : syracuseStep 11000371 = 16500557) B16500557
theorem B14667161 : Blo 1905435 14667161 := bstep (se 2 (by rfl) ⟨5500185, by rfl⟩ : syracuseStep 14667161 = 11000371) B11000371
theorem B39112429 : Blo 1905435 39112429 := bstep (se 3 (by rfl) ⟨7333580, by rfl⟩ : syracuseStep 39112429 = 14667161) B14667161
theorem B52149905 : Blo 1905435 52149905 := bstep (se 2 (by rfl) ⟨19556214, by rfl⟩ : syracuseStep 52149905 = 39112429) B39112429
theorem B34766603 : Blo 1905435 34766603 := bstep (se 1 (by rfl) ⟨26074952, by rfl⟩ : syracuseStep 34766603 = 52149905) B52149905
theorem B23177735 : Blo 1905435 23177735 := bstep (se 1 (by rfl) ⟨17383301, by rfl⟩ : syracuseStep 23177735 = 34766603) B34766603
theorem B15451823 : Blo 1905435 15451823 := bstep (se 1 (by rfl) ⟨11588867, by rfl⟩ : syracuseStep 15451823 = 23177735) B23177735
theorem B10301215 : Blo 1905435 10301215 := bstep (se 1 (by rfl) ⟨7725911, by rfl⟩ : syracuseStep 10301215 = 15451823) B15451823
theorem B13734953 : Blo 1905435 13734953 := bstep (se 2 (by rfl) ⟨5150607, by rfl⟩ : syracuseStep 13734953 = 10301215) B10301215
theorem B9156635 : Blo 1905435 9156635 := bstep (se 1 (by rfl) ⟨6867476, by rfl⟩ : syracuseStep 9156635 = 13734953) B13734953
theorem B6104423 : Blo 1905435 6104423 := bstep (se 1 (by rfl) ⟨4578317, by rfl⟩ : syracuseStep 6104423 = 9156635) B9156635
theorem B4069615 : Blo 1905435 4069615 := bstep (se 1 (by rfl) ⟨3052211, by rfl⟩ : syracuseStep 4069615 = 6104423) B6104423
theorem B5426153 : Blo 1905435 5426153 := bstep (se 2 (by rfl) ⟨2034807, by rfl⟩ : syracuseStep 5426153 = 4069615) B4069615
theorem B3617435 : Blo 1905435 3617435 := bstep (se 1 (by rfl) ⟨2713076, by rfl⟩ : syracuseStep 3617435 = 5426153) B5426153
theorem B2411623 : Blo 1905435 2411623 := bstep (se 1 (by rfl) ⟨1808717, by rfl⟩ : syracuseStep 2411623 = 3617435) B3617435
theorem B3215497 : Blo 1905435 3215497 := bstep (se 2 (by rfl) ⟨1205811, by rfl⟩ : syracuseStep 3215497 = 2411623) B2411623
theorem B4287329 : Blo 1905435 4287329 := bstep (se 2 (by rfl) ⟨1607748, by rfl⟩ : syracuseStep 4287329 = 3215497) B3215497
theorem B2858219 : Blo 1905435 2858219 := bstep (se 1 (by rfl) ⟨2143664, by rfl⟩ : syracuseStep 2858219 = 4287329) B4287329
theorem B1905479 : Blo 1905435 1905479 := bstep (se 1 (by rfl) ⟨1429109, by rfl⟩ : syracuseStep 1905479 = 2858219) B2858219
theorem B2143669 : Blo 1905435 2143669 := bbase (se 5 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 2143669 = 200969) (by norm_num)
theorem B2858225 : Blo 1905435 2858225 := bstep (se 2 (by rfl) ⟨1071834, by rfl⟩ : syracuseStep 2858225 = 2143669) B2143669
theorem B1905483 : Blo 1905435 1905483 := bstep (se 1 (by rfl) ⟨1429112, by rfl⟩ : syracuseStep 1905483 = 2858225) B2858225
theorem B2411633 : Blo 1905435 2411633 := bbase (se 2 (by rfl) ⟨904362, by rfl⟩ : syracuseStep 2411633 = 1808725) (by norm_num)
theorem B6431021 : Blo 1905435 6431021 := bstep (se 3 (by rfl) ⟨1205816, by rfl⟩ : syracuseStep 6431021 = 2411633) B2411633
theorem B4287347 : Blo 1905435 4287347 := bstep (se 1 (by rfl) ⟨3215510, by rfl⟩ : syracuseStep 4287347 = 6431021) B6431021
theorem B2858231 : Blo 1905435 2858231 := bstep (se 1 (by rfl) ⟨2143673, by rfl⟩ : syracuseStep 2858231 = 4287347) B4287347
theorem B1905487 : Blo 1905435 1905487 := bstep (se 1 (by rfl) ⟨1429115, by rfl⟩ : syracuseStep 1905487 = 2858231) B2858231
theorem B2858237 : Blo 1905435 2858237 := bbase (se 3 (by rfl) ⟨535919, by rfl⟩ : syracuseStep 2858237 = 1071839) (by norm_num)
theorem B1905491 : Blo 1905435 1905491 := bstep (se 1 (by rfl) ⟨1429118, by rfl⟩ : syracuseStep 1905491 = 2858237) B2858237
theorem B4287365 : Blo 1905435 4287365 := bbase (se 4 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 4287365 = 803881) (by norm_num)
theorem B2858243 : Blo 1905435 2858243 := bstep (se 1 (by rfl) ⟨2143682, by rfl⟩ : syracuseStep 2858243 = 4287365) B4287365
theorem B1905495 : Blo 1905435 1905495 := bstep (se 1 (by rfl) ⟨1429121, by rfl⟩ : syracuseStep 1905495 = 2858243) B2858243
theorem B2034829 : Blo 1905435 2034829 := bbase (se 3 (by rfl) ⟨381530, by rfl⟩ : syracuseStep 2034829 = 763061) (by norm_num)
theorem B2713105 : Blo 1905435 2713105 := bstep (se 2 (by rfl) ⟨1017414, by rfl⟩ : syracuseStep 2713105 = 2034829) B2034829
theorem B3617473 : Blo 1905435 3617473 := bstep (se 2 (by rfl) ⟨1356552, by rfl⟩ : syracuseStep 3617473 = 2713105) B2713105
theorem B4823297 : Blo 1905435 4823297 := bstep (se 2 (by rfl) ⟨1808736, by rfl⟩ : syracuseStep 4823297 = 3617473) B3617473
theorem B3215531 : Blo 1905435 3215531 := bstep (se 1 (by rfl) ⟨2411648, by rfl⟩ : syracuseStep 3215531 = 4823297) B4823297
theorem B2143687 : Blo 1905435 2143687 := bstep (se 1 (by rfl) ⟨1607765, by rfl⟩ : syracuseStep 2143687 = 3215531) B3215531
theorem B2858249 : Blo 1905435 2858249 := bstep (se 2 (by rfl) ⟨1071843, by rfl⟩ : syracuseStep 2858249 = 2143687) B2143687
theorem B1905499 : Blo 1905435 1905499 := bstep (se 1 (by rfl) ⟨1429124, by rfl⟩ : syracuseStep 1905499 = 2858249) B2858249
theorem B9646613 : Blo 1905435 9646613 := bbase (se 6 (by rfl) ⟨226092, by rfl⟩ : syracuseStep 9646613 = 452185) (by norm_num)
theorem B6431075 : Blo 1905435 6431075 := bstep (se 1 (by rfl) ⟨4823306, by rfl⟩ : syracuseStep 6431075 = 9646613) B9646613
theorem B4287383 : Blo 1905435 4287383 := bstep (se 1 (by rfl) ⟨3215537, by rfl⟩ : syracuseStep 4287383 = 6431075) B6431075
theorem B2858255 : Blo 1905435 2858255 := bstep (se 1 (by rfl) ⟨2143691, by rfl⟩ : syracuseStep 2858255 = 4287383) B4287383
theorem B1905503 : Blo 1905435 1905503 := bstep (se 1 (by rfl) ⟨1429127, by rfl⟩ : syracuseStep 1905503 = 2858255) B2858255
theorem B2858261 : Blo 1905435 2858261 := bbase (se 6 (by rfl) ⟨66990, by rfl⟩ : syracuseStep 2858261 = 133981) (by norm_num)
theorem B1905507 : Blo 1905435 1905507 := bstep (se 1 (by rfl) ⟨1429130, by rfl⟩ : syracuseStep 1905507 = 2858261) B2858261
theorem B5150693 : Blo 1905435 5150693 := bbase (se 4 (by rfl) ⟨482877, by rfl⟩ : syracuseStep 5150693 = 965755) (by norm_num)
theorem B3433795 : Blo 1905435 3433795 := bstep (se 1 (by rfl) ⟨2575346, by rfl⟩ : syracuseStep 3433795 = 5150693) B5150693
theorem B18313573 : Blo 1905435 18313573 := bstep (se 4 (by rfl) ⟨1716897, by rfl⟩ : syracuseStep 18313573 = 3433795) B3433795
theorem B24418097 : Blo 1905435 24418097 := bstep (se 2 (by rfl) ⟨9156786, by rfl⟩ : syracuseStep 24418097 = 18313573) B18313573
theorem B16278731 : Blo 1905435 16278731 := bstep (se 1 (by rfl) ⟨12209048, by rfl⟩ : syracuseStep 16278731 = 24418097) B24418097
theorem B10852487 : Blo 1905435 10852487 := bstep (se 1 (by rfl) ⟨8139365, by rfl⟩ : syracuseStep 10852487 = 16278731) B16278731
theorem B7234991 : Blo 1905435 7234991 := bstep (se 1 (by rfl) ⟨5426243, by rfl⟩ : syracuseStep 7234991 = 10852487) B10852487
theorem B4823327 : Blo 1905435 4823327 := bstep (se 1 (by rfl) ⟨3617495, by rfl⟩ : syracuseStep 4823327 = 7234991) B7234991
theorem B3215551 : Blo 1905435 3215551 := bstep (se 1 (by rfl) ⟨2411663, by rfl⟩ : syracuseStep 3215551 = 4823327) B4823327
theorem B4287401 : Blo 1905435 4287401 := bstep (se 2 (by rfl) ⟨1607775, by rfl⟩ : syracuseStep 4287401 = 3215551) B3215551
theorem B2858267 : Blo 1905435 2858267 := bstep (se 1 (by rfl) ⟨2143700, by rfl⟩ : syracuseStep 2858267 = 4287401) B4287401
theorem B1905511 : Blo 1905435 1905511 := bstep (se 1 (by rfl) ⟨1429133, by rfl⟩ : syracuseStep 1905511 = 2858267) B2858267
theorem B2143705 : Blo 1905435 2143705 := bbase (se 2 (by rfl) ⟨803889, by rfl⟩ : syracuseStep 2143705 = 1607779) (by norm_num)
theorem B2858273 : Blo 1905435 2858273 := bstep (se 2 (by rfl) ⟨1071852, by rfl⟩ : syracuseStep 2858273 = 2143705) B2143705
theorem B1905515 : Blo 1905435 1905515 := bstep (se 1 (by rfl) ⟨1429136, by rfl⟩ : syracuseStep 1905515 = 2858273) B2858273
theorem B2713133 : Blo 1905435 2713133 := bbase (se 3 (by rfl) ⟨508712, by rfl⟩ : syracuseStep 2713133 = 1017425) (by norm_num)
theorem B7235021 : Blo 1905435 7235021 := bstep (se 3 (by rfl) ⟨1356566, by rfl⟩ : syracuseStep 7235021 = 2713133) B2713133
theorem B4823347 : Blo 1905435 4823347 := bstep (se 1 (by rfl) ⟨3617510, by rfl⟩ : syracuseStep 4823347 = 7235021) B7235021
theorem B6431129 : Blo 1905435 6431129 := bstep (se 2 (by rfl) ⟨2411673, by rfl⟩ : syracuseStep 6431129 = 4823347) B4823347
theorem B4287419 : Blo 1905435 4287419 := bstep (se 1 (by rfl) ⟨3215564, by rfl⟩ : syracuseStep 4287419 = 6431129) B6431129
theorem B2858279 : Blo 1905435 2858279 := bstep (se 1 (by rfl) ⟨2143709, by rfl⟩ : syracuseStep 2858279 = 4287419) B4287419
theorem B1905519 : Blo 1905435 1905519 := bstep (se 1 (by rfl) ⟨1429139, by rfl⟩ : syracuseStep 1905519 = 2858279) B2858279
theorem B2858285 : Blo 1905435 2858285 := bbase (se 3 (by rfl) ⟨535928, by rfl⟩ : syracuseStep 2858285 = 1071857) (by norm_num)
theorem B1905523 : Blo 1905435 1905523 := bstep (se 1 (by rfl) ⟨1429142, by rfl⟩ : syracuseStep 1905523 = 2858285) B2858285
theorem B4287437 : Blo 1905435 4287437 := bbase (se 3 (by rfl) ⟨803894, by rfl⟩ : syracuseStep 4287437 = 1607789) (by norm_num)
theorem B2858291 : Blo 1905435 2858291 := bstep (se 1 (by rfl) ⟨2143718, by rfl⟩ : syracuseStep 2858291 = 4287437) B4287437
theorem B1905527 : Blo 1905435 1905527 := bstep (se 1 (by rfl) ⟨1429145, by rfl⟩ : syracuseStep 1905527 = 2858291) B2858291
theorem B2411689 : Blo 1905435 2411689 := bbase (se 2 (by rfl) ⟨904383, by rfl⟩ : syracuseStep 2411689 = 1808767) (by norm_num)
theorem B3215585 : Blo 1905435 3215585 := bstep (se 2 (by rfl) ⟨1205844, by rfl⟩ : syracuseStep 3215585 = 2411689) B2411689
theorem B2143723 : Blo 1905435 2143723 := bstep (se 1 (by rfl) ⟨1607792, by rfl⟩ : syracuseStep 2143723 = 3215585) B3215585
theorem B2858297 : Blo 1905435 2858297 := bstep (se 2 (by rfl) ⟨1071861, by rfl⟩ : syracuseStep 2858297 = 2143723) B2143723
theorem B1905531 : Blo 1905435 1905531 := bstep (se 1 (by rfl) ⟨1429148, by rfl⟩ : syracuseStep 1905531 = 2858297) B2858297
theorem B9156901 : Blo 1905435 9156901 := bbase (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) (by norm_num)
theorem B12209201 : Blo 1905435 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B8139467 : Blo 1905435 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B21705245 : Blo 1905435 21705245 := bstep (se 3 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 21705245 = 8139467) B8139467
theorem B14470163 : Blo 1905435 14470163 := bstep (se 1 (by rfl) ⟨10852622, by rfl⟩ : syracuseStep 14470163 = 21705245) B21705245
theorem B9646775 : Blo 1905435 9646775 := bstep (se 1 (by rfl) ⟨7235081, by rfl⟩ : syracuseStep 9646775 = 14470163) B14470163
theorem B6431183 : Blo 1905435 6431183 := bstep (se 1 (by rfl) ⟨4823387, by rfl⟩ : syracuseStep 6431183 = 9646775) B9646775
theorem B4287455 : Blo 1905435 4287455 := bstep (se 1 (by rfl) ⟨3215591, by rfl⟩ : syracuseStep 4287455 = 6431183) B6431183
theorem B2858303 : Blo 1905435 2858303 := bstep (se 1 (by rfl) ⟨2143727, by rfl⟩ : syracuseStep 2858303 = 4287455) B4287455
theorem B1905535 : Blo 1905435 1905535 := bstep (se 1 (by rfl) ⟨1429151, by rfl⟩ : syracuseStep 1905535 = 2858303) B2858303
theorem B2858309 : Blo 1905435 2858309 := bbase (se 4 (by rfl) ⟨267966, by rfl⟩ : syracuseStep 2858309 = 535933) (by norm_num)
theorem B1905539 : Blo 1905435 1905539 := bstep (se 1 (by rfl) ⟨1429154, by rfl⟩ : syracuseStep 1905539 = 2858309) B2858309
theorem B3215605 : Blo 1905435 3215605 := bbase (se 5 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 3215605 = 301463) (by norm_num)
theorem B4287473 : Blo 1905435 4287473 := bstep (se 2 (by rfl) ⟨1607802, by rfl⟩ : syracuseStep 4287473 = 3215605) B3215605
theorem B2858315 : Blo 1905435 2858315 := bstep (se 1 (by rfl) ⟨2143736, by rfl⟩ : syracuseStep 2858315 = 4287473) B4287473
theorem B1905543 : Blo 1905435 1905543 := bstep (se 1 (by rfl) ⟨1429157, by rfl⟩ : syracuseStep 1905543 = 2858315) B2858315
theorem B2143741 : Blo 1905435 2143741 := bbase (se 3 (by rfl) ⟨401951, by rfl⟩ : syracuseStep 2143741 = 803903) (by norm_num)
theorem B2858321 : Blo 1905435 2858321 := bstep (se 2 (by rfl) ⟨1071870, by rfl⟩ : syracuseStep 2858321 = 2143741) B2143741
theorem B1905547 : Blo 1905435 1905547 := bstep (se 1 (by rfl) ⟨1429160, by rfl⟩ : syracuseStep 1905547 = 2858321) B2858321
theorem B6431237 : Blo 1905435 6431237 := bbase (se 4 (by rfl) ⟨602928, by rfl⟩ : syracuseStep 6431237 = 1205857) (by norm_num)
theorem B4287491 : Blo 1905435 4287491 := bstep (se 1 (by rfl) ⟨3215618, by rfl⟩ : syracuseStep 4287491 = 6431237) B6431237
theorem B2858327 : Blo 1905435 2858327 := bstep (se 1 (by rfl) ⟨2143745, by rfl⟩ : syracuseStep 2858327 = 4287491) B4287491
theorem B1905551 : Blo 1905435 1905551 := bstep (se 1 (by rfl) ⟨1429163, by rfl⟩ : syracuseStep 1905551 = 2858327) B2858327
theorem B2858333 : Blo 1905435 2858333 := bbase (se 3 (by rfl) ⟨535937, by rfl⟩ : syracuseStep 2858333 = 1071875) (by norm_num)
theorem B1905555 : Blo 1905435 1905555 := bstep (se 1 (by rfl) ⟨1429166, by rfl⟩ : syracuseStep 1905555 = 2858333) B2858333
theorem B4287509 : Blo 1905435 4287509 := bbase (se 6 (by rfl) ⟨100488, by rfl⟩ : syracuseStep 4287509 = 200977) (by norm_num)
theorem B2858339 : Blo 1905435 2858339 := bstep (se 1 (by rfl) ⟨2143754, by rfl⟩ : syracuseStep 2858339 = 4287509) B4287509
theorem B1905559 : Blo 1905435 1905559 := bstep (se 1 (by rfl) ⟨1429169, by rfl⟩ : syracuseStep 1905559 = 2858339) B2858339
theorem B7235189 : Blo 1905435 7235189 := bbase (se 5 (by rfl) ⟨339149, by rfl⟩ : syracuseStep 7235189 = 678299) (by norm_num)
theorem B4823459 : Blo 1905435 4823459 := bstep (se 1 (by rfl) ⟨3617594, by rfl⟩ : syracuseStep 4823459 = 7235189) B7235189
theorem B3215639 : Blo 1905435 3215639 := bstep (se 1 (by rfl) ⟨2411729, by rfl⟩ : syracuseStep 3215639 = 4823459) B4823459
theorem B2143759 : Blo 1905435 2143759 := bstep (se 1 (by rfl) ⟨1607819, by rfl⟩ : syracuseStep 2143759 = 3215639) B3215639
theorem B2858345 : Blo 1905435 2858345 := bstep (se 2 (by rfl) ⟨1071879, by rfl⟩ : syracuseStep 2858345 = 2143759) B2143759
theorem B1905563 : Blo 1905435 1905563 := bstep (se 1 (by rfl) ⟨1429172, by rfl⟩ : syracuseStep 1905563 = 2858345) B2858345
theorem B2034901 : Blo 1905435 2034901 := bbase (se 7 (by rfl) ⟨23846, by rfl⟩ : syracuseStep 2034901 = 47693) (by norm_num)
theorem B10852805 : Blo 1905435 10852805 := bstep (se 4 (by rfl) ⟨1017450, by rfl⟩ : syracuseStep 10852805 = 2034901) B2034901
theorem B7235203 : Blo 1905435 7235203 := bstep (se 1 (by rfl) ⟨5426402, by rfl⟩ : syracuseStep 7235203 = 10852805) B10852805
theorem B9646937 : Blo 1905435 9646937 := bstep (se 2 (by rfl) ⟨3617601, by rfl⟩ : syracuseStep 9646937 = 7235203) B7235203
theorem B6431291 : Blo 1905435 6431291 := bstep (se 1 (by rfl) ⟨4823468, by rfl⟩ : syracuseStep 6431291 = 9646937) B9646937
theorem B4287527 : Blo 1905435 4287527 := bstep (se 1 (by rfl) ⟨3215645, by rfl⟩ : syracuseStep 4287527 = 6431291) B6431291
theorem B2858351 : Blo 1905435 2858351 := bstep (se 1 (by rfl) ⟨2143763, by rfl⟩ : syracuseStep 2858351 = 4287527) B4287527
theorem B1905567 : Blo 1905435 1905567 := bstep (se 1 (by rfl) ⟨1429175, by rfl⟩ : syracuseStep 1905567 = 2858351) B2858351
theorem B2858357 : Blo 1905435 2858357 := bbase (se 5 (by rfl) ⟨133985, by rfl⟩ : syracuseStep 2858357 = 267971) (by norm_num)
theorem B1905571 : Blo 1905435 1905571 := bstep (se 1 (by rfl) ⟨1429178, by rfl⟩ : syracuseStep 1905571 = 2858357) B2858357
theorem B2713213 : Blo 1905435 2713213 := bbase (se 3 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 2713213 = 1017455) (by norm_num)
theorem B3617617 : Blo 1905435 3617617 := bstep (se 2 (by rfl) ⟨1356606, by rfl⟩ : syracuseStep 3617617 = 2713213) B2713213
theorem B4823489 : Blo 1905435 4823489 := bstep (se 2 (by rfl) ⟨1808808, by rfl⟩ : syracuseStep 4823489 = 3617617) B3617617
theorem B3215659 : Blo 1905435 3215659 := bstep (se 1 (by rfl) ⟨2411744, by rfl⟩ : syracuseStep 3215659 = 4823489) B4823489
theorem B4287545 : Blo 1905435 4287545 := bstep (se 2 (by rfl) ⟨1607829, by rfl⟩ : syracuseStep 4287545 = 3215659) B3215659
theorem B2858363 : Blo 1905435 2858363 := bstep (se 1 (by rfl) ⟨2143772, by rfl⟩ : syracuseStep 2858363 = 4287545) B4287545
theorem B1905575 : Blo 1905435 1905575 := bstep (se 1 (by rfl) ⟨1429181, by rfl⟩ : syracuseStep 1905575 = 2858363) B2858363
theorem B2143777 : Blo 1905435 2143777 := bbase (se 2 (by rfl) ⟨803916, by rfl⟩ : syracuseStep 2143777 = 1607833) (by norm_num)
theorem B2858369 : Blo 1905435 2858369 := bstep (se 2 (by rfl) ⟨1071888, by rfl⟩ : syracuseStep 2858369 = 2143777) B2143777
theorem B1905579 : Blo 1905435 1905579 := bstep (se 1 (by rfl) ⟨1429184, by rfl⟩ : syracuseStep 1905579 = 2858369) B2858369
theorem B4823509 : Blo 1905435 4823509 := bbase (se 7 (by rfl) ⟨56525, by rfl⟩ : syracuseStep 4823509 = 113051) (by norm_num)
theorem B6431345 : Blo 1905435 6431345 := bstep (se 2 (by rfl) ⟨2411754, by rfl⟩ : syracuseStep 6431345 = 4823509) B4823509
theorem B4287563 : Blo 1905435 4287563 := bstep (se 1 (by rfl) ⟨3215672, by rfl⟩ : syracuseStep 4287563 = 6431345) B6431345
theorem B2858375 : Blo 1905435 2858375 := bstep (se 1 (by rfl) ⟨2143781, by rfl⟩ : syracuseStep 2858375 = 4287563) B4287563
theorem B1905583 : Blo 1905435 1905583 := bstep (se 1 (by rfl) ⟨1429187, by rfl⟩ : syracuseStep 1905583 = 2858375) B2858375
theorem B2858381 : Blo 1905435 2858381 := bbase (se 3 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 2858381 = 1071893) (by norm_num)
theorem B1905587 : Blo 1905435 1905587 := bstep (se 1 (by rfl) ⟨1429190, by rfl⟩ : syracuseStep 1905587 = 2858381) B2858381
theorem B4287581 : Blo 1905435 4287581 := bbase (se 3 (by rfl) ⟨803921, by rfl⟩ : syracuseStep 4287581 = 1607843) (by norm_num)
theorem B2858387 : Blo 1905435 2858387 := bstep (se 1 (by rfl) ⟨2143790, by rfl⟩ : syracuseStep 2858387 = 4287581) B4287581
theorem B1905591 : Blo 1905435 1905591 := bstep (se 1 (by rfl) ⟨1429193, by rfl⟩ : syracuseStep 1905591 = 2858387) B2858387
theorem B3215693 : Blo 1905435 3215693 := bbase (se 3 (by rfl) ⟨602942, by rfl⟩ : syracuseStep 3215693 = 1205885) (by norm_num)
theorem B2143795 : Blo 1905435 2143795 := bstep (se 1 (by rfl) ⟨1607846, by rfl⟩ : syracuseStep 2143795 = 3215693) B3215693
theorem B2858393 : Blo 1905435 2858393 := bstep (se 2 (by rfl) ⟨1071897, by rfl⟩ : syracuseStep 2858393 = 2143795) B2143795
theorem B1905595 : Blo 1905435 1905595 := bstep (se 1 (by rfl) ⟨1429196, by rfl⟩ : syracuseStep 1905595 = 2858393) B2858393
theorem B2444681 : Blo 1905435 2444681 := bbase (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) (by norm_num)
theorem B6519149 : Blo 1905435 6519149 := bstep (se 3 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 6519149 = 2444681) B2444681
theorem B4346099 : Blo 1905435 4346099 := bstep (se 1 (by rfl) ⟨3259574, by rfl⟩ : syracuseStep 4346099 = 6519149) B6519149
theorem B2897399 : Blo 1905435 2897399 := bstep (se 1 (by rfl) ⟨2173049, by rfl⟩ : syracuseStep 2897399 = 4346099) B4346099
theorem B1931599 : Blo 1905435 1931599 := bstep (se 1 (by rfl) ⟨1448699, by rfl⟩ : syracuseStep 1931599 = 2897399) B2897399
theorem B2575465 : Blo 1905435 2575465 := bstep (se 2 (by rfl) ⟨965799, by rfl⟩ : syracuseStep 2575465 = 1931599) B1931599
theorem B13735813 : Blo 1905435 13735813 := bstep (se 4 (by rfl) ⟨1287732, by rfl⟩ : syracuseStep 13735813 = 2575465) B2575465
theorem B18314417 : Blo 1905435 18314417 := bstep (se 2 (by rfl) ⟨6867906, by rfl⟩ : syracuseStep 18314417 = 13735813) B13735813
theorem B12209611 : Blo 1905435 12209611 := bstep (se 1 (by rfl) ⟨9157208, by rfl⟩ : syracuseStep 12209611 = 18314417) B18314417
theorem B16279481 : Blo 1905435 16279481 := bstep (se 2 (by rfl) ⟨6104805, by rfl⟩ : syracuseStep 16279481 = 12209611) B12209611
theorem B10852987 : Blo 1905435 10852987 := bstep (se 1 (by rfl) ⟨8139740, by rfl⟩ : syracuseStep 10852987 = 16279481) B16279481
theorem B14470649 : Blo 1905435 14470649 := bstep (se 2 (by rfl) ⟨5426493, by rfl⟩ : syracuseStep 14470649 = 10852987) B10852987
theorem B9647099 : Blo 1905435 9647099 := bstep (se 1 (by rfl) ⟨7235324, by rfl⟩ : syracuseStep 9647099 = 14470649) B14470649
theorem B6431399 : Blo 1905435 6431399 := bstep (se 1 (by rfl) ⟨4823549, by rfl⟩ : syracuseStep 6431399 = 9647099) B9647099
theorem B4287599 : Blo 1905435 4287599 := bstep (se 1 (by rfl) ⟨3215699, by rfl⟩ : syracuseStep 4287599 = 6431399) B6431399
theorem B2858399 : Blo 1905435 2858399 := bstep (se 1 (by rfl) ⟨2143799, by rfl⟩ : syracuseStep 2858399 = 4287599) B4287599
theorem B1905599 : Blo 1905435 1905599 := bstep (se 1 (by rfl) ⟨1429199, by rfl⟩ : syracuseStep 1905599 = 2858399) B2858399
theorem B2858405 : Blo 1905435 2858405 := bbase (se 4 (by rfl) ⟨267975, by rfl⟩ : syracuseStep 2858405 = 535951) (by norm_num)
theorem B1905603 : Blo 1905435 1905603 := bstep (se 1 (by rfl) ⟨1429202, by rfl⟩ : syracuseStep 1905603 = 2858405) B2858405
theorem B2411785 : Blo 1905435 2411785 := bbase (se 2 (by rfl) ⟨904419, by rfl⟩ : syracuseStep 2411785 = 1808839) (by norm_num)
theorem B3215713 : Blo 1905435 3215713 := bstep (se 2 (by rfl) ⟨1205892, by rfl⟩ : syracuseStep 3215713 = 2411785) B2411785
theorem B4287617 : Blo 1905435 4287617 := bstep (se 2 (by rfl) ⟨1607856, by rfl⟩ : syracuseStep 4287617 = 3215713) B3215713
theorem B2858411 : Blo 1905435 2858411 := bstep (se 1 (by rfl) ⟨2143808, by rfl⟩ : syracuseStep 2858411 = 4287617) B4287617
theorem B1905607 : Blo 1905435 1905607 := bstep (se 1 (by rfl) ⟨1429205, by rfl⟩ : syracuseStep 1905607 = 2858411) B2858411
theorem B2143813 : Blo 1905435 2143813 := bbase (se 4 (by rfl) ⟨200982, by rfl⟩ : syracuseStep 2143813 = 401965) (by norm_num)
theorem B2858417 : Blo 1905435 2858417 := bstep (se 2 (by rfl) ⟨1071906, by rfl⟩ : syracuseStep 2858417 = 2143813) B2143813
theorem B1905611 : Blo 1905435 1905611 := bstep (se 1 (by rfl) ⟨1429208, by rfl⟩ : syracuseStep 1905611 = 2858417) B2858417
theorem B3617693 : Blo 1905435 3617693 := bbase (se 3 (by rfl) ⟨678317, by rfl⟩ : syracuseStep 3617693 = 1356635) (by norm_num)
theorem B2411795 : Blo 1905435 2411795 := bstep (se 1 (by rfl) ⟨1808846, by rfl⟩ : syracuseStep 2411795 = 3617693) B3617693
theorem B6431453 : Blo 1905435 6431453 := bstep (se 3 (by rfl) ⟨1205897, by rfl⟩ : syracuseStep 6431453 = 2411795) B2411795
theorem B4287635 : Blo 1905435 4287635 := bstep (se 1 (by rfl) ⟨3215726, by rfl⟩ : syracuseStep 4287635 = 6431453) B6431453
theorem B2858423 : Blo 1905435 2858423 := bstep (se 1 (by rfl) ⟨2143817, by rfl⟩ : syracuseStep 2858423 = 4287635) B4287635
theorem B1905615 : Blo 1905435 1905615 := bstep (se 1 (by rfl) ⟨1429211, by rfl⟩ : syracuseStep 1905615 = 2858423) B2858423
theorem B2858429 : Blo 1905435 2858429 := bbase (se 3 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 2858429 = 1071911) (by norm_num)
theorem B1905619 : Blo 1905435 1905619 := bstep (se 1 (by rfl) ⟨1429214, by rfl⟩ : syracuseStep 1905619 = 2858429) B2858429
theorem B4287653 : Blo 1905435 4287653 := bbase (se 4 (by rfl) ⟨401967, by rfl⟩ : syracuseStep 4287653 = 803935) (by norm_num)
theorem B2858435 : Blo 1905435 2858435 := bstep (se 1 (by rfl) ⟨2143826, by rfl⟩ : syracuseStep 2858435 = 4287653) B4287653
theorem B1905623 : Blo 1905435 1905623 := bstep (se 1 (by rfl) ⟨1429217, by rfl⟩ : syracuseStep 1905623 = 2858435) B2858435
theorem B4823621 : Blo 1905435 4823621 := bbase (se 4 (by rfl) ⟨452214, by rfl⟩ : syracuseStep 4823621 = 904429) (by norm_num)
theorem B3215747 : Blo 1905435 3215747 := bstep (se 1 (by rfl) ⟨2411810, by rfl⟩ : syracuseStep 3215747 = 4823621) B4823621
theorem B2143831 : Blo 1905435 2143831 := bstep (se 1 (by rfl) ⟨1607873, by rfl⟩ : syracuseStep 2143831 = 3215747) B3215747
theorem B2858441 : Blo 1905435 2858441 := bstep (se 2 (by rfl) ⟨1071915, by rfl⟩ : syracuseStep 2858441 = 2143831) B2143831
theorem B1905627 : Blo 1905435 1905627 := bstep (se 1 (by rfl) ⟨1429220, by rfl⟩ : syracuseStep 1905627 = 2858441) B2858441
theorem B2289341 : Blo 1905435 2289341 := bbase (se 3 (by rfl) ⟨429251, by rfl⟩ : syracuseStep 2289341 = 858503) (by norm_num)
theorem B6104909 : Blo 1905435 6104909 := bstep (se 3 (by rfl) ⟨1144670, by rfl⟩ : syracuseStep 6104909 = 2289341) B2289341
theorem B4069939 : Blo 1905435 4069939 := bstep (se 1 (by rfl) ⟨3052454, by rfl⟩ : syracuseStep 4069939 = 6104909) B6104909
theorem B5426585 : Blo 1905435 5426585 := bstep (se 2 (by rfl) ⟨2034969, by rfl⟩ : syracuseStep 5426585 = 4069939) B4069939
theorem B3617723 : Blo 1905435 3617723 := bstep (se 1 (by rfl) ⟨2713292, by rfl⟩ : syracuseStep 3617723 = 5426585) B5426585
theorem B9647261 : Blo 1905435 9647261 := bstep (se 3 (by rfl) ⟨1808861, by rfl⟩ : syracuseStep 9647261 = 3617723) B3617723
theorem B6431507 : Blo 1905435 6431507 := bstep (se 1 (by rfl) ⟨4823630, by rfl⟩ : syracuseStep 6431507 = 9647261) B9647261
theorem B4287671 : Blo 1905435 4287671 := bstep (se 1 (by rfl) ⟨3215753, by rfl⟩ : syracuseStep 4287671 = 6431507) B6431507
theorem B2858447 : Blo 1905435 2858447 := bstep (se 1 (by rfl) ⟨2143835, by rfl⟩ : syracuseStep 2858447 = 4287671) B4287671
theorem B1905631 : Blo 1905435 1905631 := bstep (se 1 (by rfl) ⟨1429223, by rfl⟩ : syracuseStep 1905631 = 2858447) B2858447
theorem B2858453 : Blo 1905435 2858453 := bbase (se 7 (by rfl) ⟨33497, by rfl⟩ : syracuseStep 2858453 = 66995) (by norm_num)
theorem B1905635 : Blo 1905435 1905635 := bstep (se 1 (by rfl) ⟨1429226, by rfl⟩ : syracuseStep 1905635 = 2858453) B2858453
theorem B7235477 : Blo 1905435 7235477 := bbase (se 6 (by rfl) ⟨169581, by rfl⟩ : syracuseStep 7235477 = 339163) (by norm_num)
theorem B4823651 : Blo 1905435 4823651 := bstep (se 1 (by rfl) ⟨3617738, by rfl⟩ : syracuseStep 4823651 = 7235477) B7235477
theorem B3215767 : Blo 1905435 3215767 := bstep (se 1 (by rfl) ⟨2411825, by rfl⟩ : syracuseStep 3215767 = 4823651) B4823651
theorem B4287689 : Blo 1905435 4287689 := bstep (se 2 (by rfl) ⟨1607883, by rfl⟩ : syracuseStep 4287689 = 3215767) B3215767
theorem B2858459 : Blo 1905435 2858459 := bstep (se 1 (by rfl) ⟨2143844, by rfl⟩ : syracuseStep 2858459 = 4287689) B4287689
theorem B1905639 : Blo 1905435 1905639 := bstep (se 1 (by rfl) ⟨1429229, by rfl⟩ : syracuseStep 1905639 = 2858459) B2858459
theorem B2143849 : Blo 1905435 2143849 := bbase (se 2 (by rfl) ⟨803943, by rfl⟩ : syracuseStep 2143849 = 1607887) (by norm_num)
theorem B2858465 : Blo 1905435 2858465 := bstep (se 2 (by rfl) ⟨1071924, by rfl⟩ : syracuseStep 2858465 = 2143849) B2143849
theorem B1905643 : Blo 1905435 1905643 := bstep (se 1 (by rfl) ⟨1429232, by rfl⟩ : syracuseStep 1905643 = 2858465) B2858465
theorem B4069973 : Blo 1905435 4069973 := bbase (se 8 (by rfl) ⟨23847, by rfl⟩ : syracuseStep 4069973 = 47695) (by norm_num)
theorem B10853261 : Blo 1905435 10853261 := bstep (se 3 (by rfl) ⟨2034986, by rfl⟩ : syracuseStep 10853261 = 4069973) B4069973
theorem B7235507 : Blo 1905435 7235507 := bstep (se 1 (by rfl) ⟨5426630, by rfl⟩ : syracuseStep 7235507 = 10853261) B10853261
theorem B4823671 : Blo 1905435 4823671 := bstep (se 1 (by rfl) ⟨3617753, by rfl⟩ : syracuseStep 4823671 = 7235507) B7235507
theorem B6431561 : Blo 1905435 6431561 := bstep (se 2 (by rfl) ⟨2411835, by rfl⟩ : syracuseStep 6431561 = 4823671) B4823671
theorem B4287707 : Blo 1905435 4287707 := bstep (se 1 (by rfl) ⟨3215780, by rfl⟩ : syracuseStep 4287707 = 6431561) B6431561
theorem B2858471 : Blo 1905435 2858471 := bstep (se 1 (by rfl) ⟨2143853, by rfl⟩ : syracuseStep 2858471 = 4287707) B4287707
theorem B1905647 : Blo 1905435 1905647 := bstep (se 1 (by rfl) ⟨1429235, by rfl⟩ : syracuseStep 1905647 = 2858471) B2858471
theorem B2858477 : Blo 1905435 2858477 := bbase (se 3 (by rfl) ⟨535964, by rfl⟩ : syracuseStep 2858477 = 1071929) (by norm_num)
theorem B1905651 : Blo 1905435 1905651 := bstep (se 1 (by rfl) ⟨1429238, by rfl⟩ : syracuseStep 1905651 = 2858477) B2858477
theorem B4287725 : Blo 1905435 4287725 := bbase (se 3 (by rfl) ⟨803948, by rfl⟩ : syracuseStep 4287725 = 1607897) (by norm_num)
theorem B2858483 : Blo 1905435 2858483 := bstep (se 1 (by rfl) ⟨2143862, by rfl⟩ : syracuseStep 2858483 = 4287725) B4287725
theorem B1905655 : Blo 1905435 1905655 := bstep (se 1 (by rfl) ⟨1429241, by rfl⟩ : syracuseStep 1905655 = 2858483) B2858483
theorem B2713333 : Blo 1905435 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B3617777 : Blo 1905435 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B2411851 : Blo 1905435 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B3215801 : Blo 1905435 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B2143867 : Blo 1905435 2143867 := bstep (se 1 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 2143867 = 3215801) B3215801
theorem B2858489 : Blo 1905435 2858489 := bstep (se 2 (by rfl) ⟨1071933, by rfl⟩ : syracuseStep 2858489 = 2143867) B2143867
theorem B1905659 : Blo 1905435 1905659 := bstep (se 1 (by rfl) ⟨1429244, by rfl⟩ : syracuseStep 1905659 = 2858489) B2858489
theorem B4641229 : Blo 1905435 4641229 := bbase (se 3 (by rfl) ⟨870230, by rfl⟩ : syracuseStep 4641229 = 1740461) (by norm_num)
theorem B6188305 : Blo 1905435 6188305 := bstep (se 2 (by rfl) ⟨2320614, by rfl⟩ : syracuseStep 6188305 = 4641229) B4641229
theorem B8251073 : Blo 1905435 8251073 := bstep (se 2 (by rfl) ⟨3094152, by rfl⟩ : syracuseStep 8251073 = 6188305) B6188305
theorem B5500715 : Blo 1905435 5500715 := bstep (se 1 (by rfl) ⟨4125536, by rfl⟩ : syracuseStep 5500715 = 8251073) B8251073
theorem B14668573 : Blo 1905435 14668573 := bstep (se 3 (by rfl) ⟨2750357, by rfl⟩ : syracuseStep 14668573 = 5500715) B5500715
theorem B19558097 : Blo 1905435 19558097 := bstep (se 2 (by rfl) ⟨7334286, by rfl⟩ : syracuseStep 19558097 = 14668573) B14668573
theorem B13038731 : Blo 1905435 13038731 := bstep (se 1 (by rfl) ⟨9779048, by rfl⟩ : syracuseStep 13038731 = 19558097) B19558097
theorem B8692487 : Blo 1905435 8692487 := bstep (se 1 (by rfl) ⟨6519365, by rfl⟩ : syracuseStep 8692487 = 13038731) B13038731
theorem B5794991 : Blo 1905435 5794991 := bstep (se 1 (by rfl) ⟨4346243, by rfl⟩ : syracuseStep 5794991 = 8692487) B8692487
theorem B3863327 : Blo 1905435 3863327 := bstep (se 1 (by rfl) ⟨2897495, by rfl⟩ : syracuseStep 3863327 = 5794991) B5794991
theorem B41208821 : Blo 1905435 41208821 := bstep (se 5 (by rfl) ⟨1931663, by rfl⟩ : syracuseStep 41208821 = 3863327) B3863327
theorem B27472547 : Blo 1905435 27472547 := bstep (se 1 (by rfl) ⟨20604410, by rfl⟩ : syracuseStep 27472547 = 41208821) B41208821
theorem B73260125 : Blo 1905435 73260125 := bstep (se 3 (by rfl) ⟨13736273, by rfl⟩ : syracuseStep 73260125 = 27472547) B27472547
theorem B48840083 : Blo 1905435 48840083 := bstep (se 1 (by rfl) ⟨36630062, by rfl⟩ : syracuseStep 48840083 = 73260125) B73260125
theorem B32560055 : Blo 1905435 32560055 := bstep (se 1 (by rfl) ⟨24420041, by rfl⟩ : syracuseStep 32560055 = 48840083) B48840083
theorem B21706703 : Blo 1905435 21706703 := bstep (se 1 (by rfl) ⟨16280027, by rfl⟩ : syracuseStep 21706703 = 32560055) B32560055
theorem B14471135 : Blo 1905435 14471135 := bstep (se 1 (by rfl) ⟨10853351, by rfl⟩ : syracuseStep 14471135 = 21706703) B21706703
theorem B9647423 : Blo 1905435 9647423 := bstep (se 1 (by rfl) ⟨7235567, by rfl⟩ : syracuseStep 9647423 = 14471135) B14471135
theorem B6431615 : Blo 1905435 6431615 := bstep (se 1 (by rfl) ⟨4823711, by rfl⟩ : syracuseStep 6431615 = 9647423) B9647423
theorem B4287743 : Blo 1905435 4287743 := bstep (se 1 (by rfl) ⟨3215807, by rfl⟩ : syracuseStep 4287743 = 6431615) B6431615
theorem B2858495 : Blo 1905435 2858495 := bstep (se 1 (by rfl) ⟨2143871, by rfl⟩ : syracuseStep 2858495 = 4287743) B4287743
theorem B1905663 : Blo 1905435 1905663 := bstep (se 1 (by rfl) ⟨1429247, by rfl⟩ : syracuseStep 1905663 = 2858495) B2858495
theorem B2858501 : Blo 1905435 2858501 := bbase (se 4 (by rfl) ⟨267984, by rfl⟩ : syracuseStep 2858501 = 535969) (by norm_num)
theorem B1905667 : Blo 1905435 1905667 := bstep (se 1 (by rfl) ⟨1429250, by rfl⟩ : syracuseStep 1905667 = 2858501) B2858501
theorem B3215821 : Blo 1905435 3215821 := bbase (se 3 (by rfl) ⟨602966, by rfl⟩ : syracuseStep 3215821 = 1205933) (by norm_num)
theorem B4287761 : Blo 1905435 4287761 := bstep (se 2 (by rfl) ⟨1607910, by rfl⟩ : syracuseStep 4287761 = 3215821) B3215821
theorem B2858507 : Blo 1905435 2858507 := bstep (se 1 (by rfl) ⟨2143880, by rfl⟩ : syracuseStep 2858507 = 4287761) B4287761
theorem B1905671 : Blo 1905435 1905671 := bstep (se 1 (by rfl) ⟨1429253, by rfl⟩ : syracuseStep 1905671 = 2858507) B2858507
theorem B2143885 : Blo 1905435 2143885 := bbase (se 3 (by rfl) ⟨401978, by rfl⟩ : syracuseStep 2143885 = 803957) (by norm_num)
theorem B2858513 : Blo 1905435 2858513 := bstep (se 2 (by rfl) ⟨1071942, by rfl⟩ : syracuseStep 2858513 = 2143885) B2143885
theorem B1905675 : Blo 1905435 1905675 := bstep (se 1 (by rfl) ⟨1429256, by rfl⟩ : syracuseStep 1905675 = 2858513) B2858513
theorem B6431669 : Blo 1905435 6431669 := bbase (se 5 (by rfl) ⟨301484, by rfl⟩ : syracuseStep 6431669 = 602969) (by norm_num)
theorem B4287779 : Blo 1905435 4287779 := bstep (se 1 (by rfl) ⟨3215834, by rfl⟩ : syracuseStep 4287779 = 6431669) B6431669
theorem B2858519 : Blo 1905435 2858519 := bstep (se 1 (by rfl) ⟨2143889, by rfl⟩ : syracuseStep 2858519 = 4287779) B4287779
theorem B1905679 : Blo 1905435 1905679 := bstep (se 1 (by rfl) ⟨1429259, by rfl⟩ : syracuseStep 1905679 = 2858519) B2858519
theorem B2858525 : Blo 1905435 2858525 := bbase (se 3 (by rfl) ⟨535973, by rfl⟩ : syracuseStep 2858525 = 1071947) (by norm_num)
theorem B1905683 : Blo 1905435 1905683 := bstep (se 1 (by rfl) ⟨1429262, by rfl⟩ : syracuseStep 1905683 = 2858525) B2858525
theorem B4287797 : Blo 1905435 4287797 := bbase (se 5 (by rfl) ⟨200990, by rfl⟩ : syracuseStep 4287797 = 401981) (by norm_num)
theorem B2858531 : Blo 1905435 2858531 := bstep (se 1 (by rfl) ⟨2143898, by rfl⟩ : syracuseStep 2858531 = 4287797) B4287797
theorem B1905687 : Blo 1905435 1905687 := bstep (se 1 (by rfl) ⟨1429265, by rfl⟩ : syracuseStep 1905687 = 2858531) B2858531
theorem B13923893 : Blo 1905435 13923893 := bbase (se 5 (by rfl) ⟨652682, by rfl⟩ : syracuseStep 13923893 = 1305365) (by norm_num)
theorem B9282595 : Blo 1905435 9282595 := bstep (se 1 (by rfl) ⟨6961946, by rfl⟩ : syracuseStep 9282595 = 13923893) B13923893
theorem B12376793 : Blo 1905435 12376793 := bstep (se 2 (by rfl) ⟨4641297, by rfl⟩ : syracuseStep 12376793 = 9282595) B9282595
theorem B8251195 : Blo 1905435 8251195 := bstep (se 1 (by rfl) ⟨6188396, by rfl⟩ : syracuseStep 8251195 = 12376793) B12376793
theorem B11001593 : Blo 1905435 11001593 := bstep (se 2 (by rfl) ⟨4125597, by rfl⟩ : syracuseStep 11001593 = 8251195) B8251195
theorem B7334395 : Blo 1905435 7334395 := bstep (se 1 (by rfl) ⟨5500796, by rfl⟩ : syracuseStep 7334395 = 11001593) B11001593
theorem B39116773 : Blo 1905435 39116773 := bstep (se 4 (by rfl) ⟨3667197, by rfl⟩ : syracuseStep 39116773 = 7334395) B7334395
theorem B52155697 : Blo 1905435 52155697 := bstep (se 2 (by rfl) ⟨19558386, by rfl⟩ : syracuseStep 52155697 = 39116773) B39116773
theorem B69540929 : Blo 1905435 69540929 := bstep (se 2 (by rfl) ⟨26077848, by rfl⟩ : syracuseStep 69540929 = 52155697) B52155697
theorem B46360619 : Blo 1905435 46360619 := bstep (se 1 (by rfl) ⟨34770464, by rfl⟩ : syracuseStep 46360619 = 69540929) B69540929
theorem B30907079 : Blo 1905435 30907079 := bstep (se 1 (by rfl) ⟨23180309, by rfl⟩ : syracuseStep 30907079 = 46360619) B46360619
theorem B20604719 : Blo 1905435 20604719 := bstep (se 1 (by rfl) ⟨15453539, by rfl⟩ : syracuseStep 20604719 = 30907079) B30907079
theorem B13736479 : Blo 1905435 13736479 := bstep (se 1 (by rfl) ⟨10302359, by rfl⟩ : syracuseStep 13736479 = 20604719) B20604719
theorem B18315305 : Blo 1905435 18315305 := bstep (se 2 (by rfl) ⟨6868239, by rfl⟩ : syracuseStep 18315305 = 13736479) B13736479
theorem B12210203 : Blo 1905435 12210203 := bstep (se 1 (by rfl) ⟨9157652, by rfl⟩ : syracuseStep 12210203 = 18315305) B18315305
theorem B8140135 : Blo 1905435 8140135 := bstep (se 1 (by rfl) ⟨6105101, by rfl⟩ : syracuseStep 8140135 = 12210203) B12210203
theorem B10853513 : Blo 1905435 10853513 := bstep (se 2 (by rfl) ⟨4070067, by rfl⟩ : syracuseStep 10853513 = 8140135) B8140135
theorem B7235675 : Blo 1905435 7235675 := bstep (se 1 (by rfl) ⟨5426756, by rfl⟩ : syracuseStep 7235675 = 10853513) B10853513
theorem B4823783 : Blo 1905435 4823783 := bstep (se 1 (by rfl) ⟨3617837, by rfl⟩ : syracuseStep 4823783 = 7235675) B7235675
theorem B3215855 : Blo 1905435 3215855 := bstep (se 1 (by rfl) ⟨2411891, by rfl⟩ : syracuseStep 3215855 = 4823783) B4823783
theorem B2143903 : Blo 1905435 2143903 := bstep (se 1 (by rfl) ⟨1607927, by rfl⟩ : syracuseStep 2143903 = 3215855) B3215855
theorem B2858537 : Blo 1905435 2858537 := bstep (se 2 (by rfl) ⟨1071951, by rfl⟩ : syracuseStep 2858537 = 2143903) B2143903
theorem B1905691 : Blo 1905435 1905691 := bstep (se 1 (by rfl) ⟨1429268, by rfl⟩ : syracuseStep 1905691 = 2858537) B2858537
theorem B7832213 : Blo 1905435 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B5221475 : Blo 1905435 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B3480983 : Blo 1905435 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B2320655 : Blo 1905435 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B6188413 : Blo 1905435 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B8251217 : Blo 1905435 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B5500811 : Blo 1905435 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B3667207 : Blo 1905435 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B4889609 : Blo 1905435 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B3259739 : Blo 1905435 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B2173159 : Blo 1905435 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B2897545 : Blo 1905435 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B3863393 : Blo 1905435 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B2575595 : Blo 1905435 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B6868253 : Blo 1905435 6868253 := bstep (se 3 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 6868253 = 2575595) B2575595
theorem B18315341 : Blo 1905435 18315341 := bstep (se 3 (by rfl) ⟨3434126, by rfl⟩ : syracuseStep 18315341 = 6868253) B6868253
theorem B12210227 : Blo 1905435 12210227 := bstep (se 1 (by rfl) ⟨9157670, by rfl⟩ : syracuseStep 12210227 = 18315341) B18315341
theorem B8140151 : Blo 1905435 8140151 := bstep (se 1 (by rfl) ⟨6105113, by rfl⟩ : syracuseStep 8140151 = 12210227) B12210227
theorem B5426767 : Blo 1905435 5426767 := bstep (se 1 (by rfl) ⟨4070075, by rfl⟩ : syracuseStep 5426767 = 8140151) B8140151
theorem B7235689 : Blo 1905435 7235689 := bstep (se 2 (by rfl) ⟨2713383, by rfl⟩ : syracuseStep 7235689 = 5426767) B5426767
theorem B9647585 : Blo 1905435 9647585 := bstep (se 2 (by rfl) ⟨3617844, by rfl⟩ : syracuseStep 9647585 = 7235689) B7235689
theorem B6431723 : Blo 1905435 6431723 := bstep (se 1 (by rfl) ⟨4823792, by rfl⟩ : syracuseStep 6431723 = 9647585) B9647585
theorem B4287815 : Blo 1905435 4287815 := bstep (se 1 (by rfl) ⟨3215861, by rfl⟩ : syracuseStep 4287815 = 6431723) B6431723
theorem B2858543 : Blo 1905435 2858543 := bstep (se 1 (by rfl) ⟨2143907, by rfl⟩ : syracuseStep 2858543 = 4287815) B4287815
theorem B1905695 : Blo 1905435 1905695 := bstep (se 1 (by rfl) ⟨1429271, by rfl⟩ : syracuseStep 1905695 = 2858543) B2858543
theorem B2858549 : Blo 1905435 2858549 := bbase (se 5 (by rfl) ⟨133994, by rfl⟩ : syracuseStep 2858549 = 267989) (by norm_num)
theorem B1905699 : Blo 1905435 1905699 := bstep (se 1 (by rfl) ⟨1429274, by rfl⟩ : syracuseStep 1905699 = 2858549) B2858549
theorem B4823813 : Blo 1905435 4823813 := bbase (se 4 (by rfl) ⟨452232, by rfl⟩ : syracuseStep 4823813 = 904465) (by norm_num)
theorem B3215875 : Blo 1905435 3215875 := bstep (se 1 (by rfl) ⟨2411906, by rfl⟩ : syracuseStep 3215875 = 4823813) B4823813
theorem B4287833 : Blo 1905435 4287833 := bstep (se 2 (by rfl) ⟨1607937, by rfl⟩ : syracuseStep 4287833 = 3215875) B3215875
theorem B2858555 : Blo 1905435 2858555 := bstep (se 1 (by rfl) ⟨2143916, by rfl⟩ : syracuseStep 2858555 = 4287833) B4287833
theorem B1905703 : Blo 1905435 1905703 := bstep (se 1 (by rfl) ⟨1429277, by rfl⟩ : syracuseStep 1905703 = 2858555) B2858555
theorem B2143921 : Blo 1905435 2143921 := bbase (se 2 (by rfl) ⟨803970, by rfl⟩ : syracuseStep 2143921 = 1607941) (by norm_num)
theorem B2858561 : Blo 1905435 2858561 := bstep (se 2 (by rfl) ⟨1071960, by rfl⟩ : syracuseStep 2858561 = 2143921) B2143921
theorem B1905707 : Blo 1905435 1905707 := bstep (se 1 (by rfl) ⟨1429280, by rfl⟩ : syracuseStep 1905707 = 2858561) B2858561
theorem B7726853 : Blo 1905435 7726853 := bbase (se 4 (by rfl) ⟨724392, by rfl⟩ : syracuseStep 7726853 = 1448785) (by norm_num)
theorem B5151235 : Blo 1905435 5151235 := bstep (se 1 (by rfl) ⟨3863426, by rfl⟩ : syracuseStep 5151235 = 7726853) B7726853
theorem B6868313 : Blo 1905435 6868313 := bstep (se 2 (by rfl) ⟨2575617, by rfl⟩ : syracuseStep 6868313 = 5151235) B5151235
theorem B4578875 : Blo 1905435 4578875 := bstep (se 1 (by rfl) ⟨3434156, by rfl⟩ : syracuseStep 4578875 = 6868313) B6868313
theorem B3052583 : Blo 1905435 3052583 := bstep (se 1 (by rfl) ⟨2289437, by rfl⟩ : syracuseStep 3052583 = 4578875) B4578875
theorem B2035055 : Blo 1905435 2035055 := bstep (se 1 (by rfl) ⟨1526291, by rfl⟩ : syracuseStep 2035055 = 3052583) B3052583
theorem B5426813 : Blo 1905435 5426813 := bstep (se 3 (by rfl) ⟨1017527, by rfl⟩ : syracuseStep 5426813 = 2035055) B2035055
theorem B3617875 : Blo 1905435 3617875 := bstep (se 1 (by rfl) ⟨2713406, by rfl⟩ : syracuseStep 3617875 = 5426813) B5426813
theorem B4823833 : Blo 1905435 4823833 := bstep (se 2 (by rfl) ⟨1808937, by rfl⟩ : syracuseStep 4823833 = 3617875) B3617875
theorem B6431777 : Blo 1905435 6431777 := bstep (se 2 (by rfl) ⟨2411916, by rfl⟩ : syracuseStep 6431777 = 4823833) B4823833
theorem B4287851 : Blo 1905435 4287851 := bstep (se 1 (by rfl) ⟨3215888, by rfl⟩ : syracuseStep 4287851 = 6431777) B6431777
theorem B2858567 : Blo 1905435 2858567 := bstep (se 1 (by rfl) ⟨2143925, by rfl⟩ : syracuseStep 2858567 = 4287851) B4287851
theorem B1905711 : Blo 1905435 1905711 := bstep (se 1 (by rfl) ⟨1429283, by rfl⟩ : syracuseStep 1905711 = 2858567) B2858567
theorem B2858573 : Blo 1905435 2858573 := bbase (se 3 (by rfl) ⟨535982, by rfl⟩ : syracuseStep 2858573 = 1071965) (by norm_num)
theorem B1905715 : Blo 1905435 1905715 := bstep (se 1 (by rfl) ⟨1429286, by rfl⟩ : syracuseStep 1905715 = 2858573) B2858573
theorem B4287869 : Blo 1905435 4287869 := bbase (se 3 (by rfl) ⟨803975, by rfl⟩ : syracuseStep 4287869 = 1607951) (by norm_num)
theorem B2858579 : Blo 1905435 2858579 := bstep (se 1 (by rfl) ⟨2143934, by rfl⟩ : syracuseStep 2858579 = 4287869) B4287869
theorem B1905719 : Blo 1905435 1905719 := bstep (se 1 (by rfl) ⟨1429289, by rfl⟩ : syracuseStep 1905719 = 2858579) B2858579
theorem B3215909 : Blo 1905435 3215909 := bbase (se 4 (by rfl) ⟨301491, by rfl⟩ : syracuseStep 3215909 = 602983) (by norm_num)
theorem B2143939 : Blo 1905435 2143939 := bstep (se 1 (by rfl) ⟨1607954, by rfl⟩ : syracuseStep 2143939 = 3215909) B3215909
theorem B2858585 : Blo 1905435 2858585 := bstep (se 2 (by rfl) ⟨1071969, by rfl⟩ : syracuseStep 2858585 = 2143939) B2143939
theorem B1905723 : Blo 1905435 1905723 := bstep (se 1 (by rfl) ⟨1429292, by rfl⟩ : syracuseStep 1905723 = 2858585) B2858585
theorem B2713429 : Blo 1905435 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B14471621 : Blo 1905435 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B9647747 : Blo 1905435 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B6431831 : Blo 1905435 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B4287887 : Blo 1905435 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B2858591 : Blo 1905435 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B1905727 : Blo 1905435 1905727 := bstep (se 1 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 1905727 = 2858591) B2858591
theorem B2858597 : Blo 1905435 2858597 := bbase (se 4 (by rfl) ⟨267993, by rfl⟩ : syracuseStep 2858597 = 535987) (by norm_num)
theorem B1905731 : Blo 1905435 1905731 := bstep (se 1 (by rfl) ⟨1429298, by rfl⟩ : syracuseStep 1905731 = 2858597) B2858597
theorem B2035081 : Blo 1905435 2035081 := bbase (se 2 (by rfl) ⟨763155, by rfl⟩ : syracuseStep 2035081 = 1526311) (by norm_num)
theorem B2713441 : Blo 1905435 2713441 := bstep (se 2 (by rfl) ⟨1017540, by rfl⟩ : syracuseStep 2713441 = 2035081) B2035081
theorem B3617921 : Blo 1905435 3617921 := bstep (se 2 (by rfl) ⟨1356720, by rfl⟩ : syracuseStep 3617921 = 2713441) B2713441
theorem B2411947 : Blo 1905435 2411947 := bstep (se 1 (by rfl) ⟨1808960, by rfl⟩ : syracuseStep 2411947 = 3617921) B3617921
theorem B3215929 : Blo 1905435 3215929 := bstep (se 2 (by rfl) ⟨1205973, by rfl⟩ : syracuseStep 3215929 = 2411947) B2411947
theorem B4287905 : Blo 1905435 4287905 := bstep (se 2 (by rfl) ⟨1607964, by rfl⟩ : syracuseStep 4287905 = 3215929) B3215929
theorem B2858603 : Blo 1905435 2858603 := bstep (se 1 (by rfl) ⟨2143952, by rfl⟩ : syracuseStep 2858603 = 4287905) B4287905
theorem B1905735 : Blo 1905435 1905735 := bstep (se 1 (by rfl) ⟨1429301, by rfl⟩ : syracuseStep 1905735 = 2858603) B2858603
theorem B2143957 : Blo 1905435 2143957 := bbase (se 7 (by rfl) ⟨25124, by rfl⟩ : syracuseStep 2143957 = 50249) (by norm_num)
theorem B2858609 : Blo 1905435 2858609 := bstep (se 2 (by rfl) ⟨1071978, by rfl⟩ : syracuseStep 2858609 = 2143957) B2143957
theorem B1905739 : Blo 1905435 1905739 := bstep (se 1 (by rfl) ⟨1429304, by rfl⟩ : syracuseStep 1905739 = 2858609) B2858609
theorem B2411957 : Blo 1905435 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B6431885 : Blo 1905435 6431885 := bstep (se 3 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 6431885 = 2411957) B2411957
theorem B4287923 : Blo 1905435 4287923 := bstep (se 1 (by rfl) ⟨3215942, by rfl⟩ : syracuseStep 4287923 = 6431885) B6431885
theorem B2858615 : Blo 1905435 2858615 := bstep (se 1 (by rfl) ⟨2143961, by rfl⟩ : syracuseStep 2858615 = 4287923) B4287923
theorem B1905743 : Blo 1905435 1905743 := bstep (se 1 (by rfl) ⟨1429307, by rfl⟩ : syracuseStep 1905743 = 2858615) B2858615
theorem B2858621 : Blo 1905435 2858621 := bbase (se 3 (by rfl) ⟨535991, by rfl⟩ : syracuseStep 2858621 = 1071983) (by norm_num)
theorem B1905747 : Blo 1905435 1905747 := bstep (se 1 (by rfl) ⟨1429310, by rfl⟩ : syracuseStep 1905747 = 2858621) B2858621
theorem B4287941 : Blo 1905435 4287941 := bbase (se 4 (by rfl) ⟨401994, by rfl⟩ : syracuseStep 4287941 = 803989) (by norm_num)
theorem B2858627 : Blo 1905435 2858627 := bstep (se 1 (by rfl) ⟨2143970, by rfl⟩ : syracuseStep 2858627 = 4287941) B4287941
theorem B1905751 : Blo 1905435 1905751 := bstep (se 1 (by rfl) ⟨1429313, by rfl⟩ : syracuseStep 1905751 = 2858627) B2858627
theorem B9779525 : Blo 1905435 9779525 := bbase (se 4 (by rfl) ⟨916830, by rfl⟩ : syracuseStep 9779525 = 1833661) (by norm_num)
theorem B6519683 : Blo 1905435 6519683 := bstep (se 1 (by rfl) ⟨4889762, by rfl⟩ : syracuseStep 6519683 = 9779525) B9779525
theorem B4346455 : Blo 1905435 4346455 := bstep (se 1 (by rfl) ⟨3259841, by rfl⟩ : syracuseStep 4346455 = 6519683) B6519683
theorem B5795273 : Blo 1905435 5795273 := bstep (se 2 (by rfl) ⟨2173227, by rfl⟩ : syracuseStep 5795273 = 4346455) B4346455
theorem B15454061 : Blo 1905435 15454061 := bstep (se 3 (by rfl) ⟨2897636, by rfl⟩ : syracuseStep 15454061 = 5795273) B5795273
theorem B10302707 : Blo 1905435 10302707 := bstep (se 1 (by rfl) ⟨7727030, by rfl⟩ : syracuseStep 10302707 = 15454061) B15454061
theorem B6868471 : Blo 1905435 6868471 := bstep (se 1 (by rfl) ⟨5151353, by rfl⟩ : syracuseStep 6868471 = 10302707) B10302707
theorem B9157961 : Blo 1905435 9157961 := bstep (se 2 (by rfl) ⟨3434235, by rfl⟩ : syracuseStep 9157961 = 6868471) B6868471
theorem B6105307 : Blo 1905435 6105307 := bstep (se 1 (by rfl) ⟨4578980, by rfl⟩ : syracuseStep 6105307 = 9157961) B9157961
theorem B8140409 : Blo 1905435 8140409 := bstep (se 2 (by rfl) ⟨3052653, by rfl⟩ : syracuseStep 8140409 = 6105307) B6105307
theorem B5426939 : Blo 1905435 5426939 := bstep (se 1 (by rfl) ⟨4070204, by rfl⟩ : syracuseStep 5426939 = 8140409) B8140409
theorem B3617959 : Blo 1905435 3617959 := bstep (se 1 (by rfl) ⟨2713469, by rfl⟩ : syracuseStep 3617959 = 5426939) B5426939
theorem B4823945 : Blo 1905435 4823945 := bstep (se 2 (by rfl) ⟨1808979, by rfl⟩ : syracuseStep 4823945 = 3617959) B3617959
theorem B3215963 : Blo 1905435 3215963 := bstep (se 1 (by rfl) ⟨2411972, by rfl⟩ : syracuseStep 3215963 = 4823945) B4823945
theorem B2143975 : Blo 1905435 2143975 := bstep (se 1 (by rfl) ⟨1607981, by rfl⟩ : syracuseStep 2143975 = 3215963) B3215963
theorem B2858633 : Blo 1905435 2858633 := bstep (se 2 (by rfl) ⟨1071987, by rfl⟩ : syracuseStep 2858633 = 2143975) B2143975
theorem B1905755 : Blo 1905435 1905755 := bstep (se 1 (by rfl) ⟨1429316, by rfl⟩ : syracuseStep 1905755 = 2858633) B2858633
theorem B9647909 : Blo 1905435 9647909 := bbase (se 4 (by rfl) ⟨904491, by rfl⟩ : syracuseStep 9647909 = 1808983) (by norm_num)
theorem B6431939 : Blo 1905435 6431939 := bstep (se 1 (by rfl) ⟨4823954, by rfl⟩ : syracuseStep 6431939 = 9647909) B9647909
theorem B4287959 : Blo 1905435 4287959 := bstep (se 1 (by rfl) ⟨3215969, by rfl⟩ : syracuseStep 4287959 = 6431939) B6431939
theorem B2858639 : Blo 1905435 2858639 := bstep (se 1 (by rfl) ⟨2143979, by rfl⟩ : syracuseStep 2858639 = 4287959) B4287959
theorem B1905759 : Blo 1905435 1905759 := bstep (se 1 (by rfl) ⟨1429319, by rfl⟩ : syracuseStep 1905759 = 2858639) B2858639
theorem B2858645 : Blo 1905435 2858645 := bbase (se 6 (by rfl) ⟨66999, by rfl⟩ : syracuseStep 2858645 = 133999) (by norm_num)
theorem B1905763 : Blo 1905435 1905763 := bstep (se 1 (by rfl) ⟨1429322, by rfl⟩ : syracuseStep 1905763 = 2858645) B2858645
theorem B2173241 : Blo 1905435 2173241 := bbase (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) (by norm_num)
theorem B5795309 : Blo 1905435 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B3863539 : Blo 1905435 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B5151385 : Blo 1905435 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B6868513 : Blo 1905435 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B9158017 : Blo 1905435 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B12210689 : Blo 1905435 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B8140459 : Blo 1905435 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B10853945 : Blo 1905435 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B7235963 : Blo 1905435 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B4823975 : Blo 1905435 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B3215983 : Blo 1905435 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B4287977 : Blo 1905435 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B2858651 : Blo 1905435 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B1905767 : Blo 1905435 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B2143993 : Blo 1905435 2143993 := bbase (se 2 (by rfl) ⟨803997, by rfl⟩ : syracuseStep 2143993 = 1607995) (by norm_num)
theorem B2858657 : Blo 1905435 2858657 := bstep (se 2 (by rfl) ⟨1071996, by rfl⟩ : syracuseStep 2858657 = 2143993) B2143993
theorem B1905771 : Blo 1905435 1905771 := bstep (se 1 (by rfl) ⟨1429328, by rfl⟩ : syracuseStep 1905771 = 2858657) B2858657
theorem B3052685 : Blo 1905435 3052685 := bbase (se 3 (by rfl) ⟨572378, by rfl⟩ : syracuseStep 3052685 = 1144757) (by norm_num)
theorem B8140493 : Blo 1905435 8140493 := bstep (se 3 (by rfl) ⟨1526342, by rfl⟩ : syracuseStep 8140493 = 3052685) B3052685
theorem B5426995 : Blo 1905435 5426995 := bstep (se 1 (by rfl) ⟨4070246, by rfl⟩ : syracuseStep 5426995 = 8140493) B8140493
theorem B7235993 : Blo 1905435 7235993 := bstep (se 2 (by rfl) ⟨2713497, by rfl⟩ : syracuseStep 7235993 = 5426995) B5426995
theorem B4823995 : Blo 1905435 4823995 := bstep (se 1 (by rfl) ⟨3617996, by rfl⟩ : syracuseStep 4823995 = 7235993) B7235993
theorem B6431993 : Blo 1905435 6431993 := bstep (se 2 (by rfl) ⟨2411997, by rfl⟩ : syracuseStep 6431993 = 4823995) B4823995
theorem B4287995 : Blo 1905435 4287995 := bstep (se 1 (by rfl) ⟨3215996, by rfl⟩ : syracuseStep 4287995 = 6431993) B6431993
theorem B2858663 : Blo 1905435 2858663 := bstep (se 1 (by rfl) ⟨2143997, by rfl⟩ : syracuseStep 2858663 = 4287995) B4287995
theorem B1905775 : Blo 1905435 1905775 := bstep (se 1 (by rfl) ⟨1429331, by rfl⟩ : syracuseStep 1905775 = 2858663) B2858663
theorem B2858669 : Blo 1905435 2858669 := bbase (se 3 (by rfl) ⟨536000, by rfl⟩ : syracuseStep 2858669 = 1072001) (by norm_num)
theorem B1905779 : Blo 1905435 1905779 := bstep (se 1 (by rfl) ⟨1429334, by rfl⟩ : syracuseStep 1905779 = 2858669) B2858669
theorem B4288013 : Blo 1905435 4288013 := bbase (se 3 (by rfl) ⟨804002, by rfl⟩ : syracuseStep 4288013 = 1608005) (by norm_num)
theorem B2858675 : Blo 1905435 2858675 := bstep (se 1 (by rfl) ⟨2144006, by rfl⟩ : syracuseStep 2858675 = 4288013) B4288013
theorem B1905783 : Blo 1905435 1905783 := bstep (se 1 (by rfl) ⟨1429337, by rfl⟩ : syracuseStep 1905783 = 2858675) B2858675
theorem B2412013 : Blo 1905435 2412013 := bbase (se 3 (by rfl) ⟨452252, by rfl⟩ : syracuseStep 2412013 = 904505) (by norm_num)
theorem B3216017 : Blo 1905435 3216017 := bstep (se 2 (by rfl) ⟨1206006, by rfl⟩ : syracuseStep 3216017 = 2412013) B2412013
theorem B2144011 : Blo 1905435 2144011 := bstep (se 1 (by rfl) ⟨1608008, by rfl⟩ : syracuseStep 2144011 = 3216017) B3216017
theorem B2858681 : Blo 1905435 2858681 := bstep (se 2 (by rfl) ⟨1072005, by rfl⟩ : syracuseStep 2858681 = 2144011) B2144011
theorem B1905787 : Blo 1905435 1905787 := bstep (se 1 (by rfl) ⟨1429340, by rfl⟩ : syracuseStep 1905787 = 2858681) B2858681
theorem B5795381 : Blo 1905435 5795381 := bbase (se 5 (by rfl) ⟨271658, by rfl⟩ : syracuseStep 5795381 = 543317) (by norm_num)
theorem B3863587 : Blo 1905435 3863587 := bstep (se 1 (by rfl) ⟨2897690, by rfl⟩ : syracuseStep 3863587 = 5795381) B5795381
theorem B5151449 : Blo 1905435 5151449 := bstep (se 2 (by rfl) ⟨1931793, by rfl⟩ : syracuseStep 5151449 = 3863587) B3863587
theorem B13737197 : Blo 1905435 13737197 := bstep (se 3 (by rfl) ⟨2575724, by rfl⟩ : syracuseStep 13737197 = 5151449) B5151449
theorem B9158131 : Blo 1905435 9158131 := bstep (se 1 (by rfl) ⟨6868598, by rfl⟩ : syracuseStep 9158131 = 13737197) B13737197
theorem B12210841 : Blo 1905435 12210841 := bstep (se 2 (by rfl) ⟨4579065, by rfl⟩ : syracuseStep 12210841 = 9158131) B9158131
theorem B16281121 : Blo 1905435 16281121 := bstep (se 2 (by rfl) ⟨6105420, by rfl⟩ : syracuseStep 16281121 = 12210841) B12210841
theorem B21708161 : Blo 1905435 21708161 := bstep (se 2 (by rfl) ⟨8140560, by rfl⟩ : syracuseStep 21708161 = 16281121) B16281121
theorem B14472107 : Blo 1905435 14472107 := bstep (se 1 (by rfl) ⟨10854080, by rfl⟩ : syracuseStep 14472107 = 21708161) B21708161
theorem B9648071 : Blo 1905435 9648071 := bstep (se 1 (by rfl) ⟨7236053, by rfl⟩ : syracuseStep 9648071 = 14472107) B14472107
theorem B6432047 : Blo 1905435 6432047 := bstep (se 1 (by rfl) ⟨4824035, by rfl⟩ : syracuseStep 6432047 = 9648071) B9648071
theorem B4288031 : Blo 1905435 4288031 := bstep (se 1 (by rfl) ⟨3216023, by rfl⟩ : syracuseStep 4288031 = 6432047) B6432047
theorem B2858687 : Blo 1905435 2858687 := bstep (se 1 (by rfl) ⟨2144015, by rfl⟩ : syracuseStep 2858687 = 4288031) B4288031
theorem B1905791 : Blo 1905435 1905791 := bstep (se 1 (by rfl) ⟨1429343, by rfl⟩ : syracuseStep 1905791 = 2858687) B2858687
theorem B2858693 : Blo 1905435 2858693 := bbase (se 4 (by rfl) ⟨268002, by rfl⟩ : syracuseStep 2858693 = 536005) (by norm_num)
theorem B1905795 : Blo 1905435 1905795 := bstep (se 1 (by rfl) ⟨1429346, by rfl⟩ : syracuseStep 1905795 = 2858693) B2858693
theorem B3216037 : Blo 1905435 3216037 := bbase (se 4 (by rfl) ⟨301503, by rfl⟩ : syracuseStep 3216037 = 603007) (by norm_num)
theorem B4288049 : Blo 1905435 4288049 := bstep (se 2 (by rfl) ⟨1608018, by rfl⟩ : syracuseStep 4288049 = 3216037) B3216037
theorem B2858699 : Blo 1905435 2858699 := bstep (se 1 (by rfl) ⟨2144024, by rfl⟩ : syracuseStep 2858699 = 4288049) B4288049
theorem B1905799 : Blo 1905435 1905799 := bstep (se 1 (by rfl) ⟨1429349, by rfl⟩ : syracuseStep 1905799 = 2858699) B2858699
theorem B2144029 : Blo 1905435 2144029 := bbase (se 3 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 2144029 = 804011) (by norm_num)
theorem B2858705 : Blo 1905435 2858705 := bstep (se 2 (by rfl) ⟨1072014, by rfl⟩ : syracuseStep 2858705 = 2144029) B2144029
theorem B1905803 : Blo 1905435 1905803 := bstep (se 1 (by rfl) ⟨1429352, by rfl⟩ : syracuseStep 1905803 = 2858705) B2858705
theorem B6432101 : Blo 1905435 6432101 := bbase (se 4 (by rfl) ⟨603009, by rfl⟩ : syracuseStep 6432101 = 1206019) (by norm_num)
theorem B4288067 : Blo 1905435 4288067 := bstep (se 1 (by rfl) ⟨3216050, by rfl⟩ : syracuseStep 4288067 = 6432101) B6432101
theorem B2858711 : Blo 1905435 2858711 := bstep (se 1 (by rfl) ⟨2144033, by rfl⟩ : syracuseStep 2858711 = 4288067) B4288067
theorem B1905807 : Blo 1905435 1905807 := bstep (se 1 (by rfl) ⟨1429355, by rfl⟩ : syracuseStep 1905807 = 2858711) B2858711
theorem B2858717 : Blo 1905435 2858717 := bbase (se 3 (by rfl) ⟨536009, by rfl⟩ : syracuseStep 2858717 = 1072019) (by norm_num)
theorem B1905811 : Blo 1905435 1905811 := bstep (se 1 (by rfl) ⟨1429358, by rfl⟩ : syracuseStep 1905811 = 2858717) B2858717
theorem B4288085 : Blo 1905435 4288085 := bbase (se 8 (by rfl) ⟨25125, by rfl⟩ : syracuseStep 4288085 = 50251) (by norm_num)
theorem B2858723 : Blo 1905435 2858723 := bstep (se 1 (by rfl) ⟨2144042, by rfl⟩ : syracuseStep 2858723 = 4288085) B4288085
theorem B1905815 : Blo 1905435 1905815 := bstep (se 1 (by rfl) ⟨1429361, by rfl⟩ : syracuseStep 1905815 = 2858723) B2858723
theorem B4070341 : Blo 1905435 4070341 := bbase (se 4 (by rfl) ⟨381594, by rfl⟩ : syracuseStep 4070341 = 763189) (by norm_num)
theorem B5427121 : Blo 1905435 5427121 := bstep (se 2 (by rfl) ⟨2035170, by rfl⟩ : syracuseStep 5427121 = 4070341) B4070341
theorem B7236161 : Blo 1905435 7236161 := bstep (se 2 (by rfl) ⟨2713560, by rfl⟩ : syracuseStep 7236161 = 5427121) B5427121
theorem B4824107 : Blo 1905435 4824107 := bstep (se 1 (by rfl) ⟨3618080, by rfl⟩ : syracuseStep 4824107 = 7236161) B7236161
theorem B3216071 : Blo 1905435 3216071 := bstep (se 1 (by rfl) ⟨2412053, by rfl⟩ : syracuseStep 3216071 = 4824107) B4824107
theorem B2144047 : Blo 1905435 2144047 := bstep (se 1 (by rfl) ⟨1608035, by rfl⟩ : syracuseStep 2144047 = 3216071) B3216071
theorem B2858729 : Blo 1905435 2858729 := bstep (se 2 (by rfl) ⟨1072023, by rfl⟩ : syracuseStep 2858729 = 2144047) B2144047
theorem B1905819 : Blo 1905435 1905819 := bstep (se 1 (by rfl) ⟨1429364, by rfl⟩ : syracuseStep 1905819 = 2858729) B2858729
theorem B3434357 : Blo 1905435 3434357 := bbase (se 5 (by rfl) ⟨160985, by rfl⟩ : syracuseStep 3434357 = 321971) (by norm_num)
theorem B9158285 : Blo 1905435 9158285 := bstep (se 3 (by rfl) ⟨1717178, by rfl⟩ : syracuseStep 9158285 = 3434357) B3434357
theorem B24422093 : Blo 1905435 24422093 := bstep (se 3 (by rfl) ⟨4579142, by rfl⟩ : syracuseStep 24422093 = 9158285) B9158285
theorem B16281395 : Blo 1905435 16281395 := bstep (se 1 (by rfl) ⟨12211046, by rfl⟩ : syracuseStep 16281395 = 24422093) B24422093
theorem B10854263 : Blo 1905435 10854263 := bstep (se 1 (by rfl) ⟨8140697, by rfl⟩ : syracuseStep 10854263 = 16281395) B16281395
theorem B7236175 : Blo 1905435 7236175 := bstep (se 1 (by rfl) ⟨5427131, by rfl⟩ : syracuseStep 7236175 = 10854263) B10854263
theorem B9648233 : Blo 1905435 9648233 := bstep (se 2 (by rfl) ⟨3618087, by rfl⟩ : syracuseStep 9648233 = 7236175) B7236175
theorem B6432155 : Blo 1905435 6432155 := bstep (se 1 (by rfl) ⟨4824116, by rfl⟩ : syracuseStep 6432155 = 9648233) B9648233
theorem B4288103 : Blo 1905435 4288103 := bstep (se 1 (by rfl) ⟨3216077, by rfl⟩ : syracuseStep 4288103 = 6432155) B6432155
theorem B2858735 : Blo 1905435 2858735 := bstep (se 1 (by rfl) ⟨2144051, by rfl⟩ : syracuseStep 2858735 = 4288103) B4288103
theorem B1905823 : Blo 1905435 1905823 := bstep (se 1 (by rfl) ⟨1429367, by rfl⟩ : syracuseStep 1905823 = 2858735) B2858735
theorem B2858741 : Blo 1905435 2858741 := bbase (se 5 (by rfl) ⟨134003, by rfl⟩ : syracuseStep 2858741 = 268007) (by norm_num)
theorem B1905827 : Blo 1905435 1905827 := bstep (se 1 (by rfl) ⟨1429370, by rfl⟩ : syracuseStep 1905827 = 2858741) B2858741
theorem B4956677 : Blo 1905435 4956677 := bbase (se 4 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 4956677 = 929377) (by norm_num)
theorem B3304451 : Blo 1905435 3304451 := bstep (se 1 (by rfl) ⟨2478338, by rfl⟩ : syracuseStep 3304451 = 4956677) B4956677
theorem B2202967 : Blo 1905435 2202967 := bstep (se 1 (by rfl) ⟨1652225, by rfl⟩ : syracuseStep 2202967 = 3304451) B3304451
theorem B11749157 : Blo 1905435 11749157 := bstep (se 4 (by rfl) ⟨1101483, by rfl⟩ : syracuseStep 11749157 = 2202967) B2202967
theorem B7832771 : Blo 1905435 7832771 := bstep (se 1 (by rfl) ⟨5874578, by rfl⟩ : syracuseStep 7832771 = 11749157) B11749157
theorem B5221847 : Blo 1905435 5221847 := bstep (se 1 (by rfl) ⟨3916385, by rfl⟩ : syracuseStep 5221847 = 7832771) B7832771
theorem B3481231 : Blo 1905435 3481231 := bstep (se 1 (by rfl) ⟨2610923, by rfl⟩ : syracuseStep 3481231 = 5221847) B5221847
theorem B4641641 : Blo 1905435 4641641 := bstep (se 2 (by rfl) ⟨1740615, by rfl⟩ : syracuseStep 4641641 = 3481231) B3481231
theorem B3094427 : Blo 1905435 3094427 := bstep (se 1 (by rfl) ⟨2320820, by rfl⟩ : syracuseStep 3094427 = 4641641) B4641641
theorem B2062951 : Blo 1905435 2062951 := bstep (se 1 (by rfl) ⟨1547213, by rfl⟩ : syracuseStep 2062951 = 3094427) B3094427
theorem B11002405 : Blo 1905435 11002405 := bstep (se 4 (by rfl) ⟨1031475, by rfl⟩ : syracuseStep 11002405 = 2062951) B2062951
theorem B14669873 : Blo 1905435 14669873 := bstep (se 2 (by rfl) ⟨5501202, by rfl⟩ : syracuseStep 14669873 = 11002405) B11002405
theorem B9779915 : Blo 1905435 9779915 := bstep (se 1 (by rfl) ⟨7334936, by rfl⟩ : syracuseStep 9779915 = 14669873) B14669873
theorem B6519943 : Blo 1905435 6519943 := bstep (se 1 (by rfl) ⟨4889957, by rfl⟩ : syracuseStep 6519943 = 9779915) B9779915
theorem B8693257 : Blo 1905435 8693257 := bstep (se 2 (by rfl) ⟨3259971, by rfl⟩ : syracuseStep 8693257 = 6519943) B6519943
theorem B11591009 : Blo 1905435 11591009 := bstep (se 2 (by rfl) ⟨4346628, by rfl⟩ : syracuseStep 11591009 = 8693257) B8693257
theorem B7727339 : Blo 1905435 7727339 := bstep (se 1 (by rfl) ⟨5795504, by rfl⟩ : syracuseStep 7727339 = 11591009) B11591009
theorem B5151559 : Blo 1905435 5151559 := bstep (se 1 (by rfl) ⟨3863669, by rfl⟩ : syracuseStep 5151559 = 7727339) B7727339
theorem B6868745 : Blo 1905435 6868745 := bstep (se 2 (by rfl) ⟨2575779, by rfl⟩ : syracuseStep 6868745 = 5151559) B5151559
theorem B4579163 : Blo 1905435 4579163 := bstep (se 1 (by rfl) ⟨3434372, by rfl⟩ : syracuseStep 4579163 = 6868745) B6868745
theorem B3052775 : Blo 1905435 3052775 := bstep (se 1 (by rfl) ⟨2289581, by rfl⟩ : syracuseStep 3052775 = 4579163) B4579163
theorem B8140733 : Blo 1905435 8140733 := bstep (se 3 (by rfl) ⟨1526387, by rfl⟩ : syracuseStep 8140733 = 3052775) B3052775
theorem B5427155 : Blo 1905435 5427155 := bstep (se 1 (by rfl) ⟨4070366, by rfl⟩ : syracuseStep 5427155 = 8140733) B8140733
theorem B3618103 : Blo 1905435 3618103 := bstep (se 1 (by rfl) ⟨2713577, by rfl⟩ : syracuseStep 3618103 = 5427155) B5427155
theorem B4824137 : Blo 1905435 4824137 := bstep (se 2 (by rfl) ⟨1809051, by rfl⟩ : syracuseStep 4824137 = 3618103) B3618103
theorem B3216091 : Blo 1905435 3216091 := bstep (se 1 (by rfl) ⟨2412068, by rfl⟩ : syracuseStep 3216091 = 4824137) B4824137
theorem B4288121 : Blo 1905435 4288121 := bstep (se 2 (by rfl) ⟨1608045, by rfl⟩ : syracuseStep 4288121 = 3216091) B3216091
theorem B2858747 : Blo 1905435 2858747 := bstep (se 1 (by rfl) ⟨2144060, by rfl⟩ : syracuseStep 2858747 = 4288121) B4288121
theorem B1905831 : Blo 1905435 1905831 := bstep (se 1 (by rfl) ⟨1429373, by rfl⟩ : syracuseStep 1905831 = 2858747) B2858747
theorem B2144065 : Blo 1905435 2144065 := bbase (se 2 (by rfl) ⟨804024, by rfl⟩ : syracuseStep 2144065 = 1608049) (by norm_num)
theorem B2858753 : Blo 1905435 2858753 := bstep (se 2 (by rfl) ⟨1072032, by rfl⟩ : syracuseStep 2858753 = 2144065) B2144065
theorem B1905835 : Blo 1905435 1905835 := bstep (se 1 (by rfl) ⟨1429376, by rfl⟩ : syracuseStep 1905835 = 2858753) B2858753
theorem B4824157 : Blo 1905435 4824157 := bbase (se 3 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 4824157 = 1809059) (by norm_num)
theorem B6432209 : Blo 1905435 6432209 := bstep (se 2 (by rfl) ⟨2412078, by rfl⟩ : syracuseStep 6432209 = 4824157) B4824157
theorem B4288139 : Blo 1905435 4288139 := bstep (se 1 (by rfl) ⟨3216104, by rfl⟩ : syracuseStep 4288139 = 6432209) B6432209
theorem B2858759 : Blo 1905435 2858759 := bstep (se 1 (by rfl) ⟨2144069, by rfl⟩ : syracuseStep 2858759 = 4288139) B4288139
theorem B1905839 : Blo 1905435 1905839 := bstep (se 1 (by rfl) ⟨1429379, by rfl⟩ : syracuseStep 1905839 = 2858759) B2858759
theorem B2858765 : Blo 1905435 2858765 := bbase (se 3 (by rfl) ⟨536018, by rfl⟩ : syracuseStep 2858765 = 1072037) (by norm_num)
theorem B1905843 : Blo 1905435 1905843 := bstep (se 1 (by rfl) ⟨1429382, by rfl⟩ : syracuseStep 1905843 = 2858765) B2858765
theorem B4288157 : Blo 1905435 4288157 := bbase (se 3 (by rfl) ⟨804029, by rfl⟩ : syracuseStep 4288157 = 1608059) (by norm_num)
theorem B2858771 : Blo 1905435 2858771 := bstep (se 1 (by rfl) ⟨2144078, by rfl⟩ : syracuseStep 2858771 = 4288157) B4288157
theorem B1905847 : Blo 1905435 1905847 := bstep (se 1 (by rfl) ⟨1429385, by rfl⟩ : syracuseStep 1905847 = 2858771) B2858771
theorem B3216125 : Blo 1905435 3216125 := bbase (se 3 (by rfl) ⟨603023, by rfl⟩ : syracuseStep 3216125 = 1206047) (by norm_num)
theorem B2144083 : Blo 1905435 2144083 := bstep (se 1 (by rfl) ⟨1608062, by rfl⟩ : syracuseStep 2144083 = 3216125) B3216125
theorem B2858777 : Blo 1905435 2858777 := bstep (se 2 (by rfl) ⟨1072041, by rfl⟩ : syracuseStep 2858777 = 2144083) B2144083
theorem B1905851 : Blo 1905435 1905851 := bstep (se 1 (by rfl) ⟨1429388, by rfl⟩ : syracuseStep 1905851 = 2858777) B2858777
theorem B3052813 : Blo 1905435 3052813 := bbase (se 3 (by rfl) ⟨572402, by rfl⟩ : syracuseStep 3052813 = 1144805) (by norm_num)
theorem B4070417 : Blo 1905435 4070417 := bstep (se 2 (by rfl) ⟨1526406, by rfl⟩ : syracuseStep 4070417 = 3052813) B3052813
theorem B10854445 : Blo 1905435 10854445 := bstep (se 3 (by rfl) ⟨2035208, by rfl⟩ : syracuseStep 10854445 = 4070417) B4070417
theorem B14472593 : Blo 1905435 14472593 := bstep (se 2 (by rfl) ⟨5427222, by rfl⟩ : syracuseStep 14472593 = 10854445) B10854445
theorem B9648395 : Blo 1905435 9648395 := bstep (se 1 (by rfl) ⟨7236296, by rfl⟩ : syracuseStep 9648395 = 14472593) B14472593
theorem B6432263 : Blo 1905435 6432263 := bstep (se 1 (by rfl) ⟨4824197, by rfl⟩ : syracuseStep 6432263 = 9648395) B9648395
theorem B4288175 : Blo 1905435 4288175 := bstep (se 1 (by rfl) ⟨3216131, by rfl⟩ : syracuseStep 4288175 = 6432263) B6432263
theorem B2858783 : Blo 1905435 2858783 := bstep (se 1 (by rfl) ⟨2144087, by rfl⟩ : syracuseStep 2858783 = 4288175) B4288175
theorem B1905855 : Blo 1905435 1905855 := bstep (se 1 (by rfl) ⟨1429391, by rfl⟩ : syracuseStep 1905855 = 2858783) B2858783
theorem B2858789 : Blo 1905435 2858789 := bbase (se 4 (by rfl) ⟨268011, by rfl⟩ : syracuseStep 2858789 = 536023) (by norm_num)
theorem B1905859 : Blo 1905435 1905859 := bstep (se 1 (by rfl) ⟨1429394, by rfl⟩ : syracuseStep 1905859 = 2858789) B2858789
theorem B2412109 : Blo 1905435 2412109 := bbase (se 3 (by rfl) ⟨452270, by rfl⟩ : syracuseStep 2412109 = 904541) (by norm_num)
theorem B3216145 : Blo 1905435 3216145 := bstep (se 2 (by rfl) ⟨1206054, by rfl⟩ : syracuseStep 3216145 = 2412109) B2412109
theorem B4288193 : Blo 1905435 4288193 := bstep (se 2 (by rfl) ⟨1608072, by rfl⟩ : syracuseStep 4288193 = 3216145) B3216145
theorem B2858795 : Blo 1905435 2858795 := bstep (se 1 (by rfl) ⟨2144096, by rfl⟩ : syracuseStep 2858795 = 4288193) B4288193
theorem B1905863 : Blo 1905435 1905863 := bstep (se 1 (by rfl) ⟨1429397, by rfl⟩ : syracuseStep 1905863 = 2858795) B2858795
theorem B2144101 : Blo 1905435 2144101 := bbase (se 4 (by rfl) ⟨201009, by rfl⟩ : syracuseStep 2144101 = 402019) (by norm_num)
theorem B2858801 : Blo 1905435 2858801 := bstep (se 2 (by rfl) ⟨1072050, by rfl⟩ : syracuseStep 2858801 = 2144101) B2144101
theorem B1905867 : Blo 1905435 1905867 := bstep (se 1 (by rfl) ⟨1429400, by rfl⟩ : syracuseStep 1905867 = 2858801) B2858801
theorem B5427269 : Blo 1905435 5427269 := bbase (se 4 (by rfl) ⟨508806, by rfl⟩ : syracuseStep 5427269 = 1017613) (by norm_num)
theorem B3618179 : Blo 1905435 3618179 := bstep (se 1 (by rfl) ⟨2713634, by rfl⟩ : syracuseStep 3618179 = 5427269) B5427269
theorem B2412119 : Blo 1905435 2412119 := bstep (se 1 (by rfl) ⟨1809089, by rfl⟩ : syracuseStep 2412119 = 3618179) B3618179
theorem B6432317 : Blo 1905435 6432317 := bstep (se 3 (by rfl) ⟨1206059, by rfl⟩ : syracuseStep 6432317 = 2412119) B2412119
theorem B4288211 : Blo 1905435 4288211 := bstep (se 1 (by rfl) ⟨3216158, by rfl⟩ : syracuseStep 4288211 = 6432317) B6432317
theorem B2858807 : Blo 1905435 2858807 := bstep (se 1 (by rfl) ⟨2144105, by rfl⟩ : syracuseStep 2858807 = 4288211) B4288211
theorem B1905871 : Blo 1905435 1905871 := bstep (se 1 (by rfl) ⟨1429403, by rfl⟩ : syracuseStep 1905871 = 2858807) B2858807
theorem B2858813 : Blo 1905435 2858813 := bbase (se 3 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 2858813 = 1072055) (by norm_num)
theorem B1905875 : Blo 1905435 1905875 := bstep (se 1 (by rfl) ⟨1429406, by rfl⟩ : syracuseStep 1905875 = 2858813) B2858813
theorem B4288229 : Blo 1905435 4288229 := bbase (se 4 (by rfl) ⟨402021, by rfl⟩ : syracuseStep 4288229 = 804043) (by norm_num)
theorem B2858819 : Blo 1905435 2858819 := bstep (se 1 (by rfl) ⟨2144114, by rfl⟩ : syracuseStep 2858819 = 4288229) B4288229
theorem B1905879 : Blo 1905435 1905879 := bstep (se 1 (by rfl) ⟨1429409, by rfl⟩ : syracuseStep 1905879 = 2858819) B2858819
theorem B4824269 : Blo 1905435 4824269 := bbase (se 3 (by rfl) ⟨904550, by rfl⟩ : syracuseStep 4824269 = 1809101) (by norm_num)
theorem B3216179 : Blo 1905435 3216179 := bstep (se 1 (by rfl) ⟨2412134, by rfl⟩ : syracuseStep 3216179 = 4824269) B4824269
theorem B2144119 : Blo 1905435 2144119 := bstep (se 1 (by rfl) ⟨1608089, by rfl⟩ : syracuseStep 2144119 = 3216179) B3216179
theorem B2858825 : Blo 1905435 2858825 := bstep (se 2 (by rfl) ⟨1072059, by rfl⟩ : syracuseStep 2858825 = 2144119) B2144119
theorem B1905883 : Blo 1905435 1905883 := bstep (se 1 (by rfl) ⟨1429412, by rfl⟩ : syracuseStep 1905883 = 2858825) B2858825
theorem B2289649 : Blo 1905435 2289649 := bbase (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) (by norm_num)
theorem B3052865 : Blo 1905435 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B2035243 : Blo 1905435 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B2713657 : Blo 1905435 2713657 := bstep (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) B2035243
theorem B3618209 : Blo 1905435 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B9648557 : Blo 1905435 9648557 := bstep (se 3 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 9648557 = 3618209) B3618209
theorem B6432371 : Blo 1905435 6432371 := bstep (se 1 (by rfl) ⟨4824278, by rfl⟩ : syracuseStep 6432371 = 9648557) B9648557
theorem B4288247 : Blo 1905435 4288247 := bstep (se 1 (by rfl) ⟨3216185, by rfl⟩ : syracuseStep 4288247 = 6432371) B6432371
theorem B2858831 : Blo 1905435 2858831 := bstep (se 1 (by rfl) ⟨2144123, by rfl⟩ : syracuseStep 2858831 = 4288247) B4288247
theorem B1905887 : Blo 1905435 1905887 := bstep (se 1 (by rfl) ⟨1429415, by rfl⟩ : syracuseStep 1905887 = 2858831) B2858831
theorem B2858837 : Blo 1905435 2858837 := bbase (se 9 (by rfl) ⟨8375, by rfl⟩ : syracuseStep 2858837 = 16751) (by norm_num)
theorem B1905891 : Blo 1905435 1905891 := bstep (se 1 (by rfl) ⟨1429418, by rfl⟩ : syracuseStep 1905891 = 2858837) B2858837
theorem B2750693 : Blo 1905435 2750693 := bbase (se 4 (by rfl) ⟨257877, by rfl⟩ : syracuseStep 2750693 = 515755) (by norm_num)
theorem B7335181 : Blo 1905435 7335181 := bstep (se 3 (by rfl) ⟨1375346, by rfl⟩ : syracuseStep 7335181 = 2750693) B2750693
theorem B39120965 : Blo 1905435 39120965 := bstep (se 4 (by rfl) ⟨3667590, by rfl⟩ : syracuseStep 39120965 = 7335181) B7335181
theorem B26080643 : Blo 1905435 26080643 := bstep (se 1 (by rfl) ⟨19560482, by rfl⟩ : syracuseStep 26080643 = 39120965) B39120965
theorem B17387095 : Blo 1905435 17387095 := bstep (se 1 (by rfl) ⟨13040321, by rfl⟩ : syracuseStep 17387095 = 26080643) B26080643
theorem B23182793 : Blo 1905435 23182793 := bstep (se 2 (by rfl) ⟨8693547, by rfl⟩ : syracuseStep 23182793 = 17387095) B17387095
theorem B15455195 : Blo 1905435 15455195 := bstep (se 1 (by rfl) ⟨11591396, by rfl⟩ : syracuseStep 15455195 = 23182793) B23182793
theorem B10303463 : Blo 1905435 10303463 := bstep (se 1 (by rfl) ⟨7727597, by rfl⟩ : syracuseStep 10303463 = 15455195) B15455195
theorem B6868975 : Blo 1905435 6868975 := bstep (se 1 (by rfl) ⟨5151731, by rfl⟩ : syracuseStep 6868975 = 10303463) B10303463
theorem B9158633 : Blo 1905435 9158633 := bstep (se 2 (by rfl) ⟨3434487, by rfl⟩ : syracuseStep 9158633 = 6868975) B6868975
theorem B6105755 : Blo 1905435 6105755 := bstep (se 1 (by rfl) ⟨4579316, by rfl⟩ : syracuseStep 6105755 = 9158633) B9158633
theorem B4070503 : Blo 1905435 4070503 := bstep (se 1 (by rfl) ⟨3052877, by rfl⟩ : syracuseStep 4070503 = 6105755) B6105755
theorem B5427337 : Blo 1905435 5427337 := bstep (se 2 (by rfl) ⟨2035251, by rfl⟩ : syracuseStep 5427337 = 4070503) B4070503
theorem B7236449 : Blo 1905435 7236449 := bstep (se 2 (by rfl) ⟨2713668, by rfl⟩ : syracuseStep 7236449 = 5427337) B5427337
theorem B4824299 : Blo 1905435 4824299 := bstep (se 1 (by rfl) ⟨3618224, by rfl⟩ : syracuseStep 4824299 = 7236449) B7236449
theorem B3216199 : Blo 1905435 3216199 := bstep (se 1 (by rfl) ⟨2412149, by rfl⟩ : syracuseStep 3216199 = 4824299) B4824299
theorem B4288265 : Blo 1905435 4288265 := bstep (se 2 (by rfl) ⟨1608099, by rfl⟩ : syracuseStep 4288265 = 3216199) B3216199
theorem B2858843 : Blo 1905435 2858843 := bstep (se 1 (by rfl) ⟨2144132, by rfl⟩ : syracuseStep 2858843 = 4288265) B4288265
theorem B1905895 : Blo 1905435 1905895 := bstep (se 1 (by rfl) ⟨1429421, by rfl⟩ : syracuseStep 1905895 = 2858843) B2858843
theorem B2144137 : Blo 1905435 2144137 := bbase (se 2 (by rfl) ⟨804051, by rfl⟩ : syracuseStep 2144137 = 1608103) (by norm_num)
theorem B2858849 : Blo 1905435 2858849 := bstep (se 2 (by rfl) ⟨1072068, by rfl⟩ : syracuseStep 2858849 = 2144137) B2144137
theorem B1905899 : Blo 1905435 1905899 := bstep (se 1 (by rfl) ⟨1429424, by rfl⟩ : syracuseStep 1905899 = 2858849) B2858849
theorem B8932421 : Blo 1905435 8932421 := bbase (se 4 (by rfl) ⟨837414, by rfl⟩ : syracuseStep 8932421 = 1674829) (by norm_num)
theorem B5954947 : Blo 1905435 5954947 := bstep (se 1 (by rfl) ⟨4466210, by rfl⟩ : syracuseStep 5954947 = 8932421) B8932421
theorem B31759717 : Blo 1905435 31759717 := bstep (se 4 (by rfl) ⟨2977473, by rfl⟩ : syracuseStep 31759717 = 5954947) B5954947
theorem B42346289 : Blo 1905435 42346289 := bstep (se 2 (by rfl) ⟨15879858, by rfl⟩ : syracuseStep 42346289 = 31759717) B31759717
theorem B28230859 : Blo 1905435 28230859 := bstep (se 1 (by rfl) ⟨21173144, by rfl⟩ : syracuseStep 28230859 = 42346289) B42346289
theorem B37641145 : Blo 1905435 37641145 := bstep (se 2 (by rfl) ⟨14115429, by rfl⟩ : syracuseStep 37641145 = 28230859) B28230859
theorem B50188193 : Blo 1905435 50188193 := bstep (se 2 (by rfl) ⟨18820572, by rfl⟩ : syracuseStep 50188193 = 37641145) B37641145
theorem B33458795 : Blo 1905435 33458795 := bstep (se 1 (by rfl) ⟨25094096, by rfl⟩ : syracuseStep 33458795 = 50188193) B50188193
theorem B22305863 : Blo 1905435 22305863 := bstep (se 1 (by rfl) ⟨16729397, by rfl⟩ : syracuseStep 22305863 = 33458795) B33458795
theorem B14870575 : Blo 1905435 14870575 := bstep (se 1 (by rfl) ⟨11152931, by rfl⟩ : syracuseStep 14870575 = 22305863) B22305863
theorem B19827433 : Blo 1905435 19827433 := bstep (se 2 (by rfl) ⟨7435287, by rfl⟩ : syracuseStep 19827433 = 14870575) B14870575
theorem B26436577 : Blo 1905435 26436577 := bstep (se 2 (by rfl) ⟨9913716, by rfl⟩ : syracuseStep 26436577 = 19827433) B19827433
theorem B35248769 : Blo 1905435 35248769 := bstep (se 2 (by rfl) ⟨13218288, by rfl⟩ : syracuseStep 35248769 = 26436577) B26436577
theorem B23499179 : Blo 1905435 23499179 := bstep (se 1 (by rfl) ⟨17624384, by rfl⟩ : syracuseStep 23499179 = 35248769) B35248769
theorem B15666119 : Blo 1905435 15666119 := bstep (se 1 (by rfl) ⟨11749589, by rfl⟩ : syracuseStep 15666119 = 23499179) B23499179
theorem B10444079 : Blo 1905435 10444079 := bstep (se 1 (by rfl) ⟨7833059, by rfl⟩ : syracuseStep 10444079 = 15666119) B15666119
theorem B6962719 : Blo 1905435 6962719 := bstep (se 1 (by rfl) ⟨5222039, by rfl⟩ : syracuseStep 6962719 = 10444079) B10444079
theorem B9283625 : Blo 1905435 9283625 := bstep (se 2 (by rfl) ⟨3481359, by rfl⟩ : syracuseStep 9283625 = 6962719) B6962719
theorem B6189083 : Blo 1905435 6189083 := bstep (se 1 (by rfl) ⟨4641812, by rfl⟩ : syracuseStep 6189083 = 9283625) B9283625
theorem B66016885 : Blo 1905435 66016885 := bstep (se 5 (by rfl) ⟨3094541, by rfl⟩ : syracuseStep 66016885 = 6189083) B6189083
theorem B88022513 : Blo 1905435 88022513 := bstep (se 2 (by rfl) ⟨33008442, by rfl⟩ : syracuseStep 88022513 = 66016885) B66016885
theorem B58681675 : Blo 1905435 58681675 := bstep (se 1 (by rfl) ⟨44011256, by rfl⟩ : syracuseStep 58681675 = 88022513) B88022513
theorem B78242233 : Blo 1905435 78242233 := bstep (se 2 (by rfl) ⟨29340837, by rfl⟩ : syracuseStep 78242233 = 58681675) B58681675
theorem B104322977 : Blo 1905435 104322977 := bstep (se 2 (by rfl) ⟨39121116, by rfl⟩ : syracuseStep 104322977 = 78242233) B78242233
theorem B69548651 : Blo 1905435 69548651 := bstep (se 1 (by rfl) ⟨52161488, by rfl⟩ : syracuseStep 69548651 = 104322977) B104322977
theorem B46365767 : Blo 1905435 46365767 := bstep (se 1 (by rfl) ⟨34774325, by rfl⟩ : syracuseStep 46365767 = 69548651) B69548651
theorem B30910511 : Blo 1905435 30910511 := bstep (se 1 (by rfl) ⟨23182883, by rfl⟩ : syracuseStep 30910511 = 46365767) B46365767
theorem B82428029 : Blo 1905435 82428029 := bstep (se 3 (by rfl) ⟨15455255, by rfl⟩ : syracuseStep 82428029 = 30910511) B30910511
theorem B54952019 : Blo 1905435 54952019 := bstep (se 1 (by rfl) ⟨41214014, by rfl⟩ : syracuseStep 54952019 = 82428029) B82428029
theorem B36634679 : Blo 1905435 36634679 := bstep (se 1 (by rfl) ⟨27476009, by rfl⟩ : syracuseStep 36634679 = 54952019) B54952019
theorem B24423119 : Blo 1905435 24423119 := bstep (se 1 (by rfl) ⟨18317339, by rfl⟩ : syracuseStep 24423119 = 36634679) B36634679
theorem B16282079 : Blo 1905435 16282079 := bstep (se 1 (by rfl) ⟨12211559, by rfl⟩ : syracuseStep 16282079 = 24423119) B24423119
theorem B10854719 : Blo 1905435 10854719 := bstep (se 1 (by rfl) ⟨8141039, by rfl⟩ : syracuseStep 10854719 = 16282079) B16282079
theorem B7236479 : Blo 1905435 7236479 := bstep (se 1 (by rfl) ⟨5427359, by rfl⟩ : syracuseStep 7236479 = 10854719) B10854719
theorem B4824319 : Blo 1905435 4824319 := bstep (se 1 (by rfl) ⟨3618239, by rfl⟩ : syracuseStep 4824319 = 7236479) B7236479
theorem B6432425 : Blo 1905435 6432425 := bstep (se 2 (by rfl) ⟨2412159, by rfl⟩ : syracuseStep 6432425 = 4824319) B4824319
theorem B4288283 : Blo 1905435 4288283 := bstep (se 1 (by rfl) ⟨3216212, by rfl⟩ : syracuseStep 4288283 = 6432425) B6432425
theorem B2858855 : Blo 1905435 2858855 := bstep (se 1 (by rfl) ⟨2144141, by rfl⟩ : syracuseStep 2858855 = 4288283) B4288283
theorem B1905903 : Blo 1905435 1905903 := bstep (se 1 (by rfl) ⟨1429427, by rfl⟩ : syracuseStep 1905903 = 2858855) B2858855
theorem B2858861 : Blo 1905435 2858861 := bbase (se 3 (by rfl) ⟨536036, by rfl⟩ : syracuseStep 2858861 = 1072073) (by norm_num)
theorem B1905907 : Blo 1905435 1905907 := bstep (se 1 (by rfl) ⟨1429430, by rfl⟩ : syracuseStep 1905907 = 2858861) B2858861
theorem B4288301 : Blo 1905435 4288301 := bbase (se 3 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 4288301 = 1608113) (by norm_num)
theorem B2858867 : Blo 1905435 2858867 := bstep (se 1 (by rfl) ⟨2144150, by rfl⟩ : syracuseStep 2858867 = 4288301) B4288301
theorem B1905911 : Blo 1905435 1905911 := bstep (se 1 (by rfl) ⟨1429433, by rfl⟩ : syracuseStep 1905911 = 2858867) B2858867
theorem B8141093 : Blo 1905435 8141093 := bbase (se 4 (by rfl) ⟨763227, by rfl⟩ : syracuseStep 8141093 = 1526455) (by norm_num)
theorem B5427395 : Blo 1905435 5427395 := bstep (se 1 (by rfl) ⟨4070546, by rfl⟩ : syracuseStep 5427395 = 8141093) B8141093
theorem B3618263 : Blo 1905435 3618263 := bstep (se 1 (by rfl) ⟨2713697, by rfl⟩ : syracuseStep 3618263 = 5427395) B5427395
theorem B2412175 : Blo 1905435 2412175 := bstep (se 1 (by rfl) ⟨1809131, by rfl⟩ : syracuseStep 2412175 = 3618263) B3618263
theorem B3216233 : Blo 1905435 3216233 := bstep (se 2 (by rfl) ⟨1206087, by rfl⟩ : syracuseStep 3216233 = 2412175) B2412175
theorem B2144155 : Blo 1905435 2144155 := bstep (se 1 (by rfl) ⟨1608116, by rfl⟩ : syracuseStep 2144155 = 3216233) B3216233
theorem B2858873 : Blo 1905435 2858873 := bstep (se 2 (by rfl) ⟨1072077, by rfl⟩ : syracuseStep 2858873 = 2144155) B2144155
theorem B1905915 : Blo 1905435 1905915 := bstep (se 1 (by rfl) ⟨1429436, by rfl⟩ : syracuseStep 1905915 = 2858873) B2858873
theorem B4579373 : Blo 1905435 4579373 := bbase (se 3 (by rfl) ⟨858632, by rfl⟩ : syracuseStep 4579373 = 1717265) (by norm_num)
theorem B12211661 : Blo 1905435 12211661 := bstep (se 3 (by rfl) ⟨2289686, by rfl⟩ : syracuseStep 12211661 = 4579373) B4579373
theorem B32564429 : Blo 1905435 32564429 := bstep (se 3 (by rfl) ⟨6105830, by rfl⟩ : syracuseStep 32564429 = 12211661) B12211661
theorem B21709619 : Blo 1905435 21709619 := bstep (se 1 (by rfl) ⟨16282214, by rfl⟩ : syracuseStep 21709619 = 32564429) B32564429
theorem B14473079 : Blo 1905435 14473079 := bstep (se 1 (by rfl) ⟨10854809, by rfl⟩ : syracuseStep 14473079 = 21709619) B21709619
theorem B9648719 : Blo 1905435 9648719 := bstep (se 1 (by rfl) ⟨7236539, by rfl⟩ : syracuseStep 9648719 = 14473079) B14473079
theorem B6432479 : Blo 1905435 6432479 := bstep (se 1 (by rfl) ⟨4824359, by rfl⟩ : syracuseStep 6432479 = 9648719) B9648719
theorem B4288319 : Blo 1905435 4288319 := bstep (se 1 (by rfl) ⟨3216239, by rfl⟩ : syracuseStep 4288319 = 6432479) B6432479
theorem B2858879 : Blo 1905435 2858879 := bstep (se 1 (by rfl) ⟨2144159, by rfl⟩ : syracuseStep 2858879 = 4288319) B4288319
theorem B1905919 : Blo 1905435 1905919 := bstep (se 1 (by rfl) ⟨1429439, by rfl⟩ : syracuseStep 1905919 = 2858879) B2858879
theorem B2858885 : Blo 1905435 2858885 := bbase (se 4 (by rfl) ⟨268020, by rfl⟩ : syracuseStep 2858885 = 536041) (by norm_num)
theorem B1905923 : Blo 1905435 1905923 := bstep (se 1 (by rfl) ⟨1429442, by rfl⟩ : syracuseStep 1905923 = 2858885) B2858885
theorem B3216253 : Blo 1905435 3216253 := bbase (se 3 (by rfl) ⟨603047, by rfl⟩ : syracuseStep 3216253 = 1206095) (by norm_num)
theorem B4288337 : Blo 1905435 4288337 := bstep (se 2 (by rfl) ⟨1608126, by rfl⟩ : syracuseStep 4288337 = 3216253) B3216253
theorem B2858891 : Blo 1905435 2858891 := bstep (se 1 (by rfl) ⟨2144168, by rfl⟩ : syracuseStep 2858891 = 4288337) B4288337
theorem B1905927 : Blo 1905435 1905927 := bstep (se 1 (by rfl) ⟨1429445, by rfl⟩ : syracuseStep 1905927 = 2858891) B2858891
theorem B2144173 : Blo 1905435 2144173 := bbase (se 3 (by rfl) ⟨402032, by rfl⟩ : syracuseStep 2144173 = 804065) (by norm_num)
theorem B2858897 : Blo 1905435 2858897 := bstep (se 2 (by rfl) ⟨1072086, by rfl⟩ : syracuseStep 2858897 = 2144173) B2144173
theorem B1905931 : Blo 1905435 1905931 := bstep (se 1 (by rfl) ⟨1429448, by rfl⟩ : syracuseStep 1905931 = 2858897) B2858897
theorem B6432533 : Blo 1905435 6432533 := bbase (se 6 (by rfl) ⟨150762, by rfl⟩ : syracuseStep 6432533 = 301525) (by norm_num)
theorem B4288355 : Blo 1905435 4288355 := bstep (se 1 (by rfl) ⟨3216266, by rfl⟩ : syracuseStep 4288355 = 6432533) B6432533
theorem B2858903 : Blo 1905435 2858903 := bstep (se 1 (by rfl) ⟨2144177, by rfl⟩ : syracuseStep 2858903 = 4288355) B4288355
theorem B1905935 : Blo 1905435 1905935 := bstep (se 1 (by rfl) ⟨1429451, by rfl⟩ : syracuseStep 1905935 = 2858903) B2858903
theorem B2858909 : Blo 1905435 2858909 := bbase (se 3 (by rfl) ⟨536045, by rfl⟩ : syracuseStep 2858909 = 1072091) (by norm_num)
theorem B1905939 : Blo 1905435 1905939 := bstep (se 1 (by rfl) ⟨1429454, by rfl⟩ : syracuseStep 1905939 = 2858909) B2858909
theorem B4288373 : Blo 1905435 4288373 := bbase (se 5 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 4288373 = 402035) (by norm_num)
theorem B2858915 : Blo 1905435 2858915 := bstep (se 1 (by rfl) ⟨2144186, by rfl⟩ : syracuseStep 2858915 = 4288373) B4288373
theorem B1905943 : Blo 1905435 1905943 := bstep (se 1 (by rfl) ⟨1429457, by rfl⟩ : syracuseStep 1905943 = 2858915) B2858915
theorem B3434581 : Blo 1905435 3434581 := bbase (se 8 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 3434581 = 40249) (by norm_num)
theorem B18317765 : Blo 1905435 18317765 := bstep (se 4 (by rfl) ⟨1717290, by rfl⟩ : syracuseStep 18317765 = 3434581) B3434581
theorem B12211843 : Blo 1905435 12211843 := bstep (se 1 (by rfl) ⟨9158882, by rfl⟩ : syracuseStep 12211843 = 18317765) B18317765
theorem B16282457 : Blo 1905435 16282457 := bstep (se 2 (by rfl) ⟨6105921, by rfl⟩ : syracuseStep 16282457 = 12211843) B12211843
theorem B10854971 : Blo 1905435 10854971 := bstep (se 1 (by rfl) ⟨8141228, by rfl⟩ : syracuseStep 10854971 = 16282457) B16282457
theorem B7236647 : Blo 1905435 7236647 := bstep (se 1 (by rfl) ⟨5427485, by rfl⟩ : syracuseStep 7236647 = 10854971) B10854971
theorem B4824431 : Blo 1905435 4824431 := bstep (se 1 (by rfl) ⟨3618323, by rfl⟩ : syracuseStep 4824431 = 7236647) B7236647
theorem B3216287 : Blo 1905435 3216287 := bstep (se 1 (by rfl) ⟨2412215, by rfl⟩ : syracuseStep 3216287 = 4824431) B4824431
theorem B2144191 : Blo 1905435 2144191 := bstep (se 1 (by rfl) ⟨1608143, by rfl⟩ : syracuseStep 2144191 = 3216287) B3216287
theorem B2858921 : Blo 1905435 2858921 := bstep (se 2 (by rfl) ⟨1072095, by rfl⟩ : syracuseStep 2858921 = 2144191) B2144191
theorem B1905947 : Blo 1905435 1905947 := bstep (se 1 (by rfl) ⟨1429460, by rfl⟩ : syracuseStep 1905947 = 2858921) B2858921
theorem B7236661 : Blo 1905435 7236661 := bbase (se 5 (by rfl) ⟨339218, by rfl⟩ : syracuseStep 7236661 = 678437) (by norm_num)
theorem B9648881 : Blo 1905435 9648881 := bstep (se 2 (by rfl) ⟨3618330, by rfl⟩ : syracuseStep 9648881 = 7236661) B7236661
theorem B6432587 : Blo 1905435 6432587 := bstep (se 1 (by rfl) ⟨4824440, by rfl⟩ : syracuseStep 6432587 = 9648881) B9648881
theorem B4288391 : Blo 1905435 4288391 := bstep (se 1 (by rfl) ⟨3216293, by rfl⟩ : syracuseStep 4288391 = 6432587) B6432587
theorem B2858927 : Blo 1905435 2858927 := bstep (se 1 (by rfl) ⟨2144195, by rfl⟩ : syracuseStep 2858927 = 4288391) B4288391
theorem B1905951 : Blo 1905435 1905951 := bstep (se 1 (by rfl) ⟨1429463, by rfl⟩ : syracuseStep 1905951 = 2858927) B2858927
theorem B2858933 : Blo 1905435 2858933 := bbase (se 5 (by rfl) ⟨134012, by rfl⟩ : syracuseStep 2858933 = 268025) (by norm_num)
theorem B1905955 : Blo 1905435 1905955 := bstep (se 1 (by rfl) ⟨1429466, by rfl⟩ : syracuseStep 1905955 = 2858933) B2858933
theorem B4824461 : Blo 1905435 4824461 := bbase (se 3 (by rfl) ⟨904586, by rfl⟩ : syracuseStep 4824461 = 1809173) (by norm_num)
theorem B3216307 : Blo 1905435 3216307 := bstep (se 1 (by rfl) ⟨2412230, by rfl⟩ : syracuseStep 3216307 = 4824461) B4824461
theorem B4288409 : Blo 1905435 4288409 := bstep (se 2 (by rfl) ⟨1608153, by rfl⟩ : syracuseStep 4288409 = 3216307) B3216307
theorem B2858939 : Blo 1905435 2858939 := bstep (se 1 (by rfl) ⟨2144204, by rfl⟩ : syracuseStep 2858939 = 4288409) B4288409
theorem B1905959 : Blo 1905435 1905959 := bstep (se 1 (by rfl) ⟨1429469, by rfl⟩ : syracuseStep 1905959 = 2858939) B2858939
theorem B2144209 : Blo 1905435 2144209 := bbase (se 2 (by rfl) ⟨804078, by rfl⟩ : syracuseStep 2144209 = 1608157) (by norm_num)
theorem B2858945 : Blo 1905435 2858945 := bstep (se 2 (by rfl) ⟨1072104, by rfl⟩ : syracuseStep 2858945 = 2144209) B2144209
theorem B1905963 : Blo 1905435 1905963 := bstep (se 1 (by rfl) ⟨1429472, by rfl⟩ : syracuseStep 1905963 = 2858945) B2858945
theorem B2289745 : Blo 1905435 2289745 := bbase (se 2 (by rfl) ⟨858654, by rfl⟩ : syracuseStep 2289745 = 1717309) (by norm_num)
theorem B3052993 : Blo 1905435 3052993 := bstep (se 2 (by rfl) ⟨1144872, by rfl⟩ : syracuseStep 3052993 = 2289745) B2289745
theorem B4070657 : Blo 1905435 4070657 := bstep (se 2 (by rfl) ⟨1526496, by rfl⟩ : syracuseStep 4070657 = 3052993) B3052993
theorem B2713771 : Blo 1905435 2713771 := bstep (se 1 (by rfl) ⟨2035328, by rfl⟩ : syracuseStep 2713771 = 4070657) B4070657
theorem B3618361 : Blo 1905435 3618361 := bstep (se 2 (by rfl) ⟨1356885, by rfl⟩ : syracuseStep 3618361 = 2713771) B2713771
theorem B4824481 : Blo 1905435 4824481 := bstep (se 2 (by rfl) ⟨1809180, by rfl⟩ : syracuseStep 4824481 = 3618361) B3618361
theorem B6432641 : Blo 1905435 6432641 := bstep (se 2 (by rfl) ⟨2412240, by rfl⟩ : syracuseStep 6432641 = 4824481) B4824481
theorem B4288427 : Blo 1905435 4288427 := bstep (se 1 (by rfl) ⟨3216320, by rfl⟩ : syracuseStep 4288427 = 6432641) B6432641
theorem B2858951 : Blo 1905435 2858951 := bstep (se 1 (by rfl) ⟨2144213, by rfl⟩ : syracuseStep 2858951 = 4288427) B4288427
theorem B1905967 : Blo 1905435 1905967 := bstep (se 1 (by rfl) ⟨1429475, by rfl⟩ : syracuseStep 1905967 = 2858951) B2858951
theorem B2858957 : Blo 1905435 2858957 := bbase (se 3 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 2858957 = 1072109) (by norm_num)
theorem B1905971 : Blo 1905435 1905971 := bstep (se 1 (by rfl) ⟨1429478, by rfl⟩ : syracuseStep 1905971 = 2858957) B2858957
theorem B4288445 : Blo 1905435 4288445 := bbase (se 3 (by rfl) ⟨804083, by rfl⟩ : syracuseStep 4288445 = 1608167) (by norm_num)
theorem B2858963 : Blo 1905435 2858963 := bstep (se 1 (by rfl) ⟨2144222, by rfl⟩ : syracuseStep 2858963 = 4288445) B4288445
theorem B1905975 : Blo 1905435 1905975 := bstep (se 1 (by rfl) ⟨1429481, by rfl⟩ : syracuseStep 1905975 = 2858963) B2858963
theorem B3216341 : Blo 1905435 3216341 := bbase (se 7 (by rfl) ⟨37691, by rfl⟩ : syracuseStep 3216341 = 75383) (by norm_num)
theorem B2144227 : Blo 1905435 2144227 := bstep (se 1 (by rfl) ⟨1608170, by rfl⟩ : syracuseStep 2144227 = 3216341) B3216341
theorem B2858969 : Blo 1905435 2858969 := bstep (se 2 (by rfl) ⟨1072113, by rfl⟩ : syracuseStep 2858969 = 2144227) B2144227
theorem B1905979 : Blo 1905435 1905979 := bstep (se 1 (by rfl) ⟨1429484, by rfl⟩ : syracuseStep 1905979 = 2858969) B2858969
theorem B8141381 : Blo 1905435 8141381 := bbase (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) (by norm_num)
theorem B5427587 : Blo 1905435 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B14473565 : Blo 1905435 14473565 := bstep (se 3 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 14473565 = 5427587) B5427587
theorem B9649043 : Blo 1905435 9649043 := bstep (se 1 (by rfl) ⟨7236782, by rfl⟩ : syracuseStep 9649043 = 14473565) B14473565
theorem B6432695 : Blo 1905435 6432695 := bstep (se 1 (by rfl) ⟨4824521, by rfl⟩ : syracuseStep 6432695 = 9649043) B9649043
theorem B4288463 : Blo 1905435 4288463 := bstep (se 1 (by rfl) ⟨3216347, by rfl⟩ : syracuseStep 4288463 = 6432695) B6432695
theorem B2858975 : Blo 1905435 2858975 := bstep (se 1 (by rfl) ⟨2144231, by rfl⟩ : syracuseStep 2858975 = 4288463) B4288463
theorem B1905983 : Blo 1905435 1905983 := bstep (se 1 (by rfl) ⟨1429487, by rfl⟩ : syracuseStep 1905983 = 2858975) B2858975
theorem B2858981 : Blo 1905435 2858981 := bbase (se 4 (by rfl) ⟨268029, by rfl⟩ : syracuseStep 2858981 = 536059) (by norm_num)
theorem B1905987 : Blo 1905435 1905987 := bstep (se 1 (by rfl) ⟨1429490, by rfl⟩ : syracuseStep 1905987 = 2858981) B2858981
theorem B3260245 : Blo 1905435 3260245 := bbase (se 9 (by rfl) ⟨9551, by rfl⟩ : syracuseStep 3260245 = 19103) (by norm_num)
theorem B4346993 : Blo 1905435 4346993 := bstep (se 2 (by rfl) ⟨1630122, by rfl⟩ : syracuseStep 4346993 = 3260245) B3260245
theorem B11591981 : Blo 1905435 11591981 := bstep (se 3 (by rfl) ⟨2173496, by rfl⟩ : syracuseStep 11591981 = 4346993) B4346993
theorem B7727987 : Blo 1905435 7727987 := bstep (se 1 (by rfl) ⟨5795990, by rfl⟩ : syracuseStep 7727987 = 11591981) B11591981
theorem B20607965 : Blo 1905435 20607965 := bstep (se 3 (by rfl) ⟨3863993, by rfl⟩ : syracuseStep 20607965 = 7727987) B7727987
theorem B13738643 : Blo 1905435 13738643 := bstep (se 1 (by rfl) ⟨10303982, by rfl⟩ : syracuseStep 13738643 = 20607965) B20607965
theorem B9159095 : Blo 1905435 9159095 := bstep (se 1 (by rfl) ⟨6869321, by rfl⟩ : syracuseStep 9159095 = 13738643) B13738643
theorem B6106063 : Blo 1905435 6106063 := bstep (se 1 (by rfl) ⟨4579547, by rfl⟩ : syracuseStep 6106063 = 9159095) B9159095
theorem B8141417 : Blo 1905435 8141417 := bstep (se 2 (by rfl) ⟨3053031, by rfl⟩ : syracuseStep 8141417 = 6106063) B6106063
theorem B5427611 : Blo 1905435 5427611 := bstep (se 1 (by rfl) ⟨4070708, by rfl⟩ : syracuseStep 5427611 = 8141417) B8141417
theorem B3618407 : Blo 1905435 3618407 := bstep (se 1 (by rfl) ⟨2713805, by rfl⟩ : syracuseStep 3618407 = 5427611) B5427611
theorem B2412271 : Blo 1905435 2412271 := bstep (se 1 (by rfl) ⟨1809203, by rfl⟩ : syracuseStep 2412271 = 3618407) B3618407
theorem B3216361 : Blo 1905435 3216361 := bstep (se 2 (by rfl) ⟨1206135, by rfl⟩ : syracuseStep 3216361 = 2412271) B2412271
theorem B4288481 : Blo 1905435 4288481 := bstep (se 2 (by rfl) ⟨1608180, by rfl⟩ : syracuseStep 4288481 = 3216361) B3216361
theorem B2858987 : Blo 1905435 2858987 := bstep (se 1 (by rfl) ⟨2144240, by rfl⟩ : syracuseStep 2858987 = 4288481) B4288481
theorem B1905991 : Blo 1905435 1905991 := bstep (se 1 (by rfl) ⟨1429493, by rfl⟩ : syracuseStep 1905991 = 2858987) B2858987
theorem B2144245 : Blo 1905435 2144245 := bbase (se 5 (by rfl) ⟨100511, by rfl⟩ : syracuseStep 2144245 = 201023) (by norm_num)
theorem B2858993 : Blo 1905435 2858993 := bstep (se 2 (by rfl) ⟨1072122, by rfl⟩ : syracuseStep 2858993 = 2144245) B2144245
theorem B1905995 : Blo 1905435 1905995 := bstep (se 1 (by rfl) ⟨1429496, by rfl⟩ : syracuseStep 1905995 = 2858993) B2858993
theorem B2412281 : Blo 1905435 2412281 := bbase (se 2 (by rfl) ⟨904605, by rfl⟩ : syracuseStep 2412281 = 1809211) (by norm_num)
theorem B6432749 : Blo 1905435 6432749 := bstep (se 3 (by rfl) ⟨1206140, by rfl⟩ : syracuseStep 6432749 = 2412281) B2412281
theorem B4288499 : Blo 1905435 4288499 := bstep (se 1 (by rfl) ⟨3216374, by rfl⟩ : syracuseStep 4288499 = 6432749) B6432749
theorem B2858999 : Blo 1905435 2858999 := bstep (se 1 (by rfl) ⟨2144249, by rfl⟩ : syracuseStep 2858999 = 4288499) B4288499
theorem B1905999 : Blo 1905435 1905999 := bstep (se 1 (by rfl) ⟨1429499, by rfl⟩ : syracuseStep 1905999 = 2858999) B2858999
theorem B2859005 : Blo 1905435 2859005 := bbase (se 3 (by rfl) ⟨536063, by rfl⟩ : syracuseStep 2859005 = 1072127) (by norm_num)
theorem B1906003 : Blo 1905435 1906003 := bstep (se 1 (by rfl) ⟨1429502, by rfl⟩ : syracuseStep 1906003 = 2859005) B2859005
theorem B4288517 : Blo 1905435 4288517 := bbase (se 4 (by rfl) ⟨402048, by rfl⟩ : syracuseStep 4288517 = 804097) (by norm_num)
theorem B2859011 : Blo 1905435 2859011 := bstep (se 1 (by rfl) ⟨2144258, by rfl⟩ : syracuseStep 2859011 = 4288517) B4288517
theorem B1906007 : Blo 1905435 1906007 := bstep (se 1 (by rfl) ⟨1429505, by rfl⟩ : syracuseStep 1906007 = 2859011) B2859011
theorem B3618445 : Blo 1905435 3618445 := bbase (se 3 (by rfl) ⟨678458, by rfl⟩ : syracuseStep 3618445 = 1356917) (by norm_num)
theorem B4824593 : Blo 1905435 4824593 := bstep (se 2 (by rfl) ⟨1809222, by rfl⟩ : syracuseStep 4824593 = 3618445) B3618445
theorem B3216395 : Blo 1905435 3216395 := bstep (se 1 (by rfl) ⟨2412296, by rfl⟩ : syracuseStep 3216395 = 4824593) B4824593
theorem B2144263 : Blo 1905435 2144263 := bstep (se 1 (by rfl) ⟨1608197, by rfl⟩ : syracuseStep 2144263 = 3216395) B3216395
theorem B2859017 : Blo 1905435 2859017 := bstep (se 2 (by rfl) ⟨1072131, by rfl⟩ : syracuseStep 2859017 = 2144263) B2144263
theorem B1906011 : Blo 1905435 1906011 := bstep (se 1 (by rfl) ⟨1429508, by rfl⟩ : syracuseStep 1906011 = 2859017) B2859017
theorem B9649205 : Blo 1905435 9649205 := bbase (se 5 (by rfl) ⟨452306, by rfl⟩ : syracuseStep 9649205 = 904613) (by norm_num)
theorem B6432803 : Blo 1905435 6432803 := bstep (se 1 (by rfl) ⟨4824602, by rfl⟩ : syracuseStep 6432803 = 9649205) B9649205
theorem B4288535 : Blo 1905435 4288535 := bstep (se 1 (by rfl) ⟨3216401, by rfl⟩ : syracuseStep 4288535 = 6432803) B6432803
theorem B2859023 : Blo 1905435 2859023 := bstep (se 1 (by rfl) ⟨2144267, by rfl⟩ : syracuseStep 2859023 = 4288535) B4288535
theorem B1906015 : Blo 1905435 1906015 := bstep (se 1 (by rfl) ⟨1429511, by rfl⟩ : syracuseStep 1906015 = 2859023) B2859023
theorem B2859029 : Blo 1905435 2859029 := bbase (se 6 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 2859029 = 134017) (by norm_num)
theorem B1906019 : Blo 1905435 1906019 := bstep (se 1 (by rfl) ⟨1429514, by rfl⟩ : syracuseStep 1906019 = 2859029) B2859029
theorem B3667837 : Blo 1905435 3667837 := bbase (se 3 (by rfl) ⟨687719, by rfl⟩ : syracuseStep 3667837 = 1375439) (by norm_num)
theorem B4890449 : Blo 1905435 4890449 := bstep (se 2 (by rfl) ⟨1833918, by rfl⟩ : syracuseStep 4890449 = 3667837) B3667837
theorem B3260299 : Blo 1905435 3260299 := bstep (se 1 (by rfl) ⟨2445224, by rfl⟩ : syracuseStep 3260299 = 4890449) B4890449
theorem B4347065 : Blo 1905435 4347065 := bstep (se 2 (by rfl) ⟨1630149, by rfl⟩ : syracuseStep 4347065 = 3260299) B3260299
theorem B11592173 : Blo 1905435 11592173 := bstep (se 3 (by rfl) ⟨2173532, by rfl⟩ : syracuseStep 11592173 = 4347065) B4347065
theorem B30912461 : Blo 1905435 30912461 := bstep (se 3 (by rfl) ⟨5796086, by rfl⟩ : syracuseStep 30912461 = 11592173) B11592173
theorem B20608307 : Blo 1905435 20608307 := bstep (se 1 (by rfl) ⟨15456230, by rfl⟩ : syracuseStep 20608307 = 30912461) B30912461
theorem B13738871 : Blo 1905435 13738871 := bstep (se 1 (by rfl) ⟨10304153, by rfl⟩ : syracuseStep 13738871 = 20608307) B20608307
theorem B9159247 : Blo 1905435 9159247 := bstep (se 1 (by rfl) ⟨6869435, by rfl⟩ : syracuseStep 9159247 = 13738871) B13738871
theorem B12212329 : Blo 1905435 12212329 := bstep (se 2 (by rfl) ⟨4579623, by rfl⟩ : syracuseStep 12212329 = 9159247) B9159247
theorem B16283105 : Blo 1905435 16283105 := bstep (se 2 (by rfl) ⟨6106164, by rfl⟩ : syracuseStep 16283105 = 12212329) B12212329
theorem B10855403 : Blo 1905435 10855403 := bstep (se 1 (by rfl) ⟨8141552, by rfl⟩ : syracuseStep 10855403 = 16283105) B16283105
theorem B7236935 : Blo 1905435 7236935 := bstep (se 1 (by rfl) ⟨5427701, by rfl⟩ : syracuseStep 7236935 = 10855403) B10855403
theorem B4824623 : Blo 1905435 4824623 := bstep (se 1 (by rfl) ⟨3618467, by rfl⟩ : syracuseStep 4824623 = 7236935) B7236935
theorem B3216415 : Blo 1905435 3216415 := bstep (se 1 (by rfl) ⟨2412311, by rfl⟩ : syracuseStep 3216415 = 4824623) B4824623
theorem B4288553 : Blo 1905435 4288553 := bstep (se 2 (by rfl) ⟨1608207, by rfl⟩ : syracuseStep 4288553 = 3216415) B3216415
theorem B2859035 : Blo 1905435 2859035 := bstep (se 1 (by rfl) ⟨2144276, by rfl⟩ : syracuseStep 2859035 = 4288553) B4288553
theorem B1906023 : Blo 1905435 1906023 := bstep (se 1 (by rfl) ⟨1429517, by rfl⟩ : syracuseStep 1906023 = 2859035) B2859035
theorem B2144281 : Blo 1905435 2144281 := bbase (se 2 (by rfl) ⟨804105, by rfl⟩ : syracuseStep 2144281 = 1608211) (by norm_num)
theorem B2859041 : Blo 1905435 2859041 := bstep (se 2 (by rfl) ⟨1072140, by rfl⟩ : syracuseStep 2859041 = 2144281) B2144281
theorem B1906027 : Blo 1905435 1906027 := bstep (se 1 (by rfl) ⟨1429520, by rfl⟩ : syracuseStep 1906027 = 2859041) B2859041
theorem B7236965 : Blo 1905435 7236965 := bbase (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) (by norm_num)
theorem B4824643 : Blo 1905435 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B6432857 : Blo 1905435 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B4288571 : Blo 1905435 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B2859047 : Blo 1905435 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B1906031 : Blo 1905435 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B2859053 : Blo 1905435 2859053 := bbase (se 3 (by rfl) ⟨536072, by rfl⟩ : syracuseStep 2859053 = 1072145) (by norm_num)
theorem B1906035 : Blo 1905435 1906035 := bstep (se 1 (by rfl) ⟨1429526, by rfl⟩ : syracuseStep 1906035 = 2859053) B2859053
theorem B4288589 : Blo 1905435 4288589 := bbase (se 3 (by rfl) ⟨804110, by rfl⟩ : syracuseStep 4288589 = 1608221) (by norm_num)
theorem B2859059 : Blo 1905435 2859059 := bstep (se 1 (by rfl) ⟨2144294, by rfl⟩ : syracuseStep 2859059 = 4288589) B4288589
theorem B1906039 : Blo 1905435 1906039 := bstep (se 1 (by rfl) ⟨1429529, by rfl⟩ : syracuseStep 1906039 = 2859059) B2859059
theorem B2412337 : Blo 1905435 2412337 := bbase (se 2 (by rfl) ⟨904626, by rfl⟩ : syracuseStep 2412337 = 1809253) (by norm_num)
theorem B3216449 : Blo 1905435 3216449 := bstep (se 2 (by rfl) ⟨1206168, by rfl⟩ : syracuseStep 3216449 = 2412337) B2412337
theorem B2144299 : Blo 1905435 2144299 := bstep (se 1 (by rfl) ⟨1608224, by rfl⟩ : syracuseStep 2144299 = 3216449) B3216449
theorem B2859065 : Blo 1905435 2859065 := bstep (se 2 (by rfl) ⟨1072149, by rfl⟩ : syracuseStep 2859065 = 2144299) B2144299
theorem B1906043 : Blo 1905435 1906043 := bstep (se 1 (by rfl) ⟨1429532, by rfl⟩ : syracuseStep 1906043 = 2859065) B2859065
theorem B3260341 : Blo 1905435 3260341 := bbase (se 5 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 3260341 = 305657) (by norm_num)
theorem B4347121 : Blo 1905435 4347121 := bstep (se 2 (by rfl) ⟨1630170, by rfl⟩ : syracuseStep 4347121 = 3260341) B3260341
theorem B5796161 : Blo 1905435 5796161 := bstep (se 2 (by rfl) ⟨2173560, by rfl⟩ : syracuseStep 5796161 = 4347121) B4347121
theorem B3864107 : Blo 1905435 3864107 := bstep (se 1 (by rfl) ⟨2898080, by rfl⟩ : syracuseStep 3864107 = 5796161) B5796161
theorem B2576071 : Blo 1905435 2576071 := bstep (se 1 (by rfl) ⟨1932053, by rfl⟩ : syracuseStep 2576071 = 3864107) B3864107
theorem B3434761 : Blo 1905435 3434761 := bstep (se 2 (by rfl) ⟨1288035, by rfl⟩ : syracuseStep 3434761 = 2576071) B2576071
theorem B4579681 : Blo 1905435 4579681 := bstep (se 2 (by rfl) ⟨1717380, by rfl⟩ : syracuseStep 4579681 = 3434761) B3434761
theorem B6106241 : Blo 1905435 6106241 := bstep (se 2 (by rfl) ⟨2289840, by rfl⟩ : syracuseStep 6106241 = 4579681) B4579681
theorem B4070827 : Blo 1905435 4070827 := bstep (se 1 (by rfl) ⟨3053120, by rfl⟩ : syracuseStep 4070827 = 6106241) B6106241
theorem B21711077 : Blo 1905435 21711077 := bstep (se 4 (by rfl) ⟨2035413, by rfl⟩ : syracuseStep 21711077 = 4070827) B4070827
theorem B14474051 : Blo 1905435 14474051 := bstep (se 1 (by rfl) ⟨10855538, by rfl⟩ : syracuseStep 14474051 = 21711077) B21711077
theorem B9649367 : Blo 1905435 9649367 := bstep (se 1 (by rfl) ⟨7237025, by rfl⟩ : syracuseStep 9649367 = 14474051) B14474051
theorem B6432911 : Blo 1905435 6432911 := bstep (se 1 (by rfl) ⟨4824683, by rfl⟩ : syracuseStep 6432911 = 9649367) B9649367
theorem B4288607 : Blo 1905435 4288607 := bstep (se 1 (by rfl) ⟨3216455, by rfl⟩ : syracuseStep 4288607 = 6432911) B6432911
theorem B2859071 : Blo 1905435 2859071 := bstep (se 1 (by rfl) ⟨2144303, by rfl⟩ : syracuseStep 2859071 = 4288607) B4288607
theorem B1906047 : Blo 1905435 1906047 := bstep (se 1 (by rfl) ⟨1429535, by rfl⟩ : syracuseStep 1906047 = 2859071) B2859071
theorem B2859077 : Blo 1905435 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B1906051 : Blo 1905435 1906051 := bstep (se 1 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 1906051 = 2859077) B2859077
theorem B3216469 : Blo 1905435 3216469 := bbase (se 8 (by rfl) ⟨18846, by rfl⟩ : syracuseStep 3216469 = 37693) (by norm_num)
theorem B4288625 : Blo 1905435 4288625 := bstep (se 2 (by rfl) ⟨1608234, by rfl⟩ : syracuseStep 4288625 = 3216469) B3216469
theorem B2859083 : Blo 1905435 2859083 := bstep (se 1 (by rfl) ⟨2144312, by rfl⟩ : syracuseStep 2859083 = 4288625) B4288625
theorem B1906055 : Blo 1905435 1906055 := bstep (se 1 (by rfl) ⟨1429541, by rfl⟩ : syracuseStep 1906055 = 2859083) B2859083
theorem B2144317 : Blo 1905435 2144317 := bbase (se 3 (by rfl) ⟨402059, by rfl⟩ : syracuseStep 2144317 = 804119) (by norm_num)
theorem B2859089 : Blo 1905435 2859089 := bstep (se 2 (by rfl) ⟨1072158, by rfl⟩ : syracuseStep 2859089 = 2144317) B2144317
theorem B1906059 : Blo 1905435 1906059 := bstep (se 1 (by rfl) ⟨1429544, by rfl⟩ : syracuseStep 1906059 = 2859089) B2859089
theorem B6432965 : Blo 1905435 6432965 := bbase (se 4 (by rfl) ⟨603090, by rfl⟩ : syracuseStep 6432965 = 1206181) (by norm_num)
theorem B4288643 : Blo 1905435 4288643 := bstep (se 1 (by rfl) ⟨3216482, by rfl⟩ : syracuseStep 4288643 = 6432965) B6432965
theorem B2859095 : Blo 1905435 2859095 := bstep (se 1 (by rfl) ⟨2144321, by rfl⟩ : syracuseStep 2859095 = 4288643) B4288643
theorem B1906063 : Blo 1905435 1906063 := bstep (se 1 (by rfl) ⟨1429547, by rfl⟩ : syracuseStep 1906063 = 2859095) B2859095
theorem B2859101 : Blo 1905435 2859101 := bbase (se 3 (by rfl) ⟨536081, by rfl⟩ : syracuseStep 2859101 = 1072163) (by norm_num)
theorem B1906067 : Blo 1905435 1906067 := bstep (se 1 (by rfl) ⟨1429550, by rfl⟩ : syracuseStep 1906067 = 2859101) B2859101
theorem B4288661 : Blo 1905435 4288661 := bbase (se 6 (by rfl) ⟨100515, by rfl⟩ : syracuseStep 4288661 = 201031) (by norm_num)
theorem B2859107 : Blo 1905435 2859107 := bstep (se 1 (by rfl) ⟨2144330, by rfl⟩ : syracuseStep 2859107 = 4288661) B4288661
theorem B1906071 : Blo 1905435 1906071 := bstep (se 1 (by rfl) ⟨1429553, by rfl⟩ : syracuseStep 1906071 = 2859107) B2859107
theorem B2713925 : Blo 1905435 2713925 := bbase (se 4 (by rfl) ⟨254430, by rfl⟩ : syracuseStep 2713925 = 508861) (by norm_num)
theorem B7237133 : Blo 1905435 7237133 := bstep (se 3 (by rfl) ⟨1356962, by rfl⟩ : syracuseStep 7237133 = 2713925) B2713925
theorem B4824755 : Blo 1905435 4824755 := bstep (se 1 (by rfl) ⟨3618566, by rfl⟩ : syracuseStep 4824755 = 7237133) B7237133
theorem B3216503 : Blo 1905435 3216503 := bstep (se 1 (by rfl) ⟨2412377, by rfl⟩ : syracuseStep 3216503 = 4824755) B4824755
theorem B2144335 : Blo 1905435 2144335 := bstep (se 1 (by rfl) ⟨1608251, by rfl⟩ : syracuseStep 2144335 = 3216503) B3216503
theorem B2859113 : Blo 1905435 2859113 := bstep (se 2 (by rfl) ⟨1072167, by rfl⟩ : syracuseStep 2859113 = 2144335) B2144335
theorem B1906075 : Blo 1905435 1906075 := bstep (se 1 (by rfl) ⟨1429556, by rfl⟩ : syracuseStep 1906075 = 2859113) B2859113
theorem B38158229 : Blo 1905435 38158229 := bbase (se 6 (by rfl) ⟨894333, by rfl⟩ : syracuseStep 38158229 = 1788667) (by norm_num)
theorem B25438819 : Blo 1905435 25438819 := bstep (se 1 (by rfl) ⟨19079114, by rfl⟩ : syracuseStep 25438819 = 38158229) B38158229
theorem B33918425 : Blo 1905435 33918425 := bstep (se 2 (by rfl) ⟨12719409, by rfl⟩ : syracuseStep 33918425 = 25438819) B25438819
theorem B22612283 : Blo 1905435 22612283 := bstep (se 1 (by rfl) ⟨16959212, by rfl⟩ : syracuseStep 22612283 = 33918425) B33918425
theorem B15074855 : Blo 1905435 15074855 := bstep (se 1 (by rfl) ⟨11306141, by rfl⟩ : syracuseStep 15074855 = 22612283) B22612283
theorem B10049903 : Blo 1905435 10049903 := bstep (se 1 (by rfl) ⟨7537427, by rfl⟩ : syracuseStep 10049903 = 15074855) B15074855
theorem B6699935 : Blo 1905435 6699935 := bstep (se 1 (by rfl) ⟨5024951, by rfl⟩ : syracuseStep 6699935 = 10049903) B10049903
theorem B17866493 : Blo 1905435 17866493 := bstep (se 3 (by rfl) ⟨3349967, by rfl⟩ : syracuseStep 17866493 = 6699935) B6699935
theorem B11910995 : Blo 1905435 11910995 := bstep (se 1 (by rfl) ⟨8933246, by rfl⟩ : syracuseStep 11910995 = 17866493) B17866493
theorem B7940663 : Blo 1905435 7940663 := bstep (se 1 (by rfl) ⟨5955497, by rfl⟩ : syracuseStep 7940663 = 11910995) B11910995
theorem B5293775 : Blo 1905435 5293775 := bstep (se 1 (by rfl) ⟨3970331, by rfl⟩ : syracuseStep 5293775 = 7940663) B7940663
theorem B14116733 : Blo 1905435 14116733 := bstep (se 3 (by rfl) ⟨2646887, by rfl⟩ : syracuseStep 14116733 = 5293775) B5293775
theorem B9411155 : Blo 1905435 9411155 := bstep (se 1 (by rfl) ⟨7058366, by rfl⟩ : syracuseStep 9411155 = 14116733) B14116733
theorem B6274103 : Blo 1905435 6274103 := bstep (se 1 (by rfl) ⟨4705577, by rfl⟩ : syracuseStep 6274103 = 9411155) B9411155
theorem B66923765 : Blo 1905435 66923765 := bstep (se 5 (by rfl) ⟨3137051, by rfl⟩ : syracuseStep 66923765 = 6274103) B6274103
theorem B44615843 : Blo 1905435 44615843 := bstep (se 1 (by rfl) ⟨33461882, by rfl⟩ : syracuseStep 44615843 = 66923765) B66923765
theorem B29743895 : Blo 1905435 29743895 := bstep (se 1 (by rfl) ⟨22307921, by rfl⟩ : syracuseStep 29743895 = 44615843) B44615843
theorem B79317053 : Blo 1905435 79317053 := bstep (se 3 (by rfl) ⟨14871947, by rfl⟩ : syracuseStep 79317053 = 29743895) B29743895
theorem B52878035 : Blo 1905435 52878035 := bstep (se 1 (by rfl) ⟨39658526, by rfl⟩ : syracuseStep 52878035 = 79317053) B79317053
theorem B35252023 : Blo 1905435 35252023 := bstep (se 1 (by rfl) ⟨26439017, by rfl⟩ : syracuseStep 35252023 = 52878035) B52878035
theorem B47002697 : Blo 1905435 47002697 := bstep (se 2 (by rfl) ⟨17626011, by rfl⟩ : syracuseStep 47002697 = 35252023) B35252023
theorem B31335131 : Blo 1905435 31335131 := bstep (se 1 (by rfl) ⟨23501348, by rfl⟩ : syracuseStep 31335131 = 47002697) B47002697
theorem B83560349 : Blo 1905435 83560349 := bstep (se 3 (by rfl) ⟨15667565, by rfl⟩ : syracuseStep 83560349 = 31335131) B31335131
theorem B55706899 : Blo 1905435 55706899 := bstep (se 1 (by rfl) ⟨41780174, by rfl⟩ : syracuseStep 55706899 = 83560349) B83560349
theorem B74275865 : Blo 1905435 74275865 := bstep (se 2 (by rfl) ⟨27853449, by rfl⟩ : syracuseStep 74275865 = 55706899) B55706899
theorem B49517243 : Blo 1905435 49517243 := bstep (se 1 (by rfl) ⟨37137932, by rfl⟩ : syracuseStep 49517243 = 74275865) B74275865
theorem B33011495 : Blo 1905435 33011495 := bstep (se 1 (by rfl) ⟨24758621, by rfl⟩ : syracuseStep 33011495 = 49517243) B49517243
theorem B22007663 : Blo 1905435 22007663 := bstep (se 1 (by rfl) ⟨16505747, by rfl⟩ : syracuseStep 22007663 = 33011495) B33011495
theorem B14671775 : Blo 1905435 14671775 := bstep (se 1 (by rfl) ⟨11003831, by rfl⟩ : syracuseStep 14671775 = 22007663) B22007663
theorem B9781183 : Blo 1905435 9781183 := bstep (se 1 (by rfl) ⟨7335887, by rfl⟩ : syracuseStep 9781183 = 14671775) B14671775
theorem B13041577 : Blo 1905435 13041577 := bstep (se 2 (by rfl) ⟨4890591, by rfl⟩ : syracuseStep 13041577 = 9781183) B9781183
theorem B17388769 : Blo 1905435 17388769 := bstep (se 2 (by rfl) ⟨6520788, by rfl⟩ : syracuseStep 17388769 = 13041577) B13041577
theorem B23185025 : Blo 1905435 23185025 := bstep (se 2 (by rfl) ⟨8694384, by rfl⟩ : syracuseStep 23185025 = 17388769) B17388769
theorem B15456683 : Blo 1905435 15456683 := bstep (se 1 (by rfl) ⟨11592512, by rfl⟩ : syracuseStep 15456683 = 23185025) B23185025
theorem B41217821 : Blo 1905435 41217821 := bstep (se 3 (by rfl) ⟨7728341, by rfl⟩ : syracuseStep 41217821 = 15456683) B15456683
theorem B27478547 : Blo 1905435 27478547 := bstep (se 1 (by rfl) ⟨20608910, by rfl⟩ : syracuseStep 27478547 = 41217821) B41217821
theorem B18319031 : Blo 1905435 18319031 := bstep (se 1 (by rfl) ⟨13739273, by rfl⟩ : syracuseStep 18319031 = 27478547) B27478547
theorem B12212687 : Blo 1905435 12212687 := bstep (se 1 (by rfl) ⟨9159515, by rfl⟩ : syracuseStep 12212687 = 18319031) B18319031
theorem B8141791 : Blo 1905435 8141791 := bstep (se 1 (by rfl) ⟨6106343, by rfl⟩ : syracuseStep 8141791 = 12212687) B12212687
theorem B10855721 : Blo 1905435 10855721 := bstep (se 2 (by rfl) ⟨4070895, by rfl⟩ : syracuseStep 10855721 = 8141791) B8141791
theorem B7237147 : Blo 1905435 7237147 := bstep (se 1 (by rfl) ⟨5427860, by rfl⟩ : syracuseStep 7237147 = 10855721) B10855721
theorem B9649529 : Blo 1905435 9649529 := bstep (se 2 (by rfl) ⟨3618573, by rfl⟩ : syracuseStep 9649529 = 7237147) B7237147
theorem B6433019 : Blo 1905435 6433019 := bstep (se 1 (by rfl) ⟨4824764, by rfl⟩ : syracuseStep 6433019 = 9649529) B9649529
theorem B4288679 : Blo 1905435 4288679 := bstep (se 1 (by rfl) ⟨3216509, by rfl⟩ : syracuseStep 4288679 = 6433019) B6433019
theorem B2859119 : Blo 1905435 2859119 := bstep (se 1 (by rfl) ⟨2144339, by rfl⟩ : syracuseStep 2859119 = 4288679) B4288679
theorem B1906079 : Blo 1905435 1906079 := bstep (se 1 (by rfl) ⟨1429559, by rfl⟩ : syracuseStep 1906079 = 2859119) B2859119
theorem B2859125 : Blo 1905435 2859125 := bbase (se 5 (by rfl) ⟨134021, by rfl⟩ : syracuseStep 2859125 = 268043) (by norm_num)
theorem B1906083 : Blo 1905435 1906083 := bstep (se 1 (by rfl) ⟨1429562, by rfl⟩ : syracuseStep 1906083 = 2859125) B2859125
theorem B3618589 : Blo 1905435 3618589 := bbase (se 3 (by rfl) ⟨678485, by rfl⟩ : syracuseStep 3618589 = 1356971) (by norm_num)
theorem B4824785 : Blo 1905435 4824785 := bstep (se 2 (by rfl) ⟨1809294, by rfl⟩ : syracuseStep 4824785 = 3618589) B3618589
theorem B3216523 : Blo 1905435 3216523 := bstep (se 1 (by rfl) ⟨2412392, by rfl⟩ : syracuseStep 3216523 = 4824785) B4824785
theorem B4288697 : Blo 1905435 4288697 := bstep (se 2 (by rfl) ⟨1608261, by rfl⟩ : syracuseStep 4288697 = 3216523) B3216523
theorem B2859131 : Blo 1905435 2859131 := bstep (se 1 (by rfl) ⟨2144348, by rfl⟩ : syracuseStep 2859131 = 4288697) B4288697
theorem B1906087 : Blo 1905435 1906087 := bstep (se 1 (by rfl) ⟨1429565, by rfl⟩ : syracuseStep 1906087 = 2859131) B2859131
theorem B2144353 : Blo 1905435 2144353 := bbase (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) (by norm_num)
theorem B2859137 : Blo 1905435 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B1906091 : Blo 1905435 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B4824805 : Blo 1905435 4824805 := bbase (se 4 (by rfl) ⟨452325, by rfl⟩ : syracuseStep 4824805 = 904651) (by norm_num)
theorem B6433073 : Blo 1905435 6433073 := bstep (se 2 (by rfl) ⟨2412402, by rfl⟩ : syracuseStep 6433073 = 4824805) B4824805
theorem B4288715 : Blo 1905435 4288715 := bstep (se 1 (by rfl) ⟨3216536, by rfl⟩ : syracuseStep 4288715 = 6433073) B6433073
theorem B2859143 : Blo 1905435 2859143 := bstep (se 1 (by rfl) ⟨2144357, by rfl⟩ : syracuseStep 2859143 = 4288715) B4288715
theorem B1906095 : Blo 1905435 1906095 := bstep (se 1 (by rfl) ⟨1429571, by rfl⟩ : syracuseStep 1906095 = 2859143) B2859143
theorem B2859149 : Blo 1905435 2859149 := bbase (se 3 (by rfl) ⟨536090, by rfl⟩ : syracuseStep 2859149 = 1072181) (by norm_num)
theorem B1906099 : Blo 1905435 1906099 := bstep (se 1 (by rfl) ⟨1429574, by rfl⟩ : syracuseStep 1906099 = 2859149) B2859149
theorem B4288733 : Blo 1905435 4288733 := bbase (se 3 (by rfl) ⟨804137, by rfl⟩ : syracuseStep 4288733 = 1608275) (by norm_num)
theorem B2859155 : Blo 1905435 2859155 := bstep (se 1 (by rfl) ⟨2144366, by rfl⟩ : syracuseStep 2859155 = 4288733) B4288733
theorem B1906103 : Blo 1905435 1906103 := bstep (se 1 (by rfl) ⟨1429577, by rfl⟩ : syracuseStep 1906103 = 2859155) B2859155
theorem B3216557 : Blo 1905435 3216557 := bbase (se 3 (by rfl) ⟨603104, by rfl⟩ : syracuseStep 3216557 = 1206209) (by norm_num)
theorem B2144371 : Blo 1905435 2144371 := bstep (se 1 (by rfl) ⟨1608278, by rfl⟩ : syracuseStep 2144371 = 3216557) B3216557
theorem B2859161 : Blo 1905435 2859161 := bstep (se 2 (by rfl) ⟨1072185, by rfl⟩ : syracuseStep 2859161 = 2144371) B2144371
theorem B1906107 : Blo 1905435 1906107 := bstep (se 1 (by rfl) ⟨1429580, by rfl⟩ : syracuseStep 1906107 = 2859161) B2859161
theorem B15667829 : Blo 1905435 15667829 := bbase (se 5 (by rfl) ⟨734429, by rfl⟩ : syracuseStep 15667829 = 1468859) (by norm_num)
theorem B10445219 : Blo 1905435 10445219 := bstep (se 1 (by rfl) ⟨7833914, by rfl⟩ : syracuseStep 10445219 = 15667829) B15667829
theorem B6963479 : Blo 1905435 6963479 := bstep (se 1 (by rfl) ⟨5222609, by rfl⟩ : syracuseStep 6963479 = 10445219) B10445219
theorem B4642319 : Blo 1905435 4642319 := bstep (se 1 (by rfl) ⟨3481739, by rfl⟩ : syracuseStep 4642319 = 6963479) B6963479
theorem B12379517 : Blo 1905435 12379517 := bstep (se 3 (by rfl) ⟨2321159, by rfl⟩ : syracuseStep 12379517 = 4642319) B4642319
theorem B8253011 : Blo 1905435 8253011 := bstep (se 1 (by rfl) ⟨6189758, by rfl⟩ : syracuseStep 8253011 = 12379517) B12379517
theorem B22008029 : Blo 1905435 22008029 := bstep (se 3 (by rfl) ⟨4126505, by rfl⟩ : syracuseStep 22008029 = 8253011) B8253011
theorem B58688077 : Blo 1905435 58688077 := bstep (se 3 (by rfl) ⟨11004014, by rfl⟩ : syracuseStep 58688077 = 22008029) B22008029
theorem B78250769 : Blo 1905435 78250769 := bstep (se 2 (by rfl) ⟨29344038, by rfl⟩ : syracuseStep 78250769 = 58688077) B58688077
theorem B52167179 : Blo 1905435 52167179 := bstep (se 1 (by rfl) ⟨39125384, by rfl⟩ : syracuseStep 52167179 = 78250769) B78250769
theorem B34778119 : Blo 1905435 34778119 := bstep (se 1 (by rfl) ⟨26083589, by rfl⟩ : syracuseStep 34778119 = 52167179) B52167179
theorem B46370825 : Blo 1905435 46370825 := bstep (se 2 (by rfl) ⟨17389059, by rfl⟩ : syracuseStep 46370825 = 34778119) B34778119
theorem B30913883 : Blo 1905435 30913883 := bstep (se 1 (by rfl) ⟨23185412, by rfl⟩ : syracuseStep 30913883 = 46370825) B46370825
theorem B20609255 : Blo 1905435 20609255 := bstep (se 1 (by rfl) ⟨15456941, by rfl⟩ : syracuseStep 20609255 = 30913883) B30913883
theorem B54958013 : Blo 1905435 54958013 := bstep (se 3 (by rfl) ⟨10304627, by rfl⟩ : syracuseStep 54958013 = 20609255) B20609255
theorem B36638675 : Blo 1905435 36638675 := bstep (se 1 (by rfl) ⟨27479006, by rfl⟩ : syracuseStep 36638675 = 54958013) B54958013
theorem B24425783 : Blo 1905435 24425783 := bstep (se 1 (by rfl) ⟨18319337, by rfl⟩ : syracuseStep 24425783 = 36638675) B36638675
theorem B16283855 : Blo 1905435 16283855 := bstep (se 1 (by rfl) ⟨12212891, by rfl⟩ : syracuseStep 16283855 = 24425783) B24425783
theorem B10855903 : Blo 1905435 10855903 := bstep (se 1 (by rfl) ⟨8141927, by rfl⟩ : syracuseStep 10855903 = 16283855) B16283855
theorem B14474537 : Blo 1905435 14474537 := bstep (se 2 (by rfl) ⟨5427951, by rfl⟩ : syracuseStep 14474537 = 10855903) B10855903
theorem B9649691 : Blo 1905435 9649691 := bstep (se 1 (by rfl) ⟨7237268, by rfl⟩ : syracuseStep 9649691 = 14474537) B14474537
theorem B6433127 : Blo 1905435 6433127 := bstep (se 1 (by rfl) ⟨4824845, by rfl⟩ : syracuseStep 6433127 = 9649691) B9649691
theorem B4288751 : Blo 1905435 4288751 := bstep (se 1 (by rfl) ⟨3216563, by rfl⟩ : syracuseStep 4288751 = 6433127) B6433127
theorem B2859167 : Blo 1905435 2859167 := bstep (se 1 (by rfl) ⟨2144375, by rfl⟩ : syracuseStep 2859167 = 4288751) B4288751
theorem B1906111 : Blo 1905435 1906111 := bstep (se 1 (by rfl) ⟨1429583, by rfl⟩ : syracuseStep 1906111 = 2859167) B2859167
theorem B2859173 : Blo 1905435 2859173 := bbase (se 4 (by rfl) ⟨268047, by rfl⟩ : syracuseStep 2859173 = 536095) (by norm_num)
theorem B1906115 : Blo 1905435 1906115 := bstep (se 1 (by rfl) ⟨1429586, by rfl⟩ : syracuseStep 1906115 = 2859173) B2859173
theorem B2412433 : Blo 1905435 2412433 := bbase (se 2 (by rfl) ⟨904662, by rfl⟩ : syracuseStep 2412433 = 1809325) (by norm_num)
theorem B3216577 : Blo 1905435 3216577 := bstep (se 2 (by rfl) ⟨1206216, by rfl⟩ : syracuseStep 3216577 = 2412433) B2412433
theorem B4288769 : Blo 1905435 4288769 := bstep (se 2 (by rfl) ⟨1608288, by rfl⟩ : syracuseStep 4288769 = 3216577) B3216577
theorem B2859179 : Blo 1905435 2859179 := bstep (se 1 (by rfl) ⟨2144384, by rfl⟩ : syracuseStep 2859179 = 4288769) B4288769
theorem B1906119 : Blo 1905435 1906119 := bstep (se 1 (by rfl) ⟨1429589, by rfl⟩ : syracuseStep 1906119 = 2859179) B2859179
theorem B2144389 : Blo 1905435 2144389 := bbase (se 4 (by rfl) ⟨201036, by rfl⟩ : syracuseStep 2144389 = 402073) (by norm_num)
theorem B2859185 : Blo 1905435 2859185 := bstep (se 2 (by rfl) ⟨1072194, by rfl⟩ : syracuseStep 2859185 = 2144389) B2144389
theorem B1906123 : Blo 1905435 1906123 := bstep (se 1 (by rfl) ⟨1429592, by rfl⟩ : syracuseStep 1906123 = 2859185) B2859185
theorem B9159749 : Blo 1905435 9159749 := bbase (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) (by norm_num)
theorem B6106499 : Blo 1905435 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B4070999 : Blo 1905435 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B2713999 : Blo 1905435 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B3618665 : Blo 1905435 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B2412443 : Blo 1905435 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B6433181 : Blo 1905435 6433181 := bstep (se 3 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 6433181 = 2412443) B2412443
theorem B4288787 : Blo 1905435 4288787 := bstep (se 1 (by rfl) ⟨3216590, by rfl⟩ : syracuseStep 4288787 = 6433181) B6433181
theorem B2859191 : Blo 1905435 2859191 := bstep (se 1 (by rfl) ⟨2144393, by rfl⟩ : syracuseStep 2859191 = 4288787) B4288787
theorem B1906127 : Blo 1905435 1906127 := bstep (se 1 (by rfl) ⟨1429595, by rfl⟩ : syracuseStep 1906127 = 2859191) B2859191
theorem B2859197 : Blo 1905435 2859197 := bbase (se 3 (by rfl) ⟨536099, by rfl⟩ : syracuseStep 2859197 = 1072199) (by norm_num)
theorem B1906131 : Blo 1905435 1906131 := bstep (se 1 (by rfl) ⟨1429598, by rfl⟩ : syracuseStep 1906131 = 2859197) B2859197
theorem B4288805 : Blo 1905435 4288805 := bbase (se 4 (by rfl) ⟨402075, by rfl⟩ : syracuseStep 4288805 = 804151) (by norm_num)
theorem B2859203 : Blo 1905435 2859203 := bstep (se 1 (by rfl) ⟨2144402, by rfl⟩ : syracuseStep 2859203 = 4288805) B4288805
theorem B1906135 : Blo 1905435 1906135 := bstep (se 1 (by rfl) ⟨1429601, by rfl⟩ : syracuseStep 1906135 = 2859203) B2859203
theorem B4824917 : Blo 1905435 4824917 := bbase (se 9 (by rfl) ⟨14135, by rfl⟩ : syracuseStep 4824917 = 28271) (by norm_num)
theorem B3216611 : Blo 1905435 3216611 := bstep (se 1 (by rfl) ⟨2412458, by rfl⟩ : syracuseStep 3216611 = 4824917) B4824917
theorem B2144407 : Blo 1905435 2144407 := bstep (se 1 (by rfl) ⟨1608305, by rfl⟩ : syracuseStep 2144407 = 3216611) B3216611
theorem B2859209 : Blo 1905435 2859209 := bstep (se 2 (by rfl) ⟨1072203, by rfl⟩ : syracuseStep 2859209 = 2144407) B2144407
theorem B1906139 : Blo 1905435 1906139 := bstep (se 1 (by rfl) ⟨1429604, by rfl⟩ : syracuseStep 1906139 = 2859209) B2859209
theorem B6106549 : Blo 1905435 6106549 := bbase (se 5 (by rfl) ⟨286244, by rfl⟩ : syracuseStep 6106549 = 572489) (by norm_num)
theorem B8142065 : Blo 1905435 8142065 := bstep (se 2 (by rfl) ⟨3053274, by rfl⟩ : syracuseStep 8142065 = 6106549) B6106549
theorem B5428043 : Blo 1905435 5428043 := bstep (se 1 (by rfl) ⟨4071032, by rfl⟩ : syracuseStep 5428043 = 8142065) B8142065
theorem B3618695 : Blo 1905435 3618695 := bstep (se 1 (by rfl) ⟨2714021, by rfl⟩ : syracuseStep 3618695 = 5428043) B5428043
theorem B9649853 : Blo 1905435 9649853 := bstep (se 3 (by rfl) ⟨1809347, by rfl⟩ : syracuseStep 9649853 = 3618695) B3618695
theorem B6433235 : Blo 1905435 6433235 := bstep (se 1 (by rfl) ⟨4824926, by rfl⟩ : syracuseStep 6433235 = 9649853) B9649853
theorem B4288823 : Blo 1905435 4288823 := bstep (se 1 (by rfl) ⟨3216617, by rfl⟩ : syracuseStep 4288823 = 6433235) B6433235
theorem B2859215 : Blo 1905435 2859215 := bstep (se 1 (by rfl) ⟨2144411, by rfl⟩ : syracuseStep 2859215 = 4288823) B4288823
theorem B1906143 : Blo 1905435 1906143 := bstep (se 1 (by rfl) ⟨1429607, by rfl⟩ : syracuseStep 1906143 = 2859215) B2859215
theorem B2859221 : Blo 1905435 2859221 := bbase (se 7 (by rfl) ⟨33506, by rfl⟩ : syracuseStep 2859221 = 67013) (by norm_num)
theorem B1906147 : Blo 1905435 1906147 := bstep (se 1 (by rfl) ⟨1429610, by rfl⟩ : syracuseStep 1906147 = 2859221) B2859221
theorem B2035525 : Blo 1905435 2035525 := bbase (se 4 (by rfl) ⟨190830, by rfl⟩ : syracuseStep 2035525 = 381661) (by norm_num)
theorem B2714033 : Blo 1905435 2714033 := bstep (se 2 (by rfl) ⟨1017762, by rfl⟩ : syracuseStep 2714033 = 2035525) B2035525
theorem B7237421 : Blo 1905435 7237421 := bstep (se 3 (by rfl) ⟨1357016, by rfl⟩ : syracuseStep 7237421 = 2714033) B2714033
theorem B4824947 : Blo 1905435 4824947 := bstep (se 1 (by rfl) ⟨3618710, by rfl⟩ : syracuseStep 4824947 = 7237421) B7237421
theorem B3216631 : Blo 1905435 3216631 := bstep (se 1 (by rfl) ⟨2412473, by rfl⟩ : syracuseStep 3216631 = 4824947) B4824947
theorem B4288841 : Blo 1905435 4288841 := bstep (se 2 (by rfl) ⟨1608315, by rfl⟩ : syracuseStep 4288841 = 3216631) B3216631
theorem B2859227 : Blo 1905435 2859227 := bstep (se 1 (by rfl) ⟨2144420, by rfl⟩ : syracuseStep 2859227 = 4288841) B4288841
theorem B1906151 : Blo 1905435 1906151 := bstep (se 1 (by rfl) ⟨1429613, by rfl⟩ : syracuseStep 1906151 = 2859227) B2859227
theorem B2144425 : Blo 1905435 2144425 := bbase (se 2 (by rfl) ⟨804159, by rfl⟩ : syracuseStep 2144425 = 1608319) (by norm_num)
theorem B2859233 : Blo 1905435 2859233 := bstep (se 2 (by rfl) ⟨1072212, by rfl⟩ : syracuseStep 2859233 = 2144425) B2144425
theorem B1906155 : Blo 1905435 1906155 := bstep (se 1 (by rfl) ⟨1429616, by rfl⟩ : syracuseStep 1906155 = 2859233) B2859233
theorem B8142133 : Blo 1905435 8142133 := bbase (se 5 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 8142133 = 763325) (by norm_num)
theorem B10856177 : Blo 1905435 10856177 := bstep (se 2 (by rfl) ⟨4071066, by rfl⟩ : syracuseStep 10856177 = 8142133) B8142133
theorem B7237451 : Blo 1905435 7237451 := bstep (se 1 (by rfl) ⟨5428088, by rfl⟩ : syracuseStep 7237451 = 10856177) B10856177
theorem B4824967 : Blo 1905435 4824967 := bstep (se 1 (by rfl) ⟨3618725, by rfl⟩ : syracuseStep 4824967 = 7237451) B7237451
theorem B6433289 : Blo 1905435 6433289 := bstep (se 2 (by rfl) ⟨2412483, by rfl⟩ : syracuseStep 6433289 = 4824967) B4824967
theorem B4288859 : Blo 1905435 4288859 := bstep (se 1 (by rfl) ⟨3216644, by rfl⟩ : syracuseStep 4288859 = 6433289) B6433289
theorem B2859239 : Blo 1905435 2859239 := bstep (se 1 (by rfl) ⟨2144429, by rfl⟩ : syracuseStep 2859239 = 4288859) B4288859
theorem B1906159 : Blo 1905435 1906159 := bstep (se 1 (by rfl) ⟨1429619, by rfl⟩ : syracuseStep 1906159 = 2859239) B2859239
theorem B2859245 : Blo 1905435 2859245 := bbase (se 3 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 2859245 = 1072217) (by norm_num)
theorem B1906163 : Blo 1905435 1906163 := bstep (se 1 (by rfl) ⟨1429622, by rfl⟩ : syracuseStep 1906163 = 2859245) B2859245
theorem B4288877 : Blo 1905435 4288877 := bbase (se 3 (by rfl) ⟨804164, by rfl⟩ : syracuseStep 4288877 = 1608329) (by norm_num)
theorem B2859251 : Blo 1905435 2859251 := bstep (se 1 (by rfl) ⟨2144438, by rfl⟩ : syracuseStep 2859251 = 4288877) B4288877
theorem B1906167 : Blo 1905435 1906167 := bstep (se 1 (by rfl) ⟨1429625, by rfl⟩ : syracuseStep 1906167 = 2859251) B2859251
theorem B3618749 : Blo 1905435 3618749 := bbase (se 3 (by rfl) ⟨678515, by rfl⟩ : syracuseStep 3618749 = 1357031) (by norm_num)
theorem B2412499 : Blo 1905435 2412499 := bstep (se 1 (by rfl) ⟨1809374, by rfl⟩ : syracuseStep 2412499 = 3618749) B3618749
theorem B3216665 : Blo 1905435 3216665 := bstep (se 2 (by rfl) ⟨1206249, by rfl⟩ : syracuseStep 3216665 = 2412499) B2412499
theorem B2144443 : Blo 1905435 2144443 := bstep (se 1 (by rfl) ⟨1608332, by rfl⟩ : syracuseStep 2144443 = 3216665) B3216665
theorem B2859257 : Blo 1905435 2859257 := bstep (se 2 (by rfl) ⟨1072221, by rfl⟩ : syracuseStep 2859257 = 2144443) B2144443
theorem B1906171 : Blo 1905435 1906171 := bstep (se 1 (by rfl) ⟨1429628, by rfl⟩ : syracuseStep 1906171 = 2859257) B2859257
theorem B48853205 : Blo 1905435 48853205 := bbase (se 7 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 48853205 = 1144997) (by norm_num)
theorem B32568803 : Blo 1905435 32568803 := bstep (se 1 (by rfl) ⟨24426602, by rfl⟩ : syracuseStep 32568803 = 48853205) B48853205
theorem B21712535 : Blo 1905435 21712535 := bstep (se 1 (by rfl) ⟨16284401, by rfl⟩ : syracuseStep 21712535 = 32568803) B32568803
theorem B14475023 : Blo 1905435 14475023 := bstep (se 1 (by rfl) ⟨10856267, by rfl⟩ : syracuseStep 14475023 = 21712535) B21712535
theorem B9650015 : Blo 1905435 9650015 := bstep (se 1 (by rfl) ⟨7237511, by rfl⟩ : syracuseStep 9650015 = 14475023) B14475023
theorem B6433343 : Blo 1905435 6433343 := bstep (se 1 (by rfl) ⟨4825007, by rfl⟩ : syracuseStep 6433343 = 9650015) B9650015
theorem B4288895 : Blo 1905435 4288895 := bstep (se 1 (by rfl) ⟨3216671, by rfl⟩ : syracuseStep 4288895 = 6433343) B6433343
theorem B2859263 : Blo 1905435 2859263 := bstep (se 1 (by rfl) ⟨2144447, by rfl⟩ : syracuseStep 2859263 = 4288895) B4288895
theorem B1906175 : Blo 1905435 1906175 := bstep (se 1 (by rfl) ⟨1429631, by rfl⟩ : syracuseStep 1906175 = 2859263) B2859263
theorem B2859269 : Blo 1905435 2859269 := bbase (se 4 (by rfl) ⟨268056, by rfl⟩ : syracuseStep 2859269 = 536113) (by norm_num)
theorem B1906179 : Blo 1905435 1906179 := bstep (se 1 (by rfl) ⟨1429634, by rfl⟩ : syracuseStep 1906179 = 2859269) B2859269
theorem B3216685 : Blo 1905435 3216685 := bbase (se 3 (by rfl) ⟨603128, by rfl⟩ : syracuseStep 3216685 = 1206257) (by norm_num)
theorem B4288913 : Blo 1905435 4288913 := bstep (se 2 (by rfl) ⟨1608342, by rfl⟩ : syracuseStep 4288913 = 3216685) B3216685
theorem B2859275 : Blo 1905435 2859275 := bstep (se 1 (by rfl) ⟨2144456, by rfl⟩ : syracuseStep 2859275 = 4288913) B4288913
theorem B1906183 : Blo 1905435 1906183 := bstep (se 1 (by rfl) ⟨1429637, by rfl⟩ : syracuseStep 1906183 = 2859275) B2859275
theorem B2144461 : Blo 1905435 2144461 := bbase (se 3 (by rfl) ⟨402086, by rfl⟩ : syracuseStep 2144461 = 804173) (by norm_num)
theorem B2859281 : Blo 1905435 2859281 := bstep (se 2 (by rfl) ⟨1072230, by rfl⟩ : syracuseStep 2859281 = 2144461) B2144461
theorem B1906187 : Blo 1905435 1906187 := bstep (se 1 (by rfl) ⟨1429640, by rfl⟩ : syracuseStep 1906187 = 2859281) B2859281
theorem B6433397 : Blo 1905435 6433397 := bbase (se 5 (by rfl) ⟨301565, by rfl⟩ : syracuseStep 6433397 = 603131) (by norm_num)
theorem B4288931 : Blo 1905435 4288931 := bstep (se 1 (by rfl) ⟨3216698, by rfl⟩ : syracuseStep 4288931 = 6433397) B6433397
theorem B2859287 : Blo 1905435 2859287 := bstep (se 1 (by rfl) ⟨2144465, by rfl⟩ : syracuseStep 2859287 = 4288931) B4288931
theorem B1906191 : Blo 1905435 1906191 := bstep (se 1 (by rfl) ⟨1429643, by rfl⟩ : syracuseStep 1906191 = 2859287) B2859287
theorem B2859293 : Blo 1905435 2859293 := bbase (se 3 (by rfl) ⟨536117, by rfl⟩ : syracuseStep 2859293 = 1072235) (by norm_num)
theorem B1906195 : Blo 1905435 1906195 := bstep (se 1 (by rfl) ⟨1429646, by rfl⟩ : syracuseStep 1906195 = 2859293) B2859293
theorem B4288949 : Blo 1905435 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B2859299 : Blo 1905435 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B1906199 : Blo 1905435 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B5152565 : Blo 1905435 5152565 := bbase (se 5 (by rfl) ⟨241526, by rfl⟩ : syracuseStep 5152565 = 483053) (by norm_num)
theorem B3435043 : Blo 1905435 3435043 := bstep (se 1 (by rfl) ⟨2576282, by rfl⟩ : syracuseStep 3435043 = 5152565) B5152565
theorem B4580057 : Blo 1905435 4580057 := bstep (se 2 (by rfl) ⟨1717521, by rfl⟩ : syracuseStep 4580057 = 3435043) B3435043
theorem B3053371 : Blo 1905435 3053371 := bstep (se 1 (by rfl) ⟨2290028, by rfl⟩ : syracuseStep 3053371 = 4580057) B4580057
theorem B4071161 : Blo 1905435 4071161 := bstep (se 2 (by rfl) ⟨1526685, by rfl⟩ : syracuseStep 4071161 = 3053371) B3053371
theorem B10856429 : Blo 1905435 10856429 := bstep (se 3 (by rfl) ⟨2035580, by rfl⟩ : syracuseStep 10856429 = 4071161) B4071161
theorem B7237619 : Blo 1905435 7237619 := bstep (se 1 (by rfl) ⟨5428214, by rfl⟩ : syracuseStep 7237619 = 10856429) B10856429
theorem B4825079 : Blo 1905435 4825079 := bstep (se 1 (by rfl) ⟨3618809, by rfl⟩ : syracuseStep 4825079 = 7237619) B7237619
theorem B3216719 : Blo 1905435 3216719 := bstep (se 1 (by rfl) ⟨2412539, by rfl⟩ : syracuseStep 3216719 = 4825079) B4825079
theorem B2144479 : Blo 1905435 2144479 := bstep (se 1 (by rfl) ⟨1608359, by rfl⟩ : syracuseStep 2144479 = 3216719) B3216719
theorem B2859305 : Blo 1905435 2859305 := bstep (se 2 (by rfl) ⟨1072239, by rfl⟩ : syracuseStep 2859305 = 2144479) B2144479
theorem B1906203 : Blo 1905435 1906203 := bstep (se 1 (by rfl) ⟨1429652, by rfl⟩ : syracuseStep 1906203 = 2859305) B2859305
theorem B2290033 : Blo 1905435 2290033 := bbase (se 2 (by rfl) ⟨858762, by rfl⟩ : syracuseStep 2290033 = 1717525) (by norm_num)
theorem B3053377 : Blo 1905435 3053377 := bstep (se 2 (by rfl) ⟨1145016, by rfl⟩ : syracuseStep 3053377 = 2290033) B2290033
theorem B4071169 : Blo 1905435 4071169 := bstep (se 2 (by rfl) ⟨1526688, by rfl⟩ : syracuseStep 4071169 = 3053377) B3053377
theorem B5428225 : Blo 1905435 5428225 := bstep (se 2 (by rfl) ⟨2035584, by rfl⟩ : syracuseStep 5428225 = 4071169) B4071169
theorem B7237633 : Blo 1905435 7237633 := bstep (se 2 (by rfl) ⟨2714112, by rfl⟩ : syracuseStep 7237633 = 5428225) B5428225
theorem B9650177 : Blo 1905435 9650177 := bstep (se 2 (by rfl) ⟨3618816, by rfl⟩ : syracuseStep 9650177 = 7237633) B7237633
theorem B6433451 : Blo 1905435 6433451 := bstep (se 1 (by rfl) ⟨4825088, by rfl⟩ : syracuseStep 6433451 = 9650177) B9650177
theorem B4288967 : Blo 1905435 4288967 := bstep (se 1 (by rfl) ⟨3216725, by rfl⟩ : syracuseStep 4288967 = 6433451) B6433451
theorem B2859311 : Blo 1905435 2859311 := bstep (se 1 (by rfl) ⟨2144483, by rfl⟩ : syracuseStep 2859311 = 4288967) B4288967
theorem B1906207 : Blo 1905435 1906207 := bstep (se 1 (by rfl) ⟨1429655, by rfl⟩ : syracuseStep 1906207 = 2859311) B2859311
theorem B2859317 : Blo 1905435 2859317 := bbase (se 5 (by rfl) ⟨134030, by rfl⟩ : syracuseStep 2859317 = 268061) (by norm_num)
theorem B1906211 : Blo 1905435 1906211 := bstep (se 1 (by rfl) ⟨1429658, by rfl⟩ : syracuseStep 1906211 = 2859317) B2859317
theorem B4825109 : Blo 1905435 4825109 := bbase (se 6 (by rfl) ⟨113088, by rfl⟩ : syracuseStep 4825109 = 226177) (by norm_num)
theorem B3216739 : Blo 1905435 3216739 := bstep (se 1 (by rfl) ⟨2412554, by rfl⟩ : syracuseStep 3216739 = 4825109) B4825109
theorem B4288985 : Blo 1905435 4288985 := bstep (se 2 (by rfl) ⟨1608369, by rfl⟩ : syracuseStep 4288985 = 3216739) B3216739
theorem B2859323 : Blo 1905435 2859323 := bstep (se 1 (by rfl) ⟨2144492, by rfl⟩ : syracuseStep 2859323 = 4288985) B4288985
theorem B1906215 : Blo 1905435 1906215 := bstep (se 1 (by rfl) ⟨1429661, by rfl⟩ : syracuseStep 1906215 = 2859323) B2859323
theorem B2144497 : Blo 1905435 2144497 := bbase (se 2 (by rfl) ⟨804186, by rfl⟩ : syracuseStep 2144497 = 1608373) (by norm_num)
theorem B2859329 : Blo 1905435 2859329 := bstep (se 2 (by rfl) ⟨1072248, by rfl⟩ : syracuseStep 2859329 = 2144497) B2144497
theorem B1906219 : Blo 1905435 1906219 := bstep (se 1 (by rfl) ⟨1429664, by rfl⟩ : syracuseStep 1906219 = 2859329) B2859329
theorem B2445481 : Blo 1905435 2445481 := bbase (se 2 (by rfl) ⟨917055, by rfl⟩ : syracuseStep 2445481 = 1834111) (by norm_num)
theorem B13042565 : Blo 1905435 13042565 := bstep (se 4 (by rfl) ⟨1222740, by rfl⟩ : syracuseStep 13042565 = 2445481) B2445481
theorem B8695043 : Blo 1905435 8695043 := bstep (se 1 (by rfl) ⟨6521282, by rfl⟩ : syracuseStep 8695043 = 13042565) B13042565
theorem B5796695 : Blo 1905435 5796695 := bstep (se 1 (by rfl) ⟨4347521, by rfl⟩ : syracuseStep 5796695 = 8695043) B8695043
theorem B15457853 : Blo 1905435 15457853 := bstep (se 3 (by rfl) ⟨2898347, by rfl⟩ : syracuseStep 15457853 = 5796695) B5796695
theorem B10305235 : Blo 1905435 10305235 := bstep (se 1 (by rfl) ⟨7728926, by rfl⟩ : syracuseStep 10305235 = 15457853) B15457853
theorem B13740313 : Blo 1905435 13740313 := bstep (se 2 (by rfl) ⟨5152617, by rfl⟩ : syracuseStep 13740313 = 10305235) B10305235
theorem B18320417 : Blo 1905435 18320417 := bstep (se 2 (by rfl) ⟨6870156, by rfl⟩ : syracuseStep 18320417 = 13740313) B13740313
theorem B12213611 : Blo 1905435 12213611 := bstep (se 1 (by rfl) ⟨9160208, by rfl⟩ : syracuseStep 12213611 = 18320417) B18320417
theorem B8142407 : Blo 1905435 8142407 := bstep (se 1 (by rfl) ⟨6106805, by rfl⟩ : syracuseStep 8142407 = 12213611) B12213611
theorem B5428271 : Blo 1905435 5428271 := bstep (se 1 (by rfl) ⟨4071203, by rfl⟩ : syracuseStep 5428271 = 8142407) B8142407
theorem B3618847 : Blo 1905435 3618847 := bstep (se 1 (by rfl) ⟨2714135, by rfl⟩ : syracuseStep 3618847 = 5428271) B5428271
theorem B4825129 : Blo 1905435 4825129 := bstep (se 2 (by rfl) ⟨1809423, by rfl⟩ : syracuseStep 4825129 = 3618847) B3618847
theorem B6433505 : Blo 1905435 6433505 := bstep (se 2 (by rfl) ⟨2412564, by rfl⟩ : syracuseStep 6433505 = 4825129) B4825129
theorem B4289003 : Blo 1905435 4289003 := bstep (se 1 (by rfl) ⟨3216752, by rfl⟩ : syracuseStep 4289003 = 6433505) B6433505
theorem B2859335 : Blo 1905435 2859335 := bstep (se 1 (by rfl) ⟨2144501, by rfl⟩ : syracuseStep 2859335 = 4289003) B4289003
theorem B1906223 : Blo 1905435 1906223 := bstep (se 1 (by rfl) ⟨1429667, by rfl⟩ : syracuseStep 1906223 = 2859335) B2859335
theorem B2859341 : Blo 1905435 2859341 := bbase (se 3 (by rfl) ⟨536126, by rfl⟩ : syracuseStep 2859341 = 1072253) (by norm_num)
theorem B1906227 : Blo 1905435 1906227 := bstep (se 1 (by rfl) ⟨1429670, by rfl⟩ : syracuseStep 1906227 = 2859341) B2859341
theorem B4289021 : Blo 1905435 4289021 := bbase (se 3 (by rfl) ⟨804191, by rfl⟩ : syracuseStep 4289021 = 1608383) (by norm_num)
theorem B2859347 : Blo 1905435 2859347 := bstep (se 1 (by rfl) ⟨2144510, by rfl⟩ : syracuseStep 2859347 = 4289021) B4289021
theorem B1906231 : Blo 1905435 1906231 := bstep (se 1 (by rfl) ⟨1429673, by rfl⟩ : syracuseStep 1906231 = 2859347) B2859347
theorem B3216773 : Blo 1905435 3216773 := bbase (se 4 (by rfl) ⟨301572, by rfl⟩ : syracuseStep 3216773 = 603145) (by norm_num)
theorem B2144515 : Blo 1905435 2144515 := bstep (se 1 (by rfl) ⟨1608386, by rfl⟩ : syracuseStep 2144515 = 3216773) B3216773
theorem B2859353 : Blo 1905435 2859353 := bstep (se 2 (by rfl) ⟨1072257, by rfl⟩ : syracuseStep 2859353 = 2144515) B2144515
theorem B1906235 : Blo 1905435 1906235 := bstep (se 1 (by rfl) ⟨1429676, by rfl⟩ : syracuseStep 1906235 = 2859353) B2859353
theorem B14475509 : Blo 1905435 14475509 := bbase (se 5 (by rfl) ⟨678539, by rfl⟩ : syracuseStep 14475509 = 1357079) (by norm_num)
theorem B9650339 : Blo 1905435 9650339 := bstep (se 1 (by rfl) ⟨7237754, by rfl⟩ : syracuseStep 9650339 = 14475509) B14475509
theorem B6433559 : Blo 1905435 6433559 := bstep (se 1 (by rfl) ⟨4825169, by rfl⟩ : syracuseStep 6433559 = 9650339) B9650339
theorem B4289039 : Blo 1905435 4289039 := bstep (se 1 (by rfl) ⟨3216779, by rfl⟩ : syracuseStep 4289039 = 6433559) B6433559
theorem B2859359 : Blo 1905435 2859359 := bstep (se 1 (by rfl) ⟨2144519, by rfl⟩ : syracuseStep 2859359 = 4289039) B4289039
theorem B1906239 : Blo 1905435 1906239 := bstep (se 1 (by rfl) ⟨1429679, by rfl⟩ : syracuseStep 1906239 = 2859359) B2859359
theorem B2859365 : Blo 1905435 2859365 := bbase (se 4 (by rfl) ⟨268065, by rfl⟩ : syracuseStep 2859365 = 536131) (by norm_num)
theorem B1906243 : Blo 1905435 1906243 := bstep (se 1 (by rfl) ⟨1429682, by rfl⟩ : syracuseStep 1906243 = 2859365) B2859365
theorem B3618893 : Blo 1905435 3618893 := bbase (se 3 (by rfl) ⟨678542, by rfl⟩ : syracuseStep 3618893 = 1357085) (by norm_num)
theorem B2412595 : Blo 1905435 2412595 := bstep (se 1 (by rfl) ⟨1809446, by rfl⟩ : syracuseStep 2412595 = 3618893) B3618893
theorem B3216793 : Blo 1905435 3216793 := bstep (se 2 (by rfl) ⟨1206297, by rfl⟩ : syracuseStep 3216793 = 2412595) B2412595
theorem B4289057 : Blo 1905435 4289057 := bstep (se 2 (by rfl) ⟨1608396, by rfl⟩ : syracuseStep 4289057 = 3216793) B3216793
theorem B2859371 : Blo 1905435 2859371 := bstep (se 1 (by rfl) ⟨2144528, by rfl⟩ : syracuseStep 2859371 = 4289057) B4289057
theorem B1906247 : Blo 1905435 1906247 := bstep (se 1 (by rfl) ⟨1429685, by rfl⟩ : syracuseStep 1906247 = 2859371) B2859371
theorem B2144533 : Blo 1905435 2144533 := bbase (se 6 (by rfl) ⟨50262, by rfl⟩ : syracuseStep 2144533 = 100525) (by norm_num)
theorem B2859377 : Blo 1905435 2859377 := bstep (se 2 (by rfl) ⟨1072266, by rfl⟩ : syracuseStep 2859377 = 2144533) B2144533
theorem B1906251 : Blo 1905435 1906251 := bstep (se 1 (by rfl) ⟨1429688, by rfl⟩ : syracuseStep 1906251 = 2859377) B2859377
theorem B2412605 : Blo 1905435 2412605 := bbase (se 3 (by rfl) ⟨452363, by rfl⟩ : syracuseStep 2412605 = 904727) (by norm_num)
theorem B6433613 : Blo 1905435 6433613 := bstep (se 3 (by rfl) ⟨1206302, by rfl⟩ : syracuseStep 6433613 = 2412605) B2412605
theorem B4289075 : Blo 1905435 4289075 := bstep (se 1 (by rfl) ⟨3216806, by rfl⟩ : syracuseStep 4289075 = 6433613) B6433613
theorem B2859383 : Blo 1905435 2859383 := bstep (se 1 (by rfl) ⟨2144537, by rfl⟩ : syracuseStep 2859383 = 4289075) B4289075
theorem B1906255 : Blo 1905435 1906255 := bstep (se 1 (by rfl) ⟨1429691, by rfl⟩ : syracuseStep 1906255 = 2859383) B2859383
theorem B2859389 : Blo 1905435 2859389 := bbase (se 3 (by rfl) ⟨536135, by rfl⟩ : syracuseStep 2859389 = 1072271) (by norm_num)
theorem B1906259 : Blo 1905435 1906259 := bstep (se 1 (by rfl) ⟨1429694, by rfl⟩ : syracuseStep 1906259 = 2859389) B2859389
theorem B4289093 : Blo 1905435 4289093 := bbase (se 4 (by rfl) ⟨402102, by rfl⟩ : syracuseStep 4289093 = 804205) (by norm_num)
theorem B2859395 : Blo 1905435 2859395 := bstep (se 1 (by rfl) ⟨2144546, by rfl⟩ : syracuseStep 2859395 = 4289093) B4289093
theorem B1906263 : Blo 1905435 1906263 := bstep (se 1 (by rfl) ⟨1429697, by rfl⟩ : syracuseStep 1906263 = 2859395) B2859395
theorem B2035649 : Blo 1905435 2035649 := bbase (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) (by norm_num)
theorem B5428397 : Blo 1905435 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B3618931 : Blo 1905435 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B4825241 : Blo 1905435 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B3216827 : Blo 1905435 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B2144551 : Blo 1905435 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B2859401 : Blo 1905435 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B1906267 : Blo 1905435 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B9650501 : Blo 1905435 9650501 := bbase (se 4 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 9650501 = 1809469) (by norm_num)
theorem B6433667 : Blo 1905435 6433667 := bstep (se 1 (by rfl) ⟨4825250, by rfl⟩ : syracuseStep 6433667 = 9650501) B9650501
theorem B4289111 : Blo 1905435 4289111 := bstep (se 1 (by rfl) ⟨3216833, by rfl⟩ : syracuseStep 4289111 = 6433667) B6433667
theorem B2859407 : Blo 1905435 2859407 := bstep (se 1 (by rfl) ⟨2144555, by rfl⟩ : syracuseStep 2859407 = 4289111) B4289111
theorem B1906271 : Blo 1905435 1906271 := bstep (se 1 (by rfl) ⟨1429703, by rfl⟩ : syracuseStep 1906271 = 2859407) B2859407
theorem B2859413 : Blo 1905435 2859413 := bbase (se 6 (by rfl) ⟨67017, by rfl⟩ : syracuseStep 2859413 = 134035) (by norm_num)
theorem B1906275 : Blo 1905435 1906275 := bstep (se 1 (by rfl) ⟨1429706, by rfl⟩ : syracuseStep 1906275 = 2859413) B2859413
theorem B2173825 : Blo 1905435 2173825 := bbase (se 2 (by rfl) ⟨815184, by rfl⟩ : syracuseStep 2173825 = 1630369) (by norm_num)
theorem B2898433 : Blo 1905435 2898433 := bstep (se 2 (by rfl) ⟨1086912, by rfl⟩ : syracuseStep 2898433 = 2173825) B2173825
theorem B15458309 : Blo 1905435 15458309 := bstep (se 4 (by rfl) ⟨1449216, by rfl⟩ : syracuseStep 15458309 = 2898433) B2898433
theorem B10305539 : Blo 1905435 10305539 := bstep (se 1 (by rfl) ⟨7729154, by rfl⟩ : syracuseStep 10305539 = 15458309) B15458309
theorem B6870359 : Blo 1905435 6870359 := bstep (se 1 (by rfl) ⟨5152769, by rfl⟩ : syracuseStep 6870359 = 10305539) B10305539
theorem B4580239 : Blo 1905435 4580239 := bstep (se 1 (by rfl) ⟨3435179, by rfl⟩ : syracuseStep 4580239 = 6870359) B6870359
theorem B6106985 : Blo 1905435 6106985 := bstep (se 2 (by rfl) ⟨2290119, by rfl⟩ : syracuseStep 6106985 = 4580239) B4580239
theorem B4071323 : Blo 1905435 4071323 := bstep (se 1 (by rfl) ⟨3053492, by rfl⟩ : syracuseStep 4071323 = 6106985) B6106985
theorem B10856861 : Blo 1905435 10856861 := bstep (se 3 (by rfl) ⟨2035661, by rfl⟩ : syracuseStep 10856861 = 4071323) B4071323
theorem B7237907 : Blo 1905435 7237907 := bstep (se 1 (by rfl) ⟨5428430, by rfl⟩ : syracuseStep 7237907 = 10856861) B10856861
theorem B4825271 : Blo 1905435 4825271 := bstep (se 1 (by rfl) ⟨3618953, by rfl⟩ : syracuseStep 4825271 = 7237907) B7237907
theorem B3216847 : Blo 1905435 3216847 := bstep (se 1 (by rfl) ⟨2412635, by rfl⟩ : syracuseStep 3216847 = 4825271) B4825271
theorem B4289129 : Blo 1905435 4289129 := bstep (se 2 (by rfl) ⟨1608423, by rfl⟩ : syracuseStep 4289129 = 3216847) B3216847
theorem B2859419 : Blo 1905435 2859419 := bstep (se 1 (by rfl) ⟨2144564, by rfl⟩ : syracuseStep 2859419 = 4289129) B4289129
theorem B1906279 : Blo 1905435 1906279 := bstep (se 1 (by rfl) ⟨1429709, by rfl⟩ : syracuseStep 1906279 = 2859419) B2859419
theorem B2144569 : Blo 1905435 2144569 := bbase (se 2 (by rfl) ⟨804213, by rfl⟩ : syracuseStep 2144569 = 1608427) (by norm_num)
theorem B2859425 : Blo 1905435 2859425 := bstep (se 2 (by rfl) ⟨1072284, by rfl⟩ : syracuseStep 2859425 = 2144569) B2144569
theorem B1906283 : Blo 1905435 1906283 := bstep (se 1 (by rfl) ⟨1429712, by rfl⟩ : syracuseStep 1906283 = 2859425) B2859425
theorem B5428453 : Blo 1905435 5428453 := bbase (se 4 (by rfl) ⟨508917, by rfl⟩ : syracuseStep 5428453 = 1017835) (by norm_num)
theorem B7237937 : Blo 1905435 7237937 := bstep (se 2 (by rfl) ⟨2714226, by rfl⟩ : syracuseStep 7237937 = 5428453) B5428453
theorem B4825291 : Blo 1905435 4825291 := bstep (se 1 (by rfl) ⟨3618968, by rfl⟩ : syracuseStep 4825291 = 7237937) B7237937
theorem B6433721 : Blo 1905435 6433721 := bstep (se 2 (by rfl) ⟨2412645, by rfl⟩ : syracuseStep 6433721 = 4825291) B4825291
theorem B4289147 : Blo 1905435 4289147 := bstep (se 1 (by rfl) ⟨3216860, by rfl⟩ : syracuseStep 4289147 = 6433721) B6433721
theorem B2859431 : Blo 1905435 2859431 := bstep (se 1 (by rfl) ⟨2144573, by rfl⟩ : syracuseStep 2859431 = 4289147) B4289147
theorem B1906287 : Blo 1905435 1906287 := bstep (se 1 (by rfl) ⟨1429715, by rfl⟩ : syracuseStep 1906287 = 2859431) B2859431
theorem B2859437 : Blo 1905435 2859437 := bbase (se 3 (by rfl) ⟨536144, by rfl⟩ : syracuseStep 2859437 = 1072289) (by norm_num)
theorem B1906291 : Blo 1905435 1906291 := bstep (se 1 (by rfl) ⟨1429718, by rfl⟩ : syracuseStep 1906291 = 2859437) B2859437
theorem B4289165 : Blo 1905435 4289165 := bbase (se 3 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 4289165 = 1608437) (by norm_num)
theorem B2859443 : Blo 1905435 2859443 := bstep (se 1 (by rfl) ⟨2144582, by rfl⟩ : syracuseStep 2859443 = 4289165) B4289165
theorem B1906295 : Blo 1905435 1906295 := bstep (se 1 (by rfl) ⟨1429721, by rfl⟩ : syracuseStep 1906295 = 2859443) B2859443
theorem B2412661 : Blo 1905435 2412661 := bbase (se 5 (by rfl) ⟨113093, by rfl⟩ : syracuseStep 2412661 = 226187) (by norm_num)
theorem B3216881 : Blo 1905435 3216881 := bstep (se 2 (by rfl) ⟨1206330, by rfl⟩ : syracuseStep 3216881 = 2412661) B2412661
theorem B2144587 : Blo 1905435 2144587 := bstep (se 1 (by rfl) ⟨1608440, by rfl⟩ : syracuseStep 2144587 = 3216881) B3216881
theorem B2859449 : Blo 1905435 2859449 := bstep (se 2 (by rfl) ⟨1072293, by rfl⟩ : syracuseStep 2859449 = 2144587) B2144587
theorem B1906299 : Blo 1905435 1906299 := bstep (se 1 (by rfl) ⟨1429724, by rfl⟩ : syracuseStep 1906299 = 2859449) B2859449
theorem B8253845 : Blo 1905435 8253845 := bbase (se 6 (by rfl) ⟨193449, by rfl⟩ : syracuseStep 8253845 = 386899) (by norm_num)
theorem B5502563 : Blo 1905435 5502563 := bstep (se 1 (by rfl) ⟨4126922, by rfl⟩ : syracuseStep 5502563 = 8253845) B8253845
theorem B3668375 : Blo 1905435 3668375 := bstep (se 1 (by rfl) ⟨2751281, by rfl⟩ : syracuseStep 3668375 = 5502563) B5502563
theorem B9782333 : Blo 1905435 9782333 := bstep (se 3 (by rfl) ⟨1834187, by rfl⟩ : syracuseStep 9782333 = 3668375) B3668375
theorem B6521555 : Blo 1905435 6521555 := bstep (se 1 (by rfl) ⟨4891166, by rfl⟩ : syracuseStep 6521555 = 9782333) B9782333
theorem B4347703 : Blo 1905435 4347703 := bstep (se 1 (by rfl) ⟨3260777, by rfl⟩ : syracuseStep 4347703 = 6521555) B6521555
theorem B5796937 : Blo 1905435 5796937 := bstep (se 2 (by rfl) ⟨2173851, by rfl⟩ : syracuseStep 5796937 = 4347703) B4347703
theorem B30916997 : Blo 1905435 30916997 := bstep (se 4 (by rfl) ⟨2898468, by rfl⟩ : syracuseStep 30916997 = 5796937) B5796937
theorem B20611331 : Blo 1905435 20611331 := bstep (se 1 (by rfl) ⟨15458498, by rfl⟩ : syracuseStep 20611331 = 30916997) B30916997
theorem B13740887 : Blo 1905435 13740887 := bstep (se 1 (by rfl) ⟨10305665, by rfl⟩ : syracuseStep 13740887 = 20611331) B20611331
theorem B36642365 : Blo 1905435 36642365 := bstep (se 3 (by rfl) ⟨6870443, by rfl⟩ : syracuseStep 36642365 = 13740887) B13740887
theorem B24428243 : Blo 1905435 24428243 := bstep (se 1 (by rfl) ⟨18321182, by rfl⟩ : syracuseStep 24428243 = 36642365) B36642365
theorem B16285495 : Blo 1905435 16285495 := bstep (se 1 (by rfl) ⟨12214121, by rfl⟩ : syracuseStep 16285495 = 24428243) B24428243
theorem B21713993 : Blo 1905435 21713993 := bstep (se 2 (by rfl) ⟨8142747, by rfl⟩ : syracuseStep 21713993 = 16285495) B16285495
theorem B14475995 : Blo 1905435 14475995 := bstep (se 1 (by rfl) ⟨10856996, by rfl⟩ : syracuseStep 14475995 = 21713993) B21713993
theorem B9650663 : Blo 1905435 9650663 := bstep (se 1 (by rfl) ⟨7237997, by rfl⟩ : syracuseStep 9650663 = 14475995) B14475995
theorem B6433775 : Blo 1905435 6433775 := bstep (se 1 (by rfl) ⟨4825331, by rfl⟩ : syracuseStep 6433775 = 9650663) B9650663
theorem B4289183 : Blo 1905435 4289183 := bstep (se 1 (by rfl) ⟨3216887, by rfl⟩ : syracuseStep 4289183 = 6433775) B6433775
theorem B2859455 : Blo 1905435 2859455 := bstep (se 1 (by rfl) ⟨2144591, by rfl⟩ : syracuseStep 2859455 = 4289183) B4289183
theorem B1906303 : Blo 1905435 1906303 := bstep (se 1 (by rfl) ⟨1429727, by rfl⟩ : syracuseStep 1906303 = 2859455) B2859455
theorem B2859461 : Blo 1905435 2859461 := bbase (se 4 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 2859461 = 536149) (by norm_num)
theorem B1906307 : Blo 1905435 1906307 := bstep (se 1 (by rfl) ⟨1429730, by rfl⟩ : syracuseStep 1906307 = 2859461) B2859461
theorem B3216901 : Blo 1905435 3216901 := bbase (se 4 (by rfl) ⟨301584, by rfl⟩ : syracuseStep 3216901 = 603169) (by norm_num)
theorem B4289201 : Blo 1905435 4289201 := bstep (se 2 (by rfl) ⟨1608450, by rfl⟩ : syracuseStep 4289201 = 3216901) B3216901
theorem B2859467 : Blo 1905435 2859467 := bstep (se 1 (by rfl) ⟨2144600, by rfl⟩ : syracuseStep 2859467 = 4289201) B4289201
theorem B1906311 : Blo 1905435 1906311 := bstep (se 1 (by rfl) ⟨1429733, by rfl⟩ : syracuseStep 1906311 = 2859467) B2859467
theorem B2144605 : Blo 1905435 2144605 := bbase (se 3 (by rfl) ⟨402113, by rfl⟩ : syracuseStep 2144605 = 804227) (by norm_num)
theorem B2859473 : Blo 1905435 2859473 := bstep (se 2 (by rfl) ⟨1072302, by rfl⟩ : syracuseStep 2859473 = 2144605) B2144605
theorem B1906315 : Blo 1905435 1906315 := bstep (se 1 (by rfl) ⟨1429736, by rfl⟩ : syracuseStep 1906315 = 2859473) B2859473
theorem B6433829 : Blo 1905435 6433829 := bbase (se 4 (by rfl) ⟨603171, by rfl⟩ : syracuseStep 6433829 = 1206343) (by norm_num)
theorem B4289219 : Blo 1905435 4289219 := bstep (se 1 (by rfl) ⟨3216914, by rfl⟩ : syracuseStep 4289219 = 6433829) B6433829
theorem B2859479 : Blo 1905435 2859479 := bstep (se 1 (by rfl) ⟨2144609, by rfl⟩ : syracuseStep 2859479 = 4289219) B4289219
theorem B1906319 : Blo 1905435 1906319 := bstep (se 1 (by rfl) ⟨1429739, by rfl⟩ : syracuseStep 1906319 = 2859479) B2859479
theorem B2859485 : Blo 1905435 2859485 := bbase (se 3 (by rfl) ⟨536153, by rfl⟩ : syracuseStep 2859485 = 1072307) (by norm_num)
theorem B1906323 : Blo 1905435 1906323 := bstep (se 1 (by rfl) ⟨1429742, by rfl⟩ : syracuseStep 1906323 = 2859485) B2859485
theorem B4289237 : Blo 1905435 4289237 := bbase (se 7 (by rfl) ⟨50264, by rfl⟩ : syracuseStep 4289237 = 100529) (by norm_num)
theorem B2859491 : Blo 1905435 2859491 := bstep (se 1 (by rfl) ⟨2144618, by rfl⟩ : syracuseStep 2859491 = 4289237) B4289237
theorem B1906327 : Blo 1905435 1906327 := bstep (se 1 (by rfl) ⟨1429745, by rfl⟩ : syracuseStep 1906327 = 2859491) B2859491
theorem B8142869 : Blo 1905435 8142869 := bbase (se 6 (by rfl) ⟨190848, by rfl⟩ : syracuseStep 8142869 = 381697) (by norm_num)
theorem B5428579 : Blo 1905435 5428579 := bstep (se 1 (by rfl) ⟨4071434, by rfl⟩ : syracuseStep 5428579 = 8142869) B8142869
theorem B7238105 : Blo 1905435 7238105 := bstep (se 2 (by rfl) ⟨2714289, by rfl⟩ : syracuseStep 7238105 = 5428579) B5428579
theorem B4825403 : Blo 1905435 4825403 := bstep (se 1 (by rfl) ⟨3619052, by rfl⟩ : syracuseStep 4825403 = 7238105) B7238105
theorem B3216935 : Blo 1905435 3216935 := bstep (se 1 (by rfl) ⟨2412701, by rfl⟩ : syracuseStep 3216935 = 4825403) B4825403
theorem B2144623 : Blo 1905435 2144623 := bstep (se 1 (by rfl) ⟨1608467, by rfl⟩ : syracuseStep 2144623 = 3216935) B3216935
theorem B2859497 : Blo 1905435 2859497 := bstep (se 2 (by rfl) ⟨1072311, by rfl⟩ : syracuseStep 2859497 = 2144623) B2144623
theorem B1906331 : Blo 1905435 1906331 := bstep (se 1 (by rfl) ⟨1429748, by rfl⟩ : syracuseStep 1906331 = 2859497) B2859497
theorem B13928597 : Blo 1905435 13928597 := bbase (se 6 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 13928597 = 652903) (by norm_num)
theorem B9285731 : Blo 1905435 9285731 := bstep (se 1 (by rfl) ⟨6964298, by rfl⟩ : syracuseStep 9285731 = 13928597) B13928597
theorem B6190487 : Blo 1905435 6190487 := bstep (se 1 (by rfl) ⟨4642865, by rfl⟩ : syracuseStep 6190487 = 9285731) B9285731
theorem B4126991 : Blo 1905435 4126991 := bstep (se 1 (by rfl) ⟨3095243, by rfl⟩ : syracuseStep 4126991 = 6190487) B6190487
theorem B11005309 : Blo 1905435 11005309 := bstep (se 3 (by rfl) ⟨2063495, by rfl⟩ : syracuseStep 11005309 = 4126991) B4126991
theorem B14673745 : Blo 1905435 14673745 := bstep (se 2 (by rfl) ⟨5502654, by rfl⟩ : syracuseStep 14673745 = 11005309) B11005309
theorem B19564993 : Blo 1905435 19564993 := bstep (se 2 (by rfl) ⟨7336872, by rfl⟩ : syracuseStep 19564993 = 14673745) B14673745
theorem B26086657 : Blo 1905435 26086657 := bstep (se 2 (by rfl) ⟨9782496, by rfl⟩ : syracuseStep 26086657 = 19564993) B19564993
theorem B34782209 : Blo 1905435 34782209 := bstep (se 2 (by rfl) ⟨13043328, by rfl⟩ : syracuseStep 34782209 = 26086657) B26086657
theorem B23188139 : Blo 1905435 23188139 := bstep (se 1 (by rfl) ⟨17391104, by rfl⟩ : syracuseStep 23188139 = 34782209) B34782209
theorem B15458759 : Blo 1905435 15458759 := bstep (se 1 (by rfl) ⟨11594069, by rfl⟩ : syracuseStep 15458759 = 23188139) B23188139
theorem B10305839 : Blo 1905435 10305839 := bstep (se 1 (by rfl) ⟨7729379, by rfl⟩ : syracuseStep 10305839 = 15458759) B15458759
theorem B27482237 : Blo 1905435 27482237 := bstep (se 3 (by rfl) ⟨5152919, by rfl⟩ : syracuseStep 27482237 = 10305839) B10305839
theorem B18321491 : Blo 1905435 18321491 := bstep (se 1 (by rfl) ⟨13741118, by rfl⟩ : syracuseStep 18321491 = 27482237) B27482237
theorem B12214327 : Blo 1905435 12214327 := bstep (se 1 (by rfl) ⟨9160745, by rfl⟩ : syracuseStep 12214327 = 18321491) B18321491
theorem B16285769 : Blo 1905435 16285769 := bstep (se 2 (by rfl) ⟨6107163, by rfl⟩ : syracuseStep 16285769 = 12214327) B12214327
theorem B10857179 : Blo 1905435 10857179 := bstep (se 1 (by rfl) ⟨8142884, by rfl⟩ : syracuseStep 10857179 = 16285769) B16285769
theorem B7238119 : Blo 1905435 7238119 := bstep (se 1 (by rfl) ⟨5428589, by rfl⟩ : syracuseStep 7238119 = 10857179) B10857179
theorem B9650825 : Blo 1905435 9650825 := bstep (se 2 (by rfl) ⟨3619059, by rfl⟩ : syracuseStep 9650825 = 7238119) B7238119
theorem B6433883 : Blo 1905435 6433883 := bstep (se 1 (by rfl) ⟨4825412, by rfl⟩ : syracuseStep 6433883 = 9650825) B9650825
theorem B4289255 : Blo 1905435 4289255 := bstep (se 1 (by rfl) ⟨3216941, by rfl⟩ : syracuseStep 4289255 = 6433883) B6433883
theorem B2859503 : Blo 1905435 2859503 := bstep (se 1 (by rfl) ⟨2144627, by rfl⟩ : syracuseStep 2859503 = 4289255) B4289255
theorem B1906335 : Blo 1905435 1906335 := bstep (se 1 (by rfl) ⟨1429751, by rfl⟩ : syracuseStep 1906335 = 2859503) B2859503
theorem B2859509 : Blo 1905435 2859509 := bbase (se 5 (by rfl) ⟨134039, by rfl⟩ : syracuseStep 2859509 = 268079) (by norm_num)
theorem B1906339 : Blo 1905435 1906339 := bstep (se 1 (by rfl) ⟨1429754, by rfl⟩ : syracuseStep 1906339 = 2859509) B2859509
theorem B5428613 : Blo 1905435 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B3619075 : Blo 1905435 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B4825433 : Blo 1905435 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B3216955 : Blo 1905435 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B4289273 : Blo 1905435 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B2859515 : Blo 1905435 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1906343 : Blo 1905435 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B2144641 : Blo 1905435 2144641 := bbase (se 2 (by rfl) ⟨804240, by rfl⟩ : syracuseStep 2144641 = 1608481) (by norm_num)
theorem B2859521 : Blo 1905435 2859521 := bstep (se 2 (by rfl) ⟨1072320, by rfl⟩ : syracuseStep 2859521 = 2144641) B2144641
theorem B1906347 : Blo 1905435 1906347 := bstep (se 1 (by rfl) ⟨1429760, by rfl⟩ : syracuseStep 1906347 = 2859521) B2859521
theorem B4825453 : Blo 1905435 4825453 := bbase (se 3 (by rfl) ⟨904772, by rfl⟩ : syracuseStep 4825453 = 1809545) (by norm_num)
theorem B6433937 : Blo 1905435 6433937 := bstep (se 2 (by rfl) ⟨2412726, by rfl⟩ : syracuseStep 6433937 = 4825453) B4825453
theorem B4289291 : Blo 1905435 4289291 := bstep (se 1 (by rfl) ⟨3216968, by rfl⟩ : syracuseStep 4289291 = 6433937) B6433937
theorem B2859527 : Blo 1905435 2859527 := bstep (se 1 (by rfl) ⟨2144645, by rfl⟩ : syracuseStep 2859527 = 4289291) B4289291
theorem B1906351 : Blo 1905435 1906351 := bstep (se 1 (by rfl) ⟨1429763, by rfl⟩ : syracuseStep 1906351 = 2859527) B2859527
theorem B2859533 : Blo 1905435 2859533 := bbase (se 3 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 2859533 = 1072325) (by norm_num)
theorem B1906355 : Blo 1905435 1906355 := bstep (se 1 (by rfl) ⟨1429766, by rfl⟩ : syracuseStep 1906355 = 2859533) B2859533
theorem B4289309 : Blo 1905435 4289309 := bbase (se 3 (by rfl) ⟨804245, by rfl⟩ : syracuseStep 4289309 = 1608491) (by norm_num)
theorem B2859539 : Blo 1905435 2859539 := bstep (se 1 (by rfl) ⟨2144654, by rfl⟩ : syracuseStep 2859539 = 4289309) B4289309
theorem B1906359 : Blo 1905435 1906359 := bstep (se 1 (by rfl) ⟨1429769, by rfl⟩ : syracuseStep 1906359 = 2859539) B2859539
theorem B3216989 : Blo 1905435 3216989 := bbase (se 3 (by rfl) ⟨603185, by rfl⟩ : syracuseStep 3216989 = 1206371) (by norm_num)
theorem B2144659 : Blo 1905435 2144659 := bstep (se 1 (by rfl) ⟨1608494, by rfl⟩ : syracuseStep 2144659 = 3216989) B3216989
theorem B2859545 : Blo 1905435 2859545 := bstep (se 2 (by rfl) ⟨1072329, by rfl⟩ : syracuseStep 2859545 = 2144659) B2144659
theorem B1906363 : Blo 1905435 1906363 := bstep (se 1 (by rfl) ⟨1429772, by rfl⟩ : syracuseStep 1906363 = 2859545) B2859545
theorem B2290225 : Blo 1905435 2290225 := bbase (se 2 (by rfl) ⟨858834, by rfl⟩ : syracuseStep 2290225 = 1717669) (by norm_num)
theorem B3053633 : Blo 1905435 3053633 := bstep (se 2 (by rfl) ⟨1145112, by rfl⟩ : syracuseStep 3053633 = 2290225) B2290225
theorem B8143021 : Blo 1905435 8143021 := bstep (se 3 (by rfl) ⟨1526816, by rfl⟩ : syracuseStep 8143021 = 3053633) B3053633
theorem B10857361 : Blo 1905435 10857361 := bstep (se 2 (by rfl) ⟨4071510, by rfl⟩ : syracuseStep 10857361 = 8143021) B8143021
theorem B14476481 : Blo 1905435 14476481 := bstep (se 2 (by rfl) ⟨5428680, by rfl⟩ : syracuseStep 14476481 = 10857361) B10857361
theorem B9650987 : Blo 1905435 9650987 := bstep (se 1 (by rfl) ⟨7238240, by rfl⟩ : syracuseStep 9650987 = 14476481) B14476481
theorem B6433991 : Blo 1905435 6433991 := bstep (se 1 (by rfl) ⟨4825493, by rfl⟩ : syracuseStep 6433991 = 9650987) B9650987
theorem B4289327 : Blo 1905435 4289327 := bstep (se 1 (by rfl) ⟨3216995, by rfl⟩ : syracuseStep 4289327 = 6433991) B6433991
theorem B2859551 : Blo 1905435 2859551 := bstep (se 1 (by rfl) ⟨2144663, by rfl⟩ : syracuseStep 2859551 = 4289327) B4289327
theorem B1906367 : Blo 1905435 1906367 := bstep (se 1 (by rfl) ⟨1429775, by rfl⟩ : syracuseStep 1906367 = 2859551) B2859551
theorem B2859557 : Blo 1905435 2859557 := bbase (se 4 (by rfl) ⟨268083, by rfl⟩ : syracuseStep 2859557 = 536167) (by norm_num)
theorem B1906371 : Blo 1905435 1906371 := bstep (se 1 (by rfl) ⟨1429778, by rfl⟩ : syracuseStep 1906371 = 2859557) B2859557
theorem B2412757 : Blo 1905435 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B3217009 : Blo 1905435 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B4289345 : Blo 1905435 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B2859563 : Blo 1905435 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B1906375 : Blo 1905435 1906375 := bstep (se 1 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 1906375 = 2859563) B2859563
theorem B2144677 : Blo 1905435 2144677 := bbase (se 4 (by rfl) ⟨201063, by rfl⟩ : syracuseStep 2144677 = 402127) (by norm_num)
theorem B2859569 : Blo 1905435 2859569 := bstep (se 2 (by rfl) ⟨1072338, by rfl⟩ : syracuseStep 2859569 = 2144677) B2144677
theorem B1906379 : Blo 1905435 1906379 := bstep (se 1 (by rfl) ⟨1429784, by rfl⟩ : syracuseStep 1906379 = 2859569) B2859569
theorem B24762581 : Blo 1905435 24762581 := bbase (se 7 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 24762581 = 580373) (by norm_num)
theorem B16508387 : Blo 1905435 16508387 := bstep (se 1 (by rfl) ⟨12381290, by rfl⟩ : syracuseStep 16508387 = 24762581) B24762581
theorem B44022365 : Blo 1905435 44022365 := bstep (se 3 (by rfl) ⟨8254193, by rfl⟩ : syracuseStep 44022365 = 16508387) B16508387
theorem B29348243 : Blo 1905435 29348243 := bstep (se 1 (by rfl) ⟨22011182, by rfl⟩ : syracuseStep 29348243 = 44022365) B44022365
theorem B19565495 : Blo 1905435 19565495 := bstep (se 1 (by rfl) ⟨14674121, by rfl⟩ : syracuseStep 19565495 = 29348243) B29348243
theorem B13043663 : Blo 1905435 13043663 := bstep (se 1 (by rfl) ⟨9782747, by rfl⟩ : syracuseStep 13043663 = 19565495) B19565495
theorem B8695775 : Blo 1905435 8695775 := bstep (se 1 (by rfl) ⟨6521831, by rfl⟩ : syracuseStep 8695775 = 13043663) B13043663
theorem B5797183 : Blo 1905435 5797183 := bstep (se 1 (by rfl) ⟨4347887, by rfl⟩ : syracuseStep 5797183 = 8695775) B8695775
theorem B7729577 : Blo 1905435 7729577 := bstep (se 2 (by rfl) ⟨2898591, by rfl⟩ : syracuseStep 7729577 = 5797183) B5797183
theorem B5153051 : Blo 1905435 5153051 := bstep (se 1 (by rfl) ⟨3864788, by rfl⟩ : syracuseStep 5153051 = 7729577) B7729577
theorem B3435367 : Blo 1905435 3435367 := bstep (se 1 (by rfl) ⟨2576525, by rfl⟩ : syracuseStep 3435367 = 5153051) B5153051
theorem B4580489 : Blo 1905435 4580489 := bstep (se 2 (by rfl) ⟨1717683, by rfl⟩ : syracuseStep 4580489 = 3435367) B3435367
theorem B12214637 : Blo 1905435 12214637 := bstep (se 3 (by rfl) ⟨2290244, by rfl⟩ : syracuseStep 12214637 = 4580489) B4580489
theorem B8143091 : Blo 1905435 8143091 := bstep (se 1 (by rfl) ⟨6107318, by rfl⟩ : syracuseStep 8143091 = 12214637) B12214637
theorem B5428727 : Blo 1905435 5428727 := bstep (se 1 (by rfl) ⟨4071545, by rfl⟩ : syracuseStep 5428727 = 8143091) B8143091
theorem B3619151 : Blo 1905435 3619151 := bstep (se 1 (by rfl) ⟨2714363, by rfl⟩ : syracuseStep 3619151 = 5428727) B5428727
theorem B2412767 : Blo 1905435 2412767 := bstep (se 1 (by rfl) ⟨1809575, by rfl⟩ : syracuseStep 2412767 = 3619151) B3619151
theorem B6434045 : Blo 1905435 6434045 := bstep (se 3 (by rfl) ⟨1206383, by rfl⟩ : syracuseStep 6434045 = 2412767) B2412767
theorem B4289363 : Blo 1905435 4289363 := bstep (se 1 (by rfl) ⟨3217022, by rfl⟩ : syracuseStep 4289363 = 6434045) B6434045
theorem B2859575 : Blo 1905435 2859575 := bstep (se 1 (by rfl) ⟨2144681, by rfl⟩ : syracuseStep 2859575 = 4289363) B4289363
theorem B1906383 : Blo 1905435 1906383 := bstep (se 1 (by rfl) ⟨1429787, by rfl⟩ : syracuseStep 1906383 = 2859575) B2859575
theorem B2859581 : Blo 1905435 2859581 := bbase (se 3 (by rfl) ⟨536171, by rfl⟩ : syracuseStep 2859581 = 1072343) (by norm_num)
theorem B1906387 : Blo 1905435 1906387 := bstep (se 1 (by rfl) ⟨1429790, by rfl⟩ : syracuseStep 1906387 = 2859581) B2859581
theorem B4289381 : Blo 1905435 4289381 := bbase (se 4 (by rfl) ⟨402129, by rfl⟩ : syracuseStep 4289381 = 804259) (by norm_num)
theorem B2859587 : Blo 1905435 2859587 := bstep (se 1 (by rfl) ⟨2144690, by rfl⟩ : syracuseStep 2859587 = 4289381) B4289381
theorem B1906391 : Blo 1905435 1906391 := bstep (se 1 (by rfl) ⟨1429793, by rfl⟩ : syracuseStep 1906391 = 2859587) B2859587
theorem B4825565 : Blo 1905435 4825565 := bbase (se 3 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 4825565 = 1809587) (by norm_num)
theorem B3217043 : Blo 1905435 3217043 := bstep (se 1 (by rfl) ⟨2412782, by rfl⟩ : syracuseStep 3217043 = 4825565) B4825565
theorem B2144695 : Blo 1905435 2144695 := bstep (se 1 (by rfl) ⟨1608521, by rfl⟩ : syracuseStep 2144695 = 3217043) B3217043
theorem B2859593 : Blo 1905435 2859593 := bstep (se 2 (by rfl) ⟨1072347, by rfl⟩ : syracuseStep 2859593 = 2144695) B2144695
theorem B1906395 : Blo 1905435 1906395 := bstep (se 1 (by rfl) ⟨1429796, by rfl⟩ : syracuseStep 1906395 = 2859593) B2859593
theorem B3619181 : Blo 1905435 3619181 := bbase (se 3 (by rfl) ⟨678596, by rfl⟩ : syracuseStep 3619181 = 1357193) (by norm_num)
theorem B9651149 : Blo 1905435 9651149 := bstep (se 3 (by rfl) ⟨1809590, by rfl⟩ : syracuseStep 9651149 = 3619181) B3619181
theorem B6434099 : Blo 1905435 6434099 := bstep (se 1 (by rfl) ⟨4825574, by rfl⟩ : syracuseStep 6434099 = 9651149) B9651149
theorem B4289399 : Blo 1905435 4289399 := bstep (se 1 (by rfl) ⟨3217049, by rfl⟩ : syracuseStep 4289399 = 6434099) B6434099
theorem B2859599 : Blo 1905435 2859599 := bstep (se 1 (by rfl) ⟨2144699, by rfl⟩ : syracuseStep 2859599 = 4289399) B4289399
theorem B1906399 : Blo 1905435 1906399 := bstep (se 1 (by rfl) ⟨1429799, by rfl⟩ : syracuseStep 1906399 = 2859599) B2859599
theorem B2859605 : Blo 1905435 2859605 := bbase (se 8 (by rfl) ⟨16755, by rfl⟩ : syracuseStep 2859605 = 33511) (by norm_num)
theorem B1906403 : Blo 1905435 1906403 := bstep (se 1 (by rfl) ⟨1429802, by rfl⟩ : syracuseStep 1906403 = 2859605) B2859605
theorem B9161093 : Blo 1905435 9161093 := bbase (se 4 (by rfl) ⟨858852, by rfl⟩ : syracuseStep 9161093 = 1717705) (by norm_num)
theorem B6107395 : Blo 1905435 6107395 := bstep (se 1 (by rfl) ⟨4580546, by rfl⟩ : syracuseStep 6107395 = 9161093) B9161093
theorem B8143193 : Blo 1905435 8143193 := bstep (se 2 (by rfl) ⟨3053697, by rfl⟩ : syracuseStep 8143193 = 6107395) B6107395
theorem B5428795 : Blo 1905435 5428795 := bstep (se 1 (by rfl) ⟨4071596, by rfl⟩ : syracuseStep 5428795 = 8143193) B8143193
theorem B7238393 : Blo 1905435 7238393 := bstep (se 2 (by rfl) ⟨2714397, by rfl⟩ : syracuseStep 7238393 = 5428795) B5428795
theorem B4825595 : Blo 1905435 4825595 := bstep (se 1 (by rfl) ⟨3619196, by rfl⟩ : syracuseStep 4825595 = 7238393) B7238393
theorem B3217063 : Blo 1905435 3217063 := bstep (se 1 (by rfl) ⟨2412797, by rfl⟩ : syracuseStep 3217063 = 4825595) B4825595
theorem B4289417 : Blo 1905435 4289417 := bstep (se 2 (by rfl) ⟨1608531, by rfl⟩ : syracuseStep 4289417 = 3217063) B3217063
theorem B2859611 : Blo 1905435 2859611 := bstep (se 1 (by rfl) ⟨2144708, by rfl⟩ : syracuseStep 2859611 = 4289417) B4289417
theorem B1906407 : Blo 1905435 1906407 := bstep (se 1 (by rfl) ⟨1429805, by rfl⟩ : syracuseStep 1906407 = 2859611) B2859611
theorem B2144713 : Blo 1905435 2144713 := bbase (se 2 (by rfl) ⟨804267, by rfl⟩ : syracuseStep 2144713 = 1608535) (by norm_num)
theorem B2859617 : Blo 1905435 2859617 := bstep (se 2 (by rfl) ⟨1072356, by rfl⟩ : syracuseStep 2859617 = 2144713) B2144713
theorem B1906411 : Blo 1905435 1906411 := bstep (se 1 (by rfl) ⟨1429808, by rfl⟩ : syracuseStep 1906411 = 2859617) B2859617
theorem B16286453 : Blo 1905435 16286453 := bbase (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) (by norm_num)
theorem B10857635 : Blo 1905435 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B7238423 : Blo 1905435 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B4825615 : Blo 1905435 4825615 := bstep (se 1 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 4825615 = 7238423) B7238423
theorem B6434153 : Blo 1905435 6434153 := bstep (se 2 (by rfl) ⟨2412807, by rfl⟩ : syracuseStep 6434153 = 4825615) B4825615
theorem B4289435 : Blo 1905435 4289435 := bstep (se 1 (by rfl) ⟨3217076, by rfl⟩ : syracuseStep 4289435 = 6434153) B6434153
theorem B2859623 : Blo 1905435 2859623 := bstep (se 1 (by rfl) ⟨2144717, by rfl⟩ : syracuseStep 2859623 = 4289435) B4289435
theorem B1906415 : Blo 1905435 1906415 := bstep (se 1 (by rfl) ⟨1429811, by rfl⟩ : syracuseStep 1906415 = 2859623) B2859623
theorem B2859629 : Blo 1905435 2859629 := bbase (se 3 (by rfl) ⟨536180, by rfl⟩ : syracuseStep 2859629 = 1072361) (by norm_num)
theorem B1906419 : Blo 1905435 1906419 := bstep (se 1 (by rfl) ⟨1429814, by rfl⟩ : syracuseStep 1906419 = 2859629) B2859629
theorem B4289453 : Blo 1905435 4289453 := bbase (se 3 (by rfl) ⟨804272, by rfl⟩ : syracuseStep 4289453 = 1608545) (by norm_num)
theorem B2859635 : Blo 1905435 2859635 := bstep (se 1 (by rfl) ⟨2144726, by rfl⟩ : syracuseStep 2859635 = 4289453) B4289453
theorem B1906423 : Blo 1905435 1906423 := bstep (se 1 (by rfl) ⟨1429817, by rfl⟩ : syracuseStep 1906423 = 2859635) B2859635
theorem B5428853 : Blo 1905435 5428853 := bbase (se 5 (by rfl) ⟨254477, by rfl⟩ : syracuseStep 5428853 = 508955) (by norm_num)
theorem B3619235 : Blo 1905435 3619235 := bstep (se 1 (by rfl) ⟨2714426, by rfl⟩ : syracuseStep 3619235 = 5428853) B5428853
theorem B2412823 : Blo 1905435 2412823 := bstep (se 1 (by rfl) ⟨1809617, by rfl⟩ : syracuseStep 2412823 = 3619235) B3619235
theorem B3217097 : Blo 1905435 3217097 := bstep (se 2 (by rfl) ⟨1206411, by rfl⟩ : syracuseStep 3217097 = 2412823) B2412823
theorem B2144731 : Blo 1905435 2144731 := bstep (se 1 (by rfl) ⟨1608548, by rfl⟩ : syracuseStep 2144731 = 3217097) B3217097
theorem B2859641 : Blo 1905435 2859641 := bstep (se 2 (by rfl) ⟨1072365, by rfl⟩ : syracuseStep 2859641 = 2144731) B2144731
theorem B1906427 : Blo 1905435 1906427 := bstep (se 1 (by rfl) ⟨1429820, by rfl⟩ : syracuseStep 1906427 = 2859641) B2859641
theorem B41225429 : Blo 1905435 41225429 := bbase (se 7 (by rfl) ⟨483110, by rfl⟩ : syracuseStep 41225429 = 966221) (by norm_num)
theorem B27483619 : Blo 1905435 27483619 := bstep (se 1 (by rfl) ⟨20612714, by rfl⟩ : syracuseStep 27483619 = 41225429) B41225429
theorem B36644825 : Blo 1905435 36644825 := bstep (se 2 (by rfl) ⟨13741809, by rfl⟩ : syracuseStep 36644825 = 27483619) B27483619
theorem B24429883 : Blo 1905435 24429883 := bstep (se 1 (by rfl) ⟨18322412, by rfl⟩ : syracuseStep 24429883 = 36644825) B36644825
theorem B32573177 : Blo 1905435 32573177 := bstep (se 2 (by rfl) ⟨12214941, by rfl⟩ : syracuseStep 32573177 = 24429883) B24429883
theorem B21715451 : Blo 1905435 21715451 := bstep (se 1 (by rfl) ⟨16286588, by rfl⟩ : syracuseStep 21715451 = 32573177) B32573177
theorem B14476967 : Blo 1905435 14476967 := bstep (se 1 (by rfl) ⟨10857725, by rfl⟩ : syracuseStep 14476967 = 21715451) B21715451
theorem B9651311 : Blo 1905435 9651311 := bstep (se 1 (by rfl) ⟨7238483, by rfl⟩ : syracuseStep 9651311 = 14476967) B14476967
theorem B6434207 : Blo 1905435 6434207 := bstep (se 1 (by rfl) ⟨4825655, by rfl⟩ : syracuseStep 6434207 = 9651311) B9651311
theorem B4289471 : Blo 1905435 4289471 := bstep (se 1 (by rfl) ⟨3217103, by rfl⟩ : syracuseStep 4289471 = 6434207) B6434207
theorem B2859647 : Blo 1905435 2859647 := bstep (se 1 (by rfl) ⟨2144735, by rfl⟩ : syracuseStep 2859647 = 4289471) B4289471
theorem B1906431 : Blo 1905435 1906431 := bstep (se 1 (by rfl) ⟨1429823, by rfl⟩ : syracuseStep 1906431 = 2859647) B2859647
theorem B2859653 : Blo 1905435 2859653 := bbase (se 4 (by rfl) ⟨268092, by rfl⟩ : syracuseStep 2859653 = 536185) (by norm_num)
theorem B1906435 : Blo 1905435 1906435 := bstep (se 1 (by rfl) ⟨1429826, by rfl⟩ : syracuseStep 1906435 = 2859653) B2859653
theorem B3217117 : Blo 1905435 3217117 := bbase (se 3 (by rfl) ⟨603209, by rfl⟩ : syracuseStep 3217117 = 1206419) (by norm_num)
theorem B4289489 : Blo 1905435 4289489 := bstep (se 2 (by rfl) ⟨1608558, by rfl⟩ : syracuseStep 4289489 = 3217117) B3217117
theorem B2859659 : Blo 1905435 2859659 := bstep (se 1 (by rfl) ⟨2144744, by rfl⟩ : syracuseStep 2859659 = 4289489) B4289489
theorem B1906439 : Blo 1905435 1906439 := bstep (se 1 (by rfl) ⟨1429829, by rfl⟩ : syracuseStep 1906439 = 2859659) B2859659
theorem B2144749 : Blo 1905435 2144749 := bbase (se 3 (by rfl) ⟨402140, by rfl⟩ : syracuseStep 2144749 = 804281) (by norm_num)
theorem B2859665 : Blo 1905435 2859665 := bstep (se 2 (by rfl) ⟨1072374, by rfl⟩ : syracuseStep 2859665 = 2144749) B2144749
theorem B1906443 : Blo 1905435 1906443 := bstep (se 1 (by rfl) ⟨1429832, by rfl⟩ : syracuseStep 1906443 = 2859665) B2859665
theorem B6434261 : Blo 1905435 6434261 := bbase (se 7 (by rfl) ⟨75401, by rfl⟩ : syracuseStep 6434261 = 150803) (by norm_num)
theorem B4289507 : Blo 1905435 4289507 := bstep (se 1 (by rfl) ⟨3217130, by rfl⟩ : syracuseStep 4289507 = 6434261) B6434261
theorem B2859671 : Blo 1905435 2859671 := bstep (se 1 (by rfl) ⟨2144753, by rfl⟩ : syracuseStep 2859671 = 4289507) B4289507
theorem B1906447 : Blo 1905435 1906447 := bstep (se 1 (by rfl) ⟨1429835, by rfl⟩ : syracuseStep 1906447 = 2859671) B2859671
theorem B2859677 : Blo 1905435 2859677 := bbase (se 3 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 2859677 = 1072379) (by norm_num)
theorem B1906451 : Blo 1905435 1906451 := bstep (se 1 (by rfl) ⟨1429838, by rfl⟩ : syracuseStep 1906451 = 2859677) B2859677
theorem B4289525 : Blo 1905435 4289525 := bbase (se 5 (by rfl) ⟨201071, by rfl⟩ : syracuseStep 4289525 = 402143) (by norm_num)
theorem B2859683 : Blo 1905435 2859683 := bstep (se 1 (by rfl) ⟨2144762, by rfl⟩ : syracuseStep 2859683 = 4289525) B4289525
theorem B1906455 : Blo 1905435 1906455 := bstep (se 1 (by rfl) ⟨1429841, by rfl⟩ : syracuseStep 1906455 = 2859683) B2859683
theorem B12381781 : Blo 1905435 12381781 := bbase (se 8 (by rfl) ⟨72549, by rfl⟩ : syracuseStep 12381781 = 145099) (by norm_num)
theorem B16509041 : Blo 1905435 16509041 := bstep (se 2 (by rfl) ⟨6190890, by rfl⟩ : syracuseStep 16509041 = 12381781) B12381781
theorem B11006027 : Blo 1905435 11006027 := bstep (se 1 (by rfl) ⟨8254520, by rfl⟩ : syracuseStep 11006027 = 16509041) B16509041
theorem B7337351 : Blo 1905435 7337351 := bstep (se 1 (by rfl) ⟨5503013, by rfl⟩ : syracuseStep 7337351 = 11006027) B11006027
theorem B4891567 : Blo 1905435 4891567 := bstep (se 1 (by rfl) ⟨3668675, by rfl⟩ : syracuseStep 4891567 = 7337351) B7337351
theorem B6522089 : Blo 1905435 6522089 := bstep (se 2 (by rfl) ⟨2445783, by rfl⟩ : syracuseStep 6522089 = 4891567) B4891567
theorem B69568949 : Blo 1905435 69568949 := bstep (se 5 (by rfl) ⟨3261044, by rfl⟩ : syracuseStep 69568949 = 6522089) B6522089
theorem B46379299 : Blo 1905435 46379299 := bstep (se 1 (by rfl) ⟨34784474, by rfl⟩ : syracuseStep 46379299 = 69568949) B69568949
theorem B61839065 : Blo 1905435 61839065 := bstep (se 2 (by rfl) ⟨23189649, by rfl⟩ : syracuseStep 61839065 = 46379299) B46379299
theorem B41226043 : Blo 1905435 41226043 := bstep (se 1 (by rfl) ⟨30919532, by rfl⟩ : syracuseStep 41226043 = 61839065) B61839065
theorem B54968057 : Blo 1905435 54968057 := bstep (se 2 (by rfl) ⟨20613021, by rfl⟩ : syracuseStep 54968057 = 41226043) B41226043
theorem B36645371 : Blo 1905435 36645371 := bstep (se 1 (by rfl) ⟨27484028, by rfl⟩ : syracuseStep 36645371 = 54968057) B54968057
theorem B24430247 : Blo 1905435 24430247 := bstep (se 1 (by rfl) ⟨18322685, by rfl⟩ : syracuseStep 24430247 = 36645371) B36645371
theorem B16286831 : Blo 1905435 16286831 := bstep (se 1 (by rfl) ⟨12215123, by rfl⟩ : syracuseStep 16286831 = 24430247) B24430247
theorem B10857887 : Blo 1905435 10857887 := bstep (se 1 (by rfl) ⟨8143415, by rfl⟩ : syracuseStep 10857887 = 16286831) B16286831
theorem B7238591 : Blo 1905435 7238591 := bstep (se 1 (by rfl) ⟨5428943, by rfl⟩ : syracuseStep 7238591 = 10857887) B10857887
theorem B4825727 : Blo 1905435 4825727 := bstep (se 1 (by rfl) ⟨3619295, by rfl⟩ : syracuseStep 4825727 = 7238591) B7238591
theorem B3217151 : Blo 1905435 3217151 := bstep (se 1 (by rfl) ⟨2412863, by rfl⟩ : syracuseStep 3217151 = 4825727) B4825727
theorem B2144767 : Blo 1905435 2144767 := bstep (se 1 (by rfl) ⟨1608575, by rfl⟩ : syracuseStep 2144767 = 3217151) B3217151
theorem B2859689 : Blo 1905435 2859689 := bstep (se 2 (by rfl) ⟨1072383, by rfl⟩ : syracuseStep 2859689 = 2144767) B2144767
theorem B1906459 : Blo 1905435 1906459 := bstep (se 1 (by rfl) ⟨1429844, by rfl⟩ : syracuseStep 1906459 = 2859689) B2859689
theorem B2714477 : Blo 1905435 2714477 := bbase (se 3 (by rfl) ⟨508964, by rfl⟩ : syracuseStep 2714477 = 1017929) (by norm_num)
theorem B7238605 : Blo 1905435 7238605 := bstep (se 3 (by rfl) ⟨1357238, by rfl⟩ : syracuseStep 7238605 = 2714477) B2714477
theorem B9651473 : Blo 1905435 9651473 := bstep (se 2 (by rfl) ⟨3619302, by rfl⟩ : syracuseStep 9651473 = 7238605) B7238605
theorem B6434315 : Blo 1905435 6434315 := bstep (se 1 (by rfl) ⟨4825736, by rfl⟩ : syracuseStep 6434315 = 9651473) B9651473
theorem B4289543 : Blo 1905435 4289543 := bstep (se 1 (by rfl) ⟨3217157, by rfl⟩ : syracuseStep 4289543 = 6434315) B6434315
theorem B2859695 : Blo 1905435 2859695 := bstep (se 1 (by rfl) ⟨2144771, by rfl⟩ : syracuseStep 2859695 = 4289543) B4289543
theorem B1906463 : Blo 1905435 1906463 := bstep (se 1 (by rfl) ⟨1429847, by rfl⟩ : syracuseStep 1906463 = 2859695) B2859695
theorem B2859701 : Blo 1905435 2859701 := bbase (se 5 (by rfl) ⟨134048, by rfl⟩ : syracuseStep 2859701 = 268097) (by norm_num)
theorem B1906467 : Blo 1905435 1906467 := bstep (se 1 (by rfl) ⟨1429850, by rfl⟩ : syracuseStep 1906467 = 2859701) B2859701
theorem B4825757 : Blo 1905435 4825757 := bbase (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) (by norm_num)
theorem B3217171 : Blo 1905435 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B4289561 : Blo 1905435 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B2859707 : Blo 1905435 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B1906471 : Blo 1905435 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B2144785 : Blo 1905435 2144785 := bbase (se 2 (by rfl) ⟨804294, by rfl⟩ : syracuseStep 2144785 = 1608589) (by norm_num)
theorem B2859713 : Blo 1905435 2859713 := bstep (se 2 (by rfl) ⟨1072392, by rfl⟩ : syracuseStep 2859713 = 2144785) B2144785
theorem B1906475 : Blo 1905435 1906475 := bstep (se 1 (by rfl) ⟨1429856, by rfl⟩ : syracuseStep 1906475 = 2859713) B2859713
theorem B3619333 : Blo 1905435 3619333 := bbase (se 4 (by rfl) ⟨339312, by rfl⟩ : syracuseStep 3619333 = 678625) (by norm_num)
theorem B4825777 : Blo 1905435 4825777 := bstep (se 2 (by rfl) ⟨1809666, by rfl⟩ : syracuseStep 4825777 = 3619333) B3619333
theorem B6434369 : Blo 1905435 6434369 := bstep (se 2 (by rfl) ⟨2412888, by rfl⟩ : syracuseStep 6434369 = 4825777) B4825777
theorem B4289579 : Blo 1905435 4289579 := bstep (se 1 (by rfl) ⟨3217184, by rfl⟩ : syracuseStep 4289579 = 6434369) B6434369
theorem B2859719 : Blo 1905435 2859719 := bstep (se 1 (by rfl) ⟨2144789, by rfl⟩ : syracuseStep 2859719 = 4289579) B4289579
theorem B1906479 : Blo 1905435 1906479 := bstep (se 1 (by rfl) ⟨1429859, by rfl⟩ : syracuseStep 1906479 = 2859719) B2859719
theorem B2859725 : Blo 1905435 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B1906483 : Blo 1905435 1906483 := bstep (se 1 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 1906483 = 2859725) B2859725
theorem B4289597 : Blo 1905435 4289597 := bbase (se 3 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 4289597 = 1608599) (by norm_num)
theorem B2859731 : Blo 1905435 2859731 := bstep (se 1 (by rfl) ⟨2144798, by rfl⟩ : syracuseStep 2859731 = 4289597) B4289597
theorem B1906487 : Blo 1905435 1906487 := bstep (se 1 (by rfl) ⟨1429865, by rfl⟩ : syracuseStep 1906487 = 2859731) B2859731
theorem B3217205 : Blo 1905435 3217205 := bbase (se 5 (by rfl) ⟨150806, by rfl⟩ : syracuseStep 3217205 = 301613) (by norm_num)
theorem B2144803 : Blo 1905435 2144803 := bstep (se 1 (by rfl) ⟨1608602, by rfl⟩ : syracuseStep 2144803 = 3217205) B3217205
theorem B2859737 : Blo 1905435 2859737 := bstep (se 2 (by rfl) ⟨1072401, by rfl⟩ : syracuseStep 2859737 = 2144803) B2144803
theorem B1906491 : Blo 1905435 1906491 := bstep (se 1 (by rfl) ⟨1429868, by rfl⟩ : syracuseStep 1906491 = 2859737) B2859737
theorem B5429045 : Blo 1905435 5429045 := bbase (se 5 (by rfl) ⟨254486, by rfl⟩ : syracuseStep 5429045 = 508973) (by norm_num)
theorem B14477453 : Blo 1905435 14477453 := bstep (se 3 (by rfl) ⟨2714522, by rfl⟩ : syracuseStep 14477453 = 5429045) B5429045
theorem B9651635 : Blo 1905435 9651635 := bstep (se 1 (by rfl) ⟨7238726, by rfl⟩ : syracuseStep 9651635 = 14477453) B14477453
theorem B6434423 : Blo 1905435 6434423 := bstep (se 1 (by rfl) ⟨4825817, by rfl⟩ : syracuseStep 6434423 = 9651635) B9651635
theorem B4289615 : Blo 1905435 4289615 := bstep (se 1 (by rfl) ⟨3217211, by rfl⟩ : syracuseStep 4289615 = 6434423) B6434423
theorem B2859743 : Blo 1905435 2859743 := bstep (se 1 (by rfl) ⟨2144807, by rfl⟩ : syracuseStep 2859743 = 4289615) B4289615
theorem B1906495 : Blo 1905435 1906495 := bstep (se 1 (by rfl) ⟨1429871, by rfl⟩ : syracuseStep 1906495 = 2859743) B2859743
theorem B2859749 : Blo 1905435 2859749 := bbase (se 4 (by rfl) ⟨268101, by rfl⟩ : syracuseStep 2859749 = 536203) (by norm_num)
theorem B1906499 : Blo 1905435 1906499 := bstep (se 1 (by rfl) ⟨1429874, by rfl⟩ : syracuseStep 1906499 = 2859749) B2859749
theorem B2035901 : Blo 1905435 2035901 := bbase (se 3 (by rfl) ⟨381731, by rfl⟩ : syracuseStep 2035901 = 763463) (by norm_num)
theorem B5429069 : Blo 1905435 5429069 := bstep (se 3 (by rfl) ⟨1017950, by rfl⟩ : syracuseStep 5429069 = 2035901) B2035901
theorem B3619379 : Blo 1905435 3619379 := bstep (se 1 (by rfl) ⟨2714534, by rfl⟩ : syracuseStep 3619379 = 5429069) B5429069
theorem B2412919 : Blo 1905435 2412919 := bstep (se 1 (by rfl) ⟨1809689, by rfl⟩ : syracuseStep 2412919 = 3619379) B3619379
theorem B3217225 : Blo 1905435 3217225 := bstep (se 2 (by rfl) ⟨1206459, by rfl⟩ : syracuseStep 3217225 = 2412919) B2412919
theorem B4289633 : Blo 1905435 4289633 := bstep (se 2 (by rfl) ⟨1608612, by rfl⟩ : syracuseStep 4289633 = 3217225) B3217225
theorem B2859755 : Blo 1905435 2859755 := bstep (se 1 (by rfl) ⟨2144816, by rfl⟩ : syracuseStep 2859755 = 4289633) B4289633
theorem B1906503 : Blo 1905435 1906503 := bstep (se 1 (by rfl) ⟨1429877, by rfl⟩ : syracuseStep 1906503 = 2859755) B2859755
theorem B2144821 : Blo 1905435 2144821 := bbase (se 5 (by rfl) ⟨100538, by rfl⟩ : syracuseStep 2144821 = 201077) (by norm_num)
theorem B2859761 : Blo 1905435 2859761 := bstep (se 2 (by rfl) ⟨1072410, by rfl⟩ : syracuseStep 2859761 = 2144821) B2144821
theorem B1906507 : Blo 1905435 1906507 := bstep (se 1 (by rfl) ⟨1429880, by rfl⟩ : syracuseStep 1906507 = 2859761) B2859761
theorem B2412929 : Blo 1905435 2412929 := bbase (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) (by norm_num)
theorem B6434477 : Blo 1905435 6434477 := bstep (se 3 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 6434477 = 2412929) B2412929
theorem B4289651 : Blo 1905435 4289651 := bstep (se 1 (by rfl) ⟨3217238, by rfl⟩ : syracuseStep 4289651 = 6434477) B6434477
theorem B2859767 : Blo 1905435 2859767 := bstep (se 1 (by rfl) ⟨2144825, by rfl⟩ : syracuseStep 2859767 = 4289651) B4289651
theorem B1906511 : Blo 1905435 1906511 := bstep (se 1 (by rfl) ⟨1429883, by rfl⟩ : syracuseStep 1906511 = 2859767) B2859767
theorem B2859773 : Blo 1905435 2859773 := bbase (se 3 (by rfl) ⟨536207, by rfl⟩ : syracuseStep 2859773 = 1072415) (by norm_num)
theorem B1906515 : Blo 1905435 1906515 := bstep (se 1 (by rfl) ⟨1429886, by rfl⟩ : syracuseStep 1906515 = 2859773) B2859773
theorem B4289669 : Blo 1905435 4289669 := bbase (se 4 (by rfl) ⟨402156, by rfl⟩ : syracuseStep 4289669 = 804313) (by norm_num)
theorem B2859779 : Blo 1905435 2859779 := bstep (se 1 (by rfl) ⟨2144834, by rfl⟩ : syracuseStep 2859779 = 4289669) B4289669
theorem B1906519 : Blo 1905435 1906519 := bstep (se 1 (by rfl) ⟨1429889, by rfl⟩ : syracuseStep 1906519 = 2859779) B2859779
theorem B4071845 : Blo 1905435 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B2714563 : Blo 1905435 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B3619417 : Blo 1905435 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B4825889 : Blo 1905435 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B3217259 : Blo 1905435 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B2144839 : Blo 1905435 2144839 := bstep (se 1 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 2144839 = 3217259) B3217259
theorem B2859785 : Blo 1905435 2859785 := bstep (se 2 (by rfl) ⟨1072419, by rfl⟩ : syracuseStep 2859785 = 2144839) B2144839
theorem B1906523 : Blo 1905435 1906523 := bstep (se 1 (by rfl) ⟨1429892, by rfl⟩ : syracuseStep 1906523 = 2859785) B2859785
theorem B9651797 : Blo 1905435 9651797 := bbase (se 8 (by rfl) ⟨56553, by rfl⟩ : syracuseStep 9651797 = 113107) (by norm_num)
theorem B6434531 : Blo 1905435 6434531 := bstep (se 1 (by rfl) ⟨4825898, by rfl⟩ : syracuseStep 6434531 = 9651797) B9651797
theorem B4289687 : Blo 1905435 4289687 := bstep (se 1 (by rfl) ⟨3217265, by rfl⟩ : syracuseStep 4289687 = 6434531) B6434531
theorem B2859791 : Blo 1905435 2859791 := bstep (se 1 (by rfl) ⟨2144843, by rfl⟩ : syracuseStep 2859791 = 4289687) B4289687
theorem B1906527 : Blo 1905435 1906527 := bstep (se 1 (by rfl) ⟨1429895, by rfl⟩ : syracuseStep 1906527 = 2859791) B2859791
theorem B2859797 : Blo 1905435 2859797 := bbase (se 6 (by rfl) ⟨67026, by rfl⟩ : syracuseStep 2859797 = 134053) (by norm_num)
theorem B1906531 : Blo 1905435 1906531 := bstep (se 1 (by rfl) ⟨1429898, by rfl⟩ : syracuseStep 1906531 = 2859797) B2859797
theorem B2445881 : Blo 1905435 2445881 := bbase (se 2 (by rfl) ⟨917205, by rfl⟩ : syracuseStep 2445881 = 1834411) (by norm_num)
theorem B26089397 : Blo 1905435 26089397 := bstep (se 5 (by rfl) ⟨1222940, by rfl⟩ : syracuseStep 26089397 = 2445881) B2445881
theorem B17392931 : Blo 1905435 17392931 := bstep (se 1 (by rfl) ⟨13044698, by rfl⟩ : syracuseStep 17392931 = 26089397) B26089397
theorem B11595287 : Blo 1905435 11595287 := bstep (se 1 (by rfl) ⟨8696465, by rfl⟩ : syracuseStep 11595287 = 17392931) B17392931
theorem B7730191 : Blo 1905435 7730191 := bstep (se 1 (by rfl) ⟨5797643, by rfl⟩ : syracuseStep 7730191 = 11595287) B11595287
theorem B10306921 : Blo 1905435 10306921 := bstep (se 2 (by rfl) ⟨3865095, by rfl⟩ : syracuseStep 10306921 = 7730191) B7730191
theorem B13742561 : Blo 1905435 13742561 := bstep (se 2 (by rfl) ⟨5153460, by rfl⟩ : syracuseStep 13742561 = 10306921) B10306921
theorem B36646829 : Blo 1905435 36646829 := bstep (se 3 (by rfl) ⟨6871280, by rfl⟩ : syracuseStep 36646829 = 13742561) B13742561
theorem B24431219 : Blo 1905435 24431219 := bstep (se 1 (by rfl) ⟨18323414, by rfl⟩ : syracuseStep 24431219 = 36646829) B36646829
theorem B16287479 : Blo 1905435 16287479 := bstep (se 1 (by rfl) ⟨12215609, by rfl⟩ : syracuseStep 16287479 = 24431219) B24431219
theorem B10858319 : Blo 1905435 10858319 := bstep (se 1 (by rfl) ⟨8143739, by rfl⟩ : syracuseStep 10858319 = 16287479) B16287479
theorem B7238879 : Blo 1905435 7238879 := bstep (se 1 (by rfl) ⟨5429159, by rfl⟩ : syracuseStep 7238879 = 10858319) B10858319
theorem B4825919 : Blo 1905435 4825919 := bstep (se 1 (by rfl) ⟨3619439, by rfl⟩ : syracuseStep 4825919 = 7238879) B7238879
theorem B3217279 : Blo 1905435 3217279 := bstep (se 1 (by rfl) ⟨2412959, by rfl⟩ : syracuseStep 3217279 = 4825919) B4825919
theorem B4289705 : Blo 1905435 4289705 := bstep (se 2 (by rfl) ⟨1608639, by rfl⟩ : syracuseStep 4289705 = 3217279) B3217279
theorem B2859803 : Blo 1905435 2859803 := bstep (se 1 (by rfl) ⟨2144852, by rfl⟩ : syracuseStep 2859803 = 4289705) B4289705
theorem B1906535 : Blo 1905435 1906535 := bstep (se 1 (by rfl) ⟨1429901, by rfl⟩ : syracuseStep 1906535 = 2859803) B2859803
theorem B2144857 : Blo 1905435 2144857 := bbase (se 2 (by rfl) ⟨804321, by rfl⟩ : syracuseStep 2144857 = 1608643) (by norm_num)
theorem B2859809 : Blo 1905435 2859809 := bstep (se 2 (by rfl) ⟨1072428, by rfl⟩ : syracuseStep 2859809 = 2144857) B2144857
theorem B1906539 : Blo 1905435 1906539 := bstep (se 1 (by rfl) ⟨1429904, by rfl⟩ : syracuseStep 1906539 = 2859809) B2859809
theorem B5797669 : Blo 1905435 5797669 := bbase (se 4 (by rfl) ⟨543531, by rfl⟩ : syracuseStep 5797669 = 1087063) (by norm_num)
theorem B7730225 : Blo 1905435 7730225 := bstep (se 2 (by rfl) ⟨2898834, by rfl⟩ : syracuseStep 7730225 = 5797669) B5797669
theorem B5153483 : Blo 1905435 5153483 := bstep (se 1 (by rfl) ⟨3865112, by rfl⟩ : syracuseStep 5153483 = 7730225) B7730225
theorem B13742621 : Blo 1905435 13742621 := bstep (se 3 (by rfl) ⟨2576741, by rfl⟩ : syracuseStep 13742621 = 5153483) B5153483
theorem B9161747 : Blo 1905435 9161747 := bstep (se 1 (by rfl) ⟨6871310, by rfl⟩ : syracuseStep 9161747 = 13742621) B13742621
theorem B6107831 : Blo 1905435 6107831 := bstep (se 1 (by rfl) ⟨4580873, by rfl⟩ : syracuseStep 6107831 = 9161747) B9161747
theorem B4071887 : Blo 1905435 4071887 := bstep (se 1 (by rfl) ⟨3053915, by rfl⟩ : syracuseStep 4071887 = 6107831) B6107831
theorem B2714591 : Blo 1905435 2714591 := bstep (se 1 (by rfl) ⟨2035943, by rfl⟩ : syracuseStep 2714591 = 4071887) B4071887
theorem B7238909 : Blo 1905435 7238909 := bstep (se 3 (by rfl) ⟨1357295, by rfl⟩ : syracuseStep 7238909 = 2714591) B2714591
theorem B4825939 : Blo 1905435 4825939 := bstep (se 1 (by rfl) ⟨3619454, by rfl⟩ : syracuseStep 4825939 = 7238909) B7238909
theorem B6434585 : Blo 1905435 6434585 := bstep (se 2 (by rfl) ⟨2412969, by rfl⟩ : syracuseStep 6434585 = 4825939) B4825939
theorem B4289723 : Blo 1905435 4289723 := bstep (se 1 (by rfl) ⟨3217292, by rfl⟩ : syracuseStep 4289723 = 6434585) B6434585
theorem B2859815 : Blo 1905435 2859815 := bstep (se 1 (by rfl) ⟨2144861, by rfl⟩ : syracuseStep 2859815 = 4289723) B4289723
theorem B1906543 : Blo 1905435 1906543 := bstep (se 1 (by rfl) ⟨1429907, by rfl⟩ : syracuseStep 1906543 = 2859815) B2859815
theorem B2859821 : Blo 1905435 2859821 := bbase (se 3 (by rfl) ⟨536216, by rfl⟩ : syracuseStep 2859821 = 1072433) (by norm_num)
theorem B1906547 : Blo 1905435 1906547 := bstep (se 1 (by rfl) ⟨1429910, by rfl⟩ : syracuseStep 1906547 = 2859821) B2859821
theorem B4289741 : Blo 1905435 4289741 := bbase (se 3 (by rfl) ⟨804326, by rfl⟩ : syracuseStep 4289741 = 1608653) (by norm_num)
theorem B2859827 : Blo 1905435 2859827 := bstep (se 1 (by rfl) ⟨2144870, by rfl⟩ : syracuseStep 2859827 = 4289741) B4289741
theorem B1906551 : Blo 1905435 1906551 := bstep (se 1 (by rfl) ⟨1429913, by rfl⟩ : syracuseStep 1906551 = 2859827) B2859827
theorem B2412985 : Blo 1905435 2412985 := bbase (se 2 (by rfl) ⟨904869, by rfl⟩ : syracuseStep 2412985 = 1809739) (by norm_num)
theorem B3217313 : Blo 1905435 3217313 := bstep (se 2 (by rfl) ⟨1206492, by rfl⟩ : syracuseStep 3217313 = 2412985) B2412985
theorem B2144875 : Blo 1905435 2144875 := bstep (se 1 (by rfl) ⟨1608656, by rfl⟩ : syracuseStep 2144875 = 3217313) B3217313
theorem B2859833 : Blo 1905435 2859833 := bstep (se 2 (by rfl) ⟨1072437, by rfl⟩ : syracuseStep 2859833 = 2144875) B2144875
theorem B1906555 : Blo 1905435 1906555 := bstep (se 1 (by rfl) ⟨1429916, by rfl⟩ : syracuseStep 1906555 = 2859833) B2859833
theorem B2617381 : Blo 1905435 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B3489841 : Blo 1905435 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B4653121 : Blo 1905435 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B6204161 : Blo 1905435 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B4136107 : Blo 1905435 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B5514809 : Blo 1905435 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B58824629 : Blo 1905435 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B39216419 : Blo 1905435 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B26144279 : Blo 1905435 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B17429519 : Blo 1905435 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B46478717 : Blo 1905435 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B30985811 : Blo 1905435 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B20657207 : Blo 1905435 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B13771471 : Blo 1905435 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B18361961 : Blo 1905435 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B12241307 : Blo 1905435 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B8160871 : Blo 1905435 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B10881161 : Blo 1905435 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B7254107 : Blo 1905435 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B4836071 : Blo 1905435 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B12896189 : Blo 1905435 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B8597459 : Blo 1905435 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B22926557 : Blo 1905435 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B15284371 : Blo 1905435 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B20379161 : Blo 1905435 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B54344429 : Blo 1905435 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B36229619 : Blo 1905435 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B24153079 : Blo 1905435 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B32204105 : Blo 1905435 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B21469403 : Blo 1905435 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B14312935 : Blo 1905435 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B76335653 : Blo 1905435 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B203561741 : Blo 1905435 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B135707827 : Blo 1905435 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B180943769 : Blo 1905435 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B120629179 : Blo 1905435 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B643355621 : Blo 1905435 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B428903747 : Blo 1905435 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B285935831 : Blo 1905435 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B190623887 : Blo 1905435 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B127082591 : Blo 1905435 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B84721727 : Blo 1905435 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B56481151 : Blo 1905435 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B75308201 : Blo 1905435 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B50205467 : Blo 1905435 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B133881245 : Blo 1905435 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B89254163 : Blo 1905435 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B59502775 : Blo 1905435 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B79337033 : Blo 1905435 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B52891355 : Blo 1905435 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B35260903 : Blo 1905435 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B188058149 : Blo 1905435 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B125372099 : Blo 1905435 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B83581399 : Blo 1905435 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B111441865 : Blo 1905435 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B148589153 : Blo 1905435 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B99059435 : Blo 1905435 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B66039623 : Blo 1905435 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B44026415 : Blo 1905435 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B29350943 : Blo 1905435 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B19567295 : Blo 1905435 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B13044863 : Blo 1905435 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B8696575 : Blo 1905435 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B11595433 : Blo 1905435 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 1905435 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B10307051 : Blo 1905435 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B6871367 : Blo 1905435 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B4580911 : Blo 1905435 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B6107881 : Blo 1905435 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 1905435 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B21716909 : Blo 1905435 21716909 := bstep (se 3 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 21716909 = 8143841) B8143841
theorem B14477939 : Blo 1905435 14477939 := bstep (se 1 (by rfl) ⟨10858454, by rfl⟩ : syracuseStep 14477939 = 21716909) B21716909
theorem B9651959 : Blo 1905435 9651959 := bstep (se 1 (by rfl) ⟨7238969, by rfl⟩ : syracuseStep 9651959 = 14477939) B14477939
theorem B6434639 : Blo 1905435 6434639 := bstep (se 1 (by rfl) ⟨4825979, by rfl⟩ : syracuseStep 6434639 = 9651959) B9651959
theorem B4289759 : Blo 1905435 4289759 := bstep (se 1 (by rfl) ⟨3217319, by rfl⟩ : syracuseStep 4289759 = 6434639) B6434639
theorem B2859839 : Blo 1905435 2859839 := bstep (se 1 (by rfl) ⟨2144879, by rfl⟩ : syracuseStep 2859839 = 4289759) B4289759
theorem B1906559 : Blo 1905435 1906559 := bstep (se 1 (by rfl) ⟨1429919, by rfl⟩ : syracuseStep 1906559 = 2859839) B2859839
theorem B2859845 : Blo 1905435 2859845 := bbase (se 4 (by rfl) ⟨268110, by rfl⟩ : syracuseStep 2859845 = 536221) (by norm_num)
theorem B1906563 : Blo 1905435 1906563 := bstep (se 1 (by rfl) ⟨1429922, by rfl⟩ : syracuseStep 1906563 = 2859845) B2859845
theorem B3217333 : Blo 1905435 3217333 := bbase (se 5 (by rfl) ⟨150812, by rfl⟩ : syracuseStep 3217333 = 301625) (by norm_num)
theorem B4289777 : Blo 1905435 4289777 := bstep (se 2 (by rfl) ⟨1608666, by rfl⟩ : syracuseStep 4289777 = 3217333) B3217333
theorem B2859851 : Blo 1905435 2859851 := bstep (se 1 (by rfl) ⟨2144888, by rfl⟩ : syracuseStep 2859851 = 4289777) B4289777
theorem B1906567 : Blo 1905435 1906567 := bstep (se 1 (by rfl) ⟨1429925, by rfl⟩ : syracuseStep 1906567 = 2859851) B2859851
theorem B2144893 : Blo 1905435 2144893 := bbase (se 3 (by rfl) ⟨402167, by rfl⟩ : syracuseStep 2144893 = 804335) (by norm_num)
theorem B2859857 : Blo 1905435 2859857 := bstep (se 2 (by rfl) ⟨1072446, by rfl⟩ : syracuseStep 2859857 = 2144893) B2144893
theorem B1906571 : Blo 1905435 1906571 := bstep (se 1 (by rfl) ⟨1429928, by rfl⟩ : syracuseStep 1906571 = 2859857) B2859857
theorem B6434693 : Blo 1905435 6434693 := bbase (se 4 (by rfl) ⟨603252, by rfl⟩ : syracuseStep 6434693 = 1206505) (by norm_num)
theorem B4289795 : Blo 1905435 4289795 := bstep (se 1 (by rfl) ⟨3217346, by rfl⟩ : syracuseStep 4289795 = 6434693) B6434693
theorem B2859863 : Blo 1905435 2859863 := bstep (se 1 (by rfl) ⟨2144897, by rfl⟩ : syracuseStep 2859863 = 4289795) B4289795
theorem B1906575 : Blo 1905435 1906575 := bstep (se 1 (by rfl) ⟨1429931, by rfl⟩ : syracuseStep 1906575 = 2859863) B2859863
theorem B2859869 : Blo 1905435 2859869 := bbase (se 3 (by rfl) ⟨536225, by rfl⟩ : syracuseStep 2859869 = 1072451) (by norm_num)
theorem B1906579 : Blo 1905435 1906579 := bstep (se 1 (by rfl) ⟨1429934, by rfl⟩ : syracuseStep 1906579 = 2859869) B2859869
theorem B4289813 : Blo 1905435 4289813 := bbase (se 6 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 4289813 = 201085) (by norm_num)
theorem B2859875 : Blo 1905435 2859875 := bstep (se 1 (by rfl) ⟨2144906, by rfl⟩ : syracuseStep 2859875 = 4289813) B4289813
theorem B1906583 : Blo 1905435 1906583 := bstep (se 1 (by rfl) ⟨1429937, by rfl⟩ : syracuseStep 1906583 = 2859875) B2859875
theorem B7239077 : Blo 1905435 7239077 := bbase (se 4 (by rfl) ⟨678663, by rfl⟩ : syracuseStep 7239077 = 1357327) (by norm_num)
theorem B4826051 : Blo 1905435 4826051 := bstep (se 1 (by rfl) ⟨3619538, by rfl⟩ : syracuseStep 4826051 = 7239077) B7239077
theorem B3217367 : Blo 1905435 3217367 := bstep (se 1 (by rfl) ⟨2413025, by rfl⟩ : syracuseStep 3217367 = 4826051) B4826051
theorem B2144911 : Blo 1905435 2144911 := bstep (se 1 (by rfl) ⟨1608683, by rfl⟩ : syracuseStep 2144911 = 3217367) B3217367
theorem B2859881 : Blo 1905435 2859881 := bstep (se 2 (by rfl) ⟨1072455, by rfl⟩ : syracuseStep 2859881 = 2144911) B2144911
theorem B1906587 : Blo 1905435 1906587 := bstep (se 1 (by rfl) ⟨1429940, by rfl⟩ : syracuseStep 1906587 = 2859881) B2859881
theorem B4071989 : Blo 1905435 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B10858637 : Blo 1905435 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B7239091 : Blo 1905435 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B9652121 : Blo 1905435 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B6434747 : Blo 1905435 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B4289831 : Blo 1905435 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B2859887 : Blo 1905435 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B1906591 : Blo 1905435 1906591 := bstep (se 1 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 1906591 = 2859887) B2859887
theorem B2859893 : Blo 1905435 2859893 := bbase (se 5 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 2859893 = 268115) (by norm_num)
theorem B1906595 : Blo 1905435 1906595 := bstep (se 1 (by rfl) ⟨1429946, by rfl⟩ : syracuseStep 1906595 = 2859893) B2859893
theorem B7730453 : Blo 1905435 7730453 := bbase (se 6 (by rfl) ⟨181182, by rfl⟩ : syracuseStep 7730453 = 362365) (by norm_num)
theorem B5153635 : Blo 1905435 5153635 := bstep (se 1 (by rfl) ⟨3865226, by rfl⟩ : syracuseStep 5153635 = 7730453) B7730453
theorem B6871513 : Blo 1905435 6871513 := bstep (se 2 (by rfl) ⟨2576817, by rfl⟩ : syracuseStep 6871513 = 5153635) B5153635
theorem B9162017 : Blo 1905435 9162017 := bstep (se 2 (by rfl) ⟨3435756, by rfl⟩ : syracuseStep 9162017 = 6871513) B6871513
theorem B6108011 : Blo 1905435 6108011 := bstep (se 1 (by rfl) ⟨4581008, by rfl⟩ : syracuseStep 6108011 = 9162017) B9162017
theorem B4072007 : Blo 1905435 4072007 := bstep (se 1 (by rfl) ⟨3054005, by rfl⟩ : syracuseStep 4072007 = 6108011) B6108011
theorem B2714671 : Blo 1905435 2714671 := bstep (se 1 (by rfl) ⟨2036003, by rfl⟩ : syracuseStep 2714671 = 4072007) B4072007
theorem B3619561 : Blo 1905435 3619561 := bstep (se 2 (by rfl) ⟨1357335, by rfl⟩ : syracuseStep 3619561 = 2714671) B2714671
theorem B4826081 : Blo 1905435 4826081 := bstep (se 2 (by rfl) ⟨1809780, by rfl⟩ : syracuseStep 4826081 = 3619561) B3619561
theorem B3217387 : Blo 1905435 3217387 := bstep (se 1 (by rfl) ⟨2413040, by rfl⟩ : syracuseStep 3217387 = 4826081) B4826081
theorem B4289849 : Blo 1905435 4289849 := bstep (se 2 (by rfl) ⟨1608693, by rfl⟩ : syracuseStep 4289849 = 3217387) B3217387
theorem B2859899 : Blo 1905435 2859899 := bstep (se 1 (by rfl) ⟨2144924, by rfl⟩ : syracuseStep 2859899 = 4289849) B4289849
theorem B1906599 : Blo 1905435 1906599 := bstep (se 1 (by rfl) ⟨1429949, by rfl⟩ : syracuseStep 1906599 = 2859899) B2859899
theorem B2144929 : Blo 1905435 2144929 := bbase (se 2 (by rfl) ⟨804348, by rfl⟩ : syracuseStep 2144929 = 1608697) (by norm_num)
theorem B2859905 : Blo 1905435 2859905 := bstep (se 2 (by rfl) ⟨1072464, by rfl⟩ : syracuseStep 2859905 = 2144929) B2144929
theorem B1906603 : Blo 1905435 1906603 := bstep (se 1 (by rfl) ⟨1429952, by rfl⟩ : syracuseStep 1906603 = 2859905) B2859905
theorem B4826101 : Blo 1905435 4826101 := bbase (se 5 (by rfl) ⟨226223, by rfl⟩ : syracuseStep 4826101 = 452447) (by norm_num)
theorem B6434801 : Blo 1905435 6434801 := bstep (se 2 (by rfl) ⟨2413050, by rfl⟩ : syracuseStep 6434801 = 4826101) B4826101
theorem B4289867 : Blo 1905435 4289867 := bstep (se 1 (by rfl) ⟨3217400, by rfl⟩ : syracuseStep 4289867 = 6434801) B6434801
theorem B2859911 : Blo 1905435 2859911 := bstep (se 1 (by rfl) ⟨2144933, by rfl⟩ : syracuseStep 2859911 = 4289867) B4289867
theorem B1906607 : Blo 1905435 1906607 := bstep (se 1 (by rfl) ⟨1429955, by rfl⟩ : syracuseStep 1906607 = 2859911) B2859911
theorem B2859917 : Blo 1905435 2859917 := bbase (se 3 (by rfl) ⟨536234, by rfl⟩ : syracuseStep 2859917 = 1072469) (by norm_num)
theorem B1906611 : Blo 1905435 1906611 := bstep (se 1 (by rfl) ⟨1429958, by rfl⟩ : syracuseStep 1906611 = 2859917) B2859917
theorem B4289885 : Blo 1905435 4289885 := bbase (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) (by norm_num)
theorem B2859923 : Blo 1905435 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B1906615 : Blo 1905435 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B3217421 : Blo 1905435 3217421 := bbase (se 3 (by rfl) ⟨603266, by rfl⟩ : syracuseStep 3217421 = 1206533) (by norm_num)
theorem B2144947 : Blo 1905435 2144947 := bstep (se 1 (by rfl) ⟨1608710, by rfl⟩ : syracuseStep 2144947 = 3217421) B3217421
theorem B2859929 : Blo 1905435 2859929 := bstep (se 2 (by rfl) ⟨1072473, by rfl⟩ : syracuseStep 2859929 = 2144947) B2144947
theorem B1906619 : Blo 1905435 1906619 := bstep (se 1 (by rfl) ⟨1429964, by rfl⟩ : syracuseStep 1906619 = 2859929) B2859929
theorem B7730549 : Blo 1905435 7730549 := bbase (se 5 (by rfl) ⟨362369, by rfl⟩ : syracuseStep 7730549 = 724739) (by norm_num)
theorem B5153699 : Blo 1905435 5153699 := bstep (se 1 (by rfl) ⟨3865274, by rfl⟩ : syracuseStep 5153699 = 7730549) B7730549
theorem B3435799 : Blo 1905435 3435799 := bstep (se 1 (by rfl) ⟨2576849, by rfl⟩ : syracuseStep 3435799 = 5153699) B5153699
theorem B4581065 : Blo 1905435 4581065 := bstep (se 2 (by rfl) ⟨1717899, by rfl⟩ : syracuseStep 4581065 = 3435799) B3435799
theorem B3054043 : Blo 1905435 3054043 := bstep (se 1 (by rfl) ⟨2290532, by rfl⟩ : syracuseStep 3054043 = 4581065) B4581065
theorem B16288229 : Blo 1905435 16288229 := bstep (se 4 (by rfl) ⟨1527021, by rfl⟩ : syracuseStep 16288229 = 3054043) B3054043
theorem B10858819 : Blo 1905435 10858819 := bstep (se 1 (by rfl) ⟨8144114, by rfl⟩ : syracuseStep 10858819 = 16288229) B16288229
theorem B14478425 : Blo 1905435 14478425 := bstep (se 2 (by rfl) ⟨5429409, by rfl⟩ : syracuseStep 14478425 = 10858819) B10858819
theorem B9652283 : Blo 1905435 9652283 := bstep (se 1 (by rfl) ⟨7239212, by rfl⟩ : syracuseStep 9652283 = 14478425) B14478425
theorem B6434855 : Blo 1905435 6434855 := bstep (se 1 (by rfl) ⟨4826141, by rfl⟩ : syracuseStep 6434855 = 9652283) B9652283
theorem B4289903 : Blo 1905435 4289903 := bstep (se 1 (by rfl) ⟨3217427, by rfl⟩ : syracuseStep 4289903 = 6434855) B6434855
theorem B2859935 : Blo 1905435 2859935 := bstep (se 1 (by rfl) ⟨2144951, by rfl⟩ : syracuseStep 2859935 = 4289903) B4289903
theorem B1906623 : Blo 1905435 1906623 := bstep (se 1 (by rfl) ⟨1429967, by rfl⟩ : syracuseStep 1906623 = 2859935) B2859935
theorem B2859941 : Blo 1905435 2859941 := bbase (se 4 (by rfl) ⟨268119, by rfl⟩ : syracuseStep 2859941 = 536239) (by norm_num)
theorem B1906627 : Blo 1905435 1906627 := bstep (se 1 (by rfl) ⟨1429970, by rfl⟩ : syracuseStep 1906627 = 2859941) B2859941
theorem B2413081 : Blo 1905435 2413081 := bbase (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) (by norm_num)
theorem B3217441 : Blo 1905435 3217441 := bstep (se 2 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 3217441 = 2413081) B2413081
theorem B4289921 : Blo 1905435 4289921 := bstep (se 2 (by rfl) ⟨1608720, by rfl⟩ : syracuseStep 4289921 = 3217441) B3217441
theorem B2859947 : Blo 1905435 2859947 := bstep (se 1 (by rfl) ⟨2144960, by rfl⟩ : syracuseStep 2859947 = 4289921) B4289921
theorem B1906631 : Blo 1905435 1906631 := bstep (se 1 (by rfl) ⟨1429973, by rfl⟩ : syracuseStep 1906631 = 2859947) B2859947
theorem B2144965 : Blo 1905435 2144965 := bbase (se 4 (by rfl) ⟨201090, by rfl⟩ : syracuseStep 2144965 = 402181) (by norm_num)
theorem B2859953 : Blo 1905435 2859953 := bstep (se 2 (by rfl) ⟨1072482, by rfl⟩ : syracuseStep 2859953 = 2144965) B2144965
theorem B1906635 : Blo 1905435 1906635 := bstep (se 1 (by rfl) ⟨1429976, by rfl⟩ : syracuseStep 1906635 = 2859953) B2859953
theorem B3619637 : Blo 1905435 3619637 := bbase (se 5 (by rfl) ⟨169670, by rfl⟩ : syracuseStep 3619637 = 339341) (by norm_num)
theorem B2413091 : Blo 1905435 2413091 := bstep (se 1 (by rfl) ⟨1809818, by rfl⟩ : syracuseStep 2413091 = 3619637) B3619637
theorem B6434909 : Blo 1905435 6434909 := bstep (se 3 (by rfl) ⟨1206545, by rfl⟩ : syracuseStep 6434909 = 2413091) B2413091
theorem B4289939 : Blo 1905435 4289939 := bstep (se 1 (by rfl) ⟨3217454, by rfl⟩ : syracuseStep 4289939 = 6434909) B6434909
theorem B2859959 : Blo 1905435 2859959 := bstep (se 1 (by rfl) ⟨2144969, by rfl⟩ : syracuseStep 2859959 = 4289939) B4289939
theorem B1906639 : Blo 1905435 1906639 := bstep (se 1 (by rfl) ⟨1429979, by rfl⟩ : syracuseStep 1906639 = 2859959) B2859959
theorem B2859965 : Blo 1905435 2859965 := bbase (se 3 (by rfl) ⟨536243, by rfl⟩ : syracuseStep 2859965 = 1072487) (by norm_num)
theorem B1906643 : Blo 1905435 1906643 := bstep (se 1 (by rfl) ⟨1429982, by rfl⟩ : syracuseStep 1906643 = 2859965) B2859965
theorem B4289957 : Blo 1905435 4289957 := bbase (se 4 (by rfl) ⟨402183, by rfl⟩ : syracuseStep 4289957 = 804367) (by norm_num)
theorem B2859971 : Blo 1905435 2859971 := bstep (se 1 (by rfl) ⟨2144978, by rfl⟩ : syracuseStep 2859971 = 4289957) B4289957
theorem B1906647 : Blo 1905435 1906647 := bstep (se 1 (by rfl) ⟨1429985, by rfl⟩ : syracuseStep 1906647 = 2859971) B2859971
theorem B4826213 : Blo 1905435 4826213 := bbase (se 4 (by rfl) ⟨452457, by rfl⟩ : syracuseStep 4826213 = 904915) (by norm_num)
theorem B3217475 : Blo 1905435 3217475 := bstep (se 1 (by rfl) ⟨2413106, by rfl⟩ : syracuseStep 3217475 = 4826213) B4826213
theorem B2144983 : Blo 1905435 2144983 := bstep (se 1 (by rfl) ⟨1608737, by rfl⟩ : syracuseStep 2144983 = 3217475) B3217475
theorem B2859977 : Blo 1905435 2859977 := bstep (se 2 (by rfl) ⟨1072491, by rfl⟩ : syracuseStep 2859977 = 2144983) B2144983
theorem B1906651 : Blo 1905435 1906651 := bstep (se 1 (by rfl) ⟨1429988, by rfl⟩ : syracuseStep 1906651 = 2859977) B2859977
theorem B10307573 : Blo 1905435 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B6871715 : Blo 1905435 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B4581143 : Blo 1905435 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B3054095 : Blo 1905435 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B2036063 : Blo 1905435 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B5429501 : Blo 1905435 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B3619667 : Blo 1905435 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B9652445 : Blo 1905435 9652445 := bstep (se 3 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 9652445 = 3619667) B3619667
theorem B6434963 : Blo 1905435 6434963 := bstep (se 1 (by rfl) ⟨4826222, by rfl⟩ : syracuseStep 6434963 = 9652445) B9652445
theorem B4289975 : Blo 1905435 4289975 := bstep (se 1 (by rfl) ⟨3217481, by rfl⟩ : syracuseStep 4289975 = 6434963) B6434963
theorem B2859983 : Blo 1905435 2859983 := bstep (se 1 (by rfl) ⟨2144987, by rfl⟩ : syracuseStep 2859983 = 4289975) B4289975
theorem B1906655 : Blo 1905435 1906655 := bstep (se 1 (by rfl) ⟨1429991, by rfl⟩ : syracuseStep 1906655 = 2859983) B2859983
theorem B2859989 : Blo 1905435 2859989 := bbase (se 7 (by rfl) ⟨33515, by rfl⟩ : syracuseStep 2859989 = 67031) (by norm_num)
theorem B1906659 : Blo 1905435 1906659 := bstep (se 1 (by rfl) ⟨1429994, by rfl⟩ : syracuseStep 1906659 = 2859989) B2859989
theorem B7239365 : Blo 1905435 7239365 := bbase (se 4 (by rfl) ⟨678690, by rfl⟩ : syracuseStep 7239365 = 1357381) (by norm_num)
theorem B4826243 : Blo 1905435 4826243 := bstep (se 1 (by rfl) ⟨3619682, by rfl⟩ : syracuseStep 4826243 = 7239365) B7239365
theorem B3217495 : Blo 1905435 3217495 := bstep (se 1 (by rfl) ⟨2413121, by rfl⟩ : syracuseStep 3217495 = 4826243) B4826243
theorem B4289993 : Blo 1905435 4289993 := bstep (se 2 (by rfl) ⟨1608747, by rfl⟩ : syracuseStep 4289993 = 3217495) B3217495
theorem B2859995 : Blo 1905435 2859995 := bstep (se 1 (by rfl) ⟨2144996, by rfl⟩ : syracuseStep 2859995 = 4289993) B4289993
theorem B1906663 : Blo 1905435 1906663 := bstep (se 1 (by rfl) ⟨1429997, by rfl⟩ : syracuseStep 1906663 = 2859995) B2859995
theorem B2145001 : Blo 1905435 2145001 := bbase (se 2 (by rfl) ⟨804375, by rfl⟩ : syracuseStep 2145001 = 1608751) (by norm_num)
theorem B2860001 : Blo 1905435 2860001 := bstep (se 2 (by rfl) ⟨1072500, by rfl⟩ : syracuseStep 2860001 = 2145001) B2145001
theorem B1906667 : Blo 1905435 1906667 := bstep (se 1 (by rfl) ⟨1430000, by rfl⟩ : syracuseStep 1906667 = 2860001) B2860001
theorem B10859093 : Blo 1905435 10859093 := bbase (se 8 (by rfl) ⟨63627, by rfl⟩ : syracuseStep 10859093 = 127255) (by norm_num)
theorem B7239395 : Blo 1905435 7239395 := bstep (se 1 (by rfl) ⟨5429546, by rfl⟩ : syracuseStep 7239395 = 10859093) B10859093
theorem B4826263 : Blo 1905435 4826263 := bstep (se 1 (by rfl) ⟨3619697, by rfl⟩ : syracuseStep 4826263 = 7239395) B7239395
theorem B6435017 : Blo 1905435 6435017 := bstep (se 2 (by rfl) ⟨2413131, by rfl⟩ : syracuseStep 6435017 = 4826263) B4826263
theorem B4290011 : Blo 1905435 4290011 := bstep (se 1 (by rfl) ⟨3217508, by rfl⟩ : syracuseStep 4290011 = 6435017) B6435017
theorem B2860007 : Blo 1905435 2860007 := bstep (se 1 (by rfl) ⟨2145005, by rfl⟩ : syracuseStep 2860007 = 4290011) B4290011
theorem B1906671 : Blo 1905435 1906671 := bstep (se 1 (by rfl) ⟨1430003, by rfl⟩ : syracuseStep 1906671 = 2860007) B2860007
theorem B2860013 : Blo 1905435 2860013 := bbase (se 3 (by rfl) ⟨536252, by rfl⟩ : syracuseStep 2860013 = 1072505) (by norm_num)
theorem B1906675 : Blo 1905435 1906675 := bstep (se 1 (by rfl) ⟨1430006, by rfl⟩ : syracuseStep 1906675 = 2860013) B2860013
theorem B4290029 : Blo 1905435 4290029 := bbase (se 3 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 4290029 = 1608761) (by norm_num)
theorem B2860019 : Blo 1905435 2860019 := bstep (se 1 (by rfl) ⟨2145014, by rfl⟩ : syracuseStep 2860019 = 4290029) B4290029
theorem B1906679 : Blo 1905435 1906679 := bstep (se 1 (by rfl) ⟨1430009, by rfl⟩ : syracuseStep 1906679 = 2860019) B2860019
theorem B5224181 : Blo 1905435 5224181 := bbase (se 5 (by rfl) ⟨244883, by rfl⟩ : syracuseStep 5224181 = 489767) (by norm_num)
theorem B13931149 : Blo 1905435 13931149 := bstep (se 3 (by rfl) ⟨2612090, by rfl⟩ : syracuseStep 13931149 = 5224181) B5224181
theorem B18574865 : Blo 1905435 18574865 := bstep (se 2 (by rfl) ⟨6965574, by rfl⟩ : syracuseStep 18574865 = 13931149) B13931149
theorem B12383243 : Blo 1905435 12383243 := bstep (se 1 (by rfl) ⟨9287432, by rfl⟩ : syracuseStep 12383243 = 18574865) B18574865
theorem B8255495 : Blo 1905435 8255495 := bstep (se 1 (by rfl) ⟨6191621, by rfl⟩ : syracuseStep 8255495 = 12383243) B12383243
theorem B5503663 : Blo 1905435 5503663 := bstep (se 1 (by rfl) ⟨4127747, by rfl⟩ : syracuseStep 5503663 = 8255495) B8255495
theorem B7338217 : Blo 1905435 7338217 := bstep (se 2 (by rfl) ⟨2751831, by rfl⟩ : syracuseStep 7338217 = 5503663) B5503663
theorem B9784289 : Blo 1905435 9784289 := bstep (se 2 (by rfl) ⟨3669108, by rfl⟩ : syracuseStep 9784289 = 7338217) B7338217
theorem B6522859 : Blo 1905435 6522859 := bstep (se 1 (by rfl) ⟨4892144, by rfl⟩ : syracuseStep 6522859 = 9784289) B9784289
theorem B8697145 : Blo 1905435 8697145 := bstep (se 2 (by rfl) ⟨3261429, by rfl⟩ : syracuseStep 8697145 = 6522859) B6522859
theorem B11596193 : Blo 1905435 11596193 := bstep (se 2 (by rfl) ⟨4348572, by rfl⟩ : syracuseStep 11596193 = 8697145) B8697145
theorem B7730795 : Blo 1905435 7730795 := bstep (se 1 (by rfl) ⟨5798096, by rfl⟩ : syracuseStep 7730795 = 11596193) B11596193
theorem B5153863 : Blo 1905435 5153863 := bstep (se 1 (by rfl) ⟨3865397, by rfl⟩ : syracuseStep 5153863 = 7730795) B7730795
theorem B6871817 : Blo 1905435 6871817 := bstep (se 2 (by rfl) ⟨2576931, by rfl⟩ : syracuseStep 6871817 = 5153863) B5153863
theorem B4581211 : Blo 1905435 4581211 := bstep (se 1 (by rfl) ⟨3435908, by rfl⟩ : syracuseStep 4581211 = 6871817) B6871817
theorem B6108281 : Blo 1905435 6108281 := bstep (se 2 (by rfl) ⟨2290605, by rfl⟩ : syracuseStep 6108281 = 4581211) B4581211
theorem B4072187 : Blo 1905435 4072187 := bstep (se 1 (by rfl) ⟨3054140, by rfl⟩ : syracuseStep 4072187 = 6108281) B6108281
theorem B2714791 : Blo 1905435 2714791 := bstep (se 1 (by rfl) ⟨2036093, by rfl⟩ : syracuseStep 2714791 = 4072187) B4072187
theorem B3619721 : Blo 1905435 3619721 := bstep (se 2 (by rfl) ⟨1357395, by rfl⟩ : syracuseStep 3619721 = 2714791) B2714791
theorem B2413147 : Blo 1905435 2413147 := bstep (se 1 (by rfl) ⟨1809860, by rfl⟩ : syracuseStep 2413147 = 3619721) B3619721
theorem B3217529 : Blo 1905435 3217529 := bstep (se 2 (by rfl) ⟨1206573, by rfl⟩ : syracuseStep 3217529 = 2413147) B2413147
theorem B2145019 : Blo 1905435 2145019 := bstep (se 1 (by rfl) ⟨1608764, by rfl⟩ : syracuseStep 2145019 = 3217529) B3217529
theorem B2860025 : Blo 1905435 2860025 := bstep (se 2 (by rfl) ⟨1072509, by rfl⟩ : syracuseStep 2860025 = 2145019) B2145019
theorem B1906683 : Blo 1905435 1906683 := bstep (se 1 (by rfl) ⟨1430012, by rfl⟩ : syracuseStep 1906683 = 2860025) B2860025
theorem B6522869 : Blo 1905435 6522869 := bbase (se 5 (by rfl) ⟨305759, by rfl⟩ : syracuseStep 6522869 = 611519) (by norm_num)
theorem B4348579 : Blo 1905435 4348579 := bstep (se 1 (by rfl) ⟨3261434, by rfl⟩ : syracuseStep 4348579 = 6522869) B6522869
theorem B5798105 : Blo 1905435 5798105 := bstep (se 2 (by rfl) ⟨2174289, by rfl⟩ : syracuseStep 5798105 = 4348579) B4348579
theorem B3865403 : Blo 1905435 3865403 := bstep (se 1 (by rfl) ⟨2899052, by rfl⟩ : syracuseStep 3865403 = 5798105) B5798105
theorem B10307741 : Blo 1905435 10307741 := bstep (se 3 (by rfl) ⟨1932701, by rfl⟩ : syracuseStep 10307741 = 3865403) B3865403
theorem B109949237 : Blo 1905435 109949237 := bstep (se 5 (by rfl) ⟨5153870, by rfl⟩ : syracuseStep 109949237 = 10307741) B10307741
theorem B73299491 : Blo 1905435 73299491 := bstep (se 1 (by rfl) ⟨54974618, by rfl⟩ : syracuseStep 73299491 = 109949237) B109949237
theorem B48866327 : Blo 1905435 48866327 := bstep (se 1 (by rfl) ⟨36649745, by rfl⟩ : syracuseStep 48866327 = 73299491) B73299491
theorem B32577551 : Blo 1905435 32577551 := bstep (se 1 (by rfl) ⟨24433163, by rfl⟩ : syracuseStep 32577551 = 48866327) B48866327
theorem B21718367 : Blo 1905435 21718367 := bstep (se 1 (by rfl) ⟨16288775, by rfl⟩ : syracuseStep 21718367 = 32577551) B32577551
theorem B14478911 : Blo 1905435 14478911 := bstep (se 1 (by rfl) ⟨10859183, by rfl⟩ : syracuseStep 14478911 = 21718367) B21718367
theorem B9652607 : Blo 1905435 9652607 := bstep (se 1 (by rfl) ⟨7239455, by rfl⟩ : syracuseStep 9652607 = 14478911) B14478911
theorem B6435071 : Blo 1905435 6435071 := bstep (se 1 (by rfl) ⟨4826303, by rfl⟩ : syracuseStep 6435071 = 9652607) B9652607
theorem B4290047 : Blo 1905435 4290047 := bstep (se 1 (by rfl) ⟨3217535, by rfl⟩ : syracuseStep 4290047 = 6435071) B6435071
theorem B2860031 : Blo 1905435 2860031 := bstep (se 1 (by rfl) ⟨2145023, by rfl⟩ : syracuseStep 2860031 = 4290047) B4290047
theorem B1906687 : Blo 1905435 1906687 := bstep (se 1 (by rfl) ⟨1430015, by rfl⟩ : syracuseStep 1906687 = 2860031) B2860031
theorem B2860037 : Blo 1905435 2860037 := bbase (se 4 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 2860037 = 536257) (by norm_num)
theorem B1906691 : Blo 1905435 1906691 := bstep (se 1 (by rfl) ⟨1430018, by rfl⟩ : syracuseStep 1906691 = 2860037) B2860037
theorem B3217549 : Blo 1905435 3217549 := bbase (se 3 (by rfl) ⟨603290, by rfl⟩ : syracuseStep 3217549 = 1206581) (by norm_num)
theorem B4290065 : Blo 1905435 4290065 := bstep (se 2 (by rfl) ⟨1608774, by rfl⟩ : syracuseStep 4290065 = 3217549) B3217549
theorem B2860043 : Blo 1905435 2860043 := bstep (se 1 (by rfl) ⟨2145032, by rfl⟩ : syracuseStep 2860043 = 4290065) B4290065
theorem B1906695 : Blo 1905435 1906695 := bstep (se 1 (by rfl) ⟨1430021, by rfl⟩ : syracuseStep 1906695 = 2860043) B2860043
theorem B2145037 : Blo 1905435 2145037 := bbase (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) (by norm_num)
theorem B2860049 : Blo 1905435 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B1906699 : Blo 1905435 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B6435125 : Blo 1905435 6435125 := bbase (se 5 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 6435125 = 603293) (by norm_num)
theorem B4290083 : Blo 1905435 4290083 := bstep (se 1 (by rfl) ⟨3217562, by rfl⟩ : syracuseStep 4290083 = 6435125) B6435125
theorem B2860055 : Blo 1905435 2860055 := bstep (se 1 (by rfl) ⟨2145041, by rfl⟩ : syracuseStep 2860055 = 4290083) B4290083
theorem B1906703 : Blo 1905435 1906703 := bstep (se 1 (by rfl) ⟨1430027, by rfl⟩ : syracuseStep 1906703 = 2860055) B2860055
theorem B2860061 : Blo 1905435 2860061 := bbase (se 3 (by rfl) ⟨536261, by rfl⟩ : syracuseStep 2860061 = 1072523) (by norm_num)
theorem B1906707 : Blo 1905435 1906707 := bstep (se 1 (by rfl) ⟨1430030, by rfl⟩ : syracuseStep 1906707 = 2860061) B2860061
theorem B4290101 : Blo 1905435 4290101 := bbase (se 5 (by rfl) ⟨201098, by rfl⟩ : syracuseStep 4290101 = 402197) (by norm_num)
theorem B2860067 : Blo 1905435 2860067 := bstep (se 1 (by rfl) ⟨2145050, by rfl⟩ : syracuseStep 2860067 = 4290101) B4290101
theorem B1906711 : Blo 1905435 1906711 := bstep (se 1 (by rfl) ⟨1430033, by rfl⟩ : syracuseStep 1906711 = 2860067) B2860067
theorem B2751877 : Blo 1905435 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B14676677 : Blo 1905435 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B9784451 : Blo 1905435 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B6522967 : Blo 1905435 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B8697289 : Blo 1905435 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B11596385 : Blo 1905435 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B7730923 : Blo 1905435 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B10307897 : Blo 1905435 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B6871931 : Blo 1905435 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B4581287 : Blo 1905435 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B3054191 : Blo 1905435 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B8144509 : Blo 1905435 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B10859345 : Blo 1905435 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B7239563 : Blo 1905435 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B4826375 : Blo 1905435 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B3217583 : Blo 1905435 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B2145055 : Blo 1905435 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B2860073 : Blo 1905435 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B1906715 : Blo 1905435 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B3054197 : Blo 1905435 3054197 := bbase (se 5 (by rfl) ⟨143165, by rfl⟩ : syracuseStep 3054197 = 286331) (by norm_num)
theorem B8144525 : Blo 1905435 8144525 := bstep (se 3 (by rfl) ⟨1527098, by rfl⟩ : syracuseStep 8144525 = 3054197) B3054197
theorem B5429683 : Blo 1905435 5429683 := bstep (se 1 (by rfl) ⟨4072262, by rfl⟩ : syracuseStep 5429683 = 8144525) B8144525
theorem B7239577 : Blo 1905435 7239577 := bstep (se 2 (by rfl) ⟨2714841, by rfl⟩ : syracuseStep 7239577 = 5429683) B5429683
theorem B9652769 : Blo 1905435 9652769 := bstep (se 2 (by rfl) ⟨3619788, by rfl⟩ : syracuseStep 9652769 = 7239577) B7239577
theorem B6435179 : Blo 1905435 6435179 := bstep (se 1 (by rfl) ⟨4826384, by rfl⟩ : syracuseStep 6435179 = 9652769) B9652769
theorem B4290119 : Blo 1905435 4290119 := bstep (se 1 (by rfl) ⟨3217589, by rfl⟩ : syracuseStep 4290119 = 6435179) B6435179
theorem B2860079 : Blo 1905435 2860079 := bstep (se 1 (by rfl) ⟨2145059, by rfl⟩ : syracuseStep 2860079 = 4290119) B4290119
theorem B1906719 : Blo 1905435 1906719 := bstep (se 1 (by rfl) ⟨1430039, by rfl⟩ : syracuseStep 1906719 = 2860079) B2860079
theorem B2860085 : Blo 1905435 2860085 := bbase (se 5 (by rfl) ⟨134066, by rfl⟩ : syracuseStep 2860085 = 268133) (by norm_num)
theorem B1906723 : Blo 1905435 1906723 := bstep (se 1 (by rfl) ⟨1430042, by rfl⟩ : syracuseStep 1906723 = 2860085) B2860085
theorem B4826405 : Blo 1905435 4826405 := bbase (se 4 (by rfl) ⟨452475, by rfl⟩ : syracuseStep 4826405 = 904951) (by norm_num)
theorem B3217603 : Blo 1905435 3217603 := bstep (se 1 (by rfl) ⟨2413202, by rfl⟩ : syracuseStep 3217603 = 4826405) B4826405
theorem B4290137 : Blo 1905435 4290137 := bstep (se 2 (by rfl) ⟨1608801, by rfl⟩ : syracuseStep 4290137 = 3217603) B3217603
theorem B2860091 : Blo 1905435 2860091 := bstep (se 1 (by rfl) ⟨2145068, by rfl⟩ : syracuseStep 2860091 = 4290137) B4290137
theorem B1906727 : Blo 1905435 1906727 := bstep (se 1 (by rfl) ⟨1430045, by rfl⟩ : syracuseStep 1906727 = 2860091) B2860091
theorem B2145073 : Blo 1905435 2145073 := bbase (se 2 (by rfl) ⟨804402, by rfl⟩ : syracuseStep 2145073 = 1608805) (by norm_num)
theorem B2860097 : Blo 1905435 2860097 := bstep (se 2 (by rfl) ⟨1072536, by rfl⟩ : syracuseStep 2860097 = 2145073) B2145073
theorem B1906731 : Blo 1905435 1906731 := bstep (se 1 (by rfl) ⟨1430048, by rfl⟩ : syracuseStep 1906731 = 2860097) B2860097
theorem B4127861 : Blo 1905435 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B2751907 : Blo 1905435 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B3669209 : Blo 1905435 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B2446139 : Blo 1905435 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B6523037 : Blo 1905435 6523037 := bstep (se 3 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 6523037 = 2446139) B2446139
theorem B4348691 : Blo 1905435 4348691 := bstep (se 1 (by rfl) ⟨3261518, by rfl⟩ : syracuseStep 4348691 = 6523037) B6523037
theorem B2899127 : Blo 1905435 2899127 := bstep (se 1 (by rfl) ⟨2174345, by rfl⟩ : syracuseStep 2899127 = 4348691) B4348691
theorem B1932751 : Blo 1905435 1932751 := bstep (se 1 (by rfl) ⟨1449563, by rfl⟩ : syracuseStep 1932751 = 2899127) B2899127
theorem B10308005 : Blo 1905435 10308005 := bstep (se 4 (by rfl) ⟨966375, by rfl⟩ : syracuseStep 10308005 = 1932751) B1932751
theorem B6872003 : Blo 1905435 6872003 := bstep (se 1 (by rfl) ⟨5154002, by rfl⟩ : syracuseStep 6872003 = 10308005) B10308005
theorem B4581335 : Blo 1905435 4581335 := bstep (se 1 (by rfl) ⟨3436001, by rfl⟩ : syracuseStep 4581335 = 6872003) B6872003
theorem B3054223 : Blo 1905435 3054223 := bstep (se 1 (by rfl) ⟨2290667, by rfl⟩ : syracuseStep 3054223 = 4581335) B4581335
theorem B4072297 : Blo 1905435 4072297 := bstep (se 2 (by rfl) ⟨1527111, by rfl⟩ : syracuseStep 4072297 = 3054223) B3054223
theorem B5429729 : Blo 1905435 5429729 := bstep (se 2 (by rfl) ⟨2036148, by rfl⟩ : syracuseStep 5429729 = 4072297) B4072297
theorem B3619819 : Blo 1905435 3619819 := bstep (se 1 (by rfl) ⟨2714864, by rfl⟩ : syracuseStep 3619819 = 5429729) B5429729
theorem B4826425 : Blo 1905435 4826425 := bstep (se 2 (by rfl) ⟨1809909, by rfl⟩ : syracuseStep 4826425 = 3619819) B3619819
theorem B6435233 : Blo 1905435 6435233 := bstep (se 2 (by rfl) ⟨2413212, by rfl⟩ : syracuseStep 6435233 = 4826425) B4826425
theorem B4290155 : Blo 1905435 4290155 := bstep (se 1 (by rfl) ⟨3217616, by rfl⟩ : syracuseStep 4290155 = 6435233) B6435233
theorem B2860103 : Blo 1905435 2860103 := bstep (se 1 (by rfl) ⟨2145077, by rfl⟩ : syracuseStep 2860103 = 4290155) B4290155
theorem B1906735 : Blo 1905435 1906735 := bstep (se 1 (by rfl) ⟨1430051, by rfl⟩ : syracuseStep 1906735 = 2860103) B2860103
theorem B2860109 : Blo 1905435 2860109 := bbase (se 3 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 2860109 = 1072541) (by norm_num)
theorem B1906739 : Blo 1905435 1906739 := bstep (se 1 (by rfl) ⟨1430054, by rfl⟩ : syracuseStep 1906739 = 2860109) B2860109
theorem B4290173 : Blo 1905435 4290173 := bbase (se 3 (by rfl) ⟨804407, by rfl⟩ : syracuseStep 4290173 = 1608815) (by norm_num)
theorem B2860115 : Blo 1905435 2860115 := bstep (se 1 (by rfl) ⟨2145086, by rfl⟩ : syracuseStep 2860115 = 4290173) B4290173
theorem B1906743 : Blo 1905435 1906743 := bstep (se 1 (by rfl) ⟨1430057, by rfl⟩ : syracuseStep 1906743 = 2860115) B2860115
theorem B3217637 : Blo 1905435 3217637 := bbase (se 4 (by rfl) ⟨301653, by rfl⟩ : syracuseStep 3217637 = 603307) (by norm_num)
theorem B2145091 : Blo 1905435 2145091 := bstep (se 1 (by rfl) ⟨1608818, by rfl⟩ : syracuseStep 2145091 = 3217637) B3217637
theorem B2860121 : Blo 1905435 2860121 := bstep (se 2 (by rfl) ⟨1072545, by rfl⟩ : syracuseStep 2860121 = 2145091) B2145091
theorem B1906747 : Blo 1905435 1906747 := bstep (se 1 (by rfl) ⟨1430060, by rfl⟩ : syracuseStep 1906747 = 2860121) B2860121
theorem B4581373 : Blo 1905435 4581373 := bbase (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) (by norm_num)
theorem B6108497 : Blo 1905435 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B4072331 : Blo 1905435 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B2714887 : Blo 1905435 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B14479397 : Blo 1905435 14479397 := bstep (se 4 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 14479397 = 2714887) B2714887
theorem B9652931 : Blo 1905435 9652931 := bstep (se 1 (by rfl) ⟨7239698, by rfl⟩ : syracuseStep 9652931 = 14479397) B14479397
theorem B6435287 : Blo 1905435 6435287 := bstep (se 1 (by rfl) ⟨4826465, by rfl⟩ : syracuseStep 6435287 = 9652931) B9652931
theorem B4290191 : Blo 1905435 4290191 := bstep (se 1 (by rfl) ⟨3217643, by rfl⟩ : syracuseStep 4290191 = 6435287) B6435287
theorem B2860127 : Blo 1905435 2860127 := bstep (se 1 (by rfl) ⟨2145095, by rfl⟩ : syracuseStep 2860127 = 4290191) B4290191
theorem B1906751 : Blo 1905435 1906751 := bstep (se 1 (by rfl) ⟨1430063, by rfl⟩ : syracuseStep 1906751 = 2860127) B2860127
theorem B2860133 : Blo 1905435 2860133 := bbase (se 4 (by rfl) ⟨268137, by rfl⟩ : syracuseStep 2860133 = 536275) (by norm_num)
theorem B1906755 : Blo 1905435 1906755 := bstep (se 1 (by rfl) ⟨1430066, by rfl⟩ : syracuseStep 1906755 = 2860133) B2860133
theorem B4072349 : Blo 1905435 4072349 := bbase (se 3 (by rfl) ⟨763565, by rfl⟩ : syracuseStep 4072349 = 1527131) (by norm_num)
theorem B2714899 : Blo 1905435 2714899 := bstep (se 1 (by rfl) ⟨2036174, by rfl⟩ : syracuseStep 2714899 = 4072349) B4072349
theorem B3619865 : Blo 1905435 3619865 := bstep (se 2 (by rfl) ⟨1357449, by rfl⟩ : syracuseStep 3619865 = 2714899) B2714899
theorem B2413243 : Blo 1905435 2413243 := bstep (se 1 (by rfl) ⟨1809932, by rfl⟩ : syracuseStep 2413243 = 3619865) B3619865
theorem B3217657 : Blo 1905435 3217657 := bstep (se 2 (by rfl) ⟨1206621, by rfl⟩ : syracuseStep 3217657 = 2413243) B2413243
theorem B4290209 : Blo 1905435 4290209 := bstep (se 2 (by rfl) ⟨1608828, by rfl⟩ : syracuseStep 4290209 = 3217657) B3217657
theorem B2860139 : Blo 1905435 2860139 := bstep (se 1 (by rfl) ⟨2145104, by rfl⟩ : syracuseStep 2860139 = 4290209) B4290209
theorem B1906759 : Blo 1905435 1906759 := bstep (se 1 (by rfl) ⟨1430069, by rfl⟩ : syracuseStep 1906759 = 2860139) B2860139
theorem B2145109 : Blo 1905435 2145109 := bbase (se 9 (by rfl) ⟨6284, by rfl⟩ : syracuseStep 2145109 = 12569) (by norm_num)
theorem B2860145 : Blo 1905435 2860145 := bstep (se 2 (by rfl) ⟨1072554, by rfl⟩ : syracuseStep 2860145 = 2145109) B2145109
theorem B1906763 : Blo 1905435 1906763 := bstep (se 1 (by rfl) ⟨1430072, by rfl⟩ : syracuseStep 1906763 = 2860145) B2860145
theorem B2413253 : Blo 1905435 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B6435341 : Blo 1905435 6435341 := bstep (se 3 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 6435341 = 2413253) B2413253
theorem B4290227 : Blo 1905435 4290227 := bstep (se 1 (by rfl) ⟨3217670, by rfl⟩ : syracuseStep 4290227 = 6435341) B6435341
theorem B2860151 : Blo 1905435 2860151 := bstep (se 1 (by rfl) ⟨2145113, by rfl⟩ : syracuseStep 2860151 = 4290227) B4290227
theorem B1906767 : Blo 1905435 1906767 := bstep (se 1 (by rfl) ⟨1430075, by rfl⟩ : syracuseStep 1906767 = 2860151) B2860151
theorem B2860157 : Blo 1905435 2860157 := bbase (se 3 (by rfl) ⟨536279, by rfl⟩ : syracuseStep 2860157 = 1072559) (by norm_num)
theorem B1906771 : Blo 1905435 1906771 := bstep (se 1 (by rfl) ⟨1430078, by rfl⟩ : syracuseStep 1906771 = 2860157) B2860157
theorem B4290245 : Blo 1905435 4290245 := bbase (se 4 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 4290245 = 804421) (by norm_num)
theorem B2860163 : Blo 1905435 2860163 := bstep (se 1 (by rfl) ⟨2145122, by rfl⟩ : syracuseStep 2860163 = 4290245) B4290245
theorem B1906775 : Blo 1905435 1906775 := bstep (se 1 (by rfl) ⟨1430081, by rfl⟩ : syracuseStep 1906775 = 2860163) B2860163
theorem B3669293 : Blo 1905435 3669293 := bbase (se 3 (by rfl) ⟨687992, by rfl⟩ : syracuseStep 3669293 = 1375985) (by norm_num)
theorem B2446195 : Blo 1905435 2446195 := bstep (se 1 (by rfl) ⟨1834646, by rfl⟩ : syracuseStep 2446195 = 3669293) B3669293
theorem B3261593 : Blo 1905435 3261593 := bstep (se 2 (by rfl) ⟨1223097, by rfl⟩ : syracuseStep 3261593 = 2446195) B2446195
theorem B8697581 : Blo 1905435 8697581 := bstep (se 3 (by rfl) ⟨1630796, by rfl⟩ : syracuseStep 8697581 = 3261593) B3261593
theorem B5798387 : Blo 1905435 5798387 := bstep (se 1 (by rfl) ⟨4348790, by rfl⟩ : syracuseStep 5798387 = 8697581) B8697581
theorem B3865591 : Blo 1905435 3865591 := bstep (se 1 (by rfl) ⟨2899193, by rfl⟩ : syracuseStep 3865591 = 5798387) B5798387
theorem B5154121 : Blo 1905435 5154121 := bstep (se 2 (by rfl) ⟨1932795, by rfl⟩ : syracuseStep 5154121 = 3865591) B3865591
theorem B27488645 : Blo 1905435 27488645 := bstep (se 4 (by rfl) ⟨2577060, by rfl⟩ : syracuseStep 27488645 = 5154121) B5154121
theorem B18325763 : Blo 1905435 18325763 := bstep (se 1 (by rfl) ⟨13744322, by rfl⟩ : syracuseStep 18325763 = 27488645) B27488645
theorem B12217175 : Blo 1905435 12217175 := bstep (se 1 (by rfl) ⟨9162881, by rfl⟩ : syracuseStep 12217175 = 18325763) B18325763
theorem B8144783 : Blo 1905435 8144783 := bstep (se 1 (by rfl) ⟨6108587, by rfl⟩ : syracuseStep 8144783 = 12217175) B12217175
theorem B5429855 : Blo 1905435 5429855 := bstep (se 1 (by rfl) ⟨4072391, by rfl⟩ : syracuseStep 5429855 = 8144783) B8144783
theorem B3619903 : Blo 1905435 3619903 := bstep (se 1 (by rfl) ⟨2714927, by rfl⟩ : syracuseStep 3619903 = 5429855) B5429855
theorem B4826537 : Blo 1905435 4826537 := bstep (se 2 (by rfl) ⟨1809951, by rfl⟩ : syracuseStep 4826537 = 3619903) B3619903
theorem B3217691 : Blo 1905435 3217691 := bstep (se 1 (by rfl) ⟨2413268, by rfl⟩ : syracuseStep 3217691 = 4826537) B4826537
theorem B2145127 : Blo 1905435 2145127 := bstep (se 1 (by rfl) ⟨1608845, by rfl⟩ : syracuseStep 2145127 = 3217691) B3217691
theorem B2860169 : Blo 1905435 2860169 := bstep (se 2 (by rfl) ⟨1072563, by rfl⟩ : syracuseStep 2860169 = 2145127) B2145127
theorem B1906779 : Blo 1905435 1906779 := bstep (se 1 (by rfl) ⟨1430084, by rfl⟩ : syracuseStep 1906779 = 2860169) B2860169
theorem B9653093 : Blo 1905435 9653093 := bbase (se 4 (by rfl) ⟨904977, by rfl⟩ : syracuseStep 9653093 = 1809955) (by norm_num)
theorem B6435395 : Blo 1905435 6435395 := bstep (se 1 (by rfl) ⟨4826546, by rfl⟩ : syracuseStep 6435395 = 9653093) B9653093
theorem B4290263 : Blo 1905435 4290263 := bstep (se 1 (by rfl) ⟨3217697, by rfl⟩ : syracuseStep 4290263 = 6435395) B6435395
theorem B2860175 : Blo 1905435 2860175 := bstep (se 1 (by rfl) ⟨2145131, by rfl⟩ : syracuseStep 2860175 = 4290263) B4290263
theorem B1906783 : Blo 1905435 1906783 := bstep (se 1 (by rfl) ⟨1430087, by rfl⟩ : syracuseStep 1906783 = 2860175) B2860175
theorem B2860181 : Blo 1905435 2860181 := bbase (se 6 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 2860181 = 134071) (by norm_num)
theorem B1906787 : Blo 1905435 1906787 := bstep (se 1 (by rfl) ⟨1430090, by rfl⟩ : syracuseStep 1906787 = 2860181) B2860181
theorem B4581469 : Blo 1905435 4581469 := bbase (se 3 (by rfl) ⟨859025, by rfl⟩ : syracuseStep 4581469 = 1718051) (by norm_num)
theorem B6108625 : Blo 1905435 6108625 := bstep (se 2 (by rfl) ⟨2290734, by rfl⟩ : syracuseStep 6108625 = 4581469) B4581469
theorem B8144833 : Blo 1905435 8144833 := bstep (se 2 (by rfl) ⟨3054312, by rfl⟩ : syracuseStep 8144833 = 6108625) B6108625
theorem B10859777 : Blo 1905435 10859777 := bstep (se 2 (by rfl) ⟨4072416, by rfl⟩ : syracuseStep 10859777 = 8144833) B8144833
theorem B7239851 : Blo 1905435 7239851 := bstep (se 1 (by rfl) ⟨5429888, by rfl⟩ : syracuseStep 7239851 = 10859777) B10859777
theorem B4826567 : Blo 1905435 4826567 := bstep (se 1 (by rfl) ⟨3619925, by rfl⟩ : syracuseStep 4826567 = 7239851) B7239851
theorem B3217711 : Blo 1905435 3217711 := bstep (se 1 (by rfl) ⟨2413283, by rfl⟩ : syracuseStep 3217711 = 4826567) B4826567
theorem B4290281 : Blo 1905435 4290281 := bstep (se 2 (by rfl) ⟨1608855, by rfl⟩ : syracuseStep 4290281 = 3217711) B3217711
theorem B2860187 : Blo 1905435 2860187 := bstep (se 1 (by rfl) ⟨2145140, by rfl⟩ : syracuseStep 2860187 = 4290281) B4290281
theorem B1906791 : Blo 1905435 1906791 := bstep (se 1 (by rfl) ⟨1430093, by rfl⟩ : syracuseStep 1906791 = 2860187) B2860187
theorem B2145145 : Blo 1905435 2145145 := bbase (se 2 (by rfl) ⟨804429, by rfl⟩ : syracuseStep 2145145 = 1608859) (by norm_num)
theorem B2860193 : Blo 1905435 2860193 := bstep (se 2 (by rfl) ⟨1072572, by rfl⟩ : syracuseStep 2860193 = 2145145) B2145145
theorem B1906795 : Blo 1905435 1906795 := bstep (se 1 (by rfl) ⟨1430096, by rfl⟩ : syracuseStep 1906795 = 2860193) B2860193
theorem B12217301 : Blo 1905435 12217301 := bbase (se 7 (by rfl) ⟨143171, by rfl⟩ : syracuseStep 12217301 = 286343) (by norm_num)
theorem B8144867 : Blo 1905435 8144867 := bstep (se 1 (by rfl) ⟨6108650, by rfl⟩ : syracuseStep 8144867 = 12217301) B12217301
theorem B5429911 : Blo 1905435 5429911 := bstep (se 1 (by rfl) ⟨4072433, by rfl⟩ : syracuseStep 5429911 = 8144867) B8144867
theorem B7239881 : Blo 1905435 7239881 := bstep (se 2 (by rfl) ⟨2714955, by rfl⟩ : syracuseStep 7239881 = 5429911) B5429911
theorem B4826587 : Blo 1905435 4826587 := bstep (se 1 (by rfl) ⟨3619940, by rfl⟩ : syracuseStep 4826587 = 7239881) B7239881
theorem B6435449 : Blo 1905435 6435449 := bstep (se 2 (by rfl) ⟨2413293, by rfl⟩ : syracuseStep 6435449 = 4826587) B4826587
theorem B4290299 : Blo 1905435 4290299 := bstep (se 1 (by rfl) ⟨3217724, by rfl⟩ : syracuseStep 4290299 = 6435449) B6435449
theorem B2860199 : Blo 1905435 2860199 := bstep (se 1 (by rfl) ⟨2145149, by rfl⟩ : syracuseStep 2860199 = 4290299) B4290299
theorem B1906799 : Blo 1905435 1906799 := bstep (se 1 (by rfl) ⟨1430099, by rfl⟩ : syracuseStep 1906799 = 2860199) B2860199
theorem B2860205 : Blo 1905435 2860205 := bbase (se 3 (by rfl) ⟨536288, by rfl⟩ : syracuseStep 2860205 = 1072577) (by norm_num)
theorem B1906803 : Blo 1905435 1906803 := bstep (se 1 (by rfl) ⟨1430102, by rfl⟩ : syracuseStep 1906803 = 2860205) B2860205
theorem B4290317 : Blo 1905435 4290317 := bbase (se 3 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 4290317 = 1608869) (by norm_num)
theorem B2860211 : Blo 1905435 2860211 := bstep (se 1 (by rfl) ⟨2145158, by rfl⟩ : syracuseStep 2860211 = 4290317) B4290317
theorem B1906807 : Blo 1905435 1906807 := bstep (se 1 (by rfl) ⟨1430105, by rfl⟩ : syracuseStep 1906807 = 2860211) B2860211
theorem B2413309 : Blo 1905435 2413309 := bbase (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) (by norm_num)
theorem B3217745 : Blo 1905435 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B2145163 : Blo 1905435 2145163 := bstep (se 1 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 2145163 = 3217745) B3217745
theorem B2860217 : Blo 1905435 2860217 := bstep (se 2 (by rfl) ⟨1072581, by rfl⟩ : syracuseStep 2860217 = 2145163) B2145163
theorem B1906811 : Blo 1905435 1906811 := bstep (se 1 (by rfl) ⟨1430108, by rfl⟩ : syracuseStep 1906811 = 2860217) B2860217
theorem B2577109 : Blo 1905435 2577109 := bbase (se 7 (by rfl) ⟨30200, by rfl⟩ : syracuseStep 2577109 = 60401) (by norm_num)
theorem B3436145 : Blo 1905435 3436145 := bstep (se 2 (by rfl) ⟨1288554, by rfl⟩ : syracuseStep 3436145 = 2577109) B2577109
theorem B2290763 : Blo 1905435 2290763 := bstep (se 1 (by rfl) ⟨1718072, by rfl⟩ : syracuseStep 2290763 = 3436145) B3436145
theorem B6108701 : Blo 1905435 6108701 := bstep (se 3 (by rfl) ⟨1145381, by rfl⟩ : syracuseStep 6108701 = 2290763) B2290763
theorem B16289869 : Blo 1905435 16289869 := bstep (se 3 (by rfl) ⟨3054350, by rfl⟩ : syracuseStep 16289869 = 6108701) B6108701
theorem B21719825 : Blo 1905435 21719825 := bstep (se 2 (by rfl) ⟨8144934, by rfl⟩ : syracuseStep 21719825 = 16289869) B16289869
theorem B14479883 : Blo 1905435 14479883 := bstep (se 1 (by rfl) ⟨10859912, by rfl⟩ : syracuseStep 14479883 = 21719825) B21719825
theorem B9653255 : Blo 1905435 9653255 := bstep (se 1 (by rfl) ⟨7239941, by rfl⟩ : syracuseStep 9653255 = 14479883) B14479883
theorem B6435503 : Blo 1905435 6435503 := bstep (se 1 (by rfl) ⟨4826627, by rfl⟩ : syracuseStep 6435503 = 9653255) B9653255
theorem B4290335 : Blo 1905435 4290335 := bstep (se 1 (by rfl) ⟨3217751, by rfl⟩ : syracuseStep 4290335 = 6435503) B6435503
theorem B2860223 : Blo 1905435 2860223 := bstep (se 1 (by rfl) ⟨2145167, by rfl⟩ : syracuseStep 2860223 = 4290335) B4290335
theorem B1906815 : Blo 1905435 1906815 := bstep (se 1 (by rfl) ⟨1430111, by rfl⟩ : syracuseStep 1906815 = 2860223) B2860223
theorem B2860229 : Blo 1905435 2860229 := bbase (se 4 (by rfl) ⟨268146, by rfl⟩ : syracuseStep 2860229 = 536293) (by norm_num)
theorem B1906819 : Blo 1905435 1906819 := bstep (se 1 (by rfl) ⟨1430114, by rfl⟩ : syracuseStep 1906819 = 2860229) B2860229
theorem B3217765 : Blo 1905435 3217765 := bbase (se 4 (by rfl) ⟨301665, by rfl⟩ : syracuseStep 3217765 = 603331) (by norm_num)
theorem B4290353 : Blo 1905435 4290353 := bstep (se 2 (by rfl) ⟨1608882, by rfl⟩ : syracuseStep 4290353 = 3217765) B3217765
theorem B2860235 : Blo 1905435 2860235 := bstep (se 1 (by rfl) ⟨2145176, by rfl⟩ : syracuseStep 2860235 = 4290353) B4290353
theorem B1906823 : Blo 1905435 1906823 := bstep (se 1 (by rfl) ⟨1430117, by rfl⟩ : syracuseStep 1906823 = 2860235) B2860235
theorem B2145181 : Blo 1905435 2145181 := bbase (se 3 (by rfl) ⟨402221, by rfl⟩ : syracuseStep 2145181 = 804443) (by norm_num)
theorem B2860241 : Blo 1905435 2860241 := bstep (se 2 (by rfl) ⟨1072590, by rfl⟩ : syracuseStep 2860241 = 2145181) B2145181
theorem B1906827 : Blo 1905435 1906827 := bstep (se 1 (by rfl) ⟨1430120, by rfl⟩ : syracuseStep 1906827 = 2860241) B2860241
theorem B6435557 : Blo 1905435 6435557 := bbase (se 4 (by rfl) ⟨603333, by rfl⟩ : syracuseStep 6435557 = 1206667) (by norm_num)
theorem B4290371 : Blo 1905435 4290371 := bstep (se 1 (by rfl) ⟨3217778, by rfl⟩ : syracuseStep 4290371 = 6435557) B6435557
theorem B2860247 : Blo 1905435 2860247 := bstep (se 1 (by rfl) ⟨2145185, by rfl⟩ : syracuseStep 2860247 = 4290371) B4290371
theorem B1906831 : Blo 1905435 1906831 := bstep (se 1 (by rfl) ⟨1430123, by rfl⟩ : syracuseStep 1906831 = 2860247) B2860247
theorem B2860253 : Blo 1905435 2860253 := bbase (se 3 (by rfl) ⟨536297, by rfl⟩ : syracuseStep 2860253 = 1072595) (by norm_num)
theorem B1906835 : Blo 1905435 1906835 := bstep (se 1 (by rfl) ⟨1430126, by rfl⟩ : syracuseStep 1906835 = 2860253) B2860253
theorem B4290389 : Blo 1905435 4290389 := bbase (se 9 (by rfl) ⟨12569, by rfl⟩ : syracuseStep 4290389 = 25139) (by norm_num)
theorem B2860259 : Blo 1905435 2860259 := bstep (se 1 (by rfl) ⟨2145194, by rfl⟩ : syracuseStep 2860259 = 4290389) B4290389
theorem B1906839 : Blo 1905435 1906839 := bstep (se 1 (by rfl) ⟨1430129, by rfl⟩ : syracuseStep 1906839 = 2860259) B2860259
theorem B5430037 : Blo 1905435 5430037 := bbase (se 6 (by rfl) ⟨127266, by rfl⟩ : syracuseStep 5430037 = 254533) (by norm_num)
theorem B7240049 : Blo 1905435 7240049 := bstep (se 2 (by rfl) ⟨2715018, by rfl⟩ : syracuseStep 7240049 = 5430037) B5430037
theorem B4826699 : Blo 1905435 4826699 := bstep (se 1 (by rfl) ⟨3620024, by rfl⟩ : syracuseStep 4826699 = 7240049) B7240049
theorem B3217799 : Blo 1905435 3217799 := bstep (se 1 (by rfl) ⟨2413349, by rfl⟩ : syracuseStep 3217799 = 4826699) B4826699
theorem B2145199 : Blo 1905435 2145199 := bstep (se 1 (by rfl) ⟨1608899, by rfl⟩ : syracuseStep 2145199 = 3217799) B3217799
theorem B2860265 : Blo 1905435 2860265 := bstep (se 2 (by rfl) ⟨1072599, by rfl⟩ : syracuseStep 2860265 = 2145199) B2145199
theorem B1906843 : Blo 1905435 1906843 := bstep (se 1 (by rfl) ⟨1430132, by rfl⟩ : syracuseStep 1906843 = 2860265) B2860265
theorem B3719485 : Blo 1905435 3719485 := bbase (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) (by norm_num)
theorem B4959313 : Blo 1905435 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B26449669 : Blo 1905435 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B35266225 : Blo 1905435 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B47021633 : Blo 1905435 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B31347755 : Blo 1905435 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B20898503 : Blo 1905435 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B13932335 : Blo 1905435 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B37152893 : Blo 1905435 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B24768595 : Blo 1905435 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B132099173 : Blo 1905435 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B88066115 : Blo 1905435 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B58710743 : Blo 1905435 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B39140495 : Blo 1905435 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B26093663 : Blo 1905435 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B17395775 : Blo 1905435 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B11597183 : Blo 1905435 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B7731455 : Blo 1905435 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B82468853 : Blo 1905435 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B54979235 : Blo 1905435 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B36652823 : Blo 1905435 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B24435215 : Blo 1905435 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B16290143 : Blo 1905435 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B10860095 : Blo 1905435 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B7240063 : Blo 1905435 7240063 := bstep (se 1 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 7240063 = 10860095) B10860095
theorem B9653417 : Blo 1905435 9653417 := bstep (se 2 (by rfl) ⟨3620031, by rfl⟩ : syracuseStep 9653417 = 7240063) B7240063
theorem B6435611 : Blo 1905435 6435611 := bstep (se 1 (by rfl) ⟨4826708, by rfl⟩ : syracuseStep 6435611 = 9653417) B9653417
theorem B4290407 : Blo 1905435 4290407 := bstep (se 1 (by rfl) ⟨3217805, by rfl⟩ : syracuseStep 4290407 = 6435611) B6435611
theorem B2860271 : Blo 1905435 2860271 := bstep (se 1 (by rfl) ⟨2145203, by rfl⟩ : syracuseStep 2860271 = 4290407) B4290407
theorem B1906847 : Blo 1905435 1906847 := bstep (se 1 (by rfl) ⟨1430135, by rfl⟩ : syracuseStep 1906847 = 2860271) B2860271
theorem B2860277 : Blo 1905435 2860277 := bbase (se 5 (by rfl) ⟨134075, by rfl⟩ : syracuseStep 2860277 = 268151) (by norm_num)
theorem B1906851 : Blo 1905435 1906851 := bstep (se 1 (by rfl) ⟨1430138, by rfl⟩ : syracuseStep 1906851 = 2860277) B2860277
theorem B2899309 : Blo 1905435 2899309 := bbase (se 3 (by rfl) ⟨543620, by rfl⟩ : syracuseStep 2899309 = 1087241) (by norm_num)
theorem B3865745 : Blo 1905435 3865745 := bstep (se 2 (by rfl) ⟨1449654, by rfl⟩ : syracuseStep 3865745 = 2899309) B2899309
theorem B10308653 : Blo 1905435 10308653 := bstep (se 3 (by rfl) ⟨1932872, by rfl⟩ : syracuseStep 10308653 = 3865745) B3865745
theorem B6872435 : Blo 1905435 6872435 := bstep (se 1 (by rfl) ⟨5154326, by rfl⟩ : syracuseStep 6872435 = 10308653) B10308653
theorem B4581623 : Blo 1905435 4581623 := bstep (se 1 (by rfl) ⟨3436217, by rfl⟩ : syracuseStep 4581623 = 6872435) B6872435
theorem B12217661 : Blo 1905435 12217661 := bstep (se 3 (by rfl) ⟨2290811, by rfl⟩ : syracuseStep 12217661 = 4581623) B4581623
theorem B8145107 : Blo 1905435 8145107 := bstep (se 1 (by rfl) ⟨6108830, by rfl⟩ : syracuseStep 8145107 = 12217661) B12217661
theorem B5430071 : Blo 1905435 5430071 := bstep (se 1 (by rfl) ⟨4072553, by rfl⟩ : syracuseStep 5430071 = 8145107) B8145107
theorem B3620047 : Blo 1905435 3620047 := bstep (se 1 (by rfl) ⟨2715035, by rfl⟩ : syracuseStep 3620047 = 5430071) B5430071
theorem B4826729 : Blo 1905435 4826729 := bstep (se 2 (by rfl) ⟨1810023, by rfl⟩ : syracuseStep 4826729 = 3620047) B3620047
theorem B3217819 : Blo 1905435 3217819 := bstep (se 1 (by rfl) ⟨2413364, by rfl⟩ : syracuseStep 3217819 = 4826729) B4826729
theorem B4290425 : Blo 1905435 4290425 := bstep (se 2 (by rfl) ⟨1608909, by rfl⟩ : syracuseStep 4290425 = 3217819) B3217819
theorem B2860283 : Blo 1905435 2860283 := bstep (se 1 (by rfl) ⟨2145212, by rfl⟩ : syracuseStep 2860283 = 4290425) B4290425
theorem B1906855 : Blo 1905435 1906855 := bstep (se 1 (by rfl) ⟨1430141, by rfl⟩ : syracuseStep 1906855 = 2860283) B2860283
theorem B2145217 : Blo 1905435 2145217 := bbase (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) (by norm_num)
theorem B2860289 : Blo 1905435 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B1906859 : Blo 1905435 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B4826749 : Blo 1905435 4826749 := bbase (se 3 (by rfl) ⟨905015, by rfl⟩ : syracuseStep 4826749 = 1810031) (by norm_num)
theorem B6435665 : Blo 1905435 6435665 := bstep (se 2 (by rfl) ⟨2413374, by rfl⟩ : syracuseStep 6435665 = 4826749) B4826749
theorem B4290443 : Blo 1905435 4290443 := bstep (se 1 (by rfl) ⟨3217832, by rfl⟩ : syracuseStep 4290443 = 6435665) B6435665
theorem B2860295 : Blo 1905435 2860295 := bstep (se 1 (by rfl) ⟨2145221, by rfl⟩ : syracuseStep 2860295 = 4290443) B4290443
theorem B1906863 : Blo 1905435 1906863 := bstep (se 1 (by rfl) ⟨1430147, by rfl⟩ : syracuseStep 1906863 = 2860295) B2860295
theorem B2860301 : Blo 1905435 2860301 := bbase (se 3 (by rfl) ⟨536306, by rfl⟩ : syracuseStep 2860301 = 1072613) (by norm_num)
theorem B1906867 : Blo 1905435 1906867 := bstep (se 1 (by rfl) ⟨1430150, by rfl⟩ : syracuseStep 1906867 = 2860301) B2860301
theorem B4290461 : Blo 1905435 4290461 := bbase (se 3 (by rfl) ⟨804461, by rfl⟩ : syracuseStep 4290461 = 1608923) (by norm_num)
theorem B2860307 : Blo 1905435 2860307 := bstep (se 1 (by rfl) ⟨2145230, by rfl⟩ : syracuseStep 2860307 = 4290461) B4290461
theorem B1906871 : Blo 1905435 1906871 := bstep (se 1 (by rfl) ⟨1430153, by rfl⟩ : syracuseStep 1906871 = 2860307) B2860307
theorem B3217853 : Blo 1905435 3217853 := bbase (se 3 (by rfl) ⟨603347, by rfl⟩ : syracuseStep 3217853 = 1206695) (by norm_num)
theorem B2145235 : Blo 1905435 2145235 := bstep (se 1 (by rfl) ⟨1608926, by rfl⟩ : syracuseStep 2145235 = 3217853) B3217853
theorem B2860313 : Blo 1905435 2860313 := bstep (se 2 (by rfl) ⟨1072617, by rfl⟩ : syracuseStep 2860313 = 2145235) B2145235
theorem B1906875 : Blo 1905435 1906875 := bstep (se 1 (by rfl) ⟨1430156, by rfl⟩ : syracuseStep 1906875 = 2860313) B2860313
theorem B10860277 : Blo 1905435 10860277 := bbase (se 5 (by rfl) ⟨509075, by rfl⟩ : syracuseStep 10860277 = 1018151) (by norm_num)
theorem B14480369 : Blo 1905435 14480369 := bstep (se 2 (by rfl) ⟨5430138, by rfl⟩ : syracuseStep 14480369 = 10860277) B10860277
theorem B9653579 : Blo 1905435 9653579 := bstep (se 1 (by rfl) ⟨7240184, by rfl⟩ : syracuseStep 9653579 = 14480369) B14480369
theorem B6435719 : Blo 1905435 6435719 := bstep (se 1 (by rfl) ⟨4826789, by rfl⟩ : syracuseStep 6435719 = 9653579) B9653579
theorem B4290479 : Blo 1905435 4290479 := bstep (se 1 (by rfl) ⟨3217859, by rfl⟩ : syracuseStep 4290479 = 6435719) B6435719
theorem B2860319 : Blo 1905435 2860319 := bstep (se 1 (by rfl) ⟨2145239, by rfl⟩ : syracuseStep 2860319 = 4290479) B4290479
theorem B1906879 : Blo 1905435 1906879 := bstep (se 1 (by rfl) ⟨1430159, by rfl⟩ : syracuseStep 1906879 = 2860319) B2860319
theorem B2860325 : Blo 1905435 2860325 := bbase (se 4 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 2860325 = 536311) (by norm_num)
theorem B1906883 : Blo 1905435 1906883 := bstep (se 1 (by rfl) ⟨1430162, by rfl⟩ : syracuseStep 1906883 = 2860325) B2860325
theorem B2413405 : Blo 1905435 2413405 := bbase (se 3 (by rfl) ⟨452513, by rfl⟩ : syracuseStep 2413405 = 905027) (by norm_num)
theorem B3217873 : Blo 1905435 3217873 := bstep (se 2 (by rfl) ⟨1206702, by rfl⟩ : syracuseStep 3217873 = 2413405) B2413405
theorem B4290497 : Blo 1905435 4290497 := bstep (se 2 (by rfl) ⟨1608936, by rfl⟩ : syracuseStep 4290497 = 3217873) B3217873
theorem B2860331 : Blo 1905435 2860331 := bstep (se 1 (by rfl) ⟨2145248, by rfl⟩ : syracuseStep 2860331 = 4290497) B4290497
theorem B1906887 : Blo 1905435 1906887 := bstep (se 1 (by rfl) ⟨1430165, by rfl⟩ : syracuseStep 1906887 = 2860331) B2860331
theorem B2145253 : Blo 1905435 2145253 := bbase (se 4 (by rfl) ⟨201117, by rfl⟩ : syracuseStep 2145253 = 402235) (by norm_num)
theorem B2860337 : Blo 1905435 2860337 := bstep (se 2 (by rfl) ⟨1072626, by rfl⟩ : syracuseStep 2860337 = 2145253) B2145253
theorem B1906891 : Blo 1905435 1906891 := bstep (se 1 (by rfl) ⟨1430168, by rfl⟩ : syracuseStep 1906891 = 2860337) B2860337
theorem B16512821 : Blo 1905435 16512821 := bbase (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) (by norm_num)
theorem B11008547 : Blo 1905435 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B7339031 : Blo 1905435 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B4892687 : Blo 1905435 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B3261791 : Blo 1905435 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B8698109 : Blo 1905435 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B23194957 : Blo 1905435 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B30926609 : Blo 1905435 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B20617739 : Blo 1905435 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B13745159 : Blo 1905435 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B9163439 : Blo 1905435 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B6108959 : Blo 1905435 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B4072639 : Blo 1905435 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B5430185 : Blo 1905435 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B3620123 : Blo 1905435 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B2413415 : Blo 1905435 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B6435773 : Blo 1905435 6435773 := bstep (se 3 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 6435773 = 2413415) B2413415
theorem B4290515 : Blo 1905435 4290515 := bstep (se 1 (by rfl) ⟨3217886, by rfl⟩ : syracuseStep 4290515 = 6435773) B6435773
theorem B2860343 : Blo 1905435 2860343 := bstep (se 1 (by rfl) ⟨2145257, by rfl⟩ : syracuseStep 2860343 = 4290515) B4290515
theorem B1906895 : Blo 1905435 1906895 := bstep (se 1 (by rfl) ⟨1430171, by rfl⟩ : syracuseStep 1906895 = 2860343) B2860343
theorem B2860349 : Blo 1905435 2860349 := bbase (se 3 (by rfl) ⟨536315, by rfl⟩ : syracuseStep 2860349 = 1072631) (by norm_num)
theorem B1906899 : Blo 1905435 1906899 := bstep (se 1 (by rfl) ⟨1430174, by rfl⟩ : syracuseStep 1906899 = 2860349) B2860349
theorem B4290533 : Blo 1905435 4290533 := bbase (se 4 (by rfl) ⟨402237, by rfl⟩ : syracuseStep 4290533 = 804475) (by norm_num)
theorem B2860355 : Blo 1905435 2860355 := bstep (se 1 (by rfl) ⟨2145266, by rfl⟩ : syracuseStep 2860355 = 4290533) B4290533
theorem B1906903 : Blo 1905435 1906903 := bstep (se 1 (by rfl) ⟨1430177, by rfl⟩ : syracuseStep 1906903 = 2860355) B2860355
theorem B4826861 : Blo 1905435 4826861 := bbase (se 3 (by rfl) ⟨905036, by rfl⟩ : syracuseStep 4826861 = 1810073) (by norm_num)
theorem B3217907 : Blo 1905435 3217907 := bstep (se 1 (by rfl) ⟨2413430, by rfl⟩ : syracuseStep 3217907 = 4826861) B4826861
theorem B2145271 : Blo 1905435 2145271 := bstep (se 1 (by rfl) ⟨1608953, by rfl⟩ : syracuseStep 2145271 = 3217907) B3217907
theorem B2860361 : Blo 1905435 2860361 := bstep (se 2 (by rfl) ⟨1072635, by rfl⟩ : syracuseStep 2860361 = 2145271) B2145271
theorem B1906907 : Blo 1905435 1906907 := bstep (se 1 (by rfl) ⟨1430180, by rfl⟩ : syracuseStep 1906907 = 2860361) B2860361
theorem B3096181 : Blo 1905435 3096181 := bbase (se 5 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 3096181 = 290267) (by norm_num)
theorem B4128241 : Blo 1905435 4128241 := bstep (se 2 (by rfl) ⟨1548090, by rfl⟩ : syracuseStep 4128241 = 3096181) B3096181
theorem B5504321 : Blo 1905435 5504321 := bstep (se 2 (by rfl) ⟨2064120, by rfl⟩ : syracuseStep 5504321 = 4128241) B4128241
theorem B3669547 : Blo 1905435 3669547 := bstep (se 1 (by rfl) ⟨2752160, by rfl⟩ : syracuseStep 3669547 = 5504321) B5504321
theorem B4892729 : Blo 1905435 4892729 := bstep (se 2 (by rfl) ⟨1834773, by rfl⟩ : syracuseStep 4892729 = 3669547) B3669547
theorem B13047277 : Blo 1905435 13047277 := bstep (se 3 (by rfl) ⟨2446364, by rfl⟩ : syracuseStep 13047277 = 4892729) B4892729
theorem B17396369 : Blo 1905435 17396369 := bstep (se 2 (by rfl) ⟨6523638, by rfl⟩ : syracuseStep 17396369 = 13047277) B13047277
theorem B11597579 : Blo 1905435 11597579 := bstep (se 1 (by rfl) ⟨8698184, by rfl⟩ : syracuseStep 11597579 = 17396369) B17396369
theorem B7731719 : Blo 1905435 7731719 := bstep (se 1 (by rfl) ⟨5798789, by rfl⟩ : syracuseStep 7731719 = 11597579) B11597579
theorem B5154479 : Blo 1905435 5154479 := bstep (se 1 (by rfl) ⟨3865859, by rfl⟩ : syracuseStep 5154479 = 7731719) B7731719
theorem B3436319 : Blo 1905435 3436319 := bstep (se 1 (by rfl) ⟨2577239, by rfl⟩ : syracuseStep 3436319 = 5154479) B5154479
theorem B2290879 : Blo 1905435 2290879 := bstep (se 1 (by rfl) ⟨1718159, by rfl⟩ : syracuseStep 2290879 = 3436319) B3436319
theorem B3054505 : Blo 1905435 3054505 := bstep (se 2 (by rfl) ⟨1145439, by rfl⟩ : syracuseStep 3054505 = 2290879) B2290879
theorem B4072673 : Blo 1905435 4072673 := bstep (se 2 (by rfl) ⟨1527252, by rfl⟩ : syracuseStep 4072673 = 3054505) B3054505
theorem B2715115 : Blo 1905435 2715115 := bstep (se 1 (by rfl) ⟨2036336, by rfl⟩ : syracuseStep 2715115 = 4072673) B4072673
theorem B3620153 : Blo 1905435 3620153 := bstep (se 2 (by rfl) ⟨1357557, by rfl⟩ : syracuseStep 3620153 = 2715115) B2715115
theorem B9653741 : Blo 1905435 9653741 := bstep (se 3 (by rfl) ⟨1810076, by rfl⟩ : syracuseStep 9653741 = 3620153) B3620153
theorem B6435827 : Blo 1905435 6435827 := bstep (se 1 (by rfl) ⟨4826870, by rfl⟩ : syracuseStep 6435827 = 9653741) B9653741
theorem B4290551 : Blo 1905435 4290551 := bstep (se 1 (by rfl) ⟨3217913, by rfl⟩ : syracuseStep 4290551 = 6435827) B6435827
theorem B2860367 : Blo 1905435 2860367 := bstep (se 1 (by rfl) ⟨2145275, by rfl⟩ : syracuseStep 2860367 = 4290551) B4290551
theorem B1906911 : Blo 1905435 1906911 := bstep (se 1 (by rfl) ⟨1430183, by rfl⟩ : syracuseStep 1906911 = 2860367) B2860367
theorem B2860373 : Blo 1905435 2860373 := bbase (se 12 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 2860373 = 2095) (by norm_num)
theorem B1906915 : Blo 1905435 1906915 := bstep (se 1 (by rfl) ⟨1430186, by rfl⟩ : syracuseStep 1906915 = 2860373) B2860373
theorem B2036345 : Blo 1905435 2036345 := bbase (se 2 (by rfl) ⟨763629, by rfl⟩ : syracuseStep 2036345 = 1527259) (by norm_num)
theorem B5430253 : Blo 1905435 5430253 := bstep (se 3 (by rfl) ⟨1018172, by rfl⟩ : syracuseStep 5430253 = 2036345) B2036345
theorem B7240337 : Blo 1905435 7240337 := bstep (se 2 (by rfl) ⟨2715126, by rfl⟩ : syracuseStep 7240337 = 5430253) B5430253
theorem B4826891 : Blo 1905435 4826891 := bstep (se 1 (by rfl) ⟨3620168, by rfl⟩ : syracuseStep 4826891 = 7240337) B7240337
theorem B3217927 : Blo 1905435 3217927 := bstep (se 1 (by rfl) ⟨2413445, by rfl⟩ : syracuseStep 3217927 = 4826891) B4826891
theorem B4290569 : Blo 1905435 4290569 := bstep (se 2 (by rfl) ⟨1608963, by rfl⟩ : syracuseStep 4290569 = 3217927) B3217927
theorem B2860379 : Blo 1905435 2860379 := bstep (se 1 (by rfl) ⟨2145284, by rfl⟩ : syracuseStep 2860379 = 4290569) B4290569
theorem B1906919 : Blo 1905435 1906919 := bstep (se 1 (by rfl) ⟨1430189, by rfl⟩ : syracuseStep 1906919 = 2860379) B2860379
theorem B2145289 : Blo 1905435 2145289 := bbase (se 2 (by rfl) ⟨804483, by rfl⟩ : syracuseStep 2145289 = 1608967) (by norm_num)
theorem B2860385 : Blo 1905435 2860385 := bstep (se 2 (by rfl) ⟨1072644, by rfl⟩ : syracuseStep 2860385 = 2145289) B2145289
theorem B1906923 : Blo 1905435 1906923 := bstep (se 1 (by rfl) ⟨1430192, by rfl⟩ : syracuseStep 1906923 = 2860385) B2860385
theorem B6872693 : Blo 1905435 6872693 := bbase (se 5 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 6872693 = 644315) (by norm_num)
theorem B18327181 : Blo 1905435 18327181 := bstep (se 3 (by rfl) ⟨3436346, by rfl⟩ : syracuseStep 18327181 = 6872693) B6872693
theorem B24436241 : Blo 1905435 24436241 := bstep (se 2 (by rfl) ⟨9163590, by rfl⟩ : syracuseStep 24436241 = 18327181) B18327181
theorem B16290827 : Blo 1905435 16290827 := bstep (se 1 (by rfl) ⟨12218120, by rfl⟩ : syracuseStep 16290827 = 24436241) B24436241
theorem B10860551 : Blo 1905435 10860551 := bstep (se 1 (by rfl) ⟨8145413, by rfl⟩ : syracuseStep 10860551 = 16290827) B16290827
theorem B7240367 : Blo 1905435 7240367 := bstep (se 1 (by rfl) ⟨5430275, by rfl⟩ : syracuseStep 7240367 = 10860551) B10860551
theorem B4826911 : Blo 1905435 4826911 := bstep (se 1 (by rfl) ⟨3620183, by rfl⟩ : syracuseStep 4826911 = 7240367) B7240367
theorem B6435881 : Blo 1905435 6435881 := bstep (se 2 (by rfl) ⟨2413455, by rfl⟩ : syracuseStep 6435881 = 4826911) B4826911
theorem B4290587 : Blo 1905435 4290587 := bstep (se 1 (by rfl) ⟨3217940, by rfl⟩ : syracuseStep 4290587 = 6435881) B6435881
theorem B2860391 : Blo 1905435 2860391 := bstep (se 1 (by rfl) ⟨2145293, by rfl⟩ : syracuseStep 2860391 = 4290587) B4290587
theorem B1906927 : Blo 1905435 1906927 := bstep (se 1 (by rfl) ⟨1430195, by rfl⟩ : syracuseStep 1906927 = 2860391) B2860391
theorem B2860397 : Blo 1905435 2860397 := bbase (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) (by norm_num)
theorem B1906931 : Blo 1905435 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B4290605 : Blo 1905435 4290605 := bbase (se 3 (by rfl) ⟨804488, by rfl⟩ : syracuseStep 4290605 = 1608977) (by norm_num)
theorem B2860403 : Blo 1905435 2860403 := bstep (se 1 (by rfl) ⟨2145302, by rfl⟩ : syracuseStep 2860403 = 4290605) B4290605
theorem B1906935 : Blo 1905435 1906935 := bstep (se 1 (by rfl) ⟨1430201, by rfl⟩ : syracuseStep 1906935 = 2860403) B2860403
theorem B2577277 : Blo 1905435 2577277 := bbase (se 3 (by rfl) ⟨483239, by rfl⟩ : syracuseStep 2577277 = 966479) (by norm_num)
theorem B13745477 : Blo 1905435 13745477 := bstep (se 4 (by rfl) ⟨1288638, by rfl⟩ : syracuseStep 13745477 = 2577277) B2577277
theorem B9163651 : Blo 1905435 9163651 := bstep (se 1 (by rfl) ⟨6872738, by rfl⟩ : syracuseStep 9163651 = 13745477) B13745477
theorem B12218201 : Blo 1905435 12218201 := bstep (se 2 (by rfl) ⟨4581825, by rfl⟩ : syracuseStep 12218201 = 9163651) B9163651
theorem B8145467 : Blo 1905435 8145467 := bstep (se 1 (by rfl) ⟨6109100, by rfl⟩ : syracuseStep 8145467 = 12218201) B12218201
theorem B5430311 : Blo 1905435 5430311 := bstep (se 1 (by rfl) ⟨4072733, by rfl⟩ : syracuseStep 5430311 = 8145467) B8145467
theorem B3620207 : Blo 1905435 3620207 := bstep (se 1 (by rfl) ⟨2715155, by rfl⟩ : syracuseStep 3620207 = 5430311) B5430311
theorem B2413471 : Blo 1905435 2413471 := bstep (se 1 (by rfl) ⟨1810103, by rfl⟩ : syracuseStep 2413471 = 3620207) B3620207
theorem B3217961 : Blo 1905435 3217961 := bstep (se 2 (by rfl) ⟨1206735, by rfl⟩ : syracuseStep 3217961 = 2413471) B2413471
theorem B2145307 : Blo 1905435 2145307 := bstep (se 1 (by rfl) ⟨1608980, by rfl⟩ : syracuseStep 2145307 = 3217961) B3217961
theorem B2860409 : Blo 1905435 2860409 := bstep (se 2 (by rfl) ⟨1072653, by rfl⟩ : syracuseStep 2860409 = 2145307) B2145307
theorem B1906939 : Blo 1905435 1906939 := bstep (se 1 (by rfl) ⟨1430204, by rfl⟩ : syracuseStep 1906939 = 2860409) B2860409
theorem B7731845 : Blo 1905435 7731845 := bbase (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) (by norm_num)
theorem B5154563 : Blo 1905435 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B13745501 : Blo 1905435 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B9163667 : Blo 1905435 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B6109111 : Blo 1905435 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B32581925 : Blo 1905435 32581925 := bstep (se 4 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 32581925 = 6109111) B6109111
theorem B21721283 : Blo 1905435 21721283 := bstep (se 1 (by rfl) ⟨16290962, by rfl⟩ : syracuseStep 21721283 = 32581925) B32581925
theorem B14480855 : Blo 1905435 14480855 := bstep (se 1 (by rfl) ⟨10860641, by rfl⟩ : syracuseStep 14480855 = 21721283) B21721283
theorem B9653903 : Blo 1905435 9653903 := bstep (se 1 (by rfl) ⟨7240427, by rfl⟩ : syracuseStep 9653903 = 14480855) B14480855
theorem B6435935 : Blo 1905435 6435935 := bstep (se 1 (by rfl) ⟨4826951, by rfl⟩ : syracuseStep 6435935 = 9653903) B9653903
theorem B4290623 : Blo 1905435 4290623 := bstep (se 1 (by rfl) ⟨3217967, by rfl⟩ : syracuseStep 4290623 = 6435935) B6435935
theorem B2860415 : Blo 1905435 2860415 := bstep (se 1 (by rfl) ⟨2145311, by rfl⟩ : syracuseStep 2860415 = 4290623) B4290623
theorem B1906943 : Blo 1905435 1906943 := bstep (se 1 (by rfl) ⟨1430207, by rfl⟩ : syracuseStep 1906943 = 2860415) B2860415
theorem B2860421 : Blo 1905435 2860421 := bbase (se 4 (by rfl) ⟨268164, by rfl⟩ : syracuseStep 2860421 = 536329) (by norm_num)
theorem B1906947 : Blo 1905435 1906947 := bstep (se 1 (by rfl) ⟨1430210, by rfl⟩ : syracuseStep 1906947 = 2860421) B2860421
theorem B3217981 : Blo 1905435 3217981 := bbase (se 3 (by rfl) ⟨603371, by rfl⟩ : syracuseStep 3217981 = 1206743) (by norm_num)
theorem B4290641 : Blo 1905435 4290641 := bstep (se 2 (by rfl) ⟨1608990, by rfl⟩ : syracuseStep 4290641 = 3217981) B3217981
theorem B2860427 : Blo 1905435 2860427 := bstep (se 1 (by rfl) ⟨2145320, by rfl⟩ : syracuseStep 2860427 = 4290641) B4290641
theorem B1906951 : Blo 1905435 1906951 := bstep (se 1 (by rfl) ⟨1430213, by rfl⟩ : syracuseStep 1906951 = 2860427) B2860427
theorem B2145325 : Blo 1905435 2145325 := bbase (se 3 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 2145325 = 804497) (by norm_num)
theorem B2860433 : Blo 1905435 2860433 := bstep (se 2 (by rfl) ⟨1072662, by rfl⟩ : syracuseStep 2860433 = 2145325) B2145325
theorem B1906955 : Blo 1905435 1906955 := bstep (se 1 (by rfl) ⟨1430216, by rfl⟩ : syracuseStep 1906955 = 2860433) B2860433
theorem B6435989 : Blo 1905435 6435989 := bbase (se 6 (by rfl) ⟨150843, by rfl⟩ : syracuseStep 6435989 = 301687) (by norm_num)
theorem B4290659 : Blo 1905435 4290659 := bstep (se 1 (by rfl) ⟨3217994, by rfl⟩ : syracuseStep 4290659 = 6435989) B6435989
theorem B2860439 : Blo 1905435 2860439 := bstep (se 1 (by rfl) ⟨2145329, by rfl⟩ : syracuseStep 2860439 = 4290659) B4290659
theorem B1906959 : Blo 1905435 1906959 := bstep (se 1 (by rfl) ⟨1430219, by rfl⟩ : syracuseStep 1906959 = 2860439) B2860439
theorem B2860445 : Blo 1905435 2860445 := bbase (se 3 (by rfl) ⟨536333, by rfl⟩ : syracuseStep 2860445 = 1072667) (by norm_num)
theorem B1906963 : Blo 1905435 1906963 := bstep (se 1 (by rfl) ⟨1430222, by rfl⟩ : syracuseStep 1906963 = 2860445) B2860445
theorem B4290677 : Blo 1905435 4290677 := bbase (se 5 (by rfl) ⟨201125, by rfl⟩ : syracuseStep 4290677 = 402251) (by norm_num)
theorem B2860451 : Blo 1905435 2860451 := bstep (se 1 (by rfl) ⟨2145338, by rfl⟩ : syracuseStep 2860451 = 4290677) B4290677
theorem B1906967 : Blo 1905435 1906967 := bstep (se 1 (by rfl) ⟨1430225, by rfl⟩ : syracuseStep 1906967 = 2860451) B2860451
theorem B3865981 : Blo 1905435 3865981 := bbase (se 3 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 3865981 = 1449743) (by norm_num)
theorem B5154641 : Blo 1905435 5154641 := bstep (se 2 (by rfl) ⟨1932990, by rfl⟩ : syracuseStep 5154641 = 3865981) B3865981
theorem B3436427 : Blo 1905435 3436427 := bstep (se 1 (by rfl) ⟨2577320, by rfl⟩ : syracuseStep 3436427 = 5154641) B5154641
theorem B2290951 : Blo 1905435 2290951 := bstep (se 1 (by rfl) ⟨1718213, by rfl⟩ : syracuseStep 2290951 = 3436427) B3436427
theorem B3054601 : Blo 1905435 3054601 := bstep (se 2 (by rfl) ⟨1145475, by rfl⟩ : syracuseStep 3054601 = 2290951) B2290951
theorem B16291205 : Blo 1905435 16291205 := bstep (se 4 (by rfl) ⟨1527300, by rfl⟩ : syracuseStep 16291205 = 3054601) B3054601
theorem B10860803 : Blo 1905435 10860803 := bstep (se 1 (by rfl) ⟨8145602, by rfl⟩ : syracuseStep 10860803 = 16291205) B16291205
theorem B7240535 : Blo 1905435 7240535 := bstep (se 1 (by rfl) ⟨5430401, by rfl⟩ : syracuseStep 7240535 = 10860803) B10860803
theorem B4827023 : Blo 1905435 4827023 := bstep (se 1 (by rfl) ⟨3620267, by rfl⟩ : syracuseStep 4827023 = 7240535) B7240535
theorem B3218015 : Blo 1905435 3218015 := bstep (se 1 (by rfl) ⟨2413511, by rfl⟩ : syracuseStep 3218015 = 4827023) B4827023
theorem B2145343 : Blo 1905435 2145343 := bstep (se 1 (by rfl) ⟨1609007, by rfl⟩ : syracuseStep 2145343 = 3218015) B3218015
theorem B2860457 : Blo 1905435 2860457 := bstep (se 2 (by rfl) ⟨1072671, by rfl⟩ : syracuseStep 2860457 = 2145343) B2145343
theorem B1906971 : Blo 1905435 1906971 := bstep (se 1 (by rfl) ⟨1430228, by rfl⟩ : syracuseStep 1906971 = 2860457) B2860457
theorem B7240549 : Blo 1905435 7240549 := bbase (se 4 (by rfl) ⟨678801, by rfl⟩ : syracuseStep 7240549 = 1357603) (by norm_num)
theorem B9654065 : Blo 1905435 9654065 := bstep (se 2 (by rfl) ⟨3620274, by rfl⟩ : syracuseStep 9654065 = 7240549) B7240549
theorem B6436043 : Blo 1905435 6436043 := bstep (se 1 (by rfl) ⟨4827032, by rfl⟩ : syracuseStep 6436043 = 9654065) B9654065
theorem B4290695 : Blo 1905435 4290695 := bstep (se 1 (by rfl) ⟨3218021, by rfl⟩ : syracuseStep 4290695 = 6436043) B6436043
theorem B2860463 : Blo 1905435 2860463 := bstep (se 1 (by rfl) ⟨2145347, by rfl⟩ : syracuseStep 2860463 = 4290695) B4290695
theorem B1906975 : Blo 1905435 1906975 := bstep (se 1 (by rfl) ⟨1430231, by rfl⟩ : syracuseStep 1906975 = 2860463) B2860463
theorem B2860469 : Blo 1905435 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1906979 : Blo 1905435 1906979 := bstep (se 1 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 1906979 = 2860469) B2860469
theorem B4827053 : Blo 1905435 4827053 := bbase (se 3 (by rfl) ⟨905072, by rfl⟩ : syracuseStep 4827053 = 1810145) (by norm_num)
theorem B3218035 : Blo 1905435 3218035 := bstep (se 1 (by rfl) ⟨2413526, by rfl⟩ : syracuseStep 3218035 = 4827053) B4827053
theorem B4290713 : Blo 1905435 4290713 := bstep (se 2 (by rfl) ⟨1609017, by rfl⟩ : syracuseStep 4290713 = 3218035) B3218035
theorem B2860475 : Blo 1905435 2860475 := bstep (se 1 (by rfl) ⟨2145356, by rfl⟩ : syracuseStep 2860475 = 4290713) B4290713
theorem B1906983 : Blo 1905435 1906983 := bstep (se 1 (by rfl) ⟨1430237, by rfl⟩ : syracuseStep 1906983 = 2860475) B2860475
theorem B2145361 : Blo 1905435 2145361 := bbase (se 2 (by rfl) ⟨804510, by rfl⟩ : syracuseStep 2145361 = 1609021) (by norm_num)
theorem B2860481 : Blo 1905435 2860481 := bstep (se 2 (by rfl) ⟨1072680, by rfl⟩ : syracuseStep 2860481 = 2145361) B2145361
theorem B1906987 : Blo 1905435 1906987 := bstep (se 1 (by rfl) ⟨1430240, by rfl⟩ : syracuseStep 1906987 = 2860481) B2860481
theorem B2715229 : Blo 1905435 2715229 := bbase (se 3 (by rfl) ⟨509105, by rfl⟩ : syracuseStep 2715229 = 1018211) (by norm_num)
theorem B3620305 : Blo 1905435 3620305 := bstep (se 2 (by rfl) ⟨1357614, by rfl⟩ : syracuseStep 3620305 = 2715229) B2715229
theorem B4827073 : Blo 1905435 4827073 := bstep (se 2 (by rfl) ⟨1810152, by rfl⟩ : syracuseStep 4827073 = 3620305) B3620305
theorem B6436097 : Blo 1905435 6436097 := bstep (se 2 (by rfl) ⟨2413536, by rfl⟩ : syracuseStep 6436097 = 4827073) B4827073
theorem B4290731 : Blo 1905435 4290731 := bstep (se 1 (by rfl) ⟨3218048, by rfl⟩ : syracuseStep 4290731 = 6436097) B6436097
theorem B2860487 : Blo 1905435 2860487 := bstep (se 1 (by rfl) ⟨2145365, by rfl⟩ : syracuseStep 2860487 = 4290731) B4290731
theorem B1906991 : Blo 1905435 1906991 := bstep (se 1 (by rfl) ⟨1430243, by rfl⟩ : syracuseStep 1906991 = 2860487) B2860487
theorem B2860493 : Blo 1905435 2860493 := bbase (se 3 (by rfl) ⟨536342, by rfl⟩ : syracuseStep 2860493 = 1072685) (by norm_num)
theorem B1906995 : Blo 1905435 1906995 := bstep (se 1 (by rfl) ⟨1430246, by rfl⟩ : syracuseStep 1906995 = 2860493) B2860493
theorem B4290749 : Blo 1905435 4290749 := bbase (se 3 (by rfl) ⟨804515, by rfl⟩ : syracuseStep 4290749 = 1609031) (by norm_num)
theorem B2860499 : Blo 1905435 2860499 := bstep (se 1 (by rfl) ⟨2145374, by rfl⟩ : syracuseStep 2860499 = 4290749) B4290749
theorem B1906999 : Blo 1905435 1906999 := bstep (se 1 (by rfl) ⟨1430249, by rfl⟩ : syracuseStep 1906999 = 2860499) B2860499
theorem B3218069 : Blo 1905435 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B2145379 : Blo 1905435 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B2860505 : Blo 1905435 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B1907003 : Blo 1905435 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B4349309 : Blo 1905435 4349309 := bbase (se 3 (by rfl) ⟨815495, by rfl⟩ : syracuseStep 4349309 = 1630991) (by norm_num)
theorem B11598157 : Blo 1905435 11598157 := bstep (se 3 (by rfl) ⟨2174654, by rfl⟩ : syracuseStep 11598157 = 4349309) B4349309
theorem B15464209 : Blo 1905435 15464209 := bstep (se 2 (by rfl) ⟨5799078, by rfl⟩ : syracuseStep 15464209 = 11598157) B11598157
theorem B20618945 : Blo 1905435 20618945 := bstep (se 2 (by rfl) ⟨7732104, by rfl⟩ : syracuseStep 20618945 = 15464209) B15464209
theorem B13745963 : Blo 1905435 13745963 := bstep (se 1 (by rfl) ⟨10309472, by rfl⟩ : syracuseStep 13745963 = 20618945) B20618945
theorem B9163975 : Blo 1905435 9163975 := bstep (se 1 (by rfl) ⟨6872981, by rfl⟩ : syracuseStep 9163975 = 13745963) B13745963
theorem B12218633 : Blo 1905435 12218633 := bstep (se 2 (by rfl) ⟨4581987, by rfl⟩ : syracuseStep 12218633 = 9163975) B9163975
theorem B8145755 : Blo 1905435 8145755 := bstep (se 1 (by rfl) ⟨6109316, by rfl⟩ : syracuseStep 8145755 = 12218633) B12218633
theorem B5430503 : Blo 1905435 5430503 := bstep (se 1 (by rfl) ⟨4072877, by rfl⟩ : syracuseStep 5430503 = 8145755) B8145755
theorem B14481341 : Blo 1905435 14481341 := bstep (se 3 (by rfl) ⟨2715251, by rfl⟩ : syracuseStep 14481341 = 5430503) B5430503
theorem B9654227 : Blo 1905435 9654227 := bstep (se 1 (by rfl) ⟨7240670, by rfl⟩ : syracuseStep 9654227 = 14481341) B14481341
theorem B6436151 : Blo 1905435 6436151 := bstep (se 1 (by rfl) ⟨4827113, by rfl⟩ : syracuseStep 6436151 = 9654227) B9654227
theorem B4290767 : Blo 1905435 4290767 := bstep (se 1 (by rfl) ⟨3218075, by rfl⟩ : syracuseStep 4290767 = 6436151) B6436151
theorem B2860511 : Blo 1905435 2860511 := bstep (se 1 (by rfl) ⟨2145383, by rfl⟩ : syracuseStep 2860511 = 4290767) B4290767
theorem B1907007 : Blo 1905435 1907007 := bstep (se 1 (by rfl) ⟨1430255, by rfl⟩ : syracuseStep 1907007 = 2860511) B2860511
theorem B2860517 : Blo 1905435 2860517 := bbase (se 4 (by rfl) ⟨268173, by rfl⟩ : syracuseStep 2860517 = 536347) (by norm_num)
theorem B1907011 : Blo 1905435 1907011 := bstep (se 1 (by rfl) ⟨1430258, by rfl⟩ : syracuseStep 1907011 = 2860517) B2860517
theorem B5958421 : Blo 1905435 5958421 := bbase (se 6 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 5958421 = 279301) (by norm_num)
theorem B127112981 : Blo 1905435 127112981 := bstep (se 6 (by rfl) ⟨2979210, by rfl⟩ : syracuseStep 127112981 = 5958421) B5958421
theorem B338967949 : Blo 1905435 338967949 := bstep (se 3 (by rfl) ⟨63556490, by rfl⟩ : syracuseStep 338967949 = 127112981) B127112981
theorem B451957265 : Blo 1905435 451957265 := bstep (se 2 (by rfl) ⟨169483974, by rfl⟩ : syracuseStep 451957265 = 338967949) B338967949
theorem B301304843 : Blo 1905435 301304843 := bstep (se 1 (by rfl) ⟨225978632, by rfl⟩ : syracuseStep 301304843 = 451957265) B451957265
theorem B200869895 : Blo 1905435 200869895 := bstep (se 1 (by rfl) ⟨150652421, by rfl⟩ : syracuseStep 200869895 = 301304843) B301304843
theorem B133913263 : Blo 1905435 133913263 := bstep (se 1 (by rfl) ⟨100434947, by rfl⟩ : syracuseStep 133913263 = 200869895) B200869895
theorem B178551017 : Blo 1905435 178551017 := bstep (se 2 (by rfl) ⟨66956631, by rfl⟩ : syracuseStep 178551017 = 133913263) B133913263
theorem B119034011 : Blo 1905435 119034011 := bstep (se 1 (by rfl) ⟨89275508, by rfl⟩ : syracuseStep 119034011 = 178551017) B178551017
theorem B79356007 : Blo 1905435 79356007 := bstep (se 1 (by rfl) ⟨59517005, by rfl⟩ : syracuseStep 79356007 = 119034011) B119034011
theorem B423232037 : Blo 1905435 423232037 := bstep (se 4 (by rfl) ⟨39678003, by rfl⟩ : syracuseStep 423232037 = 79356007) B79356007
theorem B282154691 : Blo 1905435 282154691 := bstep (se 1 (by rfl) ⟨211616018, by rfl⟩ : syracuseStep 282154691 = 423232037) B423232037
theorem B752412509 : Blo 1905435 752412509 := bstep (se 3 (by rfl) ⟨141077345, by rfl⟩ : syracuseStep 752412509 = 282154691) B282154691
theorem B501608339 : Blo 1905435 501608339 := bstep (se 1 (by rfl) ⟨376206254, by rfl⟩ : syracuseStep 501608339 = 752412509) B752412509
theorem B334405559 : Blo 1905435 334405559 := bstep (se 1 (by rfl) ⟨250804169, by rfl⟩ : syracuseStep 334405559 = 501608339) B501608339
theorem B222937039 : Blo 1905435 222937039 := bstep (se 1 (by rfl) ⟨167202779, by rfl⟩ : syracuseStep 222937039 = 334405559) B334405559
theorem B297249385 : Blo 1905435 297249385 := bstep (se 2 (by rfl) ⟨111468519, by rfl⟩ : syracuseStep 297249385 = 222937039) B222937039
theorem B396332513 : Blo 1905435 396332513 := bstep (se 2 (by rfl) ⟨148624692, by rfl⟩ : syracuseStep 396332513 = 297249385) B297249385
theorem B264221675 : Blo 1905435 264221675 := bstep (se 1 (by rfl) ⟨198166256, by rfl⟩ : syracuseStep 264221675 = 396332513) B396332513
theorem B176147783 : Blo 1905435 176147783 := bstep (se 1 (by rfl) ⟨132110837, by rfl⟩ : syracuseStep 176147783 = 264221675) B264221675
theorem B117431855 : Blo 1905435 117431855 := bstep (se 1 (by rfl) ⟨88073891, by rfl⟩ : syracuseStep 117431855 = 176147783) B176147783
theorem B78287903 : Blo 1905435 78287903 := bstep (se 1 (by rfl) ⟨58715927, by rfl⟩ : syracuseStep 78287903 = 117431855) B117431855
theorem B52191935 : Blo 1905435 52191935 := bstep (se 1 (by rfl) ⟨39143951, by rfl⟩ : syracuseStep 52191935 = 78287903) B78287903
theorem B34794623 : Blo 1905435 34794623 := bstep (se 1 (by rfl) ⟨26095967, by rfl⟩ : syracuseStep 34794623 = 52191935) B52191935
theorem B92785661 : Blo 1905435 92785661 := bstep (se 3 (by rfl) ⟨17397311, by rfl⟩ : syracuseStep 92785661 = 34794623) B34794623
theorem B61857107 : Blo 1905435 61857107 := bstep (se 1 (by rfl) ⟨46392830, by rfl⟩ : syracuseStep 61857107 = 92785661) B92785661
theorem B41238071 : Blo 1905435 41238071 := bstep (se 1 (by rfl) ⟨30928553, by rfl⟩ : syracuseStep 41238071 = 61857107) B61857107
theorem B27492047 : Blo 1905435 27492047 := bstep (se 1 (by rfl) ⟨20619035, by rfl⟩ : syracuseStep 27492047 = 41238071) B41238071
theorem B18328031 : Blo 1905435 18328031 := bstep (se 1 (by rfl) ⟨13746023, by rfl⟩ : syracuseStep 18328031 = 27492047) B27492047
theorem B12218687 : Blo 1905435 12218687 := bstep (se 1 (by rfl) ⟨9164015, by rfl⟩ : syracuseStep 12218687 = 18328031) B18328031
theorem B8145791 : Blo 1905435 8145791 := bstep (se 1 (by rfl) ⟨6109343, by rfl⟩ : syracuseStep 8145791 = 12218687) B12218687
theorem B5430527 : Blo 1905435 5430527 := bstep (se 1 (by rfl) ⟨4072895, by rfl⟩ : syracuseStep 5430527 = 8145791) B8145791
theorem B3620351 : Blo 1905435 3620351 := bstep (se 1 (by rfl) ⟨2715263, by rfl⟩ : syracuseStep 3620351 = 5430527) B5430527
theorem B2413567 : Blo 1905435 2413567 := bstep (se 1 (by rfl) ⟨1810175, by rfl⟩ : syracuseStep 2413567 = 3620351) B3620351
theorem B3218089 : Blo 1905435 3218089 := bstep (se 2 (by rfl) ⟨1206783, by rfl⟩ : syracuseStep 3218089 = 2413567) B2413567
theorem B4290785 : Blo 1905435 4290785 := bstep (se 2 (by rfl) ⟨1609044, by rfl⟩ : syracuseStep 4290785 = 3218089) B3218089
theorem B2860523 : Blo 1905435 2860523 := bstep (se 1 (by rfl) ⟨2145392, by rfl⟩ : syracuseStep 2860523 = 4290785) B4290785
theorem B1907015 : Blo 1905435 1907015 := bstep (se 1 (by rfl) ⟨1430261, by rfl⟩ : syracuseStep 1907015 = 2860523) B2860523
theorem B2145397 : Blo 1905435 2145397 := bbase (se 5 (by rfl) ⟨100565, by rfl⟩ : syracuseStep 2145397 = 201131) (by norm_num)
theorem B2860529 : Blo 1905435 2860529 := bstep (se 2 (by rfl) ⟨1072698, by rfl⟩ : syracuseStep 2860529 = 2145397) B2145397
theorem B1907019 : Blo 1905435 1907019 := bstep (se 1 (by rfl) ⟨1430264, by rfl⟩ : syracuseStep 1907019 = 2860529) B2860529
theorem B2413577 : Blo 1905435 2413577 := bbase (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) (by norm_num)
theorem B6436205 : Blo 1905435 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B4290803 : Blo 1905435 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B2860535 : Blo 1905435 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B1907023 : Blo 1905435 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B2860541 : Blo 1905435 2860541 := bbase (se 3 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 2860541 = 1072703) (by norm_num)
theorem B1907027 : Blo 1905435 1907027 := bstep (se 1 (by rfl) ⟨1430270, by rfl⟩ : syracuseStep 1907027 = 2860541) B2860541
theorem B4290821 : Blo 1905435 4290821 := bbase (se 4 (by rfl) ⟨402264, by rfl⟩ : syracuseStep 4290821 = 804529) (by norm_num)
theorem B2860547 : Blo 1905435 2860547 := bstep (se 1 (by rfl) ⟨2145410, by rfl⟩ : syracuseStep 2860547 = 4290821) B4290821
theorem B1907031 : Blo 1905435 1907031 := bstep (se 1 (by rfl) ⟨1430273, by rfl⟩ : syracuseStep 1907031 = 2860547) B2860547
theorem B3620389 : Blo 1905435 3620389 := bbase (se 4 (by rfl) ⟨339411, by rfl⟩ : syracuseStep 3620389 = 678823) (by norm_num)
theorem B4827185 : Blo 1905435 4827185 := bstep (se 2 (by rfl) ⟨1810194, by rfl⟩ : syracuseStep 4827185 = 3620389) B3620389
theorem B3218123 : Blo 1905435 3218123 := bstep (se 1 (by rfl) ⟨2413592, by rfl⟩ : syracuseStep 3218123 = 4827185) B4827185
theorem B2145415 : Blo 1905435 2145415 := bstep (se 1 (by rfl) ⟨1609061, by rfl⟩ : syracuseStep 2145415 = 3218123) B3218123
theorem B2860553 : Blo 1905435 2860553 := bstep (se 2 (by rfl) ⟨1072707, by rfl⟩ : syracuseStep 2860553 = 2145415) B2145415
theorem B1907035 : Blo 1905435 1907035 := bstep (se 1 (by rfl) ⟨1430276, by rfl⟩ : syracuseStep 1907035 = 2860553) B2860553
theorem B9654389 : Blo 1905435 9654389 := bbase (se 5 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 9654389 = 905099) (by norm_num)
theorem B6436259 : Blo 1905435 6436259 := bstep (se 1 (by rfl) ⟨4827194, by rfl⟩ : syracuseStep 6436259 = 9654389) B9654389
theorem B4290839 : Blo 1905435 4290839 := bstep (se 1 (by rfl) ⟨3218129, by rfl⟩ : syracuseStep 4290839 = 6436259) B6436259
theorem B2860559 : Blo 1905435 2860559 := bstep (se 1 (by rfl) ⟨2145419, by rfl⟩ : syracuseStep 2860559 = 4290839) B4290839
theorem B1907039 : Blo 1905435 1907039 := bstep (se 1 (by rfl) ⟨1430279, by rfl⟩ : syracuseStep 1907039 = 2860559) B2860559
theorem B2860565 : Blo 1905435 2860565 := bbase (se 6 (by rfl) ⟨67044, by rfl⟩ : syracuseStep 2860565 = 134089) (by norm_num)
theorem B1907043 : Blo 1905435 1907043 := bstep (se 1 (by rfl) ⟨1430282, by rfl⟩ : syracuseStep 1907043 = 2860565) B2860565
theorem B6109445 : Blo 1905435 6109445 := bbase (se 4 (by rfl) ⟨572760, by rfl⟩ : syracuseStep 6109445 = 1145521) (by norm_num)
theorem B16291853 : Blo 1905435 16291853 := bstep (se 3 (by rfl) ⟨3054722, by rfl⟩ : syracuseStep 16291853 = 6109445) B6109445
theorem B10861235 : Blo 1905435 10861235 := bstep (se 1 (by rfl) ⟨8145926, by rfl⟩ : syracuseStep 10861235 = 16291853) B16291853
theorem B7240823 : Blo 1905435 7240823 := bstep (se 1 (by rfl) ⟨5430617, by rfl⟩ : syracuseStep 7240823 = 10861235) B10861235
theorem B4827215 : Blo 1905435 4827215 := bstep (se 1 (by rfl) ⟨3620411, by rfl⟩ : syracuseStep 4827215 = 7240823) B7240823
theorem B3218143 : Blo 1905435 3218143 := bstep (se 1 (by rfl) ⟨2413607, by rfl⟩ : syracuseStep 3218143 = 4827215) B4827215
theorem B4290857 : Blo 1905435 4290857 := bstep (se 2 (by rfl) ⟨1609071, by rfl⟩ : syracuseStep 4290857 = 3218143) B3218143
theorem B2860571 : Blo 1905435 2860571 := bstep (se 1 (by rfl) ⟨2145428, by rfl⟩ : syracuseStep 2860571 = 4290857) B4290857
theorem B1907047 : Blo 1905435 1907047 := bstep (se 1 (by rfl) ⟨1430285, by rfl⟩ : syracuseStep 1907047 = 2860571) B2860571
theorem B2145433 : Blo 1905435 2145433 := bbase (se 2 (by rfl) ⟨804537, by rfl⟩ : syracuseStep 2145433 = 1609075) (by norm_num)
theorem B2860577 : Blo 1905435 2860577 := bstep (se 2 (by rfl) ⟨1072716, by rfl⟩ : syracuseStep 2860577 = 2145433) B2145433
theorem B1907051 : Blo 1905435 1907051 := bstep (se 1 (by rfl) ⟨1430288, by rfl⟩ : syracuseStep 1907051 = 2860577) B2860577
theorem B7240853 : Blo 1905435 7240853 := bbase (se 6 (by rfl) ⟨169707, by rfl⟩ : syracuseStep 7240853 = 339415) (by norm_num)
theorem B4827235 : Blo 1905435 4827235 := bstep (se 1 (by rfl) ⟨3620426, by rfl⟩ : syracuseStep 4827235 = 7240853) B7240853
theorem B6436313 : Blo 1905435 6436313 := bstep (se 2 (by rfl) ⟨2413617, by rfl⟩ : syracuseStep 6436313 = 4827235) B4827235
theorem B4290875 : Blo 1905435 4290875 := bstep (se 1 (by rfl) ⟨3218156, by rfl⟩ : syracuseStep 4290875 = 6436313) B6436313
theorem B2860583 : Blo 1905435 2860583 := bstep (se 1 (by rfl) ⟨2145437, by rfl⟩ : syracuseStep 2860583 = 4290875) B4290875
theorem B1907055 : Blo 1905435 1907055 := bstep (se 1 (by rfl) ⟨1430291, by rfl⟩ : syracuseStep 1907055 = 2860583) B2860583
theorem B2860589 : Blo 1905435 2860589 := bbase (se 3 (by rfl) ⟨536360, by rfl⟩ : syracuseStep 2860589 = 1072721) (by norm_num)
theorem B1907059 : Blo 1905435 1907059 := bstep (se 1 (by rfl) ⟨1430294, by rfl⟩ : syracuseStep 1907059 = 2860589) B2860589
theorem B4290893 : Blo 1905435 4290893 := bbase (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) (by norm_num)
theorem B2860595 : Blo 1905435 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B1907063 : Blo 1905435 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B2413633 : Blo 1905435 2413633 := bbase (se 2 (by rfl) ⟨905112, by rfl⟩ : syracuseStep 2413633 = 1810225) (by norm_num)
theorem B3218177 : Blo 1905435 3218177 := bstep (se 2 (by rfl) ⟨1206816, by rfl⟩ : syracuseStep 3218177 = 2413633) B2413633
theorem B2145451 : Blo 1905435 2145451 := bstep (se 1 (by rfl) ⟨1609088, by rfl⟩ : syracuseStep 2145451 = 3218177) B3218177
theorem B2860601 : Blo 1905435 2860601 := bstep (se 2 (by rfl) ⟨1072725, by rfl⟩ : syracuseStep 2860601 = 2145451) B2145451
theorem B1907067 : Blo 1905435 1907067 := bstep (se 1 (by rfl) ⟨1430300, by rfl⟩ : syracuseStep 1907067 = 2860601) B2860601
theorem B4644661 : Blo 1905435 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B6192881 : Blo 1905435 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B4128587 : Blo 1905435 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B2752391 : Blo 1905435 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B7339709 : Blo 1905435 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B4893139 : Blo 1905435 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B26096741 : Blo 1905435 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B17397827 : Blo 1905435 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B11598551 : Blo 1905435 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B7732367 : Blo 1905435 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B5154911 : Blo 1905435 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B3436607 : Blo 1905435 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B2291071 : Blo 1905435 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B3054761 : Blo 1905435 3054761 := bstep (se 2 (by rfl) ⟨1145535, by rfl⟩ : syracuseStep 3054761 = 2291071) B2291071
theorem B2036507 : Blo 1905435 2036507 := bstep (se 1 (by rfl) ⟨1527380, by rfl⟩ : syracuseStep 2036507 = 3054761) B3054761
theorem B21722741 : Blo 1905435 21722741 := bstep (se 5 (by rfl) ⟨1018253, by rfl⟩ : syracuseStep 21722741 = 2036507) B2036507
theorem B14481827 : Blo 1905435 14481827 := bstep (se 1 (by rfl) ⟨10861370, by rfl⟩ : syracuseStep 14481827 = 21722741) B21722741
theorem B9654551 : Blo 1905435 9654551 := bstep (se 1 (by rfl) ⟨7240913, by rfl⟩ : syracuseStep 9654551 = 14481827) B14481827
theorem B6436367 : Blo 1905435 6436367 := bstep (se 1 (by rfl) ⟨4827275, by rfl⟩ : syracuseStep 6436367 = 9654551) B9654551
theorem B4290911 : Blo 1905435 4290911 := bstep (se 1 (by rfl) ⟨3218183, by rfl⟩ : syracuseStep 4290911 = 6436367) B6436367
theorem B2860607 : Blo 1905435 2860607 := bstep (se 1 (by rfl) ⟨2145455, by rfl⟩ : syracuseStep 2860607 = 4290911) B4290911
theorem B1907071 : Blo 1905435 1907071 := bstep (se 1 (by rfl) ⟨1430303, by rfl⟩ : syracuseStep 1907071 = 2860607) B2860607
theorem B2860613 : Blo 1905435 2860613 := bbase (se 4 (by rfl) ⟨268182, by rfl⟩ : syracuseStep 2860613 = 536365) (by norm_num)
theorem B1907075 : Blo 1905435 1907075 := bstep (se 1 (by rfl) ⟨1430306, by rfl⟩ : syracuseStep 1907075 = 2860613) B2860613
theorem B3218197 : Blo 1905435 3218197 := bbase (se 6 (by rfl) ⟨75426, by rfl⟩ : syracuseStep 3218197 = 150853) (by norm_num)
theorem B4290929 : Blo 1905435 4290929 := bstep (se 2 (by rfl) ⟨1609098, by rfl⟩ : syracuseStep 4290929 = 3218197) B3218197
theorem B2860619 : Blo 1905435 2860619 := bstep (se 1 (by rfl) ⟨2145464, by rfl⟩ : syracuseStep 2860619 = 4290929) B4290929
theorem B1907079 : Blo 1905435 1907079 := bstep (se 1 (by rfl) ⟨1430309, by rfl⟩ : syracuseStep 1907079 = 2860619) B2860619
theorem B2145469 : Blo 1905435 2145469 := bbase (se 3 (by rfl) ⟨402275, by rfl⟩ : syracuseStep 2145469 = 804551) (by norm_num)
theorem B2860625 : Blo 1905435 2860625 := bstep (se 2 (by rfl) ⟨1072734, by rfl⟩ : syracuseStep 2860625 = 2145469) B2145469
theorem B1907083 : Blo 1905435 1907083 := bstep (se 1 (by rfl) ⟨1430312, by rfl⟩ : syracuseStep 1907083 = 2860625) B2860625
theorem B6436421 : Blo 1905435 6436421 := bbase (se 4 (by rfl) ⟨603414, by rfl⟩ : syracuseStep 6436421 = 1206829) (by norm_num)
theorem B4290947 : Blo 1905435 4290947 := bstep (se 1 (by rfl) ⟨3218210, by rfl⟩ : syracuseStep 4290947 = 6436421) B6436421
theorem B2860631 : Blo 1905435 2860631 := bstep (se 1 (by rfl) ⟨2145473, by rfl⟩ : syracuseStep 2860631 = 4290947) B4290947
theorem B1907087 : Blo 1905435 1907087 := bstep (se 1 (by rfl) ⟨1430315, by rfl⟩ : syracuseStep 1907087 = 2860631) B2860631
theorem B2860637 : Blo 1905435 2860637 := bbase (se 3 (by rfl) ⟨536369, by rfl⟩ : syracuseStep 2860637 = 1072739) (by norm_num)
theorem B1907091 : Blo 1905435 1907091 := bstep (se 1 (by rfl) ⟨1430318, by rfl⟩ : syracuseStep 1907091 = 2860637) B2860637
theorem B4290965 : Blo 1905435 4290965 := bbase (se 6 (by rfl) ⟨100569, by rfl⟩ : syracuseStep 4290965 = 201139) (by norm_num)
theorem B2860643 : Blo 1905435 2860643 := bstep (se 1 (by rfl) ⟨2145482, by rfl⟩ : syracuseStep 2860643 = 4290965) B4290965
theorem B1907095 : Blo 1905435 1907095 := bstep (se 1 (by rfl) ⟨1430321, by rfl⟩ : syracuseStep 1907095 = 2860643) B2860643
theorem B2291105 : Blo 1905435 2291105 := bbase (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) (by norm_num)
theorem B6109613 : Blo 1905435 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B4073075 : Blo 1905435 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B2715383 : Blo 1905435 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B7241021 : Blo 1905435 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B4827347 : Blo 1905435 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B3218231 : Blo 1905435 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B2145487 : Blo 1905435 2145487 := bstep (se 1 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 2145487 = 3218231) B3218231
theorem B2860649 : Blo 1905435 2860649 := bstep (se 2 (by rfl) ⟨1072743, by rfl⟩ : syracuseStep 2860649 = 2145487) B2145487
theorem B1907099 : Blo 1905435 1907099 := bstep (se 1 (by rfl) ⟨1430324, by rfl⟩ : syracuseStep 1907099 = 2860649) B2860649
theorem B8146165 : Blo 1905435 8146165 := bbase (se 5 (by rfl) ⟨381851, by rfl⟩ : syracuseStep 8146165 = 763703) (by norm_num)
theorem B10861553 : Blo 1905435 10861553 := bstep (se 2 (by rfl) ⟨4073082, by rfl⟩ : syracuseStep 10861553 = 8146165) B8146165
theorem B7241035 : Blo 1905435 7241035 := bstep (se 1 (by rfl) ⟨5430776, by rfl⟩ : syracuseStep 7241035 = 10861553) B10861553
theorem B9654713 : Blo 1905435 9654713 := bstep (se 2 (by rfl) ⟨3620517, by rfl⟩ : syracuseStep 9654713 = 7241035) B7241035
theorem B6436475 : Blo 1905435 6436475 := bstep (se 1 (by rfl) ⟨4827356, by rfl⟩ : syracuseStep 6436475 = 9654713) B9654713
theorem B4290983 : Blo 1905435 4290983 := bstep (se 1 (by rfl) ⟨3218237, by rfl⟩ : syracuseStep 4290983 = 6436475) B6436475
theorem B2860655 : Blo 1905435 2860655 := bstep (se 1 (by rfl) ⟨2145491, by rfl⟩ : syracuseStep 2860655 = 4290983) B4290983
theorem B1907103 : Blo 1905435 1907103 := bstep (se 1 (by rfl) ⟨1430327, by rfl⟩ : syracuseStep 1907103 = 2860655) B2860655
theorem B2860661 : Blo 1905435 2860661 := bbase (se 5 (by rfl) ⟨134093, by rfl⟩ : syracuseStep 2860661 = 268187) (by norm_num)
theorem B1907107 : Blo 1905435 1907107 := bstep (se 1 (by rfl) ⟨1430330, by rfl⟩ : syracuseStep 1907107 = 2860661) B2860661
theorem B3620533 : Blo 1905435 3620533 := bbase (se 5 (by rfl) ⟨169712, by rfl⟩ : syracuseStep 3620533 = 339425) (by norm_num)
theorem B4827377 : Blo 1905435 4827377 := bstep (se 2 (by rfl) ⟨1810266, by rfl⟩ : syracuseStep 4827377 = 3620533) B3620533
theorem B3218251 : Blo 1905435 3218251 := bstep (se 1 (by rfl) ⟨2413688, by rfl⟩ : syracuseStep 3218251 = 4827377) B4827377
theorem B4291001 : Blo 1905435 4291001 := bstep (se 2 (by rfl) ⟨1609125, by rfl⟩ : syracuseStep 4291001 = 3218251) B3218251
theorem B2860667 : Blo 1905435 2860667 := bstep (se 1 (by rfl) ⟨2145500, by rfl⟩ : syracuseStep 2860667 = 4291001) B4291001
theorem B1907111 : Blo 1905435 1907111 := bstep (se 1 (by rfl) ⟨1430333, by rfl⟩ : syracuseStep 1907111 = 2860667) B2860667
theorem B2145505 : Blo 1905435 2145505 := bbase (se 2 (by rfl) ⟨804564, by rfl⟩ : syracuseStep 2145505 = 1609129) (by norm_num)
theorem B2860673 : Blo 1905435 2860673 := bstep (se 2 (by rfl) ⟨1072752, by rfl⟩ : syracuseStep 2860673 = 2145505) B2145505
theorem B1907115 : Blo 1905435 1907115 := bstep (se 1 (by rfl) ⟨1430336, by rfl⟩ : syracuseStep 1907115 = 2860673) B2860673
theorem B4827397 : Blo 1905435 4827397 := bbase (se 4 (by rfl) ⟨452568, by rfl⟩ : syracuseStep 4827397 = 905137) (by norm_num)
theorem B6436529 : Blo 1905435 6436529 := bstep (se 2 (by rfl) ⟨2413698, by rfl⟩ : syracuseStep 6436529 = 4827397) B4827397
theorem B4291019 : Blo 1905435 4291019 := bstep (se 1 (by rfl) ⟨3218264, by rfl⟩ : syracuseStep 4291019 = 6436529) B6436529
theorem B2860679 : Blo 1905435 2860679 := bstep (se 1 (by rfl) ⟨2145509, by rfl⟩ : syracuseStep 2860679 = 4291019) B4291019
theorem B1907119 : Blo 1905435 1907119 := bstep (se 1 (by rfl) ⟨1430339, by rfl⟩ : syracuseStep 1907119 = 2860679) B2860679
theorem B2860685 : Blo 1905435 2860685 := bbase (se 3 (by rfl) ⟨536378, by rfl⟩ : syracuseStep 2860685 = 1072757) (by norm_num)
theorem B1907123 : Blo 1905435 1907123 := bstep (se 1 (by rfl) ⟨1430342, by rfl⟩ : syracuseStep 1907123 = 2860685) B2860685
theorem B4291037 : Blo 1905435 4291037 := bbase (se 3 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 4291037 = 1609139) (by norm_num)
theorem B2860691 : Blo 1905435 2860691 := bstep (se 1 (by rfl) ⟨2145518, by rfl⟩ : syracuseStep 2860691 = 4291037) B4291037
theorem B1907127 : Blo 1905435 1907127 := bstep (se 1 (by rfl) ⟨1430345, by rfl⟩ : syracuseStep 1907127 = 2860691) B2860691
theorem B3218285 : Blo 1905435 3218285 := bbase (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) (by norm_num)
theorem B2145523 : Blo 1905435 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B2860697 : Blo 1905435 2860697 := bstep (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) B2145523
theorem B1907131 : Blo 1905435 1907131 := bstep (se 1 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 1907131 = 2860697) B2860697
theorem B18579253 : Blo 1905435 18579253 := bbase (se 5 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 18579253 = 1741805) (by norm_num)
theorem B24772337 : Blo 1905435 24772337 := bstep (se 2 (by rfl) ⟨9289626, by rfl⟩ : syracuseStep 24772337 = 18579253) B18579253
theorem B16514891 : Blo 1905435 16514891 := bstep (se 1 (by rfl) ⟨12386168, by rfl⟩ : syracuseStep 16514891 = 24772337) B24772337
theorem B11009927 : Blo 1905435 11009927 := bstep (se 1 (by rfl) ⟨8257445, by rfl⟩ : syracuseStep 11009927 = 16514891) B16514891
theorem B7339951 : Blo 1905435 7339951 := bstep (se 1 (by rfl) ⟨5504963, by rfl⟩ : syracuseStep 7339951 = 11009927) B11009927
theorem B9786601 : Blo 1905435 9786601 := bstep (se 2 (by rfl) ⟨3669975, by rfl⟩ : syracuseStep 9786601 = 7339951) B7339951
theorem B52195205 : Blo 1905435 52195205 := bstep (se 4 (by rfl) ⟨4893300, by rfl⟩ : syracuseStep 52195205 = 9786601) B9786601
theorem B34796803 : Blo 1905435 34796803 := bstep (se 1 (by rfl) ⟨26097602, by rfl⟩ : syracuseStep 34796803 = 52195205) B52195205
theorem B46395737 : Blo 1905435 46395737 := bstep (se 2 (by rfl) ⟨17398401, by rfl⟩ : syracuseStep 46395737 = 34796803) B34796803
theorem B30930491 : Blo 1905435 30930491 := bstep (se 1 (by rfl) ⟨23197868, by rfl⟩ : syracuseStep 30930491 = 46395737) B46395737
theorem B20620327 : Blo 1905435 20620327 := bstep (se 1 (by rfl) ⟨15465245, by rfl⟩ : syracuseStep 20620327 = 30930491) B30930491
theorem B27493769 : Blo 1905435 27493769 := bstep (se 2 (by rfl) ⟨10310163, by rfl⟩ : syracuseStep 27493769 = 20620327) B20620327
theorem B18329179 : Blo 1905435 18329179 := bstep (se 1 (by rfl) ⟨13746884, by rfl⟩ : syracuseStep 18329179 = 27493769) B27493769
theorem B24438905 : Blo 1905435 24438905 := bstep (se 2 (by rfl) ⟨9164589, by rfl⟩ : syracuseStep 24438905 = 18329179) B18329179
theorem B16292603 : Blo 1905435 16292603 := bstep (se 1 (by rfl) ⟨12219452, by rfl⟩ : syracuseStep 16292603 = 24438905) B24438905
theorem B10861735 : Blo 1905435 10861735 := bstep (se 1 (by rfl) ⟨8146301, by rfl⟩ : syracuseStep 10861735 = 16292603) B16292603
theorem B14482313 : Blo 1905435 14482313 := bstep (se 2 (by rfl) ⟨5430867, by rfl⟩ : syracuseStep 14482313 = 10861735) B10861735
theorem B9654875 : Blo 1905435 9654875 := bstep (se 1 (by rfl) ⟨7241156, by rfl⟩ : syracuseStep 9654875 = 14482313) B14482313
theorem B6436583 : Blo 1905435 6436583 := bstep (se 1 (by rfl) ⟨4827437, by rfl⟩ : syracuseStep 6436583 = 9654875) B9654875
theorem B4291055 : Blo 1905435 4291055 := bstep (se 1 (by rfl) ⟨3218291, by rfl⟩ : syracuseStep 4291055 = 6436583) B6436583
theorem B2860703 : Blo 1905435 2860703 := bstep (se 1 (by rfl) ⟨2145527, by rfl⟩ : syracuseStep 2860703 = 4291055) B4291055
theorem B1907135 : Blo 1905435 1907135 := bstep (se 1 (by rfl) ⟨1430351, by rfl⟩ : syracuseStep 1907135 = 2860703) B2860703
theorem B2860709 : Blo 1905435 2860709 := bbase (se 4 (by rfl) ⟨268191, by rfl⟩ : syracuseStep 2860709 = 536383) (by norm_num)
theorem B1907139 : Blo 1905435 1907139 := bstep (se 1 (by rfl) ⟨1430354, by rfl⟩ : syracuseStep 1907139 = 2860709) B2860709
theorem B2413729 : Blo 1905435 2413729 := bbase (se 2 (by rfl) ⟨905148, by rfl⟩ : syracuseStep 2413729 = 1810297) (by norm_num)
theorem B3218305 : Blo 1905435 3218305 := bstep (se 2 (by rfl) ⟨1206864, by rfl⟩ : syracuseStep 3218305 = 2413729) B2413729
theorem B4291073 : Blo 1905435 4291073 := bstep (se 2 (by rfl) ⟨1609152, by rfl⟩ : syracuseStep 4291073 = 3218305) B3218305
theorem B2860715 : Blo 1905435 2860715 := bstep (se 1 (by rfl) ⟨2145536, by rfl⟩ : syracuseStep 2860715 = 4291073) B4291073
theorem B1907143 : Blo 1905435 1907143 := bstep (se 1 (by rfl) ⟨1430357, by rfl⟩ : syracuseStep 1907143 = 2860715) B2860715
theorem B2145541 : Blo 1905435 2145541 := bbase (se 4 (by rfl) ⟨201144, by rfl⟩ : syracuseStep 2145541 = 402289) (by norm_num)
theorem B2860721 : Blo 1905435 2860721 := bstep (se 2 (by rfl) ⟨1072770, by rfl⟩ : syracuseStep 2860721 = 2145541) B2145541
theorem B1907147 : Blo 1905435 1907147 := bstep (se 1 (by rfl) ⟨1430360, by rfl⟩ : syracuseStep 1907147 = 2860721) B2860721
theorem B2036593 : Blo 1905435 2036593 := bbase (se 2 (by rfl) ⟨763722, by rfl⟩ : syracuseStep 2036593 = 1527445) (by norm_num)
theorem B2715457 : Blo 1905435 2715457 := bstep (se 2 (by rfl) ⟨1018296, by rfl⟩ : syracuseStep 2715457 = 2036593) B2036593
theorem B3620609 : Blo 1905435 3620609 := bstep (se 2 (by rfl) ⟨1357728, by rfl⟩ : syracuseStep 3620609 = 2715457) B2715457
theorem B2413739 : Blo 1905435 2413739 := bstep (se 1 (by rfl) ⟨1810304, by rfl⟩ : syracuseStep 2413739 = 3620609) B3620609
theorem B6436637 : Blo 1905435 6436637 := bstep (se 3 (by rfl) ⟨1206869, by rfl⟩ : syracuseStep 6436637 = 2413739) B2413739
theorem B4291091 : Blo 1905435 4291091 := bstep (se 1 (by rfl) ⟨3218318, by rfl⟩ : syracuseStep 4291091 = 6436637) B6436637
theorem B2860727 : Blo 1905435 2860727 := bstep (se 1 (by rfl) ⟨2145545, by rfl⟩ : syracuseStep 2860727 = 4291091) B4291091
theorem B1907151 : Blo 1905435 1907151 := bstep (se 1 (by rfl) ⟨1430363, by rfl⟩ : syracuseStep 1907151 = 2860727) B2860727
theorem B2860733 : Blo 1905435 2860733 := bbase (se 3 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 2860733 = 1072775) (by norm_num)
theorem B1907155 : Blo 1905435 1907155 := bstep (se 1 (by rfl) ⟨1430366, by rfl⟩ : syracuseStep 1907155 = 2860733) B2860733
theorem B4291109 : Blo 1905435 4291109 := bbase (se 4 (by rfl) ⟨402291, by rfl⟩ : syracuseStep 4291109 = 804583) (by norm_num)
theorem B2860739 : Blo 1905435 2860739 := bstep (se 1 (by rfl) ⟨2145554, by rfl⟩ : syracuseStep 2860739 = 4291109) B4291109
theorem B1907159 : Blo 1905435 1907159 := bstep (se 1 (by rfl) ⟨1430369, by rfl⟩ : syracuseStep 1907159 = 2860739) B2860739
theorem B4827509 : Blo 1905435 4827509 := bbase (se 5 (by rfl) ⟨226289, by rfl⟩ : syracuseStep 4827509 = 452579) (by norm_num)
theorem B3218339 : Blo 1905435 3218339 := bstep (se 1 (by rfl) ⟨2413754, by rfl⟩ : syracuseStep 3218339 = 4827509) B4827509
theorem B2145559 : Blo 1905435 2145559 := bstep (se 1 (by rfl) ⟨1609169, by rfl⟩ : syracuseStep 2145559 = 3218339) B3218339
theorem B2860745 : Blo 1905435 2860745 := bstep (se 2 (by rfl) ⟨1072779, by rfl⟩ : syracuseStep 2860745 = 2145559) B2145559
theorem B1907163 : Blo 1905435 1907163 := bstep (se 1 (by rfl) ⟨1430372, by rfl⟩ : syracuseStep 1907163 = 2860745) B2860745
theorem B8257589 : Blo 1905435 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B5505059 : Blo 1905435 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B3670039 : Blo 1905435 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B4893385 : Blo 1905435 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B6524513 : Blo 1905435 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B4349675 : Blo 1905435 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B2899783 : Blo 1905435 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B3866377 : Blo 1905435 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B5155169 : Blo 1905435 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B13747117 : Blo 1905435 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B18329489 : Blo 1905435 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B12219659 : Blo 1905435 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B8146439 : Blo 1905435 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B5430959 : Blo 1905435 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B3620639 : Blo 1905435 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B9655037 : Blo 1905435 9655037 := bstep (se 3 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 9655037 = 3620639) B3620639
theorem B6436691 : Blo 1905435 6436691 := bstep (se 1 (by rfl) ⟨4827518, by rfl⟩ : syracuseStep 6436691 = 9655037) B9655037
theorem B4291127 : Blo 1905435 4291127 := bstep (se 1 (by rfl) ⟨3218345, by rfl⟩ : syracuseStep 4291127 = 6436691) B6436691
theorem B2860751 : Blo 1905435 2860751 := bstep (se 1 (by rfl) ⟨2145563, by rfl⟩ : syracuseStep 2860751 = 4291127) B4291127
theorem B1907167 : Blo 1905435 1907167 := bstep (se 1 (by rfl) ⟨1430375, by rfl⟩ : syracuseStep 1907167 = 2860751) B2860751
theorem B2860757 : Blo 1905435 2860757 := bbase (se 7 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 2860757 = 67049) (by norm_num)
theorem B1907171 : Blo 1905435 1907171 := bstep (se 1 (by rfl) ⟨1430378, by rfl⟩ : syracuseStep 1907171 = 2860757) B2860757
theorem B4073237 : Blo 1905435 4073237 := bbase (se 6 (by rfl) ⟨95466, by rfl⟩ : syracuseStep 4073237 = 190933) (by norm_num)
theorem B2715491 : Blo 1905435 2715491 := bstep (se 1 (by rfl) ⟨2036618, by rfl⟩ : syracuseStep 2715491 = 4073237) B4073237
theorem B7241309 : Blo 1905435 7241309 := bstep (se 3 (by rfl) ⟨1357745, by rfl⟩ : syracuseStep 7241309 = 2715491) B2715491
theorem B4827539 : Blo 1905435 4827539 := bstep (se 1 (by rfl) ⟨3620654, by rfl⟩ : syracuseStep 4827539 = 7241309) B7241309
theorem B3218359 : Blo 1905435 3218359 := bstep (se 1 (by rfl) ⟨2413769, by rfl⟩ : syracuseStep 3218359 = 4827539) B4827539
theorem B4291145 : Blo 1905435 4291145 := bstep (se 2 (by rfl) ⟨1609179, by rfl⟩ : syracuseStep 4291145 = 3218359) B3218359
theorem B2860763 : Blo 1905435 2860763 := bstep (se 1 (by rfl) ⟨2145572, by rfl⟩ : syracuseStep 2860763 = 4291145) B4291145
theorem B1907175 : Blo 1905435 1907175 := bstep (se 1 (by rfl) ⟨1430381, by rfl⟩ : syracuseStep 1907175 = 2860763) B2860763
theorem B2145577 : Blo 1905435 2145577 := bbase (se 2 (by rfl) ⟨804591, by rfl⟩ : syracuseStep 2145577 = 1609183) (by norm_num)
theorem B2860769 : Blo 1905435 2860769 := bstep (se 2 (by rfl) ⟨1072788, by rfl⟩ : syracuseStep 2860769 = 2145577) B2145577
theorem B1907179 : Blo 1905435 1907179 := bstep (se 1 (by rfl) ⟨1430384, by rfl⟩ : syracuseStep 1907179 = 2860769) B2860769
theorem B9164821 : Blo 1905435 9164821 := bbase (se 6 (by rfl) ⟨214800, by rfl⟩ : syracuseStep 9164821 = 429601) (by norm_num)
theorem B12219761 : Blo 1905435 12219761 := bstep (se 2 (by rfl) ⟨4582410, by rfl⟩ : syracuseStep 12219761 = 9164821) B9164821
theorem B8146507 : Blo 1905435 8146507 := bstep (se 1 (by rfl) ⟨6109880, by rfl⟩ : syracuseStep 8146507 = 12219761) B12219761
theorem B10862009 : Blo 1905435 10862009 := bstep (se 2 (by rfl) ⟨4073253, by rfl⟩ : syracuseStep 10862009 = 8146507) B8146507
theorem B7241339 : Blo 1905435 7241339 := bstep (se 1 (by rfl) ⟨5431004, by rfl⟩ : syracuseStep 7241339 = 10862009) B10862009
theorem B4827559 : Blo 1905435 4827559 := bstep (se 1 (by rfl) ⟨3620669, by rfl⟩ : syracuseStep 4827559 = 7241339) B7241339
theorem B6436745 : Blo 1905435 6436745 := bstep (se 2 (by rfl) ⟨2413779, by rfl⟩ : syracuseStep 6436745 = 4827559) B4827559
theorem B4291163 : Blo 1905435 4291163 := bstep (se 1 (by rfl) ⟨3218372, by rfl⟩ : syracuseStep 4291163 = 6436745) B6436745
theorem B2860775 : Blo 1905435 2860775 := bstep (se 1 (by rfl) ⟨2145581, by rfl⟩ : syracuseStep 2860775 = 4291163) B4291163
theorem B1907183 : Blo 1905435 1907183 := bstep (se 1 (by rfl) ⟨1430387, by rfl⟩ : syracuseStep 1907183 = 2860775) B2860775
theorem B2860781 : Blo 1905435 2860781 := bbase (se 3 (by rfl) ⟨536396, by rfl⟩ : syracuseStep 2860781 = 1072793) (by norm_num)
theorem B1907187 : Blo 1905435 1907187 := bstep (se 1 (by rfl) ⟨1430390, by rfl⟩ : syracuseStep 1907187 = 2860781) B2860781
theorem B4291181 : Blo 1905435 4291181 := bbase (se 3 (by rfl) ⟨804596, by rfl⟩ : syracuseStep 4291181 = 1609193) (by norm_num)
theorem B2860787 : Blo 1905435 2860787 := bstep (se 1 (by rfl) ⟨2145590, by rfl⟩ : syracuseStep 2860787 = 4291181) B4291181
theorem B1907191 : Blo 1905435 1907191 := bstep (se 1 (by rfl) ⟨1430393, by rfl⟩ : syracuseStep 1907191 = 2860787) B2860787
theorem B3620693 : Blo 1905435 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B2413795 : Blo 1905435 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B3218393 : Blo 1905435 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B2145595 : Blo 1905435 2145595 := bstep (se 1 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 2145595 = 3218393) B3218393
theorem B2860793 : Blo 1905435 2860793 := bstep (se 2 (by rfl) ⟨1072797, by rfl⟩ : syracuseStep 2860793 = 2145595) B2145595
theorem B1907195 : Blo 1905435 1907195 := bstep (se 1 (by rfl) ⟨1430396, by rfl⟩ : syracuseStep 1907195 = 2860793) B2860793
theorem B2446733 : Blo 1905435 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B6524621 : Blo 1905435 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B4349747 : Blo 1905435 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B2899831 : Blo 1905435 2899831 := bstep (se 1 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 2899831 = 4349747) B4349747
theorem B3866441 : Blo 1905435 3866441 := bstep (se 2 (by rfl) ⟨1449915, by rfl⟩ : syracuseStep 3866441 = 2899831) B2899831
theorem B10310509 : Blo 1905435 10310509 := bstep (se 3 (by rfl) ⟨1933220, by rfl⟩ : syracuseStep 10310509 = 3866441) B3866441
theorem B54989381 : Blo 1905435 54989381 := bstep (se 4 (by rfl) ⟨5155254, by rfl⟩ : syracuseStep 54989381 = 10310509) B10310509
theorem B36659587 : Blo 1905435 36659587 := bstep (se 1 (by rfl) ⟨27494690, by rfl⟩ : syracuseStep 36659587 = 54989381) B54989381
theorem B48879449 : Blo 1905435 48879449 := bstep (se 2 (by rfl) ⟨18329793, by rfl⟩ : syracuseStep 48879449 = 36659587) B36659587
theorem B32586299 : Blo 1905435 32586299 := bstep (se 1 (by rfl) ⟨24439724, by rfl⟩ : syracuseStep 32586299 = 48879449) B48879449
theorem B21724199 : Blo 1905435 21724199 := bstep (se 1 (by rfl) ⟨16293149, by rfl⟩ : syracuseStep 21724199 = 32586299) B32586299
theorem B14482799 : Blo 1905435 14482799 := bstep (se 1 (by rfl) ⟨10862099, by rfl⟩ : syracuseStep 14482799 = 21724199) B21724199
theorem B9655199 : Blo 1905435 9655199 := bstep (se 1 (by rfl) ⟨7241399, by rfl⟩ : syracuseStep 9655199 = 14482799) B14482799
theorem B6436799 : Blo 1905435 6436799 := bstep (se 1 (by rfl) ⟨4827599, by rfl⟩ : syracuseStep 6436799 = 9655199) B9655199
theorem B4291199 : Blo 1905435 4291199 := bstep (se 1 (by rfl) ⟨3218399, by rfl⟩ : syracuseStep 4291199 = 6436799) B6436799
theorem B2860799 : Blo 1905435 2860799 := bstep (se 1 (by rfl) ⟨2145599, by rfl⟩ : syracuseStep 2860799 = 4291199) B4291199
theorem B1907199 : Blo 1905435 1907199 := bstep (se 1 (by rfl) ⟨1430399, by rfl⟩ : syracuseStep 1907199 = 2860799) B2860799
theorem B2860805 : Blo 1905435 2860805 := bbase (se 4 (by rfl) ⟨268200, by rfl⟩ : syracuseStep 2860805 = 536401) (by norm_num)
theorem B1907203 : Blo 1905435 1907203 := bstep (se 1 (by rfl) ⟨1430402, by rfl⟩ : syracuseStep 1907203 = 2860805) B2860805
theorem B3218413 : Blo 1905435 3218413 := bbase (se 3 (by rfl) ⟨603452, by rfl⟩ : syracuseStep 3218413 = 1206905) (by norm_num)
theorem B4291217 : Blo 1905435 4291217 := bstep (se 2 (by rfl) ⟨1609206, by rfl⟩ : syracuseStep 4291217 = 3218413) B3218413
theorem B2860811 : Blo 1905435 2860811 := bstep (se 1 (by rfl) ⟨2145608, by rfl⟩ : syracuseStep 2860811 = 4291217) B4291217
theorem B1907207 : Blo 1905435 1907207 := bstep (se 1 (by rfl) ⟨1430405, by rfl⟩ : syracuseStep 1907207 = 2860811) B2860811
theorem B2145613 : Blo 1905435 2145613 := bbase (se 3 (by rfl) ⟨402302, by rfl⟩ : syracuseStep 2145613 = 804605) (by norm_num)
theorem B2860817 : Blo 1905435 2860817 := bstep (se 2 (by rfl) ⟨1072806, by rfl⟩ : syracuseStep 2860817 = 2145613) B2145613
theorem B1907211 : Blo 1905435 1907211 := bstep (se 1 (by rfl) ⟨1430408, by rfl⟩ : syracuseStep 1907211 = 2860817) B2860817
theorem B6436853 : Blo 1905435 6436853 := bbase (se 5 (by rfl) ⟨301727, by rfl⟩ : syracuseStep 6436853 = 603455) (by norm_num)
theorem B4291235 : Blo 1905435 4291235 := bstep (se 1 (by rfl) ⟨3218426, by rfl⟩ : syracuseStep 4291235 = 6436853) B6436853
theorem B2860823 : Blo 1905435 2860823 := bstep (se 1 (by rfl) ⟨2145617, by rfl⟩ : syracuseStep 2860823 = 4291235) B4291235
theorem B1907215 : Blo 1905435 1907215 := bstep (se 1 (by rfl) ⟨1430411, by rfl⟩ : syracuseStep 1907215 = 2860823) B2860823
theorem B2860829 : Blo 1905435 2860829 := bbase (se 3 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 2860829 = 1072811) (by norm_num)
theorem B1907219 : Blo 1905435 1907219 := bstep (se 1 (by rfl) ⟨1430414, by rfl⟩ : syracuseStep 1907219 = 2860829) B2860829
theorem B4291253 : Blo 1905435 4291253 := bbase (se 5 (by rfl) ⟨201152, by rfl⟩ : syracuseStep 4291253 = 402305) (by norm_num)
theorem B2860835 : Blo 1905435 2860835 := bstep (se 1 (by rfl) ⟨2145626, by rfl⟩ : syracuseStep 2860835 = 4291253) B4291253
theorem B1907223 : Blo 1905435 1907223 := bstep (se 1 (by rfl) ⟨1430417, by rfl⟩ : syracuseStep 1907223 = 2860835) B2860835
theorem B10862261 : Blo 1905435 10862261 := bbase (se 5 (by rfl) ⟨509168, by rfl⟩ : syracuseStep 10862261 = 1018337) (by norm_num)
theorem B7241507 : Blo 1905435 7241507 := bstep (se 1 (by rfl) ⟨5431130, by rfl⟩ : syracuseStep 7241507 = 10862261) B10862261
theorem B4827671 : Blo 1905435 4827671 := bstep (se 1 (by rfl) ⟨3620753, by rfl⟩ : syracuseStep 4827671 = 7241507) B7241507
theorem B3218447 : Blo 1905435 3218447 := bstep (se 1 (by rfl) ⟨2413835, by rfl⟩ : syracuseStep 3218447 = 4827671) B4827671
theorem B2145631 : Blo 1905435 2145631 := bstep (se 1 (by rfl) ⟨1609223, by rfl⟩ : syracuseStep 2145631 = 3218447) B3218447
theorem B2860841 : Blo 1905435 2860841 := bstep (se 2 (by rfl) ⟨1072815, by rfl⟩ : syracuseStep 2860841 = 2145631) B2145631
theorem B1907227 : Blo 1905435 1907227 := bstep (se 1 (by rfl) ⟨1430420, by rfl⟩ : syracuseStep 1907227 = 2860841) B2860841
theorem B5431141 : Blo 1905435 5431141 := bbase (se 4 (by rfl) ⟨509169, by rfl⟩ : syracuseStep 5431141 = 1018339) (by norm_num)
theorem B7241521 : Blo 1905435 7241521 := bstep (se 2 (by rfl) ⟨2715570, by rfl⟩ : syracuseStep 7241521 = 5431141) B5431141
theorem B9655361 : Blo 1905435 9655361 := bstep (se 2 (by rfl) ⟨3620760, by rfl⟩ : syracuseStep 9655361 = 7241521) B7241521
theorem B6436907 : Blo 1905435 6436907 := bstep (se 1 (by rfl) ⟨4827680, by rfl⟩ : syracuseStep 6436907 = 9655361) B9655361
theorem B4291271 : Blo 1905435 4291271 := bstep (se 1 (by rfl) ⟨3218453, by rfl⟩ : syracuseStep 4291271 = 6436907) B6436907
theorem B2860847 : Blo 1905435 2860847 := bstep (se 1 (by rfl) ⟨2145635, by rfl⟩ : syracuseStep 2860847 = 4291271) B4291271
theorem B1907231 : Blo 1905435 1907231 := bstep (se 1 (by rfl) ⟨1430423, by rfl⟩ : syracuseStep 1907231 = 2860847) B2860847
theorem B2860853 : Blo 1905435 2860853 := bbase (se 5 (by rfl) ⟨134102, by rfl⟩ : syracuseStep 2860853 = 268205) (by norm_num)
theorem B1907235 : Blo 1905435 1907235 := bstep (se 1 (by rfl) ⟨1430426, by rfl⟩ : syracuseStep 1907235 = 2860853) B2860853
theorem B4827701 : Blo 1905435 4827701 := bbase (se 5 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 4827701 = 452597) (by norm_num)
theorem B3218467 : Blo 1905435 3218467 := bstep (se 1 (by rfl) ⟨2413850, by rfl⟩ : syracuseStep 3218467 = 4827701) B4827701
theorem B4291289 : Blo 1905435 4291289 := bstep (se 2 (by rfl) ⟨1609233, by rfl⟩ : syracuseStep 4291289 = 3218467) B3218467
theorem B2860859 : Blo 1905435 2860859 := bstep (se 1 (by rfl) ⟨2145644, by rfl⟩ : syracuseStep 2860859 = 4291289) B4291289
theorem B1907239 : Blo 1905435 1907239 := bstep (se 1 (by rfl) ⟨1430429, by rfl⟩ : syracuseStep 1907239 = 2860859) B2860859
theorem B2145649 : Blo 1905435 2145649 := bbase (se 2 (by rfl) ⟨804618, by rfl⟩ : syracuseStep 2145649 = 1609237) (by norm_num)
theorem B2860865 : Blo 1905435 2860865 := bstep (se 2 (by rfl) ⟨1072824, by rfl⟩ : syracuseStep 2860865 = 2145649) B2145649
theorem B1907243 : Blo 1905435 1907243 := bstep (se 1 (by rfl) ⟨1430432, by rfl⟩ : syracuseStep 1907243 = 2860865) B2860865
theorem B4582565 : Blo 1905435 4582565 := bbase (se 4 (by rfl) ⟨429615, by rfl⟩ : syracuseStep 4582565 = 859231) (by norm_num)
theorem B3055043 : Blo 1905435 3055043 := bstep (se 1 (by rfl) ⟨2291282, by rfl⟩ : syracuseStep 3055043 = 4582565) B4582565
theorem B8146781 : Blo 1905435 8146781 := bstep (se 3 (by rfl) ⟨1527521, by rfl⟩ : syracuseStep 8146781 = 3055043) B3055043
theorem B5431187 : Blo 1905435 5431187 := bstep (se 1 (by rfl) ⟨4073390, by rfl⟩ : syracuseStep 5431187 = 8146781) B8146781
theorem B3620791 : Blo 1905435 3620791 := bstep (se 1 (by rfl) ⟨2715593, by rfl⟩ : syracuseStep 3620791 = 5431187) B5431187
theorem B4827721 : Blo 1905435 4827721 := bstep (se 2 (by rfl) ⟨1810395, by rfl⟩ : syracuseStep 4827721 = 3620791) B3620791
theorem B6436961 : Blo 1905435 6436961 := bstep (se 2 (by rfl) ⟨2413860, by rfl⟩ : syracuseStep 6436961 = 4827721) B4827721
theorem B4291307 : Blo 1905435 4291307 := bstep (se 1 (by rfl) ⟨3218480, by rfl⟩ : syracuseStep 4291307 = 6436961) B6436961
theorem B2860871 : Blo 1905435 2860871 := bstep (se 1 (by rfl) ⟨2145653, by rfl⟩ : syracuseStep 2860871 = 4291307) B4291307
theorem B1907247 : Blo 1905435 1907247 := bstep (se 1 (by rfl) ⟨1430435, by rfl⟩ : syracuseStep 1907247 = 2860871) B2860871
theorem B2860877 : Blo 1905435 2860877 := bbase (se 3 (by rfl) ⟨536414, by rfl⟩ : syracuseStep 2860877 = 1072829) (by norm_num)
theorem B1907251 : Blo 1905435 1907251 := bstep (se 1 (by rfl) ⟨1430438, by rfl⟩ : syracuseStep 1907251 = 2860877) B2860877
theorem B4291325 : Blo 1905435 4291325 := bbase (se 3 (by rfl) ⟨804623, by rfl⟩ : syracuseStep 4291325 = 1609247) (by norm_num)
theorem B2860883 : Blo 1905435 2860883 := bstep (se 1 (by rfl) ⟨2145662, by rfl⟩ : syracuseStep 2860883 = 4291325) B4291325
theorem B1907255 : Blo 1905435 1907255 := bstep (se 1 (by rfl) ⟨1430441, by rfl⟩ : syracuseStep 1907255 = 2860883) B2860883
theorem B3218501 : Blo 1905435 3218501 := bbase (se 4 (by rfl) ⟨301734, by rfl⟩ : syracuseStep 3218501 = 603469) (by norm_num)
theorem B2145667 : Blo 1905435 2145667 := bstep (se 1 (by rfl) ⟨1609250, by rfl⟩ : syracuseStep 2145667 = 3218501) B3218501
theorem B2860889 : Blo 1905435 2860889 := bstep (se 2 (by rfl) ⟨1072833, by rfl⟩ : syracuseStep 2860889 = 2145667) B2145667
theorem B1907259 : Blo 1905435 1907259 := bstep (se 1 (by rfl) ⟨1430444, by rfl⟩ : syracuseStep 1907259 = 2860889) B2860889
theorem B14483285 : Blo 1905435 14483285 := bbase (se 9 (by rfl) ⟨42431, by rfl⟩ : syracuseStep 14483285 = 84863) (by norm_num)
theorem B9655523 : Blo 1905435 9655523 := bstep (se 1 (by rfl) ⟨7241642, by rfl⟩ : syracuseStep 9655523 = 14483285) B14483285
theorem B6437015 : Blo 1905435 6437015 := bstep (se 1 (by rfl) ⟨4827761, by rfl⟩ : syracuseStep 6437015 = 9655523) B9655523
theorem B4291343 : Blo 1905435 4291343 := bstep (se 1 (by rfl) ⟨3218507, by rfl⟩ : syracuseStep 4291343 = 6437015) B6437015
theorem B2860895 : Blo 1905435 2860895 := bstep (se 1 (by rfl) ⟨2145671, by rfl⟩ : syracuseStep 2860895 = 4291343) B4291343
theorem B1907263 : Blo 1905435 1907263 := bstep (se 1 (by rfl) ⟨1430447, by rfl⟩ : syracuseStep 1907263 = 2860895) B2860895
theorem B2860901 : Blo 1905435 2860901 := bbase (se 4 (by rfl) ⟨268209, by rfl⟩ : syracuseStep 2860901 = 536419) (by norm_num)
theorem B1907267 : Blo 1905435 1907267 := bstep (se 1 (by rfl) ⟨1430450, by rfl⟩ : syracuseStep 1907267 = 2860901) B2860901
theorem B3620837 : Blo 1905435 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B2413891 : Blo 1905435 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B3218521 : Blo 1905435 3218521 := bstep (se 2 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 3218521 = 2413891) B2413891
theorem B4291361 : Blo 1905435 4291361 := bstep (se 2 (by rfl) ⟨1609260, by rfl⟩ : syracuseStep 4291361 = 3218521) B3218521
theorem B2860907 : Blo 1905435 2860907 := bstep (se 1 (by rfl) ⟨2145680, by rfl⟩ : syracuseStep 2860907 = 4291361) B4291361
theorem B1907271 : Blo 1905435 1907271 := bstep (se 1 (by rfl) ⟨1430453, by rfl⟩ : syracuseStep 1907271 = 2860907) B2860907
theorem B2145685 : Blo 1905435 2145685 := bbase (se 6 (by rfl) ⟨50289, by rfl⟩ : syracuseStep 2145685 = 100579) (by norm_num)
theorem B2860913 : Blo 1905435 2860913 := bstep (se 2 (by rfl) ⟨1072842, by rfl⟩ : syracuseStep 2860913 = 2145685) B2145685
theorem B1907275 : Blo 1905435 1907275 := bstep (se 1 (by rfl) ⟨1430456, by rfl⟩ : syracuseStep 1907275 = 2860913) B2860913
theorem B2413901 : Blo 1905435 2413901 := bbase (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) (by norm_num)
theorem B6437069 : Blo 1905435 6437069 := bstep (se 3 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 6437069 = 2413901) B2413901
theorem B4291379 : Blo 1905435 4291379 := bstep (se 1 (by rfl) ⟨3218534, by rfl⟩ : syracuseStep 4291379 = 6437069) B6437069
theorem B2860919 : Blo 1905435 2860919 := bstep (se 1 (by rfl) ⟨2145689, by rfl⟩ : syracuseStep 2860919 = 4291379) B4291379
theorem B1907279 : Blo 1905435 1907279 := bstep (se 1 (by rfl) ⟨1430459, by rfl⟩ : syracuseStep 1907279 = 2860919) B2860919
theorem B2860925 : Blo 1905435 2860925 := bbase (se 3 (by rfl) ⟨536423, by rfl⟩ : syracuseStep 2860925 = 1072847) (by norm_num)
theorem B1907283 : Blo 1905435 1907283 := bstep (se 1 (by rfl) ⟨1430462, by rfl⟩ : syracuseStep 1907283 = 2860925) B2860925
theorem B4291397 : Blo 1905435 4291397 := bbase (se 4 (by rfl) ⟨402318, by rfl⟩ : syracuseStep 4291397 = 804637) (by norm_num)
theorem B2860931 : Blo 1905435 2860931 := bstep (se 1 (by rfl) ⟨2145698, by rfl⟩ : syracuseStep 2860931 = 4291397) B4291397
theorem B1907287 : Blo 1905435 1907287 := bstep (se 1 (by rfl) ⟨1430465, by rfl⟩ : syracuseStep 1907287 = 2860931) B2860931
theorem B4073485 : Blo 1905435 4073485 := bbase (se 3 (by rfl) ⟨763778, by rfl⟩ : syracuseStep 4073485 = 1527557) (by norm_num)
theorem B5431313 : Blo 1905435 5431313 := bstep (se 2 (by rfl) ⟨2036742, by rfl⟩ : syracuseStep 5431313 = 4073485) B4073485
theorem B3620875 : Blo 1905435 3620875 := bstep (se 1 (by rfl) ⟨2715656, by rfl⟩ : syracuseStep 3620875 = 5431313) B5431313
theorem B4827833 : Blo 1905435 4827833 := bstep (se 2 (by rfl) ⟨1810437, by rfl⟩ : syracuseStep 4827833 = 3620875) B3620875
theorem B3218555 : Blo 1905435 3218555 := bstep (se 1 (by rfl) ⟨2413916, by rfl⟩ : syracuseStep 3218555 = 4827833) B4827833
theorem B2145703 : Blo 1905435 2145703 := bstep (se 1 (by rfl) ⟨1609277, by rfl⟩ : syracuseStep 2145703 = 3218555) B3218555
theorem B2860937 : Blo 1905435 2860937 := bstep (se 2 (by rfl) ⟨1072851, by rfl⟩ : syracuseStep 2860937 = 2145703) B2145703
theorem B1907291 : Blo 1905435 1907291 := bstep (se 1 (by rfl) ⟨1430468, by rfl⟩ : syracuseStep 1907291 = 2860937) B2860937
theorem B9655685 : Blo 1905435 9655685 := bbase (se 4 (by rfl) ⟨905220, by rfl⟩ : syracuseStep 9655685 = 1810441) (by norm_num)
theorem B6437123 : Blo 1905435 6437123 := bstep (se 1 (by rfl) ⟨4827842, by rfl⟩ : syracuseStep 6437123 = 9655685) B9655685
theorem B4291415 : Blo 1905435 4291415 := bstep (se 1 (by rfl) ⟨3218561, by rfl⟩ : syracuseStep 4291415 = 6437123) B6437123
theorem B2860943 : Blo 1905435 2860943 := bstep (se 1 (by rfl) ⟨2145707, by rfl⟩ : syracuseStep 2860943 = 4291415) B4291415
theorem B1907295 : Blo 1905435 1907295 := bstep (se 1 (by rfl) ⟨1430471, by rfl⟩ : syracuseStep 1907295 = 2860943) B2860943
theorem B2860949 : Blo 1905435 2860949 := bbase (se 6 (by rfl) ⟨67053, by rfl⟩ : syracuseStep 2860949 = 134107) (by norm_num)
theorem B1907299 : Blo 1905435 1907299 := bstep (se 1 (by rfl) ⟨1430474, by rfl⟩ : syracuseStep 1907299 = 2860949) B2860949
theorem B3055133 : Blo 1905435 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B2036755 : Blo 1905435 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B10862693 : Blo 1905435 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B7241795 : Blo 1905435 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B4827863 : Blo 1905435 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B3218575 : Blo 1905435 3218575 := bstep (se 1 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 3218575 = 4827863) B4827863
theorem B4291433 : Blo 1905435 4291433 := bstep (se 2 (by rfl) ⟨1609287, by rfl⟩ : syracuseStep 4291433 = 3218575) B3218575
theorem B2860955 : Blo 1905435 2860955 := bstep (se 1 (by rfl) ⟨2145716, by rfl⟩ : syracuseStep 2860955 = 4291433) B4291433
theorem B1907303 : Blo 1905435 1907303 := bstep (se 1 (by rfl) ⟨1430477, by rfl⟩ : syracuseStep 1907303 = 2860955) B2860955
theorem B2145721 : Blo 1905435 2145721 := bbase (se 2 (by rfl) ⟨804645, by rfl⟩ : syracuseStep 2145721 = 1609291) (by norm_num)
theorem B2860961 : Blo 1905435 2860961 := bstep (se 2 (by rfl) ⟨1072860, by rfl⟩ : syracuseStep 2860961 = 2145721) B2145721
theorem B1907307 : Blo 1905435 1907307 := bstep (se 1 (by rfl) ⟨1430480, by rfl⟩ : syracuseStep 1907307 = 2860961) B2860961
theorem B2092721 : Blo 1905435 2092721 := bbase (se 2 (by rfl) ⟨784770, by rfl⟩ : syracuseStep 2092721 = 1569541) (by norm_num)
theorem B5580589 : Blo 1905435 5580589 := bstep (se 3 (by rfl) ⟨1046360, by rfl⟩ : syracuseStep 5580589 = 2092721) B2092721
theorem B7440785 : Blo 1905435 7440785 := bstep (se 2 (by rfl) ⟨2790294, by rfl⟩ : syracuseStep 7440785 = 5580589) B5580589
theorem B4960523 : Blo 1905435 4960523 := bstep (se 1 (by rfl) ⟨3720392, by rfl⟩ : syracuseStep 4960523 = 7440785) B7440785
theorem B3307015 : Blo 1905435 3307015 := bstep (se 1 (by rfl) ⟨2480261, by rfl⟩ : syracuseStep 3307015 = 4960523) B4960523
theorem B4409353 : Blo 1905435 4409353 := bstep (se 2 (by rfl) ⟨1653507, by rfl⟩ : syracuseStep 4409353 = 3307015) B3307015
theorem B5879137 : Blo 1905435 5879137 := bstep (se 2 (by rfl) ⟨2204676, by rfl⟩ : syracuseStep 5879137 = 4409353) B4409353
theorem B7838849 : Blo 1905435 7838849 := bstep (se 2 (by rfl) ⟨2939568, by rfl⟩ : syracuseStep 7838849 = 5879137) B5879137
theorem B20903597 : Blo 1905435 20903597 := bstep (se 3 (by rfl) ⟨3919424, by rfl⟩ : syracuseStep 20903597 = 7838849) B7838849
theorem B13935731 : Blo 1905435 13935731 := bstep (se 1 (by rfl) ⟨10451798, by rfl⟩ : syracuseStep 13935731 = 20903597) B20903597
theorem B37161949 : Blo 1905435 37161949 := bstep (se 3 (by rfl) ⟨6967865, by rfl⟩ : syracuseStep 37161949 = 13935731) B13935731
theorem B49549265 : Blo 1905435 49549265 := bstep (se 2 (by rfl) ⟨18580974, by rfl⟩ : syracuseStep 49549265 = 37161949) B37161949
theorem B33032843 : Blo 1905435 33032843 := bstep (se 1 (by rfl) ⟨24774632, by rfl⟩ : syracuseStep 33032843 = 49549265) B49549265
theorem B22021895 : Blo 1905435 22021895 := bstep (se 1 (by rfl) ⟨16516421, by rfl⟩ : syracuseStep 22021895 = 33032843) B33032843
theorem B14681263 : Blo 1905435 14681263 := bstep (se 1 (by rfl) ⟨11010947, by rfl⟩ : syracuseStep 14681263 = 22021895) B22021895
theorem B19575017 : Blo 1905435 19575017 := bstep (se 2 (by rfl) ⟨7340631, by rfl⟩ : syracuseStep 19575017 = 14681263) B14681263
theorem B13050011 : Blo 1905435 13050011 := bstep (se 1 (by rfl) ⟨9787508, by rfl⟩ : syracuseStep 13050011 = 19575017) B19575017
theorem B8700007 : Blo 1905435 8700007 := bstep (se 1 (by rfl) ⟨6525005, by rfl⟩ : syracuseStep 8700007 = 13050011) B13050011
theorem B11600009 : Blo 1905435 11600009 := bstep (se 2 (by rfl) ⟨4350003, by rfl⟩ : syracuseStep 11600009 = 8700007) B8700007
theorem B7733339 : Blo 1905435 7733339 := bstep (se 1 (by rfl) ⟨5800004, by rfl⟩ : syracuseStep 7733339 = 11600009) B11600009
theorem B5155559 : Blo 1905435 5155559 := bstep (se 1 (by rfl) ⟨3866669, by rfl⟩ : syracuseStep 5155559 = 7733339) B7733339
theorem B3437039 : Blo 1905435 3437039 := bstep (se 1 (by rfl) ⟨2577779, by rfl⟩ : syracuseStep 3437039 = 5155559) B5155559
theorem B9165437 : Blo 1905435 9165437 := bstep (se 3 (by rfl) ⟨1718519, by rfl⟩ : syracuseStep 9165437 = 3437039) B3437039
theorem B6110291 : Blo 1905435 6110291 := bstep (se 1 (by rfl) ⟨4582718, by rfl⟩ : syracuseStep 6110291 = 9165437) B9165437
theorem B4073527 : Blo 1905435 4073527 := bstep (se 1 (by rfl) ⟨3055145, by rfl⟩ : syracuseStep 4073527 = 6110291) B6110291
theorem B5431369 : Blo 1905435 5431369 := bstep (se 2 (by rfl) ⟨2036763, by rfl⟩ : syracuseStep 5431369 = 4073527) B4073527
theorem B7241825 : Blo 1905435 7241825 := bstep (se 2 (by rfl) ⟨2715684, by rfl⟩ : syracuseStep 7241825 = 5431369) B5431369
theorem B4827883 : Blo 1905435 4827883 := bstep (se 1 (by rfl) ⟨3620912, by rfl⟩ : syracuseStep 4827883 = 7241825) B7241825
theorem B6437177 : Blo 1905435 6437177 := bstep (se 2 (by rfl) ⟨2413941, by rfl⟩ : syracuseStep 6437177 = 4827883) B4827883
theorem B4291451 : Blo 1905435 4291451 := bstep (se 1 (by rfl) ⟨3218588, by rfl⟩ : syracuseStep 4291451 = 6437177) B6437177
theorem B2860967 : Blo 1905435 2860967 := bstep (se 1 (by rfl) ⟨2145725, by rfl⟩ : syracuseStep 2860967 = 4291451) B4291451
theorem B1907311 : Blo 1905435 1907311 := bstep (se 1 (by rfl) ⟨1430483, by rfl⟩ : syracuseStep 1907311 = 2860967) B2860967
theorem B2860973 : Blo 1905435 2860973 := bbase (se 3 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 2860973 = 1072865) (by norm_num)
theorem B1907315 : Blo 1905435 1907315 := bstep (se 1 (by rfl) ⟨1430486, by rfl⟩ : syracuseStep 1907315 = 2860973) B2860973
theorem B4291469 : Blo 1905435 4291469 := bbase (se 3 (by rfl) ⟨804650, by rfl⟩ : syracuseStep 4291469 = 1609301) (by norm_num)
theorem B2860979 : Blo 1905435 2860979 := bstep (se 1 (by rfl) ⟨2145734, by rfl⟩ : syracuseStep 2860979 = 4291469) B4291469
theorem B1907319 : Blo 1905435 1907319 := bstep (se 1 (by rfl) ⟨1430489, by rfl⟩ : syracuseStep 1907319 = 2860979) B2860979
theorem B2413957 : Blo 1905435 2413957 := bbase (se 4 (by rfl) ⟨226308, by rfl⟩ : syracuseStep 2413957 = 452617) (by norm_num)
theorem B3218609 : Blo 1905435 3218609 := bstep (se 2 (by rfl) ⟨1206978, by rfl⟩ : syracuseStep 3218609 = 2413957) B2413957
theorem B2145739 : Blo 1905435 2145739 := bstep (se 1 (by rfl) ⟨1609304, by rfl⟩ : syracuseStep 2145739 = 3218609) B3218609
theorem B2860985 : Blo 1905435 2860985 := bstep (se 2 (by rfl) ⟨1072869, by rfl⟩ : syracuseStep 2860985 = 2145739) B2145739
theorem B1907323 : Blo 1905435 1907323 := bstep (se 1 (by rfl) ⟨1430492, by rfl⟩ : syracuseStep 1907323 = 2860985) B2860985
theorem B24441365 : Blo 1905435 24441365 := bbase (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) (by norm_num)
theorem B16294243 : Blo 1905435 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B21725657 : Blo 1905435 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B14483771 : Blo 1905435 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B9655847 : Blo 1905435 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B6437231 : Blo 1905435 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B4291487 : Blo 1905435 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B2860991 : Blo 1905435 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B1907327 : Blo 1905435 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B2860997 : Blo 1905435 2860997 := bbase (se 4 (by rfl) ⟨268218, by rfl⟩ : syracuseStep 2860997 = 536437) (by norm_num)
theorem B1907331 : Blo 1905435 1907331 := bstep (se 1 (by rfl) ⟨1430498, by rfl⟩ : syracuseStep 1907331 = 2860997) B2860997
theorem B3218629 : Blo 1905435 3218629 := bbase (se 4 (by rfl) ⟨301746, by rfl⟩ : syracuseStep 3218629 = 603493) (by norm_num)
theorem B4291505 : Blo 1905435 4291505 := bstep (se 2 (by rfl) ⟨1609314, by rfl⟩ : syracuseStep 4291505 = 3218629) B3218629
theorem B2861003 : Blo 1905435 2861003 := bstep (se 1 (by rfl) ⟨2145752, by rfl⟩ : syracuseStep 2861003 = 4291505) B4291505
theorem B1907335 : Blo 1905435 1907335 := bstep (se 1 (by rfl) ⟨1430501, by rfl⟩ : syracuseStep 1907335 = 2861003) B2861003
theorem B2145757 : Blo 1905435 2145757 := bbase (se 3 (by rfl) ⟨402329, by rfl⟩ : syracuseStep 2145757 = 804659) (by norm_num)
theorem B2861009 : Blo 1905435 2861009 := bstep (se 2 (by rfl) ⟨1072878, by rfl⟩ : syracuseStep 2861009 = 2145757) B2145757
theorem B1907339 : Blo 1905435 1907339 := bstep (se 1 (by rfl) ⟨1430504, by rfl⟩ : syracuseStep 1907339 = 2861009) B2861009
theorem B6437285 : Blo 1905435 6437285 := bbase (se 4 (by rfl) ⟨603495, by rfl⟩ : syracuseStep 6437285 = 1206991) (by norm_num)
theorem B4291523 : Blo 1905435 4291523 := bstep (se 1 (by rfl) ⟨3218642, by rfl⟩ : syracuseStep 4291523 = 6437285) B6437285
theorem B2861015 : Blo 1905435 2861015 := bstep (se 1 (by rfl) ⟨2145761, by rfl⟩ : syracuseStep 2861015 = 4291523) B4291523
theorem B1907343 : Blo 1905435 1907343 := bstep (se 1 (by rfl) ⟨1430507, by rfl⟩ : syracuseStep 1907343 = 2861015) B2861015
theorem B2861021 : Blo 1905435 2861021 := bbase (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) (by norm_num)
theorem B1907347 : Blo 1905435 1907347 := bstep (se 1 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 1907347 = 2861021) B2861021
theorem B4291541 : Blo 1905435 4291541 := bbase (se 7 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 4291541 = 100583) (by norm_num)
theorem B2861027 : Blo 1905435 2861027 := bstep (se 1 (by rfl) ⟨2145770, by rfl⟩ : syracuseStep 2861027 = 4291541) B4291541
theorem B1907351 : Blo 1905435 1907351 := bstep (se 1 (by rfl) ⟨1430513, by rfl⟩ : syracuseStep 1907351 = 2861027) B2861027
theorem B6525157 : Blo 1905435 6525157 := bbase (se 4 (by rfl) ⟨611733, by rfl⟩ : syracuseStep 6525157 = 1223467) (by norm_num)
theorem B8700209 : Blo 1905435 8700209 := bstep (se 2 (by rfl) ⟨3262578, by rfl⟩ : syracuseStep 8700209 = 6525157) B6525157
theorem B5800139 : Blo 1905435 5800139 := bstep (se 1 (by rfl) ⟨4350104, by rfl⟩ : syracuseStep 5800139 = 8700209) B8700209
theorem B3866759 : Blo 1905435 3866759 := bstep (se 1 (by rfl) ⟨2900069, by rfl⟩ : syracuseStep 3866759 = 5800139) B5800139
theorem B2577839 : Blo 1905435 2577839 := bstep (se 1 (by rfl) ⟨1933379, by rfl⟩ : syracuseStep 2577839 = 3866759) B3866759
theorem B6874237 : Blo 1905435 6874237 := bstep (se 3 (by rfl) ⟨1288919, by rfl⟩ : syracuseStep 6874237 = 2577839) B2577839
theorem B9165649 : Blo 1905435 9165649 := bstep (se 2 (by rfl) ⟨3437118, by rfl⟩ : syracuseStep 9165649 = 6874237) B6874237
theorem B12220865 : Blo 1905435 12220865 := bstep (se 2 (by rfl) ⟨4582824, by rfl⟩ : syracuseStep 12220865 = 9165649) B9165649
theorem B8147243 : Blo 1905435 8147243 := bstep (se 1 (by rfl) ⟨6110432, by rfl⟩ : syracuseStep 8147243 = 12220865) B12220865
theorem B5431495 : Blo 1905435 5431495 := bstep (se 1 (by rfl) ⟨4073621, by rfl⟩ : syracuseStep 5431495 = 8147243) B8147243
theorem B7241993 : Blo 1905435 7241993 := bstep (se 2 (by rfl) ⟨2715747, by rfl⟩ : syracuseStep 7241993 = 5431495) B5431495
theorem B4827995 : Blo 1905435 4827995 := bstep (se 1 (by rfl) ⟨3620996, by rfl⟩ : syracuseStep 4827995 = 7241993) B7241993
theorem B3218663 : Blo 1905435 3218663 := bstep (se 1 (by rfl) ⟨2413997, by rfl⟩ : syracuseStep 3218663 = 4827995) B4827995
theorem B2145775 : Blo 1905435 2145775 := bstep (se 1 (by rfl) ⟨1609331, by rfl⟩ : syracuseStep 2145775 = 3218663) B3218663
theorem B2861033 : Blo 1905435 2861033 := bstep (se 2 (by rfl) ⟨1072887, by rfl⟩ : syracuseStep 2861033 = 2145775) B2145775
theorem B1907355 : Blo 1905435 1907355 := bstep (se 1 (by rfl) ⟨1430516, by rfl⟩ : syracuseStep 1907355 = 2861033) B2861033
theorem B16294517 : Blo 1905435 16294517 := bbase (se 5 (by rfl) ⟨763805, by rfl⟩ : syracuseStep 16294517 = 1527611) (by norm_num)
theorem B10863011 : Blo 1905435 10863011 := bstep (se 1 (by rfl) ⟨8147258, by rfl⟩ : syracuseStep 10863011 = 16294517) B16294517
theorem B7242007 : Blo 1905435 7242007 := bstep (se 1 (by rfl) ⟨5431505, by rfl⟩ : syracuseStep 7242007 = 10863011) B10863011
theorem B9656009 : Blo 1905435 9656009 := bstep (se 2 (by rfl) ⟨3621003, by rfl⟩ : syracuseStep 9656009 = 7242007) B7242007
theorem B6437339 : Blo 1905435 6437339 := bstep (se 1 (by rfl) ⟨4828004, by rfl⟩ : syracuseStep 6437339 = 9656009) B9656009
theorem B4291559 : Blo 1905435 4291559 := bstep (se 1 (by rfl) ⟨3218669, by rfl⟩ : syracuseStep 4291559 = 6437339) B6437339
theorem B2861039 : Blo 1905435 2861039 := bstep (se 1 (by rfl) ⟨2145779, by rfl⟩ : syracuseStep 2861039 = 4291559) B4291559
theorem B1907359 : Blo 1905435 1907359 := bstep (se 1 (by rfl) ⟨1430519, by rfl⟩ : syracuseStep 1907359 = 2861039) B2861039
theorem B2861045 : Blo 1905435 2861045 := bbase (se 5 (by rfl) ⟨134111, by rfl⟩ : syracuseStep 2861045 = 268223) (by norm_num)
theorem B1907363 : Blo 1905435 1907363 := bstep (se 1 (by rfl) ⟨1430522, by rfl⟩ : syracuseStep 1907363 = 2861045) B2861045
theorem B5226053 : Blo 1905435 5226053 := bbase (se 4 (by rfl) ⟨489942, by rfl⟩ : syracuseStep 5226053 = 979885) (by norm_num)
theorem B13936141 : Blo 1905435 13936141 := bstep (se 3 (by rfl) ⟨2613026, by rfl⟩ : syracuseStep 13936141 = 5226053) B5226053
theorem B74326085 : Blo 1905435 74326085 := bstep (se 4 (by rfl) ⟨6968070, by rfl⟩ : syracuseStep 74326085 = 13936141) B13936141
theorem B49550723 : Blo 1905435 49550723 := bstep (se 1 (by rfl) ⟨37163042, by rfl⟩ : syracuseStep 49550723 = 74326085) B74326085
theorem B33033815 : Blo 1905435 33033815 := bstep (se 1 (by rfl) ⟨24775361, by rfl⟩ : syracuseStep 33033815 = 49550723) B49550723
theorem B22022543 : Blo 1905435 22022543 := bstep (se 1 (by rfl) ⟨16516907, by rfl⟩ : syracuseStep 22022543 = 33033815) B33033815
theorem B14681695 : Blo 1905435 14681695 := bstep (se 1 (by rfl) ⟨11011271, by rfl⟩ : syracuseStep 14681695 = 22022543) B22022543
theorem B19575593 : Blo 1905435 19575593 := bstep (se 2 (by rfl) ⟨7340847, by rfl⟩ : syracuseStep 19575593 = 14681695) B14681695
theorem B13050395 : Blo 1905435 13050395 := bstep (se 1 (by rfl) ⟨9787796, by rfl⟩ : syracuseStep 13050395 = 19575593) B19575593
theorem B8700263 : Blo 1905435 8700263 := bstep (se 1 (by rfl) ⟨6525197, by rfl⟩ : syracuseStep 8700263 = 13050395) B13050395
theorem B5800175 : Blo 1905435 5800175 := bstep (se 1 (by rfl) ⟨4350131, by rfl⟩ : syracuseStep 5800175 = 8700263) B8700263
theorem B3866783 : Blo 1905435 3866783 := bstep (se 1 (by rfl) ⟨2900087, by rfl⟩ : syracuseStep 3866783 = 5800175) B5800175
theorem B10311421 : Blo 1905435 10311421 := bstep (se 3 (by rfl) ⟨1933391, by rfl⟩ : syracuseStep 10311421 = 3866783) B3866783
theorem B13748561 : Blo 1905435 13748561 := bstep (se 2 (by rfl) ⟨5155710, by rfl⟩ : syracuseStep 13748561 = 10311421) B10311421
theorem B9165707 : Blo 1905435 9165707 := bstep (se 1 (by rfl) ⟨6874280, by rfl⟩ : syracuseStep 9165707 = 13748561) B13748561
theorem B6110471 : Blo 1905435 6110471 := bstep (se 1 (by rfl) ⟨4582853, by rfl⟩ : syracuseStep 6110471 = 9165707) B9165707
theorem B4073647 : Blo 1905435 4073647 := bstep (se 1 (by rfl) ⟨3055235, by rfl⟩ : syracuseStep 4073647 = 6110471) B6110471
theorem B5431529 : Blo 1905435 5431529 := bstep (se 2 (by rfl) ⟨2036823, by rfl⟩ : syracuseStep 5431529 = 4073647) B4073647
theorem B3621019 : Blo 1905435 3621019 := bstep (se 1 (by rfl) ⟨2715764, by rfl⟩ : syracuseStep 3621019 = 5431529) B5431529
theorem B4828025 : Blo 1905435 4828025 := bstep (se 2 (by rfl) ⟨1810509, by rfl⟩ : syracuseStep 4828025 = 3621019) B3621019
theorem B3218683 : Blo 1905435 3218683 := bstep (se 1 (by rfl) ⟨2414012, by rfl⟩ : syracuseStep 3218683 = 4828025) B4828025
theorem B4291577 : Blo 1905435 4291577 := bstep (se 2 (by rfl) ⟨1609341, by rfl⟩ : syracuseStep 4291577 = 3218683) B3218683
theorem B2861051 : Blo 1905435 2861051 := bstep (se 1 (by rfl) ⟨2145788, by rfl⟩ : syracuseStep 2861051 = 4291577) B4291577
theorem B1907367 : Blo 1905435 1907367 := bstep (se 1 (by rfl) ⟨1430525, by rfl⟩ : syracuseStep 1907367 = 2861051) B2861051
theorem B2145793 : Blo 1905435 2145793 := bbase (se 2 (by rfl) ⟨804672, by rfl⟩ : syracuseStep 2145793 = 1609345) (by norm_num)
theorem B2861057 : Blo 1905435 2861057 := bstep (se 2 (by rfl) ⟨1072896, by rfl⟩ : syracuseStep 2861057 = 2145793) B2145793
theorem B1907371 : Blo 1905435 1907371 := bstep (se 1 (by rfl) ⟨1430528, by rfl⟩ : syracuseStep 1907371 = 2861057) B2861057
theorem B4828045 : Blo 1905435 4828045 := bbase (se 3 (by rfl) ⟨905258, by rfl⟩ : syracuseStep 4828045 = 1810517) (by norm_num)
theorem B6437393 : Blo 1905435 6437393 := bstep (se 2 (by rfl) ⟨2414022, by rfl⟩ : syracuseStep 6437393 = 4828045) B4828045
theorem B4291595 : Blo 1905435 4291595 := bstep (se 1 (by rfl) ⟨3218696, by rfl⟩ : syracuseStep 4291595 = 6437393) B6437393
theorem B2861063 : Blo 1905435 2861063 := bstep (se 1 (by rfl) ⟨2145797, by rfl⟩ : syracuseStep 2861063 = 4291595) B4291595
theorem B1907375 : Blo 1905435 1907375 := bstep (se 1 (by rfl) ⟨1430531, by rfl⟩ : syracuseStep 1907375 = 2861063) B2861063
theorem B2861069 : Blo 1905435 2861069 := bbase (se 3 (by rfl) ⟨536450, by rfl⟩ : syracuseStep 2861069 = 1072901) (by norm_num)
theorem B1907379 : Blo 1905435 1907379 := bstep (se 1 (by rfl) ⟨1430534, by rfl⟩ : syracuseStep 1907379 = 2861069) B2861069
theorem B4291613 : Blo 1905435 4291613 := bbase (se 3 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 4291613 = 1609355) (by norm_num)
theorem B2861075 : Blo 1905435 2861075 := bstep (se 1 (by rfl) ⟨2145806, by rfl⟩ : syracuseStep 2861075 = 4291613) B4291613
theorem B1907383 : Blo 1905435 1907383 := bstep (se 1 (by rfl) ⟨1430537, by rfl⟩ : syracuseStep 1907383 = 2861075) B2861075
theorem B3218717 : Blo 1905435 3218717 := bbase (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) (by norm_num)
theorem B2145811 : Blo 1905435 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B2861081 : Blo 1905435 2861081 := bstep (se 2 (by rfl) ⟨1072905, by rfl⟩ : syracuseStep 2861081 = 2145811) B2145811
theorem B1907387 : Blo 1905435 1907387 := bstep (se 1 (by rfl) ⟨1430540, by rfl⟩ : syracuseStep 1907387 = 2861081) B2861081
theorem B8819077 : Blo 1905435 8819077 := bbase (se 4 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 8819077 = 1653577) (by norm_num)
theorem B11758769 : Blo 1905435 11758769 := bstep (se 2 (by rfl) ⟨4409538, by rfl⟩ : syracuseStep 11758769 = 8819077) B8819077
theorem B7839179 : Blo 1905435 7839179 := bstep (se 1 (by rfl) ⟨5879384, by rfl⟩ : syracuseStep 7839179 = 11758769) B11758769
theorem B5226119 : Blo 1905435 5226119 := bstep (se 1 (by rfl) ⟨3919589, by rfl⟩ : syracuseStep 5226119 = 7839179) B7839179
theorem B3484079 : Blo 1905435 3484079 := bstep (se 1 (by rfl) ⟨2613059, by rfl⟩ : syracuseStep 3484079 = 5226119) B5226119
theorem B2322719 : Blo 1905435 2322719 := bstep (se 1 (by rfl) ⟨1742039, by rfl⟩ : syracuseStep 2322719 = 3484079) B3484079
theorem B24775669 : Blo 1905435 24775669 := bstep (se 5 (by rfl) ⟨1161359, by rfl⟩ : syracuseStep 24775669 = 2322719) B2322719
theorem B33034225 : Blo 1905435 33034225 := bstep (se 2 (by rfl) ⟨12387834, by rfl⟩ : syracuseStep 33034225 = 24775669) B24775669
theorem B44045633 : Blo 1905435 44045633 := bstep (se 2 (by rfl) ⟨16517112, by rfl⟩ : syracuseStep 44045633 = 33034225) B33034225
theorem B29363755 : Blo 1905435 29363755 := bstep (se 1 (by rfl) ⟨22022816, by rfl⟩ : syracuseStep 29363755 = 44045633) B44045633
theorem B39151673 : Blo 1905435 39151673 := bstep (se 2 (by rfl) ⟨14681877, by rfl⟩ : syracuseStep 39151673 = 29363755) B29363755
theorem B26101115 : Blo 1905435 26101115 := bstep (se 1 (by rfl) ⟨19575836, by rfl⟩ : syracuseStep 26101115 = 39151673) B39151673
theorem B17400743 : Blo 1905435 17400743 := bstep (se 1 (by rfl) ⟨13050557, by rfl⟩ : syracuseStep 17400743 = 26101115) B26101115
theorem B11600495 : Blo 1905435 11600495 := bstep (se 1 (by rfl) ⟨8700371, by rfl⟩ : syracuseStep 11600495 = 17400743) B17400743
theorem B7733663 : Blo 1905435 7733663 := bstep (se 1 (by rfl) ⟨5800247, by rfl⟩ : syracuseStep 7733663 = 11600495) B11600495
theorem B5155775 : Blo 1905435 5155775 := bstep (se 1 (by rfl) ⟨3866831, by rfl⟩ : syracuseStep 5155775 = 7733663) B7733663
theorem B3437183 : Blo 1905435 3437183 := bstep (se 1 (by rfl) ⟨2577887, by rfl⟩ : syracuseStep 3437183 = 5155775) B5155775
theorem B2291455 : Blo 1905435 2291455 := bstep (se 1 (by rfl) ⟨1718591, by rfl⟩ : syracuseStep 2291455 = 3437183) B3437183
theorem B12221093 : Blo 1905435 12221093 := bstep (se 4 (by rfl) ⟨1145727, by rfl⟩ : syracuseStep 12221093 = 2291455) B2291455
theorem B8147395 : Blo 1905435 8147395 := bstep (se 1 (by rfl) ⟨6110546, by rfl⟩ : syracuseStep 8147395 = 12221093) B12221093
theorem B10863193 : Blo 1905435 10863193 := bstep (se 2 (by rfl) ⟨4073697, by rfl⟩ : syracuseStep 10863193 = 8147395) B8147395
theorem B14484257 : Blo 1905435 14484257 := bstep (se 2 (by rfl) ⟨5431596, by rfl⟩ : syracuseStep 14484257 = 10863193) B10863193
theorem B9656171 : Blo 1905435 9656171 := bstep (se 1 (by rfl) ⟨7242128, by rfl⟩ : syracuseStep 9656171 = 14484257) B14484257
theorem B6437447 : Blo 1905435 6437447 := bstep (se 1 (by rfl) ⟨4828085, by rfl⟩ : syracuseStep 6437447 = 9656171) B9656171
theorem B4291631 : Blo 1905435 4291631 := bstep (se 1 (by rfl) ⟨3218723, by rfl⟩ : syracuseStep 4291631 = 6437447) B6437447
theorem B2861087 : Blo 1905435 2861087 := bstep (se 1 (by rfl) ⟨2145815, by rfl⟩ : syracuseStep 2861087 = 4291631) B4291631
theorem B1907391 : Blo 1905435 1907391 := bstep (se 1 (by rfl) ⟨1430543, by rfl⟩ : syracuseStep 1907391 = 2861087) B2861087
theorem B2861093 : Blo 1905435 2861093 := bbase (se 4 (by rfl) ⟨268227, by rfl⟩ : syracuseStep 2861093 = 536455) (by norm_num)
theorem B1907395 : Blo 1905435 1907395 := bstep (se 1 (by rfl) ⟨1430546, by rfl⟩ : syracuseStep 1907395 = 2861093) B2861093
theorem B2414053 : Blo 1905435 2414053 := bbase (se 4 (by rfl) ⟨226317, by rfl⟩ : syracuseStep 2414053 = 452635) (by norm_num)
theorem B3218737 : Blo 1905435 3218737 := bstep (se 2 (by rfl) ⟨1207026, by rfl⟩ : syracuseStep 3218737 = 2414053) B2414053
theorem B4291649 : Blo 1905435 4291649 := bstep (se 2 (by rfl) ⟨1609368, by rfl⟩ : syracuseStep 4291649 = 3218737) B3218737
theorem B2861099 : Blo 1905435 2861099 := bstep (se 1 (by rfl) ⟨2145824, by rfl⟩ : syracuseStep 2861099 = 4291649) B4291649
theorem B1907399 : Blo 1905435 1907399 := bstep (se 1 (by rfl) ⟨1430549, by rfl⟩ : syracuseStep 1907399 = 2861099) B2861099
theorem B2145829 : Blo 1905435 2145829 := bbase (se 4 (by rfl) ⟨201171, by rfl⟩ : syracuseStep 2145829 = 402343) (by norm_num)
theorem B2861105 : Blo 1905435 2861105 := bstep (se 2 (by rfl) ⟨1072914, by rfl⟩ : syracuseStep 2861105 = 2145829) B2145829
theorem B1907403 : Blo 1905435 1907403 := bstep (se 1 (by rfl) ⟨1430552, by rfl⟩ : syracuseStep 1907403 = 2861105) B2861105
theorem B10311637 : Blo 1905435 10311637 := bbase (se 7 (by rfl) ⟨120839, by rfl⟩ : syracuseStep 10311637 = 241679) (by norm_num)
theorem B13748849 : Blo 1905435 13748849 := bstep (se 2 (by rfl) ⟨5155818, by rfl⟩ : syracuseStep 13748849 = 10311637) B10311637
theorem B9165899 : Blo 1905435 9165899 := bstep (se 1 (by rfl) ⟨6874424, by rfl⟩ : syracuseStep 9165899 = 13748849) B13748849
theorem B6110599 : Blo 1905435 6110599 := bstep (se 1 (by rfl) ⟨4582949, by rfl⟩ : syracuseStep 6110599 = 9165899) B9165899
theorem B8147465 : Blo 1905435 8147465 := bstep (se 2 (by rfl) ⟨3055299, by rfl⟩ : syracuseStep 8147465 = 6110599) B6110599
theorem B5431643 : Blo 1905435 5431643 := bstep (se 1 (by rfl) ⟨4073732, by rfl⟩ : syracuseStep 5431643 = 8147465) B8147465
theorem B3621095 : Blo 1905435 3621095 := bstep (se 1 (by rfl) ⟨2715821, by rfl⟩ : syracuseStep 3621095 = 5431643) B5431643
theorem B2414063 : Blo 1905435 2414063 := bstep (se 1 (by rfl) ⟨1810547, by rfl⟩ : syracuseStep 2414063 = 3621095) B3621095
theorem B6437501 : Blo 1905435 6437501 := bstep (se 3 (by rfl) ⟨1207031, by rfl⟩ : syracuseStep 6437501 = 2414063) B2414063
theorem B4291667 : Blo 1905435 4291667 := bstep (se 1 (by rfl) ⟨3218750, by rfl⟩ : syracuseStep 4291667 = 6437501) B6437501
theorem B2861111 : Blo 1905435 2861111 := bstep (se 1 (by rfl) ⟨2145833, by rfl⟩ : syracuseStep 2861111 = 4291667) B4291667
theorem B1907407 : Blo 1905435 1907407 := bstep (se 1 (by rfl) ⟨1430555, by rfl⟩ : syracuseStep 1907407 = 2861111) B2861111
theorem B2861117 : Blo 1905435 2861117 := bbase (se 3 (by rfl) ⟨536459, by rfl⟩ : syracuseStep 2861117 = 1072919) (by norm_num)
theorem B1907411 : Blo 1905435 1907411 := bstep (se 1 (by rfl) ⟨1430558, by rfl⟩ : syracuseStep 1907411 = 2861117) B2861117
theorem B4291685 : Blo 1905435 4291685 := bbase (se 4 (by rfl) ⟨402345, by rfl⟩ : syracuseStep 4291685 = 804691) (by norm_num)
theorem B2861123 : Blo 1905435 2861123 := bstep (se 1 (by rfl) ⟨2145842, by rfl⟩ : syracuseStep 2861123 = 4291685) B4291685
theorem B1907415 : Blo 1905435 1907415 := bstep (se 1 (by rfl) ⟨1430561, by rfl⟩ : syracuseStep 1907415 = 2861123) B2861123
theorem B4828157 : Blo 1905435 4828157 := bbase (se 3 (by rfl) ⟨905279, by rfl⟩ : syracuseStep 4828157 = 1810559) (by norm_num)
theorem B3218771 : Blo 1905435 3218771 := bstep (se 1 (by rfl) ⟨2414078, by rfl⟩ : syracuseStep 3218771 = 4828157) B4828157
theorem B2145847 : Blo 1905435 2145847 := bstep (se 1 (by rfl) ⟨1609385, by rfl⟩ : syracuseStep 2145847 = 3218771) B3218771
theorem B2861129 : Blo 1905435 2861129 := bstep (se 2 (by rfl) ⟨1072923, by rfl⟩ : syracuseStep 2861129 = 2145847) B2145847
theorem B1907419 : Blo 1905435 1907419 := bstep (se 1 (by rfl) ⟨1430564, by rfl⟩ : syracuseStep 1907419 = 2861129) B2861129
theorem B3621125 : Blo 1905435 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B9656333 : Blo 1905435 9656333 := bstep (se 3 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 9656333 = 3621125) B3621125
theorem B6437555 : Blo 1905435 6437555 := bstep (se 1 (by rfl) ⟨4828166, by rfl⟩ : syracuseStep 6437555 = 9656333) B9656333
theorem B4291703 : Blo 1905435 4291703 := bstep (se 1 (by rfl) ⟨3218777, by rfl⟩ : syracuseStep 4291703 = 6437555) B6437555
theorem B2861135 : Blo 1905435 2861135 := bstep (se 1 (by rfl) ⟨2145851, by rfl⟩ : syracuseStep 2861135 = 4291703) B4291703
theorem B1907423 : Blo 1905435 1907423 := bstep (se 1 (by rfl) ⟨1430567, by rfl⟩ : syracuseStep 1907423 = 2861135) B2861135
theorem B2861141 : Blo 1905435 2861141 := bbase (se 8 (by rfl) ⟨16764, by rfl⟩ : syracuseStep 2861141 = 33529) (by norm_num)
theorem B1907427 : Blo 1905435 1907427 := bstep (se 1 (by rfl) ⟨1430570, by rfl⟩ : syracuseStep 1907427 = 2861141) B2861141
theorem B4894061 : Blo 1905435 4894061 := bbase (se 3 (by rfl) ⟨917636, by rfl⟩ : syracuseStep 4894061 = 1835273) (by norm_num)
theorem B13050829 : Blo 1905435 13050829 := bstep (se 3 (by rfl) ⟨2447030, by rfl⟩ : syracuseStep 13050829 = 4894061) B4894061
theorem B17401105 : Blo 1905435 17401105 := bstep (se 2 (by rfl) ⟨6525414, by rfl⟩ : syracuseStep 17401105 = 13050829) B13050829
theorem B23201473 : Blo 1905435 23201473 := bstep (se 2 (by rfl) ⟨8700552, by rfl⟩ : syracuseStep 23201473 = 17401105) B17401105
theorem B30935297 : Blo 1905435 30935297 := bstep (se 2 (by rfl) ⟨11600736, by rfl⟩ : syracuseStep 30935297 = 23201473) B23201473
theorem B20623531 : Blo 1905435 20623531 := bstep (se 1 (by rfl) ⟨15467648, by rfl⟩ : syracuseStep 20623531 = 30935297) B30935297
theorem B27498041 : Blo 1905435 27498041 := bstep (se 2 (by rfl) ⟨10311765, by rfl⟩ : syracuseStep 27498041 = 20623531) B20623531
theorem B18332027 : Blo 1905435 18332027 := bstep (se 1 (by rfl) ⟨13749020, by rfl⟩ : syracuseStep 18332027 = 27498041) B27498041
theorem B12221351 : Blo 1905435 12221351 := bstep (se 1 (by rfl) ⟨9166013, by rfl⟩ : syracuseStep 12221351 = 18332027) B18332027
theorem B8147567 : Blo 1905435 8147567 := bstep (se 1 (by rfl) ⟨6110675, by rfl⟩ : syracuseStep 8147567 = 12221351) B12221351
theorem B5431711 : Blo 1905435 5431711 := bstep (se 1 (by rfl) ⟨4073783, by rfl⟩ : syracuseStep 5431711 = 8147567) B8147567
theorem B7242281 : Blo 1905435 7242281 := bstep (se 2 (by rfl) ⟨2715855, by rfl⟩ : syracuseStep 7242281 = 5431711) B5431711
theorem B4828187 : Blo 1905435 4828187 := bstep (se 1 (by rfl) ⟨3621140, by rfl⟩ : syracuseStep 4828187 = 7242281) B7242281
theorem B3218791 : Blo 1905435 3218791 := bstep (se 1 (by rfl) ⟨2414093, by rfl⟩ : syracuseStep 3218791 = 4828187) B4828187
theorem B4291721 : Blo 1905435 4291721 := bstep (se 2 (by rfl) ⟨1609395, by rfl⟩ : syracuseStep 4291721 = 3218791) B3218791
theorem B2861147 : Blo 1905435 2861147 := bstep (se 1 (by rfl) ⟨2145860, by rfl⟩ : syracuseStep 2861147 = 4291721) B4291721
theorem B1907431 : Blo 1905435 1907431 := bstep (se 1 (by rfl) ⟨1430573, by rfl⟩ : syracuseStep 1907431 = 2861147) B2861147
theorem B2145865 : Blo 1905435 2145865 := bbase (se 2 (by rfl) ⟨804699, by rfl⟩ : syracuseStep 2145865 = 1609399) (by norm_num)
theorem B2861153 : Blo 1905435 2861153 := bstep (se 2 (by rfl) ⟨1072932, by rfl⟩ : syracuseStep 2861153 = 2145865) B2145865
theorem B1907435 : Blo 1905435 1907435 := bstep (se 1 (by rfl) ⟨1430576, by rfl⟩ : syracuseStep 1907435 = 2861153) B2861153
theorem C0 (j : ℕ) (h1 : 476358 ≤ j) (h2 : j ≤ 476858) : Blo 1905435 (4 * j + 3) := by
  interval_cases j
  · exact B1905435
  · exact B1905439
  · exact B1905443
  · exact B1905447
  · exact B1905451
  · exact B1905455
  · exact B1905459
  · exact B1905463
  · exact B1905467
  · exact B1905471
  · exact B1905475
  · exact B1905479
  · exact B1905483
  · exact B1905487
  · exact B1905491
  · exact B1905495
  · exact B1905499
  · exact B1905503
  · exact B1905507
  · exact B1905511
  · exact B1905515
  · exact B1905519
  · exact B1905523
  · exact B1905527
  · exact B1905531
  · exact B1905535
  · exact B1905539
  · exact B1905543
  · exact B1905547
  · exact B1905551
  · exact B1905555
  · exact B1905559
  · exact B1905563
  · exact B1905567
  · exact B1905571
  · exact B1905575
  · exact B1905579
  · exact B1905583
  · exact B1905587
  · exact B1905591
  · exact B1905595
  · exact B1905599
  · exact B1905603
  · exact B1905607
  · exact B1905611
  · exact B1905615
  · exact B1905619
  · exact B1905623
  · exact B1905627
  · exact B1905631
  · exact B1905635
  · exact B1905639
  · exact B1905643
  · exact B1905647
  · exact B1905651
  · exact B1905655
  · exact B1905659
  · exact B1905663
  · exact B1905667
  · exact B1905671
  · exact B1905675
  · exact B1905679
  · exact B1905683
  · exact B1905687
  · exact B1905691
  · exact B1905695
  · exact B1905699
  · exact B1905703
  · exact B1905707
  · exact B1905711
  · exact B1905715
  · exact B1905719
  · exact B1905723
  · exact B1905727
  · exact B1905731
  · exact B1905735
  · exact B1905739
  · exact B1905743
  · exact B1905747
  · exact B1905751
  · exact B1905755
  · exact B1905759
  · exact B1905763
  · exact B1905767
  · exact B1905771
  · exact B1905775
  · exact B1905779
  · exact B1905783
  · exact B1905787
  · exact B1905791
  · exact B1905795
  · exact B1905799
  · exact B1905803
  · exact B1905807
  · exact B1905811
  · exact B1905815
  · exact B1905819
  · exact B1905823
  · exact B1905827
  · exact B1905831
  · exact B1905835
  · exact B1905839
  · exact B1905843
  · exact B1905847
  · exact B1905851
  · exact B1905855
  · exact B1905859
  · exact B1905863
  · exact B1905867
  · exact B1905871
  · exact B1905875
  · exact B1905879
  · exact B1905883
  · exact B1905887
  · exact B1905891
  · exact B1905895
  · exact B1905899
  · exact B1905903
  · exact B1905907
  · exact B1905911
  · exact B1905915
  · exact B1905919
  · exact B1905923
  · exact B1905927
  · exact B1905931
  · exact B1905935
  · exact B1905939
  · exact B1905943
  · exact B1905947
  · exact B1905951
  · exact B1905955
  · exact B1905959
  · exact B1905963
  · exact B1905967
  · exact B1905971
  · exact B1905975
  · exact B1905979
  · exact B1905983
  · exact B1905987
  · exact B1905991
  · exact B1905995
  · exact B1905999
  · exact B1906003
  · exact B1906007
  · exact B1906011
  · exact B1906015
  · exact B1906019
  · exact B1906023
  · exact B1906027
  · exact B1906031
  · exact B1906035
  · exact B1906039
  · exact B1906043
  · exact B1906047
  · exact B1906051
  · exact B1906055
  · exact B1906059
  · exact B1906063
  · exact B1906067
  · exact B1906071
  · exact B1906075
  · exact B1906079
  · exact B1906083
  · exact B1906087
  · exact B1906091
  · exact B1906095
  · exact B1906099
  · exact B1906103
  · exact B1906107
  · exact B1906111
  · exact B1906115
  · exact B1906119
  · exact B1906123
  · exact B1906127
  · exact B1906131
  · exact B1906135
  · exact B1906139
  · exact B1906143
  · exact B1906147
  · exact B1906151
  · exact B1906155
  · exact B1906159
  · exact B1906163
  · exact B1906167
  · exact B1906171
  · exact B1906175
  · exact B1906179
  · exact B1906183
  · exact B1906187
  · exact B1906191
  · exact B1906195
  · exact B1906199
  · exact B1906203
  · exact B1906207
  · exact B1906211
  · exact B1906215
  · exact B1906219
  · exact B1906223
  · exact B1906227
  · exact B1906231
  · exact B1906235
  · exact B1906239
  · exact B1906243
  · exact B1906247
  · exact B1906251
  · exact B1906255
  · exact B1906259
  · exact B1906263
  · exact B1906267
  · exact B1906271
  · exact B1906275
  · exact B1906279
  · exact B1906283
  · exact B1906287
  · exact B1906291
  · exact B1906295
  · exact B1906299
  · exact B1906303
  · exact B1906307
  · exact B1906311
  · exact B1906315
  · exact B1906319
  · exact B1906323
  · exact B1906327
  · exact B1906331
  · exact B1906335
  · exact B1906339
  · exact B1906343
  · exact B1906347
  · exact B1906351
  · exact B1906355
  · exact B1906359
  · exact B1906363
  · exact B1906367
  · exact B1906371
  · exact B1906375
  · exact B1906379
  · exact B1906383
  · exact B1906387
  · exact B1906391
  · exact B1906395
  · exact B1906399
  · exact B1906403
  · exact B1906407
  · exact B1906411
  · exact B1906415
  · exact B1906419
  · exact B1906423
  · exact B1906427
  · exact B1906431
  · exact B1906435
  · exact B1906439
  · exact B1906443
  · exact B1906447
  · exact B1906451
  · exact B1906455
  · exact B1906459
  · exact B1906463
  · exact B1906467
  · exact B1906471
  · exact B1906475
  · exact B1906479
  · exact B1906483
  · exact B1906487
  · exact B1906491
  · exact B1906495
  · exact B1906499
  · exact B1906503
  · exact B1906507
  · exact B1906511
  · exact B1906515
  · exact B1906519
  · exact B1906523
  · exact B1906527
  · exact B1906531
  · exact B1906535
  · exact B1906539
  · exact B1906543
  · exact B1906547
  · exact B1906551
  · exact B1906555
  · exact B1906559
  · exact B1906563
  · exact B1906567
  · exact B1906571
  · exact B1906575
  · exact B1906579
  · exact B1906583
  · exact B1906587
  · exact B1906591
  · exact B1906595
  · exact B1906599
  · exact B1906603
  · exact B1906607
  · exact B1906611
  · exact B1906615
  · exact B1906619
  · exact B1906623
  · exact B1906627
  · exact B1906631
  · exact B1906635
  · exact B1906639
  · exact B1906643
  · exact B1906647
  · exact B1906651
  · exact B1906655
  · exact B1906659
  · exact B1906663
  · exact B1906667
  · exact B1906671
  · exact B1906675
  · exact B1906679
  · exact B1906683
  · exact B1906687
  · exact B1906691
  · exact B1906695
  · exact B1906699
  · exact B1906703
  · exact B1906707
  · exact B1906711
  · exact B1906715
  · exact B1906719
  · exact B1906723
  · exact B1906727
  · exact B1906731
  · exact B1906735
  · exact B1906739
  · exact B1906743
  · exact B1906747
  · exact B1906751
  · exact B1906755
  · exact B1906759
  · exact B1906763
  · exact B1906767
  · exact B1906771
  · exact B1906775
  · exact B1906779
  · exact B1906783
  · exact B1906787
  · exact B1906791
  · exact B1906795
  · exact B1906799
  · exact B1906803
  · exact B1906807
  · exact B1906811
  · exact B1906815
  · exact B1906819
  · exact B1906823
  · exact B1906827
  · exact B1906831
  · exact B1906835
  · exact B1906839
  · exact B1906843
  · exact B1906847
  · exact B1906851
  · exact B1906855
  · exact B1906859
  · exact B1906863
  · exact B1906867
  · exact B1906871
  · exact B1906875
  · exact B1906879
  · exact B1906883
  · exact B1906887
  · exact B1906891
  · exact B1906895
  · exact B1906899
  · exact B1906903
  · exact B1906907
  · exact B1906911
  · exact B1906915
  · exact B1906919
  · exact B1906923
  · exact B1906927
  · exact B1906931
  · exact B1906935
  · exact B1906939
  · exact B1906943
  · exact B1906947
  · exact B1906951
  · exact B1906955
  · exact B1906959
  · exact B1906963
  · exact B1906967
  · exact B1906971
  · exact B1906975
  · exact B1906979
  · exact B1906983
  · exact B1906987
  · exact B1906991
  · exact B1906995
  · exact B1906999
  · exact B1907003
  · exact B1907007
  · exact B1907011
  · exact B1907015
  · exact B1907019
  · exact B1907023
  · exact B1907027
  · exact B1907031
  · exact B1907035
  · exact B1907039
  · exact B1907043
  · exact B1907047
  · exact B1907051
  · exact B1907055
  · exact B1907059
  · exact B1907063
  · exact B1907067
  · exact B1907071
  · exact B1907075
  · exact B1907079
  · exact B1907083
  · exact B1907087
  · exact B1907091
  · exact B1907095
  · exact B1907099
  · exact B1907103
  · exact B1907107
  · exact B1907111
  · exact B1907115
  · exact B1907119
  · exact B1907123
  · exact B1907127
  · exact B1907131
  · exact B1907135
  · exact B1907139
  · exact B1907143
  · exact B1907147
  · exact B1907151
  · exact B1907155
  · exact B1907159
  · exact B1907163
  · exact B1907167
  · exact B1907171
  · exact B1907175
  · exact B1907179
  · exact B1907183
  · exact B1907187
  · exact B1907191
  · exact B1907195
  · exact B1907199
  · exact B1907203
  · exact B1907207
  · exact B1907211
  · exact B1907215
  · exact B1907219
  · exact B1907223
  · exact B1907227
  · exact B1907231
  · exact B1907235
  · exact B1907239
  · exact B1907243
  · exact B1907247
  · exact B1907251
  · exact B1907255
  · exact B1907259
  · exact B1907263
  · exact B1907267
  · exact B1907271
  · exact B1907275
  · exact B1907279
  · exact B1907283
  · exact B1907287
  · exact B1907291
  · exact B1907295
  · exact B1907299
  · exact B1907303
  · exact B1907307
  · exact B1907311
  · exact B1907315
  · exact B1907319
  · exact B1907323
  · exact B1907327
  · exact B1907331
  · exact B1907335
  · exact B1907339
  · exact B1907343
  · exact B1907347
  · exact B1907351
  · exact B1907355
  · exact B1907359
  · exact B1907363
  · exact B1907367
  · exact B1907371
  · exact B1907375
  · exact B1907379
  · exact B1907383
  · exact B1907387
  · exact B1907391
  · exact B1907395
  · exact B1907399
  · exact B1907403
  · exact B1907407
  · exact B1907411
  · exact B1907415
  · exact B1907419
  · exact B1907423
  · exact B1907427
  · exact B1907431
  · exact B1907435
theorem solution (m : ℕ) (hlo : 1905435 ≤ m) (hhi : m ≤ 1907435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 476358 ≤ j := by omega
    have hj2 : j ≤ 476858 := by omega
    have hb : Blo 1905435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
