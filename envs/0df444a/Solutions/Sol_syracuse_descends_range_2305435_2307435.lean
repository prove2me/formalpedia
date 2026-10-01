-- Prove2me | solution 1 for syracuse_descends_range_2305435_2307435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:50:04.871514+00:00
-- url     : https://prove2.me/submissions/faca62b5-aab1-42c4-892e-72cf79866c79

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

theorem B2461909 : Blo 2305435 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B3282545 : Blo 2305435 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B8753453 : Blo 2305435 8753453 := bstep (se 3 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 8753453 = 3282545) B3282545
theorem B5835635 : Blo 2305435 5835635 := bstep (se 1 (by rfl) ⟨4376726, by rfl⟩ : syracuseStep 5835635 = 8753453) B8753453
theorem B3890423 : Blo 2305435 3890423 := bstep (se 1 (by rfl) ⟨2917817, by rfl⟩ : syracuseStep 3890423 = 5835635) B5835635
theorem B2593615 : Blo 2305435 2593615 := bstep (se 1 (by rfl) ⟨1945211, by rfl⟩ : syracuseStep 2593615 = 3890423) B3890423
theorem B3458153 : Blo 2305435 3458153 := bstep (se 2 (by rfl) ⟨1296807, by rfl⟩ : syracuseStep 3458153 = 2593615) B2593615
theorem B2305435 : Blo 2305435 2305435 := bstep (se 1 (by rfl) ⟨1729076, by rfl⟩ : syracuseStep 2305435 = 3458153) B3458153
theorem B14771477 : Blo 2305435 14771477 := bbase (se 6 (by rfl) ⟨346206, by rfl⟩ : syracuseStep 14771477 = 692413) (by norm_num)
theorem B9847651 : Blo 2305435 9847651 := bstep (se 1 (by rfl) ⟨7385738, by rfl⟩ : syracuseStep 9847651 = 14771477) B14771477
theorem B13130201 : Blo 2305435 13130201 := bstep (se 2 (by rfl) ⟨4923825, by rfl⟩ : syracuseStep 13130201 = 9847651) B9847651
theorem B8753467 : Blo 2305435 8753467 := bstep (se 1 (by rfl) ⟨6565100, by rfl⟩ : syracuseStep 8753467 = 13130201) B13130201
theorem B11671289 : Blo 2305435 11671289 := bstep (se 2 (by rfl) ⟨4376733, by rfl⟩ : syracuseStep 11671289 = 8753467) B8753467
theorem B7780859 : Blo 2305435 7780859 := bstep (se 1 (by rfl) ⟨5835644, by rfl⟩ : syracuseStep 7780859 = 11671289) B11671289
theorem B5187239 : Blo 2305435 5187239 := bstep (se 1 (by rfl) ⟨3890429, by rfl⟩ : syracuseStep 5187239 = 7780859) B7780859
theorem B3458159 : Blo 2305435 3458159 := bstep (se 1 (by rfl) ⟨2593619, by rfl⟩ : syracuseStep 3458159 = 5187239) B5187239
theorem B2305439 : Blo 2305435 2305439 := bstep (se 1 (by rfl) ⟨1729079, by rfl⟩ : syracuseStep 2305439 = 3458159) B3458159
theorem B3458165 : Blo 2305435 3458165 := bbase (se 5 (by rfl) ⟨162101, by rfl⟩ : syracuseStep 3458165 = 324203) (by norm_num)
theorem B2305443 : Blo 2305435 2305443 := bstep (se 1 (by rfl) ⟨1729082, by rfl⟩ : syracuseStep 2305443 = 3458165) B3458165
theorem B4376749 : Blo 2305435 4376749 := bbase (se 3 (by rfl) ⟨820640, by rfl⟩ : syracuseStep 4376749 = 1641281) (by norm_num)
theorem B5835665 : Blo 2305435 5835665 := bstep (se 2 (by rfl) ⟨2188374, by rfl⟩ : syracuseStep 5835665 = 4376749) B4376749
theorem B3890443 : Blo 2305435 3890443 := bstep (se 1 (by rfl) ⟨2917832, by rfl⟩ : syracuseStep 3890443 = 5835665) B5835665
theorem B5187257 : Blo 2305435 5187257 := bstep (se 2 (by rfl) ⟨1945221, by rfl⟩ : syracuseStep 5187257 = 3890443) B3890443
theorem B3458171 : Blo 2305435 3458171 := bstep (se 1 (by rfl) ⟨2593628, by rfl⟩ : syracuseStep 3458171 = 5187257) B5187257
theorem B2305447 : Blo 2305435 2305447 := bstep (se 1 (by rfl) ⟨1729085, by rfl⟩ : syracuseStep 2305447 = 3458171) B3458171
theorem B2593633 : Blo 2305435 2593633 := bbase (se 2 (by rfl) ⟨972612, by rfl⟩ : syracuseStep 2593633 = 1945225) (by norm_num)
theorem B3458177 : Blo 2305435 3458177 := bstep (se 2 (by rfl) ⟨1296816, by rfl⟩ : syracuseStep 3458177 = 2593633) B2593633
theorem B2305451 : Blo 2305435 2305451 := bstep (se 1 (by rfl) ⟨1729088, by rfl⟩ : syracuseStep 2305451 = 3458177) B3458177
theorem B5835685 : Blo 2305435 5835685 := bbase (se 4 (by rfl) ⟨547095, by rfl⟩ : syracuseStep 5835685 = 1094191) (by norm_num)
theorem B7780913 : Blo 2305435 7780913 := bstep (se 2 (by rfl) ⟨2917842, by rfl⟩ : syracuseStep 7780913 = 5835685) B5835685
theorem B5187275 : Blo 2305435 5187275 := bstep (se 1 (by rfl) ⟨3890456, by rfl⟩ : syracuseStep 5187275 = 7780913) B7780913
theorem B3458183 : Blo 2305435 3458183 := bstep (se 1 (by rfl) ⟨2593637, by rfl⟩ : syracuseStep 3458183 = 5187275) B5187275
theorem B2305455 : Blo 2305435 2305455 := bstep (se 1 (by rfl) ⟨1729091, by rfl⟩ : syracuseStep 2305455 = 3458183) B3458183
theorem B3458189 : Blo 2305435 3458189 := bbase (se 3 (by rfl) ⟨648410, by rfl⟩ : syracuseStep 3458189 = 1296821) (by norm_num)
theorem B2305459 : Blo 2305435 2305459 := bstep (se 1 (by rfl) ⟨1729094, by rfl⟩ : syracuseStep 2305459 = 3458189) B3458189
theorem B5187293 : Blo 2305435 5187293 := bbase (se 3 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 5187293 = 1945235) (by norm_num)
theorem B3458195 : Blo 2305435 3458195 := bstep (se 1 (by rfl) ⟨2593646, by rfl⟩ : syracuseStep 3458195 = 5187293) B5187293
theorem B2305463 : Blo 2305435 2305463 := bstep (se 1 (by rfl) ⟨1729097, by rfl⟩ : syracuseStep 2305463 = 3458195) B3458195
theorem B3890477 : Blo 2305435 3890477 := bbase (se 3 (by rfl) ⟨729464, by rfl⟩ : syracuseStep 3890477 = 1458929) (by norm_num)
theorem B2593651 : Blo 2305435 2593651 := bstep (se 1 (by rfl) ⟨1945238, by rfl⟩ : syracuseStep 2593651 = 3890477) B3890477
theorem B3458201 : Blo 2305435 3458201 := bstep (se 2 (by rfl) ⟨1296825, by rfl⟩ : syracuseStep 3458201 = 2593651) B2593651
theorem B2305467 : Blo 2305435 2305467 := bstep (se 1 (by rfl) ⟨1729100, by rfl⟩ : syracuseStep 2305467 = 3458201) B3458201
theorem B17746037 : Blo 2305435 17746037 := bbase (se 5 (by rfl) ⟨831845, by rfl⟩ : syracuseStep 17746037 = 1663691) (by norm_num)
theorem B11830691 : Blo 2305435 11830691 := bstep (se 1 (by rfl) ⟨8873018, by rfl⟩ : syracuseStep 11830691 = 17746037) B17746037
theorem B7887127 : Blo 2305435 7887127 := bstep (se 1 (by rfl) ⟨5915345, by rfl⟩ : syracuseStep 7887127 = 11830691) B11830691
theorem B10516169 : Blo 2305435 10516169 := bstep (se 2 (by rfl) ⟨3943563, by rfl⟩ : syracuseStep 10516169 = 7887127) B7887127
theorem B28043117 : Blo 2305435 28043117 := bstep (se 3 (by rfl) ⟨5258084, by rfl⟩ : syracuseStep 28043117 = 10516169) B10516169
theorem B18695411 : Blo 2305435 18695411 := bstep (se 1 (by rfl) ⟨14021558, by rfl⟩ : syracuseStep 18695411 = 28043117) B28043117
theorem B12463607 : Blo 2305435 12463607 := bstep (se 1 (by rfl) ⟨9347705, by rfl⟩ : syracuseStep 12463607 = 18695411) B18695411
theorem B8309071 : Blo 2305435 8309071 := bstep (se 1 (by rfl) ⟨6231803, by rfl⟩ : syracuseStep 8309071 = 12463607) B12463607
theorem B44315045 : Blo 2305435 44315045 := bstep (se 4 (by rfl) ⟨4154535, by rfl⟩ : syracuseStep 44315045 = 8309071) B8309071
theorem B29543363 : Blo 2305435 29543363 := bstep (se 1 (by rfl) ⟨22157522, by rfl⟩ : syracuseStep 29543363 = 44315045) B44315045
theorem B19695575 : Blo 2305435 19695575 := bstep (se 1 (by rfl) ⟨14771681, by rfl⟩ : syracuseStep 19695575 = 29543363) B29543363
theorem B13130383 : Blo 2305435 13130383 := bstep (se 1 (by rfl) ⟨9847787, by rfl⟩ : syracuseStep 13130383 = 19695575) B19695575
theorem B17507177 : Blo 2305435 17507177 := bstep (se 2 (by rfl) ⟨6565191, by rfl⟩ : syracuseStep 17507177 = 13130383) B13130383
theorem B11671451 : Blo 2305435 11671451 := bstep (se 1 (by rfl) ⟨8753588, by rfl⟩ : syracuseStep 11671451 = 17507177) B17507177
theorem B7780967 : Blo 2305435 7780967 := bstep (se 1 (by rfl) ⟨5835725, by rfl⟩ : syracuseStep 7780967 = 11671451) B11671451
theorem B5187311 : Blo 2305435 5187311 := bstep (se 1 (by rfl) ⟨3890483, by rfl⟩ : syracuseStep 5187311 = 7780967) B7780967
theorem B3458207 : Blo 2305435 3458207 := bstep (se 1 (by rfl) ⟨2593655, by rfl⟩ : syracuseStep 3458207 = 5187311) B5187311
theorem B2305471 : Blo 2305435 2305471 := bstep (se 1 (by rfl) ⟨1729103, by rfl⟩ : syracuseStep 2305471 = 3458207) B3458207
theorem B3458213 : Blo 2305435 3458213 := bbase (se 4 (by rfl) ⟨324207, by rfl⟩ : syracuseStep 3458213 = 648415) (by norm_num)
theorem B2305475 : Blo 2305435 2305475 := bstep (se 1 (by rfl) ⟨1729106, by rfl⟩ : syracuseStep 2305475 = 3458213) B3458213
theorem B2917873 : Blo 2305435 2917873 := bbase (se 2 (by rfl) ⟨1094202, by rfl⟩ : syracuseStep 2917873 = 2188405) (by norm_num)
theorem B3890497 : Blo 2305435 3890497 := bstep (se 2 (by rfl) ⟨1458936, by rfl⟩ : syracuseStep 3890497 = 2917873) B2917873
theorem B5187329 : Blo 2305435 5187329 := bstep (se 2 (by rfl) ⟨1945248, by rfl⟩ : syracuseStep 5187329 = 3890497) B3890497
theorem B3458219 : Blo 2305435 3458219 := bstep (se 1 (by rfl) ⟨2593664, by rfl⟩ : syracuseStep 3458219 = 5187329) B5187329
theorem B2305479 : Blo 2305435 2305479 := bstep (se 1 (by rfl) ⟨1729109, by rfl⟩ : syracuseStep 2305479 = 3458219) B3458219
theorem B2593669 : Blo 2305435 2593669 := bbase (se 4 (by rfl) ⟨243156, by rfl⟩ : syracuseStep 2593669 = 486313) (by norm_num)
theorem B3458225 : Blo 2305435 3458225 := bstep (se 2 (by rfl) ⟨1296834, by rfl⟩ : syracuseStep 3458225 = 2593669) B2593669
theorem B2305483 : Blo 2305435 2305483 := bstep (se 1 (by rfl) ⟨1729112, by rfl⟩ : syracuseStep 2305483 = 3458225) B3458225
theorem B5539421 : Blo 2305435 5539421 := bbase (se 3 (by rfl) ⟨1038641, by rfl⟩ : syracuseStep 5539421 = 2077283) (by norm_num)
theorem B3692947 : Blo 2305435 3692947 := bstep (se 1 (by rfl) ⟨2769710, by rfl⟩ : syracuseStep 3692947 = 5539421) B5539421
theorem B4923929 : Blo 2305435 4923929 := bstep (se 2 (by rfl) ⟨1846473, by rfl⟩ : syracuseStep 4923929 = 3692947) B3692947
theorem B3282619 : Blo 2305435 3282619 := bstep (se 1 (by rfl) ⟨2461964, by rfl⟩ : syracuseStep 3282619 = 4923929) B4923929
theorem B4376825 : Blo 2305435 4376825 := bstep (se 2 (by rfl) ⟨1641309, by rfl⟩ : syracuseStep 4376825 = 3282619) B3282619
theorem B2917883 : Blo 2305435 2917883 := bstep (se 1 (by rfl) ⟨2188412, by rfl⟩ : syracuseStep 2917883 = 4376825) B4376825
theorem B7781021 : Blo 2305435 7781021 := bstep (se 3 (by rfl) ⟨1458941, by rfl⟩ : syracuseStep 7781021 = 2917883) B2917883
theorem B5187347 : Blo 2305435 5187347 := bstep (se 1 (by rfl) ⟨3890510, by rfl⟩ : syracuseStep 5187347 = 7781021) B7781021
theorem B3458231 : Blo 2305435 3458231 := bstep (se 1 (by rfl) ⟨2593673, by rfl⟩ : syracuseStep 3458231 = 5187347) B5187347
theorem B2305487 : Blo 2305435 2305487 := bstep (se 1 (by rfl) ⟨1729115, by rfl⟩ : syracuseStep 2305487 = 3458231) B3458231
theorem B3458237 : Blo 2305435 3458237 := bbase (se 3 (by rfl) ⟨648419, by rfl⟩ : syracuseStep 3458237 = 1296839) (by norm_num)
theorem B2305491 : Blo 2305435 2305491 := bstep (se 1 (by rfl) ⟨1729118, by rfl⟩ : syracuseStep 2305491 = 3458237) B3458237
theorem B5187365 : Blo 2305435 5187365 := bbase (se 4 (by rfl) ⟨486315, by rfl⟩ : syracuseStep 5187365 = 972631) (by norm_num)
theorem B3458243 : Blo 2305435 3458243 := bstep (se 1 (by rfl) ⟨2593682, by rfl⟩ : syracuseStep 3458243 = 5187365) B5187365
theorem B2305495 : Blo 2305435 2305495 := bstep (se 1 (by rfl) ⟨1729121, by rfl⟩ : syracuseStep 2305495 = 3458243) B3458243
theorem B5835797 : Blo 2305435 5835797 := bbase (se 6 (by rfl) ⟨136776, by rfl⟩ : syracuseStep 5835797 = 273553) (by norm_num)
theorem B3890531 : Blo 2305435 3890531 := bstep (se 1 (by rfl) ⟨2917898, by rfl⟩ : syracuseStep 3890531 = 5835797) B5835797
theorem B2593687 : Blo 2305435 2593687 := bstep (se 1 (by rfl) ⟨1945265, by rfl⟩ : syracuseStep 2593687 = 3890531) B3890531
theorem B3458249 : Blo 2305435 3458249 := bstep (se 2 (by rfl) ⟨1296843, by rfl⟩ : syracuseStep 3458249 = 2593687) B2593687
theorem B2305499 : Blo 2305435 2305499 := bstep (se 1 (by rfl) ⟨1729124, by rfl⟩ : syracuseStep 2305499 = 3458249) B3458249
theorem B9847925 : Blo 2305435 9847925 := bbase (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) (by norm_num)
theorem B6565283 : Blo 2305435 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B4376855 : Blo 2305435 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B11671613 : Blo 2305435 11671613 := bstep (se 3 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 11671613 = 4376855) B4376855
theorem B7781075 : Blo 2305435 7781075 := bstep (se 1 (by rfl) ⟨5835806, by rfl⟩ : syracuseStep 7781075 = 11671613) B11671613
theorem B5187383 : Blo 2305435 5187383 := bstep (se 1 (by rfl) ⟨3890537, by rfl⟩ : syracuseStep 5187383 = 7781075) B7781075
theorem B3458255 : Blo 2305435 3458255 := bstep (se 1 (by rfl) ⟨2593691, by rfl⟩ : syracuseStep 3458255 = 5187383) B5187383
theorem B2305503 : Blo 2305435 2305503 := bstep (se 1 (by rfl) ⟨1729127, by rfl⟩ : syracuseStep 2305503 = 3458255) B3458255
theorem B3458261 : Blo 2305435 3458261 := bbase (se 7 (by rfl) ⟨40526, by rfl⟩ : syracuseStep 3458261 = 81053) (by norm_num)
theorem B2305507 : Blo 2305435 2305507 := bstep (se 1 (by rfl) ⟨1729130, by rfl⟩ : syracuseStep 2305507 = 3458261) B3458261
theorem B3282653 : Blo 2305435 3282653 := bbase (se 3 (by rfl) ⟨615497, by rfl⟩ : syracuseStep 3282653 = 1230995) (by norm_num)
theorem B8753741 : Blo 2305435 8753741 := bstep (se 3 (by rfl) ⟨1641326, by rfl⟩ : syracuseStep 8753741 = 3282653) B3282653
theorem B5835827 : Blo 2305435 5835827 := bstep (se 1 (by rfl) ⟨4376870, by rfl⟩ : syracuseStep 5835827 = 8753741) B8753741
theorem B3890551 : Blo 2305435 3890551 := bstep (se 1 (by rfl) ⟨2917913, by rfl⟩ : syracuseStep 3890551 = 5835827) B5835827
theorem B5187401 : Blo 2305435 5187401 := bstep (se 2 (by rfl) ⟨1945275, by rfl⟩ : syracuseStep 5187401 = 3890551) B3890551
theorem B3458267 : Blo 2305435 3458267 := bstep (se 1 (by rfl) ⟨2593700, by rfl⟩ : syracuseStep 3458267 = 5187401) B5187401
theorem B2305511 : Blo 2305435 2305511 := bstep (se 1 (by rfl) ⟨1729133, by rfl⟩ : syracuseStep 2305511 = 3458267) B3458267
theorem B2593705 : Blo 2305435 2593705 := bbase (se 2 (by rfl) ⟨972639, by rfl⟩ : syracuseStep 2593705 = 1945279) (by norm_num)
theorem B3458273 : Blo 2305435 3458273 := bstep (se 2 (by rfl) ⟨1296852, by rfl⟩ : syracuseStep 3458273 = 2593705) B2593705
theorem B2305515 : Blo 2305435 2305515 := bstep (se 1 (by rfl) ⟨1729136, by rfl⟩ : syracuseStep 2305515 = 3458273) B3458273
theorem B9116981 : Blo 2305435 9116981 := bbase (se 5 (by rfl) ⟨427358, by rfl⟩ : syracuseStep 9116981 = 854717) (by norm_num)
theorem B6077987 : Blo 2305435 6077987 := bstep (se 1 (by rfl) ⟨4558490, by rfl⟩ : syracuseStep 6077987 = 9116981) B9116981
theorem B4051991 : Blo 2305435 4051991 := bstep (se 1 (by rfl) ⟨3038993, by rfl⟩ : syracuseStep 4051991 = 6077987) B6077987
theorem B10805309 : Blo 2305435 10805309 := bstep (se 3 (by rfl) ⟨2025995, by rfl⟩ : syracuseStep 10805309 = 4051991) B4051991
theorem B7203539 : Blo 2305435 7203539 := bstep (se 1 (by rfl) ⟨5402654, by rfl⟩ : syracuseStep 7203539 = 10805309) B10805309
theorem B19209437 : Blo 2305435 19209437 := bstep (se 3 (by rfl) ⟨3601769, by rfl⟩ : syracuseStep 19209437 = 7203539) B7203539
theorem B12806291 : Blo 2305435 12806291 := bstep (se 1 (by rfl) ⟨9604718, by rfl⟩ : syracuseStep 12806291 = 19209437) B19209437
theorem B8537527 : Blo 2305435 8537527 := bstep (se 1 (by rfl) ⟨6403145, by rfl⟩ : syracuseStep 8537527 = 12806291) B12806291
theorem B45533477 : Blo 2305435 45533477 := bstep (se 4 (by rfl) ⟨4268763, by rfl⟩ : syracuseStep 45533477 = 8537527) B8537527
theorem B30355651 : Blo 2305435 30355651 := bstep (se 1 (by rfl) ⟨22766738, by rfl⟩ : syracuseStep 30355651 = 45533477) B45533477
theorem B40474201 : Blo 2305435 40474201 := bstep (se 2 (by rfl) ⟨15177825, by rfl⟩ : syracuseStep 40474201 = 30355651) B30355651
theorem B53965601 : Blo 2305435 53965601 := bstep (se 2 (by rfl) ⟨20237100, by rfl⟩ : syracuseStep 53965601 = 40474201) B40474201
theorem B35977067 : Blo 2305435 35977067 := bstep (se 1 (by rfl) ⟨26982800, by rfl⟩ : syracuseStep 35977067 = 53965601) B53965601
theorem B23984711 : Blo 2305435 23984711 := bstep (se 1 (by rfl) ⟨17988533, by rfl⟩ : syracuseStep 23984711 = 35977067) B35977067
theorem B15989807 : Blo 2305435 15989807 := bstep (se 1 (by rfl) ⟨11992355, by rfl⟩ : syracuseStep 15989807 = 23984711) B23984711
theorem B10659871 : Blo 2305435 10659871 := bstep (se 1 (by rfl) ⟨7994903, by rfl⟩ : syracuseStep 10659871 = 15989807) B15989807
theorem B14213161 : Blo 2305435 14213161 := bstep (se 2 (by rfl) ⟨5329935, by rfl⟩ : syracuseStep 14213161 = 10659871) B10659871
theorem B75803525 : Blo 2305435 75803525 := bstep (se 4 (by rfl) ⟨7106580, by rfl⟩ : syracuseStep 75803525 = 14213161) B14213161
theorem B50535683 : Blo 2305435 50535683 := bstep (se 1 (by rfl) ⟨37901762, by rfl⟩ : syracuseStep 50535683 = 75803525) B75803525
theorem B33690455 : Blo 2305435 33690455 := bstep (se 1 (by rfl) ⟨25267841, by rfl⟩ : syracuseStep 33690455 = 50535683) B50535683
theorem B22460303 : Blo 2305435 22460303 := bstep (se 1 (by rfl) ⟨16845227, by rfl⟩ : syracuseStep 22460303 = 33690455) B33690455
theorem B14973535 : Blo 2305435 14973535 := bstep (se 1 (by rfl) ⟨11230151, by rfl⟩ : syracuseStep 14973535 = 22460303) B22460303
theorem B19964713 : Blo 2305435 19964713 := bstep (se 2 (by rfl) ⟨7486767, by rfl⟩ : syracuseStep 19964713 = 14973535) B14973535
theorem B26619617 : Blo 2305435 26619617 := bstep (se 2 (by rfl) ⟨9982356, by rfl⟩ : syracuseStep 26619617 = 19964713) B19964713
theorem B17746411 : Blo 2305435 17746411 := bstep (se 1 (by rfl) ⟨13309808, by rfl⟩ : syracuseStep 17746411 = 26619617) B26619617
theorem B23661881 : Blo 2305435 23661881 := bstep (se 2 (by rfl) ⟨8873205, by rfl⟩ : syracuseStep 23661881 = 17746411) B17746411
theorem B15774587 : Blo 2305435 15774587 := bstep (se 1 (by rfl) ⟨11830940, by rfl⟩ : syracuseStep 15774587 = 23661881) B23661881
theorem B10516391 : Blo 2305435 10516391 := bstep (se 1 (by rfl) ⟨7887293, by rfl⟩ : syracuseStep 10516391 = 15774587) B15774587
theorem B7010927 : Blo 2305435 7010927 := bstep (se 1 (by rfl) ⟨5258195, by rfl⟩ : syracuseStep 7010927 = 10516391) B10516391
theorem B4673951 : Blo 2305435 4673951 := bstep (se 1 (by rfl) ⟨3505463, by rfl⟩ : syracuseStep 4673951 = 7010927) B7010927
theorem B3115967 : Blo 2305435 3115967 := bstep (se 1 (by rfl) ⟨2336975, by rfl⟩ : syracuseStep 3115967 = 4673951) B4673951
theorem B8309245 : Blo 2305435 8309245 := bstep (se 3 (by rfl) ⟨1557983, by rfl⟩ : syracuseStep 8309245 = 3115967) B3115967
theorem B11078993 : Blo 2305435 11078993 := bstep (se 2 (by rfl) ⟨4154622, by rfl⟩ : syracuseStep 11078993 = 8309245) B8309245
theorem B7385995 : Blo 2305435 7385995 := bstep (se 1 (by rfl) ⟨5539496, by rfl⟩ : syracuseStep 7385995 = 11078993) B11078993
theorem B9847993 : Blo 2305435 9847993 := bstep (se 2 (by rfl) ⟨3692997, by rfl⟩ : syracuseStep 9847993 = 7385995) B7385995
theorem B13130657 : Blo 2305435 13130657 := bstep (se 2 (by rfl) ⟨4923996, by rfl⟩ : syracuseStep 13130657 = 9847993) B9847993
theorem B8753771 : Blo 2305435 8753771 := bstep (se 1 (by rfl) ⟨6565328, by rfl⟩ : syracuseStep 8753771 = 13130657) B13130657
theorem B5835847 : Blo 2305435 5835847 := bstep (se 1 (by rfl) ⟨4376885, by rfl⟩ : syracuseStep 5835847 = 8753771) B8753771
theorem B7781129 : Blo 2305435 7781129 := bstep (se 2 (by rfl) ⟨2917923, by rfl⟩ : syracuseStep 7781129 = 5835847) B5835847
theorem B5187419 : Blo 2305435 5187419 := bstep (se 1 (by rfl) ⟨3890564, by rfl⟩ : syracuseStep 5187419 = 7781129) B7781129
theorem B3458279 : Blo 2305435 3458279 := bstep (se 1 (by rfl) ⟨2593709, by rfl⟩ : syracuseStep 3458279 = 5187419) B5187419
theorem B2305519 : Blo 2305435 2305519 := bstep (se 1 (by rfl) ⟨1729139, by rfl⟩ : syracuseStep 2305519 = 3458279) B3458279
theorem B3458285 : Blo 2305435 3458285 := bbase (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) (by norm_num)
theorem B2305523 : Blo 2305435 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B5187437 : Blo 2305435 5187437 := bbase (se 3 (by rfl) ⟨972644, by rfl⟩ : syracuseStep 5187437 = 1945289) (by norm_num)
theorem B3458291 : Blo 2305435 3458291 := bstep (se 1 (by rfl) ⟨2593718, by rfl⟩ : syracuseStep 3458291 = 5187437) B5187437
theorem B2305527 : Blo 2305435 2305527 := bstep (se 1 (by rfl) ⟨1729145, by rfl⟩ : syracuseStep 2305527 = 3458291) B3458291
theorem B4376909 : Blo 2305435 4376909 := bbase (se 3 (by rfl) ⟨820670, by rfl⟩ : syracuseStep 4376909 = 1641341) (by norm_num)
theorem B2917939 : Blo 2305435 2917939 := bstep (se 1 (by rfl) ⟨2188454, by rfl⟩ : syracuseStep 2917939 = 4376909) B4376909
theorem B3890585 : Blo 2305435 3890585 := bstep (se 2 (by rfl) ⟨1458969, by rfl⟩ : syracuseStep 3890585 = 2917939) B2917939
theorem B2593723 : Blo 2305435 2593723 := bstep (se 1 (by rfl) ⟨1945292, by rfl⟩ : syracuseStep 2593723 = 3890585) B3890585
theorem B3458297 : Blo 2305435 3458297 := bstep (se 2 (by rfl) ⟨1296861, by rfl⟩ : syracuseStep 3458297 = 2593723) B2593723
theorem B2305531 : Blo 2305435 2305531 := bstep (se 1 (by rfl) ⟨1729148, by rfl⟩ : syracuseStep 2305531 = 3458297) B3458297
theorem B23662037 : Blo 2305435 23662037 := bbase (se 7 (by rfl) ⟨277289, by rfl⟩ : syracuseStep 23662037 = 554579) (by norm_num)
theorem B15774691 : Blo 2305435 15774691 := bstep (se 1 (by rfl) ⟨11831018, by rfl⟩ : syracuseStep 15774691 = 23662037) B23662037
theorem B21032921 : Blo 2305435 21032921 := bstep (se 2 (by rfl) ⟨7887345, by rfl⟩ : syracuseStep 21032921 = 15774691) B15774691
theorem B14021947 : Blo 2305435 14021947 := bstep (se 1 (by rfl) ⟨10516460, by rfl⟩ : syracuseStep 14021947 = 21032921) B21032921
theorem B18695929 : Blo 2305435 18695929 := bstep (se 2 (by rfl) ⟨7010973, by rfl⟩ : syracuseStep 18695929 = 14021947) B14021947
theorem B24927905 : Blo 2305435 24927905 := bstep (se 2 (by rfl) ⟨9347964, by rfl⟩ : syracuseStep 24927905 = 18695929) B18695929
theorem B16618603 : Blo 2305435 16618603 := bstep (se 1 (by rfl) ⟨12463952, by rfl⟩ : syracuseStep 16618603 = 24927905) B24927905
theorem B22158137 : Blo 2305435 22158137 := bstep (se 2 (by rfl) ⟨8309301, by rfl⟩ : syracuseStep 22158137 = 16618603) B16618603
theorem B59088365 : Blo 2305435 59088365 := bstep (se 3 (by rfl) ⟨11079068, by rfl⟩ : syracuseStep 59088365 = 22158137) B22158137
theorem B39392243 : Blo 2305435 39392243 := bstep (se 1 (by rfl) ⟨29544182, by rfl⟩ : syracuseStep 39392243 = 59088365) B59088365
theorem B26261495 : Blo 2305435 26261495 := bstep (se 1 (by rfl) ⟨19696121, by rfl⟩ : syracuseStep 26261495 = 39392243) B39392243
theorem B17507663 : Blo 2305435 17507663 := bstep (se 1 (by rfl) ⟨13130747, by rfl⟩ : syracuseStep 17507663 = 26261495) B26261495
theorem B11671775 : Blo 2305435 11671775 := bstep (se 1 (by rfl) ⟨8753831, by rfl⟩ : syracuseStep 11671775 = 17507663) B17507663
theorem B7781183 : Blo 2305435 7781183 := bstep (se 1 (by rfl) ⟨5835887, by rfl⟩ : syracuseStep 7781183 = 11671775) B11671775
theorem B5187455 : Blo 2305435 5187455 := bstep (se 1 (by rfl) ⟨3890591, by rfl⟩ : syracuseStep 5187455 = 7781183) B7781183
theorem B3458303 : Blo 2305435 3458303 := bstep (se 1 (by rfl) ⟨2593727, by rfl⟩ : syracuseStep 3458303 = 5187455) B5187455
theorem B2305535 : Blo 2305435 2305535 := bstep (se 1 (by rfl) ⟨1729151, by rfl⟩ : syracuseStep 2305535 = 3458303) B3458303
theorem B3458309 : Blo 2305435 3458309 := bbase (se 4 (by rfl) ⟨324216, by rfl⟩ : syracuseStep 3458309 = 648433) (by norm_num)
theorem B2305539 : Blo 2305435 2305539 := bstep (se 1 (by rfl) ⟨1729154, by rfl⟩ : syracuseStep 2305539 = 3458309) B3458309
theorem B3890605 : Blo 2305435 3890605 := bbase (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) (by norm_num)
theorem B5187473 : Blo 2305435 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B3458315 : Blo 2305435 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B2305543 : Blo 2305435 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B2593741 : Blo 2305435 2593741 := bbase (se 3 (by rfl) ⟨486326, by rfl⟩ : syracuseStep 2593741 = 972653) (by norm_num)
theorem B3458321 : Blo 2305435 3458321 := bstep (se 2 (by rfl) ⟨1296870, by rfl⟩ : syracuseStep 3458321 = 2593741) B2593741
theorem B2305547 : Blo 2305435 2305547 := bstep (se 1 (by rfl) ⟨1729160, by rfl⟩ : syracuseStep 2305547 = 3458321) B3458321
theorem B7781237 : Blo 2305435 7781237 := bbase (se 5 (by rfl) ⟨364745, by rfl⟩ : syracuseStep 7781237 = 729491) (by norm_num)
theorem B5187491 : Blo 2305435 5187491 := bstep (se 1 (by rfl) ⟨3890618, by rfl⟩ : syracuseStep 5187491 = 7781237) B7781237
theorem B3458327 : Blo 2305435 3458327 := bstep (se 1 (by rfl) ⟨2593745, by rfl⟩ : syracuseStep 3458327 = 5187491) B5187491
theorem B2305551 : Blo 2305435 2305551 := bstep (se 1 (by rfl) ⟨1729163, by rfl⟩ : syracuseStep 2305551 = 3458327) B3458327
theorem B3458333 : Blo 2305435 3458333 := bbase (se 3 (by rfl) ⟨648437, by rfl⟩ : syracuseStep 3458333 = 1296875) (by norm_num)
theorem B2305555 : Blo 2305435 2305555 := bstep (se 1 (by rfl) ⟨1729166, by rfl⟩ : syracuseStep 2305555 = 3458333) B3458333
theorem B5187509 : Blo 2305435 5187509 := bbase (se 5 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 5187509 = 486329) (by norm_num)
theorem B3458339 : Blo 2305435 3458339 := bstep (se 1 (by rfl) ⟨2593754, by rfl⟩ : syracuseStep 3458339 = 5187509) B5187509
theorem B2305559 : Blo 2305435 2305559 := bstep (se 1 (by rfl) ⟨1729169, by rfl⟩ : syracuseStep 2305559 = 3458339) B3458339
theorem B3327517 : Blo 2305435 3327517 := bbase (se 3 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 3327517 = 1247819) (by norm_num)
theorem B4436689 : Blo 2305435 4436689 := bstep (se 2 (by rfl) ⟨1663758, by rfl⟩ : syracuseStep 4436689 = 3327517) B3327517
theorem B5915585 : Blo 2305435 5915585 := bstep (se 2 (by rfl) ⟨2218344, by rfl⟩ : syracuseStep 5915585 = 4436689) B4436689
theorem B3943723 : Blo 2305435 3943723 := bstep (se 1 (by rfl) ⟨2957792, by rfl⟩ : syracuseStep 3943723 = 5915585) B5915585
theorem B5258297 : Blo 2305435 5258297 := bstep (se 2 (by rfl) ⟨1971861, by rfl⟩ : syracuseStep 5258297 = 3943723) B3943723
theorem B3505531 : Blo 2305435 3505531 := bstep (se 1 (by rfl) ⟨2629148, by rfl⟩ : syracuseStep 3505531 = 5258297) B5258297
theorem B4674041 : Blo 2305435 4674041 := bstep (se 2 (by rfl) ⟨1752765, by rfl⟩ : syracuseStep 4674041 = 3505531) B3505531
theorem B3116027 : Blo 2305435 3116027 := bstep (se 1 (by rfl) ⟨2337020, by rfl⟩ : syracuseStep 3116027 = 4674041) B4674041
theorem B8309405 : Blo 2305435 8309405 := bstep (se 3 (by rfl) ⟨1558013, by rfl⟩ : syracuseStep 8309405 = 3116027) B3116027
theorem B5539603 : Blo 2305435 5539603 := bstep (se 1 (by rfl) ⟨4154702, by rfl⟩ : syracuseStep 5539603 = 8309405) B8309405
theorem B7386137 : Blo 2305435 7386137 := bstep (se 2 (by rfl) ⟨2769801, by rfl⟩ : syracuseStep 7386137 = 5539603) B5539603
theorem B4924091 : Blo 2305435 4924091 := bstep (se 1 (by rfl) ⟨3693068, by rfl⟩ : syracuseStep 4924091 = 7386137) B7386137
theorem B13130909 : Blo 2305435 13130909 := bstep (se 3 (by rfl) ⟨2462045, by rfl⟩ : syracuseStep 13130909 = 4924091) B4924091
theorem B8753939 : Blo 2305435 8753939 := bstep (se 1 (by rfl) ⟨6565454, by rfl⟩ : syracuseStep 8753939 = 13130909) B13130909
theorem B5835959 : Blo 2305435 5835959 := bstep (se 1 (by rfl) ⟨4376969, by rfl⟩ : syracuseStep 5835959 = 8753939) B8753939
theorem B3890639 : Blo 2305435 3890639 := bstep (se 1 (by rfl) ⟨2917979, by rfl⟩ : syracuseStep 3890639 = 5835959) B5835959
theorem B2593759 : Blo 2305435 2593759 := bstep (se 1 (by rfl) ⟨1945319, by rfl⟩ : syracuseStep 2593759 = 3890639) B3890639
theorem B3458345 : Blo 2305435 3458345 := bstep (se 2 (by rfl) ⟨1296879, by rfl⟩ : syracuseStep 3458345 = 2593759) B2593759
theorem B2305563 : Blo 2305435 2305563 := bstep (se 1 (by rfl) ⟨1729172, by rfl⟩ : syracuseStep 2305563 = 3458345) B3458345
theorem B7386149 : Blo 2305435 7386149 := bbase (se 4 (by rfl) ⟨692451, by rfl⟩ : syracuseStep 7386149 = 1384903) (by norm_num)
theorem B4924099 : Blo 2305435 4924099 := bstep (se 1 (by rfl) ⟨3693074, by rfl⟩ : syracuseStep 4924099 = 7386149) B7386149
theorem B6565465 : Blo 2305435 6565465 := bstep (se 2 (by rfl) ⟨2462049, by rfl⟩ : syracuseStep 6565465 = 4924099) B4924099
theorem B8753953 : Blo 2305435 8753953 := bstep (se 2 (by rfl) ⟨3282732, by rfl⟩ : syracuseStep 8753953 = 6565465) B6565465
theorem B11671937 : Blo 2305435 11671937 := bstep (se 2 (by rfl) ⟨4376976, by rfl⟩ : syracuseStep 11671937 = 8753953) B8753953
theorem B7781291 : Blo 2305435 7781291 := bstep (se 1 (by rfl) ⟨5835968, by rfl⟩ : syracuseStep 7781291 = 11671937) B11671937
theorem B5187527 : Blo 2305435 5187527 := bstep (se 1 (by rfl) ⟨3890645, by rfl⟩ : syracuseStep 5187527 = 7781291) B7781291
theorem B3458351 : Blo 2305435 3458351 := bstep (se 1 (by rfl) ⟨2593763, by rfl⟩ : syracuseStep 3458351 = 5187527) B5187527
theorem B2305567 : Blo 2305435 2305567 := bstep (se 1 (by rfl) ⟨1729175, by rfl⟩ : syracuseStep 2305567 = 3458351) B3458351
theorem B3458357 : Blo 2305435 3458357 := bbase (se 5 (by rfl) ⟨162110, by rfl⟩ : syracuseStep 3458357 = 324221) (by norm_num)
theorem B2305571 : Blo 2305435 2305571 := bstep (se 1 (by rfl) ⟨1729178, by rfl⟩ : syracuseStep 2305571 = 3458357) B3458357
theorem B5835989 : Blo 2305435 5835989 := bbase (se 7 (by rfl) ⟨68390, by rfl⟩ : syracuseStep 5835989 = 136781) (by norm_num)
theorem B3890659 : Blo 2305435 3890659 := bstep (se 1 (by rfl) ⟨2917994, by rfl⟩ : syracuseStep 3890659 = 5835989) B5835989
theorem B5187545 : Blo 2305435 5187545 := bstep (se 2 (by rfl) ⟨1945329, by rfl⟩ : syracuseStep 5187545 = 3890659) B3890659
theorem B3458363 : Blo 2305435 3458363 := bstep (se 1 (by rfl) ⟨2593772, by rfl⟩ : syracuseStep 3458363 = 5187545) B5187545
theorem B2305575 : Blo 2305435 2305575 := bstep (se 1 (by rfl) ⟨1729181, by rfl⟩ : syracuseStep 2305575 = 3458363) B3458363
theorem B2593777 : Blo 2305435 2593777 := bbase (se 2 (by rfl) ⟨972666, by rfl⟩ : syracuseStep 2593777 = 1945333) (by norm_num)
theorem B3458369 : Blo 2305435 3458369 := bstep (se 2 (by rfl) ⟨1296888, by rfl⟩ : syracuseStep 3458369 = 2593777) B2593777
theorem B2305579 : Blo 2305435 2305579 := bstep (se 1 (by rfl) ⟨1729184, by rfl⟩ : syracuseStep 2305579 = 3458369) B3458369
theorem B11079301 : Blo 2305435 11079301 := bbase (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) (by norm_num)
theorem B14772401 : Blo 2305435 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B9848267 : Blo 2305435 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B6565511 : Blo 2305435 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B4377007 : Blo 2305435 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B5836009 : Blo 2305435 5836009 := bstep (se 2 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 5836009 = 4377007) B4377007
theorem B7781345 : Blo 2305435 7781345 := bstep (se 2 (by rfl) ⟨2918004, by rfl⟩ : syracuseStep 7781345 = 5836009) B5836009
theorem B5187563 : Blo 2305435 5187563 := bstep (se 1 (by rfl) ⟨3890672, by rfl⟩ : syracuseStep 5187563 = 7781345) B7781345
theorem B3458375 : Blo 2305435 3458375 := bstep (se 1 (by rfl) ⟨2593781, by rfl⟩ : syracuseStep 3458375 = 5187563) B5187563
theorem B2305583 : Blo 2305435 2305583 := bstep (se 1 (by rfl) ⟨1729187, by rfl⟩ : syracuseStep 2305583 = 3458375) B3458375
theorem B3458381 : Blo 2305435 3458381 := bbase (se 3 (by rfl) ⟨648446, by rfl⟩ : syracuseStep 3458381 = 1296893) (by norm_num)
theorem B2305587 : Blo 2305435 2305587 := bstep (se 1 (by rfl) ⟨1729190, by rfl⟩ : syracuseStep 2305587 = 3458381) B3458381
theorem B5187581 : Blo 2305435 5187581 := bbase (se 3 (by rfl) ⟨972671, by rfl⟩ : syracuseStep 5187581 = 1945343) (by norm_num)
theorem B3458387 : Blo 2305435 3458387 := bstep (se 1 (by rfl) ⟨2593790, by rfl⟩ : syracuseStep 3458387 = 5187581) B5187581
theorem B2305591 : Blo 2305435 2305591 := bstep (se 1 (by rfl) ⟨1729193, by rfl⟩ : syracuseStep 2305591 = 3458387) B3458387
theorem B3890693 : Blo 2305435 3890693 := bbase (se 4 (by rfl) ⟨364752, by rfl⟩ : syracuseStep 3890693 = 729505) (by norm_num)
theorem B2593795 : Blo 2305435 2593795 := bstep (se 1 (by rfl) ⟨1945346, by rfl⟩ : syracuseStep 2593795 = 3890693) B3890693
theorem B3458393 : Blo 2305435 3458393 := bstep (se 2 (by rfl) ⟨1296897, by rfl⟩ : syracuseStep 3458393 = 2593795) B2593795
theorem B2305595 : Blo 2305435 2305595 := bstep (se 1 (by rfl) ⟨1729196, by rfl⟩ : syracuseStep 2305595 = 3458393) B3458393
theorem B17508149 : Blo 2305435 17508149 := bbase (se 5 (by rfl) ⟨820694, by rfl⟩ : syracuseStep 17508149 = 1641389) (by norm_num)
theorem B11672099 : Blo 2305435 11672099 := bstep (se 1 (by rfl) ⟨8754074, by rfl⟩ : syracuseStep 11672099 = 17508149) B17508149
theorem B7781399 : Blo 2305435 7781399 := bstep (se 1 (by rfl) ⟨5836049, by rfl⟩ : syracuseStep 7781399 = 11672099) B11672099
theorem B5187599 : Blo 2305435 5187599 := bstep (se 1 (by rfl) ⟨3890699, by rfl⟩ : syracuseStep 5187599 = 7781399) B7781399
theorem B3458399 : Blo 2305435 3458399 := bstep (se 1 (by rfl) ⟨2593799, by rfl⟩ : syracuseStep 3458399 = 5187599) B5187599
theorem B2305599 : Blo 2305435 2305599 := bstep (se 1 (by rfl) ⟨1729199, by rfl⟩ : syracuseStep 2305599 = 3458399) B3458399
theorem B3458405 : Blo 2305435 3458405 := bbase (se 4 (by rfl) ⟨324225, by rfl⟩ : syracuseStep 3458405 = 648451) (by norm_num)
theorem B2305603 : Blo 2305435 2305603 := bstep (se 1 (by rfl) ⟨1729202, by rfl⟩ : syracuseStep 2305603 = 3458405) B3458405
theorem B4377053 : Blo 2305435 4377053 := bbase (se 3 (by rfl) ⟨820697, by rfl⟩ : syracuseStep 4377053 = 1641395) (by norm_num)
theorem B2918035 : Blo 2305435 2918035 := bstep (se 1 (by rfl) ⟨2188526, by rfl⟩ : syracuseStep 2918035 = 4377053) B4377053
theorem B3890713 : Blo 2305435 3890713 := bstep (se 2 (by rfl) ⟨1459017, by rfl⟩ : syracuseStep 3890713 = 2918035) B2918035
theorem B5187617 : Blo 2305435 5187617 := bstep (se 2 (by rfl) ⟨1945356, by rfl⟩ : syracuseStep 5187617 = 3890713) B3890713
theorem B3458411 : Blo 2305435 3458411 := bstep (se 1 (by rfl) ⟨2593808, by rfl⟩ : syracuseStep 3458411 = 5187617) B5187617
theorem B2305607 : Blo 2305435 2305607 := bstep (se 1 (by rfl) ⟨1729205, by rfl⟩ : syracuseStep 2305607 = 3458411) B3458411
theorem B2593813 : Blo 2305435 2593813 := bbase (se 6 (by rfl) ⟨60792, by rfl⟩ : syracuseStep 2593813 = 121585) (by norm_num)
theorem B3458417 : Blo 2305435 3458417 := bstep (se 2 (by rfl) ⟨1296906, by rfl⟩ : syracuseStep 3458417 = 2593813) B2593813
theorem B2305611 : Blo 2305435 2305611 := bstep (se 1 (by rfl) ⟨1729208, by rfl⟩ : syracuseStep 2305611 = 3458417) B3458417
theorem B2918045 : Blo 2305435 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B7781453 : Blo 2305435 7781453 := bstep (se 3 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 7781453 = 2918045) B2918045
theorem B5187635 : Blo 2305435 5187635 := bstep (se 1 (by rfl) ⟨3890726, by rfl⟩ : syracuseStep 5187635 = 7781453) B7781453
theorem B3458423 : Blo 2305435 3458423 := bstep (se 1 (by rfl) ⟨2593817, by rfl⟩ : syracuseStep 3458423 = 5187635) B5187635
theorem B2305615 : Blo 2305435 2305615 := bstep (se 1 (by rfl) ⟨1729211, by rfl⟩ : syracuseStep 2305615 = 3458423) B3458423
theorem B3458429 : Blo 2305435 3458429 := bbase (se 3 (by rfl) ⟨648455, by rfl⟩ : syracuseStep 3458429 = 1296911) (by norm_num)
theorem B2305619 : Blo 2305435 2305619 := bstep (se 1 (by rfl) ⟨1729214, by rfl⟩ : syracuseStep 2305619 = 3458429) B3458429
theorem B5187653 : Blo 2305435 5187653 := bbase (se 4 (by rfl) ⟨486342, by rfl⟩ : syracuseStep 5187653 = 972685) (by norm_num)
theorem B3458435 : Blo 2305435 3458435 := bstep (se 1 (by rfl) ⟨2593826, by rfl⟩ : syracuseStep 3458435 = 5187653) B5187653
theorem B2305623 : Blo 2305435 2305623 := bstep (se 1 (by rfl) ⟨1729217, by rfl⟩ : syracuseStep 2305623 = 3458435) B3458435
theorem B6565637 : Blo 2305435 6565637 := bbase (se 4 (by rfl) ⟨615528, by rfl⟩ : syracuseStep 6565637 = 1231057) (by norm_num)
theorem B4377091 : Blo 2305435 4377091 := bstep (se 1 (by rfl) ⟨3282818, by rfl⟩ : syracuseStep 4377091 = 6565637) B6565637
theorem B5836121 : Blo 2305435 5836121 := bstep (se 2 (by rfl) ⟨2188545, by rfl⟩ : syracuseStep 5836121 = 4377091) B4377091
theorem B3890747 : Blo 2305435 3890747 := bstep (se 1 (by rfl) ⟨2918060, by rfl⟩ : syracuseStep 3890747 = 5836121) B5836121
theorem B2593831 : Blo 2305435 2593831 := bstep (se 1 (by rfl) ⟨1945373, by rfl⟩ : syracuseStep 2593831 = 3890747) B3890747
theorem B3458441 : Blo 2305435 3458441 := bstep (se 2 (by rfl) ⟨1296915, by rfl⟩ : syracuseStep 3458441 = 2593831) B2593831
theorem B2305627 : Blo 2305435 2305627 := bstep (se 1 (by rfl) ⟨1729220, by rfl⟩ : syracuseStep 2305627 = 3458441) B3458441
theorem B11672261 : Blo 2305435 11672261 := bbase (se 4 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 11672261 = 2188549) (by norm_num)
theorem B7781507 : Blo 2305435 7781507 := bstep (se 1 (by rfl) ⟨5836130, by rfl⟩ : syracuseStep 7781507 = 11672261) B11672261
theorem B5187671 : Blo 2305435 5187671 := bstep (se 1 (by rfl) ⟨3890753, by rfl⟩ : syracuseStep 5187671 = 7781507) B7781507
theorem B3458447 : Blo 2305435 3458447 := bstep (se 1 (by rfl) ⟨2593835, by rfl⟩ : syracuseStep 3458447 = 5187671) B5187671
theorem B2305631 : Blo 2305435 2305631 := bstep (se 1 (by rfl) ⟨1729223, by rfl⟩ : syracuseStep 2305631 = 3458447) B3458447
theorem B3458453 : Blo 2305435 3458453 := bbase (se 6 (by rfl) ⟨81057, by rfl⟩ : syracuseStep 3458453 = 162115) (by norm_num)
theorem B2305635 : Blo 2305435 2305635 := bstep (se 1 (by rfl) ⟨1729226, by rfl⟩ : syracuseStep 2305635 = 3458453) B3458453
theorem B4924253 : Blo 2305435 4924253 := bbase (se 3 (by rfl) ⟨923297, by rfl⟩ : syracuseStep 4924253 = 1846595) (by norm_num)
theorem B13131341 : Blo 2305435 13131341 := bstep (se 3 (by rfl) ⟨2462126, by rfl⟩ : syracuseStep 13131341 = 4924253) B4924253
theorem B8754227 : Blo 2305435 8754227 := bstep (se 1 (by rfl) ⟨6565670, by rfl⟩ : syracuseStep 8754227 = 13131341) B13131341
theorem B5836151 : Blo 2305435 5836151 := bstep (se 1 (by rfl) ⟨4377113, by rfl⟩ : syracuseStep 5836151 = 8754227) B8754227
theorem B3890767 : Blo 2305435 3890767 := bstep (se 1 (by rfl) ⟨2918075, by rfl⟩ : syracuseStep 3890767 = 5836151) B5836151
theorem B5187689 : Blo 2305435 5187689 := bstep (se 2 (by rfl) ⟨1945383, by rfl⟩ : syracuseStep 5187689 = 3890767) B3890767
theorem B3458459 : Blo 2305435 3458459 := bstep (se 1 (by rfl) ⟨2593844, by rfl⟩ : syracuseStep 3458459 = 5187689) B5187689
theorem B2305639 : Blo 2305435 2305639 := bstep (se 1 (by rfl) ⟨1729229, by rfl⟩ : syracuseStep 2305639 = 3458459) B3458459
theorem B2593849 : Blo 2305435 2593849 := bbase (se 2 (by rfl) ⟨972693, by rfl⟩ : syracuseStep 2593849 = 1945387) (by norm_num)
theorem B3458465 : Blo 2305435 3458465 := bstep (se 2 (by rfl) ⟨1296924, by rfl⟩ : syracuseStep 3458465 = 2593849) B2593849
theorem B2305643 : Blo 2305435 2305643 := bstep (se 1 (by rfl) ⟨1729232, by rfl⟩ : syracuseStep 2305643 = 3458465) B3458465
theorem B5539805 : Blo 2305435 5539805 := bbase (se 3 (by rfl) ⟨1038713, by rfl⟩ : syracuseStep 5539805 = 2077427) (by norm_num)
theorem B3693203 : Blo 2305435 3693203 := bstep (se 1 (by rfl) ⟨2769902, by rfl⟩ : syracuseStep 3693203 = 5539805) B5539805
theorem B2462135 : Blo 2305435 2462135 := bstep (se 1 (by rfl) ⟨1846601, by rfl⟩ : syracuseStep 2462135 = 3693203) B3693203
theorem B6565693 : Blo 2305435 6565693 := bstep (se 3 (by rfl) ⟨1231067, by rfl⟩ : syracuseStep 6565693 = 2462135) B2462135
theorem B8754257 : Blo 2305435 8754257 := bstep (se 2 (by rfl) ⟨3282846, by rfl⟩ : syracuseStep 8754257 = 6565693) B6565693
theorem B5836171 : Blo 2305435 5836171 := bstep (se 1 (by rfl) ⟨4377128, by rfl⟩ : syracuseStep 5836171 = 8754257) B8754257
theorem B7781561 : Blo 2305435 7781561 := bstep (se 2 (by rfl) ⟨2918085, by rfl⟩ : syracuseStep 7781561 = 5836171) B5836171
theorem B5187707 : Blo 2305435 5187707 := bstep (se 1 (by rfl) ⟨3890780, by rfl⟩ : syracuseStep 5187707 = 7781561) B7781561
theorem B3458471 : Blo 2305435 3458471 := bstep (se 1 (by rfl) ⟨2593853, by rfl⟩ : syracuseStep 3458471 = 5187707) B5187707
theorem B2305647 : Blo 2305435 2305647 := bstep (se 1 (by rfl) ⟨1729235, by rfl⟩ : syracuseStep 2305647 = 3458471) B3458471
theorem B3458477 : Blo 2305435 3458477 := bbase (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) (by norm_num)
theorem B2305651 : Blo 2305435 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B5187725 : Blo 2305435 5187725 := bbase (se 3 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 5187725 = 1945397) (by norm_num)
theorem B3458483 : Blo 2305435 3458483 := bstep (se 1 (by rfl) ⟨2593862, by rfl⟩ : syracuseStep 3458483 = 5187725) B5187725
theorem B2305655 : Blo 2305435 2305655 := bstep (se 1 (by rfl) ⟨1729241, by rfl⟩ : syracuseStep 2305655 = 3458483) B3458483
theorem B2918101 : Blo 2305435 2918101 := bbase (se 7 (by rfl) ⟨34196, by rfl⟩ : syracuseStep 2918101 = 68393) (by norm_num)
theorem B3890801 : Blo 2305435 3890801 := bstep (se 2 (by rfl) ⟨1459050, by rfl⟩ : syracuseStep 3890801 = 2918101) B2918101
theorem B2593867 : Blo 2305435 2593867 := bstep (se 1 (by rfl) ⟨1945400, by rfl⟩ : syracuseStep 2593867 = 3890801) B3890801
theorem B3458489 : Blo 2305435 3458489 := bstep (se 2 (by rfl) ⟨1296933, by rfl⟩ : syracuseStep 3458489 = 2593867) B2593867
theorem B2305659 : Blo 2305435 2305659 := bstep (se 1 (by rfl) ⟨1729244, by rfl⟩ : syracuseStep 2305659 = 3458489) B3458489
theorem B2629261 : Blo 2305435 2629261 := bbase (se 3 (by rfl) ⟨492986, by rfl⟩ : syracuseStep 2629261 = 985973) (by norm_num)
theorem B14022725 : Blo 2305435 14022725 := bstep (se 4 (by rfl) ⟨1314630, by rfl⟩ : syracuseStep 14022725 = 2629261) B2629261
theorem B149575733 : Blo 2305435 149575733 := bstep (se 5 (by rfl) ⟨7011362, by rfl⟩ : syracuseStep 149575733 = 14022725) B14022725
theorem B99717155 : Blo 2305435 99717155 := bstep (se 1 (by rfl) ⟨74787866, by rfl⟩ : syracuseStep 99717155 = 149575733) B149575733
theorem B66478103 : Blo 2305435 66478103 := bstep (se 1 (by rfl) ⟨49858577, by rfl⟩ : syracuseStep 66478103 = 99717155) B99717155
theorem B44318735 : Blo 2305435 44318735 := bstep (se 1 (by rfl) ⟨33239051, by rfl⟩ : syracuseStep 44318735 = 66478103) B66478103
theorem B29545823 : Blo 2305435 29545823 := bstep (se 1 (by rfl) ⟨22159367, by rfl⟩ : syracuseStep 29545823 = 44318735) B44318735
theorem B19697215 : Blo 2305435 19697215 := bstep (se 1 (by rfl) ⟨14772911, by rfl⟩ : syracuseStep 19697215 = 29545823) B29545823
theorem B26262953 : Blo 2305435 26262953 := bstep (se 2 (by rfl) ⟨9848607, by rfl⟩ : syracuseStep 26262953 = 19697215) B19697215
theorem B17508635 : Blo 2305435 17508635 := bstep (se 1 (by rfl) ⟨13131476, by rfl⟩ : syracuseStep 17508635 = 26262953) B26262953
theorem B11672423 : Blo 2305435 11672423 := bstep (se 1 (by rfl) ⟨8754317, by rfl⟩ : syracuseStep 11672423 = 17508635) B17508635
theorem B7781615 : Blo 2305435 7781615 := bstep (se 1 (by rfl) ⟨5836211, by rfl⟩ : syracuseStep 7781615 = 11672423) B11672423
theorem B5187743 : Blo 2305435 5187743 := bstep (se 1 (by rfl) ⟨3890807, by rfl⟩ : syracuseStep 5187743 = 7781615) B7781615
theorem B3458495 : Blo 2305435 3458495 := bstep (se 1 (by rfl) ⟨2593871, by rfl⟩ : syracuseStep 3458495 = 5187743) B5187743
theorem B2305663 : Blo 2305435 2305663 := bstep (se 1 (by rfl) ⟨1729247, by rfl⟩ : syracuseStep 2305663 = 3458495) B3458495
theorem B3458501 : Blo 2305435 3458501 := bbase (se 4 (by rfl) ⟨324234, by rfl⟩ : syracuseStep 3458501 = 648469) (by norm_num)
theorem B2305667 : Blo 2305435 2305667 := bstep (se 1 (by rfl) ⟨1729250, by rfl⟩ : syracuseStep 2305667 = 3458501) B3458501
theorem B3890821 : Blo 2305435 3890821 := bbase (se 4 (by rfl) ⟨364764, by rfl⟩ : syracuseStep 3890821 = 729529) (by norm_num)
theorem B5187761 : Blo 2305435 5187761 := bstep (se 2 (by rfl) ⟨1945410, by rfl⟩ : syracuseStep 5187761 = 3890821) B3890821
theorem B3458507 : Blo 2305435 3458507 := bstep (se 1 (by rfl) ⟨2593880, by rfl⟩ : syracuseStep 3458507 = 5187761) B5187761
theorem B2305671 : Blo 2305435 2305671 := bstep (se 1 (by rfl) ⟨1729253, by rfl⟩ : syracuseStep 2305671 = 3458507) B3458507
theorem B2593885 : Blo 2305435 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B3458513 : Blo 2305435 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B2305675 : Blo 2305435 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B7781669 : Blo 2305435 7781669 := bbase (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) (by norm_num)
theorem B5187779 : Blo 2305435 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B3458519 : Blo 2305435 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B2305679 : Blo 2305435 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B3458525 : Blo 2305435 3458525 := bbase (se 3 (by rfl) ⟨648473, by rfl⟩ : syracuseStep 3458525 = 1296947) (by norm_num)
theorem B2305683 : Blo 2305435 2305683 := bstep (se 1 (by rfl) ⟨1729262, by rfl⟩ : syracuseStep 2305683 = 3458525) B3458525
theorem B5187797 : Blo 2305435 5187797 := bbase (se 7 (by rfl) ⟨60794, by rfl⟩ : syracuseStep 5187797 = 121589) (by norm_num)
theorem B3458531 : Blo 2305435 3458531 := bstep (se 1 (by rfl) ⟨2593898, by rfl⟩ : syracuseStep 3458531 = 5187797) B5187797
theorem B2305687 : Blo 2305435 2305687 := bstep (se 1 (by rfl) ⟨1729265, by rfl⟩ : syracuseStep 2305687 = 3458531) B3458531
theorem B4154933 : Blo 2305435 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B11079821 : Blo 2305435 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B7386547 : Blo 2305435 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B9848729 : Blo 2305435 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B6565819 : Blo 2305435 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B8754425 : Blo 2305435 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B5836283 : Blo 2305435 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B3890855 : Blo 2305435 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B2593903 : Blo 2305435 2593903 := bstep (se 1 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 2593903 = 3890855) B3890855
theorem B3458537 : Blo 2305435 3458537 := bstep (se 2 (by rfl) ⟨1296951, by rfl⟩ : syracuseStep 3458537 = 2593903) B2593903
theorem B2305691 : Blo 2305435 2305691 := bstep (se 1 (by rfl) ⟨1729268, by rfl⟩ : syracuseStep 2305691 = 3458537) B3458537
theorem B7011461 : Blo 2305435 7011461 := bbase (se 4 (by rfl) ⟨657324, by rfl⟩ : syracuseStep 7011461 = 1314649) (by norm_num)
theorem B18697229 : Blo 2305435 18697229 := bstep (se 3 (by rfl) ⟨3505730, by rfl⟩ : syracuseStep 18697229 = 7011461) B7011461
theorem B12464819 : Blo 2305435 12464819 := bstep (se 1 (by rfl) ⟨9348614, by rfl⟩ : syracuseStep 12464819 = 18697229) B18697229
theorem B8309879 : Blo 2305435 8309879 := bstep (se 1 (by rfl) ⟨6232409, by rfl⟩ : syracuseStep 8309879 = 12464819) B12464819
theorem B5539919 : Blo 2305435 5539919 := bstep (se 1 (by rfl) ⟨4154939, by rfl⟩ : syracuseStep 5539919 = 8309879) B8309879
theorem B14773117 : Blo 2305435 14773117 := bstep (se 3 (by rfl) ⟨2769959, by rfl⟩ : syracuseStep 14773117 = 5539919) B5539919
theorem B19697489 : Blo 2305435 19697489 := bstep (se 2 (by rfl) ⟨7386558, by rfl⟩ : syracuseStep 19697489 = 14773117) B14773117
theorem B13131659 : Blo 2305435 13131659 := bstep (se 1 (by rfl) ⟨9848744, by rfl⟩ : syracuseStep 13131659 = 19697489) B19697489
theorem B8754439 : Blo 2305435 8754439 := bstep (se 1 (by rfl) ⟨6565829, by rfl⟩ : syracuseStep 8754439 = 13131659) B13131659
theorem B11672585 : Blo 2305435 11672585 := bstep (se 2 (by rfl) ⟨4377219, by rfl⟩ : syracuseStep 11672585 = 8754439) B8754439
theorem B7781723 : Blo 2305435 7781723 := bstep (se 1 (by rfl) ⟨5836292, by rfl⟩ : syracuseStep 7781723 = 11672585) B11672585
theorem B5187815 : Blo 2305435 5187815 := bstep (se 1 (by rfl) ⟨3890861, by rfl⟩ : syracuseStep 5187815 = 7781723) B7781723
theorem B3458543 : Blo 2305435 3458543 := bstep (se 1 (by rfl) ⟨2593907, by rfl⟩ : syracuseStep 3458543 = 5187815) B5187815
theorem B2305695 : Blo 2305435 2305695 := bstep (se 1 (by rfl) ⟨1729271, by rfl⟩ : syracuseStep 2305695 = 3458543) B3458543
theorem B3458549 : Blo 2305435 3458549 := bbase (se 5 (by rfl) ⟨162119, by rfl⟩ : syracuseStep 3458549 = 324239) (by norm_num)
theorem B2305699 : Blo 2305435 2305699 := bstep (se 1 (by rfl) ⟨1729274, by rfl⟩ : syracuseStep 2305699 = 3458549) B3458549
theorem B3693293 : Blo 2305435 3693293 := bbase (se 3 (by rfl) ⟨692492, by rfl⟩ : syracuseStep 3693293 = 1384985) (by norm_num)
theorem B2462195 : Blo 2305435 2462195 := bstep (se 1 (by rfl) ⟨1846646, by rfl⟩ : syracuseStep 2462195 = 3693293) B3693293
theorem B6565853 : Blo 2305435 6565853 := bstep (se 3 (by rfl) ⟨1231097, by rfl⟩ : syracuseStep 6565853 = 2462195) B2462195
theorem B4377235 : Blo 2305435 4377235 := bstep (se 1 (by rfl) ⟨3282926, by rfl⟩ : syracuseStep 4377235 = 6565853) B6565853
theorem B5836313 : Blo 2305435 5836313 := bstep (se 2 (by rfl) ⟨2188617, by rfl⟩ : syracuseStep 5836313 = 4377235) B4377235
theorem B3890875 : Blo 2305435 3890875 := bstep (se 1 (by rfl) ⟨2918156, by rfl⟩ : syracuseStep 3890875 = 5836313) B5836313
theorem B5187833 : Blo 2305435 5187833 := bstep (se 2 (by rfl) ⟨1945437, by rfl⟩ : syracuseStep 5187833 = 3890875) B3890875
theorem B3458555 : Blo 2305435 3458555 := bstep (se 1 (by rfl) ⟨2593916, by rfl⟩ : syracuseStep 3458555 = 5187833) B5187833
theorem B2305703 : Blo 2305435 2305703 := bstep (se 1 (by rfl) ⟨1729277, by rfl⟩ : syracuseStep 2305703 = 3458555) B3458555
theorem B2593921 : Blo 2305435 2593921 := bbase (se 2 (by rfl) ⟨972720, by rfl⟩ : syracuseStep 2593921 = 1945441) (by norm_num)
theorem B3458561 : Blo 2305435 3458561 := bstep (se 2 (by rfl) ⟨1296960, by rfl⟩ : syracuseStep 3458561 = 2593921) B2593921
theorem B2305707 : Blo 2305435 2305707 := bstep (se 1 (by rfl) ⟨1729280, by rfl⟩ : syracuseStep 2305707 = 3458561) B3458561
theorem B5836333 : Blo 2305435 5836333 := bbase (se 3 (by rfl) ⟨1094312, by rfl⟩ : syracuseStep 5836333 = 2188625) (by norm_num)
theorem B7781777 : Blo 2305435 7781777 := bstep (se 2 (by rfl) ⟨2918166, by rfl⟩ : syracuseStep 7781777 = 5836333) B5836333
theorem B5187851 : Blo 2305435 5187851 := bstep (se 1 (by rfl) ⟨3890888, by rfl⟩ : syracuseStep 5187851 = 7781777) B7781777
theorem B3458567 : Blo 2305435 3458567 := bstep (se 1 (by rfl) ⟨2593925, by rfl⟩ : syracuseStep 3458567 = 5187851) B5187851
theorem B2305711 : Blo 2305435 2305711 := bstep (se 1 (by rfl) ⟨1729283, by rfl⟩ : syracuseStep 2305711 = 3458567) B3458567
theorem B3458573 : Blo 2305435 3458573 := bbase (se 3 (by rfl) ⟨648482, by rfl⟩ : syracuseStep 3458573 = 1296965) (by norm_num)
theorem B2305715 : Blo 2305435 2305715 := bstep (se 1 (by rfl) ⟨1729286, by rfl⟩ : syracuseStep 2305715 = 3458573) B3458573
theorem B5187869 : Blo 2305435 5187869 := bbase (se 3 (by rfl) ⟨972725, by rfl⟩ : syracuseStep 5187869 = 1945451) (by norm_num)
theorem B3458579 : Blo 2305435 3458579 := bstep (se 1 (by rfl) ⟨2593934, by rfl⟩ : syracuseStep 3458579 = 5187869) B5187869
theorem B2305719 : Blo 2305435 2305719 := bstep (se 1 (by rfl) ⟨1729289, by rfl⟩ : syracuseStep 2305719 = 3458579) B3458579
theorem B3890909 : Blo 2305435 3890909 := bbase (se 3 (by rfl) ⟨729545, by rfl⟩ : syracuseStep 3890909 = 1459091) (by norm_num)
theorem B2593939 : Blo 2305435 2593939 := bstep (se 1 (by rfl) ⟨1945454, by rfl⟩ : syracuseStep 2593939 = 3890909) B3890909
theorem B3458585 : Blo 2305435 3458585 := bstep (se 2 (by rfl) ⟨1296969, by rfl⟩ : syracuseStep 3458585 = 2593939) B2593939
theorem B2305723 : Blo 2305435 2305723 := bstep (se 1 (by rfl) ⟨1729292, by rfl⟩ : syracuseStep 2305723 = 3458585) B3458585
theorem B7386661 : Blo 2305435 7386661 := bbase (se 4 (by rfl) ⟨692499, by rfl⟩ : syracuseStep 7386661 = 1384999) (by norm_num)
theorem B9848881 : Blo 2305435 9848881 := bstep (se 2 (by rfl) ⟨3693330, by rfl⟩ : syracuseStep 9848881 = 7386661) B7386661
theorem B13131841 : Blo 2305435 13131841 := bstep (se 2 (by rfl) ⟨4924440, by rfl⟩ : syracuseStep 13131841 = 9848881) B9848881
theorem B17509121 : Blo 2305435 17509121 := bstep (se 2 (by rfl) ⟨6565920, by rfl⟩ : syracuseStep 17509121 = 13131841) B13131841
theorem B11672747 : Blo 2305435 11672747 := bstep (se 1 (by rfl) ⟨8754560, by rfl⟩ : syracuseStep 11672747 = 17509121) B17509121
theorem B7781831 : Blo 2305435 7781831 := bstep (se 1 (by rfl) ⟨5836373, by rfl⟩ : syracuseStep 7781831 = 11672747) B11672747
theorem B5187887 : Blo 2305435 5187887 := bstep (se 1 (by rfl) ⟨3890915, by rfl⟩ : syracuseStep 5187887 = 7781831) B7781831
theorem B3458591 : Blo 2305435 3458591 := bstep (se 1 (by rfl) ⟨2593943, by rfl⟩ : syracuseStep 3458591 = 5187887) B5187887
theorem B2305727 : Blo 2305435 2305727 := bstep (se 1 (by rfl) ⟨1729295, by rfl⟩ : syracuseStep 2305727 = 3458591) B3458591
theorem B3458597 : Blo 2305435 3458597 := bbase (se 4 (by rfl) ⟨324243, by rfl⟩ : syracuseStep 3458597 = 648487) (by norm_num)
theorem B2305731 : Blo 2305435 2305731 := bstep (se 1 (by rfl) ⟨1729298, by rfl⟩ : syracuseStep 2305731 = 3458597) B3458597
theorem B2918197 : Blo 2305435 2918197 := bbase (se 5 (by rfl) ⟨136790, by rfl⟩ : syracuseStep 2918197 = 273581) (by norm_num)
theorem B3890929 : Blo 2305435 3890929 := bstep (se 2 (by rfl) ⟨1459098, by rfl⟩ : syracuseStep 3890929 = 2918197) B2918197
theorem B5187905 : Blo 2305435 5187905 := bstep (se 2 (by rfl) ⟨1945464, by rfl⟩ : syracuseStep 5187905 = 3890929) B3890929
theorem B3458603 : Blo 2305435 3458603 := bstep (se 1 (by rfl) ⟨2593952, by rfl⟩ : syracuseStep 3458603 = 5187905) B5187905
theorem B2305735 : Blo 2305435 2305735 := bstep (se 1 (by rfl) ⟨1729301, by rfl⟩ : syracuseStep 2305735 = 3458603) B3458603
theorem B2593957 : Blo 2305435 2593957 := bbase (se 4 (by rfl) ⟨243183, by rfl⟩ : syracuseStep 2593957 = 486367) (by norm_num)
theorem B3458609 : Blo 2305435 3458609 := bstep (se 2 (by rfl) ⟨1296978, by rfl⟩ : syracuseStep 3458609 = 2593957) B2593957
theorem B2305739 : Blo 2305435 2305739 := bstep (se 1 (by rfl) ⟨1729304, by rfl⟩ : syracuseStep 2305739 = 3458609) B3458609
theorem B8310053 : Blo 2305435 8310053 := bbase (se 4 (by rfl) ⟨779067, by rfl⟩ : syracuseStep 8310053 = 1558135) (by norm_num)
theorem B22160141 : Blo 2305435 22160141 := bstep (se 3 (by rfl) ⟨4155026, by rfl⟩ : syracuseStep 22160141 = 8310053) B8310053
theorem B14773427 : Blo 2305435 14773427 := bstep (se 1 (by rfl) ⟨11080070, by rfl⟩ : syracuseStep 14773427 = 22160141) B22160141
theorem B9848951 : Blo 2305435 9848951 := bstep (se 1 (by rfl) ⟨7386713, by rfl⟩ : syracuseStep 9848951 = 14773427) B14773427
theorem B6565967 : Blo 2305435 6565967 := bstep (se 1 (by rfl) ⟨4924475, by rfl⟩ : syracuseStep 6565967 = 9848951) B9848951
theorem B4377311 : Blo 2305435 4377311 := bstep (se 1 (by rfl) ⟨3282983, by rfl⟩ : syracuseStep 4377311 = 6565967) B6565967
theorem B2918207 : Blo 2305435 2918207 := bstep (se 1 (by rfl) ⟨2188655, by rfl⟩ : syracuseStep 2918207 = 4377311) B4377311
theorem B7781885 : Blo 2305435 7781885 := bstep (se 3 (by rfl) ⟨1459103, by rfl⟩ : syracuseStep 7781885 = 2918207) B2918207
theorem B5187923 : Blo 2305435 5187923 := bstep (se 1 (by rfl) ⟨3890942, by rfl⟩ : syracuseStep 5187923 = 7781885) B7781885
theorem B3458615 : Blo 2305435 3458615 := bstep (se 1 (by rfl) ⟨2593961, by rfl⟩ : syracuseStep 3458615 = 5187923) B5187923
theorem B2305743 : Blo 2305435 2305743 := bstep (se 1 (by rfl) ⟨1729307, by rfl⟩ : syracuseStep 2305743 = 3458615) B3458615
theorem B3458621 : Blo 2305435 3458621 := bbase (se 3 (by rfl) ⟨648491, by rfl⟩ : syracuseStep 3458621 = 1296983) (by norm_num)
theorem B2305747 : Blo 2305435 2305747 := bstep (se 1 (by rfl) ⟨1729310, by rfl⟩ : syracuseStep 2305747 = 3458621) B3458621
theorem B5187941 : Blo 2305435 5187941 := bbase (se 4 (by rfl) ⟨486369, by rfl⟩ : syracuseStep 5187941 = 972739) (by norm_num)
theorem B3458627 : Blo 2305435 3458627 := bstep (se 1 (by rfl) ⟨2593970, by rfl⟩ : syracuseStep 3458627 = 5187941) B5187941
theorem B2305751 : Blo 2305435 2305751 := bstep (se 1 (by rfl) ⟨1729313, by rfl⟩ : syracuseStep 2305751 = 3458627) B3458627
theorem B5836445 : Blo 2305435 5836445 := bbase (se 3 (by rfl) ⟨1094333, by rfl⟩ : syracuseStep 5836445 = 2188667) (by norm_num)
theorem B3890963 : Blo 2305435 3890963 := bstep (se 1 (by rfl) ⟨2918222, by rfl⟩ : syracuseStep 3890963 = 5836445) B5836445
theorem B2593975 : Blo 2305435 2593975 := bstep (se 1 (by rfl) ⟨1945481, by rfl⟩ : syracuseStep 2593975 = 3890963) B3890963
theorem B3458633 : Blo 2305435 3458633 := bstep (se 2 (by rfl) ⟨1296987, by rfl⟩ : syracuseStep 3458633 = 2593975) B2593975
theorem B2305755 : Blo 2305435 2305755 := bstep (se 1 (by rfl) ⟨1729316, by rfl⟩ : syracuseStep 2305755 = 3458633) B3458633
theorem B4377341 : Blo 2305435 4377341 := bbase (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) (by norm_num)
theorem B11672909 : Blo 2305435 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B7781939 : Blo 2305435 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B5187959 : Blo 2305435 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B3458639 : Blo 2305435 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B2305759 : Blo 2305435 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B3458645 : Blo 2305435 3458645 := bbase (se 8 (by rfl) ⟨20265, by rfl⟩ : syracuseStep 3458645 = 40531) (by norm_num)
theorem B2305763 : Blo 2305435 2305763 := bstep (se 1 (by rfl) ⟨1729322, by rfl⟩ : syracuseStep 2305763 = 3458645) B3458645
theorem B5540093 : Blo 2305435 5540093 := bbase (se 3 (by rfl) ⟨1038767, by rfl⟩ : syracuseStep 5540093 = 2077535) (by norm_num)
theorem B3693395 : Blo 2305435 3693395 := bstep (se 1 (by rfl) ⟨2770046, by rfl⟩ : syracuseStep 3693395 = 5540093) B5540093
theorem B9849053 : Blo 2305435 9849053 := bstep (se 3 (by rfl) ⟨1846697, by rfl⟩ : syracuseStep 9849053 = 3693395) B3693395
theorem B6566035 : Blo 2305435 6566035 := bstep (se 1 (by rfl) ⟨4924526, by rfl⟩ : syracuseStep 6566035 = 9849053) B9849053
theorem B8754713 : Blo 2305435 8754713 := bstep (se 2 (by rfl) ⟨3283017, by rfl⟩ : syracuseStep 8754713 = 6566035) B6566035
theorem B5836475 : Blo 2305435 5836475 := bstep (se 1 (by rfl) ⟨4377356, by rfl⟩ : syracuseStep 5836475 = 8754713) B8754713
theorem B3890983 : Blo 2305435 3890983 := bstep (se 1 (by rfl) ⟨2918237, by rfl⟩ : syracuseStep 3890983 = 5836475) B5836475
theorem B5187977 : Blo 2305435 5187977 := bstep (se 2 (by rfl) ⟨1945491, by rfl⟩ : syracuseStep 5187977 = 3890983) B3890983
theorem B3458651 : Blo 2305435 3458651 := bstep (se 1 (by rfl) ⟨2593988, by rfl⟩ : syracuseStep 3458651 = 5187977) B5187977
theorem B2305767 : Blo 2305435 2305767 := bstep (se 1 (by rfl) ⟨1729325, by rfl⟩ : syracuseStep 2305767 = 3458651) B3458651
theorem B2593993 : Blo 2305435 2593993 := bbase (se 2 (by rfl) ⟨972747, by rfl⟩ : syracuseStep 2593993 = 1945495) (by norm_num)
theorem B3458657 : Blo 2305435 3458657 := bstep (se 2 (by rfl) ⟨1296996, by rfl⟩ : syracuseStep 3458657 = 2593993) B2593993
theorem B2305771 : Blo 2305435 2305771 := bstep (se 1 (by rfl) ⟨1729328, by rfl⟩ : syracuseStep 2305771 = 3458657) B3458657
theorem B2807849 : Blo 2305435 2807849 := bbase (se 2 (by rfl) ⟨1052943, by rfl⟩ : syracuseStep 2807849 = 2105887) (by norm_num)
theorem B7487597 : Blo 2305435 7487597 := bstep (se 3 (by rfl) ⟨1403924, by rfl⟩ : syracuseStep 7487597 = 2807849) B2807849
theorem B19966925 : Blo 2305435 19966925 := bstep (se 3 (by rfl) ⟨3743798, by rfl⟩ : syracuseStep 19966925 = 7487597) B7487597
theorem B13311283 : Blo 2305435 13311283 := bstep (se 1 (by rfl) ⟨9983462, by rfl⟩ : syracuseStep 13311283 = 19966925) B19966925
theorem B17748377 : Blo 2305435 17748377 := bstep (se 2 (by rfl) ⟨6655641, by rfl⟩ : syracuseStep 17748377 = 13311283) B13311283
theorem B11832251 : Blo 2305435 11832251 := bstep (se 1 (by rfl) ⟨8874188, by rfl⟩ : syracuseStep 11832251 = 17748377) B17748377
theorem B31552669 : Blo 2305435 31552669 := bstep (se 3 (by rfl) ⟨5916125, by rfl⟩ : syracuseStep 31552669 = 11832251) B11832251
theorem B42070225 : Blo 2305435 42070225 := bstep (se 2 (by rfl) ⟨15776334, by rfl⟩ : syracuseStep 42070225 = 31552669) B31552669
theorem B56093633 : Blo 2305435 56093633 := bstep (se 2 (by rfl) ⟨21035112, by rfl⟩ : syracuseStep 56093633 = 42070225) B42070225
theorem B37395755 : Blo 2305435 37395755 := bstep (se 1 (by rfl) ⟨28046816, by rfl⟩ : syracuseStep 37395755 = 56093633) B56093633
theorem B24930503 : Blo 2305435 24930503 := bstep (se 1 (by rfl) ⟨18697877, by rfl⟩ : syracuseStep 24930503 = 37395755) B37395755
theorem B16620335 : Blo 2305435 16620335 := bstep (se 1 (by rfl) ⟨12465251, by rfl⟩ : syracuseStep 16620335 = 24930503) B24930503
theorem B11080223 : Blo 2305435 11080223 := bstep (se 1 (by rfl) ⟨8310167, by rfl⟩ : syracuseStep 11080223 = 16620335) B16620335
theorem B7386815 : Blo 2305435 7386815 := bstep (se 1 (by rfl) ⟨5540111, by rfl⟩ : syracuseStep 7386815 = 11080223) B11080223
theorem B19698173 : Blo 2305435 19698173 := bstep (se 3 (by rfl) ⟨3693407, by rfl⟩ : syracuseStep 19698173 = 7386815) B7386815
theorem B13132115 : Blo 2305435 13132115 := bstep (se 1 (by rfl) ⟨9849086, by rfl⟩ : syracuseStep 13132115 = 19698173) B19698173
theorem B8754743 : Blo 2305435 8754743 := bstep (se 1 (by rfl) ⟨6566057, by rfl⟩ : syracuseStep 8754743 = 13132115) B13132115
theorem B5836495 : Blo 2305435 5836495 := bstep (se 1 (by rfl) ⟨4377371, by rfl⟩ : syracuseStep 5836495 = 8754743) B8754743
theorem B7781993 : Blo 2305435 7781993 := bstep (se 2 (by rfl) ⟨2918247, by rfl⟩ : syracuseStep 7781993 = 5836495) B5836495
theorem B5187995 : Blo 2305435 5187995 := bstep (se 1 (by rfl) ⟨3890996, by rfl⟩ : syracuseStep 5187995 = 7781993) B7781993
theorem B3458663 : Blo 2305435 3458663 := bstep (se 1 (by rfl) ⟨2593997, by rfl⟩ : syracuseStep 3458663 = 5187995) B5187995
theorem B2305775 : Blo 2305435 2305775 := bstep (se 1 (by rfl) ⟨1729331, by rfl⟩ : syracuseStep 2305775 = 3458663) B3458663
theorem B3458669 : Blo 2305435 3458669 := bbase (se 3 (by rfl) ⟨648500, by rfl⟩ : syracuseStep 3458669 = 1297001) (by norm_num)
theorem B2305779 : Blo 2305435 2305779 := bstep (se 1 (by rfl) ⟨1729334, by rfl⟩ : syracuseStep 2305779 = 3458669) B3458669
theorem B5188013 : Blo 2305435 5188013 := bbase (se 3 (by rfl) ⟨972752, by rfl⟩ : syracuseStep 5188013 = 1945505) (by norm_num)
theorem B3458675 : Blo 2305435 3458675 := bstep (se 1 (by rfl) ⟨2594006, by rfl⟩ : syracuseStep 3458675 = 5188013) B5188013
theorem B2305783 : Blo 2305435 2305783 := bstep (se 1 (by rfl) ⟨1729337, by rfl⟩ : syracuseStep 2305783 = 3458675) B3458675
theorem B2462285 : Blo 2305435 2462285 := bbase (se 3 (by rfl) ⟨461678, by rfl⟩ : syracuseStep 2462285 = 923357) (by norm_num)
theorem B6566093 : Blo 2305435 6566093 := bstep (se 3 (by rfl) ⟨1231142, by rfl⟩ : syracuseStep 6566093 = 2462285) B2462285
theorem B4377395 : Blo 2305435 4377395 := bstep (se 1 (by rfl) ⟨3283046, by rfl⟩ : syracuseStep 4377395 = 6566093) B6566093
theorem B2918263 : Blo 2305435 2918263 := bstep (se 1 (by rfl) ⟨2188697, by rfl⟩ : syracuseStep 2918263 = 4377395) B4377395
theorem B3891017 : Blo 2305435 3891017 := bstep (se 2 (by rfl) ⟨1459131, by rfl⟩ : syracuseStep 3891017 = 2918263) B2918263
theorem B2594011 : Blo 2305435 2594011 := bstep (se 1 (by rfl) ⟨1945508, by rfl⟩ : syracuseStep 2594011 = 3891017) B3891017
theorem B3458681 : Blo 2305435 3458681 := bstep (se 2 (by rfl) ⟨1297005, by rfl⟩ : syracuseStep 3458681 = 2594011) B2594011
theorem B2305787 : Blo 2305435 2305787 := bstep (se 1 (by rfl) ⟨1729340, by rfl⟩ : syracuseStep 2305787 = 3458681) B3458681
theorem B2434225 : Blo 2305435 2434225 := bbase (se 2 (by rfl) ⟨912834, by rfl⟩ : syracuseStep 2434225 = 1825669) (by norm_num)
theorem B207720533 : Blo 2305435 207720533 := bstep (se 8 (by rfl) ⟨1217112, by rfl⟩ : syracuseStep 207720533 = 2434225) B2434225
theorem B138480355 : Blo 2305435 138480355 := bstep (se 1 (by rfl) ⟨103860266, by rfl⟩ : syracuseStep 138480355 = 207720533) B207720533
theorem B184640473 : Blo 2305435 184640473 := bstep (se 2 (by rfl) ⟨69240177, by rfl⟩ : syracuseStep 184640473 = 138480355) B138480355
theorem B246187297 : Blo 2305435 246187297 := bstep (se 2 (by rfl) ⟨92320236, by rfl⟩ : syracuseStep 246187297 = 184640473) B184640473
theorem B328249729 : Blo 2305435 328249729 := bstep (se 2 (by rfl) ⟨123093648, by rfl⟩ : syracuseStep 328249729 = 246187297) B246187297
theorem B1750665221 : Blo 2305435 1750665221 := bstep (se 4 (by rfl) ⟨164124864, by rfl⟩ : syracuseStep 1750665221 = 328249729) B328249729
theorem B1167110147 : Blo 2305435 1167110147 := bstep (se 1 (by rfl) ⟨875332610, by rfl⟩ : syracuseStep 1167110147 = 1750665221) B1750665221
theorem B778073431 : Blo 2305435 778073431 := bstep (se 1 (by rfl) ⟨583555073, by rfl⟩ : syracuseStep 778073431 = 1167110147) B1167110147
theorem B1037431241 : Blo 2305435 1037431241 := bstep (se 2 (by rfl) ⟨389036715, by rfl⟩ : syracuseStep 1037431241 = 778073431) B778073431
theorem B691620827 : Blo 2305435 691620827 := bstep (se 1 (by rfl) ⟨518715620, by rfl⟩ : syracuseStep 691620827 = 1037431241) B1037431241
theorem B1844322205 : Blo 2305435 1844322205 := bstep (se 3 (by rfl) ⟨345810413, by rfl⟩ : syracuseStep 1844322205 = 691620827) B691620827
theorem B2459096273 : Blo 2305435 2459096273 := bstep (se 2 (by rfl) ⟨922161102, by rfl⟩ : syracuseStep 2459096273 = 1844322205) B1844322205
theorem B1639397515 : Blo 2305435 1639397515 := bstep (se 1 (by rfl) ⟨1229548136, by rfl⟩ : syracuseStep 1639397515 = 2459096273) B2459096273
theorem B2185863353 : Blo 2305435 2185863353 := bstep (se 2 (by rfl) ⟨819698757, by rfl⟩ : syracuseStep 2185863353 = 1639397515) B1639397515
theorem B1457242235 : Blo 2305435 1457242235 := bstep (se 1 (by rfl) ⟨1092931676, by rfl⟩ : syracuseStep 1457242235 = 2185863353) B2185863353
theorem B971494823 : Blo 2305435 971494823 := bstep (se 1 (by rfl) ⟨728621117, by rfl⟩ : syracuseStep 971494823 = 1457242235) B1457242235
theorem B647663215 : Blo 2305435 647663215 := bstep (se 1 (by rfl) ⟨485747411, by rfl⟩ : syracuseStep 647663215 = 971494823) B971494823
theorem B863550953 : Blo 2305435 863550953 := bstep (se 2 (by rfl) ⟨323831607, by rfl⟩ : syracuseStep 863550953 = 647663215) B647663215
theorem B575700635 : Blo 2305435 575700635 := bstep (se 1 (by rfl) ⟨431775476, by rfl⟩ : syracuseStep 575700635 = 863550953) B863550953
theorem B1535201693 : Blo 2305435 1535201693 := bstep (se 3 (by rfl) ⟨287850317, by rfl⟩ : syracuseStep 1535201693 = 575700635) B575700635
theorem B1023467795 : Blo 2305435 1023467795 := bstep (se 1 (by rfl) ⟨767600846, by rfl⟩ : syracuseStep 1023467795 = 1535201693) B1535201693
theorem B682311863 : Blo 2305435 682311863 := bstep (se 1 (by rfl) ⟨511733897, by rfl⟩ : syracuseStep 682311863 = 1023467795) B1023467795
theorem B454874575 : Blo 2305435 454874575 := bstep (se 1 (by rfl) ⟨341155931, by rfl⟩ : syracuseStep 454874575 = 682311863) B682311863
theorem B606499433 : Blo 2305435 606499433 := bstep (se 2 (by rfl) ⟨227437287, by rfl⟩ : syracuseStep 606499433 = 454874575) B454874575
theorem B404332955 : Blo 2305435 404332955 := bstep (se 1 (by rfl) ⟨303249716, by rfl⟩ : syracuseStep 404332955 = 606499433) B606499433
theorem B269555303 : Blo 2305435 269555303 := bstep (se 1 (by rfl) ⟨202166477, by rfl⟩ : syracuseStep 269555303 = 404332955) B404332955
theorem B179703535 : Blo 2305435 179703535 := bstep (se 1 (by rfl) ⟨134777651, by rfl⟩ : syracuseStep 179703535 = 269555303) B269555303
theorem B239604713 : Blo 2305435 239604713 := bstep (se 2 (by rfl) ⟨89851767, by rfl⟩ : syracuseStep 239604713 = 179703535) B179703535
theorem B159736475 : Blo 2305435 159736475 := bstep (se 1 (by rfl) ⟨119802356, by rfl⟩ : syracuseStep 159736475 = 239604713) B239604713
theorem B106490983 : Blo 2305435 106490983 := bstep (se 1 (by rfl) ⟨79868237, by rfl⟩ : syracuseStep 106490983 = 159736475) B159736475
theorem B141987977 : Blo 2305435 141987977 := bstep (se 2 (by rfl) ⟨53245491, by rfl⟩ : syracuseStep 141987977 = 106490983) B106490983
theorem B94658651 : Blo 2305435 94658651 := bstep (se 1 (by rfl) ⟨70993988, by rfl⟩ : syracuseStep 94658651 = 141987977) B141987977
theorem B63105767 : Blo 2305435 63105767 := bstep (se 1 (by rfl) ⟨47329325, by rfl⟩ : syracuseStep 63105767 = 94658651) B94658651
theorem B42070511 : Blo 2305435 42070511 := bstep (se 1 (by rfl) ⟨31552883, by rfl⟩ : syracuseStep 42070511 = 63105767) B63105767
theorem B28047007 : Blo 2305435 28047007 := bstep (se 1 (by rfl) ⟨21035255, by rfl⟩ : syracuseStep 28047007 = 42070511) B42070511
theorem B37396009 : Blo 2305435 37396009 := bstep (se 2 (by rfl) ⟨14023503, by rfl⟩ : syracuseStep 37396009 = 28047007) B28047007
theorem B49861345 : Blo 2305435 49861345 := bstep (se 2 (by rfl) ⟨18698004, by rfl⟩ : syracuseStep 49861345 = 37396009) B37396009
theorem B66481793 : Blo 2305435 66481793 := bstep (se 2 (by rfl) ⟨24930672, by rfl⟩ : syracuseStep 66481793 = 49861345) B49861345
theorem B44321195 : Blo 2305435 44321195 := bstep (se 1 (by rfl) ⟨33240896, by rfl⟩ : syracuseStep 44321195 = 66481793) B66481793
theorem B29547463 : Blo 2305435 29547463 := bstep (se 1 (by rfl) ⟨22160597, by rfl⟩ : syracuseStep 29547463 = 44321195) B44321195
theorem B39396617 : Blo 2305435 39396617 := bstep (se 2 (by rfl) ⟨14773731, by rfl⟩ : syracuseStep 39396617 = 29547463) B29547463
theorem B26264411 : Blo 2305435 26264411 := bstep (se 1 (by rfl) ⟨19698308, by rfl⟩ : syracuseStep 26264411 = 39396617) B39396617
theorem B17509607 : Blo 2305435 17509607 := bstep (se 1 (by rfl) ⟨13132205, by rfl⟩ : syracuseStep 17509607 = 26264411) B26264411
theorem B11673071 : Blo 2305435 11673071 := bstep (se 1 (by rfl) ⟨8754803, by rfl⟩ : syracuseStep 11673071 = 17509607) B17509607
theorem B7782047 : Blo 2305435 7782047 := bstep (se 1 (by rfl) ⟨5836535, by rfl⟩ : syracuseStep 7782047 = 11673071) B11673071
theorem B5188031 : Blo 2305435 5188031 := bstep (se 1 (by rfl) ⟨3891023, by rfl⟩ : syracuseStep 5188031 = 7782047) B7782047
theorem B3458687 : Blo 2305435 3458687 := bstep (se 1 (by rfl) ⟨2594015, by rfl⟩ : syracuseStep 3458687 = 5188031) B5188031
theorem B2305791 : Blo 2305435 2305791 := bstep (se 1 (by rfl) ⟨1729343, by rfl⟩ : syracuseStep 2305791 = 3458687) B3458687
theorem B3458693 : Blo 2305435 3458693 := bbase (se 4 (by rfl) ⟨324252, by rfl⟩ : syracuseStep 3458693 = 648505) (by norm_num)
theorem B2305795 : Blo 2305435 2305795 := bstep (se 1 (by rfl) ⟨1729346, by rfl⟩ : syracuseStep 2305795 = 3458693) B3458693
theorem B3891037 : Blo 2305435 3891037 := bbase (se 3 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 3891037 = 1459139) (by norm_num)
theorem B5188049 : Blo 2305435 5188049 := bstep (se 2 (by rfl) ⟨1945518, by rfl⟩ : syracuseStep 5188049 = 3891037) B3891037
theorem B3458699 : Blo 2305435 3458699 := bstep (se 1 (by rfl) ⟨2594024, by rfl⟩ : syracuseStep 3458699 = 5188049) B5188049
theorem B2305799 : Blo 2305435 2305799 := bstep (se 1 (by rfl) ⟨1729349, by rfl⟩ : syracuseStep 2305799 = 3458699) B3458699
theorem B2594029 : Blo 2305435 2594029 := bbase (se 3 (by rfl) ⟨486380, by rfl⟩ : syracuseStep 2594029 = 972761) (by norm_num)
theorem B3458705 : Blo 2305435 3458705 := bstep (se 2 (by rfl) ⟨1297014, by rfl⟩ : syracuseStep 3458705 = 2594029) B2594029
theorem B2305803 : Blo 2305435 2305803 := bstep (se 1 (by rfl) ⟨1729352, by rfl⟩ : syracuseStep 2305803 = 3458705) B3458705
theorem B7782101 : Blo 2305435 7782101 := bbase (se 7 (by rfl) ⟨91196, by rfl⟩ : syracuseStep 7782101 = 182393) (by norm_num)
theorem B5188067 : Blo 2305435 5188067 := bstep (se 1 (by rfl) ⟨3891050, by rfl⟩ : syracuseStep 5188067 = 7782101) B7782101
theorem B3458711 : Blo 2305435 3458711 := bstep (se 1 (by rfl) ⟨2594033, by rfl⟩ : syracuseStep 3458711 = 5188067) B5188067
theorem B2305807 : Blo 2305435 2305807 := bstep (se 1 (by rfl) ⟨1729355, by rfl⟩ : syracuseStep 2305807 = 3458711) B3458711
theorem B3458717 : Blo 2305435 3458717 := bbase (se 3 (by rfl) ⟨648509, by rfl⟩ : syracuseStep 3458717 = 1297019) (by norm_num)
theorem B2305811 : Blo 2305435 2305811 := bstep (se 1 (by rfl) ⟨1729358, by rfl⟩ : syracuseStep 2305811 = 3458717) B3458717
theorem B5188085 : Blo 2305435 5188085 := bbase (se 5 (by rfl) ⟨243191, by rfl⟩ : syracuseStep 5188085 = 486383) (by norm_num)
theorem B3458723 : Blo 2305435 3458723 := bstep (se 1 (by rfl) ⟨2594042, by rfl⟩ : syracuseStep 3458723 = 5188085) B5188085
theorem B2305815 : Blo 2305435 2305815 := bstep (se 1 (by rfl) ⟨1729361, by rfl⟩ : syracuseStep 2305815 = 3458723) B3458723
theorem B147881045 : Blo 2305435 147881045 := bbase (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) (by norm_num)
theorem B98587363 : Blo 2305435 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B131449817 : Blo 2305435 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B87633211 : Blo 2305435 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B116844281 : Blo 2305435 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B77896187 : Blo 2305435 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B51930791 : Blo 2305435 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B34620527 : Blo 2305435 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B23080351 : Blo 2305435 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B30773801 : Blo 2305435 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B82063469 : Blo 2305435 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B54708979 : Blo 2305435 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B72945305 : Blo 2305435 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B48630203 : Blo 2305435 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B32420135 : Blo 2305435 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B21613423 : Blo 2305435 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B28817897 : Blo 2305435 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B76847725 : Blo 2305435 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B102463633 : Blo 2305435 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B136618177 : Blo 2305435 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B182157569 : Blo 2305435 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B121438379 : Blo 2305435 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B80958919 : Blo 2305435 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B107945225 : Blo 2305435 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B71963483 : Blo 2305435 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B191902621 : Blo 2305435 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B255870161 : Blo 2305435 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B170580107 : Blo 2305435 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B113720071 : Blo 2305435 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B151626761 : Blo 2305435 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B101084507 : Blo 2305435 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B67389671 : Blo 2305435 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B179705789 : Blo 2305435 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B119803859 : Blo 2305435 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B79869239 : Blo 2305435 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B53246159 : Blo 2305435 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B35497439 : Blo 2305435 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B23664959 : Blo 2305435 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B15776639 : Blo 2305435 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B10517759 : Blo 2305435 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B7011839 : Blo 2305435 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B4674559 : Blo 2305435 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B6232745 : Blo 2305435 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B16620653 : Blo 2305435 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B44321741 : Blo 2305435 44321741 := bstep (se 3 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 44321741 = 16620653) B16620653
theorem B29547827 : Blo 2305435 29547827 := bstep (se 1 (by rfl) ⟨22160870, by rfl⟩ : syracuseStep 29547827 = 44321741) B44321741
theorem B19698551 : Blo 2305435 19698551 := bstep (se 1 (by rfl) ⟨14773913, by rfl⟩ : syracuseStep 19698551 = 29547827) B29547827
theorem B13132367 : Blo 2305435 13132367 := bstep (se 1 (by rfl) ⟨9849275, by rfl⟩ : syracuseStep 13132367 = 19698551) B19698551
theorem B8754911 : Blo 2305435 8754911 := bstep (se 1 (by rfl) ⟨6566183, by rfl⟩ : syracuseStep 8754911 = 13132367) B13132367
theorem B5836607 : Blo 2305435 5836607 := bstep (se 1 (by rfl) ⟨4377455, by rfl⟩ : syracuseStep 5836607 = 8754911) B8754911
theorem B3891071 : Blo 2305435 3891071 := bstep (se 1 (by rfl) ⟨2918303, by rfl⟩ : syracuseStep 3891071 = 5836607) B5836607
theorem B2594047 : Blo 2305435 2594047 := bstep (se 1 (by rfl) ⟨1945535, by rfl⟩ : syracuseStep 2594047 = 3891071) B3891071
theorem B3458729 : Blo 2305435 3458729 := bstep (se 2 (by rfl) ⟨1297023, by rfl⟩ : syracuseStep 3458729 = 2594047) B2594047
theorem B2305819 : Blo 2305435 2305819 := bstep (se 1 (by rfl) ⟨1729364, by rfl⟩ : syracuseStep 2305819 = 3458729) B3458729
theorem B3693485 : Blo 2305435 3693485 := bbase (se 3 (by rfl) ⟨692528, by rfl⟩ : syracuseStep 3693485 = 1385057) (by norm_num)
theorem B2462323 : Blo 2305435 2462323 := bstep (se 1 (by rfl) ⟨1846742, by rfl⟩ : syracuseStep 2462323 = 3693485) B3693485
theorem B3283097 : Blo 2305435 3283097 := bstep (se 2 (by rfl) ⟨1231161, by rfl⟩ : syracuseStep 3283097 = 2462323) B2462323
theorem B8754925 : Blo 2305435 8754925 := bstep (se 3 (by rfl) ⟨1641548, by rfl⟩ : syracuseStep 8754925 = 3283097) B3283097
theorem B11673233 : Blo 2305435 11673233 := bstep (se 2 (by rfl) ⟨4377462, by rfl⟩ : syracuseStep 11673233 = 8754925) B8754925
theorem B7782155 : Blo 2305435 7782155 := bstep (se 1 (by rfl) ⟨5836616, by rfl⟩ : syracuseStep 7782155 = 11673233) B11673233
theorem B5188103 : Blo 2305435 5188103 := bstep (se 1 (by rfl) ⟨3891077, by rfl⟩ : syracuseStep 5188103 = 7782155) B7782155
theorem B3458735 : Blo 2305435 3458735 := bstep (se 1 (by rfl) ⟨2594051, by rfl⟩ : syracuseStep 3458735 = 5188103) B5188103
theorem B2305823 : Blo 2305435 2305823 := bstep (se 1 (by rfl) ⟨1729367, by rfl⟩ : syracuseStep 2305823 = 3458735) B3458735
theorem B3458741 : Blo 2305435 3458741 := bbase (se 5 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 3458741 = 324257) (by norm_num)
theorem B2305827 : Blo 2305435 2305827 := bstep (se 1 (by rfl) ⟨1729370, by rfl⟩ : syracuseStep 2305827 = 3458741) B3458741
theorem B5836637 : Blo 2305435 5836637 := bbase (se 3 (by rfl) ⟨1094369, by rfl⟩ : syracuseStep 5836637 = 2188739) (by norm_num)
theorem B3891091 : Blo 2305435 3891091 := bstep (se 1 (by rfl) ⟨2918318, by rfl⟩ : syracuseStep 3891091 = 5836637) B5836637
theorem B5188121 : Blo 2305435 5188121 := bstep (se 2 (by rfl) ⟨1945545, by rfl⟩ : syracuseStep 5188121 = 3891091) B3891091
theorem B3458747 : Blo 2305435 3458747 := bstep (se 1 (by rfl) ⟨2594060, by rfl⟩ : syracuseStep 3458747 = 5188121) B5188121
theorem B2305831 : Blo 2305435 2305831 := bstep (se 1 (by rfl) ⟨1729373, by rfl⟩ : syracuseStep 2305831 = 3458747) B3458747
theorem B2594065 : Blo 2305435 2594065 := bbase (se 2 (by rfl) ⟨972774, by rfl⟩ : syracuseStep 2594065 = 1945549) (by norm_num)
theorem B3458753 : Blo 2305435 3458753 := bstep (se 2 (by rfl) ⟨1297032, by rfl⟩ : syracuseStep 3458753 = 2594065) B2594065
theorem B2305835 : Blo 2305435 2305835 := bstep (se 1 (by rfl) ⟨1729376, by rfl⟩ : syracuseStep 2305835 = 3458753) B3458753
theorem B4377493 : Blo 2305435 4377493 := bbase (se 6 (by rfl) ⟨102597, by rfl⟩ : syracuseStep 4377493 = 205195) (by norm_num)
theorem B5836657 : Blo 2305435 5836657 := bstep (se 2 (by rfl) ⟨2188746, by rfl⟩ : syracuseStep 5836657 = 4377493) B4377493
theorem B7782209 : Blo 2305435 7782209 := bstep (se 2 (by rfl) ⟨2918328, by rfl⟩ : syracuseStep 7782209 = 5836657) B5836657
theorem B5188139 : Blo 2305435 5188139 := bstep (se 1 (by rfl) ⟨3891104, by rfl⟩ : syracuseStep 5188139 = 7782209) B7782209
theorem B3458759 : Blo 2305435 3458759 := bstep (se 1 (by rfl) ⟨2594069, by rfl⟩ : syracuseStep 3458759 = 5188139) B5188139
theorem B2305839 : Blo 2305435 2305839 := bstep (se 1 (by rfl) ⟨1729379, by rfl⟩ : syracuseStep 2305839 = 3458759) B3458759
theorem B3458765 : Blo 2305435 3458765 := bbase (se 3 (by rfl) ⟨648518, by rfl⟩ : syracuseStep 3458765 = 1297037) (by norm_num)
theorem B2305843 : Blo 2305435 2305843 := bstep (se 1 (by rfl) ⟨1729382, by rfl⟩ : syracuseStep 2305843 = 3458765) B3458765
theorem B5188157 : Blo 2305435 5188157 := bbase (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) (by norm_num)
theorem B3458771 : Blo 2305435 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B2305847 : Blo 2305435 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B3891125 : Blo 2305435 3891125 := bbase (se 5 (by rfl) ⟨182396, by rfl⟩ : syracuseStep 3891125 = 364793) (by norm_num)
theorem B2594083 : Blo 2305435 2594083 := bstep (se 1 (by rfl) ⟨1945562, by rfl⟩ : syracuseStep 2594083 = 3891125) B3891125
theorem B3458777 : Blo 2305435 3458777 := bstep (se 2 (by rfl) ⟨1297041, by rfl⟩ : syracuseStep 3458777 = 2594083) B2594083
theorem B2305851 : Blo 2305435 2305851 := bstep (se 1 (by rfl) ⟨1729388, by rfl⟩ : syracuseStep 2305851 = 3458777) B3458777
theorem B2462357 : Blo 2305435 2462357 := bbase (se 6 (by rfl) ⟨57711, by rfl⟩ : syracuseStep 2462357 = 115423) (by norm_num)
theorem B6566285 : Blo 2305435 6566285 := bstep (se 3 (by rfl) ⟨1231178, by rfl⟩ : syracuseStep 6566285 = 2462357) B2462357
theorem B17510093 : Blo 2305435 17510093 := bstep (se 3 (by rfl) ⟨3283142, by rfl⟩ : syracuseStep 17510093 = 6566285) B6566285
theorem B11673395 : Blo 2305435 11673395 := bstep (se 1 (by rfl) ⟨8755046, by rfl⟩ : syracuseStep 11673395 = 17510093) B17510093
theorem B7782263 : Blo 2305435 7782263 := bstep (se 1 (by rfl) ⟨5836697, by rfl⟩ : syracuseStep 7782263 = 11673395) B11673395
theorem B5188175 : Blo 2305435 5188175 := bstep (se 1 (by rfl) ⟨3891131, by rfl⟩ : syracuseStep 5188175 = 7782263) B7782263
theorem B3458783 : Blo 2305435 3458783 := bstep (se 1 (by rfl) ⟨2594087, by rfl⟩ : syracuseStep 3458783 = 5188175) B5188175
theorem B2305855 : Blo 2305435 2305855 := bstep (se 1 (by rfl) ⟨1729391, by rfl⟩ : syracuseStep 2305855 = 3458783) B3458783
theorem B3458789 : Blo 2305435 3458789 := bbase (se 4 (by rfl) ⟨324261, by rfl⟩ : syracuseStep 3458789 = 648523) (by norm_num)
theorem B2305859 : Blo 2305435 2305859 := bstep (se 1 (by rfl) ⟨1729394, by rfl⟩ : syracuseStep 2305859 = 3458789) B3458789
theorem B6566309 : Blo 2305435 6566309 := bbase (se 4 (by rfl) ⟨615591, by rfl⟩ : syracuseStep 6566309 = 1231183) (by norm_num)
theorem B4377539 : Blo 2305435 4377539 := bstep (se 1 (by rfl) ⟨3283154, by rfl⟩ : syracuseStep 4377539 = 6566309) B6566309
theorem B2918359 : Blo 2305435 2918359 := bstep (se 1 (by rfl) ⟨2188769, by rfl⟩ : syracuseStep 2918359 = 4377539) B4377539
theorem B3891145 : Blo 2305435 3891145 := bstep (se 2 (by rfl) ⟨1459179, by rfl⟩ : syracuseStep 3891145 = 2918359) B2918359
theorem B5188193 : Blo 2305435 5188193 := bstep (se 2 (by rfl) ⟨1945572, by rfl⟩ : syracuseStep 5188193 = 3891145) B3891145
theorem B3458795 : Blo 2305435 3458795 := bstep (se 1 (by rfl) ⟨2594096, by rfl⟩ : syracuseStep 3458795 = 5188193) B5188193
theorem B2305863 : Blo 2305435 2305863 := bstep (se 1 (by rfl) ⟨1729397, by rfl⟩ : syracuseStep 2305863 = 3458795) B3458795
theorem B2594101 : Blo 2305435 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B3458801 : Blo 2305435 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B2305867 : Blo 2305435 2305867 := bstep (se 1 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 2305867 = 3458801) B3458801
theorem B2918369 : Blo 2305435 2918369 := bbase (se 2 (by rfl) ⟨1094388, by rfl⟩ : syracuseStep 2918369 = 2188777) (by norm_num)
theorem B7782317 : Blo 2305435 7782317 := bstep (se 3 (by rfl) ⟨1459184, by rfl⟩ : syracuseStep 7782317 = 2918369) B2918369
theorem B5188211 : Blo 2305435 5188211 := bstep (se 1 (by rfl) ⟨3891158, by rfl⟩ : syracuseStep 5188211 = 7782317) B7782317
theorem B3458807 : Blo 2305435 3458807 := bstep (se 1 (by rfl) ⟨2594105, by rfl⟩ : syracuseStep 3458807 = 5188211) B5188211
theorem B2305871 : Blo 2305435 2305871 := bstep (se 1 (by rfl) ⟨1729403, by rfl⟩ : syracuseStep 2305871 = 3458807) B3458807
theorem B3458813 : Blo 2305435 3458813 := bbase (se 3 (by rfl) ⟨648527, by rfl⟩ : syracuseStep 3458813 = 1297055) (by norm_num)
theorem B2305875 : Blo 2305435 2305875 := bstep (se 1 (by rfl) ⟨1729406, by rfl⟩ : syracuseStep 2305875 = 3458813) B3458813
theorem B5188229 : Blo 2305435 5188229 := bbase (se 4 (by rfl) ⟨486396, by rfl⟩ : syracuseStep 5188229 = 972793) (by norm_num)
theorem B3458819 : Blo 2305435 3458819 := bstep (se 1 (by rfl) ⟨2594114, by rfl⟩ : syracuseStep 3458819 = 5188229) B5188229
theorem B2305879 : Blo 2305435 2305879 := bstep (se 1 (by rfl) ⟨1729409, by rfl⟩ : syracuseStep 2305879 = 3458819) B3458819
theorem B5997125 : Blo 2305435 5997125 := bbase (se 4 (by rfl) ⟨562230, by rfl⟩ : syracuseStep 5997125 = 1124461) (by norm_num)
theorem B15992333 : Blo 2305435 15992333 := bstep (se 3 (by rfl) ⟨2998562, by rfl⟩ : syracuseStep 15992333 = 5997125) B5997125
theorem B10661555 : Blo 2305435 10661555 := bstep (se 1 (by rfl) ⟨7996166, by rfl⟩ : syracuseStep 10661555 = 15992333) B15992333
theorem B28430813 : Blo 2305435 28430813 := bstep (se 3 (by rfl) ⟨5330777, by rfl⟩ : syracuseStep 28430813 = 10661555) B10661555
theorem B18953875 : Blo 2305435 18953875 := bstep (se 1 (by rfl) ⟨14215406, by rfl⟩ : syracuseStep 18953875 = 28430813) B28430813
theorem B25271833 : Blo 2305435 25271833 := bstep (se 2 (by rfl) ⟨9476937, by rfl⟩ : syracuseStep 25271833 = 18953875) B18953875
theorem B33695777 : Blo 2305435 33695777 := bstep (se 2 (by rfl) ⟨12635916, by rfl⟩ : syracuseStep 33695777 = 25271833) B25271833
theorem B22463851 : Blo 2305435 22463851 := bstep (se 1 (by rfl) ⟨16847888, by rfl⟩ : syracuseStep 22463851 = 33695777) B33695777
theorem B29951801 : Blo 2305435 29951801 := bstep (se 2 (by rfl) ⟨11231925, by rfl⟩ : syracuseStep 29951801 = 22463851) B22463851
theorem B19967867 : Blo 2305435 19967867 := bstep (se 1 (by rfl) ⟨14975900, by rfl⟩ : syracuseStep 19967867 = 29951801) B29951801
theorem B13311911 : Blo 2305435 13311911 := bstep (se 1 (by rfl) ⟨9983933, by rfl⟩ : syracuseStep 13311911 = 19967867) B19967867
theorem B8874607 : Blo 2305435 8874607 := bstep (se 1 (by rfl) ⟨6655955, by rfl⟩ : syracuseStep 8874607 = 13311911) B13311911
theorem B11832809 : Blo 2305435 11832809 := bstep (se 2 (by rfl) ⟨4437303, by rfl⟩ : syracuseStep 11832809 = 8874607) B8874607
theorem B31554157 : Blo 2305435 31554157 := bstep (se 3 (by rfl) ⟨5916404, by rfl⟩ : syracuseStep 31554157 = 11832809) B11832809
theorem B42072209 : Blo 2305435 42072209 := bstep (se 2 (by rfl) ⟨15777078, by rfl⟩ : syracuseStep 42072209 = 31554157) B31554157
theorem B28048139 : Blo 2305435 28048139 := bstep (se 1 (by rfl) ⟨21036104, by rfl⟩ : syracuseStep 28048139 = 42072209) B42072209
theorem B18698759 : Blo 2305435 18698759 := bstep (se 1 (by rfl) ⟨14024069, by rfl⟩ : syracuseStep 18698759 = 28048139) B28048139
theorem B12465839 : Blo 2305435 12465839 := bstep (se 1 (by rfl) ⟨9349379, by rfl⟩ : syracuseStep 12465839 = 18698759) B18698759
theorem B8310559 : Blo 2305435 8310559 := bstep (se 1 (by rfl) ⟨6232919, by rfl⟩ : syracuseStep 8310559 = 12465839) B12465839
theorem B11080745 : Blo 2305435 11080745 := bstep (se 2 (by rfl) ⟨4155279, by rfl⟩ : syracuseStep 11080745 = 8310559) B8310559
theorem B7387163 : Blo 2305435 7387163 := bstep (se 1 (by rfl) ⟨5540372, by rfl⟩ : syracuseStep 7387163 = 11080745) B11080745
theorem B4924775 : Blo 2305435 4924775 := bstep (se 1 (by rfl) ⟨3693581, by rfl⟩ : syracuseStep 4924775 = 7387163) B7387163
theorem B3283183 : Blo 2305435 3283183 := bstep (se 1 (by rfl) ⟨2462387, by rfl⟩ : syracuseStep 3283183 = 4924775) B4924775
theorem B4377577 : Blo 2305435 4377577 := bstep (se 2 (by rfl) ⟨1641591, by rfl⟩ : syracuseStep 4377577 = 3283183) B3283183
theorem B5836769 : Blo 2305435 5836769 := bstep (se 2 (by rfl) ⟨2188788, by rfl⟩ : syracuseStep 5836769 = 4377577) B4377577
theorem B3891179 : Blo 2305435 3891179 := bstep (se 1 (by rfl) ⟨2918384, by rfl⟩ : syracuseStep 3891179 = 5836769) B5836769
theorem B2594119 : Blo 2305435 2594119 := bstep (se 1 (by rfl) ⟨1945589, by rfl⟩ : syracuseStep 2594119 = 3891179) B3891179
theorem B3458825 : Blo 2305435 3458825 := bstep (se 2 (by rfl) ⟨1297059, by rfl⟩ : syracuseStep 3458825 = 2594119) B2594119
theorem B2305883 : Blo 2305435 2305883 := bstep (se 1 (by rfl) ⟨1729412, by rfl⟩ : syracuseStep 2305883 = 3458825) B3458825
theorem B11673557 : Blo 2305435 11673557 := bbase (se 7 (by rfl) ⟨136799, by rfl⟩ : syracuseStep 11673557 = 273599) (by norm_num)
theorem B7782371 : Blo 2305435 7782371 := bstep (se 1 (by rfl) ⟨5836778, by rfl⟩ : syracuseStep 7782371 = 11673557) B11673557
theorem B5188247 : Blo 2305435 5188247 := bstep (se 1 (by rfl) ⟨3891185, by rfl⟩ : syracuseStep 5188247 = 7782371) B7782371
theorem B3458831 : Blo 2305435 3458831 := bstep (se 1 (by rfl) ⟨2594123, by rfl⟩ : syracuseStep 3458831 = 5188247) B5188247
theorem B2305887 : Blo 2305435 2305887 := bstep (se 1 (by rfl) ⟨1729415, by rfl⟩ : syracuseStep 2305887 = 3458831) B3458831
theorem B3458837 : Blo 2305435 3458837 := bbase (se 6 (by rfl) ⟨81066, by rfl⟩ : syracuseStep 3458837 = 162133) (by norm_num)
theorem B2305891 : Blo 2305435 2305891 := bstep (se 1 (by rfl) ⟨1729418, by rfl⟩ : syracuseStep 2305891 = 3458837) B3458837
theorem B4437325 : Blo 2305435 4437325 := bbase (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) (by norm_num)
theorem B5916433 : Blo 2305435 5916433 := bstep (se 2 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 5916433 = 4437325) B4437325
theorem B504868949 : Blo 2305435 504868949 := bstep (se 8 (by rfl) ⟨2958216, by rfl⟩ : syracuseStep 504868949 = 5916433) B5916433
theorem B336579299 : Blo 2305435 336579299 := bstep (se 1 (by rfl) ⟨252434474, by rfl⟩ : syracuseStep 336579299 = 504868949) B504868949
theorem B224386199 : Blo 2305435 224386199 := bstep (se 1 (by rfl) ⟨168289649, by rfl⟩ : syracuseStep 224386199 = 336579299) B336579299
theorem B149590799 : Blo 2305435 149590799 := bstep (se 1 (by rfl) ⟨112193099, by rfl⟩ : syracuseStep 149590799 = 224386199) B224386199
theorem B99727199 : Blo 2305435 99727199 := bstep (se 1 (by rfl) ⟨74795399, by rfl⟩ : syracuseStep 99727199 = 149590799) B149590799
theorem B66484799 : Blo 2305435 66484799 := bstep (se 1 (by rfl) ⟨49863599, by rfl⟩ : syracuseStep 66484799 = 99727199) B99727199
theorem B44323199 : Blo 2305435 44323199 := bstep (se 1 (by rfl) ⟨33242399, by rfl⟩ : syracuseStep 44323199 = 66484799) B66484799
theorem B29548799 : Blo 2305435 29548799 := bstep (se 1 (by rfl) ⟨22161599, by rfl⟩ : syracuseStep 29548799 = 44323199) B44323199
theorem B19699199 : Blo 2305435 19699199 := bstep (se 1 (by rfl) ⟨14774399, by rfl⟩ : syracuseStep 19699199 = 29548799) B29548799
theorem B13132799 : Blo 2305435 13132799 := bstep (se 1 (by rfl) ⟨9849599, by rfl⟩ : syracuseStep 13132799 = 19699199) B19699199
theorem B8755199 : Blo 2305435 8755199 := bstep (se 1 (by rfl) ⟨6566399, by rfl⟩ : syracuseStep 8755199 = 13132799) B13132799
theorem B5836799 : Blo 2305435 5836799 := bstep (se 1 (by rfl) ⟨4377599, by rfl⟩ : syracuseStep 5836799 = 8755199) B8755199
theorem B3891199 : Blo 2305435 3891199 := bstep (se 1 (by rfl) ⟨2918399, by rfl⟩ : syracuseStep 3891199 = 5836799) B5836799
theorem B5188265 : Blo 2305435 5188265 := bstep (se 2 (by rfl) ⟨1945599, by rfl⟩ : syracuseStep 5188265 = 3891199) B3891199
theorem B3458843 : Blo 2305435 3458843 := bstep (se 1 (by rfl) ⟨2594132, by rfl⟩ : syracuseStep 3458843 = 5188265) B5188265
theorem B2305895 : Blo 2305435 2305895 := bstep (se 1 (by rfl) ⟨1729421, by rfl⟩ : syracuseStep 2305895 = 3458843) B3458843
theorem B2594137 : Blo 2305435 2594137 := bbase (se 2 (by rfl) ⟨972801, by rfl⟩ : syracuseStep 2594137 = 1945603) (by norm_num)
theorem B3458849 : Blo 2305435 3458849 := bstep (se 2 (by rfl) ⟨1297068, by rfl⟩ : syracuseStep 3458849 = 2594137) B2594137
theorem B2305899 : Blo 2305435 2305899 := bstep (se 1 (by rfl) ⟨1729424, by rfl⟩ : syracuseStep 2305899 = 3458849) B3458849
theorem B3693613 : Blo 2305435 3693613 := bbase (se 3 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 3693613 = 1385105) (by norm_num)
theorem B4924817 : Blo 2305435 4924817 := bstep (se 2 (by rfl) ⟨1846806, by rfl⟩ : syracuseStep 4924817 = 3693613) B3693613
theorem B3283211 : Blo 2305435 3283211 := bstep (se 1 (by rfl) ⟨2462408, by rfl⟩ : syracuseStep 3283211 = 4924817) B4924817
theorem B8755229 : Blo 2305435 8755229 := bstep (se 3 (by rfl) ⟨1641605, by rfl⟩ : syracuseStep 8755229 = 3283211) B3283211
theorem B5836819 : Blo 2305435 5836819 := bstep (se 1 (by rfl) ⟨4377614, by rfl⟩ : syracuseStep 5836819 = 8755229) B8755229
theorem B7782425 : Blo 2305435 7782425 := bstep (se 2 (by rfl) ⟨2918409, by rfl⟩ : syracuseStep 7782425 = 5836819) B5836819
theorem B5188283 : Blo 2305435 5188283 := bstep (se 1 (by rfl) ⟨3891212, by rfl⟩ : syracuseStep 5188283 = 7782425) B7782425
theorem B3458855 : Blo 2305435 3458855 := bstep (se 1 (by rfl) ⟨2594141, by rfl⟩ : syracuseStep 3458855 = 5188283) B5188283
theorem B2305903 : Blo 2305435 2305903 := bstep (se 1 (by rfl) ⟨1729427, by rfl⟩ : syracuseStep 2305903 = 3458855) B3458855
theorem B3458861 : Blo 2305435 3458861 := bbase (se 3 (by rfl) ⟨648536, by rfl⟩ : syracuseStep 3458861 = 1297073) (by norm_num)
theorem B2305907 : Blo 2305435 2305907 := bstep (se 1 (by rfl) ⟨1729430, by rfl⟩ : syracuseStep 2305907 = 3458861) B3458861
theorem B5188301 : Blo 2305435 5188301 := bbase (se 3 (by rfl) ⟨972806, by rfl⟩ : syracuseStep 5188301 = 1945613) (by norm_num)
theorem B3458867 : Blo 2305435 3458867 := bstep (se 1 (by rfl) ⟨2594150, by rfl⟩ : syracuseStep 3458867 = 5188301) B5188301
theorem B2305911 : Blo 2305435 2305911 := bstep (se 1 (by rfl) ⟨1729433, by rfl⟩ : syracuseStep 2305911 = 3458867) B3458867
theorem B2918425 : Blo 2305435 2918425 := bbase (se 2 (by rfl) ⟨1094409, by rfl⟩ : syracuseStep 2918425 = 2188819) (by norm_num)
theorem B3891233 : Blo 2305435 3891233 := bstep (se 2 (by rfl) ⟨1459212, by rfl⟩ : syracuseStep 3891233 = 2918425) B2918425
theorem B2594155 : Blo 2305435 2594155 := bstep (se 1 (by rfl) ⟨1945616, by rfl⟩ : syracuseStep 2594155 = 3891233) B3891233
theorem B3458873 : Blo 2305435 3458873 := bstep (se 2 (by rfl) ⟨1297077, by rfl⟩ : syracuseStep 3458873 = 2594155) B2594155
theorem B2305915 : Blo 2305435 2305915 := bstep (se 1 (by rfl) ⟨1729436, by rfl⟩ : syracuseStep 2305915 = 3458873) B3458873
theorem B9849701 : Blo 2305435 9849701 := bbase (se 4 (by rfl) ⟨923409, by rfl⟩ : syracuseStep 9849701 = 1846819) (by norm_num)
theorem B26265869 : Blo 2305435 26265869 := bstep (se 3 (by rfl) ⟨4924850, by rfl⟩ : syracuseStep 26265869 = 9849701) B9849701
theorem B17510579 : Blo 2305435 17510579 := bstep (se 1 (by rfl) ⟨13132934, by rfl⟩ : syracuseStep 17510579 = 26265869) B26265869
theorem B11673719 : Blo 2305435 11673719 := bstep (se 1 (by rfl) ⟨8755289, by rfl⟩ : syracuseStep 11673719 = 17510579) B17510579
theorem B7782479 : Blo 2305435 7782479 := bstep (se 1 (by rfl) ⟨5836859, by rfl⟩ : syracuseStep 7782479 = 11673719) B11673719
theorem B5188319 : Blo 2305435 5188319 := bstep (se 1 (by rfl) ⟨3891239, by rfl⟩ : syracuseStep 5188319 = 7782479) B7782479
theorem B3458879 : Blo 2305435 3458879 := bstep (se 1 (by rfl) ⟨2594159, by rfl⟩ : syracuseStep 3458879 = 5188319) B5188319
theorem B2305919 : Blo 2305435 2305919 := bstep (se 1 (by rfl) ⟨1729439, by rfl⟩ : syracuseStep 2305919 = 3458879) B3458879
theorem B3458885 : Blo 2305435 3458885 := bbase (se 4 (by rfl) ⟨324270, by rfl⟩ : syracuseStep 3458885 = 648541) (by norm_num)
theorem B2305923 : Blo 2305435 2305923 := bstep (se 1 (by rfl) ⟨1729442, by rfl⟩ : syracuseStep 2305923 = 3458885) B3458885
theorem B3891253 : Blo 2305435 3891253 := bbase (se 5 (by rfl) ⟨182402, by rfl⟩ : syracuseStep 3891253 = 364805) (by norm_num)
theorem B5188337 : Blo 2305435 5188337 := bstep (se 2 (by rfl) ⟨1945626, by rfl⟩ : syracuseStep 5188337 = 3891253) B3891253
theorem B3458891 : Blo 2305435 3458891 := bstep (se 1 (by rfl) ⟨2594168, by rfl⟩ : syracuseStep 3458891 = 5188337) B5188337
theorem B2305927 : Blo 2305435 2305927 := bstep (se 1 (by rfl) ⟨1729445, by rfl⟩ : syracuseStep 2305927 = 3458891) B3458891
theorem B2594173 : Blo 2305435 2594173 := bbase (se 3 (by rfl) ⟨486407, by rfl⟩ : syracuseStep 2594173 = 972815) (by norm_num)
theorem B3458897 : Blo 2305435 3458897 := bstep (se 2 (by rfl) ⟨1297086, by rfl⟩ : syracuseStep 3458897 = 2594173) B2594173
theorem B2305931 : Blo 2305435 2305931 := bstep (se 1 (by rfl) ⟨1729448, by rfl⟩ : syracuseStep 2305931 = 3458897) B3458897
theorem B7782533 : Blo 2305435 7782533 := bbase (se 4 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 7782533 = 1459225) (by norm_num)
theorem B5188355 : Blo 2305435 5188355 := bstep (se 1 (by rfl) ⟨3891266, by rfl⟩ : syracuseStep 5188355 = 7782533) B7782533
theorem B3458903 : Blo 2305435 3458903 := bstep (se 1 (by rfl) ⟨2594177, by rfl⟩ : syracuseStep 3458903 = 5188355) B5188355
theorem B2305935 : Blo 2305435 2305935 := bstep (se 1 (by rfl) ⟨1729451, by rfl⟩ : syracuseStep 2305935 = 3458903) B3458903
theorem B3458909 : Blo 2305435 3458909 := bbase (se 3 (by rfl) ⟨648545, by rfl⟩ : syracuseStep 3458909 = 1297091) (by norm_num)
theorem B2305939 : Blo 2305435 2305939 := bstep (se 1 (by rfl) ⟨1729454, by rfl⟩ : syracuseStep 2305939 = 3458909) B3458909
theorem B5188373 : Blo 2305435 5188373 := bbase (se 6 (by rfl) ⟨121602, by rfl⟩ : syracuseStep 5188373 = 243205) (by norm_num)
theorem B3458915 : Blo 2305435 3458915 := bstep (se 1 (by rfl) ⟨2594186, by rfl⟩ : syracuseStep 3458915 = 5188373) B5188373
theorem B2305943 : Blo 2305435 2305943 := bstep (se 1 (by rfl) ⟨1729457, by rfl⟩ : syracuseStep 2305943 = 3458915) B3458915
theorem B8755397 : Blo 2305435 8755397 := bbase (se 4 (by rfl) ⟨820818, by rfl⟩ : syracuseStep 8755397 = 1641637) (by norm_num)
theorem B5836931 : Blo 2305435 5836931 := bstep (se 1 (by rfl) ⟨4377698, by rfl⟩ : syracuseStep 5836931 = 8755397) B8755397
theorem B3891287 : Blo 2305435 3891287 := bstep (se 1 (by rfl) ⟨2918465, by rfl⟩ : syracuseStep 3891287 = 5836931) B5836931
theorem B2594191 : Blo 2305435 2594191 := bstep (se 1 (by rfl) ⟨1945643, by rfl⟩ : syracuseStep 2594191 = 3891287) B3891287
theorem B3458921 : Blo 2305435 3458921 := bstep (se 2 (by rfl) ⟨1297095, by rfl⟩ : syracuseStep 3458921 = 2594191) B2594191
theorem B2305947 : Blo 2305435 2305947 := bstep (se 1 (by rfl) ⟨1729460, by rfl⟩ : syracuseStep 2305947 = 3458921) B3458921
theorem B5259181 : Blo 2305435 5259181 := bbase (se 3 (by rfl) ⟨986096, by rfl⟩ : syracuseStep 5259181 = 1972193) (by norm_num)
theorem B7012241 : Blo 2305435 7012241 := bstep (se 2 (by rfl) ⟨2629590, by rfl⟩ : syracuseStep 7012241 = 5259181) B5259181
theorem B4674827 : Blo 2305435 4674827 := bstep (se 1 (by rfl) ⟨3506120, by rfl⟩ : syracuseStep 4674827 = 7012241) B7012241
theorem B3116551 : Blo 2305435 3116551 := bstep (se 1 (by rfl) ⟨2337413, by rfl⟩ : syracuseStep 3116551 = 4674827) B4674827
theorem B4155401 : Blo 2305435 4155401 := bstep (se 2 (by rfl) ⟨1558275, by rfl⟩ : syracuseStep 4155401 = 3116551) B3116551
theorem B11081069 : Blo 2305435 11081069 := bstep (se 3 (by rfl) ⟨2077700, by rfl⟩ : syracuseStep 11081069 = 4155401) B4155401
theorem B7387379 : Blo 2305435 7387379 := bstep (se 1 (by rfl) ⟨5540534, by rfl⟩ : syracuseStep 7387379 = 11081069) B11081069
theorem B4924919 : Blo 2305435 4924919 := bstep (se 1 (by rfl) ⟨3693689, by rfl⟩ : syracuseStep 4924919 = 7387379) B7387379
theorem B13133117 : Blo 2305435 13133117 := bstep (se 3 (by rfl) ⟨2462459, by rfl⟩ : syracuseStep 13133117 = 4924919) B4924919
theorem B8755411 : Blo 2305435 8755411 := bstep (se 1 (by rfl) ⟨6566558, by rfl⟩ : syracuseStep 8755411 = 13133117) B13133117
theorem B11673881 : Blo 2305435 11673881 := bstep (se 2 (by rfl) ⟨4377705, by rfl⟩ : syracuseStep 11673881 = 8755411) B8755411
theorem B7782587 : Blo 2305435 7782587 := bstep (se 1 (by rfl) ⟨5836940, by rfl⟩ : syracuseStep 7782587 = 11673881) B11673881
theorem B5188391 : Blo 2305435 5188391 := bstep (se 1 (by rfl) ⟨3891293, by rfl⟩ : syracuseStep 5188391 = 7782587) B7782587
theorem B3458927 : Blo 2305435 3458927 := bstep (se 1 (by rfl) ⟨2594195, by rfl⟩ : syracuseStep 3458927 = 5188391) B5188391
theorem B2305951 : Blo 2305435 2305951 := bstep (se 1 (by rfl) ⟨1729463, by rfl⟩ : syracuseStep 2305951 = 3458927) B3458927
theorem B3458933 : Blo 2305435 3458933 := bbase (se 5 (by rfl) ⟨162137, by rfl⟩ : syracuseStep 3458933 = 324275) (by norm_num)
theorem B2305955 : Blo 2305435 2305955 := bstep (se 1 (by rfl) ⟨1729466, by rfl⟩ : syracuseStep 2305955 = 3458933) B3458933
theorem B6233125 : Blo 2305435 6233125 := bbase (se 4 (by rfl) ⟨584355, by rfl⟩ : syracuseStep 6233125 = 1168711) (by norm_num)
theorem B8310833 : Blo 2305435 8310833 := bstep (se 2 (by rfl) ⟨3116562, by rfl⟩ : syracuseStep 8310833 = 6233125) B6233125
theorem B5540555 : Blo 2305435 5540555 := bstep (se 1 (by rfl) ⟨4155416, by rfl⟩ : syracuseStep 5540555 = 8310833) B8310833
theorem B3693703 : Blo 2305435 3693703 := bstep (se 1 (by rfl) ⟨2770277, by rfl⟩ : syracuseStep 3693703 = 5540555) B5540555
theorem B4924937 : Blo 2305435 4924937 := bstep (se 2 (by rfl) ⟨1846851, by rfl⟩ : syracuseStep 4924937 = 3693703) B3693703
theorem B3283291 : Blo 2305435 3283291 := bstep (se 1 (by rfl) ⟨2462468, by rfl⟩ : syracuseStep 3283291 = 4924937) B4924937
theorem B4377721 : Blo 2305435 4377721 := bstep (se 2 (by rfl) ⟨1641645, by rfl⟩ : syracuseStep 4377721 = 3283291) B3283291
theorem B5836961 : Blo 2305435 5836961 := bstep (se 2 (by rfl) ⟨2188860, by rfl⟩ : syracuseStep 5836961 = 4377721) B4377721
theorem B3891307 : Blo 2305435 3891307 := bstep (se 1 (by rfl) ⟨2918480, by rfl⟩ : syracuseStep 3891307 = 5836961) B5836961
theorem B5188409 : Blo 2305435 5188409 := bstep (se 2 (by rfl) ⟨1945653, by rfl⟩ : syracuseStep 5188409 = 3891307) B3891307
theorem B3458939 : Blo 2305435 3458939 := bstep (se 1 (by rfl) ⟨2594204, by rfl⟩ : syracuseStep 3458939 = 5188409) B5188409
theorem B2305959 : Blo 2305435 2305959 := bstep (se 1 (by rfl) ⟨1729469, by rfl⟩ : syracuseStep 2305959 = 3458939) B3458939
theorem B2594209 : Blo 2305435 2594209 := bbase (se 2 (by rfl) ⟨972828, by rfl⟩ : syracuseStep 2594209 = 1945657) (by norm_num)
theorem B3458945 : Blo 2305435 3458945 := bstep (se 2 (by rfl) ⟨1297104, by rfl⟩ : syracuseStep 3458945 = 2594209) B2594209
theorem B2305963 : Blo 2305435 2305963 := bstep (se 1 (by rfl) ⟨1729472, by rfl⟩ : syracuseStep 2305963 = 3458945) B3458945
theorem B5836981 : Blo 2305435 5836981 := bbase (se 5 (by rfl) ⟨273608, by rfl⟩ : syracuseStep 5836981 = 547217) (by norm_num)
theorem B7782641 : Blo 2305435 7782641 := bstep (se 2 (by rfl) ⟨2918490, by rfl⟩ : syracuseStep 7782641 = 5836981) B5836981
theorem B5188427 : Blo 2305435 5188427 := bstep (se 1 (by rfl) ⟨3891320, by rfl⟩ : syracuseStep 5188427 = 7782641) B7782641
theorem B3458951 : Blo 2305435 3458951 := bstep (se 1 (by rfl) ⟨2594213, by rfl⟩ : syracuseStep 3458951 = 5188427) B5188427
theorem B2305967 : Blo 2305435 2305967 := bstep (se 1 (by rfl) ⟨1729475, by rfl⟩ : syracuseStep 2305967 = 3458951) B3458951
theorem B3458957 : Blo 2305435 3458957 := bbase (se 3 (by rfl) ⟨648554, by rfl⟩ : syracuseStep 3458957 = 1297109) (by norm_num)
theorem B2305971 : Blo 2305435 2305971 := bstep (se 1 (by rfl) ⟨1729478, by rfl⟩ : syracuseStep 2305971 = 3458957) B3458957
theorem B5188445 : Blo 2305435 5188445 := bbase (se 3 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 5188445 = 1945667) (by norm_num)
theorem B3458963 : Blo 2305435 3458963 := bstep (se 1 (by rfl) ⟨2594222, by rfl⟩ : syracuseStep 3458963 = 5188445) B5188445
theorem B2305975 : Blo 2305435 2305975 := bstep (se 1 (by rfl) ⟨1729481, by rfl⟩ : syracuseStep 2305975 = 3458963) B3458963
theorem B3891341 : Blo 2305435 3891341 := bbase (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) (by norm_num)
theorem B2594227 : Blo 2305435 2594227 := bstep (se 1 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 2594227 = 3891341) B3891341
theorem B3458969 : Blo 2305435 3458969 := bstep (se 2 (by rfl) ⟨1297113, by rfl⟩ : syracuseStep 3458969 = 2594227) B2594227
theorem B2305979 : Blo 2305435 2305979 := bstep (se 1 (by rfl) ⟨1729484, by rfl⟩ : syracuseStep 2305979 = 3458969) B3458969
theorem B8310917 : Blo 2305435 8310917 := bbase (se 4 (by rfl) ⟨779148, by rfl⟩ : syracuseStep 8310917 = 1558297) (by norm_num)
theorem B5540611 : Blo 2305435 5540611 := bstep (se 1 (by rfl) ⟨4155458, by rfl⟩ : syracuseStep 5540611 = 8310917) B8310917
theorem B7387481 : Blo 2305435 7387481 := bstep (se 2 (by rfl) ⟨2770305, by rfl⟩ : syracuseStep 7387481 = 5540611) B5540611
theorem B19699949 : Blo 2305435 19699949 := bstep (se 3 (by rfl) ⟨3693740, by rfl⟩ : syracuseStep 19699949 = 7387481) B7387481
theorem B13133299 : Blo 2305435 13133299 := bstep (se 1 (by rfl) ⟨9849974, by rfl⟩ : syracuseStep 13133299 = 19699949) B19699949
theorem B17511065 : Blo 2305435 17511065 := bstep (se 2 (by rfl) ⟨6566649, by rfl⟩ : syracuseStep 17511065 = 13133299) B13133299
theorem B11674043 : Blo 2305435 11674043 := bstep (se 1 (by rfl) ⟨8755532, by rfl⟩ : syracuseStep 11674043 = 17511065) B17511065
theorem B7782695 : Blo 2305435 7782695 := bstep (se 1 (by rfl) ⟨5837021, by rfl⟩ : syracuseStep 7782695 = 11674043) B11674043
theorem B5188463 : Blo 2305435 5188463 := bstep (se 1 (by rfl) ⟨3891347, by rfl⟩ : syracuseStep 5188463 = 7782695) B7782695
theorem B3458975 : Blo 2305435 3458975 := bstep (se 1 (by rfl) ⟨2594231, by rfl⟩ : syracuseStep 3458975 = 5188463) B5188463
theorem B2305983 : Blo 2305435 2305983 := bstep (se 1 (by rfl) ⟨1729487, by rfl⟩ : syracuseStep 2305983 = 3458975) B3458975
theorem B3458981 : Blo 2305435 3458981 := bbase (se 4 (by rfl) ⟨324279, by rfl⟩ : syracuseStep 3458981 = 648559) (by norm_num)
theorem B2305987 : Blo 2305435 2305987 := bstep (se 1 (by rfl) ⟨1729490, by rfl⟩ : syracuseStep 2305987 = 3458981) B3458981
theorem B2918521 : Blo 2305435 2918521 := bbase (se 2 (by rfl) ⟨1094445, by rfl⟩ : syracuseStep 2918521 = 2188891) (by norm_num)
theorem B3891361 : Blo 2305435 3891361 := bstep (se 2 (by rfl) ⟨1459260, by rfl⟩ : syracuseStep 3891361 = 2918521) B2918521
theorem B5188481 : Blo 2305435 5188481 := bstep (se 2 (by rfl) ⟨1945680, by rfl⟩ : syracuseStep 5188481 = 3891361) B3891361
theorem B3458987 : Blo 2305435 3458987 := bstep (se 1 (by rfl) ⟨2594240, by rfl⟩ : syracuseStep 3458987 = 5188481) B5188481
theorem B2305991 : Blo 2305435 2305991 := bstep (se 1 (by rfl) ⟨1729493, by rfl⟩ : syracuseStep 2305991 = 3458987) B3458987
theorem B2594245 : Blo 2305435 2594245 := bbase (se 4 (by rfl) ⟨243210, by rfl⟩ : syracuseStep 2594245 = 486421) (by norm_num)
theorem B3458993 : Blo 2305435 3458993 := bstep (se 2 (by rfl) ⟨1297122, by rfl⟩ : syracuseStep 3458993 = 2594245) B2594245
theorem B2305995 : Blo 2305435 2305995 := bstep (se 1 (by rfl) ⟨1729496, by rfl⟩ : syracuseStep 2305995 = 3458993) B3458993
theorem B4377797 : Blo 2305435 4377797 := bbase (se 4 (by rfl) ⟨410418, by rfl⟩ : syracuseStep 4377797 = 820837) (by norm_num)
theorem B2918531 : Blo 2305435 2918531 := bstep (se 1 (by rfl) ⟨2188898, by rfl⟩ : syracuseStep 2918531 = 4377797) B4377797
theorem B7782749 : Blo 2305435 7782749 := bstep (se 3 (by rfl) ⟨1459265, by rfl⟩ : syracuseStep 7782749 = 2918531) B2918531
theorem B5188499 : Blo 2305435 5188499 := bstep (se 1 (by rfl) ⟨3891374, by rfl⟩ : syracuseStep 5188499 = 7782749) B7782749
theorem B3458999 : Blo 2305435 3458999 := bstep (se 1 (by rfl) ⟨2594249, by rfl⟩ : syracuseStep 3458999 = 5188499) B5188499
theorem B2305999 : Blo 2305435 2305999 := bstep (se 1 (by rfl) ⟨1729499, by rfl⟩ : syracuseStep 2305999 = 3458999) B3458999
theorem B3459005 : Blo 2305435 3459005 := bbase (se 3 (by rfl) ⟨648563, by rfl⟩ : syracuseStep 3459005 = 1297127) (by norm_num)
theorem B2306003 : Blo 2305435 2306003 := bstep (se 1 (by rfl) ⟨1729502, by rfl⟩ : syracuseStep 2306003 = 3459005) B3459005
theorem B5188517 : Blo 2305435 5188517 := bbase (se 4 (by rfl) ⟨486423, by rfl⟩ : syracuseStep 5188517 = 972847) (by norm_num)
theorem B3459011 : Blo 2305435 3459011 := bstep (se 1 (by rfl) ⟨2594258, by rfl⟩ : syracuseStep 3459011 = 5188517) B5188517
theorem B2306007 : Blo 2305435 2306007 := bstep (se 1 (by rfl) ⟨1729505, by rfl⟩ : syracuseStep 2306007 = 3459011) B3459011
theorem B5837093 : Blo 2305435 5837093 := bbase (se 4 (by rfl) ⟨547227, by rfl⟩ : syracuseStep 5837093 = 1094455) (by norm_num)
theorem B3891395 : Blo 2305435 3891395 := bstep (se 1 (by rfl) ⟨2918546, by rfl⟩ : syracuseStep 3891395 = 5837093) B5837093
theorem B2594263 : Blo 2305435 2594263 := bstep (se 1 (by rfl) ⟨1945697, by rfl⟩ : syracuseStep 2594263 = 3891395) B3891395
theorem B3459017 : Blo 2305435 3459017 := bstep (se 2 (by rfl) ⟨1297131, by rfl⟩ : syracuseStep 3459017 = 2594263) B2594263
theorem B2306011 : Blo 2305435 2306011 := bstep (se 1 (by rfl) ⟨1729508, by rfl⟩ : syracuseStep 2306011 = 3459017) B3459017
theorem B6566741 : Blo 2305435 6566741 := bbase (se 9 (by rfl) ⟨19238, by rfl⟩ : syracuseStep 6566741 = 38477) (by norm_num)
theorem B4377827 : Blo 2305435 4377827 := bstep (se 1 (by rfl) ⟨3283370, by rfl⟩ : syracuseStep 4377827 = 6566741) B6566741
theorem B11674205 : Blo 2305435 11674205 := bstep (se 3 (by rfl) ⟨2188913, by rfl⟩ : syracuseStep 11674205 = 4377827) B4377827
theorem B7782803 : Blo 2305435 7782803 := bstep (se 1 (by rfl) ⟨5837102, by rfl⟩ : syracuseStep 7782803 = 11674205) B11674205
theorem B5188535 : Blo 2305435 5188535 := bstep (se 1 (by rfl) ⟨3891401, by rfl⟩ : syracuseStep 5188535 = 7782803) B7782803
theorem B3459023 : Blo 2305435 3459023 := bstep (se 1 (by rfl) ⟨2594267, by rfl⟩ : syracuseStep 3459023 = 5188535) B5188535
theorem B2306015 : Blo 2305435 2306015 := bstep (se 1 (by rfl) ⟨1729511, by rfl⟩ : syracuseStep 2306015 = 3459023) B3459023
theorem B3459029 : Blo 2305435 3459029 := bbase (se 7 (by rfl) ⟨40535, by rfl⟩ : syracuseStep 3459029 = 81071) (by norm_num)
theorem B2306019 : Blo 2305435 2306019 := bstep (se 1 (by rfl) ⟨1729514, by rfl⟩ : syracuseStep 2306019 = 3459029) B3459029
theorem B8755685 : Blo 2305435 8755685 := bbase (se 4 (by rfl) ⟨820845, by rfl⟩ : syracuseStep 8755685 = 1641691) (by norm_num)
theorem B5837123 : Blo 2305435 5837123 := bstep (se 1 (by rfl) ⟨4377842, by rfl⟩ : syracuseStep 5837123 = 8755685) B8755685
theorem B3891415 : Blo 2305435 3891415 := bstep (se 1 (by rfl) ⟨2918561, by rfl⟩ : syracuseStep 3891415 = 5837123) B5837123
theorem B5188553 : Blo 2305435 5188553 := bstep (se 2 (by rfl) ⟨1945707, by rfl⟩ : syracuseStep 5188553 = 3891415) B3891415
theorem B3459035 : Blo 2305435 3459035 := bstep (se 1 (by rfl) ⟨2594276, by rfl⟩ : syracuseStep 3459035 = 5188553) B5188553
theorem B2306023 : Blo 2305435 2306023 := bstep (se 1 (by rfl) ⟨1729517, by rfl⟩ : syracuseStep 2306023 = 3459035) B3459035
theorem B2594281 : Blo 2305435 2594281 := bbase (se 2 (by rfl) ⟨972855, by rfl⟩ : syracuseStep 2594281 = 1945711) (by norm_num)
theorem B3459041 : Blo 2305435 3459041 := bstep (se 2 (by rfl) ⟨1297140, by rfl⟩ : syracuseStep 3459041 = 2594281) B2594281
theorem B2306027 : Blo 2305435 2306027 := bstep (se 1 (by rfl) ⟨1729520, by rfl⟩ : syracuseStep 2306027 = 3459041) B3459041
theorem B2462545 : Blo 2305435 2462545 := bbase (se 2 (by rfl) ⟨923454, by rfl⟩ : syracuseStep 2462545 = 1846909) (by norm_num)
theorem B13133573 : Blo 2305435 13133573 := bstep (se 4 (by rfl) ⟨1231272, by rfl⟩ : syracuseStep 13133573 = 2462545) B2462545
theorem B8755715 : Blo 2305435 8755715 := bstep (se 1 (by rfl) ⟨6566786, by rfl⟩ : syracuseStep 8755715 = 13133573) B13133573
theorem B5837143 : Blo 2305435 5837143 := bstep (se 1 (by rfl) ⟨4377857, by rfl⟩ : syracuseStep 5837143 = 8755715) B8755715
theorem B7782857 : Blo 2305435 7782857 := bstep (se 2 (by rfl) ⟨2918571, by rfl⟩ : syracuseStep 7782857 = 5837143) B5837143
theorem B5188571 : Blo 2305435 5188571 := bstep (se 1 (by rfl) ⟨3891428, by rfl⟩ : syracuseStep 5188571 = 7782857) B7782857
theorem B3459047 : Blo 2305435 3459047 := bstep (se 1 (by rfl) ⟨2594285, by rfl⟩ : syracuseStep 3459047 = 5188571) B5188571
theorem B2306031 : Blo 2305435 2306031 := bstep (se 1 (by rfl) ⟨1729523, by rfl⟩ : syracuseStep 2306031 = 3459047) B3459047
theorem B3459053 : Blo 2305435 3459053 := bbase (se 3 (by rfl) ⟨648572, by rfl⟩ : syracuseStep 3459053 = 1297145) (by norm_num)
theorem B2306035 : Blo 2305435 2306035 := bstep (se 1 (by rfl) ⟨1729526, by rfl⟩ : syracuseStep 2306035 = 3459053) B3459053
theorem B5188589 : Blo 2305435 5188589 := bbase (se 3 (by rfl) ⟨972860, by rfl⟩ : syracuseStep 5188589 = 1945721) (by norm_num)
theorem B3459059 : Blo 2305435 3459059 := bstep (se 1 (by rfl) ⟨2594294, by rfl⟩ : syracuseStep 3459059 = 5188589) B5188589
theorem B2306039 : Blo 2305435 2306039 := bstep (se 1 (by rfl) ⟨1729529, by rfl⟩ : syracuseStep 2306039 = 3459059) B3459059
theorem B4925117 : Blo 2305435 4925117 := bbase (se 3 (by rfl) ⟨923459, by rfl⟩ : syracuseStep 4925117 = 1846919) (by norm_num)
theorem B3283411 : Blo 2305435 3283411 := bstep (se 1 (by rfl) ⟨2462558, by rfl⟩ : syracuseStep 3283411 = 4925117) B4925117
theorem B4377881 : Blo 2305435 4377881 := bstep (se 2 (by rfl) ⟨1641705, by rfl⟩ : syracuseStep 4377881 = 3283411) B3283411
theorem B2918587 : Blo 2305435 2918587 := bstep (se 1 (by rfl) ⟨2188940, by rfl⟩ : syracuseStep 2918587 = 4377881) B4377881
theorem B3891449 : Blo 2305435 3891449 := bstep (se 2 (by rfl) ⟨1459293, by rfl⟩ : syracuseStep 3891449 = 2918587) B2918587
theorem B2594299 : Blo 2305435 2594299 := bstep (se 1 (by rfl) ⟨1945724, by rfl⟩ : syracuseStep 2594299 = 3891449) B3891449
theorem B3459065 : Blo 2305435 3459065 := bstep (se 2 (by rfl) ⟨1297149, by rfl⟩ : syracuseStep 3459065 = 2594299) B2594299
theorem B2306043 : Blo 2305435 2306043 := bstep (se 1 (by rfl) ⟨1729532, by rfl⟩ : syracuseStep 2306043 = 3459065) B3459065
theorem B13494485 : Blo 2305435 13494485 := bbase (se 7 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 13494485 = 316277) (by norm_num)
theorem B35985293 : Blo 2305435 35985293 := bstep (se 3 (by rfl) ⟨6747242, by rfl⟩ : syracuseStep 35985293 = 13494485) B13494485
theorem B23990195 : Blo 2305435 23990195 := bstep (se 1 (by rfl) ⟨17992646, by rfl⟩ : syracuseStep 23990195 = 35985293) B35985293
theorem B15993463 : Blo 2305435 15993463 := bstep (se 1 (by rfl) ⟨11995097, by rfl⟩ : syracuseStep 15993463 = 23990195) B23990195
theorem B21324617 : Blo 2305435 21324617 := bstep (se 2 (by rfl) ⟨7996731, by rfl⟩ : syracuseStep 21324617 = 15993463) B15993463
theorem B14216411 : Blo 2305435 14216411 := bstep (se 1 (by rfl) ⟨10662308, by rfl⟩ : syracuseStep 14216411 = 21324617) B21324617
theorem B37910429 : Blo 2305435 37910429 := bstep (se 3 (by rfl) ⟨7108205, by rfl⟩ : syracuseStep 37910429 = 14216411) B14216411
theorem B25273619 : Blo 2305435 25273619 := bstep (se 1 (by rfl) ⟨18955214, by rfl⟩ : syracuseStep 25273619 = 37910429) B37910429
theorem B16849079 : Blo 2305435 16849079 := bstep (se 1 (by rfl) ⟨12636809, by rfl⟩ : syracuseStep 16849079 = 25273619) B25273619
theorem B11232719 : Blo 2305435 11232719 := bstep (se 1 (by rfl) ⟨8424539, by rfl⟩ : syracuseStep 11232719 = 16849079) B16849079
theorem B7488479 : Blo 2305435 7488479 := bstep (se 1 (by rfl) ⟨5616359, by rfl⟩ : syracuseStep 7488479 = 11232719) B11232719
theorem B4992319 : Blo 2305435 4992319 := bstep (se 1 (by rfl) ⟨3744239, by rfl⟩ : syracuseStep 4992319 = 7488479) B7488479
theorem B26625701 : Blo 2305435 26625701 := bstep (se 4 (by rfl) ⟨2496159, by rfl⟩ : syracuseStep 26625701 = 4992319) B4992319
theorem B17750467 : Blo 2305435 17750467 := bstep (se 1 (by rfl) ⟨13312850, by rfl⟩ : syracuseStep 17750467 = 26625701) B26625701
theorem B94669157 : Blo 2305435 94669157 := bstep (se 4 (by rfl) ⟨8875233, by rfl⟩ : syracuseStep 94669157 = 17750467) B17750467
theorem B63112771 : Blo 2305435 63112771 := bstep (se 1 (by rfl) ⟨47334578, by rfl⟩ : syracuseStep 63112771 = 94669157) B94669157
theorem B84150361 : Blo 2305435 84150361 := bstep (se 2 (by rfl) ⟨31556385, by rfl⟩ : syracuseStep 84150361 = 63112771) B63112771
theorem B112200481 : Blo 2305435 112200481 := bstep (se 2 (by rfl) ⟨42075180, by rfl⟩ : syracuseStep 112200481 = 84150361) B84150361
theorem B149600641 : Blo 2305435 149600641 := bstep (se 2 (by rfl) ⟨56100240, by rfl⟩ : syracuseStep 149600641 = 112200481) B112200481
theorem B199467521 : Blo 2305435 199467521 := bstep (se 2 (by rfl) ⟨74800320, by rfl⟩ : syracuseStep 199467521 = 149600641) B149600641
theorem B132978347 : Blo 2305435 132978347 := bstep (se 1 (by rfl) ⟨99733760, by rfl⟩ : syracuseStep 132978347 = 199467521) B199467521
theorem B88652231 : Blo 2305435 88652231 := bstep (se 1 (by rfl) ⟨66489173, by rfl⟩ : syracuseStep 88652231 = 132978347) B132978347
theorem B59101487 : Blo 2305435 59101487 := bstep (se 1 (by rfl) ⟨44326115, by rfl⟩ : syracuseStep 59101487 = 88652231) B88652231
theorem B39400991 : Blo 2305435 39400991 := bstep (se 1 (by rfl) ⟨29550743, by rfl⟩ : syracuseStep 39400991 = 59101487) B59101487
theorem B26267327 : Blo 2305435 26267327 := bstep (se 1 (by rfl) ⟨19700495, by rfl⟩ : syracuseStep 26267327 = 39400991) B39400991
theorem B17511551 : Blo 2305435 17511551 := bstep (se 1 (by rfl) ⟨13133663, by rfl⟩ : syracuseStep 17511551 = 26267327) B26267327
theorem B11674367 : Blo 2305435 11674367 := bstep (se 1 (by rfl) ⟨8755775, by rfl⟩ : syracuseStep 11674367 = 17511551) B17511551
theorem B7782911 : Blo 2305435 7782911 := bstep (se 1 (by rfl) ⟨5837183, by rfl⟩ : syracuseStep 7782911 = 11674367) B11674367
theorem B5188607 : Blo 2305435 5188607 := bstep (se 1 (by rfl) ⟨3891455, by rfl⟩ : syracuseStep 5188607 = 7782911) B7782911
theorem B3459071 : Blo 2305435 3459071 := bstep (se 1 (by rfl) ⟨2594303, by rfl⟩ : syracuseStep 3459071 = 5188607) B5188607
theorem B2306047 : Blo 2305435 2306047 := bstep (se 1 (by rfl) ⟨1729535, by rfl⟩ : syracuseStep 2306047 = 3459071) B3459071
theorem B3459077 : Blo 2305435 3459077 := bbase (se 4 (by rfl) ⟨324288, by rfl⟩ : syracuseStep 3459077 = 648577) (by norm_num)
theorem B2306051 : Blo 2305435 2306051 := bstep (se 1 (by rfl) ⟨1729538, by rfl⟩ : syracuseStep 2306051 = 3459077) B3459077
theorem B3891469 : Blo 2305435 3891469 := bbase (se 3 (by rfl) ⟨729650, by rfl⟩ : syracuseStep 3891469 = 1459301) (by norm_num)
theorem B5188625 : Blo 2305435 5188625 := bstep (se 2 (by rfl) ⟨1945734, by rfl⟩ : syracuseStep 5188625 = 3891469) B3891469
theorem B3459083 : Blo 2305435 3459083 := bstep (se 1 (by rfl) ⟨2594312, by rfl⟩ : syracuseStep 3459083 = 5188625) B5188625
theorem B2306055 : Blo 2305435 2306055 := bstep (se 1 (by rfl) ⟨1729541, by rfl⟩ : syracuseStep 2306055 = 3459083) B3459083
theorem B2594317 : Blo 2305435 2594317 := bbase (se 3 (by rfl) ⟨486434, by rfl⟩ : syracuseStep 2594317 = 972869) (by norm_num)
theorem B3459089 : Blo 2305435 3459089 := bstep (se 2 (by rfl) ⟨1297158, by rfl⟩ : syracuseStep 3459089 = 2594317) B2594317
theorem B2306059 : Blo 2305435 2306059 := bstep (se 1 (by rfl) ⟨1729544, by rfl⟩ : syracuseStep 2306059 = 3459089) B3459089
theorem B7782965 : Blo 2305435 7782965 := bbase (se 5 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 7782965 = 729653) (by norm_num)
theorem B5188643 : Blo 2305435 5188643 := bstep (se 1 (by rfl) ⟨3891482, by rfl⟩ : syracuseStep 5188643 = 7782965) B7782965
theorem B3459095 : Blo 2305435 3459095 := bstep (se 1 (by rfl) ⟨2594321, by rfl⟩ : syracuseStep 3459095 = 5188643) B5188643
theorem B2306063 : Blo 2305435 2306063 := bstep (se 1 (by rfl) ⟨1729547, by rfl⟩ : syracuseStep 2306063 = 3459095) B3459095
theorem B3459101 : Blo 2305435 3459101 := bbase (se 3 (by rfl) ⟨648581, by rfl⟩ : syracuseStep 3459101 = 1297163) (by norm_num)
theorem B2306067 : Blo 2305435 2306067 := bstep (se 1 (by rfl) ⟨1729550, by rfl⟩ : syracuseStep 2306067 = 3459101) B3459101
theorem B5188661 : Blo 2305435 5188661 := bbase (se 5 (by rfl) ⟨243218, by rfl⟩ : syracuseStep 5188661 = 486437) (by norm_num)
theorem B3459107 : Blo 2305435 3459107 := bstep (se 1 (by rfl) ⟨2594330, by rfl⟩ : syracuseStep 3459107 = 5188661) B5188661
theorem B2306071 : Blo 2305435 2306071 := bstep (se 1 (by rfl) ⟨1729553, by rfl⟩ : syracuseStep 2306071 = 3459107) B3459107
theorem B2958449 : Blo 2305435 2958449 := bbase (se 2 (by rfl) ⟨1109418, by rfl⟩ : syracuseStep 2958449 = 2218837) (by norm_num)
theorem B7889197 : Blo 2305435 7889197 := bstep (se 3 (by rfl) ⟨1479224, by rfl⟩ : syracuseStep 7889197 = 2958449) B2958449
theorem B10518929 : Blo 2305435 10518929 := bstep (se 2 (by rfl) ⟨3944598, by rfl⟩ : syracuseStep 10518929 = 7889197) B7889197
theorem B7012619 : Blo 2305435 7012619 := bstep (se 1 (by rfl) ⟨5259464, by rfl⟩ : syracuseStep 7012619 = 10518929) B10518929
theorem B4675079 : Blo 2305435 4675079 := bstep (se 1 (by rfl) ⟨3506309, by rfl⟩ : syracuseStep 4675079 = 7012619) B7012619
theorem B3116719 : Blo 2305435 3116719 := bstep (se 1 (by rfl) ⟨2337539, by rfl⟩ : syracuseStep 3116719 = 4675079) B4675079
theorem B4155625 : Blo 2305435 4155625 := bstep (se 2 (by rfl) ⟨1558359, by rfl⟩ : syracuseStep 4155625 = 3116719) B3116719
theorem B5540833 : Blo 2305435 5540833 := bstep (se 2 (by rfl) ⟨2077812, by rfl⟩ : syracuseStep 5540833 = 4155625) B4155625
theorem B7387777 : Blo 2305435 7387777 := bstep (se 2 (by rfl) ⟨2770416, by rfl⟩ : syracuseStep 7387777 = 5540833) B5540833
theorem B9850369 : Blo 2305435 9850369 := bstep (se 2 (by rfl) ⟨3693888, by rfl⟩ : syracuseStep 9850369 = 7387777) B7387777
theorem B13133825 : Blo 2305435 13133825 := bstep (se 2 (by rfl) ⟨4925184, by rfl⟩ : syracuseStep 13133825 = 9850369) B9850369
theorem B8755883 : Blo 2305435 8755883 := bstep (se 1 (by rfl) ⟨6566912, by rfl⟩ : syracuseStep 8755883 = 13133825) B13133825
theorem B5837255 : Blo 2305435 5837255 := bstep (se 1 (by rfl) ⟨4377941, by rfl⟩ : syracuseStep 5837255 = 8755883) B8755883
theorem B3891503 : Blo 2305435 3891503 := bstep (se 1 (by rfl) ⟨2918627, by rfl⟩ : syracuseStep 3891503 = 5837255) B5837255
theorem B2594335 : Blo 2305435 2594335 := bstep (se 1 (by rfl) ⟨1945751, by rfl⟩ : syracuseStep 2594335 = 3891503) B3891503
theorem B3459113 : Blo 2305435 3459113 := bstep (se 2 (by rfl) ⟨1297167, by rfl⟩ : syracuseStep 3459113 = 2594335) B2594335
theorem B2306075 : Blo 2305435 2306075 := bstep (se 1 (by rfl) ⟨1729556, by rfl⟩ : syracuseStep 2306075 = 3459113) B3459113
theorem B2770421 : Blo 2305435 2770421 := bbase (se 5 (by rfl) ⟨129863, by rfl⟩ : syracuseStep 2770421 = 259727) (by norm_num)
theorem B7387789 : Blo 2305435 7387789 := bstep (se 3 (by rfl) ⟨1385210, by rfl⟩ : syracuseStep 7387789 = 2770421) B2770421
theorem B9850385 : Blo 2305435 9850385 := bstep (se 2 (by rfl) ⟨3693894, by rfl⟩ : syracuseStep 9850385 = 7387789) B7387789
theorem B6566923 : Blo 2305435 6566923 := bstep (se 1 (by rfl) ⟨4925192, by rfl⟩ : syracuseStep 6566923 = 9850385) B9850385
theorem B8755897 : Blo 2305435 8755897 := bstep (se 2 (by rfl) ⟨3283461, by rfl⟩ : syracuseStep 8755897 = 6566923) B6566923
theorem B11674529 : Blo 2305435 11674529 := bstep (se 2 (by rfl) ⟨4377948, by rfl⟩ : syracuseStep 11674529 = 8755897) B8755897
theorem B7783019 : Blo 2305435 7783019 := bstep (se 1 (by rfl) ⟨5837264, by rfl⟩ : syracuseStep 7783019 = 11674529) B11674529
theorem B5188679 : Blo 2305435 5188679 := bstep (se 1 (by rfl) ⟨3891509, by rfl⟩ : syracuseStep 5188679 = 7783019) B7783019
theorem B3459119 : Blo 2305435 3459119 := bstep (se 1 (by rfl) ⟨2594339, by rfl⟩ : syracuseStep 3459119 = 5188679) B5188679
theorem B2306079 : Blo 2305435 2306079 := bstep (se 1 (by rfl) ⟨1729559, by rfl⟩ : syracuseStep 2306079 = 3459119) B3459119
theorem B3459125 : Blo 2305435 3459125 := bbase (se 5 (by rfl) ⟨162146, by rfl⟩ : syracuseStep 3459125 = 324293) (by norm_num)
theorem B2306083 : Blo 2305435 2306083 := bstep (se 1 (by rfl) ⟨1729562, by rfl⟩ : syracuseStep 2306083 = 3459125) B3459125
theorem B5837285 : Blo 2305435 5837285 := bbase (se 4 (by rfl) ⟨547245, by rfl⟩ : syracuseStep 5837285 = 1094491) (by norm_num)
theorem B3891523 : Blo 2305435 3891523 := bstep (se 1 (by rfl) ⟨2918642, by rfl⟩ : syracuseStep 3891523 = 5837285) B5837285
theorem B5188697 : Blo 2305435 5188697 := bstep (se 2 (by rfl) ⟨1945761, by rfl⟩ : syracuseStep 5188697 = 3891523) B3891523
theorem B3459131 : Blo 2305435 3459131 := bstep (se 1 (by rfl) ⟨2594348, by rfl⟩ : syracuseStep 3459131 = 5188697) B5188697
theorem B2306087 : Blo 2305435 2306087 := bstep (se 1 (by rfl) ⟨1729565, by rfl⟩ : syracuseStep 2306087 = 3459131) B3459131
theorem B2594353 : Blo 2305435 2594353 := bbase (se 2 (by rfl) ⟨972882, by rfl⟩ : syracuseStep 2594353 = 1945765) (by norm_num)
theorem B3459137 : Blo 2305435 3459137 := bstep (se 2 (by rfl) ⟨1297176, by rfl⟩ : syracuseStep 3459137 = 2594353) B2594353
theorem B2306091 : Blo 2305435 2306091 := bstep (se 1 (by rfl) ⟨1729568, by rfl⟩ : syracuseStep 2306091 = 3459137) B3459137
theorem B4155661 : Blo 2305435 4155661 := bbase (se 3 (by rfl) ⟨779186, by rfl⟩ : syracuseStep 4155661 = 1558373) (by norm_num)
theorem B5540881 : Blo 2305435 5540881 := bstep (se 2 (by rfl) ⟨2077830, by rfl⟩ : syracuseStep 5540881 = 4155661) B4155661
theorem B7387841 : Blo 2305435 7387841 := bstep (se 2 (by rfl) ⟨2770440, by rfl⟩ : syracuseStep 7387841 = 5540881) B5540881
theorem B4925227 : Blo 2305435 4925227 := bstep (se 1 (by rfl) ⟨3693920, by rfl⟩ : syracuseStep 4925227 = 7387841) B7387841
theorem B6566969 : Blo 2305435 6566969 := bstep (se 2 (by rfl) ⟨2462613, by rfl⟩ : syracuseStep 6566969 = 4925227) B4925227
theorem B4377979 : Blo 2305435 4377979 := bstep (se 1 (by rfl) ⟨3283484, by rfl⟩ : syracuseStep 4377979 = 6566969) B6566969
theorem B5837305 : Blo 2305435 5837305 := bstep (se 2 (by rfl) ⟨2188989, by rfl⟩ : syracuseStep 5837305 = 4377979) B4377979
theorem B7783073 : Blo 2305435 7783073 := bstep (se 2 (by rfl) ⟨2918652, by rfl⟩ : syracuseStep 7783073 = 5837305) B5837305
theorem B5188715 : Blo 2305435 5188715 := bstep (se 1 (by rfl) ⟨3891536, by rfl⟩ : syracuseStep 5188715 = 7783073) B7783073
theorem B3459143 : Blo 2305435 3459143 := bstep (se 1 (by rfl) ⟨2594357, by rfl⟩ : syracuseStep 3459143 = 5188715) B5188715
theorem B2306095 : Blo 2305435 2306095 := bstep (se 1 (by rfl) ⟨1729571, by rfl⟩ : syracuseStep 2306095 = 3459143) B3459143
theorem B3459149 : Blo 2305435 3459149 := bbase (se 3 (by rfl) ⟨648590, by rfl⟩ : syracuseStep 3459149 = 1297181) (by norm_num)
theorem B2306099 : Blo 2305435 2306099 := bstep (se 1 (by rfl) ⟨1729574, by rfl⟩ : syracuseStep 2306099 = 3459149) B3459149
theorem B5188733 : Blo 2305435 5188733 := bbase (se 3 (by rfl) ⟨972887, by rfl⟩ : syracuseStep 5188733 = 1945775) (by norm_num)
theorem B3459155 : Blo 2305435 3459155 := bstep (se 1 (by rfl) ⟨2594366, by rfl⟩ : syracuseStep 3459155 = 5188733) B5188733
theorem B2306103 : Blo 2305435 2306103 := bstep (se 1 (by rfl) ⟨1729577, by rfl⟩ : syracuseStep 2306103 = 3459155) B3459155
theorem B3891557 : Blo 2305435 3891557 := bbase (se 4 (by rfl) ⟨364833, by rfl⟩ : syracuseStep 3891557 = 729667) (by norm_num)
theorem B2594371 : Blo 2305435 2594371 := bstep (se 1 (by rfl) ⟨1945778, by rfl⟩ : syracuseStep 2594371 = 3891557) B3891557
theorem B3459161 : Blo 2305435 3459161 := bstep (se 2 (by rfl) ⟨1297185, by rfl⟩ : syracuseStep 3459161 = 2594371) B2594371
theorem B2306107 : Blo 2305435 2306107 := bstep (se 1 (by rfl) ⟨1729580, by rfl⟩ : syracuseStep 2306107 = 3459161) B3459161
theorem B4925261 : Blo 2305435 4925261 := bbase (se 3 (by rfl) ⟨923486, by rfl⟩ : syracuseStep 4925261 = 1846973) (by norm_num)
theorem B3283507 : Blo 2305435 3283507 := bstep (se 1 (by rfl) ⟨2462630, by rfl⟩ : syracuseStep 3283507 = 4925261) B4925261
theorem B17512037 : Blo 2305435 17512037 := bstep (se 4 (by rfl) ⟨1641753, by rfl⟩ : syracuseStep 17512037 = 3283507) B3283507
theorem B11674691 : Blo 2305435 11674691 := bstep (se 1 (by rfl) ⟨8756018, by rfl⟩ : syracuseStep 11674691 = 17512037) B17512037
theorem B7783127 : Blo 2305435 7783127 := bstep (se 1 (by rfl) ⟨5837345, by rfl⟩ : syracuseStep 7783127 = 11674691) B11674691
theorem B5188751 : Blo 2305435 5188751 := bstep (se 1 (by rfl) ⟨3891563, by rfl⟩ : syracuseStep 5188751 = 7783127) B7783127
theorem B3459167 : Blo 2305435 3459167 := bstep (se 1 (by rfl) ⟨2594375, by rfl⟩ : syracuseStep 3459167 = 5188751) B5188751
theorem B2306111 : Blo 2305435 2306111 := bstep (se 1 (by rfl) ⟨1729583, by rfl⟩ : syracuseStep 2306111 = 3459167) B3459167
theorem B3459173 : Blo 2305435 3459173 := bbase (se 4 (by rfl) ⟨324297, by rfl⟩ : syracuseStep 3459173 = 648595) (by norm_num)
theorem B2306115 : Blo 2305435 2306115 := bstep (se 1 (by rfl) ⟨1729586, by rfl⟩ : syracuseStep 2306115 = 3459173) B3459173
theorem B24934229 : Blo 2305435 24934229 := bbase (se 9 (by rfl) ⟨73049, by rfl⟩ : syracuseStep 24934229 = 146099) (by norm_num)
theorem B16622819 : Blo 2305435 16622819 := bstep (se 1 (by rfl) ⟨12467114, by rfl⟩ : syracuseStep 16622819 = 24934229) B24934229
theorem B11081879 : Blo 2305435 11081879 := bstep (se 1 (by rfl) ⟨8311409, by rfl⟩ : syracuseStep 11081879 = 16622819) B16622819
theorem B7387919 : Blo 2305435 7387919 := bstep (se 1 (by rfl) ⟨5540939, by rfl⟩ : syracuseStep 7387919 = 11081879) B11081879
theorem B4925279 : Blo 2305435 4925279 := bstep (se 1 (by rfl) ⟨3693959, by rfl⟩ : syracuseStep 4925279 = 7387919) B7387919
theorem B3283519 : Blo 2305435 3283519 := bstep (se 1 (by rfl) ⟨2462639, by rfl⟩ : syracuseStep 3283519 = 4925279) B4925279
theorem B4378025 : Blo 2305435 4378025 := bstep (se 2 (by rfl) ⟨1641759, by rfl⟩ : syracuseStep 4378025 = 3283519) B3283519
theorem B2918683 : Blo 2305435 2918683 := bstep (se 1 (by rfl) ⟨2189012, by rfl⟩ : syracuseStep 2918683 = 4378025) B4378025
theorem B3891577 : Blo 2305435 3891577 := bstep (se 2 (by rfl) ⟨1459341, by rfl⟩ : syracuseStep 3891577 = 2918683) B2918683
theorem B5188769 : Blo 2305435 5188769 := bstep (se 2 (by rfl) ⟨1945788, by rfl⟩ : syracuseStep 5188769 = 3891577) B3891577
theorem B3459179 : Blo 2305435 3459179 := bstep (se 1 (by rfl) ⟨2594384, by rfl⟩ : syracuseStep 3459179 = 5188769) B5188769
theorem B2306119 : Blo 2305435 2306119 := bstep (se 1 (by rfl) ⟨1729589, by rfl⟩ : syracuseStep 2306119 = 3459179) B3459179
theorem B2594389 : Blo 2305435 2594389 := bbase (se 8 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 2594389 = 30403) (by norm_num)
theorem B3459185 : Blo 2305435 3459185 := bstep (se 2 (by rfl) ⟨1297194, by rfl⟩ : syracuseStep 3459185 = 2594389) B2594389
theorem B2306123 : Blo 2305435 2306123 := bstep (se 1 (by rfl) ⟨1729592, by rfl⟩ : syracuseStep 2306123 = 3459185) B3459185
theorem B2918693 : Blo 2305435 2918693 := bbase (se 4 (by rfl) ⟨273627, by rfl⟩ : syracuseStep 2918693 = 547255) (by norm_num)
theorem B7783181 : Blo 2305435 7783181 := bstep (se 3 (by rfl) ⟨1459346, by rfl⟩ : syracuseStep 7783181 = 2918693) B2918693
theorem B5188787 : Blo 2305435 5188787 := bstep (se 1 (by rfl) ⟨3891590, by rfl⟩ : syracuseStep 5188787 = 7783181) B7783181
theorem B3459191 : Blo 2305435 3459191 := bstep (se 1 (by rfl) ⟨2594393, by rfl⟩ : syracuseStep 3459191 = 5188787) B5188787
theorem B2306127 : Blo 2305435 2306127 := bstep (se 1 (by rfl) ⟨1729595, by rfl⟩ : syracuseStep 2306127 = 3459191) B3459191
theorem B3459197 : Blo 2305435 3459197 := bbase (se 3 (by rfl) ⟨648599, by rfl⟩ : syracuseStep 3459197 = 1297199) (by norm_num)
theorem B2306131 : Blo 2305435 2306131 := bstep (se 1 (by rfl) ⟨1729598, by rfl⟩ : syracuseStep 2306131 = 3459197) B3459197
theorem B5188805 : Blo 2305435 5188805 := bbase (se 4 (by rfl) ⟨486450, by rfl⟩ : syracuseStep 5188805 = 972901) (by norm_num)
theorem B3459203 : Blo 2305435 3459203 := bstep (se 1 (by rfl) ⟨2594402, by rfl⟩ : syracuseStep 3459203 = 5188805) B5188805
theorem B2306135 : Blo 2305435 2306135 := bstep (se 1 (by rfl) ⟨1729601, by rfl⟩ : syracuseStep 2306135 = 3459203) B3459203
theorem B2629805 : Blo 2305435 2629805 := bbase (se 3 (by rfl) ⟨493088, by rfl⟩ : syracuseStep 2629805 = 986177) (by norm_num)
theorem B7012813 : Blo 2305435 7012813 := bstep (se 3 (by rfl) ⟨1314902, by rfl⟩ : syracuseStep 7012813 = 2629805) B2629805
theorem B9350417 : Blo 2305435 9350417 := bstep (se 2 (by rfl) ⟨3506406, by rfl⟩ : syracuseStep 9350417 = 7012813) B7012813
theorem B6233611 : Blo 2305435 6233611 := bstep (se 1 (by rfl) ⟨4675208, by rfl⟩ : syracuseStep 6233611 = 9350417) B9350417
theorem B8311481 : Blo 2305435 8311481 := bstep (se 2 (by rfl) ⟨3116805, by rfl⟩ : syracuseStep 8311481 = 6233611) B6233611
theorem B5540987 : Blo 2305435 5540987 := bstep (se 1 (by rfl) ⟨4155740, by rfl⟩ : syracuseStep 5540987 = 8311481) B8311481
theorem B14775965 : Blo 2305435 14775965 := bstep (se 3 (by rfl) ⟨2770493, by rfl⟩ : syracuseStep 14775965 = 5540987) B5540987
theorem B9850643 : Blo 2305435 9850643 := bstep (se 1 (by rfl) ⟨7387982, by rfl⟩ : syracuseStep 9850643 = 14775965) B14775965
theorem B6567095 : Blo 2305435 6567095 := bstep (se 1 (by rfl) ⟨4925321, by rfl⟩ : syracuseStep 6567095 = 9850643) B9850643
theorem B4378063 : Blo 2305435 4378063 := bstep (se 1 (by rfl) ⟨3283547, by rfl⟩ : syracuseStep 4378063 = 6567095) B6567095
theorem B5837417 : Blo 2305435 5837417 := bstep (se 2 (by rfl) ⟨2189031, by rfl⟩ : syracuseStep 5837417 = 4378063) B4378063
theorem B3891611 : Blo 2305435 3891611 := bstep (se 1 (by rfl) ⟨2918708, by rfl⟩ : syracuseStep 3891611 = 5837417) B5837417
theorem B2594407 : Blo 2305435 2594407 := bstep (se 1 (by rfl) ⟨1945805, by rfl⟩ : syracuseStep 2594407 = 3891611) B3891611
theorem B3459209 : Blo 2305435 3459209 := bstep (se 2 (by rfl) ⟨1297203, by rfl⟩ : syracuseStep 3459209 = 2594407) B2594407
theorem B2306139 : Blo 2305435 2306139 := bstep (se 1 (by rfl) ⟨1729604, by rfl⟩ : syracuseStep 2306139 = 3459209) B3459209
theorem B11674853 : Blo 2305435 11674853 := bbase (se 4 (by rfl) ⟨1094517, by rfl⟩ : syracuseStep 11674853 = 2189035) (by norm_num)
theorem B7783235 : Blo 2305435 7783235 := bstep (se 1 (by rfl) ⟨5837426, by rfl⟩ : syracuseStep 7783235 = 11674853) B11674853
theorem B5188823 : Blo 2305435 5188823 := bstep (se 1 (by rfl) ⟨3891617, by rfl⟩ : syracuseStep 5188823 = 7783235) B7783235
theorem B3459215 : Blo 2305435 3459215 := bstep (se 1 (by rfl) ⟨2594411, by rfl⟩ : syracuseStep 3459215 = 5188823) B5188823
theorem B2306143 : Blo 2305435 2306143 := bstep (se 1 (by rfl) ⟨1729607, by rfl⟩ : syracuseStep 2306143 = 3459215) B3459215
theorem B3459221 : Blo 2305435 3459221 := bbase (se 6 (by rfl) ⟨81075, by rfl⟩ : syracuseStep 3459221 = 162151) (by norm_num)
theorem B2306147 : Blo 2305435 2306147 := bstep (se 1 (by rfl) ⟨1729610, by rfl⟩ : syracuseStep 2306147 = 3459221) B3459221
theorem B9850693 : Blo 2305435 9850693 := bbase (se 4 (by rfl) ⟨923502, by rfl⟩ : syracuseStep 9850693 = 1847005) (by norm_num)
theorem B13134257 : Blo 2305435 13134257 := bstep (se 2 (by rfl) ⟨4925346, by rfl⟩ : syracuseStep 13134257 = 9850693) B9850693
theorem B8756171 : Blo 2305435 8756171 := bstep (se 1 (by rfl) ⟨6567128, by rfl⟩ : syracuseStep 8756171 = 13134257) B13134257
theorem B5837447 : Blo 2305435 5837447 := bstep (se 1 (by rfl) ⟨4378085, by rfl⟩ : syracuseStep 5837447 = 8756171) B8756171
theorem B3891631 : Blo 2305435 3891631 := bstep (se 1 (by rfl) ⟨2918723, by rfl⟩ : syracuseStep 3891631 = 5837447) B5837447
theorem B5188841 : Blo 2305435 5188841 := bstep (se 2 (by rfl) ⟨1945815, by rfl⟩ : syracuseStep 5188841 = 3891631) B3891631
theorem B3459227 : Blo 2305435 3459227 := bstep (se 1 (by rfl) ⟨2594420, by rfl⟩ : syracuseStep 3459227 = 5188841) B5188841
theorem B2306151 : Blo 2305435 2306151 := bstep (se 1 (by rfl) ⟨1729613, by rfl⟩ : syracuseStep 2306151 = 3459227) B3459227
theorem B2594425 : Blo 2305435 2594425 := bbase (se 2 (by rfl) ⟨972909, by rfl⟩ : syracuseStep 2594425 = 1945819) (by norm_num)
theorem B3459233 : Blo 2305435 3459233 := bstep (se 2 (by rfl) ⟨1297212, by rfl⟩ : syracuseStep 3459233 = 2594425) B2594425
theorem B2306155 : Blo 2305435 2306155 := bstep (se 1 (by rfl) ⟨1729616, by rfl⟩ : syracuseStep 2306155 = 3459233) B3459233
theorem B8424949 : Blo 2305435 8424949 := bbase (se 5 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 8424949 = 789839) (by norm_num)
theorem B11233265 : Blo 2305435 11233265 := bstep (se 2 (by rfl) ⟨4212474, by rfl⟩ : syracuseStep 11233265 = 8424949) B8424949
theorem B119821493 : Blo 2305435 119821493 := bstep (se 5 (by rfl) ⟨5616632, by rfl⟩ : syracuseStep 119821493 = 11233265) B11233265
theorem B79880995 : Blo 2305435 79880995 := bstep (se 1 (by rfl) ⟨59910746, by rfl⟩ : syracuseStep 79880995 = 119821493) B119821493
theorem B426031973 : Blo 2305435 426031973 := bstep (se 4 (by rfl) ⟨39940497, by rfl⟩ : syracuseStep 426031973 = 79880995) B79880995
theorem B284021315 : Blo 2305435 284021315 := bstep (se 1 (by rfl) ⟨213015986, by rfl⟩ : syracuseStep 284021315 = 426031973) B426031973
theorem B189347543 : Blo 2305435 189347543 := bstep (se 1 (by rfl) ⟨142010657, by rfl⟩ : syracuseStep 189347543 = 284021315) B284021315
theorem B126231695 : Blo 2305435 126231695 := bstep (se 1 (by rfl) ⟨94673771, by rfl⟩ : syracuseStep 126231695 = 189347543) B189347543
theorem B84154463 : Blo 2305435 84154463 := bstep (se 1 (by rfl) ⟨63115847, by rfl⟩ : syracuseStep 84154463 = 126231695) B126231695
theorem B56102975 : Blo 2305435 56102975 := bstep (se 1 (by rfl) ⟨42077231, by rfl⟩ : syracuseStep 56102975 = 84154463) B84154463
theorem B37401983 : Blo 2305435 37401983 := bstep (se 1 (by rfl) ⟨28051487, by rfl⟩ : syracuseStep 37401983 = 56102975) B56102975
theorem B24934655 : Blo 2305435 24934655 := bstep (se 1 (by rfl) ⟨18700991, by rfl⟩ : syracuseStep 24934655 = 37401983) B37401983
theorem B16623103 : Blo 2305435 16623103 := bstep (se 1 (by rfl) ⟨12467327, by rfl⟩ : syracuseStep 16623103 = 24934655) B24934655
theorem B22164137 : Blo 2305435 22164137 := bstep (se 2 (by rfl) ⟨8311551, by rfl⟩ : syracuseStep 22164137 = 16623103) B16623103
theorem B14776091 : Blo 2305435 14776091 := bstep (se 1 (by rfl) ⟨11082068, by rfl⟩ : syracuseStep 14776091 = 22164137) B22164137
theorem B9850727 : Blo 2305435 9850727 := bstep (se 1 (by rfl) ⟨7388045, by rfl⟩ : syracuseStep 9850727 = 14776091) B14776091
theorem B6567151 : Blo 2305435 6567151 := bstep (se 1 (by rfl) ⟨4925363, by rfl⟩ : syracuseStep 6567151 = 9850727) B9850727
theorem B8756201 : Blo 2305435 8756201 := bstep (se 2 (by rfl) ⟨3283575, by rfl⟩ : syracuseStep 8756201 = 6567151) B6567151
theorem B5837467 : Blo 2305435 5837467 := bstep (se 1 (by rfl) ⟨4378100, by rfl⟩ : syracuseStep 5837467 = 8756201) B8756201
theorem B7783289 : Blo 2305435 7783289 := bstep (se 2 (by rfl) ⟨2918733, by rfl⟩ : syracuseStep 7783289 = 5837467) B5837467
theorem B5188859 : Blo 2305435 5188859 := bstep (se 1 (by rfl) ⟨3891644, by rfl⟩ : syracuseStep 5188859 = 7783289) B7783289
theorem B3459239 : Blo 2305435 3459239 := bstep (se 1 (by rfl) ⟨2594429, by rfl⟩ : syracuseStep 3459239 = 5188859) B5188859
theorem B2306159 : Blo 2305435 2306159 := bstep (se 1 (by rfl) ⟨1729619, by rfl⟩ : syracuseStep 2306159 = 3459239) B3459239
theorem B3459245 : Blo 2305435 3459245 := bbase (se 3 (by rfl) ⟨648608, by rfl⟩ : syracuseStep 3459245 = 1297217) (by norm_num)
theorem B2306163 : Blo 2305435 2306163 := bstep (se 1 (by rfl) ⟨1729622, by rfl⟩ : syracuseStep 2306163 = 3459245) B3459245
theorem B5188877 : Blo 2305435 5188877 := bbase (se 3 (by rfl) ⟨972914, by rfl⟩ : syracuseStep 5188877 = 1945829) (by norm_num)
theorem B3459251 : Blo 2305435 3459251 := bstep (se 1 (by rfl) ⟨2594438, by rfl⟩ : syracuseStep 3459251 = 5188877) B5188877
theorem B2306167 : Blo 2305435 2306167 := bstep (se 1 (by rfl) ⟨1729625, by rfl⟩ : syracuseStep 2306167 = 3459251) B3459251
theorem B2918749 : Blo 2305435 2918749 := bbase (se 3 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 2918749 = 1094531) (by norm_num)
theorem B3891665 : Blo 2305435 3891665 := bstep (se 2 (by rfl) ⟨1459374, by rfl⟩ : syracuseStep 3891665 = 2918749) B2918749
theorem B2594443 : Blo 2305435 2594443 := bstep (se 1 (by rfl) ⟨1945832, by rfl⟩ : syracuseStep 2594443 = 3891665) B3891665
theorem B3459257 : Blo 2305435 3459257 := bstep (se 2 (by rfl) ⟨1297221, by rfl⟩ : syracuseStep 3459257 = 2594443) B2594443
theorem B2306171 : Blo 2305435 2306171 := bstep (se 1 (by rfl) ⟨1729628, by rfl⟩ : syracuseStep 2306171 = 3459257) B3459257
theorem B19701589 : Blo 2305435 19701589 := bbase (se 9 (by rfl) ⟨57719, by rfl⟩ : syracuseStep 19701589 = 115439) (by norm_num)
theorem B26268785 : Blo 2305435 26268785 := bstep (se 2 (by rfl) ⟨9850794, by rfl⟩ : syracuseStep 26268785 = 19701589) B19701589
theorem B17512523 : Blo 2305435 17512523 := bstep (se 1 (by rfl) ⟨13134392, by rfl⟩ : syracuseStep 17512523 = 26268785) B26268785
theorem B11675015 : Blo 2305435 11675015 := bstep (se 1 (by rfl) ⟨8756261, by rfl⟩ : syracuseStep 11675015 = 17512523) B17512523
theorem B7783343 : Blo 2305435 7783343 := bstep (se 1 (by rfl) ⟨5837507, by rfl⟩ : syracuseStep 7783343 = 11675015) B11675015
theorem B5188895 : Blo 2305435 5188895 := bstep (se 1 (by rfl) ⟨3891671, by rfl⟩ : syracuseStep 5188895 = 7783343) B7783343
theorem B3459263 : Blo 2305435 3459263 := bstep (se 1 (by rfl) ⟨2594447, by rfl⟩ : syracuseStep 3459263 = 5188895) B5188895
theorem B2306175 : Blo 2305435 2306175 := bstep (se 1 (by rfl) ⟨1729631, by rfl⟩ : syracuseStep 2306175 = 3459263) B3459263
theorem B3459269 : Blo 2305435 3459269 := bbase (se 4 (by rfl) ⟨324306, by rfl⟩ : syracuseStep 3459269 = 648613) (by norm_num)
theorem B2306179 : Blo 2305435 2306179 := bstep (se 1 (by rfl) ⟨1729634, by rfl⟩ : syracuseStep 2306179 = 3459269) B3459269
theorem B3891685 : Blo 2305435 3891685 := bbase (se 4 (by rfl) ⟨364845, by rfl⟩ : syracuseStep 3891685 = 729691) (by norm_num)
theorem B5188913 : Blo 2305435 5188913 := bstep (se 2 (by rfl) ⟨1945842, by rfl⟩ : syracuseStep 5188913 = 3891685) B3891685
theorem B3459275 : Blo 2305435 3459275 := bstep (se 1 (by rfl) ⟨2594456, by rfl⟩ : syracuseStep 3459275 = 5188913) B5188913
theorem B2306183 : Blo 2305435 2306183 := bstep (se 1 (by rfl) ⟨1729637, by rfl⟩ : syracuseStep 2306183 = 3459275) B3459275
theorem B2594461 : Blo 2305435 2594461 := bbase (se 3 (by rfl) ⟨486461, by rfl⟩ : syracuseStep 2594461 = 972923) (by norm_num)
theorem B3459281 : Blo 2305435 3459281 := bstep (se 2 (by rfl) ⟨1297230, by rfl⟩ : syracuseStep 3459281 = 2594461) B2594461
theorem B2306187 : Blo 2305435 2306187 := bstep (se 1 (by rfl) ⟨1729640, by rfl⟩ : syracuseStep 2306187 = 3459281) B3459281
theorem B7783397 : Blo 2305435 7783397 := bbase (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) (by norm_num)
theorem B5188931 : Blo 2305435 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B3459287 : Blo 2305435 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B2306191 : Blo 2305435 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B3459293 : Blo 2305435 3459293 := bbase (se 3 (by rfl) ⟨648617, by rfl⟩ : syracuseStep 3459293 = 1297235) (by norm_num)
theorem B2306195 : Blo 2305435 2306195 := bstep (se 1 (by rfl) ⟨1729646, by rfl⟩ : syracuseStep 2306195 = 3459293) B3459293
theorem B5188949 : Blo 2305435 5188949 := bbase (se 11 (by rfl) ⟨3800, by rfl⟩ : syracuseStep 5188949 = 7601) (by norm_num)
theorem B3459299 : Blo 2305435 3459299 := bstep (se 1 (by rfl) ⟨2594474, by rfl⟩ : syracuseStep 3459299 = 5188949) B5188949
theorem B2306199 : Blo 2305435 2306199 := bstep (se 1 (by rfl) ⟨1729649, by rfl⟩ : syracuseStep 2306199 = 3459299) B3459299
theorem B2462729 : Blo 2305435 2462729 := bbase (se 2 (by rfl) ⟨923523, by rfl⟩ : syracuseStep 2462729 = 1847047) (by norm_num)
theorem B6567277 : Blo 2305435 6567277 := bstep (se 3 (by rfl) ⟨1231364, by rfl⟩ : syracuseStep 6567277 = 2462729) B2462729
theorem B8756369 : Blo 2305435 8756369 := bstep (se 2 (by rfl) ⟨3283638, by rfl⟩ : syracuseStep 8756369 = 6567277) B6567277
theorem B5837579 : Blo 2305435 5837579 := bstep (se 1 (by rfl) ⟨4378184, by rfl⟩ : syracuseStep 5837579 = 8756369) B8756369
theorem B3891719 : Blo 2305435 3891719 := bstep (se 1 (by rfl) ⟨2918789, by rfl⟩ : syracuseStep 3891719 = 5837579) B5837579
theorem B2594479 : Blo 2305435 2594479 := bstep (se 1 (by rfl) ⟨1945859, by rfl⟩ : syracuseStep 2594479 = 3891719) B3891719
theorem B3459305 : Blo 2305435 3459305 := bstep (se 2 (by rfl) ⟨1297239, by rfl⟩ : syracuseStep 3459305 = 2594479) B2594479
theorem B2306203 : Blo 2305435 2306203 := bstep (se 1 (by rfl) ⟨1729652, by rfl⟩ : syracuseStep 2306203 = 3459305) B3459305
theorem B4437925 : Blo 2305435 4437925 := bbase (se 4 (by rfl) ⟨416055, by rfl⟩ : syracuseStep 4437925 = 832111) (by norm_num)
theorem B23668933 : Blo 2305435 23668933 := bstep (se 4 (by rfl) ⟨2218962, by rfl⟩ : syracuseStep 23668933 = 4437925) B4437925
theorem B31558577 : Blo 2305435 31558577 := bstep (se 2 (by rfl) ⟨11834466, by rfl⟩ : syracuseStep 31558577 = 23668933) B23668933
theorem B84156205 : Blo 2305435 84156205 := bstep (se 3 (by rfl) ⟨15779288, by rfl⟩ : syracuseStep 84156205 = 31558577) B31558577
theorem B112208273 : Blo 2305435 112208273 := bstep (se 2 (by rfl) ⟨42078102, by rfl⟩ : syracuseStep 112208273 = 84156205) B84156205
theorem B74805515 : Blo 2305435 74805515 := bstep (se 1 (by rfl) ⟨56104136, by rfl⟩ : syracuseStep 74805515 = 112208273) B112208273
theorem B49870343 : Blo 2305435 49870343 := bstep (se 1 (by rfl) ⟨37402757, by rfl⟩ : syracuseStep 49870343 = 74805515) B74805515
theorem B33246895 : Blo 2305435 33246895 := bstep (se 1 (by rfl) ⟨24935171, by rfl⟩ : syracuseStep 33246895 = 49870343) B49870343
theorem B44329193 : Blo 2305435 44329193 := bstep (se 2 (by rfl) ⟨16623447, by rfl⟩ : syracuseStep 44329193 = 33246895) B33246895
theorem B29552795 : Blo 2305435 29552795 := bstep (se 1 (by rfl) ⟨22164596, by rfl⟩ : syracuseStep 29552795 = 44329193) B44329193
theorem B19701863 : Blo 2305435 19701863 := bstep (se 1 (by rfl) ⟨14776397, by rfl⟩ : syracuseStep 19701863 = 29552795) B29552795
theorem B13134575 : Blo 2305435 13134575 := bstep (se 1 (by rfl) ⟨9850931, by rfl⟩ : syracuseStep 13134575 = 19701863) B19701863
theorem B8756383 : Blo 2305435 8756383 := bstep (se 1 (by rfl) ⟨6567287, by rfl⟩ : syracuseStep 8756383 = 13134575) B13134575
theorem B11675177 : Blo 2305435 11675177 := bstep (se 2 (by rfl) ⟨4378191, by rfl⟩ : syracuseStep 11675177 = 8756383) B8756383
theorem B7783451 : Blo 2305435 7783451 := bstep (se 1 (by rfl) ⟨5837588, by rfl⟩ : syracuseStep 7783451 = 11675177) B11675177
theorem B5188967 : Blo 2305435 5188967 := bstep (se 1 (by rfl) ⟨3891725, by rfl⟩ : syracuseStep 5188967 = 7783451) B7783451
theorem B3459311 : Blo 2305435 3459311 := bstep (se 1 (by rfl) ⟨2594483, by rfl⟩ : syracuseStep 3459311 = 5188967) B5188967
theorem B2306207 : Blo 2305435 2306207 := bstep (se 1 (by rfl) ⟨1729655, by rfl⟩ : syracuseStep 2306207 = 3459311) B3459311
theorem B3459317 : Blo 2305435 3459317 := bbase (se 5 (by rfl) ⟨162155, by rfl⟩ : syracuseStep 3459317 = 324311) (by norm_num)
theorem B2306211 : Blo 2305435 2306211 := bstep (se 1 (by rfl) ⟨1729658, by rfl⟩ : syracuseStep 2306211 = 3459317) B3459317
theorem B4155877 : Blo 2305435 4155877 := bbase (se 4 (by rfl) ⟨389613, by rfl⟩ : syracuseStep 4155877 = 779227) (by norm_num)
theorem B22164677 : Blo 2305435 22164677 := bstep (se 4 (by rfl) ⟨2077938, by rfl⟩ : syracuseStep 22164677 = 4155877) B4155877
theorem B14776451 : Blo 2305435 14776451 := bstep (se 1 (by rfl) ⟨11082338, by rfl⟩ : syracuseStep 14776451 = 22164677) B22164677
theorem B9850967 : Blo 2305435 9850967 := bstep (se 1 (by rfl) ⟨7388225, by rfl⟩ : syracuseStep 9850967 = 14776451) B14776451
theorem B6567311 : Blo 2305435 6567311 := bstep (se 1 (by rfl) ⟨4925483, by rfl⟩ : syracuseStep 6567311 = 9850967) B9850967
theorem B4378207 : Blo 2305435 4378207 := bstep (se 1 (by rfl) ⟨3283655, by rfl⟩ : syracuseStep 4378207 = 6567311) B6567311
theorem B5837609 : Blo 2305435 5837609 := bstep (se 2 (by rfl) ⟨2189103, by rfl⟩ : syracuseStep 5837609 = 4378207) B4378207
theorem B3891739 : Blo 2305435 3891739 := bstep (se 1 (by rfl) ⟨2918804, by rfl⟩ : syracuseStep 3891739 = 5837609) B5837609
theorem B5188985 : Blo 2305435 5188985 := bstep (se 2 (by rfl) ⟨1945869, by rfl⟩ : syracuseStep 5188985 = 3891739) B3891739
theorem B3459323 : Blo 2305435 3459323 := bstep (se 1 (by rfl) ⟨2594492, by rfl⟩ : syracuseStep 3459323 = 5188985) B5188985
theorem B2306215 : Blo 2305435 2306215 := bstep (se 1 (by rfl) ⟨1729661, by rfl⟩ : syracuseStep 2306215 = 3459323) B3459323
theorem B2594497 : Blo 2305435 2594497 := bbase (se 2 (by rfl) ⟨972936, by rfl⟩ : syracuseStep 2594497 = 1945873) (by norm_num)
theorem B3459329 : Blo 2305435 3459329 := bstep (se 2 (by rfl) ⟨1297248, by rfl⟩ : syracuseStep 3459329 = 2594497) B2594497
theorem B2306219 : Blo 2305435 2306219 := bstep (se 1 (by rfl) ⟨1729664, by rfl⟩ : syracuseStep 2306219 = 3459329) B3459329
theorem B5837629 : Blo 2305435 5837629 := bbase (se 3 (by rfl) ⟨1094555, by rfl⟩ : syracuseStep 5837629 = 2189111) (by norm_num)
theorem B7783505 : Blo 2305435 7783505 := bstep (se 2 (by rfl) ⟨2918814, by rfl⟩ : syracuseStep 7783505 = 5837629) B5837629
theorem B5189003 : Blo 2305435 5189003 := bstep (se 1 (by rfl) ⟨3891752, by rfl⟩ : syracuseStep 5189003 = 7783505) B7783505
theorem B3459335 : Blo 2305435 3459335 := bstep (se 1 (by rfl) ⟨2594501, by rfl⟩ : syracuseStep 3459335 = 5189003) B5189003
theorem B2306223 : Blo 2305435 2306223 := bstep (se 1 (by rfl) ⟨1729667, by rfl⟩ : syracuseStep 2306223 = 3459335) B3459335
theorem B3459341 : Blo 2305435 3459341 := bbase (se 3 (by rfl) ⟨648626, by rfl⟩ : syracuseStep 3459341 = 1297253) (by norm_num)
theorem B2306227 : Blo 2305435 2306227 := bstep (se 1 (by rfl) ⟨1729670, by rfl⟩ : syracuseStep 2306227 = 3459341) B3459341
theorem B5189021 : Blo 2305435 5189021 := bbase (se 3 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 5189021 = 1945883) (by norm_num)
theorem B3459347 : Blo 2305435 3459347 := bstep (se 1 (by rfl) ⟨2594510, by rfl⟩ : syracuseStep 3459347 = 5189021) B5189021
theorem B2306231 : Blo 2305435 2306231 := bstep (se 1 (by rfl) ⟨1729673, by rfl⟩ : syracuseStep 2306231 = 3459347) B3459347
theorem B3891773 : Blo 2305435 3891773 := bbase (se 3 (by rfl) ⟨729707, by rfl⟩ : syracuseStep 3891773 = 1459415) (by norm_num)
theorem B2594515 : Blo 2305435 2594515 := bstep (se 1 (by rfl) ⟨1945886, by rfl⟩ : syracuseStep 2594515 = 3891773) B3891773
theorem B3459353 : Blo 2305435 3459353 := bstep (se 2 (by rfl) ⟨1297257, by rfl⟩ : syracuseStep 3459353 = 2594515) B2594515
theorem B2306235 : Blo 2305435 2306235 := bstep (se 1 (by rfl) ⟨1729676, by rfl⟩ : syracuseStep 2306235 = 3459353) B3459353
theorem B9985477 : Blo 2305435 9985477 := bbase (se 4 (by rfl) ⟨936138, by rfl⟩ : syracuseStep 9985477 = 1872277) (by norm_num)
theorem B13313969 : Blo 2305435 13313969 := bstep (se 2 (by rfl) ⟨4992738, by rfl⟩ : syracuseStep 13313969 = 9985477) B9985477
theorem B8875979 : Blo 2305435 8875979 := bstep (se 1 (by rfl) ⟨6656984, by rfl⟩ : syracuseStep 8875979 = 13313969) B13313969
theorem B5917319 : Blo 2305435 5917319 := bstep (se 1 (by rfl) ⟨4437989, by rfl⟩ : syracuseStep 5917319 = 8875979) B8875979
theorem B3944879 : Blo 2305435 3944879 := bstep (se 1 (by rfl) ⟨2958659, by rfl⟩ : syracuseStep 3944879 = 5917319) B5917319
theorem B2629919 : Blo 2305435 2629919 := bstep (se 1 (by rfl) ⟨1972439, by rfl⟩ : syracuseStep 2629919 = 3944879) B3944879
theorem B7013117 : Blo 2305435 7013117 := bstep (se 3 (by rfl) ⟨1314959, by rfl⟩ : syracuseStep 7013117 = 2629919) B2629919
theorem B4675411 : Blo 2305435 4675411 := bstep (se 1 (by rfl) ⟨3506558, by rfl⟩ : syracuseStep 4675411 = 7013117) B7013117
theorem B6233881 : Blo 2305435 6233881 := bstep (se 2 (by rfl) ⟨2337705, by rfl⟩ : syracuseStep 6233881 = 4675411) B4675411
theorem B8311841 : Blo 2305435 8311841 := bstep (se 2 (by rfl) ⟨3116940, by rfl⟩ : syracuseStep 8311841 = 6233881) B6233881
theorem B5541227 : Blo 2305435 5541227 := bstep (se 1 (by rfl) ⟨4155920, by rfl⟩ : syracuseStep 5541227 = 8311841) B8311841
theorem B3694151 : Blo 2305435 3694151 := bstep (se 1 (by rfl) ⟨2770613, by rfl⟩ : syracuseStep 3694151 = 5541227) B5541227
theorem B2462767 : Blo 2305435 2462767 := bstep (se 1 (by rfl) ⟨1847075, by rfl⟩ : syracuseStep 2462767 = 3694151) B3694151
theorem B13134757 : Blo 2305435 13134757 := bstep (se 4 (by rfl) ⟨1231383, by rfl⟩ : syracuseStep 13134757 = 2462767) B2462767
theorem B17513009 : Blo 2305435 17513009 := bstep (se 2 (by rfl) ⟨6567378, by rfl⟩ : syracuseStep 17513009 = 13134757) B13134757
theorem B11675339 : Blo 2305435 11675339 := bstep (se 1 (by rfl) ⟨8756504, by rfl⟩ : syracuseStep 11675339 = 17513009) B17513009
theorem B7783559 : Blo 2305435 7783559 := bstep (se 1 (by rfl) ⟨5837669, by rfl⟩ : syracuseStep 7783559 = 11675339) B11675339
theorem B5189039 : Blo 2305435 5189039 := bstep (se 1 (by rfl) ⟨3891779, by rfl⟩ : syracuseStep 5189039 = 7783559) B7783559
theorem B3459359 : Blo 2305435 3459359 := bstep (se 1 (by rfl) ⟨2594519, by rfl⟩ : syracuseStep 3459359 = 5189039) B5189039
theorem B2306239 : Blo 2305435 2306239 := bstep (se 1 (by rfl) ⟨1729679, by rfl⟩ : syracuseStep 2306239 = 3459359) B3459359
theorem B3459365 : Blo 2305435 3459365 := bbase (se 4 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 3459365 = 648631) (by norm_num)
theorem B2306243 : Blo 2305435 2306243 := bstep (se 1 (by rfl) ⟨1729682, by rfl⟩ : syracuseStep 2306243 = 3459365) B3459365
theorem B2918845 : Blo 2305435 2918845 := bbase (se 3 (by rfl) ⟨547283, by rfl⟩ : syracuseStep 2918845 = 1094567) (by norm_num)
theorem B3891793 : Blo 2305435 3891793 := bstep (se 2 (by rfl) ⟨1459422, by rfl⟩ : syracuseStep 3891793 = 2918845) B2918845
theorem B5189057 : Blo 2305435 5189057 := bstep (se 2 (by rfl) ⟨1945896, by rfl⟩ : syracuseStep 5189057 = 3891793) B3891793
theorem B3459371 : Blo 2305435 3459371 := bstep (se 1 (by rfl) ⟨2594528, by rfl⟩ : syracuseStep 3459371 = 5189057) B5189057
theorem B2306247 : Blo 2305435 2306247 := bstep (se 1 (by rfl) ⟨1729685, by rfl⟩ : syracuseStep 2306247 = 3459371) B3459371
theorem B2594533 : Blo 2305435 2594533 := bbase (se 4 (by rfl) ⟨243237, by rfl⟩ : syracuseStep 2594533 = 486475) (by norm_num)
theorem B3459377 : Blo 2305435 3459377 := bstep (se 2 (by rfl) ⟨1297266, by rfl⟩ : syracuseStep 3459377 = 2594533) B2594533
theorem B2306251 : Blo 2305435 2306251 := bstep (se 1 (by rfl) ⟨1729688, by rfl⟩ : syracuseStep 2306251 = 3459377) B3459377
theorem B2770633 : Blo 2305435 2770633 := bbase (se 2 (by rfl) ⟨1038987, by rfl⟩ : syracuseStep 2770633 = 2077975) (by norm_num)
theorem B3694177 : Blo 2305435 3694177 := bstep (se 2 (by rfl) ⟨1385316, by rfl⟩ : syracuseStep 3694177 = 2770633) B2770633
theorem B4925569 : Blo 2305435 4925569 := bstep (se 2 (by rfl) ⟨1847088, by rfl⟩ : syracuseStep 4925569 = 3694177) B3694177
theorem B6567425 : Blo 2305435 6567425 := bstep (se 2 (by rfl) ⟨2462784, by rfl⟩ : syracuseStep 6567425 = 4925569) B4925569
theorem B4378283 : Blo 2305435 4378283 := bstep (se 1 (by rfl) ⟨3283712, by rfl⟩ : syracuseStep 4378283 = 6567425) B6567425
theorem B2918855 : Blo 2305435 2918855 := bstep (se 1 (by rfl) ⟨2189141, by rfl⟩ : syracuseStep 2918855 = 4378283) B4378283
theorem B7783613 : Blo 2305435 7783613 := bstep (se 3 (by rfl) ⟨1459427, by rfl⟩ : syracuseStep 7783613 = 2918855) B2918855
theorem B5189075 : Blo 2305435 5189075 := bstep (se 1 (by rfl) ⟨3891806, by rfl⟩ : syracuseStep 5189075 = 7783613) B7783613
theorem B3459383 : Blo 2305435 3459383 := bstep (se 1 (by rfl) ⟨2594537, by rfl⟩ : syracuseStep 3459383 = 5189075) B5189075
theorem B2306255 : Blo 2305435 2306255 := bstep (se 1 (by rfl) ⟨1729691, by rfl⟩ : syracuseStep 2306255 = 3459383) B3459383
theorem B3459389 : Blo 2305435 3459389 := bbase (se 3 (by rfl) ⟨648635, by rfl⟩ : syracuseStep 3459389 = 1297271) (by norm_num)
theorem B2306259 : Blo 2305435 2306259 := bstep (se 1 (by rfl) ⟨1729694, by rfl⟩ : syracuseStep 2306259 = 3459389) B3459389
theorem B5189093 : Blo 2305435 5189093 := bbase (se 4 (by rfl) ⟨486477, by rfl⟩ : syracuseStep 5189093 = 972955) (by norm_num)
theorem B3459395 : Blo 2305435 3459395 := bstep (se 1 (by rfl) ⟨2594546, by rfl⟩ : syracuseStep 3459395 = 5189093) B5189093
theorem B2306263 : Blo 2305435 2306263 := bstep (se 1 (by rfl) ⟨1729697, by rfl⟩ : syracuseStep 2306263 = 3459395) B3459395
theorem B5837741 : Blo 2305435 5837741 := bbase (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) (by norm_num)
theorem B3891827 : Blo 2305435 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B2594551 : Blo 2305435 2594551 := bstep (se 1 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 2594551 = 3891827) B3891827
theorem B3459401 : Blo 2305435 3459401 := bstep (se 2 (by rfl) ⟨1297275, by rfl⟩ : syracuseStep 3459401 = 2594551) B2594551
theorem B2306267 : Blo 2305435 2306267 := bstep (se 1 (by rfl) ⟨1729700, by rfl⟩ : syracuseStep 2306267 = 3459401) B3459401
theorem B7388405 : Blo 2305435 7388405 := bbase (se 5 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 7388405 = 692663) (by norm_num)
theorem B4925603 : Blo 2305435 4925603 := bstep (se 1 (by rfl) ⟨3694202, by rfl⟩ : syracuseStep 4925603 = 7388405) B7388405
theorem B3283735 : Blo 2305435 3283735 := bstep (se 1 (by rfl) ⟨2462801, by rfl⟩ : syracuseStep 3283735 = 4925603) B4925603
theorem B4378313 : Blo 2305435 4378313 := bstep (se 2 (by rfl) ⟨1641867, by rfl⟩ : syracuseStep 4378313 = 3283735) B3283735
theorem B11675501 : Blo 2305435 11675501 := bstep (se 3 (by rfl) ⟨2189156, by rfl⟩ : syracuseStep 11675501 = 4378313) B4378313
theorem B7783667 : Blo 2305435 7783667 := bstep (se 1 (by rfl) ⟨5837750, by rfl⟩ : syracuseStep 7783667 = 11675501) B11675501
theorem B5189111 : Blo 2305435 5189111 := bstep (se 1 (by rfl) ⟨3891833, by rfl⟩ : syracuseStep 5189111 = 7783667) B7783667
theorem B3459407 : Blo 2305435 3459407 := bstep (se 1 (by rfl) ⟨2594555, by rfl⟩ : syracuseStep 3459407 = 5189111) B5189111
theorem B2306271 : Blo 2305435 2306271 := bstep (se 1 (by rfl) ⟨1729703, by rfl⟩ : syracuseStep 2306271 = 3459407) B3459407
theorem B3459413 : Blo 2305435 3459413 := bbase (se 10 (by rfl) ⟨5067, by rfl⟩ : syracuseStep 3459413 = 10135) (by norm_num)
theorem B2306275 : Blo 2305435 2306275 := bstep (se 1 (by rfl) ⟨1729706, by rfl⟩ : syracuseStep 2306275 = 3459413) B3459413
theorem B6567493 : Blo 2305435 6567493 := bbase (se 4 (by rfl) ⟨615702, by rfl⟩ : syracuseStep 6567493 = 1231405) (by norm_num)
theorem B8756657 : Blo 2305435 8756657 := bstep (se 2 (by rfl) ⟨3283746, by rfl⟩ : syracuseStep 8756657 = 6567493) B6567493
theorem B5837771 : Blo 2305435 5837771 := bstep (se 1 (by rfl) ⟨4378328, by rfl⟩ : syracuseStep 5837771 = 8756657) B8756657
theorem B3891847 : Blo 2305435 3891847 := bstep (se 1 (by rfl) ⟨2918885, by rfl⟩ : syracuseStep 3891847 = 5837771) B5837771
theorem B5189129 : Blo 2305435 5189129 := bstep (se 2 (by rfl) ⟨1945923, by rfl⟩ : syracuseStep 5189129 = 3891847) B3891847
theorem B3459419 : Blo 2305435 3459419 := bstep (se 1 (by rfl) ⟨2594564, by rfl⟩ : syracuseStep 3459419 = 5189129) B5189129
theorem B2306279 : Blo 2305435 2306279 := bstep (se 1 (by rfl) ⟨1729709, by rfl⟩ : syracuseStep 2306279 = 3459419) B3459419
theorem B2594569 : Blo 2305435 2594569 := bbase (se 2 (by rfl) ⟨972963, by rfl⟩ : syracuseStep 2594569 = 1945927) (by norm_num)
theorem B3459425 : Blo 2305435 3459425 := bstep (se 2 (by rfl) ⟨1297284, by rfl⟩ : syracuseStep 3459425 = 2594569) B2594569
theorem B2306283 : Blo 2305435 2306283 := bstep (se 1 (by rfl) ⟨1729712, by rfl⟩ : syracuseStep 2306283 = 3459425) B3459425
theorem B2629973 : Blo 2305435 2629973 := bbase (se 10 (by rfl) ⟨3852, by rfl⟩ : syracuseStep 2629973 = 7705) (by norm_num)
theorem B7013261 : Blo 2305435 7013261 := bstep (se 3 (by rfl) ⟨1314986, by rfl⟩ : syracuseStep 7013261 = 2629973) B2629973
theorem B18702029 : Blo 2305435 18702029 := bstep (se 3 (by rfl) ⟨3506630, by rfl⟩ : syracuseStep 18702029 = 7013261) B7013261
theorem B12468019 : Blo 2305435 12468019 := bstep (se 1 (by rfl) ⟨9351014, by rfl⟩ : syracuseStep 12468019 = 18702029) B18702029
theorem B16624025 : Blo 2305435 16624025 := bstep (se 2 (by rfl) ⟨6234009, by rfl⟩ : syracuseStep 16624025 = 12468019) B12468019
theorem B11082683 : Blo 2305435 11082683 := bstep (se 1 (by rfl) ⟨8312012, by rfl⟩ : syracuseStep 11082683 = 16624025) B16624025
theorem B29553821 : Blo 2305435 29553821 := bstep (se 3 (by rfl) ⟨5541341, by rfl⟩ : syracuseStep 29553821 = 11082683) B11082683
theorem B19702547 : Blo 2305435 19702547 := bstep (se 1 (by rfl) ⟨14776910, by rfl⟩ : syracuseStep 19702547 = 29553821) B29553821
theorem B13135031 : Blo 2305435 13135031 := bstep (se 1 (by rfl) ⟨9851273, by rfl⟩ : syracuseStep 13135031 = 19702547) B19702547
theorem B8756687 : Blo 2305435 8756687 := bstep (se 1 (by rfl) ⟨6567515, by rfl⟩ : syracuseStep 8756687 = 13135031) B13135031
theorem B5837791 : Blo 2305435 5837791 := bstep (se 1 (by rfl) ⟨4378343, by rfl⟩ : syracuseStep 5837791 = 8756687) B8756687
theorem B7783721 : Blo 2305435 7783721 := bstep (se 2 (by rfl) ⟨2918895, by rfl⟩ : syracuseStep 7783721 = 5837791) B5837791
theorem B5189147 : Blo 2305435 5189147 := bstep (se 1 (by rfl) ⟨3891860, by rfl⟩ : syracuseStep 5189147 = 7783721) B7783721
theorem B3459431 : Blo 2305435 3459431 := bstep (se 1 (by rfl) ⟨2594573, by rfl⟩ : syracuseStep 3459431 = 5189147) B5189147
theorem B2306287 : Blo 2305435 2306287 := bstep (se 1 (by rfl) ⟨1729715, by rfl⟩ : syracuseStep 2306287 = 3459431) B3459431
theorem B3459437 : Blo 2305435 3459437 := bbase (se 3 (by rfl) ⟨648644, by rfl⟩ : syracuseStep 3459437 = 1297289) (by norm_num)
theorem B2306291 : Blo 2305435 2306291 := bstep (se 1 (by rfl) ⟨1729718, by rfl⟩ : syracuseStep 2306291 = 3459437) B3459437
theorem B5189165 : Blo 2305435 5189165 := bbase (se 3 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 5189165 = 1945937) (by norm_num)
theorem B3459443 : Blo 2305435 3459443 := bstep (se 1 (by rfl) ⟨2594582, by rfl⟩ : syracuseStep 3459443 = 5189165) B5189165
theorem B2306295 : Blo 2305435 2306295 := bstep (se 1 (by rfl) ⟨1729721, by rfl⟩ : syracuseStep 2306295 = 3459443) B3459443
theorem B5130037 : Blo 2305435 5130037 := bbase (se 5 (by rfl) ⟨240470, by rfl⟩ : syracuseStep 5130037 = 480941) (by norm_num)
theorem B6840049 : Blo 2305435 6840049 := bstep (se 2 (by rfl) ⟨2565018, by rfl⟩ : syracuseStep 6840049 = 5130037) B5130037
theorem B9120065 : Blo 2305435 9120065 := bstep (se 2 (by rfl) ⟨3420024, by rfl⟩ : syracuseStep 9120065 = 6840049) B6840049
theorem B24320173 : Blo 2305435 24320173 := bstep (se 3 (by rfl) ⟨4560032, by rfl⟩ : syracuseStep 24320173 = 9120065) B9120065
theorem B32426897 : Blo 2305435 32426897 := bstep (se 2 (by rfl) ⟨12160086, by rfl⟩ : syracuseStep 32426897 = 24320173) B24320173
theorem B86471725 : Blo 2305435 86471725 := bstep (se 3 (by rfl) ⟨16213448, by rfl⟩ : syracuseStep 86471725 = 32426897) B32426897
theorem B115295633 : Blo 2305435 115295633 := bstep (se 2 (by rfl) ⟨43235862, by rfl⟩ : syracuseStep 115295633 = 86471725) B86471725
theorem B76863755 : Blo 2305435 76863755 := bstep (se 1 (by rfl) ⟨57647816, by rfl⟩ : syracuseStep 76863755 = 115295633) B115295633
theorem B51242503 : Blo 2305435 51242503 := bstep (se 1 (by rfl) ⟨38431877, by rfl⟩ : syracuseStep 51242503 = 76863755) B76863755
theorem B68323337 : Blo 2305435 68323337 := bstep (se 2 (by rfl) ⟨25621251, by rfl⟩ : syracuseStep 68323337 = 51242503) B51242503
theorem B45548891 : Blo 2305435 45548891 := bstep (se 1 (by rfl) ⟨34161668, by rfl⟩ : syracuseStep 45548891 = 68323337) B68323337
theorem B30365927 : Blo 2305435 30365927 := bstep (se 1 (by rfl) ⟨22774445, by rfl⟩ : syracuseStep 30365927 = 45548891) B45548891
theorem B20243951 : Blo 2305435 20243951 := bstep (se 1 (by rfl) ⟨15182963, by rfl⟩ : syracuseStep 20243951 = 30365927) B30365927
theorem B13495967 : Blo 2305435 13495967 := bstep (se 1 (by rfl) ⟨10121975, by rfl⟩ : syracuseStep 13495967 = 20243951) B20243951
theorem B8997311 : Blo 2305435 8997311 := bstep (se 1 (by rfl) ⟨6747983, by rfl⟩ : syracuseStep 8997311 = 13495967) B13495967
theorem B5998207 : Blo 2305435 5998207 := bstep (se 1 (by rfl) ⟨4498655, by rfl⟩ : syracuseStep 5998207 = 8997311) B8997311
theorem B7997609 : Blo 2305435 7997609 := bstep (se 2 (by rfl) ⟨2999103, by rfl⟩ : syracuseStep 7997609 = 5998207) B5998207
theorem B5331739 : Blo 2305435 5331739 := bstep (se 1 (by rfl) ⟨3998804, by rfl⟩ : syracuseStep 5331739 = 7997609) B7997609
theorem B7108985 : Blo 2305435 7108985 := bstep (se 2 (by rfl) ⟨2665869, by rfl⟩ : syracuseStep 7108985 = 5331739) B5331739
theorem B18957293 : Blo 2305435 18957293 := bstep (se 3 (by rfl) ⟨3554492, by rfl⟩ : syracuseStep 18957293 = 7108985) B7108985
theorem B12638195 : Blo 2305435 12638195 := bstep (se 1 (by rfl) ⟨9478646, by rfl⟩ : syracuseStep 12638195 = 18957293) B18957293
theorem B8425463 : Blo 2305435 8425463 := bstep (se 1 (by rfl) ⟨6319097, by rfl⟩ : syracuseStep 8425463 = 12638195) B12638195
theorem B22467901 : Blo 2305435 22467901 := bstep (se 3 (by rfl) ⟨4212731, by rfl⟩ : syracuseStep 22467901 = 8425463) B8425463
theorem B29957201 : Blo 2305435 29957201 := bstep (se 2 (by rfl) ⟨11233950, by rfl⟩ : syracuseStep 29957201 = 22467901) B22467901
theorem B19971467 : Blo 2305435 19971467 := bstep (se 1 (by rfl) ⟨14978600, by rfl⟩ : syracuseStep 19971467 = 29957201) B29957201
theorem B13314311 : Blo 2305435 13314311 := bstep (se 1 (by rfl) ⟨9985733, by rfl⟩ : syracuseStep 13314311 = 19971467) B19971467
theorem B8876207 : Blo 2305435 8876207 := bstep (se 1 (by rfl) ⟨6657155, by rfl⟩ : syracuseStep 8876207 = 13314311) B13314311
theorem B5917471 : Blo 2305435 5917471 := bstep (se 1 (by rfl) ⟨4438103, by rfl⟩ : syracuseStep 5917471 = 8876207) B8876207
theorem B126239381 : Blo 2305435 126239381 := bstep (se 6 (by rfl) ⟨2958735, by rfl⟩ : syracuseStep 126239381 = 5917471) B5917471
theorem B84159587 : Blo 2305435 84159587 := bstep (se 1 (by rfl) ⟨63119690, by rfl⟩ : syracuseStep 84159587 = 126239381) B126239381
theorem B56106391 : Blo 2305435 56106391 := bstep (se 1 (by rfl) ⟨42079793, by rfl⟩ : syracuseStep 56106391 = 84159587) B84159587
theorem B74808521 : Blo 2305435 74808521 := bstep (se 2 (by rfl) ⟨28053195, by rfl⟩ : syracuseStep 74808521 = 56106391) B56106391
theorem B49872347 : Blo 2305435 49872347 := bstep (se 1 (by rfl) ⟨37404260, by rfl⟩ : syracuseStep 49872347 = 74808521) B74808521
theorem B33248231 : Blo 2305435 33248231 := bstep (se 1 (by rfl) ⟨24936173, by rfl⟩ : syracuseStep 33248231 = 49872347) B49872347
theorem B22165487 : Blo 2305435 22165487 := bstep (se 1 (by rfl) ⟨16624115, by rfl⟩ : syracuseStep 22165487 = 33248231) B33248231
theorem B14776991 : Blo 2305435 14776991 := bstep (se 1 (by rfl) ⟨11082743, by rfl⟩ : syracuseStep 14776991 = 22165487) B22165487
theorem B9851327 : Blo 2305435 9851327 := bstep (se 1 (by rfl) ⟨7388495, by rfl⟩ : syracuseStep 9851327 = 14776991) B14776991
theorem B6567551 : Blo 2305435 6567551 := bstep (se 1 (by rfl) ⟨4925663, by rfl⟩ : syracuseStep 6567551 = 9851327) B9851327
theorem B4378367 : Blo 2305435 4378367 := bstep (se 1 (by rfl) ⟨3283775, by rfl⟩ : syracuseStep 4378367 = 6567551) B6567551
theorem B2918911 : Blo 2305435 2918911 := bstep (se 1 (by rfl) ⟨2189183, by rfl⟩ : syracuseStep 2918911 = 4378367) B4378367
theorem B3891881 : Blo 2305435 3891881 := bstep (se 2 (by rfl) ⟨1459455, by rfl⟩ : syracuseStep 3891881 = 2918911) B2918911
theorem B2594587 : Blo 2305435 2594587 := bstep (se 1 (by rfl) ⟨1945940, by rfl⟩ : syracuseStep 2594587 = 3891881) B3891881
theorem B3459449 : Blo 2305435 3459449 := bstep (se 2 (by rfl) ⟨1297293, by rfl⟩ : syracuseStep 3459449 = 2594587) B2594587
theorem B2306299 : Blo 2305435 2306299 := bstep (se 1 (by rfl) ⟨1729724, by rfl⟩ : syracuseStep 2306299 = 3459449) B3459449
theorem B3694253 : Blo 2305435 3694253 := bbase (se 3 (by rfl) ⟨692672, by rfl⟩ : syracuseStep 3694253 = 1385345) (by norm_num)
theorem B39405365 : Blo 2305435 39405365 := bstep (se 5 (by rfl) ⟨1847126, by rfl⟩ : syracuseStep 39405365 = 3694253) B3694253
theorem B26270243 : Blo 2305435 26270243 := bstep (se 1 (by rfl) ⟨19702682, by rfl⟩ : syracuseStep 26270243 = 39405365) B39405365
theorem B17513495 : Blo 2305435 17513495 := bstep (se 1 (by rfl) ⟨13135121, by rfl⟩ : syracuseStep 17513495 = 26270243) B26270243
theorem B11675663 : Blo 2305435 11675663 := bstep (se 1 (by rfl) ⟨8756747, by rfl⟩ : syracuseStep 11675663 = 17513495) B17513495
theorem B7783775 : Blo 2305435 7783775 := bstep (se 1 (by rfl) ⟨5837831, by rfl⟩ : syracuseStep 7783775 = 11675663) B11675663
theorem B5189183 : Blo 2305435 5189183 := bstep (se 1 (by rfl) ⟨3891887, by rfl⟩ : syracuseStep 5189183 = 7783775) B7783775
theorem B3459455 : Blo 2305435 3459455 := bstep (se 1 (by rfl) ⟨2594591, by rfl⟩ : syracuseStep 3459455 = 5189183) B5189183
theorem B2306303 : Blo 2305435 2306303 := bstep (se 1 (by rfl) ⟨1729727, by rfl⟩ : syracuseStep 2306303 = 3459455) B3459455
theorem B3459461 : Blo 2305435 3459461 := bbase (se 4 (by rfl) ⟨324324, by rfl⟩ : syracuseStep 3459461 = 648649) (by norm_num)
theorem B2306307 : Blo 2305435 2306307 := bstep (se 1 (by rfl) ⟨1729730, by rfl⟩ : syracuseStep 2306307 = 3459461) B3459461
theorem B3891901 : Blo 2305435 3891901 := bbase (se 3 (by rfl) ⟨729731, by rfl⟩ : syracuseStep 3891901 = 1459463) (by norm_num)
theorem B5189201 : Blo 2305435 5189201 := bstep (se 2 (by rfl) ⟨1945950, by rfl⟩ : syracuseStep 5189201 = 3891901) B3891901
theorem B3459467 : Blo 2305435 3459467 := bstep (se 1 (by rfl) ⟨2594600, by rfl⟩ : syracuseStep 3459467 = 5189201) B5189201
theorem B2306311 : Blo 2305435 2306311 := bstep (se 1 (by rfl) ⟨1729733, by rfl⟩ : syracuseStep 2306311 = 3459467) B3459467
theorem B2594605 : Blo 2305435 2594605 := bbase (se 3 (by rfl) ⟨486488, by rfl⟩ : syracuseStep 2594605 = 972977) (by norm_num)
theorem B3459473 : Blo 2305435 3459473 := bstep (se 2 (by rfl) ⟨1297302, by rfl⟩ : syracuseStep 3459473 = 2594605) B2594605
theorem B2306315 : Blo 2305435 2306315 := bstep (se 1 (by rfl) ⟨1729736, by rfl⟩ : syracuseStep 2306315 = 3459473) B3459473
theorem B7783829 : Blo 2305435 7783829 := bbase (se 6 (by rfl) ⟨182433, by rfl⟩ : syracuseStep 7783829 = 364867) (by norm_num)
theorem B5189219 : Blo 2305435 5189219 := bstep (se 1 (by rfl) ⟨3891914, by rfl⟩ : syracuseStep 5189219 = 7783829) B7783829
theorem B3459479 : Blo 2305435 3459479 := bstep (se 1 (by rfl) ⟨2594609, by rfl⟩ : syracuseStep 3459479 = 5189219) B5189219
theorem B2306319 : Blo 2305435 2306319 := bstep (se 1 (by rfl) ⟨1729739, by rfl⟩ : syracuseStep 2306319 = 3459479) B3459479
theorem B3459485 : Blo 2305435 3459485 := bbase (se 3 (by rfl) ⟨648653, by rfl⟩ : syracuseStep 3459485 = 1297307) (by norm_num)
theorem B2306323 : Blo 2305435 2306323 := bstep (se 1 (by rfl) ⟨1729742, by rfl⟩ : syracuseStep 2306323 = 3459485) B3459485
theorem B5189237 : Blo 2305435 5189237 := bbase (se 5 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 5189237 = 486491) (by norm_num)
theorem B3459491 : Blo 2305435 3459491 := bstep (se 1 (by rfl) ⟨2594618, by rfl⟩ : syracuseStep 3459491 = 5189237) B5189237
theorem B2306327 : Blo 2305435 2306327 := bstep (se 1 (by rfl) ⟨1729745, by rfl⟩ : syracuseStep 2306327 = 3459491) B3459491
theorem B7388597 : Blo 2305435 7388597 := bbase (se 5 (by rfl) ⟨346340, by rfl⟩ : syracuseStep 7388597 = 692681) (by norm_num)
theorem B19702925 : Blo 2305435 19702925 := bstep (se 3 (by rfl) ⟨3694298, by rfl⟩ : syracuseStep 19702925 = 7388597) B7388597
theorem B13135283 : Blo 2305435 13135283 := bstep (se 1 (by rfl) ⟨9851462, by rfl⟩ : syracuseStep 13135283 = 19702925) B19702925
theorem B8756855 : Blo 2305435 8756855 := bstep (se 1 (by rfl) ⟨6567641, by rfl⟩ : syracuseStep 8756855 = 13135283) B13135283
theorem B5837903 : Blo 2305435 5837903 := bstep (se 1 (by rfl) ⟨4378427, by rfl⟩ : syracuseStep 5837903 = 8756855) B8756855
theorem B3891935 : Blo 2305435 3891935 := bstep (se 1 (by rfl) ⟨2918951, by rfl⟩ : syracuseStep 3891935 = 5837903) B5837903
theorem B2594623 : Blo 2305435 2594623 := bstep (se 1 (by rfl) ⟨1945967, by rfl⟩ : syracuseStep 2594623 = 3891935) B3891935
theorem B3459497 : Blo 2305435 3459497 := bstep (se 2 (by rfl) ⟨1297311, by rfl⟩ : syracuseStep 3459497 = 2594623) B2594623
theorem B2306331 : Blo 2305435 2306331 := bstep (se 1 (by rfl) ⟨1729748, by rfl⟩ : syracuseStep 2306331 = 3459497) B3459497
theorem B8756869 : Blo 2305435 8756869 := bbase (se 4 (by rfl) ⟨820956, by rfl⟩ : syracuseStep 8756869 = 1641913) (by norm_num)
theorem B11675825 : Blo 2305435 11675825 := bstep (se 2 (by rfl) ⟨4378434, by rfl⟩ : syracuseStep 11675825 = 8756869) B8756869
theorem B7783883 : Blo 2305435 7783883 := bstep (se 1 (by rfl) ⟨5837912, by rfl⟩ : syracuseStep 7783883 = 11675825) B11675825
theorem B5189255 : Blo 2305435 5189255 := bstep (se 1 (by rfl) ⟨3891941, by rfl⟩ : syracuseStep 5189255 = 7783883) B7783883
theorem B3459503 : Blo 2305435 3459503 := bstep (se 1 (by rfl) ⟨2594627, by rfl⟩ : syracuseStep 3459503 = 5189255) B5189255
theorem B2306335 : Blo 2305435 2306335 := bstep (se 1 (by rfl) ⟨1729751, by rfl⟩ : syracuseStep 2306335 = 3459503) B3459503
theorem B3459509 : Blo 2305435 3459509 := bbase (se 5 (by rfl) ⟨162164, by rfl⟩ : syracuseStep 3459509 = 324329) (by norm_num)
theorem B2306339 : Blo 2305435 2306339 := bstep (se 1 (by rfl) ⟨1729754, by rfl⟩ : syracuseStep 2306339 = 3459509) B3459509
theorem B5837933 : Blo 2305435 5837933 := bbase (se 3 (by rfl) ⟨1094612, by rfl⟩ : syracuseStep 5837933 = 2189225) (by norm_num)
theorem B3891955 : Blo 2305435 3891955 := bstep (se 1 (by rfl) ⟨2918966, by rfl⟩ : syracuseStep 3891955 = 5837933) B5837933
theorem B5189273 : Blo 2305435 5189273 := bstep (se 2 (by rfl) ⟨1945977, by rfl⟩ : syracuseStep 5189273 = 3891955) B3891955
theorem B3459515 : Blo 2305435 3459515 := bstep (se 1 (by rfl) ⟨2594636, by rfl⟩ : syracuseStep 3459515 = 5189273) B5189273
theorem B2306343 : Blo 2305435 2306343 := bstep (se 1 (by rfl) ⟨1729757, by rfl⟩ : syracuseStep 2306343 = 3459515) B3459515
theorem B2594641 : Blo 2305435 2594641 := bbase (se 2 (by rfl) ⟨972990, by rfl⟩ : syracuseStep 2594641 = 1945981) (by norm_num)
theorem B3459521 : Blo 2305435 3459521 := bstep (se 2 (by rfl) ⟨1297320, by rfl⟩ : syracuseStep 3459521 = 2594641) B2594641
theorem B2306347 : Blo 2305435 2306347 := bstep (se 1 (by rfl) ⟨1729760, by rfl⟩ : syracuseStep 2306347 = 3459521) B3459521
theorem B2999173 : Blo 2305435 2999173 := bbase (se 4 (by rfl) ⟨281172, by rfl⟩ : syracuseStep 2999173 = 562345) (by norm_num)
theorem B3998897 : Blo 2305435 3998897 := bstep (se 2 (by rfl) ⟨1499586, by rfl⟩ : syracuseStep 3998897 = 2999173) B2999173
theorem B2665931 : Blo 2305435 2665931 := bstep (se 1 (by rfl) ⟨1999448, by rfl⟩ : syracuseStep 2665931 = 3998897) B3998897
theorem B7109149 : Blo 2305435 7109149 := bstep (se 3 (by rfl) ⟨1332965, by rfl⟩ : syracuseStep 7109149 = 2665931) B2665931
theorem B9478865 : Blo 2305435 9478865 := bstep (se 2 (by rfl) ⟨3554574, by rfl⟩ : syracuseStep 9478865 = 7109149) B7109149
theorem B6319243 : Blo 2305435 6319243 := bstep (se 1 (by rfl) ⟨4739432, by rfl⟩ : syracuseStep 6319243 = 9478865) B9478865
theorem B8425657 : Blo 2305435 8425657 := bstep (se 2 (by rfl) ⟨3159621, by rfl⟩ : syracuseStep 8425657 = 6319243) B6319243
theorem B11234209 : Blo 2305435 11234209 := bstep (se 2 (by rfl) ⟨4212828, by rfl⟩ : syracuseStep 11234209 = 8425657) B8425657
theorem B14978945 : Blo 2305435 14978945 := bstep (se 2 (by rfl) ⟨5617104, by rfl⟩ : syracuseStep 14978945 = 11234209) B11234209
theorem B9985963 : Blo 2305435 9985963 := bstep (se 1 (by rfl) ⟨7489472, by rfl⟩ : syracuseStep 9985963 = 14978945) B14978945
theorem B13314617 : Blo 2305435 13314617 := bstep (se 2 (by rfl) ⟨4992981, by rfl⟩ : syracuseStep 13314617 = 9985963) B9985963
theorem B8876411 : Blo 2305435 8876411 := bstep (se 1 (by rfl) ⟨6657308, by rfl⟩ : syracuseStep 8876411 = 13314617) B13314617
theorem B5917607 : Blo 2305435 5917607 := bstep (se 1 (by rfl) ⟨4438205, by rfl⟩ : syracuseStep 5917607 = 8876411) B8876411
theorem B3945071 : Blo 2305435 3945071 := bstep (se 1 (by rfl) ⟨2958803, by rfl⟩ : syracuseStep 3945071 = 5917607) B5917607
theorem B10520189 : Blo 2305435 10520189 := bstep (se 3 (by rfl) ⟨1972535, by rfl⟩ : syracuseStep 10520189 = 3945071) B3945071
theorem B7013459 : Blo 2305435 7013459 := bstep (se 1 (by rfl) ⟨5260094, by rfl⟩ : syracuseStep 7013459 = 10520189) B10520189
theorem B4675639 : Blo 2305435 4675639 := bstep (se 1 (by rfl) ⟨3506729, by rfl⟩ : syracuseStep 4675639 = 7013459) B7013459
theorem B6234185 : Blo 2305435 6234185 := bstep (se 2 (by rfl) ⟨2337819, by rfl⟩ : syracuseStep 6234185 = 4675639) B4675639
theorem B4156123 : Blo 2305435 4156123 := bstep (se 1 (by rfl) ⟨3117092, by rfl⟩ : syracuseStep 4156123 = 6234185) B6234185
theorem B5541497 : Blo 2305435 5541497 := bstep (se 2 (by rfl) ⟨2078061, by rfl⟩ : syracuseStep 5541497 = 4156123) B4156123
theorem B3694331 : Blo 2305435 3694331 := bstep (se 1 (by rfl) ⟨2770748, by rfl⟩ : syracuseStep 3694331 = 5541497) B5541497
theorem B2462887 : Blo 2305435 2462887 := bstep (se 1 (by rfl) ⟨1847165, by rfl⟩ : syracuseStep 2462887 = 3694331) B3694331
theorem B3283849 : Blo 2305435 3283849 := bstep (se 2 (by rfl) ⟨1231443, by rfl⟩ : syracuseStep 3283849 = 2462887) B2462887
theorem B4378465 : Blo 2305435 4378465 := bstep (se 2 (by rfl) ⟨1641924, by rfl⟩ : syracuseStep 4378465 = 3283849) B3283849
theorem B5837953 : Blo 2305435 5837953 := bstep (se 2 (by rfl) ⟨2189232, by rfl⟩ : syracuseStep 5837953 = 4378465) B4378465
theorem B7783937 : Blo 2305435 7783937 := bstep (se 2 (by rfl) ⟨2918976, by rfl⟩ : syracuseStep 7783937 = 5837953) B5837953
theorem B5189291 : Blo 2305435 5189291 := bstep (se 1 (by rfl) ⟨3891968, by rfl⟩ : syracuseStep 5189291 = 7783937) B7783937
theorem B3459527 : Blo 2305435 3459527 := bstep (se 1 (by rfl) ⟨2594645, by rfl⟩ : syracuseStep 3459527 = 5189291) B5189291
theorem B2306351 : Blo 2305435 2306351 := bstep (se 1 (by rfl) ⟨1729763, by rfl⟩ : syracuseStep 2306351 = 3459527) B3459527
theorem B3459533 : Blo 2305435 3459533 := bbase (se 3 (by rfl) ⟨648662, by rfl⟩ : syracuseStep 3459533 = 1297325) (by norm_num)
theorem B2306355 : Blo 2305435 2306355 := bstep (se 1 (by rfl) ⟨1729766, by rfl⟩ : syracuseStep 2306355 = 3459533) B3459533
theorem B5189309 : Blo 2305435 5189309 := bbase (se 3 (by rfl) ⟨972995, by rfl⟩ : syracuseStep 5189309 = 1945991) (by norm_num)
theorem B3459539 : Blo 2305435 3459539 := bstep (se 1 (by rfl) ⟨2594654, by rfl⟩ : syracuseStep 3459539 = 5189309) B5189309
theorem B2306359 : Blo 2305435 2306359 := bstep (se 1 (by rfl) ⟨1729769, by rfl⟩ : syracuseStep 2306359 = 3459539) B3459539
theorem B3891989 : Blo 2305435 3891989 := bbase (se 6 (by rfl) ⟨91218, by rfl⟩ : syracuseStep 3891989 = 182437) (by norm_num)
theorem B2594659 : Blo 2305435 2594659 := bstep (se 1 (by rfl) ⟨1945994, by rfl⟩ : syracuseStep 2594659 = 3891989) B3891989
theorem B3459545 : Blo 2305435 3459545 := bstep (se 2 (by rfl) ⟨1297329, by rfl⟩ : syracuseStep 3459545 = 2594659) B2594659
theorem B2306363 : Blo 2305435 2306363 := bstep (se 1 (by rfl) ⟨1729772, by rfl⟩ : syracuseStep 2306363 = 3459545) B3459545
theorem B18702677 : Blo 2305435 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B49873805 : Blo 2305435 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B33249203 : Blo 2305435 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B22166135 : Blo 2305435 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B14777423 : Blo 2305435 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B9851615 : Blo 2305435 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B6567743 : Blo 2305435 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B17513981 : Blo 2305435 17513981 := bstep (se 3 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 17513981 = 6567743) B6567743
theorem B11675987 : Blo 2305435 11675987 := bstep (se 1 (by rfl) ⟨8756990, by rfl⟩ : syracuseStep 11675987 = 17513981) B17513981
theorem B7783991 : Blo 2305435 7783991 := bstep (se 1 (by rfl) ⟨5837993, by rfl⟩ : syracuseStep 7783991 = 11675987) B11675987
theorem B5189327 : Blo 2305435 5189327 := bstep (se 1 (by rfl) ⟨3891995, by rfl⟩ : syracuseStep 5189327 = 7783991) B7783991
theorem B3459551 : Blo 2305435 3459551 := bstep (se 1 (by rfl) ⟨2594663, by rfl⟩ : syracuseStep 3459551 = 5189327) B5189327
theorem B2306367 : Blo 2305435 2306367 := bstep (se 1 (by rfl) ⟨1729775, by rfl⟩ : syracuseStep 2306367 = 3459551) B3459551
theorem B3459557 : Blo 2305435 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B2306371 : Blo 2305435 2306371 := bstep (se 1 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 2306371 = 3459557) B3459557
theorem B2770777 : Blo 2305435 2770777 := bbase (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) (by norm_num)
theorem B14777477 : Blo 2305435 14777477 := bstep (se 4 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 14777477 = 2770777) B2770777
theorem B9851651 : Blo 2305435 9851651 := bstep (se 1 (by rfl) ⟨7388738, by rfl⟩ : syracuseStep 9851651 = 14777477) B14777477
theorem B6567767 : Blo 2305435 6567767 := bstep (se 1 (by rfl) ⟨4925825, by rfl⟩ : syracuseStep 6567767 = 9851651) B9851651
theorem B4378511 : Blo 2305435 4378511 := bstep (se 1 (by rfl) ⟨3283883, by rfl⟩ : syracuseStep 4378511 = 6567767) B6567767
theorem B2919007 : Blo 2305435 2919007 := bstep (se 1 (by rfl) ⟨2189255, by rfl⟩ : syracuseStep 2919007 = 4378511) B4378511
theorem B3892009 : Blo 2305435 3892009 := bstep (se 2 (by rfl) ⟨1459503, by rfl⟩ : syracuseStep 3892009 = 2919007) B2919007
theorem B5189345 : Blo 2305435 5189345 := bstep (se 2 (by rfl) ⟨1946004, by rfl⟩ : syracuseStep 5189345 = 3892009) B3892009
theorem B3459563 : Blo 2305435 3459563 := bstep (se 1 (by rfl) ⟨2594672, by rfl⟩ : syracuseStep 3459563 = 5189345) B5189345
theorem B2306375 : Blo 2305435 2306375 := bstep (se 1 (by rfl) ⟨1729781, by rfl⟩ : syracuseStep 2306375 = 3459563) B3459563
theorem B2594677 : Blo 2305435 2594677 := bbase (se 5 (by rfl) ⟨121625, by rfl⟩ : syracuseStep 2594677 = 243251) (by norm_num)
theorem B3459569 : Blo 2305435 3459569 := bstep (se 2 (by rfl) ⟨1297338, by rfl⟩ : syracuseStep 3459569 = 2594677) B2594677
theorem B2306379 : Blo 2305435 2306379 := bstep (se 1 (by rfl) ⟨1729784, by rfl⟩ : syracuseStep 2306379 = 3459569) B3459569
theorem B2919017 : Blo 2305435 2919017 := bbase (se 2 (by rfl) ⟨1094631, by rfl⟩ : syracuseStep 2919017 = 2189263) (by norm_num)
theorem B7784045 : Blo 2305435 7784045 := bstep (se 3 (by rfl) ⟨1459508, by rfl⟩ : syracuseStep 7784045 = 2919017) B2919017
theorem B5189363 : Blo 2305435 5189363 := bstep (se 1 (by rfl) ⟨3892022, by rfl⟩ : syracuseStep 5189363 = 7784045) B7784045
theorem B3459575 : Blo 2305435 3459575 := bstep (se 1 (by rfl) ⟨2594681, by rfl⟩ : syracuseStep 3459575 = 5189363) B5189363
theorem B2306383 : Blo 2305435 2306383 := bstep (se 1 (by rfl) ⟨1729787, by rfl⟩ : syracuseStep 2306383 = 3459575) B3459575
theorem B3459581 : Blo 2305435 3459581 := bbase (se 3 (by rfl) ⟨648671, by rfl⟩ : syracuseStep 3459581 = 1297343) (by norm_num)
theorem B2306387 : Blo 2305435 2306387 := bstep (se 1 (by rfl) ⟨1729790, by rfl⟩ : syracuseStep 2306387 = 3459581) B3459581
theorem B5189381 : Blo 2305435 5189381 := bbase (se 4 (by rfl) ⟨486504, by rfl⟩ : syracuseStep 5189381 = 973009) (by norm_num)
theorem B3459587 : Blo 2305435 3459587 := bstep (se 1 (by rfl) ⟨2594690, by rfl⟩ : syracuseStep 3459587 = 5189381) B5189381
theorem B2306391 : Blo 2305435 2306391 := bstep (se 1 (by rfl) ⟨1729793, by rfl⟩ : syracuseStep 2306391 = 3459587) B3459587
theorem B4378549 : Blo 2305435 4378549 := bbase (se 5 (by rfl) ⟨205244, by rfl⟩ : syracuseStep 4378549 = 410489) (by norm_num)
theorem B5838065 : Blo 2305435 5838065 := bstep (se 2 (by rfl) ⟨2189274, by rfl⟩ : syracuseStep 5838065 = 4378549) B4378549
theorem B3892043 : Blo 2305435 3892043 := bstep (se 1 (by rfl) ⟨2919032, by rfl⟩ : syracuseStep 3892043 = 5838065) B5838065
theorem B2594695 : Blo 2305435 2594695 := bstep (se 1 (by rfl) ⟨1946021, by rfl⟩ : syracuseStep 2594695 = 3892043) B3892043
theorem B3459593 : Blo 2305435 3459593 := bstep (se 2 (by rfl) ⟨1297347, by rfl⟩ : syracuseStep 3459593 = 2594695) B2594695
theorem B2306395 : Blo 2305435 2306395 := bstep (se 1 (by rfl) ⟨1729796, by rfl⟩ : syracuseStep 2306395 = 3459593) B3459593
theorem B11676149 : Blo 2305435 11676149 := bbase (se 5 (by rfl) ⟨547319, by rfl⟩ : syracuseStep 11676149 = 1094639) (by norm_num)
theorem B7784099 : Blo 2305435 7784099 := bstep (se 1 (by rfl) ⟨5838074, by rfl⟩ : syracuseStep 7784099 = 11676149) B11676149
theorem B5189399 : Blo 2305435 5189399 := bstep (se 1 (by rfl) ⟨3892049, by rfl⟩ : syracuseStep 5189399 = 7784099) B7784099
theorem B3459599 : Blo 2305435 3459599 := bstep (se 1 (by rfl) ⟨2594699, by rfl⟩ : syracuseStep 3459599 = 5189399) B5189399
theorem B2306399 : Blo 2305435 2306399 := bstep (se 1 (by rfl) ⟨1729799, by rfl⟩ : syracuseStep 2306399 = 3459599) B3459599
theorem B3459605 : Blo 2305435 3459605 := bbase (se 6 (by rfl) ⟨81084, by rfl⟩ : syracuseStep 3459605 = 162169) (by norm_num)
theorem B2306403 : Blo 2305435 2306403 := bstep (se 1 (by rfl) ⟨1729802, by rfl⟩ : syracuseStep 2306403 = 3459605) B3459605
theorem B19703573 : Blo 2305435 19703573 := bbase (se 6 (by rfl) ⟨461802, by rfl⟩ : syracuseStep 19703573 = 923605) (by norm_num)
theorem B13135715 : Blo 2305435 13135715 := bstep (se 1 (by rfl) ⟨9851786, by rfl⟩ : syracuseStep 13135715 = 19703573) B19703573
theorem B8757143 : Blo 2305435 8757143 := bstep (se 1 (by rfl) ⟨6567857, by rfl⟩ : syracuseStep 8757143 = 13135715) B13135715
theorem B5838095 : Blo 2305435 5838095 := bstep (se 1 (by rfl) ⟨4378571, by rfl⟩ : syracuseStep 5838095 = 8757143) B8757143
theorem B3892063 : Blo 2305435 3892063 := bstep (se 1 (by rfl) ⟨2919047, by rfl⟩ : syracuseStep 3892063 = 5838095) B5838095
theorem B5189417 : Blo 2305435 5189417 := bstep (se 2 (by rfl) ⟨1946031, by rfl⟩ : syracuseStep 5189417 = 3892063) B3892063
theorem B3459611 : Blo 2305435 3459611 := bstep (se 1 (by rfl) ⟨2594708, by rfl⟩ : syracuseStep 3459611 = 5189417) B5189417
theorem B2306407 : Blo 2305435 2306407 := bstep (se 1 (by rfl) ⟨1729805, by rfl⟩ : syracuseStep 2306407 = 3459611) B3459611
theorem B2594713 : Blo 2305435 2594713 := bbase (se 2 (by rfl) ⟨973017, by rfl⟩ : syracuseStep 2594713 = 1946035) (by norm_num)
theorem B3459617 : Blo 2305435 3459617 := bstep (se 2 (by rfl) ⟨1297356, by rfl⟩ : syracuseStep 3459617 = 2594713) B2594713
theorem B2306411 : Blo 2305435 2306411 := bstep (se 1 (by rfl) ⟨1729808, by rfl⟩ : syracuseStep 2306411 = 3459617) B3459617
theorem B8757173 : Blo 2305435 8757173 := bbase (se 5 (by rfl) ⟨410492, by rfl⟩ : syracuseStep 8757173 = 820985) (by norm_num)
theorem B5838115 : Blo 2305435 5838115 := bstep (se 1 (by rfl) ⟨4378586, by rfl⟩ : syracuseStep 5838115 = 8757173) B8757173
theorem B7784153 : Blo 2305435 7784153 := bstep (se 2 (by rfl) ⟨2919057, by rfl⟩ : syracuseStep 7784153 = 5838115) B5838115
theorem B5189435 : Blo 2305435 5189435 := bstep (se 1 (by rfl) ⟨3892076, by rfl⟩ : syracuseStep 5189435 = 7784153) B7784153
theorem B3459623 : Blo 2305435 3459623 := bstep (se 1 (by rfl) ⟨2594717, by rfl⟩ : syracuseStep 3459623 = 5189435) B5189435
theorem B2306415 : Blo 2305435 2306415 := bstep (se 1 (by rfl) ⟨1729811, by rfl⟩ : syracuseStep 2306415 = 3459623) B3459623
theorem B3459629 : Blo 2305435 3459629 := bbase (se 3 (by rfl) ⟨648680, by rfl⟩ : syracuseStep 3459629 = 1297361) (by norm_num)
theorem B2306419 : Blo 2305435 2306419 := bstep (se 1 (by rfl) ⟨1729814, by rfl⟩ : syracuseStep 2306419 = 3459629) B3459629
theorem B5189453 : Blo 2305435 5189453 := bbase (se 3 (by rfl) ⟨973022, by rfl⟩ : syracuseStep 5189453 = 1946045) (by norm_num)
theorem B3459635 : Blo 2305435 3459635 := bstep (se 1 (by rfl) ⟨2594726, by rfl⟩ : syracuseStep 3459635 = 5189453) B5189453
theorem B2306423 : Blo 2305435 2306423 := bstep (se 1 (by rfl) ⟨1729817, by rfl⟩ : syracuseStep 2306423 = 3459635) B3459635
theorem B2919073 : Blo 2305435 2919073 := bbase (se 2 (by rfl) ⟨1094652, by rfl⟩ : syracuseStep 2919073 = 2189305) (by norm_num)
theorem B3892097 : Blo 2305435 3892097 := bstep (se 2 (by rfl) ⟨1459536, by rfl⟩ : syracuseStep 3892097 = 2919073) B2919073
theorem B2594731 : Blo 2305435 2594731 := bstep (se 1 (by rfl) ⟨1946048, by rfl⟩ : syracuseStep 2594731 = 3892097) B3892097
theorem B3459641 : Blo 2305435 3459641 := bstep (se 2 (by rfl) ⟨1297365, by rfl⟩ : syracuseStep 3459641 = 2594731) B2594731
theorem B2306427 : Blo 2305435 2306427 := bstep (se 1 (by rfl) ⟨1729820, by rfl⟩ : syracuseStep 2306427 = 3459641) B3459641
theorem B26271701 : Blo 2305435 26271701 := bbase (se 7 (by rfl) ⟨307871, by rfl⟩ : syracuseStep 26271701 = 615743) (by norm_num)
theorem B17514467 : Blo 2305435 17514467 := bstep (se 1 (by rfl) ⟨13135850, by rfl⟩ : syracuseStep 17514467 = 26271701) B26271701
theorem B11676311 : Blo 2305435 11676311 := bstep (se 1 (by rfl) ⟨8757233, by rfl⟩ : syracuseStep 11676311 = 17514467) B17514467
theorem B7784207 : Blo 2305435 7784207 := bstep (se 1 (by rfl) ⟨5838155, by rfl⟩ : syracuseStep 7784207 = 11676311) B11676311
theorem B5189471 : Blo 2305435 5189471 := bstep (se 1 (by rfl) ⟨3892103, by rfl⟩ : syracuseStep 5189471 = 7784207) B7784207
theorem B3459647 : Blo 2305435 3459647 := bstep (se 1 (by rfl) ⟨2594735, by rfl⟩ : syracuseStep 3459647 = 5189471) B5189471
theorem B2306431 : Blo 2305435 2306431 := bstep (se 1 (by rfl) ⟨1729823, by rfl⟩ : syracuseStep 2306431 = 3459647) B3459647
theorem B3459653 : Blo 2305435 3459653 := bbase (se 4 (by rfl) ⟨324342, by rfl⟩ : syracuseStep 3459653 = 648685) (by norm_num)
theorem B2306435 : Blo 2305435 2306435 := bstep (se 1 (by rfl) ⟨1729826, by rfl⟩ : syracuseStep 2306435 = 3459653) B3459653
theorem B3892117 : Blo 2305435 3892117 := bbase (se 6 (by rfl) ⟨91221, by rfl⟩ : syracuseStep 3892117 = 182443) (by norm_num)
theorem B5189489 : Blo 2305435 5189489 := bstep (se 2 (by rfl) ⟨1946058, by rfl⟩ : syracuseStep 5189489 = 3892117) B3892117
theorem B3459659 : Blo 2305435 3459659 := bstep (se 1 (by rfl) ⟨2594744, by rfl⟩ : syracuseStep 3459659 = 5189489) B5189489
theorem B2306439 : Blo 2305435 2306439 := bstep (se 1 (by rfl) ⟨1729829, by rfl⟩ : syracuseStep 2306439 = 3459659) B3459659
theorem B2594749 : Blo 2305435 2594749 := bbase (se 3 (by rfl) ⟨486515, by rfl⟩ : syracuseStep 2594749 = 973031) (by norm_num)
theorem B3459665 : Blo 2305435 3459665 := bstep (se 2 (by rfl) ⟨1297374, by rfl⟩ : syracuseStep 3459665 = 2594749) B2594749
theorem B2306443 : Blo 2305435 2306443 := bstep (se 1 (by rfl) ⟨1729832, by rfl⟩ : syracuseStep 2306443 = 3459665) B3459665
theorem B7784261 : Blo 2305435 7784261 := bbase (se 4 (by rfl) ⟨729774, by rfl⟩ : syracuseStep 7784261 = 1459549) (by norm_num)
theorem B5189507 : Blo 2305435 5189507 := bstep (se 1 (by rfl) ⟨3892130, by rfl⟩ : syracuseStep 5189507 = 7784261) B7784261
theorem B3459671 : Blo 2305435 3459671 := bstep (se 1 (by rfl) ⟨2594753, by rfl⟩ : syracuseStep 3459671 = 5189507) B5189507
theorem B2306447 : Blo 2305435 2306447 := bstep (se 1 (by rfl) ⟨1729835, by rfl⟩ : syracuseStep 2306447 = 3459671) B3459671
theorem B3459677 : Blo 2305435 3459677 := bbase (se 3 (by rfl) ⟨648689, by rfl⟩ : syracuseStep 3459677 = 1297379) (by norm_num)
theorem B2306451 : Blo 2305435 2306451 := bstep (se 1 (by rfl) ⟨1729838, by rfl⟩ : syracuseStep 2306451 = 3459677) B3459677
theorem B5189525 : Blo 2305435 5189525 := bbase (se 6 (by rfl) ⟨121629, by rfl⟩ : syracuseStep 5189525 = 243259) (by norm_num)
theorem B3459683 : Blo 2305435 3459683 := bstep (se 1 (by rfl) ⟨2594762, by rfl⟩ : syracuseStep 3459683 = 5189525) B5189525
theorem B2306455 : Blo 2305435 2306455 := bstep (se 1 (by rfl) ⟨1729841, by rfl⟩ : syracuseStep 2306455 = 3459683) B3459683
theorem B4926005 : Blo 2305435 4926005 := bbase (se 5 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 4926005 = 461813) (by norm_num)
theorem B3284003 : Blo 2305435 3284003 := bstep (se 1 (by rfl) ⟨2463002, by rfl⟩ : syracuseStep 3284003 = 4926005) B4926005
theorem B8757341 : Blo 2305435 8757341 := bstep (se 3 (by rfl) ⟨1642001, by rfl⟩ : syracuseStep 8757341 = 3284003) B3284003
theorem B5838227 : Blo 2305435 5838227 := bstep (se 1 (by rfl) ⟨4378670, by rfl⟩ : syracuseStep 5838227 = 8757341) B8757341
theorem B3892151 : Blo 2305435 3892151 := bstep (se 1 (by rfl) ⟨2919113, by rfl⟩ : syracuseStep 3892151 = 5838227) B5838227
theorem B2594767 : Blo 2305435 2594767 := bstep (se 1 (by rfl) ⟨1946075, by rfl⟩ : syracuseStep 2594767 = 3892151) B3892151
theorem B3459689 : Blo 2305435 3459689 := bstep (se 2 (by rfl) ⟨1297383, by rfl⟩ : syracuseStep 3459689 = 2594767) B2594767
theorem B2306459 : Blo 2305435 2306459 := bstep (se 1 (by rfl) ⟨1729844, by rfl⟩ : syracuseStep 2306459 = 3459689) B3459689
theorem B8876837 : Blo 2305435 8876837 := bbase (se 4 (by rfl) ⟨832203, by rfl⟩ : syracuseStep 8876837 = 1664407) (by norm_num)
theorem B23671565 : Blo 2305435 23671565 := bstep (se 3 (by rfl) ⟨4438418, by rfl⟩ : syracuseStep 23671565 = 8876837) B8876837
theorem B15781043 : Blo 2305435 15781043 := bstep (se 1 (by rfl) ⟨11835782, by rfl⟩ : syracuseStep 15781043 = 23671565) B23671565
theorem B10520695 : Blo 2305435 10520695 := bstep (se 1 (by rfl) ⟨7890521, by rfl⟩ : syracuseStep 10520695 = 15781043) B15781043
theorem B14027593 : Blo 2305435 14027593 := bstep (se 2 (by rfl) ⟨5260347, by rfl⟩ : syracuseStep 14027593 = 10520695) B10520695
theorem B18703457 : Blo 2305435 18703457 := bstep (se 2 (by rfl) ⟨7013796, by rfl⟩ : syracuseStep 18703457 = 14027593) B14027593
theorem B12468971 : Blo 2305435 12468971 := bstep (se 1 (by rfl) ⟨9351728, by rfl⟩ : syracuseStep 12468971 = 18703457) B18703457
theorem B8312647 : Blo 2305435 8312647 := bstep (se 1 (by rfl) ⟨6234485, by rfl⟩ : syracuseStep 8312647 = 12468971) B12468971
theorem B11083529 : Blo 2305435 11083529 := bstep (se 2 (by rfl) ⟨4156323, by rfl⟩ : syracuseStep 11083529 = 8312647) B8312647
theorem B7389019 : Blo 2305435 7389019 := bstep (se 1 (by rfl) ⟨5541764, by rfl⟩ : syracuseStep 7389019 = 11083529) B11083529
theorem B9852025 : Blo 2305435 9852025 := bstep (se 2 (by rfl) ⟨3694509, by rfl⟩ : syracuseStep 9852025 = 7389019) B7389019
theorem B13136033 : Blo 2305435 13136033 := bstep (se 2 (by rfl) ⟨4926012, by rfl⟩ : syracuseStep 13136033 = 9852025) B9852025
theorem B8757355 : Blo 2305435 8757355 := bstep (se 1 (by rfl) ⟨6568016, by rfl⟩ : syracuseStep 8757355 = 13136033) B13136033
theorem B11676473 : Blo 2305435 11676473 := bstep (se 2 (by rfl) ⟨4378677, by rfl⟩ : syracuseStep 11676473 = 8757355) B8757355
theorem B7784315 : Blo 2305435 7784315 := bstep (se 1 (by rfl) ⟨5838236, by rfl⟩ : syracuseStep 7784315 = 11676473) B11676473
theorem B5189543 : Blo 2305435 5189543 := bstep (se 1 (by rfl) ⟨3892157, by rfl⟩ : syracuseStep 5189543 = 7784315) B7784315
theorem B3459695 : Blo 2305435 3459695 := bstep (se 1 (by rfl) ⟨2594771, by rfl⟩ : syracuseStep 3459695 = 5189543) B5189543
theorem B2306463 : Blo 2305435 2306463 := bstep (se 1 (by rfl) ⟨1729847, by rfl⟩ : syracuseStep 2306463 = 3459695) B3459695
theorem B3459701 : Blo 2305435 3459701 := bbase (se 5 (by rfl) ⟨162173, by rfl⟩ : syracuseStep 3459701 = 324347) (by norm_num)
theorem B2306467 : Blo 2305435 2306467 := bstep (se 1 (by rfl) ⟨1729850, by rfl⟩ : syracuseStep 2306467 = 3459701) B3459701
theorem B4378693 : Blo 2305435 4378693 := bbase (se 4 (by rfl) ⟨410502, by rfl⟩ : syracuseStep 4378693 = 821005) (by norm_num)
theorem B5838257 : Blo 2305435 5838257 := bstep (se 2 (by rfl) ⟨2189346, by rfl⟩ : syracuseStep 5838257 = 4378693) B4378693
theorem B3892171 : Blo 2305435 3892171 := bstep (se 1 (by rfl) ⟨2919128, by rfl⟩ : syracuseStep 3892171 = 5838257) B5838257
theorem B5189561 : Blo 2305435 5189561 := bstep (se 2 (by rfl) ⟨1946085, by rfl⟩ : syracuseStep 5189561 = 3892171) B3892171
theorem B3459707 : Blo 2305435 3459707 := bstep (se 1 (by rfl) ⟨2594780, by rfl⟩ : syracuseStep 3459707 = 5189561) B5189561
theorem B2306471 : Blo 2305435 2306471 := bstep (se 1 (by rfl) ⟨1729853, by rfl⟩ : syracuseStep 2306471 = 3459707) B3459707
theorem B2594785 : Blo 2305435 2594785 := bbase (se 2 (by rfl) ⟨973044, by rfl⟩ : syracuseStep 2594785 = 1946089) (by norm_num)
theorem B3459713 : Blo 2305435 3459713 := bstep (se 2 (by rfl) ⟨1297392, by rfl⟩ : syracuseStep 3459713 = 2594785) B2594785
theorem B2306475 : Blo 2305435 2306475 := bstep (se 1 (by rfl) ⟨1729856, by rfl⟩ : syracuseStep 2306475 = 3459713) B3459713
theorem B5838277 : Blo 2305435 5838277 := bbase (se 4 (by rfl) ⟨547338, by rfl⟩ : syracuseStep 5838277 = 1094677) (by norm_num)
theorem B7784369 : Blo 2305435 7784369 := bstep (se 2 (by rfl) ⟨2919138, by rfl⟩ : syracuseStep 7784369 = 5838277) B5838277
theorem B5189579 : Blo 2305435 5189579 := bstep (se 1 (by rfl) ⟨3892184, by rfl⟩ : syracuseStep 5189579 = 7784369) B7784369
theorem B3459719 : Blo 2305435 3459719 := bstep (se 1 (by rfl) ⟨2594789, by rfl⟩ : syracuseStep 3459719 = 5189579) B5189579
theorem B2306479 : Blo 2305435 2306479 := bstep (se 1 (by rfl) ⟨1729859, by rfl⟩ : syracuseStep 2306479 = 3459719) B3459719
theorem B3459725 : Blo 2305435 3459725 := bbase (se 3 (by rfl) ⟨648698, by rfl⟩ : syracuseStep 3459725 = 1297397) (by norm_num)
theorem B2306483 : Blo 2305435 2306483 := bstep (se 1 (by rfl) ⟨1729862, by rfl⟩ : syracuseStep 2306483 = 3459725) B3459725
theorem B5189597 : Blo 2305435 5189597 := bbase (se 3 (by rfl) ⟨973049, by rfl⟩ : syracuseStep 5189597 = 1946099) (by norm_num)
theorem B3459731 : Blo 2305435 3459731 := bstep (se 1 (by rfl) ⟨2594798, by rfl⟩ : syracuseStep 3459731 = 5189597) B5189597
theorem B2306487 : Blo 2305435 2306487 := bstep (se 1 (by rfl) ⟨1729865, by rfl⟩ : syracuseStep 2306487 = 3459731) B3459731
theorem B3892205 : Blo 2305435 3892205 := bbase (se 3 (by rfl) ⟨729788, by rfl⟩ : syracuseStep 3892205 = 1459577) (by norm_num)
theorem B2594803 : Blo 2305435 2594803 := bstep (se 1 (by rfl) ⟨1946102, by rfl⟩ : syracuseStep 2594803 = 3892205) B3892205
theorem B3459737 : Blo 2305435 3459737 := bstep (se 2 (by rfl) ⟨1297401, by rfl⟩ : syracuseStep 3459737 = 2594803) B2594803
theorem B2306491 : Blo 2305435 2306491 := bstep (se 1 (by rfl) ⟨1729868, by rfl⟩ : syracuseStep 2306491 = 3459737) B3459737
theorem B4156381 : Blo 2305435 4156381 := bbase (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) (by norm_num)
theorem B5541841 : Blo 2305435 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B29556485 : Blo 2305435 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B19704323 : Blo 2305435 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B13136215 : Blo 2305435 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B17514953 : Blo 2305435 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B11676635 : Blo 2305435 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B7784423 : Blo 2305435 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B5189615 : Blo 2305435 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B3459743 : Blo 2305435 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B2306495 : Blo 2305435 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B3459749 : Blo 2305435 3459749 := bbase (se 4 (by rfl) ⟨324351, by rfl⟩ : syracuseStep 3459749 = 648703) (by norm_num)
theorem B2306499 : Blo 2305435 2306499 := bstep (se 1 (by rfl) ⟨1729874, by rfl⟩ : syracuseStep 2306499 = 3459749) B3459749
theorem B2919169 : Blo 2305435 2919169 := bbase (se 2 (by rfl) ⟨1094688, by rfl⟩ : syracuseStep 2919169 = 2189377) (by norm_num)
theorem B3892225 : Blo 2305435 3892225 := bstep (se 2 (by rfl) ⟨1459584, by rfl⟩ : syracuseStep 3892225 = 2919169) B2919169
theorem B5189633 : Blo 2305435 5189633 := bstep (se 2 (by rfl) ⟨1946112, by rfl⟩ : syracuseStep 5189633 = 3892225) B3892225
theorem B3459755 : Blo 2305435 3459755 := bstep (se 1 (by rfl) ⟨2594816, by rfl⟩ : syracuseStep 3459755 = 5189633) B5189633
theorem B2306503 : Blo 2305435 2306503 := bstep (se 1 (by rfl) ⟨1729877, by rfl⟩ : syracuseStep 2306503 = 3459755) B3459755
theorem B2594821 : Blo 2305435 2594821 := bbase (se 4 (by rfl) ⟨243264, by rfl⟩ : syracuseStep 2594821 = 486529) (by norm_num)
theorem B3459761 : Blo 2305435 3459761 := bstep (se 2 (by rfl) ⟨1297410, by rfl⟩ : syracuseStep 3459761 = 2594821) B2594821
theorem B2306507 : Blo 2305435 2306507 := bstep (se 1 (by rfl) ⟨1729880, by rfl⟩ : syracuseStep 2306507 = 3459761) B3459761
theorem B3284077 : Blo 2305435 3284077 := bbase (se 3 (by rfl) ⟨615764, by rfl⟩ : syracuseStep 3284077 = 1231529) (by norm_num)
theorem B4378769 : Blo 2305435 4378769 := bstep (se 2 (by rfl) ⟨1642038, by rfl⟩ : syracuseStep 4378769 = 3284077) B3284077
theorem B2919179 : Blo 2305435 2919179 := bstep (se 1 (by rfl) ⟨2189384, by rfl⟩ : syracuseStep 2919179 = 4378769) B4378769
theorem B7784477 : Blo 2305435 7784477 := bstep (se 3 (by rfl) ⟨1459589, by rfl⟩ : syracuseStep 7784477 = 2919179) B2919179
theorem B5189651 : Blo 2305435 5189651 := bstep (se 1 (by rfl) ⟨3892238, by rfl⟩ : syracuseStep 5189651 = 7784477) B7784477
theorem B3459767 : Blo 2305435 3459767 := bstep (se 1 (by rfl) ⟨2594825, by rfl⟩ : syracuseStep 3459767 = 5189651) B5189651
theorem B2306511 : Blo 2305435 2306511 := bstep (se 1 (by rfl) ⟨1729883, by rfl⟩ : syracuseStep 2306511 = 3459767) B3459767
theorem B3459773 : Blo 2305435 3459773 := bbase (se 3 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 3459773 = 1297415) (by norm_num)
theorem B2306515 : Blo 2305435 2306515 := bstep (se 1 (by rfl) ⟨1729886, by rfl⟩ : syracuseStep 2306515 = 3459773) B3459773
theorem B5189669 : Blo 2305435 5189669 := bbase (se 4 (by rfl) ⟨486531, by rfl⟩ : syracuseStep 5189669 = 973063) (by norm_num)
theorem B3459779 : Blo 2305435 3459779 := bstep (se 1 (by rfl) ⟨2594834, by rfl⟩ : syracuseStep 3459779 = 5189669) B5189669
theorem B2306519 : Blo 2305435 2306519 := bstep (se 1 (by rfl) ⟨1729889, by rfl⟩ : syracuseStep 2306519 = 3459779) B3459779
theorem B5838389 : Blo 2305435 5838389 := bbase (se 5 (by rfl) ⟨273674, by rfl⟩ : syracuseStep 5838389 = 547349) (by norm_num)
theorem B3892259 : Blo 2305435 3892259 := bstep (se 1 (by rfl) ⟨2919194, by rfl⟩ : syracuseStep 3892259 = 5838389) B5838389
theorem B2594839 : Blo 2305435 2594839 := bstep (se 1 (by rfl) ⟨1946129, by rfl⟩ : syracuseStep 2594839 = 3892259) B3892259
theorem B3459785 : Blo 2305435 3459785 := bstep (se 2 (by rfl) ⟨1297419, by rfl⟩ : syracuseStep 3459785 = 2594839) B2594839
theorem B2306523 : Blo 2305435 2306523 := bstep (se 1 (by rfl) ⟨1729892, by rfl⟩ : syracuseStep 2306523 = 3459785) B3459785
theorem B9351989 : Blo 2305435 9351989 := bbase (se 5 (by rfl) ⟨438374, by rfl⟩ : syracuseStep 9351989 = 876749) (by norm_num)
theorem B6234659 : Blo 2305435 6234659 := bstep (se 1 (by rfl) ⟨4675994, by rfl⟩ : syracuseStep 6234659 = 9351989) B9351989
theorem B4156439 : Blo 2305435 4156439 := bstep (se 1 (by rfl) ⟨3117329, by rfl⟩ : syracuseStep 4156439 = 6234659) B6234659
theorem B11083837 : Blo 2305435 11083837 := bstep (se 3 (by rfl) ⟨2078219, by rfl⟩ : syracuseStep 11083837 = 4156439) B4156439
theorem B14778449 : Blo 2305435 14778449 := bstep (se 2 (by rfl) ⟨5541918, by rfl⟩ : syracuseStep 14778449 = 11083837) B11083837
theorem B9852299 : Blo 2305435 9852299 := bstep (se 1 (by rfl) ⟨7389224, by rfl⟩ : syracuseStep 9852299 = 14778449) B14778449
theorem B6568199 : Blo 2305435 6568199 := bstep (se 1 (by rfl) ⟨4926149, by rfl⟩ : syracuseStep 6568199 = 9852299) B9852299
theorem B4378799 : Blo 2305435 4378799 := bstep (se 1 (by rfl) ⟨3284099, by rfl⟩ : syracuseStep 4378799 = 6568199) B6568199
theorem B11676797 : Blo 2305435 11676797 := bstep (se 3 (by rfl) ⟨2189399, by rfl⟩ : syracuseStep 11676797 = 4378799) B4378799
theorem B7784531 : Blo 2305435 7784531 := bstep (se 1 (by rfl) ⟨5838398, by rfl⟩ : syracuseStep 7784531 = 11676797) B11676797
theorem B5189687 : Blo 2305435 5189687 := bstep (se 1 (by rfl) ⟨3892265, by rfl⟩ : syracuseStep 5189687 = 7784531) B7784531
theorem B3459791 : Blo 2305435 3459791 := bstep (se 1 (by rfl) ⟨2594843, by rfl⟩ : syracuseStep 3459791 = 5189687) B5189687
theorem B2306527 : Blo 2305435 2306527 := bstep (se 1 (by rfl) ⟨1729895, by rfl⟩ : syracuseStep 2306527 = 3459791) B3459791
theorem B3459797 : Blo 2305435 3459797 := bbase (se 7 (by rfl) ⟨40544, by rfl⟩ : syracuseStep 3459797 = 81089) (by norm_num)
theorem B2306531 : Blo 2305435 2306531 := bstep (se 1 (by rfl) ⟨1729898, by rfl⟩ : syracuseStep 2306531 = 3459797) B3459797
theorem B11083877 : Blo 2305435 11083877 := bbase (se 4 (by rfl) ⟨1039113, by rfl⟩ : syracuseStep 11083877 = 2078227) (by norm_num)
theorem B7389251 : Blo 2305435 7389251 := bstep (se 1 (by rfl) ⟨5541938, by rfl⟩ : syracuseStep 7389251 = 11083877) B11083877
theorem B4926167 : Blo 2305435 4926167 := bstep (se 1 (by rfl) ⟨3694625, by rfl⟩ : syracuseStep 4926167 = 7389251) B7389251
theorem B3284111 : Blo 2305435 3284111 := bstep (se 1 (by rfl) ⟨2463083, by rfl⟩ : syracuseStep 3284111 = 4926167) B4926167
theorem B8757629 : Blo 2305435 8757629 := bstep (se 3 (by rfl) ⟨1642055, by rfl⟩ : syracuseStep 8757629 = 3284111) B3284111
theorem B5838419 : Blo 2305435 5838419 := bstep (se 1 (by rfl) ⟨4378814, by rfl⟩ : syracuseStep 5838419 = 8757629) B8757629
theorem B3892279 : Blo 2305435 3892279 := bstep (se 1 (by rfl) ⟨2919209, by rfl⟩ : syracuseStep 3892279 = 5838419) B5838419
theorem B5189705 : Blo 2305435 5189705 := bstep (se 2 (by rfl) ⟨1946139, by rfl⟩ : syracuseStep 5189705 = 3892279) B3892279
theorem B3459803 : Blo 2305435 3459803 := bstep (se 1 (by rfl) ⟨2594852, by rfl⟩ : syracuseStep 3459803 = 5189705) B5189705
theorem B2306535 : Blo 2305435 2306535 := bstep (se 1 (by rfl) ⟨1729901, by rfl⟩ : syracuseStep 2306535 = 3459803) B3459803
theorem B2594857 : Blo 2305435 2594857 := bbase (se 2 (by rfl) ⟨973071, by rfl⟩ : syracuseStep 2594857 = 1946143) (by norm_num)
theorem B3459809 : Blo 2305435 3459809 := bstep (se 2 (by rfl) ⟨1297428, by rfl⟩ : syracuseStep 3459809 = 2594857) B2594857
theorem B2306539 : Blo 2305435 2306539 := bstep (se 1 (by rfl) ⟨1729904, by rfl⟩ : syracuseStep 2306539 = 3459809) B3459809
theorem B7305061 : Blo 2305435 7305061 := bbase (se 4 (by rfl) ⟨684849, by rfl⟩ : syracuseStep 7305061 = 1369699) (by norm_num)
theorem B9740081 : Blo 2305435 9740081 := bstep (se 2 (by rfl) ⟨3652530, by rfl⟩ : syracuseStep 9740081 = 7305061) B7305061
theorem B6493387 : Blo 2305435 6493387 := bstep (se 1 (by rfl) ⟨4870040, by rfl⟩ : syracuseStep 6493387 = 9740081) B9740081
theorem B8657849 : Blo 2305435 8657849 := bstep (se 2 (by rfl) ⟨3246693, by rfl⟩ : syracuseStep 8657849 = 6493387) B6493387
theorem B23087597 : Blo 2305435 23087597 := bstep (se 3 (by rfl) ⟨4328924, by rfl⟩ : syracuseStep 23087597 = 8657849) B8657849
theorem B246267701 : Blo 2305435 246267701 := bstep (se 5 (by rfl) ⟨11543798, by rfl⟩ : syracuseStep 246267701 = 23087597) B23087597
theorem B164178467 : Blo 2305435 164178467 := bstep (se 1 (by rfl) ⟨123133850, by rfl⟩ : syracuseStep 164178467 = 246267701) B246267701
theorem B109452311 : Blo 2305435 109452311 := bstep (se 1 (by rfl) ⟨82089233, by rfl⟩ : syracuseStep 109452311 = 164178467) B164178467
theorem B72968207 : Blo 2305435 72968207 := bstep (se 1 (by rfl) ⟨54726155, by rfl⟩ : syracuseStep 72968207 = 109452311) B109452311
theorem B194581885 : Blo 2305435 194581885 := bstep (se 3 (by rfl) ⟨36484103, by rfl⟩ : syracuseStep 194581885 = 72968207) B72968207
theorem B259442513 : Blo 2305435 259442513 := bstep (se 2 (by rfl) ⟨97290942, by rfl⟩ : syracuseStep 259442513 = 194581885) B194581885
theorem B172961675 : Blo 2305435 172961675 := bstep (se 1 (by rfl) ⟨129721256, by rfl⟩ : syracuseStep 172961675 = 259442513) B259442513
theorem B115307783 : Blo 2305435 115307783 := bstep (se 1 (by rfl) ⟨86480837, by rfl⟩ : syracuseStep 115307783 = 172961675) B172961675
theorem B76871855 : Blo 2305435 76871855 := bstep (se 1 (by rfl) ⟨57653891, by rfl⟩ : syracuseStep 76871855 = 115307783) B115307783
theorem B51247903 : Blo 2305435 51247903 := bstep (se 1 (by rfl) ⟨38435927, by rfl⟩ : syracuseStep 51247903 = 76871855) B76871855
theorem B68330537 : Blo 2305435 68330537 := bstep (se 2 (by rfl) ⟨25623951, by rfl⟩ : syracuseStep 68330537 = 51247903) B51247903
theorem B45553691 : Blo 2305435 45553691 := bstep (se 1 (by rfl) ⟨34165268, by rfl⟩ : syracuseStep 45553691 = 68330537) B68330537
theorem B30369127 : Blo 2305435 30369127 := bstep (se 1 (by rfl) ⟨22776845, by rfl⟩ : syracuseStep 30369127 = 45553691) B45553691
theorem B40492169 : Blo 2305435 40492169 := bstep (se 2 (by rfl) ⟨15184563, by rfl⟩ : syracuseStep 40492169 = 30369127) B30369127
theorem B26994779 : Blo 2305435 26994779 := bstep (se 1 (by rfl) ⟨20246084, by rfl⟩ : syracuseStep 26994779 = 40492169) B40492169
theorem B17996519 : Blo 2305435 17996519 := bstep (se 1 (by rfl) ⟨13497389, by rfl⟩ : syracuseStep 17996519 = 26994779) B26994779
theorem B11997679 : Blo 2305435 11997679 := bstep (se 1 (by rfl) ⟨8998259, by rfl⟩ : syracuseStep 11997679 = 17996519) B17996519
theorem B15996905 : Blo 2305435 15996905 := bstep (se 2 (by rfl) ⟨5998839, by rfl⟩ : syracuseStep 15996905 = 11997679) B11997679
theorem B10664603 : Blo 2305435 10664603 := bstep (se 1 (by rfl) ⟨7998452, by rfl⟩ : syracuseStep 10664603 = 15996905) B15996905
theorem B7109735 : Blo 2305435 7109735 := bstep (se 1 (by rfl) ⟨5332301, by rfl⟩ : syracuseStep 7109735 = 10664603) B10664603
theorem B18959293 : Blo 2305435 18959293 := bstep (se 3 (by rfl) ⟨3554867, by rfl⟩ : syracuseStep 18959293 = 7109735) B7109735
theorem B25279057 : Blo 2305435 25279057 := bstep (se 2 (by rfl) ⟨9479646, by rfl⟩ : syracuseStep 25279057 = 18959293) B18959293
theorem B33705409 : Blo 2305435 33705409 := bstep (se 2 (by rfl) ⟨12639528, by rfl⟩ : syracuseStep 33705409 = 25279057) B25279057
theorem B44940545 : Blo 2305435 44940545 := bstep (se 2 (by rfl) ⟨16852704, by rfl⟩ : syracuseStep 44940545 = 33705409) B33705409
theorem B29960363 : Blo 2305435 29960363 := bstep (se 1 (by rfl) ⟨22470272, by rfl⟩ : syracuseStep 29960363 = 44940545) B44940545
theorem B19973575 : Blo 2305435 19973575 := bstep (se 1 (by rfl) ⟨14980181, by rfl⟩ : syracuseStep 19973575 = 29960363) B29960363
theorem B26631433 : Blo 2305435 26631433 := bstep (se 2 (by rfl) ⟨9986787, by rfl⟩ : syracuseStep 26631433 = 19973575) B19973575
theorem B35508577 : Blo 2305435 35508577 := bstep (se 2 (by rfl) ⟨13315716, by rfl⟩ : syracuseStep 35508577 = 26631433) B26631433
theorem B47344769 : Blo 2305435 47344769 := bstep (se 2 (by rfl) ⟨17754288, by rfl⟩ : syracuseStep 47344769 = 35508577) B35508577
theorem B31563179 : Blo 2305435 31563179 := bstep (se 1 (by rfl) ⟨23672384, by rfl⟩ : syracuseStep 31563179 = 47344769) B47344769
theorem B21042119 : Blo 2305435 21042119 := bstep (se 1 (by rfl) ⟨15781589, by rfl⟩ : syracuseStep 21042119 = 31563179) B31563179
theorem B14028079 : Blo 2305435 14028079 := bstep (se 1 (by rfl) ⟨10521059, by rfl⟩ : syracuseStep 14028079 = 21042119) B21042119
theorem B18704105 : Blo 2305435 18704105 := bstep (se 2 (by rfl) ⟨7014039, by rfl⟩ : syracuseStep 18704105 = 14028079) B14028079
theorem B12469403 : Blo 2305435 12469403 := bstep (se 1 (by rfl) ⟨9352052, by rfl⟩ : syracuseStep 12469403 = 18704105) B18704105
theorem B33251741 : Blo 2305435 33251741 := bstep (se 3 (by rfl) ⟨6234701, by rfl⟩ : syracuseStep 33251741 = 12469403) B12469403
theorem B22167827 : Blo 2305435 22167827 := bstep (se 1 (by rfl) ⟨16625870, by rfl⟩ : syracuseStep 22167827 = 33251741) B33251741
theorem B14778551 : Blo 2305435 14778551 := bstep (se 1 (by rfl) ⟨11083913, by rfl⟩ : syracuseStep 14778551 = 22167827) B22167827
theorem B9852367 : Blo 2305435 9852367 := bstep (se 1 (by rfl) ⟨7389275, by rfl⟩ : syracuseStep 9852367 = 14778551) B14778551
theorem B13136489 : Blo 2305435 13136489 := bstep (se 2 (by rfl) ⟨4926183, by rfl⟩ : syracuseStep 13136489 = 9852367) B9852367
theorem B8757659 : Blo 2305435 8757659 := bstep (se 1 (by rfl) ⟨6568244, by rfl⟩ : syracuseStep 8757659 = 13136489) B13136489
theorem B5838439 : Blo 2305435 5838439 := bstep (se 1 (by rfl) ⟨4378829, by rfl⟩ : syracuseStep 5838439 = 8757659) B8757659
theorem B7784585 : Blo 2305435 7784585 := bstep (se 2 (by rfl) ⟨2919219, by rfl⟩ : syracuseStep 7784585 = 5838439) B5838439
theorem B5189723 : Blo 2305435 5189723 := bstep (se 1 (by rfl) ⟨3892292, by rfl⟩ : syracuseStep 5189723 = 7784585) B7784585
theorem B3459815 : Blo 2305435 3459815 := bstep (se 1 (by rfl) ⟨2594861, by rfl⟩ : syracuseStep 3459815 = 5189723) B5189723
theorem B2306543 : Blo 2305435 2306543 := bstep (se 1 (by rfl) ⟨1729907, by rfl⟩ : syracuseStep 2306543 = 3459815) B3459815
theorem B3459821 : Blo 2305435 3459821 := bbase (se 3 (by rfl) ⟨648716, by rfl⟩ : syracuseStep 3459821 = 1297433) (by norm_num)
theorem B2306547 : Blo 2305435 2306547 := bstep (se 1 (by rfl) ⟨1729910, by rfl⟩ : syracuseStep 2306547 = 3459821) B3459821
theorem B5189741 : Blo 2305435 5189741 := bbase (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) (by norm_num)
theorem B3459827 : Blo 2305435 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B2306551 : Blo 2305435 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B4378853 : Blo 2305435 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B2919235 : Blo 2305435 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B3892313 : Blo 2305435 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B2594875 : Blo 2305435 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B3459833 : Blo 2305435 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B2306555 : Blo 2305435 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B44335957 : Blo 2305435 44335957 := bbase (se 9 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 44335957 = 259781) (by norm_num)
theorem B59114609 : Blo 2305435 59114609 := bstep (se 2 (by rfl) ⟨22167978, by rfl⟩ : syracuseStep 59114609 = 44335957) B44335957
theorem B39409739 : Blo 2305435 39409739 := bstep (se 1 (by rfl) ⟨29557304, by rfl⟩ : syracuseStep 39409739 = 59114609) B59114609
theorem B26273159 : Blo 2305435 26273159 := bstep (se 1 (by rfl) ⟨19704869, by rfl⟩ : syracuseStep 26273159 = 39409739) B39409739
theorem B17515439 : Blo 2305435 17515439 := bstep (se 1 (by rfl) ⟨13136579, by rfl⟩ : syracuseStep 17515439 = 26273159) B26273159
theorem B11676959 : Blo 2305435 11676959 := bstep (se 1 (by rfl) ⟨8757719, by rfl⟩ : syracuseStep 11676959 = 17515439) B17515439
theorem B7784639 : Blo 2305435 7784639 := bstep (se 1 (by rfl) ⟨5838479, by rfl⟩ : syracuseStep 7784639 = 11676959) B11676959
theorem B5189759 : Blo 2305435 5189759 := bstep (se 1 (by rfl) ⟨3892319, by rfl⟩ : syracuseStep 5189759 = 7784639) B7784639
theorem B3459839 : Blo 2305435 3459839 := bstep (se 1 (by rfl) ⟨2594879, by rfl⟩ : syracuseStep 3459839 = 5189759) B5189759
theorem B2306559 : Blo 2305435 2306559 := bstep (se 1 (by rfl) ⟨1729919, by rfl⟩ : syracuseStep 2306559 = 3459839) B3459839
theorem B3459845 : Blo 2305435 3459845 := bbase (se 4 (by rfl) ⟨324360, by rfl⟩ : syracuseStep 3459845 = 648721) (by norm_num)
theorem B2306563 : Blo 2305435 2306563 := bstep (se 1 (by rfl) ⟨1729922, by rfl⟩ : syracuseStep 2306563 = 3459845) B3459845
theorem B3892333 : Blo 2305435 3892333 := bbase (se 3 (by rfl) ⟨729812, by rfl⟩ : syracuseStep 3892333 = 1459625) (by norm_num)
theorem B5189777 : Blo 2305435 5189777 := bstep (se 2 (by rfl) ⟨1946166, by rfl⟩ : syracuseStep 5189777 = 3892333) B3892333
theorem B3459851 : Blo 2305435 3459851 := bstep (se 1 (by rfl) ⟨2594888, by rfl⟩ : syracuseStep 3459851 = 5189777) B5189777
theorem B2306567 : Blo 2305435 2306567 := bstep (se 1 (by rfl) ⟨1729925, by rfl⟩ : syracuseStep 2306567 = 3459851) B3459851
theorem B2594893 : Blo 2305435 2594893 := bbase (se 3 (by rfl) ⟨486542, by rfl⟩ : syracuseStep 2594893 = 973085) (by norm_num)
theorem B3459857 : Blo 2305435 3459857 := bstep (se 2 (by rfl) ⟨1297446, by rfl⟩ : syracuseStep 3459857 = 2594893) B2594893
theorem B2306571 : Blo 2305435 2306571 := bstep (se 1 (by rfl) ⟨1729928, by rfl⟩ : syracuseStep 2306571 = 3459857) B3459857
theorem B7784693 : Blo 2305435 7784693 := bbase (se 5 (by rfl) ⟨364907, by rfl⟩ : syracuseStep 7784693 = 729815) (by norm_num)
theorem B5189795 : Blo 2305435 5189795 := bstep (se 1 (by rfl) ⟨3892346, by rfl⟩ : syracuseStep 5189795 = 7784693) B7784693
theorem B3459863 : Blo 2305435 3459863 := bstep (se 1 (by rfl) ⟨2594897, by rfl⟩ : syracuseStep 3459863 = 5189795) B5189795
theorem B2306575 : Blo 2305435 2306575 := bstep (se 1 (by rfl) ⟨1729931, by rfl⟩ : syracuseStep 2306575 = 3459863) B3459863
theorem B3459869 : Blo 2305435 3459869 := bbase (se 3 (by rfl) ⟨648725, by rfl⟩ : syracuseStep 3459869 = 1297451) (by norm_num)
theorem B2306579 : Blo 2305435 2306579 := bstep (se 1 (by rfl) ⟨1729934, by rfl⟩ : syracuseStep 2306579 = 3459869) B3459869
theorem B5189813 : Blo 2305435 5189813 := bbase (se 5 (by rfl) ⟨243272, by rfl⟩ : syracuseStep 5189813 = 486545) (by norm_num)
theorem B3459875 : Blo 2305435 3459875 := bstep (se 1 (by rfl) ⟨2594906, by rfl⟩ : syracuseStep 3459875 = 5189813) B5189813
theorem B2306583 : Blo 2305435 2306583 := bstep (se 1 (by rfl) ⟨1729937, by rfl⟩ : syracuseStep 2306583 = 3459875) B3459875
theorem B3694709 : Blo 2305435 3694709 := bbase (se 5 (by rfl) ⟨173189, by rfl⟩ : syracuseStep 3694709 = 346379) (by norm_num)
theorem B2463139 : Blo 2305435 2463139 := bstep (se 1 (by rfl) ⟨1847354, by rfl⟩ : syracuseStep 2463139 = 3694709) B3694709
theorem B13136741 : Blo 2305435 13136741 := bstep (se 4 (by rfl) ⟨1231569, by rfl⟩ : syracuseStep 13136741 = 2463139) B2463139
theorem B8757827 : Blo 2305435 8757827 := bstep (se 1 (by rfl) ⟨6568370, by rfl⟩ : syracuseStep 8757827 = 13136741) B13136741
theorem B5838551 : Blo 2305435 5838551 := bstep (se 1 (by rfl) ⟨4378913, by rfl⟩ : syracuseStep 5838551 = 8757827) B8757827
theorem B3892367 : Blo 2305435 3892367 := bstep (se 1 (by rfl) ⟨2919275, by rfl⟩ : syracuseStep 3892367 = 5838551) B5838551
theorem B2594911 : Blo 2305435 2594911 := bstep (se 1 (by rfl) ⟨1946183, by rfl⟩ : syracuseStep 2594911 = 3892367) B3892367
theorem B3459881 : Blo 2305435 3459881 := bstep (se 2 (by rfl) ⟨1297455, by rfl⟩ : syracuseStep 3459881 = 2594911) B2594911
theorem B2306587 : Blo 2305435 2306587 := bstep (se 1 (by rfl) ⟨1729940, by rfl⟩ : syracuseStep 2306587 = 3459881) B3459881
theorem B4676125 : Blo 2305435 4676125 := bbase (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) (by norm_num)
theorem B6234833 : Blo 2305435 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B4156555 : Blo 2305435 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B5542073 : Blo 2305435 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B3694715 : Blo 2305435 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B2463143 : Blo 2305435 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B6568381 : Blo 2305435 6568381 := bstep (se 3 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 6568381 = 2463143) B2463143
theorem B8757841 : Blo 2305435 8757841 := bstep (se 2 (by rfl) ⟨3284190, by rfl⟩ : syracuseStep 8757841 = 6568381) B6568381
theorem B11677121 : Blo 2305435 11677121 := bstep (se 2 (by rfl) ⟨4378920, by rfl⟩ : syracuseStep 11677121 = 8757841) B8757841
theorem B7784747 : Blo 2305435 7784747 := bstep (se 1 (by rfl) ⟨5838560, by rfl⟩ : syracuseStep 7784747 = 11677121) B11677121
theorem B5189831 : Blo 2305435 5189831 := bstep (se 1 (by rfl) ⟨3892373, by rfl⟩ : syracuseStep 5189831 = 7784747) B7784747
theorem B3459887 : Blo 2305435 3459887 := bstep (se 1 (by rfl) ⟨2594915, by rfl⟩ : syracuseStep 3459887 = 5189831) B5189831
theorem B2306591 : Blo 2305435 2306591 := bstep (se 1 (by rfl) ⟨1729943, by rfl⟩ : syracuseStep 2306591 = 3459887) B3459887
theorem B3459893 : Blo 2305435 3459893 := bbase (se 5 (by rfl) ⟨162182, by rfl⟩ : syracuseStep 3459893 = 324365) (by norm_num)
theorem B2306595 : Blo 2305435 2306595 := bstep (se 1 (by rfl) ⟨1729946, by rfl⟩ : syracuseStep 2306595 = 3459893) B3459893
theorem B5838581 : Blo 2305435 5838581 := bbase (se 5 (by rfl) ⟨273683, by rfl⟩ : syracuseStep 5838581 = 547367) (by norm_num)
theorem B3892387 : Blo 2305435 3892387 := bstep (se 1 (by rfl) ⟨2919290, by rfl⟩ : syracuseStep 3892387 = 5838581) B5838581
theorem B5189849 : Blo 2305435 5189849 := bstep (se 2 (by rfl) ⟨1946193, by rfl⟩ : syracuseStep 5189849 = 3892387) B3892387
theorem B3459899 : Blo 2305435 3459899 := bstep (se 1 (by rfl) ⟨2594924, by rfl⟩ : syracuseStep 3459899 = 5189849) B5189849
theorem B2306599 : Blo 2305435 2306599 := bstep (se 1 (by rfl) ⟨1729949, by rfl⟩ : syracuseStep 2306599 = 3459899) B3459899
theorem B2594929 : Blo 2305435 2594929 := bbase (se 2 (by rfl) ⟨973098, by rfl⟩ : syracuseStep 2594929 = 1946197) (by norm_num)
theorem B3459905 : Blo 2305435 3459905 := bstep (se 2 (by rfl) ⟨1297464, by rfl⟩ : syracuseStep 3459905 = 2594929) B2594929
theorem B2306603 : Blo 2305435 2306603 := bstep (se 1 (by rfl) ⟨1729952, by rfl⟩ : syracuseStep 2306603 = 3459905) B3459905
theorem B7998677 : Blo 2305435 7998677 := bbase (se 7 (by rfl) ⟨93734, by rfl⟩ : syracuseStep 7998677 = 187469) (by norm_num)
theorem B5332451 : Blo 2305435 5332451 := bstep (se 1 (by rfl) ⟨3999338, by rfl⟩ : syracuseStep 5332451 = 7998677) B7998677
theorem B14219869 : Blo 2305435 14219869 := bstep (se 3 (by rfl) ⟨2666225, by rfl⟩ : syracuseStep 14219869 = 5332451) B5332451
theorem B18959825 : Blo 2305435 18959825 := bstep (se 2 (by rfl) ⟨7109934, by rfl⟩ : syracuseStep 18959825 = 14219869) B14219869
theorem B12639883 : Blo 2305435 12639883 := bstep (se 1 (by rfl) ⟨9479912, by rfl⟩ : syracuseStep 12639883 = 18959825) B18959825
theorem B16853177 : Blo 2305435 16853177 := bstep (se 2 (by rfl) ⟨6319941, by rfl⟩ : syracuseStep 16853177 = 12639883) B12639883
theorem B11235451 : Blo 2305435 11235451 := bstep (se 1 (by rfl) ⟨8426588, by rfl⟩ : syracuseStep 11235451 = 16853177) B16853177
theorem B14980601 : Blo 2305435 14980601 := bstep (se 2 (by rfl) ⟨5617725, by rfl⟩ : syracuseStep 14980601 = 11235451) B11235451
theorem B9987067 : Blo 2305435 9987067 := bstep (se 1 (by rfl) ⟨7490300, by rfl⟩ : syracuseStep 9987067 = 14980601) B14980601
theorem B13316089 : Blo 2305435 13316089 := bstep (se 2 (by rfl) ⟨4993533, by rfl⟩ : syracuseStep 13316089 = 9987067) B9987067
theorem B17754785 : Blo 2305435 17754785 := bstep (se 2 (by rfl) ⟨6658044, by rfl⟩ : syracuseStep 17754785 = 13316089) B13316089
theorem B11836523 : Blo 2305435 11836523 := bstep (se 1 (by rfl) ⟨8877392, by rfl⟩ : syracuseStep 11836523 = 17754785) B17754785
theorem B7891015 : Blo 2305435 7891015 := bstep (se 1 (by rfl) ⟨5918261, by rfl⟩ : syracuseStep 7891015 = 11836523) B11836523
theorem B10521353 : Blo 2305435 10521353 := bstep (se 2 (by rfl) ⟨3945507, by rfl⟩ : syracuseStep 10521353 = 7891015) B7891015
theorem B28056941 : Blo 2305435 28056941 := bstep (se 3 (by rfl) ⟨5260676, by rfl⟩ : syracuseStep 28056941 = 10521353) B10521353
theorem B18704627 : Blo 2305435 18704627 := bstep (se 1 (by rfl) ⟨14028470, by rfl⟩ : syracuseStep 18704627 = 28056941) B28056941
theorem B12469751 : Blo 2305435 12469751 := bstep (se 1 (by rfl) ⟨9352313, by rfl⟩ : syracuseStep 12469751 = 18704627) B18704627
theorem B8313167 : Blo 2305435 8313167 := bstep (se 1 (by rfl) ⟨6234875, by rfl⟩ : syracuseStep 8313167 = 12469751) B12469751
theorem B5542111 : Blo 2305435 5542111 := bstep (se 1 (by rfl) ⟨4156583, by rfl⟩ : syracuseStep 5542111 = 8313167) B8313167
theorem B7389481 : Blo 2305435 7389481 := bstep (se 2 (by rfl) ⟨2771055, by rfl⟩ : syracuseStep 7389481 = 5542111) B5542111
theorem B9852641 : Blo 2305435 9852641 := bstep (se 2 (by rfl) ⟨3694740, by rfl⟩ : syracuseStep 9852641 = 7389481) B7389481
theorem B6568427 : Blo 2305435 6568427 := bstep (se 1 (by rfl) ⟨4926320, by rfl⟩ : syracuseStep 6568427 = 9852641) B9852641
theorem B4378951 : Blo 2305435 4378951 := bstep (se 1 (by rfl) ⟨3284213, by rfl⟩ : syracuseStep 4378951 = 6568427) B6568427
theorem B5838601 : Blo 2305435 5838601 := bstep (se 2 (by rfl) ⟨2189475, by rfl⟩ : syracuseStep 5838601 = 4378951) B4378951
theorem B7784801 : Blo 2305435 7784801 := bstep (se 2 (by rfl) ⟨2919300, by rfl⟩ : syracuseStep 7784801 = 5838601) B5838601
theorem B5189867 : Blo 2305435 5189867 := bstep (se 1 (by rfl) ⟨3892400, by rfl⟩ : syracuseStep 5189867 = 7784801) B7784801
theorem B3459911 : Blo 2305435 3459911 := bstep (se 1 (by rfl) ⟨2594933, by rfl⟩ : syracuseStep 3459911 = 5189867) B5189867
theorem B2306607 : Blo 2305435 2306607 := bstep (se 1 (by rfl) ⟨1729955, by rfl⟩ : syracuseStep 2306607 = 3459911) B3459911
theorem B3459917 : Blo 2305435 3459917 := bbase (se 3 (by rfl) ⟨648734, by rfl⟩ : syracuseStep 3459917 = 1297469) (by norm_num)
theorem B2306611 : Blo 2305435 2306611 := bstep (se 1 (by rfl) ⟨1729958, by rfl⟩ : syracuseStep 2306611 = 3459917) B3459917
theorem B5189885 : Blo 2305435 5189885 := bbase (se 3 (by rfl) ⟨973103, by rfl⟩ : syracuseStep 5189885 = 1946207) (by norm_num)
theorem B3459923 : Blo 2305435 3459923 := bstep (se 1 (by rfl) ⟨2594942, by rfl⟩ : syracuseStep 3459923 = 5189885) B5189885
theorem B2306615 : Blo 2305435 2306615 := bstep (se 1 (by rfl) ⟨1729961, by rfl⟩ : syracuseStep 2306615 = 3459923) B3459923
theorem B3892421 : Blo 2305435 3892421 := bbase (se 4 (by rfl) ⟨364914, by rfl⟩ : syracuseStep 3892421 = 729829) (by norm_num)
theorem B2594947 : Blo 2305435 2594947 := bstep (se 1 (by rfl) ⟨1946210, by rfl⟩ : syracuseStep 2594947 = 3892421) B3892421
theorem B3459929 : Blo 2305435 3459929 := bstep (se 2 (by rfl) ⟨1297473, by rfl⟩ : syracuseStep 3459929 = 2594947) B2594947
theorem B2306619 : Blo 2305435 2306619 := bstep (se 1 (by rfl) ⟨1729964, by rfl⟩ : syracuseStep 2306619 = 3459929) B3459929
theorem B17515925 : Blo 2305435 17515925 := bbase (se 6 (by rfl) ⟨410529, by rfl⟩ : syracuseStep 17515925 = 821059) (by norm_num)
theorem B11677283 : Blo 2305435 11677283 := bstep (se 1 (by rfl) ⟨8757962, by rfl⟩ : syracuseStep 11677283 = 17515925) B17515925
theorem B7784855 : Blo 2305435 7784855 := bstep (se 1 (by rfl) ⟨5838641, by rfl⟩ : syracuseStep 7784855 = 11677283) B11677283
theorem B5189903 : Blo 2305435 5189903 := bstep (se 1 (by rfl) ⟨3892427, by rfl⟩ : syracuseStep 5189903 = 7784855) B7784855
theorem B3459935 : Blo 2305435 3459935 := bstep (se 1 (by rfl) ⟨2594951, by rfl⟩ : syracuseStep 3459935 = 5189903) B5189903
theorem B2306623 : Blo 2305435 2306623 := bstep (se 1 (by rfl) ⟨1729967, by rfl⟩ : syracuseStep 2306623 = 3459935) B3459935
theorem B3459941 : Blo 2305435 3459941 := bbase (se 4 (by rfl) ⟨324369, by rfl⟩ : syracuseStep 3459941 = 648739) (by norm_num)
theorem B2306627 : Blo 2305435 2306627 := bstep (se 1 (by rfl) ⟨1729970, by rfl⟩ : syracuseStep 2306627 = 3459941) B3459941
theorem B4378997 : Blo 2305435 4378997 := bbase (se 5 (by rfl) ⟨205265, by rfl⟩ : syracuseStep 4378997 = 410531) (by norm_num)
theorem B2919331 : Blo 2305435 2919331 := bstep (se 1 (by rfl) ⟨2189498, by rfl⟩ : syracuseStep 2919331 = 4378997) B4378997
theorem B3892441 : Blo 2305435 3892441 := bstep (se 2 (by rfl) ⟨1459665, by rfl⟩ : syracuseStep 3892441 = 2919331) B2919331
theorem B5189921 : Blo 2305435 5189921 := bstep (se 2 (by rfl) ⟨1946220, by rfl⟩ : syracuseStep 5189921 = 3892441) B3892441
theorem B3459947 : Blo 2305435 3459947 := bstep (se 1 (by rfl) ⟨2594960, by rfl⟩ : syracuseStep 3459947 = 5189921) B5189921
theorem B2306631 : Blo 2305435 2306631 := bstep (se 1 (by rfl) ⟨1729973, by rfl⟩ : syracuseStep 2306631 = 3459947) B3459947
theorem B2594965 : Blo 2305435 2594965 := bbase (se 6 (by rfl) ⟨60819, by rfl⟩ : syracuseStep 2594965 = 121639) (by norm_num)
theorem B3459953 : Blo 2305435 3459953 := bstep (se 2 (by rfl) ⟨1297482, by rfl⟩ : syracuseStep 3459953 = 2594965) B2594965
theorem B2306635 : Blo 2305435 2306635 := bstep (se 1 (by rfl) ⟨1729976, by rfl⟩ : syracuseStep 2306635 = 3459953) B3459953
theorem B2919341 : Blo 2305435 2919341 := bbase (se 3 (by rfl) ⟨547376, by rfl⟩ : syracuseStep 2919341 = 1094753) (by norm_num)
theorem B7784909 : Blo 2305435 7784909 := bstep (se 3 (by rfl) ⟨1459670, by rfl⟩ : syracuseStep 7784909 = 2919341) B2919341
theorem B5189939 : Blo 2305435 5189939 := bstep (se 1 (by rfl) ⟨3892454, by rfl⟩ : syracuseStep 5189939 = 7784909) B7784909
theorem B3459959 : Blo 2305435 3459959 := bstep (se 1 (by rfl) ⟨2594969, by rfl⟩ : syracuseStep 3459959 = 5189939) B5189939
theorem B2306639 : Blo 2305435 2306639 := bstep (se 1 (by rfl) ⟨1729979, by rfl⟩ : syracuseStep 2306639 = 3459959) B3459959
theorem B3459965 : Blo 2305435 3459965 := bbase (se 3 (by rfl) ⟨648743, by rfl⟩ : syracuseStep 3459965 = 1297487) (by norm_num)
theorem B2306643 : Blo 2305435 2306643 := bstep (se 1 (by rfl) ⟨1729982, by rfl⟩ : syracuseStep 2306643 = 3459965) B3459965
theorem B5189957 : Blo 2305435 5189957 := bbase (se 4 (by rfl) ⟨486558, by rfl⟩ : syracuseStep 5189957 = 973117) (by norm_num)
theorem B3459971 : Blo 2305435 3459971 := bstep (se 1 (by rfl) ⟨2594978, by rfl⟩ : syracuseStep 3459971 = 5189957) B5189957
theorem B2306647 : Blo 2305435 2306647 := bstep (se 1 (by rfl) ⟨1729985, by rfl⟩ : syracuseStep 2306647 = 3459971) B3459971
theorem B2630389 : Blo 2305435 2630389 := bbase (se 5 (by rfl) ⟨123299, by rfl⟩ : syracuseStep 2630389 = 246599) (by norm_num)
theorem B3507185 : Blo 2305435 3507185 := bstep (se 2 (by rfl) ⟨1315194, by rfl⟩ : syracuseStep 3507185 = 2630389) B2630389
theorem B9352493 : Blo 2305435 9352493 := bstep (se 3 (by rfl) ⟨1753592, by rfl⟩ : syracuseStep 9352493 = 3507185) B3507185
theorem B6234995 : Blo 2305435 6234995 := bstep (se 1 (by rfl) ⟨4676246, by rfl⟩ : syracuseStep 6234995 = 9352493) B9352493
theorem B16626653 : Blo 2305435 16626653 := bstep (se 3 (by rfl) ⟨3117497, by rfl⟩ : syracuseStep 16626653 = 6234995) B6234995
theorem B11084435 : Blo 2305435 11084435 := bstep (se 1 (by rfl) ⟨8313326, by rfl⟩ : syracuseStep 11084435 = 16626653) B16626653
theorem B7389623 : Blo 2305435 7389623 := bstep (se 1 (by rfl) ⟨5542217, by rfl⟩ : syracuseStep 7389623 = 11084435) B11084435
theorem B4926415 : Blo 2305435 4926415 := bstep (se 1 (by rfl) ⟨3694811, by rfl⟩ : syracuseStep 4926415 = 7389623) B7389623
theorem B6568553 : Blo 2305435 6568553 := bstep (se 2 (by rfl) ⟨2463207, by rfl⟩ : syracuseStep 6568553 = 4926415) B4926415
theorem B4379035 : Blo 2305435 4379035 := bstep (se 1 (by rfl) ⟨3284276, by rfl⟩ : syracuseStep 4379035 = 6568553) B6568553
theorem B5838713 : Blo 2305435 5838713 := bstep (se 2 (by rfl) ⟨2189517, by rfl⟩ : syracuseStep 5838713 = 4379035) B4379035
theorem B3892475 : Blo 2305435 3892475 := bstep (se 1 (by rfl) ⟨2919356, by rfl⟩ : syracuseStep 3892475 = 5838713) B5838713
theorem B2594983 : Blo 2305435 2594983 := bstep (se 1 (by rfl) ⟨1946237, by rfl⟩ : syracuseStep 2594983 = 3892475) B3892475
theorem B3459977 : Blo 2305435 3459977 := bstep (se 2 (by rfl) ⟨1297491, by rfl⟩ : syracuseStep 3459977 = 2594983) B2594983
theorem B2306651 : Blo 2305435 2306651 := bstep (se 1 (by rfl) ⟨1729988, by rfl⟩ : syracuseStep 2306651 = 3459977) B3459977
theorem B11677445 : Blo 2305435 11677445 := bbase (se 4 (by rfl) ⟨1094760, by rfl⟩ : syracuseStep 11677445 = 2189521) (by norm_num)
theorem B7784963 : Blo 2305435 7784963 := bstep (se 1 (by rfl) ⟨5838722, by rfl⟩ : syracuseStep 7784963 = 11677445) B11677445
theorem B5189975 : Blo 2305435 5189975 := bstep (se 1 (by rfl) ⟨3892481, by rfl⟩ : syracuseStep 5189975 = 7784963) B7784963
theorem B3459983 : Blo 2305435 3459983 := bstep (se 1 (by rfl) ⟨2594987, by rfl⟩ : syracuseStep 3459983 = 5189975) B5189975
theorem B2306655 : Blo 2305435 2306655 := bstep (se 1 (by rfl) ⟨1729991, by rfl⟩ : syracuseStep 2306655 = 3459983) B3459983
theorem B3459989 : Blo 2305435 3459989 := bbase (se 6 (by rfl) ⟨81093, by rfl⟩ : syracuseStep 3459989 = 162187) (by norm_num)
theorem B2306659 : Blo 2305435 2306659 := bstep (se 1 (by rfl) ⟨1729994, by rfl⟩ : syracuseStep 2306659 = 3459989) B3459989
theorem B13137173 : Blo 2305435 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B8758115 : Blo 2305435 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B5838743 : Blo 2305435 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B3892495 : Blo 2305435 3892495 := bstep (se 1 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 3892495 = 5838743) B5838743
theorem B5189993 : Blo 2305435 5189993 := bstep (se 2 (by rfl) ⟨1946247, by rfl⟩ : syracuseStep 5189993 = 3892495) B3892495
theorem B3459995 : Blo 2305435 3459995 := bstep (se 1 (by rfl) ⟨2594996, by rfl⟩ : syracuseStep 3459995 = 5189993) B5189993
theorem B2306663 : Blo 2305435 2306663 := bstep (se 1 (by rfl) ⟨1729997, by rfl⟩ : syracuseStep 2306663 = 3459995) B3459995
theorem B2595001 : Blo 2305435 2595001 := bbase (se 2 (by rfl) ⟨973125, by rfl⟩ : syracuseStep 2595001 = 1946251) (by norm_num)
theorem B3460001 : Blo 2305435 3460001 := bstep (se 2 (by rfl) ⟨1297500, by rfl⟩ : syracuseStep 3460001 = 2595001) B2595001
theorem B2306667 : Blo 2305435 2306667 := bstep (se 1 (by rfl) ⟨1730000, by rfl⟩ : syracuseStep 2306667 = 3460001) B3460001
theorem B2808941 : Blo 2305435 2808941 := bbase (se 3 (by rfl) ⟨526676, by rfl⟩ : syracuseStep 2808941 = 1053353) (by norm_num)
theorem B29962037 : Blo 2305435 29962037 := bstep (se 5 (by rfl) ⟨1404470, by rfl⟩ : syracuseStep 29962037 = 2808941) B2808941
theorem B19974691 : Blo 2305435 19974691 := bstep (se 1 (by rfl) ⟨14981018, by rfl⟩ : syracuseStep 19974691 = 29962037) B29962037
theorem B26632921 : Blo 2305435 26632921 := bstep (se 2 (by rfl) ⟨9987345, by rfl⟩ : syracuseStep 26632921 = 19974691) B19974691
theorem B35510561 : Blo 2305435 35510561 := bstep (se 2 (by rfl) ⟨13316460, by rfl⟩ : syracuseStep 35510561 = 26632921) B26632921
theorem B23673707 : Blo 2305435 23673707 := bstep (se 1 (by rfl) ⟨17755280, by rfl⟩ : syracuseStep 23673707 = 35510561) B35510561
theorem B15782471 : Blo 2305435 15782471 := bstep (se 1 (by rfl) ⟨11836853, by rfl⟩ : syracuseStep 15782471 = 23673707) B23673707
theorem B10521647 : Blo 2305435 10521647 := bstep (se 1 (by rfl) ⟨7891235, by rfl⟩ : syracuseStep 10521647 = 15782471) B15782471
theorem B7014431 : Blo 2305435 7014431 := bstep (se 1 (by rfl) ⟨5260823, by rfl⟩ : syracuseStep 7014431 = 10521647) B10521647
theorem B4676287 : Blo 2305435 4676287 := bstep (se 1 (by rfl) ⟨3507215, by rfl⟩ : syracuseStep 4676287 = 7014431) B7014431
theorem B6235049 : Blo 2305435 6235049 := bstep (se 2 (by rfl) ⟨2338143, by rfl⟩ : syracuseStep 6235049 = 4676287) B4676287
theorem B4156699 : Blo 2305435 4156699 := bstep (se 1 (by rfl) ⟨3117524, by rfl⟩ : syracuseStep 4156699 = 6235049) B6235049
theorem B5542265 : Blo 2305435 5542265 := bstep (se 2 (by rfl) ⟨2078349, by rfl⟩ : syracuseStep 5542265 = 4156699) B4156699
theorem B3694843 : Blo 2305435 3694843 := bstep (se 1 (by rfl) ⟨2771132, by rfl⟩ : syracuseStep 3694843 = 5542265) B5542265
theorem B4926457 : Blo 2305435 4926457 := bstep (se 2 (by rfl) ⟨1847421, by rfl⟩ : syracuseStep 4926457 = 3694843) B3694843
theorem B6568609 : Blo 2305435 6568609 := bstep (se 2 (by rfl) ⟨2463228, by rfl⟩ : syracuseStep 6568609 = 4926457) B4926457
theorem B8758145 : Blo 2305435 8758145 := bstep (se 2 (by rfl) ⟨3284304, by rfl⟩ : syracuseStep 8758145 = 6568609) B6568609
theorem B5838763 : Blo 2305435 5838763 := bstep (se 1 (by rfl) ⟨4379072, by rfl⟩ : syracuseStep 5838763 = 8758145) B8758145
theorem B7785017 : Blo 2305435 7785017 := bstep (se 2 (by rfl) ⟨2919381, by rfl⟩ : syracuseStep 7785017 = 5838763) B5838763
theorem B5190011 : Blo 2305435 5190011 := bstep (se 1 (by rfl) ⟨3892508, by rfl⟩ : syracuseStep 5190011 = 7785017) B7785017
theorem B3460007 : Blo 2305435 3460007 := bstep (se 1 (by rfl) ⟨2595005, by rfl⟩ : syracuseStep 3460007 = 5190011) B5190011
theorem B2306671 : Blo 2305435 2306671 := bstep (se 1 (by rfl) ⟨1730003, by rfl⟩ : syracuseStep 2306671 = 3460007) B3460007
theorem B3460013 : Blo 2305435 3460013 := bbase (se 3 (by rfl) ⟨648752, by rfl⟩ : syracuseStep 3460013 = 1297505) (by norm_num)
theorem B2306675 : Blo 2305435 2306675 := bstep (se 1 (by rfl) ⟨1730006, by rfl⟩ : syracuseStep 2306675 = 3460013) B3460013
theorem B5190029 : Blo 2305435 5190029 := bbase (se 3 (by rfl) ⟨973130, by rfl⟩ : syracuseStep 5190029 = 1946261) (by norm_num)
theorem B3460019 : Blo 2305435 3460019 := bstep (se 1 (by rfl) ⟨2595014, by rfl⟩ : syracuseStep 3460019 = 5190029) B5190029
theorem B2306679 : Blo 2305435 2306679 := bstep (se 1 (by rfl) ⟨1730009, by rfl⟩ : syracuseStep 2306679 = 3460019) B3460019
theorem B2919397 : Blo 2305435 2919397 := bbase (se 4 (by rfl) ⟨273693, by rfl⟩ : syracuseStep 2919397 = 547387) (by norm_num)
theorem B3892529 : Blo 2305435 3892529 := bstep (se 2 (by rfl) ⟨1459698, by rfl⟩ : syracuseStep 3892529 = 2919397) B2919397
theorem B2595019 : Blo 2305435 2595019 := bstep (se 1 (by rfl) ⟨1946264, by rfl⟩ : syracuseStep 2595019 = 3892529) B3892529
theorem B3460025 : Blo 2305435 3460025 := bstep (se 2 (by rfl) ⟨1297509, by rfl⟩ : syracuseStep 3460025 = 2595019) B2595019
theorem B2306683 : Blo 2305435 2306683 := bstep (se 1 (by rfl) ⟨1730012, by rfl⟩ : syracuseStep 2306683 = 3460025) B3460025
theorem B2496853 : Blo 2305435 2496853 := bbase (se 10 (by rfl) ⟨3657, by rfl⟩ : syracuseStep 2496853 = 7315) (by norm_num)
theorem B3329137 : Blo 2305435 3329137 := bstep (se 2 (by rfl) ⟨1248426, by rfl⟩ : syracuseStep 3329137 = 2496853) B2496853
theorem B4438849 : Blo 2305435 4438849 := bstep (se 2 (by rfl) ⟨1664568, by rfl⟩ : syracuseStep 4438849 = 3329137) B3329137
theorem B5918465 : Blo 2305435 5918465 := bstep (se 2 (by rfl) ⟨2219424, by rfl⟩ : syracuseStep 5918465 = 4438849) B4438849
theorem B15782573 : Blo 2305435 15782573 := bstep (se 3 (by rfl) ⟨2959232, by rfl⟩ : syracuseStep 15782573 = 5918465) B5918465
theorem B42086861 : Blo 2305435 42086861 := bstep (se 3 (by rfl) ⟨7891286, by rfl⟩ : syracuseStep 42086861 = 15782573) B15782573
theorem B28057907 : Blo 2305435 28057907 := bstep (se 1 (by rfl) ⟨21043430, by rfl⟩ : syracuseStep 28057907 = 42086861) B42086861
theorem B18705271 : Blo 2305435 18705271 := bstep (se 1 (by rfl) ⟨14028953, by rfl⟩ : syracuseStep 18705271 = 28057907) B28057907
theorem B24940361 : Blo 2305435 24940361 := bstep (se 2 (by rfl) ⟨9352635, by rfl⟩ : syracuseStep 24940361 = 18705271) B18705271
theorem B16626907 : Blo 2305435 16626907 := bstep (se 1 (by rfl) ⟨12470180, by rfl⟩ : syracuseStep 16626907 = 24940361) B24940361
theorem B22169209 : Blo 2305435 22169209 := bstep (se 2 (by rfl) ⟨8313453, by rfl⟩ : syracuseStep 22169209 = 16626907) B16626907
theorem B29558945 : Blo 2305435 29558945 := bstep (se 2 (by rfl) ⟨11084604, by rfl⟩ : syracuseStep 29558945 = 22169209) B22169209
theorem B19705963 : Blo 2305435 19705963 := bstep (se 1 (by rfl) ⟨14779472, by rfl⟩ : syracuseStep 19705963 = 29558945) B29558945
theorem B26274617 : Blo 2305435 26274617 := bstep (se 2 (by rfl) ⟨9852981, by rfl⟩ : syracuseStep 26274617 = 19705963) B19705963
theorem B17516411 : Blo 2305435 17516411 := bstep (se 1 (by rfl) ⟨13137308, by rfl⟩ : syracuseStep 17516411 = 26274617) B26274617
theorem B11677607 : Blo 2305435 11677607 := bstep (se 1 (by rfl) ⟨8758205, by rfl⟩ : syracuseStep 11677607 = 17516411) B17516411
theorem B7785071 : Blo 2305435 7785071 := bstep (se 1 (by rfl) ⟨5838803, by rfl⟩ : syracuseStep 7785071 = 11677607) B11677607
theorem B5190047 : Blo 2305435 5190047 := bstep (se 1 (by rfl) ⟨3892535, by rfl⟩ : syracuseStep 5190047 = 7785071) B7785071
theorem B3460031 : Blo 2305435 3460031 := bstep (se 1 (by rfl) ⟨2595023, by rfl⟩ : syracuseStep 3460031 = 5190047) B5190047
theorem B2306687 : Blo 2305435 2306687 := bstep (se 1 (by rfl) ⟨1730015, by rfl⟩ : syracuseStep 2306687 = 3460031) B3460031
theorem B3460037 : Blo 2305435 3460037 := bbase (se 4 (by rfl) ⟨324378, by rfl⟩ : syracuseStep 3460037 = 648757) (by norm_num)
theorem B2306691 : Blo 2305435 2306691 := bstep (se 1 (by rfl) ⟨1730018, by rfl⟩ : syracuseStep 2306691 = 3460037) B3460037
theorem B3892549 : Blo 2305435 3892549 := bbase (se 4 (by rfl) ⟨364926, by rfl⟩ : syracuseStep 3892549 = 729853) (by norm_num)
theorem B5190065 : Blo 2305435 5190065 := bstep (se 2 (by rfl) ⟨1946274, by rfl⟩ : syracuseStep 5190065 = 3892549) B3892549
theorem B3460043 : Blo 2305435 3460043 := bstep (se 1 (by rfl) ⟨2595032, by rfl⟩ : syracuseStep 3460043 = 5190065) B5190065
theorem B2306695 : Blo 2305435 2306695 := bstep (se 1 (by rfl) ⟨1730021, by rfl⟩ : syracuseStep 2306695 = 3460043) B3460043
theorem B2595037 : Blo 2305435 2595037 := bbase (se 3 (by rfl) ⟨486569, by rfl⟩ : syracuseStep 2595037 = 973139) (by norm_num)
theorem B3460049 : Blo 2305435 3460049 := bstep (se 2 (by rfl) ⟨1297518, by rfl⟩ : syracuseStep 3460049 = 2595037) B2595037
theorem B2306699 : Blo 2305435 2306699 := bstep (se 1 (by rfl) ⟨1730024, by rfl⟩ : syracuseStep 2306699 = 3460049) B3460049
theorem B7785125 : Blo 2305435 7785125 := bbase (se 4 (by rfl) ⟨729855, by rfl⟩ : syracuseStep 7785125 = 1459711) (by norm_num)
theorem B5190083 : Blo 2305435 5190083 := bstep (se 1 (by rfl) ⟨3892562, by rfl⟩ : syracuseStep 5190083 = 7785125) B7785125
theorem B3460055 : Blo 2305435 3460055 := bstep (se 1 (by rfl) ⟨2595041, by rfl⟩ : syracuseStep 3460055 = 5190083) B5190083
theorem B2306703 : Blo 2305435 2306703 := bstep (se 1 (by rfl) ⟨1730027, by rfl⟩ : syracuseStep 2306703 = 3460055) B3460055
theorem B3460061 : Blo 2305435 3460061 := bbase (se 3 (by rfl) ⟨648761, by rfl⟩ : syracuseStep 3460061 = 1297523) (by norm_num)
theorem B2306707 : Blo 2305435 2306707 := bstep (se 1 (by rfl) ⟨1730030, by rfl⟩ : syracuseStep 2306707 = 3460061) B3460061
theorem B5190101 : Blo 2305435 5190101 := bbase (se 7 (by rfl) ⟨60821, by rfl⟩ : syracuseStep 5190101 = 121643) (by norm_num)
theorem B3460067 : Blo 2305435 3460067 := bstep (se 1 (by rfl) ⟨2595050, by rfl⟩ : syracuseStep 3460067 = 5190101) B5190101
theorem B2306711 : Blo 2305435 2306711 := bstep (se 1 (by rfl) ⟨1730033, by rfl⟩ : syracuseStep 2306711 = 3460067) B3460067
theorem B3555133 : Blo 2305435 3555133 := bbase (se 3 (by rfl) ⟨666587, by rfl⟩ : syracuseStep 3555133 = 1333175) (by norm_num)
theorem B75842837 : Blo 2305435 75842837 := bstep (se 6 (by rfl) ⟨1777566, by rfl⟩ : syracuseStep 75842837 = 3555133) B3555133
theorem B50561891 : Blo 2305435 50561891 := bstep (se 1 (by rfl) ⟨37921418, by rfl⟩ : syracuseStep 50561891 = 75842837) B75842837
theorem B33707927 : Blo 2305435 33707927 := bstep (se 1 (by rfl) ⟨25280945, by rfl⟩ : syracuseStep 33707927 = 50561891) B50561891
theorem B89887805 : Blo 2305435 89887805 := bstep (se 3 (by rfl) ⟨16853963, by rfl⟩ : syracuseStep 89887805 = 33707927) B33707927
theorem B59925203 : Blo 2305435 59925203 := bstep (se 1 (by rfl) ⟨44943902, by rfl⟩ : syracuseStep 59925203 = 89887805) B89887805
theorem B39950135 : Blo 2305435 39950135 := bstep (se 1 (by rfl) ⟨29962601, by rfl⟩ : syracuseStep 39950135 = 59925203) B59925203
theorem B26633423 : Blo 2305435 26633423 := bstep (se 1 (by rfl) ⟨19975067, by rfl⟩ : syracuseStep 26633423 = 39950135) B39950135
theorem B17755615 : Blo 2305435 17755615 := bstep (se 1 (by rfl) ⟨13316711, by rfl⟩ : syracuseStep 17755615 = 26633423) B26633423
theorem B23674153 : Blo 2305435 23674153 := bstep (se 2 (by rfl) ⟨8877807, by rfl⟩ : syracuseStep 23674153 = 17755615) B17755615
theorem B31565537 : Blo 2305435 31565537 := bstep (se 2 (by rfl) ⟨11837076, by rfl⟩ : syracuseStep 31565537 = 23674153) B23674153
theorem B21043691 : Blo 2305435 21043691 := bstep (se 1 (by rfl) ⟨15782768, by rfl⟩ : syracuseStep 21043691 = 31565537) B31565537
theorem B14029127 : Blo 2305435 14029127 := bstep (se 1 (by rfl) ⟨10521845, by rfl⟩ : syracuseStep 14029127 = 21043691) B21043691
theorem B9352751 : Blo 2305435 9352751 := bstep (se 1 (by rfl) ⟨7014563, by rfl⟩ : syracuseStep 9352751 = 14029127) B14029127
theorem B24940669 : Blo 2305435 24940669 := bstep (se 3 (by rfl) ⟨4676375, by rfl⟩ : syracuseStep 24940669 = 9352751) B9352751
theorem B33254225 : Blo 2305435 33254225 := bstep (se 2 (by rfl) ⟨12470334, by rfl⟩ : syracuseStep 33254225 = 24940669) B24940669
theorem B22169483 : Blo 2305435 22169483 := bstep (se 1 (by rfl) ⟨16627112, by rfl⟩ : syracuseStep 22169483 = 33254225) B33254225
theorem B14779655 : Blo 2305435 14779655 := bstep (se 1 (by rfl) ⟨11084741, by rfl⟩ : syracuseStep 14779655 = 22169483) B22169483
theorem B9853103 : Blo 2305435 9853103 := bstep (se 1 (by rfl) ⟨7389827, by rfl⟩ : syracuseStep 9853103 = 14779655) B14779655
theorem B6568735 : Blo 2305435 6568735 := bstep (se 1 (by rfl) ⟨4926551, by rfl⟩ : syracuseStep 6568735 = 9853103) B9853103
theorem B8758313 : Blo 2305435 8758313 := bstep (se 2 (by rfl) ⟨3284367, by rfl⟩ : syracuseStep 8758313 = 6568735) B6568735
theorem B5838875 : Blo 2305435 5838875 := bstep (se 1 (by rfl) ⟨4379156, by rfl⟩ : syracuseStep 5838875 = 8758313) B8758313
theorem B3892583 : Blo 2305435 3892583 := bstep (se 1 (by rfl) ⟨2919437, by rfl⟩ : syracuseStep 3892583 = 5838875) B5838875
theorem B2595055 : Blo 2305435 2595055 := bstep (se 1 (by rfl) ⟨1946291, by rfl⟩ : syracuseStep 2595055 = 3892583) B3892583
theorem B3460073 : Blo 2305435 3460073 := bstep (se 2 (by rfl) ⟨1297527, by rfl⟩ : syracuseStep 3460073 = 2595055) B2595055
theorem B2306715 : Blo 2305435 2306715 := bstep (se 1 (by rfl) ⟨1730036, by rfl⟩ : syracuseStep 2306715 = 3460073) B3460073
theorem B2402429 : Blo 2305435 2402429 := bbase (se 3 (by rfl) ⟨450455, by rfl⟩ : syracuseStep 2402429 = 900911) (by norm_num)
theorem B25625909 : Blo 2305435 25625909 := bstep (se 5 (by rfl) ⟨1201214, by rfl⟩ : syracuseStep 25625909 = 2402429) B2402429
theorem B17083939 : Blo 2305435 17083939 := bstep (se 1 (by rfl) ⟨12812954, by rfl⟩ : syracuseStep 17083939 = 25625909) B25625909
theorem B22778585 : Blo 2305435 22778585 := bstep (se 2 (by rfl) ⟨8541969, by rfl⟩ : syracuseStep 22778585 = 17083939) B17083939
theorem B15185723 : Blo 2305435 15185723 := bstep (se 1 (by rfl) ⟨11389292, by rfl⟩ : syracuseStep 15185723 = 22778585) B22778585
theorem B161981045 : Blo 2305435 161981045 := bstep (se 5 (by rfl) ⟨7592861, by rfl⟩ : syracuseStep 161981045 = 15185723) B15185723
theorem B107987363 : Blo 2305435 107987363 := bstep (se 1 (by rfl) ⟨80990522, by rfl⟩ : syracuseStep 107987363 = 161981045) B161981045
theorem B71991575 : Blo 2305435 71991575 := bstep (se 1 (by rfl) ⟨53993681, by rfl⟩ : syracuseStep 71991575 = 107987363) B107987363
theorem B47994383 : Blo 2305435 47994383 := bstep (se 1 (by rfl) ⟨35995787, by rfl⟩ : syracuseStep 47994383 = 71991575) B71991575
theorem B31996255 : Blo 2305435 31996255 := bstep (se 1 (by rfl) ⟨23997191, by rfl⟩ : syracuseStep 31996255 = 47994383) B47994383
theorem B42661673 : Blo 2305435 42661673 := bstep (se 2 (by rfl) ⟨15998127, by rfl⟩ : syracuseStep 42661673 = 31996255) B31996255
theorem B28441115 : Blo 2305435 28441115 := bstep (se 1 (by rfl) ⟨21330836, by rfl⟩ : syracuseStep 28441115 = 42661673) B42661673
theorem B18960743 : Blo 2305435 18960743 := bstep (se 1 (by rfl) ⟨14220557, by rfl⟩ : syracuseStep 18960743 = 28441115) B28441115
theorem B50561981 : Blo 2305435 50561981 := bstep (se 3 (by rfl) ⟨9480371, by rfl⟩ : syracuseStep 50561981 = 18960743) B18960743
theorem B33707987 : Blo 2305435 33707987 := bstep (se 1 (by rfl) ⟨25280990, by rfl⟩ : syracuseStep 33707987 = 50561981) B50561981
theorem B22471991 : Blo 2305435 22471991 := bstep (se 1 (by rfl) ⟨16853993, by rfl⟩ : syracuseStep 22471991 = 33707987) B33707987
theorem B14981327 : Blo 2305435 14981327 := bstep (se 1 (by rfl) ⟨11235995, by rfl⟩ : syracuseStep 14981327 = 22471991) B22471991
theorem B9987551 : Blo 2305435 9987551 := bstep (se 1 (by rfl) ⟨7490663, by rfl⟩ : syracuseStep 9987551 = 14981327) B14981327
theorem B6658367 : Blo 2305435 6658367 := bstep (se 1 (by rfl) ⟨4993775, by rfl⟩ : syracuseStep 6658367 = 9987551) B9987551
theorem B17755645 : Blo 2305435 17755645 := bstep (se 3 (by rfl) ⟨3329183, by rfl⟩ : syracuseStep 17755645 = 6658367) B6658367
theorem B23674193 : Blo 2305435 23674193 := bstep (se 2 (by rfl) ⟨8877822, by rfl⟩ : syracuseStep 23674193 = 17755645) B17755645
theorem B15782795 : Blo 2305435 15782795 := bstep (se 1 (by rfl) ⟨11837096, by rfl⟩ : syracuseStep 15782795 = 23674193) B23674193
theorem B10521863 : Blo 2305435 10521863 := bstep (se 1 (by rfl) ⟨7891397, by rfl⟩ : syracuseStep 10521863 = 15782795) B15782795
theorem B7014575 : Blo 2305435 7014575 := bstep (se 1 (by rfl) ⟨5260931, by rfl⟩ : syracuseStep 7014575 = 10521863) B10521863
theorem B4676383 : Blo 2305435 4676383 := bstep (se 1 (by rfl) ⟨3507287, by rfl⟩ : syracuseStep 4676383 = 7014575) B7014575
theorem B24940709 : Blo 2305435 24940709 := bstep (se 4 (by rfl) ⟨2338191, by rfl⟩ : syracuseStep 24940709 = 4676383) B4676383
theorem B16627139 : Blo 2305435 16627139 := bstep (se 1 (by rfl) ⟨12470354, by rfl⟩ : syracuseStep 16627139 = 24940709) B24940709
theorem B11084759 : Blo 2305435 11084759 := bstep (se 1 (by rfl) ⟨8313569, by rfl⟩ : syracuseStep 11084759 = 16627139) B16627139
theorem B7389839 : Blo 2305435 7389839 := bstep (se 1 (by rfl) ⟨5542379, by rfl⟩ : syracuseStep 7389839 = 11084759) B11084759
theorem B19706237 : Blo 2305435 19706237 := bstep (se 3 (by rfl) ⟨3694919, by rfl⟩ : syracuseStep 19706237 = 7389839) B7389839
theorem B13137491 : Blo 2305435 13137491 := bstep (se 1 (by rfl) ⟨9853118, by rfl⟩ : syracuseStep 13137491 = 19706237) B19706237
theorem B8758327 : Blo 2305435 8758327 := bstep (se 1 (by rfl) ⟨6568745, by rfl⟩ : syracuseStep 8758327 = 13137491) B13137491
theorem B11677769 : Blo 2305435 11677769 := bstep (se 2 (by rfl) ⟨4379163, by rfl⟩ : syracuseStep 11677769 = 8758327) B8758327
theorem B7785179 : Blo 2305435 7785179 := bstep (se 1 (by rfl) ⟨5838884, by rfl⟩ : syracuseStep 7785179 = 11677769) B11677769
theorem B5190119 : Blo 2305435 5190119 := bstep (se 1 (by rfl) ⟨3892589, by rfl⟩ : syracuseStep 5190119 = 7785179) B7785179
theorem B3460079 : Blo 2305435 3460079 := bstep (se 1 (by rfl) ⟨2595059, by rfl⟩ : syracuseStep 3460079 = 5190119) B5190119
theorem B2306719 : Blo 2305435 2306719 := bstep (se 1 (by rfl) ⟨1730039, by rfl⟩ : syracuseStep 2306719 = 3460079) B3460079
theorem B3460085 : Blo 2305435 3460085 := bbase (se 5 (by rfl) ⟨162191, by rfl⟩ : syracuseStep 3460085 = 324383) (by norm_num)
theorem B2306723 : Blo 2305435 2306723 := bstep (se 1 (by rfl) ⟨1730042, by rfl⟩ : syracuseStep 2306723 = 3460085) B3460085
theorem B3694933 : Blo 2305435 3694933 := bbase (se 10 (by rfl) ⟨5412, by rfl⟩ : syracuseStep 3694933 = 10825) (by norm_num)
theorem B4926577 : Blo 2305435 4926577 := bstep (se 2 (by rfl) ⟨1847466, by rfl⟩ : syracuseStep 4926577 = 3694933) B3694933
theorem B6568769 : Blo 2305435 6568769 := bstep (se 2 (by rfl) ⟨2463288, by rfl⟩ : syracuseStep 6568769 = 4926577) B4926577
theorem B4379179 : Blo 2305435 4379179 := bstep (se 1 (by rfl) ⟨3284384, by rfl⟩ : syracuseStep 4379179 = 6568769) B6568769
theorem B5838905 : Blo 2305435 5838905 := bstep (se 2 (by rfl) ⟨2189589, by rfl⟩ : syracuseStep 5838905 = 4379179) B4379179
theorem B3892603 : Blo 2305435 3892603 := bstep (se 1 (by rfl) ⟨2919452, by rfl⟩ : syracuseStep 3892603 = 5838905) B5838905
theorem B5190137 : Blo 2305435 5190137 := bstep (se 2 (by rfl) ⟨1946301, by rfl⟩ : syracuseStep 5190137 = 3892603) B3892603
theorem B3460091 : Blo 2305435 3460091 := bstep (se 1 (by rfl) ⟨2595068, by rfl⟩ : syracuseStep 3460091 = 5190137) B5190137
theorem B2306727 : Blo 2305435 2306727 := bstep (se 1 (by rfl) ⟨1730045, by rfl⟩ : syracuseStep 2306727 = 3460091) B3460091
theorem B2595073 : Blo 2305435 2595073 := bbase (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) (by norm_num)
theorem B3460097 : Blo 2305435 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B2306731 : Blo 2305435 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B5838925 : Blo 2305435 5838925 := bbase (se 3 (by rfl) ⟨1094798, by rfl⟩ : syracuseStep 5838925 = 2189597) (by norm_num)
theorem B7785233 : Blo 2305435 7785233 := bstep (se 2 (by rfl) ⟨2919462, by rfl⟩ : syracuseStep 7785233 = 5838925) B5838925
theorem B5190155 : Blo 2305435 5190155 := bstep (se 1 (by rfl) ⟨3892616, by rfl⟩ : syracuseStep 5190155 = 7785233) B7785233
theorem B3460103 : Blo 2305435 3460103 := bstep (se 1 (by rfl) ⟨2595077, by rfl⟩ : syracuseStep 3460103 = 5190155) B5190155
theorem B2306735 : Blo 2305435 2306735 := bstep (se 1 (by rfl) ⟨1730051, by rfl⟩ : syracuseStep 2306735 = 3460103) B3460103
theorem B3460109 : Blo 2305435 3460109 := bbase (se 3 (by rfl) ⟨648770, by rfl⟩ : syracuseStep 3460109 = 1297541) (by norm_num)
theorem B2306739 : Blo 2305435 2306739 := bstep (se 1 (by rfl) ⟨1730054, by rfl⟩ : syracuseStep 2306739 = 3460109) B3460109
theorem B5190173 : Blo 2305435 5190173 := bbase (se 3 (by rfl) ⟨973157, by rfl⟩ : syracuseStep 5190173 = 1946315) (by norm_num)
theorem B3460115 : Blo 2305435 3460115 := bstep (se 1 (by rfl) ⟨2595086, by rfl⟩ : syracuseStep 3460115 = 5190173) B5190173
theorem B2306743 : Blo 2305435 2306743 := bstep (se 1 (by rfl) ⟨1730057, by rfl⟩ : syracuseStep 2306743 = 3460115) B3460115
theorem B3892637 : Blo 2305435 3892637 := bbase (se 3 (by rfl) ⟨729869, by rfl⟩ : syracuseStep 3892637 = 1459739) (by norm_num)
theorem B2595091 : Blo 2305435 2595091 := bstep (se 1 (by rfl) ⟨1946318, by rfl⟩ : syracuseStep 2595091 = 3892637) B3892637
theorem B3460121 : Blo 2305435 3460121 := bstep (se 2 (by rfl) ⟨1297545, by rfl⟩ : syracuseStep 3460121 = 2595091) B2595091
theorem B2306747 : Blo 2305435 2306747 := bstep (se 1 (by rfl) ⟨1730060, by rfl⟩ : syracuseStep 2306747 = 3460121) B3460121
theorem B30371861 : Blo 2305435 30371861 := bbase (se 6 (by rfl) ⟨711840, by rfl⟩ : syracuseStep 30371861 = 1423681) (by norm_num)
theorem B20247907 : Blo 2305435 20247907 := bstep (se 1 (by rfl) ⟨15185930, by rfl⟩ : syracuseStep 20247907 = 30371861) B30371861
theorem B26997209 : Blo 2305435 26997209 := bstep (se 2 (by rfl) ⟨10123953, by rfl⟩ : syracuseStep 26997209 = 20247907) B20247907
theorem B17998139 : Blo 2305435 17998139 := bstep (se 1 (by rfl) ⟨13498604, by rfl⟩ : syracuseStep 17998139 = 26997209) B26997209
theorem B47995037 : Blo 2305435 47995037 := bstep (se 3 (by rfl) ⟨8999069, by rfl⟩ : syracuseStep 47995037 = 17998139) B17998139
theorem B31996691 : Blo 2305435 31996691 := bstep (se 1 (by rfl) ⟨23997518, by rfl⟩ : syracuseStep 31996691 = 47995037) B47995037
theorem B21331127 : Blo 2305435 21331127 := bstep (se 1 (by rfl) ⟨15998345, by rfl⟩ : syracuseStep 21331127 = 31996691) B31996691
theorem B56883005 : Blo 2305435 56883005 := bstep (se 3 (by rfl) ⟨10665563, by rfl⟩ : syracuseStep 56883005 = 21331127) B21331127
theorem B37922003 : Blo 2305435 37922003 := bstep (se 1 (by rfl) ⟨28441502, by rfl⟩ : syracuseStep 37922003 = 56883005) B56883005
theorem B25281335 : Blo 2305435 25281335 := bstep (se 1 (by rfl) ⟨18961001, by rfl⟩ : syracuseStep 25281335 = 37922003) B37922003
theorem B16854223 : Blo 2305435 16854223 := bstep (se 1 (by rfl) ⟨12640667, by rfl⟩ : syracuseStep 16854223 = 25281335) B25281335
theorem B22472297 : Blo 2305435 22472297 := bstep (se 2 (by rfl) ⟨8427111, by rfl⟩ : syracuseStep 22472297 = 16854223) B16854223
theorem B14981531 : Blo 2305435 14981531 := bstep (se 1 (by rfl) ⟨11236148, by rfl⟩ : syracuseStep 14981531 = 22472297) B22472297
theorem B39950749 : Blo 2305435 39950749 := bstep (se 3 (by rfl) ⟨7490765, by rfl⟩ : syracuseStep 39950749 = 14981531) B14981531
theorem B213070661 : Blo 2305435 213070661 := bstep (se 4 (by rfl) ⟨19975374, by rfl⟩ : syracuseStep 213070661 = 39950749) B39950749
theorem B142047107 : Blo 2305435 142047107 := bstep (se 1 (by rfl) ⟨106535330, by rfl⟩ : syracuseStep 142047107 = 213070661) B213070661
theorem B94698071 : Blo 2305435 94698071 := bstep (se 1 (by rfl) ⟨71023553, by rfl⟩ : syracuseStep 94698071 = 142047107) B142047107
theorem B63132047 : Blo 2305435 63132047 := bstep (se 1 (by rfl) ⟨47349035, by rfl⟩ : syracuseStep 63132047 = 94698071) B94698071
theorem B42088031 : Blo 2305435 42088031 := bstep (se 1 (by rfl) ⟨31566023, by rfl⟩ : syracuseStep 42088031 = 63132047) B63132047
theorem B28058687 : Blo 2305435 28058687 := bstep (se 1 (by rfl) ⟨21044015, by rfl⟩ : syracuseStep 28058687 = 42088031) B42088031
theorem B18705791 : Blo 2305435 18705791 := bstep (se 1 (by rfl) ⟨14029343, by rfl⟩ : syracuseStep 18705791 = 28058687) B28058687
theorem B12470527 : Blo 2305435 12470527 := bstep (se 1 (by rfl) ⟨9352895, by rfl⟩ : syracuseStep 12470527 = 18705791) B18705791
theorem B16627369 : Blo 2305435 16627369 := bstep (se 2 (by rfl) ⟨6235263, by rfl⟩ : syracuseStep 16627369 = 12470527) B12470527
theorem B22169825 : Blo 2305435 22169825 := bstep (se 2 (by rfl) ⟨8313684, by rfl⟩ : syracuseStep 22169825 = 16627369) B16627369
theorem B14779883 : Blo 2305435 14779883 := bstep (se 1 (by rfl) ⟨11084912, by rfl⟩ : syracuseStep 14779883 = 22169825) B22169825
theorem B9853255 : Blo 2305435 9853255 := bstep (se 1 (by rfl) ⟨7389941, by rfl⟩ : syracuseStep 9853255 = 14779883) B14779883
theorem B13137673 : Blo 2305435 13137673 := bstep (se 2 (by rfl) ⟨4926627, by rfl⟩ : syracuseStep 13137673 = 9853255) B9853255
theorem B17516897 : Blo 2305435 17516897 := bstep (se 2 (by rfl) ⟨6568836, by rfl⟩ : syracuseStep 17516897 = 13137673) B13137673
theorem B11677931 : Blo 2305435 11677931 := bstep (se 1 (by rfl) ⟨8758448, by rfl⟩ : syracuseStep 11677931 = 17516897) B17516897
theorem B7785287 : Blo 2305435 7785287 := bstep (se 1 (by rfl) ⟨5838965, by rfl⟩ : syracuseStep 7785287 = 11677931) B11677931
theorem B5190191 : Blo 2305435 5190191 := bstep (se 1 (by rfl) ⟨3892643, by rfl⟩ : syracuseStep 5190191 = 7785287) B7785287
theorem B3460127 : Blo 2305435 3460127 := bstep (se 1 (by rfl) ⟨2595095, by rfl⟩ : syracuseStep 3460127 = 5190191) B5190191
theorem B2306751 : Blo 2305435 2306751 := bstep (se 1 (by rfl) ⟨1730063, by rfl⟩ : syracuseStep 2306751 = 3460127) B3460127
theorem B3460133 : Blo 2305435 3460133 := bbase (se 4 (by rfl) ⟨324387, by rfl⟩ : syracuseStep 3460133 = 648775) (by norm_num)
theorem B2306755 : Blo 2305435 2306755 := bstep (se 1 (by rfl) ⟨1730066, by rfl⟩ : syracuseStep 2306755 = 3460133) B3460133
theorem B2919493 : Blo 2305435 2919493 := bbase (se 4 (by rfl) ⟨273702, by rfl⟩ : syracuseStep 2919493 = 547405) (by norm_num)
theorem B3892657 : Blo 2305435 3892657 := bstep (se 2 (by rfl) ⟨1459746, by rfl⟩ : syracuseStep 3892657 = 2919493) B2919493
theorem B5190209 : Blo 2305435 5190209 := bstep (se 2 (by rfl) ⟨1946328, by rfl⟩ : syracuseStep 5190209 = 3892657) B3892657
theorem B3460139 : Blo 2305435 3460139 := bstep (se 1 (by rfl) ⟨2595104, by rfl⟩ : syracuseStep 3460139 = 5190209) B5190209
theorem B2306759 : Blo 2305435 2306759 := bstep (se 1 (by rfl) ⟨1730069, by rfl⟩ : syracuseStep 2306759 = 3460139) B3460139
theorem B2595109 : Blo 2305435 2595109 := bbase (se 4 (by rfl) ⟨243291, by rfl⟩ : syracuseStep 2595109 = 486583) (by norm_num)
theorem B3460145 : Blo 2305435 3460145 := bstep (se 2 (by rfl) ⟨1297554, by rfl⟩ : syracuseStep 3460145 = 2595109) B2595109
theorem B2306763 : Blo 2305435 2306763 := bstep (se 1 (by rfl) ⟨1730072, by rfl⟩ : syracuseStep 2306763 = 3460145) B3460145
theorem B3694997 : Blo 2305435 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B9853325 : Blo 2305435 9853325 := bstep (se 3 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 9853325 = 3694997) B3694997
theorem B6568883 : Blo 2305435 6568883 := bstep (se 1 (by rfl) ⟨4926662, by rfl⟩ : syracuseStep 6568883 = 9853325) B9853325
theorem B4379255 : Blo 2305435 4379255 := bstep (se 1 (by rfl) ⟨3284441, by rfl⟩ : syracuseStep 4379255 = 6568883) B6568883
theorem B2919503 : Blo 2305435 2919503 := bstep (se 1 (by rfl) ⟨2189627, by rfl⟩ : syracuseStep 2919503 = 4379255) B4379255
theorem B7785341 : Blo 2305435 7785341 := bstep (se 3 (by rfl) ⟨1459751, by rfl⟩ : syracuseStep 7785341 = 2919503) B2919503
theorem B5190227 : Blo 2305435 5190227 := bstep (se 1 (by rfl) ⟨3892670, by rfl⟩ : syracuseStep 5190227 = 7785341) B7785341
theorem B3460151 : Blo 2305435 3460151 := bstep (se 1 (by rfl) ⟨2595113, by rfl⟩ : syracuseStep 3460151 = 5190227) B5190227
theorem B2306767 : Blo 2305435 2306767 := bstep (se 1 (by rfl) ⟨1730075, by rfl⟩ : syracuseStep 2306767 = 3460151) B3460151
theorem B3460157 : Blo 2305435 3460157 := bbase (se 3 (by rfl) ⟨648779, by rfl⟩ : syracuseStep 3460157 = 1297559) (by norm_num)
theorem B2306771 : Blo 2305435 2306771 := bstep (se 1 (by rfl) ⟨1730078, by rfl⟩ : syracuseStep 2306771 = 3460157) B3460157
theorem B5190245 : Blo 2305435 5190245 := bbase (se 4 (by rfl) ⟨486585, by rfl⟩ : syracuseStep 5190245 = 973171) (by norm_num)
theorem B3460163 : Blo 2305435 3460163 := bstep (se 1 (by rfl) ⟨2595122, by rfl⟩ : syracuseStep 3460163 = 5190245) B5190245
theorem B2306775 : Blo 2305435 2306775 := bstep (se 1 (by rfl) ⟨1730081, by rfl⟩ : syracuseStep 2306775 = 3460163) B3460163
theorem B5839037 : Blo 2305435 5839037 := bbase (se 3 (by rfl) ⟨1094819, by rfl⟩ : syracuseStep 5839037 = 2189639) (by norm_num)
theorem B3892691 : Blo 2305435 3892691 := bstep (se 1 (by rfl) ⟨2919518, by rfl⟩ : syracuseStep 3892691 = 5839037) B5839037
theorem B2595127 : Blo 2305435 2595127 := bstep (se 1 (by rfl) ⟨1946345, by rfl⟩ : syracuseStep 2595127 = 3892691) B3892691
theorem B3460169 : Blo 2305435 3460169 := bstep (se 2 (by rfl) ⟨1297563, by rfl⟩ : syracuseStep 3460169 = 2595127) B2595127
theorem B2306779 : Blo 2305435 2306779 := bstep (se 1 (by rfl) ⟨1730084, by rfl⟩ : syracuseStep 2306779 = 3460169) B3460169
theorem B4379285 : Blo 2305435 4379285 := bbase (se 6 (by rfl) ⟨102639, by rfl⟩ : syracuseStep 4379285 = 205279) (by norm_num)
theorem B11678093 : Blo 2305435 11678093 := bstep (se 3 (by rfl) ⟨2189642, by rfl⟩ : syracuseStep 11678093 = 4379285) B4379285
theorem B7785395 : Blo 2305435 7785395 := bstep (se 1 (by rfl) ⟨5839046, by rfl⟩ : syracuseStep 7785395 = 11678093) B11678093
theorem B5190263 : Blo 2305435 5190263 := bstep (se 1 (by rfl) ⟨3892697, by rfl⟩ : syracuseStep 5190263 = 7785395) B7785395
theorem B3460175 : Blo 2305435 3460175 := bstep (se 1 (by rfl) ⟨2595131, by rfl⟩ : syracuseStep 3460175 = 5190263) B5190263
theorem B2306783 : Blo 2305435 2306783 := bstep (se 1 (by rfl) ⟨1730087, by rfl⟩ : syracuseStep 2306783 = 3460175) B3460175
theorem B3460181 : Blo 2305435 3460181 := bbase (se 8 (by rfl) ⟨20274, by rfl⟩ : syracuseStep 3460181 = 40549) (by norm_num)
theorem B2306787 : Blo 2305435 2306787 := bstep (se 1 (by rfl) ⟨1730090, by rfl⟩ : syracuseStep 2306787 = 3460181) B3460181
theorem B2338265 : Blo 2305435 2338265 := bbase (se 2 (by rfl) ⟨876849, by rfl⟩ : syracuseStep 2338265 = 1753699) (by norm_num)
theorem B6235373 : Blo 2305435 6235373 := bstep (se 3 (by rfl) ⟨1169132, by rfl⟩ : syracuseStep 6235373 = 2338265) B2338265
theorem B4156915 : Blo 2305435 4156915 := bstep (se 1 (by rfl) ⟨3117686, by rfl⟩ : syracuseStep 4156915 = 6235373) B6235373
theorem B5542553 : Blo 2305435 5542553 := bstep (se 2 (by rfl) ⟨2078457, by rfl⟩ : syracuseStep 5542553 = 4156915) B4156915
theorem B14780141 : Blo 2305435 14780141 := bstep (se 3 (by rfl) ⟨2771276, by rfl⟩ : syracuseStep 14780141 = 5542553) B5542553
theorem B9853427 : Blo 2305435 9853427 := bstep (se 1 (by rfl) ⟨7390070, by rfl⟩ : syracuseStep 9853427 = 14780141) B14780141
theorem B6568951 : Blo 2305435 6568951 := bstep (se 1 (by rfl) ⟨4926713, by rfl⟩ : syracuseStep 6568951 = 9853427) B9853427
theorem B8758601 : Blo 2305435 8758601 := bstep (se 2 (by rfl) ⟨3284475, by rfl⟩ : syracuseStep 8758601 = 6568951) B6568951
theorem B5839067 : Blo 2305435 5839067 := bstep (se 1 (by rfl) ⟨4379300, by rfl⟩ : syracuseStep 5839067 = 8758601) B8758601
theorem B3892711 : Blo 2305435 3892711 := bstep (se 1 (by rfl) ⟨2919533, by rfl⟩ : syracuseStep 3892711 = 5839067) B5839067
theorem B5190281 : Blo 2305435 5190281 := bstep (se 2 (by rfl) ⟨1946355, by rfl⟩ : syracuseStep 5190281 = 3892711) B3892711
theorem B3460187 : Blo 2305435 3460187 := bstep (se 1 (by rfl) ⟨2595140, by rfl⟩ : syracuseStep 3460187 = 5190281) B5190281
theorem B2306791 : Blo 2305435 2306791 := bstep (se 1 (by rfl) ⟨1730093, by rfl⟩ : syracuseStep 2306791 = 3460187) B3460187
theorem B2595145 : Blo 2305435 2595145 := bbase (se 2 (by rfl) ⟨973179, by rfl⟩ : syracuseStep 2595145 = 1946359) (by norm_num)
theorem B3460193 : Blo 2305435 3460193 := bstep (se 2 (by rfl) ⟨1297572, by rfl⟩ : syracuseStep 3460193 = 2595145) B2595145
theorem B2306795 : Blo 2305435 2306795 := bstep (se 1 (by rfl) ⟨1730096, by rfl⟩ : syracuseStep 2306795 = 3460193) B3460193
theorem B4993949 : Blo 2305435 4993949 := bbase (se 3 (by rfl) ⟨936365, by rfl⟩ : syracuseStep 4993949 = 1872731) (by norm_num)
theorem B3329299 : Blo 2305435 3329299 := bstep (se 1 (by rfl) ⟨2496974, by rfl⟩ : syracuseStep 3329299 = 4993949) B4993949
theorem B4439065 : Blo 2305435 4439065 := bstep (se 2 (by rfl) ⟨1664649, by rfl⟩ : syracuseStep 4439065 = 3329299) B3329299
theorem B5918753 : Blo 2305435 5918753 := bstep (se 2 (by rfl) ⟨2219532, by rfl⟩ : syracuseStep 5918753 = 4439065) B4439065
theorem B3945835 : Blo 2305435 3945835 := bstep (se 1 (by rfl) ⟨2959376, by rfl⟩ : syracuseStep 3945835 = 5918753) B5918753
theorem B21044453 : Blo 2305435 21044453 := bstep (se 4 (by rfl) ⟨1972917, by rfl⟩ : syracuseStep 21044453 = 3945835) B3945835
theorem B56118541 : Blo 2305435 56118541 := bstep (se 3 (by rfl) ⟨10522226, by rfl⟩ : syracuseStep 56118541 = 21044453) B21044453
theorem B74824721 : Blo 2305435 74824721 := bstep (se 2 (by rfl) ⟨28059270, by rfl⟩ : syracuseStep 74824721 = 56118541) B56118541
theorem B49883147 : Blo 2305435 49883147 := bstep (se 1 (by rfl) ⟨37412360, by rfl⟩ : syracuseStep 49883147 = 74824721) B74824721
theorem B33255431 : Blo 2305435 33255431 := bstep (se 1 (by rfl) ⟨24941573, by rfl⟩ : syracuseStep 33255431 = 49883147) B49883147
theorem B22170287 : Blo 2305435 22170287 := bstep (se 1 (by rfl) ⟨16627715, by rfl⟩ : syracuseStep 22170287 = 33255431) B33255431
theorem B14780191 : Blo 2305435 14780191 := bstep (se 1 (by rfl) ⟨11085143, by rfl⟩ : syracuseStep 14780191 = 22170287) B22170287
theorem B19706921 : Blo 2305435 19706921 := bstep (se 2 (by rfl) ⟨7390095, by rfl⟩ : syracuseStep 19706921 = 14780191) B14780191
theorem B13137947 : Blo 2305435 13137947 := bstep (se 1 (by rfl) ⟨9853460, by rfl⟩ : syracuseStep 13137947 = 19706921) B19706921
theorem B8758631 : Blo 2305435 8758631 := bstep (se 1 (by rfl) ⟨6568973, by rfl⟩ : syracuseStep 8758631 = 13137947) B13137947
theorem B5839087 : Blo 2305435 5839087 := bstep (se 1 (by rfl) ⟨4379315, by rfl⟩ : syracuseStep 5839087 = 8758631) B8758631
theorem B7785449 : Blo 2305435 7785449 := bstep (se 2 (by rfl) ⟨2919543, by rfl⟩ : syracuseStep 7785449 = 5839087) B5839087
theorem B5190299 : Blo 2305435 5190299 := bstep (se 1 (by rfl) ⟨3892724, by rfl⟩ : syracuseStep 5190299 = 7785449) B7785449
theorem B3460199 : Blo 2305435 3460199 := bstep (se 1 (by rfl) ⟨2595149, by rfl⟩ : syracuseStep 3460199 = 5190299) B5190299
theorem B2306799 : Blo 2305435 2306799 := bstep (se 1 (by rfl) ⟨1730099, by rfl⟩ : syracuseStep 2306799 = 3460199) B3460199
theorem B3460205 : Blo 2305435 3460205 := bbase (se 3 (by rfl) ⟨648788, by rfl⟩ : syracuseStep 3460205 = 1297577) (by norm_num)
theorem B2306803 : Blo 2305435 2306803 := bstep (se 1 (by rfl) ⟨1730102, by rfl⟩ : syracuseStep 2306803 = 3460205) B3460205
theorem B5190317 : Blo 2305435 5190317 := bbase (se 3 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 5190317 = 1946369) (by norm_num)
theorem B3460211 : Blo 2305435 3460211 := bstep (se 1 (by rfl) ⟨2595158, by rfl⟩ : syracuseStep 3460211 = 5190317) B5190317
theorem B2306807 : Blo 2305435 2306807 := bstep (se 1 (by rfl) ⟨1730105, by rfl⟩ : syracuseStep 2306807 = 3460211) B3460211
theorem B4926757 : Blo 2305435 4926757 := bbase (se 4 (by rfl) ⟨461883, by rfl⟩ : syracuseStep 4926757 = 923767) (by norm_num)
theorem B6569009 : Blo 2305435 6569009 := bstep (se 2 (by rfl) ⟨2463378, by rfl⟩ : syracuseStep 6569009 = 4926757) B4926757
theorem B4379339 : Blo 2305435 4379339 := bstep (se 1 (by rfl) ⟨3284504, by rfl⟩ : syracuseStep 4379339 = 6569009) B6569009
theorem B2919559 : Blo 2305435 2919559 := bstep (se 1 (by rfl) ⟨2189669, by rfl⟩ : syracuseStep 2919559 = 4379339) B4379339
theorem B3892745 : Blo 2305435 3892745 := bstep (se 2 (by rfl) ⟨1459779, by rfl⟩ : syracuseStep 3892745 = 2919559) B2919559
theorem B2595163 : Blo 2305435 2595163 := bstep (se 1 (by rfl) ⟨1946372, by rfl⟩ : syracuseStep 2595163 = 3892745) B3892745
theorem B3460217 : Blo 2305435 3460217 := bstep (se 2 (by rfl) ⟨1297581, by rfl⟩ : syracuseStep 3460217 = 2595163) B2595163
theorem B2306811 : Blo 2305435 2306811 := bstep (se 1 (by rfl) ⟨1730108, by rfl⟩ : syracuseStep 2306811 = 3460217) B3460217
theorem B2999773 : Blo 2305435 2999773 := bbase (se 3 (by rfl) ⟨562457, by rfl⟩ : syracuseStep 2999773 = 1124915) (by norm_num)
theorem B15998789 : Blo 2305435 15998789 := bstep (se 4 (by rfl) ⟨1499886, by rfl⟩ : syracuseStep 15998789 = 2999773) B2999773
theorem B10665859 : Blo 2305435 10665859 := bstep (se 1 (by rfl) ⟨7999394, by rfl⟩ : syracuseStep 10665859 = 15998789) B15998789
theorem B14221145 : Blo 2305435 14221145 := bstep (se 2 (by rfl) ⟨5332929, by rfl⟩ : syracuseStep 14221145 = 10665859) B10665859
theorem B9480763 : Blo 2305435 9480763 := bstep (se 1 (by rfl) ⟨7110572, by rfl⟩ : syracuseStep 9480763 = 14221145) B14221145
theorem B12641017 : Blo 2305435 12641017 := bstep (se 2 (by rfl) ⟨4740381, by rfl⟩ : syracuseStep 12641017 = 9480763) B9480763
theorem B16854689 : Blo 2305435 16854689 := bstep (se 2 (by rfl) ⟨6320508, by rfl⟩ : syracuseStep 16854689 = 12641017) B12641017
theorem B44945837 : Blo 2305435 44945837 := bstep (se 3 (by rfl) ⟨8427344, by rfl⟩ : syracuseStep 44945837 = 16854689) B16854689
theorem B29963891 : Blo 2305435 29963891 := bstep (se 1 (by rfl) ⟨22472918, by rfl⟩ : syracuseStep 29963891 = 44945837) B44945837
theorem B79903709 : Blo 2305435 79903709 := bstep (se 3 (by rfl) ⟨14981945, by rfl⟩ : syracuseStep 79903709 = 29963891) B29963891
theorem B53269139 : Blo 2305435 53269139 := bstep (se 1 (by rfl) ⟨39951854, by rfl⟩ : syracuseStep 53269139 = 79903709) B79903709
theorem B35512759 : Blo 2305435 35512759 := bstep (se 1 (by rfl) ⟨26634569, by rfl⟩ : syracuseStep 35512759 = 53269139) B53269139
theorem B47350345 : Blo 2305435 47350345 := bstep (se 2 (by rfl) ⟨17756379, by rfl⟩ : syracuseStep 47350345 = 35512759) B35512759
theorem B63133793 : Blo 2305435 63133793 := bstep (se 2 (by rfl) ⟨23675172, by rfl⟩ : syracuseStep 63133793 = 47350345) B47350345
theorem B42089195 : Blo 2305435 42089195 := bstep (se 1 (by rfl) ⟨31566896, by rfl⟩ : syracuseStep 42089195 = 63133793) B63133793
theorem B28059463 : Blo 2305435 28059463 := bstep (se 1 (by rfl) ⟨21044597, by rfl⟩ : syracuseStep 28059463 = 42089195) B42089195
theorem B37412617 : Blo 2305435 37412617 := bstep (se 2 (by rfl) ⟨14029731, by rfl⟩ : syracuseStep 37412617 = 28059463) B28059463
theorem B49883489 : Blo 2305435 49883489 := bstep (se 2 (by rfl) ⟨18706308, by rfl⟩ : syracuseStep 49883489 = 37412617) B37412617
theorem B33255659 : Blo 2305435 33255659 := bstep (se 1 (by rfl) ⟨24941744, by rfl⟩ : syracuseStep 33255659 = 49883489) B49883489
theorem B22170439 : Blo 2305435 22170439 := bstep (se 1 (by rfl) ⟨16627829, by rfl⟩ : syracuseStep 22170439 = 33255659) B33255659
theorem B29560585 : Blo 2305435 29560585 := bstep (se 2 (by rfl) ⟨11085219, by rfl⟩ : syracuseStep 29560585 = 22170439) B22170439
theorem B39414113 : Blo 2305435 39414113 := bstep (se 2 (by rfl) ⟨14780292, by rfl⟩ : syracuseStep 39414113 = 29560585) B29560585
theorem B26276075 : Blo 2305435 26276075 := bstep (se 1 (by rfl) ⟨19707056, by rfl⟩ : syracuseStep 26276075 = 39414113) B39414113
theorem B17517383 : Blo 2305435 17517383 := bstep (se 1 (by rfl) ⟨13138037, by rfl⟩ : syracuseStep 17517383 = 26276075) B26276075
theorem B11678255 : Blo 2305435 11678255 := bstep (se 1 (by rfl) ⟨8758691, by rfl⟩ : syracuseStep 11678255 = 17517383) B17517383
theorem B7785503 : Blo 2305435 7785503 := bstep (se 1 (by rfl) ⟨5839127, by rfl⟩ : syracuseStep 7785503 = 11678255) B11678255
theorem B5190335 : Blo 2305435 5190335 := bstep (se 1 (by rfl) ⟨3892751, by rfl⟩ : syracuseStep 5190335 = 7785503) B7785503
theorem B3460223 : Blo 2305435 3460223 := bstep (se 1 (by rfl) ⟨2595167, by rfl⟩ : syracuseStep 3460223 = 5190335) B5190335
theorem B2306815 : Blo 2305435 2306815 := bstep (se 1 (by rfl) ⟨1730111, by rfl⟩ : syracuseStep 2306815 = 3460223) B3460223
theorem B3460229 : Blo 2305435 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B2306819 : Blo 2305435 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B3892765 : Blo 2305435 3892765 := bbase (se 3 (by rfl) ⟨729893, by rfl⟩ : syracuseStep 3892765 = 1459787) (by norm_num)
theorem B5190353 : Blo 2305435 5190353 := bstep (se 2 (by rfl) ⟨1946382, by rfl⟩ : syracuseStep 5190353 = 3892765) B3892765
theorem B3460235 : Blo 2305435 3460235 := bstep (se 1 (by rfl) ⟨2595176, by rfl⟩ : syracuseStep 3460235 = 5190353) B5190353
theorem B2306823 : Blo 2305435 2306823 := bstep (se 1 (by rfl) ⟨1730117, by rfl⟩ : syracuseStep 2306823 = 3460235) B3460235
theorem B2595181 : Blo 2305435 2595181 := bbase (se 3 (by rfl) ⟨486596, by rfl⟩ : syracuseStep 2595181 = 973193) (by norm_num)
theorem B3460241 : Blo 2305435 3460241 := bstep (se 2 (by rfl) ⟨1297590, by rfl⟩ : syracuseStep 3460241 = 2595181) B2595181
theorem B2306827 : Blo 2305435 2306827 := bstep (se 1 (by rfl) ⟨1730120, by rfl⟩ : syracuseStep 2306827 = 3460241) B3460241
theorem B7785557 : Blo 2305435 7785557 := bbase (se 8 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 7785557 = 91237) (by norm_num)
theorem B5190371 : Blo 2305435 5190371 := bstep (se 1 (by rfl) ⟨3892778, by rfl⟩ : syracuseStep 5190371 = 7785557) B7785557
theorem B3460247 : Blo 2305435 3460247 := bstep (se 1 (by rfl) ⟨2595185, by rfl⟩ : syracuseStep 3460247 = 5190371) B5190371
theorem B2306831 : Blo 2305435 2306831 := bstep (se 1 (by rfl) ⟨1730123, by rfl⟩ : syracuseStep 2306831 = 3460247) B3460247
theorem B3460253 : Blo 2305435 3460253 := bbase (se 3 (by rfl) ⟨648797, by rfl⟩ : syracuseStep 3460253 = 1297595) (by norm_num)
theorem B2306835 : Blo 2305435 2306835 := bstep (se 1 (by rfl) ⟨1730126, by rfl⟩ : syracuseStep 2306835 = 3460253) B3460253
theorem B5190389 : Blo 2305435 5190389 := bbase (se 5 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 5190389 = 486599) (by norm_num)
theorem B3460259 : Blo 2305435 3460259 := bstep (se 1 (by rfl) ⟨2595194, by rfl⟩ : syracuseStep 3460259 = 5190389) B5190389
theorem B2306839 : Blo 2305435 2306839 := bstep (se 1 (by rfl) ⟨1730129, by rfl⟩ : syracuseStep 2306839 = 3460259) B3460259
theorem B3117757 : Blo 2305435 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B4157009 : Blo 2305435 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B2771339 : Blo 2305435 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B29560949 : Blo 2305435 29560949 := bstep (se 5 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 29560949 = 2771339) B2771339
theorem B19707299 : Blo 2305435 19707299 := bstep (se 1 (by rfl) ⟨14780474, by rfl⟩ : syracuseStep 19707299 = 29560949) B29560949
theorem B13138199 : Blo 2305435 13138199 := bstep (se 1 (by rfl) ⟨9853649, by rfl⟩ : syracuseStep 13138199 = 19707299) B19707299
theorem B8758799 : Blo 2305435 8758799 := bstep (se 1 (by rfl) ⟨6569099, by rfl⟩ : syracuseStep 8758799 = 13138199) B13138199
theorem B5839199 : Blo 2305435 5839199 := bstep (se 1 (by rfl) ⟨4379399, by rfl⟩ : syracuseStep 5839199 = 8758799) B8758799
theorem B3892799 : Blo 2305435 3892799 := bstep (se 1 (by rfl) ⟨2919599, by rfl⟩ : syracuseStep 3892799 = 5839199) B5839199
theorem B2595199 : Blo 2305435 2595199 := bstep (se 1 (by rfl) ⟨1946399, by rfl⟩ : syracuseStep 2595199 = 3892799) B3892799
theorem B3460265 : Blo 2305435 3460265 := bstep (se 2 (by rfl) ⟨1297599, by rfl⟩ : syracuseStep 3460265 = 2595199) B2595199
theorem B2306843 : Blo 2305435 2306843 := bstep (se 1 (by rfl) ⟨1730132, by rfl⟩ : syracuseStep 2306843 = 3460265) B3460265
theorem B3695125 : Blo 2305435 3695125 := bbase (se 6 (by rfl) ⟨86604, by rfl⟩ : syracuseStep 3695125 = 173209) (by norm_num)
theorem B4926833 : Blo 2305435 4926833 := bstep (se 2 (by rfl) ⟨1847562, by rfl⟩ : syracuseStep 4926833 = 3695125) B3695125
theorem B3284555 : Blo 2305435 3284555 := bstep (se 1 (by rfl) ⟨2463416, by rfl⟩ : syracuseStep 3284555 = 4926833) B4926833
theorem B8758813 : Blo 2305435 8758813 := bstep (se 3 (by rfl) ⟨1642277, by rfl⟩ : syracuseStep 8758813 = 3284555) B3284555
theorem B11678417 : Blo 2305435 11678417 := bstep (se 2 (by rfl) ⟨4379406, by rfl⟩ : syracuseStep 11678417 = 8758813) B8758813
theorem B7785611 : Blo 2305435 7785611 := bstep (se 1 (by rfl) ⟨5839208, by rfl⟩ : syracuseStep 7785611 = 11678417) B11678417
theorem B5190407 : Blo 2305435 5190407 := bstep (se 1 (by rfl) ⟨3892805, by rfl⟩ : syracuseStep 5190407 = 7785611) B7785611
theorem B3460271 : Blo 2305435 3460271 := bstep (se 1 (by rfl) ⟨2595203, by rfl⟩ : syracuseStep 3460271 = 5190407) B5190407
theorem B2306847 : Blo 2305435 2306847 := bstep (se 1 (by rfl) ⟨1730135, by rfl⟩ : syracuseStep 2306847 = 3460271) B3460271
theorem B3460277 : Blo 2305435 3460277 := bbase (se 5 (by rfl) ⟨162200, by rfl⟩ : syracuseStep 3460277 = 324401) (by norm_num)
theorem B2306851 : Blo 2305435 2306851 := bstep (se 1 (by rfl) ⟨1730138, by rfl⟩ : syracuseStep 2306851 = 3460277) B3460277
theorem B5839229 : Blo 2305435 5839229 := bbase (se 3 (by rfl) ⟨1094855, by rfl⟩ : syracuseStep 5839229 = 2189711) (by norm_num)
theorem B3892819 : Blo 2305435 3892819 := bstep (se 1 (by rfl) ⟨2919614, by rfl⟩ : syracuseStep 3892819 = 5839229) B5839229
theorem B5190425 : Blo 2305435 5190425 := bstep (se 2 (by rfl) ⟨1946409, by rfl⟩ : syracuseStep 5190425 = 3892819) B3892819
theorem B3460283 : Blo 2305435 3460283 := bstep (se 1 (by rfl) ⟨2595212, by rfl⟩ : syracuseStep 3460283 = 5190425) B5190425
theorem B2306855 : Blo 2305435 2306855 := bstep (se 1 (by rfl) ⟨1730141, by rfl⟩ : syracuseStep 2306855 = 3460283) B3460283
theorem B2595217 : Blo 2305435 2595217 := bbase (se 2 (by rfl) ⟨973206, by rfl⟩ : syracuseStep 2595217 = 1946413) (by norm_num)
theorem B3460289 : Blo 2305435 3460289 := bstep (se 2 (by rfl) ⟨1297608, by rfl⟩ : syracuseStep 3460289 = 2595217) B2595217
theorem B2306859 : Blo 2305435 2306859 := bstep (se 1 (by rfl) ⟨1730144, by rfl⟩ : syracuseStep 2306859 = 3460289) B3460289
theorem B4379437 : Blo 2305435 4379437 := bbase (se 3 (by rfl) ⟨821144, by rfl⟩ : syracuseStep 4379437 = 1642289) (by norm_num)
theorem B5839249 : Blo 2305435 5839249 := bstep (se 2 (by rfl) ⟨2189718, by rfl⟩ : syracuseStep 5839249 = 4379437) B4379437
theorem B7785665 : Blo 2305435 7785665 := bstep (se 2 (by rfl) ⟨2919624, by rfl⟩ : syracuseStep 7785665 = 5839249) B5839249
theorem B5190443 : Blo 2305435 5190443 := bstep (se 1 (by rfl) ⟨3892832, by rfl⟩ : syracuseStep 5190443 = 7785665) B7785665
theorem B3460295 : Blo 2305435 3460295 := bstep (se 1 (by rfl) ⟨2595221, by rfl⟩ : syracuseStep 3460295 = 5190443) B5190443
theorem B2306863 : Blo 2305435 2306863 := bstep (se 1 (by rfl) ⟨1730147, by rfl⟩ : syracuseStep 2306863 = 3460295) B3460295
theorem B3460301 : Blo 2305435 3460301 := bbase (se 3 (by rfl) ⟨648806, by rfl⟩ : syracuseStep 3460301 = 1297613) (by norm_num)
theorem B2306867 : Blo 2305435 2306867 := bstep (se 1 (by rfl) ⟨1730150, by rfl⟩ : syracuseStep 2306867 = 3460301) B3460301
theorem B5190461 : Blo 2305435 5190461 := bbase (se 3 (by rfl) ⟨973211, by rfl⟩ : syracuseStep 5190461 = 1946423) (by norm_num)
theorem B3460307 : Blo 2305435 3460307 := bstep (se 1 (by rfl) ⟨2595230, by rfl⟩ : syracuseStep 3460307 = 5190461) B5190461
theorem B2306871 : Blo 2305435 2306871 := bstep (se 1 (by rfl) ⟨1730153, by rfl⟩ : syracuseStep 2306871 = 3460307) B3460307
theorem B3892853 : Blo 2305435 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B2595235 : Blo 2305435 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B3460313 : Blo 2305435 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B2306875 : Blo 2305435 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B4926901 : Blo 2305435 4926901 := bbase (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) (by norm_num)
theorem B6569201 : Blo 2305435 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B17517869 : Blo 2305435 17517869 := bstep (se 3 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 17517869 = 6569201) B6569201
theorem B11678579 : Blo 2305435 11678579 := bstep (se 1 (by rfl) ⟨8758934, by rfl⟩ : syracuseStep 11678579 = 17517869) B17517869
theorem B7785719 : Blo 2305435 7785719 := bstep (se 1 (by rfl) ⟨5839289, by rfl⟩ : syracuseStep 7785719 = 11678579) B11678579
theorem B5190479 : Blo 2305435 5190479 := bstep (se 1 (by rfl) ⟨3892859, by rfl⟩ : syracuseStep 5190479 = 7785719) B7785719
theorem B3460319 : Blo 2305435 3460319 := bstep (se 1 (by rfl) ⟨2595239, by rfl⟩ : syracuseStep 3460319 = 5190479) B5190479
theorem B2306879 : Blo 2305435 2306879 := bstep (se 1 (by rfl) ⟨1730159, by rfl⟩ : syracuseStep 2306879 = 3460319) B3460319
theorem B3460325 : Blo 2305435 3460325 := bbase (se 4 (by rfl) ⟨324405, by rfl⟩ : syracuseStep 3460325 = 648811) (by norm_num)
theorem B2306883 : Blo 2305435 2306883 := bstep (se 1 (by rfl) ⟨1730162, by rfl⟩ : syracuseStep 2306883 = 3460325) B3460325
theorem B4676725 : Blo 2305435 4676725 := bbase (se 5 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 4676725 = 438443) (by norm_num)
theorem B6235633 : Blo 2305435 6235633 := bstep (se 2 (by rfl) ⟨2338362, by rfl⟩ : syracuseStep 6235633 = 4676725) B4676725
theorem B8314177 : Blo 2305435 8314177 := bstep (se 2 (by rfl) ⟨3117816, by rfl⟩ : syracuseStep 8314177 = 6235633) B6235633
theorem B11085569 : Blo 2305435 11085569 := bstep (se 2 (by rfl) ⟨4157088, by rfl⟩ : syracuseStep 11085569 = 8314177) B8314177
theorem B7390379 : Blo 2305435 7390379 := bstep (se 1 (by rfl) ⟨5542784, by rfl⟩ : syracuseStep 7390379 = 11085569) B11085569
theorem B4926919 : Blo 2305435 4926919 := bstep (se 1 (by rfl) ⟨3695189, by rfl⟩ : syracuseStep 4926919 = 7390379) B7390379
theorem B6569225 : Blo 2305435 6569225 := bstep (se 2 (by rfl) ⟨2463459, by rfl⟩ : syracuseStep 6569225 = 4926919) B4926919
theorem B4379483 : Blo 2305435 4379483 := bstep (se 1 (by rfl) ⟨3284612, by rfl⟩ : syracuseStep 4379483 = 6569225) B6569225
theorem B2919655 : Blo 2305435 2919655 := bstep (se 1 (by rfl) ⟨2189741, by rfl⟩ : syracuseStep 2919655 = 4379483) B4379483
theorem B3892873 : Blo 2305435 3892873 := bstep (se 2 (by rfl) ⟨1459827, by rfl⟩ : syracuseStep 3892873 = 2919655) B2919655
theorem B5190497 : Blo 2305435 5190497 := bstep (se 2 (by rfl) ⟨1946436, by rfl⟩ : syracuseStep 5190497 = 3892873) B3892873
theorem B3460331 : Blo 2305435 3460331 := bstep (se 1 (by rfl) ⟨2595248, by rfl⟩ : syracuseStep 3460331 = 5190497) B5190497
theorem B2306887 : Blo 2305435 2306887 := bstep (se 1 (by rfl) ⟨1730165, by rfl⟩ : syracuseStep 2306887 = 3460331) B3460331
theorem B2595253 : Blo 2305435 2595253 := bbase (se 5 (by rfl) ⟨121652, by rfl⟩ : syracuseStep 2595253 = 243305) (by norm_num)
theorem B3460337 : Blo 2305435 3460337 := bstep (se 2 (by rfl) ⟨1297626, by rfl⟩ : syracuseStep 3460337 = 2595253) B2595253
theorem B2306891 : Blo 2305435 2306891 := bstep (se 1 (by rfl) ⟨1730168, by rfl⟩ : syracuseStep 2306891 = 3460337) B3460337
theorem B2919665 : Blo 2305435 2919665 := bbase (se 2 (by rfl) ⟨1094874, by rfl⟩ : syracuseStep 2919665 = 2189749) (by norm_num)
theorem B7785773 : Blo 2305435 7785773 := bstep (se 3 (by rfl) ⟨1459832, by rfl⟩ : syracuseStep 7785773 = 2919665) B2919665
theorem B5190515 : Blo 2305435 5190515 := bstep (se 1 (by rfl) ⟨3892886, by rfl⟩ : syracuseStep 5190515 = 7785773) B7785773
theorem B3460343 : Blo 2305435 3460343 := bstep (se 1 (by rfl) ⟨2595257, by rfl⟩ : syracuseStep 3460343 = 5190515) B5190515
theorem B2306895 : Blo 2305435 2306895 := bstep (se 1 (by rfl) ⟨1730171, by rfl⟩ : syracuseStep 2306895 = 3460343) B3460343
theorem B3460349 : Blo 2305435 3460349 := bbase (se 3 (by rfl) ⟨648815, by rfl⟩ : syracuseStep 3460349 = 1297631) (by norm_num)
theorem B2306899 : Blo 2305435 2306899 := bstep (se 1 (by rfl) ⟨1730174, by rfl⟩ : syracuseStep 2306899 = 3460349) B3460349
theorem B5190533 : Blo 2305435 5190533 := bbase (se 4 (by rfl) ⟨486612, by rfl⟩ : syracuseStep 5190533 = 973225) (by norm_num)
theorem B3460355 : Blo 2305435 3460355 := bstep (se 1 (by rfl) ⟨2595266, by rfl⟩ : syracuseStep 3460355 = 5190533) B5190533
theorem B2306903 : Blo 2305435 2306903 := bstep (se 1 (by rfl) ⟨1730177, by rfl⟩ : syracuseStep 2306903 = 3460355) B3460355
theorem B2463481 : Blo 2305435 2463481 := bbase (se 2 (by rfl) ⟨923805, by rfl⟩ : syracuseStep 2463481 = 1847611) (by norm_num)
theorem B3284641 : Blo 2305435 3284641 := bstep (se 2 (by rfl) ⟨1231740, by rfl⟩ : syracuseStep 3284641 = 2463481) B2463481
theorem B4379521 : Blo 2305435 4379521 := bstep (se 2 (by rfl) ⟨1642320, by rfl⟩ : syracuseStep 4379521 = 3284641) B3284641
theorem B5839361 : Blo 2305435 5839361 := bstep (se 2 (by rfl) ⟨2189760, by rfl⟩ : syracuseStep 5839361 = 4379521) B4379521
theorem B3892907 : Blo 2305435 3892907 := bstep (se 1 (by rfl) ⟨2919680, by rfl⟩ : syracuseStep 3892907 = 5839361) B5839361
theorem B2595271 : Blo 2305435 2595271 := bstep (se 1 (by rfl) ⟨1946453, by rfl⟩ : syracuseStep 2595271 = 3892907) B3892907
theorem B3460361 : Blo 2305435 3460361 := bstep (se 2 (by rfl) ⟨1297635, by rfl⟩ : syracuseStep 3460361 = 2595271) B2595271
theorem B2306907 : Blo 2305435 2306907 := bstep (se 1 (by rfl) ⟨1730180, by rfl⟩ : syracuseStep 2306907 = 3460361) B3460361
theorem B11678741 : Blo 2305435 11678741 := bbase (se 6 (by rfl) ⟨273720, by rfl⟩ : syracuseStep 11678741 = 547441) (by norm_num)
theorem B7785827 : Blo 2305435 7785827 := bstep (se 1 (by rfl) ⟨5839370, by rfl⟩ : syracuseStep 7785827 = 11678741) B11678741
theorem B5190551 : Blo 2305435 5190551 := bstep (se 1 (by rfl) ⟨3892913, by rfl⟩ : syracuseStep 5190551 = 7785827) B7785827
theorem B3460367 : Blo 2305435 3460367 := bstep (se 1 (by rfl) ⟨2595275, by rfl⟩ : syracuseStep 3460367 = 5190551) B5190551
theorem B2306911 : Blo 2305435 2306911 := bstep (se 1 (by rfl) ⟨1730183, by rfl⟩ : syracuseStep 2306911 = 3460367) B3460367
theorem B3460373 : Blo 2305435 3460373 := bbase (se 6 (by rfl) ⟨81102, by rfl⟩ : syracuseStep 3460373 = 162205) (by norm_num)
theorem B2306915 : Blo 2305435 2306915 := bstep (se 1 (by rfl) ⟨1730186, by rfl⟩ : syracuseStep 2306915 = 3460373) B3460373
theorem B4676789 : Blo 2305435 4676789 := bbase (se 5 (by rfl) ⟨219224, by rfl⟩ : syracuseStep 4676789 = 438449) (by norm_num)
theorem B3117859 : Blo 2305435 3117859 := bstep (se 1 (by rfl) ⟨2338394, by rfl⟩ : syracuseStep 3117859 = 4676789) B4676789
theorem B16628581 : Blo 2305435 16628581 := bstep (se 4 (by rfl) ⟨1558929, by rfl⟩ : syracuseStep 16628581 = 3117859) B3117859
theorem B22171441 : Blo 2305435 22171441 := bstep (se 2 (by rfl) ⟨8314290, by rfl⟩ : syracuseStep 22171441 = 16628581) B16628581
theorem B29561921 : Blo 2305435 29561921 := bstep (se 2 (by rfl) ⟨11085720, by rfl⟩ : syracuseStep 29561921 = 22171441) B22171441
theorem B19707947 : Blo 2305435 19707947 := bstep (se 1 (by rfl) ⟨14780960, by rfl⟩ : syracuseStep 19707947 = 29561921) B29561921
theorem B13138631 : Blo 2305435 13138631 := bstep (se 1 (by rfl) ⟨9853973, by rfl⟩ : syracuseStep 13138631 = 19707947) B19707947
theorem B8759087 : Blo 2305435 8759087 := bstep (se 1 (by rfl) ⟨6569315, by rfl⟩ : syracuseStep 8759087 = 13138631) B13138631
theorem B5839391 : Blo 2305435 5839391 := bstep (se 1 (by rfl) ⟨4379543, by rfl⟩ : syracuseStep 5839391 = 8759087) B8759087
theorem B3892927 : Blo 2305435 3892927 := bstep (se 1 (by rfl) ⟨2919695, by rfl⟩ : syracuseStep 3892927 = 5839391) B5839391
theorem B5190569 : Blo 2305435 5190569 := bstep (se 2 (by rfl) ⟨1946463, by rfl⟩ : syracuseStep 5190569 = 3892927) B3892927
theorem B3460379 : Blo 2305435 3460379 := bstep (se 1 (by rfl) ⟨2595284, by rfl⟩ : syracuseStep 3460379 = 5190569) B5190569
theorem B2306919 : Blo 2305435 2306919 := bstep (se 1 (by rfl) ⟨1730189, by rfl⟩ : syracuseStep 2306919 = 3460379) B3460379
theorem B2595289 : Blo 2305435 2595289 := bbase (se 2 (by rfl) ⟨973233, by rfl⟩ : syracuseStep 2595289 = 1946467) (by norm_num)
theorem B3460385 : Blo 2305435 3460385 := bstep (se 2 (by rfl) ⟨1297644, by rfl⟩ : syracuseStep 3460385 = 2595289) B2595289
theorem B2306923 : Blo 2305435 2306923 := bstep (se 1 (by rfl) ⟨1730192, by rfl⟩ : syracuseStep 2306923 = 3460385) B3460385
theorem B3284669 : Blo 2305435 3284669 := bbase (se 3 (by rfl) ⟨615875, by rfl⟩ : syracuseStep 3284669 = 1231751) (by norm_num)
theorem B8759117 : Blo 2305435 8759117 := bstep (se 3 (by rfl) ⟨1642334, by rfl⟩ : syracuseStep 8759117 = 3284669) B3284669
theorem B5839411 : Blo 2305435 5839411 := bstep (se 1 (by rfl) ⟨4379558, by rfl⟩ : syracuseStep 5839411 = 8759117) B8759117
theorem B7785881 : Blo 2305435 7785881 := bstep (se 2 (by rfl) ⟨2919705, by rfl⟩ : syracuseStep 7785881 = 5839411) B5839411
theorem B5190587 : Blo 2305435 5190587 := bstep (se 1 (by rfl) ⟨3892940, by rfl⟩ : syracuseStep 5190587 = 7785881) B7785881
theorem B3460391 : Blo 2305435 3460391 := bstep (se 1 (by rfl) ⟨2595293, by rfl⟩ : syracuseStep 3460391 = 5190587) B5190587
theorem B2306927 : Blo 2305435 2306927 := bstep (se 1 (by rfl) ⟨1730195, by rfl⟩ : syracuseStep 2306927 = 3460391) B3460391
theorem B3460397 : Blo 2305435 3460397 := bbase (se 3 (by rfl) ⟨648824, by rfl⟩ : syracuseStep 3460397 = 1297649) (by norm_num)
theorem B2306931 : Blo 2305435 2306931 := bstep (se 1 (by rfl) ⟨1730198, by rfl⟩ : syracuseStep 2306931 = 3460397) B3460397
theorem B5190605 : Blo 2305435 5190605 := bbase (se 3 (by rfl) ⟨973238, by rfl⟩ : syracuseStep 5190605 = 1946477) (by norm_num)
theorem B3460403 : Blo 2305435 3460403 := bstep (se 1 (by rfl) ⟨2595302, by rfl⟩ : syracuseStep 3460403 = 5190605) B5190605
theorem B2306935 : Blo 2305435 2306935 := bstep (se 1 (by rfl) ⟨1730201, by rfl⟩ : syracuseStep 2306935 = 3460403) B3460403
theorem B2919721 : Blo 2305435 2919721 := bbase (se 2 (by rfl) ⟨1094895, by rfl⟩ : syracuseStep 2919721 = 2189791) (by norm_num)
theorem B3892961 : Blo 2305435 3892961 := bstep (se 2 (by rfl) ⟨1459860, by rfl⟩ : syracuseStep 3892961 = 2919721) B2919721
theorem B2595307 : Blo 2305435 2595307 := bstep (se 1 (by rfl) ⟨1946480, by rfl⟩ : syracuseStep 2595307 = 3892961) B3892961
theorem B3460409 : Blo 2305435 3460409 := bstep (se 2 (by rfl) ⟨1297653, by rfl⟩ : syracuseStep 3460409 = 2595307) B2595307
theorem B2306939 : Blo 2305435 2306939 := bstep (se 1 (by rfl) ⟨1730204, by rfl⟩ : syracuseStep 2306939 = 3460409) B3460409
theorem B4676837 : Blo 2305435 4676837 := bbase (se 4 (by rfl) ⟨438453, by rfl⟩ : syracuseStep 4676837 = 876907) (by norm_num)
theorem B12471565 : Blo 2305435 12471565 := bstep (se 3 (by rfl) ⟨2338418, by rfl⟩ : syracuseStep 12471565 = 4676837) B4676837
theorem B16628753 : Blo 2305435 16628753 := bstep (se 2 (by rfl) ⟨6235782, by rfl⟩ : syracuseStep 16628753 = 12471565) B12471565
theorem B11085835 : Blo 2305435 11085835 := bstep (se 1 (by rfl) ⟨8314376, by rfl⟩ : syracuseStep 11085835 = 16628753) B16628753
theorem B14781113 : Blo 2305435 14781113 := bstep (se 2 (by rfl) ⟨5542917, by rfl⟩ : syracuseStep 14781113 = 11085835) B11085835
theorem B9854075 : Blo 2305435 9854075 := bstep (se 1 (by rfl) ⟨7390556, by rfl⟩ : syracuseStep 9854075 = 14781113) B14781113
theorem B26277533 : Blo 2305435 26277533 := bstep (se 3 (by rfl) ⟨4927037, by rfl⟩ : syracuseStep 26277533 = 9854075) B9854075
theorem B17518355 : Blo 2305435 17518355 := bstep (se 1 (by rfl) ⟨13138766, by rfl⟩ : syracuseStep 17518355 = 26277533) B26277533
theorem B11678903 : Blo 2305435 11678903 := bstep (se 1 (by rfl) ⟨8759177, by rfl⟩ : syracuseStep 11678903 = 17518355) B17518355
theorem B7785935 : Blo 2305435 7785935 := bstep (se 1 (by rfl) ⟨5839451, by rfl⟩ : syracuseStep 7785935 = 11678903) B11678903
theorem B5190623 : Blo 2305435 5190623 := bstep (se 1 (by rfl) ⟨3892967, by rfl⟩ : syracuseStep 5190623 = 7785935) B7785935
theorem B3460415 : Blo 2305435 3460415 := bstep (se 1 (by rfl) ⟨2595311, by rfl⟩ : syracuseStep 3460415 = 5190623) B5190623
theorem B2306943 : Blo 2305435 2306943 := bstep (se 1 (by rfl) ⟨1730207, by rfl⟩ : syracuseStep 2306943 = 3460415) B3460415
theorem B3460421 : Blo 2305435 3460421 := bbase (se 4 (by rfl) ⟨324414, by rfl⟩ : syracuseStep 3460421 = 648829) (by norm_num)
theorem B2306947 : Blo 2305435 2306947 := bstep (se 1 (by rfl) ⟨1730210, by rfl⟩ : syracuseStep 2306947 = 3460421) B3460421
theorem B3892981 : Blo 2305435 3892981 := bbase (se 5 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 3892981 = 364967) (by norm_num)
theorem B5190641 : Blo 2305435 5190641 := bstep (se 2 (by rfl) ⟨1946490, by rfl⟩ : syracuseStep 5190641 = 3892981) B3892981
theorem B3460427 : Blo 2305435 3460427 := bstep (se 1 (by rfl) ⟨2595320, by rfl⟩ : syracuseStep 3460427 = 5190641) B5190641
theorem B2306951 : Blo 2305435 2306951 := bstep (se 1 (by rfl) ⟨1730213, by rfl⟩ : syracuseStep 2306951 = 3460427) B3460427
theorem B2595325 : Blo 2305435 2595325 := bbase (se 3 (by rfl) ⟨486623, by rfl⟩ : syracuseStep 2595325 = 973247) (by norm_num)
theorem B3460433 : Blo 2305435 3460433 := bstep (se 2 (by rfl) ⟨1297662, by rfl⟩ : syracuseStep 3460433 = 2595325) B2595325
theorem B2306955 : Blo 2305435 2306955 := bstep (se 1 (by rfl) ⟨1730216, by rfl⟩ : syracuseStep 2306955 = 3460433) B3460433
theorem B7785989 : Blo 2305435 7785989 := bbase (se 4 (by rfl) ⟨729936, by rfl⟩ : syracuseStep 7785989 = 1459873) (by norm_num)
theorem B5190659 : Blo 2305435 5190659 := bstep (se 1 (by rfl) ⟨3892994, by rfl⟩ : syracuseStep 5190659 = 7785989) B7785989
theorem B3460439 : Blo 2305435 3460439 := bstep (se 1 (by rfl) ⟨2595329, by rfl⟩ : syracuseStep 3460439 = 5190659) B5190659
theorem B2306959 : Blo 2305435 2306959 := bstep (se 1 (by rfl) ⟨1730219, by rfl⟩ : syracuseStep 2306959 = 3460439) B3460439
theorem B3460445 : Blo 2305435 3460445 := bbase (se 3 (by rfl) ⟨648833, by rfl⟩ : syracuseStep 3460445 = 1297667) (by norm_num)
theorem B2306963 : Blo 2305435 2306963 := bstep (se 1 (by rfl) ⟨1730222, by rfl⟩ : syracuseStep 2306963 = 3460445) B3460445
theorem B5190677 : Blo 2305435 5190677 := bbase (se 6 (by rfl) ⟨121656, by rfl⟩ : syracuseStep 5190677 = 243313) (by norm_num)
theorem B3460451 : Blo 2305435 3460451 := bstep (se 1 (by rfl) ⟨2595338, by rfl⟩ : syracuseStep 3460451 = 5190677) B5190677
theorem B2306967 : Blo 2305435 2306967 := bstep (se 1 (by rfl) ⟨1730225, by rfl⟩ : syracuseStep 2306967 = 3460451) B3460451
theorem B8759285 : Blo 2305435 8759285 := bbase (se 5 (by rfl) ⟨410591, by rfl⟩ : syracuseStep 8759285 = 821183) (by norm_num)
theorem B5839523 : Blo 2305435 5839523 := bstep (se 1 (by rfl) ⟨4379642, by rfl⟩ : syracuseStep 5839523 = 8759285) B8759285
theorem B3893015 : Blo 2305435 3893015 := bstep (se 1 (by rfl) ⟨2919761, by rfl⟩ : syracuseStep 3893015 = 5839523) B5839523
theorem B2595343 : Blo 2305435 2595343 := bstep (se 1 (by rfl) ⟨1946507, by rfl⟩ : syracuseStep 2595343 = 3893015) B3893015
theorem B3460457 : Blo 2305435 3460457 := bstep (se 2 (by rfl) ⟨1297671, by rfl⟩ : syracuseStep 3460457 = 2595343) B2595343
theorem B2306971 : Blo 2305435 2306971 := bstep (se 1 (by rfl) ⟨1730228, by rfl⟩ : syracuseStep 2306971 = 3460457) B3460457
theorem B2463553 : Blo 2305435 2463553 := bbase (se 2 (by rfl) ⟨923832, by rfl⟩ : syracuseStep 2463553 = 1847665) (by norm_num)
theorem B13138949 : Blo 2305435 13138949 := bstep (se 4 (by rfl) ⟨1231776, by rfl⟩ : syracuseStep 13138949 = 2463553) B2463553
theorem B8759299 : Blo 2305435 8759299 := bstep (se 1 (by rfl) ⟨6569474, by rfl⟩ : syracuseStep 8759299 = 13138949) B13138949
theorem B11679065 : Blo 2305435 11679065 := bstep (se 2 (by rfl) ⟨4379649, by rfl⟩ : syracuseStep 11679065 = 8759299) B8759299
theorem B7786043 : Blo 2305435 7786043 := bstep (se 1 (by rfl) ⟨5839532, by rfl⟩ : syracuseStep 7786043 = 11679065) B11679065
theorem B5190695 : Blo 2305435 5190695 := bstep (se 1 (by rfl) ⟨3893021, by rfl⟩ : syracuseStep 5190695 = 7786043) B7786043
theorem B3460463 : Blo 2305435 3460463 := bstep (se 1 (by rfl) ⟨2595347, by rfl⟩ : syracuseStep 3460463 = 5190695) B5190695
theorem B2306975 : Blo 2305435 2306975 := bstep (se 1 (by rfl) ⟨1730231, by rfl⟩ : syracuseStep 2306975 = 3460463) B3460463
theorem B3460469 : Blo 2305435 3460469 := bbase (se 5 (by rfl) ⟨162209, by rfl⟩ : syracuseStep 3460469 = 324419) (by norm_num)
theorem B2306979 : Blo 2305435 2306979 := bstep (se 1 (by rfl) ⟨1730234, by rfl⟩ : syracuseStep 2306979 = 3460469) B3460469
theorem B3284749 : Blo 2305435 3284749 := bbase (se 3 (by rfl) ⟨615890, by rfl⟩ : syracuseStep 3284749 = 1231781) (by norm_num)
theorem B4379665 : Blo 2305435 4379665 := bstep (se 2 (by rfl) ⟨1642374, by rfl⟩ : syracuseStep 4379665 = 3284749) B3284749
theorem B5839553 : Blo 2305435 5839553 := bstep (se 2 (by rfl) ⟨2189832, by rfl⟩ : syracuseStep 5839553 = 4379665) B4379665
theorem B3893035 : Blo 2305435 3893035 := bstep (se 1 (by rfl) ⟨2919776, by rfl⟩ : syracuseStep 3893035 = 5839553) B5839553
theorem B5190713 : Blo 2305435 5190713 := bstep (se 2 (by rfl) ⟨1946517, by rfl⟩ : syracuseStep 5190713 = 3893035) B3893035
theorem B3460475 : Blo 2305435 3460475 := bstep (se 1 (by rfl) ⟨2595356, by rfl⟩ : syracuseStep 3460475 = 5190713) B5190713
theorem B2306983 : Blo 2305435 2306983 := bstep (se 1 (by rfl) ⟨1730237, by rfl⟩ : syracuseStep 2306983 = 3460475) B3460475
theorem B2595361 : Blo 2305435 2595361 := bbase (se 2 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 2595361 = 1946521) (by norm_num)
theorem B3460481 : Blo 2305435 3460481 := bstep (se 2 (by rfl) ⟨1297680, by rfl⟩ : syracuseStep 3460481 = 2595361) B2595361
theorem B2306987 : Blo 2305435 2306987 := bstep (se 1 (by rfl) ⟨1730240, by rfl⟩ : syracuseStep 2306987 = 3460481) B3460481
theorem B5839573 : Blo 2305435 5839573 := bbase (se 7 (by rfl) ⟨68432, by rfl⟩ : syracuseStep 5839573 = 136865) (by norm_num)
theorem B7786097 : Blo 2305435 7786097 := bstep (se 2 (by rfl) ⟨2919786, by rfl⟩ : syracuseStep 7786097 = 5839573) B5839573
theorem B5190731 : Blo 2305435 5190731 := bstep (se 1 (by rfl) ⟨3893048, by rfl⟩ : syracuseStep 5190731 = 7786097) B7786097
theorem B3460487 : Blo 2305435 3460487 := bstep (se 1 (by rfl) ⟨2595365, by rfl⟩ : syracuseStep 3460487 = 5190731) B5190731
theorem B2306991 : Blo 2305435 2306991 := bstep (se 1 (by rfl) ⟨1730243, by rfl⟩ : syracuseStep 2306991 = 3460487) B3460487
theorem B3460493 : Blo 2305435 3460493 := bbase (se 3 (by rfl) ⟨648842, by rfl⟩ : syracuseStep 3460493 = 1297685) (by norm_num)
theorem B2306995 : Blo 2305435 2306995 := bstep (se 1 (by rfl) ⟨1730246, by rfl⟩ : syracuseStep 2306995 = 3460493) B3460493
theorem B5190749 : Blo 2305435 5190749 := bbase (se 3 (by rfl) ⟨973265, by rfl⟩ : syracuseStep 5190749 = 1946531) (by norm_num)
theorem B3460499 : Blo 2305435 3460499 := bstep (se 1 (by rfl) ⟨2595374, by rfl⟩ : syracuseStep 3460499 = 5190749) B5190749
theorem B2306999 : Blo 2305435 2306999 := bstep (se 1 (by rfl) ⟨1730249, by rfl⟩ : syracuseStep 2306999 = 3460499) B3460499
theorem B3893069 : Blo 2305435 3893069 := bbase (se 3 (by rfl) ⟨729950, by rfl⟩ : syracuseStep 3893069 = 1459901) (by norm_num)
theorem B2595379 : Blo 2305435 2595379 := bstep (se 1 (by rfl) ⟨1946534, by rfl⟩ : syracuseStep 2595379 = 3893069) B3893069
theorem B3460505 : Blo 2305435 3460505 := bstep (se 2 (by rfl) ⟨1297689, by rfl⟩ : syracuseStep 3460505 = 2595379) B2595379
theorem B2307003 : Blo 2305435 2307003 := bstep (se 1 (by rfl) ⟨1730252, by rfl⟩ : syracuseStep 2307003 = 3460505) B3460505
theorem B2370389 : Blo 2305435 2370389 := bbase (se 9 (by rfl) ⟨6944, by rfl⟩ : syracuseStep 2370389 = 13889) (by norm_num)
theorem B6321037 : Blo 2305435 6321037 := bstep (se 3 (by rfl) ⟨1185194, by rfl⟩ : syracuseStep 6321037 = 2370389) B2370389
theorem B8428049 : Blo 2305435 8428049 := bstep (se 2 (by rfl) ⟨3160518, by rfl⟩ : syracuseStep 8428049 = 6321037) B6321037
theorem B5618699 : Blo 2305435 5618699 := bstep (se 1 (by rfl) ⟨4214024, by rfl⟩ : syracuseStep 5618699 = 8428049) B8428049
theorem B3745799 : Blo 2305435 3745799 := bstep (se 1 (by rfl) ⟨2809349, by rfl⟩ : syracuseStep 3745799 = 5618699) B5618699
theorem B2497199 : Blo 2305435 2497199 := bstep (se 1 (by rfl) ⟨1872899, by rfl⟩ : syracuseStep 2497199 = 3745799) B3745799
theorem B26636789 : Blo 2305435 26636789 := bstep (se 5 (by rfl) ⟨1248599, by rfl⟩ : syracuseStep 26636789 = 2497199) B2497199
theorem B71031437 : Blo 2305435 71031437 := bstep (se 3 (by rfl) ⟨13318394, by rfl⟩ : syracuseStep 71031437 = 26636789) B26636789
theorem B47354291 : Blo 2305435 47354291 := bstep (se 1 (by rfl) ⟨35515718, by rfl⟩ : syracuseStep 47354291 = 71031437) B71031437
theorem B31569527 : Blo 2305435 31569527 := bstep (se 1 (by rfl) ⟨23677145, by rfl⟩ : syracuseStep 31569527 = 47354291) B47354291
theorem B21046351 : Blo 2305435 21046351 := bstep (se 1 (by rfl) ⟨15784763, by rfl⟩ : syracuseStep 21046351 = 31569527) B31569527
theorem B28061801 : Blo 2305435 28061801 := bstep (se 2 (by rfl) ⟨10523175, by rfl⟩ : syracuseStep 28061801 = 21046351) B21046351
theorem B18707867 : Blo 2305435 18707867 := bstep (se 1 (by rfl) ⟨14030900, by rfl⟩ : syracuseStep 18707867 = 28061801) B28061801
theorem B12471911 : Blo 2305435 12471911 := bstep (se 1 (by rfl) ⟨9353933, by rfl⟩ : syracuseStep 12471911 = 18707867) B18707867
theorem B8314607 : Blo 2305435 8314607 := bstep (se 1 (by rfl) ⟨6235955, by rfl⟩ : syracuseStep 8314607 = 12471911) B12471911
theorem B22172285 : Blo 2305435 22172285 := bstep (se 3 (by rfl) ⟨4157303, by rfl⟩ : syracuseStep 22172285 = 8314607) B8314607
theorem B14781523 : Blo 2305435 14781523 := bstep (se 1 (by rfl) ⟨11086142, by rfl⟩ : syracuseStep 14781523 = 22172285) B22172285
theorem B19708697 : Blo 2305435 19708697 := bstep (se 2 (by rfl) ⟨7390761, by rfl⟩ : syracuseStep 19708697 = 14781523) B14781523
theorem B13139131 : Blo 2305435 13139131 := bstep (se 1 (by rfl) ⟨9854348, by rfl⟩ : syracuseStep 13139131 = 19708697) B19708697
theorem B17518841 : Blo 2305435 17518841 := bstep (se 2 (by rfl) ⟨6569565, by rfl⟩ : syracuseStep 17518841 = 13139131) B13139131
theorem B11679227 : Blo 2305435 11679227 := bstep (se 1 (by rfl) ⟨8759420, by rfl⟩ : syracuseStep 11679227 = 17518841) B17518841
theorem B7786151 : Blo 2305435 7786151 := bstep (se 1 (by rfl) ⟨5839613, by rfl⟩ : syracuseStep 7786151 = 11679227) B11679227
theorem B5190767 : Blo 2305435 5190767 := bstep (se 1 (by rfl) ⟨3893075, by rfl⟩ : syracuseStep 5190767 = 7786151) B7786151
theorem B3460511 : Blo 2305435 3460511 := bstep (se 1 (by rfl) ⟨2595383, by rfl⟩ : syracuseStep 3460511 = 5190767) B5190767
theorem B2307007 : Blo 2305435 2307007 := bstep (se 1 (by rfl) ⟨1730255, by rfl⟩ : syracuseStep 2307007 = 3460511) B3460511
theorem B3460517 : Blo 2305435 3460517 := bbase (se 4 (by rfl) ⟨324423, by rfl⟩ : syracuseStep 3460517 = 648847) (by norm_num)
theorem B2307011 : Blo 2305435 2307011 := bstep (se 1 (by rfl) ⟨1730258, by rfl⟩ : syracuseStep 2307011 = 3460517) B3460517
theorem B2919817 : Blo 2305435 2919817 := bbase (se 2 (by rfl) ⟨1094931, by rfl⟩ : syracuseStep 2919817 = 2189863) (by norm_num)
theorem B3893089 : Blo 2305435 3893089 := bstep (se 2 (by rfl) ⟨1459908, by rfl⟩ : syracuseStep 3893089 = 2919817) B2919817
theorem B5190785 : Blo 2305435 5190785 := bstep (se 2 (by rfl) ⟨1946544, by rfl⟩ : syracuseStep 5190785 = 3893089) B3893089
theorem B3460523 : Blo 2305435 3460523 := bstep (se 1 (by rfl) ⟨2595392, by rfl⟩ : syracuseStep 3460523 = 5190785) B5190785
theorem B2307015 : Blo 2305435 2307015 := bstep (se 1 (by rfl) ⟨1730261, by rfl⟩ : syracuseStep 2307015 = 3460523) B3460523
theorem B2595397 : Blo 2305435 2595397 := bbase (se 4 (by rfl) ⟨243318, by rfl⟩ : syracuseStep 2595397 = 486637) (by norm_num)
theorem B3460529 : Blo 2305435 3460529 := bstep (se 2 (by rfl) ⟨1297698, by rfl⟩ : syracuseStep 3460529 = 2595397) B2595397
theorem B2307019 : Blo 2305435 2307019 := bstep (se 1 (by rfl) ⟨1730264, by rfl⟩ : syracuseStep 2307019 = 3460529) B3460529
theorem B4379741 : Blo 2305435 4379741 := bbase (se 3 (by rfl) ⟨821201, by rfl⟩ : syracuseStep 4379741 = 1642403) (by norm_num)
theorem B2919827 : Blo 2305435 2919827 := bstep (se 1 (by rfl) ⟨2189870, by rfl⟩ : syracuseStep 2919827 = 4379741) B4379741
theorem B7786205 : Blo 2305435 7786205 := bstep (se 3 (by rfl) ⟨1459913, by rfl⟩ : syracuseStep 7786205 = 2919827) B2919827
theorem B5190803 : Blo 2305435 5190803 := bstep (se 1 (by rfl) ⟨3893102, by rfl⟩ : syracuseStep 5190803 = 7786205) B7786205
theorem B3460535 : Blo 2305435 3460535 := bstep (se 1 (by rfl) ⟨2595401, by rfl⟩ : syracuseStep 3460535 = 5190803) B5190803
theorem B2307023 : Blo 2305435 2307023 := bstep (se 1 (by rfl) ⟨1730267, by rfl⟩ : syracuseStep 2307023 = 3460535) B3460535
theorem B3460541 : Blo 2305435 3460541 := bbase (se 3 (by rfl) ⟨648851, by rfl⟩ : syracuseStep 3460541 = 1297703) (by norm_num)
theorem B2307027 : Blo 2305435 2307027 := bstep (se 1 (by rfl) ⟨1730270, by rfl⟩ : syracuseStep 2307027 = 3460541) B3460541
theorem B5190821 : Blo 2305435 5190821 := bbase (se 4 (by rfl) ⟨486639, by rfl⟩ : syracuseStep 5190821 = 973279) (by norm_num)
theorem B3460547 : Blo 2305435 3460547 := bstep (se 1 (by rfl) ⟨2595410, by rfl⟩ : syracuseStep 3460547 = 5190821) B5190821
theorem B2307031 : Blo 2305435 2307031 := bstep (se 1 (by rfl) ⟨1730273, by rfl⟩ : syracuseStep 2307031 = 3460547) B3460547
theorem B5839685 : Blo 2305435 5839685 := bbase (se 4 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 5839685 = 1094941) (by norm_num)
theorem B3893123 : Blo 2305435 3893123 := bstep (se 1 (by rfl) ⟨2919842, by rfl⟩ : syracuseStep 3893123 = 5839685) B5839685
theorem B2595415 : Blo 2305435 2595415 := bstep (se 1 (by rfl) ⟨1946561, by rfl⟩ : syracuseStep 2595415 = 3893123) B3893123
theorem B3460553 : Blo 2305435 3460553 := bstep (se 2 (by rfl) ⟨1297707, by rfl⟩ : syracuseStep 3460553 = 2595415) B2595415
theorem B2307035 : Blo 2305435 2307035 := bstep (se 1 (by rfl) ⟨1730276, by rfl⟩ : syracuseStep 2307035 = 3460553) B3460553
theorem B5543149 : Blo 2305435 5543149 := bbase (se 3 (by rfl) ⟨1039340, by rfl⟩ : syracuseStep 5543149 = 2078681) (by norm_num)
theorem B7390865 : Blo 2305435 7390865 := bstep (se 2 (by rfl) ⟨2771574, by rfl⟩ : syracuseStep 7390865 = 5543149) B5543149
theorem B4927243 : Blo 2305435 4927243 := bstep (se 1 (by rfl) ⟨3695432, by rfl⟩ : syracuseStep 4927243 = 7390865) B7390865
theorem B6569657 : Blo 2305435 6569657 := bstep (se 2 (by rfl) ⟨2463621, by rfl⟩ : syracuseStep 6569657 = 4927243) B4927243
theorem B4379771 : Blo 2305435 4379771 := bstep (se 1 (by rfl) ⟨3284828, by rfl⟩ : syracuseStep 4379771 = 6569657) B6569657
theorem B11679389 : Blo 2305435 11679389 := bstep (se 3 (by rfl) ⟨2189885, by rfl⟩ : syracuseStep 11679389 = 4379771) B4379771
theorem B7786259 : Blo 2305435 7786259 := bstep (se 1 (by rfl) ⟨5839694, by rfl⟩ : syracuseStep 7786259 = 11679389) B11679389
theorem B5190839 : Blo 2305435 5190839 := bstep (se 1 (by rfl) ⟨3893129, by rfl⟩ : syracuseStep 5190839 = 7786259) B7786259
theorem B3460559 : Blo 2305435 3460559 := bstep (se 1 (by rfl) ⟨2595419, by rfl⟩ : syracuseStep 3460559 = 5190839) B5190839
theorem B2307039 : Blo 2305435 2307039 := bstep (se 1 (by rfl) ⟨1730279, by rfl⟩ : syracuseStep 2307039 = 3460559) B3460559
theorem B3460565 : Blo 2305435 3460565 := bbase (se 7 (by rfl) ⟨40553, by rfl⟩ : syracuseStep 3460565 = 81107) (by norm_num)
theorem B2307043 : Blo 2305435 2307043 := bstep (se 1 (by rfl) ⟨1730282, by rfl⟩ : syracuseStep 2307043 = 3460565) B3460565
theorem B8759573 : Blo 2305435 8759573 := bbase (se 6 (by rfl) ⟨205302, by rfl⟩ : syracuseStep 8759573 = 410605) (by norm_num)
theorem B5839715 : Blo 2305435 5839715 := bstep (se 1 (by rfl) ⟨4379786, by rfl⟩ : syracuseStep 5839715 = 8759573) B8759573
theorem B3893143 : Blo 2305435 3893143 := bstep (se 1 (by rfl) ⟨2919857, by rfl⟩ : syracuseStep 3893143 = 5839715) B5839715
theorem B5190857 : Blo 2305435 5190857 := bstep (se 2 (by rfl) ⟨1946571, by rfl⟩ : syracuseStep 5190857 = 3893143) B3893143
theorem B3460571 : Blo 2305435 3460571 := bstep (se 1 (by rfl) ⟨2595428, by rfl⟩ : syracuseStep 3460571 = 5190857) B5190857
theorem B2307047 : Blo 2305435 2307047 := bstep (se 1 (by rfl) ⟨1730285, by rfl⟩ : syracuseStep 2307047 = 3460571) B3460571
theorem B2595433 : Blo 2305435 2595433 := bbase (se 2 (by rfl) ⟨973287, by rfl⟩ : syracuseStep 2595433 = 1946575) (by norm_num)
theorem B3460577 : Blo 2305435 3460577 := bstep (se 2 (by rfl) ⟨1297716, by rfl⟩ : syracuseStep 3460577 = 2595433) B2595433
theorem B2307051 : Blo 2305435 2307051 := bstep (se 1 (by rfl) ⟨1730288, by rfl⟩ : syracuseStep 2307051 = 3460577) B3460577
theorem B4927277 : Blo 2305435 4927277 := bbase (se 3 (by rfl) ⟨923864, by rfl⟩ : syracuseStep 4927277 = 1847729) (by norm_num)
theorem B13139405 : Blo 2305435 13139405 := bstep (se 3 (by rfl) ⟨2463638, by rfl⟩ : syracuseStep 13139405 = 4927277) B4927277
theorem B8759603 : Blo 2305435 8759603 := bstep (se 1 (by rfl) ⟨6569702, by rfl⟩ : syracuseStep 8759603 = 13139405) B13139405
theorem B5839735 : Blo 2305435 5839735 := bstep (se 1 (by rfl) ⟨4379801, by rfl⟩ : syracuseStep 5839735 = 8759603) B8759603
theorem B7786313 : Blo 2305435 7786313 := bstep (se 2 (by rfl) ⟨2919867, by rfl⟩ : syracuseStep 7786313 = 5839735) B5839735
theorem B5190875 : Blo 2305435 5190875 := bstep (se 1 (by rfl) ⟨3893156, by rfl⟩ : syracuseStep 5190875 = 7786313) B7786313
theorem B3460583 : Blo 2305435 3460583 := bstep (se 1 (by rfl) ⟨2595437, by rfl⟩ : syracuseStep 3460583 = 5190875) B5190875
theorem B2307055 : Blo 2305435 2307055 := bstep (se 1 (by rfl) ⟨1730291, by rfl⟩ : syracuseStep 2307055 = 3460583) B3460583
theorem B3460589 : Blo 2305435 3460589 := bbase (se 3 (by rfl) ⟨648860, by rfl⟩ : syracuseStep 3460589 = 1297721) (by norm_num)
theorem B2307059 : Blo 2305435 2307059 := bstep (se 1 (by rfl) ⟨1730294, by rfl⟩ : syracuseStep 2307059 = 3460589) B3460589
theorem B5190893 : Blo 2305435 5190893 := bbase (se 3 (by rfl) ⟨973292, by rfl⟩ : syracuseStep 5190893 = 1946585) (by norm_num)
theorem B3460595 : Blo 2305435 3460595 := bstep (se 1 (by rfl) ⟨2595446, by rfl⟩ : syracuseStep 3460595 = 5190893) B5190893
theorem B2307063 : Blo 2305435 2307063 := bstep (se 1 (by rfl) ⟨1730297, by rfl⟩ : syracuseStep 2307063 = 3460595) B3460595
theorem B3284869 : Blo 2305435 3284869 := bbase (se 4 (by rfl) ⟨307956, by rfl⟩ : syracuseStep 3284869 = 615913) (by norm_num)
theorem B4379825 : Blo 2305435 4379825 := bstep (se 2 (by rfl) ⟨1642434, by rfl⟩ : syracuseStep 4379825 = 3284869) B3284869
theorem B2919883 : Blo 2305435 2919883 := bstep (se 1 (by rfl) ⟨2189912, by rfl⟩ : syracuseStep 2919883 = 4379825) B4379825
theorem B3893177 : Blo 2305435 3893177 := bstep (se 2 (by rfl) ⟨1459941, by rfl⟩ : syracuseStep 3893177 = 2919883) B2919883
theorem B2595451 : Blo 2305435 2595451 := bstep (se 1 (by rfl) ⟨1946588, by rfl⟩ : syracuseStep 2595451 = 3893177) B3893177
theorem B3460601 : Blo 2305435 3460601 := bstep (se 2 (by rfl) ⟨1297725, by rfl⟩ : syracuseStep 3460601 = 2595451) B2595451
theorem B2307067 : Blo 2305435 2307067 := bstep (se 1 (by rfl) ⟨1730300, by rfl⟩ : syracuseStep 2307067 = 3460601) B3460601
theorem B33259349 : Blo 2305435 33259349 := bbase (se 9 (by rfl) ⟨97439, by rfl⟩ : syracuseStep 33259349 = 194879) (by norm_num)
theorem B88691597 : Blo 2305435 88691597 := bstep (se 3 (by rfl) ⟨16629674, by rfl⟩ : syracuseStep 88691597 = 33259349) B33259349
theorem B59127731 : Blo 2305435 59127731 := bstep (se 1 (by rfl) ⟨44345798, by rfl⟩ : syracuseStep 59127731 = 88691597) B88691597
theorem B39418487 : Blo 2305435 39418487 := bstep (se 1 (by rfl) ⟨29563865, by rfl⟩ : syracuseStep 39418487 = 59127731) B59127731
theorem B26278991 : Blo 2305435 26278991 := bstep (se 1 (by rfl) ⟨19709243, by rfl⟩ : syracuseStep 26278991 = 39418487) B39418487
theorem B17519327 : Blo 2305435 17519327 := bstep (se 1 (by rfl) ⟨13139495, by rfl⟩ : syracuseStep 17519327 = 26278991) B26278991
theorem B11679551 : Blo 2305435 11679551 := bstep (se 1 (by rfl) ⟨8759663, by rfl⟩ : syracuseStep 11679551 = 17519327) B17519327
theorem B7786367 : Blo 2305435 7786367 := bstep (se 1 (by rfl) ⟨5839775, by rfl⟩ : syracuseStep 7786367 = 11679551) B11679551
theorem B5190911 : Blo 2305435 5190911 := bstep (se 1 (by rfl) ⟨3893183, by rfl⟩ : syracuseStep 5190911 = 7786367) B7786367
theorem B3460607 : Blo 2305435 3460607 := bstep (se 1 (by rfl) ⟨2595455, by rfl⟩ : syracuseStep 3460607 = 5190911) B5190911
theorem B2307071 : Blo 2305435 2307071 := bstep (se 1 (by rfl) ⟨1730303, by rfl⟩ : syracuseStep 2307071 = 3460607) B3460607
theorem B3460613 : Blo 2305435 3460613 := bbase (se 4 (by rfl) ⟨324432, by rfl⟩ : syracuseStep 3460613 = 648865) (by norm_num)
theorem B2307075 : Blo 2305435 2307075 := bstep (se 1 (by rfl) ⟨1730306, by rfl⟩ : syracuseStep 2307075 = 3460613) B3460613
theorem B3893197 : Blo 2305435 3893197 := bbase (se 3 (by rfl) ⟨729974, by rfl⟩ : syracuseStep 3893197 = 1459949) (by norm_num)
theorem B5190929 : Blo 2305435 5190929 := bstep (se 2 (by rfl) ⟨1946598, by rfl⟩ : syracuseStep 5190929 = 3893197) B3893197
theorem B3460619 : Blo 2305435 3460619 := bstep (se 1 (by rfl) ⟨2595464, by rfl⟩ : syracuseStep 3460619 = 5190929) B5190929
theorem B2307079 : Blo 2305435 2307079 := bstep (se 1 (by rfl) ⟨1730309, by rfl⟩ : syracuseStep 2307079 = 3460619) B3460619
theorem B2595469 : Blo 2305435 2595469 := bbase (se 3 (by rfl) ⟨486650, by rfl⟩ : syracuseStep 2595469 = 973301) (by norm_num)
theorem B3460625 : Blo 2305435 3460625 := bstep (se 2 (by rfl) ⟨1297734, by rfl⟩ : syracuseStep 3460625 = 2595469) B2595469
theorem B2307083 : Blo 2305435 2307083 := bstep (se 1 (by rfl) ⟨1730312, by rfl⟩ : syracuseStep 2307083 = 3460625) B3460625
theorem B7786421 : Blo 2305435 7786421 := bbase (se 5 (by rfl) ⟨364988, by rfl⟩ : syracuseStep 7786421 = 729977) (by norm_num)
theorem B5190947 : Blo 2305435 5190947 := bstep (se 1 (by rfl) ⟨3893210, by rfl⟩ : syracuseStep 5190947 = 7786421) B7786421
theorem B3460631 : Blo 2305435 3460631 := bstep (se 1 (by rfl) ⟨2595473, by rfl⟩ : syracuseStep 3460631 = 5190947) B5190947
theorem B2307087 : Blo 2305435 2307087 := bstep (se 1 (by rfl) ⟨1730315, by rfl⟩ : syracuseStep 2307087 = 3460631) B3460631
theorem B3460637 : Blo 2305435 3460637 := bbase (se 3 (by rfl) ⟨648869, by rfl⟩ : syracuseStep 3460637 = 1297739) (by norm_num)
theorem B2307091 : Blo 2305435 2307091 := bstep (se 1 (by rfl) ⟨1730318, by rfl⟩ : syracuseStep 2307091 = 3460637) B3460637
theorem B5190965 : Blo 2305435 5190965 := bbase (se 5 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 5190965 = 486653) (by norm_num)
theorem B3460643 : Blo 2305435 3460643 := bstep (se 1 (by rfl) ⟨2595482, by rfl⟩ : syracuseStep 3460643 = 5190965) B5190965
theorem B2307095 : Blo 2305435 2307095 := bstep (se 1 (by rfl) ⟨1730321, by rfl⟩ : syracuseStep 2307095 = 3460643) B3460643
theorem B22173173 : Blo 2305435 22173173 := bbase (se 5 (by rfl) ⟨1039367, by rfl⟩ : syracuseStep 22173173 = 2078735) (by norm_num)
theorem B14782115 : Blo 2305435 14782115 := bstep (se 1 (by rfl) ⟨11086586, by rfl⟩ : syracuseStep 14782115 = 22173173) B22173173
theorem B9854743 : Blo 2305435 9854743 := bstep (se 1 (by rfl) ⟨7391057, by rfl⟩ : syracuseStep 9854743 = 14782115) B14782115
theorem B13139657 : Blo 2305435 13139657 := bstep (se 2 (by rfl) ⟨4927371, by rfl⟩ : syracuseStep 13139657 = 9854743) B9854743
theorem B8759771 : Blo 2305435 8759771 := bstep (se 1 (by rfl) ⟨6569828, by rfl⟩ : syracuseStep 8759771 = 13139657) B13139657
theorem B5839847 : Blo 2305435 5839847 := bstep (se 1 (by rfl) ⟨4379885, by rfl⟩ : syracuseStep 5839847 = 8759771) B8759771
theorem B3893231 : Blo 2305435 3893231 := bstep (se 1 (by rfl) ⟨2919923, by rfl⟩ : syracuseStep 3893231 = 5839847) B5839847
theorem B2595487 : Blo 2305435 2595487 := bstep (se 1 (by rfl) ⟨1946615, by rfl⟩ : syracuseStep 2595487 = 3893231) B3893231
theorem B3460649 : Blo 2305435 3460649 := bstep (se 2 (by rfl) ⟨1297743, by rfl⟩ : syracuseStep 3460649 = 2595487) B2595487
theorem B2307099 : Blo 2305435 2307099 := bstep (se 1 (by rfl) ⟨1730324, by rfl⟩ : syracuseStep 2307099 = 3460649) B3460649
theorem B3082573 : Blo 2305435 3082573 := bbase (se 3 (by rfl) ⟨577982, by rfl⟩ : syracuseStep 3082573 = 1155965) (by norm_num)
theorem B4110097 : Blo 2305435 4110097 := bstep (se 2 (by rfl) ⟨1541286, by rfl⟩ : syracuseStep 4110097 = 3082573) B3082573
theorem B5480129 : Blo 2305435 5480129 := bstep (se 2 (by rfl) ⟨2055048, by rfl⟩ : syracuseStep 5480129 = 4110097) B4110097
theorem B14613677 : Blo 2305435 14613677 := bstep (se 3 (by rfl) ⟨2740064, by rfl⟩ : syracuseStep 14613677 = 5480129) B5480129
theorem B9742451 : Blo 2305435 9742451 := bstep (se 1 (by rfl) ⟨7306838, by rfl⟩ : syracuseStep 9742451 = 14613677) B14613677
theorem B25979869 : Blo 2305435 25979869 := bstep (se 3 (by rfl) ⟨4871225, by rfl⟩ : syracuseStep 25979869 = 9742451) B9742451
theorem B34639825 : Blo 2305435 34639825 := bstep (se 2 (by rfl) ⟨12989934, by rfl⟩ : syracuseStep 34639825 = 25979869) B25979869
theorem B46186433 : Blo 2305435 46186433 := bstep (se 2 (by rfl) ⟨17319912, by rfl⟩ : syracuseStep 46186433 = 34639825) B34639825
theorem B30790955 : Blo 2305435 30790955 := bstep (se 1 (by rfl) ⟨23093216, by rfl⟩ : syracuseStep 30790955 = 46186433) B46186433
theorem B20527303 : Blo 2305435 20527303 := bstep (se 1 (by rfl) ⟨15395477, by rfl⟩ : syracuseStep 20527303 = 30790955) B30790955
theorem B27369737 : Blo 2305435 27369737 := bstep (se 2 (by rfl) ⟨10263651, by rfl⟩ : syracuseStep 27369737 = 20527303) B20527303
theorem B18246491 : Blo 2305435 18246491 := bstep (se 1 (by rfl) ⟨13684868, by rfl⟩ : syracuseStep 18246491 = 27369737) B27369737
theorem B12164327 : Blo 2305435 12164327 := bstep (se 1 (by rfl) ⟨9123245, by rfl⟩ : syracuseStep 12164327 = 18246491) B18246491
theorem B8109551 : Blo 2305435 8109551 := bstep (se 1 (by rfl) ⟨6082163, by rfl⟩ : syracuseStep 8109551 = 12164327) B12164327
theorem B5406367 : Blo 2305435 5406367 := bstep (se 1 (by rfl) ⟨4054775, by rfl⟩ : syracuseStep 5406367 = 8109551) B8109551
theorem B7208489 : Blo 2305435 7208489 := bstep (se 2 (by rfl) ⟨2703183, by rfl⟩ : syracuseStep 7208489 = 5406367) B5406367
theorem B4805659 : Blo 2305435 4805659 := bstep (se 1 (by rfl) ⟨3604244, by rfl⟩ : syracuseStep 4805659 = 7208489) B7208489
theorem B25630181 : Blo 2305435 25630181 := bstep (se 4 (by rfl) ⟨2402829, by rfl⟩ : syracuseStep 25630181 = 4805659) B4805659
theorem B17086787 : Blo 2305435 17086787 := bstep (se 1 (by rfl) ⟨12815090, by rfl⟩ : syracuseStep 17086787 = 25630181) B25630181
theorem B11391191 : Blo 2305435 11391191 := bstep (se 1 (by rfl) ⟨8543393, by rfl⟩ : syracuseStep 11391191 = 17086787) B17086787
theorem B7594127 : Blo 2305435 7594127 := bstep (se 1 (by rfl) ⟨5695595, by rfl⟩ : syracuseStep 7594127 = 11391191) B11391191
theorem B5062751 : Blo 2305435 5062751 := bstep (se 1 (by rfl) ⟨3797063, by rfl⟩ : syracuseStep 5062751 = 7594127) B7594127
theorem B3375167 : Blo 2305435 3375167 := bstep (se 1 (by rfl) ⟨2531375, by rfl⟩ : syracuseStep 3375167 = 5062751) B5062751
theorem B9000445 : Blo 2305435 9000445 := bstep (se 3 (by rfl) ⟨1687583, by rfl⟩ : syracuseStep 9000445 = 3375167) B3375167
theorem B12000593 : Blo 2305435 12000593 := bstep (se 2 (by rfl) ⟨4500222, by rfl⟩ : syracuseStep 12000593 = 9000445) B9000445
theorem B32001581 : Blo 2305435 32001581 := bstep (se 3 (by rfl) ⟨6000296, by rfl⟩ : syracuseStep 32001581 = 12000593) B12000593
theorem B21334387 : Blo 2305435 21334387 := bstep (se 1 (by rfl) ⟨16000790, by rfl⟩ : syracuseStep 21334387 = 32001581) B32001581
theorem B28445849 : Blo 2305435 28445849 := bstep (se 2 (by rfl) ⟨10667193, by rfl⟩ : syracuseStep 28445849 = 21334387) B21334387
theorem B18963899 : Blo 2305435 18963899 := bstep (se 1 (by rfl) ⟨14222924, by rfl⟩ : syracuseStep 18963899 = 28445849) B28445849
theorem B12642599 : Blo 2305435 12642599 := bstep (se 1 (by rfl) ⟨9481949, by rfl⟩ : syracuseStep 12642599 = 18963899) B18963899
theorem B33713597 : Blo 2305435 33713597 := bstep (se 3 (by rfl) ⟨6321299, by rfl⟩ : syracuseStep 33713597 = 12642599) B12642599
theorem B22475731 : Blo 2305435 22475731 := bstep (se 1 (by rfl) ⟨16856798, by rfl⟩ : syracuseStep 22475731 = 33713597) B33713597
theorem B29967641 : Blo 2305435 29967641 := bstep (se 2 (by rfl) ⟨11237865, by rfl⟩ : syracuseStep 29967641 = 22475731) B22475731
theorem B19978427 : Blo 2305435 19978427 := bstep (se 1 (by rfl) ⟨14983820, by rfl⟩ : syracuseStep 19978427 = 29967641) B29967641
theorem B13318951 : Blo 2305435 13318951 := bstep (se 1 (by rfl) ⟨9989213, by rfl⟩ : syracuseStep 13318951 = 19978427) B19978427
theorem B17758601 : Blo 2305435 17758601 := bstep (se 2 (by rfl) ⟨6659475, by rfl⟩ : syracuseStep 17758601 = 13318951) B13318951
theorem B11839067 : Blo 2305435 11839067 := bstep (se 1 (by rfl) ⟨8879300, by rfl⟩ : syracuseStep 11839067 = 17758601) B17758601
theorem B7892711 : Blo 2305435 7892711 := bstep (se 1 (by rfl) ⟨5919533, by rfl⟩ : syracuseStep 7892711 = 11839067) B11839067
theorem B5261807 : Blo 2305435 5261807 := bstep (se 1 (by rfl) ⟨3946355, by rfl⟩ : syracuseStep 5261807 = 7892711) B7892711
theorem B14031485 : Blo 2305435 14031485 := bstep (se 3 (by rfl) ⟨2630903, by rfl⟩ : syracuseStep 14031485 = 5261807) B5261807
theorem B9354323 : Blo 2305435 9354323 := bstep (se 1 (by rfl) ⟨7015742, by rfl⟩ : syracuseStep 9354323 = 14031485) B14031485
theorem B24944861 : Blo 2305435 24944861 := bstep (se 3 (by rfl) ⟨4677161, by rfl⟩ : syracuseStep 24944861 = 9354323) B9354323
theorem B16629907 : Blo 2305435 16629907 := bstep (se 1 (by rfl) ⟨12472430, by rfl⟩ : syracuseStep 16629907 = 24944861) B24944861
theorem B22173209 : Blo 2305435 22173209 := bstep (se 2 (by rfl) ⟨8314953, by rfl⟩ : syracuseStep 22173209 = 16629907) B16629907
theorem B14782139 : Blo 2305435 14782139 := bstep (se 1 (by rfl) ⟨11086604, by rfl⟩ : syracuseStep 14782139 = 22173209) B22173209
theorem B9854759 : Blo 2305435 9854759 := bstep (se 1 (by rfl) ⟨7391069, by rfl⟩ : syracuseStep 9854759 = 14782139) B14782139
theorem B6569839 : Blo 2305435 6569839 := bstep (se 1 (by rfl) ⟨4927379, by rfl⟩ : syracuseStep 6569839 = 9854759) B9854759
theorem B8759785 : Blo 2305435 8759785 := bstep (se 2 (by rfl) ⟨3284919, by rfl⟩ : syracuseStep 8759785 = 6569839) B6569839
theorem B11679713 : Blo 2305435 11679713 := bstep (se 2 (by rfl) ⟨4379892, by rfl⟩ : syracuseStep 11679713 = 8759785) B8759785
theorem B7786475 : Blo 2305435 7786475 := bstep (se 1 (by rfl) ⟨5839856, by rfl⟩ : syracuseStep 7786475 = 11679713) B11679713
theorem B5190983 : Blo 2305435 5190983 := bstep (se 1 (by rfl) ⟨3893237, by rfl⟩ : syracuseStep 5190983 = 7786475) B7786475
theorem B3460655 : Blo 2305435 3460655 := bstep (se 1 (by rfl) ⟨2595491, by rfl⟩ : syracuseStep 3460655 = 5190983) B5190983
theorem B2307103 : Blo 2305435 2307103 := bstep (se 1 (by rfl) ⟨1730327, by rfl⟩ : syracuseStep 2307103 = 3460655) B3460655
theorem B3460661 : Blo 2305435 3460661 := bbase (se 5 (by rfl) ⟨162218, by rfl⟩ : syracuseStep 3460661 = 324437) (by norm_num)
theorem B2307107 : Blo 2305435 2307107 := bstep (se 1 (by rfl) ⟨1730330, by rfl⟩ : syracuseStep 2307107 = 3460661) B3460661
theorem B5839877 : Blo 2305435 5839877 := bbase (se 4 (by rfl) ⟨547488, by rfl⟩ : syracuseStep 5839877 = 1094977) (by norm_num)
theorem B3893251 : Blo 2305435 3893251 := bstep (se 1 (by rfl) ⟨2919938, by rfl⟩ : syracuseStep 3893251 = 5839877) B5839877
theorem B5191001 : Blo 2305435 5191001 := bstep (se 2 (by rfl) ⟨1946625, by rfl⟩ : syracuseStep 5191001 = 3893251) B3893251
theorem B3460667 : Blo 2305435 3460667 := bstep (se 1 (by rfl) ⟨2595500, by rfl⟩ : syracuseStep 3460667 = 5191001) B5191001
theorem B2307111 : Blo 2305435 2307111 := bstep (se 1 (by rfl) ⟨1730333, by rfl⟩ : syracuseStep 2307111 = 3460667) B3460667
theorem B2595505 : Blo 2305435 2595505 := bbase (se 2 (by rfl) ⟨973314, by rfl⟩ : syracuseStep 2595505 = 1946629) (by norm_num)
theorem B3460673 : Blo 2305435 3460673 := bstep (se 2 (by rfl) ⟨1297752, by rfl⟩ : syracuseStep 3460673 = 2595505) B2595505
theorem B2307115 : Blo 2305435 2307115 := bstep (se 1 (by rfl) ⟨1730336, by rfl⟩ : syracuseStep 2307115 = 3460673) B3460673
theorem B6236261 : Blo 2305435 6236261 := bbase (se 4 (by rfl) ⟨584649, by rfl⟩ : syracuseStep 6236261 = 1169299) (by norm_num)
theorem B4157507 : Blo 2305435 4157507 := bstep (se 1 (by rfl) ⟨3118130, by rfl⟩ : syracuseStep 4157507 = 6236261) B6236261
theorem B2771671 : Blo 2305435 2771671 := bstep (se 1 (by rfl) ⟨2078753, by rfl⟩ : syracuseStep 2771671 = 4157507) B4157507
theorem B3695561 : Blo 2305435 3695561 := bstep (se 2 (by rfl) ⟨1385835, by rfl⟩ : syracuseStep 3695561 = 2771671) B2771671
theorem B2463707 : Blo 2305435 2463707 := bstep (se 1 (by rfl) ⟨1847780, by rfl⟩ : syracuseStep 2463707 = 3695561) B3695561
theorem B6569885 : Blo 2305435 6569885 := bstep (se 3 (by rfl) ⟨1231853, by rfl⟩ : syracuseStep 6569885 = 2463707) B2463707
theorem B4379923 : Blo 2305435 4379923 := bstep (se 1 (by rfl) ⟨3284942, by rfl⟩ : syracuseStep 4379923 = 6569885) B6569885
theorem B5839897 : Blo 2305435 5839897 := bstep (se 2 (by rfl) ⟨2189961, by rfl⟩ : syracuseStep 5839897 = 4379923) B4379923
theorem B7786529 : Blo 2305435 7786529 := bstep (se 2 (by rfl) ⟨2919948, by rfl⟩ : syracuseStep 7786529 = 5839897) B5839897
theorem B5191019 : Blo 2305435 5191019 := bstep (se 1 (by rfl) ⟨3893264, by rfl⟩ : syracuseStep 5191019 = 7786529) B7786529
theorem B3460679 : Blo 2305435 3460679 := bstep (se 1 (by rfl) ⟨2595509, by rfl⟩ : syracuseStep 3460679 = 5191019) B5191019
theorem B2307119 : Blo 2305435 2307119 := bstep (se 1 (by rfl) ⟨1730339, by rfl⟩ : syracuseStep 2307119 = 3460679) B3460679
theorem B3460685 : Blo 2305435 3460685 := bbase (se 3 (by rfl) ⟨648878, by rfl⟩ : syracuseStep 3460685 = 1297757) (by norm_num)
theorem B2307123 : Blo 2305435 2307123 := bstep (se 1 (by rfl) ⟨1730342, by rfl⟩ : syracuseStep 2307123 = 3460685) B3460685
theorem B5191037 : Blo 2305435 5191037 := bbase (se 3 (by rfl) ⟨973319, by rfl⟩ : syracuseStep 5191037 = 1946639) (by norm_num)
theorem B3460691 : Blo 2305435 3460691 := bstep (se 1 (by rfl) ⟨2595518, by rfl⟩ : syracuseStep 3460691 = 5191037) B5191037
theorem B2307127 : Blo 2305435 2307127 := bstep (se 1 (by rfl) ⟨1730345, by rfl⟩ : syracuseStep 2307127 = 3460691) B3460691
theorem B3893285 : Blo 2305435 3893285 := bbase (se 4 (by rfl) ⟨364995, by rfl⟩ : syracuseStep 3893285 = 729991) (by norm_num)
theorem B2595523 : Blo 2305435 2595523 := bstep (se 1 (by rfl) ⟨1946642, by rfl⟩ : syracuseStep 2595523 = 3893285) B3893285
theorem B3460697 : Blo 2305435 3460697 := bstep (se 2 (by rfl) ⟨1297761, by rfl⟩ : syracuseStep 3460697 = 2595523) B2595523
theorem B2307131 : Blo 2305435 2307131 := bstep (se 1 (by rfl) ⟨1730348, by rfl⟩ : syracuseStep 2307131 = 3460697) B3460697
theorem B3284965 : Blo 2305435 3284965 := bbase (se 4 (by rfl) ⟨307965, by rfl⟩ : syracuseStep 3284965 = 615931) (by norm_num)
theorem B17519813 : Blo 2305435 17519813 := bstep (se 4 (by rfl) ⟨1642482, by rfl⟩ : syracuseStep 17519813 = 3284965) B3284965
theorem B11679875 : Blo 2305435 11679875 := bstep (se 1 (by rfl) ⟨8759906, by rfl⟩ : syracuseStep 11679875 = 17519813) B17519813
theorem B7786583 : Blo 2305435 7786583 := bstep (se 1 (by rfl) ⟨5839937, by rfl⟩ : syracuseStep 7786583 = 11679875) B11679875
theorem B5191055 : Blo 2305435 5191055 := bstep (se 1 (by rfl) ⟨3893291, by rfl⟩ : syracuseStep 5191055 = 7786583) B7786583
theorem B3460703 : Blo 2305435 3460703 := bstep (se 1 (by rfl) ⟨2595527, by rfl⟩ : syracuseStep 3460703 = 5191055) B5191055
theorem B2307135 : Blo 2305435 2307135 := bstep (se 1 (by rfl) ⟨1730351, by rfl⟩ : syracuseStep 2307135 = 3460703) B3460703
theorem B3460709 : Blo 2305435 3460709 := bbase (se 4 (by rfl) ⟨324441, by rfl⟩ : syracuseStep 3460709 = 648883) (by norm_num)
theorem B2307139 : Blo 2305435 2307139 := bstep (se 1 (by rfl) ⟨1730354, by rfl⟩ : syracuseStep 2307139 = 3460709) B3460709
theorem B2463733 : Blo 2305435 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B3284977 : Blo 2305435 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B4379969 : Blo 2305435 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B2919979 : Blo 2305435 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B3893305 : Blo 2305435 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B5191073 : Blo 2305435 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B3460715 : Blo 2305435 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B2307143 : Blo 2305435 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B2595541 : Blo 2305435 2595541 := bbase (se 7 (by rfl) ⟨30416, by rfl⟩ : syracuseStep 2595541 = 60833) (by norm_num)
theorem B3460721 : Blo 2305435 3460721 := bstep (se 2 (by rfl) ⟨1297770, by rfl⟩ : syracuseStep 3460721 = 2595541) B2595541
theorem B2307147 : Blo 2305435 2307147 := bstep (se 1 (by rfl) ⟨1730360, by rfl⟩ : syracuseStep 2307147 = 3460721) B3460721
theorem B2919989 : Blo 2305435 2919989 := bbase (se 5 (by rfl) ⟨136874, by rfl⟩ : syracuseStep 2919989 = 273749) (by norm_num)
theorem B7786637 : Blo 2305435 7786637 := bstep (se 3 (by rfl) ⟨1459994, by rfl⟩ : syracuseStep 7786637 = 2919989) B2919989
theorem B5191091 : Blo 2305435 5191091 := bstep (se 1 (by rfl) ⟨3893318, by rfl⟩ : syracuseStep 5191091 = 7786637) B7786637
theorem B3460727 : Blo 2305435 3460727 := bstep (se 1 (by rfl) ⟨2595545, by rfl⟩ : syracuseStep 3460727 = 5191091) B5191091
theorem B2307151 : Blo 2305435 2307151 := bstep (se 1 (by rfl) ⟨1730363, by rfl⟩ : syracuseStep 2307151 = 3460727) B3460727
theorem B3460733 : Blo 2305435 3460733 := bbase (se 3 (by rfl) ⟨648887, by rfl⟩ : syracuseStep 3460733 = 1297775) (by norm_num)
theorem B2307155 : Blo 2305435 2307155 := bstep (se 1 (by rfl) ⟨1730366, by rfl⟩ : syracuseStep 2307155 = 3460733) B3460733
theorem B5191109 : Blo 2305435 5191109 := bbase (se 4 (by rfl) ⟨486666, by rfl⟩ : syracuseStep 5191109 = 973333) (by norm_num)
theorem B3460739 : Blo 2305435 3460739 := bstep (se 1 (by rfl) ⟨2595554, by rfl⟩ : syracuseStep 3460739 = 5191109) B5191109
theorem B2307159 : Blo 2305435 2307159 := bstep (se 1 (by rfl) ⟨1730369, by rfl⟩ : syracuseStep 2307159 = 3460739) B3460739
theorem B31571669 : Blo 2305435 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B21047779 : Blo 2305435 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B28063705 : Blo 2305435 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B37418273 : Blo 2305435 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B24945515 : Blo 2305435 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B16630343 : Blo 2305435 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B11086895 : Blo 2305435 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B7391263 : Blo 2305435 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B9855017 : Blo 2305435 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B6570011 : Blo 2305435 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B4380007 : Blo 2305435 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B5840009 : Blo 2305435 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B3893339 : Blo 2305435 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B2595559 : Blo 2305435 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B3460745 : Blo 2305435 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B2307163 : Blo 2305435 2307163 := bstep (se 1 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 2307163 = 3460745) B3460745
theorem B11680037 : Blo 2305435 11680037 := bbase (se 4 (by rfl) ⟨1095003, by rfl⟩ : syracuseStep 11680037 = 2190007) (by norm_num)
theorem B7786691 : Blo 2305435 7786691 := bstep (se 1 (by rfl) ⟨5840018, by rfl⟩ : syracuseStep 7786691 = 11680037) B11680037
theorem B5191127 : Blo 2305435 5191127 := bstep (se 1 (by rfl) ⟨3893345, by rfl⟩ : syracuseStep 5191127 = 7786691) B7786691
theorem B3460751 : Blo 2305435 3460751 := bstep (se 1 (by rfl) ⟨2595563, by rfl⟩ : syracuseStep 3460751 = 5191127) B5191127
theorem B2307167 : Blo 2305435 2307167 := bstep (se 1 (by rfl) ⟨1730375, by rfl⟩ : syracuseStep 2307167 = 3460751) B3460751
theorem B3460757 : Blo 2305435 3460757 := bbase (se 6 (by rfl) ⟨81111, by rfl⟩ : syracuseStep 3460757 = 162223) (by norm_num)
theorem B2307171 : Blo 2305435 2307171 := bstep (se 1 (by rfl) ⟨1730378, by rfl⟩ : syracuseStep 2307171 = 3460757) B3460757
theorem B8428661 : Blo 2305435 8428661 := bbase (se 5 (by rfl) ⟨395093, by rfl⟩ : syracuseStep 8428661 = 790187) (by norm_num)
theorem B89905717 : Blo 2305435 89905717 := bstep (se 5 (by rfl) ⟨4214330, by rfl⟩ : syracuseStep 89905717 = 8428661) B8428661
theorem B119874289 : Blo 2305435 119874289 := bstep (se 2 (by rfl) ⟨44952858, by rfl⟩ : syracuseStep 119874289 = 89905717) B89905717
theorem B159832385 : Blo 2305435 159832385 := bstep (se 2 (by rfl) ⟨59937144, by rfl⟩ : syracuseStep 159832385 = 119874289) B119874289
theorem B106554923 : Blo 2305435 106554923 := bstep (se 1 (by rfl) ⟨79916192, by rfl⟩ : syracuseStep 106554923 = 159832385) B159832385
theorem B71036615 : Blo 2305435 71036615 := bstep (se 1 (by rfl) ⟨53277461, by rfl⟩ : syracuseStep 71036615 = 106554923) B106554923
theorem B47357743 : Blo 2305435 47357743 := bstep (se 1 (by rfl) ⟨35518307, by rfl⟩ : syracuseStep 47357743 = 71036615) B71036615
theorem B63143657 : Blo 2305435 63143657 := bstep (se 2 (by rfl) ⟨23678871, by rfl⟩ : syracuseStep 63143657 = 47357743) B47357743
theorem B42095771 : Blo 2305435 42095771 := bstep (se 1 (by rfl) ⟨31571828, by rfl⟩ : syracuseStep 42095771 = 63143657) B63143657
theorem B28063847 : Blo 2305435 28063847 := bstep (se 1 (by rfl) ⟨21047885, by rfl⟩ : syracuseStep 28063847 = 42095771) B42095771
theorem B18709231 : Blo 2305435 18709231 := bstep (se 1 (by rfl) ⟨14031923, by rfl⟩ : syracuseStep 18709231 = 28063847) B28063847
theorem B24945641 : Blo 2305435 24945641 := bstep (se 2 (by rfl) ⟨9354615, by rfl⟩ : syracuseStep 24945641 = 18709231) B18709231
theorem B16630427 : Blo 2305435 16630427 := bstep (se 1 (by rfl) ⟨12472820, by rfl⟩ : syracuseStep 16630427 = 24945641) B24945641
theorem B11086951 : Blo 2305435 11086951 := bstep (se 1 (by rfl) ⟨8315213, by rfl⟩ : syracuseStep 11086951 = 16630427) B16630427
theorem B14782601 : Blo 2305435 14782601 := bstep (se 2 (by rfl) ⟨5543475, by rfl⟩ : syracuseStep 14782601 = 11086951) B11086951
theorem B9855067 : Blo 2305435 9855067 := bstep (se 1 (by rfl) ⟨7391300, by rfl⟩ : syracuseStep 9855067 = 14782601) B14782601
theorem B13140089 : Blo 2305435 13140089 := bstep (se 2 (by rfl) ⟨4927533, by rfl⟩ : syracuseStep 13140089 = 9855067) B9855067
theorem B8760059 : Blo 2305435 8760059 := bstep (se 1 (by rfl) ⟨6570044, by rfl⟩ : syracuseStep 8760059 = 13140089) B13140089
theorem B5840039 : Blo 2305435 5840039 := bstep (se 1 (by rfl) ⟨4380029, by rfl⟩ : syracuseStep 5840039 = 8760059) B8760059
theorem B3893359 : Blo 2305435 3893359 := bstep (se 1 (by rfl) ⟨2920019, by rfl⟩ : syracuseStep 3893359 = 5840039) B5840039
theorem B5191145 : Blo 2305435 5191145 := bstep (se 2 (by rfl) ⟨1946679, by rfl⟩ : syracuseStep 5191145 = 3893359) B3893359
theorem B3460763 : Blo 2305435 3460763 := bstep (se 1 (by rfl) ⟨2595572, by rfl⟩ : syracuseStep 3460763 = 5191145) B5191145
theorem B2307175 : Blo 2305435 2307175 := bstep (se 1 (by rfl) ⟨1730381, by rfl⟩ : syracuseStep 2307175 = 3460763) B3460763
theorem B2595577 : Blo 2305435 2595577 := bbase (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) (by norm_num)
theorem B3460769 : Blo 2305435 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B2307179 : Blo 2305435 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B3946493 : Blo 2305435 3946493 := bbase (se 3 (by rfl) ⟨739967, by rfl⟩ : syracuseStep 3946493 = 1479935) (by norm_num)
theorem B10523981 : Blo 2305435 10523981 := bstep (se 3 (by rfl) ⟨1973246, by rfl⟩ : syracuseStep 10523981 = 3946493) B3946493
theorem B7015987 : Blo 2305435 7015987 := bstep (se 1 (by rfl) ⟨5261990, by rfl⟩ : syracuseStep 7015987 = 10523981) B10523981
theorem B9354649 : Blo 2305435 9354649 := bstep (se 2 (by rfl) ⟨3507993, by rfl⟩ : syracuseStep 9354649 = 7015987) B7015987
theorem B12472865 : Blo 2305435 12472865 := bstep (se 2 (by rfl) ⟨4677324, by rfl⟩ : syracuseStep 12472865 = 9354649) B9354649
theorem B8315243 : Blo 2305435 8315243 := bstep (se 1 (by rfl) ⟨6236432, by rfl⟩ : syracuseStep 8315243 = 12472865) B12472865
theorem B5543495 : Blo 2305435 5543495 := bstep (se 1 (by rfl) ⟨4157621, by rfl⟩ : syracuseStep 5543495 = 8315243) B8315243
theorem B3695663 : Blo 2305435 3695663 := bstep (se 1 (by rfl) ⟨2771747, by rfl⟩ : syracuseStep 3695663 = 5543495) B5543495
theorem B9855101 : Blo 2305435 9855101 := bstep (se 3 (by rfl) ⟨1847831, by rfl⟩ : syracuseStep 9855101 = 3695663) B3695663
theorem B6570067 : Blo 2305435 6570067 := bstep (se 1 (by rfl) ⟨4927550, by rfl⟩ : syracuseStep 6570067 = 9855101) B9855101
theorem B8760089 : Blo 2305435 8760089 := bstep (se 2 (by rfl) ⟨3285033, by rfl⟩ : syracuseStep 8760089 = 6570067) B6570067
theorem B5840059 : Blo 2305435 5840059 := bstep (se 1 (by rfl) ⟨4380044, by rfl⟩ : syracuseStep 5840059 = 8760089) B8760089
theorem B7786745 : Blo 2305435 7786745 := bstep (se 2 (by rfl) ⟨2920029, by rfl⟩ : syracuseStep 7786745 = 5840059) B5840059
theorem B5191163 : Blo 2305435 5191163 := bstep (se 1 (by rfl) ⟨3893372, by rfl⟩ : syracuseStep 5191163 = 7786745) B7786745
theorem B3460775 : Blo 2305435 3460775 := bstep (se 1 (by rfl) ⟨2595581, by rfl⟩ : syracuseStep 3460775 = 5191163) B5191163
theorem B2307183 : Blo 2305435 2307183 := bstep (se 1 (by rfl) ⟨1730387, by rfl⟩ : syracuseStep 2307183 = 3460775) B3460775
theorem B3460781 : Blo 2305435 3460781 := bbase (se 3 (by rfl) ⟨648896, by rfl⟩ : syracuseStep 3460781 = 1297793) (by norm_num)
theorem B2307187 : Blo 2305435 2307187 := bstep (se 1 (by rfl) ⟨1730390, by rfl⟩ : syracuseStep 2307187 = 3460781) B3460781
theorem B5191181 : Blo 2305435 5191181 := bbase (se 3 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 5191181 = 1946693) (by norm_num)
theorem B3460787 : Blo 2305435 3460787 := bstep (se 1 (by rfl) ⟨2595590, by rfl⟩ : syracuseStep 3460787 = 5191181) B5191181
theorem B2307191 : Blo 2305435 2307191 := bstep (se 1 (by rfl) ⟨1730393, by rfl⟩ : syracuseStep 2307191 = 3460787) B3460787
theorem B2920045 : Blo 2305435 2920045 := bbase (se 3 (by rfl) ⟨547508, by rfl⟩ : syracuseStep 2920045 = 1095017) (by norm_num)
theorem B3893393 : Blo 2305435 3893393 := bstep (se 2 (by rfl) ⟨1460022, by rfl⟩ : syracuseStep 3893393 = 2920045) B2920045
theorem B2595595 : Blo 2305435 2595595 := bstep (se 1 (by rfl) ⟨1946696, by rfl⟩ : syracuseStep 2595595 = 3893393) B3893393
theorem B3460793 : Blo 2305435 3460793 := bstep (se 2 (by rfl) ⟨1297797, by rfl⟩ : syracuseStep 3460793 = 2595595) B2595595
theorem B2307195 : Blo 2305435 2307195 := bstep (se 1 (by rfl) ⟨1730396, by rfl⟩ : syracuseStep 2307195 = 3460793) B3460793
theorem B12472949 : Blo 2305435 12472949 := bbase (se 5 (by rfl) ⟨584669, by rfl⟩ : syracuseStep 12472949 = 1169339) (by norm_num)
theorem B8315299 : Blo 2305435 8315299 := bstep (se 1 (by rfl) ⟨6236474, by rfl⟩ : syracuseStep 8315299 = 12472949) B12472949
theorem B11087065 : Blo 2305435 11087065 := bstep (se 2 (by rfl) ⟨4157649, by rfl⟩ : syracuseStep 11087065 = 8315299) B8315299
theorem B14782753 : Blo 2305435 14782753 := bstep (se 2 (by rfl) ⟨5543532, by rfl⟩ : syracuseStep 14782753 = 11087065) B11087065
theorem B19710337 : Blo 2305435 19710337 := bstep (se 2 (by rfl) ⟨7391376, by rfl⟩ : syracuseStep 19710337 = 14782753) B14782753
theorem B26280449 : Blo 2305435 26280449 := bstep (se 2 (by rfl) ⟨9855168, by rfl⟩ : syracuseStep 26280449 = 19710337) B19710337
theorem B17520299 : Blo 2305435 17520299 := bstep (se 1 (by rfl) ⟨13140224, by rfl⟩ : syracuseStep 17520299 = 26280449) B26280449
theorem B11680199 : Blo 2305435 11680199 := bstep (se 1 (by rfl) ⟨8760149, by rfl⟩ : syracuseStep 11680199 = 17520299) B17520299
theorem B7786799 : Blo 2305435 7786799 := bstep (se 1 (by rfl) ⟨5840099, by rfl⟩ : syracuseStep 7786799 = 11680199) B11680199
theorem B5191199 : Blo 2305435 5191199 := bstep (se 1 (by rfl) ⟨3893399, by rfl⟩ : syracuseStep 5191199 = 7786799) B7786799
theorem B3460799 : Blo 2305435 3460799 := bstep (se 1 (by rfl) ⟨2595599, by rfl⟩ : syracuseStep 3460799 = 5191199) B5191199
theorem B2307199 : Blo 2305435 2307199 := bstep (se 1 (by rfl) ⟨1730399, by rfl⟩ : syracuseStep 2307199 = 3460799) B3460799
theorem B3460805 : Blo 2305435 3460805 := bbase (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) (by norm_num)
theorem B2307203 : Blo 2305435 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B3893413 : Blo 2305435 3893413 := bbase (se 4 (by rfl) ⟨365007, by rfl⟩ : syracuseStep 3893413 = 730015) (by norm_num)
theorem B5191217 : Blo 2305435 5191217 := bstep (se 2 (by rfl) ⟨1946706, by rfl⟩ : syracuseStep 5191217 = 3893413) B3893413
theorem B3460811 : Blo 2305435 3460811 := bstep (se 1 (by rfl) ⟨2595608, by rfl⟩ : syracuseStep 3460811 = 5191217) B5191217
theorem B2307207 : Blo 2305435 2307207 := bstep (se 1 (by rfl) ⟨1730405, by rfl⟩ : syracuseStep 2307207 = 3460811) B3460811
theorem B2595613 : Blo 2305435 2595613 := bbase (se 3 (by rfl) ⟨486677, by rfl⟩ : syracuseStep 2595613 = 973355) (by norm_num)
theorem B3460817 : Blo 2305435 3460817 := bstep (se 2 (by rfl) ⟨1297806, by rfl⟩ : syracuseStep 3460817 = 2595613) B2595613
theorem B2307211 : Blo 2305435 2307211 := bstep (se 1 (by rfl) ⟨1730408, by rfl⟩ : syracuseStep 2307211 = 3460817) B3460817
theorem B7786853 : Blo 2305435 7786853 := bbase (se 4 (by rfl) ⟨730017, by rfl⟩ : syracuseStep 7786853 = 1460035) (by norm_num)
theorem B5191235 : Blo 2305435 5191235 := bstep (se 1 (by rfl) ⟨3893426, by rfl⟩ : syracuseStep 5191235 = 7786853) B7786853
theorem B3460823 : Blo 2305435 3460823 := bstep (se 1 (by rfl) ⟨2595617, by rfl⟩ : syracuseStep 3460823 = 5191235) B5191235
theorem B2307215 : Blo 2305435 2307215 := bstep (se 1 (by rfl) ⟨1730411, by rfl⟩ : syracuseStep 2307215 = 3460823) B3460823
theorem B3460829 : Blo 2305435 3460829 := bbase (se 3 (by rfl) ⟨648905, by rfl⟩ : syracuseStep 3460829 = 1297811) (by norm_num)
theorem B2307219 : Blo 2305435 2307219 := bstep (se 1 (by rfl) ⟨1730414, by rfl⟩ : syracuseStep 2307219 = 3460829) B3460829
theorem B5191253 : Blo 2305435 5191253 := bbase (se 8 (by rfl) ⟨30417, by rfl⟩ : syracuseStep 5191253 = 60835) (by norm_num)
theorem B3460835 : Blo 2305435 3460835 := bstep (se 1 (by rfl) ⟨2595626, by rfl⟩ : syracuseStep 3460835 = 5191253) B5191253
theorem B2307223 : Blo 2305435 2307223 := bstep (se 1 (by rfl) ⟨1730417, by rfl⟩ : syracuseStep 2307223 = 3460835) B3460835
theorem B4927645 : Blo 2305435 4927645 := bbase (se 3 (by rfl) ⟨923933, by rfl⟩ : syracuseStep 4927645 = 1847867) (by norm_num)
theorem B6570193 : Blo 2305435 6570193 := bstep (se 2 (by rfl) ⟨2463822, by rfl⟩ : syracuseStep 6570193 = 4927645) B4927645
theorem B8760257 : Blo 2305435 8760257 := bstep (se 2 (by rfl) ⟨3285096, by rfl⟩ : syracuseStep 8760257 = 6570193) B6570193
theorem B5840171 : Blo 2305435 5840171 := bstep (se 1 (by rfl) ⟨4380128, by rfl⟩ : syracuseStep 5840171 = 8760257) B8760257
theorem B3893447 : Blo 2305435 3893447 := bstep (se 1 (by rfl) ⟨2920085, by rfl⟩ : syracuseStep 3893447 = 5840171) B5840171
theorem B2595631 : Blo 2305435 2595631 := bstep (se 1 (by rfl) ⟨1946723, by rfl⟩ : syracuseStep 2595631 = 3893447) B3893447
theorem B3460841 : Blo 2305435 3460841 := bstep (se 2 (by rfl) ⟨1297815, by rfl⟩ : syracuseStep 3460841 = 2595631) B2595631
theorem B2307227 : Blo 2305435 2307227 := bstep (se 1 (by rfl) ⟨1730420, by rfl⟩ : syracuseStep 2307227 = 3460841) B3460841
theorem B4677421 : Blo 2305435 4677421 := bbase (se 3 (by rfl) ⟨877016, by rfl⟩ : syracuseStep 4677421 = 1754033) (by norm_num)
theorem B6236561 : Blo 2305435 6236561 := bstep (se 2 (by rfl) ⟨2338710, by rfl⟩ : syracuseStep 6236561 = 4677421) B4677421
theorem B16630829 : Blo 2305435 16630829 := bstep (se 3 (by rfl) ⟨3118280, by rfl⟩ : syracuseStep 16630829 = 6236561) B6236561
theorem B11087219 : Blo 2305435 11087219 := bstep (se 1 (by rfl) ⟨8315414, by rfl⟩ : syracuseStep 11087219 = 16630829) B16630829
theorem B29565917 : Blo 2305435 29565917 := bstep (se 3 (by rfl) ⟨5543609, by rfl⟩ : syracuseStep 29565917 = 11087219) B11087219
theorem B19710611 : Blo 2305435 19710611 := bstep (se 1 (by rfl) ⟨14782958, by rfl⟩ : syracuseStep 19710611 = 29565917) B29565917
theorem B13140407 : Blo 2305435 13140407 := bstep (se 1 (by rfl) ⟨9855305, by rfl⟩ : syracuseStep 13140407 = 19710611) B19710611
theorem B8760271 : Blo 2305435 8760271 := bstep (se 1 (by rfl) ⟨6570203, by rfl⟩ : syracuseStep 8760271 = 13140407) B13140407
theorem B11680361 : Blo 2305435 11680361 := bstep (se 2 (by rfl) ⟨4380135, by rfl⟩ : syracuseStep 11680361 = 8760271) B8760271
theorem B7786907 : Blo 2305435 7786907 := bstep (se 1 (by rfl) ⟨5840180, by rfl⟩ : syracuseStep 7786907 = 11680361) B11680361
theorem B5191271 : Blo 2305435 5191271 := bstep (se 1 (by rfl) ⟨3893453, by rfl⟩ : syracuseStep 5191271 = 7786907) B7786907
theorem B3460847 : Blo 2305435 3460847 := bstep (se 1 (by rfl) ⟨2595635, by rfl⟩ : syracuseStep 3460847 = 5191271) B5191271
theorem B2307231 : Blo 2305435 2307231 := bstep (se 1 (by rfl) ⟨1730423, by rfl⟩ : syracuseStep 2307231 = 3460847) B3460847
theorem B3460853 : Blo 2305435 3460853 := bbase (se 5 (by rfl) ⟨162227, by rfl⟩ : syracuseStep 3460853 = 324455) (by norm_num)
theorem B2307235 : Blo 2305435 2307235 := bstep (se 1 (by rfl) ⟨1730426, by rfl⟩ : syracuseStep 2307235 = 3460853) B3460853
theorem B11238533 : Blo 2305435 11238533 := bbase (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) (by norm_num)
theorem B7492355 : Blo 2305435 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B4994903 : Blo 2305435 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B13319741 : Blo 2305435 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B35519309 : Blo 2305435 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B23679539 : Blo 2305435 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B15786359 : Blo 2305435 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B10524239 : Blo 2305435 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B7016159 : Blo 2305435 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B4677439 : Blo 2305435 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B6236585 : Blo 2305435 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B4157723 : Blo 2305435 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B2771815 : Blo 2305435 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B3695753 : Blo 2305435 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B9855341 : Blo 2305435 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B6570227 : Blo 2305435 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B4380151 : Blo 2305435 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B5840201 : Blo 2305435 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B3893467 : Blo 2305435 3893467 := bstep (se 1 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 3893467 = 5840201) B5840201
theorem B5191289 : Blo 2305435 5191289 := bstep (se 2 (by rfl) ⟨1946733, by rfl⟩ : syracuseStep 5191289 = 3893467) B3893467
theorem B3460859 : Blo 2305435 3460859 := bstep (se 1 (by rfl) ⟨2595644, by rfl⟩ : syracuseStep 3460859 = 5191289) B5191289
theorem B2307239 : Blo 2305435 2307239 := bstep (se 1 (by rfl) ⟨1730429, by rfl⟩ : syracuseStep 2307239 = 3460859) B3460859
theorem B2595649 : Blo 2305435 2595649 := bbase (se 2 (by rfl) ⟨973368, by rfl⟩ : syracuseStep 2595649 = 1946737) (by norm_num)
theorem B3460865 : Blo 2305435 3460865 := bstep (se 2 (by rfl) ⟨1297824, by rfl⟩ : syracuseStep 3460865 = 2595649) B2595649
theorem B2307243 : Blo 2305435 2307243 := bstep (se 1 (by rfl) ⟨1730432, by rfl⟩ : syracuseStep 2307243 = 3460865) B3460865
theorem B5840221 : Blo 2305435 5840221 := bbase (se 3 (by rfl) ⟨1095041, by rfl⟩ : syracuseStep 5840221 = 2190083) (by norm_num)
theorem B7786961 : Blo 2305435 7786961 := bstep (se 2 (by rfl) ⟨2920110, by rfl⟩ : syracuseStep 7786961 = 5840221) B5840221
theorem B5191307 : Blo 2305435 5191307 := bstep (se 1 (by rfl) ⟨3893480, by rfl⟩ : syracuseStep 5191307 = 7786961) B7786961
theorem B3460871 : Blo 2305435 3460871 := bstep (se 1 (by rfl) ⟨2595653, by rfl⟩ : syracuseStep 3460871 = 5191307) B5191307
theorem B2307247 : Blo 2305435 2307247 := bstep (se 1 (by rfl) ⟨1730435, by rfl⟩ : syracuseStep 2307247 = 3460871) B3460871
theorem B3460877 : Blo 2305435 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2307251 : Blo 2305435 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B5191325 : Blo 2305435 5191325 := bbase (se 3 (by rfl) ⟨973373, by rfl⟩ : syracuseStep 5191325 = 1946747) (by norm_num)
theorem B3460883 : Blo 2305435 3460883 := bstep (se 1 (by rfl) ⟨2595662, by rfl⟩ : syracuseStep 3460883 = 5191325) B5191325
theorem B2307255 : Blo 2305435 2307255 := bstep (se 1 (by rfl) ⟨1730441, by rfl⟩ : syracuseStep 2307255 = 3460883) B3460883
theorem B3893501 : Blo 2305435 3893501 := bbase (se 3 (by rfl) ⟨730031, by rfl⟩ : syracuseStep 3893501 = 1460063) (by norm_num)
theorem B2595667 : Blo 2305435 2595667 := bstep (se 1 (by rfl) ⟨1946750, by rfl⟩ : syracuseStep 2595667 = 3893501) B3893501
theorem B3460889 : Blo 2305435 3460889 := bstep (se 2 (by rfl) ⟨1297833, by rfl⟩ : syracuseStep 3460889 = 2595667) B2595667
theorem B2307259 : Blo 2305435 2307259 := bstep (se 1 (by rfl) ⟨1730444, by rfl⟩ : syracuseStep 2307259 = 3460889) B3460889
theorem B5262173 : Blo 2305435 5262173 := bbase (se 3 (by rfl) ⟨986657, by rfl⟩ : syracuseStep 5262173 = 1973315) (by norm_num)
theorem B3508115 : Blo 2305435 3508115 := bstep (se 1 (by rfl) ⟨2631086, by rfl⟩ : syracuseStep 3508115 = 5262173) B5262173
theorem B9354973 : Blo 2305435 9354973 := bstep (se 3 (by rfl) ⟨1754057, by rfl⟩ : syracuseStep 9354973 = 3508115) B3508115
theorem B12473297 : Blo 2305435 12473297 := bstep (se 2 (by rfl) ⟨4677486, by rfl⟩ : syracuseStep 12473297 = 9354973) B9354973
theorem B8315531 : Blo 2305435 8315531 := bstep (se 1 (by rfl) ⟨6236648, by rfl⟩ : syracuseStep 8315531 = 12473297) B12473297
theorem B5543687 : Blo 2305435 5543687 := bstep (se 1 (by rfl) ⟨4157765, by rfl⟩ : syracuseStep 5543687 = 8315531) B8315531
theorem B3695791 : Blo 2305435 3695791 := bstep (se 1 (by rfl) ⟨2771843, by rfl⟩ : syracuseStep 3695791 = 5543687) B5543687
theorem B4927721 : Blo 2305435 4927721 := bstep (se 2 (by rfl) ⟨1847895, by rfl⟩ : syracuseStep 4927721 = 3695791) B3695791
theorem B13140589 : Blo 2305435 13140589 := bstep (se 3 (by rfl) ⟨2463860, by rfl⟩ : syracuseStep 13140589 = 4927721) B4927721
theorem B17520785 : Blo 2305435 17520785 := bstep (se 2 (by rfl) ⟨6570294, by rfl⟩ : syracuseStep 17520785 = 13140589) B13140589
theorem B11680523 : Blo 2305435 11680523 := bstep (se 1 (by rfl) ⟨8760392, by rfl⟩ : syracuseStep 11680523 = 17520785) B17520785
theorem B7787015 : Blo 2305435 7787015 := bstep (se 1 (by rfl) ⟨5840261, by rfl⟩ : syracuseStep 7787015 = 11680523) B11680523
theorem B5191343 : Blo 2305435 5191343 := bstep (se 1 (by rfl) ⟨3893507, by rfl⟩ : syracuseStep 5191343 = 7787015) B7787015
theorem B3460895 : Blo 2305435 3460895 := bstep (se 1 (by rfl) ⟨2595671, by rfl⟩ : syracuseStep 3460895 = 5191343) B5191343
theorem B2307263 : Blo 2305435 2307263 := bstep (se 1 (by rfl) ⟨1730447, by rfl⟩ : syracuseStep 2307263 = 3460895) B3460895
theorem B3460901 : Blo 2305435 3460901 := bbase (se 4 (by rfl) ⟨324459, by rfl⟩ : syracuseStep 3460901 = 648919) (by norm_num)
theorem B2307267 : Blo 2305435 2307267 := bstep (se 1 (by rfl) ⟨1730450, by rfl⟩ : syracuseStep 2307267 = 3460901) B3460901
theorem B2920141 : Blo 2305435 2920141 := bbase (se 3 (by rfl) ⟨547526, by rfl⟩ : syracuseStep 2920141 = 1095053) (by norm_num)
theorem B3893521 : Blo 2305435 3893521 := bstep (se 2 (by rfl) ⟨1460070, by rfl⟩ : syracuseStep 3893521 = 2920141) B2920141
theorem B5191361 : Blo 2305435 5191361 := bstep (se 2 (by rfl) ⟨1946760, by rfl⟩ : syracuseStep 5191361 = 3893521) B3893521
theorem B3460907 : Blo 2305435 3460907 := bstep (se 1 (by rfl) ⟨2595680, by rfl⟩ : syracuseStep 3460907 = 5191361) B5191361
theorem B2307271 : Blo 2305435 2307271 := bstep (se 1 (by rfl) ⟨1730453, by rfl⟩ : syracuseStep 2307271 = 3460907) B3460907
theorem B2595685 : Blo 2305435 2595685 := bbase (se 4 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 2595685 = 486691) (by norm_num)
theorem B3460913 : Blo 2305435 3460913 := bstep (se 2 (by rfl) ⟨1297842, by rfl⟩ : syracuseStep 3460913 = 2595685) B2595685
theorem B2307275 : Blo 2305435 2307275 := bstep (se 1 (by rfl) ⟨1730456, by rfl⟩ : syracuseStep 2307275 = 3460913) B3460913
theorem B6570341 : Blo 2305435 6570341 := bbase (se 4 (by rfl) ⟨615969, by rfl⟩ : syracuseStep 6570341 = 1231939) (by norm_num)
theorem B4380227 : Blo 2305435 4380227 := bstep (se 1 (by rfl) ⟨3285170, by rfl⟩ : syracuseStep 4380227 = 6570341) B6570341
theorem B2920151 : Blo 2305435 2920151 := bstep (se 1 (by rfl) ⟨2190113, by rfl⟩ : syracuseStep 2920151 = 4380227) B4380227
theorem B7787069 : Blo 2305435 7787069 := bstep (se 3 (by rfl) ⟨1460075, by rfl⟩ : syracuseStep 7787069 = 2920151) B2920151
theorem B5191379 : Blo 2305435 5191379 := bstep (se 1 (by rfl) ⟨3893534, by rfl⟩ : syracuseStep 5191379 = 7787069) B7787069
theorem B3460919 : Blo 2305435 3460919 := bstep (se 1 (by rfl) ⟨2595689, by rfl⟩ : syracuseStep 3460919 = 5191379) B5191379
theorem B2307279 : Blo 2305435 2307279 := bstep (se 1 (by rfl) ⟨1730459, by rfl⟩ : syracuseStep 2307279 = 3460919) B3460919
theorem B3460925 : Blo 2305435 3460925 := bbase (se 3 (by rfl) ⟨648923, by rfl⟩ : syracuseStep 3460925 = 1297847) (by norm_num)
theorem B2307283 : Blo 2305435 2307283 := bstep (se 1 (by rfl) ⟨1730462, by rfl⟩ : syracuseStep 2307283 = 3460925) B3460925
theorem B5191397 : Blo 2305435 5191397 := bbase (se 4 (by rfl) ⟨486693, by rfl⟩ : syracuseStep 5191397 = 973387) (by norm_num)
theorem B3460931 : Blo 2305435 3460931 := bstep (se 1 (by rfl) ⟨2595698, by rfl⟩ : syracuseStep 3460931 = 5191397) B5191397
theorem B2307287 : Blo 2305435 2307287 := bstep (se 1 (by rfl) ⟨1730465, by rfl⟩ : syracuseStep 2307287 = 3460931) B3460931
theorem B5840333 : Blo 2305435 5840333 := bbase (se 3 (by rfl) ⟨1095062, by rfl⟩ : syracuseStep 5840333 = 2190125) (by norm_num)
theorem B3893555 : Blo 2305435 3893555 := bstep (se 1 (by rfl) ⟨2920166, by rfl⟩ : syracuseStep 3893555 = 5840333) B5840333
theorem B2595703 : Blo 2305435 2595703 := bstep (se 1 (by rfl) ⟨1946777, by rfl⟩ : syracuseStep 2595703 = 3893555) B3893555
theorem B3460937 : Blo 2305435 3460937 := bstep (se 2 (by rfl) ⟨1297851, by rfl⟩ : syracuseStep 3460937 = 2595703) B2595703
theorem B2307291 : Blo 2305435 2307291 := bstep (se 1 (by rfl) ⟨1730468, by rfl⟩ : syracuseStep 2307291 = 3460937) B3460937
theorem B5543765 : Blo 2305435 5543765 := bbase (se 9 (by rfl) ⟨16241, by rfl⟩ : syracuseStep 5543765 = 32483) (by norm_num)
theorem B3695843 : Blo 2305435 3695843 := bstep (se 1 (by rfl) ⟨2771882, by rfl⟩ : syracuseStep 3695843 = 5543765) B5543765
theorem B2463895 : Blo 2305435 2463895 := bstep (se 1 (by rfl) ⟨1847921, by rfl⟩ : syracuseStep 2463895 = 3695843) B3695843
theorem B3285193 : Blo 2305435 3285193 := bstep (se 2 (by rfl) ⟨1231947, by rfl⟩ : syracuseStep 3285193 = 2463895) B2463895
theorem B4380257 : Blo 2305435 4380257 := bstep (se 2 (by rfl) ⟨1642596, by rfl⟩ : syracuseStep 4380257 = 3285193) B3285193
theorem B11680685 : Blo 2305435 11680685 := bstep (se 3 (by rfl) ⟨2190128, by rfl⟩ : syracuseStep 11680685 = 4380257) B4380257
theorem B7787123 : Blo 2305435 7787123 := bstep (se 1 (by rfl) ⟨5840342, by rfl⟩ : syracuseStep 7787123 = 11680685) B11680685
theorem B5191415 : Blo 2305435 5191415 := bstep (se 1 (by rfl) ⟨3893561, by rfl⟩ : syracuseStep 5191415 = 7787123) B7787123
theorem B3460943 : Blo 2305435 3460943 := bstep (se 1 (by rfl) ⟨2595707, by rfl⟩ : syracuseStep 3460943 = 5191415) B5191415
theorem B2307295 : Blo 2305435 2307295 := bstep (se 1 (by rfl) ⟨1730471, by rfl⟩ : syracuseStep 2307295 = 3460943) B3460943
theorem B3460949 : Blo 2305435 3460949 := bbase (se 9 (by rfl) ⟨10139, by rfl⟩ : syracuseStep 3460949 = 20279) (by norm_num)
theorem B2307299 : Blo 2305435 2307299 := bstep (se 1 (by rfl) ⟨1730474, by rfl⟩ : syracuseStep 2307299 = 3460949) B3460949
theorem B5063189 : Blo 2305435 5063189 := bbase (se 6 (by rfl) ⟨118668, by rfl⟩ : syracuseStep 5063189 = 237337) (by norm_num)
theorem B13501837 : Blo 2305435 13501837 := bstep (se 3 (by rfl) ⟨2531594, by rfl⟩ : syracuseStep 13501837 = 5063189) B5063189
theorem B18002449 : Blo 2305435 18002449 := bstep (se 2 (by rfl) ⟨6750918, by rfl⟩ : syracuseStep 18002449 = 13501837) B13501837
theorem B24003265 : Blo 2305435 24003265 := bstep (se 2 (by rfl) ⟨9001224, by rfl⟩ : syracuseStep 24003265 = 18002449) B18002449
theorem B32004353 : Blo 2305435 32004353 := bstep (se 2 (by rfl) ⟨12001632, by rfl⟩ : syracuseStep 32004353 = 24003265) B24003265
theorem B85344941 : Blo 2305435 85344941 := bstep (se 3 (by rfl) ⟨16002176, by rfl⟩ : syracuseStep 85344941 = 32004353) B32004353
theorem B56896627 : Blo 2305435 56896627 := bstep (se 1 (by rfl) ⟨42672470, by rfl⟩ : syracuseStep 56896627 = 85344941) B85344941
theorem B75862169 : Blo 2305435 75862169 := bstep (se 2 (by rfl) ⟨28448313, by rfl⟩ : syracuseStep 75862169 = 56896627) B56896627
theorem B50574779 : Blo 2305435 50574779 := bstep (se 1 (by rfl) ⟨37931084, by rfl⟩ : syracuseStep 50574779 = 75862169) B75862169
theorem B33716519 : Blo 2305435 33716519 := bstep (se 1 (by rfl) ⟨25287389, by rfl⟩ : syracuseStep 33716519 = 50574779) B50574779
theorem B22477679 : Blo 2305435 22477679 := bstep (se 1 (by rfl) ⟨16858259, by rfl⟩ : syracuseStep 22477679 = 33716519) B33716519
theorem B14985119 : Blo 2305435 14985119 := bstep (se 1 (by rfl) ⟨11238839, by rfl⟩ : syracuseStep 14985119 = 22477679) B22477679
theorem B39960317 : Blo 2305435 39960317 := bstep (se 3 (by rfl) ⟨7492559, by rfl⟩ : syracuseStep 39960317 = 14985119) B14985119
theorem B106560845 : Blo 2305435 106560845 := bstep (se 3 (by rfl) ⟨19980158, by rfl⟩ : syracuseStep 106560845 = 39960317) B39960317
theorem B71040563 : Blo 2305435 71040563 := bstep (se 1 (by rfl) ⟨53280422, by rfl⟩ : syracuseStep 71040563 = 106560845) B106560845
theorem B47360375 : Blo 2305435 47360375 := bstep (se 1 (by rfl) ⟨35520281, by rfl⟩ : syracuseStep 47360375 = 71040563) B71040563
theorem B31573583 : Blo 2305435 31573583 := bstep (se 1 (by rfl) ⟨23680187, by rfl⟩ : syracuseStep 31573583 = 47360375) B47360375
theorem B21049055 : Blo 2305435 21049055 := bstep (se 1 (by rfl) ⟨15786791, by rfl⟩ : syracuseStep 21049055 = 31573583) B31573583
theorem B14032703 : Blo 2305435 14032703 := bstep (se 1 (by rfl) ⟨10524527, by rfl⟩ : syracuseStep 14032703 = 21049055) B21049055
theorem B37420541 : Blo 2305435 37420541 := bstep (se 3 (by rfl) ⟨7016351, by rfl⟩ : syracuseStep 37420541 = 14032703) B14032703
theorem B24947027 : Blo 2305435 24947027 := bstep (se 1 (by rfl) ⟨18710270, by rfl⟩ : syracuseStep 24947027 = 37420541) B37420541
theorem B16631351 : Blo 2305435 16631351 := bstep (se 1 (by rfl) ⟨12473513, by rfl⟩ : syracuseStep 16631351 = 24947027) B24947027
theorem B11087567 : Blo 2305435 11087567 := bstep (se 1 (by rfl) ⟨8315675, by rfl⟩ : syracuseStep 11087567 = 16631351) B16631351
theorem B7391711 : Blo 2305435 7391711 := bstep (se 1 (by rfl) ⟨5543783, by rfl⟩ : syracuseStep 7391711 = 11087567) B11087567
theorem B4927807 : Blo 2305435 4927807 := bstep (se 1 (by rfl) ⟨3695855, by rfl⟩ : syracuseStep 4927807 = 7391711) B7391711
theorem B6570409 : Blo 2305435 6570409 := bstep (se 2 (by rfl) ⟨2463903, by rfl⟩ : syracuseStep 6570409 = 4927807) B4927807
theorem B8760545 : Blo 2305435 8760545 := bstep (se 2 (by rfl) ⟨3285204, by rfl⟩ : syracuseStep 8760545 = 6570409) B6570409
theorem B5840363 : Blo 2305435 5840363 := bstep (se 1 (by rfl) ⟨4380272, by rfl⟩ : syracuseStep 5840363 = 8760545) B8760545
theorem B3893575 : Blo 2305435 3893575 := bstep (se 1 (by rfl) ⟨2920181, by rfl⟩ : syracuseStep 3893575 = 5840363) B5840363
theorem B5191433 : Blo 2305435 5191433 := bstep (se 2 (by rfl) ⟨1946787, by rfl⟩ : syracuseStep 5191433 = 3893575) B3893575
theorem B3460955 : Blo 2305435 3460955 := bstep (se 1 (by rfl) ⟨2595716, by rfl⟩ : syracuseStep 3460955 = 5191433) B5191433
theorem B2307303 : Blo 2305435 2307303 := bstep (se 1 (by rfl) ⟨1730477, by rfl⟩ : syracuseStep 2307303 = 3460955) B3460955
theorem B2595721 : Blo 2305435 2595721 := bbase (se 2 (by rfl) ⟨973395, by rfl⟩ : syracuseStep 2595721 = 1946791) (by norm_num)
theorem B3460961 : Blo 2305435 3460961 := bstep (se 2 (by rfl) ⟨1297860, by rfl⟩ : syracuseStep 3460961 = 2595721) B2595721
theorem B2307307 : Blo 2305435 2307307 := bstep (se 1 (by rfl) ⟨1730480, by rfl⟩ : syracuseStep 2307307 = 3460961) B3460961
theorem B2960033 : Blo 2305435 2960033 := bbase (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) (by norm_num)
theorem B31573685 : Blo 2305435 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B84196493 : Blo 2305435 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B56130995 : Blo 2305435 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B149682653 : Blo 2305435 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B99788435 : Blo 2305435 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B66525623 : Blo 2305435 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B44350415 : Blo 2305435 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B29566943 : Blo 2305435 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B19711295 : Blo 2305435 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B13140863 : Blo 2305435 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B8760575 : Blo 2305435 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B5840383 : Blo 2305435 5840383 := bstep (se 1 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 5840383 = 8760575) B8760575
theorem B7787177 : Blo 2305435 7787177 := bstep (se 2 (by rfl) ⟨2920191, by rfl⟩ : syracuseStep 7787177 = 5840383) B5840383
theorem B5191451 : Blo 2305435 5191451 := bstep (se 1 (by rfl) ⟨3893588, by rfl⟩ : syracuseStep 5191451 = 7787177) B7787177
theorem B3460967 : Blo 2305435 3460967 := bstep (se 1 (by rfl) ⟨2595725, by rfl⟩ : syracuseStep 3460967 = 5191451) B5191451
theorem B2307311 : Blo 2305435 2307311 := bstep (se 1 (by rfl) ⟨1730483, by rfl⟩ : syracuseStep 2307311 = 3460967) B3460967
theorem B3460973 : Blo 2305435 3460973 := bbase (se 3 (by rfl) ⟨648932, by rfl⟩ : syracuseStep 3460973 = 1297865) (by norm_num)
theorem B2307315 : Blo 2305435 2307315 := bstep (se 1 (by rfl) ⟨1730486, by rfl⟩ : syracuseStep 2307315 = 3460973) B3460973
theorem B5191469 : Blo 2305435 5191469 := bbase (se 3 (by rfl) ⟨973400, by rfl⟩ : syracuseStep 5191469 = 1946801) (by norm_num)
theorem B3460979 : Blo 2305435 3460979 := bstep (se 1 (by rfl) ⟨2595734, by rfl⟩ : syracuseStep 3460979 = 5191469) B5191469
theorem B2307319 : Blo 2305435 2307319 := bstep (se 1 (by rfl) ⟨1730489, by rfl⟩ : syracuseStep 2307319 = 3460979) B3460979
theorem B9855701 : Blo 2305435 9855701 := bbase (se 7 (by rfl) ⟨115496, by rfl⟩ : syracuseStep 9855701 = 230993) (by norm_num)
theorem B6570467 : Blo 2305435 6570467 := bstep (se 1 (by rfl) ⟨4927850, by rfl⟩ : syracuseStep 6570467 = 9855701) B9855701
theorem B4380311 : Blo 2305435 4380311 := bstep (se 1 (by rfl) ⟨3285233, by rfl⟩ : syracuseStep 4380311 = 6570467) B6570467
theorem B2920207 : Blo 2305435 2920207 := bstep (se 1 (by rfl) ⟨2190155, by rfl⟩ : syracuseStep 2920207 = 4380311) B4380311
theorem B3893609 : Blo 2305435 3893609 := bstep (se 2 (by rfl) ⟨1460103, by rfl⟩ : syracuseStep 3893609 = 2920207) B2920207
theorem B2595739 : Blo 2305435 2595739 := bstep (se 1 (by rfl) ⟨1946804, by rfl⟩ : syracuseStep 2595739 = 3893609) B3893609
theorem B3460985 : Blo 2305435 3460985 := bstep (se 2 (by rfl) ⟨1297869, by rfl⟩ : syracuseStep 3460985 = 2595739) B2595739
theorem B2307323 : Blo 2305435 2307323 := bstep (se 1 (by rfl) ⟨1730492, by rfl⟩ : syracuseStep 2307323 = 3460985) B3460985
theorem B14783573 : Blo 2305435 14783573 := bbase (se 8 (by rfl) ⟨86622, by rfl⟩ : syracuseStep 14783573 = 173245) (by norm_num)
theorem B39422861 : Blo 2305435 39422861 := bstep (se 3 (by rfl) ⟨7391786, by rfl⟩ : syracuseStep 39422861 = 14783573) B14783573
theorem B26281907 : Blo 2305435 26281907 := bstep (se 1 (by rfl) ⟨19711430, by rfl⟩ : syracuseStep 26281907 = 39422861) B39422861
theorem B17521271 : Blo 2305435 17521271 := bstep (se 1 (by rfl) ⟨13140953, by rfl⟩ : syracuseStep 17521271 = 26281907) B26281907
theorem B11680847 : Blo 2305435 11680847 := bstep (se 1 (by rfl) ⟨8760635, by rfl⟩ : syracuseStep 11680847 = 17521271) B17521271
theorem B7787231 : Blo 2305435 7787231 := bstep (se 1 (by rfl) ⟨5840423, by rfl⟩ : syracuseStep 7787231 = 11680847) B11680847
theorem B5191487 : Blo 2305435 5191487 := bstep (se 1 (by rfl) ⟨3893615, by rfl⟩ : syracuseStep 5191487 = 7787231) B7787231
theorem B3460991 : Blo 2305435 3460991 := bstep (se 1 (by rfl) ⟨2595743, by rfl⟩ : syracuseStep 3460991 = 5191487) B5191487
theorem B2307327 : Blo 2305435 2307327 := bstep (se 1 (by rfl) ⟨1730495, by rfl⟩ : syracuseStep 2307327 = 3460991) B3460991
theorem B3460997 : Blo 2305435 3460997 := bbase (se 4 (by rfl) ⟨324468, by rfl⟩ : syracuseStep 3460997 = 648937) (by norm_num)
theorem B2307331 : Blo 2305435 2307331 := bstep (se 1 (by rfl) ⟨1730498, by rfl⟩ : syracuseStep 2307331 = 3460997) B3460997
theorem B3893629 : Blo 2305435 3893629 := bbase (se 3 (by rfl) ⟨730055, by rfl⟩ : syracuseStep 3893629 = 1460111) (by norm_num)
theorem B5191505 : Blo 2305435 5191505 := bstep (se 2 (by rfl) ⟨1946814, by rfl⟩ : syracuseStep 5191505 = 3893629) B3893629
theorem B3461003 : Blo 2305435 3461003 := bstep (se 1 (by rfl) ⟨2595752, by rfl⟩ : syracuseStep 3461003 = 5191505) B5191505
theorem B2307335 : Blo 2305435 2307335 := bstep (se 1 (by rfl) ⟨1730501, by rfl⟩ : syracuseStep 2307335 = 3461003) B3461003
theorem B2595757 : Blo 2305435 2595757 := bbase (se 3 (by rfl) ⟨486704, by rfl⟩ : syracuseStep 2595757 = 973409) (by norm_num)
theorem B3461009 : Blo 2305435 3461009 := bstep (se 2 (by rfl) ⟨1297878, by rfl⟩ : syracuseStep 3461009 = 2595757) B2595757
theorem B2307339 : Blo 2305435 2307339 := bstep (se 1 (by rfl) ⟨1730504, by rfl⟩ : syracuseStep 2307339 = 3461009) B3461009
theorem B7787285 : Blo 2305435 7787285 := bbase (se 6 (by rfl) ⟨182514, by rfl⟩ : syracuseStep 7787285 = 365029) (by norm_num)
theorem B5191523 : Blo 2305435 5191523 := bstep (se 1 (by rfl) ⟨3893642, by rfl⟩ : syracuseStep 5191523 = 7787285) B7787285
theorem B3461015 : Blo 2305435 3461015 := bstep (se 1 (by rfl) ⟨2595761, by rfl⟩ : syracuseStep 3461015 = 5191523) B5191523
theorem B2307343 : Blo 2305435 2307343 := bstep (se 1 (by rfl) ⟨1730507, by rfl⟩ : syracuseStep 2307343 = 3461015) B3461015
theorem B3461021 : Blo 2305435 3461021 := bbase (se 3 (by rfl) ⟨648941, by rfl⟩ : syracuseStep 3461021 = 1297883) (by norm_num)
theorem B2307347 : Blo 2305435 2307347 := bstep (se 1 (by rfl) ⟨1730510, by rfl⟩ : syracuseStep 2307347 = 3461021) B3461021
theorem B5191541 : Blo 2305435 5191541 := bbase (se 5 (by rfl) ⟨243353, by rfl⟩ : syracuseStep 5191541 = 486707) (by norm_num)
theorem B3461027 : Blo 2305435 3461027 := bstep (se 1 (by rfl) ⟨2595770, by rfl⟩ : syracuseStep 3461027 = 5191541) B5191541
theorem B2307351 : Blo 2305435 2307351 := bstep (se 1 (by rfl) ⟨1730513, by rfl⟩ : syracuseStep 2307351 = 3461027) B3461027
theorem B14985461 : Blo 2305435 14985461 := bbase (se 5 (by rfl) ⟨702443, by rfl⟩ : syracuseStep 14985461 = 1404887) (by norm_num)
theorem B9990307 : Blo 2305435 9990307 := bstep (se 1 (by rfl) ⟨7492730, by rfl⟩ : syracuseStep 9990307 = 14985461) B14985461
theorem B13320409 : Blo 2305435 13320409 := bstep (se 2 (by rfl) ⟨4995153, by rfl⟩ : syracuseStep 13320409 = 9990307) B9990307
theorem B17760545 : Blo 2305435 17760545 := bstep (se 2 (by rfl) ⟨6660204, by rfl⟩ : syracuseStep 17760545 = 13320409) B13320409
theorem B11840363 : Blo 2305435 11840363 := bstep (se 1 (by rfl) ⟨8880272, by rfl⟩ : syracuseStep 11840363 = 17760545) B17760545
theorem B7893575 : Blo 2305435 7893575 := bstep (se 1 (by rfl) ⟨5920181, by rfl⟩ : syracuseStep 7893575 = 11840363) B11840363
theorem B5262383 : Blo 2305435 5262383 := bstep (se 1 (by rfl) ⟨3946787, by rfl⟩ : syracuseStep 5262383 = 7893575) B7893575
theorem B3508255 : Blo 2305435 3508255 := bstep (se 1 (by rfl) ⟨2631191, by rfl⟩ : syracuseStep 3508255 = 5262383) B5262383
theorem B4677673 : Blo 2305435 4677673 := bstep (se 2 (by rfl) ⟨1754127, by rfl⟩ : syracuseStep 4677673 = 3508255) B3508255
theorem B6236897 : Blo 2305435 6236897 := bstep (se 2 (by rfl) ⟨2338836, by rfl⟩ : syracuseStep 6236897 = 4677673) B4677673
theorem B16631725 : Blo 2305435 16631725 := bstep (se 3 (by rfl) ⟨3118448, by rfl⟩ : syracuseStep 16631725 = 6236897) B6236897
theorem B22175633 : Blo 2305435 22175633 := bstep (se 2 (by rfl) ⟨8315862, by rfl⟩ : syracuseStep 22175633 = 16631725) B16631725
theorem B14783755 : Blo 2305435 14783755 := bstep (se 1 (by rfl) ⟨11087816, by rfl⟩ : syracuseStep 14783755 = 22175633) B22175633
theorem B19711673 : Blo 2305435 19711673 := bstep (se 2 (by rfl) ⟨7391877, by rfl⟩ : syracuseStep 19711673 = 14783755) B14783755
theorem B13141115 : Blo 2305435 13141115 := bstep (se 1 (by rfl) ⟨9855836, by rfl⟩ : syracuseStep 13141115 = 19711673) B19711673
theorem B8760743 : Blo 2305435 8760743 := bstep (se 1 (by rfl) ⟨6570557, by rfl⟩ : syracuseStep 8760743 = 13141115) B13141115
theorem B5840495 : Blo 2305435 5840495 := bstep (se 1 (by rfl) ⟨4380371, by rfl⟩ : syracuseStep 5840495 = 8760743) B8760743
theorem B3893663 : Blo 2305435 3893663 := bstep (se 1 (by rfl) ⟨2920247, by rfl⟩ : syracuseStep 3893663 = 5840495) B5840495
theorem B2595775 : Blo 2305435 2595775 := bstep (se 1 (by rfl) ⟨1946831, by rfl⟩ : syracuseStep 2595775 = 3893663) B3893663
theorem B3461033 : Blo 2305435 3461033 := bstep (se 2 (by rfl) ⟨1297887, by rfl⟩ : syracuseStep 3461033 = 2595775) B2595775
theorem B2307355 : Blo 2305435 2307355 := bstep (se 1 (by rfl) ⟨1730516, by rfl⟩ : syracuseStep 2307355 = 3461033) B3461033
theorem B8760757 : Blo 2305435 8760757 := bbase (se 5 (by rfl) ⟨410660, by rfl⟩ : syracuseStep 8760757 = 821321) (by norm_num)
theorem B11681009 : Blo 2305435 11681009 := bstep (se 2 (by rfl) ⟨4380378, by rfl⟩ : syracuseStep 11681009 = 8760757) B8760757
theorem B7787339 : Blo 2305435 7787339 := bstep (se 1 (by rfl) ⟨5840504, by rfl⟩ : syracuseStep 7787339 = 11681009) B11681009
theorem B5191559 : Blo 2305435 5191559 := bstep (se 1 (by rfl) ⟨3893669, by rfl⟩ : syracuseStep 5191559 = 7787339) B7787339
theorem B3461039 : Blo 2305435 3461039 := bstep (se 1 (by rfl) ⟨2595779, by rfl⟩ : syracuseStep 3461039 = 5191559) B5191559
theorem B2307359 : Blo 2305435 2307359 := bstep (se 1 (by rfl) ⟨1730519, by rfl⟩ : syracuseStep 2307359 = 3461039) B3461039
theorem B3461045 : Blo 2305435 3461045 := bbase (se 5 (by rfl) ⟨162236, by rfl⟩ : syracuseStep 3461045 = 324473) (by norm_num)
theorem B2307363 : Blo 2305435 2307363 := bstep (se 1 (by rfl) ⟨1730522, by rfl⟩ : syracuseStep 2307363 = 3461045) B3461045
theorem B5840525 : Blo 2305435 5840525 := bbase (se 3 (by rfl) ⟨1095098, by rfl⟩ : syracuseStep 5840525 = 2190197) (by norm_num)
theorem B3893683 : Blo 2305435 3893683 := bstep (se 1 (by rfl) ⟨2920262, by rfl⟩ : syracuseStep 3893683 = 5840525) B5840525
theorem B5191577 : Blo 2305435 5191577 := bstep (se 2 (by rfl) ⟨1946841, by rfl⟩ : syracuseStep 5191577 = 3893683) B3893683
theorem B3461051 : Blo 2305435 3461051 := bstep (se 1 (by rfl) ⟨2595788, by rfl⟩ : syracuseStep 3461051 = 5191577) B5191577
theorem B2307367 : Blo 2305435 2307367 := bstep (se 1 (by rfl) ⟨1730525, by rfl⟩ : syracuseStep 2307367 = 3461051) B3461051
theorem B2595793 : Blo 2305435 2595793 := bbase (se 2 (by rfl) ⟨973422, by rfl⟩ : syracuseStep 2595793 = 1946845) (by norm_num)
theorem B3461057 : Blo 2305435 3461057 := bstep (se 2 (by rfl) ⟨1297896, by rfl⟩ : syracuseStep 3461057 = 2595793) B2595793
theorem B2307371 : Blo 2305435 2307371 := bstep (se 1 (by rfl) ⟨1730528, by rfl⟩ : syracuseStep 2307371 = 3461057) B3461057
theorem B5543957 : Blo 2305435 5543957 := bbase (se 6 (by rfl) ⟨129936, by rfl⟩ : syracuseStep 5543957 = 259873) (by norm_num)
theorem B3695971 : Blo 2305435 3695971 := bstep (se 1 (by rfl) ⟨2771978, by rfl⟩ : syracuseStep 3695971 = 5543957) B5543957
theorem B4927961 : Blo 2305435 4927961 := bstep (se 2 (by rfl) ⟨1847985, by rfl⟩ : syracuseStep 4927961 = 3695971) B3695971
theorem B3285307 : Blo 2305435 3285307 := bstep (se 1 (by rfl) ⟨2463980, by rfl⟩ : syracuseStep 3285307 = 4927961) B4927961
theorem B4380409 : Blo 2305435 4380409 := bstep (se 2 (by rfl) ⟨1642653, by rfl⟩ : syracuseStep 4380409 = 3285307) B3285307
theorem B5840545 : Blo 2305435 5840545 := bstep (se 2 (by rfl) ⟨2190204, by rfl⟩ : syracuseStep 5840545 = 4380409) B4380409
theorem B7787393 : Blo 2305435 7787393 := bstep (se 2 (by rfl) ⟨2920272, by rfl⟩ : syracuseStep 7787393 = 5840545) B5840545
theorem B5191595 : Blo 2305435 5191595 := bstep (se 1 (by rfl) ⟨3893696, by rfl⟩ : syracuseStep 5191595 = 7787393) B7787393
theorem B3461063 : Blo 2305435 3461063 := bstep (se 1 (by rfl) ⟨2595797, by rfl⟩ : syracuseStep 3461063 = 5191595) B5191595
theorem B2307375 : Blo 2305435 2307375 := bstep (se 1 (by rfl) ⟨1730531, by rfl⟩ : syracuseStep 2307375 = 3461063) B3461063
theorem B3461069 : Blo 2305435 3461069 := bbase (se 3 (by rfl) ⟨648950, by rfl⟩ : syracuseStep 3461069 = 1297901) (by norm_num)
theorem B2307379 : Blo 2305435 2307379 := bstep (se 1 (by rfl) ⟨1730534, by rfl⟩ : syracuseStep 2307379 = 3461069) B3461069
theorem B5191613 : Blo 2305435 5191613 := bbase (se 3 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 5191613 = 1946855) (by norm_num)
theorem B3461075 : Blo 2305435 3461075 := bstep (se 1 (by rfl) ⟨2595806, by rfl⟩ : syracuseStep 3461075 = 5191613) B5191613
theorem B2307383 : Blo 2305435 2307383 := bstep (se 1 (by rfl) ⟨1730537, by rfl⟩ : syracuseStep 2307383 = 3461075) B3461075
theorem B3893717 : Blo 2305435 3893717 := bbase (se 7 (by rfl) ⟨45629, by rfl⟩ : syracuseStep 3893717 = 91259) (by norm_num)
theorem B2595811 : Blo 2305435 2595811 := bstep (se 1 (by rfl) ⟨1946858, by rfl⟩ : syracuseStep 2595811 = 3893717) B3893717
theorem B3461081 : Blo 2305435 3461081 := bstep (se 2 (by rfl) ⟨1297905, by rfl⟩ : syracuseStep 3461081 = 2595811) B2595811
theorem B2307387 : Blo 2305435 2307387 := bstep (se 1 (by rfl) ⟨1730540, by rfl⟩ : syracuseStep 2307387 = 3461081) B3461081
theorem B9855989 : Blo 2305435 9855989 := bbase (se 5 (by rfl) ⟨461999, by rfl⟩ : syracuseStep 9855989 = 923999) (by norm_num)
theorem B6570659 : Blo 2305435 6570659 := bstep (se 1 (by rfl) ⟨4927994, by rfl⟩ : syracuseStep 6570659 = 9855989) B9855989
theorem B17521757 : Blo 2305435 17521757 := bstep (se 3 (by rfl) ⟨3285329, by rfl⟩ : syracuseStep 17521757 = 6570659) B6570659
theorem B11681171 : Blo 2305435 11681171 := bstep (se 1 (by rfl) ⟨8760878, by rfl⟩ : syracuseStep 11681171 = 17521757) B17521757
theorem B7787447 : Blo 2305435 7787447 := bstep (se 1 (by rfl) ⟨5840585, by rfl⟩ : syracuseStep 7787447 = 11681171) B11681171
theorem B5191631 : Blo 2305435 5191631 := bstep (se 1 (by rfl) ⟨3893723, by rfl⟩ : syracuseStep 5191631 = 7787447) B7787447
theorem B3461087 : Blo 2305435 3461087 := bstep (se 1 (by rfl) ⟨2595815, by rfl⟩ : syracuseStep 3461087 = 5191631) B5191631
theorem B2307391 : Blo 2305435 2307391 := bstep (se 1 (by rfl) ⟨1730543, by rfl⟩ : syracuseStep 2307391 = 3461087) B3461087
theorem B3461093 : Blo 2305435 3461093 := bbase (se 4 (by rfl) ⟨324477, by rfl⟩ : syracuseStep 3461093 = 648955) (by norm_num)
theorem B2307395 : Blo 2305435 2307395 := bstep (se 1 (by rfl) ⟨1730546, by rfl⟩ : syracuseStep 2307395 = 3461093) B3461093
theorem B7016645 : Blo 2305435 7016645 := bbase (se 4 (by rfl) ⟨657810, by rfl⟩ : syracuseStep 7016645 = 1315621) (by norm_num)
theorem B4677763 : Blo 2305435 4677763 := bstep (se 1 (by rfl) ⟨3508322, by rfl⟩ : syracuseStep 4677763 = 7016645) B7016645
theorem B6237017 : Blo 2305435 6237017 := bstep (se 2 (by rfl) ⟨2338881, by rfl⟩ : syracuseStep 6237017 = 4677763) B4677763
theorem B4158011 : Blo 2305435 4158011 := bstep (se 1 (by rfl) ⟨3118508, by rfl⟩ : syracuseStep 4158011 = 6237017) B6237017
theorem B11088029 : Blo 2305435 11088029 := bstep (se 3 (by rfl) ⟨2079005, by rfl⟩ : syracuseStep 11088029 = 4158011) B4158011
theorem B7392019 : Blo 2305435 7392019 := bstep (se 1 (by rfl) ⟨5544014, by rfl⟩ : syracuseStep 7392019 = 11088029) B11088029
theorem B9856025 : Blo 2305435 9856025 := bstep (se 2 (by rfl) ⟨3696009, by rfl⟩ : syracuseStep 9856025 = 7392019) B7392019
theorem B6570683 : Blo 2305435 6570683 := bstep (se 1 (by rfl) ⟨4928012, by rfl⟩ : syracuseStep 6570683 = 9856025) B9856025
theorem B4380455 : Blo 2305435 4380455 := bstep (se 1 (by rfl) ⟨3285341, by rfl⟩ : syracuseStep 4380455 = 6570683) B6570683
theorem B2920303 : Blo 2305435 2920303 := bstep (se 1 (by rfl) ⟨2190227, by rfl⟩ : syracuseStep 2920303 = 4380455) B4380455
theorem B3893737 : Blo 2305435 3893737 := bstep (se 2 (by rfl) ⟨1460151, by rfl⟩ : syracuseStep 3893737 = 2920303) B2920303
theorem B5191649 : Blo 2305435 5191649 := bstep (se 2 (by rfl) ⟨1946868, by rfl⟩ : syracuseStep 5191649 = 3893737) B3893737
theorem B3461099 : Blo 2305435 3461099 := bstep (se 1 (by rfl) ⟨2595824, by rfl⟩ : syracuseStep 3461099 = 5191649) B5191649
theorem B2307399 : Blo 2305435 2307399 := bstep (se 1 (by rfl) ⟨1730549, by rfl⟩ : syracuseStep 2307399 = 3461099) B3461099
theorem B2595829 : Blo 2305435 2595829 := bbase (se 5 (by rfl) ⟨121679, by rfl⟩ : syracuseStep 2595829 = 243359) (by norm_num)
theorem B3461105 : Blo 2305435 3461105 := bstep (se 2 (by rfl) ⟨1297914, by rfl⟩ : syracuseStep 3461105 = 2595829) B2595829
theorem B2307403 : Blo 2305435 2307403 := bstep (se 1 (by rfl) ⟨1730552, by rfl⟩ : syracuseStep 2307403 = 3461105) B3461105
theorem B2920313 : Blo 2305435 2920313 := bbase (se 2 (by rfl) ⟨1095117, by rfl⟩ : syracuseStep 2920313 = 2190235) (by norm_num)
theorem B7787501 : Blo 2305435 7787501 := bstep (se 3 (by rfl) ⟨1460156, by rfl⟩ : syracuseStep 7787501 = 2920313) B2920313
theorem B5191667 : Blo 2305435 5191667 := bstep (se 1 (by rfl) ⟨3893750, by rfl⟩ : syracuseStep 5191667 = 7787501) B7787501
theorem B3461111 : Blo 2305435 3461111 := bstep (se 1 (by rfl) ⟨2595833, by rfl⟩ : syracuseStep 3461111 = 5191667) B5191667
theorem B2307407 : Blo 2305435 2307407 := bstep (se 1 (by rfl) ⟨1730555, by rfl⟩ : syracuseStep 2307407 = 3461111) B3461111
theorem B3461117 : Blo 2305435 3461117 := bbase (se 3 (by rfl) ⟨648959, by rfl⟩ : syracuseStep 3461117 = 1297919) (by norm_num)
theorem B2307411 : Blo 2305435 2307411 := bstep (se 1 (by rfl) ⟨1730558, by rfl⟩ : syracuseStep 2307411 = 3461117) B3461117
theorem B5191685 : Blo 2305435 5191685 := bbase (se 4 (by rfl) ⟨486720, by rfl⟩ : syracuseStep 5191685 = 973441) (by norm_num)
theorem B3461123 : Blo 2305435 3461123 := bstep (se 1 (by rfl) ⟨2595842, by rfl⟩ : syracuseStep 3461123 = 5191685) B5191685
theorem B2307415 : Blo 2305435 2307415 := bstep (se 1 (by rfl) ⟨1730561, by rfl⟩ : syracuseStep 2307415 = 3461123) B3461123
theorem B4380493 : Blo 2305435 4380493 := bbase (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) (by norm_num)
theorem B5840657 : Blo 2305435 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B3893771 : Blo 2305435 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B2595847 : Blo 2305435 2595847 := bstep (se 1 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 2595847 = 3893771) B3893771
theorem B3461129 : Blo 2305435 3461129 := bstep (se 2 (by rfl) ⟨1297923, by rfl⟩ : syracuseStep 3461129 = 2595847) B2595847
theorem B2307419 : Blo 2305435 2307419 := bstep (se 1 (by rfl) ⟨1730564, by rfl⟩ : syracuseStep 2307419 = 3461129) B3461129
theorem B11681333 : Blo 2305435 11681333 := bbase (se 5 (by rfl) ⟨547562, by rfl⟩ : syracuseStep 11681333 = 1095125) (by norm_num)
theorem B7787555 : Blo 2305435 7787555 := bstep (se 1 (by rfl) ⟨5840666, by rfl⟩ : syracuseStep 7787555 = 11681333) B11681333
theorem B5191703 : Blo 2305435 5191703 := bstep (se 1 (by rfl) ⟨3893777, by rfl⟩ : syracuseStep 5191703 = 7787555) B7787555
theorem B3461135 : Blo 2305435 3461135 := bstep (se 1 (by rfl) ⟨2595851, by rfl⟩ : syracuseStep 3461135 = 5191703) B5191703
theorem B2307423 : Blo 2305435 2307423 := bstep (se 1 (by rfl) ⟨1730567, by rfl⟩ : syracuseStep 2307423 = 3461135) B3461135
theorem B3461141 : Blo 2305435 3461141 := bbase (se 6 (by rfl) ⟨81120, by rfl⟩ : syracuseStep 3461141 = 162241) (by norm_num)
theorem B2307427 : Blo 2305435 2307427 := bstep (se 1 (by rfl) ⟨1730570, by rfl⟩ : syracuseStep 2307427 = 3461141) B3461141
theorem B11088181 : Blo 2305435 11088181 := bbase (se 5 (by rfl) ⟨519758, by rfl⟩ : syracuseStep 11088181 = 1039517) (by norm_num)
theorem B14784241 : Blo 2305435 14784241 := bstep (se 2 (by rfl) ⟨5544090, by rfl⟩ : syracuseStep 14784241 = 11088181) B11088181
theorem B19712321 : Blo 2305435 19712321 := bstep (se 2 (by rfl) ⟨7392120, by rfl⟩ : syracuseStep 19712321 = 14784241) B14784241
theorem B13141547 : Blo 2305435 13141547 := bstep (se 1 (by rfl) ⟨9856160, by rfl⟩ : syracuseStep 13141547 = 19712321) B19712321
theorem B8761031 : Blo 2305435 8761031 := bstep (se 1 (by rfl) ⟨6570773, by rfl⟩ : syracuseStep 8761031 = 13141547) B13141547
theorem B5840687 : Blo 2305435 5840687 := bstep (se 1 (by rfl) ⟨4380515, by rfl⟩ : syracuseStep 5840687 = 8761031) B8761031
theorem B3893791 : Blo 2305435 3893791 := bstep (se 1 (by rfl) ⟨2920343, by rfl⟩ : syracuseStep 3893791 = 5840687) B5840687
theorem B5191721 : Blo 2305435 5191721 := bstep (se 2 (by rfl) ⟨1946895, by rfl⟩ : syracuseStep 5191721 = 3893791) B3893791
theorem B3461147 : Blo 2305435 3461147 := bstep (se 1 (by rfl) ⟨2595860, by rfl⟩ : syracuseStep 3461147 = 5191721) B5191721
theorem B2307431 : Blo 2305435 2307431 := bstep (se 1 (by rfl) ⟨1730573, by rfl⟩ : syracuseStep 2307431 = 3461147) B3461147
theorem B2595865 : Blo 2305435 2595865 := bbase (se 2 (by rfl) ⟨973449, by rfl⟩ : syracuseStep 2595865 = 1946899) (by norm_num)
theorem B3461153 : Blo 2305435 3461153 := bstep (se 2 (by rfl) ⟨1297932, by rfl⟩ : syracuseStep 3461153 = 2595865) B2595865
theorem B2307435 : Blo 2305435 2307435 := bstep (se 1 (by rfl) ⟨1730576, by rfl⟩ : syracuseStep 2307435 = 3461153) B3461153
theorem C0 (j : ℕ) (h1 : 576358 ≤ j) (h2 : j ≤ 576858) : Blo 2305435 (4 * j + 3) := by
  interval_cases j
  · exact B2305435
  · exact B2305439
  · exact B2305443
  · exact B2305447
  · exact B2305451
  · exact B2305455
  · exact B2305459
  · exact B2305463
  · exact B2305467
  · exact B2305471
  · exact B2305475
  · exact B2305479
  · exact B2305483
  · exact B2305487
  · exact B2305491
  · exact B2305495
  · exact B2305499
  · exact B2305503
  · exact B2305507
  · exact B2305511
  · exact B2305515
  · exact B2305519
  · exact B2305523
  · exact B2305527
  · exact B2305531
  · exact B2305535
  · exact B2305539
  · exact B2305543
  · exact B2305547
  · exact B2305551
  · exact B2305555
  · exact B2305559
  · exact B2305563
  · exact B2305567
  · exact B2305571
  · exact B2305575
  · exact B2305579
  · exact B2305583
  · exact B2305587
  · exact B2305591
  · exact B2305595
  · exact B2305599
  · exact B2305603
  · exact B2305607
  · exact B2305611
  · exact B2305615
  · exact B2305619
  · exact B2305623
  · exact B2305627
  · exact B2305631
  · exact B2305635
  · exact B2305639
  · exact B2305643
  · exact B2305647
  · exact B2305651
  · exact B2305655
  · exact B2305659
  · exact B2305663
  · exact B2305667
  · exact B2305671
  · exact B2305675
  · exact B2305679
  · exact B2305683
  · exact B2305687
  · exact B2305691
  · exact B2305695
  · exact B2305699
  · exact B2305703
  · exact B2305707
  · exact B2305711
  · exact B2305715
  · exact B2305719
  · exact B2305723
  · exact B2305727
  · exact B2305731
  · exact B2305735
  · exact B2305739
  · exact B2305743
  · exact B2305747
  · exact B2305751
  · exact B2305755
  · exact B2305759
  · exact B2305763
  · exact B2305767
  · exact B2305771
  · exact B2305775
  · exact B2305779
  · exact B2305783
  · exact B2305787
  · exact B2305791
  · exact B2305795
  · exact B2305799
  · exact B2305803
  · exact B2305807
  · exact B2305811
  · exact B2305815
  · exact B2305819
  · exact B2305823
  · exact B2305827
  · exact B2305831
  · exact B2305835
  · exact B2305839
  · exact B2305843
  · exact B2305847
  · exact B2305851
  · exact B2305855
  · exact B2305859
  · exact B2305863
  · exact B2305867
  · exact B2305871
  · exact B2305875
  · exact B2305879
  · exact B2305883
  · exact B2305887
  · exact B2305891
  · exact B2305895
  · exact B2305899
  · exact B2305903
  · exact B2305907
  · exact B2305911
  · exact B2305915
  · exact B2305919
  · exact B2305923
  · exact B2305927
  · exact B2305931
  · exact B2305935
  · exact B2305939
  · exact B2305943
  · exact B2305947
  · exact B2305951
  · exact B2305955
  · exact B2305959
  · exact B2305963
  · exact B2305967
  · exact B2305971
  · exact B2305975
  · exact B2305979
  · exact B2305983
  · exact B2305987
  · exact B2305991
  · exact B2305995
  · exact B2305999
  · exact B2306003
  · exact B2306007
  · exact B2306011
  · exact B2306015
  · exact B2306019
  · exact B2306023
  · exact B2306027
  · exact B2306031
  · exact B2306035
  · exact B2306039
  · exact B2306043
  · exact B2306047
  · exact B2306051
  · exact B2306055
  · exact B2306059
  · exact B2306063
  · exact B2306067
  · exact B2306071
  · exact B2306075
  · exact B2306079
  · exact B2306083
  · exact B2306087
  · exact B2306091
  · exact B2306095
  · exact B2306099
  · exact B2306103
  · exact B2306107
  · exact B2306111
  · exact B2306115
  · exact B2306119
  · exact B2306123
  · exact B2306127
  · exact B2306131
  · exact B2306135
  · exact B2306139
  · exact B2306143
  · exact B2306147
  · exact B2306151
  · exact B2306155
  · exact B2306159
  · exact B2306163
  · exact B2306167
  · exact B2306171
  · exact B2306175
  · exact B2306179
  · exact B2306183
  · exact B2306187
  · exact B2306191
  · exact B2306195
  · exact B2306199
  · exact B2306203
  · exact B2306207
  · exact B2306211
  · exact B2306215
  · exact B2306219
  · exact B2306223
  · exact B2306227
  · exact B2306231
  · exact B2306235
  · exact B2306239
  · exact B2306243
  · exact B2306247
  · exact B2306251
  · exact B2306255
  · exact B2306259
  · exact B2306263
  · exact B2306267
  · exact B2306271
  · exact B2306275
  · exact B2306279
  · exact B2306283
  · exact B2306287
  · exact B2306291
  · exact B2306295
  · exact B2306299
  · exact B2306303
  · exact B2306307
  · exact B2306311
  · exact B2306315
  · exact B2306319
  · exact B2306323
  · exact B2306327
  · exact B2306331
  · exact B2306335
  · exact B2306339
  · exact B2306343
  · exact B2306347
  · exact B2306351
  · exact B2306355
  · exact B2306359
  · exact B2306363
  · exact B2306367
  · exact B2306371
  · exact B2306375
  · exact B2306379
  · exact B2306383
  · exact B2306387
  · exact B2306391
  · exact B2306395
  · exact B2306399
  · exact B2306403
  · exact B2306407
  · exact B2306411
  · exact B2306415
  · exact B2306419
  · exact B2306423
  · exact B2306427
  · exact B2306431
  · exact B2306435
  · exact B2306439
  · exact B2306443
  · exact B2306447
  · exact B2306451
  · exact B2306455
  · exact B2306459
  · exact B2306463
  · exact B2306467
  · exact B2306471
  · exact B2306475
  · exact B2306479
  · exact B2306483
  · exact B2306487
  · exact B2306491
  · exact B2306495
  · exact B2306499
  · exact B2306503
  · exact B2306507
  · exact B2306511
  · exact B2306515
  · exact B2306519
  · exact B2306523
  · exact B2306527
  · exact B2306531
  · exact B2306535
  · exact B2306539
  · exact B2306543
  · exact B2306547
  · exact B2306551
  · exact B2306555
  · exact B2306559
  · exact B2306563
  · exact B2306567
  · exact B2306571
  · exact B2306575
  · exact B2306579
  · exact B2306583
  · exact B2306587
  · exact B2306591
  · exact B2306595
  · exact B2306599
  · exact B2306603
  · exact B2306607
  · exact B2306611
  · exact B2306615
  · exact B2306619
  · exact B2306623
  · exact B2306627
  · exact B2306631
  · exact B2306635
  · exact B2306639
  · exact B2306643
  · exact B2306647
  · exact B2306651
  · exact B2306655
  · exact B2306659
  · exact B2306663
  · exact B2306667
  · exact B2306671
  · exact B2306675
  · exact B2306679
  · exact B2306683
  · exact B2306687
  · exact B2306691
  · exact B2306695
  · exact B2306699
  · exact B2306703
  · exact B2306707
  · exact B2306711
  · exact B2306715
  · exact B2306719
  · exact B2306723
  · exact B2306727
  · exact B2306731
  · exact B2306735
  · exact B2306739
  · exact B2306743
  · exact B2306747
  · exact B2306751
  · exact B2306755
  · exact B2306759
  · exact B2306763
  · exact B2306767
  · exact B2306771
  · exact B2306775
  · exact B2306779
  · exact B2306783
  · exact B2306787
  · exact B2306791
  · exact B2306795
  · exact B2306799
  · exact B2306803
  · exact B2306807
  · exact B2306811
  · exact B2306815
  · exact B2306819
  · exact B2306823
  · exact B2306827
  · exact B2306831
  · exact B2306835
  · exact B2306839
  · exact B2306843
  · exact B2306847
  · exact B2306851
  · exact B2306855
  · exact B2306859
  · exact B2306863
  · exact B2306867
  · exact B2306871
  · exact B2306875
  · exact B2306879
  · exact B2306883
  · exact B2306887
  · exact B2306891
  · exact B2306895
  · exact B2306899
  · exact B2306903
  · exact B2306907
  · exact B2306911
  · exact B2306915
  · exact B2306919
  · exact B2306923
  · exact B2306927
  · exact B2306931
  · exact B2306935
  · exact B2306939
  · exact B2306943
  · exact B2306947
  · exact B2306951
  · exact B2306955
  · exact B2306959
  · exact B2306963
  · exact B2306967
  · exact B2306971
  · exact B2306975
  · exact B2306979
  · exact B2306983
  · exact B2306987
  · exact B2306991
  · exact B2306995
  · exact B2306999
  · exact B2307003
  · exact B2307007
  · exact B2307011
  · exact B2307015
  · exact B2307019
  · exact B2307023
  · exact B2307027
  · exact B2307031
  · exact B2307035
  · exact B2307039
  · exact B2307043
  · exact B2307047
  · exact B2307051
  · exact B2307055
  · exact B2307059
  · exact B2307063
  · exact B2307067
  · exact B2307071
  · exact B2307075
  · exact B2307079
  · exact B2307083
  · exact B2307087
  · exact B2307091
  · exact B2307095
  · exact B2307099
  · exact B2307103
  · exact B2307107
  · exact B2307111
  · exact B2307115
  · exact B2307119
  · exact B2307123
  · exact B2307127
  · exact B2307131
  · exact B2307135
  · exact B2307139
  · exact B2307143
  · exact B2307147
  · exact B2307151
  · exact B2307155
  · exact B2307159
  · exact B2307163
  · exact B2307167
  · exact B2307171
  · exact B2307175
  · exact B2307179
  · exact B2307183
  · exact B2307187
  · exact B2307191
  · exact B2307195
  · exact B2307199
  · exact B2307203
  · exact B2307207
  · exact B2307211
  · exact B2307215
  · exact B2307219
  · exact B2307223
  · exact B2307227
  · exact B2307231
  · exact B2307235
  · exact B2307239
  · exact B2307243
  · exact B2307247
  · exact B2307251
  · exact B2307255
  · exact B2307259
  · exact B2307263
  · exact B2307267
  · exact B2307271
  · exact B2307275
  · exact B2307279
  · exact B2307283
  · exact B2307287
  · exact B2307291
  · exact B2307295
  · exact B2307299
  · exact B2307303
  · exact B2307307
  · exact B2307311
  · exact B2307315
  · exact B2307319
  · exact B2307323
  · exact B2307327
  · exact B2307331
  · exact B2307335
  · exact B2307339
  · exact B2307343
  · exact B2307347
  · exact B2307351
  · exact B2307355
  · exact B2307359
  · exact B2307363
  · exact B2307367
  · exact B2307371
  · exact B2307375
  · exact B2307379
  · exact B2307383
  · exact B2307387
  · exact B2307391
  · exact B2307395
  · exact B2307399
  · exact B2307403
  · exact B2307407
  · exact B2307411
  · exact B2307415
  · exact B2307419
  · exact B2307423
  · exact B2307427
  · exact B2307431
  · exact B2307435
theorem solution (m : ℕ) (hlo : 2305435 ≤ m) (hhi : m ≤ 2307435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 576358 ≤ j := by omega
    have hj2 : j ≤ 576858 := by omega
    have hb : Blo 2305435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
