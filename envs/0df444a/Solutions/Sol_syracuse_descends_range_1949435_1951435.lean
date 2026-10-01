-- Prove2me | solution 1 for syracuse_descends_range_1949435_1951435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:39.907358+00:00
-- url     : https://prove2.me/submissions/47150df6-6038-4b71-9f38-badc3dbf5701

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

theorem B3122621 : Blo 1949435 3122621 := bbase (se 3 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 3122621 = 1170983) (by norm_num)
theorem B2081747 : Blo 1949435 2081747 := bstep (se 1 (by rfl) ⟨1561310, by rfl⟩ : syracuseStep 2081747 = 3122621) B3122621
theorem B5551325 : Blo 1949435 5551325 := bstep (se 3 (by rfl) ⟨1040873, by rfl⟩ : syracuseStep 5551325 = 2081747) B2081747
theorem B3700883 : Blo 1949435 3700883 := bstep (se 1 (by rfl) ⟨2775662, by rfl⟩ : syracuseStep 3700883 = 5551325) B5551325
theorem B2467255 : Blo 1949435 2467255 := bstep (se 1 (by rfl) ⟨1850441, by rfl⟩ : syracuseStep 2467255 = 3700883) B3700883
theorem B3289673 : Blo 1949435 3289673 := bstep (se 2 (by rfl) ⟨1233627, by rfl⟩ : syracuseStep 3289673 = 2467255) B2467255
theorem B2193115 : Blo 1949435 2193115 := bstep (se 1 (by rfl) ⟨1644836, by rfl⟩ : syracuseStep 2193115 = 3289673) B3289673
theorem B2924153 : Blo 1949435 2924153 := bstep (se 2 (by rfl) ⟨1096557, by rfl⟩ : syracuseStep 2924153 = 2193115) B2193115
theorem B1949435 : Blo 1949435 1949435 := bstep (se 1 (by rfl) ⟨1462076, by rfl⟩ : syracuseStep 1949435 = 2924153) B2924153
theorem B6669125 : Blo 1949435 6669125 := bbase (se 4 (by rfl) ⟨625230, by rfl⟩ : syracuseStep 6669125 = 1250461) (by norm_num)
theorem B4446083 : Blo 1949435 4446083 := bstep (se 1 (by rfl) ⟨3334562, by rfl⟩ : syracuseStep 4446083 = 6669125) B6669125
theorem B11856221 : Blo 1949435 11856221 := bstep (se 3 (by rfl) ⟨2223041, by rfl⟩ : syracuseStep 11856221 = 4446083) B4446083
theorem B7904147 : Blo 1949435 7904147 := bstep (se 1 (by rfl) ⟨5928110, by rfl⟩ : syracuseStep 7904147 = 11856221) B11856221
theorem B84310901 : Blo 1949435 84310901 := bstep (se 5 (by rfl) ⟨3952073, by rfl⟩ : syracuseStep 84310901 = 7904147) B7904147
theorem B56207267 : Blo 1949435 56207267 := bstep (se 1 (by rfl) ⟨42155450, by rfl⟩ : syracuseStep 56207267 = 84310901) B84310901
theorem B37471511 : Blo 1949435 37471511 := bstep (se 1 (by rfl) ⟨28103633, by rfl⟩ : syracuseStep 37471511 = 56207267) B56207267
theorem B24981007 : Blo 1949435 24981007 := bstep (se 1 (by rfl) ⟨18735755, by rfl⟩ : syracuseStep 24981007 = 37471511) B37471511
theorem B33308009 : Blo 1949435 33308009 := bstep (se 2 (by rfl) ⟨12490503, by rfl⟩ : syracuseStep 33308009 = 24981007) B24981007
theorem B22205339 : Blo 1949435 22205339 := bstep (se 1 (by rfl) ⟨16654004, by rfl⟩ : syracuseStep 22205339 = 33308009) B33308009
theorem B14803559 : Blo 1949435 14803559 := bstep (se 1 (by rfl) ⟨11102669, by rfl⟩ : syracuseStep 14803559 = 22205339) B22205339
theorem B9869039 : Blo 1949435 9869039 := bstep (se 1 (by rfl) ⟨7401779, by rfl⟩ : syracuseStep 9869039 = 14803559) B14803559
theorem B6579359 : Blo 1949435 6579359 := bstep (se 1 (by rfl) ⟨4934519, by rfl⟩ : syracuseStep 6579359 = 9869039) B9869039
theorem B4386239 : Blo 1949435 4386239 := bstep (se 1 (by rfl) ⟨3289679, by rfl⟩ : syracuseStep 4386239 = 6579359) B6579359
theorem B2924159 : Blo 1949435 2924159 := bstep (se 1 (by rfl) ⟨2193119, by rfl⟩ : syracuseStep 2924159 = 4386239) B4386239
theorem B1949439 : Blo 1949435 1949439 := bstep (se 1 (by rfl) ⟨1462079, by rfl⟩ : syracuseStep 1949439 = 2924159) B2924159
theorem B2924165 : Blo 1949435 2924165 := bbase (se 4 (by rfl) ⟨274140, by rfl⟩ : syracuseStep 2924165 = 548281) (by norm_num)
theorem B1949443 : Blo 1949435 1949443 := bstep (se 1 (by rfl) ⟨1462082, by rfl⟩ : syracuseStep 1949443 = 2924165) B2924165
theorem B3289693 : Blo 1949435 3289693 := bbase (se 3 (by rfl) ⟨616817, by rfl⟩ : syracuseStep 3289693 = 1233635) (by norm_num)
theorem B4386257 : Blo 1949435 4386257 := bstep (se 2 (by rfl) ⟨1644846, by rfl⟩ : syracuseStep 4386257 = 3289693) B3289693
theorem B2924171 : Blo 1949435 2924171 := bstep (se 1 (by rfl) ⟨2193128, by rfl⟩ : syracuseStep 2924171 = 4386257) B4386257
theorem B1949447 : Blo 1949435 1949447 := bstep (se 1 (by rfl) ⟨1462085, by rfl⟩ : syracuseStep 1949447 = 2924171) B2924171
theorem B2193133 : Blo 1949435 2193133 := bbase (se 3 (by rfl) ⟨411212, by rfl⟩ : syracuseStep 2193133 = 822425) (by norm_num)
theorem B2924177 : Blo 1949435 2924177 := bstep (se 2 (by rfl) ⟨1096566, by rfl⟩ : syracuseStep 2924177 = 2193133) B2193133
theorem B1949451 : Blo 1949435 1949451 := bstep (se 1 (by rfl) ⟨1462088, by rfl⟩ : syracuseStep 1949451 = 2924177) B2924177
theorem B6579413 : Blo 1949435 6579413 := bbase (se 7 (by rfl) ⟨77102, by rfl⟩ : syracuseStep 6579413 = 154205) (by norm_num)
theorem B4386275 : Blo 1949435 4386275 := bstep (se 1 (by rfl) ⟨3289706, by rfl⟩ : syracuseStep 4386275 = 6579413) B6579413
theorem B2924183 : Blo 1949435 2924183 := bstep (se 1 (by rfl) ⟨2193137, by rfl⟩ : syracuseStep 2924183 = 4386275) B4386275
theorem B1949455 : Blo 1949435 1949455 := bstep (se 1 (by rfl) ⟨1462091, by rfl⟩ : syracuseStep 1949455 = 2924183) B2924183
theorem B2924189 : Blo 1949435 2924189 := bbase (se 3 (by rfl) ⟨548285, by rfl⟩ : syracuseStep 2924189 = 1096571) (by norm_num)
theorem B1949459 : Blo 1949435 1949459 := bstep (se 1 (by rfl) ⟨1462094, by rfl⟩ : syracuseStep 1949459 = 2924189) B2924189
theorem B4386293 : Blo 1949435 4386293 := bbase (se 5 (by rfl) ⟨205607, by rfl⟩ : syracuseStep 4386293 = 411215) (by norm_num)
theorem B2924195 : Blo 1949435 2924195 := bstep (se 1 (by rfl) ⟨2193146, by rfl⟩ : syracuseStep 2924195 = 4386293) B4386293
theorem B1949463 : Blo 1949435 1949463 := bstep (se 1 (by rfl) ⟨1462097, by rfl⟩ : syracuseStep 1949463 = 2924195) B2924195
theorem B15005749 : Blo 1949435 15005749 := bbase (se 5 (by rfl) ⟨703394, by rfl⟩ : syracuseStep 15005749 = 1406789) (by norm_num)
theorem B20007665 : Blo 1949435 20007665 := bstep (se 2 (by rfl) ⟨7502874, by rfl⟩ : syracuseStep 20007665 = 15005749) B15005749
theorem B13338443 : Blo 1949435 13338443 := bstep (se 1 (by rfl) ⟨10003832, by rfl⟩ : syracuseStep 13338443 = 20007665) B20007665
theorem B35569181 : Blo 1949435 35569181 := bstep (se 3 (by rfl) ⟨6669221, by rfl⟩ : syracuseStep 35569181 = 13338443) B13338443
theorem B23712787 : Blo 1949435 23712787 := bstep (se 1 (by rfl) ⟨17784590, by rfl⟩ : syracuseStep 23712787 = 35569181) B35569181
theorem B31617049 : Blo 1949435 31617049 := bstep (se 2 (by rfl) ⟨11856393, by rfl⟩ : syracuseStep 31617049 = 23712787) B23712787
theorem B42156065 : Blo 1949435 42156065 := bstep (se 2 (by rfl) ⟨15808524, by rfl⟩ : syracuseStep 42156065 = 31617049) B31617049
theorem B28104043 : Blo 1949435 28104043 := bstep (se 1 (by rfl) ⟨21078032, by rfl⟩ : syracuseStep 28104043 = 42156065) B42156065
theorem B37472057 : Blo 1949435 37472057 := bstep (se 2 (by rfl) ⟨14052021, by rfl⟩ : syracuseStep 37472057 = 28104043) B28104043
theorem B24981371 : Blo 1949435 24981371 := bstep (se 1 (by rfl) ⟨18736028, by rfl⟩ : syracuseStep 24981371 = 37472057) B37472057
theorem B16654247 : Blo 1949435 16654247 := bstep (se 1 (by rfl) ⟨12490685, by rfl⟩ : syracuseStep 16654247 = 24981371) B24981371
theorem B11102831 : Blo 1949435 11102831 := bstep (se 1 (by rfl) ⟨8327123, by rfl⟩ : syracuseStep 11102831 = 16654247) B16654247
theorem B7401887 : Blo 1949435 7401887 := bstep (se 1 (by rfl) ⟨5551415, by rfl⟩ : syracuseStep 7401887 = 11102831) B11102831
theorem B4934591 : Blo 1949435 4934591 := bstep (se 1 (by rfl) ⟨3700943, by rfl⟩ : syracuseStep 4934591 = 7401887) B7401887
theorem B3289727 : Blo 1949435 3289727 := bstep (se 1 (by rfl) ⟨2467295, by rfl⟩ : syracuseStep 3289727 = 4934591) B4934591
theorem B2193151 : Blo 1949435 2193151 := bstep (se 1 (by rfl) ⟨1644863, by rfl⟩ : syracuseStep 2193151 = 3289727) B3289727
theorem B2924201 : Blo 1949435 2924201 := bstep (se 2 (by rfl) ⟨1096575, by rfl⟩ : syracuseStep 2924201 = 2193151) B2193151
theorem B1949467 : Blo 1949435 1949467 := bstep (se 1 (by rfl) ⟨1462100, by rfl⟩ : syracuseStep 1949467 = 2924201) B2924201
theorem B2081785 : Blo 1949435 2081785 := bbase (se 2 (by rfl) ⟨780669, by rfl⟩ : syracuseStep 2081785 = 1561339) (by norm_num)
theorem B2775713 : Blo 1949435 2775713 := bstep (se 2 (by rfl) ⟨1040892, by rfl⟩ : syracuseStep 2775713 = 2081785) B2081785
theorem B7401901 : Blo 1949435 7401901 := bstep (se 3 (by rfl) ⟨1387856, by rfl⟩ : syracuseStep 7401901 = 2775713) B2775713
theorem B9869201 : Blo 1949435 9869201 := bstep (se 2 (by rfl) ⟨3700950, by rfl⟩ : syracuseStep 9869201 = 7401901) B7401901
theorem B6579467 : Blo 1949435 6579467 := bstep (se 1 (by rfl) ⟨4934600, by rfl⟩ : syracuseStep 6579467 = 9869201) B9869201
theorem B4386311 : Blo 1949435 4386311 := bstep (se 1 (by rfl) ⟨3289733, by rfl⟩ : syracuseStep 4386311 = 6579467) B6579467
theorem B2924207 : Blo 1949435 2924207 := bstep (se 1 (by rfl) ⟨2193155, by rfl⟩ : syracuseStep 2924207 = 4386311) B4386311
theorem B1949471 : Blo 1949435 1949471 := bstep (se 1 (by rfl) ⟨1462103, by rfl⟩ : syracuseStep 1949471 = 2924207) B2924207
theorem B2924213 : Blo 1949435 2924213 := bbase (se 5 (by rfl) ⟨137072, by rfl⟩ : syracuseStep 2924213 = 274145) (by norm_num)
theorem B1949475 : Blo 1949435 1949475 := bstep (se 1 (by rfl) ⟨1462106, by rfl⟩ : syracuseStep 1949475 = 2924213) B2924213
theorem B4934621 : Blo 1949435 4934621 := bbase (se 3 (by rfl) ⟨925241, by rfl⟩ : syracuseStep 4934621 = 1850483) (by norm_num)
theorem B3289747 : Blo 1949435 3289747 := bstep (se 1 (by rfl) ⟨2467310, by rfl⟩ : syracuseStep 3289747 = 4934621) B4934621
theorem B4386329 : Blo 1949435 4386329 := bstep (se 2 (by rfl) ⟨1644873, by rfl⟩ : syracuseStep 4386329 = 3289747) B3289747
theorem B2924219 : Blo 1949435 2924219 := bstep (se 1 (by rfl) ⟨2193164, by rfl⟩ : syracuseStep 2924219 = 4386329) B4386329
theorem B1949479 : Blo 1949435 1949479 := bstep (se 1 (by rfl) ⟨1462109, by rfl⟩ : syracuseStep 1949479 = 2924219) B2924219
theorem B2193169 : Blo 1949435 2193169 := bbase (se 2 (by rfl) ⟨822438, by rfl⟩ : syracuseStep 2193169 = 1644877) (by norm_num)
theorem B2924225 : Blo 1949435 2924225 := bstep (se 2 (by rfl) ⟨1096584, by rfl⟩ : syracuseStep 2924225 = 2193169) B2193169
theorem B1949483 : Blo 1949435 1949483 := bstep (se 1 (by rfl) ⟨1462112, by rfl⟩ : syracuseStep 1949483 = 2924225) B2924225
theorem B3700981 : Blo 1949435 3700981 := bbase (se 5 (by rfl) ⟨173483, by rfl⟩ : syracuseStep 3700981 = 346967) (by norm_num)
theorem B4934641 : Blo 1949435 4934641 := bstep (se 2 (by rfl) ⟨1850490, by rfl⟩ : syracuseStep 4934641 = 3700981) B3700981
theorem B6579521 : Blo 1949435 6579521 := bstep (se 2 (by rfl) ⟨2467320, by rfl⟩ : syracuseStep 6579521 = 4934641) B4934641
theorem B4386347 : Blo 1949435 4386347 := bstep (se 1 (by rfl) ⟨3289760, by rfl⟩ : syracuseStep 4386347 = 6579521) B6579521
theorem B2924231 : Blo 1949435 2924231 := bstep (se 1 (by rfl) ⟨2193173, by rfl⟩ : syracuseStep 2924231 = 4386347) B4386347
theorem B1949487 : Blo 1949435 1949487 := bstep (se 1 (by rfl) ⟨1462115, by rfl⟩ : syracuseStep 1949487 = 2924231) B2924231
theorem B2924237 : Blo 1949435 2924237 := bbase (se 3 (by rfl) ⟨548294, by rfl⟩ : syracuseStep 2924237 = 1096589) (by norm_num)
theorem B1949491 : Blo 1949435 1949491 := bstep (se 1 (by rfl) ⟨1462118, by rfl⟩ : syracuseStep 1949491 = 2924237) B2924237
theorem B4386365 : Blo 1949435 4386365 := bbase (se 3 (by rfl) ⟨822443, by rfl⟩ : syracuseStep 4386365 = 1644887) (by norm_num)
theorem B2924243 : Blo 1949435 2924243 := bstep (se 1 (by rfl) ⟨2193182, by rfl⟩ : syracuseStep 2924243 = 4386365) B4386365
theorem B1949495 : Blo 1949435 1949495 := bstep (se 1 (by rfl) ⟨1462121, by rfl⟩ : syracuseStep 1949495 = 2924243) B2924243
theorem B3289781 : Blo 1949435 3289781 := bbase (se 5 (by rfl) ⟨154208, by rfl⟩ : syracuseStep 3289781 = 308417) (by norm_num)
theorem B2193187 : Blo 1949435 2193187 := bstep (se 1 (by rfl) ⟨1644890, by rfl⟩ : syracuseStep 2193187 = 3289781) B3289781
theorem B2924249 : Blo 1949435 2924249 := bstep (se 2 (by rfl) ⟨1096593, by rfl⟩ : syracuseStep 2924249 = 2193187) B2193187
theorem B1949499 : Blo 1949435 1949499 := bstep (se 1 (by rfl) ⟨1462124, by rfl⟩ : syracuseStep 1949499 = 2924249) B2924249
theorem B2030393 : Blo 1949435 2030393 := bbase (se 2 (by rfl) ⟨761397, by rfl⟩ : syracuseStep 2030393 = 1522795) (by norm_num)
theorem B5414381 : Blo 1949435 5414381 := bstep (se 3 (by rfl) ⟨1015196, by rfl⟩ : syracuseStep 5414381 = 2030393) B2030393
theorem B3609587 : Blo 1949435 3609587 := bstep (se 1 (by rfl) ⟨2707190, by rfl⟩ : syracuseStep 3609587 = 5414381) B5414381
theorem B2406391 : Blo 1949435 2406391 := bstep (se 1 (by rfl) ⟨1804793, by rfl⟩ : syracuseStep 2406391 = 3609587) B3609587
theorem B51336341 : Blo 1949435 51336341 := bstep (se 6 (by rfl) ⟨1203195, by rfl⟩ : syracuseStep 51336341 = 2406391) B2406391
theorem B34224227 : Blo 1949435 34224227 := bstep (se 1 (by rfl) ⟨25668170, by rfl⟩ : syracuseStep 34224227 = 51336341) B51336341
theorem B22816151 : Blo 1949435 22816151 := bstep (se 1 (by rfl) ⟨17112113, by rfl⟩ : syracuseStep 22816151 = 34224227) B34224227
theorem B15210767 : Blo 1949435 15210767 := bstep (se 1 (by rfl) ⟨11408075, by rfl⟩ : syracuseStep 15210767 = 22816151) B22816151
theorem B40562045 : Blo 1949435 40562045 := bstep (se 3 (by rfl) ⟨7605383, by rfl⟩ : syracuseStep 40562045 = 15210767) B15210767
theorem B27041363 : Blo 1949435 27041363 := bstep (se 1 (by rfl) ⟨20281022, by rfl⟩ : syracuseStep 27041363 = 40562045) B40562045
theorem B18027575 : Blo 1949435 18027575 := bstep (se 1 (by rfl) ⟨13520681, by rfl⟩ : syracuseStep 18027575 = 27041363) B27041363
theorem B12018383 : Blo 1949435 12018383 := bstep (se 1 (by rfl) ⟨9013787, by rfl⟩ : syracuseStep 12018383 = 18027575) B18027575
theorem B8012255 : Blo 1949435 8012255 := bstep (se 1 (by rfl) ⟨6009191, by rfl⟩ : syracuseStep 8012255 = 12018383) B12018383
theorem B21366013 : Blo 1949435 21366013 := bstep (se 3 (by rfl) ⟨4006127, by rfl⟩ : syracuseStep 21366013 = 8012255) B8012255
theorem B28488017 : Blo 1949435 28488017 := bstep (se 2 (by rfl) ⟨10683006, by rfl⟩ : syracuseStep 28488017 = 21366013) B21366013
theorem B18992011 : Blo 1949435 18992011 := bstep (se 1 (by rfl) ⟨14244008, by rfl⟩ : syracuseStep 18992011 = 28488017) B28488017
theorem B25322681 : Blo 1949435 25322681 := bstep (se 2 (by rfl) ⟨9496005, by rfl⟩ : syracuseStep 25322681 = 18992011) B18992011
theorem B16881787 : Blo 1949435 16881787 := bstep (se 1 (by rfl) ⟨12661340, by rfl⟩ : syracuseStep 16881787 = 25322681) B25322681
theorem B22509049 : Blo 1949435 22509049 := bstep (se 2 (by rfl) ⟨8440893, by rfl⟩ : syracuseStep 22509049 = 16881787) B16881787
theorem B30012065 : Blo 1949435 30012065 := bstep (se 2 (by rfl) ⟨11254524, by rfl⟩ : syracuseStep 30012065 = 22509049) B22509049
theorem B20008043 : Blo 1949435 20008043 := bstep (se 1 (by rfl) ⟨15006032, by rfl⟩ : syracuseStep 20008043 = 30012065) B30012065
theorem B13338695 : Blo 1949435 13338695 := bstep (se 1 (by rfl) ⟨10004021, by rfl⟩ : syracuseStep 13338695 = 20008043) B20008043
theorem B8892463 : Blo 1949435 8892463 := bstep (se 1 (by rfl) ⟨6669347, by rfl⟩ : syracuseStep 8892463 = 13338695) B13338695
theorem B11856617 : Blo 1949435 11856617 := bstep (se 2 (by rfl) ⟨4446231, by rfl⟩ : syracuseStep 11856617 = 8892463) B8892463
theorem B7904411 : Blo 1949435 7904411 := bstep (se 1 (by rfl) ⟨5928308, by rfl⟩ : syracuseStep 7904411 = 11856617) B11856617
theorem B5269607 : Blo 1949435 5269607 := bstep (se 1 (by rfl) ⟨3952205, by rfl⟩ : syracuseStep 5269607 = 7904411) B7904411
theorem B3513071 : Blo 1949435 3513071 := bstep (se 1 (by rfl) ⟨2634803, by rfl⟩ : syracuseStep 3513071 = 5269607) B5269607
theorem B2342047 : Blo 1949435 2342047 := bstep (se 1 (by rfl) ⟨1756535, by rfl⟩ : syracuseStep 2342047 = 3513071) B3513071
theorem B3122729 : Blo 1949435 3122729 := bstep (se 2 (by rfl) ⟨1171023, by rfl⟩ : syracuseStep 3122729 = 2342047) B2342047
theorem B2081819 : Blo 1949435 2081819 := bstep (se 1 (by rfl) ⟨1561364, by rfl⟩ : syracuseStep 2081819 = 3122729) B3122729
theorem B5551517 : Blo 1949435 5551517 := bstep (se 3 (by rfl) ⟨1040909, by rfl⟩ : syracuseStep 5551517 = 2081819) B2081819
theorem B14804045 : Blo 1949435 14804045 := bstep (se 3 (by rfl) ⟨2775758, by rfl⟩ : syracuseStep 14804045 = 5551517) B5551517
theorem B9869363 : Blo 1949435 9869363 := bstep (se 1 (by rfl) ⟨7402022, by rfl⟩ : syracuseStep 9869363 = 14804045) B14804045
theorem B6579575 : Blo 1949435 6579575 := bstep (se 1 (by rfl) ⟨4934681, by rfl⟩ : syracuseStep 6579575 = 9869363) B9869363
theorem B4386383 : Blo 1949435 4386383 := bstep (se 1 (by rfl) ⟨3289787, by rfl⟩ : syracuseStep 4386383 = 6579575) B6579575
theorem B2924255 : Blo 1949435 2924255 := bstep (se 1 (by rfl) ⟨2193191, by rfl⟩ : syracuseStep 2924255 = 4386383) B4386383
theorem B1949503 : Blo 1949435 1949503 := bstep (se 1 (by rfl) ⟨1462127, by rfl⟩ : syracuseStep 1949503 = 2924255) B2924255
theorem B2924261 : Blo 1949435 2924261 := bbase (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) (by norm_num)
theorem B1949507 : Blo 1949435 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B5551541 : Blo 1949435 5551541 := bbase (se 5 (by rfl) ⟨260228, by rfl⟩ : syracuseStep 5551541 = 520457) (by norm_num)
theorem B3701027 : Blo 1949435 3701027 := bstep (se 1 (by rfl) ⟨2775770, by rfl⟩ : syracuseStep 3701027 = 5551541) B5551541
theorem B2467351 : Blo 1949435 2467351 := bstep (se 1 (by rfl) ⟨1850513, by rfl⟩ : syracuseStep 2467351 = 3701027) B3701027
theorem B3289801 : Blo 1949435 3289801 := bstep (se 2 (by rfl) ⟨1233675, by rfl⟩ : syracuseStep 3289801 = 2467351) B2467351
theorem B4386401 : Blo 1949435 4386401 := bstep (se 2 (by rfl) ⟨1644900, by rfl⟩ : syracuseStep 4386401 = 3289801) B3289801
theorem B2924267 : Blo 1949435 2924267 := bstep (se 1 (by rfl) ⟨2193200, by rfl⟩ : syracuseStep 2924267 = 4386401) B4386401
theorem B1949511 : Blo 1949435 1949511 := bstep (se 1 (by rfl) ⟨1462133, by rfl⟩ : syracuseStep 1949511 = 2924267) B2924267
theorem B2193205 : Blo 1949435 2193205 := bbase (se 5 (by rfl) ⟨102806, by rfl⟩ : syracuseStep 2193205 = 205613) (by norm_num)
theorem B2924273 : Blo 1949435 2924273 := bstep (se 2 (by rfl) ⟨1096602, by rfl⟩ : syracuseStep 2924273 = 2193205) B2193205
theorem B1949515 : Blo 1949435 1949515 := bstep (se 1 (by rfl) ⟨1462136, by rfl⟩ : syracuseStep 1949515 = 2924273) B2924273
theorem B2467361 : Blo 1949435 2467361 := bbase (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) (by norm_num)
theorem B6579629 : Blo 1949435 6579629 := bstep (se 3 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 6579629 = 2467361) B2467361
theorem B4386419 : Blo 1949435 4386419 := bstep (se 1 (by rfl) ⟨3289814, by rfl⟩ : syracuseStep 4386419 = 6579629) B6579629
theorem B2924279 : Blo 1949435 2924279 := bstep (se 1 (by rfl) ⟨2193209, by rfl⟩ : syracuseStep 2924279 = 4386419) B4386419
theorem B1949519 : Blo 1949435 1949519 := bstep (se 1 (by rfl) ⟨1462139, by rfl⟩ : syracuseStep 1949519 = 2924279) B2924279
theorem B2924285 : Blo 1949435 2924285 := bbase (se 3 (by rfl) ⟨548303, by rfl⟩ : syracuseStep 2924285 = 1096607) (by norm_num)
theorem B1949523 : Blo 1949435 1949523 := bstep (se 1 (by rfl) ⟨1462142, by rfl⟩ : syracuseStep 1949523 = 2924285) B2924285
theorem B4386437 : Blo 1949435 4386437 := bbase (se 4 (by rfl) ⟨411228, by rfl⟩ : syracuseStep 4386437 = 822457) (by norm_num)
theorem B2924291 : Blo 1949435 2924291 := bstep (se 1 (by rfl) ⟨2193218, by rfl⟩ : syracuseStep 2924291 = 4386437) B4386437
theorem B1949527 : Blo 1949435 1949527 := bstep (se 1 (by rfl) ⟨1462145, by rfl⟩ : syracuseStep 1949527 = 2924291) B2924291
theorem B2342081 : Blo 1949435 2342081 := bbase (se 2 (by rfl) ⟨878280, by rfl⟩ : syracuseStep 2342081 = 1756561) (by norm_num)
theorem B6245549 : Blo 1949435 6245549 := bstep (se 3 (by rfl) ⟨1171040, by rfl⟩ : syracuseStep 6245549 = 2342081) B2342081
theorem B4163699 : Blo 1949435 4163699 := bstep (se 1 (by rfl) ⟨3122774, by rfl⟩ : syracuseStep 4163699 = 6245549) B6245549
theorem B2775799 : Blo 1949435 2775799 := bstep (se 1 (by rfl) ⟨2081849, by rfl⟩ : syracuseStep 2775799 = 4163699) B4163699
theorem B3701065 : Blo 1949435 3701065 := bstep (se 2 (by rfl) ⟨1387899, by rfl⟩ : syracuseStep 3701065 = 2775799) B2775799
theorem B4934753 : Blo 1949435 4934753 := bstep (se 2 (by rfl) ⟨1850532, by rfl⟩ : syracuseStep 4934753 = 3701065) B3701065
theorem B3289835 : Blo 1949435 3289835 := bstep (se 1 (by rfl) ⟨2467376, by rfl⟩ : syracuseStep 3289835 = 4934753) B4934753
theorem B2193223 : Blo 1949435 2193223 := bstep (se 1 (by rfl) ⟨1644917, by rfl⟩ : syracuseStep 2193223 = 3289835) B3289835
theorem B2924297 : Blo 1949435 2924297 := bstep (se 2 (by rfl) ⟨1096611, by rfl⟩ : syracuseStep 2924297 = 2193223) B2193223
theorem B1949531 : Blo 1949435 1949531 := bstep (se 1 (by rfl) ⟨1462148, by rfl⟩ : syracuseStep 1949531 = 2924297) B2924297
theorem B9869525 : Blo 1949435 9869525 := bbase (se 7 (by rfl) ⟨115658, by rfl⟩ : syracuseStep 9869525 = 231317) (by norm_num)
theorem B6579683 : Blo 1949435 6579683 := bstep (se 1 (by rfl) ⟨4934762, by rfl⟩ : syracuseStep 6579683 = 9869525) B9869525
theorem B4386455 : Blo 1949435 4386455 := bstep (se 1 (by rfl) ⟨3289841, by rfl⟩ : syracuseStep 4386455 = 6579683) B6579683
theorem B2924303 : Blo 1949435 2924303 := bstep (se 1 (by rfl) ⟨2193227, by rfl⟩ : syracuseStep 2924303 = 4386455) B4386455
theorem B1949535 : Blo 1949435 1949535 := bstep (se 1 (by rfl) ⟨1462151, by rfl⟩ : syracuseStep 1949535 = 2924303) B2924303
theorem B2924309 : Blo 1949435 2924309 := bbase (se 6 (by rfl) ⟨68538, by rfl⟩ : syracuseStep 2924309 = 137077) (by norm_num)
theorem B1949539 : Blo 1949435 1949539 := bstep (se 1 (by rfl) ⟨1462154, by rfl⟩ : syracuseStep 1949539 = 2924309) B2924309
theorem B5139533 : Blo 1949435 5139533 := bbase (se 3 (by rfl) ⟨963662, by rfl⟩ : syracuseStep 5139533 = 1927325) (by norm_num)
theorem B13705421 : Blo 1949435 13705421 := bstep (se 3 (by rfl) ⟨2569766, by rfl⟩ : syracuseStep 13705421 = 5139533) B5139533
theorem B36547789 : Blo 1949435 36547789 := bstep (se 3 (by rfl) ⟨6852710, by rfl⟩ : syracuseStep 36547789 = 13705421) B13705421
theorem B48730385 : Blo 1949435 48730385 := bstep (se 2 (by rfl) ⟨18273894, by rfl⟩ : syracuseStep 48730385 = 36547789) B36547789
theorem B32486923 : Blo 1949435 32486923 := bstep (se 1 (by rfl) ⟨24365192, by rfl⟩ : syracuseStep 32486923 = 48730385) B48730385
theorem B43315897 : Blo 1949435 43315897 := bstep (se 2 (by rfl) ⟨16243461, by rfl⟩ : syracuseStep 43315897 = 32486923) B32486923
theorem B57754529 : Blo 1949435 57754529 := bstep (se 2 (by rfl) ⟨21657948, by rfl⟩ : syracuseStep 57754529 = 43315897) B43315897
theorem B38503019 : Blo 1949435 38503019 := bstep (se 1 (by rfl) ⟨28877264, by rfl⟩ : syracuseStep 38503019 = 57754529) B57754529
theorem B25668679 : Blo 1949435 25668679 := bstep (se 1 (by rfl) ⟨19251509, by rfl⟩ : syracuseStep 25668679 = 38503019) B38503019
theorem B34224905 : Blo 1949435 34224905 := bstep (se 2 (by rfl) ⟨12834339, by rfl⟩ : syracuseStep 34224905 = 25668679) B25668679
theorem B22816603 : Blo 1949435 22816603 := bstep (se 1 (by rfl) ⟨17112452, by rfl⟩ : syracuseStep 22816603 = 34224905) B34224905
theorem B30422137 : Blo 1949435 30422137 := bstep (se 2 (by rfl) ⟨11408301, by rfl⟩ : syracuseStep 30422137 = 22816603) B22816603
theorem B40562849 : Blo 1949435 40562849 := bstep (se 2 (by rfl) ⟨15211068, by rfl⟩ : syracuseStep 40562849 = 30422137) B30422137
theorem B27041899 : Blo 1949435 27041899 := bstep (se 1 (by rfl) ⟨20281424, by rfl⟩ : syracuseStep 27041899 = 40562849) B40562849
theorem B36055865 : Blo 1949435 36055865 := bstep (se 2 (by rfl) ⟨13520949, by rfl⟩ : syracuseStep 36055865 = 27041899) B27041899
theorem B24037243 : Blo 1949435 24037243 := bstep (se 1 (by rfl) ⟨18027932, by rfl⟩ : syracuseStep 24037243 = 36055865) B36055865
theorem B128198629 : Blo 1949435 128198629 := bstep (se 4 (by rfl) ⟨12018621, by rfl⟩ : syracuseStep 128198629 = 24037243) B24037243
theorem B170931505 : Blo 1949435 170931505 := bstep (se 2 (by rfl) ⟨64099314, by rfl⟩ : syracuseStep 170931505 = 128198629) B128198629
theorem B227908673 : Blo 1949435 227908673 := bstep (se 2 (by rfl) ⟨85465752, by rfl⟩ : syracuseStep 227908673 = 170931505) B170931505
theorem B151939115 : Blo 1949435 151939115 := bstep (se 1 (by rfl) ⟨113954336, by rfl⟩ : syracuseStep 151939115 = 227908673) B227908673
theorem B101292743 : Blo 1949435 101292743 := bstep (se 1 (by rfl) ⟨75969557, by rfl⟩ : syracuseStep 101292743 = 151939115) B151939115
theorem B67528495 : Blo 1949435 67528495 := bstep (se 1 (by rfl) ⟨50646371, by rfl⟩ : syracuseStep 67528495 = 101292743) B101292743
theorem B90037993 : Blo 1949435 90037993 := bstep (se 2 (by rfl) ⟨33764247, by rfl⟩ : syracuseStep 90037993 = 67528495) B67528495
theorem B120050657 : Blo 1949435 120050657 := bstep (se 2 (by rfl) ⟨45018996, by rfl⟩ : syracuseStep 120050657 = 90037993) B90037993
theorem B80033771 : Blo 1949435 80033771 := bstep (se 1 (by rfl) ⟨60025328, by rfl⟩ : syracuseStep 80033771 = 120050657) B120050657
theorem B53355847 : Blo 1949435 53355847 := bstep (se 1 (by rfl) ⟨40016885, by rfl⟩ : syracuseStep 53355847 = 80033771) B80033771
theorem B71141129 : Blo 1949435 71141129 := bstep (se 2 (by rfl) ⟨26677923, by rfl⟩ : syracuseStep 71141129 = 53355847) B53355847
theorem B47427419 : Blo 1949435 47427419 := bstep (se 1 (by rfl) ⟨35570564, by rfl⟩ : syracuseStep 47427419 = 71141129) B71141129
theorem B31618279 : Blo 1949435 31618279 := bstep (se 1 (by rfl) ⟨23713709, by rfl⟩ : syracuseStep 31618279 = 47427419) B47427419
theorem B42157705 : Blo 1949435 42157705 := bstep (se 2 (by rfl) ⟨15809139, by rfl⟩ : syracuseStep 42157705 = 31618279) B31618279
theorem B56210273 : Blo 1949435 56210273 := bstep (se 2 (by rfl) ⟨21078852, by rfl⟩ : syracuseStep 56210273 = 42157705) B42157705
theorem B37473515 : Blo 1949435 37473515 := bstep (se 1 (by rfl) ⟨28105136, by rfl⟩ : syracuseStep 37473515 = 56210273) B56210273
theorem B24982343 : Blo 1949435 24982343 := bstep (se 1 (by rfl) ⟨18736757, by rfl⟩ : syracuseStep 24982343 = 37473515) B37473515
theorem B16654895 : Blo 1949435 16654895 := bstep (se 1 (by rfl) ⟨12491171, by rfl⟩ : syracuseStep 16654895 = 24982343) B24982343
theorem B11103263 : Blo 1949435 11103263 := bstep (se 1 (by rfl) ⟨8327447, by rfl⟩ : syracuseStep 11103263 = 16654895) B16654895
theorem B7402175 : Blo 1949435 7402175 := bstep (se 1 (by rfl) ⟨5551631, by rfl⟩ : syracuseStep 7402175 = 11103263) B11103263
theorem B4934783 : Blo 1949435 4934783 := bstep (se 1 (by rfl) ⟨3701087, by rfl⟩ : syracuseStep 4934783 = 7402175) B7402175
theorem B3289855 : Blo 1949435 3289855 := bstep (se 1 (by rfl) ⟨2467391, by rfl⟩ : syracuseStep 3289855 = 4934783) B4934783
theorem B4386473 : Blo 1949435 4386473 := bstep (se 2 (by rfl) ⟨1644927, by rfl⟩ : syracuseStep 4386473 = 3289855) B3289855
theorem B2924315 : Blo 1949435 2924315 := bstep (se 1 (by rfl) ⟨2193236, by rfl⟩ : syracuseStep 2924315 = 4386473) B4386473
theorem B1949543 : Blo 1949435 1949543 := bstep (se 1 (by rfl) ⟨1462157, by rfl⟩ : syracuseStep 1949543 = 2924315) B2924315
theorem B2193241 : Blo 1949435 2193241 := bbase (se 2 (by rfl) ⟨822465, by rfl⟩ : syracuseStep 2193241 = 1644931) (by norm_num)
theorem B2924321 : Blo 1949435 2924321 := bstep (se 2 (by rfl) ⟨1096620, by rfl⟩ : syracuseStep 2924321 = 2193241) B2193241
theorem B1949547 : Blo 1949435 1949547 := bstep (se 1 (by rfl) ⟨1462160, by rfl⟩ : syracuseStep 1949547 = 2924321) B2924321
theorem B4163741 : Blo 1949435 4163741 := bbase (se 3 (by rfl) ⟨780701, by rfl⟩ : syracuseStep 4163741 = 1561403) (by norm_num)
theorem B2775827 : Blo 1949435 2775827 := bstep (se 1 (by rfl) ⟨2081870, by rfl⟩ : syracuseStep 2775827 = 4163741) B4163741
theorem B7402205 : Blo 1949435 7402205 := bstep (se 3 (by rfl) ⟨1387913, by rfl⟩ : syracuseStep 7402205 = 2775827) B2775827
theorem B4934803 : Blo 1949435 4934803 := bstep (se 1 (by rfl) ⟨3701102, by rfl⟩ : syracuseStep 4934803 = 7402205) B7402205
theorem B6579737 : Blo 1949435 6579737 := bstep (se 2 (by rfl) ⟨2467401, by rfl⟩ : syracuseStep 6579737 = 4934803) B4934803
theorem B4386491 : Blo 1949435 4386491 := bstep (se 1 (by rfl) ⟨3289868, by rfl⟩ : syracuseStep 4386491 = 6579737) B6579737
theorem B2924327 : Blo 1949435 2924327 := bstep (se 1 (by rfl) ⟨2193245, by rfl⟩ : syracuseStep 2924327 = 4386491) B4386491
theorem B1949551 : Blo 1949435 1949551 := bstep (se 1 (by rfl) ⟨1462163, by rfl⟩ : syracuseStep 1949551 = 2924327) B2924327
theorem B2924333 : Blo 1949435 2924333 := bbase (se 3 (by rfl) ⟨548312, by rfl⟩ : syracuseStep 2924333 = 1096625) (by norm_num)
theorem B1949555 : Blo 1949435 1949555 := bstep (se 1 (by rfl) ⟨1462166, by rfl⟩ : syracuseStep 1949555 = 2924333) B2924333
theorem B4386509 : Blo 1949435 4386509 := bbase (se 3 (by rfl) ⟨822470, by rfl⟩ : syracuseStep 4386509 = 1644941) (by norm_num)
theorem B2924339 : Blo 1949435 2924339 := bstep (se 1 (by rfl) ⟨2193254, by rfl⟩ : syracuseStep 2924339 = 4386509) B4386509
theorem B1949559 : Blo 1949435 1949559 := bstep (se 1 (by rfl) ⟨1462169, by rfl⟩ : syracuseStep 1949559 = 2924339) B2924339
theorem B2467417 : Blo 1949435 2467417 := bbase (se 2 (by rfl) ⟨925281, by rfl⟩ : syracuseStep 2467417 = 1850563) (by norm_num)
theorem B3289889 : Blo 1949435 3289889 := bstep (se 2 (by rfl) ⟨1233708, by rfl⟩ : syracuseStep 3289889 = 2467417) B2467417
theorem B2193259 : Blo 1949435 2193259 := bstep (se 1 (by rfl) ⟨1644944, by rfl⟩ : syracuseStep 2193259 = 3289889) B3289889
theorem B2924345 : Blo 1949435 2924345 := bstep (se 2 (by rfl) ⟨1096629, by rfl⟩ : syracuseStep 2924345 = 2193259) B2193259
theorem B1949563 : Blo 1949435 1949563 := bstep (se 1 (by rfl) ⟨1462172, by rfl⟩ : syracuseStep 1949563 = 2924345) B2924345
theorem B4812941 : Blo 1949435 4812941 := bbase (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) (by norm_num)
theorem B3208627 : Blo 1949435 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B4278169 : Blo 1949435 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B5704225 : Blo 1949435 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B121690133 : Blo 1949435 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B81126755 : Blo 1949435 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B54084503 : Blo 1949435 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B36056335 : Blo 1949435 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B48075113 : Blo 1949435 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B32050075 : Blo 1949435 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B42733433 : Blo 1949435 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B28488955 : Blo 1949435 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B37985273 : Blo 1949435 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B25323515 : Blo 1949435 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B16882343 : Blo 1949435 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B11254895 : Blo 1949435 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B7503263 : Blo 1949435 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B5002175 : Blo 1949435 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B3334783 : Blo 1949435 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B4446377 : Blo 1949435 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B2964251 : Blo 1949435 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B1976167 : Blo 1949435 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B10539557 : Blo 1949435 10539557 := bstep (se 4 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 10539557 = 1976167) B1976167
theorem B7026371 : Blo 1949435 7026371 := bstep (se 1 (by rfl) ⟨5269778, by rfl⟩ : syracuseStep 7026371 = 10539557) B10539557
theorem B4684247 : Blo 1949435 4684247 := bstep (se 1 (by rfl) ⟨3513185, by rfl⟩ : syracuseStep 4684247 = 7026371) B7026371
theorem B3122831 : Blo 1949435 3122831 := bstep (se 1 (by rfl) ⟨2342123, by rfl⟩ : syracuseStep 3122831 = 4684247) B4684247
theorem B8327549 : Blo 1949435 8327549 := bstep (se 3 (by rfl) ⟨1561415, by rfl⟩ : syracuseStep 8327549 = 3122831) B3122831
theorem B22206797 : Blo 1949435 22206797 := bstep (se 3 (by rfl) ⟨4163774, by rfl⟩ : syracuseStep 22206797 = 8327549) B8327549
theorem B14804531 : Blo 1949435 14804531 := bstep (se 1 (by rfl) ⟨11103398, by rfl⟩ : syracuseStep 14804531 = 22206797) B22206797
theorem B9869687 : Blo 1949435 9869687 := bstep (se 1 (by rfl) ⟨7402265, by rfl⟩ : syracuseStep 9869687 = 14804531) B14804531
theorem B6579791 : Blo 1949435 6579791 := bstep (se 1 (by rfl) ⟨4934843, by rfl⟩ : syracuseStep 6579791 = 9869687) B9869687
theorem B4386527 : Blo 1949435 4386527 := bstep (se 1 (by rfl) ⟨3289895, by rfl⟩ : syracuseStep 4386527 = 6579791) B6579791
theorem B2924351 : Blo 1949435 2924351 := bstep (se 1 (by rfl) ⟨2193263, by rfl⟩ : syracuseStep 2924351 = 4386527) B4386527
theorem B1949567 : Blo 1949435 1949567 := bstep (se 1 (by rfl) ⟨1462175, by rfl⟩ : syracuseStep 1949567 = 2924351) B2924351
theorem B2924357 : Blo 1949435 2924357 := bbase (se 4 (by rfl) ⟨274158, by rfl⟩ : syracuseStep 2924357 = 548317) (by norm_num)
theorem B1949571 : Blo 1949435 1949571 := bstep (se 1 (by rfl) ⟨1462178, by rfl⟩ : syracuseStep 1949571 = 2924357) B2924357
theorem B3289909 : Blo 1949435 3289909 := bbase (se 5 (by rfl) ⟨154214, by rfl⟩ : syracuseStep 3289909 = 308429) (by norm_num)
theorem B4386545 : Blo 1949435 4386545 := bstep (se 2 (by rfl) ⟨1644954, by rfl⟩ : syracuseStep 4386545 = 3289909) B3289909
theorem B2924363 : Blo 1949435 2924363 := bstep (se 1 (by rfl) ⟨2193272, by rfl⟩ : syracuseStep 2924363 = 4386545) B4386545
theorem B1949575 : Blo 1949435 1949575 := bstep (se 1 (by rfl) ⟨1462181, by rfl⟩ : syracuseStep 1949575 = 2924363) B2924363
theorem B2193277 : Blo 1949435 2193277 := bbase (se 3 (by rfl) ⟨411239, by rfl⟩ : syracuseStep 2193277 = 822479) (by norm_num)
theorem B2924369 : Blo 1949435 2924369 := bstep (se 2 (by rfl) ⟨1096638, by rfl⟩ : syracuseStep 2924369 = 2193277) B2193277
theorem B1949579 : Blo 1949435 1949579 := bstep (se 1 (by rfl) ⟨1462184, by rfl⟩ : syracuseStep 1949579 = 2924369) B2924369
theorem B6579845 : Blo 1949435 6579845 := bbase (se 4 (by rfl) ⟨616860, by rfl⟩ : syracuseStep 6579845 = 1233721) (by norm_num)
theorem B4386563 : Blo 1949435 4386563 := bstep (se 1 (by rfl) ⟨3289922, by rfl⟩ : syracuseStep 4386563 = 6579845) B6579845
theorem B2924375 : Blo 1949435 2924375 := bstep (se 1 (by rfl) ⟨2193281, by rfl⟩ : syracuseStep 2924375 = 4386563) B4386563
theorem B1949583 : Blo 1949435 1949583 := bstep (se 1 (by rfl) ⟨1462187, by rfl⟩ : syracuseStep 1949583 = 2924375) B2924375
theorem B2924381 : Blo 1949435 2924381 := bbase (se 3 (by rfl) ⟨548321, by rfl⟩ : syracuseStep 2924381 = 1096643) (by norm_num)
theorem B1949587 : Blo 1949435 1949587 := bstep (se 1 (by rfl) ⟨1462190, by rfl⟩ : syracuseStep 1949587 = 2924381) B2924381
theorem B4386581 : Blo 1949435 4386581 := bbase (se 6 (by rfl) ⟨102810, by rfl⟩ : syracuseStep 4386581 = 205621) (by norm_num)
theorem B2924387 : Blo 1949435 2924387 := bstep (se 1 (by rfl) ⟨2193290, by rfl⟩ : syracuseStep 2924387 = 4386581) B4386581
theorem B1949591 : Blo 1949435 1949591 := bstep (se 1 (by rfl) ⟨1462193, by rfl⟩ : syracuseStep 1949591 = 2924387) B2924387
theorem B7402373 : Blo 1949435 7402373 := bbase (se 4 (by rfl) ⟨693972, by rfl⟩ : syracuseStep 7402373 = 1387945) (by norm_num)
theorem B4934915 : Blo 1949435 4934915 := bstep (se 1 (by rfl) ⟨3701186, by rfl⟩ : syracuseStep 4934915 = 7402373) B7402373
theorem B3289943 : Blo 1949435 3289943 := bstep (se 1 (by rfl) ⟨2467457, by rfl⟩ : syracuseStep 3289943 = 4934915) B4934915
theorem B2193295 : Blo 1949435 2193295 := bstep (se 1 (by rfl) ⟨1644971, by rfl⟩ : syracuseStep 2193295 = 3289943) B3289943
theorem B2924393 : Blo 1949435 2924393 := bstep (se 2 (by rfl) ⟨1096647, by rfl⟩ : syracuseStep 2924393 = 2193295) B2193295
theorem B1949595 : Blo 1949435 1949595 := bstep (se 1 (by rfl) ⟨1462196, by rfl⟩ : syracuseStep 1949595 = 2924393) B2924393
theorem B6245765 : Blo 1949435 6245765 := bbase (se 4 (by rfl) ⟨585540, by rfl⟩ : syracuseStep 6245765 = 1171081) (by norm_num)
theorem B4163843 : Blo 1949435 4163843 := bstep (se 1 (by rfl) ⟨3122882, by rfl⟩ : syracuseStep 4163843 = 6245765) B6245765
theorem B11103581 : Blo 1949435 11103581 := bstep (se 3 (by rfl) ⟨2081921, by rfl⟩ : syracuseStep 11103581 = 4163843) B4163843
theorem B7402387 : Blo 1949435 7402387 := bstep (se 1 (by rfl) ⟨5551790, by rfl⟩ : syracuseStep 7402387 = 11103581) B11103581
theorem B9869849 : Blo 1949435 9869849 := bstep (se 2 (by rfl) ⟨3701193, by rfl⟩ : syracuseStep 9869849 = 7402387) B7402387
theorem B6579899 : Blo 1949435 6579899 := bstep (se 1 (by rfl) ⟨4934924, by rfl⟩ : syracuseStep 6579899 = 9869849) B9869849
theorem B4386599 : Blo 1949435 4386599 := bstep (se 1 (by rfl) ⟨3289949, by rfl⟩ : syracuseStep 4386599 = 6579899) B6579899
theorem B2924399 : Blo 1949435 2924399 := bstep (se 1 (by rfl) ⟨2193299, by rfl⟩ : syracuseStep 2924399 = 4386599) B4386599
theorem B1949599 : Blo 1949435 1949599 := bstep (se 1 (by rfl) ⟨1462199, by rfl⟩ : syracuseStep 1949599 = 2924399) B2924399
theorem B2924405 : Blo 1949435 2924405 := bbase (se 5 (by rfl) ⟨137081, by rfl⟩ : syracuseStep 2924405 = 274163) (by norm_num)
theorem B1949603 : Blo 1949435 1949603 := bstep (se 1 (by rfl) ⟨1462202, by rfl⟩ : syracuseStep 1949603 = 2924405) B2924405
theorem B4163861 : Blo 1949435 4163861 := bbase (se 6 (by rfl) ⟨97590, by rfl⟩ : syracuseStep 4163861 = 195181) (by norm_num)
theorem B2775907 : Blo 1949435 2775907 := bstep (se 1 (by rfl) ⟨2081930, by rfl⟩ : syracuseStep 2775907 = 4163861) B4163861
theorem B3701209 : Blo 1949435 3701209 := bstep (se 2 (by rfl) ⟨1387953, by rfl⟩ : syracuseStep 3701209 = 2775907) B2775907
theorem B4934945 : Blo 1949435 4934945 := bstep (se 2 (by rfl) ⟨1850604, by rfl⟩ : syracuseStep 4934945 = 3701209) B3701209
theorem B3289963 : Blo 1949435 3289963 := bstep (se 1 (by rfl) ⟨2467472, by rfl⟩ : syracuseStep 3289963 = 4934945) B4934945
theorem B4386617 : Blo 1949435 4386617 := bstep (se 2 (by rfl) ⟨1644981, by rfl⟩ : syracuseStep 4386617 = 3289963) B3289963
theorem B2924411 : Blo 1949435 2924411 := bstep (se 1 (by rfl) ⟨2193308, by rfl⟩ : syracuseStep 2924411 = 4386617) B4386617
theorem B1949607 : Blo 1949435 1949607 := bstep (se 1 (by rfl) ⟨1462205, by rfl⟩ : syracuseStep 1949607 = 2924411) B2924411
theorem B2193313 : Blo 1949435 2193313 := bbase (se 2 (by rfl) ⟨822492, by rfl⟩ : syracuseStep 2193313 = 1644985) (by norm_num)
theorem B2924417 : Blo 1949435 2924417 := bstep (se 2 (by rfl) ⟨1096656, by rfl⟩ : syracuseStep 2924417 = 2193313) B2193313
theorem B1949611 : Blo 1949435 1949611 := bstep (se 1 (by rfl) ⟨1462208, by rfl⟩ : syracuseStep 1949611 = 2924417) B2924417
theorem B4934965 : Blo 1949435 4934965 := bbase (se 5 (by rfl) ⟨231326, by rfl⟩ : syracuseStep 4934965 = 462653) (by norm_num)
theorem B6579953 : Blo 1949435 6579953 := bstep (se 2 (by rfl) ⟨2467482, by rfl⟩ : syracuseStep 6579953 = 4934965) B4934965
theorem B4386635 : Blo 1949435 4386635 := bstep (se 1 (by rfl) ⟨3289976, by rfl⟩ : syracuseStep 4386635 = 6579953) B6579953
theorem B2924423 : Blo 1949435 2924423 := bstep (se 1 (by rfl) ⟨2193317, by rfl⟩ : syracuseStep 2924423 = 4386635) B4386635
theorem B1949615 : Blo 1949435 1949615 := bstep (se 1 (by rfl) ⟨1462211, by rfl⟩ : syracuseStep 1949615 = 2924423) B2924423
theorem B2924429 : Blo 1949435 2924429 := bbase (se 3 (by rfl) ⟨548330, by rfl⟩ : syracuseStep 2924429 = 1096661) (by norm_num)
theorem B1949619 : Blo 1949435 1949619 := bstep (se 1 (by rfl) ⟨1462214, by rfl⟩ : syracuseStep 1949619 = 2924429) B2924429
theorem B4386653 : Blo 1949435 4386653 := bbase (se 3 (by rfl) ⟨822497, by rfl⟩ : syracuseStep 4386653 = 1644995) (by norm_num)
theorem B2924435 : Blo 1949435 2924435 := bstep (se 1 (by rfl) ⟨2193326, by rfl⟩ : syracuseStep 2924435 = 4386653) B4386653
theorem B1949623 : Blo 1949435 1949623 := bstep (se 1 (by rfl) ⟨1462217, by rfl⟩ : syracuseStep 1949623 = 2924435) B2924435
theorem B3289997 : Blo 1949435 3289997 := bbase (se 3 (by rfl) ⟨616874, by rfl⟩ : syracuseStep 3289997 = 1233749) (by norm_num)
theorem B2193331 : Blo 1949435 2193331 := bstep (se 1 (by rfl) ⟨1644998, by rfl⟩ : syracuseStep 2193331 = 3289997) B3289997
theorem B2924441 : Blo 1949435 2924441 := bstep (se 2 (by rfl) ⟨1096665, by rfl⟩ : syracuseStep 2924441 = 2193331) B2193331
theorem B1949627 : Blo 1949435 1949627 := bstep (se 1 (by rfl) ⟨1462220, by rfl⟩ : syracuseStep 1949627 = 2924441) B2924441
theorem B8911637 : Blo 1949435 8911637 := bbase (se 6 (by rfl) ⟨208866, by rfl⟩ : syracuseStep 8911637 = 417733) (by norm_num)
theorem B5941091 : Blo 1949435 5941091 := bstep (se 1 (by rfl) ⟨4455818, by rfl⟩ : syracuseStep 5941091 = 8911637) B8911637
theorem B15842909 : Blo 1949435 15842909 := bstep (se 3 (by rfl) ⟨2970545, by rfl⟩ : syracuseStep 15842909 = 5941091) B5941091
theorem B42247757 : Blo 1949435 42247757 := bstep (se 3 (by rfl) ⟨7921454, by rfl⟩ : syracuseStep 42247757 = 15842909) B15842909
theorem B28165171 : Blo 1949435 28165171 := bstep (se 1 (by rfl) ⟨21123878, by rfl⟩ : syracuseStep 28165171 = 42247757) B42247757
theorem B37553561 : Blo 1949435 37553561 := bstep (se 2 (by rfl) ⟨14082585, by rfl⟩ : syracuseStep 37553561 = 28165171) B28165171
theorem B25035707 : Blo 1949435 25035707 := bstep (se 1 (by rfl) ⟨18776780, by rfl⟩ : syracuseStep 25035707 = 37553561) B37553561
theorem B66761885 : Blo 1949435 66761885 := bstep (se 3 (by rfl) ⟨12517853, by rfl⟩ : syracuseStep 66761885 = 25035707) B25035707
theorem B178031693 : Blo 1949435 178031693 := bstep (se 3 (by rfl) ⟨33380942, by rfl⟩ : syracuseStep 178031693 = 66761885) B66761885
theorem B474751181 : Blo 1949435 474751181 := bstep (se 3 (by rfl) ⟨89015846, by rfl⟩ : syracuseStep 474751181 = 178031693) B178031693
theorem B316500787 : Blo 1949435 316500787 := bstep (se 1 (by rfl) ⟨237375590, by rfl⟩ : syracuseStep 316500787 = 474751181) B474751181
theorem B422001049 : Blo 1949435 422001049 := bstep (se 2 (by rfl) ⟨158250393, by rfl⟩ : syracuseStep 422001049 = 316500787) B316500787
theorem B562668065 : Blo 1949435 562668065 := bstep (se 2 (by rfl) ⟨211000524, by rfl⟩ : syracuseStep 562668065 = 422001049) B422001049
theorem B375112043 : Blo 1949435 375112043 := bstep (se 1 (by rfl) ⟨281334032, by rfl⟩ : syracuseStep 375112043 = 562668065) B562668065
theorem B250074695 : Blo 1949435 250074695 := bstep (se 1 (by rfl) ⟨187556021, by rfl⟩ : syracuseStep 250074695 = 375112043) B375112043
theorem B166716463 : Blo 1949435 166716463 := bstep (se 1 (by rfl) ⟨125037347, by rfl⟩ : syracuseStep 166716463 = 250074695) B250074695
theorem B222288617 : Blo 1949435 222288617 := bstep (se 2 (by rfl) ⟨83358231, by rfl⟩ : syracuseStep 222288617 = 166716463) B166716463
theorem B148192411 : Blo 1949435 148192411 := bstep (se 1 (by rfl) ⟨111144308, by rfl⟩ : syracuseStep 148192411 = 222288617) B222288617
theorem B197589881 : Blo 1949435 197589881 := bstep (se 2 (by rfl) ⟨74096205, by rfl⟩ : syracuseStep 197589881 = 148192411) B148192411
theorem B131726587 : Blo 1949435 131726587 := bstep (se 1 (by rfl) ⟨98794940, by rfl⟩ : syracuseStep 131726587 = 197589881) B197589881
theorem B175635449 : Blo 1949435 175635449 := bstep (se 2 (by rfl) ⟨65863293, by rfl⟩ : syracuseStep 175635449 = 131726587) B131726587
theorem B117090299 : Blo 1949435 117090299 := bstep (se 1 (by rfl) ⟨87817724, by rfl⟩ : syracuseStep 117090299 = 175635449) B175635449
theorem B78060199 : Blo 1949435 78060199 := bstep (se 1 (by rfl) ⟨58545149, by rfl⟩ : syracuseStep 78060199 = 117090299) B117090299
theorem B104080265 : Blo 1949435 104080265 := bstep (se 2 (by rfl) ⟨39030099, by rfl⟩ : syracuseStep 104080265 = 78060199) B78060199
theorem B69386843 : Blo 1949435 69386843 := bstep (se 1 (by rfl) ⟨52040132, by rfl⟩ : syracuseStep 69386843 = 104080265) B104080265
theorem B46257895 : Blo 1949435 46257895 := bstep (se 1 (by rfl) ⟨34693421, by rfl⟩ : syracuseStep 46257895 = 69386843) B69386843
theorem B246708773 : Blo 1949435 246708773 := bstep (se 4 (by rfl) ⟨23128947, by rfl⟩ : syracuseStep 246708773 = 46257895) B46257895
theorem B164472515 : Blo 1949435 164472515 := bstep (se 1 (by rfl) ⟨123354386, by rfl⟩ : syracuseStep 164472515 = 246708773) B246708773
theorem B109648343 : Blo 1949435 109648343 := bstep (se 1 (by rfl) ⟨82236257, by rfl⟩ : syracuseStep 109648343 = 164472515) B164472515
theorem B292395581 : Blo 1949435 292395581 := bstep (se 3 (by rfl) ⟨54824171, by rfl⟩ : syracuseStep 292395581 = 109648343) B109648343
theorem B194930387 : Blo 1949435 194930387 := bstep (se 1 (by rfl) ⟨146197790, by rfl⟩ : syracuseStep 194930387 = 292395581) B292395581
theorem B129953591 : Blo 1949435 129953591 := bstep (se 1 (by rfl) ⟨97465193, by rfl⟩ : syracuseStep 129953591 = 194930387) B194930387
theorem B86635727 : Blo 1949435 86635727 := bstep (se 1 (by rfl) ⟨64976795, by rfl⟩ : syracuseStep 86635727 = 129953591) B129953591
theorem B57757151 : Blo 1949435 57757151 := bstep (se 1 (by rfl) ⟨43317863, by rfl⟩ : syracuseStep 57757151 = 86635727) B86635727
theorem B38504767 : Blo 1949435 38504767 := bstep (se 1 (by rfl) ⟨28878575, by rfl⟩ : syracuseStep 38504767 = 57757151) B57757151
theorem B51339689 : Blo 1949435 51339689 := bstep (se 2 (by rfl) ⟨19252383, by rfl⟩ : syracuseStep 51339689 = 38504767) B38504767
theorem B34226459 : Blo 1949435 34226459 := bstep (se 1 (by rfl) ⟨25669844, by rfl⟩ : syracuseStep 34226459 = 51339689) B51339689
theorem B22817639 : Blo 1949435 22817639 := bstep (se 1 (by rfl) ⟨17113229, by rfl⟩ : syracuseStep 22817639 = 34226459) B34226459
theorem B15211759 : Blo 1949435 15211759 := bstep (se 1 (by rfl) ⟨11408819, by rfl⟩ : syracuseStep 15211759 = 22817639) B22817639
theorem B20282345 : Blo 1949435 20282345 := bstep (se 2 (by rfl) ⟨7605879, by rfl⟩ : syracuseStep 20282345 = 15211759) B15211759
theorem B13521563 : Blo 1949435 13521563 := bstep (se 1 (by rfl) ⟨10141172, by rfl⟩ : syracuseStep 13521563 = 20282345) B20282345
theorem B9014375 : Blo 1949435 9014375 := bstep (se 1 (by rfl) ⟨6760781, by rfl⟩ : syracuseStep 9014375 = 13521563) B13521563
theorem B24038333 : Blo 1949435 24038333 := bstep (se 3 (by rfl) ⟨4507187, by rfl⟩ : syracuseStep 24038333 = 9014375) B9014375
theorem B16025555 : Blo 1949435 16025555 := bstep (se 1 (by rfl) ⟨12019166, by rfl⟩ : syracuseStep 16025555 = 24038333) B24038333
theorem B10683703 : Blo 1949435 10683703 := bstep (se 1 (by rfl) ⟨8012777, by rfl⟩ : syracuseStep 10683703 = 16025555) B16025555
theorem B56979749 : Blo 1949435 56979749 := bstep (se 4 (by rfl) ⟨5341851, by rfl⟩ : syracuseStep 56979749 = 10683703) B10683703
theorem B37986499 : Blo 1949435 37986499 := bstep (se 1 (by rfl) ⟨28489874, by rfl⟩ : syracuseStep 37986499 = 56979749) B56979749
theorem B50648665 : Blo 1949435 50648665 := bstep (se 2 (by rfl) ⟨18993249, by rfl⟩ : syracuseStep 50648665 = 37986499) B37986499
theorem B67531553 : Blo 1949435 67531553 := bstep (se 2 (by rfl) ⟨25324332, by rfl⟩ : syracuseStep 67531553 = 50648665) B50648665
theorem B45021035 : Blo 1949435 45021035 := bstep (se 1 (by rfl) ⟨33765776, by rfl⟩ : syracuseStep 45021035 = 67531553) B67531553
theorem B30014023 : Blo 1949435 30014023 := bstep (se 1 (by rfl) ⟨22510517, by rfl⟩ : syracuseStep 30014023 = 45021035) B45021035
theorem B40018697 : Blo 1949435 40018697 := bstep (se 2 (by rfl) ⟨15007011, by rfl⟩ : syracuseStep 40018697 = 30014023) B30014023
theorem B26679131 : Blo 1949435 26679131 := bstep (se 1 (by rfl) ⟨20009348, by rfl⟩ : syracuseStep 26679131 = 40018697) B40018697
theorem B17786087 : Blo 1949435 17786087 := bstep (se 1 (by rfl) ⟨13339565, by rfl⟩ : syracuseStep 17786087 = 26679131) B26679131
theorem B11857391 : Blo 1949435 11857391 := bstep (se 1 (by rfl) ⟨8893043, by rfl⟩ : syracuseStep 11857391 = 17786087) B17786087
theorem B7904927 : Blo 1949435 7904927 := bstep (se 1 (by rfl) ⟨5928695, by rfl⟩ : syracuseStep 7904927 = 11857391) B11857391
theorem B5269951 : Blo 1949435 5269951 := bstep (se 1 (by rfl) ⟨3952463, by rfl⟩ : syracuseStep 5269951 = 7904927) B7904927
theorem B7026601 : Blo 1949435 7026601 := bstep (se 2 (by rfl) ⟨2634975, by rfl⟩ : syracuseStep 7026601 = 5269951) B5269951
theorem B9368801 : Blo 1949435 9368801 := bstep (se 2 (by rfl) ⟨3513300, by rfl⟩ : syracuseStep 9368801 = 7026601) B7026601
theorem B6245867 : Blo 1949435 6245867 := bstep (se 1 (by rfl) ⟨4684400, by rfl⟩ : syracuseStep 6245867 = 9368801) B9368801
theorem B16655645 : Blo 1949435 16655645 := bstep (se 3 (by rfl) ⟨3122933, by rfl⟩ : syracuseStep 16655645 = 6245867) B6245867
theorem B11103763 : Blo 1949435 11103763 := bstep (se 1 (by rfl) ⟨8327822, by rfl⟩ : syracuseStep 11103763 = 16655645) B16655645
theorem B14805017 : Blo 1949435 14805017 := bstep (se 2 (by rfl) ⟨5551881, by rfl⟩ : syracuseStep 14805017 = 11103763) B11103763
theorem B9870011 : Blo 1949435 9870011 := bstep (se 1 (by rfl) ⟨7402508, by rfl⟩ : syracuseStep 9870011 = 14805017) B14805017
theorem B6580007 : Blo 1949435 6580007 := bstep (se 1 (by rfl) ⟨4935005, by rfl⟩ : syracuseStep 6580007 = 9870011) B9870011
theorem B4386671 : Blo 1949435 4386671 := bstep (se 1 (by rfl) ⟨3290003, by rfl⟩ : syracuseStep 4386671 = 6580007) B6580007
theorem B2924447 : Blo 1949435 2924447 := bstep (se 1 (by rfl) ⟨2193335, by rfl⟩ : syracuseStep 2924447 = 4386671) B4386671
theorem B1949631 : Blo 1949435 1949631 := bstep (se 1 (by rfl) ⟨1462223, by rfl⟩ : syracuseStep 1949631 = 2924447) B2924447
theorem B2924453 : Blo 1949435 2924453 := bbase (se 4 (by rfl) ⟨274167, by rfl⟩ : syracuseStep 2924453 = 548335) (by norm_num)
theorem B1949635 : Blo 1949435 1949635 := bstep (se 1 (by rfl) ⟨1462226, by rfl⟩ : syracuseStep 1949635 = 2924453) B2924453
theorem B2467513 : Blo 1949435 2467513 := bbase (se 2 (by rfl) ⟨925317, by rfl⟩ : syracuseStep 2467513 = 1850635) (by norm_num)
theorem B3290017 : Blo 1949435 3290017 := bstep (se 2 (by rfl) ⟨1233756, by rfl⟩ : syracuseStep 3290017 = 2467513) B2467513
theorem B4386689 : Blo 1949435 4386689 := bstep (se 2 (by rfl) ⟨1645008, by rfl⟩ : syracuseStep 4386689 = 3290017) B3290017
theorem B2924459 : Blo 1949435 2924459 := bstep (se 1 (by rfl) ⟨2193344, by rfl⟩ : syracuseStep 2924459 = 4386689) B4386689
theorem B1949639 : Blo 1949435 1949639 := bstep (se 1 (by rfl) ⟨1462229, by rfl⟩ : syracuseStep 1949639 = 2924459) B2924459
theorem B2193349 : Blo 1949435 2193349 := bbase (se 4 (by rfl) ⟨205626, by rfl⟩ : syracuseStep 2193349 = 411253) (by norm_num)
theorem B2924465 : Blo 1949435 2924465 := bstep (se 2 (by rfl) ⟨1096674, by rfl⟩ : syracuseStep 2924465 = 2193349) B2193349
theorem B1949643 : Blo 1949435 1949643 := bstep (se 1 (by rfl) ⟨1462232, by rfl⟩ : syracuseStep 1949643 = 2924465) B2924465
theorem B3701285 : Blo 1949435 3701285 := bbase (se 4 (by rfl) ⟨346995, by rfl⟩ : syracuseStep 3701285 = 693991) (by norm_num)
theorem B2467523 : Blo 1949435 2467523 := bstep (se 1 (by rfl) ⟨1850642, by rfl⟩ : syracuseStep 2467523 = 3701285) B3701285
theorem B6580061 : Blo 1949435 6580061 := bstep (se 3 (by rfl) ⟨1233761, by rfl⟩ : syracuseStep 6580061 = 2467523) B2467523
theorem B4386707 : Blo 1949435 4386707 := bstep (se 1 (by rfl) ⟨3290030, by rfl⟩ : syracuseStep 4386707 = 6580061) B6580061
theorem B2924471 : Blo 1949435 2924471 := bstep (se 1 (by rfl) ⟨2193353, by rfl⟩ : syracuseStep 2924471 = 4386707) B4386707
theorem B1949647 : Blo 1949435 1949647 := bstep (se 1 (by rfl) ⟨1462235, by rfl⟩ : syracuseStep 1949647 = 2924471) B2924471
theorem B2924477 : Blo 1949435 2924477 := bbase (se 3 (by rfl) ⟨548339, by rfl⟩ : syracuseStep 2924477 = 1096679) (by norm_num)
theorem B1949651 : Blo 1949435 1949651 := bstep (se 1 (by rfl) ⟨1462238, by rfl⟩ : syracuseStep 1949651 = 2924477) B2924477
theorem B4386725 : Blo 1949435 4386725 := bbase (se 4 (by rfl) ⟨411255, by rfl⟩ : syracuseStep 4386725 = 822511) (by norm_num)
theorem B2924483 : Blo 1949435 2924483 := bstep (se 1 (by rfl) ⟨2193362, by rfl⟩ : syracuseStep 2924483 = 4386725) B4386725
theorem B1949655 : Blo 1949435 1949655 := bstep (se 1 (by rfl) ⟨1462241, by rfl⟩ : syracuseStep 1949655 = 2924483) B2924483
theorem B4935077 : Blo 1949435 4935077 := bbase (se 4 (by rfl) ⟨462663, by rfl⟩ : syracuseStep 4935077 = 925327) (by norm_num)
theorem B3290051 : Blo 1949435 3290051 := bstep (se 1 (by rfl) ⟨2467538, by rfl⟩ : syracuseStep 3290051 = 4935077) B4935077
theorem B2193367 : Blo 1949435 2193367 := bstep (se 1 (by rfl) ⟨1645025, by rfl⟩ : syracuseStep 2193367 = 3290051) B3290051
theorem B2924489 : Blo 1949435 2924489 := bstep (se 2 (by rfl) ⟨1096683, by rfl⟩ : syracuseStep 2924489 = 2193367) B2193367
theorem B1949659 : Blo 1949435 1949659 := bstep (se 1 (by rfl) ⟨1462244, by rfl⟩ : syracuseStep 1949659 = 2924489) B2924489
theorem B5551973 : Blo 1949435 5551973 := bbase (se 4 (by rfl) ⟨520497, by rfl⟩ : syracuseStep 5551973 = 1040995) (by norm_num)
theorem B3701315 : Blo 1949435 3701315 := bstep (se 1 (by rfl) ⟨2775986, by rfl⟩ : syracuseStep 3701315 = 5551973) B5551973
theorem B9870173 : Blo 1949435 9870173 := bstep (se 3 (by rfl) ⟨1850657, by rfl⟩ : syracuseStep 9870173 = 3701315) B3701315
theorem B6580115 : Blo 1949435 6580115 := bstep (se 1 (by rfl) ⟨4935086, by rfl⟩ : syracuseStep 6580115 = 9870173) B9870173
theorem B4386743 : Blo 1949435 4386743 := bstep (se 1 (by rfl) ⟨3290057, by rfl⟩ : syracuseStep 4386743 = 6580115) B6580115
theorem B2924495 : Blo 1949435 2924495 := bstep (se 1 (by rfl) ⟨2193371, by rfl⟩ : syracuseStep 2924495 = 4386743) B4386743
theorem B1949663 : Blo 1949435 1949663 := bstep (se 1 (by rfl) ⟨1462247, by rfl⟩ : syracuseStep 1949663 = 2924495) B2924495
theorem B2924501 : Blo 1949435 2924501 := bbase (se 7 (by rfl) ⟨34271, by rfl⟩ : syracuseStep 2924501 = 68543) (by norm_num)
theorem B1949667 : Blo 1949435 1949667 := bstep (se 1 (by rfl) ⟨1462250, by rfl⟩ : syracuseStep 1949667 = 2924501) B2924501
theorem B7402661 : Blo 1949435 7402661 := bbase (se 4 (by rfl) ⟨693999, by rfl⟩ : syracuseStep 7402661 = 1387999) (by norm_num)
theorem B4935107 : Blo 1949435 4935107 := bstep (se 1 (by rfl) ⟨3701330, by rfl⟩ : syracuseStep 4935107 = 7402661) B7402661
theorem B3290071 : Blo 1949435 3290071 := bstep (se 1 (by rfl) ⟨2467553, by rfl⟩ : syracuseStep 3290071 = 4935107) B4935107
theorem B4386761 : Blo 1949435 4386761 := bstep (se 2 (by rfl) ⟨1645035, by rfl⟩ : syracuseStep 4386761 = 3290071) B3290071
theorem B2924507 : Blo 1949435 2924507 := bstep (se 1 (by rfl) ⟨2193380, by rfl⟩ : syracuseStep 2924507 = 4386761) B4386761
theorem B1949671 : Blo 1949435 1949671 := bstep (se 1 (by rfl) ⟨1462253, by rfl⟩ : syracuseStep 1949671 = 2924507) B2924507
theorem B2193385 : Blo 1949435 2193385 := bbase (se 2 (by rfl) ⟨822519, by rfl⟩ : syracuseStep 2193385 = 1645039) (by norm_num)
theorem B2924513 : Blo 1949435 2924513 := bstep (se 2 (by rfl) ⟨1096692, by rfl⟩ : syracuseStep 2924513 = 2193385) B2193385
theorem B1949675 : Blo 1949435 1949675 := bstep (se 1 (by rfl) ⟨1462256, by rfl⟩ : syracuseStep 1949675 = 2924513) B2924513
theorem B4684517 : Blo 1949435 4684517 := bbase (se 4 (by rfl) ⟨439173, by rfl⟩ : syracuseStep 4684517 = 878347) (by norm_num)
theorem B3123011 : Blo 1949435 3123011 := bstep (se 1 (by rfl) ⟨2342258, by rfl⟩ : syracuseStep 3123011 = 4684517) B4684517
theorem B2082007 : Blo 1949435 2082007 := bstep (se 1 (by rfl) ⟨1561505, by rfl⟩ : syracuseStep 2082007 = 3123011) B3123011
theorem B11104037 : Blo 1949435 11104037 := bstep (se 4 (by rfl) ⟨1041003, by rfl⟩ : syracuseStep 11104037 = 2082007) B2082007
theorem B7402691 : Blo 1949435 7402691 := bstep (se 1 (by rfl) ⟨5552018, by rfl⟩ : syracuseStep 7402691 = 11104037) B11104037
theorem B4935127 : Blo 1949435 4935127 := bstep (se 1 (by rfl) ⟨3701345, by rfl⟩ : syracuseStep 4935127 = 7402691) B7402691
theorem B6580169 : Blo 1949435 6580169 := bstep (se 2 (by rfl) ⟨2467563, by rfl⟩ : syracuseStep 6580169 = 4935127) B4935127
theorem B4386779 : Blo 1949435 4386779 := bstep (se 1 (by rfl) ⟨3290084, by rfl⟩ : syracuseStep 4386779 = 6580169) B6580169
theorem B2924519 : Blo 1949435 2924519 := bstep (se 1 (by rfl) ⟨2193389, by rfl⟩ : syracuseStep 2924519 = 4386779) B4386779
theorem B1949679 : Blo 1949435 1949679 := bstep (se 1 (by rfl) ⟨1462259, by rfl⟩ : syracuseStep 1949679 = 2924519) B2924519
theorem B2924525 : Blo 1949435 2924525 := bbase (se 3 (by rfl) ⟨548348, by rfl⟩ : syracuseStep 2924525 = 1096697) (by norm_num)
theorem B1949683 : Blo 1949435 1949683 := bstep (se 1 (by rfl) ⟨1462262, by rfl⟩ : syracuseStep 1949683 = 2924525) B2924525
theorem B4386797 : Blo 1949435 4386797 := bbase (se 3 (by rfl) ⟨822524, by rfl⟩ : syracuseStep 4386797 = 1645049) (by norm_num)
theorem B2924531 : Blo 1949435 2924531 := bstep (se 1 (by rfl) ⟨2193398, by rfl⟩ : syracuseStep 2924531 = 4386797) B4386797
theorem B1949687 : Blo 1949435 1949687 := bstep (se 1 (by rfl) ⟨1462265, by rfl⟩ : syracuseStep 1949687 = 2924531) B2924531
theorem B7026821 : Blo 1949435 7026821 := bbase (se 4 (by rfl) ⟨658764, by rfl⟩ : syracuseStep 7026821 = 1317529) (by norm_num)
theorem B4684547 : Blo 1949435 4684547 := bstep (se 1 (by rfl) ⟨3513410, by rfl⟩ : syracuseStep 4684547 = 7026821) B7026821
theorem B3123031 : Blo 1949435 3123031 := bstep (se 1 (by rfl) ⟨2342273, by rfl⟩ : syracuseStep 3123031 = 4684547) B4684547
theorem B4164041 : Blo 1949435 4164041 := bstep (se 2 (by rfl) ⟨1561515, by rfl⟩ : syracuseStep 4164041 = 3123031) B3123031
theorem B2776027 : Blo 1949435 2776027 := bstep (se 1 (by rfl) ⟨2082020, by rfl⟩ : syracuseStep 2776027 = 4164041) B4164041
theorem B3701369 : Blo 1949435 3701369 := bstep (se 2 (by rfl) ⟨1388013, by rfl⟩ : syracuseStep 3701369 = 2776027) B2776027
theorem B2467579 : Blo 1949435 2467579 := bstep (se 1 (by rfl) ⟨1850684, by rfl⟩ : syracuseStep 2467579 = 3701369) B3701369
theorem B3290105 : Blo 1949435 3290105 := bstep (se 2 (by rfl) ⟨1233789, by rfl⟩ : syracuseStep 3290105 = 2467579) B2467579
theorem B2193403 : Blo 1949435 2193403 := bstep (se 1 (by rfl) ⟨1645052, by rfl⟩ : syracuseStep 2193403 = 3290105) B3290105
theorem B2924537 : Blo 1949435 2924537 := bstep (se 2 (by rfl) ⟨1096701, by rfl⟩ : syracuseStep 2924537 = 2193403) B2193403
theorem B1949691 : Blo 1949435 1949691 := bstep (se 1 (by rfl) ⟨1462268, by rfl⟩ : syracuseStep 1949691 = 2924537) B2924537
theorem B7219877 : Blo 1949435 7219877 := bbase (se 4 (by rfl) ⟨676863, by rfl⟩ : syracuseStep 7219877 = 1353727) (by norm_num)
theorem B19253005 : Blo 1949435 19253005 := bstep (se 3 (by rfl) ⟨3609938, by rfl⟩ : syracuseStep 19253005 = 7219877) B7219877
theorem B102682693 : Blo 1949435 102682693 := bstep (se 4 (by rfl) ⟨9626502, by rfl⟩ : syracuseStep 102682693 = 19253005) B19253005
theorem B136910257 : Blo 1949435 136910257 := bstep (se 2 (by rfl) ⟨51341346, by rfl⟩ : syracuseStep 136910257 = 102682693) B102682693
theorem B730188037 : Blo 1949435 730188037 := bstep (se 4 (by rfl) ⟨68455128, by rfl⟩ : syracuseStep 730188037 = 136910257) B136910257
theorem B973584049 : Blo 1949435 973584049 := bstep (se 2 (by rfl) ⟨365094018, by rfl⟩ : syracuseStep 973584049 = 730188037) B730188037
theorem B1298112065 : Blo 1949435 1298112065 := bstep (se 2 (by rfl) ⟨486792024, by rfl⟩ : syracuseStep 1298112065 = 973584049) B973584049
theorem B865408043 : Blo 1949435 865408043 := bstep (se 1 (by rfl) ⟨649056032, by rfl⟩ : syracuseStep 865408043 = 1298112065) B1298112065
theorem B576938695 : Blo 1949435 576938695 := bstep (se 1 (by rfl) ⟨432704021, by rfl⟩ : syracuseStep 576938695 = 865408043) B865408043
theorem B769251593 : Blo 1949435 769251593 := bstep (se 2 (by rfl) ⟨288469347, by rfl⟩ : syracuseStep 769251593 = 576938695) B576938695
theorem B2051337581 : Blo 1949435 2051337581 := bstep (se 3 (by rfl) ⟨384625796, by rfl⟩ : syracuseStep 2051337581 = 769251593) B769251593
theorem B1367558387 : Blo 1949435 1367558387 := bstep (se 1 (by rfl) ⟨1025668790, by rfl⟩ : syracuseStep 1367558387 = 2051337581) B2051337581
theorem B911705591 : Blo 1949435 911705591 := bstep (se 1 (by rfl) ⟨683779193, by rfl⟩ : syracuseStep 911705591 = 1367558387) B1367558387
theorem B2431214909 : Blo 1949435 2431214909 := bstep (se 3 (by rfl) ⟨455852795, by rfl⟩ : syracuseStep 2431214909 = 911705591) B911705591
theorem B1620809939 : Blo 1949435 1620809939 := bstep (se 1 (by rfl) ⟨1215607454, by rfl⟩ : syracuseStep 1620809939 = 2431214909) B2431214909
theorem B1080539959 : Blo 1949435 1080539959 := bstep (se 1 (by rfl) ⟨810404969, by rfl⟩ : syracuseStep 1080539959 = 1620809939) B1620809939
theorem B1440719945 : Blo 1949435 1440719945 := bstep (se 2 (by rfl) ⟨540269979, by rfl⟩ : syracuseStep 1440719945 = 1080539959) B1080539959
theorem B960479963 : Blo 1949435 960479963 := bstep (se 1 (by rfl) ⟨720359972, by rfl⟩ : syracuseStep 960479963 = 1440719945) B1440719945
theorem B640319975 : Blo 1949435 640319975 := bstep (se 1 (by rfl) ⟨480239981, by rfl⟩ : syracuseStep 640319975 = 960479963) B960479963
theorem B426879983 : Blo 1949435 426879983 := bstep (se 1 (by rfl) ⟨320159987, by rfl⟩ : syracuseStep 426879983 = 640319975) B640319975
theorem B284586655 : Blo 1949435 284586655 := bstep (se 1 (by rfl) ⟨213439991, by rfl⟩ : syracuseStep 284586655 = 426879983) B426879983
theorem B379448873 : Blo 1949435 379448873 := bstep (se 2 (by rfl) ⟨142293327, by rfl⟩ : syracuseStep 379448873 = 284586655) B284586655
theorem B252965915 : Blo 1949435 252965915 := bstep (se 1 (by rfl) ⟨189724436, by rfl⟩ : syracuseStep 252965915 = 379448873) B379448873
theorem B168643943 : Blo 1949435 168643943 := bstep (se 1 (by rfl) ⟨126482957, by rfl⟩ : syracuseStep 168643943 = 252965915) B252965915
theorem B112429295 : Blo 1949435 112429295 := bstep (se 1 (by rfl) ⟨84321971, by rfl⟩ : syracuseStep 112429295 = 168643943) B168643943
theorem B74952863 : Blo 1949435 74952863 := bstep (se 1 (by rfl) ⟨56214647, by rfl⟩ : syracuseStep 74952863 = 112429295) B112429295
theorem B49968575 : Blo 1949435 49968575 := bstep (se 1 (by rfl) ⟨37476431, by rfl⟩ : syracuseStep 49968575 = 74952863) B74952863
theorem B33312383 : Blo 1949435 33312383 := bstep (se 1 (by rfl) ⟨24984287, by rfl⟩ : syracuseStep 33312383 = 49968575) B49968575
theorem B22208255 : Blo 1949435 22208255 := bstep (se 1 (by rfl) ⟨16656191, by rfl⟩ : syracuseStep 22208255 = 33312383) B33312383
theorem B14805503 : Blo 1949435 14805503 := bstep (se 1 (by rfl) ⟨11104127, by rfl⟩ : syracuseStep 14805503 = 22208255) B22208255
theorem B9870335 : Blo 1949435 9870335 := bstep (se 1 (by rfl) ⟨7402751, by rfl⟩ : syracuseStep 9870335 = 14805503) B14805503
theorem B6580223 : Blo 1949435 6580223 := bstep (se 1 (by rfl) ⟨4935167, by rfl⟩ : syracuseStep 6580223 = 9870335) B9870335
theorem B4386815 : Blo 1949435 4386815 := bstep (se 1 (by rfl) ⟨3290111, by rfl⟩ : syracuseStep 4386815 = 6580223) B6580223
theorem B2924543 : Blo 1949435 2924543 := bstep (se 1 (by rfl) ⟨2193407, by rfl⟩ : syracuseStep 2924543 = 4386815) B4386815
theorem B1949695 : Blo 1949435 1949695 := bstep (se 1 (by rfl) ⟨1462271, by rfl⟩ : syracuseStep 1949695 = 2924543) B2924543
theorem B2924549 : Blo 1949435 2924549 := bbase (se 4 (by rfl) ⟨274176, by rfl⟩ : syracuseStep 2924549 = 548353) (by norm_num)
theorem B1949699 : Blo 1949435 1949699 := bstep (se 1 (by rfl) ⟨1462274, by rfl⟩ : syracuseStep 1949699 = 2924549) B2924549
theorem B3290125 : Blo 1949435 3290125 := bbase (se 3 (by rfl) ⟨616898, by rfl⟩ : syracuseStep 3290125 = 1233797) (by norm_num)
theorem B4386833 : Blo 1949435 4386833 := bstep (se 2 (by rfl) ⟨1645062, by rfl⟩ : syracuseStep 4386833 = 3290125) B3290125
theorem B2924555 : Blo 1949435 2924555 := bstep (se 1 (by rfl) ⟨2193416, by rfl⟩ : syracuseStep 2924555 = 4386833) B4386833
theorem B1949703 : Blo 1949435 1949703 := bstep (se 1 (by rfl) ⟨1462277, by rfl⟩ : syracuseStep 1949703 = 2924555) B2924555
theorem B2193421 : Blo 1949435 2193421 := bbase (se 3 (by rfl) ⟨411266, by rfl⟩ : syracuseStep 2193421 = 822533) (by norm_num)
theorem B2924561 : Blo 1949435 2924561 := bstep (se 2 (by rfl) ⟨1096710, by rfl⟩ : syracuseStep 2924561 = 2193421) B2193421
theorem B1949707 : Blo 1949435 1949707 := bstep (se 1 (by rfl) ⟨1462280, by rfl⟩ : syracuseStep 1949707 = 2924561) B2924561
theorem B6580277 : Blo 1949435 6580277 := bbase (se 5 (by rfl) ⟨308450, by rfl⟩ : syracuseStep 6580277 = 616901) (by norm_num)
theorem B4386851 : Blo 1949435 4386851 := bstep (se 1 (by rfl) ⟨3290138, by rfl⟩ : syracuseStep 4386851 = 6580277) B6580277
theorem B2924567 : Blo 1949435 2924567 := bstep (se 1 (by rfl) ⟨2193425, by rfl⟩ : syracuseStep 2924567 = 4386851) B4386851
theorem B1949711 : Blo 1949435 1949711 := bstep (se 1 (by rfl) ⟨1462283, by rfl⟩ : syracuseStep 1949711 = 2924567) B2924567
theorem B2924573 : Blo 1949435 2924573 := bbase (se 3 (by rfl) ⟨548357, by rfl⟩ : syracuseStep 2924573 = 1096715) (by norm_num)
theorem B1949715 : Blo 1949435 1949715 := bstep (se 1 (by rfl) ⟨1462286, by rfl⟩ : syracuseStep 1949715 = 2924573) B2924573
theorem B4386869 : Blo 1949435 4386869 := bbase (se 5 (by rfl) ⟨205634, by rfl⟩ : syracuseStep 4386869 = 411269) (by norm_num)
theorem B2924579 : Blo 1949435 2924579 := bstep (se 1 (by rfl) ⟨2193434, by rfl⟩ : syracuseStep 2924579 = 4386869) B4386869
theorem B1949719 : Blo 1949435 1949719 := bstep (se 1 (by rfl) ⟨1462289, by rfl⟩ : syracuseStep 1949719 = 2924579) B2924579
theorem B4446733 : Blo 1949435 4446733 := bbase (se 3 (by rfl) ⟨833762, by rfl⟩ : syracuseStep 4446733 = 1667525) (by norm_num)
theorem B5928977 : Blo 1949435 5928977 := bstep (se 2 (by rfl) ⟨2223366, by rfl⟩ : syracuseStep 5928977 = 4446733) B4446733
theorem B3952651 : Blo 1949435 3952651 := bstep (se 1 (by rfl) ⟨2964488, by rfl⟩ : syracuseStep 3952651 = 5928977) B5928977
theorem B5270201 : Blo 1949435 5270201 := bstep (se 2 (by rfl) ⟨1976325, by rfl⟩ : syracuseStep 5270201 = 3952651) B3952651
theorem B3513467 : Blo 1949435 3513467 := bstep (se 1 (by rfl) ⟨2635100, by rfl⟩ : syracuseStep 3513467 = 5270201) B5270201
theorem B9369245 : Blo 1949435 9369245 := bstep (se 3 (by rfl) ⟨1756733, by rfl⟩ : syracuseStep 9369245 = 3513467) B3513467
theorem B6246163 : Blo 1949435 6246163 := bstep (se 1 (by rfl) ⟨4684622, by rfl⟩ : syracuseStep 6246163 = 9369245) B9369245
theorem B8328217 : Blo 1949435 8328217 := bstep (se 2 (by rfl) ⟨3123081, by rfl⟩ : syracuseStep 8328217 = 6246163) B6246163
theorem B11104289 : Blo 1949435 11104289 := bstep (se 2 (by rfl) ⟨4164108, by rfl⟩ : syracuseStep 11104289 = 8328217) B8328217
theorem B7402859 : Blo 1949435 7402859 := bstep (se 1 (by rfl) ⟨5552144, by rfl⟩ : syracuseStep 7402859 = 11104289) B11104289
theorem B4935239 : Blo 1949435 4935239 := bstep (se 1 (by rfl) ⟨3701429, by rfl⟩ : syracuseStep 4935239 = 7402859) B7402859
theorem B3290159 : Blo 1949435 3290159 := bstep (se 1 (by rfl) ⟨2467619, by rfl⟩ : syracuseStep 3290159 = 4935239) B4935239
theorem B2193439 : Blo 1949435 2193439 := bstep (se 1 (by rfl) ⟨1645079, by rfl⟩ : syracuseStep 2193439 = 3290159) B3290159
theorem B2924585 : Blo 1949435 2924585 := bstep (se 2 (by rfl) ⟨1096719, by rfl⟩ : syracuseStep 2924585 = 2193439) B2193439
theorem B1949723 : Blo 1949435 1949723 := bstep (se 1 (by rfl) ⟨1462292, by rfl⟩ : syracuseStep 1949723 = 2924585) B2924585
theorem B9497093 : Blo 1949435 9497093 := bbase (se 4 (by rfl) ⟨890352, by rfl⟩ : syracuseStep 9497093 = 1780705) (by norm_num)
theorem B25325581 : Blo 1949435 25325581 := bstep (se 3 (by rfl) ⟨4748546, by rfl⟩ : syracuseStep 25325581 = 9497093) B9497093
theorem B33767441 : Blo 1949435 33767441 := bstep (se 2 (by rfl) ⟨12662790, by rfl⟩ : syracuseStep 33767441 = 25325581) B25325581
theorem B22511627 : Blo 1949435 22511627 := bstep (se 1 (by rfl) ⟨16883720, by rfl⟩ : syracuseStep 22511627 = 33767441) B33767441
theorem B15007751 : Blo 1949435 15007751 := bstep (se 1 (by rfl) ⟨11255813, by rfl⟩ : syracuseStep 15007751 = 22511627) B22511627
theorem B10005167 : Blo 1949435 10005167 := bstep (se 1 (by rfl) ⟨7503875, by rfl⟩ : syracuseStep 10005167 = 15007751) B15007751
theorem B6670111 : Blo 1949435 6670111 := bstep (se 1 (by rfl) ⟨5002583, by rfl⟩ : syracuseStep 6670111 = 10005167) B10005167
theorem B8893481 : Blo 1949435 8893481 := bstep (se 2 (by rfl) ⟨3335055, by rfl⟩ : syracuseStep 8893481 = 6670111) B6670111
theorem B23715949 : Blo 1949435 23715949 := bstep (se 3 (by rfl) ⟨4446740, by rfl⟩ : syracuseStep 23715949 = 8893481) B8893481
theorem B31621265 : Blo 1949435 31621265 := bstep (se 2 (by rfl) ⟨11857974, by rfl⟩ : syracuseStep 31621265 = 23715949) B23715949
theorem B21080843 : Blo 1949435 21080843 := bstep (se 1 (by rfl) ⟨15810632, by rfl⟩ : syracuseStep 21080843 = 31621265) B31621265
theorem B14053895 : Blo 1949435 14053895 := bstep (se 1 (by rfl) ⟨10540421, by rfl⟩ : syracuseStep 14053895 = 21080843) B21080843
theorem B9369263 : Blo 1949435 9369263 := bstep (se 1 (by rfl) ⟨7026947, by rfl⟩ : syracuseStep 9369263 = 14053895) B14053895
theorem B6246175 : Blo 1949435 6246175 := bstep (se 1 (by rfl) ⟨4684631, by rfl⟩ : syracuseStep 6246175 = 9369263) B9369263
theorem B8328233 : Blo 1949435 8328233 := bstep (se 2 (by rfl) ⟨3123087, by rfl⟩ : syracuseStep 8328233 = 6246175) B6246175
theorem B5552155 : Blo 1949435 5552155 := bstep (se 1 (by rfl) ⟨4164116, by rfl⟩ : syracuseStep 5552155 = 8328233) B8328233
theorem B7402873 : Blo 1949435 7402873 := bstep (se 2 (by rfl) ⟨2776077, by rfl⟩ : syracuseStep 7402873 = 5552155) B5552155
theorem B9870497 : Blo 1949435 9870497 := bstep (se 2 (by rfl) ⟨3701436, by rfl⟩ : syracuseStep 9870497 = 7402873) B7402873
theorem B6580331 : Blo 1949435 6580331 := bstep (se 1 (by rfl) ⟨4935248, by rfl⟩ : syracuseStep 6580331 = 9870497) B9870497
theorem B4386887 : Blo 1949435 4386887 := bstep (se 1 (by rfl) ⟨3290165, by rfl⟩ : syracuseStep 4386887 = 6580331) B6580331
theorem B2924591 : Blo 1949435 2924591 := bstep (se 1 (by rfl) ⟨2193443, by rfl⟩ : syracuseStep 2924591 = 4386887) B4386887
theorem B1949727 : Blo 1949435 1949727 := bstep (se 1 (by rfl) ⟨1462295, by rfl⟩ : syracuseStep 1949727 = 2924591) B2924591
theorem B2924597 : Blo 1949435 2924597 := bbase (se 5 (by rfl) ⟨137090, by rfl⟩ : syracuseStep 2924597 = 274181) (by norm_num)
theorem B1949731 : Blo 1949435 1949731 := bstep (se 1 (by rfl) ⟨1462298, by rfl⟩ : syracuseStep 1949731 = 2924597) B2924597
theorem B4935269 : Blo 1949435 4935269 := bbase (se 4 (by rfl) ⟨462681, by rfl⟩ : syracuseStep 4935269 = 925363) (by norm_num)
theorem B3290179 : Blo 1949435 3290179 := bstep (se 1 (by rfl) ⟨2467634, by rfl⟩ : syracuseStep 3290179 = 4935269) B4935269
theorem B4386905 : Blo 1949435 4386905 := bstep (se 2 (by rfl) ⟨1645089, by rfl⟩ : syracuseStep 4386905 = 3290179) B3290179
theorem B2924603 : Blo 1949435 2924603 := bstep (se 1 (by rfl) ⟨2193452, by rfl⟩ : syracuseStep 2924603 = 4386905) B4386905
theorem B1949735 : Blo 1949435 1949735 := bstep (se 1 (by rfl) ⟨1462301, by rfl⟩ : syracuseStep 1949735 = 2924603) B2924603
theorem B2193457 : Blo 1949435 2193457 := bbase (se 2 (by rfl) ⟨822546, by rfl⟩ : syracuseStep 2193457 = 1645093) (by norm_num)
theorem B2924609 : Blo 1949435 2924609 := bstep (se 2 (by rfl) ⟨1096728, by rfl⟩ : syracuseStep 2924609 = 2193457) B2193457
theorem B1949739 : Blo 1949435 1949739 := bstep (se 1 (by rfl) ⟨1462304, by rfl⟩ : syracuseStep 1949739 = 2924609) B2924609
theorem B9497173 : Blo 1949435 9497173 := bbase (se 8 (by rfl) ⟨55647, by rfl⟩ : syracuseStep 9497173 = 111295) (by norm_num)
theorem B12662897 : Blo 1949435 12662897 := bstep (se 2 (by rfl) ⟨4748586, by rfl⟩ : syracuseStep 12662897 = 9497173) B9497173
theorem B33767725 : Blo 1949435 33767725 := bstep (se 3 (by rfl) ⟨6331448, by rfl⟩ : syracuseStep 33767725 = 12662897) B12662897
theorem B45023633 : Blo 1949435 45023633 := bstep (se 2 (by rfl) ⟨16883862, by rfl⟩ : syracuseStep 45023633 = 33767725) B33767725
theorem B30015755 : Blo 1949435 30015755 := bstep (se 1 (by rfl) ⟨22511816, by rfl⟩ : syracuseStep 30015755 = 45023633) B45023633
theorem B20010503 : Blo 1949435 20010503 := bstep (se 1 (by rfl) ⟨15007877, by rfl⟩ : syracuseStep 20010503 = 30015755) B30015755
theorem B13340335 : Blo 1949435 13340335 := bstep (se 1 (by rfl) ⟨10005251, by rfl⟩ : syracuseStep 13340335 = 20010503) B20010503
theorem B17787113 : Blo 1949435 17787113 := bstep (se 2 (by rfl) ⟨6670167, by rfl⟩ : syracuseStep 17787113 = 13340335) B13340335
theorem B11858075 : Blo 1949435 11858075 := bstep (se 1 (by rfl) ⟨8893556, by rfl⟩ : syracuseStep 11858075 = 17787113) B17787113
theorem B7905383 : Blo 1949435 7905383 := bstep (se 1 (by rfl) ⟨5929037, by rfl⟩ : syracuseStep 7905383 = 11858075) B11858075
theorem B5270255 : Blo 1949435 5270255 := bstep (se 1 (by rfl) ⟨3952691, by rfl⟩ : syracuseStep 5270255 = 7905383) B7905383
theorem B3513503 : Blo 1949435 3513503 := bstep (se 1 (by rfl) ⟨2635127, by rfl⟩ : syracuseStep 3513503 = 5270255) B5270255
theorem B9369341 : Blo 1949435 9369341 := bstep (se 3 (by rfl) ⟨1756751, by rfl⟩ : syracuseStep 9369341 = 3513503) B3513503
theorem B6246227 : Blo 1949435 6246227 := bstep (se 1 (by rfl) ⟨4684670, by rfl⟩ : syracuseStep 6246227 = 9369341) B9369341
theorem B4164151 : Blo 1949435 4164151 := bstep (se 1 (by rfl) ⟨3123113, by rfl⟩ : syracuseStep 4164151 = 6246227) B6246227
theorem B5552201 : Blo 1949435 5552201 := bstep (se 2 (by rfl) ⟨2082075, by rfl⟩ : syracuseStep 5552201 = 4164151) B4164151
theorem B3701467 : Blo 1949435 3701467 := bstep (se 1 (by rfl) ⟨2776100, by rfl⟩ : syracuseStep 3701467 = 5552201) B5552201
theorem B4935289 : Blo 1949435 4935289 := bstep (se 2 (by rfl) ⟨1850733, by rfl⟩ : syracuseStep 4935289 = 3701467) B3701467
theorem B6580385 : Blo 1949435 6580385 := bstep (se 2 (by rfl) ⟨2467644, by rfl⟩ : syracuseStep 6580385 = 4935289) B4935289
theorem B4386923 : Blo 1949435 4386923 := bstep (se 1 (by rfl) ⟨3290192, by rfl⟩ : syracuseStep 4386923 = 6580385) B6580385
theorem B2924615 : Blo 1949435 2924615 := bstep (se 1 (by rfl) ⟨2193461, by rfl⟩ : syracuseStep 2924615 = 4386923) B4386923
theorem B1949743 : Blo 1949435 1949743 := bstep (se 1 (by rfl) ⟨1462307, by rfl⟩ : syracuseStep 1949743 = 2924615) B2924615
theorem B2924621 : Blo 1949435 2924621 := bbase (se 3 (by rfl) ⟨548366, by rfl⟩ : syracuseStep 2924621 = 1096733) (by norm_num)
theorem B1949747 : Blo 1949435 1949747 := bstep (se 1 (by rfl) ⟨1462310, by rfl⟩ : syracuseStep 1949747 = 2924621) B2924621
theorem B4386941 : Blo 1949435 4386941 := bbase (se 3 (by rfl) ⟨822551, by rfl⟩ : syracuseStep 4386941 = 1645103) (by norm_num)
theorem B2924627 : Blo 1949435 2924627 := bstep (se 1 (by rfl) ⟨2193470, by rfl⟩ : syracuseStep 2924627 = 4386941) B4386941
theorem B1949751 : Blo 1949435 1949751 := bstep (se 1 (by rfl) ⟨1462313, by rfl⟩ : syracuseStep 1949751 = 2924627) B2924627
theorem B3290213 : Blo 1949435 3290213 := bbase (se 4 (by rfl) ⟨308457, by rfl⟩ : syracuseStep 3290213 = 616915) (by norm_num)
theorem B2193475 : Blo 1949435 2193475 := bstep (se 1 (by rfl) ⟨1645106, by rfl⟩ : syracuseStep 2193475 = 3290213) B3290213
theorem B2924633 : Blo 1949435 2924633 := bstep (se 2 (by rfl) ⟨1096737, by rfl⟩ : syracuseStep 2924633 = 2193475) B2193475
theorem B1949755 : Blo 1949435 1949755 := bstep (se 1 (by rfl) ⟨1462316, by rfl⟩ : syracuseStep 1949755 = 2924633) B2924633
theorem B4684709 : Blo 1949435 4684709 := bbase (se 4 (by rfl) ⟨439191, by rfl⟩ : syracuseStep 4684709 = 878383) (by norm_num)
theorem B3123139 : Blo 1949435 3123139 := bstep (se 1 (by rfl) ⟨2342354, by rfl⟩ : syracuseStep 3123139 = 4684709) B4684709
theorem B4164185 : Blo 1949435 4164185 := bstep (se 2 (by rfl) ⟨1561569, by rfl⟩ : syracuseStep 4164185 = 3123139) B3123139
theorem B2776123 : Blo 1949435 2776123 := bstep (se 1 (by rfl) ⟨2082092, by rfl⟩ : syracuseStep 2776123 = 4164185) B4164185
theorem B14805989 : Blo 1949435 14805989 := bstep (se 4 (by rfl) ⟨1388061, by rfl⟩ : syracuseStep 14805989 = 2776123) B2776123
theorem B9870659 : Blo 1949435 9870659 := bstep (se 1 (by rfl) ⟨7402994, by rfl⟩ : syracuseStep 9870659 = 14805989) B14805989
theorem B6580439 : Blo 1949435 6580439 := bstep (se 1 (by rfl) ⟨4935329, by rfl⟩ : syracuseStep 6580439 = 9870659) B9870659
theorem B4386959 : Blo 1949435 4386959 := bstep (se 1 (by rfl) ⟨3290219, by rfl⟩ : syracuseStep 4386959 = 6580439) B6580439
theorem B2924639 : Blo 1949435 2924639 := bstep (se 1 (by rfl) ⟨2193479, by rfl⟩ : syracuseStep 2924639 = 4386959) B4386959
theorem B1949759 : Blo 1949435 1949759 := bstep (se 1 (by rfl) ⟨1462319, by rfl⟩ : syracuseStep 1949759 = 2924639) B2924639
theorem B2924645 : Blo 1949435 2924645 := bbase (se 4 (by rfl) ⟨274185, by rfl⟩ : syracuseStep 2924645 = 548371) (by norm_num)
theorem B1949763 : Blo 1949435 1949763 := bstep (se 1 (by rfl) ⟨1462322, by rfl⟩ : syracuseStep 1949763 = 2924645) B2924645
theorem B3952741 : Blo 1949435 3952741 := bbase (se 4 (by rfl) ⟨370569, by rfl⟩ : syracuseStep 3952741 = 741139) (by norm_num)
theorem B5270321 : Blo 1949435 5270321 := bstep (se 2 (by rfl) ⟨1976370, by rfl⟩ : syracuseStep 5270321 = 3952741) B3952741
theorem B3513547 : Blo 1949435 3513547 := bstep (se 1 (by rfl) ⟨2635160, by rfl⟩ : syracuseStep 3513547 = 5270321) B5270321
theorem B4684729 : Blo 1949435 4684729 := bstep (se 2 (by rfl) ⟨1756773, by rfl⟩ : syracuseStep 4684729 = 3513547) B3513547
theorem B6246305 : Blo 1949435 6246305 := bstep (se 2 (by rfl) ⟨2342364, by rfl⟩ : syracuseStep 6246305 = 4684729) B4684729
theorem B4164203 : Blo 1949435 4164203 := bstep (se 1 (by rfl) ⟨3123152, by rfl⟩ : syracuseStep 4164203 = 6246305) B6246305
theorem B2776135 : Blo 1949435 2776135 := bstep (se 1 (by rfl) ⟨2082101, by rfl⟩ : syracuseStep 2776135 = 4164203) B4164203
theorem B3701513 : Blo 1949435 3701513 := bstep (se 2 (by rfl) ⟨1388067, by rfl⟩ : syracuseStep 3701513 = 2776135) B2776135
theorem B2467675 : Blo 1949435 2467675 := bstep (se 1 (by rfl) ⟨1850756, by rfl⟩ : syracuseStep 2467675 = 3701513) B3701513
theorem B3290233 : Blo 1949435 3290233 := bstep (se 2 (by rfl) ⟨1233837, by rfl⟩ : syracuseStep 3290233 = 2467675) B2467675
theorem B4386977 : Blo 1949435 4386977 := bstep (se 2 (by rfl) ⟨1645116, by rfl⟩ : syracuseStep 4386977 = 3290233) B3290233
theorem B2924651 : Blo 1949435 2924651 := bstep (se 1 (by rfl) ⟨2193488, by rfl⟩ : syracuseStep 2924651 = 4386977) B4386977
theorem B1949767 : Blo 1949435 1949767 := bstep (se 1 (by rfl) ⟨1462325, by rfl⟩ : syracuseStep 1949767 = 2924651) B2924651
theorem B2193493 : Blo 1949435 2193493 := bbase (se 8 (by rfl) ⟨12852, by rfl⟩ : syracuseStep 2193493 = 25705) (by norm_num)
theorem B2924657 : Blo 1949435 2924657 := bstep (se 2 (by rfl) ⟨1096746, by rfl⟩ : syracuseStep 2924657 = 2193493) B2193493
theorem B1949771 : Blo 1949435 1949771 := bstep (se 1 (by rfl) ⟨1462328, by rfl⟩ : syracuseStep 1949771 = 2924657) B2924657
theorem B2467685 : Blo 1949435 2467685 := bbase (se 4 (by rfl) ⟨231345, by rfl⟩ : syracuseStep 2467685 = 462691) (by norm_num)
theorem B6580493 : Blo 1949435 6580493 := bstep (se 3 (by rfl) ⟨1233842, by rfl⟩ : syracuseStep 6580493 = 2467685) B2467685
theorem B4386995 : Blo 1949435 4386995 := bstep (se 1 (by rfl) ⟨3290246, by rfl⟩ : syracuseStep 4386995 = 6580493) B6580493
theorem B2924663 : Blo 1949435 2924663 := bstep (se 1 (by rfl) ⟨2193497, by rfl⟩ : syracuseStep 2924663 = 4386995) B4386995
theorem B1949775 : Blo 1949435 1949775 := bstep (se 1 (by rfl) ⟨1462331, by rfl⟩ : syracuseStep 1949775 = 2924663) B2924663
theorem B2924669 : Blo 1949435 2924669 := bbase (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) (by norm_num)
theorem B1949779 : Blo 1949435 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B4387013 : Blo 1949435 4387013 := bbase (se 4 (by rfl) ⟨411282, by rfl⟩ : syracuseStep 4387013 = 822565) (by norm_num)
theorem B2924675 : Blo 1949435 2924675 := bstep (se 1 (by rfl) ⟨2193506, by rfl⟩ : syracuseStep 2924675 = 4387013) B4387013
theorem B1949783 : Blo 1949435 1949783 := bstep (se 1 (by rfl) ⟨1462337, by rfl⟩ : syracuseStep 1949783 = 2924675) B2924675
theorem B3952781 : Blo 1949435 3952781 := bbase (se 3 (by rfl) ⟨741146, by rfl⟩ : syracuseStep 3952781 = 1482293) (by norm_num)
theorem B2635187 : Blo 1949435 2635187 := bstep (se 1 (by rfl) ⟨1976390, by rfl⟩ : syracuseStep 2635187 = 3952781) B3952781
theorem B7027165 : Blo 1949435 7027165 := bstep (se 3 (by rfl) ⟨1317593, by rfl⟩ : syracuseStep 7027165 = 2635187) B2635187
theorem B9369553 : Blo 1949435 9369553 := bstep (se 2 (by rfl) ⟨3513582, by rfl⟩ : syracuseStep 9369553 = 7027165) B7027165
theorem B12492737 : Blo 1949435 12492737 := bstep (se 2 (by rfl) ⟨4684776, by rfl⟩ : syracuseStep 12492737 = 9369553) B9369553
theorem B8328491 : Blo 1949435 8328491 := bstep (se 1 (by rfl) ⟨6246368, by rfl⟩ : syracuseStep 8328491 = 12492737) B12492737
theorem B5552327 : Blo 1949435 5552327 := bstep (se 1 (by rfl) ⟨4164245, by rfl⟩ : syracuseStep 5552327 = 8328491) B8328491
theorem B3701551 : Blo 1949435 3701551 := bstep (se 1 (by rfl) ⟨2776163, by rfl⟩ : syracuseStep 3701551 = 5552327) B5552327
theorem B4935401 : Blo 1949435 4935401 := bstep (se 2 (by rfl) ⟨1850775, by rfl⟩ : syracuseStep 4935401 = 3701551) B3701551
theorem B3290267 : Blo 1949435 3290267 := bstep (se 1 (by rfl) ⟨2467700, by rfl⟩ : syracuseStep 3290267 = 4935401) B4935401
theorem B2193511 : Blo 1949435 2193511 := bstep (se 1 (by rfl) ⟨1645133, by rfl⟩ : syracuseStep 2193511 = 3290267) B3290267
theorem B2924681 : Blo 1949435 2924681 := bstep (se 2 (by rfl) ⟨1096755, by rfl⟩ : syracuseStep 2924681 = 2193511) B2193511
theorem B1949787 : Blo 1949435 1949787 := bstep (se 1 (by rfl) ⟨1462340, by rfl⟩ : syracuseStep 1949787 = 2924681) B2924681
theorem B9870821 : Blo 1949435 9870821 := bbase (se 4 (by rfl) ⟨925389, by rfl⟩ : syracuseStep 9870821 = 1850779) (by norm_num)
theorem B6580547 : Blo 1949435 6580547 := bstep (se 1 (by rfl) ⟨4935410, by rfl⟩ : syracuseStep 6580547 = 9870821) B9870821
theorem B4387031 : Blo 1949435 4387031 := bstep (se 1 (by rfl) ⟨3290273, by rfl⟩ : syracuseStep 4387031 = 6580547) B6580547
theorem B2924687 : Blo 1949435 2924687 := bstep (se 1 (by rfl) ⟨2193515, by rfl⟩ : syracuseStep 2924687 = 4387031) B4387031
theorem B1949791 : Blo 1949435 1949791 := bstep (se 1 (by rfl) ⟨1462343, by rfl⟩ : syracuseStep 1949791 = 2924687) B2924687
theorem B2924693 : Blo 1949435 2924693 := bbase (se 6 (by rfl) ⟨68547, by rfl⟩ : syracuseStep 2924693 = 137095) (by norm_num)
theorem B1949795 : Blo 1949435 1949795 := bstep (se 1 (by rfl) ⟨1462346, by rfl⟩ : syracuseStep 1949795 = 2924693) B2924693
theorem B4684805 : Blo 1949435 4684805 := bbase (se 4 (by rfl) ⟨439200, by rfl⟩ : syracuseStep 4684805 = 878401) (by norm_num)
theorem B3123203 : Blo 1949435 3123203 := bstep (se 1 (by rfl) ⟨2342402, by rfl⟩ : syracuseStep 3123203 = 4684805) B4684805
theorem B8328541 : Blo 1949435 8328541 := bstep (se 3 (by rfl) ⟨1561601, by rfl⟩ : syracuseStep 8328541 = 3123203) B3123203
theorem B11104721 : Blo 1949435 11104721 := bstep (se 2 (by rfl) ⟨4164270, by rfl⟩ : syracuseStep 11104721 = 8328541) B8328541
theorem B7403147 : Blo 1949435 7403147 := bstep (se 1 (by rfl) ⟨5552360, by rfl⟩ : syracuseStep 7403147 = 11104721) B11104721
theorem B4935431 : Blo 1949435 4935431 := bstep (se 1 (by rfl) ⟨3701573, by rfl⟩ : syracuseStep 4935431 = 7403147) B7403147
theorem B3290287 : Blo 1949435 3290287 := bstep (se 1 (by rfl) ⟨2467715, by rfl⟩ : syracuseStep 3290287 = 4935431) B4935431
theorem B4387049 : Blo 1949435 4387049 := bstep (se 2 (by rfl) ⟨1645143, by rfl⟩ : syracuseStep 4387049 = 3290287) B3290287
theorem B2924699 : Blo 1949435 2924699 := bstep (se 1 (by rfl) ⟨2193524, by rfl⟩ : syracuseStep 2924699 = 4387049) B4387049
theorem B1949799 : Blo 1949435 1949799 := bstep (se 1 (by rfl) ⟨1462349, by rfl⟩ : syracuseStep 1949799 = 2924699) B2924699
theorem B2193529 : Blo 1949435 2193529 := bbase (se 2 (by rfl) ⟨822573, by rfl⟩ : syracuseStep 2193529 = 1645147) (by norm_num)
theorem B2924705 : Blo 1949435 2924705 := bstep (se 2 (by rfl) ⟨1096764, by rfl⟩ : syracuseStep 2924705 = 2193529) B2193529
theorem B1949803 : Blo 1949435 1949803 := bstep (se 1 (by rfl) ⟨1462352, by rfl⟩ : syracuseStep 1949803 = 2924705) B2924705
theorem B20284181 : Blo 1949435 20284181 := bbase (se 6 (by rfl) ⟨475410, by rfl⟩ : syracuseStep 20284181 = 950821) (by norm_num)
theorem B13522787 : Blo 1949435 13522787 := bstep (se 1 (by rfl) ⟨10142090, by rfl⟩ : syracuseStep 13522787 = 20284181) B20284181
theorem B9015191 : Blo 1949435 9015191 := bstep (se 1 (by rfl) ⟨6761393, by rfl⟩ : syracuseStep 9015191 = 13522787) B13522787
theorem B6010127 : Blo 1949435 6010127 := bstep (se 1 (by rfl) ⟨4507595, by rfl⟩ : syracuseStep 6010127 = 9015191) B9015191
theorem B4006751 : Blo 1949435 4006751 := bstep (se 1 (by rfl) ⟨3005063, by rfl⟩ : syracuseStep 4006751 = 6010127) B6010127
theorem B10684669 : Blo 1949435 10684669 := bstep (se 3 (by rfl) ⟨2003375, by rfl⟩ : syracuseStep 10684669 = 4006751) B4006751
theorem B14246225 : Blo 1949435 14246225 := bstep (se 2 (by rfl) ⟨5342334, by rfl⟩ : syracuseStep 14246225 = 10684669) B10684669
theorem B9497483 : Blo 1949435 9497483 := bstep (se 1 (by rfl) ⟨7123112, by rfl⟩ : syracuseStep 9497483 = 14246225) B14246225
theorem B6331655 : Blo 1949435 6331655 := bstep (se 1 (by rfl) ⟨4748741, by rfl⟩ : syracuseStep 6331655 = 9497483) B9497483
theorem B4221103 : Blo 1949435 4221103 := bstep (se 1 (by rfl) ⟨3165827, by rfl⟩ : syracuseStep 4221103 = 6331655) B6331655
theorem B5628137 : Blo 1949435 5628137 := bstep (se 2 (by rfl) ⟨2110551, by rfl⟩ : syracuseStep 5628137 = 4221103) B4221103
theorem B15008365 : Blo 1949435 15008365 := bstep (se 3 (by rfl) ⟨2814068, by rfl⟩ : syracuseStep 15008365 = 5628137) B5628137
theorem B20011153 : Blo 1949435 20011153 := bstep (se 2 (by rfl) ⟨7504182, by rfl⟩ : syracuseStep 20011153 = 15008365) B15008365
theorem B26681537 : Blo 1949435 26681537 := bstep (se 2 (by rfl) ⟨10005576, by rfl⟩ : syracuseStep 26681537 = 20011153) B20011153
theorem B17787691 : Blo 1949435 17787691 := bstep (se 1 (by rfl) ⟨13340768, by rfl⟩ : syracuseStep 17787691 = 26681537) B26681537
theorem B94867685 : Blo 1949435 94867685 := bstep (se 4 (by rfl) ⟨8893845, by rfl⟩ : syracuseStep 94867685 = 17787691) B17787691
theorem B63245123 : Blo 1949435 63245123 := bstep (se 1 (by rfl) ⟨47433842, by rfl⟩ : syracuseStep 63245123 = 94867685) B94867685
theorem B42163415 : Blo 1949435 42163415 := bstep (se 1 (by rfl) ⟨31622561, by rfl⟩ : syracuseStep 42163415 = 63245123) B63245123
theorem B28108943 : Blo 1949435 28108943 := bstep (se 1 (by rfl) ⟨21081707, by rfl⟩ : syracuseStep 28108943 = 42163415) B42163415
theorem B18739295 : Blo 1949435 18739295 := bstep (se 1 (by rfl) ⟨14054471, by rfl⟩ : syracuseStep 18739295 = 28108943) B28108943
theorem B12492863 : Blo 1949435 12492863 := bstep (se 1 (by rfl) ⟨9369647, by rfl⟩ : syracuseStep 12492863 = 18739295) B18739295
theorem B8328575 : Blo 1949435 8328575 := bstep (se 1 (by rfl) ⟨6246431, by rfl⟩ : syracuseStep 8328575 = 12492863) B12492863
theorem B5552383 : Blo 1949435 5552383 := bstep (se 1 (by rfl) ⟨4164287, by rfl⟩ : syracuseStep 5552383 = 8328575) B8328575
theorem B7403177 : Blo 1949435 7403177 := bstep (se 2 (by rfl) ⟨2776191, by rfl⟩ : syracuseStep 7403177 = 5552383) B5552383
theorem B4935451 : Blo 1949435 4935451 := bstep (se 1 (by rfl) ⟨3701588, by rfl⟩ : syracuseStep 4935451 = 7403177) B7403177
theorem B6580601 : Blo 1949435 6580601 := bstep (se 2 (by rfl) ⟨2467725, by rfl⟩ : syracuseStep 6580601 = 4935451) B4935451
theorem B4387067 : Blo 1949435 4387067 := bstep (se 1 (by rfl) ⟨3290300, by rfl⟩ : syracuseStep 4387067 = 6580601) B6580601
theorem B2924711 : Blo 1949435 2924711 := bstep (se 1 (by rfl) ⟨2193533, by rfl⟩ : syracuseStep 2924711 = 4387067) B4387067
theorem B1949807 : Blo 1949435 1949807 := bstep (se 1 (by rfl) ⟨1462355, by rfl⟩ : syracuseStep 1949807 = 2924711) B2924711
theorem B2924717 : Blo 1949435 2924717 := bbase (se 3 (by rfl) ⟨548384, by rfl⟩ : syracuseStep 2924717 = 1096769) (by norm_num)
theorem B1949811 : Blo 1949435 1949811 := bstep (se 1 (by rfl) ⟨1462358, by rfl⟩ : syracuseStep 1949811 = 2924717) B2924717
theorem B4387085 : Blo 1949435 4387085 := bbase (se 3 (by rfl) ⟨822578, by rfl⟩ : syracuseStep 4387085 = 1645157) (by norm_num)
theorem B2924723 : Blo 1949435 2924723 := bstep (se 1 (by rfl) ⟨2193542, by rfl⟩ : syracuseStep 2924723 = 4387085) B4387085
theorem B1949815 : Blo 1949435 1949815 := bstep (se 1 (by rfl) ⟨1462361, by rfl⟩ : syracuseStep 1949815 = 2924723) B2924723
theorem B2467741 : Blo 1949435 2467741 := bbase (se 3 (by rfl) ⟨462701, by rfl⟩ : syracuseStep 2467741 = 925403) (by norm_num)
theorem B3290321 : Blo 1949435 3290321 := bstep (se 2 (by rfl) ⟨1233870, by rfl⟩ : syracuseStep 3290321 = 2467741) B2467741
theorem B2193547 : Blo 1949435 2193547 := bstep (se 1 (by rfl) ⟨1645160, by rfl⟩ : syracuseStep 2193547 = 3290321) B3290321
theorem B2924729 : Blo 1949435 2924729 := bstep (se 2 (by rfl) ⟨1096773, by rfl⟩ : syracuseStep 2924729 = 2193547) B2193547
theorem B1949819 : Blo 1949435 1949819 := bstep (se 1 (by rfl) ⟨1462364, by rfl⟩ : syracuseStep 1949819 = 2924729) B2924729
theorem B2003393 : Blo 1949435 2003393 := bbase (se 2 (by rfl) ⟨751272, by rfl⟩ : syracuseStep 2003393 = 1502545) (by norm_num)
theorem B5342381 : Blo 1949435 5342381 := bstep (se 3 (by rfl) ⟨1001696, by rfl⟩ : syracuseStep 5342381 = 2003393) B2003393
theorem B3561587 : Blo 1949435 3561587 := bstep (se 1 (by rfl) ⟨2671190, by rfl⟩ : syracuseStep 3561587 = 5342381) B5342381
theorem B2374391 : Blo 1949435 2374391 := bstep (se 1 (by rfl) ⟨1780793, by rfl⟩ : syracuseStep 2374391 = 3561587) B3561587
theorem B6331709 : Blo 1949435 6331709 := bstep (se 3 (by rfl) ⟨1187195, by rfl⟩ : syracuseStep 6331709 = 2374391) B2374391
theorem B16884557 : Blo 1949435 16884557 := bstep (se 3 (by rfl) ⟨3165854, by rfl⟩ : syracuseStep 16884557 = 6331709) B6331709
theorem B11256371 : Blo 1949435 11256371 := bstep (se 1 (by rfl) ⟨8442278, by rfl⟩ : syracuseStep 11256371 = 16884557) B16884557
theorem B7504247 : Blo 1949435 7504247 := bstep (se 1 (by rfl) ⟨5628185, by rfl⟩ : syracuseStep 7504247 = 11256371) B11256371
theorem B5002831 : Blo 1949435 5002831 := bstep (se 1 (by rfl) ⟨3752123, by rfl⟩ : syracuseStep 5002831 = 7504247) B7504247
theorem B6670441 : Blo 1949435 6670441 := bstep (se 2 (by rfl) ⟨2501415, by rfl⟩ : syracuseStep 6670441 = 5002831) B5002831
theorem B8893921 : Blo 1949435 8893921 := bstep (se 2 (by rfl) ⟨3335220, by rfl⟩ : syracuseStep 8893921 = 6670441) B6670441
theorem B11858561 : Blo 1949435 11858561 := bstep (se 2 (by rfl) ⟨4446960, by rfl⟩ : syracuseStep 11858561 = 8893921) B8893921
theorem B7905707 : Blo 1949435 7905707 := bstep (se 1 (by rfl) ⟨5929280, by rfl⟩ : syracuseStep 7905707 = 11858561) B11858561
theorem B5270471 : Blo 1949435 5270471 := bstep (se 1 (by rfl) ⟨3952853, by rfl⟩ : syracuseStep 5270471 = 7905707) B7905707
theorem B3513647 : Blo 1949435 3513647 := bstep (se 1 (by rfl) ⟨2635235, by rfl⟩ : syracuseStep 3513647 = 5270471) B5270471
theorem B2342431 : Blo 1949435 2342431 := bstep (se 1 (by rfl) ⟨1756823, by rfl⟩ : syracuseStep 2342431 = 3513647) B3513647
theorem B3123241 : Blo 1949435 3123241 := bstep (se 2 (by rfl) ⟨1171215, by rfl⟩ : syracuseStep 3123241 = 2342431) B2342431
theorem B16657285 : Blo 1949435 16657285 := bstep (se 4 (by rfl) ⟨1561620, by rfl⟩ : syracuseStep 16657285 = 3123241) B3123241
theorem B22209713 : Blo 1949435 22209713 := bstep (se 2 (by rfl) ⟨8328642, by rfl⟩ : syracuseStep 22209713 = 16657285) B16657285
theorem B14806475 : Blo 1949435 14806475 := bstep (se 1 (by rfl) ⟨11104856, by rfl⟩ : syracuseStep 14806475 = 22209713) B22209713
theorem B9870983 : Blo 1949435 9870983 := bstep (se 1 (by rfl) ⟨7403237, by rfl⟩ : syracuseStep 9870983 = 14806475) B14806475
theorem B6580655 : Blo 1949435 6580655 := bstep (se 1 (by rfl) ⟨4935491, by rfl⟩ : syracuseStep 6580655 = 9870983) B9870983
theorem B4387103 : Blo 1949435 4387103 := bstep (se 1 (by rfl) ⟨3290327, by rfl⟩ : syracuseStep 4387103 = 6580655) B6580655
theorem B2924735 : Blo 1949435 2924735 := bstep (se 1 (by rfl) ⟨2193551, by rfl⟩ : syracuseStep 2924735 = 4387103) B4387103
theorem B1949823 : Blo 1949435 1949823 := bstep (se 1 (by rfl) ⟨1462367, by rfl⟩ : syracuseStep 1949823 = 2924735) B2924735
theorem B2924741 : Blo 1949435 2924741 := bbase (se 4 (by rfl) ⟨274194, by rfl⟩ : syracuseStep 2924741 = 548389) (by norm_num)
theorem B1949827 : Blo 1949435 1949827 := bstep (se 1 (by rfl) ⟨1462370, by rfl⟩ : syracuseStep 1949827 = 2924741) B2924741
theorem B3290341 : Blo 1949435 3290341 := bbase (se 4 (by rfl) ⟨308469, by rfl⟩ : syracuseStep 3290341 = 616939) (by norm_num)
theorem B4387121 : Blo 1949435 4387121 := bstep (se 2 (by rfl) ⟨1645170, by rfl⟩ : syracuseStep 4387121 = 3290341) B3290341
theorem B2924747 : Blo 1949435 2924747 := bstep (se 1 (by rfl) ⟨2193560, by rfl⟩ : syracuseStep 2924747 = 4387121) B4387121
theorem B1949831 : Blo 1949435 1949831 := bstep (se 1 (by rfl) ⟨1462373, by rfl⟩ : syracuseStep 1949831 = 2924747) B2924747
theorem B2193565 : Blo 1949435 2193565 := bbase (se 3 (by rfl) ⟨411293, by rfl⟩ : syracuseStep 2193565 = 822587) (by norm_num)
theorem B2924753 : Blo 1949435 2924753 := bstep (se 2 (by rfl) ⟨1096782, by rfl⟩ : syracuseStep 2924753 = 2193565) B2193565
theorem B1949835 : Blo 1949435 1949835 := bstep (se 1 (by rfl) ⟨1462376, by rfl⟩ : syracuseStep 1949835 = 2924753) B2924753
theorem B6580709 : Blo 1949435 6580709 := bbase (se 4 (by rfl) ⟨616941, by rfl⟩ : syracuseStep 6580709 = 1233883) (by norm_num)
theorem B4387139 : Blo 1949435 4387139 := bstep (se 1 (by rfl) ⟨3290354, by rfl⟩ : syracuseStep 4387139 = 6580709) B6580709
theorem B2924759 : Blo 1949435 2924759 := bstep (se 1 (by rfl) ⟨2193569, by rfl⟩ : syracuseStep 2924759 = 4387139) B4387139
theorem B1949839 : Blo 1949435 1949839 := bstep (se 1 (by rfl) ⟨1462379, by rfl⟩ : syracuseStep 1949839 = 2924759) B2924759
theorem B2924765 : Blo 1949435 2924765 := bbase (se 3 (by rfl) ⟨548393, by rfl⟩ : syracuseStep 2924765 = 1096787) (by norm_num)
theorem B1949843 : Blo 1949435 1949843 := bstep (se 1 (by rfl) ⟨1462382, by rfl⟩ : syracuseStep 1949843 = 2924765) B2924765
theorem B4387157 : Blo 1949435 4387157 := bbase (se 10 (by rfl) ⟨6426, by rfl⟩ : syracuseStep 4387157 = 12853) (by norm_num)
theorem B2924771 : Blo 1949435 2924771 := bstep (se 1 (by rfl) ⟨2193578, by rfl⟩ : syracuseStep 2924771 = 4387157) B4387157
theorem B1949847 : Blo 1949435 1949847 := bstep (se 1 (by rfl) ⟨1462385, by rfl⟩ : syracuseStep 1949847 = 2924771) B2924771
theorem B7027397 : Blo 1949435 7027397 := bbase (se 4 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 7027397 = 1317637) (by norm_num)
theorem B4684931 : Blo 1949435 4684931 := bstep (se 1 (by rfl) ⟨3513698, by rfl⟩ : syracuseStep 4684931 = 7027397) B7027397
theorem B3123287 : Blo 1949435 3123287 := bstep (se 1 (by rfl) ⟨2342465, by rfl⟩ : syracuseStep 3123287 = 4684931) B4684931
theorem B2082191 : Blo 1949435 2082191 := bstep (se 1 (by rfl) ⟨1561643, by rfl⟩ : syracuseStep 2082191 = 3123287) B3123287
theorem B5552509 : Blo 1949435 5552509 := bstep (se 3 (by rfl) ⟨1041095, by rfl⟩ : syracuseStep 5552509 = 2082191) B2082191
theorem B7403345 : Blo 1949435 7403345 := bstep (se 2 (by rfl) ⟨2776254, by rfl⟩ : syracuseStep 7403345 = 5552509) B5552509
theorem B4935563 : Blo 1949435 4935563 := bstep (se 1 (by rfl) ⟨3701672, by rfl⟩ : syracuseStep 4935563 = 7403345) B7403345
theorem B3290375 : Blo 1949435 3290375 := bstep (se 1 (by rfl) ⟨2467781, by rfl⟩ : syracuseStep 3290375 = 4935563) B4935563
theorem B2193583 : Blo 1949435 2193583 := bstep (se 1 (by rfl) ⟨1645187, by rfl⟩ : syracuseStep 2193583 = 3290375) B3290375
theorem B2924777 : Blo 1949435 2924777 := bstep (se 2 (by rfl) ⟨1096791, by rfl⟩ : syracuseStep 2924777 = 2193583) B2193583
theorem B1949851 : Blo 1949435 1949851 := bstep (se 1 (by rfl) ⟨1462388, by rfl⟩ : syracuseStep 1949851 = 2924777) B2924777
theorem B37479509 : Blo 1949435 37479509 := bbase (se 8 (by rfl) ⟨219606, by rfl⟩ : syracuseStep 37479509 = 439213) (by norm_num)
theorem B24986339 : Blo 1949435 24986339 := bstep (se 1 (by rfl) ⟨18739754, by rfl⟩ : syracuseStep 24986339 = 37479509) B37479509
theorem B16657559 : Blo 1949435 16657559 := bstep (se 1 (by rfl) ⟨12493169, by rfl⟩ : syracuseStep 16657559 = 24986339) B24986339
theorem B11105039 : Blo 1949435 11105039 := bstep (se 1 (by rfl) ⟨8328779, by rfl⟩ : syracuseStep 11105039 = 16657559) B16657559
theorem B7403359 : Blo 1949435 7403359 := bstep (se 1 (by rfl) ⟨5552519, by rfl⟩ : syracuseStep 7403359 = 11105039) B11105039
theorem B9871145 : Blo 1949435 9871145 := bstep (se 2 (by rfl) ⟨3701679, by rfl⟩ : syracuseStep 9871145 = 7403359) B7403359
theorem B6580763 : Blo 1949435 6580763 := bstep (se 1 (by rfl) ⟨4935572, by rfl⟩ : syracuseStep 6580763 = 9871145) B9871145
theorem B4387175 : Blo 1949435 4387175 := bstep (se 1 (by rfl) ⟨3290381, by rfl⟩ : syracuseStep 4387175 = 6580763) B6580763
theorem B2924783 : Blo 1949435 2924783 := bstep (se 1 (by rfl) ⟨2193587, by rfl⟩ : syracuseStep 2924783 = 4387175) B4387175
theorem B1949855 : Blo 1949435 1949855 := bstep (se 1 (by rfl) ⟨1462391, by rfl⟩ : syracuseStep 1949855 = 2924783) B2924783
theorem B2924789 : Blo 1949435 2924789 := bbase (se 5 (by rfl) ⟨137099, by rfl⟩ : syracuseStep 2924789 = 274199) (by norm_num)
theorem B1949859 : Blo 1949435 1949859 := bstep (se 1 (by rfl) ⟨1462394, by rfl⟩ : syracuseStep 1949859 = 2924789) B2924789
theorem B5002933 : Blo 1949435 5002933 := bbase (se 5 (by rfl) ⟨234512, by rfl⟩ : syracuseStep 5002933 = 469025) (by norm_num)
theorem B6670577 : Blo 1949435 6670577 := bstep (se 2 (by rfl) ⟨2501466, by rfl⟩ : syracuseStep 6670577 = 5002933) B5002933
theorem B4447051 : Blo 1949435 4447051 := bstep (se 1 (by rfl) ⟨3335288, by rfl⟩ : syracuseStep 4447051 = 6670577) B6670577
theorem B23717605 : Blo 1949435 23717605 := bstep (se 4 (by rfl) ⟨2223525, by rfl⟩ : syracuseStep 23717605 = 4447051) B4447051
theorem B31623473 : Blo 1949435 31623473 := bstep (se 2 (by rfl) ⟨11858802, by rfl⟩ : syracuseStep 31623473 = 23717605) B23717605
theorem B21082315 : Blo 1949435 21082315 := bstep (se 1 (by rfl) ⟨15811736, by rfl⟩ : syracuseStep 21082315 = 31623473) B31623473
theorem B28109753 : Blo 1949435 28109753 := bstep (se 2 (by rfl) ⟨10541157, by rfl⟩ : syracuseStep 28109753 = 21082315) B21082315
theorem B18739835 : Blo 1949435 18739835 := bstep (se 1 (by rfl) ⟨14054876, by rfl⟩ : syracuseStep 18739835 = 28109753) B28109753
theorem B12493223 : Blo 1949435 12493223 := bstep (se 1 (by rfl) ⟨9369917, by rfl⟩ : syracuseStep 12493223 = 18739835) B18739835
theorem B8328815 : Blo 1949435 8328815 := bstep (se 1 (by rfl) ⟨6246611, by rfl⟩ : syracuseStep 8328815 = 12493223) B12493223
theorem B5552543 : Blo 1949435 5552543 := bstep (se 1 (by rfl) ⟨4164407, by rfl⟩ : syracuseStep 5552543 = 8328815) B8328815
theorem B3701695 : Blo 1949435 3701695 := bstep (se 1 (by rfl) ⟨2776271, by rfl⟩ : syracuseStep 3701695 = 5552543) B5552543
theorem B4935593 : Blo 1949435 4935593 := bstep (se 2 (by rfl) ⟨1850847, by rfl⟩ : syracuseStep 4935593 = 3701695) B3701695
theorem B3290395 : Blo 1949435 3290395 := bstep (se 1 (by rfl) ⟨2467796, by rfl⟩ : syracuseStep 3290395 = 4935593) B4935593
theorem B4387193 : Blo 1949435 4387193 := bstep (se 2 (by rfl) ⟨1645197, by rfl⟩ : syracuseStep 4387193 = 3290395) B3290395
theorem B2924795 : Blo 1949435 2924795 := bstep (se 1 (by rfl) ⟨2193596, by rfl⟩ : syracuseStep 2924795 = 4387193) B4387193
theorem B1949863 : Blo 1949435 1949863 := bstep (se 1 (by rfl) ⟨1462397, by rfl⟩ : syracuseStep 1949863 = 2924795) B2924795
theorem B2193601 : Blo 1949435 2193601 := bbase (se 2 (by rfl) ⟨822600, by rfl⟩ : syracuseStep 2193601 = 1645201) (by norm_num)
theorem B2924801 : Blo 1949435 2924801 := bstep (se 2 (by rfl) ⟨1096800, by rfl⟩ : syracuseStep 2924801 = 2193601) B2193601
theorem B1949867 : Blo 1949435 1949867 := bstep (se 1 (by rfl) ⟨1462400, by rfl⟩ : syracuseStep 1949867 = 2924801) B2924801
theorem B4935613 : Blo 1949435 4935613 := bbase (se 3 (by rfl) ⟨925427, by rfl⟩ : syracuseStep 4935613 = 1850855) (by norm_num)
theorem B6580817 : Blo 1949435 6580817 := bstep (se 2 (by rfl) ⟨2467806, by rfl⟩ : syracuseStep 6580817 = 4935613) B4935613
theorem B4387211 : Blo 1949435 4387211 := bstep (se 1 (by rfl) ⟨3290408, by rfl⟩ : syracuseStep 4387211 = 6580817) B6580817
theorem B2924807 : Blo 1949435 2924807 := bstep (se 1 (by rfl) ⟨2193605, by rfl⟩ : syracuseStep 2924807 = 4387211) B4387211
theorem B1949871 : Blo 1949435 1949871 := bstep (se 1 (by rfl) ⟨1462403, by rfl⟩ : syracuseStep 1949871 = 2924807) B2924807
theorem B2924813 : Blo 1949435 2924813 := bbase (se 3 (by rfl) ⟨548402, by rfl⟩ : syracuseStep 2924813 = 1096805) (by norm_num)
theorem B1949875 : Blo 1949435 1949875 := bstep (se 1 (by rfl) ⟨1462406, by rfl⟩ : syracuseStep 1949875 = 2924813) B2924813
theorem B4387229 : Blo 1949435 4387229 := bbase (se 3 (by rfl) ⟨822605, by rfl⟩ : syracuseStep 4387229 = 1645211) (by norm_num)
theorem B2924819 : Blo 1949435 2924819 := bstep (se 1 (by rfl) ⟨2193614, by rfl⟩ : syracuseStep 2924819 = 4387229) B4387229
theorem B1949879 : Blo 1949435 1949879 := bstep (se 1 (by rfl) ⟨1462409, by rfl⟩ : syracuseStep 1949879 = 2924819) B2924819
theorem B3290429 : Blo 1949435 3290429 := bbase (se 3 (by rfl) ⟨616955, by rfl⟩ : syracuseStep 3290429 = 1233911) (by norm_num)
theorem B2193619 : Blo 1949435 2193619 := bstep (se 1 (by rfl) ⟨1645214, by rfl⟩ : syracuseStep 2193619 = 3290429) B3290429
theorem B2924825 : Blo 1949435 2924825 := bstep (se 2 (by rfl) ⟨1096809, by rfl⟩ : syracuseStep 2924825 = 2193619) B2193619
theorem B1949883 : Blo 1949435 1949883 := bstep (se 1 (by rfl) ⟨1462412, by rfl⟩ : syracuseStep 1949883 = 2924825) B2924825
theorem B2082229 : Blo 1949435 2082229 := bbase (se 5 (by rfl) ⟨97604, by rfl⟩ : syracuseStep 2082229 = 195209) (by norm_num)
theorem B11105221 : Blo 1949435 11105221 := bstep (se 4 (by rfl) ⟨1041114, by rfl⟩ : syracuseStep 11105221 = 2082229) B2082229
theorem B14806961 : Blo 1949435 14806961 := bstep (se 2 (by rfl) ⟨5552610, by rfl⟩ : syracuseStep 14806961 = 11105221) B11105221
theorem B9871307 : Blo 1949435 9871307 := bstep (se 1 (by rfl) ⟨7403480, by rfl⟩ : syracuseStep 9871307 = 14806961) B14806961
theorem B6580871 : Blo 1949435 6580871 := bstep (se 1 (by rfl) ⟨4935653, by rfl⟩ : syracuseStep 6580871 = 9871307) B9871307
theorem B4387247 : Blo 1949435 4387247 := bstep (se 1 (by rfl) ⟨3290435, by rfl⟩ : syracuseStep 4387247 = 6580871) B6580871
theorem B2924831 : Blo 1949435 2924831 := bstep (se 1 (by rfl) ⟨2193623, by rfl⟩ : syracuseStep 2924831 = 4387247) B4387247
theorem B1949887 : Blo 1949435 1949887 := bstep (se 1 (by rfl) ⟨1462415, by rfl⟩ : syracuseStep 1949887 = 2924831) B2924831
theorem B2924837 : Blo 1949435 2924837 := bbase (se 4 (by rfl) ⟨274203, by rfl⟩ : syracuseStep 2924837 = 548407) (by norm_num)
theorem B1949891 : Blo 1949435 1949891 := bstep (se 1 (by rfl) ⟨1462418, by rfl⟩ : syracuseStep 1949891 = 2924837) B2924837
theorem B2467837 : Blo 1949435 2467837 := bbase (se 3 (by rfl) ⟨462719, by rfl⟩ : syracuseStep 2467837 = 925439) (by norm_num)
theorem B3290449 : Blo 1949435 3290449 := bstep (se 2 (by rfl) ⟨1233918, by rfl⟩ : syracuseStep 3290449 = 2467837) B2467837
theorem B4387265 : Blo 1949435 4387265 := bstep (se 2 (by rfl) ⟨1645224, by rfl⟩ : syracuseStep 4387265 = 3290449) B3290449
theorem B2924843 : Blo 1949435 2924843 := bstep (se 1 (by rfl) ⟨2193632, by rfl⟩ : syracuseStep 2924843 = 4387265) B4387265
theorem B1949895 : Blo 1949435 1949895 := bstep (se 1 (by rfl) ⟨1462421, by rfl⟩ : syracuseStep 1949895 = 2924843) B2924843
theorem B2193637 : Blo 1949435 2193637 := bbase (se 4 (by rfl) ⟨205653, by rfl⟩ : syracuseStep 2193637 = 411307) (by norm_num)
theorem B2924849 : Blo 1949435 2924849 := bstep (se 2 (by rfl) ⟨1096818, by rfl⟩ : syracuseStep 2924849 = 2193637) B2193637
theorem B1949899 : Blo 1949435 1949899 := bstep (se 1 (by rfl) ⟨1462424, by rfl⟩ : syracuseStep 1949899 = 2924849) B2924849
theorem B4164493 : Blo 1949435 4164493 := bbase (se 3 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 4164493 = 1561685) (by norm_num)
theorem B5552657 : Blo 1949435 5552657 := bstep (se 2 (by rfl) ⟨2082246, by rfl⟩ : syracuseStep 5552657 = 4164493) B4164493
theorem B3701771 : Blo 1949435 3701771 := bstep (se 1 (by rfl) ⟨2776328, by rfl⟩ : syracuseStep 3701771 = 5552657) B5552657
theorem B2467847 : Blo 1949435 2467847 := bstep (se 1 (by rfl) ⟨1850885, by rfl⟩ : syracuseStep 2467847 = 3701771) B3701771
theorem B6580925 : Blo 1949435 6580925 := bstep (se 3 (by rfl) ⟨1233923, by rfl⟩ : syracuseStep 6580925 = 2467847) B2467847
theorem B4387283 : Blo 1949435 4387283 := bstep (se 1 (by rfl) ⟨3290462, by rfl⟩ : syracuseStep 4387283 = 6580925) B6580925
theorem B2924855 : Blo 1949435 2924855 := bstep (se 1 (by rfl) ⟨2193641, by rfl⟩ : syracuseStep 2924855 = 4387283) B4387283
theorem B1949903 : Blo 1949435 1949903 := bstep (se 1 (by rfl) ⟨1462427, by rfl⟩ : syracuseStep 1949903 = 2924855) B2924855
theorem B2924861 : Blo 1949435 2924861 := bbase (se 3 (by rfl) ⟨548411, by rfl⟩ : syracuseStep 2924861 = 1096823) (by norm_num)
theorem B1949907 : Blo 1949435 1949907 := bstep (se 1 (by rfl) ⟨1462430, by rfl⟩ : syracuseStep 1949907 = 2924861) B2924861
theorem B4387301 : Blo 1949435 4387301 := bbase (se 4 (by rfl) ⟨411309, by rfl⟩ : syracuseStep 4387301 = 822619) (by norm_num)
theorem B2924867 : Blo 1949435 2924867 := bstep (se 1 (by rfl) ⟨2193650, by rfl⟩ : syracuseStep 2924867 = 4387301) B4387301
theorem B1949911 : Blo 1949435 1949911 := bstep (se 1 (by rfl) ⟨1462433, by rfl⟩ : syracuseStep 1949911 = 2924867) B2924867
theorem B4935725 : Blo 1949435 4935725 := bbase (se 3 (by rfl) ⟨925448, by rfl⟩ : syracuseStep 4935725 = 1850897) (by norm_num)
theorem B3290483 : Blo 1949435 3290483 := bstep (se 1 (by rfl) ⟨2467862, by rfl⟩ : syracuseStep 3290483 = 4935725) B4935725
theorem B2193655 : Blo 1949435 2193655 := bstep (se 1 (by rfl) ⟨1645241, by rfl⟩ : syracuseStep 2193655 = 3290483) B3290483
theorem B2924873 : Blo 1949435 2924873 := bstep (se 2 (by rfl) ⟨1096827, by rfl⟩ : syracuseStep 2924873 = 2193655) B2193655
theorem B1949915 : Blo 1949435 1949915 := bstep (se 1 (by rfl) ⟨1462436, by rfl⟩ : syracuseStep 1949915 = 2924873) B2924873
theorem B10541461 : Blo 1949435 10541461 := bbase (se 6 (by rfl) ⟨247065, by rfl⟩ : syracuseStep 10541461 = 494131) (by norm_num)
theorem B14055281 : Blo 1949435 14055281 := bstep (se 2 (by rfl) ⟨5270730, by rfl⟩ : syracuseStep 14055281 = 10541461) B10541461
theorem B9370187 : Blo 1949435 9370187 := bstep (se 1 (by rfl) ⟨7027640, by rfl⟩ : syracuseStep 9370187 = 14055281) B14055281
theorem B6246791 : Blo 1949435 6246791 := bstep (se 1 (by rfl) ⟨4685093, by rfl⟩ : syracuseStep 6246791 = 9370187) B9370187
theorem B4164527 : Blo 1949435 4164527 := bstep (se 1 (by rfl) ⟨3123395, by rfl⟩ : syracuseStep 4164527 = 6246791) B6246791
theorem B2776351 : Blo 1949435 2776351 := bstep (se 1 (by rfl) ⟨2082263, by rfl⟩ : syracuseStep 2776351 = 4164527) B4164527
theorem B3701801 : Blo 1949435 3701801 := bstep (se 2 (by rfl) ⟨1388175, by rfl⟩ : syracuseStep 3701801 = 2776351) B2776351
theorem B9871469 : Blo 1949435 9871469 := bstep (se 3 (by rfl) ⟨1850900, by rfl⟩ : syracuseStep 9871469 = 3701801) B3701801
theorem B6580979 : Blo 1949435 6580979 := bstep (se 1 (by rfl) ⟨4935734, by rfl⟩ : syracuseStep 6580979 = 9871469) B9871469
theorem B4387319 : Blo 1949435 4387319 := bstep (se 1 (by rfl) ⟨3290489, by rfl⟩ : syracuseStep 4387319 = 6580979) B6580979
theorem B2924879 : Blo 1949435 2924879 := bstep (se 1 (by rfl) ⟨2193659, by rfl⟩ : syracuseStep 2924879 = 4387319) B4387319
theorem B1949919 : Blo 1949435 1949919 := bstep (se 1 (by rfl) ⟨1462439, by rfl⟩ : syracuseStep 1949919 = 2924879) B2924879
theorem B2924885 : Blo 1949435 2924885 := bbase (se 10 (by rfl) ⟨4284, by rfl⟩ : syracuseStep 2924885 = 8569) (by norm_num)
theorem B1949923 : Blo 1949435 1949923 := bstep (se 1 (by rfl) ⟨1462442, by rfl⟩ : syracuseStep 1949923 = 2924885) B2924885
theorem B5552725 : Blo 1949435 5552725 := bbase (se 8 (by rfl) ⟨32535, by rfl⟩ : syracuseStep 5552725 = 65071) (by norm_num)
theorem B7403633 : Blo 1949435 7403633 := bstep (se 2 (by rfl) ⟨2776362, by rfl⟩ : syracuseStep 7403633 = 5552725) B5552725
theorem B4935755 : Blo 1949435 4935755 := bstep (se 1 (by rfl) ⟨3701816, by rfl⟩ : syracuseStep 4935755 = 7403633) B7403633
theorem B3290503 : Blo 1949435 3290503 := bstep (se 1 (by rfl) ⟨2467877, by rfl⟩ : syracuseStep 3290503 = 4935755) B4935755
theorem B4387337 : Blo 1949435 4387337 := bstep (se 2 (by rfl) ⟨1645251, by rfl⟩ : syracuseStep 4387337 = 3290503) B3290503
theorem B2924891 : Blo 1949435 2924891 := bstep (se 1 (by rfl) ⟨2193668, by rfl⟩ : syracuseStep 2924891 = 4387337) B4387337
theorem B1949927 : Blo 1949435 1949927 := bstep (se 1 (by rfl) ⟨1462445, by rfl⟩ : syracuseStep 1949927 = 2924891) B2924891
theorem B2193673 : Blo 1949435 2193673 := bbase (se 2 (by rfl) ⟨822627, by rfl⟩ : syracuseStep 2193673 = 1645255) (by norm_num)
theorem B2924897 : Blo 1949435 2924897 := bstep (se 2 (by rfl) ⟨1096836, by rfl⟩ : syracuseStep 2924897 = 2193673) B2193673
theorem B1949931 : Blo 1949435 1949931 := bstep (se 1 (by rfl) ⟨1462448, by rfl⟩ : syracuseStep 1949931 = 2924897) B2924897
theorem B5270773 : Blo 1949435 5270773 := bbase (se 5 (by rfl) ⟨247067, by rfl⟩ : syracuseStep 5270773 = 494135) (by norm_num)
theorem B7027697 : Blo 1949435 7027697 := bstep (se 2 (by rfl) ⟨2635386, by rfl⟩ : syracuseStep 7027697 = 5270773) B5270773
theorem B4685131 : Blo 1949435 4685131 := bstep (se 1 (by rfl) ⟨3513848, by rfl⟩ : syracuseStep 4685131 = 7027697) B7027697
theorem B24987365 : Blo 1949435 24987365 := bstep (se 4 (by rfl) ⟨2342565, by rfl⟩ : syracuseStep 24987365 = 4685131) B4685131
theorem B16658243 : Blo 1949435 16658243 := bstep (se 1 (by rfl) ⟨12493682, by rfl⟩ : syracuseStep 16658243 = 24987365) B24987365
theorem B11105495 : Blo 1949435 11105495 := bstep (se 1 (by rfl) ⟨8329121, by rfl⟩ : syracuseStep 11105495 = 16658243) B16658243
theorem B7403663 : Blo 1949435 7403663 := bstep (se 1 (by rfl) ⟨5552747, by rfl⟩ : syracuseStep 7403663 = 11105495) B11105495
theorem B4935775 : Blo 1949435 4935775 := bstep (se 1 (by rfl) ⟨3701831, by rfl⟩ : syracuseStep 4935775 = 7403663) B7403663
theorem B6581033 : Blo 1949435 6581033 := bstep (se 2 (by rfl) ⟨2467887, by rfl⟩ : syracuseStep 6581033 = 4935775) B4935775
theorem B4387355 : Blo 1949435 4387355 := bstep (se 1 (by rfl) ⟨3290516, by rfl⟩ : syracuseStep 4387355 = 6581033) B6581033
theorem B2924903 : Blo 1949435 2924903 := bstep (se 1 (by rfl) ⟨2193677, by rfl⟩ : syracuseStep 2924903 = 4387355) B4387355
theorem B1949935 : Blo 1949435 1949935 := bstep (se 1 (by rfl) ⟨1462451, by rfl⟩ : syracuseStep 1949935 = 2924903) B2924903
theorem B2924909 : Blo 1949435 2924909 := bbase (se 3 (by rfl) ⟨548420, by rfl⟩ : syracuseStep 2924909 = 1096841) (by norm_num)
theorem B1949939 : Blo 1949435 1949939 := bstep (se 1 (by rfl) ⟨1462454, by rfl⟩ : syracuseStep 1949939 = 2924909) B2924909
theorem B4387373 : Blo 1949435 4387373 := bbase (se 3 (by rfl) ⟨822632, by rfl⟩ : syracuseStep 4387373 = 1645265) (by norm_num)
theorem B2924915 : Blo 1949435 2924915 := bstep (se 1 (by rfl) ⟨2193686, by rfl⟩ : syracuseStep 2924915 = 4387373) B4387373
theorem B1949943 : Blo 1949435 1949943 := bstep (se 1 (by rfl) ⟨1462457, by rfl⟩ : syracuseStep 1949943 = 2924915) B2924915
theorem B11859317 : Blo 1949435 11859317 := bbase (se 5 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 11859317 = 1111811) (by norm_num)
theorem B7906211 : Blo 1949435 7906211 := bstep (se 1 (by rfl) ⟨5929658, by rfl⟩ : syracuseStep 7906211 = 11859317) B11859317
theorem B5270807 : Blo 1949435 5270807 := bstep (se 1 (by rfl) ⟨3953105, by rfl⟩ : syracuseStep 5270807 = 7906211) B7906211
theorem B3513871 : Blo 1949435 3513871 := bstep (se 1 (by rfl) ⟨2635403, by rfl⟩ : syracuseStep 3513871 = 5270807) B5270807
theorem B18740645 : Blo 1949435 18740645 := bstep (se 4 (by rfl) ⟨1756935, by rfl⟩ : syracuseStep 18740645 = 3513871) B3513871
theorem B12493763 : Blo 1949435 12493763 := bstep (se 1 (by rfl) ⟨9370322, by rfl⟩ : syracuseStep 12493763 = 18740645) B18740645
theorem B8329175 : Blo 1949435 8329175 := bstep (se 1 (by rfl) ⟨6246881, by rfl⟩ : syracuseStep 8329175 = 12493763) B12493763
theorem B5552783 : Blo 1949435 5552783 := bstep (se 1 (by rfl) ⟨4164587, by rfl⟩ : syracuseStep 5552783 = 8329175) B8329175
theorem B3701855 : Blo 1949435 3701855 := bstep (se 1 (by rfl) ⟨2776391, by rfl⟩ : syracuseStep 3701855 = 5552783) B5552783
theorem B2467903 : Blo 1949435 2467903 := bstep (se 1 (by rfl) ⟨1850927, by rfl⟩ : syracuseStep 2467903 = 3701855) B3701855
theorem B3290537 : Blo 1949435 3290537 := bstep (se 2 (by rfl) ⟨1233951, by rfl⟩ : syracuseStep 3290537 = 2467903) B2467903
theorem B2193691 : Blo 1949435 2193691 := bstep (se 1 (by rfl) ⟨1645268, by rfl⟩ : syracuseStep 2193691 = 3290537) B3290537
theorem B2924921 : Blo 1949435 2924921 := bstep (se 2 (by rfl) ⟨1096845, by rfl⟩ : syracuseStep 2924921 = 2193691) B2193691
theorem B1949947 : Blo 1949435 1949947 := bstep (se 1 (by rfl) ⟨1462460, by rfl⟩ : syracuseStep 1949947 = 2924921) B2924921
theorem B33316757 : Blo 1949435 33316757 := bbase (se 6 (by rfl) ⟨780861, by rfl⟩ : syracuseStep 33316757 = 1561723) (by norm_num)
theorem B22211171 : Blo 1949435 22211171 := bstep (se 1 (by rfl) ⟨16658378, by rfl⟩ : syracuseStep 22211171 = 33316757) B33316757
theorem B14807447 : Blo 1949435 14807447 := bstep (se 1 (by rfl) ⟨11105585, by rfl⟩ : syracuseStep 14807447 = 22211171) B22211171
theorem B9871631 : Blo 1949435 9871631 := bstep (se 1 (by rfl) ⟨7403723, by rfl⟩ : syracuseStep 9871631 = 14807447) B14807447
theorem B6581087 : Blo 1949435 6581087 := bstep (se 1 (by rfl) ⟨4935815, by rfl⟩ : syracuseStep 6581087 = 9871631) B9871631
theorem B4387391 : Blo 1949435 4387391 := bstep (se 1 (by rfl) ⟨3290543, by rfl⟩ : syracuseStep 4387391 = 6581087) B6581087
theorem B2924927 : Blo 1949435 2924927 := bstep (se 1 (by rfl) ⟨2193695, by rfl⟩ : syracuseStep 2924927 = 4387391) B4387391
theorem B1949951 : Blo 1949435 1949951 := bstep (se 1 (by rfl) ⟨1462463, by rfl⟩ : syracuseStep 1949951 = 2924927) B2924927
theorem B2924933 : Blo 1949435 2924933 := bbase (se 4 (by rfl) ⟨274212, by rfl⟩ : syracuseStep 2924933 = 548425) (by norm_num)
theorem B1949955 : Blo 1949435 1949955 := bstep (se 1 (by rfl) ⟨1462466, by rfl⟩ : syracuseStep 1949955 = 2924933) B2924933
theorem B3290557 : Blo 1949435 3290557 := bbase (se 3 (by rfl) ⟨616979, by rfl⟩ : syracuseStep 3290557 = 1233959) (by norm_num)
theorem B4387409 : Blo 1949435 4387409 := bstep (se 2 (by rfl) ⟨1645278, by rfl⟩ : syracuseStep 4387409 = 3290557) B3290557
theorem B2924939 : Blo 1949435 2924939 := bstep (se 1 (by rfl) ⟨2193704, by rfl⟩ : syracuseStep 2924939 = 4387409) B4387409
theorem B1949959 : Blo 1949435 1949959 := bstep (se 1 (by rfl) ⟨1462469, by rfl⟩ : syracuseStep 1949959 = 2924939) B2924939
theorem B2193709 : Blo 1949435 2193709 := bbase (se 3 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 2193709 = 822641) (by norm_num)
theorem B2924945 : Blo 1949435 2924945 := bstep (se 2 (by rfl) ⟨1096854, by rfl⟩ : syracuseStep 2924945 = 2193709) B2193709
theorem B1949963 : Blo 1949435 1949963 := bstep (se 1 (by rfl) ⟨1462472, by rfl⟩ : syracuseStep 1949963 = 2924945) B2924945
theorem B6581141 : Blo 1949435 6581141 := bbase (se 6 (by rfl) ⟨154245, by rfl⟩ : syracuseStep 6581141 = 308491) (by norm_num)
theorem B4387427 : Blo 1949435 4387427 := bstep (se 1 (by rfl) ⟨3290570, by rfl⟩ : syracuseStep 4387427 = 6581141) B6581141
theorem B2924951 : Blo 1949435 2924951 := bstep (se 1 (by rfl) ⟨2193713, by rfl⟩ : syracuseStep 2924951 = 4387427) B4387427
theorem B1949967 : Blo 1949435 1949967 := bstep (se 1 (by rfl) ⟨1462475, by rfl⟩ : syracuseStep 1949967 = 2924951) B2924951
theorem B2924957 : Blo 1949435 2924957 := bbase (se 3 (by rfl) ⟨548429, by rfl⟩ : syracuseStep 2924957 = 1096859) (by norm_num)
theorem B1949971 : Blo 1949435 1949971 := bstep (se 1 (by rfl) ⟨1462478, by rfl⟩ : syracuseStep 1949971 = 2924957) B2924957
theorem B4387445 : Blo 1949435 4387445 := bbase (se 5 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 4387445 = 411323) (by norm_num)
theorem B2924963 : Blo 1949435 2924963 := bstep (se 1 (by rfl) ⟨2193722, by rfl⟩ : syracuseStep 2924963 = 4387445) B4387445
theorem B1949975 : Blo 1949435 1949975 := bstep (se 1 (by rfl) ⟨1462481, by rfl⟩ : syracuseStep 1949975 = 2924963) B2924963
theorem B11859509 : Blo 1949435 11859509 := bbase (se 5 (by rfl) ⟨555914, by rfl⟩ : syracuseStep 11859509 = 1111829) (by norm_num)
theorem B7906339 : Blo 1949435 7906339 := bstep (se 1 (by rfl) ⟨5929754, by rfl⟩ : syracuseStep 7906339 = 11859509) B11859509
theorem B10541785 : Blo 1949435 10541785 := bstep (se 2 (by rfl) ⟨3953169, by rfl⟩ : syracuseStep 10541785 = 7906339) B7906339
theorem B14055713 : Blo 1949435 14055713 := bstep (se 2 (by rfl) ⟨5270892, by rfl⟩ : syracuseStep 14055713 = 10541785) B10541785
theorem B9370475 : Blo 1949435 9370475 := bstep (se 1 (by rfl) ⟨7027856, by rfl⟩ : syracuseStep 9370475 = 14055713) B14055713
theorem B6246983 : Blo 1949435 6246983 := bstep (se 1 (by rfl) ⟨4685237, by rfl⟩ : syracuseStep 6246983 = 9370475) B9370475
theorem B16658621 : Blo 1949435 16658621 := bstep (se 3 (by rfl) ⟨3123491, by rfl⟩ : syracuseStep 16658621 = 6246983) B6246983
theorem B11105747 : Blo 1949435 11105747 := bstep (se 1 (by rfl) ⟨8329310, by rfl⟩ : syracuseStep 11105747 = 16658621) B16658621
theorem B7403831 : Blo 1949435 7403831 := bstep (se 1 (by rfl) ⟨5552873, by rfl⟩ : syracuseStep 7403831 = 11105747) B11105747
theorem B4935887 : Blo 1949435 4935887 := bstep (se 1 (by rfl) ⟨3701915, by rfl⟩ : syracuseStep 4935887 = 7403831) B7403831
theorem B3290591 : Blo 1949435 3290591 := bstep (se 1 (by rfl) ⟨2467943, by rfl⟩ : syracuseStep 3290591 = 4935887) B4935887
theorem B2193727 : Blo 1949435 2193727 := bstep (se 1 (by rfl) ⟨1645295, by rfl⟩ : syracuseStep 2193727 = 3290591) B3290591
theorem B2924969 : Blo 1949435 2924969 := bstep (se 2 (by rfl) ⟨1096863, by rfl⟩ : syracuseStep 2924969 = 2193727) B2193727
theorem B1949979 : Blo 1949435 1949979 := bstep (se 1 (by rfl) ⟨1462484, by rfl⟩ : syracuseStep 1949979 = 2924969) B2924969
theorem B7403845 : Blo 1949435 7403845 := bbase (se 4 (by rfl) ⟨694110, by rfl⟩ : syracuseStep 7403845 = 1388221) (by norm_num)
theorem B9871793 : Blo 1949435 9871793 := bstep (se 2 (by rfl) ⟨3701922, by rfl⟩ : syracuseStep 9871793 = 7403845) B7403845
theorem B6581195 : Blo 1949435 6581195 := bstep (se 1 (by rfl) ⟨4935896, by rfl⟩ : syracuseStep 6581195 = 9871793) B9871793
theorem B4387463 : Blo 1949435 4387463 := bstep (se 1 (by rfl) ⟨3290597, by rfl⟩ : syracuseStep 4387463 = 6581195) B6581195
theorem B2924975 : Blo 1949435 2924975 := bstep (se 1 (by rfl) ⟨2193731, by rfl⟩ : syracuseStep 2924975 = 4387463) B4387463
theorem B1949983 : Blo 1949435 1949983 := bstep (se 1 (by rfl) ⟨1462487, by rfl⟩ : syracuseStep 1949983 = 2924975) B2924975
theorem B2924981 : Blo 1949435 2924981 := bbase (se 5 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 2924981 = 274217) (by norm_num)
theorem B1949987 : Blo 1949435 1949987 := bstep (se 1 (by rfl) ⟨1462490, by rfl⟩ : syracuseStep 1949987 = 2924981) B2924981
theorem B4935917 : Blo 1949435 4935917 := bbase (se 3 (by rfl) ⟨925484, by rfl⟩ : syracuseStep 4935917 = 1850969) (by norm_num)
theorem B3290611 : Blo 1949435 3290611 := bstep (se 1 (by rfl) ⟨2467958, by rfl⟩ : syracuseStep 3290611 = 4935917) B4935917
theorem B4387481 : Blo 1949435 4387481 := bstep (se 2 (by rfl) ⟨1645305, by rfl⟩ : syracuseStep 4387481 = 3290611) B3290611
theorem B2924987 : Blo 1949435 2924987 := bstep (se 1 (by rfl) ⟨2193740, by rfl⟩ : syracuseStep 2924987 = 4387481) B4387481
theorem B1949991 : Blo 1949435 1949991 := bstep (se 1 (by rfl) ⟨1462493, by rfl⟩ : syracuseStep 1949991 = 2924987) B2924987
theorem B2193745 : Blo 1949435 2193745 := bbase (se 2 (by rfl) ⟨822654, by rfl⟩ : syracuseStep 2193745 = 1645309) (by norm_num)
theorem B2924993 : Blo 1949435 2924993 := bstep (se 2 (by rfl) ⟨1096872, by rfl⟩ : syracuseStep 2924993 = 2193745) B2193745
theorem B1949995 : Blo 1949435 1949995 := bstep (se 1 (by rfl) ⟨1462496, by rfl⟩ : syracuseStep 1949995 = 2924993) B2924993
theorem B2082349 : Blo 1949435 2082349 := bbase (se 3 (by rfl) ⟨390440, by rfl⟩ : syracuseStep 2082349 = 780881) (by norm_num)
theorem B2776465 : Blo 1949435 2776465 := bstep (se 2 (by rfl) ⟨1041174, by rfl⟩ : syracuseStep 2776465 = 2082349) B2082349
theorem B3701953 : Blo 1949435 3701953 := bstep (se 2 (by rfl) ⟨1388232, by rfl⟩ : syracuseStep 3701953 = 2776465) B2776465
theorem B4935937 : Blo 1949435 4935937 := bstep (se 2 (by rfl) ⟨1850976, by rfl⟩ : syracuseStep 4935937 = 3701953) B3701953
theorem B6581249 : Blo 1949435 6581249 := bstep (se 2 (by rfl) ⟨2467968, by rfl⟩ : syracuseStep 6581249 = 4935937) B4935937
theorem B4387499 : Blo 1949435 4387499 := bstep (se 1 (by rfl) ⟨3290624, by rfl⟩ : syracuseStep 4387499 = 6581249) B6581249
theorem B2924999 : Blo 1949435 2924999 := bstep (se 1 (by rfl) ⟨2193749, by rfl⟩ : syracuseStep 2924999 = 4387499) B4387499
theorem B1949999 : Blo 1949435 1949999 := bstep (se 1 (by rfl) ⟨1462499, by rfl⟩ : syracuseStep 1949999 = 2924999) B2924999
theorem B2925005 : Blo 1949435 2925005 := bbase (se 3 (by rfl) ⟨548438, by rfl⟩ : syracuseStep 2925005 = 1096877) (by norm_num)
theorem B1950003 : Blo 1949435 1950003 := bstep (se 1 (by rfl) ⟨1462502, by rfl⟩ : syracuseStep 1950003 = 2925005) B2925005
theorem B4387517 : Blo 1949435 4387517 := bbase (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) (by norm_num)
theorem B2925011 : Blo 1949435 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B1950007 : Blo 1949435 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B3290645 : Blo 1949435 3290645 := bbase (se 6 (by rfl) ⟨77124, by rfl⟩ : syracuseStep 3290645 = 154249) (by norm_num)
theorem B2193763 : Blo 1949435 2193763 := bstep (se 1 (by rfl) ⟨1645322, by rfl⟩ : syracuseStep 2193763 = 3290645) B3290645
theorem B2925017 : Blo 1949435 2925017 := bstep (se 2 (by rfl) ⟨1096881, by rfl⟩ : syracuseStep 2925017 = 2193763) B2193763
theorem B1950011 : Blo 1949435 1950011 := bstep (se 1 (by rfl) ⟨1462508, by rfl⟩ : syracuseStep 1950011 = 2925017) B2925017
theorem B1976621 : Blo 1949435 1976621 := bbase (se 3 (by rfl) ⟨370616, by rfl⟩ : syracuseStep 1976621 = 741233) (by norm_num)
theorem B5270989 : Blo 1949435 5270989 := bstep (se 3 (by rfl) ⟨988310, by rfl⟩ : syracuseStep 5270989 = 1976621) B1976621
theorem B7027985 : Blo 1949435 7027985 := bstep (se 2 (by rfl) ⟨2635494, by rfl⟩ : syracuseStep 7027985 = 5270989) B5270989
theorem B18741293 : Blo 1949435 18741293 := bstep (se 3 (by rfl) ⟨3513992, by rfl⟩ : syracuseStep 18741293 = 7027985) B7027985
theorem B12494195 : Blo 1949435 12494195 := bstep (se 1 (by rfl) ⟨9370646, by rfl⟩ : syracuseStep 12494195 = 18741293) B18741293
theorem B8329463 : Blo 1949435 8329463 := bstep (se 1 (by rfl) ⟨6247097, by rfl⟩ : syracuseStep 8329463 = 12494195) B12494195
theorem B5552975 : Blo 1949435 5552975 := bstep (se 1 (by rfl) ⟨4164731, by rfl⟩ : syracuseStep 5552975 = 8329463) B8329463
theorem B14807933 : Blo 1949435 14807933 := bstep (se 3 (by rfl) ⟨2776487, by rfl⟩ : syracuseStep 14807933 = 5552975) B5552975
theorem B9871955 : Blo 1949435 9871955 := bstep (se 1 (by rfl) ⟨7403966, by rfl⟩ : syracuseStep 9871955 = 14807933) B14807933
theorem B6581303 : Blo 1949435 6581303 := bstep (se 1 (by rfl) ⟨4935977, by rfl⟩ : syracuseStep 6581303 = 9871955) B9871955
theorem B4387535 : Blo 1949435 4387535 := bstep (se 1 (by rfl) ⟨3290651, by rfl⟩ : syracuseStep 4387535 = 6581303) B6581303
theorem B2925023 : Blo 1949435 2925023 := bstep (se 1 (by rfl) ⟨2193767, by rfl⟩ : syracuseStep 2925023 = 4387535) B4387535
theorem B1950015 : Blo 1949435 1950015 := bstep (se 1 (by rfl) ⟨1462511, by rfl⟩ : syracuseStep 1950015 = 2925023) B2925023
theorem B2925029 : Blo 1949435 2925029 := bbase (se 4 (by rfl) ⟨274221, by rfl⟩ : syracuseStep 2925029 = 548443) (by norm_num)
theorem B1950019 : Blo 1949435 1950019 := bstep (se 1 (by rfl) ⟨1462514, by rfl⟩ : syracuseStep 1950019 = 2925029) B2925029
theorem B5013805 : Blo 1949435 5013805 := bbase (se 3 (by rfl) ⟨940088, by rfl⟩ : syracuseStep 5013805 = 1880177) (by norm_num)
theorem B6685073 : Blo 1949435 6685073 := bstep (se 2 (by rfl) ⟨2506902, by rfl⟩ : syracuseStep 6685073 = 5013805) B5013805
theorem B4456715 : Blo 1949435 4456715 := bstep (se 1 (by rfl) ⟨3342536, by rfl⟩ : syracuseStep 4456715 = 6685073) B6685073
theorem B11884573 : Blo 1949435 11884573 := bstep (se 3 (by rfl) ⟨2228357, by rfl⟩ : syracuseStep 11884573 = 4456715) B4456715
theorem B15846097 : Blo 1949435 15846097 := bstep (se 2 (by rfl) ⟨5942286, by rfl⟩ : syracuseStep 15846097 = 11884573) B11884573
theorem B21128129 : Blo 1949435 21128129 := bstep (se 2 (by rfl) ⟨7923048, by rfl⟩ : syracuseStep 21128129 = 15846097) B15846097
theorem B14085419 : Blo 1949435 14085419 := bstep (se 1 (by rfl) ⟨10564064, by rfl⟩ : syracuseStep 14085419 = 21128129) B21128129
theorem B37561117 : Blo 1949435 37561117 := bstep (se 3 (by rfl) ⟨7042709, by rfl⟩ : syracuseStep 37561117 = 14085419) B14085419
theorem B50081489 : Blo 1949435 50081489 := bstep (se 2 (by rfl) ⟨18780558, by rfl⟩ : syracuseStep 50081489 = 37561117) B37561117
theorem B33387659 : Blo 1949435 33387659 := bstep (se 1 (by rfl) ⟨25040744, by rfl⟩ : syracuseStep 33387659 = 50081489) B50081489
theorem B22258439 : Blo 1949435 22258439 := bstep (se 1 (by rfl) ⟨16693829, by rfl⟩ : syracuseStep 22258439 = 33387659) B33387659
theorem B14838959 : Blo 1949435 14838959 := bstep (se 1 (by rfl) ⟨11129219, by rfl⟩ : syracuseStep 14838959 = 22258439) B22258439
theorem B9892639 : Blo 1949435 9892639 := bstep (se 1 (by rfl) ⟨7419479, by rfl⟩ : syracuseStep 9892639 = 14838959) B14838959
theorem B52760741 : Blo 1949435 52760741 := bstep (se 4 (by rfl) ⟨4946319, by rfl⟩ : syracuseStep 52760741 = 9892639) B9892639
theorem B140695309 : Blo 1949435 140695309 := bstep (se 3 (by rfl) ⟨26380370, by rfl⟩ : syracuseStep 140695309 = 52760741) B52760741
theorem B187593745 : Blo 1949435 187593745 := bstep (se 2 (by rfl) ⟨70347654, by rfl⟩ : syracuseStep 187593745 = 140695309) B140695309
theorem B250124993 : Blo 1949435 250124993 := bstep (se 2 (by rfl) ⟨93796872, by rfl⟩ : syracuseStep 250124993 = 187593745) B187593745
theorem B166749995 : Blo 1949435 166749995 := bstep (se 1 (by rfl) ⟨125062496, by rfl⟩ : syracuseStep 166749995 = 250124993) B250124993
theorem B111166663 : Blo 1949435 111166663 := bstep (se 1 (by rfl) ⟨83374997, by rfl⟩ : syracuseStep 111166663 = 166749995) B166749995
theorem B148222217 : Blo 1949435 148222217 := bstep (se 2 (by rfl) ⟨55583331, by rfl⟩ : syracuseStep 148222217 = 111166663) B111166663
theorem B98814811 : Blo 1949435 98814811 := bstep (se 1 (by rfl) ⟨74111108, by rfl⟩ : syracuseStep 98814811 = 148222217) B148222217
theorem B131753081 : Blo 1949435 131753081 := bstep (se 2 (by rfl) ⟨49407405, by rfl⟩ : syracuseStep 131753081 = 98814811) B98814811
theorem B351341549 : Blo 1949435 351341549 := bstep (se 3 (by rfl) ⟨65876540, by rfl⟩ : syracuseStep 351341549 = 131753081) B131753081
theorem B234227699 : Blo 1949435 234227699 := bstep (se 1 (by rfl) ⟨175670774, by rfl⟩ : syracuseStep 234227699 = 351341549) B351341549
theorem B156151799 : Blo 1949435 156151799 := bstep (se 1 (by rfl) ⟨117113849, by rfl⟩ : syracuseStep 156151799 = 234227699) B234227699
theorem B104101199 : Blo 1949435 104101199 := bstep (se 1 (by rfl) ⟨78075899, by rfl⟩ : syracuseStep 104101199 = 156151799) B156151799
theorem B69400799 : Blo 1949435 69400799 := bstep (se 1 (by rfl) ⟨52050599, by rfl⟩ : syracuseStep 69400799 = 104101199) B104101199
theorem B46267199 : Blo 1949435 46267199 := bstep (se 1 (by rfl) ⟨34700399, by rfl⟩ : syracuseStep 46267199 = 69400799) B69400799
theorem B30844799 : Blo 1949435 30844799 := bstep (se 1 (by rfl) ⟨23133599, by rfl⟩ : syracuseStep 30844799 = 46267199) B46267199
theorem B20563199 : Blo 1949435 20563199 := bstep (se 1 (by rfl) ⟨15422399, by rfl⟩ : syracuseStep 20563199 = 30844799) B30844799
theorem B13708799 : Blo 1949435 13708799 := bstep (se 1 (by rfl) ⟨10281599, by rfl⟩ : syracuseStep 13708799 = 20563199) B20563199
theorem B9139199 : Blo 1949435 9139199 := bstep (se 1 (by rfl) ⟨6854399, by rfl⟩ : syracuseStep 9139199 = 13708799) B13708799
theorem B97484789 : Blo 1949435 97484789 := bstep (se 5 (by rfl) ⟨4569599, by rfl⟩ : syracuseStep 97484789 = 9139199) B9139199
theorem B64989859 : Blo 1949435 64989859 := bstep (se 1 (by rfl) ⟨48742394, by rfl⟩ : syracuseStep 64989859 = 97484789) B97484789
theorem B86653145 : Blo 1949435 86653145 := bstep (se 2 (by rfl) ⟨32494929, by rfl⟩ : syracuseStep 86653145 = 64989859) B64989859
theorem B57768763 : Blo 1949435 57768763 := bstep (se 1 (by rfl) ⟨43326572, by rfl⟩ : syracuseStep 57768763 = 86653145) B86653145
theorem B77025017 : Blo 1949435 77025017 := bstep (se 2 (by rfl) ⟨28884381, by rfl⟩ : syracuseStep 77025017 = 57768763) B57768763
theorem B205400045 : Blo 1949435 205400045 := bstep (se 3 (by rfl) ⟨38512508, by rfl⟩ : syracuseStep 205400045 = 77025017) B77025017
theorem B136933363 : Blo 1949435 136933363 := bstep (se 1 (by rfl) ⟨102700022, by rfl⟩ : syracuseStep 136933363 = 205400045) B205400045
theorem B182577817 : Blo 1949435 182577817 := bstep (se 2 (by rfl) ⟨68466681, by rfl⟩ : syracuseStep 182577817 = 136933363) B136933363
theorem B243437089 : Blo 1949435 243437089 := bstep (se 2 (by rfl) ⟨91288908, by rfl⟩ : syracuseStep 243437089 = 182577817) B182577817
theorem B324582785 : Blo 1949435 324582785 := bstep (se 2 (by rfl) ⟨121718544, by rfl⟩ : syracuseStep 324582785 = 243437089) B243437089
theorem B216388523 : Blo 1949435 216388523 := bstep (se 1 (by rfl) ⟨162291392, by rfl⟩ : syracuseStep 216388523 = 324582785) B324582785
theorem B144259015 : Blo 1949435 144259015 := bstep (se 1 (by rfl) ⟨108194261, by rfl⟩ : syracuseStep 144259015 = 216388523) B216388523
theorem B192345353 : Blo 1949435 192345353 := bstep (se 2 (by rfl) ⟨72129507, by rfl⟩ : syracuseStep 192345353 = 144259015) B144259015
theorem B128230235 : Blo 1949435 128230235 := bstep (se 1 (by rfl) ⟨96172676, by rfl⟩ : syracuseStep 128230235 = 192345353) B192345353
theorem B85486823 : Blo 1949435 85486823 := bstep (se 1 (by rfl) ⟨64115117, by rfl⟩ : syracuseStep 85486823 = 128230235) B128230235
theorem B56991215 : Blo 1949435 56991215 := bstep (se 1 (by rfl) ⟨42743411, by rfl⟩ : syracuseStep 56991215 = 85486823) B85486823
theorem B37994143 : Blo 1949435 37994143 := bstep (se 1 (by rfl) ⟨28495607, by rfl⟩ : syracuseStep 37994143 = 56991215) B56991215
theorem B50658857 : Blo 1949435 50658857 := bstep (se 2 (by rfl) ⟨18997071, by rfl⟩ : syracuseStep 50658857 = 37994143) B37994143
theorem B33772571 : Blo 1949435 33772571 := bstep (se 1 (by rfl) ⟨25329428, by rfl⟩ : syracuseStep 33772571 = 50658857) B50658857
theorem B22515047 : Blo 1949435 22515047 := bstep (se 1 (by rfl) ⟨16886285, by rfl⟩ : syracuseStep 22515047 = 33772571) B33772571
theorem B15010031 : Blo 1949435 15010031 := bstep (se 1 (by rfl) ⟨11257523, by rfl⟩ : syracuseStep 15010031 = 22515047) B22515047
theorem B10006687 : Blo 1949435 10006687 := bstep (se 1 (by rfl) ⟨7505015, by rfl⟩ : syracuseStep 10006687 = 15010031) B15010031
theorem B13342249 : Blo 1949435 13342249 := bstep (se 2 (by rfl) ⟨5003343, by rfl⟩ : syracuseStep 13342249 = 10006687) B10006687
theorem B71158661 : Blo 1949435 71158661 := bstep (se 4 (by rfl) ⟨6671124, by rfl⟩ : syracuseStep 71158661 = 13342249) B13342249
theorem B47439107 : Blo 1949435 47439107 := bstep (se 1 (by rfl) ⟨35579330, by rfl⟩ : syracuseStep 47439107 = 71158661) B71158661
theorem B31626071 : Blo 1949435 31626071 := bstep (se 1 (by rfl) ⟨23719553, by rfl⟩ : syracuseStep 31626071 = 47439107) B47439107
theorem B21084047 : Blo 1949435 21084047 := bstep (se 1 (by rfl) ⟨15813035, by rfl⟩ : syracuseStep 21084047 = 31626071) B31626071
theorem B14056031 : Blo 1949435 14056031 := bstep (se 1 (by rfl) ⟨10542023, by rfl⟩ : syracuseStep 14056031 = 21084047) B21084047
theorem B9370687 : Blo 1949435 9370687 := bstep (se 1 (by rfl) ⟨7028015, by rfl⟩ : syracuseStep 9370687 = 14056031) B14056031
theorem B12494249 : Blo 1949435 12494249 := bstep (se 2 (by rfl) ⟨4685343, by rfl⟩ : syracuseStep 12494249 = 9370687) B9370687
theorem B8329499 : Blo 1949435 8329499 := bstep (se 1 (by rfl) ⟨6247124, by rfl⟩ : syracuseStep 8329499 = 12494249) B12494249
theorem B5552999 : Blo 1949435 5552999 := bstep (se 1 (by rfl) ⟨4164749, by rfl⟩ : syracuseStep 5552999 = 8329499) B8329499
theorem B3701999 : Blo 1949435 3701999 := bstep (se 1 (by rfl) ⟨2776499, by rfl⟩ : syracuseStep 3701999 = 5552999) B5552999
theorem B2467999 : Blo 1949435 2467999 := bstep (se 1 (by rfl) ⟨1850999, by rfl⟩ : syracuseStep 2467999 = 3701999) B3701999
theorem B3290665 : Blo 1949435 3290665 := bstep (se 2 (by rfl) ⟨1233999, by rfl⟩ : syracuseStep 3290665 = 2467999) B2467999
theorem B4387553 : Blo 1949435 4387553 := bstep (se 2 (by rfl) ⟨1645332, by rfl⟩ : syracuseStep 4387553 = 3290665) B3290665
theorem B2925035 : Blo 1949435 2925035 := bstep (se 1 (by rfl) ⟨2193776, by rfl⟩ : syracuseStep 2925035 = 4387553) B4387553
theorem B1950023 : Blo 1949435 1950023 := bstep (se 1 (by rfl) ⟨1462517, by rfl⟩ : syracuseStep 1950023 = 2925035) B2925035
theorem B2193781 : Blo 1949435 2193781 := bbase (se 5 (by rfl) ⟨102833, by rfl⟩ : syracuseStep 2193781 = 205667) (by norm_num)
theorem B2925041 : Blo 1949435 2925041 := bstep (se 2 (by rfl) ⟨1096890, by rfl⟩ : syracuseStep 2925041 = 2193781) B2193781
theorem B1950027 : Blo 1949435 1950027 := bstep (se 1 (by rfl) ⟨1462520, by rfl⟩ : syracuseStep 1950027 = 2925041) B2925041
theorem B2468009 : Blo 1949435 2468009 := bbase (se 2 (by rfl) ⟨925503, by rfl⟩ : syracuseStep 2468009 = 1851007) (by norm_num)
theorem B6581357 : Blo 1949435 6581357 := bstep (se 3 (by rfl) ⟨1234004, by rfl⟩ : syracuseStep 6581357 = 2468009) B2468009
theorem B4387571 : Blo 1949435 4387571 := bstep (se 1 (by rfl) ⟨3290678, by rfl⟩ : syracuseStep 4387571 = 6581357) B6581357
theorem B2925047 : Blo 1949435 2925047 := bstep (se 1 (by rfl) ⟨2193785, by rfl⟩ : syracuseStep 2925047 = 4387571) B4387571
theorem B1950031 : Blo 1949435 1950031 := bstep (se 1 (by rfl) ⟨1462523, by rfl⟩ : syracuseStep 1950031 = 2925047) B2925047
theorem B2925053 : Blo 1949435 2925053 := bbase (se 3 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 2925053 = 1096895) (by norm_num)
theorem B1950035 : Blo 1949435 1950035 := bstep (se 1 (by rfl) ⟨1462526, by rfl⟩ : syracuseStep 1950035 = 2925053) B2925053
theorem B4387589 : Blo 1949435 4387589 := bbase (se 4 (by rfl) ⟨411336, by rfl⟩ : syracuseStep 4387589 = 822673) (by norm_num)
theorem B2925059 : Blo 1949435 2925059 := bstep (se 1 (by rfl) ⟨2193794, by rfl⟩ : syracuseStep 2925059 = 4387589) B4387589
theorem B1950039 : Blo 1949435 1950039 := bstep (se 1 (by rfl) ⟨1462529, by rfl⟩ : syracuseStep 1950039 = 2925059) B2925059
theorem B3702037 : Blo 1949435 3702037 := bbase (se 6 (by rfl) ⟨86766, by rfl⟩ : syracuseStep 3702037 = 173533) (by norm_num)
theorem B4936049 : Blo 1949435 4936049 := bstep (se 2 (by rfl) ⟨1851018, by rfl⟩ : syracuseStep 4936049 = 3702037) B3702037
theorem B3290699 : Blo 1949435 3290699 := bstep (se 1 (by rfl) ⟨2468024, by rfl⟩ : syracuseStep 3290699 = 4936049) B4936049
theorem B2193799 : Blo 1949435 2193799 := bstep (se 1 (by rfl) ⟨1645349, by rfl⟩ : syracuseStep 2193799 = 3290699) B3290699
theorem B2925065 : Blo 1949435 2925065 := bstep (se 2 (by rfl) ⟨1096899, by rfl⟩ : syracuseStep 2925065 = 2193799) B2193799
theorem B1950043 : Blo 1949435 1950043 := bstep (se 1 (by rfl) ⟨1462532, by rfl⟩ : syracuseStep 1950043 = 2925065) B2925065
theorem B9872117 : Blo 1949435 9872117 := bbase (se 5 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 9872117 = 925511) (by norm_num)
theorem B6581411 : Blo 1949435 6581411 := bstep (se 1 (by rfl) ⟨4936058, by rfl⟩ : syracuseStep 6581411 = 9872117) B9872117
theorem B4387607 : Blo 1949435 4387607 := bstep (se 1 (by rfl) ⟨3290705, by rfl⟩ : syracuseStep 4387607 = 6581411) B6581411
theorem B2925071 : Blo 1949435 2925071 := bstep (se 1 (by rfl) ⟨2193803, by rfl⟩ : syracuseStep 2925071 = 4387607) B4387607
theorem B1950047 : Blo 1949435 1950047 := bstep (se 1 (by rfl) ⟨1462535, by rfl⟩ : syracuseStep 1950047 = 2925071) B2925071
theorem B2925077 : Blo 1949435 2925077 := bbase (se 6 (by rfl) ⟨68556, by rfl⟩ : syracuseStep 2925077 = 137113) (by norm_num)
theorem B1950051 : Blo 1949435 1950051 := bstep (se 1 (by rfl) ⟨1462538, by rfl⟩ : syracuseStep 1950051 = 2925077) B2925077
theorem B3123613 : Blo 1949435 3123613 := bbase (se 3 (by rfl) ⟨585677, by rfl⟩ : syracuseStep 3123613 = 1171355) (by norm_num)
theorem B16659269 : Blo 1949435 16659269 := bstep (se 4 (by rfl) ⟨1561806, by rfl⟩ : syracuseStep 16659269 = 3123613) B3123613
theorem B11106179 : Blo 1949435 11106179 := bstep (se 1 (by rfl) ⟨8329634, by rfl⟩ : syracuseStep 11106179 = 16659269) B16659269
theorem B7404119 : Blo 1949435 7404119 := bstep (se 1 (by rfl) ⟨5553089, by rfl⟩ : syracuseStep 7404119 = 11106179) B11106179
theorem B4936079 : Blo 1949435 4936079 := bstep (se 1 (by rfl) ⟨3702059, by rfl⟩ : syracuseStep 4936079 = 7404119) B7404119
theorem B3290719 : Blo 1949435 3290719 := bstep (se 1 (by rfl) ⟨2468039, by rfl⟩ : syracuseStep 3290719 = 4936079) B4936079
theorem B4387625 : Blo 1949435 4387625 := bstep (se 2 (by rfl) ⟨1645359, by rfl⟩ : syracuseStep 4387625 = 3290719) B3290719
theorem B2925083 : Blo 1949435 2925083 := bstep (se 1 (by rfl) ⟨2193812, by rfl⟩ : syracuseStep 2925083 = 4387625) B4387625
theorem B1950055 : Blo 1949435 1950055 := bstep (se 1 (by rfl) ⟨1462541, by rfl⟩ : syracuseStep 1950055 = 2925083) B2925083
theorem B2193817 : Blo 1949435 2193817 := bbase (se 2 (by rfl) ⟨822681, by rfl⟩ : syracuseStep 2193817 = 1645363) (by norm_num)
theorem B2925089 : Blo 1949435 2925089 := bstep (se 2 (by rfl) ⟨1096908, by rfl⟩ : syracuseStep 2925089 = 2193817) B2193817
theorem B1950059 : Blo 1949435 1950059 := bstep (se 1 (by rfl) ⟨1462544, by rfl⟩ : syracuseStep 1950059 = 2925089) B2925089
theorem B7404149 : Blo 1949435 7404149 := bbase (se 5 (by rfl) ⟨347069, by rfl⟩ : syracuseStep 7404149 = 694139) (by norm_num)
theorem B4936099 : Blo 1949435 4936099 := bstep (se 1 (by rfl) ⟨3702074, by rfl⟩ : syracuseStep 4936099 = 7404149) B7404149
theorem B6581465 : Blo 1949435 6581465 := bstep (se 2 (by rfl) ⟨2468049, by rfl⟩ : syracuseStep 6581465 = 4936099) B4936099
theorem B4387643 : Blo 1949435 4387643 := bstep (se 1 (by rfl) ⟨3290732, by rfl⟩ : syracuseStep 4387643 = 6581465) B6581465
theorem B2925095 : Blo 1949435 2925095 := bstep (se 1 (by rfl) ⟨2193821, by rfl⟩ : syracuseStep 2925095 = 4387643) B4387643
theorem B1950063 : Blo 1949435 1950063 := bstep (se 1 (by rfl) ⟨1462547, by rfl⟩ : syracuseStep 1950063 = 2925095) B2925095
theorem B2925101 : Blo 1949435 2925101 := bbase (se 3 (by rfl) ⟨548456, by rfl⟩ : syracuseStep 2925101 = 1096913) (by norm_num)
theorem B1950067 : Blo 1949435 1950067 := bstep (se 1 (by rfl) ⟨1462550, by rfl⟩ : syracuseStep 1950067 = 2925101) B2925101
theorem B4387661 : Blo 1949435 4387661 := bbase (se 3 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 4387661 = 1645373) (by norm_num)
theorem B2925107 : Blo 1949435 2925107 := bstep (se 1 (by rfl) ⟨2193830, by rfl⟩ : syracuseStep 2925107 = 4387661) B4387661
theorem B1950071 : Blo 1949435 1950071 := bstep (se 1 (by rfl) ⟨1462553, by rfl⟩ : syracuseStep 1950071 = 2925107) B2925107
theorem B2468065 : Blo 1949435 2468065 := bbase (se 2 (by rfl) ⟨925524, by rfl⟩ : syracuseStep 2468065 = 1851049) (by norm_num)
theorem B3290753 : Blo 1949435 3290753 := bstep (se 2 (by rfl) ⟨1234032, by rfl⟩ : syracuseStep 3290753 = 2468065) B2468065
theorem B2193835 : Blo 1949435 2193835 := bstep (se 1 (by rfl) ⟨1645376, by rfl⟩ : syracuseStep 2193835 = 3290753) B3290753
theorem B2925113 : Blo 1949435 2925113 := bstep (se 2 (by rfl) ⟨1096917, by rfl⟩ : syracuseStep 2925113 = 2193835) B2193835
theorem B1950075 : Blo 1949435 1950075 := bstep (se 1 (by rfl) ⟨1462556, by rfl⟩ : syracuseStep 1950075 = 2925113) B2925113
theorem B22212629 : Blo 1949435 22212629 := bbase (se 6 (by rfl) ⟨520608, by rfl⟩ : syracuseStep 22212629 = 1041217) (by norm_num)
theorem B14808419 : Blo 1949435 14808419 := bstep (se 1 (by rfl) ⟨11106314, by rfl⟩ : syracuseStep 14808419 = 22212629) B22212629
theorem B9872279 : Blo 1949435 9872279 := bstep (se 1 (by rfl) ⟨7404209, by rfl⟩ : syracuseStep 9872279 = 14808419) B14808419
theorem B6581519 : Blo 1949435 6581519 := bstep (se 1 (by rfl) ⟨4936139, by rfl⟩ : syracuseStep 6581519 = 9872279) B9872279
theorem B4387679 : Blo 1949435 4387679 := bstep (se 1 (by rfl) ⟨3290759, by rfl⟩ : syracuseStep 4387679 = 6581519) B6581519
theorem B2925119 : Blo 1949435 2925119 := bstep (se 1 (by rfl) ⟨2193839, by rfl⟩ : syracuseStep 2925119 = 4387679) B4387679
theorem B1950079 : Blo 1949435 1950079 := bstep (se 1 (by rfl) ⟨1462559, by rfl⟩ : syracuseStep 1950079 = 2925119) B2925119
theorem B2925125 : Blo 1949435 2925125 := bbase (se 4 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 2925125 = 548461) (by norm_num)
theorem B1950083 : Blo 1949435 1950083 := bstep (se 1 (by rfl) ⟨1462562, by rfl⟩ : syracuseStep 1950083 = 2925125) B2925125
theorem B3290773 : Blo 1949435 3290773 := bbase (se 6 (by rfl) ⟨77127, by rfl⟩ : syracuseStep 3290773 = 154255) (by norm_num)
theorem B4387697 : Blo 1949435 4387697 := bstep (se 2 (by rfl) ⟨1645386, by rfl⟩ : syracuseStep 4387697 = 3290773) B3290773
theorem B2925131 : Blo 1949435 2925131 := bstep (se 1 (by rfl) ⟨2193848, by rfl⟩ : syracuseStep 2925131 = 4387697) B4387697
theorem B1950087 : Blo 1949435 1950087 := bstep (se 1 (by rfl) ⟨1462565, by rfl⟩ : syracuseStep 1950087 = 2925131) B2925131
theorem B2193853 : Blo 1949435 2193853 := bbase (se 3 (by rfl) ⟨411347, by rfl⟩ : syracuseStep 2193853 = 822695) (by norm_num)
theorem B2925137 : Blo 1949435 2925137 := bstep (se 2 (by rfl) ⟨1096926, by rfl⟩ : syracuseStep 2925137 = 2193853) B2193853
theorem B1950091 : Blo 1949435 1950091 := bstep (se 1 (by rfl) ⟨1462568, by rfl⟩ : syracuseStep 1950091 = 2925137) B2925137
theorem B6581573 : Blo 1949435 6581573 := bbase (se 4 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 6581573 = 1234045) (by norm_num)
theorem B4387715 : Blo 1949435 4387715 := bstep (se 1 (by rfl) ⟨3290786, by rfl⟩ : syracuseStep 4387715 = 6581573) B6581573
theorem B2925143 : Blo 1949435 2925143 := bstep (se 1 (by rfl) ⟨2193857, by rfl⟩ : syracuseStep 2925143 = 4387715) B4387715
theorem B1950095 : Blo 1949435 1950095 := bstep (se 1 (by rfl) ⟨1462571, by rfl⟩ : syracuseStep 1950095 = 2925143) B2925143
theorem B2925149 : Blo 1949435 2925149 := bbase (se 3 (by rfl) ⟨548465, by rfl⟩ : syracuseStep 2925149 = 1096931) (by norm_num)
theorem B1950099 : Blo 1949435 1950099 := bstep (se 1 (by rfl) ⟨1462574, by rfl⟩ : syracuseStep 1950099 = 2925149) B2925149
theorem B4387733 : Blo 1949435 4387733 := bbase (se 6 (by rfl) ⟨102837, by rfl⟩ : syracuseStep 4387733 = 205675) (by norm_num)
theorem B2925155 : Blo 1949435 2925155 := bstep (se 1 (by rfl) ⟨2193866, by rfl⟩ : syracuseStep 2925155 = 4387733) B4387733
theorem B1950103 : Blo 1949435 1950103 := bstep (se 1 (by rfl) ⟨1462577, by rfl⟩ : syracuseStep 1950103 = 2925155) B2925155
theorem B2342773 : Blo 1949435 2342773 := bbase (se 5 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 2342773 = 219635) (by norm_num)
theorem B3123697 : Blo 1949435 3123697 := bstep (se 2 (by rfl) ⟨1171386, by rfl⟩ : syracuseStep 3123697 = 2342773) B2342773
theorem B4164929 : Blo 1949435 4164929 := bstep (se 2 (by rfl) ⟨1561848, by rfl⟩ : syracuseStep 4164929 = 3123697) B3123697
theorem B2776619 : Blo 1949435 2776619 := bstep (se 1 (by rfl) ⟨2082464, by rfl⟩ : syracuseStep 2776619 = 4164929) B4164929
theorem B7404317 : Blo 1949435 7404317 := bstep (se 3 (by rfl) ⟨1388309, by rfl⟩ : syracuseStep 7404317 = 2776619) B2776619
theorem B4936211 : Blo 1949435 4936211 := bstep (se 1 (by rfl) ⟨3702158, by rfl⟩ : syracuseStep 4936211 = 7404317) B7404317
theorem B3290807 : Blo 1949435 3290807 := bstep (se 1 (by rfl) ⟨2468105, by rfl⟩ : syracuseStep 3290807 = 4936211) B4936211
theorem B2193871 : Blo 1949435 2193871 := bstep (se 1 (by rfl) ⟨1645403, by rfl⟩ : syracuseStep 2193871 = 3290807) B3290807
theorem B2925161 : Blo 1949435 2925161 := bstep (se 2 (by rfl) ⟨1096935, by rfl⟩ : syracuseStep 2925161 = 2193871) B2193871
theorem B1950107 : Blo 1949435 1950107 := bstep (se 1 (by rfl) ⟨1462580, by rfl⟩ : syracuseStep 1950107 = 2925161) B2925161
theorem B2342777 : Blo 1949435 2342777 := bbase (se 2 (by rfl) ⟨878541, by rfl⟩ : syracuseStep 2342777 = 1757083) (by norm_num)
theorem B6247405 : Blo 1949435 6247405 := bstep (se 3 (by rfl) ⟨1171388, by rfl⟩ : syracuseStep 6247405 = 2342777) B2342777
theorem B8329873 : Blo 1949435 8329873 := bstep (se 2 (by rfl) ⟨3123702, by rfl⟩ : syracuseStep 8329873 = 6247405) B6247405
theorem B11106497 : Blo 1949435 11106497 := bstep (se 2 (by rfl) ⟨4164936, by rfl⟩ : syracuseStep 11106497 = 8329873) B8329873
theorem B7404331 : Blo 1949435 7404331 := bstep (se 1 (by rfl) ⟨5553248, by rfl⟩ : syracuseStep 7404331 = 11106497) B11106497
theorem B9872441 : Blo 1949435 9872441 := bstep (se 2 (by rfl) ⟨3702165, by rfl⟩ : syracuseStep 9872441 = 7404331) B7404331
theorem B6581627 : Blo 1949435 6581627 := bstep (se 1 (by rfl) ⟨4936220, by rfl⟩ : syracuseStep 6581627 = 9872441) B9872441
theorem B4387751 : Blo 1949435 4387751 := bstep (se 1 (by rfl) ⟨3290813, by rfl⟩ : syracuseStep 4387751 = 6581627) B6581627
theorem B2925167 : Blo 1949435 2925167 := bstep (se 1 (by rfl) ⟨2193875, by rfl⟩ : syracuseStep 2925167 = 4387751) B4387751
theorem B1950111 : Blo 1949435 1950111 := bstep (se 1 (by rfl) ⟨1462583, by rfl⟩ : syracuseStep 1950111 = 2925167) B2925167
theorem B2925173 : Blo 1949435 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B1950115 : Blo 1949435 1950115 := bstep (se 1 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 1950115 = 2925173) B2925173
theorem B3702181 : Blo 1949435 3702181 := bbase (se 4 (by rfl) ⟨347079, by rfl⟩ : syracuseStep 3702181 = 694159) (by norm_num)
theorem B4936241 : Blo 1949435 4936241 := bstep (se 2 (by rfl) ⟨1851090, by rfl⟩ : syracuseStep 4936241 = 3702181) B3702181
theorem B3290827 : Blo 1949435 3290827 := bstep (se 1 (by rfl) ⟨2468120, by rfl⟩ : syracuseStep 3290827 = 4936241) B4936241
theorem B4387769 : Blo 1949435 4387769 := bstep (se 2 (by rfl) ⟨1645413, by rfl⟩ : syracuseStep 4387769 = 3290827) B3290827
theorem B2925179 : Blo 1949435 2925179 := bstep (se 1 (by rfl) ⟨2193884, by rfl⟩ : syracuseStep 2925179 = 4387769) B4387769
theorem B1950119 : Blo 1949435 1950119 := bstep (se 1 (by rfl) ⟨1462589, by rfl⟩ : syracuseStep 1950119 = 2925179) B2925179
theorem B2193889 : Blo 1949435 2193889 := bbase (se 2 (by rfl) ⟨822708, by rfl⟩ : syracuseStep 2193889 = 1645417) (by norm_num)
theorem B2925185 : Blo 1949435 2925185 := bstep (se 2 (by rfl) ⟨1096944, by rfl⟩ : syracuseStep 2925185 = 2193889) B2193889
theorem B1950123 : Blo 1949435 1950123 := bstep (se 1 (by rfl) ⟨1462592, by rfl⟩ : syracuseStep 1950123 = 2925185) B2925185
theorem B4936261 : Blo 1949435 4936261 := bbase (se 4 (by rfl) ⟨462774, by rfl⟩ : syracuseStep 4936261 = 925549) (by norm_num)
theorem B6581681 : Blo 1949435 6581681 := bstep (se 2 (by rfl) ⟨2468130, by rfl⟩ : syracuseStep 6581681 = 4936261) B4936261
theorem B4387787 : Blo 1949435 4387787 := bstep (se 1 (by rfl) ⟨3290840, by rfl⟩ : syracuseStep 4387787 = 6581681) B6581681
theorem B2925191 : Blo 1949435 2925191 := bstep (se 1 (by rfl) ⟨2193893, by rfl⟩ : syracuseStep 2925191 = 4387787) B4387787
theorem B1950127 : Blo 1949435 1950127 := bstep (se 1 (by rfl) ⟨1462595, by rfl⟩ : syracuseStep 1950127 = 2925191) B2925191
theorem B2925197 : Blo 1949435 2925197 := bbase (se 3 (by rfl) ⟨548474, by rfl⟩ : syracuseStep 2925197 = 1096949) (by norm_num)
theorem B1950131 : Blo 1949435 1950131 := bstep (se 1 (by rfl) ⟨1462598, by rfl⟩ : syracuseStep 1950131 = 2925197) B2925197
theorem B4387805 : Blo 1949435 4387805 := bbase (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) (by norm_num)
theorem B2925203 : Blo 1949435 2925203 := bstep (se 1 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 2925203 = 4387805) B4387805
theorem B1950135 : Blo 1949435 1950135 := bstep (se 1 (by rfl) ⟨1462601, by rfl⟩ : syracuseStep 1950135 = 2925203) B2925203
theorem B3290861 : Blo 1949435 3290861 := bbase (se 3 (by rfl) ⟨617036, by rfl⟩ : syracuseStep 3290861 = 1234073) (by norm_num)
theorem B2193907 : Blo 1949435 2193907 := bstep (se 1 (by rfl) ⟨1645430, by rfl⟩ : syracuseStep 2193907 = 3290861) B3290861
theorem B2925209 : Blo 1949435 2925209 := bstep (se 2 (by rfl) ⟨1096953, by rfl⟩ : syracuseStep 2925209 = 2193907) B2193907
theorem B1950139 : Blo 1949435 1950139 := bstep (se 1 (by rfl) ⟨1462604, by rfl⟩ : syracuseStep 1950139 = 2925209) B2925209
theorem B7505477 : Blo 1949435 7505477 := bbase (se 4 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 7505477 = 1407277) (by norm_num)
theorem B5003651 : Blo 1949435 5003651 := bstep (se 1 (by rfl) ⟨3752738, by rfl⟩ : syracuseStep 5003651 = 7505477) B7505477
theorem B13343069 : Blo 1949435 13343069 := bstep (se 3 (by rfl) ⟨2501825, by rfl⟩ : syracuseStep 13343069 = 5003651) B5003651
theorem B8895379 : Blo 1949435 8895379 := bstep (se 1 (by rfl) ⟨6671534, by rfl⟩ : syracuseStep 8895379 = 13343069) B13343069
theorem B11860505 : Blo 1949435 11860505 := bstep (se 2 (by rfl) ⟨4447689, by rfl⟩ : syracuseStep 11860505 = 8895379) B8895379
theorem B7907003 : Blo 1949435 7907003 := bstep (se 1 (by rfl) ⟨5930252, by rfl⟩ : syracuseStep 7907003 = 11860505) B11860505
theorem B5271335 : Blo 1949435 5271335 := bstep (se 1 (by rfl) ⟨3953501, by rfl⟩ : syracuseStep 5271335 = 7907003) B7907003
theorem B3514223 : Blo 1949435 3514223 := bstep (se 1 (by rfl) ⟨2635667, by rfl⟩ : syracuseStep 3514223 = 5271335) B5271335
theorem B9371261 : Blo 1949435 9371261 := bstep (se 3 (by rfl) ⟨1757111, by rfl⟩ : syracuseStep 9371261 = 3514223) B3514223
theorem B24990029 : Blo 1949435 24990029 := bstep (se 3 (by rfl) ⟨4685630, by rfl⟩ : syracuseStep 24990029 = 9371261) B9371261
theorem B16660019 : Blo 1949435 16660019 := bstep (se 1 (by rfl) ⟨12495014, by rfl⟩ : syracuseStep 16660019 = 24990029) B24990029
theorem B11106679 : Blo 1949435 11106679 := bstep (se 1 (by rfl) ⟨8330009, by rfl⟩ : syracuseStep 11106679 = 16660019) B16660019
theorem B14808905 : Blo 1949435 14808905 := bstep (se 2 (by rfl) ⟨5553339, by rfl⟩ : syracuseStep 14808905 = 11106679) B11106679
theorem B9872603 : Blo 1949435 9872603 := bstep (se 1 (by rfl) ⟨7404452, by rfl⟩ : syracuseStep 9872603 = 14808905) B14808905
theorem B6581735 : Blo 1949435 6581735 := bstep (se 1 (by rfl) ⟨4936301, by rfl⟩ : syracuseStep 6581735 = 9872603) B9872603
theorem B4387823 : Blo 1949435 4387823 := bstep (se 1 (by rfl) ⟨3290867, by rfl⟩ : syracuseStep 4387823 = 6581735) B6581735
theorem B2925215 : Blo 1949435 2925215 := bstep (se 1 (by rfl) ⟨2193911, by rfl⟩ : syracuseStep 2925215 = 4387823) B4387823
theorem B1950143 : Blo 1949435 1950143 := bstep (se 1 (by rfl) ⟨1462607, by rfl⟩ : syracuseStep 1950143 = 2925215) B2925215
theorem B2925221 : Blo 1949435 2925221 := bbase (se 4 (by rfl) ⟨274239, by rfl⟩ : syracuseStep 2925221 = 548479) (by norm_num)
theorem B1950147 : Blo 1949435 1950147 := bstep (se 1 (by rfl) ⟨1462610, by rfl⟩ : syracuseStep 1950147 = 2925221) B2925221
theorem B2468161 : Blo 1949435 2468161 := bbase (se 2 (by rfl) ⟨925560, by rfl⟩ : syracuseStep 2468161 = 1851121) (by norm_num)
theorem B3290881 : Blo 1949435 3290881 := bstep (se 2 (by rfl) ⟨1234080, by rfl⟩ : syracuseStep 3290881 = 2468161) B2468161
theorem B4387841 : Blo 1949435 4387841 := bstep (se 2 (by rfl) ⟨1645440, by rfl⟩ : syracuseStep 4387841 = 3290881) B3290881
theorem B2925227 : Blo 1949435 2925227 := bstep (se 1 (by rfl) ⟨2193920, by rfl⟩ : syracuseStep 2925227 = 4387841) B4387841
theorem B1950151 : Blo 1949435 1950151 := bstep (se 1 (by rfl) ⟨1462613, by rfl⟩ : syracuseStep 1950151 = 2925227) B2925227
theorem B2193925 : Blo 1949435 2193925 := bbase (se 4 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 2193925 = 411361) (by norm_num)
theorem B2925233 : Blo 1949435 2925233 := bstep (se 2 (by rfl) ⟨1096962, by rfl⟩ : syracuseStep 2925233 = 2193925) B2193925
theorem B1950155 : Blo 1949435 1950155 := bstep (se 1 (by rfl) ⟨1462616, by rfl⟩ : syracuseStep 1950155 = 2925233) B2925233
theorem B2776693 : Blo 1949435 2776693 := bbase (se 5 (by rfl) ⟨130157, by rfl⟩ : syracuseStep 2776693 = 260315) (by norm_num)
theorem B3702257 : Blo 1949435 3702257 := bstep (se 2 (by rfl) ⟨1388346, by rfl⟩ : syracuseStep 3702257 = 2776693) B2776693
theorem B2468171 : Blo 1949435 2468171 := bstep (se 1 (by rfl) ⟨1851128, by rfl⟩ : syracuseStep 2468171 = 3702257) B3702257
theorem B6581789 : Blo 1949435 6581789 := bstep (se 3 (by rfl) ⟨1234085, by rfl⟩ : syracuseStep 6581789 = 2468171) B2468171
theorem B4387859 : Blo 1949435 4387859 := bstep (se 1 (by rfl) ⟨3290894, by rfl⟩ : syracuseStep 4387859 = 6581789) B6581789
theorem B2925239 : Blo 1949435 2925239 := bstep (se 1 (by rfl) ⟨2193929, by rfl⟩ : syracuseStep 2925239 = 4387859) B4387859
theorem B1950159 : Blo 1949435 1950159 := bstep (se 1 (by rfl) ⟨1462619, by rfl⟩ : syracuseStep 1950159 = 2925239) B2925239
theorem B2925245 : Blo 1949435 2925245 := bbase (se 3 (by rfl) ⟨548483, by rfl⟩ : syracuseStep 2925245 = 1096967) (by norm_num)
theorem B1950163 : Blo 1949435 1950163 := bstep (se 1 (by rfl) ⟨1462622, by rfl⟩ : syracuseStep 1950163 = 2925245) B2925245
theorem B4387877 : Blo 1949435 4387877 := bbase (se 4 (by rfl) ⟨411363, by rfl⟩ : syracuseStep 4387877 = 822727) (by norm_num)
theorem B2925251 : Blo 1949435 2925251 := bstep (se 1 (by rfl) ⟨2193938, by rfl⟩ : syracuseStep 2925251 = 4387877) B4387877
theorem B1950167 : Blo 1949435 1950167 := bstep (se 1 (by rfl) ⟨1462625, by rfl⟩ : syracuseStep 1950167 = 2925251) B2925251
theorem B4936373 : Blo 1949435 4936373 := bbase (se 5 (by rfl) ⟨231392, by rfl⟩ : syracuseStep 4936373 = 462785) (by norm_num)
theorem B3290915 : Blo 1949435 3290915 := bstep (se 1 (by rfl) ⟨2468186, by rfl⟩ : syracuseStep 3290915 = 4936373) B4936373
theorem B2193943 : Blo 1949435 2193943 := bstep (se 1 (by rfl) ⟨1645457, by rfl⟩ : syracuseStep 2193943 = 3290915) B3290915
theorem B2925257 : Blo 1949435 2925257 := bstep (se 2 (by rfl) ⟨1096971, by rfl⟩ : syracuseStep 2925257 = 2193943) B2193943
theorem B1950171 : Blo 1949435 1950171 := bstep (se 1 (by rfl) ⟨1462628, by rfl⟩ : syracuseStep 1950171 = 2925257) B2925257
theorem B12495221 : Blo 1949435 12495221 := bbase (se 5 (by rfl) ⟨585713, by rfl⟩ : syracuseStep 12495221 = 1171427) (by norm_num)
theorem B8330147 : Blo 1949435 8330147 := bstep (se 1 (by rfl) ⟨6247610, by rfl⟩ : syracuseStep 8330147 = 12495221) B12495221
theorem B5553431 : Blo 1949435 5553431 := bstep (se 1 (by rfl) ⟨4165073, by rfl⟩ : syracuseStep 5553431 = 8330147) B8330147
theorem B3702287 : Blo 1949435 3702287 := bstep (se 1 (by rfl) ⟨2776715, by rfl⟩ : syracuseStep 3702287 = 5553431) B5553431
theorem B9872765 : Blo 1949435 9872765 := bstep (se 3 (by rfl) ⟨1851143, by rfl⟩ : syracuseStep 9872765 = 3702287) B3702287
theorem B6581843 : Blo 1949435 6581843 := bstep (se 1 (by rfl) ⟨4936382, by rfl⟩ : syracuseStep 6581843 = 9872765) B9872765
theorem B4387895 : Blo 1949435 4387895 := bstep (se 1 (by rfl) ⟨3290921, by rfl⟩ : syracuseStep 4387895 = 6581843) B6581843
theorem B2925263 : Blo 1949435 2925263 := bstep (se 1 (by rfl) ⟨2193947, by rfl⟩ : syracuseStep 2925263 = 4387895) B4387895
theorem B1950175 : Blo 1949435 1950175 := bstep (se 1 (by rfl) ⟨1462631, by rfl⟩ : syracuseStep 1950175 = 2925263) B2925263
theorem B2925269 : Blo 1949435 2925269 := bbase (se 7 (by rfl) ⟨34280, by rfl⟩ : syracuseStep 2925269 = 68561) (by norm_num)
theorem B1950179 : Blo 1949435 1950179 := bstep (se 1 (by rfl) ⟨1462634, by rfl⟩ : syracuseStep 1950179 = 2925269) B2925269
theorem B6247637 : Blo 1949435 6247637 := bbase (se 7 (by rfl) ⟨73214, by rfl⟩ : syracuseStep 6247637 = 146429) (by norm_num)
theorem B4165091 : Blo 1949435 4165091 := bstep (se 1 (by rfl) ⟨3123818, by rfl⟩ : syracuseStep 4165091 = 6247637) B6247637
theorem B2776727 : Blo 1949435 2776727 := bstep (se 1 (by rfl) ⟨2082545, by rfl⟩ : syracuseStep 2776727 = 4165091) B4165091
theorem B7404605 : Blo 1949435 7404605 := bstep (se 3 (by rfl) ⟨1388363, by rfl⟩ : syracuseStep 7404605 = 2776727) B2776727
theorem B4936403 : Blo 1949435 4936403 := bstep (se 1 (by rfl) ⟨3702302, by rfl⟩ : syracuseStep 4936403 = 7404605) B7404605
theorem B3290935 : Blo 1949435 3290935 := bstep (se 1 (by rfl) ⟨2468201, by rfl⟩ : syracuseStep 3290935 = 4936403) B4936403
theorem B4387913 : Blo 1949435 4387913 := bstep (se 2 (by rfl) ⟨1645467, by rfl⟩ : syracuseStep 4387913 = 3290935) B3290935
theorem B2925275 : Blo 1949435 2925275 := bstep (se 1 (by rfl) ⟨2193956, by rfl⟩ : syracuseStep 2925275 = 4387913) B4387913
theorem B1950183 : Blo 1949435 1950183 := bstep (se 1 (by rfl) ⟨1462637, by rfl⟩ : syracuseStep 1950183 = 2925275) B2925275
theorem B2193961 : Blo 1949435 2193961 := bbase (se 2 (by rfl) ⟨822735, by rfl⟩ : syracuseStep 2193961 = 1645471) (by norm_num)
theorem B2925281 : Blo 1949435 2925281 := bstep (se 2 (by rfl) ⟨1096980, by rfl⟩ : syracuseStep 2925281 = 2193961) B2193961
theorem B1950187 : Blo 1949435 1950187 := bstep (se 1 (by rfl) ⟨1462640, by rfl⟩ : syracuseStep 1950187 = 2925281) B2925281
theorem B2139769 : Blo 1949435 2139769 := bbase (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) (by norm_num)
theorem B2853025 : Blo 1949435 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B15216133 : Blo 1949435 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B20288177 : Blo 1949435 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B13525451 : Blo 1949435 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B9016967 : Blo 1949435 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B24045245 : Blo 1949435 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B16030163 : Blo 1949435 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B42747101 : Blo 1949435 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B28498067 : Blo 1949435 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B18998711 : Blo 1949435 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B12665807 : Blo 1949435 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B8443871 : Blo 1949435 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B5629247 : Blo 1949435 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B3752831 : Blo 1949435 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B10007549 : Blo 1949435 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B6671699 : Blo 1949435 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B4447799 : Blo 1949435 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B2965199 : Blo 1949435 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B31628789 : Blo 1949435 31628789 := bstep (se 5 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 31628789 = 2965199) B2965199
theorem B21085859 : Blo 1949435 21085859 := bstep (se 1 (by rfl) ⟨15814394, by rfl⟩ : syracuseStep 21085859 = 31628789) B31628789
theorem B14057239 : Blo 1949435 14057239 := bstep (se 1 (by rfl) ⟨10542929, by rfl⟩ : syracuseStep 14057239 = 21085859) B21085859
theorem B18742985 : Blo 1949435 18742985 := bstep (se 2 (by rfl) ⟨7028619, by rfl⟩ : syracuseStep 18742985 = 14057239) B14057239
theorem B12495323 : Blo 1949435 12495323 := bstep (se 1 (by rfl) ⟨9371492, by rfl⟩ : syracuseStep 12495323 = 18742985) B18742985
theorem B8330215 : Blo 1949435 8330215 := bstep (se 1 (by rfl) ⟨6247661, by rfl⟩ : syracuseStep 8330215 = 12495323) B12495323
theorem B11106953 : Blo 1949435 11106953 := bstep (se 2 (by rfl) ⟨4165107, by rfl⟩ : syracuseStep 11106953 = 8330215) B8330215
theorem B7404635 : Blo 1949435 7404635 := bstep (se 1 (by rfl) ⟨5553476, by rfl⟩ : syracuseStep 7404635 = 11106953) B11106953
theorem B4936423 : Blo 1949435 4936423 := bstep (se 1 (by rfl) ⟨3702317, by rfl⟩ : syracuseStep 4936423 = 7404635) B7404635
theorem B6581897 : Blo 1949435 6581897 := bstep (se 2 (by rfl) ⟨2468211, by rfl⟩ : syracuseStep 6581897 = 4936423) B4936423
theorem B4387931 : Blo 1949435 4387931 := bstep (se 1 (by rfl) ⟨3290948, by rfl⟩ : syracuseStep 4387931 = 6581897) B6581897
theorem B2925287 : Blo 1949435 2925287 := bstep (se 1 (by rfl) ⟨2193965, by rfl⟩ : syracuseStep 2925287 = 4387931) B4387931
theorem B1950191 : Blo 1949435 1950191 := bstep (se 1 (by rfl) ⟨1462643, by rfl⟩ : syracuseStep 1950191 = 2925287) B2925287
theorem B2925293 : Blo 1949435 2925293 := bbase (se 3 (by rfl) ⟨548492, by rfl⟩ : syracuseStep 2925293 = 1096985) (by norm_num)
theorem B1950195 : Blo 1949435 1950195 := bstep (se 1 (by rfl) ⟨1462646, by rfl⟩ : syracuseStep 1950195 = 2925293) B2925293
theorem B4387949 : Blo 1949435 4387949 := bbase (se 3 (by rfl) ⟨822740, by rfl⟩ : syracuseStep 4387949 = 1645481) (by norm_num)
theorem B2925299 : Blo 1949435 2925299 := bstep (se 1 (by rfl) ⟨2193974, by rfl⟩ : syracuseStep 2925299 = 4387949) B4387949
theorem B1950199 : Blo 1949435 1950199 := bstep (se 1 (by rfl) ⟨1462649, by rfl⟩ : syracuseStep 1950199 = 2925299) B2925299
theorem B3702341 : Blo 1949435 3702341 := bbase (se 4 (by rfl) ⟨347094, by rfl⟩ : syracuseStep 3702341 = 694189) (by norm_num)
theorem B2468227 : Blo 1949435 2468227 := bstep (se 1 (by rfl) ⟨1851170, by rfl⟩ : syracuseStep 2468227 = 3702341) B3702341
theorem B3290969 : Blo 1949435 3290969 := bstep (se 2 (by rfl) ⟨1234113, by rfl⟩ : syracuseStep 3290969 = 2468227) B2468227
theorem B2193979 : Blo 1949435 2193979 := bstep (se 1 (by rfl) ⟨1645484, by rfl⟩ : syracuseStep 2193979 = 3290969) B3290969
theorem B2925305 : Blo 1949435 2925305 := bstep (se 2 (by rfl) ⟨1096989, by rfl⟩ : syracuseStep 2925305 = 2193979) B2193979
theorem B1950203 : Blo 1949435 1950203 := bstep (se 1 (by rfl) ⟨1462652, by rfl⟩ : syracuseStep 1950203 = 2925305) B2925305
theorem B12665909 : Blo 1949435 12665909 := bbase (se 5 (by rfl) ⟨593714, by rfl⟩ : syracuseStep 12665909 = 1187429) (by norm_num)
theorem B8443939 : Blo 1949435 8443939 := bstep (se 1 (by rfl) ⟨6332954, by rfl⟩ : syracuseStep 8443939 = 12665909) B12665909
theorem B11258585 : Blo 1949435 11258585 := bstep (se 2 (by rfl) ⟨4221969, by rfl⟩ : syracuseStep 11258585 = 8443939) B8443939
theorem B7505723 : Blo 1949435 7505723 := bstep (se 1 (by rfl) ⟨5629292, by rfl⟩ : syracuseStep 7505723 = 11258585) B11258585
theorem B5003815 : Blo 1949435 5003815 := bstep (se 1 (by rfl) ⟨3752861, by rfl⟩ : syracuseStep 5003815 = 7505723) B7505723
theorem B6671753 : Blo 1949435 6671753 := bstep (se 2 (by rfl) ⟨2501907, by rfl⟩ : syracuseStep 6671753 = 5003815) B5003815
theorem B4447835 : Blo 1949435 4447835 := bstep (se 1 (by rfl) ⟨3335876, by rfl⟩ : syracuseStep 4447835 = 6671753) B6671753
theorem B2965223 : Blo 1949435 2965223 := bstep (se 1 (by rfl) ⟨2223917, by rfl⟩ : syracuseStep 2965223 = 4447835) B4447835
theorem B7907261 : Blo 1949435 7907261 := bstep (se 3 (by rfl) ⟨1482611, by rfl⟩ : syracuseStep 7907261 = 2965223) B2965223
theorem B21086029 : Blo 1949435 21086029 := bstep (se 3 (by rfl) ⟨3953630, by rfl⟩ : syracuseStep 21086029 = 7907261) B7907261
theorem B28114705 : Blo 1949435 28114705 := bstep (se 2 (by rfl) ⟨10543014, by rfl⟩ : syracuseStep 28114705 = 21086029) B21086029
theorem B37486273 : Blo 1949435 37486273 := bstep (se 2 (by rfl) ⟨14057352, by rfl⟩ : syracuseStep 37486273 = 28114705) B28114705
theorem B49981697 : Blo 1949435 49981697 := bstep (se 2 (by rfl) ⟨18743136, by rfl⟩ : syracuseStep 49981697 = 37486273) B37486273
theorem B33321131 : Blo 1949435 33321131 := bstep (se 1 (by rfl) ⟨24990848, by rfl⟩ : syracuseStep 33321131 = 49981697) B49981697
theorem B22214087 : Blo 1949435 22214087 := bstep (se 1 (by rfl) ⟨16660565, by rfl⟩ : syracuseStep 22214087 = 33321131) B33321131
theorem B14809391 : Blo 1949435 14809391 := bstep (se 1 (by rfl) ⟨11107043, by rfl⟩ : syracuseStep 14809391 = 22214087) B22214087
theorem B9872927 : Blo 1949435 9872927 := bstep (se 1 (by rfl) ⟨7404695, by rfl⟩ : syracuseStep 9872927 = 14809391) B14809391
theorem B6581951 : Blo 1949435 6581951 := bstep (se 1 (by rfl) ⟨4936463, by rfl⟩ : syracuseStep 6581951 = 9872927) B9872927
theorem B4387967 : Blo 1949435 4387967 := bstep (se 1 (by rfl) ⟨3290975, by rfl⟩ : syracuseStep 4387967 = 6581951) B6581951
theorem B2925311 : Blo 1949435 2925311 := bstep (se 1 (by rfl) ⟨2193983, by rfl⟩ : syracuseStep 2925311 = 4387967) B4387967
theorem B1950207 : Blo 1949435 1950207 := bstep (se 1 (by rfl) ⟨1462655, by rfl⟩ : syracuseStep 1950207 = 2925311) B2925311
theorem B2925317 : Blo 1949435 2925317 := bbase (se 4 (by rfl) ⟨274248, by rfl⟩ : syracuseStep 2925317 = 548497) (by norm_num)
theorem B1950211 : Blo 1949435 1950211 := bstep (se 1 (by rfl) ⟨1462658, by rfl⟩ : syracuseStep 1950211 = 2925317) B2925317
theorem B3290989 : Blo 1949435 3290989 := bbase (se 3 (by rfl) ⟨617060, by rfl⟩ : syracuseStep 3290989 = 1234121) (by norm_num)
theorem B4387985 : Blo 1949435 4387985 := bstep (se 2 (by rfl) ⟨1645494, by rfl⟩ : syracuseStep 4387985 = 3290989) B3290989
theorem B2925323 : Blo 1949435 2925323 := bstep (se 1 (by rfl) ⟨2193992, by rfl⟩ : syracuseStep 2925323 = 4387985) B4387985
theorem B1950215 : Blo 1949435 1950215 := bstep (se 1 (by rfl) ⟨1462661, by rfl⟩ : syracuseStep 1950215 = 2925323) B2925323
theorem B2193997 : Blo 1949435 2193997 := bbase (se 3 (by rfl) ⟨411374, by rfl⟩ : syracuseStep 2193997 = 822749) (by norm_num)
theorem B2925329 : Blo 1949435 2925329 := bstep (se 2 (by rfl) ⟨1096998, by rfl⟩ : syracuseStep 2925329 = 2193997) B2193997
theorem B1950219 : Blo 1949435 1950219 := bstep (se 1 (by rfl) ⟨1462664, by rfl⟩ : syracuseStep 1950219 = 2925329) B2925329
theorem B6582005 : Blo 1949435 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B4388003 : Blo 1949435 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B2925335 : Blo 1949435 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B1950223 : Blo 1949435 1950223 := bstep (se 1 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 1950223 = 2925335) B2925335
theorem B2925341 : Blo 1949435 2925341 := bbase (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) (by norm_num)
theorem B1950227 : Blo 1949435 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B4388021 : Blo 1949435 4388021 := bbase (se 5 (by rfl) ⟨205688, by rfl⟩ : syracuseStep 4388021 = 411377) (by norm_num)
theorem B2925347 : Blo 1949435 2925347 := bstep (se 1 (by rfl) ⟨2194010, by rfl⟩ : syracuseStep 2925347 = 4388021) B4388021
theorem B1950231 : Blo 1949435 1950231 := bstep (se 1 (by rfl) ⟨1462673, by rfl⟩ : syracuseStep 1950231 = 2925347) B2925347
theorem B2082601 : Blo 1949435 2082601 := bbase (se 2 (by rfl) ⟨780975, by rfl⟩ : syracuseStep 2082601 = 1561951) (by norm_num)
theorem B11107205 : Blo 1949435 11107205 := bstep (se 4 (by rfl) ⟨1041300, by rfl⟩ : syracuseStep 11107205 = 2082601) B2082601
theorem B7404803 : Blo 1949435 7404803 := bstep (se 1 (by rfl) ⟨5553602, by rfl⟩ : syracuseStep 7404803 = 11107205) B11107205
theorem B4936535 : Blo 1949435 4936535 := bstep (se 1 (by rfl) ⟨3702401, by rfl⟩ : syracuseStep 4936535 = 7404803) B7404803
theorem B3291023 : Blo 1949435 3291023 := bstep (se 1 (by rfl) ⟨2468267, by rfl⟩ : syracuseStep 3291023 = 4936535) B4936535
theorem B2194015 : Blo 1949435 2194015 := bstep (se 1 (by rfl) ⟨1645511, by rfl⟩ : syracuseStep 2194015 = 3291023) B3291023
theorem B2925353 : Blo 1949435 2925353 := bstep (se 2 (by rfl) ⟨1097007, by rfl⟩ : syracuseStep 2925353 = 2194015) B2194015
theorem B1950235 : Blo 1949435 1950235 := bstep (se 1 (by rfl) ⟨1462676, by rfl⟩ : syracuseStep 1950235 = 2925353) B2925353
theorem B2082605 : Blo 1949435 2082605 := bbase (se 3 (by rfl) ⟨390488, by rfl⟩ : syracuseStep 2082605 = 780977) (by norm_num)
theorem B5553613 : Blo 1949435 5553613 := bstep (se 3 (by rfl) ⟨1041302, by rfl⟩ : syracuseStep 5553613 = 2082605) B2082605
theorem B7404817 : Blo 1949435 7404817 := bstep (se 2 (by rfl) ⟨2776806, by rfl⟩ : syracuseStep 7404817 = 5553613) B5553613
theorem B9873089 : Blo 1949435 9873089 := bstep (se 2 (by rfl) ⟨3702408, by rfl⟩ : syracuseStep 9873089 = 7404817) B7404817
theorem B6582059 : Blo 1949435 6582059 := bstep (se 1 (by rfl) ⟨4936544, by rfl⟩ : syracuseStep 6582059 = 9873089) B9873089
theorem B4388039 : Blo 1949435 4388039 := bstep (se 1 (by rfl) ⟨3291029, by rfl⟩ : syracuseStep 4388039 = 6582059) B6582059
theorem B2925359 : Blo 1949435 2925359 := bstep (se 1 (by rfl) ⟨2194019, by rfl⟩ : syracuseStep 2925359 = 4388039) B4388039
theorem B1950239 : Blo 1949435 1950239 := bstep (se 1 (by rfl) ⟨1462679, by rfl⟩ : syracuseStep 1950239 = 2925359) B2925359
theorem B2925365 : Blo 1949435 2925365 := bbase (se 5 (by rfl) ⟨137126, by rfl⟩ : syracuseStep 2925365 = 274253) (by norm_num)
theorem B1950243 : Blo 1949435 1950243 := bstep (se 1 (by rfl) ⟨1462682, by rfl⟩ : syracuseStep 1950243 = 2925365) B2925365
theorem B4936565 : Blo 1949435 4936565 := bbase (se 5 (by rfl) ⟨231401, by rfl⟩ : syracuseStep 4936565 = 462803) (by norm_num)
theorem B3291043 : Blo 1949435 3291043 := bstep (se 1 (by rfl) ⟨2468282, by rfl⟩ : syracuseStep 3291043 = 4936565) B4936565
theorem B4388057 : Blo 1949435 4388057 := bstep (se 2 (by rfl) ⟨1645521, by rfl⟩ : syracuseStep 4388057 = 3291043) B3291043
theorem B2925371 : Blo 1949435 2925371 := bstep (se 1 (by rfl) ⟨2194028, by rfl⟩ : syracuseStep 2925371 = 4388057) B4388057
theorem B1950247 : Blo 1949435 1950247 := bstep (se 1 (by rfl) ⟨1462685, by rfl⟩ : syracuseStep 1950247 = 2925371) B2925371
theorem B2194033 : Blo 1949435 2194033 := bbase (se 2 (by rfl) ⟨822762, by rfl⟩ : syracuseStep 2194033 = 1645525) (by norm_num)
theorem B2925377 : Blo 1949435 2925377 := bstep (se 2 (by rfl) ⟨1097016, by rfl⟩ : syracuseStep 2925377 = 2194033) B2194033
theorem B1950251 : Blo 1949435 1950251 := bstep (se 1 (by rfl) ⟨1462688, by rfl⟩ : syracuseStep 1950251 = 2925377) B2925377
theorem B2223973 : Blo 1949435 2223973 := bbase (se 4 (by rfl) ⟨208497, by rfl⟩ : syracuseStep 2223973 = 416995) (by norm_num)
theorem B2965297 : Blo 1949435 2965297 := bstep (se 2 (by rfl) ⟨1111986, by rfl⟩ : syracuseStep 2965297 = 2223973) B2223973
theorem B3953729 : Blo 1949435 3953729 := bstep (se 2 (by rfl) ⟨1482648, by rfl⟩ : syracuseStep 3953729 = 2965297) B2965297
theorem B10543277 : Blo 1949435 10543277 := bstep (se 3 (by rfl) ⟨1976864, by rfl⟩ : syracuseStep 10543277 = 3953729) B3953729
theorem B7028851 : Blo 1949435 7028851 := bstep (se 1 (by rfl) ⟨5271638, by rfl⟩ : syracuseStep 7028851 = 10543277) B10543277
theorem B9371801 : Blo 1949435 9371801 := bstep (se 2 (by rfl) ⟨3514425, by rfl⟩ : syracuseStep 9371801 = 7028851) B7028851
theorem B6247867 : Blo 1949435 6247867 := bstep (se 1 (by rfl) ⟨4685900, by rfl⟩ : syracuseStep 6247867 = 9371801) B9371801
theorem B8330489 : Blo 1949435 8330489 := bstep (se 2 (by rfl) ⟨3123933, by rfl⟩ : syracuseStep 8330489 = 6247867) B6247867
theorem B5553659 : Blo 1949435 5553659 := bstep (se 1 (by rfl) ⟨4165244, by rfl⟩ : syracuseStep 5553659 = 8330489) B8330489
theorem B3702439 : Blo 1949435 3702439 := bstep (se 1 (by rfl) ⟨2776829, by rfl⟩ : syracuseStep 3702439 = 5553659) B5553659
theorem B4936585 : Blo 1949435 4936585 := bstep (se 2 (by rfl) ⟨1851219, by rfl⟩ : syracuseStep 4936585 = 3702439) B3702439
theorem B6582113 : Blo 1949435 6582113 := bstep (se 2 (by rfl) ⟨2468292, by rfl⟩ : syracuseStep 6582113 = 4936585) B4936585
theorem B4388075 : Blo 1949435 4388075 := bstep (se 1 (by rfl) ⟨3291056, by rfl⟩ : syracuseStep 4388075 = 6582113) B6582113
theorem B2925383 : Blo 1949435 2925383 := bstep (se 1 (by rfl) ⟨2194037, by rfl⟩ : syracuseStep 2925383 = 4388075) B4388075
theorem B1950255 : Blo 1949435 1950255 := bstep (se 1 (by rfl) ⟨1462691, by rfl⟩ : syracuseStep 1950255 = 2925383) B2925383
theorem B2925389 : Blo 1949435 2925389 := bbase (se 3 (by rfl) ⟨548510, by rfl⟩ : syracuseStep 2925389 = 1097021) (by norm_num)
theorem B1950259 : Blo 1949435 1950259 := bstep (se 1 (by rfl) ⟨1462694, by rfl⟩ : syracuseStep 1950259 = 2925389) B2925389
theorem B4388093 : Blo 1949435 4388093 := bbase (se 3 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 4388093 = 1645535) (by norm_num)
theorem B2925395 : Blo 1949435 2925395 := bstep (se 1 (by rfl) ⟨2194046, by rfl⟩ : syracuseStep 2925395 = 4388093) B4388093
theorem B1950263 : Blo 1949435 1950263 := bstep (se 1 (by rfl) ⟨1462697, by rfl⟩ : syracuseStep 1950263 = 2925395) B2925395
theorem B3291077 : Blo 1949435 3291077 := bbase (se 4 (by rfl) ⟨308538, by rfl⟩ : syracuseStep 3291077 = 617077) (by norm_num)
theorem B2194051 : Blo 1949435 2194051 := bstep (se 1 (by rfl) ⟨1645538, by rfl⟩ : syracuseStep 2194051 = 3291077) B3291077
theorem B2925401 : Blo 1949435 2925401 := bstep (se 2 (by rfl) ⟨1097025, by rfl⟩ : syracuseStep 2925401 = 2194051) B2194051
theorem B1950267 : Blo 1949435 1950267 := bstep (se 1 (by rfl) ⟨1462700, by rfl⟩ : syracuseStep 1950267 = 2925401) B2925401
theorem B14809877 : Blo 1949435 14809877 := bbase (se 6 (by rfl) ⟨347106, by rfl⟩ : syracuseStep 14809877 = 694213) (by norm_num)
theorem B9873251 : Blo 1949435 9873251 := bstep (se 1 (by rfl) ⟨7404938, by rfl⟩ : syracuseStep 9873251 = 14809877) B14809877
theorem B6582167 : Blo 1949435 6582167 := bstep (se 1 (by rfl) ⟨4936625, by rfl⟩ : syracuseStep 6582167 = 9873251) B9873251
theorem B4388111 : Blo 1949435 4388111 := bstep (se 1 (by rfl) ⟨3291083, by rfl⟩ : syracuseStep 4388111 = 6582167) B6582167
theorem B2925407 : Blo 1949435 2925407 := bstep (se 1 (by rfl) ⟨2194055, by rfl⟩ : syracuseStep 2925407 = 4388111) B4388111
theorem B1950271 : Blo 1949435 1950271 := bstep (se 1 (by rfl) ⟨1462703, by rfl⟩ : syracuseStep 1950271 = 2925407) B2925407
theorem B2925413 : Blo 1949435 2925413 := bbase (se 4 (by rfl) ⟨274257, by rfl⟩ : syracuseStep 2925413 = 548515) (by norm_num)
theorem B1950275 : Blo 1949435 1950275 := bstep (se 1 (by rfl) ⟨1462706, by rfl⟩ : syracuseStep 1950275 = 2925413) B2925413
theorem B3702485 : Blo 1949435 3702485 := bbase (se 7 (by rfl) ⟨43388, by rfl⟩ : syracuseStep 3702485 = 86777) (by norm_num)
theorem B2468323 : Blo 1949435 2468323 := bstep (se 1 (by rfl) ⟨1851242, by rfl⟩ : syracuseStep 2468323 = 3702485) B3702485
theorem B3291097 : Blo 1949435 3291097 := bstep (se 2 (by rfl) ⟨1234161, by rfl⟩ : syracuseStep 3291097 = 2468323) B2468323
theorem B4388129 : Blo 1949435 4388129 := bstep (se 2 (by rfl) ⟨1645548, by rfl⟩ : syracuseStep 4388129 = 3291097) B3291097
theorem B2925419 : Blo 1949435 2925419 := bstep (se 1 (by rfl) ⟨2194064, by rfl⟩ : syracuseStep 2925419 = 4388129) B4388129
theorem B1950279 : Blo 1949435 1950279 := bstep (se 1 (by rfl) ⟨1462709, by rfl⟩ : syracuseStep 1950279 = 2925419) B2925419
theorem B2194069 : Blo 1949435 2194069 := bbase (se 6 (by rfl) ⟨51423, by rfl⟩ : syracuseStep 2194069 = 102847) (by norm_num)
theorem B2925425 : Blo 1949435 2925425 := bstep (se 2 (by rfl) ⟨1097034, by rfl⟩ : syracuseStep 2925425 = 2194069) B2194069
theorem B1950283 : Blo 1949435 1950283 := bstep (se 1 (by rfl) ⟨1462712, by rfl⟩ : syracuseStep 1950283 = 2925425) B2925425
theorem B2468333 : Blo 1949435 2468333 := bbase (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) (by norm_num)
theorem B6582221 : Blo 1949435 6582221 := bstep (se 3 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 6582221 = 2468333) B2468333
theorem B4388147 : Blo 1949435 4388147 := bstep (se 1 (by rfl) ⟨3291110, by rfl⟩ : syracuseStep 4388147 = 6582221) B6582221
theorem B2925431 : Blo 1949435 2925431 := bstep (se 1 (by rfl) ⟨2194073, by rfl⟩ : syracuseStep 2925431 = 4388147) B4388147
theorem B1950287 : Blo 1949435 1950287 := bstep (se 1 (by rfl) ⟨1462715, by rfl⟩ : syracuseStep 1950287 = 2925431) B2925431
theorem B2925437 : Blo 1949435 2925437 := bbase (se 3 (by rfl) ⟨548519, by rfl⟩ : syracuseStep 2925437 = 1097039) (by norm_num)
theorem B1950291 : Blo 1949435 1950291 := bstep (se 1 (by rfl) ⟨1462718, by rfl⟩ : syracuseStep 1950291 = 2925437) B2925437
theorem B4388165 : Blo 1949435 4388165 := bbase (se 4 (by rfl) ⟨411390, by rfl⟩ : syracuseStep 4388165 = 822781) (by norm_num)
theorem B2925443 : Blo 1949435 2925443 := bstep (se 1 (by rfl) ⟨2194082, by rfl⟩ : syracuseStep 2925443 = 4388165) B4388165
theorem B1950295 : Blo 1949435 1950295 := bstep (se 1 (by rfl) ⟨1462721, by rfl⟩ : syracuseStep 1950295 = 2925443) B2925443
theorem B8444341 : Blo 1949435 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B11259121 : Blo 1949435 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B15012161 : Blo 1949435 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B10008107 : Blo 1949435 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B6672071 : Blo 1949435 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B4448047 : Blo 1949435 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B5930729 : Blo 1949435 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B3953819 : Blo 1949435 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B10543517 : Blo 1949435 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B7029011 : Blo 1949435 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B4686007 : Blo 1949435 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B6248009 : Blo 1949435 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B4165339 : Blo 1949435 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B5553785 : Blo 1949435 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B3702523 : Blo 1949435 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B4936697 : Blo 1949435 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B3291131 : Blo 1949435 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B2194087 : Blo 1949435 2194087 := bstep (se 1 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 2194087 = 3291131) B3291131
theorem B2925449 : Blo 1949435 2925449 := bstep (se 2 (by rfl) ⟨1097043, by rfl⟩ : syracuseStep 2925449 = 2194087) B2194087
theorem B1950299 : Blo 1949435 1950299 := bstep (se 1 (by rfl) ⟨1462724, by rfl⟩ : syracuseStep 1950299 = 2925449) B2925449
theorem B9873413 : Blo 1949435 9873413 := bbase (se 4 (by rfl) ⟨925632, by rfl⟩ : syracuseStep 9873413 = 1851265) (by norm_num)
theorem B6582275 : Blo 1949435 6582275 := bstep (se 1 (by rfl) ⟨4936706, by rfl⟩ : syracuseStep 6582275 = 9873413) B9873413
theorem B4388183 : Blo 1949435 4388183 := bstep (se 1 (by rfl) ⟨3291137, by rfl⟩ : syracuseStep 4388183 = 6582275) B6582275
theorem B2925455 : Blo 1949435 2925455 := bstep (se 1 (by rfl) ⟨2194091, by rfl⟩ : syracuseStep 2925455 = 4388183) B4388183
theorem B1950303 : Blo 1949435 1950303 := bstep (se 1 (by rfl) ⟨1462727, by rfl⟩ : syracuseStep 1950303 = 2925455) B2925455
theorem B2925461 : Blo 1949435 2925461 := bbase (se 6 (by rfl) ⟨68565, by rfl⟩ : syracuseStep 2925461 = 137131) (by norm_num)
theorem B1950307 : Blo 1949435 1950307 := bstep (se 1 (by rfl) ⟨1462730, by rfl⟩ : syracuseStep 1950307 = 2925461) B2925461
theorem B11107637 : Blo 1949435 11107637 := bbase (se 5 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 11107637 = 1041341) (by norm_num)
theorem B7405091 : Blo 1949435 7405091 := bstep (se 1 (by rfl) ⟨5553818, by rfl⟩ : syracuseStep 7405091 = 11107637) B11107637
theorem B4936727 : Blo 1949435 4936727 := bstep (se 1 (by rfl) ⟨3702545, by rfl⟩ : syracuseStep 4936727 = 7405091) B7405091
theorem B3291151 : Blo 1949435 3291151 := bstep (se 1 (by rfl) ⟨2468363, by rfl⟩ : syracuseStep 3291151 = 4936727) B4936727
theorem B4388201 : Blo 1949435 4388201 := bstep (se 2 (by rfl) ⟨1645575, by rfl⟩ : syracuseStep 4388201 = 3291151) B3291151
theorem B2925467 : Blo 1949435 2925467 := bstep (se 1 (by rfl) ⟨2194100, by rfl⟩ : syracuseStep 2925467 = 4388201) B4388201
theorem B1950311 : Blo 1949435 1950311 := bstep (se 1 (by rfl) ⟨1462733, by rfl⟩ : syracuseStep 1950311 = 2925467) B2925467
theorem B2194105 : Blo 1949435 2194105 := bbase (se 2 (by rfl) ⟨822789, by rfl⟩ : syracuseStep 2194105 = 1645579) (by norm_num)
theorem B2925473 : Blo 1949435 2925473 := bstep (se 2 (by rfl) ⟨1097052, by rfl⟩ : syracuseStep 2925473 = 2194105) B2194105
theorem B1950315 : Blo 1949435 1950315 := bstep (se 1 (by rfl) ⟨1462736, by rfl⟩ : syracuseStep 1950315 = 2925473) B2925473
theorem B4165381 : Blo 1949435 4165381 := bbase (se 4 (by rfl) ⟨390504, by rfl⟩ : syracuseStep 4165381 = 781009) (by norm_num)
theorem B5553841 : Blo 1949435 5553841 := bstep (se 2 (by rfl) ⟨2082690, by rfl⟩ : syracuseStep 5553841 = 4165381) B4165381
theorem B7405121 : Blo 1949435 7405121 := bstep (se 2 (by rfl) ⟨2776920, by rfl⟩ : syracuseStep 7405121 = 5553841) B5553841
theorem B4936747 : Blo 1949435 4936747 := bstep (se 1 (by rfl) ⟨3702560, by rfl⟩ : syracuseStep 4936747 = 7405121) B7405121
theorem B6582329 : Blo 1949435 6582329 := bstep (se 2 (by rfl) ⟨2468373, by rfl⟩ : syracuseStep 6582329 = 4936747) B4936747
theorem B4388219 : Blo 1949435 4388219 := bstep (se 1 (by rfl) ⟨3291164, by rfl⟩ : syracuseStep 4388219 = 6582329) B6582329
theorem B2925479 : Blo 1949435 2925479 := bstep (se 1 (by rfl) ⟨2194109, by rfl⟩ : syracuseStep 2925479 = 4388219) B4388219
theorem B1950319 : Blo 1949435 1950319 := bstep (se 1 (by rfl) ⟨1462739, by rfl⟩ : syracuseStep 1950319 = 2925479) B2925479
theorem B2925485 : Blo 1949435 2925485 := bbase (se 3 (by rfl) ⟨548528, by rfl⟩ : syracuseStep 2925485 = 1097057) (by norm_num)
theorem B1950323 : Blo 1949435 1950323 := bstep (se 1 (by rfl) ⟨1462742, by rfl⟩ : syracuseStep 1950323 = 2925485) B2925485
theorem B4388237 : Blo 1949435 4388237 := bbase (se 3 (by rfl) ⟨822794, by rfl⟩ : syracuseStep 4388237 = 1645589) (by norm_num)
theorem B2925491 : Blo 1949435 2925491 := bstep (se 1 (by rfl) ⟨2194118, by rfl⟩ : syracuseStep 2925491 = 4388237) B4388237
theorem B1950327 : Blo 1949435 1950327 := bstep (se 1 (by rfl) ⟨1462745, by rfl⟩ : syracuseStep 1950327 = 2925491) B2925491
theorem B2468389 : Blo 1949435 2468389 := bbase (se 4 (by rfl) ⟨231411, by rfl⟩ : syracuseStep 2468389 = 462823) (by norm_num)
theorem B3291185 : Blo 1949435 3291185 := bstep (se 2 (by rfl) ⟨1234194, by rfl⟩ : syracuseStep 3291185 = 2468389) B2468389
theorem B2194123 : Blo 1949435 2194123 := bstep (se 1 (by rfl) ⟨1645592, by rfl⟩ : syracuseStep 2194123 = 3291185) B3291185
theorem B2925497 : Blo 1949435 2925497 := bstep (se 2 (by rfl) ⟨1097061, by rfl⟩ : syracuseStep 2925497 = 2194123) B2194123
theorem B1950331 : Blo 1949435 1950331 := bstep (se 1 (by rfl) ⟨1462748, by rfl⟩ : syracuseStep 1950331 = 2925497) B2925497
theorem B16888981 : Blo 1949435 16888981 := bbase (se 6 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 16888981 = 791671) (by norm_num)
theorem B22518641 : Blo 1949435 22518641 := bstep (se 2 (by rfl) ⟨8444490, by rfl⟩ : syracuseStep 22518641 = 16888981) B16888981
theorem B15012427 : Blo 1949435 15012427 := bstep (se 1 (by rfl) ⟨11259320, by rfl⟩ : syracuseStep 15012427 = 22518641) B22518641
theorem B20016569 : Blo 1949435 20016569 := bstep (se 2 (by rfl) ⟨7506213, by rfl⟩ : syracuseStep 20016569 = 15012427) B15012427
theorem B53377517 : Blo 1949435 53377517 := bstep (se 3 (by rfl) ⟨10008284, by rfl⟩ : syracuseStep 53377517 = 20016569) B20016569
theorem B35585011 : Blo 1949435 35585011 := bstep (se 1 (by rfl) ⟨26688758, by rfl⟩ : syracuseStep 35585011 = 53377517) B53377517
theorem B47446681 : Blo 1949435 47446681 := bstep (se 2 (by rfl) ⟨17792505, by rfl⟩ : syracuseStep 47446681 = 35585011) B35585011
theorem B63262241 : Blo 1949435 63262241 := bstep (se 2 (by rfl) ⟨23723340, by rfl⟩ : syracuseStep 63262241 = 47446681) B47446681
theorem B42174827 : Blo 1949435 42174827 := bstep (se 1 (by rfl) ⟨31631120, by rfl⟩ : syracuseStep 42174827 = 63262241) B63262241
theorem B28116551 : Blo 1949435 28116551 := bstep (se 1 (by rfl) ⟨21087413, by rfl⟩ : syracuseStep 28116551 = 42174827) B42174827
theorem B18744367 : Blo 1949435 18744367 := bstep (se 1 (by rfl) ⟨14058275, by rfl⟩ : syracuseStep 18744367 = 28116551) B28116551
theorem B24992489 : Blo 1949435 24992489 := bstep (se 2 (by rfl) ⟨9372183, by rfl⟩ : syracuseStep 24992489 = 18744367) B18744367
theorem B16661659 : Blo 1949435 16661659 := bstep (se 1 (by rfl) ⟨12496244, by rfl⟩ : syracuseStep 16661659 = 24992489) B24992489
theorem B22215545 : Blo 1949435 22215545 := bstep (se 2 (by rfl) ⟨8330829, by rfl⟩ : syracuseStep 22215545 = 16661659) B16661659
theorem B14810363 : Blo 1949435 14810363 := bstep (se 1 (by rfl) ⟨11107772, by rfl⟩ : syracuseStep 14810363 = 22215545) B22215545
theorem B9873575 : Blo 1949435 9873575 := bstep (se 1 (by rfl) ⟨7405181, by rfl⟩ : syracuseStep 9873575 = 14810363) B14810363
theorem B6582383 : Blo 1949435 6582383 := bstep (se 1 (by rfl) ⟨4936787, by rfl⟩ : syracuseStep 6582383 = 9873575) B9873575
theorem B4388255 : Blo 1949435 4388255 := bstep (se 1 (by rfl) ⟨3291191, by rfl⟩ : syracuseStep 4388255 = 6582383) B6582383
theorem B2925503 : Blo 1949435 2925503 := bstep (se 1 (by rfl) ⟨2194127, by rfl⟩ : syracuseStep 2925503 = 4388255) B4388255
theorem B1950335 : Blo 1949435 1950335 := bstep (se 1 (by rfl) ⟨1462751, by rfl⟩ : syracuseStep 1950335 = 2925503) B2925503
theorem B2925509 : Blo 1949435 2925509 := bbase (se 4 (by rfl) ⟨274266, by rfl⟩ : syracuseStep 2925509 = 548533) (by norm_num)
theorem B1950339 : Blo 1949435 1950339 := bstep (se 1 (by rfl) ⟨1462754, by rfl⟩ : syracuseStep 1950339 = 2925509) B2925509
theorem B3291205 : Blo 1949435 3291205 := bbase (se 4 (by rfl) ⟨308550, by rfl⟩ : syracuseStep 3291205 = 617101) (by norm_num)
theorem B4388273 : Blo 1949435 4388273 := bstep (se 2 (by rfl) ⟨1645602, by rfl⟩ : syracuseStep 4388273 = 3291205) B3291205
theorem B2925515 : Blo 1949435 2925515 := bstep (se 1 (by rfl) ⟨2194136, by rfl⟩ : syracuseStep 2925515 = 4388273) B4388273
theorem B1950343 : Blo 1949435 1950343 := bstep (se 1 (by rfl) ⟨1462757, by rfl⟩ : syracuseStep 1950343 = 2925515) B2925515
theorem B2194141 : Blo 1949435 2194141 := bbase (se 3 (by rfl) ⟨411401, by rfl⟩ : syracuseStep 2194141 = 822803) (by norm_num)
theorem B2925521 : Blo 1949435 2925521 := bstep (se 2 (by rfl) ⟨1097070, by rfl⟩ : syracuseStep 2925521 = 2194141) B2194141
theorem B1950347 : Blo 1949435 1950347 := bstep (se 1 (by rfl) ⟨1462760, by rfl⟩ : syracuseStep 1950347 = 2925521) B2925521
theorem B6582437 : Blo 1949435 6582437 := bbase (se 4 (by rfl) ⟨617103, by rfl⟩ : syracuseStep 6582437 = 1234207) (by norm_num)
theorem B4388291 : Blo 1949435 4388291 := bstep (se 1 (by rfl) ⟨3291218, by rfl⟩ : syracuseStep 4388291 = 6582437) B6582437
theorem B2925527 : Blo 1949435 2925527 := bstep (se 1 (by rfl) ⟨2194145, by rfl⟩ : syracuseStep 2925527 = 4388291) B4388291
theorem B1950351 : Blo 1949435 1950351 := bstep (se 1 (by rfl) ⟨1462763, by rfl⟩ : syracuseStep 1950351 = 2925527) B2925527
theorem B2925533 : Blo 1949435 2925533 := bbase (se 3 (by rfl) ⟨548537, by rfl⟩ : syracuseStep 2925533 = 1097075) (by norm_num)
theorem B1950355 : Blo 1949435 1950355 := bstep (se 1 (by rfl) ⟨1462766, by rfl⟩ : syracuseStep 1950355 = 2925533) B2925533
theorem B4388309 : Blo 1949435 4388309 := bbase (se 7 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 4388309 = 102851) (by norm_num)
theorem B2925539 : Blo 1949435 2925539 := bstep (se 1 (by rfl) ⟨2194154, by rfl⟩ : syracuseStep 2925539 = 4388309) B4388309
theorem B1950359 : Blo 1949435 1950359 := bstep (se 1 (by rfl) ⟨1462769, by rfl⟩ : syracuseStep 1950359 = 2925539) B2925539
theorem B10543861 : Blo 1949435 10543861 := bbase (se 5 (by rfl) ⟨494243, by rfl⟩ : syracuseStep 10543861 = 988487) (by norm_num)
theorem B14058481 : Blo 1949435 14058481 := bstep (se 2 (by rfl) ⟨5271930, by rfl⟩ : syracuseStep 14058481 = 10543861) B10543861
theorem B18744641 : Blo 1949435 18744641 := bstep (se 2 (by rfl) ⟨7029240, by rfl⟩ : syracuseStep 18744641 = 14058481) B14058481
theorem B12496427 : Blo 1949435 12496427 := bstep (se 1 (by rfl) ⟨9372320, by rfl⟩ : syracuseStep 12496427 = 18744641) B18744641
theorem B8330951 : Blo 1949435 8330951 := bstep (se 1 (by rfl) ⟨6248213, by rfl⟩ : syracuseStep 8330951 = 12496427) B12496427
theorem B5553967 : Blo 1949435 5553967 := bstep (se 1 (by rfl) ⟨4165475, by rfl⟩ : syracuseStep 5553967 = 8330951) B8330951
theorem B7405289 : Blo 1949435 7405289 := bstep (se 2 (by rfl) ⟨2776983, by rfl⟩ : syracuseStep 7405289 = 5553967) B5553967
theorem B4936859 : Blo 1949435 4936859 := bstep (se 1 (by rfl) ⟨3702644, by rfl⟩ : syracuseStep 4936859 = 7405289) B7405289
theorem B3291239 : Blo 1949435 3291239 := bstep (se 1 (by rfl) ⟨2468429, by rfl⟩ : syracuseStep 3291239 = 4936859) B4936859
theorem B2194159 : Blo 1949435 2194159 := bstep (se 1 (by rfl) ⟨1645619, by rfl⟩ : syracuseStep 2194159 = 3291239) B3291239
theorem B2925545 : Blo 1949435 2925545 := bstep (se 2 (by rfl) ⟨1097079, by rfl⟩ : syracuseStep 2925545 = 2194159) B2194159
theorem B1950363 : Blo 1949435 1950363 := bstep (se 1 (by rfl) ⟨1462772, by rfl⟩ : syracuseStep 1950363 = 2925545) B2925545
theorem B5271941 : Blo 1949435 5271941 := bbase (se 4 (by rfl) ⟨494244, by rfl⟩ : syracuseStep 5271941 = 988489) (by norm_num)
theorem B3514627 : Blo 1949435 3514627 := bstep (se 1 (by rfl) ⟨2635970, by rfl⟩ : syracuseStep 3514627 = 5271941) B5271941
theorem B4686169 : Blo 1949435 4686169 := bstep (se 2 (by rfl) ⟨1757313, by rfl⟩ : syracuseStep 4686169 = 3514627) B3514627
theorem B6248225 : Blo 1949435 6248225 := bstep (se 2 (by rfl) ⟨2343084, by rfl⟩ : syracuseStep 6248225 = 4686169) B4686169
theorem B16661933 : Blo 1949435 16661933 := bstep (se 3 (by rfl) ⟨3124112, by rfl⟩ : syracuseStep 16661933 = 6248225) B6248225
theorem B11107955 : Blo 1949435 11107955 := bstep (se 1 (by rfl) ⟨8330966, by rfl⟩ : syracuseStep 11107955 = 16661933) B16661933
theorem B7405303 : Blo 1949435 7405303 := bstep (se 1 (by rfl) ⟨5553977, by rfl⟩ : syracuseStep 7405303 = 11107955) B11107955
theorem B9873737 : Blo 1949435 9873737 := bstep (se 2 (by rfl) ⟨3702651, by rfl⟩ : syracuseStep 9873737 = 7405303) B7405303
theorem B6582491 : Blo 1949435 6582491 := bstep (se 1 (by rfl) ⟨4936868, by rfl⟩ : syracuseStep 6582491 = 9873737) B9873737
theorem B4388327 : Blo 1949435 4388327 := bstep (se 1 (by rfl) ⟨3291245, by rfl⟩ : syracuseStep 4388327 = 6582491) B6582491
theorem B2925551 : Blo 1949435 2925551 := bstep (se 1 (by rfl) ⟨2194163, by rfl⟩ : syracuseStep 2925551 = 4388327) B4388327
theorem B1950367 : Blo 1949435 1950367 := bstep (se 1 (by rfl) ⟨1462775, by rfl⟩ : syracuseStep 1950367 = 2925551) B2925551
theorem B2925557 : Blo 1949435 2925557 := bbase (se 5 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 2925557 = 274271) (by norm_num)
theorem B1950371 : Blo 1949435 1950371 := bstep (se 1 (by rfl) ⟨1462778, by rfl⟩ : syracuseStep 1950371 = 2925557) B2925557
theorem B4165501 : Blo 1949435 4165501 := bbase (se 3 (by rfl) ⟨781031, by rfl⟩ : syracuseStep 4165501 = 1562063) (by norm_num)
theorem B5554001 : Blo 1949435 5554001 := bstep (se 2 (by rfl) ⟨2082750, by rfl⟩ : syracuseStep 5554001 = 4165501) B4165501
theorem B3702667 : Blo 1949435 3702667 := bstep (se 1 (by rfl) ⟨2777000, by rfl⟩ : syracuseStep 3702667 = 5554001) B5554001
theorem B4936889 : Blo 1949435 4936889 := bstep (se 2 (by rfl) ⟨1851333, by rfl⟩ : syracuseStep 4936889 = 3702667) B3702667
theorem B3291259 : Blo 1949435 3291259 := bstep (se 1 (by rfl) ⟨2468444, by rfl⟩ : syracuseStep 3291259 = 4936889) B4936889
theorem B4388345 : Blo 1949435 4388345 := bstep (se 2 (by rfl) ⟨1645629, by rfl⟩ : syracuseStep 4388345 = 3291259) B3291259
theorem B2925563 : Blo 1949435 2925563 := bstep (se 1 (by rfl) ⟨2194172, by rfl⟩ : syracuseStep 2925563 = 4388345) B4388345
theorem B1950375 : Blo 1949435 1950375 := bstep (se 1 (by rfl) ⟨1462781, by rfl⟩ : syracuseStep 1950375 = 2925563) B2925563
theorem B2194177 : Blo 1949435 2194177 := bbase (se 2 (by rfl) ⟨822816, by rfl⟩ : syracuseStep 2194177 = 1645633) (by norm_num)
theorem B2925569 : Blo 1949435 2925569 := bstep (se 2 (by rfl) ⟨1097088, by rfl⟩ : syracuseStep 2925569 = 2194177) B2194177
theorem B1950379 : Blo 1949435 1950379 := bstep (se 1 (by rfl) ⟨1462784, by rfl⟩ : syracuseStep 1950379 = 2925569) B2925569
theorem B4936909 : Blo 1949435 4936909 := bbase (se 3 (by rfl) ⟨925670, by rfl⟩ : syracuseStep 4936909 = 1851341) (by norm_num)
theorem B6582545 : Blo 1949435 6582545 := bstep (se 2 (by rfl) ⟨2468454, by rfl⟩ : syracuseStep 6582545 = 4936909) B4936909
theorem B4388363 : Blo 1949435 4388363 := bstep (se 1 (by rfl) ⟨3291272, by rfl⟩ : syracuseStep 4388363 = 6582545) B6582545
theorem B2925575 : Blo 1949435 2925575 := bstep (se 1 (by rfl) ⟨2194181, by rfl⟩ : syracuseStep 2925575 = 4388363) B4388363
theorem B1950383 : Blo 1949435 1950383 := bstep (se 1 (by rfl) ⟨1462787, by rfl⟩ : syracuseStep 1950383 = 2925575) B2925575
theorem B2925581 : Blo 1949435 2925581 := bbase (se 3 (by rfl) ⟨548546, by rfl⟩ : syracuseStep 2925581 = 1097093) (by norm_num)
theorem B1950387 : Blo 1949435 1950387 := bstep (se 1 (by rfl) ⟨1462790, by rfl⟩ : syracuseStep 1950387 = 2925581) B2925581
theorem B4388381 : Blo 1949435 4388381 := bbase (se 3 (by rfl) ⟨822821, by rfl⟩ : syracuseStep 4388381 = 1645643) (by norm_num)
theorem B2925587 : Blo 1949435 2925587 := bstep (se 1 (by rfl) ⟨2194190, by rfl⟩ : syracuseStep 2925587 = 4388381) B4388381
theorem B1950391 : Blo 1949435 1950391 := bstep (se 1 (by rfl) ⟨1462793, by rfl⟩ : syracuseStep 1950391 = 2925587) B2925587
theorem B3291293 : Blo 1949435 3291293 := bbase (se 3 (by rfl) ⟨617117, by rfl⟩ : syracuseStep 3291293 = 1234235) (by norm_num)
theorem B2194195 : Blo 1949435 2194195 := bstep (se 1 (by rfl) ⟨1645646, by rfl⟩ : syracuseStep 2194195 = 3291293) B3291293
theorem B2925593 : Blo 1949435 2925593 := bstep (se 2 (by rfl) ⟨1097097, by rfl⟩ : syracuseStep 2925593 = 2194195) B2194195
theorem B1950395 : Blo 1949435 1950395 := bstep (se 1 (by rfl) ⟨1462796, by rfl⟩ : syracuseStep 1950395 = 2925593) B2925593
theorem B42176213 : Blo 1949435 42176213 := bbase (se 7 (by rfl) ⟨494252, by rfl⟩ : syracuseStep 42176213 = 988505) (by norm_num)
theorem B28117475 : Blo 1949435 28117475 := bstep (se 1 (by rfl) ⟨21088106, by rfl⟩ : syracuseStep 28117475 = 42176213) B42176213
theorem B18744983 : Blo 1949435 18744983 := bstep (se 1 (by rfl) ⟨14058737, by rfl⟩ : syracuseStep 18744983 = 28117475) B28117475
theorem B12496655 : Blo 1949435 12496655 := bstep (se 1 (by rfl) ⟨9372491, by rfl⟩ : syracuseStep 12496655 = 18744983) B18744983
theorem B8331103 : Blo 1949435 8331103 := bstep (se 1 (by rfl) ⟨6248327, by rfl⟩ : syracuseStep 8331103 = 12496655) B12496655
theorem B11108137 : Blo 1949435 11108137 := bstep (se 2 (by rfl) ⟨4165551, by rfl⟩ : syracuseStep 11108137 = 8331103) B8331103
theorem B14810849 : Blo 1949435 14810849 := bstep (se 2 (by rfl) ⟨5554068, by rfl⟩ : syracuseStep 14810849 = 11108137) B11108137
theorem B9873899 : Blo 1949435 9873899 := bstep (se 1 (by rfl) ⟨7405424, by rfl⟩ : syracuseStep 9873899 = 14810849) B14810849
theorem B6582599 : Blo 1949435 6582599 := bstep (se 1 (by rfl) ⟨4936949, by rfl⟩ : syracuseStep 6582599 = 9873899) B9873899
theorem B4388399 : Blo 1949435 4388399 := bstep (se 1 (by rfl) ⟨3291299, by rfl⟩ : syracuseStep 4388399 = 6582599) B6582599
theorem B2925599 : Blo 1949435 2925599 := bstep (se 1 (by rfl) ⟨2194199, by rfl⟩ : syracuseStep 2925599 = 4388399) B4388399
theorem B1950399 : Blo 1949435 1950399 := bstep (se 1 (by rfl) ⟨1462799, by rfl⟩ : syracuseStep 1950399 = 2925599) B2925599
theorem B2925605 : Blo 1949435 2925605 := bbase (se 4 (by rfl) ⟨274275, by rfl⟩ : syracuseStep 2925605 = 548551) (by norm_num)
theorem B1950403 : Blo 1949435 1950403 := bstep (se 1 (by rfl) ⟨1462802, by rfl⟩ : syracuseStep 1950403 = 2925605) B2925605
theorem B2468485 : Blo 1949435 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B3291313 : Blo 1949435 3291313 := bstep (se 2 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 3291313 = 2468485) B2468485
theorem B4388417 : Blo 1949435 4388417 := bstep (se 2 (by rfl) ⟨1645656, by rfl⟩ : syracuseStep 4388417 = 3291313) B3291313
theorem B2925611 : Blo 1949435 2925611 := bstep (se 1 (by rfl) ⟨2194208, by rfl⟩ : syracuseStep 2925611 = 4388417) B4388417
theorem B1950407 : Blo 1949435 1950407 := bstep (se 1 (by rfl) ⟨1462805, by rfl⟩ : syracuseStep 1950407 = 2925611) B2925611
theorem B2194213 : Blo 1949435 2194213 := bbase (se 4 (by rfl) ⟨205707, by rfl⟩ : syracuseStep 2194213 = 411415) (by norm_num)
theorem B2925617 : Blo 1949435 2925617 := bstep (se 2 (by rfl) ⟨1097106, by rfl⟩ : syracuseStep 2925617 = 2194213) B2194213
theorem B1950411 : Blo 1949435 1950411 := bstep (se 1 (by rfl) ⟨1462808, by rfl⟩ : syracuseStep 1950411 = 2925617) B2925617
theorem B8331173 : Blo 1949435 8331173 := bbase (se 4 (by rfl) ⟨781047, by rfl⟩ : syracuseStep 8331173 = 1562095) (by norm_num)
theorem B5554115 : Blo 1949435 5554115 := bstep (se 1 (by rfl) ⟨4165586, by rfl⟩ : syracuseStep 5554115 = 8331173) B8331173
theorem B3702743 : Blo 1949435 3702743 := bstep (se 1 (by rfl) ⟨2777057, by rfl⟩ : syracuseStep 3702743 = 5554115) B5554115
theorem B2468495 : Blo 1949435 2468495 := bstep (se 1 (by rfl) ⟨1851371, by rfl⟩ : syracuseStep 2468495 = 3702743) B3702743
theorem B6582653 : Blo 1949435 6582653 := bstep (se 3 (by rfl) ⟨1234247, by rfl⟩ : syracuseStep 6582653 = 2468495) B2468495
theorem B4388435 : Blo 1949435 4388435 := bstep (se 1 (by rfl) ⟨3291326, by rfl⟩ : syracuseStep 4388435 = 6582653) B6582653
theorem B2925623 : Blo 1949435 2925623 := bstep (se 1 (by rfl) ⟨2194217, by rfl⟩ : syracuseStep 2925623 = 4388435) B4388435
theorem B1950415 : Blo 1949435 1950415 := bstep (se 1 (by rfl) ⟨1462811, by rfl⟩ : syracuseStep 1950415 = 2925623) B2925623
theorem B2925629 : Blo 1949435 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B1950419 : Blo 1949435 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B4388453 : Blo 1949435 4388453 := bbase (se 4 (by rfl) ⟨411417, by rfl⟩ : syracuseStep 4388453 = 822835) (by norm_num)
theorem B2925635 : Blo 1949435 2925635 := bstep (se 1 (by rfl) ⟨2194226, by rfl⟩ : syracuseStep 2925635 = 4388453) B4388453
theorem B1950423 : Blo 1949435 1950423 := bstep (se 1 (by rfl) ⟨1462817, by rfl⟩ : syracuseStep 1950423 = 2925635) B2925635
theorem B4937021 : Blo 1949435 4937021 := bbase (se 3 (by rfl) ⟨925691, by rfl⟩ : syracuseStep 4937021 = 1851383) (by norm_num)
theorem B3291347 : Blo 1949435 3291347 := bstep (se 1 (by rfl) ⟨2468510, by rfl⟩ : syracuseStep 3291347 = 4937021) B4937021
theorem B2194231 : Blo 1949435 2194231 := bstep (se 1 (by rfl) ⟨1645673, by rfl⟩ : syracuseStep 2194231 = 3291347) B3291347
theorem B2925641 : Blo 1949435 2925641 := bstep (se 2 (by rfl) ⟨1097115, by rfl⟩ : syracuseStep 2925641 = 2194231) B2194231
theorem B1950427 : Blo 1949435 1950427 := bstep (se 1 (by rfl) ⟨1462820, by rfl⟩ : syracuseStep 1950427 = 2925641) B2925641
theorem B3702773 : Blo 1949435 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B9874061 : Blo 1949435 9874061 := bstep (se 3 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 9874061 = 3702773) B3702773
theorem B6582707 : Blo 1949435 6582707 := bstep (se 1 (by rfl) ⟨4937030, by rfl⟩ : syracuseStep 6582707 = 9874061) B9874061
theorem B4388471 : Blo 1949435 4388471 := bstep (se 1 (by rfl) ⟨3291353, by rfl⟩ : syracuseStep 4388471 = 6582707) B6582707
theorem B2925647 : Blo 1949435 2925647 := bstep (se 1 (by rfl) ⟨2194235, by rfl⟩ : syracuseStep 2925647 = 4388471) B4388471
theorem B1950431 : Blo 1949435 1950431 := bstep (se 1 (by rfl) ⟨1462823, by rfl⟩ : syracuseStep 1950431 = 2925647) B2925647
theorem B2925653 : Blo 1949435 2925653 := bbase (se 8 (by rfl) ⟨17142, by rfl⟩ : syracuseStep 2925653 = 34285) (by norm_num)
theorem B1950435 : Blo 1949435 1950435 := bstep (se 1 (by rfl) ⟨1462826, by rfl⟩ : syracuseStep 1950435 = 2925653) B2925653
theorem B3514757 : Blo 1949435 3514757 := bbase (se 4 (by rfl) ⟨329508, by rfl⟩ : syracuseStep 3514757 = 659017) (by norm_num)
theorem B9372685 : Blo 1949435 9372685 := bstep (se 3 (by rfl) ⟨1757378, by rfl⟩ : syracuseStep 9372685 = 3514757) B3514757
theorem B12496913 : Blo 1949435 12496913 := bstep (se 2 (by rfl) ⟨4686342, by rfl⟩ : syracuseStep 12496913 = 9372685) B9372685
theorem B8331275 : Blo 1949435 8331275 := bstep (se 1 (by rfl) ⟨6248456, by rfl⟩ : syracuseStep 8331275 = 12496913) B12496913
theorem B5554183 : Blo 1949435 5554183 := bstep (se 1 (by rfl) ⟨4165637, by rfl⟩ : syracuseStep 5554183 = 8331275) B8331275
theorem B7405577 : Blo 1949435 7405577 := bstep (se 2 (by rfl) ⟨2777091, by rfl⟩ : syracuseStep 7405577 = 5554183) B5554183
theorem B4937051 : Blo 1949435 4937051 := bstep (se 1 (by rfl) ⟨3702788, by rfl⟩ : syracuseStep 4937051 = 7405577) B7405577
theorem B3291367 : Blo 1949435 3291367 := bstep (se 1 (by rfl) ⟨2468525, by rfl⟩ : syracuseStep 3291367 = 4937051) B4937051
theorem B4388489 : Blo 1949435 4388489 := bstep (se 2 (by rfl) ⟨1645683, by rfl⟩ : syracuseStep 4388489 = 3291367) B3291367
theorem B2925659 : Blo 1949435 2925659 := bstep (se 1 (by rfl) ⟨2194244, by rfl⟩ : syracuseStep 2925659 = 4388489) B4388489
theorem B1950439 : Blo 1949435 1950439 := bstep (se 1 (by rfl) ⟨1462829, by rfl⟩ : syracuseStep 1950439 = 2925659) B2925659
theorem B2194249 : Blo 1949435 2194249 := bbase (se 2 (by rfl) ⟨822843, by rfl⟩ : syracuseStep 2194249 = 1645687) (by norm_num)
theorem B2925665 : Blo 1949435 2925665 := bstep (se 2 (by rfl) ⟨1097124, by rfl⟩ : syracuseStep 2925665 = 2194249) B2194249
theorem B1950443 : Blo 1949435 1950443 := bstep (se 1 (by rfl) ⟨1462832, by rfl⟩ : syracuseStep 1950443 = 2925665) B2925665
theorem B2965589 : Blo 1949435 2965589 := bbase (se 8 (by rfl) ⟨17376, by rfl⟩ : syracuseStep 2965589 = 34753) (by norm_num)
theorem B1977059 : Blo 1949435 1977059 := bstep (se 1 (by rfl) ⟨1482794, by rfl⟩ : syracuseStep 1977059 = 2965589) B2965589
theorem B5272157 : Blo 1949435 5272157 := bstep (se 3 (by rfl) ⟨988529, by rfl⟩ : syracuseStep 5272157 = 1977059) B1977059
theorem B3514771 : Blo 1949435 3514771 := bstep (se 1 (by rfl) ⟨2636078, by rfl⟩ : syracuseStep 3514771 = 5272157) B5272157
theorem B18745445 : Blo 1949435 18745445 := bstep (se 4 (by rfl) ⟨1757385, by rfl⟩ : syracuseStep 18745445 = 3514771) B3514771
theorem B12496963 : Blo 1949435 12496963 := bstep (se 1 (by rfl) ⟨9372722, by rfl⟩ : syracuseStep 12496963 = 18745445) B18745445
theorem B16662617 : Blo 1949435 16662617 := bstep (se 2 (by rfl) ⟨6248481, by rfl⟩ : syracuseStep 16662617 = 12496963) B12496963
theorem B11108411 : Blo 1949435 11108411 := bstep (se 1 (by rfl) ⟨8331308, by rfl⟩ : syracuseStep 11108411 = 16662617) B16662617
theorem B7405607 : Blo 1949435 7405607 := bstep (se 1 (by rfl) ⟨5554205, by rfl⟩ : syracuseStep 7405607 = 11108411) B11108411
theorem B4937071 : Blo 1949435 4937071 := bstep (se 1 (by rfl) ⟨3702803, by rfl⟩ : syracuseStep 4937071 = 7405607) B7405607
theorem B6582761 : Blo 1949435 6582761 := bstep (se 2 (by rfl) ⟨2468535, by rfl⟩ : syracuseStep 6582761 = 4937071) B4937071
theorem B4388507 : Blo 1949435 4388507 := bstep (se 1 (by rfl) ⟨3291380, by rfl⟩ : syracuseStep 4388507 = 6582761) B6582761
theorem B2925671 : Blo 1949435 2925671 := bstep (se 1 (by rfl) ⟨2194253, by rfl⟩ : syracuseStep 2925671 = 4388507) B4388507
theorem B1950447 : Blo 1949435 1950447 := bstep (se 1 (by rfl) ⟨1462835, by rfl⟩ : syracuseStep 1950447 = 2925671) B2925671
theorem B2925677 : Blo 1949435 2925677 := bbase (se 3 (by rfl) ⟨548564, by rfl⟩ : syracuseStep 2925677 = 1097129) (by norm_num)
theorem B1950451 : Blo 1949435 1950451 := bstep (se 1 (by rfl) ⟨1462838, by rfl⟩ : syracuseStep 1950451 = 2925677) B2925677
theorem B4388525 : Blo 1949435 4388525 := bbase (se 3 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 4388525 = 1645697) (by norm_num)
theorem B2925683 : Blo 1949435 2925683 := bstep (se 1 (by rfl) ⟨2194262, by rfl⟩ : syracuseStep 2925683 = 4388525) B4388525
theorem B1950455 : Blo 1949435 1950455 := bstep (se 1 (by rfl) ⟨1462841, by rfl⟩ : syracuseStep 1950455 = 2925683) B2925683
theorem B3124261 : Blo 1949435 3124261 := bbase (se 4 (by rfl) ⟨292899, by rfl⟩ : syracuseStep 3124261 = 585799) (by norm_num)
theorem B4165681 : Blo 1949435 4165681 := bstep (se 2 (by rfl) ⟨1562130, by rfl⟩ : syracuseStep 4165681 = 3124261) B3124261
theorem B5554241 : Blo 1949435 5554241 := bstep (se 2 (by rfl) ⟨2082840, by rfl⟩ : syracuseStep 5554241 = 4165681) B4165681
theorem B3702827 : Blo 1949435 3702827 := bstep (se 1 (by rfl) ⟨2777120, by rfl⟩ : syracuseStep 3702827 = 5554241) B5554241
theorem B2468551 : Blo 1949435 2468551 := bstep (se 1 (by rfl) ⟨1851413, by rfl⟩ : syracuseStep 2468551 = 3702827) B3702827
theorem B3291401 : Blo 1949435 3291401 := bstep (se 2 (by rfl) ⟨1234275, by rfl⟩ : syracuseStep 3291401 = 2468551) B2468551
theorem B2194267 : Blo 1949435 2194267 := bstep (se 1 (by rfl) ⟨1645700, by rfl⟩ : syracuseStep 2194267 = 3291401) B3291401
theorem B2925689 : Blo 1949435 2925689 := bstep (se 2 (by rfl) ⟨1097133, by rfl⟩ : syracuseStep 2925689 = 2194267) B2194267
theorem B1950459 : Blo 1949435 1950459 := bstep (se 1 (by rfl) ⟨1462844, by rfl⟩ : syracuseStep 1950459 = 2925689) B2925689
theorem B35587349 : Blo 1949435 35587349 := bbase (se 6 (by rfl) ⟨834078, by rfl⟩ : syracuseStep 35587349 = 1668157) (by norm_num)
theorem B23724899 : Blo 1949435 23724899 := bstep (se 1 (by rfl) ⟨17793674, by rfl⟩ : syracuseStep 23724899 = 35587349) B35587349
theorem B15816599 : Blo 1949435 15816599 := bstep (se 1 (by rfl) ⟨11862449, by rfl⟩ : syracuseStep 15816599 = 23724899) B23724899
theorem B10544399 : Blo 1949435 10544399 := bstep (se 1 (by rfl) ⟨7908299, by rfl⟩ : syracuseStep 10544399 = 15816599) B15816599
theorem B7029599 : Blo 1949435 7029599 := bstep (se 1 (by rfl) ⟨5272199, by rfl⟩ : syracuseStep 7029599 = 10544399) B10544399
theorem B18745597 : Blo 1949435 18745597 := bstep (se 3 (by rfl) ⟨3514799, by rfl⟩ : syracuseStep 18745597 = 7029599) B7029599
theorem B24994129 : Blo 1949435 24994129 := bstep (se 2 (by rfl) ⟨9372798, by rfl⟩ : syracuseStep 24994129 = 18745597) B18745597
theorem B33325505 : Blo 1949435 33325505 := bstep (se 2 (by rfl) ⟨12497064, by rfl⟩ : syracuseStep 33325505 = 24994129) B24994129
theorem B22217003 : Blo 1949435 22217003 := bstep (se 1 (by rfl) ⟨16662752, by rfl⟩ : syracuseStep 22217003 = 33325505) B33325505
theorem B14811335 : Blo 1949435 14811335 := bstep (se 1 (by rfl) ⟨11108501, by rfl⟩ : syracuseStep 14811335 = 22217003) B22217003
theorem B9874223 : Blo 1949435 9874223 := bstep (se 1 (by rfl) ⟨7405667, by rfl⟩ : syracuseStep 9874223 = 14811335) B14811335
theorem B6582815 : Blo 1949435 6582815 := bstep (se 1 (by rfl) ⟨4937111, by rfl⟩ : syracuseStep 6582815 = 9874223) B9874223
theorem B4388543 : Blo 1949435 4388543 := bstep (se 1 (by rfl) ⟨3291407, by rfl⟩ : syracuseStep 4388543 = 6582815) B6582815
theorem B2925695 : Blo 1949435 2925695 := bstep (se 1 (by rfl) ⟨2194271, by rfl⟩ : syracuseStep 2925695 = 4388543) B4388543
theorem B1950463 : Blo 1949435 1950463 := bstep (se 1 (by rfl) ⟨1462847, by rfl⟩ : syracuseStep 1950463 = 2925695) B2925695
theorem B2925701 : Blo 1949435 2925701 := bbase (se 4 (by rfl) ⟨274284, by rfl⟩ : syracuseStep 2925701 = 548569) (by norm_num)
theorem B1950467 : Blo 1949435 1950467 := bstep (se 1 (by rfl) ⟨1462850, by rfl⟩ : syracuseStep 1950467 = 2925701) B2925701
theorem B3291421 : Blo 1949435 3291421 := bbase (se 3 (by rfl) ⟨617141, by rfl⟩ : syracuseStep 3291421 = 1234283) (by norm_num)
theorem B4388561 : Blo 1949435 4388561 := bstep (se 2 (by rfl) ⟨1645710, by rfl⟩ : syracuseStep 4388561 = 3291421) B3291421
theorem B2925707 : Blo 1949435 2925707 := bstep (se 1 (by rfl) ⟨2194280, by rfl⟩ : syracuseStep 2925707 = 4388561) B4388561
theorem B1950471 : Blo 1949435 1950471 := bstep (se 1 (by rfl) ⟨1462853, by rfl⟩ : syracuseStep 1950471 = 2925707) B2925707
theorem B2194285 : Blo 1949435 2194285 := bbase (se 3 (by rfl) ⟨411428, by rfl⟩ : syracuseStep 2194285 = 822857) (by norm_num)
theorem B2925713 : Blo 1949435 2925713 := bstep (se 2 (by rfl) ⟨1097142, by rfl⟩ : syracuseStep 2925713 = 2194285) B2194285
theorem B1950475 : Blo 1949435 1950475 := bstep (se 1 (by rfl) ⟨1462856, by rfl⟩ : syracuseStep 1950475 = 2925713) B2925713
theorem B6582869 : Blo 1949435 6582869 := bbase (se 8 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 6582869 = 77143) (by norm_num)
theorem B4388579 : Blo 1949435 4388579 := bstep (se 1 (by rfl) ⟨3291434, by rfl⟩ : syracuseStep 4388579 = 6582869) B6582869
theorem B2925719 : Blo 1949435 2925719 := bstep (se 1 (by rfl) ⟨2194289, by rfl⟩ : syracuseStep 2925719 = 4388579) B4388579
theorem B1950479 : Blo 1949435 1950479 := bstep (se 1 (by rfl) ⟨1462859, by rfl⟩ : syracuseStep 1950479 = 2925719) B2925719
theorem B2925725 : Blo 1949435 2925725 := bbase (se 3 (by rfl) ⟨548573, by rfl⟩ : syracuseStep 2925725 = 1097147) (by norm_num)
theorem B1950483 : Blo 1949435 1950483 := bstep (se 1 (by rfl) ⟨1462862, by rfl⟩ : syracuseStep 1950483 = 2925725) B2925725
theorem B4388597 : Blo 1949435 4388597 := bbase (se 5 (by rfl) ⟨205715, by rfl⟩ : syracuseStep 4388597 = 411431) (by norm_num)
theorem B2925731 : Blo 1949435 2925731 := bstep (se 1 (by rfl) ⟨2194298, by rfl⟩ : syracuseStep 2925731 = 4388597) B4388597
theorem B1950487 : Blo 1949435 1950487 := bstep (se 1 (by rfl) ⟨1462865, by rfl⟩ : syracuseStep 1950487 = 2925731) B2925731
theorem B6333877 : Blo 1949435 6333877 := bbase (se 5 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 6333877 = 593801) (by norm_num)
theorem B8445169 : Blo 1949435 8445169 := bstep (se 2 (by rfl) ⟨3166938, by rfl⟩ : syracuseStep 8445169 = 6333877) B6333877
theorem B11260225 : Blo 1949435 11260225 := bstep (se 2 (by rfl) ⟨4222584, by rfl⟩ : syracuseStep 11260225 = 8445169) B8445169
theorem B15013633 : Blo 1949435 15013633 := bstep (se 2 (by rfl) ⟨5630112, by rfl⟩ : syracuseStep 15013633 = 11260225) B11260225
theorem B20018177 : Blo 1949435 20018177 := bstep (se 2 (by rfl) ⟨7506816, by rfl⟩ : syracuseStep 20018177 = 15013633) B15013633
theorem B13345451 : Blo 1949435 13345451 := bstep (se 1 (by rfl) ⟨10009088, by rfl⟩ : syracuseStep 13345451 = 20018177) B20018177
theorem B8896967 : Blo 1949435 8896967 := bstep (se 1 (by rfl) ⟨6672725, by rfl⟩ : syracuseStep 8896967 = 13345451) B13345451
theorem B5931311 : Blo 1949435 5931311 := bstep (se 1 (by rfl) ⟨4448483, by rfl⟩ : syracuseStep 5931311 = 8896967) B8896967
theorem B15816829 : Blo 1949435 15816829 := bstep (se 3 (by rfl) ⟨2965655, by rfl⟩ : syracuseStep 15816829 = 5931311) B5931311
theorem B21089105 : Blo 1949435 21089105 := bstep (se 2 (by rfl) ⟨7908414, by rfl⟩ : syracuseStep 21089105 = 15816829) B15816829
theorem B14059403 : Blo 1949435 14059403 := bstep (se 1 (by rfl) ⟨10544552, by rfl⟩ : syracuseStep 14059403 = 21089105) B21089105
theorem B9372935 : Blo 1949435 9372935 := bstep (se 1 (by rfl) ⟨7029701, by rfl⟩ : syracuseStep 9372935 = 14059403) B14059403
theorem B24994493 : Blo 1949435 24994493 := bstep (se 3 (by rfl) ⟨4686467, by rfl⟩ : syracuseStep 24994493 = 9372935) B9372935
theorem B16662995 : Blo 1949435 16662995 := bstep (se 1 (by rfl) ⟨12497246, by rfl⟩ : syracuseStep 16662995 = 24994493) B24994493
theorem B11108663 : Blo 1949435 11108663 := bstep (se 1 (by rfl) ⟨8331497, by rfl⟩ : syracuseStep 11108663 = 16662995) B16662995
theorem B7405775 : Blo 1949435 7405775 := bstep (se 1 (by rfl) ⟨5554331, by rfl⟩ : syracuseStep 7405775 = 11108663) B11108663
theorem B4937183 : Blo 1949435 4937183 := bstep (se 1 (by rfl) ⟨3702887, by rfl⟩ : syracuseStep 4937183 = 7405775) B7405775
theorem B3291455 : Blo 1949435 3291455 := bstep (se 1 (by rfl) ⟨2468591, by rfl⟩ : syracuseStep 3291455 = 4937183) B4937183
theorem B2194303 : Blo 1949435 2194303 := bstep (se 1 (by rfl) ⟨1645727, by rfl⟩ : syracuseStep 2194303 = 3291455) B3291455
theorem B2925737 : Blo 1949435 2925737 := bstep (se 2 (by rfl) ⟨1097151, by rfl⟩ : syracuseStep 2925737 = 2194303) B2194303
theorem B1950491 : Blo 1949435 1950491 := bstep (se 1 (by rfl) ⟨1462868, by rfl⟩ : syracuseStep 1950491 = 2925737) B2925737
theorem B4165757 : Blo 1949435 4165757 := bbase (se 3 (by rfl) ⟨781079, by rfl⟩ : syracuseStep 4165757 = 1562159) (by norm_num)
theorem B2777171 : Blo 1949435 2777171 := bstep (se 1 (by rfl) ⟨2082878, by rfl⟩ : syracuseStep 2777171 = 4165757) B4165757
theorem B7405789 : Blo 1949435 7405789 := bstep (se 3 (by rfl) ⟨1388585, by rfl⟩ : syracuseStep 7405789 = 2777171) B2777171
theorem B9874385 : Blo 1949435 9874385 := bstep (se 2 (by rfl) ⟨3702894, by rfl⟩ : syracuseStep 9874385 = 7405789) B7405789
theorem B6582923 : Blo 1949435 6582923 := bstep (se 1 (by rfl) ⟨4937192, by rfl⟩ : syracuseStep 6582923 = 9874385) B9874385
theorem B4388615 : Blo 1949435 4388615 := bstep (se 1 (by rfl) ⟨3291461, by rfl⟩ : syracuseStep 4388615 = 6582923) B6582923
theorem B2925743 : Blo 1949435 2925743 := bstep (se 1 (by rfl) ⟨2194307, by rfl⟩ : syracuseStep 2925743 = 4388615) B4388615
theorem B1950495 : Blo 1949435 1950495 := bstep (se 1 (by rfl) ⟨1462871, by rfl⟩ : syracuseStep 1950495 = 2925743) B2925743
theorem B2925749 : Blo 1949435 2925749 := bbase (se 5 (by rfl) ⟨137144, by rfl⟩ : syracuseStep 2925749 = 274289) (by norm_num)
theorem B1950499 : Blo 1949435 1950499 := bstep (se 1 (by rfl) ⟨1462874, by rfl⟩ : syracuseStep 1950499 = 2925749) B2925749
theorem B4937213 : Blo 1949435 4937213 := bbase (se 3 (by rfl) ⟨925727, by rfl⟩ : syracuseStep 4937213 = 1851455) (by norm_num)
theorem B3291475 : Blo 1949435 3291475 := bstep (se 1 (by rfl) ⟨2468606, by rfl⟩ : syracuseStep 3291475 = 4937213) B4937213
theorem B4388633 : Blo 1949435 4388633 := bstep (se 2 (by rfl) ⟨1645737, by rfl⟩ : syracuseStep 4388633 = 3291475) B3291475
theorem B2925755 : Blo 1949435 2925755 := bstep (se 1 (by rfl) ⟨2194316, by rfl⟩ : syracuseStep 2925755 = 4388633) B4388633
theorem B1950503 : Blo 1949435 1950503 := bstep (se 1 (by rfl) ⟨1462877, by rfl⟩ : syracuseStep 1950503 = 2925755) B2925755
theorem B2194321 : Blo 1949435 2194321 := bbase (se 2 (by rfl) ⟨822870, by rfl⟩ : syracuseStep 2194321 = 1645741) (by norm_num)
theorem B2925761 : Blo 1949435 2925761 := bstep (se 2 (by rfl) ⟨1097160, by rfl⟩ : syracuseStep 2925761 = 2194321) B2194321
theorem B1950507 : Blo 1949435 1950507 := bstep (se 1 (by rfl) ⟨1462880, by rfl⟩ : syracuseStep 1950507 = 2925761) B2925761
theorem B3702925 : Blo 1949435 3702925 := bbase (se 3 (by rfl) ⟨694298, by rfl⟩ : syracuseStep 3702925 = 1388597) (by norm_num)
theorem B4937233 : Blo 1949435 4937233 := bstep (se 2 (by rfl) ⟨1851462, by rfl⟩ : syracuseStep 4937233 = 3702925) B3702925
theorem B6582977 : Blo 1949435 6582977 := bstep (se 2 (by rfl) ⟨2468616, by rfl⟩ : syracuseStep 6582977 = 4937233) B4937233
theorem B4388651 : Blo 1949435 4388651 := bstep (se 1 (by rfl) ⟨3291488, by rfl⟩ : syracuseStep 4388651 = 6582977) B6582977
theorem B2925767 : Blo 1949435 2925767 := bstep (se 1 (by rfl) ⟨2194325, by rfl⟩ : syracuseStep 2925767 = 4388651) B4388651
theorem B1950511 : Blo 1949435 1950511 := bstep (se 1 (by rfl) ⟨1462883, by rfl⟩ : syracuseStep 1950511 = 2925767) B2925767
theorem B2925773 : Blo 1949435 2925773 := bbase (se 3 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 2925773 = 1097165) (by norm_num)
theorem B1950515 : Blo 1949435 1950515 := bstep (se 1 (by rfl) ⟨1462886, by rfl⟩ : syracuseStep 1950515 = 2925773) B2925773
theorem B4388669 : Blo 1949435 4388669 := bbase (se 3 (by rfl) ⟨822875, by rfl⟩ : syracuseStep 4388669 = 1645751) (by norm_num)
theorem B2925779 : Blo 1949435 2925779 := bstep (se 1 (by rfl) ⟨2194334, by rfl⟩ : syracuseStep 2925779 = 4388669) B4388669
theorem B1950519 : Blo 1949435 1950519 := bstep (se 1 (by rfl) ⟨1462889, by rfl⟩ : syracuseStep 1950519 = 2925779) B2925779
theorem B3291509 : Blo 1949435 3291509 := bbase (se 5 (by rfl) ⟨154289, by rfl⟩ : syracuseStep 3291509 = 308579) (by norm_num)
theorem B2194339 : Blo 1949435 2194339 := bstep (se 1 (by rfl) ⟨1645754, by rfl⟩ : syracuseStep 2194339 = 3291509) B3291509
theorem B2925785 : Blo 1949435 2925785 := bstep (se 2 (by rfl) ⟨1097169, by rfl⟩ : syracuseStep 2925785 = 2194339) B2194339
theorem B1950523 : Blo 1949435 1950523 := bstep (se 1 (by rfl) ⟨1462892, by rfl⟩ : syracuseStep 1950523 = 2925785) B2925785
theorem B2343277 : Blo 1949435 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B3124369 : Blo 1949435 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B4165825 : Blo 1949435 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B5554433 : Blo 1949435 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B14811821 : Blo 1949435 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B9874547 : Blo 1949435 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B6583031 : Blo 1949435 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B4388687 : Blo 1949435 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B2925791 : Blo 1949435 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B1950527 : Blo 1949435 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B2925797 : Blo 1949435 2925797 := bbase (se 4 (by rfl) ⟨274293, by rfl⟩ : syracuseStep 2925797 = 548587) (by norm_num)
theorem B1950531 : Blo 1949435 1950531 := bstep (se 1 (by rfl) ⟨1462898, by rfl⟩ : syracuseStep 1950531 = 2925797) B2925797
theorem B1977149 : Blo 1949435 1977149 := bbase (se 3 (by rfl) ⟨370715, by rfl⟩ : syracuseStep 1977149 = 741431) (by norm_num)
theorem B5272397 : Blo 1949435 5272397 := bstep (se 3 (by rfl) ⟨988574, by rfl⟩ : syracuseStep 5272397 = 1977149) B1977149
theorem B3514931 : Blo 1949435 3514931 := bstep (se 1 (by rfl) ⟨2636198, by rfl⟩ : syracuseStep 3514931 = 5272397) B5272397
theorem B2343287 : Blo 1949435 2343287 := bstep (se 1 (by rfl) ⟨1757465, by rfl⟩ : syracuseStep 2343287 = 3514931) B3514931
theorem B6248765 : Blo 1949435 6248765 := bstep (se 3 (by rfl) ⟨1171643, by rfl⟩ : syracuseStep 6248765 = 2343287) B2343287
theorem B4165843 : Blo 1949435 4165843 := bstep (se 1 (by rfl) ⟨3124382, by rfl⟩ : syracuseStep 4165843 = 6248765) B6248765
theorem B5554457 : Blo 1949435 5554457 := bstep (se 2 (by rfl) ⟨2082921, by rfl⟩ : syracuseStep 5554457 = 4165843) B4165843
theorem B3702971 : Blo 1949435 3702971 := bstep (se 1 (by rfl) ⟨2777228, by rfl⟩ : syracuseStep 3702971 = 5554457) B5554457
theorem B2468647 : Blo 1949435 2468647 := bstep (se 1 (by rfl) ⟨1851485, by rfl⟩ : syracuseStep 2468647 = 3702971) B3702971
theorem B3291529 : Blo 1949435 3291529 := bstep (se 2 (by rfl) ⟨1234323, by rfl⟩ : syracuseStep 3291529 = 2468647) B2468647
theorem B4388705 : Blo 1949435 4388705 := bstep (se 2 (by rfl) ⟨1645764, by rfl⟩ : syracuseStep 4388705 = 3291529) B3291529
theorem B2925803 : Blo 1949435 2925803 := bstep (se 1 (by rfl) ⟨2194352, by rfl⟩ : syracuseStep 2925803 = 4388705) B4388705
theorem B1950535 : Blo 1949435 1950535 := bstep (se 1 (by rfl) ⟨1462901, by rfl⟩ : syracuseStep 1950535 = 2925803) B2925803
theorem B2194357 : Blo 1949435 2194357 := bbase (se 5 (by rfl) ⟨102860, by rfl⟩ : syracuseStep 2194357 = 205721) (by norm_num)
theorem B2925809 : Blo 1949435 2925809 := bstep (se 2 (by rfl) ⟨1097178, by rfl⟩ : syracuseStep 2925809 = 2194357) B2194357
theorem B1950539 : Blo 1949435 1950539 := bstep (se 1 (by rfl) ⟨1462904, by rfl⟩ : syracuseStep 1950539 = 2925809) B2925809
theorem B2468657 : Blo 1949435 2468657 := bbase (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) (by norm_num)
theorem B6583085 : Blo 1949435 6583085 := bstep (se 3 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 6583085 = 2468657) B2468657
theorem B4388723 : Blo 1949435 4388723 := bstep (se 1 (by rfl) ⟨3291542, by rfl⟩ : syracuseStep 4388723 = 6583085) B6583085
theorem B2925815 : Blo 1949435 2925815 := bstep (se 1 (by rfl) ⟨2194361, by rfl⟩ : syracuseStep 2925815 = 4388723) B4388723
theorem B1950543 : Blo 1949435 1950543 := bstep (se 1 (by rfl) ⟨1462907, by rfl⟩ : syracuseStep 1950543 = 2925815) B2925815
theorem B2925821 : Blo 1949435 2925821 := bbase (se 3 (by rfl) ⟨548591, by rfl⟩ : syracuseStep 2925821 = 1097183) (by norm_num)
theorem B1950547 : Blo 1949435 1950547 := bstep (se 1 (by rfl) ⟨1462910, by rfl⟩ : syracuseStep 1950547 = 2925821) B2925821
theorem B4388741 : Blo 1949435 4388741 := bbase (se 4 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 4388741 = 822889) (by norm_num)
theorem B2925827 : Blo 1949435 2925827 := bstep (se 1 (by rfl) ⟨2194370, by rfl⟩ : syracuseStep 2925827 = 4388741) B4388741
theorem B1950551 : Blo 1949435 1950551 := bstep (se 1 (by rfl) ⟨1462913, by rfl⟩ : syracuseStep 1950551 = 2925827) B2925827
theorem B3753533 : Blo 1949435 3753533 := bbase (se 3 (by rfl) ⟨703787, by rfl⟩ : syracuseStep 3753533 = 1407575) (by norm_num)
theorem B10009421 : Blo 1949435 10009421 := bstep (se 3 (by rfl) ⟨1876766, by rfl⟩ : syracuseStep 10009421 = 3753533) B3753533
theorem B6672947 : Blo 1949435 6672947 := bstep (se 1 (by rfl) ⟨5004710, by rfl⟩ : syracuseStep 6672947 = 10009421) B10009421
theorem B17794525 : Blo 1949435 17794525 := bstep (se 3 (by rfl) ⟨3336473, by rfl⟩ : syracuseStep 17794525 = 6672947) B6672947
theorem B23726033 : Blo 1949435 23726033 := bstep (se 2 (by rfl) ⟨8897262, by rfl⟩ : syracuseStep 23726033 = 17794525) B17794525
theorem B15817355 : Blo 1949435 15817355 := bstep (se 1 (by rfl) ⟨11863016, by rfl⟩ : syracuseStep 15817355 = 23726033) B23726033
theorem B10544903 : Blo 1949435 10544903 := bstep (se 1 (by rfl) ⟨7908677, by rfl⟩ : syracuseStep 10544903 = 15817355) B15817355
theorem B7029935 : Blo 1949435 7029935 := bstep (se 1 (by rfl) ⟨5272451, by rfl⟩ : syracuseStep 7029935 = 10544903) B10544903
theorem B4686623 : Blo 1949435 4686623 := bstep (se 1 (by rfl) ⟨3514967, by rfl⟩ : syracuseStep 4686623 = 7029935) B7029935
theorem B3124415 : Blo 1949435 3124415 := bstep (se 1 (by rfl) ⟨2343311, by rfl⟩ : syracuseStep 3124415 = 4686623) B4686623
theorem B2082943 : Blo 1949435 2082943 := bstep (se 1 (by rfl) ⟨1562207, by rfl⟩ : syracuseStep 2082943 = 3124415) B3124415
theorem B2777257 : Blo 1949435 2777257 := bstep (se 2 (by rfl) ⟨1041471, by rfl⟩ : syracuseStep 2777257 = 2082943) B2082943
theorem B3703009 : Blo 1949435 3703009 := bstep (se 2 (by rfl) ⟨1388628, by rfl⟩ : syracuseStep 3703009 = 2777257) B2777257
theorem B4937345 : Blo 1949435 4937345 := bstep (se 2 (by rfl) ⟨1851504, by rfl⟩ : syracuseStep 4937345 = 3703009) B3703009
theorem B3291563 : Blo 1949435 3291563 := bstep (se 1 (by rfl) ⟨2468672, by rfl⟩ : syracuseStep 3291563 = 4937345) B4937345
theorem B2194375 : Blo 1949435 2194375 := bstep (se 1 (by rfl) ⟨1645781, by rfl⟩ : syracuseStep 2194375 = 3291563) B3291563
theorem B2925833 : Blo 1949435 2925833 := bstep (se 2 (by rfl) ⟨1097187, by rfl⟩ : syracuseStep 2925833 = 2194375) B2194375
theorem B1950555 : Blo 1949435 1950555 := bstep (se 1 (by rfl) ⟨1462916, by rfl⟩ : syracuseStep 1950555 = 2925833) B2925833
theorem B9874709 : Blo 1949435 9874709 := bbase (se 6 (by rfl) ⟨231438, by rfl⟩ : syracuseStep 9874709 = 462877) (by norm_num)
theorem B6583139 : Blo 1949435 6583139 := bstep (se 1 (by rfl) ⟨4937354, by rfl⟩ : syracuseStep 6583139 = 9874709) B9874709
theorem B4388759 : Blo 1949435 4388759 := bstep (se 1 (by rfl) ⟨3291569, by rfl⟩ : syracuseStep 4388759 = 6583139) B6583139
theorem B2925839 : Blo 1949435 2925839 := bstep (se 1 (by rfl) ⟨2194379, by rfl⟩ : syracuseStep 2925839 = 4388759) B4388759
theorem B1950559 : Blo 1949435 1950559 := bstep (se 1 (by rfl) ⟨1462919, by rfl⟩ : syracuseStep 1950559 = 2925839) B2925839
theorem B2925845 : Blo 1949435 2925845 := bbase (se 6 (by rfl) ⟨68574, by rfl⟩ : syracuseStep 2925845 = 137149) (by norm_num)
theorem B1950563 : Blo 1949435 1950563 := bstep (se 1 (by rfl) ⟨1462922, by rfl⟩ : syracuseStep 1950563 = 2925845) B2925845
theorem B11260661 : Blo 1949435 11260661 := bbase (se 5 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 11260661 = 1055687) (by norm_num)
theorem B30028429 : Blo 1949435 30028429 := bstep (se 3 (by rfl) ⟨5630330, by rfl⟩ : syracuseStep 30028429 = 11260661) B11260661
theorem B40037905 : Blo 1949435 40037905 := bstep (se 2 (by rfl) ⟨15014214, by rfl⟩ : syracuseStep 40037905 = 30028429) B30028429
theorem B53383873 : Blo 1949435 53383873 := bstep (se 2 (by rfl) ⟨20018952, by rfl⟩ : syracuseStep 53383873 = 40037905) B40037905
theorem B71178497 : Blo 1949435 71178497 := bstep (se 2 (by rfl) ⟨26691936, by rfl⟩ : syracuseStep 71178497 = 53383873) B53383873
theorem B47452331 : Blo 1949435 47452331 := bstep (se 1 (by rfl) ⟨35589248, by rfl⟩ : syracuseStep 47452331 = 71178497) B71178497
theorem B31634887 : Blo 1949435 31634887 := bstep (se 1 (by rfl) ⟨23726165, by rfl⟩ : syracuseStep 31634887 = 47452331) B47452331
theorem B42179849 : Blo 1949435 42179849 := bstep (se 2 (by rfl) ⟨15817443, by rfl⟩ : syracuseStep 42179849 = 31634887) B31634887
theorem B28119899 : Blo 1949435 28119899 := bstep (se 1 (by rfl) ⟨21089924, by rfl⟩ : syracuseStep 28119899 = 42179849) B42179849
theorem B18746599 : Blo 1949435 18746599 := bstep (se 1 (by rfl) ⟨14059949, by rfl⟩ : syracuseStep 18746599 = 28119899) B28119899
theorem B24995465 : Blo 1949435 24995465 := bstep (se 2 (by rfl) ⟨9373299, by rfl⟩ : syracuseStep 24995465 = 18746599) B18746599
theorem B16663643 : Blo 1949435 16663643 := bstep (se 1 (by rfl) ⟨12497732, by rfl⟩ : syracuseStep 16663643 = 24995465) B24995465
theorem B11109095 : Blo 1949435 11109095 := bstep (se 1 (by rfl) ⟨8331821, by rfl⟩ : syracuseStep 11109095 = 16663643) B16663643
theorem B7406063 : Blo 1949435 7406063 := bstep (se 1 (by rfl) ⟨5554547, by rfl⟩ : syracuseStep 7406063 = 11109095) B11109095
theorem B4937375 : Blo 1949435 4937375 := bstep (se 1 (by rfl) ⟨3703031, by rfl⟩ : syracuseStep 4937375 = 7406063) B7406063
theorem B3291583 : Blo 1949435 3291583 := bstep (se 1 (by rfl) ⟨2468687, by rfl⟩ : syracuseStep 3291583 = 4937375) B4937375
theorem B4388777 : Blo 1949435 4388777 := bstep (se 2 (by rfl) ⟨1645791, by rfl⟩ : syracuseStep 4388777 = 3291583) B3291583
theorem B2925851 : Blo 1949435 2925851 := bstep (se 1 (by rfl) ⟨2194388, by rfl⟩ : syracuseStep 2925851 = 4388777) B4388777
theorem B1950567 : Blo 1949435 1950567 := bstep (se 1 (by rfl) ⟨1462925, by rfl⟩ : syracuseStep 1950567 = 2925851) B2925851
theorem B2194393 : Blo 1949435 2194393 := bbase (se 2 (by rfl) ⟨822897, by rfl⟩ : syracuseStep 2194393 = 1645795) (by norm_num)
theorem B2925857 : Blo 1949435 2925857 := bstep (se 2 (by rfl) ⟨1097196, by rfl⟩ : syracuseStep 2925857 = 2194393) B2194393
theorem B1950571 : Blo 1949435 1950571 := bstep (se 1 (by rfl) ⟨1462928, by rfl⟩ : syracuseStep 1950571 = 2925857) B2925857
theorem B2777285 : Blo 1949435 2777285 := bbase (se 4 (by rfl) ⟨260370, by rfl⟩ : syracuseStep 2777285 = 520741) (by norm_num)
theorem B7406093 : Blo 1949435 7406093 := bstep (se 3 (by rfl) ⟨1388642, by rfl⟩ : syracuseStep 7406093 = 2777285) B2777285
theorem B4937395 : Blo 1949435 4937395 := bstep (se 1 (by rfl) ⟨3703046, by rfl⟩ : syracuseStep 4937395 = 7406093) B7406093
theorem B6583193 : Blo 1949435 6583193 := bstep (se 2 (by rfl) ⟨2468697, by rfl⟩ : syracuseStep 6583193 = 4937395) B4937395
theorem B4388795 : Blo 1949435 4388795 := bstep (se 1 (by rfl) ⟨3291596, by rfl⟩ : syracuseStep 4388795 = 6583193) B6583193
theorem B2925863 : Blo 1949435 2925863 := bstep (se 1 (by rfl) ⟨2194397, by rfl⟩ : syracuseStep 2925863 = 4388795) B4388795
theorem B1950575 : Blo 1949435 1950575 := bstep (se 1 (by rfl) ⟨1462931, by rfl⟩ : syracuseStep 1950575 = 2925863) B2925863
theorem B2925869 : Blo 1949435 2925869 := bbase (se 3 (by rfl) ⟨548600, by rfl⟩ : syracuseStep 2925869 = 1097201) (by norm_num)
theorem B1950579 : Blo 1949435 1950579 := bstep (se 1 (by rfl) ⟨1462934, by rfl⟩ : syracuseStep 1950579 = 2925869) B2925869
theorem B4388813 : Blo 1949435 4388813 := bbase (se 3 (by rfl) ⟨822902, by rfl⟩ : syracuseStep 4388813 = 1645805) (by norm_num)
theorem B2925875 : Blo 1949435 2925875 := bstep (se 1 (by rfl) ⟨2194406, by rfl⟩ : syracuseStep 2925875 = 4388813) B4388813
theorem B1950583 : Blo 1949435 1950583 := bstep (se 1 (by rfl) ⟨1462937, by rfl⟩ : syracuseStep 1950583 = 2925875) B2925875
theorem B2468713 : Blo 1949435 2468713 := bbase (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) (by norm_num)
theorem B3291617 : Blo 1949435 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B2194411 : Blo 1949435 2194411 := bstep (se 1 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 2194411 = 3291617) B3291617
theorem B2925881 : Blo 1949435 2925881 := bstep (se 2 (by rfl) ⟨1097205, by rfl⟩ : syracuseStep 2925881 = 2194411) B2194411
theorem B1950587 : Blo 1949435 1950587 := bstep (se 1 (by rfl) ⟨1462940, by rfl⟩ : syracuseStep 1950587 = 2925881) B2925881
theorem B1977205 : Blo 1949435 1977205 := bbase (se 5 (by rfl) ⟨92681, by rfl⟩ : syracuseStep 1977205 = 185363) (by norm_num)
theorem B2636273 : Blo 1949435 2636273 := bstep (se 2 (by rfl) ⟨988602, by rfl⟩ : syracuseStep 2636273 = 1977205) B1977205
theorem B7030061 : Blo 1949435 7030061 := bstep (se 3 (by rfl) ⟨1318136, by rfl⟩ : syracuseStep 7030061 = 2636273) B2636273
theorem B4686707 : Blo 1949435 4686707 := bstep (se 1 (by rfl) ⟨3515030, by rfl⟩ : syracuseStep 4686707 = 7030061) B7030061
theorem B12497885 : Blo 1949435 12497885 := bstep (se 3 (by rfl) ⟨2343353, by rfl⟩ : syracuseStep 12497885 = 4686707) B4686707
theorem B8331923 : Blo 1949435 8331923 := bstep (se 1 (by rfl) ⟨6248942, by rfl⟩ : syracuseStep 8331923 = 12497885) B12497885
theorem B22218461 : Blo 1949435 22218461 := bstep (se 3 (by rfl) ⟨4165961, by rfl⟩ : syracuseStep 22218461 = 8331923) B8331923
theorem B14812307 : Blo 1949435 14812307 := bstep (se 1 (by rfl) ⟨11109230, by rfl⟩ : syracuseStep 14812307 = 22218461) B22218461
theorem B9874871 : Blo 1949435 9874871 := bstep (se 1 (by rfl) ⟨7406153, by rfl⟩ : syracuseStep 9874871 = 14812307) B14812307
theorem B6583247 : Blo 1949435 6583247 := bstep (se 1 (by rfl) ⟨4937435, by rfl⟩ : syracuseStep 6583247 = 9874871) B9874871
theorem B4388831 : Blo 1949435 4388831 := bstep (se 1 (by rfl) ⟨3291623, by rfl⟩ : syracuseStep 4388831 = 6583247) B6583247
theorem B2925887 : Blo 1949435 2925887 := bstep (se 1 (by rfl) ⟨2194415, by rfl⟩ : syracuseStep 2925887 = 4388831) B4388831
theorem B1950591 : Blo 1949435 1950591 := bstep (se 1 (by rfl) ⟨1462943, by rfl⟩ : syracuseStep 1950591 = 2925887) B2925887
theorem B2925893 : Blo 1949435 2925893 := bbase (se 4 (by rfl) ⟨274302, by rfl⟩ : syracuseStep 2925893 = 548605) (by norm_num)
theorem B1950595 : Blo 1949435 1950595 := bstep (se 1 (by rfl) ⟨1462946, by rfl⟩ : syracuseStep 1950595 = 2925893) B2925893
theorem B3291637 : Blo 1949435 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B4388849 : Blo 1949435 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B2925899 : Blo 1949435 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B1950599 : Blo 1949435 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B2194429 : Blo 1949435 2194429 := bbase (se 3 (by rfl) ⟨411455, by rfl⟩ : syracuseStep 2194429 = 822911) (by norm_num)
theorem B2925905 : Blo 1949435 2925905 := bstep (se 2 (by rfl) ⟨1097214, by rfl⟩ : syracuseStep 2925905 = 2194429) B2194429
theorem B1950603 : Blo 1949435 1950603 := bstep (se 1 (by rfl) ⟨1462952, by rfl⟩ : syracuseStep 1950603 = 2925905) B2925905
theorem B6583301 : Blo 1949435 6583301 := bbase (se 4 (by rfl) ⟨617184, by rfl⟩ : syracuseStep 6583301 = 1234369) (by norm_num)
theorem B4388867 : Blo 1949435 4388867 := bstep (se 1 (by rfl) ⟨3291650, by rfl⟩ : syracuseStep 4388867 = 6583301) B6583301
theorem B2925911 : Blo 1949435 2925911 := bstep (se 1 (by rfl) ⟨2194433, by rfl⟩ : syracuseStep 2925911 = 4388867) B4388867
theorem B1950607 : Blo 1949435 1950607 := bstep (se 1 (by rfl) ⟨1462955, by rfl⟩ : syracuseStep 1950607 = 2925911) B2925911
theorem B2925917 : Blo 1949435 2925917 := bbase (se 3 (by rfl) ⟨548609, by rfl⟩ : syracuseStep 2925917 = 1097219) (by norm_num)
theorem B1950611 : Blo 1949435 1950611 := bstep (se 1 (by rfl) ⟨1462958, by rfl⟩ : syracuseStep 1950611 = 2925917) B2925917
theorem B4388885 : Blo 1949435 4388885 := bbase (se 6 (by rfl) ⟨102864, by rfl⟩ : syracuseStep 4388885 = 205729) (by norm_num)
theorem B2925923 : Blo 1949435 2925923 := bstep (se 1 (by rfl) ⟨2194442, by rfl⟩ : syracuseStep 2925923 = 4388885) B4388885
theorem B1950615 : Blo 1949435 1950615 := bstep (se 1 (by rfl) ⟨1462961, by rfl⟩ : syracuseStep 1950615 = 2925923) B2925923
theorem B7406261 : Blo 1949435 7406261 := bbase (se 5 (by rfl) ⟨347168, by rfl⟩ : syracuseStep 7406261 = 694337) (by norm_num)
theorem B4937507 : Blo 1949435 4937507 := bstep (se 1 (by rfl) ⟨3703130, by rfl⟩ : syracuseStep 4937507 = 7406261) B7406261
theorem B3291671 : Blo 1949435 3291671 := bstep (se 1 (by rfl) ⟨2468753, by rfl⟩ : syracuseStep 3291671 = 4937507) B4937507
theorem B2194447 : Blo 1949435 2194447 := bstep (se 1 (by rfl) ⟨1645835, by rfl⟩ : syracuseStep 2194447 = 3291671) B3291671
theorem B2925929 : Blo 1949435 2925929 := bstep (se 2 (by rfl) ⟨1097223, by rfl⟩ : syracuseStep 2925929 = 2194447) B2194447
theorem B1950619 : Blo 1949435 1950619 := bstep (se 1 (by rfl) ⟨1462964, by rfl⟩ : syracuseStep 1950619 = 2925929) B2925929
theorem B2636317 : Blo 1949435 2636317 := bbase (se 3 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 2636317 = 988619) (by norm_num)
theorem B3515089 : Blo 1949435 3515089 := bstep (se 2 (by rfl) ⟨1318158, by rfl⟩ : syracuseStep 3515089 = 2636317) B2636317
theorem B4686785 : Blo 1949435 4686785 := bstep (se 2 (by rfl) ⟨1757544, by rfl⟩ : syracuseStep 4686785 = 3515089) B3515089
theorem B3124523 : Blo 1949435 3124523 := bstep (se 1 (by rfl) ⟨2343392, by rfl⟩ : syracuseStep 3124523 = 4686785) B4686785
theorem B2083015 : Blo 1949435 2083015 := bstep (se 1 (by rfl) ⟨1562261, by rfl⟩ : syracuseStep 2083015 = 3124523) B3124523
theorem B11109413 : Blo 1949435 11109413 := bstep (se 4 (by rfl) ⟨1041507, by rfl⟩ : syracuseStep 11109413 = 2083015) B2083015
theorem B7406275 : Blo 1949435 7406275 := bstep (se 1 (by rfl) ⟨5554706, by rfl⟩ : syracuseStep 7406275 = 11109413) B11109413
theorem B9875033 : Blo 1949435 9875033 := bstep (se 2 (by rfl) ⟨3703137, by rfl⟩ : syracuseStep 9875033 = 7406275) B7406275
theorem B6583355 : Blo 1949435 6583355 := bstep (se 1 (by rfl) ⟨4937516, by rfl⟩ : syracuseStep 6583355 = 9875033) B9875033
theorem B4388903 : Blo 1949435 4388903 := bstep (se 1 (by rfl) ⟨3291677, by rfl⟩ : syracuseStep 4388903 = 6583355) B6583355
theorem B2925935 : Blo 1949435 2925935 := bstep (se 1 (by rfl) ⟨2194451, by rfl⟩ : syracuseStep 2925935 = 4388903) B4388903
theorem B1950623 : Blo 1949435 1950623 := bstep (se 1 (by rfl) ⟨1462967, by rfl⟩ : syracuseStep 1950623 = 2925935) B2925935
theorem B2925941 : Blo 1949435 2925941 := bbase (se 5 (by rfl) ⟨137153, by rfl⟩ : syracuseStep 2925941 = 274307) (by norm_num)
theorem B1950627 : Blo 1949435 1950627 := bstep (se 1 (by rfl) ⟨1462970, by rfl⟩ : syracuseStep 1950627 = 2925941) B2925941
theorem B2777365 : Blo 1949435 2777365 := bbase (se 6 (by rfl) ⟨65094, by rfl⟩ : syracuseStep 2777365 = 130189) (by norm_num)
theorem B3703153 : Blo 1949435 3703153 := bstep (se 2 (by rfl) ⟨1388682, by rfl⟩ : syracuseStep 3703153 = 2777365) B2777365
theorem B4937537 : Blo 1949435 4937537 := bstep (se 2 (by rfl) ⟨1851576, by rfl⟩ : syracuseStep 4937537 = 3703153) B3703153
theorem B3291691 : Blo 1949435 3291691 := bstep (se 1 (by rfl) ⟨2468768, by rfl⟩ : syracuseStep 3291691 = 4937537) B4937537
theorem B4388921 : Blo 1949435 4388921 := bstep (se 2 (by rfl) ⟨1645845, by rfl⟩ : syracuseStep 4388921 = 3291691) B3291691
theorem B2925947 : Blo 1949435 2925947 := bstep (se 1 (by rfl) ⟨2194460, by rfl⟩ : syracuseStep 2925947 = 4388921) B4388921
theorem B1950631 : Blo 1949435 1950631 := bstep (se 1 (by rfl) ⟨1462973, by rfl⟩ : syracuseStep 1950631 = 2925947) B2925947
theorem B2194465 : Blo 1949435 2194465 := bbase (se 2 (by rfl) ⟨822924, by rfl⟩ : syracuseStep 2194465 = 1645849) (by norm_num)
theorem B2925953 : Blo 1949435 2925953 := bstep (se 2 (by rfl) ⟨1097232, by rfl⟩ : syracuseStep 2925953 = 2194465) B2194465
theorem B1950635 : Blo 1949435 1950635 := bstep (se 1 (by rfl) ⟨1462976, by rfl⟩ : syracuseStep 1950635 = 2925953) B2925953
theorem B4937557 : Blo 1949435 4937557 := bbase (se 9 (by rfl) ⟨14465, by rfl⟩ : syracuseStep 4937557 = 28931) (by norm_num)
theorem B6583409 : Blo 1949435 6583409 := bstep (se 2 (by rfl) ⟨2468778, by rfl⟩ : syracuseStep 6583409 = 4937557) B4937557
theorem B4388939 : Blo 1949435 4388939 := bstep (se 1 (by rfl) ⟨3291704, by rfl⟩ : syracuseStep 4388939 = 6583409) B6583409
theorem B2925959 : Blo 1949435 2925959 := bstep (se 1 (by rfl) ⟨2194469, by rfl⟩ : syracuseStep 2925959 = 4388939) B4388939
theorem B1950639 : Blo 1949435 1950639 := bstep (se 1 (by rfl) ⟨1462979, by rfl⟩ : syracuseStep 1950639 = 2925959) B2925959
theorem B2925965 : Blo 1949435 2925965 := bbase (se 3 (by rfl) ⟨548618, by rfl⟩ : syracuseStep 2925965 = 1097237) (by norm_num)
theorem B1950643 : Blo 1949435 1950643 := bstep (se 1 (by rfl) ⟨1462982, by rfl⟩ : syracuseStep 1950643 = 2925965) B2925965
theorem B4388957 : Blo 1949435 4388957 := bbase (se 3 (by rfl) ⟨822929, by rfl⟩ : syracuseStep 4388957 = 1645859) (by norm_num)
theorem B2925971 : Blo 1949435 2925971 := bstep (se 1 (by rfl) ⟨2194478, by rfl⟩ : syracuseStep 2925971 = 4388957) B4388957
theorem B1950647 : Blo 1949435 1950647 := bstep (se 1 (by rfl) ⟨1462985, by rfl⟩ : syracuseStep 1950647 = 2925971) B2925971
theorem B3291725 : Blo 1949435 3291725 := bbase (se 3 (by rfl) ⟨617198, by rfl⟩ : syracuseStep 3291725 = 1234397) (by norm_num)
theorem B2194483 : Blo 1949435 2194483 := bstep (se 1 (by rfl) ⟨1645862, by rfl⟩ : syracuseStep 2194483 = 3291725) B3291725
theorem B2925977 : Blo 1949435 2925977 := bstep (se 2 (by rfl) ⟨1097241, by rfl⟩ : syracuseStep 2925977 = 2194483) B2194483
theorem B1950651 : Blo 1949435 1950651 := bstep (se 1 (by rfl) ⟨1462988, by rfl⟩ : syracuseStep 1950651 = 2925977) B2925977
theorem B5004965 : Blo 1949435 5004965 := bbase (se 4 (by rfl) ⟨469215, by rfl⟩ : syracuseStep 5004965 = 938431) (by norm_num)
theorem B3336643 : Blo 1949435 3336643 := bstep (se 1 (by rfl) ⟨2502482, by rfl⟩ : syracuseStep 3336643 = 5004965) B5004965
theorem B4448857 : Blo 1949435 4448857 := bstep (se 2 (by rfl) ⟨1668321, by rfl⟩ : syracuseStep 4448857 = 3336643) B3336643
theorem B5931809 : Blo 1949435 5931809 := bstep (se 2 (by rfl) ⟨2224428, by rfl⟩ : syracuseStep 5931809 = 4448857) B4448857
theorem B3954539 : Blo 1949435 3954539 := bstep (se 1 (by rfl) ⟨2965904, by rfl⟩ : syracuseStep 3954539 = 5931809) B5931809
theorem B10545437 : Blo 1949435 10545437 := bstep (se 3 (by rfl) ⟨1977269, by rfl⟩ : syracuseStep 10545437 = 3954539) B3954539
theorem B28121165 : Blo 1949435 28121165 := bstep (se 3 (by rfl) ⟨5272718, by rfl⟩ : syracuseStep 28121165 = 10545437) B10545437
theorem B18747443 : Blo 1949435 18747443 := bstep (se 1 (by rfl) ⟨14060582, by rfl⟩ : syracuseStep 18747443 = 28121165) B28121165
theorem B12498295 : Blo 1949435 12498295 := bstep (se 1 (by rfl) ⟨9373721, by rfl⟩ : syracuseStep 12498295 = 18747443) B18747443
theorem B16664393 : Blo 1949435 16664393 := bstep (se 2 (by rfl) ⟨6249147, by rfl⟩ : syracuseStep 16664393 = 12498295) B12498295
theorem B11109595 : Blo 1949435 11109595 := bstep (se 1 (by rfl) ⟨8332196, by rfl⟩ : syracuseStep 11109595 = 16664393) B16664393
theorem B14812793 : Blo 1949435 14812793 := bstep (se 2 (by rfl) ⟨5554797, by rfl⟩ : syracuseStep 14812793 = 11109595) B11109595
theorem B9875195 : Blo 1949435 9875195 := bstep (se 1 (by rfl) ⟨7406396, by rfl⟩ : syracuseStep 9875195 = 14812793) B14812793
theorem B6583463 : Blo 1949435 6583463 := bstep (se 1 (by rfl) ⟨4937597, by rfl⟩ : syracuseStep 6583463 = 9875195) B9875195
theorem B4388975 : Blo 1949435 4388975 := bstep (se 1 (by rfl) ⟨3291731, by rfl⟩ : syracuseStep 4388975 = 6583463) B6583463
theorem B2925983 : Blo 1949435 2925983 := bstep (se 1 (by rfl) ⟨2194487, by rfl⟩ : syracuseStep 2925983 = 4388975) B4388975
theorem B1950655 : Blo 1949435 1950655 := bstep (se 1 (by rfl) ⟨1462991, by rfl⟩ : syracuseStep 1950655 = 2925983) B2925983
theorem B2925989 : Blo 1949435 2925989 := bbase (se 4 (by rfl) ⟨274311, by rfl⟩ : syracuseStep 2925989 = 548623) (by norm_num)
theorem B1950659 : Blo 1949435 1950659 := bstep (se 1 (by rfl) ⟨1462994, by rfl⟩ : syracuseStep 1950659 = 2925989) B2925989
theorem B2468809 : Blo 1949435 2468809 := bbase (se 2 (by rfl) ⟨925803, by rfl⟩ : syracuseStep 2468809 = 1851607) (by norm_num)
theorem B3291745 : Blo 1949435 3291745 := bstep (se 2 (by rfl) ⟨1234404, by rfl⟩ : syracuseStep 3291745 = 2468809) B2468809
theorem B4388993 : Blo 1949435 4388993 := bstep (se 2 (by rfl) ⟨1645872, by rfl⟩ : syracuseStep 4388993 = 3291745) B3291745
theorem B2925995 : Blo 1949435 2925995 := bstep (se 1 (by rfl) ⟨2194496, by rfl⟩ : syracuseStep 2925995 = 4388993) B4388993
theorem B1950663 : Blo 1949435 1950663 := bstep (se 1 (by rfl) ⟨1462997, by rfl⟩ : syracuseStep 1950663 = 2925995) B2925995
theorem B2194501 : Blo 1949435 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B2926001 : Blo 1949435 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B1950667 : Blo 1949435 1950667 := bstep (se 1 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 1950667 = 2926001) B2926001
theorem B3703229 : Blo 1949435 3703229 := bbase (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) (by norm_num)
theorem B2468819 : Blo 1949435 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B6583517 : Blo 1949435 6583517 := bstep (se 3 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 6583517 = 2468819) B2468819
theorem B4389011 : Blo 1949435 4389011 := bstep (se 1 (by rfl) ⟨3291758, by rfl⟩ : syracuseStep 4389011 = 6583517) B6583517
theorem B2926007 : Blo 1949435 2926007 := bstep (se 1 (by rfl) ⟨2194505, by rfl⟩ : syracuseStep 2926007 = 4389011) B4389011
theorem B1950671 : Blo 1949435 1950671 := bstep (se 1 (by rfl) ⟨1463003, by rfl⟩ : syracuseStep 1950671 = 2926007) B2926007
theorem B2926013 : Blo 1949435 2926013 := bbase (se 3 (by rfl) ⟨548627, by rfl⟩ : syracuseStep 2926013 = 1097255) (by norm_num)
theorem B1950675 : Blo 1949435 1950675 := bstep (se 1 (by rfl) ⟨1463006, by rfl⟩ : syracuseStep 1950675 = 2926013) B2926013
theorem B4389029 : Blo 1949435 4389029 := bbase (se 4 (by rfl) ⟨411471, by rfl⟩ : syracuseStep 4389029 = 822943) (by norm_num)
theorem B2926019 : Blo 1949435 2926019 := bstep (se 1 (by rfl) ⟨2194514, by rfl⟩ : syracuseStep 2926019 = 4389029) B4389029
theorem B1950679 : Blo 1949435 1950679 := bstep (se 1 (by rfl) ⟨1463009, by rfl⟩ : syracuseStep 1950679 = 2926019) B2926019
theorem B4937669 : Blo 1949435 4937669 := bbase (se 4 (by rfl) ⟨462906, by rfl⟩ : syracuseStep 4937669 = 925813) (by norm_num)
theorem B3291779 : Blo 1949435 3291779 := bstep (se 1 (by rfl) ⟨2468834, by rfl⟩ : syracuseStep 3291779 = 4937669) B4937669
theorem B2194519 : Blo 1949435 2194519 := bstep (se 1 (by rfl) ⟨1645889, by rfl⟩ : syracuseStep 2194519 = 3291779) B3291779
theorem B2926025 : Blo 1949435 2926025 := bstep (se 2 (by rfl) ⟨1097259, by rfl⟩ : syracuseStep 2926025 = 2194519) B2194519
theorem B1950683 : Blo 1949435 1950683 := bstep (se 1 (by rfl) ⟨1463012, by rfl⟩ : syracuseStep 1950683 = 2926025) B2926025
theorem B9373877 : Blo 1949435 9373877 := bbase (se 5 (by rfl) ⟨439400, by rfl⟩ : syracuseStep 9373877 = 878801) (by norm_num)
theorem B6249251 : Blo 1949435 6249251 := bstep (se 1 (by rfl) ⟨4686938, by rfl⟩ : syracuseStep 6249251 = 9373877) B9373877
theorem B4166167 : Blo 1949435 4166167 := bstep (se 1 (by rfl) ⟨3124625, by rfl⟩ : syracuseStep 4166167 = 6249251) B6249251
theorem B5554889 : Blo 1949435 5554889 := bstep (se 2 (by rfl) ⟨2083083, by rfl⟩ : syracuseStep 5554889 = 4166167) B4166167
theorem B3703259 : Blo 1949435 3703259 := bstep (se 1 (by rfl) ⟨2777444, by rfl⟩ : syracuseStep 3703259 = 5554889) B5554889
theorem B9875357 : Blo 1949435 9875357 := bstep (se 3 (by rfl) ⟨1851629, by rfl⟩ : syracuseStep 9875357 = 3703259) B3703259
theorem B6583571 : Blo 1949435 6583571 := bstep (se 1 (by rfl) ⟨4937678, by rfl⟩ : syracuseStep 6583571 = 9875357) B9875357
theorem B4389047 : Blo 1949435 4389047 := bstep (se 1 (by rfl) ⟨3291785, by rfl⟩ : syracuseStep 4389047 = 6583571) B6583571
theorem B2926031 : Blo 1949435 2926031 := bstep (se 1 (by rfl) ⟨2194523, by rfl⟩ : syracuseStep 2926031 = 4389047) B4389047
theorem B1950687 : Blo 1949435 1950687 := bstep (se 1 (by rfl) ⟨1463015, by rfl⟩ : syracuseStep 1950687 = 2926031) B2926031
theorem B2926037 : Blo 1949435 2926037 := bbase (se 7 (by rfl) ⟨34289, by rfl⟩ : syracuseStep 2926037 = 68579) (by norm_num)
theorem B1950691 : Blo 1949435 1950691 := bstep (se 1 (by rfl) ⟨1463018, by rfl⟩ : syracuseStep 1950691 = 2926037) B2926037
theorem B7406549 : Blo 1949435 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B4937699 : Blo 1949435 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B3291799 : Blo 1949435 3291799 := bstep (se 1 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 3291799 = 4937699) B4937699
theorem B4389065 : Blo 1949435 4389065 := bstep (se 2 (by rfl) ⟨1645899, by rfl⟩ : syracuseStep 4389065 = 3291799) B3291799
theorem B2926043 : Blo 1949435 2926043 := bstep (se 1 (by rfl) ⟨2194532, by rfl⟩ : syracuseStep 2926043 = 4389065) B4389065
theorem B1950695 : Blo 1949435 1950695 := bstep (se 1 (by rfl) ⟨1463021, by rfl⟩ : syracuseStep 1950695 = 2926043) B2926043
theorem B2194537 : Blo 1949435 2194537 := bbase (se 2 (by rfl) ⟨822951, by rfl⟩ : syracuseStep 2194537 = 1645903) (by norm_num)
theorem B2926049 : Blo 1949435 2926049 := bstep (se 2 (by rfl) ⟨1097268, by rfl⟩ : syracuseStep 2926049 = 2194537) B2194537
theorem B1950699 : Blo 1949435 1950699 := bstep (se 1 (by rfl) ⟨1463024, by rfl⟩ : syracuseStep 1950699 = 2926049) B2926049
theorem B7507637 : Blo 1949435 7507637 := bbase (se 5 (by rfl) ⟨351920, by rfl⟩ : syracuseStep 7507637 = 703841) (by norm_num)
theorem B5005091 : Blo 1949435 5005091 := bstep (se 1 (by rfl) ⟨3753818, by rfl⟩ : syracuseStep 5005091 = 7507637) B7507637
theorem B3336727 : Blo 1949435 3336727 := bstep (se 1 (by rfl) ⟨2502545, by rfl⟩ : syracuseStep 3336727 = 5005091) B5005091
theorem B4448969 : Blo 1949435 4448969 := bstep (se 2 (by rfl) ⟨1668363, by rfl⟩ : syracuseStep 4448969 = 3336727) B3336727
theorem B2965979 : Blo 1949435 2965979 := bstep (se 1 (by rfl) ⟨2224484, by rfl⟩ : syracuseStep 2965979 = 4448969) B4448969
theorem B1977319 : Blo 1949435 1977319 := bstep (se 1 (by rfl) ⟨1482989, by rfl⟩ : syracuseStep 1977319 = 2965979) B2965979
theorem B2636425 : Blo 1949435 2636425 := bstep (se 2 (by rfl) ⟨988659, by rfl⟩ : syracuseStep 2636425 = 1977319) B1977319
theorem B3515233 : Blo 1949435 3515233 := bstep (se 2 (by rfl) ⟨1318212, by rfl⟩ : syracuseStep 3515233 = 2636425) B2636425
theorem B4686977 : Blo 1949435 4686977 := bstep (se 2 (by rfl) ⟨1757616, by rfl⟩ : syracuseStep 4686977 = 3515233) B3515233
theorem B3124651 : Blo 1949435 3124651 := bstep (se 1 (by rfl) ⟨2343488, by rfl⟩ : syracuseStep 3124651 = 4686977) B4686977
theorem B4166201 : Blo 1949435 4166201 := bstep (se 2 (by rfl) ⟨1562325, by rfl⟩ : syracuseStep 4166201 = 3124651) B3124651
theorem B11109869 : Blo 1949435 11109869 := bstep (se 3 (by rfl) ⟨2083100, by rfl⟩ : syracuseStep 11109869 = 4166201) B4166201
theorem B7406579 : Blo 1949435 7406579 := bstep (se 1 (by rfl) ⟨5554934, by rfl⟩ : syracuseStep 7406579 = 11109869) B11109869
theorem B4937719 : Blo 1949435 4937719 := bstep (se 1 (by rfl) ⟨3703289, by rfl⟩ : syracuseStep 4937719 = 7406579) B7406579
theorem B6583625 : Blo 1949435 6583625 := bstep (se 2 (by rfl) ⟨2468859, by rfl⟩ : syracuseStep 6583625 = 4937719) B4937719
theorem B4389083 : Blo 1949435 4389083 := bstep (se 1 (by rfl) ⟨3291812, by rfl⟩ : syracuseStep 4389083 = 6583625) B6583625
theorem B2926055 : Blo 1949435 2926055 := bstep (se 1 (by rfl) ⟨2194541, by rfl⟩ : syracuseStep 2926055 = 4389083) B4389083
theorem B1950703 : Blo 1949435 1950703 := bstep (se 1 (by rfl) ⟨1463027, by rfl⟩ : syracuseStep 1950703 = 2926055) B2926055
theorem B2926061 : Blo 1949435 2926061 := bbase (se 3 (by rfl) ⟨548636, by rfl⟩ : syracuseStep 2926061 = 1097273) (by norm_num)
theorem B1950707 : Blo 1949435 1950707 := bstep (se 1 (by rfl) ⟨1463030, by rfl⟩ : syracuseStep 1950707 = 2926061) B2926061
theorem B4389101 : Blo 1949435 4389101 := bbase (se 3 (by rfl) ⟨822956, by rfl⟩ : syracuseStep 4389101 = 1645913) (by norm_num)
theorem B2926067 : Blo 1949435 2926067 := bstep (se 1 (by rfl) ⟨2194550, by rfl⟩ : syracuseStep 2926067 = 4389101) B4389101
theorem B1950711 : Blo 1949435 1950711 := bstep (se 1 (by rfl) ⟨1463033, by rfl⟩ : syracuseStep 1950711 = 2926067) B2926067
theorem B2777485 : Blo 1949435 2777485 := bbase (se 3 (by rfl) ⟨520778, by rfl⟩ : syracuseStep 2777485 = 1041557) (by norm_num)
theorem B3703313 : Blo 1949435 3703313 := bstep (se 2 (by rfl) ⟨1388742, by rfl⟩ : syracuseStep 3703313 = 2777485) B2777485
theorem B2468875 : Blo 1949435 2468875 := bstep (se 1 (by rfl) ⟨1851656, by rfl⟩ : syracuseStep 2468875 = 3703313) B3703313
theorem B3291833 : Blo 1949435 3291833 := bstep (se 2 (by rfl) ⟨1234437, by rfl⟩ : syracuseStep 3291833 = 2468875) B2468875
theorem B2194555 : Blo 1949435 2194555 := bstep (se 1 (by rfl) ⟨1645916, by rfl⟩ : syracuseStep 2194555 = 3291833) B3291833
theorem B2926073 : Blo 1949435 2926073 := bstep (se 2 (by rfl) ⟨1097277, by rfl⟩ : syracuseStep 2926073 = 2194555) B2194555
theorem B1950715 : Blo 1949435 1950715 := bstep (se 1 (by rfl) ⟨1463036, by rfl⟩ : syracuseStep 1950715 = 2926073) B2926073
theorem B8898005 : Blo 1949435 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B5932003 : Blo 1949435 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B7909337 : Blo 1949435 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B21091565 : Blo 1949435 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B14061043 : Blo 1949435 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B74992229 : Blo 1949435 74992229 := bstep (se 4 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 74992229 = 14061043) B14061043
theorem B49994819 : Blo 1949435 49994819 := bstep (se 1 (by rfl) ⟨37496114, by rfl⟩ : syracuseStep 49994819 = 74992229) B74992229
theorem B33329879 : Blo 1949435 33329879 := bstep (se 1 (by rfl) ⟨24997409, by rfl⟩ : syracuseStep 33329879 = 49994819) B49994819
theorem B22219919 : Blo 1949435 22219919 := bstep (se 1 (by rfl) ⟨16664939, by rfl⟩ : syracuseStep 22219919 = 33329879) B33329879
theorem B14813279 : Blo 1949435 14813279 := bstep (se 1 (by rfl) ⟨11109959, by rfl⟩ : syracuseStep 14813279 = 22219919) B22219919
theorem B9875519 : Blo 1949435 9875519 := bstep (se 1 (by rfl) ⟨7406639, by rfl⟩ : syracuseStep 9875519 = 14813279) B14813279
theorem B6583679 : Blo 1949435 6583679 := bstep (se 1 (by rfl) ⟨4937759, by rfl⟩ : syracuseStep 6583679 = 9875519) B9875519
theorem B4389119 : Blo 1949435 4389119 := bstep (se 1 (by rfl) ⟨3291839, by rfl⟩ : syracuseStep 4389119 = 6583679) B6583679
theorem B2926079 : Blo 1949435 2926079 := bstep (se 1 (by rfl) ⟨2194559, by rfl⟩ : syracuseStep 2926079 = 4389119) B4389119
theorem B1950719 : Blo 1949435 1950719 := bstep (se 1 (by rfl) ⟨1463039, by rfl⟩ : syracuseStep 1950719 = 2926079) B2926079
theorem B2926085 : Blo 1949435 2926085 := bbase (se 4 (by rfl) ⟨274320, by rfl⟩ : syracuseStep 2926085 = 548641) (by norm_num)
theorem B1950723 : Blo 1949435 1950723 := bstep (se 1 (by rfl) ⟨1463042, by rfl⟩ : syracuseStep 1950723 = 2926085) B2926085
theorem B3291853 : Blo 1949435 3291853 := bbase (se 3 (by rfl) ⟨617222, by rfl⟩ : syracuseStep 3291853 = 1234445) (by norm_num)
theorem B4389137 : Blo 1949435 4389137 := bstep (se 2 (by rfl) ⟨1645926, by rfl⟩ : syracuseStep 4389137 = 3291853) B3291853
theorem B2926091 : Blo 1949435 2926091 := bstep (se 1 (by rfl) ⟨2194568, by rfl⟩ : syracuseStep 2926091 = 4389137) B4389137
theorem B1950727 : Blo 1949435 1950727 := bstep (se 1 (by rfl) ⟨1463045, by rfl⟩ : syracuseStep 1950727 = 2926091) B2926091
theorem B2194573 : Blo 1949435 2194573 := bbase (se 3 (by rfl) ⟨411482, by rfl⟩ : syracuseStep 2194573 = 822965) (by norm_num)
theorem B2926097 : Blo 1949435 2926097 := bstep (se 2 (by rfl) ⟨1097286, by rfl⟩ : syracuseStep 2926097 = 2194573) B2194573
theorem B1950731 : Blo 1949435 1950731 := bstep (se 1 (by rfl) ⟨1463048, by rfl⟩ : syracuseStep 1950731 = 2926097) B2926097
theorem B6583733 : Blo 1949435 6583733 := bbase (se 5 (by rfl) ⟨308612, by rfl⟩ : syracuseStep 6583733 = 617225) (by norm_num)
theorem B4389155 : Blo 1949435 4389155 := bstep (se 1 (by rfl) ⟨3291866, by rfl⟩ : syracuseStep 4389155 = 6583733) B6583733
theorem B2926103 : Blo 1949435 2926103 := bstep (se 1 (by rfl) ⟨2194577, by rfl⟩ : syracuseStep 2926103 = 4389155) B4389155
theorem B1950735 : Blo 1949435 1950735 := bstep (se 1 (by rfl) ⟨1463051, by rfl⟩ : syracuseStep 1950735 = 2926103) B2926103
theorem B2926109 : Blo 1949435 2926109 := bbase (se 3 (by rfl) ⟨548645, by rfl⟩ : syracuseStep 2926109 = 1097291) (by norm_num)
theorem B1950739 : Blo 1949435 1950739 := bstep (se 1 (by rfl) ⟨1463054, by rfl⟩ : syracuseStep 1950739 = 2926109) B2926109
theorem B4389173 : Blo 1949435 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B2926115 : Blo 1949435 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B1950743 : Blo 1949435 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B3753901 : Blo 1949435 3753901 := bbase (se 3 (by rfl) ⟨703856, by rfl⟩ : syracuseStep 3753901 = 1407713) (by norm_num)
theorem B5005201 : Blo 1949435 5005201 := bstep (se 2 (by rfl) ⟨1876950, by rfl⟩ : syracuseStep 5005201 = 3753901) B3753901
theorem B6673601 : Blo 1949435 6673601 := bstep (se 2 (by rfl) ⟨2502600, by rfl⟩ : syracuseStep 6673601 = 5005201) B5005201
theorem B17796269 : Blo 1949435 17796269 := bstep (se 3 (by rfl) ⟨3336800, by rfl⟩ : syracuseStep 17796269 = 6673601) B6673601
theorem B11864179 : Blo 1949435 11864179 := bstep (se 1 (by rfl) ⟨8898134, by rfl⟩ : syracuseStep 11864179 = 17796269) B17796269
theorem B15818905 : Blo 1949435 15818905 := bstep (se 2 (by rfl) ⟨5932089, by rfl⟩ : syracuseStep 15818905 = 11864179) B11864179
theorem B21091873 : Blo 1949435 21091873 := bstep (se 2 (by rfl) ⟨7909452, by rfl⟩ : syracuseStep 21091873 = 15818905) B15818905
theorem B28122497 : Blo 1949435 28122497 := bstep (se 2 (by rfl) ⟨10545936, by rfl⟩ : syracuseStep 28122497 = 21091873) B21091873
theorem B18748331 : Blo 1949435 18748331 := bstep (se 1 (by rfl) ⟨14061248, by rfl⟩ : syracuseStep 18748331 = 28122497) B28122497
theorem B12498887 : Blo 1949435 12498887 := bstep (se 1 (by rfl) ⟨9374165, by rfl⟩ : syracuseStep 12498887 = 18748331) B18748331
theorem B8332591 : Blo 1949435 8332591 := bstep (se 1 (by rfl) ⟨6249443, by rfl⟩ : syracuseStep 8332591 = 12498887) B12498887
theorem B11110121 : Blo 1949435 11110121 := bstep (se 2 (by rfl) ⟨4166295, by rfl⟩ : syracuseStep 11110121 = 8332591) B8332591
theorem B7406747 : Blo 1949435 7406747 := bstep (se 1 (by rfl) ⟨5555060, by rfl⟩ : syracuseStep 7406747 = 11110121) B11110121
theorem B4937831 : Blo 1949435 4937831 := bstep (se 1 (by rfl) ⟨3703373, by rfl⟩ : syracuseStep 4937831 = 7406747) B7406747
theorem B3291887 : Blo 1949435 3291887 := bstep (se 1 (by rfl) ⟨2468915, by rfl⟩ : syracuseStep 3291887 = 4937831) B4937831
theorem B2194591 : Blo 1949435 2194591 := bstep (se 1 (by rfl) ⟨1645943, by rfl⟩ : syracuseStep 2194591 = 3291887) B3291887
theorem B2926121 : Blo 1949435 2926121 := bstep (se 2 (by rfl) ⟨1097295, by rfl⟩ : syracuseStep 2926121 = 2194591) B2194591
theorem B1950747 : Blo 1949435 1950747 := bstep (se 1 (by rfl) ⟨1463060, by rfl⟩ : syracuseStep 1950747 = 2926121) B2926121
theorem B3089117 : Blo 1949435 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B8237645 : Blo 1949435 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B5491763 : Blo 1949435 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B3661175 : Blo 1949435 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B2440783 : Blo 1949435 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B13017509 : Blo 1949435 13017509 := bstep (se 4 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 13017509 = 2440783) B2440783
theorem B8678339 : Blo 1949435 8678339 := bstep (se 1 (by rfl) ⟨6508754, by rfl⟩ : syracuseStep 8678339 = 13017509) B13017509
theorem B5785559 : Blo 1949435 5785559 := bstep (se 1 (by rfl) ⟨4339169, by rfl⟩ : syracuseStep 5785559 = 8678339) B8678339
theorem B3857039 : Blo 1949435 3857039 := bstep (se 1 (by rfl) ⟨2892779, by rfl⟩ : syracuseStep 3857039 = 5785559) B5785559
theorem B2571359 : Blo 1949435 2571359 := bstep (se 1 (by rfl) ⟨1928519, by rfl⟩ : syracuseStep 2571359 = 3857039) B3857039
theorem B6856957 : Blo 1949435 6856957 := bstep (se 3 (by rfl) ⟨1285679, by rfl⟩ : syracuseStep 6856957 = 2571359) B2571359
theorem B36570437 : Blo 1949435 36570437 := bstep (se 4 (by rfl) ⟨3428478, by rfl⟩ : syracuseStep 36570437 = 6856957) B6856957
theorem B24380291 : Blo 1949435 24380291 := bstep (se 1 (by rfl) ⟨18285218, by rfl⟩ : syracuseStep 24380291 = 36570437) B36570437
theorem B65014109 : Blo 1949435 65014109 := bstep (se 3 (by rfl) ⟨12190145, by rfl⟩ : syracuseStep 65014109 = 24380291) B24380291
theorem B43342739 : Blo 1949435 43342739 := bstep (se 1 (by rfl) ⟨32507054, by rfl⟩ : syracuseStep 43342739 = 65014109) B65014109
theorem B28895159 : Blo 1949435 28895159 := bstep (se 1 (by rfl) ⟨21671369, by rfl⟩ : syracuseStep 28895159 = 43342739) B43342739
theorem B19263439 : Blo 1949435 19263439 := bstep (se 1 (by rfl) ⟨14447579, by rfl⟩ : syracuseStep 19263439 = 28895159) B28895159
theorem B102738341 : Blo 1949435 102738341 := bstep (se 4 (by rfl) ⟨9631719, by rfl⟩ : syracuseStep 102738341 = 19263439) B19263439
theorem B68492227 : Blo 1949435 68492227 := bstep (se 1 (by rfl) ⟨51369170, by rfl⟩ : syracuseStep 68492227 = 102738341) B102738341
theorem B91322969 : Blo 1949435 91322969 := bstep (se 2 (by rfl) ⟨34246113, by rfl⟩ : syracuseStep 91322969 = 68492227) B68492227
theorem B243527917 : Blo 1949435 243527917 := bstep (se 3 (by rfl) ⟨45661484, by rfl⟩ : syracuseStep 243527917 = 91322969) B91322969
theorem B324703889 : Blo 1949435 324703889 := bstep (se 2 (by rfl) ⟨121763958, by rfl⟩ : syracuseStep 324703889 = 243527917) B243527917
theorem B216469259 : Blo 1949435 216469259 := bstep (se 1 (by rfl) ⟨162351944, by rfl⟩ : syracuseStep 216469259 = 324703889) B324703889
theorem B144312839 : Blo 1949435 144312839 := bstep (se 1 (by rfl) ⟨108234629, by rfl⟩ : syracuseStep 144312839 = 216469259) B216469259
theorem B96208559 : Blo 1949435 96208559 := bstep (se 1 (by rfl) ⟨72156419, by rfl⟩ : syracuseStep 96208559 = 144312839) B144312839
theorem B64139039 : Blo 1949435 64139039 := bstep (se 1 (by rfl) ⟨48104279, by rfl⟩ : syracuseStep 64139039 = 96208559) B96208559
theorem B42759359 : Blo 1949435 42759359 := bstep (se 1 (by rfl) ⟨32069519, by rfl⟩ : syracuseStep 42759359 = 64139039) B64139039
theorem B28506239 : Blo 1949435 28506239 := bstep (se 1 (by rfl) ⟨21379679, by rfl⟩ : syracuseStep 28506239 = 42759359) B42759359
theorem B19004159 : Blo 1949435 19004159 := bstep (se 1 (by rfl) ⟨14253119, by rfl⟩ : syracuseStep 19004159 = 28506239) B28506239
theorem B50677757 : Blo 1949435 50677757 := bstep (se 3 (by rfl) ⟨9502079, by rfl⟩ : syracuseStep 50677757 = 19004159) B19004159
theorem B33785171 : Blo 1949435 33785171 := bstep (se 1 (by rfl) ⟨25338878, by rfl⟩ : syracuseStep 33785171 = 50677757) B50677757
theorem B22523447 : Blo 1949435 22523447 := bstep (se 1 (by rfl) ⟨16892585, by rfl⟩ : syracuseStep 22523447 = 33785171) B33785171
theorem B15015631 : Blo 1949435 15015631 := bstep (se 1 (by rfl) ⟨11261723, by rfl⟩ : syracuseStep 15015631 = 22523447) B22523447
theorem B20020841 : Blo 1949435 20020841 := bstep (se 2 (by rfl) ⟨7507815, by rfl⟩ : syracuseStep 20020841 = 15015631) B15015631
theorem B13347227 : Blo 1949435 13347227 := bstep (se 1 (by rfl) ⟨10010420, by rfl⟩ : syracuseStep 13347227 = 20020841) B20020841
theorem B35592605 : Blo 1949435 35592605 := bstep (se 3 (by rfl) ⟨6673613, by rfl⟩ : syracuseStep 35592605 = 13347227) B13347227
theorem B23728403 : Blo 1949435 23728403 := bstep (se 1 (by rfl) ⟨17796302, by rfl⟩ : syracuseStep 23728403 = 35592605) B35592605
theorem B63275741 : Blo 1949435 63275741 := bstep (se 3 (by rfl) ⟨11864201, by rfl⟩ : syracuseStep 63275741 = 23728403) B23728403
theorem B42183827 : Blo 1949435 42183827 := bstep (se 1 (by rfl) ⟨31637870, by rfl⟩ : syracuseStep 42183827 = 63275741) B63275741
theorem B28122551 : Blo 1949435 28122551 := bstep (se 1 (by rfl) ⟨21091913, by rfl⟩ : syracuseStep 28122551 = 42183827) B42183827
theorem B18748367 : Blo 1949435 18748367 := bstep (se 1 (by rfl) ⟨14061275, by rfl⟩ : syracuseStep 18748367 = 28122551) B28122551
theorem B12498911 : Blo 1949435 12498911 := bstep (se 1 (by rfl) ⟨9374183, by rfl⟩ : syracuseStep 12498911 = 18748367) B18748367
theorem B8332607 : Blo 1949435 8332607 := bstep (se 1 (by rfl) ⟨6249455, by rfl⟩ : syracuseStep 8332607 = 12498911) B12498911
theorem B5555071 : Blo 1949435 5555071 := bstep (se 1 (by rfl) ⟨4166303, by rfl⟩ : syracuseStep 5555071 = 8332607) B8332607
theorem B7406761 : Blo 1949435 7406761 := bstep (se 2 (by rfl) ⟨2777535, by rfl⟩ : syracuseStep 7406761 = 5555071) B5555071
theorem B9875681 : Blo 1949435 9875681 := bstep (se 2 (by rfl) ⟨3703380, by rfl⟩ : syracuseStep 9875681 = 7406761) B7406761
theorem B6583787 : Blo 1949435 6583787 := bstep (se 1 (by rfl) ⟨4937840, by rfl⟩ : syracuseStep 6583787 = 9875681) B9875681
theorem B4389191 : Blo 1949435 4389191 := bstep (se 1 (by rfl) ⟨3291893, by rfl⟩ : syracuseStep 4389191 = 6583787) B6583787
theorem B2926127 : Blo 1949435 2926127 := bstep (se 1 (by rfl) ⟨2194595, by rfl⟩ : syracuseStep 2926127 = 4389191) B4389191
theorem B1950751 : Blo 1949435 1950751 := bstep (se 1 (by rfl) ⟨1463063, by rfl⟩ : syracuseStep 1950751 = 2926127) B2926127
theorem B2926133 : Blo 1949435 2926133 := bbase (se 5 (by rfl) ⟨137162, by rfl⟩ : syracuseStep 2926133 = 274325) (by norm_num)
theorem B1950755 : Blo 1949435 1950755 := bstep (se 1 (by rfl) ⟨1463066, by rfl⟩ : syracuseStep 1950755 = 2926133) B2926133
theorem B4937861 : Blo 1949435 4937861 := bbase (se 4 (by rfl) ⟨462924, by rfl⟩ : syracuseStep 4937861 = 925849) (by norm_num)
theorem B3291907 : Blo 1949435 3291907 := bstep (se 1 (by rfl) ⟨2468930, by rfl⟩ : syracuseStep 3291907 = 4937861) B4937861
theorem B4389209 : Blo 1949435 4389209 := bstep (se 2 (by rfl) ⟨1645953, by rfl⟩ : syracuseStep 4389209 = 3291907) B3291907
theorem B2926139 : Blo 1949435 2926139 := bstep (se 1 (by rfl) ⟨2194604, by rfl⟩ : syracuseStep 2926139 = 4389209) B4389209
theorem B1950759 : Blo 1949435 1950759 := bstep (se 1 (by rfl) ⟨1463069, by rfl⟩ : syracuseStep 1950759 = 2926139) B2926139
theorem B2194609 : Blo 1949435 2194609 := bbase (se 2 (by rfl) ⟨822978, by rfl⟩ : syracuseStep 2194609 = 1645957) (by norm_num)
theorem B2926145 : Blo 1949435 2926145 := bstep (se 2 (by rfl) ⟨1097304, by rfl⟩ : syracuseStep 2926145 = 2194609) B2194609
theorem B1950763 : Blo 1949435 1950763 := bstep (se 1 (by rfl) ⟨1463072, by rfl⟩ : syracuseStep 1950763 = 2926145) B2926145
theorem B2083169 : Blo 1949435 2083169 := bbase (se 2 (by rfl) ⟨781188, by rfl⟩ : syracuseStep 2083169 = 1562377) (by norm_num)
theorem B5555117 : Blo 1949435 5555117 := bstep (se 3 (by rfl) ⟨1041584, by rfl⟩ : syracuseStep 5555117 = 2083169) B2083169
theorem B3703411 : Blo 1949435 3703411 := bstep (se 1 (by rfl) ⟨2777558, by rfl⟩ : syracuseStep 3703411 = 5555117) B5555117
theorem B4937881 : Blo 1949435 4937881 := bstep (se 2 (by rfl) ⟨1851705, by rfl⟩ : syracuseStep 4937881 = 3703411) B3703411
theorem B6583841 : Blo 1949435 6583841 := bstep (se 2 (by rfl) ⟨2468940, by rfl⟩ : syracuseStep 6583841 = 4937881) B4937881
theorem B4389227 : Blo 1949435 4389227 := bstep (se 1 (by rfl) ⟨3291920, by rfl⟩ : syracuseStep 4389227 = 6583841) B6583841
theorem B2926151 : Blo 1949435 2926151 := bstep (se 1 (by rfl) ⟨2194613, by rfl⟩ : syracuseStep 2926151 = 4389227) B4389227
theorem B1950767 : Blo 1949435 1950767 := bstep (se 1 (by rfl) ⟨1463075, by rfl⟩ : syracuseStep 1950767 = 2926151) B2926151
theorem B2926157 : Blo 1949435 2926157 := bbase (se 3 (by rfl) ⟨548654, by rfl⟩ : syracuseStep 2926157 = 1097309) (by norm_num)
theorem B1950771 : Blo 1949435 1950771 := bstep (se 1 (by rfl) ⟨1463078, by rfl⟩ : syracuseStep 1950771 = 2926157) B2926157
theorem B4389245 : Blo 1949435 4389245 := bbase (se 3 (by rfl) ⟨822983, by rfl⟩ : syracuseStep 4389245 = 1645967) (by norm_num)
theorem B2926163 : Blo 1949435 2926163 := bstep (se 1 (by rfl) ⟨2194622, by rfl⟩ : syracuseStep 2926163 = 4389245) B4389245
theorem B1950775 : Blo 1949435 1950775 := bstep (se 1 (by rfl) ⟨1463081, by rfl⟩ : syracuseStep 1950775 = 2926163) B2926163
theorem B3291941 : Blo 1949435 3291941 := bbase (se 4 (by rfl) ⟨308619, by rfl⟩ : syracuseStep 3291941 = 617239) (by norm_num)
theorem B2194627 : Blo 1949435 2194627 := bstep (se 1 (by rfl) ⟨1645970, by rfl⟩ : syracuseStep 2194627 = 3291941) B3291941
theorem B2926169 : Blo 1949435 2926169 := bstep (se 2 (by rfl) ⟨1097313, by rfl⟩ : syracuseStep 2926169 = 2194627) B2194627
theorem B1950779 : Blo 1949435 1950779 := bstep (se 1 (by rfl) ⟨1463084, by rfl⟩ : syracuseStep 1950779 = 2926169) B2926169
theorem B2777581 : Blo 1949435 2777581 := bbase (se 3 (by rfl) ⟨520796, by rfl⟩ : syracuseStep 2777581 = 1041593) (by norm_num)
theorem B14813765 : Blo 1949435 14813765 := bstep (se 4 (by rfl) ⟨1388790, by rfl⟩ : syracuseStep 14813765 = 2777581) B2777581
theorem B9875843 : Blo 1949435 9875843 := bstep (se 1 (by rfl) ⟨7406882, by rfl⟩ : syracuseStep 9875843 = 14813765) B14813765
theorem B6583895 : Blo 1949435 6583895 := bstep (se 1 (by rfl) ⟨4937921, by rfl⟩ : syracuseStep 6583895 = 9875843) B9875843
theorem B4389263 : Blo 1949435 4389263 := bstep (se 1 (by rfl) ⟨3291947, by rfl⟩ : syracuseStep 4389263 = 6583895) B6583895
theorem B2926175 : Blo 1949435 2926175 := bstep (se 1 (by rfl) ⟨2194631, by rfl⟩ : syracuseStep 2926175 = 4389263) B4389263
theorem B1950783 : Blo 1949435 1950783 := bstep (se 1 (by rfl) ⟨1463087, by rfl⟩ : syracuseStep 1950783 = 2926175) B2926175
theorem B2926181 : Blo 1949435 2926181 := bbase (se 4 (by rfl) ⟨274329, by rfl⟩ : syracuseStep 2926181 = 548659) (by norm_num)
theorem B1950787 : Blo 1949435 1950787 := bstep (se 1 (by rfl) ⟨1463090, by rfl⟩ : syracuseStep 1950787 = 2926181) B2926181
theorem B1977409 : Blo 1949435 1977409 := bbase (se 2 (by rfl) ⟨741528, by rfl⟩ : syracuseStep 1977409 = 1483057) (by norm_num)
theorem B2636545 : Blo 1949435 2636545 := bstep (se 2 (by rfl) ⟨988704, by rfl⟩ : syracuseStep 2636545 = 1977409) B1977409
theorem B3515393 : Blo 1949435 3515393 := bstep (se 2 (by rfl) ⟨1318272, by rfl⟩ : syracuseStep 3515393 = 2636545) B2636545
theorem B2343595 : Blo 1949435 2343595 := bstep (se 1 (by rfl) ⟨1757696, by rfl⟩ : syracuseStep 2343595 = 3515393) B3515393
theorem B3124793 : Blo 1949435 3124793 := bstep (se 2 (by rfl) ⟨1171797, by rfl⟩ : syracuseStep 3124793 = 2343595) B2343595
theorem B2083195 : Blo 1949435 2083195 := bstep (se 1 (by rfl) ⟨1562396, by rfl⟩ : syracuseStep 2083195 = 3124793) B3124793
theorem B2777593 : Blo 1949435 2777593 := bstep (se 2 (by rfl) ⟨1041597, by rfl⟩ : syracuseStep 2777593 = 2083195) B2083195
theorem B3703457 : Blo 1949435 3703457 := bstep (se 2 (by rfl) ⟨1388796, by rfl⟩ : syracuseStep 3703457 = 2777593) B2777593
theorem B2468971 : Blo 1949435 2468971 := bstep (se 1 (by rfl) ⟨1851728, by rfl⟩ : syracuseStep 2468971 = 3703457) B3703457
theorem B3291961 : Blo 1949435 3291961 := bstep (se 2 (by rfl) ⟨1234485, by rfl⟩ : syracuseStep 3291961 = 2468971) B2468971
theorem B4389281 : Blo 1949435 4389281 := bstep (se 2 (by rfl) ⟨1645980, by rfl⟩ : syracuseStep 4389281 = 3291961) B3291961
theorem B2926187 : Blo 1949435 2926187 := bstep (se 1 (by rfl) ⟨2194640, by rfl⟩ : syracuseStep 2926187 = 4389281) B4389281
theorem B1950791 : Blo 1949435 1950791 := bstep (se 1 (by rfl) ⟨1463093, by rfl⟩ : syracuseStep 1950791 = 2926187) B2926187
theorem B2194645 : Blo 1949435 2194645 := bbase (se 7 (by rfl) ⟨25718, by rfl⟩ : syracuseStep 2194645 = 51437) (by norm_num)
theorem B2926193 : Blo 1949435 2926193 := bstep (se 2 (by rfl) ⟨1097322, by rfl⟩ : syracuseStep 2926193 = 2194645) B2194645
theorem B1950795 : Blo 1949435 1950795 := bstep (se 1 (by rfl) ⟨1463096, by rfl⟩ : syracuseStep 1950795 = 2926193) B2926193
theorem B2468981 : Blo 1949435 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B6583949 : Blo 1949435 6583949 := bstep (se 3 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 6583949 = 2468981) B2468981
theorem B4389299 : Blo 1949435 4389299 := bstep (se 1 (by rfl) ⟨3291974, by rfl⟩ : syracuseStep 4389299 = 6583949) B6583949
theorem B2926199 : Blo 1949435 2926199 := bstep (se 1 (by rfl) ⟨2194649, by rfl⟩ : syracuseStep 2926199 = 4389299) B4389299
theorem B1950799 : Blo 1949435 1950799 := bstep (se 1 (by rfl) ⟨1463099, by rfl⟩ : syracuseStep 1950799 = 2926199) B2926199
theorem B2926205 : Blo 1949435 2926205 := bbase (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) (by norm_num)
theorem B1950803 : Blo 1949435 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B4389317 : Blo 1949435 4389317 := bbase (se 4 (by rfl) ⟨411498, by rfl⟩ : syracuseStep 4389317 = 822997) (by norm_num)
theorem B2926211 : Blo 1949435 2926211 := bstep (se 1 (by rfl) ⟨2194658, by rfl⟩ : syracuseStep 2926211 = 4389317) B4389317
theorem B1950807 : Blo 1949435 1950807 := bstep (se 1 (by rfl) ⟨1463105, by rfl⟩ : syracuseStep 1950807 = 2926211) B2926211
theorem B4687237 : Blo 1949435 4687237 := bbase (se 4 (by rfl) ⟨439428, by rfl⟩ : syracuseStep 4687237 = 878857) (by norm_num)
theorem B6249649 : Blo 1949435 6249649 := bstep (se 2 (by rfl) ⟨2343618, by rfl⟩ : syracuseStep 6249649 = 4687237) B4687237
theorem B8332865 : Blo 1949435 8332865 := bstep (se 2 (by rfl) ⟨3124824, by rfl⟩ : syracuseStep 8332865 = 6249649) B6249649
theorem B5555243 : Blo 1949435 5555243 := bstep (se 1 (by rfl) ⟨4166432, by rfl⟩ : syracuseStep 5555243 = 8332865) B8332865
theorem B3703495 : Blo 1949435 3703495 := bstep (se 1 (by rfl) ⟨2777621, by rfl⟩ : syracuseStep 3703495 = 5555243) B5555243
theorem B4937993 : Blo 1949435 4937993 := bstep (se 2 (by rfl) ⟨1851747, by rfl⟩ : syracuseStep 4937993 = 3703495) B3703495
theorem B3291995 : Blo 1949435 3291995 := bstep (se 1 (by rfl) ⟨2468996, by rfl⟩ : syracuseStep 3291995 = 4937993) B4937993
theorem B2194663 : Blo 1949435 2194663 := bstep (se 1 (by rfl) ⟨1645997, by rfl⟩ : syracuseStep 2194663 = 3291995) B3291995
theorem B2926217 : Blo 1949435 2926217 := bstep (se 2 (by rfl) ⟨1097331, by rfl⟩ : syracuseStep 2926217 = 2194663) B2194663
theorem B1950811 : Blo 1949435 1950811 := bstep (se 1 (by rfl) ⟨1463108, by rfl⟩ : syracuseStep 1950811 = 2926217) B2926217
theorem B9876005 : Blo 1949435 9876005 := bbase (se 4 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 9876005 = 1851751) (by norm_num)
theorem B6584003 : Blo 1949435 6584003 := bstep (se 1 (by rfl) ⟨4938002, by rfl⟩ : syracuseStep 6584003 = 9876005) B9876005
theorem B4389335 : Blo 1949435 4389335 := bstep (se 1 (by rfl) ⟨3292001, by rfl⟩ : syracuseStep 4389335 = 6584003) B6584003
theorem B2926223 : Blo 1949435 2926223 := bstep (se 1 (by rfl) ⟨2194667, by rfl⟩ : syracuseStep 2926223 = 4389335) B4389335
theorem B1950815 : Blo 1949435 1950815 := bstep (se 1 (by rfl) ⟨1463111, by rfl⟩ : syracuseStep 1950815 = 2926223) B2926223
theorem B2926229 : Blo 1949435 2926229 := bbase (se 6 (by rfl) ⟨68583, by rfl⟩ : syracuseStep 2926229 = 137167) (by norm_num)
theorem B1950819 : Blo 1949435 1950819 := bstep (se 1 (by rfl) ⟨1463114, by rfl⟩ : syracuseStep 1950819 = 2926229) B2926229
theorem B2224621 : Blo 1949435 2224621 := bbase (se 3 (by rfl) ⟨417116, by rfl⟩ : syracuseStep 2224621 = 834233) (by norm_num)
theorem B2966161 : Blo 1949435 2966161 := bstep (se 2 (by rfl) ⟨1112310, by rfl⟩ : syracuseStep 2966161 = 2224621) B2224621
theorem B3954881 : Blo 1949435 3954881 := bstep (se 2 (by rfl) ⟨1483080, by rfl⟩ : syracuseStep 3954881 = 2966161) B2966161
theorem B2636587 : Blo 1949435 2636587 := bstep (se 1 (by rfl) ⟨1977440, by rfl⟩ : syracuseStep 2636587 = 3954881) B3954881
theorem B3515449 : Blo 1949435 3515449 := bstep (se 2 (by rfl) ⟨1318293, by rfl⟩ : syracuseStep 3515449 = 2636587) B2636587
theorem B4687265 : Blo 1949435 4687265 := bstep (se 2 (by rfl) ⟨1757724, by rfl⟩ : syracuseStep 4687265 = 3515449) B3515449
theorem B12499373 : Blo 1949435 12499373 := bstep (se 3 (by rfl) ⟨2343632, by rfl⟩ : syracuseStep 12499373 = 4687265) B4687265
theorem B8332915 : Blo 1949435 8332915 := bstep (se 1 (by rfl) ⟨6249686, by rfl⟩ : syracuseStep 8332915 = 12499373) B12499373
theorem B11110553 : Blo 1949435 11110553 := bstep (se 2 (by rfl) ⟨4166457, by rfl⟩ : syracuseStep 11110553 = 8332915) B8332915
theorem B7407035 : Blo 1949435 7407035 := bstep (se 1 (by rfl) ⟨5555276, by rfl⟩ : syracuseStep 7407035 = 11110553) B11110553
theorem B4938023 : Blo 1949435 4938023 := bstep (se 1 (by rfl) ⟨3703517, by rfl⟩ : syracuseStep 4938023 = 7407035) B7407035
theorem B3292015 : Blo 1949435 3292015 := bstep (se 1 (by rfl) ⟨2469011, by rfl⟩ : syracuseStep 3292015 = 4938023) B4938023
theorem B4389353 : Blo 1949435 4389353 := bstep (se 2 (by rfl) ⟨1646007, by rfl⟩ : syracuseStep 4389353 = 3292015) B3292015
theorem B2926235 : Blo 1949435 2926235 := bstep (se 1 (by rfl) ⟨2194676, by rfl⟩ : syracuseStep 2926235 = 4389353) B4389353
theorem B1950823 : Blo 1949435 1950823 := bstep (se 1 (by rfl) ⟨1463117, by rfl⟩ : syracuseStep 1950823 = 2926235) B2926235
theorem B2194681 : Blo 1949435 2194681 := bbase (se 2 (by rfl) ⟨823005, by rfl⟩ : syracuseStep 2194681 = 1646011) (by norm_num)
theorem B2926241 : Blo 1949435 2926241 := bstep (se 2 (by rfl) ⟨1097340, by rfl⟩ : syracuseStep 2926241 = 2194681) B2194681
theorem B1950827 : Blo 1949435 1950827 := bstep (se 1 (by rfl) ⟨1463120, by rfl⟩ : syracuseStep 1950827 = 2926241) B2926241
theorem B8332949 : Blo 1949435 8332949 := bbase (se 6 (by rfl) ⟨195303, by rfl⟩ : syracuseStep 8332949 = 390607) (by norm_num)
theorem B5555299 : Blo 1949435 5555299 := bstep (se 1 (by rfl) ⟨4166474, by rfl⟩ : syracuseStep 5555299 = 8332949) B8332949
theorem B7407065 : Blo 1949435 7407065 := bstep (se 2 (by rfl) ⟨2777649, by rfl⟩ : syracuseStep 7407065 = 5555299) B5555299
theorem B4938043 : Blo 1949435 4938043 := bstep (se 1 (by rfl) ⟨3703532, by rfl⟩ : syracuseStep 4938043 = 7407065) B7407065
theorem B6584057 : Blo 1949435 6584057 := bstep (se 2 (by rfl) ⟨2469021, by rfl⟩ : syracuseStep 6584057 = 4938043) B4938043
theorem B4389371 : Blo 1949435 4389371 := bstep (se 1 (by rfl) ⟨3292028, by rfl⟩ : syracuseStep 4389371 = 6584057) B6584057
theorem B2926247 : Blo 1949435 2926247 := bstep (se 1 (by rfl) ⟨2194685, by rfl⟩ : syracuseStep 2926247 = 4389371) B4389371
theorem B1950831 : Blo 1949435 1950831 := bstep (se 1 (by rfl) ⟨1463123, by rfl⟩ : syracuseStep 1950831 = 2926247) B2926247
theorem B2926253 : Blo 1949435 2926253 := bbase (se 3 (by rfl) ⟨548672, by rfl⟩ : syracuseStep 2926253 = 1097345) (by norm_num)
theorem B1950835 : Blo 1949435 1950835 := bstep (se 1 (by rfl) ⟨1463126, by rfl⟩ : syracuseStep 1950835 = 2926253) B2926253
theorem B4389389 : Blo 1949435 4389389 := bbase (se 3 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 4389389 = 1646021) (by norm_num)
theorem B2926259 : Blo 1949435 2926259 := bstep (se 1 (by rfl) ⟨2194694, by rfl⟩ : syracuseStep 2926259 = 4389389) B4389389
theorem B1950839 : Blo 1949435 1950839 := bstep (se 1 (by rfl) ⟨1463129, by rfl⟩ : syracuseStep 1950839 = 2926259) B2926259
theorem B2469037 : Blo 1949435 2469037 := bbase (se 3 (by rfl) ⟨462944, by rfl⟩ : syracuseStep 2469037 = 925889) (by norm_num)
theorem B3292049 : Blo 1949435 3292049 := bstep (se 2 (by rfl) ⟨1234518, by rfl⟩ : syracuseStep 3292049 = 2469037) B2469037
theorem B2194699 : Blo 1949435 2194699 := bstep (se 1 (by rfl) ⟨1646024, by rfl⟩ : syracuseStep 2194699 = 3292049) B3292049
theorem B2926265 : Blo 1949435 2926265 := bstep (se 2 (by rfl) ⟨1097349, by rfl⟩ : syracuseStep 2926265 = 2194699) B2194699
theorem B1950843 : Blo 1949435 1950843 := bstep (se 1 (by rfl) ⟨1463132, by rfl⟩ : syracuseStep 1950843 = 2926265) B2926265
theorem B2343661 : Blo 1949435 2343661 := bbase (se 3 (by rfl) ⟨439436, by rfl⟩ : syracuseStep 2343661 = 878873) (by norm_num)
theorem B12499525 : Blo 1949435 12499525 := bstep (se 4 (by rfl) ⟨1171830, by rfl⟩ : syracuseStep 12499525 = 2343661) B2343661
theorem B16666033 : Blo 1949435 16666033 := bstep (se 2 (by rfl) ⟨6249762, by rfl⟩ : syracuseStep 16666033 = 12499525) B12499525
theorem B22221377 : Blo 1949435 22221377 := bstep (se 2 (by rfl) ⟨8333016, by rfl⟩ : syracuseStep 22221377 = 16666033) B16666033
theorem B14814251 : Blo 1949435 14814251 := bstep (se 1 (by rfl) ⟨11110688, by rfl⟩ : syracuseStep 14814251 = 22221377) B22221377
theorem B9876167 : Blo 1949435 9876167 := bstep (se 1 (by rfl) ⟨7407125, by rfl⟩ : syracuseStep 9876167 = 14814251) B14814251
theorem B6584111 : Blo 1949435 6584111 := bstep (se 1 (by rfl) ⟨4938083, by rfl⟩ : syracuseStep 6584111 = 9876167) B9876167
theorem B4389407 : Blo 1949435 4389407 := bstep (se 1 (by rfl) ⟨3292055, by rfl⟩ : syracuseStep 4389407 = 6584111) B6584111
theorem B2926271 : Blo 1949435 2926271 := bstep (se 1 (by rfl) ⟨2194703, by rfl⟩ : syracuseStep 2926271 = 4389407) B4389407
theorem B1950847 : Blo 1949435 1950847 := bstep (se 1 (by rfl) ⟨1463135, by rfl⟩ : syracuseStep 1950847 = 2926271) B2926271
theorem B2926277 : Blo 1949435 2926277 := bbase (se 4 (by rfl) ⟨274338, by rfl⟩ : syracuseStep 2926277 = 548677) (by norm_num)
theorem B1950851 : Blo 1949435 1950851 := bstep (se 1 (by rfl) ⟨1463138, by rfl⟩ : syracuseStep 1950851 = 2926277) B2926277
theorem B3292069 : Blo 1949435 3292069 := bbase (se 4 (by rfl) ⟨308631, by rfl⟩ : syracuseStep 3292069 = 617263) (by norm_num)
theorem B4389425 : Blo 1949435 4389425 := bstep (se 2 (by rfl) ⟨1646034, by rfl⟩ : syracuseStep 4389425 = 3292069) B3292069
theorem B2926283 : Blo 1949435 2926283 := bstep (se 1 (by rfl) ⟨2194712, by rfl⟩ : syracuseStep 2926283 = 4389425) B4389425
theorem B1950855 : Blo 1949435 1950855 := bstep (se 1 (by rfl) ⟨1463141, by rfl⟩ : syracuseStep 1950855 = 2926283) B2926283
theorem B2194717 : Blo 1949435 2194717 := bbase (se 3 (by rfl) ⟨411509, by rfl⟩ : syracuseStep 2194717 = 823019) (by norm_num)
theorem B2926289 : Blo 1949435 2926289 := bstep (se 2 (by rfl) ⟨1097358, by rfl⟩ : syracuseStep 2926289 = 2194717) B2194717
theorem B1950859 : Blo 1949435 1950859 := bstep (se 1 (by rfl) ⟨1463144, by rfl⟩ : syracuseStep 1950859 = 2926289) B2926289
theorem B6584165 : Blo 1949435 6584165 := bbase (se 4 (by rfl) ⟨617265, by rfl⟩ : syracuseStep 6584165 = 1234531) (by norm_num)
theorem B4389443 : Blo 1949435 4389443 := bstep (se 1 (by rfl) ⟨3292082, by rfl⟩ : syracuseStep 4389443 = 6584165) B6584165
theorem B2926295 : Blo 1949435 2926295 := bstep (se 1 (by rfl) ⟨2194721, by rfl⟩ : syracuseStep 2926295 = 4389443) B4389443
theorem B1950863 : Blo 1949435 1950863 := bstep (se 1 (by rfl) ⟨1463147, by rfl⟩ : syracuseStep 1950863 = 2926295) B2926295
theorem B2926301 : Blo 1949435 2926301 := bbase (se 3 (by rfl) ⟨548681, by rfl⟩ : syracuseStep 2926301 = 1097363) (by norm_num)
theorem B1950867 : Blo 1949435 1950867 := bstep (se 1 (by rfl) ⟨1463150, by rfl⟩ : syracuseStep 1950867 = 2926301) B2926301
theorem B4389461 : Blo 1949435 4389461 := bbase (se 8 (by rfl) ⟨25719, by rfl⟩ : syracuseStep 4389461 = 51439) (by norm_num)
theorem B2926307 : Blo 1949435 2926307 := bstep (se 1 (by rfl) ⟨2194730, by rfl⟩ : syracuseStep 2926307 = 4389461) B4389461
theorem B1950871 : Blo 1949435 1950871 := bstep (se 1 (by rfl) ⟨1463153, by rfl⟩ : syracuseStep 1950871 = 2926307) B2926307
theorem B10011061 : Blo 1949435 10011061 := bbase (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) (by norm_num)
theorem B13348081 : Blo 1949435 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B17797441 : Blo 1949435 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B23729921 : Blo 1949435 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B15819947 : Blo 1949435 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B10546631 : Blo 1949435 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B7031087 : Blo 1949435 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B4687391 : Blo 1949435 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B3124927 : Blo 1949435 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B4166569 : Blo 1949435 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B5555425 : Blo 1949435 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B7407233 : Blo 1949435 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B4938155 : Blo 1949435 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B3292103 : Blo 1949435 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B2194735 : Blo 1949435 2194735 := bstep (se 1 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 2194735 = 3292103) B3292103
theorem B2926313 : Blo 1949435 2926313 := bstep (se 2 (by rfl) ⟨1097367, by rfl⟩ : syracuseStep 2926313 = 2194735) B2194735
theorem B1950875 : Blo 1949435 1950875 := bstep (se 1 (by rfl) ⟨1463156, by rfl⟩ : syracuseStep 1950875 = 2926313) B2926313
theorem B11864981 : Blo 1949435 11864981 := bbase (se 6 (by rfl) ⟨278085, by rfl⟩ : syracuseStep 11864981 = 556171) (by norm_num)
theorem B7909987 : Blo 1949435 7909987 := bstep (se 1 (by rfl) ⟨5932490, by rfl⟩ : syracuseStep 7909987 = 11864981) B11864981
theorem B10546649 : Blo 1949435 10546649 := bstep (se 2 (by rfl) ⟨3954993, by rfl⟩ : syracuseStep 10546649 = 7909987) B7909987
theorem B7031099 : Blo 1949435 7031099 := bstep (se 1 (by rfl) ⟨5273324, by rfl⟩ : syracuseStep 7031099 = 10546649) B10546649
theorem B4687399 : Blo 1949435 4687399 := bstep (se 1 (by rfl) ⟨3515549, by rfl⟩ : syracuseStep 4687399 = 7031099) B7031099
theorem B24999461 : Blo 1949435 24999461 := bstep (se 4 (by rfl) ⟨2343699, by rfl⟩ : syracuseStep 24999461 = 4687399) B4687399
theorem B16666307 : Blo 1949435 16666307 := bstep (se 1 (by rfl) ⟨12499730, by rfl⟩ : syracuseStep 16666307 = 24999461) B24999461
theorem B11110871 : Blo 1949435 11110871 := bstep (se 1 (by rfl) ⟨8333153, by rfl⟩ : syracuseStep 11110871 = 16666307) B16666307
theorem B7407247 : Blo 1949435 7407247 := bstep (se 1 (by rfl) ⟨5555435, by rfl⟩ : syracuseStep 7407247 = 11110871) B11110871
theorem B9876329 : Blo 1949435 9876329 := bstep (se 2 (by rfl) ⟨3703623, by rfl⟩ : syracuseStep 9876329 = 7407247) B7407247
theorem B6584219 : Blo 1949435 6584219 := bstep (se 1 (by rfl) ⟨4938164, by rfl⟩ : syracuseStep 6584219 = 9876329) B9876329
theorem B4389479 : Blo 1949435 4389479 := bstep (se 1 (by rfl) ⟨3292109, by rfl⟩ : syracuseStep 4389479 = 6584219) B6584219
theorem B2926319 : Blo 1949435 2926319 := bstep (se 1 (by rfl) ⟨2194739, by rfl⟩ : syracuseStep 2926319 = 4389479) B4389479
theorem B1950879 : Blo 1949435 1950879 := bstep (se 1 (by rfl) ⟨1463159, by rfl⟩ : syracuseStep 1950879 = 2926319) B2926319
theorem B2926325 : Blo 1949435 2926325 := bbase (se 5 (by rfl) ⟨137171, by rfl⟩ : syracuseStep 2926325 = 274343) (by norm_num)
theorem B1950883 : Blo 1949435 1950883 := bstep (se 1 (by rfl) ⟨1463162, by rfl⟩ : syracuseStep 1950883 = 2926325) B2926325
theorem B8333189 : Blo 1949435 8333189 := bbase (se 4 (by rfl) ⟨781236, by rfl⟩ : syracuseStep 8333189 = 1562473) (by norm_num)
theorem B5555459 : Blo 1949435 5555459 := bstep (se 1 (by rfl) ⟨4166594, by rfl⟩ : syracuseStep 5555459 = 8333189) B8333189
theorem B3703639 : Blo 1949435 3703639 := bstep (se 1 (by rfl) ⟨2777729, by rfl⟩ : syracuseStep 3703639 = 5555459) B5555459
theorem B4938185 : Blo 1949435 4938185 := bstep (se 2 (by rfl) ⟨1851819, by rfl⟩ : syracuseStep 4938185 = 3703639) B3703639
theorem B3292123 : Blo 1949435 3292123 := bstep (se 1 (by rfl) ⟨2469092, by rfl⟩ : syracuseStep 3292123 = 4938185) B4938185
theorem B4389497 : Blo 1949435 4389497 := bstep (se 2 (by rfl) ⟨1646061, by rfl⟩ : syracuseStep 4389497 = 3292123) B3292123
theorem B2926331 : Blo 1949435 2926331 := bstep (se 1 (by rfl) ⟨2194748, by rfl⟩ : syracuseStep 2926331 = 4389497) B4389497
theorem B1950887 : Blo 1949435 1950887 := bstep (se 1 (by rfl) ⟨1463165, by rfl⟩ : syracuseStep 1950887 = 2926331) B2926331
theorem B2194753 : Blo 1949435 2194753 := bbase (se 2 (by rfl) ⟨823032, by rfl⟩ : syracuseStep 2194753 = 1646065) (by norm_num)
theorem B2926337 : Blo 1949435 2926337 := bstep (se 2 (by rfl) ⟨1097376, by rfl⟩ : syracuseStep 2926337 = 2194753) B2194753
theorem B1950891 : Blo 1949435 1950891 := bstep (se 1 (by rfl) ⟨1463168, by rfl⟩ : syracuseStep 1950891 = 2926337) B2926337
theorem B4938205 : Blo 1949435 4938205 := bbase (se 3 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 4938205 = 1851827) (by norm_num)
theorem B6584273 : Blo 1949435 6584273 := bstep (se 2 (by rfl) ⟨2469102, by rfl⟩ : syracuseStep 6584273 = 4938205) B4938205
theorem B4389515 : Blo 1949435 4389515 := bstep (se 1 (by rfl) ⟨3292136, by rfl⟩ : syracuseStep 4389515 = 6584273) B6584273
theorem B2926343 : Blo 1949435 2926343 := bstep (se 1 (by rfl) ⟨2194757, by rfl⟩ : syracuseStep 2926343 = 4389515) B4389515
theorem B1950895 : Blo 1949435 1950895 := bstep (se 1 (by rfl) ⟨1463171, by rfl⟩ : syracuseStep 1950895 = 2926343) B2926343
theorem B2926349 : Blo 1949435 2926349 := bbase (se 3 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 2926349 = 1097381) (by norm_num)
theorem B1950899 : Blo 1949435 1950899 := bstep (se 1 (by rfl) ⟨1463174, by rfl⟩ : syracuseStep 1950899 = 2926349) B2926349
theorem B4389533 : Blo 1949435 4389533 := bbase (se 3 (by rfl) ⟨823037, by rfl⟩ : syracuseStep 4389533 = 1646075) (by norm_num)
theorem B2926355 : Blo 1949435 2926355 := bstep (se 1 (by rfl) ⟨2194766, by rfl⟩ : syracuseStep 2926355 = 4389533) B4389533
theorem B1950903 : Blo 1949435 1950903 := bstep (se 1 (by rfl) ⟨1463177, by rfl⟩ : syracuseStep 1950903 = 2926355) B2926355
theorem B3292157 : Blo 1949435 3292157 := bbase (se 3 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 3292157 = 1234559) (by norm_num)
theorem B2194771 : Blo 1949435 2194771 := bstep (se 1 (by rfl) ⟨1646078, by rfl⟩ : syracuseStep 2194771 = 3292157) B3292157
theorem B2926361 : Blo 1949435 2926361 := bstep (se 2 (by rfl) ⟨1097385, by rfl⟩ : syracuseStep 2926361 = 2194771) B2194771
theorem B1950907 : Blo 1949435 1950907 := bstep (se 1 (by rfl) ⟨1463180, by rfl⟩ : syracuseStep 1950907 = 2926361) B2926361
theorem B4166645 : Blo 1949435 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B11111053 : Blo 1949435 11111053 := bstep (se 3 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 11111053 = 4166645) B4166645
theorem B14814737 : Blo 1949435 14814737 := bstep (se 2 (by rfl) ⟨5555526, by rfl⟩ : syracuseStep 14814737 = 11111053) B11111053
theorem B9876491 : Blo 1949435 9876491 := bstep (se 1 (by rfl) ⟨7407368, by rfl⟩ : syracuseStep 9876491 = 14814737) B14814737
theorem B6584327 : Blo 1949435 6584327 := bstep (se 1 (by rfl) ⟨4938245, by rfl⟩ : syracuseStep 6584327 = 9876491) B9876491
theorem B4389551 : Blo 1949435 4389551 := bstep (se 1 (by rfl) ⟨3292163, by rfl⟩ : syracuseStep 4389551 = 6584327) B6584327
theorem B2926367 : Blo 1949435 2926367 := bstep (se 1 (by rfl) ⟨2194775, by rfl⟩ : syracuseStep 2926367 = 4389551) B4389551
theorem B1950911 : Blo 1949435 1950911 := bstep (se 1 (by rfl) ⟨1463183, by rfl⟩ : syracuseStep 1950911 = 2926367) B2926367
theorem B2926373 : Blo 1949435 2926373 := bbase (se 4 (by rfl) ⟨274347, by rfl⟩ : syracuseStep 2926373 = 548695) (by norm_num)
theorem B1950915 : Blo 1949435 1950915 := bstep (se 1 (by rfl) ⟨1463186, by rfl⟩ : syracuseStep 1950915 = 2926373) B2926373
theorem B2469133 : Blo 1949435 2469133 := bbase (se 3 (by rfl) ⟨462962, by rfl⟩ : syracuseStep 2469133 = 925925) (by norm_num)
theorem B3292177 : Blo 1949435 3292177 := bstep (se 2 (by rfl) ⟨1234566, by rfl⟩ : syracuseStep 3292177 = 2469133) B2469133
theorem B4389569 : Blo 1949435 4389569 := bstep (se 2 (by rfl) ⟨1646088, by rfl⟩ : syracuseStep 4389569 = 3292177) B3292177
theorem B2926379 : Blo 1949435 2926379 := bstep (se 1 (by rfl) ⟨2194784, by rfl⟩ : syracuseStep 2926379 = 4389569) B4389569
theorem B1950919 : Blo 1949435 1950919 := bstep (se 1 (by rfl) ⟨1463189, by rfl⟩ : syracuseStep 1950919 = 2926379) B2926379
theorem B2194789 : Blo 1949435 2194789 := bbase (se 4 (by rfl) ⟨205761, by rfl⟩ : syracuseStep 2194789 = 411523) (by norm_num)
theorem B2926385 : Blo 1949435 2926385 := bstep (se 2 (by rfl) ⟨1097394, by rfl⟩ : syracuseStep 2926385 = 2194789) B2194789
theorem B1950923 : Blo 1949435 1950923 := bstep (se 1 (by rfl) ⟨1463192, by rfl⟩ : syracuseStep 1950923 = 2926385) B2926385
theorem B5555573 : Blo 1949435 5555573 := bbase (se 5 (by rfl) ⟨260417, by rfl⟩ : syracuseStep 5555573 = 520835) (by norm_num)
theorem B3703715 : Blo 1949435 3703715 := bstep (se 1 (by rfl) ⟨2777786, by rfl⟩ : syracuseStep 3703715 = 5555573) B5555573
theorem B2469143 : Blo 1949435 2469143 := bstep (se 1 (by rfl) ⟨1851857, by rfl⟩ : syracuseStep 2469143 = 3703715) B3703715
theorem B6584381 : Blo 1949435 6584381 := bstep (se 3 (by rfl) ⟨1234571, by rfl⟩ : syracuseStep 6584381 = 2469143) B2469143
theorem B4389587 : Blo 1949435 4389587 := bstep (se 1 (by rfl) ⟨3292190, by rfl⟩ : syracuseStep 4389587 = 6584381) B6584381
theorem B2926391 : Blo 1949435 2926391 := bstep (se 1 (by rfl) ⟨2194793, by rfl⟩ : syracuseStep 2926391 = 4389587) B4389587
theorem B1950927 : Blo 1949435 1950927 := bstep (se 1 (by rfl) ⟨1463195, by rfl⟩ : syracuseStep 1950927 = 2926391) B2926391
theorem B2926397 : Blo 1949435 2926397 := bbase (se 3 (by rfl) ⟨548699, by rfl⟩ : syracuseStep 2926397 = 1097399) (by norm_num)
theorem B1950931 : Blo 1949435 1950931 := bstep (se 1 (by rfl) ⟨1463198, by rfl⟩ : syracuseStep 1950931 = 2926397) B2926397
theorem B4389605 : Blo 1949435 4389605 := bbase (se 4 (by rfl) ⟨411525, by rfl⟩ : syracuseStep 4389605 = 823051) (by norm_num)
theorem B2926403 : Blo 1949435 2926403 := bstep (se 1 (by rfl) ⟨2194802, by rfl⟩ : syracuseStep 2926403 = 4389605) B4389605
theorem B1950935 : Blo 1949435 1950935 := bstep (se 1 (by rfl) ⟨1463201, by rfl⟩ : syracuseStep 1950935 = 2926403) B2926403
theorem B4938317 : Blo 1949435 4938317 := bbase (se 3 (by rfl) ⟨925934, by rfl⟩ : syracuseStep 4938317 = 1851869) (by norm_num)
theorem B3292211 : Blo 1949435 3292211 := bstep (se 1 (by rfl) ⟨2469158, by rfl⟩ : syracuseStep 3292211 = 4938317) B4938317
theorem B2194807 : Blo 1949435 2194807 := bstep (se 1 (by rfl) ⟨1646105, by rfl⟩ : syracuseStep 2194807 = 3292211) B3292211
theorem B2926409 : Blo 1949435 2926409 := bstep (se 2 (by rfl) ⟨1097403, by rfl⟩ : syracuseStep 2926409 = 2194807) B2194807
theorem B1950939 : Blo 1949435 1950939 := bstep (se 1 (by rfl) ⟨1463204, by rfl⟩ : syracuseStep 1950939 = 2926409) B2926409
theorem B2083357 : Blo 1949435 2083357 := bbase (se 3 (by rfl) ⟨390629, by rfl⟩ : syracuseStep 2083357 = 781259) (by norm_num)
theorem B2777809 : Blo 1949435 2777809 := bstep (se 2 (by rfl) ⟨1041678, by rfl⟩ : syracuseStep 2777809 = 2083357) B2083357
theorem B3703745 : Blo 1949435 3703745 := bstep (se 2 (by rfl) ⟨1388904, by rfl⟩ : syracuseStep 3703745 = 2777809) B2777809
theorem B9876653 : Blo 1949435 9876653 := bstep (se 3 (by rfl) ⟨1851872, by rfl⟩ : syracuseStep 9876653 = 3703745) B3703745
theorem B6584435 : Blo 1949435 6584435 := bstep (se 1 (by rfl) ⟨4938326, by rfl⟩ : syracuseStep 6584435 = 9876653) B9876653
theorem B4389623 : Blo 1949435 4389623 := bstep (se 1 (by rfl) ⟨3292217, by rfl⟩ : syracuseStep 4389623 = 6584435) B6584435
theorem B2926415 : Blo 1949435 2926415 := bstep (se 1 (by rfl) ⟨2194811, by rfl⟩ : syracuseStep 2926415 = 4389623) B4389623
theorem B1950943 : Blo 1949435 1950943 := bstep (se 1 (by rfl) ⟨1463207, by rfl⟩ : syracuseStep 1950943 = 2926415) B2926415
theorem B2926421 : Blo 1949435 2926421 := bbase (se 9 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 2926421 = 17147) (by norm_num)
theorem B1950947 : Blo 1949435 1950947 := bstep (se 1 (by rfl) ⟨1463210, by rfl⟩ : syracuseStep 1950947 = 2926421) B2926421
theorem B4687573 : Blo 1949435 4687573 := bbase (se 7 (by rfl) ⟨54932, by rfl⟩ : syracuseStep 4687573 = 109865) (by norm_num)
theorem B6250097 : Blo 1949435 6250097 := bstep (se 2 (by rfl) ⟨2343786, by rfl⟩ : syracuseStep 6250097 = 4687573) B4687573
theorem B4166731 : Blo 1949435 4166731 := bstep (se 1 (by rfl) ⟨3125048, by rfl⟩ : syracuseStep 4166731 = 6250097) B6250097
theorem B5555641 : Blo 1949435 5555641 := bstep (se 2 (by rfl) ⟨2083365, by rfl⟩ : syracuseStep 5555641 = 4166731) B4166731
theorem B7407521 : Blo 1949435 7407521 := bstep (se 2 (by rfl) ⟨2777820, by rfl⟩ : syracuseStep 7407521 = 5555641) B5555641
theorem B4938347 : Blo 1949435 4938347 := bstep (se 1 (by rfl) ⟨3703760, by rfl⟩ : syracuseStep 4938347 = 7407521) B7407521
theorem B3292231 : Blo 1949435 3292231 := bstep (se 1 (by rfl) ⟨2469173, by rfl⟩ : syracuseStep 3292231 = 4938347) B4938347
theorem B4389641 : Blo 1949435 4389641 := bstep (se 2 (by rfl) ⟨1646115, by rfl⟩ : syracuseStep 4389641 = 3292231) B3292231
theorem B2926427 : Blo 1949435 2926427 := bstep (se 1 (by rfl) ⟨2194820, by rfl⟩ : syracuseStep 2926427 = 4389641) B4389641
theorem B1950951 : Blo 1949435 1950951 := bstep (se 1 (by rfl) ⟨1463213, by rfl⟩ : syracuseStep 1950951 = 2926427) B2926427
theorem B2194825 : Blo 1949435 2194825 := bbase (se 2 (by rfl) ⟨823059, by rfl⟩ : syracuseStep 2194825 = 1646119) (by norm_num)
theorem B2926433 : Blo 1949435 2926433 := bstep (se 2 (by rfl) ⟨1097412, by rfl⟩ : syracuseStep 2926433 = 2194825) B2194825
theorem B1950955 : Blo 1949435 1950955 := bstep (se 1 (by rfl) ⟨1463216, by rfl⟩ : syracuseStep 1950955 = 2926433) B2926433
theorem B3754309 : Blo 1949435 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B5005745 : Blo 1949435 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B3337163 : Blo 1949435 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B2224775 : Blo 1949435 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B5932733 : Blo 1949435 5932733 := bstep (se 3 (by rfl) ⟨1112387, by rfl⟩ : syracuseStep 5932733 = 2224775) B2224775
theorem B63282485 : Blo 1949435 63282485 := bstep (se 5 (by rfl) ⟨2966366, by rfl⟩ : syracuseStep 63282485 = 5932733) B5932733
theorem B42188323 : Blo 1949435 42188323 := bstep (se 1 (by rfl) ⟨31641242, by rfl⟩ : syracuseStep 42188323 = 63282485) B63282485
theorem B56251097 : Blo 1949435 56251097 := bstep (se 2 (by rfl) ⟨21094161, by rfl⟩ : syracuseStep 56251097 = 42188323) B42188323
theorem B37500731 : Blo 1949435 37500731 := bstep (se 1 (by rfl) ⟨28125548, by rfl⟩ : syracuseStep 37500731 = 56251097) B56251097
theorem B25000487 : Blo 1949435 25000487 := bstep (se 1 (by rfl) ⟨18750365, by rfl⟩ : syracuseStep 25000487 = 37500731) B37500731
theorem B16666991 : Blo 1949435 16666991 := bstep (se 1 (by rfl) ⟨12500243, by rfl⟩ : syracuseStep 16666991 = 25000487) B25000487
theorem B11111327 : Blo 1949435 11111327 := bstep (se 1 (by rfl) ⟨8333495, by rfl⟩ : syracuseStep 11111327 = 16666991) B16666991
theorem B7407551 : Blo 1949435 7407551 := bstep (se 1 (by rfl) ⟨5555663, by rfl⟩ : syracuseStep 7407551 = 11111327) B11111327
theorem B4938367 : Blo 1949435 4938367 := bstep (se 1 (by rfl) ⟨3703775, by rfl⟩ : syracuseStep 4938367 = 7407551) B7407551
theorem B6584489 : Blo 1949435 6584489 := bstep (se 2 (by rfl) ⟨2469183, by rfl⟩ : syracuseStep 6584489 = 4938367) B4938367
theorem B4389659 : Blo 1949435 4389659 := bstep (se 1 (by rfl) ⟨3292244, by rfl⟩ : syracuseStep 4389659 = 6584489) B6584489
theorem B2926439 : Blo 1949435 2926439 := bstep (se 1 (by rfl) ⟨2194829, by rfl⟩ : syracuseStep 2926439 = 4389659) B4389659
theorem B1950959 : Blo 1949435 1950959 := bstep (se 1 (by rfl) ⟨1463219, by rfl⟩ : syracuseStep 1950959 = 2926439) B2926439
theorem B2926445 : Blo 1949435 2926445 := bbase (se 3 (by rfl) ⟨548708, by rfl⟩ : syracuseStep 2926445 = 1097417) (by norm_num)
theorem B1950963 : Blo 1949435 1950963 := bstep (se 1 (by rfl) ⟨1463222, by rfl⟩ : syracuseStep 1950963 = 2926445) B2926445
theorem B4389677 : Blo 1949435 4389677 := bbase (se 3 (by rfl) ⟨823064, by rfl⟩ : syracuseStep 4389677 = 1646129) (by norm_num)
theorem B2926451 : Blo 1949435 2926451 := bstep (se 1 (by rfl) ⟨2194838, by rfl⟩ : syracuseStep 2926451 = 4389677) B4389677
theorem B1950967 : Blo 1949435 1950967 := bstep (se 1 (by rfl) ⟨1463225, by rfl⟩ : syracuseStep 1950967 = 2926451) B2926451
theorem B3515717 : Blo 1949435 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B2343811 : Blo 1949435 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B3125081 : Blo 1949435 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B8333549 : Blo 1949435 8333549 := bstep (se 3 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 8333549 = 3125081) B3125081
theorem B5555699 : Blo 1949435 5555699 := bstep (se 1 (by rfl) ⟨4166774, by rfl⟩ : syracuseStep 5555699 = 8333549) B8333549
theorem B3703799 : Blo 1949435 3703799 := bstep (se 1 (by rfl) ⟨2777849, by rfl⟩ : syracuseStep 3703799 = 5555699) B5555699
theorem B2469199 : Blo 1949435 2469199 := bstep (se 1 (by rfl) ⟨1851899, by rfl⟩ : syracuseStep 2469199 = 3703799) B3703799
theorem B3292265 : Blo 1949435 3292265 := bstep (se 2 (by rfl) ⟨1234599, by rfl⟩ : syracuseStep 3292265 = 2469199) B2469199
theorem B2194843 : Blo 1949435 2194843 := bstep (se 1 (by rfl) ⟨1646132, by rfl⟩ : syracuseStep 2194843 = 3292265) B3292265
theorem B2926457 : Blo 1949435 2926457 := bstep (se 2 (by rfl) ⟨1097421, by rfl⟩ : syracuseStep 2926457 = 2194843) B2194843
theorem B1950971 : Blo 1949435 1950971 := bstep (se 1 (by rfl) ⟨1463228, by rfl⟩ : syracuseStep 1950971 = 2926457) B2926457
theorem B30034709 : Blo 1949435 30034709 := bbase (se 6 (by rfl) ⟨703938, by rfl⟩ : syracuseStep 30034709 = 1407877) (by norm_num)
theorem B20023139 : Blo 1949435 20023139 := bstep (se 1 (by rfl) ⟨15017354, by rfl⟩ : syracuseStep 20023139 = 30034709) B30034709
theorem B53395037 : Blo 1949435 53395037 := bstep (se 3 (by rfl) ⟨10011569, by rfl⟩ : syracuseStep 53395037 = 20023139) B20023139
theorem B35596691 : Blo 1949435 35596691 := bstep (se 1 (by rfl) ⟨26697518, by rfl⟩ : syracuseStep 35596691 = 53395037) B53395037
theorem B23731127 : Blo 1949435 23731127 := bstep (se 1 (by rfl) ⟨17798345, by rfl⟩ : syracuseStep 23731127 = 35596691) B35596691
theorem B15820751 : Blo 1949435 15820751 := bstep (se 1 (by rfl) ⟨11865563, by rfl⟩ : syracuseStep 15820751 = 23731127) B23731127
theorem B10547167 : Blo 1949435 10547167 := bstep (se 1 (by rfl) ⟨7910375, by rfl⟩ : syracuseStep 10547167 = 15820751) B15820751
theorem B14062889 : Blo 1949435 14062889 := bstep (se 2 (by rfl) ⟨5273583, by rfl⟩ : syracuseStep 14062889 = 10547167) B10547167
theorem B9375259 : Blo 1949435 9375259 := bstep (se 1 (by rfl) ⟨7031444, by rfl⟩ : syracuseStep 9375259 = 14062889) B14062889
theorem B12500345 : Blo 1949435 12500345 := bstep (se 2 (by rfl) ⟨4687629, by rfl⟩ : syracuseStep 12500345 = 9375259) B9375259
theorem B33334253 : Blo 1949435 33334253 := bstep (se 3 (by rfl) ⟨6250172, by rfl⟩ : syracuseStep 33334253 = 12500345) B12500345
theorem B22222835 : Blo 1949435 22222835 := bstep (se 1 (by rfl) ⟨16667126, by rfl⟩ : syracuseStep 22222835 = 33334253) B33334253
theorem B14815223 : Blo 1949435 14815223 := bstep (se 1 (by rfl) ⟨11111417, by rfl⟩ : syracuseStep 14815223 = 22222835) B22222835
theorem B9876815 : Blo 1949435 9876815 := bstep (se 1 (by rfl) ⟨7407611, by rfl⟩ : syracuseStep 9876815 = 14815223) B14815223
theorem B6584543 : Blo 1949435 6584543 := bstep (se 1 (by rfl) ⟨4938407, by rfl⟩ : syracuseStep 6584543 = 9876815) B9876815
theorem B4389695 : Blo 1949435 4389695 := bstep (se 1 (by rfl) ⟨3292271, by rfl⟩ : syracuseStep 4389695 = 6584543) B6584543
theorem B2926463 : Blo 1949435 2926463 := bstep (se 1 (by rfl) ⟨2194847, by rfl⟩ : syracuseStep 2926463 = 4389695) B4389695
theorem B1950975 : Blo 1949435 1950975 := bstep (se 1 (by rfl) ⟨1463231, by rfl⟩ : syracuseStep 1950975 = 2926463) B2926463
theorem B2926469 : Blo 1949435 2926469 := bbase (se 4 (by rfl) ⟨274356, by rfl⟩ : syracuseStep 2926469 = 548713) (by norm_num)
theorem B1950979 : Blo 1949435 1950979 := bstep (se 1 (by rfl) ⟨1463234, by rfl⟩ : syracuseStep 1950979 = 2926469) B2926469
theorem B3292285 : Blo 1949435 3292285 := bbase (se 3 (by rfl) ⟨617303, by rfl⟩ : syracuseStep 3292285 = 1234607) (by norm_num)
theorem B4389713 : Blo 1949435 4389713 := bstep (se 2 (by rfl) ⟨1646142, by rfl⟩ : syracuseStep 4389713 = 3292285) B3292285
theorem B2926475 : Blo 1949435 2926475 := bstep (se 1 (by rfl) ⟨2194856, by rfl⟩ : syracuseStep 2926475 = 4389713) B4389713
theorem B1950983 : Blo 1949435 1950983 := bstep (se 1 (by rfl) ⟨1463237, by rfl⟩ : syracuseStep 1950983 = 2926475) B2926475
theorem B2194861 : Blo 1949435 2194861 := bbase (se 3 (by rfl) ⟨411536, by rfl⟩ : syracuseStep 2194861 = 823073) (by norm_num)
theorem B2926481 : Blo 1949435 2926481 := bstep (se 2 (by rfl) ⟨1097430, by rfl⟩ : syracuseStep 2926481 = 2194861) B2194861
theorem B1950987 : Blo 1949435 1950987 := bstep (se 1 (by rfl) ⟨1463240, by rfl⟩ : syracuseStep 1950987 = 2926481) B2926481
theorem B6584597 : Blo 1949435 6584597 := bbase (se 6 (by rfl) ⟨154326, by rfl⟩ : syracuseStep 6584597 = 308653) (by norm_num)
theorem B4389731 : Blo 1949435 4389731 := bstep (se 1 (by rfl) ⟨3292298, by rfl⟩ : syracuseStep 4389731 = 6584597) B6584597
theorem B2926487 : Blo 1949435 2926487 := bstep (se 1 (by rfl) ⟨2194865, by rfl⟩ : syracuseStep 2926487 = 4389731) B4389731
theorem B1950991 : Blo 1949435 1950991 := bstep (se 1 (by rfl) ⟨1463243, by rfl⟩ : syracuseStep 1950991 = 2926487) B2926487
theorem B2926493 : Blo 1949435 2926493 := bbase (se 3 (by rfl) ⟨548717, by rfl⟩ : syracuseStep 2926493 = 1097435) (by norm_num)
theorem B1950995 : Blo 1949435 1950995 := bstep (se 1 (by rfl) ⟨1463246, by rfl⟩ : syracuseStep 1950995 = 2926493) B2926493
theorem B4389749 : Blo 1949435 4389749 := bbase (se 5 (by rfl) ⟨205769, by rfl⟩ : syracuseStep 4389749 = 411539) (by norm_num)
theorem B2926499 : Blo 1949435 2926499 := bstep (se 1 (by rfl) ⟨2194874, by rfl⟩ : syracuseStep 2926499 = 4389749) B4389749
theorem B1950999 : Blo 1949435 1950999 := bstep (se 1 (by rfl) ⟨1463249, by rfl⟩ : syracuseStep 1950999 = 2926499) B2926499
theorem B4223693 : Blo 1949435 4223693 := bbase (se 3 (by rfl) ⟨791942, by rfl⟩ : syracuseStep 4223693 = 1583885) (by norm_num)
theorem B2815795 : Blo 1949435 2815795 := bstep (se 1 (by rfl) ⟨2111846, by rfl⟩ : syracuseStep 2815795 = 4223693) B4223693
theorem B3754393 : Blo 1949435 3754393 := bstep (se 2 (by rfl) ⟨1407897, by rfl⟩ : syracuseStep 3754393 = 2815795) B2815795
theorem B80093717 : Blo 1949435 80093717 := bstep (se 6 (by rfl) ⟨1877196, by rfl⟩ : syracuseStep 80093717 = 3754393) B3754393
theorem B53395811 : Blo 1949435 53395811 := bstep (se 1 (by rfl) ⟨40046858, by rfl⟩ : syracuseStep 53395811 = 80093717) B80093717
theorem B35597207 : Blo 1949435 35597207 := bstep (se 1 (by rfl) ⟨26697905, by rfl⟩ : syracuseStep 35597207 = 53395811) B53395811
theorem B23731471 : Blo 1949435 23731471 := bstep (se 1 (by rfl) ⟨17798603, by rfl⟩ : syracuseStep 23731471 = 35597207) B35597207
theorem B31641961 : Blo 1949435 31641961 := bstep (se 2 (by rfl) ⟨11865735, by rfl⟩ : syracuseStep 31641961 = 23731471) B23731471
theorem B42189281 : Blo 1949435 42189281 := bstep (se 2 (by rfl) ⟨15820980, by rfl⟩ : syracuseStep 42189281 = 31641961) B31641961
theorem B28126187 : Blo 1949435 28126187 := bstep (se 1 (by rfl) ⟨21094640, by rfl⟩ : syracuseStep 28126187 = 42189281) B42189281
theorem B18750791 : Blo 1949435 18750791 := bstep (se 1 (by rfl) ⟨14063093, by rfl⟩ : syracuseStep 18750791 = 28126187) B28126187
theorem B12500527 : Blo 1949435 12500527 := bstep (se 1 (by rfl) ⟨9375395, by rfl⟩ : syracuseStep 12500527 = 18750791) B18750791
theorem B16667369 : Blo 1949435 16667369 := bstep (se 2 (by rfl) ⟨6250263, by rfl⟩ : syracuseStep 16667369 = 12500527) B12500527
theorem B11111579 : Blo 1949435 11111579 := bstep (se 1 (by rfl) ⟨8333684, by rfl⟩ : syracuseStep 11111579 = 16667369) B16667369
theorem B7407719 : Blo 1949435 7407719 := bstep (se 1 (by rfl) ⟨5555789, by rfl⟩ : syracuseStep 7407719 = 11111579) B11111579
theorem B4938479 : Blo 1949435 4938479 := bstep (se 1 (by rfl) ⟨3703859, by rfl⟩ : syracuseStep 4938479 = 7407719) B7407719
theorem B3292319 : Blo 1949435 3292319 := bstep (se 1 (by rfl) ⟨2469239, by rfl⟩ : syracuseStep 3292319 = 4938479) B4938479
theorem B2194879 : Blo 1949435 2194879 := bstep (se 1 (by rfl) ⟨1646159, by rfl⟩ : syracuseStep 2194879 = 3292319) B3292319
theorem B2926505 : Blo 1949435 2926505 := bstep (se 2 (by rfl) ⟨1097439, by rfl⟩ : syracuseStep 2926505 = 2194879) B2194879
theorem B1951003 : Blo 1949435 1951003 := bstep (se 1 (by rfl) ⟨1463252, by rfl⟩ : syracuseStep 1951003 = 2926505) B2926505
theorem B7407733 : Blo 1949435 7407733 := bbase (se 5 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 7407733 = 694475) (by norm_num)
theorem B9876977 : Blo 1949435 9876977 := bstep (se 2 (by rfl) ⟨3703866, by rfl⟩ : syracuseStep 9876977 = 7407733) B7407733
theorem B6584651 : Blo 1949435 6584651 := bstep (se 1 (by rfl) ⟨4938488, by rfl⟩ : syracuseStep 6584651 = 9876977) B9876977
theorem B4389767 : Blo 1949435 4389767 := bstep (se 1 (by rfl) ⟨3292325, by rfl⟩ : syracuseStep 4389767 = 6584651) B6584651
theorem B2926511 : Blo 1949435 2926511 := bstep (se 1 (by rfl) ⟨2194883, by rfl⟩ : syracuseStep 2926511 = 4389767) B4389767
theorem B1951007 : Blo 1949435 1951007 := bstep (se 1 (by rfl) ⟨1463255, by rfl⟩ : syracuseStep 1951007 = 2926511) B2926511
theorem B2926517 : Blo 1949435 2926517 := bbase (se 5 (by rfl) ⟨137180, by rfl⟩ : syracuseStep 2926517 = 274361) (by norm_num)
theorem B1951011 : Blo 1949435 1951011 := bstep (se 1 (by rfl) ⟨1463258, by rfl⟩ : syracuseStep 1951011 = 2926517) B2926517
theorem B4938509 : Blo 1949435 4938509 := bbase (se 3 (by rfl) ⟨925970, by rfl⟩ : syracuseStep 4938509 = 1851941) (by norm_num)
theorem B3292339 : Blo 1949435 3292339 := bstep (se 1 (by rfl) ⟨2469254, by rfl⟩ : syracuseStep 3292339 = 4938509) B4938509
theorem B4389785 : Blo 1949435 4389785 := bstep (se 2 (by rfl) ⟨1646169, by rfl⟩ : syracuseStep 4389785 = 3292339) B3292339
theorem B2926523 : Blo 1949435 2926523 := bstep (se 1 (by rfl) ⟨2194892, by rfl⟩ : syracuseStep 2926523 = 4389785) B4389785
theorem B1951015 : Blo 1949435 1951015 := bstep (se 1 (by rfl) ⟨1463261, by rfl⟩ : syracuseStep 1951015 = 2926523) B2926523
theorem B2194897 : Blo 1949435 2194897 := bbase (se 2 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 2194897 = 1646173) (by norm_num)
theorem B2926529 : Blo 1949435 2926529 := bstep (se 2 (by rfl) ⟨1097448, by rfl⟩ : syracuseStep 2926529 = 2194897) B2194897
theorem B1951019 : Blo 1949435 1951019 := bstep (se 1 (by rfl) ⟨1463264, by rfl⟩ : syracuseStep 1951019 = 2926529) B2926529
theorem B4166885 : Blo 1949435 4166885 := bbase (se 4 (by rfl) ⟨390645, by rfl⟩ : syracuseStep 4166885 = 781291) (by norm_num)
theorem B2777923 : Blo 1949435 2777923 := bstep (se 1 (by rfl) ⟨2083442, by rfl⟩ : syracuseStep 2777923 = 4166885) B4166885
theorem B3703897 : Blo 1949435 3703897 := bstep (se 2 (by rfl) ⟨1388961, by rfl⟩ : syracuseStep 3703897 = 2777923) B2777923
theorem B4938529 : Blo 1949435 4938529 := bstep (se 2 (by rfl) ⟨1851948, by rfl⟩ : syracuseStep 4938529 = 3703897) B3703897
theorem B6584705 : Blo 1949435 6584705 := bstep (se 2 (by rfl) ⟨2469264, by rfl⟩ : syracuseStep 6584705 = 4938529) B4938529
theorem B4389803 : Blo 1949435 4389803 := bstep (se 1 (by rfl) ⟨3292352, by rfl⟩ : syracuseStep 4389803 = 6584705) B6584705
theorem B2926535 : Blo 1949435 2926535 := bstep (se 1 (by rfl) ⟨2194901, by rfl⟩ : syracuseStep 2926535 = 4389803) B4389803
theorem B1951023 : Blo 1949435 1951023 := bstep (se 1 (by rfl) ⟨1463267, by rfl⟩ : syracuseStep 1951023 = 2926535) B2926535
theorem B2926541 : Blo 1949435 2926541 := bbase (se 3 (by rfl) ⟨548726, by rfl⟩ : syracuseStep 2926541 = 1097453) (by norm_num)
theorem B1951027 : Blo 1949435 1951027 := bstep (se 1 (by rfl) ⟨1463270, by rfl⟩ : syracuseStep 1951027 = 2926541) B2926541
theorem B4389821 : Blo 1949435 4389821 := bbase (se 3 (by rfl) ⟨823091, by rfl⟩ : syracuseStep 4389821 = 1646183) (by norm_num)
theorem B2926547 : Blo 1949435 2926547 := bstep (se 1 (by rfl) ⟨2194910, by rfl⟩ : syracuseStep 2926547 = 4389821) B4389821
theorem B1951031 : Blo 1949435 1951031 := bstep (se 1 (by rfl) ⟨1463273, by rfl⟩ : syracuseStep 1951031 = 2926547) B2926547
theorem B3292373 : Blo 1949435 3292373 := bbase (se 7 (by rfl) ⟨38582, by rfl⟩ : syracuseStep 3292373 = 77165) (by norm_num)
theorem B2194915 : Blo 1949435 2194915 := bstep (se 1 (by rfl) ⟨1646186, by rfl⟩ : syracuseStep 2194915 = 3292373) B3292373
theorem B2926553 : Blo 1949435 2926553 := bstep (se 2 (by rfl) ⟨1097457, by rfl⟩ : syracuseStep 2926553 = 2194915) B2194915
theorem B1951035 : Blo 1949435 1951035 := bstep (se 1 (by rfl) ⟨1463276, by rfl⟩ : syracuseStep 1951035 = 2926553) B2926553
theorem B3125189 : Blo 1949435 3125189 := bbase (se 4 (by rfl) ⟨292986, by rfl⟩ : syracuseStep 3125189 = 585973) (by norm_num)
theorem B8333837 : Blo 1949435 8333837 := bstep (se 3 (by rfl) ⟨1562594, by rfl⟩ : syracuseStep 8333837 = 3125189) B3125189
theorem B5555891 : Blo 1949435 5555891 := bstep (se 1 (by rfl) ⟨4166918, by rfl⟩ : syracuseStep 5555891 = 8333837) B8333837
theorem B14815709 : Blo 1949435 14815709 := bstep (se 3 (by rfl) ⟨2777945, by rfl⟩ : syracuseStep 14815709 = 5555891) B5555891
theorem B9877139 : Blo 1949435 9877139 := bstep (se 1 (by rfl) ⟨7407854, by rfl⟩ : syracuseStep 9877139 = 14815709) B14815709
theorem B6584759 : Blo 1949435 6584759 := bstep (se 1 (by rfl) ⟨4938569, by rfl⟩ : syracuseStep 6584759 = 9877139) B9877139
theorem B4389839 : Blo 1949435 4389839 := bstep (se 1 (by rfl) ⟨3292379, by rfl⟩ : syracuseStep 4389839 = 6584759) B6584759
theorem B2926559 : Blo 1949435 2926559 := bstep (se 1 (by rfl) ⟨2194919, by rfl⟩ : syracuseStep 2926559 = 4389839) B4389839
theorem B1951039 : Blo 1949435 1951039 := bstep (se 1 (by rfl) ⟨1463279, by rfl⟩ : syracuseStep 1951039 = 2926559) B2926559
theorem B2926565 : Blo 1949435 2926565 := bbase (se 4 (by rfl) ⟨274365, by rfl⟩ : syracuseStep 2926565 = 548731) (by norm_num)
theorem B1951043 : Blo 1949435 1951043 := bstep (se 1 (by rfl) ⟨1463282, by rfl⟩ : syracuseStep 1951043 = 2926565) B2926565
theorem B6250405 : Blo 1949435 6250405 := bbase (se 4 (by rfl) ⟨585975, by rfl⟩ : syracuseStep 6250405 = 1171951) (by norm_num)
theorem B8333873 : Blo 1949435 8333873 := bstep (se 2 (by rfl) ⟨3125202, by rfl⟩ : syracuseStep 8333873 = 6250405) B6250405
theorem B5555915 : Blo 1949435 5555915 := bstep (se 1 (by rfl) ⟨4166936, by rfl⟩ : syracuseStep 5555915 = 8333873) B8333873
theorem B3703943 : Blo 1949435 3703943 := bstep (se 1 (by rfl) ⟨2777957, by rfl⟩ : syracuseStep 3703943 = 5555915) B5555915
theorem B2469295 : Blo 1949435 2469295 := bstep (se 1 (by rfl) ⟨1851971, by rfl⟩ : syracuseStep 2469295 = 3703943) B3703943
theorem B3292393 : Blo 1949435 3292393 := bstep (se 2 (by rfl) ⟨1234647, by rfl⟩ : syracuseStep 3292393 = 2469295) B2469295
theorem B4389857 : Blo 1949435 4389857 := bstep (se 2 (by rfl) ⟨1646196, by rfl⟩ : syracuseStep 4389857 = 3292393) B3292393
theorem B2926571 : Blo 1949435 2926571 := bstep (se 1 (by rfl) ⟨2194928, by rfl⟩ : syracuseStep 2926571 = 4389857) B4389857
theorem B1951047 : Blo 1949435 1951047 := bstep (se 1 (by rfl) ⟨1463285, by rfl⟩ : syracuseStep 1951047 = 2926571) B2926571
theorem B2194933 : Blo 1949435 2194933 := bbase (se 5 (by rfl) ⟨102887, by rfl⟩ : syracuseStep 2194933 = 205775) (by norm_num)
theorem B2926577 : Blo 1949435 2926577 := bstep (se 2 (by rfl) ⟨1097466, by rfl⟩ : syracuseStep 2926577 = 2194933) B2194933
theorem B1951051 : Blo 1949435 1951051 := bstep (se 1 (by rfl) ⟨1463288, by rfl⟩ : syracuseStep 1951051 = 2926577) B2926577
theorem B2469305 : Blo 1949435 2469305 := bbase (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) (by norm_num)
theorem B6584813 : Blo 1949435 6584813 := bstep (se 3 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 6584813 = 2469305) B2469305
theorem B4389875 : Blo 1949435 4389875 := bstep (se 1 (by rfl) ⟨3292406, by rfl⟩ : syracuseStep 4389875 = 6584813) B6584813
theorem B2926583 : Blo 1949435 2926583 := bstep (se 1 (by rfl) ⟨2194937, by rfl⟩ : syracuseStep 2926583 = 4389875) B4389875
theorem B1951055 : Blo 1949435 1951055 := bstep (se 1 (by rfl) ⟨1463291, by rfl⟩ : syracuseStep 1951055 = 2926583) B2926583
theorem B2926589 : Blo 1949435 2926589 := bbase (se 3 (by rfl) ⟨548735, by rfl⟩ : syracuseStep 2926589 = 1097471) (by norm_num)
theorem B1951059 : Blo 1949435 1951059 := bstep (se 1 (by rfl) ⟨1463294, by rfl⟩ : syracuseStep 1951059 = 2926589) B2926589
theorem B4389893 : Blo 1949435 4389893 := bbase (se 4 (by rfl) ⟨411552, by rfl⟩ : syracuseStep 4389893 = 823105) (by norm_num)
theorem B2926595 : Blo 1949435 2926595 := bstep (se 1 (by rfl) ⟨2194946, by rfl⟩ : syracuseStep 2926595 = 4389893) B4389893
theorem B1951063 : Blo 1949435 1951063 := bstep (se 1 (by rfl) ⟨1463297, by rfl⟩ : syracuseStep 1951063 = 2926595) B2926595
theorem B3703981 : Blo 1949435 3703981 := bbase (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) (by norm_num)
theorem B4938641 : Blo 1949435 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B3292427 : Blo 1949435 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B2194951 : Blo 1949435 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B2926601 : Blo 1949435 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B1951067 : Blo 1949435 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B9877301 : Blo 1949435 9877301 := bbase (se 5 (by rfl) ⟨462998, by rfl⟩ : syracuseStep 9877301 = 925997) (by norm_num)
theorem B6584867 : Blo 1949435 6584867 := bstep (se 1 (by rfl) ⟨4938650, by rfl⟩ : syracuseStep 6584867 = 9877301) B9877301
theorem B4389911 : Blo 1949435 4389911 := bstep (se 1 (by rfl) ⟨3292433, by rfl⟩ : syracuseStep 4389911 = 6584867) B6584867
theorem B2926607 : Blo 1949435 2926607 := bstep (se 1 (by rfl) ⟨2194955, by rfl⟩ : syracuseStep 2926607 = 4389911) B4389911
theorem B1951071 : Blo 1949435 1951071 := bstep (se 1 (by rfl) ⟨1463303, by rfl⟩ : syracuseStep 1951071 = 2926607) B2926607
theorem B2926613 : Blo 1949435 2926613 := bbase (se 6 (by rfl) ⟨68592, by rfl⟩ : syracuseStep 2926613 = 137185) (by norm_num)
theorem B1951075 : Blo 1949435 1951075 := bstep (se 1 (by rfl) ⟨1463306, by rfl⟩ : syracuseStep 1951075 = 2926613) B2926613
theorem B12501013 : Blo 1949435 12501013 := bbase (se 6 (by rfl) ⟨292992, by rfl⟩ : syracuseStep 12501013 = 585985) (by norm_num)
theorem B16668017 : Blo 1949435 16668017 := bstep (se 2 (by rfl) ⟨6250506, by rfl⟩ : syracuseStep 16668017 = 12501013) B12501013
theorem B11112011 : Blo 1949435 11112011 := bstep (se 1 (by rfl) ⟨8334008, by rfl⟩ : syracuseStep 11112011 = 16668017) B16668017
theorem B7408007 : Blo 1949435 7408007 := bstep (se 1 (by rfl) ⟨5556005, by rfl⟩ : syracuseStep 7408007 = 11112011) B11112011
theorem B4938671 : Blo 1949435 4938671 := bstep (se 1 (by rfl) ⟨3704003, by rfl⟩ : syracuseStep 4938671 = 7408007) B7408007
theorem B3292447 : Blo 1949435 3292447 := bstep (se 1 (by rfl) ⟨2469335, by rfl⟩ : syracuseStep 3292447 = 4938671) B4938671
theorem B4389929 : Blo 1949435 4389929 := bstep (se 2 (by rfl) ⟨1646223, by rfl⟩ : syracuseStep 4389929 = 3292447) B3292447
theorem B2926619 : Blo 1949435 2926619 := bstep (se 1 (by rfl) ⟨2194964, by rfl⟩ : syracuseStep 2926619 = 4389929) B4389929
theorem B1951079 : Blo 1949435 1951079 := bstep (se 1 (by rfl) ⟨1463309, by rfl⟩ : syracuseStep 1951079 = 2926619) B2926619
theorem B2194969 : Blo 1949435 2194969 := bbase (se 2 (by rfl) ⟨823113, by rfl⟩ : syracuseStep 2194969 = 1646227) (by norm_num)
theorem B2926625 : Blo 1949435 2926625 := bstep (se 2 (by rfl) ⟨1097484, by rfl⟩ : syracuseStep 2926625 = 2194969) B2194969
theorem B1951083 : Blo 1949435 1951083 := bstep (se 1 (by rfl) ⟨1463312, by rfl⟩ : syracuseStep 1951083 = 2926625) B2926625
theorem B7408037 : Blo 1949435 7408037 := bbase (se 4 (by rfl) ⟨694503, by rfl⟩ : syracuseStep 7408037 = 1389007) (by norm_num)
theorem B4938691 : Blo 1949435 4938691 := bstep (se 1 (by rfl) ⟨3704018, by rfl⟩ : syracuseStep 4938691 = 7408037) B7408037
theorem B6584921 : Blo 1949435 6584921 := bstep (se 2 (by rfl) ⟨2469345, by rfl⟩ : syracuseStep 6584921 = 4938691) B4938691
theorem B4389947 : Blo 1949435 4389947 := bstep (se 1 (by rfl) ⟨3292460, by rfl⟩ : syracuseStep 4389947 = 6584921) B6584921
theorem B2926631 : Blo 1949435 2926631 := bstep (se 1 (by rfl) ⟨2194973, by rfl⟩ : syracuseStep 2926631 = 4389947) B4389947
theorem B1951087 : Blo 1949435 1951087 := bstep (se 1 (by rfl) ⟨1463315, by rfl⟩ : syracuseStep 1951087 = 2926631) B2926631
theorem B2926637 : Blo 1949435 2926637 := bbase (se 3 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 2926637 = 1097489) (by norm_num)
theorem B1951091 : Blo 1949435 1951091 := bstep (se 1 (by rfl) ⟨1463318, by rfl⟩ : syracuseStep 1951091 = 2926637) B2926637
theorem B4389965 : Blo 1949435 4389965 := bbase (se 3 (by rfl) ⟨823118, by rfl⟩ : syracuseStep 4389965 = 1646237) (by norm_num)
theorem B2926643 : Blo 1949435 2926643 := bstep (se 1 (by rfl) ⟨2194982, by rfl⟩ : syracuseStep 2926643 = 4389965) B4389965
theorem B1951095 : Blo 1949435 1951095 := bstep (se 1 (by rfl) ⟨1463321, by rfl⟩ : syracuseStep 1951095 = 2926643) B2926643
theorem B2469361 : Blo 1949435 2469361 := bbase (se 2 (by rfl) ⟨926010, by rfl⟩ : syracuseStep 2469361 = 1852021) (by norm_num)
theorem B3292481 : Blo 1949435 3292481 := bstep (se 2 (by rfl) ⟨1234680, by rfl⟩ : syracuseStep 3292481 = 2469361) B2469361
theorem B2194987 : Blo 1949435 2194987 := bstep (se 1 (by rfl) ⟨1646240, by rfl⟩ : syracuseStep 2194987 = 3292481) B3292481
theorem B2926649 : Blo 1949435 2926649 := bstep (se 2 (by rfl) ⟨1097493, by rfl⟩ : syracuseStep 2926649 = 2194987) B2194987
theorem B1951099 : Blo 1949435 1951099 := bstep (se 1 (by rfl) ⟨1463324, by rfl⟩ : syracuseStep 1951099 = 2926649) B2926649
theorem B2636965 : Blo 1949435 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B14063813 : Blo 1949435 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B9375875 : Blo 1949435 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B6250583 : Blo 1949435 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B4167055 : Blo 1949435 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B22224293 : Blo 1949435 22224293 := bstep (se 4 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 22224293 = 4167055) B4167055
theorem B14816195 : Blo 1949435 14816195 := bstep (se 1 (by rfl) ⟨11112146, by rfl⟩ : syracuseStep 14816195 = 22224293) B22224293
theorem B9877463 : Blo 1949435 9877463 := bstep (se 1 (by rfl) ⟨7408097, by rfl⟩ : syracuseStep 9877463 = 14816195) B14816195
theorem B6584975 : Blo 1949435 6584975 := bstep (se 1 (by rfl) ⟨4938731, by rfl⟩ : syracuseStep 6584975 = 9877463) B9877463
theorem B4389983 : Blo 1949435 4389983 := bstep (se 1 (by rfl) ⟨3292487, by rfl⟩ : syracuseStep 4389983 = 6584975) B6584975
theorem B2926655 : Blo 1949435 2926655 := bstep (se 1 (by rfl) ⟨2194991, by rfl⟩ : syracuseStep 2926655 = 4389983) B4389983
theorem B1951103 : Blo 1949435 1951103 := bstep (se 1 (by rfl) ⟨1463327, by rfl⟩ : syracuseStep 1951103 = 2926655) B2926655
theorem B2926661 : Blo 1949435 2926661 := bbase (se 4 (by rfl) ⟨274374, by rfl⟩ : syracuseStep 2926661 = 548749) (by norm_num)
theorem B1951107 : Blo 1949435 1951107 := bstep (se 1 (by rfl) ⟨1463330, by rfl⟩ : syracuseStep 1951107 = 2926661) B2926661
theorem B3292501 : Blo 1949435 3292501 := bbase (se 11 (by rfl) ⟨2411, by rfl⟩ : syracuseStep 3292501 = 4823) (by norm_num)
theorem B4390001 : Blo 1949435 4390001 := bstep (se 2 (by rfl) ⟨1646250, by rfl⟩ : syracuseStep 4390001 = 3292501) B3292501
theorem B2926667 : Blo 1949435 2926667 := bstep (se 1 (by rfl) ⟨2195000, by rfl⟩ : syracuseStep 2926667 = 4390001) B4390001
theorem B1951111 : Blo 1949435 1951111 := bstep (se 1 (by rfl) ⟨1463333, by rfl⟩ : syracuseStep 1951111 = 2926667) B2926667
theorem B2195005 : Blo 1949435 2195005 := bbase (se 3 (by rfl) ⟨411563, by rfl⟩ : syracuseStep 2195005 = 823127) (by norm_num)
theorem B2926673 : Blo 1949435 2926673 := bstep (se 2 (by rfl) ⟨1097502, by rfl⟩ : syracuseStep 2926673 = 2195005) B2195005
theorem B1951115 : Blo 1949435 1951115 := bstep (se 1 (by rfl) ⟨1463336, by rfl⟩ : syracuseStep 1951115 = 2926673) B2926673
theorem B6585029 : Blo 1949435 6585029 := bbase (se 4 (by rfl) ⟨617346, by rfl⟩ : syracuseStep 6585029 = 1234693) (by norm_num)
theorem B4390019 : Blo 1949435 4390019 := bstep (se 1 (by rfl) ⟨3292514, by rfl⟩ : syracuseStep 4390019 = 6585029) B6585029
theorem B2926679 : Blo 1949435 2926679 := bstep (se 1 (by rfl) ⟨2195009, by rfl⟩ : syracuseStep 2926679 = 4390019) B4390019
theorem B1951119 : Blo 1949435 1951119 := bstep (se 1 (by rfl) ⟨1463339, by rfl⟩ : syracuseStep 1951119 = 2926679) B2926679
theorem B2926685 : Blo 1949435 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B1951123 : Blo 1949435 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B4390037 : Blo 1949435 4390037 := bbase (se 6 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 4390037 = 205783) (by norm_num)
theorem B2926691 : Blo 1949435 2926691 := bstep (se 1 (by rfl) ⟨2195018, by rfl⟩ : syracuseStep 2926691 = 4390037) B4390037
theorem B1951127 : Blo 1949435 1951127 := bstep (se 1 (by rfl) ⟨1463345, by rfl⟩ : syracuseStep 1951127 = 2926691) B2926691
theorem B2778077 : Blo 1949435 2778077 := bbase (se 3 (by rfl) ⟨520889, by rfl⟩ : syracuseStep 2778077 = 1041779) (by norm_num)
theorem B7408205 : Blo 1949435 7408205 := bstep (se 3 (by rfl) ⟨1389038, by rfl⟩ : syracuseStep 7408205 = 2778077) B2778077
theorem B4938803 : Blo 1949435 4938803 := bstep (se 1 (by rfl) ⟨3704102, by rfl⟩ : syracuseStep 4938803 = 7408205) B7408205
theorem B3292535 : Blo 1949435 3292535 := bstep (se 1 (by rfl) ⟨2469401, by rfl⟩ : syracuseStep 3292535 = 4938803) B4938803
theorem B2195023 : Blo 1949435 2195023 := bstep (se 1 (by rfl) ⟨1646267, by rfl⟩ : syracuseStep 2195023 = 3292535) B3292535
theorem B2926697 : Blo 1949435 2926697 := bstep (se 2 (by rfl) ⟨1097511, by rfl⟩ : syracuseStep 2926697 = 2195023) B2195023
theorem B1951131 : Blo 1949435 1951131 := bstep (se 1 (by rfl) ⟨1463348, by rfl⟩ : syracuseStep 1951131 = 2926697) B2926697
theorem B2854405 : Blo 1949435 2854405 := bbase (se 4 (by rfl) ⟨267600, by rfl⟩ : syracuseStep 2854405 = 535201) (by norm_num)
theorem B3805873 : Blo 1949435 3805873 := bstep (se 2 (by rfl) ⟨1427202, by rfl⟩ : syracuseStep 3805873 = 2854405) B2854405
theorem B20297989 : Blo 1949435 20297989 := bstep (se 4 (by rfl) ⟨1902936, by rfl⟩ : syracuseStep 20297989 = 3805873) B3805873
theorem B27063985 : Blo 1949435 27063985 := bstep (se 2 (by rfl) ⟨10148994, by rfl⟩ : syracuseStep 27063985 = 20297989) B20297989
theorem B36085313 : Blo 1949435 36085313 := bstep (se 2 (by rfl) ⟨13531992, by rfl⟩ : syracuseStep 36085313 = 27063985) B27063985
theorem B24056875 : Blo 1949435 24056875 := bstep (se 1 (by rfl) ⟨18042656, by rfl⟩ : syracuseStep 24056875 = 36085313) B36085313
theorem B32075833 : Blo 1949435 32075833 := bstep (se 2 (by rfl) ⟨12028437, by rfl⟩ : syracuseStep 32075833 = 24056875) B24056875
theorem B42767777 : Blo 1949435 42767777 := bstep (se 2 (by rfl) ⟨16037916, by rfl⟩ : syracuseStep 42767777 = 32075833) B32075833
theorem B28511851 : Blo 1949435 28511851 := bstep (se 1 (by rfl) ⟨21383888, by rfl⟩ : syracuseStep 28511851 = 42767777) B42767777
theorem B38015801 : Blo 1949435 38015801 := bstep (se 2 (by rfl) ⟨14255925, by rfl⟩ : syracuseStep 38015801 = 28511851) B28511851
theorem B25343867 : Blo 1949435 25343867 := bstep (se 1 (by rfl) ⟨19007900, by rfl⟩ : syracuseStep 25343867 = 38015801) B38015801
theorem B67583645 : Blo 1949435 67583645 := bstep (se 3 (by rfl) ⟨12671933, by rfl⟩ : syracuseStep 67583645 = 25343867) B25343867
theorem B45055763 : Blo 1949435 45055763 := bstep (se 1 (by rfl) ⟨33791822, by rfl⟩ : syracuseStep 45055763 = 67583645) B67583645
theorem B30037175 : Blo 1949435 30037175 := bstep (se 1 (by rfl) ⟨22527881, by rfl⟩ : syracuseStep 30037175 = 45055763) B45055763
theorem B20024783 : Blo 1949435 20024783 := bstep (se 1 (by rfl) ⟨15018587, by rfl⟩ : syracuseStep 20024783 = 30037175) B30037175
theorem B13349855 : Blo 1949435 13349855 := bstep (se 1 (by rfl) ⟨10012391, by rfl⟩ : syracuseStep 13349855 = 20024783) B20024783
theorem B8899903 : Blo 1949435 8899903 := bstep (se 1 (by rfl) ⟨6674927, by rfl⟩ : syracuseStep 8899903 = 13349855) B13349855
theorem B11866537 : Blo 1949435 11866537 := bstep (se 2 (by rfl) ⟨4449951, by rfl⟩ : syracuseStep 11866537 = 8899903) B8899903
theorem B15822049 : Blo 1949435 15822049 := bstep (se 2 (by rfl) ⟨5933268, by rfl⟩ : syracuseStep 15822049 = 11866537) B11866537
theorem B21096065 : Blo 1949435 21096065 := bstep (se 2 (by rfl) ⟨7911024, by rfl⟩ : syracuseStep 21096065 = 15822049) B15822049
theorem B14064043 : Blo 1949435 14064043 := bstep (se 1 (by rfl) ⟨10548032, by rfl⟩ : syracuseStep 14064043 = 21096065) B21096065
theorem B18752057 : Blo 1949435 18752057 := bstep (se 2 (by rfl) ⟨7032021, by rfl⟩ : syracuseStep 18752057 = 14064043) B14064043
theorem B12501371 : Blo 1949435 12501371 := bstep (se 1 (by rfl) ⟨9376028, by rfl⟩ : syracuseStep 12501371 = 18752057) B18752057
theorem B8334247 : Blo 1949435 8334247 := bstep (se 1 (by rfl) ⟨6250685, by rfl⟩ : syracuseStep 8334247 = 12501371) B12501371
theorem B11112329 : Blo 1949435 11112329 := bstep (se 2 (by rfl) ⟨4167123, by rfl⟩ : syracuseStep 11112329 = 8334247) B8334247
theorem B7408219 : Blo 1949435 7408219 := bstep (se 1 (by rfl) ⟨5556164, by rfl⟩ : syracuseStep 7408219 = 11112329) B11112329
theorem B9877625 : Blo 1949435 9877625 := bstep (se 2 (by rfl) ⟨3704109, by rfl⟩ : syracuseStep 9877625 = 7408219) B7408219
theorem B6585083 : Blo 1949435 6585083 := bstep (se 1 (by rfl) ⟨4938812, by rfl⟩ : syracuseStep 6585083 = 9877625) B9877625
theorem B4390055 : Blo 1949435 4390055 := bstep (se 1 (by rfl) ⟨3292541, by rfl⟩ : syracuseStep 4390055 = 6585083) B6585083
theorem B2926703 : Blo 1949435 2926703 := bstep (se 1 (by rfl) ⟨2195027, by rfl⟩ : syracuseStep 2926703 = 4390055) B4390055
theorem B1951135 : Blo 1949435 1951135 := bstep (se 1 (by rfl) ⟨1463351, by rfl⟩ : syracuseStep 1951135 = 2926703) B2926703
theorem B2926709 : Blo 1949435 2926709 := bbase (se 5 (by rfl) ⟨137189, by rfl⟩ : syracuseStep 2926709 = 274379) (by norm_num)
theorem B1951139 : Blo 1949435 1951139 := bstep (se 1 (by rfl) ⟨1463354, by rfl⟩ : syracuseStep 1951139 = 2926709) B2926709
theorem B3704125 : Blo 1949435 3704125 := bbase (se 3 (by rfl) ⟨694523, by rfl⟩ : syracuseStep 3704125 = 1389047) (by norm_num)
theorem B4938833 : Blo 1949435 4938833 := bstep (se 2 (by rfl) ⟨1852062, by rfl⟩ : syracuseStep 4938833 = 3704125) B3704125
theorem B3292555 : Blo 1949435 3292555 := bstep (se 1 (by rfl) ⟨2469416, by rfl⟩ : syracuseStep 3292555 = 4938833) B4938833
theorem B4390073 : Blo 1949435 4390073 := bstep (se 2 (by rfl) ⟨1646277, by rfl⟩ : syracuseStep 4390073 = 3292555) B3292555
theorem B2926715 : Blo 1949435 2926715 := bstep (se 1 (by rfl) ⟨2195036, by rfl⟩ : syracuseStep 2926715 = 4390073) B4390073
theorem B1951143 : Blo 1949435 1951143 := bstep (se 1 (by rfl) ⟨1463357, by rfl⟩ : syracuseStep 1951143 = 2926715) B2926715
theorem B2195041 : Blo 1949435 2195041 := bbase (se 2 (by rfl) ⟨823140, by rfl⟩ : syracuseStep 2195041 = 1646281) (by norm_num)
theorem B2926721 : Blo 1949435 2926721 := bstep (se 2 (by rfl) ⟨1097520, by rfl⟩ : syracuseStep 2926721 = 2195041) B2195041
theorem B1951147 : Blo 1949435 1951147 := bstep (se 1 (by rfl) ⟨1463360, by rfl⟩ : syracuseStep 1951147 = 2926721) B2926721
theorem B4938853 : Blo 1949435 4938853 := bbase (se 4 (by rfl) ⟨463017, by rfl⟩ : syracuseStep 4938853 = 926035) (by norm_num)
theorem B6585137 : Blo 1949435 6585137 := bstep (se 2 (by rfl) ⟨2469426, by rfl⟩ : syracuseStep 6585137 = 4938853) B4938853
theorem B4390091 : Blo 1949435 4390091 := bstep (se 1 (by rfl) ⟨3292568, by rfl⟩ : syracuseStep 4390091 = 6585137) B6585137
theorem B2926727 : Blo 1949435 2926727 := bstep (se 1 (by rfl) ⟨2195045, by rfl⟩ : syracuseStep 2926727 = 4390091) B4390091
theorem B1951151 : Blo 1949435 1951151 := bstep (se 1 (by rfl) ⟨1463363, by rfl⟩ : syracuseStep 1951151 = 2926727) B2926727
theorem B2926733 : Blo 1949435 2926733 := bbase (se 3 (by rfl) ⟨548762, by rfl⟩ : syracuseStep 2926733 = 1097525) (by norm_num)
theorem B1951155 : Blo 1949435 1951155 := bstep (se 1 (by rfl) ⟨1463366, by rfl⟩ : syracuseStep 1951155 = 2926733) B2926733
theorem B4390109 : Blo 1949435 4390109 := bbase (se 3 (by rfl) ⟨823145, by rfl⟩ : syracuseStep 4390109 = 1646291) (by norm_num)
theorem B2926739 : Blo 1949435 2926739 := bstep (se 1 (by rfl) ⟨2195054, by rfl⟩ : syracuseStep 2926739 = 4390109) B4390109
theorem B1951159 : Blo 1949435 1951159 := bstep (se 1 (by rfl) ⟨1463369, by rfl⟩ : syracuseStep 1951159 = 2926739) B2926739
theorem B3292589 : Blo 1949435 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B2195059 : Blo 1949435 2195059 := bstep (se 1 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 2195059 = 3292589) B3292589
theorem B2926745 : Blo 1949435 2926745 := bstep (se 2 (by rfl) ⟨1097529, by rfl⟩ : syracuseStep 2926745 = 2195059) B2195059
theorem B1951163 : Blo 1949435 1951163 := bstep (se 1 (by rfl) ⟨1463372, by rfl⟩ : syracuseStep 1951163 = 2926745) B2926745
theorem B23733461 : Blo 1949435 23733461 := bbase (se 7 (by rfl) ⟨278126, by rfl⟩ : syracuseStep 23733461 = 556253) (by norm_num)
theorem B15822307 : Blo 1949435 15822307 := bstep (se 1 (by rfl) ⟨11866730, by rfl⟩ : syracuseStep 15822307 = 23733461) B23733461
theorem B84385637 : Blo 1949435 84385637 := bstep (se 4 (by rfl) ⟨7911153, by rfl⟩ : syracuseStep 84385637 = 15822307) B15822307
theorem B56257091 : Blo 1949435 56257091 := bstep (se 1 (by rfl) ⟨42192818, by rfl⟩ : syracuseStep 56257091 = 84385637) B84385637
theorem B37504727 : Blo 1949435 37504727 := bstep (se 1 (by rfl) ⟨28128545, by rfl⟩ : syracuseStep 37504727 = 56257091) B56257091
theorem B25003151 : Blo 1949435 25003151 := bstep (se 1 (by rfl) ⟨18752363, by rfl⟩ : syracuseStep 25003151 = 37504727) B37504727
theorem B16668767 : Blo 1949435 16668767 := bstep (se 1 (by rfl) ⟨12501575, by rfl⟩ : syracuseStep 16668767 = 25003151) B25003151
theorem B11112511 : Blo 1949435 11112511 := bstep (se 1 (by rfl) ⟨8334383, by rfl⟩ : syracuseStep 11112511 = 16668767) B16668767
theorem B14816681 : Blo 1949435 14816681 := bstep (se 2 (by rfl) ⟨5556255, by rfl⟩ : syracuseStep 14816681 = 11112511) B11112511
theorem B9877787 : Blo 1949435 9877787 := bstep (se 1 (by rfl) ⟨7408340, by rfl⟩ : syracuseStep 9877787 = 14816681) B14816681
theorem B6585191 : Blo 1949435 6585191 := bstep (se 1 (by rfl) ⟨4938893, by rfl⟩ : syracuseStep 6585191 = 9877787) B9877787
theorem B4390127 : Blo 1949435 4390127 := bstep (se 1 (by rfl) ⟨3292595, by rfl⟩ : syracuseStep 4390127 = 6585191) B6585191
theorem B2926751 : Blo 1949435 2926751 := bstep (se 1 (by rfl) ⟨2195063, by rfl⟩ : syracuseStep 2926751 = 4390127) B4390127
theorem B1951167 : Blo 1949435 1951167 := bstep (se 1 (by rfl) ⟨1463375, by rfl⟩ : syracuseStep 1951167 = 2926751) B2926751
theorem B2926757 : Blo 1949435 2926757 := bbase (se 4 (by rfl) ⟨274383, by rfl⟩ : syracuseStep 2926757 = 548767) (by norm_num)
theorem B1951171 : Blo 1949435 1951171 := bstep (se 1 (by rfl) ⟨1463378, by rfl⟩ : syracuseStep 1951171 = 2926757) B2926757
theorem B2469457 : Blo 1949435 2469457 := bbase (se 2 (by rfl) ⟨926046, by rfl⟩ : syracuseStep 2469457 = 1852093) (by norm_num)
theorem B3292609 : Blo 1949435 3292609 := bstep (se 2 (by rfl) ⟨1234728, by rfl⟩ : syracuseStep 3292609 = 2469457) B2469457
theorem B4390145 : Blo 1949435 4390145 := bstep (se 2 (by rfl) ⟨1646304, by rfl⟩ : syracuseStep 4390145 = 3292609) B3292609
theorem B2926763 : Blo 1949435 2926763 := bstep (se 1 (by rfl) ⟨2195072, by rfl⟩ : syracuseStep 2926763 = 4390145) B4390145
theorem B1951175 : Blo 1949435 1951175 := bstep (se 1 (by rfl) ⟨1463381, by rfl⟩ : syracuseStep 1951175 = 2926763) B2926763
theorem B2195077 : Blo 1949435 2195077 := bbase (se 4 (by rfl) ⟨205788, by rfl⟩ : syracuseStep 2195077 = 411577) (by norm_num)
theorem B2926769 : Blo 1949435 2926769 := bstep (se 2 (by rfl) ⟨1097538, by rfl⟩ : syracuseStep 2926769 = 2195077) B2195077
theorem B1951179 : Blo 1949435 1951179 := bstep (se 1 (by rfl) ⟨1463384, by rfl⟩ : syracuseStep 1951179 = 2926769) B2926769
theorem B7032197 : Blo 1949435 7032197 := bbase (se 4 (by rfl) ⟨659268, by rfl⟩ : syracuseStep 7032197 = 1318537) (by norm_num)
theorem B4688131 : Blo 1949435 4688131 := bstep (se 1 (by rfl) ⟨3516098, by rfl⟩ : syracuseStep 4688131 = 7032197) B7032197
theorem B6250841 : Blo 1949435 6250841 := bstep (se 2 (by rfl) ⟨2344065, by rfl⟩ : syracuseStep 6250841 = 4688131) B4688131
theorem B4167227 : Blo 1949435 4167227 := bstep (se 1 (by rfl) ⟨3125420, by rfl⟩ : syracuseStep 4167227 = 6250841) B6250841
theorem B2778151 : Blo 1949435 2778151 := bstep (se 1 (by rfl) ⟨2083613, by rfl⟩ : syracuseStep 2778151 = 4167227) B4167227
theorem B3704201 : Blo 1949435 3704201 := bstep (se 2 (by rfl) ⟨1389075, by rfl⟩ : syracuseStep 3704201 = 2778151) B2778151
theorem B2469467 : Blo 1949435 2469467 := bstep (se 1 (by rfl) ⟨1852100, by rfl⟩ : syracuseStep 2469467 = 3704201) B3704201
theorem B6585245 : Blo 1949435 6585245 := bstep (se 3 (by rfl) ⟨1234733, by rfl⟩ : syracuseStep 6585245 = 2469467) B2469467
theorem B4390163 : Blo 1949435 4390163 := bstep (se 1 (by rfl) ⟨3292622, by rfl⟩ : syracuseStep 4390163 = 6585245) B6585245
theorem B2926775 : Blo 1949435 2926775 := bstep (se 1 (by rfl) ⟨2195081, by rfl⟩ : syracuseStep 2926775 = 4390163) B4390163
theorem B1951183 : Blo 1949435 1951183 := bstep (se 1 (by rfl) ⟨1463387, by rfl⟩ : syracuseStep 1951183 = 2926775) B2926775
theorem B2926781 : Blo 1949435 2926781 := bbase (se 3 (by rfl) ⟨548771, by rfl⟩ : syracuseStep 2926781 = 1097543) (by norm_num)
theorem B1951187 : Blo 1949435 1951187 := bstep (se 1 (by rfl) ⟨1463390, by rfl⟩ : syracuseStep 1951187 = 2926781) B2926781
theorem B4390181 : Blo 1949435 4390181 := bbase (se 4 (by rfl) ⟨411579, by rfl⟩ : syracuseStep 4390181 = 823159) (by norm_num)
theorem B2926787 : Blo 1949435 2926787 := bstep (se 1 (by rfl) ⟨2195090, by rfl⟩ : syracuseStep 2926787 = 4390181) B4390181
theorem B1951191 : Blo 1949435 1951191 := bstep (se 1 (by rfl) ⟨1463393, by rfl⟩ : syracuseStep 1951191 = 2926787) B2926787
theorem B4938965 : Blo 1949435 4938965 := bbase (se 7 (by rfl) ⟨57878, by rfl⟩ : syracuseStep 4938965 = 115757) (by norm_num)
theorem B3292643 : Blo 1949435 3292643 := bstep (se 1 (by rfl) ⟨2469482, by rfl⟩ : syracuseStep 3292643 = 4938965) B4938965
theorem B2195095 : Blo 1949435 2195095 := bstep (se 1 (by rfl) ⟨1646321, by rfl⟩ : syracuseStep 2195095 = 3292643) B3292643
theorem B2926793 : Blo 1949435 2926793 := bstep (se 2 (by rfl) ⟨1097547, by rfl⟩ : syracuseStep 2926793 = 2195095) B2195095
theorem B1951195 : Blo 1949435 1951195 := bstep (se 1 (by rfl) ⟨1463396, by rfl⟩ : syracuseStep 1951195 = 2926793) B2926793
theorem B2503181 : Blo 1949435 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B6675149 : Blo 1949435 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B4450099 : Blo 1949435 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B5933465 : Blo 1949435 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B3955643 : Blo 1949435 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B2637095 : Blo 1949435 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B7032253 : Blo 1949435 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B9376337 : Blo 1949435 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B6250891 : Blo 1949435 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B8334521 : Blo 1949435 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B5556347 : Blo 1949435 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B3704231 : Blo 1949435 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B9877949 : Blo 1949435 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B6585299 : Blo 1949435 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B4390199 : Blo 1949435 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B2926799 : Blo 1949435 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B1951199 : Blo 1949435 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B2926805 : Blo 1949435 2926805 := bbase (se 7 (by rfl) ⟨34298, by rfl⟩ : syracuseStep 2926805 = 68597) (by norm_num)
theorem B1951203 : Blo 1949435 1951203 := bstep (se 1 (by rfl) ⟨1463402, by rfl⟩ : syracuseStep 1951203 = 2926805) B2926805
theorem B4688189 : Blo 1949435 4688189 := bbase (se 3 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 4688189 = 1758071) (by norm_num)
theorem B3125459 : Blo 1949435 3125459 := bstep (se 1 (by rfl) ⟨2344094, by rfl⟩ : syracuseStep 3125459 = 4688189) B4688189
theorem B2083639 : Blo 1949435 2083639 := bstep (se 1 (by rfl) ⟨1562729, by rfl⟩ : syracuseStep 2083639 = 3125459) B3125459
theorem B2778185 : Blo 1949435 2778185 := bstep (se 2 (by rfl) ⟨1041819, by rfl⟩ : syracuseStep 2778185 = 2083639) B2083639
theorem B7408493 : Blo 1949435 7408493 := bstep (se 3 (by rfl) ⟨1389092, by rfl⟩ : syracuseStep 7408493 = 2778185) B2778185
theorem B4938995 : Blo 1949435 4938995 := bstep (se 1 (by rfl) ⟨3704246, by rfl⟩ : syracuseStep 4938995 = 7408493) B7408493
theorem B3292663 : Blo 1949435 3292663 := bstep (se 1 (by rfl) ⟨2469497, by rfl⟩ : syracuseStep 3292663 = 4938995) B4938995
theorem B4390217 : Blo 1949435 4390217 := bstep (se 2 (by rfl) ⟨1646331, by rfl⟩ : syracuseStep 4390217 = 3292663) B3292663
theorem B2926811 : Blo 1949435 2926811 := bstep (se 1 (by rfl) ⟨2195108, by rfl⟩ : syracuseStep 2926811 = 4390217) B4390217
theorem B1951207 : Blo 1949435 1951207 := bstep (se 1 (by rfl) ⟨1463405, by rfl⟩ : syracuseStep 1951207 = 2926811) B2926811
theorem B2195113 : Blo 1949435 2195113 := bbase (se 2 (by rfl) ⟨823167, by rfl⟩ : syracuseStep 2195113 = 1646335) (by norm_num)
theorem B2926817 : Blo 1949435 2926817 := bstep (se 2 (by rfl) ⟨1097556, by rfl⟩ : syracuseStep 2926817 = 2195113) B2195113
theorem B1951211 : Blo 1949435 1951211 := bstep (se 1 (by rfl) ⟨1463408, by rfl⟩ : syracuseStep 1951211 = 2926817) B2926817
theorem B10012805 : Blo 1949435 10012805 := bbase (se 4 (by rfl) ⟨938700, by rfl⟩ : syracuseStep 10012805 = 1877401) (by norm_num)
theorem B6675203 : Blo 1949435 6675203 := bstep (se 1 (by rfl) ⟨5006402, by rfl⟩ : syracuseStep 6675203 = 10012805) B10012805
theorem B4450135 : Blo 1949435 4450135 := bstep (se 1 (by rfl) ⟨3337601, by rfl⟩ : syracuseStep 4450135 = 6675203) B6675203
theorem B5933513 : Blo 1949435 5933513 := bstep (se 2 (by rfl) ⟨2225067, by rfl⟩ : syracuseStep 5933513 = 4450135) B4450135
theorem B15822701 : Blo 1949435 15822701 := bstep (se 3 (by rfl) ⟨2966756, by rfl⟩ : syracuseStep 15822701 = 5933513) B5933513
theorem B10548467 : Blo 1949435 10548467 := bstep (se 1 (by rfl) ⟨7911350, by rfl⟩ : syracuseStep 10548467 = 15822701) B15822701
theorem B7032311 : Blo 1949435 7032311 := bstep (se 1 (by rfl) ⟨5274233, by rfl⟩ : syracuseStep 7032311 = 10548467) B10548467
theorem B4688207 : Blo 1949435 4688207 := bstep (se 1 (by rfl) ⟨3516155, by rfl⟩ : syracuseStep 4688207 = 7032311) B7032311
theorem B3125471 : Blo 1949435 3125471 := bstep (se 1 (by rfl) ⟨2344103, by rfl⟩ : syracuseStep 3125471 = 4688207) B4688207
theorem B8334589 : Blo 1949435 8334589 := bstep (se 3 (by rfl) ⟨1562735, by rfl⟩ : syracuseStep 8334589 = 3125471) B3125471
theorem B11112785 : Blo 1949435 11112785 := bstep (se 2 (by rfl) ⟨4167294, by rfl⟩ : syracuseStep 11112785 = 8334589) B8334589
theorem B7408523 : Blo 1949435 7408523 := bstep (se 1 (by rfl) ⟨5556392, by rfl⟩ : syracuseStep 7408523 = 11112785) B11112785
theorem B4939015 : Blo 1949435 4939015 := bstep (se 1 (by rfl) ⟨3704261, by rfl⟩ : syracuseStep 4939015 = 7408523) B7408523
theorem B6585353 : Blo 1949435 6585353 := bstep (se 2 (by rfl) ⟨2469507, by rfl⟩ : syracuseStep 6585353 = 4939015) B4939015
theorem B4390235 : Blo 1949435 4390235 := bstep (se 1 (by rfl) ⟨3292676, by rfl⟩ : syracuseStep 4390235 = 6585353) B6585353
theorem B2926823 : Blo 1949435 2926823 := bstep (se 1 (by rfl) ⟨2195117, by rfl⟩ : syracuseStep 2926823 = 4390235) B4390235
theorem B1951215 : Blo 1949435 1951215 := bstep (se 1 (by rfl) ⟨1463411, by rfl⟩ : syracuseStep 1951215 = 2926823) B2926823
theorem B2926829 : Blo 1949435 2926829 := bbase (se 3 (by rfl) ⟨548780, by rfl⟩ : syracuseStep 2926829 = 1097561) (by norm_num)
theorem B1951219 : Blo 1949435 1951219 := bstep (se 1 (by rfl) ⟨1463414, by rfl⟩ : syracuseStep 1951219 = 2926829) B2926829
theorem B4390253 : Blo 1949435 4390253 := bbase (se 3 (by rfl) ⟨823172, by rfl⟩ : syracuseStep 4390253 = 1646345) (by norm_num)
theorem B2926835 : Blo 1949435 2926835 := bstep (se 1 (by rfl) ⟨2195126, by rfl⟩ : syracuseStep 2926835 = 4390253) B4390253
theorem B1951223 : Blo 1949435 1951223 := bstep (se 1 (by rfl) ⟨1463417, by rfl⟩ : syracuseStep 1951223 = 2926835) B2926835
theorem B3704285 : Blo 1949435 3704285 := bbase (se 3 (by rfl) ⟨694553, by rfl⟩ : syracuseStep 3704285 = 1389107) (by norm_num)
theorem B2469523 : Blo 1949435 2469523 := bstep (se 1 (by rfl) ⟨1852142, by rfl⟩ : syracuseStep 2469523 = 3704285) B3704285
theorem B3292697 : Blo 1949435 3292697 := bstep (se 2 (by rfl) ⟨1234761, by rfl⟩ : syracuseStep 3292697 = 2469523) B2469523
theorem B2195131 : Blo 1949435 2195131 := bstep (se 1 (by rfl) ⟨1646348, by rfl⟩ : syracuseStep 2195131 = 3292697) B3292697
theorem B2926841 : Blo 1949435 2926841 := bstep (se 2 (by rfl) ⟨1097565, by rfl⟩ : syracuseStep 2926841 = 2195131) B2195131
theorem B1951227 : Blo 1949435 1951227 := bstep (se 1 (by rfl) ⟨1463420, by rfl⟩ : syracuseStep 1951227 = 2926841) B2926841
theorem B3383165 : Blo 1949435 3383165 := bbase (se 3 (by rfl) ⟨634343, by rfl⟩ : syracuseStep 3383165 = 1268687) (by norm_num)
theorem B9021773 : Blo 1949435 9021773 := bstep (se 3 (by rfl) ⟨1691582, by rfl⟩ : syracuseStep 9021773 = 3383165) B3383165
theorem B6014515 : Blo 1949435 6014515 := bstep (se 1 (by rfl) ⟨4510886, by rfl⟩ : syracuseStep 6014515 = 9021773) B9021773
theorem B8019353 : Blo 1949435 8019353 := bstep (se 2 (by rfl) ⟨3007257, by rfl⟩ : syracuseStep 8019353 = 6014515) B6014515
theorem B5346235 : Blo 1949435 5346235 := bstep (se 1 (by rfl) ⟨4009676, by rfl⟩ : syracuseStep 5346235 = 8019353) B8019353
theorem B7128313 : Blo 1949435 7128313 := bstep (se 2 (by rfl) ⟨2673117, by rfl⟩ : syracuseStep 7128313 = 5346235) B5346235
theorem B38017669 : Blo 1949435 38017669 := bstep (se 4 (by rfl) ⟨3564156, by rfl⟩ : syracuseStep 38017669 = 7128313) B7128313
theorem B50690225 : Blo 1949435 50690225 := bstep (se 2 (by rfl) ⟨19008834, by rfl⟩ : syracuseStep 50690225 = 38017669) B38017669
theorem B33793483 : Blo 1949435 33793483 := bstep (se 1 (by rfl) ⟨25345112, by rfl⟩ : syracuseStep 33793483 = 50690225) B50690225
theorem B45057977 : Blo 1949435 45057977 := bstep (se 2 (by rfl) ⟨16896741, by rfl⟩ : syracuseStep 45057977 = 33793483) B33793483
theorem B30038651 : Blo 1949435 30038651 := bstep (se 1 (by rfl) ⟨22528988, by rfl⟩ : syracuseStep 30038651 = 45057977) B45057977
theorem B20025767 : Blo 1949435 20025767 := bstep (se 1 (by rfl) ⟨15019325, by rfl⟩ : syracuseStep 20025767 = 30038651) B30038651
theorem B13350511 : Blo 1949435 13350511 := bstep (se 1 (by rfl) ⟨10012883, by rfl⟩ : syracuseStep 13350511 = 20025767) B20025767
theorem B17800681 : Blo 1949435 17800681 := bstep (se 2 (by rfl) ⟨6675255, by rfl⟩ : syracuseStep 17800681 = 13350511) B13350511
theorem B23734241 : Blo 1949435 23734241 := bstep (se 2 (by rfl) ⟨8900340, by rfl⟩ : syracuseStep 23734241 = 17800681) B17800681
theorem B15822827 : Blo 1949435 15822827 := bstep (se 1 (by rfl) ⟨11867120, by rfl⟩ : syracuseStep 15822827 = 23734241) B23734241
theorem B10548551 : Blo 1949435 10548551 := bstep (se 1 (by rfl) ⟨7911413, by rfl⟩ : syracuseStep 10548551 = 15822827) B15822827
theorem B7032367 : Blo 1949435 7032367 := bstep (se 1 (by rfl) ⟨5274275, by rfl⟩ : syracuseStep 7032367 = 10548551) B10548551
theorem B9376489 : Blo 1949435 9376489 := bstep (se 2 (by rfl) ⟨3516183, by rfl⟩ : syracuseStep 9376489 = 7032367) B7032367
theorem B50007941 : Blo 1949435 50007941 := bstep (se 4 (by rfl) ⟨4688244, by rfl⟩ : syracuseStep 50007941 = 9376489) B9376489
theorem B33338627 : Blo 1949435 33338627 := bstep (se 1 (by rfl) ⟨25003970, by rfl⟩ : syracuseStep 33338627 = 50007941) B50007941
theorem B22225751 : Blo 1949435 22225751 := bstep (se 1 (by rfl) ⟨16669313, by rfl⟩ : syracuseStep 22225751 = 33338627) B33338627
theorem B14817167 : Blo 1949435 14817167 := bstep (se 1 (by rfl) ⟨11112875, by rfl⟩ : syracuseStep 14817167 = 22225751) B22225751
theorem B9878111 : Blo 1949435 9878111 := bstep (se 1 (by rfl) ⟨7408583, by rfl⟩ : syracuseStep 9878111 = 14817167) B14817167
theorem B6585407 : Blo 1949435 6585407 := bstep (se 1 (by rfl) ⟨4939055, by rfl⟩ : syracuseStep 6585407 = 9878111) B9878111
theorem B4390271 : Blo 1949435 4390271 := bstep (se 1 (by rfl) ⟨3292703, by rfl⟩ : syracuseStep 4390271 = 6585407) B6585407
theorem B2926847 : Blo 1949435 2926847 := bstep (se 1 (by rfl) ⟨2195135, by rfl⟩ : syracuseStep 2926847 = 4390271) B4390271
theorem B1951231 : Blo 1949435 1951231 := bstep (se 1 (by rfl) ⟨1463423, by rfl⟩ : syracuseStep 1951231 = 2926847) B2926847
theorem B2926853 : Blo 1949435 2926853 := bbase (se 4 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 2926853 = 548785) (by norm_num)
theorem B1951235 : Blo 1949435 1951235 := bstep (se 1 (by rfl) ⟨1463426, by rfl⟩ : syracuseStep 1951235 = 2926853) B2926853
theorem B3292717 : Blo 1949435 3292717 := bbase (se 3 (by rfl) ⟨617384, by rfl⟩ : syracuseStep 3292717 = 1234769) (by norm_num)
theorem B4390289 : Blo 1949435 4390289 := bstep (se 2 (by rfl) ⟨1646358, by rfl⟩ : syracuseStep 4390289 = 3292717) B3292717
theorem B2926859 : Blo 1949435 2926859 := bstep (se 1 (by rfl) ⟨2195144, by rfl⟩ : syracuseStep 2926859 = 4390289) B4390289
theorem B1951239 : Blo 1949435 1951239 := bstep (se 1 (by rfl) ⟨1463429, by rfl⟩ : syracuseStep 1951239 = 2926859) B2926859
theorem B2195149 : Blo 1949435 2195149 := bbase (se 3 (by rfl) ⟨411590, by rfl⟩ : syracuseStep 2195149 = 823181) (by norm_num)
theorem B2926865 : Blo 1949435 2926865 := bstep (se 2 (by rfl) ⟨1097574, by rfl⟩ : syracuseStep 2926865 = 2195149) B2195149
theorem B1951243 : Blo 1949435 1951243 := bstep (se 1 (by rfl) ⟨1463432, by rfl⟩ : syracuseStep 1951243 = 2926865) B2926865
theorem B6585461 : Blo 1949435 6585461 := bbase (se 5 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 6585461 = 617387) (by norm_num)
theorem B4390307 : Blo 1949435 4390307 := bstep (se 1 (by rfl) ⟨3292730, by rfl⟩ : syracuseStep 4390307 = 6585461) B6585461
theorem B2926871 : Blo 1949435 2926871 := bstep (se 1 (by rfl) ⟨2195153, by rfl⟩ : syracuseStep 2926871 = 4390307) B4390307
theorem B1951247 : Blo 1949435 1951247 := bstep (se 1 (by rfl) ⟨1463435, by rfl⟩ : syracuseStep 1951247 = 2926871) B2926871
theorem B2926877 : Blo 1949435 2926877 := bbase (se 3 (by rfl) ⟨548789, by rfl⟩ : syracuseStep 2926877 = 1097579) (by norm_num)
theorem B1951251 : Blo 1949435 1951251 := bstep (se 1 (by rfl) ⟨1463438, by rfl⟩ : syracuseStep 1951251 = 2926877) B2926877
theorem B4390325 : Blo 1949435 4390325 := bbase (se 5 (by rfl) ⟨205796, by rfl⟩ : syracuseStep 4390325 = 411593) (by norm_num)
theorem B2926883 : Blo 1949435 2926883 := bstep (se 1 (by rfl) ⟨2195162, by rfl⟩ : syracuseStep 2926883 = 4390325) B4390325
theorem B1951255 : Blo 1949435 1951255 := bstep (se 1 (by rfl) ⟨1463441, by rfl⟩ : syracuseStep 1951255 = 2926883) B2926883
theorem B4167389 : Blo 1949435 4167389 := bbase (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) (by norm_num)
theorem B11113037 : Blo 1949435 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B7408691 : Blo 1949435 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B4939127 : Blo 1949435 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B3292751 : Blo 1949435 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B2195167 : Blo 1949435 2195167 := bstep (se 1 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 2195167 = 3292751) B3292751
theorem B2926889 : Blo 1949435 2926889 := bstep (se 2 (by rfl) ⟨1097583, by rfl⟩ : syracuseStep 2926889 = 2195167) B2195167
theorem B1951259 : Blo 1949435 1951259 := bstep (se 1 (by rfl) ⟨1463444, by rfl⟩ : syracuseStep 1951259 = 2926889) B2926889
theorem B4167397 : Blo 1949435 4167397 := bbase (se 4 (by rfl) ⟨390693, by rfl⟩ : syracuseStep 4167397 = 781387) (by norm_num)
theorem B5556529 : Blo 1949435 5556529 := bstep (se 2 (by rfl) ⟨2083698, by rfl⟩ : syracuseStep 5556529 = 4167397) B4167397
theorem B7408705 : Blo 1949435 7408705 := bstep (se 2 (by rfl) ⟨2778264, by rfl⟩ : syracuseStep 7408705 = 5556529) B5556529
theorem B9878273 : Blo 1949435 9878273 := bstep (se 2 (by rfl) ⟨3704352, by rfl⟩ : syracuseStep 9878273 = 7408705) B7408705
theorem B6585515 : Blo 1949435 6585515 := bstep (se 1 (by rfl) ⟨4939136, by rfl⟩ : syracuseStep 6585515 = 9878273) B9878273
theorem B4390343 : Blo 1949435 4390343 := bstep (se 1 (by rfl) ⟨3292757, by rfl⟩ : syracuseStep 4390343 = 6585515) B6585515
theorem B2926895 : Blo 1949435 2926895 := bstep (se 1 (by rfl) ⟨2195171, by rfl⟩ : syracuseStep 2926895 = 4390343) B4390343
theorem B1951263 : Blo 1949435 1951263 := bstep (se 1 (by rfl) ⟨1463447, by rfl⟩ : syracuseStep 1951263 = 2926895) B2926895
theorem B2926901 : Blo 1949435 2926901 := bbase (se 5 (by rfl) ⟨137198, by rfl⟩ : syracuseStep 2926901 = 274397) (by norm_num)
theorem B1951267 : Blo 1949435 1951267 := bstep (se 1 (by rfl) ⟨1463450, by rfl⟩ : syracuseStep 1951267 = 2926901) B2926901
theorem B4939157 : Blo 1949435 4939157 := bbase (se 6 (by rfl) ⟨115761, by rfl⟩ : syracuseStep 4939157 = 231523) (by norm_num)
theorem B3292771 : Blo 1949435 3292771 := bstep (se 1 (by rfl) ⟨2469578, by rfl⟩ : syracuseStep 3292771 = 4939157) B4939157
theorem B4390361 : Blo 1949435 4390361 := bstep (se 2 (by rfl) ⟨1646385, by rfl⟩ : syracuseStep 4390361 = 3292771) B3292771
theorem B2926907 : Blo 1949435 2926907 := bstep (se 1 (by rfl) ⟨2195180, by rfl⟩ : syracuseStep 2926907 = 4390361) B4390361
theorem B1951271 : Blo 1949435 1951271 := bstep (se 1 (by rfl) ⟨1463453, by rfl⟩ : syracuseStep 1951271 = 2926907) B2926907
theorem B2195185 : Blo 1949435 2195185 := bbase (se 2 (by rfl) ⟨823194, by rfl⟩ : syracuseStep 2195185 = 1646389) (by norm_num)
theorem B2926913 : Blo 1949435 2926913 := bstep (se 2 (by rfl) ⟨1097592, by rfl⟩ : syracuseStep 2926913 = 2195185) B2195185
theorem B1951275 : Blo 1949435 1951275 := bstep (se 1 (by rfl) ⟨1463456, by rfl⟩ : syracuseStep 1951275 = 2926913) B2926913
theorem B3955805 : Blo 1949435 3955805 := bbase (se 3 (by rfl) ⟨741713, by rfl⟩ : syracuseStep 3955805 = 1483427) (by norm_num)
theorem B2637203 : Blo 1949435 2637203 := bstep (se 1 (by rfl) ⟨1977902, by rfl⟩ : syracuseStep 2637203 = 3955805) B3955805
theorem B28130165 : Blo 1949435 28130165 := bstep (se 5 (by rfl) ⟨1318601, by rfl⟩ : syracuseStep 28130165 = 2637203) B2637203
theorem B18753443 : Blo 1949435 18753443 := bstep (se 1 (by rfl) ⟨14065082, by rfl⟩ : syracuseStep 18753443 = 28130165) B28130165
theorem B12502295 : Blo 1949435 12502295 := bstep (se 1 (by rfl) ⟨9376721, by rfl⟩ : syracuseStep 12502295 = 18753443) B18753443
theorem B8334863 : Blo 1949435 8334863 := bstep (se 1 (by rfl) ⟨6251147, by rfl⟩ : syracuseStep 8334863 = 12502295) B12502295
theorem B5556575 : Blo 1949435 5556575 := bstep (se 1 (by rfl) ⟨4167431, by rfl⟩ : syracuseStep 5556575 = 8334863) B8334863
theorem B3704383 : Blo 1949435 3704383 := bstep (se 1 (by rfl) ⟨2778287, by rfl⟩ : syracuseStep 3704383 = 5556575) B5556575
theorem B4939177 : Blo 1949435 4939177 := bstep (se 2 (by rfl) ⟨1852191, by rfl⟩ : syracuseStep 4939177 = 3704383) B3704383
theorem B6585569 : Blo 1949435 6585569 := bstep (se 2 (by rfl) ⟨2469588, by rfl⟩ : syracuseStep 6585569 = 4939177) B4939177
theorem B4390379 : Blo 1949435 4390379 := bstep (se 1 (by rfl) ⟨3292784, by rfl⟩ : syracuseStep 4390379 = 6585569) B6585569
theorem B2926919 : Blo 1949435 2926919 := bstep (se 1 (by rfl) ⟨2195189, by rfl⟩ : syracuseStep 2926919 = 4390379) B4390379
theorem B1951279 : Blo 1949435 1951279 := bstep (se 1 (by rfl) ⟨1463459, by rfl⟩ : syracuseStep 1951279 = 2926919) B2926919
theorem B2926925 : Blo 1949435 2926925 := bbase (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) (by norm_num)
theorem B1951283 : Blo 1949435 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B4390397 : Blo 1949435 4390397 := bbase (se 3 (by rfl) ⟨823199, by rfl⟩ : syracuseStep 4390397 = 1646399) (by norm_num)
theorem B2926931 : Blo 1949435 2926931 := bstep (se 1 (by rfl) ⟨2195198, by rfl⟩ : syracuseStep 2926931 = 4390397) B4390397
theorem B1951287 : Blo 1949435 1951287 := bstep (se 1 (by rfl) ⟨1463465, by rfl⟩ : syracuseStep 1951287 = 2926931) B2926931
theorem B3292805 : Blo 1949435 3292805 := bbase (se 4 (by rfl) ⟨308700, by rfl⟩ : syracuseStep 3292805 = 617401) (by norm_num)
theorem B2195203 : Blo 1949435 2195203 := bstep (se 1 (by rfl) ⟨1646402, by rfl⟩ : syracuseStep 2195203 = 3292805) B3292805
theorem B2926937 : Blo 1949435 2926937 := bstep (se 2 (by rfl) ⟨1097601, by rfl⟩ : syracuseStep 2926937 = 2195203) B2195203
theorem B1951291 : Blo 1949435 1951291 := bstep (se 1 (by rfl) ⟨1463468, by rfl⟩ : syracuseStep 1951291 = 2926937) B2926937
theorem B14817653 : Blo 1949435 14817653 := bbase (se 5 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 14817653 = 1389155) (by norm_num)
theorem B9878435 : Blo 1949435 9878435 := bstep (se 1 (by rfl) ⟨7408826, by rfl⟩ : syracuseStep 9878435 = 14817653) B14817653
theorem B6585623 : Blo 1949435 6585623 := bstep (se 1 (by rfl) ⟨4939217, by rfl⟩ : syracuseStep 6585623 = 9878435) B9878435
theorem B4390415 : Blo 1949435 4390415 := bstep (se 1 (by rfl) ⟨3292811, by rfl⟩ : syracuseStep 4390415 = 6585623) B6585623
theorem B2926943 : Blo 1949435 2926943 := bstep (se 1 (by rfl) ⟨2195207, by rfl⟩ : syracuseStep 2926943 = 4390415) B4390415
theorem B1951295 : Blo 1949435 1951295 := bstep (se 1 (by rfl) ⟨1463471, by rfl⟩ : syracuseStep 1951295 = 2926943) B2926943
theorem B2926949 : Blo 1949435 2926949 := bbase (se 4 (by rfl) ⟨274401, by rfl⟩ : syracuseStep 2926949 = 548803) (by norm_num)
theorem B1951299 : Blo 1949435 1951299 := bstep (se 1 (by rfl) ⟨1463474, by rfl⟩ : syracuseStep 1951299 = 2926949) B2926949
theorem B3704429 : Blo 1949435 3704429 := bbase (se 3 (by rfl) ⟨694580, by rfl⟩ : syracuseStep 3704429 = 1389161) (by norm_num)
theorem B2469619 : Blo 1949435 2469619 := bstep (se 1 (by rfl) ⟨1852214, by rfl⟩ : syracuseStep 2469619 = 3704429) B3704429
theorem B3292825 : Blo 1949435 3292825 := bstep (se 2 (by rfl) ⟨1234809, by rfl⟩ : syracuseStep 3292825 = 2469619) B2469619
theorem B4390433 : Blo 1949435 4390433 := bstep (se 2 (by rfl) ⟨1646412, by rfl⟩ : syracuseStep 4390433 = 3292825) B3292825
theorem B2926955 : Blo 1949435 2926955 := bstep (se 1 (by rfl) ⟨2195216, by rfl⟩ : syracuseStep 2926955 = 4390433) B4390433
theorem B1951303 : Blo 1949435 1951303 := bstep (se 1 (by rfl) ⟨1463477, by rfl⟩ : syracuseStep 1951303 = 2926955) B2926955
theorem B2195221 : Blo 1949435 2195221 := bbase (se 6 (by rfl) ⟨51450, by rfl⟩ : syracuseStep 2195221 = 102901) (by norm_num)
theorem B2926961 : Blo 1949435 2926961 := bstep (se 2 (by rfl) ⟨1097610, by rfl⟩ : syracuseStep 2926961 = 2195221) B2195221
theorem B1951307 : Blo 1949435 1951307 := bstep (se 1 (by rfl) ⟨1463480, by rfl⟩ : syracuseStep 1951307 = 2926961) B2926961
theorem B2469629 : Blo 1949435 2469629 := bbase (se 3 (by rfl) ⟨463055, by rfl⟩ : syracuseStep 2469629 = 926111) (by norm_num)
theorem B6585677 : Blo 1949435 6585677 := bstep (se 3 (by rfl) ⟨1234814, by rfl⟩ : syracuseStep 6585677 = 2469629) B2469629
theorem B4390451 : Blo 1949435 4390451 := bstep (se 1 (by rfl) ⟨3292838, by rfl⟩ : syracuseStep 4390451 = 6585677) B6585677
theorem B2926967 : Blo 1949435 2926967 := bstep (se 1 (by rfl) ⟨2195225, by rfl⟩ : syracuseStep 2926967 = 4390451) B4390451
theorem B1951311 : Blo 1949435 1951311 := bstep (se 1 (by rfl) ⟨1463483, by rfl⟩ : syracuseStep 1951311 = 2926967) B2926967
theorem B2926973 : Blo 1949435 2926973 := bbase (se 3 (by rfl) ⟨548807, by rfl⟩ : syracuseStep 2926973 = 1097615) (by norm_num)
theorem B1951315 : Blo 1949435 1951315 := bstep (se 1 (by rfl) ⟨1463486, by rfl⟩ : syracuseStep 1951315 = 2926973) B2926973
theorem B4390469 : Blo 1949435 4390469 := bbase (se 4 (by rfl) ⟨411606, by rfl⟩ : syracuseStep 4390469 = 823213) (by norm_num)
theorem B2926979 : Blo 1949435 2926979 := bstep (se 1 (by rfl) ⟨2195234, by rfl⟩ : syracuseStep 2926979 = 4390469) B4390469
theorem B1951319 : Blo 1949435 1951319 := bstep (se 1 (by rfl) ⟨1463489, by rfl⟩ : syracuseStep 1951319 = 2926979) B2926979
theorem B3125645 : Blo 1949435 3125645 := bbase (se 3 (by rfl) ⟨586058, by rfl⟩ : syracuseStep 3125645 = 1172117) (by norm_num)
theorem B2083763 : Blo 1949435 2083763 := bstep (se 1 (by rfl) ⟨1562822, by rfl⟩ : syracuseStep 2083763 = 3125645) B3125645
theorem B5556701 : Blo 1949435 5556701 := bstep (se 3 (by rfl) ⟨1041881, by rfl⟩ : syracuseStep 5556701 = 2083763) B2083763
theorem B3704467 : Blo 1949435 3704467 := bstep (se 1 (by rfl) ⟨2778350, by rfl⟩ : syracuseStep 3704467 = 5556701) B5556701
theorem B4939289 : Blo 1949435 4939289 := bstep (se 2 (by rfl) ⟨1852233, by rfl⟩ : syracuseStep 4939289 = 3704467) B3704467
theorem B3292859 : Blo 1949435 3292859 := bstep (se 1 (by rfl) ⟨2469644, by rfl⟩ : syracuseStep 3292859 = 4939289) B4939289
theorem B2195239 : Blo 1949435 2195239 := bstep (se 1 (by rfl) ⟨1646429, by rfl⟩ : syracuseStep 2195239 = 3292859) B3292859
theorem B2926985 : Blo 1949435 2926985 := bstep (se 2 (by rfl) ⟨1097619, by rfl⟩ : syracuseStep 2926985 = 2195239) B2195239
theorem B1951323 : Blo 1949435 1951323 := bstep (se 1 (by rfl) ⟨1463492, by rfl⟩ : syracuseStep 1951323 = 2926985) B2926985
theorem B9878597 : Blo 1949435 9878597 := bbase (se 4 (by rfl) ⟨926118, by rfl⟩ : syracuseStep 9878597 = 1852237) (by norm_num)
theorem B6585731 : Blo 1949435 6585731 := bstep (se 1 (by rfl) ⟨4939298, by rfl⟩ : syracuseStep 6585731 = 9878597) B9878597
theorem B4390487 : Blo 1949435 4390487 := bstep (se 1 (by rfl) ⟨3292865, by rfl⟩ : syracuseStep 4390487 = 6585731) B6585731
theorem B2926991 : Blo 1949435 2926991 := bstep (se 1 (by rfl) ⟨2195243, by rfl⟩ : syracuseStep 2926991 = 4390487) B4390487
theorem B1951327 : Blo 1949435 1951327 := bstep (se 1 (by rfl) ⟨1463495, by rfl⟩ : syracuseStep 1951327 = 2926991) B2926991
theorem B2926997 : Blo 1949435 2926997 := bbase (se 6 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 2926997 = 137203) (by norm_num)
theorem B1951331 : Blo 1949435 1951331 := bstep (se 1 (by rfl) ⟨1463498, by rfl⟩ : syracuseStep 1951331 = 2926997) B2926997
theorem B6014837 : Blo 1949435 6014837 := bbase (se 5 (by rfl) ⟨281945, by rfl⟩ : syracuseStep 6014837 = 563891) (by norm_num)
theorem B16039565 : Blo 1949435 16039565 := bstep (se 3 (by rfl) ⟨3007418, by rfl⟩ : syracuseStep 16039565 = 6014837) B6014837
theorem B10693043 : Blo 1949435 10693043 := bstep (se 1 (by rfl) ⟨8019782, by rfl⟩ : syracuseStep 10693043 = 16039565) B16039565
theorem B7128695 : Blo 1949435 7128695 := bstep (se 1 (by rfl) ⟨5346521, by rfl⟩ : syracuseStep 7128695 = 10693043) B10693043
theorem B19009853 : Blo 1949435 19009853 := bstep (se 3 (by rfl) ⟨3564347, by rfl⟩ : syracuseStep 19009853 = 7128695) B7128695
theorem B12673235 : Blo 1949435 12673235 := bstep (se 1 (by rfl) ⟨9504926, by rfl⟩ : syracuseStep 12673235 = 19009853) B19009853
theorem B8448823 : Blo 1949435 8448823 := bstep (se 1 (by rfl) ⟨6336617, by rfl⟩ : syracuseStep 8448823 = 12673235) B12673235
theorem B11265097 : Blo 1949435 11265097 := bstep (se 2 (by rfl) ⟨4224411, by rfl⟩ : syracuseStep 11265097 = 8448823) B8448823
theorem B15020129 : Blo 1949435 15020129 := bstep (se 2 (by rfl) ⟨5632548, by rfl⟩ : syracuseStep 15020129 = 11265097) B11265097
theorem B10013419 : Blo 1949435 10013419 := bstep (se 1 (by rfl) ⟨7510064, by rfl⟩ : syracuseStep 10013419 = 15020129) B15020129
theorem B13351225 : Blo 1949435 13351225 := bstep (se 2 (by rfl) ⟨5006709, by rfl⟩ : syracuseStep 13351225 = 10013419) B10013419
theorem B17801633 : Blo 1949435 17801633 := bstep (se 2 (by rfl) ⟨6675612, by rfl⟩ : syracuseStep 17801633 = 13351225) B13351225
theorem B47471021 : Blo 1949435 47471021 := bstep (se 3 (by rfl) ⟨8900816, by rfl⟩ : syracuseStep 47471021 = 17801633) B17801633
theorem B31647347 : Blo 1949435 31647347 := bstep (se 1 (by rfl) ⟨23735510, by rfl⟩ : syracuseStep 31647347 = 47471021) B47471021
theorem B21098231 : Blo 1949435 21098231 := bstep (se 1 (by rfl) ⟨15823673, by rfl⟩ : syracuseStep 21098231 = 31647347) B31647347
theorem B14065487 : Blo 1949435 14065487 := bstep (se 1 (by rfl) ⟨10549115, by rfl⟩ : syracuseStep 14065487 = 21098231) B21098231
theorem B9376991 : Blo 1949435 9376991 := bstep (se 1 (by rfl) ⟨7032743, by rfl⟩ : syracuseStep 9376991 = 14065487) B14065487
theorem B6251327 : Blo 1949435 6251327 := bstep (se 1 (by rfl) ⟨4688495, by rfl⟩ : syracuseStep 6251327 = 9376991) B9376991
theorem B4167551 : Blo 1949435 4167551 := bstep (se 1 (by rfl) ⟨3125663, by rfl⟩ : syracuseStep 4167551 = 6251327) B6251327
theorem B11113469 : Blo 1949435 11113469 := bstep (se 3 (by rfl) ⟨2083775, by rfl⟩ : syracuseStep 11113469 = 4167551) B4167551
theorem B7408979 : Blo 1949435 7408979 := bstep (se 1 (by rfl) ⟨5556734, by rfl⟩ : syracuseStep 7408979 = 11113469) B11113469
theorem B4939319 : Blo 1949435 4939319 := bstep (se 1 (by rfl) ⟨3704489, by rfl⟩ : syracuseStep 4939319 = 7408979) B7408979
theorem B3292879 : Blo 1949435 3292879 := bstep (se 1 (by rfl) ⟨2469659, by rfl⟩ : syracuseStep 3292879 = 4939319) B4939319
theorem B4390505 : Blo 1949435 4390505 := bstep (se 2 (by rfl) ⟨1646439, by rfl⟩ : syracuseStep 4390505 = 3292879) B3292879
theorem B2927003 : Blo 1949435 2927003 := bstep (se 1 (by rfl) ⟨2195252, by rfl⟩ : syracuseStep 2927003 = 4390505) B4390505
theorem B1951335 : Blo 1949435 1951335 := bstep (se 1 (by rfl) ⟨1463501, by rfl⟩ : syracuseStep 1951335 = 2927003) B2927003
theorem B2195257 : Blo 1949435 2195257 := bbase (se 2 (by rfl) ⟨823221, by rfl⟩ : syracuseStep 2195257 = 1646443) (by norm_num)
theorem B2927009 : Blo 1949435 2927009 := bstep (se 2 (by rfl) ⟨1097628, by rfl⟩ : syracuseStep 2927009 = 2195257) B2195257
theorem B1951339 : Blo 1949435 1951339 := bstep (se 1 (by rfl) ⟨1463504, by rfl⟩ : syracuseStep 1951339 = 2927009) B2927009
theorem B5556757 : Blo 1949435 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B7409009 : Blo 1949435 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B4939339 : Blo 1949435 4939339 := bstep (se 1 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 4939339 = 7409009) B7409009
theorem B6585785 : Blo 1949435 6585785 := bstep (se 2 (by rfl) ⟨2469669, by rfl⟩ : syracuseStep 6585785 = 4939339) B4939339
theorem B4390523 : Blo 1949435 4390523 := bstep (se 1 (by rfl) ⟨3292892, by rfl⟩ : syracuseStep 4390523 = 6585785) B6585785
theorem B2927015 : Blo 1949435 2927015 := bstep (se 1 (by rfl) ⟨2195261, by rfl⟩ : syracuseStep 2927015 = 4390523) B4390523
theorem B1951343 : Blo 1949435 1951343 := bstep (se 1 (by rfl) ⟨1463507, by rfl⟩ : syracuseStep 1951343 = 2927015) B2927015
theorem B2927021 : Blo 1949435 2927021 := bbase (se 3 (by rfl) ⟨548816, by rfl⟩ : syracuseStep 2927021 = 1097633) (by norm_num)
theorem B1951347 : Blo 1949435 1951347 := bstep (se 1 (by rfl) ⟨1463510, by rfl⟩ : syracuseStep 1951347 = 2927021) B2927021
theorem B4390541 : Blo 1949435 4390541 := bbase (se 3 (by rfl) ⟨823226, by rfl⟩ : syracuseStep 4390541 = 1646453) (by norm_num)
theorem B2927027 : Blo 1949435 2927027 := bstep (se 1 (by rfl) ⟨2195270, by rfl⟩ : syracuseStep 2927027 = 4390541) B4390541
theorem B1951351 : Blo 1949435 1951351 := bstep (se 1 (by rfl) ⟨1463513, by rfl⟩ : syracuseStep 1951351 = 2927027) B2927027
theorem B2469685 : Blo 1949435 2469685 := bbase (se 5 (by rfl) ⟨115766, by rfl⟩ : syracuseStep 2469685 = 231533) (by norm_num)
theorem B3292913 : Blo 1949435 3292913 := bstep (se 2 (by rfl) ⟨1234842, by rfl⟩ : syracuseStep 3292913 = 2469685) B2469685
theorem B2195275 : Blo 1949435 2195275 := bstep (se 1 (by rfl) ⟨1646456, by rfl⟩ : syracuseStep 2195275 = 3292913) B3292913
theorem B2927033 : Blo 1949435 2927033 := bstep (se 2 (by rfl) ⟨1097637, by rfl⟩ : syracuseStep 2927033 = 2195275) B2195275
theorem B1951355 : Blo 1949435 1951355 := bstep (se 1 (by rfl) ⟨1463516, by rfl⟩ : syracuseStep 1951355 = 2927033) B2927033
theorem B13718197 : Blo 1949435 13718197 := bbase (se 5 (by rfl) ⟨643040, by rfl⟩ : syracuseStep 13718197 = 1286081) (by norm_num)
theorem B18290929 : Blo 1949435 18290929 := bstep (se 2 (by rfl) ⟨6859098, by rfl⟩ : syracuseStep 18290929 = 13718197) B13718197
theorem B24387905 : Blo 1949435 24387905 := bstep (se 2 (by rfl) ⟨9145464, by rfl⟩ : syracuseStep 24387905 = 18290929) B18290929
theorem B16258603 : Blo 1949435 16258603 := bstep (se 1 (by rfl) ⟨12193952, by rfl⟩ : syracuseStep 16258603 = 24387905) B24387905
theorem B21678137 : Blo 1949435 21678137 := bstep (se 2 (by rfl) ⟨8129301, by rfl⟩ : syracuseStep 21678137 = 16258603) B16258603
theorem B14452091 : Blo 1949435 14452091 := bstep (se 1 (by rfl) ⟨10839068, by rfl⟩ : syracuseStep 14452091 = 21678137) B21678137
theorem B9634727 : Blo 1949435 9634727 := bstep (se 1 (by rfl) ⟨7226045, by rfl⟩ : syracuseStep 9634727 = 14452091) B14452091
theorem B6423151 : Blo 1949435 6423151 := bstep (se 1 (by rfl) ⟨4817363, by rfl⟩ : syracuseStep 6423151 = 9634727) B9634727
theorem B8564201 : Blo 1949435 8564201 := bstep (se 2 (by rfl) ⟨3211575, by rfl⟩ : syracuseStep 8564201 = 6423151) B6423151
theorem B5709467 : Blo 1949435 5709467 := bstep (se 1 (by rfl) ⟨4282100, by rfl⟩ : syracuseStep 5709467 = 8564201) B8564201
theorem B15225245 : Blo 1949435 15225245 := bstep (se 3 (by rfl) ⟨2854733, by rfl⟩ : syracuseStep 15225245 = 5709467) B5709467
theorem B10150163 : Blo 1949435 10150163 := bstep (se 1 (by rfl) ⟨7612622, by rfl⟩ : syracuseStep 10150163 = 15225245) B15225245
theorem B6766775 : Blo 1949435 6766775 := bstep (se 1 (by rfl) ⟨5075081, by rfl⟩ : syracuseStep 6766775 = 10150163) B10150163
theorem B4511183 : Blo 1949435 4511183 := bstep (se 1 (by rfl) ⟨3383387, by rfl⟩ : syracuseStep 4511183 = 6766775) B6766775
theorem B48119285 : Blo 1949435 48119285 := bstep (se 5 (by rfl) ⟨2255591, by rfl⟩ : syracuseStep 48119285 = 4511183) B4511183
theorem B128318093 : Blo 1949435 128318093 := bstep (se 3 (by rfl) ⟨24059642, by rfl⟩ : syracuseStep 128318093 = 48119285) B48119285
theorem B85545395 : Blo 1949435 85545395 := bstep (se 1 (by rfl) ⟨64159046, by rfl⟩ : syracuseStep 85545395 = 128318093) B128318093
theorem B57030263 : Blo 1949435 57030263 := bstep (se 1 (by rfl) ⟨42772697, by rfl⟩ : syracuseStep 57030263 = 85545395) B85545395
theorem B38020175 : Blo 1949435 38020175 := bstep (se 1 (by rfl) ⟨28515131, by rfl⟩ : syracuseStep 38020175 = 57030263) B57030263
theorem B25346783 : Blo 1949435 25346783 := bstep (se 1 (by rfl) ⟨19010087, by rfl⟩ : syracuseStep 25346783 = 38020175) B38020175
theorem B16897855 : Blo 1949435 16897855 := bstep (se 1 (by rfl) ⟨12673391, by rfl⟩ : syracuseStep 16897855 = 25346783) B25346783
theorem B22530473 : Blo 1949435 22530473 := bstep (se 2 (by rfl) ⟨8448927, by rfl⟩ : syracuseStep 22530473 = 16897855) B16897855
theorem B15020315 : Blo 1949435 15020315 := bstep (se 1 (by rfl) ⟨11265236, by rfl⟩ : syracuseStep 15020315 = 22530473) B22530473
theorem B10013543 : Blo 1949435 10013543 := bstep (se 1 (by rfl) ⟨7510157, by rfl⟩ : syracuseStep 10013543 = 15020315) B15020315
theorem B6675695 : Blo 1949435 6675695 := bstep (se 1 (by rfl) ⟨5006771, by rfl⟩ : syracuseStep 6675695 = 10013543) B10013543
theorem B4450463 : Blo 1949435 4450463 := bstep (se 1 (by rfl) ⟨3337847, by rfl⟩ : syracuseStep 4450463 = 6675695) B6675695
theorem B2966975 : Blo 1949435 2966975 := bstep (se 1 (by rfl) ⟨2225231, by rfl⟩ : syracuseStep 2966975 = 4450463) B4450463
theorem B1977983 : Blo 1949435 1977983 := bstep (se 1 (by rfl) ⟨1483487, by rfl⟩ : syracuseStep 1977983 = 2966975) B2966975
theorem B21098485 : Blo 1949435 21098485 := bstep (se 5 (by rfl) ⟨988991, by rfl⟩ : syracuseStep 21098485 = 1977983) B1977983
theorem B28131313 : Blo 1949435 28131313 := bstep (se 2 (by rfl) ⟨10549242, by rfl⟩ : syracuseStep 28131313 = 21098485) B21098485
theorem B37508417 : Blo 1949435 37508417 := bstep (se 2 (by rfl) ⟨14065656, by rfl⟩ : syracuseStep 37508417 = 28131313) B28131313
theorem B25005611 : Blo 1949435 25005611 := bstep (se 1 (by rfl) ⟨18754208, by rfl⟩ : syracuseStep 25005611 = 37508417) B37508417
theorem B16670407 : Blo 1949435 16670407 := bstep (se 1 (by rfl) ⟨12502805, by rfl⟩ : syracuseStep 16670407 = 25005611) B25005611
theorem B22227209 : Blo 1949435 22227209 := bstep (se 2 (by rfl) ⟨8335203, by rfl⟩ : syracuseStep 22227209 = 16670407) B16670407
theorem B14818139 : Blo 1949435 14818139 := bstep (se 1 (by rfl) ⟨11113604, by rfl⟩ : syracuseStep 14818139 = 22227209) B22227209
theorem B9878759 : Blo 1949435 9878759 := bstep (se 1 (by rfl) ⟨7409069, by rfl⟩ : syracuseStep 9878759 = 14818139) B14818139
theorem B6585839 : Blo 1949435 6585839 := bstep (se 1 (by rfl) ⟨4939379, by rfl⟩ : syracuseStep 6585839 = 9878759) B9878759
theorem B4390559 : Blo 1949435 4390559 := bstep (se 1 (by rfl) ⟨3292919, by rfl⟩ : syracuseStep 4390559 = 6585839) B6585839
theorem B2927039 : Blo 1949435 2927039 := bstep (se 1 (by rfl) ⟨2195279, by rfl⟩ : syracuseStep 2927039 = 4390559) B4390559
theorem B1951359 : Blo 1949435 1951359 := bstep (se 1 (by rfl) ⟨1463519, by rfl⟩ : syracuseStep 1951359 = 2927039) B2927039
theorem B2927045 : Blo 1949435 2927045 := bbase (se 4 (by rfl) ⟨274410, by rfl⟩ : syracuseStep 2927045 = 548821) (by norm_num)
theorem B1951363 : Blo 1949435 1951363 := bstep (se 1 (by rfl) ⟨1463522, by rfl⟩ : syracuseStep 1951363 = 2927045) B2927045
theorem B3292933 : Blo 1949435 3292933 := bbase (se 4 (by rfl) ⟨308712, by rfl⟩ : syracuseStep 3292933 = 617425) (by norm_num)
theorem B4390577 : Blo 1949435 4390577 := bstep (se 2 (by rfl) ⟨1646466, by rfl⟩ : syracuseStep 4390577 = 3292933) B3292933
theorem B2927051 : Blo 1949435 2927051 := bstep (se 1 (by rfl) ⟨2195288, by rfl⟩ : syracuseStep 2927051 = 4390577) B4390577
theorem B1951367 : Blo 1949435 1951367 := bstep (se 1 (by rfl) ⟨1463525, by rfl⟩ : syracuseStep 1951367 = 2927051) B2927051
theorem B2195293 : Blo 1949435 2195293 := bbase (se 3 (by rfl) ⟨411617, by rfl⟩ : syracuseStep 2195293 = 823235) (by norm_num)
theorem B2927057 : Blo 1949435 2927057 := bstep (se 2 (by rfl) ⟨1097646, by rfl⟩ : syracuseStep 2927057 = 2195293) B2195293
theorem B1951371 : Blo 1949435 1951371 := bstep (se 1 (by rfl) ⟨1463528, by rfl⟩ : syracuseStep 1951371 = 2927057) B2927057
theorem B6585893 : Blo 1949435 6585893 := bbase (se 4 (by rfl) ⟨617427, by rfl⟩ : syracuseStep 6585893 = 1234855) (by norm_num)
theorem B4390595 : Blo 1949435 4390595 := bstep (se 1 (by rfl) ⟨3292946, by rfl⟩ : syracuseStep 4390595 = 6585893) B6585893
theorem B2927063 : Blo 1949435 2927063 := bstep (se 1 (by rfl) ⟨2195297, by rfl⟩ : syracuseStep 2927063 = 4390595) B4390595
theorem B1951375 : Blo 1949435 1951375 := bstep (se 1 (by rfl) ⟨1463531, by rfl⟩ : syracuseStep 1951375 = 2927063) B2927063
theorem B2927069 : Blo 1949435 2927069 := bbase (se 3 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 2927069 = 1097651) (by norm_num)
theorem B1951379 : Blo 1949435 1951379 := bstep (se 1 (by rfl) ⟨1463534, by rfl⟩ : syracuseStep 1951379 = 2927069) B2927069
theorem B4390613 : Blo 1949435 4390613 := bbase (se 7 (by rfl) ⟨51452, by rfl⟩ : syracuseStep 4390613 = 102905) (by norm_num)
theorem B2927075 : Blo 1949435 2927075 := bstep (se 1 (by rfl) ⟨2195306, by rfl⟩ : syracuseStep 2927075 = 4390613) B4390613
theorem B1951383 : Blo 1949435 1951383 := bstep (se 1 (by rfl) ⟨1463537, by rfl⟩ : syracuseStep 1951383 = 2927075) B2927075
theorem B4688621 : Blo 1949435 4688621 := bbase (se 3 (by rfl) ⟨879116, by rfl⟩ : syracuseStep 4688621 = 1758233) (by norm_num)
theorem B3125747 : Blo 1949435 3125747 := bstep (se 1 (by rfl) ⟨2344310, by rfl⟩ : syracuseStep 3125747 = 4688621) B4688621
theorem B8335325 : Blo 1949435 8335325 := bstep (se 3 (by rfl) ⟨1562873, by rfl⟩ : syracuseStep 8335325 = 3125747) B3125747
theorem B5556883 : Blo 1949435 5556883 := bstep (se 1 (by rfl) ⟨4167662, by rfl⟩ : syracuseStep 5556883 = 8335325) B8335325
theorem B7409177 : Blo 1949435 7409177 := bstep (se 2 (by rfl) ⟨2778441, by rfl⟩ : syracuseStep 7409177 = 5556883) B5556883
theorem B4939451 : Blo 1949435 4939451 := bstep (se 1 (by rfl) ⟨3704588, by rfl⟩ : syracuseStep 4939451 = 7409177) B7409177
theorem B3292967 : Blo 1949435 3292967 := bstep (se 1 (by rfl) ⟨2469725, by rfl⟩ : syracuseStep 3292967 = 4939451) B4939451
theorem B2195311 : Blo 1949435 2195311 := bstep (se 1 (by rfl) ⟨1646483, by rfl⟩ : syracuseStep 2195311 = 3292967) B3292967
theorem B2927081 : Blo 1949435 2927081 := bstep (se 2 (by rfl) ⟨1097655, by rfl⟩ : syracuseStep 2927081 = 2195311) B2195311
theorem B1951387 : Blo 1949435 1951387 := bstep (se 1 (by rfl) ⟨1463540, by rfl⟩ : syracuseStep 1951387 = 2927081) B2927081
theorem B18754517 : Blo 1949435 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B12503011 : Blo 1949435 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B16670681 : Blo 1949435 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B11113787 : Blo 1949435 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B7409191 : Blo 1949435 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B9878921 : Blo 1949435 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B6585947 : Blo 1949435 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B4390631 : Blo 1949435 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B2927087 : Blo 1949435 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B1951391 : Blo 1949435 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B2927093 : Blo 1949435 2927093 := bbase (se 5 (by rfl) ⟨137207, by rfl⟩ : syracuseStep 2927093 = 274415) (by norm_num)
theorem B1951395 : Blo 1949435 1951395 := bstep (se 1 (by rfl) ⟨1463546, by rfl⟩ : syracuseStep 1951395 = 2927093) B2927093
theorem B5556917 : Blo 1949435 5556917 := bbase (se 5 (by rfl) ⟨260480, by rfl⟩ : syracuseStep 5556917 = 520961) (by norm_num)
theorem B3704611 : Blo 1949435 3704611 := bstep (se 1 (by rfl) ⟨2778458, by rfl⟩ : syracuseStep 3704611 = 5556917) B5556917
theorem B4939481 : Blo 1949435 4939481 := bstep (se 2 (by rfl) ⟨1852305, by rfl⟩ : syracuseStep 4939481 = 3704611) B3704611
theorem B3292987 : Blo 1949435 3292987 := bstep (se 1 (by rfl) ⟨2469740, by rfl⟩ : syracuseStep 3292987 = 4939481) B4939481
theorem B4390649 : Blo 1949435 4390649 := bstep (se 2 (by rfl) ⟨1646493, by rfl⟩ : syracuseStep 4390649 = 3292987) B3292987
theorem B2927099 : Blo 1949435 2927099 := bstep (se 1 (by rfl) ⟨2195324, by rfl⟩ : syracuseStep 2927099 = 4390649) B4390649
theorem B1951399 : Blo 1949435 1951399 := bstep (se 1 (by rfl) ⟨1463549, by rfl⟩ : syracuseStep 1951399 = 2927099) B2927099
theorem B2195329 : Blo 1949435 2195329 := bbase (se 2 (by rfl) ⟨823248, by rfl⟩ : syracuseStep 2195329 = 1646497) (by norm_num)
theorem B2927105 : Blo 1949435 2927105 := bstep (se 2 (by rfl) ⟨1097664, by rfl⟩ : syracuseStep 2927105 = 2195329) B2195329
theorem B1951403 : Blo 1949435 1951403 := bstep (se 1 (by rfl) ⟨1463552, by rfl⟩ : syracuseStep 1951403 = 2927105) B2927105
theorem B4939501 : Blo 1949435 4939501 := bbase (se 3 (by rfl) ⟨926156, by rfl⟩ : syracuseStep 4939501 = 1852313) (by norm_num)
theorem B6586001 : Blo 1949435 6586001 := bstep (se 2 (by rfl) ⟨2469750, by rfl⟩ : syracuseStep 6586001 = 4939501) B4939501
theorem B4390667 : Blo 1949435 4390667 := bstep (se 1 (by rfl) ⟨3293000, by rfl⟩ : syracuseStep 4390667 = 6586001) B6586001
theorem B2927111 : Blo 1949435 2927111 := bstep (se 1 (by rfl) ⟨2195333, by rfl⟩ : syracuseStep 2927111 = 4390667) B4390667
theorem B1951407 : Blo 1949435 1951407 := bstep (se 1 (by rfl) ⟨1463555, by rfl⟩ : syracuseStep 1951407 = 2927111) B2927111
theorem B2927117 : Blo 1949435 2927117 := bbase (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) (by norm_num)
theorem B1951411 : Blo 1949435 1951411 := bstep (se 1 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 1951411 = 2927117) B2927117
theorem B4390685 : Blo 1949435 4390685 := bbase (se 3 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 4390685 = 1646507) (by norm_num)
theorem B2927123 : Blo 1949435 2927123 := bstep (se 1 (by rfl) ⟨2195342, by rfl⟩ : syracuseStep 2927123 = 4390685) B4390685
theorem B1951415 : Blo 1949435 1951415 := bstep (se 1 (by rfl) ⟨1463561, by rfl⟩ : syracuseStep 1951415 = 2927123) B2927123
theorem B3293021 : Blo 1949435 3293021 := bbase (se 3 (by rfl) ⟨617441, by rfl⟩ : syracuseStep 3293021 = 1234883) (by norm_num)
theorem B2195347 : Blo 1949435 2195347 := bstep (se 1 (by rfl) ⟨1646510, by rfl⟩ : syracuseStep 2195347 = 3293021) B3293021
theorem B2927129 : Blo 1949435 2927129 := bstep (se 2 (by rfl) ⟨1097673, by rfl⟩ : syracuseStep 2927129 = 2195347) B2195347
theorem B1951419 : Blo 1949435 1951419 := bstep (se 1 (by rfl) ⟨1463564, by rfl⟩ : syracuseStep 1951419 = 2927129) B2927129
theorem B8335477 : Blo 1949435 8335477 := bbase (se 5 (by rfl) ⟨390725, by rfl⟩ : syracuseStep 8335477 = 781451) (by norm_num)
theorem B11113969 : Blo 1949435 11113969 := bstep (se 2 (by rfl) ⟨4167738, by rfl⟩ : syracuseStep 11113969 = 8335477) B8335477
theorem B14818625 : Blo 1949435 14818625 := bstep (se 2 (by rfl) ⟨5556984, by rfl⟩ : syracuseStep 14818625 = 11113969) B11113969
theorem B9879083 : Blo 1949435 9879083 := bstep (se 1 (by rfl) ⟨7409312, by rfl⟩ : syracuseStep 9879083 = 14818625) B14818625
theorem B6586055 : Blo 1949435 6586055 := bstep (se 1 (by rfl) ⟨4939541, by rfl⟩ : syracuseStep 6586055 = 9879083) B9879083
theorem B4390703 : Blo 1949435 4390703 := bstep (se 1 (by rfl) ⟨3293027, by rfl⟩ : syracuseStep 4390703 = 6586055) B6586055
theorem B2927135 : Blo 1949435 2927135 := bstep (se 1 (by rfl) ⟨2195351, by rfl⟩ : syracuseStep 2927135 = 4390703) B4390703
theorem B1951423 : Blo 1949435 1951423 := bstep (se 1 (by rfl) ⟨1463567, by rfl⟩ : syracuseStep 1951423 = 2927135) B2927135
theorem B2927141 : Blo 1949435 2927141 := bbase (se 4 (by rfl) ⟨274419, by rfl⟩ : syracuseStep 2927141 = 548839) (by norm_num)
theorem B1951427 : Blo 1949435 1951427 := bstep (se 1 (by rfl) ⟨1463570, by rfl⟩ : syracuseStep 1951427 = 2927141) B2927141
theorem B2469781 : Blo 1949435 2469781 := bbase (se 6 (by rfl) ⟨57885, by rfl⟩ : syracuseStep 2469781 = 115771) (by norm_num)
theorem B3293041 : Blo 1949435 3293041 := bstep (se 2 (by rfl) ⟨1234890, by rfl⟩ : syracuseStep 3293041 = 2469781) B2469781
theorem B4390721 : Blo 1949435 4390721 := bstep (se 2 (by rfl) ⟨1646520, by rfl⟩ : syracuseStep 4390721 = 3293041) B3293041
theorem B2927147 : Blo 1949435 2927147 := bstep (se 1 (by rfl) ⟨2195360, by rfl⟩ : syracuseStep 2927147 = 4390721) B4390721
theorem B1951431 : Blo 1949435 1951431 := bstep (se 1 (by rfl) ⟨1463573, by rfl⟩ : syracuseStep 1951431 = 2927147) B2927147
theorem B2195365 : Blo 1949435 2195365 := bbase (se 4 (by rfl) ⟨205815, by rfl⟩ : syracuseStep 2195365 = 411631) (by norm_num)
theorem B2927153 : Blo 1949435 2927153 := bstep (se 2 (by rfl) ⟨1097682, by rfl⟩ : syracuseStep 2927153 = 2195365) B2195365
theorem B1951435 : Blo 1949435 1951435 := bstep (se 1 (by rfl) ⟨1463576, by rfl⟩ : syracuseStep 1951435 = 2927153) B2927153
theorem C0 (j : ℕ) (h1 : 487358 ≤ j) (h2 : j ≤ 487858) : Blo 1949435 (4 * j + 3) := by
  interval_cases j
  · exact B1949435
  · exact B1949439
  · exact B1949443
  · exact B1949447
  · exact B1949451
  · exact B1949455
  · exact B1949459
  · exact B1949463
  · exact B1949467
  · exact B1949471
  · exact B1949475
  · exact B1949479
  · exact B1949483
  · exact B1949487
  · exact B1949491
  · exact B1949495
  · exact B1949499
  · exact B1949503
  · exact B1949507
  · exact B1949511
  · exact B1949515
  · exact B1949519
  · exact B1949523
  · exact B1949527
  · exact B1949531
  · exact B1949535
  · exact B1949539
  · exact B1949543
  · exact B1949547
  · exact B1949551
  · exact B1949555
  · exact B1949559
  · exact B1949563
  · exact B1949567
  · exact B1949571
  · exact B1949575
  · exact B1949579
  · exact B1949583
  · exact B1949587
  · exact B1949591
  · exact B1949595
  · exact B1949599
  · exact B1949603
  · exact B1949607
  · exact B1949611
  · exact B1949615
  · exact B1949619
  · exact B1949623
  · exact B1949627
  · exact B1949631
  · exact B1949635
  · exact B1949639
  · exact B1949643
  · exact B1949647
  · exact B1949651
  · exact B1949655
  · exact B1949659
  · exact B1949663
  · exact B1949667
  · exact B1949671
  · exact B1949675
  · exact B1949679
  · exact B1949683
  · exact B1949687
  · exact B1949691
  · exact B1949695
  · exact B1949699
  · exact B1949703
  · exact B1949707
  · exact B1949711
  · exact B1949715
  · exact B1949719
  · exact B1949723
  · exact B1949727
  · exact B1949731
  · exact B1949735
  · exact B1949739
  · exact B1949743
  · exact B1949747
  · exact B1949751
  · exact B1949755
  · exact B1949759
  · exact B1949763
  · exact B1949767
  · exact B1949771
  · exact B1949775
  · exact B1949779
  · exact B1949783
  · exact B1949787
  · exact B1949791
  · exact B1949795
  · exact B1949799
  · exact B1949803
  · exact B1949807
  · exact B1949811
  · exact B1949815
  · exact B1949819
  · exact B1949823
  · exact B1949827
  · exact B1949831
  · exact B1949835
  · exact B1949839
  · exact B1949843
  · exact B1949847
  · exact B1949851
  · exact B1949855
  · exact B1949859
  · exact B1949863
  · exact B1949867
  · exact B1949871
  · exact B1949875
  · exact B1949879
  · exact B1949883
  · exact B1949887
  · exact B1949891
  · exact B1949895
  · exact B1949899
  · exact B1949903
  · exact B1949907
  · exact B1949911
  · exact B1949915
  · exact B1949919
  · exact B1949923
  · exact B1949927
  · exact B1949931
  · exact B1949935
  · exact B1949939
  · exact B1949943
  · exact B1949947
  · exact B1949951
  · exact B1949955
  · exact B1949959
  · exact B1949963
  · exact B1949967
  · exact B1949971
  · exact B1949975
  · exact B1949979
  · exact B1949983
  · exact B1949987
  · exact B1949991
  · exact B1949995
  · exact B1949999
  · exact B1950003
  · exact B1950007
  · exact B1950011
  · exact B1950015
  · exact B1950019
  · exact B1950023
  · exact B1950027
  · exact B1950031
  · exact B1950035
  · exact B1950039
  · exact B1950043
  · exact B1950047
  · exact B1950051
  · exact B1950055
  · exact B1950059
  · exact B1950063
  · exact B1950067
  · exact B1950071
  · exact B1950075
  · exact B1950079
  · exact B1950083
  · exact B1950087
  · exact B1950091
  · exact B1950095
  · exact B1950099
  · exact B1950103
  · exact B1950107
  · exact B1950111
  · exact B1950115
  · exact B1950119
  · exact B1950123
  · exact B1950127
  · exact B1950131
  · exact B1950135
  · exact B1950139
  · exact B1950143
  · exact B1950147
  · exact B1950151
  · exact B1950155
  · exact B1950159
  · exact B1950163
  · exact B1950167
  · exact B1950171
  · exact B1950175
  · exact B1950179
  · exact B1950183
  · exact B1950187
  · exact B1950191
  · exact B1950195
  · exact B1950199
  · exact B1950203
  · exact B1950207
  · exact B1950211
  · exact B1950215
  · exact B1950219
  · exact B1950223
  · exact B1950227
  · exact B1950231
  · exact B1950235
  · exact B1950239
  · exact B1950243
  · exact B1950247
  · exact B1950251
  · exact B1950255
  · exact B1950259
  · exact B1950263
  · exact B1950267
  · exact B1950271
  · exact B1950275
  · exact B1950279
  · exact B1950283
  · exact B1950287
  · exact B1950291
  · exact B1950295
  · exact B1950299
  · exact B1950303
  · exact B1950307
  · exact B1950311
  · exact B1950315
  · exact B1950319
  · exact B1950323
  · exact B1950327
  · exact B1950331
  · exact B1950335
  · exact B1950339
  · exact B1950343
  · exact B1950347
  · exact B1950351
  · exact B1950355
  · exact B1950359
  · exact B1950363
  · exact B1950367
  · exact B1950371
  · exact B1950375
  · exact B1950379
  · exact B1950383
  · exact B1950387
  · exact B1950391
  · exact B1950395
  · exact B1950399
  · exact B1950403
  · exact B1950407
  · exact B1950411
  · exact B1950415
  · exact B1950419
  · exact B1950423
  · exact B1950427
  · exact B1950431
  · exact B1950435
  · exact B1950439
  · exact B1950443
  · exact B1950447
  · exact B1950451
  · exact B1950455
  · exact B1950459
  · exact B1950463
  · exact B1950467
  · exact B1950471
  · exact B1950475
  · exact B1950479
  · exact B1950483
  · exact B1950487
  · exact B1950491
  · exact B1950495
  · exact B1950499
  · exact B1950503
  · exact B1950507
  · exact B1950511
  · exact B1950515
  · exact B1950519
  · exact B1950523
  · exact B1950527
  · exact B1950531
  · exact B1950535
  · exact B1950539
  · exact B1950543
  · exact B1950547
  · exact B1950551
  · exact B1950555
  · exact B1950559
  · exact B1950563
  · exact B1950567
  · exact B1950571
  · exact B1950575
  · exact B1950579
  · exact B1950583
  · exact B1950587
  · exact B1950591
  · exact B1950595
  · exact B1950599
  · exact B1950603
  · exact B1950607
  · exact B1950611
  · exact B1950615
  · exact B1950619
  · exact B1950623
  · exact B1950627
  · exact B1950631
  · exact B1950635
  · exact B1950639
  · exact B1950643
  · exact B1950647
  · exact B1950651
  · exact B1950655
  · exact B1950659
  · exact B1950663
  · exact B1950667
  · exact B1950671
  · exact B1950675
  · exact B1950679
  · exact B1950683
  · exact B1950687
  · exact B1950691
  · exact B1950695
  · exact B1950699
  · exact B1950703
  · exact B1950707
  · exact B1950711
  · exact B1950715
  · exact B1950719
  · exact B1950723
  · exact B1950727
  · exact B1950731
  · exact B1950735
  · exact B1950739
  · exact B1950743
  · exact B1950747
  · exact B1950751
  · exact B1950755
  · exact B1950759
  · exact B1950763
  · exact B1950767
  · exact B1950771
  · exact B1950775
  · exact B1950779
  · exact B1950783
  · exact B1950787
  · exact B1950791
  · exact B1950795
  · exact B1950799
  · exact B1950803
  · exact B1950807
  · exact B1950811
  · exact B1950815
  · exact B1950819
  · exact B1950823
  · exact B1950827
  · exact B1950831
  · exact B1950835
  · exact B1950839
  · exact B1950843
  · exact B1950847
  · exact B1950851
  · exact B1950855
  · exact B1950859
  · exact B1950863
  · exact B1950867
  · exact B1950871
  · exact B1950875
  · exact B1950879
  · exact B1950883
  · exact B1950887
  · exact B1950891
  · exact B1950895
  · exact B1950899
  · exact B1950903
  · exact B1950907
  · exact B1950911
  · exact B1950915
  · exact B1950919
  · exact B1950923
  · exact B1950927
  · exact B1950931
  · exact B1950935
  · exact B1950939
  · exact B1950943
  · exact B1950947
  · exact B1950951
  · exact B1950955
  · exact B1950959
  · exact B1950963
  · exact B1950967
  · exact B1950971
  · exact B1950975
  · exact B1950979
  · exact B1950983
  · exact B1950987
  · exact B1950991
  · exact B1950995
  · exact B1950999
  · exact B1951003
  · exact B1951007
  · exact B1951011
  · exact B1951015
  · exact B1951019
  · exact B1951023
  · exact B1951027
  · exact B1951031
  · exact B1951035
  · exact B1951039
  · exact B1951043
  · exact B1951047
  · exact B1951051
  · exact B1951055
  · exact B1951059
  · exact B1951063
  · exact B1951067
  · exact B1951071
  · exact B1951075
  · exact B1951079
  · exact B1951083
  · exact B1951087
  · exact B1951091
  · exact B1951095
  · exact B1951099
  · exact B1951103
  · exact B1951107
  · exact B1951111
  · exact B1951115
  · exact B1951119
  · exact B1951123
  · exact B1951127
  · exact B1951131
  · exact B1951135
  · exact B1951139
  · exact B1951143
  · exact B1951147
  · exact B1951151
  · exact B1951155
  · exact B1951159
  · exact B1951163
  · exact B1951167
  · exact B1951171
  · exact B1951175
  · exact B1951179
  · exact B1951183
  · exact B1951187
  · exact B1951191
  · exact B1951195
  · exact B1951199
  · exact B1951203
  · exact B1951207
  · exact B1951211
  · exact B1951215
  · exact B1951219
  · exact B1951223
  · exact B1951227
  · exact B1951231
  · exact B1951235
  · exact B1951239
  · exact B1951243
  · exact B1951247
  · exact B1951251
  · exact B1951255
  · exact B1951259
  · exact B1951263
  · exact B1951267
  · exact B1951271
  · exact B1951275
  · exact B1951279
  · exact B1951283
  · exact B1951287
  · exact B1951291
  · exact B1951295
  · exact B1951299
  · exact B1951303
  · exact B1951307
  · exact B1951311
  · exact B1951315
  · exact B1951319
  · exact B1951323
  · exact B1951327
  · exact B1951331
  · exact B1951335
  · exact B1951339
  · exact B1951343
  · exact B1951347
  · exact B1951351
  · exact B1951355
  · exact B1951359
  · exact B1951363
  · exact B1951367
  · exact B1951371
  · exact B1951375
  · exact B1951379
  · exact B1951383
  · exact B1951387
  · exact B1951391
  · exact B1951395
  · exact B1951399
  · exact B1951403
  · exact B1951407
  · exact B1951411
  · exact B1951415
  · exact B1951419
  · exact B1951423
  · exact B1951427
  · exact B1951431
  · exact B1951435
theorem solution (m : ℕ) (hlo : 1949435 ≤ m) (hhi : m ≤ 1951435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 487358 ≤ j := by omega
    have hj2 : j ≤ 487858 := by omega
    have hb : Blo 1949435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
