-- Prove2me | solution 1 for syracuse_descends_range_2101435_2103435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:35.796977+00:00
-- url     : https://prove2.me/submissions/2e6519b5-3c36-4581-aca0-357304ff153e

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

theorem B3546173 : Blo 2101435 3546173 := bbase (se 3 (by rfl) ⟨664907, by rfl⟩ : syracuseStep 3546173 = 1329815) (by norm_num)
theorem B2364115 : Blo 2101435 2364115 := bstep (se 1 (by rfl) ⟨1773086, by rfl⟩ : syracuseStep 2364115 = 3546173) B3546173
theorem B3152153 : Blo 2101435 3152153 := bstep (se 2 (by rfl) ⟨1182057, by rfl⟩ : syracuseStep 3152153 = 2364115) B2364115
theorem B2101435 : Blo 2101435 2101435 := bstep (se 1 (by rfl) ⟨1576076, by rfl⟩ : syracuseStep 2101435 = 3152153) B3152153
theorem B3366101 : Blo 2101435 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B2244067 : Blo 2101435 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B11968357 : Blo 2101435 11968357 := bstep (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) B2244067
theorem B15957809 : Blo 2101435 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B10638539 : Blo 2101435 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B7092359 : Blo 2101435 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B4728239 : Blo 2101435 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B3152159 : Blo 2101435 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B2101439 : Blo 2101435 2101439 := bstep (se 1 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 2101439 = 3152159) B3152159
theorem B3152165 : Blo 2101435 3152165 := bbase (se 4 (by rfl) ⟨295515, by rfl⟩ : syracuseStep 3152165 = 591031) (by norm_num)
theorem B2101443 : Blo 2101435 2101443 := bstep (se 1 (by rfl) ⟨1576082, by rfl⟩ : syracuseStep 2101443 = 3152165) B3152165
theorem B2659645 : Blo 2101435 2659645 := bbase (se 3 (by rfl) ⟨498683, by rfl⟩ : syracuseStep 2659645 = 997367) (by norm_num)
theorem B3546193 : Blo 2101435 3546193 := bstep (se 2 (by rfl) ⟨1329822, by rfl⟩ : syracuseStep 3546193 = 2659645) B2659645
theorem B4728257 : Blo 2101435 4728257 := bstep (se 2 (by rfl) ⟨1773096, by rfl⟩ : syracuseStep 4728257 = 3546193) B3546193
theorem B3152171 : Blo 2101435 3152171 := bstep (se 1 (by rfl) ⟨2364128, by rfl⟩ : syracuseStep 3152171 = 4728257) B4728257
theorem B2101447 : Blo 2101435 2101447 := bstep (se 1 (by rfl) ⟨1576085, by rfl⟩ : syracuseStep 2101447 = 3152171) B3152171
theorem B2364133 : Blo 2101435 2364133 := bbase (se 4 (by rfl) ⟨221637, by rfl⟩ : syracuseStep 2364133 = 443275) (by norm_num)
theorem B3152177 : Blo 2101435 3152177 := bstep (se 2 (by rfl) ⟨1182066, by rfl⟩ : syracuseStep 3152177 = 2364133) B2364133
theorem B2101451 : Blo 2101435 2101451 := bstep (se 1 (by rfl) ⟨1576088, by rfl⟩ : syracuseStep 2101451 = 3152177) B3152177
theorem B13648213 : Blo 2101435 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B18197617 : Blo 2101435 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B24263489 : Blo 2101435 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B64702637 : Blo 2101435 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B43135091 : Blo 2101435 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B28756727 : Blo 2101435 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B19171151 : Blo 2101435 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B12780767 : Blo 2101435 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B8520511 : Blo 2101435 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B11360681 : Blo 2101435 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B7573787 : Blo 2101435 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B5049191 : Blo 2101435 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B3366127 : Blo 2101435 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B4488169 : Blo 2101435 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B5984225 : Blo 2101435 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B3989483 : Blo 2101435 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B2659655 : Blo 2101435 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B7092413 : Blo 2101435 7092413 := bstep (se 3 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 7092413 = 2659655) B2659655
theorem B4728275 : Blo 2101435 4728275 := bstep (se 1 (by rfl) ⟨3546206, by rfl⟩ : syracuseStep 4728275 = 7092413) B7092413
theorem B3152183 : Blo 2101435 3152183 := bstep (se 1 (by rfl) ⟨2364137, by rfl⟩ : syracuseStep 3152183 = 4728275) B4728275
theorem B2101455 : Blo 2101435 2101455 := bstep (se 1 (by rfl) ⟨1576091, by rfl⟩ : syracuseStep 2101455 = 3152183) B3152183
theorem B3152189 : Blo 2101435 3152189 := bbase (se 3 (by rfl) ⟨591035, by rfl⟩ : syracuseStep 3152189 = 1182071) (by norm_num)
theorem B2101459 : Blo 2101435 2101459 := bstep (se 1 (by rfl) ⟨1576094, by rfl⟩ : syracuseStep 2101459 = 3152189) B3152189
theorem B4728293 : Blo 2101435 4728293 := bbase (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) (by norm_num)
theorem B3152195 : Blo 2101435 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B2101463 : Blo 2101435 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B5319341 : Blo 2101435 5319341 := bbase (se 3 (by rfl) ⟨997376, by rfl⟩ : syracuseStep 5319341 = 1994753) (by norm_num)
theorem B3546227 : Blo 2101435 3546227 := bstep (se 1 (by rfl) ⟨2659670, by rfl⟩ : syracuseStep 3546227 = 5319341) B5319341
theorem B2364151 : Blo 2101435 2364151 := bstep (se 1 (by rfl) ⟨1773113, by rfl⟩ : syracuseStep 2364151 = 3546227) B3546227
theorem B3152201 : Blo 2101435 3152201 := bstep (se 2 (by rfl) ⟨1182075, by rfl⟩ : syracuseStep 3152201 = 2364151) B2364151
theorem B2101467 : Blo 2101435 2101467 := bstep (se 1 (by rfl) ⟨1576100, by rfl⟩ : syracuseStep 2101467 = 3152201) B3152201
theorem B5049229 : Blo 2101435 5049229 := bbase (se 3 (by rfl) ⟨946730, by rfl⟩ : syracuseStep 5049229 = 1893461) (by norm_num)
theorem B6732305 : Blo 2101435 6732305 := bstep (se 2 (by rfl) ⟨2524614, by rfl⟩ : syracuseStep 6732305 = 5049229) B5049229
theorem B4488203 : Blo 2101435 4488203 := bstep (se 1 (by rfl) ⟨3366152, by rfl⟩ : syracuseStep 4488203 = 6732305) B6732305
theorem B2992135 : Blo 2101435 2992135 := bstep (se 1 (by rfl) ⟨2244101, by rfl⟩ : syracuseStep 2992135 = 4488203) B4488203
theorem B3989513 : Blo 2101435 3989513 := bstep (se 2 (by rfl) ⟨1496067, by rfl⟩ : syracuseStep 3989513 = 2992135) B2992135
theorem B10638701 : Blo 2101435 10638701 := bstep (se 3 (by rfl) ⟨1994756, by rfl⟩ : syracuseStep 10638701 = 3989513) B3989513
theorem B7092467 : Blo 2101435 7092467 := bstep (se 1 (by rfl) ⟨5319350, by rfl⟩ : syracuseStep 7092467 = 10638701) B10638701
theorem B4728311 : Blo 2101435 4728311 := bstep (se 1 (by rfl) ⟨3546233, by rfl⟩ : syracuseStep 4728311 = 7092467) B7092467
theorem B3152207 : Blo 2101435 3152207 := bstep (se 1 (by rfl) ⟨2364155, by rfl⟩ : syracuseStep 3152207 = 4728311) B4728311
theorem B2101471 : Blo 2101435 2101471 := bstep (se 1 (by rfl) ⟨1576103, by rfl⟩ : syracuseStep 2101471 = 3152207) B3152207
theorem B3152213 : Blo 2101435 3152213 := bbase (se 10 (by rfl) ⟨4617, by rfl⟩ : syracuseStep 3152213 = 9235) (by norm_num)
theorem B2101475 : Blo 2101435 2101475 := bstep (se 1 (by rfl) ⟨1576106, by rfl⟩ : syracuseStep 2101475 = 3152213) B3152213
theorem B5984293 : Blo 2101435 5984293 := bbase (se 4 (by rfl) ⟨561027, by rfl⟩ : syracuseStep 5984293 = 1122055) (by norm_num)
theorem B7979057 : Blo 2101435 7979057 := bstep (se 2 (by rfl) ⟨2992146, by rfl⟩ : syracuseStep 7979057 = 5984293) B5984293
theorem B5319371 : Blo 2101435 5319371 := bstep (se 1 (by rfl) ⟨3989528, by rfl⟩ : syracuseStep 5319371 = 7979057) B7979057
theorem B3546247 : Blo 2101435 3546247 := bstep (se 1 (by rfl) ⟨2659685, by rfl⟩ : syracuseStep 3546247 = 5319371) B5319371
theorem B4728329 : Blo 2101435 4728329 := bstep (se 2 (by rfl) ⟨1773123, by rfl⟩ : syracuseStep 4728329 = 3546247) B3546247
theorem B3152219 : Blo 2101435 3152219 := bstep (se 1 (by rfl) ⟨2364164, by rfl⟩ : syracuseStep 3152219 = 4728329) B4728329
theorem B2101479 : Blo 2101435 2101479 := bstep (se 1 (by rfl) ⟨1576109, by rfl⟩ : syracuseStep 2101479 = 3152219) B3152219
theorem B2364169 : Blo 2101435 2364169 := bbase (se 2 (by rfl) ⟨886563, by rfl⟩ : syracuseStep 2364169 = 1773127) (by norm_num)
theorem B3152225 : Blo 2101435 3152225 := bstep (se 2 (by rfl) ⟨1182084, by rfl⟩ : syracuseStep 3152225 = 2364169) B2364169
theorem B2101483 : Blo 2101435 2101483 := bstep (se 1 (by rfl) ⟨1576112, by rfl⟩ : syracuseStep 2101483 = 3152225) B3152225
theorem B10098533 : Blo 2101435 10098533 := bbase (se 4 (by rfl) ⟨946737, by rfl⟩ : syracuseStep 10098533 = 1893475) (by norm_num)
theorem B26929421 : Blo 2101435 26929421 := bstep (se 3 (by rfl) ⟨5049266, by rfl⟩ : syracuseStep 26929421 = 10098533) B10098533
theorem B17952947 : Blo 2101435 17952947 := bstep (se 1 (by rfl) ⟨13464710, by rfl⟩ : syracuseStep 17952947 = 26929421) B26929421
theorem B11968631 : Blo 2101435 11968631 := bstep (se 1 (by rfl) ⟨8976473, by rfl⟩ : syracuseStep 11968631 = 17952947) B17952947
theorem B7979087 : Blo 2101435 7979087 := bstep (se 1 (by rfl) ⟨5984315, by rfl⟩ : syracuseStep 7979087 = 11968631) B11968631
theorem B5319391 : Blo 2101435 5319391 := bstep (se 1 (by rfl) ⟨3989543, by rfl⟩ : syracuseStep 5319391 = 7979087) B7979087
theorem B7092521 : Blo 2101435 7092521 := bstep (se 2 (by rfl) ⟨2659695, by rfl⟩ : syracuseStep 7092521 = 5319391) B5319391
theorem B4728347 : Blo 2101435 4728347 := bstep (se 1 (by rfl) ⟨3546260, by rfl⟩ : syracuseStep 4728347 = 7092521) B7092521
theorem B3152231 : Blo 2101435 3152231 := bstep (se 1 (by rfl) ⟨2364173, by rfl⟩ : syracuseStep 3152231 = 4728347) B4728347
theorem B2101487 : Blo 2101435 2101487 := bstep (se 1 (by rfl) ⟨1576115, by rfl⟩ : syracuseStep 2101487 = 3152231) B3152231
theorem B3152237 : Blo 2101435 3152237 := bbase (se 3 (by rfl) ⟨591044, by rfl⟩ : syracuseStep 3152237 = 1182089) (by norm_num)
theorem B2101491 : Blo 2101435 2101491 := bstep (se 1 (by rfl) ⟨1576118, by rfl⟩ : syracuseStep 2101491 = 3152237) B3152237
theorem B4728365 : Blo 2101435 4728365 := bbase (se 3 (by rfl) ⟨886568, by rfl⟩ : syracuseStep 4728365 = 1773137) (by norm_num)
theorem B3152243 : Blo 2101435 3152243 := bstep (se 1 (by rfl) ⟨2364182, by rfl⟩ : syracuseStep 3152243 = 4728365) B4728365
theorem B2101495 : Blo 2101435 2101495 := bstep (se 1 (by rfl) ⟨1576121, by rfl⟩ : syracuseStep 2101495 = 3152243) B3152243
theorem B6390517 : Blo 2101435 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B8520689 : Blo 2101435 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B5680459 : Blo 2101435 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B30295781 : Blo 2101435 30295781 := bstep (se 4 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 30295781 = 5680459) B5680459
theorem B20197187 : Blo 2101435 20197187 := bstep (se 1 (by rfl) ⟨15147890, by rfl⟩ : syracuseStep 20197187 = 30295781) B30295781
theorem B13464791 : Blo 2101435 13464791 := bstep (se 1 (by rfl) ⟨10098593, by rfl⟩ : syracuseStep 13464791 = 20197187) B20197187
theorem B8976527 : Blo 2101435 8976527 := bstep (se 1 (by rfl) ⟨6732395, by rfl⟩ : syracuseStep 8976527 = 13464791) B13464791
theorem B5984351 : Blo 2101435 5984351 := bstep (se 1 (by rfl) ⟨4488263, by rfl⟩ : syracuseStep 5984351 = 8976527) B8976527
theorem B3989567 : Blo 2101435 3989567 := bstep (se 1 (by rfl) ⟨2992175, by rfl⟩ : syracuseStep 3989567 = 5984351) B5984351
theorem B2659711 : Blo 2101435 2659711 := bstep (se 1 (by rfl) ⟨1994783, by rfl⟩ : syracuseStep 2659711 = 3989567) B3989567
theorem B3546281 : Blo 2101435 3546281 := bstep (se 2 (by rfl) ⟨1329855, by rfl⟩ : syracuseStep 3546281 = 2659711) B2659711
theorem B2364187 : Blo 2101435 2364187 := bstep (se 1 (by rfl) ⟨1773140, by rfl⟩ : syracuseStep 2364187 = 3546281) B3546281
theorem B3152249 : Blo 2101435 3152249 := bstep (se 2 (by rfl) ⟨1182093, by rfl⟩ : syracuseStep 3152249 = 2364187) B2364187
theorem B2101499 : Blo 2101435 2101499 := bstep (se 1 (by rfl) ⟨1576124, by rfl⟩ : syracuseStep 2101499 = 3152249) B3152249
theorem B5680469 : Blo 2101435 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B3786979 : Blo 2101435 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B5049305 : Blo 2101435 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B3366203 : Blo 2101435 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B35906165 : Blo 2101435 35906165 := bstep (se 5 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 35906165 = 3366203) B3366203
theorem B23937443 : Blo 2101435 23937443 := bstep (se 1 (by rfl) ⟨17953082, by rfl⟩ : syracuseStep 23937443 = 35906165) B35906165
theorem B15958295 : Blo 2101435 15958295 := bstep (se 1 (by rfl) ⟨11968721, by rfl⟩ : syracuseStep 15958295 = 23937443) B23937443
theorem B10638863 : Blo 2101435 10638863 := bstep (se 1 (by rfl) ⟨7979147, by rfl⟩ : syracuseStep 10638863 = 15958295) B15958295
theorem B7092575 : Blo 2101435 7092575 := bstep (se 1 (by rfl) ⟨5319431, by rfl⟩ : syracuseStep 7092575 = 10638863) B10638863
theorem B4728383 : Blo 2101435 4728383 := bstep (se 1 (by rfl) ⟨3546287, by rfl⟩ : syracuseStep 4728383 = 7092575) B7092575
theorem B3152255 : Blo 2101435 3152255 := bstep (se 1 (by rfl) ⟨2364191, by rfl⟩ : syracuseStep 3152255 = 4728383) B4728383
theorem B2101503 : Blo 2101435 2101503 := bstep (se 1 (by rfl) ⟨1576127, by rfl⟩ : syracuseStep 2101503 = 3152255) B3152255
theorem B3152261 : Blo 2101435 3152261 := bbase (se 4 (by rfl) ⟨295524, by rfl⟩ : syracuseStep 3152261 = 591049) (by norm_num)
theorem B2101507 : Blo 2101435 2101507 := bstep (se 1 (by rfl) ⟨1576130, by rfl⟩ : syracuseStep 2101507 = 3152261) B3152261
theorem B3546301 : Blo 2101435 3546301 := bbase (se 3 (by rfl) ⟨664931, by rfl⟩ : syracuseStep 3546301 = 1329863) (by norm_num)
theorem B4728401 : Blo 2101435 4728401 := bstep (se 2 (by rfl) ⟨1773150, by rfl⟩ : syracuseStep 4728401 = 3546301) B3546301
theorem B3152267 : Blo 2101435 3152267 := bstep (se 1 (by rfl) ⟨2364200, by rfl⟩ : syracuseStep 3152267 = 4728401) B4728401
theorem B2101511 : Blo 2101435 2101511 := bstep (se 1 (by rfl) ⟨1576133, by rfl⟩ : syracuseStep 2101511 = 3152267) B3152267
theorem B2364205 : Blo 2101435 2364205 := bbase (se 3 (by rfl) ⟨443288, by rfl⟩ : syracuseStep 2364205 = 886577) (by norm_num)
theorem B3152273 : Blo 2101435 3152273 := bstep (se 2 (by rfl) ⟨1182102, by rfl⟩ : syracuseStep 3152273 = 2364205) B2364205
theorem B2101515 : Blo 2101435 2101515 := bstep (se 1 (by rfl) ⟨1576136, by rfl⟩ : syracuseStep 2101515 = 3152273) B3152273
theorem B7092629 : Blo 2101435 7092629 := bbase (se 6 (by rfl) ⟨166233, by rfl⟩ : syracuseStep 7092629 = 332467) (by norm_num)
theorem B4728419 : Blo 2101435 4728419 := bstep (se 1 (by rfl) ⟨3546314, by rfl⟩ : syracuseStep 4728419 = 7092629) B7092629
theorem B3152279 : Blo 2101435 3152279 := bstep (se 1 (by rfl) ⟨2364209, by rfl⟩ : syracuseStep 3152279 = 4728419) B4728419
theorem B2101519 : Blo 2101435 2101519 := bstep (se 1 (by rfl) ⟨1576139, by rfl⟩ : syracuseStep 2101519 = 3152279) B3152279
theorem B3152285 : Blo 2101435 3152285 := bbase (se 3 (by rfl) ⟨591053, by rfl⟩ : syracuseStep 3152285 = 1182107) (by norm_num)
theorem B2101523 : Blo 2101435 2101523 := bstep (se 1 (by rfl) ⟨1576142, by rfl⟩ : syracuseStep 2101523 = 3152285) B3152285
theorem B4728437 : Blo 2101435 4728437 := bbase (se 5 (by rfl) ⟨221645, by rfl⟩ : syracuseStep 4728437 = 443291) (by norm_num)
theorem B3152291 : Blo 2101435 3152291 := bstep (se 1 (by rfl) ⟨2364218, by rfl⟩ : syracuseStep 3152291 = 4728437) B4728437
theorem B2101527 : Blo 2101435 2101527 := bstep (se 1 (by rfl) ⟨1576145, by rfl⟩ : syracuseStep 2101527 = 3152291) B3152291
theorem B5049373 : Blo 2101435 5049373 := bbase (se 3 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 5049373 = 1893515) (by norm_num)
theorem B6732497 : Blo 2101435 6732497 := bstep (se 2 (by rfl) ⟨2524686, by rfl⟩ : syracuseStep 6732497 = 5049373) B5049373
theorem B17953325 : Blo 2101435 17953325 := bstep (se 3 (by rfl) ⟨3366248, by rfl⟩ : syracuseStep 17953325 = 6732497) B6732497
theorem B11968883 : Blo 2101435 11968883 := bstep (se 1 (by rfl) ⟨8976662, by rfl⟩ : syracuseStep 11968883 = 17953325) B17953325
theorem B7979255 : Blo 2101435 7979255 := bstep (se 1 (by rfl) ⟨5984441, by rfl⟩ : syracuseStep 7979255 = 11968883) B11968883
theorem B5319503 : Blo 2101435 5319503 := bstep (se 1 (by rfl) ⟨3989627, by rfl⟩ : syracuseStep 5319503 = 7979255) B7979255
theorem B3546335 : Blo 2101435 3546335 := bstep (se 1 (by rfl) ⟨2659751, by rfl⟩ : syracuseStep 3546335 = 5319503) B5319503
theorem B2364223 : Blo 2101435 2364223 := bstep (se 1 (by rfl) ⟨1773167, by rfl⟩ : syracuseStep 2364223 = 3546335) B3546335
theorem B3152297 : Blo 2101435 3152297 := bstep (se 2 (by rfl) ⟨1182111, by rfl⟩ : syracuseStep 3152297 = 2364223) B2364223
theorem B2101531 : Blo 2101435 2101531 := bstep (se 1 (by rfl) ⟨1576148, by rfl⟩ : syracuseStep 2101531 = 3152297) B3152297
theorem B7979269 : Blo 2101435 7979269 := bbase (se 4 (by rfl) ⟨748056, by rfl⟩ : syracuseStep 7979269 = 1496113) (by norm_num)
theorem B10639025 : Blo 2101435 10639025 := bstep (se 2 (by rfl) ⟨3989634, by rfl⟩ : syracuseStep 10639025 = 7979269) B7979269
theorem B7092683 : Blo 2101435 7092683 := bstep (se 1 (by rfl) ⟨5319512, by rfl⟩ : syracuseStep 7092683 = 10639025) B10639025
theorem B4728455 : Blo 2101435 4728455 := bstep (se 1 (by rfl) ⟨3546341, by rfl⟩ : syracuseStep 4728455 = 7092683) B7092683
theorem B3152303 : Blo 2101435 3152303 := bstep (se 1 (by rfl) ⟨2364227, by rfl⟩ : syracuseStep 3152303 = 4728455) B4728455
theorem B2101535 : Blo 2101435 2101535 := bstep (se 1 (by rfl) ⟨1576151, by rfl⟩ : syracuseStep 2101535 = 3152303) B3152303
theorem B3152309 : Blo 2101435 3152309 := bbase (se 5 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 3152309 = 295529) (by norm_num)
theorem B2101539 : Blo 2101435 2101539 := bstep (se 1 (by rfl) ⟨1576154, by rfl⟩ : syracuseStep 2101539 = 3152309) B3152309
theorem B5319533 : Blo 2101435 5319533 := bbase (se 3 (by rfl) ⟨997412, by rfl⟩ : syracuseStep 5319533 = 1994825) (by norm_num)
theorem B3546355 : Blo 2101435 3546355 := bstep (se 1 (by rfl) ⟨2659766, by rfl⟩ : syracuseStep 3546355 = 5319533) B5319533
theorem B4728473 : Blo 2101435 4728473 := bstep (se 2 (by rfl) ⟨1773177, by rfl⟩ : syracuseStep 4728473 = 3546355) B3546355
theorem B3152315 : Blo 2101435 3152315 := bstep (se 1 (by rfl) ⟨2364236, by rfl⟩ : syracuseStep 3152315 = 4728473) B4728473
theorem B2101543 : Blo 2101435 2101543 := bstep (se 1 (by rfl) ⟨1576157, by rfl⟩ : syracuseStep 2101543 = 3152315) B3152315
theorem B2364241 : Blo 2101435 2364241 := bbase (se 2 (by rfl) ⟨886590, by rfl⟩ : syracuseStep 2364241 = 1773181) (by norm_num)
theorem B3152321 : Blo 2101435 3152321 := bstep (se 2 (by rfl) ⟨1182120, by rfl⟩ : syracuseStep 3152321 = 2364241) B2364241
theorem B2101547 : Blo 2101435 2101547 := bstep (se 1 (by rfl) ⟨1576160, by rfl⟩ : syracuseStep 2101547 = 3152321) B3152321
theorem B6390677 : Blo 2101435 6390677 := bbase (se 6 (by rfl) ⟨149781, by rfl⟩ : syracuseStep 6390677 = 299563) (by norm_num)
theorem B4260451 : Blo 2101435 4260451 := bstep (se 1 (by rfl) ⟨3195338, by rfl⟩ : syracuseStep 4260451 = 6390677) B6390677
theorem B5680601 : Blo 2101435 5680601 := bstep (se 2 (by rfl) ⟨2130225, by rfl⟩ : syracuseStep 5680601 = 4260451) B4260451
theorem B3787067 : Blo 2101435 3787067 := bstep (se 1 (by rfl) ⟨2840300, by rfl⟩ : syracuseStep 3787067 = 5680601) B5680601
theorem B2524711 : Blo 2101435 2524711 := bstep (se 1 (by rfl) ⟨1893533, by rfl⟩ : syracuseStep 2524711 = 3787067) B3787067
theorem B3366281 : Blo 2101435 3366281 := bstep (se 2 (by rfl) ⟨1262355, by rfl⟩ : syracuseStep 3366281 = 2524711) B2524711
theorem B2244187 : Blo 2101435 2244187 := bstep (se 1 (by rfl) ⟨1683140, by rfl⟩ : syracuseStep 2244187 = 3366281) B3366281
theorem B2992249 : Blo 2101435 2992249 := bstep (se 2 (by rfl) ⟨1122093, by rfl⟩ : syracuseStep 2992249 = 2244187) B2244187
theorem B3989665 : Blo 2101435 3989665 := bstep (se 2 (by rfl) ⟨1496124, by rfl⟩ : syracuseStep 3989665 = 2992249) B2992249
theorem B5319553 : Blo 2101435 5319553 := bstep (se 2 (by rfl) ⟨1994832, by rfl⟩ : syracuseStep 5319553 = 3989665) B3989665
theorem B7092737 : Blo 2101435 7092737 := bstep (se 2 (by rfl) ⟨2659776, by rfl⟩ : syracuseStep 7092737 = 5319553) B5319553
theorem B4728491 : Blo 2101435 4728491 := bstep (se 1 (by rfl) ⟨3546368, by rfl⟩ : syracuseStep 4728491 = 7092737) B7092737
theorem B3152327 : Blo 2101435 3152327 := bstep (se 1 (by rfl) ⟨2364245, by rfl⟩ : syracuseStep 3152327 = 4728491) B4728491
theorem B2101551 : Blo 2101435 2101551 := bstep (se 1 (by rfl) ⟨1576163, by rfl⟩ : syracuseStep 2101551 = 3152327) B3152327
theorem B3152333 : Blo 2101435 3152333 := bbase (se 3 (by rfl) ⟨591062, by rfl⟩ : syracuseStep 3152333 = 1182125) (by norm_num)
theorem B2101555 : Blo 2101435 2101555 := bstep (se 1 (by rfl) ⟨1576166, by rfl⟩ : syracuseStep 2101555 = 3152333) B3152333
theorem B4728509 : Blo 2101435 4728509 := bbase (se 3 (by rfl) ⟨886595, by rfl⟩ : syracuseStep 4728509 = 1773191) (by norm_num)
theorem B3152339 : Blo 2101435 3152339 := bstep (se 1 (by rfl) ⟨2364254, by rfl⟩ : syracuseStep 3152339 = 4728509) B4728509
theorem B2101559 : Blo 2101435 2101559 := bstep (se 1 (by rfl) ⟨1576169, by rfl⟩ : syracuseStep 2101559 = 3152339) B3152339
theorem B3546389 : Blo 2101435 3546389 := bbase (se 6 (by rfl) ⟨83118, by rfl⟩ : syracuseStep 3546389 = 166237) (by norm_num)
theorem B2364259 : Blo 2101435 2364259 := bstep (se 1 (by rfl) ⟨1773194, by rfl⟩ : syracuseStep 2364259 = 3546389) B3546389
theorem B3152345 : Blo 2101435 3152345 := bstep (se 2 (by rfl) ⟨1182129, by rfl⟩ : syracuseStep 3152345 = 2364259) B2364259
theorem B2101563 : Blo 2101435 2101563 := bstep (se 1 (by rfl) ⟨1576172, by rfl⟩ : syracuseStep 2101563 = 3152345) B3152345
theorem B2396521 : Blo 2101435 2396521 := bbase (se 2 (by rfl) ⟨898695, by rfl⟩ : syracuseStep 2396521 = 1797391) (by norm_num)
theorem B3195361 : Blo 2101435 3195361 := bstep (se 2 (by rfl) ⟨1198260, by rfl⟩ : syracuseStep 3195361 = 2396521) B2396521
theorem B4260481 : Blo 2101435 4260481 := bstep (se 2 (by rfl) ⟨1597680, by rfl⟩ : syracuseStep 4260481 = 3195361) B3195361
theorem B22722565 : Blo 2101435 22722565 := bstep (se 4 (by rfl) ⟨2130240, by rfl⟩ : syracuseStep 22722565 = 4260481) B4260481
theorem B30296753 : Blo 2101435 30296753 := bstep (se 2 (by rfl) ⟨11361282, by rfl⟩ : syracuseStep 30296753 = 22722565) B22722565
theorem B20197835 : Blo 2101435 20197835 := bstep (se 1 (by rfl) ⟨15148376, by rfl⟩ : syracuseStep 20197835 = 30296753) B30296753
theorem B13465223 : Blo 2101435 13465223 := bstep (se 1 (by rfl) ⟨10098917, by rfl⟩ : syracuseStep 13465223 = 20197835) B20197835
theorem B8976815 : Blo 2101435 8976815 := bstep (se 1 (by rfl) ⟨6732611, by rfl⟩ : syracuseStep 8976815 = 13465223) B13465223
theorem B5984543 : Blo 2101435 5984543 := bstep (se 1 (by rfl) ⟨4488407, by rfl⟩ : syracuseStep 5984543 = 8976815) B8976815
theorem B15958781 : Blo 2101435 15958781 := bstep (se 3 (by rfl) ⟨2992271, by rfl⟩ : syracuseStep 15958781 = 5984543) B5984543
theorem B10639187 : Blo 2101435 10639187 := bstep (se 1 (by rfl) ⟨7979390, by rfl⟩ : syracuseStep 10639187 = 15958781) B15958781
theorem B7092791 : Blo 2101435 7092791 := bstep (se 1 (by rfl) ⟨5319593, by rfl⟩ : syracuseStep 7092791 = 10639187) B10639187
theorem B4728527 : Blo 2101435 4728527 := bstep (se 1 (by rfl) ⟨3546395, by rfl⟩ : syracuseStep 4728527 = 7092791) B7092791
theorem B3152351 : Blo 2101435 3152351 := bstep (se 1 (by rfl) ⟨2364263, by rfl⟩ : syracuseStep 3152351 = 4728527) B4728527
theorem B2101567 : Blo 2101435 2101567 := bstep (se 1 (by rfl) ⟨1576175, by rfl⟩ : syracuseStep 2101567 = 3152351) B3152351
theorem B3152357 : Blo 2101435 3152357 := bbase (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) (by norm_num)
theorem B2101571 : Blo 2101435 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B8520997 : Blo 2101435 8520997 := bbase (se 4 (by rfl) ⟨798843, by rfl⟩ : syracuseStep 8520997 = 1597687) (by norm_num)
theorem B11361329 : Blo 2101435 11361329 := bstep (se 2 (by rfl) ⟨4260498, by rfl⟩ : syracuseStep 11361329 = 8520997) B8520997
theorem B7574219 : Blo 2101435 7574219 := bstep (se 1 (by rfl) ⟨5680664, by rfl⟩ : syracuseStep 7574219 = 11361329) B11361329
theorem B5049479 : Blo 2101435 5049479 := bstep (se 1 (by rfl) ⟨3787109, by rfl⟩ : syracuseStep 5049479 = 7574219) B7574219
theorem B13465277 : Blo 2101435 13465277 := bstep (se 3 (by rfl) ⟨2524739, by rfl⟩ : syracuseStep 13465277 = 5049479) B5049479
theorem B8976851 : Blo 2101435 8976851 := bstep (se 1 (by rfl) ⟨6732638, by rfl⟩ : syracuseStep 8976851 = 13465277) B13465277
theorem B5984567 : Blo 2101435 5984567 := bstep (se 1 (by rfl) ⟨4488425, by rfl⟩ : syracuseStep 5984567 = 8976851) B8976851
theorem B3989711 : Blo 2101435 3989711 := bstep (se 1 (by rfl) ⟨2992283, by rfl⟩ : syracuseStep 3989711 = 5984567) B5984567
theorem B2659807 : Blo 2101435 2659807 := bstep (se 1 (by rfl) ⟨1994855, by rfl⟩ : syracuseStep 2659807 = 3989711) B3989711
theorem B3546409 : Blo 2101435 3546409 := bstep (se 2 (by rfl) ⟨1329903, by rfl⟩ : syracuseStep 3546409 = 2659807) B2659807
theorem B4728545 : Blo 2101435 4728545 := bstep (se 2 (by rfl) ⟨1773204, by rfl⟩ : syracuseStep 4728545 = 3546409) B3546409
theorem B3152363 : Blo 2101435 3152363 := bstep (se 1 (by rfl) ⟨2364272, by rfl⟩ : syracuseStep 3152363 = 4728545) B4728545
theorem B2101575 : Blo 2101435 2101575 := bstep (se 1 (by rfl) ⟨1576181, by rfl⟩ : syracuseStep 2101575 = 3152363) B3152363
theorem B2364277 : Blo 2101435 2364277 := bbase (se 5 (by rfl) ⟨110825, by rfl⟩ : syracuseStep 2364277 = 221651) (by norm_num)
theorem B3152369 : Blo 2101435 3152369 := bstep (se 2 (by rfl) ⟨1182138, by rfl⟩ : syracuseStep 3152369 = 2364277) B2364277
theorem B2101579 : Blo 2101435 2101579 := bstep (se 1 (by rfl) ⟨1576184, by rfl⟩ : syracuseStep 2101579 = 3152369) B3152369
theorem B2659817 : Blo 2101435 2659817 := bbase (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) (by norm_num)
theorem B7092845 : Blo 2101435 7092845 := bstep (se 3 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 7092845 = 2659817) B2659817
theorem B4728563 : Blo 2101435 4728563 := bstep (se 1 (by rfl) ⟨3546422, by rfl⟩ : syracuseStep 4728563 = 7092845) B7092845
theorem B3152375 : Blo 2101435 3152375 := bstep (se 1 (by rfl) ⟨2364281, by rfl⟩ : syracuseStep 3152375 = 4728563) B4728563
theorem B2101583 : Blo 2101435 2101583 := bstep (se 1 (by rfl) ⟨1576187, by rfl⟩ : syracuseStep 2101583 = 3152375) B3152375
theorem B3152381 : Blo 2101435 3152381 := bbase (se 3 (by rfl) ⟨591071, by rfl⟩ : syracuseStep 3152381 = 1182143) (by norm_num)
theorem B2101587 : Blo 2101435 2101587 := bstep (se 1 (by rfl) ⟨1576190, by rfl⟩ : syracuseStep 2101587 = 3152381) B3152381
theorem B4728581 : Blo 2101435 4728581 := bbase (se 4 (by rfl) ⟨443304, by rfl⟩ : syracuseStep 4728581 = 886609) (by norm_num)
theorem B3152387 : Blo 2101435 3152387 := bstep (se 1 (by rfl) ⟨2364290, by rfl⟩ : syracuseStep 3152387 = 4728581) B4728581
theorem B2101591 : Blo 2101435 2101591 := bstep (se 1 (by rfl) ⟨1576193, by rfl⟩ : syracuseStep 2101591 = 3152387) B3152387
theorem B3989749 : Blo 2101435 3989749 := bbase (se 5 (by rfl) ⟨187019, by rfl⟩ : syracuseStep 3989749 = 374039) (by norm_num)
theorem B5319665 : Blo 2101435 5319665 := bstep (se 2 (by rfl) ⟨1994874, by rfl⟩ : syracuseStep 5319665 = 3989749) B3989749
theorem B3546443 : Blo 2101435 3546443 := bstep (se 1 (by rfl) ⟨2659832, by rfl⟩ : syracuseStep 3546443 = 5319665) B5319665
theorem B2364295 : Blo 2101435 2364295 := bstep (se 1 (by rfl) ⟨1773221, by rfl⟩ : syracuseStep 2364295 = 3546443) B3546443
theorem B3152393 : Blo 2101435 3152393 := bstep (se 2 (by rfl) ⟨1182147, by rfl⟩ : syracuseStep 3152393 = 2364295) B2364295
theorem B2101595 : Blo 2101435 2101595 := bstep (se 1 (by rfl) ⟨1576196, by rfl⟩ : syracuseStep 2101595 = 3152393) B3152393
theorem B10639349 : Blo 2101435 10639349 := bbase (se 5 (by rfl) ⟨498719, by rfl⟩ : syracuseStep 10639349 = 997439) (by norm_num)
theorem B7092899 : Blo 2101435 7092899 := bstep (se 1 (by rfl) ⟨5319674, by rfl⟩ : syracuseStep 7092899 = 10639349) B10639349
theorem B4728599 : Blo 2101435 4728599 := bstep (se 1 (by rfl) ⟨3546449, by rfl⟩ : syracuseStep 4728599 = 7092899) B7092899
theorem B3152399 : Blo 2101435 3152399 := bstep (se 1 (by rfl) ⟨2364299, by rfl⟩ : syracuseStep 3152399 = 4728599) B4728599
theorem B2101599 : Blo 2101435 2101599 := bstep (se 1 (by rfl) ⟨1576199, by rfl⟩ : syracuseStep 2101599 = 3152399) B3152399
theorem B3152405 : Blo 2101435 3152405 := bbase (se 6 (by rfl) ⟨73884, by rfl⟩ : syracuseStep 3152405 = 147769) (by norm_num)
theorem B2101603 : Blo 2101435 2101603 := bstep (se 1 (by rfl) ⟨1576202, by rfl⟩ : syracuseStep 2101603 = 3152405) B3152405
theorem B17953973 : Blo 2101435 17953973 := bbase (se 5 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 17953973 = 1683185) (by norm_num)
theorem B11969315 : Blo 2101435 11969315 := bstep (se 1 (by rfl) ⟨8976986, by rfl⟩ : syracuseStep 11969315 = 17953973) B17953973
theorem B7979543 : Blo 2101435 7979543 := bstep (se 1 (by rfl) ⟨5984657, by rfl⟩ : syracuseStep 7979543 = 11969315) B11969315
theorem B5319695 : Blo 2101435 5319695 := bstep (se 1 (by rfl) ⟨3989771, by rfl⟩ : syracuseStep 5319695 = 7979543) B7979543
theorem B3546463 : Blo 2101435 3546463 := bstep (se 1 (by rfl) ⟨2659847, by rfl⟩ : syracuseStep 3546463 = 5319695) B5319695
theorem B4728617 : Blo 2101435 4728617 := bstep (se 2 (by rfl) ⟨1773231, by rfl⟩ : syracuseStep 4728617 = 3546463) B3546463
theorem B3152411 : Blo 2101435 3152411 := bstep (se 1 (by rfl) ⟨2364308, by rfl⟩ : syracuseStep 3152411 = 4728617) B4728617
theorem B2101607 : Blo 2101435 2101607 := bstep (se 1 (by rfl) ⟨1576205, by rfl⟩ : syracuseStep 2101607 = 3152411) B3152411
theorem B2364313 : Blo 2101435 2364313 := bbase (se 2 (by rfl) ⟨886617, by rfl⟩ : syracuseStep 2364313 = 1773235) (by norm_num)
theorem B3152417 : Blo 2101435 3152417 := bstep (se 2 (by rfl) ⟨1182156, by rfl⟩ : syracuseStep 3152417 = 2364313) B2364313
theorem B2101611 : Blo 2101435 2101611 := bstep (se 1 (by rfl) ⟨1576208, by rfl⟩ : syracuseStep 2101611 = 3152417) B3152417
theorem B7979573 : Blo 2101435 7979573 := bbase (se 5 (by rfl) ⟨374042, by rfl⟩ : syracuseStep 7979573 = 748085) (by norm_num)
theorem B5319715 : Blo 2101435 5319715 := bstep (se 1 (by rfl) ⟨3989786, by rfl⟩ : syracuseStep 5319715 = 7979573) B7979573
theorem B7092953 : Blo 2101435 7092953 := bstep (se 2 (by rfl) ⟨2659857, by rfl⟩ : syracuseStep 7092953 = 5319715) B5319715
theorem B4728635 : Blo 2101435 4728635 := bstep (se 1 (by rfl) ⟨3546476, by rfl⟩ : syracuseStep 4728635 = 7092953) B7092953
theorem B3152423 : Blo 2101435 3152423 := bstep (se 1 (by rfl) ⟨2364317, by rfl⟩ : syracuseStep 3152423 = 4728635) B4728635
theorem B2101615 : Blo 2101435 2101615 := bstep (se 1 (by rfl) ⟨1576211, by rfl⟩ : syracuseStep 2101615 = 3152423) B3152423
theorem B3152429 : Blo 2101435 3152429 := bbase (se 3 (by rfl) ⟨591080, by rfl⟩ : syracuseStep 3152429 = 1182161) (by norm_num)
theorem B2101619 : Blo 2101435 2101619 := bstep (se 1 (by rfl) ⟨1576214, by rfl⟩ : syracuseStep 2101619 = 3152429) B3152429
theorem B4728653 : Blo 2101435 4728653 := bbase (se 3 (by rfl) ⟨886622, by rfl⟩ : syracuseStep 4728653 = 1773245) (by norm_num)
theorem B3152435 : Blo 2101435 3152435 := bstep (se 1 (by rfl) ⟨2364326, by rfl⟩ : syracuseStep 3152435 = 4728653) B4728653
theorem B2101623 : Blo 2101435 2101623 := bstep (se 1 (by rfl) ⟨1576217, by rfl⟩ : syracuseStep 2101623 = 3152435) B3152435
theorem B2659873 : Blo 2101435 2659873 := bbase (se 2 (by rfl) ⟨997452, by rfl⟩ : syracuseStep 2659873 = 1994905) (by norm_num)
theorem B3546497 : Blo 2101435 3546497 := bstep (se 2 (by rfl) ⟨1329936, by rfl⟩ : syracuseStep 3546497 = 2659873) B2659873
theorem B2364331 : Blo 2101435 2364331 := bstep (se 1 (by rfl) ⟨1773248, by rfl⟩ : syracuseStep 2364331 = 3546497) B3546497
theorem B3152441 : Blo 2101435 3152441 := bstep (se 2 (by rfl) ⟨1182165, by rfl⟩ : syracuseStep 3152441 = 2364331) B2364331
theorem B2101627 : Blo 2101435 2101627 := bstep (se 1 (by rfl) ⟨1576220, by rfl⟩ : syracuseStep 2101627 = 3152441) B3152441
theorem B23938901 : Blo 2101435 23938901 := bbase (se 9 (by rfl) ⟨70133, by rfl⟩ : syracuseStep 23938901 = 140267) (by norm_num)
theorem B15959267 : Blo 2101435 15959267 := bstep (se 1 (by rfl) ⟨11969450, by rfl⟩ : syracuseStep 15959267 = 23938901) B23938901
theorem B10639511 : Blo 2101435 10639511 := bstep (se 1 (by rfl) ⟨7979633, by rfl⟩ : syracuseStep 10639511 = 15959267) B15959267
theorem B7093007 : Blo 2101435 7093007 := bstep (se 1 (by rfl) ⟨5319755, by rfl⟩ : syracuseStep 7093007 = 10639511) B10639511
theorem B4728671 : Blo 2101435 4728671 := bstep (se 1 (by rfl) ⟨3546503, by rfl⟩ : syracuseStep 4728671 = 7093007) B7093007
theorem B3152447 : Blo 2101435 3152447 := bstep (se 1 (by rfl) ⟨2364335, by rfl⟩ : syracuseStep 3152447 = 4728671) B4728671
theorem B2101631 : Blo 2101435 2101631 := bstep (se 1 (by rfl) ⟨1576223, by rfl⟩ : syracuseStep 2101631 = 3152447) B3152447
theorem B3152453 : Blo 2101435 3152453 := bbase (se 4 (by rfl) ⟨295542, by rfl⟩ : syracuseStep 3152453 = 591085) (by norm_num)
theorem B2101635 : Blo 2101435 2101635 := bstep (se 1 (by rfl) ⟨1576226, by rfl⟩ : syracuseStep 2101635 = 3152453) B3152453
theorem B3546517 : Blo 2101435 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B4728689 : Blo 2101435 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B3152459 : Blo 2101435 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B2101639 : Blo 2101435 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B2364349 : Blo 2101435 2364349 := bbase (se 3 (by rfl) ⟨443315, by rfl⟩ : syracuseStep 2364349 = 886631) (by norm_num)
theorem B3152465 : Blo 2101435 3152465 := bstep (se 2 (by rfl) ⟨1182174, by rfl⟩ : syracuseStep 3152465 = 2364349) B2364349
theorem B2101643 : Blo 2101435 2101643 := bstep (se 1 (by rfl) ⟨1576232, by rfl⟩ : syracuseStep 2101643 = 3152465) B3152465
theorem B7093061 : Blo 2101435 7093061 := bbase (se 4 (by rfl) ⟨664974, by rfl⟩ : syracuseStep 7093061 = 1329949) (by norm_num)
theorem B4728707 : Blo 2101435 4728707 := bstep (se 1 (by rfl) ⟨3546530, by rfl⟩ : syracuseStep 4728707 = 7093061) B7093061
theorem B3152471 : Blo 2101435 3152471 := bstep (se 1 (by rfl) ⟨2364353, by rfl⟩ : syracuseStep 3152471 = 4728707) B4728707
theorem B2101647 : Blo 2101435 2101647 := bstep (se 1 (by rfl) ⟨1576235, by rfl⟩ : syracuseStep 2101647 = 3152471) B3152471
theorem B3152477 : Blo 2101435 3152477 := bbase (se 3 (by rfl) ⟨591089, by rfl⟩ : syracuseStep 3152477 = 1182179) (by norm_num)
theorem B2101651 : Blo 2101435 2101651 := bstep (se 1 (by rfl) ⟨1576238, by rfl⟩ : syracuseStep 2101651 = 3152477) B3152477
theorem B4728725 : Blo 2101435 4728725 := bbase (se 6 (by rfl) ⟨110829, by rfl⟩ : syracuseStep 4728725 = 221659) (by norm_num)
theorem B3152483 : Blo 2101435 3152483 := bstep (se 1 (by rfl) ⟨2364362, by rfl⟩ : syracuseStep 3152483 = 4728725) B4728725
theorem B2101655 : Blo 2101435 2101655 := bstep (se 1 (by rfl) ⟨1576241, by rfl⟩ : syracuseStep 2101655 = 3152483) B3152483
theorem B4488605 : Blo 2101435 4488605 := bbase (se 3 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 4488605 = 1683227) (by norm_num)
theorem B2992403 : Blo 2101435 2992403 := bstep (se 1 (by rfl) ⟨2244302, by rfl⟩ : syracuseStep 2992403 = 4488605) B4488605
theorem B7979741 : Blo 2101435 7979741 := bstep (se 3 (by rfl) ⟨1496201, by rfl⟩ : syracuseStep 7979741 = 2992403) B2992403
theorem B5319827 : Blo 2101435 5319827 := bstep (se 1 (by rfl) ⟨3989870, by rfl⟩ : syracuseStep 5319827 = 7979741) B7979741
theorem B3546551 : Blo 2101435 3546551 := bstep (se 1 (by rfl) ⟨2659913, by rfl⟩ : syracuseStep 3546551 = 5319827) B5319827
theorem B2364367 : Blo 2101435 2364367 := bstep (se 1 (by rfl) ⟨1773275, by rfl⟩ : syracuseStep 2364367 = 3546551) B3546551
theorem B3152489 : Blo 2101435 3152489 := bstep (se 2 (by rfl) ⟨1182183, by rfl⟩ : syracuseStep 3152489 = 2364367) B2364367
theorem B2101659 : Blo 2101435 2101659 := bstep (se 1 (by rfl) ⟨1576244, by rfl⟩ : syracuseStep 2101659 = 3152489) B3152489
theorem B5680901 : Blo 2101435 5680901 := bbase (se 4 (by rfl) ⟨532584, by rfl⟩ : syracuseStep 5680901 = 1065169) (by norm_num)
theorem B15149069 : Blo 2101435 15149069 := bstep (se 3 (by rfl) ⟨2840450, by rfl⟩ : syracuseStep 15149069 = 5680901) B5680901
theorem B10099379 : Blo 2101435 10099379 := bstep (se 1 (by rfl) ⟨7574534, by rfl⟩ : syracuseStep 10099379 = 15149069) B15149069
theorem B6732919 : Blo 2101435 6732919 := bstep (se 1 (by rfl) ⟨5049689, by rfl⟩ : syracuseStep 6732919 = 10099379) B10099379
theorem B8977225 : Blo 2101435 8977225 := bstep (se 2 (by rfl) ⟨3366459, by rfl⟩ : syracuseStep 8977225 = 6732919) B6732919
theorem B11969633 : Blo 2101435 11969633 := bstep (se 2 (by rfl) ⟨4488612, by rfl⟩ : syracuseStep 11969633 = 8977225) B8977225
theorem B7979755 : Blo 2101435 7979755 := bstep (se 1 (by rfl) ⟨5984816, by rfl⟩ : syracuseStep 7979755 = 11969633) B11969633
theorem B10639673 : Blo 2101435 10639673 := bstep (se 2 (by rfl) ⟨3989877, by rfl⟩ : syracuseStep 10639673 = 7979755) B7979755
theorem B7093115 : Blo 2101435 7093115 := bstep (se 1 (by rfl) ⟨5319836, by rfl⟩ : syracuseStep 7093115 = 10639673) B10639673
theorem B4728743 : Blo 2101435 4728743 := bstep (se 1 (by rfl) ⟨3546557, by rfl⟩ : syracuseStep 4728743 = 7093115) B7093115
theorem B3152495 : Blo 2101435 3152495 := bstep (se 1 (by rfl) ⟨2364371, by rfl⟩ : syracuseStep 3152495 = 4728743) B4728743
theorem B2101663 : Blo 2101435 2101663 := bstep (se 1 (by rfl) ⟨1576247, by rfl⟩ : syracuseStep 2101663 = 3152495) B3152495
theorem B3152501 : Blo 2101435 3152501 := bbase (se 5 (by rfl) ⟨147773, by rfl⟩ : syracuseStep 3152501 = 295547) (by norm_num)
theorem B2101667 : Blo 2101435 2101667 := bstep (se 1 (by rfl) ⟨1576250, by rfl⟩ : syracuseStep 2101667 = 3152501) B3152501
theorem B3989893 : Blo 2101435 3989893 := bbase (se 4 (by rfl) ⟨374052, by rfl⟩ : syracuseStep 3989893 = 748105) (by norm_num)
theorem B5319857 : Blo 2101435 5319857 := bstep (se 2 (by rfl) ⟨1994946, by rfl⟩ : syracuseStep 5319857 = 3989893) B3989893
theorem B3546571 : Blo 2101435 3546571 := bstep (se 1 (by rfl) ⟨2659928, by rfl⟩ : syracuseStep 3546571 = 5319857) B5319857
theorem B4728761 : Blo 2101435 4728761 := bstep (se 2 (by rfl) ⟨1773285, by rfl⟩ : syracuseStep 4728761 = 3546571) B3546571
theorem B3152507 : Blo 2101435 3152507 := bstep (se 1 (by rfl) ⟨2364380, by rfl⟩ : syracuseStep 3152507 = 4728761) B4728761
theorem B2101671 : Blo 2101435 2101671 := bstep (se 1 (by rfl) ⟨1576253, by rfl⟩ : syracuseStep 2101671 = 3152507) B3152507
theorem B2364385 : Blo 2101435 2364385 := bbase (se 2 (by rfl) ⟨886644, by rfl⟩ : syracuseStep 2364385 = 1773289) (by norm_num)
theorem B3152513 : Blo 2101435 3152513 := bstep (se 2 (by rfl) ⟨1182192, by rfl⟩ : syracuseStep 3152513 = 2364385) B2364385
theorem B2101675 : Blo 2101435 2101675 := bstep (se 1 (by rfl) ⟨1576256, by rfl⟩ : syracuseStep 2101675 = 3152513) B3152513
theorem B5319877 : Blo 2101435 5319877 := bbase (se 4 (by rfl) ⟨498738, by rfl⟩ : syracuseStep 5319877 = 997477) (by norm_num)
theorem B7093169 : Blo 2101435 7093169 := bstep (se 2 (by rfl) ⟨2659938, by rfl⟩ : syracuseStep 7093169 = 5319877) B5319877
theorem B4728779 : Blo 2101435 4728779 := bstep (se 1 (by rfl) ⟨3546584, by rfl⟩ : syracuseStep 4728779 = 7093169) B7093169
theorem B3152519 : Blo 2101435 3152519 := bstep (se 1 (by rfl) ⟨2364389, by rfl⟩ : syracuseStep 3152519 = 4728779) B4728779
theorem B2101679 : Blo 2101435 2101679 := bstep (se 1 (by rfl) ⟨1576259, by rfl⟩ : syracuseStep 2101679 = 3152519) B3152519
theorem B3152525 : Blo 2101435 3152525 := bbase (se 3 (by rfl) ⟨591098, by rfl⟩ : syracuseStep 3152525 = 1182197) (by norm_num)
theorem B2101683 : Blo 2101435 2101683 := bstep (se 1 (by rfl) ⟨1576262, by rfl⟩ : syracuseStep 2101683 = 3152525) B3152525
theorem B4728797 : Blo 2101435 4728797 := bbase (se 3 (by rfl) ⟨886649, by rfl⟩ : syracuseStep 4728797 = 1773299) (by norm_num)
theorem B3152531 : Blo 2101435 3152531 := bstep (se 1 (by rfl) ⟨2364398, by rfl⟩ : syracuseStep 3152531 = 4728797) B4728797
theorem B2101687 : Blo 2101435 2101687 := bstep (se 1 (by rfl) ⟨1576265, by rfl⟩ : syracuseStep 2101687 = 3152531) B3152531
theorem B3546605 : Blo 2101435 3546605 := bbase (se 3 (by rfl) ⟨664988, by rfl⟩ : syracuseStep 3546605 = 1329977) (by norm_num)
theorem B2364403 : Blo 2101435 2364403 := bstep (se 1 (by rfl) ⟨1773302, by rfl⟩ : syracuseStep 2364403 = 3546605) B3546605
theorem B3152537 : Blo 2101435 3152537 := bstep (se 2 (by rfl) ⟨1182201, by rfl⟩ : syracuseStep 3152537 = 2364403) B2364403
theorem B2101691 : Blo 2101435 2101691 := bstep (se 1 (by rfl) ⟨1576268, by rfl⟩ : syracuseStep 2101691 = 3152537) B3152537
theorem B3787325 : Blo 2101435 3787325 := bbase (se 3 (by rfl) ⟨710123, by rfl⟩ : syracuseStep 3787325 = 1420247) (by norm_num)
theorem B2524883 : Blo 2101435 2524883 := bstep (se 1 (by rfl) ⟨1893662, by rfl⟩ : syracuseStep 2524883 = 3787325) B3787325
theorem B26932085 : Blo 2101435 26932085 := bstep (se 5 (by rfl) ⟨1262441, by rfl⟩ : syracuseStep 26932085 = 2524883) B2524883
theorem B17954723 : Blo 2101435 17954723 := bstep (se 1 (by rfl) ⟨13466042, by rfl⟩ : syracuseStep 17954723 = 26932085) B26932085
theorem B11969815 : Blo 2101435 11969815 := bstep (se 1 (by rfl) ⟨8977361, by rfl⟩ : syracuseStep 11969815 = 17954723) B17954723
theorem B15959753 : Blo 2101435 15959753 := bstep (se 2 (by rfl) ⟨5984907, by rfl⟩ : syracuseStep 15959753 = 11969815) B11969815
theorem B10639835 : Blo 2101435 10639835 := bstep (se 1 (by rfl) ⟨7979876, by rfl⟩ : syracuseStep 10639835 = 15959753) B15959753
theorem B7093223 : Blo 2101435 7093223 := bstep (se 1 (by rfl) ⟨5319917, by rfl⟩ : syracuseStep 7093223 = 10639835) B10639835
theorem B4728815 : Blo 2101435 4728815 := bstep (se 1 (by rfl) ⟨3546611, by rfl⟩ : syracuseStep 4728815 = 7093223) B7093223
theorem B3152543 : Blo 2101435 3152543 := bstep (se 1 (by rfl) ⟨2364407, by rfl⟩ : syracuseStep 3152543 = 4728815) B4728815
theorem B2101695 : Blo 2101435 2101695 := bstep (se 1 (by rfl) ⟨1576271, by rfl⟩ : syracuseStep 2101695 = 3152543) B3152543
theorem B3152549 : Blo 2101435 3152549 := bbase (se 4 (by rfl) ⟨295551, by rfl⟩ : syracuseStep 3152549 = 591103) (by norm_num)
theorem B2101699 : Blo 2101435 2101699 := bstep (se 1 (by rfl) ⟨1576274, by rfl⟩ : syracuseStep 2101699 = 3152549) B3152549
theorem B2659969 : Blo 2101435 2659969 := bbase (se 2 (by rfl) ⟨997488, by rfl⟩ : syracuseStep 2659969 = 1994977) (by norm_num)
theorem B3546625 : Blo 2101435 3546625 := bstep (se 2 (by rfl) ⟨1329984, by rfl⟩ : syracuseStep 3546625 = 2659969) B2659969
theorem B4728833 : Blo 2101435 4728833 := bstep (se 2 (by rfl) ⟨1773312, by rfl⟩ : syracuseStep 4728833 = 3546625) B3546625
theorem B3152555 : Blo 2101435 3152555 := bstep (se 1 (by rfl) ⟨2364416, by rfl⟩ : syracuseStep 3152555 = 4728833) B4728833
theorem B2101703 : Blo 2101435 2101703 := bstep (se 1 (by rfl) ⟨1576277, by rfl⟩ : syracuseStep 2101703 = 3152555) B3152555
theorem B2364421 : Blo 2101435 2364421 := bbase (se 4 (by rfl) ⟨221664, by rfl⟩ : syracuseStep 2364421 = 443329) (by norm_num)
theorem B3152561 : Blo 2101435 3152561 := bstep (se 2 (by rfl) ⟨1182210, by rfl⟩ : syracuseStep 3152561 = 2364421) B2364421
theorem B2101707 : Blo 2101435 2101707 := bstep (se 1 (by rfl) ⟨1576280, by rfl⟩ : syracuseStep 2101707 = 3152561) B3152561
theorem B2992477 : Blo 2101435 2992477 := bbase (se 3 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 2992477 = 1122179) (by norm_num)
theorem B3989969 : Blo 2101435 3989969 := bstep (se 2 (by rfl) ⟨1496238, by rfl⟩ : syracuseStep 3989969 = 2992477) B2992477
theorem B2659979 : Blo 2101435 2659979 := bstep (se 1 (by rfl) ⟨1994984, by rfl⟩ : syracuseStep 2659979 = 3989969) B3989969
theorem B7093277 : Blo 2101435 7093277 := bstep (se 3 (by rfl) ⟨1329989, by rfl⟩ : syracuseStep 7093277 = 2659979) B2659979
theorem B4728851 : Blo 2101435 4728851 := bstep (se 1 (by rfl) ⟨3546638, by rfl⟩ : syracuseStep 4728851 = 7093277) B7093277
theorem B3152567 : Blo 2101435 3152567 := bstep (se 1 (by rfl) ⟨2364425, by rfl⟩ : syracuseStep 3152567 = 4728851) B4728851
theorem B2101711 : Blo 2101435 2101711 := bstep (se 1 (by rfl) ⟨1576283, by rfl⟩ : syracuseStep 2101711 = 3152567) B3152567
theorem B3152573 : Blo 2101435 3152573 := bbase (se 3 (by rfl) ⟨591107, by rfl⟩ : syracuseStep 3152573 = 1182215) (by norm_num)
theorem B2101715 : Blo 2101435 2101715 := bstep (se 1 (by rfl) ⟨1576286, by rfl⟩ : syracuseStep 2101715 = 3152573) B3152573
theorem B4728869 : Blo 2101435 4728869 := bbase (se 4 (by rfl) ⟨443331, by rfl⟩ : syracuseStep 4728869 = 886663) (by norm_num)
theorem B3152579 : Blo 2101435 3152579 := bstep (se 1 (by rfl) ⟨2364434, by rfl⟩ : syracuseStep 3152579 = 4728869) B4728869
theorem B2101719 : Blo 2101435 2101719 := bstep (se 1 (by rfl) ⟨1576289, by rfl⟩ : syracuseStep 2101719 = 3152579) B3152579
theorem B5319989 : Blo 2101435 5319989 := bbase (se 5 (by rfl) ⟨249374, by rfl⟩ : syracuseStep 5319989 = 498749) (by norm_num)
theorem B3546659 : Blo 2101435 3546659 := bstep (se 1 (by rfl) ⟨2659994, by rfl⟩ : syracuseStep 3546659 = 5319989) B5319989
theorem B2364439 : Blo 2101435 2364439 := bstep (se 1 (by rfl) ⟨1773329, by rfl⟩ : syracuseStep 2364439 = 3546659) B3546659
theorem B3152585 : Blo 2101435 3152585 := bstep (se 2 (by rfl) ⟨1182219, by rfl⟩ : syracuseStep 3152585 = 2364439) B2364439
theorem B2101723 : Blo 2101435 2101723 := bstep (se 1 (by rfl) ⟨1576292, by rfl⟩ : syracuseStep 2101723 = 3152585) B3152585
theorem B2879293 : Blo 2101435 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B3839057 : Blo 2101435 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B2559371 : Blo 2101435 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B6824989 : Blo 2101435 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B9099985 : Blo 2101435 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B12133313 : Blo 2101435 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B8088875 : Blo 2101435 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B5392583 : Blo 2101435 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B3595055 : Blo 2101435 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B38347253 : Blo 2101435 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B25564835 : Blo 2101435 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B17043223 : Blo 2101435 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B22724297 : Blo 2101435 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B15149531 : Blo 2101435 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B10099687 : Blo 2101435 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B13466249 : Blo 2101435 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B8977499 : Blo 2101435 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B5984999 : Blo 2101435 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B3989999 : Blo 2101435 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B10639997 : Blo 2101435 10639997 := bstep (se 3 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 10639997 = 3989999) B3989999
theorem B7093331 : Blo 2101435 7093331 := bstep (se 1 (by rfl) ⟨5319998, by rfl⟩ : syracuseStep 7093331 = 10639997) B10639997
theorem B4728887 : Blo 2101435 4728887 := bstep (se 1 (by rfl) ⟨3546665, by rfl⟩ : syracuseStep 4728887 = 7093331) B7093331
theorem B3152591 : Blo 2101435 3152591 := bstep (se 1 (by rfl) ⟨2364443, by rfl⟩ : syracuseStep 3152591 = 4728887) B4728887
theorem B2101727 : Blo 2101435 2101727 := bstep (se 1 (by rfl) ⟨1576295, by rfl⟩ : syracuseStep 2101727 = 3152591) B3152591
theorem B3152597 : Blo 2101435 3152597 := bbase (se 7 (by rfl) ⟨36944, by rfl⟩ : syracuseStep 3152597 = 73889) (by norm_num)
theorem B2101731 : Blo 2101435 2101731 := bstep (se 1 (by rfl) ⟨1576298, by rfl⟩ : syracuseStep 2101731 = 3152597) B3152597
theorem B2396713 : Blo 2101435 2396713 := bbase (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) (by norm_num)
theorem B3195617 : Blo 2101435 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B34086581 : Blo 2101435 34086581 := bstep (se 5 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 34086581 = 3195617) B3195617
theorem B22724387 : Blo 2101435 22724387 := bstep (se 1 (by rfl) ⟨17043290, by rfl⟩ : syracuseStep 22724387 = 34086581) B34086581
theorem B15149591 : Blo 2101435 15149591 := bstep (se 1 (by rfl) ⟨11362193, by rfl⟩ : syracuseStep 15149591 = 22724387) B22724387
theorem B10099727 : Blo 2101435 10099727 := bstep (se 1 (by rfl) ⟨7574795, by rfl⟩ : syracuseStep 10099727 = 15149591) B15149591
theorem B6733151 : Blo 2101435 6733151 := bstep (se 1 (by rfl) ⟨5049863, by rfl⟩ : syracuseStep 6733151 = 10099727) B10099727
theorem B4488767 : Blo 2101435 4488767 := bstep (se 1 (by rfl) ⟨3366575, by rfl⟩ : syracuseStep 4488767 = 6733151) B6733151
theorem B2992511 : Blo 2101435 2992511 := bstep (se 1 (by rfl) ⟨2244383, by rfl⟩ : syracuseStep 2992511 = 4488767) B4488767
theorem B7980029 : Blo 2101435 7980029 := bstep (se 3 (by rfl) ⟨1496255, by rfl⟩ : syracuseStep 7980029 = 2992511) B2992511
theorem B5320019 : Blo 2101435 5320019 := bstep (se 1 (by rfl) ⟨3990014, by rfl⟩ : syracuseStep 5320019 = 7980029) B7980029
theorem B3546679 : Blo 2101435 3546679 := bstep (se 1 (by rfl) ⟨2660009, by rfl⟩ : syracuseStep 3546679 = 5320019) B5320019
theorem B4728905 : Blo 2101435 4728905 := bstep (se 2 (by rfl) ⟨1773339, by rfl⟩ : syracuseStep 4728905 = 3546679) B3546679
theorem B3152603 : Blo 2101435 3152603 := bstep (se 1 (by rfl) ⟨2364452, by rfl⟩ : syracuseStep 3152603 = 4728905) B4728905
theorem B2101735 : Blo 2101435 2101735 := bstep (se 1 (by rfl) ⟨1576301, by rfl⟩ : syracuseStep 2101735 = 3152603) B3152603
theorem B2364457 : Blo 2101435 2364457 := bbase (se 2 (by rfl) ⟨886671, by rfl⟩ : syracuseStep 2364457 = 1773343) (by norm_num)
theorem B3152609 : Blo 2101435 3152609 := bstep (se 2 (by rfl) ⟨1182228, by rfl⟩ : syracuseStep 3152609 = 2364457) B2364457
theorem B2101739 : Blo 2101435 2101739 := bstep (se 1 (by rfl) ⟨1576304, by rfl⟩ : syracuseStep 2101739 = 3152609) B3152609
theorem B2275013 : Blo 2101435 2275013 := bbase (se 4 (by rfl) ⟨213282, by rfl⟩ : syracuseStep 2275013 = 426565) (by norm_num)
theorem B6066701 : Blo 2101435 6066701 := bstep (se 3 (by rfl) ⟨1137506, by rfl⟩ : syracuseStep 6066701 = 2275013) B2275013
theorem B64711477 : Blo 2101435 64711477 := bstep (se 5 (by rfl) ⟨3033350, by rfl⟩ : syracuseStep 64711477 = 6066701) B6066701
theorem B86281969 : Blo 2101435 86281969 := bstep (se 2 (by rfl) ⟨32355738, by rfl⟩ : syracuseStep 86281969 = 64711477) B64711477
theorem B115042625 : Blo 2101435 115042625 := bstep (se 2 (by rfl) ⟨43140984, by rfl⟩ : syracuseStep 115042625 = 86281969) B86281969
theorem B76695083 : Blo 2101435 76695083 := bstep (se 1 (by rfl) ⟨57521312, by rfl⟩ : syracuseStep 76695083 = 115042625) B115042625
theorem B51130055 : Blo 2101435 51130055 := bstep (se 1 (by rfl) ⟨38347541, by rfl⟩ : syracuseStep 51130055 = 76695083) B76695083
theorem B34086703 : Blo 2101435 34086703 := bstep (se 1 (by rfl) ⟨25565027, by rfl⟩ : syracuseStep 34086703 = 51130055) B51130055
theorem B45448937 : Blo 2101435 45448937 := bstep (se 2 (by rfl) ⟨17043351, by rfl⟩ : syracuseStep 45448937 = 34086703) B34086703
theorem B30299291 : Blo 2101435 30299291 := bstep (se 1 (by rfl) ⟨22724468, by rfl⟩ : syracuseStep 30299291 = 45448937) B45448937
theorem B20199527 : Blo 2101435 20199527 := bstep (se 1 (by rfl) ⟨15149645, by rfl⟩ : syracuseStep 20199527 = 30299291) B30299291
theorem B13466351 : Blo 2101435 13466351 := bstep (se 1 (by rfl) ⟨10099763, by rfl⟩ : syracuseStep 13466351 = 20199527) B20199527
theorem B8977567 : Blo 2101435 8977567 := bstep (se 1 (by rfl) ⟨6733175, by rfl⟩ : syracuseStep 8977567 = 13466351) B13466351
theorem B11970089 : Blo 2101435 11970089 := bstep (se 2 (by rfl) ⟨4488783, by rfl⟩ : syracuseStep 11970089 = 8977567) B8977567
theorem B7980059 : Blo 2101435 7980059 := bstep (se 1 (by rfl) ⟨5985044, by rfl⟩ : syracuseStep 7980059 = 11970089) B11970089
theorem B5320039 : Blo 2101435 5320039 := bstep (se 1 (by rfl) ⟨3990029, by rfl⟩ : syracuseStep 5320039 = 7980059) B7980059
theorem B7093385 : Blo 2101435 7093385 := bstep (se 2 (by rfl) ⟨2660019, by rfl⟩ : syracuseStep 7093385 = 5320039) B5320039
theorem B4728923 : Blo 2101435 4728923 := bstep (se 1 (by rfl) ⟨3546692, by rfl⟩ : syracuseStep 4728923 = 7093385) B7093385
theorem B3152615 : Blo 2101435 3152615 := bstep (se 1 (by rfl) ⟨2364461, by rfl⟩ : syracuseStep 3152615 = 4728923) B4728923
theorem B2101743 : Blo 2101435 2101743 := bstep (se 1 (by rfl) ⟨1576307, by rfl⟩ : syracuseStep 2101743 = 3152615) B3152615
theorem B3152621 : Blo 2101435 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B2101747 : Blo 2101435 2101747 := bstep (se 1 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 2101747 = 3152621) B3152621
theorem B4728941 : Blo 2101435 4728941 := bbase (se 3 (by rfl) ⟨886676, by rfl⟩ : syracuseStep 4728941 = 1773353) (by norm_num)
theorem B3152627 : Blo 2101435 3152627 := bstep (se 1 (by rfl) ⟨2364470, by rfl⟩ : syracuseStep 3152627 = 4728941) B4728941
theorem B2101751 : Blo 2101435 2101751 := bstep (se 1 (by rfl) ⟨1576313, by rfl⟩ : syracuseStep 2101751 = 3152627) B3152627
theorem B3990053 : Blo 2101435 3990053 := bbase (se 4 (by rfl) ⟨374067, by rfl⟩ : syracuseStep 3990053 = 748135) (by norm_num)
theorem B2660035 : Blo 2101435 2660035 := bstep (se 1 (by rfl) ⟨1995026, by rfl⟩ : syracuseStep 2660035 = 3990053) B3990053
theorem B3546713 : Blo 2101435 3546713 := bstep (se 2 (by rfl) ⟨1330017, by rfl⟩ : syracuseStep 3546713 = 2660035) B2660035
theorem B2364475 : Blo 2101435 2364475 := bstep (se 1 (by rfl) ⟨1773356, by rfl⟩ : syracuseStep 2364475 = 3546713) B3546713
theorem B3152633 : Blo 2101435 3152633 := bstep (se 2 (by rfl) ⟨1182237, by rfl⟩ : syracuseStep 3152633 = 2364475) B2364475
theorem B2101755 : Blo 2101435 2101755 := bstep (se 1 (by rfl) ⟨1576316, by rfl⟩ : syracuseStep 2101755 = 3152633) B3152633
theorem B21864949 : Blo 2101435 21864949 := bbase (se 5 (by rfl) ⟨1024919, by rfl⟩ : syracuseStep 21864949 = 2049839) (by norm_num)
theorem B466452245 : Blo 2101435 466452245 := bstep (se 6 (by rfl) ⟨10932474, by rfl⟩ : syracuseStep 466452245 = 21864949) B21864949
theorem B310968163 : Blo 2101435 310968163 := bstep (se 1 (by rfl) ⟨233226122, by rfl⟩ : syracuseStep 310968163 = 466452245) B466452245
theorem B414624217 : Blo 2101435 414624217 := bstep (se 2 (by rfl) ⟨155484081, by rfl⟩ : syracuseStep 414624217 = 310968163) B310968163
theorem B552832289 : Blo 2101435 552832289 := bstep (se 2 (by rfl) ⟨207312108, by rfl⟩ : syracuseStep 552832289 = 414624217) B414624217
theorem B368554859 : Blo 2101435 368554859 := bstep (se 1 (by rfl) ⟨276416144, by rfl⟩ : syracuseStep 368554859 = 552832289) B552832289
theorem B245703239 : Blo 2101435 245703239 := bstep (se 1 (by rfl) ⟨184277429, by rfl⟩ : syracuseStep 245703239 = 368554859) B368554859
theorem B163802159 : Blo 2101435 163802159 := bstep (se 1 (by rfl) ⟨122851619, by rfl⟩ : syracuseStep 163802159 = 245703239) B245703239
theorem B109201439 : Blo 2101435 109201439 := bstep (se 1 (by rfl) ⟨81901079, by rfl⟩ : syracuseStep 109201439 = 163802159) B163802159
theorem B72800959 : Blo 2101435 72800959 := bstep (se 1 (by rfl) ⟨54600719, by rfl⟩ : syracuseStep 72800959 = 109201439) B109201439
theorem B97067945 : Blo 2101435 97067945 := bstep (se 2 (by rfl) ⟨36400479, by rfl⟩ : syracuseStep 97067945 = 72800959) B72800959
theorem B64711963 : Blo 2101435 64711963 := bstep (se 1 (by rfl) ⟨48533972, by rfl⟩ : syracuseStep 64711963 = 97067945) B97067945
theorem B86282617 : Blo 2101435 86282617 := bstep (se 2 (by rfl) ⟨32355981, by rfl⟩ : syracuseStep 86282617 = 64711963) B64711963
theorem B115043489 : Blo 2101435 115043489 := bstep (se 2 (by rfl) ⟨43141308, by rfl⟩ : syracuseStep 115043489 = 86282617) B86282617
theorem B76695659 : Blo 2101435 76695659 := bstep (se 1 (by rfl) ⟨57521744, by rfl⟩ : syracuseStep 76695659 = 115043489) B115043489
theorem B51130439 : Blo 2101435 51130439 := bstep (se 1 (by rfl) ⟨38347829, by rfl⟩ : syracuseStep 51130439 = 76695659) B76695659
theorem B34086959 : Blo 2101435 34086959 := bstep (se 1 (by rfl) ⟨25565219, by rfl⟩ : syracuseStep 34086959 = 51130439) B51130439
theorem B22724639 : Blo 2101435 22724639 := bstep (se 1 (by rfl) ⟨17043479, by rfl⟩ : syracuseStep 22724639 = 34086959) B34086959
theorem B15149759 : Blo 2101435 15149759 := bstep (se 1 (by rfl) ⟨11362319, by rfl⟩ : syracuseStep 15149759 = 22724639) B22724639
theorem B40399357 : Blo 2101435 40399357 := bstep (se 3 (by rfl) ⟨7574879, by rfl⟩ : syracuseStep 40399357 = 15149759) B15149759
theorem B53865809 : Blo 2101435 53865809 := bstep (se 2 (by rfl) ⟨20199678, by rfl⟩ : syracuseStep 53865809 = 40399357) B40399357
theorem B35910539 : Blo 2101435 35910539 := bstep (se 1 (by rfl) ⟨26932904, by rfl⟩ : syracuseStep 35910539 = 53865809) B53865809
theorem B23940359 : Blo 2101435 23940359 := bstep (se 1 (by rfl) ⟨17955269, by rfl⟩ : syracuseStep 23940359 = 35910539) B35910539
theorem B15960239 : Blo 2101435 15960239 := bstep (se 1 (by rfl) ⟨11970179, by rfl⟩ : syracuseStep 15960239 = 23940359) B23940359
theorem B10640159 : Blo 2101435 10640159 := bstep (se 1 (by rfl) ⟨7980119, by rfl⟩ : syracuseStep 10640159 = 15960239) B15960239
theorem B7093439 : Blo 2101435 7093439 := bstep (se 1 (by rfl) ⟨5320079, by rfl⟩ : syracuseStep 7093439 = 10640159) B10640159
theorem B4728959 : Blo 2101435 4728959 := bstep (se 1 (by rfl) ⟨3546719, by rfl⟩ : syracuseStep 4728959 = 7093439) B7093439
theorem B3152639 : Blo 2101435 3152639 := bstep (se 1 (by rfl) ⟨2364479, by rfl⟩ : syracuseStep 3152639 = 4728959) B4728959
theorem B2101759 : Blo 2101435 2101759 := bstep (se 1 (by rfl) ⟨1576319, by rfl⟩ : syracuseStep 2101759 = 3152639) B3152639
theorem B3152645 : Blo 2101435 3152645 := bbase (se 4 (by rfl) ⟨295560, by rfl⟩ : syracuseStep 3152645 = 591121) (by norm_num)
theorem B2101763 : Blo 2101435 2101763 := bstep (se 1 (by rfl) ⟨1576322, by rfl⟩ : syracuseStep 2101763 = 3152645) B3152645
theorem B3546733 : Blo 2101435 3546733 := bbase (se 3 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 3546733 = 1330025) (by norm_num)
theorem B4728977 : Blo 2101435 4728977 := bstep (se 2 (by rfl) ⟨1773366, by rfl⟩ : syracuseStep 4728977 = 3546733) B3546733
theorem B3152651 : Blo 2101435 3152651 := bstep (se 1 (by rfl) ⟨2364488, by rfl⟩ : syracuseStep 3152651 = 4728977) B4728977
theorem B2101767 : Blo 2101435 2101767 := bstep (se 1 (by rfl) ⟨1576325, by rfl⟩ : syracuseStep 2101767 = 3152651) B3152651
theorem B2364493 : Blo 2101435 2364493 := bbase (se 3 (by rfl) ⟨443342, by rfl⟩ : syracuseStep 2364493 = 886685) (by norm_num)
theorem B3152657 : Blo 2101435 3152657 := bstep (se 2 (by rfl) ⟨1182246, by rfl⟩ : syracuseStep 3152657 = 2364493) B2364493
theorem B2101771 : Blo 2101435 2101771 := bstep (se 1 (by rfl) ⟨1576328, by rfl⟩ : syracuseStep 2101771 = 3152657) B3152657
theorem B7093493 : Blo 2101435 7093493 := bbase (se 5 (by rfl) ⟨332507, by rfl⟩ : syracuseStep 7093493 = 665015) (by norm_num)
theorem B4728995 : Blo 2101435 4728995 := bstep (se 1 (by rfl) ⟨3546746, by rfl⟩ : syracuseStep 4728995 = 7093493) B7093493
theorem B3152663 : Blo 2101435 3152663 := bstep (se 1 (by rfl) ⟨2364497, by rfl⟩ : syracuseStep 3152663 = 4728995) B4728995
theorem B2101775 : Blo 2101435 2101775 := bstep (se 1 (by rfl) ⟨1576331, by rfl⟩ : syracuseStep 2101775 = 3152663) B3152663
theorem B3152669 : Blo 2101435 3152669 := bbase (se 3 (by rfl) ⟨591125, by rfl⟩ : syracuseStep 3152669 = 1182251) (by norm_num)
theorem B2101779 : Blo 2101435 2101779 := bstep (se 1 (by rfl) ⟨1576334, by rfl⟩ : syracuseStep 2101779 = 3152669) B3152669
theorem B4729013 : Blo 2101435 4729013 := bbase (se 5 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 4729013 = 443345) (by norm_num)
theorem B3152675 : Blo 2101435 3152675 := bstep (se 1 (by rfl) ⟨2364506, by rfl⟩ : syracuseStep 3152675 = 4729013) B4729013
theorem B2101783 : Blo 2101435 2101783 := bstep (se 1 (by rfl) ⟨1576337, by rfl⟩ : syracuseStep 2101783 = 3152675) B3152675
theorem B5049989 : Blo 2101435 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B3366659 : Blo 2101435 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B2244439 : Blo 2101435 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B11970341 : Blo 2101435 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B7980227 : Blo 2101435 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B5320151 : Blo 2101435 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B3546767 : Blo 2101435 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B2364511 : Blo 2101435 2364511 := bstep (se 1 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 2364511 = 3546767) B3546767
theorem B3152681 : Blo 2101435 3152681 := bstep (se 2 (by rfl) ⟨1182255, by rfl⟩ : syracuseStep 3152681 = 2364511) B2364511
theorem B2101787 : Blo 2101435 2101787 := bstep (se 1 (by rfl) ⟨1576340, by rfl⟩ : syracuseStep 2101787 = 3152681) B3152681
theorem B6478613 : Blo 2101435 6478613 := bbase (se 6 (by rfl) ⟨151842, by rfl⟩ : syracuseStep 6478613 = 303685) (by norm_num)
theorem B4319075 : Blo 2101435 4319075 := bstep (se 1 (by rfl) ⟨3239306, by rfl⟩ : syracuseStep 4319075 = 6478613) B6478613
theorem B2879383 : Blo 2101435 2879383 := bstep (se 1 (by rfl) ⟨2159537, by rfl⟩ : syracuseStep 2879383 = 4319075) B4319075
theorem B3839177 : Blo 2101435 3839177 := bstep (se 2 (by rfl) ⟨1439691, by rfl⟩ : syracuseStep 3839177 = 2879383) B2879383
theorem B2559451 : Blo 2101435 2559451 := bstep (se 1 (by rfl) ⟨1919588, by rfl⟩ : syracuseStep 2559451 = 3839177) B3839177
theorem B3412601 : Blo 2101435 3412601 := bstep (se 2 (by rfl) ⟨1279725, by rfl⟩ : syracuseStep 3412601 = 2559451) B2559451
theorem B2275067 : Blo 2101435 2275067 := bstep (se 1 (by rfl) ⟨1706300, by rfl⟩ : syracuseStep 2275067 = 3412601) B3412601
theorem B6066845 : Blo 2101435 6066845 := bstep (se 3 (by rfl) ⟨1137533, by rfl⟩ : syracuseStep 6066845 = 2275067) B2275067
theorem B4044563 : Blo 2101435 4044563 := bstep (se 1 (by rfl) ⟨3033422, by rfl⟩ : syracuseStep 4044563 = 6066845) B6066845
theorem B2696375 : Blo 2101435 2696375 := bstep (se 1 (by rfl) ⟨2022281, by rfl⟩ : syracuseStep 2696375 = 4044563) B4044563
theorem B7190333 : Blo 2101435 7190333 := bstep (se 3 (by rfl) ⟨1348187, by rfl⟩ : syracuseStep 7190333 = 2696375) B2696375
theorem B4793555 : Blo 2101435 4793555 := bstep (se 1 (by rfl) ⟨3595166, by rfl⟩ : syracuseStep 4793555 = 7190333) B7190333
theorem B3195703 : Blo 2101435 3195703 := bstep (se 1 (by rfl) ⟨2396777, by rfl⟩ : syracuseStep 3195703 = 4793555) B4793555
theorem B4260937 : Blo 2101435 4260937 := bstep (se 2 (by rfl) ⟨1597851, by rfl⟩ : syracuseStep 4260937 = 3195703) B3195703
theorem B5681249 : Blo 2101435 5681249 := bstep (se 2 (by rfl) ⟨2130468, by rfl⟩ : syracuseStep 5681249 = 4260937) B4260937
theorem B3787499 : Blo 2101435 3787499 := bstep (se 1 (by rfl) ⟨2840624, by rfl⟩ : syracuseStep 3787499 = 5681249) B5681249
theorem B2524999 : Blo 2101435 2524999 := bstep (se 1 (by rfl) ⟨1893749, by rfl⟩ : syracuseStep 2524999 = 3787499) B3787499
theorem B3366665 : Blo 2101435 3366665 := bstep (se 2 (by rfl) ⟨1262499, by rfl⟩ : syracuseStep 3366665 = 2524999) B2524999
theorem B2244443 : Blo 2101435 2244443 := bstep (se 1 (by rfl) ⟨1683332, by rfl⟩ : syracuseStep 2244443 = 3366665) B3366665
theorem B5985181 : Blo 2101435 5985181 := bstep (se 3 (by rfl) ⟨1122221, by rfl⟩ : syracuseStep 5985181 = 2244443) B2244443
theorem B7980241 : Blo 2101435 7980241 := bstep (se 2 (by rfl) ⟨2992590, by rfl⟩ : syracuseStep 7980241 = 5985181) B5985181
theorem B10640321 : Blo 2101435 10640321 := bstep (se 2 (by rfl) ⟨3990120, by rfl⟩ : syracuseStep 10640321 = 7980241) B7980241
theorem B7093547 : Blo 2101435 7093547 := bstep (se 1 (by rfl) ⟨5320160, by rfl⟩ : syracuseStep 7093547 = 10640321) B10640321
theorem B4729031 : Blo 2101435 4729031 := bstep (se 1 (by rfl) ⟨3546773, by rfl⟩ : syracuseStep 4729031 = 7093547) B7093547
theorem B3152687 : Blo 2101435 3152687 := bstep (se 1 (by rfl) ⟨2364515, by rfl⟩ : syracuseStep 3152687 = 4729031) B4729031
theorem B2101791 : Blo 2101435 2101791 := bstep (se 1 (by rfl) ⟨1576343, by rfl⟩ : syracuseStep 2101791 = 3152687) B3152687
theorem B3152693 : Blo 2101435 3152693 := bbase (se 5 (by rfl) ⟨147782, by rfl⟩ : syracuseStep 3152693 = 295565) (by norm_num)
theorem B2101795 : Blo 2101435 2101795 := bstep (se 1 (by rfl) ⟨1576346, by rfl⟩ : syracuseStep 2101795 = 3152693) B3152693
theorem B5320181 : Blo 2101435 5320181 := bbase (se 5 (by rfl) ⟨249383, by rfl⟩ : syracuseStep 5320181 = 498767) (by norm_num)
theorem B3546787 : Blo 2101435 3546787 := bstep (se 1 (by rfl) ⟨2660090, by rfl⟩ : syracuseStep 3546787 = 5320181) B5320181
theorem B4729049 : Blo 2101435 4729049 := bstep (se 2 (by rfl) ⟨1773393, by rfl⟩ : syracuseStep 4729049 = 3546787) B3546787
theorem B3152699 : Blo 2101435 3152699 := bstep (se 1 (by rfl) ⟨2364524, by rfl⟩ : syracuseStep 3152699 = 4729049) B4729049
theorem B2101799 : Blo 2101435 2101799 := bstep (se 1 (by rfl) ⟨1576349, by rfl⟩ : syracuseStep 2101799 = 3152699) B3152699
theorem B2364529 : Blo 2101435 2364529 := bbase (se 2 (by rfl) ⟨886698, by rfl⟩ : syracuseStep 2364529 = 1773397) (by norm_num)
theorem B3152705 : Blo 2101435 3152705 := bstep (se 2 (by rfl) ⟨1182264, by rfl⟩ : syracuseStep 3152705 = 2364529) B2364529
theorem B2101803 : Blo 2101435 2101803 := bstep (se 1 (by rfl) ⟨1576352, by rfl⟩ : syracuseStep 2101803 = 3152705) B3152705
theorem B6733381 : Blo 2101435 6733381 := bbase (se 4 (by rfl) ⟨631254, by rfl⟩ : syracuseStep 6733381 = 1262509) (by norm_num)
theorem B8977841 : Blo 2101435 8977841 := bstep (se 2 (by rfl) ⟨3366690, by rfl⟩ : syracuseStep 8977841 = 6733381) B6733381
theorem B5985227 : Blo 2101435 5985227 := bstep (se 1 (by rfl) ⟨4488920, by rfl⟩ : syracuseStep 5985227 = 8977841) B8977841
theorem B3990151 : Blo 2101435 3990151 := bstep (se 1 (by rfl) ⟨2992613, by rfl⟩ : syracuseStep 3990151 = 5985227) B5985227
theorem B5320201 : Blo 2101435 5320201 := bstep (se 2 (by rfl) ⟨1995075, by rfl⟩ : syracuseStep 5320201 = 3990151) B3990151
theorem B7093601 : Blo 2101435 7093601 := bstep (se 2 (by rfl) ⟨2660100, by rfl⟩ : syracuseStep 7093601 = 5320201) B5320201
theorem B4729067 : Blo 2101435 4729067 := bstep (se 1 (by rfl) ⟨3546800, by rfl⟩ : syracuseStep 4729067 = 7093601) B7093601
theorem B3152711 : Blo 2101435 3152711 := bstep (se 1 (by rfl) ⟨2364533, by rfl⟩ : syracuseStep 3152711 = 4729067) B4729067
theorem B2101807 : Blo 2101435 2101807 := bstep (se 1 (by rfl) ⟨1576355, by rfl⟩ : syracuseStep 2101807 = 3152711) B3152711
theorem B3152717 : Blo 2101435 3152717 := bbase (se 3 (by rfl) ⟨591134, by rfl⟩ : syracuseStep 3152717 = 1182269) (by norm_num)
theorem B2101811 : Blo 2101435 2101811 := bstep (se 1 (by rfl) ⟨1576358, by rfl⟩ : syracuseStep 2101811 = 3152717) B3152717
theorem B4729085 : Blo 2101435 4729085 := bbase (se 3 (by rfl) ⟨886703, by rfl⟩ : syracuseStep 4729085 = 1773407) (by norm_num)
theorem B3152723 : Blo 2101435 3152723 := bstep (se 1 (by rfl) ⟨2364542, by rfl⟩ : syracuseStep 3152723 = 4729085) B4729085
theorem B2101815 : Blo 2101435 2101815 := bstep (se 1 (by rfl) ⟨1576361, by rfl⟩ : syracuseStep 2101815 = 3152723) B3152723
theorem B3546821 : Blo 2101435 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2364547 : Blo 2101435 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3152729 : Blo 2101435 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B2101819 : Blo 2101435 2101819 := bstep (se 1 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 2101819 = 3152729) B3152729
theorem B15960725 : Blo 2101435 15960725 := bbase (se 6 (by rfl) ⟨374079, by rfl⟩ : syracuseStep 15960725 = 748159) (by norm_num)
theorem B10640483 : Blo 2101435 10640483 := bstep (se 1 (by rfl) ⟨7980362, by rfl⟩ : syracuseStep 10640483 = 15960725) B15960725
theorem B7093655 : Blo 2101435 7093655 := bstep (se 1 (by rfl) ⟨5320241, by rfl⟩ : syracuseStep 7093655 = 10640483) B10640483
theorem B4729103 : Blo 2101435 4729103 := bstep (se 1 (by rfl) ⟨3546827, by rfl⟩ : syracuseStep 4729103 = 7093655) B7093655
theorem B3152735 : Blo 2101435 3152735 := bstep (se 1 (by rfl) ⟨2364551, by rfl⟩ : syracuseStep 3152735 = 4729103) B4729103
theorem B2101823 : Blo 2101435 2101823 := bstep (se 1 (by rfl) ⟨1576367, by rfl⟩ : syracuseStep 2101823 = 3152735) B3152735
theorem B3152741 : Blo 2101435 3152741 := bbase (se 4 (by rfl) ⟨295569, by rfl⟩ : syracuseStep 3152741 = 591139) (by norm_num)
theorem B2101827 : Blo 2101435 2101827 := bstep (se 1 (by rfl) ⟨1576370, by rfl⟩ : syracuseStep 2101827 = 3152741) B3152741
theorem B3990197 : Blo 2101435 3990197 := bbase (se 5 (by rfl) ⟨187040, by rfl⟩ : syracuseStep 3990197 = 374081) (by norm_num)
theorem B2660131 : Blo 2101435 2660131 := bstep (se 1 (by rfl) ⟨1995098, by rfl⟩ : syracuseStep 2660131 = 3990197) B3990197
theorem B3546841 : Blo 2101435 3546841 := bstep (se 2 (by rfl) ⟨1330065, by rfl⟩ : syracuseStep 3546841 = 2660131) B2660131
theorem B4729121 : Blo 2101435 4729121 := bstep (se 2 (by rfl) ⟨1773420, by rfl⟩ : syracuseStep 4729121 = 3546841) B3546841
theorem B3152747 : Blo 2101435 3152747 := bstep (se 1 (by rfl) ⟨2364560, by rfl⟩ : syracuseStep 3152747 = 4729121) B4729121
theorem B2101831 : Blo 2101435 2101831 := bstep (se 1 (by rfl) ⟨1576373, by rfl⟩ : syracuseStep 2101831 = 3152747) B3152747
theorem B2364565 : Blo 2101435 2364565 := bbase (se 6 (by rfl) ⟨55419, by rfl⟩ : syracuseStep 2364565 = 110839) (by norm_num)
theorem B3152753 : Blo 2101435 3152753 := bstep (se 2 (by rfl) ⟨1182282, by rfl⟩ : syracuseStep 3152753 = 2364565) B2364565
theorem B2101835 : Blo 2101435 2101835 := bstep (se 1 (by rfl) ⟨1576376, by rfl⟩ : syracuseStep 2101835 = 3152753) B3152753
theorem B2660141 : Blo 2101435 2660141 := bbase (se 3 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 2660141 = 997553) (by norm_num)
theorem B7093709 : Blo 2101435 7093709 := bstep (se 3 (by rfl) ⟨1330070, by rfl⟩ : syracuseStep 7093709 = 2660141) B2660141
theorem B4729139 : Blo 2101435 4729139 := bstep (se 1 (by rfl) ⟨3546854, by rfl⟩ : syracuseStep 4729139 = 7093709) B7093709
theorem B3152759 : Blo 2101435 3152759 := bstep (se 1 (by rfl) ⟨2364569, by rfl⟩ : syracuseStep 3152759 = 4729139) B4729139
theorem B2101839 : Blo 2101435 2101839 := bstep (se 1 (by rfl) ⟨1576379, by rfl⟩ : syracuseStep 2101839 = 3152759) B3152759
theorem B3152765 : Blo 2101435 3152765 := bbase (se 3 (by rfl) ⟨591143, by rfl⟩ : syracuseStep 3152765 = 1182287) (by norm_num)
theorem B2101843 : Blo 2101435 2101843 := bstep (se 1 (by rfl) ⟨1576382, by rfl⟩ : syracuseStep 2101843 = 3152765) B3152765
theorem B4729157 : Blo 2101435 4729157 := bbase (se 4 (by rfl) ⟨443358, by rfl⟩ : syracuseStep 4729157 = 886717) (by norm_num)
theorem B3152771 : Blo 2101435 3152771 := bstep (se 1 (by rfl) ⟨2364578, by rfl⟩ : syracuseStep 3152771 = 4729157) B4729157
theorem B2101847 : Blo 2101435 2101847 := bstep (se 1 (by rfl) ⟨1576385, by rfl⟩ : syracuseStep 2101847 = 3152771) B3152771
theorem B8522117 : Blo 2101435 8522117 := bbase (se 4 (by rfl) ⟨798948, by rfl⟩ : syracuseStep 8522117 = 1597897) (by norm_num)
theorem B5681411 : Blo 2101435 5681411 := bstep (se 1 (by rfl) ⟨4261058, by rfl⟩ : syracuseStep 5681411 = 8522117) B8522117
theorem B3787607 : Blo 2101435 3787607 := bstep (se 1 (by rfl) ⟨2840705, by rfl⟩ : syracuseStep 3787607 = 5681411) B5681411
theorem B10100285 : Blo 2101435 10100285 := bstep (se 3 (by rfl) ⟨1893803, by rfl⟩ : syracuseStep 10100285 = 3787607) B3787607
theorem B6733523 : Blo 2101435 6733523 := bstep (se 1 (by rfl) ⟨5050142, by rfl⟩ : syracuseStep 6733523 = 10100285) B10100285
theorem B4489015 : Blo 2101435 4489015 := bstep (se 1 (by rfl) ⟨3366761, by rfl⟩ : syracuseStep 4489015 = 6733523) B6733523
theorem B5985353 : Blo 2101435 5985353 := bstep (se 2 (by rfl) ⟨2244507, by rfl⟩ : syracuseStep 5985353 = 4489015) B4489015
theorem B3990235 : Blo 2101435 3990235 := bstep (se 1 (by rfl) ⟨2992676, by rfl⟩ : syracuseStep 3990235 = 5985353) B5985353
theorem B5320313 : Blo 2101435 5320313 := bstep (se 2 (by rfl) ⟨1995117, by rfl⟩ : syracuseStep 5320313 = 3990235) B3990235
theorem B3546875 : Blo 2101435 3546875 := bstep (se 1 (by rfl) ⟨2660156, by rfl⟩ : syracuseStep 3546875 = 5320313) B5320313
theorem B2364583 : Blo 2101435 2364583 := bstep (se 1 (by rfl) ⟨1773437, by rfl⟩ : syracuseStep 2364583 = 3546875) B3546875
theorem B3152777 : Blo 2101435 3152777 := bstep (se 2 (by rfl) ⟨1182291, by rfl⟩ : syracuseStep 3152777 = 2364583) B2364583
theorem B2101851 : Blo 2101435 2101851 := bstep (se 1 (by rfl) ⟨1576388, by rfl⟩ : syracuseStep 2101851 = 3152777) B3152777
theorem B10640645 : Blo 2101435 10640645 := bbase (se 4 (by rfl) ⟨997560, by rfl⟩ : syracuseStep 10640645 = 1995121) (by norm_num)
theorem B7093763 : Blo 2101435 7093763 := bstep (se 1 (by rfl) ⟨5320322, by rfl⟩ : syracuseStep 7093763 = 10640645) B10640645
theorem B4729175 : Blo 2101435 4729175 := bstep (se 1 (by rfl) ⟨3546881, by rfl⟩ : syracuseStep 4729175 = 7093763) B7093763
theorem B3152783 : Blo 2101435 3152783 := bstep (se 1 (by rfl) ⟨2364587, by rfl⟩ : syracuseStep 3152783 = 4729175) B4729175
theorem B2101855 : Blo 2101435 2101855 := bstep (se 1 (by rfl) ⟨1576391, by rfl⟩ : syracuseStep 2101855 = 3152783) B3152783
theorem B3152789 : Blo 2101435 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B2101859 : Blo 2101435 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B11970773 : Blo 2101435 11970773 := bbase (se 7 (by rfl) ⟨140282, by rfl⟩ : syracuseStep 11970773 = 280565) (by norm_num)
theorem B7980515 : Blo 2101435 7980515 := bstep (se 1 (by rfl) ⟨5985386, by rfl⟩ : syracuseStep 7980515 = 11970773) B11970773
theorem B5320343 : Blo 2101435 5320343 := bstep (se 1 (by rfl) ⟨3990257, by rfl⟩ : syracuseStep 5320343 = 7980515) B7980515
theorem B3546895 : Blo 2101435 3546895 := bstep (se 1 (by rfl) ⟨2660171, by rfl⟩ : syracuseStep 3546895 = 5320343) B5320343
theorem B4729193 : Blo 2101435 4729193 := bstep (se 2 (by rfl) ⟨1773447, by rfl⟩ : syracuseStep 4729193 = 3546895) B3546895
theorem B3152795 : Blo 2101435 3152795 := bstep (se 1 (by rfl) ⟨2364596, by rfl⟩ : syracuseStep 3152795 = 4729193) B4729193
theorem B2101863 : Blo 2101435 2101863 := bstep (se 1 (by rfl) ⟨1576397, by rfl⟩ : syracuseStep 2101863 = 3152795) B3152795
theorem B2364601 : Blo 2101435 2364601 := bbase (se 2 (by rfl) ⟨886725, by rfl⟩ : syracuseStep 2364601 = 1773451) (by norm_num)
theorem B3152801 : Blo 2101435 3152801 := bstep (se 2 (by rfl) ⟨1182300, by rfl⟩ : syracuseStep 3152801 = 2364601) B2364601
theorem B2101867 : Blo 2101435 2101867 := bstep (se 1 (by rfl) ⟨1576400, by rfl⟩ : syracuseStep 2101867 = 3152801) B3152801
theorem B9100613 : Blo 2101435 9100613 := bbase (se 4 (by rfl) ⟨853182, by rfl⟩ : syracuseStep 9100613 = 1706365) (by norm_num)
theorem B6067075 : Blo 2101435 6067075 := bstep (se 1 (by rfl) ⟨4550306, by rfl⟩ : syracuseStep 6067075 = 9100613) B9100613
theorem B8089433 : Blo 2101435 8089433 := bstep (se 2 (by rfl) ⟨3033537, by rfl⟩ : syracuseStep 8089433 = 6067075) B6067075
theorem B5392955 : Blo 2101435 5392955 := bstep (se 1 (by rfl) ⟨4044716, by rfl⟩ : syracuseStep 5392955 = 8089433) B8089433
theorem B3595303 : Blo 2101435 3595303 := bstep (se 1 (by rfl) ⟨2696477, by rfl⟩ : syracuseStep 3595303 = 5392955) B5392955
theorem B4793737 : Blo 2101435 4793737 := bstep (se 2 (by rfl) ⟨1797651, by rfl⟩ : syracuseStep 4793737 = 3595303) B3595303
theorem B6391649 : Blo 2101435 6391649 := bstep (se 2 (by rfl) ⟨2396868, by rfl⟩ : syracuseStep 6391649 = 4793737) B4793737
theorem B4261099 : Blo 2101435 4261099 := bstep (se 1 (by rfl) ⟨3195824, by rfl⟩ : syracuseStep 4261099 = 6391649) B6391649
theorem B5681465 : Blo 2101435 5681465 := bstep (se 2 (by rfl) ⟨2130549, by rfl⟩ : syracuseStep 5681465 = 4261099) B4261099
theorem B3787643 : Blo 2101435 3787643 := bstep (se 1 (by rfl) ⟨2840732, by rfl⟩ : syracuseStep 3787643 = 5681465) B5681465
theorem B2525095 : Blo 2101435 2525095 := bstep (se 1 (by rfl) ⟨1893821, by rfl⟩ : syracuseStep 2525095 = 3787643) B3787643
theorem B3366793 : Blo 2101435 3366793 := bstep (se 2 (by rfl) ⟨1262547, by rfl⟩ : syracuseStep 3366793 = 2525095) B2525095
theorem B4489057 : Blo 2101435 4489057 := bstep (se 2 (by rfl) ⟨1683396, by rfl⟩ : syracuseStep 4489057 = 3366793) B3366793
theorem B5985409 : Blo 2101435 5985409 := bstep (se 2 (by rfl) ⟨2244528, by rfl⟩ : syracuseStep 5985409 = 4489057) B4489057
theorem B7980545 : Blo 2101435 7980545 := bstep (se 2 (by rfl) ⟨2992704, by rfl⟩ : syracuseStep 7980545 = 5985409) B5985409
theorem B5320363 : Blo 2101435 5320363 := bstep (se 1 (by rfl) ⟨3990272, by rfl⟩ : syracuseStep 5320363 = 7980545) B7980545
theorem B7093817 : Blo 2101435 7093817 := bstep (se 2 (by rfl) ⟨2660181, by rfl⟩ : syracuseStep 7093817 = 5320363) B5320363
theorem B4729211 : Blo 2101435 4729211 := bstep (se 1 (by rfl) ⟨3546908, by rfl⟩ : syracuseStep 4729211 = 7093817) B7093817
theorem B3152807 : Blo 2101435 3152807 := bstep (se 1 (by rfl) ⟨2364605, by rfl⟩ : syracuseStep 3152807 = 4729211) B4729211
theorem B2101871 : Blo 2101435 2101871 := bstep (se 1 (by rfl) ⟨1576403, by rfl⟩ : syracuseStep 2101871 = 3152807) B3152807
theorem B3152813 : Blo 2101435 3152813 := bbase (se 3 (by rfl) ⟨591152, by rfl⟩ : syracuseStep 3152813 = 1182305) (by norm_num)
theorem B2101875 : Blo 2101435 2101875 := bstep (se 1 (by rfl) ⟨1576406, by rfl⟩ : syracuseStep 2101875 = 3152813) B3152813
theorem B4729229 : Blo 2101435 4729229 := bbase (se 3 (by rfl) ⟨886730, by rfl⟩ : syracuseStep 4729229 = 1773461) (by norm_num)
theorem B3152819 : Blo 2101435 3152819 := bstep (se 1 (by rfl) ⟨2364614, by rfl⟩ : syracuseStep 3152819 = 4729229) B4729229
theorem B2101879 : Blo 2101435 2101879 := bstep (se 1 (by rfl) ⟨1576409, by rfl⟩ : syracuseStep 2101879 = 3152819) B3152819
theorem B2660197 : Blo 2101435 2660197 := bbase (se 4 (by rfl) ⟨249393, by rfl⟩ : syracuseStep 2660197 = 498787) (by norm_num)
theorem B3546929 : Blo 2101435 3546929 := bstep (se 2 (by rfl) ⟨1330098, by rfl⟩ : syracuseStep 3546929 = 2660197) B2660197
theorem B2364619 : Blo 2101435 2364619 := bstep (se 1 (by rfl) ⟨1773464, by rfl⟩ : syracuseStep 2364619 = 3546929) B3546929
theorem B3152825 : Blo 2101435 3152825 := bstep (se 2 (by rfl) ⟨1182309, by rfl⟩ : syracuseStep 3152825 = 2364619) B2364619
theorem B2101883 : Blo 2101435 2101883 := bstep (se 1 (by rfl) ⟨1576412, by rfl⟩ : syracuseStep 2101883 = 3152825) B3152825
theorem B2130565 : Blo 2101435 2130565 := bbase (se 4 (by rfl) ⟨199740, by rfl⟩ : syracuseStep 2130565 = 399481) (by norm_num)
theorem B2840753 : Blo 2101435 2840753 := bstep (se 2 (by rfl) ⟨1065282, by rfl⟩ : syracuseStep 2840753 = 2130565) B2130565
theorem B7575341 : Blo 2101435 7575341 := bstep (se 3 (by rfl) ⟨1420376, by rfl⟩ : syracuseStep 7575341 = 2840753) B2840753
theorem B20200909 : Blo 2101435 20200909 := bstep (se 3 (by rfl) ⟨3787670, by rfl⟩ : syracuseStep 20200909 = 7575341) B7575341
theorem B26934545 : Blo 2101435 26934545 := bstep (se 2 (by rfl) ⟨10100454, by rfl⟩ : syracuseStep 26934545 = 20200909) B20200909
theorem B17956363 : Blo 2101435 17956363 := bstep (se 1 (by rfl) ⟨13467272, by rfl⟩ : syracuseStep 17956363 = 26934545) B26934545
theorem B23941817 : Blo 2101435 23941817 := bstep (se 2 (by rfl) ⟨8978181, by rfl⟩ : syracuseStep 23941817 = 17956363) B17956363
theorem B15961211 : Blo 2101435 15961211 := bstep (se 1 (by rfl) ⟨11970908, by rfl⟩ : syracuseStep 15961211 = 23941817) B23941817
theorem B10640807 : Blo 2101435 10640807 := bstep (se 1 (by rfl) ⟨7980605, by rfl⟩ : syracuseStep 10640807 = 15961211) B15961211
theorem B7093871 : Blo 2101435 7093871 := bstep (se 1 (by rfl) ⟨5320403, by rfl⟩ : syracuseStep 7093871 = 10640807) B10640807
theorem B4729247 : Blo 2101435 4729247 := bstep (se 1 (by rfl) ⟨3546935, by rfl⟩ : syracuseStep 4729247 = 7093871) B7093871
theorem B3152831 : Blo 2101435 3152831 := bstep (se 1 (by rfl) ⟨2364623, by rfl⟩ : syracuseStep 3152831 = 4729247) B4729247
theorem B2101887 : Blo 2101435 2101887 := bstep (se 1 (by rfl) ⟨1576415, by rfl⟩ : syracuseStep 2101887 = 3152831) B3152831
theorem B3152837 : Blo 2101435 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B2101891 : Blo 2101435 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B3546949 : Blo 2101435 3546949 := bbase (se 4 (by rfl) ⟨332526, by rfl⟩ : syracuseStep 3546949 = 665053) (by norm_num)
theorem B4729265 : Blo 2101435 4729265 := bstep (se 2 (by rfl) ⟨1773474, by rfl⟩ : syracuseStep 4729265 = 3546949) B3546949
theorem B3152843 : Blo 2101435 3152843 := bstep (se 1 (by rfl) ⟨2364632, by rfl⟩ : syracuseStep 3152843 = 4729265) B4729265
theorem B2101895 : Blo 2101435 2101895 := bstep (se 1 (by rfl) ⟨1576421, by rfl⟩ : syracuseStep 2101895 = 3152843) B3152843
theorem B2364637 : Blo 2101435 2364637 := bbase (se 3 (by rfl) ⟨443369, by rfl⟩ : syracuseStep 2364637 = 886739) (by norm_num)
theorem B3152849 : Blo 2101435 3152849 := bstep (se 2 (by rfl) ⟨1182318, by rfl⟩ : syracuseStep 3152849 = 2364637) B2364637
theorem B2101899 : Blo 2101435 2101899 := bstep (se 1 (by rfl) ⟨1576424, by rfl⟩ : syracuseStep 2101899 = 3152849) B3152849
theorem B7093925 : Blo 2101435 7093925 := bbase (se 4 (by rfl) ⟨665055, by rfl⟩ : syracuseStep 7093925 = 1330111) (by norm_num)
theorem B4729283 : Blo 2101435 4729283 := bstep (se 1 (by rfl) ⟨3546962, by rfl⟩ : syracuseStep 4729283 = 7093925) B7093925
theorem B3152855 : Blo 2101435 3152855 := bstep (se 1 (by rfl) ⟨2364641, by rfl⟩ : syracuseStep 3152855 = 4729283) B4729283
theorem B2101903 : Blo 2101435 2101903 := bstep (se 1 (by rfl) ⟨1576427, by rfl⟩ : syracuseStep 2101903 = 3152855) B3152855
theorem B3152861 : Blo 2101435 3152861 := bbase (se 3 (by rfl) ⟨591161, by rfl⟩ : syracuseStep 3152861 = 1182323) (by norm_num)
theorem B2101907 : Blo 2101435 2101907 := bstep (se 1 (by rfl) ⟨1576430, by rfl⟩ : syracuseStep 2101907 = 3152861) B3152861
theorem B4729301 : Blo 2101435 4729301 := bbase (se 7 (by rfl) ⟨55421, by rfl⟩ : syracuseStep 4729301 = 110843) (by norm_num)
theorem B3152867 : Blo 2101435 3152867 := bstep (se 1 (by rfl) ⟨2364650, by rfl⟩ : syracuseStep 3152867 = 4729301) B4729301
theorem B2101911 : Blo 2101435 2101911 := bstep (se 1 (by rfl) ⟨1576433, by rfl⟩ : syracuseStep 2101911 = 3152867) B3152867
theorem B166049365 : Blo 2101435 166049365 := bbase (se 8 (by rfl) ⟨972945, by rfl⟩ : syracuseStep 166049365 = 1945891) (by norm_num)
theorem B221399153 : Blo 2101435 221399153 := bstep (se 2 (by rfl) ⟨83024682, by rfl⟩ : syracuseStep 221399153 = 166049365) B166049365
theorem B147599435 : Blo 2101435 147599435 := bstep (se 1 (by rfl) ⟨110699576, by rfl⟩ : syracuseStep 147599435 = 221399153) B221399153
theorem B98399623 : Blo 2101435 98399623 := bstep (se 1 (by rfl) ⟨73799717, by rfl⟩ : syracuseStep 98399623 = 147599435) B147599435
theorem B131199497 : Blo 2101435 131199497 := bstep (se 2 (by rfl) ⟨49199811, by rfl⟩ : syracuseStep 131199497 = 98399623) B98399623
theorem B87466331 : Blo 2101435 87466331 := bstep (se 1 (by rfl) ⟨65599748, by rfl⟩ : syracuseStep 87466331 = 131199497) B131199497
theorem B233243549 : Blo 2101435 233243549 := bstep (se 3 (by rfl) ⟨43733165, by rfl⟩ : syracuseStep 233243549 = 87466331) B87466331
theorem B155495699 : Blo 2101435 155495699 := bstep (se 1 (by rfl) ⟨116621774, by rfl⟩ : syracuseStep 155495699 = 233243549) B233243549
theorem B103663799 : Blo 2101435 103663799 := bstep (se 1 (by rfl) ⟨77747849, by rfl⟩ : syracuseStep 103663799 = 155495699) B155495699
theorem B69109199 : Blo 2101435 69109199 := bstep (se 1 (by rfl) ⟨51831899, by rfl⟩ : syracuseStep 69109199 = 103663799) B103663799
theorem B46072799 : Blo 2101435 46072799 := bstep (se 1 (by rfl) ⟨34554599, by rfl⟩ : syracuseStep 46072799 = 69109199) B69109199
theorem B30715199 : Blo 2101435 30715199 := bstep (se 1 (by rfl) ⟨23036399, by rfl⟩ : syracuseStep 30715199 = 46072799) B46072799
theorem B20476799 : Blo 2101435 20476799 := bstep (se 1 (by rfl) ⟨15357599, by rfl⟩ : syracuseStep 20476799 = 30715199) B30715199
theorem B13651199 : Blo 2101435 13651199 := bstep (se 1 (by rfl) ⟨10238399, by rfl⟩ : syracuseStep 13651199 = 20476799) B20476799
theorem B9100799 : Blo 2101435 9100799 := bstep (se 1 (by rfl) ⟨6825599, by rfl⟩ : syracuseStep 9100799 = 13651199) B13651199
theorem B6067199 : Blo 2101435 6067199 := bstep (se 1 (by rfl) ⟨4550399, by rfl⟩ : syracuseStep 6067199 = 9100799) B9100799
theorem B4044799 : Blo 2101435 4044799 := bstep (se 1 (by rfl) ⟨3033599, by rfl⟩ : syracuseStep 4044799 = 6067199) B6067199
theorem B21572261 : Blo 2101435 21572261 := bstep (se 4 (by rfl) ⟨2022399, by rfl⟩ : syracuseStep 21572261 = 4044799) B4044799
theorem B14381507 : Blo 2101435 14381507 := bstep (se 1 (by rfl) ⟨10786130, by rfl⟩ : syracuseStep 14381507 = 21572261) B21572261
theorem B38350685 : Blo 2101435 38350685 := bstep (se 3 (by rfl) ⟨7190753, by rfl⟩ : syracuseStep 38350685 = 14381507) B14381507
theorem B102268493 : Blo 2101435 102268493 := bstep (se 3 (by rfl) ⟨19175342, by rfl⟩ : syracuseStep 102268493 = 38350685) B38350685
theorem B68178995 : Blo 2101435 68178995 := bstep (se 1 (by rfl) ⟨51134246, by rfl⟩ : syracuseStep 68178995 = 102268493) B102268493
theorem B45452663 : Blo 2101435 45452663 := bstep (se 1 (by rfl) ⟨34089497, by rfl⟩ : syracuseStep 45452663 = 68178995) B68178995
theorem B30301775 : Blo 2101435 30301775 := bstep (se 1 (by rfl) ⟨22726331, by rfl⟩ : syracuseStep 30301775 = 45452663) B45452663
theorem B20201183 : Blo 2101435 20201183 := bstep (se 1 (by rfl) ⟨15150887, by rfl⟩ : syracuseStep 20201183 = 30301775) B30301775
theorem B13467455 : Blo 2101435 13467455 := bstep (se 1 (by rfl) ⟨10100591, by rfl⟩ : syracuseStep 13467455 = 20201183) B20201183
theorem B8978303 : Blo 2101435 8978303 := bstep (se 1 (by rfl) ⟨6733727, by rfl⟩ : syracuseStep 8978303 = 13467455) B13467455
theorem B5985535 : Blo 2101435 5985535 := bstep (se 1 (by rfl) ⟨4489151, by rfl⟩ : syracuseStep 5985535 = 8978303) B8978303
theorem B7980713 : Blo 2101435 7980713 := bstep (se 2 (by rfl) ⟨2992767, by rfl⟩ : syracuseStep 7980713 = 5985535) B5985535
theorem B5320475 : Blo 2101435 5320475 := bstep (se 1 (by rfl) ⟨3990356, by rfl⟩ : syracuseStep 5320475 = 7980713) B7980713
theorem B3546983 : Blo 2101435 3546983 := bstep (se 1 (by rfl) ⟨2660237, by rfl⟩ : syracuseStep 3546983 = 5320475) B5320475
theorem B2364655 : Blo 2101435 2364655 := bstep (se 1 (by rfl) ⟨1773491, by rfl⟩ : syracuseStep 2364655 = 3546983) B3546983
theorem B3152873 : Blo 2101435 3152873 := bstep (se 2 (by rfl) ⟨1182327, by rfl⟩ : syracuseStep 3152873 = 2364655) B2364655
theorem B2101915 : Blo 2101435 2101915 := bstep (se 1 (by rfl) ⟨1576436, by rfl⟩ : syracuseStep 2101915 = 3152873) B3152873
theorem B4793845 : Blo 2101435 4793845 := bbase (se 5 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 4793845 = 449423) (by norm_num)
theorem B6391793 : Blo 2101435 6391793 := bstep (se 2 (by rfl) ⟨2396922, by rfl⟩ : syracuseStep 6391793 = 4793845) B4793845
theorem B4261195 : Blo 2101435 4261195 := bstep (se 1 (by rfl) ⟨3195896, by rfl⟩ : syracuseStep 4261195 = 6391793) B6391793
theorem B5681593 : Blo 2101435 5681593 := bstep (se 2 (by rfl) ⟨2130597, by rfl⟩ : syracuseStep 5681593 = 4261195) B4261195
theorem B7575457 : Blo 2101435 7575457 := bstep (se 2 (by rfl) ⟨2840796, by rfl⟩ : syracuseStep 7575457 = 5681593) B5681593
theorem B10100609 : Blo 2101435 10100609 := bstep (se 2 (by rfl) ⟨3787728, by rfl⟩ : syracuseStep 10100609 = 7575457) B7575457
theorem B6733739 : Blo 2101435 6733739 := bstep (se 1 (by rfl) ⟨5050304, by rfl⟩ : syracuseStep 6733739 = 10100609) B10100609
theorem B17956637 : Blo 2101435 17956637 := bstep (se 3 (by rfl) ⟨3366869, by rfl⟩ : syracuseStep 17956637 = 6733739) B6733739
theorem B11971091 : Blo 2101435 11971091 := bstep (se 1 (by rfl) ⟨8978318, by rfl⟩ : syracuseStep 11971091 = 17956637) B17956637
theorem B7980727 : Blo 2101435 7980727 := bstep (se 1 (by rfl) ⟨5985545, by rfl⟩ : syracuseStep 7980727 = 11971091) B11971091
theorem B10640969 : Blo 2101435 10640969 := bstep (se 2 (by rfl) ⟨3990363, by rfl⟩ : syracuseStep 10640969 = 7980727) B7980727
theorem B7093979 : Blo 2101435 7093979 := bstep (se 1 (by rfl) ⟨5320484, by rfl⟩ : syracuseStep 7093979 = 10640969) B10640969
theorem B4729319 : Blo 2101435 4729319 := bstep (se 1 (by rfl) ⟨3546989, by rfl⟩ : syracuseStep 4729319 = 7093979) B7093979
theorem B3152879 : Blo 2101435 3152879 := bstep (se 1 (by rfl) ⟨2364659, by rfl⟩ : syracuseStep 3152879 = 4729319) B4729319
theorem B2101919 : Blo 2101435 2101919 := bstep (se 1 (by rfl) ⟨1576439, by rfl⟩ : syracuseStep 2101919 = 3152879) B3152879
theorem B3152885 : Blo 2101435 3152885 := bbase (se 5 (by rfl) ⟨147791, by rfl⟩ : syracuseStep 3152885 = 295583) (by norm_num)
theorem B2101923 : Blo 2101435 2101923 := bstep (se 1 (by rfl) ⟨1576442, by rfl⟩ : syracuseStep 2101923 = 3152885) B3152885
theorem B5050325 : Blo 2101435 5050325 := bbase (se 7 (by rfl) ⟨59183, by rfl⟩ : syracuseStep 5050325 = 118367) (by norm_num)
theorem B3366883 : Blo 2101435 3366883 := bstep (se 1 (by rfl) ⟨2525162, by rfl⟩ : syracuseStep 3366883 = 5050325) B5050325
theorem B4489177 : Blo 2101435 4489177 := bstep (se 2 (by rfl) ⟨1683441, by rfl⟩ : syracuseStep 4489177 = 3366883) B3366883
theorem B5985569 : Blo 2101435 5985569 := bstep (se 2 (by rfl) ⟨2244588, by rfl⟩ : syracuseStep 5985569 = 4489177) B4489177
theorem B3990379 : Blo 2101435 3990379 := bstep (se 1 (by rfl) ⟨2992784, by rfl⟩ : syracuseStep 3990379 = 5985569) B5985569
theorem B5320505 : Blo 2101435 5320505 := bstep (se 2 (by rfl) ⟨1995189, by rfl⟩ : syracuseStep 5320505 = 3990379) B3990379
theorem B3547003 : Blo 2101435 3547003 := bstep (se 1 (by rfl) ⟨2660252, by rfl⟩ : syracuseStep 3547003 = 5320505) B5320505
theorem B4729337 : Blo 2101435 4729337 := bstep (se 2 (by rfl) ⟨1773501, by rfl⟩ : syracuseStep 4729337 = 3547003) B3547003
theorem B3152891 : Blo 2101435 3152891 := bstep (se 1 (by rfl) ⟨2364668, by rfl⟩ : syracuseStep 3152891 = 4729337) B4729337
theorem B2101927 : Blo 2101435 2101927 := bstep (se 1 (by rfl) ⟨1576445, by rfl⟩ : syracuseStep 2101927 = 3152891) B3152891
theorem B2364673 : Blo 2101435 2364673 := bbase (se 2 (by rfl) ⟨886752, by rfl⟩ : syracuseStep 2364673 = 1773505) (by norm_num)
theorem B3152897 : Blo 2101435 3152897 := bstep (se 2 (by rfl) ⟨1182336, by rfl⟩ : syracuseStep 3152897 = 2364673) B2364673
theorem B2101931 : Blo 2101435 2101931 := bstep (se 1 (by rfl) ⟨1576448, by rfl⟩ : syracuseStep 2101931 = 3152897) B3152897
theorem B5320525 : Blo 2101435 5320525 := bbase (se 3 (by rfl) ⟨997598, by rfl⟩ : syracuseStep 5320525 = 1995197) (by norm_num)
theorem B7094033 : Blo 2101435 7094033 := bstep (se 2 (by rfl) ⟨2660262, by rfl⟩ : syracuseStep 7094033 = 5320525) B5320525
theorem B4729355 : Blo 2101435 4729355 := bstep (se 1 (by rfl) ⟨3547016, by rfl⟩ : syracuseStep 4729355 = 7094033) B7094033
theorem B3152903 : Blo 2101435 3152903 := bstep (se 1 (by rfl) ⟨2364677, by rfl⟩ : syracuseStep 3152903 = 4729355) B4729355
theorem B2101935 : Blo 2101435 2101935 := bstep (se 1 (by rfl) ⟨1576451, by rfl⟩ : syracuseStep 2101935 = 3152903) B3152903
theorem B3152909 : Blo 2101435 3152909 := bbase (se 3 (by rfl) ⟨591170, by rfl⟩ : syracuseStep 3152909 = 1182341) (by norm_num)
theorem B2101939 : Blo 2101435 2101939 := bstep (se 1 (by rfl) ⟨1576454, by rfl⟩ : syracuseStep 2101939 = 3152909) B3152909
theorem B4729373 : Blo 2101435 4729373 := bbase (se 3 (by rfl) ⟨886757, by rfl⟩ : syracuseStep 4729373 = 1773515) (by norm_num)
theorem B3152915 : Blo 2101435 3152915 := bstep (se 1 (by rfl) ⟨2364686, by rfl⟩ : syracuseStep 3152915 = 4729373) B4729373
theorem B2101943 : Blo 2101435 2101943 := bstep (se 1 (by rfl) ⟨1576457, by rfl⟩ : syracuseStep 2101943 = 3152915) B3152915
theorem B3547037 : Blo 2101435 3547037 := bbase (se 3 (by rfl) ⟨665069, by rfl⟩ : syracuseStep 3547037 = 1330139) (by norm_num)
theorem B2364691 : Blo 2101435 2364691 := bstep (se 1 (by rfl) ⟨1773518, by rfl⟩ : syracuseStep 2364691 = 3547037) B3547037
theorem B3152921 : Blo 2101435 3152921 := bstep (se 2 (by rfl) ⟨1182345, by rfl⟩ : syracuseStep 3152921 = 2364691) B2364691
theorem B2101947 : Blo 2101435 2101947 := bstep (se 1 (by rfl) ⟨1576460, by rfl⟩ : syracuseStep 2101947 = 3152921) B3152921
theorem B20201525 : Blo 2101435 20201525 := bbase (se 5 (by rfl) ⟨946946, by rfl⟩ : syracuseStep 20201525 = 1893893) (by norm_num)
theorem B13467683 : Blo 2101435 13467683 := bstep (se 1 (by rfl) ⟨10100762, by rfl⟩ : syracuseStep 13467683 = 20201525) B20201525
theorem B8978455 : Blo 2101435 8978455 := bstep (se 1 (by rfl) ⟨6733841, by rfl⟩ : syracuseStep 8978455 = 13467683) B13467683
theorem B11971273 : Blo 2101435 11971273 := bstep (se 2 (by rfl) ⟨4489227, by rfl⟩ : syracuseStep 11971273 = 8978455) B8978455
theorem B15961697 : Blo 2101435 15961697 := bstep (se 2 (by rfl) ⟨5985636, by rfl⟩ : syracuseStep 15961697 = 11971273) B11971273
theorem B10641131 : Blo 2101435 10641131 := bstep (se 1 (by rfl) ⟨7980848, by rfl⟩ : syracuseStep 10641131 = 15961697) B15961697
theorem B7094087 : Blo 2101435 7094087 := bstep (se 1 (by rfl) ⟨5320565, by rfl⟩ : syracuseStep 7094087 = 10641131) B10641131
theorem B4729391 : Blo 2101435 4729391 := bstep (se 1 (by rfl) ⟨3547043, by rfl⟩ : syracuseStep 4729391 = 7094087) B7094087
theorem B3152927 : Blo 2101435 3152927 := bstep (se 1 (by rfl) ⟨2364695, by rfl⟩ : syracuseStep 3152927 = 4729391) B4729391
theorem B2101951 : Blo 2101435 2101951 := bstep (se 1 (by rfl) ⟨1576463, by rfl⟩ : syracuseStep 2101951 = 3152927) B3152927
theorem B3152933 : Blo 2101435 3152933 := bbase (se 4 (by rfl) ⟨295587, by rfl⟩ : syracuseStep 3152933 = 591175) (by norm_num)
theorem B2101955 : Blo 2101435 2101955 := bstep (se 1 (by rfl) ⟨1576466, by rfl⟩ : syracuseStep 2101955 = 3152933) B3152933
theorem B2660293 : Blo 2101435 2660293 := bbase (se 4 (by rfl) ⟨249402, by rfl⟩ : syracuseStep 2660293 = 498805) (by norm_num)
theorem B3547057 : Blo 2101435 3547057 := bstep (se 2 (by rfl) ⟨1330146, by rfl⟩ : syracuseStep 3547057 = 2660293) B2660293
theorem B4729409 : Blo 2101435 4729409 := bstep (se 2 (by rfl) ⟨1773528, by rfl⟩ : syracuseStep 4729409 = 3547057) B3547057
theorem B3152939 : Blo 2101435 3152939 := bstep (se 1 (by rfl) ⟨2364704, by rfl⟩ : syracuseStep 3152939 = 4729409) B4729409
theorem B2101959 : Blo 2101435 2101959 := bstep (se 1 (by rfl) ⟨1576469, by rfl⟩ : syracuseStep 2101959 = 3152939) B3152939
theorem B2364709 : Blo 2101435 2364709 := bbase (se 4 (by rfl) ⟨221691, by rfl⟩ : syracuseStep 2364709 = 443383) (by norm_num)
theorem B3152945 : Blo 2101435 3152945 := bstep (se 2 (by rfl) ⟨1182354, by rfl⟩ : syracuseStep 3152945 = 2364709) B2364709
theorem B2101963 : Blo 2101435 2101963 := bstep (se 1 (by rfl) ⟨1576472, by rfl⟩ : syracuseStep 2101963 = 3152945) B3152945
theorem B5050421 : Blo 2101435 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B3366947 : Blo 2101435 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B8978525 : Blo 2101435 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B5985683 : Blo 2101435 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B3990455 : Blo 2101435 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B2660303 : Blo 2101435 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B7094141 : Blo 2101435 7094141 := bstep (se 3 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 7094141 = 2660303) B2660303
theorem B4729427 : Blo 2101435 4729427 := bstep (se 1 (by rfl) ⟨3547070, by rfl⟩ : syracuseStep 4729427 = 7094141) B7094141
theorem B3152951 : Blo 2101435 3152951 := bstep (se 1 (by rfl) ⟨2364713, by rfl⟩ : syracuseStep 3152951 = 4729427) B4729427
theorem B2101967 : Blo 2101435 2101967 := bstep (se 1 (by rfl) ⟨1576475, by rfl⟩ : syracuseStep 2101967 = 3152951) B3152951
theorem B3152957 : Blo 2101435 3152957 := bbase (se 3 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 3152957 = 1182359) (by norm_num)
theorem B2101971 : Blo 2101435 2101971 := bstep (se 1 (by rfl) ⟨1576478, by rfl⟩ : syracuseStep 2101971 = 3152957) B3152957
theorem B4729445 : Blo 2101435 4729445 := bbase (se 4 (by rfl) ⟨443385, by rfl⟩ : syracuseStep 4729445 = 886771) (by norm_num)
theorem B3152963 : Blo 2101435 3152963 := bstep (se 1 (by rfl) ⟨2364722, by rfl⟩ : syracuseStep 3152963 = 4729445) B4729445
theorem B2101975 : Blo 2101435 2101975 := bstep (se 1 (by rfl) ⟨1576481, by rfl⟩ : syracuseStep 2101975 = 3152963) B3152963
theorem B5320637 : Blo 2101435 5320637 := bbase (se 3 (by rfl) ⟨997619, by rfl⟩ : syracuseStep 5320637 = 1995239) (by norm_num)
theorem B3547091 : Blo 2101435 3547091 := bstep (se 1 (by rfl) ⟨2660318, by rfl⟩ : syracuseStep 3547091 = 5320637) B5320637
theorem B2364727 : Blo 2101435 2364727 := bstep (se 1 (by rfl) ⟨1773545, by rfl⟩ : syracuseStep 2364727 = 3547091) B3547091
theorem B3152969 : Blo 2101435 3152969 := bstep (se 2 (by rfl) ⟨1182363, by rfl⟩ : syracuseStep 3152969 = 2364727) B2364727
theorem B2101979 : Blo 2101435 2101979 := bstep (se 1 (by rfl) ⟨1576484, by rfl⟩ : syracuseStep 2101979 = 3152969) B3152969
theorem B3990485 : Blo 2101435 3990485 := bbase (se 7 (by rfl) ⟨46763, by rfl⟩ : syracuseStep 3990485 = 93527) (by norm_num)
theorem B10641293 : Blo 2101435 10641293 := bstep (se 3 (by rfl) ⟨1995242, by rfl⟩ : syracuseStep 10641293 = 3990485) B3990485
theorem B7094195 : Blo 2101435 7094195 := bstep (se 1 (by rfl) ⟨5320646, by rfl⟩ : syracuseStep 7094195 = 10641293) B10641293
theorem B4729463 : Blo 2101435 4729463 := bstep (se 1 (by rfl) ⟨3547097, by rfl⟩ : syracuseStep 4729463 = 7094195) B7094195
theorem B3152975 : Blo 2101435 3152975 := bstep (se 1 (by rfl) ⟨2364731, by rfl⟩ : syracuseStep 3152975 = 4729463) B4729463
theorem B2101983 : Blo 2101435 2101983 := bstep (se 1 (by rfl) ⟨1576487, by rfl⟩ : syracuseStep 2101983 = 3152975) B3152975
theorem B3152981 : Blo 2101435 3152981 := bbase (se 8 (by rfl) ⟨18474, by rfl⟩ : syracuseStep 3152981 = 36949) (by norm_num)
theorem B2101987 : Blo 2101435 2101987 := bstep (se 1 (by rfl) ⟨1576490, by rfl⟩ : syracuseStep 2101987 = 3152981) B3152981
theorem B10378469 : Blo 2101435 10378469 := bbase (se 4 (by rfl) ⟨972981, by rfl⟩ : syracuseStep 10378469 = 1945963) (by norm_num)
theorem B27675917 : Blo 2101435 27675917 := bstep (se 3 (by rfl) ⟨5189234, by rfl⟩ : syracuseStep 27675917 = 10378469) B10378469
theorem B18450611 : Blo 2101435 18450611 := bstep (se 1 (by rfl) ⟨13837958, by rfl⟩ : syracuseStep 18450611 = 27675917) B27675917
theorem B12300407 : Blo 2101435 12300407 := bstep (se 1 (by rfl) ⟨9225305, by rfl⟩ : syracuseStep 12300407 = 18450611) B18450611
theorem B8200271 : Blo 2101435 8200271 := bstep (se 1 (by rfl) ⟨6150203, by rfl⟩ : syracuseStep 8200271 = 12300407) B12300407
theorem B5466847 : Blo 2101435 5466847 := bstep (se 1 (by rfl) ⟨4100135, by rfl⟩ : syracuseStep 5466847 = 8200271) B8200271
theorem B7289129 : Blo 2101435 7289129 := bstep (se 2 (by rfl) ⟨2733423, by rfl⟩ : syracuseStep 7289129 = 5466847) B5466847
theorem B19437677 : Blo 2101435 19437677 := bstep (se 3 (by rfl) ⟨3644564, by rfl⟩ : syracuseStep 19437677 = 7289129) B7289129
theorem B12958451 : Blo 2101435 12958451 := bstep (se 1 (by rfl) ⟨9718838, by rfl⟩ : syracuseStep 12958451 = 19437677) B19437677
theorem B8638967 : Blo 2101435 8638967 := bstep (se 1 (by rfl) ⟨6479225, by rfl⟩ : syracuseStep 8638967 = 12958451) B12958451
theorem B5759311 : Blo 2101435 5759311 := bstep (se 1 (by rfl) ⟨4319483, by rfl⟩ : syracuseStep 5759311 = 8638967) B8638967
theorem B7679081 : Blo 2101435 7679081 := bstep (se 2 (by rfl) ⟨2879655, by rfl⟩ : syracuseStep 7679081 = 5759311) B5759311
theorem B20477549 : Blo 2101435 20477549 := bstep (se 3 (by rfl) ⟨3839540, by rfl⟩ : syracuseStep 20477549 = 7679081) B7679081
theorem B13651699 : Blo 2101435 13651699 := bstep (se 1 (by rfl) ⟨10238774, by rfl⟩ : syracuseStep 13651699 = 20477549) B20477549
theorem B18202265 : Blo 2101435 18202265 := bstep (se 2 (by rfl) ⟨6825849, by rfl⟩ : syracuseStep 18202265 = 13651699) B13651699
theorem B12134843 : Blo 2101435 12134843 := bstep (se 1 (by rfl) ⟨9101132, by rfl⟩ : syracuseStep 12134843 = 18202265) B18202265
theorem B8089895 : Blo 2101435 8089895 := bstep (se 1 (by rfl) ⟨6067421, by rfl⟩ : syracuseStep 8089895 = 12134843) B12134843
theorem B5393263 : Blo 2101435 5393263 := bstep (se 1 (by rfl) ⟨4044947, by rfl⟩ : syracuseStep 5393263 = 8089895) B8089895
theorem B7191017 : Blo 2101435 7191017 := bstep (se 2 (by rfl) ⟨2696631, by rfl⟩ : syracuseStep 7191017 = 5393263) B5393263
theorem B4794011 : Blo 2101435 4794011 := bstep (se 1 (by rfl) ⟨3595508, by rfl⟩ : syracuseStep 4794011 = 7191017) B7191017
theorem B3196007 : Blo 2101435 3196007 := bstep (se 1 (by rfl) ⟨2397005, by rfl⟩ : syracuseStep 3196007 = 4794011) B4794011
theorem B2130671 : Blo 2101435 2130671 := bstep (se 1 (by rfl) ⟨1598003, by rfl⟩ : syracuseStep 2130671 = 3196007) B3196007
theorem B5681789 : Blo 2101435 5681789 := bstep (se 3 (by rfl) ⟨1065335, by rfl⟩ : syracuseStep 5681789 = 2130671) B2130671
theorem B3787859 : Blo 2101435 3787859 := bstep (se 1 (by rfl) ⟨2840894, by rfl⟩ : syracuseStep 3787859 = 5681789) B5681789
theorem B2525239 : Blo 2101435 2525239 := bstep (se 1 (by rfl) ⟨1893929, by rfl⟩ : syracuseStep 2525239 = 3787859) B3787859
theorem B13467941 : Blo 2101435 13467941 := bstep (se 4 (by rfl) ⟨1262619, by rfl⟩ : syracuseStep 13467941 = 2525239) B2525239
theorem B8978627 : Blo 2101435 8978627 := bstep (se 1 (by rfl) ⟨6733970, by rfl⟩ : syracuseStep 8978627 = 13467941) B13467941
theorem B5985751 : Blo 2101435 5985751 := bstep (se 1 (by rfl) ⟨4489313, by rfl⟩ : syracuseStep 5985751 = 8978627) B8978627
theorem B7981001 : Blo 2101435 7981001 := bstep (se 2 (by rfl) ⟨2992875, by rfl⟩ : syracuseStep 7981001 = 5985751) B5985751
theorem B5320667 : Blo 2101435 5320667 := bstep (se 1 (by rfl) ⟨3990500, by rfl⟩ : syracuseStep 5320667 = 7981001) B7981001
theorem B3547111 : Blo 2101435 3547111 := bstep (se 1 (by rfl) ⟨2660333, by rfl⟩ : syracuseStep 3547111 = 5320667) B5320667
theorem B4729481 : Blo 2101435 4729481 := bstep (se 2 (by rfl) ⟨1773555, by rfl⟩ : syracuseStep 4729481 = 3547111) B3547111
theorem B3152987 : Blo 2101435 3152987 := bstep (se 1 (by rfl) ⟨2364740, by rfl⟩ : syracuseStep 3152987 = 4729481) B4729481
theorem B2101991 : Blo 2101435 2101991 := bstep (se 1 (by rfl) ⟨1576493, by rfl⟩ : syracuseStep 2101991 = 3152987) B3152987
theorem B2364745 : Blo 2101435 2364745 := bbase (se 2 (by rfl) ⟨886779, by rfl⟩ : syracuseStep 2364745 = 1773559) (by norm_num)
theorem B3152993 : Blo 2101435 3152993 := bstep (se 2 (by rfl) ⟨1182372, by rfl⟩ : syracuseStep 3152993 = 2364745) B2364745
theorem B2101995 : Blo 2101435 2101995 := bstep (se 1 (by rfl) ⟨1576496, by rfl⟩ : syracuseStep 2101995 = 3152993) B3152993
theorem B4261357 : Blo 2101435 4261357 := bbase (se 3 (by rfl) ⟨799004, by rfl⟩ : syracuseStep 4261357 = 1598009) (by norm_num)
theorem B5681809 : Blo 2101435 5681809 := bstep (se 2 (by rfl) ⟨2130678, by rfl⟩ : syracuseStep 5681809 = 4261357) B4261357
theorem B30302981 : Blo 2101435 30302981 := bstep (se 4 (by rfl) ⟨2840904, by rfl⟩ : syracuseStep 30302981 = 5681809) B5681809
theorem B20201987 : Blo 2101435 20201987 := bstep (se 1 (by rfl) ⟨15151490, by rfl⟩ : syracuseStep 20201987 = 30302981) B30302981
theorem B13467991 : Blo 2101435 13467991 := bstep (se 1 (by rfl) ⟨10100993, by rfl⟩ : syracuseStep 13467991 = 20201987) B20201987
theorem B17957321 : Blo 2101435 17957321 := bstep (se 2 (by rfl) ⟨6733995, by rfl⟩ : syracuseStep 17957321 = 13467991) B13467991
theorem B11971547 : Blo 2101435 11971547 := bstep (se 1 (by rfl) ⟨8978660, by rfl⟩ : syracuseStep 11971547 = 17957321) B17957321
theorem B7981031 : Blo 2101435 7981031 := bstep (se 1 (by rfl) ⟨5985773, by rfl⟩ : syracuseStep 7981031 = 11971547) B11971547
theorem B5320687 : Blo 2101435 5320687 := bstep (se 1 (by rfl) ⟨3990515, by rfl⟩ : syracuseStep 5320687 = 7981031) B7981031
theorem B7094249 : Blo 2101435 7094249 := bstep (se 2 (by rfl) ⟨2660343, by rfl⟩ : syracuseStep 7094249 = 5320687) B5320687
theorem B4729499 : Blo 2101435 4729499 := bstep (se 1 (by rfl) ⟨3547124, by rfl⟩ : syracuseStep 4729499 = 7094249) B7094249
theorem B3152999 : Blo 2101435 3152999 := bstep (se 1 (by rfl) ⟨2364749, by rfl⟩ : syracuseStep 3152999 = 4729499) B4729499
theorem B2101999 : Blo 2101435 2101999 := bstep (se 1 (by rfl) ⟨1576499, by rfl⟩ : syracuseStep 2101999 = 3152999) B3152999
theorem B3153005 : Blo 2101435 3153005 := bbase (se 3 (by rfl) ⟨591188, by rfl⟩ : syracuseStep 3153005 = 1182377) (by norm_num)
theorem B2102003 : Blo 2101435 2102003 := bstep (se 1 (by rfl) ⟨1576502, by rfl⟩ : syracuseStep 2102003 = 3153005) B3153005
theorem B4729517 : Blo 2101435 4729517 := bbase (se 3 (by rfl) ⟨886784, by rfl⟩ : syracuseStep 4729517 = 1773569) (by norm_num)
theorem B3153011 : Blo 2101435 3153011 := bstep (se 1 (by rfl) ⟨2364758, by rfl⟩ : syracuseStep 3153011 = 4729517) B4729517
theorem B2102007 : Blo 2101435 2102007 := bstep (se 1 (by rfl) ⟨1576505, by rfl⟩ : syracuseStep 2102007 = 3153011) B3153011
theorem B4489357 : Blo 2101435 4489357 := bbase (se 3 (by rfl) ⟨841754, by rfl⟩ : syracuseStep 4489357 = 1683509) (by norm_num)
theorem B5985809 : Blo 2101435 5985809 := bstep (se 2 (by rfl) ⟨2244678, by rfl⟩ : syracuseStep 5985809 = 4489357) B4489357
theorem B3990539 : Blo 2101435 3990539 := bstep (se 1 (by rfl) ⟨2992904, by rfl⟩ : syracuseStep 3990539 = 5985809) B5985809
theorem B2660359 : Blo 2101435 2660359 := bstep (se 1 (by rfl) ⟨1995269, by rfl⟩ : syracuseStep 2660359 = 3990539) B3990539
theorem B3547145 : Blo 2101435 3547145 := bstep (se 2 (by rfl) ⟨1330179, by rfl⟩ : syracuseStep 3547145 = 2660359) B2660359
theorem B2364763 : Blo 2101435 2364763 := bstep (se 1 (by rfl) ⟨1773572, by rfl⟩ : syracuseStep 2364763 = 3547145) B3547145
theorem B3153017 : Blo 2101435 3153017 := bstep (se 2 (by rfl) ⟨1182381, by rfl⟩ : syracuseStep 3153017 = 2364763) B2364763
theorem B2102011 : Blo 2101435 2102011 := bstep (se 1 (by rfl) ⟨1576508, by rfl⟩ : syracuseStep 2102011 = 3153017) B3153017
theorem B3839581 : Blo 2101435 3839581 := bbase (se 3 (by rfl) ⟨719921, by rfl⟩ : syracuseStep 3839581 = 1439843) (by norm_num)
theorem B5119441 : Blo 2101435 5119441 := bstep (se 2 (by rfl) ⟨1919790, by rfl⟩ : syracuseStep 5119441 = 3839581) B3839581
theorem B27303685 : Blo 2101435 27303685 := bstep (se 4 (by rfl) ⟨2559720, by rfl⟩ : syracuseStep 27303685 = 5119441) B5119441
theorem B145619653 : Blo 2101435 145619653 := bstep (se 4 (by rfl) ⟨13651842, by rfl⟩ : syracuseStep 145619653 = 27303685) B27303685
theorem B194159537 : Blo 2101435 194159537 := bstep (se 2 (by rfl) ⟨72809826, by rfl⟩ : syracuseStep 194159537 = 145619653) B145619653
theorem B129439691 : Blo 2101435 129439691 := bstep (se 1 (by rfl) ⟨97079768, by rfl⟩ : syracuseStep 129439691 = 194159537) B194159537
theorem B86293127 : Blo 2101435 86293127 := bstep (se 1 (by rfl) ⟨64719845, by rfl⟩ : syracuseStep 86293127 = 129439691) B129439691
theorem B57528751 : Blo 2101435 57528751 := bstep (se 1 (by rfl) ⟨43146563, by rfl⟩ : syracuseStep 57528751 = 86293127) B86293127
theorem B76705001 : Blo 2101435 76705001 := bstep (se 2 (by rfl) ⟨28764375, by rfl⟩ : syracuseStep 76705001 = 57528751) B57528751
theorem B51136667 : Blo 2101435 51136667 := bstep (se 1 (by rfl) ⟨38352500, by rfl⟩ : syracuseStep 51136667 = 76705001) B76705001
theorem B34091111 : Blo 2101435 34091111 := bstep (se 1 (by rfl) ⟨25568333, by rfl⟩ : syracuseStep 34091111 = 51136667) B51136667
theorem B22727407 : Blo 2101435 22727407 := bstep (se 1 (by rfl) ⟨17045555, by rfl⟩ : syracuseStep 22727407 = 34091111) B34091111
theorem B30303209 : Blo 2101435 30303209 := bstep (se 2 (by rfl) ⟨11363703, by rfl⟩ : syracuseStep 30303209 = 22727407) B22727407
theorem B20202139 : Blo 2101435 20202139 := bstep (se 1 (by rfl) ⟨15151604, by rfl⟩ : syracuseStep 20202139 = 30303209) B30303209
theorem B26936185 : Blo 2101435 26936185 := bstep (se 2 (by rfl) ⟨10101069, by rfl⟩ : syracuseStep 26936185 = 20202139) B20202139
theorem B35914913 : Blo 2101435 35914913 := bstep (se 2 (by rfl) ⟨13468092, by rfl⟩ : syracuseStep 35914913 = 26936185) B26936185
theorem B23943275 : Blo 2101435 23943275 := bstep (se 1 (by rfl) ⟨17957456, by rfl⟩ : syracuseStep 23943275 = 35914913) B35914913
theorem B15962183 : Blo 2101435 15962183 := bstep (se 1 (by rfl) ⟨11971637, by rfl⟩ : syracuseStep 15962183 = 23943275) B23943275
theorem B10641455 : Blo 2101435 10641455 := bstep (se 1 (by rfl) ⟨7981091, by rfl⟩ : syracuseStep 10641455 = 15962183) B15962183
theorem B7094303 : Blo 2101435 7094303 := bstep (se 1 (by rfl) ⟨5320727, by rfl⟩ : syracuseStep 7094303 = 10641455) B10641455
theorem B4729535 : Blo 2101435 4729535 := bstep (se 1 (by rfl) ⟨3547151, by rfl⟩ : syracuseStep 4729535 = 7094303) B7094303
theorem B3153023 : Blo 2101435 3153023 := bstep (se 1 (by rfl) ⟨2364767, by rfl⟩ : syracuseStep 3153023 = 4729535) B4729535
theorem B2102015 : Blo 2101435 2102015 := bstep (se 1 (by rfl) ⟨1576511, by rfl⟩ : syracuseStep 2102015 = 3153023) B3153023
theorem B3153029 : Blo 2101435 3153029 := bbase (se 4 (by rfl) ⟨295596, by rfl⟩ : syracuseStep 3153029 = 591193) (by norm_num)
theorem B2102019 : Blo 2101435 2102019 := bstep (se 1 (by rfl) ⟨1576514, by rfl⟩ : syracuseStep 2102019 = 3153029) B3153029
theorem B3547165 : Blo 2101435 3547165 := bbase (se 3 (by rfl) ⟨665093, by rfl⟩ : syracuseStep 3547165 = 1330187) (by norm_num)
theorem B4729553 : Blo 2101435 4729553 := bstep (se 2 (by rfl) ⟨1773582, by rfl⟩ : syracuseStep 4729553 = 3547165) B3547165
theorem B3153035 : Blo 2101435 3153035 := bstep (se 1 (by rfl) ⟨2364776, by rfl⟩ : syracuseStep 3153035 = 4729553) B4729553
theorem B2102023 : Blo 2101435 2102023 := bstep (se 1 (by rfl) ⟨1576517, by rfl⟩ : syracuseStep 2102023 = 3153035) B3153035
theorem B2364781 : Blo 2101435 2364781 := bbase (se 3 (by rfl) ⟨443396, by rfl⟩ : syracuseStep 2364781 = 886793) (by norm_num)
theorem B3153041 : Blo 2101435 3153041 := bstep (se 2 (by rfl) ⟨1182390, by rfl⟩ : syracuseStep 3153041 = 2364781) B2364781
theorem B2102027 : Blo 2101435 2102027 := bstep (se 1 (by rfl) ⟨1576520, by rfl⟩ : syracuseStep 2102027 = 3153041) B3153041
theorem B7094357 : Blo 2101435 7094357 := bbase (se 8 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 7094357 = 83137) (by norm_num)
theorem B4729571 : Blo 2101435 4729571 := bstep (se 1 (by rfl) ⟨3547178, by rfl⟩ : syracuseStep 4729571 = 7094357) B7094357
theorem B3153047 : Blo 2101435 3153047 := bstep (se 1 (by rfl) ⟨2364785, by rfl⟩ : syracuseStep 3153047 = 4729571) B4729571
theorem B2102031 : Blo 2101435 2102031 := bstep (se 1 (by rfl) ⟨1576523, by rfl⟩ : syracuseStep 2102031 = 3153047) B3153047
theorem B3153053 : Blo 2101435 3153053 := bbase (se 3 (by rfl) ⟨591197, by rfl⟩ : syracuseStep 3153053 = 1182395) (by norm_num)
theorem B2102035 : Blo 2101435 2102035 := bstep (se 1 (by rfl) ⟨1576526, by rfl⟩ : syracuseStep 2102035 = 3153053) B3153053
theorem B4729589 : Blo 2101435 4729589 := bbase (se 5 (by rfl) ⟨221699, by rfl⟩ : syracuseStep 4729589 = 443399) (by norm_num)
theorem B3153059 : Blo 2101435 3153059 := bstep (se 1 (by rfl) ⟨2364794, by rfl⟩ : syracuseStep 3153059 = 4729589) B4729589
theorem B2102039 : Blo 2101435 2102039 := bstep (se 1 (by rfl) ⟨1576529, by rfl⟩ : syracuseStep 2102039 = 3153059) B3153059
theorem B2559757 : Blo 2101435 2559757 := bbase (se 3 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 2559757 = 959909) (by norm_num)
theorem B3413009 : Blo 2101435 3413009 := bstep (se 2 (by rfl) ⟨1279878, by rfl⟩ : syracuseStep 3413009 = 2559757) B2559757
theorem B2275339 : Blo 2101435 2275339 := bstep (se 1 (by rfl) ⟨1706504, by rfl⟩ : syracuseStep 2275339 = 3413009) B3413009
theorem B3033785 : Blo 2101435 3033785 := bstep (se 2 (by rfl) ⟨1137669, by rfl⟩ : syracuseStep 3033785 = 2275339) B2275339
theorem B8090093 : Blo 2101435 8090093 := bstep (se 3 (by rfl) ⟨1516892, by rfl⟩ : syracuseStep 8090093 = 3033785) B3033785
theorem B5393395 : Blo 2101435 5393395 := bstep (se 1 (by rfl) ⟨4045046, by rfl⟩ : syracuseStep 5393395 = 8090093) B8090093
theorem B7191193 : Blo 2101435 7191193 := bstep (se 2 (by rfl) ⟨2696697, by rfl⟩ : syracuseStep 7191193 = 5393395) B5393395
theorem B9588257 : Blo 2101435 9588257 := bstep (se 2 (by rfl) ⟨3595596, by rfl⟩ : syracuseStep 9588257 = 7191193) B7191193
theorem B6392171 : Blo 2101435 6392171 := bstep (se 1 (by rfl) ⟨4794128, by rfl⟩ : syracuseStep 6392171 = 9588257) B9588257
theorem B4261447 : Blo 2101435 4261447 := bstep (se 1 (by rfl) ⟨3196085, by rfl⟩ : syracuseStep 4261447 = 6392171) B6392171
theorem B5681929 : Blo 2101435 5681929 := bstep (se 2 (by rfl) ⟨2130723, by rfl⟩ : syracuseStep 5681929 = 4261447) B4261447
theorem B7575905 : Blo 2101435 7575905 := bstep (se 2 (by rfl) ⟨2840964, by rfl⟩ : syracuseStep 7575905 = 5681929) B5681929
theorem B5050603 : Blo 2101435 5050603 := bstep (se 1 (by rfl) ⟨3787952, by rfl⟩ : syracuseStep 5050603 = 7575905) B7575905
theorem B26936549 : Blo 2101435 26936549 := bstep (se 4 (by rfl) ⟨2525301, by rfl⟩ : syracuseStep 26936549 = 5050603) B5050603
theorem B17957699 : Blo 2101435 17957699 := bstep (se 1 (by rfl) ⟨13468274, by rfl⟩ : syracuseStep 17957699 = 26936549) B26936549
theorem B11971799 : Blo 2101435 11971799 := bstep (se 1 (by rfl) ⟨8978849, by rfl⟩ : syracuseStep 11971799 = 17957699) B17957699
theorem B7981199 : Blo 2101435 7981199 := bstep (se 1 (by rfl) ⟨5985899, by rfl⟩ : syracuseStep 7981199 = 11971799) B11971799
theorem B5320799 : Blo 2101435 5320799 := bstep (se 1 (by rfl) ⟨3990599, by rfl⟩ : syracuseStep 5320799 = 7981199) B7981199
theorem B3547199 : Blo 2101435 3547199 := bstep (se 1 (by rfl) ⟨2660399, by rfl⟩ : syracuseStep 3547199 = 5320799) B5320799
theorem B2364799 : Blo 2101435 2364799 := bstep (se 1 (by rfl) ⟨1773599, by rfl⟩ : syracuseStep 2364799 = 3547199) B3547199
theorem B3153065 : Blo 2101435 3153065 := bstep (se 2 (by rfl) ⟨1182399, by rfl⟩ : syracuseStep 3153065 = 2364799) B2364799
theorem B2102043 : Blo 2101435 2102043 := bstep (se 1 (by rfl) ⟨1576532, by rfl⟩ : syracuseStep 2102043 = 3153065) B3153065
theorem B5050613 : Blo 2101435 5050613 := bbase (se 5 (by rfl) ⟨236747, by rfl⟩ : syracuseStep 5050613 = 473495) (by norm_num)
theorem B3367075 : Blo 2101435 3367075 := bstep (se 1 (by rfl) ⟨2525306, by rfl⟩ : syracuseStep 3367075 = 5050613) B5050613
theorem B4489433 : Blo 2101435 4489433 := bstep (se 2 (by rfl) ⟨1683537, by rfl⟩ : syracuseStep 4489433 = 3367075) B3367075
theorem B2992955 : Blo 2101435 2992955 := bstep (se 1 (by rfl) ⟨2244716, by rfl⟩ : syracuseStep 2992955 = 4489433) B4489433
theorem B7981213 : Blo 2101435 7981213 := bstep (se 3 (by rfl) ⟨1496477, by rfl⟩ : syracuseStep 7981213 = 2992955) B2992955
theorem B10641617 : Blo 2101435 10641617 := bstep (se 2 (by rfl) ⟨3990606, by rfl⟩ : syracuseStep 10641617 = 7981213) B7981213
theorem B7094411 : Blo 2101435 7094411 := bstep (se 1 (by rfl) ⟨5320808, by rfl⟩ : syracuseStep 7094411 = 10641617) B10641617
theorem B4729607 : Blo 2101435 4729607 := bstep (se 1 (by rfl) ⟨3547205, by rfl⟩ : syracuseStep 4729607 = 7094411) B7094411
theorem B3153071 : Blo 2101435 3153071 := bstep (se 1 (by rfl) ⟨2364803, by rfl⟩ : syracuseStep 3153071 = 4729607) B4729607
theorem B2102047 : Blo 2101435 2102047 := bstep (se 1 (by rfl) ⟨1576535, by rfl⟩ : syracuseStep 2102047 = 3153071) B3153071
theorem B3153077 : Blo 2101435 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B2102051 : Blo 2101435 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B5320829 : Blo 2101435 5320829 := bbase (se 3 (by rfl) ⟨997655, by rfl⟩ : syracuseStep 5320829 = 1995311) (by norm_num)
theorem B3547219 : Blo 2101435 3547219 := bstep (se 1 (by rfl) ⟨2660414, by rfl⟩ : syracuseStep 3547219 = 5320829) B5320829
theorem B4729625 : Blo 2101435 4729625 := bstep (se 2 (by rfl) ⟨1773609, by rfl⟩ : syracuseStep 4729625 = 3547219) B3547219
theorem B3153083 : Blo 2101435 3153083 := bstep (se 1 (by rfl) ⟨2364812, by rfl⟩ : syracuseStep 3153083 = 4729625) B4729625
theorem B2102055 : Blo 2101435 2102055 := bstep (se 1 (by rfl) ⟨1576541, by rfl⟩ : syracuseStep 2102055 = 3153083) B3153083
theorem B2364817 : Blo 2101435 2364817 := bbase (se 2 (by rfl) ⟨886806, by rfl⟩ : syracuseStep 2364817 = 1773613) (by norm_num)
theorem B3153089 : Blo 2101435 3153089 := bstep (se 2 (by rfl) ⟨1182408, by rfl⟩ : syracuseStep 3153089 = 2364817) B2364817
theorem B2102059 : Blo 2101435 2102059 := bstep (se 1 (by rfl) ⟨1576544, by rfl⟩ : syracuseStep 2102059 = 3153089) B3153089
theorem B3990637 : Blo 2101435 3990637 := bbase (se 3 (by rfl) ⟨748244, by rfl⟩ : syracuseStep 3990637 = 1496489) (by norm_num)
theorem B5320849 : Blo 2101435 5320849 := bstep (se 2 (by rfl) ⟨1995318, by rfl⟩ : syracuseStep 5320849 = 3990637) B3990637
theorem B7094465 : Blo 2101435 7094465 := bstep (se 2 (by rfl) ⟨2660424, by rfl⟩ : syracuseStep 7094465 = 5320849) B5320849
theorem B4729643 : Blo 2101435 4729643 := bstep (se 1 (by rfl) ⟨3547232, by rfl⟩ : syracuseStep 4729643 = 7094465) B7094465
theorem B3153095 : Blo 2101435 3153095 := bstep (se 1 (by rfl) ⟨2364821, by rfl⟩ : syracuseStep 3153095 = 4729643) B4729643
theorem B2102063 : Blo 2101435 2102063 := bstep (se 1 (by rfl) ⟨1576547, by rfl⟩ : syracuseStep 2102063 = 3153095) B3153095
theorem B3153101 : Blo 2101435 3153101 := bbase (se 3 (by rfl) ⟨591206, by rfl⟩ : syracuseStep 3153101 = 1182413) (by norm_num)
theorem B2102067 : Blo 2101435 2102067 := bstep (se 1 (by rfl) ⟨1576550, by rfl⟩ : syracuseStep 2102067 = 3153101) B3153101
theorem B4729661 : Blo 2101435 4729661 := bbase (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) (by norm_num)
theorem B3153107 : Blo 2101435 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B2102071 : Blo 2101435 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B3547253 : Blo 2101435 3547253 := bbase (se 5 (by rfl) ⟨166277, by rfl⟩ : syracuseStep 3547253 = 332555) (by norm_num)
theorem B2364835 : Blo 2101435 2364835 := bstep (se 1 (by rfl) ⟨1773626, by rfl⟩ : syracuseStep 2364835 = 3547253) B3547253
theorem B3153113 : Blo 2101435 3153113 := bstep (se 2 (by rfl) ⟨1182417, by rfl⟩ : syracuseStep 3153113 = 2364835) B2364835
theorem B2102075 : Blo 2101435 2102075 := bstep (se 1 (by rfl) ⟨1576556, by rfl⟩ : syracuseStep 2102075 = 3153113) B3153113
theorem B4489501 : Blo 2101435 4489501 := bbase (se 3 (by rfl) ⟨841781, by rfl⟩ : syracuseStep 4489501 = 1683563) (by norm_num)
theorem B5986001 : Blo 2101435 5986001 := bstep (se 2 (by rfl) ⟨2244750, by rfl⟩ : syracuseStep 5986001 = 4489501) B4489501
theorem B15962669 : Blo 2101435 15962669 := bstep (se 3 (by rfl) ⟨2993000, by rfl⟩ : syracuseStep 15962669 = 5986001) B5986001
theorem B10641779 : Blo 2101435 10641779 := bstep (se 1 (by rfl) ⟨7981334, by rfl⟩ : syracuseStep 10641779 = 15962669) B15962669
theorem B7094519 : Blo 2101435 7094519 := bstep (se 1 (by rfl) ⟨5320889, by rfl⟩ : syracuseStep 7094519 = 10641779) B10641779
theorem B4729679 : Blo 2101435 4729679 := bstep (se 1 (by rfl) ⟨3547259, by rfl⟩ : syracuseStep 4729679 = 7094519) B7094519
theorem B3153119 : Blo 2101435 3153119 := bstep (se 1 (by rfl) ⟨2364839, by rfl⟩ : syracuseStep 3153119 = 4729679) B4729679
theorem B2102079 : Blo 2101435 2102079 := bstep (se 1 (by rfl) ⟨1576559, by rfl⟩ : syracuseStep 2102079 = 3153119) B3153119
theorem B3153125 : Blo 2101435 3153125 := bbase (se 4 (by rfl) ⟨295605, by rfl⟩ : syracuseStep 3153125 = 591211) (by norm_num)
theorem B2102083 : Blo 2101435 2102083 := bstep (se 1 (by rfl) ⟨1576562, by rfl⟩ : syracuseStep 2102083 = 3153125) B3153125
theorem B4794229 : Blo 2101435 4794229 := bbase (se 5 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 4794229 = 449459) (by norm_num)
theorem B6392305 : Blo 2101435 6392305 := bstep (se 2 (by rfl) ⟨2397114, by rfl⟩ : syracuseStep 6392305 = 4794229) B4794229
theorem B8523073 : Blo 2101435 8523073 := bstep (se 2 (by rfl) ⟨3196152, by rfl⟩ : syracuseStep 8523073 = 6392305) B6392305
theorem B11364097 : Blo 2101435 11364097 := bstep (se 2 (by rfl) ⟨4261536, by rfl⟩ : syracuseStep 11364097 = 8523073) B8523073
theorem B15152129 : Blo 2101435 15152129 := bstep (se 2 (by rfl) ⟨5682048, by rfl⟩ : syracuseStep 15152129 = 11364097) B11364097
theorem B10101419 : Blo 2101435 10101419 := bstep (se 1 (by rfl) ⟨7576064, by rfl⟩ : syracuseStep 10101419 = 15152129) B15152129
theorem B6734279 : Blo 2101435 6734279 := bstep (se 1 (by rfl) ⟨5050709, by rfl⟩ : syracuseStep 6734279 = 10101419) B10101419
theorem B4489519 : Blo 2101435 4489519 := bstep (se 1 (by rfl) ⟨3367139, by rfl⟩ : syracuseStep 4489519 = 6734279) B6734279
theorem B5986025 : Blo 2101435 5986025 := bstep (se 2 (by rfl) ⟨2244759, by rfl⟩ : syracuseStep 5986025 = 4489519) B4489519
theorem B3990683 : Blo 2101435 3990683 := bstep (se 1 (by rfl) ⟨2993012, by rfl⟩ : syracuseStep 3990683 = 5986025) B5986025
theorem B2660455 : Blo 2101435 2660455 := bstep (se 1 (by rfl) ⟨1995341, by rfl⟩ : syracuseStep 2660455 = 3990683) B3990683
theorem B3547273 : Blo 2101435 3547273 := bstep (se 2 (by rfl) ⟨1330227, by rfl⟩ : syracuseStep 3547273 = 2660455) B2660455
theorem B4729697 : Blo 2101435 4729697 := bstep (se 2 (by rfl) ⟨1773636, by rfl⟩ : syracuseStep 4729697 = 3547273) B3547273
theorem B3153131 : Blo 2101435 3153131 := bstep (se 1 (by rfl) ⟨2364848, by rfl⟩ : syracuseStep 3153131 = 4729697) B4729697
theorem B2102087 : Blo 2101435 2102087 := bstep (se 1 (by rfl) ⟨1576565, by rfl⟩ : syracuseStep 2102087 = 3153131) B3153131
theorem B2364853 : Blo 2101435 2364853 := bbase (se 5 (by rfl) ⟨110852, by rfl⟩ : syracuseStep 2364853 = 221705) (by norm_num)
theorem B3153137 : Blo 2101435 3153137 := bstep (se 2 (by rfl) ⟨1182426, by rfl⟩ : syracuseStep 3153137 = 2364853) B2364853
theorem B2102091 : Blo 2101435 2102091 := bstep (se 1 (by rfl) ⟨1576568, by rfl⟩ : syracuseStep 2102091 = 3153137) B3153137
theorem B2660465 : Blo 2101435 2660465 := bbase (se 2 (by rfl) ⟨997674, by rfl⟩ : syracuseStep 2660465 = 1995349) (by norm_num)
theorem B7094573 : Blo 2101435 7094573 := bstep (se 3 (by rfl) ⟨1330232, by rfl⟩ : syracuseStep 7094573 = 2660465) B2660465
theorem B4729715 : Blo 2101435 4729715 := bstep (se 1 (by rfl) ⟨3547286, by rfl⟩ : syracuseStep 4729715 = 7094573) B7094573
theorem B3153143 : Blo 2101435 3153143 := bstep (se 1 (by rfl) ⟨2364857, by rfl⟩ : syracuseStep 3153143 = 4729715) B4729715
theorem B2102095 : Blo 2101435 2102095 := bstep (se 1 (by rfl) ⟨1576571, by rfl⟩ : syracuseStep 2102095 = 3153143) B3153143
theorem B3153149 : Blo 2101435 3153149 := bbase (se 3 (by rfl) ⟨591215, by rfl⟩ : syracuseStep 3153149 = 1182431) (by norm_num)
theorem B2102099 : Blo 2101435 2102099 := bstep (se 1 (by rfl) ⟨1576574, by rfl⟩ : syracuseStep 2102099 = 3153149) B3153149
theorem B4729733 : Blo 2101435 4729733 := bbase (se 4 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 4729733 = 886825) (by norm_num)
theorem B3153155 : Blo 2101435 3153155 := bstep (se 1 (by rfl) ⟨2364866, by rfl⟩ : syracuseStep 3153155 = 4729733) B4729733
theorem B2102103 : Blo 2101435 2102103 := bstep (se 1 (by rfl) ⟨1576577, by rfl⟩ : syracuseStep 2102103 = 3153155) B3153155
theorem B2244781 : Blo 2101435 2244781 := bbase (se 3 (by rfl) ⟨420896, by rfl⟩ : syracuseStep 2244781 = 841793) (by norm_num)
theorem B2993041 : Blo 2101435 2993041 := bstep (se 2 (by rfl) ⟨1122390, by rfl⟩ : syracuseStep 2993041 = 2244781) B2244781
theorem B3990721 : Blo 2101435 3990721 := bstep (se 2 (by rfl) ⟨1496520, by rfl⟩ : syracuseStep 3990721 = 2993041) B2993041
theorem B5320961 : Blo 2101435 5320961 := bstep (se 2 (by rfl) ⟨1995360, by rfl⟩ : syracuseStep 5320961 = 3990721) B3990721
theorem B3547307 : Blo 2101435 3547307 := bstep (se 1 (by rfl) ⟨2660480, by rfl⟩ : syracuseStep 3547307 = 5320961) B5320961
theorem B2364871 : Blo 2101435 2364871 := bstep (se 1 (by rfl) ⟨1773653, by rfl⟩ : syracuseStep 2364871 = 3547307) B3547307
theorem B3153161 : Blo 2101435 3153161 := bstep (se 2 (by rfl) ⟨1182435, by rfl⟩ : syracuseStep 3153161 = 2364871) B2364871
theorem B2102107 : Blo 2101435 2102107 := bstep (se 1 (by rfl) ⟨1576580, by rfl⟩ : syracuseStep 2102107 = 3153161) B3153161
theorem B10641941 : Blo 2101435 10641941 := bbase (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) (by norm_num)
theorem B7094627 : Blo 2101435 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B4729751 : Blo 2101435 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B3153167 : Blo 2101435 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B2102111 : Blo 2101435 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B3153173 : Blo 2101435 3153173 := bbase (se 6 (by rfl) ⟨73902, by rfl⟩ : syracuseStep 3153173 = 147805) (by norm_num)
theorem B2102115 : Blo 2101435 2102115 := bstep (se 1 (by rfl) ⟨1576586, by rfl⟩ : syracuseStep 2102115 = 3153173) B3153173
theorem B6479621 : Blo 2101435 6479621 := bbase (se 4 (by rfl) ⟨607464, by rfl⟩ : syracuseStep 6479621 = 1214929) (by norm_num)
theorem B4319747 : Blo 2101435 4319747 := bstep (se 1 (by rfl) ⟨3239810, by rfl⟩ : syracuseStep 4319747 = 6479621) B6479621
theorem B2879831 : Blo 2101435 2879831 := bstep (se 1 (by rfl) ⟨2159873, by rfl⟩ : syracuseStep 2879831 = 4319747) B4319747
theorem B7679549 : Blo 2101435 7679549 := bstep (se 3 (by rfl) ⟨1439915, by rfl⟩ : syracuseStep 7679549 = 2879831) B2879831
theorem B5119699 : Blo 2101435 5119699 := bstep (se 1 (by rfl) ⟨3839774, by rfl⟩ : syracuseStep 5119699 = 7679549) B7679549
theorem B6826265 : Blo 2101435 6826265 := bstep (se 2 (by rfl) ⟨2559849, by rfl⟩ : syracuseStep 6826265 = 5119699) B5119699
theorem B4550843 : Blo 2101435 4550843 := bstep (se 1 (by rfl) ⟨3413132, by rfl⟩ : syracuseStep 4550843 = 6826265) B6826265
theorem B12135581 : Blo 2101435 12135581 := bstep (se 3 (by rfl) ⟨2275421, by rfl⟩ : syracuseStep 12135581 = 4550843) B4550843
theorem B8090387 : Blo 2101435 8090387 := bstep (se 1 (by rfl) ⟨6067790, by rfl⟩ : syracuseStep 8090387 = 12135581) B12135581
theorem B5393591 : Blo 2101435 5393591 := bstep (se 1 (by rfl) ⟨4045193, by rfl⟩ : syracuseStep 5393591 = 8090387) B8090387
theorem B3595727 : Blo 2101435 3595727 := bstep (se 1 (by rfl) ⟨2696795, by rfl⟩ : syracuseStep 3595727 = 5393591) B5393591
theorem B2397151 : Blo 2101435 2397151 := bstep (se 1 (by rfl) ⟨1797863, by rfl⟩ : syracuseStep 2397151 = 3595727) B3595727
theorem B3196201 : Blo 2101435 3196201 := bstep (se 2 (by rfl) ⟨1198575, by rfl⟩ : syracuseStep 3196201 = 2397151) B2397151
theorem B4261601 : Blo 2101435 4261601 := bstep (se 2 (by rfl) ⟨1598100, by rfl⟩ : syracuseStep 4261601 = 3196201) B3196201
theorem B2841067 : Blo 2101435 2841067 := bstep (se 1 (by rfl) ⟨2130800, by rfl⟩ : syracuseStep 2841067 = 4261601) B4261601
theorem B3788089 : Blo 2101435 3788089 := bstep (se 2 (by rfl) ⟨1420533, by rfl⟩ : syracuseStep 3788089 = 2841067) B2841067
theorem B20203141 : Blo 2101435 20203141 := bstep (se 4 (by rfl) ⟨1894044, by rfl⟩ : syracuseStep 20203141 = 3788089) B3788089
theorem B26937521 : Blo 2101435 26937521 := bstep (se 2 (by rfl) ⟨10101570, by rfl⟩ : syracuseStep 26937521 = 20203141) B20203141
theorem B17958347 : Blo 2101435 17958347 := bstep (se 1 (by rfl) ⟨13468760, by rfl⟩ : syracuseStep 17958347 = 26937521) B26937521
theorem B11972231 : Blo 2101435 11972231 := bstep (se 1 (by rfl) ⟨8979173, by rfl⟩ : syracuseStep 11972231 = 17958347) B17958347
theorem B7981487 : Blo 2101435 7981487 := bstep (se 1 (by rfl) ⟨5986115, by rfl⟩ : syracuseStep 7981487 = 11972231) B11972231
theorem B5320991 : Blo 2101435 5320991 := bstep (se 1 (by rfl) ⟨3990743, by rfl⟩ : syracuseStep 5320991 = 7981487) B7981487
theorem B3547327 : Blo 2101435 3547327 := bstep (se 1 (by rfl) ⟨2660495, by rfl⟩ : syracuseStep 3547327 = 5320991) B5320991
theorem B4729769 : Blo 2101435 4729769 := bstep (se 2 (by rfl) ⟨1773663, by rfl⟩ : syracuseStep 4729769 = 3547327) B3547327
theorem B3153179 : Blo 2101435 3153179 := bstep (se 1 (by rfl) ⟨2364884, by rfl⟩ : syracuseStep 3153179 = 4729769) B4729769
theorem B2102119 : Blo 2101435 2102119 := bstep (se 1 (by rfl) ⟨1576589, by rfl⟩ : syracuseStep 2102119 = 3153179) B3153179
theorem B2364889 : Blo 2101435 2364889 := bbase (se 2 (by rfl) ⟨886833, by rfl⟩ : syracuseStep 2364889 = 1773667) (by norm_num)
theorem B3153185 : Blo 2101435 3153185 := bstep (se 2 (by rfl) ⟨1182444, by rfl⟩ : syracuseStep 3153185 = 2364889) B2364889
theorem B2102123 : Blo 2101435 2102123 := bstep (se 1 (by rfl) ⟨1576592, by rfl⟩ : syracuseStep 2102123 = 3153185) B3153185
theorem B2993069 : Blo 2101435 2993069 := bbase (se 3 (by rfl) ⟨561200, by rfl⟩ : syracuseStep 2993069 = 1122401) (by norm_num)
theorem B7981517 : Blo 2101435 7981517 := bstep (se 3 (by rfl) ⟨1496534, by rfl⟩ : syracuseStep 7981517 = 2993069) B2993069
theorem B5321011 : Blo 2101435 5321011 := bstep (se 1 (by rfl) ⟨3990758, by rfl⟩ : syracuseStep 5321011 = 7981517) B7981517
theorem B7094681 : Blo 2101435 7094681 := bstep (se 2 (by rfl) ⟨2660505, by rfl⟩ : syracuseStep 7094681 = 5321011) B5321011
theorem B4729787 : Blo 2101435 4729787 := bstep (se 1 (by rfl) ⟨3547340, by rfl⟩ : syracuseStep 4729787 = 7094681) B7094681
theorem B3153191 : Blo 2101435 3153191 := bstep (se 1 (by rfl) ⟨2364893, by rfl⟩ : syracuseStep 3153191 = 4729787) B4729787
theorem B2102127 : Blo 2101435 2102127 := bstep (se 1 (by rfl) ⟨1576595, by rfl⟩ : syracuseStep 2102127 = 3153191) B3153191
theorem B3153197 : Blo 2101435 3153197 := bbase (se 3 (by rfl) ⟨591224, by rfl⟩ : syracuseStep 3153197 = 1182449) (by norm_num)
theorem B2102131 : Blo 2101435 2102131 := bstep (se 1 (by rfl) ⟨1576598, by rfl⟩ : syracuseStep 2102131 = 3153197) B3153197
theorem B4729805 : Blo 2101435 4729805 := bbase (se 3 (by rfl) ⟨886838, by rfl⟩ : syracuseStep 4729805 = 1773677) (by norm_num)
theorem B3153203 : Blo 2101435 3153203 := bstep (se 1 (by rfl) ⟨2364902, by rfl⟩ : syracuseStep 3153203 = 4729805) B4729805
theorem B2102135 : Blo 2101435 2102135 := bstep (se 1 (by rfl) ⟨1576601, by rfl⟩ : syracuseStep 2102135 = 3153203) B3153203
theorem B2660521 : Blo 2101435 2660521 := bbase (se 2 (by rfl) ⟨997695, by rfl⟩ : syracuseStep 2660521 = 1995391) (by norm_num)
theorem B3547361 : Blo 2101435 3547361 := bstep (se 2 (by rfl) ⟨1330260, by rfl⟩ : syracuseStep 3547361 = 2660521) B2660521
theorem B2364907 : Blo 2101435 2364907 := bstep (se 1 (by rfl) ⟨1773680, by rfl⟩ : syracuseStep 2364907 = 3547361) B3547361
theorem B3153209 : Blo 2101435 3153209 := bstep (se 2 (by rfl) ⟨1182453, by rfl⟩ : syracuseStep 3153209 = 2364907) B2364907
theorem B2102139 : Blo 2101435 2102139 := bstep (se 1 (by rfl) ⟨1576604, by rfl⟩ : syracuseStep 2102139 = 3153209) B3153209
theorem B10101685 : Blo 2101435 10101685 := bbase (se 5 (by rfl) ⟨473516, by rfl⟩ : syracuseStep 10101685 = 947033) (by norm_num)
theorem B13468913 : Blo 2101435 13468913 := bstep (se 2 (by rfl) ⟨5050842, by rfl⟩ : syracuseStep 13468913 = 10101685) B10101685
theorem B8979275 : Blo 2101435 8979275 := bstep (se 1 (by rfl) ⟨6734456, by rfl⟩ : syracuseStep 8979275 = 13468913) B13468913
theorem B23944733 : Blo 2101435 23944733 := bstep (se 3 (by rfl) ⟨4489637, by rfl⟩ : syracuseStep 23944733 = 8979275) B8979275
theorem B15963155 : Blo 2101435 15963155 := bstep (se 1 (by rfl) ⟨11972366, by rfl⟩ : syracuseStep 15963155 = 23944733) B23944733
theorem B10642103 : Blo 2101435 10642103 := bstep (se 1 (by rfl) ⟨7981577, by rfl⟩ : syracuseStep 10642103 = 15963155) B15963155
theorem B7094735 : Blo 2101435 7094735 := bstep (se 1 (by rfl) ⟨5321051, by rfl⟩ : syracuseStep 7094735 = 10642103) B10642103
theorem B4729823 : Blo 2101435 4729823 := bstep (se 1 (by rfl) ⟨3547367, by rfl⟩ : syracuseStep 4729823 = 7094735) B7094735
theorem B3153215 : Blo 2101435 3153215 := bstep (se 1 (by rfl) ⟨2364911, by rfl⟩ : syracuseStep 3153215 = 4729823) B4729823
theorem B2102143 : Blo 2101435 2102143 := bstep (se 1 (by rfl) ⟨1576607, by rfl⟩ : syracuseStep 2102143 = 3153215) B3153215
theorem B3153221 : Blo 2101435 3153221 := bbase (se 4 (by rfl) ⟨295614, by rfl⟩ : syracuseStep 3153221 = 591229) (by norm_num)
theorem B2102147 : Blo 2101435 2102147 := bstep (se 1 (by rfl) ⟨1576610, by rfl⟩ : syracuseStep 2102147 = 3153221) B3153221
theorem B3547381 : Blo 2101435 3547381 := bbase (se 5 (by rfl) ⟨166283, by rfl⟩ : syracuseStep 3547381 = 332567) (by norm_num)
theorem B4729841 : Blo 2101435 4729841 := bstep (se 2 (by rfl) ⟨1773690, by rfl⟩ : syracuseStep 4729841 = 3547381) B3547381
theorem B3153227 : Blo 2101435 3153227 := bstep (se 1 (by rfl) ⟨2364920, by rfl⟩ : syracuseStep 3153227 = 4729841) B4729841
theorem B2102151 : Blo 2101435 2102151 := bstep (se 1 (by rfl) ⟨1576613, by rfl⟩ : syracuseStep 2102151 = 3153227) B3153227
theorem B2364925 : Blo 2101435 2364925 := bbase (se 3 (by rfl) ⟨443423, by rfl⟩ : syracuseStep 2364925 = 886847) (by norm_num)
theorem B3153233 : Blo 2101435 3153233 := bstep (se 2 (by rfl) ⟨1182462, by rfl⟩ : syracuseStep 3153233 = 2364925) B2364925
theorem B2102155 : Blo 2101435 2102155 := bstep (se 1 (by rfl) ⟨1576616, by rfl⟩ : syracuseStep 2102155 = 3153233) B3153233
theorem B7094789 : Blo 2101435 7094789 := bbase (se 4 (by rfl) ⟨665136, by rfl⟩ : syracuseStep 7094789 = 1330273) (by norm_num)
theorem B4729859 : Blo 2101435 4729859 := bstep (se 1 (by rfl) ⟨3547394, by rfl⟩ : syracuseStep 4729859 = 7094789) B7094789
theorem B3153239 : Blo 2101435 3153239 := bstep (se 1 (by rfl) ⟨2364929, by rfl⟩ : syracuseStep 3153239 = 4729859) B4729859
theorem B2102159 : Blo 2101435 2102159 := bstep (se 1 (by rfl) ⟨1576619, by rfl⟩ : syracuseStep 2102159 = 3153239) B3153239
theorem B3153245 : Blo 2101435 3153245 := bbase (se 3 (by rfl) ⟨591233, by rfl⟩ : syracuseStep 3153245 = 1182467) (by norm_num)
theorem B2102163 : Blo 2101435 2102163 := bstep (se 1 (by rfl) ⟨1576622, by rfl⟩ : syracuseStep 2102163 = 3153245) B3153245
theorem B4729877 : Blo 2101435 4729877 := bbase (se 6 (by rfl) ⟨110856, by rfl⟩ : syracuseStep 4729877 = 221713) (by norm_num)
theorem B3153251 : Blo 2101435 3153251 := bstep (se 1 (by rfl) ⟨2364938, by rfl⟩ : syracuseStep 3153251 = 4729877) B4729877
theorem B2102167 : Blo 2101435 2102167 := bstep (se 1 (by rfl) ⟨1576625, by rfl⟩ : syracuseStep 2102167 = 3153251) B3153251
theorem B7981685 : Blo 2101435 7981685 := bbase (se 5 (by rfl) ⟨374141, by rfl⟩ : syracuseStep 7981685 = 748283) (by norm_num)
theorem B5321123 : Blo 2101435 5321123 := bstep (se 1 (by rfl) ⟨3990842, by rfl⟩ : syracuseStep 5321123 = 7981685) B7981685
theorem B3547415 : Blo 2101435 3547415 := bstep (se 1 (by rfl) ⟨2660561, by rfl⟩ : syracuseStep 3547415 = 5321123) B5321123
theorem B2364943 : Blo 2101435 2364943 := bstep (se 1 (by rfl) ⟨1773707, by rfl⟩ : syracuseStep 2364943 = 3547415) B3547415
theorem B3153257 : Blo 2101435 3153257 := bstep (se 2 (by rfl) ⟨1182471, by rfl⟩ : syracuseStep 3153257 = 2364943) B2364943
theorem B2102171 : Blo 2101435 2102171 := bstep (se 1 (by rfl) ⟨1576628, by rfl⟩ : syracuseStep 2102171 = 3153257) B3153257
theorem B2244853 : Blo 2101435 2244853 := bbase (se 5 (by rfl) ⟨105227, by rfl⟩ : syracuseStep 2244853 = 210455) (by norm_num)
theorem B11972549 : Blo 2101435 11972549 := bstep (se 4 (by rfl) ⟨1122426, by rfl⟩ : syracuseStep 11972549 = 2244853) B2244853
theorem B7981699 : Blo 2101435 7981699 := bstep (se 1 (by rfl) ⟨5986274, by rfl⟩ : syracuseStep 7981699 = 11972549) B11972549
theorem B10642265 : Blo 2101435 10642265 := bstep (se 2 (by rfl) ⟨3990849, by rfl⟩ : syracuseStep 10642265 = 7981699) B7981699
theorem B7094843 : Blo 2101435 7094843 := bstep (se 1 (by rfl) ⟨5321132, by rfl⟩ : syracuseStep 7094843 = 10642265) B10642265
theorem B4729895 : Blo 2101435 4729895 := bstep (se 1 (by rfl) ⟨3547421, by rfl⟩ : syracuseStep 4729895 = 7094843) B7094843
theorem B3153263 : Blo 2101435 3153263 := bstep (se 1 (by rfl) ⟨2364947, by rfl⟩ : syracuseStep 3153263 = 4729895) B4729895
theorem B2102175 : Blo 2101435 2102175 := bstep (se 1 (by rfl) ⟨1576631, by rfl⟩ : syracuseStep 2102175 = 3153263) B3153263
theorem B3153269 : Blo 2101435 3153269 := bbase (se 5 (by rfl) ⟨147809, by rfl⟩ : syracuseStep 3153269 = 295619) (by norm_num)
theorem B2102179 : Blo 2101435 2102179 := bstep (se 1 (by rfl) ⟨1576634, by rfl⟩ : syracuseStep 2102179 = 3153269) B3153269
theorem B2993149 : Blo 2101435 2993149 := bbase (se 3 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 2993149 = 1122431) (by norm_num)
theorem B3990865 : Blo 2101435 3990865 := bstep (se 2 (by rfl) ⟨1496574, by rfl⟩ : syracuseStep 3990865 = 2993149) B2993149
theorem B5321153 : Blo 2101435 5321153 := bstep (se 2 (by rfl) ⟨1995432, by rfl⟩ : syracuseStep 5321153 = 3990865) B3990865
theorem B3547435 : Blo 2101435 3547435 := bstep (se 1 (by rfl) ⟨2660576, by rfl⟩ : syracuseStep 3547435 = 5321153) B5321153
theorem B4729913 : Blo 2101435 4729913 := bstep (se 2 (by rfl) ⟨1773717, by rfl⟩ : syracuseStep 4729913 = 3547435) B3547435
theorem B3153275 : Blo 2101435 3153275 := bstep (se 1 (by rfl) ⟨2364956, by rfl⟩ : syracuseStep 3153275 = 4729913) B4729913
theorem B2102183 : Blo 2101435 2102183 := bstep (se 1 (by rfl) ⟨1576637, by rfl⟩ : syracuseStep 2102183 = 3153275) B3153275
theorem B2364961 : Blo 2101435 2364961 := bbase (se 2 (by rfl) ⟨886860, by rfl⟩ : syracuseStep 2364961 = 1773721) (by norm_num)
theorem B3153281 : Blo 2101435 3153281 := bstep (se 2 (by rfl) ⟨1182480, by rfl⟩ : syracuseStep 3153281 = 2364961) B2364961
theorem B2102187 : Blo 2101435 2102187 := bstep (se 1 (by rfl) ⟨1576640, by rfl⟩ : syracuseStep 2102187 = 3153281) B3153281
theorem B5321173 : Blo 2101435 5321173 := bbase (se 7 (by rfl) ⟨62357, by rfl⟩ : syracuseStep 5321173 = 124715) (by norm_num)
theorem B7094897 : Blo 2101435 7094897 := bstep (se 2 (by rfl) ⟨2660586, by rfl⟩ : syracuseStep 7094897 = 5321173) B5321173
theorem B4729931 : Blo 2101435 4729931 := bstep (se 1 (by rfl) ⟨3547448, by rfl⟩ : syracuseStep 4729931 = 7094897) B7094897
theorem B3153287 : Blo 2101435 3153287 := bstep (se 1 (by rfl) ⟨2364965, by rfl⟩ : syracuseStep 3153287 = 4729931) B4729931
theorem B2102191 : Blo 2101435 2102191 := bstep (se 1 (by rfl) ⟨1576643, by rfl⟩ : syracuseStep 2102191 = 3153287) B3153287
theorem B3153293 : Blo 2101435 3153293 := bbase (se 3 (by rfl) ⟨591242, by rfl⟩ : syracuseStep 3153293 = 1182485) (by norm_num)
theorem B2102195 : Blo 2101435 2102195 := bstep (se 1 (by rfl) ⟨1576646, by rfl⟩ : syracuseStep 2102195 = 3153293) B3153293
theorem B4729949 : Blo 2101435 4729949 := bbase (se 3 (by rfl) ⟨886865, by rfl⟩ : syracuseStep 4729949 = 1773731) (by norm_num)
theorem B3153299 : Blo 2101435 3153299 := bstep (se 1 (by rfl) ⟨2364974, by rfl⟩ : syracuseStep 3153299 = 4729949) B4729949
theorem B2102199 : Blo 2101435 2102199 := bstep (se 1 (by rfl) ⟨1576649, by rfl⟩ : syracuseStep 2102199 = 3153299) B3153299
theorem B3547469 : Blo 2101435 3547469 := bbase (se 3 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 3547469 = 1330301) (by norm_num)
theorem B2364979 : Blo 2101435 2364979 := bstep (se 1 (by rfl) ⟨1773734, by rfl⟩ : syracuseStep 2364979 = 3547469) B3547469
theorem B3153305 : Blo 2101435 3153305 := bstep (se 2 (by rfl) ⟨1182489, by rfl⟩ : syracuseStep 3153305 = 2364979) B2364979
theorem B2102203 : Blo 2101435 2102203 := bstep (se 1 (by rfl) ⟨1576652, by rfl⟩ : syracuseStep 2102203 = 3153305) B3153305
theorem B8523557 : Blo 2101435 8523557 := bbase (se 4 (by rfl) ⟨799083, by rfl⟩ : syracuseStep 8523557 = 1598167) (by norm_num)
theorem B5682371 : Blo 2101435 5682371 := bstep (se 1 (by rfl) ⟨4261778, by rfl⟩ : syracuseStep 5682371 = 8523557) B8523557
theorem B15152989 : Blo 2101435 15152989 := bstep (se 3 (by rfl) ⟨2841185, by rfl⟩ : syracuseStep 15152989 = 5682371) B5682371
theorem B20203985 : Blo 2101435 20203985 := bstep (se 2 (by rfl) ⟨7576494, by rfl⟩ : syracuseStep 20203985 = 15152989) B15152989
theorem B13469323 : Blo 2101435 13469323 := bstep (se 1 (by rfl) ⟨10101992, by rfl⟩ : syracuseStep 13469323 = 20203985) B20203985
theorem B17959097 : Blo 2101435 17959097 := bstep (se 2 (by rfl) ⟨6734661, by rfl⟩ : syracuseStep 17959097 = 13469323) B13469323
theorem B11972731 : Blo 2101435 11972731 := bstep (se 1 (by rfl) ⟨8979548, by rfl⟩ : syracuseStep 11972731 = 17959097) B17959097
theorem B15963641 : Blo 2101435 15963641 := bstep (se 2 (by rfl) ⟨5986365, by rfl⟩ : syracuseStep 15963641 = 11972731) B11972731
theorem B10642427 : Blo 2101435 10642427 := bstep (se 1 (by rfl) ⟨7981820, by rfl⟩ : syracuseStep 10642427 = 15963641) B15963641
theorem B7094951 : Blo 2101435 7094951 := bstep (se 1 (by rfl) ⟨5321213, by rfl⟩ : syracuseStep 7094951 = 10642427) B10642427
theorem B4729967 : Blo 2101435 4729967 := bstep (se 1 (by rfl) ⟨3547475, by rfl⟩ : syracuseStep 4729967 = 7094951) B7094951
theorem B3153311 : Blo 2101435 3153311 := bstep (se 1 (by rfl) ⟨2364983, by rfl⟩ : syracuseStep 3153311 = 4729967) B4729967
theorem B2102207 : Blo 2101435 2102207 := bstep (se 1 (by rfl) ⟨1576655, by rfl⟩ : syracuseStep 2102207 = 3153311) B3153311
theorem B3153317 : Blo 2101435 3153317 := bbase (se 4 (by rfl) ⟨295623, by rfl⟩ : syracuseStep 3153317 = 591247) (by norm_num)
theorem B2102211 : Blo 2101435 2102211 := bstep (se 1 (by rfl) ⟨1576658, by rfl⟩ : syracuseStep 2102211 = 3153317) B3153317
theorem B2660617 : Blo 2101435 2660617 := bbase (se 2 (by rfl) ⟨997731, by rfl⟩ : syracuseStep 2660617 = 1995463) (by norm_num)
theorem B3547489 : Blo 2101435 3547489 := bstep (se 2 (by rfl) ⟨1330308, by rfl⟩ : syracuseStep 3547489 = 2660617) B2660617
theorem B4729985 : Blo 2101435 4729985 := bstep (se 2 (by rfl) ⟨1773744, by rfl⟩ : syracuseStep 4729985 = 3547489) B3547489
theorem B3153323 : Blo 2101435 3153323 := bstep (se 1 (by rfl) ⟨2364992, by rfl⟩ : syracuseStep 3153323 = 4729985) B4729985
theorem B2102215 : Blo 2101435 2102215 := bstep (se 1 (by rfl) ⟨1576661, by rfl⟩ : syracuseStep 2102215 = 3153323) B3153323
theorem B2364997 : Blo 2101435 2364997 := bbase (se 4 (by rfl) ⟨221718, by rfl⟩ : syracuseStep 2364997 = 443437) (by norm_num)
theorem B3153329 : Blo 2101435 3153329 := bstep (se 2 (by rfl) ⟨1182498, by rfl⟩ : syracuseStep 3153329 = 2364997) B2364997
theorem B2102219 : Blo 2101435 2102219 := bstep (se 1 (by rfl) ⟨1576664, by rfl⟩ : syracuseStep 2102219 = 3153329) B3153329
theorem B3990941 : Blo 2101435 3990941 := bbase (se 3 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 3990941 = 1496603) (by norm_num)
theorem B2660627 : Blo 2101435 2660627 := bstep (se 1 (by rfl) ⟨1995470, by rfl⟩ : syracuseStep 2660627 = 3990941) B3990941
theorem B7095005 : Blo 2101435 7095005 := bstep (se 3 (by rfl) ⟨1330313, by rfl⟩ : syracuseStep 7095005 = 2660627) B2660627
theorem B4730003 : Blo 2101435 4730003 := bstep (se 1 (by rfl) ⟨3547502, by rfl⟩ : syracuseStep 4730003 = 7095005) B7095005
theorem B3153335 : Blo 2101435 3153335 := bstep (se 1 (by rfl) ⟨2365001, by rfl⟩ : syracuseStep 3153335 = 4730003) B4730003
theorem B2102223 : Blo 2101435 2102223 := bstep (se 1 (by rfl) ⟨1576667, by rfl⟩ : syracuseStep 2102223 = 3153335) B3153335
theorem B3153341 : Blo 2101435 3153341 := bbase (se 3 (by rfl) ⟨591251, by rfl⟩ : syracuseStep 3153341 = 1182503) (by norm_num)
theorem B2102227 : Blo 2101435 2102227 := bstep (se 1 (by rfl) ⟨1576670, by rfl⟩ : syracuseStep 2102227 = 3153341) B3153341
theorem B4730021 : Blo 2101435 4730021 := bbase (se 4 (by rfl) ⟨443439, by rfl⟩ : syracuseStep 4730021 = 886879) (by norm_num)
theorem B3153347 : Blo 2101435 3153347 := bstep (se 1 (by rfl) ⟨2365010, by rfl⟩ : syracuseStep 3153347 = 4730021) B4730021
theorem B2102231 : Blo 2101435 2102231 := bstep (se 1 (by rfl) ⟨1576673, by rfl⟩ : syracuseStep 2102231 = 3153347) B3153347
theorem B5321285 : Blo 2101435 5321285 := bbase (se 4 (by rfl) ⟨498870, by rfl⟩ : syracuseStep 5321285 = 997741) (by norm_num)
theorem B3547523 : Blo 2101435 3547523 := bstep (se 1 (by rfl) ⟨2660642, by rfl⟩ : syracuseStep 3547523 = 5321285) B5321285
theorem B2365015 : Blo 2101435 2365015 := bstep (se 1 (by rfl) ⟨1773761, by rfl⟩ : syracuseStep 2365015 = 3547523) B3547523
theorem B3153353 : Blo 2101435 3153353 := bstep (se 2 (by rfl) ⟨1182507, by rfl⟩ : syracuseStep 3153353 = 2365015) B2365015
theorem B2102235 : Blo 2101435 2102235 := bstep (se 1 (by rfl) ⟨1576676, by rfl⟩ : syracuseStep 2102235 = 3153353) B3153353
theorem B2525537 : Blo 2101435 2525537 := bbase (se 2 (by rfl) ⟨947076, by rfl⟩ : syracuseStep 2525537 = 1894153) (by norm_num)
theorem B6734765 : Blo 2101435 6734765 := bstep (se 3 (by rfl) ⟨1262768, by rfl⟩ : syracuseStep 6734765 = 2525537) B2525537
theorem B4489843 : Blo 2101435 4489843 := bstep (se 1 (by rfl) ⟨3367382, by rfl⟩ : syracuseStep 4489843 = 6734765) B6734765
theorem B5986457 : Blo 2101435 5986457 := bstep (se 2 (by rfl) ⟨2244921, by rfl⟩ : syracuseStep 5986457 = 4489843) B4489843
theorem B3990971 : Blo 2101435 3990971 := bstep (se 1 (by rfl) ⟨2993228, by rfl⟩ : syracuseStep 3990971 = 5986457) B5986457
theorem B10642589 : Blo 2101435 10642589 := bstep (se 3 (by rfl) ⟨1995485, by rfl⟩ : syracuseStep 10642589 = 3990971) B3990971
theorem B7095059 : Blo 2101435 7095059 := bstep (se 1 (by rfl) ⟨5321294, by rfl⟩ : syracuseStep 7095059 = 10642589) B10642589
theorem B4730039 : Blo 2101435 4730039 := bstep (se 1 (by rfl) ⟨3547529, by rfl⟩ : syracuseStep 4730039 = 7095059) B7095059
theorem B3153359 : Blo 2101435 3153359 := bstep (se 1 (by rfl) ⟨2365019, by rfl⟩ : syracuseStep 3153359 = 4730039) B4730039
theorem B2102239 : Blo 2101435 2102239 := bstep (se 1 (by rfl) ⟨1576679, by rfl⟩ : syracuseStep 2102239 = 3153359) B3153359
theorem B3153365 : Blo 2101435 3153365 := bbase (se 7 (by rfl) ⟨36953, by rfl⟩ : syracuseStep 3153365 = 73907) (by norm_num)
theorem B2102243 : Blo 2101435 2102243 := bstep (se 1 (by rfl) ⟨1576682, by rfl⟩ : syracuseStep 2102243 = 3153365) B3153365
theorem B7981973 : Blo 2101435 7981973 := bbase (se 6 (by rfl) ⟨187077, by rfl⟩ : syracuseStep 7981973 = 374155) (by norm_num)
theorem B5321315 : Blo 2101435 5321315 := bstep (se 1 (by rfl) ⟨3990986, by rfl⟩ : syracuseStep 5321315 = 7981973) B7981973
theorem B3547543 : Blo 2101435 3547543 := bstep (se 1 (by rfl) ⟨2660657, by rfl⟩ : syracuseStep 3547543 = 5321315) B5321315
theorem B4730057 : Blo 2101435 4730057 := bstep (se 2 (by rfl) ⟨1773771, by rfl⟩ : syracuseStep 4730057 = 3547543) B3547543
theorem B3153371 : Blo 2101435 3153371 := bstep (se 1 (by rfl) ⟨2365028, by rfl⟩ : syracuseStep 3153371 = 4730057) B4730057
theorem B2102247 : Blo 2101435 2102247 := bstep (se 1 (by rfl) ⟨1576685, by rfl⟩ : syracuseStep 2102247 = 3153371) B3153371
theorem B2365033 : Blo 2101435 2365033 := bbase (se 2 (by rfl) ⟨886887, by rfl⟩ : syracuseStep 2365033 = 1773775) (by norm_num)
theorem B3153377 : Blo 2101435 3153377 := bstep (se 2 (by rfl) ⟨1182516, by rfl⟩ : syracuseStep 3153377 = 2365033) B2365033
theorem B2102251 : Blo 2101435 2102251 := bstep (se 1 (by rfl) ⟨1576688, by rfl⟩ : syracuseStep 2102251 = 3153377) B3153377
theorem B4489877 : Blo 2101435 4489877 := bbase (se 6 (by rfl) ⟨105231, by rfl⟩ : syracuseStep 4489877 = 210463) (by norm_num)
theorem B11973005 : Blo 2101435 11973005 := bstep (se 3 (by rfl) ⟨2244938, by rfl⟩ : syracuseStep 11973005 = 4489877) B4489877
theorem B7982003 : Blo 2101435 7982003 := bstep (se 1 (by rfl) ⟨5986502, by rfl⟩ : syracuseStep 7982003 = 11973005) B11973005
theorem B5321335 : Blo 2101435 5321335 := bstep (se 1 (by rfl) ⟨3991001, by rfl⟩ : syracuseStep 5321335 = 7982003) B7982003
theorem B7095113 : Blo 2101435 7095113 := bstep (se 2 (by rfl) ⟨2660667, by rfl⟩ : syracuseStep 7095113 = 5321335) B5321335
theorem B4730075 : Blo 2101435 4730075 := bstep (se 1 (by rfl) ⟨3547556, by rfl⟩ : syracuseStep 4730075 = 7095113) B7095113
theorem B3153383 : Blo 2101435 3153383 := bstep (se 1 (by rfl) ⟨2365037, by rfl⟩ : syracuseStep 3153383 = 4730075) B4730075
theorem B2102255 : Blo 2101435 2102255 := bstep (se 1 (by rfl) ⟨1576691, by rfl⟩ : syracuseStep 2102255 = 3153383) B3153383
theorem B3153389 : Blo 2101435 3153389 := bbase (se 3 (by rfl) ⟨591260, by rfl⟩ : syracuseStep 3153389 = 1182521) (by norm_num)
theorem B2102259 : Blo 2101435 2102259 := bstep (se 1 (by rfl) ⟨1576694, by rfl⟩ : syracuseStep 2102259 = 3153389) B3153389
theorem B4730093 : Blo 2101435 4730093 := bbase (se 3 (by rfl) ⟨886892, by rfl⟩ : syracuseStep 4730093 = 1773785) (by norm_num)
theorem B3153395 : Blo 2101435 3153395 := bstep (se 1 (by rfl) ⟨2365046, by rfl⟩ : syracuseStep 3153395 = 4730093) B4730093
theorem B2102263 : Blo 2101435 2102263 := bstep (se 1 (by rfl) ⟨1576697, by rfl⟩ : syracuseStep 2102263 = 3153395) B3153395
theorem B2993269 : Blo 2101435 2993269 := bbase (se 5 (by rfl) ⟨140309, by rfl⟩ : syracuseStep 2993269 = 280619) (by norm_num)
theorem B3991025 : Blo 2101435 3991025 := bstep (se 2 (by rfl) ⟨1496634, by rfl⟩ : syracuseStep 3991025 = 2993269) B2993269
theorem B2660683 : Blo 2101435 2660683 := bstep (se 1 (by rfl) ⟨1995512, by rfl⟩ : syracuseStep 2660683 = 3991025) B3991025
theorem B3547577 : Blo 2101435 3547577 := bstep (se 2 (by rfl) ⟨1330341, by rfl⟩ : syracuseStep 3547577 = 2660683) B2660683
theorem B2365051 : Blo 2101435 2365051 := bstep (se 1 (by rfl) ⟨1773788, by rfl⟩ : syracuseStep 2365051 = 3547577) B3547577
theorem B3153401 : Blo 2101435 3153401 := bstep (se 2 (by rfl) ⟨1182525, by rfl⟩ : syracuseStep 3153401 = 2365051) B2365051
theorem B2102267 : Blo 2101435 2102267 := bstep (se 1 (by rfl) ⟨1576700, by rfl⟩ : syracuseStep 2102267 = 3153401) B3153401
theorem B2560033 : Blo 2101435 2560033 := bbase (se 2 (by rfl) ⟨960012, by rfl⟩ : syracuseStep 2560033 = 1920025) (by norm_num)
theorem B3413377 : Blo 2101435 3413377 := bstep (se 2 (by rfl) ⟨1280016, by rfl⟩ : syracuseStep 3413377 = 2560033) B2560033
theorem B4551169 : Blo 2101435 4551169 := bstep (se 2 (by rfl) ⟨1706688, by rfl⟩ : syracuseStep 4551169 = 3413377) B3413377
theorem B6068225 : Blo 2101435 6068225 := bstep (se 2 (by rfl) ⟨2275584, by rfl⟩ : syracuseStep 6068225 = 4551169) B4551169
theorem B4045483 : Blo 2101435 4045483 := bstep (se 1 (by rfl) ⟨3034112, by rfl⟩ : syracuseStep 4045483 = 6068225) B6068225
theorem B21575909 : Blo 2101435 21575909 := bstep (se 4 (by rfl) ⟨2022741, by rfl⟩ : syracuseStep 21575909 = 4045483) B4045483
theorem B57535757 : Blo 2101435 57535757 := bstep (se 3 (by rfl) ⟨10787954, by rfl⟩ : syracuseStep 57535757 = 21575909) B21575909
theorem B38357171 : Blo 2101435 38357171 := bstep (se 1 (by rfl) ⟨28767878, by rfl⟩ : syracuseStep 38357171 = 57535757) B57535757
theorem B25571447 : Blo 2101435 25571447 := bstep (se 1 (by rfl) ⟨19178585, by rfl⟩ : syracuseStep 25571447 = 38357171) B38357171
theorem B17047631 : Blo 2101435 17047631 := bstep (se 1 (by rfl) ⟨12785723, by rfl⟩ : syracuseStep 17047631 = 25571447) B25571447
theorem B45460349 : Blo 2101435 45460349 := bstep (se 3 (by rfl) ⟨8523815, by rfl⟩ : syracuseStep 45460349 = 17047631) B17047631
theorem B30306899 : Blo 2101435 30306899 := bstep (se 1 (by rfl) ⟨22730174, by rfl⟩ : syracuseStep 30306899 = 45460349) B45460349
theorem B80818397 : Blo 2101435 80818397 := bstep (se 3 (by rfl) ⟨15153449, by rfl⟩ : syracuseStep 80818397 = 30306899) B30306899
theorem B53878931 : Blo 2101435 53878931 := bstep (se 1 (by rfl) ⟨40409198, by rfl⟩ : syracuseStep 53878931 = 80818397) B80818397
theorem B35919287 : Blo 2101435 35919287 := bstep (se 1 (by rfl) ⟨26939465, by rfl⟩ : syracuseStep 35919287 = 53878931) B53878931
theorem B23946191 : Blo 2101435 23946191 := bstep (se 1 (by rfl) ⟨17959643, by rfl⟩ : syracuseStep 23946191 = 35919287) B35919287
theorem B15964127 : Blo 2101435 15964127 := bstep (se 1 (by rfl) ⟨11973095, by rfl⟩ : syracuseStep 15964127 = 23946191) B23946191
theorem B10642751 : Blo 2101435 10642751 := bstep (se 1 (by rfl) ⟨7982063, by rfl⟩ : syracuseStep 10642751 = 15964127) B15964127
theorem B7095167 : Blo 2101435 7095167 := bstep (se 1 (by rfl) ⟨5321375, by rfl⟩ : syracuseStep 7095167 = 10642751) B10642751
theorem B4730111 : Blo 2101435 4730111 := bstep (se 1 (by rfl) ⟨3547583, by rfl⟩ : syracuseStep 4730111 = 7095167) B7095167
theorem B3153407 : Blo 2101435 3153407 := bstep (se 1 (by rfl) ⟨2365055, by rfl⟩ : syracuseStep 3153407 = 4730111) B4730111
theorem B2102271 : Blo 2101435 2102271 := bstep (se 1 (by rfl) ⟨1576703, by rfl⟩ : syracuseStep 2102271 = 3153407) B3153407
theorem B3153413 : Blo 2101435 3153413 := bbase (se 4 (by rfl) ⟨295632, by rfl⟩ : syracuseStep 3153413 = 591265) (by norm_num)
theorem B2102275 : Blo 2101435 2102275 := bstep (se 1 (by rfl) ⟨1576706, by rfl⟩ : syracuseStep 2102275 = 3153413) B3153413
theorem B3547597 : Blo 2101435 3547597 := bbase (se 3 (by rfl) ⟨665174, by rfl⟩ : syracuseStep 3547597 = 1330349) (by norm_num)
theorem B4730129 : Blo 2101435 4730129 := bstep (se 2 (by rfl) ⟨1773798, by rfl⟩ : syracuseStep 4730129 = 3547597) B3547597
theorem B3153419 : Blo 2101435 3153419 := bstep (se 1 (by rfl) ⟨2365064, by rfl⟩ : syracuseStep 3153419 = 4730129) B4730129
theorem B2102279 : Blo 2101435 2102279 := bstep (se 1 (by rfl) ⟨1576709, by rfl⟩ : syracuseStep 2102279 = 3153419) B3153419
theorem B2365069 : Blo 2101435 2365069 := bbase (se 3 (by rfl) ⟨443450, by rfl⟩ : syracuseStep 2365069 = 886901) (by norm_num)
theorem B3153425 : Blo 2101435 3153425 := bstep (se 2 (by rfl) ⟨1182534, by rfl⟩ : syracuseStep 3153425 = 2365069) B2365069
theorem B2102283 : Blo 2101435 2102283 := bstep (se 1 (by rfl) ⟨1576712, by rfl⟩ : syracuseStep 2102283 = 3153425) B3153425
theorem B7095221 : Blo 2101435 7095221 := bbase (se 5 (by rfl) ⟨332588, by rfl⟩ : syracuseStep 7095221 = 665177) (by norm_num)
theorem B4730147 : Blo 2101435 4730147 := bstep (se 1 (by rfl) ⟨3547610, by rfl⟩ : syracuseStep 4730147 = 7095221) B7095221
theorem B3153431 : Blo 2101435 3153431 := bstep (se 1 (by rfl) ⟨2365073, by rfl⟩ : syracuseStep 3153431 = 4730147) B4730147
theorem B2102287 : Blo 2101435 2102287 := bstep (se 1 (by rfl) ⟨1576715, by rfl⟩ : syracuseStep 2102287 = 3153431) B3153431
theorem B3153437 : Blo 2101435 3153437 := bbase (se 3 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 3153437 = 1182539) (by norm_num)
theorem B2102291 : Blo 2101435 2102291 := bstep (se 1 (by rfl) ⟨1576718, by rfl⟩ : syracuseStep 2102291 = 3153437) B3153437
theorem B4730165 : Blo 2101435 4730165 := bbase (se 5 (by rfl) ⟨221726, by rfl⟩ : syracuseStep 4730165 = 443453) (by norm_num)
theorem B3153443 : Blo 2101435 3153443 := bstep (se 1 (by rfl) ⟨2365082, by rfl⟩ : syracuseStep 3153443 = 4730165) B4730165
theorem B2102295 : Blo 2101435 2102295 := bstep (se 1 (by rfl) ⟨1576721, by rfl⟩ : syracuseStep 2102295 = 3153443) B3153443
theorem B8640229 : Blo 2101435 8640229 := bbase (se 4 (by rfl) ⟨810021, by rfl⟩ : syracuseStep 8640229 = 1620043) (by norm_num)
theorem B11520305 : Blo 2101435 11520305 := bstep (se 2 (by rfl) ⟨4320114, by rfl⟩ : syracuseStep 11520305 = 8640229) B8640229
theorem B7680203 : Blo 2101435 7680203 := bstep (se 1 (by rfl) ⟨5760152, by rfl⟩ : syracuseStep 7680203 = 11520305) B11520305
theorem B5120135 : Blo 2101435 5120135 := bstep (se 1 (by rfl) ⟨3840101, by rfl⟩ : syracuseStep 5120135 = 7680203) B7680203
theorem B3413423 : Blo 2101435 3413423 := bstep (se 1 (by rfl) ⟨2560067, by rfl⟩ : syracuseStep 3413423 = 5120135) B5120135
theorem B9102461 : Blo 2101435 9102461 := bstep (se 3 (by rfl) ⟨1706711, by rfl⟩ : syracuseStep 9102461 = 3413423) B3413423
theorem B24273229 : Blo 2101435 24273229 := bstep (se 3 (by rfl) ⟨4551230, by rfl⟩ : syracuseStep 24273229 = 9102461) B9102461
theorem B32364305 : Blo 2101435 32364305 := bstep (se 2 (by rfl) ⟨12136614, by rfl⟩ : syracuseStep 32364305 = 24273229) B24273229
theorem B21576203 : Blo 2101435 21576203 := bstep (se 1 (by rfl) ⟨16182152, by rfl⟩ : syracuseStep 21576203 = 32364305) B32364305
theorem B14384135 : Blo 2101435 14384135 := bstep (se 1 (by rfl) ⟨10788101, by rfl⟩ : syracuseStep 14384135 = 21576203) B21576203
theorem B9589423 : Blo 2101435 9589423 := bstep (se 1 (by rfl) ⟨7192067, by rfl⟩ : syracuseStep 9589423 = 14384135) B14384135
theorem B12785897 : Blo 2101435 12785897 := bstep (se 2 (by rfl) ⟨4794711, by rfl⟩ : syracuseStep 12785897 = 9589423) B9589423
theorem B34095725 : Blo 2101435 34095725 := bstep (se 3 (by rfl) ⟨6392948, by rfl⟩ : syracuseStep 34095725 = 12785897) B12785897
theorem B22730483 : Blo 2101435 22730483 := bstep (se 1 (by rfl) ⟨17047862, by rfl⟩ : syracuseStep 22730483 = 34095725) B34095725
theorem B15153655 : Blo 2101435 15153655 := bstep (se 1 (by rfl) ⟨11365241, by rfl⟩ : syracuseStep 15153655 = 22730483) B22730483
theorem B20204873 : Blo 2101435 20204873 := bstep (se 2 (by rfl) ⟨7576827, by rfl⟩ : syracuseStep 20204873 = 15153655) B15153655
theorem B13469915 : Blo 2101435 13469915 := bstep (se 1 (by rfl) ⟨10102436, by rfl⟩ : syracuseStep 13469915 = 20204873) B20204873
theorem B8979943 : Blo 2101435 8979943 := bstep (se 1 (by rfl) ⟨6734957, by rfl⟩ : syracuseStep 8979943 = 13469915) B13469915
theorem B11973257 : Blo 2101435 11973257 := bstep (se 2 (by rfl) ⟨4489971, by rfl⟩ : syracuseStep 11973257 = 8979943) B8979943
theorem B7982171 : Blo 2101435 7982171 := bstep (se 1 (by rfl) ⟨5986628, by rfl⟩ : syracuseStep 7982171 = 11973257) B11973257
theorem B5321447 : Blo 2101435 5321447 := bstep (se 1 (by rfl) ⟨3991085, by rfl⟩ : syracuseStep 5321447 = 7982171) B7982171
theorem B3547631 : Blo 2101435 3547631 := bstep (se 1 (by rfl) ⟨2660723, by rfl⟩ : syracuseStep 3547631 = 5321447) B5321447
theorem B2365087 : Blo 2101435 2365087 := bstep (se 1 (by rfl) ⟨1773815, by rfl⟩ : syracuseStep 2365087 = 3547631) B3547631
theorem B3153449 : Blo 2101435 3153449 := bstep (se 2 (by rfl) ⟨1182543, by rfl⟩ : syracuseStep 3153449 = 2365087) B2365087
theorem B2102299 : Blo 2101435 2102299 := bstep (se 1 (by rfl) ⟨1576724, by rfl⟩ : syracuseStep 2102299 = 3153449) B3153449
theorem B5394061 : Blo 2101435 5394061 := bbase (se 3 (by rfl) ⟨1011386, by rfl⟩ : syracuseStep 5394061 = 2022773) (by norm_num)
theorem B7192081 : Blo 2101435 7192081 := bstep (se 2 (by rfl) ⟨2697030, by rfl⟩ : syracuseStep 7192081 = 5394061) B5394061
theorem B9589441 : Blo 2101435 9589441 := bstep (se 2 (by rfl) ⟨3596040, by rfl⟩ : syracuseStep 9589441 = 7192081) B7192081
theorem B12785921 : Blo 2101435 12785921 := bstep (se 2 (by rfl) ⟨4794720, by rfl⟩ : syracuseStep 12785921 = 9589441) B9589441
theorem B8523947 : Blo 2101435 8523947 := bstep (se 1 (by rfl) ⟨6392960, by rfl⟩ : syracuseStep 8523947 = 12785921) B12785921
theorem B5682631 : Blo 2101435 5682631 := bstep (se 1 (by rfl) ⟨4261973, by rfl⟩ : syracuseStep 5682631 = 8523947) B8523947
theorem B7576841 : Blo 2101435 7576841 := bstep (se 2 (by rfl) ⟨2841315, by rfl⟩ : syracuseStep 7576841 = 5682631) B5682631
theorem B20204909 : Blo 2101435 20204909 := bstep (se 3 (by rfl) ⟨3788420, by rfl⟩ : syracuseStep 20204909 = 7576841) B7576841
theorem B13469939 : Blo 2101435 13469939 := bstep (se 1 (by rfl) ⟨10102454, by rfl⟩ : syracuseStep 13469939 = 20204909) B20204909
theorem B8979959 : Blo 2101435 8979959 := bstep (se 1 (by rfl) ⟨6734969, by rfl⟩ : syracuseStep 8979959 = 13469939) B13469939
theorem B5986639 : Blo 2101435 5986639 := bstep (se 1 (by rfl) ⟨4489979, by rfl⟩ : syracuseStep 5986639 = 8979959) B8979959
theorem B7982185 : Blo 2101435 7982185 := bstep (se 2 (by rfl) ⟨2993319, by rfl⟩ : syracuseStep 7982185 = 5986639) B5986639
theorem B10642913 : Blo 2101435 10642913 := bstep (se 2 (by rfl) ⟨3991092, by rfl⟩ : syracuseStep 10642913 = 7982185) B7982185
theorem B7095275 : Blo 2101435 7095275 := bstep (se 1 (by rfl) ⟨5321456, by rfl⟩ : syracuseStep 7095275 = 10642913) B10642913
theorem B4730183 : Blo 2101435 4730183 := bstep (se 1 (by rfl) ⟨3547637, by rfl⟩ : syracuseStep 4730183 = 7095275) B7095275
theorem B3153455 : Blo 2101435 3153455 := bstep (se 1 (by rfl) ⟨2365091, by rfl⟩ : syracuseStep 3153455 = 4730183) B4730183
theorem B2102303 : Blo 2101435 2102303 := bstep (se 1 (by rfl) ⟨1576727, by rfl⟩ : syracuseStep 2102303 = 3153455) B3153455
theorem B3153461 : Blo 2101435 3153461 := bbase (se 5 (by rfl) ⟨147818, by rfl⟩ : syracuseStep 3153461 = 295637) (by norm_num)
theorem B2102307 : Blo 2101435 2102307 := bstep (se 1 (by rfl) ⟨1576730, by rfl⟩ : syracuseStep 2102307 = 3153461) B3153461
theorem B5321477 : Blo 2101435 5321477 := bbase (se 4 (by rfl) ⟨498888, by rfl⟩ : syracuseStep 5321477 = 997777) (by norm_num)
theorem B3547651 : Blo 2101435 3547651 := bstep (se 1 (by rfl) ⟨2660738, by rfl⟩ : syracuseStep 3547651 = 5321477) B5321477
theorem B4730201 : Blo 2101435 4730201 := bstep (se 2 (by rfl) ⟨1773825, by rfl⟩ : syracuseStep 4730201 = 3547651) B3547651
theorem B3153467 : Blo 2101435 3153467 := bstep (se 1 (by rfl) ⟨2365100, by rfl⟩ : syracuseStep 3153467 = 4730201) B4730201
theorem B2102311 : Blo 2101435 2102311 := bstep (se 1 (by rfl) ⟨1576733, by rfl⟩ : syracuseStep 2102311 = 3153467) B3153467
theorem B2365105 : Blo 2101435 2365105 := bbase (se 2 (by rfl) ⟨886914, by rfl⟩ : syracuseStep 2365105 = 1773829) (by norm_num)
theorem B3153473 : Blo 2101435 3153473 := bstep (se 2 (by rfl) ⟨1182552, by rfl⟩ : syracuseStep 3153473 = 2365105) B2365105
theorem B2102315 : Blo 2101435 2102315 := bstep (se 1 (by rfl) ⟨1576736, by rfl⟩ : syracuseStep 2102315 = 3153473) B3153473
theorem B7576901 : Blo 2101435 7576901 := bbase (se 4 (by rfl) ⟨710334, by rfl⟩ : syracuseStep 7576901 = 1420669) (by norm_num)
theorem B5051267 : Blo 2101435 5051267 := bstep (se 1 (by rfl) ⟨3788450, by rfl⟩ : syracuseStep 5051267 = 7576901) B7576901
theorem B3367511 : Blo 2101435 3367511 := bstep (se 1 (by rfl) ⟨2525633, by rfl⟩ : syracuseStep 3367511 = 5051267) B5051267
theorem B2245007 : Blo 2101435 2245007 := bstep (se 1 (by rfl) ⟨1683755, by rfl⟩ : syracuseStep 2245007 = 3367511) B3367511
theorem B5986685 : Blo 2101435 5986685 := bstep (se 3 (by rfl) ⟨1122503, by rfl⟩ : syracuseStep 5986685 = 2245007) B2245007
theorem B3991123 : Blo 2101435 3991123 := bstep (se 1 (by rfl) ⟨2993342, by rfl⟩ : syracuseStep 3991123 = 5986685) B5986685
theorem B5321497 : Blo 2101435 5321497 := bstep (se 2 (by rfl) ⟨1995561, by rfl⟩ : syracuseStep 5321497 = 3991123) B3991123
theorem B7095329 : Blo 2101435 7095329 := bstep (se 2 (by rfl) ⟨2660748, by rfl⟩ : syracuseStep 7095329 = 5321497) B5321497
theorem B4730219 : Blo 2101435 4730219 := bstep (se 1 (by rfl) ⟨3547664, by rfl⟩ : syracuseStep 4730219 = 7095329) B7095329
theorem B3153479 : Blo 2101435 3153479 := bstep (se 1 (by rfl) ⟨2365109, by rfl⟩ : syracuseStep 3153479 = 4730219) B4730219
theorem B2102319 : Blo 2101435 2102319 := bstep (se 1 (by rfl) ⟨1576739, by rfl⟩ : syracuseStep 2102319 = 3153479) B3153479
theorem B3153485 : Blo 2101435 3153485 := bbase (se 3 (by rfl) ⟨591278, by rfl⟩ : syracuseStep 3153485 = 1182557) (by norm_num)
theorem B2102323 : Blo 2101435 2102323 := bstep (se 1 (by rfl) ⟨1576742, by rfl⟩ : syracuseStep 2102323 = 3153485) B3153485
theorem B4730237 : Blo 2101435 4730237 := bbase (se 3 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 4730237 = 1773839) (by norm_num)
theorem B3153491 : Blo 2101435 3153491 := bstep (se 1 (by rfl) ⟨2365118, by rfl⟩ : syracuseStep 3153491 = 4730237) B4730237
theorem B2102327 : Blo 2101435 2102327 := bstep (se 1 (by rfl) ⟨1576745, by rfl⟩ : syracuseStep 2102327 = 3153491) B3153491
theorem B3547685 : Blo 2101435 3547685 := bbase (se 4 (by rfl) ⟨332595, by rfl⟩ : syracuseStep 3547685 = 665191) (by norm_num)
theorem B2365123 : Blo 2101435 2365123 := bstep (se 1 (by rfl) ⟨1773842, by rfl⟩ : syracuseStep 2365123 = 3547685) B3547685
theorem B3153497 : Blo 2101435 3153497 := bstep (se 2 (by rfl) ⟨1182561, by rfl⟩ : syracuseStep 3153497 = 2365123) B2365123
theorem B2102331 : Blo 2101435 2102331 := bstep (se 1 (by rfl) ⟨1576748, by rfl⟩ : syracuseStep 2102331 = 3153497) B3153497
theorem B2993365 : Blo 2101435 2993365 := bbase (se 7 (by rfl) ⟨35078, by rfl⟩ : syracuseStep 2993365 = 70157) (by norm_num)
theorem B15964613 : Blo 2101435 15964613 := bstep (se 4 (by rfl) ⟨1496682, by rfl⟩ : syracuseStep 15964613 = 2993365) B2993365
theorem B10643075 : Blo 2101435 10643075 := bstep (se 1 (by rfl) ⟨7982306, by rfl⟩ : syracuseStep 10643075 = 15964613) B15964613
theorem B7095383 : Blo 2101435 7095383 := bstep (se 1 (by rfl) ⟨5321537, by rfl⟩ : syracuseStep 7095383 = 10643075) B10643075
theorem B4730255 : Blo 2101435 4730255 := bstep (se 1 (by rfl) ⟨3547691, by rfl⟩ : syracuseStep 4730255 = 7095383) B7095383
theorem B3153503 : Blo 2101435 3153503 := bstep (se 1 (by rfl) ⟨2365127, by rfl⟩ : syracuseStep 3153503 = 4730255) B4730255
theorem B2102335 : Blo 2101435 2102335 := bstep (se 1 (by rfl) ⟨1576751, by rfl⟩ : syracuseStep 2102335 = 3153503) B3153503
theorem B3153509 : Blo 2101435 3153509 := bbase (se 4 (by rfl) ⟨295641, by rfl⟩ : syracuseStep 3153509 = 591283) (by norm_num)
theorem B2102339 : Blo 2101435 2102339 := bstep (se 1 (by rfl) ⟨1576754, by rfl⟩ : syracuseStep 2102339 = 3153509) B3153509
theorem B2245033 : Blo 2101435 2245033 := bbase (se 2 (by rfl) ⟨841887, by rfl⟩ : syracuseStep 2245033 = 1683775) (by norm_num)
theorem B2993377 : Blo 2101435 2993377 := bstep (se 2 (by rfl) ⟨1122516, by rfl⟩ : syracuseStep 2993377 = 2245033) B2245033
theorem B3991169 : Blo 2101435 3991169 := bstep (se 2 (by rfl) ⟨1496688, by rfl⟩ : syracuseStep 3991169 = 2993377) B2993377
theorem B2660779 : Blo 2101435 2660779 := bstep (se 1 (by rfl) ⟨1995584, by rfl⟩ : syracuseStep 2660779 = 3991169) B3991169
theorem B3547705 : Blo 2101435 3547705 := bstep (se 2 (by rfl) ⟨1330389, by rfl⟩ : syracuseStep 3547705 = 2660779) B2660779
theorem B4730273 : Blo 2101435 4730273 := bstep (se 2 (by rfl) ⟨1773852, by rfl⟩ : syracuseStep 4730273 = 3547705) B3547705
theorem B3153515 : Blo 2101435 3153515 := bstep (se 1 (by rfl) ⟨2365136, by rfl⟩ : syracuseStep 3153515 = 4730273) B4730273
theorem B2102343 : Blo 2101435 2102343 := bstep (se 1 (by rfl) ⟨1576757, by rfl⟩ : syracuseStep 2102343 = 3153515) B3153515
theorem B2365141 : Blo 2101435 2365141 := bbase (se 7 (by rfl) ⟨27716, by rfl⟩ : syracuseStep 2365141 = 55433) (by norm_num)
theorem B3153521 : Blo 2101435 3153521 := bstep (se 2 (by rfl) ⟨1182570, by rfl⟩ : syracuseStep 3153521 = 2365141) B2365141
theorem B2102347 : Blo 2101435 2102347 := bstep (se 1 (by rfl) ⟨1576760, by rfl⟩ : syracuseStep 2102347 = 3153521) B3153521
theorem B2660789 : Blo 2101435 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B7095437 : Blo 2101435 7095437 := bstep (se 3 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 7095437 = 2660789) B2660789
theorem B4730291 : Blo 2101435 4730291 := bstep (se 1 (by rfl) ⟨3547718, by rfl⟩ : syracuseStep 4730291 = 7095437) B7095437
theorem B3153527 : Blo 2101435 3153527 := bstep (se 1 (by rfl) ⟨2365145, by rfl⟩ : syracuseStep 3153527 = 4730291) B4730291
theorem B2102351 : Blo 2101435 2102351 := bstep (se 1 (by rfl) ⟨1576763, by rfl⟩ : syracuseStep 2102351 = 3153527) B3153527
theorem B3153533 : Blo 2101435 3153533 := bbase (se 3 (by rfl) ⟨591287, by rfl⟩ : syracuseStep 3153533 = 1182575) (by norm_num)
theorem B2102355 : Blo 2101435 2102355 := bstep (se 1 (by rfl) ⟨1576766, by rfl⟩ : syracuseStep 2102355 = 3153533) B3153533
theorem B4730309 : Blo 2101435 4730309 := bbase (se 4 (by rfl) ⟨443466, by rfl⟩ : syracuseStep 4730309 = 886933) (by norm_num)
theorem B3153539 : Blo 2101435 3153539 := bstep (se 1 (by rfl) ⟨2365154, by rfl⟩ : syracuseStep 3153539 = 4730309) B4730309
theorem B2102359 : Blo 2101435 2102359 := bstep (se 1 (by rfl) ⟨1576769, by rfl⟩ : syracuseStep 2102359 = 3153539) B3153539
theorem B11365589 : Blo 2101435 11365589 := bbase (se 7 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 11365589 = 266381) (by norm_num)
theorem B7577059 : Blo 2101435 7577059 := bstep (se 1 (by rfl) ⟨5682794, by rfl⟩ : syracuseStep 7577059 = 11365589) B11365589
theorem B10102745 : Blo 2101435 10102745 := bstep (se 2 (by rfl) ⟨3788529, by rfl⟩ : syracuseStep 10102745 = 7577059) B7577059
theorem B6735163 : Blo 2101435 6735163 := bstep (se 1 (by rfl) ⟨5051372, by rfl⟩ : syracuseStep 6735163 = 10102745) B10102745
theorem B8980217 : Blo 2101435 8980217 := bstep (se 2 (by rfl) ⟨3367581, by rfl⟩ : syracuseStep 8980217 = 6735163) B6735163
theorem B5986811 : Blo 2101435 5986811 := bstep (se 1 (by rfl) ⟨4490108, by rfl⟩ : syracuseStep 5986811 = 8980217) B8980217
theorem B3991207 : Blo 2101435 3991207 := bstep (se 1 (by rfl) ⟨2993405, by rfl⟩ : syracuseStep 3991207 = 5986811) B5986811
theorem B5321609 : Blo 2101435 5321609 := bstep (se 2 (by rfl) ⟨1995603, by rfl⟩ : syracuseStep 5321609 = 3991207) B3991207
theorem B3547739 : Blo 2101435 3547739 := bstep (se 1 (by rfl) ⟨2660804, by rfl⟩ : syracuseStep 3547739 = 5321609) B5321609
theorem B2365159 : Blo 2101435 2365159 := bstep (se 1 (by rfl) ⟨1773869, by rfl⟩ : syracuseStep 2365159 = 3547739) B3547739
theorem B3153545 : Blo 2101435 3153545 := bstep (se 2 (by rfl) ⟨1182579, by rfl⟩ : syracuseStep 3153545 = 2365159) B2365159
theorem B2102363 : Blo 2101435 2102363 := bstep (se 1 (by rfl) ⟨1576772, by rfl⟩ : syracuseStep 2102363 = 3153545) B3153545
theorem B10643237 : Blo 2101435 10643237 := bbase (se 4 (by rfl) ⟨997803, by rfl⟩ : syracuseStep 10643237 = 1995607) (by norm_num)
theorem B7095491 : Blo 2101435 7095491 := bstep (se 1 (by rfl) ⟨5321618, by rfl⟩ : syracuseStep 7095491 = 10643237) B10643237
theorem B4730327 : Blo 2101435 4730327 := bstep (se 1 (by rfl) ⟨3547745, by rfl⟩ : syracuseStep 4730327 = 7095491) B7095491
theorem B3153551 : Blo 2101435 3153551 := bstep (se 1 (by rfl) ⟨2365163, by rfl⟩ : syracuseStep 3153551 = 4730327) B4730327
theorem B2102367 : Blo 2101435 2102367 := bstep (se 1 (by rfl) ⟨1576775, by rfl⟩ : syracuseStep 2102367 = 3153551) B3153551
theorem B3153557 : Blo 2101435 3153557 := bbase (se 6 (by rfl) ⟨73911, by rfl⟩ : syracuseStep 3153557 = 147823) (by norm_num)
theorem B2102371 : Blo 2101435 2102371 := bstep (se 1 (by rfl) ⟨1576778, by rfl⟩ : syracuseStep 2102371 = 3153557) B3153557
theorem B2841413 : Blo 2101435 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B7577101 : Blo 2101435 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B10102801 : Blo 2101435 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B13470401 : Blo 2101435 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B8980267 : Blo 2101435 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B11973689 : Blo 2101435 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B7982459 : Blo 2101435 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B5321639 : Blo 2101435 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B3547759 : Blo 2101435 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B4730345 : Blo 2101435 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B3153563 : Blo 2101435 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B2102375 : Blo 2101435 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B2365177 : Blo 2101435 2365177 := bbase (se 2 (by rfl) ⟨886941, by rfl⟩ : syracuseStep 2365177 = 1773883) (by norm_num)
theorem B3153569 : Blo 2101435 3153569 := bstep (se 2 (by rfl) ⟨1182588, by rfl⟩ : syracuseStep 3153569 = 2365177) B2365177
theorem B2102379 : Blo 2101435 2102379 := bstep (se 1 (by rfl) ⟨1576784, by rfl⟩ : syracuseStep 2102379 = 3153569) B3153569
theorem B3367613 : Blo 2101435 3367613 := bbase (se 3 (by rfl) ⟨631427, by rfl⟩ : syracuseStep 3367613 = 1262855) (by norm_num)
theorem B8980301 : Blo 2101435 8980301 := bstep (se 3 (by rfl) ⟨1683806, by rfl⟩ : syracuseStep 8980301 = 3367613) B3367613
theorem B5986867 : Blo 2101435 5986867 := bstep (se 1 (by rfl) ⟨4490150, by rfl⟩ : syracuseStep 5986867 = 8980301) B8980301
theorem B7982489 : Blo 2101435 7982489 := bstep (se 2 (by rfl) ⟨2993433, by rfl⟩ : syracuseStep 7982489 = 5986867) B5986867
theorem B5321659 : Blo 2101435 5321659 := bstep (se 1 (by rfl) ⟨3991244, by rfl⟩ : syracuseStep 5321659 = 7982489) B7982489
theorem B7095545 : Blo 2101435 7095545 := bstep (se 2 (by rfl) ⟨2660829, by rfl⟩ : syracuseStep 7095545 = 5321659) B5321659
theorem B4730363 : Blo 2101435 4730363 := bstep (se 1 (by rfl) ⟨3547772, by rfl⟩ : syracuseStep 4730363 = 7095545) B7095545
theorem B3153575 : Blo 2101435 3153575 := bstep (se 1 (by rfl) ⟨2365181, by rfl⟩ : syracuseStep 3153575 = 4730363) B4730363
theorem B2102383 : Blo 2101435 2102383 := bstep (se 1 (by rfl) ⟨1576787, by rfl⟩ : syracuseStep 2102383 = 3153575) B3153575
theorem B3153581 : Blo 2101435 3153581 := bbase (se 3 (by rfl) ⟨591296, by rfl⟩ : syracuseStep 3153581 = 1182593) (by norm_num)
theorem B2102387 : Blo 2101435 2102387 := bstep (se 1 (by rfl) ⟨1576790, by rfl⟩ : syracuseStep 2102387 = 3153581) B3153581
theorem B4730381 : Blo 2101435 4730381 := bbase (se 3 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 4730381 = 1773893) (by norm_num)
theorem B3153587 : Blo 2101435 3153587 := bstep (se 1 (by rfl) ⟨2365190, by rfl⟩ : syracuseStep 3153587 = 4730381) B4730381
theorem B2102391 : Blo 2101435 2102391 := bstep (se 1 (by rfl) ⟨1576793, by rfl⟩ : syracuseStep 2102391 = 3153587) B3153587
theorem B2660845 : Blo 2101435 2660845 := bbase (se 3 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 2660845 = 997817) (by norm_num)
theorem B3547793 : Blo 2101435 3547793 := bstep (se 2 (by rfl) ⟨1330422, by rfl⟩ : syracuseStep 3547793 = 2660845) B2660845
theorem B2365195 : Blo 2101435 2365195 := bstep (se 1 (by rfl) ⟨1773896, by rfl⟩ : syracuseStep 2365195 = 3547793) B3547793
theorem B3153593 : Blo 2101435 3153593 := bstep (se 2 (by rfl) ⟨1182597, by rfl⟩ : syracuseStep 3153593 = 2365195) B2365195
theorem B2102395 : Blo 2101435 2102395 := bstep (se 1 (by rfl) ⟨1576796, by rfl⟩ : syracuseStep 2102395 = 3153593) B3153593
theorem B2841445 : Blo 2101435 2841445 := bbase (se 4 (by rfl) ⟨266385, by rfl⟩ : syracuseStep 2841445 = 532771) (by norm_num)
theorem B15154373 : Blo 2101435 15154373 := bstep (se 4 (by rfl) ⟨1420722, by rfl⟩ : syracuseStep 15154373 = 2841445) B2841445
theorem B10102915 : Blo 2101435 10102915 := bstep (se 1 (by rfl) ⟨7577186, by rfl⟩ : syracuseStep 10102915 = 15154373) B15154373
theorem B13470553 : Blo 2101435 13470553 := bstep (se 2 (by rfl) ⟨5051457, by rfl⟩ : syracuseStep 13470553 = 10102915) B10102915
theorem B17960737 : Blo 2101435 17960737 := bstep (se 2 (by rfl) ⟨6735276, by rfl⟩ : syracuseStep 17960737 = 13470553) B13470553
theorem B23947649 : Blo 2101435 23947649 := bstep (se 2 (by rfl) ⟨8980368, by rfl⟩ : syracuseStep 23947649 = 17960737) B17960737
theorem B15965099 : Blo 2101435 15965099 := bstep (se 1 (by rfl) ⟨11973824, by rfl⟩ : syracuseStep 15965099 = 23947649) B23947649
theorem B10643399 : Blo 2101435 10643399 := bstep (se 1 (by rfl) ⟨7982549, by rfl⟩ : syracuseStep 10643399 = 15965099) B15965099
theorem B7095599 : Blo 2101435 7095599 := bstep (se 1 (by rfl) ⟨5321699, by rfl⟩ : syracuseStep 7095599 = 10643399) B10643399
theorem B4730399 : Blo 2101435 4730399 := bstep (se 1 (by rfl) ⟨3547799, by rfl⟩ : syracuseStep 4730399 = 7095599) B7095599
theorem B3153599 : Blo 2101435 3153599 := bstep (se 1 (by rfl) ⟨2365199, by rfl⟩ : syracuseStep 3153599 = 4730399) B4730399
theorem B2102399 : Blo 2101435 2102399 := bstep (se 1 (by rfl) ⟨1576799, by rfl⟩ : syracuseStep 2102399 = 3153599) B3153599
theorem B3153605 : Blo 2101435 3153605 := bbase (se 4 (by rfl) ⟨295650, by rfl⟩ : syracuseStep 3153605 = 591301) (by norm_num)
theorem B2102403 : Blo 2101435 2102403 := bstep (se 1 (by rfl) ⟨1576802, by rfl⟩ : syracuseStep 2102403 = 3153605) B3153605
theorem B3547813 : Blo 2101435 3547813 := bbase (se 4 (by rfl) ⟨332607, by rfl⟩ : syracuseStep 3547813 = 665215) (by norm_num)
theorem B4730417 : Blo 2101435 4730417 := bstep (se 2 (by rfl) ⟨1773906, by rfl⟩ : syracuseStep 4730417 = 3547813) B3547813
theorem B3153611 : Blo 2101435 3153611 := bstep (se 1 (by rfl) ⟨2365208, by rfl⟩ : syracuseStep 3153611 = 4730417) B4730417
theorem B2102407 : Blo 2101435 2102407 := bstep (se 1 (by rfl) ⟨1576805, by rfl⟩ : syracuseStep 2102407 = 3153611) B3153611
theorem B2365213 : Blo 2101435 2365213 := bbase (se 3 (by rfl) ⟨443477, by rfl⟩ : syracuseStep 2365213 = 886955) (by norm_num)
theorem B3153617 : Blo 2101435 3153617 := bstep (se 2 (by rfl) ⟨1182606, by rfl⟩ : syracuseStep 3153617 = 2365213) B2365213
theorem B2102411 : Blo 2101435 2102411 := bstep (se 1 (by rfl) ⟨1576808, by rfl⟩ : syracuseStep 2102411 = 3153617) B3153617
theorem B7095653 : Blo 2101435 7095653 := bbase (se 4 (by rfl) ⟨665217, by rfl⟩ : syracuseStep 7095653 = 1330435) (by norm_num)
theorem B4730435 : Blo 2101435 4730435 := bstep (se 1 (by rfl) ⟨3547826, by rfl⟩ : syracuseStep 4730435 = 7095653) B7095653
theorem B3153623 : Blo 2101435 3153623 := bstep (se 1 (by rfl) ⟨2365217, by rfl⟩ : syracuseStep 3153623 = 4730435) B4730435
theorem B2102415 : Blo 2101435 2102415 := bstep (se 1 (by rfl) ⟨1576811, by rfl⟩ : syracuseStep 2102415 = 3153623) B3153623
theorem B3153629 : Blo 2101435 3153629 := bbase (se 3 (by rfl) ⟨591305, by rfl⟩ : syracuseStep 3153629 = 1182611) (by norm_num)
theorem B2102419 : Blo 2101435 2102419 := bstep (se 1 (by rfl) ⟨1576814, by rfl⟩ : syracuseStep 2102419 = 3153629) B3153629
theorem B4730453 : Blo 2101435 4730453 := bbase (se 8 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 4730453 = 55435) (by norm_num)
theorem B3153635 : Blo 2101435 3153635 := bstep (se 1 (by rfl) ⟨2365226, by rfl⟩ : syracuseStep 3153635 = 4730453) B4730453
theorem B2102423 : Blo 2101435 2102423 := bstep (se 1 (by rfl) ⟨1576817, by rfl⟩ : syracuseStep 2102423 = 3153635) B3153635
theorem B4490245 : Blo 2101435 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B5986993 : Blo 2101435 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B7982657 : Blo 2101435 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B5321771 : Blo 2101435 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B3547847 : Blo 2101435 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B2365231 : Blo 2101435 2365231 := bstep (se 1 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 2365231 = 3547847) B3547847
theorem B3153641 : Blo 2101435 3153641 := bstep (se 2 (by rfl) ⟨1182615, by rfl⟩ : syracuseStep 3153641 = 2365231) B2365231
theorem B2102427 : Blo 2101435 2102427 := bstep (se 1 (by rfl) ⟨1576820, by rfl⟩ : syracuseStep 2102427 = 3153641) B3153641
theorem B4795013 : Blo 2101435 4795013 := bbase (se 4 (by rfl) ⟨449532, by rfl⟩ : syracuseStep 4795013 = 899065) (by norm_num)
theorem B3196675 : Blo 2101435 3196675 := bstep (se 1 (by rfl) ⟨2397506, by rfl⟩ : syracuseStep 3196675 = 4795013) B4795013
theorem B4262233 : Blo 2101435 4262233 := bstep (se 2 (by rfl) ⟨1598337, by rfl⟩ : syracuseStep 4262233 = 3196675) B3196675
theorem B5682977 : Blo 2101435 5682977 := bstep (se 2 (by rfl) ⟨2131116, by rfl⟩ : syracuseStep 5682977 = 4262233) B4262233
theorem B3788651 : Blo 2101435 3788651 := bstep (se 1 (by rfl) ⟨2841488, by rfl⟩ : syracuseStep 3788651 = 5682977) B5682977
theorem B10103069 : Blo 2101435 10103069 := bstep (se 3 (by rfl) ⟨1894325, by rfl⟩ : syracuseStep 10103069 = 3788651) B3788651
theorem B26941517 : Blo 2101435 26941517 := bstep (se 3 (by rfl) ⟨5051534, by rfl⟩ : syracuseStep 26941517 = 10103069) B10103069
theorem B17961011 : Blo 2101435 17961011 := bstep (se 1 (by rfl) ⟨13470758, by rfl⟩ : syracuseStep 17961011 = 26941517) B26941517
theorem B11974007 : Blo 2101435 11974007 := bstep (se 1 (by rfl) ⟨8980505, by rfl⟩ : syracuseStep 11974007 = 17961011) B17961011
theorem B7982671 : Blo 2101435 7982671 := bstep (se 1 (by rfl) ⟨5987003, by rfl⟩ : syracuseStep 7982671 = 11974007) B11974007
theorem B10643561 : Blo 2101435 10643561 := bstep (se 2 (by rfl) ⟨3991335, by rfl⟩ : syracuseStep 10643561 = 7982671) B7982671
theorem B7095707 : Blo 2101435 7095707 := bstep (se 1 (by rfl) ⟨5321780, by rfl⟩ : syracuseStep 7095707 = 10643561) B10643561
theorem B4730471 : Blo 2101435 4730471 := bstep (se 1 (by rfl) ⟨3547853, by rfl⟩ : syracuseStep 4730471 = 7095707) B7095707
theorem B3153647 : Blo 2101435 3153647 := bstep (se 1 (by rfl) ⟨2365235, by rfl⟩ : syracuseStep 3153647 = 4730471) B4730471
theorem B2102431 : Blo 2101435 2102431 := bstep (se 1 (by rfl) ⟨1576823, by rfl⟩ : syracuseStep 2102431 = 3153647) B3153647
theorem B3153653 : Blo 2101435 3153653 := bbase (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) (by norm_num)
theorem B2102435 : Blo 2101435 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B7577333 : Blo 2101435 7577333 := bbase (se 5 (by rfl) ⟨355187, by rfl⟩ : syracuseStep 7577333 = 710375) (by norm_num)
theorem B5051555 : Blo 2101435 5051555 := bstep (se 1 (by rfl) ⟨3788666, by rfl⟩ : syracuseStep 5051555 = 7577333) B7577333
theorem B3367703 : Blo 2101435 3367703 := bstep (se 1 (by rfl) ⟨2525777, by rfl⟩ : syracuseStep 3367703 = 5051555) B5051555
theorem B8980541 : Blo 2101435 8980541 := bstep (se 3 (by rfl) ⟨1683851, by rfl⟩ : syracuseStep 8980541 = 3367703) B3367703
theorem B5987027 : Blo 2101435 5987027 := bstep (se 1 (by rfl) ⟨4490270, by rfl⟩ : syracuseStep 5987027 = 8980541) B8980541
theorem B3991351 : Blo 2101435 3991351 := bstep (se 1 (by rfl) ⟨2993513, by rfl⟩ : syracuseStep 3991351 = 5987027) B5987027
theorem B5321801 : Blo 2101435 5321801 := bstep (se 2 (by rfl) ⟨1995675, by rfl⟩ : syracuseStep 5321801 = 3991351) B3991351
theorem B3547867 : Blo 2101435 3547867 := bstep (se 1 (by rfl) ⟨2660900, by rfl⟩ : syracuseStep 3547867 = 5321801) B5321801
theorem B4730489 : Blo 2101435 4730489 := bstep (se 2 (by rfl) ⟨1773933, by rfl⟩ : syracuseStep 4730489 = 3547867) B3547867
theorem B3153659 : Blo 2101435 3153659 := bstep (se 1 (by rfl) ⟨2365244, by rfl⟩ : syracuseStep 3153659 = 4730489) B4730489
theorem B2102439 : Blo 2101435 2102439 := bstep (se 1 (by rfl) ⟨1576829, by rfl⟩ : syracuseStep 2102439 = 3153659) B3153659
theorem B2365249 : Blo 2101435 2365249 := bbase (se 2 (by rfl) ⟨886968, by rfl⟩ : syracuseStep 2365249 = 1773937) (by norm_num)
theorem B3153665 : Blo 2101435 3153665 := bstep (se 2 (by rfl) ⟨1182624, by rfl⟩ : syracuseStep 3153665 = 2365249) B2365249
theorem B2102443 : Blo 2101435 2102443 := bstep (se 1 (by rfl) ⟨1576832, by rfl⟩ : syracuseStep 2102443 = 3153665) B3153665
theorem B5321821 : Blo 2101435 5321821 := bbase (se 3 (by rfl) ⟨997841, by rfl⟩ : syracuseStep 5321821 = 1995683) (by norm_num)
theorem B7095761 : Blo 2101435 7095761 := bstep (se 2 (by rfl) ⟨2660910, by rfl⟩ : syracuseStep 7095761 = 5321821) B5321821
theorem B4730507 : Blo 2101435 4730507 := bstep (se 1 (by rfl) ⟨3547880, by rfl⟩ : syracuseStep 4730507 = 7095761) B7095761
theorem B3153671 : Blo 2101435 3153671 := bstep (se 1 (by rfl) ⟨2365253, by rfl⟩ : syracuseStep 3153671 = 4730507) B4730507
theorem B2102447 : Blo 2101435 2102447 := bstep (se 1 (by rfl) ⟨1576835, by rfl⟩ : syracuseStep 2102447 = 3153671) B3153671
theorem B3153677 : Blo 2101435 3153677 := bbase (se 3 (by rfl) ⟨591314, by rfl⟩ : syracuseStep 3153677 = 1182629) (by norm_num)
theorem B2102451 : Blo 2101435 2102451 := bstep (se 1 (by rfl) ⟨1576838, by rfl⟩ : syracuseStep 2102451 = 3153677) B3153677
theorem B4730525 : Blo 2101435 4730525 := bbase (se 3 (by rfl) ⟨886973, by rfl⟩ : syracuseStep 4730525 = 1773947) (by norm_num)
theorem B3153683 : Blo 2101435 3153683 := bstep (se 1 (by rfl) ⟨2365262, by rfl⟩ : syracuseStep 3153683 = 4730525) B4730525
theorem B2102455 : Blo 2101435 2102455 := bstep (se 1 (by rfl) ⟨1576841, by rfl⟩ : syracuseStep 2102455 = 3153683) B3153683
theorem B3547901 : Blo 2101435 3547901 := bbase (se 3 (by rfl) ⟨665231, by rfl⟩ : syracuseStep 3547901 = 1330463) (by norm_num)
theorem B2365267 : Blo 2101435 2365267 := bstep (se 1 (by rfl) ⟨1773950, by rfl⟩ : syracuseStep 2365267 = 3547901) B3547901
theorem B3153689 : Blo 2101435 3153689 := bstep (se 2 (by rfl) ⟨1182633, by rfl⟩ : syracuseStep 3153689 = 2365267) B2365267
theorem B2102459 : Blo 2101435 2102459 := bstep (se 1 (by rfl) ⟨1576844, by rfl⟩ : syracuseStep 2102459 = 3153689) B3153689
theorem B3367741 : Blo 2101435 3367741 := bbase (se 3 (by rfl) ⟨631451, by rfl⟩ : syracuseStep 3367741 = 1262903) (by norm_num)
theorem B4490321 : Blo 2101435 4490321 := bstep (se 2 (by rfl) ⟨1683870, by rfl⟩ : syracuseStep 4490321 = 3367741) B3367741
theorem B11974189 : Blo 2101435 11974189 := bstep (se 3 (by rfl) ⟨2245160, by rfl⟩ : syracuseStep 11974189 = 4490321) B4490321
theorem B15965585 : Blo 2101435 15965585 := bstep (se 2 (by rfl) ⟨5987094, by rfl⟩ : syracuseStep 15965585 = 11974189) B11974189
theorem B10643723 : Blo 2101435 10643723 := bstep (se 1 (by rfl) ⟨7982792, by rfl⟩ : syracuseStep 10643723 = 15965585) B15965585
theorem B7095815 : Blo 2101435 7095815 := bstep (se 1 (by rfl) ⟨5321861, by rfl⟩ : syracuseStep 7095815 = 10643723) B10643723
theorem B4730543 : Blo 2101435 4730543 := bstep (se 1 (by rfl) ⟨3547907, by rfl⟩ : syracuseStep 4730543 = 7095815) B7095815
theorem B3153695 : Blo 2101435 3153695 := bstep (se 1 (by rfl) ⟨2365271, by rfl⟩ : syracuseStep 3153695 = 4730543) B4730543
theorem B2102463 : Blo 2101435 2102463 := bstep (se 1 (by rfl) ⟨1576847, by rfl⟩ : syracuseStep 2102463 = 3153695) B3153695
theorem B3153701 : Blo 2101435 3153701 := bbase (se 4 (by rfl) ⟨295659, by rfl⟩ : syracuseStep 3153701 = 591319) (by norm_num)
theorem B2102467 : Blo 2101435 2102467 := bstep (se 1 (by rfl) ⟨1576850, by rfl⟩ : syracuseStep 2102467 = 3153701) B3153701
theorem B2660941 : Blo 2101435 2660941 := bbase (se 3 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 2660941 = 997853) (by norm_num)
theorem B3547921 : Blo 2101435 3547921 := bstep (se 2 (by rfl) ⟨1330470, by rfl⟩ : syracuseStep 3547921 = 2660941) B2660941
theorem B4730561 : Blo 2101435 4730561 := bstep (se 2 (by rfl) ⟨1773960, by rfl⟩ : syracuseStep 4730561 = 3547921) B3547921
theorem B3153707 : Blo 2101435 3153707 := bstep (se 1 (by rfl) ⟨2365280, by rfl⟩ : syracuseStep 3153707 = 4730561) B4730561
theorem B2102471 : Blo 2101435 2102471 := bstep (se 1 (by rfl) ⟨1576853, by rfl⟩ : syracuseStep 2102471 = 3153707) B3153707
theorem B2365285 : Blo 2101435 2365285 := bbase (se 4 (by rfl) ⟨221745, by rfl⟩ : syracuseStep 2365285 = 443491) (by norm_num)
theorem B3153713 : Blo 2101435 3153713 := bstep (se 2 (by rfl) ⟨1182642, by rfl⟩ : syracuseStep 3153713 = 2365285) B2365285
theorem B2102475 : Blo 2101435 2102475 := bstep (se 1 (by rfl) ⟨1576856, by rfl⟩ : syracuseStep 2102475 = 3153713) B3153713
theorem B5987141 : Blo 2101435 5987141 := bbase (se 4 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 5987141 = 1122589) (by norm_num)
theorem B3991427 : Blo 2101435 3991427 := bstep (se 1 (by rfl) ⟨2993570, by rfl⟩ : syracuseStep 3991427 = 5987141) B5987141
theorem B2660951 : Blo 2101435 2660951 := bstep (se 1 (by rfl) ⟨1995713, by rfl⟩ : syracuseStep 2660951 = 3991427) B3991427
theorem B7095869 : Blo 2101435 7095869 := bstep (se 3 (by rfl) ⟨1330475, by rfl⟩ : syracuseStep 7095869 = 2660951) B2660951
theorem B4730579 : Blo 2101435 4730579 := bstep (se 1 (by rfl) ⟨3547934, by rfl⟩ : syracuseStep 4730579 = 7095869) B7095869
theorem B3153719 : Blo 2101435 3153719 := bstep (se 1 (by rfl) ⟨2365289, by rfl⟩ : syracuseStep 3153719 = 4730579) B4730579
theorem B2102479 : Blo 2101435 2102479 := bstep (se 1 (by rfl) ⟨1576859, by rfl⟩ : syracuseStep 2102479 = 3153719) B3153719
theorem B3153725 : Blo 2101435 3153725 := bbase (se 3 (by rfl) ⟨591323, by rfl⟩ : syracuseStep 3153725 = 1182647) (by norm_num)
theorem B2102483 : Blo 2101435 2102483 := bstep (se 1 (by rfl) ⟨1576862, by rfl⟩ : syracuseStep 2102483 = 3153725) B3153725
theorem B4730597 : Blo 2101435 4730597 := bbase (se 4 (by rfl) ⟨443493, by rfl⟩ : syracuseStep 4730597 = 886987) (by norm_num)
theorem B3153731 : Blo 2101435 3153731 := bstep (se 1 (by rfl) ⟨2365298, by rfl⟩ : syracuseStep 3153731 = 4730597) B4730597
theorem B2102487 : Blo 2101435 2102487 := bstep (se 1 (by rfl) ⟨1576865, by rfl⟩ : syracuseStep 2102487 = 3153731) B3153731
theorem B5321933 : Blo 2101435 5321933 := bbase (se 3 (by rfl) ⟨997862, by rfl⟩ : syracuseStep 5321933 = 1995725) (by norm_num)
theorem B3547955 : Blo 2101435 3547955 := bstep (se 1 (by rfl) ⟨2660966, by rfl⟩ : syracuseStep 3547955 = 5321933) B5321933
theorem B2365303 : Blo 2101435 2365303 := bstep (se 1 (by rfl) ⟨1773977, by rfl⟩ : syracuseStep 2365303 = 3547955) B3547955
theorem B3153737 : Blo 2101435 3153737 := bstep (se 2 (by rfl) ⟨1182651, by rfl⟩ : syracuseStep 3153737 = 2365303) B2365303
theorem B2102491 : Blo 2101435 2102491 := bstep (se 1 (by rfl) ⟨1576868, by rfl⟩ : syracuseStep 2102491 = 3153737) B3153737
theorem B2525845 : Blo 2101435 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B3367793 : Blo 2101435 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B2245195 : Blo 2101435 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B2993593 : Blo 2101435 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B3991457 : Blo 2101435 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B10643885 : Blo 2101435 10643885 := bstep (se 3 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 10643885 = 3991457) B3991457
theorem B7095923 : Blo 2101435 7095923 := bstep (se 1 (by rfl) ⟨5321942, by rfl⟩ : syracuseStep 7095923 = 10643885) B10643885
theorem B4730615 : Blo 2101435 4730615 := bstep (se 1 (by rfl) ⟨3547961, by rfl⟩ : syracuseStep 4730615 = 7095923) B7095923
theorem B3153743 : Blo 2101435 3153743 := bstep (se 1 (by rfl) ⟨2365307, by rfl⟩ : syracuseStep 3153743 = 4730615) B4730615
theorem B2102495 : Blo 2101435 2102495 := bstep (se 1 (by rfl) ⟨1576871, by rfl⟩ : syracuseStep 2102495 = 3153743) B3153743
theorem B3153749 : Blo 2101435 3153749 := bbase (se 9 (by rfl) ⟨9239, by rfl⟩ : syracuseStep 3153749 = 18479) (by norm_num)
theorem B2102499 : Blo 2101435 2102499 := bstep (se 1 (by rfl) ⟨1576874, by rfl⟩ : syracuseStep 2102499 = 3153749) B3153749
theorem B9721205 : Blo 2101435 9721205 := bbase (se 5 (by rfl) ⟨455681, by rfl⟩ : syracuseStep 9721205 = 911363) (by norm_num)
theorem B6480803 : Blo 2101435 6480803 := bstep (se 1 (by rfl) ⟨4860602, by rfl⟩ : syracuseStep 6480803 = 9721205) B9721205
theorem B4320535 : Blo 2101435 4320535 := bstep (se 1 (by rfl) ⟨3240401, by rfl⟩ : syracuseStep 4320535 = 6480803) B6480803
theorem B5760713 : Blo 2101435 5760713 := bstep (se 2 (by rfl) ⟨2160267, by rfl⟩ : syracuseStep 5760713 = 4320535) B4320535
theorem B3840475 : Blo 2101435 3840475 := bstep (se 1 (by rfl) ⟨2880356, by rfl⟩ : syracuseStep 3840475 = 5760713) B5760713
theorem B5120633 : Blo 2101435 5120633 := bstep (se 2 (by rfl) ⟨1920237, by rfl⟩ : syracuseStep 5120633 = 3840475) B3840475
theorem B3413755 : Blo 2101435 3413755 := bstep (se 1 (by rfl) ⟨2560316, by rfl⟩ : syracuseStep 3413755 = 5120633) B5120633
theorem B18206693 : Blo 2101435 18206693 := bstep (se 4 (by rfl) ⟨1706877, by rfl⟩ : syracuseStep 18206693 = 3413755) B3413755
theorem B12137795 : Blo 2101435 12137795 := bstep (se 1 (by rfl) ⟨9103346, by rfl⟩ : syracuseStep 12137795 = 18206693) B18206693
theorem B8091863 : Blo 2101435 8091863 := bstep (se 1 (by rfl) ⟨6068897, by rfl⟩ : syracuseStep 8091863 = 12137795) B12137795
theorem B5394575 : Blo 2101435 5394575 := bstep (se 1 (by rfl) ⟨4045931, by rfl⟩ : syracuseStep 5394575 = 8091863) B8091863
theorem B3596383 : Blo 2101435 3596383 := bstep (se 1 (by rfl) ⟨2697287, by rfl⟩ : syracuseStep 3596383 = 5394575) B5394575
theorem B19180709 : Blo 2101435 19180709 := bstep (se 4 (by rfl) ⟨1798191, by rfl⟩ : syracuseStep 19180709 = 3596383) B3596383
theorem B12787139 : Blo 2101435 12787139 := bstep (se 1 (by rfl) ⟨9590354, by rfl⟩ : syracuseStep 12787139 = 19180709) B19180709
theorem B8524759 : Blo 2101435 8524759 := bstep (se 1 (by rfl) ⟨6393569, by rfl⟩ : syracuseStep 8524759 = 12787139) B12787139
theorem B11366345 : Blo 2101435 11366345 := bstep (se 2 (by rfl) ⟨4262379, by rfl⟩ : syracuseStep 11366345 = 8524759) B8524759
theorem B7577563 : Blo 2101435 7577563 := bstep (se 1 (by rfl) ⟨5683172, by rfl⟩ : syracuseStep 7577563 = 11366345) B11366345
theorem B10103417 : Blo 2101435 10103417 := bstep (se 2 (by rfl) ⟨3788781, by rfl⟩ : syracuseStep 10103417 = 7577563) B7577563
theorem B6735611 : Blo 2101435 6735611 := bstep (se 1 (by rfl) ⟨5051708, by rfl⟩ : syracuseStep 6735611 = 10103417) B10103417
theorem B4490407 : Blo 2101435 4490407 := bstep (se 1 (by rfl) ⟨3367805, by rfl⟩ : syracuseStep 4490407 = 6735611) B6735611
theorem B5987209 : Blo 2101435 5987209 := bstep (se 2 (by rfl) ⟨2245203, by rfl⟩ : syracuseStep 5987209 = 4490407) B4490407
theorem B7982945 : Blo 2101435 7982945 := bstep (se 2 (by rfl) ⟨2993604, by rfl⟩ : syracuseStep 7982945 = 5987209) B5987209
theorem B5321963 : Blo 2101435 5321963 := bstep (se 1 (by rfl) ⟨3991472, by rfl⟩ : syracuseStep 5321963 = 7982945) B7982945
theorem B3547975 : Blo 2101435 3547975 := bstep (se 1 (by rfl) ⟨2660981, by rfl⟩ : syracuseStep 3547975 = 5321963) B5321963
theorem B4730633 : Blo 2101435 4730633 := bstep (se 2 (by rfl) ⟨1773987, by rfl⟩ : syracuseStep 4730633 = 3547975) B3547975
theorem B3153755 : Blo 2101435 3153755 := bstep (se 1 (by rfl) ⟨2365316, by rfl⟩ : syracuseStep 3153755 = 4730633) B4730633
theorem B2102503 : Blo 2101435 2102503 := bstep (se 1 (by rfl) ⟨1576877, by rfl⟩ : syracuseStep 2102503 = 3153755) B3153755
theorem B2365321 : Blo 2101435 2365321 := bbase (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) (by norm_num)
theorem B3153761 : Blo 2101435 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B2102507 : Blo 2101435 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B34099157 : Blo 2101435 34099157 := bbase (se 7 (by rfl) ⟨399599, by rfl⟩ : syracuseStep 34099157 = 799199) (by norm_num)
theorem B90931085 : Blo 2101435 90931085 := bstep (se 3 (by rfl) ⟨17049578, by rfl⟩ : syracuseStep 90931085 = 34099157) B34099157
theorem B60620723 : Blo 2101435 60620723 := bstep (se 1 (by rfl) ⟨45465542, by rfl⟩ : syracuseStep 60620723 = 90931085) B90931085
theorem B40413815 : Blo 2101435 40413815 := bstep (se 1 (by rfl) ⟨30310361, by rfl⟩ : syracuseStep 40413815 = 60620723) B60620723
theorem B26942543 : Blo 2101435 26942543 := bstep (se 1 (by rfl) ⟨20206907, by rfl⟩ : syracuseStep 26942543 = 40413815) B40413815
theorem B17961695 : Blo 2101435 17961695 := bstep (se 1 (by rfl) ⟨13471271, by rfl⟩ : syracuseStep 17961695 = 26942543) B26942543
theorem B11974463 : Blo 2101435 11974463 := bstep (se 1 (by rfl) ⟨8980847, by rfl⟩ : syracuseStep 11974463 = 17961695) B17961695
theorem B7982975 : Blo 2101435 7982975 := bstep (se 1 (by rfl) ⟨5987231, by rfl⟩ : syracuseStep 7982975 = 11974463) B11974463
theorem B5321983 : Blo 2101435 5321983 := bstep (se 1 (by rfl) ⟨3991487, by rfl⟩ : syracuseStep 5321983 = 7982975) B7982975
theorem B7095977 : Blo 2101435 7095977 := bstep (se 2 (by rfl) ⟨2660991, by rfl⟩ : syracuseStep 7095977 = 5321983) B5321983
theorem B4730651 : Blo 2101435 4730651 := bstep (se 1 (by rfl) ⟨3547988, by rfl⟩ : syracuseStep 4730651 = 7095977) B7095977
theorem B3153767 : Blo 2101435 3153767 := bstep (se 1 (by rfl) ⟨2365325, by rfl⟩ : syracuseStep 3153767 = 4730651) B4730651
theorem B2102511 : Blo 2101435 2102511 := bstep (se 1 (by rfl) ⟨1576883, by rfl⟩ : syracuseStep 2102511 = 3153767) B3153767
theorem B3153773 : Blo 2101435 3153773 := bbase (se 3 (by rfl) ⟨591332, by rfl⟩ : syracuseStep 3153773 = 1182665) (by norm_num)
theorem B2102515 : Blo 2101435 2102515 := bstep (se 1 (by rfl) ⟨1576886, by rfl⟩ : syracuseStep 2102515 = 3153773) B3153773
theorem B4730669 : Blo 2101435 4730669 := bbase (se 3 (by rfl) ⟨887000, by rfl⟩ : syracuseStep 4730669 = 1774001) (by norm_num)
theorem B3153779 : Blo 2101435 3153779 := bstep (se 1 (by rfl) ⟨2365334, by rfl⟩ : syracuseStep 3153779 = 4730669) B4730669
theorem B2102519 : Blo 2101435 2102519 := bstep (se 1 (by rfl) ⟨1576889, by rfl⟩ : syracuseStep 2102519 = 3153779) B3153779
theorem B8980901 : Blo 2101435 8980901 := bbase (se 4 (by rfl) ⟨841959, by rfl⟩ : syracuseStep 8980901 = 1683919) (by norm_num)
theorem B5987267 : Blo 2101435 5987267 := bstep (se 1 (by rfl) ⟨4490450, by rfl⟩ : syracuseStep 5987267 = 8980901) B8980901
theorem B3991511 : Blo 2101435 3991511 := bstep (se 1 (by rfl) ⟨2993633, by rfl⟩ : syracuseStep 3991511 = 5987267) B5987267
theorem B2661007 : Blo 2101435 2661007 := bstep (se 1 (by rfl) ⟨1995755, by rfl⟩ : syracuseStep 2661007 = 3991511) B3991511
theorem B3548009 : Blo 2101435 3548009 := bstep (se 2 (by rfl) ⟨1330503, by rfl⟩ : syracuseStep 3548009 = 2661007) B2661007
theorem B2365339 : Blo 2101435 2365339 := bstep (se 1 (by rfl) ⟨1774004, by rfl⟩ : syracuseStep 2365339 = 3548009) B3548009
theorem B3153785 : Blo 2101435 3153785 := bstep (se 2 (by rfl) ⟨1182669, by rfl⟩ : syracuseStep 3153785 = 2365339) B2365339
theorem B2102523 : Blo 2101435 2102523 := bstep (se 1 (by rfl) ⟨1576892, by rfl⟩ : syracuseStep 2102523 = 3153785) B3153785
theorem B5051765 : Blo 2101435 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B13471373 : Blo 2101435 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B35923661 : Blo 2101435 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B23949107 : Blo 2101435 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B15966071 : Blo 2101435 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B10644047 : Blo 2101435 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B7096031 : Blo 2101435 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B4730687 : Blo 2101435 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B3153791 : Blo 2101435 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B2102527 : Blo 2101435 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B3153797 : Blo 2101435 3153797 := bbase (se 4 (by rfl) ⟨295668, by rfl⟩ : syracuseStep 3153797 = 591337) (by norm_num)
theorem B2102531 : Blo 2101435 2102531 := bstep (se 1 (by rfl) ⟨1576898, by rfl⟩ : syracuseStep 2102531 = 3153797) B3153797
theorem B3548029 : Blo 2101435 3548029 := bbase (se 3 (by rfl) ⟨665255, by rfl⟩ : syracuseStep 3548029 = 1330511) (by norm_num)
theorem B4730705 : Blo 2101435 4730705 := bstep (se 2 (by rfl) ⟨1774014, by rfl⟩ : syracuseStep 4730705 = 3548029) B3548029
theorem B3153803 : Blo 2101435 3153803 := bstep (se 1 (by rfl) ⟨2365352, by rfl⟩ : syracuseStep 3153803 = 4730705) B4730705
theorem B2102535 : Blo 2101435 2102535 := bstep (se 1 (by rfl) ⟨1576901, by rfl⟩ : syracuseStep 2102535 = 3153803) B3153803
theorem B2365357 : Blo 2101435 2365357 := bbase (se 3 (by rfl) ⟨443504, by rfl⟩ : syracuseStep 2365357 = 887009) (by norm_num)
theorem B3153809 : Blo 2101435 3153809 := bstep (se 2 (by rfl) ⟨1182678, by rfl⟩ : syracuseStep 3153809 = 2365357) B2365357
theorem B2102539 : Blo 2101435 2102539 := bstep (se 1 (by rfl) ⟨1576904, by rfl⟩ : syracuseStep 2102539 = 3153809) B3153809
theorem B7096085 : Blo 2101435 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B4730723 : Blo 2101435 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B3153815 : Blo 2101435 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B2102543 : Blo 2101435 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B3153821 : Blo 2101435 3153821 := bbase (se 3 (by rfl) ⟨591341, by rfl⟩ : syracuseStep 3153821 = 1182683) (by norm_num)
theorem B2102547 : Blo 2101435 2102547 := bstep (se 1 (by rfl) ⟨1576910, by rfl⟩ : syracuseStep 2102547 = 3153821) B3153821
theorem B4730741 : Blo 2101435 4730741 := bbase (se 5 (by rfl) ⟨221753, by rfl⟩ : syracuseStep 4730741 = 443507) (by norm_num)
theorem B3153827 : Blo 2101435 3153827 := bstep (se 1 (by rfl) ⟨2365370, by rfl⟩ : syracuseStep 3153827 = 4730741) B4730741
theorem B2102551 : Blo 2101435 2102551 := bstep (se 1 (by rfl) ⟨1576913, by rfl⟩ : syracuseStep 2102551 = 3153827) B3153827
theorem B4262485 : Blo 2101435 4262485 := bbase (se 8 (by rfl) ⟨24975, by rfl⟩ : syracuseStep 4262485 = 49951) (by norm_num)
theorem B5683313 : Blo 2101435 5683313 := bstep (se 2 (by rfl) ⟨2131242, by rfl⟩ : syracuseStep 5683313 = 4262485) B4262485
theorem B3788875 : Blo 2101435 3788875 := bstep (se 1 (by rfl) ⟨2841656, by rfl⟩ : syracuseStep 3788875 = 5683313) B5683313
theorem B20207333 : Blo 2101435 20207333 := bstep (se 4 (by rfl) ⟨1894437, by rfl⟩ : syracuseStep 20207333 = 3788875) B3788875
theorem B13471555 : Blo 2101435 13471555 := bstep (se 1 (by rfl) ⟨10103666, by rfl⟩ : syracuseStep 13471555 = 20207333) B20207333
theorem B17962073 : Blo 2101435 17962073 := bstep (se 2 (by rfl) ⟨6735777, by rfl⟩ : syracuseStep 17962073 = 13471555) B13471555
theorem B11974715 : Blo 2101435 11974715 := bstep (se 1 (by rfl) ⟨8981036, by rfl⟩ : syracuseStep 11974715 = 17962073) B17962073
theorem B7983143 : Blo 2101435 7983143 := bstep (se 1 (by rfl) ⟨5987357, by rfl⟩ : syracuseStep 7983143 = 11974715) B11974715
theorem B5322095 : Blo 2101435 5322095 := bstep (se 1 (by rfl) ⟨3991571, by rfl⟩ : syracuseStep 5322095 = 7983143) B7983143
theorem B3548063 : Blo 2101435 3548063 := bstep (se 1 (by rfl) ⟨2661047, by rfl⟩ : syracuseStep 3548063 = 5322095) B5322095
theorem B2365375 : Blo 2101435 2365375 := bstep (se 1 (by rfl) ⟨1774031, by rfl⟩ : syracuseStep 2365375 = 3548063) B3548063
theorem B3153833 : Blo 2101435 3153833 := bstep (se 2 (by rfl) ⟨1182687, by rfl⟩ : syracuseStep 3153833 = 2365375) B2365375
theorem B2102555 : Blo 2101435 2102555 := bstep (se 1 (by rfl) ⟨1576916, by rfl⟩ : syracuseStep 2102555 = 3153833) B3153833
theorem B7983157 : Blo 2101435 7983157 := bbase (se 5 (by rfl) ⟨374210, by rfl⟩ : syracuseStep 7983157 = 748421) (by norm_num)
theorem B10644209 : Blo 2101435 10644209 := bstep (se 2 (by rfl) ⟨3991578, by rfl⟩ : syracuseStep 10644209 = 7983157) B7983157
theorem B7096139 : Blo 2101435 7096139 := bstep (se 1 (by rfl) ⟨5322104, by rfl⟩ : syracuseStep 7096139 = 10644209) B10644209
theorem B4730759 : Blo 2101435 4730759 := bstep (se 1 (by rfl) ⟨3548069, by rfl⟩ : syracuseStep 4730759 = 7096139) B7096139
theorem B3153839 : Blo 2101435 3153839 := bstep (se 1 (by rfl) ⟨2365379, by rfl⟩ : syracuseStep 3153839 = 4730759) B4730759
theorem B2102559 : Blo 2101435 2102559 := bstep (se 1 (by rfl) ⟨1576919, by rfl⟩ : syracuseStep 2102559 = 3153839) B3153839
theorem B3153845 : Blo 2101435 3153845 := bbase (se 5 (by rfl) ⟨147836, by rfl⟩ : syracuseStep 3153845 = 295673) (by norm_num)
theorem B2102563 : Blo 2101435 2102563 := bstep (se 1 (by rfl) ⟨1576922, by rfl⟩ : syracuseStep 2102563 = 3153845) B3153845
theorem B5322125 : Blo 2101435 5322125 := bbase (se 3 (by rfl) ⟨997898, by rfl⟩ : syracuseStep 5322125 = 1995797) (by norm_num)
theorem B3548083 : Blo 2101435 3548083 := bstep (se 1 (by rfl) ⟨2661062, by rfl⟩ : syracuseStep 3548083 = 5322125) B5322125
theorem B4730777 : Blo 2101435 4730777 := bstep (se 2 (by rfl) ⟨1774041, by rfl⟩ : syracuseStep 4730777 = 3548083) B3548083
theorem B3153851 : Blo 2101435 3153851 := bstep (se 1 (by rfl) ⟨2365388, by rfl⟩ : syracuseStep 3153851 = 4730777) B4730777
theorem B2102567 : Blo 2101435 2102567 := bstep (se 1 (by rfl) ⟨1576925, by rfl⟩ : syracuseStep 2102567 = 3153851) B3153851
theorem B2365393 : Blo 2101435 2365393 := bbase (se 2 (by rfl) ⟨887022, by rfl⟩ : syracuseStep 2365393 = 1774045) (by norm_num)
theorem B3153857 : Blo 2101435 3153857 := bstep (se 2 (by rfl) ⟨1182696, by rfl⟩ : syracuseStep 3153857 = 2365393) B2365393
theorem B2102571 : Blo 2101435 2102571 := bstep (se 1 (by rfl) ⟨1576928, by rfl⟩ : syracuseStep 2102571 = 3153857) B3153857
theorem B2525941 : Blo 2101435 2525941 := bbase (se 5 (by rfl) ⟨118403, by rfl⟩ : syracuseStep 2525941 = 236807) (by norm_num)
theorem B3367921 : Blo 2101435 3367921 := bstep (se 2 (by rfl) ⟨1262970, by rfl⟩ : syracuseStep 3367921 = 2525941) B2525941
theorem B4490561 : Blo 2101435 4490561 := bstep (se 2 (by rfl) ⟨1683960, by rfl⟩ : syracuseStep 4490561 = 3367921) B3367921
theorem B2993707 : Blo 2101435 2993707 := bstep (se 1 (by rfl) ⟨2245280, by rfl⟩ : syracuseStep 2993707 = 4490561) B4490561
theorem B3991609 : Blo 2101435 3991609 := bstep (se 2 (by rfl) ⟨1496853, by rfl⟩ : syracuseStep 3991609 = 2993707) B2993707
theorem B5322145 : Blo 2101435 5322145 := bstep (se 2 (by rfl) ⟨1995804, by rfl⟩ : syracuseStep 5322145 = 3991609) B3991609
theorem B7096193 : Blo 2101435 7096193 := bstep (se 2 (by rfl) ⟨2661072, by rfl⟩ : syracuseStep 7096193 = 5322145) B5322145
theorem B4730795 : Blo 2101435 4730795 := bstep (se 1 (by rfl) ⟨3548096, by rfl⟩ : syracuseStep 4730795 = 7096193) B7096193
theorem B3153863 : Blo 2101435 3153863 := bstep (se 1 (by rfl) ⟨2365397, by rfl⟩ : syracuseStep 3153863 = 4730795) B4730795
theorem B2102575 : Blo 2101435 2102575 := bstep (se 1 (by rfl) ⟨1576931, by rfl⟩ : syracuseStep 2102575 = 3153863) B3153863
theorem B3153869 : Blo 2101435 3153869 := bbase (se 3 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 3153869 = 1182701) (by norm_num)
theorem B2102579 : Blo 2101435 2102579 := bstep (se 1 (by rfl) ⟨1576934, by rfl⟩ : syracuseStep 2102579 = 3153869) B3153869
theorem B4730813 : Blo 2101435 4730813 := bbase (se 3 (by rfl) ⟨887027, by rfl⟩ : syracuseStep 4730813 = 1774055) (by norm_num)
theorem B3153875 : Blo 2101435 3153875 := bstep (se 1 (by rfl) ⟨2365406, by rfl⟩ : syracuseStep 3153875 = 4730813) B4730813
theorem B2102583 : Blo 2101435 2102583 := bstep (se 1 (by rfl) ⟨1576937, by rfl⟩ : syracuseStep 2102583 = 3153875) B3153875
theorem B3548117 : Blo 2101435 3548117 := bbase (se 7 (by rfl) ⟨41579, by rfl⟩ : syracuseStep 3548117 = 83159) (by norm_num)
theorem B2365411 : Blo 2101435 2365411 := bstep (se 1 (by rfl) ⟨1774058, by rfl⟩ : syracuseStep 2365411 = 3548117) B3548117
theorem B3153881 : Blo 2101435 3153881 := bstep (se 2 (by rfl) ⟨1182705, by rfl⟩ : syracuseStep 3153881 = 2365411) B2365411
theorem B2102587 : Blo 2101435 2102587 := bstep (se 1 (by rfl) ⟨1576940, by rfl⟩ : syracuseStep 2102587 = 3153881) B3153881
theorem B8981189 : Blo 2101435 8981189 := bbase (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) (by norm_num)
theorem B5987459 : Blo 2101435 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B15966557 : Blo 2101435 15966557 := bstep (se 3 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 15966557 = 5987459) B5987459
theorem B10644371 : Blo 2101435 10644371 := bstep (se 1 (by rfl) ⟨7983278, by rfl⟩ : syracuseStep 10644371 = 15966557) B15966557
theorem B7096247 : Blo 2101435 7096247 := bstep (se 1 (by rfl) ⟨5322185, by rfl⟩ : syracuseStep 7096247 = 10644371) B10644371
theorem B4730831 : Blo 2101435 4730831 := bstep (se 1 (by rfl) ⟨3548123, by rfl⟩ : syracuseStep 4730831 = 7096247) B7096247
theorem B3153887 : Blo 2101435 3153887 := bstep (se 1 (by rfl) ⟨2365415, by rfl⟩ : syracuseStep 3153887 = 4730831) B4730831
theorem B2102591 : Blo 2101435 2102591 := bstep (se 1 (by rfl) ⟨1576943, by rfl⟩ : syracuseStep 2102591 = 3153887) B3153887
theorem B3153893 : Blo 2101435 3153893 := bbase (se 4 (by rfl) ⟨295677, by rfl⟩ : syracuseStep 3153893 = 591355) (by norm_num)
theorem B2102595 : Blo 2101435 2102595 := bstep (se 1 (by rfl) ⟨1576946, by rfl⟩ : syracuseStep 2102595 = 3153893) B3153893
theorem B5394821 : Blo 2101435 5394821 := bbase (se 4 (by rfl) ⟨505764, by rfl⟩ : syracuseStep 5394821 = 1011529) (by norm_num)
theorem B14386189 : Blo 2101435 14386189 := bstep (se 3 (by rfl) ⟨2697410, by rfl⟩ : syracuseStep 14386189 = 5394821) B5394821
theorem B19181585 : Blo 2101435 19181585 := bstep (se 2 (by rfl) ⟨7193094, by rfl⟩ : syracuseStep 19181585 = 14386189) B14386189
theorem B12787723 : Blo 2101435 12787723 := bstep (se 1 (by rfl) ⟨9590792, by rfl⟩ : syracuseStep 12787723 = 19181585) B19181585
theorem B17050297 : Blo 2101435 17050297 := bstep (se 2 (by rfl) ⟨6393861, by rfl⟩ : syracuseStep 17050297 = 12787723) B12787723
theorem B22733729 : Blo 2101435 22733729 := bstep (se 2 (by rfl) ⟨8525148, by rfl⟩ : syracuseStep 22733729 = 17050297) B17050297
theorem B15155819 : Blo 2101435 15155819 := bstep (se 1 (by rfl) ⟨11366864, by rfl⟩ : syracuseStep 15155819 = 22733729) B22733729
theorem B10103879 : Blo 2101435 10103879 := bstep (se 1 (by rfl) ⟨7577909, by rfl⟩ : syracuseStep 10103879 = 15155819) B15155819
theorem B6735919 : Blo 2101435 6735919 := bstep (se 1 (by rfl) ⟨5051939, by rfl⟩ : syracuseStep 6735919 = 10103879) B10103879
theorem B8981225 : Blo 2101435 8981225 := bstep (se 2 (by rfl) ⟨3367959, by rfl⟩ : syracuseStep 8981225 = 6735919) B6735919
theorem B5987483 : Blo 2101435 5987483 := bstep (se 1 (by rfl) ⟨4490612, by rfl⟩ : syracuseStep 5987483 = 8981225) B8981225
theorem B3991655 : Blo 2101435 3991655 := bstep (se 1 (by rfl) ⟨2993741, by rfl⟩ : syracuseStep 3991655 = 5987483) B5987483
theorem B2661103 : Blo 2101435 2661103 := bstep (se 1 (by rfl) ⟨1995827, by rfl⟩ : syracuseStep 2661103 = 3991655) B3991655
theorem B3548137 : Blo 2101435 3548137 := bstep (se 2 (by rfl) ⟨1330551, by rfl⟩ : syracuseStep 3548137 = 2661103) B2661103
theorem B4730849 : Blo 2101435 4730849 := bstep (se 2 (by rfl) ⟨1774068, by rfl⟩ : syracuseStep 4730849 = 3548137) B3548137
theorem B3153899 : Blo 2101435 3153899 := bstep (se 1 (by rfl) ⟨2365424, by rfl⟩ : syracuseStep 3153899 = 4730849) B4730849
theorem B2102599 : Blo 2101435 2102599 := bstep (se 1 (by rfl) ⟨1576949, by rfl⟩ : syracuseStep 2102599 = 3153899) B3153899
theorem B2365429 : Blo 2101435 2365429 := bbase (se 5 (by rfl) ⟨110879, by rfl⟩ : syracuseStep 2365429 = 221759) (by norm_num)
theorem B3153905 : Blo 2101435 3153905 := bstep (se 2 (by rfl) ⟨1182714, by rfl⟩ : syracuseStep 3153905 = 2365429) B2365429
theorem B2102603 : Blo 2101435 2102603 := bstep (se 1 (by rfl) ⟨1576952, by rfl⟩ : syracuseStep 2102603 = 3153905) B3153905
theorem B2661113 : Blo 2101435 2661113 := bbase (se 2 (by rfl) ⟨997917, by rfl⟩ : syracuseStep 2661113 = 1995835) (by norm_num)
theorem B7096301 : Blo 2101435 7096301 := bstep (se 3 (by rfl) ⟨1330556, by rfl⟩ : syracuseStep 7096301 = 2661113) B2661113
theorem B4730867 : Blo 2101435 4730867 := bstep (se 1 (by rfl) ⟨3548150, by rfl⟩ : syracuseStep 4730867 = 7096301) B7096301
theorem B3153911 : Blo 2101435 3153911 := bstep (se 1 (by rfl) ⟨2365433, by rfl⟩ : syracuseStep 3153911 = 4730867) B4730867
theorem B2102607 : Blo 2101435 2102607 := bstep (se 1 (by rfl) ⟨1576955, by rfl⟩ : syracuseStep 2102607 = 3153911) B3153911
theorem B3153917 : Blo 2101435 3153917 := bbase (se 3 (by rfl) ⟨591359, by rfl⟩ : syracuseStep 3153917 = 1182719) (by norm_num)
theorem B2102611 : Blo 2101435 2102611 := bstep (se 1 (by rfl) ⟨1576958, by rfl⟩ : syracuseStep 2102611 = 3153917) B3153917
theorem B4730885 : Blo 2101435 4730885 := bbase (se 4 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 4730885 = 887041) (by norm_num)
theorem B3153923 : Blo 2101435 3153923 := bstep (se 1 (by rfl) ⟨2365442, by rfl⟩ : syracuseStep 3153923 = 4730885) B4730885
theorem B2102615 : Blo 2101435 2102615 := bstep (se 1 (by rfl) ⟨1576961, by rfl⟩ : syracuseStep 2102615 = 3153923) B3153923
theorem B3991693 : Blo 2101435 3991693 := bbase (se 3 (by rfl) ⟨748442, by rfl⟩ : syracuseStep 3991693 = 1496885) (by norm_num)
theorem B5322257 : Blo 2101435 5322257 := bstep (se 2 (by rfl) ⟨1995846, by rfl⟩ : syracuseStep 5322257 = 3991693) B3991693
theorem B3548171 : Blo 2101435 3548171 := bstep (se 1 (by rfl) ⟨2661128, by rfl⟩ : syracuseStep 3548171 = 5322257) B5322257
theorem B2365447 : Blo 2101435 2365447 := bstep (se 1 (by rfl) ⟨1774085, by rfl⟩ : syracuseStep 2365447 = 3548171) B3548171
theorem B3153929 : Blo 2101435 3153929 := bstep (se 2 (by rfl) ⟨1182723, by rfl⟩ : syracuseStep 3153929 = 2365447) B2365447
theorem B2102619 : Blo 2101435 2102619 := bstep (se 1 (by rfl) ⟨1576964, by rfl⟩ : syracuseStep 2102619 = 3153929) B3153929
theorem B10644533 : Blo 2101435 10644533 := bbase (se 5 (by rfl) ⟨498962, by rfl⟩ : syracuseStep 10644533 = 997925) (by norm_num)
theorem B7096355 : Blo 2101435 7096355 := bstep (se 1 (by rfl) ⟨5322266, by rfl⟩ : syracuseStep 7096355 = 10644533) B10644533
theorem B4730903 : Blo 2101435 4730903 := bstep (se 1 (by rfl) ⟨3548177, by rfl⟩ : syracuseStep 4730903 = 7096355) B7096355
theorem B3153935 : Blo 2101435 3153935 := bstep (se 1 (by rfl) ⟨2365451, by rfl⟩ : syracuseStep 3153935 = 4730903) B4730903
theorem B2102623 : Blo 2101435 2102623 := bstep (se 1 (by rfl) ⟨1576967, by rfl⟩ : syracuseStep 2102623 = 3153935) B3153935
theorem B3153941 : Blo 2101435 3153941 := bbase (se 6 (by rfl) ⟨73920, by rfl⟩ : syracuseStep 3153941 = 147841) (by norm_num)
theorem B2102627 : Blo 2101435 2102627 := bstep (se 1 (by rfl) ⟨1576970, by rfl⟩ : syracuseStep 2102627 = 3153941) B3153941
theorem B3840709 : Blo 2101435 3840709 := bbase (se 4 (by rfl) ⟨360066, by rfl⟩ : syracuseStep 3840709 = 720133) (by norm_num)
theorem B5120945 : Blo 2101435 5120945 := bstep (se 2 (by rfl) ⟨1920354, by rfl⟩ : syracuseStep 5120945 = 3840709) B3840709
theorem B3413963 : Blo 2101435 3413963 := bstep (se 1 (by rfl) ⟨2560472, by rfl⟩ : syracuseStep 3413963 = 5120945) B5120945
theorem B2275975 : Blo 2101435 2275975 := bstep (se 1 (by rfl) ⟨1706981, by rfl⟩ : syracuseStep 2275975 = 3413963) B3413963
theorem B3034633 : Blo 2101435 3034633 := bstep (se 2 (by rfl) ⟨1137987, by rfl⟩ : syracuseStep 3034633 = 2275975) B2275975
theorem B4046177 : Blo 2101435 4046177 := bstep (se 2 (by rfl) ⟨1517316, by rfl⟩ : syracuseStep 4046177 = 3034633) B3034633
theorem B2697451 : Blo 2101435 2697451 := bstep (se 1 (by rfl) ⟨2023088, by rfl⟩ : syracuseStep 2697451 = 4046177) B4046177
theorem B14386405 : Blo 2101435 14386405 := bstep (se 4 (by rfl) ⟨1348725, by rfl⟩ : syracuseStep 14386405 = 2697451) B2697451
theorem B19181873 : Blo 2101435 19181873 := bstep (se 2 (by rfl) ⟨7193202, by rfl⟩ : syracuseStep 19181873 = 14386405) B14386405
theorem B51151661 : Blo 2101435 51151661 := bstep (se 3 (by rfl) ⟨9590936, by rfl⟩ : syracuseStep 51151661 = 19181873) B19181873
theorem B34101107 : Blo 2101435 34101107 := bstep (se 1 (by rfl) ⟨25575830, by rfl⟩ : syracuseStep 34101107 = 51151661) B51151661
theorem B22734071 : Blo 2101435 22734071 := bstep (se 1 (by rfl) ⟨17050553, by rfl⟩ : syracuseStep 22734071 = 34101107) B34101107
theorem B15156047 : Blo 2101435 15156047 := bstep (se 1 (by rfl) ⟨11367035, by rfl⟩ : syracuseStep 15156047 = 22734071) B22734071
theorem B10104031 : Blo 2101435 10104031 := bstep (se 1 (by rfl) ⟨7578023, by rfl⟩ : syracuseStep 10104031 = 15156047) B15156047
theorem B13472041 : Blo 2101435 13472041 := bstep (se 2 (by rfl) ⟨5052015, by rfl⟩ : syracuseStep 13472041 = 10104031) B10104031
theorem B17962721 : Blo 2101435 17962721 := bstep (se 2 (by rfl) ⟨6736020, by rfl⟩ : syracuseStep 17962721 = 13472041) B13472041
theorem B11975147 : Blo 2101435 11975147 := bstep (se 1 (by rfl) ⟨8981360, by rfl⟩ : syracuseStep 11975147 = 17962721) B17962721
theorem B7983431 : Blo 2101435 7983431 := bstep (se 1 (by rfl) ⟨5987573, by rfl⟩ : syracuseStep 7983431 = 11975147) B11975147
theorem B5322287 : Blo 2101435 5322287 := bstep (se 1 (by rfl) ⟨3991715, by rfl⟩ : syracuseStep 5322287 = 7983431) B7983431
theorem B3548191 : Blo 2101435 3548191 := bstep (se 1 (by rfl) ⟨2661143, by rfl⟩ : syracuseStep 3548191 = 5322287) B5322287
theorem B4730921 : Blo 2101435 4730921 := bstep (se 2 (by rfl) ⟨1774095, by rfl⟩ : syracuseStep 4730921 = 3548191) B3548191
theorem B3153947 : Blo 2101435 3153947 := bstep (se 1 (by rfl) ⟨2365460, by rfl⟩ : syracuseStep 3153947 = 4730921) B4730921
theorem B2102631 : Blo 2101435 2102631 := bstep (se 1 (by rfl) ⟨1576973, by rfl⟩ : syracuseStep 2102631 = 3153947) B3153947
theorem B2365465 : Blo 2101435 2365465 := bbase (se 2 (by rfl) ⟨887049, by rfl⟩ : syracuseStep 2365465 = 1774099) (by norm_num)
theorem B3153953 : Blo 2101435 3153953 := bstep (se 2 (by rfl) ⟨1182732, by rfl⟩ : syracuseStep 3153953 = 2365465) B2365465
theorem B2102635 : Blo 2101435 2102635 := bstep (se 1 (by rfl) ⟨1576976, by rfl⟩ : syracuseStep 2102635 = 3153953) B3153953
theorem B7983461 : Blo 2101435 7983461 := bbase (se 4 (by rfl) ⟨748449, by rfl⟩ : syracuseStep 7983461 = 1496899) (by norm_num)
theorem B5322307 : Blo 2101435 5322307 := bstep (se 1 (by rfl) ⟨3991730, by rfl⟩ : syracuseStep 5322307 = 7983461) B7983461
theorem B7096409 : Blo 2101435 7096409 := bstep (se 2 (by rfl) ⟨2661153, by rfl⟩ : syracuseStep 7096409 = 5322307) B5322307
theorem B4730939 : Blo 2101435 4730939 := bstep (se 1 (by rfl) ⟨3548204, by rfl⟩ : syracuseStep 4730939 = 7096409) B7096409
theorem B3153959 : Blo 2101435 3153959 := bstep (se 1 (by rfl) ⟨2365469, by rfl⟩ : syracuseStep 3153959 = 4730939) B4730939
theorem B2102639 : Blo 2101435 2102639 := bstep (se 1 (by rfl) ⟨1576979, by rfl⟩ : syracuseStep 2102639 = 3153959) B3153959
theorem B3153965 : Blo 2101435 3153965 := bbase (se 3 (by rfl) ⟨591368, by rfl⟩ : syracuseStep 3153965 = 1182737) (by norm_num)
theorem B2102643 : Blo 2101435 2102643 := bstep (se 1 (by rfl) ⟨1576982, by rfl⟩ : syracuseStep 2102643 = 3153965) B3153965
theorem B4730957 : Blo 2101435 4730957 := bbase (se 3 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 4730957 = 1774109) (by norm_num)
theorem B3153971 : Blo 2101435 3153971 := bstep (se 1 (by rfl) ⟨2365478, by rfl⟩ : syracuseStep 3153971 = 4730957) B4730957
theorem B2102647 : Blo 2101435 2102647 := bstep (se 1 (by rfl) ⟨1576985, by rfl⟩ : syracuseStep 2102647 = 3153971) B3153971
theorem B2661169 : Blo 2101435 2661169 := bbase (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) (by norm_num)
theorem B3548225 : Blo 2101435 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B2365483 : Blo 2101435 2365483 := bstep (se 1 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 2365483 = 3548225) B3548225
theorem B3153977 : Blo 2101435 3153977 := bstep (se 2 (by rfl) ⟨1182741, by rfl⟩ : syracuseStep 3153977 = 2365483) B2365483
theorem B2102651 : Blo 2101435 2102651 := bstep (se 1 (by rfl) ⟨1576988, by rfl⟩ : syracuseStep 2102651 = 3153977) B3153977
theorem B2560501 : Blo 2101435 2560501 := bbase (se 5 (by rfl) ⟨120023, by rfl⟩ : syracuseStep 2560501 = 240047) (by norm_num)
theorem B13656005 : Blo 2101435 13656005 := bstep (se 4 (by rfl) ⟨1280250, by rfl⟩ : syracuseStep 13656005 = 2560501) B2560501
theorem B9104003 : Blo 2101435 9104003 := bstep (se 1 (by rfl) ⟨6828002, by rfl⟩ : syracuseStep 9104003 = 13656005) B13656005
theorem B6069335 : Blo 2101435 6069335 := bstep (se 1 (by rfl) ⟨4552001, by rfl⟩ : syracuseStep 6069335 = 9104003) B9104003
theorem B64739573 : Blo 2101435 64739573 := bstep (se 5 (by rfl) ⟨3034667, by rfl⟩ : syracuseStep 64739573 = 6069335) B6069335
theorem B43159715 : Blo 2101435 43159715 := bstep (se 1 (by rfl) ⟨32369786, by rfl⟩ : syracuseStep 43159715 = 64739573) B64739573
theorem B28773143 : Blo 2101435 28773143 := bstep (se 1 (by rfl) ⟨21579857, by rfl⟩ : syracuseStep 28773143 = 43159715) B43159715
theorem B19182095 : Blo 2101435 19182095 := bstep (se 1 (by rfl) ⟨14386571, by rfl⟩ : syracuseStep 19182095 = 28773143) B28773143
theorem B12788063 : Blo 2101435 12788063 := bstep (se 1 (by rfl) ⟨9591047, by rfl⟩ : syracuseStep 12788063 = 19182095) B19182095
theorem B8525375 : Blo 2101435 8525375 := bstep (se 1 (by rfl) ⟨6394031, by rfl⟩ : syracuseStep 8525375 = 12788063) B12788063
theorem B5683583 : Blo 2101435 5683583 := bstep (se 1 (by rfl) ⟨4262687, by rfl⟩ : syracuseStep 5683583 = 8525375) B8525375
theorem B3789055 : Blo 2101435 3789055 := bstep (se 1 (by rfl) ⟨2841791, by rfl⟩ : syracuseStep 3789055 = 5683583) B5683583
theorem B5052073 : Blo 2101435 5052073 := bstep (se 2 (by rfl) ⟨1894527, by rfl⟩ : syracuseStep 5052073 = 3789055) B3789055
theorem B6736097 : Blo 2101435 6736097 := bstep (se 2 (by rfl) ⟨2526036, by rfl⟩ : syracuseStep 6736097 = 5052073) B5052073
theorem B4490731 : Blo 2101435 4490731 := bstep (se 1 (by rfl) ⟨3368048, by rfl⟩ : syracuseStep 4490731 = 6736097) B6736097
theorem B23950565 : Blo 2101435 23950565 := bstep (se 4 (by rfl) ⟨2245365, by rfl⟩ : syracuseStep 23950565 = 4490731) B4490731
theorem B15967043 : Blo 2101435 15967043 := bstep (se 1 (by rfl) ⟨11975282, by rfl⟩ : syracuseStep 15967043 = 23950565) B23950565
theorem B10644695 : Blo 2101435 10644695 := bstep (se 1 (by rfl) ⟨7983521, by rfl⟩ : syracuseStep 10644695 = 15967043) B15967043
theorem B7096463 : Blo 2101435 7096463 := bstep (se 1 (by rfl) ⟨5322347, by rfl⟩ : syracuseStep 7096463 = 10644695) B10644695
theorem B4730975 : Blo 2101435 4730975 := bstep (se 1 (by rfl) ⟨3548231, by rfl⟩ : syracuseStep 4730975 = 7096463) B7096463
theorem B3153983 : Blo 2101435 3153983 := bstep (se 1 (by rfl) ⟨2365487, by rfl⟩ : syracuseStep 3153983 = 4730975) B4730975
theorem B2102655 : Blo 2101435 2102655 := bstep (se 1 (by rfl) ⟨1576991, by rfl⟩ : syracuseStep 2102655 = 3153983) B3153983
theorem B3153989 : Blo 2101435 3153989 := bbase (se 4 (by rfl) ⟨295686, by rfl⟩ : syracuseStep 3153989 = 591373) (by norm_num)
theorem B2102659 : Blo 2101435 2102659 := bstep (se 1 (by rfl) ⟨1576994, by rfl⟩ : syracuseStep 2102659 = 3153989) B3153989
theorem B3548245 : Blo 2101435 3548245 := bbase (se 8 (by rfl) ⟨20790, by rfl⟩ : syracuseStep 3548245 = 41581) (by norm_num)
theorem B4730993 : Blo 2101435 4730993 := bstep (se 2 (by rfl) ⟨1774122, by rfl⟩ : syracuseStep 4730993 = 3548245) B3548245
theorem B3153995 : Blo 2101435 3153995 := bstep (se 1 (by rfl) ⟨2365496, by rfl⟩ : syracuseStep 3153995 = 4730993) B4730993
theorem B2102663 : Blo 2101435 2102663 := bstep (se 1 (by rfl) ⟨1576997, by rfl⟩ : syracuseStep 2102663 = 3153995) B3153995
theorem B2365501 : Blo 2101435 2365501 := bbase (se 3 (by rfl) ⟨443531, by rfl⟩ : syracuseStep 2365501 = 887063) (by norm_num)
theorem B3154001 : Blo 2101435 3154001 := bstep (se 2 (by rfl) ⟨1182750, by rfl⟩ : syracuseStep 3154001 = 2365501) B2365501
theorem B2102667 : Blo 2101435 2102667 := bstep (se 1 (by rfl) ⟨1577000, by rfl⟩ : syracuseStep 2102667 = 3154001) B3154001
theorem B7096517 : Blo 2101435 7096517 := bbase (se 4 (by rfl) ⟨665298, by rfl⟩ : syracuseStep 7096517 = 1330597) (by norm_num)
theorem B4731011 : Blo 2101435 4731011 := bstep (se 1 (by rfl) ⟨3548258, by rfl⟩ : syracuseStep 4731011 = 7096517) B7096517
theorem B3154007 : Blo 2101435 3154007 := bstep (se 1 (by rfl) ⟨2365505, by rfl⟩ : syracuseStep 3154007 = 4731011) B4731011
theorem B2102671 : Blo 2101435 2102671 := bstep (se 1 (by rfl) ⟨1577003, by rfl⟩ : syracuseStep 2102671 = 3154007) B3154007
theorem B3154013 : Blo 2101435 3154013 := bbase (se 3 (by rfl) ⟨591377, by rfl⟩ : syracuseStep 3154013 = 1182755) (by norm_num)
theorem B2102675 : Blo 2101435 2102675 := bstep (se 1 (by rfl) ⟨1577006, by rfl⟩ : syracuseStep 2102675 = 3154013) B3154013
theorem B4731029 : Blo 2101435 4731029 := bbase (se 6 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 4731029 = 221767) (by norm_num)
theorem B3154019 : Blo 2101435 3154019 := bstep (se 1 (by rfl) ⟨2365514, by rfl⟩ : syracuseStep 3154019 = 4731029) B4731029
theorem B2102679 : Blo 2101435 2102679 := bstep (se 1 (by rfl) ⟨1577009, by rfl⟩ : syracuseStep 2102679 = 3154019) B3154019
theorem B2993861 : Blo 2101435 2993861 := bbase (se 4 (by rfl) ⟨280674, by rfl⟩ : syracuseStep 2993861 = 561349) (by norm_num)
theorem B7983629 : Blo 2101435 7983629 := bstep (se 3 (by rfl) ⟨1496930, by rfl⟩ : syracuseStep 7983629 = 2993861) B2993861
theorem B5322419 : Blo 2101435 5322419 := bstep (se 1 (by rfl) ⟨3991814, by rfl⟩ : syracuseStep 5322419 = 7983629) B7983629
theorem B3548279 : Blo 2101435 3548279 := bstep (se 1 (by rfl) ⟨2661209, by rfl⟩ : syracuseStep 3548279 = 5322419) B5322419
theorem B2365519 : Blo 2101435 2365519 := bstep (se 1 (by rfl) ⟨1774139, by rfl⟩ : syracuseStep 2365519 = 3548279) B3548279
theorem B3154025 : Blo 2101435 3154025 := bstep (se 2 (by rfl) ⟨1182759, by rfl⟩ : syracuseStep 3154025 = 2365519) B2365519
theorem B2102683 : Blo 2101435 2102683 := bstep (se 1 (by rfl) ⟨1577012, by rfl⟩ : syracuseStep 2102683 = 3154025) B3154025
theorem B2307089 : Blo 2101435 2307089 := bbase (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) (by norm_num)
theorem B6152237 : Blo 2101435 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B4101491 : Blo 2101435 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B2734327 : Blo 2101435 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B14583077 : Blo 2101435 14583077 := bstep (se 4 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 14583077 = 2734327) B2734327
theorem B9722051 : Blo 2101435 9722051 := bstep (se 1 (by rfl) ⟨7291538, by rfl⟩ : syracuseStep 9722051 = 14583077) B14583077
theorem B6481367 : Blo 2101435 6481367 := bstep (se 1 (by rfl) ⟨4861025, by rfl⟩ : syracuseStep 6481367 = 9722051) B9722051
theorem B4320911 : Blo 2101435 4320911 := bstep (se 1 (by rfl) ⟨3240683, by rfl⟩ : syracuseStep 4320911 = 6481367) B6481367
theorem B2880607 : Blo 2101435 2880607 := bstep (se 1 (by rfl) ⟨2160455, by rfl⟩ : syracuseStep 2880607 = 4320911) B4320911
theorem B3840809 : Blo 2101435 3840809 := bstep (se 2 (by rfl) ⟨1440303, by rfl⟩ : syracuseStep 3840809 = 2880607) B2880607
theorem B10242157 : Blo 2101435 10242157 := bstep (se 3 (by rfl) ⟨1920404, by rfl⟩ : syracuseStep 10242157 = 3840809) B3840809
theorem B13656209 : Blo 2101435 13656209 := bstep (se 2 (by rfl) ⟨5121078, by rfl⟩ : syracuseStep 13656209 = 10242157) B10242157
theorem B36416557 : Blo 2101435 36416557 := bstep (se 3 (by rfl) ⟨6828104, by rfl⟩ : syracuseStep 36416557 = 13656209) B13656209
theorem B48555409 : Blo 2101435 48555409 := bstep (se 2 (by rfl) ⟨18208278, by rfl⟩ : syracuseStep 48555409 = 36416557) B36416557
theorem B64740545 : Blo 2101435 64740545 := bstep (se 2 (by rfl) ⟨24277704, by rfl⟩ : syracuseStep 64740545 = 48555409) B48555409
theorem B43160363 : Blo 2101435 43160363 := bstep (se 1 (by rfl) ⟨32370272, by rfl⟩ : syracuseStep 43160363 = 64740545) B64740545
theorem B28773575 : Blo 2101435 28773575 := bstep (se 1 (by rfl) ⟨21580181, by rfl⟩ : syracuseStep 28773575 = 43160363) B43160363
theorem B19182383 : Blo 2101435 19182383 := bstep (se 1 (by rfl) ⟨14386787, by rfl⟩ : syracuseStep 19182383 = 28773575) B28773575
theorem B12788255 : Blo 2101435 12788255 := bstep (se 1 (by rfl) ⟨9591191, by rfl⟩ : syracuseStep 12788255 = 19182383) B19182383
theorem B8525503 : Blo 2101435 8525503 := bstep (se 1 (by rfl) ⟨6394127, by rfl⟩ : syracuseStep 8525503 = 12788255) B12788255
theorem B45469349 : Blo 2101435 45469349 := bstep (se 4 (by rfl) ⟨4262751, by rfl⟩ : syracuseStep 45469349 = 8525503) B8525503
theorem B30312899 : Blo 2101435 30312899 := bstep (se 1 (by rfl) ⟨22734674, by rfl⟩ : syracuseStep 30312899 = 45469349) B45469349
theorem B20208599 : Blo 2101435 20208599 := bstep (se 1 (by rfl) ⟨15156449, by rfl⟩ : syracuseStep 20208599 = 30312899) B30312899
theorem B13472399 : Blo 2101435 13472399 := bstep (se 1 (by rfl) ⟨10104299, by rfl⟩ : syracuseStep 13472399 = 20208599) B20208599
theorem B8981599 : Blo 2101435 8981599 := bstep (se 1 (by rfl) ⟨6736199, by rfl⟩ : syracuseStep 8981599 = 13472399) B13472399
theorem B11975465 : Blo 2101435 11975465 := bstep (se 2 (by rfl) ⟨4490799, by rfl⟩ : syracuseStep 11975465 = 8981599) B8981599
theorem B7983643 : Blo 2101435 7983643 := bstep (se 1 (by rfl) ⟨5987732, by rfl⟩ : syracuseStep 7983643 = 11975465) B11975465
theorem B10644857 : Blo 2101435 10644857 := bstep (se 2 (by rfl) ⟨3991821, by rfl⟩ : syracuseStep 10644857 = 7983643) B7983643
theorem B7096571 : Blo 2101435 7096571 := bstep (se 1 (by rfl) ⟨5322428, by rfl⟩ : syracuseStep 7096571 = 10644857) B10644857
theorem B4731047 : Blo 2101435 4731047 := bstep (se 1 (by rfl) ⟨3548285, by rfl⟩ : syracuseStep 4731047 = 7096571) B7096571
theorem B3154031 : Blo 2101435 3154031 := bstep (se 1 (by rfl) ⟨2365523, by rfl⟩ : syracuseStep 3154031 = 4731047) B4731047
theorem B2102687 : Blo 2101435 2102687 := bstep (se 1 (by rfl) ⟨1577015, by rfl⟩ : syracuseStep 2102687 = 3154031) B3154031
theorem B3154037 : Blo 2101435 3154037 := bbase (se 5 (by rfl) ⟨147845, by rfl⟩ : syracuseStep 3154037 = 295691) (by norm_num)
theorem B2102691 : Blo 2101435 2102691 := bstep (se 1 (by rfl) ⟨1577018, by rfl⟩ : syracuseStep 2102691 = 3154037) B3154037
theorem B3991837 : Blo 2101435 3991837 := bbase (se 3 (by rfl) ⟨748469, by rfl⟩ : syracuseStep 3991837 = 1496939) (by norm_num)
theorem B5322449 : Blo 2101435 5322449 := bstep (se 2 (by rfl) ⟨1995918, by rfl⟩ : syracuseStep 5322449 = 3991837) B3991837
theorem B3548299 : Blo 2101435 3548299 := bstep (se 1 (by rfl) ⟨2661224, by rfl⟩ : syracuseStep 3548299 = 5322449) B5322449
theorem B4731065 : Blo 2101435 4731065 := bstep (se 2 (by rfl) ⟨1774149, by rfl⟩ : syracuseStep 4731065 = 3548299) B3548299
theorem B3154043 : Blo 2101435 3154043 := bstep (se 1 (by rfl) ⟨2365532, by rfl⟩ : syracuseStep 3154043 = 4731065) B4731065
theorem B2102695 : Blo 2101435 2102695 := bstep (se 1 (by rfl) ⟨1577021, by rfl⟩ : syracuseStep 2102695 = 3154043) B3154043
theorem B2365537 : Blo 2101435 2365537 := bbase (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) (by norm_num)
theorem B3154049 : Blo 2101435 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B2102699 : Blo 2101435 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B5322469 : Blo 2101435 5322469 := bbase (se 4 (by rfl) ⟨498981, by rfl⟩ : syracuseStep 5322469 = 997963) (by norm_num)
theorem B7096625 : Blo 2101435 7096625 := bstep (se 2 (by rfl) ⟨2661234, by rfl⟩ : syracuseStep 7096625 = 5322469) B5322469
theorem B4731083 : Blo 2101435 4731083 := bstep (se 1 (by rfl) ⟨3548312, by rfl⟩ : syracuseStep 4731083 = 7096625) B7096625
theorem B3154055 : Blo 2101435 3154055 := bstep (se 1 (by rfl) ⟨2365541, by rfl⟩ : syracuseStep 3154055 = 4731083) B4731083
theorem B2102703 : Blo 2101435 2102703 := bstep (se 1 (by rfl) ⟨1577027, by rfl⟩ : syracuseStep 2102703 = 3154055) B3154055
theorem B3154061 : Blo 2101435 3154061 := bbase (se 3 (by rfl) ⟨591386, by rfl⟩ : syracuseStep 3154061 = 1182773) (by norm_num)
theorem B2102707 : Blo 2101435 2102707 := bstep (se 1 (by rfl) ⟨1577030, by rfl⟩ : syracuseStep 2102707 = 3154061) B3154061
theorem B4731101 : Blo 2101435 4731101 := bbase (se 3 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 4731101 = 1774163) (by norm_num)
theorem B3154067 : Blo 2101435 3154067 := bstep (se 1 (by rfl) ⟨2365550, by rfl⟩ : syracuseStep 3154067 = 4731101) B4731101
theorem B2102711 : Blo 2101435 2102711 := bstep (se 1 (by rfl) ⟨1577033, by rfl⟩ : syracuseStep 2102711 = 3154067) B3154067
theorem B3548333 : Blo 2101435 3548333 := bbase (se 3 (by rfl) ⟨665312, by rfl⟩ : syracuseStep 3548333 = 1330625) (by norm_num)
theorem B2365555 : Blo 2101435 2365555 := bstep (se 1 (by rfl) ⟨1774166, by rfl⟩ : syracuseStep 2365555 = 3548333) B3548333
theorem B3154073 : Blo 2101435 3154073 := bstep (se 2 (by rfl) ⟨1182777, by rfl⟩ : syracuseStep 3154073 = 2365555) B2365555
theorem B2102715 : Blo 2101435 2102715 := bstep (se 1 (by rfl) ⟨1577036, by rfl⟩ : syracuseStep 2102715 = 3154073) B3154073
theorem B5121157 : Blo 2101435 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B6828209 : Blo 2101435 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B4552139 : Blo 2101435 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B12139037 : Blo 2101435 12139037 := bstep (se 3 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 12139037 = 4552139) B4552139
theorem B8092691 : Blo 2101435 8092691 := bstep (se 1 (by rfl) ⟨6069518, by rfl⟩ : syracuseStep 8092691 = 12139037) B12139037
theorem B5395127 : Blo 2101435 5395127 := bstep (se 1 (by rfl) ⟨4046345, by rfl⟩ : syracuseStep 5395127 = 8092691) B8092691
theorem B14387005 : Blo 2101435 14387005 := bstep (se 3 (by rfl) ⟨2697563, by rfl⟩ : syracuseStep 14387005 = 5395127) B5395127
theorem B19182673 : Blo 2101435 19182673 := bstep (se 2 (by rfl) ⟨7193502, by rfl⟩ : syracuseStep 19182673 = 14387005) B14387005
theorem B25576897 : Blo 2101435 25576897 := bstep (se 2 (by rfl) ⟨9591336, by rfl⟩ : syracuseStep 25576897 = 19182673) B19182673
theorem B34102529 : Blo 2101435 34102529 := bstep (se 2 (by rfl) ⟨12788448, by rfl⟩ : syracuseStep 34102529 = 25576897) B25576897
theorem B22735019 : Blo 2101435 22735019 := bstep (se 1 (by rfl) ⟨17051264, by rfl⟩ : syracuseStep 22735019 = 34102529) B34102529
theorem B60626717 : Blo 2101435 60626717 := bstep (se 3 (by rfl) ⟨11367509, by rfl⟩ : syracuseStep 60626717 = 22735019) B22735019
theorem B40417811 : Blo 2101435 40417811 := bstep (se 1 (by rfl) ⟨30313358, by rfl⟩ : syracuseStep 40417811 = 60626717) B60626717
theorem B26945207 : Blo 2101435 26945207 := bstep (se 1 (by rfl) ⟨20208905, by rfl⟩ : syracuseStep 26945207 = 40417811) B40417811
theorem B17963471 : Blo 2101435 17963471 := bstep (se 1 (by rfl) ⟨13472603, by rfl⟩ : syracuseStep 17963471 = 26945207) B26945207
theorem B11975647 : Blo 2101435 11975647 := bstep (se 1 (by rfl) ⟨8981735, by rfl⟩ : syracuseStep 11975647 = 17963471) B17963471
theorem B15967529 : Blo 2101435 15967529 := bstep (se 2 (by rfl) ⟨5987823, by rfl⟩ : syracuseStep 15967529 = 11975647) B11975647
theorem B10645019 : Blo 2101435 10645019 := bstep (se 1 (by rfl) ⟨7983764, by rfl⟩ : syracuseStep 10645019 = 15967529) B15967529
theorem B7096679 : Blo 2101435 7096679 := bstep (se 1 (by rfl) ⟨5322509, by rfl⟩ : syracuseStep 7096679 = 10645019) B10645019
theorem B4731119 : Blo 2101435 4731119 := bstep (se 1 (by rfl) ⟨3548339, by rfl⟩ : syracuseStep 4731119 = 7096679) B7096679
theorem B3154079 : Blo 2101435 3154079 := bstep (se 1 (by rfl) ⟨2365559, by rfl⟩ : syracuseStep 3154079 = 4731119) B4731119
theorem B2102719 : Blo 2101435 2102719 := bstep (se 1 (by rfl) ⟨1577039, by rfl⟩ : syracuseStep 2102719 = 3154079) B3154079
theorem B3154085 : Blo 2101435 3154085 := bbase (se 4 (by rfl) ⟨295695, by rfl⟩ : syracuseStep 3154085 = 591391) (by norm_num)
theorem B2102723 : Blo 2101435 2102723 := bstep (se 1 (by rfl) ⟨1577042, by rfl⟩ : syracuseStep 2102723 = 3154085) B3154085
theorem B2661265 : Blo 2101435 2661265 := bbase (se 2 (by rfl) ⟨997974, by rfl⟩ : syracuseStep 2661265 = 1995949) (by norm_num)
theorem B3548353 : Blo 2101435 3548353 := bstep (se 2 (by rfl) ⟨1330632, by rfl⟩ : syracuseStep 3548353 = 2661265) B2661265
theorem B4731137 : Blo 2101435 4731137 := bstep (se 2 (by rfl) ⟨1774176, by rfl⟩ : syracuseStep 4731137 = 3548353) B3548353
theorem B3154091 : Blo 2101435 3154091 := bstep (se 1 (by rfl) ⟨2365568, by rfl⟩ : syracuseStep 3154091 = 4731137) B4731137
theorem B2102727 : Blo 2101435 2102727 := bstep (se 1 (by rfl) ⟨1577045, by rfl⟩ : syracuseStep 2102727 = 3154091) B3154091
theorem B2365573 : Blo 2101435 2365573 := bbase (se 4 (by rfl) ⟨221772, by rfl⟩ : syracuseStep 2365573 = 443545) (by norm_num)
theorem B3154097 : Blo 2101435 3154097 := bstep (se 2 (by rfl) ⟨1182786, by rfl⟩ : syracuseStep 3154097 = 2365573) B2365573
theorem B2102731 : Blo 2101435 2102731 := bstep (se 1 (by rfl) ⟨1577048, by rfl⟩ : syracuseStep 2102731 = 3154097) B3154097
theorem B10104533 : Blo 2101435 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B6736355 : Blo 2101435 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B4490903 : Blo 2101435 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B2993935 : Blo 2101435 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B3991913 : Blo 2101435 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B2661275 : Blo 2101435 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B7096733 : Blo 2101435 7096733 := bstep (se 3 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 7096733 = 2661275) B2661275
theorem B4731155 : Blo 2101435 4731155 := bstep (se 1 (by rfl) ⟨3548366, by rfl⟩ : syracuseStep 4731155 = 7096733) B7096733
theorem B3154103 : Blo 2101435 3154103 := bstep (se 1 (by rfl) ⟨2365577, by rfl⟩ : syracuseStep 3154103 = 4731155) B4731155
theorem B2102735 : Blo 2101435 2102735 := bstep (se 1 (by rfl) ⟨1577051, by rfl⟩ : syracuseStep 2102735 = 3154103) B3154103
theorem B3154109 : Blo 2101435 3154109 := bbase (se 3 (by rfl) ⟨591395, by rfl⟩ : syracuseStep 3154109 = 1182791) (by norm_num)
theorem B2102739 : Blo 2101435 2102739 := bstep (se 1 (by rfl) ⟨1577054, by rfl⟩ : syracuseStep 2102739 = 3154109) B3154109
theorem B4731173 : Blo 2101435 4731173 := bbase (se 4 (by rfl) ⟨443547, by rfl⟩ : syracuseStep 4731173 = 887095) (by norm_num)
theorem B3154115 : Blo 2101435 3154115 := bstep (se 1 (by rfl) ⟨2365586, by rfl⟩ : syracuseStep 3154115 = 4731173) B4731173
theorem B2102743 : Blo 2101435 2102743 := bstep (se 1 (by rfl) ⟨1577057, by rfl⟩ : syracuseStep 2102743 = 3154115) B3154115
theorem B5322581 : Blo 2101435 5322581 := bbase (se 9 (by rfl) ⟨15593, by rfl⟩ : syracuseStep 5322581 = 31187) (by norm_num)
theorem B3548387 : Blo 2101435 3548387 := bstep (se 1 (by rfl) ⟨2661290, by rfl⟩ : syracuseStep 3548387 = 5322581) B5322581
theorem B2365591 : Blo 2101435 2365591 := bstep (se 1 (by rfl) ⟨1774193, by rfl⟩ : syracuseStep 2365591 = 3548387) B3548387
theorem B3154121 : Blo 2101435 3154121 := bstep (se 2 (by rfl) ⟨1182795, by rfl⟩ : syracuseStep 3154121 = 2365591) B2365591
theorem B2102747 : Blo 2101435 2102747 := bstep (se 1 (by rfl) ⟨1577060, by rfl⟩ : syracuseStep 2102747 = 3154121) B3154121
theorem B6736405 : Blo 2101435 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B8981873 : Blo 2101435 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B5987915 : Blo 2101435 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B3991943 : Blo 2101435 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B10645181 : Blo 2101435 10645181 := bstep (se 3 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 10645181 = 3991943) B3991943
theorem B7096787 : Blo 2101435 7096787 := bstep (se 1 (by rfl) ⟨5322590, by rfl⟩ : syracuseStep 7096787 = 10645181) B10645181
theorem B4731191 : Blo 2101435 4731191 := bstep (se 1 (by rfl) ⟨3548393, by rfl⟩ : syracuseStep 4731191 = 7096787) B7096787
theorem B3154127 : Blo 2101435 3154127 := bstep (se 1 (by rfl) ⟨2365595, by rfl⟩ : syracuseStep 3154127 = 4731191) B4731191
theorem B2102751 : Blo 2101435 2102751 := bstep (se 1 (by rfl) ⟨1577063, by rfl⟩ : syracuseStep 2102751 = 3154127) B3154127
theorem B3154133 : Blo 2101435 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B2102755 : Blo 2101435 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B2245477 : Blo 2101435 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B2993969 : Blo 2101435 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B7983917 : Blo 2101435 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B5322611 : Blo 2101435 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B3548407 : Blo 2101435 3548407 := bstep (se 1 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 3548407 = 5322611) B5322611
theorem B4731209 : Blo 2101435 4731209 := bstep (se 2 (by rfl) ⟨1774203, by rfl⟩ : syracuseStep 4731209 = 3548407) B3548407
theorem B3154139 : Blo 2101435 3154139 := bstep (se 1 (by rfl) ⟨2365604, by rfl⟩ : syracuseStep 3154139 = 4731209) B4731209
theorem B2102759 : Blo 2101435 2102759 := bstep (se 1 (by rfl) ⟨1577069, by rfl⟩ : syracuseStep 2102759 = 3154139) B3154139
theorem B2365609 : Blo 2101435 2365609 := bbase (se 2 (by rfl) ⟨887103, by rfl⟩ : syracuseStep 2365609 = 1774207) (by norm_num)
theorem B3154145 : Blo 2101435 3154145 := bstep (se 2 (by rfl) ⟨1182804, by rfl⟩ : syracuseStep 3154145 = 2365609) B2365609
theorem B2102763 : Blo 2101435 2102763 := bstep (se 1 (by rfl) ⟨1577072, by rfl⟩ : syracuseStep 2102763 = 3154145) B3154145
theorem B8981941 : Blo 2101435 8981941 := bbase (se 5 (by rfl) ⟨421028, by rfl⟩ : syracuseStep 8981941 = 842057) (by norm_num)
theorem B11975921 : Blo 2101435 11975921 := bstep (se 2 (by rfl) ⟨4490970, by rfl⟩ : syracuseStep 11975921 = 8981941) B8981941
theorem B7983947 : Blo 2101435 7983947 := bstep (se 1 (by rfl) ⟨5987960, by rfl⟩ : syracuseStep 7983947 = 11975921) B11975921
theorem B5322631 : Blo 2101435 5322631 := bstep (se 1 (by rfl) ⟨3991973, by rfl⟩ : syracuseStep 5322631 = 7983947) B7983947
theorem B7096841 : Blo 2101435 7096841 := bstep (se 2 (by rfl) ⟨2661315, by rfl⟩ : syracuseStep 7096841 = 5322631) B5322631
theorem B4731227 : Blo 2101435 4731227 := bstep (se 1 (by rfl) ⟨3548420, by rfl⟩ : syracuseStep 4731227 = 7096841) B7096841
theorem B3154151 : Blo 2101435 3154151 := bstep (se 1 (by rfl) ⟨2365613, by rfl⟩ : syracuseStep 3154151 = 4731227) B4731227
theorem B2102767 : Blo 2101435 2102767 := bstep (se 1 (by rfl) ⟨1577075, by rfl⟩ : syracuseStep 2102767 = 3154151) B3154151
theorem B3154157 : Blo 2101435 3154157 := bbase (se 3 (by rfl) ⟨591404, by rfl⟩ : syracuseStep 3154157 = 1182809) (by norm_num)
theorem B2102771 : Blo 2101435 2102771 := bstep (se 1 (by rfl) ⟨1577078, by rfl⟩ : syracuseStep 2102771 = 3154157) B3154157
theorem B4731245 : Blo 2101435 4731245 := bbase (se 3 (by rfl) ⟨887108, by rfl⟩ : syracuseStep 4731245 = 1774217) (by norm_num)
theorem B3154163 : Blo 2101435 3154163 := bstep (se 1 (by rfl) ⟨2365622, by rfl⟩ : syracuseStep 3154163 = 4731245) B4731245
theorem B2102775 : Blo 2101435 2102775 := bstep (se 1 (by rfl) ⟨1577081, by rfl⟩ : syracuseStep 2102775 = 3154163) B3154163
theorem B3991997 : Blo 2101435 3991997 := bbase (se 3 (by rfl) ⟨748499, by rfl⟩ : syracuseStep 3991997 = 1496999) (by norm_num)
theorem B2661331 : Blo 2101435 2661331 := bstep (se 1 (by rfl) ⟨1995998, by rfl⟩ : syracuseStep 2661331 = 3991997) B3991997
theorem B3548441 : Blo 2101435 3548441 := bstep (se 2 (by rfl) ⟨1330665, by rfl⟩ : syracuseStep 3548441 = 2661331) B2661331
theorem B2365627 : Blo 2101435 2365627 := bstep (se 1 (by rfl) ⟨1774220, by rfl⟩ : syracuseStep 2365627 = 3548441) B3548441
theorem B3154169 : Blo 2101435 3154169 := bstep (se 2 (by rfl) ⟨1182813, by rfl⟩ : syracuseStep 3154169 = 2365627) B2365627
theorem B2102779 : Blo 2101435 2102779 := bstep (se 1 (by rfl) ⟨1577084, by rfl⟩ : syracuseStep 2102779 = 3154169) B3154169
theorem B53892053 : Blo 2101435 53892053 := bbase (se 7 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 53892053 = 1263095) (by norm_num)
theorem B35928035 : Blo 2101435 35928035 := bstep (se 1 (by rfl) ⟨26946026, by rfl⟩ : syracuseStep 35928035 = 53892053) B53892053
theorem B23952023 : Blo 2101435 23952023 := bstep (se 1 (by rfl) ⟨17964017, by rfl⟩ : syracuseStep 23952023 = 35928035) B35928035
theorem B15968015 : Blo 2101435 15968015 := bstep (se 1 (by rfl) ⟨11976011, by rfl⟩ : syracuseStep 15968015 = 23952023) B23952023
theorem B10645343 : Blo 2101435 10645343 := bstep (se 1 (by rfl) ⟨7984007, by rfl⟩ : syracuseStep 10645343 = 15968015) B15968015
theorem B7096895 : Blo 2101435 7096895 := bstep (se 1 (by rfl) ⟨5322671, by rfl⟩ : syracuseStep 7096895 = 10645343) B10645343
theorem B4731263 : Blo 2101435 4731263 := bstep (se 1 (by rfl) ⟨3548447, by rfl⟩ : syracuseStep 4731263 = 7096895) B7096895
theorem B3154175 : Blo 2101435 3154175 := bstep (se 1 (by rfl) ⟨2365631, by rfl⟩ : syracuseStep 3154175 = 4731263) B4731263
theorem B2102783 : Blo 2101435 2102783 := bstep (se 1 (by rfl) ⟨1577087, by rfl⟩ : syracuseStep 2102783 = 3154175) B3154175
theorem B3154181 : Blo 2101435 3154181 := bbase (se 4 (by rfl) ⟨295704, by rfl⟩ : syracuseStep 3154181 = 591409) (by norm_num)
theorem B2102787 : Blo 2101435 2102787 := bstep (se 1 (by rfl) ⟨1577090, by rfl⟩ : syracuseStep 2102787 = 3154181) B3154181
theorem B3548461 : Blo 2101435 3548461 := bbase (se 3 (by rfl) ⟨665336, by rfl⟩ : syracuseStep 3548461 = 1330673) (by norm_num)
theorem B4731281 : Blo 2101435 4731281 := bstep (se 2 (by rfl) ⟨1774230, by rfl⟩ : syracuseStep 4731281 = 3548461) B3548461
theorem B3154187 : Blo 2101435 3154187 := bstep (se 1 (by rfl) ⟨2365640, by rfl⟩ : syracuseStep 3154187 = 4731281) B4731281
theorem B2102791 : Blo 2101435 2102791 := bstep (se 1 (by rfl) ⟨1577093, by rfl⟩ : syracuseStep 2102791 = 3154187) B3154187
theorem B2365645 : Blo 2101435 2365645 := bbase (se 3 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 2365645 = 887117) (by norm_num)
theorem B3154193 : Blo 2101435 3154193 := bstep (se 2 (by rfl) ⟨1182822, by rfl⟩ : syracuseStep 3154193 = 2365645) B2365645
theorem B2102795 : Blo 2101435 2102795 := bstep (se 1 (by rfl) ⟨1577096, by rfl⟩ : syracuseStep 2102795 = 3154193) B3154193
theorem B7096949 : Blo 2101435 7096949 := bbase (se 5 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 7096949 = 665339) (by norm_num)
theorem B4731299 : Blo 2101435 4731299 := bstep (se 1 (by rfl) ⟨3548474, by rfl⟩ : syracuseStep 4731299 = 7096949) B7096949
theorem B3154199 : Blo 2101435 3154199 := bstep (se 1 (by rfl) ⟨2365649, by rfl⟩ : syracuseStep 3154199 = 4731299) B4731299
theorem B2102799 : Blo 2101435 2102799 := bstep (se 1 (by rfl) ⟨1577099, by rfl⟩ : syracuseStep 2102799 = 3154199) B3154199
theorem B3154205 : Blo 2101435 3154205 := bbase (se 3 (by rfl) ⟨591413, by rfl⟩ : syracuseStep 3154205 = 1182827) (by norm_num)
theorem B2102803 : Blo 2101435 2102803 := bstep (se 1 (by rfl) ⟨1577102, by rfl⟩ : syracuseStep 2102803 = 3154205) B3154205
theorem B4731317 : Blo 2101435 4731317 := bbase (se 5 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 4731317 = 443561) (by norm_num)
theorem B3154211 : Blo 2101435 3154211 := bstep (se 1 (by rfl) ⟨2365658, by rfl⟩ : syracuseStep 3154211 = 4731317) B4731317
theorem B2102807 : Blo 2101435 2102807 := bstep (se 1 (by rfl) ⟨1577105, by rfl⟩ : syracuseStep 2102807 = 3154211) B3154211
theorem B4263005 : Blo 2101435 4263005 := bbase (se 3 (by rfl) ⟨799313, by rfl⟩ : syracuseStep 4263005 = 1598627) (by norm_num)
theorem B2842003 : Blo 2101435 2842003 := bstep (se 1 (by rfl) ⟨2131502, by rfl⟩ : syracuseStep 2842003 = 4263005) B4263005
theorem B3789337 : Blo 2101435 3789337 := bstep (se 2 (by rfl) ⟨1421001, by rfl⟩ : syracuseStep 3789337 = 2842003) B2842003
theorem B5052449 : Blo 2101435 5052449 := bstep (se 2 (by rfl) ⟨1894668, by rfl⟩ : syracuseStep 5052449 = 3789337) B3789337
theorem B3368299 : Blo 2101435 3368299 := bstep (se 1 (by rfl) ⟨2526224, by rfl⟩ : syracuseStep 3368299 = 5052449) B5052449
theorem B4491065 : Blo 2101435 4491065 := bstep (se 2 (by rfl) ⟨1684149, by rfl⟩ : syracuseStep 4491065 = 3368299) B3368299
theorem B11976173 : Blo 2101435 11976173 := bstep (se 3 (by rfl) ⟨2245532, by rfl⟩ : syracuseStep 11976173 = 4491065) B4491065
theorem B7984115 : Blo 2101435 7984115 := bstep (se 1 (by rfl) ⟨5988086, by rfl⟩ : syracuseStep 7984115 = 11976173) B11976173
theorem B5322743 : Blo 2101435 5322743 := bstep (se 1 (by rfl) ⟨3992057, by rfl⟩ : syracuseStep 5322743 = 7984115) B7984115
theorem B3548495 : Blo 2101435 3548495 := bstep (se 1 (by rfl) ⟨2661371, by rfl⟩ : syracuseStep 3548495 = 5322743) B5322743
theorem B2365663 : Blo 2101435 2365663 := bstep (se 1 (by rfl) ⟨1774247, by rfl⟩ : syracuseStep 2365663 = 3548495) B3548495
theorem B3154217 : Blo 2101435 3154217 := bstep (se 2 (by rfl) ⟨1182831, by rfl⟩ : syracuseStep 3154217 = 2365663) B2365663
theorem B2102811 : Blo 2101435 2102811 := bstep (se 1 (by rfl) ⟨1577108, by rfl⟩ : syracuseStep 2102811 = 3154217) B3154217
theorem B2526229 : Blo 2101435 2526229 := bbase (se 6 (by rfl) ⟨59208, by rfl⟩ : syracuseStep 2526229 = 118417) (by norm_num)
theorem B3368305 : Blo 2101435 3368305 := bstep (se 2 (by rfl) ⟨1263114, by rfl⟩ : syracuseStep 3368305 = 2526229) B2526229
theorem B4491073 : Blo 2101435 4491073 := bstep (se 2 (by rfl) ⟨1684152, by rfl⟩ : syracuseStep 4491073 = 3368305) B3368305
theorem B5988097 : Blo 2101435 5988097 := bstep (se 2 (by rfl) ⟨2245536, by rfl⟩ : syracuseStep 5988097 = 4491073) B4491073
theorem B7984129 : Blo 2101435 7984129 := bstep (se 2 (by rfl) ⟨2994048, by rfl⟩ : syracuseStep 7984129 = 5988097) B5988097
theorem B10645505 : Blo 2101435 10645505 := bstep (se 2 (by rfl) ⟨3992064, by rfl⟩ : syracuseStep 10645505 = 7984129) B7984129
theorem B7097003 : Blo 2101435 7097003 := bstep (se 1 (by rfl) ⟨5322752, by rfl⟩ : syracuseStep 7097003 = 10645505) B10645505
theorem B4731335 : Blo 2101435 4731335 := bstep (se 1 (by rfl) ⟨3548501, by rfl⟩ : syracuseStep 4731335 = 7097003) B7097003
theorem B3154223 : Blo 2101435 3154223 := bstep (se 1 (by rfl) ⟨2365667, by rfl⟩ : syracuseStep 3154223 = 4731335) B4731335
theorem B2102815 : Blo 2101435 2102815 := bstep (se 1 (by rfl) ⟨1577111, by rfl⟩ : syracuseStep 2102815 = 3154223) B3154223
theorem B3154229 : Blo 2101435 3154229 := bbase (se 5 (by rfl) ⟨147854, by rfl⟩ : syracuseStep 3154229 = 295709) (by norm_num)
theorem B2102819 : Blo 2101435 2102819 := bstep (se 1 (by rfl) ⟨1577114, by rfl⟩ : syracuseStep 2102819 = 3154229) B3154229
theorem B5322773 : Blo 2101435 5322773 := bbase (se 6 (by rfl) ⟨124752, by rfl⟩ : syracuseStep 5322773 = 249505) (by norm_num)
theorem B3548515 : Blo 2101435 3548515 := bstep (se 1 (by rfl) ⟨2661386, by rfl⟩ : syracuseStep 3548515 = 5322773) B5322773
theorem B4731353 : Blo 2101435 4731353 := bstep (se 2 (by rfl) ⟨1774257, by rfl⟩ : syracuseStep 4731353 = 3548515) B3548515
theorem B3154235 : Blo 2101435 3154235 := bstep (se 1 (by rfl) ⟨2365676, by rfl⟩ : syracuseStep 3154235 = 4731353) B4731353
theorem B2102823 : Blo 2101435 2102823 := bstep (se 1 (by rfl) ⟨1577117, by rfl⟩ : syracuseStep 2102823 = 3154235) B3154235
theorem B2365681 : Blo 2101435 2365681 := bbase (se 2 (by rfl) ⟨887130, by rfl⟩ : syracuseStep 2365681 = 1774261) (by norm_num)
theorem B3154241 : Blo 2101435 3154241 := bstep (se 2 (by rfl) ⟨1182840, by rfl⟩ : syracuseStep 3154241 = 2365681) B2365681
theorem B2102827 : Blo 2101435 2102827 := bstep (se 1 (by rfl) ⟨1577120, by rfl⟩ : syracuseStep 2102827 = 3154241) B3154241
theorem B11368117 : Blo 2101435 11368117 := bbase (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) (by norm_num)
theorem B15157489 : Blo 2101435 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B20209985 : Blo 2101435 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B13473323 : Blo 2101435 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B8982215 : Blo 2101435 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B5988143 : Blo 2101435 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B3992095 : Blo 2101435 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B5322793 : Blo 2101435 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B7097057 : Blo 2101435 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B4731371 : Blo 2101435 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B3154247 : Blo 2101435 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B2102831 : Blo 2101435 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B3154253 : Blo 2101435 3154253 := bbase (se 3 (by rfl) ⟨591422, by rfl⟩ : syracuseStep 3154253 = 1182845) (by norm_num)
theorem B2102835 : Blo 2101435 2102835 := bstep (se 1 (by rfl) ⟨1577126, by rfl⟩ : syracuseStep 2102835 = 3154253) B3154253
theorem B4731389 : Blo 2101435 4731389 := bbase (se 3 (by rfl) ⟨887135, by rfl⟩ : syracuseStep 4731389 = 1774271) (by norm_num)
theorem B3154259 : Blo 2101435 3154259 := bstep (se 1 (by rfl) ⟨2365694, by rfl⟩ : syracuseStep 3154259 = 4731389) B4731389
theorem B2102839 : Blo 2101435 2102839 := bstep (se 1 (by rfl) ⟨1577129, by rfl⟩ : syracuseStep 2102839 = 3154259) B3154259
theorem B3548549 : Blo 2101435 3548549 := bbase (se 4 (by rfl) ⟨332676, by rfl⟩ : syracuseStep 3548549 = 665353) (by norm_num)
theorem B2365699 : Blo 2101435 2365699 := bstep (se 1 (by rfl) ⟨1774274, by rfl⟩ : syracuseStep 2365699 = 3548549) B3548549
theorem B3154265 : Blo 2101435 3154265 := bstep (se 2 (by rfl) ⟨1182849, by rfl⟩ : syracuseStep 3154265 = 2365699) B2365699
theorem B2102843 : Blo 2101435 2102843 := bstep (se 1 (by rfl) ⟨1577132, by rfl⟩ : syracuseStep 2102843 = 3154265) B3154265
theorem B15968501 : Blo 2101435 15968501 := bbase (se 5 (by rfl) ⟨748523, by rfl⟩ : syracuseStep 15968501 = 1497047) (by norm_num)
theorem B10645667 : Blo 2101435 10645667 := bstep (se 1 (by rfl) ⟨7984250, by rfl⟩ : syracuseStep 10645667 = 15968501) B15968501
theorem B7097111 : Blo 2101435 7097111 := bstep (se 1 (by rfl) ⟨5322833, by rfl⟩ : syracuseStep 7097111 = 10645667) B10645667
theorem B4731407 : Blo 2101435 4731407 := bstep (se 1 (by rfl) ⟨3548555, by rfl⟩ : syracuseStep 4731407 = 7097111) B7097111
theorem B3154271 : Blo 2101435 3154271 := bstep (se 1 (by rfl) ⟨2365703, by rfl⟩ : syracuseStep 3154271 = 4731407) B4731407
theorem B2102847 : Blo 2101435 2102847 := bstep (se 1 (by rfl) ⟨1577135, by rfl⟩ : syracuseStep 2102847 = 3154271) B3154271
theorem B3154277 : Blo 2101435 3154277 := bbase (se 4 (by rfl) ⟨295713, by rfl⟩ : syracuseStep 3154277 = 591427) (by norm_num)
theorem B2102851 : Blo 2101435 2102851 := bstep (se 1 (by rfl) ⟨1577138, by rfl⟩ : syracuseStep 2102851 = 3154277) B3154277
theorem B3992141 : Blo 2101435 3992141 := bbase (se 3 (by rfl) ⟨748526, by rfl⟩ : syracuseStep 3992141 = 1497053) (by norm_num)
theorem B2661427 : Blo 2101435 2661427 := bstep (se 1 (by rfl) ⟨1996070, by rfl⟩ : syracuseStep 2661427 = 3992141) B3992141
theorem B3548569 : Blo 2101435 3548569 := bstep (se 2 (by rfl) ⟨1330713, by rfl⟩ : syracuseStep 3548569 = 2661427) B2661427
theorem B4731425 : Blo 2101435 4731425 := bstep (se 2 (by rfl) ⟨1774284, by rfl⟩ : syracuseStep 4731425 = 3548569) B3548569
theorem B3154283 : Blo 2101435 3154283 := bstep (se 1 (by rfl) ⟨2365712, by rfl⟩ : syracuseStep 3154283 = 4731425) B4731425
theorem B2102855 : Blo 2101435 2102855 := bstep (se 1 (by rfl) ⟨1577141, by rfl⟩ : syracuseStep 2102855 = 3154283) B3154283
theorem B2365717 : Blo 2101435 2365717 := bbase (se 6 (by rfl) ⟨55446, by rfl⟩ : syracuseStep 2365717 = 110893) (by norm_num)
theorem B3154289 : Blo 2101435 3154289 := bstep (se 2 (by rfl) ⟨1182858, by rfl⟩ : syracuseStep 3154289 = 2365717) B2365717
theorem B2102859 : Blo 2101435 2102859 := bstep (se 1 (by rfl) ⟨1577144, by rfl⟩ : syracuseStep 2102859 = 3154289) B3154289
theorem B2661437 : Blo 2101435 2661437 := bbase (se 3 (by rfl) ⟨499019, by rfl⟩ : syracuseStep 2661437 = 998039) (by norm_num)
theorem B7097165 : Blo 2101435 7097165 := bstep (se 3 (by rfl) ⟨1330718, by rfl⟩ : syracuseStep 7097165 = 2661437) B2661437
theorem B4731443 : Blo 2101435 4731443 := bstep (se 1 (by rfl) ⟨3548582, by rfl⟩ : syracuseStep 4731443 = 7097165) B7097165
theorem B3154295 : Blo 2101435 3154295 := bstep (se 1 (by rfl) ⟨2365721, by rfl⟩ : syracuseStep 3154295 = 4731443) B4731443
theorem B2102863 : Blo 2101435 2102863 := bstep (se 1 (by rfl) ⟨1577147, by rfl⟩ : syracuseStep 2102863 = 3154295) B3154295
theorem B3154301 : Blo 2101435 3154301 := bbase (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) (by norm_num)
theorem B2102867 : Blo 2101435 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B4731461 : Blo 2101435 4731461 := bbase (se 4 (by rfl) ⟨443574, by rfl⟩ : syracuseStep 4731461 = 887149) (by norm_num)
theorem B3154307 : Blo 2101435 3154307 := bstep (se 1 (by rfl) ⟨2365730, by rfl⟩ : syracuseStep 3154307 = 4731461) B4731461
theorem B2102871 : Blo 2101435 2102871 := bstep (se 1 (by rfl) ⟨1577153, by rfl⟩ : syracuseStep 2102871 = 3154307) B3154307
theorem B2245601 : Blo 2101435 2245601 := bbase (se 2 (by rfl) ⟨842100, by rfl⟩ : syracuseStep 2245601 = 1684201) (by norm_num)
theorem B5988269 : Blo 2101435 5988269 := bstep (se 3 (by rfl) ⟨1122800, by rfl⟩ : syracuseStep 5988269 = 2245601) B2245601
theorem B3992179 : Blo 2101435 3992179 := bstep (se 1 (by rfl) ⟨2994134, by rfl⟩ : syracuseStep 3992179 = 5988269) B5988269
theorem B5322905 : Blo 2101435 5322905 := bstep (se 2 (by rfl) ⟨1996089, by rfl⟩ : syracuseStep 5322905 = 3992179) B3992179
theorem B3548603 : Blo 2101435 3548603 := bstep (se 1 (by rfl) ⟨2661452, by rfl⟩ : syracuseStep 3548603 = 5322905) B5322905
theorem B2365735 : Blo 2101435 2365735 := bstep (se 1 (by rfl) ⟨1774301, by rfl⟩ : syracuseStep 2365735 = 3548603) B3548603
theorem B3154313 : Blo 2101435 3154313 := bstep (se 2 (by rfl) ⟨1182867, by rfl⟩ : syracuseStep 3154313 = 2365735) B2365735
theorem B2102875 : Blo 2101435 2102875 := bstep (se 1 (by rfl) ⟨1577156, by rfl⟩ : syracuseStep 2102875 = 3154313) B3154313
theorem B10645829 : Blo 2101435 10645829 := bbase (se 4 (by rfl) ⟨998046, by rfl⟩ : syracuseStep 10645829 = 1996093) (by norm_num)
theorem B7097219 : Blo 2101435 7097219 := bstep (se 1 (by rfl) ⟨5322914, by rfl⟩ : syracuseStep 7097219 = 10645829) B10645829
theorem B4731479 : Blo 2101435 4731479 := bstep (se 1 (by rfl) ⟨3548609, by rfl⟩ : syracuseStep 4731479 = 7097219) B7097219
theorem B3154319 : Blo 2101435 3154319 := bstep (se 1 (by rfl) ⟨2365739, by rfl⟩ : syracuseStep 3154319 = 4731479) B4731479
theorem B2102879 : Blo 2101435 2102879 := bstep (se 1 (by rfl) ⟨1577159, by rfl⟩ : syracuseStep 2102879 = 3154319) B3154319
theorem B3154325 : Blo 2101435 3154325 := bbase (se 6 (by rfl) ⟨73929, by rfl⟩ : syracuseStep 3154325 = 147859) (by norm_num)
theorem B2102883 : Blo 2101435 2102883 := bstep (se 1 (by rfl) ⟨1577162, by rfl⟩ : syracuseStep 2102883 = 3154325) B3154325
theorem B2697781 : Blo 2101435 2697781 := bbase (se 5 (by rfl) ⟨126458, by rfl⟩ : syracuseStep 2697781 = 252917) (by norm_num)
theorem B3597041 : Blo 2101435 3597041 := bstep (se 2 (by rfl) ⟨1348890, by rfl⟩ : syracuseStep 3597041 = 2697781) B2697781
theorem B2398027 : Blo 2101435 2398027 := bstep (se 1 (by rfl) ⟨1798520, by rfl⟩ : syracuseStep 2398027 = 3597041) B3597041
theorem B3197369 : Blo 2101435 3197369 := bstep (se 2 (by rfl) ⟨1199013, by rfl⟩ : syracuseStep 3197369 = 2398027) B2398027
theorem B2131579 : Blo 2101435 2131579 := bstep (se 1 (by rfl) ⟨1598684, by rfl⟩ : syracuseStep 2131579 = 3197369) B3197369
theorem B11368421 : Blo 2101435 11368421 := bstep (se 4 (by rfl) ⟨1065789, by rfl⟩ : syracuseStep 11368421 = 2131579) B2131579
theorem B7578947 : Blo 2101435 7578947 := bstep (se 1 (by rfl) ⟨5684210, by rfl⟩ : syracuseStep 7578947 = 11368421) B11368421
theorem B5052631 : Blo 2101435 5052631 := bstep (se 1 (by rfl) ⟨3789473, by rfl⟩ : syracuseStep 5052631 = 7578947) B7578947
theorem B6736841 : Blo 2101435 6736841 := bstep (se 2 (by rfl) ⟨2526315, by rfl⟩ : syracuseStep 6736841 = 5052631) B5052631
theorem B4491227 : Blo 2101435 4491227 := bstep (se 1 (by rfl) ⟨3368420, by rfl⟩ : syracuseStep 4491227 = 6736841) B6736841
theorem B11976605 : Blo 2101435 11976605 := bstep (se 3 (by rfl) ⟨2245613, by rfl⟩ : syracuseStep 11976605 = 4491227) B4491227
theorem B7984403 : Blo 2101435 7984403 := bstep (se 1 (by rfl) ⟨5988302, by rfl⟩ : syracuseStep 7984403 = 11976605) B11976605
theorem B5322935 : Blo 2101435 5322935 := bstep (se 1 (by rfl) ⟨3992201, by rfl⟩ : syracuseStep 5322935 = 7984403) B7984403
theorem B3548623 : Blo 2101435 3548623 := bstep (se 1 (by rfl) ⟨2661467, by rfl⟩ : syracuseStep 3548623 = 5322935) B5322935
theorem B4731497 : Blo 2101435 4731497 := bstep (se 2 (by rfl) ⟨1774311, by rfl⟩ : syracuseStep 4731497 = 3548623) B3548623
theorem B3154331 : Blo 2101435 3154331 := bstep (se 1 (by rfl) ⟨2365748, by rfl⟩ : syracuseStep 3154331 = 4731497) B4731497
theorem B2102887 : Blo 2101435 2102887 := bstep (se 1 (by rfl) ⟨1577165, by rfl⟩ : syracuseStep 2102887 = 3154331) B3154331
theorem B2365753 : Blo 2101435 2365753 := bbase (se 2 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 2365753 = 1774315) (by norm_num)
theorem B3154337 : Blo 2101435 3154337 := bstep (se 2 (by rfl) ⟨1182876, by rfl⟩ : syracuseStep 3154337 = 2365753) B2365753
theorem B2102891 : Blo 2101435 2102891 := bstep (se 1 (by rfl) ⟨1577168, by rfl⟩ : syracuseStep 2102891 = 3154337) B3154337
theorem B5988325 : Blo 2101435 5988325 := bbase (se 4 (by rfl) ⟨561405, by rfl⟩ : syracuseStep 5988325 = 1122811) (by norm_num)
theorem B7984433 : Blo 2101435 7984433 := bstep (se 2 (by rfl) ⟨2994162, by rfl⟩ : syracuseStep 7984433 = 5988325) B5988325
theorem B5322955 : Blo 2101435 5322955 := bstep (se 1 (by rfl) ⟨3992216, by rfl⟩ : syracuseStep 5322955 = 7984433) B7984433
theorem B7097273 : Blo 2101435 7097273 := bstep (se 2 (by rfl) ⟨2661477, by rfl⟩ : syracuseStep 7097273 = 5322955) B5322955
theorem B4731515 : Blo 2101435 4731515 := bstep (se 1 (by rfl) ⟨3548636, by rfl⟩ : syracuseStep 4731515 = 7097273) B7097273
theorem B3154343 : Blo 2101435 3154343 := bstep (se 1 (by rfl) ⟨2365757, by rfl⟩ : syracuseStep 3154343 = 4731515) B4731515
theorem B2102895 : Blo 2101435 2102895 := bstep (se 1 (by rfl) ⟨1577171, by rfl⟩ : syracuseStep 2102895 = 3154343) B3154343
theorem B3154349 : Blo 2101435 3154349 := bbase (se 3 (by rfl) ⟨591440, by rfl⟩ : syracuseStep 3154349 = 1182881) (by norm_num)
theorem B2102899 : Blo 2101435 2102899 := bstep (se 1 (by rfl) ⟨1577174, by rfl⟩ : syracuseStep 2102899 = 3154349) B3154349
theorem B4731533 : Blo 2101435 4731533 := bbase (se 3 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 4731533 = 1774325) (by norm_num)
theorem B3154355 : Blo 2101435 3154355 := bstep (se 1 (by rfl) ⟨2365766, by rfl⟩ : syracuseStep 3154355 = 4731533) B4731533
theorem B2102903 : Blo 2101435 2102903 := bstep (se 1 (by rfl) ⟨1577177, by rfl⟩ : syracuseStep 2102903 = 3154355) B3154355
theorem B2661493 : Blo 2101435 2661493 := bbase (se 5 (by rfl) ⟨124757, by rfl⟩ : syracuseStep 2661493 = 249515) (by norm_num)
theorem B3548657 : Blo 2101435 3548657 := bstep (se 2 (by rfl) ⟨1330746, by rfl⟩ : syracuseStep 3548657 = 2661493) B2661493
theorem B2365771 : Blo 2101435 2365771 := bstep (se 1 (by rfl) ⟨1774328, by rfl⟩ : syracuseStep 2365771 = 3548657) B3548657
theorem B3154361 : Blo 2101435 3154361 := bstep (se 2 (by rfl) ⟨1182885, by rfl⟩ : syracuseStep 3154361 = 2365771) B2365771
theorem B2102907 : Blo 2101435 2102907 := bstep (se 1 (by rfl) ⟨1577180, by rfl⟩ : syracuseStep 2102907 = 3154361) B3154361
theorem B10938469 : Blo 2101435 10938469 := bbase (se 4 (by rfl) ⟨1025481, by rfl⟩ : syracuseStep 10938469 = 2050963) (by norm_num)
theorem B14584625 : Blo 2101435 14584625 := bstep (se 2 (by rfl) ⟨5469234, by rfl⟩ : syracuseStep 14584625 = 10938469) B10938469
theorem B9723083 : Blo 2101435 9723083 := bstep (se 1 (by rfl) ⟨7292312, by rfl⟩ : syracuseStep 9723083 = 14584625) B14584625
theorem B103712885 : Blo 2101435 103712885 := bstep (se 5 (by rfl) ⟨4861541, by rfl⟩ : syracuseStep 103712885 = 9723083) B9723083
theorem B69141923 : Blo 2101435 69141923 := bstep (se 1 (by rfl) ⟨51856442, by rfl⟩ : syracuseStep 69141923 = 103712885) B103712885
theorem B46094615 : Blo 2101435 46094615 := bstep (se 1 (by rfl) ⟨34570961, by rfl⟩ : syracuseStep 46094615 = 69141923) B69141923
theorem B30729743 : Blo 2101435 30729743 := bstep (se 1 (by rfl) ⟨23047307, by rfl⟩ : syracuseStep 30729743 = 46094615) B46094615
theorem B20486495 : Blo 2101435 20486495 := bstep (se 1 (by rfl) ⟨15364871, by rfl⟩ : syracuseStep 20486495 = 30729743) B30729743
theorem B13657663 : Blo 2101435 13657663 := bstep (se 1 (by rfl) ⟨10243247, by rfl⟩ : syracuseStep 13657663 = 20486495) B20486495
theorem B18210217 : Blo 2101435 18210217 := bstep (se 2 (by rfl) ⟨6828831, by rfl⟩ : syracuseStep 18210217 = 13657663) B13657663
theorem B24280289 : Blo 2101435 24280289 := bstep (se 2 (by rfl) ⟨9105108, by rfl⟩ : syracuseStep 24280289 = 18210217) B18210217
theorem B16186859 : Blo 2101435 16186859 := bstep (se 1 (by rfl) ⟨12140144, by rfl⟩ : syracuseStep 16186859 = 24280289) B24280289
theorem B10791239 : Blo 2101435 10791239 := bstep (se 1 (by rfl) ⟨8093429, by rfl⟩ : syracuseStep 10791239 = 16186859) B16186859
theorem B28776637 : Blo 2101435 28776637 := bstep (se 3 (by rfl) ⟨5395619, by rfl⟩ : syracuseStep 28776637 = 10791239) B10791239
theorem B38368849 : Blo 2101435 38368849 := bstep (se 2 (by rfl) ⟨14388318, by rfl⟩ : syracuseStep 38368849 = 28776637) B28776637
theorem B51158465 : Blo 2101435 51158465 := bstep (se 2 (by rfl) ⟨19184424, by rfl⟩ : syracuseStep 51158465 = 38368849) B38368849
theorem B34105643 : Blo 2101435 34105643 := bstep (se 1 (by rfl) ⟨25579232, by rfl⟩ : syracuseStep 34105643 = 51158465) B51158465
theorem B22737095 : Blo 2101435 22737095 := bstep (se 1 (by rfl) ⟨17052821, by rfl⟩ : syracuseStep 22737095 = 34105643) B34105643
theorem B15158063 : Blo 2101435 15158063 := bstep (se 1 (by rfl) ⟨11368547, by rfl⟩ : syracuseStep 15158063 = 22737095) B22737095
theorem B40421501 : Blo 2101435 40421501 := bstep (se 3 (by rfl) ⟨7579031, by rfl⟩ : syracuseStep 40421501 = 15158063) B15158063
theorem B26947667 : Blo 2101435 26947667 := bstep (se 1 (by rfl) ⟨20210750, by rfl⟩ : syracuseStep 26947667 = 40421501) B40421501
theorem B17965111 : Blo 2101435 17965111 := bstep (se 1 (by rfl) ⟨13473833, by rfl⟩ : syracuseStep 17965111 = 26947667) B26947667
theorem B23953481 : Blo 2101435 23953481 := bstep (se 2 (by rfl) ⟨8982555, by rfl⟩ : syracuseStep 23953481 = 17965111) B17965111
theorem B15968987 : Blo 2101435 15968987 := bstep (se 1 (by rfl) ⟨11976740, by rfl⟩ : syracuseStep 15968987 = 23953481) B23953481
theorem B10645991 : Blo 2101435 10645991 := bstep (se 1 (by rfl) ⟨7984493, by rfl⟩ : syracuseStep 10645991 = 15968987) B15968987
theorem B7097327 : Blo 2101435 7097327 := bstep (se 1 (by rfl) ⟨5322995, by rfl⟩ : syracuseStep 7097327 = 10645991) B10645991
theorem B4731551 : Blo 2101435 4731551 := bstep (se 1 (by rfl) ⟨3548663, by rfl⟩ : syracuseStep 4731551 = 7097327) B7097327
theorem B3154367 : Blo 2101435 3154367 := bstep (se 1 (by rfl) ⟨2365775, by rfl⟩ : syracuseStep 3154367 = 4731551) B4731551
theorem B2102911 : Blo 2101435 2102911 := bstep (se 1 (by rfl) ⟨1577183, by rfl⟩ : syracuseStep 2102911 = 3154367) B3154367
theorem B3154373 : Blo 2101435 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B2102915 : Blo 2101435 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B3548677 : Blo 2101435 3548677 := bbase (se 4 (by rfl) ⟨332688, by rfl⟩ : syracuseStep 3548677 = 665377) (by norm_num)
theorem B4731569 : Blo 2101435 4731569 := bstep (se 2 (by rfl) ⟨1774338, by rfl⟩ : syracuseStep 4731569 = 3548677) B3548677
theorem B3154379 : Blo 2101435 3154379 := bstep (se 1 (by rfl) ⟨2365784, by rfl⟩ : syracuseStep 3154379 = 4731569) B4731569
theorem B2102919 : Blo 2101435 2102919 := bstep (se 1 (by rfl) ⟨1577189, by rfl⟩ : syracuseStep 2102919 = 3154379) B3154379
theorem B2365789 : Blo 2101435 2365789 := bbase (se 3 (by rfl) ⟨443585, by rfl⟩ : syracuseStep 2365789 = 887171) (by norm_num)
theorem B3154385 : Blo 2101435 3154385 := bstep (se 2 (by rfl) ⟨1182894, by rfl⟩ : syracuseStep 3154385 = 2365789) B2365789
theorem B2102923 : Blo 2101435 2102923 := bstep (se 1 (by rfl) ⟨1577192, by rfl⟩ : syracuseStep 2102923 = 3154385) B3154385
theorem B7097381 : Blo 2101435 7097381 := bbase (se 4 (by rfl) ⟨665379, by rfl⟩ : syracuseStep 7097381 = 1330759) (by norm_num)
theorem B4731587 : Blo 2101435 4731587 := bstep (se 1 (by rfl) ⟨3548690, by rfl⟩ : syracuseStep 4731587 = 7097381) B7097381
theorem B3154391 : Blo 2101435 3154391 := bstep (se 1 (by rfl) ⟨2365793, by rfl⟩ : syracuseStep 3154391 = 4731587) B4731587
theorem B2102927 : Blo 2101435 2102927 := bstep (se 1 (by rfl) ⟨1577195, by rfl⟩ : syracuseStep 2102927 = 3154391) B3154391
theorem B3154397 : Blo 2101435 3154397 := bbase (se 3 (by rfl) ⟨591449, by rfl⟩ : syracuseStep 3154397 = 1182899) (by norm_num)
theorem B2102931 : Blo 2101435 2102931 := bstep (se 1 (by rfl) ⟨1577198, by rfl⟩ : syracuseStep 2102931 = 3154397) B3154397
theorem B4731605 : Blo 2101435 4731605 := bbase (se 7 (by rfl) ⟨55448, by rfl⟩ : syracuseStep 4731605 = 110897) (by norm_num)
theorem B3154403 : Blo 2101435 3154403 := bstep (se 1 (by rfl) ⟨2365802, by rfl⟩ : syracuseStep 3154403 = 4731605) B4731605
theorem B2102935 : Blo 2101435 2102935 := bstep (se 1 (by rfl) ⟨1577201, by rfl⟩ : syracuseStep 2102935 = 3154403) B3154403
theorem B8982677 : Blo 2101435 8982677 := bbase (se 6 (by rfl) ⟨210531, by rfl⟩ : syracuseStep 8982677 = 421063) (by norm_num)
theorem B5988451 : Blo 2101435 5988451 := bstep (se 1 (by rfl) ⟨4491338, by rfl⟩ : syracuseStep 5988451 = 8982677) B8982677
theorem B7984601 : Blo 2101435 7984601 := bstep (se 2 (by rfl) ⟨2994225, by rfl⟩ : syracuseStep 7984601 = 5988451) B5988451
theorem B5323067 : Blo 2101435 5323067 := bstep (se 1 (by rfl) ⟨3992300, by rfl⟩ : syracuseStep 5323067 = 7984601) B7984601
theorem B3548711 : Blo 2101435 3548711 := bstep (se 1 (by rfl) ⟨2661533, by rfl⟩ : syracuseStep 3548711 = 5323067) B5323067
theorem B2365807 : Blo 2101435 2365807 := bstep (se 1 (by rfl) ⟨1774355, by rfl⟩ : syracuseStep 2365807 = 3548711) B3548711
theorem B3154409 : Blo 2101435 3154409 := bstep (se 2 (by rfl) ⟨1182903, by rfl⟩ : syracuseStep 3154409 = 2365807) B2365807
theorem B2102939 : Blo 2101435 2102939 := bstep (se 1 (by rfl) ⟨1577204, by rfl⟩ : syracuseStep 2102939 = 3154409) B3154409
theorem B3197453 : Blo 2101435 3197453 := bbase (se 3 (by rfl) ⟨599522, by rfl⟩ : syracuseStep 3197453 = 1199045) (by norm_num)
theorem B8526541 : Blo 2101435 8526541 := bstep (se 3 (by rfl) ⟨1598726, by rfl⟩ : syracuseStep 8526541 = 3197453) B3197453
theorem B11368721 : Blo 2101435 11368721 := bstep (se 2 (by rfl) ⟨4263270, by rfl⟩ : syracuseStep 11368721 = 8526541) B8526541
theorem B30316589 : Blo 2101435 30316589 := bstep (se 3 (by rfl) ⟨5684360, by rfl⟩ : syracuseStep 30316589 = 11368721) B11368721
theorem B20211059 : Blo 2101435 20211059 := bstep (se 1 (by rfl) ⟨15158294, by rfl⟩ : syracuseStep 20211059 = 30316589) B30316589
theorem B13474039 : Blo 2101435 13474039 := bstep (se 1 (by rfl) ⟨10105529, by rfl⟩ : syracuseStep 13474039 = 20211059) B20211059
theorem B17965385 : Blo 2101435 17965385 := bstep (se 2 (by rfl) ⟨6737019, by rfl⟩ : syracuseStep 17965385 = 13474039) B13474039
theorem B11976923 : Blo 2101435 11976923 := bstep (se 1 (by rfl) ⟨8982692, by rfl⟩ : syracuseStep 11976923 = 17965385) B17965385
theorem B7984615 : Blo 2101435 7984615 := bstep (se 1 (by rfl) ⟨5988461, by rfl⟩ : syracuseStep 7984615 = 11976923) B11976923
theorem B10646153 : Blo 2101435 10646153 := bstep (se 2 (by rfl) ⟨3992307, by rfl⟩ : syracuseStep 10646153 = 7984615) B7984615
theorem B7097435 : Blo 2101435 7097435 := bstep (se 1 (by rfl) ⟨5323076, by rfl⟩ : syracuseStep 7097435 = 10646153) B10646153
theorem B4731623 : Blo 2101435 4731623 := bstep (se 1 (by rfl) ⟨3548717, by rfl⟩ : syracuseStep 4731623 = 7097435) B7097435
theorem B3154415 : Blo 2101435 3154415 := bstep (se 1 (by rfl) ⟨2365811, by rfl⟩ : syracuseStep 3154415 = 4731623) B4731623
theorem B2102943 : Blo 2101435 2102943 := bstep (se 1 (by rfl) ⟨1577207, by rfl⟩ : syracuseStep 2102943 = 3154415) B3154415
theorem B3154421 : Blo 2101435 3154421 := bbase (se 5 (by rfl) ⟨147863, by rfl⟩ : syracuseStep 3154421 = 295727) (by norm_num)
theorem B2102947 : Blo 2101435 2102947 := bstep (se 1 (by rfl) ⟨1577210, by rfl⟩ : syracuseStep 2102947 = 3154421) B3154421
theorem B5988485 : Blo 2101435 5988485 := bbase (se 4 (by rfl) ⟨561420, by rfl⟩ : syracuseStep 5988485 = 1122841) (by norm_num)
theorem B3992323 : Blo 2101435 3992323 := bstep (se 1 (by rfl) ⟨2994242, by rfl⟩ : syracuseStep 3992323 = 5988485) B5988485
theorem B5323097 : Blo 2101435 5323097 := bstep (se 2 (by rfl) ⟨1996161, by rfl⟩ : syracuseStep 5323097 = 3992323) B3992323
theorem B3548731 : Blo 2101435 3548731 := bstep (se 1 (by rfl) ⟨2661548, by rfl⟩ : syracuseStep 3548731 = 5323097) B5323097
theorem B4731641 : Blo 2101435 4731641 := bstep (se 2 (by rfl) ⟨1774365, by rfl⟩ : syracuseStep 4731641 = 3548731) B3548731
theorem B3154427 : Blo 2101435 3154427 := bstep (se 1 (by rfl) ⟨2365820, by rfl⟩ : syracuseStep 3154427 = 4731641) B4731641
theorem B2102951 : Blo 2101435 2102951 := bstep (se 1 (by rfl) ⟨1577213, by rfl⟩ : syracuseStep 2102951 = 3154427) B3154427
theorem B2365825 : Blo 2101435 2365825 := bbase (se 2 (by rfl) ⟨887184, by rfl⟩ : syracuseStep 2365825 = 1774369) (by norm_num)
theorem B3154433 : Blo 2101435 3154433 := bstep (se 2 (by rfl) ⟨1182912, by rfl⟩ : syracuseStep 3154433 = 2365825) B2365825
theorem B2102955 : Blo 2101435 2102955 := bstep (se 1 (by rfl) ⟨1577216, by rfl⟩ : syracuseStep 2102955 = 3154433) B3154433
theorem B5323117 : Blo 2101435 5323117 := bbase (se 3 (by rfl) ⟨998084, by rfl⟩ : syracuseStep 5323117 = 1996169) (by norm_num)
theorem B7097489 : Blo 2101435 7097489 := bstep (se 2 (by rfl) ⟨2661558, by rfl⟩ : syracuseStep 7097489 = 5323117) B5323117
theorem B4731659 : Blo 2101435 4731659 := bstep (se 1 (by rfl) ⟨3548744, by rfl⟩ : syracuseStep 4731659 = 7097489) B7097489
theorem B3154439 : Blo 2101435 3154439 := bstep (se 1 (by rfl) ⟨2365829, by rfl⟩ : syracuseStep 3154439 = 4731659) B4731659
theorem B2102959 : Blo 2101435 2102959 := bstep (se 1 (by rfl) ⟨1577219, by rfl⟩ : syracuseStep 2102959 = 3154439) B3154439
theorem B3154445 : Blo 2101435 3154445 := bbase (se 3 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 3154445 = 1182917) (by norm_num)
theorem B2102963 : Blo 2101435 2102963 := bstep (se 1 (by rfl) ⟨1577222, by rfl⟩ : syracuseStep 2102963 = 3154445) B3154445
theorem B4731677 : Blo 2101435 4731677 := bbase (se 3 (by rfl) ⟨887189, by rfl⟩ : syracuseStep 4731677 = 1774379) (by norm_num)
theorem B3154451 : Blo 2101435 3154451 := bstep (se 1 (by rfl) ⟨2365838, by rfl⟩ : syracuseStep 3154451 = 4731677) B4731677
theorem B2102967 : Blo 2101435 2102967 := bstep (se 1 (by rfl) ⟨1577225, by rfl⟩ : syracuseStep 2102967 = 3154451) B3154451
theorem B3548765 : Blo 2101435 3548765 := bbase (se 3 (by rfl) ⟨665393, by rfl⟩ : syracuseStep 3548765 = 1330787) (by norm_num)
theorem B2365843 : Blo 2101435 2365843 := bstep (se 1 (by rfl) ⟨1774382, by rfl⟩ : syracuseStep 2365843 = 3548765) B3548765
theorem B3154457 : Blo 2101435 3154457 := bstep (se 2 (by rfl) ⟨1182921, by rfl⟩ : syracuseStep 3154457 = 2365843) B2365843
theorem B2102971 : Blo 2101435 2102971 := bstep (se 1 (by rfl) ⟨1577228, by rfl⟩ : syracuseStep 2102971 = 3154457) B3154457
theorem B2526421 : Blo 2101435 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B3368561 : Blo 2101435 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B8982829 : Blo 2101435 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B11977105 : Blo 2101435 11977105 := bstep (se 2 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 11977105 = 8982829) B8982829
theorem B15969473 : Blo 2101435 15969473 := bstep (se 2 (by rfl) ⟨5988552, by rfl⟩ : syracuseStep 15969473 = 11977105) B11977105
theorem B10646315 : Blo 2101435 10646315 := bstep (se 1 (by rfl) ⟨7984736, by rfl⟩ : syracuseStep 10646315 = 15969473) B15969473
theorem B7097543 : Blo 2101435 7097543 := bstep (se 1 (by rfl) ⟨5323157, by rfl⟩ : syracuseStep 7097543 = 10646315) B10646315
theorem B4731695 : Blo 2101435 4731695 := bstep (se 1 (by rfl) ⟨3548771, by rfl⟩ : syracuseStep 4731695 = 7097543) B7097543
theorem B3154463 : Blo 2101435 3154463 := bstep (se 1 (by rfl) ⟨2365847, by rfl⟩ : syracuseStep 3154463 = 4731695) B4731695
theorem B2102975 : Blo 2101435 2102975 := bstep (se 1 (by rfl) ⟨1577231, by rfl⟩ : syracuseStep 2102975 = 3154463) B3154463
theorem B3154469 : Blo 2101435 3154469 := bbase (se 4 (by rfl) ⟨295731, by rfl⟩ : syracuseStep 3154469 = 591463) (by norm_num)
theorem B2102979 : Blo 2101435 2102979 := bstep (se 1 (by rfl) ⟨1577234, by rfl⟩ : syracuseStep 2102979 = 3154469) B3154469
theorem B2661589 : Blo 2101435 2661589 := bbase (se 7 (by rfl) ⟨31190, by rfl⟩ : syracuseStep 2661589 = 62381) (by norm_num)
theorem B3548785 : Blo 2101435 3548785 := bstep (se 2 (by rfl) ⟨1330794, by rfl⟩ : syracuseStep 3548785 = 2661589) B2661589
theorem B4731713 : Blo 2101435 4731713 := bstep (se 2 (by rfl) ⟨1774392, by rfl⟩ : syracuseStep 4731713 = 3548785) B3548785
theorem B3154475 : Blo 2101435 3154475 := bstep (se 1 (by rfl) ⟨2365856, by rfl⟩ : syracuseStep 3154475 = 4731713) B4731713
theorem B2102983 : Blo 2101435 2102983 := bstep (se 1 (by rfl) ⟨1577237, by rfl⟩ : syracuseStep 2102983 = 3154475) B3154475
theorem B2365861 : Blo 2101435 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B3154481 : Blo 2101435 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B2102987 : Blo 2101435 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B3789661 : Blo 2101435 3789661 := bbase (se 3 (by rfl) ⟨710561, by rfl⟩ : syracuseStep 3789661 = 1421123) (by norm_num)
theorem B5052881 : Blo 2101435 5052881 := bstep (se 2 (by rfl) ⟨1894830, by rfl⟩ : syracuseStep 5052881 = 3789661) B3789661
theorem B13474349 : Blo 2101435 13474349 := bstep (se 3 (by rfl) ⟨2526440, by rfl⟩ : syracuseStep 13474349 = 5052881) B5052881
theorem B8982899 : Blo 2101435 8982899 := bstep (se 1 (by rfl) ⟨6737174, by rfl⟩ : syracuseStep 8982899 = 13474349) B13474349
theorem B5988599 : Blo 2101435 5988599 := bstep (se 1 (by rfl) ⟨4491449, by rfl⟩ : syracuseStep 5988599 = 8982899) B8982899
theorem B3992399 : Blo 2101435 3992399 := bstep (se 1 (by rfl) ⟨2994299, by rfl⟩ : syracuseStep 3992399 = 5988599) B5988599
theorem B2661599 : Blo 2101435 2661599 := bstep (se 1 (by rfl) ⟨1996199, by rfl⟩ : syracuseStep 2661599 = 3992399) B3992399
theorem B7097597 : Blo 2101435 7097597 := bstep (se 3 (by rfl) ⟨1330799, by rfl⟩ : syracuseStep 7097597 = 2661599) B2661599
theorem B4731731 : Blo 2101435 4731731 := bstep (se 1 (by rfl) ⟨3548798, by rfl⟩ : syracuseStep 4731731 = 7097597) B7097597
theorem B3154487 : Blo 2101435 3154487 := bstep (se 1 (by rfl) ⟨2365865, by rfl⟩ : syracuseStep 3154487 = 4731731) B4731731
theorem B2102991 : Blo 2101435 2102991 := bstep (se 1 (by rfl) ⟨1577243, by rfl⟩ : syracuseStep 2102991 = 3154487) B3154487
theorem B3154493 : Blo 2101435 3154493 := bbase (se 3 (by rfl) ⟨591467, by rfl⟩ : syracuseStep 3154493 = 1182935) (by norm_num)
theorem B2102995 : Blo 2101435 2102995 := bstep (se 1 (by rfl) ⟨1577246, by rfl⟩ : syracuseStep 2102995 = 3154493) B3154493
theorem B4731749 : Blo 2101435 4731749 := bbase (se 4 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 4731749 = 887203) (by norm_num)
theorem B3154499 : Blo 2101435 3154499 := bstep (se 1 (by rfl) ⟨2365874, by rfl⟩ : syracuseStep 3154499 = 4731749) B4731749
theorem B2102999 : Blo 2101435 2102999 := bstep (se 1 (by rfl) ⟨1577249, by rfl⟩ : syracuseStep 2102999 = 3154499) B3154499
theorem B5323229 : Blo 2101435 5323229 := bbase (se 3 (by rfl) ⟨998105, by rfl⟩ : syracuseStep 5323229 = 1996211) (by norm_num)
theorem B3548819 : Blo 2101435 3548819 := bstep (se 1 (by rfl) ⟨2661614, by rfl⟩ : syracuseStep 3548819 = 5323229) B5323229
theorem B2365879 : Blo 2101435 2365879 := bstep (se 1 (by rfl) ⟨1774409, by rfl⟩ : syracuseStep 2365879 = 3548819) B3548819
theorem B3154505 : Blo 2101435 3154505 := bstep (se 2 (by rfl) ⟨1182939, by rfl⟩ : syracuseStep 3154505 = 2365879) B2365879
theorem B2103003 : Blo 2101435 2103003 := bstep (se 1 (by rfl) ⟨1577252, by rfl⟩ : syracuseStep 2103003 = 3154505) B3154505
theorem B3992429 : Blo 2101435 3992429 := bbase (se 3 (by rfl) ⟨748580, by rfl⟩ : syracuseStep 3992429 = 1497161) (by norm_num)
theorem B10646477 : Blo 2101435 10646477 := bstep (se 3 (by rfl) ⟨1996214, by rfl⟩ : syracuseStep 10646477 = 3992429) B3992429
theorem B7097651 : Blo 2101435 7097651 := bstep (se 1 (by rfl) ⟨5323238, by rfl⟩ : syracuseStep 7097651 = 10646477) B10646477
theorem B4731767 : Blo 2101435 4731767 := bstep (se 1 (by rfl) ⟨3548825, by rfl⟩ : syracuseStep 4731767 = 7097651) B7097651
theorem B3154511 : Blo 2101435 3154511 := bstep (se 1 (by rfl) ⟨2365883, by rfl⟩ : syracuseStep 3154511 = 4731767) B4731767
theorem B2103007 : Blo 2101435 2103007 := bstep (se 1 (by rfl) ⟨1577255, by rfl⟩ : syracuseStep 2103007 = 3154511) B3154511
theorem B3154517 : Blo 2101435 3154517 := bbase (se 8 (by rfl) ⟨18483, by rfl⟩ : syracuseStep 3154517 = 36967) (by norm_num)
theorem B2103011 : Blo 2101435 2103011 := bstep (se 1 (by rfl) ⟨1577258, by rfl⟩ : syracuseStep 2103011 = 3154517) B3154517
theorem B10105877 : Blo 2101435 10105877 := bbase (se 6 (by rfl) ⟨236856, by rfl⟩ : syracuseStep 10105877 = 473713) (by norm_num)
theorem B6737251 : Blo 2101435 6737251 := bstep (se 1 (by rfl) ⟨5052938, by rfl⟩ : syracuseStep 6737251 = 10105877) B10105877
theorem B8983001 : Blo 2101435 8983001 := bstep (se 2 (by rfl) ⟨3368625, by rfl⟩ : syracuseStep 8983001 = 6737251) B6737251
theorem B5988667 : Blo 2101435 5988667 := bstep (se 1 (by rfl) ⟨4491500, by rfl⟩ : syracuseStep 5988667 = 8983001) B8983001
theorem B7984889 : Blo 2101435 7984889 := bstep (se 2 (by rfl) ⟨2994333, by rfl⟩ : syracuseStep 7984889 = 5988667) B5988667
theorem B5323259 : Blo 2101435 5323259 := bstep (se 1 (by rfl) ⟨3992444, by rfl⟩ : syracuseStep 5323259 = 7984889) B7984889
theorem B3548839 : Blo 2101435 3548839 := bstep (se 1 (by rfl) ⟨2661629, by rfl⟩ : syracuseStep 3548839 = 5323259) B5323259
theorem B4731785 : Blo 2101435 4731785 := bstep (se 2 (by rfl) ⟨1774419, by rfl⟩ : syracuseStep 4731785 = 3548839) B3548839
theorem B3154523 : Blo 2101435 3154523 := bstep (se 1 (by rfl) ⟨2365892, by rfl⟩ : syracuseStep 3154523 = 4731785) B4731785
theorem B2103015 : Blo 2101435 2103015 := bstep (se 1 (by rfl) ⟨1577261, by rfl⟩ : syracuseStep 2103015 = 3154523) B3154523
theorem B2365897 : Blo 2101435 2365897 := bbase (se 2 (by rfl) ⟨887211, by rfl⟩ : syracuseStep 2365897 = 1774423) (by norm_num)
theorem B3154529 : Blo 2101435 3154529 := bstep (se 2 (by rfl) ⟨1182948, by rfl⟩ : syracuseStep 3154529 = 2365897) B2365897
theorem B2103019 : Blo 2101435 2103019 := bstep (se 1 (by rfl) ⟨1577264, by rfl⟩ : syracuseStep 2103019 = 3154529) B3154529
theorem B17966069 : Blo 2101435 17966069 := bbase (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) (by norm_num)
theorem B11977379 : Blo 2101435 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B7984919 : Blo 2101435 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B5323279 : Blo 2101435 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B7097705 : Blo 2101435 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B4731803 : Blo 2101435 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B3154535 : Blo 2101435 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B2103023 : Blo 2101435 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B3154541 : Blo 2101435 3154541 := bbase (se 3 (by rfl) ⟨591476, by rfl⟩ : syracuseStep 3154541 = 1182953) (by norm_num)
theorem B2103027 : Blo 2101435 2103027 := bstep (se 1 (by rfl) ⟨1577270, by rfl⟩ : syracuseStep 2103027 = 3154541) B3154541
theorem B4731821 : Blo 2101435 4731821 := bbase (se 3 (by rfl) ⟨887216, by rfl⟩ : syracuseStep 4731821 = 1774433) (by norm_num)
theorem B3154547 : Blo 2101435 3154547 := bstep (se 1 (by rfl) ⟨2365910, by rfl⟩ : syracuseStep 3154547 = 4731821) B4731821
theorem B2103031 : Blo 2101435 2103031 := bstep (se 1 (by rfl) ⟨1577273, by rfl⟩ : syracuseStep 2103031 = 3154547) B3154547
theorem B5988725 : Blo 2101435 5988725 := bbase (se 5 (by rfl) ⟨280721, by rfl⟩ : syracuseStep 5988725 = 561443) (by norm_num)
theorem B3992483 : Blo 2101435 3992483 := bstep (se 1 (by rfl) ⟨2994362, by rfl⟩ : syracuseStep 3992483 = 5988725) B5988725
theorem B2661655 : Blo 2101435 2661655 := bstep (se 1 (by rfl) ⟨1996241, by rfl⟩ : syracuseStep 2661655 = 3992483) B3992483
theorem B3548873 : Blo 2101435 3548873 := bstep (se 2 (by rfl) ⟨1330827, by rfl⟩ : syracuseStep 3548873 = 2661655) B2661655
theorem B2365915 : Blo 2101435 2365915 := bstep (se 1 (by rfl) ⟨1774436, by rfl⟩ : syracuseStep 2365915 = 3548873) B3548873
theorem B3154553 : Blo 2101435 3154553 := bstep (se 2 (by rfl) ⟨1182957, by rfl⟩ : syracuseStep 3154553 = 2365915) B2365915
theorem B2103035 : Blo 2101435 2103035 := bstep (se 1 (by rfl) ⟨1577276, by rfl⟩ : syracuseStep 2103035 = 3154553) B3154553
theorem B5395949 : Blo 2101435 5395949 := bbase (se 3 (by rfl) ⟨1011740, by rfl⟩ : syracuseStep 5395949 = 2023481) (by norm_num)
theorem B3597299 : Blo 2101435 3597299 := bstep (se 1 (by rfl) ⟨2697974, by rfl⟩ : syracuseStep 3597299 = 5395949) B5395949
theorem B2398199 : Blo 2101435 2398199 := bstep (se 1 (by rfl) ⟨1798649, by rfl⟩ : syracuseStep 2398199 = 3597299) B3597299
theorem B25580789 : Blo 2101435 25580789 := bstep (se 5 (by rfl) ⟨1199099, by rfl⟩ : syracuseStep 25580789 = 2398199) B2398199
theorem B17053859 : Blo 2101435 17053859 := bstep (se 1 (by rfl) ⟨12790394, by rfl⟩ : syracuseStep 17053859 = 25580789) B25580789
theorem B45476957 : Blo 2101435 45476957 := bstep (se 3 (by rfl) ⟨8526929, by rfl⟩ : syracuseStep 45476957 = 17053859) B17053859
theorem B30317971 : Blo 2101435 30317971 := bstep (se 1 (by rfl) ⟨22738478, by rfl⟩ : syracuseStep 30317971 = 45476957) B45476957
theorem B40423961 : Blo 2101435 40423961 := bstep (se 2 (by rfl) ⟨15158985, by rfl⟩ : syracuseStep 40423961 = 30317971) B30317971
theorem B26949307 : Blo 2101435 26949307 := bstep (se 1 (by rfl) ⟨20211980, by rfl⟩ : syracuseStep 26949307 = 40423961) B40423961
theorem B35932409 : Blo 2101435 35932409 := bstep (se 2 (by rfl) ⟨13474653, by rfl⟩ : syracuseStep 35932409 = 26949307) B26949307
theorem B23954939 : Blo 2101435 23954939 := bstep (se 1 (by rfl) ⟨17966204, by rfl⟩ : syracuseStep 23954939 = 35932409) B35932409
theorem B15969959 : Blo 2101435 15969959 := bstep (se 1 (by rfl) ⟨11977469, by rfl⟩ : syracuseStep 15969959 = 23954939) B23954939
theorem B10646639 : Blo 2101435 10646639 := bstep (se 1 (by rfl) ⟨7984979, by rfl⟩ : syracuseStep 10646639 = 15969959) B15969959
theorem B7097759 : Blo 2101435 7097759 := bstep (se 1 (by rfl) ⟨5323319, by rfl⟩ : syracuseStep 7097759 = 10646639) B10646639
theorem B4731839 : Blo 2101435 4731839 := bstep (se 1 (by rfl) ⟨3548879, by rfl⟩ : syracuseStep 4731839 = 7097759) B7097759
theorem B3154559 : Blo 2101435 3154559 := bstep (se 1 (by rfl) ⟨2365919, by rfl⟩ : syracuseStep 3154559 = 4731839) B4731839
theorem B2103039 : Blo 2101435 2103039 := bstep (se 1 (by rfl) ⟨1577279, by rfl⟩ : syracuseStep 2103039 = 3154559) B3154559
theorem B3154565 : Blo 2101435 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B2103043 : Blo 2101435 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B3548893 : Blo 2101435 3548893 := bbase (se 3 (by rfl) ⟨665417, by rfl⟩ : syracuseStep 3548893 = 1330835) (by norm_num)
theorem B4731857 : Blo 2101435 4731857 := bstep (se 2 (by rfl) ⟨1774446, by rfl⟩ : syracuseStep 4731857 = 3548893) B3548893
theorem B3154571 : Blo 2101435 3154571 := bstep (se 1 (by rfl) ⟨2365928, by rfl⟩ : syracuseStep 3154571 = 4731857) B4731857
theorem B2103047 : Blo 2101435 2103047 := bstep (se 1 (by rfl) ⟨1577285, by rfl⟩ : syracuseStep 2103047 = 3154571) B3154571
theorem B2365933 : Blo 2101435 2365933 := bbase (se 3 (by rfl) ⟨443612, by rfl⟩ : syracuseStep 2365933 = 887225) (by norm_num)
theorem B3154577 : Blo 2101435 3154577 := bstep (se 2 (by rfl) ⟨1182966, by rfl⟩ : syracuseStep 3154577 = 2365933) B2365933
theorem B2103051 : Blo 2101435 2103051 := bstep (se 1 (by rfl) ⟨1577288, by rfl⟩ : syracuseStep 2103051 = 3154577) B3154577
theorem B7097813 : Blo 2101435 7097813 := bbase (se 7 (by rfl) ⟨83177, by rfl⟩ : syracuseStep 7097813 = 166355) (by norm_num)
theorem B4731875 : Blo 2101435 4731875 := bstep (se 1 (by rfl) ⟨3548906, by rfl⟩ : syracuseStep 4731875 = 7097813) B7097813
theorem B3154583 : Blo 2101435 3154583 := bstep (se 1 (by rfl) ⟨2365937, by rfl⟩ : syracuseStep 3154583 = 4731875) B4731875
theorem B2103055 : Blo 2101435 2103055 := bstep (se 1 (by rfl) ⟨1577291, by rfl⟩ : syracuseStep 2103055 = 3154583) B3154583
theorem B3154589 : Blo 2101435 3154589 := bbase (se 3 (by rfl) ⟨591485, by rfl⟩ : syracuseStep 3154589 = 1182971) (by norm_num)
theorem B2103059 : Blo 2101435 2103059 := bstep (se 1 (by rfl) ⟨1577294, by rfl⟩ : syracuseStep 2103059 = 3154589) B3154589
theorem B4731893 : Blo 2101435 4731893 := bbase (se 5 (by rfl) ⟨221807, by rfl⟩ : syracuseStep 4731893 = 443615) (by norm_num)
theorem B3154595 : Blo 2101435 3154595 := bstep (se 1 (by rfl) ⟨2365946, by rfl⟩ : syracuseStep 3154595 = 4731893) B4731893
theorem B2103063 : Blo 2101435 2103063 := bstep (se 1 (by rfl) ⟨1577297, by rfl⟩ : syracuseStep 2103063 = 3154595) B3154595
theorem B2307505 : Blo 2101435 2307505 := bbase (se 2 (by rfl) ⟨865314, by rfl⟩ : syracuseStep 2307505 = 1730629) (by norm_num)
theorem B49226773 : Blo 2101435 49226773 := bstep (se 6 (by rfl) ⟨1153752, by rfl⟩ : syracuseStep 49226773 = 2307505) B2307505
theorem B65635697 : Blo 2101435 65635697 := bstep (se 2 (by rfl) ⟨24613386, by rfl⟩ : syracuseStep 65635697 = 49226773) B49226773
theorem B43757131 : Blo 2101435 43757131 := bstep (se 1 (by rfl) ⟨32817848, by rfl⟩ : syracuseStep 43757131 = 65635697) B65635697
theorem B58342841 : Blo 2101435 58342841 := bstep (se 2 (by rfl) ⟨21878565, by rfl⟩ : syracuseStep 58342841 = 43757131) B43757131
theorem B38895227 : Blo 2101435 38895227 := bstep (se 1 (by rfl) ⟨29171420, by rfl⟩ : syracuseStep 38895227 = 58342841) B58342841
theorem B25930151 : Blo 2101435 25930151 := bstep (se 1 (by rfl) ⟨19447613, by rfl⟩ : syracuseStep 25930151 = 38895227) B38895227
theorem B17286767 : Blo 2101435 17286767 := bstep (se 1 (by rfl) ⟨12965075, by rfl⟩ : syracuseStep 17286767 = 25930151) B25930151
theorem B11524511 : Blo 2101435 11524511 := bstep (se 1 (by rfl) ⟨8643383, by rfl⟩ : syracuseStep 11524511 = 17286767) B17286767
theorem B7683007 : Blo 2101435 7683007 := bstep (se 1 (by rfl) ⟨5762255, by rfl⟩ : syracuseStep 7683007 = 11524511) B11524511
theorem B10244009 : Blo 2101435 10244009 := bstep (se 2 (by rfl) ⟨3841503, by rfl⟩ : syracuseStep 10244009 = 7683007) B7683007
theorem B27317357 : Blo 2101435 27317357 := bstep (se 3 (by rfl) ⟨5122004, by rfl⟩ : syracuseStep 27317357 = 10244009) B10244009
theorem B18211571 : Blo 2101435 18211571 := bstep (se 1 (by rfl) ⟨13658678, by rfl⟩ : syracuseStep 18211571 = 27317357) B27317357
theorem B12141047 : Blo 2101435 12141047 := bstep (se 1 (by rfl) ⟨9105785, by rfl⟩ : syracuseStep 12141047 = 18211571) B18211571
theorem B32376125 : Blo 2101435 32376125 := bstep (se 3 (by rfl) ⟨6070523, by rfl⟩ : syracuseStep 32376125 = 12141047) B12141047
theorem B21584083 : Blo 2101435 21584083 := bstep (se 1 (by rfl) ⟨16188062, by rfl⟩ : syracuseStep 21584083 = 32376125) B32376125
theorem B28778777 : Blo 2101435 28778777 := bstep (se 2 (by rfl) ⟨10792041, by rfl⟩ : syracuseStep 28778777 = 21584083) B21584083
theorem B19185851 : Blo 2101435 19185851 := bstep (se 1 (by rfl) ⟨14389388, by rfl⟩ : syracuseStep 19185851 = 28778777) B28778777
theorem B12790567 : Blo 2101435 12790567 := bstep (se 1 (by rfl) ⟨9592925, by rfl⟩ : syracuseStep 12790567 = 19185851) B19185851
theorem B68216357 : Blo 2101435 68216357 := bstep (se 4 (by rfl) ⟨6395283, by rfl⟩ : syracuseStep 68216357 = 12790567) B12790567
theorem B45477571 : Blo 2101435 45477571 := bstep (se 1 (by rfl) ⟨34108178, by rfl⟩ : syracuseStep 45477571 = 68216357) B68216357
theorem B60636761 : Blo 2101435 60636761 := bstep (se 2 (by rfl) ⟨22738785, by rfl⟩ : syracuseStep 60636761 = 45477571) B45477571
theorem B40424507 : Blo 2101435 40424507 := bstep (se 1 (by rfl) ⟨30318380, by rfl⟩ : syracuseStep 40424507 = 60636761) B60636761
theorem B26949671 : Blo 2101435 26949671 := bstep (se 1 (by rfl) ⟨20212253, by rfl⟩ : syracuseStep 26949671 = 40424507) B40424507
theorem B17966447 : Blo 2101435 17966447 := bstep (se 1 (by rfl) ⟨13474835, by rfl⟩ : syracuseStep 17966447 = 26949671) B26949671
theorem B11977631 : Blo 2101435 11977631 := bstep (se 1 (by rfl) ⟨8983223, by rfl⟩ : syracuseStep 11977631 = 17966447) B17966447
theorem B7985087 : Blo 2101435 7985087 := bstep (se 1 (by rfl) ⟨5988815, by rfl⟩ : syracuseStep 7985087 = 11977631) B11977631
theorem B5323391 : Blo 2101435 5323391 := bstep (se 1 (by rfl) ⟨3992543, by rfl⟩ : syracuseStep 5323391 = 7985087) B7985087
theorem B3548927 : Blo 2101435 3548927 := bstep (se 1 (by rfl) ⟨2661695, by rfl⟩ : syracuseStep 3548927 = 5323391) B5323391
theorem B2365951 : Blo 2101435 2365951 := bstep (se 1 (by rfl) ⟨1774463, by rfl⟩ : syracuseStep 2365951 = 3548927) B3548927
theorem B3154601 : Blo 2101435 3154601 := bstep (se 2 (by rfl) ⟨1182975, by rfl⟩ : syracuseStep 3154601 = 2365951) B2365951
theorem B2103067 : Blo 2101435 2103067 := bstep (se 1 (by rfl) ⟨1577300, by rfl⟩ : syracuseStep 2103067 = 3154601) B3154601
theorem B2994413 : Blo 2101435 2994413 := bbase (se 3 (by rfl) ⟨561452, by rfl⟩ : syracuseStep 2994413 = 1122905) (by norm_num)
theorem B7985101 : Blo 2101435 7985101 := bstep (se 3 (by rfl) ⟨1497206, by rfl⟩ : syracuseStep 7985101 = 2994413) B2994413
theorem B10646801 : Blo 2101435 10646801 := bstep (se 2 (by rfl) ⟨3992550, by rfl⟩ : syracuseStep 10646801 = 7985101) B7985101
theorem B7097867 : Blo 2101435 7097867 := bstep (se 1 (by rfl) ⟨5323400, by rfl⟩ : syracuseStep 7097867 = 10646801) B10646801
theorem B4731911 : Blo 2101435 4731911 := bstep (se 1 (by rfl) ⟨3548933, by rfl⟩ : syracuseStep 4731911 = 7097867) B7097867
theorem B3154607 : Blo 2101435 3154607 := bstep (se 1 (by rfl) ⟨2365955, by rfl⟩ : syracuseStep 3154607 = 4731911) B4731911
theorem B2103071 : Blo 2101435 2103071 := bstep (se 1 (by rfl) ⟨1577303, by rfl⟩ : syracuseStep 2103071 = 3154607) B3154607
theorem B3154613 : Blo 2101435 3154613 := bbase (se 5 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 3154613 = 295745) (by norm_num)
theorem B2103075 : Blo 2101435 2103075 := bstep (se 1 (by rfl) ⟨1577306, by rfl⟩ : syracuseStep 2103075 = 3154613) B3154613
theorem B5323421 : Blo 2101435 5323421 := bbase (se 3 (by rfl) ⟨998141, by rfl⟩ : syracuseStep 5323421 = 1996283) (by norm_num)
theorem B3548947 : Blo 2101435 3548947 := bstep (se 1 (by rfl) ⟨2661710, by rfl⟩ : syracuseStep 3548947 = 5323421) B5323421
theorem B4731929 : Blo 2101435 4731929 := bstep (se 2 (by rfl) ⟨1774473, by rfl⟩ : syracuseStep 4731929 = 3548947) B3548947
theorem B3154619 : Blo 2101435 3154619 := bstep (se 1 (by rfl) ⟨2365964, by rfl⟩ : syracuseStep 3154619 = 4731929) B4731929
theorem B2103079 : Blo 2101435 2103079 := bstep (se 1 (by rfl) ⟨1577309, by rfl⟩ : syracuseStep 2103079 = 3154619) B3154619
theorem B2365969 : Blo 2101435 2365969 := bbase (se 2 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 2365969 = 1774477) (by norm_num)
theorem B3154625 : Blo 2101435 3154625 := bstep (se 2 (by rfl) ⟨1182984, by rfl⟩ : syracuseStep 3154625 = 2365969) B2365969
theorem B2103083 : Blo 2101435 2103083 := bstep (se 1 (by rfl) ⟨1577312, by rfl⟩ : syracuseStep 2103083 = 3154625) B3154625
theorem B3992581 : Blo 2101435 3992581 := bbase (se 4 (by rfl) ⟨374304, by rfl⟩ : syracuseStep 3992581 = 748609) (by norm_num)
theorem B5323441 : Blo 2101435 5323441 := bstep (se 2 (by rfl) ⟨1996290, by rfl⟩ : syracuseStep 5323441 = 3992581) B3992581
theorem B7097921 : Blo 2101435 7097921 := bstep (se 2 (by rfl) ⟨2661720, by rfl⟩ : syracuseStep 7097921 = 5323441) B5323441
theorem B4731947 : Blo 2101435 4731947 := bstep (se 1 (by rfl) ⟨3548960, by rfl⟩ : syracuseStep 4731947 = 7097921) B7097921
theorem B3154631 : Blo 2101435 3154631 := bstep (se 1 (by rfl) ⟨2365973, by rfl⟩ : syracuseStep 3154631 = 4731947) B4731947
theorem B2103087 : Blo 2101435 2103087 := bstep (se 1 (by rfl) ⟨1577315, by rfl⟩ : syracuseStep 2103087 = 3154631) B3154631
theorem B3154637 : Blo 2101435 3154637 := bbase (se 3 (by rfl) ⟨591494, by rfl⟩ : syracuseStep 3154637 = 1182989) (by norm_num)
theorem B2103091 : Blo 2101435 2103091 := bstep (se 1 (by rfl) ⟨1577318, by rfl⟩ : syracuseStep 2103091 = 3154637) B3154637
theorem B4731965 : Blo 2101435 4731965 := bbase (se 3 (by rfl) ⟨887243, by rfl⟩ : syracuseStep 4731965 = 1774487) (by norm_num)
theorem B3154643 : Blo 2101435 3154643 := bstep (se 1 (by rfl) ⟨2365982, by rfl⟩ : syracuseStep 3154643 = 4731965) B4731965
theorem B2103095 : Blo 2101435 2103095 := bstep (se 1 (by rfl) ⟨1577321, by rfl⟩ : syracuseStep 2103095 = 3154643) B3154643
theorem B3548981 : Blo 2101435 3548981 := bbase (se 5 (by rfl) ⟨166358, by rfl⟩ : syracuseStep 3548981 = 332717) (by norm_num)
theorem B2365987 : Blo 2101435 2365987 := bstep (se 1 (by rfl) ⟨1774490, by rfl⟩ : syracuseStep 2365987 = 3548981) B3548981
theorem B3154649 : Blo 2101435 3154649 := bstep (se 2 (by rfl) ⟨1182993, by rfl⟩ : syracuseStep 3154649 = 2365987) B2365987
theorem B2103099 : Blo 2101435 2103099 := bstep (se 1 (by rfl) ⟨1577324, by rfl⟩ : syracuseStep 2103099 = 3154649) B3154649
theorem B5988917 : Blo 2101435 5988917 := bbase (se 5 (by rfl) ⟨280730, by rfl⟩ : syracuseStep 5988917 = 561461) (by norm_num)
theorem B15970445 : Blo 2101435 15970445 := bstep (se 3 (by rfl) ⟨2994458, by rfl⟩ : syracuseStep 15970445 = 5988917) B5988917
theorem B10646963 : Blo 2101435 10646963 := bstep (se 1 (by rfl) ⟨7985222, by rfl⟩ : syracuseStep 10646963 = 15970445) B15970445
theorem B7097975 : Blo 2101435 7097975 := bstep (se 1 (by rfl) ⟨5323481, by rfl⟩ : syracuseStep 7097975 = 10646963) B10646963
theorem B4731983 : Blo 2101435 4731983 := bstep (se 1 (by rfl) ⟨3548987, by rfl⟩ : syracuseStep 4731983 = 7097975) B7097975
theorem B3154655 : Blo 2101435 3154655 := bstep (se 1 (by rfl) ⟨2365991, by rfl⟩ : syracuseStep 3154655 = 4731983) B4731983
theorem B2103103 : Blo 2101435 2103103 := bstep (se 1 (by rfl) ⟨1577327, by rfl⟩ : syracuseStep 2103103 = 3154655) B3154655
theorem B3154661 : Blo 2101435 3154661 := bbase (se 4 (by rfl) ⟨295749, by rfl⟩ : syracuseStep 3154661 = 591499) (by norm_num)
theorem B2103107 : Blo 2101435 2103107 := bstep (se 1 (by rfl) ⟨1577330, by rfl⟩ : syracuseStep 2103107 = 3154661) B3154661
theorem B2245853 : Blo 2101435 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B5988941 : Blo 2101435 5988941 := bstep (se 3 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 5988941 = 2245853) B2245853
theorem B3992627 : Blo 2101435 3992627 := bstep (se 1 (by rfl) ⟨2994470, by rfl⟩ : syracuseStep 3992627 = 5988941) B5988941
theorem B2661751 : Blo 2101435 2661751 := bstep (se 1 (by rfl) ⟨1996313, by rfl⟩ : syracuseStep 2661751 = 3992627) B3992627
theorem B3549001 : Blo 2101435 3549001 := bstep (se 2 (by rfl) ⟨1330875, by rfl⟩ : syracuseStep 3549001 = 2661751) B2661751
theorem B4732001 : Blo 2101435 4732001 := bstep (se 2 (by rfl) ⟨1774500, by rfl⟩ : syracuseStep 4732001 = 3549001) B3549001
theorem B3154667 : Blo 2101435 3154667 := bstep (se 1 (by rfl) ⟨2366000, by rfl⟩ : syracuseStep 3154667 = 4732001) B4732001
theorem B2103111 : Blo 2101435 2103111 := bstep (se 1 (by rfl) ⟨1577333, by rfl⟩ : syracuseStep 2103111 = 3154667) B3154667
theorem B2366005 : Blo 2101435 2366005 := bbase (se 5 (by rfl) ⟨110906, by rfl⟩ : syracuseStep 2366005 = 221813) (by norm_num)
theorem B3154673 : Blo 2101435 3154673 := bstep (se 2 (by rfl) ⟨1183002, by rfl⟩ : syracuseStep 3154673 = 2366005) B2366005
theorem B2103115 : Blo 2101435 2103115 := bstep (se 1 (by rfl) ⟨1577336, by rfl⟩ : syracuseStep 2103115 = 3154673) B3154673
theorem B2661761 : Blo 2101435 2661761 := bbase (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) (by norm_num)
theorem B7098029 : Blo 2101435 7098029 := bstep (se 3 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 7098029 = 2661761) B2661761
theorem B4732019 : Blo 2101435 4732019 := bstep (se 1 (by rfl) ⟨3549014, by rfl⟩ : syracuseStep 4732019 = 7098029) B7098029
theorem B3154679 : Blo 2101435 3154679 := bstep (se 1 (by rfl) ⟨2366009, by rfl⟩ : syracuseStep 3154679 = 4732019) B4732019
theorem B2103119 : Blo 2101435 2103119 := bstep (se 1 (by rfl) ⟨1577339, by rfl⟩ : syracuseStep 2103119 = 3154679) B3154679
theorem B3154685 : Blo 2101435 3154685 := bbase (se 3 (by rfl) ⟨591503, by rfl⟩ : syracuseStep 3154685 = 1183007) (by norm_num)
theorem B2103123 : Blo 2101435 2103123 := bstep (se 1 (by rfl) ⟨1577342, by rfl⟩ : syracuseStep 2103123 = 3154685) B3154685
theorem B4732037 : Blo 2101435 4732037 := bbase (se 4 (by rfl) ⟨443628, by rfl⟩ : syracuseStep 4732037 = 887257) (by norm_num)
theorem B3154691 : Blo 2101435 3154691 := bstep (se 1 (by rfl) ⟨2366018, by rfl⟩ : syracuseStep 3154691 = 4732037) B4732037
theorem B2103127 : Blo 2101435 2103127 := bstep (se 1 (by rfl) ⟨1577345, by rfl⟩ : syracuseStep 2103127 = 3154691) B3154691
theorem B4491749 : Blo 2101435 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B2994499 : Blo 2101435 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B3992665 : Blo 2101435 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B5323553 : Blo 2101435 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B3549035 : Blo 2101435 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B2366023 : Blo 2101435 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B3154697 : Blo 2101435 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B2103131 : Blo 2101435 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B10647125 : Blo 2101435 10647125 := bbase (se 8 (by rfl) ⟨62385, by rfl⟩ : syracuseStep 10647125 = 124771) (by norm_num)
theorem B7098083 : Blo 2101435 7098083 := bstep (se 1 (by rfl) ⟨5323562, by rfl⟩ : syracuseStep 7098083 = 10647125) B10647125
theorem B4732055 : Blo 2101435 4732055 := bstep (se 1 (by rfl) ⟨3549041, by rfl⟩ : syracuseStep 4732055 = 7098083) B7098083
theorem B3154703 : Blo 2101435 3154703 := bstep (se 1 (by rfl) ⟨2366027, by rfl⟩ : syracuseStep 3154703 = 4732055) B4732055
theorem B2103135 : Blo 2101435 2103135 := bstep (se 1 (by rfl) ⟨1577351, by rfl⟩ : syracuseStep 2103135 = 3154703) B3154703
theorem B3154709 : Blo 2101435 3154709 := bbase (se 6 (by rfl) ⟨73938, by rfl⟩ : syracuseStep 3154709 = 147877) (by norm_num)
theorem B2103139 : Blo 2101435 2103139 := bstep (se 1 (by rfl) ⟨1577354, by rfl⟩ : syracuseStep 2103139 = 3154709) B3154709
theorem B12791029 : Blo 2101435 12791029 := bbase (se 5 (by rfl) ⟨599579, by rfl⟩ : syracuseStep 12791029 = 1199159) (by norm_num)
theorem B17054705 : Blo 2101435 17054705 := bstep (se 2 (by rfl) ⟨6395514, by rfl⟩ : syracuseStep 17054705 = 12791029) B12791029
theorem B11369803 : Blo 2101435 11369803 := bstep (se 1 (by rfl) ⟨8527352, by rfl⟩ : syracuseStep 11369803 = 17054705) B17054705
theorem B15159737 : Blo 2101435 15159737 := bstep (se 2 (by rfl) ⟨5684901, by rfl⟩ : syracuseStep 15159737 = 11369803) B11369803
theorem B40425965 : Blo 2101435 40425965 := bstep (se 3 (by rfl) ⟨7579868, by rfl⟩ : syracuseStep 40425965 = 15159737) B15159737
theorem B26950643 : Blo 2101435 26950643 := bstep (se 1 (by rfl) ⟨20212982, by rfl⟩ : syracuseStep 26950643 = 40425965) B40425965
theorem B17967095 : Blo 2101435 17967095 := bstep (se 1 (by rfl) ⟨13475321, by rfl⟩ : syracuseStep 17967095 = 26950643) B26950643
theorem B11978063 : Blo 2101435 11978063 := bstep (se 1 (by rfl) ⟨8983547, by rfl⟩ : syracuseStep 11978063 = 17967095) B17967095
theorem B7985375 : Blo 2101435 7985375 := bstep (se 1 (by rfl) ⟨5989031, by rfl⟩ : syracuseStep 7985375 = 11978063) B11978063
theorem B5323583 : Blo 2101435 5323583 := bstep (se 1 (by rfl) ⟨3992687, by rfl⟩ : syracuseStep 5323583 = 7985375) B7985375
theorem B3549055 : Blo 2101435 3549055 := bstep (se 1 (by rfl) ⟨2661791, by rfl⟩ : syracuseStep 3549055 = 5323583) B5323583
theorem B4732073 : Blo 2101435 4732073 := bstep (se 2 (by rfl) ⟨1774527, by rfl⟩ : syracuseStep 4732073 = 3549055) B3549055
theorem B3154715 : Blo 2101435 3154715 := bstep (se 1 (by rfl) ⟨2366036, by rfl⟩ : syracuseStep 3154715 = 4732073) B4732073
theorem B2103143 : Blo 2101435 2103143 := bstep (se 1 (by rfl) ⟨1577357, by rfl⟩ : syracuseStep 2103143 = 3154715) B3154715
theorem B2366041 : Blo 2101435 2366041 := bbase (se 2 (by rfl) ⟨887265, by rfl⟩ : syracuseStep 2366041 = 1774531) (by norm_num)
theorem B3154721 : Blo 2101435 3154721 := bstep (se 2 (by rfl) ⟨1183020, by rfl⟩ : syracuseStep 3154721 = 2366041) B2366041
theorem B2103147 : Blo 2101435 2103147 := bstep (se 1 (by rfl) ⟨1577360, by rfl⟩ : syracuseStep 2103147 = 3154721) B3154721
theorem B15159797 : Blo 2101435 15159797 := bbase (se 5 (by rfl) ⟨710615, by rfl⟩ : syracuseStep 15159797 = 1421231) (by norm_num)
theorem B10106531 : Blo 2101435 10106531 := bstep (se 1 (by rfl) ⟨7579898, by rfl⟩ : syracuseStep 10106531 = 15159797) B15159797
theorem B6737687 : Blo 2101435 6737687 := bstep (se 1 (by rfl) ⟨5053265, by rfl⟩ : syracuseStep 6737687 = 10106531) B10106531
theorem B4491791 : Blo 2101435 4491791 := bstep (se 1 (by rfl) ⟨3368843, by rfl⟩ : syracuseStep 4491791 = 6737687) B6737687
theorem B2994527 : Blo 2101435 2994527 := bstep (se 1 (by rfl) ⟨2245895, by rfl⟩ : syracuseStep 2994527 = 4491791) B4491791
theorem B7985405 : Blo 2101435 7985405 := bstep (se 3 (by rfl) ⟨1497263, by rfl⟩ : syracuseStep 7985405 = 2994527) B2994527
theorem B5323603 : Blo 2101435 5323603 := bstep (se 1 (by rfl) ⟨3992702, by rfl⟩ : syracuseStep 5323603 = 7985405) B7985405
theorem B7098137 : Blo 2101435 7098137 := bstep (se 2 (by rfl) ⟨2661801, by rfl⟩ : syracuseStep 7098137 = 5323603) B5323603
theorem B4732091 : Blo 2101435 4732091 := bstep (se 1 (by rfl) ⟨3549068, by rfl⟩ : syracuseStep 4732091 = 7098137) B7098137
theorem B3154727 : Blo 2101435 3154727 := bstep (se 1 (by rfl) ⟨2366045, by rfl⟩ : syracuseStep 3154727 = 4732091) B4732091
theorem B2103151 : Blo 2101435 2103151 := bstep (se 1 (by rfl) ⟨1577363, by rfl⟩ : syracuseStep 2103151 = 3154727) B3154727
theorem B3154733 : Blo 2101435 3154733 := bbase (se 3 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 3154733 = 1183025) (by norm_num)
theorem B2103155 : Blo 2101435 2103155 := bstep (se 1 (by rfl) ⟨1577366, by rfl⟩ : syracuseStep 2103155 = 3154733) B3154733
theorem B4732109 : Blo 2101435 4732109 := bbase (se 3 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 4732109 = 1774541) (by norm_num)
theorem B3154739 : Blo 2101435 3154739 := bstep (se 1 (by rfl) ⟨2366054, by rfl⟩ : syracuseStep 3154739 = 4732109) B4732109
theorem B2103159 : Blo 2101435 2103159 := bstep (se 1 (by rfl) ⟨1577369, by rfl⟩ : syracuseStep 2103159 = 3154739) B3154739
theorem B2661817 : Blo 2101435 2661817 := bbase (se 2 (by rfl) ⟨998181, by rfl⟩ : syracuseStep 2661817 = 1996363) (by norm_num)
theorem B3549089 : Blo 2101435 3549089 := bstep (se 2 (by rfl) ⟨1330908, by rfl⟩ : syracuseStep 3549089 = 2661817) B2661817
theorem B2366059 : Blo 2101435 2366059 := bstep (se 1 (by rfl) ⟨1774544, by rfl⟩ : syracuseStep 2366059 = 3549089) B3549089
theorem B3154745 : Blo 2101435 3154745 := bstep (se 2 (by rfl) ⟨1183029, by rfl⟩ : syracuseStep 3154745 = 2366059) B2366059
theorem B2103163 : Blo 2101435 2103163 := bstep (se 1 (by rfl) ⟨1577372, by rfl⟩ : syracuseStep 2103163 = 3154745) B3154745
theorem B4263725 : Blo 2101435 4263725 := bbase (se 3 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 4263725 = 1598897) (by norm_num)
theorem B11369933 : Blo 2101435 11369933 := bstep (se 3 (by rfl) ⟨2131862, by rfl⟩ : syracuseStep 11369933 = 4263725) B4263725
theorem B7579955 : Blo 2101435 7579955 := bstep (se 1 (by rfl) ⟨5684966, by rfl⟩ : syracuseStep 7579955 = 11369933) B11369933
theorem B5053303 : Blo 2101435 5053303 := bstep (se 1 (by rfl) ⟨3789977, by rfl⟩ : syracuseStep 5053303 = 7579955) B7579955
theorem B6737737 : Blo 2101435 6737737 := bstep (se 2 (by rfl) ⟨2526651, by rfl⟩ : syracuseStep 6737737 = 5053303) B5053303
theorem B8983649 : Blo 2101435 8983649 := bstep (se 2 (by rfl) ⟨3368868, by rfl⟩ : syracuseStep 8983649 = 6737737) B6737737
theorem B23956397 : Blo 2101435 23956397 := bstep (se 3 (by rfl) ⟨4491824, by rfl⟩ : syracuseStep 23956397 = 8983649) B8983649
theorem B15970931 : Blo 2101435 15970931 := bstep (se 1 (by rfl) ⟨11978198, by rfl⟩ : syracuseStep 15970931 = 23956397) B23956397
theorem B10647287 : Blo 2101435 10647287 := bstep (se 1 (by rfl) ⟨7985465, by rfl⟩ : syracuseStep 10647287 = 15970931) B15970931
theorem B7098191 : Blo 2101435 7098191 := bstep (se 1 (by rfl) ⟨5323643, by rfl⟩ : syracuseStep 7098191 = 10647287) B10647287
theorem B4732127 : Blo 2101435 4732127 := bstep (se 1 (by rfl) ⟨3549095, by rfl⟩ : syracuseStep 4732127 = 7098191) B7098191
theorem B3154751 : Blo 2101435 3154751 := bstep (se 1 (by rfl) ⟨2366063, by rfl⟩ : syracuseStep 3154751 = 4732127) B4732127
theorem B2103167 : Blo 2101435 2103167 := bstep (se 1 (by rfl) ⟨1577375, by rfl⟩ : syracuseStep 2103167 = 3154751) B3154751
theorem B3154757 : Blo 2101435 3154757 := bbase (se 4 (by rfl) ⟨295758, by rfl⟩ : syracuseStep 3154757 = 591517) (by norm_num)
theorem B2103171 : Blo 2101435 2103171 := bstep (se 1 (by rfl) ⟨1577378, by rfl⟩ : syracuseStep 2103171 = 3154757) B3154757
theorem B3549109 : Blo 2101435 3549109 := bbase (se 5 (by rfl) ⟨166364, by rfl⟩ : syracuseStep 3549109 = 332729) (by norm_num)
theorem B4732145 : Blo 2101435 4732145 := bstep (se 2 (by rfl) ⟨1774554, by rfl⟩ : syracuseStep 4732145 = 3549109) B3549109
theorem B3154763 : Blo 2101435 3154763 := bstep (se 1 (by rfl) ⟨2366072, by rfl⟩ : syracuseStep 3154763 = 4732145) B4732145
theorem B2103175 : Blo 2101435 2103175 := bstep (se 1 (by rfl) ⟨1577381, by rfl⟩ : syracuseStep 2103175 = 3154763) B3154763
theorem B2366077 : Blo 2101435 2366077 := bbase (se 3 (by rfl) ⟨443639, by rfl⟩ : syracuseStep 2366077 = 887279) (by norm_num)
theorem B3154769 : Blo 2101435 3154769 := bstep (se 2 (by rfl) ⟨1183038, by rfl⟩ : syracuseStep 3154769 = 2366077) B2366077
theorem B2103179 : Blo 2101435 2103179 := bstep (se 1 (by rfl) ⟨1577384, by rfl⟩ : syracuseStep 2103179 = 3154769) B3154769
theorem B7098245 : Blo 2101435 7098245 := bbase (se 4 (by rfl) ⟨665460, by rfl⟩ : syracuseStep 7098245 = 1330921) (by norm_num)
theorem B4732163 : Blo 2101435 4732163 := bstep (se 1 (by rfl) ⟨3549122, by rfl⟩ : syracuseStep 4732163 = 7098245) B7098245
theorem B3154775 : Blo 2101435 3154775 := bstep (se 1 (by rfl) ⟨2366081, by rfl⟩ : syracuseStep 3154775 = 4732163) B4732163
theorem B2103183 : Blo 2101435 2103183 := bstep (se 1 (by rfl) ⟨1577387, by rfl⟩ : syracuseStep 2103183 = 3154775) B3154775
theorem B3154781 : Blo 2101435 3154781 := bbase (se 3 (by rfl) ⟨591521, by rfl⟩ : syracuseStep 3154781 = 1183043) (by norm_num)
theorem B2103187 : Blo 2101435 2103187 := bstep (se 1 (by rfl) ⟨1577390, by rfl⟩ : syracuseStep 2103187 = 3154781) B3154781
theorem B4732181 : Blo 2101435 4732181 := bbase (se 6 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 4732181 = 221821) (by norm_num)
theorem B3154787 : Blo 2101435 3154787 := bstep (se 1 (by rfl) ⟨2366090, by rfl⟩ : syracuseStep 3154787 = 4732181) B4732181
theorem B2103191 : Blo 2101435 2103191 := bstep (se 1 (by rfl) ⟨1577393, by rfl⟩ : syracuseStep 2103191 = 3154787) B3154787
theorem B7985573 : Blo 2101435 7985573 := bbase (se 4 (by rfl) ⟨748647, by rfl⟩ : syracuseStep 7985573 = 1497295) (by norm_num)
theorem B5323715 : Blo 2101435 5323715 := bstep (se 1 (by rfl) ⟨3992786, by rfl⟩ : syracuseStep 5323715 = 7985573) B7985573
theorem B3549143 : Blo 2101435 3549143 := bstep (se 1 (by rfl) ⟨2661857, by rfl⟩ : syracuseStep 3549143 = 5323715) B5323715
theorem B2366095 : Blo 2101435 2366095 := bstep (se 1 (by rfl) ⟨1774571, by rfl⟩ : syracuseStep 2366095 = 3549143) B3549143
theorem B3154793 : Blo 2101435 3154793 := bstep (se 2 (by rfl) ⟨1183047, by rfl⟩ : syracuseStep 3154793 = 2366095) B2366095
theorem B2103195 : Blo 2101435 2103195 := bstep (se 1 (by rfl) ⟨1577396, by rfl⟩ : syracuseStep 2103195 = 3154793) B3154793
theorem B4491893 : Blo 2101435 4491893 := bbase (se 5 (by rfl) ⟨210557, by rfl⟩ : syracuseStep 4491893 = 421115) (by norm_num)
theorem B11978381 : Blo 2101435 11978381 := bstep (se 3 (by rfl) ⟨2245946, by rfl⟩ : syracuseStep 11978381 = 4491893) B4491893
theorem B7985587 : Blo 2101435 7985587 := bstep (se 1 (by rfl) ⟨5989190, by rfl⟩ : syracuseStep 7985587 = 11978381) B11978381
theorem B10647449 : Blo 2101435 10647449 := bstep (se 2 (by rfl) ⟨3992793, by rfl⟩ : syracuseStep 10647449 = 7985587) B7985587
theorem B7098299 : Blo 2101435 7098299 := bstep (se 1 (by rfl) ⟨5323724, by rfl⟩ : syracuseStep 7098299 = 10647449) B10647449
theorem B4732199 : Blo 2101435 4732199 := bstep (se 1 (by rfl) ⟨3549149, by rfl⟩ : syracuseStep 4732199 = 7098299) B7098299
theorem B3154799 : Blo 2101435 3154799 := bstep (se 1 (by rfl) ⟨2366099, by rfl⟩ : syracuseStep 3154799 = 4732199) B4732199
theorem B2103199 : Blo 2101435 2103199 := bstep (se 1 (by rfl) ⟨1577399, by rfl⟩ : syracuseStep 2103199 = 3154799) B3154799
theorem B3154805 : Blo 2101435 3154805 := bbase (se 5 (by rfl) ⟨147881, by rfl⟩ : syracuseStep 3154805 = 295763) (by norm_num)
theorem B2103203 : Blo 2101435 2103203 := bstep (se 1 (by rfl) ⟨1577402, by rfl⟩ : syracuseStep 2103203 = 3154805) B3154805
theorem B7580101 : Blo 2101435 7580101 := bbase (se 4 (by rfl) ⟨710634, by rfl⟩ : syracuseStep 7580101 = 1421269) (by norm_num)
theorem B10106801 : Blo 2101435 10106801 := bstep (se 2 (by rfl) ⟨3790050, by rfl⟩ : syracuseStep 10106801 = 7580101) B7580101
theorem B6737867 : Blo 2101435 6737867 := bstep (se 1 (by rfl) ⟨5053400, by rfl⟩ : syracuseStep 6737867 = 10106801) B10106801
theorem B4491911 : Blo 2101435 4491911 := bstep (se 1 (by rfl) ⟨3368933, by rfl⟩ : syracuseStep 4491911 = 6737867) B6737867
theorem B2994607 : Blo 2101435 2994607 := bstep (se 1 (by rfl) ⟨2245955, by rfl⟩ : syracuseStep 2994607 = 4491911) B4491911
theorem B3992809 : Blo 2101435 3992809 := bstep (se 2 (by rfl) ⟨1497303, by rfl⟩ : syracuseStep 3992809 = 2994607) B2994607
theorem B5323745 : Blo 2101435 5323745 := bstep (se 2 (by rfl) ⟨1996404, by rfl⟩ : syracuseStep 5323745 = 3992809) B3992809
theorem B3549163 : Blo 2101435 3549163 := bstep (se 1 (by rfl) ⟨2661872, by rfl⟩ : syracuseStep 3549163 = 5323745) B5323745
theorem B4732217 : Blo 2101435 4732217 := bstep (se 2 (by rfl) ⟨1774581, by rfl⟩ : syracuseStep 4732217 = 3549163) B3549163
theorem B3154811 : Blo 2101435 3154811 := bstep (se 1 (by rfl) ⟨2366108, by rfl⟩ : syracuseStep 3154811 = 4732217) B4732217
theorem B2103207 : Blo 2101435 2103207 := bstep (se 1 (by rfl) ⟨1577405, by rfl⟩ : syracuseStep 2103207 = 3154811) B3154811
theorem B2366113 : Blo 2101435 2366113 := bbase (se 2 (by rfl) ⟨887292, by rfl⟩ : syracuseStep 2366113 = 1774585) (by norm_num)
theorem B3154817 : Blo 2101435 3154817 := bstep (se 2 (by rfl) ⟨1183056, by rfl⟩ : syracuseStep 3154817 = 2366113) B2366113
theorem B2103211 : Blo 2101435 2103211 := bstep (se 1 (by rfl) ⟨1577408, by rfl⟩ : syracuseStep 2103211 = 3154817) B3154817
theorem B5323765 : Blo 2101435 5323765 := bbase (se 5 (by rfl) ⟨249551, by rfl⟩ : syracuseStep 5323765 = 499103) (by norm_num)
theorem B7098353 : Blo 2101435 7098353 := bstep (se 2 (by rfl) ⟨2661882, by rfl⟩ : syracuseStep 7098353 = 5323765) B5323765
theorem B4732235 : Blo 2101435 4732235 := bstep (se 1 (by rfl) ⟨3549176, by rfl⟩ : syracuseStep 4732235 = 7098353) B7098353
theorem B3154823 : Blo 2101435 3154823 := bstep (se 1 (by rfl) ⟨2366117, by rfl⟩ : syracuseStep 3154823 = 4732235) B4732235
theorem B2103215 : Blo 2101435 2103215 := bstep (se 1 (by rfl) ⟨1577411, by rfl⟩ : syracuseStep 2103215 = 3154823) B3154823
theorem B3154829 : Blo 2101435 3154829 := bbase (se 3 (by rfl) ⟨591530, by rfl⟩ : syracuseStep 3154829 = 1183061) (by norm_num)
theorem B2103219 : Blo 2101435 2103219 := bstep (se 1 (by rfl) ⟨1577414, by rfl⟩ : syracuseStep 2103219 = 3154829) B3154829
theorem B4732253 : Blo 2101435 4732253 := bbase (se 3 (by rfl) ⟨887297, by rfl⟩ : syracuseStep 4732253 = 1774595) (by norm_num)
theorem B3154835 : Blo 2101435 3154835 := bstep (se 1 (by rfl) ⟨2366126, by rfl⟩ : syracuseStep 3154835 = 4732253) B4732253
theorem B2103223 : Blo 2101435 2103223 := bstep (se 1 (by rfl) ⟨1577417, by rfl⟩ : syracuseStep 2103223 = 3154835) B3154835
theorem B3549197 : Blo 2101435 3549197 := bbase (se 3 (by rfl) ⟨665474, by rfl⟩ : syracuseStep 3549197 = 1330949) (by norm_num)
theorem B2366131 : Blo 2101435 2366131 := bstep (se 1 (by rfl) ⟨1774598, by rfl⟩ : syracuseStep 2366131 = 3549197) B3549197
theorem B3154841 : Blo 2101435 3154841 := bstep (se 2 (by rfl) ⟨1183065, by rfl⟩ : syracuseStep 3154841 = 2366131) B2366131
theorem B2103227 : Blo 2101435 2103227 := bstep (se 1 (by rfl) ⟨1577420, by rfl⟩ : syracuseStep 2103227 = 3154841) B3154841
theorem B3790093 : Blo 2101435 3790093 := bbase (se 3 (by rfl) ⟨710642, by rfl⟩ : syracuseStep 3790093 = 1421285) (by norm_num)
theorem B5053457 : Blo 2101435 5053457 := bstep (se 2 (by rfl) ⟨1895046, by rfl⟩ : syracuseStep 5053457 = 3790093) B3790093
theorem B3368971 : Blo 2101435 3368971 := bstep (se 1 (by rfl) ⟨2526728, by rfl⟩ : syracuseStep 3368971 = 5053457) B5053457
theorem B17967845 : Blo 2101435 17967845 := bstep (se 4 (by rfl) ⟨1684485, by rfl⟩ : syracuseStep 17967845 = 3368971) B3368971
theorem B11978563 : Blo 2101435 11978563 := bstep (se 1 (by rfl) ⟨8983922, by rfl⟩ : syracuseStep 11978563 = 17967845) B17967845
theorem B15971417 : Blo 2101435 15971417 := bstep (se 2 (by rfl) ⟨5989281, by rfl⟩ : syracuseStep 15971417 = 11978563) B11978563
theorem B10647611 : Blo 2101435 10647611 := bstep (se 1 (by rfl) ⟨7985708, by rfl⟩ : syracuseStep 10647611 = 15971417) B15971417
theorem B7098407 : Blo 2101435 7098407 := bstep (se 1 (by rfl) ⟨5323805, by rfl⟩ : syracuseStep 7098407 = 10647611) B10647611
theorem B4732271 : Blo 2101435 4732271 := bstep (se 1 (by rfl) ⟨3549203, by rfl⟩ : syracuseStep 4732271 = 7098407) B7098407
theorem B3154847 : Blo 2101435 3154847 := bstep (se 1 (by rfl) ⟨2366135, by rfl⟩ : syracuseStep 3154847 = 4732271) B4732271
theorem B2103231 : Blo 2101435 2103231 := bstep (se 1 (by rfl) ⟨1577423, by rfl⟩ : syracuseStep 2103231 = 3154847) B3154847
theorem B3154853 : Blo 2101435 3154853 := bbase (se 4 (by rfl) ⟨295767, by rfl⟩ : syracuseStep 3154853 = 591535) (by norm_num)
theorem B2103235 : Blo 2101435 2103235 := bstep (se 1 (by rfl) ⟨1577426, by rfl⟩ : syracuseStep 2103235 = 3154853) B3154853
theorem B2661913 : Blo 2101435 2661913 := bbase (se 2 (by rfl) ⟨998217, by rfl⟩ : syracuseStep 2661913 = 1996435) (by norm_num)
theorem B3549217 : Blo 2101435 3549217 := bstep (se 2 (by rfl) ⟨1330956, by rfl⟩ : syracuseStep 3549217 = 2661913) B2661913
theorem B4732289 : Blo 2101435 4732289 := bstep (se 2 (by rfl) ⟨1774608, by rfl⟩ : syracuseStep 4732289 = 3549217) B3549217
theorem B3154859 : Blo 2101435 3154859 := bstep (se 1 (by rfl) ⟨2366144, by rfl⟩ : syracuseStep 3154859 = 4732289) B4732289
theorem B2103239 : Blo 2101435 2103239 := bstep (se 1 (by rfl) ⟨1577429, by rfl⟩ : syracuseStep 2103239 = 3154859) B3154859
theorem B2366149 : Blo 2101435 2366149 := bbase (se 4 (by rfl) ⟨221826, by rfl⟩ : syracuseStep 2366149 = 443653) (by norm_num)
theorem B3154865 : Blo 2101435 3154865 := bstep (se 2 (by rfl) ⟨1183074, by rfl⟩ : syracuseStep 3154865 = 2366149) B2366149
theorem B2103243 : Blo 2101435 2103243 := bstep (se 1 (by rfl) ⟨1577432, by rfl⟩ : syracuseStep 2103243 = 3154865) B3154865
theorem B3992885 : Blo 2101435 3992885 := bbase (se 5 (by rfl) ⟨187166, by rfl⟩ : syracuseStep 3992885 = 374333) (by norm_num)
theorem B2661923 : Blo 2101435 2661923 := bstep (se 1 (by rfl) ⟨1996442, by rfl⟩ : syracuseStep 2661923 = 3992885) B3992885
theorem B7098461 : Blo 2101435 7098461 := bstep (se 3 (by rfl) ⟨1330961, by rfl⟩ : syracuseStep 7098461 = 2661923) B2661923
theorem B4732307 : Blo 2101435 4732307 := bstep (se 1 (by rfl) ⟨3549230, by rfl⟩ : syracuseStep 4732307 = 7098461) B7098461
theorem B3154871 : Blo 2101435 3154871 := bstep (se 1 (by rfl) ⟨2366153, by rfl⟩ : syracuseStep 3154871 = 4732307) B4732307
theorem B2103247 : Blo 2101435 2103247 := bstep (se 1 (by rfl) ⟨1577435, by rfl⟩ : syracuseStep 2103247 = 3154871) B3154871
theorem B3154877 : Blo 2101435 3154877 := bbase (se 3 (by rfl) ⟨591539, by rfl⟩ : syracuseStep 3154877 = 1183079) (by norm_num)
theorem B2103251 : Blo 2101435 2103251 := bstep (se 1 (by rfl) ⟨1577438, by rfl⟩ : syracuseStep 2103251 = 3154877) B3154877
theorem B4732325 : Blo 2101435 4732325 := bbase (se 4 (by rfl) ⟨443655, by rfl⟩ : syracuseStep 4732325 = 887311) (by norm_num)
theorem B3154883 : Blo 2101435 3154883 := bstep (se 1 (by rfl) ⟨2366162, by rfl⟩ : syracuseStep 3154883 = 4732325) B4732325
theorem B2103255 : Blo 2101435 2103255 := bstep (se 1 (by rfl) ⟨1577441, by rfl⟩ : syracuseStep 2103255 = 3154883) B3154883
theorem B5323877 : Blo 2101435 5323877 := bbase (se 4 (by rfl) ⟨499113, by rfl⟩ : syracuseStep 5323877 = 998227) (by norm_num)
theorem B3549251 : Blo 2101435 3549251 := bstep (se 1 (by rfl) ⟨2661938, by rfl⟩ : syracuseStep 3549251 = 5323877) B5323877
theorem B2366167 : Blo 2101435 2366167 := bstep (se 1 (by rfl) ⟨1774625, by rfl⟩ : syracuseStep 2366167 = 3549251) B3549251
theorem B3154889 : Blo 2101435 3154889 := bstep (se 2 (by rfl) ⟨1183083, by rfl⟩ : syracuseStep 3154889 = 2366167) B2366167
theorem B2103259 : Blo 2101435 2103259 := bstep (se 1 (by rfl) ⟨1577444, by rfl⟩ : syracuseStep 2103259 = 3154889) B3154889
theorem B21052853 : Blo 2101435 21052853 := bbase (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) (by norm_num)
theorem B14035235 : Blo 2101435 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B37427293 : Blo 2101435 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B49903057 : Blo 2101435 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B66537409 : Blo 2101435 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B88716545 : Blo 2101435 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B59144363 : Blo 2101435 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B39429575 : Blo 2101435 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B26286383 : Blo 2101435 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B17524255 : Blo 2101435 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B23365673 : Blo 2101435 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B15577115 : Blo 2101435 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B41538973 : Blo 2101435 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B55385297 : Blo 2101435 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B36923531 : Blo 2101435 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B98462749 : Blo 2101435 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B131283665 : Blo 2101435 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B87522443 : Blo 2101435 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B58348295 : Blo 2101435 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B38898863 : Blo 2101435 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B25932575 : Blo 2101435 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B69153533 : Blo 2101435 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B46102355 : Blo 2101435 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B30734903 : Blo 2101435 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B20489935 : Blo 2101435 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B27319913 : Blo 2101435 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B18213275 : Blo 2101435 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B12142183 : Blo 2101435 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B16189577 : Blo 2101435 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B10793051 : Blo 2101435 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B7195367 : Blo 2101435 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B4796911 : Blo 2101435 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B25583525 : Blo 2101435 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B17055683 : Blo 2101435 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B11370455 : Blo 2101435 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B7580303 : Blo 2101435 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B5053535 : Blo 2101435 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B3369023 : Blo 2101435 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B2246015 : Blo 2101435 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B5989373 : Blo 2101435 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B3992915 : Blo 2101435 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B10647773 : Blo 2101435 10647773 := bstep (se 3 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 10647773 = 3992915) B3992915
theorem B7098515 : Blo 2101435 7098515 := bstep (se 1 (by rfl) ⟨5323886, by rfl⟩ : syracuseStep 7098515 = 10647773) B10647773
theorem B4732343 : Blo 2101435 4732343 := bstep (se 1 (by rfl) ⟨3549257, by rfl⟩ : syracuseStep 4732343 = 7098515) B7098515
theorem B3154895 : Blo 2101435 3154895 := bstep (se 1 (by rfl) ⟨2366171, by rfl⟩ : syracuseStep 3154895 = 4732343) B4732343
theorem B2103263 : Blo 2101435 2103263 := bstep (se 1 (by rfl) ⟨1577447, by rfl⟩ : syracuseStep 2103263 = 3154895) B3154895
theorem B3154901 : Blo 2101435 3154901 := bbase (se 7 (by rfl) ⟨36971, by rfl⟩ : syracuseStep 3154901 = 73943) (by norm_num)
theorem B2103267 : Blo 2101435 2103267 := bstep (se 1 (by rfl) ⟨1577450, by rfl⟩ : syracuseStep 2103267 = 3154901) B3154901
theorem B7985861 : Blo 2101435 7985861 := bbase (se 4 (by rfl) ⟨748674, by rfl⟩ : syracuseStep 7985861 = 1497349) (by norm_num)
theorem B5323907 : Blo 2101435 5323907 := bstep (se 1 (by rfl) ⟨3992930, by rfl⟩ : syracuseStep 5323907 = 7985861) B7985861
theorem B3549271 : Blo 2101435 3549271 := bstep (se 1 (by rfl) ⟨2661953, by rfl⟩ : syracuseStep 3549271 = 5323907) B5323907
theorem B4732361 : Blo 2101435 4732361 := bstep (se 2 (by rfl) ⟨1774635, by rfl⟩ : syracuseStep 4732361 = 3549271) B3549271
theorem B3154907 : Blo 2101435 3154907 := bstep (se 1 (by rfl) ⟨2366180, by rfl⟩ : syracuseStep 3154907 = 4732361) B4732361
theorem B2103271 : Blo 2101435 2103271 := bstep (se 1 (by rfl) ⟨1577453, by rfl⟩ : syracuseStep 2103271 = 3154907) B3154907
theorem B2366185 : Blo 2101435 2366185 := bbase (se 2 (by rfl) ⟨887319, by rfl⟩ : syracuseStep 2366185 = 1774639) (by norm_num)
theorem B3154913 : Blo 2101435 3154913 := bstep (se 2 (by rfl) ⟨1183092, by rfl⟩ : syracuseStep 3154913 = 2366185) B2366185
theorem B2103275 : Blo 2101435 2103275 := bstep (se 1 (by rfl) ⟨1577456, by rfl⟩ : syracuseStep 2103275 = 3154913) B3154913
theorem B11978837 : Blo 2101435 11978837 := bbase (se 8 (by rfl) ⟨70188, by rfl⟩ : syracuseStep 11978837 = 140377) (by norm_num)
theorem B7985891 : Blo 2101435 7985891 := bstep (se 1 (by rfl) ⟨5989418, by rfl⟩ : syracuseStep 7985891 = 11978837) B11978837
theorem B5323927 : Blo 2101435 5323927 := bstep (se 1 (by rfl) ⟨3992945, by rfl⟩ : syracuseStep 5323927 = 7985891) B7985891
theorem B7098569 : Blo 2101435 7098569 := bstep (se 2 (by rfl) ⟨2661963, by rfl⟩ : syracuseStep 7098569 = 5323927) B5323927
theorem B4732379 : Blo 2101435 4732379 := bstep (se 1 (by rfl) ⟨3549284, by rfl⟩ : syracuseStep 4732379 = 7098569) B7098569
theorem B3154919 : Blo 2101435 3154919 := bstep (se 1 (by rfl) ⟨2366189, by rfl⟩ : syracuseStep 3154919 = 4732379) B4732379
theorem B2103279 : Blo 2101435 2103279 := bstep (se 1 (by rfl) ⟨1577459, by rfl⟩ : syracuseStep 2103279 = 3154919) B3154919
theorem B3154925 : Blo 2101435 3154925 := bbase (se 3 (by rfl) ⟨591548, by rfl⟩ : syracuseStep 3154925 = 1183097) (by norm_num)
theorem B2103283 : Blo 2101435 2103283 := bstep (se 1 (by rfl) ⟨1577462, by rfl⟩ : syracuseStep 2103283 = 3154925) B3154925
theorem B4732397 : Blo 2101435 4732397 := bbase (se 3 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 4732397 = 1774649) (by norm_num)
theorem B3154931 : Blo 2101435 3154931 := bstep (se 1 (by rfl) ⟨2366198, by rfl⟩ : syracuseStep 3154931 = 4732397) B4732397
theorem B2103287 : Blo 2101435 2103287 := bstep (se 1 (by rfl) ⟨1577465, by rfl⟩ : syracuseStep 2103287 = 3154931) B3154931
theorem B7580405 : Blo 2101435 7580405 := bbase (se 5 (by rfl) ⟨355331, by rfl⟩ : syracuseStep 7580405 = 710663) (by norm_num)
theorem B5053603 : Blo 2101435 5053603 := bstep (se 1 (by rfl) ⟨3790202, by rfl⟩ : syracuseStep 5053603 = 7580405) B7580405
theorem B6738137 : Blo 2101435 6738137 := bstep (se 2 (by rfl) ⟨2526801, by rfl⟩ : syracuseStep 6738137 = 5053603) B5053603
theorem B4492091 : Blo 2101435 4492091 := bstep (se 1 (by rfl) ⟨3369068, by rfl⟩ : syracuseStep 4492091 = 6738137) B6738137
theorem B2994727 : Blo 2101435 2994727 := bstep (se 1 (by rfl) ⟨2246045, by rfl⟩ : syracuseStep 2994727 = 4492091) B4492091
theorem B3992969 : Blo 2101435 3992969 := bstep (se 2 (by rfl) ⟨1497363, by rfl⟩ : syracuseStep 3992969 = 2994727) B2994727
theorem B2661979 : Blo 2101435 2661979 := bstep (se 1 (by rfl) ⟨1996484, by rfl⟩ : syracuseStep 2661979 = 3992969) B3992969
theorem B3549305 : Blo 2101435 3549305 := bstep (se 2 (by rfl) ⟨1330989, by rfl⟩ : syracuseStep 3549305 = 2661979) B2661979
theorem B2366203 : Blo 2101435 2366203 := bstep (se 1 (by rfl) ⟨1774652, by rfl⟩ : syracuseStep 2366203 = 3549305) B3549305
theorem B3154937 : Blo 2101435 3154937 := bstep (se 2 (by rfl) ⟨1183101, by rfl⟩ : syracuseStep 3154937 = 2366203) B2366203
theorem B2103291 : Blo 2101435 2103291 := bstep (se 1 (by rfl) ⟨1577468, by rfl⟩ : syracuseStep 2103291 = 3154937) B3154937
theorem B2772433 : Blo 2101435 2772433 := bbase (se 2 (by rfl) ⟨1039662, by rfl⟩ : syracuseStep 2772433 = 2079325) (by norm_num)
theorem B14786309 : Blo 2101435 14786309 := bstep (se 4 (by rfl) ⟨1386216, by rfl⟩ : syracuseStep 14786309 = 2772433) B2772433
theorem B9857539 : Blo 2101435 9857539 := bstep (se 1 (by rfl) ⟨7393154, by rfl⟩ : syracuseStep 9857539 = 14786309) B14786309
theorem B52573541 : Blo 2101435 52573541 := bstep (se 4 (by rfl) ⟨4928769, by rfl⟩ : syracuseStep 52573541 = 9857539) B9857539
theorem B140196109 : Blo 2101435 140196109 := bstep (se 3 (by rfl) ⟨26286770, by rfl⟩ : syracuseStep 140196109 = 52573541) B52573541
theorem B186928145 : Blo 2101435 186928145 := bstep (se 2 (by rfl) ⟨70098054, by rfl⟩ : syracuseStep 186928145 = 140196109) B140196109
theorem B124618763 : Blo 2101435 124618763 := bstep (se 1 (by rfl) ⟨93464072, by rfl⟩ : syracuseStep 124618763 = 186928145) B186928145
theorem B332316701 : Blo 2101435 332316701 := bstep (se 3 (by rfl) ⟨62309381, by rfl⟩ : syracuseStep 332316701 = 124618763) B124618763
theorem B221544467 : Blo 2101435 221544467 := bstep (se 1 (by rfl) ⟨166158350, by rfl⟩ : syracuseStep 221544467 = 332316701) B332316701
theorem B147696311 : Blo 2101435 147696311 := bstep (se 1 (by rfl) ⟨110772233, by rfl⟩ : syracuseStep 147696311 = 221544467) B221544467
theorem B98464207 : Blo 2101435 98464207 := bstep (se 1 (by rfl) ⟨73848155, by rfl⟩ : syracuseStep 98464207 = 147696311) B147696311
theorem B131285609 : Blo 2101435 131285609 := bstep (se 2 (by rfl) ⟨49232103, by rfl⟩ : syracuseStep 131285609 = 98464207) B98464207
theorem B87523739 : Blo 2101435 87523739 := bstep (se 1 (by rfl) ⟨65642804, by rfl⟩ : syracuseStep 87523739 = 131285609) B131285609
theorem B58349159 : Blo 2101435 58349159 := bstep (se 1 (by rfl) ⟨43761869, by rfl⟩ : syracuseStep 58349159 = 87523739) B87523739
theorem B38899439 : Blo 2101435 38899439 := bstep (se 1 (by rfl) ⟨29174579, by rfl⟩ : syracuseStep 38899439 = 58349159) B58349159
theorem B25932959 : Blo 2101435 25932959 := bstep (se 1 (by rfl) ⟨19449719, by rfl⟩ : syracuseStep 25932959 = 38899439) B38899439
theorem B17288639 : Blo 2101435 17288639 := bstep (se 1 (by rfl) ⟨12966479, by rfl⟩ : syracuseStep 17288639 = 25932959) B25932959
theorem B11525759 : Blo 2101435 11525759 := bstep (se 1 (by rfl) ⟨8644319, by rfl⟩ : syracuseStep 11525759 = 17288639) B17288639
theorem B7683839 : Blo 2101435 7683839 := bstep (se 1 (by rfl) ⟨5762879, by rfl⟩ : syracuseStep 7683839 = 11525759) B11525759
theorem B5122559 : Blo 2101435 5122559 := bstep (se 1 (by rfl) ⟨3841919, by rfl⟩ : syracuseStep 5122559 = 7683839) B7683839
theorem B3415039 : Blo 2101435 3415039 := bstep (se 1 (by rfl) ⟨2561279, by rfl⟩ : syracuseStep 3415039 = 5122559) B5122559
theorem B18213541 : Blo 2101435 18213541 := bstep (se 4 (by rfl) ⟨1707519, by rfl⟩ : syracuseStep 18213541 = 3415039) B3415039
theorem B97138885 : Blo 2101435 97138885 := bstep (se 4 (by rfl) ⟨9106770, by rfl⟩ : syracuseStep 97138885 = 18213541) B18213541
theorem B129518513 : Blo 2101435 129518513 := bstep (se 2 (by rfl) ⟨48569442, by rfl⟩ : syracuseStep 129518513 = 97138885) B97138885
theorem B86345675 : Blo 2101435 86345675 := bstep (se 1 (by rfl) ⟨64759256, by rfl⟩ : syracuseStep 86345675 = 129518513) B129518513
theorem B57563783 : Blo 2101435 57563783 := bstep (se 1 (by rfl) ⟨43172837, by rfl⟩ : syracuseStep 57563783 = 86345675) B86345675
theorem B38375855 : Blo 2101435 38375855 := bstep (se 1 (by rfl) ⟨28781891, by rfl⟩ : syracuseStep 38375855 = 57563783) B57563783
theorem B25583903 : Blo 2101435 25583903 := bstep (se 1 (by rfl) ⟨19187927, by rfl⟩ : syracuseStep 25583903 = 38375855) B38375855
theorem B17055935 : Blo 2101435 17055935 := bstep (se 1 (by rfl) ⟨12791951, by rfl⟩ : syracuseStep 17055935 = 25583903) B25583903
theorem B11370623 : Blo 2101435 11370623 := bstep (se 1 (by rfl) ⟨8527967, by rfl⟩ : syracuseStep 11370623 = 17055935) B17055935
theorem B121286645 : Blo 2101435 121286645 := bstep (se 5 (by rfl) ⟨5685311, by rfl⟩ : syracuseStep 121286645 = 11370623) B11370623
theorem B80857763 : Blo 2101435 80857763 := bstep (se 1 (by rfl) ⟨60643322, by rfl⟩ : syracuseStep 80857763 = 121286645) B121286645
theorem B53905175 : Blo 2101435 53905175 := bstep (se 1 (by rfl) ⟨40428881, by rfl⟩ : syracuseStep 53905175 = 80857763) B80857763
theorem B35936783 : Blo 2101435 35936783 := bstep (se 1 (by rfl) ⟨26952587, by rfl⟩ : syracuseStep 35936783 = 53905175) B53905175
theorem B23957855 : Blo 2101435 23957855 := bstep (se 1 (by rfl) ⟨17968391, by rfl⟩ : syracuseStep 23957855 = 35936783) B35936783
theorem B15971903 : Blo 2101435 15971903 := bstep (se 1 (by rfl) ⟨11978927, by rfl⟩ : syracuseStep 15971903 = 23957855) B23957855
theorem B10647935 : Blo 2101435 10647935 := bstep (se 1 (by rfl) ⟨7985951, by rfl⟩ : syracuseStep 10647935 = 15971903) B15971903
theorem B7098623 : Blo 2101435 7098623 := bstep (se 1 (by rfl) ⟨5323967, by rfl⟩ : syracuseStep 7098623 = 10647935) B10647935
theorem B4732415 : Blo 2101435 4732415 := bstep (se 1 (by rfl) ⟨3549311, by rfl⟩ : syracuseStep 4732415 = 7098623) B7098623
theorem B3154943 : Blo 2101435 3154943 := bstep (se 1 (by rfl) ⟨2366207, by rfl⟩ : syracuseStep 3154943 = 4732415) B4732415
theorem B2103295 : Blo 2101435 2103295 := bstep (se 1 (by rfl) ⟨1577471, by rfl⟩ : syracuseStep 2103295 = 3154943) B3154943
theorem B3154949 : Blo 2101435 3154949 := bbase (se 4 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 3154949 = 591553) (by norm_num)
theorem B2103299 : Blo 2101435 2103299 := bstep (se 1 (by rfl) ⟨1577474, by rfl⟩ : syracuseStep 2103299 = 3154949) B3154949
theorem B3549325 : Blo 2101435 3549325 := bbase (se 3 (by rfl) ⟨665498, by rfl⟩ : syracuseStep 3549325 = 1330997) (by norm_num)
theorem B4732433 : Blo 2101435 4732433 := bstep (se 2 (by rfl) ⟨1774662, by rfl⟩ : syracuseStep 4732433 = 3549325) B3549325
theorem B3154955 : Blo 2101435 3154955 := bstep (se 1 (by rfl) ⟨2366216, by rfl⟩ : syracuseStep 3154955 = 4732433) B4732433
theorem B2103303 : Blo 2101435 2103303 := bstep (se 1 (by rfl) ⟨1577477, by rfl⟩ : syracuseStep 2103303 = 3154955) B3154955
theorem B2366221 : Blo 2101435 2366221 := bbase (se 3 (by rfl) ⟨443666, by rfl⟩ : syracuseStep 2366221 = 887333) (by norm_num)
theorem B3154961 : Blo 2101435 3154961 := bstep (se 2 (by rfl) ⟨1183110, by rfl⟩ : syracuseStep 3154961 = 2366221) B2366221
theorem B2103307 : Blo 2101435 2103307 := bstep (se 1 (by rfl) ⟨1577480, by rfl⟩ : syracuseStep 2103307 = 3154961) B3154961
theorem B7098677 : Blo 2101435 7098677 := bbase (se 5 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 7098677 = 665501) (by norm_num)
theorem B4732451 : Blo 2101435 4732451 := bstep (se 1 (by rfl) ⟨3549338, by rfl⟩ : syracuseStep 4732451 = 7098677) B7098677
theorem B3154967 : Blo 2101435 3154967 := bstep (se 1 (by rfl) ⟨2366225, by rfl⟩ : syracuseStep 3154967 = 4732451) B4732451
theorem B2103311 : Blo 2101435 2103311 := bstep (se 1 (by rfl) ⟨1577483, by rfl⟩ : syracuseStep 2103311 = 3154967) B3154967
theorem B3154973 : Blo 2101435 3154973 := bbase (se 3 (by rfl) ⟨591557, by rfl⟩ : syracuseStep 3154973 = 1183115) (by norm_num)
theorem B2103315 : Blo 2101435 2103315 := bstep (se 1 (by rfl) ⟨1577486, by rfl⟩ : syracuseStep 2103315 = 3154973) B3154973
theorem B4732469 : Blo 2101435 4732469 := bbase (se 5 (by rfl) ⟨221834, by rfl⟩ : syracuseStep 4732469 = 443669) (by norm_num)
theorem B3154979 : Blo 2101435 3154979 := bstep (se 1 (by rfl) ⟨2366234, by rfl⟩ : syracuseStep 3154979 = 4732469) B4732469
theorem B2103319 : Blo 2101435 2103319 := bstep (se 1 (by rfl) ⟨1577489, by rfl⟩ : syracuseStep 2103319 = 3154979) B3154979
theorem B2339273 : Blo 2101435 2339273 := bbase (se 2 (by rfl) ⟨877227, by rfl⟩ : syracuseStep 2339273 = 1754455) (by norm_num)
theorem B6238061 : Blo 2101435 6238061 := bstep (se 3 (by rfl) ⟨1169636, by rfl⟩ : syracuseStep 6238061 = 2339273) B2339273
theorem B4158707 : Blo 2101435 4158707 := bstep (se 1 (by rfl) ⟨3119030, by rfl⟩ : syracuseStep 4158707 = 6238061) B6238061
theorem B11089885 : Blo 2101435 11089885 := bstep (se 3 (by rfl) ⟨2079353, by rfl⟩ : syracuseStep 11089885 = 4158707) B4158707
theorem B14786513 : Blo 2101435 14786513 := bstep (se 2 (by rfl) ⟨5544942, by rfl⟩ : syracuseStep 14786513 = 11089885) B11089885
theorem B9857675 : Blo 2101435 9857675 := bstep (se 1 (by rfl) ⟨7393256, by rfl⟩ : syracuseStep 9857675 = 14786513) B14786513
theorem B6571783 : Blo 2101435 6571783 := bstep (se 1 (by rfl) ⟨4928837, by rfl⟩ : syracuseStep 6571783 = 9857675) B9857675
theorem B8762377 : Blo 2101435 8762377 := bstep (se 2 (by rfl) ⟨3285891, by rfl⟩ : syracuseStep 8762377 = 6571783) B6571783
theorem B11683169 : Blo 2101435 11683169 := bstep (se 2 (by rfl) ⟨4381188, by rfl⟩ : syracuseStep 11683169 = 8762377) B8762377
theorem B7788779 : Blo 2101435 7788779 := bstep (se 1 (by rfl) ⟨5841584, by rfl⟩ : syracuseStep 7788779 = 11683169) B11683169
theorem B5192519 : Blo 2101435 5192519 := bstep (se 1 (by rfl) ⟨3894389, by rfl⟩ : syracuseStep 5192519 = 7788779) B7788779
theorem B13846717 : Blo 2101435 13846717 := bstep (se 3 (by rfl) ⟨2596259, by rfl⟩ : syracuseStep 13846717 = 5192519) B5192519
theorem B73849157 : Blo 2101435 73849157 := bstep (se 4 (by rfl) ⟨6923358, by rfl⟩ : syracuseStep 73849157 = 13846717) B13846717
theorem B49232771 : Blo 2101435 49232771 := bstep (se 1 (by rfl) ⟨36924578, by rfl⟩ : syracuseStep 49232771 = 73849157) B73849157
theorem B32821847 : Blo 2101435 32821847 := bstep (se 1 (by rfl) ⟨24616385, by rfl⟩ : syracuseStep 32821847 = 49232771) B49232771
theorem B21881231 : Blo 2101435 21881231 := bstep (se 1 (by rfl) ⟨16410923, by rfl⟩ : syracuseStep 21881231 = 32821847) B32821847
theorem B14587487 : Blo 2101435 14587487 := bstep (se 1 (by rfl) ⟨10940615, by rfl⟩ : syracuseStep 14587487 = 21881231) B21881231
theorem B9724991 : Blo 2101435 9724991 := bstep (se 1 (by rfl) ⟨7293743, by rfl⟩ : syracuseStep 9724991 = 14587487) B14587487
theorem B103733237 : Blo 2101435 103733237 := bstep (se 5 (by rfl) ⟨4862495, by rfl⟩ : syracuseStep 103733237 = 9724991) B9724991
theorem B276621965 : Blo 2101435 276621965 := bstep (se 3 (by rfl) ⟨51866618, by rfl⟩ : syracuseStep 276621965 = 103733237) B103733237
theorem B184414643 : Blo 2101435 184414643 := bstep (se 1 (by rfl) ⟨138310982, by rfl⟩ : syracuseStep 184414643 = 276621965) B276621965
theorem B122943095 : Blo 2101435 122943095 := bstep (se 1 (by rfl) ⟨92207321, by rfl⟩ : syracuseStep 122943095 = 184414643) B184414643
theorem B81962063 : Blo 2101435 81962063 := bstep (se 1 (by rfl) ⟨61471547, by rfl⟩ : syracuseStep 81962063 = 122943095) B122943095
theorem B54641375 : Blo 2101435 54641375 := bstep (se 1 (by rfl) ⟨40981031, by rfl⟩ : syracuseStep 54641375 = 81962063) B81962063
theorem B36427583 : Blo 2101435 36427583 := bstep (se 1 (by rfl) ⟨27320687, by rfl⟩ : syracuseStep 36427583 = 54641375) B54641375
theorem B97140221 : Blo 2101435 97140221 := bstep (se 3 (by rfl) ⟨18213791, by rfl⟩ : syracuseStep 97140221 = 36427583) B36427583
theorem B64760147 : Blo 2101435 64760147 := bstep (se 1 (by rfl) ⟨48570110, by rfl⟩ : syracuseStep 64760147 = 97140221) B97140221
theorem B43173431 : Blo 2101435 43173431 := bstep (se 1 (by rfl) ⟨32380073, by rfl⟩ : syracuseStep 43173431 = 64760147) B64760147
theorem B28782287 : Blo 2101435 28782287 := bstep (se 1 (by rfl) ⟨21586715, by rfl⟩ : syracuseStep 28782287 = 43173431) B43173431
theorem B19188191 : Blo 2101435 19188191 := bstep (se 1 (by rfl) ⟨14391143, by rfl⟩ : syracuseStep 19188191 = 28782287) B28782287
theorem B12792127 : Blo 2101435 12792127 := bstep (se 1 (by rfl) ⟨9594095, by rfl⟩ : syracuseStep 12792127 = 19188191) B19188191
theorem B17056169 : Blo 2101435 17056169 := bstep (se 2 (by rfl) ⟨6396063, by rfl⟩ : syracuseStep 17056169 = 12792127) B12792127
theorem B11370779 : Blo 2101435 11370779 := bstep (se 1 (by rfl) ⟨8528084, by rfl⟩ : syracuseStep 11370779 = 17056169) B17056169
theorem B7580519 : Blo 2101435 7580519 := bstep (se 1 (by rfl) ⟨5685389, by rfl⟩ : syracuseStep 7580519 = 11370779) B11370779
theorem B5053679 : Blo 2101435 5053679 := bstep (se 1 (by rfl) ⟨3790259, by rfl⟩ : syracuseStep 5053679 = 7580519) B7580519
theorem B3369119 : Blo 2101435 3369119 := bstep (se 1 (by rfl) ⟨2526839, by rfl⟩ : syracuseStep 3369119 = 5053679) B5053679
theorem B8984317 : Blo 2101435 8984317 := bstep (se 3 (by rfl) ⟨1684559, by rfl⟩ : syracuseStep 8984317 = 3369119) B3369119
theorem B11979089 : Blo 2101435 11979089 := bstep (se 2 (by rfl) ⟨4492158, by rfl⟩ : syracuseStep 11979089 = 8984317) B8984317
theorem B7986059 : Blo 2101435 7986059 := bstep (se 1 (by rfl) ⟨5989544, by rfl⟩ : syracuseStep 7986059 = 11979089) B11979089
theorem B5324039 : Blo 2101435 5324039 := bstep (se 1 (by rfl) ⟨3993029, by rfl⟩ : syracuseStep 5324039 = 7986059) B7986059
theorem B3549359 : Blo 2101435 3549359 := bstep (se 1 (by rfl) ⟨2662019, by rfl⟩ : syracuseStep 3549359 = 5324039) B5324039
theorem B2366239 : Blo 2101435 2366239 := bstep (se 1 (by rfl) ⟨1774679, by rfl⟩ : syracuseStep 2366239 = 3549359) B3549359
theorem B3154985 : Blo 2101435 3154985 := bstep (se 2 (by rfl) ⟨1183119, by rfl⟩ : syracuseStep 3154985 = 2366239) B2366239
theorem B2103323 : Blo 2101435 2103323 := bstep (se 1 (by rfl) ⟨1577492, by rfl⟩ : syracuseStep 2103323 = 3154985) B3154985
theorem B3369125 : Blo 2101435 3369125 := bbase (se 4 (by rfl) ⟨315855, by rfl⟩ : syracuseStep 3369125 = 631711) (by norm_num)
theorem B8984333 : Blo 2101435 8984333 := bstep (se 3 (by rfl) ⟨1684562, by rfl⟩ : syracuseStep 8984333 = 3369125) B3369125
theorem B5989555 : Blo 2101435 5989555 := bstep (se 1 (by rfl) ⟨4492166, by rfl⟩ : syracuseStep 5989555 = 8984333) B8984333
theorem B7986073 : Blo 2101435 7986073 := bstep (se 2 (by rfl) ⟨2994777, by rfl⟩ : syracuseStep 7986073 = 5989555) B5989555
theorem B10648097 : Blo 2101435 10648097 := bstep (se 2 (by rfl) ⟨3993036, by rfl⟩ : syracuseStep 10648097 = 7986073) B7986073
theorem B7098731 : Blo 2101435 7098731 := bstep (se 1 (by rfl) ⟨5324048, by rfl⟩ : syracuseStep 7098731 = 10648097) B10648097
theorem B4732487 : Blo 2101435 4732487 := bstep (se 1 (by rfl) ⟨3549365, by rfl⟩ : syracuseStep 4732487 = 7098731) B7098731
theorem B3154991 : Blo 2101435 3154991 := bstep (se 1 (by rfl) ⟨2366243, by rfl⟩ : syracuseStep 3154991 = 4732487) B4732487
theorem B2103327 : Blo 2101435 2103327 := bstep (se 1 (by rfl) ⟨1577495, by rfl⟩ : syracuseStep 2103327 = 3154991) B3154991
theorem B3154997 : Blo 2101435 3154997 := bbase (se 5 (by rfl) ⟨147890, by rfl⟩ : syracuseStep 3154997 = 295781) (by norm_num)
theorem B2103331 : Blo 2101435 2103331 := bstep (se 1 (by rfl) ⟨1577498, by rfl⟩ : syracuseStep 2103331 = 3154997) B3154997
theorem B5324069 : Blo 2101435 5324069 := bbase (se 4 (by rfl) ⟨499131, by rfl⟩ : syracuseStep 5324069 = 998263) (by norm_num)
theorem B3549379 : Blo 2101435 3549379 := bstep (se 1 (by rfl) ⟨2662034, by rfl⟩ : syracuseStep 3549379 = 5324069) B5324069
theorem B4732505 : Blo 2101435 4732505 := bstep (se 2 (by rfl) ⟨1774689, by rfl⟩ : syracuseStep 4732505 = 3549379) B3549379
theorem B3155003 : Blo 2101435 3155003 := bstep (se 1 (by rfl) ⟨2366252, by rfl⟩ : syracuseStep 3155003 = 4732505) B4732505
theorem B2103335 : Blo 2101435 2103335 := bstep (se 1 (by rfl) ⟨1577501, by rfl⟩ : syracuseStep 2103335 = 3155003) B3155003
theorem B2366257 : Blo 2101435 2366257 := bbase (se 2 (by rfl) ⟨887346, by rfl⟩ : syracuseStep 2366257 = 1774693) (by norm_num)
theorem B3155009 : Blo 2101435 3155009 := bstep (se 2 (by rfl) ⟨1183128, by rfl⟩ : syracuseStep 3155009 = 2366257) B2366257
theorem B2103339 : Blo 2101435 2103339 := bstep (se 1 (by rfl) ⟨1577504, by rfl⟩ : syracuseStep 2103339 = 3155009) B3155009
theorem B19188373 : Blo 2101435 19188373 := bbase (se 6 (by rfl) ⟨449727, by rfl⟩ : syracuseStep 19188373 = 899455) (by norm_num)
theorem B25584497 : Blo 2101435 25584497 := bstep (se 2 (by rfl) ⟨9594186, by rfl⟩ : syracuseStep 25584497 = 19188373) B19188373
theorem B17056331 : Blo 2101435 17056331 := bstep (se 1 (by rfl) ⟨12792248, by rfl⟩ : syracuseStep 17056331 = 25584497) B25584497
theorem B11370887 : Blo 2101435 11370887 := bstep (se 1 (by rfl) ⟨8528165, by rfl⟩ : syracuseStep 11370887 = 17056331) B17056331
theorem B7580591 : Blo 2101435 7580591 := bstep (se 1 (by rfl) ⟨5685443, by rfl⟩ : syracuseStep 7580591 = 11370887) B11370887
theorem B5053727 : Blo 2101435 5053727 := bstep (se 1 (by rfl) ⟨3790295, by rfl⟩ : syracuseStep 5053727 = 7580591) B7580591
theorem B3369151 : Blo 2101435 3369151 := bstep (se 1 (by rfl) ⟨2526863, by rfl⟩ : syracuseStep 3369151 = 5053727) B5053727
theorem B4492201 : Blo 2101435 4492201 := bstep (se 2 (by rfl) ⟨1684575, by rfl⟩ : syracuseStep 4492201 = 3369151) B3369151
theorem B5989601 : Blo 2101435 5989601 := bstep (se 2 (by rfl) ⟨2246100, by rfl⟩ : syracuseStep 5989601 = 4492201) B4492201
theorem B3993067 : Blo 2101435 3993067 := bstep (se 1 (by rfl) ⟨2994800, by rfl⟩ : syracuseStep 3993067 = 5989601) B5989601
theorem B5324089 : Blo 2101435 5324089 := bstep (se 2 (by rfl) ⟨1996533, by rfl⟩ : syracuseStep 5324089 = 3993067) B3993067
theorem B7098785 : Blo 2101435 7098785 := bstep (se 2 (by rfl) ⟨2662044, by rfl⟩ : syracuseStep 7098785 = 5324089) B5324089
theorem B4732523 : Blo 2101435 4732523 := bstep (se 1 (by rfl) ⟨3549392, by rfl⟩ : syracuseStep 4732523 = 7098785) B7098785
theorem B3155015 : Blo 2101435 3155015 := bstep (se 1 (by rfl) ⟨2366261, by rfl⟩ : syracuseStep 3155015 = 4732523) B4732523
theorem B2103343 : Blo 2101435 2103343 := bstep (se 1 (by rfl) ⟨1577507, by rfl⟩ : syracuseStep 2103343 = 3155015) B3155015
theorem B3155021 : Blo 2101435 3155021 := bbase (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) (by norm_num)
theorem B2103347 : Blo 2101435 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B4732541 : Blo 2101435 4732541 := bbase (se 3 (by rfl) ⟨887351, by rfl⟩ : syracuseStep 4732541 = 1774703) (by norm_num)
theorem B3155027 : Blo 2101435 3155027 := bstep (se 1 (by rfl) ⟨2366270, by rfl⟩ : syracuseStep 3155027 = 4732541) B4732541
theorem B2103351 : Blo 2101435 2103351 := bstep (se 1 (by rfl) ⟨1577513, by rfl⟩ : syracuseStep 2103351 = 3155027) B3155027
theorem B3549413 : Blo 2101435 3549413 := bbase (se 4 (by rfl) ⟨332757, by rfl⟩ : syracuseStep 3549413 = 665515) (by norm_num)
theorem B2366275 : Blo 2101435 2366275 := bstep (se 1 (by rfl) ⟨1774706, by rfl⟩ : syracuseStep 2366275 = 3549413) B3549413
theorem B3155033 : Blo 2101435 3155033 := bstep (se 2 (by rfl) ⟨1183137, by rfl⟩ : syracuseStep 3155033 = 2366275) B2366275
theorem B2103355 : Blo 2101435 2103355 := bstep (se 1 (by rfl) ⟨1577516, by rfl⟩ : syracuseStep 2103355 = 3155033) B3155033
theorem B5053765 : Blo 2101435 5053765 := bbase (se 4 (by rfl) ⟨473790, by rfl⟩ : syracuseStep 5053765 = 947581) (by norm_num)
theorem B6738353 : Blo 2101435 6738353 := bstep (se 2 (by rfl) ⟨2526882, by rfl⟩ : syracuseStep 6738353 = 5053765) B5053765
theorem B4492235 : Blo 2101435 4492235 := bstep (se 1 (by rfl) ⟨3369176, by rfl⟩ : syracuseStep 4492235 = 6738353) B6738353
theorem B2994823 : Blo 2101435 2994823 := bstep (se 1 (by rfl) ⟨2246117, by rfl⟩ : syracuseStep 2994823 = 4492235) B4492235
theorem B15972389 : Blo 2101435 15972389 := bstep (se 4 (by rfl) ⟨1497411, by rfl⟩ : syracuseStep 15972389 = 2994823) B2994823
theorem B10648259 : Blo 2101435 10648259 := bstep (se 1 (by rfl) ⟨7986194, by rfl⟩ : syracuseStep 10648259 = 15972389) B15972389
theorem B7098839 : Blo 2101435 7098839 := bstep (se 1 (by rfl) ⟨5324129, by rfl⟩ : syracuseStep 7098839 = 10648259) B10648259
theorem B4732559 : Blo 2101435 4732559 := bstep (se 1 (by rfl) ⟨3549419, by rfl⟩ : syracuseStep 4732559 = 7098839) B7098839
theorem B3155039 : Blo 2101435 3155039 := bstep (se 1 (by rfl) ⟨2366279, by rfl⟩ : syracuseStep 3155039 = 4732559) B4732559
theorem B2103359 : Blo 2101435 2103359 := bstep (se 1 (by rfl) ⟨1577519, by rfl⟩ : syracuseStep 2103359 = 3155039) B3155039
theorem B3155045 : Blo 2101435 3155045 := bbase (se 4 (by rfl) ⟨295785, by rfl⟩ : syracuseStep 3155045 = 591571) (by norm_num)
theorem B2103363 : Blo 2101435 2103363 := bstep (se 1 (by rfl) ⟨1577522, by rfl⟩ : syracuseStep 2103363 = 3155045) B3155045
theorem B4492253 : Blo 2101435 4492253 := bbase (se 3 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 4492253 = 1684595) (by norm_num)
theorem B2994835 : Blo 2101435 2994835 := bstep (se 1 (by rfl) ⟨2246126, by rfl⟩ : syracuseStep 2994835 = 4492253) B4492253
theorem B3993113 : Blo 2101435 3993113 := bstep (se 2 (by rfl) ⟨1497417, by rfl⟩ : syracuseStep 3993113 = 2994835) B2994835
theorem B2662075 : Blo 2101435 2662075 := bstep (se 1 (by rfl) ⟨1996556, by rfl⟩ : syracuseStep 2662075 = 3993113) B3993113
theorem B3549433 : Blo 2101435 3549433 := bstep (se 2 (by rfl) ⟨1331037, by rfl⟩ : syracuseStep 3549433 = 2662075) B2662075
theorem B4732577 : Blo 2101435 4732577 := bstep (se 2 (by rfl) ⟨1774716, by rfl⟩ : syracuseStep 4732577 = 3549433) B3549433
theorem B3155051 : Blo 2101435 3155051 := bstep (se 1 (by rfl) ⟨2366288, by rfl⟩ : syracuseStep 3155051 = 4732577) B4732577
theorem B2103367 : Blo 2101435 2103367 := bstep (se 1 (by rfl) ⟨1577525, by rfl⟩ : syracuseStep 2103367 = 3155051) B3155051
theorem B2366293 : Blo 2101435 2366293 := bbase (se 9 (by rfl) ⟨6932, by rfl⟩ : syracuseStep 2366293 = 13865) (by norm_num)
theorem B3155057 : Blo 2101435 3155057 := bstep (se 2 (by rfl) ⟨1183146, by rfl⟩ : syracuseStep 3155057 = 2366293) B2366293
theorem B2103371 : Blo 2101435 2103371 := bstep (se 1 (by rfl) ⟨1577528, by rfl⟩ : syracuseStep 2103371 = 3155057) B3155057
theorem B2662085 : Blo 2101435 2662085 := bbase (se 4 (by rfl) ⟨249570, by rfl⟩ : syracuseStep 2662085 = 499141) (by norm_num)
theorem B7098893 : Blo 2101435 7098893 := bstep (se 3 (by rfl) ⟨1331042, by rfl⟩ : syracuseStep 7098893 = 2662085) B2662085
theorem B4732595 : Blo 2101435 4732595 := bstep (se 1 (by rfl) ⟨3549446, by rfl⟩ : syracuseStep 4732595 = 7098893) B7098893
theorem B3155063 : Blo 2101435 3155063 := bstep (se 1 (by rfl) ⟨2366297, by rfl⟩ : syracuseStep 3155063 = 4732595) B4732595
theorem B2103375 : Blo 2101435 2103375 := bstep (se 1 (by rfl) ⟨1577531, by rfl⟩ : syracuseStep 2103375 = 3155063) B3155063
theorem B3155069 : Blo 2101435 3155069 := bbase (se 3 (by rfl) ⟨591575, by rfl⟩ : syracuseStep 3155069 = 1183151) (by norm_num)
theorem B2103379 : Blo 2101435 2103379 := bstep (se 1 (by rfl) ⟨1577534, by rfl⟩ : syracuseStep 2103379 = 3155069) B3155069
theorem B4732613 : Blo 2101435 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B3155075 : Blo 2101435 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B2103383 : Blo 2101435 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B2842781 : Blo 2101435 2842781 := bbase (se 3 (by rfl) ⟨533021, by rfl⟩ : syracuseStep 2842781 = 1066043) (by norm_num)
theorem B30322997 : Blo 2101435 30322997 := bstep (se 5 (by rfl) ⟨1421390, by rfl⟩ : syracuseStep 30322997 = 2842781) B2842781
theorem B20215331 : Blo 2101435 20215331 := bstep (se 1 (by rfl) ⟨15161498, by rfl⟩ : syracuseStep 20215331 = 30322997) B30322997
theorem B13476887 : Blo 2101435 13476887 := bstep (se 1 (by rfl) ⟨10107665, by rfl⟩ : syracuseStep 13476887 = 20215331) B20215331
theorem B8984591 : Blo 2101435 8984591 := bstep (se 1 (by rfl) ⟨6738443, by rfl⟩ : syracuseStep 8984591 = 13476887) B13476887
theorem B5989727 : Blo 2101435 5989727 := bstep (se 1 (by rfl) ⟨4492295, by rfl⟩ : syracuseStep 5989727 = 8984591) B8984591
theorem B3993151 : Blo 2101435 3993151 := bstep (se 1 (by rfl) ⟨2994863, by rfl⟩ : syracuseStep 3993151 = 5989727) B5989727
theorem B5324201 : Blo 2101435 5324201 := bstep (se 2 (by rfl) ⟨1996575, by rfl⟩ : syracuseStep 5324201 = 3993151) B3993151
theorem B3549467 : Blo 2101435 3549467 := bstep (se 1 (by rfl) ⟨2662100, by rfl⟩ : syracuseStep 3549467 = 5324201) B5324201
theorem B2366311 : Blo 2101435 2366311 := bstep (se 1 (by rfl) ⟨1774733, by rfl⟩ : syracuseStep 2366311 = 3549467) B3549467
theorem B3155081 : Blo 2101435 3155081 := bstep (se 2 (by rfl) ⟨1183155, by rfl⟩ : syracuseStep 3155081 = 2366311) B2366311
theorem B2103387 : Blo 2101435 2103387 := bstep (se 1 (by rfl) ⟨1577540, by rfl⟩ : syracuseStep 2103387 = 3155081) B3155081
theorem B10648421 : Blo 2101435 10648421 := bbase (se 4 (by rfl) ⟨998289, by rfl⟩ : syracuseStep 10648421 = 1996579) (by norm_num)
theorem B7098947 : Blo 2101435 7098947 := bstep (se 1 (by rfl) ⟨5324210, by rfl⟩ : syracuseStep 7098947 = 10648421) B10648421
theorem B4732631 : Blo 2101435 4732631 := bstep (se 1 (by rfl) ⟨3549473, by rfl⟩ : syracuseStep 4732631 = 7098947) B7098947
theorem B3155087 : Blo 2101435 3155087 := bstep (se 1 (by rfl) ⟨2366315, by rfl⟩ : syracuseStep 3155087 = 4732631) B4732631
theorem B2103391 : Blo 2101435 2103391 := bstep (se 1 (by rfl) ⟨1577543, by rfl⟩ : syracuseStep 2103391 = 3155087) B3155087
theorem B3155093 : Blo 2101435 3155093 := bbase (se 6 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 3155093 = 147895) (by norm_num)
theorem B2103395 : Blo 2101435 2103395 := bstep (se 1 (by rfl) ⟨1577546, by rfl⟩ : syracuseStep 2103395 = 3155093) B3155093
theorem B5053861 : Blo 2101435 5053861 := bbase (se 4 (by rfl) ⟨473799, by rfl⟩ : syracuseStep 5053861 = 947599) (by norm_num)
theorem B6738481 : Blo 2101435 6738481 := bstep (se 2 (by rfl) ⟨2526930, by rfl⟩ : syracuseStep 6738481 = 5053861) B5053861
theorem B8984641 : Blo 2101435 8984641 := bstep (se 2 (by rfl) ⟨3369240, by rfl⟩ : syracuseStep 8984641 = 6738481) B6738481
theorem B11979521 : Blo 2101435 11979521 := bstep (se 2 (by rfl) ⟨4492320, by rfl⟩ : syracuseStep 11979521 = 8984641) B8984641
theorem B7986347 : Blo 2101435 7986347 := bstep (se 1 (by rfl) ⟨5989760, by rfl⟩ : syracuseStep 7986347 = 11979521) B11979521
theorem B5324231 : Blo 2101435 5324231 := bstep (se 1 (by rfl) ⟨3993173, by rfl⟩ : syracuseStep 5324231 = 7986347) B7986347
theorem B3549487 : Blo 2101435 3549487 := bstep (se 1 (by rfl) ⟨2662115, by rfl⟩ : syracuseStep 3549487 = 5324231) B5324231
theorem B4732649 : Blo 2101435 4732649 := bstep (se 2 (by rfl) ⟨1774743, by rfl⟩ : syracuseStep 4732649 = 3549487) B3549487
theorem B3155099 : Blo 2101435 3155099 := bstep (se 1 (by rfl) ⟨2366324, by rfl⟩ : syracuseStep 3155099 = 4732649) B4732649
theorem B2103399 : Blo 2101435 2103399 := bstep (se 1 (by rfl) ⟨1577549, by rfl⟩ : syracuseStep 2103399 = 3155099) B3155099
theorem B2366329 : Blo 2101435 2366329 := bbase (se 2 (by rfl) ⟨887373, by rfl⟩ : syracuseStep 2366329 = 1774747) (by norm_num)
theorem B3155105 : Blo 2101435 3155105 := bstep (se 2 (by rfl) ⟨1183164, by rfl⟩ : syracuseStep 3155105 = 2366329) B2366329
theorem B2103403 : Blo 2101435 2103403 := bstep (se 1 (by rfl) ⟨1577552, by rfl⟩ : syracuseStep 2103403 = 3155105) B3155105
theorem B13477013 : Blo 2101435 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B8984675 : Blo 2101435 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B5989783 : Blo 2101435 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B7986377 : Blo 2101435 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B5324251 : Blo 2101435 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B7099001 : Blo 2101435 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B4732667 : Blo 2101435 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B3155111 : Blo 2101435 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B2103407 : Blo 2101435 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B3155117 : Blo 2101435 3155117 := bbase (se 3 (by rfl) ⟨591584, by rfl⟩ : syracuseStep 3155117 = 1183169) (by norm_num)
theorem B2103411 : Blo 2101435 2103411 := bstep (se 1 (by rfl) ⟨1577558, by rfl⟩ : syracuseStep 2103411 = 3155117) B3155117
theorem B4732685 : Blo 2101435 4732685 := bbase (se 3 (by rfl) ⟨887378, by rfl⟩ : syracuseStep 4732685 = 1774757) (by norm_num)
theorem B3155123 : Blo 2101435 3155123 := bstep (se 1 (by rfl) ⟨2366342, by rfl⟩ : syracuseStep 3155123 = 4732685) B4732685
theorem B2103415 : Blo 2101435 2103415 := bstep (se 1 (by rfl) ⟨1577561, by rfl⟩ : syracuseStep 2103415 = 3155123) B3155123
theorem B2662141 : Blo 2101435 2662141 := bbase (se 3 (by rfl) ⟨499151, by rfl⟩ : syracuseStep 2662141 = 998303) (by norm_num)
theorem B3549521 : Blo 2101435 3549521 := bstep (se 2 (by rfl) ⟨1331070, by rfl⟩ : syracuseStep 3549521 = 2662141) B2662141
theorem B2366347 : Blo 2101435 2366347 := bstep (se 1 (by rfl) ⟨1774760, by rfl⟩ : syracuseStep 2366347 = 3549521) B3549521
theorem B3155129 : Blo 2101435 3155129 := bstep (se 2 (by rfl) ⟨1183173, by rfl⟩ : syracuseStep 3155129 = 2366347) B2366347
theorem B2103419 : Blo 2101435 2103419 := bstep (se 1 (by rfl) ⟨1577564, by rfl⟩ : syracuseStep 2103419 = 3155129) B3155129
theorem B2596385 : Blo 2101435 2596385 := bbase (se 2 (by rfl) ⟨973644, by rfl⟩ : syracuseStep 2596385 = 1947289) (by norm_num)
theorem B6923693 : Blo 2101435 6923693 := bstep (se 3 (by rfl) ⟨1298192, by rfl⟩ : syracuseStep 6923693 = 2596385) B2596385
theorem B4615795 : Blo 2101435 4615795 := bstep (se 1 (by rfl) ⟨3461846, by rfl⟩ : syracuseStep 4615795 = 6923693) B6923693
theorem B6154393 : Blo 2101435 6154393 := bstep (se 2 (by rfl) ⟨2307897, by rfl⟩ : syracuseStep 6154393 = 4615795) B4615795
theorem B8205857 : Blo 2101435 8205857 := bstep (se 2 (by rfl) ⟨3077196, by rfl⟩ : syracuseStep 8205857 = 6154393) B6154393
theorem B5470571 : Blo 2101435 5470571 := bstep (se 1 (by rfl) ⟨4102928, by rfl⟩ : syracuseStep 5470571 = 8205857) B8205857
theorem B3647047 : Blo 2101435 3647047 := bstep (se 1 (by rfl) ⟨2735285, by rfl⟩ : syracuseStep 3647047 = 5470571) B5470571
theorem B4862729 : Blo 2101435 4862729 := bstep (se 2 (by rfl) ⟨1823523, by rfl⟩ : syracuseStep 4862729 = 3647047) B3647047
theorem B3241819 : Blo 2101435 3241819 := bstep (se 1 (by rfl) ⟨2431364, by rfl⟩ : syracuseStep 3241819 = 4862729) B4862729
theorem B4322425 : Blo 2101435 4322425 := bstep (se 2 (by rfl) ⟨1620909, by rfl⟩ : syracuseStep 4322425 = 3241819) B3241819
theorem B5763233 : Blo 2101435 5763233 := bstep (se 2 (by rfl) ⟨2161212, by rfl⟩ : syracuseStep 5763233 = 4322425) B4322425
theorem B3842155 : Blo 2101435 3842155 := bstep (se 1 (by rfl) ⟨2881616, by rfl⟩ : syracuseStep 3842155 = 5763233) B5763233
theorem B5122873 : Blo 2101435 5122873 := bstep (se 2 (by rfl) ⟨1921077, by rfl⟩ : syracuseStep 5122873 = 3842155) B3842155
theorem B6830497 : Blo 2101435 6830497 := bstep (se 2 (by rfl) ⟨2561436, by rfl⟩ : syracuseStep 6830497 = 5122873) B5122873
theorem B9107329 : Blo 2101435 9107329 := bstep (se 2 (by rfl) ⟨3415248, by rfl⟩ : syracuseStep 9107329 = 6830497) B6830497
theorem B12143105 : Blo 2101435 12143105 := bstep (se 2 (by rfl) ⟨4553664, by rfl⟩ : syracuseStep 12143105 = 9107329) B9107329
theorem B8095403 : Blo 2101435 8095403 := bstep (se 1 (by rfl) ⟨6071552, by rfl⟩ : syracuseStep 8095403 = 12143105) B12143105
theorem B21587741 : Blo 2101435 21587741 := bstep (se 3 (by rfl) ⟨4047701, by rfl⟩ : syracuseStep 21587741 = 8095403) B8095403
theorem B14391827 : Blo 2101435 14391827 := bstep (se 1 (by rfl) ⟨10793870, by rfl⟩ : syracuseStep 14391827 = 21587741) B21587741
theorem B9594551 : Blo 2101435 9594551 := bstep (se 1 (by rfl) ⟨7195913, by rfl⟩ : syracuseStep 9594551 = 14391827) B14391827
theorem B6396367 : Blo 2101435 6396367 := bstep (se 1 (by rfl) ⟨4797275, by rfl⟩ : syracuseStep 6396367 = 9594551) B9594551
theorem B8528489 : Blo 2101435 8528489 := bstep (se 2 (by rfl) ⟨3198183, by rfl⟩ : syracuseStep 8528489 = 6396367) B6396367
theorem B5685659 : Blo 2101435 5685659 := bstep (se 1 (by rfl) ⟨4264244, by rfl⟩ : syracuseStep 5685659 = 8528489) B8528489
theorem B3790439 : Blo 2101435 3790439 := bstep (se 1 (by rfl) ⟨2842829, by rfl⟩ : syracuseStep 3790439 = 5685659) B5685659
theorem B2526959 : Blo 2101435 2526959 := bstep (se 1 (by rfl) ⟨1895219, by rfl⟩ : syracuseStep 2526959 = 3790439) B3790439
theorem B6738557 : Blo 2101435 6738557 := bstep (se 3 (by rfl) ⟨1263479, by rfl⟩ : syracuseStep 6738557 = 2526959) B2526959
theorem B17969485 : Blo 2101435 17969485 := bstep (se 3 (by rfl) ⟨3369278, by rfl⟩ : syracuseStep 17969485 = 6738557) B6738557
theorem B23959313 : Blo 2101435 23959313 := bstep (se 2 (by rfl) ⟨8984742, by rfl⟩ : syracuseStep 23959313 = 17969485) B17969485
theorem B15972875 : Blo 2101435 15972875 := bstep (se 1 (by rfl) ⟨11979656, by rfl⟩ : syracuseStep 15972875 = 23959313) B23959313
theorem B10648583 : Blo 2101435 10648583 := bstep (se 1 (by rfl) ⟨7986437, by rfl⟩ : syracuseStep 10648583 = 15972875) B15972875
theorem B7099055 : Blo 2101435 7099055 := bstep (se 1 (by rfl) ⟨5324291, by rfl⟩ : syracuseStep 7099055 = 10648583) B10648583
theorem B4732703 : Blo 2101435 4732703 := bstep (se 1 (by rfl) ⟨3549527, by rfl⟩ : syracuseStep 4732703 = 7099055) B7099055
theorem B3155135 : Blo 2101435 3155135 := bstep (se 1 (by rfl) ⟨2366351, by rfl⟩ : syracuseStep 3155135 = 4732703) B4732703
theorem B2103423 : Blo 2101435 2103423 := bstep (se 1 (by rfl) ⟨1577567, by rfl⟩ : syracuseStep 2103423 = 3155135) B3155135
theorem B3155141 : Blo 2101435 3155141 := bbase (se 4 (by rfl) ⟨295794, by rfl⟩ : syracuseStep 3155141 = 591589) (by norm_num)
theorem B2103427 : Blo 2101435 2103427 := bstep (se 1 (by rfl) ⟨1577570, by rfl⟩ : syracuseStep 2103427 = 3155141) B3155141
theorem B3549541 : Blo 2101435 3549541 := bbase (se 4 (by rfl) ⟨332769, by rfl⟩ : syracuseStep 3549541 = 665539) (by norm_num)
theorem B4732721 : Blo 2101435 4732721 := bstep (se 2 (by rfl) ⟨1774770, by rfl⟩ : syracuseStep 4732721 = 3549541) B3549541
theorem B3155147 : Blo 2101435 3155147 := bstep (se 1 (by rfl) ⟨2366360, by rfl⟩ : syracuseStep 3155147 = 4732721) B4732721
theorem B2103431 : Blo 2101435 2103431 := bstep (se 1 (by rfl) ⟨1577573, by rfl⟩ : syracuseStep 2103431 = 3155147) B3155147
theorem B2366365 : Blo 2101435 2366365 := bbase (se 3 (by rfl) ⟨443693, by rfl⟩ : syracuseStep 2366365 = 887387) (by norm_num)
theorem B3155153 : Blo 2101435 3155153 := bstep (se 2 (by rfl) ⟨1183182, by rfl⟩ : syracuseStep 3155153 = 2366365) B2366365
theorem B2103435 : Blo 2101435 2103435 := bstep (se 1 (by rfl) ⟨1577576, by rfl⟩ : syracuseStep 2103435 = 3155153) B3155153
theorem C0 (j : ℕ) (h1 : 525358 ≤ j) (h2 : j ≤ 525858) : Blo 2101435 (4 * j + 3) := by
  interval_cases j
  · exact B2101435
  · exact B2101439
  · exact B2101443
  · exact B2101447
  · exact B2101451
  · exact B2101455
  · exact B2101459
  · exact B2101463
  · exact B2101467
  · exact B2101471
  · exact B2101475
  · exact B2101479
  · exact B2101483
  · exact B2101487
  · exact B2101491
  · exact B2101495
  · exact B2101499
  · exact B2101503
  · exact B2101507
  · exact B2101511
  · exact B2101515
  · exact B2101519
  · exact B2101523
  · exact B2101527
  · exact B2101531
  · exact B2101535
  · exact B2101539
  · exact B2101543
  · exact B2101547
  · exact B2101551
  · exact B2101555
  · exact B2101559
  · exact B2101563
  · exact B2101567
  · exact B2101571
  · exact B2101575
  · exact B2101579
  · exact B2101583
  · exact B2101587
  · exact B2101591
  · exact B2101595
  · exact B2101599
  · exact B2101603
  · exact B2101607
  · exact B2101611
  · exact B2101615
  · exact B2101619
  · exact B2101623
  · exact B2101627
  · exact B2101631
  · exact B2101635
  · exact B2101639
  · exact B2101643
  · exact B2101647
  · exact B2101651
  · exact B2101655
  · exact B2101659
  · exact B2101663
  · exact B2101667
  · exact B2101671
  · exact B2101675
  · exact B2101679
  · exact B2101683
  · exact B2101687
  · exact B2101691
  · exact B2101695
  · exact B2101699
  · exact B2101703
  · exact B2101707
  · exact B2101711
  · exact B2101715
  · exact B2101719
  · exact B2101723
  · exact B2101727
  · exact B2101731
  · exact B2101735
  · exact B2101739
  · exact B2101743
  · exact B2101747
  · exact B2101751
  · exact B2101755
  · exact B2101759
  · exact B2101763
  · exact B2101767
  · exact B2101771
  · exact B2101775
  · exact B2101779
  · exact B2101783
  · exact B2101787
  · exact B2101791
  · exact B2101795
  · exact B2101799
  · exact B2101803
  · exact B2101807
  · exact B2101811
  · exact B2101815
  · exact B2101819
  · exact B2101823
  · exact B2101827
  · exact B2101831
  · exact B2101835
  · exact B2101839
  · exact B2101843
  · exact B2101847
  · exact B2101851
  · exact B2101855
  · exact B2101859
  · exact B2101863
  · exact B2101867
  · exact B2101871
  · exact B2101875
  · exact B2101879
  · exact B2101883
  · exact B2101887
  · exact B2101891
  · exact B2101895
  · exact B2101899
  · exact B2101903
  · exact B2101907
  · exact B2101911
  · exact B2101915
  · exact B2101919
  · exact B2101923
  · exact B2101927
  · exact B2101931
  · exact B2101935
  · exact B2101939
  · exact B2101943
  · exact B2101947
  · exact B2101951
  · exact B2101955
  · exact B2101959
  · exact B2101963
  · exact B2101967
  · exact B2101971
  · exact B2101975
  · exact B2101979
  · exact B2101983
  · exact B2101987
  · exact B2101991
  · exact B2101995
  · exact B2101999
  · exact B2102003
  · exact B2102007
  · exact B2102011
  · exact B2102015
  · exact B2102019
  · exact B2102023
  · exact B2102027
  · exact B2102031
  · exact B2102035
  · exact B2102039
  · exact B2102043
  · exact B2102047
  · exact B2102051
  · exact B2102055
  · exact B2102059
  · exact B2102063
  · exact B2102067
  · exact B2102071
  · exact B2102075
  · exact B2102079
  · exact B2102083
  · exact B2102087
  · exact B2102091
  · exact B2102095
  · exact B2102099
  · exact B2102103
  · exact B2102107
  · exact B2102111
  · exact B2102115
  · exact B2102119
  · exact B2102123
  · exact B2102127
  · exact B2102131
  · exact B2102135
  · exact B2102139
  · exact B2102143
  · exact B2102147
  · exact B2102151
  · exact B2102155
  · exact B2102159
  · exact B2102163
  · exact B2102167
  · exact B2102171
  · exact B2102175
  · exact B2102179
  · exact B2102183
  · exact B2102187
  · exact B2102191
  · exact B2102195
  · exact B2102199
  · exact B2102203
  · exact B2102207
  · exact B2102211
  · exact B2102215
  · exact B2102219
  · exact B2102223
  · exact B2102227
  · exact B2102231
  · exact B2102235
  · exact B2102239
  · exact B2102243
  · exact B2102247
  · exact B2102251
  · exact B2102255
  · exact B2102259
  · exact B2102263
  · exact B2102267
  · exact B2102271
  · exact B2102275
  · exact B2102279
  · exact B2102283
  · exact B2102287
  · exact B2102291
  · exact B2102295
  · exact B2102299
  · exact B2102303
  · exact B2102307
  · exact B2102311
  · exact B2102315
  · exact B2102319
  · exact B2102323
  · exact B2102327
  · exact B2102331
  · exact B2102335
  · exact B2102339
  · exact B2102343
  · exact B2102347
  · exact B2102351
  · exact B2102355
  · exact B2102359
  · exact B2102363
  · exact B2102367
  · exact B2102371
  · exact B2102375
  · exact B2102379
  · exact B2102383
  · exact B2102387
  · exact B2102391
  · exact B2102395
  · exact B2102399
  · exact B2102403
  · exact B2102407
  · exact B2102411
  · exact B2102415
  · exact B2102419
  · exact B2102423
  · exact B2102427
  · exact B2102431
  · exact B2102435
  · exact B2102439
  · exact B2102443
  · exact B2102447
  · exact B2102451
  · exact B2102455
  · exact B2102459
  · exact B2102463
  · exact B2102467
  · exact B2102471
  · exact B2102475
  · exact B2102479
  · exact B2102483
  · exact B2102487
  · exact B2102491
  · exact B2102495
  · exact B2102499
  · exact B2102503
  · exact B2102507
  · exact B2102511
  · exact B2102515
  · exact B2102519
  · exact B2102523
  · exact B2102527
  · exact B2102531
  · exact B2102535
  · exact B2102539
  · exact B2102543
  · exact B2102547
  · exact B2102551
  · exact B2102555
  · exact B2102559
  · exact B2102563
  · exact B2102567
  · exact B2102571
  · exact B2102575
  · exact B2102579
  · exact B2102583
  · exact B2102587
  · exact B2102591
  · exact B2102595
  · exact B2102599
  · exact B2102603
  · exact B2102607
  · exact B2102611
  · exact B2102615
  · exact B2102619
  · exact B2102623
  · exact B2102627
  · exact B2102631
  · exact B2102635
  · exact B2102639
  · exact B2102643
  · exact B2102647
  · exact B2102651
  · exact B2102655
  · exact B2102659
  · exact B2102663
  · exact B2102667
  · exact B2102671
  · exact B2102675
  · exact B2102679
  · exact B2102683
  · exact B2102687
  · exact B2102691
  · exact B2102695
  · exact B2102699
  · exact B2102703
  · exact B2102707
  · exact B2102711
  · exact B2102715
  · exact B2102719
  · exact B2102723
  · exact B2102727
  · exact B2102731
  · exact B2102735
  · exact B2102739
  · exact B2102743
  · exact B2102747
  · exact B2102751
  · exact B2102755
  · exact B2102759
  · exact B2102763
  · exact B2102767
  · exact B2102771
  · exact B2102775
  · exact B2102779
  · exact B2102783
  · exact B2102787
  · exact B2102791
  · exact B2102795
  · exact B2102799
  · exact B2102803
  · exact B2102807
  · exact B2102811
  · exact B2102815
  · exact B2102819
  · exact B2102823
  · exact B2102827
  · exact B2102831
  · exact B2102835
  · exact B2102839
  · exact B2102843
  · exact B2102847
  · exact B2102851
  · exact B2102855
  · exact B2102859
  · exact B2102863
  · exact B2102867
  · exact B2102871
  · exact B2102875
  · exact B2102879
  · exact B2102883
  · exact B2102887
  · exact B2102891
  · exact B2102895
  · exact B2102899
  · exact B2102903
  · exact B2102907
  · exact B2102911
  · exact B2102915
  · exact B2102919
  · exact B2102923
  · exact B2102927
  · exact B2102931
  · exact B2102935
  · exact B2102939
  · exact B2102943
  · exact B2102947
  · exact B2102951
  · exact B2102955
  · exact B2102959
  · exact B2102963
  · exact B2102967
  · exact B2102971
  · exact B2102975
  · exact B2102979
  · exact B2102983
  · exact B2102987
  · exact B2102991
  · exact B2102995
  · exact B2102999
  · exact B2103003
  · exact B2103007
  · exact B2103011
  · exact B2103015
  · exact B2103019
  · exact B2103023
  · exact B2103027
  · exact B2103031
  · exact B2103035
  · exact B2103039
  · exact B2103043
  · exact B2103047
  · exact B2103051
  · exact B2103055
  · exact B2103059
  · exact B2103063
  · exact B2103067
  · exact B2103071
  · exact B2103075
  · exact B2103079
  · exact B2103083
  · exact B2103087
  · exact B2103091
  · exact B2103095
  · exact B2103099
  · exact B2103103
  · exact B2103107
  · exact B2103111
  · exact B2103115
  · exact B2103119
  · exact B2103123
  · exact B2103127
  · exact B2103131
  · exact B2103135
  · exact B2103139
  · exact B2103143
  · exact B2103147
  · exact B2103151
  · exact B2103155
  · exact B2103159
  · exact B2103163
  · exact B2103167
  · exact B2103171
  · exact B2103175
  · exact B2103179
  · exact B2103183
  · exact B2103187
  · exact B2103191
  · exact B2103195
  · exact B2103199
  · exact B2103203
  · exact B2103207
  · exact B2103211
  · exact B2103215
  · exact B2103219
  · exact B2103223
  · exact B2103227
  · exact B2103231
  · exact B2103235
  · exact B2103239
  · exact B2103243
  · exact B2103247
  · exact B2103251
  · exact B2103255
  · exact B2103259
  · exact B2103263
  · exact B2103267
  · exact B2103271
  · exact B2103275
  · exact B2103279
  · exact B2103283
  · exact B2103287
  · exact B2103291
  · exact B2103295
  · exact B2103299
  · exact B2103303
  · exact B2103307
  · exact B2103311
  · exact B2103315
  · exact B2103319
  · exact B2103323
  · exact B2103327
  · exact B2103331
  · exact B2103335
  · exact B2103339
  · exact B2103343
  · exact B2103347
  · exact B2103351
  · exact B2103355
  · exact B2103359
  · exact B2103363
  · exact B2103367
  · exact B2103371
  · exact B2103375
  · exact B2103379
  · exact B2103383
  · exact B2103387
  · exact B2103391
  · exact B2103395
  · exact B2103399
  · exact B2103403
  · exact B2103407
  · exact B2103411
  · exact B2103415
  · exact B2103419
  · exact B2103423
  · exact B2103427
  · exact B2103431
  · exact B2103435
theorem solution (m : ℕ) (hlo : 2101435 ≤ m) (hhi : m ≤ 2103435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 525358 ≤ j := by omega
    have hj2 : j ≤ 525858 := by omega
    have hb : Blo 2101435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
