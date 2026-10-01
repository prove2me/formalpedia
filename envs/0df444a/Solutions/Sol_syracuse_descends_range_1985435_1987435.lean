-- Prove2me | solution 1 for syracuse_descends_range_1985435_1987435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:19.073503+00:00
-- url     : https://prove2.me/submissions/7e4a573a-3762-4000-9e2d-c8e62766b50f

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

theorem B7538453 : Blo 1985435 7538453 := bbase (se 6 (by rfl) ⟨176682, by rfl⟩ : syracuseStep 7538453 = 353365) (by norm_num)
theorem B5025635 : Blo 1985435 5025635 := bstep (se 1 (by rfl) ⟨3769226, by rfl⟩ : syracuseStep 5025635 = 7538453) B7538453
theorem B3350423 : Blo 1985435 3350423 := bstep (se 1 (by rfl) ⟨2512817, by rfl⟩ : syracuseStep 3350423 = 5025635) B5025635
theorem B2233615 : Blo 1985435 2233615 := bstep (se 1 (by rfl) ⟨1675211, by rfl⟩ : syracuseStep 2233615 = 3350423) B3350423
theorem B2978153 : Blo 1985435 2978153 := bstep (se 2 (by rfl) ⟨1116807, by rfl⟩ : syracuseStep 2978153 = 2233615) B2233615
theorem B1985435 : Blo 1985435 1985435 := bstep (se 1 (by rfl) ⟨1489076, by rfl⟩ : syracuseStep 1985435 = 2978153) B2978153
theorem B11307701 : Blo 1985435 11307701 := bbase (se 5 (by rfl) ⟨530048, by rfl⟩ : syracuseStep 11307701 = 1060097) (by norm_num)
theorem B7538467 : Blo 1985435 7538467 := bstep (se 1 (by rfl) ⟨5653850, by rfl⟩ : syracuseStep 7538467 = 11307701) B11307701
theorem B10051289 : Blo 1985435 10051289 := bstep (se 2 (by rfl) ⟨3769233, by rfl⟩ : syracuseStep 10051289 = 7538467) B7538467
theorem B6700859 : Blo 1985435 6700859 := bstep (se 1 (by rfl) ⟨5025644, by rfl⟩ : syracuseStep 6700859 = 10051289) B10051289
theorem B4467239 : Blo 1985435 4467239 := bstep (se 1 (by rfl) ⟨3350429, by rfl⟩ : syracuseStep 4467239 = 6700859) B6700859
theorem B2978159 : Blo 1985435 2978159 := bstep (se 1 (by rfl) ⟨2233619, by rfl⟩ : syracuseStep 2978159 = 4467239) B4467239
theorem B1985439 : Blo 1985435 1985439 := bstep (se 1 (by rfl) ⟨1489079, by rfl⟩ : syracuseStep 1985439 = 2978159) B2978159
theorem B2978165 : Blo 1985435 2978165 := bbase (se 5 (by rfl) ⟨139601, by rfl⟩ : syracuseStep 2978165 = 279203) (by norm_num)
theorem B1985443 : Blo 1985435 1985443 := bstep (se 1 (by rfl) ⟨1489082, by rfl⟩ : syracuseStep 1985443 = 2978165) B2978165
theorem B2385229 : Blo 1985435 2385229 := bbase (se 3 (by rfl) ⟨447230, by rfl⟩ : syracuseStep 2385229 = 894461) (by norm_num)
theorem B3180305 : Blo 1985435 3180305 := bstep (se 2 (by rfl) ⟨1192614, by rfl⟩ : syracuseStep 3180305 = 2385229) B2385229
theorem B2120203 : Blo 1985435 2120203 := bstep (se 1 (by rfl) ⟨1590152, by rfl⟩ : syracuseStep 2120203 = 3180305) B3180305
theorem B2826937 : Blo 1985435 2826937 := bstep (se 2 (by rfl) ⟨1060101, by rfl⟩ : syracuseStep 2826937 = 2120203) B2120203
theorem B3769249 : Blo 1985435 3769249 := bstep (se 2 (by rfl) ⟨1413468, by rfl⟩ : syracuseStep 3769249 = 2826937) B2826937
theorem B5025665 : Blo 1985435 5025665 := bstep (se 2 (by rfl) ⟨1884624, by rfl⟩ : syracuseStep 5025665 = 3769249) B3769249
theorem B3350443 : Blo 1985435 3350443 := bstep (se 1 (by rfl) ⟨2512832, by rfl⟩ : syracuseStep 3350443 = 5025665) B5025665
theorem B4467257 : Blo 1985435 4467257 := bstep (se 2 (by rfl) ⟨1675221, by rfl⟩ : syracuseStep 4467257 = 3350443) B3350443
theorem B2978171 : Blo 1985435 2978171 := bstep (se 1 (by rfl) ⟨2233628, by rfl⟩ : syracuseStep 2978171 = 4467257) B4467257
theorem B1985447 : Blo 1985435 1985447 := bstep (se 1 (by rfl) ⟨1489085, by rfl⟩ : syracuseStep 1985447 = 2978171) B2978171
theorem B2233633 : Blo 1985435 2233633 := bbase (se 2 (by rfl) ⟨837612, by rfl⟩ : syracuseStep 2233633 = 1675225) (by norm_num)
theorem B2978177 : Blo 1985435 2978177 := bstep (se 2 (by rfl) ⟨1116816, by rfl⟩ : syracuseStep 2978177 = 2233633) B2233633
theorem B1985451 : Blo 1985435 1985451 := bstep (se 1 (by rfl) ⟨1489088, by rfl⟩ : syracuseStep 1985451 = 2978177) B2978177
theorem B5025685 : Blo 1985435 5025685 := bbase (se 6 (by rfl) ⟨117789, by rfl⟩ : syracuseStep 5025685 = 235579) (by norm_num)
theorem B6700913 : Blo 1985435 6700913 := bstep (se 2 (by rfl) ⟨2512842, by rfl⟩ : syracuseStep 6700913 = 5025685) B5025685
theorem B4467275 : Blo 1985435 4467275 := bstep (se 1 (by rfl) ⟨3350456, by rfl⟩ : syracuseStep 4467275 = 6700913) B6700913
theorem B2978183 : Blo 1985435 2978183 := bstep (se 1 (by rfl) ⟨2233637, by rfl⟩ : syracuseStep 2978183 = 4467275) B4467275
theorem B1985455 : Blo 1985435 1985455 := bstep (se 1 (by rfl) ⟨1489091, by rfl⟩ : syracuseStep 1985455 = 2978183) B2978183
theorem B2978189 : Blo 1985435 2978189 := bbase (se 3 (by rfl) ⟨558410, by rfl⟩ : syracuseStep 2978189 = 1116821) (by norm_num)
theorem B1985459 : Blo 1985435 1985459 := bstep (se 1 (by rfl) ⟨1489094, by rfl⟩ : syracuseStep 1985459 = 2978189) B2978189
theorem B4467293 : Blo 1985435 4467293 := bbase (se 3 (by rfl) ⟨837617, by rfl⟩ : syracuseStep 4467293 = 1675235) (by norm_num)
theorem B2978195 : Blo 1985435 2978195 := bstep (se 1 (by rfl) ⟨2233646, by rfl⟩ : syracuseStep 2978195 = 4467293) B4467293
theorem B1985463 : Blo 1985435 1985463 := bstep (se 1 (by rfl) ⟨1489097, by rfl⟩ : syracuseStep 1985463 = 2978195) B2978195
theorem B3350477 : Blo 1985435 3350477 := bbase (se 3 (by rfl) ⟨628214, by rfl⟩ : syracuseStep 3350477 = 1256429) (by norm_num)
theorem B2233651 : Blo 1985435 2233651 := bstep (se 1 (by rfl) ⟨1675238, by rfl⟩ : syracuseStep 2233651 = 3350477) B3350477
theorem B2978201 : Blo 1985435 2978201 := bstep (se 2 (by rfl) ⟨1116825, by rfl⟩ : syracuseStep 2978201 = 2233651) B2233651
theorem B1985467 : Blo 1985435 1985467 := bstep (se 1 (by rfl) ⟨1489100, by rfl⟩ : syracuseStep 1985467 = 2978201) B2978201
theorem B14311541 : Blo 1985435 14311541 := bbase (se 5 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 14311541 = 1341707) (by norm_num)
theorem B9541027 : Blo 1985435 9541027 := bstep (se 1 (by rfl) ⟨7155770, by rfl⟩ : syracuseStep 9541027 = 14311541) B14311541
theorem B12721369 : Blo 1985435 12721369 := bstep (se 2 (by rfl) ⟨4770513, by rfl⟩ : syracuseStep 12721369 = 9541027) B9541027
theorem B16961825 : Blo 1985435 16961825 := bstep (se 2 (by rfl) ⟨6360684, by rfl⟩ : syracuseStep 16961825 = 12721369) B12721369
theorem B11307883 : Blo 1985435 11307883 := bstep (se 1 (by rfl) ⟨8480912, by rfl⟩ : syracuseStep 11307883 = 16961825) B16961825
theorem B15077177 : Blo 1985435 15077177 := bstep (se 2 (by rfl) ⟨5653941, by rfl⟩ : syracuseStep 15077177 = 11307883) B11307883
theorem B10051451 : Blo 1985435 10051451 := bstep (se 1 (by rfl) ⟨7538588, by rfl⟩ : syracuseStep 10051451 = 15077177) B15077177
theorem B6700967 : Blo 1985435 6700967 := bstep (se 1 (by rfl) ⟨5025725, by rfl⟩ : syracuseStep 6700967 = 10051451) B10051451
theorem B4467311 : Blo 1985435 4467311 := bstep (se 1 (by rfl) ⟨3350483, by rfl⟩ : syracuseStep 4467311 = 6700967) B6700967
theorem B2978207 : Blo 1985435 2978207 := bstep (se 1 (by rfl) ⟨2233655, by rfl⟩ : syracuseStep 2978207 = 4467311) B4467311
theorem B1985471 : Blo 1985435 1985471 := bstep (se 1 (by rfl) ⟨1489103, by rfl⟩ : syracuseStep 1985471 = 2978207) B2978207
theorem B2978213 : Blo 1985435 2978213 := bbase (se 4 (by rfl) ⟨279207, by rfl⟩ : syracuseStep 2978213 = 558415) (by norm_num)
theorem B1985475 : Blo 1985435 1985475 := bstep (se 1 (by rfl) ⟨1489106, by rfl⟩ : syracuseStep 1985475 = 2978213) B2978213
theorem B2512873 : Blo 1985435 2512873 := bbase (se 2 (by rfl) ⟨942327, by rfl⟩ : syracuseStep 2512873 = 1884655) (by norm_num)
theorem B3350497 : Blo 1985435 3350497 := bstep (se 2 (by rfl) ⟨1256436, by rfl⟩ : syracuseStep 3350497 = 2512873) B2512873
theorem B4467329 : Blo 1985435 4467329 := bstep (se 2 (by rfl) ⟨1675248, by rfl⟩ : syracuseStep 4467329 = 3350497) B3350497
theorem B2978219 : Blo 1985435 2978219 := bstep (se 1 (by rfl) ⟨2233664, by rfl⟩ : syracuseStep 2978219 = 4467329) B4467329
theorem B1985479 : Blo 1985435 1985479 := bstep (se 1 (by rfl) ⟨1489109, by rfl⟩ : syracuseStep 1985479 = 2978219) B2978219
theorem B2233669 : Blo 1985435 2233669 := bbase (se 4 (by rfl) ⟨209406, by rfl⟩ : syracuseStep 2233669 = 418813) (by norm_num)
theorem B2978225 : Blo 1985435 2978225 := bstep (se 2 (by rfl) ⟨1116834, by rfl⟩ : syracuseStep 2978225 = 2233669) B2233669
theorem B1985483 : Blo 1985435 1985483 := bstep (se 1 (by rfl) ⟨1489112, by rfl⟩ : syracuseStep 1985483 = 2978225) B2978225
theorem B3769325 : Blo 1985435 3769325 := bbase (se 3 (by rfl) ⟨706748, by rfl⟩ : syracuseStep 3769325 = 1413497) (by norm_num)
theorem B2512883 : Blo 1985435 2512883 := bstep (se 1 (by rfl) ⟨1884662, by rfl⟩ : syracuseStep 2512883 = 3769325) B3769325
theorem B6701021 : Blo 1985435 6701021 := bstep (se 3 (by rfl) ⟨1256441, by rfl⟩ : syracuseStep 6701021 = 2512883) B2512883
theorem B4467347 : Blo 1985435 4467347 := bstep (se 1 (by rfl) ⟨3350510, by rfl⟩ : syracuseStep 4467347 = 6701021) B6701021
theorem B2978231 : Blo 1985435 2978231 := bstep (se 1 (by rfl) ⟨2233673, by rfl⟩ : syracuseStep 2978231 = 4467347) B4467347
theorem B1985487 : Blo 1985435 1985487 := bstep (se 1 (by rfl) ⟨1489115, by rfl⟩ : syracuseStep 1985487 = 2978231) B2978231
theorem B2978237 : Blo 1985435 2978237 := bbase (se 3 (by rfl) ⟨558419, by rfl⟩ : syracuseStep 2978237 = 1116839) (by norm_num)
theorem B1985491 : Blo 1985435 1985491 := bstep (se 1 (by rfl) ⟨1489118, by rfl⟩ : syracuseStep 1985491 = 2978237) B2978237
theorem B4467365 : Blo 1985435 4467365 := bbase (se 4 (by rfl) ⟨418815, by rfl⟩ : syracuseStep 4467365 = 837631) (by norm_num)
theorem B2978243 : Blo 1985435 2978243 := bstep (se 1 (by rfl) ⟨2233682, by rfl⟩ : syracuseStep 2978243 = 4467365) B4467365
theorem B1985495 : Blo 1985435 1985495 := bstep (se 1 (by rfl) ⟨1489121, by rfl⟩ : syracuseStep 1985495 = 2978243) B2978243
theorem B5025797 : Blo 1985435 5025797 := bbase (se 4 (by rfl) ⟨471168, by rfl⟩ : syracuseStep 5025797 = 942337) (by norm_num)
theorem B3350531 : Blo 1985435 3350531 := bstep (se 1 (by rfl) ⟨2512898, by rfl⟩ : syracuseStep 3350531 = 5025797) B5025797
theorem B2233687 : Blo 1985435 2233687 := bstep (se 1 (by rfl) ⟨1675265, by rfl⟩ : syracuseStep 2233687 = 3350531) B3350531
theorem B2978249 : Blo 1985435 2978249 := bstep (se 2 (by rfl) ⟨1116843, by rfl⟩ : syracuseStep 2978249 = 2233687) B2233687
theorem B1985499 : Blo 1985435 1985499 := bstep (se 1 (by rfl) ⟨1489124, by rfl⟩ : syracuseStep 1985499 = 2978249) B2978249
theorem B4240525 : Blo 1985435 4240525 := bbase (se 3 (by rfl) ⟨795098, by rfl⟩ : syracuseStep 4240525 = 1590197) (by norm_num)
theorem B5654033 : Blo 1985435 5654033 := bstep (se 2 (by rfl) ⟨2120262, by rfl⟩ : syracuseStep 5654033 = 4240525) B4240525
theorem B3769355 : Blo 1985435 3769355 := bstep (se 1 (by rfl) ⟨2827016, by rfl⟩ : syracuseStep 3769355 = 5654033) B5654033
theorem B10051613 : Blo 1985435 10051613 := bstep (se 3 (by rfl) ⟨1884677, by rfl⟩ : syracuseStep 10051613 = 3769355) B3769355
theorem B6701075 : Blo 1985435 6701075 := bstep (se 1 (by rfl) ⟨5025806, by rfl⟩ : syracuseStep 6701075 = 10051613) B10051613
theorem B4467383 : Blo 1985435 4467383 := bstep (se 1 (by rfl) ⟨3350537, by rfl⟩ : syracuseStep 4467383 = 6701075) B6701075
theorem B2978255 : Blo 1985435 2978255 := bstep (se 1 (by rfl) ⟨2233691, by rfl⟩ : syracuseStep 2978255 = 4467383) B4467383
theorem B1985503 : Blo 1985435 1985503 := bstep (se 1 (by rfl) ⟨1489127, by rfl⟩ : syracuseStep 1985503 = 2978255) B2978255
theorem B2978261 : Blo 1985435 2978261 := bbase (se 7 (by rfl) ⟨34901, by rfl⟩ : syracuseStep 2978261 = 69803) (by norm_num)
theorem B1985507 : Blo 1985435 1985507 := bstep (se 1 (by rfl) ⟨1489130, by rfl⟩ : syracuseStep 1985507 = 2978261) B2978261
theorem B7538741 : Blo 1985435 7538741 := bbase (se 5 (by rfl) ⟨353378, by rfl⟩ : syracuseStep 7538741 = 706757) (by norm_num)
theorem B5025827 : Blo 1985435 5025827 := bstep (se 1 (by rfl) ⟨3769370, by rfl⟩ : syracuseStep 5025827 = 7538741) B7538741
theorem B3350551 : Blo 1985435 3350551 := bstep (se 1 (by rfl) ⟨2512913, by rfl⟩ : syracuseStep 3350551 = 5025827) B5025827
theorem B4467401 : Blo 1985435 4467401 := bstep (se 2 (by rfl) ⟨1675275, by rfl⟩ : syracuseStep 4467401 = 3350551) B3350551
theorem B2978267 : Blo 1985435 2978267 := bstep (se 1 (by rfl) ⟨2233700, by rfl⟩ : syracuseStep 2978267 = 4467401) B4467401
theorem B1985511 : Blo 1985435 1985511 := bstep (se 1 (by rfl) ⟨1489133, by rfl⟩ : syracuseStep 1985511 = 2978267) B2978267
theorem B2233705 : Blo 1985435 2233705 := bbase (se 2 (by rfl) ⟨837639, by rfl⟩ : syracuseStep 2233705 = 1675279) (by norm_num)
theorem B2978273 : Blo 1985435 2978273 := bstep (se 2 (by rfl) ⟨1116852, by rfl⟩ : syracuseStep 2978273 = 2233705) B2233705
theorem B1985515 : Blo 1985435 1985515 := bstep (se 1 (by rfl) ⟨1489136, by rfl⟩ : syracuseStep 1985515 = 2978273) B2978273
theorem B6037829 : Blo 1985435 6037829 := bbase (se 4 (by rfl) ⟨566046, by rfl⟩ : syracuseStep 6037829 = 1132093) (by norm_num)
theorem B4025219 : Blo 1985435 4025219 := bstep (se 1 (by rfl) ⟨3018914, by rfl⟩ : syracuseStep 4025219 = 6037829) B6037829
theorem B10733917 : Blo 1985435 10733917 := bstep (se 3 (by rfl) ⟨2012609, by rfl⟩ : syracuseStep 10733917 = 4025219) B4025219
theorem B14311889 : Blo 1985435 14311889 := bstep (se 2 (by rfl) ⟨5366958, by rfl⟩ : syracuseStep 14311889 = 10733917) B10733917
theorem B9541259 : Blo 1985435 9541259 := bstep (se 1 (by rfl) ⟨7155944, by rfl⟩ : syracuseStep 9541259 = 14311889) B14311889
theorem B6360839 : Blo 1985435 6360839 := bstep (se 1 (by rfl) ⟨4770629, by rfl⟩ : syracuseStep 6360839 = 9541259) B9541259
theorem B4240559 : Blo 1985435 4240559 := bstep (se 1 (by rfl) ⟨3180419, by rfl⟩ : syracuseStep 4240559 = 6360839) B6360839
theorem B11308157 : Blo 1985435 11308157 := bstep (se 3 (by rfl) ⟨2120279, by rfl⟩ : syracuseStep 11308157 = 4240559) B4240559
theorem B7538771 : Blo 1985435 7538771 := bstep (se 1 (by rfl) ⟨5654078, by rfl⟩ : syracuseStep 7538771 = 11308157) B11308157
theorem B5025847 : Blo 1985435 5025847 := bstep (se 1 (by rfl) ⟨3769385, by rfl⟩ : syracuseStep 5025847 = 7538771) B7538771
theorem B6701129 : Blo 1985435 6701129 := bstep (se 2 (by rfl) ⟨2512923, by rfl⟩ : syracuseStep 6701129 = 5025847) B5025847
theorem B4467419 : Blo 1985435 4467419 := bstep (se 1 (by rfl) ⟨3350564, by rfl⟩ : syracuseStep 4467419 = 6701129) B6701129
theorem B2978279 : Blo 1985435 2978279 := bstep (se 1 (by rfl) ⟨2233709, by rfl⟩ : syracuseStep 2978279 = 4467419) B4467419
theorem B1985519 : Blo 1985435 1985519 := bstep (se 1 (by rfl) ⟨1489139, by rfl⟩ : syracuseStep 1985519 = 2978279) B2978279
theorem B2978285 : Blo 1985435 2978285 := bbase (se 3 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 2978285 = 1116857) (by norm_num)
theorem B1985523 : Blo 1985435 1985523 := bstep (se 1 (by rfl) ⟨1489142, by rfl⟩ : syracuseStep 1985523 = 2978285) B2978285
theorem B4467437 : Blo 1985435 4467437 := bbase (se 3 (by rfl) ⟨837644, by rfl⟩ : syracuseStep 4467437 = 1675289) (by norm_num)
theorem B2978291 : Blo 1985435 2978291 := bstep (se 1 (by rfl) ⟨2233718, by rfl⟩ : syracuseStep 2978291 = 4467437) B4467437
theorem B1985527 : Blo 1985435 1985527 := bstep (se 1 (by rfl) ⟨1489145, by rfl⟩ : syracuseStep 1985527 = 2978291) B2978291
theorem B2120293 : Blo 1985435 2120293 := bbase (se 4 (by rfl) ⟨198777, by rfl⟩ : syracuseStep 2120293 = 397555) (by norm_num)
theorem B2827057 : Blo 1985435 2827057 := bstep (se 2 (by rfl) ⟨1060146, by rfl⟩ : syracuseStep 2827057 = 2120293) B2120293
theorem B3769409 : Blo 1985435 3769409 := bstep (se 2 (by rfl) ⟨1413528, by rfl⟩ : syracuseStep 3769409 = 2827057) B2827057
theorem B2512939 : Blo 1985435 2512939 := bstep (se 1 (by rfl) ⟨1884704, by rfl⟩ : syracuseStep 2512939 = 3769409) B3769409
theorem B3350585 : Blo 1985435 3350585 := bstep (se 2 (by rfl) ⟨1256469, by rfl⟩ : syracuseStep 3350585 = 2512939) B2512939
theorem B2233723 : Blo 1985435 2233723 := bstep (se 1 (by rfl) ⟨1675292, by rfl⟩ : syracuseStep 2233723 = 3350585) B3350585
theorem B2978297 : Blo 1985435 2978297 := bstep (se 2 (by rfl) ⟨1116861, by rfl⟩ : syracuseStep 2978297 = 2233723) B2233723
theorem B1985531 : Blo 1985435 1985531 := bstep (se 1 (by rfl) ⟨1489148, by rfl⟩ : syracuseStep 1985531 = 2978297) B2978297
theorem B8050501 : Blo 1985435 8050501 := bbase (se 4 (by rfl) ⟨754734, by rfl⟩ : syracuseStep 8050501 = 1509469) (by norm_num)
theorem B10734001 : Blo 1985435 10734001 := bstep (se 2 (by rfl) ⟨4025250, by rfl⟩ : syracuseStep 10734001 = 8050501) B8050501
theorem B57248005 : Blo 1985435 57248005 := bstep (se 4 (by rfl) ⟨5367000, by rfl⟩ : syracuseStep 57248005 = 10734001) B10734001
theorem B76330673 : Blo 1985435 76330673 := bstep (se 2 (by rfl) ⟨28624002, by rfl⟩ : syracuseStep 76330673 = 57248005) B57248005
theorem B50887115 : Blo 1985435 50887115 := bstep (se 1 (by rfl) ⟨38165336, by rfl⟩ : syracuseStep 50887115 = 76330673) B76330673
theorem B33924743 : Blo 1985435 33924743 := bstep (se 1 (by rfl) ⟨25443557, by rfl⟩ : syracuseStep 33924743 = 50887115) B50887115
theorem B22616495 : Blo 1985435 22616495 := bstep (se 1 (by rfl) ⟨16962371, by rfl⟩ : syracuseStep 22616495 = 33924743) B33924743
theorem B15077663 : Blo 1985435 15077663 := bstep (se 1 (by rfl) ⟨11308247, by rfl⟩ : syracuseStep 15077663 = 22616495) B22616495
theorem B10051775 : Blo 1985435 10051775 := bstep (se 1 (by rfl) ⟨7538831, by rfl⟩ : syracuseStep 10051775 = 15077663) B15077663
theorem B6701183 : Blo 1985435 6701183 := bstep (se 1 (by rfl) ⟨5025887, by rfl⟩ : syracuseStep 6701183 = 10051775) B10051775
theorem B4467455 : Blo 1985435 4467455 := bstep (se 1 (by rfl) ⟨3350591, by rfl⟩ : syracuseStep 4467455 = 6701183) B6701183
theorem B2978303 : Blo 1985435 2978303 := bstep (se 1 (by rfl) ⟨2233727, by rfl⟩ : syracuseStep 2978303 = 4467455) B4467455
theorem B1985535 : Blo 1985435 1985535 := bstep (se 1 (by rfl) ⟨1489151, by rfl⟩ : syracuseStep 1985535 = 2978303) B2978303
theorem B2978309 : Blo 1985435 2978309 := bbase (se 4 (by rfl) ⟨279216, by rfl⟩ : syracuseStep 2978309 = 558433) (by norm_num)
theorem B1985539 : Blo 1985435 1985539 := bstep (se 1 (by rfl) ⟨1489154, by rfl⟩ : syracuseStep 1985539 = 2978309) B2978309
theorem B3350605 : Blo 1985435 3350605 := bbase (se 3 (by rfl) ⟨628238, by rfl⟩ : syracuseStep 3350605 = 1256477) (by norm_num)
theorem B4467473 : Blo 1985435 4467473 := bstep (se 2 (by rfl) ⟨1675302, by rfl⟩ : syracuseStep 4467473 = 3350605) B3350605
theorem B2978315 : Blo 1985435 2978315 := bstep (se 1 (by rfl) ⟨2233736, by rfl⟩ : syracuseStep 2978315 = 4467473) B4467473
theorem B1985543 : Blo 1985435 1985543 := bstep (se 1 (by rfl) ⟨1489157, by rfl⟩ : syracuseStep 1985543 = 2978315) B2978315
theorem B2233741 : Blo 1985435 2233741 := bbase (se 3 (by rfl) ⟨418826, by rfl⟩ : syracuseStep 2233741 = 837653) (by norm_num)
theorem B2978321 : Blo 1985435 2978321 := bstep (se 2 (by rfl) ⟨1116870, by rfl⟩ : syracuseStep 2978321 = 2233741) B2233741
theorem B1985547 : Blo 1985435 1985547 := bstep (se 1 (by rfl) ⟨1489160, by rfl⟩ : syracuseStep 1985547 = 2978321) B2978321
theorem B6701237 : Blo 1985435 6701237 := bbase (se 5 (by rfl) ⟨314120, by rfl⟩ : syracuseStep 6701237 = 628241) (by norm_num)
theorem B4467491 : Blo 1985435 4467491 := bstep (se 1 (by rfl) ⟨3350618, by rfl⟩ : syracuseStep 4467491 = 6701237) B6701237
theorem B2978327 : Blo 1985435 2978327 := bstep (se 1 (by rfl) ⟨2233745, by rfl⟩ : syracuseStep 2978327 = 4467491) B4467491
theorem B1985551 : Blo 1985435 1985551 := bstep (se 1 (by rfl) ⟨1489163, by rfl⟩ : syracuseStep 1985551 = 2978327) B2978327
theorem B2978333 : Blo 1985435 2978333 := bbase (se 3 (by rfl) ⟨558437, by rfl⟩ : syracuseStep 2978333 = 1116875) (by norm_num)
theorem B1985555 : Blo 1985435 1985555 := bstep (se 1 (by rfl) ⟨1489166, by rfl⟩ : syracuseStep 1985555 = 2978333) B2978333
theorem B4467509 : Blo 1985435 4467509 := bbase (se 5 (by rfl) ⟨209414, by rfl⟩ : syracuseStep 4467509 = 418829) (by norm_num)
theorem B2978339 : Blo 1985435 2978339 := bstep (se 1 (by rfl) ⟨2233754, by rfl⟩ : syracuseStep 2978339 = 4467509) B4467509
theorem B1985559 : Blo 1985435 1985559 := bstep (se 1 (by rfl) ⟨1489169, by rfl⟩ : syracuseStep 1985559 = 2978339) B2978339
theorem B48303701 : Blo 1985435 48303701 := bbase (se 8 (by rfl) ⟨283029, by rfl⟩ : syracuseStep 48303701 = 566059) (by norm_num)
theorem B32202467 : Blo 1985435 32202467 := bstep (se 1 (by rfl) ⟨24151850, by rfl⟩ : syracuseStep 32202467 = 48303701) B48303701
theorem B21468311 : Blo 1985435 21468311 := bstep (se 1 (by rfl) ⟨16101233, by rfl⟩ : syracuseStep 21468311 = 32202467) B32202467
theorem B14312207 : Blo 1985435 14312207 := bstep (se 1 (by rfl) ⟨10734155, by rfl⟩ : syracuseStep 14312207 = 21468311) B21468311
theorem B9541471 : Blo 1985435 9541471 := bstep (se 1 (by rfl) ⟨7156103, by rfl⟩ : syracuseStep 9541471 = 14312207) B14312207
theorem B12721961 : Blo 1985435 12721961 := bstep (se 2 (by rfl) ⟨4770735, by rfl⟩ : syracuseStep 12721961 = 9541471) B9541471
theorem B8481307 : Blo 1985435 8481307 := bstep (se 1 (by rfl) ⟨6360980, by rfl⟩ : syracuseStep 8481307 = 12721961) B12721961
theorem B11308409 : Blo 1985435 11308409 := bstep (se 2 (by rfl) ⟨4240653, by rfl⟩ : syracuseStep 11308409 = 8481307) B8481307
theorem B7538939 : Blo 1985435 7538939 := bstep (se 1 (by rfl) ⟨5654204, by rfl⟩ : syracuseStep 7538939 = 11308409) B11308409
theorem B5025959 : Blo 1985435 5025959 := bstep (se 1 (by rfl) ⟨3769469, by rfl⟩ : syracuseStep 5025959 = 7538939) B7538939
theorem B3350639 : Blo 1985435 3350639 := bstep (se 1 (by rfl) ⟨2512979, by rfl⟩ : syracuseStep 3350639 = 5025959) B5025959
theorem B2233759 : Blo 1985435 2233759 := bstep (se 1 (by rfl) ⟨1675319, by rfl⟩ : syracuseStep 2233759 = 3350639) B3350639
theorem B2978345 : Blo 1985435 2978345 := bstep (se 2 (by rfl) ⟨1116879, by rfl⟩ : syracuseStep 2978345 = 2233759) B2233759
theorem B1985563 : Blo 1985435 1985563 := bstep (se 1 (by rfl) ⟨1489172, by rfl⟩ : syracuseStep 1985563 = 2978345) B2978345
theorem B7156117 : Blo 1985435 7156117 := bbase (se 6 (by rfl) ⟨167721, by rfl⟩ : syracuseStep 7156117 = 335443) (by norm_num)
theorem B9541489 : Blo 1985435 9541489 := bstep (se 2 (by rfl) ⟨3578058, by rfl⟩ : syracuseStep 9541489 = 7156117) B7156117
theorem B12721985 : Blo 1985435 12721985 := bstep (se 2 (by rfl) ⟨4770744, by rfl⟩ : syracuseStep 12721985 = 9541489) B9541489
theorem B8481323 : Blo 1985435 8481323 := bstep (se 1 (by rfl) ⟨6360992, by rfl⟩ : syracuseStep 8481323 = 12721985) B12721985
theorem B5654215 : Blo 1985435 5654215 := bstep (se 1 (by rfl) ⟨4240661, by rfl⟩ : syracuseStep 5654215 = 8481323) B8481323
theorem B7538953 : Blo 1985435 7538953 := bstep (se 2 (by rfl) ⟨2827107, by rfl⟩ : syracuseStep 7538953 = 5654215) B5654215
theorem B10051937 : Blo 1985435 10051937 := bstep (se 2 (by rfl) ⟨3769476, by rfl⟩ : syracuseStep 10051937 = 7538953) B7538953
theorem B6701291 : Blo 1985435 6701291 := bstep (se 1 (by rfl) ⟨5025968, by rfl⟩ : syracuseStep 6701291 = 10051937) B10051937
theorem B4467527 : Blo 1985435 4467527 := bstep (se 1 (by rfl) ⟨3350645, by rfl⟩ : syracuseStep 4467527 = 6701291) B6701291
theorem B2978351 : Blo 1985435 2978351 := bstep (se 1 (by rfl) ⟨2233763, by rfl⟩ : syracuseStep 2978351 = 4467527) B4467527
theorem B1985567 : Blo 1985435 1985567 := bstep (se 1 (by rfl) ⟨1489175, by rfl⟩ : syracuseStep 1985567 = 2978351) B2978351
theorem B2978357 : Blo 1985435 2978357 := bbase (se 5 (by rfl) ⟨139610, by rfl⟩ : syracuseStep 2978357 = 279221) (by norm_num)
theorem B1985571 : Blo 1985435 1985571 := bstep (se 1 (by rfl) ⟨1489178, by rfl⟩ : syracuseStep 1985571 = 2978357) B2978357
theorem B5025989 : Blo 1985435 5025989 := bbase (se 4 (by rfl) ⟨471186, by rfl⟩ : syracuseStep 5025989 = 942373) (by norm_num)
theorem B3350659 : Blo 1985435 3350659 := bstep (se 1 (by rfl) ⟨2512994, by rfl⟩ : syracuseStep 3350659 = 5025989) B5025989
theorem B4467545 : Blo 1985435 4467545 := bstep (se 2 (by rfl) ⟨1675329, by rfl⟩ : syracuseStep 4467545 = 3350659) B3350659
theorem B2978363 : Blo 1985435 2978363 := bstep (se 1 (by rfl) ⟨2233772, by rfl⟩ : syracuseStep 2978363 = 4467545) B4467545
theorem B1985575 : Blo 1985435 1985575 := bstep (se 1 (by rfl) ⟨1489181, by rfl⟩ : syracuseStep 1985575 = 2978363) B2978363
theorem B2233777 : Blo 1985435 2233777 := bbase (se 2 (by rfl) ⟨837666, by rfl⟩ : syracuseStep 2233777 = 1675333) (by norm_num)
theorem B2978369 : Blo 1985435 2978369 := bstep (se 2 (by rfl) ⟨1116888, by rfl⟩ : syracuseStep 2978369 = 2233777) B2233777
theorem B1985579 : Blo 1985435 1985579 := bstep (se 1 (by rfl) ⟨1489184, by rfl⟩ : syracuseStep 1985579 = 2978369) B2978369
theorem B5654261 : Blo 1985435 5654261 := bbase (se 5 (by rfl) ⟨265043, by rfl⟩ : syracuseStep 5654261 = 530087) (by norm_num)
theorem B3769507 : Blo 1985435 3769507 := bstep (se 1 (by rfl) ⟨2827130, by rfl⟩ : syracuseStep 3769507 = 5654261) B5654261
theorem B5026009 : Blo 1985435 5026009 := bstep (se 2 (by rfl) ⟨1884753, by rfl⟩ : syracuseStep 5026009 = 3769507) B3769507
theorem B6701345 : Blo 1985435 6701345 := bstep (se 2 (by rfl) ⟨2513004, by rfl⟩ : syracuseStep 6701345 = 5026009) B5026009
theorem B4467563 : Blo 1985435 4467563 := bstep (se 1 (by rfl) ⟨3350672, by rfl⟩ : syracuseStep 4467563 = 6701345) B6701345
theorem B2978375 : Blo 1985435 2978375 := bstep (se 1 (by rfl) ⟨2233781, by rfl⟩ : syracuseStep 2978375 = 4467563) B4467563
theorem B1985583 : Blo 1985435 1985583 := bstep (se 1 (by rfl) ⟨1489187, by rfl⟩ : syracuseStep 1985583 = 2978375) B2978375
theorem B2978381 : Blo 1985435 2978381 := bbase (se 3 (by rfl) ⟨558446, by rfl⟩ : syracuseStep 2978381 = 1116893) (by norm_num)
theorem B1985587 : Blo 1985435 1985587 := bstep (se 1 (by rfl) ⟨1489190, by rfl⟩ : syracuseStep 1985587 = 2978381) B2978381
theorem B4467581 : Blo 1985435 4467581 := bbase (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) (by norm_num)
theorem B2978387 : Blo 1985435 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B1985591 : Blo 1985435 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B3350693 : Blo 1985435 3350693 := bbase (se 4 (by rfl) ⟨314127, by rfl⟩ : syracuseStep 3350693 = 628255) (by norm_num)
theorem B2233795 : Blo 1985435 2233795 := bstep (se 1 (by rfl) ⟨1675346, by rfl⟩ : syracuseStep 2233795 = 3350693) B3350693
theorem B2978393 : Blo 1985435 2978393 := bstep (se 2 (by rfl) ⟨1116897, by rfl⟩ : syracuseStep 2978393 = 2233795) B2233795
theorem B1985595 : Blo 1985435 1985595 := bstep (se 1 (by rfl) ⟨1489196, by rfl⟩ : syracuseStep 1985595 = 2978393) B2978393
theorem B2120365 : Blo 1985435 2120365 := bbase (se 3 (by rfl) ⟨397568, by rfl⟩ : syracuseStep 2120365 = 795137) (by norm_num)
theorem B2827153 : Blo 1985435 2827153 := bstep (se 2 (by rfl) ⟨1060182, by rfl⟩ : syracuseStep 2827153 = 2120365) B2120365
theorem B15078149 : Blo 1985435 15078149 := bstep (se 4 (by rfl) ⟨1413576, by rfl⟩ : syracuseStep 15078149 = 2827153) B2827153
theorem B10052099 : Blo 1985435 10052099 := bstep (se 1 (by rfl) ⟨7539074, by rfl⟩ : syracuseStep 10052099 = 15078149) B15078149
theorem B6701399 : Blo 1985435 6701399 := bstep (se 1 (by rfl) ⟨5026049, by rfl⟩ : syracuseStep 6701399 = 10052099) B10052099
theorem B4467599 : Blo 1985435 4467599 := bstep (se 1 (by rfl) ⟨3350699, by rfl⟩ : syracuseStep 4467599 = 6701399) B6701399
theorem B2978399 : Blo 1985435 2978399 := bstep (se 1 (by rfl) ⟨2233799, by rfl⟩ : syracuseStep 2978399 = 4467599) B4467599
theorem B1985599 : Blo 1985435 1985599 := bstep (se 1 (by rfl) ⟨1489199, by rfl⟩ : syracuseStep 1985599 = 2978399) B2978399
theorem B2978405 : Blo 1985435 2978405 := bbase (se 4 (by rfl) ⟨279225, by rfl⟩ : syracuseStep 2978405 = 558451) (by norm_num)
theorem B1985603 : Blo 1985435 1985603 := bstep (se 1 (by rfl) ⟨1489202, by rfl⟩ : syracuseStep 1985603 = 2978405) B2978405
theorem B2827165 : Blo 1985435 2827165 := bbase (se 3 (by rfl) ⟨530093, by rfl⟩ : syracuseStep 2827165 = 1060187) (by norm_num)
theorem B3769553 : Blo 1985435 3769553 := bstep (se 2 (by rfl) ⟨1413582, by rfl⟩ : syracuseStep 3769553 = 2827165) B2827165
theorem B2513035 : Blo 1985435 2513035 := bstep (se 1 (by rfl) ⟨1884776, by rfl⟩ : syracuseStep 2513035 = 3769553) B3769553
theorem B3350713 : Blo 1985435 3350713 := bstep (se 2 (by rfl) ⟨1256517, by rfl⟩ : syracuseStep 3350713 = 2513035) B2513035
theorem B4467617 : Blo 1985435 4467617 := bstep (se 2 (by rfl) ⟨1675356, by rfl⟩ : syracuseStep 4467617 = 3350713) B3350713
theorem B2978411 : Blo 1985435 2978411 := bstep (se 1 (by rfl) ⟨2233808, by rfl⟩ : syracuseStep 2978411 = 4467617) B4467617
theorem B1985607 : Blo 1985435 1985607 := bstep (se 1 (by rfl) ⟨1489205, by rfl⟩ : syracuseStep 1985607 = 2978411) B2978411
theorem B2233813 : Blo 1985435 2233813 := bbase (se 7 (by rfl) ⟨26177, by rfl⟩ : syracuseStep 2233813 = 52355) (by norm_num)
theorem B2978417 : Blo 1985435 2978417 := bstep (se 2 (by rfl) ⟨1116906, by rfl⟩ : syracuseStep 2978417 = 2233813) B2233813
theorem B1985611 : Blo 1985435 1985611 := bstep (se 1 (by rfl) ⟨1489208, by rfl⟩ : syracuseStep 1985611 = 2978417) B2978417
theorem B2513045 : Blo 1985435 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B6701453 : Blo 1985435 6701453 := bstep (se 3 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 6701453 = 2513045) B2513045
theorem B4467635 : Blo 1985435 4467635 := bstep (se 1 (by rfl) ⟨3350726, by rfl⟩ : syracuseStep 4467635 = 6701453) B6701453
theorem B2978423 : Blo 1985435 2978423 := bstep (se 1 (by rfl) ⟨2233817, by rfl⟩ : syracuseStep 2978423 = 4467635) B4467635
theorem B1985615 : Blo 1985435 1985615 := bstep (se 1 (by rfl) ⟨1489211, by rfl⟩ : syracuseStep 1985615 = 2978423) B2978423
theorem B2978429 : Blo 1985435 2978429 := bbase (se 3 (by rfl) ⟨558455, by rfl⟩ : syracuseStep 2978429 = 1116911) (by norm_num)
theorem B1985619 : Blo 1985435 1985619 := bstep (se 1 (by rfl) ⟨1489214, by rfl⟩ : syracuseStep 1985619 = 2978429) B2978429
theorem B4467653 : Blo 1985435 4467653 := bbase (se 4 (by rfl) ⟨418842, by rfl⟩ : syracuseStep 4467653 = 837685) (by norm_num)
theorem B2978435 : Blo 1985435 2978435 := bstep (se 1 (by rfl) ⟨2233826, by rfl⟩ : syracuseStep 2978435 = 4467653) B4467653
theorem B1985623 : Blo 1985435 1985623 := bstep (se 1 (by rfl) ⟨1489217, by rfl⟩ : syracuseStep 1985623 = 2978435) B2978435
theorem B2385445 : Blo 1985435 2385445 := bbase (se 4 (by rfl) ⟨223635, by rfl⟩ : syracuseStep 2385445 = 447271) (by norm_num)
theorem B3180593 : Blo 1985435 3180593 := bstep (se 2 (by rfl) ⟨1192722, by rfl⟩ : syracuseStep 3180593 = 2385445) B2385445
theorem B8481581 : Blo 1985435 8481581 := bstep (se 3 (by rfl) ⟨1590296, by rfl⟩ : syracuseStep 8481581 = 3180593) B3180593
theorem B5654387 : Blo 1985435 5654387 := bstep (se 1 (by rfl) ⟨4240790, by rfl⟩ : syracuseStep 5654387 = 8481581) B8481581
theorem B3769591 : Blo 1985435 3769591 := bstep (se 1 (by rfl) ⟨2827193, by rfl⟩ : syracuseStep 3769591 = 5654387) B5654387
theorem B5026121 : Blo 1985435 5026121 := bstep (se 2 (by rfl) ⟨1884795, by rfl⟩ : syracuseStep 5026121 = 3769591) B3769591
theorem B3350747 : Blo 1985435 3350747 := bstep (se 1 (by rfl) ⟨2513060, by rfl⟩ : syracuseStep 3350747 = 5026121) B5026121
theorem B2233831 : Blo 1985435 2233831 := bstep (se 1 (by rfl) ⟨1675373, by rfl⟩ : syracuseStep 2233831 = 3350747) B3350747
theorem B2978441 : Blo 1985435 2978441 := bstep (se 2 (by rfl) ⟨1116915, by rfl⟩ : syracuseStep 2978441 = 2233831) B2233831
theorem B1985627 : Blo 1985435 1985627 := bstep (se 1 (by rfl) ⟨1489220, by rfl⟩ : syracuseStep 1985627 = 2978441) B2978441
theorem B10052261 : Blo 1985435 10052261 := bbase (se 4 (by rfl) ⟨942399, by rfl⟩ : syracuseStep 10052261 = 1884799) (by norm_num)
theorem B6701507 : Blo 1985435 6701507 := bstep (se 1 (by rfl) ⟨5026130, by rfl⟩ : syracuseStep 6701507 = 10052261) B10052261
theorem B4467671 : Blo 1985435 4467671 := bstep (se 1 (by rfl) ⟨3350753, by rfl⟩ : syracuseStep 4467671 = 6701507) B6701507
theorem B2978447 : Blo 1985435 2978447 := bstep (se 1 (by rfl) ⟨2233835, by rfl⟩ : syracuseStep 2978447 = 4467671) B4467671
theorem B1985631 : Blo 1985435 1985631 := bstep (se 1 (by rfl) ⟨1489223, by rfl⟩ : syracuseStep 1985631 = 2978447) B2978447
theorem B2978453 : Blo 1985435 2978453 := bbase (se 6 (by rfl) ⟨69807, by rfl⟩ : syracuseStep 2978453 = 139615) (by norm_num)
theorem B1985635 : Blo 1985435 1985635 := bstep (se 1 (by rfl) ⟨1489226, by rfl⟩ : syracuseStep 1985635 = 2978453) B2978453
theorem B3396485 : Blo 1985435 3396485 := bbase (se 4 (by rfl) ⟨318420, by rfl⟩ : syracuseStep 3396485 = 636841) (by norm_num)
theorem B2264323 : Blo 1985435 2264323 := bstep (se 1 (by rfl) ⟨1698242, by rfl⟩ : syracuseStep 2264323 = 3396485) B3396485
theorem B3019097 : Blo 1985435 3019097 := bstep (se 2 (by rfl) ⟨1132161, by rfl⟩ : syracuseStep 3019097 = 2264323) B2264323
theorem B2012731 : Blo 1985435 2012731 := bstep (se 1 (by rfl) ⟨1509548, by rfl⟩ : syracuseStep 2012731 = 3019097) B3019097
theorem B42938261 : Blo 1985435 42938261 := bstep (se 6 (by rfl) ⟨1006365, by rfl⟩ : syracuseStep 42938261 = 2012731) B2012731
theorem B28625507 : Blo 1985435 28625507 := bstep (se 1 (by rfl) ⟨21469130, by rfl⟩ : syracuseStep 28625507 = 42938261) B42938261
theorem B19083671 : Blo 1985435 19083671 := bstep (se 1 (by rfl) ⟨14312753, by rfl⟩ : syracuseStep 19083671 = 28625507) B28625507
theorem B12722447 : Blo 1985435 12722447 := bstep (se 1 (by rfl) ⟨9541835, by rfl⟩ : syracuseStep 12722447 = 19083671) B19083671
theorem B8481631 : Blo 1985435 8481631 := bstep (se 1 (by rfl) ⟨6361223, by rfl⟩ : syracuseStep 8481631 = 12722447) B12722447
theorem B11308841 : Blo 1985435 11308841 := bstep (se 2 (by rfl) ⟨4240815, by rfl⟩ : syracuseStep 11308841 = 8481631) B8481631
theorem B7539227 : Blo 1985435 7539227 := bstep (se 1 (by rfl) ⟨5654420, by rfl⟩ : syracuseStep 7539227 = 11308841) B11308841
theorem B5026151 : Blo 1985435 5026151 := bstep (se 1 (by rfl) ⟨3769613, by rfl⟩ : syracuseStep 5026151 = 7539227) B7539227
theorem B3350767 : Blo 1985435 3350767 := bstep (se 1 (by rfl) ⟨2513075, by rfl⟩ : syracuseStep 3350767 = 5026151) B5026151
theorem B4467689 : Blo 1985435 4467689 := bstep (se 2 (by rfl) ⟨1675383, by rfl⟩ : syracuseStep 4467689 = 3350767) B3350767
theorem B2978459 : Blo 1985435 2978459 := bstep (se 1 (by rfl) ⟨2233844, by rfl⟩ : syracuseStep 2978459 = 4467689) B4467689
theorem B1985639 : Blo 1985435 1985639 := bstep (se 1 (by rfl) ⟨1489229, by rfl⟩ : syracuseStep 1985639 = 2978459) B2978459
theorem B2233849 : Blo 1985435 2233849 := bbase (se 2 (by rfl) ⟨837693, by rfl⟩ : syracuseStep 2233849 = 1675387) (by norm_num)
theorem B2978465 : Blo 1985435 2978465 := bstep (se 2 (by rfl) ⟨1116924, by rfl⟩ : syracuseStep 2978465 = 2233849) B2233849
theorem B1985643 : Blo 1985435 1985643 := bstep (se 1 (by rfl) ⟨1489232, by rfl⟩ : syracuseStep 1985643 = 2978465) B2978465
theorem B6792997 : Blo 1985435 6792997 := bbase (se 4 (by rfl) ⟨636843, by rfl⟩ : syracuseStep 6792997 = 1273687) (by norm_num)
theorem B9057329 : Blo 1985435 9057329 := bstep (se 2 (by rfl) ⟨3396498, by rfl⟩ : syracuseStep 9057329 = 6792997) B6792997
theorem B6038219 : Blo 1985435 6038219 := bstep (se 1 (by rfl) ⟨4528664, by rfl⟩ : syracuseStep 6038219 = 9057329) B9057329
theorem B4025479 : Blo 1985435 4025479 := bstep (se 1 (by rfl) ⟨3019109, by rfl⟩ : syracuseStep 4025479 = 6038219) B6038219
theorem B5367305 : Blo 1985435 5367305 := bstep (se 2 (by rfl) ⟨2012739, by rfl⟩ : syracuseStep 5367305 = 4025479) B4025479
theorem B3578203 : Blo 1985435 3578203 := bstep (se 1 (by rfl) ⟨2683652, by rfl⟩ : syracuseStep 3578203 = 5367305) B5367305
theorem B4770937 : Blo 1985435 4770937 := bstep (se 2 (by rfl) ⟨1789101, by rfl⟩ : syracuseStep 4770937 = 3578203) B3578203
theorem B6361249 : Blo 1985435 6361249 := bstep (se 2 (by rfl) ⟨2385468, by rfl⟩ : syracuseStep 6361249 = 4770937) B4770937
theorem B8481665 : Blo 1985435 8481665 := bstep (se 2 (by rfl) ⟨3180624, by rfl⟩ : syracuseStep 8481665 = 6361249) B6361249
theorem B5654443 : Blo 1985435 5654443 := bstep (se 1 (by rfl) ⟨4240832, by rfl⟩ : syracuseStep 5654443 = 8481665) B8481665
theorem B7539257 : Blo 1985435 7539257 := bstep (se 2 (by rfl) ⟨2827221, by rfl⟩ : syracuseStep 7539257 = 5654443) B5654443
theorem B5026171 : Blo 1985435 5026171 := bstep (se 1 (by rfl) ⟨3769628, by rfl⟩ : syracuseStep 5026171 = 7539257) B7539257
theorem B6701561 : Blo 1985435 6701561 := bstep (se 2 (by rfl) ⟨2513085, by rfl⟩ : syracuseStep 6701561 = 5026171) B5026171
theorem B4467707 : Blo 1985435 4467707 := bstep (se 1 (by rfl) ⟨3350780, by rfl⟩ : syracuseStep 4467707 = 6701561) B6701561
theorem B2978471 : Blo 1985435 2978471 := bstep (se 1 (by rfl) ⟨2233853, by rfl⟩ : syracuseStep 2978471 = 4467707) B4467707
theorem B1985647 : Blo 1985435 1985647 := bstep (se 1 (by rfl) ⟨1489235, by rfl⟩ : syracuseStep 1985647 = 2978471) B2978471
theorem B2978477 : Blo 1985435 2978477 := bbase (se 3 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 2978477 = 1116929) (by norm_num)
theorem B1985651 : Blo 1985435 1985651 := bstep (se 1 (by rfl) ⟨1489238, by rfl⟩ : syracuseStep 1985651 = 2978477) B2978477
theorem B4467725 : Blo 1985435 4467725 := bbase (se 3 (by rfl) ⟨837698, by rfl⟩ : syracuseStep 4467725 = 1675397) (by norm_num)
theorem B2978483 : Blo 1985435 2978483 := bstep (se 1 (by rfl) ⟨2233862, by rfl⟩ : syracuseStep 2978483 = 4467725) B4467725
theorem B1985655 : Blo 1985435 1985655 := bstep (se 1 (by rfl) ⟨1489241, by rfl⟩ : syracuseStep 1985655 = 2978483) B2978483
theorem B2513101 : Blo 1985435 2513101 := bbase (se 3 (by rfl) ⟨471206, by rfl⟩ : syracuseStep 2513101 = 942413) (by norm_num)
theorem B3350801 : Blo 1985435 3350801 := bstep (se 2 (by rfl) ⟨1256550, by rfl⟩ : syracuseStep 3350801 = 2513101) B2513101
theorem B2233867 : Blo 1985435 2233867 := bstep (se 1 (by rfl) ⟨1675400, by rfl⟩ : syracuseStep 2233867 = 3350801) B3350801
theorem B2978489 : Blo 1985435 2978489 := bstep (se 2 (by rfl) ⟨1116933, by rfl⟩ : syracuseStep 2978489 = 2233867) B2233867
theorem B1985659 : Blo 1985435 1985659 := bstep (se 1 (by rfl) ⟨1489244, by rfl⟩ : syracuseStep 1985659 = 2978489) B2978489
theorem B7642181 : Blo 1985435 7642181 := bbase (se 4 (by rfl) ⟨716454, by rfl⟩ : syracuseStep 7642181 = 1432909) (by norm_num)
theorem B5094787 : Blo 1985435 5094787 := bstep (se 1 (by rfl) ⟨3821090, by rfl⟩ : syracuseStep 5094787 = 7642181) B7642181
theorem B6793049 : Blo 1985435 6793049 := bstep (se 2 (by rfl) ⟨2547393, by rfl⟩ : syracuseStep 6793049 = 5094787) B5094787
theorem B4528699 : Blo 1985435 4528699 := bstep (se 1 (by rfl) ⟨3396524, by rfl⟩ : syracuseStep 4528699 = 6793049) B6793049
theorem B24153061 : Blo 1985435 24153061 := bstep (se 4 (by rfl) ⟨2264349, by rfl⟩ : syracuseStep 24153061 = 4528699) B4528699
theorem B32204081 : Blo 1985435 32204081 := bstep (se 2 (by rfl) ⟨12076530, by rfl⟩ : syracuseStep 32204081 = 24153061) B24153061
theorem B21469387 : Blo 1985435 21469387 := bstep (se 1 (by rfl) ⟨16102040, by rfl⟩ : syracuseStep 21469387 = 32204081) B32204081
theorem B28625849 : Blo 1985435 28625849 := bstep (se 2 (by rfl) ⟨10734693, by rfl⟩ : syracuseStep 28625849 = 21469387) B21469387
theorem B19083899 : Blo 1985435 19083899 := bstep (se 1 (by rfl) ⟨14312924, by rfl⟩ : syracuseStep 19083899 = 28625849) B28625849
theorem B12722599 : Blo 1985435 12722599 := bstep (se 1 (by rfl) ⟨9541949, by rfl⟩ : syracuseStep 12722599 = 19083899) B19083899
theorem B16963465 : Blo 1985435 16963465 := bstep (se 2 (by rfl) ⟨6361299, by rfl⟩ : syracuseStep 16963465 = 12722599) B12722599
theorem B22617953 : Blo 1985435 22617953 := bstep (se 2 (by rfl) ⟨8481732, by rfl⟩ : syracuseStep 22617953 = 16963465) B16963465
theorem B15078635 : Blo 1985435 15078635 := bstep (se 1 (by rfl) ⟨11308976, by rfl⟩ : syracuseStep 15078635 = 22617953) B22617953
theorem B10052423 : Blo 1985435 10052423 := bstep (se 1 (by rfl) ⟨7539317, by rfl⟩ : syracuseStep 10052423 = 15078635) B15078635
theorem B6701615 : Blo 1985435 6701615 := bstep (se 1 (by rfl) ⟨5026211, by rfl⟩ : syracuseStep 6701615 = 10052423) B10052423
theorem B4467743 : Blo 1985435 4467743 := bstep (se 1 (by rfl) ⟨3350807, by rfl⟩ : syracuseStep 4467743 = 6701615) B6701615
theorem B2978495 : Blo 1985435 2978495 := bstep (se 1 (by rfl) ⟨2233871, by rfl⟩ : syracuseStep 2978495 = 4467743) B4467743
theorem B1985663 : Blo 1985435 1985663 := bstep (se 1 (by rfl) ⟨1489247, by rfl⟩ : syracuseStep 1985663 = 2978495) B2978495
theorem B2978501 : Blo 1985435 2978501 := bbase (se 4 (by rfl) ⟨279234, by rfl⟩ : syracuseStep 2978501 = 558469) (by norm_num)
theorem B1985667 : Blo 1985435 1985667 := bstep (se 1 (by rfl) ⟨1489250, by rfl⟩ : syracuseStep 1985667 = 2978501) B2978501
theorem B3350821 : Blo 1985435 3350821 := bbase (se 4 (by rfl) ⟨314139, by rfl⟩ : syracuseStep 3350821 = 628279) (by norm_num)
theorem B4467761 : Blo 1985435 4467761 := bstep (se 2 (by rfl) ⟨1675410, by rfl⟩ : syracuseStep 4467761 = 3350821) B3350821
theorem B2978507 : Blo 1985435 2978507 := bstep (se 1 (by rfl) ⟨2233880, by rfl⟩ : syracuseStep 2978507 = 4467761) B4467761
theorem B1985671 : Blo 1985435 1985671 := bstep (se 1 (by rfl) ⟨1489253, by rfl⟩ : syracuseStep 1985671 = 2978507) B2978507
theorem B2233885 : Blo 1985435 2233885 := bbase (se 3 (by rfl) ⟨418853, by rfl⟩ : syracuseStep 2233885 = 837707) (by norm_num)
theorem B2978513 : Blo 1985435 2978513 := bstep (se 2 (by rfl) ⟨1116942, by rfl⟩ : syracuseStep 2978513 = 2233885) B2233885
theorem B1985675 : Blo 1985435 1985675 := bstep (se 1 (by rfl) ⟨1489256, by rfl⟩ : syracuseStep 1985675 = 2978513) B2978513
theorem B6701669 : Blo 1985435 6701669 := bbase (se 4 (by rfl) ⟨628281, by rfl⟩ : syracuseStep 6701669 = 1256563) (by norm_num)
theorem B4467779 : Blo 1985435 4467779 := bstep (se 1 (by rfl) ⟨3350834, by rfl⟩ : syracuseStep 4467779 = 6701669) B6701669
theorem B2978519 : Blo 1985435 2978519 := bstep (se 1 (by rfl) ⟨2233889, by rfl⟩ : syracuseStep 2978519 = 4467779) B4467779
theorem B1985679 : Blo 1985435 1985679 := bstep (se 1 (by rfl) ⟨1489259, by rfl⟩ : syracuseStep 1985679 = 2978519) B2978519
theorem B2978525 : Blo 1985435 2978525 := bbase (se 3 (by rfl) ⟨558473, by rfl⟩ : syracuseStep 2978525 = 1116947) (by norm_num)
theorem B1985683 : Blo 1985435 1985683 := bstep (se 1 (by rfl) ⟨1489262, by rfl⟩ : syracuseStep 1985683 = 2978525) B2978525
theorem B4467797 : Blo 1985435 4467797 := bbase (se 8 (by rfl) ⟨26178, by rfl⟩ : syracuseStep 4467797 = 52357) (by norm_num)
theorem B2978531 : Blo 1985435 2978531 := bstep (se 1 (by rfl) ⟨2233898, by rfl⟩ : syracuseStep 2978531 = 4467797) B4467797
theorem B1985687 : Blo 1985435 1985687 := bstep (se 1 (by rfl) ⟨1489265, by rfl⟩ : syracuseStep 1985687 = 2978531) B2978531
theorem B4298789 : Blo 1985435 4298789 := bbase (se 4 (by rfl) ⟨403011, by rfl⟩ : syracuseStep 4298789 = 806023) (by norm_num)
theorem B11463437 : Blo 1985435 11463437 := bstep (se 3 (by rfl) ⟨2149394, by rfl⟩ : syracuseStep 11463437 = 4298789) B4298789
theorem B7642291 : Blo 1985435 7642291 := bstep (se 1 (by rfl) ⟨5731718, by rfl⟩ : syracuseStep 7642291 = 11463437) B11463437
theorem B10189721 : Blo 1985435 10189721 := bstep (se 2 (by rfl) ⟨3821145, by rfl⟩ : syracuseStep 10189721 = 7642291) B7642291
theorem B6793147 : Blo 1985435 6793147 := bstep (se 1 (by rfl) ⟨5094860, by rfl⟩ : syracuseStep 6793147 = 10189721) B10189721
theorem B9057529 : Blo 1985435 9057529 := bstep (se 2 (by rfl) ⟨3396573, by rfl⟩ : syracuseStep 9057529 = 6793147) B6793147
theorem B12076705 : Blo 1985435 12076705 := bstep (se 2 (by rfl) ⟨4528764, by rfl⟩ : syracuseStep 12076705 = 9057529) B9057529
theorem B16102273 : Blo 1985435 16102273 := bstep (se 2 (by rfl) ⟨6038352, by rfl⟩ : syracuseStep 16102273 = 12076705) B12076705
theorem B21469697 : Blo 1985435 21469697 := bstep (se 2 (by rfl) ⟨8051136, by rfl⟩ : syracuseStep 21469697 = 16102273) B16102273
theorem B14313131 : Blo 1985435 14313131 := bstep (se 1 (by rfl) ⟨10734848, by rfl⟩ : syracuseStep 14313131 = 21469697) B21469697
theorem B9542087 : Blo 1985435 9542087 := bstep (se 1 (by rfl) ⟨7156565, by rfl⟩ : syracuseStep 9542087 = 14313131) B14313131
theorem B6361391 : Blo 1985435 6361391 := bstep (se 1 (by rfl) ⟨4771043, by rfl⟩ : syracuseStep 6361391 = 9542087) B9542087
theorem B4240927 : Blo 1985435 4240927 := bstep (se 1 (by rfl) ⟨3180695, by rfl⟩ : syracuseStep 4240927 = 6361391) B6361391
theorem B5654569 : Blo 1985435 5654569 := bstep (se 2 (by rfl) ⟨2120463, by rfl⟩ : syracuseStep 5654569 = 4240927) B4240927
theorem B7539425 : Blo 1985435 7539425 := bstep (se 2 (by rfl) ⟨2827284, by rfl⟩ : syracuseStep 7539425 = 5654569) B5654569
theorem B5026283 : Blo 1985435 5026283 := bstep (se 1 (by rfl) ⟨3769712, by rfl⟩ : syracuseStep 5026283 = 7539425) B7539425
theorem B3350855 : Blo 1985435 3350855 := bstep (se 1 (by rfl) ⟨2513141, by rfl⟩ : syracuseStep 3350855 = 5026283) B5026283
theorem B2233903 : Blo 1985435 2233903 := bstep (se 1 (by rfl) ⟨1675427, by rfl⟩ : syracuseStep 2233903 = 3350855) B3350855
theorem B2978537 : Blo 1985435 2978537 := bstep (se 2 (by rfl) ⟨1116951, by rfl⟩ : syracuseStep 2978537 = 2233903) B2233903
theorem B1985691 : Blo 1985435 1985691 := bstep (se 1 (by rfl) ⟨1489268, by rfl⟩ : syracuseStep 1985691 = 2978537) B2978537
theorem B48306901 : Blo 1985435 48306901 := bbase (se 7 (by rfl) ⟨566096, by rfl⟩ : syracuseStep 48306901 = 1132193) (by norm_num)
theorem B64409201 : Blo 1985435 64409201 := bstep (se 2 (by rfl) ⟨24153450, by rfl⟩ : syracuseStep 64409201 = 48306901) B48306901
theorem B42939467 : Blo 1985435 42939467 := bstep (se 1 (by rfl) ⟨32204600, by rfl⟩ : syracuseStep 42939467 = 64409201) B64409201
theorem B28626311 : Blo 1985435 28626311 := bstep (se 1 (by rfl) ⟨21469733, by rfl⟩ : syracuseStep 28626311 = 42939467) B42939467
theorem B19084207 : Blo 1985435 19084207 := bstep (se 1 (by rfl) ⟨14313155, by rfl⟩ : syracuseStep 19084207 = 28626311) B28626311
theorem B25445609 : Blo 1985435 25445609 := bstep (se 2 (by rfl) ⟨9542103, by rfl⟩ : syracuseStep 25445609 = 19084207) B19084207
theorem B16963739 : Blo 1985435 16963739 := bstep (se 1 (by rfl) ⟨12722804, by rfl⟩ : syracuseStep 16963739 = 25445609) B25445609
theorem B11309159 : Blo 1985435 11309159 := bstep (se 1 (by rfl) ⟨8481869, by rfl⟩ : syracuseStep 11309159 = 16963739) B16963739
theorem B7539439 : Blo 1985435 7539439 := bstep (se 1 (by rfl) ⟨5654579, by rfl⟩ : syracuseStep 7539439 = 11309159) B11309159
theorem B10052585 : Blo 1985435 10052585 := bstep (se 2 (by rfl) ⟨3769719, by rfl⟩ : syracuseStep 10052585 = 7539439) B7539439
theorem B6701723 : Blo 1985435 6701723 := bstep (se 1 (by rfl) ⟨5026292, by rfl⟩ : syracuseStep 6701723 = 10052585) B10052585
theorem B4467815 : Blo 1985435 4467815 := bstep (se 1 (by rfl) ⟨3350861, by rfl⟩ : syracuseStep 4467815 = 6701723) B6701723
theorem B2978543 : Blo 1985435 2978543 := bstep (se 1 (by rfl) ⟨2233907, by rfl⟩ : syracuseStep 2978543 = 4467815) B4467815
theorem B1985695 : Blo 1985435 1985695 := bstep (se 1 (by rfl) ⟨1489271, by rfl⟩ : syracuseStep 1985695 = 2978543) B2978543
theorem B2978549 : Blo 1985435 2978549 := bbase (se 5 (by rfl) ⟨139619, by rfl⟩ : syracuseStep 2978549 = 279239) (by norm_num)
theorem B1985699 : Blo 1985435 1985699 := bstep (se 1 (by rfl) ⟨1489274, by rfl⟩ : syracuseStep 1985699 = 2978549) B2978549
theorem B6361429 : Blo 1985435 6361429 := bbase (se 10 (by rfl) ⟨9318, by rfl⟩ : syracuseStep 6361429 = 18637) (by norm_num)
theorem B8481905 : Blo 1985435 8481905 := bstep (se 2 (by rfl) ⟨3180714, by rfl⟩ : syracuseStep 8481905 = 6361429) B6361429
theorem B5654603 : Blo 1985435 5654603 := bstep (se 1 (by rfl) ⟨4240952, by rfl⟩ : syracuseStep 5654603 = 8481905) B8481905
theorem B3769735 : Blo 1985435 3769735 := bstep (se 1 (by rfl) ⟨2827301, by rfl⟩ : syracuseStep 3769735 = 5654603) B5654603
theorem B5026313 : Blo 1985435 5026313 := bstep (se 2 (by rfl) ⟨1884867, by rfl⟩ : syracuseStep 5026313 = 3769735) B3769735
theorem B3350875 : Blo 1985435 3350875 := bstep (se 1 (by rfl) ⟨2513156, by rfl⟩ : syracuseStep 3350875 = 5026313) B5026313
theorem B4467833 : Blo 1985435 4467833 := bstep (se 2 (by rfl) ⟨1675437, by rfl⟩ : syracuseStep 4467833 = 3350875) B3350875
theorem B2978555 : Blo 1985435 2978555 := bstep (se 1 (by rfl) ⟨2233916, by rfl⟩ : syracuseStep 2978555 = 4467833) B4467833
theorem B1985703 : Blo 1985435 1985703 := bstep (se 1 (by rfl) ⟨1489277, by rfl⟩ : syracuseStep 1985703 = 2978555) B2978555
theorem B2233921 : Blo 1985435 2233921 := bbase (se 2 (by rfl) ⟨837720, by rfl⟩ : syracuseStep 2233921 = 1675441) (by norm_num)
theorem B2978561 : Blo 1985435 2978561 := bstep (se 2 (by rfl) ⟨1116960, by rfl⟩ : syracuseStep 2978561 = 2233921) B2233921
theorem B1985707 : Blo 1985435 1985707 := bstep (se 1 (by rfl) ⟨1489280, by rfl⟩ : syracuseStep 1985707 = 2978561) B2978561
theorem B5026333 : Blo 1985435 5026333 := bbase (se 3 (by rfl) ⟨942437, by rfl⟩ : syracuseStep 5026333 = 1884875) (by norm_num)
theorem B6701777 : Blo 1985435 6701777 := bstep (se 2 (by rfl) ⟨2513166, by rfl⟩ : syracuseStep 6701777 = 5026333) B5026333
theorem B4467851 : Blo 1985435 4467851 := bstep (se 1 (by rfl) ⟨3350888, by rfl⟩ : syracuseStep 4467851 = 6701777) B6701777
theorem B2978567 : Blo 1985435 2978567 := bstep (se 1 (by rfl) ⟨2233925, by rfl⟩ : syracuseStep 2978567 = 4467851) B4467851
theorem B1985711 : Blo 1985435 1985711 := bstep (se 1 (by rfl) ⟨1489283, by rfl⟩ : syracuseStep 1985711 = 2978567) B2978567
theorem B2978573 : Blo 1985435 2978573 := bbase (se 3 (by rfl) ⟨558482, by rfl⟩ : syracuseStep 2978573 = 1116965) (by norm_num)
theorem B1985715 : Blo 1985435 1985715 := bstep (se 1 (by rfl) ⟨1489286, by rfl⟩ : syracuseStep 1985715 = 2978573) B2978573
theorem B4467869 : Blo 1985435 4467869 := bbase (se 3 (by rfl) ⟨837725, by rfl⟩ : syracuseStep 4467869 = 1675451) (by norm_num)
theorem B2978579 : Blo 1985435 2978579 := bstep (se 1 (by rfl) ⟨2233934, by rfl⟩ : syracuseStep 2978579 = 4467869) B4467869
theorem B1985719 : Blo 1985435 1985719 := bstep (se 1 (by rfl) ⟨1489289, by rfl⟩ : syracuseStep 1985719 = 2978579) B2978579
theorem B3350909 : Blo 1985435 3350909 := bbase (se 3 (by rfl) ⟨628295, by rfl⟩ : syracuseStep 3350909 = 1256591) (by norm_num)
theorem B2233939 : Blo 1985435 2233939 := bstep (se 1 (by rfl) ⟨1675454, by rfl⟩ : syracuseStep 2233939 = 3350909) B3350909
theorem B2978585 : Blo 1985435 2978585 := bstep (se 2 (by rfl) ⟨1116969, by rfl⟩ : syracuseStep 2978585 = 2233939) B2233939
theorem B1985723 : Blo 1985435 1985723 := bstep (se 1 (by rfl) ⟨1489292, by rfl⟩ : syracuseStep 1985723 = 2978585) B2978585
theorem B4590637 : Blo 1985435 4590637 := bbase (se 3 (by rfl) ⟨860744, by rfl⟩ : syracuseStep 4590637 = 1721489) (by norm_num)
theorem B24483397 : Blo 1985435 24483397 := bstep (se 4 (by rfl) ⟨2295318, by rfl⟩ : syracuseStep 24483397 = 4590637) B4590637
theorem B32644529 : Blo 1985435 32644529 := bstep (se 2 (by rfl) ⟨12241698, by rfl⟩ : syracuseStep 32644529 = 24483397) B24483397
theorem B21763019 : Blo 1985435 21763019 := bstep (se 1 (by rfl) ⟨16322264, by rfl⟩ : syracuseStep 21763019 = 32644529) B32644529
theorem B14508679 : Blo 1985435 14508679 := bstep (se 1 (by rfl) ⟨10881509, by rfl⟩ : syracuseStep 14508679 = 21763019) B21763019
theorem B19344905 : Blo 1985435 19344905 := bstep (se 2 (by rfl) ⟨7254339, by rfl⟩ : syracuseStep 19344905 = 14508679) B14508679
theorem B12896603 : Blo 1985435 12896603 := bstep (se 1 (by rfl) ⟨9672452, by rfl⟩ : syracuseStep 12896603 = 19344905) B19344905
theorem B8597735 : Blo 1985435 8597735 := bstep (se 1 (by rfl) ⟨6448301, by rfl⟩ : syracuseStep 8597735 = 12896603) B12896603
theorem B5731823 : Blo 1985435 5731823 := bstep (se 1 (by rfl) ⟨4298867, by rfl⟩ : syracuseStep 5731823 = 8597735) B8597735
theorem B15284861 : Blo 1985435 15284861 := bstep (se 3 (by rfl) ⟨2865911, by rfl⟩ : syracuseStep 15284861 = 5731823) B5731823
theorem B10189907 : Blo 1985435 10189907 := bstep (se 1 (by rfl) ⟨7642430, by rfl⟩ : syracuseStep 10189907 = 15284861) B15284861
theorem B6793271 : Blo 1985435 6793271 := bstep (se 1 (by rfl) ⟨5094953, by rfl⟩ : syracuseStep 6793271 = 10189907) B10189907
theorem B4528847 : Blo 1985435 4528847 := bstep (se 1 (by rfl) ⟨3396635, by rfl⟩ : syracuseStep 4528847 = 6793271) B6793271
theorem B3019231 : Blo 1985435 3019231 := bstep (se 1 (by rfl) ⟨2264423, by rfl⟩ : syracuseStep 3019231 = 4528847) B4528847
theorem B4025641 : Blo 1985435 4025641 := bstep (se 2 (by rfl) ⟨1509615, by rfl⟩ : syracuseStep 4025641 = 3019231) B3019231
theorem B5367521 : Blo 1985435 5367521 := bstep (se 2 (by rfl) ⟨2012820, by rfl⟩ : syracuseStep 5367521 = 4025641) B4025641
theorem B3578347 : Blo 1985435 3578347 := bstep (se 1 (by rfl) ⟨2683760, by rfl⟩ : syracuseStep 3578347 = 5367521) B5367521
theorem B4771129 : Blo 1985435 4771129 := bstep (se 2 (by rfl) ⟨1789173, by rfl⟩ : syracuseStep 4771129 = 3578347) B3578347
theorem B6361505 : Blo 1985435 6361505 := bstep (se 2 (by rfl) ⟨2385564, by rfl⟩ : syracuseStep 6361505 = 4771129) B4771129
theorem B4241003 : Blo 1985435 4241003 := bstep (se 1 (by rfl) ⟨3180752, by rfl⟩ : syracuseStep 4241003 = 6361505) B6361505
theorem B11309341 : Blo 1985435 11309341 := bstep (se 3 (by rfl) ⟨2120501, by rfl⟩ : syracuseStep 11309341 = 4241003) B4241003
theorem B15079121 : Blo 1985435 15079121 := bstep (se 2 (by rfl) ⟨5654670, by rfl⟩ : syracuseStep 15079121 = 11309341) B11309341
theorem B10052747 : Blo 1985435 10052747 := bstep (se 1 (by rfl) ⟨7539560, by rfl⟩ : syracuseStep 10052747 = 15079121) B15079121
theorem B6701831 : Blo 1985435 6701831 := bstep (se 1 (by rfl) ⟨5026373, by rfl⟩ : syracuseStep 6701831 = 10052747) B10052747
theorem B4467887 : Blo 1985435 4467887 := bstep (se 1 (by rfl) ⟨3350915, by rfl⟩ : syracuseStep 4467887 = 6701831) B6701831
theorem B2978591 : Blo 1985435 2978591 := bstep (se 1 (by rfl) ⟨2233943, by rfl⟩ : syracuseStep 2978591 = 4467887) B4467887
theorem B1985727 : Blo 1985435 1985727 := bstep (se 1 (by rfl) ⟨1489295, by rfl⟩ : syracuseStep 1985727 = 2978591) B2978591
theorem B2978597 : Blo 1985435 2978597 := bbase (se 4 (by rfl) ⟨279243, by rfl⟩ : syracuseStep 2978597 = 558487) (by norm_num)
theorem B1985731 : Blo 1985435 1985731 := bstep (se 1 (by rfl) ⟨1489298, by rfl⟩ : syracuseStep 1985731 = 2978597) B2978597
theorem B2513197 : Blo 1985435 2513197 := bbase (se 3 (by rfl) ⟨471224, by rfl⟩ : syracuseStep 2513197 = 942449) (by norm_num)
theorem B3350929 : Blo 1985435 3350929 := bstep (se 2 (by rfl) ⟨1256598, by rfl⟩ : syracuseStep 3350929 = 2513197) B2513197
theorem B4467905 : Blo 1985435 4467905 := bstep (se 2 (by rfl) ⟨1675464, by rfl⟩ : syracuseStep 4467905 = 3350929) B3350929
theorem B2978603 : Blo 1985435 2978603 := bstep (se 1 (by rfl) ⟨2233952, by rfl⟩ : syracuseStep 2978603 = 4467905) B4467905
theorem B1985735 : Blo 1985435 1985735 := bstep (se 1 (by rfl) ⟨1489301, by rfl⟩ : syracuseStep 1985735 = 2978603) B2978603
theorem B2233957 : Blo 1985435 2233957 := bbase (se 4 (by rfl) ⟨209433, by rfl⟩ : syracuseStep 2233957 = 418867) (by norm_num)
theorem B2978609 : Blo 1985435 2978609 := bstep (se 2 (by rfl) ⟨1116978, by rfl⟩ : syracuseStep 2978609 = 2233957) B2233957
theorem B1985739 : Blo 1985435 1985739 := bstep (se 1 (by rfl) ⟨1489304, by rfl⟩ : syracuseStep 1985739 = 2978609) B2978609
theorem B4528885 : Blo 1985435 4528885 := bbase (se 5 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 4528885 = 424583) (by norm_num)
theorem B6038513 : Blo 1985435 6038513 := bstep (se 2 (by rfl) ⟨2264442, by rfl⟩ : syracuseStep 6038513 = 4528885) B4528885
theorem B4025675 : Blo 1985435 4025675 := bstep (se 1 (by rfl) ⟨3019256, by rfl⟩ : syracuseStep 4025675 = 6038513) B6038513
theorem B2683783 : Blo 1985435 2683783 := bstep (se 1 (by rfl) ⟨2012837, by rfl⟩ : syracuseStep 2683783 = 4025675) B4025675
theorem B3578377 : Blo 1985435 3578377 := bstep (se 2 (by rfl) ⟨1341891, by rfl⟩ : syracuseStep 3578377 = 2683783) B2683783
theorem B4771169 : Blo 1985435 4771169 := bstep (se 2 (by rfl) ⟨1789188, by rfl⟩ : syracuseStep 4771169 = 3578377) B3578377
theorem B3180779 : Blo 1985435 3180779 := bstep (se 1 (by rfl) ⟨2385584, by rfl⟩ : syracuseStep 3180779 = 4771169) B4771169
theorem B2120519 : Blo 1985435 2120519 := bstep (se 1 (by rfl) ⟨1590389, by rfl⟩ : syracuseStep 2120519 = 3180779) B3180779
theorem B5654717 : Blo 1985435 5654717 := bstep (se 3 (by rfl) ⟨1060259, by rfl⟩ : syracuseStep 5654717 = 2120519) B2120519
theorem B3769811 : Blo 1985435 3769811 := bstep (se 1 (by rfl) ⟨2827358, by rfl⟩ : syracuseStep 3769811 = 5654717) B5654717
theorem B2513207 : Blo 1985435 2513207 := bstep (se 1 (by rfl) ⟨1884905, by rfl⟩ : syracuseStep 2513207 = 3769811) B3769811
theorem B6701885 : Blo 1985435 6701885 := bstep (se 3 (by rfl) ⟨1256603, by rfl⟩ : syracuseStep 6701885 = 2513207) B2513207
theorem B4467923 : Blo 1985435 4467923 := bstep (se 1 (by rfl) ⟨3350942, by rfl⟩ : syracuseStep 4467923 = 6701885) B6701885
theorem B2978615 : Blo 1985435 2978615 := bstep (se 1 (by rfl) ⟨2233961, by rfl⟩ : syracuseStep 2978615 = 4467923) B4467923
theorem B1985743 : Blo 1985435 1985743 := bstep (se 1 (by rfl) ⟨1489307, by rfl⟩ : syracuseStep 1985743 = 2978615) B2978615
theorem B2978621 : Blo 1985435 2978621 := bbase (se 3 (by rfl) ⟨558491, by rfl⟩ : syracuseStep 2978621 = 1116983) (by norm_num)
theorem B1985747 : Blo 1985435 1985747 := bstep (se 1 (by rfl) ⟨1489310, by rfl⟩ : syracuseStep 1985747 = 2978621) B2978621
theorem B4467941 : Blo 1985435 4467941 := bbase (se 4 (by rfl) ⟨418869, by rfl⟩ : syracuseStep 4467941 = 837739) (by norm_num)
theorem B2978627 : Blo 1985435 2978627 := bstep (se 1 (by rfl) ⟨2233970, by rfl⟩ : syracuseStep 2978627 = 4467941) B4467941
theorem B1985751 : Blo 1985435 1985751 := bstep (se 1 (by rfl) ⟨1489313, by rfl⟩ : syracuseStep 1985751 = 2978627) B2978627
theorem B5026445 : Blo 1985435 5026445 := bbase (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) (by norm_num)
theorem B3350963 : Blo 1985435 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B2233975 : Blo 1985435 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B2978633 : Blo 1985435 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B1985755 : Blo 1985435 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B2827381 : Blo 1985435 2827381 := bbase (se 5 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 2827381 = 265067) (by norm_num)
theorem B3769841 : Blo 1985435 3769841 := bstep (se 2 (by rfl) ⟨1413690, by rfl⟩ : syracuseStep 3769841 = 2827381) B2827381
theorem B10052909 : Blo 1985435 10052909 := bstep (se 3 (by rfl) ⟨1884920, by rfl⟩ : syracuseStep 10052909 = 3769841) B3769841
theorem B6701939 : Blo 1985435 6701939 := bstep (se 1 (by rfl) ⟨5026454, by rfl⟩ : syracuseStep 6701939 = 10052909) B10052909
theorem B4467959 : Blo 1985435 4467959 := bstep (se 1 (by rfl) ⟨3350969, by rfl⟩ : syracuseStep 4467959 = 6701939) B6701939
theorem B2978639 : Blo 1985435 2978639 := bstep (se 1 (by rfl) ⟨2233979, by rfl⟩ : syracuseStep 2978639 = 4467959) B4467959
theorem B1985759 : Blo 1985435 1985759 := bstep (se 1 (by rfl) ⟨1489319, by rfl⟩ : syracuseStep 1985759 = 2978639) B2978639
theorem B2978645 : Blo 1985435 2978645 := bbase (se 9 (by rfl) ⟨8726, by rfl⟩ : syracuseStep 2978645 = 17453) (by norm_num)
theorem B1985763 : Blo 1985435 1985763 := bstep (se 1 (by rfl) ⟨1489322, by rfl⟩ : syracuseStep 1985763 = 2978645) B2978645
theorem B2385613 : Blo 1985435 2385613 := bbase (se 3 (by rfl) ⟨447302, by rfl⟩ : syracuseStep 2385613 = 894605) (by norm_num)
theorem B3180817 : Blo 1985435 3180817 := bstep (se 2 (by rfl) ⟨1192806, by rfl⟩ : syracuseStep 3180817 = 2385613) B2385613
theorem B4241089 : Blo 1985435 4241089 := bstep (se 2 (by rfl) ⟨1590408, by rfl⟩ : syracuseStep 4241089 = 3180817) B3180817
theorem B5654785 : Blo 1985435 5654785 := bstep (se 2 (by rfl) ⟨2120544, by rfl⟩ : syracuseStep 5654785 = 4241089) B4241089
theorem B7539713 : Blo 1985435 7539713 := bstep (se 2 (by rfl) ⟨2827392, by rfl⟩ : syracuseStep 7539713 = 5654785) B5654785
theorem B5026475 : Blo 1985435 5026475 := bstep (se 1 (by rfl) ⟨3769856, by rfl⟩ : syracuseStep 5026475 = 7539713) B7539713
theorem B3350983 : Blo 1985435 3350983 := bstep (se 1 (by rfl) ⟨2513237, by rfl⟩ : syracuseStep 3350983 = 5026475) B5026475
theorem B4467977 : Blo 1985435 4467977 := bstep (se 2 (by rfl) ⟨1675491, by rfl⟩ : syracuseStep 4467977 = 3350983) B3350983
theorem B2978651 : Blo 1985435 2978651 := bstep (se 1 (by rfl) ⟨2233988, by rfl⟩ : syracuseStep 2978651 = 4467977) B4467977
theorem B1985767 : Blo 1985435 1985767 := bstep (se 1 (by rfl) ⟨1489325, by rfl⟩ : syracuseStep 1985767 = 2978651) B2978651
theorem B2233993 : Blo 1985435 2233993 := bbase (se 2 (by rfl) ⟨837747, by rfl⟩ : syracuseStep 2233993 = 1675495) (by norm_num)
theorem B2978657 : Blo 1985435 2978657 := bstep (se 2 (by rfl) ⟨1116996, by rfl⟩ : syracuseStep 2978657 = 2233993) B2233993
theorem B1985771 : Blo 1985435 1985771 := bstep (se 1 (by rfl) ⟨1489328, by rfl⟩ : syracuseStep 1985771 = 2978657) B2978657
theorem B36231637 : Blo 1985435 36231637 := bbase (se 7 (by rfl) ⟨424589, by rfl⟩ : syracuseStep 36231637 = 849179) (by norm_num)
theorem B48308849 : Blo 1985435 48308849 := bstep (se 2 (by rfl) ⟨18115818, by rfl⟩ : syracuseStep 48308849 = 36231637) B36231637
theorem B32205899 : Blo 1985435 32205899 := bstep (se 1 (by rfl) ⟨24154424, by rfl⟩ : syracuseStep 32205899 = 48308849) B48308849
theorem B21470599 : Blo 1985435 21470599 := bstep (se 1 (by rfl) ⟨16102949, by rfl⟩ : syracuseStep 21470599 = 32205899) B32205899
theorem B28627465 : Blo 1985435 28627465 := bstep (se 2 (by rfl) ⟨10735299, by rfl⟩ : syracuseStep 28627465 = 21470599) B21470599
theorem B38169953 : Blo 1985435 38169953 := bstep (se 2 (by rfl) ⟨14313732, by rfl⟩ : syracuseStep 38169953 = 28627465) B28627465
theorem B25446635 : Blo 1985435 25446635 := bstep (se 1 (by rfl) ⟨19084976, by rfl⟩ : syracuseStep 25446635 = 38169953) B38169953
theorem B16964423 : Blo 1985435 16964423 := bstep (se 1 (by rfl) ⟨12723317, by rfl⟩ : syracuseStep 16964423 = 25446635) B25446635
theorem B11309615 : Blo 1985435 11309615 := bstep (se 1 (by rfl) ⟨8482211, by rfl⟩ : syracuseStep 11309615 = 16964423) B16964423
theorem B7539743 : Blo 1985435 7539743 := bstep (se 1 (by rfl) ⟨5654807, by rfl⟩ : syracuseStep 7539743 = 11309615) B11309615
theorem B5026495 : Blo 1985435 5026495 := bstep (se 1 (by rfl) ⟨3769871, by rfl⟩ : syracuseStep 5026495 = 7539743) B7539743
theorem B6701993 : Blo 1985435 6701993 := bstep (se 2 (by rfl) ⟨2513247, by rfl⟩ : syracuseStep 6701993 = 5026495) B5026495
theorem B4467995 : Blo 1985435 4467995 := bstep (se 1 (by rfl) ⟨3350996, by rfl⟩ : syracuseStep 4467995 = 6701993) B6701993
theorem B2978663 : Blo 1985435 2978663 := bstep (se 1 (by rfl) ⟨2233997, by rfl⟩ : syracuseStep 2978663 = 4467995) B4467995
theorem B1985775 : Blo 1985435 1985775 := bstep (se 1 (by rfl) ⟨1489331, by rfl⟩ : syracuseStep 1985775 = 2978663) B2978663
theorem B2978669 : Blo 1985435 2978669 := bbase (se 3 (by rfl) ⟨558500, by rfl⟩ : syracuseStep 2978669 = 1117001) (by norm_num)
theorem B1985779 : Blo 1985435 1985779 := bstep (se 1 (by rfl) ⟨1489334, by rfl⟩ : syracuseStep 1985779 = 2978669) B2978669
theorem B4468013 : Blo 1985435 4468013 := bbase (se 3 (by rfl) ⟨837752, by rfl⟩ : syracuseStep 4468013 = 1675505) (by norm_num)
theorem B2978675 : Blo 1985435 2978675 := bstep (se 1 (by rfl) ⟨2234006, by rfl⟩ : syracuseStep 2978675 = 4468013) B4468013
theorem B1985783 : Blo 1985435 1985783 := bstep (se 1 (by rfl) ⟨1489337, by rfl⟩ : syracuseStep 1985783 = 2978675) B2978675
theorem B9542549 : Blo 1985435 9542549 := bbase (se 6 (by rfl) ⟨223653, by rfl⟩ : syracuseStep 9542549 = 447307) (by norm_num)
theorem B6361699 : Blo 1985435 6361699 := bstep (se 1 (by rfl) ⟨4771274, by rfl⟩ : syracuseStep 6361699 = 9542549) B9542549
theorem B8482265 : Blo 1985435 8482265 := bstep (se 2 (by rfl) ⟨3180849, by rfl⟩ : syracuseStep 8482265 = 6361699) B6361699
theorem B5654843 : Blo 1985435 5654843 := bstep (se 1 (by rfl) ⟨4241132, by rfl⟩ : syracuseStep 5654843 = 8482265) B8482265
theorem B3769895 : Blo 1985435 3769895 := bstep (se 1 (by rfl) ⟨2827421, by rfl⟩ : syracuseStep 3769895 = 5654843) B5654843
theorem B2513263 : Blo 1985435 2513263 := bstep (se 1 (by rfl) ⟨1884947, by rfl⟩ : syracuseStep 2513263 = 3769895) B3769895
theorem B3351017 : Blo 1985435 3351017 := bstep (se 2 (by rfl) ⟨1256631, by rfl⟩ : syracuseStep 3351017 = 2513263) B2513263
theorem B2234011 : Blo 1985435 2234011 := bstep (se 1 (by rfl) ⟨1675508, by rfl⟩ : syracuseStep 2234011 = 3351017) B3351017
theorem B2978681 : Blo 1985435 2978681 := bstep (se 2 (by rfl) ⟨1117005, by rfl⟩ : syracuseStep 2978681 = 2234011) B2234011
theorem B1985787 : Blo 1985435 1985787 := bstep (se 1 (by rfl) ⟨1489340, by rfl⟩ : syracuseStep 1985787 = 2978681) B2978681
theorem B22928021 : Blo 1985435 22928021 := bbase (se 6 (by rfl) ⟨537375, by rfl⟩ : syracuseStep 22928021 = 1074751) (by norm_num)
theorem B15285347 : Blo 1985435 15285347 := bstep (se 1 (by rfl) ⟨11464010, by rfl⟩ : syracuseStep 15285347 = 22928021) B22928021
theorem B10190231 : Blo 1985435 10190231 := bstep (se 1 (by rfl) ⟨7642673, by rfl⟩ : syracuseStep 10190231 = 15285347) B15285347
theorem B6793487 : Blo 1985435 6793487 := bstep (se 1 (by rfl) ⟨5095115, by rfl⟩ : syracuseStep 6793487 = 10190231) B10190231
theorem B4528991 : Blo 1985435 4528991 := bstep (se 1 (by rfl) ⟨3396743, by rfl⟩ : syracuseStep 4528991 = 6793487) B6793487
theorem B12077309 : Blo 1985435 12077309 := bstep (se 3 (by rfl) ⟨2264495, by rfl⟩ : syracuseStep 12077309 = 4528991) B4528991
theorem B32206157 : Blo 1985435 32206157 := bstep (se 3 (by rfl) ⟨6038654, by rfl⟩ : syracuseStep 32206157 = 12077309) B12077309
theorem B21470771 : Blo 1985435 21470771 := bstep (se 1 (by rfl) ⟨16103078, by rfl⟩ : syracuseStep 21470771 = 32206157) B32206157
theorem B14313847 : Blo 1985435 14313847 := bstep (se 1 (by rfl) ⟨10735385, by rfl⟩ : syracuseStep 14313847 = 21470771) B21470771
theorem B19085129 : Blo 1985435 19085129 := bstep (se 2 (by rfl) ⟨7156923, by rfl⟩ : syracuseStep 19085129 = 14313847) B14313847
theorem B12723419 : Blo 1985435 12723419 := bstep (se 1 (by rfl) ⟨9542564, by rfl⟩ : syracuseStep 12723419 = 19085129) B19085129
theorem B33929117 : Blo 1985435 33929117 := bstep (se 3 (by rfl) ⟨6361709, by rfl⟩ : syracuseStep 33929117 = 12723419) B12723419
theorem B22619411 : Blo 1985435 22619411 := bstep (se 1 (by rfl) ⟨16964558, by rfl⟩ : syracuseStep 22619411 = 33929117) B33929117
theorem B15079607 : Blo 1985435 15079607 := bstep (se 1 (by rfl) ⟨11309705, by rfl⟩ : syracuseStep 15079607 = 22619411) B22619411
theorem B10053071 : Blo 1985435 10053071 := bstep (se 1 (by rfl) ⟨7539803, by rfl⟩ : syracuseStep 10053071 = 15079607) B15079607
theorem B6702047 : Blo 1985435 6702047 := bstep (se 1 (by rfl) ⟨5026535, by rfl⟩ : syracuseStep 6702047 = 10053071) B10053071
theorem B4468031 : Blo 1985435 4468031 := bstep (se 1 (by rfl) ⟨3351023, by rfl⟩ : syracuseStep 4468031 = 6702047) B6702047
theorem B2978687 : Blo 1985435 2978687 := bstep (se 1 (by rfl) ⟨2234015, by rfl⟩ : syracuseStep 2978687 = 4468031) B4468031
theorem B1985791 : Blo 1985435 1985791 := bstep (se 1 (by rfl) ⟨1489343, by rfl⟩ : syracuseStep 1985791 = 2978687) B2978687
theorem B2978693 : Blo 1985435 2978693 := bbase (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) (by norm_num)
theorem B1985795 : Blo 1985435 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B3351037 : Blo 1985435 3351037 := bbase (se 3 (by rfl) ⟨628319, by rfl⟩ : syracuseStep 3351037 = 1256639) (by norm_num)
theorem B4468049 : Blo 1985435 4468049 := bstep (se 2 (by rfl) ⟨1675518, by rfl⟩ : syracuseStep 4468049 = 3351037) B3351037
theorem B2978699 : Blo 1985435 2978699 := bstep (se 1 (by rfl) ⟨2234024, by rfl⟩ : syracuseStep 2978699 = 4468049) B4468049
theorem B1985799 : Blo 1985435 1985799 := bstep (se 1 (by rfl) ⟨1489349, by rfl⟩ : syracuseStep 1985799 = 2978699) B2978699
theorem B2234029 : Blo 1985435 2234029 := bbase (se 3 (by rfl) ⟨418880, by rfl⟩ : syracuseStep 2234029 = 837761) (by norm_num)
theorem B2978705 : Blo 1985435 2978705 := bstep (se 2 (by rfl) ⟨1117014, by rfl⟩ : syracuseStep 2978705 = 2234029) B2234029
theorem B1985803 : Blo 1985435 1985803 := bstep (se 1 (by rfl) ⟨1489352, by rfl⟩ : syracuseStep 1985803 = 2978705) B2978705
theorem B6702101 : Blo 1985435 6702101 := bbase (se 6 (by rfl) ⟨157080, by rfl⟩ : syracuseStep 6702101 = 314161) (by norm_num)
theorem B4468067 : Blo 1985435 4468067 := bstep (se 1 (by rfl) ⟨3351050, by rfl⟩ : syracuseStep 4468067 = 6702101) B6702101
theorem B2978711 : Blo 1985435 2978711 := bstep (se 1 (by rfl) ⟨2234033, by rfl⟩ : syracuseStep 2978711 = 4468067) B4468067
theorem B1985807 : Blo 1985435 1985807 := bstep (se 1 (by rfl) ⟨1489355, by rfl⟩ : syracuseStep 1985807 = 2978711) B2978711
theorem B2978717 : Blo 1985435 2978717 := bbase (se 3 (by rfl) ⟨558509, by rfl⟩ : syracuseStep 2978717 = 1117019) (by norm_num)
theorem B1985811 : Blo 1985435 1985811 := bstep (se 1 (by rfl) ⟨1489358, by rfl⟩ : syracuseStep 1985811 = 2978717) B2978717
theorem B4468085 : Blo 1985435 4468085 := bbase (se 5 (by rfl) ⟨209441, by rfl⟩ : syracuseStep 4468085 = 418883) (by norm_num)
theorem B2978723 : Blo 1985435 2978723 := bstep (se 1 (by rfl) ⟨2234042, by rfl⟩ : syracuseStep 2978723 = 4468085) B4468085
theorem B1985815 : Blo 1985435 1985815 := bstep (se 1 (by rfl) ⟨1489361, by rfl⟩ : syracuseStep 1985815 = 2978723) B2978723
theorem B2683885 : Blo 1985435 2683885 := bbase (se 3 (by rfl) ⟨503228, by rfl⟩ : syracuseStep 2683885 = 1006457) (by norm_num)
theorem B3578513 : Blo 1985435 3578513 := bstep (se 2 (by rfl) ⟨1341942, by rfl⟩ : syracuseStep 3578513 = 2683885) B2683885
theorem B9542701 : Blo 1985435 9542701 := bstep (se 3 (by rfl) ⟨1789256, by rfl⟩ : syracuseStep 9542701 = 3578513) B3578513
theorem B12723601 : Blo 1985435 12723601 := bstep (se 2 (by rfl) ⟨4771350, by rfl⟩ : syracuseStep 12723601 = 9542701) B9542701
theorem B16964801 : Blo 1985435 16964801 := bstep (se 2 (by rfl) ⟨6361800, by rfl⟩ : syracuseStep 16964801 = 12723601) B12723601
theorem B11309867 : Blo 1985435 11309867 := bstep (se 1 (by rfl) ⟨8482400, by rfl⟩ : syracuseStep 11309867 = 16964801) B16964801
theorem B7539911 : Blo 1985435 7539911 := bstep (se 1 (by rfl) ⟨5654933, by rfl⟩ : syracuseStep 7539911 = 11309867) B11309867
theorem B5026607 : Blo 1985435 5026607 := bstep (se 1 (by rfl) ⟨3769955, by rfl⟩ : syracuseStep 5026607 = 7539911) B7539911
theorem B3351071 : Blo 1985435 3351071 := bstep (se 1 (by rfl) ⟨2513303, by rfl⟩ : syracuseStep 3351071 = 5026607) B5026607
theorem B2234047 : Blo 1985435 2234047 := bstep (se 1 (by rfl) ⟨1675535, by rfl⟩ : syracuseStep 2234047 = 3351071) B3351071
theorem B2978729 : Blo 1985435 2978729 := bstep (se 2 (by rfl) ⟨1117023, by rfl⟩ : syracuseStep 2978729 = 2234047) B2234047
theorem B1985819 : Blo 1985435 1985819 := bstep (se 1 (by rfl) ⟨1489364, by rfl⟩ : syracuseStep 1985819 = 2978729) B2978729
theorem B7539925 : Blo 1985435 7539925 := bbase (se 7 (by rfl) ⟨88358, by rfl⟩ : syracuseStep 7539925 = 176717) (by norm_num)
theorem B10053233 : Blo 1985435 10053233 := bstep (se 2 (by rfl) ⟨3769962, by rfl⟩ : syracuseStep 10053233 = 7539925) B7539925
theorem B6702155 : Blo 1985435 6702155 := bstep (se 1 (by rfl) ⟨5026616, by rfl⟩ : syracuseStep 6702155 = 10053233) B10053233
theorem B4468103 : Blo 1985435 4468103 := bstep (se 1 (by rfl) ⟨3351077, by rfl⟩ : syracuseStep 4468103 = 6702155) B6702155
theorem B2978735 : Blo 1985435 2978735 := bstep (se 1 (by rfl) ⟨2234051, by rfl⟩ : syracuseStep 2978735 = 4468103) B4468103
theorem B1985823 : Blo 1985435 1985823 := bstep (se 1 (by rfl) ⟨1489367, by rfl⟩ : syracuseStep 1985823 = 2978735) B2978735
theorem B2978741 : Blo 1985435 2978741 := bbase (se 5 (by rfl) ⟨139628, by rfl⟩ : syracuseStep 2978741 = 279257) (by norm_num)
theorem B1985827 : Blo 1985435 1985827 := bstep (se 1 (by rfl) ⟨1489370, by rfl⟩ : syracuseStep 1985827 = 2978741) B2978741
theorem B5026637 : Blo 1985435 5026637 := bbase (se 3 (by rfl) ⟨942494, by rfl⟩ : syracuseStep 5026637 = 1884989) (by norm_num)
theorem B3351091 : Blo 1985435 3351091 := bstep (se 1 (by rfl) ⟨2513318, by rfl⟩ : syracuseStep 3351091 = 5026637) B5026637
theorem B4468121 : Blo 1985435 4468121 := bstep (se 2 (by rfl) ⟨1675545, by rfl⟩ : syracuseStep 4468121 = 3351091) B3351091
theorem B2978747 : Blo 1985435 2978747 := bstep (se 1 (by rfl) ⟨2234060, by rfl⟩ : syracuseStep 2978747 = 4468121) B4468121
theorem B1985831 : Blo 1985435 1985831 := bstep (se 1 (by rfl) ⟨1489373, by rfl⟩ : syracuseStep 1985831 = 2978747) B2978747
theorem B2234065 : Blo 1985435 2234065 := bbase (se 2 (by rfl) ⟨837774, by rfl⟩ : syracuseStep 2234065 = 1675549) (by norm_num)
theorem B2978753 : Blo 1985435 2978753 := bstep (se 2 (by rfl) ⟨1117032, by rfl⟩ : syracuseStep 2978753 = 2234065) B2234065
theorem B1985835 : Blo 1985435 1985835 := bstep (se 1 (by rfl) ⟨1489376, by rfl⟩ : syracuseStep 1985835 = 2978753) B2978753
theorem B3224333 : Blo 1985435 3224333 := bbase (se 3 (by rfl) ⟨604562, by rfl⟩ : syracuseStep 3224333 = 1209125) (by norm_num)
theorem B8598221 : Blo 1985435 8598221 := bstep (se 3 (by rfl) ⟨1612166, by rfl⟩ : syracuseStep 8598221 = 3224333) B3224333
theorem B5732147 : Blo 1985435 5732147 := bstep (se 1 (by rfl) ⟨4299110, by rfl⟩ : syracuseStep 5732147 = 8598221) B8598221
theorem B3821431 : Blo 1985435 3821431 := bstep (se 1 (by rfl) ⟨2866073, by rfl⟩ : syracuseStep 3821431 = 5732147) B5732147
theorem B5095241 : Blo 1985435 5095241 := bstep (se 2 (by rfl) ⟨1910715, by rfl⟩ : syracuseStep 5095241 = 3821431) B3821431
theorem B3396827 : Blo 1985435 3396827 := bstep (se 1 (by rfl) ⟨2547620, by rfl⟩ : syracuseStep 3396827 = 5095241) B5095241
theorem B9058205 : Blo 1985435 9058205 := bstep (se 3 (by rfl) ⟨1698413, by rfl⟩ : syracuseStep 9058205 = 3396827) B3396827
theorem B6038803 : Blo 1985435 6038803 := bstep (se 1 (by rfl) ⟨4529102, by rfl⟩ : syracuseStep 6038803 = 9058205) B9058205
theorem B8051737 : Blo 1985435 8051737 := bstep (se 2 (by rfl) ⟨3019401, by rfl⟩ : syracuseStep 8051737 = 6038803) B6038803
theorem B10735649 : Blo 1985435 10735649 := bstep (se 2 (by rfl) ⟨4025868, by rfl⟩ : syracuseStep 10735649 = 8051737) B8051737
theorem B7157099 : Blo 1985435 7157099 := bstep (se 1 (by rfl) ⟨5367824, by rfl⟩ : syracuseStep 7157099 = 10735649) B10735649
theorem B4771399 : Blo 1985435 4771399 := bstep (se 1 (by rfl) ⟨3578549, by rfl⟩ : syracuseStep 4771399 = 7157099) B7157099
theorem B6361865 : Blo 1985435 6361865 := bstep (se 2 (by rfl) ⟨2385699, by rfl⟩ : syracuseStep 6361865 = 4771399) B4771399
theorem B4241243 : Blo 1985435 4241243 := bstep (se 1 (by rfl) ⟨3180932, by rfl⟩ : syracuseStep 4241243 = 6361865) B6361865
theorem B2827495 : Blo 1985435 2827495 := bstep (se 1 (by rfl) ⟨2120621, by rfl⟩ : syracuseStep 2827495 = 4241243) B4241243
theorem B3769993 : Blo 1985435 3769993 := bstep (se 2 (by rfl) ⟨1413747, by rfl⟩ : syracuseStep 3769993 = 2827495) B2827495
theorem B5026657 : Blo 1985435 5026657 := bstep (se 2 (by rfl) ⟨1884996, by rfl⟩ : syracuseStep 5026657 = 3769993) B3769993
theorem B6702209 : Blo 1985435 6702209 := bstep (se 2 (by rfl) ⟨2513328, by rfl⟩ : syracuseStep 6702209 = 5026657) B5026657
theorem B4468139 : Blo 1985435 4468139 := bstep (se 1 (by rfl) ⟨3351104, by rfl⟩ : syracuseStep 4468139 = 6702209) B6702209
theorem B2978759 : Blo 1985435 2978759 := bstep (se 1 (by rfl) ⟨2234069, by rfl⟩ : syracuseStep 2978759 = 4468139) B4468139
theorem B1985839 : Blo 1985435 1985839 := bstep (se 1 (by rfl) ⟨1489379, by rfl⟩ : syracuseStep 1985839 = 2978759) B2978759
theorem B2978765 : Blo 1985435 2978765 := bbase (se 3 (by rfl) ⟨558518, by rfl⟩ : syracuseStep 2978765 = 1117037) (by norm_num)
theorem B1985843 : Blo 1985435 1985843 := bstep (se 1 (by rfl) ⟨1489382, by rfl⟩ : syracuseStep 1985843 = 2978765) B2978765
theorem B4468157 : Blo 1985435 4468157 := bbase (se 3 (by rfl) ⟨837779, by rfl⟩ : syracuseStep 4468157 = 1675559) (by norm_num)
theorem B2978771 : Blo 1985435 2978771 := bstep (se 1 (by rfl) ⟨2234078, by rfl⟩ : syracuseStep 2978771 = 4468157) B4468157
theorem B1985847 : Blo 1985435 1985847 := bstep (se 1 (by rfl) ⟨1489385, by rfl⟩ : syracuseStep 1985847 = 2978771) B2978771
theorem B3351125 : Blo 1985435 3351125 := bbase (se 8 (by rfl) ⟨19635, by rfl⟩ : syracuseStep 3351125 = 39271) (by norm_num)
theorem B2234083 : Blo 1985435 2234083 := bstep (se 1 (by rfl) ⟨1675562, by rfl⟩ : syracuseStep 2234083 = 3351125) B3351125
theorem B2978777 : Blo 1985435 2978777 := bstep (se 2 (by rfl) ⟨1117041, by rfl⟩ : syracuseStep 2978777 = 2234083) B2234083
theorem B1985851 : Blo 1985435 1985851 := bstep (se 1 (by rfl) ⟨1489388, by rfl⟩ : syracuseStep 1985851 = 2978777) B2978777
theorem B10735733 : Blo 1985435 10735733 := bbase (se 5 (by rfl) ⟨503237, by rfl⟩ : syracuseStep 10735733 = 1006475) (by norm_num)
theorem B7157155 : Blo 1985435 7157155 := bstep (se 1 (by rfl) ⟨5367866, by rfl⟩ : syracuseStep 7157155 = 10735733) B10735733
theorem B9542873 : Blo 1985435 9542873 := bstep (se 2 (by rfl) ⟨3578577, by rfl⟩ : syracuseStep 9542873 = 7157155) B7157155
theorem B6361915 : Blo 1985435 6361915 := bstep (se 1 (by rfl) ⟨4771436, by rfl⟩ : syracuseStep 6361915 = 9542873) B9542873
theorem B8482553 : Blo 1985435 8482553 := bstep (se 2 (by rfl) ⟨3180957, by rfl⟩ : syracuseStep 8482553 = 6361915) B6361915
theorem B5655035 : Blo 1985435 5655035 := bstep (se 1 (by rfl) ⟨4241276, by rfl⟩ : syracuseStep 5655035 = 8482553) B8482553
theorem B15080093 : Blo 1985435 15080093 := bstep (se 3 (by rfl) ⟨2827517, by rfl⟩ : syracuseStep 15080093 = 5655035) B5655035
theorem B10053395 : Blo 1985435 10053395 := bstep (se 1 (by rfl) ⟨7540046, by rfl⟩ : syracuseStep 10053395 = 15080093) B15080093
theorem B6702263 : Blo 1985435 6702263 := bstep (se 1 (by rfl) ⟨5026697, by rfl⟩ : syracuseStep 6702263 = 10053395) B10053395
theorem B4468175 : Blo 1985435 4468175 := bstep (se 1 (by rfl) ⟨3351131, by rfl⟩ : syracuseStep 4468175 = 6702263) B6702263
theorem B2978783 : Blo 1985435 2978783 := bstep (se 1 (by rfl) ⟨2234087, by rfl⟩ : syracuseStep 2978783 = 4468175) B4468175
theorem B1985855 : Blo 1985435 1985855 := bstep (se 1 (by rfl) ⟨1489391, by rfl⟩ : syracuseStep 1985855 = 2978783) B2978783
theorem B2978789 : Blo 1985435 2978789 := bbase (se 4 (by rfl) ⟨279261, by rfl⟩ : syracuseStep 2978789 = 558523) (by norm_num)
theorem B1985859 : Blo 1985435 1985859 := bstep (se 1 (by rfl) ⟨1489394, by rfl⟩ : syracuseStep 1985859 = 2978789) B2978789
theorem B2866109 : Blo 1985435 2866109 := bbase (se 3 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 2866109 = 1074791) (by norm_num)
theorem B7642957 : Blo 1985435 7642957 := bstep (se 3 (by rfl) ⟨1433054, by rfl⟩ : syracuseStep 7642957 = 2866109) B2866109
theorem B10190609 : Blo 1985435 10190609 := bstep (se 2 (by rfl) ⟨3821478, by rfl⟩ : syracuseStep 10190609 = 7642957) B7642957
theorem B6793739 : Blo 1985435 6793739 := bstep (se 1 (by rfl) ⟨5095304, by rfl⟩ : syracuseStep 6793739 = 10190609) B10190609
theorem B4529159 : Blo 1985435 4529159 := bstep (se 1 (by rfl) ⟨3396869, by rfl⟩ : syracuseStep 4529159 = 6793739) B6793739
theorem B3019439 : Blo 1985435 3019439 := bstep (se 1 (by rfl) ⟨2264579, by rfl⟩ : syracuseStep 3019439 = 4529159) B4529159
theorem B2012959 : Blo 1985435 2012959 := bstep (se 1 (by rfl) ⟨1509719, by rfl⟩ : syracuseStep 2012959 = 3019439) B3019439
theorem B2683945 : Blo 1985435 2683945 := bstep (se 2 (by rfl) ⟨1006479, by rfl⟩ : syracuseStep 2683945 = 2012959) B2012959
theorem B3578593 : Blo 1985435 3578593 := bstep (se 2 (by rfl) ⟨1341972, by rfl⟩ : syracuseStep 3578593 = 2683945) B2683945
theorem B4771457 : Blo 1985435 4771457 := bstep (se 2 (by rfl) ⟨1789296, by rfl⟩ : syracuseStep 4771457 = 3578593) B3578593
theorem B3180971 : Blo 1985435 3180971 := bstep (se 1 (by rfl) ⟨2385728, by rfl⟩ : syracuseStep 3180971 = 4771457) B4771457
theorem B8482589 : Blo 1985435 8482589 := bstep (se 3 (by rfl) ⟨1590485, by rfl⟩ : syracuseStep 8482589 = 3180971) B3180971
theorem B5655059 : Blo 1985435 5655059 := bstep (se 1 (by rfl) ⟨4241294, by rfl⟩ : syracuseStep 5655059 = 8482589) B8482589
theorem B3770039 : Blo 1985435 3770039 := bstep (se 1 (by rfl) ⟨2827529, by rfl⟩ : syracuseStep 3770039 = 5655059) B5655059
theorem B2513359 : Blo 1985435 2513359 := bstep (se 1 (by rfl) ⟨1885019, by rfl⟩ : syracuseStep 2513359 = 3770039) B3770039
theorem B3351145 : Blo 1985435 3351145 := bstep (se 2 (by rfl) ⟨1256679, by rfl⟩ : syracuseStep 3351145 = 2513359) B2513359
theorem B4468193 : Blo 1985435 4468193 := bstep (se 2 (by rfl) ⟨1675572, by rfl⟩ : syracuseStep 4468193 = 3351145) B3351145
theorem B2978795 : Blo 1985435 2978795 := bstep (se 1 (by rfl) ⟨2234096, by rfl⟩ : syracuseStep 2978795 = 4468193) B4468193
theorem B1985863 : Blo 1985435 1985863 := bstep (se 1 (by rfl) ⟨1489397, by rfl⟩ : syracuseStep 1985863 = 2978795) B2978795
theorem B2234101 : Blo 1985435 2234101 := bbase (se 5 (by rfl) ⟨104723, by rfl⟩ : syracuseStep 2234101 = 209447) (by norm_num)
theorem B2978801 : Blo 1985435 2978801 := bstep (se 2 (by rfl) ⟨1117050, by rfl⟩ : syracuseStep 2978801 = 2234101) B2234101
theorem B1985867 : Blo 1985435 1985867 := bstep (se 1 (by rfl) ⟨1489400, by rfl⟩ : syracuseStep 1985867 = 2978801) B2978801
theorem B2513369 : Blo 1985435 2513369 := bbase (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) (by norm_num)
theorem B6702317 : Blo 1985435 6702317 := bstep (se 3 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 6702317 = 2513369) B2513369
theorem B4468211 : Blo 1985435 4468211 := bstep (se 1 (by rfl) ⟨3351158, by rfl⟩ : syracuseStep 4468211 = 6702317) B6702317
theorem B2978807 : Blo 1985435 2978807 := bstep (se 1 (by rfl) ⟨2234105, by rfl⟩ : syracuseStep 2978807 = 4468211) B4468211
theorem B1985871 : Blo 1985435 1985871 := bstep (se 1 (by rfl) ⟨1489403, by rfl⟩ : syracuseStep 1985871 = 2978807) B2978807
theorem B2978813 : Blo 1985435 2978813 := bbase (se 3 (by rfl) ⟨558527, by rfl⟩ : syracuseStep 2978813 = 1117055) (by norm_num)
theorem B1985875 : Blo 1985435 1985875 := bstep (se 1 (by rfl) ⟨1489406, by rfl⟩ : syracuseStep 1985875 = 2978813) B2978813
theorem B4468229 : Blo 1985435 4468229 := bbase (se 4 (by rfl) ⟨418896, by rfl⟩ : syracuseStep 4468229 = 837793) (by norm_num)
theorem B2978819 : Blo 1985435 2978819 := bstep (se 1 (by rfl) ⟨2234114, by rfl⟩ : syracuseStep 2978819 = 4468229) B4468229
theorem B1985879 : Blo 1985435 1985879 := bstep (se 1 (by rfl) ⟨1489409, by rfl⟩ : syracuseStep 1985879 = 2978819) B2978819
theorem B3770077 : Blo 1985435 3770077 := bbase (se 3 (by rfl) ⟨706889, by rfl⟩ : syracuseStep 3770077 = 1413779) (by norm_num)
theorem B5026769 : Blo 1985435 5026769 := bstep (se 2 (by rfl) ⟨1885038, by rfl⟩ : syracuseStep 5026769 = 3770077) B3770077
theorem B3351179 : Blo 1985435 3351179 := bstep (se 1 (by rfl) ⟨2513384, by rfl⟩ : syracuseStep 3351179 = 5026769) B5026769
theorem B2234119 : Blo 1985435 2234119 := bstep (se 1 (by rfl) ⟨1675589, by rfl⟩ : syracuseStep 2234119 = 3351179) B3351179
theorem B2978825 : Blo 1985435 2978825 := bstep (se 2 (by rfl) ⟨1117059, by rfl⟩ : syracuseStep 2978825 = 2234119) B2234119
theorem B1985883 : Blo 1985435 1985883 := bstep (se 1 (by rfl) ⟨1489412, by rfl⟩ : syracuseStep 1985883 = 2978825) B2978825
theorem B10053557 : Blo 1985435 10053557 := bbase (se 5 (by rfl) ⟨471260, by rfl⟩ : syracuseStep 10053557 = 942521) (by norm_num)
theorem B6702371 : Blo 1985435 6702371 := bstep (se 1 (by rfl) ⟨5026778, by rfl⟩ : syracuseStep 6702371 = 10053557) B10053557
theorem B4468247 : Blo 1985435 4468247 := bstep (se 1 (by rfl) ⟨3351185, by rfl⟩ : syracuseStep 4468247 = 6702371) B6702371
theorem B2978831 : Blo 1985435 2978831 := bstep (se 1 (by rfl) ⟨2234123, by rfl⟩ : syracuseStep 2978831 = 4468247) B4468247
theorem B1985887 : Blo 1985435 1985887 := bstep (se 1 (by rfl) ⟨1489415, by rfl⟩ : syracuseStep 1985887 = 2978831) B2978831
theorem B2978837 : Blo 1985435 2978837 := bbase (se 6 (by rfl) ⟨69816, by rfl⟩ : syracuseStep 2978837 = 139633) (by norm_num)
theorem B1985891 : Blo 1985435 1985891 := bstep (se 1 (by rfl) ⟨1489418, by rfl⟩ : syracuseStep 1985891 = 2978837) B2978837
theorem B4025981 : Blo 1985435 4025981 := bbase (se 3 (by rfl) ⟨754871, by rfl⟩ : syracuseStep 4025981 = 1509743) (by norm_num)
theorem B10735949 : Blo 1985435 10735949 := bstep (se 3 (by rfl) ⟨2012990, by rfl⟩ : syracuseStep 10735949 = 4025981) B4025981
theorem B28629197 : Blo 1985435 28629197 := bstep (se 3 (by rfl) ⟨5367974, by rfl⟩ : syracuseStep 28629197 = 10735949) B10735949
theorem B19086131 : Blo 1985435 19086131 := bstep (se 1 (by rfl) ⟨14314598, by rfl⟩ : syracuseStep 19086131 = 28629197) B28629197
theorem B12724087 : Blo 1985435 12724087 := bstep (se 1 (by rfl) ⟨9543065, by rfl⟩ : syracuseStep 12724087 = 19086131) B19086131
theorem B16965449 : Blo 1985435 16965449 := bstep (se 2 (by rfl) ⟨6362043, by rfl⟩ : syracuseStep 16965449 = 12724087) B12724087
theorem B11310299 : Blo 1985435 11310299 := bstep (se 1 (by rfl) ⟨8482724, by rfl⟩ : syracuseStep 11310299 = 16965449) B16965449
theorem B7540199 : Blo 1985435 7540199 := bstep (se 1 (by rfl) ⟨5655149, by rfl⟩ : syracuseStep 7540199 = 11310299) B11310299
theorem B5026799 : Blo 1985435 5026799 := bstep (se 1 (by rfl) ⟨3770099, by rfl⟩ : syracuseStep 5026799 = 7540199) B7540199
theorem B3351199 : Blo 1985435 3351199 := bstep (se 1 (by rfl) ⟨2513399, by rfl⟩ : syracuseStep 3351199 = 5026799) B5026799
theorem B4468265 : Blo 1985435 4468265 := bstep (se 2 (by rfl) ⟨1675599, by rfl⟩ : syracuseStep 4468265 = 3351199) B3351199
theorem B2978843 : Blo 1985435 2978843 := bstep (se 1 (by rfl) ⟨2234132, by rfl⟩ : syracuseStep 2978843 = 4468265) B4468265
theorem B1985895 : Blo 1985435 1985895 := bstep (se 1 (by rfl) ⟨1489421, by rfl⟩ : syracuseStep 1985895 = 2978843) B2978843
theorem B2234137 : Blo 1985435 2234137 := bbase (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) (by norm_num)
theorem B2978849 : Blo 1985435 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B1985899 : Blo 1985435 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B7540229 : Blo 1985435 7540229 := bbase (se 4 (by rfl) ⟨706896, by rfl⟩ : syracuseStep 7540229 = 1413793) (by norm_num)
theorem B5026819 : Blo 1985435 5026819 := bstep (se 1 (by rfl) ⟨3770114, by rfl⟩ : syracuseStep 5026819 = 7540229) B7540229
theorem B6702425 : Blo 1985435 6702425 := bstep (se 2 (by rfl) ⟨2513409, by rfl⟩ : syracuseStep 6702425 = 5026819) B5026819
theorem B4468283 : Blo 1985435 4468283 := bstep (se 1 (by rfl) ⟨3351212, by rfl⟩ : syracuseStep 4468283 = 6702425) B6702425
theorem B2978855 : Blo 1985435 2978855 := bstep (se 1 (by rfl) ⟨2234141, by rfl⟩ : syracuseStep 2978855 = 4468283) B4468283
theorem B1985903 : Blo 1985435 1985903 := bstep (se 1 (by rfl) ⟨1489427, by rfl⟩ : syracuseStep 1985903 = 2978855) B2978855
theorem B2978861 : Blo 1985435 2978861 := bbase (se 3 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 2978861 = 1117073) (by norm_num)
theorem B1985907 : Blo 1985435 1985907 := bstep (se 1 (by rfl) ⟨1489430, by rfl⟩ : syracuseStep 1985907 = 2978861) B2978861
theorem B4468301 : Blo 1985435 4468301 := bbase (se 3 (by rfl) ⟨837806, by rfl⟩ : syracuseStep 4468301 = 1675613) (by norm_num)
theorem B2978867 : Blo 1985435 2978867 := bstep (se 1 (by rfl) ⟨2234150, by rfl⟩ : syracuseStep 2978867 = 4468301) B4468301
theorem B1985911 : Blo 1985435 1985911 := bstep (se 1 (by rfl) ⟨1489433, by rfl⟩ : syracuseStep 1985911 = 2978867) B2978867
theorem B2513425 : Blo 1985435 2513425 := bbase (se 2 (by rfl) ⟨942534, by rfl⟩ : syracuseStep 2513425 = 1885069) (by norm_num)
theorem B3351233 : Blo 1985435 3351233 := bstep (se 2 (by rfl) ⟨1256712, by rfl⟩ : syracuseStep 3351233 = 2513425) B2513425
theorem B2234155 : Blo 1985435 2234155 := bstep (se 1 (by rfl) ⟨1675616, by rfl⟩ : syracuseStep 2234155 = 3351233) B3351233
theorem B2978873 : Blo 1985435 2978873 := bstep (se 2 (by rfl) ⟨1117077, by rfl⟩ : syracuseStep 2978873 = 2234155) B2234155
theorem B1985915 : Blo 1985435 1985915 := bstep (se 1 (by rfl) ⟨1489436, by rfl⟩ : syracuseStep 1985915 = 2978873) B2978873
theorem B4241413 : Blo 1985435 4241413 := bbase (se 4 (by rfl) ⟨397632, by rfl⟩ : syracuseStep 4241413 = 795265) (by norm_num)
theorem B22620869 : Blo 1985435 22620869 := bstep (se 4 (by rfl) ⟨2120706, by rfl⟩ : syracuseStep 22620869 = 4241413) B4241413
theorem B15080579 : Blo 1985435 15080579 := bstep (se 1 (by rfl) ⟨11310434, by rfl⟩ : syracuseStep 15080579 = 22620869) B22620869
theorem B10053719 : Blo 1985435 10053719 := bstep (se 1 (by rfl) ⟨7540289, by rfl⟩ : syracuseStep 10053719 = 15080579) B15080579
theorem B6702479 : Blo 1985435 6702479 := bstep (se 1 (by rfl) ⟨5026859, by rfl⟩ : syracuseStep 6702479 = 10053719) B10053719
theorem B4468319 : Blo 1985435 4468319 := bstep (se 1 (by rfl) ⟨3351239, by rfl⟩ : syracuseStep 4468319 = 6702479) B6702479
theorem B2978879 : Blo 1985435 2978879 := bstep (se 1 (by rfl) ⟨2234159, by rfl⟩ : syracuseStep 2978879 = 4468319) B4468319
theorem B1985919 : Blo 1985435 1985919 := bstep (se 1 (by rfl) ⟨1489439, by rfl⟩ : syracuseStep 1985919 = 2978879) B2978879
theorem B2978885 : Blo 1985435 2978885 := bbase (se 4 (by rfl) ⟨279270, by rfl⟩ : syracuseStep 2978885 = 558541) (by norm_num)
theorem B1985923 : Blo 1985435 1985923 := bstep (se 1 (by rfl) ⟨1489442, by rfl⟩ : syracuseStep 1985923 = 2978885) B2978885
theorem B3351253 : Blo 1985435 3351253 := bbase (se 7 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 3351253 = 78545) (by norm_num)
theorem B4468337 : Blo 1985435 4468337 := bstep (se 2 (by rfl) ⟨1675626, by rfl⟩ : syracuseStep 4468337 = 3351253) B3351253
theorem B2978891 : Blo 1985435 2978891 := bstep (se 1 (by rfl) ⟨2234168, by rfl⟩ : syracuseStep 2978891 = 4468337) B4468337
theorem B1985927 : Blo 1985435 1985927 := bstep (se 1 (by rfl) ⟨1489445, by rfl⟩ : syracuseStep 1985927 = 2978891) B2978891
theorem B2234173 : Blo 1985435 2234173 := bbase (se 3 (by rfl) ⟨418907, by rfl⟩ : syracuseStep 2234173 = 837815) (by norm_num)
theorem B2978897 : Blo 1985435 2978897 := bstep (se 2 (by rfl) ⟨1117086, by rfl⟩ : syracuseStep 2978897 = 2234173) B2234173
theorem B1985931 : Blo 1985435 1985931 := bstep (se 1 (by rfl) ⟨1489448, by rfl⟩ : syracuseStep 1985931 = 2978897) B2978897
theorem B6702533 : Blo 1985435 6702533 := bbase (se 4 (by rfl) ⟨628362, by rfl⟩ : syracuseStep 6702533 = 1256725) (by norm_num)
theorem B4468355 : Blo 1985435 4468355 := bstep (se 1 (by rfl) ⟨3351266, by rfl⟩ : syracuseStep 4468355 = 6702533) B6702533
theorem B2978903 : Blo 1985435 2978903 := bstep (se 1 (by rfl) ⟨2234177, by rfl⟩ : syracuseStep 2978903 = 4468355) B4468355
theorem B1985935 : Blo 1985435 1985935 := bstep (se 1 (by rfl) ⟨1489451, by rfl⟩ : syracuseStep 1985935 = 2978903) B2978903
theorem B2978909 : Blo 1985435 2978909 := bbase (se 3 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 2978909 = 1117091) (by norm_num)
theorem B1985939 : Blo 1985435 1985939 := bstep (se 1 (by rfl) ⟨1489454, by rfl⟩ : syracuseStep 1985939 = 2978909) B2978909
theorem B4468373 : Blo 1985435 4468373 := bbase (se 6 (by rfl) ⟨104727, by rfl⟩ : syracuseStep 4468373 = 209455) (by norm_num)
theorem B2978915 : Blo 1985435 2978915 := bstep (se 1 (by rfl) ⟨2234186, by rfl⟩ : syracuseStep 2978915 = 4468373) B4468373
theorem B1985943 : Blo 1985435 1985943 := bstep (se 1 (by rfl) ⟨1489457, by rfl⟩ : syracuseStep 1985943 = 2978915) B2978915
theorem B2120737 : Blo 1985435 2120737 := bbase (se 2 (by rfl) ⟨795276, by rfl⟩ : syracuseStep 2120737 = 1590553) (by norm_num)
theorem B2827649 : Blo 1985435 2827649 := bstep (se 2 (by rfl) ⟨1060368, by rfl⟩ : syracuseStep 2827649 = 2120737) B2120737
theorem B7540397 : Blo 1985435 7540397 := bstep (se 3 (by rfl) ⟨1413824, by rfl⟩ : syracuseStep 7540397 = 2827649) B2827649
theorem B5026931 : Blo 1985435 5026931 := bstep (se 1 (by rfl) ⟨3770198, by rfl⟩ : syracuseStep 5026931 = 7540397) B7540397
theorem B3351287 : Blo 1985435 3351287 := bstep (se 1 (by rfl) ⟨2513465, by rfl⟩ : syracuseStep 3351287 = 5026931) B5026931
theorem B2234191 : Blo 1985435 2234191 := bstep (se 1 (by rfl) ⟨1675643, by rfl⟩ : syracuseStep 2234191 = 3351287) B3351287
theorem B2978921 : Blo 1985435 2978921 := bstep (se 2 (by rfl) ⟨1117095, by rfl⟩ : syracuseStep 2978921 = 2234191) B2234191
theorem B1985947 : Blo 1985435 1985947 := bstep (se 1 (by rfl) ⟨1489460, by rfl⟩ : syracuseStep 1985947 = 2978921) B2978921
theorem B2295577 : Blo 1985435 2295577 := bbase (se 2 (by rfl) ⟨860841, by rfl⟩ : syracuseStep 2295577 = 1721683) (by norm_num)
theorem B12243077 : Blo 1985435 12243077 := bstep (se 4 (by rfl) ⟨1147788, by rfl⟩ : syracuseStep 12243077 = 2295577) B2295577
theorem B8162051 : Blo 1985435 8162051 := bstep (se 1 (by rfl) ⟨6121538, by rfl⟩ : syracuseStep 8162051 = 12243077) B12243077
theorem B21765469 : Blo 1985435 21765469 := bstep (se 3 (by rfl) ⟨4081025, by rfl⟩ : syracuseStep 21765469 = 8162051) B8162051
theorem B29020625 : Blo 1985435 29020625 := bstep (se 2 (by rfl) ⟨10882734, by rfl⟩ : syracuseStep 29020625 = 21765469) B21765469
theorem B19347083 : Blo 1985435 19347083 := bstep (se 1 (by rfl) ⟨14510312, by rfl⟩ : syracuseStep 19347083 = 29020625) B29020625
theorem B12898055 : Blo 1985435 12898055 := bstep (se 1 (by rfl) ⟨9673541, by rfl⟩ : syracuseStep 12898055 = 19347083) B19347083
theorem B34394813 : Blo 1985435 34394813 := bstep (se 3 (by rfl) ⟨6449027, by rfl⟩ : syracuseStep 34394813 = 12898055) B12898055
theorem B22929875 : Blo 1985435 22929875 := bstep (se 1 (by rfl) ⟨17197406, by rfl⟩ : syracuseStep 22929875 = 34394813) B34394813
theorem B15286583 : Blo 1985435 15286583 := bstep (se 1 (by rfl) ⟨11464937, by rfl⟩ : syracuseStep 15286583 = 22929875) B22929875
theorem B10191055 : Blo 1985435 10191055 := bstep (se 1 (by rfl) ⟨7643291, by rfl⟩ : syracuseStep 10191055 = 15286583) B15286583
theorem B13588073 : Blo 1985435 13588073 := bstep (se 2 (by rfl) ⟨5095527, by rfl⟩ : syracuseStep 13588073 = 10191055) B10191055
theorem B9058715 : Blo 1985435 9058715 := bstep (se 1 (by rfl) ⟨6794036, by rfl⟩ : syracuseStep 9058715 = 13588073) B13588073
theorem B6039143 : Blo 1985435 6039143 := bstep (se 1 (by rfl) ⟨4529357, by rfl⟩ : syracuseStep 6039143 = 9058715) B9058715
theorem B4026095 : Blo 1985435 4026095 := bstep (se 1 (by rfl) ⟨3019571, by rfl⟩ : syracuseStep 4026095 = 6039143) B6039143
theorem B2684063 : Blo 1985435 2684063 := bstep (se 1 (by rfl) ⟨2013047, by rfl⟩ : syracuseStep 2684063 = 4026095) B4026095
theorem B7157501 : Blo 1985435 7157501 := bstep (se 3 (by rfl) ⟨1342031, by rfl⟩ : syracuseStep 7157501 = 2684063) B2684063
theorem B4771667 : Blo 1985435 4771667 := bstep (se 1 (by rfl) ⟨3578750, by rfl⟩ : syracuseStep 4771667 = 7157501) B7157501
theorem B12724445 : Blo 1985435 12724445 := bstep (se 3 (by rfl) ⟨2385833, by rfl⟩ : syracuseStep 12724445 = 4771667) B4771667
theorem B8482963 : Blo 1985435 8482963 := bstep (se 1 (by rfl) ⟨6362222, by rfl⟩ : syracuseStep 8482963 = 12724445) B12724445
theorem B11310617 : Blo 1985435 11310617 := bstep (se 2 (by rfl) ⟨4241481, by rfl⟩ : syracuseStep 11310617 = 8482963) B8482963
theorem B7540411 : Blo 1985435 7540411 := bstep (se 1 (by rfl) ⟨5655308, by rfl⟩ : syracuseStep 7540411 = 11310617) B11310617
theorem B10053881 : Blo 1985435 10053881 := bstep (se 2 (by rfl) ⟨3770205, by rfl⟩ : syracuseStep 10053881 = 7540411) B7540411
theorem B6702587 : Blo 1985435 6702587 := bstep (se 1 (by rfl) ⟨5026940, by rfl⟩ : syracuseStep 6702587 = 10053881) B10053881
theorem B4468391 : Blo 1985435 4468391 := bstep (se 1 (by rfl) ⟨3351293, by rfl⟩ : syracuseStep 4468391 = 6702587) B6702587
theorem B2978927 : Blo 1985435 2978927 := bstep (se 1 (by rfl) ⟨2234195, by rfl⟩ : syracuseStep 2978927 = 4468391) B4468391
theorem B1985951 : Blo 1985435 1985951 := bstep (se 1 (by rfl) ⟨1489463, by rfl⟩ : syracuseStep 1985951 = 2978927) B2978927
theorem B2978933 : Blo 1985435 2978933 := bbase (se 5 (by rfl) ⟨139637, by rfl⟩ : syracuseStep 2978933 = 279275) (by norm_num)
theorem B1985955 : Blo 1985435 1985955 := bstep (se 1 (by rfl) ⟨1489466, by rfl⟩ : syracuseStep 1985955 = 2978933) B2978933
theorem B3770221 : Blo 1985435 3770221 := bbase (se 3 (by rfl) ⟨706916, by rfl⟩ : syracuseStep 3770221 = 1413833) (by norm_num)
theorem B5026961 : Blo 1985435 5026961 := bstep (se 2 (by rfl) ⟨1885110, by rfl⟩ : syracuseStep 5026961 = 3770221) B3770221
theorem B3351307 : Blo 1985435 3351307 := bstep (se 1 (by rfl) ⟨2513480, by rfl⟩ : syracuseStep 3351307 = 5026961) B5026961
theorem B4468409 : Blo 1985435 4468409 := bstep (se 2 (by rfl) ⟨1675653, by rfl⟩ : syracuseStep 4468409 = 3351307) B3351307
theorem B2978939 : Blo 1985435 2978939 := bstep (se 1 (by rfl) ⟨2234204, by rfl⟩ : syracuseStep 2978939 = 4468409) B4468409
theorem B1985959 : Blo 1985435 1985959 := bstep (se 1 (by rfl) ⟨1489469, by rfl⟩ : syracuseStep 1985959 = 2978939) B2978939
theorem B2234209 : Blo 1985435 2234209 := bbase (se 2 (by rfl) ⟨837828, by rfl⟩ : syracuseStep 2234209 = 1675657) (by norm_num)
theorem B2978945 : Blo 1985435 2978945 := bstep (se 2 (by rfl) ⟨1117104, by rfl⟩ : syracuseStep 2978945 = 2234209) B2234209
theorem B1985963 : Blo 1985435 1985963 := bstep (se 1 (by rfl) ⟨1489472, by rfl⟩ : syracuseStep 1985963 = 2978945) B2978945
theorem B5026981 : Blo 1985435 5026981 := bbase (se 4 (by rfl) ⟨471279, by rfl⟩ : syracuseStep 5026981 = 942559) (by norm_num)
theorem B6702641 : Blo 1985435 6702641 := bstep (se 2 (by rfl) ⟨2513490, by rfl⟩ : syracuseStep 6702641 = 5026981) B5026981
theorem B4468427 : Blo 1985435 4468427 := bstep (se 1 (by rfl) ⟨3351320, by rfl⟩ : syracuseStep 4468427 = 6702641) B6702641
theorem B2978951 : Blo 1985435 2978951 := bstep (se 1 (by rfl) ⟨2234213, by rfl⟩ : syracuseStep 2978951 = 4468427) B4468427
theorem B1985967 : Blo 1985435 1985967 := bstep (se 1 (by rfl) ⟨1489475, by rfl⟩ : syracuseStep 1985967 = 2978951) B2978951
theorem B2978957 : Blo 1985435 2978957 := bbase (se 3 (by rfl) ⟨558554, by rfl⟩ : syracuseStep 2978957 = 1117109) (by norm_num)
theorem B1985971 : Blo 1985435 1985971 := bstep (se 1 (by rfl) ⟨1489478, by rfl⟩ : syracuseStep 1985971 = 2978957) B2978957
theorem B4468445 : Blo 1985435 4468445 := bbase (se 3 (by rfl) ⟨837833, by rfl⟩ : syracuseStep 4468445 = 1675667) (by norm_num)
theorem B2978963 : Blo 1985435 2978963 := bstep (se 1 (by rfl) ⟨2234222, by rfl⟩ : syracuseStep 2978963 = 4468445) B4468445
theorem B1985975 : Blo 1985435 1985975 := bstep (se 1 (by rfl) ⟨1489481, by rfl⟩ : syracuseStep 1985975 = 2978963) B2978963
theorem B3351341 : Blo 1985435 3351341 := bbase (se 3 (by rfl) ⟨628376, by rfl⟩ : syracuseStep 3351341 = 1256753) (by norm_num)
theorem B2234227 : Blo 1985435 2234227 := bstep (se 1 (by rfl) ⟨1675670, by rfl⟩ : syracuseStep 2234227 = 3351341) B3351341
theorem B2978969 : Blo 1985435 2978969 := bstep (se 2 (by rfl) ⟨1117113, by rfl⟩ : syracuseStep 2978969 = 2234227) B2234227
theorem B1985979 : Blo 1985435 1985979 := bstep (se 1 (by rfl) ⟨1489484, by rfl⟩ : syracuseStep 1985979 = 2978969) B2978969
theorem B2040545 : Blo 1985435 2040545 := bbase (se 2 (by rfl) ⟨765204, by rfl⟩ : syracuseStep 2040545 = 1530409) (by norm_num)
theorem B5441453 : Blo 1985435 5441453 := bstep (se 3 (by rfl) ⟨1020272, by rfl⟩ : syracuseStep 5441453 = 2040545) B2040545
theorem B3627635 : Blo 1985435 3627635 := bstep (se 1 (by rfl) ⟨2720726, by rfl⟩ : syracuseStep 3627635 = 5441453) B5441453
theorem B38694773 : Blo 1985435 38694773 := bstep (se 5 (by rfl) ⟨1813817, by rfl⟩ : syracuseStep 38694773 = 3627635) B3627635
theorem B25796515 : Blo 1985435 25796515 := bstep (se 1 (by rfl) ⟨19347386, by rfl⟩ : syracuseStep 25796515 = 38694773) B38694773
theorem B34395353 : Blo 1985435 34395353 := bstep (se 2 (by rfl) ⟨12898257, by rfl⟩ : syracuseStep 34395353 = 25796515) B25796515
theorem B22930235 : Blo 1985435 22930235 := bstep (se 1 (by rfl) ⟨17197676, by rfl⟩ : syracuseStep 22930235 = 34395353) B34395353
theorem B15286823 : Blo 1985435 15286823 := bstep (se 1 (by rfl) ⟨11465117, by rfl⟩ : syracuseStep 15286823 = 22930235) B22930235
theorem B10191215 : Blo 1985435 10191215 := bstep (se 1 (by rfl) ⟨7643411, by rfl⟩ : syracuseStep 10191215 = 15286823) B15286823
theorem B27176573 : Blo 1985435 27176573 := bstep (se 3 (by rfl) ⟨5095607, by rfl⟩ : syracuseStep 27176573 = 10191215) B10191215
theorem B72470861 : Blo 1985435 72470861 := bstep (se 3 (by rfl) ⟨13588286, by rfl⟩ : syracuseStep 72470861 = 27176573) B27176573
theorem B48313907 : Blo 1985435 48313907 := bstep (se 1 (by rfl) ⟨36235430, by rfl⟩ : syracuseStep 48313907 = 72470861) B72470861
theorem B32209271 : Blo 1985435 32209271 := bstep (se 1 (by rfl) ⟨24156953, by rfl⟩ : syracuseStep 32209271 = 48313907) B48313907
theorem B21472847 : Blo 1985435 21472847 := bstep (se 1 (by rfl) ⟨16104635, by rfl⟩ : syracuseStep 21472847 = 32209271) B32209271
theorem B14315231 : Blo 1985435 14315231 := bstep (se 1 (by rfl) ⟨10736423, by rfl⟩ : syracuseStep 14315231 = 21472847) B21472847
theorem B38173949 : Blo 1985435 38173949 := bstep (se 3 (by rfl) ⟨7157615, by rfl⟩ : syracuseStep 38173949 = 14315231) B14315231
theorem B25449299 : Blo 1985435 25449299 := bstep (se 1 (by rfl) ⟨19086974, by rfl⟩ : syracuseStep 25449299 = 38173949) B38173949
theorem B16966199 : Blo 1985435 16966199 := bstep (se 1 (by rfl) ⟨12724649, by rfl⟩ : syracuseStep 16966199 = 25449299) B25449299
theorem B11310799 : Blo 1985435 11310799 := bstep (se 1 (by rfl) ⟨8483099, by rfl⟩ : syracuseStep 11310799 = 16966199) B16966199
theorem B15081065 : Blo 1985435 15081065 := bstep (se 2 (by rfl) ⟨5655399, by rfl⟩ : syracuseStep 15081065 = 11310799) B11310799
theorem B10054043 : Blo 1985435 10054043 := bstep (se 1 (by rfl) ⟨7540532, by rfl⟩ : syracuseStep 10054043 = 15081065) B15081065
theorem B6702695 : Blo 1985435 6702695 := bstep (se 1 (by rfl) ⟨5027021, by rfl⟩ : syracuseStep 6702695 = 10054043) B10054043
theorem B4468463 : Blo 1985435 4468463 := bstep (se 1 (by rfl) ⟨3351347, by rfl⟩ : syracuseStep 4468463 = 6702695) B6702695
theorem B2978975 : Blo 1985435 2978975 := bstep (se 1 (by rfl) ⟨2234231, by rfl⟩ : syracuseStep 2978975 = 4468463) B4468463
theorem B1985983 : Blo 1985435 1985983 := bstep (se 1 (by rfl) ⟨1489487, by rfl⟩ : syracuseStep 1985983 = 2978975) B2978975
theorem B2978981 : Blo 1985435 2978981 := bbase (se 4 (by rfl) ⟨279279, by rfl⟩ : syracuseStep 2978981 = 558559) (by norm_num)
theorem B1985987 : Blo 1985435 1985987 := bstep (se 1 (by rfl) ⟨1489490, by rfl⟩ : syracuseStep 1985987 = 2978981) B2978981
theorem B2513521 : Blo 1985435 2513521 := bbase (se 2 (by rfl) ⟨942570, by rfl⟩ : syracuseStep 2513521 = 1885141) (by norm_num)
theorem B3351361 : Blo 1985435 3351361 := bstep (se 2 (by rfl) ⟨1256760, by rfl⟩ : syracuseStep 3351361 = 2513521) B2513521
theorem B4468481 : Blo 1985435 4468481 := bstep (se 2 (by rfl) ⟨1675680, by rfl⟩ : syracuseStep 4468481 = 3351361) B3351361
theorem B2978987 : Blo 1985435 2978987 := bstep (se 1 (by rfl) ⟨2234240, by rfl⟩ : syracuseStep 2978987 = 4468481) B4468481
theorem B1985991 : Blo 1985435 1985991 := bstep (se 1 (by rfl) ⟨1489493, by rfl⟩ : syracuseStep 1985991 = 2978987) B2978987
theorem B2234245 : Blo 1985435 2234245 := bbase (se 4 (by rfl) ⟨209460, by rfl⟩ : syracuseStep 2234245 = 418921) (by norm_num)
theorem B2978993 : Blo 1985435 2978993 := bstep (se 2 (by rfl) ⟨1117122, by rfl⟩ : syracuseStep 2978993 = 2234245) B2234245
theorem B1985995 : Blo 1985435 1985995 := bstep (se 1 (by rfl) ⟨1489496, by rfl⟩ : syracuseStep 1985995 = 2978993) B2978993
theorem B3181189 : Blo 1985435 3181189 := bbase (se 4 (by rfl) ⟨298236, by rfl⟩ : syracuseStep 3181189 = 596473) (by norm_num)
theorem B4241585 : Blo 1985435 4241585 := bstep (se 2 (by rfl) ⟨1590594, by rfl⟩ : syracuseStep 4241585 = 3181189) B3181189
theorem B2827723 : Blo 1985435 2827723 := bstep (se 1 (by rfl) ⟨2120792, by rfl⟩ : syracuseStep 2827723 = 4241585) B4241585
theorem B3770297 : Blo 1985435 3770297 := bstep (se 2 (by rfl) ⟨1413861, by rfl⟩ : syracuseStep 3770297 = 2827723) B2827723
theorem B2513531 : Blo 1985435 2513531 := bstep (se 1 (by rfl) ⟨1885148, by rfl⟩ : syracuseStep 2513531 = 3770297) B3770297
theorem B6702749 : Blo 1985435 6702749 := bstep (se 3 (by rfl) ⟨1256765, by rfl⟩ : syracuseStep 6702749 = 2513531) B2513531
theorem B4468499 : Blo 1985435 4468499 := bstep (se 1 (by rfl) ⟨3351374, by rfl⟩ : syracuseStep 4468499 = 6702749) B6702749
theorem B2978999 : Blo 1985435 2978999 := bstep (se 1 (by rfl) ⟨2234249, by rfl⟩ : syracuseStep 2978999 = 4468499) B4468499
theorem B1985999 : Blo 1985435 1985999 := bstep (se 1 (by rfl) ⟨1489499, by rfl⟩ : syracuseStep 1985999 = 2978999) B2978999
theorem B2979005 : Blo 1985435 2979005 := bbase (se 3 (by rfl) ⟨558563, by rfl⟩ : syracuseStep 2979005 = 1117127) (by norm_num)
theorem B1986003 : Blo 1985435 1986003 := bstep (se 1 (by rfl) ⟨1489502, by rfl⟩ : syracuseStep 1986003 = 2979005) B2979005
theorem B4468517 : Blo 1985435 4468517 := bbase (se 4 (by rfl) ⟨418923, by rfl⟩ : syracuseStep 4468517 = 837847) (by norm_num)
theorem B2979011 : Blo 1985435 2979011 := bstep (se 1 (by rfl) ⟨2234258, by rfl⟩ : syracuseStep 2979011 = 4468517) B4468517
theorem B1986007 : Blo 1985435 1986007 := bstep (se 1 (by rfl) ⟨1489505, by rfl⟩ : syracuseStep 1986007 = 2979011) B2979011
theorem B5027093 : Blo 1985435 5027093 := bbase (se 6 (by rfl) ⟨117822, by rfl⟩ : syracuseStep 5027093 = 235645) (by norm_num)
theorem B3351395 : Blo 1985435 3351395 := bstep (se 1 (by rfl) ⟨2513546, by rfl⟩ : syracuseStep 3351395 = 5027093) B5027093
theorem B2234263 : Blo 1985435 2234263 := bstep (se 1 (by rfl) ⟨1675697, by rfl⟩ : syracuseStep 2234263 = 3351395) B3351395
theorem B2979017 : Blo 1985435 2979017 := bstep (se 2 (by rfl) ⟨1117131, by rfl⟩ : syracuseStep 2979017 = 2234263) B2234263
theorem B1986011 : Blo 1985435 1986011 := bstep (se 1 (by rfl) ⟨1489508, by rfl⟩ : syracuseStep 1986011 = 2979017) B2979017
theorem B8483237 : Blo 1985435 8483237 := bbase (se 4 (by rfl) ⟨795303, by rfl⟩ : syracuseStep 8483237 = 1590607) (by norm_num)
theorem B5655491 : Blo 1985435 5655491 := bstep (se 1 (by rfl) ⟨4241618, by rfl⟩ : syracuseStep 5655491 = 8483237) B8483237
theorem B3770327 : Blo 1985435 3770327 := bstep (se 1 (by rfl) ⟨2827745, by rfl⟩ : syracuseStep 3770327 = 5655491) B5655491
theorem B10054205 : Blo 1985435 10054205 := bstep (se 3 (by rfl) ⟨1885163, by rfl⟩ : syracuseStep 10054205 = 3770327) B3770327
theorem B6702803 : Blo 1985435 6702803 := bstep (se 1 (by rfl) ⟨5027102, by rfl⟩ : syracuseStep 6702803 = 10054205) B10054205
theorem B4468535 : Blo 1985435 4468535 := bstep (se 1 (by rfl) ⟨3351401, by rfl⟩ : syracuseStep 4468535 = 6702803) B6702803
theorem B2979023 : Blo 1985435 2979023 := bstep (se 1 (by rfl) ⟨2234267, by rfl⟩ : syracuseStep 2979023 = 4468535) B4468535
theorem B1986015 : Blo 1985435 1986015 := bstep (se 1 (by rfl) ⟨1489511, by rfl⟩ : syracuseStep 1986015 = 2979023) B2979023
theorem B2979029 : Blo 1985435 2979029 := bbase (se 7 (by rfl) ⟨34910, by rfl⟩ : syracuseStep 2979029 = 69821) (by norm_num)
theorem B1986019 : Blo 1985435 1986019 := bstep (se 1 (by rfl) ⟨1489514, by rfl⟩ : syracuseStep 1986019 = 2979029) B2979029
theorem B2827757 : Blo 1985435 2827757 := bbase (se 3 (by rfl) ⟨530204, by rfl⟩ : syracuseStep 2827757 = 1060409) (by norm_num)
theorem B7540685 : Blo 1985435 7540685 := bstep (se 3 (by rfl) ⟨1413878, by rfl⟩ : syracuseStep 7540685 = 2827757) B2827757
theorem B5027123 : Blo 1985435 5027123 := bstep (se 1 (by rfl) ⟨3770342, by rfl⟩ : syracuseStep 5027123 = 7540685) B7540685
theorem B3351415 : Blo 1985435 3351415 := bstep (se 1 (by rfl) ⟨2513561, by rfl⟩ : syracuseStep 3351415 = 5027123) B5027123
theorem B4468553 : Blo 1985435 4468553 := bstep (se 2 (by rfl) ⟨1675707, by rfl⟩ : syracuseStep 4468553 = 3351415) B3351415
theorem B2979035 : Blo 1985435 2979035 := bstep (se 1 (by rfl) ⟨2234276, by rfl⟩ : syracuseStep 2979035 = 4468553) B4468553
theorem B1986023 : Blo 1985435 1986023 := bstep (se 1 (by rfl) ⟨1489517, by rfl⟩ : syracuseStep 1986023 = 2979035) B2979035
theorem B2234281 : Blo 1985435 2234281 := bbase (se 2 (by rfl) ⟨837855, by rfl⟩ : syracuseStep 2234281 = 1675711) (by norm_num)
theorem B2979041 : Blo 1985435 2979041 := bstep (se 2 (by rfl) ⟨1117140, by rfl⟩ : syracuseStep 2979041 = 2234281) B2234281
theorem B1986027 : Blo 1985435 1986027 := bstep (se 1 (by rfl) ⟨1489520, by rfl⟩ : syracuseStep 1986027 = 2979041) B2979041
theorem B6794309 : Blo 1985435 6794309 := bbase (se 4 (by rfl) ⟨636966, by rfl⟩ : syracuseStep 6794309 = 1273933) (by norm_num)
theorem B4529539 : Blo 1985435 4529539 := bstep (se 1 (by rfl) ⟨3397154, by rfl⟩ : syracuseStep 4529539 = 6794309) B6794309
theorem B24157541 : Blo 1985435 24157541 := bstep (se 4 (by rfl) ⟨2264769, by rfl⟩ : syracuseStep 24157541 = 4529539) B4529539
theorem B16105027 : Blo 1985435 16105027 := bstep (se 1 (by rfl) ⟨12078770, by rfl⟩ : syracuseStep 16105027 = 24157541) B24157541
theorem B21473369 : Blo 1985435 21473369 := bstep (se 2 (by rfl) ⟨8052513, by rfl⟩ : syracuseStep 21473369 = 16105027) B16105027
theorem B14315579 : Blo 1985435 14315579 := bstep (se 1 (by rfl) ⟨10736684, by rfl⟩ : syracuseStep 14315579 = 21473369) B21473369
theorem B9543719 : Blo 1985435 9543719 := bstep (se 1 (by rfl) ⟨7157789, by rfl⟩ : syracuseStep 9543719 = 14315579) B14315579
theorem B6362479 : Blo 1985435 6362479 := bstep (se 1 (by rfl) ⟨4771859, by rfl⟩ : syracuseStep 6362479 = 9543719) B9543719
theorem B8483305 : Blo 1985435 8483305 := bstep (se 2 (by rfl) ⟨3181239, by rfl⟩ : syracuseStep 8483305 = 6362479) B6362479
theorem B11311073 : Blo 1985435 11311073 := bstep (se 2 (by rfl) ⟨4241652, by rfl⟩ : syracuseStep 11311073 = 8483305) B8483305
theorem B7540715 : Blo 1985435 7540715 := bstep (se 1 (by rfl) ⟨5655536, by rfl⟩ : syracuseStep 7540715 = 11311073) B11311073
theorem B5027143 : Blo 1985435 5027143 := bstep (se 1 (by rfl) ⟨3770357, by rfl⟩ : syracuseStep 5027143 = 7540715) B7540715
theorem B6702857 : Blo 1985435 6702857 := bstep (se 2 (by rfl) ⟨2513571, by rfl⟩ : syracuseStep 6702857 = 5027143) B5027143
theorem B4468571 : Blo 1985435 4468571 := bstep (se 1 (by rfl) ⟨3351428, by rfl⟩ : syracuseStep 4468571 = 6702857) B6702857
theorem B2979047 : Blo 1985435 2979047 := bstep (se 1 (by rfl) ⟨2234285, by rfl⟩ : syracuseStep 2979047 = 4468571) B4468571
theorem B1986031 : Blo 1985435 1986031 := bstep (se 1 (by rfl) ⟨1489523, by rfl⟩ : syracuseStep 1986031 = 2979047) B2979047
theorem B2979053 : Blo 1985435 2979053 := bbase (se 3 (by rfl) ⟨558572, by rfl⟩ : syracuseStep 2979053 = 1117145) (by norm_num)
theorem B1986035 : Blo 1985435 1986035 := bstep (se 1 (by rfl) ⟨1489526, by rfl⟩ : syracuseStep 1986035 = 2979053) B2979053
theorem B4468589 : Blo 1985435 4468589 := bbase (se 3 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 4468589 = 1675721) (by norm_num)
theorem B2979059 : Blo 1985435 2979059 := bstep (se 1 (by rfl) ⟨2234294, by rfl⟩ : syracuseStep 2979059 = 4468589) B4468589
theorem B1986039 : Blo 1985435 1986039 := bstep (se 1 (by rfl) ⟨1489529, by rfl⟩ : syracuseStep 1986039 = 2979059) B2979059
theorem B3770381 : Blo 1985435 3770381 := bbase (se 3 (by rfl) ⟨706946, by rfl⟩ : syracuseStep 3770381 = 1413893) (by norm_num)
theorem B2513587 : Blo 1985435 2513587 := bstep (se 1 (by rfl) ⟨1885190, by rfl⟩ : syracuseStep 2513587 = 3770381) B3770381
theorem B3351449 : Blo 1985435 3351449 := bstep (se 2 (by rfl) ⟨1256793, by rfl⟩ : syracuseStep 3351449 = 2513587) B2513587
theorem B2234299 : Blo 1985435 2234299 := bstep (se 1 (by rfl) ⟨1675724, by rfl⟩ : syracuseStep 2234299 = 3351449) B3351449
theorem B2979065 : Blo 1985435 2979065 := bstep (se 2 (by rfl) ⟨1117149, by rfl⟩ : syracuseStep 2979065 = 2234299) B2234299
theorem B1986043 : Blo 1985435 1986043 := bstep (se 1 (by rfl) ⟨1489532, by rfl⟩ : syracuseStep 1986043 = 2979065) B2979065
theorem B3019717 : Blo 1985435 3019717 := bbase (se 4 (by rfl) ⟨283098, by rfl⟩ : syracuseStep 3019717 = 566197) (by norm_num)
theorem B4026289 : Blo 1985435 4026289 := bstep (se 2 (by rfl) ⟨1509858, by rfl⟩ : syracuseStep 4026289 = 3019717) B3019717
theorem B5368385 : Blo 1985435 5368385 := bstep (se 2 (by rfl) ⟨2013144, by rfl⟩ : syracuseStep 5368385 = 4026289) B4026289
theorem B3578923 : Blo 1985435 3578923 := bstep (se 1 (by rfl) ⟨2684192, by rfl⟩ : syracuseStep 3578923 = 5368385) B5368385
theorem B19087589 : Blo 1985435 19087589 := bstep (se 4 (by rfl) ⟨1789461, by rfl⟩ : syracuseStep 19087589 = 3578923) B3578923
theorem B50900237 : Blo 1985435 50900237 := bstep (se 3 (by rfl) ⟨9543794, by rfl⟩ : syracuseStep 50900237 = 19087589) B19087589
theorem B33933491 : Blo 1985435 33933491 := bstep (se 1 (by rfl) ⟨25450118, by rfl⟩ : syracuseStep 33933491 = 50900237) B50900237
theorem B22622327 : Blo 1985435 22622327 := bstep (se 1 (by rfl) ⟨16966745, by rfl⟩ : syracuseStep 22622327 = 33933491) B33933491
theorem B15081551 : Blo 1985435 15081551 := bstep (se 1 (by rfl) ⟨11311163, by rfl⟩ : syracuseStep 15081551 = 22622327) B22622327
theorem B10054367 : Blo 1985435 10054367 := bstep (se 1 (by rfl) ⟨7540775, by rfl⟩ : syracuseStep 10054367 = 15081551) B15081551
theorem B6702911 : Blo 1985435 6702911 := bstep (se 1 (by rfl) ⟨5027183, by rfl⟩ : syracuseStep 6702911 = 10054367) B10054367
theorem B4468607 : Blo 1985435 4468607 := bstep (se 1 (by rfl) ⟨3351455, by rfl⟩ : syracuseStep 4468607 = 6702911) B6702911
theorem B2979071 : Blo 1985435 2979071 := bstep (se 1 (by rfl) ⟨2234303, by rfl⟩ : syracuseStep 2979071 = 4468607) B4468607
theorem B1986047 : Blo 1985435 1986047 := bstep (se 1 (by rfl) ⟨1489535, by rfl⟩ : syracuseStep 1986047 = 2979071) B2979071
theorem B2979077 : Blo 1985435 2979077 := bbase (se 4 (by rfl) ⟨279288, by rfl⟩ : syracuseStep 2979077 = 558577) (by norm_num)
theorem B1986051 : Blo 1985435 1986051 := bstep (se 1 (by rfl) ⟨1489538, by rfl⟩ : syracuseStep 1986051 = 2979077) B2979077
theorem B3351469 : Blo 1985435 3351469 := bbase (se 3 (by rfl) ⟨628400, by rfl⟩ : syracuseStep 3351469 = 1256801) (by norm_num)
theorem B4468625 : Blo 1985435 4468625 := bstep (se 2 (by rfl) ⟨1675734, by rfl⟩ : syracuseStep 4468625 = 3351469) B3351469
theorem B2979083 : Blo 1985435 2979083 := bstep (se 1 (by rfl) ⟨2234312, by rfl⟩ : syracuseStep 2979083 = 4468625) B4468625
theorem B1986055 : Blo 1985435 1986055 := bstep (se 1 (by rfl) ⟨1489541, by rfl⟩ : syracuseStep 1986055 = 2979083) B2979083
theorem B2234317 : Blo 1985435 2234317 := bbase (se 3 (by rfl) ⟨418934, by rfl⟩ : syracuseStep 2234317 = 837869) (by norm_num)
theorem B2979089 : Blo 1985435 2979089 := bstep (se 2 (by rfl) ⟨1117158, by rfl⟩ : syracuseStep 2979089 = 2234317) B2234317
theorem B1986059 : Blo 1985435 1986059 := bstep (se 1 (by rfl) ⟨1489544, by rfl⟩ : syracuseStep 1986059 = 2979089) B2979089
theorem B6702965 : Blo 1985435 6702965 := bbase (se 5 (by rfl) ⟨314201, by rfl⟩ : syracuseStep 6702965 = 628403) (by norm_num)
theorem B4468643 : Blo 1985435 4468643 := bstep (se 1 (by rfl) ⟨3351482, by rfl⟩ : syracuseStep 4468643 = 6702965) B6702965
theorem B2979095 : Blo 1985435 2979095 := bstep (se 1 (by rfl) ⟨2234321, by rfl⟩ : syracuseStep 2979095 = 4468643) B4468643
theorem B1986063 : Blo 1985435 1986063 := bstep (se 1 (by rfl) ⟨1489547, by rfl⟩ : syracuseStep 1986063 = 2979095) B2979095
theorem B2979101 : Blo 1985435 2979101 := bbase (se 3 (by rfl) ⟨558581, by rfl⟩ : syracuseStep 2979101 = 1117163) (by norm_num)
theorem B1986067 : Blo 1985435 1986067 := bstep (se 1 (by rfl) ⟨1489550, by rfl⟩ : syracuseStep 1986067 = 2979101) B2979101
theorem B4468661 : Blo 1985435 4468661 := bbase (se 5 (by rfl) ⟨209468, by rfl⟩ : syracuseStep 4468661 = 418937) (by norm_num)
theorem B2979107 : Blo 1985435 2979107 := bstep (se 1 (by rfl) ⟨2234330, by rfl⟩ : syracuseStep 2979107 = 4468661) B4468661
theorem B1986071 : Blo 1985435 1986071 := bstep (se 1 (by rfl) ⟨1489553, by rfl⟩ : syracuseStep 1986071 = 2979107) B2979107
theorem B9674149 : Blo 1985435 9674149 := bbase (se 4 (by rfl) ⟨906951, by rfl⟩ : syracuseStep 9674149 = 1813903) (by norm_num)
theorem B12898865 : Blo 1985435 12898865 := bstep (se 2 (by rfl) ⟨4837074, by rfl⟩ : syracuseStep 12898865 = 9674149) B9674149
theorem B8599243 : Blo 1985435 8599243 := bstep (se 1 (by rfl) ⟨6449432, by rfl⟩ : syracuseStep 8599243 = 12898865) B12898865
theorem B11465657 : Blo 1985435 11465657 := bstep (se 2 (by rfl) ⟨4299621, by rfl⟩ : syracuseStep 11465657 = 8599243) B8599243
theorem B7643771 : Blo 1985435 7643771 := bstep (se 1 (by rfl) ⟨5732828, by rfl⟩ : syracuseStep 7643771 = 11465657) B11465657
theorem B5095847 : Blo 1985435 5095847 := bstep (se 1 (by rfl) ⟨3821885, by rfl⟩ : syracuseStep 5095847 = 7643771) B7643771
theorem B3397231 : Blo 1985435 3397231 := bstep (se 1 (by rfl) ⟨2547923, by rfl⟩ : syracuseStep 3397231 = 5095847) B5095847
theorem B18118565 : Blo 1985435 18118565 := bstep (se 4 (by rfl) ⟨1698615, by rfl⟩ : syracuseStep 18118565 = 3397231) B3397231
theorem B12079043 : Blo 1985435 12079043 := bstep (se 1 (by rfl) ⟨9059282, by rfl⟩ : syracuseStep 12079043 = 18118565) B18118565
theorem B8052695 : Blo 1985435 8052695 := bstep (se 1 (by rfl) ⟨6039521, by rfl⟩ : syracuseStep 8052695 = 12079043) B12079043
theorem B5368463 : Blo 1985435 5368463 := bstep (se 1 (by rfl) ⟨4026347, by rfl⟩ : syracuseStep 5368463 = 8052695) B8052695
theorem B3578975 : Blo 1985435 3578975 := bstep (se 1 (by rfl) ⟨2684231, by rfl⟩ : syracuseStep 3578975 = 5368463) B5368463
theorem B2385983 : Blo 1985435 2385983 := bstep (se 1 (by rfl) ⟨1789487, by rfl⟩ : syracuseStep 2385983 = 3578975) B3578975
theorem B6362621 : Blo 1985435 6362621 := bstep (se 3 (by rfl) ⟨1192991, by rfl⟩ : syracuseStep 6362621 = 2385983) B2385983
theorem B4241747 : Blo 1985435 4241747 := bstep (se 1 (by rfl) ⟨3181310, by rfl⟩ : syracuseStep 4241747 = 6362621) B6362621
theorem B11311325 : Blo 1985435 11311325 := bstep (se 3 (by rfl) ⟨2120873, by rfl⟩ : syracuseStep 11311325 = 4241747) B4241747
theorem B7540883 : Blo 1985435 7540883 := bstep (se 1 (by rfl) ⟨5655662, by rfl⟩ : syracuseStep 7540883 = 11311325) B11311325
theorem B5027255 : Blo 1985435 5027255 := bstep (se 1 (by rfl) ⟨3770441, by rfl⟩ : syracuseStep 5027255 = 7540883) B7540883
theorem B3351503 : Blo 1985435 3351503 := bstep (se 1 (by rfl) ⟨2513627, by rfl⟩ : syracuseStep 3351503 = 5027255) B5027255
theorem B2234335 : Blo 1985435 2234335 := bstep (se 1 (by rfl) ⟨1675751, by rfl⟩ : syracuseStep 2234335 = 3351503) B3351503
theorem B2979113 : Blo 1985435 2979113 := bstep (se 2 (by rfl) ⟨1117167, by rfl⟩ : syracuseStep 2979113 = 2234335) B2234335
theorem B1986075 : Blo 1985435 1986075 := bstep (se 1 (by rfl) ⟨1489556, by rfl⟩ : syracuseStep 1986075 = 2979113) B2979113
theorem B8052709 : Blo 1985435 8052709 := bbase (se 4 (by rfl) ⟨754941, by rfl⟩ : syracuseStep 8052709 = 1509883) (by norm_num)
theorem B10736945 : Blo 1985435 10736945 := bstep (se 2 (by rfl) ⟨4026354, by rfl⟩ : syracuseStep 10736945 = 8052709) B8052709
theorem B7157963 : Blo 1985435 7157963 := bstep (se 1 (by rfl) ⟨5368472, by rfl⟩ : syracuseStep 7157963 = 10736945) B10736945
theorem B4771975 : Blo 1985435 4771975 := bstep (se 1 (by rfl) ⟨3578981, by rfl⟩ : syracuseStep 4771975 = 7157963) B7157963
theorem B6362633 : Blo 1985435 6362633 := bstep (se 2 (by rfl) ⟨2385987, by rfl⟩ : syracuseStep 6362633 = 4771975) B4771975
theorem B4241755 : Blo 1985435 4241755 := bstep (se 1 (by rfl) ⟨3181316, by rfl⟩ : syracuseStep 4241755 = 6362633) B6362633
theorem B5655673 : Blo 1985435 5655673 := bstep (se 2 (by rfl) ⟨2120877, by rfl⟩ : syracuseStep 5655673 = 4241755) B4241755
theorem B7540897 : Blo 1985435 7540897 := bstep (se 2 (by rfl) ⟨2827836, by rfl⟩ : syracuseStep 7540897 = 5655673) B5655673
theorem B10054529 : Blo 1985435 10054529 := bstep (se 2 (by rfl) ⟨3770448, by rfl⟩ : syracuseStep 10054529 = 7540897) B7540897
theorem B6703019 : Blo 1985435 6703019 := bstep (se 1 (by rfl) ⟨5027264, by rfl⟩ : syracuseStep 6703019 = 10054529) B10054529
theorem B4468679 : Blo 1985435 4468679 := bstep (se 1 (by rfl) ⟨3351509, by rfl⟩ : syracuseStep 4468679 = 6703019) B6703019
theorem B2979119 : Blo 1985435 2979119 := bstep (se 1 (by rfl) ⟨2234339, by rfl⟩ : syracuseStep 2979119 = 4468679) B4468679
theorem B1986079 : Blo 1985435 1986079 := bstep (se 1 (by rfl) ⟨1489559, by rfl⟩ : syracuseStep 1986079 = 2979119) B2979119
theorem B2979125 : Blo 1985435 2979125 := bbase (se 5 (by rfl) ⟨139646, by rfl⟩ : syracuseStep 2979125 = 279293) (by norm_num)
theorem B1986083 : Blo 1985435 1986083 := bstep (se 1 (by rfl) ⟨1489562, by rfl⟩ : syracuseStep 1986083 = 2979125) B2979125
theorem B5027285 : Blo 1985435 5027285 := bbase (se 7 (by rfl) ⟨58913, by rfl⟩ : syracuseStep 5027285 = 117827) (by norm_num)
theorem B3351523 : Blo 1985435 3351523 := bstep (se 1 (by rfl) ⟨2513642, by rfl⟩ : syracuseStep 3351523 = 5027285) B5027285
theorem B4468697 : Blo 1985435 4468697 := bstep (se 2 (by rfl) ⟨1675761, by rfl⟩ : syracuseStep 4468697 = 3351523) B3351523
theorem B2979131 : Blo 1985435 2979131 := bstep (se 1 (by rfl) ⟨2234348, by rfl⟩ : syracuseStep 2979131 = 4468697) B4468697
theorem B1986087 : Blo 1985435 1986087 := bstep (se 1 (by rfl) ⟨1489565, by rfl⟩ : syracuseStep 1986087 = 2979131) B2979131
theorem B2234353 : Blo 1985435 2234353 := bbase (se 2 (by rfl) ⟨837882, by rfl⟩ : syracuseStep 2234353 = 1675765) (by norm_num)
theorem B2979137 : Blo 1985435 2979137 := bstep (se 2 (by rfl) ⟨1117176, by rfl⟩ : syracuseStep 2979137 = 2234353) B2234353
theorem B1986091 : Blo 1985435 1986091 := bstep (se 1 (by rfl) ⟨1489568, by rfl⟩ : syracuseStep 1986091 = 2979137) B2979137
theorem B18118741 : Blo 1985435 18118741 := bbase (se 8 (by rfl) ⟨106164, by rfl⟩ : syracuseStep 18118741 = 212329) (by norm_num)
theorem B24158321 : Blo 1985435 24158321 := bstep (se 2 (by rfl) ⟨9059370, by rfl⟩ : syracuseStep 24158321 = 18118741) B18118741
theorem B16105547 : Blo 1985435 16105547 := bstep (se 1 (by rfl) ⟨12079160, by rfl⟩ : syracuseStep 16105547 = 24158321) B24158321
theorem B10737031 : Blo 1985435 10737031 := bstep (se 1 (by rfl) ⟨8052773, by rfl⟩ : syracuseStep 10737031 = 16105547) B16105547
theorem B14316041 : Blo 1985435 14316041 := bstep (se 2 (by rfl) ⟨5368515, by rfl⟩ : syracuseStep 14316041 = 10737031) B10737031
theorem B9544027 : Blo 1985435 9544027 := bstep (se 1 (by rfl) ⟨7158020, by rfl⟩ : syracuseStep 9544027 = 14316041) B14316041
theorem B12725369 : Blo 1985435 12725369 := bstep (se 2 (by rfl) ⟨4772013, by rfl⟩ : syracuseStep 12725369 = 9544027) B9544027
theorem B8483579 : Blo 1985435 8483579 := bstep (se 1 (by rfl) ⟨6362684, by rfl⟩ : syracuseStep 8483579 = 12725369) B12725369
theorem B5655719 : Blo 1985435 5655719 := bstep (se 1 (by rfl) ⟨4241789, by rfl⟩ : syracuseStep 5655719 = 8483579) B8483579
theorem B3770479 : Blo 1985435 3770479 := bstep (se 1 (by rfl) ⟨2827859, by rfl⟩ : syracuseStep 3770479 = 5655719) B5655719
theorem B5027305 : Blo 1985435 5027305 := bstep (se 2 (by rfl) ⟨1885239, by rfl⟩ : syracuseStep 5027305 = 3770479) B3770479
theorem B6703073 : Blo 1985435 6703073 := bstep (se 2 (by rfl) ⟨2513652, by rfl⟩ : syracuseStep 6703073 = 5027305) B5027305
theorem B4468715 : Blo 1985435 4468715 := bstep (se 1 (by rfl) ⟨3351536, by rfl⟩ : syracuseStep 4468715 = 6703073) B6703073
theorem B2979143 : Blo 1985435 2979143 := bstep (se 1 (by rfl) ⟨2234357, by rfl⟩ : syracuseStep 2979143 = 4468715) B4468715
theorem B1986095 : Blo 1985435 1986095 := bstep (se 1 (by rfl) ⟨1489571, by rfl⟩ : syracuseStep 1986095 = 2979143) B2979143
theorem B2979149 : Blo 1985435 2979149 := bbase (se 3 (by rfl) ⟨558590, by rfl⟩ : syracuseStep 2979149 = 1117181) (by norm_num)
theorem B1986099 : Blo 1985435 1986099 := bstep (se 1 (by rfl) ⟨1489574, by rfl⟩ : syracuseStep 1986099 = 2979149) B2979149
theorem B4468733 : Blo 1985435 4468733 := bbase (se 3 (by rfl) ⟨837887, by rfl⟩ : syracuseStep 4468733 = 1675775) (by norm_num)
theorem B2979155 : Blo 1985435 2979155 := bstep (se 1 (by rfl) ⟨2234366, by rfl⟩ : syracuseStep 2979155 = 4468733) B4468733
theorem B1986103 : Blo 1985435 1986103 := bstep (se 1 (by rfl) ⟨1489577, by rfl⟩ : syracuseStep 1986103 = 2979155) B2979155
theorem B3351557 : Blo 1985435 3351557 := bbase (se 4 (by rfl) ⟨314208, by rfl⟩ : syracuseStep 3351557 = 628417) (by norm_num)
theorem B2234371 : Blo 1985435 2234371 := bstep (se 1 (by rfl) ⟨1675778, by rfl⟩ : syracuseStep 2234371 = 3351557) B3351557
theorem B2979161 : Blo 1985435 2979161 := bstep (se 2 (by rfl) ⟨1117185, by rfl⟩ : syracuseStep 2979161 = 2234371) B2234371
theorem B1986107 : Blo 1985435 1986107 := bstep (se 1 (by rfl) ⟨1489580, by rfl⟩ : syracuseStep 1986107 = 2979161) B2979161
theorem B15082037 : Blo 1985435 15082037 := bbase (se 5 (by rfl) ⟨706970, by rfl⟩ : syracuseStep 15082037 = 1413941) (by norm_num)
theorem B10054691 : Blo 1985435 10054691 := bstep (se 1 (by rfl) ⟨7541018, by rfl⟩ : syracuseStep 10054691 = 15082037) B15082037
theorem B6703127 : Blo 1985435 6703127 := bstep (se 1 (by rfl) ⟨5027345, by rfl⟩ : syracuseStep 6703127 = 10054691) B10054691
theorem B4468751 : Blo 1985435 4468751 := bstep (se 1 (by rfl) ⟨3351563, by rfl⟩ : syracuseStep 4468751 = 6703127) B6703127
theorem B2979167 : Blo 1985435 2979167 := bstep (se 1 (by rfl) ⟨2234375, by rfl⟩ : syracuseStep 2979167 = 4468751) B4468751
theorem B1986111 : Blo 1985435 1986111 := bstep (se 1 (by rfl) ⟨1489583, by rfl⟩ : syracuseStep 1986111 = 2979167) B2979167
theorem B2979173 : Blo 1985435 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B1986115 : Blo 1985435 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B3770525 : Blo 1985435 3770525 := bbase (se 3 (by rfl) ⟨706973, by rfl⟩ : syracuseStep 3770525 = 1413947) (by norm_num)
theorem B2513683 : Blo 1985435 2513683 := bstep (se 1 (by rfl) ⟨1885262, by rfl⟩ : syracuseStep 2513683 = 3770525) B3770525
theorem B3351577 : Blo 1985435 3351577 := bstep (se 2 (by rfl) ⟨1256841, by rfl⟩ : syracuseStep 3351577 = 2513683) B2513683
theorem B4468769 : Blo 1985435 4468769 := bstep (se 2 (by rfl) ⟨1675788, by rfl⟩ : syracuseStep 4468769 = 3351577) B3351577
theorem B2979179 : Blo 1985435 2979179 := bstep (se 1 (by rfl) ⟨2234384, by rfl⟩ : syracuseStep 2979179 = 4468769) B4468769
theorem B1986119 : Blo 1985435 1986119 := bstep (se 1 (by rfl) ⟨1489589, by rfl⟩ : syracuseStep 1986119 = 2979179) B2979179
theorem B2234389 : Blo 1985435 2234389 := bbase (se 6 (by rfl) ⟨52368, by rfl⟩ : syracuseStep 2234389 = 104737) (by norm_num)
theorem B2979185 : Blo 1985435 2979185 := bstep (se 2 (by rfl) ⟨1117194, by rfl⟩ : syracuseStep 2979185 = 2234389) B2234389
theorem B1986123 : Blo 1985435 1986123 := bstep (se 1 (by rfl) ⟨1489592, by rfl⟩ : syracuseStep 1986123 = 2979185) B2979185
theorem B2513693 : Blo 1985435 2513693 := bbase (se 3 (by rfl) ⟨471317, by rfl⟩ : syracuseStep 2513693 = 942635) (by norm_num)
theorem B6703181 : Blo 1985435 6703181 := bstep (se 3 (by rfl) ⟨1256846, by rfl⟩ : syracuseStep 6703181 = 2513693) B2513693
theorem B4468787 : Blo 1985435 4468787 := bstep (se 1 (by rfl) ⟨3351590, by rfl⟩ : syracuseStep 4468787 = 6703181) B6703181
theorem B2979191 : Blo 1985435 2979191 := bstep (se 1 (by rfl) ⟨2234393, by rfl⟩ : syracuseStep 2979191 = 4468787) B4468787
theorem B1986127 : Blo 1985435 1986127 := bstep (se 1 (by rfl) ⟨1489595, by rfl⟩ : syracuseStep 1986127 = 2979191) B2979191
theorem B2979197 : Blo 1985435 2979197 := bbase (se 3 (by rfl) ⟨558599, by rfl⟩ : syracuseStep 2979197 = 1117199) (by norm_num)
theorem B1986131 : Blo 1985435 1986131 := bstep (se 1 (by rfl) ⟨1489598, by rfl⟩ : syracuseStep 1986131 = 2979197) B2979197
theorem B4468805 : Blo 1985435 4468805 := bbase (se 4 (by rfl) ⟨418950, by rfl⟩ : syracuseStep 4468805 = 837901) (by norm_num)
theorem B2979203 : Blo 1985435 2979203 := bstep (se 1 (by rfl) ⟨2234402, by rfl⟩ : syracuseStep 2979203 = 4468805) B4468805
theorem B1986135 : Blo 1985435 1986135 := bstep (se 1 (by rfl) ⟨1489601, by rfl⟩ : syracuseStep 1986135 = 2979203) B2979203
theorem B5655845 : Blo 1985435 5655845 := bbase (se 4 (by rfl) ⟨530235, by rfl⟩ : syracuseStep 5655845 = 1060471) (by norm_num)
theorem B3770563 : Blo 1985435 3770563 := bstep (se 1 (by rfl) ⟨2827922, by rfl⟩ : syracuseStep 3770563 = 5655845) B5655845
theorem B5027417 : Blo 1985435 5027417 := bstep (se 2 (by rfl) ⟨1885281, by rfl⟩ : syracuseStep 5027417 = 3770563) B3770563
theorem B3351611 : Blo 1985435 3351611 := bstep (se 1 (by rfl) ⟨2513708, by rfl⟩ : syracuseStep 3351611 = 5027417) B5027417
theorem B2234407 : Blo 1985435 2234407 := bstep (se 1 (by rfl) ⟨1675805, by rfl⟩ : syracuseStep 2234407 = 3351611) B3351611
theorem B2979209 : Blo 1985435 2979209 := bstep (se 2 (by rfl) ⟨1117203, by rfl⟩ : syracuseStep 2979209 = 2234407) B2234407
theorem B1986139 : Blo 1985435 1986139 := bstep (se 1 (by rfl) ⟨1489604, by rfl⟩ : syracuseStep 1986139 = 2979209) B2979209
theorem B10054853 : Blo 1985435 10054853 := bbase (se 4 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 10054853 = 1885285) (by norm_num)
theorem B6703235 : Blo 1985435 6703235 := bstep (se 1 (by rfl) ⟨5027426, by rfl⟩ : syracuseStep 6703235 = 10054853) B10054853
theorem B4468823 : Blo 1985435 4468823 := bstep (se 1 (by rfl) ⟨3351617, by rfl⟩ : syracuseStep 4468823 = 6703235) B6703235
theorem B2979215 : Blo 1985435 2979215 := bstep (se 1 (by rfl) ⟨2234411, by rfl⟩ : syracuseStep 2979215 = 4468823) B4468823
theorem B1986143 : Blo 1985435 1986143 := bstep (se 1 (by rfl) ⟨1489607, by rfl⟩ : syracuseStep 1986143 = 2979215) B2979215
theorem B2979221 : Blo 1985435 2979221 := bbase (se 6 (by rfl) ⟨69825, by rfl⟩ : syracuseStep 2979221 = 139651) (by norm_num)
theorem B1986147 : Blo 1985435 1986147 := bstep (se 1 (by rfl) ⟨1489610, by rfl⟩ : syracuseStep 1986147 = 2979221) B2979221
theorem B4241909 : Blo 1985435 4241909 := bbase (se 5 (by rfl) ⟨198839, by rfl⟩ : syracuseStep 4241909 = 397679) (by norm_num)
theorem B11311757 : Blo 1985435 11311757 := bstep (se 3 (by rfl) ⟨2120954, by rfl⟩ : syracuseStep 11311757 = 4241909) B4241909
theorem B7541171 : Blo 1985435 7541171 := bstep (se 1 (by rfl) ⟨5655878, by rfl⟩ : syracuseStep 7541171 = 11311757) B11311757
theorem B5027447 : Blo 1985435 5027447 := bstep (se 1 (by rfl) ⟨3770585, by rfl⟩ : syracuseStep 5027447 = 7541171) B7541171
theorem B3351631 : Blo 1985435 3351631 := bstep (se 1 (by rfl) ⟨2513723, by rfl⟩ : syracuseStep 3351631 = 5027447) B5027447
theorem B4468841 : Blo 1985435 4468841 := bstep (se 2 (by rfl) ⟨1675815, by rfl⟩ : syracuseStep 4468841 = 3351631) B3351631
theorem B2979227 : Blo 1985435 2979227 := bstep (se 1 (by rfl) ⟨2234420, by rfl⟩ : syracuseStep 2979227 = 4468841) B4468841
theorem B1986151 : Blo 1985435 1986151 := bstep (se 1 (by rfl) ⟨1489613, by rfl⟩ : syracuseStep 1986151 = 2979227) B2979227
theorem B2234425 : Blo 1985435 2234425 := bbase (se 2 (by rfl) ⟨837909, by rfl⟩ : syracuseStep 2234425 = 1675819) (by norm_num)
theorem B2979233 : Blo 1985435 2979233 := bstep (se 2 (by rfl) ⟨1117212, by rfl⟩ : syracuseStep 2979233 = 2234425) B2234425
theorem B1986155 : Blo 1985435 1986155 := bstep (se 1 (by rfl) ⟨1489616, by rfl⟩ : syracuseStep 1986155 = 2979233) B2979233
theorem B3181445 : Blo 1985435 3181445 := bbase (se 4 (by rfl) ⟨298260, by rfl⟩ : syracuseStep 3181445 = 596521) (by norm_num)
theorem B2120963 : Blo 1985435 2120963 := bstep (se 1 (by rfl) ⟨1590722, by rfl⟩ : syracuseStep 2120963 = 3181445) B3181445
theorem B5655901 : Blo 1985435 5655901 := bstep (se 3 (by rfl) ⟨1060481, by rfl⟩ : syracuseStep 5655901 = 2120963) B2120963
theorem B7541201 : Blo 1985435 7541201 := bstep (se 2 (by rfl) ⟨2827950, by rfl⟩ : syracuseStep 7541201 = 5655901) B5655901
theorem B5027467 : Blo 1985435 5027467 := bstep (se 1 (by rfl) ⟨3770600, by rfl⟩ : syracuseStep 5027467 = 7541201) B7541201
theorem B6703289 : Blo 1985435 6703289 := bstep (se 2 (by rfl) ⟨2513733, by rfl⟩ : syracuseStep 6703289 = 5027467) B5027467
theorem B4468859 : Blo 1985435 4468859 := bstep (se 1 (by rfl) ⟨3351644, by rfl⟩ : syracuseStep 4468859 = 6703289) B6703289
theorem B2979239 : Blo 1985435 2979239 := bstep (se 1 (by rfl) ⟨2234429, by rfl⟩ : syracuseStep 2979239 = 4468859) B4468859
theorem B1986159 : Blo 1985435 1986159 := bstep (se 1 (by rfl) ⟨1489619, by rfl⟩ : syracuseStep 1986159 = 2979239) B2979239
theorem B2979245 : Blo 1985435 2979245 := bbase (se 3 (by rfl) ⟨558608, by rfl⟩ : syracuseStep 2979245 = 1117217) (by norm_num)
theorem B1986163 : Blo 1985435 1986163 := bstep (se 1 (by rfl) ⟨1489622, by rfl⟩ : syracuseStep 1986163 = 2979245) B2979245
theorem B4468877 : Blo 1985435 4468877 := bbase (se 3 (by rfl) ⟨837914, by rfl⟩ : syracuseStep 4468877 = 1675829) (by norm_num)
theorem B2979251 : Blo 1985435 2979251 := bstep (se 1 (by rfl) ⟨2234438, by rfl⟩ : syracuseStep 2979251 = 4468877) B4468877
theorem B1986167 : Blo 1985435 1986167 := bstep (se 1 (by rfl) ⟨1489625, by rfl⟩ : syracuseStep 1986167 = 2979251) B2979251
theorem B2513749 : Blo 1985435 2513749 := bbase (se 9 (by rfl) ⟨7364, by rfl⟩ : syracuseStep 2513749 = 14729) (by norm_num)
theorem B3351665 : Blo 1985435 3351665 := bstep (se 2 (by rfl) ⟨1256874, by rfl⟩ : syracuseStep 3351665 = 2513749) B2513749
theorem B2234443 : Blo 1985435 2234443 := bstep (se 1 (by rfl) ⟨1675832, by rfl⟩ : syracuseStep 2234443 = 3351665) B3351665
theorem B2979257 : Blo 1985435 2979257 := bstep (se 2 (by rfl) ⟨1117221, by rfl⟩ : syracuseStep 2979257 = 2234443) B2234443
theorem B1986171 : Blo 1985435 1986171 := bstep (se 1 (by rfl) ⟨1489628, by rfl⟩ : syracuseStep 1986171 = 2979257) B2979257
theorem B8716997 : Blo 1985435 8716997 := bbase (se 4 (by rfl) ⟨817218, by rfl⟩ : syracuseStep 8716997 = 1634437) (by norm_num)
theorem B5811331 : Blo 1985435 5811331 := bstep (se 1 (by rfl) ⟨4358498, by rfl⟩ : syracuseStep 5811331 = 8716997) B8716997
theorem B7748441 : Blo 1985435 7748441 := bstep (se 2 (by rfl) ⟨2905665, by rfl⟩ : syracuseStep 7748441 = 5811331) B5811331
theorem B330600149 : Blo 1985435 330600149 := bstep (se 7 (by rfl) ⟨3874220, by rfl⟩ : syracuseStep 330600149 = 7748441) B7748441
theorem B220400099 : Blo 1985435 220400099 := bstep (se 1 (by rfl) ⟨165300074, by rfl⟩ : syracuseStep 220400099 = 330600149) B330600149
theorem B146933399 : Blo 1985435 146933399 := bstep (se 1 (by rfl) ⟨110200049, by rfl⟩ : syracuseStep 146933399 = 220400099) B220400099
theorem B391822397 : Blo 1985435 391822397 := bstep (se 3 (by rfl) ⟨73466699, by rfl⟩ : syracuseStep 391822397 = 146933399) B146933399
theorem B261214931 : Blo 1985435 261214931 := bstep (se 1 (by rfl) ⟨195911198, by rfl⟩ : syracuseStep 261214931 = 391822397) B391822397
theorem B174143287 : Blo 1985435 174143287 := bstep (se 1 (by rfl) ⟨130607465, by rfl⟩ : syracuseStep 174143287 = 261214931) B261214931
theorem B232191049 : Blo 1985435 232191049 := bstep (se 2 (by rfl) ⟨87071643, by rfl⟩ : syracuseStep 232191049 = 174143287) B174143287
theorem B309588065 : Blo 1985435 309588065 := bstep (se 2 (by rfl) ⟨116095524, by rfl⟩ : syracuseStep 309588065 = 232191049) B232191049
theorem B206392043 : Blo 1985435 206392043 := bstep (se 1 (by rfl) ⟨154794032, by rfl⟩ : syracuseStep 206392043 = 309588065) B309588065
theorem B137594695 : Blo 1985435 137594695 := bstep (se 1 (by rfl) ⟨103196021, by rfl⟩ : syracuseStep 137594695 = 206392043) B206392043
theorem B183459593 : Blo 1985435 183459593 := bstep (se 2 (by rfl) ⟨68797347, by rfl⟩ : syracuseStep 183459593 = 137594695) B137594695
theorem B489225581 : Blo 1985435 489225581 := bstep (se 3 (by rfl) ⟨91729796, by rfl⟩ : syracuseStep 489225581 = 183459593) B183459593
theorem B326150387 : Blo 1985435 326150387 := bstep (se 1 (by rfl) ⟨244612790, by rfl⟩ : syracuseStep 326150387 = 489225581) B489225581
theorem B217433591 : Blo 1985435 217433591 := bstep (se 1 (by rfl) ⟨163075193, by rfl⟩ : syracuseStep 217433591 = 326150387) B326150387
theorem B144955727 : Blo 1985435 144955727 := bstep (se 1 (by rfl) ⟨108716795, by rfl⟩ : syracuseStep 144955727 = 217433591) B217433591
theorem B96637151 : Blo 1985435 96637151 := bstep (se 1 (by rfl) ⟨72477863, by rfl⟩ : syracuseStep 96637151 = 144955727) B144955727
theorem B64424767 : Blo 1985435 64424767 := bstep (se 1 (by rfl) ⟨48318575, by rfl⟩ : syracuseStep 64424767 = 96637151) B96637151
theorem B85899689 : Blo 1985435 85899689 := bstep (se 2 (by rfl) ⟨32212383, by rfl⟩ : syracuseStep 85899689 = 64424767) B64424767
theorem B57266459 : Blo 1985435 57266459 := bstep (se 1 (by rfl) ⟨42949844, by rfl⟩ : syracuseStep 57266459 = 85899689) B85899689
theorem B38177639 : Blo 1985435 38177639 := bstep (se 1 (by rfl) ⟨28633229, by rfl⟩ : syracuseStep 38177639 = 57266459) B57266459
theorem B25451759 : Blo 1985435 25451759 := bstep (se 1 (by rfl) ⟨19088819, by rfl⟩ : syracuseStep 25451759 = 38177639) B38177639
theorem B16967839 : Blo 1985435 16967839 := bstep (se 1 (by rfl) ⟨12725879, by rfl⟩ : syracuseStep 16967839 = 25451759) B25451759
theorem B22623785 : Blo 1985435 22623785 := bstep (se 2 (by rfl) ⟨8483919, by rfl⟩ : syracuseStep 22623785 = 16967839) B16967839
theorem B15082523 : Blo 1985435 15082523 := bstep (se 1 (by rfl) ⟨11311892, by rfl⟩ : syracuseStep 15082523 = 22623785) B22623785
theorem B10055015 : Blo 1985435 10055015 := bstep (se 1 (by rfl) ⟨7541261, by rfl⟩ : syracuseStep 10055015 = 15082523) B15082523
theorem B6703343 : Blo 1985435 6703343 := bstep (se 1 (by rfl) ⟨5027507, by rfl⟩ : syracuseStep 6703343 = 10055015) B10055015
theorem B4468895 : Blo 1985435 4468895 := bstep (se 1 (by rfl) ⟨3351671, by rfl⟩ : syracuseStep 4468895 = 6703343) B6703343
theorem B2979263 : Blo 1985435 2979263 := bstep (se 1 (by rfl) ⟨2234447, by rfl⟩ : syracuseStep 2979263 = 4468895) B4468895
theorem B1986175 : Blo 1985435 1986175 := bstep (se 1 (by rfl) ⟨1489631, by rfl⟩ : syracuseStep 1986175 = 2979263) B2979263
theorem B2979269 : Blo 1985435 2979269 := bbase (se 4 (by rfl) ⟨279306, by rfl⟩ : syracuseStep 2979269 = 558613) (by norm_num)
theorem B1986179 : Blo 1985435 1986179 := bstep (se 1 (by rfl) ⟨1489634, by rfl⟩ : syracuseStep 1986179 = 2979269) B2979269
theorem B3351685 : Blo 1985435 3351685 := bbase (se 4 (by rfl) ⟨314220, by rfl⟩ : syracuseStep 3351685 = 628441) (by norm_num)
theorem B4468913 : Blo 1985435 4468913 := bstep (se 2 (by rfl) ⟨1675842, by rfl⟩ : syracuseStep 4468913 = 3351685) B3351685
theorem B2979275 : Blo 1985435 2979275 := bstep (se 1 (by rfl) ⟨2234456, by rfl⟩ : syracuseStep 2979275 = 4468913) B4468913
theorem B1986183 : Blo 1985435 1986183 := bstep (se 1 (by rfl) ⟨1489637, by rfl⟩ : syracuseStep 1986183 = 2979275) B2979275
theorem B2234461 : Blo 1985435 2234461 := bbase (se 3 (by rfl) ⟨418961, by rfl⟩ : syracuseStep 2234461 = 837923) (by norm_num)
theorem B2979281 : Blo 1985435 2979281 := bstep (se 2 (by rfl) ⟨1117230, by rfl⟩ : syracuseStep 2979281 = 2234461) B2234461
theorem B1986187 : Blo 1985435 1986187 := bstep (se 1 (by rfl) ⟨1489640, by rfl⟩ : syracuseStep 1986187 = 2979281) B2979281
theorem B6703397 : Blo 1985435 6703397 := bbase (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) (by norm_num)
theorem B4468931 : Blo 1985435 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B2979287 : Blo 1985435 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B1986191 : Blo 1985435 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B2979293 : Blo 1985435 2979293 := bbase (se 3 (by rfl) ⟨558617, by rfl⟩ : syracuseStep 2979293 = 1117235) (by norm_num)
theorem B1986195 : Blo 1985435 1986195 := bstep (se 1 (by rfl) ⟨1489646, by rfl⟩ : syracuseStep 1986195 = 2979293) B2979293
theorem B4468949 : Blo 1985435 4468949 := bbase (se 7 (by rfl) ⟨52370, by rfl⟩ : syracuseStep 4468949 = 104741) (by norm_num)
theorem B2979299 : Blo 1985435 2979299 := bstep (se 1 (by rfl) ⟨2234474, by rfl⟩ : syracuseStep 2979299 = 4468949) B4468949
theorem B1986199 : Blo 1985435 1986199 := bstep (se 1 (by rfl) ⟨1489649, by rfl⟩ : syracuseStep 1986199 = 2979299) B2979299
theorem B14316821 : Blo 1985435 14316821 := bbase (se 6 (by rfl) ⟨335550, by rfl⟩ : syracuseStep 14316821 = 671101) (by norm_num)
theorem B9544547 : Blo 1985435 9544547 := bstep (se 1 (by rfl) ⟨7158410, by rfl⟩ : syracuseStep 9544547 = 14316821) B14316821
theorem B6363031 : Blo 1985435 6363031 := bstep (se 1 (by rfl) ⟨4772273, by rfl⟩ : syracuseStep 6363031 = 9544547) B9544547
theorem B8484041 : Blo 1985435 8484041 := bstep (se 2 (by rfl) ⟨3181515, by rfl⟩ : syracuseStep 8484041 = 6363031) B6363031
theorem B5656027 : Blo 1985435 5656027 := bstep (se 1 (by rfl) ⟨4242020, by rfl⟩ : syracuseStep 5656027 = 8484041) B8484041
theorem B7541369 : Blo 1985435 7541369 := bstep (se 2 (by rfl) ⟨2828013, by rfl⟩ : syracuseStep 7541369 = 5656027) B5656027
theorem B5027579 : Blo 1985435 5027579 := bstep (se 1 (by rfl) ⟨3770684, by rfl⟩ : syracuseStep 5027579 = 7541369) B7541369
theorem B3351719 : Blo 1985435 3351719 := bstep (se 1 (by rfl) ⟨2513789, by rfl⟩ : syracuseStep 3351719 = 5027579) B5027579
theorem B2234479 : Blo 1985435 2234479 := bstep (se 1 (by rfl) ⟨1675859, by rfl⟩ : syracuseStep 2234479 = 3351719) B3351719
theorem B2979305 : Blo 1985435 2979305 := bstep (se 2 (by rfl) ⟨1117239, by rfl⟩ : syracuseStep 2979305 = 2234479) B2234479
theorem B1986203 : Blo 1985435 1986203 := bstep (se 1 (by rfl) ⟨1489652, by rfl⟩ : syracuseStep 1986203 = 2979305) B2979305
theorem B2386141 : Blo 1985435 2386141 := bbase (se 3 (by rfl) ⟨447401, by rfl⟩ : syracuseStep 2386141 = 894803) (by norm_num)
theorem B12726085 : Blo 1985435 12726085 := bstep (se 4 (by rfl) ⟨1193070, by rfl⟩ : syracuseStep 12726085 = 2386141) B2386141
theorem B16968113 : Blo 1985435 16968113 := bstep (se 2 (by rfl) ⟨6363042, by rfl⟩ : syracuseStep 16968113 = 12726085) B12726085
theorem B11312075 : Blo 1985435 11312075 := bstep (se 1 (by rfl) ⟨8484056, by rfl⟩ : syracuseStep 11312075 = 16968113) B16968113
theorem B7541383 : Blo 1985435 7541383 := bstep (se 1 (by rfl) ⟨5656037, by rfl⟩ : syracuseStep 7541383 = 11312075) B11312075
theorem B10055177 : Blo 1985435 10055177 := bstep (se 2 (by rfl) ⟨3770691, by rfl⟩ : syracuseStep 10055177 = 7541383) B7541383
theorem B6703451 : Blo 1985435 6703451 := bstep (se 1 (by rfl) ⟨5027588, by rfl⟩ : syracuseStep 6703451 = 10055177) B10055177
theorem B4468967 : Blo 1985435 4468967 := bstep (se 1 (by rfl) ⟨3351725, by rfl⟩ : syracuseStep 4468967 = 6703451) B6703451
theorem B2979311 : Blo 1985435 2979311 := bstep (se 1 (by rfl) ⟨2234483, by rfl⟩ : syracuseStep 2979311 = 4468967) B4468967
theorem B1986207 : Blo 1985435 1986207 := bstep (se 1 (by rfl) ⟨1489655, by rfl⟩ : syracuseStep 1986207 = 2979311) B2979311
theorem B2979317 : Blo 1985435 2979317 := bbase (se 5 (by rfl) ⟨139655, by rfl⟩ : syracuseStep 2979317 = 279311) (by norm_num)
theorem B1986211 : Blo 1985435 1986211 := bstep (se 1 (by rfl) ⟨1489658, by rfl⟩ : syracuseStep 1986211 = 2979317) B2979317
theorem B4299925 : Blo 1985435 4299925 := bbase (se 6 (by rfl) ⟨100779, by rfl⟩ : syracuseStep 4299925 = 201559) (by norm_num)
theorem B5733233 : Blo 1985435 5733233 := bstep (se 2 (by rfl) ⟨2149962, by rfl⟩ : syracuseStep 5733233 = 4299925) B4299925
theorem B3822155 : Blo 1985435 3822155 := bstep (se 1 (by rfl) ⟨2866616, by rfl⟩ : syracuseStep 3822155 = 5733233) B5733233
theorem B2548103 : Blo 1985435 2548103 := bstep (se 1 (by rfl) ⟨1911077, by rfl⟩ : syracuseStep 2548103 = 3822155) B3822155
theorem B6794941 : Blo 1985435 6794941 := bstep (se 3 (by rfl) ⟨1274051, by rfl⟩ : syracuseStep 6794941 = 2548103) B2548103
theorem B9059921 : Blo 1985435 9059921 := bstep (se 2 (by rfl) ⟨3397470, by rfl⟩ : syracuseStep 9059921 = 6794941) B6794941
theorem B6039947 : Blo 1985435 6039947 := bstep (se 1 (by rfl) ⟨4529960, by rfl⟩ : syracuseStep 6039947 = 9059921) B9059921
theorem B16106525 : Blo 1985435 16106525 := bstep (se 3 (by rfl) ⟨3019973, by rfl⟩ : syracuseStep 16106525 = 6039947) B6039947
theorem B10737683 : Blo 1985435 10737683 := bstep (se 1 (by rfl) ⟨8053262, by rfl⟩ : syracuseStep 10737683 = 16106525) B16106525
theorem B7158455 : Blo 1985435 7158455 := bstep (se 1 (by rfl) ⟨5368841, by rfl⟩ : syracuseStep 7158455 = 10737683) B10737683
theorem B4772303 : Blo 1985435 4772303 := bstep (se 1 (by rfl) ⟨3579227, by rfl⟩ : syracuseStep 4772303 = 7158455) B7158455
theorem B3181535 : Blo 1985435 3181535 := bstep (se 1 (by rfl) ⟨2386151, by rfl⟩ : syracuseStep 3181535 = 4772303) B4772303
theorem B2121023 : Blo 1985435 2121023 := bstep (se 1 (by rfl) ⟨1590767, by rfl⟩ : syracuseStep 2121023 = 3181535) B3181535
theorem B5656061 : Blo 1985435 5656061 := bstep (se 3 (by rfl) ⟨1060511, by rfl⟩ : syracuseStep 5656061 = 2121023) B2121023
theorem B3770707 : Blo 1985435 3770707 := bstep (se 1 (by rfl) ⟨2828030, by rfl⟩ : syracuseStep 3770707 = 5656061) B5656061
theorem B5027609 : Blo 1985435 5027609 := bstep (se 2 (by rfl) ⟨1885353, by rfl⟩ : syracuseStep 5027609 = 3770707) B3770707
theorem B3351739 : Blo 1985435 3351739 := bstep (se 1 (by rfl) ⟨2513804, by rfl⟩ : syracuseStep 3351739 = 5027609) B5027609
theorem B4468985 : Blo 1985435 4468985 := bstep (se 2 (by rfl) ⟨1675869, by rfl⟩ : syracuseStep 4468985 = 3351739) B3351739
theorem B2979323 : Blo 1985435 2979323 := bstep (se 1 (by rfl) ⟨2234492, by rfl⟩ : syracuseStep 2979323 = 4468985) B4468985
theorem B1986215 : Blo 1985435 1986215 := bstep (se 1 (by rfl) ⟨1489661, by rfl⟩ : syracuseStep 1986215 = 2979323) B2979323
theorem B2234497 : Blo 1985435 2234497 := bbase (se 2 (by rfl) ⟨837936, by rfl⟩ : syracuseStep 2234497 = 1675873) (by norm_num)
theorem B2979329 : Blo 1985435 2979329 := bstep (se 2 (by rfl) ⟨1117248, by rfl⟩ : syracuseStep 2979329 = 2234497) B2234497
theorem B1986219 : Blo 1985435 1986219 := bstep (se 1 (by rfl) ⟨1489664, by rfl⟩ : syracuseStep 1986219 = 2979329) B2979329
theorem B5027629 : Blo 1985435 5027629 := bbase (se 3 (by rfl) ⟨942680, by rfl⟩ : syracuseStep 5027629 = 1885361) (by norm_num)
theorem B6703505 : Blo 1985435 6703505 := bstep (se 2 (by rfl) ⟨2513814, by rfl⟩ : syracuseStep 6703505 = 5027629) B5027629
theorem B4469003 : Blo 1985435 4469003 := bstep (se 1 (by rfl) ⟨3351752, by rfl⟩ : syracuseStep 4469003 = 6703505) B6703505
theorem B2979335 : Blo 1985435 2979335 := bstep (se 1 (by rfl) ⟨2234501, by rfl⟩ : syracuseStep 2979335 = 4469003) B4469003
theorem B1986223 : Blo 1985435 1986223 := bstep (se 1 (by rfl) ⟨1489667, by rfl⟩ : syracuseStep 1986223 = 2979335) B2979335
theorem B2979341 : Blo 1985435 2979341 := bbase (se 3 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 2979341 = 1117253) (by norm_num)
theorem B1986227 : Blo 1985435 1986227 := bstep (se 1 (by rfl) ⟨1489670, by rfl⟩ : syracuseStep 1986227 = 2979341) B2979341
theorem B4469021 : Blo 1985435 4469021 := bbase (se 3 (by rfl) ⟨837941, by rfl⟩ : syracuseStep 4469021 = 1675883) (by norm_num)
theorem B2979347 : Blo 1985435 2979347 := bstep (se 1 (by rfl) ⟨2234510, by rfl⟩ : syracuseStep 2979347 = 4469021) B4469021
theorem B1986231 : Blo 1985435 1986231 := bstep (se 1 (by rfl) ⟨1489673, by rfl⟩ : syracuseStep 1986231 = 2979347) B2979347
theorem B3351773 : Blo 1985435 3351773 := bbase (se 3 (by rfl) ⟨628457, by rfl⟩ : syracuseStep 3351773 = 1256915) (by norm_num)
theorem B2234515 : Blo 1985435 2234515 := bstep (se 1 (by rfl) ⟨1675886, by rfl⟩ : syracuseStep 2234515 = 3351773) B3351773
theorem B2979353 : Blo 1985435 2979353 := bstep (se 2 (by rfl) ⟨1117257, by rfl⟩ : syracuseStep 2979353 = 2234515) B2234515
theorem B1986235 : Blo 1985435 1986235 := bstep (se 1 (by rfl) ⟨1489676, by rfl⟩ : syracuseStep 1986235 = 2979353) B2979353
theorem B5733301 : Blo 1985435 5733301 := bbase (se 5 (by rfl) ⟨268748, by rfl⟩ : syracuseStep 5733301 = 537497) (by norm_num)
theorem B7644401 : Blo 1985435 7644401 := bstep (se 2 (by rfl) ⟨2866650, by rfl⟩ : syracuseStep 7644401 = 5733301) B5733301
theorem B5096267 : Blo 1985435 5096267 := bstep (se 1 (by rfl) ⟨3822200, by rfl⟩ : syracuseStep 5096267 = 7644401) B7644401
theorem B3397511 : Blo 1985435 3397511 := bstep (se 1 (by rfl) ⟨2548133, by rfl⟩ : syracuseStep 3397511 = 5096267) B5096267
theorem B2265007 : Blo 1985435 2265007 := bstep (se 1 (by rfl) ⟨1698755, by rfl⟩ : syracuseStep 2265007 = 3397511) B3397511
theorem B3020009 : Blo 1985435 3020009 := bstep (se 2 (by rfl) ⟨1132503, by rfl⟩ : syracuseStep 3020009 = 2265007) B2265007
theorem B8053357 : Blo 1985435 8053357 := bstep (se 3 (by rfl) ⟨1510004, by rfl⟩ : syracuseStep 8053357 = 3020009) B3020009
theorem B10737809 : Blo 1985435 10737809 := bstep (se 2 (by rfl) ⟨4026678, by rfl⟩ : syracuseStep 10737809 = 8053357) B8053357
theorem B7158539 : Blo 1985435 7158539 := bstep (se 1 (by rfl) ⟨5368904, by rfl⟩ : syracuseStep 7158539 = 10737809) B10737809
theorem B4772359 : Blo 1985435 4772359 := bstep (se 1 (by rfl) ⟨3579269, by rfl⟩ : syracuseStep 4772359 = 7158539) B7158539
theorem B6363145 : Blo 1985435 6363145 := bstep (se 2 (by rfl) ⟨2386179, by rfl⟩ : syracuseStep 6363145 = 4772359) B4772359
theorem B8484193 : Blo 1985435 8484193 := bstep (se 2 (by rfl) ⟨3181572, by rfl⟩ : syracuseStep 8484193 = 6363145) B6363145
theorem B11312257 : Blo 1985435 11312257 := bstep (se 2 (by rfl) ⟨4242096, by rfl⟩ : syracuseStep 11312257 = 8484193) B8484193
theorem B15083009 : Blo 1985435 15083009 := bstep (se 2 (by rfl) ⟨5656128, by rfl⟩ : syracuseStep 15083009 = 11312257) B11312257
theorem B10055339 : Blo 1985435 10055339 := bstep (se 1 (by rfl) ⟨7541504, by rfl⟩ : syracuseStep 10055339 = 15083009) B15083009
theorem B6703559 : Blo 1985435 6703559 := bstep (se 1 (by rfl) ⟨5027669, by rfl⟩ : syracuseStep 6703559 = 10055339) B10055339
theorem B4469039 : Blo 1985435 4469039 := bstep (se 1 (by rfl) ⟨3351779, by rfl⟩ : syracuseStep 4469039 = 6703559) B6703559
theorem B2979359 : Blo 1985435 2979359 := bstep (se 1 (by rfl) ⟨2234519, by rfl⟩ : syracuseStep 2979359 = 4469039) B4469039
theorem B1986239 : Blo 1985435 1986239 := bstep (se 1 (by rfl) ⟨1489679, by rfl⟩ : syracuseStep 1986239 = 2979359) B2979359
theorem B2979365 : Blo 1985435 2979365 := bbase (se 4 (by rfl) ⟨279315, by rfl⟩ : syracuseStep 2979365 = 558631) (by norm_num)
theorem B1986243 : Blo 1985435 1986243 := bstep (se 1 (by rfl) ⟨1489682, by rfl⟩ : syracuseStep 1986243 = 2979365) B2979365
theorem B2513845 : Blo 1985435 2513845 := bbase (se 5 (by rfl) ⟨117836, by rfl⟩ : syracuseStep 2513845 = 235673) (by norm_num)
theorem B3351793 : Blo 1985435 3351793 := bstep (se 2 (by rfl) ⟨1256922, by rfl⟩ : syracuseStep 3351793 = 2513845) B2513845
theorem B4469057 : Blo 1985435 4469057 := bstep (se 2 (by rfl) ⟨1675896, by rfl⟩ : syracuseStep 4469057 = 3351793) B3351793
theorem B2979371 : Blo 1985435 2979371 := bstep (se 1 (by rfl) ⟨2234528, by rfl⟩ : syracuseStep 2979371 = 4469057) B4469057
theorem B1986247 : Blo 1985435 1986247 := bstep (se 1 (by rfl) ⟨1489685, by rfl⟩ : syracuseStep 1986247 = 2979371) B2979371
theorem B2234533 : Blo 1985435 2234533 := bbase (se 4 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 2234533 = 418975) (by norm_num)
theorem B2979377 : Blo 1985435 2979377 := bstep (se 2 (by rfl) ⟨1117266, by rfl⟩ : syracuseStep 2979377 = 2234533) B2234533
theorem B1986251 : Blo 1985435 1986251 := bstep (se 1 (by rfl) ⟨1489688, by rfl⟩ : syracuseStep 1986251 = 2979377) B2979377
theorem B9060101 : Blo 1985435 9060101 := bbase (se 4 (by rfl) ⟨849384, by rfl⟩ : syracuseStep 9060101 = 1698769) (by norm_num)
theorem B6040067 : Blo 1985435 6040067 := bstep (se 1 (by rfl) ⟨4530050, by rfl⟩ : syracuseStep 6040067 = 9060101) B9060101
theorem B16106845 : Blo 1985435 16106845 := bstep (se 3 (by rfl) ⟨3020033, by rfl⟩ : syracuseStep 16106845 = 6040067) B6040067
theorem B21475793 : Blo 1985435 21475793 := bstep (se 2 (by rfl) ⟨8053422, by rfl⟩ : syracuseStep 21475793 = 16106845) B16106845
theorem B14317195 : Blo 1985435 14317195 := bstep (se 1 (by rfl) ⟨10737896, by rfl⟩ : syracuseStep 14317195 = 21475793) B21475793
theorem B19089593 : Blo 1985435 19089593 := bstep (se 2 (by rfl) ⟨7158597, by rfl⟩ : syracuseStep 19089593 = 14317195) B14317195
theorem B12726395 : Blo 1985435 12726395 := bstep (se 1 (by rfl) ⟨9544796, by rfl⟩ : syracuseStep 12726395 = 19089593) B19089593
theorem B8484263 : Blo 1985435 8484263 := bstep (se 1 (by rfl) ⟨6363197, by rfl⟩ : syracuseStep 8484263 = 12726395) B12726395
theorem B5656175 : Blo 1985435 5656175 := bstep (se 1 (by rfl) ⟨4242131, by rfl⟩ : syracuseStep 5656175 = 8484263) B8484263
theorem B3770783 : Blo 1985435 3770783 := bstep (se 1 (by rfl) ⟨2828087, by rfl⟩ : syracuseStep 3770783 = 5656175) B5656175
theorem B2513855 : Blo 1985435 2513855 := bstep (se 1 (by rfl) ⟨1885391, by rfl⟩ : syracuseStep 2513855 = 3770783) B3770783
theorem B6703613 : Blo 1985435 6703613 := bstep (se 3 (by rfl) ⟨1256927, by rfl⟩ : syracuseStep 6703613 = 2513855) B2513855
theorem B4469075 : Blo 1985435 4469075 := bstep (se 1 (by rfl) ⟨3351806, by rfl⟩ : syracuseStep 4469075 = 6703613) B6703613
theorem B2979383 : Blo 1985435 2979383 := bstep (se 1 (by rfl) ⟨2234537, by rfl⟩ : syracuseStep 2979383 = 4469075) B4469075
theorem B1986255 : Blo 1985435 1986255 := bstep (se 1 (by rfl) ⟨1489691, by rfl⟩ : syracuseStep 1986255 = 2979383) B2979383
theorem B2979389 : Blo 1985435 2979389 := bbase (se 3 (by rfl) ⟨558635, by rfl⟩ : syracuseStep 2979389 = 1117271) (by norm_num)
theorem B1986259 : Blo 1985435 1986259 := bstep (se 1 (by rfl) ⟨1489694, by rfl⟩ : syracuseStep 1986259 = 2979389) B2979389
theorem B4469093 : Blo 1985435 4469093 := bbase (se 4 (by rfl) ⟨418977, by rfl⟩ : syracuseStep 4469093 = 837955) (by norm_num)
theorem B2979395 : Blo 1985435 2979395 := bstep (se 1 (by rfl) ⟨2234546, by rfl⟩ : syracuseStep 2979395 = 4469093) B4469093
theorem B1986263 : Blo 1985435 1986263 := bstep (se 1 (by rfl) ⟨1489697, by rfl⟩ : syracuseStep 1986263 = 2979395) B2979395
theorem B5027741 : Blo 1985435 5027741 := bbase (se 3 (by rfl) ⟨942701, by rfl⟩ : syracuseStep 5027741 = 1885403) (by norm_num)
theorem B3351827 : Blo 1985435 3351827 := bstep (se 1 (by rfl) ⟨2513870, by rfl⟩ : syracuseStep 3351827 = 5027741) B5027741
theorem B2234551 : Blo 1985435 2234551 := bstep (se 1 (by rfl) ⟨1675913, by rfl⟩ : syracuseStep 2234551 = 3351827) B3351827
theorem B2979401 : Blo 1985435 2979401 := bstep (se 2 (by rfl) ⟨1117275, by rfl⟩ : syracuseStep 2979401 = 2234551) B2234551
theorem B1986267 : Blo 1985435 1986267 := bstep (se 1 (by rfl) ⟨1489700, by rfl⟩ : syracuseStep 1986267 = 2979401) B2979401
theorem B3770813 : Blo 1985435 3770813 := bbase (se 3 (by rfl) ⟨707027, by rfl⟩ : syracuseStep 3770813 = 1414055) (by norm_num)
theorem B10055501 : Blo 1985435 10055501 := bstep (se 3 (by rfl) ⟨1885406, by rfl⟩ : syracuseStep 10055501 = 3770813) B3770813
theorem B6703667 : Blo 1985435 6703667 := bstep (se 1 (by rfl) ⟨5027750, by rfl⟩ : syracuseStep 6703667 = 10055501) B10055501
theorem B4469111 : Blo 1985435 4469111 := bstep (se 1 (by rfl) ⟨3351833, by rfl⟩ : syracuseStep 4469111 = 6703667) B6703667
theorem B2979407 : Blo 1985435 2979407 := bstep (se 1 (by rfl) ⟨2234555, by rfl⟩ : syracuseStep 2979407 = 4469111) B4469111
theorem B1986271 : Blo 1985435 1986271 := bstep (se 1 (by rfl) ⟨1489703, by rfl⟩ : syracuseStep 1986271 = 2979407) B2979407
theorem B2979413 : Blo 1985435 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B1986275 : Blo 1985435 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B3181637 : Blo 1985435 3181637 := bbase (se 4 (by rfl) ⟨298278, by rfl⟩ : syracuseStep 3181637 = 596557) (by norm_num)
theorem B8484365 : Blo 1985435 8484365 := bstep (se 3 (by rfl) ⟨1590818, by rfl⟩ : syracuseStep 8484365 = 3181637) B3181637
theorem B5656243 : Blo 1985435 5656243 := bstep (se 1 (by rfl) ⟨4242182, by rfl⟩ : syracuseStep 5656243 = 8484365) B8484365
theorem B7541657 : Blo 1985435 7541657 := bstep (se 2 (by rfl) ⟨2828121, by rfl⟩ : syracuseStep 7541657 = 5656243) B5656243
theorem B5027771 : Blo 1985435 5027771 := bstep (se 1 (by rfl) ⟨3770828, by rfl⟩ : syracuseStep 5027771 = 7541657) B7541657
theorem B3351847 : Blo 1985435 3351847 := bstep (se 1 (by rfl) ⟨2513885, by rfl⟩ : syracuseStep 3351847 = 5027771) B5027771
theorem B4469129 : Blo 1985435 4469129 := bstep (se 2 (by rfl) ⟨1675923, by rfl⟩ : syracuseStep 4469129 = 3351847) B3351847
theorem B2979419 : Blo 1985435 2979419 := bstep (se 1 (by rfl) ⟨2234564, by rfl⟩ : syracuseStep 2979419 = 4469129) B4469129
theorem B1986279 : Blo 1985435 1986279 := bstep (se 1 (by rfl) ⟨1489709, by rfl⟩ : syracuseStep 1986279 = 2979419) B2979419
theorem B2234569 : Blo 1985435 2234569 := bbase (se 2 (by rfl) ⟨837963, by rfl⟩ : syracuseStep 2234569 = 1675927) (by norm_num)
theorem B2979425 : Blo 1985435 2979425 := bstep (se 2 (by rfl) ⟨1117284, by rfl⟩ : syracuseStep 2979425 = 2234569) B2234569
theorem B1986283 : Blo 1985435 1986283 := bstep (se 1 (by rfl) ⟨1489712, by rfl⟩ : syracuseStep 1986283 = 2979425) B2979425
theorem B9544949 : Blo 1985435 9544949 := bbase (se 5 (by rfl) ⟨447419, by rfl⟩ : syracuseStep 9544949 = 894839) (by norm_num)
theorem B6363299 : Blo 1985435 6363299 := bstep (se 1 (by rfl) ⟨4772474, by rfl⟩ : syracuseStep 6363299 = 9544949) B9544949
theorem B16968797 : Blo 1985435 16968797 := bstep (se 3 (by rfl) ⟨3181649, by rfl⟩ : syracuseStep 16968797 = 6363299) B6363299
theorem B11312531 : Blo 1985435 11312531 := bstep (se 1 (by rfl) ⟨8484398, by rfl⟩ : syracuseStep 11312531 = 16968797) B16968797
theorem B7541687 : Blo 1985435 7541687 := bstep (se 1 (by rfl) ⟨5656265, by rfl⟩ : syracuseStep 7541687 = 11312531) B11312531
theorem B5027791 : Blo 1985435 5027791 := bstep (se 1 (by rfl) ⟨3770843, by rfl⟩ : syracuseStep 5027791 = 7541687) B7541687
theorem B6703721 : Blo 1985435 6703721 := bstep (se 2 (by rfl) ⟨2513895, by rfl⟩ : syracuseStep 6703721 = 5027791) B5027791
theorem B4469147 : Blo 1985435 4469147 := bstep (se 1 (by rfl) ⟨3351860, by rfl⟩ : syracuseStep 4469147 = 6703721) B6703721
theorem B2979431 : Blo 1985435 2979431 := bstep (se 1 (by rfl) ⟨2234573, by rfl⟩ : syracuseStep 2979431 = 4469147) B4469147
theorem B1986287 : Blo 1985435 1986287 := bstep (se 1 (by rfl) ⟨1489715, by rfl⟩ : syracuseStep 1986287 = 2979431) B2979431
theorem B2979437 : Blo 1985435 2979437 := bbase (se 3 (by rfl) ⟨558644, by rfl⟩ : syracuseStep 2979437 = 1117289) (by norm_num)
theorem B1986291 : Blo 1985435 1986291 := bstep (se 1 (by rfl) ⟨1489718, by rfl⟩ : syracuseStep 1986291 = 2979437) B2979437
theorem B4469165 : Blo 1985435 4469165 := bbase (se 3 (by rfl) ⟨837968, by rfl⟩ : syracuseStep 4469165 = 1675937) (by norm_num)
theorem B2979443 : Blo 1985435 2979443 := bstep (se 1 (by rfl) ⟨2234582, by rfl⟩ : syracuseStep 2979443 = 4469165) B4469165
theorem B1986295 : Blo 1985435 1986295 := bstep (se 1 (by rfl) ⟨1489721, by rfl⟩ : syracuseStep 1986295 = 2979443) B2979443
theorem B2121113 : Blo 1985435 2121113 := bbase (se 2 (by rfl) ⟨795417, by rfl⟩ : syracuseStep 2121113 = 1590835) (by norm_num)
theorem B5656301 : Blo 1985435 5656301 := bstep (se 3 (by rfl) ⟨1060556, by rfl⟩ : syracuseStep 5656301 = 2121113) B2121113
theorem B3770867 : Blo 1985435 3770867 := bstep (se 1 (by rfl) ⟨2828150, by rfl⟩ : syracuseStep 3770867 = 5656301) B5656301
theorem B2513911 : Blo 1985435 2513911 := bstep (se 1 (by rfl) ⟨1885433, by rfl⟩ : syracuseStep 2513911 = 3770867) B3770867
theorem B3351881 : Blo 1985435 3351881 := bstep (se 2 (by rfl) ⟨1256955, by rfl⟩ : syracuseStep 3351881 = 2513911) B2513911
theorem B2234587 : Blo 1985435 2234587 := bstep (se 1 (by rfl) ⟨1675940, by rfl⟩ : syracuseStep 2234587 = 3351881) B3351881
theorem B2979449 : Blo 1985435 2979449 := bstep (se 2 (by rfl) ⟨1117293, by rfl⟩ : syracuseStep 2979449 = 2234587) B2234587
theorem B1986299 : Blo 1985435 1986299 := bstep (se 1 (by rfl) ⟨1489724, by rfl⟩ : syracuseStep 1986299 = 2979449) B2979449
theorem B11466965 : Blo 1985435 11466965 := bbase (se 7 (by rfl) ⟨134378, by rfl⟩ : syracuseStep 11466965 = 268757) (by norm_num)
theorem B30578573 : Blo 1985435 30578573 := bstep (se 3 (by rfl) ⟨5733482, by rfl⟩ : syracuseStep 30578573 = 11466965) B11466965
theorem B20385715 : Blo 1985435 20385715 := bstep (se 1 (by rfl) ⟨15289286, by rfl⟩ : syracuseStep 20385715 = 30578573) B30578573
theorem B27180953 : Blo 1985435 27180953 := bstep (se 2 (by rfl) ⟨10192857, by rfl⟩ : syracuseStep 27180953 = 20385715) B20385715
theorem B18120635 : Blo 1985435 18120635 := bstep (se 1 (by rfl) ⟨13590476, by rfl⟩ : syracuseStep 18120635 = 27180953) B27180953
theorem B12080423 : Blo 1985435 12080423 := bstep (se 1 (by rfl) ⟨9060317, by rfl⟩ : syracuseStep 12080423 = 18120635) B18120635
theorem B8053615 : Blo 1985435 8053615 := bstep (se 1 (by rfl) ⟨6040211, by rfl⟩ : syracuseStep 8053615 = 12080423) B12080423
theorem B10738153 : Blo 1985435 10738153 := bstep (se 2 (by rfl) ⟨4026807, by rfl⟩ : syracuseStep 10738153 = 8053615) B8053615
theorem B57270149 : Blo 1985435 57270149 := bstep (se 4 (by rfl) ⟨5369076, by rfl⟩ : syracuseStep 57270149 = 10738153) B10738153
theorem B38180099 : Blo 1985435 38180099 := bstep (se 1 (by rfl) ⟨28635074, by rfl⟩ : syracuseStep 38180099 = 57270149) B57270149
theorem B25453399 : Blo 1985435 25453399 := bstep (se 1 (by rfl) ⟨19090049, by rfl⟩ : syracuseStep 25453399 = 38180099) B38180099
theorem B33937865 : Blo 1985435 33937865 := bstep (se 2 (by rfl) ⟨12726699, by rfl⟩ : syracuseStep 33937865 = 25453399) B25453399
theorem B22625243 : Blo 1985435 22625243 := bstep (se 1 (by rfl) ⟨16968932, by rfl⟩ : syracuseStep 22625243 = 33937865) B33937865
theorem B15083495 : Blo 1985435 15083495 := bstep (se 1 (by rfl) ⟨11312621, by rfl⟩ : syracuseStep 15083495 = 22625243) B22625243
theorem B10055663 : Blo 1985435 10055663 := bstep (se 1 (by rfl) ⟨7541747, by rfl⟩ : syracuseStep 10055663 = 15083495) B15083495
theorem B6703775 : Blo 1985435 6703775 := bstep (se 1 (by rfl) ⟨5027831, by rfl⟩ : syracuseStep 6703775 = 10055663) B10055663
theorem B4469183 : Blo 1985435 4469183 := bstep (se 1 (by rfl) ⟨3351887, by rfl⟩ : syracuseStep 4469183 = 6703775) B6703775
theorem B2979455 : Blo 1985435 2979455 := bstep (se 1 (by rfl) ⟨2234591, by rfl⟩ : syracuseStep 2979455 = 4469183) B4469183
theorem B1986303 : Blo 1985435 1986303 := bstep (se 1 (by rfl) ⟨1489727, by rfl⟩ : syracuseStep 1986303 = 2979455) B2979455
theorem B2979461 : Blo 1985435 2979461 := bbase (se 4 (by rfl) ⟨279324, by rfl⟩ : syracuseStep 2979461 = 558649) (by norm_num)
theorem B1986307 : Blo 1985435 1986307 := bstep (se 1 (by rfl) ⟨1489730, by rfl⟩ : syracuseStep 1986307 = 2979461) B2979461
theorem B3351901 : Blo 1985435 3351901 := bbase (se 3 (by rfl) ⟨628481, by rfl⟩ : syracuseStep 3351901 = 1256963) (by norm_num)
theorem B4469201 : Blo 1985435 4469201 := bstep (se 2 (by rfl) ⟨1675950, by rfl⟩ : syracuseStep 4469201 = 3351901) B3351901
theorem B2979467 : Blo 1985435 2979467 := bstep (se 1 (by rfl) ⟨2234600, by rfl⟩ : syracuseStep 2979467 = 4469201) B4469201
theorem B1986311 : Blo 1985435 1986311 := bstep (se 1 (by rfl) ⟨1489733, by rfl⟩ : syracuseStep 1986311 = 2979467) B2979467
theorem B2234605 : Blo 1985435 2234605 := bbase (se 3 (by rfl) ⟨418988, by rfl⟩ : syracuseStep 2234605 = 837977) (by norm_num)
theorem B2979473 : Blo 1985435 2979473 := bstep (se 2 (by rfl) ⟨1117302, by rfl⟩ : syracuseStep 2979473 = 2234605) B2234605
theorem B1986315 : Blo 1985435 1986315 := bstep (se 1 (by rfl) ⟨1489736, by rfl⟩ : syracuseStep 1986315 = 2979473) B2979473
theorem B6703829 : Blo 1985435 6703829 := bbase (se 7 (by rfl) ⟨78560, by rfl⟩ : syracuseStep 6703829 = 157121) (by norm_num)
theorem B4469219 : Blo 1985435 4469219 := bstep (se 1 (by rfl) ⟨3351914, by rfl⟩ : syracuseStep 4469219 = 6703829) B6703829
theorem B2979479 : Blo 1985435 2979479 := bstep (se 1 (by rfl) ⟨2234609, by rfl⟩ : syracuseStep 2979479 = 4469219) B4469219
theorem B1986319 : Blo 1985435 1986319 := bstep (se 1 (by rfl) ⟨1489739, by rfl⟩ : syracuseStep 1986319 = 2979479) B2979479
theorem B2979485 : Blo 1985435 2979485 := bbase (se 3 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 2979485 = 1117307) (by norm_num)
theorem B1986323 : Blo 1985435 1986323 := bstep (se 1 (by rfl) ⟨1489742, by rfl⟩ : syracuseStep 1986323 = 2979485) B2979485
theorem B4469237 : Blo 1985435 4469237 := bbase (se 5 (by rfl) ⟨209495, by rfl⟩ : syracuseStep 4469237 = 418991) (by norm_num)
theorem B2979491 : Blo 1985435 2979491 := bstep (se 1 (by rfl) ⟨2234618, by rfl⟩ : syracuseStep 2979491 = 4469237) B4469237
theorem B1986327 : Blo 1985435 1986327 := bstep (se 1 (by rfl) ⟨1489745, by rfl⟩ : syracuseStep 1986327 = 2979491) B2979491
theorem B3020149 : Blo 1985435 3020149 := bbase (se 5 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 3020149 = 283139) (by norm_num)
theorem B16107461 : Blo 1985435 16107461 := bstep (se 4 (by rfl) ⟨1510074, by rfl⟩ : syracuseStep 16107461 = 3020149) B3020149
theorem B10738307 : Blo 1985435 10738307 := bstep (se 1 (by rfl) ⟨8053730, by rfl⟩ : syracuseStep 10738307 = 16107461) B16107461
theorem B7158871 : Blo 1985435 7158871 := bstep (se 1 (by rfl) ⟨5369153, by rfl⟩ : syracuseStep 7158871 = 10738307) B10738307
theorem B38180645 : Blo 1985435 38180645 := bstep (se 4 (by rfl) ⟨3579435, by rfl⟩ : syracuseStep 38180645 = 7158871) B7158871
theorem B25453763 : Blo 1985435 25453763 := bstep (se 1 (by rfl) ⟨19090322, by rfl⟩ : syracuseStep 25453763 = 38180645) B38180645
theorem B16969175 : Blo 1985435 16969175 := bstep (se 1 (by rfl) ⟨12726881, by rfl⟩ : syracuseStep 16969175 = 25453763) B25453763
theorem B11312783 : Blo 1985435 11312783 := bstep (se 1 (by rfl) ⟨8484587, by rfl⟩ : syracuseStep 11312783 = 16969175) B16969175
theorem B7541855 : Blo 1985435 7541855 := bstep (se 1 (by rfl) ⟨5656391, by rfl⟩ : syracuseStep 7541855 = 11312783) B11312783
theorem B5027903 : Blo 1985435 5027903 := bstep (se 1 (by rfl) ⟨3770927, by rfl⟩ : syracuseStep 5027903 = 7541855) B7541855
theorem B3351935 : Blo 1985435 3351935 := bstep (se 1 (by rfl) ⟨2513951, by rfl⟩ : syracuseStep 3351935 = 5027903) B5027903
theorem B2234623 : Blo 1985435 2234623 := bstep (se 1 (by rfl) ⟨1675967, by rfl⟩ : syracuseStep 2234623 = 3351935) B3351935
theorem B2979497 : Blo 1985435 2979497 := bstep (se 2 (by rfl) ⟨1117311, by rfl⟩ : syracuseStep 2979497 = 2234623) B2234623
theorem B1986331 : Blo 1985435 1986331 := bstep (se 1 (by rfl) ⟨1489748, by rfl⟩ : syracuseStep 1986331 = 2979497) B2979497
theorem B2418853 : Blo 1985435 2418853 := bbase (se 4 (by rfl) ⟨226767, by rfl⟩ : syracuseStep 2418853 = 453535) (by norm_num)
theorem B51602197 : Blo 1985435 51602197 := bstep (se 6 (by rfl) ⟨1209426, by rfl⟩ : syracuseStep 51602197 = 2418853) B2418853
theorem B68802929 : Blo 1985435 68802929 := bstep (se 2 (by rfl) ⟨25801098, by rfl⟩ : syracuseStep 68802929 = 51602197) B51602197
theorem B45868619 : Blo 1985435 45868619 := bstep (se 1 (by rfl) ⟨34401464, by rfl⟩ : syracuseStep 45868619 = 68802929) B68802929
theorem B30579079 : Blo 1985435 30579079 := bstep (se 1 (by rfl) ⟨22934309, by rfl⟩ : syracuseStep 30579079 = 45868619) B45868619
theorem B40772105 : Blo 1985435 40772105 := bstep (se 2 (by rfl) ⟨15289539, by rfl⟩ : syracuseStep 40772105 = 30579079) B30579079
theorem B27181403 : Blo 1985435 27181403 := bstep (se 1 (by rfl) ⟨20386052, by rfl⟩ : syracuseStep 27181403 = 40772105) B40772105
theorem B18120935 : Blo 1985435 18120935 := bstep (se 1 (by rfl) ⟨13590701, by rfl⟩ : syracuseStep 18120935 = 27181403) B27181403
theorem B12080623 : Blo 1985435 12080623 := bstep (se 1 (by rfl) ⟨9060467, by rfl⟩ : syracuseStep 12080623 = 18120935) B18120935
theorem B16107497 : Blo 1985435 16107497 := bstep (se 2 (by rfl) ⟨6040311, by rfl⟩ : syracuseStep 16107497 = 12080623) B12080623
theorem B10738331 : Blo 1985435 10738331 := bstep (se 1 (by rfl) ⟨8053748, by rfl⟩ : syracuseStep 10738331 = 16107497) B16107497
theorem B7158887 : Blo 1985435 7158887 := bstep (se 1 (by rfl) ⟨5369165, by rfl⟩ : syracuseStep 7158887 = 10738331) B10738331
theorem B4772591 : Blo 1985435 4772591 := bstep (se 1 (by rfl) ⟨3579443, by rfl⟩ : syracuseStep 4772591 = 7158887) B7158887
theorem B3181727 : Blo 1985435 3181727 := bstep (se 1 (by rfl) ⟨2386295, by rfl⟩ : syracuseStep 3181727 = 4772591) B4772591
theorem B2121151 : Blo 1985435 2121151 := bstep (se 1 (by rfl) ⟨1590863, by rfl⟩ : syracuseStep 2121151 = 3181727) B3181727
theorem B2828201 : Blo 1985435 2828201 := bstep (se 2 (by rfl) ⟨1060575, by rfl⟩ : syracuseStep 2828201 = 2121151) B2121151
theorem B7541869 : Blo 1985435 7541869 := bstep (se 3 (by rfl) ⟨1414100, by rfl⟩ : syracuseStep 7541869 = 2828201) B2828201
theorem B10055825 : Blo 1985435 10055825 := bstep (se 2 (by rfl) ⟨3770934, by rfl⟩ : syracuseStep 10055825 = 7541869) B7541869
theorem B6703883 : Blo 1985435 6703883 := bstep (se 1 (by rfl) ⟨5027912, by rfl⟩ : syracuseStep 6703883 = 10055825) B10055825
theorem B4469255 : Blo 1985435 4469255 := bstep (se 1 (by rfl) ⟨3351941, by rfl⟩ : syracuseStep 4469255 = 6703883) B6703883
theorem B2979503 : Blo 1985435 2979503 := bstep (se 1 (by rfl) ⟨2234627, by rfl⟩ : syracuseStep 2979503 = 4469255) B4469255
theorem B1986335 : Blo 1985435 1986335 := bstep (se 1 (by rfl) ⟨1489751, by rfl⟩ : syracuseStep 1986335 = 2979503) B2979503
theorem B2979509 : Blo 1985435 2979509 := bbase (se 5 (by rfl) ⟨139664, by rfl⟩ : syracuseStep 2979509 = 279329) (by norm_num)
theorem B1986339 : Blo 1985435 1986339 := bstep (se 1 (by rfl) ⟨1489754, by rfl⟩ : syracuseStep 1986339 = 2979509) B2979509
theorem B5027933 : Blo 1985435 5027933 := bbase (se 3 (by rfl) ⟨942737, by rfl⟩ : syracuseStep 5027933 = 1885475) (by norm_num)
theorem B3351955 : Blo 1985435 3351955 := bstep (se 1 (by rfl) ⟨2513966, by rfl⟩ : syracuseStep 3351955 = 5027933) B5027933
theorem B4469273 : Blo 1985435 4469273 := bstep (se 2 (by rfl) ⟨1675977, by rfl⟩ : syracuseStep 4469273 = 3351955) B3351955
theorem B2979515 : Blo 1985435 2979515 := bstep (se 1 (by rfl) ⟨2234636, by rfl⟩ : syracuseStep 2979515 = 4469273) B4469273
theorem B1986343 : Blo 1985435 1986343 := bstep (se 1 (by rfl) ⟨1489757, by rfl⟩ : syracuseStep 1986343 = 2979515) B2979515
theorem B2234641 : Blo 1985435 2234641 := bbase (se 2 (by rfl) ⟨837990, by rfl⟩ : syracuseStep 2234641 = 1675981) (by norm_num)
theorem B2979521 : Blo 1985435 2979521 := bstep (se 2 (by rfl) ⟨1117320, by rfl⟩ : syracuseStep 2979521 = 2234641) B2234641
theorem B1986347 : Blo 1985435 1986347 := bstep (se 1 (by rfl) ⟨1489760, by rfl⟩ : syracuseStep 1986347 = 2979521) B2979521
theorem B3770965 : Blo 1985435 3770965 := bbase (se 8 (by rfl) ⟨22095, by rfl⟩ : syracuseStep 3770965 = 44191) (by norm_num)
theorem B5027953 : Blo 1985435 5027953 := bstep (se 2 (by rfl) ⟨1885482, by rfl⟩ : syracuseStep 5027953 = 3770965) B3770965
theorem B6703937 : Blo 1985435 6703937 := bstep (se 2 (by rfl) ⟨2513976, by rfl⟩ : syracuseStep 6703937 = 5027953) B5027953
theorem B4469291 : Blo 1985435 4469291 := bstep (se 1 (by rfl) ⟨3351968, by rfl⟩ : syracuseStep 4469291 = 6703937) B6703937
theorem B2979527 : Blo 1985435 2979527 := bstep (se 1 (by rfl) ⟨2234645, by rfl⟩ : syracuseStep 2979527 = 4469291) B4469291
theorem B1986351 : Blo 1985435 1986351 := bstep (se 1 (by rfl) ⟨1489763, by rfl⟩ : syracuseStep 1986351 = 2979527) B2979527
theorem B2979533 : Blo 1985435 2979533 := bbase (se 3 (by rfl) ⟨558662, by rfl⟩ : syracuseStep 2979533 = 1117325) (by norm_num)
theorem B1986355 : Blo 1985435 1986355 := bstep (se 1 (by rfl) ⟨1489766, by rfl⟩ : syracuseStep 1986355 = 2979533) B2979533
theorem B4469309 : Blo 1985435 4469309 := bbase (se 3 (by rfl) ⟨837995, by rfl⟩ : syracuseStep 4469309 = 1675991) (by norm_num)
theorem B2979539 : Blo 1985435 2979539 := bstep (se 1 (by rfl) ⟨2234654, by rfl⟩ : syracuseStep 2979539 = 4469309) B4469309
theorem B1986359 : Blo 1985435 1986359 := bstep (se 1 (by rfl) ⟨1489769, by rfl⟩ : syracuseStep 1986359 = 2979539) B2979539
theorem B3351989 : Blo 1985435 3351989 := bbase (se 5 (by rfl) ⟨157124, by rfl⟩ : syracuseStep 3351989 = 314249) (by norm_num)
theorem B2234659 : Blo 1985435 2234659 := bstep (se 1 (by rfl) ⟨1675994, by rfl⟩ : syracuseStep 2234659 = 3351989) B3351989
theorem B2979545 : Blo 1985435 2979545 := bstep (se 2 (by rfl) ⟨1117329, by rfl⟩ : syracuseStep 2979545 = 2234659) B2234659
theorem B1986363 : Blo 1985435 1986363 := bstep (se 1 (by rfl) ⟨1489772, by rfl⟩ : syracuseStep 1986363 = 2979545) B2979545
theorem B2121185 : Blo 1985435 2121185 := bbase (se 2 (by rfl) ⟨795444, by rfl⟩ : syracuseStep 2121185 = 1590889) (by norm_num)
theorem B5656493 : Blo 1985435 5656493 := bstep (se 3 (by rfl) ⟨1060592, by rfl⟩ : syracuseStep 5656493 = 2121185) B2121185
theorem B15083981 : Blo 1985435 15083981 := bstep (se 3 (by rfl) ⟨2828246, by rfl⟩ : syracuseStep 15083981 = 5656493) B5656493
theorem B10055987 : Blo 1985435 10055987 := bstep (se 1 (by rfl) ⟨7541990, by rfl⟩ : syracuseStep 10055987 = 15083981) B15083981
theorem B6703991 : Blo 1985435 6703991 := bstep (se 1 (by rfl) ⟨5027993, by rfl⟩ : syracuseStep 6703991 = 10055987) B10055987
theorem B4469327 : Blo 1985435 4469327 := bstep (se 1 (by rfl) ⟨3351995, by rfl⟩ : syracuseStep 4469327 = 6703991) B6703991
theorem B2979551 : Blo 1985435 2979551 := bstep (se 1 (by rfl) ⟨2234663, by rfl⟩ : syracuseStep 2979551 = 4469327) B4469327
theorem B1986367 : Blo 1985435 1986367 := bstep (se 1 (by rfl) ⟨1489775, by rfl⟩ : syracuseStep 1986367 = 2979551) B2979551
theorem B2979557 : Blo 1985435 2979557 := bbase (se 4 (by rfl) ⟨279333, by rfl⟩ : syracuseStep 2979557 = 558667) (by norm_num)
theorem B1986371 : Blo 1985435 1986371 := bstep (se 1 (by rfl) ⟨1489778, by rfl⟩ : syracuseStep 1986371 = 2979557) B2979557
theorem B5656517 : Blo 1985435 5656517 := bbase (se 4 (by rfl) ⟨530298, by rfl⟩ : syracuseStep 5656517 = 1060597) (by norm_num)
theorem B3771011 : Blo 1985435 3771011 := bstep (se 1 (by rfl) ⟨2828258, by rfl⟩ : syracuseStep 3771011 = 5656517) B5656517
theorem B2514007 : Blo 1985435 2514007 := bstep (se 1 (by rfl) ⟨1885505, by rfl⟩ : syracuseStep 2514007 = 3771011) B3771011
theorem B3352009 : Blo 1985435 3352009 := bstep (se 2 (by rfl) ⟨1257003, by rfl⟩ : syracuseStep 3352009 = 2514007) B2514007
theorem B4469345 : Blo 1985435 4469345 := bstep (se 2 (by rfl) ⟨1676004, by rfl⟩ : syracuseStep 4469345 = 3352009) B3352009
theorem B2979563 : Blo 1985435 2979563 := bstep (se 1 (by rfl) ⟨2234672, by rfl⟩ : syracuseStep 2979563 = 4469345) B4469345
theorem B1986375 : Blo 1985435 1986375 := bstep (se 1 (by rfl) ⟨1489781, by rfl⟩ : syracuseStep 1986375 = 2979563) B2979563
theorem B2234677 : Blo 1985435 2234677 := bbase (se 5 (by rfl) ⟨104750, by rfl⟩ : syracuseStep 2234677 = 209501) (by norm_num)
theorem B2979569 : Blo 1985435 2979569 := bstep (se 2 (by rfl) ⟨1117338, by rfl⟩ : syracuseStep 2979569 = 2234677) B2234677
theorem B1986379 : Blo 1985435 1986379 := bstep (se 1 (by rfl) ⟨1489784, by rfl⟩ : syracuseStep 1986379 = 2979569) B2979569
theorem B2514017 : Blo 1985435 2514017 := bbase (se 2 (by rfl) ⟨942756, by rfl⟩ : syracuseStep 2514017 = 1885513) (by norm_num)
theorem B6704045 : Blo 1985435 6704045 := bstep (se 3 (by rfl) ⟨1257008, by rfl⟩ : syracuseStep 6704045 = 2514017) B2514017
theorem B4469363 : Blo 1985435 4469363 := bstep (se 1 (by rfl) ⟨3352022, by rfl⟩ : syracuseStep 4469363 = 6704045) B6704045
theorem B2979575 : Blo 1985435 2979575 := bstep (se 1 (by rfl) ⟨2234681, by rfl⟩ : syracuseStep 2979575 = 4469363) B4469363
theorem B1986383 : Blo 1985435 1986383 := bstep (se 1 (by rfl) ⟨1489787, by rfl⟩ : syracuseStep 1986383 = 2979575) B2979575
theorem B2979581 : Blo 1985435 2979581 := bbase (se 3 (by rfl) ⟨558671, by rfl⟩ : syracuseStep 2979581 = 1117343) (by norm_num)
theorem B1986387 : Blo 1985435 1986387 := bstep (se 1 (by rfl) ⟨1489790, by rfl⟩ : syracuseStep 1986387 = 2979581) B2979581
theorem B4469381 : Blo 1985435 4469381 := bbase (se 4 (by rfl) ⟨419004, by rfl⟩ : syracuseStep 4469381 = 838009) (by norm_num)
theorem B2979587 : Blo 1985435 2979587 := bstep (se 1 (by rfl) ⟨2234690, by rfl⟩ : syracuseStep 2979587 = 4469381) B4469381
theorem B1986391 : Blo 1985435 1986391 := bstep (se 1 (by rfl) ⟨1489793, by rfl⟩ : syracuseStep 1986391 = 2979587) B2979587
theorem B6450469 : Blo 1985435 6450469 := bbase (se 4 (by rfl) ⟨604731, by rfl⟩ : syracuseStep 6450469 = 1209463) (by norm_num)
theorem B34402501 : Blo 1985435 34402501 := bstep (se 4 (by rfl) ⟨3225234, by rfl⟩ : syracuseStep 34402501 = 6450469) B6450469
theorem B183480005 : Blo 1985435 183480005 := bstep (se 4 (by rfl) ⟨17201250, by rfl⟩ : syracuseStep 183480005 = 34402501) B34402501
theorem B122320003 : Blo 1985435 122320003 := bstep (se 1 (by rfl) ⟨91740002, by rfl⟩ : syracuseStep 122320003 = 183480005) B183480005
theorem B163093337 : Blo 1985435 163093337 := bstep (se 2 (by rfl) ⟨61160001, by rfl⟩ : syracuseStep 163093337 = 122320003) B122320003
theorem B108728891 : Blo 1985435 108728891 := bstep (se 1 (by rfl) ⟨81546668, by rfl⟩ : syracuseStep 108728891 = 163093337) B163093337
theorem B72485927 : Blo 1985435 72485927 := bstep (se 1 (by rfl) ⟨54364445, by rfl⟩ : syracuseStep 72485927 = 108728891) B108728891
theorem B48323951 : Blo 1985435 48323951 := bstep (se 1 (by rfl) ⟨36242963, by rfl⟩ : syracuseStep 48323951 = 72485927) B72485927
theorem B32215967 : Blo 1985435 32215967 := bstep (se 1 (by rfl) ⟨24161975, by rfl⟩ : syracuseStep 32215967 = 48323951) B48323951
theorem B21477311 : Blo 1985435 21477311 := bstep (se 1 (by rfl) ⟨16107983, by rfl⟩ : syracuseStep 21477311 = 32215967) B32215967
theorem B14318207 : Blo 1985435 14318207 := bstep (se 1 (by rfl) ⟨10738655, by rfl⟩ : syracuseStep 14318207 = 21477311) B21477311
theorem B9545471 : Blo 1985435 9545471 := bstep (se 1 (by rfl) ⟨7159103, by rfl⟩ : syracuseStep 9545471 = 14318207) B14318207
theorem B6363647 : Blo 1985435 6363647 := bstep (se 1 (by rfl) ⟨4772735, by rfl⟩ : syracuseStep 6363647 = 9545471) B9545471
theorem B4242431 : Blo 1985435 4242431 := bstep (se 1 (by rfl) ⟨3181823, by rfl⟩ : syracuseStep 4242431 = 6363647) B6363647
theorem B2828287 : Blo 1985435 2828287 := bstep (se 1 (by rfl) ⟨2121215, by rfl⟩ : syracuseStep 2828287 = 4242431) B4242431
theorem B3771049 : Blo 1985435 3771049 := bstep (se 2 (by rfl) ⟨1414143, by rfl⟩ : syracuseStep 3771049 = 2828287) B2828287
theorem B5028065 : Blo 1985435 5028065 := bstep (se 2 (by rfl) ⟨1885524, by rfl⟩ : syracuseStep 5028065 = 3771049) B3771049
theorem B3352043 : Blo 1985435 3352043 := bstep (se 1 (by rfl) ⟨2514032, by rfl⟩ : syracuseStep 3352043 = 5028065) B5028065
theorem B2234695 : Blo 1985435 2234695 := bstep (se 1 (by rfl) ⟨1676021, by rfl⟩ : syracuseStep 2234695 = 3352043) B3352043
theorem B2979593 : Blo 1985435 2979593 := bstep (se 2 (by rfl) ⟨1117347, by rfl⟩ : syracuseStep 2979593 = 2234695) B2234695
theorem B1986395 : Blo 1985435 1986395 := bstep (se 1 (by rfl) ⟨1489796, by rfl⟩ : syracuseStep 1986395 = 2979593) B2979593
theorem B10056149 : Blo 1985435 10056149 := bbase (se 7 (by rfl) ⟨117845, by rfl⟩ : syracuseStep 10056149 = 235691) (by norm_num)
theorem B6704099 : Blo 1985435 6704099 := bstep (se 1 (by rfl) ⟨5028074, by rfl⟩ : syracuseStep 6704099 = 10056149) B10056149
theorem B4469399 : Blo 1985435 4469399 := bstep (se 1 (by rfl) ⟨3352049, by rfl⟩ : syracuseStep 4469399 = 6704099) B6704099
theorem B2979599 : Blo 1985435 2979599 := bstep (se 1 (by rfl) ⟨2234699, by rfl⟩ : syracuseStep 2979599 = 4469399) B4469399
theorem B1986399 : Blo 1985435 1986399 := bstep (se 1 (by rfl) ⟨1489799, by rfl⟩ : syracuseStep 1986399 = 2979599) B2979599
theorem B2979605 : Blo 1985435 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B1986403 : Blo 1985435 1986403 := bstep (se 1 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 1986403 = 2979605) B2979605
theorem B13591189 : Blo 1985435 13591189 := bbase (se 6 (by rfl) ⟨318543, by rfl⟩ : syracuseStep 13591189 = 637087) (by norm_num)
theorem B18121585 : Blo 1985435 18121585 := bstep (se 2 (by rfl) ⟨6795594, by rfl⟩ : syracuseStep 18121585 = 13591189) B13591189
theorem B24162113 : Blo 1985435 24162113 := bstep (se 2 (by rfl) ⟨9060792, by rfl⟩ : syracuseStep 24162113 = 18121585) B18121585
theorem B16108075 : Blo 1985435 16108075 := bstep (se 1 (by rfl) ⟨12081056, by rfl⟩ : syracuseStep 16108075 = 24162113) B24162113
theorem B85909733 : Blo 1985435 85909733 := bstep (se 4 (by rfl) ⟨8054037, by rfl⟩ : syracuseStep 85909733 = 16108075) B16108075
theorem B57273155 : Blo 1985435 57273155 := bstep (se 1 (by rfl) ⟨42954866, by rfl⟩ : syracuseStep 57273155 = 85909733) B85909733
theorem B38182103 : Blo 1985435 38182103 := bstep (se 1 (by rfl) ⟨28636577, by rfl⟩ : syracuseStep 38182103 = 57273155) B57273155
theorem B25454735 : Blo 1985435 25454735 := bstep (se 1 (by rfl) ⟨19091051, by rfl⟩ : syracuseStep 25454735 = 38182103) B38182103
theorem B16969823 : Blo 1985435 16969823 := bstep (se 1 (by rfl) ⟨12727367, by rfl⟩ : syracuseStep 16969823 = 25454735) B25454735
theorem B11313215 : Blo 1985435 11313215 := bstep (se 1 (by rfl) ⟨8484911, by rfl⟩ : syracuseStep 11313215 = 16969823) B16969823
theorem B7542143 : Blo 1985435 7542143 := bstep (se 1 (by rfl) ⟨5656607, by rfl⟩ : syracuseStep 7542143 = 11313215) B11313215
theorem B5028095 : Blo 1985435 5028095 := bstep (se 1 (by rfl) ⟨3771071, by rfl⟩ : syracuseStep 5028095 = 7542143) B7542143
theorem B3352063 : Blo 1985435 3352063 := bstep (se 1 (by rfl) ⟨2514047, by rfl⟩ : syracuseStep 3352063 = 5028095) B5028095
theorem B4469417 : Blo 1985435 4469417 := bstep (se 2 (by rfl) ⟨1676031, by rfl⟩ : syracuseStep 4469417 = 3352063) B3352063
theorem B2979611 : Blo 1985435 2979611 := bstep (se 1 (by rfl) ⟨2234708, by rfl⟩ : syracuseStep 2979611 = 4469417) B4469417
theorem B1986407 : Blo 1985435 1986407 := bstep (se 1 (by rfl) ⟨1489805, by rfl⟩ : syracuseStep 1986407 = 2979611) B2979611
theorem B2234713 : Blo 1985435 2234713 := bbase (se 2 (by rfl) ⟨838017, by rfl⟩ : syracuseStep 2234713 = 1676035) (by norm_num)
theorem B2979617 : Blo 1985435 2979617 := bstep (se 2 (by rfl) ⟨1117356, by rfl⟩ : syracuseStep 2979617 = 2234713) B2234713
theorem B1986411 : Blo 1985435 1986411 := bstep (se 1 (by rfl) ⟨1489808, by rfl⟩ : syracuseStep 1986411 = 2979617) B2979617
theorem B12081109 : Blo 1985435 12081109 := bbase (se 7 (by rfl) ⟨141575, by rfl⟩ : syracuseStep 12081109 = 283151) (by norm_num)
theorem B16108145 : Blo 1985435 16108145 := bstep (se 2 (by rfl) ⟨6040554, by rfl⟩ : syracuseStep 16108145 = 12081109) B12081109
theorem B10738763 : Blo 1985435 10738763 := bstep (se 1 (by rfl) ⟨8054072, by rfl⟩ : syracuseStep 10738763 = 16108145) B16108145
theorem B7159175 : Blo 1985435 7159175 := bstep (se 1 (by rfl) ⟨5369381, by rfl⟩ : syracuseStep 7159175 = 10738763) B10738763
theorem B4772783 : Blo 1985435 4772783 := bstep (se 1 (by rfl) ⟨3579587, by rfl⟩ : syracuseStep 4772783 = 7159175) B7159175
theorem B3181855 : Blo 1985435 3181855 := bstep (se 1 (by rfl) ⟨2386391, by rfl⟩ : syracuseStep 3181855 = 4772783) B4772783
theorem B4242473 : Blo 1985435 4242473 := bstep (se 2 (by rfl) ⟨1590927, by rfl⟩ : syracuseStep 4242473 = 3181855) B3181855
theorem B2828315 : Blo 1985435 2828315 := bstep (se 1 (by rfl) ⟨2121236, by rfl⟩ : syracuseStep 2828315 = 4242473) B4242473
theorem B7542173 : Blo 1985435 7542173 := bstep (se 3 (by rfl) ⟨1414157, by rfl⟩ : syracuseStep 7542173 = 2828315) B2828315
theorem B5028115 : Blo 1985435 5028115 := bstep (se 1 (by rfl) ⟨3771086, by rfl⟩ : syracuseStep 5028115 = 7542173) B7542173
theorem B6704153 : Blo 1985435 6704153 := bstep (se 2 (by rfl) ⟨2514057, by rfl⟩ : syracuseStep 6704153 = 5028115) B5028115
theorem B4469435 : Blo 1985435 4469435 := bstep (se 1 (by rfl) ⟨3352076, by rfl⟩ : syracuseStep 4469435 = 6704153) B6704153
theorem B2979623 : Blo 1985435 2979623 := bstep (se 1 (by rfl) ⟨2234717, by rfl⟩ : syracuseStep 2979623 = 4469435) B4469435
theorem B1986415 : Blo 1985435 1986415 := bstep (se 1 (by rfl) ⟨1489811, by rfl⟩ : syracuseStep 1986415 = 2979623) B2979623
theorem B2979629 : Blo 1985435 2979629 := bbase (se 3 (by rfl) ⟨558680, by rfl⟩ : syracuseStep 2979629 = 1117361) (by norm_num)
theorem B1986419 : Blo 1985435 1986419 := bstep (se 1 (by rfl) ⟨1489814, by rfl⟩ : syracuseStep 1986419 = 2979629) B2979629
theorem B4469453 : Blo 1985435 4469453 := bbase (se 3 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 4469453 = 1676045) (by norm_num)
theorem B2979635 : Blo 1985435 2979635 := bstep (se 1 (by rfl) ⟨2234726, by rfl⟩ : syracuseStep 2979635 = 4469453) B4469453
theorem B1986423 : Blo 1985435 1986423 := bstep (se 1 (by rfl) ⟨1489817, by rfl⟩ : syracuseStep 1986423 = 2979635) B2979635
theorem B2514073 : Blo 1985435 2514073 := bbase (se 2 (by rfl) ⟨942777, by rfl⟩ : syracuseStep 2514073 = 1885555) (by norm_num)
theorem B3352097 : Blo 1985435 3352097 := bstep (se 2 (by rfl) ⟨1257036, by rfl⟩ : syracuseStep 3352097 = 2514073) B2514073
theorem B2234731 : Blo 1985435 2234731 := bstep (se 1 (by rfl) ⟨1676048, by rfl⟩ : syracuseStep 2234731 = 3352097) B3352097
theorem B2979641 : Blo 1985435 2979641 := bstep (se 2 (by rfl) ⟨1117365, by rfl⟩ : syracuseStep 2979641 = 2234731) B2234731
theorem B1986427 : Blo 1985435 1986427 := bstep (se 1 (by rfl) ⟨1489820, by rfl⟩ : syracuseStep 1986427 = 2979641) B2979641
theorem B8485013 : Blo 1985435 8485013 := bbase (se 6 (by rfl) ⟨198867, by rfl⟩ : syracuseStep 8485013 = 397735) (by norm_num)
theorem B22626701 : Blo 1985435 22626701 := bstep (se 3 (by rfl) ⟨4242506, by rfl⟩ : syracuseStep 22626701 = 8485013) B8485013
theorem B15084467 : Blo 1985435 15084467 := bstep (se 1 (by rfl) ⟨11313350, by rfl⟩ : syracuseStep 15084467 = 22626701) B22626701
theorem B10056311 : Blo 1985435 10056311 := bstep (se 1 (by rfl) ⟨7542233, by rfl⟩ : syracuseStep 10056311 = 15084467) B15084467
theorem B6704207 : Blo 1985435 6704207 := bstep (se 1 (by rfl) ⟨5028155, by rfl⟩ : syracuseStep 6704207 = 10056311) B10056311
theorem B4469471 : Blo 1985435 4469471 := bstep (se 1 (by rfl) ⟨3352103, by rfl⟩ : syracuseStep 4469471 = 6704207) B6704207
theorem B2979647 : Blo 1985435 2979647 := bstep (se 1 (by rfl) ⟨2234735, by rfl⟩ : syracuseStep 2979647 = 4469471) B4469471
theorem B1986431 : Blo 1985435 1986431 := bstep (se 1 (by rfl) ⟨1489823, by rfl⟩ : syracuseStep 1986431 = 2979647) B2979647
theorem B2979653 : Blo 1985435 2979653 := bbase (se 4 (by rfl) ⟨279342, by rfl⟩ : syracuseStep 2979653 = 558685) (by norm_num)
theorem B1986435 : Blo 1985435 1986435 := bstep (se 1 (by rfl) ⟨1489826, by rfl⟩ : syracuseStep 1986435 = 2979653) B2979653
theorem B3352117 : Blo 1985435 3352117 := bbase (se 5 (by rfl) ⟨157130, by rfl⟩ : syracuseStep 3352117 = 314261) (by norm_num)
theorem B4469489 : Blo 1985435 4469489 := bstep (se 2 (by rfl) ⟨1676058, by rfl⟩ : syracuseStep 4469489 = 3352117) B3352117
theorem B2979659 : Blo 1985435 2979659 := bstep (se 1 (by rfl) ⟨2234744, by rfl⟩ : syracuseStep 2979659 = 4469489) B4469489
theorem B1986439 : Blo 1985435 1986439 := bstep (se 1 (by rfl) ⟨1489829, by rfl⟩ : syracuseStep 1986439 = 2979659) B2979659
theorem B2234749 : Blo 1985435 2234749 := bbase (se 3 (by rfl) ⟨419015, by rfl⟩ : syracuseStep 2234749 = 838031) (by norm_num)
theorem B2979665 : Blo 1985435 2979665 := bstep (se 2 (by rfl) ⟨1117374, by rfl⟩ : syracuseStep 2979665 = 2234749) B2234749
theorem B1986443 : Blo 1985435 1986443 := bstep (se 1 (by rfl) ⟨1489832, by rfl⟩ : syracuseStep 1986443 = 2979665) B2979665
theorem B6704261 : Blo 1985435 6704261 := bbase (se 4 (by rfl) ⟨628524, by rfl⟩ : syracuseStep 6704261 = 1257049) (by norm_num)
theorem B4469507 : Blo 1985435 4469507 := bstep (se 1 (by rfl) ⟨3352130, by rfl⟩ : syracuseStep 4469507 = 6704261) B6704261
theorem B2979671 : Blo 1985435 2979671 := bstep (se 1 (by rfl) ⟨2234753, by rfl⟩ : syracuseStep 2979671 = 4469507) B4469507
theorem B1986447 : Blo 1985435 1986447 := bstep (se 1 (by rfl) ⟨1489835, by rfl⟩ : syracuseStep 1986447 = 2979671) B2979671
theorem B2979677 : Blo 1985435 2979677 := bbase (se 3 (by rfl) ⟨558689, by rfl⟩ : syracuseStep 2979677 = 1117379) (by norm_num)
theorem B1986451 : Blo 1985435 1986451 := bstep (se 1 (by rfl) ⟨1489838, by rfl⟩ : syracuseStep 1986451 = 2979677) B2979677
theorem B4469525 : Blo 1985435 4469525 := bbase (se 6 (by rfl) ⟨104754, by rfl⟩ : syracuseStep 4469525 = 209509) (by norm_num)
theorem B2979683 : Blo 1985435 2979683 := bstep (se 1 (by rfl) ⟨2234762, by rfl⟩ : syracuseStep 2979683 = 4469525) B4469525
theorem B1986455 : Blo 1985435 1986455 := bstep (se 1 (by rfl) ⟨1489841, by rfl⟩ : syracuseStep 1986455 = 2979683) B2979683
theorem B7542341 : Blo 1985435 7542341 := bbase (se 4 (by rfl) ⟨707094, by rfl⟩ : syracuseStep 7542341 = 1414189) (by norm_num)
theorem B5028227 : Blo 1985435 5028227 := bstep (se 1 (by rfl) ⟨3771170, by rfl⟩ : syracuseStep 5028227 = 7542341) B7542341
theorem B3352151 : Blo 1985435 3352151 := bstep (se 1 (by rfl) ⟨2514113, by rfl⟩ : syracuseStep 3352151 = 5028227) B5028227
theorem B2234767 : Blo 1985435 2234767 := bstep (se 1 (by rfl) ⟨1676075, by rfl⟩ : syracuseStep 2234767 = 3352151) B3352151
theorem B2979689 : Blo 1985435 2979689 := bstep (se 2 (by rfl) ⟨1117383, by rfl⟩ : syracuseStep 2979689 = 2234767) B2234767
theorem B1986459 : Blo 1985435 1986459 := bstep (se 1 (by rfl) ⟨1489844, by rfl⟩ : syracuseStep 1986459 = 2979689) B2979689
theorem B4027133 : Blo 1985435 4027133 := bbase (se 3 (by rfl) ⟨755087, by rfl⟩ : syracuseStep 4027133 = 1510175) (by norm_num)
theorem B2684755 : Blo 1985435 2684755 := bstep (se 1 (by rfl) ⟨2013566, by rfl⟩ : syracuseStep 2684755 = 4027133) B4027133
theorem B14318693 : Blo 1985435 14318693 := bstep (se 4 (by rfl) ⟨1342377, by rfl⟩ : syracuseStep 14318693 = 2684755) B2684755
theorem B9545795 : Blo 1985435 9545795 := bstep (se 1 (by rfl) ⟨7159346, by rfl⟩ : syracuseStep 9545795 = 14318693) B14318693
theorem B6363863 : Blo 1985435 6363863 := bstep (se 1 (by rfl) ⟨4772897, by rfl⟩ : syracuseStep 6363863 = 9545795) B9545795
theorem B4242575 : Blo 1985435 4242575 := bstep (se 1 (by rfl) ⟨3181931, by rfl⟩ : syracuseStep 4242575 = 6363863) B6363863
theorem B11313533 : Blo 1985435 11313533 := bstep (se 3 (by rfl) ⟨2121287, by rfl⟩ : syracuseStep 11313533 = 4242575) B4242575
theorem B7542355 : Blo 1985435 7542355 := bstep (se 1 (by rfl) ⟨5656766, by rfl⟩ : syracuseStep 7542355 = 11313533) B11313533
theorem B10056473 : Blo 1985435 10056473 := bstep (se 2 (by rfl) ⟨3771177, by rfl⟩ : syracuseStep 10056473 = 7542355) B7542355
theorem B6704315 : Blo 1985435 6704315 := bstep (se 1 (by rfl) ⟨5028236, by rfl⟩ : syracuseStep 6704315 = 10056473) B10056473
theorem B4469543 : Blo 1985435 4469543 := bstep (se 1 (by rfl) ⟨3352157, by rfl⟩ : syracuseStep 4469543 = 6704315) B6704315
theorem B2979695 : Blo 1985435 2979695 := bstep (se 1 (by rfl) ⟨2234771, by rfl⟩ : syracuseStep 2979695 = 4469543) B4469543
theorem B1986463 : Blo 1985435 1986463 := bstep (se 1 (by rfl) ⟨1489847, by rfl⟩ : syracuseStep 1986463 = 2979695) B2979695
theorem B2979701 : Blo 1985435 2979701 := bbase (se 5 (by rfl) ⟨139673, by rfl⟩ : syracuseStep 2979701 = 279347) (by norm_num)
theorem B1986467 : Blo 1985435 1986467 := bstep (se 1 (by rfl) ⟨1489850, by rfl⟩ : syracuseStep 1986467 = 2979701) B2979701
theorem B13591637 : Blo 1985435 13591637 := bbase (se 8 (by rfl) ⟨79638, by rfl⟩ : syracuseStep 13591637 = 159277) (by norm_num)
theorem B9061091 : Blo 1985435 9061091 := bstep (se 1 (by rfl) ⟨6795818, by rfl⟩ : syracuseStep 9061091 = 13591637) B13591637
theorem B6040727 : Blo 1985435 6040727 := bstep (se 1 (by rfl) ⟨4530545, by rfl⟩ : syracuseStep 6040727 = 9061091) B9061091
theorem B4027151 : Blo 1985435 4027151 := bstep (se 1 (by rfl) ⟨3020363, by rfl⟩ : syracuseStep 4027151 = 6040727) B6040727
theorem B2684767 : Blo 1985435 2684767 := bstep (se 1 (by rfl) ⟨2013575, by rfl⟩ : syracuseStep 2684767 = 4027151) B4027151
theorem B3579689 : Blo 1985435 3579689 := bstep (se 2 (by rfl) ⟨1342383, by rfl⟩ : syracuseStep 3579689 = 2684767) B2684767
theorem B2386459 : Blo 1985435 2386459 := bstep (se 1 (by rfl) ⟨1789844, by rfl⟩ : syracuseStep 2386459 = 3579689) B3579689
theorem B3181945 : Blo 1985435 3181945 := bstep (se 2 (by rfl) ⟨1193229, by rfl⟩ : syracuseStep 3181945 = 2386459) B2386459
theorem B4242593 : Blo 1985435 4242593 := bstep (se 2 (by rfl) ⟨1590972, by rfl⟩ : syracuseStep 4242593 = 3181945) B3181945
theorem B2828395 : Blo 1985435 2828395 := bstep (se 1 (by rfl) ⟨2121296, by rfl⟩ : syracuseStep 2828395 = 4242593) B4242593
theorem B3771193 : Blo 1985435 3771193 := bstep (se 2 (by rfl) ⟨1414197, by rfl⟩ : syracuseStep 3771193 = 2828395) B2828395
theorem B5028257 : Blo 1985435 5028257 := bstep (se 2 (by rfl) ⟨1885596, by rfl⟩ : syracuseStep 5028257 = 3771193) B3771193
theorem B3352171 : Blo 1985435 3352171 := bstep (se 1 (by rfl) ⟨2514128, by rfl⟩ : syracuseStep 3352171 = 5028257) B5028257
theorem B4469561 : Blo 1985435 4469561 := bstep (se 2 (by rfl) ⟨1676085, by rfl⟩ : syracuseStep 4469561 = 3352171) B3352171
theorem B2979707 : Blo 1985435 2979707 := bstep (se 1 (by rfl) ⟨2234780, by rfl⟩ : syracuseStep 2979707 = 4469561) B4469561
theorem B1986471 : Blo 1985435 1986471 := bstep (se 1 (by rfl) ⟨1489853, by rfl⟩ : syracuseStep 1986471 = 2979707) B2979707
theorem B2234785 : Blo 1985435 2234785 := bbase (se 2 (by rfl) ⟨838044, by rfl⟩ : syracuseStep 2234785 = 1676089) (by norm_num)
theorem B2979713 : Blo 1985435 2979713 := bstep (se 2 (by rfl) ⟨1117392, by rfl⟩ : syracuseStep 2979713 = 2234785) B2234785
theorem B1986475 : Blo 1985435 1986475 := bstep (se 1 (by rfl) ⟨1489856, by rfl⟩ : syracuseStep 1986475 = 2979713) B2979713
theorem B5028277 : Blo 1985435 5028277 := bbase (se 5 (by rfl) ⟨235700, by rfl⟩ : syracuseStep 5028277 = 471401) (by norm_num)
theorem B6704369 : Blo 1985435 6704369 := bstep (se 2 (by rfl) ⟨2514138, by rfl⟩ : syracuseStep 6704369 = 5028277) B5028277
theorem B4469579 : Blo 1985435 4469579 := bstep (se 1 (by rfl) ⟨3352184, by rfl⟩ : syracuseStep 4469579 = 6704369) B6704369
theorem B2979719 : Blo 1985435 2979719 := bstep (se 1 (by rfl) ⟨2234789, by rfl⟩ : syracuseStep 2979719 = 4469579) B4469579
theorem B1986479 : Blo 1985435 1986479 := bstep (se 1 (by rfl) ⟨1489859, by rfl⟩ : syracuseStep 1986479 = 2979719) B2979719
theorem B2979725 : Blo 1985435 2979725 := bbase (se 3 (by rfl) ⟨558698, by rfl⟩ : syracuseStep 2979725 = 1117397) (by norm_num)
theorem B1986483 : Blo 1985435 1986483 := bstep (se 1 (by rfl) ⟨1489862, by rfl⟩ : syracuseStep 1986483 = 2979725) B2979725
theorem B4469597 : Blo 1985435 4469597 := bbase (se 3 (by rfl) ⟨838049, by rfl⟩ : syracuseStep 4469597 = 1676099) (by norm_num)
theorem B2979731 : Blo 1985435 2979731 := bstep (se 1 (by rfl) ⟨2234798, by rfl⟩ : syracuseStep 2979731 = 4469597) B4469597
theorem B1986487 : Blo 1985435 1986487 := bstep (se 1 (by rfl) ⟨1489865, by rfl⟩ : syracuseStep 1986487 = 2979731) B2979731
theorem B3352205 : Blo 1985435 3352205 := bbase (se 3 (by rfl) ⟨628538, by rfl⟩ : syracuseStep 3352205 = 1257077) (by norm_num)
theorem B2234803 : Blo 1985435 2234803 := bstep (se 1 (by rfl) ⟨1676102, by rfl⟩ : syracuseStep 2234803 = 3352205) B3352205
theorem B2979737 : Blo 1985435 2979737 := bstep (se 2 (by rfl) ⟨1117401, by rfl⟩ : syracuseStep 2979737 = 2234803) B2234803
theorem B1986491 : Blo 1985435 1986491 := bstep (se 1 (by rfl) ⟨1489868, by rfl⟩ : syracuseStep 1986491 = 2979737) B2979737
theorem B8601061 : Blo 1985435 8601061 := bbase (se 4 (by rfl) ⟨806349, by rfl⟩ : syracuseStep 8601061 = 1612699) (by norm_num)
theorem B11468081 : Blo 1985435 11468081 := bstep (se 2 (by rfl) ⟨4300530, by rfl⟩ : syracuseStep 11468081 = 8601061) B8601061
theorem B7645387 : Blo 1985435 7645387 := bstep (se 1 (by rfl) ⟨5734040, by rfl⟩ : syracuseStep 7645387 = 11468081) B11468081
theorem B10193849 : Blo 1985435 10193849 := bstep (se 2 (by rfl) ⟨3822693, by rfl⟩ : syracuseStep 10193849 = 7645387) B7645387
theorem B6795899 : Blo 1985435 6795899 := bstep (se 1 (by rfl) ⟨5096924, by rfl⟩ : syracuseStep 6795899 = 10193849) B10193849
theorem B4530599 : Blo 1985435 4530599 := bstep (se 1 (by rfl) ⟨3397949, by rfl⟩ : syracuseStep 4530599 = 6795899) B6795899
theorem B3020399 : Blo 1985435 3020399 := bstep (se 1 (by rfl) ⟨2265299, by rfl⟩ : syracuseStep 3020399 = 4530599) B4530599
theorem B2013599 : Blo 1985435 2013599 := bstep (se 1 (by rfl) ⟨1510199, by rfl⟩ : syracuseStep 2013599 = 3020399) B3020399
theorem B5369597 : Blo 1985435 5369597 := bstep (se 3 (by rfl) ⟨1006799, by rfl⟩ : syracuseStep 5369597 = 2013599) B2013599
theorem B3579731 : Blo 1985435 3579731 := bstep (se 1 (by rfl) ⟨2684798, by rfl⟩ : syracuseStep 3579731 = 5369597) B5369597
theorem B2386487 : Blo 1985435 2386487 := bstep (se 1 (by rfl) ⟨1789865, by rfl⟩ : syracuseStep 2386487 = 3579731) B3579731
theorem B6363965 : Blo 1985435 6363965 := bstep (se 3 (by rfl) ⟨1193243, by rfl⟩ : syracuseStep 6363965 = 2386487) B2386487
theorem B16970573 : Blo 1985435 16970573 := bstep (se 3 (by rfl) ⟨3181982, by rfl⟩ : syracuseStep 16970573 = 6363965) B6363965
theorem B11313715 : Blo 1985435 11313715 := bstep (se 1 (by rfl) ⟨8485286, by rfl⟩ : syracuseStep 11313715 = 16970573) B16970573
theorem B15084953 : Blo 1985435 15084953 := bstep (se 2 (by rfl) ⟨5656857, by rfl⟩ : syracuseStep 15084953 = 11313715) B11313715
theorem B10056635 : Blo 1985435 10056635 := bstep (se 1 (by rfl) ⟨7542476, by rfl⟩ : syracuseStep 10056635 = 15084953) B15084953
theorem B6704423 : Blo 1985435 6704423 := bstep (se 1 (by rfl) ⟨5028317, by rfl⟩ : syracuseStep 6704423 = 10056635) B10056635
theorem B4469615 : Blo 1985435 4469615 := bstep (se 1 (by rfl) ⟨3352211, by rfl⟩ : syracuseStep 4469615 = 6704423) B6704423
theorem B2979743 : Blo 1985435 2979743 := bstep (se 1 (by rfl) ⟨2234807, by rfl⟩ : syracuseStep 2979743 = 4469615) B4469615
theorem B1986495 : Blo 1985435 1986495 := bstep (se 1 (by rfl) ⟨1489871, by rfl⟩ : syracuseStep 1986495 = 2979743) B2979743
theorem B2979749 : Blo 1985435 2979749 := bbase (se 4 (by rfl) ⟨279351, by rfl⟩ : syracuseStep 2979749 = 558703) (by norm_num)
theorem B1986499 : Blo 1985435 1986499 := bstep (se 1 (by rfl) ⟨1489874, by rfl⟩ : syracuseStep 1986499 = 2979749) B2979749
theorem B2514169 : Blo 1985435 2514169 := bbase (se 2 (by rfl) ⟨942813, by rfl⟩ : syracuseStep 2514169 = 1885627) (by norm_num)
theorem B3352225 : Blo 1985435 3352225 := bstep (se 2 (by rfl) ⟨1257084, by rfl⟩ : syracuseStep 3352225 = 2514169) B2514169
theorem B4469633 : Blo 1985435 4469633 := bstep (se 2 (by rfl) ⟨1676112, by rfl⟩ : syracuseStep 4469633 = 3352225) B3352225
theorem B2979755 : Blo 1985435 2979755 := bstep (se 1 (by rfl) ⟨2234816, by rfl⟩ : syracuseStep 2979755 = 4469633) B4469633
theorem B1986503 : Blo 1985435 1986503 := bstep (se 1 (by rfl) ⟨1489877, by rfl⟩ : syracuseStep 1986503 = 2979755) B2979755
theorem B2234821 : Blo 1985435 2234821 := bbase (se 4 (by rfl) ⟨209514, by rfl⟩ : syracuseStep 2234821 = 419029) (by norm_num)
theorem B2979761 : Blo 1985435 2979761 := bstep (se 2 (by rfl) ⟨1117410, by rfl⟩ : syracuseStep 2979761 = 2234821) B2234821
theorem B1986507 : Blo 1985435 1986507 := bstep (se 1 (by rfl) ⟨1489880, by rfl⟩ : syracuseStep 1986507 = 2979761) B2979761
theorem B3771269 : Blo 1985435 3771269 := bbase (se 4 (by rfl) ⟨353556, by rfl⟩ : syracuseStep 3771269 = 707113) (by norm_num)
theorem B2514179 : Blo 1985435 2514179 := bstep (se 1 (by rfl) ⟨1885634, by rfl⟩ : syracuseStep 2514179 = 3771269) B3771269
theorem B6704477 : Blo 1985435 6704477 := bstep (se 3 (by rfl) ⟨1257089, by rfl⟩ : syracuseStep 6704477 = 2514179) B2514179
theorem B4469651 : Blo 1985435 4469651 := bstep (se 1 (by rfl) ⟨3352238, by rfl⟩ : syracuseStep 4469651 = 6704477) B6704477
theorem B2979767 : Blo 1985435 2979767 := bstep (se 1 (by rfl) ⟨2234825, by rfl⟩ : syracuseStep 2979767 = 4469651) B4469651
theorem B1986511 : Blo 1985435 1986511 := bstep (se 1 (by rfl) ⟨1489883, by rfl⟩ : syracuseStep 1986511 = 2979767) B2979767
theorem B2979773 : Blo 1985435 2979773 := bbase (se 3 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 2979773 = 1117415) (by norm_num)
theorem B1986515 : Blo 1985435 1986515 := bstep (se 1 (by rfl) ⟨1489886, by rfl⟩ : syracuseStep 1986515 = 2979773) B2979773
theorem B4469669 : Blo 1985435 4469669 := bbase (se 4 (by rfl) ⟨419031, by rfl⟩ : syracuseStep 4469669 = 838063) (by norm_num)
theorem B2979779 : Blo 1985435 2979779 := bstep (se 1 (by rfl) ⟨2234834, by rfl⟩ : syracuseStep 2979779 = 4469669) B4469669
theorem B1986519 : Blo 1985435 1986519 := bstep (se 1 (by rfl) ⟨1489889, by rfl⟩ : syracuseStep 1986519 = 2979779) B2979779
theorem B5028389 : Blo 1985435 5028389 := bbase (se 4 (by rfl) ⟨471411, by rfl⟩ : syracuseStep 5028389 = 942823) (by norm_num)
theorem B3352259 : Blo 1985435 3352259 := bstep (se 1 (by rfl) ⟨2514194, by rfl⟩ : syracuseStep 3352259 = 5028389) B5028389
theorem B2234839 : Blo 1985435 2234839 := bstep (se 1 (by rfl) ⟨1676129, by rfl⟩ : syracuseStep 2234839 = 3352259) B3352259
theorem B2979785 : Blo 1985435 2979785 := bstep (se 2 (by rfl) ⟨1117419, by rfl⟩ : syracuseStep 2979785 = 2234839) B2234839
theorem B1986523 : Blo 1985435 1986523 := bstep (se 1 (by rfl) ⟨1489892, by rfl⟩ : syracuseStep 1986523 = 2979785) B2979785
theorem B5656949 : Blo 1985435 5656949 := bbase (se 5 (by rfl) ⟨265169, by rfl⟩ : syracuseStep 5656949 = 530339) (by norm_num)
theorem B3771299 : Blo 1985435 3771299 := bstep (se 1 (by rfl) ⟨2828474, by rfl⟩ : syracuseStep 3771299 = 5656949) B5656949
theorem B10056797 : Blo 1985435 10056797 := bstep (se 3 (by rfl) ⟨1885649, by rfl⟩ : syracuseStep 10056797 = 3771299) B3771299
theorem B6704531 : Blo 1985435 6704531 := bstep (se 1 (by rfl) ⟨5028398, by rfl⟩ : syracuseStep 6704531 = 10056797) B10056797
theorem B4469687 : Blo 1985435 4469687 := bstep (se 1 (by rfl) ⟨3352265, by rfl⟩ : syracuseStep 4469687 = 6704531) B6704531
theorem B2979791 : Blo 1985435 2979791 := bstep (se 1 (by rfl) ⟨2234843, by rfl⟩ : syracuseStep 2979791 = 4469687) B4469687
theorem B1986527 : Blo 1985435 1986527 := bstep (se 1 (by rfl) ⟨1489895, by rfl⟩ : syracuseStep 1986527 = 2979791) B2979791
theorem B2979797 : Blo 1985435 2979797 := bbase (se 7 (by rfl) ⟨34919, by rfl⟩ : syracuseStep 2979797 = 69839) (by norm_num)
theorem B1986531 : Blo 1985435 1986531 := bstep (se 1 (by rfl) ⟨1489898, by rfl⟩ : syracuseStep 1986531 = 2979797) B2979797
theorem B7542629 : Blo 1985435 7542629 := bbase (se 4 (by rfl) ⟨707121, by rfl⟩ : syracuseStep 7542629 = 1414243) (by norm_num)
theorem B5028419 : Blo 1985435 5028419 := bstep (se 1 (by rfl) ⟨3771314, by rfl⟩ : syracuseStep 5028419 = 7542629) B7542629
theorem B3352279 : Blo 1985435 3352279 := bstep (se 1 (by rfl) ⟨2514209, by rfl⟩ : syracuseStep 3352279 = 5028419) B5028419
theorem B4469705 : Blo 1985435 4469705 := bstep (se 2 (by rfl) ⟨1676139, by rfl⟩ : syracuseStep 4469705 = 3352279) B3352279
theorem B2979803 : Blo 1985435 2979803 := bstep (se 1 (by rfl) ⟨2234852, by rfl⟩ : syracuseStep 2979803 = 4469705) B4469705
theorem B1986535 : Blo 1985435 1986535 := bstep (se 1 (by rfl) ⟨1489901, by rfl⟩ : syracuseStep 1986535 = 2979803) B2979803
theorem B2234857 : Blo 1985435 2234857 := bbase (se 2 (by rfl) ⟨838071, by rfl⟩ : syracuseStep 2234857 = 1676143) (by norm_num)
theorem B2979809 : Blo 1985435 2979809 := bstep (se 2 (by rfl) ⟨1117428, by rfl⟩ : syracuseStep 2979809 = 2234857) B2234857
theorem B1986539 : Blo 1985435 1986539 := bstep (se 1 (by rfl) ⟨1489904, by rfl⟩ : syracuseStep 1986539 = 2979809) B2979809
theorem B2121373 : Blo 1985435 2121373 := bbase (se 3 (by rfl) ⟨397757, by rfl⟩ : syracuseStep 2121373 = 795515) (by norm_num)
theorem B11313989 : Blo 1985435 11313989 := bstep (se 4 (by rfl) ⟨1060686, by rfl⟩ : syracuseStep 11313989 = 2121373) B2121373
theorem B7542659 : Blo 1985435 7542659 := bstep (se 1 (by rfl) ⟨5656994, by rfl⟩ : syracuseStep 7542659 = 11313989) B11313989
theorem B5028439 : Blo 1985435 5028439 := bstep (se 1 (by rfl) ⟨3771329, by rfl⟩ : syracuseStep 5028439 = 7542659) B7542659
theorem B6704585 : Blo 1985435 6704585 := bstep (se 2 (by rfl) ⟨2514219, by rfl⟩ : syracuseStep 6704585 = 5028439) B5028439
theorem B4469723 : Blo 1985435 4469723 := bstep (se 1 (by rfl) ⟨3352292, by rfl⟩ : syracuseStep 4469723 = 6704585) B6704585
theorem B2979815 : Blo 1985435 2979815 := bstep (se 1 (by rfl) ⟨2234861, by rfl⟩ : syracuseStep 2979815 = 4469723) B4469723
theorem B1986543 : Blo 1985435 1986543 := bstep (se 1 (by rfl) ⟨1489907, by rfl⟩ : syracuseStep 1986543 = 2979815) B2979815
theorem B2979821 : Blo 1985435 2979821 := bbase (se 3 (by rfl) ⟨558716, by rfl⟩ : syracuseStep 2979821 = 1117433) (by norm_num)
theorem B1986547 : Blo 1985435 1986547 := bstep (se 1 (by rfl) ⟨1489910, by rfl⟩ : syracuseStep 1986547 = 2979821) B2979821
theorem B4469741 : Blo 1985435 4469741 := bbase (se 3 (by rfl) ⟨838076, by rfl⟩ : syracuseStep 4469741 = 1676153) (by norm_num)
theorem B2979827 : Blo 1985435 2979827 := bstep (se 1 (by rfl) ⟨2234870, by rfl⟩ : syracuseStep 2979827 = 4469741) B4469741
theorem B1986551 : Blo 1985435 1986551 := bstep (se 1 (by rfl) ⟨1489913, by rfl⟩ : syracuseStep 1986551 = 2979827) B2979827
theorem B4242773 : Blo 1985435 4242773 := bbase (se 11 (by rfl) ⟨3107, by rfl⟩ : syracuseStep 4242773 = 6215) (by norm_num)
theorem B2828515 : Blo 1985435 2828515 := bstep (se 1 (by rfl) ⟨2121386, by rfl⟩ : syracuseStep 2828515 = 4242773) B4242773
theorem B3771353 : Blo 1985435 3771353 := bstep (se 2 (by rfl) ⟨1414257, by rfl⟩ : syracuseStep 3771353 = 2828515) B2828515
theorem B2514235 : Blo 1985435 2514235 := bstep (se 1 (by rfl) ⟨1885676, by rfl⟩ : syracuseStep 2514235 = 3771353) B3771353
theorem B3352313 : Blo 1985435 3352313 := bstep (se 2 (by rfl) ⟨1257117, by rfl⟩ : syracuseStep 3352313 = 2514235) B2514235
theorem B2234875 : Blo 1985435 2234875 := bstep (se 1 (by rfl) ⟨1676156, by rfl⟩ : syracuseStep 2234875 = 3352313) B3352313
theorem B2979833 : Blo 1985435 2979833 := bstep (se 2 (by rfl) ⟨1117437, by rfl⟩ : syracuseStep 2979833 = 2234875) B2234875
theorem B1986555 : Blo 1985435 1986555 := bstep (se 1 (by rfl) ⟨1489916, by rfl⟩ : syracuseStep 1986555 = 2979833) B2979833
theorem B20388341 : Blo 1985435 20388341 := bbase (se 5 (by rfl) ⟨955703, by rfl⟩ : syracuseStep 20388341 = 1911407) (by norm_num)
theorem B13592227 : Blo 1985435 13592227 := bstep (se 1 (by rfl) ⟨10194170, by rfl⟩ : syracuseStep 13592227 = 20388341) B20388341
theorem B18122969 : Blo 1985435 18122969 := bstep (se 2 (by rfl) ⟨6796113, by rfl⟩ : syracuseStep 18122969 = 13592227) B13592227
theorem B12081979 : Blo 1985435 12081979 := bstep (se 1 (by rfl) ⟨9061484, by rfl⟩ : syracuseStep 12081979 = 18122969) B18122969
theorem B64437221 : Blo 1985435 64437221 := bstep (se 4 (by rfl) ⟨6040989, by rfl⟩ : syracuseStep 64437221 = 12081979) B12081979
theorem B171832589 : Blo 1985435 171832589 := bstep (se 3 (by rfl) ⟨32218610, by rfl⟩ : syracuseStep 171832589 = 64437221) B64437221
theorem B114555059 : Blo 1985435 114555059 := bstep (se 1 (by rfl) ⟨85916294, by rfl⟩ : syracuseStep 114555059 = 171832589) B171832589
theorem B76370039 : Blo 1985435 76370039 := bstep (se 1 (by rfl) ⟨57277529, by rfl⟩ : syracuseStep 76370039 = 114555059) B114555059
theorem B50913359 : Blo 1985435 50913359 := bstep (se 1 (by rfl) ⟨38185019, by rfl⟩ : syracuseStep 50913359 = 76370039) B76370039
theorem B33942239 : Blo 1985435 33942239 := bstep (se 1 (by rfl) ⟨25456679, by rfl⟩ : syracuseStep 33942239 = 50913359) B50913359
theorem B22628159 : Blo 1985435 22628159 := bstep (se 1 (by rfl) ⟨16971119, by rfl⟩ : syracuseStep 22628159 = 33942239) B33942239
theorem B15085439 : Blo 1985435 15085439 := bstep (se 1 (by rfl) ⟨11314079, by rfl⟩ : syracuseStep 15085439 = 22628159) B22628159
theorem B10056959 : Blo 1985435 10056959 := bstep (se 1 (by rfl) ⟨7542719, by rfl⟩ : syracuseStep 10056959 = 15085439) B15085439
theorem B6704639 : Blo 1985435 6704639 := bstep (se 1 (by rfl) ⟨5028479, by rfl⟩ : syracuseStep 6704639 = 10056959) B10056959
theorem B4469759 : Blo 1985435 4469759 := bstep (se 1 (by rfl) ⟨3352319, by rfl⟩ : syracuseStep 4469759 = 6704639) B6704639
theorem B2979839 : Blo 1985435 2979839 := bstep (se 1 (by rfl) ⟨2234879, by rfl⟩ : syracuseStep 2979839 = 4469759) B4469759
theorem B1986559 : Blo 1985435 1986559 := bstep (se 1 (by rfl) ⟨1489919, by rfl⟩ : syracuseStep 1986559 = 2979839) B2979839
theorem B2979845 : Blo 1985435 2979845 := bbase (se 4 (by rfl) ⟨279360, by rfl⟩ : syracuseStep 2979845 = 558721) (by norm_num)
theorem B1986563 : Blo 1985435 1986563 := bstep (se 1 (by rfl) ⟨1489922, by rfl⟩ : syracuseStep 1986563 = 2979845) B2979845
theorem B3352333 : Blo 1985435 3352333 := bbase (se 3 (by rfl) ⟨628562, by rfl⟩ : syracuseStep 3352333 = 1257125) (by norm_num)
theorem B4469777 : Blo 1985435 4469777 := bstep (se 2 (by rfl) ⟨1676166, by rfl⟩ : syracuseStep 4469777 = 3352333) B3352333
theorem B2979851 : Blo 1985435 2979851 := bstep (se 1 (by rfl) ⟨2234888, by rfl⟩ : syracuseStep 2979851 = 4469777) B4469777
theorem B1986567 : Blo 1985435 1986567 := bstep (se 1 (by rfl) ⟨1489925, by rfl⟩ : syracuseStep 1986567 = 2979851) B2979851
theorem B2234893 : Blo 1985435 2234893 := bbase (se 3 (by rfl) ⟨419042, by rfl⟩ : syracuseStep 2234893 = 838085) (by norm_num)
theorem B2979857 : Blo 1985435 2979857 := bstep (se 2 (by rfl) ⟨1117446, by rfl⟩ : syracuseStep 2979857 = 2234893) B2234893
theorem B1986571 : Blo 1985435 1986571 := bstep (se 1 (by rfl) ⟨1489928, by rfl⟩ : syracuseStep 1986571 = 2979857) B2979857
theorem B6704693 : Blo 1985435 6704693 := bbase (se 5 (by rfl) ⟨314282, by rfl⟩ : syracuseStep 6704693 = 628565) (by norm_num)
theorem B4469795 : Blo 1985435 4469795 := bstep (se 1 (by rfl) ⟨3352346, by rfl⟩ : syracuseStep 4469795 = 6704693) B6704693
theorem B2979863 : Blo 1985435 2979863 := bstep (se 1 (by rfl) ⟨2234897, by rfl⟩ : syracuseStep 2979863 = 4469795) B4469795
theorem B1986575 : Blo 1985435 1986575 := bstep (se 1 (by rfl) ⟨1489931, by rfl⟩ : syracuseStep 1986575 = 2979863) B2979863
theorem B2979869 : Blo 1985435 2979869 := bbase (se 3 (by rfl) ⟨558725, by rfl⟩ : syracuseStep 2979869 = 1117451) (by norm_num)
theorem B1986579 : Blo 1985435 1986579 := bstep (se 1 (by rfl) ⟨1489934, by rfl⟩ : syracuseStep 1986579 = 2979869) B2979869
theorem B4469813 : Blo 1985435 4469813 := bbase (se 5 (by rfl) ⟨209522, by rfl⟩ : syracuseStep 4469813 = 419045) (by norm_num)
theorem B2979875 : Blo 1985435 2979875 := bstep (se 1 (by rfl) ⟨2234906, by rfl⟩ : syracuseStep 2979875 = 4469813) B4469813
theorem B1986583 : Blo 1985435 1986583 := bstep (se 1 (by rfl) ⟨1489937, by rfl⟩ : syracuseStep 1986583 = 2979875) B2979875
theorem B6364261 : Blo 1985435 6364261 := bbase (se 4 (by rfl) ⟨596649, by rfl⟩ : syracuseStep 6364261 = 1193299) (by norm_num)
theorem B8485681 : Blo 1985435 8485681 := bstep (se 2 (by rfl) ⟨3182130, by rfl⟩ : syracuseStep 8485681 = 6364261) B6364261
theorem B11314241 : Blo 1985435 11314241 := bstep (se 2 (by rfl) ⟨4242840, by rfl⟩ : syracuseStep 11314241 = 8485681) B8485681
theorem B7542827 : Blo 1985435 7542827 := bstep (se 1 (by rfl) ⟨5657120, by rfl⟩ : syracuseStep 7542827 = 11314241) B11314241
theorem B5028551 : Blo 1985435 5028551 := bstep (se 1 (by rfl) ⟨3771413, by rfl⟩ : syracuseStep 5028551 = 7542827) B7542827
theorem B3352367 : Blo 1985435 3352367 := bstep (se 1 (by rfl) ⟨2514275, by rfl⟩ : syracuseStep 3352367 = 5028551) B5028551
theorem B2234911 : Blo 1985435 2234911 := bstep (se 1 (by rfl) ⟨1676183, by rfl⟩ : syracuseStep 2234911 = 3352367) B3352367
theorem B2979881 : Blo 1985435 2979881 := bstep (se 2 (by rfl) ⟨1117455, by rfl⟩ : syracuseStep 2979881 = 2234911) B2234911
theorem B1986587 : Blo 1985435 1986587 := bstep (se 1 (by rfl) ⟨1489940, by rfl⟩ : syracuseStep 1986587 = 2979881) B2979881
theorem B4773205 : Blo 1985435 4773205 := bbase (se 15 (by rfl) ⟨218, by rfl⟩ : syracuseStep 4773205 = 437) (by norm_num)
theorem B6364273 : Blo 1985435 6364273 := bstep (se 2 (by rfl) ⟨2386602, by rfl⟩ : syracuseStep 6364273 = 4773205) B4773205
theorem B8485697 : Blo 1985435 8485697 := bstep (se 2 (by rfl) ⟨3182136, by rfl⟩ : syracuseStep 8485697 = 6364273) B6364273
theorem B5657131 : Blo 1985435 5657131 := bstep (se 1 (by rfl) ⟨4242848, by rfl⟩ : syracuseStep 5657131 = 8485697) B8485697
theorem B7542841 : Blo 1985435 7542841 := bstep (se 2 (by rfl) ⟨2828565, by rfl⟩ : syracuseStep 7542841 = 5657131) B5657131
theorem B10057121 : Blo 1985435 10057121 := bstep (se 2 (by rfl) ⟨3771420, by rfl⟩ : syracuseStep 10057121 = 7542841) B7542841
theorem B6704747 : Blo 1985435 6704747 := bstep (se 1 (by rfl) ⟨5028560, by rfl⟩ : syracuseStep 6704747 = 10057121) B10057121
theorem B4469831 : Blo 1985435 4469831 := bstep (se 1 (by rfl) ⟨3352373, by rfl⟩ : syracuseStep 4469831 = 6704747) B6704747
theorem B2979887 : Blo 1985435 2979887 := bstep (se 1 (by rfl) ⟨2234915, by rfl⟩ : syracuseStep 2979887 = 4469831) B4469831
theorem B1986591 : Blo 1985435 1986591 := bstep (se 1 (by rfl) ⟨1489943, by rfl⟩ : syracuseStep 1986591 = 2979887) B2979887
theorem B2979893 : Blo 1985435 2979893 := bbase (se 5 (by rfl) ⟨139682, by rfl⟩ : syracuseStep 2979893 = 279365) (by norm_num)
theorem B1986595 : Blo 1985435 1986595 := bstep (se 1 (by rfl) ⟨1489946, by rfl⟩ : syracuseStep 1986595 = 2979893) B2979893
theorem B5028581 : Blo 1985435 5028581 := bbase (se 4 (by rfl) ⟨471429, by rfl⟩ : syracuseStep 5028581 = 942859) (by norm_num)
theorem B3352387 : Blo 1985435 3352387 := bstep (se 1 (by rfl) ⟨2514290, by rfl⟩ : syracuseStep 3352387 = 5028581) B5028581
theorem B4469849 : Blo 1985435 4469849 := bstep (se 2 (by rfl) ⟨1676193, by rfl⟩ : syracuseStep 4469849 = 3352387) B3352387
theorem B2979899 : Blo 1985435 2979899 := bstep (se 1 (by rfl) ⟨2234924, by rfl⟩ : syracuseStep 2979899 = 4469849) B4469849
theorem B1986599 : Blo 1985435 1986599 := bstep (se 1 (by rfl) ⟨1489949, by rfl⟩ : syracuseStep 1986599 = 2979899) B2979899
theorem B2234929 : Blo 1985435 2234929 := bbase (se 2 (by rfl) ⟨838098, by rfl⟩ : syracuseStep 2234929 = 1676197) (by norm_num)
theorem B2979905 : Blo 1985435 2979905 := bstep (se 2 (by rfl) ⟨1117464, by rfl⟩ : syracuseStep 2979905 = 2234929) B2234929
theorem B1986603 : Blo 1985435 1986603 := bstep (se 1 (by rfl) ⟨1489952, by rfl⟩ : syracuseStep 1986603 = 2979905) B2979905
theorem B6364325 : Blo 1985435 6364325 := bbase (se 4 (by rfl) ⟨596655, by rfl⟩ : syracuseStep 6364325 = 1193311) (by norm_num)
theorem B4242883 : Blo 1985435 4242883 := bstep (se 1 (by rfl) ⟨3182162, by rfl⟩ : syracuseStep 4242883 = 6364325) B6364325
theorem B5657177 : Blo 1985435 5657177 := bstep (se 2 (by rfl) ⟨2121441, by rfl⟩ : syracuseStep 5657177 = 4242883) B4242883
theorem B3771451 : Blo 1985435 3771451 := bstep (se 1 (by rfl) ⟨2828588, by rfl⟩ : syracuseStep 3771451 = 5657177) B5657177
theorem B5028601 : Blo 1985435 5028601 := bstep (se 2 (by rfl) ⟨1885725, by rfl⟩ : syracuseStep 5028601 = 3771451) B3771451
theorem B6704801 : Blo 1985435 6704801 := bstep (se 2 (by rfl) ⟨2514300, by rfl⟩ : syracuseStep 6704801 = 5028601) B5028601
theorem B4469867 : Blo 1985435 4469867 := bstep (se 1 (by rfl) ⟨3352400, by rfl⟩ : syracuseStep 4469867 = 6704801) B6704801
theorem B2979911 : Blo 1985435 2979911 := bstep (se 1 (by rfl) ⟨2234933, by rfl⟩ : syracuseStep 2979911 = 4469867) B4469867
theorem B1986607 : Blo 1985435 1986607 := bstep (se 1 (by rfl) ⟨1489955, by rfl⟩ : syracuseStep 1986607 = 2979911) B2979911
theorem B2979917 : Blo 1985435 2979917 := bbase (se 3 (by rfl) ⟨558734, by rfl⟩ : syracuseStep 2979917 = 1117469) (by norm_num)
theorem B1986611 : Blo 1985435 1986611 := bstep (se 1 (by rfl) ⟨1489958, by rfl⟩ : syracuseStep 1986611 = 2979917) B2979917
theorem B4469885 : Blo 1985435 4469885 := bbase (se 3 (by rfl) ⟨838103, by rfl⟩ : syracuseStep 4469885 = 1676207) (by norm_num)
theorem B2979923 : Blo 1985435 2979923 := bstep (se 1 (by rfl) ⟨2234942, by rfl⟩ : syracuseStep 2979923 = 4469885) B4469885
theorem B1986615 : Blo 1985435 1986615 := bstep (se 1 (by rfl) ⟨1489961, by rfl⟩ : syracuseStep 1986615 = 2979923) B2979923
theorem B3352421 : Blo 1985435 3352421 := bbase (se 4 (by rfl) ⟨314289, by rfl⟩ : syracuseStep 3352421 = 628579) (by norm_num)
theorem B2234947 : Blo 1985435 2234947 := bstep (se 1 (by rfl) ⟨1676210, by rfl⟩ : syracuseStep 2234947 = 3352421) B3352421
theorem B2979929 : Blo 1985435 2979929 := bstep (se 2 (by rfl) ⟨1117473, by rfl⟩ : syracuseStep 2979929 = 2234947) B2234947
theorem B1986619 : Blo 1985435 1986619 := bstep (se 1 (by rfl) ⟨1489964, by rfl⟩ : syracuseStep 1986619 = 2979929) B2979929
theorem B4242917 : Blo 1985435 4242917 := bbase (se 4 (by rfl) ⟨397773, by rfl⟩ : syracuseStep 4242917 = 795547) (by norm_num)
theorem B2828611 : Blo 1985435 2828611 := bstep (se 1 (by rfl) ⟨2121458, by rfl⟩ : syracuseStep 2828611 = 4242917) B4242917
theorem B15085925 : Blo 1985435 15085925 := bstep (se 4 (by rfl) ⟨1414305, by rfl⟩ : syracuseStep 15085925 = 2828611) B2828611
theorem B10057283 : Blo 1985435 10057283 := bstep (se 1 (by rfl) ⟨7542962, by rfl⟩ : syracuseStep 10057283 = 15085925) B15085925
theorem B6704855 : Blo 1985435 6704855 := bstep (se 1 (by rfl) ⟨5028641, by rfl⟩ : syracuseStep 6704855 = 10057283) B10057283
theorem B4469903 : Blo 1985435 4469903 := bstep (se 1 (by rfl) ⟨3352427, by rfl⟩ : syracuseStep 4469903 = 6704855) B6704855
theorem B2979935 : Blo 1985435 2979935 := bstep (se 1 (by rfl) ⟨2234951, by rfl⟩ : syracuseStep 2979935 = 4469903) B4469903
theorem B1986623 : Blo 1985435 1986623 := bstep (se 1 (by rfl) ⟨1489967, by rfl⟩ : syracuseStep 1986623 = 2979935) B2979935
theorem B2979941 : Blo 1985435 2979941 := bbase (se 4 (by rfl) ⟨279369, by rfl⟩ : syracuseStep 2979941 = 558739) (by norm_num)
theorem B1986627 : Blo 1985435 1986627 := bstep (se 1 (by rfl) ⟨1489970, by rfl⟩ : syracuseStep 1986627 = 2979941) B2979941
theorem B8601653 : Blo 1985435 8601653 := bbase (se 5 (by rfl) ⟨403202, by rfl⟩ : syracuseStep 8601653 = 806405) (by norm_num)
theorem B5734435 : Blo 1985435 5734435 := bstep (se 1 (by rfl) ⟨4300826, by rfl⟩ : syracuseStep 5734435 = 8601653) B8601653
theorem B7645913 : Blo 1985435 7645913 := bstep (se 2 (by rfl) ⟨2867217, by rfl⟩ : syracuseStep 7645913 = 5734435) B5734435
theorem B5097275 : Blo 1985435 5097275 := bstep (se 1 (by rfl) ⟨3822956, by rfl⟩ : syracuseStep 5097275 = 7645913) B7645913
theorem B3398183 : Blo 1985435 3398183 := bstep (se 1 (by rfl) ⟨2548637, by rfl⟩ : syracuseStep 3398183 = 5097275) B5097275
theorem B2265455 : Blo 1985435 2265455 := bstep (se 1 (by rfl) ⟨1699091, by rfl⟩ : syracuseStep 2265455 = 3398183) B3398183
theorem B6041213 : Blo 1985435 6041213 := bstep (se 3 (by rfl) ⟨1132727, by rfl⟩ : syracuseStep 6041213 = 2265455) B2265455
theorem B4027475 : Blo 1985435 4027475 := bstep (se 1 (by rfl) ⟨3020606, by rfl⟩ : syracuseStep 4027475 = 6041213) B6041213
theorem B2684983 : Blo 1985435 2684983 := bstep (se 1 (by rfl) ⟨2013737, by rfl⟩ : syracuseStep 2684983 = 4027475) B4027475
theorem B3579977 : Blo 1985435 3579977 := bstep (se 2 (by rfl) ⟨1342491, by rfl⟩ : syracuseStep 3579977 = 2684983) B2684983
theorem B9546605 : Blo 1985435 9546605 := bstep (se 3 (by rfl) ⟨1789988, by rfl⟩ : syracuseStep 9546605 = 3579977) B3579977
theorem B6364403 : Blo 1985435 6364403 := bstep (se 1 (by rfl) ⟨4773302, by rfl⟩ : syracuseStep 6364403 = 9546605) B9546605
theorem B4242935 : Blo 1985435 4242935 := bstep (se 1 (by rfl) ⟨3182201, by rfl⟩ : syracuseStep 4242935 = 6364403) B6364403
theorem B2828623 : Blo 1985435 2828623 := bstep (se 1 (by rfl) ⟨2121467, by rfl⟩ : syracuseStep 2828623 = 4242935) B4242935
theorem B3771497 : Blo 1985435 3771497 := bstep (se 2 (by rfl) ⟨1414311, by rfl⟩ : syracuseStep 3771497 = 2828623) B2828623
theorem B2514331 : Blo 1985435 2514331 := bstep (se 1 (by rfl) ⟨1885748, by rfl⟩ : syracuseStep 2514331 = 3771497) B3771497
theorem B3352441 : Blo 1985435 3352441 := bstep (se 2 (by rfl) ⟨1257165, by rfl⟩ : syracuseStep 3352441 = 2514331) B2514331
theorem B4469921 : Blo 1985435 4469921 := bstep (se 2 (by rfl) ⟨1676220, by rfl⟩ : syracuseStep 4469921 = 3352441) B3352441
theorem B2979947 : Blo 1985435 2979947 := bstep (se 1 (by rfl) ⟨2234960, by rfl⟩ : syracuseStep 2979947 = 4469921) B4469921
theorem B1986631 : Blo 1985435 1986631 := bstep (se 1 (by rfl) ⟨1489973, by rfl⟩ : syracuseStep 1986631 = 2979947) B2979947
theorem B2234965 : Blo 1985435 2234965 := bbase (se 8 (by rfl) ⟨13095, by rfl⟩ : syracuseStep 2234965 = 26191) (by norm_num)
theorem B2979953 : Blo 1985435 2979953 := bstep (se 2 (by rfl) ⟨1117482, by rfl⟩ : syracuseStep 2979953 = 2234965) B2234965
theorem B1986635 : Blo 1985435 1986635 := bstep (se 1 (by rfl) ⟨1489976, by rfl⟩ : syracuseStep 1986635 = 2979953) B2979953
theorem B2514341 : Blo 1985435 2514341 := bbase (se 4 (by rfl) ⟨235719, by rfl⟩ : syracuseStep 2514341 = 471439) (by norm_num)
theorem B6704909 : Blo 1985435 6704909 := bstep (se 3 (by rfl) ⟨1257170, by rfl⟩ : syracuseStep 6704909 = 2514341) B2514341
theorem B4469939 : Blo 1985435 4469939 := bstep (se 1 (by rfl) ⟨3352454, by rfl⟩ : syracuseStep 4469939 = 6704909) B6704909
theorem B2979959 : Blo 1985435 2979959 := bstep (se 1 (by rfl) ⟨2234969, by rfl⟩ : syracuseStep 2979959 = 4469939) B4469939
theorem B1986639 : Blo 1985435 1986639 := bstep (se 1 (by rfl) ⟨1489979, by rfl⟩ : syracuseStep 1986639 = 2979959) B2979959
theorem B2979965 : Blo 1985435 2979965 := bbase (se 3 (by rfl) ⟨558743, by rfl⟩ : syracuseStep 2979965 = 1117487) (by norm_num)
theorem B1986643 : Blo 1985435 1986643 := bstep (se 1 (by rfl) ⟨1489982, by rfl⟩ : syracuseStep 1986643 = 2979965) B2979965
theorem B4469957 : Blo 1985435 4469957 := bbase (se 4 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 4469957 = 838117) (by norm_num)
theorem B2979971 : Blo 1985435 2979971 := bstep (se 1 (by rfl) ⟨2234978, by rfl⟩ : syracuseStep 2979971 = 4469957) B4469957
theorem B1986647 : Blo 1985435 1986647 := bstep (se 1 (by rfl) ⟨1489985, by rfl⟩ : syracuseStep 1986647 = 2979971) B2979971
theorem B3580013 : Blo 1985435 3580013 := bbase (se 3 (by rfl) ⟨671252, by rfl⟩ : syracuseStep 3580013 = 1342505) (by norm_num)
theorem B2386675 : Blo 1985435 2386675 := bstep (se 1 (by rfl) ⟨1790006, by rfl⟩ : syracuseStep 2386675 = 3580013) B3580013
theorem B12728933 : Blo 1985435 12728933 := bstep (se 4 (by rfl) ⟨1193337, by rfl⟩ : syracuseStep 12728933 = 2386675) B2386675
theorem B8485955 : Blo 1985435 8485955 := bstep (se 1 (by rfl) ⟨6364466, by rfl⟩ : syracuseStep 8485955 = 12728933) B12728933
theorem B5657303 : Blo 1985435 5657303 := bstep (se 1 (by rfl) ⟨4242977, by rfl⟩ : syracuseStep 5657303 = 8485955) B8485955
theorem B3771535 : Blo 1985435 3771535 := bstep (se 1 (by rfl) ⟨2828651, by rfl⟩ : syracuseStep 3771535 = 5657303) B5657303
theorem B5028713 : Blo 1985435 5028713 := bstep (se 2 (by rfl) ⟨1885767, by rfl⟩ : syracuseStep 5028713 = 3771535) B3771535
theorem B3352475 : Blo 1985435 3352475 := bstep (se 1 (by rfl) ⟨2514356, by rfl⟩ : syracuseStep 3352475 = 5028713) B5028713
theorem B2234983 : Blo 1985435 2234983 := bstep (se 1 (by rfl) ⟨1676237, by rfl⟩ : syracuseStep 2234983 = 3352475) B3352475
theorem B2979977 : Blo 1985435 2979977 := bstep (se 2 (by rfl) ⟨1117491, by rfl⟩ : syracuseStep 2979977 = 2234983) B2234983
theorem B1986651 : Blo 1985435 1986651 := bstep (se 1 (by rfl) ⟨1489988, by rfl⟩ : syracuseStep 1986651 = 2979977) B2979977
theorem B10057445 : Blo 1985435 10057445 := bbase (se 4 (by rfl) ⟨942885, by rfl⟩ : syracuseStep 10057445 = 1885771) (by norm_num)
theorem B6704963 : Blo 1985435 6704963 := bstep (se 1 (by rfl) ⟨5028722, by rfl⟩ : syracuseStep 6704963 = 10057445) B10057445
theorem B4469975 : Blo 1985435 4469975 := bstep (se 1 (by rfl) ⟨3352481, by rfl⟩ : syracuseStep 4469975 = 6704963) B6704963
theorem B2979983 : Blo 1985435 2979983 := bstep (se 1 (by rfl) ⟨2234987, by rfl⟩ : syracuseStep 2979983 = 4469975) B4469975
theorem B1986655 : Blo 1985435 1986655 := bstep (se 1 (by rfl) ⟨1489991, by rfl⟩ : syracuseStep 1986655 = 2979983) B2979983
theorem B2979989 : Blo 1985435 2979989 := bbase (se 6 (by rfl) ⟨69843, by rfl⟩ : syracuseStep 2979989 = 139687) (by norm_num)
theorem B1986659 : Blo 1985435 1986659 := bstep (se 1 (by rfl) ⟨1489994, by rfl⟩ : syracuseStep 1986659 = 2979989) B2979989
theorem B8486005 : Blo 1985435 8486005 := bbase (se 5 (by rfl) ⟨397781, by rfl⟩ : syracuseStep 8486005 = 795563) (by norm_num)
theorem B11314673 : Blo 1985435 11314673 := bstep (se 2 (by rfl) ⟨4243002, by rfl⟩ : syracuseStep 11314673 = 8486005) B8486005
theorem B7543115 : Blo 1985435 7543115 := bstep (se 1 (by rfl) ⟨5657336, by rfl⟩ : syracuseStep 7543115 = 11314673) B11314673
theorem B5028743 : Blo 1985435 5028743 := bstep (se 1 (by rfl) ⟨3771557, by rfl⟩ : syracuseStep 5028743 = 7543115) B7543115
theorem B3352495 : Blo 1985435 3352495 := bstep (se 1 (by rfl) ⟨2514371, by rfl⟩ : syracuseStep 3352495 = 5028743) B5028743
theorem B4469993 : Blo 1985435 4469993 := bstep (se 2 (by rfl) ⟨1676247, by rfl⟩ : syracuseStep 4469993 = 3352495) B3352495
theorem B2979995 : Blo 1985435 2979995 := bstep (se 1 (by rfl) ⟨2234996, by rfl⟩ : syracuseStep 2979995 = 4469993) B4469993
theorem B1986663 : Blo 1985435 1986663 := bstep (se 1 (by rfl) ⟨1489997, by rfl⟩ : syracuseStep 1986663 = 2979995) B2979995
theorem B2235001 : Blo 1985435 2235001 := bbase (se 2 (by rfl) ⟨838125, by rfl⟩ : syracuseStep 2235001 = 1676251) (by norm_num)
theorem B2980001 : Blo 1985435 2980001 := bstep (se 2 (by rfl) ⟨1117500, by rfl⟩ : syracuseStep 2980001 = 2235001) B2235001
theorem B1986667 : Blo 1985435 1986667 := bstep (se 1 (by rfl) ⟨1490000, by rfl⟩ : syracuseStep 1986667 = 2980001) B2980001
theorem B19093589 : Blo 1985435 19093589 := bbase (se 8 (by rfl) ⟨111876, by rfl⟩ : syracuseStep 19093589 = 223753) (by norm_num)
theorem B12729059 : Blo 1985435 12729059 := bstep (se 1 (by rfl) ⟨9546794, by rfl⟩ : syracuseStep 12729059 = 19093589) B19093589
theorem B8486039 : Blo 1985435 8486039 := bstep (se 1 (by rfl) ⟨6364529, by rfl⟩ : syracuseStep 8486039 = 12729059) B12729059
theorem B5657359 : Blo 1985435 5657359 := bstep (se 1 (by rfl) ⟨4243019, by rfl⟩ : syracuseStep 5657359 = 8486039) B8486039
theorem B7543145 : Blo 1985435 7543145 := bstep (se 2 (by rfl) ⟨2828679, by rfl⟩ : syracuseStep 7543145 = 5657359) B5657359
theorem B5028763 : Blo 1985435 5028763 := bstep (se 1 (by rfl) ⟨3771572, by rfl⟩ : syracuseStep 5028763 = 7543145) B7543145
theorem B6705017 : Blo 1985435 6705017 := bstep (se 2 (by rfl) ⟨2514381, by rfl⟩ : syracuseStep 6705017 = 5028763) B5028763
theorem B4470011 : Blo 1985435 4470011 := bstep (se 1 (by rfl) ⟨3352508, by rfl⟩ : syracuseStep 4470011 = 6705017) B6705017
theorem B2980007 : Blo 1985435 2980007 := bstep (se 1 (by rfl) ⟨2235005, by rfl⟩ : syracuseStep 2980007 = 4470011) B4470011
theorem B1986671 : Blo 1985435 1986671 := bstep (se 1 (by rfl) ⟨1490003, by rfl⟩ : syracuseStep 1986671 = 2980007) B2980007
theorem B2980013 : Blo 1985435 2980013 := bbase (se 3 (by rfl) ⟨558752, by rfl⟩ : syracuseStep 2980013 = 1117505) (by norm_num)
theorem B1986675 : Blo 1985435 1986675 := bstep (se 1 (by rfl) ⟨1490006, by rfl⟩ : syracuseStep 1986675 = 2980013) B2980013
theorem B4470029 : Blo 1985435 4470029 := bbase (se 3 (by rfl) ⟨838130, by rfl⟩ : syracuseStep 4470029 = 1676261) (by norm_num)
theorem B2980019 : Blo 1985435 2980019 := bstep (se 1 (by rfl) ⟨2235014, by rfl⟩ : syracuseStep 2980019 = 4470029) B4470029
theorem B1986679 : Blo 1985435 1986679 := bstep (se 1 (by rfl) ⟨1490009, by rfl⟩ : syracuseStep 1986679 = 2980019) B2980019
theorem B2514397 : Blo 1985435 2514397 := bbase (se 3 (by rfl) ⟨471449, by rfl⟩ : syracuseStep 2514397 = 942899) (by norm_num)
theorem B3352529 : Blo 1985435 3352529 := bstep (se 2 (by rfl) ⟨1257198, by rfl⟩ : syracuseStep 3352529 = 2514397) B2514397
theorem B2235019 : Blo 1985435 2235019 := bstep (se 1 (by rfl) ⟨1676264, by rfl⟩ : syracuseStep 2235019 = 3352529) B3352529
theorem B2980025 : Blo 1985435 2980025 := bstep (se 2 (by rfl) ⟨1117509, by rfl⟩ : syracuseStep 2980025 = 2235019) B2235019
theorem B1986683 : Blo 1985435 1986683 := bstep (se 1 (by rfl) ⟨1490012, by rfl⟩ : syracuseStep 1986683 = 2980025) B2980025
theorem B16972213 : Blo 1985435 16972213 := bbase (se 5 (by rfl) ⟨795572, by rfl⟩ : syracuseStep 16972213 = 1591145) (by norm_num)
theorem B22629617 : Blo 1985435 22629617 := bstep (se 2 (by rfl) ⟨8486106, by rfl⟩ : syracuseStep 22629617 = 16972213) B16972213
theorem B15086411 : Blo 1985435 15086411 := bstep (se 1 (by rfl) ⟨11314808, by rfl⟩ : syracuseStep 15086411 = 22629617) B22629617
theorem B10057607 : Blo 1985435 10057607 := bstep (se 1 (by rfl) ⟨7543205, by rfl⟩ : syracuseStep 10057607 = 15086411) B15086411
theorem B6705071 : Blo 1985435 6705071 := bstep (se 1 (by rfl) ⟨5028803, by rfl⟩ : syracuseStep 6705071 = 10057607) B10057607
theorem B4470047 : Blo 1985435 4470047 := bstep (se 1 (by rfl) ⟨3352535, by rfl⟩ : syracuseStep 4470047 = 6705071) B6705071
theorem B2980031 : Blo 1985435 2980031 := bstep (se 1 (by rfl) ⟨2235023, by rfl⟩ : syracuseStep 2980031 = 4470047) B4470047
theorem B1986687 : Blo 1985435 1986687 := bstep (se 1 (by rfl) ⟨1490015, by rfl⟩ : syracuseStep 1986687 = 2980031) B2980031
theorem B2980037 : Blo 1985435 2980037 := bbase (se 4 (by rfl) ⟨279378, by rfl⟩ : syracuseStep 2980037 = 558757) (by norm_num)
theorem B1986691 : Blo 1985435 1986691 := bstep (se 1 (by rfl) ⟨1490018, by rfl⟩ : syracuseStep 1986691 = 2980037) B2980037
theorem B3352549 : Blo 1985435 3352549 := bbase (se 4 (by rfl) ⟨314301, by rfl⟩ : syracuseStep 3352549 = 628603) (by norm_num)
theorem B4470065 : Blo 1985435 4470065 := bstep (se 2 (by rfl) ⟨1676274, by rfl⟩ : syracuseStep 4470065 = 3352549) B3352549
theorem B2980043 : Blo 1985435 2980043 := bstep (se 1 (by rfl) ⟨2235032, by rfl⟩ : syracuseStep 2980043 = 4470065) B4470065
theorem B1986695 : Blo 1985435 1986695 := bstep (se 1 (by rfl) ⟨1490021, by rfl⟩ : syracuseStep 1986695 = 2980043) B2980043
theorem B2235037 : Blo 1985435 2235037 := bbase (se 3 (by rfl) ⟨419069, by rfl⟩ : syracuseStep 2235037 = 838139) (by norm_num)
theorem B2980049 : Blo 1985435 2980049 := bstep (se 2 (by rfl) ⟨1117518, by rfl⟩ : syracuseStep 2980049 = 2235037) B2235037
theorem B1986699 : Blo 1985435 1986699 := bstep (se 1 (by rfl) ⟨1490024, by rfl⟩ : syracuseStep 1986699 = 2980049) B2980049
theorem B6705125 : Blo 1985435 6705125 := bbase (se 4 (by rfl) ⟨628605, by rfl⟩ : syracuseStep 6705125 = 1257211) (by norm_num)
theorem B4470083 : Blo 1985435 4470083 := bstep (se 1 (by rfl) ⟨3352562, by rfl⟩ : syracuseStep 4470083 = 6705125) B6705125
theorem B2980055 : Blo 1985435 2980055 := bstep (se 1 (by rfl) ⟨2235041, by rfl⟩ : syracuseStep 2980055 = 4470083) B4470083
theorem B1986703 : Blo 1985435 1986703 := bstep (se 1 (by rfl) ⟨1490027, by rfl⟩ : syracuseStep 1986703 = 2980055) B2980055
theorem B2980061 : Blo 1985435 2980061 := bbase (se 3 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 2980061 = 1117523) (by norm_num)
theorem B1986707 : Blo 1985435 1986707 := bstep (se 1 (by rfl) ⟨1490030, by rfl⟩ : syracuseStep 1986707 = 2980061) B2980061
theorem B4470101 : Blo 1985435 4470101 := bbase (se 13 (by rfl) ⟨818, by rfl⟩ : syracuseStep 4470101 = 1637) (by norm_num)
theorem B2980067 : Blo 1985435 2980067 := bstep (se 1 (by rfl) ⟨2235050, by rfl⟩ : syracuseStep 2980067 = 4470101) B4470101
theorem B1986711 : Blo 1985435 1986711 := bstep (se 1 (by rfl) ⟨1490033, by rfl⟩ : syracuseStep 1986711 = 2980067) B2980067
theorem B2121557 : Blo 1985435 2121557 := bbase (se 9 (by rfl) ⟨6215, by rfl⟩ : syracuseStep 2121557 = 12431) (by norm_num)
theorem B5657485 : Blo 1985435 5657485 := bstep (se 3 (by rfl) ⟨1060778, by rfl⟩ : syracuseStep 5657485 = 2121557) B2121557
theorem B7543313 : Blo 1985435 7543313 := bstep (se 2 (by rfl) ⟨2828742, by rfl⟩ : syracuseStep 7543313 = 5657485) B5657485
theorem B5028875 : Blo 1985435 5028875 := bstep (se 1 (by rfl) ⟨3771656, by rfl⟩ : syracuseStep 5028875 = 7543313) B7543313
theorem B3352583 : Blo 1985435 3352583 := bstep (se 1 (by rfl) ⟨2514437, by rfl⟩ : syracuseStep 3352583 = 5028875) B5028875
theorem B2235055 : Blo 1985435 2235055 := bstep (se 1 (by rfl) ⟨1676291, by rfl⟩ : syracuseStep 2235055 = 3352583) B3352583
theorem B2980073 : Blo 1985435 2980073 := bstep (se 2 (by rfl) ⟨1117527, by rfl⟩ : syracuseStep 2980073 = 2235055) B2235055
theorem B1986715 : Blo 1985435 1986715 := bstep (se 1 (by rfl) ⟨1490036, by rfl⟩ : syracuseStep 1986715 = 2980073) B2980073
theorem B6041477 : Blo 1985435 6041477 := bbase (se 4 (by rfl) ⟨566388, by rfl⟩ : syracuseStep 6041477 = 1132777) (by norm_num)
theorem B4027651 : Blo 1985435 4027651 := bstep (se 1 (by rfl) ⟨3020738, by rfl⟩ : syracuseStep 4027651 = 6041477) B6041477
theorem B21480805 : Blo 1985435 21480805 := bstep (se 4 (by rfl) ⟨2013825, by rfl⟩ : syracuseStep 21480805 = 4027651) B4027651
theorem B28641073 : Blo 1985435 28641073 := bstep (se 2 (by rfl) ⟨10740402, by rfl⟩ : syracuseStep 28641073 = 21480805) B21480805
theorem B38188097 : Blo 1985435 38188097 := bstep (se 2 (by rfl) ⟨14320536, by rfl⟩ : syracuseStep 38188097 = 28641073) B28641073
theorem B25458731 : Blo 1985435 25458731 := bstep (se 1 (by rfl) ⟨19094048, by rfl⟩ : syracuseStep 25458731 = 38188097) B38188097
theorem B16972487 : Blo 1985435 16972487 := bstep (se 1 (by rfl) ⟨12729365, by rfl⟩ : syracuseStep 16972487 = 25458731) B25458731
theorem B11314991 : Blo 1985435 11314991 := bstep (se 1 (by rfl) ⟨8486243, by rfl⟩ : syracuseStep 11314991 = 16972487) B16972487
theorem B7543327 : Blo 1985435 7543327 := bstep (se 1 (by rfl) ⟨5657495, by rfl⟩ : syracuseStep 7543327 = 11314991) B11314991
theorem B10057769 : Blo 1985435 10057769 := bstep (se 2 (by rfl) ⟨3771663, by rfl⟩ : syracuseStep 10057769 = 7543327) B7543327
theorem B6705179 : Blo 1985435 6705179 := bstep (se 1 (by rfl) ⟨5028884, by rfl⟩ : syracuseStep 6705179 = 10057769) B10057769
theorem B4470119 : Blo 1985435 4470119 := bstep (se 1 (by rfl) ⟨3352589, by rfl⟩ : syracuseStep 4470119 = 6705179) B6705179
theorem B2980079 : Blo 1985435 2980079 := bstep (se 1 (by rfl) ⟨2235059, by rfl⟩ : syracuseStep 2980079 = 4470119) B4470119
theorem B1986719 : Blo 1985435 1986719 := bstep (se 1 (by rfl) ⟨1490039, by rfl⟩ : syracuseStep 1986719 = 2980079) B2980079
theorem B2980085 : Blo 1985435 2980085 := bbase (se 5 (by rfl) ⟨139691, by rfl⟩ : syracuseStep 2980085 = 279383) (by norm_num)
theorem B1986723 : Blo 1985435 1986723 := bstep (se 1 (by rfl) ⟨1490042, by rfl⟩ : syracuseStep 1986723 = 2980085) B2980085
theorem B14320597 : Blo 1985435 14320597 := bbase (se 7 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 14320597 = 335639) (by norm_num)
theorem B19094129 : Blo 1985435 19094129 := bstep (se 2 (by rfl) ⟨7160298, by rfl⟩ : syracuseStep 19094129 = 14320597) B14320597
theorem B12729419 : Blo 1985435 12729419 := bstep (se 1 (by rfl) ⟨9547064, by rfl⟩ : syracuseStep 12729419 = 19094129) B19094129
theorem B8486279 : Blo 1985435 8486279 := bstep (se 1 (by rfl) ⟨6364709, by rfl⟩ : syracuseStep 8486279 = 12729419) B12729419
theorem B5657519 : Blo 1985435 5657519 := bstep (se 1 (by rfl) ⟨4243139, by rfl⟩ : syracuseStep 5657519 = 8486279) B8486279
theorem B3771679 : Blo 1985435 3771679 := bstep (se 1 (by rfl) ⟨2828759, by rfl⟩ : syracuseStep 3771679 = 5657519) B5657519
theorem B5028905 : Blo 1985435 5028905 := bstep (se 2 (by rfl) ⟨1885839, by rfl⟩ : syracuseStep 5028905 = 3771679) B3771679
theorem B3352603 : Blo 1985435 3352603 := bstep (se 1 (by rfl) ⟨2514452, by rfl⟩ : syracuseStep 3352603 = 5028905) B5028905
theorem B4470137 : Blo 1985435 4470137 := bstep (se 2 (by rfl) ⟨1676301, by rfl⟩ : syracuseStep 4470137 = 3352603) B3352603
theorem B2980091 : Blo 1985435 2980091 := bstep (se 1 (by rfl) ⟨2235068, by rfl⟩ : syracuseStep 2980091 = 4470137) B4470137
theorem B1986727 : Blo 1985435 1986727 := bstep (se 1 (by rfl) ⟨1490045, by rfl⟩ : syracuseStep 1986727 = 2980091) B2980091
theorem B2235073 : Blo 1985435 2235073 := bbase (se 2 (by rfl) ⟨838152, by rfl⟩ : syracuseStep 2235073 = 1676305) (by norm_num)
theorem B2980097 : Blo 1985435 2980097 := bstep (se 2 (by rfl) ⟨1117536, by rfl⟩ : syracuseStep 2980097 = 2235073) B2235073
theorem B1986731 : Blo 1985435 1986731 := bstep (se 1 (by rfl) ⟨1490048, by rfl⟩ : syracuseStep 1986731 = 2980097) B2980097
theorem B5028925 : Blo 1985435 5028925 := bbase (se 3 (by rfl) ⟨942923, by rfl⟩ : syracuseStep 5028925 = 1885847) (by norm_num)
theorem B6705233 : Blo 1985435 6705233 := bstep (se 2 (by rfl) ⟨2514462, by rfl⟩ : syracuseStep 6705233 = 5028925) B5028925
theorem B4470155 : Blo 1985435 4470155 := bstep (se 1 (by rfl) ⟨3352616, by rfl⟩ : syracuseStep 4470155 = 6705233) B6705233
theorem B2980103 : Blo 1985435 2980103 := bstep (se 1 (by rfl) ⟨2235077, by rfl⟩ : syracuseStep 2980103 = 4470155) B4470155
theorem B1986735 : Blo 1985435 1986735 := bstep (se 1 (by rfl) ⟨1490051, by rfl⟩ : syracuseStep 1986735 = 2980103) B2980103
theorem B2980109 : Blo 1985435 2980109 := bbase (se 3 (by rfl) ⟨558770, by rfl⟩ : syracuseStep 2980109 = 1117541) (by norm_num)
theorem B1986739 : Blo 1985435 1986739 := bstep (se 1 (by rfl) ⟨1490054, by rfl⟩ : syracuseStep 1986739 = 2980109) B2980109
theorem B4470173 : Blo 1985435 4470173 := bbase (se 3 (by rfl) ⟨838157, by rfl⟩ : syracuseStep 4470173 = 1676315) (by norm_num)
theorem B2980115 : Blo 1985435 2980115 := bstep (se 1 (by rfl) ⟨2235086, by rfl⟩ : syracuseStep 2980115 = 4470173) B4470173
theorem B1986743 : Blo 1985435 1986743 := bstep (se 1 (by rfl) ⟨1490057, by rfl⟩ : syracuseStep 1986743 = 2980115) B2980115
theorem B3352637 : Blo 1985435 3352637 := bbase (se 3 (by rfl) ⟨628619, by rfl⟩ : syracuseStep 3352637 = 1257239) (by norm_num)
theorem B2235091 : Blo 1985435 2235091 := bstep (se 1 (by rfl) ⟨1676318, by rfl⟩ : syracuseStep 2235091 = 3352637) B3352637
theorem B2980121 : Blo 1985435 2980121 := bstep (se 2 (by rfl) ⟨1117545, by rfl⟩ : syracuseStep 2980121 = 2235091) B2235091
theorem B1986747 : Blo 1985435 1986747 := bstep (se 1 (by rfl) ⟨1490060, by rfl⟩ : syracuseStep 1986747 = 2980121) B2980121
theorem B3020789 : Blo 1985435 3020789 := bbase (se 5 (by rfl) ⟨141599, by rfl⟩ : syracuseStep 3020789 = 283199) (by norm_num)
theorem B2013859 : Blo 1985435 2013859 := bstep (se 1 (by rfl) ⟨1510394, by rfl⟩ : syracuseStep 2013859 = 3020789) B3020789
theorem B2685145 : Blo 1985435 2685145 := bstep (se 2 (by rfl) ⟨1006929, by rfl⟩ : syracuseStep 2685145 = 2013859) B2013859
theorem B3580193 : Blo 1985435 3580193 := bstep (se 2 (by rfl) ⟨1342572, by rfl⟩ : syracuseStep 3580193 = 2685145) B2685145
theorem B2386795 : Blo 1985435 2386795 := bstep (se 1 (by rfl) ⟨1790096, by rfl⟩ : syracuseStep 2386795 = 3580193) B3580193
theorem B3182393 : Blo 1985435 3182393 := bstep (se 2 (by rfl) ⟨1193397, by rfl⟩ : syracuseStep 3182393 = 2386795) B2386795
theorem B2121595 : Blo 1985435 2121595 := bstep (se 1 (by rfl) ⟨1591196, by rfl⟩ : syracuseStep 2121595 = 3182393) B3182393
theorem B11315173 : Blo 1985435 11315173 := bstep (se 4 (by rfl) ⟨1060797, by rfl⟩ : syracuseStep 11315173 = 2121595) B2121595
theorem B15086897 : Blo 1985435 15086897 := bstep (se 2 (by rfl) ⟨5657586, by rfl⟩ : syracuseStep 15086897 = 11315173) B11315173
theorem B10057931 : Blo 1985435 10057931 := bstep (se 1 (by rfl) ⟨7543448, by rfl⟩ : syracuseStep 10057931 = 15086897) B15086897
theorem B6705287 : Blo 1985435 6705287 := bstep (se 1 (by rfl) ⟨5028965, by rfl⟩ : syracuseStep 6705287 = 10057931) B10057931
theorem B4470191 : Blo 1985435 4470191 := bstep (se 1 (by rfl) ⟨3352643, by rfl⟩ : syracuseStep 4470191 = 6705287) B6705287
theorem B2980127 : Blo 1985435 2980127 := bstep (se 1 (by rfl) ⟨2235095, by rfl⟩ : syracuseStep 2980127 = 4470191) B4470191
theorem B1986751 : Blo 1985435 1986751 := bstep (se 1 (by rfl) ⟨1490063, by rfl⟩ : syracuseStep 1986751 = 2980127) B2980127
theorem B2980133 : Blo 1985435 2980133 := bbase (se 4 (by rfl) ⟨279387, by rfl⟩ : syracuseStep 2980133 = 558775) (by norm_num)
theorem B1986755 : Blo 1985435 1986755 := bstep (se 1 (by rfl) ⟨1490066, by rfl⟩ : syracuseStep 1986755 = 2980133) B2980133
theorem B2514493 : Blo 1985435 2514493 := bbase (se 3 (by rfl) ⟨471467, by rfl⟩ : syracuseStep 2514493 = 942935) (by norm_num)
theorem B3352657 : Blo 1985435 3352657 := bstep (se 2 (by rfl) ⟨1257246, by rfl⟩ : syracuseStep 3352657 = 2514493) B2514493
theorem B4470209 : Blo 1985435 4470209 := bstep (se 2 (by rfl) ⟨1676328, by rfl⟩ : syracuseStep 4470209 = 3352657) B3352657
theorem B2980139 : Blo 1985435 2980139 := bstep (se 1 (by rfl) ⟨2235104, by rfl⟩ : syracuseStep 2980139 = 4470209) B4470209
theorem B1986759 : Blo 1985435 1986759 := bstep (se 1 (by rfl) ⟨1490069, by rfl⟩ : syracuseStep 1986759 = 2980139) B2980139
theorem B2235109 : Blo 1985435 2235109 := bbase (se 4 (by rfl) ⟨209541, by rfl⟩ : syracuseStep 2235109 = 419083) (by norm_num)
theorem B2980145 : Blo 1985435 2980145 := bstep (se 2 (by rfl) ⟨1117554, by rfl⟩ : syracuseStep 2980145 = 2235109) B2235109
theorem B1986763 : Blo 1985435 1986763 := bstep (se 1 (by rfl) ⟨1490072, by rfl⟩ : syracuseStep 1986763 = 2980145) B2980145
theorem B4773629 : Blo 1985435 4773629 := bbase (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) (by norm_num)
theorem B3182419 : Blo 1985435 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B4243225 : Blo 1985435 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B5657633 : Blo 1985435 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B3771755 : Blo 1985435 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B2514503 : Blo 1985435 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B6705341 : Blo 1985435 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B4470227 : Blo 1985435 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B2980151 : Blo 1985435 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B1986767 : Blo 1985435 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B2980157 : Blo 1985435 2980157 := bbase (se 3 (by rfl) ⟨558779, by rfl⟩ : syracuseStep 2980157 = 1117559) (by norm_num)
theorem B1986771 : Blo 1985435 1986771 := bstep (se 1 (by rfl) ⟨1490078, by rfl⟩ : syracuseStep 1986771 = 2980157) B2980157
theorem B4470245 : Blo 1985435 4470245 := bbase (se 4 (by rfl) ⟨419085, by rfl⟩ : syracuseStep 4470245 = 838171) (by norm_num)
theorem B2980163 : Blo 1985435 2980163 := bstep (se 1 (by rfl) ⟨2235122, by rfl⟩ : syracuseStep 2980163 = 4470245) B4470245
theorem B1986775 : Blo 1985435 1986775 := bstep (se 1 (by rfl) ⟨1490081, by rfl⟩ : syracuseStep 1986775 = 2980163) B2980163
theorem B5029037 : Blo 1985435 5029037 := bbase (se 3 (by rfl) ⟨942944, by rfl⟩ : syracuseStep 5029037 = 1885889) (by norm_num)
theorem B3352691 : Blo 1985435 3352691 := bstep (se 1 (by rfl) ⟨2514518, by rfl⟩ : syracuseStep 3352691 = 5029037) B5029037
theorem B2235127 : Blo 1985435 2235127 := bstep (se 1 (by rfl) ⟨1676345, by rfl⟩ : syracuseStep 2235127 = 3352691) B3352691
theorem B2980169 : Blo 1985435 2980169 := bstep (se 2 (by rfl) ⟨1117563, by rfl⟩ : syracuseStep 2980169 = 2235127) B2235127
theorem B1986779 : Blo 1985435 1986779 := bstep (se 1 (by rfl) ⟨1490084, by rfl⟩ : syracuseStep 1986779 = 2980169) B2980169
theorem B7160501 : Blo 1985435 7160501 := bbase (se 5 (by rfl) ⟨335648, by rfl⟩ : syracuseStep 7160501 = 671297) (by norm_num)
theorem B4773667 : Blo 1985435 4773667 := bstep (se 1 (by rfl) ⟨3580250, by rfl⟩ : syracuseStep 4773667 = 7160501) B7160501
theorem B6364889 : Blo 1985435 6364889 := bstep (se 2 (by rfl) ⟨2386833, by rfl⟩ : syracuseStep 6364889 = 4773667) B4773667
theorem B4243259 : Blo 1985435 4243259 := bstep (se 1 (by rfl) ⟨3182444, by rfl⟩ : syracuseStep 4243259 = 6364889) B6364889
theorem B2828839 : Blo 1985435 2828839 := bstep (se 1 (by rfl) ⟨2121629, by rfl⟩ : syracuseStep 2828839 = 4243259) B4243259
theorem B3771785 : Blo 1985435 3771785 := bstep (se 2 (by rfl) ⟨1414419, by rfl⟩ : syracuseStep 3771785 = 2828839) B2828839
theorem B10058093 : Blo 1985435 10058093 := bstep (se 3 (by rfl) ⟨1885892, by rfl⟩ : syracuseStep 10058093 = 3771785) B3771785
theorem B6705395 : Blo 1985435 6705395 := bstep (se 1 (by rfl) ⟨5029046, by rfl⟩ : syracuseStep 6705395 = 10058093) B10058093
theorem B4470263 : Blo 1985435 4470263 := bstep (se 1 (by rfl) ⟨3352697, by rfl⟩ : syracuseStep 4470263 = 6705395) B6705395
theorem B2980175 : Blo 1985435 2980175 := bstep (se 1 (by rfl) ⟨2235131, by rfl⟩ : syracuseStep 2980175 = 4470263) B4470263
theorem B1986783 : Blo 1985435 1986783 := bstep (se 1 (by rfl) ⟨1490087, by rfl⟩ : syracuseStep 1986783 = 2980175) B2980175
theorem B2980181 : Blo 1985435 2980181 := bbase (se 10 (by rfl) ⟨4365, by rfl⟩ : syracuseStep 2980181 = 8731) (by norm_num)
theorem B1986787 : Blo 1985435 1986787 := bstep (se 1 (by rfl) ⟨1490090, by rfl⟩ : syracuseStep 1986787 = 2980181) B2980181
theorem B5657701 : Blo 1985435 5657701 := bbase (se 4 (by rfl) ⟨530409, by rfl⟩ : syracuseStep 5657701 = 1060819) (by norm_num)
theorem B7543601 : Blo 1985435 7543601 := bstep (se 2 (by rfl) ⟨2828850, by rfl⟩ : syracuseStep 7543601 = 5657701) B5657701
theorem B5029067 : Blo 1985435 5029067 := bstep (se 1 (by rfl) ⟨3771800, by rfl⟩ : syracuseStep 5029067 = 7543601) B7543601
theorem B3352711 : Blo 1985435 3352711 := bstep (se 1 (by rfl) ⟨2514533, by rfl⟩ : syracuseStep 3352711 = 5029067) B5029067
theorem B4470281 : Blo 1985435 4470281 := bstep (se 2 (by rfl) ⟨1676355, by rfl⟩ : syracuseStep 4470281 = 3352711) B3352711
theorem B2980187 : Blo 1985435 2980187 := bstep (se 1 (by rfl) ⟨2235140, by rfl⟩ : syracuseStep 2980187 = 4470281) B4470281
theorem B1986791 : Blo 1985435 1986791 := bstep (se 1 (by rfl) ⟨1490093, by rfl⟩ : syracuseStep 1986791 = 2980187) B2980187
theorem B2235145 : Blo 1985435 2235145 := bbase (se 2 (by rfl) ⟨838179, by rfl⟩ : syracuseStep 2235145 = 1676359) (by norm_num)
theorem B2980193 : Blo 1985435 2980193 := bstep (se 2 (by rfl) ⟨1117572, by rfl⟩ : syracuseStep 2980193 = 2235145) B2235145
theorem B1986795 : Blo 1985435 1986795 := bstep (se 1 (by rfl) ⟨1490096, by rfl⟩ : syracuseStep 1986795 = 2980193) B2980193
theorem B3020861 : Blo 1985435 3020861 := bbase (se 3 (by rfl) ⟨566411, by rfl⟩ : syracuseStep 3020861 = 1132823) (by norm_num)
theorem B2013907 : Blo 1985435 2013907 := bstep (se 1 (by rfl) ⟨1510430, by rfl⟩ : syracuseStep 2013907 = 3020861) B3020861
theorem B2685209 : Blo 1985435 2685209 := bstep (se 2 (by rfl) ⟨1006953, by rfl⟩ : syracuseStep 2685209 = 2013907) B2013907
theorem B7160557 : Blo 1985435 7160557 := bstep (se 3 (by rfl) ⟨1342604, by rfl⟩ : syracuseStep 7160557 = 2685209) B2685209
theorem B9547409 : Blo 1985435 9547409 := bstep (se 2 (by rfl) ⟨3580278, by rfl⟩ : syracuseStep 9547409 = 7160557) B7160557
theorem B25459757 : Blo 1985435 25459757 := bstep (se 3 (by rfl) ⟨4773704, by rfl⟩ : syracuseStep 25459757 = 9547409) B9547409
theorem B16973171 : Blo 1985435 16973171 := bstep (se 1 (by rfl) ⟨12729878, by rfl⟩ : syracuseStep 16973171 = 25459757) B25459757
theorem B11315447 : Blo 1985435 11315447 := bstep (se 1 (by rfl) ⟨8486585, by rfl⟩ : syracuseStep 11315447 = 16973171) B16973171
theorem B7543631 : Blo 1985435 7543631 := bstep (se 1 (by rfl) ⟨5657723, by rfl⟩ : syracuseStep 7543631 = 11315447) B11315447
theorem B5029087 : Blo 1985435 5029087 := bstep (se 1 (by rfl) ⟨3771815, by rfl⟩ : syracuseStep 5029087 = 7543631) B7543631
theorem B6705449 : Blo 1985435 6705449 := bstep (se 2 (by rfl) ⟨2514543, by rfl⟩ : syracuseStep 6705449 = 5029087) B5029087
theorem B4470299 : Blo 1985435 4470299 := bstep (se 1 (by rfl) ⟨3352724, by rfl⟩ : syracuseStep 4470299 = 6705449) B6705449
theorem B2980199 : Blo 1985435 2980199 := bstep (se 1 (by rfl) ⟨2235149, by rfl⟩ : syracuseStep 2980199 = 4470299) B4470299
theorem B1986799 : Blo 1985435 1986799 := bstep (se 1 (by rfl) ⟨1490099, by rfl⟩ : syracuseStep 1986799 = 2980199) B2980199
theorem B2980205 : Blo 1985435 2980205 := bbase (se 3 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 2980205 = 1117577) (by norm_num)
theorem B1986803 : Blo 1985435 1986803 := bstep (se 1 (by rfl) ⟨1490102, by rfl⟩ : syracuseStep 1986803 = 2980205) B2980205
theorem B4470317 : Blo 1985435 4470317 := bbase (se 3 (by rfl) ⟨838184, by rfl⟩ : syracuseStep 4470317 = 1676369) (by norm_num)
theorem B2980211 : Blo 1985435 2980211 := bstep (se 1 (by rfl) ⟨2235158, by rfl⟩ : syracuseStep 2980211 = 4470317) B4470317
theorem B1986807 : Blo 1985435 1986807 := bstep (se 1 (by rfl) ⟨1490105, by rfl⟩ : syracuseStep 1986807 = 2980211) B2980211
theorem B4301213 : Blo 1985435 4301213 := bbase (se 3 (by rfl) ⟨806477, by rfl⟩ : syracuseStep 4301213 = 1612955) (by norm_num)
theorem B45879605 : Blo 1985435 45879605 := bstep (se 5 (by rfl) ⟨2150606, by rfl⟩ : syracuseStep 45879605 = 4301213) B4301213
theorem B30586403 : Blo 1985435 30586403 := bstep (se 1 (by rfl) ⟨22939802, by rfl⟩ : syracuseStep 30586403 = 45879605) B45879605
theorem B20390935 : Blo 1985435 20390935 := bstep (se 1 (by rfl) ⟨15293201, by rfl⟩ : syracuseStep 20390935 = 30586403) B30586403
theorem B27187913 : Blo 1985435 27187913 := bstep (se 2 (by rfl) ⟨10195467, by rfl⟩ : syracuseStep 27187913 = 20390935) B20390935
theorem B72501101 : Blo 1985435 72501101 := bstep (se 3 (by rfl) ⟨13593956, by rfl⟩ : syracuseStep 72501101 = 27187913) B27187913
theorem B48334067 : Blo 1985435 48334067 := bstep (se 1 (by rfl) ⟨36250550, by rfl⟩ : syracuseStep 48334067 = 72501101) B72501101
theorem B32222711 : Blo 1985435 32222711 := bstep (se 1 (by rfl) ⟨24167033, by rfl⟩ : syracuseStep 32222711 = 48334067) B48334067
theorem B21481807 : Blo 1985435 21481807 := bstep (se 1 (by rfl) ⟨16111355, by rfl⟩ : syracuseStep 21481807 = 32222711) B32222711
theorem B28642409 : Blo 1985435 28642409 := bstep (se 2 (by rfl) ⟨10740903, by rfl⟩ : syracuseStep 28642409 = 21481807) B21481807
theorem B19094939 : Blo 1985435 19094939 := bstep (se 1 (by rfl) ⟨14321204, by rfl⟩ : syracuseStep 19094939 = 28642409) B28642409
theorem B12729959 : Blo 1985435 12729959 := bstep (se 1 (by rfl) ⟨9547469, by rfl⟩ : syracuseStep 12729959 = 19094939) B19094939
theorem B8486639 : Blo 1985435 8486639 := bstep (se 1 (by rfl) ⟨6364979, by rfl⟩ : syracuseStep 8486639 = 12729959) B12729959
theorem B5657759 : Blo 1985435 5657759 := bstep (se 1 (by rfl) ⟨4243319, by rfl⟩ : syracuseStep 5657759 = 8486639) B8486639
theorem B3771839 : Blo 1985435 3771839 := bstep (se 1 (by rfl) ⟨2828879, by rfl⟩ : syracuseStep 3771839 = 5657759) B5657759
theorem B2514559 : Blo 1985435 2514559 := bstep (se 1 (by rfl) ⟨1885919, by rfl⟩ : syracuseStep 2514559 = 3771839) B3771839
theorem B3352745 : Blo 1985435 3352745 := bstep (se 2 (by rfl) ⟨1257279, by rfl⟩ : syracuseStep 3352745 = 2514559) B2514559
theorem B2235163 : Blo 1985435 2235163 := bstep (se 1 (by rfl) ⟨1676372, by rfl⟩ : syracuseStep 2235163 = 3352745) B3352745
theorem B2980217 : Blo 1985435 2980217 := bstep (se 2 (by rfl) ⟨1117581, by rfl⟩ : syracuseStep 2980217 = 2235163) B2235163
theorem B1986811 : Blo 1985435 1986811 := bstep (se 1 (by rfl) ⟨1490108, by rfl⟩ : syracuseStep 1986811 = 2980217) B2980217
theorem B5237797 : Blo 1985435 5237797 := bbase (se 4 (by rfl) ⟨491043, by rfl⟩ : syracuseStep 5237797 = 982087) (by norm_num)
theorem B6983729 : Blo 1985435 6983729 := bstep (se 2 (by rfl) ⟨2618898, by rfl⟩ : syracuseStep 6983729 = 5237797) B5237797
theorem B4655819 : Blo 1985435 4655819 := bstep (se 1 (by rfl) ⟨3491864, by rfl⟩ : syracuseStep 4655819 = 6983729) B6983729
theorem B3103879 : Blo 1985435 3103879 := bstep (se 1 (by rfl) ⟨2327909, by rfl⟩ : syracuseStep 3103879 = 4655819) B4655819
theorem B4138505 : Blo 1985435 4138505 := bstep (se 2 (by rfl) ⟨1551939, by rfl⟩ : syracuseStep 4138505 = 3103879) B3103879
theorem B2759003 : Blo 1985435 2759003 := bstep (se 1 (by rfl) ⟨2069252, by rfl⟩ : syracuseStep 2759003 = 4138505) B4138505
theorem B29429365 : Blo 1985435 29429365 := bstep (se 5 (by rfl) ⟨1379501, by rfl⟩ : syracuseStep 29429365 = 2759003) B2759003
theorem B39239153 : Blo 1985435 39239153 := bstep (se 2 (by rfl) ⟨14714682, by rfl⟩ : syracuseStep 39239153 = 29429365) B29429365
theorem B26159435 : Blo 1985435 26159435 := bstep (se 1 (by rfl) ⟨19619576, by rfl⟩ : syracuseStep 26159435 = 39239153) B39239153
theorem B17439623 : Blo 1985435 17439623 := bstep (se 1 (by rfl) ⟨13079717, by rfl⟩ : syracuseStep 17439623 = 26159435) B26159435
theorem B11626415 : Blo 1985435 11626415 := bstep (se 1 (by rfl) ⟨8719811, by rfl⟩ : syracuseStep 11626415 = 17439623) B17439623
theorem B7750943 : Blo 1985435 7750943 := bstep (se 1 (by rfl) ⟨5813207, by rfl⟩ : syracuseStep 7750943 = 11626415) B11626415
theorem B5167295 : Blo 1985435 5167295 := bstep (se 1 (by rfl) ⟨3875471, by rfl⟩ : syracuseStep 5167295 = 7750943) B7750943
theorem B3444863 : Blo 1985435 3444863 := bstep (se 1 (by rfl) ⟨2583647, by rfl⟩ : syracuseStep 3444863 = 5167295) B5167295
theorem B9186301 : Blo 1985435 9186301 := bstep (se 3 (by rfl) ⟨1722431, by rfl⟩ : syracuseStep 9186301 = 3444863) B3444863
theorem B12248401 : Blo 1985435 12248401 := bstep (se 2 (by rfl) ⟨4593150, by rfl⟩ : syracuseStep 12248401 = 9186301) B9186301
theorem B16331201 : Blo 1985435 16331201 := bstep (se 2 (by rfl) ⟨6124200, by rfl⟩ : syracuseStep 16331201 = 12248401) B12248401
theorem B10887467 : Blo 1985435 10887467 := bstep (se 1 (by rfl) ⟨8165600, by rfl⟩ : syracuseStep 10887467 = 16331201) B16331201
theorem B29033245 : Blo 1985435 29033245 := bstep (se 3 (by rfl) ⟨5443733, by rfl⟩ : syracuseStep 29033245 = 10887467) B10887467
theorem B38710993 : Blo 1985435 38710993 := bstep (se 2 (by rfl) ⟨14516622, by rfl⟩ : syracuseStep 38710993 = 29033245) B29033245
theorem B51614657 : Blo 1985435 51614657 := bstep (se 2 (by rfl) ⟨19355496, by rfl⟩ : syracuseStep 51614657 = 38710993) B38710993
theorem B34409771 : Blo 1985435 34409771 := bstep (se 1 (by rfl) ⟨25807328, by rfl⟩ : syracuseStep 34409771 = 51614657) B51614657
theorem B22939847 : Blo 1985435 22939847 := bstep (se 1 (by rfl) ⟨17204885, by rfl⟩ : syracuseStep 22939847 = 34409771) B34409771
theorem B15293231 : Blo 1985435 15293231 := bstep (se 1 (by rfl) ⟨11469923, by rfl⟩ : syracuseStep 15293231 = 22939847) B22939847
theorem B10195487 : Blo 1985435 10195487 := bstep (se 1 (by rfl) ⟨7646615, by rfl⟩ : syracuseStep 10195487 = 15293231) B15293231
theorem B6796991 : Blo 1985435 6796991 := bstep (se 1 (by rfl) ⟨5097743, by rfl⟩ : syracuseStep 6796991 = 10195487) B10195487
theorem B18125309 : Blo 1985435 18125309 := bstep (se 3 (by rfl) ⟨3398495, by rfl⟩ : syracuseStep 18125309 = 6796991) B6796991
theorem B12083539 : Blo 1985435 12083539 := bstep (se 1 (by rfl) ⟨9062654, by rfl⟩ : syracuseStep 12083539 = 18125309) B18125309
theorem B16111385 : Blo 1985435 16111385 := bstep (se 2 (by rfl) ⟨6041769, by rfl⟩ : syracuseStep 16111385 = 12083539) B12083539
theorem B10740923 : Blo 1985435 10740923 := bstep (se 1 (by rfl) ⟨8055692, by rfl⟩ : syracuseStep 10740923 = 16111385) B16111385
theorem B7160615 : Blo 1985435 7160615 := bstep (se 1 (by rfl) ⟨5370461, by rfl⟩ : syracuseStep 7160615 = 10740923) B10740923
theorem B4773743 : Blo 1985435 4773743 := bstep (se 1 (by rfl) ⟨3580307, by rfl⟩ : syracuseStep 4773743 = 7160615) B7160615
theorem B3182495 : Blo 1985435 3182495 := bstep (se 1 (by rfl) ⟨2386871, by rfl⟩ : syracuseStep 3182495 = 4773743) B4773743
theorem B33946613 : Blo 1985435 33946613 := bstep (se 5 (by rfl) ⟨1591247, by rfl⟩ : syracuseStep 33946613 = 3182495) B3182495
theorem B22631075 : Blo 1985435 22631075 := bstep (se 1 (by rfl) ⟨16973306, by rfl⟩ : syracuseStep 22631075 = 33946613) B33946613
theorem B15087383 : Blo 1985435 15087383 := bstep (se 1 (by rfl) ⟨11315537, by rfl⟩ : syracuseStep 15087383 = 22631075) B22631075
theorem B10058255 : Blo 1985435 10058255 := bstep (se 1 (by rfl) ⟨7543691, by rfl⟩ : syracuseStep 10058255 = 15087383) B15087383
theorem B6705503 : Blo 1985435 6705503 := bstep (se 1 (by rfl) ⟨5029127, by rfl⟩ : syracuseStep 6705503 = 10058255) B10058255
theorem B4470335 : Blo 1985435 4470335 := bstep (se 1 (by rfl) ⟨3352751, by rfl⟩ : syracuseStep 4470335 = 6705503) B6705503
theorem B2980223 : Blo 1985435 2980223 := bstep (se 1 (by rfl) ⟨2235167, by rfl⟩ : syracuseStep 2980223 = 4470335) B4470335
theorem B1986815 : Blo 1985435 1986815 := bstep (se 1 (by rfl) ⟨1490111, by rfl⟩ : syracuseStep 1986815 = 2980223) B2980223
theorem B2980229 : Blo 1985435 2980229 := bbase (se 4 (by rfl) ⟨279396, by rfl⟩ : syracuseStep 2980229 = 558793) (by norm_num)
theorem B1986819 : Blo 1985435 1986819 := bstep (se 1 (by rfl) ⟨1490114, by rfl⟩ : syracuseStep 1986819 = 2980229) B2980229
theorem B3352765 : Blo 1985435 3352765 := bbase (se 3 (by rfl) ⟨628643, by rfl⟩ : syracuseStep 3352765 = 1257287) (by norm_num)
theorem B4470353 : Blo 1985435 4470353 := bstep (se 2 (by rfl) ⟨1676382, by rfl⟩ : syracuseStep 4470353 = 3352765) B3352765
theorem B2980235 : Blo 1985435 2980235 := bstep (se 1 (by rfl) ⟨2235176, by rfl⟩ : syracuseStep 2980235 = 4470353) B4470353
theorem B1986823 : Blo 1985435 1986823 := bstep (se 1 (by rfl) ⟨1490117, by rfl⟩ : syracuseStep 1986823 = 2980235) B2980235
theorem B2235181 : Blo 1985435 2235181 := bbase (se 3 (by rfl) ⟨419096, by rfl⟩ : syracuseStep 2235181 = 838193) (by norm_num)
theorem B2980241 : Blo 1985435 2980241 := bstep (se 2 (by rfl) ⟨1117590, by rfl⟩ : syracuseStep 2980241 = 2235181) B2235181
theorem B1986827 : Blo 1985435 1986827 := bstep (se 1 (by rfl) ⟨1490120, by rfl⟩ : syracuseStep 1986827 = 2980241) B2980241
theorem B6705557 : Blo 1985435 6705557 := bbase (se 6 (by rfl) ⟨157161, by rfl⟩ : syracuseStep 6705557 = 314323) (by norm_num)
theorem B4470371 : Blo 1985435 4470371 := bstep (se 1 (by rfl) ⟨3352778, by rfl⟩ : syracuseStep 4470371 = 6705557) B6705557
theorem B2980247 : Blo 1985435 2980247 := bstep (se 1 (by rfl) ⟨2235185, by rfl⟩ : syracuseStep 2980247 = 4470371) B4470371
theorem B1986831 : Blo 1985435 1986831 := bstep (se 1 (by rfl) ⟨1490123, by rfl⟩ : syracuseStep 1986831 = 2980247) B2980247
theorem B2980253 : Blo 1985435 2980253 := bbase (se 3 (by rfl) ⟨558797, by rfl⟩ : syracuseStep 2980253 = 1117595) (by norm_num)
theorem B1986835 : Blo 1985435 1986835 := bstep (se 1 (by rfl) ⟨1490126, by rfl⟩ : syracuseStep 1986835 = 2980253) B2980253
theorem B4470389 : Blo 1985435 4470389 := bbase (se 5 (by rfl) ⟨209549, by rfl⟩ : syracuseStep 4470389 = 419099) (by norm_num)
theorem B2980259 : Blo 1985435 2980259 := bstep (se 1 (by rfl) ⟨2235194, by rfl⟩ : syracuseStep 2980259 = 4470389) B4470389
theorem B1986839 : Blo 1985435 1986839 := bstep (se 1 (by rfl) ⟨1490129, by rfl⟩ : syracuseStep 1986839 = 2980259) B2980259
theorem B2685269 : Blo 1985435 2685269 := bbase (se 10 (by rfl) ⟨3933, by rfl⟩ : syracuseStep 2685269 = 7867) (by norm_num)
theorem B7160717 : Blo 1985435 7160717 := bstep (se 3 (by rfl) ⟨1342634, by rfl⟩ : syracuseStep 7160717 = 2685269) B2685269
theorem B4773811 : Blo 1985435 4773811 := bstep (se 1 (by rfl) ⟨3580358, by rfl⟩ : syracuseStep 4773811 = 7160717) B7160717
theorem B6365081 : Blo 1985435 6365081 := bstep (se 2 (by rfl) ⟨2386905, by rfl⟩ : syracuseStep 6365081 = 4773811) B4773811
theorem B16973549 : Blo 1985435 16973549 := bstep (se 3 (by rfl) ⟨3182540, by rfl⟩ : syracuseStep 16973549 = 6365081) B6365081
theorem B11315699 : Blo 1985435 11315699 := bstep (se 1 (by rfl) ⟨8486774, by rfl⟩ : syracuseStep 11315699 = 16973549) B16973549
theorem B7543799 : Blo 1985435 7543799 := bstep (se 1 (by rfl) ⟨5657849, by rfl⟩ : syracuseStep 7543799 = 11315699) B11315699
theorem B5029199 : Blo 1985435 5029199 := bstep (se 1 (by rfl) ⟨3771899, by rfl⟩ : syracuseStep 5029199 = 7543799) B7543799
theorem B3352799 : Blo 1985435 3352799 := bstep (se 1 (by rfl) ⟨2514599, by rfl⟩ : syracuseStep 3352799 = 5029199) B5029199
theorem B2235199 : Blo 1985435 2235199 := bstep (se 1 (by rfl) ⟨1676399, by rfl⟩ : syracuseStep 2235199 = 3352799) B3352799
theorem B2980265 : Blo 1985435 2980265 := bstep (se 2 (by rfl) ⟨1117599, by rfl⟩ : syracuseStep 2980265 = 2235199) B2235199
theorem B1986843 : Blo 1985435 1986843 := bstep (se 1 (by rfl) ⟨1490132, by rfl⟩ : syracuseStep 1986843 = 2980265) B2980265
theorem B7543813 : Blo 1985435 7543813 := bbase (se 4 (by rfl) ⟨707232, by rfl⟩ : syracuseStep 7543813 = 1414465) (by norm_num)
theorem B10058417 : Blo 1985435 10058417 := bstep (se 2 (by rfl) ⟨3771906, by rfl⟩ : syracuseStep 10058417 = 7543813) B7543813
theorem B6705611 : Blo 1985435 6705611 := bstep (se 1 (by rfl) ⟨5029208, by rfl⟩ : syracuseStep 6705611 = 10058417) B10058417
theorem B4470407 : Blo 1985435 4470407 := bstep (se 1 (by rfl) ⟨3352805, by rfl⟩ : syracuseStep 4470407 = 6705611) B6705611
theorem B2980271 : Blo 1985435 2980271 := bstep (se 1 (by rfl) ⟨2235203, by rfl⟩ : syracuseStep 2980271 = 4470407) B4470407
theorem B1986847 : Blo 1985435 1986847 := bstep (se 1 (by rfl) ⟨1490135, by rfl⟩ : syracuseStep 1986847 = 2980271) B2980271
theorem B2980277 : Blo 1985435 2980277 := bbase (se 5 (by rfl) ⟨139700, by rfl⟩ : syracuseStep 2980277 = 279401) (by norm_num)
theorem B1986851 : Blo 1985435 1986851 := bstep (se 1 (by rfl) ⟨1490138, by rfl⟩ : syracuseStep 1986851 = 2980277) B2980277
theorem B5029229 : Blo 1985435 5029229 := bbase (se 3 (by rfl) ⟨942980, by rfl⟩ : syracuseStep 5029229 = 1885961) (by norm_num)
theorem B3352819 : Blo 1985435 3352819 := bstep (se 1 (by rfl) ⟨2514614, by rfl⟩ : syracuseStep 3352819 = 5029229) B5029229
theorem B4470425 : Blo 1985435 4470425 := bstep (se 2 (by rfl) ⟨1676409, by rfl⟩ : syracuseStep 4470425 = 3352819) B3352819
theorem B2980283 : Blo 1985435 2980283 := bstep (se 1 (by rfl) ⟨2235212, by rfl⟩ : syracuseStep 2980283 = 4470425) B4470425
theorem B1986855 : Blo 1985435 1986855 := bstep (se 1 (by rfl) ⟨1490141, by rfl⟩ : syracuseStep 1986855 = 2980283) B2980283
theorem B2235217 : Blo 1985435 2235217 := bbase (se 2 (by rfl) ⟨838206, by rfl⟩ : syracuseStep 2235217 = 1676413) (by norm_num)
theorem B2980289 : Blo 1985435 2980289 := bstep (se 2 (by rfl) ⟨1117608, by rfl⟩ : syracuseStep 2980289 = 2235217) B2235217
theorem B1986859 : Blo 1985435 1986859 := bstep (se 1 (by rfl) ⟨1490144, by rfl⟩ : syracuseStep 1986859 = 2980289) B2980289
theorem B3182573 : Blo 1985435 3182573 := bbase (se 3 (by rfl) ⟨596732, by rfl⟩ : syracuseStep 3182573 = 1193465) (by norm_num)
theorem B2121715 : Blo 1985435 2121715 := bstep (se 1 (by rfl) ⟨1591286, by rfl⟩ : syracuseStep 2121715 = 3182573) B3182573
theorem B2828953 : Blo 1985435 2828953 := bstep (se 2 (by rfl) ⟨1060857, by rfl⟩ : syracuseStep 2828953 = 2121715) B2121715
theorem B3771937 : Blo 1985435 3771937 := bstep (se 2 (by rfl) ⟨1414476, by rfl⟩ : syracuseStep 3771937 = 2828953) B2828953
theorem B5029249 : Blo 1985435 5029249 := bstep (se 2 (by rfl) ⟨1885968, by rfl⟩ : syracuseStep 5029249 = 3771937) B3771937
theorem B6705665 : Blo 1985435 6705665 := bstep (se 2 (by rfl) ⟨2514624, by rfl⟩ : syracuseStep 6705665 = 5029249) B5029249
theorem B4470443 : Blo 1985435 4470443 := bstep (se 1 (by rfl) ⟨3352832, by rfl⟩ : syracuseStep 4470443 = 6705665) B6705665
theorem B2980295 : Blo 1985435 2980295 := bstep (se 1 (by rfl) ⟨2235221, by rfl⟩ : syracuseStep 2980295 = 4470443) B4470443
theorem B1986863 : Blo 1985435 1986863 := bstep (se 1 (by rfl) ⟨1490147, by rfl⟩ : syracuseStep 1986863 = 2980295) B2980295
theorem B2980301 : Blo 1985435 2980301 := bbase (se 3 (by rfl) ⟨558806, by rfl⟩ : syracuseStep 2980301 = 1117613) (by norm_num)
theorem B1986867 : Blo 1985435 1986867 := bstep (se 1 (by rfl) ⟨1490150, by rfl⟩ : syracuseStep 1986867 = 2980301) B2980301
theorem B4470461 : Blo 1985435 4470461 := bbase (se 3 (by rfl) ⟨838211, by rfl⟩ : syracuseStep 4470461 = 1676423) (by norm_num)
theorem B2980307 : Blo 1985435 2980307 := bstep (se 1 (by rfl) ⟨2235230, by rfl⟩ : syracuseStep 2980307 = 4470461) B4470461
theorem B1986871 : Blo 1985435 1986871 := bstep (se 1 (by rfl) ⟨1490153, by rfl⟩ : syracuseStep 1986871 = 2980307) B2980307
theorem B3352853 : Blo 1985435 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B2235235 : Blo 1985435 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B2980313 : Blo 1985435 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B1986875 : Blo 1985435 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B2685317 : Blo 1985435 2685317 := bbase (se 4 (by rfl) ⟨251748, by rfl⟩ : syracuseStep 2685317 = 503497) (by norm_num)
theorem B28643381 : Blo 1985435 28643381 := bstep (se 5 (by rfl) ⟨1342658, by rfl⟩ : syracuseStep 28643381 = 2685317) B2685317
theorem B19095587 : Blo 1985435 19095587 := bstep (se 1 (by rfl) ⟨14321690, by rfl⟩ : syracuseStep 19095587 = 28643381) B28643381
theorem B12730391 : Blo 1985435 12730391 := bstep (se 1 (by rfl) ⟨9547793, by rfl⟩ : syracuseStep 12730391 = 19095587) B19095587
theorem B8486927 : Blo 1985435 8486927 := bstep (se 1 (by rfl) ⟨6365195, by rfl⟩ : syracuseStep 8486927 = 12730391) B12730391
theorem B5657951 : Blo 1985435 5657951 := bstep (se 1 (by rfl) ⟨4243463, by rfl⟩ : syracuseStep 5657951 = 8486927) B8486927
theorem B15087869 : Blo 1985435 15087869 := bstep (se 3 (by rfl) ⟨2828975, by rfl⟩ : syracuseStep 15087869 = 5657951) B5657951
theorem B10058579 : Blo 1985435 10058579 := bstep (se 1 (by rfl) ⟨7543934, by rfl⟩ : syracuseStep 10058579 = 15087869) B15087869
theorem B6705719 : Blo 1985435 6705719 := bstep (se 1 (by rfl) ⟨5029289, by rfl⟩ : syracuseStep 6705719 = 10058579) B10058579
theorem B4470479 : Blo 1985435 4470479 := bstep (se 1 (by rfl) ⟨3352859, by rfl⟩ : syracuseStep 4470479 = 6705719) B6705719
theorem B2980319 : Blo 1985435 2980319 := bstep (se 1 (by rfl) ⟨2235239, by rfl⟩ : syracuseStep 2980319 = 4470479) B4470479
theorem B1986879 : Blo 1985435 1986879 := bstep (se 1 (by rfl) ⟨1490159, by rfl⟩ : syracuseStep 1986879 = 2980319) B2980319
theorem B2980325 : Blo 1985435 2980325 := bbase (se 4 (by rfl) ⟨279405, by rfl⟩ : syracuseStep 2980325 = 558811) (by norm_num)
theorem B1986883 : Blo 1985435 1986883 := bstep (se 1 (by rfl) ⟨1490162, by rfl⟩ : syracuseStep 1986883 = 2980325) B2980325
theorem B4773917 : Blo 1985435 4773917 := bbase (se 3 (by rfl) ⟨895109, by rfl⟩ : syracuseStep 4773917 = 1790219) (by norm_num)
theorem B12730445 : Blo 1985435 12730445 := bstep (se 3 (by rfl) ⟨2386958, by rfl⟩ : syracuseStep 12730445 = 4773917) B4773917
theorem B8486963 : Blo 1985435 8486963 := bstep (se 1 (by rfl) ⟨6365222, by rfl⟩ : syracuseStep 8486963 = 12730445) B12730445
theorem B5657975 : Blo 1985435 5657975 := bstep (se 1 (by rfl) ⟨4243481, by rfl⟩ : syracuseStep 5657975 = 8486963) B8486963
theorem B3771983 : Blo 1985435 3771983 := bstep (se 1 (by rfl) ⟨2828987, by rfl⟩ : syracuseStep 3771983 = 5657975) B5657975
theorem B2514655 : Blo 1985435 2514655 := bstep (se 1 (by rfl) ⟨1885991, by rfl⟩ : syracuseStep 2514655 = 3771983) B3771983
theorem B3352873 : Blo 1985435 3352873 := bstep (se 2 (by rfl) ⟨1257327, by rfl⟩ : syracuseStep 3352873 = 2514655) B2514655
theorem B4470497 : Blo 1985435 4470497 := bstep (se 2 (by rfl) ⟨1676436, by rfl⟩ : syracuseStep 4470497 = 3352873) B3352873
theorem B2980331 : Blo 1985435 2980331 := bstep (se 1 (by rfl) ⟨2235248, by rfl⟩ : syracuseStep 2980331 = 4470497) B4470497
theorem B1986887 : Blo 1985435 1986887 := bstep (se 1 (by rfl) ⟨1490165, by rfl⟩ : syracuseStep 1986887 = 2980331) B2980331
theorem B2235253 : Blo 1985435 2235253 := bbase (se 5 (by rfl) ⟨104777, by rfl⟩ : syracuseStep 2235253 = 209555) (by norm_num)
theorem B2980337 : Blo 1985435 2980337 := bstep (se 2 (by rfl) ⟨1117626, by rfl⟩ : syracuseStep 2980337 = 2235253) B2235253
theorem B1986891 : Blo 1985435 1986891 := bstep (se 1 (by rfl) ⟨1490168, by rfl⟩ : syracuseStep 1986891 = 2980337) B2980337
theorem B2514665 : Blo 1985435 2514665 := bbase (se 2 (by rfl) ⟨942999, by rfl⟩ : syracuseStep 2514665 = 1885999) (by norm_num)
theorem B6705773 : Blo 1985435 6705773 := bstep (se 3 (by rfl) ⟨1257332, by rfl⟩ : syracuseStep 6705773 = 2514665) B2514665
theorem B4470515 : Blo 1985435 4470515 := bstep (se 1 (by rfl) ⟨3352886, by rfl⟩ : syracuseStep 4470515 = 6705773) B6705773
theorem B2980343 : Blo 1985435 2980343 := bstep (se 1 (by rfl) ⟨2235257, by rfl⟩ : syracuseStep 2980343 = 4470515) B4470515
theorem B1986895 : Blo 1985435 1986895 := bstep (se 1 (by rfl) ⟨1490171, by rfl⟩ : syracuseStep 1986895 = 2980343) B2980343
theorem B2980349 : Blo 1985435 2980349 := bbase (se 3 (by rfl) ⟨558815, by rfl⟩ : syracuseStep 2980349 = 1117631) (by norm_num)
theorem B1986899 : Blo 1985435 1986899 := bstep (se 1 (by rfl) ⟨1490174, by rfl⟩ : syracuseStep 1986899 = 2980349) B2980349
theorem B4470533 : Blo 1985435 4470533 := bbase (se 4 (by rfl) ⟨419112, by rfl⟩ : syracuseStep 4470533 = 838225) (by norm_num)
theorem B2980355 : Blo 1985435 2980355 := bstep (se 1 (by rfl) ⟨2235266, by rfl⟩ : syracuseStep 2980355 = 4470533) B4470533
theorem B1986903 : Blo 1985435 1986903 := bstep (se 1 (by rfl) ⟨1490177, by rfl⟩ : syracuseStep 1986903 = 2980355) B2980355
theorem B3772021 : Blo 1985435 3772021 := bbase (se 5 (by rfl) ⟨176813, by rfl⟩ : syracuseStep 3772021 = 353627) (by norm_num)
theorem B5029361 : Blo 1985435 5029361 := bstep (se 2 (by rfl) ⟨1886010, by rfl⟩ : syracuseStep 5029361 = 3772021) B3772021
theorem B3352907 : Blo 1985435 3352907 := bstep (se 1 (by rfl) ⟨2514680, by rfl⟩ : syracuseStep 3352907 = 5029361) B5029361
theorem B2235271 : Blo 1985435 2235271 := bstep (se 1 (by rfl) ⟨1676453, by rfl⟩ : syracuseStep 2235271 = 3352907) B3352907
theorem B2980361 : Blo 1985435 2980361 := bstep (se 2 (by rfl) ⟨1117635, by rfl⟩ : syracuseStep 2980361 = 2235271) B2235271
theorem B1986907 : Blo 1985435 1986907 := bstep (se 1 (by rfl) ⟨1490180, by rfl⟩ : syracuseStep 1986907 = 2980361) B2980361
theorem B10058741 : Blo 1985435 10058741 := bbase (se 5 (by rfl) ⟨471503, by rfl⟩ : syracuseStep 10058741 = 943007) (by norm_num)
theorem B6705827 : Blo 1985435 6705827 := bstep (se 1 (by rfl) ⟨5029370, by rfl⟩ : syracuseStep 6705827 = 10058741) B10058741
theorem B4470551 : Blo 1985435 4470551 := bstep (se 1 (by rfl) ⟨3352913, by rfl⟩ : syracuseStep 4470551 = 6705827) B6705827
theorem B2980367 : Blo 1985435 2980367 := bstep (se 1 (by rfl) ⟨2235275, by rfl⟩ : syracuseStep 2980367 = 4470551) B4470551
theorem B1986911 : Blo 1985435 1986911 := bstep (se 1 (by rfl) ⟨1490183, by rfl⟩ : syracuseStep 1986911 = 2980367) B2980367
theorem B2980373 : Blo 1985435 2980373 := bbase (se 6 (by rfl) ⟨69852, by rfl⟩ : syracuseStep 2980373 = 139705) (by norm_num)
theorem B1986915 : Blo 1985435 1986915 := bstep (se 1 (by rfl) ⟨1490186, by rfl⟩ : syracuseStep 1986915 = 2980373) B2980373
theorem B16974197 : Blo 1985435 16974197 := bbase (se 5 (by rfl) ⟨795665, by rfl⟩ : syracuseStep 16974197 = 1591331) (by norm_num)
theorem B11316131 : Blo 1985435 11316131 := bstep (se 1 (by rfl) ⟨8487098, by rfl⟩ : syracuseStep 11316131 = 16974197) B16974197
theorem B7544087 : Blo 1985435 7544087 := bstep (se 1 (by rfl) ⟨5658065, by rfl⟩ : syracuseStep 7544087 = 11316131) B11316131
theorem B5029391 : Blo 1985435 5029391 := bstep (se 1 (by rfl) ⟨3772043, by rfl⟩ : syracuseStep 5029391 = 7544087) B7544087
theorem B3352927 : Blo 1985435 3352927 := bstep (se 1 (by rfl) ⟨2514695, by rfl⟩ : syracuseStep 3352927 = 5029391) B5029391
theorem B4470569 : Blo 1985435 4470569 := bstep (se 2 (by rfl) ⟨1676463, by rfl⟩ : syracuseStep 4470569 = 3352927) B3352927
theorem B2980379 : Blo 1985435 2980379 := bstep (se 1 (by rfl) ⟨2235284, by rfl⟩ : syracuseStep 2980379 = 4470569) B4470569
theorem B1986919 : Blo 1985435 1986919 := bstep (se 1 (by rfl) ⟨1490189, by rfl⟩ : syracuseStep 1986919 = 2980379) B2980379
theorem B2235289 : Blo 1985435 2235289 := bbase (se 2 (by rfl) ⟨838233, by rfl⟩ : syracuseStep 2235289 = 1676467) (by norm_num)
theorem B2980385 : Blo 1985435 2980385 := bstep (se 2 (by rfl) ⟨1117644, by rfl⟩ : syracuseStep 2980385 = 2235289) B2235289
theorem B1986923 : Blo 1985435 1986923 := bstep (se 1 (by rfl) ⟨1490192, by rfl⟩ : syracuseStep 1986923 = 2980385) B2980385
theorem B7544117 : Blo 1985435 7544117 := bbase (se 5 (by rfl) ⟨353630, by rfl⟩ : syracuseStep 7544117 = 707261) (by norm_num)
theorem B5029411 : Blo 1985435 5029411 := bstep (se 1 (by rfl) ⟨3772058, by rfl⟩ : syracuseStep 5029411 = 7544117) B7544117
theorem B6705881 : Blo 1985435 6705881 := bstep (se 2 (by rfl) ⟨2514705, by rfl⟩ : syracuseStep 6705881 = 5029411) B5029411
theorem B4470587 : Blo 1985435 4470587 := bstep (se 1 (by rfl) ⟨3352940, by rfl⟩ : syracuseStep 4470587 = 6705881) B6705881
theorem B2980391 : Blo 1985435 2980391 := bstep (se 1 (by rfl) ⟨2235293, by rfl⟩ : syracuseStep 2980391 = 4470587) B4470587
theorem B1986927 : Blo 1985435 1986927 := bstep (se 1 (by rfl) ⟨1490195, by rfl⟩ : syracuseStep 1986927 = 2980391) B2980391
theorem B2980397 : Blo 1985435 2980397 := bbase (se 3 (by rfl) ⟨558824, by rfl⟩ : syracuseStep 2980397 = 1117649) (by norm_num)
theorem B1986931 : Blo 1985435 1986931 := bstep (se 1 (by rfl) ⟨1490198, by rfl⟩ : syracuseStep 1986931 = 2980397) B2980397
theorem B4470605 : Blo 1985435 4470605 := bbase (se 3 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 4470605 = 1676477) (by norm_num)
theorem B2980403 : Blo 1985435 2980403 := bstep (se 1 (by rfl) ⟨2235302, by rfl⟩ : syracuseStep 2980403 = 4470605) B4470605
theorem B1986935 : Blo 1985435 1986935 := bstep (se 1 (by rfl) ⟨1490201, by rfl⟩ : syracuseStep 1986935 = 2980403) B2980403
theorem B2514721 : Blo 1985435 2514721 := bbase (se 2 (by rfl) ⟨943020, by rfl⟩ : syracuseStep 2514721 = 1886041) (by norm_num)
theorem B3352961 : Blo 1985435 3352961 := bstep (se 2 (by rfl) ⟨1257360, by rfl⟩ : syracuseStep 3352961 = 2514721) B2514721
theorem B2235307 : Blo 1985435 2235307 := bstep (se 1 (by rfl) ⟨1676480, by rfl⟩ : syracuseStep 2235307 = 3352961) B3352961
theorem B2980409 : Blo 1985435 2980409 := bstep (se 2 (by rfl) ⟨1117653, by rfl⟩ : syracuseStep 2980409 = 2235307) B2235307
theorem B1986939 : Blo 1985435 1986939 := bstep (se 1 (by rfl) ⟨1490204, by rfl⟩ : syracuseStep 1986939 = 2980409) B2980409
theorem B22632533 : Blo 1985435 22632533 := bbase (se 8 (by rfl) ⟨132612, by rfl⟩ : syracuseStep 22632533 = 265225) (by norm_num)
theorem B15088355 : Blo 1985435 15088355 := bstep (se 1 (by rfl) ⟨11316266, by rfl⟩ : syracuseStep 15088355 = 22632533) B22632533
theorem B10058903 : Blo 1985435 10058903 := bstep (se 1 (by rfl) ⟨7544177, by rfl⟩ : syracuseStep 10058903 = 15088355) B15088355
theorem B6705935 : Blo 1985435 6705935 := bstep (se 1 (by rfl) ⟨5029451, by rfl⟩ : syracuseStep 6705935 = 10058903) B10058903
theorem B4470623 : Blo 1985435 4470623 := bstep (se 1 (by rfl) ⟨3352967, by rfl⟩ : syracuseStep 4470623 = 6705935) B6705935
theorem B2980415 : Blo 1985435 2980415 := bstep (se 1 (by rfl) ⟨2235311, by rfl⟩ : syracuseStep 2980415 = 4470623) B4470623
theorem B1986943 : Blo 1985435 1986943 := bstep (se 1 (by rfl) ⟨1490207, by rfl⟩ : syracuseStep 1986943 = 2980415) B2980415
theorem B2980421 : Blo 1985435 2980421 := bbase (se 4 (by rfl) ⟨279414, by rfl⟩ : syracuseStep 2980421 = 558829) (by norm_num)
theorem B1986947 : Blo 1985435 1986947 := bstep (se 1 (by rfl) ⟨1490210, by rfl⟩ : syracuseStep 1986947 = 2980421) B2980421
theorem B3352981 : Blo 1985435 3352981 := bbase (se 6 (by rfl) ⟨78585, by rfl⟩ : syracuseStep 3352981 = 157171) (by norm_num)
theorem B4470641 : Blo 1985435 4470641 := bstep (se 2 (by rfl) ⟨1676490, by rfl⟩ : syracuseStep 4470641 = 3352981) B3352981
theorem B2980427 : Blo 1985435 2980427 := bstep (se 1 (by rfl) ⟨2235320, by rfl⟩ : syracuseStep 2980427 = 4470641) B4470641
theorem B1986951 : Blo 1985435 1986951 := bstep (se 1 (by rfl) ⟨1490213, by rfl⟩ : syracuseStep 1986951 = 2980427) B2980427
theorem B2235325 : Blo 1985435 2235325 := bbase (se 3 (by rfl) ⟨419123, by rfl⟩ : syracuseStep 2235325 = 838247) (by norm_num)
theorem B2980433 : Blo 1985435 2980433 := bstep (se 2 (by rfl) ⟨1117662, by rfl⟩ : syracuseStep 2980433 = 2235325) B2235325
theorem B1986955 : Blo 1985435 1986955 := bstep (se 1 (by rfl) ⟨1490216, by rfl⟩ : syracuseStep 1986955 = 2980433) B2980433
theorem B6705989 : Blo 1985435 6705989 := bbase (se 4 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 6705989 = 1257373) (by norm_num)
theorem B4470659 : Blo 1985435 4470659 := bstep (se 1 (by rfl) ⟨3352994, by rfl⟩ : syracuseStep 4470659 = 6705989) B6705989
theorem B2980439 : Blo 1985435 2980439 := bstep (se 1 (by rfl) ⟨2235329, by rfl⟩ : syracuseStep 2980439 = 4470659) B4470659
theorem B1986959 : Blo 1985435 1986959 := bstep (se 1 (by rfl) ⟨1490219, by rfl⟩ : syracuseStep 1986959 = 2980439) B2980439
theorem B2980445 : Blo 1985435 2980445 := bbase (se 3 (by rfl) ⟨558833, by rfl⟩ : syracuseStep 2980445 = 1117667) (by norm_num)
theorem B1986963 : Blo 1985435 1986963 := bstep (se 1 (by rfl) ⟨1490222, by rfl⟩ : syracuseStep 1986963 = 2980445) B2980445
theorem B4470677 : Blo 1985435 4470677 := bbase (se 6 (by rfl) ⟨104781, by rfl⟩ : syracuseStep 4470677 = 209563) (by norm_num)
theorem B2980451 : Blo 1985435 2980451 := bstep (se 1 (by rfl) ⟨2235338, by rfl⟩ : syracuseStep 2980451 = 4470677) B4470677
theorem B1986967 : Blo 1985435 1986967 := bstep (se 1 (by rfl) ⟨1490225, by rfl⟩ : syracuseStep 1986967 = 2980451) B2980451
theorem B4243661 : Blo 1985435 4243661 := bbase (se 3 (by rfl) ⟨795686, by rfl⟩ : syracuseStep 4243661 = 1591373) (by norm_num)
theorem B2829107 : Blo 1985435 2829107 := bstep (se 1 (by rfl) ⟨2121830, by rfl⟩ : syracuseStep 2829107 = 4243661) B4243661
theorem B7544285 : Blo 1985435 7544285 := bstep (se 3 (by rfl) ⟨1414553, by rfl⟩ : syracuseStep 7544285 = 2829107) B2829107
theorem B5029523 : Blo 1985435 5029523 := bstep (se 1 (by rfl) ⟨3772142, by rfl⟩ : syracuseStep 5029523 = 7544285) B7544285
theorem B3353015 : Blo 1985435 3353015 := bstep (se 1 (by rfl) ⟨2514761, by rfl⟩ : syracuseStep 3353015 = 5029523) B5029523
theorem B2235343 : Blo 1985435 2235343 := bstep (se 1 (by rfl) ⟨1676507, by rfl⟩ : syracuseStep 2235343 = 3353015) B3353015
theorem B2980457 : Blo 1985435 2980457 := bstep (se 2 (by rfl) ⟨1117671, by rfl⟩ : syracuseStep 2980457 = 2235343) B2235343
theorem B1986971 : Blo 1985435 1986971 := bstep (se 1 (by rfl) ⟨1490228, by rfl⟩ : syracuseStep 1986971 = 2980457) B2980457
theorem B2906837 : Blo 1985435 2906837 := bbase (se 7 (by rfl) ⟨34064, by rfl⟩ : syracuseStep 2906837 = 68129) (by norm_num)
theorem B31006261 : Blo 1985435 31006261 := bstep (se 5 (by rfl) ⟨1453418, by rfl⟩ : syracuseStep 31006261 = 2906837) B2906837
theorem B41341681 : Blo 1985435 41341681 := bstep (se 2 (by rfl) ⟨15503130, by rfl⟩ : syracuseStep 41341681 = 31006261) B31006261
theorem B55122241 : Blo 1985435 55122241 := bstep (se 2 (by rfl) ⟨20670840, by rfl⟩ : syracuseStep 55122241 = 41341681) B41341681
theorem B73496321 : Blo 1985435 73496321 := bstep (se 2 (by rfl) ⟨27561120, by rfl⟩ : syracuseStep 73496321 = 55122241) B55122241
theorem B48997547 : Blo 1985435 48997547 := bstep (se 1 (by rfl) ⟨36748160, by rfl⟩ : syracuseStep 48997547 = 73496321) B73496321
theorem B32665031 : Blo 1985435 32665031 := bstep (se 1 (by rfl) ⟨24498773, by rfl⟩ : syracuseStep 32665031 = 48997547) B48997547
theorem B21776687 : Blo 1985435 21776687 := bstep (se 1 (by rfl) ⟨16332515, by rfl⟩ : syracuseStep 21776687 = 32665031) B32665031
theorem B14517791 : Blo 1985435 14517791 := bstep (se 1 (by rfl) ⟨10888343, by rfl⟩ : syracuseStep 14517791 = 21776687) B21776687
theorem B9678527 : Blo 1985435 9678527 := bstep (se 1 (by rfl) ⟨7258895, by rfl⟩ : syracuseStep 9678527 = 14517791) B14517791
theorem B6452351 : Blo 1985435 6452351 := bstep (se 1 (by rfl) ⟨4839263, by rfl⟩ : syracuseStep 6452351 = 9678527) B9678527
theorem B4301567 : Blo 1985435 4301567 := bstep (se 1 (by rfl) ⟨3226175, by rfl⟩ : syracuseStep 4301567 = 6452351) B6452351
theorem B45883381 : Blo 1985435 45883381 := bstep (se 5 (by rfl) ⟨2150783, by rfl⟩ : syracuseStep 45883381 = 4301567) B4301567
theorem B61177841 : Blo 1985435 61177841 := bstep (se 2 (by rfl) ⟨22941690, by rfl⟩ : syracuseStep 61177841 = 45883381) B45883381
theorem B40785227 : Blo 1985435 40785227 := bstep (se 1 (by rfl) ⟨30588920, by rfl⟩ : syracuseStep 40785227 = 61177841) B61177841
theorem B27190151 : Blo 1985435 27190151 := bstep (se 1 (by rfl) ⟨20392613, by rfl⟩ : syracuseStep 27190151 = 40785227) B40785227
theorem B18126767 : Blo 1985435 18126767 := bstep (se 1 (by rfl) ⟨13595075, by rfl⟩ : syracuseStep 18126767 = 27190151) B27190151
theorem B48338045 : Blo 1985435 48338045 := bstep (se 3 (by rfl) ⟨9063383, by rfl⟩ : syracuseStep 48338045 = 18126767) B18126767
theorem B32225363 : Blo 1985435 32225363 := bstep (se 1 (by rfl) ⟨24169022, by rfl⟩ : syracuseStep 32225363 = 48338045) B48338045
theorem B21483575 : Blo 1985435 21483575 := bstep (se 1 (by rfl) ⟨16112681, by rfl⟩ : syracuseStep 21483575 = 32225363) B32225363
theorem B14322383 : Blo 1985435 14322383 := bstep (se 1 (by rfl) ⟨10741787, by rfl⟩ : syracuseStep 14322383 = 21483575) B21483575
theorem B9548255 : Blo 1985435 9548255 := bstep (se 1 (by rfl) ⟨7161191, by rfl⟩ : syracuseStep 9548255 = 14322383) B14322383
theorem B6365503 : Blo 1985435 6365503 := bstep (se 1 (by rfl) ⟨4774127, by rfl⟩ : syracuseStep 6365503 = 9548255) B9548255
theorem B8487337 : Blo 1985435 8487337 := bstep (se 2 (by rfl) ⟨3182751, by rfl⟩ : syracuseStep 8487337 = 6365503) B6365503
theorem B11316449 : Blo 1985435 11316449 := bstep (se 2 (by rfl) ⟨4243668, by rfl⟩ : syracuseStep 11316449 = 8487337) B8487337
theorem B7544299 : Blo 1985435 7544299 := bstep (se 1 (by rfl) ⟨5658224, by rfl⟩ : syracuseStep 7544299 = 11316449) B11316449
theorem B10059065 : Blo 1985435 10059065 := bstep (se 2 (by rfl) ⟨3772149, by rfl⟩ : syracuseStep 10059065 = 7544299) B7544299
theorem B6706043 : Blo 1985435 6706043 := bstep (se 1 (by rfl) ⟨5029532, by rfl⟩ : syracuseStep 6706043 = 10059065) B10059065
theorem B4470695 : Blo 1985435 4470695 := bstep (se 1 (by rfl) ⟨3353021, by rfl⟩ : syracuseStep 4470695 = 6706043) B6706043
theorem B2980463 : Blo 1985435 2980463 := bstep (se 1 (by rfl) ⟨2235347, by rfl⟩ : syracuseStep 2980463 = 4470695) B4470695
theorem B1986975 : Blo 1985435 1986975 := bstep (se 1 (by rfl) ⟨1490231, by rfl⟩ : syracuseStep 1986975 = 2980463) B2980463
theorem B2980469 : Blo 1985435 2980469 := bbase (se 5 (by rfl) ⟨139709, by rfl⟩ : syracuseStep 2980469 = 279419) (by norm_num)
theorem B1986979 : Blo 1985435 1986979 := bstep (se 1 (by rfl) ⟨1490234, by rfl⟩ : syracuseStep 1986979 = 2980469) B2980469
theorem B3772165 : Blo 1985435 3772165 := bbase (se 4 (by rfl) ⟨353640, by rfl⟩ : syracuseStep 3772165 = 707281) (by norm_num)
theorem B5029553 : Blo 1985435 5029553 := bstep (se 2 (by rfl) ⟨1886082, by rfl⟩ : syracuseStep 5029553 = 3772165) B3772165
theorem B3353035 : Blo 1985435 3353035 := bstep (se 1 (by rfl) ⟨2514776, by rfl⟩ : syracuseStep 3353035 = 5029553) B5029553
theorem B4470713 : Blo 1985435 4470713 := bstep (se 2 (by rfl) ⟨1676517, by rfl⟩ : syracuseStep 4470713 = 3353035) B3353035
theorem B2980475 : Blo 1985435 2980475 := bstep (se 1 (by rfl) ⟨2235356, by rfl⟩ : syracuseStep 2980475 = 4470713) B4470713
theorem B1986983 : Blo 1985435 1986983 := bstep (se 1 (by rfl) ⟨1490237, by rfl⟩ : syracuseStep 1986983 = 2980475) B2980475
theorem B2235361 : Blo 1985435 2235361 := bbase (se 2 (by rfl) ⟨838260, by rfl⟩ : syracuseStep 2235361 = 1676521) (by norm_num)
theorem B2980481 : Blo 1985435 2980481 := bstep (se 2 (by rfl) ⟨1117680, by rfl⟩ : syracuseStep 2980481 = 2235361) B2235361
theorem B1986987 : Blo 1985435 1986987 := bstep (se 1 (by rfl) ⟨1490240, by rfl⟩ : syracuseStep 1986987 = 2980481) B2980481
theorem B5029573 : Blo 1985435 5029573 := bbase (se 4 (by rfl) ⟨471522, by rfl⟩ : syracuseStep 5029573 = 943045) (by norm_num)
theorem B6706097 : Blo 1985435 6706097 := bstep (se 2 (by rfl) ⟨2514786, by rfl⟩ : syracuseStep 6706097 = 5029573) B5029573
theorem B4470731 : Blo 1985435 4470731 := bstep (se 1 (by rfl) ⟨3353048, by rfl⟩ : syracuseStep 4470731 = 6706097) B6706097
theorem B2980487 : Blo 1985435 2980487 := bstep (se 1 (by rfl) ⟨2235365, by rfl⟩ : syracuseStep 2980487 = 4470731) B4470731
theorem B1986991 : Blo 1985435 1986991 := bstep (se 1 (by rfl) ⟨1490243, by rfl⟩ : syracuseStep 1986991 = 2980487) B2980487
theorem B2980493 : Blo 1985435 2980493 := bbase (se 3 (by rfl) ⟨558842, by rfl⟩ : syracuseStep 2980493 = 1117685) (by norm_num)
theorem B1986995 : Blo 1985435 1986995 := bstep (se 1 (by rfl) ⟨1490246, by rfl⟩ : syracuseStep 1986995 = 2980493) B2980493
theorem B4470749 : Blo 1985435 4470749 := bbase (se 3 (by rfl) ⟨838265, by rfl⟩ : syracuseStep 4470749 = 1676531) (by norm_num)
theorem B2980499 : Blo 1985435 2980499 := bstep (se 1 (by rfl) ⟨2235374, by rfl⟩ : syracuseStep 2980499 = 4470749) B4470749
theorem B1986999 : Blo 1985435 1986999 := bstep (se 1 (by rfl) ⟨1490249, by rfl⟩ : syracuseStep 1986999 = 2980499) B2980499
theorem B3353069 : Blo 1985435 3353069 := bbase (se 3 (by rfl) ⟨628700, by rfl⟩ : syracuseStep 3353069 = 1257401) (by norm_num)
theorem B2235379 : Blo 1985435 2235379 := bstep (se 1 (by rfl) ⟨1676534, by rfl⟩ : syracuseStep 2235379 = 3353069) B3353069
theorem B2980505 : Blo 1985435 2980505 := bstep (se 2 (by rfl) ⟨1117689, by rfl⟩ : syracuseStep 2980505 = 2235379) B2235379
theorem B1987003 : Blo 1985435 1987003 := bstep (se 1 (by rfl) ⟨1490252, by rfl⟩ : syracuseStep 1987003 = 2980505) B2980505
theorem B25462421 : Blo 1985435 25462421 := bbase (se 6 (by rfl) ⟨596775, by rfl⟩ : syracuseStep 25462421 = 1193551) (by norm_num)
theorem B16974947 : Blo 1985435 16974947 := bstep (se 1 (by rfl) ⟨12731210, by rfl⟩ : syracuseStep 16974947 = 25462421) B25462421
theorem B11316631 : Blo 1985435 11316631 := bstep (se 1 (by rfl) ⟨8487473, by rfl⟩ : syracuseStep 11316631 = 16974947) B16974947
theorem B15088841 : Blo 1985435 15088841 := bstep (se 2 (by rfl) ⟨5658315, by rfl⟩ : syracuseStep 15088841 = 11316631) B11316631
theorem B10059227 : Blo 1985435 10059227 := bstep (se 1 (by rfl) ⟨7544420, by rfl⟩ : syracuseStep 10059227 = 15088841) B15088841
theorem B6706151 : Blo 1985435 6706151 := bstep (se 1 (by rfl) ⟨5029613, by rfl⟩ : syracuseStep 6706151 = 10059227) B10059227
theorem B4470767 : Blo 1985435 4470767 := bstep (se 1 (by rfl) ⟨3353075, by rfl⟩ : syracuseStep 4470767 = 6706151) B6706151
theorem B2980511 : Blo 1985435 2980511 := bstep (se 1 (by rfl) ⟨2235383, by rfl⟩ : syracuseStep 2980511 = 4470767) B4470767
theorem B1987007 : Blo 1985435 1987007 := bstep (se 1 (by rfl) ⟨1490255, by rfl⟩ : syracuseStep 1987007 = 2980511) B2980511
theorem B2980517 : Blo 1985435 2980517 := bbase (se 4 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 2980517 = 558847) (by norm_num)
theorem B1987011 : Blo 1985435 1987011 := bstep (se 1 (by rfl) ⟨1490258, by rfl⟩ : syracuseStep 1987011 = 2980517) B2980517
theorem B2514817 : Blo 1985435 2514817 := bbase (se 2 (by rfl) ⟨943056, by rfl⟩ : syracuseStep 2514817 = 1886113) (by norm_num)
theorem B3353089 : Blo 1985435 3353089 := bstep (se 2 (by rfl) ⟨1257408, by rfl⟩ : syracuseStep 3353089 = 2514817) B2514817
theorem B4470785 : Blo 1985435 4470785 := bstep (se 2 (by rfl) ⟨1676544, by rfl⟩ : syracuseStep 4470785 = 3353089) B3353089
theorem B2980523 : Blo 1985435 2980523 := bstep (se 1 (by rfl) ⟨2235392, by rfl⟩ : syracuseStep 2980523 = 4470785) B4470785
theorem B1987015 : Blo 1985435 1987015 := bstep (se 1 (by rfl) ⟨1490261, by rfl⟩ : syracuseStep 1987015 = 2980523) B2980523
theorem B2235397 : Blo 1985435 2235397 := bbase (se 4 (by rfl) ⟨209568, by rfl⟩ : syracuseStep 2235397 = 419137) (by norm_num)
theorem B2980529 : Blo 1985435 2980529 := bstep (se 2 (by rfl) ⟨1117698, by rfl⟩ : syracuseStep 2980529 = 2235397) B2235397
theorem B1987019 : Blo 1985435 1987019 := bstep (se 1 (by rfl) ⟨1490264, by rfl⟩ : syracuseStep 1987019 = 2980529) B2980529
theorem B2829181 : Blo 1985435 2829181 := bbase (se 3 (by rfl) ⟨530471, by rfl⟩ : syracuseStep 2829181 = 1060943) (by norm_num)
theorem B3772241 : Blo 1985435 3772241 := bstep (se 2 (by rfl) ⟨1414590, by rfl⟩ : syracuseStep 3772241 = 2829181) B2829181
theorem B2514827 : Blo 1985435 2514827 := bstep (se 1 (by rfl) ⟨1886120, by rfl⟩ : syracuseStep 2514827 = 3772241) B3772241
theorem B6706205 : Blo 1985435 6706205 := bstep (se 3 (by rfl) ⟨1257413, by rfl⟩ : syracuseStep 6706205 = 2514827) B2514827
theorem B4470803 : Blo 1985435 4470803 := bstep (se 1 (by rfl) ⟨3353102, by rfl⟩ : syracuseStep 4470803 = 6706205) B6706205
theorem B2980535 : Blo 1985435 2980535 := bstep (se 1 (by rfl) ⟨2235401, by rfl⟩ : syracuseStep 2980535 = 4470803) B4470803
theorem B1987023 : Blo 1985435 1987023 := bstep (se 1 (by rfl) ⟨1490267, by rfl⟩ : syracuseStep 1987023 = 2980535) B2980535
theorem B2980541 : Blo 1985435 2980541 := bbase (se 3 (by rfl) ⟨558851, by rfl⟩ : syracuseStep 2980541 = 1117703) (by norm_num)
theorem B1987027 : Blo 1985435 1987027 := bstep (se 1 (by rfl) ⟨1490270, by rfl⟩ : syracuseStep 1987027 = 2980541) B2980541
theorem B4470821 : Blo 1985435 4470821 := bbase (se 4 (by rfl) ⟨419139, by rfl⟩ : syracuseStep 4470821 = 838279) (by norm_num)
theorem B2980547 : Blo 1985435 2980547 := bstep (se 1 (by rfl) ⟨2235410, by rfl⟩ : syracuseStep 2980547 = 4470821) B4470821
theorem B1987031 : Blo 1985435 1987031 := bstep (se 1 (by rfl) ⟨1490273, by rfl⟩ : syracuseStep 1987031 = 2980547) B2980547
theorem B5029685 : Blo 1985435 5029685 := bbase (se 5 (by rfl) ⟨235766, by rfl⟩ : syracuseStep 5029685 = 471533) (by norm_num)
theorem B3353123 : Blo 1985435 3353123 := bstep (se 1 (by rfl) ⟨2514842, by rfl⟩ : syracuseStep 3353123 = 5029685) B5029685
theorem B2235415 : Blo 1985435 2235415 := bstep (se 1 (by rfl) ⟨1676561, by rfl⟩ : syracuseStep 2235415 = 3353123) B3353123
theorem B2980553 : Blo 1985435 2980553 := bstep (se 2 (by rfl) ⟨1117707, by rfl⟩ : syracuseStep 2980553 = 2235415) B2235415
theorem B1987035 : Blo 1985435 1987035 := bstep (se 1 (by rfl) ⟨1490276, by rfl⟩ : syracuseStep 1987035 = 2980553) B2980553
theorem B4839421 : Blo 1985435 4839421 := bbase (se 3 (by rfl) ⟨907391, by rfl⟩ : syracuseStep 4839421 = 1814783) (by norm_num)
theorem B6452561 : Blo 1985435 6452561 := bstep (se 2 (by rfl) ⟨2419710, by rfl⟩ : syracuseStep 6452561 = 4839421) B4839421
theorem B17206829 : Blo 1985435 17206829 := bstep (se 3 (by rfl) ⟨3226280, by rfl⟩ : syracuseStep 17206829 = 6452561) B6452561
theorem B11471219 : Blo 1985435 11471219 := bstep (se 1 (by rfl) ⟨8603414, by rfl⟩ : syracuseStep 11471219 = 17206829) B17206829
theorem B7647479 : Blo 1985435 7647479 := bstep (se 1 (by rfl) ⟨5735609, by rfl⟩ : syracuseStep 7647479 = 11471219) B11471219
theorem B5098319 : Blo 1985435 5098319 := bstep (se 1 (by rfl) ⟨3823739, by rfl⟩ : syracuseStep 5098319 = 7647479) B7647479
theorem B3398879 : Blo 1985435 3398879 := bstep (se 1 (by rfl) ⟨2549159, by rfl⟩ : syracuseStep 3398879 = 5098319) B5098319
theorem B9063677 : Blo 1985435 9063677 := bstep (se 3 (by rfl) ⟨1699439, by rfl⟩ : syracuseStep 9063677 = 3398879) B3398879
theorem B6042451 : Blo 1985435 6042451 := bstep (se 1 (by rfl) ⟨4531838, by rfl⟩ : syracuseStep 6042451 = 9063677) B9063677
theorem B8056601 : Blo 1985435 8056601 := bstep (se 2 (by rfl) ⟨3021225, by rfl⟩ : syracuseStep 8056601 = 6042451) B6042451
theorem B5371067 : Blo 1985435 5371067 := bstep (se 1 (by rfl) ⟨4028300, by rfl⟩ : syracuseStep 5371067 = 8056601) B8056601
theorem B14322845 : Blo 1985435 14322845 := bstep (se 3 (by rfl) ⟨2685533, by rfl⟩ : syracuseStep 14322845 = 5371067) B5371067
theorem B9548563 : Blo 1985435 9548563 := bstep (se 1 (by rfl) ⟨7161422, by rfl⟩ : syracuseStep 9548563 = 14322845) B14322845
theorem B12731417 : Blo 1985435 12731417 := bstep (se 2 (by rfl) ⟨4774281, by rfl⟩ : syracuseStep 12731417 = 9548563) B9548563
theorem B8487611 : Blo 1985435 8487611 := bstep (se 1 (by rfl) ⟨6365708, by rfl⟩ : syracuseStep 8487611 = 12731417) B12731417
theorem B5658407 : Blo 1985435 5658407 := bstep (se 1 (by rfl) ⟨4243805, by rfl⟩ : syracuseStep 5658407 = 8487611) B8487611
theorem B3772271 : Blo 1985435 3772271 := bstep (se 1 (by rfl) ⟨2829203, by rfl⟩ : syracuseStep 3772271 = 5658407) B5658407
theorem B10059389 : Blo 1985435 10059389 := bstep (se 3 (by rfl) ⟨1886135, by rfl⟩ : syracuseStep 10059389 = 3772271) B3772271
theorem B6706259 : Blo 1985435 6706259 := bstep (se 1 (by rfl) ⟨5029694, by rfl⟩ : syracuseStep 6706259 = 10059389) B10059389
theorem B4470839 : Blo 1985435 4470839 := bstep (se 1 (by rfl) ⟨3353129, by rfl⟩ : syracuseStep 4470839 = 6706259) B6706259
theorem B2980559 : Blo 1985435 2980559 := bstep (se 1 (by rfl) ⟨2235419, by rfl⟩ : syracuseStep 2980559 = 4470839) B4470839
theorem B1987039 : Blo 1985435 1987039 := bstep (se 1 (by rfl) ⟨1490279, by rfl⟩ : syracuseStep 1987039 = 2980559) B2980559
theorem B2980565 : Blo 1985435 2980565 := bbase (se 7 (by rfl) ⟨34928, by rfl⟩ : syracuseStep 2980565 = 69857) (by norm_num)
theorem B1987043 : Blo 1985435 1987043 := bstep (se 1 (by rfl) ⟨1490282, by rfl⟩ : syracuseStep 1987043 = 2980565) B2980565
theorem B16113269 : Blo 1985435 16113269 := bbase (se 5 (by rfl) ⟨755309, by rfl⟩ : syracuseStep 16113269 = 1510619) (by norm_num)
theorem B10742179 : Blo 1985435 10742179 := bstep (se 1 (by rfl) ⟨8056634, by rfl⟩ : syracuseStep 10742179 = 16113269) B16113269
theorem B14322905 : Blo 1985435 14322905 := bstep (se 2 (by rfl) ⟨5371089, by rfl⟩ : syracuseStep 14322905 = 10742179) B10742179
theorem B9548603 : Blo 1985435 9548603 := bstep (se 1 (by rfl) ⟨7161452, by rfl⟩ : syracuseStep 9548603 = 14322905) B14322905
theorem B6365735 : Blo 1985435 6365735 := bstep (se 1 (by rfl) ⟨4774301, by rfl⟩ : syracuseStep 6365735 = 9548603) B9548603
theorem B4243823 : Blo 1985435 4243823 := bstep (se 1 (by rfl) ⟨3182867, by rfl⟩ : syracuseStep 4243823 = 6365735) B6365735
theorem B2829215 : Blo 1985435 2829215 := bstep (se 1 (by rfl) ⟨2121911, by rfl⟩ : syracuseStep 2829215 = 4243823) B4243823
theorem B7544573 : Blo 1985435 7544573 := bstep (se 3 (by rfl) ⟨1414607, by rfl⟩ : syracuseStep 7544573 = 2829215) B2829215
theorem B5029715 : Blo 1985435 5029715 := bstep (se 1 (by rfl) ⟨3772286, by rfl⟩ : syracuseStep 5029715 = 7544573) B7544573
theorem B3353143 : Blo 1985435 3353143 := bstep (se 1 (by rfl) ⟨2514857, by rfl⟩ : syracuseStep 3353143 = 5029715) B5029715
theorem B4470857 : Blo 1985435 4470857 := bstep (se 2 (by rfl) ⟨1676571, by rfl⟩ : syracuseStep 4470857 = 3353143) B3353143
theorem B2980571 : Blo 1985435 2980571 := bstep (se 1 (by rfl) ⟨2235428, by rfl⟩ : syracuseStep 2980571 = 4470857) B4470857
theorem B1987047 : Blo 1985435 1987047 := bstep (se 1 (by rfl) ⟨1490285, by rfl⟩ : syracuseStep 1987047 = 2980571) B2980571
theorem B2235433 : Blo 1985435 2235433 := bbase (se 2 (by rfl) ⟨838287, by rfl⟩ : syracuseStep 2235433 = 1676575) (by norm_num)
theorem B2980577 : Blo 1985435 2980577 := bstep (se 2 (by rfl) ⟨1117716, by rfl⟩ : syracuseStep 2980577 = 2235433) B2235433
theorem B1987051 : Blo 1985435 1987051 := bstep (se 1 (by rfl) ⟨1490288, by rfl⟩ : syracuseStep 1987051 = 2980577) B2980577
theorem B22942613 : Blo 1985435 22942613 := bbase (se 6 (by rfl) ⟨537717, by rfl⟩ : syracuseStep 22942613 = 1075435) (by norm_num)
theorem B15295075 : Blo 1985435 15295075 := bstep (se 1 (by rfl) ⟨11471306, by rfl⟩ : syracuseStep 15295075 = 22942613) B22942613
theorem B81573733 : Blo 1985435 81573733 := bstep (se 4 (by rfl) ⟨7647537, by rfl⟩ : syracuseStep 81573733 = 15295075) B15295075
theorem B108764977 : Blo 1985435 108764977 := bstep (se 2 (by rfl) ⟨40786866, by rfl⟩ : syracuseStep 108764977 = 81573733) B81573733
theorem B145019969 : Blo 1985435 145019969 := bstep (se 2 (by rfl) ⟨54382488, by rfl⟩ : syracuseStep 145019969 = 108764977) B108764977
theorem B96679979 : Blo 1985435 96679979 := bstep (se 1 (by rfl) ⟨72509984, by rfl⟩ : syracuseStep 96679979 = 145019969) B145019969
theorem B64453319 : Blo 1985435 64453319 := bstep (se 1 (by rfl) ⟨48339989, by rfl⟩ : syracuseStep 64453319 = 96679979) B96679979
theorem B42968879 : Blo 1985435 42968879 := bstep (se 1 (by rfl) ⟨32226659, by rfl⟩ : syracuseStep 42968879 = 64453319) B64453319
theorem B28645919 : Blo 1985435 28645919 := bstep (se 1 (by rfl) ⟨21484439, by rfl⟩ : syracuseStep 28645919 = 42968879) B42968879
theorem B19097279 : Blo 1985435 19097279 := bstep (se 1 (by rfl) ⟨14322959, by rfl⟩ : syracuseStep 19097279 = 28645919) B28645919
theorem B12731519 : Blo 1985435 12731519 := bstep (se 1 (by rfl) ⟨9548639, by rfl⟩ : syracuseStep 12731519 = 19097279) B19097279
theorem B8487679 : Blo 1985435 8487679 := bstep (se 1 (by rfl) ⟨6365759, by rfl⟩ : syracuseStep 8487679 = 12731519) B12731519
theorem B11316905 : Blo 1985435 11316905 := bstep (se 2 (by rfl) ⟨4243839, by rfl⟩ : syracuseStep 11316905 = 8487679) B8487679
theorem B7544603 : Blo 1985435 7544603 := bstep (se 1 (by rfl) ⟨5658452, by rfl⟩ : syracuseStep 7544603 = 11316905) B11316905
theorem B5029735 : Blo 1985435 5029735 := bstep (se 1 (by rfl) ⟨3772301, by rfl⟩ : syracuseStep 5029735 = 7544603) B7544603
theorem B6706313 : Blo 1985435 6706313 := bstep (se 2 (by rfl) ⟨2514867, by rfl⟩ : syracuseStep 6706313 = 5029735) B5029735
theorem B4470875 : Blo 1985435 4470875 := bstep (se 1 (by rfl) ⟨3353156, by rfl⟩ : syracuseStep 4470875 = 6706313) B6706313
theorem B2980583 : Blo 1985435 2980583 := bstep (se 1 (by rfl) ⟨2235437, by rfl⟩ : syracuseStep 2980583 = 4470875) B4470875
theorem B1987055 : Blo 1985435 1987055 := bstep (se 1 (by rfl) ⟨1490291, by rfl⟩ : syracuseStep 1987055 = 2980583) B2980583
theorem B2980589 : Blo 1985435 2980589 := bbase (se 3 (by rfl) ⟨558860, by rfl⟩ : syracuseStep 2980589 = 1117721) (by norm_num)
theorem B1987059 : Blo 1985435 1987059 := bstep (se 1 (by rfl) ⟨1490294, by rfl⟩ : syracuseStep 1987059 = 2980589) B2980589
theorem B4470893 : Blo 1985435 4470893 := bbase (se 3 (by rfl) ⟨838292, by rfl⟩ : syracuseStep 4470893 = 1676585) (by norm_num)
theorem B2980595 : Blo 1985435 2980595 := bstep (se 1 (by rfl) ⟨2235446, by rfl⟩ : syracuseStep 2980595 = 4470893) B4470893
theorem B1987063 : Blo 1985435 1987063 := bstep (se 1 (by rfl) ⟨1490297, by rfl⟩ : syracuseStep 1987063 = 2980595) B2980595
theorem B3772325 : Blo 1985435 3772325 := bbase (se 4 (by rfl) ⟨353655, by rfl⟩ : syracuseStep 3772325 = 707311) (by norm_num)
theorem B2514883 : Blo 1985435 2514883 := bstep (se 1 (by rfl) ⟨1886162, by rfl⟩ : syracuseStep 2514883 = 3772325) B3772325
theorem B3353177 : Blo 1985435 3353177 := bstep (se 2 (by rfl) ⟨1257441, by rfl⟩ : syracuseStep 3353177 = 2514883) B2514883
theorem B2235451 : Blo 1985435 2235451 := bstep (se 1 (by rfl) ⟨1676588, by rfl⟩ : syracuseStep 2235451 = 3353177) B3353177
theorem B2980601 : Blo 1985435 2980601 := bstep (se 2 (by rfl) ⟨1117725, by rfl⟩ : syracuseStep 2980601 = 2235451) B2235451
theorem B1987067 : Blo 1985435 1987067 := bstep (se 1 (by rfl) ⟨1490300, by rfl⟩ : syracuseStep 1987067 = 2980601) B2980601
theorem B3398933 : Blo 1985435 3398933 := bbase (se 6 (by rfl) ⟨79662, by rfl⟩ : syracuseStep 3398933 = 159325) (by norm_num)
theorem B9063821 : Blo 1985435 9063821 := bstep (se 3 (by rfl) ⟨1699466, by rfl⟩ : syracuseStep 9063821 = 3398933) B3398933
theorem B6042547 : Blo 1985435 6042547 := bstep (se 1 (by rfl) ⟨4531910, by rfl⟩ : syracuseStep 6042547 = 9063821) B9063821
theorem B8056729 : Blo 1985435 8056729 := bstep (se 2 (by rfl) ⟨3021273, by rfl⟩ : syracuseStep 8056729 = 6042547) B6042547
theorem B10742305 : Blo 1985435 10742305 := bstep (se 2 (by rfl) ⟨4028364, by rfl⟩ : syracuseStep 10742305 = 8056729) B8056729
theorem B14323073 : Blo 1985435 14323073 := bstep (se 2 (by rfl) ⟨5371152, by rfl⟩ : syracuseStep 14323073 = 10742305) B10742305
theorem B38194861 : Blo 1985435 38194861 := bstep (se 3 (by rfl) ⟨7161536, by rfl⟩ : syracuseStep 38194861 = 14323073) B14323073
theorem B50926481 : Blo 1985435 50926481 := bstep (se 2 (by rfl) ⟨19097430, by rfl⟩ : syracuseStep 50926481 = 38194861) B38194861
theorem B33950987 : Blo 1985435 33950987 := bstep (se 1 (by rfl) ⟨25463240, by rfl⟩ : syracuseStep 33950987 = 50926481) B50926481
theorem B22633991 : Blo 1985435 22633991 := bstep (se 1 (by rfl) ⟨16975493, by rfl⟩ : syracuseStep 22633991 = 33950987) B33950987
theorem B15089327 : Blo 1985435 15089327 := bstep (se 1 (by rfl) ⟨11316995, by rfl⟩ : syracuseStep 15089327 = 22633991) B22633991
theorem B10059551 : Blo 1985435 10059551 := bstep (se 1 (by rfl) ⟨7544663, by rfl⟩ : syracuseStep 10059551 = 15089327) B15089327
theorem B6706367 : Blo 1985435 6706367 := bstep (se 1 (by rfl) ⟨5029775, by rfl⟩ : syracuseStep 6706367 = 10059551) B10059551
theorem B4470911 : Blo 1985435 4470911 := bstep (se 1 (by rfl) ⟨3353183, by rfl⟩ : syracuseStep 4470911 = 6706367) B6706367
theorem B2980607 : Blo 1985435 2980607 := bstep (se 1 (by rfl) ⟨2235455, by rfl⟩ : syracuseStep 2980607 = 4470911) B4470911
theorem B1987071 : Blo 1985435 1987071 := bstep (se 1 (by rfl) ⟨1490303, by rfl⟩ : syracuseStep 1987071 = 2980607) B2980607
theorem B2980613 : Blo 1985435 2980613 := bbase (se 4 (by rfl) ⟨279432, by rfl⟩ : syracuseStep 2980613 = 558865) (by norm_num)
theorem B1987075 : Blo 1985435 1987075 := bstep (se 1 (by rfl) ⟨1490306, by rfl⟩ : syracuseStep 1987075 = 2980613) B2980613
theorem B3353197 : Blo 1985435 3353197 := bbase (se 3 (by rfl) ⟨628724, by rfl⟩ : syracuseStep 3353197 = 1257449) (by norm_num)
theorem B4470929 : Blo 1985435 4470929 := bstep (se 2 (by rfl) ⟨1676598, by rfl⟩ : syracuseStep 4470929 = 3353197) B3353197
theorem B2980619 : Blo 1985435 2980619 := bstep (se 1 (by rfl) ⟨2235464, by rfl⟩ : syracuseStep 2980619 = 4470929) B4470929
theorem B1987079 : Blo 1985435 1987079 := bstep (se 1 (by rfl) ⟨1490309, by rfl⟩ : syracuseStep 1987079 = 2980619) B2980619
theorem B2235469 : Blo 1985435 2235469 := bbase (se 3 (by rfl) ⟨419150, by rfl⟩ : syracuseStep 2235469 = 838301) (by norm_num)
theorem B2980625 : Blo 1985435 2980625 := bstep (se 2 (by rfl) ⟨1117734, by rfl⟩ : syracuseStep 2980625 = 2235469) B2235469
theorem B1987083 : Blo 1985435 1987083 := bstep (se 1 (by rfl) ⟨1490312, by rfl⟩ : syracuseStep 1987083 = 2980625) B2980625
theorem B6706421 : Blo 1985435 6706421 := bbase (se 5 (by rfl) ⟨314363, by rfl⟩ : syracuseStep 6706421 = 628727) (by norm_num)
theorem B4470947 : Blo 1985435 4470947 := bstep (se 1 (by rfl) ⟨3353210, by rfl⟩ : syracuseStep 4470947 = 6706421) B6706421
theorem B2980631 : Blo 1985435 2980631 := bstep (se 1 (by rfl) ⟨2235473, by rfl⟩ : syracuseStep 2980631 = 4470947) B4470947
theorem B1987087 : Blo 1985435 1987087 := bstep (se 1 (by rfl) ⟨1490315, by rfl⟩ : syracuseStep 1987087 = 2980631) B2980631
theorem B2980637 : Blo 1985435 2980637 := bbase (se 3 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 2980637 = 1117739) (by norm_num)
theorem B1987091 : Blo 1985435 1987091 := bstep (se 1 (by rfl) ⟨1490318, by rfl⟩ : syracuseStep 1987091 = 2980637) B2980637
theorem B4470965 : Blo 1985435 4470965 := bbase (se 5 (by rfl) ⟨209576, by rfl⟩ : syracuseStep 4470965 = 419153) (by norm_num)
theorem B2980643 : Blo 1985435 2980643 := bstep (se 1 (by rfl) ⟨2235482, by rfl⟩ : syracuseStep 2980643 = 4470965) B4470965
theorem B1987095 : Blo 1985435 1987095 := bstep (se 1 (by rfl) ⟨1490321, by rfl⟩ : syracuseStep 1987095 = 2980643) B2980643
theorem B2549237 : Blo 1985435 2549237 := bbase (se 5 (by rfl) ⟨119495, by rfl⟩ : syracuseStep 2549237 = 238991) (by norm_num)
theorem B27191861 : Blo 1985435 27191861 := bstep (se 5 (by rfl) ⟨1274618, by rfl⟩ : syracuseStep 27191861 = 2549237) B2549237
theorem B18127907 : Blo 1985435 18127907 := bstep (se 1 (by rfl) ⟨13595930, by rfl⟩ : syracuseStep 18127907 = 27191861) B27191861
theorem B12085271 : Blo 1985435 12085271 := bstep (se 1 (by rfl) ⟨9063953, by rfl⟩ : syracuseStep 12085271 = 18127907) B18127907
theorem B8056847 : Blo 1985435 8056847 := bstep (se 1 (by rfl) ⟨6042635, by rfl⟩ : syracuseStep 8056847 = 12085271) B12085271
theorem B5371231 : Blo 1985435 5371231 := bstep (se 1 (by rfl) ⟨4028423, by rfl⟩ : syracuseStep 5371231 = 8056847) B8056847
theorem B7161641 : Blo 1985435 7161641 := bstep (se 2 (by rfl) ⟨2685615, by rfl⟩ : syracuseStep 7161641 = 5371231) B5371231
theorem B4774427 : Blo 1985435 4774427 := bstep (se 1 (by rfl) ⟨3580820, by rfl⟩ : syracuseStep 4774427 = 7161641) B7161641
theorem B3182951 : Blo 1985435 3182951 := bstep (se 1 (by rfl) ⟨2387213, by rfl⟩ : syracuseStep 3182951 = 4774427) B4774427
theorem B2121967 : Blo 1985435 2121967 := bstep (se 1 (by rfl) ⟨1591475, by rfl⟩ : syracuseStep 2121967 = 3182951) B3182951
theorem B11317157 : Blo 1985435 11317157 := bstep (se 4 (by rfl) ⟨1060983, by rfl⟩ : syracuseStep 11317157 = 2121967) B2121967
theorem B7544771 : Blo 1985435 7544771 := bstep (se 1 (by rfl) ⟨5658578, by rfl⟩ : syracuseStep 7544771 = 11317157) B11317157
theorem B5029847 : Blo 1985435 5029847 := bstep (se 1 (by rfl) ⟨3772385, by rfl⟩ : syracuseStep 5029847 = 7544771) B7544771
theorem B3353231 : Blo 1985435 3353231 := bstep (se 1 (by rfl) ⟨2514923, by rfl⟩ : syracuseStep 3353231 = 5029847) B5029847
theorem B2235487 : Blo 1985435 2235487 := bstep (se 1 (by rfl) ⟨1676615, by rfl⟩ : syracuseStep 2235487 = 3353231) B3353231
theorem B2980649 : Blo 1985435 2980649 := bstep (se 2 (by rfl) ⟨1117743, by rfl⟩ : syracuseStep 2980649 = 2235487) B2235487
theorem B1987099 : Blo 1985435 1987099 := bstep (se 1 (by rfl) ⟨1490324, by rfl⟩ : syracuseStep 1987099 = 2980649) B2980649
theorem B3182957 : Blo 1985435 3182957 := bbase (se 3 (by rfl) ⟨596804, by rfl⟩ : syracuseStep 3182957 = 1193609) (by norm_num)
theorem B2121971 : Blo 1985435 2121971 := bstep (se 1 (by rfl) ⟨1591478, by rfl⟩ : syracuseStep 2121971 = 3182957) B3182957
theorem B5658589 : Blo 1985435 5658589 := bstep (se 3 (by rfl) ⟨1060985, by rfl⟩ : syracuseStep 5658589 = 2121971) B2121971
theorem B7544785 : Blo 1985435 7544785 := bstep (se 2 (by rfl) ⟨2829294, by rfl⟩ : syracuseStep 7544785 = 5658589) B5658589
theorem B10059713 : Blo 1985435 10059713 := bstep (se 2 (by rfl) ⟨3772392, by rfl⟩ : syracuseStep 10059713 = 7544785) B7544785
theorem B6706475 : Blo 1985435 6706475 := bstep (se 1 (by rfl) ⟨5029856, by rfl⟩ : syracuseStep 6706475 = 10059713) B10059713
theorem B4470983 : Blo 1985435 4470983 := bstep (se 1 (by rfl) ⟨3353237, by rfl⟩ : syracuseStep 4470983 = 6706475) B6706475
theorem B2980655 : Blo 1985435 2980655 := bstep (se 1 (by rfl) ⟨2235491, by rfl⟩ : syracuseStep 2980655 = 4470983) B4470983
theorem B1987103 : Blo 1985435 1987103 := bstep (se 1 (by rfl) ⟨1490327, by rfl⟩ : syracuseStep 1987103 = 2980655) B2980655
theorem B2980661 : Blo 1985435 2980661 := bbase (se 5 (by rfl) ⟨139718, by rfl⟩ : syracuseStep 2980661 = 279437) (by norm_num)
theorem B1987107 : Blo 1985435 1987107 := bstep (se 1 (by rfl) ⟨1490330, by rfl⟩ : syracuseStep 1987107 = 2980661) B2980661
theorem B5029877 : Blo 1985435 5029877 := bbase (se 5 (by rfl) ⟨235775, by rfl⟩ : syracuseStep 5029877 = 471551) (by norm_num)
theorem B3353251 : Blo 1985435 3353251 := bstep (se 1 (by rfl) ⟨2514938, by rfl⟩ : syracuseStep 3353251 = 5029877) B5029877
theorem B4471001 : Blo 1985435 4471001 := bstep (se 2 (by rfl) ⟨1676625, by rfl⟩ : syracuseStep 4471001 = 3353251) B3353251
theorem B2980667 : Blo 1985435 2980667 := bstep (se 1 (by rfl) ⟨2235500, by rfl⟩ : syracuseStep 2980667 = 4471001) B4471001
theorem B1987111 : Blo 1985435 1987111 := bstep (se 1 (by rfl) ⟨1490333, by rfl⟩ : syracuseStep 1987111 = 2980667) B2980667
theorem B2235505 : Blo 1985435 2235505 := bbase (se 2 (by rfl) ⟨838314, by rfl⟩ : syracuseStep 2235505 = 1676629) (by norm_num)
theorem B2980673 : Blo 1985435 2980673 := bstep (se 2 (by rfl) ⟨1117752, by rfl⟩ : syracuseStep 2980673 = 2235505) B2235505
theorem B1987115 : Blo 1985435 1987115 := bstep (se 1 (by rfl) ⟨1490336, by rfl⟩ : syracuseStep 1987115 = 2980673) B2980673
theorem B2387237 : Blo 1985435 2387237 := bbase (se 4 (by rfl) ⟨223803, by rfl⟩ : syracuseStep 2387237 = 447607) (by norm_num)
theorem B6365965 : Blo 1985435 6365965 := bstep (se 3 (by rfl) ⟨1193618, by rfl⟩ : syracuseStep 6365965 = 2387237) B2387237
theorem B8487953 : Blo 1985435 8487953 := bstep (se 2 (by rfl) ⟨3182982, by rfl⟩ : syracuseStep 8487953 = 6365965) B6365965
theorem B5658635 : Blo 1985435 5658635 := bstep (se 1 (by rfl) ⟨4243976, by rfl⟩ : syracuseStep 5658635 = 8487953) B8487953
theorem B3772423 : Blo 1985435 3772423 := bstep (se 1 (by rfl) ⟨2829317, by rfl⟩ : syracuseStep 3772423 = 5658635) B5658635
theorem B5029897 : Blo 1985435 5029897 := bstep (se 2 (by rfl) ⟨1886211, by rfl⟩ : syracuseStep 5029897 = 3772423) B3772423
theorem B6706529 : Blo 1985435 6706529 := bstep (se 2 (by rfl) ⟨2514948, by rfl⟩ : syracuseStep 6706529 = 5029897) B5029897
theorem B4471019 : Blo 1985435 4471019 := bstep (se 1 (by rfl) ⟨3353264, by rfl⟩ : syracuseStep 4471019 = 6706529) B6706529
theorem B2980679 : Blo 1985435 2980679 := bstep (se 1 (by rfl) ⟨2235509, by rfl⟩ : syracuseStep 2980679 = 4471019) B4471019
theorem B1987119 : Blo 1985435 1987119 := bstep (se 1 (by rfl) ⟨1490339, by rfl⟩ : syracuseStep 1987119 = 2980679) B2980679
theorem B2980685 : Blo 1985435 2980685 := bbase (se 3 (by rfl) ⟨558878, by rfl⟩ : syracuseStep 2980685 = 1117757) (by norm_num)
theorem B1987123 : Blo 1985435 1987123 := bstep (se 1 (by rfl) ⟨1490342, by rfl⟩ : syracuseStep 1987123 = 2980685) B2980685
theorem B4471037 : Blo 1985435 4471037 := bbase (se 3 (by rfl) ⟨838319, by rfl⟩ : syracuseStep 4471037 = 1676639) (by norm_num)
theorem B2980691 : Blo 1985435 2980691 := bstep (se 1 (by rfl) ⟨2235518, by rfl⟩ : syracuseStep 2980691 = 4471037) B4471037
theorem B1987127 : Blo 1985435 1987127 := bstep (se 1 (by rfl) ⟨1490345, by rfl⟩ : syracuseStep 1987127 = 2980691) B2980691
theorem B3353285 : Blo 1985435 3353285 := bbase (se 4 (by rfl) ⟨314370, by rfl⟩ : syracuseStep 3353285 = 628741) (by norm_num)
theorem B2235523 : Blo 1985435 2235523 := bstep (se 1 (by rfl) ⟨1676642, by rfl⟩ : syracuseStep 2235523 = 3353285) B3353285
theorem B2980697 : Blo 1985435 2980697 := bstep (se 2 (by rfl) ⟨1117761, by rfl⟩ : syracuseStep 2980697 = 2235523) B2235523
theorem B1987131 : Blo 1985435 1987131 := bstep (se 1 (by rfl) ⟨1490348, by rfl⟩ : syracuseStep 1987131 = 2980697) B2980697
theorem B15089813 : Blo 1985435 15089813 := bbase (se 6 (by rfl) ⟨353667, by rfl⟩ : syracuseStep 15089813 = 707335) (by norm_num)
theorem B10059875 : Blo 1985435 10059875 := bstep (se 1 (by rfl) ⟨7544906, by rfl⟩ : syracuseStep 10059875 = 15089813) B15089813
theorem B6706583 : Blo 1985435 6706583 := bstep (se 1 (by rfl) ⟨5029937, by rfl⟩ : syracuseStep 6706583 = 10059875) B10059875
theorem B4471055 : Blo 1985435 4471055 := bstep (se 1 (by rfl) ⟨3353291, by rfl⟩ : syracuseStep 4471055 = 6706583) B6706583
theorem B2980703 : Blo 1985435 2980703 := bstep (se 1 (by rfl) ⟨2235527, by rfl⟩ : syracuseStep 2980703 = 4471055) B4471055
theorem B1987135 : Blo 1985435 1987135 := bstep (se 1 (by rfl) ⟨1490351, by rfl⟩ : syracuseStep 1987135 = 2980703) B2980703
theorem B2980709 : Blo 1985435 2980709 := bbase (se 4 (by rfl) ⟨279441, by rfl⟩ : syracuseStep 2980709 = 558883) (by norm_num)
theorem B1987139 : Blo 1985435 1987139 := bstep (se 1 (by rfl) ⟨1490354, by rfl⟩ : syracuseStep 1987139 = 2980709) B2980709
theorem B3772469 : Blo 1985435 3772469 := bbase (se 5 (by rfl) ⟨176834, by rfl⟩ : syracuseStep 3772469 = 353669) (by norm_num)
theorem B2514979 : Blo 1985435 2514979 := bstep (se 1 (by rfl) ⟨1886234, by rfl⟩ : syracuseStep 2514979 = 3772469) B3772469
theorem B3353305 : Blo 1985435 3353305 := bstep (se 2 (by rfl) ⟨1257489, by rfl⟩ : syracuseStep 3353305 = 2514979) B2514979
theorem B4471073 : Blo 1985435 4471073 := bstep (se 2 (by rfl) ⟨1676652, by rfl⟩ : syracuseStep 4471073 = 3353305) B3353305
theorem B2980715 : Blo 1985435 2980715 := bstep (se 1 (by rfl) ⟨2235536, by rfl⟩ : syracuseStep 2980715 = 4471073) B4471073
theorem B1987143 : Blo 1985435 1987143 := bstep (se 1 (by rfl) ⟨1490357, by rfl⟩ : syracuseStep 1987143 = 2980715) B2980715
theorem B2235541 : Blo 1985435 2235541 := bbase (se 6 (by rfl) ⟨52395, by rfl⟩ : syracuseStep 2235541 = 104791) (by norm_num)
theorem B2980721 : Blo 1985435 2980721 := bstep (se 2 (by rfl) ⟨1117770, by rfl⟩ : syracuseStep 2980721 = 2235541) B2235541
theorem B1987147 : Blo 1985435 1987147 := bstep (se 1 (by rfl) ⟨1490360, by rfl⟩ : syracuseStep 1987147 = 2980721) B2980721
theorem B2514989 : Blo 1985435 2514989 := bbase (se 3 (by rfl) ⟨471560, by rfl⟩ : syracuseStep 2514989 = 943121) (by norm_num)
theorem B6706637 : Blo 1985435 6706637 := bstep (se 3 (by rfl) ⟨1257494, by rfl⟩ : syracuseStep 6706637 = 2514989) B2514989
theorem B4471091 : Blo 1985435 4471091 := bstep (se 1 (by rfl) ⟨3353318, by rfl⟩ : syracuseStep 4471091 = 6706637) B6706637
theorem B2980727 : Blo 1985435 2980727 := bstep (se 1 (by rfl) ⟨2235545, by rfl⟩ : syracuseStep 2980727 = 4471091) B4471091
theorem B1987151 : Blo 1985435 1987151 := bstep (se 1 (by rfl) ⟨1490363, by rfl⟩ : syracuseStep 1987151 = 2980727) B2980727
theorem B2980733 : Blo 1985435 2980733 := bbase (se 3 (by rfl) ⟨558887, by rfl⟩ : syracuseStep 2980733 = 1117775) (by norm_num)
theorem B1987155 : Blo 1985435 1987155 := bstep (se 1 (by rfl) ⟨1490366, by rfl⟩ : syracuseStep 1987155 = 2980733) B2980733
theorem B4471109 : Blo 1985435 4471109 := bbase (se 4 (by rfl) ⟨419166, by rfl⟩ : syracuseStep 4471109 = 838333) (by norm_num)
theorem B2980739 : Blo 1985435 2980739 := bstep (se 1 (by rfl) ⟨2235554, by rfl⟩ : syracuseStep 2980739 = 4471109) B4471109
theorem B1987159 : Blo 1985435 1987159 := bstep (se 1 (by rfl) ⟨1490369, by rfl⟩ : syracuseStep 1987159 = 2980739) B2980739
theorem B2266061 : Blo 1985435 2266061 := bbase (se 3 (by rfl) ⟨424886, by rfl⟩ : syracuseStep 2266061 = 849773) (by norm_num)
theorem B24171317 : Blo 1985435 24171317 := bstep (se 5 (by rfl) ⟨1133030, by rfl⟩ : syracuseStep 24171317 = 2266061) B2266061
theorem B16114211 : Blo 1985435 16114211 := bstep (se 1 (by rfl) ⟨12085658, by rfl⟩ : syracuseStep 16114211 = 24171317) B24171317
theorem B10742807 : Blo 1985435 10742807 := bstep (se 1 (by rfl) ⟨8057105, by rfl⟩ : syracuseStep 10742807 = 16114211) B16114211
theorem B7161871 : Blo 1985435 7161871 := bstep (se 1 (by rfl) ⟨5371403, by rfl⟩ : syracuseStep 7161871 = 10742807) B10742807
theorem B9549161 : Blo 1985435 9549161 := bstep (se 2 (by rfl) ⟨3580935, by rfl⟩ : syracuseStep 9549161 = 7161871) B7161871
theorem B6366107 : Blo 1985435 6366107 := bstep (se 1 (by rfl) ⟨4774580, by rfl⟩ : syracuseStep 6366107 = 9549161) B9549161
theorem B4244071 : Blo 1985435 4244071 := bstep (se 1 (by rfl) ⟨3183053, by rfl⟩ : syracuseStep 4244071 = 6366107) B6366107
theorem B5658761 : Blo 1985435 5658761 := bstep (se 2 (by rfl) ⟨2122035, by rfl⟩ : syracuseStep 5658761 = 4244071) B4244071
theorem B3772507 : Blo 1985435 3772507 := bstep (se 1 (by rfl) ⟨2829380, by rfl⟩ : syracuseStep 3772507 = 5658761) B5658761
theorem B5030009 : Blo 1985435 5030009 := bstep (se 2 (by rfl) ⟨1886253, by rfl⟩ : syracuseStep 5030009 = 3772507) B3772507
theorem B3353339 : Blo 1985435 3353339 := bstep (se 1 (by rfl) ⟨2515004, by rfl⟩ : syracuseStep 3353339 = 5030009) B5030009
theorem B2235559 : Blo 1985435 2235559 := bstep (se 1 (by rfl) ⟨1676669, by rfl⟩ : syracuseStep 2235559 = 3353339) B3353339
theorem B2980745 : Blo 1985435 2980745 := bstep (se 2 (by rfl) ⟨1117779, by rfl⟩ : syracuseStep 2980745 = 2235559) B2235559
theorem B1987163 : Blo 1985435 1987163 := bstep (se 1 (by rfl) ⟨1490372, by rfl⟩ : syracuseStep 1987163 = 2980745) B2980745
theorem B10060037 : Blo 1985435 10060037 := bbase (se 4 (by rfl) ⟨943128, by rfl⟩ : syracuseStep 10060037 = 1886257) (by norm_num)
theorem B6706691 : Blo 1985435 6706691 := bstep (se 1 (by rfl) ⟨5030018, by rfl⟩ : syracuseStep 6706691 = 10060037) B10060037
theorem B4471127 : Blo 1985435 4471127 := bstep (se 1 (by rfl) ⟨3353345, by rfl⟩ : syracuseStep 4471127 = 6706691) B6706691
theorem B2980751 : Blo 1985435 2980751 := bstep (se 1 (by rfl) ⟨2235563, by rfl⟩ : syracuseStep 2980751 = 4471127) B4471127
theorem B1987167 : Blo 1985435 1987167 := bstep (se 1 (by rfl) ⟨1490375, by rfl⟩ : syracuseStep 1987167 = 2980751) B2980751
theorem B2980757 : Blo 1985435 2980757 := bbase (se 6 (by rfl) ⟨69861, by rfl⟩ : syracuseStep 2980757 = 139723) (by norm_num)
theorem B1987171 : Blo 1985435 1987171 := bstep (se 1 (by rfl) ⟨1490378, by rfl⟩ : syracuseStep 1987171 = 2980757) B2980757
theorem B11317589 : Blo 1985435 11317589 := bbase (se 10 (by rfl) ⟨16578, by rfl⟩ : syracuseStep 11317589 = 33157) (by norm_num)
theorem B7545059 : Blo 1985435 7545059 := bstep (se 1 (by rfl) ⟨5658794, by rfl⟩ : syracuseStep 7545059 = 11317589) B11317589
theorem B5030039 : Blo 1985435 5030039 := bstep (se 1 (by rfl) ⟨3772529, by rfl⟩ : syracuseStep 5030039 = 7545059) B7545059
theorem B3353359 : Blo 1985435 3353359 := bstep (se 1 (by rfl) ⟨2515019, by rfl⟩ : syracuseStep 3353359 = 5030039) B5030039
theorem B4471145 : Blo 1985435 4471145 := bstep (se 2 (by rfl) ⟨1676679, by rfl⟩ : syracuseStep 4471145 = 3353359) B3353359
theorem B2980763 : Blo 1985435 2980763 := bstep (se 1 (by rfl) ⟨2235572, by rfl⟩ : syracuseStep 2980763 = 4471145) B4471145
theorem B1987175 : Blo 1985435 1987175 := bstep (se 1 (by rfl) ⟨1490381, by rfl⟩ : syracuseStep 1987175 = 2980763) B2980763
theorem B2235577 : Blo 1985435 2235577 := bbase (se 2 (by rfl) ⟨838341, by rfl⟩ : syracuseStep 2235577 = 1676683) (by norm_num)
theorem B2980769 : Blo 1985435 2980769 := bstep (se 2 (by rfl) ⟨1117788, by rfl⟩ : syracuseStep 2980769 = 2235577) B2235577
theorem B1987179 : Blo 1985435 1987179 := bstep (se 1 (by rfl) ⟨1490384, by rfl⟩ : syracuseStep 1987179 = 2980769) B2980769
theorem B3183085 : Blo 1985435 3183085 := bbase (se 3 (by rfl) ⟨596828, by rfl⟩ : syracuseStep 3183085 = 1193657) (by norm_num)
theorem B4244113 : Blo 1985435 4244113 := bstep (se 2 (by rfl) ⟨1591542, by rfl⟩ : syracuseStep 4244113 = 3183085) B3183085
theorem B5658817 : Blo 1985435 5658817 := bstep (se 2 (by rfl) ⟨2122056, by rfl⟩ : syracuseStep 5658817 = 4244113) B4244113
theorem B7545089 : Blo 1985435 7545089 := bstep (se 2 (by rfl) ⟨2829408, by rfl⟩ : syracuseStep 7545089 = 5658817) B5658817
theorem B5030059 : Blo 1985435 5030059 := bstep (se 1 (by rfl) ⟨3772544, by rfl⟩ : syracuseStep 5030059 = 7545089) B7545089
theorem B6706745 : Blo 1985435 6706745 := bstep (se 2 (by rfl) ⟨2515029, by rfl⟩ : syracuseStep 6706745 = 5030059) B5030059
theorem B4471163 : Blo 1985435 4471163 := bstep (se 1 (by rfl) ⟨3353372, by rfl⟩ : syracuseStep 4471163 = 6706745) B6706745
theorem B2980775 : Blo 1985435 2980775 := bstep (se 1 (by rfl) ⟨2235581, by rfl⟩ : syracuseStep 2980775 = 4471163) B4471163
theorem B1987183 : Blo 1985435 1987183 := bstep (se 1 (by rfl) ⟨1490387, by rfl⟩ : syracuseStep 1987183 = 2980775) B2980775
theorem B2980781 : Blo 1985435 2980781 := bbase (se 3 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 2980781 = 1117793) (by norm_num)
theorem B1987187 : Blo 1985435 1987187 := bstep (se 1 (by rfl) ⟨1490390, by rfl⟩ : syracuseStep 1987187 = 2980781) B2980781
theorem B4471181 : Blo 1985435 4471181 := bbase (se 3 (by rfl) ⟨838346, by rfl⟩ : syracuseStep 4471181 = 1676693) (by norm_num)
theorem B2980787 : Blo 1985435 2980787 := bstep (se 1 (by rfl) ⟨2235590, by rfl⟩ : syracuseStep 2980787 = 4471181) B4471181
theorem B1987191 : Blo 1985435 1987191 := bstep (se 1 (by rfl) ⟨1490393, by rfl⟩ : syracuseStep 1987191 = 2980787) B2980787
theorem B2515045 : Blo 1985435 2515045 := bbase (se 4 (by rfl) ⟨235785, by rfl⟩ : syracuseStep 2515045 = 471571) (by norm_num)
theorem B3353393 : Blo 1985435 3353393 := bstep (se 2 (by rfl) ⟨1257522, by rfl⟩ : syracuseStep 3353393 = 2515045) B2515045
theorem B2235595 : Blo 1985435 2235595 := bstep (se 1 (by rfl) ⟨1676696, by rfl⟩ : syracuseStep 2235595 = 3353393) B3353393
theorem B2980793 : Blo 1985435 2980793 := bstep (se 2 (by rfl) ⟨1117797, by rfl⟩ : syracuseStep 2980793 = 2235595) B2235595
theorem B1987195 : Blo 1985435 1987195 := bstep (se 1 (by rfl) ⟨1490396, by rfl⟩ : syracuseStep 1987195 = 2980793) B2980793
theorem B9679621 : Blo 1985435 9679621 := bbase (se 4 (by rfl) ⟨907464, by rfl⟩ : syracuseStep 9679621 = 1814929) (by norm_num)
theorem B12906161 : Blo 1985435 12906161 := bstep (se 2 (by rfl) ⟨4839810, by rfl⟩ : syracuseStep 12906161 = 9679621) B9679621
theorem B8604107 : Blo 1985435 8604107 := bstep (se 1 (by rfl) ⟨6453080, by rfl⟩ : syracuseStep 8604107 = 12906161) B12906161
theorem B5736071 : Blo 1985435 5736071 := bstep (se 1 (by rfl) ⟨4302053, by rfl⟩ : syracuseStep 5736071 = 8604107) B8604107
theorem B3824047 : Blo 1985435 3824047 := bstep (se 1 (by rfl) ⟨2868035, by rfl⟩ : syracuseStep 3824047 = 5736071) B5736071
theorem B5098729 : Blo 1985435 5098729 := bstep (se 2 (by rfl) ⟨1912023, by rfl⟩ : syracuseStep 5098729 = 3824047) B3824047
theorem B6798305 : Blo 1985435 6798305 := bstep (se 2 (by rfl) ⟨2549364, by rfl⟩ : syracuseStep 6798305 = 5098729) B5098729
theorem B4532203 : Blo 1985435 4532203 := bstep (se 1 (by rfl) ⟨3399152, by rfl⟩ : syracuseStep 4532203 = 6798305) B6798305
theorem B6042937 : Blo 1985435 6042937 := bstep (se 2 (by rfl) ⟨2266101, by rfl⟩ : syracuseStep 6042937 = 4532203) B4532203
theorem B8057249 : Blo 1985435 8057249 := bstep (se 2 (by rfl) ⟨3021468, by rfl⟩ : syracuseStep 8057249 = 6042937) B6042937
theorem B5371499 : Blo 1985435 5371499 := bstep (se 1 (by rfl) ⟨4028624, by rfl⟩ : syracuseStep 5371499 = 8057249) B8057249
theorem B3580999 : Blo 1985435 3580999 := bstep (se 1 (by rfl) ⟨2685749, by rfl⟩ : syracuseStep 3580999 = 5371499) B5371499
theorem B19098661 : Blo 1985435 19098661 := bstep (se 4 (by rfl) ⟨1790499, by rfl⟩ : syracuseStep 19098661 = 3580999) B3580999
theorem B25464881 : Blo 1985435 25464881 := bstep (se 2 (by rfl) ⟨9549330, by rfl⟩ : syracuseStep 25464881 = 19098661) B19098661
theorem B16976587 : Blo 1985435 16976587 := bstep (se 1 (by rfl) ⟨12732440, by rfl⟩ : syracuseStep 16976587 = 25464881) B25464881
theorem B22635449 : Blo 1985435 22635449 := bstep (se 2 (by rfl) ⟨8488293, by rfl⟩ : syracuseStep 22635449 = 16976587) B16976587
theorem B15090299 : Blo 1985435 15090299 := bstep (se 1 (by rfl) ⟨11317724, by rfl⟩ : syracuseStep 15090299 = 22635449) B22635449
theorem B10060199 : Blo 1985435 10060199 := bstep (se 1 (by rfl) ⟨7545149, by rfl⟩ : syracuseStep 10060199 = 15090299) B15090299
theorem B6706799 : Blo 1985435 6706799 := bstep (se 1 (by rfl) ⟨5030099, by rfl⟩ : syracuseStep 6706799 = 10060199) B10060199
theorem B4471199 : Blo 1985435 4471199 := bstep (se 1 (by rfl) ⟨3353399, by rfl⟩ : syracuseStep 4471199 = 6706799) B6706799
theorem B2980799 : Blo 1985435 2980799 := bstep (se 1 (by rfl) ⟨2235599, by rfl⟩ : syracuseStep 2980799 = 4471199) B4471199
theorem B1987199 : Blo 1985435 1987199 := bstep (se 1 (by rfl) ⟨1490399, by rfl⟩ : syracuseStep 1987199 = 2980799) B2980799
theorem B2980805 : Blo 1985435 2980805 := bbase (se 4 (by rfl) ⟨279450, by rfl⟩ : syracuseStep 2980805 = 558901) (by norm_num)
theorem B1987203 : Blo 1985435 1987203 := bstep (se 1 (by rfl) ⟨1490402, by rfl⟩ : syracuseStep 1987203 = 2980805) B2980805
theorem B3353413 : Blo 1985435 3353413 := bbase (se 4 (by rfl) ⟨314382, by rfl⟩ : syracuseStep 3353413 = 628765) (by norm_num)
theorem B4471217 : Blo 1985435 4471217 := bstep (se 2 (by rfl) ⟨1676706, by rfl⟩ : syracuseStep 4471217 = 3353413) B3353413
theorem B2980811 : Blo 1985435 2980811 := bstep (se 1 (by rfl) ⟨2235608, by rfl⟩ : syracuseStep 2980811 = 4471217) B4471217
theorem B1987207 : Blo 1985435 1987207 := bstep (se 1 (by rfl) ⟨1490405, by rfl⟩ : syracuseStep 1987207 = 2980811) B2980811
theorem B2235613 : Blo 1985435 2235613 := bbase (se 3 (by rfl) ⟨419177, by rfl⟩ : syracuseStep 2235613 = 838355) (by norm_num)
theorem B2980817 : Blo 1985435 2980817 := bstep (se 2 (by rfl) ⟨1117806, by rfl⟩ : syracuseStep 2980817 = 2235613) B2235613
theorem B1987211 : Blo 1985435 1987211 := bstep (se 1 (by rfl) ⟨1490408, by rfl⟩ : syracuseStep 1987211 = 2980817) B2980817
theorem B6706853 : Blo 1985435 6706853 := bbase (se 4 (by rfl) ⟨628767, by rfl⟩ : syracuseStep 6706853 = 1257535) (by norm_num)
theorem B4471235 : Blo 1985435 4471235 := bstep (se 1 (by rfl) ⟨3353426, by rfl⟩ : syracuseStep 4471235 = 6706853) B6706853
theorem B2980823 : Blo 1985435 2980823 := bstep (se 1 (by rfl) ⟨2235617, by rfl⟩ : syracuseStep 2980823 = 4471235) B4471235
theorem B1987215 : Blo 1985435 1987215 := bstep (se 1 (by rfl) ⟨1490411, by rfl⟩ : syracuseStep 1987215 = 2980823) B2980823
theorem B2980829 : Blo 1985435 2980829 := bbase (se 3 (by rfl) ⟨558905, by rfl⟩ : syracuseStep 2980829 = 1117811) (by norm_num)
theorem B1987219 : Blo 1985435 1987219 := bstep (se 1 (by rfl) ⟨1490414, by rfl⟩ : syracuseStep 1987219 = 2980829) B2980829
theorem B4471253 : Blo 1985435 4471253 := bbase (se 7 (by rfl) ⟨52397, by rfl⟩ : syracuseStep 4471253 = 104795) (by norm_num)
theorem B2980835 : Blo 1985435 2980835 := bstep (se 1 (by rfl) ⟨2235626, by rfl⟩ : syracuseStep 2980835 = 4471253) B4471253
theorem B1987223 : Blo 1985435 1987223 := bstep (se 1 (by rfl) ⟨1490417, by rfl⟩ : syracuseStep 1987223 = 2980835) B2980835
theorem B3629909 : Blo 1985435 3629909 := bbase (se 9 (by rfl) ⟨10634, by rfl⟩ : syracuseStep 3629909 = 21269) (by norm_num)
theorem B2419939 : Blo 1985435 2419939 := bstep (se 1 (by rfl) ⟨1814954, by rfl⟩ : syracuseStep 2419939 = 3629909) B3629909
theorem B12906341 : Blo 1985435 12906341 := bstep (se 4 (by rfl) ⟨1209969, by rfl⟩ : syracuseStep 12906341 = 2419939) B2419939
theorem B8604227 : Blo 1985435 8604227 := bstep (se 1 (by rfl) ⟨6453170, by rfl⟩ : syracuseStep 8604227 = 12906341) B12906341
theorem B5736151 : Blo 1985435 5736151 := bstep (se 1 (by rfl) ⟨4302113, by rfl⟩ : syracuseStep 5736151 = 8604227) B8604227
theorem B7648201 : Blo 1985435 7648201 := bstep (se 2 (by rfl) ⟨2868075, by rfl⟩ : syracuseStep 7648201 = 5736151) B5736151
theorem B40790405 : Blo 1985435 40790405 := bstep (se 4 (by rfl) ⟨3824100, by rfl⟩ : syracuseStep 40790405 = 7648201) B7648201
theorem B27193603 : Blo 1985435 27193603 := bstep (se 1 (by rfl) ⟨20395202, by rfl⟩ : syracuseStep 27193603 = 40790405) B40790405
theorem B36258137 : Blo 1985435 36258137 := bstep (se 2 (by rfl) ⟨13596801, by rfl⟩ : syracuseStep 36258137 = 27193603) B27193603
theorem B24172091 : Blo 1985435 24172091 := bstep (se 1 (by rfl) ⟨18129068, by rfl⟩ : syracuseStep 24172091 = 36258137) B36258137
theorem B16114727 : Blo 1985435 16114727 := bstep (se 1 (by rfl) ⟨12086045, by rfl⟩ : syracuseStep 16114727 = 24172091) B24172091
theorem B42972605 : Blo 1985435 42972605 := bstep (se 3 (by rfl) ⟨8057363, by rfl⟩ : syracuseStep 42972605 = 16114727) B16114727
theorem B28648403 : Blo 1985435 28648403 := bstep (se 1 (by rfl) ⟨21486302, by rfl⟩ : syracuseStep 28648403 = 42972605) B42972605
theorem B19098935 : Blo 1985435 19098935 := bstep (se 1 (by rfl) ⟨14324201, by rfl⟩ : syracuseStep 19098935 = 28648403) B28648403
theorem B12732623 : Blo 1985435 12732623 := bstep (se 1 (by rfl) ⟨9549467, by rfl⟩ : syracuseStep 12732623 = 19098935) B19098935
theorem B8488415 : Blo 1985435 8488415 := bstep (se 1 (by rfl) ⟨6366311, by rfl⟩ : syracuseStep 8488415 = 12732623) B12732623
theorem B5658943 : Blo 1985435 5658943 := bstep (se 1 (by rfl) ⟨4244207, by rfl⟩ : syracuseStep 5658943 = 8488415) B8488415
theorem B7545257 : Blo 1985435 7545257 := bstep (se 2 (by rfl) ⟨2829471, by rfl⟩ : syracuseStep 7545257 = 5658943) B5658943
theorem B5030171 : Blo 1985435 5030171 := bstep (se 1 (by rfl) ⟨3772628, by rfl⟩ : syracuseStep 5030171 = 7545257) B7545257
theorem B3353447 : Blo 1985435 3353447 := bstep (se 1 (by rfl) ⟨2515085, by rfl⟩ : syracuseStep 3353447 = 5030171) B5030171
theorem B2235631 : Blo 1985435 2235631 := bstep (se 1 (by rfl) ⟨1676723, by rfl⟩ : syracuseStep 2235631 = 3353447) B3353447
theorem B2980841 : Blo 1985435 2980841 := bstep (se 2 (by rfl) ⟨1117815, by rfl⟩ : syracuseStep 2980841 = 2235631) B2235631
theorem B1987227 : Blo 1985435 1987227 := bstep (se 1 (by rfl) ⟨1490420, by rfl⟩ : syracuseStep 1987227 = 2980841) B2980841
theorem B2014345 : Blo 1985435 2014345 := bbase (se 2 (by rfl) ⟨755379, by rfl⟩ : syracuseStep 2014345 = 1510759) (by norm_num)
theorem B2685793 : Blo 1985435 2685793 := bstep (se 2 (by rfl) ⟨1007172, by rfl⟩ : syracuseStep 2685793 = 2014345) B2014345
theorem B3581057 : Blo 1985435 3581057 := bstep (se 2 (by rfl) ⟨1342896, by rfl⟩ : syracuseStep 3581057 = 2685793) B2685793
theorem B9549485 : Blo 1985435 9549485 := bstep (se 3 (by rfl) ⟨1790528, by rfl⟩ : syracuseStep 9549485 = 3581057) B3581057
theorem B6366323 : Blo 1985435 6366323 := bstep (se 1 (by rfl) ⟨4774742, by rfl⟩ : syracuseStep 6366323 = 9549485) B9549485
theorem B16976861 : Blo 1985435 16976861 := bstep (se 3 (by rfl) ⟨3183161, by rfl⟩ : syracuseStep 16976861 = 6366323) B6366323
theorem B11317907 : Blo 1985435 11317907 := bstep (se 1 (by rfl) ⟨8488430, by rfl⟩ : syracuseStep 11317907 = 16976861) B16976861
theorem B7545271 : Blo 1985435 7545271 := bstep (se 1 (by rfl) ⟨5658953, by rfl⟩ : syracuseStep 7545271 = 11317907) B11317907
theorem B10060361 : Blo 1985435 10060361 := bstep (se 2 (by rfl) ⟨3772635, by rfl⟩ : syracuseStep 10060361 = 7545271) B7545271
theorem B6706907 : Blo 1985435 6706907 := bstep (se 1 (by rfl) ⟨5030180, by rfl⟩ : syracuseStep 6706907 = 10060361) B10060361
theorem B4471271 : Blo 1985435 4471271 := bstep (se 1 (by rfl) ⟨3353453, by rfl⟩ : syracuseStep 4471271 = 6706907) B6706907
theorem B2980847 : Blo 1985435 2980847 := bstep (se 1 (by rfl) ⟨2235635, by rfl⟩ : syracuseStep 2980847 = 4471271) B4471271
theorem B1987231 : Blo 1985435 1987231 := bstep (se 1 (by rfl) ⟨1490423, by rfl⟩ : syracuseStep 1987231 = 2980847) B2980847
theorem B2980853 : Blo 1985435 2980853 := bbase (se 5 (by rfl) ⟨139727, by rfl⟩ : syracuseStep 2980853 = 279455) (by norm_num)
theorem B1987235 : Blo 1985435 1987235 := bstep (se 1 (by rfl) ⟨1490426, by rfl⟩ : syracuseStep 1987235 = 2980853) B2980853
theorem B6043061 : Blo 1985435 6043061 := bbase (se 5 (by rfl) ⟨283268, by rfl⟩ : syracuseStep 6043061 = 566537) (by norm_num)
theorem B4028707 : Blo 1985435 4028707 := bstep (se 1 (by rfl) ⟨3021530, by rfl⟩ : syracuseStep 4028707 = 6043061) B6043061
theorem B5371609 : Blo 1985435 5371609 := bstep (se 2 (by rfl) ⟨2014353, by rfl⟩ : syracuseStep 5371609 = 4028707) B4028707
theorem B7162145 : Blo 1985435 7162145 := bstep (se 2 (by rfl) ⟨2685804, by rfl⟩ : syracuseStep 7162145 = 5371609) B5371609
theorem B4774763 : Blo 1985435 4774763 := bstep (se 1 (by rfl) ⟨3581072, by rfl⟩ : syracuseStep 4774763 = 7162145) B7162145
theorem B3183175 : Blo 1985435 3183175 := bstep (se 1 (by rfl) ⟨2387381, by rfl⟩ : syracuseStep 3183175 = 4774763) B4774763
theorem B4244233 : Blo 1985435 4244233 := bstep (se 2 (by rfl) ⟨1591587, by rfl⟩ : syracuseStep 4244233 = 3183175) B3183175
theorem B5658977 : Blo 1985435 5658977 := bstep (se 2 (by rfl) ⟨2122116, by rfl⟩ : syracuseStep 5658977 = 4244233) B4244233
theorem B3772651 : Blo 1985435 3772651 := bstep (se 1 (by rfl) ⟨2829488, by rfl⟩ : syracuseStep 3772651 = 5658977) B5658977
theorem B5030201 : Blo 1985435 5030201 := bstep (se 2 (by rfl) ⟨1886325, by rfl⟩ : syracuseStep 5030201 = 3772651) B3772651
theorem B3353467 : Blo 1985435 3353467 := bstep (se 1 (by rfl) ⟨2515100, by rfl⟩ : syracuseStep 3353467 = 5030201) B5030201
theorem B4471289 : Blo 1985435 4471289 := bstep (se 2 (by rfl) ⟨1676733, by rfl⟩ : syracuseStep 4471289 = 3353467) B3353467
theorem B2980859 : Blo 1985435 2980859 := bstep (se 1 (by rfl) ⟨2235644, by rfl⟩ : syracuseStep 2980859 = 4471289) B4471289
theorem B1987239 : Blo 1985435 1987239 := bstep (se 1 (by rfl) ⟨1490429, by rfl⟩ : syracuseStep 1987239 = 2980859) B2980859
theorem B2235649 : Blo 1985435 2235649 := bbase (se 2 (by rfl) ⟨838368, by rfl⟩ : syracuseStep 2235649 = 1676737) (by norm_num)
theorem B2980865 : Blo 1985435 2980865 := bstep (se 2 (by rfl) ⟨1117824, by rfl⟩ : syracuseStep 2980865 = 2235649) B2235649
theorem B1987243 : Blo 1985435 1987243 := bstep (se 1 (by rfl) ⟨1490432, by rfl⟩ : syracuseStep 1987243 = 2980865) B2980865
theorem B5030221 : Blo 1985435 5030221 := bbase (se 3 (by rfl) ⟨943166, by rfl⟩ : syracuseStep 5030221 = 1886333) (by norm_num)
theorem B6706961 : Blo 1985435 6706961 := bstep (se 2 (by rfl) ⟨2515110, by rfl⟩ : syracuseStep 6706961 = 5030221) B5030221
theorem B4471307 : Blo 1985435 4471307 := bstep (se 1 (by rfl) ⟨3353480, by rfl⟩ : syracuseStep 4471307 = 6706961) B6706961
theorem B2980871 : Blo 1985435 2980871 := bstep (se 1 (by rfl) ⟨2235653, by rfl⟩ : syracuseStep 2980871 = 4471307) B4471307
theorem B1987247 : Blo 1985435 1987247 := bstep (se 1 (by rfl) ⟨1490435, by rfl⟩ : syracuseStep 1987247 = 2980871) B2980871
theorem B2980877 : Blo 1985435 2980877 := bbase (se 3 (by rfl) ⟨558914, by rfl⟩ : syracuseStep 2980877 = 1117829) (by norm_num)
theorem B1987251 : Blo 1985435 1987251 := bstep (se 1 (by rfl) ⟨1490438, by rfl⟩ : syracuseStep 1987251 = 2980877) B2980877
theorem B4471325 : Blo 1985435 4471325 := bbase (se 3 (by rfl) ⟨838373, by rfl⟩ : syracuseStep 4471325 = 1676747) (by norm_num)
theorem B2980883 : Blo 1985435 2980883 := bstep (se 1 (by rfl) ⟨2235662, by rfl⟩ : syracuseStep 2980883 = 4471325) B4471325
theorem B1987255 : Blo 1985435 1987255 := bstep (se 1 (by rfl) ⟨1490441, by rfl⟩ : syracuseStep 1987255 = 2980883) B2980883
theorem B3353501 : Blo 1985435 3353501 := bbase (se 3 (by rfl) ⟨628781, by rfl⟩ : syracuseStep 3353501 = 1257563) (by norm_num)
theorem B2235667 : Blo 1985435 2235667 := bstep (se 1 (by rfl) ⟨1676750, by rfl⟩ : syracuseStep 2235667 = 3353501) B3353501
theorem B2980889 : Blo 1985435 2980889 := bstep (se 2 (by rfl) ⟨1117833, by rfl⟩ : syracuseStep 2980889 = 2235667) B2235667
theorem B1987259 : Blo 1985435 1987259 := bstep (se 1 (by rfl) ⟨1490444, by rfl⟩ : syracuseStep 1987259 = 2980889) B2980889
theorem B7162229 : Blo 1985435 7162229 := bbase (se 5 (by rfl) ⟨335729, by rfl⟩ : syracuseStep 7162229 = 671459) (by norm_num)
theorem B19099277 : Blo 1985435 19099277 := bstep (se 3 (by rfl) ⟨3581114, by rfl⟩ : syracuseStep 19099277 = 7162229) B7162229
theorem B12732851 : Blo 1985435 12732851 := bstep (se 1 (by rfl) ⟨9549638, by rfl⟩ : syracuseStep 12732851 = 19099277) B19099277
theorem B8488567 : Blo 1985435 8488567 := bstep (se 1 (by rfl) ⟨6366425, by rfl⟩ : syracuseStep 8488567 = 12732851) B12732851
theorem B11318089 : Blo 1985435 11318089 := bstep (se 2 (by rfl) ⟨4244283, by rfl⟩ : syracuseStep 11318089 = 8488567) B8488567
theorem B15090785 : Blo 1985435 15090785 := bstep (se 2 (by rfl) ⟨5659044, by rfl⟩ : syracuseStep 15090785 = 11318089) B11318089
theorem B10060523 : Blo 1985435 10060523 := bstep (se 1 (by rfl) ⟨7545392, by rfl⟩ : syracuseStep 10060523 = 15090785) B15090785
theorem B6707015 : Blo 1985435 6707015 := bstep (se 1 (by rfl) ⟨5030261, by rfl⟩ : syracuseStep 6707015 = 10060523) B10060523
theorem B4471343 : Blo 1985435 4471343 := bstep (se 1 (by rfl) ⟨3353507, by rfl⟩ : syracuseStep 4471343 = 6707015) B6707015
theorem B2980895 : Blo 1985435 2980895 := bstep (se 1 (by rfl) ⟨2235671, by rfl⟩ : syracuseStep 2980895 = 4471343) B4471343
theorem B1987263 : Blo 1985435 1987263 := bstep (se 1 (by rfl) ⟨1490447, by rfl⟩ : syracuseStep 1987263 = 2980895) B2980895
theorem B2980901 : Blo 1985435 2980901 := bbase (se 4 (by rfl) ⟨279459, by rfl⟩ : syracuseStep 2980901 = 558919) (by norm_num)
theorem B1987267 : Blo 1985435 1987267 := bstep (se 1 (by rfl) ⟨1490450, by rfl⟩ : syracuseStep 1987267 = 2980901) B2980901
theorem B2515141 : Blo 1985435 2515141 := bbase (se 4 (by rfl) ⟨235794, by rfl⟩ : syracuseStep 2515141 = 471589) (by norm_num)
theorem B3353521 : Blo 1985435 3353521 := bstep (se 2 (by rfl) ⟨1257570, by rfl⟩ : syracuseStep 3353521 = 2515141) B2515141
theorem B4471361 : Blo 1985435 4471361 := bstep (se 2 (by rfl) ⟨1676760, by rfl⟩ : syracuseStep 4471361 = 3353521) B3353521
theorem B2980907 : Blo 1985435 2980907 := bstep (se 1 (by rfl) ⟨2235680, by rfl⟩ : syracuseStep 2980907 = 4471361) B4471361
theorem B1987271 : Blo 1985435 1987271 := bstep (se 1 (by rfl) ⟨1490453, by rfl⟩ : syracuseStep 1987271 = 2980907) B2980907
theorem B2235685 : Blo 1985435 2235685 := bbase (se 4 (by rfl) ⟨209595, by rfl⟩ : syracuseStep 2235685 = 419191) (by norm_num)
theorem B2980913 : Blo 1985435 2980913 := bstep (se 2 (by rfl) ⟨1117842, by rfl⟩ : syracuseStep 2980913 = 2235685) B2235685
theorem B1987275 : Blo 1985435 1987275 := bstep (se 1 (by rfl) ⟨1490456, by rfl⟩ : syracuseStep 1987275 = 2980913) B2980913
theorem B5371717 : Blo 1985435 5371717 := bbase (se 4 (by rfl) ⟨503598, by rfl⟩ : syracuseStep 5371717 = 1007197) (by norm_num)
theorem B7162289 : Blo 1985435 7162289 := bstep (se 2 (by rfl) ⟨2685858, by rfl⟩ : syracuseStep 7162289 = 5371717) B5371717
theorem B4774859 : Blo 1985435 4774859 := bstep (se 1 (by rfl) ⟨3581144, by rfl⟩ : syracuseStep 4774859 = 7162289) B7162289
theorem B3183239 : Blo 1985435 3183239 := bstep (se 1 (by rfl) ⟨2387429, by rfl⟩ : syracuseStep 3183239 = 4774859) B4774859
theorem B8488637 : Blo 1985435 8488637 := bstep (se 3 (by rfl) ⟨1591619, by rfl⟩ : syracuseStep 8488637 = 3183239) B3183239
theorem B5659091 : Blo 1985435 5659091 := bstep (se 1 (by rfl) ⟨4244318, by rfl⟩ : syracuseStep 5659091 = 8488637) B8488637
theorem B3772727 : Blo 1985435 3772727 := bstep (se 1 (by rfl) ⟨2829545, by rfl⟩ : syracuseStep 3772727 = 5659091) B5659091
theorem B2515151 : Blo 1985435 2515151 := bstep (se 1 (by rfl) ⟨1886363, by rfl⟩ : syracuseStep 2515151 = 3772727) B3772727
theorem B6707069 : Blo 1985435 6707069 := bstep (se 3 (by rfl) ⟨1257575, by rfl⟩ : syracuseStep 6707069 = 2515151) B2515151
theorem B4471379 : Blo 1985435 4471379 := bstep (se 1 (by rfl) ⟨3353534, by rfl⟩ : syracuseStep 4471379 = 6707069) B6707069
theorem B2980919 : Blo 1985435 2980919 := bstep (se 1 (by rfl) ⟨2235689, by rfl⟩ : syracuseStep 2980919 = 4471379) B4471379
theorem B1987279 : Blo 1985435 1987279 := bstep (se 1 (by rfl) ⟨1490459, by rfl⟩ : syracuseStep 1987279 = 2980919) B2980919
theorem B2980925 : Blo 1985435 2980925 := bbase (se 3 (by rfl) ⟨558923, by rfl⟩ : syracuseStep 2980925 = 1117847) (by norm_num)
theorem B1987283 : Blo 1985435 1987283 := bstep (se 1 (by rfl) ⟨1490462, by rfl⟩ : syracuseStep 1987283 = 2980925) B2980925
theorem B4471397 : Blo 1985435 4471397 := bbase (se 4 (by rfl) ⟨419193, by rfl⟩ : syracuseStep 4471397 = 838387) (by norm_num)
theorem B2980931 : Blo 1985435 2980931 := bstep (se 1 (by rfl) ⟨2235698, by rfl⟩ : syracuseStep 2980931 = 4471397) B4471397
theorem B1987287 : Blo 1985435 1987287 := bstep (se 1 (by rfl) ⟨1490465, by rfl⟩ : syracuseStep 1987287 = 2980931) B2980931
theorem B5030333 : Blo 1985435 5030333 := bbase (se 3 (by rfl) ⟨943187, by rfl⟩ : syracuseStep 5030333 = 1886375) (by norm_num)
theorem B3353555 : Blo 1985435 3353555 := bstep (se 1 (by rfl) ⟨2515166, by rfl⟩ : syracuseStep 3353555 = 5030333) B5030333
theorem B2235703 : Blo 1985435 2235703 := bstep (se 1 (by rfl) ⟨1676777, by rfl⟩ : syracuseStep 2235703 = 3353555) B3353555
theorem B2980937 : Blo 1985435 2980937 := bstep (se 2 (by rfl) ⟨1117851, by rfl⟩ : syracuseStep 2980937 = 2235703) B2235703
theorem B1987291 : Blo 1985435 1987291 := bstep (se 1 (by rfl) ⟨1490468, by rfl⟩ : syracuseStep 1987291 = 2980937) B2980937
theorem B3772757 : Blo 1985435 3772757 := bbase (se 10 (by rfl) ⟨5526, by rfl⟩ : syracuseStep 3772757 = 11053) (by norm_num)
theorem B10060685 : Blo 1985435 10060685 := bstep (se 3 (by rfl) ⟨1886378, by rfl⟩ : syracuseStep 10060685 = 3772757) B3772757
theorem B6707123 : Blo 1985435 6707123 := bstep (se 1 (by rfl) ⟨5030342, by rfl⟩ : syracuseStep 6707123 = 10060685) B10060685
theorem B4471415 : Blo 1985435 4471415 := bstep (se 1 (by rfl) ⟨3353561, by rfl⟩ : syracuseStep 4471415 = 6707123) B6707123
theorem B2980943 : Blo 1985435 2980943 := bstep (se 1 (by rfl) ⟨2235707, by rfl⟩ : syracuseStep 2980943 = 4471415) B4471415
theorem B1987295 : Blo 1985435 1987295 := bstep (se 1 (by rfl) ⟨1490471, by rfl⟩ : syracuseStep 1987295 = 2980943) B2980943
theorem B2980949 : Blo 1985435 2980949 := bbase (se 8 (by rfl) ⟨17466, by rfl⟩ : syracuseStep 2980949 = 34933) (by norm_num)
theorem B1987299 : Blo 1985435 1987299 := bstep (se 1 (by rfl) ⟨1490474, by rfl⟩ : syracuseStep 1987299 = 2980949) B2980949
theorem B12733109 : Blo 1985435 12733109 := bbase (se 5 (by rfl) ⟨596864, by rfl⟩ : syracuseStep 12733109 = 1193729) (by norm_num)
theorem B8488739 : Blo 1985435 8488739 := bstep (se 1 (by rfl) ⟨6366554, by rfl⟩ : syracuseStep 8488739 = 12733109) B12733109
theorem B5659159 : Blo 1985435 5659159 := bstep (se 1 (by rfl) ⟨4244369, by rfl⟩ : syracuseStep 5659159 = 8488739) B8488739
theorem B7545545 : Blo 1985435 7545545 := bstep (se 2 (by rfl) ⟨2829579, by rfl⟩ : syracuseStep 7545545 = 5659159) B5659159
theorem B5030363 : Blo 1985435 5030363 := bstep (se 1 (by rfl) ⟨3772772, by rfl⟩ : syracuseStep 5030363 = 7545545) B7545545
theorem B3353575 : Blo 1985435 3353575 := bstep (se 1 (by rfl) ⟨2515181, by rfl⟩ : syracuseStep 3353575 = 5030363) B5030363
theorem B4471433 : Blo 1985435 4471433 := bstep (se 2 (by rfl) ⟨1676787, by rfl⟩ : syracuseStep 4471433 = 3353575) B3353575
theorem B2980955 : Blo 1985435 2980955 := bstep (se 1 (by rfl) ⟨2235716, by rfl⟩ : syracuseStep 2980955 = 4471433) B4471433
theorem B1987303 : Blo 1985435 1987303 := bstep (se 1 (by rfl) ⟨1490477, by rfl⟩ : syracuseStep 1987303 = 2980955) B2980955
theorem B2235721 : Blo 1985435 2235721 := bbase (se 2 (by rfl) ⟨838395, by rfl⟩ : syracuseStep 2235721 = 1676791) (by norm_num)
theorem B2980961 : Blo 1985435 2980961 := bstep (se 2 (by rfl) ⟨1117860, by rfl⟩ : syracuseStep 2980961 = 2235721) B2235721
theorem B1987307 : Blo 1985435 1987307 := bstep (se 1 (by rfl) ⟨1490480, by rfl⟩ : syracuseStep 1987307 = 2980961) B2980961
theorem B3630061 : Blo 1985435 3630061 := bbase (se 3 (by rfl) ⟨680636, by rfl⟩ : syracuseStep 3630061 = 1361273) (by norm_num)
theorem B4840081 : Blo 1985435 4840081 := bstep (se 2 (by rfl) ⟨1815030, by rfl⟩ : syracuseStep 4840081 = 3630061) B3630061
theorem B25813765 : Blo 1985435 25813765 := bstep (se 4 (by rfl) ⟨2420040, by rfl⟩ : syracuseStep 25813765 = 4840081) B4840081
theorem B34418353 : Blo 1985435 34418353 := bstep (se 2 (by rfl) ⟨12906882, by rfl⟩ : syracuseStep 34418353 = 25813765) B25813765
theorem B45891137 : Blo 1985435 45891137 := bstep (se 2 (by rfl) ⟨17209176, by rfl⟩ : syracuseStep 45891137 = 34418353) B34418353
theorem B122376365 : Blo 1985435 122376365 := bstep (se 3 (by rfl) ⟨22945568, by rfl⟩ : syracuseStep 122376365 = 45891137) B45891137
theorem B81584243 : Blo 1985435 81584243 := bstep (se 1 (by rfl) ⟨61188182, by rfl⟩ : syracuseStep 81584243 = 122376365) B122376365
theorem B54389495 : Blo 1985435 54389495 := bstep (se 1 (by rfl) ⟨40792121, by rfl⟩ : syracuseStep 54389495 = 81584243) B81584243
theorem B36259663 : Blo 1985435 36259663 := bstep (se 1 (by rfl) ⟨27194747, by rfl⟩ : syracuseStep 36259663 = 54389495) B54389495
theorem B48346217 : Blo 1985435 48346217 := bstep (se 2 (by rfl) ⟨18129831, by rfl⟩ : syracuseStep 48346217 = 36259663) B36259663
theorem B32230811 : Blo 1985435 32230811 := bstep (se 1 (by rfl) ⟨24173108, by rfl⟩ : syracuseStep 32230811 = 48346217) B48346217
theorem B21487207 : Blo 1985435 21487207 := bstep (se 1 (by rfl) ⟨16115405, by rfl⟩ : syracuseStep 21487207 = 32230811) B32230811
theorem B28649609 : Blo 1985435 28649609 := bstep (se 2 (by rfl) ⟨10743603, by rfl⟩ : syracuseStep 28649609 = 21487207) B21487207
theorem B19099739 : Blo 1985435 19099739 := bstep (se 1 (by rfl) ⟨14324804, by rfl⟩ : syracuseStep 19099739 = 28649609) B28649609
theorem B12733159 : Blo 1985435 12733159 := bstep (se 1 (by rfl) ⟨9549869, by rfl⟩ : syracuseStep 12733159 = 19099739) B19099739
theorem B16977545 : Blo 1985435 16977545 := bstep (se 2 (by rfl) ⟨6366579, by rfl⟩ : syracuseStep 16977545 = 12733159) B12733159
theorem B11318363 : Blo 1985435 11318363 := bstep (se 1 (by rfl) ⟨8488772, by rfl⟩ : syracuseStep 11318363 = 16977545) B16977545
theorem B7545575 : Blo 1985435 7545575 := bstep (se 1 (by rfl) ⟨5659181, by rfl⟩ : syracuseStep 7545575 = 11318363) B11318363
theorem B5030383 : Blo 1985435 5030383 := bstep (se 1 (by rfl) ⟨3772787, by rfl⟩ : syracuseStep 5030383 = 7545575) B7545575
theorem B6707177 : Blo 1985435 6707177 := bstep (se 2 (by rfl) ⟨2515191, by rfl⟩ : syracuseStep 6707177 = 5030383) B5030383
theorem B4471451 : Blo 1985435 4471451 := bstep (se 1 (by rfl) ⟨3353588, by rfl⟩ : syracuseStep 4471451 = 6707177) B6707177
theorem B2980967 : Blo 1985435 2980967 := bstep (se 1 (by rfl) ⟨2235725, by rfl⟩ : syracuseStep 2980967 = 4471451) B4471451
theorem B1987311 : Blo 1985435 1987311 := bstep (se 1 (by rfl) ⟨1490483, by rfl⟩ : syracuseStep 1987311 = 2980967) B2980967
theorem B2980973 : Blo 1985435 2980973 := bbase (se 3 (by rfl) ⟨558932, by rfl⟩ : syracuseStep 2980973 = 1117865) (by norm_num)
theorem B1987315 : Blo 1985435 1987315 := bstep (se 1 (by rfl) ⟨1490486, by rfl⟩ : syracuseStep 1987315 = 2980973) B2980973
theorem B4471469 : Blo 1985435 4471469 := bbase (se 3 (by rfl) ⟨838400, by rfl⟩ : syracuseStep 4471469 = 1676801) (by norm_num)
theorem B2980979 : Blo 1985435 2980979 := bstep (se 1 (by rfl) ⟨2235734, by rfl⟩ : syracuseStep 2980979 = 4471469) B4471469
theorem B1987319 : Blo 1985435 1987319 := bstep (se 1 (by rfl) ⟨1490489, by rfl⟩ : syracuseStep 1987319 = 2980979) B2980979
theorem B4244413 : Blo 1985435 4244413 := bbase (se 3 (by rfl) ⟨795827, by rfl⟩ : syracuseStep 4244413 = 1591655) (by norm_num)
theorem B5659217 : Blo 1985435 5659217 := bstep (se 2 (by rfl) ⟨2122206, by rfl⟩ : syracuseStep 5659217 = 4244413) B4244413
theorem B3772811 : Blo 1985435 3772811 := bstep (se 1 (by rfl) ⟨2829608, by rfl⟩ : syracuseStep 3772811 = 5659217) B5659217
theorem B2515207 : Blo 1985435 2515207 := bstep (se 1 (by rfl) ⟨1886405, by rfl⟩ : syracuseStep 2515207 = 3772811) B3772811
theorem B3353609 : Blo 1985435 3353609 := bstep (se 2 (by rfl) ⟨1257603, by rfl⟩ : syracuseStep 3353609 = 2515207) B2515207
theorem B2235739 : Blo 1985435 2235739 := bstep (se 1 (by rfl) ⟨1676804, by rfl⟩ : syracuseStep 2235739 = 3353609) B3353609
theorem B2980985 : Blo 1985435 2980985 := bstep (se 2 (by rfl) ⟨1117869, by rfl⟩ : syracuseStep 2980985 = 2235739) B2235739
theorem B1987323 : Blo 1985435 1987323 := bstep (se 1 (by rfl) ⟨1490492, by rfl⟩ : syracuseStep 1987323 = 2980985) B2980985
theorem B4083853 : Blo 1985435 4083853 := bbase (se 3 (by rfl) ⟨765722, by rfl⟩ : syracuseStep 4083853 = 1531445) (by norm_num)
theorem B5445137 : Blo 1985435 5445137 := bstep (se 2 (by rfl) ⟨2041926, by rfl⟩ : syracuseStep 5445137 = 4083853) B4083853
theorem B3630091 : Blo 1985435 3630091 := bstep (se 1 (by rfl) ⟨2722568, by rfl⟩ : syracuseStep 3630091 = 5445137) B5445137
theorem B4840121 : Blo 1985435 4840121 := bstep (se 2 (by rfl) ⟨1815045, by rfl⟩ : syracuseStep 4840121 = 3630091) B3630091
theorem B3226747 : Blo 1985435 3226747 := bstep (se 1 (by rfl) ⟨2420060, by rfl⟩ : syracuseStep 3226747 = 4840121) B4840121
theorem B4302329 : Blo 1985435 4302329 := bstep (se 2 (by rfl) ⟨1613373, by rfl⟩ : syracuseStep 4302329 = 3226747) B3226747
theorem B11472877 : Blo 1985435 11472877 := bstep (se 3 (by rfl) ⟨2151164, by rfl⟩ : syracuseStep 11472877 = 4302329) B4302329
theorem B15297169 : Blo 1985435 15297169 := bstep (se 2 (by rfl) ⟨5736438, by rfl⟩ : syracuseStep 15297169 = 11472877) B11472877
theorem B20396225 : Blo 1985435 20396225 := bstep (se 2 (by rfl) ⟨7648584, by rfl⟩ : syracuseStep 20396225 = 15297169) B15297169
theorem B13597483 : Blo 1985435 13597483 := bstep (se 1 (by rfl) ⟨10198112, by rfl⟩ : syracuseStep 13597483 = 20396225) B20396225
theorem B18129977 : Blo 1985435 18129977 := bstep (se 2 (by rfl) ⟨6798741, by rfl⟩ : syracuseStep 18129977 = 13597483) B13597483
theorem B12086651 : Blo 1985435 12086651 := bstep (se 1 (by rfl) ⟨9064988, by rfl⟩ : syracuseStep 12086651 = 18129977) B18129977
theorem B8057767 : Blo 1985435 8057767 := bstep (se 1 (by rfl) ⟨6043325, by rfl⟩ : syracuseStep 8057767 = 12086651) B12086651
theorem B10743689 : Blo 1985435 10743689 := bstep (se 2 (by rfl) ⟨4028883, by rfl⟩ : syracuseStep 10743689 = 8057767) B8057767
theorem B28649837 : Blo 1985435 28649837 := bstep (se 3 (by rfl) ⟨5371844, by rfl⟩ : syracuseStep 28649837 = 10743689) B10743689
theorem B19099891 : Blo 1985435 19099891 := bstep (se 1 (by rfl) ⟨14324918, by rfl⟩ : syracuseStep 19099891 = 28649837) B28649837
theorem B25466521 : Blo 1985435 25466521 := bstep (se 2 (by rfl) ⟨9549945, by rfl⟩ : syracuseStep 25466521 = 19099891) B19099891
theorem B33955361 : Blo 1985435 33955361 := bstep (se 2 (by rfl) ⟨12733260, by rfl⟩ : syracuseStep 33955361 = 25466521) B25466521
theorem B22636907 : Blo 1985435 22636907 := bstep (se 1 (by rfl) ⟨16977680, by rfl⟩ : syracuseStep 22636907 = 33955361) B33955361
theorem B15091271 : Blo 1985435 15091271 := bstep (se 1 (by rfl) ⟨11318453, by rfl⟩ : syracuseStep 15091271 = 22636907) B22636907
theorem B10060847 : Blo 1985435 10060847 := bstep (se 1 (by rfl) ⟨7545635, by rfl⟩ : syracuseStep 10060847 = 15091271) B15091271
theorem B6707231 : Blo 1985435 6707231 := bstep (se 1 (by rfl) ⟨5030423, by rfl⟩ : syracuseStep 6707231 = 10060847) B10060847
theorem B4471487 : Blo 1985435 4471487 := bstep (se 1 (by rfl) ⟨3353615, by rfl⟩ : syracuseStep 4471487 = 6707231) B6707231
theorem B2980991 : Blo 1985435 2980991 := bstep (se 1 (by rfl) ⟨2235743, by rfl⟩ : syracuseStep 2980991 = 4471487) B4471487
theorem B1987327 : Blo 1985435 1987327 := bstep (se 1 (by rfl) ⟨1490495, by rfl⟩ : syracuseStep 1987327 = 2980991) B2980991
theorem B2980997 : Blo 1985435 2980997 := bbase (se 4 (by rfl) ⟨279468, by rfl⟩ : syracuseStep 2980997 = 558937) (by norm_num)
theorem B1987331 : Blo 1985435 1987331 := bstep (se 1 (by rfl) ⟨1490498, by rfl⟩ : syracuseStep 1987331 = 2980997) B2980997
theorem B3353629 : Blo 1985435 3353629 := bbase (se 3 (by rfl) ⟨628805, by rfl⟩ : syracuseStep 3353629 = 1257611) (by norm_num)
theorem B4471505 : Blo 1985435 4471505 := bstep (se 2 (by rfl) ⟨1676814, by rfl⟩ : syracuseStep 4471505 = 3353629) B3353629
theorem B2981003 : Blo 1985435 2981003 := bstep (se 1 (by rfl) ⟨2235752, by rfl⟩ : syracuseStep 2981003 = 4471505) B4471505
theorem B1987335 : Blo 1985435 1987335 := bstep (se 1 (by rfl) ⟨1490501, by rfl⟩ : syracuseStep 1987335 = 2981003) B2981003
theorem B2235757 : Blo 1985435 2235757 := bbase (se 3 (by rfl) ⟨419204, by rfl⟩ : syracuseStep 2235757 = 838409) (by norm_num)
theorem B2981009 : Blo 1985435 2981009 := bstep (se 2 (by rfl) ⟨1117878, by rfl⟩ : syracuseStep 2981009 = 2235757) B2235757
theorem B1987339 : Blo 1985435 1987339 := bstep (se 1 (by rfl) ⟨1490504, by rfl⟩ : syracuseStep 1987339 = 2981009) B2981009
theorem B6707285 : Blo 1985435 6707285 := bbase (se 8 (by rfl) ⟨39300, by rfl⟩ : syracuseStep 6707285 = 78601) (by norm_num)
theorem B4471523 : Blo 1985435 4471523 := bstep (se 1 (by rfl) ⟨3353642, by rfl⟩ : syracuseStep 4471523 = 6707285) B6707285
theorem B2981015 : Blo 1985435 2981015 := bstep (se 1 (by rfl) ⟨2235761, by rfl⟩ : syracuseStep 2981015 = 4471523) B4471523
theorem B1987343 : Blo 1985435 1987343 := bstep (se 1 (by rfl) ⟨1490507, by rfl⟩ : syracuseStep 1987343 = 2981015) B2981015
theorem B2981021 : Blo 1985435 2981021 := bbase (se 3 (by rfl) ⟨558941, by rfl⟩ : syracuseStep 2981021 = 1117883) (by norm_num)
theorem B1987347 : Blo 1985435 1987347 := bstep (se 1 (by rfl) ⟨1490510, by rfl⟩ : syracuseStep 1987347 = 2981021) B2981021
theorem B4471541 : Blo 1985435 4471541 := bbase (se 5 (by rfl) ⟨209603, by rfl⟩ : syracuseStep 4471541 = 419207) (by norm_num)
theorem B2981027 : Blo 1985435 2981027 := bstep (se 1 (by rfl) ⟨2235770, by rfl⟩ : syracuseStep 2981027 = 4471541) B4471541
theorem B1987351 : Blo 1985435 1987351 := bstep (se 1 (by rfl) ⟨1490513, by rfl⟩ : syracuseStep 1987351 = 2981027) B2981027
theorem B3399421 : Blo 1985435 3399421 := bbase (se 3 (by rfl) ⟨637391, by rfl⟩ : syracuseStep 3399421 = 1274783) (by norm_num)
theorem B4532561 : Blo 1985435 4532561 := bstep (se 2 (by rfl) ⟨1699710, by rfl⟩ : syracuseStep 4532561 = 3399421) B3399421
theorem B3021707 : Blo 1985435 3021707 := bstep (se 1 (by rfl) ⟨2266280, by rfl⟩ : syracuseStep 3021707 = 4532561) B4532561
theorem B2014471 : Blo 1985435 2014471 := bstep (se 1 (by rfl) ⟨1510853, by rfl⟩ : syracuseStep 2014471 = 3021707) B3021707
theorem B2685961 : Blo 1985435 2685961 := bstep (se 2 (by rfl) ⟨1007235, by rfl⟩ : syracuseStep 2685961 = 2014471) B2014471
theorem B3581281 : Blo 1985435 3581281 := bstep (se 2 (by rfl) ⟨1342980, by rfl⟩ : syracuseStep 3581281 = 2685961) B2685961
theorem B4775041 : Blo 1985435 4775041 := bstep (se 2 (by rfl) ⟨1790640, by rfl⟩ : syracuseStep 4775041 = 3581281) B3581281
theorem B25466885 : Blo 1985435 25466885 := bstep (se 4 (by rfl) ⟨2387520, by rfl⟩ : syracuseStep 25466885 = 4775041) B4775041
theorem B16977923 : Blo 1985435 16977923 := bstep (se 1 (by rfl) ⟨12733442, by rfl⟩ : syracuseStep 16977923 = 25466885) B25466885
theorem B11318615 : Blo 1985435 11318615 := bstep (se 1 (by rfl) ⟨8488961, by rfl⟩ : syracuseStep 11318615 = 16977923) B16977923
theorem B7545743 : Blo 1985435 7545743 := bstep (se 1 (by rfl) ⟨5659307, by rfl⟩ : syracuseStep 7545743 = 11318615) B11318615
theorem B5030495 : Blo 1985435 5030495 := bstep (se 1 (by rfl) ⟨3772871, by rfl⟩ : syracuseStep 5030495 = 7545743) B7545743
theorem B3353663 : Blo 1985435 3353663 := bstep (se 1 (by rfl) ⟨2515247, by rfl⟩ : syracuseStep 3353663 = 5030495) B5030495
theorem B2235775 : Blo 1985435 2235775 := bstep (se 1 (by rfl) ⟨1676831, by rfl⟩ : syracuseStep 2235775 = 3353663) B3353663
theorem B2981033 : Blo 1985435 2981033 := bstep (se 2 (by rfl) ⟨1117887, by rfl⟩ : syracuseStep 2981033 = 2235775) B2235775
theorem B1987355 : Blo 1985435 1987355 := bstep (se 1 (by rfl) ⟨1490516, by rfl⟩ : syracuseStep 1987355 = 2981033) B2981033
theorem B2266285 : Blo 1985435 2266285 := bbase (se 3 (by rfl) ⟨424928, by rfl⟩ : syracuseStep 2266285 = 849857) (by norm_num)
theorem B3021713 : Blo 1985435 3021713 := bstep (se 2 (by rfl) ⟨1133142, by rfl⟩ : syracuseStep 3021713 = 2266285) B2266285
theorem B2014475 : Blo 1985435 2014475 := bstep (se 1 (by rfl) ⟨1510856, by rfl⟩ : syracuseStep 2014475 = 3021713) B3021713
theorem B5371933 : Blo 1985435 5371933 := bstep (se 3 (by rfl) ⟨1007237, by rfl⟩ : syracuseStep 5371933 = 2014475) B2014475
theorem B7162577 : Blo 1985435 7162577 := bstep (se 2 (by rfl) ⟨2685966, by rfl⟩ : syracuseStep 7162577 = 5371933) B5371933
theorem B4775051 : Blo 1985435 4775051 := bstep (se 1 (by rfl) ⟨3581288, by rfl⟩ : syracuseStep 4775051 = 7162577) B7162577
theorem B3183367 : Blo 1985435 3183367 := bstep (se 1 (by rfl) ⟨2387525, by rfl⟩ : syracuseStep 3183367 = 4775051) B4775051
theorem B4244489 : Blo 1985435 4244489 := bstep (se 2 (by rfl) ⟨1591683, by rfl⟩ : syracuseStep 4244489 = 3183367) B3183367
theorem B2829659 : Blo 1985435 2829659 := bstep (se 1 (by rfl) ⟨2122244, by rfl⟩ : syracuseStep 2829659 = 4244489) B4244489
theorem B7545757 : Blo 1985435 7545757 := bstep (se 3 (by rfl) ⟨1414829, by rfl⟩ : syracuseStep 7545757 = 2829659) B2829659
theorem B10061009 : Blo 1985435 10061009 := bstep (se 2 (by rfl) ⟨3772878, by rfl⟩ : syracuseStep 10061009 = 7545757) B7545757
theorem B6707339 : Blo 1985435 6707339 := bstep (se 1 (by rfl) ⟨5030504, by rfl⟩ : syracuseStep 6707339 = 10061009) B10061009
theorem B4471559 : Blo 1985435 4471559 := bstep (se 1 (by rfl) ⟨3353669, by rfl⟩ : syracuseStep 4471559 = 6707339) B6707339
theorem B2981039 : Blo 1985435 2981039 := bstep (se 1 (by rfl) ⟨2235779, by rfl⟩ : syracuseStep 2981039 = 4471559) B4471559
theorem B1987359 : Blo 1985435 1987359 := bstep (se 1 (by rfl) ⟨1490519, by rfl⟩ : syracuseStep 1987359 = 2981039) B2981039
theorem B2981045 : Blo 1985435 2981045 := bbase (se 5 (by rfl) ⟨139736, by rfl⟩ : syracuseStep 2981045 = 279473) (by norm_num)
theorem B1987363 : Blo 1985435 1987363 := bstep (se 1 (by rfl) ⟨1490522, by rfl⟩ : syracuseStep 1987363 = 2981045) B2981045
theorem B5030525 : Blo 1985435 5030525 := bbase (se 3 (by rfl) ⟨943223, by rfl⟩ : syracuseStep 5030525 = 1886447) (by norm_num)
theorem B3353683 : Blo 1985435 3353683 := bstep (se 1 (by rfl) ⟨2515262, by rfl⟩ : syracuseStep 3353683 = 5030525) B5030525
theorem B4471577 : Blo 1985435 4471577 := bstep (se 2 (by rfl) ⟨1676841, by rfl⟩ : syracuseStep 4471577 = 3353683) B3353683
theorem B2981051 : Blo 1985435 2981051 := bstep (se 1 (by rfl) ⟨2235788, by rfl⟩ : syracuseStep 2981051 = 4471577) B4471577
theorem B1987367 : Blo 1985435 1987367 := bstep (se 1 (by rfl) ⟨1490525, by rfl⟩ : syracuseStep 1987367 = 2981051) B2981051
theorem B2235793 : Blo 1985435 2235793 := bbase (se 2 (by rfl) ⟨838422, by rfl⟩ : syracuseStep 2235793 = 1676845) (by norm_num)
theorem B2981057 : Blo 1985435 2981057 := bstep (se 2 (by rfl) ⟨1117896, by rfl⟩ : syracuseStep 2981057 = 2235793) B2235793
theorem B1987371 : Blo 1985435 1987371 := bstep (se 1 (by rfl) ⟨1490528, by rfl⟩ : syracuseStep 1987371 = 2981057) B2981057
theorem B3772909 : Blo 1985435 3772909 := bbase (se 3 (by rfl) ⟨707420, by rfl⟩ : syracuseStep 3772909 = 1414841) (by norm_num)
theorem B5030545 : Blo 1985435 5030545 := bstep (se 2 (by rfl) ⟨1886454, by rfl⟩ : syracuseStep 5030545 = 3772909) B3772909
theorem B6707393 : Blo 1985435 6707393 := bstep (se 2 (by rfl) ⟨2515272, by rfl⟩ : syracuseStep 6707393 = 5030545) B5030545
theorem B4471595 : Blo 1985435 4471595 := bstep (se 1 (by rfl) ⟨3353696, by rfl⟩ : syracuseStep 4471595 = 6707393) B6707393
theorem B2981063 : Blo 1985435 2981063 := bstep (se 1 (by rfl) ⟨2235797, by rfl⟩ : syracuseStep 2981063 = 4471595) B4471595
theorem B1987375 : Blo 1985435 1987375 := bstep (se 1 (by rfl) ⟨1490531, by rfl⟩ : syracuseStep 1987375 = 2981063) B2981063
theorem B2981069 : Blo 1985435 2981069 := bbase (se 3 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 2981069 = 1117901) (by norm_num)
theorem B1987379 : Blo 1985435 1987379 := bstep (se 1 (by rfl) ⟨1490534, by rfl⟩ : syracuseStep 1987379 = 2981069) B2981069
theorem B4471613 : Blo 1985435 4471613 := bbase (se 3 (by rfl) ⟨838427, by rfl⟩ : syracuseStep 4471613 = 1676855) (by norm_num)
theorem B2981075 : Blo 1985435 2981075 := bstep (se 1 (by rfl) ⟨2235806, by rfl⟩ : syracuseStep 2981075 = 4471613) B4471613
theorem B1987383 : Blo 1985435 1987383 := bstep (se 1 (by rfl) ⟨1490537, by rfl⟩ : syracuseStep 1987383 = 2981075) B2981075
theorem B3353717 : Blo 1985435 3353717 := bbase (se 5 (by rfl) ⟨157205, by rfl⟩ : syracuseStep 3353717 = 314411) (by norm_num)
theorem B2235811 : Blo 1985435 2235811 := bstep (se 1 (by rfl) ⟨1676858, by rfl⟩ : syracuseStep 2235811 = 3353717) B3353717
theorem B2981081 : Blo 1985435 2981081 := bstep (se 2 (by rfl) ⟨1117905, by rfl⟩ : syracuseStep 2981081 = 2235811) B2235811
theorem B1987387 : Blo 1985435 1987387 := bstep (se 1 (by rfl) ⟨1490540, by rfl⟩ : syracuseStep 1987387 = 2981081) B2981081
theorem B4244557 : Blo 1985435 4244557 := bbase (se 3 (by rfl) ⟨795854, by rfl⟩ : syracuseStep 4244557 = 1591709) (by norm_num)
theorem B5659409 : Blo 1985435 5659409 := bstep (se 2 (by rfl) ⟨2122278, by rfl⟩ : syracuseStep 5659409 = 4244557) B4244557
theorem B15091757 : Blo 1985435 15091757 := bstep (se 3 (by rfl) ⟨2829704, by rfl⟩ : syracuseStep 15091757 = 5659409) B5659409
theorem B10061171 : Blo 1985435 10061171 := bstep (se 1 (by rfl) ⟨7545878, by rfl⟩ : syracuseStep 10061171 = 15091757) B15091757
theorem B6707447 : Blo 1985435 6707447 := bstep (se 1 (by rfl) ⟨5030585, by rfl⟩ : syracuseStep 6707447 = 10061171) B10061171
theorem B4471631 : Blo 1985435 4471631 := bstep (se 1 (by rfl) ⟨3353723, by rfl⟩ : syracuseStep 4471631 = 6707447) B6707447
theorem B2981087 : Blo 1985435 2981087 := bstep (se 1 (by rfl) ⟨2235815, by rfl⟩ : syracuseStep 2981087 = 4471631) B4471631
theorem B1987391 : Blo 1985435 1987391 := bstep (se 1 (by rfl) ⟨1490543, by rfl⟩ : syracuseStep 1987391 = 2981087) B2981087
theorem B2981093 : Blo 1985435 2981093 := bbase (se 4 (by rfl) ⟨279477, by rfl⟩ : syracuseStep 2981093 = 558955) (by norm_num)
theorem B1987395 : Blo 1985435 1987395 := bstep (se 1 (by rfl) ⟨1490546, by rfl⟩ : syracuseStep 1987395 = 2981093) B2981093
theorem B9680597 : Blo 1985435 9680597 := bbase (se 7 (by rfl) ⟨113444, by rfl⟩ : syracuseStep 9680597 = 226889) (by norm_num)
theorem B6453731 : Blo 1985435 6453731 := bstep (se 1 (by rfl) ⟨4840298, by rfl⟩ : syracuseStep 6453731 = 9680597) B9680597
theorem B4302487 : Blo 1985435 4302487 := bstep (se 1 (by rfl) ⟨3226865, by rfl⟩ : syracuseStep 4302487 = 6453731) B6453731
theorem B22946597 : Blo 1985435 22946597 := bstep (se 4 (by rfl) ⟨2151243, by rfl⟩ : syracuseStep 22946597 = 4302487) B4302487
theorem B15297731 : Blo 1985435 15297731 := bstep (se 1 (by rfl) ⟨11473298, by rfl⟩ : syracuseStep 15297731 = 22946597) B22946597
theorem B10198487 : Blo 1985435 10198487 := bstep (se 1 (by rfl) ⟨7648865, by rfl⟩ : syracuseStep 10198487 = 15297731) B15297731
theorem B6798991 : Blo 1985435 6798991 := bstep (se 1 (by rfl) ⟨5099243, by rfl⟩ : syracuseStep 6798991 = 10198487) B10198487
theorem B9065321 : Blo 1985435 9065321 := bstep (se 2 (by rfl) ⟨3399495, by rfl⟩ : syracuseStep 9065321 = 6798991) B6798991
theorem B6043547 : Blo 1985435 6043547 := bstep (se 1 (by rfl) ⟨4532660, by rfl⟩ : syracuseStep 6043547 = 9065321) B9065321
theorem B4029031 : Blo 1985435 4029031 := bstep (se 1 (by rfl) ⟨3021773, by rfl⟩ : syracuseStep 4029031 = 6043547) B6043547
theorem B21488165 : Blo 1985435 21488165 := bstep (se 4 (by rfl) ⟨2014515, by rfl⟩ : syracuseStep 21488165 = 4029031) B4029031
theorem B14325443 : Blo 1985435 14325443 := bstep (se 1 (by rfl) ⟨10744082, by rfl⟩ : syracuseStep 14325443 = 21488165) B21488165
theorem B9550295 : Blo 1985435 9550295 := bstep (se 1 (by rfl) ⟨7162721, by rfl⟩ : syracuseStep 9550295 = 14325443) B14325443
theorem B6366863 : Blo 1985435 6366863 := bstep (se 1 (by rfl) ⟨4775147, by rfl⟩ : syracuseStep 6366863 = 9550295) B9550295
theorem B4244575 : Blo 1985435 4244575 := bstep (se 1 (by rfl) ⟨3183431, by rfl⟩ : syracuseStep 4244575 = 6366863) B6366863
theorem B5659433 : Blo 1985435 5659433 := bstep (se 2 (by rfl) ⟨2122287, by rfl⟩ : syracuseStep 5659433 = 4244575) B4244575
theorem B3772955 : Blo 1985435 3772955 := bstep (se 1 (by rfl) ⟨2829716, by rfl⟩ : syracuseStep 3772955 = 5659433) B5659433
theorem B2515303 : Blo 1985435 2515303 := bstep (se 1 (by rfl) ⟨1886477, by rfl⟩ : syracuseStep 2515303 = 3772955) B3772955
theorem B3353737 : Blo 1985435 3353737 := bstep (se 2 (by rfl) ⟨1257651, by rfl⟩ : syracuseStep 3353737 = 2515303) B2515303
theorem B4471649 : Blo 1985435 4471649 := bstep (se 2 (by rfl) ⟨1676868, by rfl⟩ : syracuseStep 4471649 = 3353737) B3353737
theorem B2981099 : Blo 1985435 2981099 := bstep (se 1 (by rfl) ⟨2235824, by rfl⟩ : syracuseStep 2981099 = 4471649) B4471649
theorem B1987399 : Blo 1985435 1987399 := bstep (se 1 (by rfl) ⟨1490549, by rfl⟩ : syracuseStep 1987399 = 2981099) B2981099
theorem B2235829 : Blo 1985435 2235829 := bbase (se 5 (by rfl) ⟨104804, by rfl⟩ : syracuseStep 2235829 = 209609) (by norm_num)
theorem B2981105 : Blo 1985435 2981105 := bstep (se 2 (by rfl) ⟨1117914, by rfl⟩ : syracuseStep 2981105 = 2235829) B2235829
theorem B1987403 : Blo 1985435 1987403 := bstep (se 1 (by rfl) ⟨1490552, by rfl⟩ : syracuseStep 1987403 = 2981105) B2981105
theorem B2515313 : Blo 1985435 2515313 := bbase (se 2 (by rfl) ⟨943242, by rfl⟩ : syracuseStep 2515313 = 1886485) (by norm_num)
theorem B6707501 : Blo 1985435 6707501 := bstep (se 3 (by rfl) ⟨1257656, by rfl⟩ : syracuseStep 6707501 = 2515313) B2515313
theorem B4471667 : Blo 1985435 4471667 := bstep (se 1 (by rfl) ⟨3353750, by rfl⟩ : syracuseStep 4471667 = 6707501) B6707501
theorem B2981111 : Blo 1985435 2981111 := bstep (se 1 (by rfl) ⟨2235833, by rfl⟩ : syracuseStep 2981111 = 4471667) B4471667
theorem B1987407 : Blo 1985435 1987407 := bstep (se 1 (by rfl) ⟨1490555, by rfl⟩ : syracuseStep 1987407 = 2981111) B2981111
theorem B2981117 : Blo 1985435 2981117 := bbase (se 3 (by rfl) ⟨558959, by rfl⟩ : syracuseStep 2981117 = 1117919) (by norm_num)
theorem B1987411 : Blo 1985435 1987411 := bstep (se 1 (by rfl) ⟨1490558, by rfl⟩ : syracuseStep 1987411 = 2981117) B2981117
theorem B4471685 : Blo 1985435 4471685 := bbase (se 4 (by rfl) ⟨419220, by rfl⟩ : syracuseStep 4471685 = 838441) (by norm_num)
theorem B2981123 : Blo 1985435 2981123 := bstep (se 1 (by rfl) ⟨2235842, by rfl⟩ : syracuseStep 2981123 = 4471685) B4471685
theorem B1987415 : Blo 1985435 1987415 := bstep (se 1 (by rfl) ⟨1490561, by rfl⟩ : syracuseStep 1987415 = 2981123) B2981123
theorem B2122309 : Blo 1985435 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B2829745 : Blo 1985435 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B3772993 : Blo 1985435 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B5030657 : Blo 1985435 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B3353771 : Blo 1985435 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B2235847 : Blo 1985435 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B2981129 : Blo 1985435 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B1987419 : Blo 1985435 1987419 := bstep (se 1 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 1987419 = 2981129) B2981129
theorem B10061333 : Blo 1985435 10061333 := bbase (se 6 (by rfl) ⟨235812, by rfl⟩ : syracuseStep 10061333 = 471625) (by norm_num)
theorem B6707555 : Blo 1985435 6707555 := bstep (se 1 (by rfl) ⟨5030666, by rfl⟩ : syracuseStep 6707555 = 10061333) B10061333
theorem B4471703 : Blo 1985435 4471703 := bstep (se 1 (by rfl) ⟨3353777, by rfl⟩ : syracuseStep 4471703 = 6707555) B6707555
theorem B2981135 : Blo 1985435 2981135 := bstep (se 1 (by rfl) ⟨2235851, by rfl⟩ : syracuseStep 2981135 = 4471703) B4471703
theorem B1987423 : Blo 1985435 1987423 := bstep (se 1 (by rfl) ⟨1490567, by rfl⟩ : syracuseStep 1987423 = 2981135) B2981135
theorem B2981141 : Blo 1985435 2981141 := bbase (se 6 (by rfl) ⟨69870, by rfl⟩ : syracuseStep 2981141 = 139741) (by norm_num)
theorem B1987427 : Blo 1985435 1987427 := bstep (se 1 (by rfl) ⟨1490570, by rfl⟩ : syracuseStep 1987427 = 2981141) B2981141
theorem B6126101 : Blo 1985435 6126101 := bbase (se 6 (by rfl) ⟨143580, by rfl⟩ : syracuseStep 6126101 = 287161) (by norm_num)
theorem B4084067 : Blo 1985435 4084067 := bstep (se 1 (by rfl) ⟨3063050, by rfl⟩ : syracuseStep 4084067 = 6126101) B6126101
theorem B10890845 : Blo 1985435 10890845 := bstep (se 3 (by rfl) ⟨2042033, by rfl⟩ : syracuseStep 10890845 = 4084067) B4084067
theorem B7260563 : Blo 1985435 7260563 := bstep (se 1 (by rfl) ⟨5445422, by rfl⟩ : syracuseStep 7260563 = 10890845) B10890845
theorem B19361501 : Blo 1985435 19361501 := bstep (se 3 (by rfl) ⟨3630281, by rfl⟩ : syracuseStep 19361501 = 7260563) B7260563
theorem B12907667 : Blo 1985435 12907667 := bstep (se 1 (by rfl) ⟨9680750, by rfl⟩ : syracuseStep 12907667 = 19361501) B19361501
theorem B8605111 : Blo 1985435 8605111 := bstep (se 1 (by rfl) ⟨6453833, by rfl⟩ : syracuseStep 8605111 = 12907667) B12907667
theorem B11473481 : Blo 1985435 11473481 := bstep (se 2 (by rfl) ⟨4302555, by rfl⟩ : syracuseStep 11473481 = 8605111) B8605111
theorem B7648987 : Blo 1985435 7648987 := bstep (se 1 (by rfl) ⟨5736740, by rfl⟩ : syracuseStep 7648987 = 11473481) B11473481
theorem B10198649 : Blo 1985435 10198649 := bstep (se 2 (by rfl) ⟨3824493, by rfl⟩ : syracuseStep 10198649 = 7648987) B7648987
theorem B6799099 : Blo 1985435 6799099 := bstep (se 1 (by rfl) ⟨5099324, by rfl⟩ : syracuseStep 6799099 = 10198649) B10198649
theorem B9065465 : Blo 1985435 9065465 := bstep (se 2 (by rfl) ⟨3399549, by rfl⟩ : syracuseStep 9065465 = 6799099) B6799099
theorem B6043643 : Blo 1985435 6043643 := bstep (se 1 (by rfl) ⟨4532732, by rfl⟩ : syracuseStep 6043643 = 9065465) B9065465
theorem B4029095 : Blo 1985435 4029095 := bstep (se 1 (by rfl) ⟨3021821, by rfl⟩ : syracuseStep 4029095 = 6043643) B6043643
theorem B10744253 : Blo 1985435 10744253 := bstep (se 3 (by rfl) ⟨2014547, by rfl⟩ : syracuseStep 10744253 = 4029095) B4029095
theorem B7162835 : Blo 1985435 7162835 := bstep (se 1 (by rfl) ⟨5372126, by rfl⟩ : syracuseStep 7162835 = 10744253) B10744253
theorem B19100893 : Blo 1985435 19100893 := bstep (se 3 (by rfl) ⟨3581417, by rfl⟩ : syracuseStep 19100893 = 7162835) B7162835
theorem B25467857 : Blo 1985435 25467857 := bstep (se 2 (by rfl) ⟨9550446, by rfl⟩ : syracuseStep 25467857 = 19100893) B19100893
theorem B16978571 : Blo 1985435 16978571 := bstep (se 1 (by rfl) ⟨12733928, by rfl⟩ : syracuseStep 16978571 = 25467857) B25467857
theorem B11319047 : Blo 1985435 11319047 := bstep (se 1 (by rfl) ⟨8489285, by rfl⟩ : syracuseStep 11319047 = 16978571) B16978571
theorem B7546031 : Blo 1985435 7546031 := bstep (se 1 (by rfl) ⟨5659523, by rfl⟩ : syracuseStep 7546031 = 11319047) B11319047
theorem B5030687 : Blo 1985435 5030687 := bstep (se 1 (by rfl) ⟨3773015, by rfl⟩ : syracuseStep 5030687 = 7546031) B7546031
theorem B3353791 : Blo 1985435 3353791 := bstep (se 1 (by rfl) ⟨2515343, by rfl⟩ : syracuseStep 3353791 = 5030687) B5030687
theorem B4471721 : Blo 1985435 4471721 := bstep (se 2 (by rfl) ⟨1676895, by rfl⟩ : syracuseStep 4471721 = 3353791) B3353791
theorem B2981147 : Blo 1985435 2981147 := bstep (se 1 (by rfl) ⟨2235860, by rfl⟩ : syracuseStep 2981147 = 4471721) B4471721
theorem B1987431 : Blo 1985435 1987431 := bstep (se 1 (by rfl) ⟨1490573, by rfl⟩ : syracuseStep 1987431 = 2981147) B2981147
theorem B2235865 : Blo 1985435 2235865 := bbase (se 2 (by rfl) ⟨838449, by rfl⟩ : syracuseStep 2235865 = 1676899) (by norm_num)
theorem B2981153 : Blo 1985435 2981153 := bstep (se 2 (by rfl) ⟨1117932, by rfl⟩ : syracuseStep 2981153 = 2235865) B2235865
theorem B1987435 : Blo 1985435 1987435 := bstep (se 1 (by rfl) ⟨1490576, by rfl⟩ : syracuseStep 1987435 = 2981153) B2981153
theorem C0 (j : ℕ) (h1 : 496358 ≤ j) (h2 : j ≤ 496858) : Blo 1985435 (4 * j + 3) := by
  interval_cases j
  · exact B1985435
  · exact B1985439
  · exact B1985443
  · exact B1985447
  · exact B1985451
  · exact B1985455
  · exact B1985459
  · exact B1985463
  · exact B1985467
  · exact B1985471
  · exact B1985475
  · exact B1985479
  · exact B1985483
  · exact B1985487
  · exact B1985491
  · exact B1985495
  · exact B1985499
  · exact B1985503
  · exact B1985507
  · exact B1985511
  · exact B1985515
  · exact B1985519
  · exact B1985523
  · exact B1985527
  · exact B1985531
  · exact B1985535
  · exact B1985539
  · exact B1985543
  · exact B1985547
  · exact B1985551
  · exact B1985555
  · exact B1985559
  · exact B1985563
  · exact B1985567
  · exact B1985571
  · exact B1985575
  · exact B1985579
  · exact B1985583
  · exact B1985587
  · exact B1985591
  · exact B1985595
  · exact B1985599
  · exact B1985603
  · exact B1985607
  · exact B1985611
  · exact B1985615
  · exact B1985619
  · exact B1985623
  · exact B1985627
  · exact B1985631
  · exact B1985635
  · exact B1985639
  · exact B1985643
  · exact B1985647
  · exact B1985651
  · exact B1985655
  · exact B1985659
  · exact B1985663
  · exact B1985667
  · exact B1985671
  · exact B1985675
  · exact B1985679
  · exact B1985683
  · exact B1985687
  · exact B1985691
  · exact B1985695
  · exact B1985699
  · exact B1985703
  · exact B1985707
  · exact B1985711
  · exact B1985715
  · exact B1985719
  · exact B1985723
  · exact B1985727
  · exact B1985731
  · exact B1985735
  · exact B1985739
  · exact B1985743
  · exact B1985747
  · exact B1985751
  · exact B1985755
  · exact B1985759
  · exact B1985763
  · exact B1985767
  · exact B1985771
  · exact B1985775
  · exact B1985779
  · exact B1985783
  · exact B1985787
  · exact B1985791
  · exact B1985795
  · exact B1985799
  · exact B1985803
  · exact B1985807
  · exact B1985811
  · exact B1985815
  · exact B1985819
  · exact B1985823
  · exact B1985827
  · exact B1985831
  · exact B1985835
  · exact B1985839
  · exact B1985843
  · exact B1985847
  · exact B1985851
  · exact B1985855
  · exact B1985859
  · exact B1985863
  · exact B1985867
  · exact B1985871
  · exact B1985875
  · exact B1985879
  · exact B1985883
  · exact B1985887
  · exact B1985891
  · exact B1985895
  · exact B1985899
  · exact B1985903
  · exact B1985907
  · exact B1985911
  · exact B1985915
  · exact B1985919
  · exact B1985923
  · exact B1985927
  · exact B1985931
  · exact B1985935
  · exact B1985939
  · exact B1985943
  · exact B1985947
  · exact B1985951
  · exact B1985955
  · exact B1985959
  · exact B1985963
  · exact B1985967
  · exact B1985971
  · exact B1985975
  · exact B1985979
  · exact B1985983
  · exact B1985987
  · exact B1985991
  · exact B1985995
  · exact B1985999
  · exact B1986003
  · exact B1986007
  · exact B1986011
  · exact B1986015
  · exact B1986019
  · exact B1986023
  · exact B1986027
  · exact B1986031
  · exact B1986035
  · exact B1986039
  · exact B1986043
  · exact B1986047
  · exact B1986051
  · exact B1986055
  · exact B1986059
  · exact B1986063
  · exact B1986067
  · exact B1986071
  · exact B1986075
  · exact B1986079
  · exact B1986083
  · exact B1986087
  · exact B1986091
  · exact B1986095
  · exact B1986099
  · exact B1986103
  · exact B1986107
  · exact B1986111
  · exact B1986115
  · exact B1986119
  · exact B1986123
  · exact B1986127
  · exact B1986131
  · exact B1986135
  · exact B1986139
  · exact B1986143
  · exact B1986147
  · exact B1986151
  · exact B1986155
  · exact B1986159
  · exact B1986163
  · exact B1986167
  · exact B1986171
  · exact B1986175
  · exact B1986179
  · exact B1986183
  · exact B1986187
  · exact B1986191
  · exact B1986195
  · exact B1986199
  · exact B1986203
  · exact B1986207
  · exact B1986211
  · exact B1986215
  · exact B1986219
  · exact B1986223
  · exact B1986227
  · exact B1986231
  · exact B1986235
  · exact B1986239
  · exact B1986243
  · exact B1986247
  · exact B1986251
  · exact B1986255
  · exact B1986259
  · exact B1986263
  · exact B1986267
  · exact B1986271
  · exact B1986275
  · exact B1986279
  · exact B1986283
  · exact B1986287
  · exact B1986291
  · exact B1986295
  · exact B1986299
  · exact B1986303
  · exact B1986307
  · exact B1986311
  · exact B1986315
  · exact B1986319
  · exact B1986323
  · exact B1986327
  · exact B1986331
  · exact B1986335
  · exact B1986339
  · exact B1986343
  · exact B1986347
  · exact B1986351
  · exact B1986355
  · exact B1986359
  · exact B1986363
  · exact B1986367
  · exact B1986371
  · exact B1986375
  · exact B1986379
  · exact B1986383
  · exact B1986387
  · exact B1986391
  · exact B1986395
  · exact B1986399
  · exact B1986403
  · exact B1986407
  · exact B1986411
  · exact B1986415
  · exact B1986419
  · exact B1986423
  · exact B1986427
  · exact B1986431
  · exact B1986435
  · exact B1986439
  · exact B1986443
  · exact B1986447
  · exact B1986451
  · exact B1986455
  · exact B1986459
  · exact B1986463
  · exact B1986467
  · exact B1986471
  · exact B1986475
  · exact B1986479
  · exact B1986483
  · exact B1986487
  · exact B1986491
  · exact B1986495
  · exact B1986499
  · exact B1986503
  · exact B1986507
  · exact B1986511
  · exact B1986515
  · exact B1986519
  · exact B1986523
  · exact B1986527
  · exact B1986531
  · exact B1986535
  · exact B1986539
  · exact B1986543
  · exact B1986547
  · exact B1986551
  · exact B1986555
  · exact B1986559
  · exact B1986563
  · exact B1986567
  · exact B1986571
  · exact B1986575
  · exact B1986579
  · exact B1986583
  · exact B1986587
  · exact B1986591
  · exact B1986595
  · exact B1986599
  · exact B1986603
  · exact B1986607
  · exact B1986611
  · exact B1986615
  · exact B1986619
  · exact B1986623
  · exact B1986627
  · exact B1986631
  · exact B1986635
  · exact B1986639
  · exact B1986643
  · exact B1986647
  · exact B1986651
  · exact B1986655
  · exact B1986659
  · exact B1986663
  · exact B1986667
  · exact B1986671
  · exact B1986675
  · exact B1986679
  · exact B1986683
  · exact B1986687
  · exact B1986691
  · exact B1986695
  · exact B1986699
  · exact B1986703
  · exact B1986707
  · exact B1986711
  · exact B1986715
  · exact B1986719
  · exact B1986723
  · exact B1986727
  · exact B1986731
  · exact B1986735
  · exact B1986739
  · exact B1986743
  · exact B1986747
  · exact B1986751
  · exact B1986755
  · exact B1986759
  · exact B1986763
  · exact B1986767
  · exact B1986771
  · exact B1986775
  · exact B1986779
  · exact B1986783
  · exact B1986787
  · exact B1986791
  · exact B1986795
  · exact B1986799
  · exact B1986803
  · exact B1986807
  · exact B1986811
  · exact B1986815
  · exact B1986819
  · exact B1986823
  · exact B1986827
  · exact B1986831
  · exact B1986835
  · exact B1986839
  · exact B1986843
  · exact B1986847
  · exact B1986851
  · exact B1986855
  · exact B1986859
  · exact B1986863
  · exact B1986867
  · exact B1986871
  · exact B1986875
  · exact B1986879
  · exact B1986883
  · exact B1986887
  · exact B1986891
  · exact B1986895
  · exact B1986899
  · exact B1986903
  · exact B1986907
  · exact B1986911
  · exact B1986915
  · exact B1986919
  · exact B1986923
  · exact B1986927
  · exact B1986931
  · exact B1986935
  · exact B1986939
  · exact B1986943
  · exact B1986947
  · exact B1986951
  · exact B1986955
  · exact B1986959
  · exact B1986963
  · exact B1986967
  · exact B1986971
  · exact B1986975
  · exact B1986979
  · exact B1986983
  · exact B1986987
  · exact B1986991
  · exact B1986995
  · exact B1986999
  · exact B1987003
  · exact B1987007
  · exact B1987011
  · exact B1987015
  · exact B1987019
  · exact B1987023
  · exact B1987027
  · exact B1987031
  · exact B1987035
  · exact B1987039
  · exact B1987043
  · exact B1987047
  · exact B1987051
  · exact B1987055
  · exact B1987059
  · exact B1987063
  · exact B1987067
  · exact B1987071
  · exact B1987075
  · exact B1987079
  · exact B1987083
  · exact B1987087
  · exact B1987091
  · exact B1987095
  · exact B1987099
  · exact B1987103
  · exact B1987107
  · exact B1987111
  · exact B1987115
  · exact B1987119
  · exact B1987123
  · exact B1987127
  · exact B1987131
  · exact B1987135
  · exact B1987139
  · exact B1987143
  · exact B1987147
  · exact B1987151
  · exact B1987155
  · exact B1987159
  · exact B1987163
  · exact B1987167
  · exact B1987171
  · exact B1987175
  · exact B1987179
  · exact B1987183
  · exact B1987187
  · exact B1987191
  · exact B1987195
  · exact B1987199
  · exact B1987203
  · exact B1987207
  · exact B1987211
  · exact B1987215
  · exact B1987219
  · exact B1987223
  · exact B1987227
  · exact B1987231
  · exact B1987235
  · exact B1987239
  · exact B1987243
  · exact B1987247
  · exact B1987251
  · exact B1987255
  · exact B1987259
  · exact B1987263
  · exact B1987267
  · exact B1987271
  · exact B1987275
  · exact B1987279
  · exact B1987283
  · exact B1987287
  · exact B1987291
  · exact B1987295
  · exact B1987299
  · exact B1987303
  · exact B1987307
  · exact B1987311
  · exact B1987315
  · exact B1987319
  · exact B1987323
  · exact B1987327
  · exact B1987331
  · exact B1987335
  · exact B1987339
  · exact B1987343
  · exact B1987347
  · exact B1987351
  · exact B1987355
  · exact B1987359
  · exact B1987363
  · exact B1987367
  · exact B1987371
  · exact B1987375
  · exact B1987379
  · exact B1987383
  · exact B1987387
  · exact B1987391
  · exact B1987395
  · exact B1987399
  · exact B1987403
  · exact B1987407
  · exact B1987411
  · exact B1987415
  · exact B1987419
  · exact B1987423
  · exact B1987427
  · exact B1987431
  · exact B1987435
theorem solution (m : ℕ) (hlo : 1985435 ≤ m) (hhi : m ≤ 1987435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 496358 ≤ j := by omega
    have hj2 : j ≤ 496858 := by omega
    have hb : Blo 1985435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
