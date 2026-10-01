-- Prove2me | solution 1 for syracuse_descends_range_2169435_2171435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:45.905031+00:00
-- url     : https://prove2.me/submissions/ff7cc3a8-4f16-499e-95ae-05a8f2cb5878

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

theorem B4633357 : Blo 2169435 4633357 := bbase (se 3 (by rfl) ⟨868754, by rfl⟩ : syracuseStep 4633357 = 1737509) (by norm_num)
theorem B6177809 : Blo 2169435 6177809 := bstep (se 2 (by rfl) ⟨2316678, by rfl⟩ : syracuseStep 6177809 = 4633357) B4633357
theorem B4118539 : Blo 2169435 4118539 := bstep (se 1 (by rfl) ⟨3088904, by rfl⟩ : syracuseStep 4118539 = 6177809) B6177809
theorem B5491385 : Blo 2169435 5491385 := bstep (se 2 (by rfl) ⟨2059269, by rfl⟩ : syracuseStep 5491385 = 4118539) B4118539
theorem B3660923 : Blo 2169435 3660923 := bstep (se 1 (by rfl) ⟨2745692, by rfl⟩ : syracuseStep 3660923 = 5491385) B5491385
theorem B2440615 : Blo 2169435 2440615 := bstep (se 1 (by rfl) ⟨1830461, by rfl⟩ : syracuseStep 2440615 = 3660923) B3660923
theorem B3254153 : Blo 2169435 3254153 := bstep (se 2 (by rfl) ⟨1220307, by rfl⟩ : syracuseStep 3254153 = 2440615) B2440615
theorem B2169435 : Blo 2169435 2169435 := bstep (se 1 (by rfl) ⟨1627076, by rfl⟩ : syracuseStep 2169435 = 3254153) B3254153
theorem B10982789 : Blo 2169435 10982789 := bbase (se 4 (by rfl) ⟨1029636, by rfl⟩ : syracuseStep 10982789 = 2059273) (by norm_num)
theorem B7321859 : Blo 2169435 7321859 := bstep (se 1 (by rfl) ⟨5491394, by rfl⟩ : syracuseStep 7321859 = 10982789) B10982789
theorem B4881239 : Blo 2169435 4881239 := bstep (se 1 (by rfl) ⟨3660929, by rfl⟩ : syracuseStep 4881239 = 7321859) B7321859
theorem B3254159 : Blo 2169435 3254159 := bstep (se 1 (by rfl) ⟨2440619, by rfl⟩ : syracuseStep 3254159 = 4881239) B4881239
theorem B2169439 : Blo 2169435 2169439 := bstep (se 1 (by rfl) ⟨1627079, by rfl⟩ : syracuseStep 2169439 = 3254159) B3254159
theorem B3254165 : Blo 2169435 3254165 := bbase (se 6 (by rfl) ⟨76269, by rfl⟩ : syracuseStep 3254165 = 152539) (by norm_num)
theorem B2169443 : Blo 2169435 2169443 := bstep (se 1 (by rfl) ⟨1627082, by rfl⟩ : syracuseStep 2169443 = 3254165) B3254165
theorem B3475037 : Blo 2169435 3475037 := bbase (se 3 (by rfl) ⟨651569, by rfl⟩ : syracuseStep 3475037 = 1303139) (by norm_num)
theorem B2316691 : Blo 2169435 2316691 := bstep (se 1 (by rfl) ⟨1737518, by rfl⟩ : syracuseStep 2316691 = 3475037) B3475037
theorem B12355685 : Blo 2169435 12355685 := bstep (se 4 (by rfl) ⟨1158345, by rfl⟩ : syracuseStep 12355685 = 2316691) B2316691
theorem B8237123 : Blo 2169435 8237123 := bstep (se 1 (by rfl) ⟨6177842, by rfl⟩ : syracuseStep 8237123 = 12355685) B12355685
theorem B5491415 : Blo 2169435 5491415 := bstep (se 1 (by rfl) ⟨4118561, by rfl⟩ : syracuseStep 5491415 = 8237123) B8237123
theorem B3660943 : Blo 2169435 3660943 := bstep (se 1 (by rfl) ⟨2745707, by rfl⟩ : syracuseStep 3660943 = 5491415) B5491415
theorem B4881257 : Blo 2169435 4881257 := bstep (se 2 (by rfl) ⟨1830471, by rfl⟩ : syracuseStep 4881257 = 3660943) B3660943
theorem B3254171 : Blo 2169435 3254171 := bstep (se 1 (by rfl) ⟨2440628, by rfl⟩ : syracuseStep 3254171 = 4881257) B4881257
theorem B2169447 : Blo 2169435 2169447 := bstep (se 1 (by rfl) ⟨1627085, by rfl⟩ : syracuseStep 2169447 = 3254171) B3254171
theorem B2440633 : Blo 2169435 2440633 := bbase (se 2 (by rfl) ⟨915237, by rfl⟩ : syracuseStep 2440633 = 1830475) (by norm_num)
theorem B3254177 : Blo 2169435 3254177 := bstep (se 2 (by rfl) ⟨1220316, by rfl⟩ : syracuseStep 3254177 = 2440633) B2440633
theorem B2169451 : Blo 2169435 2169451 := bstep (se 1 (by rfl) ⟨1627088, by rfl⟩ : syracuseStep 2169451 = 3254177) B3254177
theorem B7421813 : Blo 2169435 7421813 := bbase (se 5 (by rfl) ⟨347897, by rfl⟩ : syracuseStep 7421813 = 695795) (by norm_num)
theorem B4947875 : Blo 2169435 4947875 := bstep (se 1 (by rfl) ⟨3710906, by rfl⟩ : syracuseStep 4947875 = 7421813) B7421813
theorem B3298583 : Blo 2169435 3298583 := bstep (se 1 (by rfl) ⟨2473937, by rfl⟩ : syracuseStep 3298583 = 4947875) B4947875
theorem B8796221 : Blo 2169435 8796221 := bstep (se 3 (by rfl) ⟨1649291, by rfl⟩ : syracuseStep 8796221 = 3298583) B3298583
theorem B5864147 : Blo 2169435 5864147 := bstep (se 1 (by rfl) ⟨4398110, by rfl⟩ : syracuseStep 5864147 = 8796221) B8796221
theorem B3909431 : Blo 2169435 3909431 := bstep (se 1 (by rfl) ⟨2932073, by rfl⟩ : syracuseStep 3909431 = 5864147) B5864147
theorem B10425149 : Blo 2169435 10425149 := bstep (se 3 (by rfl) ⟨1954715, by rfl⟩ : syracuseStep 10425149 = 3909431) B3909431
theorem B6950099 : Blo 2169435 6950099 := bstep (se 1 (by rfl) ⟨5212574, by rfl⟩ : syracuseStep 6950099 = 10425149) B10425149
theorem B4633399 : Blo 2169435 4633399 := bstep (se 1 (by rfl) ⟨3475049, by rfl⟩ : syracuseStep 4633399 = 6950099) B6950099
theorem B6177865 : Blo 2169435 6177865 := bstep (se 2 (by rfl) ⟨2316699, by rfl⟩ : syracuseStep 6177865 = 4633399) B4633399
theorem B8237153 : Blo 2169435 8237153 := bstep (se 2 (by rfl) ⟨3088932, by rfl⟩ : syracuseStep 8237153 = 6177865) B6177865
theorem B5491435 : Blo 2169435 5491435 := bstep (se 1 (by rfl) ⟨4118576, by rfl⟩ : syracuseStep 5491435 = 8237153) B8237153
theorem B7321913 : Blo 2169435 7321913 := bstep (se 2 (by rfl) ⟨2745717, by rfl⟩ : syracuseStep 7321913 = 5491435) B5491435
theorem B4881275 : Blo 2169435 4881275 := bstep (se 1 (by rfl) ⟨3660956, by rfl⟩ : syracuseStep 4881275 = 7321913) B7321913
theorem B3254183 : Blo 2169435 3254183 := bstep (se 1 (by rfl) ⟨2440637, by rfl⟩ : syracuseStep 3254183 = 4881275) B4881275
theorem B2169455 : Blo 2169435 2169455 := bstep (se 1 (by rfl) ⟨1627091, by rfl⟩ : syracuseStep 2169455 = 3254183) B3254183
theorem B3254189 : Blo 2169435 3254189 := bbase (se 3 (by rfl) ⟨610160, by rfl⟩ : syracuseStep 3254189 = 1220321) (by norm_num)
theorem B2169459 : Blo 2169435 2169459 := bstep (se 1 (by rfl) ⟨1627094, by rfl⟩ : syracuseStep 2169459 = 3254189) B3254189
theorem B4881293 : Blo 2169435 4881293 := bbase (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) (by norm_num)
theorem B3254195 : Blo 2169435 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B2169463 : Blo 2169435 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B2745733 : Blo 2169435 2745733 := bbase (se 4 (by rfl) ⟨257412, by rfl⟩ : syracuseStep 2745733 = 514825) (by norm_num)
theorem B3660977 : Blo 2169435 3660977 := bstep (se 2 (by rfl) ⟨1372866, by rfl⟩ : syracuseStep 3660977 = 2745733) B2745733
theorem B2440651 : Blo 2169435 2440651 := bstep (se 1 (by rfl) ⟨1830488, by rfl⟩ : syracuseStep 2440651 = 3660977) B3660977
theorem B3254201 : Blo 2169435 3254201 := bstep (se 2 (by rfl) ⟨1220325, by rfl⟩ : syracuseStep 3254201 = 2440651) B2440651
theorem B2169467 : Blo 2169435 2169467 := bstep (se 1 (by rfl) ⟨1627100, by rfl⟩ : syracuseStep 2169467 = 3254201) B3254201
theorem B27800597 : Blo 2169435 27800597 := bbase (se 6 (by rfl) ⟨651576, by rfl⟩ : syracuseStep 27800597 = 1303153) (by norm_num)
theorem B18533731 : Blo 2169435 18533731 := bstep (se 1 (by rfl) ⟨13900298, by rfl⟩ : syracuseStep 18533731 = 27800597) B27800597
theorem B24711641 : Blo 2169435 24711641 := bstep (se 2 (by rfl) ⟨9266865, by rfl⟩ : syracuseStep 24711641 = 18533731) B18533731
theorem B16474427 : Blo 2169435 16474427 := bstep (se 1 (by rfl) ⟨12355820, by rfl⟩ : syracuseStep 16474427 = 24711641) B24711641
theorem B10982951 : Blo 2169435 10982951 := bstep (se 1 (by rfl) ⟨8237213, by rfl⟩ : syracuseStep 10982951 = 16474427) B16474427
theorem B7321967 : Blo 2169435 7321967 := bstep (se 1 (by rfl) ⟨5491475, by rfl⟩ : syracuseStep 7321967 = 10982951) B10982951
theorem B4881311 : Blo 2169435 4881311 := bstep (se 1 (by rfl) ⟨3660983, by rfl⟩ : syracuseStep 4881311 = 7321967) B7321967
theorem B3254207 : Blo 2169435 3254207 := bstep (se 1 (by rfl) ⟨2440655, by rfl⟩ : syracuseStep 3254207 = 4881311) B4881311
theorem B2169471 : Blo 2169435 2169471 := bstep (se 1 (by rfl) ⟨1627103, by rfl⟩ : syracuseStep 2169471 = 3254207) B3254207
theorem B3254213 : Blo 2169435 3254213 := bbase (se 4 (by rfl) ⟨305082, by rfl⟩ : syracuseStep 3254213 = 610165) (by norm_num)
theorem B2169475 : Blo 2169435 2169475 := bstep (se 1 (by rfl) ⟨1627106, by rfl⟩ : syracuseStep 2169475 = 3254213) B3254213
theorem B3660997 : Blo 2169435 3660997 := bbase (se 4 (by rfl) ⟨343218, by rfl⟩ : syracuseStep 3660997 = 686437) (by norm_num)
theorem B4881329 : Blo 2169435 4881329 := bstep (se 2 (by rfl) ⟨1830498, by rfl⟩ : syracuseStep 4881329 = 3660997) B3660997
theorem B3254219 : Blo 2169435 3254219 := bstep (se 1 (by rfl) ⟨2440664, by rfl⟩ : syracuseStep 3254219 = 4881329) B4881329
theorem B2169479 : Blo 2169435 2169479 := bstep (se 1 (by rfl) ⟨1627109, by rfl⟩ : syracuseStep 2169479 = 3254219) B3254219
theorem B2440669 : Blo 2169435 2440669 := bbase (se 3 (by rfl) ⟨457625, by rfl⟩ : syracuseStep 2440669 = 915251) (by norm_num)
theorem B3254225 : Blo 2169435 3254225 := bstep (se 2 (by rfl) ⟨1220334, by rfl⟩ : syracuseStep 3254225 = 2440669) B2440669
theorem B2169483 : Blo 2169435 2169483 := bstep (se 1 (by rfl) ⟨1627112, by rfl⟩ : syracuseStep 2169483 = 3254225) B3254225
theorem B7322021 : Blo 2169435 7322021 := bbase (se 4 (by rfl) ⟨686439, by rfl⟩ : syracuseStep 7322021 = 1372879) (by norm_num)
theorem B4881347 : Blo 2169435 4881347 := bstep (se 1 (by rfl) ⟨3661010, by rfl⟩ : syracuseStep 4881347 = 7322021) B7322021
theorem B3254231 : Blo 2169435 3254231 := bstep (se 1 (by rfl) ⟨2440673, by rfl⟩ : syracuseStep 3254231 = 4881347) B4881347
theorem B2169487 : Blo 2169435 2169487 := bstep (se 1 (by rfl) ⟨1627115, by rfl⟩ : syracuseStep 2169487 = 3254231) B3254231
theorem B3254237 : Blo 2169435 3254237 := bbase (se 3 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 3254237 = 1220339) (by norm_num)
theorem B2169491 : Blo 2169435 2169491 := bstep (se 1 (by rfl) ⟨1627118, by rfl⟩ : syracuseStep 2169491 = 3254237) B3254237
theorem B4881365 : Blo 2169435 4881365 := bbase (se 7 (by rfl) ⟨57203, by rfl⟩ : syracuseStep 4881365 = 114407) (by norm_num)
theorem B3254243 : Blo 2169435 3254243 := bstep (se 1 (by rfl) ⟨2440682, by rfl⟩ : syracuseStep 3254243 = 4881365) B4881365
theorem B2169495 : Blo 2169435 2169495 := bstep (se 1 (by rfl) ⟨1627121, by rfl⟩ : syracuseStep 2169495 = 3254243) B3254243
theorem B2932133 : Blo 2169435 2932133 := bbase (se 4 (by rfl) ⟨274887, by rfl⟩ : syracuseStep 2932133 = 549775) (by norm_num)
theorem B7819021 : Blo 2169435 7819021 := bstep (se 3 (by rfl) ⟨1466066, by rfl⟩ : syracuseStep 7819021 = 2932133) B2932133
theorem B10425361 : Blo 2169435 10425361 := bstep (se 2 (by rfl) ⟨3909510, by rfl⟩ : syracuseStep 10425361 = 7819021) B7819021
theorem B13900481 : Blo 2169435 13900481 := bstep (se 2 (by rfl) ⟨5212680, by rfl⟩ : syracuseStep 13900481 = 10425361) B10425361
theorem B9266987 : Blo 2169435 9266987 := bstep (se 1 (by rfl) ⟨6950240, by rfl⟩ : syracuseStep 9266987 = 13900481) B13900481
theorem B6177991 : Blo 2169435 6177991 := bstep (se 1 (by rfl) ⟨4633493, by rfl⟩ : syracuseStep 6177991 = 9266987) B9266987
theorem B8237321 : Blo 2169435 8237321 := bstep (se 2 (by rfl) ⟨3088995, by rfl⟩ : syracuseStep 8237321 = 6177991) B6177991
theorem B5491547 : Blo 2169435 5491547 := bstep (se 1 (by rfl) ⟨4118660, by rfl⟩ : syracuseStep 5491547 = 8237321) B8237321
theorem B3661031 : Blo 2169435 3661031 := bstep (se 1 (by rfl) ⟨2745773, by rfl⟩ : syracuseStep 3661031 = 5491547) B5491547
theorem B2440687 : Blo 2169435 2440687 := bstep (se 1 (by rfl) ⟨1830515, by rfl⟩ : syracuseStep 2440687 = 3661031) B3661031
theorem B3254249 : Blo 2169435 3254249 := bstep (se 2 (by rfl) ⟨1220343, by rfl⟩ : syracuseStep 3254249 = 2440687) B2440687
theorem B2169499 : Blo 2169435 2169499 := bstep (se 1 (by rfl) ⟨1627124, by rfl⟩ : syracuseStep 2169499 = 3254249) B3254249
theorem B18534005 : Blo 2169435 18534005 := bbase (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) (by norm_num)
theorem B12356003 : Blo 2169435 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B8237335 : Blo 2169435 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B10983113 : Blo 2169435 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B7322075 : Blo 2169435 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B4881383 : Blo 2169435 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B3254255 : Blo 2169435 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B2169503 : Blo 2169435 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B3254261 : Blo 2169435 3254261 := bbase (se 5 (by rfl) ⟨152543, by rfl⟩ : syracuseStep 3254261 = 305087) (by norm_num)
theorem B2169507 : Blo 2169435 2169507 := bstep (se 1 (by rfl) ⟨1627130, by rfl⟩ : syracuseStep 2169507 = 3254261) B3254261
theorem B11728597 : Blo 2169435 11728597 := bbase (se 7 (by rfl) ⟨137444, by rfl⟩ : syracuseStep 11728597 = 274889) (by norm_num)
theorem B15638129 : Blo 2169435 15638129 := bstep (se 2 (by rfl) ⟨5864298, by rfl⟩ : syracuseStep 15638129 = 11728597) B11728597
theorem B10425419 : Blo 2169435 10425419 := bstep (se 1 (by rfl) ⟨7819064, by rfl⟩ : syracuseStep 10425419 = 15638129) B15638129
theorem B6950279 : Blo 2169435 6950279 := bstep (se 1 (by rfl) ⟨5212709, by rfl⟩ : syracuseStep 6950279 = 10425419) B10425419
theorem B4633519 : Blo 2169435 4633519 := bstep (se 1 (by rfl) ⟨3475139, by rfl⟩ : syracuseStep 4633519 = 6950279) B6950279
theorem B6178025 : Blo 2169435 6178025 := bstep (se 2 (by rfl) ⟨2316759, by rfl⟩ : syracuseStep 6178025 = 4633519) B4633519
theorem B4118683 : Blo 2169435 4118683 := bstep (se 1 (by rfl) ⟨3089012, by rfl⟩ : syracuseStep 4118683 = 6178025) B6178025
theorem B5491577 : Blo 2169435 5491577 := bstep (se 2 (by rfl) ⟨2059341, by rfl⟩ : syracuseStep 5491577 = 4118683) B4118683
theorem B3661051 : Blo 2169435 3661051 := bstep (se 1 (by rfl) ⟨2745788, by rfl⟩ : syracuseStep 3661051 = 5491577) B5491577
theorem B4881401 : Blo 2169435 4881401 := bstep (se 2 (by rfl) ⟨1830525, by rfl⟩ : syracuseStep 4881401 = 3661051) B3661051
theorem B3254267 : Blo 2169435 3254267 := bstep (se 1 (by rfl) ⟨2440700, by rfl⟩ : syracuseStep 3254267 = 4881401) B4881401
theorem B2169511 : Blo 2169435 2169511 := bstep (se 1 (by rfl) ⟨1627133, by rfl⟩ : syracuseStep 2169511 = 3254267) B3254267
theorem B2440705 : Blo 2169435 2440705 := bbase (se 2 (by rfl) ⟨915264, by rfl⟩ : syracuseStep 2440705 = 1830529) (by norm_num)
theorem B3254273 : Blo 2169435 3254273 := bstep (se 2 (by rfl) ⟨1220352, by rfl⟩ : syracuseStep 3254273 = 2440705) B2440705
theorem B2169515 : Blo 2169435 2169515 := bstep (se 1 (by rfl) ⟨1627136, by rfl⟩ : syracuseStep 2169515 = 3254273) B3254273
theorem B5491597 : Blo 2169435 5491597 := bbase (se 3 (by rfl) ⟨1029674, by rfl⟩ : syracuseStep 5491597 = 2059349) (by norm_num)
theorem B7322129 : Blo 2169435 7322129 := bstep (se 2 (by rfl) ⟨2745798, by rfl⟩ : syracuseStep 7322129 = 5491597) B5491597
theorem B4881419 : Blo 2169435 4881419 := bstep (se 1 (by rfl) ⟨3661064, by rfl⟩ : syracuseStep 4881419 = 7322129) B7322129
theorem B3254279 : Blo 2169435 3254279 := bstep (se 1 (by rfl) ⟨2440709, by rfl⟩ : syracuseStep 3254279 = 4881419) B4881419
theorem B2169519 : Blo 2169435 2169519 := bstep (se 1 (by rfl) ⟨1627139, by rfl⟩ : syracuseStep 2169519 = 3254279) B3254279
theorem B3254285 : Blo 2169435 3254285 := bbase (se 3 (by rfl) ⟨610178, by rfl⟩ : syracuseStep 3254285 = 1220357) (by norm_num)
theorem B2169523 : Blo 2169435 2169523 := bstep (se 1 (by rfl) ⟨1627142, by rfl⟩ : syracuseStep 2169523 = 3254285) B3254285
theorem B4881437 : Blo 2169435 4881437 := bbase (se 3 (by rfl) ⟨915269, by rfl⟩ : syracuseStep 4881437 = 1830539) (by norm_num)
theorem B3254291 : Blo 2169435 3254291 := bstep (se 1 (by rfl) ⟨2440718, by rfl⟩ : syracuseStep 3254291 = 4881437) B4881437
theorem B2169527 : Blo 2169435 2169527 := bstep (se 1 (by rfl) ⟨1627145, by rfl⟩ : syracuseStep 2169527 = 3254291) B3254291
theorem B3661085 : Blo 2169435 3661085 := bbase (se 3 (by rfl) ⟨686453, by rfl⟩ : syracuseStep 3661085 = 1372907) (by norm_num)
theorem B2440723 : Blo 2169435 2440723 := bstep (se 1 (by rfl) ⟨1830542, by rfl⟩ : syracuseStep 2440723 = 3661085) B3661085
theorem B3254297 : Blo 2169435 3254297 := bstep (se 2 (by rfl) ⟨1220361, by rfl⟩ : syracuseStep 3254297 = 2440723) B2440723
theorem B2169531 : Blo 2169435 2169531 := bstep (se 1 (by rfl) ⟨1627148, by rfl⟩ : syracuseStep 2169531 = 3254297) B3254297
theorem B5566565 : Blo 2169435 5566565 := bbase (se 4 (by rfl) ⟨521865, by rfl⟩ : syracuseStep 5566565 = 1043731) (by norm_num)
theorem B3711043 : Blo 2169435 3711043 := bstep (se 1 (by rfl) ⟨2783282, by rfl⟩ : syracuseStep 3711043 = 5566565) B5566565
theorem B4948057 : Blo 2169435 4948057 := bstep (se 2 (by rfl) ⟨1855521, by rfl⟩ : syracuseStep 4948057 = 3711043) B3711043
theorem B6597409 : Blo 2169435 6597409 := bstep (se 2 (by rfl) ⟨2474028, by rfl⟩ : syracuseStep 6597409 = 4948057) B4948057
theorem B8796545 : Blo 2169435 8796545 := bstep (se 2 (by rfl) ⟨3298704, by rfl⟩ : syracuseStep 8796545 = 6597409) B6597409
theorem B5864363 : Blo 2169435 5864363 := bstep (se 1 (by rfl) ⟨4398272, by rfl⟩ : syracuseStep 5864363 = 8796545) B8796545
theorem B3909575 : Blo 2169435 3909575 := bstep (se 1 (by rfl) ⟨2932181, by rfl⟩ : syracuseStep 3909575 = 5864363) B5864363
theorem B2606383 : Blo 2169435 2606383 := bstep (se 1 (by rfl) ⟨1954787, by rfl⟩ : syracuseStep 2606383 = 3909575) B3909575
theorem B13900709 : Blo 2169435 13900709 := bstep (se 4 (by rfl) ⟨1303191, by rfl⟩ : syracuseStep 13900709 = 2606383) B2606383
theorem B9267139 : Blo 2169435 9267139 := bstep (se 1 (by rfl) ⟨6950354, by rfl⟩ : syracuseStep 9267139 = 13900709) B13900709
theorem B12356185 : Blo 2169435 12356185 := bstep (se 2 (by rfl) ⟨4633569, by rfl⟩ : syracuseStep 12356185 = 9267139) B9267139
theorem B16474913 : Blo 2169435 16474913 := bstep (se 2 (by rfl) ⟨6178092, by rfl⟩ : syracuseStep 16474913 = 12356185) B12356185
theorem B10983275 : Blo 2169435 10983275 := bstep (se 1 (by rfl) ⟨8237456, by rfl⟩ : syracuseStep 10983275 = 16474913) B16474913
theorem B7322183 : Blo 2169435 7322183 := bstep (se 1 (by rfl) ⟨5491637, by rfl⟩ : syracuseStep 7322183 = 10983275) B10983275
theorem B4881455 : Blo 2169435 4881455 := bstep (se 1 (by rfl) ⟨3661091, by rfl⟩ : syracuseStep 4881455 = 7322183) B7322183
theorem B3254303 : Blo 2169435 3254303 := bstep (se 1 (by rfl) ⟨2440727, by rfl⟩ : syracuseStep 3254303 = 4881455) B4881455
theorem B2169535 : Blo 2169435 2169535 := bstep (se 1 (by rfl) ⟨1627151, by rfl⟩ : syracuseStep 2169535 = 3254303) B3254303
theorem B3254309 : Blo 2169435 3254309 := bbase (se 4 (by rfl) ⟨305091, by rfl⟩ : syracuseStep 3254309 = 610183) (by norm_num)
theorem B2169539 : Blo 2169435 2169539 := bstep (se 1 (by rfl) ⟨1627154, by rfl⟩ : syracuseStep 2169539 = 3254309) B3254309
theorem B2745829 : Blo 2169435 2745829 := bbase (se 4 (by rfl) ⟨257421, by rfl⟩ : syracuseStep 2745829 = 514843) (by norm_num)
theorem B3661105 : Blo 2169435 3661105 := bstep (se 2 (by rfl) ⟨1372914, by rfl⟩ : syracuseStep 3661105 = 2745829) B2745829
theorem B4881473 : Blo 2169435 4881473 := bstep (se 2 (by rfl) ⟨1830552, by rfl⟩ : syracuseStep 4881473 = 3661105) B3661105
theorem B3254315 : Blo 2169435 3254315 := bstep (se 1 (by rfl) ⟨2440736, by rfl⟩ : syracuseStep 3254315 = 4881473) B4881473
theorem B2169543 : Blo 2169435 2169543 := bstep (se 1 (by rfl) ⟨1627157, by rfl⟩ : syracuseStep 2169543 = 3254315) B3254315
theorem B2440741 : Blo 2169435 2440741 := bbase (se 4 (by rfl) ⟨228819, by rfl⟩ : syracuseStep 2440741 = 457639) (by norm_num)
theorem B3254321 : Blo 2169435 3254321 := bstep (se 2 (by rfl) ⟨1220370, by rfl⟩ : syracuseStep 3254321 = 2440741) B2440741
theorem B2169547 : Blo 2169435 2169547 := bstep (se 1 (by rfl) ⟨1627160, by rfl⟩ : syracuseStep 2169547 = 3254321) B3254321
theorem B5944421 : Blo 2169435 5944421 := bbase (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) (by norm_num)
theorem B3962947 : Blo 2169435 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B5283929 : Blo 2169435 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B3522619 : Blo 2169435 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B18787301 : Blo 2169435 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B12524867 : Blo 2169435 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B8349911 : Blo 2169435 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B5566607 : Blo 2169435 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B3711071 : Blo 2169435 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B2474047 : Blo 2169435 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B3298729 : Blo 2169435 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B4398305 : Blo 2169435 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B11728813 : Blo 2169435 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B15638417 : Blo 2169435 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B10425611 : Blo 2169435 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B6950407 : Blo 2169435 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B9267209 : Blo 2169435 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B6178139 : Blo 2169435 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B4118759 : Blo 2169435 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B2745839 : Blo 2169435 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B7322237 : Blo 2169435 7322237 := bstep (se 3 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 7322237 = 2745839) B2745839
theorem B4881491 : Blo 2169435 4881491 := bstep (se 1 (by rfl) ⟨3661118, by rfl⟩ : syracuseStep 4881491 = 7322237) B7322237
theorem B3254327 : Blo 2169435 3254327 := bstep (se 1 (by rfl) ⟨2440745, by rfl⟩ : syracuseStep 3254327 = 4881491) B4881491
theorem B2169551 : Blo 2169435 2169551 := bstep (se 1 (by rfl) ⟨1627163, by rfl⟩ : syracuseStep 2169551 = 3254327) B3254327
theorem B3254333 : Blo 2169435 3254333 := bbase (se 3 (by rfl) ⟨610187, by rfl⟩ : syracuseStep 3254333 = 1220375) (by norm_num)
theorem B2169555 : Blo 2169435 2169555 := bstep (se 1 (by rfl) ⟨1627166, by rfl⟩ : syracuseStep 2169555 = 3254333) B3254333
theorem B4881509 : Blo 2169435 4881509 := bbase (se 4 (by rfl) ⟨457641, by rfl⟩ : syracuseStep 4881509 = 915283) (by norm_num)
theorem B3254339 : Blo 2169435 3254339 := bstep (se 1 (by rfl) ⟨2440754, by rfl⟩ : syracuseStep 3254339 = 4881509) B4881509
theorem B2169559 : Blo 2169435 2169559 := bstep (se 1 (by rfl) ⟨1627169, by rfl⟩ : syracuseStep 2169559 = 3254339) B3254339
theorem B5491709 : Blo 2169435 5491709 := bbase (se 3 (by rfl) ⟨1029695, by rfl⟩ : syracuseStep 5491709 = 2059391) (by norm_num)
theorem B3661139 : Blo 2169435 3661139 := bstep (se 1 (by rfl) ⟨2745854, by rfl⟩ : syracuseStep 3661139 = 5491709) B5491709
theorem B2440759 : Blo 2169435 2440759 := bstep (se 1 (by rfl) ⟨1830569, by rfl⟩ : syracuseStep 2440759 = 3661139) B3661139
theorem B3254345 : Blo 2169435 3254345 := bstep (se 2 (by rfl) ⟨1220379, by rfl⟩ : syracuseStep 3254345 = 2440759) B2440759
theorem B2169563 : Blo 2169435 2169563 := bstep (se 1 (by rfl) ⟨1627172, by rfl⟩ : syracuseStep 2169563 = 3254345) B3254345
theorem B4118789 : Blo 2169435 4118789 := bbase (se 4 (by rfl) ⟨386136, by rfl⟩ : syracuseStep 4118789 = 772273) (by norm_num)
theorem B10983437 : Blo 2169435 10983437 := bstep (se 3 (by rfl) ⟨2059394, by rfl⟩ : syracuseStep 10983437 = 4118789) B4118789
theorem B7322291 : Blo 2169435 7322291 := bstep (se 1 (by rfl) ⟨5491718, by rfl⟩ : syracuseStep 7322291 = 10983437) B10983437
theorem B4881527 : Blo 2169435 4881527 := bstep (se 1 (by rfl) ⟨3661145, by rfl⟩ : syracuseStep 4881527 = 7322291) B7322291
theorem B3254351 : Blo 2169435 3254351 := bstep (se 1 (by rfl) ⟨2440763, by rfl⟩ : syracuseStep 3254351 = 4881527) B4881527
theorem B2169567 : Blo 2169435 2169567 := bstep (se 1 (by rfl) ⟨1627175, by rfl⟩ : syracuseStep 2169567 = 3254351) B3254351
theorem B3254357 : Blo 2169435 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B2169571 : Blo 2169435 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B4760957 : Blo 2169435 4760957 := bbase (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) (by norm_num)
theorem B3173971 : Blo 2169435 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B4231961 : Blo 2169435 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B2821307 : Blo 2169435 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B7523485 : Blo 2169435 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B160501013 : Blo 2169435 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B107000675 : Blo 2169435 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B71333783 : Blo 2169435 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B47555855 : Blo 2169435 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B31703903 : Blo 2169435 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B21135935 : Blo 2169435 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B56362493 : Blo 2169435 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B150299981 : Blo 2169435 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B100199987 : Blo 2169435 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B66799991 : Blo 2169435 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B44533327 : Blo 2169435 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B59377769 : Blo 2169435 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B39585179 : Blo 2169435 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B26390119 : Blo 2169435 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B35186825 : Blo 2169435 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B23457883 : Blo 2169435 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B31277177 : Blo 2169435 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B20851451 : Blo 2169435 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B13900967 : Blo 2169435 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B9267311 : Blo 2169435 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B6178207 : Blo 2169435 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B8237609 : Blo 2169435 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B5491739 : Blo 2169435 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B3661159 : Blo 2169435 3661159 := bstep (se 1 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 3661159 = 5491739) B5491739
theorem B4881545 : Blo 2169435 4881545 := bstep (se 2 (by rfl) ⟨1830579, by rfl⟩ : syracuseStep 4881545 = 3661159) B3661159
theorem B3254363 : Blo 2169435 3254363 := bstep (se 1 (by rfl) ⟨2440772, by rfl⟩ : syracuseStep 3254363 = 4881545) B4881545
theorem B2169575 : Blo 2169435 2169575 := bstep (se 1 (by rfl) ⟨1627181, by rfl⟩ : syracuseStep 2169575 = 3254363) B3254363
theorem B2440777 : Blo 2169435 2440777 := bbase (se 2 (by rfl) ⟨915291, by rfl⟩ : syracuseStep 2440777 = 1830583) (by norm_num)
theorem B3254369 : Blo 2169435 3254369 := bstep (se 2 (by rfl) ⟨1220388, by rfl⟩ : syracuseStep 3254369 = 2440777) B2440777
theorem B2169579 : Blo 2169435 2169579 := bstep (se 1 (by rfl) ⟨1627184, by rfl⟩ : syracuseStep 2169579 = 3254369) B3254369
theorem B15638645 : Blo 2169435 15638645 := bbase (se 5 (by rfl) ⟨733061, by rfl⟩ : syracuseStep 15638645 = 1466123) (by norm_num)
theorem B10425763 : Blo 2169435 10425763 := bstep (se 1 (by rfl) ⟨7819322, by rfl⟩ : syracuseStep 10425763 = 15638645) B15638645
theorem B13901017 : Blo 2169435 13901017 := bstep (se 2 (by rfl) ⟨5212881, by rfl⟩ : syracuseStep 13901017 = 10425763) B10425763
theorem B18534689 : Blo 2169435 18534689 := bstep (se 2 (by rfl) ⟨6950508, by rfl⟩ : syracuseStep 18534689 = 13901017) B13901017
theorem B12356459 : Blo 2169435 12356459 := bstep (se 1 (by rfl) ⟨9267344, by rfl⟩ : syracuseStep 12356459 = 18534689) B18534689
theorem B8237639 : Blo 2169435 8237639 := bstep (se 1 (by rfl) ⟨6178229, by rfl⟩ : syracuseStep 8237639 = 12356459) B12356459
theorem B5491759 : Blo 2169435 5491759 := bstep (se 1 (by rfl) ⟨4118819, by rfl⟩ : syracuseStep 5491759 = 8237639) B8237639
theorem B7322345 : Blo 2169435 7322345 := bstep (se 2 (by rfl) ⟨2745879, by rfl⟩ : syracuseStep 7322345 = 5491759) B5491759
theorem B4881563 : Blo 2169435 4881563 := bstep (se 1 (by rfl) ⟨3661172, by rfl⟩ : syracuseStep 4881563 = 7322345) B7322345
theorem B3254375 : Blo 2169435 3254375 := bstep (se 1 (by rfl) ⟨2440781, by rfl⟩ : syracuseStep 3254375 = 4881563) B4881563
theorem B2169583 : Blo 2169435 2169583 := bstep (se 1 (by rfl) ⟨1627187, by rfl⟩ : syracuseStep 2169583 = 3254375) B3254375
theorem B3254381 : Blo 2169435 3254381 := bbase (se 3 (by rfl) ⟨610196, by rfl⟩ : syracuseStep 3254381 = 1220393) (by norm_num)
theorem B2169587 : Blo 2169435 2169587 := bstep (se 1 (by rfl) ⟨1627190, by rfl⟩ : syracuseStep 2169587 = 3254381) B3254381
theorem B4881581 : Blo 2169435 4881581 := bbase (se 3 (by rfl) ⟨915296, by rfl⟩ : syracuseStep 4881581 = 1830593) (by norm_num)
theorem B3254387 : Blo 2169435 3254387 := bstep (se 1 (by rfl) ⟨2440790, by rfl⟩ : syracuseStep 3254387 = 4881581) B4881581
theorem B2169591 : Blo 2169435 2169591 := bstep (se 1 (by rfl) ⟨1627193, by rfl⟩ : syracuseStep 2169591 = 3254387) B3254387
theorem B6950549 : Blo 2169435 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B4633699 : Blo 2169435 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B6178265 : Blo 2169435 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B4118843 : Blo 2169435 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B2745895 : Blo 2169435 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B3661193 : Blo 2169435 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B2440795 : Blo 2169435 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B3254393 : Blo 2169435 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B2169595 : Blo 2169435 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B4175045 : Blo 2169435 4175045 := bbase (se 4 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 4175045 = 782821) (by norm_num)
theorem B44533813 : Blo 2169435 44533813 := bstep (se 5 (by rfl) ⟨2087522, by rfl⟩ : syracuseStep 44533813 = 4175045) B4175045
theorem B59378417 : Blo 2169435 59378417 := bstep (se 2 (by rfl) ⟨22266906, by rfl⟩ : syracuseStep 59378417 = 44533813) B44533813
theorem B39585611 : Blo 2169435 39585611 := bstep (se 1 (by rfl) ⟨29689208, by rfl⟩ : syracuseStep 39585611 = 59378417) B59378417
theorem B26390407 : Blo 2169435 26390407 := bstep (se 1 (by rfl) ⟨19792805, by rfl⟩ : syracuseStep 26390407 = 39585611) B39585611
theorem B35187209 : Blo 2169435 35187209 := bstep (se 2 (by rfl) ⟨13195203, by rfl⟩ : syracuseStep 35187209 = 26390407) B26390407
theorem B23458139 : Blo 2169435 23458139 := bstep (se 1 (by rfl) ⟨17593604, by rfl⟩ : syracuseStep 23458139 = 35187209) B35187209
theorem B15638759 : Blo 2169435 15638759 := bstep (se 1 (by rfl) ⟨11729069, by rfl⟩ : syracuseStep 15638759 = 23458139) B23458139
theorem B10425839 : Blo 2169435 10425839 := bstep (se 1 (by rfl) ⟨7819379, by rfl⟩ : syracuseStep 10425839 = 15638759) B15638759
theorem B27802237 : Blo 2169435 27802237 := bstep (se 3 (by rfl) ⟨5212919, by rfl⟩ : syracuseStep 27802237 = 10425839) B10425839
theorem B37069649 : Blo 2169435 37069649 := bstep (se 2 (by rfl) ⟨13901118, by rfl⟩ : syracuseStep 37069649 = 27802237) B27802237
theorem B24713099 : Blo 2169435 24713099 := bstep (se 1 (by rfl) ⟨18534824, by rfl⟩ : syracuseStep 24713099 = 37069649) B37069649
theorem B16475399 : Blo 2169435 16475399 := bstep (se 1 (by rfl) ⟨12356549, by rfl⟩ : syracuseStep 16475399 = 24713099) B24713099
theorem B10983599 : Blo 2169435 10983599 := bstep (se 1 (by rfl) ⟨8237699, by rfl⟩ : syracuseStep 10983599 = 16475399) B16475399
theorem B7322399 : Blo 2169435 7322399 := bstep (se 1 (by rfl) ⟨5491799, by rfl⟩ : syracuseStep 7322399 = 10983599) B10983599
theorem B4881599 : Blo 2169435 4881599 := bstep (se 1 (by rfl) ⟨3661199, by rfl⟩ : syracuseStep 4881599 = 7322399) B7322399
theorem B3254399 : Blo 2169435 3254399 := bstep (se 1 (by rfl) ⟨2440799, by rfl⟩ : syracuseStep 3254399 = 4881599) B4881599
theorem B2169599 : Blo 2169435 2169599 := bstep (se 1 (by rfl) ⟨1627199, by rfl⟩ : syracuseStep 2169599 = 3254399) B3254399
theorem B3254405 : Blo 2169435 3254405 := bbase (se 4 (by rfl) ⟨305100, by rfl⟩ : syracuseStep 3254405 = 610201) (by norm_num)
theorem B2169603 : Blo 2169435 2169603 := bstep (se 1 (by rfl) ⟨1627202, by rfl⟩ : syracuseStep 2169603 = 3254405) B3254405
theorem B3661213 : Blo 2169435 3661213 := bbase (se 3 (by rfl) ⟨686477, by rfl⟩ : syracuseStep 3661213 = 1372955) (by norm_num)
theorem B4881617 : Blo 2169435 4881617 := bstep (se 2 (by rfl) ⟨1830606, by rfl⟩ : syracuseStep 4881617 = 3661213) B3661213
theorem B3254411 : Blo 2169435 3254411 := bstep (se 1 (by rfl) ⟨2440808, by rfl⟩ : syracuseStep 3254411 = 4881617) B4881617
theorem B2169607 : Blo 2169435 2169607 := bstep (se 1 (by rfl) ⟨1627205, by rfl⟩ : syracuseStep 2169607 = 3254411) B3254411
theorem B2440813 : Blo 2169435 2440813 := bbase (se 3 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 2440813 = 915305) (by norm_num)
theorem B3254417 : Blo 2169435 3254417 := bstep (se 2 (by rfl) ⟨1220406, by rfl⟩ : syracuseStep 3254417 = 2440813) B2440813
theorem B2169611 : Blo 2169435 2169611 := bstep (se 1 (by rfl) ⟨1627208, by rfl⟩ : syracuseStep 2169611 = 3254417) B3254417
theorem B7322453 : Blo 2169435 7322453 := bbase (se 9 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 7322453 = 42905) (by norm_num)
theorem B4881635 : Blo 2169435 4881635 := bstep (se 1 (by rfl) ⟨3661226, by rfl⟩ : syracuseStep 4881635 = 7322453) B7322453
theorem B3254423 : Blo 2169435 3254423 := bstep (se 1 (by rfl) ⟨2440817, by rfl⟩ : syracuseStep 3254423 = 4881635) B4881635
theorem B2169615 : Blo 2169435 2169615 := bstep (se 1 (by rfl) ⟨1627211, by rfl⟩ : syracuseStep 2169615 = 3254423) B3254423
theorem B3254429 : Blo 2169435 3254429 := bbase (se 3 (by rfl) ⟨610205, by rfl⟩ : syracuseStep 3254429 = 1220411) (by norm_num)
theorem B2169619 : Blo 2169435 2169619 := bstep (se 1 (by rfl) ⟨1627214, by rfl⟩ : syracuseStep 2169619 = 3254429) B3254429
theorem B4881653 : Blo 2169435 4881653 := bbase (se 5 (by rfl) ⟨228827, by rfl⟩ : syracuseStep 4881653 = 457655) (by norm_num)
theorem B3254435 : Blo 2169435 3254435 := bstep (se 1 (by rfl) ⟨2440826, by rfl⟩ : syracuseStep 3254435 = 4881653) B4881653
theorem B2169623 : Blo 2169435 2169623 := bstep (se 1 (by rfl) ⟨1627217, by rfl⟩ : syracuseStep 2169623 = 3254435) B3254435
theorem B2542105 : Blo 2169435 2542105 := bbase (se 2 (by rfl) ⟨953289, by rfl⟩ : syracuseStep 2542105 = 1906579) (by norm_num)
theorem B3389473 : Blo 2169435 3389473 := bstep (se 2 (by rfl) ⟨1271052, by rfl⟩ : syracuseStep 3389473 = 2542105) B2542105
theorem B4519297 : Blo 2169435 4519297 := bstep (se 2 (by rfl) ⟨1694736, by rfl⟩ : syracuseStep 4519297 = 3389473) B3389473
theorem B24102917 : Blo 2169435 24102917 := bstep (se 4 (by rfl) ⟨2259648, by rfl⟩ : syracuseStep 24102917 = 4519297) B4519297
theorem B16068611 : Blo 2169435 16068611 := bstep (se 1 (by rfl) ⟨12051458, by rfl⟩ : syracuseStep 16068611 = 24102917) B24102917
theorem B10712407 : Blo 2169435 10712407 := bstep (se 1 (by rfl) ⟨8034305, by rfl⟩ : syracuseStep 10712407 = 16068611) B16068611
theorem B14283209 : Blo 2169435 14283209 := bstep (se 2 (by rfl) ⟨5356203, by rfl⟩ : syracuseStep 14283209 = 10712407) B10712407
theorem B9522139 : Blo 2169435 9522139 := bstep (se 1 (by rfl) ⟨7141604, by rfl⟩ : syracuseStep 9522139 = 14283209) B14283209
theorem B12696185 : Blo 2169435 12696185 := bstep (se 2 (by rfl) ⟨4761069, by rfl⟩ : syracuseStep 12696185 = 9522139) B9522139
theorem B8464123 : Blo 2169435 8464123 := bstep (se 1 (by rfl) ⟨6348092, by rfl⟩ : syracuseStep 8464123 = 12696185) B12696185
theorem B45141989 : Blo 2169435 45141989 := bstep (se 4 (by rfl) ⟨4232061, by rfl⟩ : syracuseStep 45141989 = 8464123) B8464123
theorem B120378637 : Blo 2169435 120378637 := bstep (se 3 (by rfl) ⟨22570994, by rfl⟩ : syracuseStep 120378637 = 45141989) B45141989
theorem B160504849 : Blo 2169435 160504849 := bstep (se 2 (by rfl) ⟨60189318, by rfl⟩ : syracuseStep 160504849 = 120378637) B120378637
theorem B214006465 : Blo 2169435 214006465 := bstep (se 2 (by rfl) ⟨80252424, by rfl⟩ : syracuseStep 214006465 = 160504849) B160504849
theorem B285341953 : Blo 2169435 285341953 := bstep (se 2 (by rfl) ⟨107003232, by rfl⟩ : syracuseStep 285341953 = 214006465) B214006465
theorem B380455937 : Blo 2169435 380455937 := bstep (se 2 (by rfl) ⟨142670976, by rfl⟩ : syracuseStep 380455937 = 285341953) B285341953
theorem B253637291 : Blo 2169435 253637291 := bstep (se 1 (by rfl) ⟨190227968, by rfl⟩ : syracuseStep 253637291 = 380455937) B380455937
theorem B676366109 : Blo 2169435 676366109 := bstep (se 3 (by rfl) ⟨126818645, by rfl⟩ : syracuseStep 676366109 = 253637291) B253637291
theorem B450910739 : Blo 2169435 450910739 := bstep (se 1 (by rfl) ⟨338183054, by rfl⟩ : syracuseStep 450910739 = 676366109) B676366109
theorem B300607159 : Blo 2169435 300607159 := bstep (se 1 (by rfl) ⟨225455369, by rfl⟩ : syracuseStep 300607159 = 450910739) B450910739
theorem B400809545 : Blo 2169435 400809545 := bstep (se 2 (by rfl) ⟨150303579, by rfl⟩ : syracuseStep 400809545 = 300607159) B300607159
theorem B267206363 : Blo 2169435 267206363 := bstep (se 1 (by rfl) ⟨200404772, by rfl⟩ : syracuseStep 267206363 = 400809545) B400809545
theorem B178137575 : Blo 2169435 178137575 := bstep (se 1 (by rfl) ⟨133603181, by rfl⟩ : syracuseStep 178137575 = 267206363) B267206363
theorem B118758383 : Blo 2169435 118758383 := bstep (se 1 (by rfl) ⟨89068787, by rfl⟩ : syracuseStep 118758383 = 178137575) B178137575
theorem B79172255 : Blo 2169435 79172255 := bstep (se 1 (by rfl) ⟨59379191, by rfl⟩ : syracuseStep 79172255 = 118758383) B118758383
theorem B52781503 : Blo 2169435 52781503 := bstep (se 1 (by rfl) ⟨39586127, by rfl⟩ : syracuseStep 52781503 = 79172255) B79172255
theorem B70375337 : Blo 2169435 70375337 := bstep (se 2 (by rfl) ⟨26390751, by rfl⟩ : syracuseStep 70375337 = 52781503) B52781503
theorem B46916891 : Blo 2169435 46916891 := bstep (se 1 (by rfl) ⟨35187668, by rfl⟩ : syracuseStep 46916891 = 70375337) B70375337
theorem B31277927 : Blo 2169435 31277927 := bstep (se 1 (by rfl) ⟨23458445, by rfl⟩ : syracuseStep 31277927 = 46916891) B46916891
theorem B20851951 : Blo 2169435 20851951 := bstep (se 1 (by rfl) ⟨15638963, by rfl⟩ : syracuseStep 20851951 = 31277927) B31277927
theorem B27802601 : Blo 2169435 27802601 := bstep (se 2 (by rfl) ⟨10425975, by rfl⟩ : syracuseStep 27802601 = 20851951) B20851951
theorem B18535067 : Blo 2169435 18535067 := bstep (se 1 (by rfl) ⟨13901300, by rfl⟩ : syracuseStep 18535067 = 27802601) B27802601
theorem B12356711 : Blo 2169435 12356711 := bstep (se 1 (by rfl) ⟨9267533, by rfl⟩ : syracuseStep 12356711 = 18535067) B18535067
theorem B8237807 : Blo 2169435 8237807 := bstep (se 1 (by rfl) ⟨6178355, by rfl⟩ : syracuseStep 8237807 = 12356711) B12356711
theorem B5491871 : Blo 2169435 5491871 := bstep (se 1 (by rfl) ⟨4118903, by rfl⟩ : syracuseStep 5491871 = 8237807) B8237807
theorem B3661247 : Blo 2169435 3661247 := bstep (se 1 (by rfl) ⟨2745935, by rfl⟩ : syracuseStep 3661247 = 5491871) B5491871
theorem B2440831 : Blo 2169435 2440831 := bstep (se 1 (by rfl) ⟨1830623, by rfl⟩ : syracuseStep 2440831 = 3661247) B3661247
theorem B3254441 : Blo 2169435 3254441 := bstep (se 2 (by rfl) ⟨1220415, by rfl⟩ : syracuseStep 3254441 = 2440831) B2440831
theorem B2169627 : Blo 2169435 2169627 := bstep (se 1 (by rfl) ⟨1627220, by rfl⟩ : syracuseStep 2169627 = 3254441) B3254441
theorem B6597701 : Blo 2169435 6597701 := bbase (se 4 (by rfl) ⟨618534, by rfl⟩ : syracuseStep 6597701 = 1237069) (by norm_num)
theorem B4398467 : Blo 2169435 4398467 := bstep (se 1 (by rfl) ⟨3298850, by rfl⟩ : syracuseStep 4398467 = 6597701) B6597701
theorem B11729245 : Blo 2169435 11729245 := bstep (se 3 (by rfl) ⟨2199233, by rfl⟩ : syracuseStep 11729245 = 4398467) B4398467
theorem B15638993 : Blo 2169435 15638993 := bstep (se 2 (by rfl) ⟨5864622, by rfl⟩ : syracuseStep 15638993 = 11729245) B11729245
theorem B10425995 : Blo 2169435 10425995 := bstep (se 1 (by rfl) ⟨7819496, by rfl⟩ : syracuseStep 10425995 = 15638993) B15638993
theorem B6950663 : Blo 2169435 6950663 := bstep (se 1 (by rfl) ⟨5212997, by rfl⟩ : syracuseStep 6950663 = 10425995) B10425995
theorem B4633775 : Blo 2169435 4633775 := bstep (se 1 (by rfl) ⟨3475331, by rfl⟩ : syracuseStep 4633775 = 6950663) B6950663
theorem B3089183 : Blo 2169435 3089183 := bstep (se 1 (by rfl) ⟨2316887, by rfl⟩ : syracuseStep 3089183 = 4633775) B4633775
theorem B8237821 : Blo 2169435 8237821 := bstep (se 3 (by rfl) ⟨1544591, by rfl⟩ : syracuseStep 8237821 = 3089183) B3089183
theorem B10983761 : Blo 2169435 10983761 := bstep (se 2 (by rfl) ⟨4118910, by rfl⟩ : syracuseStep 10983761 = 8237821) B8237821
theorem B7322507 : Blo 2169435 7322507 := bstep (se 1 (by rfl) ⟨5491880, by rfl⟩ : syracuseStep 7322507 = 10983761) B10983761
theorem B4881671 : Blo 2169435 4881671 := bstep (se 1 (by rfl) ⟨3661253, by rfl⟩ : syracuseStep 4881671 = 7322507) B7322507
theorem B3254447 : Blo 2169435 3254447 := bstep (se 1 (by rfl) ⟨2440835, by rfl⟩ : syracuseStep 3254447 = 4881671) B4881671
theorem B2169631 : Blo 2169435 2169631 := bstep (se 1 (by rfl) ⟨1627223, by rfl⟩ : syracuseStep 2169631 = 3254447) B3254447
theorem B3254453 : Blo 2169435 3254453 := bbase (se 5 (by rfl) ⟨152552, by rfl⟩ : syracuseStep 3254453 = 305105) (by norm_num)
theorem B2169635 : Blo 2169435 2169635 := bstep (se 1 (by rfl) ⟨1627226, by rfl⟩ : syracuseStep 2169635 = 3254453) B3254453
theorem B5491901 : Blo 2169435 5491901 := bbase (se 3 (by rfl) ⟨1029731, by rfl⟩ : syracuseStep 5491901 = 2059463) (by norm_num)
theorem B3661267 : Blo 2169435 3661267 := bstep (se 1 (by rfl) ⟨2745950, by rfl⟩ : syracuseStep 3661267 = 5491901) B5491901
theorem B4881689 : Blo 2169435 4881689 := bstep (se 2 (by rfl) ⟨1830633, by rfl⟩ : syracuseStep 4881689 = 3661267) B3661267
theorem B3254459 : Blo 2169435 3254459 := bstep (se 1 (by rfl) ⟨2440844, by rfl⟩ : syracuseStep 3254459 = 4881689) B4881689
theorem B2169639 : Blo 2169435 2169639 := bstep (se 1 (by rfl) ⟨1627229, by rfl⟩ : syracuseStep 2169639 = 3254459) B3254459
theorem B2440849 : Blo 2169435 2440849 := bbase (se 2 (by rfl) ⟨915318, by rfl⟩ : syracuseStep 2440849 = 1830637) (by norm_num)
theorem B3254465 : Blo 2169435 3254465 := bstep (se 2 (by rfl) ⟨1220424, by rfl⟩ : syracuseStep 3254465 = 2440849) B2440849
theorem B2169643 : Blo 2169435 2169643 := bstep (se 1 (by rfl) ⟨1627232, by rfl⟩ : syracuseStep 2169643 = 3254465) B3254465
theorem B4118941 : Blo 2169435 4118941 := bbase (se 3 (by rfl) ⟨772301, by rfl⟩ : syracuseStep 4118941 = 1544603) (by norm_num)
theorem B5491921 : Blo 2169435 5491921 := bstep (se 2 (by rfl) ⟨2059470, by rfl⟩ : syracuseStep 5491921 = 4118941) B4118941
theorem B7322561 : Blo 2169435 7322561 := bstep (se 2 (by rfl) ⟨2745960, by rfl⟩ : syracuseStep 7322561 = 5491921) B5491921
theorem B4881707 : Blo 2169435 4881707 := bstep (se 1 (by rfl) ⟨3661280, by rfl⟩ : syracuseStep 4881707 = 7322561) B7322561
theorem B3254471 : Blo 2169435 3254471 := bstep (se 1 (by rfl) ⟨2440853, by rfl⟩ : syracuseStep 3254471 = 4881707) B4881707
theorem B2169647 : Blo 2169435 2169647 := bstep (se 1 (by rfl) ⟨1627235, by rfl⟩ : syracuseStep 2169647 = 3254471) B3254471
theorem B3254477 : Blo 2169435 3254477 := bbase (se 3 (by rfl) ⟨610214, by rfl⟩ : syracuseStep 3254477 = 1220429) (by norm_num)
theorem B2169651 : Blo 2169435 2169651 := bstep (se 1 (by rfl) ⟨1627238, by rfl⟩ : syracuseStep 2169651 = 3254477) B3254477
theorem B4881725 : Blo 2169435 4881725 := bbase (se 3 (by rfl) ⟨915323, by rfl⟩ : syracuseStep 4881725 = 1830647) (by norm_num)
theorem B3254483 : Blo 2169435 3254483 := bstep (se 1 (by rfl) ⟨2440862, by rfl⟩ : syracuseStep 3254483 = 4881725) B4881725
theorem B2169655 : Blo 2169435 2169655 := bstep (se 1 (by rfl) ⟨1627241, by rfl⟩ : syracuseStep 2169655 = 3254483) B3254483
theorem B3661301 : Blo 2169435 3661301 := bbase (se 5 (by rfl) ⟨171623, by rfl⟩ : syracuseStep 3661301 = 343247) (by norm_num)
theorem B2440867 : Blo 2169435 2440867 := bstep (se 1 (by rfl) ⟨1830650, by rfl⟩ : syracuseStep 2440867 = 3661301) B3661301
theorem B3254489 : Blo 2169435 3254489 := bstep (se 2 (by rfl) ⟨1220433, by rfl⟩ : syracuseStep 3254489 = 2440867) B2440867
theorem B2169659 : Blo 2169435 2169659 := bstep (se 1 (by rfl) ⟨1627244, by rfl⟩ : syracuseStep 2169659 = 3254489) B3254489
theorem B2606537 : Blo 2169435 2606537 := bbase (se 2 (by rfl) ⟨977451, by rfl⟩ : syracuseStep 2606537 = 1954903) (by norm_num)
theorem B6950765 : Blo 2169435 6950765 := bstep (se 3 (by rfl) ⟨1303268, by rfl⟩ : syracuseStep 6950765 = 2606537) B2606537
theorem B4633843 : Blo 2169435 4633843 := bstep (se 1 (by rfl) ⟨3475382, by rfl⟩ : syracuseStep 4633843 = 6950765) B6950765
theorem B6178457 : Blo 2169435 6178457 := bstep (se 2 (by rfl) ⟨2316921, by rfl⟩ : syracuseStep 6178457 = 4633843) B4633843
theorem B16475885 : Blo 2169435 16475885 := bstep (se 3 (by rfl) ⟨3089228, by rfl⟩ : syracuseStep 16475885 = 6178457) B6178457
theorem B10983923 : Blo 2169435 10983923 := bstep (se 1 (by rfl) ⟨8237942, by rfl⟩ : syracuseStep 10983923 = 16475885) B16475885
theorem B7322615 : Blo 2169435 7322615 := bstep (se 1 (by rfl) ⟨5491961, by rfl⟩ : syracuseStep 7322615 = 10983923) B10983923
theorem B4881743 : Blo 2169435 4881743 := bstep (se 1 (by rfl) ⟨3661307, by rfl⟩ : syracuseStep 4881743 = 7322615) B7322615
theorem B3254495 : Blo 2169435 3254495 := bstep (se 1 (by rfl) ⟨2440871, by rfl⟩ : syracuseStep 3254495 = 4881743) B4881743
theorem B2169663 : Blo 2169435 2169663 := bstep (se 1 (by rfl) ⟨1627247, by rfl⟩ : syracuseStep 2169663 = 3254495) B3254495
theorem B3254501 : Blo 2169435 3254501 := bbase (se 4 (by rfl) ⟨305109, by rfl⟩ : syracuseStep 3254501 = 610219) (by norm_num)
theorem B2169667 : Blo 2169435 2169667 := bstep (se 1 (by rfl) ⟨1627250, by rfl⟩ : syracuseStep 2169667 = 3254501) B3254501
theorem B4633861 : Blo 2169435 4633861 := bbase (se 4 (by rfl) ⟨434424, by rfl⟩ : syracuseStep 4633861 = 868849) (by norm_num)
theorem B6178481 : Blo 2169435 6178481 := bstep (se 2 (by rfl) ⟨2316930, by rfl⟩ : syracuseStep 6178481 = 4633861) B4633861
theorem B4118987 : Blo 2169435 4118987 := bstep (se 1 (by rfl) ⟨3089240, by rfl⟩ : syracuseStep 4118987 = 6178481) B6178481
theorem B2745991 : Blo 2169435 2745991 := bstep (se 1 (by rfl) ⟨2059493, by rfl⟩ : syracuseStep 2745991 = 4118987) B4118987
theorem B3661321 : Blo 2169435 3661321 := bstep (se 2 (by rfl) ⟨1372995, by rfl⟩ : syracuseStep 3661321 = 2745991) B2745991
theorem B4881761 : Blo 2169435 4881761 := bstep (se 2 (by rfl) ⟨1830660, by rfl⟩ : syracuseStep 4881761 = 3661321) B3661321
theorem B3254507 : Blo 2169435 3254507 := bstep (se 1 (by rfl) ⟨2440880, by rfl⟩ : syracuseStep 3254507 = 4881761) B4881761
theorem B2169671 : Blo 2169435 2169671 := bstep (se 1 (by rfl) ⟨1627253, by rfl⟩ : syracuseStep 2169671 = 3254507) B3254507
theorem B2440885 : Blo 2169435 2440885 := bbase (se 5 (by rfl) ⟨114416, by rfl⟩ : syracuseStep 2440885 = 228833) (by norm_num)
theorem B3254513 : Blo 2169435 3254513 := bstep (se 2 (by rfl) ⟨1220442, by rfl⟩ : syracuseStep 3254513 = 2440885) B2440885
theorem B2169675 : Blo 2169435 2169675 := bstep (se 1 (by rfl) ⟨1627256, by rfl⟩ : syracuseStep 2169675 = 3254513) B3254513
theorem B2746001 : Blo 2169435 2746001 := bbase (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) (by norm_num)
theorem B7322669 : Blo 2169435 7322669 := bstep (se 3 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 7322669 = 2746001) B2746001
theorem B4881779 : Blo 2169435 4881779 := bstep (se 1 (by rfl) ⟨3661334, by rfl⟩ : syracuseStep 4881779 = 7322669) B7322669
theorem B3254519 : Blo 2169435 3254519 := bstep (se 1 (by rfl) ⟨2440889, by rfl⟩ : syracuseStep 3254519 = 4881779) B4881779
theorem B2169679 : Blo 2169435 2169679 := bstep (se 1 (by rfl) ⟨1627259, by rfl⟩ : syracuseStep 2169679 = 3254519) B3254519
theorem B3254525 : Blo 2169435 3254525 := bbase (se 3 (by rfl) ⟨610223, by rfl⟩ : syracuseStep 3254525 = 1220447) (by norm_num)
theorem B2169683 : Blo 2169435 2169683 := bstep (se 1 (by rfl) ⟨1627262, by rfl⟩ : syracuseStep 2169683 = 3254525) B3254525
theorem B4881797 : Blo 2169435 4881797 := bbase (se 4 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 4881797 = 915337) (by norm_num)
theorem B3254531 : Blo 2169435 3254531 := bstep (se 1 (by rfl) ⟨2440898, by rfl⟩ : syracuseStep 3254531 = 4881797) B4881797
theorem B2169687 : Blo 2169435 2169687 := bstep (se 1 (by rfl) ⟨1627265, by rfl⟩ : syracuseStep 2169687 = 3254531) B3254531
theorem B3089269 : Blo 2169435 3089269 := bbase (se 5 (by rfl) ⟨144809, by rfl⟩ : syracuseStep 3089269 = 289619) (by norm_num)
theorem B4119025 : Blo 2169435 4119025 := bstep (se 2 (by rfl) ⟨1544634, by rfl⟩ : syracuseStep 4119025 = 3089269) B3089269
theorem B5492033 : Blo 2169435 5492033 := bstep (se 2 (by rfl) ⟨2059512, by rfl⟩ : syracuseStep 5492033 = 4119025) B4119025
theorem B3661355 : Blo 2169435 3661355 := bstep (se 1 (by rfl) ⟨2746016, by rfl⟩ : syracuseStep 3661355 = 5492033) B5492033
theorem B2440903 : Blo 2169435 2440903 := bstep (se 1 (by rfl) ⟨1830677, by rfl⟩ : syracuseStep 2440903 = 3661355) B3661355
theorem B3254537 : Blo 2169435 3254537 := bstep (se 2 (by rfl) ⟨1220451, by rfl⟩ : syracuseStep 3254537 = 2440903) B2440903
theorem B2169691 : Blo 2169435 2169691 := bstep (se 1 (by rfl) ⟨1627268, by rfl⟩ : syracuseStep 2169691 = 3254537) B3254537
theorem B10984085 : Blo 2169435 10984085 := bbase (se 6 (by rfl) ⟨257439, by rfl⟩ : syracuseStep 10984085 = 514879) (by norm_num)
theorem B7322723 : Blo 2169435 7322723 := bstep (se 1 (by rfl) ⟨5492042, by rfl⟩ : syracuseStep 7322723 = 10984085) B10984085
theorem B4881815 : Blo 2169435 4881815 := bstep (se 1 (by rfl) ⟨3661361, by rfl⟩ : syracuseStep 4881815 = 7322723) B7322723
theorem B3254543 : Blo 2169435 3254543 := bstep (se 1 (by rfl) ⟨2440907, by rfl⟩ : syracuseStep 3254543 = 4881815) B4881815
theorem B2169695 : Blo 2169435 2169695 := bstep (se 1 (by rfl) ⟨1627271, by rfl⟩ : syracuseStep 2169695 = 3254543) B3254543
theorem B3254549 : Blo 2169435 3254549 := bbase (se 6 (by rfl) ⟨76278, by rfl⟩ : syracuseStep 3254549 = 152557) (by norm_num)
theorem B2169699 : Blo 2169435 2169699 := bstep (se 1 (by rfl) ⟨1627274, by rfl⟩ : syracuseStep 2169699 = 3254549) B3254549
theorem B2606585 : Blo 2169435 2606585 := bbase (se 2 (by rfl) ⟨977469, by rfl⟩ : syracuseStep 2606585 = 1954939) (by norm_num)
theorem B27803573 : Blo 2169435 27803573 := bstep (se 5 (by rfl) ⟨1303292, by rfl⟩ : syracuseStep 27803573 = 2606585) B2606585
theorem B18535715 : Blo 2169435 18535715 := bstep (se 1 (by rfl) ⟨13901786, by rfl⟩ : syracuseStep 18535715 = 27803573) B27803573
theorem B12357143 : Blo 2169435 12357143 := bstep (se 1 (by rfl) ⟨9267857, by rfl⟩ : syracuseStep 12357143 = 18535715) B18535715
theorem B8238095 : Blo 2169435 8238095 := bstep (se 1 (by rfl) ⟨6178571, by rfl⟩ : syracuseStep 8238095 = 12357143) B12357143
theorem B5492063 : Blo 2169435 5492063 := bstep (se 1 (by rfl) ⟨4119047, by rfl⟩ : syracuseStep 5492063 = 8238095) B8238095
theorem B3661375 : Blo 2169435 3661375 := bstep (se 1 (by rfl) ⟨2746031, by rfl⟩ : syracuseStep 3661375 = 5492063) B5492063
theorem B4881833 : Blo 2169435 4881833 := bstep (se 2 (by rfl) ⟨1830687, by rfl⟩ : syracuseStep 4881833 = 3661375) B3661375
theorem B3254555 : Blo 2169435 3254555 := bstep (se 1 (by rfl) ⟨2440916, by rfl⟩ : syracuseStep 3254555 = 4881833) B4881833
theorem B2169703 : Blo 2169435 2169703 := bstep (se 1 (by rfl) ⟨1627277, by rfl⟩ : syracuseStep 2169703 = 3254555) B3254555
theorem B2440921 : Blo 2169435 2440921 := bbase (se 2 (by rfl) ⟨915345, by rfl⟩ : syracuseStep 2440921 = 1830691) (by norm_num)
theorem B3254561 : Blo 2169435 3254561 := bstep (se 2 (by rfl) ⟨1220460, by rfl⟩ : syracuseStep 3254561 = 2440921) B2440921
theorem B2169707 : Blo 2169435 2169707 := bstep (se 1 (by rfl) ⟨1627280, by rfl⟩ : syracuseStep 2169707 = 3254561) B3254561
theorem B2316973 : Blo 2169435 2316973 := bbase (se 3 (by rfl) ⟨434432, by rfl⟩ : syracuseStep 2316973 = 868865) (by norm_num)
theorem B3089297 : Blo 2169435 3089297 := bstep (se 2 (by rfl) ⟨1158486, by rfl⟩ : syracuseStep 3089297 = 2316973) B2316973
theorem B8238125 : Blo 2169435 8238125 := bstep (se 3 (by rfl) ⟨1544648, by rfl⟩ : syracuseStep 8238125 = 3089297) B3089297
theorem B5492083 : Blo 2169435 5492083 := bstep (se 1 (by rfl) ⟨4119062, by rfl⟩ : syracuseStep 5492083 = 8238125) B8238125
theorem B7322777 : Blo 2169435 7322777 := bstep (se 2 (by rfl) ⟨2746041, by rfl⟩ : syracuseStep 7322777 = 5492083) B5492083
theorem B4881851 : Blo 2169435 4881851 := bstep (se 1 (by rfl) ⟨3661388, by rfl⟩ : syracuseStep 4881851 = 7322777) B7322777
theorem B3254567 : Blo 2169435 3254567 := bstep (se 1 (by rfl) ⟨2440925, by rfl⟩ : syracuseStep 3254567 = 4881851) B4881851
theorem B2169711 : Blo 2169435 2169711 := bstep (se 1 (by rfl) ⟨1627283, by rfl⟩ : syracuseStep 2169711 = 3254567) B3254567
theorem B3254573 : Blo 2169435 3254573 := bbase (se 3 (by rfl) ⟨610232, by rfl⟩ : syracuseStep 3254573 = 1220465) (by norm_num)
theorem B2169715 : Blo 2169435 2169715 := bstep (se 1 (by rfl) ⟨1627286, by rfl⟩ : syracuseStep 2169715 = 3254573) B3254573
theorem B4881869 : Blo 2169435 4881869 := bbase (se 3 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 4881869 = 1830701) (by norm_num)
theorem B3254579 : Blo 2169435 3254579 := bstep (se 1 (by rfl) ⟨2440934, by rfl⟩ : syracuseStep 3254579 = 4881869) B4881869
theorem B2169719 : Blo 2169435 2169719 := bstep (se 1 (by rfl) ⟨1627289, by rfl⟩ : syracuseStep 2169719 = 3254579) B3254579
theorem B2746057 : Blo 2169435 2746057 := bbase (se 2 (by rfl) ⟨1029771, by rfl⟩ : syracuseStep 2746057 = 2059543) (by norm_num)
theorem B3661409 : Blo 2169435 3661409 := bstep (se 2 (by rfl) ⟨1373028, by rfl⟩ : syracuseStep 3661409 = 2746057) B2746057
theorem B2440939 : Blo 2169435 2440939 := bstep (se 1 (by rfl) ⟨1830704, by rfl⟩ : syracuseStep 2440939 = 3661409) B3661409
theorem B3254585 : Blo 2169435 3254585 := bstep (se 2 (by rfl) ⟨1220469, by rfl⟩ : syracuseStep 3254585 = 2440939) B2440939
theorem B2169723 : Blo 2169435 2169723 := bstep (se 1 (by rfl) ⟨1627292, by rfl⟩ : syracuseStep 2169723 = 3254585) B3254585
theorem B4398661 : Blo 2169435 4398661 := bbase (se 4 (by rfl) ⟨412374, by rfl⟩ : syracuseStep 4398661 = 824749) (by norm_num)
theorem B5864881 : Blo 2169435 5864881 := bstep (se 2 (by rfl) ⟨2199330, by rfl⟩ : syracuseStep 5864881 = 4398661) B4398661
theorem B7819841 : Blo 2169435 7819841 := bstep (se 2 (by rfl) ⟨2932440, by rfl⟩ : syracuseStep 7819841 = 5864881) B5864881
theorem B20852909 : Blo 2169435 20852909 := bstep (se 3 (by rfl) ⟨3909920, by rfl⟩ : syracuseStep 20852909 = 7819841) B7819841
theorem B13901939 : Blo 2169435 13901939 := bstep (se 1 (by rfl) ⟨10426454, by rfl⟩ : syracuseStep 13901939 = 20852909) B20852909
theorem B9267959 : Blo 2169435 9267959 := bstep (se 1 (by rfl) ⟨6950969, by rfl⟩ : syracuseStep 9267959 = 13901939) B13901939
theorem B24714557 : Blo 2169435 24714557 := bstep (se 3 (by rfl) ⟨4633979, by rfl⟩ : syracuseStep 24714557 = 9267959) B9267959
theorem B16476371 : Blo 2169435 16476371 := bstep (se 1 (by rfl) ⟨12357278, by rfl⟩ : syracuseStep 16476371 = 24714557) B24714557
theorem B10984247 : Blo 2169435 10984247 := bstep (se 1 (by rfl) ⟨8238185, by rfl⟩ : syracuseStep 10984247 = 16476371) B16476371
theorem B7322831 : Blo 2169435 7322831 := bstep (se 1 (by rfl) ⟨5492123, by rfl⟩ : syracuseStep 7322831 = 10984247) B10984247
theorem B4881887 : Blo 2169435 4881887 := bstep (se 1 (by rfl) ⟨3661415, by rfl⟩ : syracuseStep 4881887 = 7322831) B7322831
theorem B3254591 : Blo 2169435 3254591 := bstep (se 1 (by rfl) ⟨2440943, by rfl⟩ : syracuseStep 3254591 = 4881887) B4881887
theorem B2169727 : Blo 2169435 2169727 := bstep (se 1 (by rfl) ⟨1627295, by rfl⟩ : syracuseStep 2169727 = 3254591) B3254591
theorem B3254597 : Blo 2169435 3254597 := bbase (se 4 (by rfl) ⟨305118, by rfl⟩ : syracuseStep 3254597 = 610237) (by norm_num)
theorem B2169731 : Blo 2169435 2169731 := bstep (se 1 (by rfl) ⟨1627298, by rfl⟩ : syracuseStep 2169731 = 3254597) B3254597
theorem B3661429 : Blo 2169435 3661429 := bbase (se 5 (by rfl) ⟨171629, by rfl⟩ : syracuseStep 3661429 = 343259) (by norm_num)
theorem B4881905 : Blo 2169435 4881905 := bstep (se 2 (by rfl) ⟨1830714, by rfl⟩ : syracuseStep 4881905 = 3661429) B3661429
theorem B3254603 : Blo 2169435 3254603 := bstep (se 1 (by rfl) ⟨2440952, by rfl⟩ : syracuseStep 3254603 = 4881905) B4881905
theorem B2169735 : Blo 2169435 2169735 := bstep (se 1 (by rfl) ⟨1627301, by rfl⟩ : syracuseStep 2169735 = 3254603) B3254603
theorem B2440957 : Blo 2169435 2440957 := bbase (se 3 (by rfl) ⟨457679, by rfl⟩ : syracuseStep 2440957 = 915359) (by norm_num)
theorem B3254609 : Blo 2169435 3254609 := bstep (se 2 (by rfl) ⟨1220478, by rfl⟩ : syracuseStep 3254609 = 2440957) B2440957
theorem B2169739 : Blo 2169435 2169739 := bstep (se 1 (by rfl) ⟨1627304, by rfl⟩ : syracuseStep 2169739 = 3254609) B3254609
theorem B7322885 : Blo 2169435 7322885 := bbase (se 4 (by rfl) ⟨686520, by rfl⟩ : syracuseStep 7322885 = 1373041) (by norm_num)
theorem B4881923 : Blo 2169435 4881923 := bstep (se 1 (by rfl) ⟨3661442, by rfl⟩ : syracuseStep 4881923 = 7322885) B7322885
theorem B3254615 : Blo 2169435 3254615 := bstep (se 1 (by rfl) ⟨2440961, by rfl⟩ : syracuseStep 3254615 = 4881923) B4881923
theorem B2169743 : Blo 2169435 2169743 := bstep (se 1 (by rfl) ⟨1627307, by rfl⟩ : syracuseStep 2169743 = 3254615) B3254615
theorem B3254621 : Blo 2169435 3254621 := bbase (se 3 (by rfl) ⟨610241, by rfl⟩ : syracuseStep 3254621 = 1220483) (by norm_num)
theorem B2169747 : Blo 2169435 2169747 := bstep (se 1 (by rfl) ⟨1627310, by rfl⟩ : syracuseStep 2169747 = 3254621) B3254621
theorem B4881941 : Blo 2169435 4881941 := bbase (se 6 (by rfl) ⟨114420, by rfl⟩ : syracuseStep 4881941 = 228841) (by norm_num)
theorem B3254627 : Blo 2169435 3254627 := bstep (se 1 (by rfl) ⟨2440970, by rfl⟩ : syracuseStep 3254627 = 4881941) B4881941
theorem B2169751 : Blo 2169435 2169751 := bstep (se 1 (by rfl) ⟨1627313, by rfl⟩ : syracuseStep 2169751 = 3254627) B3254627
theorem B8238293 : Blo 2169435 8238293 := bbase (se 7 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 8238293 = 193085) (by norm_num)
theorem B5492195 : Blo 2169435 5492195 := bstep (se 1 (by rfl) ⟨4119146, by rfl⟩ : syracuseStep 5492195 = 8238293) B8238293
theorem B3661463 : Blo 2169435 3661463 := bstep (se 1 (by rfl) ⟨2746097, by rfl⟩ : syracuseStep 3661463 = 5492195) B5492195
theorem B2440975 : Blo 2169435 2440975 := bstep (se 1 (by rfl) ⟨1830731, by rfl⟩ : syracuseStep 2440975 = 3661463) B3661463
theorem B3254633 : Blo 2169435 3254633 := bstep (se 2 (by rfl) ⟨1220487, by rfl⟩ : syracuseStep 3254633 = 2440975) B2440975
theorem B2169755 : Blo 2169435 2169755 := bstep (se 1 (by rfl) ⟨1627316, by rfl⟩ : syracuseStep 2169755 = 3254633) B3254633
theorem B12357461 : Blo 2169435 12357461 := bbase (se 9 (by rfl) ⟨36203, by rfl⟩ : syracuseStep 12357461 = 72407) (by norm_num)
theorem B8238307 : Blo 2169435 8238307 := bstep (se 1 (by rfl) ⟨6178730, by rfl⟩ : syracuseStep 8238307 = 12357461) B12357461
theorem B10984409 : Blo 2169435 10984409 := bstep (se 2 (by rfl) ⟨4119153, by rfl⟩ : syracuseStep 10984409 = 8238307) B8238307
theorem B7322939 : Blo 2169435 7322939 := bstep (se 1 (by rfl) ⟨5492204, by rfl⟩ : syracuseStep 7322939 = 10984409) B10984409
theorem B4881959 : Blo 2169435 4881959 := bstep (se 1 (by rfl) ⟨3661469, by rfl⟩ : syracuseStep 4881959 = 7322939) B7322939
theorem B3254639 : Blo 2169435 3254639 := bstep (se 1 (by rfl) ⟨2440979, by rfl⟩ : syracuseStep 3254639 = 4881959) B4881959
theorem B2169759 : Blo 2169435 2169759 := bstep (se 1 (by rfl) ⟨1627319, by rfl⟩ : syracuseStep 2169759 = 3254639) B3254639
theorem B3254645 : Blo 2169435 3254645 := bbase (se 5 (by rfl) ⟨152561, by rfl⟩ : syracuseStep 3254645 = 305123) (by norm_num)
theorem B2169763 : Blo 2169435 2169763 := bstep (se 1 (by rfl) ⟨1627322, by rfl⟩ : syracuseStep 2169763 = 3254645) B3254645
theorem B2317033 : Blo 2169435 2317033 := bbase (se 2 (by rfl) ⟨868887, by rfl⟩ : syracuseStep 2317033 = 1737775) (by norm_num)
theorem B3089377 : Blo 2169435 3089377 := bstep (se 2 (by rfl) ⟨1158516, by rfl⟩ : syracuseStep 3089377 = 2317033) B2317033
theorem B4119169 : Blo 2169435 4119169 := bstep (se 2 (by rfl) ⟨1544688, by rfl⟩ : syracuseStep 4119169 = 3089377) B3089377
theorem B5492225 : Blo 2169435 5492225 := bstep (se 2 (by rfl) ⟨2059584, by rfl⟩ : syracuseStep 5492225 = 4119169) B4119169
theorem B3661483 : Blo 2169435 3661483 := bstep (se 1 (by rfl) ⟨2746112, by rfl⟩ : syracuseStep 3661483 = 5492225) B5492225
theorem B4881977 : Blo 2169435 4881977 := bstep (se 2 (by rfl) ⟨1830741, by rfl⟩ : syracuseStep 4881977 = 3661483) B3661483
theorem B3254651 : Blo 2169435 3254651 := bstep (se 1 (by rfl) ⟨2440988, by rfl⟩ : syracuseStep 3254651 = 4881977) B4881977
theorem B2169767 : Blo 2169435 2169767 := bstep (se 1 (by rfl) ⟨1627325, by rfl⟩ : syracuseStep 2169767 = 3254651) B3254651
theorem B2440993 : Blo 2169435 2440993 := bbase (se 2 (by rfl) ⟨915372, by rfl⟩ : syracuseStep 2440993 = 1830745) (by norm_num)
theorem B3254657 : Blo 2169435 3254657 := bstep (se 2 (by rfl) ⟨1220496, by rfl⟩ : syracuseStep 3254657 = 2440993) B2440993
theorem B2169771 : Blo 2169435 2169771 := bstep (se 1 (by rfl) ⟨1627328, by rfl⟩ : syracuseStep 2169771 = 3254657) B3254657
theorem B5492245 : Blo 2169435 5492245 := bbase (se 6 (by rfl) ⟨128724, by rfl⟩ : syracuseStep 5492245 = 257449) (by norm_num)
theorem B7322993 : Blo 2169435 7322993 := bstep (se 2 (by rfl) ⟨2746122, by rfl⟩ : syracuseStep 7322993 = 5492245) B5492245
theorem B4881995 : Blo 2169435 4881995 := bstep (se 1 (by rfl) ⟨3661496, by rfl⟩ : syracuseStep 4881995 = 7322993) B7322993
theorem B3254663 : Blo 2169435 3254663 := bstep (se 1 (by rfl) ⟨2440997, by rfl⟩ : syracuseStep 3254663 = 4881995) B4881995
theorem B2169775 : Blo 2169435 2169775 := bstep (se 1 (by rfl) ⟨1627331, by rfl⟩ : syracuseStep 2169775 = 3254663) B3254663
theorem B3254669 : Blo 2169435 3254669 := bbase (se 3 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 3254669 = 1220501) (by norm_num)
theorem B2169779 : Blo 2169435 2169779 := bstep (se 1 (by rfl) ⟨1627334, by rfl⟩ : syracuseStep 2169779 = 3254669) B3254669
theorem B4882013 : Blo 2169435 4882013 := bbase (se 3 (by rfl) ⟨915377, by rfl⟩ : syracuseStep 4882013 = 1830755) (by norm_num)
theorem B3254675 : Blo 2169435 3254675 := bstep (se 1 (by rfl) ⟨2441006, by rfl⟩ : syracuseStep 3254675 = 4882013) B4882013
theorem B2169783 : Blo 2169435 2169783 := bstep (se 1 (by rfl) ⟨1627337, by rfl⟩ : syracuseStep 2169783 = 3254675) B3254675
theorem B3661517 : Blo 2169435 3661517 := bbase (se 3 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 3661517 = 1373069) (by norm_num)
theorem B2441011 : Blo 2169435 2441011 := bstep (se 1 (by rfl) ⟨1830758, by rfl⟩ : syracuseStep 2441011 = 3661517) B3661517
theorem B3254681 : Blo 2169435 3254681 := bstep (se 2 (by rfl) ⟨1220505, by rfl⟩ : syracuseStep 3254681 = 2441011) B2441011
theorem B2169787 : Blo 2169435 2169787 := bstep (se 1 (by rfl) ⟨1627340, by rfl⟩ : syracuseStep 2169787 = 3254681) B3254681
theorem B5213381 : Blo 2169435 5213381 := bbase (se 4 (by rfl) ⟨488754, by rfl⟩ : syracuseStep 5213381 = 977509) (by norm_num)
theorem B13902349 : Blo 2169435 13902349 := bstep (se 3 (by rfl) ⟨2606690, by rfl⟩ : syracuseStep 13902349 = 5213381) B5213381
theorem B18536465 : Blo 2169435 18536465 := bstep (se 2 (by rfl) ⟨6951174, by rfl⟩ : syracuseStep 18536465 = 13902349) B13902349
theorem B12357643 : Blo 2169435 12357643 := bstep (se 1 (by rfl) ⟨9268232, by rfl⟩ : syracuseStep 12357643 = 18536465) B18536465
theorem B16476857 : Blo 2169435 16476857 := bstep (se 2 (by rfl) ⟨6178821, by rfl⟩ : syracuseStep 16476857 = 12357643) B12357643
theorem B10984571 : Blo 2169435 10984571 := bstep (se 1 (by rfl) ⟨8238428, by rfl⟩ : syracuseStep 10984571 = 16476857) B16476857
theorem B7323047 : Blo 2169435 7323047 := bstep (se 1 (by rfl) ⟨5492285, by rfl⟩ : syracuseStep 7323047 = 10984571) B10984571
theorem B4882031 : Blo 2169435 4882031 := bstep (se 1 (by rfl) ⟨3661523, by rfl⟩ : syracuseStep 4882031 = 7323047) B7323047
theorem B3254687 : Blo 2169435 3254687 := bstep (se 1 (by rfl) ⟨2441015, by rfl⟩ : syracuseStep 3254687 = 4882031) B4882031
theorem B2169791 : Blo 2169435 2169791 := bstep (se 1 (by rfl) ⟨1627343, by rfl⟩ : syracuseStep 2169791 = 3254687) B3254687
theorem B3254693 : Blo 2169435 3254693 := bbase (se 4 (by rfl) ⟨305127, by rfl⟩ : syracuseStep 3254693 = 610255) (by norm_num)
theorem B2169795 : Blo 2169435 2169795 := bstep (se 1 (by rfl) ⟨1627346, by rfl⟩ : syracuseStep 2169795 = 3254693) B3254693
theorem B2746153 : Blo 2169435 2746153 := bbase (se 2 (by rfl) ⟨1029807, by rfl⟩ : syracuseStep 2746153 = 2059615) (by norm_num)
theorem B3661537 : Blo 2169435 3661537 := bstep (se 2 (by rfl) ⟨1373076, by rfl⟩ : syracuseStep 3661537 = 2746153) B2746153
theorem B4882049 : Blo 2169435 4882049 := bstep (se 2 (by rfl) ⟨1830768, by rfl⟩ : syracuseStep 4882049 = 3661537) B3661537
theorem B3254699 : Blo 2169435 3254699 := bstep (se 1 (by rfl) ⟨2441024, by rfl⟩ : syracuseStep 3254699 = 4882049) B4882049
theorem B2169799 : Blo 2169435 2169799 := bstep (se 1 (by rfl) ⟨1627349, by rfl⟩ : syracuseStep 2169799 = 3254699) B3254699
theorem B2441029 : Blo 2169435 2441029 := bbase (se 4 (by rfl) ⟨228846, by rfl⟩ : syracuseStep 2441029 = 457693) (by norm_num)
theorem B3254705 : Blo 2169435 3254705 := bstep (se 2 (by rfl) ⟨1220514, by rfl⟩ : syracuseStep 3254705 = 2441029) B2441029
theorem B2169803 : Blo 2169435 2169803 := bstep (se 1 (by rfl) ⟨1627352, by rfl⟩ : syracuseStep 2169803 = 3254705) B3254705
theorem B4119245 : Blo 2169435 4119245 := bbase (se 3 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 4119245 = 1544717) (by norm_num)
theorem B2746163 : Blo 2169435 2746163 := bstep (se 1 (by rfl) ⟨2059622, by rfl⟩ : syracuseStep 2746163 = 4119245) B4119245
theorem B7323101 : Blo 2169435 7323101 := bstep (se 3 (by rfl) ⟨1373081, by rfl⟩ : syracuseStep 7323101 = 2746163) B2746163
theorem B4882067 : Blo 2169435 4882067 := bstep (se 1 (by rfl) ⟨3661550, by rfl⟩ : syracuseStep 4882067 = 7323101) B7323101
theorem B3254711 : Blo 2169435 3254711 := bstep (se 1 (by rfl) ⟨2441033, by rfl⟩ : syracuseStep 3254711 = 4882067) B4882067
theorem B2169807 : Blo 2169435 2169807 := bstep (se 1 (by rfl) ⟨1627355, by rfl⟩ : syracuseStep 2169807 = 3254711) B3254711
theorem B3254717 : Blo 2169435 3254717 := bbase (se 3 (by rfl) ⟨610259, by rfl⟩ : syracuseStep 3254717 = 1220519) (by norm_num)
theorem B2169811 : Blo 2169435 2169811 := bstep (se 1 (by rfl) ⟨1627358, by rfl⟩ : syracuseStep 2169811 = 3254717) B3254717
theorem B4882085 : Blo 2169435 4882085 := bbase (se 4 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 4882085 = 915391) (by norm_num)
theorem B3254723 : Blo 2169435 3254723 := bstep (se 1 (by rfl) ⟨2441042, by rfl⟩ : syracuseStep 3254723 = 4882085) B4882085
theorem B2169815 : Blo 2169435 2169815 := bstep (se 1 (by rfl) ⟨1627361, by rfl⟩ : syracuseStep 2169815 = 3254723) B3254723
theorem B5492357 : Blo 2169435 5492357 := bbase (se 4 (by rfl) ⟨514908, by rfl⟩ : syracuseStep 5492357 = 1029817) (by norm_num)
theorem B3661571 : Blo 2169435 3661571 := bstep (se 1 (by rfl) ⟨2746178, by rfl⟩ : syracuseStep 3661571 = 5492357) B5492357
theorem B2441047 : Blo 2169435 2441047 := bstep (se 1 (by rfl) ⟨1830785, by rfl⟩ : syracuseStep 2441047 = 3661571) B3661571
theorem B3254729 : Blo 2169435 3254729 := bstep (se 2 (by rfl) ⟨1220523, by rfl⟩ : syracuseStep 3254729 = 2441047) B2441047
theorem B2169819 : Blo 2169435 2169819 := bstep (se 1 (by rfl) ⟨1627364, by rfl⟩ : syracuseStep 2169819 = 3254729) B3254729
theorem B3523061 : Blo 2169435 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B9394829 : Blo 2169435 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B6263219 : Blo 2169435 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B4175479 : Blo 2169435 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B5567305 : Blo 2169435 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B7423073 : Blo 2169435 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B4948715 : Blo 2169435 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B3299143 : Blo 2169435 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B4398857 : Blo 2169435 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B2932571 : Blo 2169435 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B7820189 : Blo 2169435 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B5213459 : Blo 2169435 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B3475639 : Blo 2169435 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B4634185 : Blo 2169435 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B6178913 : Blo 2169435 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B4119275 : Blo 2169435 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B10984733 : Blo 2169435 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B7323155 : Blo 2169435 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B4882103 : Blo 2169435 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B3254735 : Blo 2169435 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B2169823 : Blo 2169435 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B3254741 : Blo 2169435 3254741 := bbase (se 7 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 3254741 = 76283) (by norm_num)
theorem B2169827 : Blo 2169435 2169827 := bstep (se 1 (by rfl) ⟨1627370, by rfl⟩ : syracuseStep 2169827 = 3254741) B3254741
theorem B8238581 : Blo 2169435 8238581 := bbase (se 5 (by rfl) ⟨386183, by rfl⟩ : syracuseStep 8238581 = 772367) (by norm_num)
theorem B5492387 : Blo 2169435 5492387 := bstep (se 1 (by rfl) ⟨4119290, by rfl⟩ : syracuseStep 5492387 = 8238581) B8238581
theorem B3661591 : Blo 2169435 3661591 := bstep (se 1 (by rfl) ⟨2746193, by rfl⟩ : syracuseStep 3661591 = 5492387) B5492387
theorem B4882121 : Blo 2169435 4882121 := bstep (se 2 (by rfl) ⟨1830795, by rfl⟩ : syracuseStep 4882121 = 3661591) B3661591
theorem B3254747 : Blo 2169435 3254747 := bstep (se 1 (by rfl) ⟨2441060, by rfl⟩ : syracuseStep 3254747 = 4882121) B4882121
theorem B2169831 : Blo 2169435 2169831 := bstep (se 1 (by rfl) ⟨1627373, by rfl⟩ : syracuseStep 2169831 = 3254747) B3254747
theorem B2441065 : Blo 2169435 2441065 := bbase (se 2 (by rfl) ⟨915399, by rfl⟩ : syracuseStep 2441065 = 1830799) (by norm_num)
theorem B3254753 : Blo 2169435 3254753 := bstep (se 2 (by rfl) ⟨1220532, by rfl⟩ : syracuseStep 3254753 = 2441065) B2441065
theorem B2169835 : Blo 2169435 2169835 := bstep (se 1 (by rfl) ⟨1627376, by rfl⟩ : syracuseStep 2169835 = 3254753) B3254753
theorem B16702037 : Blo 2169435 16702037 := bbase (se 8 (by rfl) ⟨97863, by rfl⟩ : syracuseStep 16702037 = 195727) (by norm_num)
theorem B11134691 : Blo 2169435 11134691 := bstep (se 1 (by rfl) ⟨8351018, by rfl⟩ : syracuseStep 11134691 = 16702037) B16702037
theorem B7423127 : Blo 2169435 7423127 := bstep (se 1 (by rfl) ⟨5567345, by rfl⟩ : syracuseStep 7423127 = 11134691) B11134691
theorem B4948751 : Blo 2169435 4948751 := bstep (se 1 (by rfl) ⟨3711563, by rfl⟩ : syracuseStep 4948751 = 7423127) B7423127
theorem B3299167 : Blo 2169435 3299167 := bstep (se 1 (by rfl) ⟨2474375, by rfl⟩ : syracuseStep 3299167 = 4948751) B4948751
theorem B4398889 : Blo 2169435 4398889 := bstep (se 2 (by rfl) ⟨1649583, by rfl⟩ : syracuseStep 4398889 = 3299167) B3299167
theorem B5865185 : Blo 2169435 5865185 := bstep (se 2 (by rfl) ⟨2199444, by rfl⟩ : syracuseStep 5865185 = 4398889) B4398889
theorem B3910123 : Blo 2169435 3910123 := bstep (se 1 (by rfl) ⟨2932592, by rfl⟩ : syracuseStep 3910123 = 5865185) B5865185
theorem B5213497 : Blo 2169435 5213497 := bstep (se 2 (by rfl) ⟨1955061, by rfl⟩ : syracuseStep 5213497 = 3910123) B3910123
theorem B6951329 : Blo 2169435 6951329 := bstep (se 2 (by rfl) ⟨2606748, by rfl⟩ : syracuseStep 6951329 = 5213497) B5213497
theorem B4634219 : Blo 2169435 4634219 := bstep (se 1 (by rfl) ⟨3475664, by rfl⟩ : syracuseStep 4634219 = 6951329) B6951329
theorem B12357917 : Blo 2169435 12357917 := bstep (se 3 (by rfl) ⟨2317109, by rfl⟩ : syracuseStep 12357917 = 4634219) B4634219
theorem B8238611 : Blo 2169435 8238611 := bstep (se 1 (by rfl) ⟨6178958, by rfl⟩ : syracuseStep 8238611 = 12357917) B12357917
theorem B5492407 : Blo 2169435 5492407 := bstep (se 1 (by rfl) ⟨4119305, by rfl⟩ : syracuseStep 5492407 = 8238611) B8238611
theorem B7323209 : Blo 2169435 7323209 := bstep (se 2 (by rfl) ⟨2746203, by rfl⟩ : syracuseStep 7323209 = 5492407) B5492407
theorem B4882139 : Blo 2169435 4882139 := bstep (se 1 (by rfl) ⟨3661604, by rfl⟩ : syracuseStep 4882139 = 7323209) B7323209
theorem B3254759 : Blo 2169435 3254759 := bstep (se 1 (by rfl) ⟨2441069, by rfl⟩ : syracuseStep 3254759 = 4882139) B4882139
theorem B2169839 : Blo 2169435 2169839 := bstep (se 1 (by rfl) ⟨1627379, by rfl⟩ : syracuseStep 2169839 = 3254759) B3254759
theorem B3254765 : Blo 2169435 3254765 := bbase (se 3 (by rfl) ⟨610268, by rfl⟩ : syracuseStep 3254765 = 1220537) (by norm_num)
theorem B2169843 : Blo 2169435 2169843 := bstep (se 1 (by rfl) ⟨1627382, by rfl⟩ : syracuseStep 2169843 = 3254765) B3254765
theorem B4882157 : Blo 2169435 4882157 := bbase (se 3 (by rfl) ⟨915404, by rfl⟩ : syracuseStep 4882157 = 1830809) (by norm_num)
theorem B3254771 : Blo 2169435 3254771 := bstep (se 1 (by rfl) ⟨2441078, by rfl⟩ : syracuseStep 3254771 = 4882157) B4882157
theorem B2169847 : Blo 2169435 2169847 := bstep (se 1 (by rfl) ⟨1627385, by rfl⟩ : syracuseStep 2169847 = 3254771) B3254771
theorem B3475685 : Blo 2169435 3475685 := bbase (se 4 (by rfl) ⟨325845, by rfl⟩ : syracuseStep 3475685 = 651691) (by norm_num)
theorem B2317123 : Blo 2169435 2317123 := bstep (se 1 (by rfl) ⟨1737842, by rfl⟩ : syracuseStep 2317123 = 3475685) B3475685
theorem B3089497 : Blo 2169435 3089497 := bstep (se 2 (by rfl) ⟨1158561, by rfl⟩ : syracuseStep 3089497 = 2317123) B2317123
theorem B4119329 : Blo 2169435 4119329 := bstep (se 2 (by rfl) ⟨1544748, by rfl⟩ : syracuseStep 4119329 = 3089497) B3089497
theorem B2746219 : Blo 2169435 2746219 := bstep (se 1 (by rfl) ⟨2059664, by rfl⟩ : syracuseStep 2746219 = 4119329) B4119329
theorem B3661625 : Blo 2169435 3661625 := bstep (se 2 (by rfl) ⟨1373109, by rfl⟩ : syracuseStep 3661625 = 2746219) B2746219
theorem B2441083 : Blo 2169435 2441083 := bstep (se 1 (by rfl) ⟨1830812, by rfl⟩ : syracuseStep 2441083 = 3661625) B3661625
theorem B3254777 : Blo 2169435 3254777 := bstep (se 2 (by rfl) ⟨1220541, by rfl⟩ : syracuseStep 3254777 = 2441083) B2441083
theorem B2169851 : Blo 2169435 2169851 := bstep (se 1 (by rfl) ⟨1627388, by rfl⟩ : syracuseStep 2169851 = 3254777) B3254777
theorem B2860169 : Blo 2169435 2860169 := bbase (se 2 (by rfl) ⟨1072563, by rfl⟩ : syracuseStep 2860169 = 2145127) (by norm_num)
theorem B7627117 : Blo 2169435 7627117 := bstep (se 3 (by rfl) ⟨1430084, by rfl⟩ : syracuseStep 7627117 = 2860169) B2860169
theorem B10169489 : Blo 2169435 10169489 := bstep (se 2 (by rfl) ⟨3813558, by rfl⟩ : syracuseStep 10169489 = 7627117) B7627117
theorem B6779659 : Blo 2169435 6779659 := bstep (se 1 (by rfl) ⟨5084744, by rfl⟩ : syracuseStep 6779659 = 10169489) B10169489
theorem B9039545 : Blo 2169435 9039545 := bstep (se 2 (by rfl) ⟨3389829, by rfl⟩ : syracuseStep 9039545 = 6779659) B6779659
theorem B6026363 : Blo 2169435 6026363 := bstep (se 1 (by rfl) ⟨4519772, by rfl⟩ : syracuseStep 6026363 = 9039545) B9039545
theorem B4017575 : Blo 2169435 4017575 := bstep (se 1 (by rfl) ⟨3013181, by rfl⟩ : syracuseStep 4017575 = 6026363) B6026363
theorem B2678383 : Blo 2169435 2678383 := bstep (se 1 (by rfl) ⟨2008787, by rfl⟩ : syracuseStep 2678383 = 4017575) B4017575
theorem B3571177 : Blo 2169435 3571177 := bstep (se 2 (by rfl) ⟨1339191, by rfl⟩ : syracuseStep 3571177 = 2678383) B2678383
theorem B4761569 : Blo 2169435 4761569 := bstep (se 2 (by rfl) ⟨1785588, by rfl⟩ : syracuseStep 4761569 = 3571177) B3571177
theorem B12697517 : Blo 2169435 12697517 := bstep (se 3 (by rfl) ⟨2380784, by rfl⟩ : syracuseStep 12697517 = 4761569) B4761569
theorem B33860045 : Blo 2169435 33860045 := bstep (se 3 (by rfl) ⟨6348758, by rfl⟩ : syracuseStep 33860045 = 12697517) B12697517
theorem B90293453 : Blo 2169435 90293453 := bstep (se 3 (by rfl) ⟨16930022, by rfl⟩ : syracuseStep 90293453 = 33860045) B33860045
theorem B60195635 : Blo 2169435 60195635 := bstep (se 1 (by rfl) ⟨45146726, by rfl⟩ : syracuseStep 60195635 = 90293453) B90293453
theorem B40130423 : Blo 2169435 40130423 := bstep (se 1 (by rfl) ⟨30097817, by rfl⟩ : syracuseStep 40130423 = 60195635) B60195635
theorem B26753615 : Blo 2169435 26753615 := bstep (se 1 (by rfl) ⟨20065211, by rfl⟩ : syracuseStep 26753615 = 40130423) B40130423
theorem B17835743 : Blo 2169435 17835743 := bstep (se 1 (by rfl) ⟨13376807, by rfl⟩ : syracuseStep 17835743 = 26753615) B26753615
theorem B11890495 : Blo 2169435 11890495 := bstep (se 1 (by rfl) ⟨8917871, by rfl⟩ : syracuseStep 11890495 = 17835743) B17835743
theorem B15853993 : Blo 2169435 15853993 := bstep (se 2 (by rfl) ⟨5945247, by rfl⟩ : syracuseStep 15853993 = 11890495) B11890495
theorem B338218517 : Blo 2169435 338218517 := bstep (se 6 (by rfl) ⟨7926996, by rfl⟩ : syracuseStep 338218517 = 15853993) B15853993
theorem B901916045 : Blo 2169435 901916045 := bstep (se 3 (by rfl) ⟨169109258, by rfl⟩ : syracuseStep 901916045 = 338218517) B338218517
theorem B601277363 : Blo 2169435 601277363 := bstep (se 1 (by rfl) ⟨450958022, by rfl⟩ : syracuseStep 601277363 = 901916045) B901916045
theorem B400851575 : Blo 2169435 400851575 := bstep (se 1 (by rfl) ⟨300638681, by rfl⟩ : syracuseStep 400851575 = 601277363) B601277363
theorem B267234383 : Blo 2169435 267234383 := bstep (se 1 (by rfl) ⟨200425787, by rfl⟩ : syracuseStep 267234383 = 400851575) B400851575
theorem B178156255 : Blo 2169435 178156255 := bstep (se 1 (by rfl) ⟨133617191, by rfl⟩ : syracuseStep 178156255 = 267234383) B267234383
theorem B237541673 : Blo 2169435 237541673 := bstep (se 2 (by rfl) ⟨89078127, by rfl⟩ : syracuseStep 237541673 = 178156255) B178156255
theorem B158361115 : Blo 2169435 158361115 := bstep (se 1 (by rfl) ⟨118770836, by rfl⟩ : syracuseStep 158361115 = 237541673) B237541673
theorem B211148153 : Blo 2169435 211148153 := bstep (se 2 (by rfl) ⟨79180557, by rfl⟩ : syracuseStep 211148153 = 158361115) B158361115
theorem B140765435 : Blo 2169435 140765435 := bstep (se 1 (by rfl) ⟨105574076, by rfl⟩ : syracuseStep 140765435 = 211148153) B211148153
theorem B93843623 : Blo 2169435 93843623 := bstep (se 1 (by rfl) ⟨70382717, by rfl⟩ : syracuseStep 93843623 = 140765435) B140765435
theorem B62562415 : Blo 2169435 62562415 := bstep (se 1 (by rfl) ⟨46921811, by rfl⟩ : syracuseStep 62562415 = 93843623) B93843623
theorem B83416553 : Blo 2169435 83416553 := bstep (se 2 (by rfl) ⟨31281207, by rfl⟩ : syracuseStep 83416553 = 62562415) B62562415
theorem B55611035 : Blo 2169435 55611035 := bstep (se 1 (by rfl) ⟨41708276, by rfl⟩ : syracuseStep 55611035 = 83416553) B83416553
theorem B37074023 : Blo 2169435 37074023 := bstep (se 1 (by rfl) ⟨27805517, by rfl⟩ : syracuseStep 37074023 = 55611035) B55611035
theorem B24716015 : Blo 2169435 24716015 := bstep (se 1 (by rfl) ⟨18537011, by rfl⟩ : syracuseStep 24716015 = 37074023) B37074023
theorem B16477343 : Blo 2169435 16477343 := bstep (se 1 (by rfl) ⟨12358007, by rfl⟩ : syracuseStep 16477343 = 24716015) B24716015
theorem B10984895 : Blo 2169435 10984895 := bstep (se 1 (by rfl) ⟨8238671, by rfl⟩ : syracuseStep 10984895 = 16477343) B16477343
theorem B7323263 : Blo 2169435 7323263 := bstep (se 1 (by rfl) ⟨5492447, by rfl⟩ : syracuseStep 7323263 = 10984895) B10984895
theorem B4882175 : Blo 2169435 4882175 := bstep (se 1 (by rfl) ⟨3661631, by rfl⟩ : syracuseStep 4882175 = 7323263) B7323263
theorem B3254783 : Blo 2169435 3254783 := bstep (se 1 (by rfl) ⟨2441087, by rfl⟩ : syracuseStep 3254783 = 4882175) B4882175
theorem B2169855 : Blo 2169435 2169855 := bstep (se 1 (by rfl) ⟨1627391, by rfl⟩ : syracuseStep 2169855 = 3254783) B3254783
theorem B3254789 : Blo 2169435 3254789 := bbase (se 4 (by rfl) ⟨305136, by rfl⟩ : syracuseStep 3254789 = 610273) (by norm_num)
theorem B2169859 : Blo 2169435 2169859 := bstep (se 1 (by rfl) ⟨1627394, by rfl⟩ : syracuseStep 2169859 = 3254789) B3254789
theorem B3661645 : Blo 2169435 3661645 := bbase (se 3 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 3661645 = 1373117) (by norm_num)
theorem B4882193 : Blo 2169435 4882193 := bstep (se 2 (by rfl) ⟨1830822, by rfl⟩ : syracuseStep 4882193 = 3661645) B3661645
theorem B3254795 : Blo 2169435 3254795 := bstep (se 1 (by rfl) ⟨2441096, by rfl⟩ : syracuseStep 3254795 = 4882193) B4882193
theorem B2169863 : Blo 2169435 2169863 := bstep (se 1 (by rfl) ⟨1627397, by rfl⟩ : syracuseStep 2169863 = 3254795) B3254795
theorem B2441101 : Blo 2169435 2441101 := bbase (se 3 (by rfl) ⟨457706, by rfl⟩ : syracuseStep 2441101 = 915413) (by norm_num)
theorem B3254801 : Blo 2169435 3254801 := bstep (se 2 (by rfl) ⟨1220550, by rfl⟩ : syracuseStep 3254801 = 2441101) B2441101
theorem B2169867 : Blo 2169435 2169867 := bstep (se 1 (by rfl) ⟨1627400, by rfl⟩ : syracuseStep 2169867 = 3254801) B3254801
theorem B7323317 : Blo 2169435 7323317 := bbase (se 5 (by rfl) ⟨343280, by rfl⟩ : syracuseStep 7323317 = 686561) (by norm_num)
theorem B4882211 : Blo 2169435 4882211 := bstep (se 1 (by rfl) ⟨3661658, by rfl⟩ : syracuseStep 4882211 = 7323317) B7323317
theorem B3254807 : Blo 2169435 3254807 := bstep (se 1 (by rfl) ⟨2441105, by rfl⟩ : syracuseStep 3254807 = 4882211) B4882211
theorem B2169871 : Blo 2169435 2169871 := bstep (se 1 (by rfl) ⟨1627403, by rfl⟩ : syracuseStep 2169871 = 3254807) B3254807
theorem B3254813 : Blo 2169435 3254813 := bbase (se 3 (by rfl) ⟨610277, by rfl⟩ : syracuseStep 3254813 = 1220555) (by norm_num)
theorem B2169875 : Blo 2169435 2169875 := bstep (se 1 (by rfl) ⟨1627406, by rfl⟩ : syracuseStep 2169875 = 3254813) B3254813
theorem B4882229 : Blo 2169435 4882229 := bbase (se 5 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 4882229 = 457709) (by norm_num)
theorem B3254819 : Blo 2169435 3254819 := bstep (se 1 (by rfl) ⟨2441114, by rfl⟩ : syracuseStep 3254819 = 4882229) B4882229
theorem B2169879 : Blo 2169435 2169879 := bstep (se 1 (by rfl) ⟨1627409, by rfl⟩ : syracuseStep 2169879 = 3254819) B3254819
theorem B7820405 : Blo 2169435 7820405 := bbase (se 5 (by rfl) ⟨366581, by rfl⟩ : syracuseStep 7820405 = 733163) (by norm_num)
theorem B5213603 : Blo 2169435 5213603 := bstep (se 1 (by rfl) ⟨3910202, by rfl⟩ : syracuseStep 5213603 = 7820405) B7820405
theorem B13902941 : Blo 2169435 13902941 := bstep (se 3 (by rfl) ⟨2606801, by rfl⟩ : syracuseStep 13902941 = 5213603) B5213603
theorem B9268627 : Blo 2169435 9268627 := bstep (se 1 (by rfl) ⟨6951470, by rfl⟩ : syracuseStep 9268627 = 13902941) B13902941
theorem B12358169 : Blo 2169435 12358169 := bstep (se 2 (by rfl) ⟨4634313, by rfl⟩ : syracuseStep 12358169 = 9268627) B9268627
theorem B8238779 : Blo 2169435 8238779 := bstep (se 1 (by rfl) ⟨6179084, by rfl⟩ : syracuseStep 8238779 = 12358169) B12358169
theorem B5492519 : Blo 2169435 5492519 := bstep (se 1 (by rfl) ⟨4119389, by rfl⟩ : syracuseStep 5492519 = 8238779) B8238779
theorem B3661679 : Blo 2169435 3661679 := bstep (se 1 (by rfl) ⟨2746259, by rfl⟩ : syracuseStep 3661679 = 5492519) B5492519
theorem B2441119 : Blo 2169435 2441119 := bstep (se 1 (by rfl) ⟨1830839, by rfl⟩ : syracuseStep 2441119 = 3661679) B3661679
theorem B3254825 : Blo 2169435 3254825 := bstep (se 2 (by rfl) ⟨1220559, by rfl⟩ : syracuseStep 3254825 = 2441119) B2441119
theorem B2169883 : Blo 2169435 2169883 := bstep (se 1 (by rfl) ⟨1627412, by rfl⟩ : syracuseStep 2169883 = 3254825) B3254825
theorem B13902965 : Blo 2169435 13902965 := bbase (se 5 (by rfl) ⟨651701, by rfl⟩ : syracuseStep 13902965 = 1303403) (by norm_num)
theorem B9268643 : Blo 2169435 9268643 := bstep (se 1 (by rfl) ⟨6951482, by rfl⟩ : syracuseStep 9268643 = 13902965) B13902965
theorem B6179095 : Blo 2169435 6179095 := bstep (se 1 (by rfl) ⟨4634321, by rfl⟩ : syracuseStep 6179095 = 9268643) B9268643
theorem B8238793 : Blo 2169435 8238793 := bstep (se 2 (by rfl) ⟨3089547, by rfl⟩ : syracuseStep 8238793 = 6179095) B6179095
theorem B10985057 : Blo 2169435 10985057 := bstep (se 2 (by rfl) ⟨4119396, by rfl⟩ : syracuseStep 10985057 = 8238793) B8238793
theorem B7323371 : Blo 2169435 7323371 := bstep (se 1 (by rfl) ⟨5492528, by rfl⟩ : syracuseStep 7323371 = 10985057) B10985057
theorem B4882247 : Blo 2169435 4882247 := bstep (se 1 (by rfl) ⟨3661685, by rfl⟩ : syracuseStep 4882247 = 7323371) B7323371
theorem B3254831 : Blo 2169435 3254831 := bstep (se 1 (by rfl) ⟨2441123, by rfl⟩ : syracuseStep 3254831 = 4882247) B4882247
theorem B2169887 : Blo 2169435 2169887 := bstep (se 1 (by rfl) ⟨1627415, by rfl⟩ : syracuseStep 2169887 = 3254831) B3254831
theorem B3254837 : Blo 2169435 3254837 := bbase (se 5 (by rfl) ⟨152570, by rfl⟩ : syracuseStep 3254837 = 305141) (by norm_num)
theorem B2169891 : Blo 2169435 2169891 := bstep (se 1 (by rfl) ⟨1627418, by rfl⟩ : syracuseStep 2169891 = 3254837) B3254837
theorem B5492549 : Blo 2169435 5492549 := bbase (se 4 (by rfl) ⟨514926, by rfl⟩ : syracuseStep 5492549 = 1029853) (by norm_num)
theorem B3661699 : Blo 2169435 3661699 := bstep (se 1 (by rfl) ⟨2746274, by rfl⟩ : syracuseStep 3661699 = 5492549) B5492549
theorem B4882265 : Blo 2169435 4882265 := bstep (se 2 (by rfl) ⟨1830849, by rfl⟩ : syracuseStep 4882265 = 3661699) B3661699
theorem B3254843 : Blo 2169435 3254843 := bstep (se 1 (by rfl) ⟨2441132, by rfl⟩ : syracuseStep 3254843 = 4882265) B4882265
theorem B2169895 : Blo 2169435 2169895 := bstep (se 1 (by rfl) ⟨1627421, by rfl⟩ : syracuseStep 2169895 = 3254843) B3254843
theorem B2441137 : Blo 2169435 2441137 := bbase (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) (by norm_num)
theorem B3254849 : Blo 2169435 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B2169899 : Blo 2169435 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B6179141 : Blo 2169435 6179141 := bbase (se 4 (by rfl) ⟨579294, by rfl⟩ : syracuseStep 6179141 = 1158589) (by norm_num)
theorem B4119427 : Blo 2169435 4119427 := bstep (se 1 (by rfl) ⟨3089570, by rfl⟩ : syracuseStep 4119427 = 6179141) B6179141
theorem B5492569 : Blo 2169435 5492569 := bstep (se 2 (by rfl) ⟨2059713, by rfl⟩ : syracuseStep 5492569 = 4119427) B4119427
theorem B7323425 : Blo 2169435 7323425 := bstep (se 2 (by rfl) ⟨2746284, by rfl⟩ : syracuseStep 7323425 = 5492569) B5492569
theorem B4882283 : Blo 2169435 4882283 := bstep (se 1 (by rfl) ⟨3661712, by rfl⟩ : syracuseStep 4882283 = 7323425) B7323425
theorem B3254855 : Blo 2169435 3254855 := bstep (se 1 (by rfl) ⟨2441141, by rfl⟩ : syracuseStep 3254855 = 4882283) B4882283
theorem B2169903 : Blo 2169435 2169903 := bstep (se 1 (by rfl) ⟨1627427, by rfl⟩ : syracuseStep 2169903 = 3254855) B3254855
theorem B3254861 : Blo 2169435 3254861 := bbase (se 3 (by rfl) ⟨610286, by rfl⟩ : syracuseStep 3254861 = 1220573) (by norm_num)
theorem B2169907 : Blo 2169435 2169907 := bstep (se 1 (by rfl) ⟨1627430, by rfl⟩ : syracuseStep 2169907 = 3254861) B3254861
theorem B4882301 : Blo 2169435 4882301 := bbase (se 3 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 4882301 = 1830863) (by norm_num)
theorem B3254867 : Blo 2169435 3254867 := bstep (se 1 (by rfl) ⟨2441150, by rfl⟩ : syracuseStep 3254867 = 4882301) B4882301
theorem B2169911 : Blo 2169435 2169911 := bstep (se 1 (by rfl) ⟨1627433, by rfl⟩ : syracuseStep 2169911 = 3254867) B3254867
theorem B3661733 : Blo 2169435 3661733 := bbase (se 4 (by rfl) ⟨343287, by rfl⟩ : syracuseStep 3661733 = 686575) (by norm_num)
theorem B2441155 : Blo 2169435 2441155 := bstep (se 1 (by rfl) ⟨1830866, by rfl⟩ : syracuseStep 2441155 = 3661733) B3661733
theorem B3254873 : Blo 2169435 3254873 := bstep (se 2 (by rfl) ⟨1220577, by rfl⟩ : syracuseStep 3254873 = 2441155) B2441155
theorem B2169915 : Blo 2169435 2169915 := bstep (se 1 (by rfl) ⟨1627436, by rfl⟩ : syracuseStep 2169915 = 3254873) B3254873
theorem B2606845 : Blo 2169435 2606845 := bbase (se 3 (by rfl) ⟨488783, by rfl⟩ : syracuseStep 2606845 = 977567) (by norm_num)
theorem B3475793 : Blo 2169435 3475793 := bstep (se 2 (by rfl) ⟨1303422, by rfl⟩ : syracuseStep 3475793 = 2606845) B2606845
theorem B2317195 : Blo 2169435 2317195 := bstep (se 1 (by rfl) ⟨1737896, by rfl⟩ : syracuseStep 2317195 = 3475793) B3475793
theorem B3089593 : Blo 2169435 3089593 := bstep (se 2 (by rfl) ⟨1158597, by rfl⟩ : syracuseStep 3089593 = 2317195) B2317195
theorem B16477829 : Blo 2169435 16477829 := bstep (se 4 (by rfl) ⟨1544796, by rfl⟩ : syracuseStep 16477829 = 3089593) B3089593
theorem B10985219 : Blo 2169435 10985219 := bstep (se 1 (by rfl) ⟨8238914, by rfl⟩ : syracuseStep 10985219 = 16477829) B16477829
theorem B7323479 : Blo 2169435 7323479 := bstep (se 1 (by rfl) ⟨5492609, by rfl⟩ : syracuseStep 7323479 = 10985219) B10985219
theorem B4882319 : Blo 2169435 4882319 := bstep (se 1 (by rfl) ⟨3661739, by rfl⟩ : syracuseStep 4882319 = 7323479) B7323479
theorem B3254879 : Blo 2169435 3254879 := bstep (se 1 (by rfl) ⟨2441159, by rfl⟩ : syracuseStep 3254879 = 4882319) B4882319
theorem B2169919 : Blo 2169435 2169919 := bstep (se 1 (by rfl) ⟨1627439, by rfl⟩ : syracuseStep 2169919 = 3254879) B3254879
theorem B3254885 : Blo 2169435 3254885 := bbase (se 4 (by rfl) ⟨305145, by rfl⟩ : syracuseStep 3254885 = 610291) (by norm_num)
theorem B2169923 : Blo 2169435 2169923 := bstep (se 1 (by rfl) ⟨1627442, by rfl⟩ : syracuseStep 2169923 = 3254885) B3254885
theorem B3089605 : Blo 2169435 3089605 := bbase (se 4 (by rfl) ⟨289650, by rfl⟩ : syracuseStep 3089605 = 579301) (by norm_num)
theorem B4119473 : Blo 2169435 4119473 := bstep (se 2 (by rfl) ⟨1544802, by rfl⟩ : syracuseStep 4119473 = 3089605) B3089605
theorem B2746315 : Blo 2169435 2746315 := bstep (se 1 (by rfl) ⟨2059736, by rfl⟩ : syracuseStep 2746315 = 4119473) B4119473
theorem B3661753 : Blo 2169435 3661753 := bstep (se 2 (by rfl) ⟨1373157, by rfl⟩ : syracuseStep 3661753 = 2746315) B2746315
theorem B4882337 : Blo 2169435 4882337 := bstep (se 2 (by rfl) ⟨1830876, by rfl⟩ : syracuseStep 4882337 = 3661753) B3661753
theorem B3254891 : Blo 2169435 3254891 := bstep (se 1 (by rfl) ⟨2441168, by rfl⟩ : syracuseStep 3254891 = 4882337) B4882337
theorem B2169927 : Blo 2169435 2169927 := bstep (se 1 (by rfl) ⟨1627445, by rfl⟩ : syracuseStep 2169927 = 3254891) B3254891
theorem B2441173 : Blo 2169435 2441173 := bbase (se 7 (by rfl) ⟨28607, by rfl⟩ : syracuseStep 2441173 = 57215) (by norm_num)
theorem B3254897 : Blo 2169435 3254897 := bstep (se 2 (by rfl) ⟨1220586, by rfl⟩ : syracuseStep 3254897 = 2441173) B2441173
theorem B2169931 : Blo 2169435 2169931 := bstep (se 1 (by rfl) ⟨1627448, by rfl⟩ : syracuseStep 2169931 = 3254897) B3254897
theorem B2746325 : Blo 2169435 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B7323533 : Blo 2169435 7323533 := bstep (se 3 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 7323533 = 2746325) B2746325
theorem B4882355 : Blo 2169435 4882355 := bstep (se 1 (by rfl) ⟨3661766, by rfl⟩ : syracuseStep 4882355 = 7323533) B7323533
theorem B3254903 : Blo 2169435 3254903 := bstep (se 1 (by rfl) ⟨2441177, by rfl⟩ : syracuseStep 3254903 = 4882355) B4882355
theorem B2169935 : Blo 2169435 2169935 := bstep (se 1 (by rfl) ⟨1627451, by rfl⟩ : syracuseStep 2169935 = 3254903) B3254903
theorem B3254909 : Blo 2169435 3254909 := bbase (se 3 (by rfl) ⟨610295, by rfl⟩ : syracuseStep 3254909 = 1220591) (by norm_num)
theorem B2169939 : Blo 2169435 2169939 := bstep (se 1 (by rfl) ⟨1627454, by rfl⟩ : syracuseStep 2169939 = 3254909) B3254909
theorem B4882373 : Blo 2169435 4882373 := bbase (se 4 (by rfl) ⟨457722, by rfl⟩ : syracuseStep 4882373 = 915445) (by norm_num)
theorem B3254915 : Blo 2169435 3254915 := bstep (se 1 (by rfl) ⟨2441186, by rfl⟩ : syracuseStep 3254915 = 4882373) B4882373
theorem B2169943 : Blo 2169435 2169943 := bstep (se 1 (by rfl) ⟨1627457, by rfl⟩ : syracuseStep 2169943 = 3254915) B3254915
theorem B9268901 : Blo 2169435 9268901 := bbase (se 4 (by rfl) ⟨868959, by rfl⟩ : syracuseStep 9268901 = 1737919) (by norm_num)
theorem B6179267 : Blo 2169435 6179267 := bstep (se 1 (by rfl) ⟨4634450, by rfl⟩ : syracuseStep 6179267 = 9268901) B9268901
theorem B4119511 : Blo 2169435 4119511 := bstep (se 1 (by rfl) ⟨3089633, by rfl⟩ : syracuseStep 4119511 = 6179267) B6179267
theorem B5492681 : Blo 2169435 5492681 := bstep (se 2 (by rfl) ⟨2059755, by rfl⟩ : syracuseStep 5492681 = 4119511) B4119511
theorem B3661787 : Blo 2169435 3661787 := bstep (se 1 (by rfl) ⟨2746340, by rfl⟩ : syracuseStep 3661787 = 5492681) B5492681
theorem B2441191 : Blo 2169435 2441191 := bstep (se 1 (by rfl) ⟨1830893, by rfl⟩ : syracuseStep 2441191 = 3661787) B3661787
theorem B3254921 : Blo 2169435 3254921 := bstep (se 2 (by rfl) ⟨1220595, by rfl⟩ : syracuseStep 3254921 = 2441191) B2441191
theorem B2169947 : Blo 2169435 2169947 := bstep (se 1 (by rfl) ⟨1627460, by rfl⟩ : syracuseStep 2169947 = 3254921) B3254921
theorem B10985381 : Blo 2169435 10985381 := bbase (se 4 (by rfl) ⟨1029879, by rfl⟩ : syracuseStep 10985381 = 2059759) (by norm_num)
theorem B7323587 : Blo 2169435 7323587 := bstep (se 1 (by rfl) ⟨5492690, by rfl⟩ : syracuseStep 7323587 = 10985381) B10985381
theorem B4882391 : Blo 2169435 4882391 := bstep (se 1 (by rfl) ⟨3661793, by rfl⟩ : syracuseStep 4882391 = 7323587) B7323587
theorem B3254927 : Blo 2169435 3254927 := bstep (se 1 (by rfl) ⟨2441195, by rfl⟩ : syracuseStep 3254927 = 4882391) B4882391
theorem B2169951 : Blo 2169435 2169951 := bstep (se 1 (by rfl) ⟨1627463, by rfl⟩ : syracuseStep 2169951 = 3254927) B3254927
theorem B3254933 : Blo 2169435 3254933 := bbase (se 6 (by rfl) ⟨76287, by rfl⟩ : syracuseStep 3254933 = 152575) (by norm_num)
theorem B2169955 : Blo 2169435 2169955 := bstep (se 1 (by rfl) ⟨1627466, by rfl⟩ : syracuseStep 2169955 = 3254933) B3254933
theorem B5865509 : Blo 2169435 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B3910339 : Blo 2169435 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B20855141 : Blo 2169435 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B13903427 : Blo 2169435 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B9268951 : Blo 2169435 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B12358601 : Blo 2169435 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B8239067 : Blo 2169435 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B5492711 : Blo 2169435 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B3661807 : Blo 2169435 3661807 := bstep (se 1 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 3661807 = 5492711) B5492711
theorem B4882409 : Blo 2169435 4882409 := bstep (se 2 (by rfl) ⟨1830903, by rfl⟩ : syracuseStep 4882409 = 3661807) B3661807
theorem B3254939 : Blo 2169435 3254939 := bstep (se 1 (by rfl) ⟨2441204, by rfl⟩ : syracuseStep 3254939 = 4882409) B4882409
theorem B2169959 : Blo 2169435 2169959 := bstep (se 1 (by rfl) ⟨1627469, by rfl⟩ : syracuseStep 2169959 = 3254939) B3254939
theorem B2441209 : Blo 2169435 2441209 := bbase (se 2 (by rfl) ⟨915453, by rfl⟩ : syracuseStep 2441209 = 1830907) (by norm_num)
theorem B3254945 : Blo 2169435 3254945 := bstep (se 2 (by rfl) ⟨1220604, by rfl⟩ : syracuseStep 3254945 = 2441209) B2441209
theorem B2169963 : Blo 2169435 2169963 := bstep (se 1 (by rfl) ⟨1627472, by rfl⟩ : syracuseStep 2169963 = 3254945) B3254945
theorem B11731061 : Blo 2169435 11731061 := bbase (se 5 (by rfl) ⟨549893, by rfl⟩ : syracuseStep 11731061 = 1099787) (by norm_num)
theorem B7820707 : Blo 2169435 7820707 := bstep (se 1 (by rfl) ⟨5865530, by rfl⟩ : syracuseStep 7820707 = 11731061) B11731061
theorem B10427609 : Blo 2169435 10427609 := bstep (se 2 (by rfl) ⟨3910353, by rfl⟩ : syracuseStep 10427609 = 7820707) B7820707
theorem B6951739 : Blo 2169435 6951739 := bstep (se 1 (by rfl) ⟨5213804, by rfl⟩ : syracuseStep 6951739 = 10427609) B10427609
theorem B9268985 : Blo 2169435 9268985 := bstep (se 2 (by rfl) ⟨3475869, by rfl⟩ : syracuseStep 9268985 = 6951739) B6951739
theorem B6179323 : Blo 2169435 6179323 := bstep (se 1 (by rfl) ⟨4634492, by rfl⟩ : syracuseStep 6179323 = 9268985) B9268985
theorem B8239097 : Blo 2169435 8239097 := bstep (se 2 (by rfl) ⟨3089661, by rfl⟩ : syracuseStep 8239097 = 6179323) B6179323
theorem B5492731 : Blo 2169435 5492731 := bstep (se 1 (by rfl) ⟨4119548, by rfl⟩ : syracuseStep 5492731 = 8239097) B8239097
theorem B7323641 : Blo 2169435 7323641 := bstep (se 2 (by rfl) ⟨2746365, by rfl⟩ : syracuseStep 7323641 = 5492731) B5492731
theorem B4882427 : Blo 2169435 4882427 := bstep (se 1 (by rfl) ⟨3661820, by rfl⟩ : syracuseStep 4882427 = 7323641) B7323641
theorem B3254951 : Blo 2169435 3254951 := bstep (se 1 (by rfl) ⟨2441213, by rfl⟩ : syracuseStep 3254951 = 4882427) B4882427
theorem B2169967 : Blo 2169435 2169967 := bstep (se 1 (by rfl) ⟨1627475, by rfl⟩ : syracuseStep 2169967 = 3254951) B3254951
theorem B3254957 : Blo 2169435 3254957 := bbase (se 3 (by rfl) ⟨610304, by rfl⟩ : syracuseStep 3254957 = 1220609) (by norm_num)
theorem B2169971 : Blo 2169435 2169971 := bstep (se 1 (by rfl) ⟨1627478, by rfl⟩ : syracuseStep 2169971 = 3254957) B3254957
theorem B4882445 : Blo 2169435 4882445 := bbase (se 3 (by rfl) ⟨915458, by rfl⟩ : syracuseStep 4882445 = 1830917) (by norm_num)
theorem B3254963 : Blo 2169435 3254963 := bstep (se 1 (by rfl) ⟨2441222, by rfl⟩ : syracuseStep 3254963 = 4882445) B4882445
theorem B2169975 : Blo 2169435 2169975 := bstep (se 1 (by rfl) ⟨1627481, by rfl⟩ : syracuseStep 2169975 = 3254963) B3254963
theorem B2746381 : Blo 2169435 2746381 := bbase (se 3 (by rfl) ⟨514946, by rfl⟩ : syracuseStep 2746381 = 1029893) (by norm_num)
theorem B3661841 : Blo 2169435 3661841 := bstep (se 2 (by rfl) ⟨1373190, by rfl⟩ : syracuseStep 3661841 = 2746381) B2746381
theorem B2441227 : Blo 2169435 2441227 := bstep (se 1 (by rfl) ⟨1830920, by rfl⟩ : syracuseStep 2441227 = 3661841) B3661841
theorem B3254969 : Blo 2169435 3254969 := bstep (se 2 (by rfl) ⟨1220613, by rfl⟩ : syracuseStep 3254969 = 2441227) B2441227
theorem B2169979 : Blo 2169435 2169979 := bstep (se 1 (by rfl) ⟨1627484, by rfl⟩ : syracuseStep 2169979 = 3254969) B3254969
theorem B19796309 : Blo 2169435 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B13197539 : Blo 2169435 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B35193437 : Blo 2169435 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B23462291 : Blo 2169435 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B15641527 : Blo 2169435 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B20855369 : Blo 2169435 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B13903579 : Blo 2169435 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B18538105 : Blo 2169435 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B24717473 : Blo 2169435 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B16478315 : Blo 2169435 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B10985543 : Blo 2169435 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B7323695 : Blo 2169435 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B4882463 : Blo 2169435 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B3254975 : Blo 2169435 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B2169983 : Blo 2169435 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B3254981 : Blo 2169435 3254981 := bbase (se 4 (by rfl) ⟨305154, by rfl⟩ : syracuseStep 3254981 = 610309) (by norm_num)
theorem B2169987 : Blo 2169435 2169987 := bstep (se 1 (by rfl) ⟨1627490, by rfl⟩ : syracuseStep 2169987 = 3254981) B3254981
theorem B3661861 : Blo 2169435 3661861 := bbase (se 4 (by rfl) ⟨343299, by rfl⟩ : syracuseStep 3661861 = 686599) (by norm_num)
theorem B4882481 : Blo 2169435 4882481 := bstep (se 2 (by rfl) ⟨1830930, by rfl⟩ : syracuseStep 4882481 = 3661861) B3661861
theorem B3254987 : Blo 2169435 3254987 := bstep (se 1 (by rfl) ⟨2441240, by rfl⟩ : syracuseStep 3254987 = 4882481) B4882481
theorem B2169991 : Blo 2169435 2169991 := bstep (se 1 (by rfl) ⟨1627493, by rfl⟩ : syracuseStep 2169991 = 3254987) B3254987
theorem B2441245 : Blo 2169435 2441245 := bbase (se 3 (by rfl) ⟨457733, by rfl⟩ : syracuseStep 2441245 = 915467) (by norm_num)
theorem B3254993 : Blo 2169435 3254993 := bstep (se 2 (by rfl) ⟨1220622, by rfl⟩ : syracuseStep 3254993 = 2441245) B2441245
theorem B2169995 : Blo 2169435 2169995 := bstep (se 1 (by rfl) ⟨1627496, by rfl⟩ : syracuseStep 2169995 = 3254993) B3254993
theorem B7323749 : Blo 2169435 7323749 := bbase (se 4 (by rfl) ⟨686601, by rfl⟩ : syracuseStep 7323749 = 1373203) (by norm_num)
theorem B4882499 : Blo 2169435 4882499 := bstep (se 1 (by rfl) ⟨3661874, by rfl⟩ : syracuseStep 4882499 = 7323749) B7323749
theorem B3254999 : Blo 2169435 3254999 := bstep (se 1 (by rfl) ⟨2441249, by rfl⟩ : syracuseStep 3254999 = 4882499) B4882499
theorem B2169999 : Blo 2169435 2169999 := bstep (se 1 (by rfl) ⟨1627499, by rfl⟩ : syracuseStep 2169999 = 3254999) B3254999
theorem B3255005 : Blo 2169435 3255005 := bbase (se 3 (by rfl) ⟨610313, by rfl⟩ : syracuseStep 3255005 = 1220627) (by norm_num)
theorem B2170003 : Blo 2169435 2170003 := bstep (se 1 (by rfl) ⟨1627502, by rfl⟩ : syracuseStep 2170003 = 3255005) B3255005
theorem B4882517 : Blo 2169435 4882517 := bbase (se 8 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 4882517 = 57217) (by norm_num)
theorem B3255011 : Blo 2169435 3255011 := bstep (se 1 (by rfl) ⟨2441258, by rfl⟩ : syracuseStep 3255011 = 4882517) B4882517
theorem B2170007 : Blo 2169435 2170007 := bstep (se 1 (by rfl) ⟨1627505, by rfl⟩ : syracuseStep 2170007 = 3255011) B3255011
theorem B3299429 : Blo 2169435 3299429 := bbase (se 4 (by rfl) ⟨309321, by rfl⟩ : syracuseStep 3299429 = 618643) (by norm_num)
theorem B2199619 : Blo 2169435 2199619 := bstep (se 1 (by rfl) ⟨1649714, by rfl⟩ : syracuseStep 2199619 = 3299429) B3299429
theorem B11731301 : Blo 2169435 11731301 := bstep (se 4 (by rfl) ⟨1099809, by rfl⟩ : syracuseStep 11731301 = 2199619) B2199619
theorem B7820867 : Blo 2169435 7820867 := bstep (se 1 (by rfl) ⟨5865650, by rfl⟩ : syracuseStep 7820867 = 11731301) B11731301
theorem B5213911 : Blo 2169435 5213911 := bstep (se 1 (by rfl) ⟨3910433, by rfl⟩ : syracuseStep 5213911 = 7820867) B7820867
theorem B6951881 : Blo 2169435 6951881 := bstep (se 2 (by rfl) ⟨2606955, by rfl⟩ : syracuseStep 6951881 = 5213911) B5213911
theorem B4634587 : Blo 2169435 4634587 := bstep (se 1 (by rfl) ⟨3475940, by rfl⟩ : syracuseStep 4634587 = 6951881) B6951881
theorem B6179449 : Blo 2169435 6179449 := bstep (se 2 (by rfl) ⟨2317293, by rfl⟩ : syracuseStep 6179449 = 4634587) B4634587
theorem B8239265 : Blo 2169435 8239265 := bstep (se 2 (by rfl) ⟨3089724, by rfl⟩ : syracuseStep 8239265 = 6179449) B6179449
theorem B5492843 : Blo 2169435 5492843 := bstep (se 1 (by rfl) ⟨4119632, by rfl⟩ : syracuseStep 5492843 = 8239265) B8239265
theorem B3661895 : Blo 2169435 3661895 := bstep (se 1 (by rfl) ⟨2746421, by rfl⟩ : syracuseStep 3661895 = 5492843) B5492843
theorem B2441263 : Blo 2169435 2441263 := bstep (se 1 (by rfl) ⟨1830947, by rfl⟩ : syracuseStep 2441263 = 3661895) B3661895
theorem B3255017 : Blo 2169435 3255017 := bstep (se 2 (by rfl) ⟨1220631, by rfl⟩ : syracuseStep 3255017 = 2441263) B2441263
theorem B2170011 : Blo 2169435 2170011 := bstep (se 1 (by rfl) ⟨1627508, by rfl⟩ : syracuseStep 2170011 = 3255017) B3255017
theorem B3131885 : Blo 2169435 3131885 := bbase (se 3 (by rfl) ⟨587228, by rfl⟩ : syracuseStep 3131885 = 1174457) (by norm_num)
theorem B8351693 : Blo 2169435 8351693 := bstep (se 3 (by rfl) ⟨1565942, by rfl⟩ : syracuseStep 8351693 = 3131885) B3131885
theorem B5567795 : Blo 2169435 5567795 := bstep (se 1 (by rfl) ⟨4175846, by rfl⟩ : syracuseStep 5567795 = 8351693) B8351693
theorem B3711863 : Blo 2169435 3711863 := bstep (se 1 (by rfl) ⟨2783897, by rfl⟩ : syracuseStep 3711863 = 5567795) B5567795
theorem B9898301 : Blo 2169435 9898301 := bstep (se 3 (by rfl) ⟨1855931, by rfl⟩ : syracuseStep 9898301 = 3711863) B3711863
theorem B26395469 : Blo 2169435 26395469 := bstep (se 3 (by rfl) ⟨4949150, by rfl⟩ : syracuseStep 26395469 = 9898301) B9898301
theorem B17596979 : Blo 2169435 17596979 := bstep (se 1 (by rfl) ⟨13197734, by rfl⟩ : syracuseStep 17596979 = 26395469) B26395469
theorem B11731319 : Blo 2169435 11731319 := bstep (se 1 (by rfl) ⟨8798489, by rfl⟩ : syracuseStep 11731319 = 17596979) B17596979
theorem B7820879 : Blo 2169435 7820879 := bstep (se 1 (by rfl) ⟨5865659, by rfl⟩ : syracuseStep 7820879 = 11731319) B11731319
theorem B20855677 : Blo 2169435 20855677 := bstep (se 3 (by rfl) ⟨3910439, by rfl⟩ : syracuseStep 20855677 = 7820879) B7820879
theorem B27807569 : Blo 2169435 27807569 := bstep (se 2 (by rfl) ⟨10427838, by rfl⟩ : syracuseStep 27807569 = 20855677) B20855677
theorem B18538379 : Blo 2169435 18538379 := bstep (se 1 (by rfl) ⟨13903784, by rfl⟩ : syracuseStep 18538379 = 27807569) B27807569
theorem B12358919 : Blo 2169435 12358919 := bstep (se 1 (by rfl) ⟨9269189, by rfl⟩ : syracuseStep 12358919 = 18538379) B18538379
theorem B8239279 : Blo 2169435 8239279 := bstep (se 1 (by rfl) ⟨6179459, by rfl⟩ : syracuseStep 8239279 = 12358919) B12358919
theorem B10985705 : Blo 2169435 10985705 := bstep (se 2 (by rfl) ⟨4119639, by rfl⟩ : syracuseStep 10985705 = 8239279) B8239279
theorem B7323803 : Blo 2169435 7323803 := bstep (se 1 (by rfl) ⟨5492852, by rfl⟩ : syracuseStep 7323803 = 10985705) B10985705
theorem B4882535 : Blo 2169435 4882535 := bstep (se 1 (by rfl) ⟨3661901, by rfl⟩ : syracuseStep 4882535 = 7323803) B7323803
theorem B3255023 : Blo 2169435 3255023 := bstep (se 1 (by rfl) ⟨2441267, by rfl⟩ : syracuseStep 3255023 = 4882535) B4882535
theorem B2170015 : Blo 2169435 2170015 := bstep (se 1 (by rfl) ⟨1627511, by rfl⟩ : syracuseStep 2170015 = 3255023) B3255023
theorem B3255029 : Blo 2169435 3255029 := bbase (se 5 (by rfl) ⟨152579, by rfl⟩ : syracuseStep 3255029 = 305159) (by norm_num)
theorem B2170019 : Blo 2169435 2170019 := bstep (se 1 (by rfl) ⟨1627514, by rfl⟩ : syracuseStep 2170019 = 3255029) B3255029
theorem B14847509 : Blo 2169435 14847509 := bbase (se 6 (by rfl) ⟨347988, by rfl⟩ : syracuseStep 14847509 = 695977) (by norm_num)
theorem B39593357 : Blo 2169435 39593357 := bstep (se 3 (by rfl) ⟨7423754, by rfl⟩ : syracuseStep 39593357 = 14847509) B14847509
theorem B26395571 : Blo 2169435 26395571 := bstep (se 1 (by rfl) ⟨19796678, by rfl⟩ : syracuseStep 26395571 = 39593357) B39593357
theorem B17597047 : Blo 2169435 17597047 := bstep (se 1 (by rfl) ⟨13197785, by rfl⟩ : syracuseStep 17597047 = 26395571) B26395571
theorem B23462729 : Blo 2169435 23462729 := bstep (se 2 (by rfl) ⟨8798523, by rfl⟩ : syracuseStep 23462729 = 17597047) B17597047
theorem B15641819 : Blo 2169435 15641819 := bstep (se 1 (by rfl) ⟨11731364, by rfl⟩ : syracuseStep 15641819 = 23462729) B23462729
theorem B10427879 : Blo 2169435 10427879 := bstep (se 1 (by rfl) ⟨7820909, by rfl⟩ : syracuseStep 10427879 = 15641819) B15641819
theorem B6951919 : Blo 2169435 6951919 := bstep (se 1 (by rfl) ⟨5213939, by rfl⟩ : syracuseStep 6951919 = 10427879) B10427879
theorem B9269225 : Blo 2169435 9269225 := bstep (se 2 (by rfl) ⟨3475959, by rfl⟩ : syracuseStep 9269225 = 6951919) B6951919
theorem B6179483 : Blo 2169435 6179483 := bstep (se 1 (by rfl) ⟨4634612, by rfl⟩ : syracuseStep 6179483 = 9269225) B9269225
theorem B4119655 : Blo 2169435 4119655 := bstep (se 1 (by rfl) ⟨3089741, by rfl⟩ : syracuseStep 4119655 = 6179483) B6179483
theorem B5492873 : Blo 2169435 5492873 := bstep (se 2 (by rfl) ⟨2059827, by rfl⟩ : syracuseStep 5492873 = 4119655) B4119655
theorem B3661915 : Blo 2169435 3661915 := bstep (se 1 (by rfl) ⟨2746436, by rfl⟩ : syracuseStep 3661915 = 5492873) B5492873
theorem B4882553 : Blo 2169435 4882553 := bstep (se 2 (by rfl) ⟨1830957, by rfl⟩ : syracuseStep 4882553 = 3661915) B3661915
theorem B3255035 : Blo 2169435 3255035 := bstep (se 1 (by rfl) ⟨2441276, by rfl⟩ : syracuseStep 3255035 = 4882553) B4882553
theorem B2170023 : Blo 2169435 2170023 := bstep (se 1 (by rfl) ⟨1627517, by rfl⟩ : syracuseStep 2170023 = 3255035) B3255035
theorem B2441281 : Blo 2169435 2441281 := bbase (se 2 (by rfl) ⟨915480, by rfl⟩ : syracuseStep 2441281 = 1830961) (by norm_num)
theorem B3255041 : Blo 2169435 3255041 := bstep (se 2 (by rfl) ⟨1220640, by rfl⟩ : syracuseStep 3255041 = 2441281) B2441281
theorem B2170027 : Blo 2169435 2170027 := bstep (se 1 (by rfl) ⟨1627520, by rfl⟩ : syracuseStep 2170027 = 3255041) B3255041
theorem B5492893 : Blo 2169435 5492893 := bbase (se 3 (by rfl) ⟨1029917, by rfl⟩ : syracuseStep 5492893 = 2059835) (by norm_num)
theorem B7323857 : Blo 2169435 7323857 := bstep (se 2 (by rfl) ⟨2746446, by rfl⟩ : syracuseStep 7323857 = 5492893) B5492893
theorem B4882571 : Blo 2169435 4882571 := bstep (se 1 (by rfl) ⟨3661928, by rfl⟩ : syracuseStep 4882571 = 7323857) B7323857
theorem B3255047 : Blo 2169435 3255047 := bstep (se 1 (by rfl) ⟨2441285, by rfl⟩ : syracuseStep 3255047 = 4882571) B4882571
theorem B2170031 : Blo 2169435 2170031 := bstep (se 1 (by rfl) ⟨1627523, by rfl⟩ : syracuseStep 2170031 = 3255047) B3255047
theorem B3255053 : Blo 2169435 3255053 := bbase (se 3 (by rfl) ⟨610322, by rfl⟩ : syracuseStep 3255053 = 1220645) (by norm_num)
theorem B2170035 : Blo 2169435 2170035 := bstep (se 1 (by rfl) ⟨1627526, by rfl⟩ : syracuseStep 2170035 = 3255053) B3255053
theorem B4882589 : Blo 2169435 4882589 := bbase (se 3 (by rfl) ⟨915485, by rfl⟩ : syracuseStep 4882589 = 1830971) (by norm_num)
theorem B3255059 : Blo 2169435 3255059 := bstep (se 1 (by rfl) ⟨2441294, by rfl⟩ : syracuseStep 3255059 = 4882589) B4882589
theorem B2170039 : Blo 2169435 2170039 := bstep (se 1 (by rfl) ⟨1627529, by rfl⟩ : syracuseStep 2170039 = 3255059) B3255059
theorem B3661949 : Blo 2169435 3661949 := bbase (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) (by norm_num)
theorem B2441299 : Blo 2169435 2441299 := bstep (se 1 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 2441299 = 3661949) B3661949
theorem B3255065 : Blo 2169435 3255065 := bstep (se 2 (by rfl) ⟨1220649, by rfl⟩ : syracuseStep 3255065 = 2441299) B2441299
theorem B2170043 : Blo 2169435 2170043 := bstep (se 1 (by rfl) ⟨1627532, by rfl⟩ : syracuseStep 2170043 = 3255065) B3255065
theorem B9395797 : Blo 2169435 9395797 := bbase (se 8 (by rfl) ⟨55053, by rfl⟩ : syracuseStep 9395797 = 110107) (by norm_num)
theorem B12527729 : Blo 2169435 12527729 := bstep (se 2 (by rfl) ⟨4697898, by rfl⟩ : syracuseStep 12527729 = 9395797) B9395797
theorem B8351819 : Blo 2169435 8351819 := bstep (se 1 (by rfl) ⟨6263864, by rfl⟩ : syracuseStep 8351819 = 12527729) B12527729
theorem B5567879 : Blo 2169435 5567879 := bstep (se 1 (by rfl) ⟨4175909, by rfl⟩ : syracuseStep 5567879 = 8351819) B8351819
theorem B3711919 : Blo 2169435 3711919 := bstep (se 1 (by rfl) ⟨2783939, by rfl⟩ : syracuseStep 3711919 = 5567879) B5567879
theorem B4949225 : Blo 2169435 4949225 := bstep (se 2 (by rfl) ⟨1855959, by rfl⟩ : syracuseStep 4949225 = 3711919) B3711919
theorem B3299483 : Blo 2169435 3299483 := bstep (se 1 (by rfl) ⟨2474612, by rfl⟩ : syracuseStep 3299483 = 4949225) B4949225
theorem B2199655 : Blo 2169435 2199655 := bstep (se 1 (by rfl) ⟨1649741, by rfl⟩ : syracuseStep 2199655 = 3299483) B3299483
theorem B11731493 : Blo 2169435 11731493 := bstep (se 4 (by rfl) ⟨1099827, by rfl⟩ : syracuseStep 11731493 = 2199655) B2199655
theorem B7820995 : Blo 2169435 7820995 := bstep (se 1 (by rfl) ⟨5865746, by rfl⟩ : syracuseStep 7820995 = 11731493) B11731493
theorem B10427993 : Blo 2169435 10427993 := bstep (se 2 (by rfl) ⟨3910497, by rfl⟩ : syracuseStep 10427993 = 7820995) B7820995
theorem B6951995 : Blo 2169435 6951995 := bstep (se 1 (by rfl) ⟨5213996, by rfl⟩ : syracuseStep 6951995 = 10427993) B10427993
theorem B4634663 : Blo 2169435 4634663 := bstep (se 1 (by rfl) ⟨3475997, by rfl⟩ : syracuseStep 4634663 = 6951995) B6951995
theorem B12359101 : Blo 2169435 12359101 := bstep (se 3 (by rfl) ⟨2317331, by rfl⟩ : syracuseStep 12359101 = 4634663) B4634663
theorem B16478801 : Blo 2169435 16478801 := bstep (se 2 (by rfl) ⟨6179550, by rfl⟩ : syracuseStep 16478801 = 12359101) B12359101
theorem B10985867 : Blo 2169435 10985867 := bstep (se 1 (by rfl) ⟨8239400, by rfl⟩ : syracuseStep 10985867 = 16478801) B16478801
theorem B7323911 : Blo 2169435 7323911 := bstep (se 1 (by rfl) ⟨5492933, by rfl⟩ : syracuseStep 7323911 = 10985867) B10985867
theorem B4882607 : Blo 2169435 4882607 := bstep (se 1 (by rfl) ⟨3661955, by rfl⟩ : syracuseStep 4882607 = 7323911) B7323911
theorem B3255071 : Blo 2169435 3255071 := bstep (se 1 (by rfl) ⟨2441303, by rfl⟩ : syracuseStep 3255071 = 4882607) B4882607
theorem B2170047 : Blo 2169435 2170047 := bstep (se 1 (by rfl) ⟨1627535, by rfl⟩ : syracuseStep 2170047 = 3255071) B3255071
theorem B3255077 : Blo 2169435 3255077 := bbase (se 4 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 3255077 = 610327) (by norm_num)
theorem B2170051 : Blo 2169435 2170051 := bstep (se 1 (by rfl) ⟨1627538, by rfl⟩ : syracuseStep 2170051 = 3255077) B3255077
theorem B2746477 : Blo 2169435 2746477 := bbase (se 3 (by rfl) ⟨514964, by rfl⟩ : syracuseStep 2746477 = 1029929) (by norm_num)
theorem B3661969 : Blo 2169435 3661969 := bstep (se 2 (by rfl) ⟨1373238, by rfl⟩ : syracuseStep 3661969 = 2746477) B2746477
theorem B4882625 : Blo 2169435 4882625 := bstep (se 2 (by rfl) ⟨1830984, by rfl⟩ : syracuseStep 4882625 = 3661969) B3661969
theorem B3255083 : Blo 2169435 3255083 := bstep (se 1 (by rfl) ⟨2441312, by rfl⟩ : syracuseStep 3255083 = 4882625) B4882625
theorem B2170055 : Blo 2169435 2170055 := bstep (se 1 (by rfl) ⟨1627541, by rfl⟩ : syracuseStep 2170055 = 3255083) B3255083
theorem B2441317 : Blo 2169435 2441317 := bbase (se 4 (by rfl) ⟨228873, by rfl⟩ : syracuseStep 2441317 = 457747) (by norm_num)
theorem B3255089 : Blo 2169435 3255089 := bstep (se 2 (by rfl) ⟨1220658, by rfl⟩ : syracuseStep 3255089 = 2441317) B2441317
theorem B2170059 : Blo 2169435 2170059 := bstep (se 1 (by rfl) ⟨1627544, by rfl⟩ : syracuseStep 2170059 = 3255089) B3255089
theorem B2317349 : Blo 2169435 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B6179597 : Blo 2169435 6179597 := bstep (se 3 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 6179597 = 2317349) B2317349
theorem B4119731 : Blo 2169435 4119731 := bstep (se 1 (by rfl) ⟨3089798, by rfl⟩ : syracuseStep 4119731 = 6179597) B6179597
theorem B2746487 : Blo 2169435 2746487 := bstep (se 1 (by rfl) ⟨2059865, by rfl⟩ : syracuseStep 2746487 = 4119731) B4119731
theorem B7323965 : Blo 2169435 7323965 := bstep (se 3 (by rfl) ⟨1373243, by rfl⟩ : syracuseStep 7323965 = 2746487) B2746487
theorem B4882643 : Blo 2169435 4882643 := bstep (se 1 (by rfl) ⟨3661982, by rfl⟩ : syracuseStep 4882643 = 7323965) B7323965
theorem B3255095 : Blo 2169435 3255095 := bstep (se 1 (by rfl) ⟨2441321, by rfl⟩ : syracuseStep 3255095 = 4882643) B4882643
theorem B2170063 : Blo 2169435 2170063 := bstep (se 1 (by rfl) ⟨1627547, by rfl⟩ : syracuseStep 2170063 = 3255095) B3255095
theorem B3255101 : Blo 2169435 3255101 := bbase (se 3 (by rfl) ⟨610331, by rfl⟩ : syracuseStep 3255101 = 1220663) (by norm_num)
theorem B2170067 : Blo 2169435 2170067 := bstep (se 1 (by rfl) ⟨1627550, by rfl⟩ : syracuseStep 2170067 = 3255101) B3255101
theorem B4882661 : Blo 2169435 4882661 := bbase (se 4 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 4882661 = 915499) (by norm_num)
theorem B3255107 : Blo 2169435 3255107 := bstep (se 1 (by rfl) ⟨2441330, by rfl⟩ : syracuseStep 3255107 = 4882661) B4882661
theorem B2170071 : Blo 2169435 2170071 := bstep (se 1 (by rfl) ⟨1627553, by rfl⟩ : syracuseStep 2170071 = 3255107) B3255107
theorem B5493005 : Blo 2169435 5493005 := bbase (se 3 (by rfl) ⟨1029938, by rfl⟩ : syracuseStep 5493005 = 2059877) (by norm_num)
theorem B3662003 : Blo 2169435 3662003 := bstep (se 1 (by rfl) ⟨2746502, by rfl⟩ : syracuseStep 3662003 = 5493005) B5493005
theorem B2441335 : Blo 2169435 2441335 := bstep (se 1 (by rfl) ⟨1831001, by rfl⟩ : syracuseStep 2441335 = 3662003) B3662003
theorem B3255113 : Blo 2169435 3255113 := bstep (se 2 (by rfl) ⟨1220667, by rfl⟩ : syracuseStep 3255113 = 2441335) B2441335
theorem B2170075 : Blo 2169435 2170075 := bstep (se 1 (by rfl) ⟨1627556, by rfl⟩ : syracuseStep 2170075 = 3255113) B3255113
theorem B3089821 : Blo 2169435 3089821 := bbase (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) (by norm_num)
theorem B4119761 : Blo 2169435 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B10986029 : Blo 2169435 10986029 := bstep (se 3 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 10986029 = 4119761) B4119761
theorem B7324019 : Blo 2169435 7324019 := bstep (se 1 (by rfl) ⟨5493014, by rfl⟩ : syracuseStep 7324019 = 10986029) B10986029
theorem B4882679 : Blo 2169435 4882679 := bstep (se 1 (by rfl) ⟨3662009, by rfl⟩ : syracuseStep 4882679 = 7324019) B7324019
theorem B3255119 : Blo 2169435 3255119 := bstep (se 1 (by rfl) ⟨2441339, by rfl⟩ : syracuseStep 3255119 = 4882679) B4882679
theorem B2170079 : Blo 2169435 2170079 := bstep (se 1 (by rfl) ⟨1627559, by rfl⟩ : syracuseStep 2170079 = 3255119) B3255119
theorem B3255125 : Blo 2169435 3255125 := bbase (se 9 (by rfl) ⟨9536, by rfl⟩ : syracuseStep 3255125 = 19073) (by norm_num)
theorem B2170083 : Blo 2169435 2170083 := bstep (se 1 (by rfl) ⟨1627562, by rfl⟩ : syracuseStep 2170083 = 3255125) B3255125
theorem B4634749 : Blo 2169435 4634749 := bbase (se 3 (by rfl) ⟨869015, by rfl⟩ : syracuseStep 4634749 = 1738031) (by norm_num)
theorem B6179665 : Blo 2169435 6179665 := bstep (se 2 (by rfl) ⟨2317374, by rfl⟩ : syracuseStep 6179665 = 4634749) B4634749
theorem B8239553 : Blo 2169435 8239553 := bstep (se 2 (by rfl) ⟨3089832, by rfl⟩ : syracuseStep 8239553 = 6179665) B6179665
theorem B5493035 : Blo 2169435 5493035 := bstep (se 1 (by rfl) ⟨4119776, by rfl⟩ : syracuseStep 5493035 = 8239553) B8239553
theorem B3662023 : Blo 2169435 3662023 := bstep (se 1 (by rfl) ⟨2746517, by rfl⟩ : syracuseStep 3662023 = 5493035) B5493035
theorem B4882697 : Blo 2169435 4882697 := bstep (se 2 (by rfl) ⟨1831011, by rfl⟩ : syracuseStep 4882697 = 3662023) B3662023
theorem B3255131 : Blo 2169435 3255131 := bstep (se 1 (by rfl) ⟨2441348, by rfl⟩ : syracuseStep 3255131 = 4882697) B4882697
theorem B2170087 : Blo 2169435 2170087 := bstep (se 1 (by rfl) ⟨1627565, by rfl⟩ : syracuseStep 2170087 = 3255131) B3255131
theorem B2441353 : Blo 2169435 2441353 := bbase (se 2 (by rfl) ⟨915507, by rfl⟩ : syracuseStep 2441353 = 1831015) (by norm_num)
theorem B3255137 : Blo 2169435 3255137 := bstep (se 2 (by rfl) ⟨1220676, by rfl⟩ : syracuseStep 3255137 = 2441353) B2441353
theorem B2170091 : Blo 2169435 2170091 := bstep (se 1 (by rfl) ⟨1627568, by rfl⟩ : syracuseStep 2170091 = 3255137) B3255137
theorem B32144149 : Blo 2169435 32144149 := bbase (se 6 (by rfl) ⟨753378, by rfl⟩ : syracuseStep 32144149 = 1506757) (by norm_num)
theorem B42858865 : Blo 2169435 42858865 := bstep (se 2 (by rfl) ⟨16072074, by rfl⟩ : syracuseStep 42858865 = 32144149) B32144149
theorem B228580613 : Blo 2169435 228580613 := bstep (se 4 (by rfl) ⟨21429432, by rfl⟩ : syracuseStep 228580613 = 42858865) B42858865
theorem B152387075 : Blo 2169435 152387075 := bstep (se 1 (by rfl) ⟨114290306, by rfl⟩ : syracuseStep 152387075 = 228580613) B228580613
theorem B101591383 : Blo 2169435 101591383 := bstep (se 1 (by rfl) ⟨76193537, by rfl⟩ : syracuseStep 101591383 = 152387075) B152387075
theorem B135455177 : Blo 2169435 135455177 := bstep (se 2 (by rfl) ⟨50795691, by rfl⟩ : syracuseStep 135455177 = 101591383) B101591383
theorem B361213805 : Blo 2169435 361213805 := bstep (se 3 (by rfl) ⟨67727588, by rfl⟩ : syracuseStep 361213805 = 135455177) B135455177
theorem B240809203 : Blo 2169435 240809203 := bstep (se 1 (by rfl) ⟨180606902, by rfl⟩ : syracuseStep 240809203 = 361213805) B361213805
theorem B321078937 : Blo 2169435 321078937 := bstep (se 2 (by rfl) ⟨120404601, by rfl⟩ : syracuseStep 321078937 = 240809203) B240809203
theorem B428105249 : Blo 2169435 428105249 := bstep (se 2 (by rfl) ⟨160539468, by rfl⟩ : syracuseStep 428105249 = 321078937) B321078937
theorem B285403499 : Blo 2169435 285403499 := bstep (se 1 (by rfl) ⟨214052624, by rfl⟩ : syracuseStep 285403499 = 428105249) B428105249
theorem B190268999 : Blo 2169435 190268999 := bstep (se 1 (by rfl) ⟨142701749, by rfl⟩ : syracuseStep 190268999 = 285403499) B285403499
theorem B126845999 : Blo 2169435 126845999 := bstep (se 1 (by rfl) ⟨95134499, by rfl⟩ : syracuseStep 126845999 = 190268999) B190268999
theorem B84563999 : Blo 2169435 84563999 := bstep (se 1 (by rfl) ⟨63422999, by rfl⟩ : syracuseStep 84563999 = 126845999) B126845999
theorem B56375999 : Blo 2169435 56375999 := bstep (se 1 (by rfl) ⟨42281999, by rfl⟩ : syracuseStep 56375999 = 84563999) B84563999
theorem B37583999 : Blo 2169435 37583999 := bstep (se 1 (by rfl) ⟨28187999, by rfl⟩ : syracuseStep 37583999 = 56375999) B56375999
theorem B25055999 : Blo 2169435 25055999 := bstep (se 1 (by rfl) ⟨18791999, by rfl⟩ : syracuseStep 25055999 = 37583999) B37583999
theorem B16703999 : Blo 2169435 16703999 := bstep (se 1 (by rfl) ⟨12527999, by rfl⟩ : syracuseStep 16703999 = 25055999) B25055999
theorem B11135999 : Blo 2169435 11135999 := bstep (se 1 (by rfl) ⟨8351999, by rfl⟩ : syracuseStep 11135999 = 16703999) B16703999
theorem B29695997 : Blo 2169435 29695997 := bstep (se 3 (by rfl) ⟨5567999, by rfl⟩ : syracuseStep 29695997 = 11135999) B11135999
theorem B79189325 : Blo 2169435 79189325 := bstep (se 3 (by rfl) ⟨14847998, by rfl⟩ : syracuseStep 79189325 = 29695997) B29695997
theorem B52792883 : Blo 2169435 52792883 := bstep (se 1 (by rfl) ⟨39594662, by rfl⟩ : syracuseStep 52792883 = 79189325) B79189325
theorem B35195255 : Blo 2169435 35195255 := bstep (se 1 (by rfl) ⟨26396441, by rfl⟩ : syracuseStep 35195255 = 52792883) B52792883
theorem B23463503 : Blo 2169435 23463503 := bstep (se 1 (by rfl) ⟨17597627, by rfl⟩ : syracuseStep 23463503 = 35195255) B35195255
theorem B15642335 : Blo 2169435 15642335 := bstep (se 1 (by rfl) ⟨11731751, by rfl⟩ : syracuseStep 15642335 = 23463503) B23463503
theorem B41712893 : Blo 2169435 41712893 := bstep (se 3 (by rfl) ⟨7821167, by rfl⟩ : syracuseStep 41712893 = 15642335) B15642335
theorem B27808595 : Blo 2169435 27808595 := bstep (se 1 (by rfl) ⟨20856446, by rfl⟩ : syracuseStep 27808595 = 41712893) B41712893
theorem B18539063 : Blo 2169435 18539063 := bstep (se 1 (by rfl) ⟨13904297, by rfl⟩ : syracuseStep 18539063 = 27808595) B27808595
theorem B12359375 : Blo 2169435 12359375 := bstep (se 1 (by rfl) ⟨9269531, by rfl⟩ : syracuseStep 12359375 = 18539063) B18539063
theorem B8239583 : Blo 2169435 8239583 := bstep (se 1 (by rfl) ⟨6179687, by rfl⟩ : syracuseStep 8239583 = 12359375) B12359375
theorem B5493055 : Blo 2169435 5493055 := bstep (se 1 (by rfl) ⟨4119791, by rfl⟩ : syracuseStep 5493055 = 8239583) B8239583
theorem B7324073 : Blo 2169435 7324073 := bstep (se 2 (by rfl) ⟨2746527, by rfl⟩ : syracuseStep 7324073 = 5493055) B5493055
theorem B4882715 : Blo 2169435 4882715 := bstep (se 1 (by rfl) ⟨3662036, by rfl⟩ : syracuseStep 4882715 = 7324073) B7324073
theorem B3255143 : Blo 2169435 3255143 := bstep (se 1 (by rfl) ⟨2441357, by rfl⟩ : syracuseStep 3255143 = 4882715) B4882715
theorem B2170095 : Blo 2169435 2170095 := bstep (se 1 (by rfl) ⟨1627571, by rfl⟩ : syracuseStep 2170095 = 3255143) B3255143
theorem B3255149 : Blo 2169435 3255149 := bbase (se 3 (by rfl) ⟨610340, by rfl⟩ : syracuseStep 3255149 = 1220681) (by norm_num)
theorem B2170099 : Blo 2169435 2170099 := bstep (se 1 (by rfl) ⟨1627574, by rfl⟩ : syracuseStep 2170099 = 3255149) B3255149
theorem B4882733 : Blo 2169435 4882733 := bbase (se 3 (by rfl) ⟨915512, by rfl⟩ : syracuseStep 4882733 = 1831025) (by norm_num)
theorem B3255155 : Blo 2169435 3255155 := bstep (se 1 (by rfl) ⟨2441366, by rfl⟩ : syracuseStep 3255155 = 4882733) B4882733
theorem B2170103 : Blo 2169435 2170103 := bstep (se 1 (by rfl) ⟨1627577, by rfl⟩ : syracuseStep 2170103 = 3255155) B3255155
theorem B2784017 : Blo 2169435 2784017 := bbase (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) (by norm_num)
theorem B7424045 : Blo 2169435 7424045 := bstep (se 3 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 7424045 = 2784017) B2784017
theorem B4949363 : Blo 2169435 4949363 := bstep (se 1 (by rfl) ⟨3712022, by rfl⟩ : syracuseStep 4949363 = 7424045) B7424045
theorem B13198301 : Blo 2169435 13198301 := bstep (se 3 (by rfl) ⟨2474681, by rfl⟩ : syracuseStep 13198301 = 4949363) B4949363
theorem B8798867 : Blo 2169435 8798867 := bstep (se 1 (by rfl) ⟨6599150, by rfl⟩ : syracuseStep 8798867 = 13198301) B13198301
theorem B5865911 : Blo 2169435 5865911 := bstep (se 1 (by rfl) ⟨4399433, by rfl⟩ : syracuseStep 5865911 = 8798867) B8798867
theorem B3910607 : Blo 2169435 3910607 := bstep (se 1 (by rfl) ⟨2932955, by rfl⟩ : syracuseStep 3910607 = 5865911) B5865911
theorem B2607071 : Blo 2169435 2607071 := bstep (se 1 (by rfl) ⟨1955303, by rfl⟩ : syracuseStep 2607071 = 3910607) B3910607
theorem B6952189 : Blo 2169435 6952189 := bstep (se 3 (by rfl) ⟨1303535, by rfl⟩ : syracuseStep 6952189 = 2607071) B2607071
theorem B9269585 : Blo 2169435 9269585 := bstep (se 2 (by rfl) ⟨3476094, by rfl⟩ : syracuseStep 9269585 = 6952189) B6952189
theorem B6179723 : Blo 2169435 6179723 := bstep (se 1 (by rfl) ⟨4634792, by rfl⟩ : syracuseStep 6179723 = 9269585) B9269585
theorem B4119815 : Blo 2169435 4119815 := bstep (se 1 (by rfl) ⟨3089861, by rfl⟩ : syracuseStep 4119815 = 6179723) B6179723
theorem B2746543 : Blo 2169435 2746543 := bstep (se 1 (by rfl) ⟨2059907, by rfl⟩ : syracuseStep 2746543 = 4119815) B4119815
theorem B3662057 : Blo 2169435 3662057 := bstep (se 2 (by rfl) ⟨1373271, by rfl⟩ : syracuseStep 3662057 = 2746543) B2746543
theorem B2441371 : Blo 2169435 2441371 := bstep (se 1 (by rfl) ⟨1831028, by rfl⟩ : syracuseStep 2441371 = 3662057) B3662057
theorem B3255161 : Blo 2169435 3255161 := bstep (se 2 (by rfl) ⟨1220685, by rfl⟩ : syracuseStep 3255161 = 2441371) B2441371
theorem B2170107 : Blo 2169435 2170107 := bstep (se 1 (by rfl) ⟨1627580, by rfl⟩ : syracuseStep 2170107 = 3255161) B3255161
theorem B5721013 : Blo 2169435 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B7628017 : Blo 2169435 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B10170689 : Blo 2169435 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B27121837 : Blo 2169435 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B36162449 : Blo 2169435 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B24108299 : Blo 2169435 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B16072199 : Blo 2169435 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B10714799 : Blo 2169435 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B28572797 : Blo 2169435 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B19048531 : Blo 2169435 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B25398041 : Blo 2169435 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B270912437 : Blo 2169435 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B180608291 : Blo 2169435 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B120405527 : Blo 2169435 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B80270351 : Blo 2169435 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B53513567 : Blo 2169435 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B35675711 : Blo 2169435 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B23783807 : Blo 2169435 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B15855871 : Blo 2169435 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B21141161 : Blo 2169435 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B14094107 : Blo 2169435 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B9396071 : Blo 2169435 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B6264047 : Blo 2169435 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B4176031 : Blo 2169435 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B5568041 : Blo 2169435 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B14848109 : Blo 2169435 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B9898739 : Blo 2169435 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B6599159 : Blo 2169435 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B4399439 : Blo 2169435 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B46927349 : Blo 2169435 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B31284899 : Blo 2169435 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B20856599 : Blo 2169435 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B13904399 : Blo 2169435 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B37078397 : Blo 2169435 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B24718931 : Blo 2169435 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B16479287 : Blo 2169435 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B10986191 : Blo 2169435 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B7324127 : Blo 2169435 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B4882751 : Blo 2169435 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B3255167 : Blo 2169435 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B2170111 : Blo 2169435 2170111 := bstep (se 1 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 2170111 = 3255167) B3255167
theorem B3255173 : Blo 2169435 3255173 := bbase (se 4 (by rfl) ⟨305172, by rfl⟩ : syracuseStep 3255173 = 610345) (by norm_num)
theorem B2170115 : Blo 2169435 2170115 := bstep (se 1 (by rfl) ⟨1627586, by rfl⟩ : syracuseStep 2170115 = 3255173) B3255173
theorem B3662077 : Blo 2169435 3662077 := bbase (se 3 (by rfl) ⟨686639, by rfl⟩ : syracuseStep 3662077 = 1373279) (by norm_num)
theorem B4882769 : Blo 2169435 4882769 := bstep (se 2 (by rfl) ⟨1831038, by rfl⟩ : syracuseStep 4882769 = 3662077) B3662077
theorem B3255179 : Blo 2169435 3255179 := bstep (se 1 (by rfl) ⟨2441384, by rfl⟩ : syracuseStep 3255179 = 4882769) B4882769
theorem B2170119 : Blo 2169435 2170119 := bstep (se 1 (by rfl) ⟨1627589, by rfl⟩ : syracuseStep 2170119 = 3255179) B3255179
theorem B2441389 : Blo 2169435 2441389 := bbase (se 3 (by rfl) ⟨457760, by rfl⟩ : syracuseStep 2441389 = 915521) (by norm_num)
theorem B3255185 : Blo 2169435 3255185 := bstep (se 2 (by rfl) ⟨1220694, by rfl⟩ : syracuseStep 3255185 = 2441389) B2441389
theorem B2170123 : Blo 2169435 2170123 := bstep (se 1 (by rfl) ⟨1627592, by rfl⟩ : syracuseStep 2170123 = 3255185) B3255185
theorem B7324181 : Blo 2169435 7324181 := bbase (se 6 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 7324181 = 343321) (by norm_num)
theorem B4882787 : Blo 2169435 4882787 := bstep (se 1 (by rfl) ⟨3662090, by rfl⟩ : syracuseStep 4882787 = 7324181) B7324181
theorem B3255191 : Blo 2169435 3255191 := bstep (se 1 (by rfl) ⟨2441393, by rfl⟩ : syracuseStep 3255191 = 4882787) B4882787
theorem B2170127 : Blo 2169435 2170127 := bstep (se 1 (by rfl) ⟨1627595, by rfl⟩ : syracuseStep 2170127 = 3255191) B3255191
theorem B3255197 : Blo 2169435 3255197 := bbase (se 3 (by rfl) ⟨610349, by rfl⟩ : syracuseStep 3255197 = 1220699) (by norm_num)
theorem B2170131 : Blo 2169435 2170131 := bstep (se 1 (by rfl) ⟨1627598, by rfl⟩ : syracuseStep 2170131 = 3255197) B3255197
theorem B4882805 : Blo 2169435 4882805 := bbase (se 5 (by rfl) ⟨228881, by rfl⟩ : syracuseStep 4882805 = 457763) (by norm_num)
theorem B3255203 : Blo 2169435 3255203 := bstep (se 1 (by rfl) ⟨2441402, by rfl⟩ : syracuseStep 3255203 = 4882805) B4882805
theorem B2170135 : Blo 2169435 2170135 := bstep (se 1 (by rfl) ⟨1627601, by rfl⟩ : syracuseStep 2170135 = 3255203) B3255203
theorem B2607109 : Blo 2169435 2607109 := bbase (se 4 (by rfl) ⟨244416, by rfl⟩ : syracuseStep 2607109 = 488833) (by norm_num)
theorem B13904581 : Blo 2169435 13904581 := bstep (se 4 (by rfl) ⟨1303554, by rfl⟩ : syracuseStep 13904581 = 2607109) B2607109
theorem B18539441 : Blo 2169435 18539441 := bstep (se 2 (by rfl) ⟨6952290, by rfl⟩ : syracuseStep 18539441 = 13904581) B13904581
theorem B12359627 : Blo 2169435 12359627 := bstep (se 1 (by rfl) ⟨9269720, by rfl⟩ : syracuseStep 12359627 = 18539441) B18539441
theorem B8239751 : Blo 2169435 8239751 := bstep (se 1 (by rfl) ⟨6179813, by rfl⟩ : syracuseStep 8239751 = 12359627) B12359627
theorem B5493167 : Blo 2169435 5493167 := bstep (se 1 (by rfl) ⟨4119875, by rfl⟩ : syracuseStep 5493167 = 8239751) B8239751
theorem B3662111 : Blo 2169435 3662111 := bstep (se 1 (by rfl) ⟨2746583, by rfl⟩ : syracuseStep 3662111 = 5493167) B5493167
theorem B2441407 : Blo 2169435 2441407 := bstep (se 1 (by rfl) ⟨1831055, by rfl⟩ : syracuseStep 2441407 = 3662111) B3662111
theorem B3255209 : Blo 2169435 3255209 := bstep (se 2 (by rfl) ⟨1220703, by rfl⟩ : syracuseStep 3255209 = 2441407) B2441407
theorem B2170139 : Blo 2169435 2170139 := bstep (se 1 (by rfl) ⟨1627604, by rfl⟩ : syracuseStep 2170139 = 3255209) B3255209
theorem B8239765 : Blo 2169435 8239765 := bbase (se 6 (by rfl) ⟨193119, by rfl⟩ : syracuseStep 8239765 = 386239) (by norm_num)
theorem B10986353 : Blo 2169435 10986353 := bstep (se 2 (by rfl) ⟨4119882, by rfl⟩ : syracuseStep 10986353 = 8239765) B8239765
theorem B7324235 : Blo 2169435 7324235 := bstep (se 1 (by rfl) ⟨5493176, by rfl⟩ : syracuseStep 7324235 = 10986353) B10986353
theorem B4882823 : Blo 2169435 4882823 := bstep (se 1 (by rfl) ⟨3662117, by rfl⟩ : syracuseStep 4882823 = 7324235) B7324235
theorem B3255215 : Blo 2169435 3255215 := bstep (se 1 (by rfl) ⟨2441411, by rfl⟩ : syracuseStep 3255215 = 4882823) B4882823
theorem B2170143 : Blo 2169435 2170143 := bstep (se 1 (by rfl) ⟨1627607, by rfl⟩ : syracuseStep 2170143 = 3255215) B3255215
theorem B3255221 : Blo 2169435 3255221 := bbase (se 5 (by rfl) ⟨152588, by rfl⟩ : syracuseStep 3255221 = 305177) (by norm_num)
theorem B2170147 : Blo 2169435 2170147 := bstep (se 1 (by rfl) ⟨1627610, by rfl⟩ : syracuseStep 2170147 = 3255221) B3255221
theorem B5493197 : Blo 2169435 5493197 := bbase (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) (by norm_num)
theorem B3662131 : Blo 2169435 3662131 := bstep (se 1 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 3662131 = 5493197) B5493197
theorem B4882841 : Blo 2169435 4882841 := bstep (se 2 (by rfl) ⟨1831065, by rfl⟩ : syracuseStep 4882841 = 3662131) B3662131
theorem B3255227 : Blo 2169435 3255227 := bstep (se 1 (by rfl) ⟨2441420, by rfl⟩ : syracuseStep 3255227 = 4882841) B4882841
theorem B2170151 : Blo 2169435 2170151 := bstep (se 1 (by rfl) ⟨1627613, by rfl⟩ : syracuseStep 2170151 = 3255227) B3255227
theorem B2441425 : Blo 2169435 2441425 := bbase (se 2 (by rfl) ⟨915534, by rfl⟩ : syracuseStep 2441425 = 1831069) (by norm_num)
theorem B3255233 : Blo 2169435 3255233 := bstep (se 2 (by rfl) ⟨1220712, by rfl⟩ : syracuseStep 3255233 = 2441425) B2441425
theorem B2170155 : Blo 2169435 2170155 := bstep (se 1 (by rfl) ⟨1627616, by rfl⟩ : syracuseStep 2170155 = 3255233) B3255233
theorem B10428533 : Blo 2169435 10428533 := bbase (se 5 (by rfl) ⟨488837, by rfl⟩ : syracuseStep 10428533 = 977675) (by norm_num)
theorem B6952355 : Blo 2169435 6952355 := bstep (se 1 (by rfl) ⟨5214266, by rfl⟩ : syracuseStep 6952355 = 10428533) B10428533
theorem B4634903 : Blo 2169435 4634903 := bstep (se 1 (by rfl) ⟨3476177, by rfl⟩ : syracuseStep 4634903 = 6952355) B6952355
theorem B3089935 : Blo 2169435 3089935 := bstep (se 1 (by rfl) ⟨2317451, by rfl⟩ : syracuseStep 3089935 = 4634903) B4634903
theorem B4119913 : Blo 2169435 4119913 := bstep (se 2 (by rfl) ⟨1544967, by rfl⟩ : syracuseStep 4119913 = 3089935) B3089935
theorem B5493217 : Blo 2169435 5493217 := bstep (se 2 (by rfl) ⟨2059956, by rfl⟩ : syracuseStep 5493217 = 4119913) B4119913
theorem B7324289 : Blo 2169435 7324289 := bstep (se 2 (by rfl) ⟨2746608, by rfl⟩ : syracuseStep 7324289 = 5493217) B5493217
theorem B4882859 : Blo 2169435 4882859 := bstep (se 1 (by rfl) ⟨3662144, by rfl⟩ : syracuseStep 4882859 = 7324289) B7324289
theorem B3255239 : Blo 2169435 3255239 := bstep (se 1 (by rfl) ⟨2441429, by rfl⟩ : syracuseStep 3255239 = 4882859) B4882859
theorem B2170159 : Blo 2169435 2170159 := bstep (se 1 (by rfl) ⟨1627619, by rfl⟩ : syracuseStep 2170159 = 3255239) B3255239
theorem B3255245 : Blo 2169435 3255245 := bbase (se 3 (by rfl) ⟨610358, by rfl⟩ : syracuseStep 3255245 = 1220717) (by norm_num)
theorem B2170163 : Blo 2169435 2170163 := bstep (se 1 (by rfl) ⟨1627622, by rfl⟩ : syracuseStep 2170163 = 3255245) B3255245
theorem B4882877 : Blo 2169435 4882877 := bbase (se 3 (by rfl) ⟨915539, by rfl⟩ : syracuseStep 4882877 = 1831079) (by norm_num)
theorem B3255251 : Blo 2169435 3255251 := bstep (se 1 (by rfl) ⟨2441438, by rfl⟩ : syracuseStep 3255251 = 4882877) B4882877
theorem B2170167 : Blo 2169435 2170167 := bstep (se 1 (by rfl) ⟨1627625, by rfl⟩ : syracuseStep 2170167 = 3255251) B3255251
theorem B3662165 : Blo 2169435 3662165 := bbase (se 10 (by rfl) ⟨5364, by rfl⟩ : syracuseStep 3662165 = 10729) (by norm_num)
theorem B2441443 : Blo 2169435 2441443 := bstep (se 1 (by rfl) ⟨1831082, by rfl⟩ : syracuseStep 2441443 = 3662165) B3662165
theorem B3255257 : Blo 2169435 3255257 := bstep (se 2 (by rfl) ⟨1220721, by rfl⟩ : syracuseStep 3255257 = 2441443) B2441443
theorem B2170171 : Blo 2169435 2170171 := bstep (se 1 (by rfl) ⟨1627628, by rfl⟩ : syracuseStep 2170171 = 3255257) B3255257
theorem B6952405 : Blo 2169435 6952405 := bbase (se 7 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 6952405 = 162947) (by norm_num)
theorem B9269873 : Blo 2169435 9269873 := bstep (se 2 (by rfl) ⟨3476202, by rfl⟩ : syracuseStep 9269873 = 6952405) B6952405
theorem B6179915 : Blo 2169435 6179915 := bstep (se 1 (by rfl) ⟨4634936, by rfl⟩ : syracuseStep 6179915 = 9269873) B9269873
theorem B16479773 : Blo 2169435 16479773 := bstep (se 3 (by rfl) ⟨3089957, by rfl⟩ : syracuseStep 16479773 = 6179915) B6179915
theorem B10986515 : Blo 2169435 10986515 := bstep (se 1 (by rfl) ⟨8239886, by rfl⟩ : syracuseStep 10986515 = 16479773) B16479773
theorem B7324343 : Blo 2169435 7324343 := bstep (se 1 (by rfl) ⟨5493257, by rfl⟩ : syracuseStep 7324343 = 10986515) B10986515
theorem B4882895 : Blo 2169435 4882895 := bstep (se 1 (by rfl) ⟨3662171, by rfl⟩ : syracuseStep 4882895 = 7324343) B7324343
theorem B3255263 : Blo 2169435 3255263 := bstep (se 1 (by rfl) ⟨2441447, by rfl⟩ : syracuseStep 3255263 = 4882895) B4882895
theorem B2170175 : Blo 2169435 2170175 := bstep (se 1 (by rfl) ⟨1627631, by rfl⟩ : syracuseStep 2170175 = 3255263) B3255263
theorem B3255269 : Blo 2169435 3255269 := bbase (se 4 (by rfl) ⟨305181, by rfl⟩ : syracuseStep 3255269 = 610363) (by norm_num)
theorem B2170179 : Blo 2169435 2170179 := bstep (se 1 (by rfl) ⟨1627634, by rfl⟩ : syracuseStep 2170179 = 3255269) B3255269
theorem B9269909 : Blo 2169435 9269909 := bbase (se 6 (by rfl) ⟨217263, by rfl⟩ : syracuseStep 9269909 = 434527) (by norm_num)
theorem B6179939 : Blo 2169435 6179939 := bstep (se 1 (by rfl) ⟨4634954, by rfl⟩ : syracuseStep 6179939 = 9269909) B9269909
theorem B4119959 : Blo 2169435 4119959 := bstep (se 1 (by rfl) ⟨3089969, by rfl⟩ : syracuseStep 4119959 = 6179939) B6179939
theorem B2746639 : Blo 2169435 2746639 := bstep (se 1 (by rfl) ⟨2059979, by rfl⟩ : syracuseStep 2746639 = 4119959) B4119959
theorem B3662185 : Blo 2169435 3662185 := bstep (se 2 (by rfl) ⟨1373319, by rfl⟩ : syracuseStep 3662185 = 2746639) B2746639
theorem B4882913 : Blo 2169435 4882913 := bstep (se 2 (by rfl) ⟨1831092, by rfl⟩ : syracuseStep 4882913 = 3662185) B3662185
theorem B3255275 : Blo 2169435 3255275 := bstep (se 1 (by rfl) ⟨2441456, by rfl⟩ : syracuseStep 3255275 = 4882913) B4882913
theorem B2170183 : Blo 2169435 2170183 := bstep (se 1 (by rfl) ⟨1627637, by rfl⟩ : syracuseStep 2170183 = 3255275) B3255275
theorem B2441461 : Blo 2169435 2441461 := bbase (se 5 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 2441461 = 228887) (by norm_num)
theorem B3255281 : Blo 2169435 3255281 := bstep (se 2 (by rfl) ⟨1220730, by rfl⟩ : syracuseStep 3255281 = 2441461) B2441461
theorem B2170187 : Blo 2169435 2170187 := bstep (se 1 (by rfl) ⟨1627640, by rfl⟩ : syracuseStep 2170187 = 3255281) B3255281
theorem B2746649 : Blo 2169435 2746649 := bbase (se 2 (by rfl) ⟨1029993, by rfl⟩ : syracuseStep 2746649 = 2059987) (by norm_num)
theorem B7324397 : Blo 2169435 7324397 := bstep (se 3 (by rfl) ⟨1373324, by rfl⟩ : syracuseStep 7324397 = 2746649) B2746649
theorem B4882931 : Blo 2169435 4882931 := bstep (se 1 (by rfl) ⟨3662198, by rfl⟩ : syracuseStep 4882931 = 7324397) B7324397
theorem B3255287 : Blo 2169435 3255287 := bstep (se 1 (by rfl) ⟨2441465, by rfl⟩ : syracuseStep 3255287 = 4882931) B4882931
theorem B2170191 : Blo 2169435 2170191 := bstep (se 1 (by rfl) ⟨1627643, by rfl⟩ : syracuseStep 2170191 = 3255287) B3255287
theorem B3255293 : Blo 2169435 3255293 := bbase (se 3 (by rfl) ⟨610367, by rfl⟩ : syracuseStep 3255293 = 1220735) (by norm_num)
theorem B2170195 : Blo 2169435 2170195 := bstep (se 1 (by rfl) ⟨1627646, by rfl⟩ : syracuseStep 2170195 = 3255293) B3255293
theorem B4882949 : Blo 2169435 4882949 := bbase (se 4 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 4882949 = 915553) (by norm_num)
theorem B3255299 : Blo 2169435 3255299 := bstep (se 1 (by rfl) ⟨2441474, by rfl⟩ : syracuseStep 3255299 = 4882949) B4882949
theorem B2170199 : Blo 2169435 2170199 := bstep (se 1 (by rfl) ⟨1627649, by rfl⟩ : syracuseStep 2170199 = 3255299) B3255299
theorem B4119997 : Blo 2169435 4119997 := bbase (se 3 (by rfl) ⟨772499, by rfl⟩ : syracuseStep 4119997 = 1544999) (by norm_num)
theorem B5493329 : Blo 2169435 5493329 := bstep (se 2 (by rfl) ⟨2059998, by rfl⟩ : syracuseStep 5493329 = 4119997) B4119997
theorem B3662219 : Blo 2169435 3662219 := bstep (se 1 (by rfl) ⟨2746664, by rfl⟩ : syracuseStep 3662219 = 5493329) B5493329
theorem B2441479 : Blo 2169435 2441479 := bstep (se 1 (by rfl) ⟨1831109, by rfl⟩ : syracuseStep 2441479 = 3662219) B3662219
theorem B3255305 : Blo 2169435 3255305 := bstep (se 2 (by rfl) ⟨1220739, by rfl⟩ : syracuseStep 3255305 = 2441479) B2441479
theorem B2170203 : Blo 2169435 2170203 := bstep (se 1 (by rfl) ⟨1627652, by rfl⟩ : syracuseStep 2170203 = 3255305) B3255305
theorem B10986677 : Blo 2169435 10986677 := bbase (se 5 (by rfl) ⟨515000, by rfl⟩ : syracuseStep 10986677 = 1030001) (by norm_num)
theorem B7324451 : Blo 2169435 7324451 := bstep (se 1 (by rfl) ⟨5493338, by rfl⟩ : syracuseStep 7324451 = 10986677) B10986677
theorem B4882967 : Blo 2169435 4882967 := bstep (se 1 (by rfl) ⟨3662225, by rfl⟩ : syracuseStep 4882967 = 7324451) B7324451
theorem B3255311 : Blo 2169435 3255311 := bstep (se 1 (by rfl) ⟨2441483, by rfl⟩ : syracuseStep 3255311 = 4882967) B4882967
theorem B2170207 : Blo 2169435 2170207 := bstep (se 1 (by rfl) ⟨1627655, by rfl⟩ : syracuseStep 2170207 = 3255311) B3255311
theorem B3255317 : Blo 2169435 3255317 := bbase (se 6 (by rfl) ⟨76296, by rfl⟩ : syracuseStep 3255317 = 152593) (by norm_num)
theorem B2170211 : Blo 2169435 2170211 := bstep (se 1 (by rfl) ⟨1627658, by rfl⟩ : syracuseStep 2170211 = 3255317) B3255317
theorem B8799301 : Blo 2169435 8799301 := bbase (se 4 (by rfl) ⟨824934, by rfl⟩ : syracuseStep 8799301 = 1649869) (by norm_num)
theorem B11732401 : Blo 2169435 11732401 := bstep (se 2 (by rfl) ⟨4399650, by rfl⟩ : syracuseStep 11732401 = 8799301) B8799301
theorem B15643201 : Blo 2169435 15643201 := bstep (se 2 (by rfl) ⟨5866200, by rfl⟩ : syracuseStep 15643201 = 11732401) B11732401
theorem B20857601 : Blo 2169435 20857601 := bstep (se 2 (by rfl) ⟨7821600, by rfl⟩ : syracuseStep 20857601 = 15643201) B15643201
theorem B13905067 : Blo 2169435 13905067 := bstep (se 1 (by rfl) ⟨10428800, by rfl⟩ : syracuseStep 13905067 = 20857601) B20857601
theorem B18540089 : Blo 2169435 18540089 := bstep (se 2 (by rfl) ⟨6952533, by rfl⟩ : syracuseStep 18540089 = 13905067) B13905067
theorem B12360059 : Blo 2169435 12360059 := bstep (se 1 (by rfl) ⟨9270044, by rfl⟩ : syracuseStep 12360059 = 18540089) B18540089
theorem B8240039 : Blo 2169435 8240039 := bstep (se 1 (by rfl) ⟨6180029, by rfl⟩ : syracuseStep 8240039 = 12360059) B12360059
theorem B5493359 : Blo 2169435 5493359 := bstep (se 1 (by rfl) ⟨4120019, by rfl⟩ : syracuseStep 5493359 = 8240039) B8240039
theorem B3662239 : Blo 2169435 3662239 := bstep (se 1 (by rfl) ⟨2746679, by rfl⟩ : syracuseStep 3662239 = 5493359) B5493359
theorem B4882985 : Blo 2169435 4882985 := bstep (se 2 (by rfl) ⟨1831119, by rfl⟩ : syracuseStep 4882985 = 3662239) B3662239
theorem B3255323 : Blo 2169435 3255323 := bstep (se 1 (by rfl) ⟨2441492, by rfl⟩ : syracuseStep 3255323 = 4882985) B4882985
theorem B2170215 : Blo 2169435 2170215 := bstep (se 1 (by rfl) ⟨1627661, by rfl⟩ : syracuseStep 2170215 = 3255323) B3255323
theorem B2441497 : Blo 2169435 2441497 := bbase (se 2 (by rfl) ⟨915561, by rfl⟩ : syracuseStep 2441497 = 1831123) (by norm_num)
theorem B3255329 : Blo 2169435 3255329 := bstep (se 2 (by rfl) ⟨1220748, by rfl⟩ : syracuseStep 3255329 = 2441497) B2441497
theorem B2170219 : Blo 2169435 2170219 := bstep (se 1 (by rfl) ⟨1627664, by rfl⟩ : syracuseStep 2170219 = 3255329) B3255329
theorem B8240069 : Blo 2169435 8240069 := bbase (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) (by norm_num)
theorem B5493379 : Blo 2169435 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B7324505 : Blo 2169435 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B4883003 : Blo 2169435 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B3255335 : Blo 2169435 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B2170223 : Blo 2169435 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B3255341 : Blo 2169435 3255341 := bbase (se 3 (by rfl) ⟨610376, by rfl⟩ : syracuseStep 3255341 = 1220753) (by norm_num)
theorem B2170227 : Blo 2169435 2170227 := bstep (se 1 (by rfl) ⟨1627670, by rfl⟩ : syracuseStep 2170227 = 3255341) B3255341
theorem B4883021 : Blo 2169435 4883021 := bbase (se 3 (by rfl) ⟨915566, by rfl⟩ : syracuseStep 4883021 = 1831133) (by norm_num)
theorem B3255347 : Blo 2169435 3255347 := bstep (se 1 (by rfl) ⟨2441510, by rfl⟩ : syracuseStep 3255347 = 4883021) B4883021
theorem B2170231 : Blo 2169435 2170231 := bstep (se 1 (by rfl) ⟨1627673, by rfl⟩ : syracuseStep 2170231 = 3255347) B3255347
theorem B2746705 : Blo 2169435 2746705 := bbase (se 2 (by rfl) ⟨1030014, by rfl⟩ : syracuseStep 2746705 = 2060029) (by norm_num)
theorem B3662273 : Blo 2169435 3662273 := bstep (se 2 (by rfl) ⟨1373352, by rfl⟩ : syracuseStep 3662273 = 2746705) B2746705
theorem B2441515 : Blo 2169435 2441515 := bstep (se 1 (by rfl) ⟨1831136, by rfl⟩ : syracuseStep 2441515 = 3662273) B3662273
theorem B3255353 : Blo 2169435 3255353 := bstep (se 2 (by rfl) ⟨1220757, by rfl⟩ : syracuseStep 3255353 = 2441515) B2441515
theorem B2170235 : Blo 2169435 2170235 := bstep (se 1 (by rfl) ⟨1627676, by rfl⟩ : syracuseStep 2170235 = 3255353) B3255353
theorem B2607229 : Blo 2169435 2607229 := bbase (se 3 (by rfl) ⟨488855, by rfl⟩ : syracuseStep 2607229 = 977711) (by norm_num)
theorem B3476305 : Blo 2169435 3476305 := bstep (se 2 (by rfl) ⟨1303614, by rfl⟩ : syracuseStep 3476305 = 2607229) B2607229
theorem B4635073 : Blo 2169435 4635073 := bstep (se 2 (by rfl) ⟨1738152, by rfl⟩ : syracuseStep 4635073 = 3476305) B3476305
theorem B24720389 : Blo 2169435 24720389 := bstep (se 4 (by rfl) ⟨2317536, by rfl⟩ : syracuseStep 24720389 = 4635073) B4635073
theorem B16480259 : Blo 2169435 16480259 := bstep (se 1 (by rfl) ⟨12360194, by rfl⟩ : syracuseStep 16480259 = 24720389) B24720389
theorem B10986839 : Blo 2169435 10986839 := bstep (se 1 (by rfl) ⟨8240129, by rfl⟩ : syracuseStep 10986839 = 16480259) B16480259
theorem B7324559 : Blo 2169435 7324559 := bstep (se 1 (by rfl) ⟨5493419, by rfl⟩ : syracuseStep 7324559 = 10986839) B10986839
theorem B4883039 : Blo 2169435 4883039 := bstep (se 1 (by rfl) ⟨3662279, by rfl⟩ : syracuseStep 4883039 = 7324559) B7324559
theorem B3255359 : Blo 2169435 3255359 := bstep (se 1 (by rfl) ⟨2441519, by rfl⟩ : syracuseStep 3255359 = 4883039) B4883039
theorem B2170239 : Blo 2169435 2170239 := bstep (se 1 (by rfl) ⟨1627679, by rfl⟩ : syracuseStep 2170239 = 3255359) B3255359
theorem B3255365 : Blo 2169435 3255365 := bbase (se 4 (by rfl) ⟨305190, by rfl⟩ : syracuseStep 3255365 = 610381) (by norm_num)
theorem B2170243 : Blo 2169435 2170243 := bstep (se 1 (by rfl) ⟨1627682, by rfl⟩ : syracuseStep 2170243 = 3255365) B3255365
theorem B3662293 : Blo 2169435 3662293 := bbase (se 7 (by rfl) ⟨42917, by rfl⟩ : syracuseStep 3662293 = 85835) (by norm_num)
theorem B4883057 : Blo 2169435 4883057 := bstep (se 2 (by rfl) ⟨1831146, by rfl⟩ : syracuseStep 4883057 = 3662293) B3662293
theorem B3255371 : Blo 2169435 3255371 := bstep (se 1 (by rfl) ⟨2441528, by rfl⟩ : syracuseStep 3255371 = 4883057) B4883057
theorem B2170247 : Blo 2169435 2170247 := bstep (se 1 (by rfl) ⟨1627685, by rfl⟩ : syracuseStep 2170247 = 3255371) B3255371
theorem B2441533 : Blo 2169435 2441533 := bbase (se 3 (by rfl) ⟨457787, by rfl⟩ : syracuseStep 2441533 = 915575) (by norm_num)
theorem B3255377 : Blo 2169435 3255377 := bstep (se 2 (by rfl) ⟨1220766, by rfl⟩ : syracuseStep 3255377 = 2441533) B2441533
theorem B2170251 : Blo 2169435 2170251 := bstep (se 1 (by rfl) ⟨1627688, by rfl⟩ : syracuseStep 2170251 = 3255377) B3255377
theorem B7324613 : Blo 2169435 7324613 := bbase (se 4 (by rfl) ⟨686682, by rfl⟩ : syracuseStep 7324613 = 1373365) (by norm_num)
theorem B4883075 : Blo 2169435 4883075 := bstep (se 1 (by rfl) ⟨3662306, by rfl⟩ : syracuseStep 4883075 = 7324613) B7324613
theorem B3255383 : Blo 2169435 3255383 := bstep (se 1 (by rfl) ⟨2441537, by rfl⟩ : syracuseStep 3255383 = 4883075) B4883075
theorem B2170255 : Blo 2169435 2170255 := bstep (se 1 (by rfl) ⟨1627691, by rfl⟩ : syracuseStep 2170255 = 3255383) B3255383
theorem B3255389 : Blo 2169435 3255389 := bbase (se 3 (by rfl) ⟨610385, by rfl⟩ : syracuseStep 3255389 = 1220771) (by norm_num)
theorem B2170259 : Blo 2169435 2170259 := bstep (se 1 (by rfl) ⟨1627694, by rfl⟩ : syracuseStep 2170259 = 3255389) B3255389
theorem B4883093 : Blo 2169435 4883093 := bbase (se 6 (by rfl) ⟨114447, by rfl⟩ : syracuseStep 4883093 = 228895) (by norm_num)
theorem B3255395 : Blo 2169435 3255395 := bstep (se 1 (by rfl) ⟨2441546, by rfl⟩ : syracuseStep 3255395 = 4883093) B4883093
theorem B2170263 : Blo 2169435 2170263 := bstep (se 1 (by rfl) ⟨1627697, by rfl⟩ : syracuseStep 2170263 = 3255395) B3255395
theorem B5357789 : Blo 2169435 5357789 := bbase (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) (by norm_num)
theorem B3571859 : Blo 2169435 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B2381239 : Blo 2169435 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B3174985 : Blo 2169435 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B4233313 : Blo 2169435 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B5644417 : Blo 2169435 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B7525889 : Blo 2169435 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B5017259 : Blo 2169435 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B3344839 : Blo 2169435 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B71356565 : Blo 2169435 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B190284173 : Blo 2169435 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B126856115 : Blo 2169435 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B84570743 : Blo 2169435 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B56380495 : Blo 2169435 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B75173993 : Blo 2169435 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B50115995 : Blo 2169435 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B33410663 : Blo 2169435 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B22273775 : Blo 2169435 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B14849183 : Blo 2169435 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B39597821 : Blo 2169435 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B26398547 : Blo 2169435 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B17599031 : Blo 2169435 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B11732687 : Blo 2169435 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B7821791 : Blo 2169435 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B5214527 : Blo 2169435 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B3476351 : Blo 2169435 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B2317567 : Blo 2169435 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B3090089 : Blo 2169435 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B8240237 : Blo 2169435 8240237 := bstep (se 3 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 8240237 = 3090089) B3090089
theorem B5493491 : Blo 2169435 5493491 := bstep (se 1 (by rfl) ⟨4120118, by rfl⟩ : syracuseStep 5493491 = 8240237) B8240237
theorem B3662327 : Blo 2169435 3662327 := bstep (se 1 (by rfl) ⟨2746745, by rfl⟩ : syracuseStep 3662327 = 5493491) B5493491
theorem B2441551 : Blo 2169435 2441551 := bstep (se 1 (by rfl) ⟨1831163, by rfl⟩ : syracuseStep 2441551 = 3662327) B3662327
theorem B3255401 : Blo 2169435 3255401 := bstep (se 2 (by rfl) ⟨1220775, by rfl⟩ : syracuseStep 3255401 = 2441551) B2441551
theorem B2170267 : Blo 2169435 2170267 := bstep (se 1 (by rfl) ⟨1627700, by rfl⟩ : syracuseStep 2170267 = 3255401) B3255401
theorem B3910901 : Blo 2169435 3910901 := bbase (se 5 (by rfl) ⟨183323, by rfl⟩ : syracuseStep 3910901 = 366647) (by norm_num)
theorem B10429069 : Blo 2169435 10429069 := bstep (se 3 (by rfl) ⟨1955450, by rfl⟩ : syracuseStep 10429069 = 3910901) B3910901
theorem B13905425 : Blo 2169435 13905425 := bstep (se 2 (by rfl) ⟨5214534, by rfl⟩ : syracuseStep 13905425 = 10429069) B10429069
theorem B9270283 : Blo 2169435 9270283 := bstep (se 1 (by rfl) ⟨6952712, by rfl⟩ : syracuseStep 9270283 = 13905425) B13905425
theorem B12360377 : Blo 2169435 12360377 := bstep (se 2 (by rfl) ⟨4635141, by rfl⟩ : syracuseStep 12360377 = 9270283) B9270283
theorem B8240251 : Blo 2169435 8240251 := bstep (se 1 (by rfl) ⟨6180188, by rfl⟩ : syracuseStep 8240251 = 12360377) B12360377
theorem B10987001 : Blo 2169435 10987001 := bstep (se 2 (by rfl) ⟨4120125, by rfl⟩ : syracuseStep 10987001 = 8240251) B8240251
theorem B7324667 : Blo 2169435 7324667 := bstep (se 1 (by rfl) ⟨5493500, by rfl⟩ : syracuseStep 7324667 = 10987001) B10987001
theorem B4883111 : Blo 2169435 4883111 := bstep (se 1 (by rfl) ⟨3662333, by rfl⟩ : syracuseStep 4883111 = 7324667) B7324667
theorem B3255407 : Blo 2169435 3255407 := bstep (se 1 (by rfl) ⟨2441555, by rfl⟩ : syracuseStep 3255407 = 4883111) B4883111
theorem B2170271 : Blo 2169435 2170271 := bstep (se 1 (by rfl) ⟨1627703, by rfl⟩ : syracuseStep 2170271 = 3255407) B3255407
theorem B3255413 : Blo 2169435 3255413 := bbase (se 5 (by rfl) ⟨152597, by rfl⟩ : syracuseStep 3255413 = 305195) (by norm_num)
theorem B2170275 : Blo 2169435 2170275 := bstep (se 1 (by rfl) ⟨1627706, by rfl⟩ : syracuseStep 2170275 = 3255413) B3255413
theorem B4120141 : Blo 2169435 4120141 := bbase (se 3 (by rfl) ⟨772526, by rfl⟩ : syracuseStep 4120141 = 1545053) (by norm_num)
theorem B5493521 : Blo 2169435 5493521 := bstep (se 2 (by rfl) ⟨2060070, by rfl⟩ : syracuseStep 5493521 = 4120141) B4120141
theorem B3662347 : Blo 2169435 3662347 := bstep (se 1 (by rfl) ⟨2746760, by rfl⟩ : syracuseStep 3662347 = 5493521) B5493521
theorem B4883129 : Blo 2169435 4883129 := bstep (se 2 (by rfl) ⟨1831173, by rfl⟩ : syracuseStep 4883129 = 3662347) B3662347
theorem B3255419 : Blo 2169435 3255419 := bstep (se 1 (by rfl) ⟨2441564, by rfl⟩ : syracuseStep 3255419 = 4883129) B4883129
theorem B2170279 : Blo 2169435 2170279 := bstep (se 1 (by rfl) ⟨1627709, by rfl⟩ : syracuseStep 2170279 = 3255419) B3255419
theorem B2441569 : Blo 2169435 2441569 := bbase (se 2 (by rfl) ⟨915588, by rfl⟩ : syracuseStep 2441569 = 1831177) (by norm_num)
theorem B3255425 : Blo 2169435 3255425 := bstep (se 2 (by rfl) ⟨1220784, by rfl⟩ : syracuseStep 3255425 = 2441569) B2441569
theorem B2170283 : Blo 2169435 2170283 := bstep (se 1 (by rfl) ⟨1627712, by rfl⟩ : syracuseStep 2170283 = 3255425) B3255425
theorem B5493541 : Blo 2169435 5493541 := bbase (se 4 (by rfl) ⟨515019, by rfl⟩ : syracuseStep 5493541 = 1030039) (by norm_num)
theorem B7324721 : Blo 2169435 7324721 := bstep (se 2 (by rfl) ⟨2746770, by rfl⟩ : syracuseStep 7324721 = 5493541) B5493541
theorem B4883147 : Blo 2169435 4883147 := bstep (se 1 (by rfl) ⟨3662360, by rfl⟩ : syracuseStep 4883147 = 7324721) B7324721
theorem B3255431 : Blo 2169435 3255431 := bstep (se 1 (by rfl) ⟨2441573, by rfl⟩ : syracuseStep 3255431 = 4883147) B4883147
theorem B2170287 : Blo 2169435 2170287 := bstep (se 1 (by rfl) ⟨1627715, by rfl⟩ : syracuseStep 2170287 = 3255431) B3255431
theorem B3255437 : Blo 2169435 3255437 := bbase (se 3 (by rfl) ⟨610394, by rfl⟩ : syracuseStep 3255437 = 1220789) (by norm_num)
theorem B2170291 : Blo 2169435 2170291 := bstep (se 1 (by rfl) ⟨1627718, by rfl⟩ : syracuseStep 2170291 = 3255437) B3255437
theorem B4883165 : Blo 2169435 4883165 := bbase (se 3 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 4883165 = 1831187) (by norm_num)
theorem B3255443 : Blo 2169435 3255443 := bstep (se 1 (by rfl) ⟨2441582, by rfl⟩ : syracuseStep 3255443 = 4883165) B4883165
theorem B2170295 : Blo 2169435 2170295 := bstep (se 1 (by rfl) ⟨1627721, by rfl⟩ : syracuseStep 2170295 = 3255443) B3255443
theorem B3662381 : Blo 2169435 3662381 := bbase (se 3 (by rfl) ⟨686696, by rfl⟩ : syracuseStep 3662381 = 1373393) (by norm_num)
theorem B2441587 : Blo 2169435 2441587 := bstep (se 1 (by rfl) ⟨1831190, by rfl⟩ : syracuseStep 2441587 = 3662381) B3662381
theorem B3255449 : Blo 2169435 3255449 := bstep (se 2 (by rfl) ⟨1220793, by rfl⟩ : syracuseStep 3255449 = 2441587) B2441587
theorem B2170299 : Blo 2169435 2170299 := bstep (se 1 (by rfl) ⟨1627724, by rfl⟩ : syracuseStep 2170299 = 3255449) B3255449
theorem B9396901 : Blo 2169435 9396901 := bbase (se 4 (by rfl) ⟨880959, by rfl⟩ : syracuseStep 9396901 = 1761919) (by norm_num)
theorem B12529201 : Blo 2169435 12529201 := bstep (se 2 (by rfl) ⟨4698450, by rfl⟩ : syracuseStep 12529201 = 9396901) B9396901
theorem B16705601 : Blo 2169435 16705601 := bstep (se 2 (by rfl) ⟨6264600, by rfl⟩ : syracuseStep 16705601 = 12529201) B12529201
theorem B11137067 : Blo 2169435 11137067 := bstep (se 1 (by rfl) ⟨8352800, by rfl⟩ : syracuseStep 11137067 = 16705601) B16705601
theorem B7424711 : Blo 2169435 7424711 := bstep (se 1 (by rfl) ⟨5568533, by rfl⟩ : syracuseStep 7424711 = 11137067) B11137067
theorem B4949807 : Blo 2169435 4949807 := bstep (se 1 (by rfl) ⟨3712355, by rfl⟩ : syracuseStep 4949807 = 7424711) B7424711
theorem B13199485 : Blo 2169435 13199485 := bstep (se 3 (by rfl) ⟨2474903, by rfl⟩ : syracuseStep 13199485 = 4949807) B4949807
theorem B17599313 : Blo 2169435 17599313 := bstep (se 2 (by rfl) ⟨6599742, by rfl⟩ : syracuseStep 17599313 = 13199485) B13199485
theorem B46931501 : Blo 2169435 46931501 := bstep (se 3 (by rfl) ⟨8799656, by rfl⟩ : syracuseStep 46931501 = 17599313) B17599313
theorem B31287667 : Blo 2169435 31287667 := bstep (se 1 (by rfl) ⟨23465750, by rfl⟩ : syracuseStep 31287667 = 46931501) B46931501
theorem B41716889 : Blo 2169435 41716889 := bstep (se 2 (by rfl) ⟨15643833, by rfl⟩ : syracuseStep 41716889 = 31287667) B31287667
theorem B27811259 : Blo 2169435 27811259 := bstep (se 1 (by rfl) ⟨20858444, by rfl⟩ : syracuseStep 27811259 = 41716889) B41716889
theorem B18540839 : Blo 2169435 18540839 := bstep (se 1 (by rfl) ⟨13905629, by rfl⟩ : syracuseStep 18540839 = 27811259) B27811259
theorem B12360559 : Blo 2169435 12360559 := bstep (se 1 (by rfl) ⟨9270419, by rfl⟩ : syracuseStep 12360559 = 18540839) B18540839
theorem B16480745 : Blo 2169435 16480745 := bstep (se 2 (by rfl) ⟨6180279, by rfl⟩ : syracuseStep 16480745 = 12360559) B12360559
theorem B10987163 : Blo 2169435 10987163 := bstep (se 1 (by rfl) ⟨8240372, by rfl⟩ : syracuseStep 10987163 = 16480745) B16480745
theorem B7324775 : Blo 2169435 7324775 := bstep (se 1 (by rfl) ⟨5493581, by rfl⟩ : syracuseStep 7324775 = 10987163) B10987163
theorem B4883183 : Blo 2169435 4883183 := bstep (se 1 (by rfl) ⟨3662387, by rfl⟩ : syracuseStep 4883183 = 7324775) B7324775
theorem B3255455 : Blo 2169435 3255455 := bstep (se 1 (by rfl) ⟨2441591, by rfl⟩ : syracuseStep 3255455 = 4883183) B4883183
theorem B2170303 : Blo 2169435 2170303 := bstep (se 1 (by rfl) ⟨1627727, by rfl⟩ : syracuseStep 2170303 = 3255455) B3255455
theorem B3255461 : Blo 2169435 3255461 := bbase (se 4 (by rfl) ⟨305199, by rfl⟩ : syracuseStep 3255461 = 610399) (by norm_num)
theorem B2170307 : Blo 2169435 2170307 := bstep (se 1 (by rfl) ⟨1627730, by rfl⟩ : syracuseStep 2170307 = 3255461) B3255461
theorem B2746801 : Blo 2169435 2746801 := bbase (se 2 (by rfl) ⟨1030050, by rfl⟩ : syracuseStep 2746801 = 2060101) (by norm_num)
theorem B3662401 : Blo 2169435 3662401 := bstep (se 2 (by rfl) ⟨1373400, by rfl⟩ : syracuseStep 3662401 = 2746801) B2746801
theorem B4883201 : Blo 2169435 4883201 := bstep (se 2 (by rfl) ⟨1831200, by rfl⟩ : syracuseStep 4883201 = 3662401) B3662401
theorem B3255467 : Blo 2169435 3255467 := bstep (se 1 (by rfl) ⟨2441600, by rfl⟩ : syracuseStep 3255467 = 4883201) B4883201
theorem B2170311 : Blo 2169435 2170311 := bstep (se 1 (by rfl) ⟨1627733, by rfl⟩ : syracuseStep 2170311 = 3255467) B3255467
theorem B2441605 : Blo 2169435 2441605 := bbase (se 4 (by rfl) ⟨228900, by rfl⟩ : syracuseStep 2441605 = 457801) (by norm_num)
theorem B3255473 : Blo 2169435 3255473 := bstep (se 2 (by rfl) ⟨1220802, by rfl⟩ : syracuseStep 3255473 = 2441605) B2441605
theorem B2170315 : Blo 2169435 2170315 := bstep (se 1 (by rfl) ⟨1627736, by rfl⟩ : syracuseStep 2170315 = 3255473) B3255473
theorem B4635245 : Blo 2169435 4635245 := bbase (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) (by norm_num)
theorem B3090163 : Blo 2169435 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B4120217 : Blo 2169435 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B2746811 : Blo 2169435 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B7324829 : Blo 2169435 7324829 := bstep (se 3 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 7324829 = 2746811) B2746811
theorem B4883219 : Blo 2169435 4883219 := bstep (se 1 (by rfl) ⟨3662414, by rfl⟩ : syracuseStep 4883219 = 7324829) B7324829
theorem B3255479 : Blo 2169435 3255479 := bstep (se 1 (by rfl) ⟨2441609, by rfl⟩ : syracuseStep 3255479 = 4883219) B4883219
theorem B2170319 : Blo 2169435 2170319 := bstep (se 1 (by rfl) ⟨1627739, by rfl⟩ : syracuseStep 2170319 = 3255479) B3255479
theorem B3255485 : Blo 2169435 3255485 := bbase (se 3 (by rfl) ⟨610403, by rfl⟩ : syracuseStep 3255485 = 1220807) (by norm_num)
theorem B2170323 : Blo 2169435 2170323 := bstep (se 1 (by rfl) ⟨1627742, by rfl⟩ : syracuseStep 2170323 = 3255485) B3255485
theorem B4883237 : Blo 2169435 4883237 := bbase (se 4 (by rfl) ⟨457803, by rfl⟩ : syracuseStep 4883237 = 915607) (by norm_num)
theorem B3255491 : Blo 2169435 3255491 := bstep (se 1 (by rfl) ⟨2441618, by rfl⟩ : syracuseStep 3255491 = 4883237) B4883237
theorem B2170327 : Blo 2169435 2170327 := bstep (se 1 (by rfl) ⟨1627745, by rfl⟩ : syracuseStep 2170327 = 3255491) B3255491
theorem B5493653 : Blo 2169435 5493653 := bbase (se 6 (by rfl) ⟨128757, by rfl⟩ : syracuseStep 5493653 = 257515) (by norm_num)
theorem B3662435 : Blo 2169435 3662435 := bstep (se 1 (by rfl) ⟨2746826, by rfl⟩ : syracuseStep 3662435 = 5493653) B5493653
theorem B2441623 : Blo 2169435 2441623 := bstep (se 1 (by rfl) ⟨1831217, by rfl⟩ : syracuseStep 2441623 = 3662435) B3662435
theorem B3255497 : Blo 2169435 3255497 := bstep (se 2 (by rfl) ⟨1220811, by rfl⟩ : syracuseStep 3255497 = 2441623) B2441623
theorem B2170331 : Blo 2169435 2170331 := bstep (se 1 (by rfl) ⟨1627748, by rfl⟩ : syracuseStep 2170331 = 3255497) B3255497
theorem B9899765 : Blo 2169435 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B6599843 : Blo 2169435 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B4399895 : Blo 2169435 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B2933263 : Blo 2169435 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B3911017 : Blo 2169435 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B5214689 : Blo 2169435 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B3476459 : Blo 2169435 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B9270557 : Blo 2169435 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B6180371 : Blo 2169435 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B4120247 : Blo 2169435 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B10987325 : Blo 2169435 10987325 := bstep (se 3 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 10987325 = 4120247) B4120247
theorem B7324883 : Blo 2169435 7324883 := bstep (se 1 (by rfl) ⟨5493662, by rfl⟩ : syracuseStep 7324883 = 10987325) B10987325
theorem B4883255 : Blo 2169435 4883255 := bstep (se 1 (by rfl) ⟨3662441, by rfl⟩ : syracuseStep 4883255 = 7324883) B7324883
theorem B3255503 : Blo 2169435 3255503 := bstep (se 1 (by rfl) ⟨2441627, by rfl⟩ : syracuseStep 3255503 = 4883255) B4883255
theorem B2170335 : Blo 2169435 2170335 := bstep (se 1 (by rfl) ⟨1627751, by rfl⟩ : syracuseStep 2170335 = 3255503) B3255503
theorem B3255509 : Blo 2169435 3255509 := bbase (se 7 (by rfl) ⟨38150, by rfl⟩ : syracuseStep 3255509 = 76301) (by norm_num)
theorem B2170339 : Blo 2169435 2170339 := bstep (se 1 (by rfl) ⟨1627754, by rfl⟩ : syracuseStep 2170339 = 3255509) B3255509
theorem B3090197 : Blo 2169435 3090197 := bbase (se 6 (by rfl) ⟨72426, by rfl⟩ : syracuseStep 3090197 = 144853) (by norm_num)
theorem B8240525 : Blo 2169435 8240525 := bstep (se 3 (by rfl) ⟨1545098, by rfl⟩ : syracuseStep 8240525 = 3090197) B3090197
theorem B5493683 : Blo 2169435 5493683 := bstep (se 1 (by rfl) ⟨4120262, by rfl⟩ : syracuseStep 5493683 = 8240525) B8240525
theorem B3662455 : Blo 2169435 3662455 := bstep (se 1 (by rfl) ⟨2746841, by rfl⟩ : syracuseStep 3662455 = 5493683) B5493683
theorem B4883273 : Blo 2169435 4883273 := bstep (se 2 (by rfl) ⟨1831227, by rfl⟩ : syracuseStep 4883273 = 3662455) B3662455
theorem B3255515 : Blo 2169435 3255515 := bstep (se 1 (by rfl) ⟨2441636, by rfl⟩ : syracuseStep 3255515 = 4883273) B4883273
theorem B2170343 : Blo 2169435 2170343 := bstep (se 1 (by rfl) ⟨1627757, by rfl⟩ : syracuseStep 2170343 = 3255515) B3255515
theorem B2441641 : Blo 2169435 2441641 := bbase (se 2 (by rfl) ⟨915615, by rfl⟩ : syracuseStep 2441641 = 1831231) (by norm_num)
theorem B3255521 : Blo 2169435 3255521 := bstep (se 2 (by rfl) ⟨1220820, by rfl⟩ : syracuseStep 3255521 = 2441641) B2441641
theorem B2170347 : Blo 2169435 2170347 := bstep (se 1 (by rfl) ⟨1627760, by rfl⟩ : syracuseStep 2170347 = 3255521) B3255521
theorem B4698557 : Blo 2169435 4698557 := bbase (se 3 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 4698557 = 1761959) (by norm_num)
theorem B3132371 : Blo 2169435 3132371 := bstep (se 1 (by rfl) ⟨2349278, by rfl⟩ : syracuseStep 3132371 = 4698557) B4698557
theorem B8352989 : Blo 2169435 8352989 := bstep (se 3 (by rfl) ⟨1566185, by rfl⟩ : syracuseStep 8352989 = 3132371) B3132371
theorem B5568659 : Blo 2169435 5568659 := bstep (se 1 (by rfl) ⟨4176494, by rfl⟩ : syracuseStep 5568659 = 8352989) B8352989
theorem B3712439 : Blo 2169435 3712439 := bstep (se 1 (by rfl) ⟨2784329, by rfl⟩ : syracuseStep 3712439 = 5568659) B5568659
theorem B2474959 : Blo 2169435 2474959 := bstep (se 1 (by rfl) ⟨1856219, by rfl⟩ : syracuseStep 2474959 = 3712439) B3712439
theorem B3299945 : Blo 2169435 3299945 := bstep (se 2 (by rfl) ⟨1237479, by rfl⟩ : syracuseStep 3299945 = 2474959) B2474959
theorem B8799853 : Blo 2169435 8799853 := bstep (se 3 (by rfl) ⟨1649972, by rfl⟩ : syracuseStep 8799853 = 3299945) B3299945
theorem B11733137 : Blo 2169435 11733137 := bstep (se 2 (by rfl) ⟨4399926, by rfl⟩ : syracuseStep 11733137 = 8799853) B8799853
theorem B7822091 : Blo 2169435 7822091 := bstep (se 1 (by rfl) ⟨5866568, by rfl⟩ : syracuseStep 7822091 = 11733137) B11733137
theorem B5214727 : Blo 2169435 5214727 := bstep (se 1 (by rfl) ⟨3911045, by rfl⟩ : syracuseStep 5214727 = 7822091) B7822091
theorem B6952969 : Blo 2169435 6952969 := bstep (se 2 (by rfl) ⟨2607363, by rfl⟩ : syracuseStep 6952969 = 5214727) B5214727
theorem B9270625 : Blo 2169435 9270625 := bstep (se 2 (by rfl) ⟨3476484, by rfl⟩ : syracuseStep 9270625 = 6952969) B6952969
theorem B12360833 : Blo 2169435 12360833 := bstep (se 2 (by rfl) ⟨4635312, by rfl⟩ : syracuseStep 12360833 = 9270625) B9270625
theorem B8240555 : Blo 2169435 8240555 := bstep (se 1 (by rfl) ⟨6180416, by rfl⟩ : syracuseStep 8240555 = 12360833) B12360833
theorem B5493703 : Blo 2169435 5493703 := bstep (se 1 (by rfl) ⟨4120277, by rfl⟩ : syracuseStep 5493703 = 8240555) B8240555
theorem B7324937 : Blo 2169435 7324937 := bstep (se 2 (by rfl) ⟨2746851, by rfl⟩ : syracuseStep 7324937 = 5493703) B5493703
theorem B4883291 : Blo 2169435 4883291 := bstep (se 1 (by rfl) ⟨3662468, by rfl⟩ : syracuseStep 4883291 = 7324937) B7324937
theorem B3255527 : Blo 2169435 3255527 := bstep (se 1 (by rfl) ⟨2441645, by rfl⟩ : syracuseStep 3255527 = 4883291) B4883291
theorem B2170351 : Blo 2169435 2170351 := bstep (se 1 (by rfl) ⟨1627763, by rfl⟩ : syracuseStep 2170351 = 3255527) B3255527
theorem B3255533 : Blo 2169435 3255533 := bbase (se 3 (by rfl) ⟨610412, by rfl⟩ : syracuseStep 3255533 = 1220825) (by norm_num)
theorem B2170355 : Blo 2169435 2170355 := bstep (se 1 (by rfl) ⟨1627766, by rfl⟩ : syracuseStep 2170355 = 3255533) B3255533
theorem B4883309 : Blo 2169435 4883309 := bbase (se 3 (by rfl) ⟨915620, by rfl⟩ : syracuseStep 4883309 = 1831241) (by norm_num)
theorem B3255539 : Blo 2169435 3255539 := bstep (se 1 (by rfl) ⟨2441654, by rfl⟩ : syracuseStep 3255539 = 4883309) B4883309
theorem B2170359 : Blo 2169435 2170359 := bstep (se 1 (by rfl) ⟨1627769, by rfl⟩ : syracuseStep 2170359 = 3255539) B3255539
theorem B4120301 : Blo 2169435 4120301 := bbase (se 3 (by rfl) ⟨772556, by rfl⟩ : syracuseStep 4120301 = 1545113) (by norm_num)
theorem B2746867 : Blo 2169435 2746867 := bstep (se 1 (by rfl) ⟨2060150, by rfl⟩ : syracuseStep 2746867 = 4120301) B4120301
theorem B3662489 : Blo 2169435 3662489 := bstep (se 2 (by rfl) ⟨1373433, by rfl⟩ : syracuseStep 3662489 = 2746867) B2746867
theorem B2441659 : Blo 2169435 2441659 := bstep (se 1 (by rfl) ⟨1831244, by rfl⟩ : syracuseStep 2441659 = 3662489) B3662489
theorem B3255545 : Blo 2169435 3255545 := bstep (se 2 (by rfl) ⟨1220829, by rfl⟩ : syracuseStep 3255545 = 2441659) B2441659
theorem B2170363 : Blo 2169435 2170363 := bstep (se 1 (by rfl) ⟨1627772, by rfl⟩ : syracuseStep 2170363 = 3255545) B3255545
theorem B2474977 : Blo 2169435 2474977 := bbase (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) (by norm_num)
theorem B3299969 : Blo 2169435 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B2199979 : Blo 2169435 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B11733221 : Blo 2169435 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B31288589 : Blo 2169435 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B20859059 : Blo 2169435 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B55624157 : Blo 2169435 55624157 := bstep (se 3 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 55624157 = 20859059) B20859059
theorem B37082771 : Blo 2169435 37082771 := bstep (se 1 (by rfl) ⟨27812078, by rfl⟩ : syracuseStep 37082771 = 55624157) B55624157
theorem B24721847 : Blo 2169435 24721847 := bstep (se 1 (by rfl) ⟨18541385, by rfl⟩ : syracuseStep 24721847 = 37082771) B37082771
theorem B16481231 : Blo 2169435 16481231 := bstep (se 1 (by rfl) ⟨12360923, by rfl⟩ : syracuseStep 16481231 = 24721847) B24721847
theorem B10987487 : Blo 2169435 10987487 := bstep (se 1 (by rfl) ⟨8240615, by rfl⟩ : syracuseStep 10987487 = 16481231) B16481231
theorem B7324991 : Blo 2169435 7324991 := bstep (se 1 (by rfl) ⟨5493743, by rfl⟩ : syracuseStep 7324991 = 10987487) B10987487
theorem B4883327 : Blo 2169435 4883327 := bstep (se 1 (by rfl) ⟨3662495, by rfl⟩ : syracuseStep 4883327 = 7324991) B7324991
theorem B3255551 : Blo 2169435 3255551 := bstep (se 1 (by rfl) ⟨2441663, by rfl⟩ : syracuseStep 3255551 = 4883327) B4883327
theorem B2170367 : Blo 2169435 2170367 := bstep (se 1 (by rfl) ⟨1627775, by rfl⟩ : syracuseStep 2170367 = 3255551) B3255551
theorem B3255557 : Blo 2169435 3255557 := bbase (se 4 (by rfl) ⟨305208, by rfl⟩ : syracuseStep 3255557 = 610417) (by norm_num)
theorem B2170371 : Blo 2169435 2170371 := bstep (se 1 (by rfl) ⟨1627778, by rfl⟩ : syracuseStep 2170371 = 3255557) B3255557
theorem B3662509 : Blo 2169435 3662509 := bbase (se 3 (by rfl) ⟨686720, by rfl⟩ : syracuseStep 3662509 = 1373441) (by norm_num)
theorem B4883345 : Blo 2169435 4883345 := bstep (se 2 (by rfl) ⟨1831254, by rfl⟩ : syracuseStep 4883345 = 3662509) B3662509
theorem B3255563 : Blo 2169435 3255563 := bstep (se 1 (by rfl) ⟨2441672, by rfl⟩ : syracuseStep 3255563 = 4883345) B4883345
theorem B2170375 : Blo 2169435 2170375 := bstep (se 1 (by rfl) ⟨1627781, by rfl⟩ : syracuseStep 2170375 = 3255563) B3255563
theorem B2441677 : Blo 2169435 2441677 := bbase (se 3 (by rfl) ⟨457814, by rfl⟩ : syracuseStep 2441677 = 915629) (by norm_num)
theorem B3255569 : Blo 2169435 3255569 := bstep (se 2 (by rfl) ⟨1220838, by rfl⟩ : syracuseStep 3255569 = 2441677) B2441677
theorem B2170379 : Blo 2169435 2170379 := bstep (se 1 (by rfl) ⟨1627784, by rfl⟩ : syracuseStep 2170379 = 3255569) B3255569
theorem B7325045 : Blo 2169435 7325045 := bbase (se 5 (by rfl) ⟨343361, by rfl⟩ : syracuseStep 7325045 = 686723) (by norm_num)
theorem B4883363 : Blo 2169435 4883363 := bstep (se 1 (by rfl) ⟨3662522, by rfl⟩ : syracuseStep 4883363 = 7325045) B7325045
theorem B3255575 : Blo 2169435 3255575 := bstep (se 1 (by rfl) ⟨2441681, by rfl⟩ : syracuseStep 3255575 = 4883363) B4883363
theorem B2170383 : Blo 2169435 2170383 := bstep (se 1 (by rfl) ⟨1627787, by rfl⟩ : syracuseStep 2170383 = 3255575) B3255575
theorem B3255581 : Blo 2169435 3255581 := bbase (se 3 (by rfl) ⟨610421, by rfl⟩ : syracuseStep 3255581 = 1220843) (by norm_num)
theorem B2170387 : Blo 2169435 2170387 := bstep (se 1 (by rfl) ⟨1627790, by rfl⟩ : syracuseStep 2170387 = 3255581) B3255581
theorem B4883381 : Blo 2169435 4883381 := bbase (se 5 (by rfl) ⟨228908, by rfl⟩ : syracuseStep 4883381 = 457817) (by norm_num)
theorem B3255587 : Blo 2169435 3255587 := bstep (se 1 (by rfl) ⟨2441690, by rfl⟩ : syracuseStep 3255587 = 4883381) B4883381
theorem B2170391 : Blo 2169435 2170391 := bstep (se 1 (by rfl) ⟨1627793, by rfl⟩ : syracuseStep 2170391 = 3255587) B3255587
theorem B15644501 : Blo 2169435 15644501 := bbase (se 9 (by rfl) ⟨45833, by rfl⟩ : syracuseStep 15644501 = 91667) (by norm_num)
theorem B10429667 : Blo 2169435 10429667 := bstep (se 1 (by rfl) ⟨7822250, by rfl⟩ : syracuseStep 10429667 = 15644501) B15644501
theorem B6953111 : Blo 2169435 6953111 := bstep (se 1 (by rfl) ⟨5214833, by rfl⟩ : syracuseStep 6953111 = 10429667) B10429667
theorem B4635407 : Blo 2169435 4635407 := bstep (se 1 (by rfl) ⟨3476555, by rfl⟩ : syracuseStep 4635407 = 6953111) B6953111
theorem B12361085 : Blo 2169435 12361085 := bstep (se 3 (by rfl) ⟨2317703, by rfl⟩ : syracuseStep 12361085 = 4635407) B4635407
theorem B8240723 : Blo 2169435 8240723 := bstep (se 1 (by rfl) ⟨6180542, by rfl⟩ : syracuseStep 8240723 = 12361085) B12361085
theorem B5493815 : Blo 2169435 5493815 := bstep (se 1 (by rfl) ⟨4120361, by rfl⟩ : syracuseStep 5493815 = 8240723) B8240723
theorem B3662543 : Blo 2169435 3662543 := bstep (se 1 (by rfl) ⟨2746907, by rfl⟩ : syracuseStep 3662543 = 5493815) B5493815
theorem B2441695 : Blo 2169435 2441695 := bstep (se 1 (by rfl) ⟨1831271, by rfl⟩ : syracuseStep 2441695 = 3662543) B3662543
theorem B3255593 : Blo 2169435 3255593 := bstep (se 2 (by rfl) ⟨1220847, by rfl⟩ : syracuseStep 3255593 = 2441695) B2441695
theorem B2170395 : Blo 2169435 2170395 := bstep (se 1 (by rfl) ⟨1627796, by rfl⟩ : syracuseStep 2170395 = 3255593) B3255593
theorem B10429685 : Blo 2169435 10429685 := bbase (se 5 (by rfl) ⟨488891, by rfl⟩ : syracuseStep 10429685 = 977783) (by norm_num)
theorem B6953123 : Blo 2169435 6953123 := bstep (se 1 (by rfl) ⟨5214842, by rfl⟩ : syracuseStep 6953123 = 10429685) B10429685
theorem B4635415 : Blo 2169435 4635415 := bstep (se 1 (by rfl) ⟨3476561, by rfl⟩ : syracuseStep 4635415 = 6953123) B6953123
theorem B6180553 : Blo 2169435 6180553 := bstep (se 2 (by rfl) ⟨2317707, by rfl⟩ : syracuseStep 6180553 = 4635415) B4635415
theorem B8240737 : Blo 2169435 8240737 := bstep (se 2 (by rfl) ⟨3090276, by rfl⟩ : syracuseStep 8240737 = 6180553) B6180553
theorem B10987649 : Blo 2169435 10987649 := bstep (se 2 (by rfl) ⟨4120368, by rfl⟩ : syracuseStep 10987649 = 8240737) B8240737
theorem B7325099 : Blo 2169435 7325099 := bstep (se 1 (by rfl) ⟨5493824, by rfl⟩ : syracuseStep 7325099 = 10987649) B10987649
theorem B4883399 : Blo 2169435 4883399 := bstep (se 1 (by rfl) ⟨3662549, by rfl⟩ : syracuseStep 4883399 = 7325099) B7325099
theorem B3255599 : Blo 2169435 3255599 := bstep (se 1 (by rfl) ⟨2441699, by rfl⟩ : syracuseStep 3255599 = 4883399) B4883399
theorem B2170399 : Blo 2169435 2170399 := bstep (se 1 (by rfl) ⟨1627799, by rfl⟩ : syracuseStep 2170399 = 3255599) B3255599
theorem B3255605 : Blo 2169435 3255605 := bbase (se 5 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 3255605 = 305213) (by norm_num)
theorem B2170403 : Blo 2169435 2170403 := bstep (se 1 (by rfl) ⟨1627802, by rfl⟩ : syracuseStep 2170403 = 3255605) B3255605
theorem B5493845 : Blo 2169435 5493845 := bbase (se 8 (by rfl) ⟨32190, by rfl⟩ : syracuseStep 5493845 = 64381) (by norm_num)
theorem B3662563 : Blo 2169435 3662563 := bstep (se 1 (by rfl) ⟨2746922, by rfl⟩ : syracuseStep 3662563 = 5493845) B5493845
theorem B4883417 : Blo 2169435 4883417 := bstep (se 2 (by rfl) ⟨1831281, by rfl⟩ : syracuseStep 4883417 = 3662563) B3662563
theorem B3255611 : Blo 2169435 3255611 := bstep (se 1 (by rfl) ⟨2441708, by rfl⟩ : syracuseStep 3255611 = 4883417) B4883417
theorem B2170407 : Blo 2169435 2170407 := bstep (se 1 (by rfl) ⟨1627805, by rfl⟩ : syracuseStep 2170407 = 3255611) B3255611
theorem B2441713 : Blo 2169435 2441713 := bbase (se 2 (by rfl) ⟨915642, by rfl⟩ : syracuseStep 2441713 = 1831285) (by norm_num)
theorem B3255617 : Blo 2169435 3255617 := bstep (se 2 (by rfl) ⟨1220856, by rfl⟩ : syracuseStep 3255617 = 2441713) B2441713
theorem B2170411 : Blo 2169435 2170411 := bstep (se 1 (by rfl) ⟨1627808, by rfl⟩ : syracuseStep 2170411 = 3255617) B3255617
theorem B3712549 : Blo 2169435 3712549 := bbase (se 4 (by rfl) ⟨348051, by rfl⟩ : syracuseStep 3712549 = 696103) (by norm_num)
theorem B4950065 : Blo 2169435 4950065 := bstep (se 2 (by rfl) ⟨1856274, by rfl⟩ : syracuseStep 4950065 = 3712549) B3712549
theorem B3300043 : Blo 2169435 3300043 := bstep (se 1 (by rfl) ⟨2475032, by rfl⟩ : syracuseStep 3300043 = 4950065) B4950065
theorem B4400057 : Blo 2169435 4400057 := bstep (se 2 (by rfl) ⟨1650021, by rfl⟩ : syracuseStep 4400057 = 3300043) B3300043
theorem B2933371 : Blo 2169435 2933371 := bstep (se 1 (by rfl) ⟨2200028, by rfl⟩ : syracuseStep 2933371 = 4400057) B4400057
theorem B3911161 : Blo 2169435 3911161 := bstep (se 2 (by rfl) ⟨1466685, by rfl⟩ : syracuseStep 3911161 = 2933371) B2933371
theorem B5214881 : Blo 2169435 5214881 := bstep (se 2 (by rfl) ⟨1955580, by rfl⟩ : syracuseStep 5214881 = 3911161) B3911161
theorem B13906349 : Blo 2169435 13906349 := bstep (se 3 (by rfl) ⟨2607440, by rfl⟩ : syracuseStep 13906349 = 5214881) B5214881
theorem B9270899 : Blo 2169435 9270899 := bstep (se 1 (by rfl) ⟨6953174, by rfl⟩ : syracuseStep 9270899 = 13906349) B13906349
theorem B6180599 : Blo 2169435 6180599 := bstep (se 1 (by rfl) ⟨4635449, by rfl⟩ : syracuseStep 6180599 = 9270899) B9270899
theorem B4120399 : Blo 2169435 4120399 := bstep (se 1 (by rfl) ⟨3090299, by rfl⟩ : syracuseStep 4120399 = 6180599) B6180599
theorem B5493865 : Blo 2169435 5493865 := bstep (se 2 (by rfl) ⟨2060199, by rfl⟩ : syracuseStep 5493865 = 4120399) B4120399
theorem B7325153 : Blo 2169435 7325153 := bstep (se 2 (by rfl) ⟨2746932, by rfl⟩ : syracuseStep 7325153 = 5493865) B5493865
theorem B4883435 : Blo 2169435 4883435 := bstep (se 1 (by rfl) ⟨3662576, by rfl⟩ : syracuseStep 4883435 = 7325153) B7325153
theorem B3255623 : Blo 2169435 3255623 := bstep (se 1 (by rfl) ⟨2441717, by rfl⟩ : syracuseStep 3255623 = 4883435) B4883435
theorem B2170415 : Blo 2169435 2170415 := bstep (se 1 (by rfl) ⟨1627811, by rfl⟩ : syracuseStep 2170415 = 3255623) B3255623
theorem B3255629 : Blo 2169435 3255629 := bbase (se 3 (by rfl) ⟨610430, by rfl⟩ : syracuseStep 3255629 = 1220861) (by norm_num)
theorem B2170419 : Blo 2169435 2170419 := bstep (se 1 (by rfl) ⟨1627814, by rfl⟩ : syracuseStep 2170419 = 3255629) B3255629
theorem B4883453 : Blo 2169435 4883453 := bbase (se 3 (by rfl) ⟨915647, by rfl⟩ : syracuseStep 4883453 = 1831295) (by norm_num)
theorem B3255635 : Blo 2169435 3255635 := bstep (se 1 (by rfl) ⟨2441726, by rfl⟩ : syracuseStep 3255635 = 4883453) B4883453
theorem B2170423 : Blo 2169435 2170423 := bstep (se 1 (by rfl) ⟨1627817, by rfl⟩ : syracuseStep 2170423 = 3255635) B3255635
theorem B3662597 : Blo 2169435 3662597 := bbase (se 4 (by rfl) ⟨343368, by rfl⟩ : syracuseStep 3662597 = 686737) (by norm_num)
theorem B2441731 : Blo 2169435 2441731 := bstep (se 1 (by rfl) ⟨1831298, by rfl⟩ : syracuseStep 2441731 = 3662597) B3662597
theorem B3255641 : Blo 2169435 3255641 := bstep (se 2 (by rfl) ⟨1220865, by rfl⟩ : syracuseStep 3255641 = 2441731) B2441731
theorem B2170427 : Blo 2169435 2170427 := bstep (se 1 (by rfl) ⟨1627820, by rfl⟩ : syracuseStep 2170427 = 3255641) B3255641
theorem B16481717 : Blo 2169435 16481717 := bbase (se 5 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 16481717 = 1545161) (by norm_num)
theorem B10987811 : Blo 2169435 10987811 := bstep (se 1 (by rfl) ⟨8240858, by rfl⟩ : syracuseStep 10987811 = 16481717) B16481717
theorem B7325207 : Blo 2169435 7325207 := bstep (se 1 (by rfl) ⟨5493905, by rfl⟩ : syracuseStep 7325207 = 10987811) B10987811
theorem B4883471 : Blo 2169435 4883471 := bstep (se 1 (by rfl) ⟨3662603, by rfl⟩ : syracuseStep 4883471 = 7325207) B7325207
theorem B3255647 : Blo 2169435 3255647 := bstep (se 1 (by rfl) ⟨2441735, by rfl⟩ : syracuseStep 3255647 = 4883471) B4883471
theorem B2170431 : Blo 2169435 2170431 := bstep (se 1 (by rfl) ⟨1627823, by rfl⟩ : syracuseStep 2170431 = 3255647) B3255647
theorem B3255653 : Blo 2169435 3255653 := bbase (se 4 (by rfl) ⟨305217, by rfl⟩ : syracuseStep 3255653 = 610435) (by norm_num)
theorem B2170435 : Blo 2169435 2170435 := bstep (se 1 (by rfl) ⟨1627826, by rfl⟩ : syracuseStep 2170435 = 3255653) B3255653
theorem B4120445 : Blo 2169435 4120445 := bbase (se 3 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 4120445 = 1545167) (by norm_num)
theorem B2746963 : Blo 2169435 2746963 := bstep (se 1 (by rfl) ⟨2060222, by rfl⟩ : syracuseStep 2746963 = 4120445) B4120445
theorem B3662617 : Blo 2169435 3662617 := bstep (se 2 (by rfl) ⟨1373481, by rfl⟩ : syracuseStep 3662617 = 2746963) B2746963
theorem B4883489 : Blo 2169435 4883489 := bstep (se 2 (by rfl) ⟨1831308, by rfl⟩ : syracuseStep 4883489 = 3662617) B3662617
theorem B3255659 : Blo 2169435 3255659 := bstep (se 1 (by rfl) ⟨2441744, by rfl⟩ : syracuseStep 3255659 = 4883489) B4883489
theorem B2170439 : Blo 2169435 2170439 := bstep (se 1 (by rfl) ⟨1627829, by rfl⟩ : syracuseStep 2170439 = 3255659) B3255659
theorem B2441749 : Blo 2169435 2441749 := bbase (se 6 (by rfl) ⟨57228, by rfl⟩ : syracuseStep 2441749 = 114457) (by norm_num)
theorem B3255665 : Blo 2169435 3255665 := bstep (se 2 (by rfl) ⟨1220874, by rfl⟩ : syracuseStep 3255665 = 2441749) B2441749
theorem B2170443 : Blo 2169435 2170443 := bstep (se 1 (by rfl) ⟨1627832, by rfl⟩ : syracuseStep 2170443 = 3255665) B3255665
theorem B2746973 : Blo 2169435 2746973 := bbase (se 3 (by rfl) ⟨515057, by rfl⟩ : syracuseStep 2746973 = 1030115) (by norm_num)
theorem B7325261 : Blo 2169435 7325261 := bstep (se 3 (by rfl) ⟨1373486, by rfl⟩ : syracuseStep 7325261 = 2746973) B2746973
theorem B4883507 : Blo 2169435 4883507 := bstep (se 1 (by rfl) ⟨3662630, by rfl⟩ : syracuseStep 4883507 = 7325261) B7325261
theorem B3255671 : Blo 2169435 3255671 := bstep (se 1 (by rfl) ⟨2441753, by rfl⟩ : syracuseStep 3255671 = 4883507) B4883507
theorem B2170447 : Blo 2169435 2170447 := bstep (se 1 (by rfl) ⟨1627835, by rfl⟩ : syracuseStep 2170447 = 3255671) B3255671
theorem B3255677 : Blo 2169435 3255677 := bbase (se 3 (by rfl) ⟨610439, by rfl⟩ : syracuseStep 3255677 = 1220879) (by norm_num)
theorem B2170451 : Blo 2169435 2170451 := bstep (se 1 (by rfl) ⟨1627838, by rfl⟩ : syracuseStep 2170451 = 3255677) B3255677
theorem B4883525 : Blo 2169435 4883525 := bbase (se 4 (by rfl) ⟨457830, by rfl⟩ : syracuseStep 4883525 = 915661) (by norm_num)
theorem B3255683 : Blo 2169435 3255683 := bstep (se 1 (by rfl) ⟨2441762, by rfl⟩ : syracuseStep 3255683 = 4883525) B4883525
theorem B2170455 : Blo 2169435 2170455 := bstep (se 1 (by rfl) ⟨1627841, by rfl⟩ : syracuseStep 2170455 = 3255683) B3255683
theorem B6180725 : Blo 2169435 6180725 := bbase (se 5 (by rfl) ⟨289721, by rfl⟩ : syracuseStep 6180725 = 579443) (by norm_num)
theorem B4120483 : Blo 2169435 4120483 := bstep (se 1 (by rfl) ⟨3090362, by rfl⟩ : syracuseStep 4120483 = 6180725) B6180725
theorem B5493977 : Blo 2169435 5493977 := bstep (se 2 (by rfl) ⟨2060241, by rfl⟩ : syracuseStep 5493977 = 4120483) B4120483
theorem B3662651 : Blo 2169435 3662651 := bstep (se 1 (by rfl) ⟨2746988, by rfl⟩ : syracuseStep 3662651 = 5493977) B5493977
theorem B2441767 : Blo 2169435 2441767 := bstep (se 1 (by rfl) ⟨1831325, by rfl⟩ : syracuseStep 2441767 = 3662651) B3662651
theorem B3255689 : Blo 2169435 3255689 := bstep (se 2 (by rfl) ⟨1220883, by rfl⟩ : syracuseStep 3255689 = 2441767) B2441767
theorem B2170459 : Blo 2169435 2170459 := bstep (se 1 (by rfl) ⟨1627844, by rfl⟩ : syracuseStep 2170459 = 3255689) B3255689
theorem B10987973 : Blo 2169435 10987973 := bbase (se 4 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 10987973 = 2060245) (by norm_num)
theorem B7325315 : Blo 2169435 7325315 := bstep (se 1 (by rfl) ⟨5493986, by rfl⟩ : syracuseStep 7325315 = 10987973) B10987973
theorem B4883543 : Blo 2169435 4883543 := bstep (se 1 (by rfl) ⟨3662657, by rfl⟩ : syracuseStep 4883543 = 7325315) B7325315
theorem B3255695 : Blo 2169435 3255695 := bstep (se 1 (by rfl) ⟨2441771, by rfl⟩ : syracuseStep 3255695 = 4883543) B4883543
theorem B2170463 : Blo 2169435 2170463 := bstep (se 1 (by rfl) ⟨1627847, by rfl⟩ : syracuseStep 2170463 = 3255695) B3255695
theorem B3255701 : Blo 2169435 3255701 := bbase (se 6 (by rfl) ⟨76305, by rfl⟩ : syracuseStep 3255701 = 152611) (by norm_num)
theorem B2170467 : Blo 2169435 2170467 := bstep (se 1 (by rfl) ⟨1627850, by rfl⟩ : syracuseStep 2170467 = 3255701) B3255701
theorem B3476677 : Blo 2169435 3476677 := bbase (se 4 (by rfl) ⟨325938, by rfl⟩ : syracuseStep 3476677 = 651877) (by norm_num)
theorem B4635569 : Blo 2169435 4635569 := bstep (se 2 (by rfl) ⟨1738338, by rfl⟩ : syracuseStep 4635569 = 3476677) B3476677
theorem B12361517 : Blo 2169435 12361517 := bstep (se 3 (by rfl) ⟨2317784, by rfl⟩ : syracuseStep 12361517 = 4635569) B4635569
theorem B8241011 : Blo 2169435 8241011 := bstep (se 1 (by rfl) ⟨6180758, by rfl⟩ : syracuseStep 8241011 = 12361517) B12361517
theorem B5494007 : Blo 2169435 5494007 := bstep (se 1 (by rfl) ⟨4120505, by rfl⟩ : syracuseStep 5494007 = 8241011) B8241011
theorem B3662671 : Blo 2169435 3662671 := bstep (se 1 (by rfl) ⟨2747003, by rfl⟩ : syracuseStep 3662671 = 5494007) B5494007
theorem B4883561 : Blo 2169435 4883561 := bstep (se 2 (by rfl) ⟨1831335, by rfl⟩ : syracuseStep 4883561 = 3662671) B3662671
theorem B3255707 : Blo 2169435 3255707 := bstep (se 1 (by rfl) ⟨2441780, by rfl⟩ : syracuseStep 3255707 = 4883561) B4883561
theorem B2170471 : Blo 2169435 2170471 := bstep (se 1 (by rfl) ⟨1627853, by rfl⟩ : syracuseStep 2170471 = 3255707) B3255707
theorem B2441785 : Blo 2169435 2441785 := bbase (se 2 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 2441785 = 1831339) (by norm_num)
theorem B3255713 : Blo 2169435 3255713 := bstep (se 2 (by rfl) ⟨1220892, by rfl⟩ : syracuseStep 3255713 = 2441785) B2441785
theorem B2170475 : Blo 2169435 2170475 := bstep (se 1 (by rfl) ⟨1627856, by rfl⟩ : syracuseStep 2170475 = 3255713) B3255713
theorem B2317793 : Blo 2169435 2317793 := bbase (se 2 (by rfl) ⟨869172, by rfl⟩ : syracuseStep 2317793 = 1738345) (by norm_num)
theorem B6180781 : Blo 2169435 6180781 := bstep (se 3 (by rfl) ⟨1158896, by rfl⟩ : syracuseStep 6180781 = 2317793) B2317793
theorem B8241041 : Blo 2169435 8241041 := bstep (se 2 (by rfl) ⟨3090390, by rfl⟩ : syracuseStep 8241041 = 6180781) B6180781
theorem B5494027 : Blo 2169435 5494027 := bstep (se 1 (by rfl) ⟨4120520, by rfl⟩ : syracuseStep 5494027 = 8241041) B8241041
theorem B7325369 : Blo 2169435 7325369 := bstep (se 2 (by rfl) ⟨2747013, by rfl⟩ : syracuseStep 7325369 = 5494027) B5494027
theorem B4883579 : Blo 2169435 4883579 := bstep (se 1 (by rfl) ⟨3662684, by rfl⟩ : syracuseStep 4883579 = 7325369) B7325369
theorem B3255719 : Blo 2169435 3255719 := bstep (se 1 (by rfl) ⟨2441789, by rfl⟩ : syracuseStep 3255719 = 4883579) B4883579
theorem B2170479 : Blo 2169435 2170479 := bstep (se 1 (by rfl) ⟨1627859, by rfl⟩ : syracuseStep 2170479 = 3255719) B3255719
theorem B3255725 : Blo 2169435 3255725 := bbase (se 3 (by rfl) ⟨610448, by rfl⟩ : syracuseStep 3255725 = 1220897) (by norm_num)
theorem B2170483 : Blo 2169435 2170483 := bstep (se 1 (by rfl) ⟨1627862, by rfl⟩ : syracuseStep 2170483 = 3255725) B3255725
theorem B4883597 : Blo 2169435 4883597 := bbase (se 3 (by rfl) ⟨915674, by rfl⟩ : syracuseStep 4883597 = 1831349) (by norm_num)
theorem B3255731 : Blo 2169435 3255731 := bstep (se 1 (by rfl) ⟨2441798, by rfl⟩ : syracuseStep 3255731 = 4883597) B4883597
theorem B2170487 : Blo 2169435 2170487 := bstep (se 1 (by rfl) ⟨1627865, by rfl⟩ : syracuseStep 2170487 = 3255731) B3255731
theorem B2747029 : Blo 2169435 2747029 := bbase (se 6 (by rfl) ⟨64383, by rfl⟩ : syracuseStep 2747029 = 128767) (by norm_num)
theorem B3662705 : Blo 2169435 3662705 := bstep (se 2 (by rfl) ⟨1373514, by rfl⟩ : syracuseStep 3662705 = 2747029) B2747029
theorem B2441803 : Blo 2169435 2441803 := bstep (se 1 (by rfl) ⟨1831352, by rfl⟩ : syracuseStep 2441803 = 3662705) B3662705
theorem B3255737 : Blo 2169435 3255737 := bstep (se 2 (by rfl) ⟨1220901, by rfl⟩ : syracuseStep 3255737 = 2441803) B2441803
theorem B2170491 : Blo 2169435 2170491 := bstep (se 1 (by rfl) ⟨1627868, by rfl⟩ : syracuseStep 2170491 = 3255737) B3255737
theorem B4950245 : Blo 2169435 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B13200653 : Blo 2169435 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B8800435 : Blo 2169435 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B11733913 : Blo 2169435 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B62580869 : Blo 2169435 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B41720579 : Blo 2169435 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B27813719 : Blo 2169435 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B18542479 : Blo 2169435 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B24723305 : Blo 2169435 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B16482203 : Blo 2169435 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B10988135 : Blo 2169435 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B7325423 : Blo 2169435 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B4883615 : Blo 2169435 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B3255743 : Blo 2169435 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B2170495 : Blo 2169435 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B3255749 : Blo 2169435 3255749 := bbase (se 4 (by rfl) ⟨305226, by rfl⟩ : syracuseStep 3255749 = 610453) (by norm_num)
theorem B2170499 : Blo 2169435 2170499 := bstep (se 1 (by rfl) ⟨1627874, by rfl⟩ : syracuseStep 2170499 = 3255749) B3255749
theorem B3662725 : Blo 2169435 3662725 := bbase (se 4 (by rfl) ⟨343380, by rfl⟩ : syracuseStep 3662725 = 686761) (by norm_num)
theorem B4883633 : Blo 2169435 4883633 := bstep (se 2 (by rfl) ⟨1831362, by rfl⟩ : syracuseStep 4883633 = 3662725) B3662725
theorem B3255755 : Blo 2169435 3255755 := bstep (se 1 (by rfl) ⟨2441816, by rfl⟩ : syracuseStep 3255755 = 4883633) B4883633
theorem B2170503 : Blo 2169435 2170503 := bstep (se 1 (by rfl) ⟨1627877, by rfl⟩ : syracuseStep 2170503 = 3255755) B3255755
theorem B2441821 : Blo 2169435 2441821 := bbase (se 3 (by rfl) ⟨457841, by rfl⟩ : syracuseStep 2441821 = 915683) (by norm_num)
theorem B3255761 : Blo 2169435 3255761 := bstep (se 2 (by rfl) ⟨1220910, by rfl⟩ : syracuseStep 3255761 = 2441821) B2441821
theorem B2170507 : Blo 2169435 2170507 := bstep (se 1 (by rfl) ⟨1627880, by rfl⟩ : syracuseStep 2170507 = 3255761) B3255761
theorem B7325477 : Blo 2169435 7325477 := bbase (se 4 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 7325477 = 1373527) (by norm_num)
theorem B4883651 : Blo 2169435 4883651 := bstep (se 1 (by rfl) ⟨3662738, by rfl⟩ : syracuseStep 4883651 = 7325477) B7325477
theorem B3255767 : Blo 2169435 3255767 := bstep (se 1 (by rfl) ⟨2441825, by rfl⟩ : syracuseStep 3255767 = 4883651) B4883651
theorem B2170511 : Blo 2169435 2170511 := bstep (se 1 (by rfl) ⟨1627883, by rfl⟩ : syracuseStep 2170511 = 3255767) B3255767
theorem B3255773 : Blo 2169435 3255773 := bbase (se 3 (by rfl) ⟨610457, by rfl⟩ : syracuseStep 3255773 = 1220915) (by norm_num)
theorem B2170515 : Blo 2169435 2170515 := bstep (se 1 (by rfl) ⟨1627886, by rfl⟩ : syracuseStep 2170515 = 3255773) B3255773
theorem B4883669 : Blo 2169435 4883669 := bbase (se 7 (by rfl) ⟨57230, by rfl⟩ : syracuseStep 4883669 = 114461) (by norm_num)
theorem B3255779 : Blo 2169435 3255779 := bstep (se 1 (by rfl) ⟨2441834, by rfl⟩ : syracuseStep 3255779 = 4883669) B4883669
theorem B2170519 : Blo 2169435 2170519 := bstep (se 1 (by rfl) ⟨1627889, by rfl⟩ : syracuseStep 2170519 = 3255779) B3255779
theorem B5215141 : Blo 2169435 5215141 := bbase (se 4 (by rfl) ⟨488919, by rfl⟩ : syracuseStep 5215141 = 977839) (by norm_num)
theorem B6953521 : Blo 2169435 6953521 := bstep (se 2 (by rfl) ⟨2607570, by rfl⟩ : syracuseStep 6953521 = 5215141) B5215141
theorem B9271361 : Blo 2169435 9271361 := bstep (se 2 (by rfl) ⟨3476760, by rfl⟩ : syracuseStep 9271361 = 6953521) B6953521
theorem B6180907 : Blo 2169435 6180907 := bstep (se 1 (by rfl) ⟨4635680, by rfl⟩ : syracuseStep 6180907 = 9271361) B9271361
theorem B8241209 : Blo 2169435 8241209 := bstep (se 2 (by rfl) ⟨3090453, by rfl⟩ : syracuseStep 8241209 = 6180907) B6180907
theorem B5494139 : Blo 2169435 5494139 := bstep (se 1 (by rfl) ⟨4120604, by rfl⟩ : syracuseStep 5494139 = 8241209) B8241209
theorem B3662759 : Blo 2169435 3662759 := bstep (se 1 (by rfl) ⟨2747069, by rfl⟩ : syracuseStep 3662759 = 5494139) B5494139
theorem B2441839 : Blo 2169435 2441839 := bstep (se 1 (by rfl) ⟨1831379, by rfl⟩ : syracuseStep 2441839 = 3662759) B3662759
theorem B3255785 : Blo 2169435 3255785 := bstep (se 2 (by rfl) ⟨1220919, by rfl⟩ : syracuseStep 3255785 = 2441839) B2441839
theorem B2170523 : Blo 2169435 2170523 := bstep (se 1 (by rfl) ⟨1627892, by rfl⟩ : syracuseStep 2170523 = 3255785) B3255785
theorem B2508929 : Blo 2169435 2508929 := bbase (se 2 (by rfl) ⟨940848, by rfl⟩ : syracuseStep 2508929 = 1881697) (by norm_num)
theorem B26761909 : Blo 2169435 26761909 := bstep (se 5 (by rfl) ⟨1254464, by rfl⟩ : syracuseStep 26761909 = 2508929) B2508929
theorem B35682545 : Blo 2169435 35682545 := bstep (se 2 (by rfl) ⟨13380954, by rfl⟩ : syracuseStep 35682545 = 26761909) B26761909
theorem B23788363 : Blo 2169435 23788363 := bstep (se 1 (by rfl) ⟨17841272, by rfl⟩ : syracuseStep 23788363 = 35682545) B35682545
theorem B31717817 : Blo 2169435 31717817 := bstep (se 2 (by rfl) ⟨11894181, by rfl⟩ : syracuseStep 31717817 = 23788363) B23788363
theorem B21145211 : Blo 2169435 21145211 := bstep (se 1 (by rfl) ⟨15858908, by rfl⟩ : syracuseStep 21145211 = 31717817) B31717817
theorem B14096807 : Blo 2169435 14096807 := bstep (se 1 (by rfl) ⟨10572605, by rfl⟩ : syracuseStep 14096807 = 21145211) B21145211
theorem B9397871 : Blo 2169435 9397871 := bstep (se 1 (by rfl) ⟨7048403, by rfl⟩ : syracuseStep 9397871 = 14096807) B14096807
theorem B6265247 : Blo 2169435 6265247 := bstep (se 1 (by rfl) ⟨4698935, by rfl⟩ : syracuseStep 6265247 = 9397871) B9397871
theorem B16707325 : Blo 2169435 16707325 := bstep (se 3 (by rfl) ⟨3132623, by rfl⟩ : syracuseStep 16707325 = 6265247) B6265247
theorem B22276433 : Blo 2169435 22276433 := bstep (se 2 (by rfl) ⟨8353662, by rfl⟩ : syracuseStep 22276433 = 16707325) B16707325
theorem B14850955 : Blo 2169435 14850955 := bstep (se 1 (by rfl) ⟨11138216, by rfl⟩ : syracuseStep 14850955 = 22276433) B22276433
theorem B19801273 : Blo 2169435 19801273 := bstep (se 2 (by rfl) ⟨7425477, by rfl⟩ : syracuseStep 19801273 = 14850955) B14850955
theorem B26401697 : Blo 2169435 26401697 := bstep (se 2 (by rfl) ⟨9900636, by rfl⟩ : syracuseStep 26401697 = 19801273) B19801273
theorem B17601131 : Blo 2169435 17601131 := bstep (se 1 (by rfl) ⟨13200848, by rfl⟩ : syracuseStep 17601131 = 26401697) B26401697
theorem B11734087 : Blo 2169435 11734087 := bstep (se 1 (by rfl) ⟨8800565, by rfl⟩ : syracuseStep 11734087 = 17601131) B17601131
theorem B15645449 : Blo 2169435 15645449 := bstep (se 2 (by rfl) ⟨5867043, by rfl⟩ : syracuseStep 15645449 = 11734087) B11734087
theorem B10430299 : Blo 2169435 10430299 := bstep (se 1 (by rfl) ⟨7822724, by rfl⟩ : syracuseStep 10430299 = 15645449) B15645449
theorem B13907065 : Blo 2169435 13907065 := bstep (se 2 (by rfl) ⟨5215149, by rfl⟩ : syracuseStep 13907065 = 10430299) B10430299
theorem B18542753 : Blo 2169435 18542753 := bstep (se 2 (by rfl) ⟨6953532, by rfl⟩ : syracuseStep 18542753 = 13907065) B13907065
theorem B12361835 : Blo 2169435 12361835 := bstep (se 1 (by rfl) ⟨9271376, by rfl⟩ : syracuseStep 12361835 = 18542753) B18542753
theorem B8241223 : Blo 2169435 8241223 := bstep (se 1 (by rfl) ⟨6180917, by rfl⟩ : syracuseStep 8241223 = 12361835) B12361835
theorem B10988297 : Blo 2169435 10988297 := bstep (se 2 (by rfl) ⟨4120611, by rfl⟩ : syracuseStep 10988297 = 8241223) B8241223
theorem B7325531 : Blo 2169435 7325531 := bstep (se 1 (by rfl) ⟨5494148, by rfl⟩ : syracuseStep 7325531 = 10988297) B10988297
theorem B4883687 : Blo 2169435 4883687 := bstep (se 1 (by rfl) ⟨3662765, by rfl⟩ : syracuseStep 4883687 = 7325531) B7325531
theorem B3255791 : Blo 2169435 3255791 := bstep (se 1 (by rfl) ⟨2441843, by rfl⟩ : syracuseStep 3255791 = 4883687) B4883687
theorem B2170527 : Blo 2169435 2170527 := bstep (se 1 (by rfl) ⟨1627895, by rfl⟩ : syracuseStep 2170527 = 3255791) B3255791
theorem B3255797 : Blo 2169435 3255797 := bbase (se 5 (by rfl) ⟨152615, by rfl⟩ : syracuseStep 3255797 = 305231) (by norm_num)
theorem B2170531 : Blo 2169435 2170531 := bstep (se 1 (by rfl) ⟨1627898, by rfl⟩ : syracuseStep 2170531 = 3255797) B3255797
theorem B2317853 : Blo 2169435 2317853 := bbase (se 3 (by rfl) ⟨434597, by rfl⟩ : syracuseStep 2317853 = 869195) (by norm_num)
theorem B6180941 : Blo 2169435 6180941 := bstep (se 3 (by rfl) ⟨1158926, by rfl⟩ : syracuseStep 6180941 = 2317853) B2317853
theorem B4120627 : Blo 2169435 4120627 := bstep (se 1 (by rfl) ⟨3090470, by rfl⟩ : syracuseStep 4120627 = 6180941) B6180941
theorem B5494169 : Blo 2169435 5494169 := bstep (se 2 (by rfl) ⟨2060313, by rfl⟩ : syracuseStep 5494169 = 4120627) B4120627
theorem B3662779 : Blo 2169435 3662779 := bstep (se 1 (by rfl) ⟨2747084, by rfl⟩ : syracuseStep 3662779 = 5494169) B5494169
theorem B4883705 : Blo 2169435 4883705 := bstep (se 2 (by rfl) ⟨1831389, by rfl⟩ : syracuseStep 4883705 = 3662779) B3662779
theorem B3255803 : Blo 2169435 3255803 := bstep (se 1 (by rfl) ⟨2441852, by rfl⟩ : syracuseStep 3255803 = 4883705) B4883705
theorem B2170535 : Blo 2169435 2170535 := bstep (se 1 (by rfl) ⟨1627901, by rfl⟩ : syracuseStep 2170535 = 3255803) B3255803
theorem B2441857 : Blo 2169435 2441857 := bbase (se 2 (by rfl) ⟨915696, by rfl⟩ : syracuseStep 2441857 = 1831393) (by norm_num)
theorem B3255809 : Blo 2169435 3255809 := bstep (se 2 (by rfl) ⟨1220928, by rfl⟩ : syracuseStep 3255809 = 2441857) B2441857
theorem B2170539 : Blo 2169435 2170539 := bstep (se 1 (by rfl) ⟨1627904, by rfl⟩ : syracuseStep 2170539 = 3255809) B3255809
theorem B5494189 : Blo 2169435 5494189 := bbase (se 3 (by rfl) ⟨1030160, by rfl⟩ : syracuseStep 5494189 = 2060321) (by norm_num)
theorem B7325585 : Blo 2169435 7325585 := bstep (se 2 (by rfl) ⟨2747094, by rfl⟩ : syracuseStep 7325585 = 5494189) B5494189
theorem B4883723 : Blo 2169435 4883723 := bstep (se 1 (by rfl) ⟨3662792, by rfl⟩ : syracuseStep 4883723 = 7325585) B7325585
theorem B3255815 : Blo 2169435 3255815 := bstep (se 1 (by rfl) ⟨2441861, by rfl⟩ : syracuseStep 3255815 = 4883723) B4883723
theorem B2170543 : Blo 2169435 2170543 := bstep (se 1 (by rfl) ⟨1627907, by rfl⟩ : syracuseStep 2170543 = 3255815) B3255815
theorem B3255821 : Blo 2169435 3255821 := bbase (se 3 (by rfl) ⟨610466, by rfl⟩ : syracuseStep 3255821 = 1220933) (by norm_num)
theorem B2170547 : Blo 2169435 2170547 := bstep (se 1 (by rfl) ⟨1627910, by rfl⟩ : syracuseStep 2170547 = 3255821) B3255821
theorem B4883741 : Blo 2169435 4883741 := bbase (se 3 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 4883741 = 1831403) (by norm_num)
theorem B3255827 : Blo 2169435 3255827 := bstep (se 1 (by rfl) ⟨2441870, by rfl⟩ : syracuseStep 3255827 = 4883741) B4883741
theorem B2170551 : Blo 2169435 2170551 := bstep (se 1 (by rfl) ⟨1627913, by rfl⟩ : syracuseStep 2170551 = 3255827) B3255827
theorem B3662813 : Blo 2169435 3662813 := bbase (se 3 (by rfl) ⟨686777, by rfl⟩ : syracuseStep 3662813 = 1373555) (by norm_num)
theorem B2441875 : Blo 2169435 2441875 := bstep (se 1 (by rfl) ⟨1831406, by rfl⟩ : syracuseStep 2441875 = 3662813) B3662813
theorem B3255833 : Blo 2169435 3255833 := bstep (se 2 (by rfl) ⟨1220937, by rfl⟩ : syracuseStep 3255833 = 2441875) B2441875
theorem B2170555 : Blo 2169435 2170555 := bstep (se 1 (by rfl) ⟨1627916, by rfl⟩ : syracuseStep 2170555 = 3255833) B3255833
theorem B10430453 : Blo 2169435 10430453 := bbase (se 5 (by rfl) ⟨488927, by rfl⟩ : syracuseStep 10430453 = 977855) (by norm_num)
theorem B6953635 : Blo 2169435 6953635 := bstep (se 1 (by rfl) ⟨5215226, by rfl⟩ : syracuseStep 6953635 = 10430453) B10430453
theorem B9271513 : Blo 2169435 9271513 := bstep (se 2 (by rfl) ⟨3476817, by rfl⟩ : syracuseStep 9271513 = 6953635) B6953635
theorem B12362017 : Blo 2169435 12362017 := bstep (se 2 (by rfl) ⟨4635756, by rfl⟩ : syracuseStep 12362017 = 9271513) B9271513
theorem B16482689 : Blo 2169435 16482689 := bstep (se 2 (by rfl) ⟨6181008, by rfl⟩ : syracuseStep 16482689 = 12362017) B12362017
theorem B10988459 : Blo 2169435 10988459 := bstep (se 1 (by rfl) ⟨8241344, by rfl⟩ : syracuseStep 10988459 = 16482689) B16482689
theorem B7325639 : Blo 2169435 7325639 := bstep (se 1 (by rfl) ⟨5494229, by rfl⟩ : syracuseStep 7325639 = 10988459) B10988459
theorem B4883759 : Blo 2169435 4883759 := bstep (se 1 (by rfl) ⟨3662819, by rfl⟩ : syracuseStep 4883759 = 7325639) B7325639
theorem B3255839 : Blo 2169435 3255839 := bstep (se 1 (by rfl) ⟨2441879, by rfl⟩ : syracuseStep 3255839 = 4883759) B4883759
theorem B2170559 : Blo 2169435 2170559 := bstep (se 1 (by rfl) ⟨1627919, by rfl⟩ : syracuseStep 2170559 = 3255839) B3255839
theorem B3255845 : Blo 2169435 3255845 := bbase (se 4 (by rfl) ⟨305235, by rfl⟩ : syracuseStep 3255845 = 610471) (by norm_num)
theorem B2170563 : Blo 2169435 2170563 := bstep (se 1 (by rfl) ⟨1627922, by rfl⟩ : syracuseStep 2170563 = 3255845) B3255845
theorem B2747125 : Blo 2169435 2747125 := bbase (se 5 (by rfl) ⟨128771, by rfl⟩ : syracuseStep 2747125 = 257543) (by norm_num)
theorem B3662833 : Blo 2169435 3662833 := bstep (se 2 (by rfl) ⟨1373562, by rfl⟩ : syracuseStep 3662833 = 2747125) B2747125
theorem B4883777 : Blo 2169435 4883777 := bstep (se 2 (by rfl) ⟨1831416, by rfl⟩ : syracuseStep 4883777 = 3662833) B3662833
theorem B3255851 : Blo 2169435 3255851 := bstep (se 1 (by rfl) ⟨2441888, by rfl⟩ : syracuseStep 3255851 = 4883777) B4883777
theorem B2170567 : Blo 2169435 2170567 := bstep (se 1 (by rfl) ⟨1627925, by rfl⟩ : syracuseStep 2170567 = 3255851) B3255851
theorem B2441893 : Blo 2169435 2441893 := bbase (se 4 (by rfl) ⟨228927, by rfl⟩ : syracuseStep 2441893 = 457855) (by norm_num)
theorem B3255857 : Blo 2169435 3255857 := bstep (se 2 (by rfl) ⟨1220946, by rfl⟩ : syracuseStep 3255857 = 2441893) B2441893
theorem B2170571 : Blo 2169435 2170571 := bstep (se 1 (by rfl) ⟨1627928, by rfl⟩ : syracuseStep 2170571 = 3255857) B3255857
theorem B5286421 : Blo 2169435 5286421 := bbase (se 6 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 5286421 = 247801) (by norm_num)
theorem B7048561 : Blo 2169435 7048561 := bstep (se 2 (by rfl) ⟨2643210, by rfl⟩ : syracuseStep 7048561 = 5286421) B5286421
theorem B9398081 : Blo 2169435 9398081 := bstep (se 2 (by rfl) ⟨3524280, by rfl⟩ : syracuseStep 9398081 = 7048561) B7048561
theorem B6265387 : Blo 2169435 6265387 := bstep (se 1 (by rfl) ⟨4699040, by rfl⟩ : syracuseStep 6265387 = 9398081) B9398081
theorem B8353849 : Blo 2169435 8353849 := bstep (se 2 (by rfl) ⟨3132693, by rfl⟩ : syracuseStep 8353849 = 6265387) B6265387
theorem B11138465 : Blo 2169435 11138465 := bstep (se 2 (by rfl) ⟨4176924, by rfl⟩ : syracuseStep 11138465 = 8353849) B8353849
theorem B7425643 : Blo 2169435 7425643 := bstep (se 1 (by rfl) ⟨5569232, by rfl⟩ : syracuseStep 7425643 = 11138465) B11138465
theorem B9900857 : Blo 2169435 9900857 := bstep (se 2 (by rfl) ⟨3712821, by rfl⟩ : syracuseStep 9900857 = 7425643) B7425643
theorem B6600571 : Blo 2169435 6600571 := bstep (se 1 (by rfl) ⟨4950428, by rfl⟩ : syracuseStep 6600571 = 9900857) B9900857
theorem B35203045 : Blo 2169435 35203045 := bstep (se 4 (by rfl) ⟨3300285, by rfl⟩ : syracuseStep 35203045 = 6600571) B6600571
theorem B46937393 : Blo 2169435 46937393 := bstep (se 2 (by rfl) ⟨17601522, by rfl⟩ : syracuseStep 46937393 = 35203045) B35203045
theorem B31291595 : Blo 2169435 31291595 := bstep (se 1 (by rfl) ⟨23468696, by rfl⟩ : syracuseStep 31291595 = 46937393) B46937393
theorem B20861063 : Blo 2169435 20861063 := bstep (se 1 (by rfl) ⟨15645797, by rfl⟩ : syracuseStep 20861063 = 31291595) B31291595
theorem B13907375 : Blo 2169435 13907375 := bstep (se 1 (by rfl) ⟨10430531, by rfl⟩ : syracuseStep 13907375 = 20861063) B20861063
theorem B9271583 : Blo 2169435 9271583 := bstep (se 1 (by rfl) ⟨6953687, by rfl⟩ : syracuseStep 9271583 = 13907375) B13907375
theorem B6181055 : Blo 2169435 6181055 := bstep (se 1 (by rfl) ⟨4635791, by rfl⟩ : syracuseStep 6181055 = 9271583) B9271583
theorem B4120703 : Blo 2169435 4120703 := bstep (se 1 (by rfl) ⟨3090527, by rfl⟩ : syracuseStep 4120703 = 6181055) B6181055
theorem B2747135 : Blo 2169435 2747135 := bstep (se 1 (by rfl) ⟨2060351, by rfl⟩ : syracuseStep 2747135 = 4120703) B4120703
theorem B7325693 : Blo 2169435 7325693 := bstep (se 3 (by rfl) ⟨1373567, by rfl⟩ : syracuseStep 7325693 = 2747135) B2747135
theorem B4883795 : Blo 2169435 4883795 := bstep (se 1 (by rfl) ⟨3662846, by rfl⟩ : syracuseStep 4883795 = 7325693) B7325693
theorem B3255863 : Blo 2169435 3255863 := bstep (se 1 (by rfl) ⟨2441897, by rfl⟩ : syracuseStep 3255863 = 4883795) B4883795
theorem B2170575 : Blo 2169435 2170575 := bstep (se 1 (by rfl) ⟨1627931, by rfl⟩ : syracuseStep 2170575 = 3255863) B3255863
theorem B3255869 : Blo 2169435 3255869 := bbase (se 3 (by rfl) ⟨610475, by rfl⟩ : syracuseStep 3255869 = 1220951) (by norm_num)
theorem B2170579 : Blo 2169435 2170579 := bstep (se 1 (by rfl) ⟨1627934, by rfl⟩ : syracuseStep 2170579 = 3255869) B3255869
theorem B4883813 : Blo 2169435 4883813 := bbase (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) (by norm_num)
theorem B3255875 : Blo 2169435 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B2170583 : Blo 2169435 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B5494301 : Blo 2169435 5494301 := bbase (se 3 (by rfl) ⟨1030181, by rfl⟩ : syracuseStep 5494301 = 2060363) (by norm_num)
theorem B3662867 : Blo 2169435 3662867 := bstep (se 1 (by rfl) ⟨2747150, by rfl⟩ : syracuseStep 3662867 = 5494301) B5494301
theorem B2441911 : Blo 2169435 2441911 := bstep (se 1 (by rfl) ⟨1831433, by rfl⟩ : syracuseStep 2441911 = 3662867) B3662867
theorem B3255881 : Blo 2169435 3255881 := bstep (se 2 (by rfl) ⟨1220955, by rfl⟩ : syracuseStep 3255881 = 2441911) B2441911
theorem B2170587 : Blo 2169435 2170587 := bstep (se 1 (by rfl) ⟨1627940, by rfl⟩ : syracuseStep 2170587 = 3255881) B3255881
theorem B4120733 : Blo 2169435 4120733 := bbase (se 3 (by rfl) ⟨772637, by rfl⟩ : syracuseStep 4120733 = 1545275) (by norm_num)
theorem B10988621 : Blo 2169435 10988621 := bstep (se 3 (by rfl) ⟨2060366, by rfl⟩ : syracuseStep 10988621 = 4120733) B4120733
theorem B7325747 : Blo 2169435 7325747 := bstep (se 1 (by rfl) ⟨5494310, by rfl⟩ : syracuseStep 7325747 = 10988621) B10988621
theorem B4883831 : Blo 2169435 4883831 := bstep (se 1 (by rfl) ⟨3662873, by rfl⟩ : syracuseStep 4883831 = 7325747) B7325747
theorem B3255887 : Blo 2169435 3255887 := bstep (se 1 (by rfl) ⟨2441915, by rfl⟩ : syracuseStep 3255887 = 4883831) B4883831
theorem B2170591 : Blo 2169435 2170591 := bstep (se 1 (by rfl) ⟨1627943, by rfl⟩ : syracuseStep 2170591 = 3255887) B3255887
theorem B3255893 : Blo 2169435 3255893 := bbase (se 8 (by rfl) ⟨19077, by rfl⟩ : syracuseStep 3255893 = 38155) (by norm_num)
theorem B2170595 : Blo 2169435 2170595 := bstep (se 1 (by rfl) ⟨1627946, by rfl⟩ : syracuseStep 2170595 = 3255893) B3255893
theorem B9271685 : Blo 2169435 9271685 := bbase (se 4 (by rfl) ⟨869220, by rfl⟩ : syracuseStep 9271685 = 1738441) (by norm_num)
theorem B6181123 : Blo 2169435 6181123 := bstep (se 1 (by rfl) ⟨4635842, by rfl⟩ : syracuseStep 6181123 = 9271685) B9271685
theorem B8241497 : Blo 2169435 8241497 := bstep (se 2 (by rfl) ⟨3090561, by rfl⟩ : syracuseStep 8241497 = 6181123) B6181123
theorem B5494331 : Blo 2169435 5494331 := bstep (se 1 (by rfl) ⟨4120748, by rfl⟩ : syracuseStep 5494331 = 8241497) B8241497
theorem B3662887 : Blo 2169435 3662887 := bstep (se 1 (by rfl) ⟨2747165, by rfl⟩ : syracuseStep 3662887 = 5494331) B5494331
theorem B4883849 : Blo 2169435 4883849 := bstep (se 2 (by rfl) ⟨1831443, by rfl⟩ : syracuseStep 4883849 = 3662887) B3662887
theorem B3255899 : Blo 2169435 3255899 := bstep (se 1 (by rfl) ⟨2441924, by rfl⟩ : syracuseStep 3255899 = 4883849) B4883849
theorem B2170599 : Blo 2169435 2170599 := bstep (se 1 (by rfl) ⟨1627949, by rfl⟩ : syracuseStep 2170599 = 3255899) B3255899
theorem B2441929 : Blo 2169435 2441929 := bbase (se 2 (by rfl) ⟨915723, by rfl⟩ : syracuseStep 2441929 = 1831447) (by norm_num)
theorem B3255905 : Blo 2169435 3255905 := bstep (se 2 (by rfl) ⟨1220964, by rfl⟩ : syracuseStep 3255905 = 2441929) B2441929
theorem B2170603 : Blo 2169435 2170603 := bstep (se 1 (by rfl) ⟨1627952, by rfl⟩ : syracuseStep 2170603 = 3255905) B3255905
theorem B17841941 : Blo 2169435 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B11894627 : Blo 2169435 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B7929751 : Blo 2169435 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B10573001 : Blo 2169435 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B7048667 : Blo 2169435 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B18796445 : Blo 2169435 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B12530963 : Blo 2169435 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B8353975 : Blo 2169435 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B11138633 : Blo 2169435 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B7425755 : Blo 2169435 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B4950503 : Blo 2169435 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B3300335 : Blo 2169435 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2200223 : Blo 2169435 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B5867261 : Blo 2169435 5867261 := bstep (se 3 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 5867261 = 2200223) B2200223
theorem B3911507 : Blo 2169435 3911507 := bstep (se 1 (by rfl) ⟨2933630, by rfl⟩ : syracuseStep 3911507 = 5867261) B5867261
theorem B2607671 : Blo 2169435 2607671 := bstep (se 1 (by rfl) ⟨1955753, by rfl⟩ : syracuseStep 2607671 = 3911507) B3911507
theorem B6953789 : Blo 2169435 6953789 := bstep (se 3 (by rfl) ⟨1303835, by rfl⟩ : syracuseStep 6953789 = 2607671) B2607671
theorem B18543437 : Blo 2169435 18543437 := bstep (se 3 (by rfl) ⟨3476894, by rfl⟩ : syracuseStep 18543437 = 6953789) B6953789
theorem B12362291 : Blo 2169435 12362291 := bstep (se 1 (by rfl) ⟨9271718, by rfl⟩ : syracuseStep 12362291 = 18543437) B18543437
theorem B8241527 : Blo 2169435 8241527 := bstep (se 1 (by rfl) ⟨6181145, by rfl⟩ : syracuseStep 8241527 = 12362291) B12362291
theorem B5494351 : Blo 2169435 5494351 := bstep (se 1 (by rfl) ⟨4120763, by rfl⟩ : syracuseStep 5494351 = 8241527) B8241527
theorem B7325801 : Blo 2169435 7325801 := bstep (se 2 (by rfl) ⟨2747175, by rfl⟩ : syracuseStep 7325801 = 5494351) B5494351
theorem B4883867 : Blo 2169435 4883867 := bstep (se 1 (by rfl) ⟨3662900, by rfl⟩ : syracuseStep 4883867 = 7325801) B7325801
theorem B3255911 : Blo 2169435 3255911 := bstep (se 1 (by rfl) ⟨2441933, by rfl⟩ : syracuseStep 3255911 = 4883867) B4883867
theorem B2170607 : Blo 2169435 2170607 := bstep (se 1 (by rfl) ⟨1627955, by rfl⟩ : syracuseStep 2170607 = 3255911) B3255911
theorem B3255917 : Blo 2169435 3255917 := bbase (se 3 (by rfl) ⟨610484, by rfl⟩ : syracuseStep 3255917 = 1220969) (by norm_num)
theorem B2170611 : Blo 2169435 2170611 := bstep (se 1 (by rfl) ⟨1627958, by rfl⟩ : syracuseStep 2170611 = 3255917) B3255917
theorem B4883885 : Blo 2169435 4883885 := bbase (se 3 (by rfl) ⟨915728, by rfl⟩ : syracuseStep 4883885 = 1831457) (by norm_num)
theorem B3255923 : Blo 2169435 3255923 := bstep (se 1 (by rfl) ⟨2441942, by rfl⟩ : syracuseStep 3255923 = 4883885) B4883885
theorem B2170615 : Blo 2169435 2170615 := bstep (se 1 (by rfl) ⟨1627961, by rfl⟩ : syracuseStep 2170615 = 3255923) B3255923
theorem B5215373 : Blo 2169435 5215373 := bbase (se 3 (by rfl) ⟨977882, by rfl⟩ : syracuseStep 5215373 = 1955765) (by norm_num)
theorem B3476915 : Blo 2169435 3476915 := bstep (se 1 (by rfl) ⟨2607686, by rfl⟩ : syracuseStep 3476915 = 5215373) B5215373
theorem B2317943 : Blo 2169435 2317943 := bstep (se 1 (by rfl) ⟨1738457, by rfl⟩ : syracuseStep 2317943 = 3476915) B3476915
theorem B6181181 : Blo 2169435 6181181 := bstep (se 3 (by rfl) ⟨1158971, by rfl⟩ : syracuseStep 6181181 = 2317943) B2317943
theorem B4120787 : Blo 2169435 4120787 := bstep (se 1 (by rfl) ⟨3090590, by rfl⟩ : syracuseStep 4120787 = 6181181) B6181181
theorem B2747191 : Blo 2169435 2747191 := bstep (se 1 (by rfl) ⟨2060393, by rfl⟩ : syracuseStep 2747191 = 4120787) B4120787
theorem B3662921 : Blo 2169435 3662921 := bstep (se 2 (by rfl) ⟨1373595, by rfl⟩ : syracuseStep 3662921 = 2747191) B2747191
theorem B2441947 : Blo 2169435 2441947 := bstep (se 1 (by rfl) ⟨1831460, by rfl⟩ : syracuseStep 2441947 = 3662921) B3662921
theorem B3255929 : Blo 2169435 3255929 := bstep (se 2 (by rfl) ⟨1220973, by rfl⟩ : syracuseStep 3255929 = 2441947) B2441947
theorem B2170619 : Blo 2169435 2170619 := bstep (se 1 (by rfl) ⟨1627964, by rfl⟩ : syracuseStep 2170619 = 3255929) B3255929
theorem B8921029 : Blo 2169435 8921029 := bbase (se 4 (by rfl) ⟨836346, by rfl⟩ : syracuseStep 8921029 = 1672693) (by norm_num)
theorem B11894705 : Blo 2169435 11894705 := bstep (se 2 (by rfl) ⟨4460514, by rfl⟩ : syracuseStep 11894705 = 8921029) B8921029
theorem B7929803 : Blo 2169435 7929803 := bstep (se 1 (by rfl) ⟨5947352, by rfl⟩ : syracuseStep 7929803 = 11894705) B11894705
theorem B5286535 : Blo 2169435 5286535 := bstep (se 1 (by rfl) ⟨3964901, by rfl⟩ : syracuseStep 5286535 = 7929803) B7929803
theorem B28194853 : Blo 2169435 28194853 := bstep (se 4 (by rfl) ⟨2643267, by rfl⟩ : syracuseStep 28194853 = 5286535) B5286535
theorem B37593137 : Blo 2169435 37593137 := bstep (se 2 (by rfl) ⟨14097426, by rfl⟩ : syracuseStep 37593137 = 28194853) B28194853
theorem B25062091 : Blo 2169435 25062091 := bstep (se 1 (by rfl) ⟨18796568, by rfl⟩ : syracuseStep 25062091 = 37593137) B37593137
theorem B534657941 : Blo 2169435 534657941 := bstep (se 6 (by rfl) ⟨12531045, by rfl⟩ : syracuseStep 534657941 = 25062091) B25062091
theorem B356438627 : Blo 2169435 356438627 := bstep (se 1 (by rfl) ⟨267328970, by rfl⟩ : syracuseStep 356438627 = 534657941) B534657941
theorem B237625751 : Blo 2169435 237625751 := bstep (se 1 (by rfl) ⟨178219313, by rfl⟩ : syracuseStep 237625751 = 356438627) B356438627
theorem B158417167 : Blo 2169435 158417167 := bstep (se 1 (by rfl) ⟨118812875, by rfl⟩ : syracuseStep 158417167 = 237625751) B237625751
theorem B211222889 : Blo 2169435 211222889 := bstep (se 2 (by rfl) ⟨79208583, by rfl⟩ : syracuseStep 211222889 = 158417167) B158417167
theorem B140815259 : Blo 2169435 140815259 := bstep (se 1 (by rfl) ⟨105611444, by rfl⟩ : syracuseStep 140815259 = 211222889) B211222889
theorem B93876839 : Blo 2169435 93876839 := bstep (se 1 (by rfl) ⟨70407629, by rfl⟩ : syracuseStep 93876839 = 140815259) B140815259
theorem B62584559 : Blo 2169435 62584559 := bstep (se 1 (by rfl) ⟨46938419, by rfl⟩ : syracuseStep 62584559 = 93876839) B93876839
theorem B41723039 : Blo 2169435 41723039 := bstep (se 1 (by rfl) ⟨31292279, by rfl⟩ : syracuseStep 41723039 = 62584559) B62584559
theorem B27815359 : Blo 2169435 27815359 := bstep (se 1 (by rfl) ⟨20861519, by rfl⟩ : syracuseStep 27815359 = 41723039) B41723039
theorem B37087145 : Blo 2169435 37087145 := bstep (se 2 (by rfl) ⟨13907679, by rfl⟩ : syracuseStep 37087145 = 27815359) B27815359
theorem B24724763 : Blo 2169435 24724763 := bstep (se 1 (by rfl) ⟨18543572, by rfl⟩ : syracuseStep 24724763 = 37087145) B37087145
theorem B16483175 : Blo 2169435 16483175 := bstep (se 1 (by rfl) ⟨12362381, by rfl⟩ : syracuseStep 16483175 = 24724763) B24724763
theorem B10988783 : Blo 2169435 10988783 := bstep (se 1 (by rfl) ⟨8241587, by rfl⟩ : syracuseStep 10988783 = 16483175) B16483175
theorem B7325855 : Blo 2169435 7325855 := bstep (se 1 (by rfl) ⟨5494391, by rfl⟩ : syracuseStep 7325855 = 10988783) B10988783
theorem B4883903 : Blo 2169435 4883903 := bstep (se 1 (by rfl) ⟨3662927, by rfl⟩ : syracuseStep 4883903 = 7325855) B7325855
theorem B3255935 : Blo 2169435 3255935 := bstep (se 1 (by rfl) ⟨2441951, by rfl⟩ : syracuseStep 3255935 = 4883903) B4883903
theorem B2170623 : Blo 2169435 2170623 := bstep (se 1 (by rfl) ⟨1627967, by rfl⟩ : syracuseStep 2170623 = 3255935) B3255935
theorem B3255941 : Blo 2169435 3255941 := bbase (se 4 (by rfl) ⟨305244, by rfl⟩ : syracuseStep 3255941 = 610489) (by norm_num)
theorem B2170627 : Blo 2169435 2170627 := bstep (se 1 (by rfl) ⟨1627970, by rfl⟩ : syracuseStep 2170627 = 3255941) B3255941
theorem B3662941 : Blo 2169435 3662941 := bbase (se 3 (by rfl) ⟨686801, by rfl⟩ : syracuseStep 3662941 = 1373603) (by norm_num)
theorem B4883921 : Blo 2169435 4883921 := bstep (se 2 (by rfl) ⟨1831470, by rfl⟩ : syracuseStep 4883921 = 3662941) B3662941
theorem B3255947 : Blo 2169435 3255947 := bstep (se 1 (by rfl) ⟨2441960, by rfl⟩ : syracuseStep 3255947 = 4883921) B4883921
theorem B2170631 : Blo 2169435 2170631 := bstep (se 1 (by rfl) ⟨1627973, by rfl⟩ : syracuseStep 2170631 = 3255947) B3255947
theorem B2441965 : Blo 2169435 2441965 := bbase (se 3 (by rfl) ⟨457868, by rfl⟩ : syracuseStep 2441965 = 915737) (by norm_num)
theorem B3255953 : Blo 2169435 3255953 := bstep (se 2 (by rfl) ⟨1220982, by rfl⟩ : syracuseStep 3255953 = 2441965) B2441965
theorem B2170635 : Blo 2169435 2170635 := bstep (se 1 (by rfl) ⟨1627976, by rfl⟩ : syracuseStep 2170635 = 3255953) B3255953
theorem B7325909 : Blo 2169435 7325909 := bbase (se 7 (by rfl) ⟨85850, by rfl⟩ : syracuseStep 7325909 = 171701) (by norm_num)
theorem B4883939 : Blo 2169435 4883939 := bstep (se 1 (by rfl) ⟨3662954, by rfl⟩ : syracuseStep 4883939 = 7325909) B7325909
theorem B3255959 : Blo 2169435 3255959 := bstep (se 1 (by rfl) ⟨2441969, by rfl⟩ : syracuseStep 3255959 = 4883939) B4883939
theorem B2170639 : Blo 2169435 2170639 := bstep (se 1 (by rfl) ⟨1627979, by rfl⟩ : syracuseStep 2170639 = 3255959) B3255959
theorem B3255965 : Blo 2169435 3255965 := bbase (se 3 (by rfl) ⟨610493, by rfl⟩ : syracuseStep 3255965 = 1220987) (by norm_num)
theorem B2170643 : Blo 2169435 2170643 := bstep (se 1 (by rfl) ⟨1627982, by rfl⟩ : syracuseStep 2170643 = 3255965) B3255965
theorem B4883957 : Blo 2169435 4883957 := bbase (se 5 (by rfl) ⟨228935, by rfl⟩ : syracuseStep 4883957 = 457871) (by norm_num)
theorem B3255971 : Blo 2169435 3255971 := bstep (se 1 (by rfl) ⟨2441978, by rfl⟩ : syracuseStep 3255971 = 4883957) B4883957
theorem B2170647 : Blo 2169435 2170647 := bstep (se 1 (by rfl) ⟨1627985, by rfl⟩ : syracuseStep 2170647 = 3255971) B3255971
theorem B2475301 : Blo 2169435 2475301 := bbase (se 4 (by rfl) ⟨232059, by rfl⟩ : syracuseStep 2475301 = 464119) (by norm_num)
theorem B3300401 : Blo 2169435 3300401 := bstep (se 2 (by rfl) ⟨1237650, by rfl⟩ : syracuseStep 3300401 = 2475301) B2475301
theorem B8801069 : Blo 2169435 8801069 := bstep (se 3 (by rfl) ⟨1650200, by rfl⟩ : syracuseStep 8801069 = 3300401) B3300401
theorem B23469517 : Blo 2169435 23469517 := bstep (se 3 (by rfl) ⟨4400534, by rfl⟩ : syracuseStep 23469517 = 8801069) B8801069
theorem B31292689 : Blo 2169435 31292689 := bstep (se 2 (by rfl) ⟨11734758, by rfl⟩ : syracuseStep 31292689 = 23469517) B23469517
theorem B41723585 : Blo 2169435 41723585 := bstep (se 2 (by rfl) ⟨15646344, by rfl⟩ : syracuseStep 41723585 = 31292689) B31292689
theorem B27815723 : Blo 2169435 27815723 := bstep (se 1 (by rfl) ⟨20861792, by rfl⟩ : syracuseStep 27815723 = 41723585) B41723585
theorem B18543815 : Blo 2169435 18543815 := bstep (se 1 (by rfl) ⟨13907861, by rfl⟩ : syracuseStep 18543815 = 27815723) B27815723
theorem B12362543 : Blo 2169435 12362543 := bstep (se 1 (by rfl) ⟨9271907, by rfl⟩ : syracuseStep 12362543 = 18543815) B18543815
theorem B8241695 : Blo 2169435 8241695 := bstep (se 1 (by rfl) ⟨6181271, by rfl⟩ : syracuseStep 8241695 = 12362543) B12362543
theorem B5494463 : Blo 2169435 5494463 := bstep (se 1 (by rfl) ⟨4120847, by rfl⟩ : syracuseStep 5494463 = 8241695) B8241695
theorem B3662975 : Blo 2169435 3662975 := bstep (se 1 (by rfl) ⟨2747231, by rfl⟩ : syracuseStep 3662975 = 5494463) B5494463
theorem B2441983 : Blo 2169435 2441983 := bstep (se 1 (by rfl) ⟨1831487, by rfl⟩ : syracuseStep 2441983 = 3662975) B3662975
theorem B3255977 : Blo 2169435 3255977 := bstep (se 2 (by rfl) ⟨1220991, by rfl⟩ : syracuseStep 3255977 = 2441983) B2441983
theorem B2170651 : Blo 2169435 2170651 := bstep (se 1 (by rfl) ⟨1627988, by rfl⟩ : syracuseStep 2170651 = 3255977) B3255977
theorem B2317981 : Blo 2169435 2317981 := bbase (se 3 (by rfl) ⟨434621, by rfl⟩ : syracuseStep 2317981 = 869243) (by norm_num)
theorem B3090641 : Blo 2169435 3090641 := bstep (se 2 (by rfl) ⟨1158990, by rfl⟩ : syracuseStep 3090641 = 2317981) B2317981
theorem B8241709 : Blo 2169435 8241709 := bstep (se 3 (by rfl) ⟨1545320, by rfl⟩ : syracuseStep 8241709 = 3090641) B3090641
theorem B10988945 : Blo 2169435 10988945 := bstep (se 2 (by rfl) ⟨4120854, by rfl⟩ : syracuseStep 10988945 = 8241709) B8241709
theorem B7325963 : Blo 2169435 7325963 := bstep (se 1 (by rfl) ⟨5494472, by rfl⟩ : syracuseStep 7325963 = 10988945) B10988945
theorem B4883975 : Blo 2169435 4883975 := bstep (se 1 (by rfl) ⟨3662981, by rfl⟩ : syracuseStep 4883975 = 7325963) B7325963
theorem B3255983 : Blo 2169435 3255983 := bstep (se 1 (by rfl) ⟨2441987, by rfl⟩ : syracuseStep 3255983 = 4883975) B4883975
theorem B2170655 : Blo 2169435 2170655 := bstep (se 1 (by rfl) ⟨1627991, by rfl⟩ : syracuseStep 2170655 = 3255983) B3255983
theorem B3255989 : Blo 2169435 3255989 := bbase (se 5 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 3255989 = 305249) (by norm_num)
theorem B2170659 : Blo 2169435 2170659 := bstep (se 1 (by rfl) ⟨1627994, by rfl⟩ : syracuseStep 2170659 = 3255989) B3255989
theorem B5494493 : Blo 2169435 5494493 := bbase (se 3 (by rfl) ⟨1030217, by rfl⟩ : syracuseStep 5494493 = 2060435) (by norm_num)
theorem B3662995 : Blo 2169435 3662995 := bstep (se 1 (by rfl) ⟨2747246, by rfl⟩ : syracuseStep 3662995 = 5494493) B5494493
theorem B4883993 : Blo 2169435 4883993 := bstep (se 2 (by rfl) ⟨1831497, by rfl⟩ : syracuseStep 4883993 = 3662995) B3662995
theorem B3255995 : Blo 2169435 3255995 := bstep (se 1 (by rfl) ⟨2441996, by rfl⟩ : syracuseStep 3255995 = 4883993) B4883993
theorem B2170663 : Blo 2169435 2170663 := bstep (se 1 (by rfl) ⟨1627997, by rfl⟩ : syracuseStep 2170663 = 3255995) B3255995
theorem B2442001 : Blo 2169435 2442001 := bbase (se 2 (by rfl) ⟨915750, by rfl⟩ : syracuseStep 2442001 = 1831501) (by norm_num)
theorem B3256001 : Blo 2169435 3256001 := bstep (se 2 (by rfl) ⟨1221000, by rfl⟩ : syracuseStep 3256001 = 2442001) B2442001
theorem B2170667 : Blo 2169435 2170667 := bstep (se 1 (by rfl) ⟨1628000, by rfl⟩ : syracuseStep 2170667 = 3256001) B3256001
theorem B4120885 : Blo 2169435 4120885 := bbase (se 5 (by rfl) ⟨193166, by rfl⟩ : syracuseStep 4120885 = 386333) (by norm_num)
theorem B5494513 : Blo 2169435 5494513 := bstep (se 2 (by rfl) ⟨2060442, by rfl⟩ : syracuseStep 5494513 = 4120885) B4120885
theorem B7326017 : Blo 2169435 7326017 := bstep (se 2 (by rfl) ⟨2747256, by rfl⟩ : syracuseStep 7326017 = 5494513) B5494513
theorem B4884011 : Blo 2169435 4884011 := bstep (se 1 (by rfl) ⟨3663008, by rfl⟩ : syracuseStep 4884011 = 7326017) B7326017
theorem B3256007 : Blo 2169435 3256007 := bstep (se 1 (by rfl) ⟨2442005, by rfl⟩ : syracuseStep 3256007 = 4884011) B4884011
theorem B2170671 : Blo 2169435 2170671 := bstep (se 1 (by rfl) ⟨1628003, by rfl⟩ : syracuseStep 2170671 = 3256007) B3256007
theorem B3256013 : Blo 2169435 3256013 := bbase (se 3 (by rfl) ⟨610502, by rfl⟩ : syracuseStep 3256013 = 1221005) (by norm_num)
theorem B2170675 : Blo 2169435 2170675 := bstep (se 1 (by rfl) ⟨1628006, by rfl⟩ : syracuseStep 2170675 = 3256013) B3256013
theorem B4884029 : Blo 2169435 4884029 := bbase (se 3 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 4884029 = 1831511) (by norm_num)
theorem B3256019 : Blo 2169435 3256019 := bstep (se 1 (by rfl) ⟨2442014, by rfl⟩ : syracuseStep 3256019 = 4884029) B4884029
theorem B2170679 : Blo 2169435 2170679 := bstep (se 1 (by rfl) ⟨1628009, by rfl⟩ : syracuseStep 2170679 = 3256019) B3256019
theorem B3663029 : Blo 2169435 3663029 := bbase (se 5 (by rfl) ⟨171704, by rfl⟩ : syracuseStep 3663029 = 343409) (by norm_num)
theorem B2442019 : Blo 2169435 2442019 := bstep (se 1 (by rfl) ⟨1831514, by rfl⟩ : syracuseStep 2442019 = 3663029) B3663029
theorem B3256025 : Blo 2169435 3256025 := bstep (se 2 (by rfl) ⟨1221009, by rfl⟩ : syracuseStep 3256025 = 2442019) B2442019
theorem B2170683 : Blo 2169435 2170683 := bstep (se 1 (by rfl) ⟨1628012, by rfl⟩ : syracuseStep 2170683 = 3256025) B3256025
theorem B4234133 : Blo 2169435 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B2822755 : Blo 2169435 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B3763673 : Blo 2169435 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B2509115 : Blo 2169435 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B6690973 : Blo 2169435 6690973 := bstep (se 3 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 6690973 = 2509115) B2509115
theorem B8921297 : Blo 2169435 8921297 := bstep (se 2 (by rfl) ⟨3345486, by rfl⟩ : syracuseStep 8921297 = 6690973) B6690973
theorem B23790125 : Blo 2169435 23790125 := bstep (se 3 (by rfl) ⟨4460648, by rfl⟩ : syracuseStep 23790125 = 8921297) B8921297
theorem B15860083 : Blo 2169435 15860083 := bstep (se 1 (by rfl) ⟨11895062, by rfl⟩ : syracuseStep 15860083 = 23790125) B23790125
theorem B21146777 : Blo 2169435 21146777 := bstep (se 2 (by rfl) ⟨7930041, by rfl⟩ : syracuseStep 21146777 = 15860083) B15860083
theorem B14097851 : Blo 2169435 14097851 := bstep (se 1 (by rfl) ⟨10573388, by rfl⟩ : syracuseStep 14097851 = 21146777) B21146777
theorem B9398567 : Blo 2169435 9398567 := bstep (se 1 (by rfl) ⟨7048925, by rfl⟩ : syracuseStep 9398567 = 14097851) B14097851
theorem B6265711 : Blo 2169435 6265711 := bstep (se 1 (by rfl) ⟨4699283, by rfl⟩ : syracuseStep 6265711 = 9398567) B9398567
theorem B8354281 : Blo 2169435 8354281 := bstep (se 2 (by rfl) ⟨3132855, by rfl⟩ : syracuseStep 8354281 = 6265711) B6265711
theorem B11139041 : Blo 2169435 11139041 := bstep (se 2 (by rfl) ⟨4177140, by rfl⟩ : syracuseStep 11139041 = 8354281) B8354281
theorem B7426027 : Blo 2169435 7426027 := bstep (se 1 (by rfl) ⟨5569520, by rfl⟩ : syracuseStep 7426027 = 11139041) B11139041
theorem B9901369 : Blo 2169435 9901369 := bstep (se 2 (by rfl) ⟨3713013, by rfl⟩ : syracuseStep 9901369 = 7426027) B7426027
theorem B13201825 : Blo 2169435 13201825 := bstep (se 2 (by rfl) ⟨4950684, by rfl⟩ : syracuseStep 13201825 = 9901369) B9901369
theorem B17602433 : Blo 2169435 17602433 := bstep (se 2 (by rfl) ⟨6600912, by rfl⟩ : syracuseStep 17602433 = 13201825) B13201825
theorem B11734955 : Blo 2169435 11734955 := bstep (se 1 (by rfl) ⟨8801216, by rfl⟩ : syracuseStep 11734955 = 17602433) B17602433
theorem B7823303 : Blo 2169435 7823303 := bstep (se 1 (by rfl) ⟨5867477, by rfl⟩ : syracuseStep 7823303 = 11734955) B11734955
theorem B5215535 : Blo 2169435 5215535 := bstep (se 1 (by rfl) ⟨3911651, by rfl⟩ : syracuseStep 5215535 = 7823303) B7823303
theorem B3477023 : Blo 2169435 3477023 := bstep (se 1 (by rfl) ⟨2607767, by rfl⟩ : syracuseStep 3477023 = 5215535) B5215535
theorem B2318015 : Blo 2169435 2318015 := bstep (se 1 (by rfl) ⟨1738511, by rfl⟩ : syracuseStep 2318015 = 3477023) B3477023
theorem B6181373 : Blo 2169435 6181373 := bstep (se 3 (by rfl) ⟨1159007, by rfl⟩ : syracuseStep 6181373 = 2318015) B2318015
theorem B16483661 : Blo 2169435 16483661 := bstep (se 3 (by rfl) ⟨3090686, by rfl⟩ : syracuseStep 16483661 = 6181373) B6181373
theorem B10989107 : Blo 2169435 10989107 := bstep (se 1 (by rfl) ⟨8241830, by rfl⟩ : syracuseStep 10989107 = 16483661) B16483661
theorem B7326071 : Blo 2169435 7326071 := bstep (se 1 (by rfl) ⟨5494553, by rfl⟩ : syracuseStep 7326071 = 10989107) B10989107
theorem B4884047 : Blo 2169435 4884047 := bstep (se 1 (by rfl) ⟨3663035, by rfl⟩ : syracuseStep 4884047 = 7326071) B7326071
theorem B3256031 : Blo 2169435 3256031 := bstep (se 1 (by rfl) ⟨2442023, by rfl⟩ : syracuseStep 3256031 = 4884047) B4884047
theorem B2170687 : Blo 2169435 2170687 := bstep (se 1 (by rfl) ⟨1628015, by rfl⟩ : syracuseStep 2170687 = 3256031) B3256031
theorem B3256037 : Blo 2169435 3256037 := bbase (se 4 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 3256037 = 610507) (by norm_num)
theorem B2170691 : Blo 2169435 2170691 := bstep (se 1 (by rfl) ⟨1628018, by rfl⟩ : syracuseStep 2170691 = 3256037) B3256037
theorem B6181397 : Blo 2169435 6181397 := bbase (se 6 (by rfl) ⟨144876, by rfl⟩ : syracuseStep 6181397 = 289753) (by norm_num)
theorem B4120931 : Blo 2169435 4120931 := bstep (se 1 (by rfl) ⟨3090698, by rfl⟩ : syracuseStep 4120931 = 6181397) B6181397
theorem B2747287 : Blo 2169435 2747287 := bstep (se 1 (by rfl) ⟨2060465, by rfl⟩ : syracuseStep 2747287 = 4120931) B4120931
theorem B3663049 : Blo 2169435 3663049 := bstep (se 2 (by rfl) ⟨1373643, by rfl⟩ : syracuseStep 3663049 = 2747287) B2747287
theorem B4884065 : Blo 2169435 4884065 := bstep (se 2 (by rfl) ⟨1831524, by rfl⟩ : syracuseStep 4884065 = 3663049) B3663049
theorem B3256043 : Blo 2169435 3256043 := bstep (se 1 (by rfl) ⟨2442032, by rfl⟩ : syracuseStep 3256043 = 4884065) B4884065
theorem B2170695 : Blo 2169435 2170695 := bstep (se 1 (by rfl) ⟨1628021, by rfl⟩ : syracuseStep 2170695 = 3256043) B3256043
theorem B2442037 : Blo 2169435 2442037 := bbase (se 5 (by rfl) ⟨114470, by rfl⟩ : syracuseStep 2442037 = 228941) (by norm_num)
theorem B3256049 : Blo 2169435 3256049 := bstep (se 2 (by rfl) ⟨1221018, by rfl⟩ : syracuseStep 3256049 = 2442037) B2442037
theorem B2170699 : Blo 2169435 2170699 := bstep (se 1 (by rfl) ⟨1628024, by rfl⟩ : syracuseStep 2170699 = 3256049) B3256049
theorem B2747297 : Blo 2169435 2747297 := bbase (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) (by norm_num)
theorem B7326125 : Blo 2169435 7326125 := bstep (se 3 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 7326125 = 2747297) B2747297
theorem B4884083 : Blo 2169435 4884083 := bstep (se 1 (by rfl) ⟨3663062, by rfl⟩ : syracuseStep 4884083 = 7326125) B7326125
theorem B3256055 : Blo 2169435 3256055 := bstep (se 1 (by rfl) ⟨2442041, by rfl⟩ : syracuseStep 3256055 = 4884083) B4884083
theorem B2170703 : Blo 2169435 2170703 := bstep (se 1 (by rfl) ⟨1628027, by rfl⟩ : syracuseStep 2170703 = 3256055) B3256055
theorem B3256061 : Blo 2169435 3256061 := bbase (se 3 (by rfl) ⟨610511, by rfl⟩ : syracuseStep 3256061 = 1221023) (by norm_num)
theorem B2170707 : Blo 2169435 2170707 := bstep (se 1 (by rfl) ⟨1628030, by rfl⟩ : syracuseStep 2170707 = 3256061) B3256061
theorem B4884101 : Blo 2169435 4884101 := bbase (se 4 (by rfl) ⟨457884, by rfl⟩ : syracuseStep 4884101 = 915769) (by norm_num)
theorem B3256067 : Blo 2169435 3256067 := bstep (se 1 (by rfl) ⟨2442050, by rfl⟩ : syracuseStep 3256067 = 4884101) B4884101
theorem B2170711 : Blo 2169435 2170711 := bstep (se 1 (by rfl) ⟨1628033, by rfl⟩ : syracuseStep 2170711 = 3256067) B3256067
theorem B2200333 : Blo 2169435 2200333 := bbase (se 3 (by rfl) ⟨412562, by rfl⟩ : syracuseStep 2200333 = 825125) (by norm_num)
theorem B2933777 : Blo 2169435 2933777 := bstep (se 2 (by rfl) ⟨1100166, by rfl⟩ : syracuseStep 2933777 = 2200333) B2200333
theorem B7823405 : Blo 2169435 7823405 := bstep (se 3 (by rfl) ⟨1466888, by rfl⟩ : syracuseStep 7823405 = 2933777) B2933777
theorem B5215603 : Blo 2169435 5215603 := bstep (se 1 (by rfl) ⟨3911702, by rfl⟩ : syracuseStep 5215603 = 7823405) B7823405
theorem B6954137 : Blo 2169435 6954137 := bstep (se 2 (by rfl) ⟨2607801, by rfl⟩ : syracuseStep 6954137 = 5215603) B5215603
theorem B4636091 : Blo 2169435 4636091 := bstep (se 1 (by rfl) ⟨3477068, by rfl⟩ : syracuseStep 4636091 = 6954137) B6954137
theorem B3090727 : Blo 2169435 3090727 := bstep (se 1 (by rfl) ⟨2318045, by rfl⟩ : syracuseStep 3090727 = 4636091) B4636091
theorem B4120969 : Blo 2169435 4120969 := bstep (se 2 (by rfl) ⟨1545363, by rfl⟩ : syracuseStep 4120969 = 3090727) B3090727
theorem B5494625 : Blo 2169435 5494625 := bstep (se 2 (by rfl) ⟨2060484, by rfl⟩ : syracuseStep 5494625 = 4120969) B4120969
theorem B3663083 : Blo 2169435 3663083 := bstep (se 1 (by rfl) ⟨2747312, by rfl⟩ : syracuseStep 3663083 = 5494625) B5494625
theorem B2442055 : Blo 2169435 2442055 := bstep (se 1 (by rfl) ⟨1831541, by rfl⟩ : syracuseStep 2442055 = 3663083) B3663083
theorem B3256073 : Blo 2169435 3256073 := bstep (se 2 (by rfl) ⟨1221027, by rfl⟩ : syracuseStep 3256073 = 2442055) B2442055
theorem B2170715 : Blo 2169435 2170715 := bstep (se 1 (by rfl) ⟨1628036, by rfl⟩ : syracuseStep 2170715 = 3256073) B3256073
theorem B10989269 : Blo 2169435 10989269 := bbase (se 7 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 10989269 = 257561) (by norm_num)
theorem B7326179 : Blo 2169435 7326179 := bstep (se 1 (by rfl) ⟨5494634, by rfl⟩ : syracuseStep 7326179 = 10989269) B10989269
theorem B4884119 : Blo 2169435 4884119 := bstep (se 1 (by rfl) ⟨3663089, by rfl⟩ : syracuseStep 4884119 = 7326179) B7326179
theorem B3256079 : Blo 2169435 3256079 := bstep (se 1 (by rfl) ⟨2442059, by rfl⟩ : syracuseStep 3256079 = 4884119) B4884119
theorem B2170719 : Blo 2169435 2170719 := bstep (se 1 (by rfl) ⟨1628039, by rfl⟩ : syracuseStep 2170719 = 3256079) B3256079
theorem B3256085 : Blo 2169435 3256085 := bbase (se 6 (by rfl) ⟨76314, by rfl⟩ : syracuseStep 3256085 = 152629) (by norm_num)
theorem B2170723 : Blo 2169435 2170723 := bstep (se 1 (by rfl) ⟨1628042, by rfl⟩ : syracuseStep 2170723 = 3256085) B3256085
theorem B2349685 : Blo 2169435 2349685 := bbase (se 5 (by rfl) ⟨110141, by rfl⟩ : syracuseStep 2349685 = 220283) (by norm_num)
theorem B3132913 : Blo 2169435 3132913 := bstep (se 2 (by rfl) ⟨1174842, by rfl⟩ : syracuseStep 3132913 = 2349685) B2349685
theorem B4177217 : Blo 2169435 4177217 := bstep (se 2 (by rfl) ⟨1566456, by rfl⟩ : syracuseStep 4177217 = 3132913) B3132913
theorem B2784811 : Blo 2169435 2784811 := bstep (se 1 (by rfl) ⟨2088608, by rfl⟩ : syracuseStep 2784811 = 4177217) B4177217
theorem B3713081 : Blo 2169435 3713081 := bstep (se 2 (by rfl) ⟨1392405, by rfl⟩ : syracuseStep 3713081 = 2784811) B2784811
theorem B9901549 : Blo 2169435 9901549 := bstep (se 3 (by rfl) ⟨1856540, by rfl⟩ : syracuseStep 9901549 = 3713081) B3713081
theorem B13202065 : Blo 2169435 13202065 := bstep (se 2 (by rfl) ⟨4950774, by rfl⟩ : syracuseStep 13202065 = 9901549) B9901549
theorem B17602753 : Blo 2169435 17602753 := bstep (se 2 (by rfl) ⟨6601032, by rfl⟩ : syracuseStep 17602753 = 13202065) B13202065
theorem B23470337 : Blo 2169435 23470337 := bstep (se 2 (by rfl) ⟨8801376, by rfl⟩ : syracuseStep 23470337 = 17602753) B17602753
theorem B62587565 : Blo 2169435 62587565 := bstep (se 3 (by rfl) ⟨11735168, by rfl⟩ : syracuseStep 62587565 = 23470337) B23470337
theorem B41725043 : Blo 2169435 41725043 := bstep (se 1 (by rfl) ⟨31293782, by rfl⟩ : syracuseStep 41725043 = 62587565) B62587565
theorem B27816695 : Blo 2169435 27816695 := bstep (se 1 (by rfl) ⟨20862521, by rfl⟩ : syracuseStep 27816695 = 41725043) B41725043
theorem B18544463 : Blo 2169435 18544463 := bstep (se 1 (by rfl) ⟨13908347, by rfl⟩ : syracuseStep 18544463 = 27816695) B27816695
theorem B12362975 : Blo 2169435 12362975 := bstep (se 1 (by rfl) ⟨9272231, by rfl⟩ : syracuseStep 12362975 = 18544463) B18544463
theorem B8241983 : Blo 2169435 8241983 := bstep (se 1 (by rfl) ⟨6181487, by rfl⟩ : syracuseStep 8241983 = 12362975) B12362975
theorem B5494655 : Blo 2169435 5494655 := bstep (se 1 (by rfl) ⟨4120991, by rfl⟩ : syracuseStep 5494655 = 8241983) B8241983
theorem B3663103 : Blo 2169435 3663103 := bstep (se 1 (by rfl) ⟨2747327, by rfl⟩ : syracuseStep 3663103 = 5494655) B5494655
theorem B4884137 : Blo 2169435 4884137 := bstep (se 2 (by rfl) ⟨1831551, by rfl⟩ : syracuseStep 4884137 = 3663103) B3663103
theorem B3256091 : Blo 2169435 3256091 := bstep (se 1 (by rfl) ⟨2442068, by rfl⟩ : syracuseStep 3256091 = 4884137) B4884137
theorem B2170727 : Blo 2169435 2170727 := bstep (se 1 (by rfl) ⟨1628045, by rfl⟩ : syracuseStep 2170727 = 3256091) B3256091
theorem B2442073 : Blo 2169435 2442073 := bbase (se 2 (by rfl) ⟨915777, by rfl⟩ : syracuseStep 2442073 = 1831555) (by norm_num)
theorem B3256097 : Blo 2169435 3256097 := bstep (se 2 (by rfl) ⟨1221036, by rfl⟩ : syracuseStep 3256097 = 2442073) B2442073
theorem B2170731 : Blo 2169435 2170731 := bstep (se 1 (by rfl) ⟨1628048, by rfl⟩ : syracuseStep 2170731 = 3256097) B3256097
theorem B4636133 : Blo 2169435 4636133 := bbase (se 4 (by rfl) ⟨434637, by rfl⟩ : syracuseStep 4636133 = 869275) (by norm_num)
theorem B3090755 : Blo 2169435 3090755 := bstep (se 1 (by rfl) ⟨2318066, by rfl⟩ : syracuseStep 3090755 = 4636133) B4636133
theorem B8242013 : Blo 2169435 8242013 := bstep (se 3 (by rfl) ⟨1545377, by rfl⟩ : syracuseStep 8242013 = 3090755) B3090755
theorem B5494675 : Blo 2169435 5494675 := bstep (se 1 (by rfl) ⟨4121006, by rfl⟩ : syracuseStep 5494675 = 8242013) B8242013
theorem B7326233 : Blo 2169435 7326233 := bstep (se 2 (by rfl) ⟨2747337, by rfl⟩ : syracuseStep 7326233 = 5494675) B5494675
theorem B4884155 : Blo 2169435 4884155 := bstep (se 1 (by rfl) ⟨3663116, by rfl⟩ : syracuseStep 4884155 = 7326233) B7326233
theorem B3256103 : Blo 2169435 3256103 := bstep (se 1 (by rfl) ⟨2442077, by rfl⟩ : syracuseStep 3256103 = 4884155) B4884155
theorem B2170735 : Blo 2169435 2170735 := bstep (se 1 (by rfl) ⟨1628051, by rfl⟩ : syracuseStep 2170735 = 3256103) B3256103
theorem B3256109 : Blo 2169435 3256109 := bbase (se 3 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 3256109 = 1221041) (by norm_num)
theorem B2170739 : Blo 2169435 2170739 := bstep (se 1 (by rfl) ⟨1628054, by rfl⟩ : syracuseStep 2170739 = 3256109) B3256109
theorem B4884173 : Blo 2169435 4884173 := bbase (se 3 (by rfl) ⟨915782, by rfl⟩ : syracuseStep 4884173 = 1831565) (by norm_num)
theorem B3256115 : Blo 2169435 3256115 := bstep (se 1 (by rfl) ⟨2442086, by rfl⟩ : syracuseStep 3256115 = 4884173) B4884173
theorem B2170743 : Blo 2169435 2170743 := bstep (se 1 (by rfl) ⟨1628057, by rfl⟩ : syracuseStep 2170743 = 3256115) B3256115
theorem B2747353 : Blo 2169435 2747353 := bbase (se 2 (by rfl) ⟨1030257, by rfl⟩ : syracuseStep 2747353 = 2060515) (by norm_num)
theorem B3663137 : Blo 2169435 3663137 := bstep (se 2 (by rfl) ⟨1373676, by rfl⟩ : syracuseStep 3663137 = 2747353) B2747353
theorem B2442091 : Blo 2169435 2442091 := bstep (se 1 (by rfl) ⟨1831568, by rfl⟩ : syracuseStep 2442091 = 3663137) B3663137
theorem B3256121 : Blo 2169435 3256121 := bstep (se 2 (by rfl) ⟨1221045, by rfl⟩ : syracuseStep 3256121 = 2442091) B2442091
theorem B2170747 : Blo 2169435 2170747 := bstep (se 1 (by rfl) ⟨1628060, by rfl⟩ : syracuseStep 2170747 = 3256121) B3256121
theorem B3477125 : Blo 2169435 3477125 := bbase (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) (by norm_num)
theorem B9272333 : Blo 2169435 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B24726221 : Blo 2169435 24726221 := bstep (se 3 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 24726221 = 9272333) B9272333
theorem B16484147 : Blo 2169435 16484147 := bstep (se 1 (by rfl) ⟨12363110, by rfl⟩ : syracuseStep 16484147 = 24726221) B24726221
theorem B10989431 : Blo 2169435 10989431 := bstep (se 1 (by rfl) ⟨8242073, by rfl⟩ : syracuseStep 10989431 = 16484147) B16484147
theorem B7326287 : Blo 2169435 7326287 := bstep (se 1 (by rfl) ⟨5494715, by rfl⟩ : syracuseStep 7326287 = 10989431) B10989431
theorem B4884191 : Blo 2169435 4884191 := bstep (se 1 (by rfl) ⟨3663143, by rfl⟩ : syracuseStep 4884191 = 7326287) B7326287
theorem B3256127 : Blo 2169435 3256127 := bstep (se 1 (by rfl) ⟨2442095, by rfl⟩ : syracuseStep 3256127 = 4884191) B4884191
theorem B2170751 : Blo 2169435 2170751 := bstep (se 1 (by rfl) ⟨1628063, by rfl⟩ : syracuseStep 2170751 = 3256127) B3256127
theorem B3256133 : Blo 2169435 3256133 := bbase (se 4 (by rfl) ⟨305262, by rfl⟩ : syracuseStep 3256133 = 610525) (by norm_num)
theorem B2170755 : Blo 2169435 2170755 := bstep (se 1 (by rfl) ⟨1628066, by rfl⟩ : syracuseStep 2170755 = 3256133) B3256133
theorem B3663157 : Blo 2169435 3663157 := bbase (se 5 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 3663157 = 343421) (by norm_num)
theorem B4884209 : Blo 2169435 4884209 := bstep (se 2 (by rfl) ⟨1831578, by rfl⟩ : syracuseStep 4884209 = 3663157) B3663157
theorem B3256139 : Blo 2169435 3256139 := bstep (se 1 (by rfl) ⟨2442104, by rfl⟩ : syracuseStep 3256139 = 4884209) B4884209
theorem B2170759 : Blo 2169435 2170759 := bstep (se 1 (by rfl) ⟨1628069, by rfl⟩ : syracuseStep 2170759 = 3256139) B3256139
theorem B2442109 : Blo 2169435 2442109 := bbase (se 3 (by rfl) ⟨457895, by rfl⟩ : syracuseStep 2442109 = 915791) (by norm_num)
theorem B3256145 : Blo 2169435 3256145 := bstep (se 2 (by rfl) ⟨1221054, by rfl⟩ : syracuseStep 3256145 = 2442109) B2442109
theorem B2170763 : Blo 2169435 2170763 := bstep (se 1 (by rfl) ⟨1628072, by rfl⟩ : syracuseStep 2170763 = 3256145) B3256145
theorem B7326341 : Blo 2169435 7326341 := bbase (se 4 (by rfl) ⟨686844, by rfl⟩ : syracuseStep 7326341 = 1373689) (by norm_num)
theorem B4884227 : Blo 2169435 4884227 := bstep (se 1 (by rfl) ⟨3663170, by rfl⟩ : syracuseStep 4884227 = 7326341) B7326341
theorem B3256151 : Blo 2169435 3256151 := bstep (se 1 (by rfl) ⟨2442113, by rfl⟩ : syracuseStep 3256151 = 4884227) B4884227
theorem B2170767 : Blo 2169435 2170767 := bstep (se 1 (by rfl) ⟨1628075, by rfl⟩ : syracuseStep 2170767 = 3256151) B3256151
theorem B3256157 : Blo 2169435 3256157 := bbase (se 3 (by rfl) ⟨610529, by rfl⟩ : syracuseStep 3256157 = 1221059) (by norm_num)
theorem B2170771 : Blo 2169435 2170771 := bstep (se 1 (by rfl) ⟨1628078, by rfl⟩ : syracuseStep 2170771 = 3256157) B3256157
theorem B4884245 : Blo 2169435 4884245 := bbase (se 6 (by rfl) ⟨114474, by rfl⟩ : syracuseStep 4884245 = 228949) (by norm_num)
theorem B3256163 : Blo 2169435 3256163 := bstep (se 1 (by rfl) ⟨2442122, by rfl⟩ : syracuseStep 3256163 = 4884245) B4884245
theorem B2170775 : Blo 2169435 2170775 := bstep (se 1 (by rfl) ⟨1628081, by rfl⟩ : syracuseStep 2170775 = 3256163) B3256163
theorem B8242181 : Blo 2169435 8242181 := bbase (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) (by norm_num)
theorem B5494787 : Blo 2169435 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B3663191 : Blo 2169435 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B2442127 : Blo 2169435 2442127 := bstep (se 1 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 2442127 = 3663191) B3663191
theorem B3256169 : Blo 2169435 3256169 := bstep (se 2 (by rfl) ⟨1221063, by rfl⟩ : syracuseStep 3256169 = 2442127) B2442127
theorem B2170779 : Blo 2169435 2170779 := bstep (se 1 (by rfl) ⟨1628084, by rfl⟩ : syracuseStep 2170779 = 3256169) B3256169
theorem B5215765 : Blo 2169435 5215765 := bbase (se 6 (by rfl) ⟨122244, by rfl⟩ : syracuseStep 5215765 = 244489) (by norm_num)
theorem B6954353 : Blo 2169435 6954353 := bstep (se 2 (by rfl) ⟨2607882, by rfl⟩ : syracuseStep 6954353 = 5215765) B5215765
theorem B4636235 : Blo 2169435 4636235 := bstep (se 1 (by rfl) ⟨3477176, by rfl⟩ : syracuseStep 4636235 = 6954353) B6954353
theorem B12363293 : Blo 2169435 12363293 := bstep (se 3 (by rfl) ⟨2318117, by rfl⟩ : syracuseStep 12363293 = 4636235) B4636235
theorem B8242195 : Blo 2169435 8242195 := bstep (se 1 (by rfl) ⟨6181646, by rfl⟩ : syracuseStep 8242195 = 12363293) B12363293
theorem B10989593 : Blo 2169435 10989593 := bstep (se 2 (by rfl) ⟨4121097, by rfl⟩ : syracuseStep 10989593 = 8242195) B8242195
theorem B7326395 : Blo 2169435 7326395 := bstep (se 1 (by rfl) ⟨5494796, by rfl⟩ : syracuseStep 7326395 = 10989593) B10989593
theorem B4884263 : Blo 2169435 4884263 := bstep (se 1 (by rfl) ⟨3663197, by rfl⟩ : syracuseStep 4884263 = 7326395) B7326395
theorem B3256175 : Blo 2169435 3256175 := bstep (se 1 (by rfl) ⟨2442131, by rfl⟩ : syracuseStep 3256175 = 4884263) B4884263
theorem B2170783 : Blo 2169435 2170783 := bstep (se 1 (by rfl) ⟨1628087, by rfl⟩ : syracuseStep 2170783 = 3256175) B3256175
theorem B3256181 : Blo 2169435 3256181 := bbase (se 5 (by rfl) ⟨152633, by rfl⟩ : syracuseStep 3256181 = 305267) (by norm_num)
theorem B2170787 : Blo 2169435 2170787 := bstep (se 1 (by rfl) ⟨1628090, by rfl⟩ : syracuseStep 2170787 = 3256181) B3256181
theorem B4636253 : Blo 2169435 4636253 := bbase (se 3 (by rfl) ⟨869297, by rfl⟩ : syracuseStep 4636253 = 1738595) (by norm_num)
theorem B3090835 : Blo 2169435 3090835 := bstep (se 1 (by rfl) ⟨2318126, by rfl⟩ : syracuseStep 3090835 = 4636253) B4636253
theorem B4121113 : Blo 2169435 4121113 := bstep (se 2 (by rfl) ⟨1545417, by rfl⟩ : syracuseStep 4121113 = 3090835) B3090835
theorem B5494817 : Blo 2169435 5494817 := bstep (se 2 (by rfl) ⟨2060556, by rfl⟩ : syracuseStep 5494817 = 4121113) B4121113
theorem B3663211 : Blo 2169435 3663211 := bstep (se 1 (by rfl) ⟨2747408, by rfl⟩ : syracuseStep 3663211 = 5494817) B5494817
theorem B4884281 : Blo 2169435 4884281 := bstep (se 2 (by rfl) ⟨1831605, by rfl⟩ : syracuseStep 4884281 = 3663211) B3663211
theorem B3256187 : Blo 2169435 3256187 := bstep (se 1 (by rfl) ⟨2442140, by rfl⟩ : syracuseStep 3256187 = 4884281) B4884281
theorem B2170791 : Blo 2169435 2170791 := bstep (se 1 (by rfl) ⟨1628093, by rfl⟩ : syracuseStep 2170791 = 3256187) B3256187
theorem B2442145 : Blo 2169435 2442145 := bbase (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) (by norm_num)
theorem B3256193 : Blo 2169435 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B2170795 : Blo 2169435 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B5494837 : Blo 2169435 5494837 := bbase (se 5 (by rfl) ⟨257570, by rfl⟩ : syracuseStep 5494837 = 515141) (by norm_num)
theorem B7326449 : Blo 2169435 7326449 := bstep (se 2 (by rfl) ⟨2747418, by rfl⟩ : syracuseStep 7326449 = 5494837) B5494837
theorem B4884299 : Blo 2169435 4884299 := bstep (se 1 (by rfl) ⟨3663224, by rfl⟩ : syracuseStep 4884299 = 7326449) B7326449
theorem B3256199 : Blo 2169435 3256199 := bstep (se 1 (by rfl) ⟨2442149, by rfl⟩ : syracuseStep 3256199 = 4884299) B4884299
theorem B2170799 : Blo 2169435 2170799 := bstep (se 1 (by rfl) ⟨1628099, by rfl⟩ : syracuseStep 2170799 = 3256199) B3256199
theorem B3256205 : Blo 2169435 3256205 := bbase (se 3 (by rfl) ⟨610538, by rfl⟩ : syracuseStep 3256205 = 1221077) (by norm_num)
theorem B2170803 : Blo 2169435 2170803 := bstep (se 1 (by rfl) ⟨1628102, by rfl⟩ : syracuseStep 2170803 = 3256205) B3256205
theorem B4884317 : Blo 2169435 4884317 := bbase (se 3 (by rfl) ⟨915809, by rfl⟩ : syracuseStep 4884317 = 1831619) (by norm_num)
theorem B3256211 : Blo 2169435 3256211 := bstep (se 1 (by rfl) ⟨2442158, by rfl⟩ : syracuseStep 3256211 = 4884317) B4884317
theorem B2170807 : Blo 2169435 2170807 := bstep (se 1 (by rfl) ⟨1628105, by rfl⟩ : syracuseStep 2170807 = 3256211) B3256211
theorem B3663245 : Blo 2169435 3663245 := bbase (se 3 (by rfl) ⟨686858, by rfl⟩ : syracuseStep 3663245 = 1373717) (by norm_num)
theorem B2442163 : Blo 2169435 2442163 := bstep (se 1 (by rfl) ⟨1831622, by rfl⟩ : syracuseStep 2442163 = 3663245) B3663245
theorem B3256217 : Blo 2169435 3256217 := bstep (se 2 (by rfl) ⟨1221081, by rfl⟩ : syracuseStep 3256217 = 2442163) B2442163
theorem B2170811 : Blo 2169435 2170811 := bstep (se 1 (by rfl) ⟨1628108, by rfl⟩ : syracuseStep 2170811 = 3256217) B3256217
theorem B6601301 : Blo 2169435 6601301 := bbase (se 8 (by rfl) ⟨38679, by rfl⟩ : syracuseStep 6601301 = 77359) (by norm_num)
theorem B4400867 : Blo 2169435 4400867 := bstep (se 1 (by rfl) ⟨3300650, by rfl⟩ : syracuseStep 4400867 = 6601301) B6601301
theorem B2933911 : Blo 2169435 2933911 := bstep (se 1 (by rfl) ⟨2200433, by rfl⟩ : syracuseStep 2933911 = 4400867) B4400867
theorem B15647525 : Blo 2169435 15647525 := bstep (se 4 (by rfl) ⟨1466955, by rfl⟩ : syracuseStep 15647525 = 2933911) B2933911
theorem B10431683 : Blo 2169435 10431683 := bstep (se 1 (by rfl) ⟨7823762, by rfl⟩ : syracuseStep 10431683 = 15647525) B15647525
theorem B6954455 : Blo 2169435 6954455 := bstep (se 1 (by rfl) ⟨5215841, by rfl⟩ : syracuseStep 6954455 = 10431683) B10431683
theorem B18545213 : Blo 2169435 18545213 := bstep (se 3 (by rfl) ⟨3477227, by rfl⟩ : syracuseStep 18545213 = 6954455) B6954455
theorem B12363475 : Blo 2169435 12363475 := bstep (se 1 (by rfl) ⟨9272606, by rfl⟩ : syracuseStep 12363475 = 18545213) B18545213
theorem B16484633 : Blo 2169435 16484633 := bstep (se 2 (by rfl) ⟨6181737, by rfl⟩ : syracuseStep 16484633 = 12363475) B12363475
theorem B10989755 : Blo 2169435 10989755 := bstep (se 1 (by rfl) ⟨8242316, by rfl⟩ : syracuseStep 10989755 = 16484633) B16484633
theorem B7326503 : Blo 2169435 7326503 := bstep (se 1 (by rfl) ⟨5494877, by rfl⟩ : syracuseStep 7326503 = 10989755) B10989755
theorem B4884335 : Blo 2169435 4884335 := bstep (se 1 (by rfl) ⟨3663251, by rfl⟩ : syracuseStep 4884335 = 7326503) B7326503
theorem B3256223 : Blo 2169435 3256223 := bstep (se 1 (by rfl) ⟨2442167, by rfl⟩ : syracuseStep 3256223 = 4884335) B4884335
theorem B2170815 : Blo 2169435 2170815 := bstep (se 1 (by rfl) ⟨1628111, by rfl⟩ : syracuseStep 2170815 = 3256223) B3256223
theorem B3256229 : Blo 2169435 3256229 := bbase (se 4 (by rfl) ⟨305271, by rfl⟩ : syracuseStep 3256229 = 610543) (by norm_num)
theorem B2170819 : Blo 2169435 2170819 := bstep (se 1 (by rfl) ⟨1628114, by rfl⟩ : syracuseStep 2170819 = 3256229) B3256229
theorem B2747449 : Blo 2169435 2747449 := bbase (se 2 (by rfl) ⟨1030293, by rfl⟩ : syracuseStep 2747449 = 2060587) (by norm_num)
theorem B3663265 : Blo 2169435 3663265 := bstep (se 2 (by rfl) ⟨1373724, by rfl⟩ : syracuseStep 3663265 = 2747449) B2747449
theorem B4884353 : Blo 2169435 4884353 := bstep (se 2 (by rfl) ⟨1831632, by rfl⟩ : syracuseStep 4884353 = 3663265) B3663265
theorem B3256235 : Blo 2169435 3256235 := bstep (se 1 (by rfl) ⟨2442176, by rfl⟩ : syracuseStep 3256235 = 4884353) B4884353
theorem B2170823 : Blo 2169435 2170823 := bstep (se 1 (by rfl) ⟨1628117, by rfl⟩ : syracuseStep 2170823 = 3256235) B3256235
theorem B2442181 : Blo 2169435 2442181 := bbase (se 4 (by rfl) ⟨228954, by rfl⟩ : syracuseStep 2442181 = 457909) (by norm_num)
theorem B3256241 : Blo 2169435 3256241 := bstep (se 2 (by rfl) ⟨1221090, by rfl⟩ : syracuseStep 3256241 = 2442181) B2442181
theorem B2170827 : Blo 2169435 2170827 := bstep (se 1 (by rfl) ⟨1628120, by rfl⟩ : syracuseStep 2170827 = 3256241) B3256241
theorem B4121189 : Blo 2169435 4121189 := bbase (se 4 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 4121189 = 772723) (by norm_num)
theorem B2747459 : Blo 2169435 2747459 := bstep (se 1 (by rfl) ⟨2060594, by rfl⟩ : syracuseStep 2747459 = 4121189) B4121189
theorem B7326557 : Blo 2169435 7326557 := bstep (se 3 (by rfl) ⟨1373729, by rfl⟩ : syracuseStep 7326557 = 2747459) B2747459
theorem B4884371 : Blo 2169435 4884371 := bstep (se 1 (by rfl) ⟨3663278, by rfl⟩ : syracuseStep 4884371 = 7326557) B7326557
theorem B3256247 : Blo 2169435 3256247 := bstep (se 1 (by rfl) ⟨2442185, by rfl⟩ : syracuseStep 3256247 = 4884371) B4884371
theorem B2170831 : Blo 2169435 2170831 := bstep (se 1 (by rfl) ⟨1628123, by rfl⟩ : syracuseStep 2170831 = 3256247) B3256247
theorem B3256253 : Blo 2169435 3256253 := bbase (se 3 (by rfl) ⟨610547, by rfl⟩ : syracuseStep 3256253 = 1221095) (by norm_num)
theorem B2170835 : Blo 2169435 2170835 := bstep (se 1 (by rfl) ⟨1628126, by rfl⟩ : syracuseStep 2170835 = 3256253) B3256253
theorem B4884389 : Blo 2169435 4884389 := bbase (se 4 (by rfl) ⟨457911, by rfl⟩ : syracuseStep 4884389 = 915823) (by norm_num)
theorem B3256259 : Blo 2169435 3256259 := bstep (se 1 (by rfl) ⟨2442194, by rfl⟩ : syracuseStep 3256259 = 4884389) B4884389
theorem B2170839 : Blo 2169435 2170839 := bstep (se 1 (by rfl) ⟨1628129, by rfl⟩ : syracuseStep 2170839 = 3256259) B3256259
theorem B5494949 : Blo 2169435 5494949 := bbase (se 4 (by rfl) ⟨515151, by rfl⟩ : syracuseStep 5494949 = 1030303) (by norm_num)
theorem B3663299 : Blo 2169435 3663299 := bstep (se 1 (by rfl) ⟨2747474, by rfl⟩ : syracuseStep 3663299 = 5494949) B5494949
theorem B2442199 : Blo 2169435 2442199 := bstep (se 1 (by rfl) ⟨1831649, by rfl⟩ : syracuseStep 2442199 = 3663299) B3663299
theorem B3256265 : Blo 2169435 3256265 := bstep (se 2 (by rfl) ⟨1221099, by rfl⟩ : syracuseStep 3256265 = 2442199) B2442199
theorem B2170843 : Blo 2169435 2170843 := bstep (se 1 (by rfl) ⟨1628132, by rfl⟩ : syracuseStep 2170843 = 3256265) B3256265
theorem B6181829 : Blo 2169435 6181829 := bbase (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) (by norm_num)
theorem B4121219 : Blo 2169435 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B10989917 : Blo 2169435 10989917 := bstep (se 3 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 10989917 = 4121219) B4121219
theorem B7326611 : Blo 2169435 7326611 := bstep (se 1 (by rfl) ⟨5494958, by rfl⟩ : syracuseStep 7326611 = 10989917) B10989917
theorem B4884407 : Blo 2169435 4884407 := bstep (se 1 (by rfl) ⟨3663305, by rfl⟩ : syracuseStep 4884407 = 7326611) B7326611
theorem B3256271 : Blo 2169435 3256271 := bstep (se 1 (by rfl) ⟨2442203, by rfl⟩ : syracuseStep 3256271 = 4884407) B4884407
theorem B2170847 : Blo 2169435 2170847 := bstep (se 1 (by rfl) ⟨1628135, by rfl⟩ : syracuseStep 2170847 = 3256271) B3256271
theorem B3256277 : Blo 2169435 3256277 := bbase (se 7 (by rfl) ⟨38159, by rfl⟩ : syracuseStep 3256277 = 76319) (by norm_num)
theorem B2170851 : Blo 2169435 2170851 := bstep (se 1 (by rfl) ⟨1628138, by rfl⟩ : syracuseStep 2170851 = 3256277) B3256277
theorem B8242469 : Blo 2169435 8242469 := bbase (se 4 (by rfl) ⟨772731, by rfl⟩ : syracuseStep 8242469 = 1545463) (by norm_num)
theorem B5494979 : Blo 2169435 5494979 := bstep (se 1 (by rfl) ⟨4121234, by rfl⟩ : syracuseStep 5494979 = 8242469) B8242469
theorem B3663319 : Blo 2169435 3663319 := bstep (se 1 (by rfl) ⟨2747489, by rfl⟩ : syracuseStep 3663319 = 5494979) B5494979
theorem B4884425 : Blo 2169435 4884425 := bstep (se 2 (by rfl) ⟨1831659, by rfl⟩ : syracuseStep 4884425 = 3663319) B3663319
theorem B3256283 : Blo 2169435 3256283 := bstep (se 1 (by rfl) ⟨2442212, by rfl⟩ : syracuseStep 3256283 = 4884425) B4884425
theorem B2170855 : Blo 2169435 2170855 := bstep (se 1 (by rfl) ⟨1628141, by rfl⟩ : syracuseStep 2170855 = 3256283) B3256283
theorem B2442217 : Blo 2169435 2442217 := bbase (se 2 (by rfl) ⟨915831, by rfl⟩ : syracuseStep 2442217 = 1831663) (by norm_num)
theorem B3256289 : Blo 2169435 3256289 := bstep (se 2 (by rfl) ⟨1221108, by rfl⟩ : syracuseStep 3256289 = 2442217) B2442217
theorem B2170859 : Blo 2169435 2170859 := bstep (se 1 (by rfl) ⟨1628144, by rfl⟩ : syracuseStep 2170859 = 3256289) B3256289
theorem B3300725 : Blo 2169435 3300725 := bbase (se 5 (by rfl) ⟨154721, by rfl⟩ : syracuseStep 3300725 = 309443) (by norm_num)
theorem B2200483 : Blo 2169435 2200483 := bstep (se 1 (by rfl) ⟨1650362, by rfl⟩ : syracuseStep 2200483 = 3300725) B3300725
theorem B2933977 : Blo 2169435 2933977 := bstep (se 2 (by rfl) ⟨1100241, by rfl⟩ : syracuseStep 2933977 = 2200483) B2200483
theorem B3911969 : Blo 2169435 3911969 := bstep (se 2 (by rfl) ⟨1466988, by rfl⟩ : syracuseStep 3911969 = 2933977) B2933977
theorem B2607979 : Blo 2169435 2607979 := bstep (se 1 (by rfl) ⟨1955984, by rfl⟩ : syracuseStep 2607979 = 3911969) B3911969
theorem B3477305 : Blo 2169435 3477305 := bstep (se 2 (by rfl) ⟨1303989, by rfl⟩ : syracuseStep 3477305 = 2607979) B2607979
theorem B2318203 : Blo 2169435 2318203 := bstep (se 1 (by rfl) ⟨1738652, by rfl⟩ : syracuseStep 2318203 = 3477305) B3477305
theorem B12363749 : Blo 2169435 12363749 := bstep (se 4 (by rfl) ⟨1159101, by rfl⟩ : syracuseStep 12363749 = 2318203) B2318203
theorem B8242499 : Blo 2169435 8242499 := bstep (se 1 (by rfl) ⟨6181874, by rfl⟩ : syracuseStep 8242499 = 12363749) B12363749
theorem B5494999 : Blo 2169435 5494999 := bstep (se 1 (by rfl) ⟨4121249, by rfl⟩ : syracuseStep 5494999 = 8242499) B8242499
theorem B7326665 : Blo 2169435 7326665 := bstep (se 2 (by rfl) ⟨2747499, by rfl⟩ : syracuseStep 7326665 = 5494999) B5494999
theorem B4884443 : Blo 2169435 4884443 := bstep (se 1 (by rfl) ⟨3663332, by rfl⟩ : syracuseStep 4884443 = 7326665) B7326665
theorem B3256295 : Blo 2169435 3256295 := bstep (se 1 (by rfl) ⟨2442221, by rfl⟩ : syracuseStep 3256295 = 4884443) B4884443
theorem B2170863 : Blo 2169435 2170863 := bstep (se 1 (by rfl) ⟨1628147, by rfl⟩ : syracuseStep 2170863 = 3256295) B3256295
theorem B3256301 : Blo 2169435 3256301 := bbase (se 3 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 3256301 = 1221113) (by norm_num)
theorem B2170867 : Blo 2169435 2170867 := bstep (se 1 (by rfl) ⟨1628150, by rfl⟩ : syracuseStep 2170867 = 3256301) B3256301
theorem B4884461 : Blo 2169435 4884461 := bbase (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) (by norm_num)
theorem B3256307 : Blo 2169435 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B2170871 : Blo 2169435 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B3477325 : Blo 2169435 3477325 := bbase (se 3 (by rfl) ⟨651998, by rfl⟩ : syracuseStep 3477325 = 1303997) (by norm_num)
theorem B4636433 : Blo 2169435 4636433 := bstep (se 2 (by rfl) ⟨1738662, by rfl⟩ : syracuseStep 4636433 = 3477325) B3477325
theorem B3090955 : Blo 2169435 3090955 := bstep (se 1 (by rfl) ⟨2318216, by rfl⟩ : syracuseStep 3090955 = 4636433) B4636433
theorem B4121273 : Blo 2169435 4121273 := bstep (se 2 (by rfl) ⟨1545477, by rfl⟩ : syracuseStep 4121273 = 3090955) B3090955
theorem B2747515 : Blo 2169435 2747515 := bstep (se 1 (by rfl) ⟨2060636, by rfl⟩ : syracuseStep 2747515 = 4121273) B4121273
theorem B3663353 : Blo 2169435 3663353 := bstep (se 2 (by rfl) ⟨1373757, by rfl⟩ : syracuseStep 3663353 = 2747515) B2747515
theorem B2442235 : Blo 2169435 2442235 := bstep (se 1 (by rfl) ⟨1831676, by rfl⟩ : syracuseStep 2442235 = 3663353) B3663353
theorem B3256313 : Blo 2169435 3256313 := bstep (se 2 (by rfl) ⟨1221117, by rfl⟩ : syracuseStep 3256313 = 2442235) B2442235
theorem B2170875 : Blo 2169435 2170875 := bstep (se 1 (by rfl) ⟨1628156, by rfl⟩ : syracuseStep 2170875 = 3256313) B3256313
theorem B11140021 : Blo 2169435 11140021 := bbase (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) (by norm_num)
theorem B14853361 : Blo 2169435 14853361 := bstep (se 2 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 14853361 = 11140021) B11140021
theorem B19804481 : Blo 2169435 19804481 := bstep (se 2 (by rfl) ⟨7426680, by rfl⟩ : syracuseStep 19804481 = 14853361) B14853361
theorem B211247797 : Blo 2169435 211247797 := bstep (se 5 (by rfl) ⟨9902240, by rfl⟩ : syracuseStep 211247797 = 19804481) B19804481
theorem B281663729 : Blo 2169435 281663729 := bstep (se 2 (by rfl) ⟨105623898, by rfl⟩ : syracuseStep 281663729 = 211247797) B211247797
theorem B187775819 : Blo 2169435 187775819 := bstep (se 1 (by rfl) ⟨140831864, by rfl⟩ : syracuseStep 187775819 = 281663729) B281663729
theorem B125183879 : Blo 2169435 125183879 := bstep (se 1 (by rfl) ⟨93887909, by rfl⟩ : syracuseStep 125183879 = 187775819) B187775819
theorem B83455919 : Blo 2169435 83455919 := bstep (se 1 (by rfl) ⟨62591939, by rfl⟩ : syracuseStep 83455919 = 125183879) B125183879
theorem B55637279 : Blo 2169435 55637279 := bstep (se 1 (by rfl) ⟨41727959, by rfl⟩ : syracuseStep 55637279 = 83455919) B83455919
theorem B37091519 : Blo 2169435 37091519 := bstep (se 1 (by rfl) ⟨27818639, by rfl⟩ : syracuseStep 37091519 = 55637279) B55637279
theorem B24727679 : Blo 2169435 24727679 := bstep (se 1 (by rfl) ⟨18545759, by rfl⟩ : syracuseStep 24727679 = 37091519) B37091519
theorem B16485119 : Blo 2169435 16485119 := bstep (se 1 (by rfl) ⟨12363839, by rfl⟩ : syracuseStep 16485119 = 24727679) B24727679
theorem B10990079 : Blo 2169435 10990079 := bstep (se 1 (by rfl) ⟨8242559, by rfl⟩ : syracuseStep 10990079 = 16485119) B16485119
theorem B7326719 : Blo 2169435 7326719 := bstep (se 1 (by rfl) ⟨5495039, by rfl⟩ : syracuseStep 7326719 = 10990079) B10990079
theorem B4884479 : Blo 2169435 4884479 := bstep (se 1 (by rfl) ⟨3663359, by rfl⟩ : syracuseStep 4884479 = 7326719) B7326719
theorem B3256319 : Blo 2169435 3256319 := bstep (se 1 (by rfl) ⟨2442239, by rfl⟩ : syracuseStep 3256319 = 4884479) B4884479
theorem B2170879 : Blo 2169435 2170879 := bstep (se 1 (by rfl) ⟨1628159, by rfl⟩ : syracuseStep 2170879 = 3256319) B3256319
theorem B3256325 : Blo 2169435 3256325 := bbase (se 4 (by rfl) ⟨305280, by rfl⟩ : syracuseStep 3256325 = 610561) (by norm_num)
theorem B2170883 : Blo 2169435 2170883 := bstep (se 1 (by rfl) ⟨1628162, by rfl⟩ : syracuseStep 2170883 = 3256325) B3256325
theorem B3663373 : Blo 2169435 3663373 := bbase (se 3 (by rfl) ⟨686882, by rfl⟩ : syracuseStep 3663373 = 1373765) (by norm_num)
theorem B4884497 : Blo 2169435 4884497 := bstep (se 2 (by rfl) ⟨1831686, by rfl⟩ : syracuseStep 4884497 = 3663373) B3663373
theorem B3256331 : Blo 2169435 3256331 := bstep (se 1 (by rfl) ⟨2442248, by rfl⟩ : syracuseStep 3256331 = 4884497) B4884497
theorem B2170887 : Blo 2169435 2170887 := bstep (se 1 (by rfl) ⟨1628165, by rfl⟩ : syracuseStep 2170887 = 3256331) B3256331
theorem B2442253 : Blo 2169435 2442253 := bbase (se 3 (by rfl) ⟨457922, by rfl⟩ : syracuseStep 2442253 = 915845) (by norm_num)
theorem B3256337 : Blo 2169435 3256337 := bstep (se 2 (by rfl) ⟨1221126, by rfl⟩ : syracuseStep 3256337 = 2442253) B2442253
theorem B2170891 : Blo 2169435 2170891 := bstep (se 1 (by rfl) ⟨1628168, by rfl⟩ : syracuseStep 2170891 = 3256337) B3256337
theorem B7326773 : Blo 2169435 7326773 := bbase (se 5 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 7326773 = 686885) (by norm_num)
theorem B4884515 : Blo 2169435 4884515 := bstep (se 1 (by rfl) ⟨3663386, by rfl⟩ : syracuseStep 4884515 = 7326773) B7326773
theorem B3256343 : Blo 2169435 3256343 := bstep (se 1 (by rfl) ⟨2442257, by rfl⟩ : syracuseStep 3256343 = 4884515) B4884515
theorem B2170895 : Blo 2169435 2170895 := bstep (se 1 (by rfl) ⟨1628171, by rfl⟩ : syracuseStep 2170895 = 3256343) B3256343
theorem B3256349 : Blo 2169435 3256349 := bbase (se 3 (by rfl) ⟨610565, by rfl⟩ : syracuseStep 3256349 = 1221131) (by norm_num)
theorem B2170899 : Blo 2169435 2170899 := bstep (se 1 (by rfl) ⟨1628174, by rfl⟩ : syracuseStep 2170899 = 3256349) B3256349
theorem B4884533 : Blo 2169435 4884533 := bbase (se 5 (by rfl) ⟨228962, by rfl⟩ : syracuseStep 4884533 = 457925) (by norm_num)
theorem B3256355 : Blo 2169435 3256355 := bstep (se 1 (by rfl) ⟨2442266, by rfl⟩ : syracuseStep 3256355 = 4884533) B4884533
theorem B2170903 : Blo 2169435 2170903 := bstep (se 1 (by rfl) ⟨1628177, by rfl⟩ : syracuseStep 2170903 = 3256355) B3256355
theorem B2543605 : Blo 2169435 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B13565893 : Blo 2169435 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B18087857 : Blo 2169435 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B12058571 : Blo 2169435 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B32156189 : Blo 2169435 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B21437459 : Blo 2169435 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B14291639 : Blo 2169435 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B9527759 : Blo 2169435 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B6351839 : Blo 2169435 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B4234559 : Blo 2169435 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B11292157 : Blo 2169435 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B15056209 : Blo 2169435 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B80299781 : Blo 2169435 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B53533187 : Blo 2169435 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B35688791 : Blo 2169435 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B23792527 : Blo 2169435 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B31723369 : Blo 2169435 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B676765205 : Blo 2169435 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B451176803 : Blo 2169435 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B300784535 : Blo 2169435 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B200523023 : Blo 2169435 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B133682015 : Blo 2169435 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B89121343 : Blo 2169435 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B118828457 : Blo 2169435 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B79218971 : Blo 2169435 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B52812647 : Blo 2169435 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B35208431 : Blo 2169435 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B23472287 : Blo 2169435 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B15648191 : Blo 2169435 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B10432127 : Blo 2169435 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B6954751 : Blo 2169435 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B9273001 : Blo 2169435 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B12364001 : Blo 2169435 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B8242667 : Blo 2169435 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B5495111 : Blo 2169435 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B3663407 : Blo 2169435 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B2442271 : Blo 2169435 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B3256361 : Blo 2169435 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B2170907 : Blo 2169435 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B3300797 : Blo 2169435 3300797 := bbase (se 3 (by rfl) ⟨618899, by rfl⟩ : syracuseStep 3300797 = 1237799) (by norm_num)
theorem B2200531 : Blo 2169435 2200531 := bstep (se 1 (by rfl) ⟨1650398, by rfl⟩ : syracuseStep 2200531 = 3300797) B3300797
theorem B2934041 : Blo 2169435 2934041 := bstep (se 2 (by rfl) ⟨1100265, by rfl⟩ : syracuseStep 2934041 = 2200531) B2200531
theorem B7824109 : Blo 2169435 7824109 := bstep (se 3 (by rfl) ⟨1467020, by rfl⟩ : syracuseStep 7824109 = 2934041) B2934041
theorem B10432145 : Blo 2169435 10432145 := bstep (se 2 (by rfl) ⟨3912054, by rfl⟩ : syracuseStep 10432145 = 7824109) B7824109
theorem B6954763 : Blo 2169435 6954763 := bstep (se 1 (by rfl) ⟨5216072, by rfl⟩ : syracuseStep 6954763 = 10432145) B10432145
theorem B9273017 : Blo 2169435 9273017 := bstep (se 2 (by rfl) ⟨3477381, by rfl⟩ : syracuseStep 9273017 = 6954763) B6954763
theorem B6182011 : Blo 2169435 6182011 := bstep (se 1 (by rfl) ⟨4636508, by rfl⟩ : syracuseStep 6182011 = 9273017) B9273017
theorem B8242681 : Blo 2169435 8242681 := bstep (se 2 (by rfl) ⟨3091005, by rfl⟩ : syracuseStep 8242681 = 6182011) B6182011
theorem B10990241 : Blo 2169435 10990241 := bstep (se 2 (by rfl) ⟨4121340, by rfl⟩ : syracuseStep 10990241 = 8242681) B8242681
theorem B7326827 : Blo 2169435 7326827 := bstep (se 1 (by rfl) ⟨5495120, by rfl⟩ : syracuseStep 7326827 = 10990241) B10990241
theorem B4884551 : Blo 2169435 4884551 := bstep (se 1 (by rfl) ⟨3663413, by rfl⟩ : syracuseStep 4884551 = 7326827) B7326827
theorem B3256367 : Blo 2169435 3256367 := bstep (se 1 (by rfl) ⟨2442275, by rfl⟩ : syracuseStep 3256367 = 4884551) B4884551
theorem B2170911 : Blo 2169435 2170911 := bstep (se 1 (by rfl) ⟨1628183, by rfl⟩ : syracuseStep 2170911 = 3256367) B3256367
theorem B3256373 : Blo 2169435 3256373 := bbase (se 5 (by rfl) ⟨152642, by rfl⟩ : syracuseStep 3256373 = 305285) (by norm_num)
theorem B2170915 : Blo 2169435 2170915 := bstep (se 1 (by rfl) ⟨1628186, by rfl⟩ : syracuseStep 2170915 = 3256373) B3256373
theorem B5495141 : Blo 2169435 5495141 := bbase (se 4 (by rfl) ⟨515169, by rfl⟩ : syracuseStep 5495141 = 1030339) (by norm_num)
theorem B3663427 : Blo 2169435 3663427 := bstep (se 1 (by rfl) ⟨2747570, by rfl⟩ : syracuseStep 3663427 = 5495141) B5495141
theorem B4884569 : Blo 2169435 4884569 := bstep (se 2 (by rfl) ⟨1831713, by rfl⟩ : syracuseStep 4884569 = 3663427) B3663427
theorem B3256379 : Blo 2169435 3256379 := bstep (se 1 (by rfl) ⟨2442284, by rfl⟩ : syracuseStep 3256379 = 4884569) B4884569
theorem B2170919 : Blo 2169435 2170919 := bstep (se 1 (by rfl) ⟨1628189, by rfl⟩ : syracuseStep 2170919 = 3256379) B3256379
theorem B2442289 : Blo 2169435 2442289 := bbase (se 2 (by rfl) ⟨915858, by rfl⟩ : syracuseStep 2442289 = 1831717) (by norm_num)
theorem B3256385 : Blo 2169435 3256385 := bstep (se 2 (by rfl) ⟨1221144, by rfl⟩ : syracuseStep 3256385 = 2442289) B2442289
theorem B2170923 : Blo 2169435 2170923 := bstep (se 1 (by rfl) ⟨1628192, by rfl⟩ : syracuseStep 2170923 = 3256385) B3256385
theorem B2543629 : Blo 2169435 2543629 := bbase (se 3 (by rfl) ⟨476930, by rfl⟩ : syracuseStep 2543629 = 953861) (by norm_num)
theorem B3391505 : Blo 2169435 3391505 := bstep (se 2 (by rfl) ⟨1271814, by rfl⟩ : syracuseStep 3391505 = 2543629) B2543629
theorem B2261003 : Blo 2169435 2261003 := bstep (se 1 (by rfl) ⟨1695752, by rfl⟩ : syracuseStep 2261003 = 3391505) B3391505
theorem B24117365 : Blo 2169435 24117365 := bstep (se 5 (by rfl) ⟨1130501, by rfl⟩ : syracuseStep 24117365 = 2261003) B2261003
theorem B64312973 : Blo 2169435 64312973 := bstep (se 3 (by rfl) ⟨12058682, by rfl⟩ : syracuseStep 64312973 = 24117365) B24117365
theorem B42875315 : Blo 2169435 42875315 := bstep (se 1 (by rfl) ⟨32156486, by rfl⟩ : syracuseStep 42875315 = 64312973) B64312973
theorem B28583543 : Blo 2169435 28583543 := bstep (se 1 (by rfl) ⟨21437657, by rfl⟩ : syracuseStep 28583543 = 42875315) B42875315
theorem B76222781 : Blo 2169435 76222781 := bstep (se 3 (by rfl) ⟨14291771, by rfl⟩ : syracuseStep 76222781 = 28583543) B28583543
theorem B50815187 : Blo 2169435 50815187 := bstep (se 1 (by rfl) ⟨38111390, by rfl⟩ : syracuseStep 50815187 = 76222781) B76222781
theorem B33876791 : Blo 2169435 33876791 := bstep (se 1 (by rfl) ⟨25407593, by rfl⟩ : syracuseStep 33876791 = 50815187) B50815187
theorem B22584527 : Blo 2169435 22584527 := bstep (se 1 (by rfl) ⟨16938395, by rfl⟩ : syracuseStep 22584527 = 33876791) B33876791
theorem B15056351 : Blo 2169435 15056351 := bstep (se 1 (by rfl) ⟨11292263, by rfl⟩ : syracuseStep 15056351 = 22584527) B22584527
theorem B10037567 : Blo 2169435 10037567 := bstep (se 1 (by rfl) ⟨7528175, by rfl⟩ : syracuseStep 10037567 = 15056351) B15056351
theorem B26766845 : Blo 2169435 26766845 := bstep (se 3 (by rfl) ⟨5018783, by rfl⟩ : syracuseStep 26766845 = 10037567) B10037567
theorem B17844563 : Blo 2169435 17844563 := bstep (se 1 (by rfl) ⟨13383422, by rfl⟩ : syracuseStep 17844563 = 26766845) B26766845
theorem B11896375 : Blo 2169435 11896375 := bstep (se 1 (by rfl) ⟨8922281, by rfl⟩ : syracuseStep 11896375 = 17844563) B17844563
theorem B15861833 : Blo 2169435 15861833 := bstep (se 2 (by rfl) ⟨5948187, by rfl⟩ : syracuseStep 15861833 = 11896375) B11896375
theorem B10574555 : Blo 2169435 10574555 := bstep (se 1 (by rfl) ⟨7930916, by rfl⟩ : syracuseStep 10574555 = 15861833) B15861833
theorem B28198813 : Blo 2169435 28198813 := bstep (se 3 (by rfl) ⟨5287277, by rfl⟩ : syracuseStep 28198813 = 10574555) B10574555
theorem B37598417 : Blo 2169435 37598417 := bstep (se 2 (by rfl) ⟨14099406, by rfl⟩ : syracuseStep 37598417 = 28198813) B28198813
theorem B25065611 : Blo 2169435 25065611 := bstep (se 1 (by rfl) ⟨18799208, by rfl⟩ : syracuseStep 25065611 = 37598417) B37598417
theorem B16710407 : Blo 2169435 16710407 := bstep (se 1 (by rfl) ⟨12532805, by rfl⟩ : syracuseStep 16710407 = 25065611) B25065611
theorem B11140271 : Blo 2169435 11140271 := bstep (se 1 (by rfl) ⟨8355203, by rfl⟩ : syracuseStep 11140271 = 16710407) B16710407
theorem B7426847 : Blo 2169435 7426847 := bstep (se 1 (by rfl) ⟨5570135, by rfl⟩ : syracuseStep 7426847 = 11140271) B11140271
theorem B19804925 : Blo 2169435 19804925 := bstep (se 3 (by rfl) ⟨3713423, by rfl⟩ : syracuseStep 19804925 = 7426847) B7426847
theorem B52813133 : Blo 2169435 52813133 := bstep (se 3 (by rfl) ⟨9902462, by rfl⟩ : syracuseStep 52813133 = 19804925) B19804925
theorem B35208755 : Blo 2169435 35208755 := bstep (se 1 (by rfl) ⟨26406566, by rfl⟩ : syracuseStep 35208755 = 52813133) B52813133
theorem B23472503 : Blo 2169435 23472503 := bstep (se 1 (by rfl) ⟨17604377, by rfl⟩ : syracuseStep 23472503 = 35208755) B35208755
theorem B15648335 : Blo 2169435 15648335 := bstep (se 1 (by rfl) ⟨11736251, by rfl⟩ : syracuseStep 15648335 = 23472503) B23472503
theorem B10432223 : Blo 2169435 10432223 := bstep (se 1 (by rfl) ⟨7824167, by rfl⟩ : syracuseStep 10432223 = 15648335) B15648335
theorem B6954815 : Blo 2169435 6954815 := bstep (se 1 (by rfl) ⟨5216111, by rfl⟩ : syracuseStep 6954815 = 10432223) B10432223
theorem B4636543 : Blo 2169435 4636543 := bstep (se 1 (by rfl) ⟨3477407, by rfl⟩ : syracuseStep 4636543 = 6954815) B6954815
theorem B6182057 : Blo 2169435 6182057 := bstep (se 2 (by rfl) ⟨2318271, by rfl⟩ : syracuseStep 6182057 = 4636543) B4636543
theorem B4121371 : Blo 2169435 4121371 := bstep (se 1 (by rfl) ⟨3091028, by rfl⟩ : syracuseStep 4121371 = 6182057) B6182057
theorem B5495161 : Blo 2169435 5495161 := bstep (se 2 (by rfl) ⟨2060685, by rfl⟩ : syracuseStep 5495161 = 4121371) B4121371
theorem B7326881 : Blo 2169435 7326881 := bstep (se 2 (by rfl) ⟨2747580, by rfl⟩ : syracuseStep 7326881 = 5495161) B5495161
theorem B4884587 : Blo 2169435 4884587 := bstep (se 1 (by rfl) ⟨3663440, by rfl⟩ : syracuseStep 4884587 = 7326881) B7326881
theorem B3256391 : Blo 2169435 3256391 := bstep (se 1 (by rfl) ⟨2442293, by rfl⟩ : syracuseStep 3256391 = 4884587) B4884587
theorem B2170927 : Blo 2169435 2170927 := bstep (se 1 (by rfl) ⟨1628195, by rfl⟩ : syracuseStep 2170927 = 3256391) B3256391
theorem B3256397 : Blo 2169435 3256397 := bbase (se 3 (by rfl) ⟨610574, by rfl⟩ : syracuseStep 3256397 = 1221149) (by norm_num)
theorem B2170931 : Blo 2169435 2170931 := bstep (se 1 (by rfl) ⟨1628198, by rfl⟩ : syracuseStep 2170931 = 3256397) B3256397
theorem B4884605 : Blo 2169435 4884605 := bbase (se 3 (by rfl) ⟨915863, by rfl⟩ : syracuseStep 4884605 = 1831727) (by norm_num)
theorem B3256403 : Blo 2169435 3256403 := bstep (se 1 (by rfl) ⟨2442302, by rfl⟩ : syracuseStep 3256403 = 4884605) B4884605
theorem B2170935 : Blo 2169435 2170935 := bstep (se 1 (by rfl) ⟨1628201, by rfl⟩ : syracuseStep 2170935 = 3256403) B3256403
theorem B3663461 : Blo 2169435 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2442307 : Blo 2169435 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B3256409 : Blo 2169435 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B2170939 : Blo 2169435 2170939 := bstep (se 1 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 2170939 = 3256409) B3256409
theorem B2934085 : Blo 2169435 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B3912113 : Blo 2169435 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B2608075 : Blo 2169435 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B3477433 : Blo 2169435 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B4636577 : Blo 2169435 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B3091051 : Blo 2169435 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B16485605 : Blo 2169435 16485605 := bstep (se 4 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 16485605 = 3091051) B3091051
theorem B10990403 : Blo 2169435 10990403 := bstep (se 1 (by rfl) ⟨8242802, by rfl⟩ : syracuseStep 10990403 = 16485605) B16485605
theorem B7326935 : Blo 2169435 7326935 := bstep (se 1 (by rfl) ⟨5495201, by rfl⟩ : syracuseStep 7326935 = 10990403) B10990403
theorem B4884623 : Blo 2169435 4884623 := bstep (se 1 (by rfl) ⟨3663467, by rfl⟩ : syracuseStep 4884623 = 7326935) B7326935
theorem B3256415 : Blo 2169435 3256415 := bstep (se 1 (by rfl) ⟨2442311, by rfl⟩ : syracuseStep 3256415 = 4884623) B4884623
theorem B2170943 : Blo 2169435 2170943 := bstep (se 1 (by rfl) ⟨1628207, by rfl⟩ : syracuseStep 2170943 = 3256415) B3256415
theorem B3256421 : Blo 2169435 3256421 := bbase (se 4 (by rfl) ⟨305289, by rfl⟩ : syracuseStep 3256421 = 610579) (by norm_num)
theorem B2170947 : Blo 2169435 2170947 := bstep (se 1 (by rfl) ⟨1628210, by rfl⟩ : syracuseStep 2170947 = 3256421) B3256421
theorem B2608085 : Blo 2169435 2608085 := bbase (se 7 (by rfl) ⟨30563, by rfl⟩ : syracuseStep 2608085 = 61127) (by norm_num)
theorem B6954893 : Blo 2169435 6954893 := bstep (se 3 (by rfl) ⟨1304042, by rfl⟩ : syracuseStep 6954893 = 2608085) B2608085
theorem B4636595 : Blo 2169435 4636595 := bstep (se 1 (by rfl) ⟨3477446, by rfl⟩ : syracuseStep 4636595 = 6954893) B6954893
theorem B3091063 : Blo 2169435 3091063 := bstep (se 1 (by rfl) ⟨2318297, by rfl⟩ : syracuseStep 3091063 = 4636595) B4636595
theorem B4121417 : Blo 2169435 4121417 := bstep (se 2 (by rfl) ⟨1545531, by rfl⟩ : syracuseStep 4121417 = 3091063) B3091063
theorem B2747611 : Blo 2169435 2747611 := bstep (se 1 (by rfl) ⟨2060708, by rfl⟩ : syracuseStep 2747611 = 4121417) B4121417
theorem B3663481 : Blo 2169435 3663481 := bstep (se 2 (by rfl) ⟨1373805, by rfl⟩ : syracuseStep 3663481 = 2747611) B2747611
theorem B4884641 : Blo 2169435 4884641 := bstep (se 2 (by rfl) ⟨1831740, by rfl⟩ : syracuseStep 4884641 = 3663481) B3663481
theorem B3256427 : Blo 2169435 3256427 := bstep (se 1 (by rfl) ⟨2442320, by rfl⟩ : syracuseStep 3256427 = 4884641) B4884641
theorem B2170951 : Blo 2169435 2170951 := bstep (se 1 (by rfl) ⟨1628213, by rfl⟩ : syracuseStep 2170951 = 3256427) B3256427
theorem B2442325 : Blo 2169435 2442325 := bbase (se 8 (by rfl) ⟨14310, by rfl⟩ : syracuseStep 2442325 = 28621) (by norm_num)
theorem B3256433 : Blo 2169435 3256433 := bstep (se 2 (by rfl) ⟨1221162, by rfl⟩ : syracuseStep 3256433 = 2442325) B2442325
theorem B2170955 : Blo 2169435 2170955 := bstep (se 1 (by rfl) ⟨1628216, by rfl⟩ : syracuseStep 2170955 = 3256433) B3256433
theorem B2747621 : Blo 2169435 2747621 := bbase (se 4 (by rfl) ⟨257589, by rfl⟩ : syracuseStep 2747621 = 515179) (by norm_num)
theorem B7326989 : Blo 2169435 7326989 := bstep (se 3 (by rfl) ⟨1373810, by rfl⟩ : syracuseStep 7326989 = 2747621) B2747621
theorem B4884659 : Blo 2169435 4884659 := bstep (se 1 (by rfl) ⟨3663494, by rfl⟩ : syracuseStep 4884659 = 7326989) B7326989
theorem B3256439 : Blo 2169435 3256439 := bstep (se 1 (by rfl) ⟨2442329, by rfl⟩ : syracuseStep 3256439 = 4884659) B4884659
theorem B2170959 : Blo 2169435 2170959 := bstep (se 1 (by rfl) ⟨1628219, by rfl⟩ : syracuseStep 2170959 = 3256439) B3256439
theorem B3256445 : Blo 2169435 3256445 := bbase (se 3 (by rfl) ⟨610583, by rfl⟩ : syracuseStep 3256445 = 1221167) (by norm_num)
theorem B2170963 : Blo 2169435 2170963 := bstep (se 1 (by rfl) ⟨1628222, by rfl⟩ : syracuseStep 2170963 = 3256445) B3256445
theorem B4884677 : Blo 2169435 4884677 := bbase (se 4 (by rfl) ⟨457938, by rfl⟩ : syracuseStep 4884677 = 915877) (by norm_num)
theorem B3256451 : Blo 2169435 3256451 := bstep (se 1 (by rfl) ⟨2442338, by rfl⟩ : syracuseStep 3256451 = 4884677) B4884677
theorem B2170967 : Blo 2169435 2170967 := bstep (se 1 (by rfl) ⟨1628225, by rfl⟩ : syracuseStep 2170967 = 3256451) B3256451
theorem B5868245 : Blo 2169435 5868245 := bbase (se 7 (by rfl) ⟨68768, by rfl⟩ : syracuseStep 5868245 = 137537) (by norm_num)
theorem B15648653 : Blo 2169435 15648653 := bstep (se 3 (by rfl) ⟨2934122, by rfl⟩ : syracuseStep 15648653 = 5868245) B5868245
theorem B10432435 : Blo 2169435 10432435 := bstep (se 1 (by rfl) ⟨7824326, by rfl⟩ : syracuseStep 10432435 = 15648653) B15648653
theorem B13909913 : Blo 2169435 13909913 := bstep (se 2 (by rfl) ⟨5216217, by rfl⟩ : syracuseStep 13909913 = 10432435) B10432435
theorem B9273275 : Blo 2169435 9273275 := bstep (se 1 (by rfl) ⟨6954956, by rfl⟩ : syracuseStep 9273275 = 13909913) B13909913
theorem B6182183 : Blo 2169435 6182183 := bstep (se 1 (by rfl) ⟨4636637, by rfl⟩ : syracuseStep 6182183 = 9273275) B9273275
theorem B4121455 : Blo 2169435 4121455 := bstep (se 1 (by rfl) ⟨3091091, by rfl⟩ : syracuseStep 4121455 = 6182183) B6182183
theorem B5495273 : Blo 2169435 5495273 := bstep (se 2 (by rfl) ⟨2060727, by rfl⟩ : syracuseStep 5495273 = 4121455) B4121455
theorem B3663515 : Blo 2169435 3663515 := bstep (se 1 (by rfl) ⟨2747636, by rfl⟩ : syracuseStep 3663515 = 5495273) B5495273
theorem B2442343 : Blo 2169435 2442343 := bstep (se 1 (by rfl) ⟨1831757, by rfl⟩ : syracuseStep 2442343 = 3663515) B3663515
theorem B3256457 : Blo 2169435 3256457 := bstep (se 2 (by rfl) ⟨1221171, by rfl⟩ : syracuseStep 3256457 = 2442343) B2442343
theorem B2170971 : Blo 2169435 2170971 := bstep (se 1 (by rfl) ⟨1628228, by rfl⟩ : syracuseStep 2170971 = 3256457) B3256457
theorem B10990565 : Blo 2169435 10990565 := bbase (se 4 (by rfl) ⟨1030365, by rfl⟩ : syracuseStep 10990565 = 2060731) (by norm_num)
theorem B7327043 : Blo 2169435 7327043 := bstep (se 1 (by rfl) ⟨5495282, by rfl⟩ : syracuseStep 7327043 = 10990565) B10990565
theorem B4884695 : Blo 2169435 4884695 := bstep (se 1 (by rfl) ⟨3663521, by rfl⟩ : syracuseStep 4884695 = 7327043) B7327043
theorem B3256463 : Blo 2169435 3256463 := bstep (se 1 (by rfl) ⟨2442347, by rfl⟩ : syracuseStep 3256463 = 4884695) B4884695
theorem B2170975 : Blo 2169435 2170975 := bstep (se 1 (by rfl) ⟨1628231, by rfl⟩ : syracuseStep 2170975 = 3256463) B3256463
theorem B3256469 : Blo 2169435 3256469 := bbase (se 6 (by rfl) ⟨76323, by rfl⟩ : syracuseStep 3256469 = 152647) (by norm_num)
theorem B2170979 : Blo 2169435 2170979 := bstep (se 1 (by rfl) ⟨1628234, by rfl⟩ : syracuseStep 2170979 = 3256469) B3256469
theorem B2785141 : Blo 2169435 2785141 := bbase (se 5 (by rfl) ⟨130553, by rfl⟩ : syracuseStep 2785141 = 261107) (by norm_num)
theorem B3713521 : Blo 2169435 3713521 := bstep (se 2 (by rfl) ⟨1392570, by rfl⟩ : syracuseStep 3713521 = 2785141) B2785141
theorem B4951361 : Blo 2169435 4951361 := bstep (se 2 (by rfl) ⟨1856760, by rfl⟩ : syracuseStep 4951361 = 3713521) B3713521
theorem B3300907 : Blo 2169435 3300907 := bstep (se 1 (by rfl) ⟨2475680, by rfl⟩ : syracuseStep 3300907 = 4951361) B4951361
theorem B4401209 : Blo 2169435 4401209 := bstep (se 2 (by rfl) ⟨1650453, by rfl⟩ : syracuseStep 4401209 = 3300907) B3300907
theorem B2934139 : Blo 2169435 2934139 := bstep (se 1 (by rfl) ⟨2200604, by rfl⟩ : syracuseStep 2934139 = 4401209) B4401209
theorem B3912185 : Blo 2169435 3912185 := bstep (se 2 (by rfl) ⟨1467069, by rfl⟩ : syracuseStep 3912185 = 2934139) B2934139
theorem B2608123 : Blo 2169435 2608123 := bstep (se 1 (by rfl) ⟨1956092, by rfl⟩ : syracuseStep 2608123 = 3912185) B3912185
theorem B3477497 : Blo 2169435 3477497 := bstep (se 2 (by rfl) ⟨1304061, by rfl⟩ : syracuseStep 3477497 = 2608123) B2608123
theorem B9273325 : Blo 2169435 9273325 := bstep (se 3 (by rfl) ⟨1738748, by rfl⟩ : syracuseStep 9273325 = 3477497) B3477497
theorem B12364433 : Blo 2169435 12364433 := bstep (se 2 (by rfl) ⟨4636662, by rfl⟩ : syracuseStep 12364433 = 9273325) B9273325
theorem B8242955 : Blo 2169435 8242955 := bstep (se 1 (by rfl) ⟨6182216, by rfl⟩ : syracuseStep 8242955 = 12364433) B12364433
theorem B5495303 : Blo 2169435 5495303 := bstep (se 1 (by rfl) ⟨4121477, by rfl⟩ : syracuseStep 5495303 = 8242955) B8242955
theorem B3663535 : Blo 2169435 3663535 := bstep (se 1 (by rfl) ⟨2747651, by rfl⟩ : syracuseStep 3663535 = 5495303) B5495303
theorem B4884713 : Blo 2169435 4884713 := bstep (se 2 (by rfl) ⟨1831767, by rfl⟩ : syracuseStep 4884713 = 3663535) B3663535
theorem B3256475 : Blo 2169435 3256475 := bstep (se 1 (by rfl) ⟨2442356, by rfl⟩ : syracuseStep 3256475 = 4884713) B4884713
theorem B2170983 : Blo 2169435 2170983 := bstep (se 1 (by rfl) ⟨1628237, by rfl⟩ : syracuseStep 2170983 = 3256475) B3256475
theorem B2442361 : Blo 2169435 2442361 := bbase (se 2 (by rfl) ⟨915885, by rfl⟩ : syracuseStep 2442361 = 1831771) (by norm_num)
theorem B3256481 : Blo 2169435 3256481 := bstep (se 2 (by rfl) ⟨1221180, by rfl⟩ : syracuseStep 3256481 = 2442361) B2442361
theorem B2170987 : Blo 2169435 2170987 := bstep (se 1 (by rfl) ⟨1628240, by rfl⟩ : syracuseStep 2170987 = 3256481) B3256481
theorem B2934149 : Blo 2169435 2934149 := bbase (se 4 (by rfl) ⟨275076, by rfl⟩ : syracuseStep 2934149 = 550153) (by norm_num)
theorem B31297589 : Blo 2169435 31297589 := bstep (se 5 (by rfl) ⟨1467074, by rfl⟩ : syracuseStep 31297589 = 2934149) B2934149
theorem B20865059 : Blo 2169435 20865059 := bstep (se 1 (by rfl) ⟨15648794, by rfl⟩ : syracuseStep 20865059 = 31297589) B31297589
theorem B13910039 : Blo 2169435 13910039 := bstep (se 1 (by rfl) ⟨10432529, by rfl⟩ : syracuseStep 13910039 = 20865059) B20865059
theorem B9273359 : Blo 2169435 9273359 := bstep (se 1 (by rfl) ⟨6955019, by rfl⟩ : syracuseStep 9273359 = 13910039) B13910039
theorem B6182239 : Blo 2169435 6182239 := bstep (se 1 (by rfl) ⟨4636679, by rfl⟩ : syracuseStep 6182239 = 9273359) B9273359
theorem B8242985 : Blo 2169435 8242985 := bstep (se 2 (by rfl) ⟨3091119, by rfl⟩ : syracuseStep 8242985 = 6182239) B6182239
theorem B5495323 : Blo 2169435 5495323 := bstep (se 1 (by rfl) ⟨4121492, by rfl⟩ : syracuseStep 5495323 = 8242985) B8242985
theorem B7327097 : Blo 2169435 7327097 := bstep (se 2 (by rfl) ⟨2747661, by rfl⟩ : syracuseStep 7327097 = 5495323) B5495323
theorem B4884731 : Blo 2169435 4884731 := bstep (se 1 (by rfl) ⟨3663548, by rfl⟩ : syracuseStep 4884731 = 7327097) B7327097
theorem B3256487 : Blo 2169435 3256487 := bstep (se 1 (by rfl) ⟨2442365, by rfl⟩ : syracuseStep 3256487 = 4884731) B4884731
theorem B2170991 : Blo 2169435 2170991 := bstep (se 1 (by rfl) ⟨1628243, by rfl⟩ : syracuseStep 2170991 = 3256487) B3256487
theorem B3256493 : Blo 2169435 3256493 := bbase (se 3 (by rfl) ⟨610592, by rfl⟩ : syracuseStep 3256493 = 1221185) (by norm_num)
theorem B2170995 : Blo 2169435 2170995 := bstep (se 1 (by rfl) ⟨1628246, by rfl⟩ : syracuseStep 2170995 = 3256493) B3256493
theorem B4884749 : Blo 2169435 4884749 := bbase (se 3 (by rfl) ⟨915890, by rfl⟩ : syracuseStep 4884749 = 1831781) (by norm_num)
theorem B3256499 : Blo 2169435 3256499 := bstep (se 1 (by rfl) ⟨2442374, by rfl⟩ : syracuseStep 3256499 = 4884749) B4884749
theorem B2170999 : Blo 2169435 2170999 := bstep (se 1 (by rfl) ⟨1628249, by rfl⟩ : syracuseStep 2170999 = 3256499) B3256499
theorem B2747677 : Blo 2169435 2747677 := bbase (se 3 (by rfl) ⟨515189, by rfl⟩ : syracuseStep 2747677 = 1030379) (by norm_num)
theorem B3663569 : Blo 2169435 3663569 := bstep (se 2 (by rfl) ⟨1373838, by rfl⟩ : syracuseStep 3663569 = 2747677) B2747677
theorem B2442379 : Blo 2169435 2442379 := bstep (se 1 (by rfl) ⟨1831784, by rfl⟩ : syracuseStep 2442379 = 3663569) B3663569
theorem B3256505 : Blo 2169435 3256505 := bstep (se 2 (by rfl) ⟨1221189, by rfl⟩ : syracuseStep 3256505 = 2442379) B2442379
theorem B2171003 : Blo 2169435 2171003 := bstep (se 1 (by rfl) ⟨1628252, by rfl⟩ : syracuseStep 2171003 = 3256505) B3256505
theorem B5646341 : Blo 2169435 5646341 := bbase (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) (by norm_num)
theorem B3764227 : Blo 2169435 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B5018969 : Blo 2169435 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B13383917 : Blo 2169435 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B8922611 : Blo 2169435 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B5948407 : Blo 2169435 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B7931209 : Blo 2169435 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B10574945 : Blo 2169435 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B7049963 : Blo 2169435 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B18799901 : Blo 2169435 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B12533267 : Blo 2169435 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B8355511 : Blo 2169435 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B11140681 : Blo 2169435 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B14854241 : Blo 2169435 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B9902827 : Blo 2169435 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B13203769 : Blo 2169435 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B17605025 : Blo 2169435 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B11736683 : Blo 2169435 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B7824455 : Blo 2169435 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B5216303 : Blo 2169435 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B3477535 : Blo 2169435 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B18546853 : Blo 2169435 18546853 := bstep (se 4 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 18546853 = 3477535) B3477535
theorem B24729137 : Blo 2169435 24729137 := bstep (se 2 (by rfl) ⟨9273426, by rfl⟩ : syracuseStep 24729137 = 18546853) B18546853
theorem B16486091 : Blo 2169435 16486091 := bstep (se 1 (by rfl) ⟨12364568, by rfl⟩ : syracuseStep 16486091 = 24729137) B24729137
theorem B10990727 : Blo 2169435 10990727 := bstep (se 1 (by rfl) ⟨8243045, by rfl⟩ : syracuseStep 10990727 = 16486091) B16486091
theorem B7327151 : Blo 2169435 7327151 := bstep (se 1 (by rfl) ⟨5495363, by rfl⟩ : syracuseStep 7327151 = 10990727) B10990727
theorem B4884767 : Blo 2169435 4884767 := bstep (se 1 (by rfl) ⟨3663575, by rfl⟩ : syracuseStep 4884767 = 7327151) B7327151
theorem B3256511 : Blo 2169435 3256511 := bstep (se 1 (by rfl) ⟨2442383, by rfl⟩ : syracuseStep 3256511 = 4884767) B4884767
theorem B2171007 : Blo 2169435 2171007 := bstep (se 1 (by rfl) ⟨1628255, by rfl⟩ : syracuseStep 2171007 = 3256511) B3256511
theorem B3256517 : Blo 2169435 3256517 := bbase (se 4 (by rfl) ⟨305298, by rfl⟩ : syracuseStep 3256517 = 610597) (by norm_num)
theorem B2171011 : Blo 2169435 2171011 := bstep (se 1 (by rfl) ⟨1628258, by rfl⟩ : syracuseStep 2171011 = 3256517) B3256517
theorem B3663589 : Blo 2169435 3663589 := bbase (se 4 (by rfl) ⟨343461, by rfl⟩ : syracuseStep 3663589 = 686923) (by norm_num)
theorem B4884785 : Blo 2169435 4884785 := bstep (se 2 (by rfl) ⟨1831794, by rfl⟩ : syracuseStep 4884785 = 3663589) B3663589
theorem B3256523 : Blo 2169435 3256523 := bstep (se 1 (by rfl) ⟨2442392, by rfl⟩ : syracuseStep 3256523 = 4884785) B4884785
theorem B2171015 : Blo 2169435 2171015 := bstep (se 1 (by rfl) ⟨1628261, by rfl⟩ : syracuseStep 2171015 = 3256523) B3256523
theorem B2442397 : Blo 2169435 2442397 := bbase (se 3 (by rfl) ⟨457949, by rfl⟩ : syracuseStep 2442397 = 915899) (by norm_num)
theorem B3256529 : Blo 2169435 3256529 := bstep (se 2 (by rfl) ⟨1221198, by rfl⟩ : syracuseStep 3256529 = 2442397) B2442397
theorem B2171019 : Blo 2169435 2171019 := bstep (se 1 (by rfl) ⟨1628264, by rfl⟩ : syracuseStep 2171019 = 3256529) B3256529
theorem B7327205 : Blo 2169435 7327205 := bbase (se 4 (by rfl) ⟨686925, by rfl⟩ : syracuseStep 7327205 = 1373851) (by norm_num)
theorem B4884803 : Blo 2169435 4884803 := bstep (se 1 (by rfl) ⟨3663602, by rfl⟩ : syracuseStep 4884803 = 7327205) B7327205
theorem B3256535 : Blo 2169435 3256535 := bstep (se 1 (by rfl) ⟨2442401, by rfl⟩ : syracuseStep 3256535 = 4884803) B4884803
theorem B2171023 : Blo 2169435 2171023 := bstep (se 1 (by rfl) ⟨1628267, by rfl⟩ : syracuseStep 2171023 = 3256535) B3256535
theorem B3256541 : Blo 2169435 3256541 := bbase (se 3 (by rfl) ⟨610601, by rfl⟩ : syracuseStep 3256541 = 1221203) (by norm_num)
theorem B2171027 : Blo 2169435 2171027 := bstep (se 1 (by rfl) ⟨1628270, by rfl⟩ : syracuseStep 2171027 = 3256541) B3256541
theorem B4884821 : Blo 2169435 4884821 := bbase (se 10 (by rfl) ⟨7155, by rfl⟩ : syracuseStep 4884821 = 14311) (by norm_num)
theorem B3256547 : Blo 2169435 3256547 := bstep (se 1 (by rfl) ⟨2442410, by rfl⟩ : syracuseStep 3256547 = 4884821) B4884821
theorem B2171031 : Blo 2169435 2171031 := bstep (se 1 (by rfl) ⟨1628273, by rfl⟩ : syracuseStep 2171031 = 3256547) B3256547
theorem B3477581 : Blo 2169435 3477581 := bbase (se 3 (by rfl) ⟨652046, by rfl⟩ : syracuseStep 3477581 = 1304093) (by norm_num)
theorem B2318387 : Blo 2169435 2318387 := bstep (se 1 (by rfl) ⟨1738790, by rfl⟩ : syracuseStep 2318387 = 3477581) B3477581
theorem B6182365 : Blo 2169435 6182365 := bstep (se 3 (by rfl) ⟨1159193, by rfl⟩ : syracuseStep 6182365 = 2318387) B2318387
theorem B8243153 : Blo 2169435 8243153 := bstep (se 2 (by rfl) ⟨3091182, by rfl⟩ : syracuseStep 8243153 = 6182365) B6182365
theorem B5495435 : Blo 2169435 5495435 := bstep (se 1 (by rfl) ⟨4121576, by rfl⟩ : syracuseStep 5495435 = 8243153) B8243153
theorem B3663623 : Blo 2169435 3663623 := bstep (se 1 (by rfl) ⟨2747717, by rfl⟩ : syracuseStep 3663623 = 5495435) B5495435
theorem B2442415 : Blo 2169435 2442415 := bstep (se 1 (by rfl) ⟨1831811, by rfl⟩ : syracuseStep 2442415 = 3663623) B3663623
theorem B3256553 : Blo 2169435 3256553 := bstep (se 2 (by rfl) ⟨1221207, by rfl⟩ : syracuseStep 3256553 = 2442415) B2442415
theorem B2171035 : Blo 2169435 2171035 := bstep (se 1 (by rfl) ⟨1628276, by rfl⟩ : syracuseStep 2171035 = 3256553) B3256553
theorem B4700045 : Blo 2169435 4700045 := bbase (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) (by norm_num)
theorem B12533453 : Blo 2169435 12533453 := bstep (se 3 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 12533453 = 4700045) B4700045
theorem B8355635 : Blo 2169435 8355635 := bstep (se 1 (by rfl) ⟨6266726, by rfl⟩ : syracuseStep 8355635 = 12533453) B12533453
theorem B5570423 : Blo 2169435 5570423 := bstep (se 1 (by rfl) ⟨4177817, by rfl⟩ : syracuseStep 5570423 = 8355635) B8355635
theorem B3713615 : Blo 2169435 3713615 := bstep (se 1 (by rfl) ⟨2785211, by rfl⟩ : syracuseStep 3713615 = 5570423) B5570423
theorem B2475743 : Blo 2169435 2475743 := bstep (se 1 (by rfl) ⟨1856807, by rfl⟩ : syracuseStep 2475743 = 3713615) B3713615
theorem B6601981 : Blo 2169435 6601981 := bstep (se 3 (by rfl) ⟨1237871, by rfl⟩ : syracuseStep 6601981 = 2475743) B2475743
theorem B8802641 : Blo 2169435 8802641 := bstep (se 2 (by rfl) ⟨3300990, by rfl⟩ : syracuseStep 8802641 = 6601981) B6601981
theorem B23473709 : Blo 2169435 23473709 := bstep (se 3 (by rfl) ⟨4401320, by rfl⟩ : syracuseStep 23473709 = 8802641) B8802641
theorem B15649139 : Blo 2169435 15649139 := bstep (se 1 (by rfl) ⟨11736854, by rfl⟩ : syracuseStep 15649139 = 23473709) B23473709
theorem B41731037 : Blo 2169435 41731037 := bstep (se 3 (by rfl) ⟨7824569, by rfl⟩ : syracuseStep 41731037 = 15649139) B15649139
theorem B27820691 : Blo 2169435 27820691 := bstep (se 1 (by rfl) ⟨20865518, by rfl⟩ : syracuseStep 27820691 = 41731037) B41731037
theorem B18547127 : Blo 2169435 18547127 := bstep (se 1 (by rfl) ⟨13910345, by rfl⟩ : syracuseStep 18547127 = 27820691) B27820691
theorem B12364751 : Blo 2169435 12364751 := bstep (se 1 (by rfl) ⟨9273563, by rfl⟩ : syracuseStep 12364751 = 18547127) B18547127
theorem B8243167 : Blo 2169435 8243167 := bstep (se 1 (by rfl) ⟨6182375, by rfl⟩ : syracuseStep 8243167 = 12364751) B12364751
theorem B10990889 : Blo 2169435 10990889 := bstep (se 2 (by rfl) ⟨4121583, by rfl⟩ : syracuseStep 10990889 = 8243167) B8243167
theorem B7327259 : Blo 2169435 7327259 := bstep (se 1 (by rfl) ⟨5495444, by rfl⟩ : syracuseStep 7327259 = 10990889) B10990889
theorem B4884839 : Blo 2169435 4884839 := bstep (se 1 (by rfl) ⟨3663629, by rfl⟩ : syracuseStep 4884839 = 7327259) B7327259
theorem B3256559 : Blo 2169435 3256559 := bstep (se 1 (by rfl) ⟨2442419, by rfl⟩ : syracuseStep 3256559 = 4884839) B4884839
theorem B2171039 : Blo 2169435 2171039 := bstep (se 1 (by rfl) ⟨1628279, by rfl⟩ : syracuseStep 2171039 = 3256559) B3256559
theorem B3256565 : Blo 2169435 3256565 := bbase (se 5 (by rfl) ⟨152651, by rfl⟩ : syracuseStep 3256565 = 305303) (by norm_num)
theorem B2171043 : Blo 2169435 2171043 := bstep (se 1 (by rfl) ⟨1628282, by rfl⟩ : syracuseStep 2171043 = 3256565) B3256565
theorem B4461389 : Blo 2169435 4461389 := bbase (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) (by norm_num)
theorem B2974259 : Blo 2169435 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B7931357 : Blo 2169435 7931357 := bstep (se 3 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 7931357 = 2974259) B2974259
theorem B5287571 : Blo 2169435 5287571 := bstep (se 1 (by rfl) ⟨3965678, by rfl⟩ : syracuseStep 5287571 = 7931357) B7931357
theorem B3525047 : Blo 2169435 3525047 := bstep (se 1 (by rfl) ⟨2643785, by rfl⟩ : syracuseStep 3525047 = 5287571) B5287571
theorem B2350031 : Blo 2169435 2350031 := bstep (se 1 (by rfl) ⟨1762523, by rfl⟩ : syracuseStep 2350031 = 3525047) B3525047
theorem B6266749 : Blo 2169435 6266749 := bstep (se 3 (by rfl) ⟨1175015, by rfl⟩ : syracuseStep 6266749 = 2350031) B2350031
theorem B8355665 : Blo 2169435 8355665 := bstep (se 2 (by rfl) ⟨3133374, by rfl⟩ : syracuseStep 8355665 = 6266749) B6266749
theorem B5570443 : Blo 2169435 5570443 := bstep (se 1 (by rfl) ⟨4177832, by rfl⟩ : syracuseStep 5570443 = 8355665) B8355665
theorem B7427257 : Blo 2169435 7427257 := bstep (se 2 (by rfl) ⟨2785221, by rfl⟩ : syracuseStep 7427257 = 5570443) B5570443
theorem B158448149 : Blo 2169435 158448149 := bstep (se 6 (by rfl) ⟨3713628, by rfl⟩ : syracuseStep 158448149 = 7427257) B7427257
theorem B105632099 : Blo 2169435 105632099 := bstep (se 1 (by rfl) ⟨79224074, by rfl⟩ : syracuseStep 105632099 = 158448149) B158448149
theorem B70421399 : Blo 2169435 70421399 := bstep (se 1 (by rfl) ⟨52816049, by rfl⟩ : syracuseStep 70421399 = 105632099) B105632099
theorem B46947599 : Blo 2169435 46947599 := bstep (se 1 (by rfl) ⟨35210699, by rfl⟩ : syracuseStep 46947599 = 70421399) B70421399
theorem B31298399 : Blo 2169435 31298399 := bstep (se 1 (by rfl) ⟨23473799, by rfl⟩ : syracuseStep 31298399 = 46947599) B46947599
theorem B20865599 : Blo 2169435 20865599 := bstep (se 1 (by rfl) ⟨15649199, by rfl⟩ : syracuseStep 20865599 = 31298399) B31298399
theorem B13910399 : Blo 2169435 13910399 := bstep (se 1 (by rfl) ⟨10432799, by rfl⟩ : syracuseStep 13910399 = 20865599) B20865599
theorem B9273599 : Blo 2169435 9273599 := bstep (se 1 (by rfl) ⟨6955199, by rfl⟩ : syracuseStep 9273599 = 13910399) B13910399
theorem B6182399 : Blo 2169435 6182399 := bstep (se 1 (by rfl) ⟨4636799, by rfl⟩ : syracuseStep 6182399 = 9273599) B9273599
theorem B4121599 : Blo 2169435 4121599 := bstep (se 1 (by rfl) ⟨3091199, by rfl⟩ : syracuseStep 4121599 = 6182399) B6182399
theorem B5495465 : Blo 2169435 5495465 := bstep (se 2 (by rfl) ⟨2060799, by rfl⟩ : syracuseStep 5495465 = 4121599) B4121599
theorem B3663643 : Blo 2169435 3663643 := bstep (se 1 (by rfl) ⟨2747732, by rfl⟩ : syracuseStep 3663643 = 5495465) B5495465
theorem B4884857 : Blo 2169435 4884857 := bstep (se 2 (by rfl) ⟨1831821, by rfl⟩ : syracuseStep 4884857 = 3663643) B3663643
theorem B3256571 : Blo 2169435 3256571 := bstep (se 1 (by rfl) ⟨2442428, by rfl⟩ : syracuseStep 3256571 = 4884857) B4884857
theorem B2171047 : Blo 2169435 2171047 := bstep (se 1 (by rfl) ⟨1628285, by rfl⟩ : syracuseStep 2171047 = 3256571) B3256571
theorem B2442433 : Blo 2169435 2442433 := bbase (se 2 (by rfl) ⟨915912, by rfl⟩ : syracuseStep 2442433 = 1831825) (by norm_num)
theorem B3256577 : Blo 2169435 3256577 := bstep (se 2 (by rfl) ⟨1221216, by rfl⟩ : syracuseStep 3256577 = 2442433) B2442433
theorem B2171051 : Blo 2169435 2171051 := bstep (se 1 (by rfl) ⟨1628288, by rfl⟩ : syracuseStep 2171051 = 3256577) B3256577
theorem B5495485 : Blo 2169435 5495485 := bbase (se 3 (by rfl) ⟨1030403, by rfl⟩ : syracuseStep 5495485 = 2060807) (by norm_num)
theorem B7327313 : Blo 2169435 7327313 := bstep (se 2 (by rfl) ⟨2747742, by rfl⟩ : syracuseStep 7327313 = 5495485) B5495485
theorem B4884875 : Blo 2169435 4884875 := bstep (se 1 (by rfl) ⟨3663656, by rfl⟩ : syracuseStep 4884875 = 7327313) B7327313
theorem B3256583 : Blo 2169435 3256583 := bstep (se 1 (by rfl) ⟨2442437, by rfl⟩ : syracuseStep 3256583 = 4884875) B4884875
theorem B2171055 : Blo 2169435 2171055 := bstep (se 1 (by rfl) ⟨1628291, by rfl⟩ : syracuseStep 2171055 = 3256583) B3256583
theorem B3256589 : Blo 2169435 3256589 := bbase (se 3 (by rfl) ⟨610610, by rfl⟩ : syracuseStep 3256589 = 1221221) (by norm_num)
theorem B2171059 : Blo 2169435 2171059 := bstep (se 1 (by rfl) ⟨1628294, by rfl⟩ : syracuseStep 2171059 = 3256589) B3256589
theorem B4884893 : Blo 2169435 4884893 := bbase (se 3 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 4884893 = 1831835) (by norm_num)
theorem B3256595 : Blo 2169435 3256595 := bstep (se 1 (by rfl) ⟨2442446, by rfl⟩ : syracuseStep 3256595 = 4884893) B4884893
theorem B2171063 : Blo 2169435 2171063 := bstep (se 1 (by rfl) ⟨1628297, by rfl⟩ : syracuseStep 2171063 = 3256595) B3256595
theorem B3663677 : Blo 2169435 3663677 := bbase (se 3 (by rfl) ⟨686939, by rfl⟩ : syracuseStep 3663677 = 1373879) (by norm_num)
theorem B2442451 : Blo 2169435 2442451 := bstep (se 1 (by rfl) ⟨1831838, by rfl⟩ : syracuseStep 2442451 = 3663677) B3663677
theorem B3256601 : Blo 2169435 3256601 := bstep (se 2 (by rfl) ⟨1221225, by rfl⟩ : syracuseStep 3256601 = 2442451) B2442451
theorem B2171067 : Blo 2169435 2171067 := bstep (se 1 (by rfl) ⟨1628300, by rfl⟩ : syracuseStep 2171067 = 3256601) B3256601
theorem B2318425 : Blo 2169435 2318425 := bbase (se 2 (by rfl) ⟨869409, by rfl⟩ : syracuseStep 2318425 = 1738819) (by norm_num)
theorem B12364933 : Blo 2169435 12364933 := bstep (se 4 (by rfl) ⟨1159212, by rfl⟩ : syracuseStep 12364933 = 2318425) B2318425
theorem B16486577 : Blo 2169435 16486577 := bstep (se 2 (by rfl) ⟨6182466, by rfl⟩ : syracuseStep 16486577 = 12364933) B12364933
theorem B10991051 : Blo 2169435 10991051 := bstep (se 1 (by rfl) ⟨8243288, by rfl⟩ : syracuseStep 10991051 = 16486577) B16486577
theorem B7327367 : Blo 2169435 7327367 := bstep (se 1 (by rfl) ⟨5495525, by rfl⟩ : syracuseStep 7327367 = 10991051) B10991051
theorem B4884911 : Blo 2169435 4884911 := bstep (se 1 (by rfl) ⟨3663683, by rfl⟩ : syracuseStep 4884911 = 7327367) B7327367
theorem B3256607 : Blo 2169435 3256607 := bstep (se 1 (by rfl) ⟨2442455, by rfl⟩ : syracuseStep 3256607 = 4884911) B4884911
theorem B2171071 : Blo 2169435 2171071 := bstep (se 1 (by rfl) ⟨1628303, by rfl⟩ : syracuseStep 2171071 = 3256607) B3256607
theorem B3256613 : Blo 2169435 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B2171075 : Blo 2169435 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B2747773 : Blo 2169435 2747773 := bbase (se 3 (by rfl) ⟨515207, by rfl⟩ : syracuseStep 2747773 = 1030415) (by norm_num)
theorem B3663697 : Blo 2169435 3663697 := bstep (se 2 (by rfl) ⟨1373886, by rfl⟩ : syracuseStep 3663697 = 2747773) B2747773
theorem B4884929 : Blo 2169435 4884929 := bstep (se 2 (by rfl) ⟨1831848, by rfl⟩ : syracuseStep 4884929 = 3663697) B3663697
theorem B3256619 : Blo 2169435 3256619 := bstep (se 1 (by rfl) ⟨2442464, by rfl⟩ : syracuseStep 3256619 = 4884929) B4884929
theorem B2171079 : Blo 2169435 2171079 := bstep (se 1 (by rfl) ⟨1628309, by rfl⟩ : syracuseStep 2171079 = 3256619) B3256619
theorem B2442469 : Blo 2169435 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B3256625 : Blo 2169435 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B2171083 : Blo 2169435 2171083 := bstep (se 1 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 2171083 = 3256625) B3256625
theorem B4636885 : Blo 2169435 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B6182513 : Blo 2169435 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B4121675 : Blo 2169435 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B2747783 : Blo 2169435 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B7327421 : Blo 2169435 7327421 := bstep (se 3 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 7327421 = 2747783) B2747783
theorem B4884947 : Blo 2169435 4884947 := bstep (se 1 (by rfl) ⟨3663710, by rfl⟩ : syracuseStep 4884947 = 7327421) B7327421
theorem B3256631 : Blo 2169435 3256631 := bstep (se 1 (by rfl) ⟨2442473, by rfl⟩ : syracuseStep 3256631 = 4884947) B4884947
theorem B2171087 : Blo 2169435 2171087 := bstep (se 1 (by rfl) ⟨1628315, by rfl⟩ : syracuseStep 2171087 = 3256631) B3256631
theorem B3256637 : Blo 2169435 3256637 := bbase (se 3 (by rfl) ⟨610619, by rfl⟩ : syracuseStep 3256637 = 1221239) (by norm_num)
theorem B2171091 : Blo 2169435 2171091 := bstep (se 1 (by rfl) ⟨1628318, by rfl⟩ : syracuseStep 2171091 = 3256637) B3256637
theorem B4884965 : Blo 2169435 4884965 := bbase (se 4 (by rfl) ⟨457965, by rfl⟩ : syracuseStep 4884965 = 915931) (by norm_num)
theorem B3256643 : Blo 2169435 3256643 := bstep (se 1 (by rfl) ⟨2442482, by rfl⟩ : syracuseStep 3256643 = 4884965) B4884965
theorem B2171095 : Blo 2169435 2171095 := bstep (se 1 (by rfl) ⟨1628321, by rfl⟩ : syracuseStep 2171095 = 3256643) B3256643
theorem B5495597 : Blo 2169435 5495597 := bbase (se 3 (by rfl) ⟨1030424, by rfl⟩ : syracuseStep 5495597 = 2060849) (by norm_num)
theorem B3663731 : Blo 2169435 3663731 := bstep (se 1 (by rfl) ⟨2747798, by rfl⟩ : syracuseStep 3663731 = 5495597) B5495597
theorem B2442487 : Blo 2169435 2442487 := bstep (se 1 (by rfl) ⟨1831865, by rfl⟩ : syracuseStep 2442487 = 3663731) B3663731
theorem B3256649 : Blo 2169435 3256649 := bstep (se 2 (by rfl) ⟨1221243, by rfl⟩ : syracuseStep 3256649 = 2442487) B2442487
theorem B2171099 : Blo 2169435 2171099 := bstep (se 1 (by rfl) ⟨1628324, by rfl⟩ : syracuseStep 2171099 = 3256649) B3256649
theorem B2934301 : Blo 2169435 2934301 := bbase (se 3 (by rfl) ⟨550181, by rfl⟩ : syracuseStep 2934301 = 1100363) (by norm_num)
theorem B3912401 : Blo 2169435 3912401 := bstep (se 2 (by rfl) ⟨1467150, by rfl⟩ : syracuseStep 3912401 = 2934301) B2934301
theorem B10433069 : Blo 2169435 10433069 := bstep (se 3 (by rfl) ⟨1956200, by rfl⟩ : syracuseStep 10433069 = 3912401) B3912401
theorem B6955379 : Blo 2169435 6955379 := bstep (se 1 (by rfl) ⟨5216534, by rfl⟩ : syracuseStep 6955379 = 10433069) B10433069
theorem B4636919 : Blo 2169435 4636919 := bstep (se 1 (by rfl) ⟨3477689, by rfl⟩ : syracuseStep 4636919 = 6955379) B6955379
theorem B3091279 : Blo 2169435 3091279 := bstep (se 1 (by rfl) ⟨2318459, by rfl⟩ : syracuseStep 3091279 = 4636919) B4636919
theorem B4121705 : Blo 2169435 4121705 := bstep (se 2 (by rfl) ⟨1545639, by rfl⟩ : syracuseStep 4121705 = 3091279) B3091279
theorem B10991213 : Blo 2169435 10991213 := bstep (se 3 (by rfl) ⟨2060852, by rfl⟩ : syracuseStep 10991213 = 4121705) B4121705
theorem B7327475 : Blo 2169435 7327475 := bstep (se 1 (by rfl) ⟨5495606, by rfl⟩ : syracuseStep 7327475 = 10991213) B10991213
theorem B4884983 : Blo 2169435 4884983 := bstep (se 1 (by rfl) ⟨3663737, by rfl⟩ : syracuseStep 4884983 = 7327475) B7327475
theorem B3256655 : Blo 2169435 3256655 := bstep (se 1 (by rfl) ⟨2442491, by rfl⟩ : syracuseStep 3256655 = 4884983) B4884983
theorem B2171103 : Blo 2169435 2171103 := bstep (se 1 (by rfl) ⟨1628327, by rfl⟩ : syracuseStep 2171103 = 3256655) B3256655
theorem B3256661 : Blo 2169435 3256661 := bbase (se 10 (by rfl) ⟨4770, by rfl⟩ : syracuseStep 3256661 = 9541) (by norm_num)
theorem B2171107 : Blo 2169435 2171107 := bstep (se 1 (by rfl) ⟨1628330, by rfl⟩ : syracuseStep 2171107 = 3256661) B3256661
theorem B6182581 : Blo 2169435 6182581 := bbase (se 5 (by rfl) ⟨289808, by rfl⟩ : syracuseStep 6182581 = 579617) (by norm_num)
theorem B8243441 : Blo 2169435 8243441 := bstep (se 2 (by rfl) ⟨3091290, by rfl⟩ : syracuseStep 8243441 = 6182581) B6182581
theorem B5495627 : Blo 2169435 5495627 := bstep (se 1 (by rfl) ⟨4121720, by rfl⟩ : syracuseStep 5495627 = 8243441) B8243441
theorem B3663751 : Blo 2169435 3663751 := bstep (se 1 (by rfl) ⟨2747813, by rfl⟩ : syracuseStep 3663751 = 5495627) B5495627
theorem B4885001 : Blo 2169435 4885001 := bstep (se 2 (by rfl) ⟨1831875, by rfl⟩ : syracuseStep 4885001 = 3663751) B3663751
theorem B3256667 : Blo 2169435 3256667 := bstep (se 1 (by rfl) ⟨2442500, by rfl⟩ : syracuseStep 3256667 = 4885001) B4885001
theorem B2171111 : Blo 2169435 2171111 := bstep (se 1 (by rfl) ⟨1628333, by rfl⟩ : syracuseStep 2171111 = 3256667) B3256667
theorem B2442505 : Blo 2169435 2442505 := bbase (se 2 (by rfl) ⟨915939, by rfl⟩ : syracuseStep 2442505 = 1831879) (by norm_num)
theorem B3256673 : Blo 2169435 3256673 := bstep (se 2 (by rfl) ⟨1221252, by rfl⟩ : syracuseStep 3256673 = 2442505) B2442505
theorem B2171115 : Blo 2169435 2171115 := bstep (se 1 (by rfl) ⟨1628336, by rfl⟩ : syracuseStep 2171115 = 3256673) B3256673
theorem B27821717 : Blo 2169435 27821717 := bbase (se 6 (by rfl) ⟨652071, by rfl⟩ : syracuseStep 27821717 = 1304143) (by norm_num)
theorem B18547811 : Blo 2169435 18547811 := bstep (se 1 (by rfl) ⟨13910858, by rfl⟩ : syracuseStep 18547811 = 27821717) B27821717
theorem B12365207 : Blo 2169435 12365207 := bstep (se 1 (by rfl) ⟨9273905, by rfl⟩ : syracuseStep 12365207 = 18547811) B18547811
theorem B8243471 : Blo 2169435 8243471 := bstep (se 1 (by rfl) ⟨6182603, by rfl⟩ : syracuseStep 8243471 = 12365207) B12365207
theorem B5495647 : Blo 2169435 5495647 := bstep (se 1 (by rfl) ⟨4121735, by rfl⟩ : syracuseStep 5495647 = 8243471) B8243471
theorem B7327529 : Blo 2169435 7327529 := bstep (se 2 (by rfl) ⟨2747823, by rfl⟩ : syracuseStep 7327529 = 5495647) B5495647
theorem B4885019 : Blo 2169435 4885019 := bstep (se 1 (by rfl) ⟨3663764, by rfl⟩ : syracuseStep 4885019 = 7327529) B7327529
theorem B3256679 : Blo 2169435 3256679 := bstep (se 1 (by rfl) ⟨2442509, by rfl⟩ : syracuseStep 3256679 = 4885019) B4885019
theorem B2171119 : Blo 2169435 2171119 := bstep (se 1 (by rfl) ⟨1628339, by rfl⟩ : syracuseStep 2171119 = 3256679) B3256679
theorem B3256685 : Blo 2169435 3256685 := bbase (se 3 (by rfl) ⟨610628, by rfl⟩ : syracuseStep 3256685 = 1221257) (by norm_num)
theorem B2171123 : Blo 2169435 2171123 := bstep (se 1 (by rfl) ⟨1628342, by rfl⟩ : syracuseStep 2171123 = 3256685) B3256685
theorem B4885037 : Blo 2169435 4885037 := bbase (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) (by norm_num)
theorem B3256691 : Blo 2169435 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B2171127 : Blo 2169435 2171127 := bstep (se 1 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 2171127 = 3256691) B3256691
theorem B3713773 : Blo 2169435 3713773 := bbase (se 3 (by rfl) ⟨696332, by rfl⟩ : syracuseStep 3713773 = 1392665) (by norm_num)
theorem B4951697 : Blo 2169435 4951697 := bstep (se 2 (by rfl) ⟨1856886, by rfl⟩ : syracuseStep 4951697 = 3713773) B3713773
theorem B52818101 : Blo 2169435 52818101 := bstep (se 5 (by rfl) ⟨2475848, by rfl⟩ : syracuseStep 52818101 = 4951697) B4951697
theorem B35212067 : Blo 2169435 35212067 := bstep (se 1 (by rfl) ⟨26409050, by rfl⟩ : syracuseStep 35212067 = 52818101) B52818101
theorem B23474711 : Blo 2169435 23474711 := bstep (se 1 (by rfl) ⟨17606033, by rfl⟩ : syracuseStep 23474711 = 35212067) B35212067
theorem B15649807 : Blo 2169435 15649807 := bstep (se 1 (by rfl) ⟨11737355, by rfl⟩ : syracuseStep 15649807 = 23474711) B23474711
theorem B20866409 : Blo 2169435 20866409 := bstep (se 2 (by rfl) ⟨7824903, by rfl⟩ : syracuseStep 20866409 = 15649807) B15649807
theorem B13910939 : Blo 2169435 13910939 := bstep (se 1 (by rfl) ⟨10433204, by rfl⟩ : syracuseStep 13910939 = 20866409) B20866409
theorem B9273959 : Blo 2169435 9273959 := bstep (se 1 (by rfl) ⟨6955469, by rfl⟩ : syracuseStep 9273959 = 13910939) B13910939
theorem B6182639 : Blo 2169435 6182639 := bstep (se 1 (by rfl) ⟨4636979, by rfl⟩ : syracuseStep 6182639 = 9273959) B9273959
theorem B4121759 : Blo 2169435 4121759 := bstep (se 1 (by rfl) ⟨3091319, by rfl⟩ : syracuseStep 4121759 = 6182639) B6182639
theorem B2747839 : Blo 2169435 2747839 := bstep (se 1 (by rfl) ⟨2060879, by rfl⟩ : syracuseStep 2747839 = 4121759) B4121759
theorem B3663785 : Blo 2169435 3663785 := bstep (se 2 (by rfl) ⟨1373919, by rfl⟩ : syracuseStep 3663785 = 2747839) B2747839
theorem B2442523 : Blo 2169435 2442523 := bstep (se 1 (by rfl) ⟨1831892, by rfl⟩ : syracuseStep 2442523 = 3663785) B3663785
theorem B3256697 : Blo 2169435 3256697 := bstep (se 2 (by rfl) ⟨1221261, by rfl⟩ : syracuseStep 3256697 = 2442523) B2442523
theorem B2171131 : Blo 2169435 2171131 := bstep (se 1 (by rfl) ⟨1628348, by rfl⟩ : syracuseStep 2171131 = 3256697) B3256697
theorem B37095893 : Blo 2169435 37095893 := bbase (se 7 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 37095893 = 869435) (by norm_num)
theorem B24730595 : Blo 2169435 24730595 := bstep (se 1 (by rfl) ⟨18547946, by rfl⟩ : syracuseStep 24730595 = 37095893) B37095893
theorem B16487063 : Blo 2169435 16487063 := bstep (se 1 (by rfl) ⟨12365297, by rfl⟩ : syracuseStep 16487063 = 24730595) B24730595
theorem B10991375 : Blo 2169435 10991375 := bstep (se 1 (by rfl) ⟨8243531, by rfl⟩ : syracuseStep 10991375 = 16487063) B16487063
theorem B7327583 : Blo 2169435 7327583 := bstep (se 1 (by rfl) ⟨5495687, by rfl⟩ : syracuseStep 7327583 = 10991375) B10991375
theorem B4885055 : Blo 2169435 4885055 := bstep (se 1 (by rfl) ⟨3663791, by rfl⟩ : syracuseStep 4885055 = 7327583) B7327583
theorem B3256703 : Blo 2169435 3256703 := bstep (se 1 (by rfl) ⟨2442527, by rfl⟩ : syracuseStep 3256703 = 4885055) B4885055
theorem B2171135 : Blo 2169435 2171135 := bstep (se 1 (by rfl) ⟨1628351, by rfl⟩ : syracuseStep 2171135 = 3256703) B3256703
theorem B3256709 : Blo 2169435 3256709 := bbase (se 4 (by rfl) ⟨305316, by rfl⟩ : syracuseStep 3256709 = 610633) (by norm_num)
theorem B2171139 : Blo 2169435 2171139 := bstep (se 1 (by rfl) ⟨1628354, by rfl⟩ : syracuseStep 2171139 = 3256709) B3256709
theorem B3663805 : Blo 2169435 3663805 := bbase (se 3 (by rfl) ⟨686963, by rfl⟩ : syracuseStep 3663805 = 1373927) (by norm_num)
theorem B4885073 : Blo 2169435 4885073 := bstep (se 2 (by rfl) ⟨1831902, by rfl⟩ : syracuseStep 4885073 = 3663805) B3663805
theorem B3256715 : Blo 2169435 3256715 := bstep (se 1 (by rfl) ⟨2442536, by rfl⟩ : syracuseStep 3256715 = 4885073) B4885073
theorem B2171143 : Blo 2169435 2171143 := bstep (se 1 (by rfl) ⟨1628357, by rfl⟩ : syracuseStep 2171143 = 3256715) B3256715
theorem B2442541 : Blo 2169435 2442541 := bbase (se 3 (by rfl) ⟨457976, by rfl⟩ : syracuseStep 2442541 = 915953) (by norm_num)
theorem B3256721 : Blo 2169435 3256721 := bstep (se 2 (by rfl) ⟨1221270, by rfl⟩ : syracuseStep 3256721 = 2442541) B2442541
theorem B2171147 : Blo 2169435 2171147 := bstep (se 1 (by rfl) ⟨1628360, by rfl⟩ : syracuseStep 2171147 = 3256721) B3256721
theorem B7327637 : Blo 2169435 7327637 := bbase (se 6 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 7327637 = 343483) (by norm_num)
theorem B4885091 : Blo 2169435 4885091 := bstep (se 1 (by rfl) ⟨3663818, by rfl⟩ : syracuseStep 4885091 = 7327637) B7327637
theorem B3256727 : Blo 2169435 3256727 := bstep (se 1 (by rfl) ⟨2442545, by rfl⟩ : syracuseStep 3256727 = 4885091) B4885091
theorem B2171151 : Blo 2169435 2171151 := bstep (se 1 (by rfl) ⟨1628363, by rfl⟩ : syracuseStep 2171151 = 3256727) B3256727
theorem B3256733 : Blo 2169435 3256733 := bbase (se 3 (by rfl) ⟨610637, by rfl⟩ : syracuseStep 3256733 = 1221275) (by norm_num)
theorem B2171155 : Blo 2169435 2171155 := bstep (se 1 (by rfl) ⟨1628366, by rfl⟩ : syracuseStep 2171155 = 3256733) B3256733
theorem B4885109 : Blo 2169435 4885109 := bbase (se 5 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 4885109 = 457979) (by norm_num)
theorem B3256739 : Blo 2169435 3256739 := bstep (se 1 (by rfl) ⟨2442554, by rfl⟩ : syracuseStep 3256739 = 4885109) B4885109
theorem B2171159 : Blo 2169435 2171159 := bstep (se 1 (by rfl) ⟨1628369, by rfl⟩ : syracuseStep 2171159 = 3256739) B3256739
theorem B3912509 : Blo 2169435 3912509 := bbase (se 3 (by rfl) ⟨733595, by rfl⟩ : syracuseStep 3912509 = 1467191) (by norm_num)
theorem B10433357 : Blo 2169435 10433357 := bstep (se 3 (by rfl) ⟨1956254, by rfl⟩ : syracuseStep 10433357 = 3912509) B3912509
theorem B6955571 : Blo 2169435 6955571 := bstep (se 1 (by rfl) ⟨5216678, by rfl⟩ : syracuseStep 6955571 = 10433357) B10433357
theorem B18548189 : Blo 2169435 18548189 := bstep (se 3 (by rfl) ⟨3477785, by rfl⟩ : syracuseStep 18548189 = 6955571) B6955571
theorem B12365459 : Blo 2169435 12365459 := bstep (se 1 (by rfl) ⟨9274094, by rfl⟩ : syracuseStep 12365459 = 18548189) B18548189
theorem B8243639 : Blo 2169435 8243639 := bstep (se 1 (by rfl) ⟨6182729, by rfl⟩ : syracuseStep 8243639 = 12365459) B12365459
theorem B5495759 : Blo 2169435 5495759 := bstep (se 1 (by rfl) ⟨4121819, by rfl⟩ : syracuseStep 5495759 = 8243639) B8243639
theorem B3663839 : Blo 2169435 3663839 := bstep (se 1 (by rfl) ⟨2747879, by rfl⟩ : syracuseStep 3663839 = 5495759) B5495759
theorem B2442559 : Blo 2169435 2442559 := bstep (se 1 (by rfl) ⟨1831919, by rfl⟩ : syracuseStep 2442559 = 3663839) B3663839
theorem B3256745 : Blo 2169435 3256745 := bstep (se 2 (by rfl) ⟨1221279, by rfl⟩ : syracuseStep 3256745 = 2442559) B2442559
theorem B2171163 : Blo 2169435 2171163 := bstep (se 1 (by rfl) ⟨1628372, by rfl⟩ : syracuseStep 2171163 = 3256745) B3256745
theorem B8243653 : Blo 2169435 8243653 := bbase (se 4 (by rfl) ⟨772842, by rfl⟩ : syracuseStep 8243653 = 1545685) (by norm_num)
theorem B10991537 : Blo 2169435 10991537 := bstep (se 2 (by rfl) ⟨4121826, by rfl⟩ : syracuseStep 10991537 = 8243653) B8243653
theorem B7327691 : Blo 2169435 7327691 := bstep (se 1 (by rfl) ⟨5495768, by rfl⟩ : syracuseStep 7327691 = 10991537) B10991537
theorem B4885127 : Blo 2169435 4885127 := bstep (se 1 (by rfl) ⟨3663845, by rfl⟩ : syracuseStep 4885127 = 7327691) B7327691
theorem B3256751 : Blo 2169435 3256751 := bstep (se 1 (by rfl) ⟨2442563, by rfl⟩ : syracuseStep 3256751 = 4885127) B4885127
theorem B2171167 : Blo 2169435 2171167 := bstep (se 1 (by rfl) ⟨1628375, by rfl⟩ : syracuseStep 2171167 = 3256751) B3256751
theorem B3256757 : Blo 2169435 3256757 := bbase (se 5 (by rfl) ⟨152660, by rfl⟩ : syracuseStep 3256757 = 305321) (by norm_num)
theorem B2171171 : Blo 2169435 2171171 := bstep (se 1 (by rfl) ⟨1628378, by rfl⟩ : syracuseStep 2171171 = 3256757) B3256757
theorem B5495789 : Blo 2169435 5495789 := bbase (se 3 (by rfl) ⟨1030460, by rfl⟩ : syracuseStep 5495789 = 2060921) (by norm_num)
theorem B3663859 : Blo 2169435 3663859 := bstep (se 1 (by rfl) ⟨2747894, by rfl⟩ : syracuseStep 3663859 = 5495789) B5495789
theorem B4885145 : Blo 2169435 4885145 := bstep (se 2 (by rfl) ⟨1831929, by rfl⟩ : syracuseStep 4885145 = 3663859) B3663859
theorem B3256763 : Blo 2169435 3256763 := bstep (se 1 (by rfl) ⟨2442572, by rfl⟩ : syracuseStep 3256763 = 4885145) B4885145
theorem B2171175 : Blo 2169435 2171175 := bstep (se 1 (by rfl) ⟨1628381, by rfl⟩ : syracuseStep 2171175 = 3256763) B3256763
theorem B2442577 : Blo 2169435 2442577 := bbase (se 2 (by rfl) ⟨915966, by rfl⟩ : syracuseStep 2442577 = 1831933) (by norm_num)
theorem B3256769 : Blo 2169435 3256769 := bstep (se 2 (by rfl) ⟨1221288, by rfl⟩ : syracuseStep 3256769 = 2442577) B2442577
theorem B2171179 : Blo 2169435 2171179 := bstep (se 1 (by rfl) ⟨1628384, by rfl⟩ : syracuseStep 2171179 = 3256769) B3256769
theorem B2318545 : Blo 2169435 2318545 := bbase (se 2 (by rfl) ⟨869454, by rfl⟩ : syracuseStep 2318545 = 1738909) (by norm_num)
theorem B3091393 : Blo 2169435 3091393 := bstep (se 2 (by rfl) ⟨1159272, by rfl⟩ : syracuseStep 3091393 = 2318545) B2318545
theorem B4121857 : Blo 2169435 4121857 := bstep (se 2 (by rfl) ⟨1545696, by rfl⟩ : syracuseStep 4121857 = 3091393) B3091393
theorem B5495809 : Blo 2169435 5495809 := bstep (se 2 (by rfl) ⟨2060928, by rfl⟩ : syracuseStep 5495809 = 4121857) B4121857
theorem B7327745 : Blo 2169435 7327745 := bstep (se 2 (by rfl) ⟨2747904, by rfl⟩ : syracuseStep 7327745 = 5495809) B5495809
theorem B4885163 : Blo 2169435 4885163 := bstep (se 1 (by rfl) ⟨3663872, by rfl⟩ : syracuseStep 4885163 = 7327745) B7327745
theorem B3256775 : Blo 2169435 3256775 := bstep (se 1 (by rfl) ⟨2442581, by rfl⟩ : syracuseStep 3256775 = 4885163) B4885163
theorem B2171183 : Blo 2169435 2171183 := bstep (se 1 (by rfl) ⟨1628387, by rfl⟩ : syracuseStep 2171183 = 3256775) B3256775
theorem B3256781 : Blo 2169435 3256781 := bbase (se 3 (by rfl) ⟨610646, by rfl⟩ : syracuseStep 3256781 = 1221293) (by norm_num)
theorem B2171187 : Blo 2169435 2171187 := bstep (se 1 (by rfl) ⟨1628390, by rfl⟩ : syracuseStep 2171187 = 3256781) B3256781
theorem B4885181 : Blo 2169435 4885181 := bbase (se 3 (by rfl) ⟨915971, by rfl⟩ : syracuseStep 4885181 = 1831943) (by norm_num)
theorem B3256787 : Blo 2169435 3256787 := bstep (se 1 (by rfl) ⟨2442590, by rfl⟩ : syracuseStep 3256787 = 4885181) B4885181
theorem B2171191 : Blo 2169435 2171191 := bstep (se 1 (by rfl) ⟨1628393, by rfl⟩ : syracuseStep 2171191 = 3256787) B3256787
theorem B3663893 : Blo 2169435 3663893 := bbase (se 6 (by rfl) ⟨85872, by rfl⟩ : syracuseStep 3663893 = 171745) (by norm_num)
theorem B2442595 : Blo 2169435 2442595 := bstep (se 1 (by rfl) ⟨1831946, by rfl⟩ : syracuseStep 2442595 = 3663893) B3663893
theorem B3256793 : Blo 2169435 3256793 := bstep (se 2 (by rfl) ⟨1221297, by rfl⟩ : syracuseStep 3256793 = 2442595) B2442595
theorem B2171195 : Blo 2169435 2171195 := bstep (se 1 (by rfl) ⟨1628396, by rfl⟩ : syracuseStep 2171195 = 3256793) B3256793
theorem B15650293 : Blo 2169435 15650293 := bbase (se 5 (by rfl) ⟨733607, by rfl⟩ : syracuseStep 15650293 = 1467215) (by norm_num)
theorem B20867057 : Blo 2169435 20867057 := bstep (se 2 (by rfl) ⟨7825146, by rfl⟩ : syracuseStep 20867057 = 15650293) B15650293
theorem B13911371 : Blo 2169435 13911371 := bstep (se 1 (by rfl) ⟨10433528, by rfl⟩ : syracuseStep 13911371 = 20867057) B20867057
theorem B9274247 : Blo 2169435 9274247 := bstep (se 1 (by rfl) ⟨6955685, by rfl⟩ : syracuseStep 9274247 = 13911371) B13911371
theorem B6182831 : Blo 2169435 6182831 := bstep (se 1 (by rfl) ⟨4637123, by rfl⟩ : syracuseStep 6182831 = 9274247) B9274247
theorem B16487549 : Blo 2169435 16487549 := bstep (se 3 (by rfl) ⟨3091415, by rfl⟩ : syracuseStep 16487549 = 6182831) B6182831
theorem B10991699 : Blo 2169435 10991699 := bstep (se 1 (by rfl) ⟨8243774, by rfl⟩ : syracuseStep 10991699 = 16487549) B16487549
theorem B7327799 : Blo 2169435 7327799 := bstep (se 1 (by rfl) ⟨5495849, by rfl⟩ : syracuseStep 7327799 = 10991699) B10991699
theorem B4885199 : Blo 2169435 4885199 := bstep (se 1 (by rfl) ⟨3663899, by rfl⟩ : syracuseStep 4885199 = 7327799) B7327799
theorem B3256799 : Blo 2169435 3256799 := bstep (se 1 (by rfl) ⟨2442599, by rfl⟩ : syracuseStep 3256799 = 4885199) B4885199
theorem B2171199 : Blo 2169435 2171199 := bstep (se 1 (by rfl) ⟨1628399, by rfl⟩ : syracuseStep 2171199 = 3256799) B3256799
theorem B3256805 : Blo 2169435 3256805 := bbase (se 4 (by rfl) ⟨305325, by rfl⟩ : syracuseStep 3256805 = 610651) (by norm_num)
theorem B2171203 : Blo 2169435 2171203 := bstep (se 1 (by rfl) ⟨1628402, by rfl⟩ : syracuseStep 2171203 = 3256805) B3256805
theorem B2509717 : Blo 2169435 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B3346289 : Blo 2169435 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B2230859 : Blo 2169435 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B5948957 : Blo 2169435 5948957 := bstep (se 3 (by rfl) ⟨1115429, by rfl⟩ : syracuseStep 5948957 = 2230859) B2230859
theorem B3965971 : Blo 2169435 3965971 := bstep (se 1 (by rfl) ⟨2974478, by rfl⟩ : syracuseStep 3965971 = 5948957) B5948957
theorem B5287961 : Blo 2169435 5287961 := bstep (se 2 (by rfl) ⟨1982985, by rfl⟩ : syracuseStep 5287961 = 3965971) B3965971
theorem B14101229 : Blo 2169435 14101229 := bstep (se 3 (by rfl) ⟨2643980, by rfl⟩ : syracuseStep 14101229 = 5287961) B5287961
theorem B37603277 : Blo 2169435 37603277 := bstep (se 3 (by rfl) ⟨7050614, by rfl⟩ : syracuseStep 37603277 = 14101229) B14101229
theorem B25068851 : Blo 2169435 25068851 := bstep (se 1 (by rfl) ⟨18801638, by rfl⟩ : syracuseStep 25068851 = 37603277) B37603277
theorem B16712567 : Blo 2169435 16712567 := bstep (se 1 (by rfl) ⟨12534425, by rfl⟩ : syracuseStep 16712567 = 25068851) B25068851
theorem B11141711 : Blo 2169435 11141711 := bstep (se 1 (by rfl) ⟨8356283, by rfl⟩ : syracuseStep 11141711 = 16712567) B16712567
theorem B7427807 : Blo 2169435 7427807 := bstep (se 1 (by rfl) ⟨5570855, by rfl⟩ : syracuseStep 7427807 = 11141711) B11141711
theorem B4951871 : Blo 2169435 4951871 := bstep (se 1 (by rfl) ⟨3713903, by rfl⟩ : syracuseStep 4951871 = 7427807) B7427807
theorem B3301247 : Blo 2169435 3301247 := bstep (se 1 (by rfl) ⟨2475935, by rfl⟩ : syracuseStep 3301247 = 4951871) B4951871
theorem B8803325 : Blo 2169435 8803325 := bstep (se 3 (by rfl) ⟨1650623, by rfl⟩ : syracuseStep 8803325 = 3301247) B3301247
theorem B5868883 : Blo 2169435 5868883 := bstep (se 1 (by rfl) ⟨4401662, by rfl⟩ : syracuseStep 5868883 = 8803325) B8803325
theorem B7825177 : Blo 2169435 7825177 := bstep (se 2 (by rfl) ⟨2934441, by rfl⟩ : syracuseStep 7825177 = 5868883) B5868883
theorem B10433569 : Blo 2169435 10433569 := bstep (se 2 (by rfl) ⟨3912588, by rfl⟩ : syracuseStep 10433569 = 7825177) B7825177
theorem B13911425 : Blo 2169435 13911425 := bstep (se 2 (by rfl) ⟨5216784, by rfl⟩ : syracuseStep 13911425 = 10433569) B10433569
theorem B9274283 : Blo 2169435 9274283 := bstep (se 1 (by rfl) ⟨6955712, by rfl⟩ : syracuseStep 9274283 = 13911425) B13911425
theorem B6182855 : Blo 2169435 6182855 := bstep (se 1 (by rfl) ⟨4637141, by rfl⟩ : syracuseStep 6182855 = 9274283) B9274283
theorem B4121903 : Blo 2169435 4121903 := bstep (se 1 (by rfl) ⟨3091427, by rfl⟩ : syracuseStep 4121903 = 6182855) B6182855
theorem B2747935 : Blo 2169435 2747935 := bstep (se 1 (by rfl) ⟨2060951, by rfl⟩ : syracuseStep 2747935 = 4121903) B4121903
theorem B3663913 : Blo 2169435 3663913 := bstep (se 2 (by rfl) ⟨1373967, by rfl⟩ : syracuseStep 3663913 = 2747935) B2747935
theorem B4885217 : Blo 2169435 4885217 := bstep (se 2 (by rfl) ⟨1831956, by rfl⟩ : syracuseStep 4885217 = 3663913) B3663913
theorem B3256811 : Blo 2169435 3256811 := bstep (se 1 (by rfl) ⟨2442608, by rfl⟩ : syracuseStep 3256811 = 4885217) B4885217
theorem B2171207 : Blo 2169435 2171207 := bstep (se 1 (by rfl) ⟨1628405, by rfl⟩ : syracuseStep 2171207 = 3256811) B3256811
theorem B2442613 : Blo 2169435 2442613 := bbase (se 5 (by rfl) ⟨114497, by rfl⟩ : syracuseStep 2442613 = 228995) (by norm_num)
theorem B3256817 : Blo 2169435 3256817 := bstep (se 2 (by rfl) ⟨1221306, by rfl⟩ : syracuseStep 3256817 = 2442613) B2442613
theorem B2171211 : Blo 2169435 2171211 := bstep (se 1 (by rfl) ⟨1628408, by rfl⟩ : syracuseStep 2171211 = 3256817) B3256817
theorem B2747945 : Blo 2169435 2747945 := bbase (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) (by norm_num)
theorem B7327853 : Blo 2169435 7327853 := bstep (se 3 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 7327853 = 2747945) B2747945
theorem B4885235 : Blo 2169435 4885235 := bstep (se 1 (by rfl) ⟨3663926, by rfl⟩ : syracuseStep 4885235 = 7327853) B7327853
theorem B3256823 : Blo 2169435 3256823 := bstep (se 1 (by rfl) ⟨2442617, by rfl⟩ : syracuseStep 3256823 = 4885235) B4885235
theorem B2171215 : Blo 2169435 2171215 := bstep (se 1 (by rfl) ⟨1628411, by rfl⟩ : syracuseStep 2171215 = 3256823) B3256823
theorem B3256829 : Blo 2169435 3256829 := bbase (se 3 (by rfl) ⟨610655, by rfl⟩ : syracuseStep 3256829 = 1221311) (by norm_num)
theorem B2171219 : Blo 2169435 2171219 := bstep (se 1 (by rfl) ⟨1628414, by rfl⟩ : syracuseStep 2171219 = 3256829) B3256829
theorem B4885253 : Blo 2169435 4885253 := bbase (se 4 (by rfl) ⟨457992, by rfl⟩ : syracuseStep 4885253 = 915985) (by norm_num)
theorem B3256835 : Blo 2169435 3256835 := bstep (se 1 (by rfl) ⟨2442626, by rfl⟩ : syracuseStep 3256835 = 4885253) B4885253
theorem B2171223 : Blo 2169435 2171223 := bstep (se 1 (by rfl) ⟨1628417, by rfl⟩ : syracuseStep 2171223 = 3256835) B3256835
theorem B4121941 : Blo 2169435 4121941 := bbase (se 12 (by rfl) ⟨1509, by rfl⟩ : syracuseStep 4121941 = 3019) (by norm_num)
theorem B5495921 : Blo 2169435 5495921 := bstep (se 2 (by rfl) ⟨2060970, by rfl⟩ : syracuseStep 5495921 = 4121941) B4121941
theorem B3663947 : Blo 2169435 3663947 := bstep (se 1 (by rfl) ⟨2747960, by rfl⟩ : syracuseStep 3663947 = 5495921) B5495921
theorem B2442631 : Blo 2169435 2442631 := bstep (se 1 (by rfl) ⟨1831973, by rfl⟩ : syracuseStep 2442631 = 3663947) B3663947
theorem B3256841 : Blo 2169435 3256841 := bstep (se 2 (by rfl) ⟨1221315, by rfl⟩ : syracuseStep 3256841 = 2442631) B2442631
theorem B2171227 : Blo 2169435 2171227 := bstep (se 1 (by rfl) ⟨1628420, by rfl⟩ : syracuseStep 2171227 = 3256841) B3256841
theorem B10991861 : Blo 2169435 10991861 := bbase (se 5 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 10991861 = 1030487) (by norm_num)
theorem B7327907 : Blo 2169435 7327907 := bstep (se 1 (by rfl) ⟨5495930, by rfl⟩ : syracuseStep 7327907 = 10991861) B10991861
theorem B4885271 : Blo 2169435 4885271 := bstep (se 1 (by rfl) ⟨3663953, by rfl⟩ : syracuseStep 4885271 = 7327907) B7327907
theorem B3256847 : Blo 2169435 3256847 := bstep (se 1 (by rfl) ⟨2442635, by rfl⟩ : syracuseStep 3256847 = 4885271) B4885271
theorem B2171231 : Blo 2169435 2171231 := bstep (se 1 (by rfl) ⟨1628423, by rfl⟩ : syracuseStep 2171231 = 3256847) B3256847
theorem B3256853 : Blo 2169435 3256853 := bbase (se 6 (by rfl) ⟨76332, by rfl⟩ : syracuseStep 3256853 = 152665) (by norm_num)
theorem B2171235 : Blo 2169435 2171235 := bstep (se 1 (by rfl) ⟨1628426, by rfl⟩ : syracuseStep 2171235 = 3256853) B3256853
theorem B5216861 : Blo 2169435 5216861 := bbase (se 3 (by rfl) ⟨978161, by rfl⟩ : syracuseStep 5216861 = 1956323) (by norm_num)
theorem B3477907 : Blo 2169435 3477907 := bstep (se 1 (by rfl) ⟨2608430, by rfl⟩ : syracuseStep 3477907 = 5216861) B5216861
theorem B18548837 : Blo 2169435 18548837 := bstep (se 4 (by rfl) ⟨1738953, by rfl⟩ : syracuseStep 18548837 = 3477907) B3477907
theorem B12365891 : Blo 2169435 12365891 := bstep (se 1 (by rfl) ⟨9274418, by rfl⟩ : syracuseStep 12365891 = 18548837) B18548837
theorem B8243927 : Blo 2169435 8243927 := bstep (se 1 (by rfl) ⟨6182945, by rfl⟩ : syracuseStep 8243927 = 12365891) B12365891
theorem B5495951 : Blo 2169435 5495951 := bstep (se 1 (by rfl) ⟨4121963, by rfl⟩ : syracuseStep 5495951 = 8243927) B8243927
theorem B3663967 : Blo 2169435 3663967 := bstep (se 1 (by rfl) ⟨2747975, by rfl⟩ : syracuseStep 3663967 = 5495951) B5495951
theorem B4885289 : Blo 2169435 4885289 := bstep (se 2 (by rfl) ⟨1831983, by rfl⟩ : syracuseStep 4885289 = 3663967) B3663967
theorem B3256859 : Blo 2169435 3256859 := bstep (se 1 (by rfl) ⟨2442644, by rfl⟩ : syracuseStep 3256859 = 4885289) B4885289
theorem B2171239 : Blo 2169435 2171239 := bstep (se 1 (by rfl) ⟨1628429, by rfl⟩ : syracuseStep 2171239 = 3256859) B3256859
theorem B2442649 : Blo 2169435 2442649 := bbase (se 2 (by rfl) ⟨915993, by rfl⟩ : syracuseStep 2442649 = 1831987) (by norm_num)
theorem B3256865 : Blo 2169435 3256865 := bstep (se 2 (by rfl) ⟨1221324, by rfl⟩ : syracuseStep 3256865 = 2442649) B2442649
theorem B2171243 : Blo 2169435 2171243 := bstep (se 1 (by rfl) ⟨1628432, by rfl⟩ : syracuseStep 2171243 = 3256865) B3256865
theorem B8243957 : Blo 2169435 8243957 := bbase (se 5 (by rfl) ⟨386435, by rfl⟩ : syracuseStep 8243957 = 772871) (by norm_num)
theorem B5495971 : Blo 2169435 5495971 := bstep (se 1 (by rfl) ⟨4121978, by rfl⟩ : syracuseStep 5495971 = 8243957) B8243957
theorem B7327961 : Blo 2169435 7327961 := bstep (se 2 (by rfl) ⟨2747985, by rfl⟩ : syracuseStep 7327961 = 5495971) B5495971
theorem B4885307 : Blo 2169435 4885307 := bstep (se 1 (by rfl) ⟨3663980, by rfl⟩ : syracuseStep 4885307 = 7327961) B7327961
theorem B3256871 : Blo 2169435 3256871 := bstep (se 1 (by rfl) ⟨2442653, by rfl⟩ : syracuseStep 3256871 = 4885307) B4885307
theorem B2171247 : Blo 2169435 2171247 := bstep (se 1 (by rfl) ⟨1628435, by rfl⟩ : syracuseStep 2171247 = 3256871) B3256871
theorem B3256877 : Blo 2169435 3256877 := bbase (se 3 (by rfl) ⟨610664, by rfl⟩ : syracuseStep 3256877 = 1221329) (by norm_num)
theorem B2171251 : Blo 2169435 2171251 := bstep (se 1 (by rfl) ⟨1628438, by rfl⟩ : syracuseStep 2171251 = 3256877) B3256877
theorem B4885325 : Blo 2169435 4885325 := bbase (se 3 (by rfl) ⟨915998, by rfl⟩ : syracuseStep 4885325 = 1831997) (by norm_num)
theorem B3256883 : Blo 2169435 3256883 := bstep (se 1 (by rfl) ⟨2442662, by rfl⟩ : syracuseStep 3256883 = 4885325) B4885325
theorem B2171255 : Blo 2169435 2171255 := bstep (se 1 (by rfl) ⟨1628441, by rfl⟩ : syracuseStep 2171255 = 3256883) B3256883
theorem B2748001 : Blo 2169435 2748001 := bbase (se 2 (by rfl) ⟨1030500, by rfl⟩ : syracuseStep 2748001 = 2061001) (by norm_num)
theorem B3664001 : Blo 2169435 3664001 := bstep (se 2 (by rfl) ⟨1374000, by rfl⟩ : syracuseStep 3664001 = 2748001) B2748001
theorem B2442667 : Blo 2169435 2442667 := bstep (se 1 (by rfl) ⟨1832000, by rfl⟩ : syracuseStep 2442667 = 3664001) B3664001
theorem B3256889 : Blo 2169435 3256889 := bstep (se 2 (by rfl) ⟨1221333, by rfl⟩ : syracuseStep 3256889 = 2442667) B2442667
theorem B2171259 : Blo 2169435 2171259 := bstep (se 1 (by rfl) ⟨1628444, by rfl⟩ : syracuseStep 2171259 = 3256889) B3256889
theorem B24732053 : Blo 2169435 24732053 := bbase (se 6 (by rfl) ⟨579657, by rfl⟩ : syracuseStep 24732053 = 1159315) (by norm_num)
theorem B16488035 : Blo 2169435 16488035 := bstep (se 1 (by rfl) ⟨12366026, by rfl⟩ : syracuseStep 16488035 = 24732053) B24732053
theorem B10992023 : Blo 2169435 10992023 := bstep (se 1 (by rfl) ⟨8244017, by rfl⟩ : syracuseStep 10992023 = 16488035) B16488035
theorem B7328015 : Blo 2169435 7328015 := bstep (se 1 (by rfl) ⟨5496011, by rfl⟩ : syracuseStep 7328015 = 10992023) B10992023
theorem B4885343 : Blo 2169435 4885343 := bstep (se 1 (by rfl) ⟨3664007, by rfl⟩ : syracuseStep 4885343 = 7328015) B7328015
theorem B3256895 : Blo 2169435 3256895 := bstep (se 1 (by rfl) ⟨2442671, by rfl⟩ : syracuseStep 3256895 = 4885343) B4885343
theorem B2171263 : Blo 2169435 2171263 := bstep (se 1 (by rfl) ⟨1628447, by rfl⟩ : syracuseStep 2171263 = 3256895) B3256895
theorem B3256901 : Blo 2169435 3256901 := bbase (se 4 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 3256901 = 610669) (by norm_num)
theorem B2171267 : Blo 2169435 2171267 := bstep (se 1 (by rfl) ⟨1628450, by rfl⟩ : syracuseStep 2171267 = 3256901) B3256901
theorem B3664021 : Blo 2169435 3664021 := bbase (se 6 (by rfl) ⟨85875, by rfl⟩ : syracuseStep 3664021 = 171751) (by norm_num)
theorem B4885361 : Blo 2169435 4885361 := bstep (se 2 (by rfl) ⟨1832010, by rfl⟩ : syracuseStep 4885361 = 3664021) B3664021
theorem B3256907 : Blo 2169435 3256907 := bstep (se 1 (by rfl) ⟨2442680, by rfl⟩ : syracuseStep 3256907 = 4885361) B4885361
theorem B2171271 : Blo 2169435 2171271 := bstep (se 1 (by rfl) ⟨1628453, by rfl⟩ : syracuseStep 2171271 = 3256907) B3256907
theorem B2442685 : Blo 2169435 2442685 := bbase (se 3 (by rfl) ⟨458003, by rfl⟩ : syracuseStep 2442685 = 916007) (by norm_num)
theorem B3256913 : Blo 2169435 3256913 := bstep (se 2 (by rfl) ⟨1221342, by rfl⟩ : syracuseStep 3256913 = 2442685) B2442685
theorem B2171275 : Blo 2169435 2171275 := bstep (se 1 (by rfl) ⟨1628456, by rfl⟩ : syracuseStep 2171275 = 3256913) B3256913
theorem B7328069 : Blo 2169435 7328069 := bbase (se 4 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 7328069 = 1374013) (by norm_num)
theorem B4885379 : Blo 2169435 4885379 := bstep (se 1 (by rfl) ⟨3664034, by rfl⟩ : syracuseStep 4885379 = 7328069) B7328069
theorem B3256919 : Blo 2169435 3256919 := bstep (se 1 (by rfl) ⟨2442689, by rfl⟩ : syracuseStep 3256919 = 4885379) B4885379
theorem B2171279 : Blo 2169435 2171279 := bstep (se 1 (by rfl) ⟨1628459, by rfl⟩ : syracuseStep 2171279 = 3256919) B3256919
theorem B3256925 : Blo 2169435 3256925 := bbase (se 3 (by rfl) ⟨610673, by rfl⟩ : syracuseStep 3256925 = 1221347) (by norm_num)
theorem B2171283 : Blo 2169435 2171283 := bstep (se 1 (by rfl) ⟨1628462, by rfl⟩ : syracuseStep 2171283 = 3256925) B3256925
theorem B4885397 : Blo 2169435 4885397 := bbase (se 6 (by rfl) ⟨114501, by rfl⟩ : syracuseStep 4885397 = 229003) (by norm_num)
theorem B3256931 : Blo 2169435 3256931 := bstep (se 1 (by rfl) ⟨2442698, by rfl⟩ : syracuseStep 3256931 = 4885397) B4885397
theorem B2171287 : Blo 2169435 2171287 := bstep (se 1 (by rfl) ⟨1628465, by rfl⟩ : syracuseStep 2171287 = 3256931) B3256931
theorem B18091061 : Blo 2169435 18091061 := bbase (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) (by norm_num)
theorem B12060707 : Blo 2169435 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B128647541 : Blo 2169435 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B85765027 : Blo 2169435 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B114353369 : Blo 2169435 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B76235579 : Blo 2169435 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B50823719 : Blo 2169435 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B33882479 : Blo 2169435 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B22588319 : Blo 2169435 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B15058879 : Blo 2169435 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B80314021 : Blo 2169435 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B428341445 : Blo 2169435 428341445 := bstep (se 4 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 428341445 = 80314021) B80314021
theorem B285560963 : Blo 2169435 285560963 := bstep (se 1 (by rfl) ⟨214170722, by rfl⟩ : syracuseStep 285560963 = 428341445) B428341445
theorem B190373975 : Blo 2169435 190373975 := bstep (se 1 (by rfl) ⟨142780481, by rfl⟩ : syracuseStep 190373975 = 285560963) B285560963
theorem B126915983 : Blo 2169435 126915983 := bstep (se 1 (by rfl) ⟨95186987, by rfl⟩ : syracuseStep 126915983 = 190373975) B190373975
theorem B84610655 : Blo 2169435 84610655 := bstep (se 1 (by rfl) ⟨63457991, by rfl⟩ : syracuseStep 84610655 = 126915983) B126915983
theorem B56407103 : Blo 2169435 56407103 := bstep (se 1 (by rfl) ⟨42305327, by rfl⟩ : syracuseStep 56407103 = 84610655) B84610655
theorem B37604735 : Blo 2169435 37604735 := bstep (se 1 (by rfl) ⟨28203551, by rfl⟩ : syracuseStep 37604735 = 56407103) B56407103
theorem B25069823 : Blo 2169435 25069823 := bstep (se 1 (by rfl) ⟨18802367, by rfl⟩ : syracuseStep 25069823 = 37604735) B37604735
theorem B16713215 : Blo 2169435 16713215 := bstep (se 1 (by rfl) ⟨12534911, by rfl⟩ : syracuseStep 16713215 = 25069823) B25069823
theorem B11142143 : Blo 2169435 11142143 := bstep (se 1 (by rfl) ⟨8356607, by rfl⟩ : syracuseStep 11142143 = 16713215) B16713215
theorem B7428095 : Blo 2169435 7428095 := bstep (se 1 (by rfl) ⟨5571071, by rfl⟩ : syracuseStep 7428095 = 11142143) B11142143
theorem B4952063 : Blo 2169435 4952063 := bstep (se 1 (by rfl) ⟨3714047, by rfl⟩ : syracuseStep 4952063 = 7428095) B7428095
theorem B13205501 : Blo 2169435 13205501 := bstep (se 3 (by rfl) ⟨2476031, by rfl⟩ : syracuseStep 13205501 = 4952063) B4952063
theorem B8803667 : Blo 2169435 8803667 := bstep (se 1 (by rfl) ⟨6602750, by rfl⟩ : syracuseStep 8803667 = 13205501) B13205501
theorem B5869111 : Blo 2169435 5869111 := bstep (se 1 (by rfl) ⟨4401833, by rfl⟩ : syracuseStep 5869111 = 8803667) B8803667
theorem B7825481 : Blo 2169435 7825481 := bstep (se 2 (by rfl) ⟨2934555, by rfl⟩ : syracuseStep 7825481 = 5869111) B5869111
theorem B5216987 : Blo 2169435 5216987 := bstep (se 1 (by rfl) ⟨3912740, by rfl⟩ : syracuseStep 5216987 = 7825481) B7825481
theorem B3477991 : Blo 2169435 3477991 := bstep (se 1 (by rfl) ⟨2608493, by rfl⟩ : syracuseStep 3477991 = 5216987) B5216987
theorem B4637321 : Blo 2169435 4637321 := bstep (se 2 (by rfl) ⟨1738995, by rfl⟩ : syracuseStep 4637321 = 3477991) B3477991
theorem B3091547 : Blo 2169435 3091547 := bstep (se 1 (by rfl) ⟨2318660, by rfl⟩ : syracuseStep 3091547 = 4637321) B4637321
theorem B8244125 : Blo 2169435 8244125 := bstep (se 3 (by rfl) ⟨1545773, by rfl⟩ : syracuseStep 8244125 = 3091547) B3091547
theorem B5496083 : Blo 2169435 5496083 := bstep (se 1 (by rfl) ⟨4122062, by rfl⟩ : syracuseStep 5496083 = 8244125) B8244125
theorem B3664055 : Blo 2169435 3664055 := bstep (se 1 (by rfl) ⟨2748041, by rfl⟩ : syracuseStep 3664055 = 5496083) B5496083
theorem B2442703 : Blo 2169435 2442703 := bstep (se 1 (by rfl) ⟨1832027, by rfl⟩ : syracuseStep 2442703 = 3664055) B3664055
theorem B3256937 : Blo 2169435 3256937 := bstep (se 2 (by rfl) ⟨1221351, by rfl⟩ : syracuseStep 3256937 = 2442703) B2442703
theorem B2171291 : Blo 2169435 2171291 := bstep (se 1 (by rfl) ⟨1628468, by rfl⟩ : syracuseStep 2171291 = 3256937) B3256937
theorem B7825493 : Blo 2169435 7825493 := bbase (se 8 (by rfl) ⟨45852, by rfl⟩ : syracuseStep 7825493 = 91705) (by norm_num)
theorem B5216995 : Blo 2169435 5216995 := bstep (se 1 (by rfl) ⟨3912746, by rfl⟩ : syracuseStep 5216995 = 7825493) B7825493
theorem B6955993 : Blo 2169435 6955993 := bstep (se 2 (by rfl) ⟨2608497, by rfl⟩ : syracuseStep 6955993 = 5216995) B5216995
theorem B9274657 : Blo 2169435 9274657 := bstep (se 2 (by rfl) ⟨3477996, by rfl⟩ : syracuseStep 9274657 = 6955993) B6955993
theorem B12366209 : Blo 2169435 12366209 := bstep (se 2 (by rfl) ⟨4637328, by rfl⟩ : syracuseStep 12366209 = 9274657) B9274657
theorem B8244139 : Blo 2169435 8244139 := bstep (se 1 (by rfl) ⟨6183104, by rfl⟩ : syracuseStep 8244139 = 12366209) B12366209
theorem B10992185 : Blo 2169435 10992185 := bstep (se 2 (by rfl) ⟨4122069, by rfl⟩ : syracuseStep 10992185 = 8244139) B8244139
theorem B7328123 : Blo 2169435 7328123 := bstep (se 1 (by rfl) ⟨5496092, by rfl⟩ : syracuseStep 7328123 = 10992185) B10992185
theorem B4885415 : Blo 2169435 4885415 := bstep (se 1 (by rfl) ⟨3664061, by rfl⟩ : syracuseStep 4885415 = 7328123) B7328123
theorem B3256943 : Blo 2169435 3256943 := bstep (se 1 (by rfl) ⟨2442707, by rfl⟩ : syracuseStep 3256943 = 4885415) B4885415
theorem B2171295 : Blo 2169435 2171295 := bstep (se 1 (by rfl) ⟨1628471, by rfl⟩ : syracuseStep 2171295 = 3256943) B3256943
theorem B3256949 : Blo 2169435 3256949 := bbase (se 5 (by rfl) ⟨152669, by rfl⟩ : syracuseStep 3256949 = 305339) (by norm_num)
theorem B2171299 : Blo 2169435 2171299 := bstep (se 1 (by rfl) ⟨1628474, by rfl⟩ : syracuseStep 2171299 = 3256949) B3256949
theorem B4122085 : Blo 2169435 4122085 := bbase (se 4 (by rfl) ⟨386445, by rfl⟩ : syracuseStep 4122085 = 772891) (by norm_num)
theorem B5496113 : Blo 2169435 5496113 := bstep (se 2 (by rfl) ⟨2061042, by rfl⟩ : syracuseStep 5496113 = 4122085) B4122085
theorem B3664075 : Blo 2169435 3664075 := bstep (se 1 (by rfl) ⟨2748056, by rfl⟩ : syracuseStep 3664075 = 5496113) B5496113
theorem B4885433 : Blo 2169435 4885433 := bstep (se 2 (by rfl) ⟨1832037, by rfl⟩ : syracuseStep 4885433 = 3664075) B3664075
theorem B3256955 : Blo 2169435 3256955 := bstep (se 1 (by rfl) ⟨2442716, by rfl⟩ : syracuseStep 3256955 = 4885433) B4885433
theorem B2171303 : Blo 2169435 2171303 := bstep (se 1 (by rfl) ⟨1628477, by rfl⟩ : syracuseStep 2171303 = 3256955) B3256955
theorem B2442721 : Blo 2169435 2442721 := bbase (se 2 (by rfl) ⟨916020, by rfl⟩ : syracuseStep 2442721 = 1832041) (by norm_num)
theorem B3256961 : Blo 2169435 3256961 := bstep (se 2 (by rfl) ⟨1221360, by rfl⟩ : syracuseStep 3256961 = 2442721) B2442721
theorem B2171307 : Blo 2169435 2171307 := bstep (se 1 (by rfl) ⟨1628480, by rfl⟩ : syracuseStep 2171307 = 3256961) B3256961
theorem B5496133 : Blo 2169435 5496133 := bbase (se 4 (by rfl) ⟨515262, by rfl⟩ : syracuseStep 5496133 = 1030525) (by norm_num)
theorem B7328177 : Blo 2169435 7328177 := bstep (se 2 (by rfl) ⟨2748066, by rfl⟩ : syracuseStep 7328177 = 5496133) B5496133
theorem B4885451 : Blo 2169435 4885451 := bstep (se 1 (by rfl) ⟨3664088, by rfl⟩ : syracuseStep 4885451 = 7328177) B7328177
theorem B3256967 : Blo 2169435 3256967 := bstep (se 1 (by rfl) ⟨2442725, by rfl⟩ : syracuseStep 3256967 = 4885451) B4885451
theorem B2171311 : Blo 2169435 2171311 := bstep (se 1 (by rfl) ⟨1628483, by rfl⟩ : syracuseStep 2171311 = 3256967) B3256967
theorem B3256973 : Blo 2169435 3256973 := bbase (se 3 (by rfl) ⟨610682, by rfl⟩ : syracuseStep 3256973 = 1221365) (by norm_num)
theorem B2171315 : Blo 2169435 2171315 := bstep (se 1 (by rfl) ⟨1628486, by rfl⟩ : syracuseStep 2171315 = 3256973) B3256973
theorem B4885469 : Blo 2169435 4885469 := bbase (se 3 (by rfl) ⟨916025, by rfl⟩ : syracuseStep 4885469 = 1832051) (by norm_num)
theorem B3256979 : Blo 2169435 3256979 := bstep (se 1 (by rfl) ⟨2442734, by rfl⟩ : syracuseStep 3256979 = 4885469) B4885469
theorem B2171319 : Blo 2169435 2171319 := bstep (se 1 (by rfl) ⟨1628489, by rfl⟩ : syracuseStep 2171319 = 3256979) B3256979
theorem B3664109 : Blo 2169435 3664109 := bbase (se 3 (by rfl) ⟨687020, by rfl⟩ : syracuseStep 3664109 = 1374041) (by norm_num)
theorem B2442739 : Blo 2169435 2442739 := bstep (se 1 (by rfl) ⟨1832054, by rfl⟩ : syracuseStep 2442739 = 3664109) B3664109
theorem B3256985 : Blo 2169435 3256985 := bstep (se 2 (by rfl) ⟨1221369, by rfl⟩ : syracuseStep 3256985 = 2442739) B2442739
theorem B2171323 : Blo 2169435 2171323 := bstep (se 1 (by rfl) ⟨1628492, by rfl⟩ : syracuseStep 2171323 = 3256985) B3256985
theorem B6267557 : Blo 2169435 6267557 := bbase (se 4 (by rfl) ⟨587583, by rfl⟩ : syracuseStep 6267557 = 1175167) (by norm_num)
theorem B4178371 : Blo 2169435 4178371 := bstep (se 1 (by rfl) ⟨3133778, by rfl⟩ : syracuseStep 4178371 = 6267557) B6267557
theorem B5571161 : Blo 2169435 5571161 := bstep (se 2 (by rfl) ⟨2089185, by rfl⟩ : syracuseStep 5571161 = 4178371) B4178371
theorem B3714107 : Blo 2169435 3714107 := bstep (se 1 (by rfl) ⟨2785580, by rfl⟩ : syracuseStep 3714107 = 5571161) B5571161
theorem B9904285 : Blo 2169435 9904285 := bstep (se 3 (by rfl) ⟨1857053, by rfl⟩ : syracuseStep 9904285 = 3714107) B3714107
theorem B52822853 : Blo 2169435 52822853 := bstep (se 4 (by rfl) ⟨4952142, by rfl⟩ : syracuseStep 52822853 = 9904285) B9904285
theorem B35215235 : Blo 2169435 35215235 := bstep (se 1 (by rfl) ⟨26411426, by rfl⟩ : syracuseStep 35215235 = 52822853) B52822853
theorem B23476823 : Blo 2169435 23476823 := bstep (se 1 (by rfl) ⟨17607617, by rfl⟩ : syracuseStep 23476823 = 35215235) B35215235
theorem B15651215 : Blo 2169435 15651215 := bstep (se 1 (by rfl) ⟨11738411, by rfl⟩ : syracuseStep 15651215 = 23476823) B23476823
theorem B10434143 : Blo 2169435 10434143 := bstep (se 1 (by rfl) ⟨7825607, by rfl⟩ : syracuseStep 10434143 = 15651215) B15651215
theorem B27824381 : Blo 2169435 27824381 := bstep (se 3 (by rfl) ⟨5217071, by rfl⟩ : syracuseStep 27824381 = 10434143) B10434143
theorem B18549587 : Blo 2169435 18549587 := bstep (se 1 (by rfl) ⟨13912190, by rfl⟩ : syracuseStep 18549587 = 27824381) B27824381
theorem B12366391 : Blo 2169435 12366391 := bstep (se 1 (by rfl) ⟨9274793, by rfl⟩ : syracuseStep 12366391 = 18549587) B18549587
theorem B16488521 : Blo 2169435 16488521 := bstep (se 2 (by rfl) ⟨6183195, by rfl⟩ : syracuseStep 16488521 = 12366391) B12366391
theorem B10992347 : Blo 2169435 10992347 := bstep (se 1 (by rfl) ⟨8244260, by rfl⟩ : syracuseStep 10992347 = 16488521) B16488521
theorem B7328231 : Blo 2169435 7328231 := bstep (se 1 (by rfl) ⟨5496173, by rfl⟩ : syracuseStep 7328231 = 10992347) B10992347
theorem B4885487 : Blo 2169435 4885487 := bstep (se 1 (by rfl) ⟨3664115, by rfl⟩ : syracuseStep 4885487 = 7328231) B7328231
theorem B3256991 : Blo 2169435 3256991 := bstep (se 1 (by rfl) ⟨2442743, by rfl⟩ : syracuseStep 3256991 = 4885487) B4885487
theorem B2171327 : Blo 2169435 2171327 := bstep (se 1 (by rfl) ⟨1628495, by rfl⟩ : syracuseStep 2171327 = 3256991) B3256991
theorem B3256997 : Blo 2169435 3256997 := bbase (se 4 (by rfl) ⟨305343, by rfl⟩ : syracuseStep 3256997 = 610687) (by norm_num)
theorem B2171331 : Blo 2169435 2171331 := bstep (se 1 (by rfl) ⟨1628498, by rfl⟩ : syracuseStep 2171331 = 3256997) B3256997
theorem B2748097 : Blo 2169435 2748097 := bbase (se 2 (by rfl) ⟨1030536, by rfl⟩ : syracuseStep 2748097 = 2061073) (by norm_num)
theorem B3664129 : Blo 2169435 3664129 := bstep (se 2 (by rfl) ⟨1374048, by rfl⟩ : syracuseStep 3664129 = 2748097) B2748097
theorem B4885505 : Blo 2169435 4885505 := bstep (se 2 (by rfl) ⟨1832064, by rfl⟩ : syracuseStep 4885505 = 3664129) B3664129
theorem B3257003 : Blo 2169435 3257003 := bstep (se 1 (by rfl) ⟨2442752, by rfl⟩ : syracuseStep 3257003 = 4885505) B4885505
theorem B2171335 : Blo 2169435 2171335 := bstep (se 1 (by rfl) ⟨1628501, by rfl⟩ : syracuseStep 2171335 = 3257003) B3257003
theorem B2442757 : Blo 2169435 2442757 := bbase (se 4 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 2442757 = 458017) (by norm_num)
theorem B3257009 : Blo 2169435 3257009 := bstep (se 2 (by rfl) ⟨1221378, by rfl⟩ : syracuseStep 3257009 = 2442757) B2442757
theorem B2171339 : Blo 2169435 2171339 := bstep (se 1 (by rfl) ⟨1628504, by rfl⟩ : syracuseStep 2171339 = 3257009) B3257009
theorem B3091621 : Blo 2169435 3091621 := bbase (se 4 (by rfl) ⟨289839, by rfl⟩ : syracuseStep 3091621 = 579679) (by norm_num)
theorem B4122161 : Blo 2169435 4122161 := bstep (se 2 (by rfl) ⟨1545810, by rfl⟩ : syracuseStep 4122161 = 3091621) B3091621
theorem B2748107 : Blo 2169435 2748107 := bstep (se 1 (by rfl) ⟨2061080, by rfl⟩ : syracuseStep 2748107 = 4122161) B4122161
theorem B7328285 : Blo 2169435 7328285 := bstep (se 3 (by rfl) ⟨1374053, by rfl⟩ : syracuseStep 7328285 = 2748107) B2748107
theorem B4885523 : Blo 2169435 4885523 := bstep (se 1 (by rfl) ⟨3664142, by rfl⟩ : syracuseStep 4885523 = 7328285) B7328285
theorem B3257015 : Blo 2169435 3257015 := bstep (se 1 (by rfl) ⟨2442761, by rfl⟩ : syracuseStep 3257015 = 4885523) B4885523
theorem B2171343 : Blo 2169435 2171343 := bstep (se 1 (by rfl) ⟨1628507, by rfl⟩ : syracuseStep 2171343 = 3257015) B3257015
theorem B3257021 : Blo 2169435 3257021 := bbase (se 3 (by rfl) ⟨610691, by rfl⟩ : syracuseStep 3257021 = 1221383) (by norm_num)
theorem B2171347 : Blo 2169435 2171347 := bstep (se 1 (by rfl) ⟨1628510, by rfl⟩ : syracuseStep 2171347 = 3257021) B3257021
theorem B4885541 : Blo 2169435 4885541 := bbase (se 4 (by rfl) ⟨458019, by rfl⟩ : syracuseStep 4885541 = 916039) (by norm_num)
theorem B3257027 : Blo 2169435 3257027 := bstep (se 1 (by rfl) ⟨2442770, by rfl⟩ : syracuseStep 3257027 = 4885541) B4885541
theorem B2171351 : Blo 2169435 2171351 := bstep (se 1 (by rfl) ⟨1628513, by rfl⟩ : syracuseStep 2171351 = 3257027) B3257027
theorem B5496245 : Blo 2169435 5496245 := bbase (se 5 (by rfl) ⟨257636, by rfl⟩ : syracuseStep 5496245 = 515273) (by norm_num)
theorem B3664163 : Blo 2169435 3664163 := bstep (se 1 (by rfl) ⟨2748122, by rfl⟩ : syracuseStep 3664163 = 5496245) B5496245
theorem B2442775 : Blo 2169435 2442775 := bstep (se 1 (by rfl) ⟨1832081, by rfl⟩ : syracuseStep 2442775 = 3664163) B3664163
theorem B3257033 : Blo 2169435 3257033 := bstep (se 2 (by rfl) ⟨1221387, by rfl⟩ : syracuseStep 3257033 = 2442775) B2442775
theorem B2171355 : Blo 2169435 2171355 := bstep (se 1 (by rfl) ⟨1628516, by rfl⟩ : syracuseStep 2171355 = 3257033) B3257033
theorem B5217149 : Blo 2169435 5217149 := bbase (se 3 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 5217149 = 1956431) (by norm_num)
theorem B13912397 : Blo 2169435 13912397 := bstep (se 3 (by rfl) ⟨2608574, by rfl⟩ : syracuseStep 13912397 = 5217149) B5217149
theorem B9274931 : Blo 2169435 9274931 := bstep (se 1 (by rfl) ⟨6956198, by rfl⟩ : syracuseStep 9274931 = 13912397) B13912397
theorem B6183287 : Blo 2169435 6183287 := bstep (se 1 (by rfl) ⟨4637465, by rfl⟩ : syracuseStep 6183287 = 9274931) B9274931
theorem B4122191 : Blo 2169435 4122191 := bstep (se 1 (by rfl) ⟨3091643, by rfl⟩ : syracuseStep 4122191 = 6183287) B6183287
theorem B10992509 : Blo 2169435 10992509 := bstep (se 3 (by rfl) ⟨2061095, by rfl⟩ : syracuseStep 10992509 = 4122191) B4122191
theorem B7328339 : Blo 2169435 7328339 := bstep (se 1 (by rfl) ⟨5496254, by rfl⟩ : syracuseStep 7328339 = 10992509) B10992509
theorem B4885559 : Blo 2169435 4885559 := bstep (se 1 (by rfl) ⟨3664169, by rfl⟩ : syracuseStep 4885559 = 7328339) B7328339
theorem B3257039 : Blo 2169435 3257039 := bstep (se 1 (by rfl) ⟨2442779, by rfl⟩ : syracuseStep 3257039 = 4885559) B4885559
theorem B2171359 : Blo 2169435 2171359 := bstep (se 1 (by rfl) ⟨1628519, by rfl⟩ : syracuseStep 2171359 = 3257039) B3257039
theorem B3257045 : Blo 2169435 3257045 := bbase (se 7 (by rfl) ⟨38168, by rfl⟩ : syracuseStep 3257045 = 76337) (by norm_num)
theorem B2171363 : Blo 2169435 2171363 := bstep (se 1 (by rfl) ⟨1628522, by rfl⟩ : syracuseStep 2171363 = 3257045) B3257045
theorem B3912877 : Blo 2169435 3912877 := bbase (se 3 (by rfl) ⟨733664, by rfl⟩ : syracuseStep 3912877 = 1467329) (by norm_num)
theorem B5217169 : Blo 2169435 5217169 := bstep (se 2 (by rfl) ⟨1956438, by rfl⟩ : syracuseStep 5217169 = 3912877) B3912877
theorem B6956225 : Blo 2169435 6956225 := bstep (se 2 (by rfl) ⟨2608584, by rfl⟩ : syracuseStep 6956225 = 5217169) B5217169
theorem B4637483 : Blo 2169435 4637483 := bstep (se 1 (by rfl) ⟨3478112, by rfl⟩ : syracuseStep 4637483 = 6956225) B6956225
theorem B3091655 : Blo 2169435 3091655 := bstep (se 1 (by rfl) ⟨2318741, by rfl⟩ : syracuseStep 3091655 = 4637483) B4637483
theorem B8244413 : Blo 2169435 8244413 := bstep (se 3 (by rfl) ⟨1545827, by rfl⟩ : syracuseStep 8244413 = 3091655) B3091655
theorem B5496275 : Blo 2169435 5496275 := bstep (se 1 (by rfl) ⟨4122206, by rfl⟩ : syracuseStep 5496275 = 8244413) B8244413
theorem B3664183 : Blo 2169435 3664183 := bstep (se 1 (by rfl) ⟨2748137, by rfl⟩ : syracuseStep 3664183 = 5496275) B5496275
theorem B4885577 : Blo 2169435 4885577 := bstep (se 2 (by rfl) ⟨1832091, by rfl⟩ : syracuseStep 4885577 = 3664183) B3664183
theorem B3257051 : Blo 2169435 3257051 := bstep (se 1 (by rfl) ⟨2442788, by rfl⟩ : syracuseStep 3257051 = 4885577) B4885577
theorem B2171367 : Blo 2169435 2171367 := bstep (se 1 (by rfl) ⟨1628525, by rfl⟩ : syracuseStep 2171367 = 3257051) B3257051
theorem B2442793 : Blo 2169435 2442793 := bbase (se 2 (by rfl) ⟨916047, by rfl⟩ : syracuseStep 2442793 = 1832095) (by norm_num)
theorem B3257057 : Blo 2169435 3257057 := bstep (se 2 (by rfl) ⟨1221396, by rfl⟩ : syracuseStep 3257057 = 2442793) B2442793
theorem B2171371 : Blo 2169435 2171371 := bstep (se 1 (by rfl) ⟨1628528, by rfl⟩ : syracuseStep 2171371 = 3257057) B3257057
theorem B7825781 : Blo 2169435 7825781 := bbase (se 5 (by rfl) ⟨366833, by rfl⟩ : syracuseStep 7825781 = 733667) (by norm_num)
theorem B20868749 : Blo 2169435 20868749 := bstep (se 3 (by rfl) ⟨3912890, by rfl⟩ : syracuseStep 20868749 = 7825781) B7825781
theorem B13912499 : Blo 2169435 13912499 := bstep (se 1 (by rfl) ⟨10434374, by rfl⟩ : syracuseStep 13912499 = 20868749) B20868749
theorem B9274999 : Blo 2169435 9274999 := bstep (se 1 (by rfl) ⟨6956249, by rfl⟩ : syracuseStep 9274999 = 13912499) B13912499
theorem B12366665 : Blo 2169435 12366665 := bstep (se 2 (by rfl) ⟨4637499, by rfl⟩ : syracuseStep 12366665 = 9274999) B9274999
theorem B8244443 : Blo 2169435 8244443 := bstep (se 1 (by rfl) ⟨6183332, by rfl⟩ : syracuseStep 8244443 = 12366665) B12366665
theorem B5496295 : Blo 2169435 5496295 := bstep (se 1 (by rfl) ⟨4122221, by rfl⟩ : syracuseStep 5496295 = 8244443) B8244443
theorem B7328393 : Blo 2169435 7328393 := bstep (se 2 (by rfl) ⟨2748147, by rfl⟩ : syracuseStep 7328393 = 5496295) B5496295
theorem B4885595 : Blo 2169435 4885595 := bstep (se 1 (by rfl) ⟨3664196, by rfl⟩ : syracuseStep 4885595 = 7328393) B7328393
theorem B3257063 : Blo 2169435 3257063 := bstep (se 1 (by rfl) ⟨2442797, by rfl⟩ : syracuseStep 3257063 = 4885595) B4885595
theorem B2171375 : Blo 2169435 2171375 := bstep (se 1 (by rfl) ⟨1628531, by rfl⟩ : syracuseStep 2171375 = 3257063) B3257063
theorem B3257069 : Blo 2169435 3257069 := bbase (se 3 (by rfl) ⟨610700, by rfl⟩ : syracuseStep 3257069 = 1221401) (by norm_num)
theorem B2171379 : Blo 2169435 2171379 := bstep (se 1 (by rfl) ⟨1628534, by rfl⟩ : syracuseStep 2171379 = 3257069) B3257069
theorem B4885613 : Blo 2169435 4885613 := bbase (se 3 (by rfl) ⟨916052, by rfl⟩ : syracuseStep 4885613 = 1832105) (by norm_num)
theorem B3257075 : Blo 2169435 3257075 := bstep (se 1 (by rfl) ⟨2442806, by rfl⟩ : syracuseStep 3257075 = 4885613) B4885613
theorem B2171383 : Blo 2169435 2171383 := bstep (se 1 (by rfl) ⟨1628537, by rfl⟩ : syracuseStep 2171383 = 3257075) B3257075
theorem B4122245 : Blo 2169435 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B2748163 : Blo 2169435 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B3664217 : Blo 2169435 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B2442811 : Blo 2169435 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B3257081 : Blo 2169435 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B2171387 : Blo 2169435 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B16713973 : Blo 2169435 16713973 := bbase (se 5 (by rfl) ⟨783467, by rfl⟩ : syracuseStep 16713973 = 1566935) (by norm_num)
theorem B22285297 : Blo 2169435 22285297 := bstep (se 2 (by rfl) ⟨8356986, by rfl⟩ : syracuseStep 22285297 = 16713973) B16713973
theorem B29713729 : Blo 2169435 29713729 := bstep (se 2 (by rfl) ⟨11142648, by rfl⟩ : syracuseStep 29713729 = 22285297) B22285297
theorem B39618305 : Blo 2169435 39618305 := bstep (se 2 (by rfl) ⟨14856864, by rfl⟩ : syracuseStep 39618305 = 29713729) B29713729
theorem B26412203 : Blo 2169435 26412203 := bstep (se 1 (by rfl) ⟨19809152, by rfl⟩ : syracuseStep 26412203 = 39618305) B39618305
theorem B70432541 : Blo 2169435 70432541 := bstep (se 3 (by rfl) ⟨13206101, by rfl⟩ : syracuseStep 70432541 = 26412203) B26412203
theorem B46955027 : Blo 2169435 46955027 := bstep (se 1 (by rfl) ⟨35216270, by rfl⟩ : syracuseStep 46955027 = 70432541) B70432541
theorem B31303351 : Blo 2169435 31303351 := bstep (se 1 (by rfl) ⟨23477513, by rfl⟩ : syracuseStep 31303351 = 46955027) B46955027
theorem B41737801 : Blo 2169435 41737801 := bstep (se 2 (by rfl) ⟨15651675, by rfl⟩ : syracuseStep 41737801 = 31303351) B31303351
theorem B55650401 : Blo 2169435 55650401 := bstep (se 2 (by rfl) ⟨20868900, by rfl⟩ : syracuseStep 55650401 = 41737801) B41737801
theorem B37100267 : Blo 2169435 37100267 := bstep (se 1 (by rfl) ⟨27825200, by rfl⟩ : syracuseStep 37100267 = 55650401) B55650401
theorem B24733511 : Blo 2169435 24733511 := bstep (se 1 (by rfl) ⟨18550133, by rfl⟩ : syracuseStep 24733511 = 37100267) B37100267
theorem B16489007 : Blo 2169435 16489007 := bstep (se 1 (by rfl) ⟨12366755, by rfl⟩ : syracuseStep 16489007 = 24733511) B24733511
theorem B10992671 : Blo 2169435 10992671 := bstep (se 1 (by rfl) ⟨8244503, by rfl⟩ : syracuseStep 10992671 = 16489007) B16489007
theorem B7328447 : Blo 2169435 7328447 := bstep (se 1 (by rfl) ⟨5496335, by rfl⟩ : syracuseStep 7328447 = 10992671) B10992671
theorem B4885631 : Blo 2169435 4885631 := bstep (se 1 (by rfl) ⟨3664223, by rfl⟩ : syracuseStep 4885631 = 7328447) B7328447
theorem B3257087 : Blo 2169435 3257087 := bstep (se 1 (by rfl) ⟨2442815, by rfl⟩ : syracuseStep 3257087 = 4885631) B4885631
theorem B2171391 : Blo 2169435 2171391 := bstep (se 1 (by rfl) ⟨1628543, by rfl⟩ : syracuseStep 2171391 = 3257087) B3257087
theorem B3257093 : Blo 2169435 3257093 := bbase (se 4 (by rfl) ⟨305352, by rfl⟩ : syracuseStep 3257093 = 610705) (by norm_num)
theorem B2171395 : Blo 2169435 2171395 := bstep (se 1 (by rfl) ⟨1628546, by rfl⟩ : syracuseStep 2171395 = 3257093) B3257093
theorem B3664237 : Blo 2169435 3664237 := bbase (se 3 (by rfl) ⟨687044, by rfl⟩ : syracuseStep 3664237 = 1374089) (by norm_num)
theorem B4885649 : Blo 2169435 4885649 := bstep (se 2 (by rfl) ⟨1832118, by rfl⟩ : syracuseStep 4885649 = 3664237) B3664237
theorem B3257099 : Blo 2169435 3257099 := bstep (se 1 (by rfl) ⟨2442824, by rfl⟩ : syracuseStep 3257099 = 4885649) B4885649
theorem B2171399 : Blo 2169435 2171399 := bstep (se 1 (by rfl) ⟨1628549, by rfl⟩ : syracuseStep 2171399 = 3257099) B3257099
theorem B2442829 : Blo 2169435 2442829 := bbase (se 3 (by rfl) ⟨458030, by rfl⟩ : syracuseStep 2442829 = 916061) (by norm_num)
theorem B3257105 : Blo 2169435 3257105 := bstep (se 2 (by rfl) ⟨1221414, by rfl⟩ : syracuseStep 3257105 = 2442829) B2442829
theorem B2171403 : Blo 2169435 2171403 := bstep (se 1 (by rfl) ⟨1628552, by rfl⟩ : syracuseStep 2171403 = 3257105) B3257105
theorem B7328501 : Blo 2169435 7328501 := bbase (se 5 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 7328501 = 687047) (by norm_num)
theorem B4885667 : Blo 2169435 4885667 := bstep (se 1 (by rfl) ⟨3664250, by rfl⟩ : syracuseStep 4885667 = 7328501) B7328501
theorem B3257111 : Blo 2169435 3257111 := bstep (se 1 (by rfl) ⟨2442833, by rfl⟩ : syracuseStep 3257111 = 4885667) B4885667
theorem B2171407 : Blo 2169435 2171407 := bstep (se 1 (by rfl) ⟨1628555, by rfl⟩ : syracuseStep 2171407 = 3257111) B3257111
theorem B3257117 : Blo 2169435 3257117 := bbase (se 3 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 3257117 = 1221419) (by norm_num)
theorem B2171411 : Blo 2169435 2171411 := bstep (se 1 (by rfl) ⟨1628558, by rfl⟩ : syracuseStep 2171411 = 3257117) B3257117
theorem B4885685 : Blo 2169435 4885685 := bbase (se 5 (by rfl) ⟨229016, by rfl⟩ : syracuseStep 4885685 = 458033) (by norm_num)
theorem B3257123 : Blo 2169435 3257123 := bstep (se 1 (by rfl) ⟨2442842, by rfl⟩ : syracuseStep 3257123 = 4885685) B4885685
theorem B2171415 : Blo 2169435 2171415 := bstep (se 1 (by rfl) ⟨1628561, by rfl⟩ : syracuseStep 2171415 = 3257123) B3257123
theorem B2318797 : Blo 2169435 2318797 := bbase (se 3 (by rfl) ⟨434774, by rfl⟩ : syracuseStep 2318797 = 869549) (by norm_num)
theorem B12366917 : Blo 2169435 12366917 := bstep (se 4 (by rfl) ⟨1159398, by rfl⟩ : syracuseStep 12366917 = 2318797) B2318797
theorem B8244611 : Blo 2169435 8244611 := bstep (se 1 (by rfl) ⟨6183458, by rfl⟩ : syracuseStep 8244611 = 12366917) B12366917
theorem B5496407 : Blo 2169435 5496407 := bstep (se 1 (by rfl) ⟨4122305, by rfl⟩ : syracuseStep 5496407 = 8244611) B8244611
theorem B3664271 : Blo 2169435 3664271 := bstep (se 1 (by rfl) ⟨2748203, by rfl⟩ : syracuseStep 3664271 = 5496407) B5496407
theorem B2442847 : Blo 2169435 2442847 := bstep (se 1 (by rfl) ⟨1832135, by rfl⟩ : syracuseStep 2442847 = 3664271) B3664271
theorem B3257129 : Blo 2169435 3257129 := bstep (se 2 (by rfl) ⟨1221423, by rfl⟩ : syracuseStep 3257129 = 2442847) B2442847
theorem B2171419 : Blo 2169435 2171419 := bstep (se 1 (by rfl) ⟨1628564, by rfl⟩ : syracuseStep 2171419 = 3257129) B3257129
theorem B2318801 : Blo 2169435 2318801 := bbase (se 2 (by rfl) ⟨869550, by rfl⟩ : syracuseStep 2318801 = 1739101) (by norm_num)
theorem B6183469 : Blo 2169435 6183469 := bstep (se 3 (by rfl) ⟨1159400, by rfl⟩ : syracuseStep 6183469 = 2318801) B2318801
theorem B8244625 : Blo 2169435 8244625 := bstep (se 2 (by rfl) ⟨3091734, by rfl⟩ : syracuseStep 8244625 = 6183469) B6183469
theorem B10992833 : Blo 2169435 10992833 := bstep (se 2 (by rfl) ⟨4122312, by rfl⟩ : syracuseStep 10992833 = 8244625) B8244625
theorem B7328555 : Blo 2169435 7328555 := bstep (se 1 (by rfl) ⟨5496416, by rfl⟩ : syracuseStep 7328555 = 10992833) B10992833
theorem B4885703 : Blo 2169435 4885703 := bstep (se 1 (by rfl) ⟨3664277, by rfl⟩ : syracuseStep 4885703 = 7328555) B7328555
theorem B3257135 : Blo 2169435 3257135 := bstep (se 1 (by rfl) ⟨2442851, by rfl⟩ : syracuseStep 3257135 = 4885703) B4885703
theorem B2171423 : Blo 2169435 2171423 := bstep (se 1 (by rfl) ⟨1628567, by rfl⟩ : syracuseStep 2171423 = 3257135) B3257135
theorem B3257141 : Blo 2169435 3257141 := bbase (se 5 (by rfl) ⟨152678, by rfl⟩ : syracuseStep 3257141 = 305357) (by norm_num)
theorem B2171427 : Blo 2169435 2171427 := bstep (se 1 (by rfl) ⟨1628570, by rfl⟩ : syracuseStep 2171427 = 3257141) B3257141
theorem B5496437 : Blo 2169435 5496437 := bbase (se 5 (by rfl) ⟨257645, by rfl⟩ : syracuseStep 5496437 = 515291) (by norm_num)
theorem B3664291 : Blo 2169435 3664291 := bstep (se 1 (by rfl) ⟨2748218, by rfl⟩ : syracuseStep 3664291 = 5496437) B5496437
theorem B4885721 : Blo 2169435 4885721 := bstep (se 2 (by rfl) ⟨1832145, by rfl⟩ : syracuseStep 4885721 = 3664291) B3664291
theorem B3257147 : Blo 2169435 3257147 := bstep (se 1 (by rfl) ⟨2442860, by rfl⟩ : syracuseStep 3257147 = 4885721) B4885721
theorem B2171431 : Blo 2169435 2171431 := bstep (se 1 (by rfl) ⟨1628573, by rfl⟩ : syracuseStep 2171431 = 3257147) B3257147
theorem B2442865 : Blo 2169435 2442865 := bbase (se 2 (by rfl) ⟨916074, by rfl⟩ : syracuseStep 2442865 = 1832149) (by norm_num)
theorem B3257153 : Blo 2169435 3257153 := bstep (se 2 (by rfl) ⟨1221432, by rfl⟩ : syracuseStep 3257153 = 2442865) B2442865
theorem B2171435 : Blo 2169435 2171435 := bstep (se 1 (by rfl) ⟨1628576, by rfl⟩ : syracuseStep 2171435 = 3257153) B3257153
theorem C0 (j : ℕ) (h1 : 542358 ≤ j) (h2 : j ≤ 542858) : Blo 2169435 (4 * j + 3) := by
  interval_cases j
  · exact B2169435
  · exact B2169439
  · exact B2169443
  · exact B2169447
  · exact B2169451
  · exact B2169455
  · exact B2169459
  · exact B2169463
  · exact B2169467
  · exact B2169471
  · exact B2169475
  · exact B2169479
  · exact B2169483
  · exact B2169487
  · exact B2169491
  · exact B2169495
  · exact B2169499
  · exact B2169503
  · exact B2169507
  · exact B2169511
  · exact B2169515
  · exact B2169519
  · exact B2169523
  · exact B2169527
  · exact B2169531
  · exact B2169535
  · exact B2169539
  · exact B2169543
  · exact B2169547
  · exact B2169551
  · exact B2169555
  · exact B2169559
  · exact B2169563
  · exact B2169567
  · exact B2169571
  · exact B2169575
  · exact B2169579
  · exact B2169583
  · exact B2169587
  · exact B2169591
  · exact B2169595
  · exact B2169599
  · exact B2169603
  · exact B2169607
  · exact B2169611
  · exact B2169615
  · exact B2169619
  · exact B2169623
  · exact B2169627
  · exact B2169631
  · exact B2169635
  · exact B2169639
  · exact B2169643
  · exact B2169647
  · exact B2169651
  · exact B2169655
  · exact B2169659
  · exact B2169663
  · exact B2169667
  · exact B2169671
  · exact B2169675
  · exact B2169679
  · exact B2169683
  · exact B2169687
  · exact B2169691
  · exact B2169695
  · exact B2169699
  · exact B2169703
  · exact B2169707
  · exact B2169711
  · exact B2169715
  · exact B2169719
  · exact B2169723
  · exact B2169727
  · exact B2169731
  · exact B2169735
  · exact B2169739
  · exact B2169743
  · exact B2169747
  · exact B2169751
  · exact B2169755
  · exact B2169759
  · exact B2169763
  · exact B2169767
  · exact B2169771
  · exact B2169775
  · exact B2169779
  · exact B2169783
  · exact B2169787
  · exact B2169791
  · exact B2169795
  · exact B2169799
  · exact B2169803
  · exact B2169807
  · exact B2169811
  · exact B2169815
  · exact B2169819
  · exact B2169823
  · exact B2169827
  · exact B2169831
  · exact B2169835
  · exact B2169839
  · exact B2169843
  · exact B2169847
  · exact B2169851
  · exact B2169855
  · exact B2169859
  · exact B2169863
  · exact B2169867
  · exact B2169871
  · exact B2169875
  · exact B2169879
  · exact B2169883
  · exact B2169887
  · exact B2169891
  · exact B2169895
  · exact B2169899
  · exact B2169903
  · exact B2169907
  · exact B2169911
  · exact B2169915
  · exact B2169919
  · exact B2169923
  · exact B2169927
  · exact B2169931
  · exact B2169935
  · exact B2169939
  · exact B2169943
  · exact B2169947
  · exact B2169951
  · exact B2169955
  · exact B2169959
  · exact B2169963
  · exact B2169967
  · exact B2169971
  · exact B2169975
  · exact B2169979
  · exact B2169983
  · exact B2169987
  · exact B2169991
  · exact B2169995
  · exact B2169999
  · exact B2170003
  · exact B2170007
  · exact B2170011
  · exact B2170015
  · exact B2170019
  · exact B2170023
  · exact B2170027
  · exact B2170031
  · exact B2170035
  · exact B2170039
  · exact B2170043
  · exact B2170047
  · exact B2170051
  · exact B2170055
  · exact B2170059
  · exact B2170063
  · exact B2170067
  · exact B2170071
  · exact B2170075
  · exact B2170079
  · exact B2170083
  · exact B2170087
  · exact B2170091
  · exact B2170095
  · exact B2170099
  · exact B2170103
  · exact B2170107
  · exact B2170111
  · exact B2170115
  · exact B2170119
  · exact B2170123
  · exact B2170127
  · exact B2170131
  · exact B2170135
  · exact B2170139
  · exact B2170143
  · exact B2170147
  · exact B2170151
  · exact B2170155
  · exact B2170159
  · exact B2170163
  · exact B2170167
  · exact B2170171
  · exact B2170175
  · exact B2170179
  · exact B2170183
  · exact B2170187
  · exact B2170191
  · exact B2170195
  · exact B2170199
  · exact B2170203
  · exact B2170207
  · exact B2170211
  · exact B2170215
  · exact B2170219
  · exact B2170223
  · exact B2170227
  · exact B2170231
  · exact B2170235
  · exact B2170239
  · exact B2170243
  · exact B2170247
  · exact B2170251
  · exact B2170255
  · exact B2170259
  · exact B2170263
  · exact B2170267
  · exact B2170271
  · exact B2170275
  · exact B2170279
  · exact B2170283
  · exact B2170287
  · exact B2170291
  · exact B2170295
  · exact B2170299
  · exact B2170303
  · exact B2170307
  · exact B2170311
  · exact B2170315
  · exact B2170319
  · exact B2170323
  · exact B2170327
  · exact B2170331
  · exact B2170335
  · exact B2170339
  · exact B2170343
  · exact B2170347
  · exact B2170351
  · exact B2170355
  · exact B2170359
  · exact B2170363
  · exact B2170367
  · exact B2170371
  · exact B2170375
  · exact B2170379
  · exact B2170383
  · exact B2170387
  · exact B2170391
  · exact B2170395
  · exact B2170399
  · exact B2170403
  · exact B2170407
  · exact B2170411
  · exact B2170415
  · exact B2170419
  · exact B2170423
  · exact B2170427
  · exact B2170431
  · exact B2170435
  · exact B2170439
  · exact B2170443
  · exact B2170447
  · exact B2170451
  · exact B2170455
  · exact B2170459
  · exact B2170463
  · exact B2170467
  · exact B2170471
  · exact B2170475
  · exact B2170479
  · exact B2170483
  · exact B2170487
  · exact B2170491
  · exact B2170495
  · exact B2170499
  · exact B2170503
  · exact B2170507
  · exact B2170511
  · exact B2170515
  · exact B2170519
  · exact B2170523
  · exact B2170527
  · exact B2170531
  · exact B2170535
  · exact B2170539
  · exact B2170543
  · exact B2170547
  · exact B2170551
  · exact B2170555
  · exact B2170559
  · exact B2170563
  · exact B2170567
  · exact B2170571
  · exact B2170575
  · exact B2170579
  · exact B2170583
  · exact B2170587
  · exact B2170591
  · exact B2170595
  · exact B2170599
  · exact B2170603
  · exact B2170607
  · exact B2170611
  · exact B2170615
  · exact B2170619
  · exact B2170623
  · exact B2170627
  · exact B2170631
  · exact B2170635
  · exact B2170639
  · exact B2170643
  · exact B2170647
  · exact B2170651
  · exact B2170655
  · exact B2170659
  · exact B2170663
  · exact B2170667
  · exact B2170671
  · exact B2170675
  · exact B2170679
  · exact B2170683
  · exact B2170687
  · exact B2170691
  · exact B2170695
  · exact B2170699
  · exact B2170703
  · exact B2170707
  · exact B2170711
  · exact B2170715
  · exact B2170719
  · exact B2170723
  · exact B2170727
  · exact B2170731
  · exact B2170735
  · exact B2170739
  · exact B2170743
  · exact B2170747
  · exact B2170751
  · exact B2170755
  · exact B2170759
  · exact B2170763
  · exact B2170767
  · exact B2170771
  · exact B2170775
  · exact B2170779
  · exact B2170783
  · exact B2170787
  · exact B2170791
  · exact B2170795
  · exact B2170799
  · exact B2170803
  · exact B2170807
  · exact B2170811
  · exact B2170815
  · exact B2170819
  · exact B2170823
  · exact B2170827
  · exact B2170831
  · exact B2170835
  · exact B2170839
  · exact B2170843
  · exact B2170847
  · exact B2170851
  · exact B2170855
  · exact B2170859
  · exact B2170863
  · exact B2170867
  · exact B2170871
  · exact B2170875
  · exact B2170879
  · exact B2170883
  · exact B2170887
  · exact B2170891
  · exact B2170895
  · exact B2170899
  · exact B2170903
  · exact B2170907
  · exact B2170911
  · exact B2170915
  · exact B2170919
  · exact B2170923
  · exact B2170927
  · exact B2170931
  · exact B2170935
  · exact B2170939
  · exact B2170943
  · exact B2170947
  · exact B2170951
  · exact B2170955
  · exact B2170959
  · exact B2170963
  · exact B2170967
  · exact B2170971
  · exact B2170975
  · exact B2170979
  · exact B2170983
  · exact B2170987
  · exact B2170991
  · exact B2170995
  · exact B2170999
  · exact B2171003
  · exact B2171007
  · exact B2171011
  · exact B2171015
  · exact B2171019
  · exact B2171023
  · exact B2171027
  · exact B2171031
  · exact B2171035
  · exact B2171039
  · exact B2171043
  · exact B2171047
  · exact B2171051
  · exact B2171055
  · exact B2171059
  · exact B2171063
  · exact B2171067
  · exact B2171071
  · exact B2171075
  · exact B2171079
  · exact B2171083
  · exact B2171087
  · exact B2171091
  · exact B2171095
  · exact B2171099
  · exact B2171103
  · exact B2171107
  · exact B2171111
  · exact B2171115
  · exact B2171119
  · exact B2171123
  · exact B2171127
  · exact B2171131
  · exact B2171135
  · exact B2171139
  · exact B2171143
  · exact B2171147
  · exact B2171151
  · exact B2171155
  · exact B2171159
  · exact B2171163
  · exact B2171167
  · exact B2171171
  · exact B2171175
  · exact B2171179
  · exact B2171183
  · exact B2171187
  · exact B2171191
  · exact B2171195
  · exact B2171199
  · exact B2171203
  · exact B2171207
  · exact B2171211
  · exact B2171215
  · exact B2171219
  · exact B2171223
  · exact B2171227
  · exact B2171231
  · exact B2171235
  · exact B2171239
  · exact B2171243
  · exact B2171247
  · exact B2171251
  · exact B2171255
  · exact B2171259
  · exact B2171263
  · exact B2171267
  · exact B2171271
  · exact B2171275
  · exact B2171279
  · exact B2171283
  · exact B2171287
  · exact B2171291
  · exact B2171295
  · exact B2171299
  · exact B2171303
  · exact B2171307
  · exact B2171311
  · exact B2171315
  · exact B2171319
  · exact B2171323
  · exact B2171327
  · exact B2171331
  · exact B2171335
  · exact B2171339
  · exact B2171343
  · exact B2171347
  · exact B2171351
  · exact B2171355
  · exact B2171359
  · exact B2171363
  · exact B2171367
  · exact B2171371
  · exact B2171375
  · exact B2171379
  · exact B2171383
  · exact B2171387
  · exact B2171391
  · exact B2171395
  · exact B2171399
  · exact B2171403
  · exact B2171407
  · exact B2171411
  · exact B2171415
  · exact B2171419
  · exact B2171423
  · exact B2171427
  · exact B2171431
  · exact B2171435
theorem solution (m : ℕ) (hlo : 2169435 ≤ m) (hhi : m ≤ 2171435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 542358 ≤ j := by omega
    have hj2 : j ≤ 542858 := by omega
    have hb : Blo 2169435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
