-- Prove2me | solution 1 for syracuse_descends_range_2285435_2287435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:49:41.874395+00:00
-- url     : https://prove2.me/submissions/c6cde37f-70a0-4e47-b847-7fac8bc192bd

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

theorem B2892505 : Blo 2285435 2892505 := bbase (se 2 (by rfl) ⟨1084689, by rfl⟩ : syracuseStep 2892505 = 2169379) (by norm_num)
theorem B3856673 : Blo 2285435 3856673 := bstep (se 2 (by rfl) ⟨1446252, by rfl⟩ : syracuseStep 3856673 = 2892505) B2892505
theorem B2571115 : Blo 2285435 2571115 := bstep (se 1 (by rfl) ⟨1928336, by rfl⟩ : syracuseStep 2571115 = 3856673) B3856673
theorem B3428153 : Blo 2285435 3428153 := bstep (se 2 (by rfl) ⟨1285557, by rfl⟩ : syracuseStep 3428153 = 2571115) B2571115
theorem B2285435 : Blo 2285435 2285435 := bstep (se 1 (by rfl) ⟨1714076, by rfl⟩ : syracuseStep 2285435 = 3428153) B3428153
theorem B2745625 : Blo 2285435 2745625 := bbase (se 2 (by rfl) ⟨1029609, by rfl⟩ : syracuseStep 2745625 = 2059219) (by norm_num)
theorem B3660833 : Blo 2285435 3660833 := bstep (se 2 (by rfl) ⟨1372812, by rfl⟩ : syracuseStep 3660833 = 2745625) B2745625
theorem B9762221 : Blo 2285435 9762221 := bstep (se 3 (by rfl) ⟨1830416, by rfl⟩ : syracuseStep 9762221 = 3660833) B3660833
theorem B26032589 : Blo 2285435 26032589 := bstep (se 3 (by rfl) ⟨4881110, by rfl⟩ : syracuseStep 26032589 = 9762221) B9762221
theorem B17355059 : Blo 2285435 17355059 := bstep (se 1 (by rfl) ⟨13016294, by rfl⟩ : syracuseStep 17355059 = 26032589) B26032589
theorem B11570039 : Blo 2285435 11570039 := bstep (se 1 (by rfl) ⟨8677529, by rfl⟩ : syracuseStep 11570039 = 17355059) B17355059
theorem B7713359 : Blo 2285435 7713359 := bstep (se 1 (by rfl) ⟨5785019, by rfl⟩ : syracuseStep 7713359 = 11570039) B11570039
theorem B5142239 : Blo 2285435 5142239 := bstep (se 1 (by rfl) ⟨3856679, by rfl⟩ : syracuseStep 5142239 = 7713359) B7713359
theorem B3428159 : Blo 2285435 3428159 := bstep (se 1 (by rfl) ⟨2571119, by rfl⟩ : syracuseStep 3428159 = 5142239) B5142239
theorem B2285439 : Blo 2285435 2285439 := bstep (se 1 (by rfl) ⟨1714079, by rfl⟩ : syracuseStep 2285439 = 3428159) B3428159
theorem B3428165 : Blo 2285435 3428165 := bbase (se 4 (by rfl) ⟨321390, by rfl⟩ : syracuseStep 3428165 = 642781) (by norm_num)
theorem B2285443 : Blo 2285435 2285443 := bstep (se 1 (by rfl) ⟨1714082, by rfl⟩ : syracuseStep 2285443 = 3428165) B3428165
theorem B3856693 : Blo 2285435 3856693 := bbase (se 5 (by rfl) ⟨180782, by rfl⟩ : syracuseStep 3856693 = 361565) (by norm_num)
theorem B5142257 : Blo 2285435 5142257 := bstep (se 2 (by rfl) ⟨1928346, by rfl⟩ : syracuseStep 5142257 = 3856693) B3856693
theorem B3428171 : Blo 2285435 3428171 := bstep (se 1 (by rfl) ⟨2571128, by rfl⟩ : syracuseStep 3428171 = 5142257) B5142257
theorem B2285447 : Blo 2285435 2285447 := bstep (se 1 (by rfl) ⟨1714085, by rfl⟩ : syracuseStep 2285447 = 3428171) B3428171
theorem B2571133 : Blo 2285435 2571133 := bbase (se 3 (by rfl) ⟨482087, by rfl⟩ : syracuseStep 2571133 = 964175) (by norm_num)
theorem B3428177 : Blo 2285435 3428177 := bstep (se 2 (by rfl) ⟨1285566, by rfl⟩ : syracuseStep 3428177 = 2571133) B2571133
theorem B2285451 : Blo 2285435 2285451 := bstep (se 1 (by rfl) ⟨1714088, by rfl⟩ : syracuseStep 2285451 = 3428177) B3428177
theorem B7713413 : Blo 2285435 7713413 := bbase (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) (by norm_num)
theorem B5142275 : Blo 2285435 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B3428183 : Blo 2285435 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B2285455 : Blo 2285435 2285455 := bstep (se 1 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 2285455 = 3428183) B3428183
theorem B3428189 : Blo 2285435 3428189 := bbase (se 3 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 3428189 = 1285571) (by norm_num)
theorem B2285459 : Blo 2285435 2285459 := bstep (se 1 (by rfl) ⟨1714094, by rfl⟩ : syracuseStep 2285459 = 3428189) B3428189
theorem B5142293 : Blo 2285435 5142293 := bbase (se 6 (by rfl) ⟨120522, by rfl⟩ : syracuseStep 5142293 = 241045) (by norm_num)
theorem B3428195 : Blo 2285435 3428195 := bstep (se 1 (by rfl) ⟨2571146, by rfl⟩ : syracuseStep 3428195 = 5142293) B5142293
theorem B2285463 : Blo 2285435 2285463 := bstep (se 1 (by rfl) ⟨1714097, by rfl⟩ : syracuseStep 2285463 = 3428195) B3428195
theorem B8677637 : Blo 2285435 8677637 := bbase (se 4 (by rfl) ⟨813528, by rfl⟩ : syracuseStep 8677637 = 1627057) (by norm_num)
theorem B5785091 : Blo 2285435 5785091 := bstep (se 1 (by rfl) ⟨4338818, by rfl⟩ : syracuseStep 5785091 = 8677637) B8677637
theorem B3856727 : Blo 2285435 3856727 := bstep (se 1 (by rfl) ⟨2892545, by rfl⟩ : syracuseStep 3856727 = 5785091) B5785091
theorem B2571151 : Blo 2285435 2571151 := bstep (se 1 (by rfl) ⟨1928363, by rfl⟩ : syracuseStep 2571151 = 3856727) B3856727
theorem B3428201 : Blo 2285435 3428201 := bstep (se 2 (by rfl) ⟨1285575, by rfl⟩ : syracuseStep 3428201 = 2571151) B2571151
theorem B2285467 : Blo 2285435 2285467 := bstep (se 1 (by rfl) ⟨1714100, by rfl⟩ : syracuseStep 2285467 = 3428201) B3428201
theorem B6870757 : Blo 2285435 6870757 := bbase (se 4 (by rfl) ⟨644133, by rfl⟩ : syracuseStep 6870757 = 1288267) (by norm_num)
theorem B9161009 : Blo 2285435 9161009 := bstep (se 2 (by rfl) ⟨3435378, by rfl⟩ : syracuseStep 9161009 = 6870757) B6870757
theorem B6107339 : Blo 2285435 6107339 := bstep (se 1 (by rfl) ⟨4580504, by rfl⟩ : syracuseStep 6107339 = 9161009) B9161009
theorem B4071559 : Blo 2285435 4071559 := bstep (se 1 (by rfl) ⟨3053669, by rfl⟩ : syracuseStep 4071559 = 6107339) B6107339
theorem B5428745 : Blo 2285435 5428745 := bstep (se 2 (by rfl) ⟨2035779, by rfl⟩ : syracuseStep 5428745 = 4071559) B4071559
theorem B3619163 : Blo 2285435 3619163 := bstep (se 1 (by rfl) ⟨2714372, by rfl⟩ : syracuseStep 3619163 = 5428745) B5428745
theorem B2412775 : Blo 2285435 2412775 := bstep (se 1 (by rfl) ⟨1809581, by rfl⟩ : syracuseStep 2412775 = 3619163) B3619163
theorem B3217033 : Blo 2285435 3217033 := bstep (se 2 (by rfl) ⟨1206387, by rfl⟩ : syracuseStep 3217033 = 2412775) B2412775
theorem B4289377 : Blo 2285435 4289377 := bstep (se 2 (by rfl) ⟨1608516, by rfl⟩ : syracuseStep 4289377 = 3217033) B3217033
theorem B5719169 : Blo 2285435 5719169 := bstep (se 2 (by rfl) ⟨2144688, by rfl⟩ : syracuseStep 5719169 = 4289377) B4289377
theorem B3812779 : Blo 2285435 3812779 := bstep (se 1 (by rfl) ⟨2859584, by rfl⟩ : syracuseStep 3812779 = 5719169) B5719169
theorem B5083705 : Blo 2285435 5083705 := bstep (se 2 (by rfl) ⟨1906389, by rfl⟩ : syracuseStep 5083705 = 3812779) B3812779
theorem B6778273 : Blo 2285435 6778273 := bstep (se 2 (by rfl) ⟨2541852, by rfl⟩ : syracuseStep 6778273 = 5083705) B5083705
theorem B144603157 : Blo 2285435 144603157 := bstep (se 6 (by rfl) ⟨3389136, by rfl⟩ : syracuseStep 144603157 = 6778273) B6778273
theorem B192804209 : Blo 2285435 192804209 := bstep (se 2 (by rfl) ⟨72301578, by rfl⟩ : syracuseStep 192804209 = 144603157) B144603157
theorem B128536139 : Blo 2285435 128536139 := bstep (se 1 (by rfl) ⟨96402104, by rfl⟩ : syracuseStep 128536139 = 192804209) B192804209
theorem B85690759 : Blo 2285435 85690759 := bstep (se 1 (by rfl) ⟨64268069, by rfl⟩ : syracuseStep 85690759 = 128536139) B128536139
theorem B114254345 : Blo 2285435 114254345 := bstep (se 2 (by rfl) ⟨42845379, by rfl⟩ : syracuseStep 114254345 = 85690759) B85690759
theorem B304678253 : Blo 2285435 304678253 := bstep (se 3 (by rfl) ⟨57127172, by rfl⟩ : syracuseStep 304678253 = 114254345) B114254345
theorem B203118835 : Blo 2285435 203118835 := bstep (se 1 (by rfl) ⟨152339126, by rfl⟩ : syracuseStep 203118835 = 304678253) B304678253
theorem B270825113 : Blo 2285435 270825113 := bstep (se 2 (by rfl) ⟨101559417, by rfl⟩ : syracuseStep 270825113 = 203118835) B203118835
theorem B180550075 : Blo 2285435 180550075 := bstep (se 1 (by rfl) ⟨135412556, by rfl⟩ : syracuseStep 180550075 = 270825113) B270825113
theorem B240733433 : Blo 2285435 240733433 := bstep (se 2 (by rfl) ⟨90275037, by rfl⟩ : syracuseStep 240733433 = 180550075) B180550075
theorem B160488955 : Blo 2285435 160488955 := bstep (se 1 (by rfl) ⟨120366716, by rfl⟩ : syracuseStep 160488955 = 240733433) B240733433
theorem B213985273 : Blo 2285435 213985273 := bstep (se 2 (by rfl) ⟨80244477, by rfl⟩ : syracuseStep 213985273 = 160488955) B160488955
theorem B285313697 : Blo 2285435 285313697 := bstep (se 2 (by rfl) ⟨106992636, by rfl⟩ : syracuseStep 285313697 = 213985273) B213985273
theorem B190209131 : Blo 2285435 190209131 := bstep (se 1 (by rfl) ⟨142656848, by rfl⟩ : syracuseStep 190209131 = 285313697) B285313697
theorem B126806087 : Blo 2285435 126806087 := bstep (se 1 (by rfl) ⟨95104565, by rfl⟩ : syracuseStep 126806087 = 190209131) B190209131
theorem B338149565 : Blo 2285435 338149565 := bstep (se 3 (by rfl) ⟨63403043, by rfl⟩ : syracuseStep 338149565 = 126806087) B126806087
theorem B225433043 : Blo 2285435 225433043 := bstep (se 1 (by rfl) ⟨169074782, by rfl⟩ : syracuseStep 225433043 = 338149565) B338149565
theorem B150288695 : Blo 2285435 150288695 := bstep (se 1 (by rfl) ⟨112716521, by rfl⟩ : syracuseStep 150288695 = 225433043) B225433043
theorem B100192463 : Blo 2285435 100192463 := bstep (se 1 (by rfl) ⟨75144347, by rfl⟩ : syracuseStep 100192463 = 150288695) B150288695
theorem B66794975 : Blo 2285435 66794975 := bstep (se 1 (by rfl) ⟨50096231, by rfl⟩ : syracuseStep 66794975 = 100192463) B100192463
theorem B44529983 : Blo 2285435 44529983 := bstep (se 1 (by rfl) ⟨33397487, by rfl⟩ : syracuseStep 44529983 = 66794975) B66794975
theorem B29686655 : Blo 2285435 29686655 := bstep (se 1 (by rfl) ⟨22264991, by rfl⟩ : syracuseStep 29686655 = 44529983) B44529983
theorem B19791103 : Blo 2285435 19791103 := bstep (se 1 (by rfl) ⟨14843327, by rfl⟩ : syracuseStep 19791103 = 29686655) B29686655
theorem B26388137 : Blo 2285435 26388137 := bstep (se 2 (by rfl) ⟨9895551, by rfl⟩ : syracuseStep 26388137 = 19791103) B19791103
theorem B70368365 : Blo 2285435 70368365 := bstep (se 3 (by rfl) ⟨13194068, by rfl⟩ : syracuseStep 70368365 = 26388137) B26388137
theorem B46912243 : Blo 2285435 46912243 := bstep (se 1 (by rfl) ⟨35184182, by rfl⟩ : syracuseStep 46912243 = 70368365) B70368365
theorem B62549657 : Blo 2285435 62549657 := bstep (se 2 (by rfl) ⟨23456121, by rfl⟩ : syracuseStep 62549657 = 46912243) B46912243
theorem B41699771 : Blo 2285435 41699771 := bstep (se 1 (by rfl) ⟨31274828, by rfl⟩ : syracuseStep 41699771 = 62549657) B62549657
theorem B27799847 : Blo 2285435 27799847 := bstep (se 1 (by rfl) ⟨20849885, by rfl⟩ : syracuseStep 27799847 = 41699771) B41699771
theorem B18533231 : Blo 2285435 18533231 := bstep (se 1 (by rfl) ⟨13899923, by rfl⟩ : syracuseStep 18533231 = 27799847) B27799847
theorem B12355487 : Blo 2285435 12355487 := bstep (se 1 (by rfl) ⟨9266615, by rfl⟩ : syracuseStep 12355487 = 18533231) B18533231
theorem B8236991 : Blo 2285435 8236991 := bstep (se 1 (by rfl) ⟨6177743, by rfl⟩ : syracuseStep 8236991 = 12355487) B12355487
theorem B5491327 : Blo 2285435 5491327 := bstep (se 1 (by rfl) ⟨4118495, by rfl⟩ : syracuseStep 5491327 = 8236991) B8236991
theorem B7321769 : Blo 2285435 7321769 := bstep (se 2 (by rfl) ⟨2745663, by rfl⟩ : syracuseStep 7321769 = 5491327) B5491327
theorem B4881179 : Blo 2285435 4881179 := bstep (se 1 (by rfl) ⟨3660884, by rfl⟩ : syracuseStep 4881179 = 7321769) B7321769
theorem B13016477 : Blo 2285435 13016477 := bstep (se 3 (by rfl) ⟨2440589, by rfl⟩ : syracuseStep 13016477 = 4881179) B4881179
theorem B8677651 : Blo 2285435 8677651 := bstep (se 1 (by rfl) ⟨6508238, by rfl⟩ : syracuseStep 8677651 = 13016477) B13016477
theorem B11570201 : Blo 2285435 11570201 := bstep (se 2 (by rfl) ⟨4338825, by rfl⟩ : syracuseStep 11570201 = 8677651) B8677651
theorem B7713467 : Blo 2285435 7713467 := bstep (se 1 (by rfl) ⟨5785100, by rfl⟩ : syracuseStep 7713467 = 11570201) B11570201
theorem B5142311 : Blo 2285435 5142311 := bstep (se 1 (by rfl) ⟨3856733, by rfl⟩ : syracuseStep 5142311 = 7713467) B7713467
theorem B3428207 : Blo 2285435 3428207 := bstep (se 1 (by rfl) ⟨2571155, by rfl⟩ : syracuseStep 3428207 = 5142311) B5142311
theorem B2285471 : Blo 2285435 2285471 := bstep (se 1 (by rfl) ⟨1714103, by rfl⟩ : syracuseStep 2285471 = 3428207) B3428207
theorem B3428213 : Blo 2285435 3428213 := bbase (se 5 (by rfl) ⟨160697, by rfl⟩ : syracuseStep 3428213 = 321395) (by norm_num)
theorem B2285475 : Blo 2285435 2285475 := bstep (se 1 (by rfl) ⟨1714106, by rfl⟩ : syracuseStep 2285475 = 3428213) B3428213
theorem B4881197 : Blo 2285435 4881197 := bbase (se 3 (by rfl) ⟨915224, by rfl⟩ : syracuseStep 4881197 = 1830449) (by norm_num)
theorem B3254131 : Blo 2285435 3254131 := bstep (se 1 (by rfl) ⟨2440598, by rfl⟩ : syracuseStep 3254131 = 4881197) B4881197
theorem B4338841 : Blo 2285435 4338841 := bstep (se 2 (by rfl) ⟨1627065, by rfl⟩ : syracuseStep 4338841 = 3254131) B3254131
theorem B5785121 : Blo 2285435 5785121 := bstep (se 2 (by rfl) ⟨2169420, by rfl⟩ : syracuseStep 5785121 = 4338841) B4338841
theorem B3856747 : Blo 2285435 3856747 := bstep (se 1 (by rfl) ⟨2892560, by rfl⟩ : syracuseStep 3856747 = 5785121) B5785121
theorem B5142329 : Blo 2285435 5142329 := bstep (se 2 (by rfl) ⟨1928373, by rfl⟩ : syracuseStep 5142329 = 3856747) B3856747
theorem B3428219 : Blo 2285435 3428219 := bstep (se 1 (by rfl) ⟨2571164, by rfl⟩ : syracuseStep 3428219 = 5142329) B5142329
theorem B2285479 : Blo 2285435 2285479 := bstep (se 1 (by rfl) ⟨1714109, by rfl⟩ : syracuseStep 2285479 = 3428219) B3428219
theorem B2571169 : Blo 2285435 2571169 := bbase (se 2 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 2571169 = 1928377) (by norm_num)
theorem B3428225 : Blo 2285435 3428225 := bstep (se 2 (by rfl) ⟨1285584, by rfl⟩ : syracuseStep 3428225 = 2571169) B2571169
theorem B2285483 : Blo 2285435 2285483 := bstep (se 1 (by rfl) ⟨1714112, by rfl⟩ : syracuseStep 2285483 = 3428225) B3428225
theorem B5785141 : Blo 2285435 5785141 := bbase (se 5 (by rfl) ⟨271178, by rfl⟩ : syracuseStep 5785141 = 542357) (by norm_num)
theorem B7713521 : Blo 2285435 7713521 := bstep (se 2 (by rfl) ⟨2892570, by rfl⟩ : syracuseStep 7713521 = 5785141) B5785141
theorem B5142347 : Blo 2285435 5142347 := bstep (se 1 (by rfl) ⟨3856760, by rfl⟩ : syracuseStep 5142347 = 7713521) B7713521
theorem B3428231 : Blo 2285435 3428231 := bstep (se 1 (by rfl) ⟨2571173, by rfl⟩ : syracuseStep 3428231 = 5142347) B5142347
theorem B2285487 : Blo 2285435 2285487 := bstep (se 1 (by rfl) ⟨1714115, by rfl⟩ : syracuseStep 2285487 = 3428231) B3428231
theorem B3428237 : Blo 2285435 3428237 := bbase (se 3 (by rfl) ⟨642794, by rfl⟩ : syracuseStep 3428237 = 1285589) (by norm_num)
theorem B2285491 : Blo 2285435 2285491 := bstep (se 1 (by rfl) ⟨1714118, by rfl⟩ : syracuseStep 2285491 = 3428237) B3428237
theorem B5142365 : Blo 2285435 5142365 := bbase (se 3 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 5142365 = 1928387) (by norm_num)
theorem B3428243 : Blo 2285435 3428243 := bstep (se 1 (by rfl) ⟨2571182, by rfl⟩ : syracuseStep 3428243 = 5142365) B5142365
theorem B2285495 : Blo 2285435 2285495 := bstep (se 1 (by rfl) ⟨1714121, by rfl⟩ : syracuseStep 2285495 = 3428243) B3428243
theorem B3856781 : Blo 2285435 3856781 := bbase (se 3 (by rfl) ⟨723146, by rfl⟩ : syracuseStep 3856781 = 1446293) (by norm_num)
theorem B2571187 : Blo 2285435 2571187 := bstep (se 1 (by rfl) ⟨1928390, by rfl⟩ : syracuseStep 2571187 = 3856781) B3856781
theorem B3428249 : Blo 2285435 3428249 := bstep (se 2 (by rfl) ⟨1285593, by rfl⟩ : syracuseStep 3428249 = 2571187) B2571187
theorem B2285499 : Blo 2285435 2285499 := bstep (se 1 (by rfl) ⟨1714124, by rfl⟩ : syracuseStep 2285499 = 3428249) B3428249
theorem B24711317 : Blo 2285435 24711317 := bbase (se 6 (by rfl) ⟨579171, by rfl⟩ : syracuseStep 24711317 = 1158343) (by norm_num)
theorem B16474211 : Blo 2285435 16474211 := bstep (se 1 (by rfl) ⟨12355658, by rfl⟩ : syracuseStep 16474211 = 24711317) B24711317
theorem B10982807 : Blo 2285435 10982807 := bstep (se 1 (by rfl) ⟨8237105, by rfl⟩ : syracuseStep 10982807 = 16474211) B16474211
theorem B7321871 : Blo 2285435 7321871 := bstep (se 1 (by rfl) ⟨5491403, by rfl⟩ : syracuseStep 7321871 = 10982807) B10982807
theorem B19524989 : Blo 2285435 19524989 := bstep (se 3 (by rfl) ⟨3660935, by rfl⟩ : syracuseStep 19524989 = 7321871) B7321871
theorem B13016659 : Blo 2285435 13016659 := bstep (se 1 (by rfl) ⟨9762494, by rfl⟩ : syracuseStep 13016659 = 19524989) B19524989
theorem B17355545 : Blo 2285435 17355545 := bstep (se 2 (by rfl) ⟨6508329, by rfl⟩ : syracuseStep 17355545 = 13016659) B13016659
theorem B11570363 : Blo 2285435 11570363 := bstep (se 1 (by rfl) ⟨8677772, by rfl⟩ : syracuseStep 11570363 = 17355545) B17355545
theorem B7713575 : Blo 2285435 7713575 := bstep (se 1 (by rfl) ⟨5785181, by rfl⟩ : syracuseStep 7713575 = 11570363) B11570363
theorem B5142383 : Blo 2285435 5142383 := bstep (se 1 (by rfl) ⟨3856787, by rfl⟩ : syracuseStep 5142383 = 7713575) B7713575
theorem B3428255 : Blo 2285435 3428255 := bstep (se 1 (by rfl) ⟨2571191, by rfl⟩ : syracuseStep 3428255 = 5142383) B5142383
theorem B2285503 : Blo 2285435 2285503 := bstep (se 1 (by rfl) ⟨1714127, by rfl⟩ : syracuseStep 2285503 = 3428255) B3428255
theorem B3428261 : Blo 2285435 3428261 := bbase (se 4 (by rfl) ⟨321399, by rfl⟩ : syracuseStep 3428261 = 642799) (by norm_num)
theorem B2285507 : Blo 2285435 2285507 := bstep (se 1 (by rfl) ⟨1714130, by rfl⟩ : syracuseStep 2285507 = 3428261) B3428261
theorem B2892601 : Blo 2285435 2892601 := bbase (se 2 (by rfl) ⟨1084725, by rfl⟩ : syracuseStep 2892601 = 2169451) (by norm_num)
theorem B3856801 : Blo 2285435 3856801 := bstep (se 2 (by rfl) ⟨1446300, by rfl⟩ : syracuseStep 3856801 = 2892601) B2892601
theorem B5142401 : Blo 2285435 5142401 := bstep (se 2 (by rfl) ⟨1928400, by rfl⟩ : syracuseStep 5142401 = 3856801) B3856801
theorem B3428267 : Blo 2285435 3428267 := bstep (se 1 (by rfl) ⟨2571200, by rfl⟩ : syracuseStep 3428267 = 5142401) B5142401
theorem B2285511 : Blo 2285435 2285511 := bstep (se 1 (by rfl) ⟨1714133, by rfl⟩ : syracuseStep 2285511 = 3428267) B3428267
theorem B2571205 : Blo 2285435 2571205 := bbase (se 4 (by rfl) ⟨241050, by rfl⟩ : syracuseStep 2571205 = 482101) (by norm_num)
theorem B3428273 : Blo 2285435 3428273 := bstep (se 2 (by rfl) ⟨1285602, by rfl⟩ : syracuseStep 3428273 = 2571205) B2571205
theorem B2285515 : Blo 2285435 2285515 := bstep (se 1 (by rfl) ⟨1714136, by rfl⟩ : syracuseStep 2285515 = 3428273) B3428273
theorem B4338917 : Blo 2285435 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B2892611 : Blo 2285435 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B7713629 : Blo 2285435 7713629 := bstep (se 3 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 7713629 = 2892611) B2892611
theorem B5142419 : Blo 2285435 5142419 := bstep (se 1 (by rfl) ⟨3856814, by rfl⟩ : syracuseStep 5142419 = 7713629) B7713629
theorem B3428279 : Blo 2285435 3428279 := bstep (se 1 (by rfl) ⟨2571209, by rfl⟩ : syracuseStep 3428279 = 5142419) B5142419
theorem B2285519 : Blo 2285435 2285519 := bstep (se 1 (by rfl) ⟨1714139, by rfl⟩ : syracuseStep 2285519 = 3428279) B3428279
theorem B3428285 : Blo 2285435 3428285 := bbase (se 3 (by rfl) ⟨642803, by rfl⟩ : syracuseStep 3428285 = 1285607) (by norm_num)
theorem B2285523 : Blo 2285435 2285523 := bstep (se 1 (by rfl) ⟨1714142, by rfl⟩ : syracuseStep 2285523 = 3428285) B3428285
theorem B5142437 : Blo 2285435 5142437 := bbase (se 4 (by rfl) ⟨482103, by rfl⟩ : syracuseStep 5142437 = 964207) (by norm_num)
theorem B3428291 : Blo 2285435 3428291 := bstep (se 1 (by rfl) ⟨2571218, by rfl⟩ : syracuseStep 3428291 = 5142437) B5142437
theorem B2285527 : Blo 2285435 2285527 := bstep (se 1 (by rfl) ⟨1714145, by rfl⟩ : syracuseStep 2285527 = 3428291) B3428291
theorem B5785253 : Blo 2285435 5785253 := bbase (se 4 (by rfl) ⟨542367, by rfl⟩ : syracuseStep 5785253 = 1084735) (by norm_num)
theorem B3856835 : Blo 2285435 3856835 := bstep (se 1 (by rfl) ⟨2892626, by rfl⟩ : syracuseStep 3856835 = 5785253) B5785253
theorem B2571223 : Blo 2285435 2571223 := bstep (se 1 (by rfl) ⟨1928417, by rfl⟩ : syracuseStep 2571223 = 3856835) B3856835
theorem B3428297 : Blo 2285435 3428297 := bstep (se 2 (by rfl) ⟨1285611, by rfl⟩ : syracuseStep 3428297 = 2571223) B2571223
theorem B2285531 : Blo 2285435 2285531 := bstep (se 1 (by rfl) ⟨1714148, by rfl⟩ : syracuseStep 2285531 = 3428297) B3428297
theorem B6508421 : Blo 2285435 6508421 := bbase (se 4 (by rfl) ⟨610164, by rfl⟩ : syracuseStep 6508421 = 1220329) (by norm_num)
theorem B4338947 : Blo 2285435 4338947 := bstep (se 1 (by rfl) ⟨3254210, by rfl⟩ : syracuseStep 4338947 = 6508421) B6508421
theorem B11570525 : Blo 2285435 11570525 := bstep (se 3 (by rfl) ⟨2169473, by rfl⟩ : syracuseStep 11570525 = 4338947) B4338947
theorem B7713683 : Blo 2285435 7713683 := bstep (se 1 (by rfl) ⟨5785262, by rfl⟩ : syracuseStep 7713683 = 11570525) B11570525
theorem B5142455 : Blo 2285435 5142455 := bstep (se 1 (by rfl) ⟨3856841, by rfl⟩ : syracuseStep 5142455 = 7713683) B7713683
theorem B3428303 : Blo 2285435 3428303 := bstep (se 1 (by rfl) ⟨2571227, by rfl⟩ : syracuseStep 3428303 = 5142455) B5142455
theorem B2285535 : Blo 2285435 2285535 := bstep (se 1 (by rfl) ⟨1714151, by rfl⟩ : syracuseStep 2285535 = 3428303) B3428303
theorem B3428309 : Blo 2285435 3428309 := bbase (se 7 (by rfl) ⟨40175, by rfl⟩ : syracuseStep 3428309 = 80351) (by norm_num)
theorem B2285539 : Blo 2285435 2285539 := bstep (se 1 (by rfl) ⟨1714154, by rfl⟩ : syracuseStep 2285539 = 3428309) B3428309
theorem B8677925 : Blo 2285435 8677925 := bbase (se 4 (by rfl) ⟨813555, by rfl⟩ : syracuseStep 8677925 = 1627111) (by norm_num)
theorem B5785283 : Blo 2285435 5785283 := bstep (se 1 (by rfl) ⟨4338962, by rfl⟩ : syracuseStep 5785283 = 8677925) B8677925
theorem B3856855 : Blo 2285435 3856855 := bstep (se 1 (by rfl) ⟨2892641, by rfl⟩ : syracuseStep 3856855 = 5785283) B5785283
theorem B5142473 : Blo 2285435 5142473 := bstep (se 2 (by rfl) ⟨1928427, by rfl⟩ : syracuseStep 5142473 = 3856855) B3856855
theorem B3428315 : Blo 2285435 3428315 := bstep (se 1 (by rfl) ⟨2571236, by rfl⟩ : syracuseStep 3428315 = 5142473) B5142473
theorem B2285543 : Blo 2285435 2285543 := bstep (se 1 (by rfl) ⟨1714157, by rfl⟩ : syracuseStep 2285543 = 3428315) B3428315
theorem B2571241 : Blo 2285435 2571241 := bbase (se 2 (by rfl) ⟨964215, by rfl⟩ : syracuseStep 2571241 = 1928431) (by norm_num)
theorem B3428321 : Blo 2285435 3428321 := bstep (se 2 (by rfl) ⟨1285620, by rfl⟩ : syracuseStep 3428321 = 2571241) B2571241
theorem B2285547 : Blo 2285435 2285547 := bstep (se 1 (by rfl) ⟨1714160, by rfl⟩ : syracuseStep 2285547 = 3428321) B3428321
theorem B3661013 : Blo 2285435 3661013 := bbase (se 7 (by rfl) ⟨42902, by rfl⟩ : syracuseStep 3661013 = 85805) (by norm_num)
theorem B2440675 : Blo 2285435 2440675 := bstep (se 1 (by rfl) ⟨1830506, by rfl⟩ : syracuseStep 2440675 = 3661013) B3661013
theorem B13016933 : Blo 2285435 13016933 := bstep (se 4 (by rfl) ⟨1220337, by rfl⟩ : syracuseStep 13016933 = 2440675) B2440675
theorem B8677955 : Blo 2285435 8677955 := bstep (se 1 (by rfl) ⟨6508466, by rfl⟩ : syracuseStep 8677955 = 13016933) B13016933
theorem B5785303 : Blo 2285435 5785303 := bstep (se 1 (by rfl) ⟨4338977, by rfl⟩ : syracuseStep 5785303 = 8677955) B8677955
theorem B7713737 : Blo 2285435 7713737 := bstep (se 2 (by rfl) ⟨2892651, by rfl⟩ : syracuseStep 7713737 = 5785303) B5785303
theorem B5142491 : Blo 2285435 5142491 := bstep (se 1 (by rfl) ⟨3856868, by rfl⟩ : syracuseStep 5142491 = 7713737) B7713737
theorem B3428327 : Blo 2285435 3428327 := bstep (se 1 (by rfl) ⟨2571245, by rfl⟩ : syracuseStep 3428327 = 5142491) B5142491
theorem B2285551 : Blo 2285435 2285551 := bstep (se 1 (by rfl) ⟨1714163, by rfl⟩ : syracuseStep 2285551 = 3428327) B3428327
theorem B3428333 : Blo 2285435 3428333 := bbase (se 3 (by rfl) ⟨642812, by rfl⟩ : syracuseStep 3428333 = 1285625) (by norm_num)
theorem B2285555 : Blo 2285435 2285555 := bstep (se 1 (by rfl) ⟨1714166, by rfl⟩ : syracuseStep 2285555 = 3428333) B3428333
theorem B5142509 : Blo 2285435 5142509 := bbase (se 3 (by rfl) ⟨964220, by rfl⟩ : syracuseStep 5142509 = 1928441) (by norm_num)
theorem B3428339 : Blo 2285435 3428339 := bstep (se 1 (by rfl) ⟨2571254, by rfl⟩ : syracuseStep 3428339 = 5142509) B5142509
theorem B2285559 : Blo 2285435 2285559 := bstep (se 1 (by rfl) ⟨1714169, by rfl⟩ : syracuseStep 2285559 = 3428339) B3428339
theorem B6950245 : Blo 2285435 6950245 := bbase (se 4 (by rfl) ⟨651585, by rfl⟩ : syracuseStep 6950245 = 1303171) (by norm_num)
theorem B9266993 : Blo 2285435 9266993 := bstep (se 2 (by rfl) ⟨3475122, by rfl⟩ : syracuseStep 9266993 = 6950245) B6950245
theorem B6177995 : Blo 2285435 6177995 := bstep (se 1 (by rfl) ⟨4633496, by rfl⟩ : syracuseStep 6177995 = 9266993) B9266993
theorem B4118663 : Blo 2285435 4118663 := bstep (se 1 (by rfl) ⟨3088997, by rfl⟩ : syracuseStep 4118663 = 6177995) B6177995
theorem B2745775 : Blo 2285435 2745775 := bstep (se 1 (by rfl) ⟨2059331, by rfl⟩ : syracuseStep 2745775 = 4118663) B4118663
theorem B3661033 : Blo 2285435 3661033 := bstep (se 2 (by rfl) ⟨1372887, by rfl⟩ : syracuseStep 3661033 = 2745775) B2745775
theorem B4881377 : Blo 2285435 4881377 := bstep (se 2 (by rfl) ⟨1830516, by rfl⟩ : syracuseStep 4881377 = 3661033) B3661033
theorem B3254251 : Blo 2285435 3254251 := bstep (se 1 (by rfl) ⟨2440688, by rfl⟩ : syracuseStep 3254251 = 4881377) B4881377
theorem B4339001 : Blo 2285435 4339001 := bstep (se 2 (by rfl) ⟨1627125, by rfl⟩ : syracuseStep 4339001 = 3254251) B3254251
theorem B2892667 : Blo 2285435 2892667 := bstep (se 1 (by rfl) ⟨2169500, by rfl⟩ : syracuseStep 2892667 = 4339001) B4339001
theorem B3856889 : Blo 2285435 3856889 := bstep (se 2 (by rfl) ⟨1446333, by rfl⟩ : syracuseStep 3856889 = 2892667) B2892667
theorem B2571259 : Blo 2285435 2571259 := bstep (se 1 (by rfl) ⟨1928444, by rfl⟩ : syracuseStep 2571259 = 3856889) B3856889
theorem B3428345 : Blo 2285435 3428345 := bstep (se 2 (by rfl) ⟨1285629, by rfl⟩ : syracuseStep 3428345 = 2571259) B2571259
theorem B2285563 : Blo 2285435 2285563 := bstep (se 1 (by rfl) ⟨1714172, by rfl⟩ : syracuseStep 2285563 = 3428345) B3428345
theorem B2541961 : Blo 2285435 2541961 := bbase (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) (by norm_num)
theorem B13557125 : Blo 2285435 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B9038083 : Blo 2285435 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B12050777 : Blo 2285435 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B8033851 : Blo 2285435 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B10711801 : Blo 2285435 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B14282401 : Blo 2285435 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B19043201 : Blo 2285435 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B12695467 : Blo 2285435 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B16927289 : Blo 2285435 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B11284859 : Blo 2285435 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B7523239 : Blo 2285435 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B10030985 : Blo 2285435 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B6687323 : Blo 2285435 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B4458215 : Blo 2285435 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B2972143 : Blo 2285435 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B3962857 : Blo 2285435 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B5283809 : Blo 2285435 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B3522539 : Blo 2285435 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B2348359 : Blo 2285435 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B12524581 : Blo 2285435 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B16699441 : Blo 2285435 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B22265921 : Blo 2285435 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B14843947 : Blo 2285435 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B19791929 : Blo 2285435 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B13194619 : Blo 2285435 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B70371301 : Blo 2285435 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B93828401 : Blo 2285435 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B62552267 : Blo 2285435 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B41701511 : Blo 2285435 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B111204029 : Blo 2285435 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B296544077 : Blo 2285435 296544077 := bstep (se 3 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 296544077 = 111204029) B111204029
theorem B197696051 : Blo 2285435 197696051 := bstep (se 1 (by rfl) ⟨148272038, by rfl⟩ : syracuseStep 197696051 = 296544077) B296544077
theorem B131797367 : Blo 2285435 131797367 := bstep (se 1 (by rfl) ⟨98848025, by rfl⟩ : syracuseStep 131797367 = 197696051) B197696051
theorem B87864911 : Blo 2285435 87864911 := bstep (se 1 (by rfl) ⟨65898683, by rfl⟩ : syracuseStep 87864911 = 131797367) B131797367
theorem B58576607 : Blo 2285435 58576607 := bstep (se 1 (by rfl) ⟨43932455, by rfl⟩ : syracuseStep 58576607 = 87864911) B87864911
theorem B39051071 : Blo 2285435 39051071 := bstep (se 1 (by rfl) ⟨29288303, by rfl⟩ : syracuseStep 39051071 = 58576607) B58576607
theorem B26034047 : Blo 2285435 26034047 := bstep (se 1 (by rfl) ⟨19525535, by rfl⟩ : syracuseStep 26034047 = 39051071) B39051071
theorem B17356031 : Blo 2285435 17356031 := bstep (se 1 (by rfl) ⟨13017023, by rfl⟩ : syracuseStep 17356031 = 26034047) B26034047
theorem B11570687 : Blo 2285435 11570687 := bstep (se 1 (by rfl) ⟨8678015, by rfl⟩ : syracuseStep 11570687 = 17356031) B17356031
theorem B7713791 : Blo 2285435 7713791 := bstep (se 1 (by rfl) ⟨5785343, by rfl⟩ : syracuseStep 7713791 = 11570687) B11570687
theorem B5142527 : Blo 2285435 5142527 := bstep (se 1 (by rfl) ⟨3856895, by rfl⟩ : syracuseStep 5142527 = 7713791) B7713791
theorem B3428351 : Blo 2285435 3428351 := bstep (se 1 (by rfl) ⟨2571263, by rfl⟩ : syracuseStep 3428351 = 5142527) B5142527
theorem B2285567 : Blo 2285435 2285567 := bstep (se 1 (by rfl) ⟨1714175, by rfl⟩ : syracuseStep 2285567 = 3428351) B3428351
theorem B3428357 : Blo 2285435 3428357 := bbase (se 4 (by rfl) ⟨321408, by rfl⟩ : syracuseStep 3428357 = 642817) (by norm_num)
theorem B2285571 : Blo 2285435 2285571 := bstep (se 1 (by rfl) ⟨1714178, by rfl⟩ : syracuseStep 2285571 = 3428357) B3428357
theorem B3856909 : Blo 2285435 3856909 := bbase (se 3 (by rfl) ⟨723170, by rfl⟩ : syracuseStep 3856909 = 1446341) (by norm_num)
theorem B5142545 : Blo 2285435 5142545 := bstep (se 2 (by rfl) ⟨1928454, by rfl⟩ : syracuseStep 5142545 = 3856909) B3856909
theorem B3428363 : Blo 2285435 3428363 := bstep (se 1 (by rfl) ⟨2571272, by rfl⟩ : syracuseStep 3428363 = 5142545) B5142545
theorem B2285575 : Blo 2285435 2285575 := bstep (se 1 (by rfl) ⟨1714181, by rfl⟩ : syracuseStep 2285575 = 3428363) B3428363
theorem B2571277 : Blo 2285435 2571277 := bbase (se 3 (by rfl) ⟨482114, by rfl⟩ : syracuseStep 2571277 = 964229) (by norm_num)
theorem B3428369 : Blo 2285435 3428369 := bstep (se 2 (by rfl) ⟨1285638, by rfl⟩ : syracuseStep 3428369 = 2571277) B2571277
theorem B2285579 : Blo 2285435 2285579 := bstep (se 1 (by rfl) ⟨1714184, by rfl⟩ : syracuseStep 2285579 = 3428369) B3428369
theorem B7713845 : Blo 2285435 7713845 := bbase (se 5 (by rfl) ⟨361586, by rfl⟩ : syracuseStep 7713845 = 723173) (by norm_num)
theorem B5142563 : Blo 2285435 5142563 := bstep (se 1 (by rfl) ⟨3856922, by rfl⟩ : syracuseStep 5142563 = 7713845) B7713845
theorem B3428375 : Blo 2285435 3428375 := bstep (se 1 (by rfl) ⟨2571281, by rfl⟩ : syracuseStep 3428375 = 5142563) B5142563
theorem B2285583 : Blo 2285435 2285583 := bstep (se 1 (by rfl) ⟨1714187, by rfl⟩ : syracuseStep 2285583 = 3428375) B3428375
theorem B3428381 : Blo 2285435 3428381 := bbase (se 3 (by rfl) ⟨642821, by rfl⟩ : syracuseStep 3428381 = 1285643) (by norm_num)
theorem B2285587 : Blo 2285435 2285587 := bstep (se 1 (by rfl) ⟨1714190, by rfl⟩ : syracuseStep 2285587 = 3428381) B3428381
theorem B5142581 : Blo 2285435 5142581 := bbase (se 5 (by rfl) ⟨241058, by rfl⟩ : syracuseStep 5142581 = 482117) (by norm_num)
theorem B3428387 : Blo 2285435 3428387 := bstep (se 1 (by rfl) ⟨2571290, by rfl⟩ : syracuseStep 3428387 = 5142581) B5142581
theorem B2285591 : Blo 2285435 2285591 := bstep (se 1 (by rfl) ⟨1714193, by rfl⟩ : syracuseStep 2285591 = 3428387) B3428387
theorem B23457397 : Blo 2285435 23457397 := bbase (se 5 (by rfl) ⟨1099565, by rfl⟩ : syracuseStep 23457397 = 2199131) (by norm_num)
theorem B31276529 : Blo 2285435 31276529 := bstep (se 2 (by rfl) ⟨11728698, by rfl⟩ : syracuseStep 31276529 = 23457397) B23457397
theorem B20851019 : Blo 2285435 20851019 := bstep (se 1 (by rfl) ⟨15638264, by rfl⟩ : syracuseStep 20851019 = 31276529) B31276529
theorem B13900679 : Blo 2285435 13900679 := bstep (se 1 (by rfl) ⟨10425509, by rfl⟩ : syracuseStep 13900679 = 20851019) B20851019
theorem B9267119 : Blo 2285435 9267119 := bstep (se 1 (by rfl) ⟨6950339, by rfl⟩ : syracuseStep 9267119 = 13900679) B13900679
theorem B6178079 : Blo 2285435 6178079 := bstep (se 1 (by rfl) ⟨4633559, by rfl⟩ : syracuseStep 6178079 = 9267119) B9267119
theorem B16474877 : Blo 2285435 16474877 := bstep (se 3 (by rfl) ⟨3089039, by rfl⟩ : syracuseStep 16474877 = 6178079) B6178079
theorem B10983251 : Blo 2285435 10983251 := bstep (se 1 (by rfl) ⟨8237438, by rfl⟩ : syracuseStep 10983251 = 16474877) B16474877
theorem B7322167 : Blo 2285435 7322167 := bstep (se 1 (by rfl) ⟨5491625, by rfl⟩ : syracuseStep 7322167 = 10983251) B10983251
theorem B9762889 : Blo 2285435 9762889 := bstep (se 2 (by rfl) ⟨3661083, by rfl⟩ : syracuseStep 9762889 = 7322167) B7322167
theorem B13017185 : Blo 2285435 13017185 := bstep (se 2 (by rfl) ⟨4881444, by rfl⟩ : syracuseStep 13017185 = 9762889) B9762889
theorem B8678123 : Blo 2285435 8678123 := bstep (se 1 (by rfl) ⟨6508592, by rfl⟩ : syracuseStep 8678123 = 13017185) B13017185
theorem B5785415 : Blo 2285435 5785415 := bstep (se 1 (by rfl) ⟨4339061, by rfl⟩ : syracuseStep 5785415 = 8678123) B8678123
theorem B3856943 : Blo 2285435 3856943 := bstep (se 1 (by rfl) ⟨2892707, by rfl⟩ : syracuseStep 3856943 = 5785415) B5785415
theorem B2571295 : Blo 2285435 2571295 := bstep (se 1 (by rfl) ⟨1928471, by rfl⟩ : syracuseStep 2571295 = 3856943) B3856943
theorem B3428393 : Blo 2285435 3428393 := bstep (se 2 (by rfl) ⟨1285647, by rfl⟩ : syracuseStep 3428393 = 2571295) B2571295
theorem B2285595 : Blo 2285435 2285595 := bstep (se 1 (by rfl) ⟨1714196, by rfl⟩ : syracuseStep 2285595 = 3428393) B3428393
theorem B10983269 : Blo 2285435 10983269 := bbase (se 4 (by rfl) ⟨1029681, by rfl⟩ : syracuseStep 10983269 = 2059363) (by norm_num)
theorem B7322179 : Blo 2285435 7322179 := bstep (se 1 (by rfl) ⟨5491634, by rfl⟩ : syracuseStep 7322179 = 10983269) B10983269
theorem B9762905 : Blo 2285435 9762905 := bstep (se 2 (by rfl) ⟨3661089, by rfl⟩ : syracuseStep 9762905 = 7322179) B7322179
theorem B6508603 : Blo 2285435 6508603 := bstep (se 1 (by rfl) ⟨4881452, by rfl⟩ : syracuseStep 6508603 = 9762905) B9762905
theorem B8678137 : Blo 2285435 8678137 := bstep (se 2 (by rfl) ⟨3254301, by rfl⟩ : syracuseStep 8678137 = 6508603) B6508603
theorem B11570849 : Blo 2285435 11570849 := bstep (se 2 (by rfl) ⟨4339068, by rfl⟩ : syracuseStep 11570849 = 8678137) B8678137
theorem B7713899 : Blo 2285435 7713899 := bstep (se 1 (by rfl) ⟨5785424, by rfl⟩ : syracuseStep 7713899 = 11570849) B11570849
theorem B5142599 : Blo 2285435 5142599 := bstep (se 1 (by rfl) ⟨3856949, by rfl⟩ : syracuseStep 5142599 = 7713899) B7713899
theorem B3428399 : Blo 2285435 3428399 := bstep (se 1 (by rfl) ⟨2571299, by rfl⟩ : syracuseStep 3428399 = 5142599) B5142599
theorem B2285599 : Blo 2285435 2285599 := bstep (se 1 (by rfl) ⟨1714199, by rfl⟩ : syracuseStep 2285599 = 3428399) B3428399
theorem B3428405 : Blo 2285435 3428405 := bbase (se 5 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 3428405 = 321413) (by norm_num)
theorem B2285603 : Blo 2285435 2285603 := bstep (se 1 (by rfl) ⟨1714202, by rfl⟩ : syracuseStep 2285603 = 3428405) B3428405
theorem B5785445 : Blo 2285435 5785445 := bbase (se 4 (by rfl) ⟨542385, by rfl⟩ : syracuseStep 5785445 = 1084771) (by norm_num)
theorem B3856963 : Blo 2285435 3856963 := bstep (se 1 (by rfl) ⟨2892722, by rfl⟩ : syracuseStep 3856963 = 5785445) B5785445
theorem B5142617 : Blo 2285435 5142617 := bstep (se 2 (by rfl) ⟨1928481, by rfl⟩ : syracuseStep 5142617 = 3856963) B3856963
theorem B3428411 : Blo 2285435 3428411 := bstep (se 1 (by rfl) ⟨2571308, by rfl⟩ : syracuseStep 3428411 = 5142617) B5142617
theorem B2285607 : Blo 2285435 2285607 := bstep (se 1 (by rfl) ⟨1714205, by rfl⟩ : syracuseStep 2285607 = 3428411) B3428411
theorem B2571313 : Blo 2285435 2571313 := bbase (se 2 (by rfl) ⟨964242, by rfl⟩ : syracuseStep 2571313 = 1928485) (by norm_num)
theorem B3428417 : Blo 2285435 3428417 := bstep (se 2 (by rfl) ⟨1285656, by rfl⟩ : syracuseStep 3428417 = 2571313) B2571313
theorem B2285611 : Blo 2285435 2285611 := bstep (se 1 (by rfl) ⟨1714208, by rfl⟩ : syracuseStep 2285611 = 3428417) B3428417
theorem B6178133 : Blo 2285435 6178133 := bbase (se 12 (by rfl) ⟨2262, by rfl⟩ : syracuseStep 6178133 = 4525) (by norm_num)
theorem B16475021 : Blo 2285435 16475021 := bstep (se 3 (by rfl) ⟨3089066, by rfl⟩ : syracuseStep 16475021 = 6178133) B6178133
theorem B10983347 : Blo 2285435 10983347 := bstep (se 1 (by rfl) ⟨8237510, by rfl⟩ : syracuseStep 10983347 = 16475021) B16475021
theorem B7322231 : Blo 2285435 7322231 := bstep (se 1 (by rfl) ⟨5491673, by rfl⟩ : syracuseStep 7322231 = 10983347) B10983347
theorem B4881487 : Blo 2285435 4881487 := bstep (se 1 (by rfl) ⟨3661115, by rfl⟩ : syracuseStep 4881487 = 7322231) B7322231
theorem B6508649 : Blo 2285435 6508649 := bstep (se 2 (by rfl) ⟨2440743, by rfl⟩ : syracuseStep 6508649 = 4881487) B4881487
theorem B4339099 : Blo 2285435 4339099 := bstep (se 1 (by rfl) ⟨3254324, by rfl⟩ : syracuseStep 4339099 = 6508649) B6508649
theorem B5785465 : Blo 2285435 5785465 := bstep (se 2 (by rfl) ⟨2169549, by rfl⟩ : syracuseStep 5785465 = 4339099) B4339099
theorem B7713953 : Blo 2285435 7713953 := bstep (se 2 (by rfl) ⟨2892732, by rfl⟩ : syracuseStep 7713953 = 5785465) B5785465
theorem B5142635 : Blo 2285435 5142635 := bstep (se 1 (by rfl) ⟨3856976, by rfl⟩ : syracuseStep 5142635 = 7713953) B7713953
theorem B3428423 : Blo 2285435 3428423 := bstep (se 1 (by rfl) ⟨2571317, by rfl⟩ : syracuseStep 3428423 = 5142635) B5142635
theorem B2285615 : Blo 2285435 2285615 := bstep (se 1 (by rfl) ⟨1714211, by rfl⟩ : syracuseStep 2285615 = 3428423) B3428423
theorem B3428429 : Blo 2285435 3428429 := bbase (se 3 (by rfl) ⟨642830, by rfl⟩ : syracuseStep 3428429 = 1285661) (by norm_num)
theorem B2285619 : Blo 2285435 2285619 := bstep (se 1 (by rfl) ⟨1714214, by rfl⟩ : syracuseStep 2285619 = 3428429) B3428429
theorem B5142653 : Blo 2285435 5142653 := bbase (se 3 (by rfl) ⟨964247, by rfl⟩ : syracuseStep 5142653 = 1928495) (by norm_num)
theorem B3428435 : Blo 2285435 3428435 := bstep (se 1 (by rfl) ⟨2571326, by rfl⟩ : syracuseStep 3428435 = 5142653) B5142653
theorem B2285623 : Blo 2285435 2285623 := bstep (se 1 (by rfl) ⟨1714217, by rfl⟩ : syracuseStep 2285623 = 3428435) B3428435
theorem B3856997 : Blo 2285435 3856997 := bbase (se 4 (by rfl) ⟨361593, by rfl⟩ : syracuseStep 3856997 = 723187) (by norm_num)
theorem B2571331 : Blo 2285435 2571331 := bstep (se 1 (by rfl) ⟨1928498, by rfl⟩ : syracuseStep 2571331 = 3856997) B3856997
theorem B3428441 : Blo 2285435 3428441 := bstep (se 2 (by rfl) ⟨1285665, by rfl⟩ : syracuseStep 3428441 = 2571331) B2571331
theorem B2285627 : Blo 2285435 2285627 := bstep (se 1 (by rfl) ⟨1714220, by rfl⟩ : syracuseStep 2285627 = 3428441) B3428441
theorem B3661141 : Blo 2285435 3661141 := bbase (se 11 (by rfl) ⟨2681, by rfl⟩ : syracuseStep 3661141 = 5363) (by norm_num)
theorem B4881521 : Blo 2285435 4881521 := bstep (se 2 (by rfl) ⟨1830570, by rfl⟩ : syracuseStep 4881521 = 3661141) B3661141
theorem B3254347 : Blo 2285435 3254347 := bstep (se 1 (by rfl) ⟨2440760, by rfl⟩ : syracuseStep 3254347 = 4881521) B4881521
theorem B17356517 : Blo 2285435 17356517 := bstep (se 4 (by rfl) ⟨1627173, by rfl⟩ : syracuseStep 17356517 = 3254347) B3254347
theorem B11571011 : Blo 2285435 11571011 := bstep (se 1 (by rfl) ⟨8678258, by rfl⟩ : syracuseStep 11571011 = 17356517) B17356517
theorem B7714007 : Blo 2285435 7714007 := bstep (se 1 (by rfl) ⟨5785505, by rfl⟩ : syracuseStep 7714007 = 11571011) B11571011
theorem B5142671 : Blo 2285435 5142671 := bstep (se 1 (by rfl) ⟨3857003, by rfl⟩ : syracuseStep 5142671 = 7714007) B7714007
theorem B3428447 : Blo 2285435 3428447 := bstep (se 1 (by rfl) ⟨2571335, by rfl⟩ : syracuseStep 3428447 = 5142671) B5142671
theorem B2285631 : Blo 2285435 2285631 := bstep (se 1 (by rfl) ⟨1714223, by rfl⟩ : syracuseStep 2285631 = 3428447) B3428447
theorem B3428453 : Blo 2285435 3428453 := bbase (se 4 (by rfl) ⟨321417, by rfl⟩ : syracuseStep 3428453 = 642835) (by norm_num)
theorem B2285635 : Blo 2285435 2285635 := bstep (se 1 (by rfl) ⟨1714226, by rfl⟩ : syracuseStep 2285635 = 3428453) B3428453
theorem B7322309 : Blo 2285435 7322309 := bbase (se 4 (by rfl) ⟨686466, by rfl⟩ : syracuseStep 7322309 = 1372933) (by norm_num)
theorem B4881539 : Blo 2285435 4881539 := bstep (se 1 (by rfl) ⟨3661154, by rfl⟩ : syracuseStep 4881539 = 7322309) B7322309
theorem B3254359 : Blo 2285435 3254359 := bstep (se 1 (by rfl) ⟨2440769, by rfl⟩ : syracuseStep 3254359 = 4881539) B4881539
theorem B4339145 : Blo 2285435 4339145 := bstep (se 2 (by rfl) ⟨1627179, by rfl⟩ : syracuseStep 4339145 = 3254359) B3254359
theorem B2892763 : Blo 2285435 2892763 := bstep (se 1 (by rfl) ⟨2169572, by rfl⟩ : syracuseStep 2892763 = 4339145) B4339145
theorem B3857017 : Blo 2285435 3857017 := bstep (se 2 (by rfl) ⟨1446381, by rfl⟩ : syracuseStep 3857017 = 2892763) B2892763
theorem B5142689 : Blo 2285435 5142689 := bstep (se 2 (by rfl) ⟨1928508, by rfl⟩ : syracuseStep 5142689 = 3857017) B3857017
theorem B3428459 : Blo 2285435 3428459 := bstep (se 1 (by rfl) ⟨2571344, by rfl⟩ : syracuseStep 3428459 = 5142689) B5142689
theorem B2285639 : Blo 2285435 2285639 := bstep (se 1 (by rfl) ⟨1714229, by rfl⟩ : syracuseStep 2285639 = 3428459) B3428459
theorem B2571349 : Blo 2285435 2571349 := bbase (se 8 (by rfl) ⟨15066, by rfl⟩ : syracuseStep 2571349 = 30133) (by norm_num)
theorem B3428465 : Blo 2285435 3428465 := bstep (se 2 (by rfl) ⟨1285674, by rfl⟩ : syracuseStep 3428465 = 2571349) B2571349
theorem B2285643 : Blo 2285435 2285643 := bstep (se 1 (by rfl) ⟨1714232, by rfl⟩ : syracuseStep 2285643 = 3428465) B3428465
theorem B2892773 : Blo 2285435 2892773 := bbase (se 4 (by rfl) ⟨271197, by rfl⟩ : syracuseStep 2892773 = 542395) (by norm_num)
theorem B7714061 : Blo 2285435 7714061 := bstep (se 3 (by rfl) ⟨1446386, by rfl⟩ : syracuseStep 7714061 = 2892773) B2892773
theorem B5142707 : Blo 2285435 5142707 := bstep (se 1 (by rfl) ⟨3857030, by rfl⟩ : syracuseStep 5142707 = 7714061) B7714061
theorem B3428471 : Blo 2285435 3428471 := bstep (se 1 (by rfl) ⟨2571353, by rfl⟩ : syracuseStep 3428471 = 5142707) B5142707
theorem B2285647 : Blo 2285435 2285647 := bstep (se 1 (by rfl) ⟨1714235, by rfl⟩ : syracuseStep 2285647 = 3428471) B3428471
theorem B3428477 : Blo 2285435 3428477 := bbase (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) (by norm_num)
theorem B2285651 : Blo 2285435 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B5142725 : Blo 2285435 5142725 := bbase (se 4 (by rfl) ⟨482130, by rfl⟩ : syracuseStep 5142725 = 964261) (by norm_num)
theorem B3428483 : Blo 2285435 3428483 := bstep (se 1 (by rfl) ⟨2571362, by rfl⟩ : syracuseStep 3428483 = 5142725) B5142725
theorem B2285655 : Blo 2285435 2285655 := bstep (se 1 (by rfl) ⟨1714241, by rfl⟩ : syracuseStep 2285655 = 3428483) B3428483
theorem B5212901 : Blo 2285435 5212901 := bbase (se 4 (by rfl) ⟨488709, by rfl⟩ : syracuseStep 5212901 = 977419) (by norm_num)
theorem B3475267 : Blo 2285435 3475267 := bstep (se 1 (by rfl) ⟨2606450, by rfl⟩ : syracuseStep 3475267 = 5212901) B5212901
theorem B18534757 : Blo 2285435 18534757 := bstep (se 4 (by rfl) ⟨1737633, by rfl⟩ : syracuseStep 18534757 = 3475267) B3475267
theorem B24713009 : Blo 2285435 24713009 := bstep (se 2 (by rfl) ⟨9267378, by rfl⟩ : syracuseStep 24713009 = 18534757) B18534757
theorem B16475339 : Blo 2285435 16475339 := bstep (se 1 (by rfl) ⟨12356504, by rfl⟩ : syracuseStep 16475339 = 24713009) B24713009
theorem B10983559 : Blo 2285435 10983559 := bstep (se 1 (by rfl) ⟨8237669, by rfl⟩ : syracuseStep 10983559 = 16475339) B16475339
theorem B14644745 : Blo 2285435 14644745 := bstep (se 2 (by rfl) ⟨5491779, by rfl⟩ : syracuseStep 14644745 = 10983559) B10983559
theorem B9763163 : Blo 2285435 9763163 := bstep (se 1 (by rfl) ⟨7322372, by rfl⟩ : syracuseStep 9763163 = 14644745) B14644745
theorem B6508775 : Blo 2285435 6508775 := bstep (se 1 (by rfl) ⟨4881581, by rfl⟩ : syracuseStep 6508775 = 9763163) B9763163
theorem B4339183 : Blo 2285435 4339183 := bstep (se 1 (by rfl) ⟨3254387, by rfl⟩ : syracuseStep 4339183 = 6508775) B6508775
theorem B5785577 : Blo 2285435 5785577 := bstep (se 2 (by rfl) ⟨2169591, by rfl⟩ : syracuseStep 5785577 = 4339183) B4339183
theorem B3857051 : Blo 2285435 3857051 := bstep (se 1 (by rfl) ⟨2892788, by rfl⟩ : syracuseStep 3857051 = 5785577) B5785577
theorem B2571367 : Blo 2285435 2571367 := bstep (se 1 (by rfl) ⟨1928525, by rfl⟩ : syracuseStep 2571367 = 3857051) B3857051
theorem B3428489 : Blo 2285435 3428489 := bstep (se 2 (by rfl) ⟨1285683, by rfl⟩ : syracuseStep 3428489 = 2571367) B2571367
theorem B2285659 : Blo 2285435 2285659 := bstep (se 1 (by rfl) ⟨1714244, by rfl⟩ : syracuseStep 2285659 = 3428489) B3428489
theorem B11571173 : Blo 2285435 11571173 := bbase (se 4 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 11571173 = 2169595) (by norm_num)
theorem B7714115 : Blo 2285435 7714115 := bstep (se 1 (by rfl) ⟨5785586, by rfl⟩ : syracuseStep 7714115 = 11571173) B11571173
theorem B5142743 : Blo 2285435 5142743 := bstep (se 1 (by rfl) ⟨3857057, by rfl⟩ : syracuseStep 5142743 = 7714115) B7714115
theorem B3428495 : Blo 2285435 3428495 := bstep (se 1 (by rfl) ⟨2571371, by rfl⟩ : syracuseStep 3428495 = 5142743) B5142743
theorem B2285663 : Blo 2285435 2285663 := bstep (se 1 (by rfl) ⟨1714247, by rfl⟩ : syracuseStep 2285663 = 3428495) B3428495
theorem B3428501 : Blo 2285435 3428501 := bbase (se 6 (by rfl) ⟨80355, by rfl⟩ : syracuseStep 3428501 = 160711) (by norm_num)
theorem B2285667 : Blo 2285435 2285667 := bstep (se 1 (by rfl) ⟨1714250, by rfl⟩ : syracuseStep 2285667 = 3428501) B3428501
theorem B3661205 : Blo 2285435 3661205 := bbase (se 6 (by rfl) ⟨85809, by rfl⟩ : syracuseStep 3661205 = 171619) (by norm_num)
theorem B9763213 : Blo 2285435 9763213 := bstep (se 3 (by rfl) ⟨1830602, by rfl⟩ : syracuseStep 9763213 = 3661205) B3661205
theorem B13017617 : Blo 2285435 13017617 := bstep (se 2 (by rfl) ⟨4881606, by rfl⟩ : syracuseStep 13017617 = 9763213) B9763213
theorem B8678411 : Blo 2285435 8678411 := bstep (se 1 (by rfl) ⟨6508808, by rfl⟩ : syracuseStep 8678411 = 13017617) B13017617
theorem B5785607 : Blo 2285435 5785607 := bstep (se 1 (by rfl) ⟨4339205, by rfl⟩ : syracuseStep 5785607 = 8678411) B8678411
theorem B3857071 : Blo 2285435 3857071 := bstep (se 1 (by rfl) ⟨2892803, by rfl⟩ : syracuseStep 3857071 = 5785607) B5785607
theorem B5142761 : Blo 2285435 5142761 := bstep (se 2 (by rfl) ⟨1928535, by rfl⟩ : syracuseStep 5142761 = 3857071) B3857071
theorem B3428507 : Blo 2285435 3428507 := bstep (se 1 (by rfl) ⟨2571380, by rfl⟩ : syracuseStep 3428507 = 5142761) B5142761
theorem B2285671 : Blo 2285435 2285671 := bstep (se 1 (by rfl) ⟨1714253, by rfl⟩ : syracuseStep 2285671 = 3428507) B3428507
theorem B2571385 : Blo 2285435 2571385 := bbase (se 2 (by rfl) ⟨964269, by rfl⟩ : syracuseStep 2571385 = 1928539) (by norm_num)
theorem B3428513 : Blo 2285435 3428513 := bstep (se 2 (by rfl) ⟨1285692, by rfl⟩ : syracuseStep 3428513 = 2571385) B2571385
theorem B2285675 : Blo 2285435 2285675 := bstep (se 1 (by rfl) ⟨1714256, by rfl⟩ : syracuseStep 2285675 = 3428513) B3428513
theorem B2606473 : Blo 2285435 2606473 := bbase (se 2 (by rfl) ⟨977427, by rfl⟩ : syracuseStep 2606473 = 1954855) (by norm_num)
theorem B3475297 : Blo 2285435 3475297 := bstep (se 2 (by rfl) ⟨1303236, by rfl⟩ : syracuseStep 3475297 = 2606473) B2606473
theorem B4633729 : Blo 2285435 4633729 := bstep (se 2 (by rfl) ⟨1737648, by rfl⟩ : syracuseStep 4633729 = 3475297) B3475297
theorem B24713221 : Blo 2285435 24713221 := bstep (se 4 (by rfl) ⟨2316864, by rfl⟩ : syracuseStep 24713221 = 4633729) B4633729
theorem B32950961 : Blo 2285435 32950961 := bstep (se 2 (by rfl) ⟨12356610, by rfl⟩ : syracuseStep 32950961 = 24713221) B24713221
theorem B21967307 : Blo 2285435 21967307 := bstep (se 1 (by rfl) ⟨16475480, by rfl⟩ : syracuseStep 21967307 = 32950961) B32950961
theorem B14644871 : Blo 2285435 14644871 := bstep (se 1 (by rfl) ⟨10983653, by rfl⟩ : syracuseStep 14644871 = 21967307) B21967307
theorem B9763247 : Blo 2285435 9763247 := bstep (se 1 (by rfl) ⟨7322435, by rfl⟩ : syracuseStep 9763247 = 14644871) B14644871
theorem B6508831 : Blo 2285435 6508831 := bstep (se 1 (by rfl) ⟨4881623, by rfl⟩ : syracuseStep 6508831 = 9763247) B9763247
theorem B8678441 : Blo 2285435 8678441 := bstep (se 2 (by rfl) ⟨3254415, by rfl⟩ : syracuseStep 8678441 = 6508831) B6508831
theorem B5785627 : Blo 2285435 5785627 := bstep (se 1 (by rfl) ⟨4339220, by rfl⟩ : syracuseStep 5785627 = 8678441) B8678441
theorem B7714169 : Blo 2285435 7714169 := bstep (se 2 (by rfl) ⟨2892813, by rfl⟩ : syracuseStep 7714169 = 5785627) B5785627
theorem B5142779 : Blo 2285435 5142779 := bstep (se 1 (by rfl) ⟨3857084, by rfl⟩ : syracuseStep 5142779 = 7714169) B7714169
theorem B3428519 : Blo 2285435 3428519 := bstep (se 1 (by rfl) ⟨2571389, by rfl⟩ : syracuseStep 3428519 = 5142779) B5142779
theorem B2285679 : Blo 2285435 2285679 := bstep (se 1 (by rfl) ⟨1714259, by rfl⟩ : syracuseStep 2285679 = 3428519) B3428519
theorem B3428525 : Blo 2285435 3428525 := bbase (se 3 (by rfl) ⟨642848, by rfl⟩ : syracuseStep 3428525 = 1285697) (by norm_num)
theorem B2285683 : Blo 2285435 2285683 := bstep (se 1 (by rfl) ⟨1714262, by rfl⟩ : syracuseStep 2285683 = 3428525) B3428525
theorem B5142797 : Blo 2285435 5142797 := bbase (se 3 (by rfl) ⟨964274, by rfl⟩ : syracuseStep 5142797 = 1928549) (by norm_num)
theorem B3428531 : Blo 2285435 3428531 := bstep (se 1 (by rfl) ⟨2571398, by rfl⟩ : syracuseStep 3428531 = 5142797) B5142797
theorem B2285687 : Blo 2285435 2285687 := bstep (se 1 (by rfl) ⟨1714265, by rfl⟩ : syracuseStep 2285687 = 3428531) B3428531
theorem B2892829 : Blo 2285435 2892829 := bbase (se 3 (by rfl) ⟨542405, by rfl⟩ : syracuseStep 2892829 = 1084811) (by norm_num)
theorem B3857105 : Blo 2285435 3857105 := bstep (se 2 (by rfl) ⟨1446414, by rfl⟩ : syracuseStep 3857105 = 2892829) B2892829
theorem B2571403 : Blo 2285435 2571403 := bstep (se 1 (by rfl) ⟨1928552, by rfl⟩ : syracuseStep 2571403 = 3857105) B3857105
theorem B3428537 : Blo 2285435 3428537 := bstep (se 2 (by rfl) ⟨1285701, by rfl⟩ : syracuseStep 3428537 = 2571403) B2571403
theorem B2285691 : Blo 2285435 2285691 := bstep (se 1 (by rfl) ⟨1714268, by rfl⟩ : syracuseStep 2285691 = 3428537) B3428537
theorem B2316881 : Blo 2285435 2316881 := bbase (se 2 (by rfl) ⟨868830, by rfl⟩ : syracuseStep 2316881 = 1737661) (by norm_num)
theorem B6178349 : Blo 2285435 6178349 := bstep (se 3 (by rfl) ⟨1158440, by rfl⟩ : syracuseStep 6178349 = 2316881) B2316881
theorem B4118899 : Blo 2285435 4118899 := bstep (se 1 (by rfl) ⟨3089174, by rfl⟩ : syracuseStep 4118899 = 6178349) B6178349
theorem B5491865 : Blo 2285435 5491865 := bstep (se 2 (by rfl) ⟨2059449, by rfl⟩ : syracuseStep 5491865 = 4118899) B4118899
theorem B3661243 : Blo 2285435 3661243 := bstep (se 1 (by rfl) ⟨2745932, by rfl⟩ : syracuseStep 3661243 = 5491865) B5491865
theorem B19526629 : Blo 2285435 19526629 := bstep (se 4 (by rfl) ⟨1830621, by rfl⟩ : syracuseStep 19526629 = 3661243) B3661243
theorem B26035505 : Blo 2285435 26035505 := bstep (se 2 (by rfl) ⟨9763314, by rfl⟩ : syracuseStep 26035505 = 19526629) B19526629
theorem B17357003 : Blo 2285435 17357003 := bstep (se 1 (by rfl) ⟨13017752, by rfl⟩ : syracuseStep 17357003 = 26035505) B26035505
theorem B11571335 : Blo 2285435 11571335 := bstep (se 1 (by rfl) ⟨8678501, by rfl⟩ : syracuseStep 11571335 = 17357003) B17357003
theorem B7714223 : Blo 2285435 7714223 := bstep (se 1 (by rfl) ⟨5785667, by rfl⟩ : syracuseStep 7714223 = 11571335) B11571335
theorem B5142815 : Blo 2285435 5142815 := bstep (se 1 (by rfl) ⟨3857111, by rfl⟩ : syracuseStep 5142815 = 7714223) B7714223
theorem B3428543 : Blo 2285435 3428543 := bstep (se 1 (by rfl) ⟨2571407, by rfl⟩ : syracuseStep 3428543 = 5142815) B5142815
theorem B2285695 : Blo 2285435 2285695 := bstep (se 1 (by rfl) ⟨1714271, by rfl⟩ : syracuseStep 2285695 = 3428543) B3428543
theorem B3428549 : Blo 2285435 3428549 := bbase (se 4 (by rfl) ⟨321426, by rfl⟩ : syracuseStep 3428549 = 642853) (by norm_num)
theorem B2285699 : Blo 2285435 2285699 := bstep (se 1 (by rfl) ⟨1714274, by rfl⟩ : syracuseStep 2285699 = 3428549) B3428549
theorem B3857125 : Blo 2285435 3857125 := bbase (se 4 (by rfl) ⟨361605, by rfl⟩ : syracuseStep 3857125 = 723211) (by norm_num)
theorem B5142833 : Blo 2285435 5142833 := bstep (se 2 (by rfl) ⟨1928562, by rfl⟩ : syracuseStep 5142833 = 3857125) B3857125
theorem B3428555 : Blo 2285435 3428555 := bstep (se 1 (by rfl) ⟨2571416, by rfl⟩ : syracuseStep 3428555 = 5142833) B5142833
theorem B2285703 : Blo 2285435 2285703 := bstep (se 1 (by rfl) ⟨1714277, by rfl⟩ : syracuseStep 2285703 = 3428555) B3428555
theorem B2571421 : Blo 2285435 2571421 := bbase (se 3 (by rfl) ⟨482141, by rfl⟩ : syracuseStep 2571421 = 964283) (by norm_num)
theorem B3428561 : Blo 2285435 3428561 := bstep (se 2 (by rfl) ⟨1285710, by rfl⟩ : syracuseStep 3428561 = 2571421) B2571421
theorem B2285707 : Blo 2285435 2285707 := bstep (se 1 (by rfl) ⟨1714280, by rfl⟩ : syracuseStep 2285707 = 3428561) B3428561
theorem B7714277 : Blo 2285435 7714277 := bbase (se 4 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 7714277 = 1446427) (by norm_num)
theorem B5142851 : Blo 2285435 5142851 := bstep (se 1 (by rfl) ⟨3857138, by rfl⟩ : syracuseStep 5142851 = 7714277) B7714277
theorem B3428567 : Blo 2285435 3428567 := bstep (se 1 (by rfl) ⟨2571425, by rfl⟩ : syracuseStep 3428567 = 5142851) B5142851
theorem B2285711 : Blo 2285435 2285711 := bstep (se 1 (by rfl) ⟨1714283, by rfl⟩ : syracuseStep 2285711 = 3428567) B3428567
theorem B3428573 : Blo 2285435 3428573 := bbase (se 3 (by rfl) ⟨642857, by rfl⟩ : syracuseStep 3428573 = 1285715) (by norm_num)
theorem B2285715 : Blo 2285435 2285715 := bstep (se 1 (by rfl) ⟨1714286, by rfl⟩ : syracuseStep 2285715 = 3428573) B3428573
theorem B5142869 : Blo 2285435 5142869 := bbase (se 10 (by rfl) ⟨7533, by rfl⟩ : syracuseStep 5142869 = 15067) (by norm_num)
theorem B3428579 : Blo 2285435 3428579 := bstep (se 1 (by rfl) ⟨2571434, by rfl⟩ : syracuseStep 3428579 = 5142869) B5142869
theorem B2285719 : Blo 2285435 2285719 := bstep (se 1 (by rfl) ⟨1714289, by rfl⟩ : syracuseStep 2285719 = 3428579) B3428579
theorem B7819573 : Blo 2285435 7819573 := bbase (se 5 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 7819573 = 733085) (by norm_num)
theorem B10426097 : Blo 2285435 10426097 := bstep (se 2 (by rfl) ⟨3909786, by rfl⟩ : syracuseStep 10426097 = 7819573) B7819573
theorem B6950731 : Blo 2285435 6950731 := bstep (se 1 (by rfl) ⟨5213048, by rfl⟩ : syracuseStep 6950731 = 10426097) B10426097
theorem B9267641 : Blo 2285435 9267641 := bstep (se 2 (by rfl) ⟨3475365, by rfl⟩ : syracuseStep 9267641 = 6950731) B6950731
theorem B6178427 : Blo 2285435 6178427 := bstep (se 1 (by rfl) ⟨4633820, by rfl⟩ : syracuseStep 6178427 = 9267641) B9267641
theorem B4118951 : Blo 2285435 4118951 := bstep (se 1 (by rfl) ⟨3089213, by rfl⟩ : syracuseStep 4118951 = 6178427) B6178427
theorem B2745967 : Blo 2285435 2745967 := bstep (se 1 (by rfl) ⟨2059475, by rfl⟩ : syracuseStep 2745967 = 4118951) B4118951
theorem B3661289 : Blo 2285435 3661289 := bstep (se 2 (by rfl) ⟨1372983, by rfl⟩ : syracuseStep 3661289 = 2745967) B2745967
theorem B2440859 : Blo 2285435 2440859 := bstep (se 1 (by rfl) ⟨1830644, by rfl⟩ : syracuseStep 2440859 = 3661289) B3661289
theorem B6508957 : Blo 2285435 6508957 := bstep (se 3 (by rfl) ⟨1220429, by rfl⟩ : syracuseStep 6508957 = 2440859) B2440859
theorem B8678609 : Blo 2285435 8678609 := bstep (se 2 (by rfl) ⟨3254478, by rfl⟩ : syracuseStep 8678609 = 6508957) B6508957
theorem B5785739 : Blo 2285435 5785739 := bstep (se 1 (by rfl) ⟨4339304, by rfl⟩ : syracuseStep 5785739 = 8678609) B8678609
theorem B3857159 : Blo 2285435 3857159 := bstep (se 1 (by rfl) ⟨2892869, by rfl⟩ : syracuseStep 3857159 = 5785739) B5785739
theorem B2571439 : Blo 2285435 2571439 := bstep (se 1 (by rfl) ⟨1928579, by rfl⟩ : syracuseStep 2571439 = 3857159) B3857159
theorem B3428585 : Blo 2285435 3428585 := bstep (se 2 (by rfl) ⟨1285719, by rfl⟩ : syracuseStep 3428585 = 2571439) B2571439
theorem B2285723 : Blo 2285435 2285723 := bstep (se 1 (by rfl) ⟨1714292, by rfl⟩ : syracuseStep 2285723 = 3428585) B3428585
theorem B2316913 : Blo 2285435 2316913 := bbase (se 2 (by rfl) ⟨868842, by rfl⟩ : syracuseStep 2316913 = 1737685) (by norm_num)
theorem B12356869 : Blo 2285435 12356869 := bstep (se 4 (by rfl) ⟨1158456, by rfl⟩ : syracuseStep 12356869 = 2316913) B2316913
theorem B16475825 : Blo 2285435 16475825 := bstep (se 2 (by rfl) ⟨6178434, by rfl⟩ : syracuseStep 16475825 = 12356869) B12356869
theorem B43935533 : Blo 2285435 43935533 := bstep (se 3 (by rfl) ⟨8237912, by rfl⟩ : syracuseStep 43935533 = 16475825) B16475825
theorem B29290355 : Blo 2285435 29290355 := bstep (se 1 (by rfl) ⟨21967766, by rfl⟩ : syracuseStep 29290355 = 43935533) B43935533
theorem B19526903 : Blo 2285435 19526903 := bstep (se 1 (by rfl) ⟨14645177, by rfl⟩ : syracuseStep 19526903 = 29290355) B29290355
theorem B13017935 : Blo 2285435 13017935 := bstep (se 1 (by rfl) ⟨9763451, by rfl⟩ : syracuseStep 13017935 = 19526903) B19526903
theorem B8678623 : Blo 2285435 8678623 := bstep (se 1 (by rfl) ⟨6508967, by rfl⟩ : syracuseStep 8678623 = 13017935) B13017935
theorem B11571497 : Blo 2285435 11571497 := bstep (se 2 (by rfl) ⟨4339311, by rfl⟩ : syracuseStep 11571497 = 8678623) B8678623
theorem B7714331 : Blo 2285435 7714331 := bstep (se 1 (by rfl) ⟨5785748, by rfl⟩ : syracuseStep 7714331 = 11571497) B11571497
theorem B5142887 : Blo 2285435 5142887 := bstep (se 1 (by rfl) ⟨3857165, by rfl⟩ : syracuseStep 5142887 = 7714331) B7714331
theorem B3428591 : Blo 2285435 3428591 := bstep (se 1 (by rfl) ⟨2571443, by rfl⟩ : syracuseStep 3428591 = 5142887) B5142887
theorem B2285727 : Blo 2285435 2285727 := bstep (se 1 (by rfl) ⟨1714295, by rfl⟩ : syracuseStep 2285727 = 3428591) B3428591
theorem B3428597 : Blo 2285435 3428597 := bbase (se 5 (by rfl) ⟨160715, by rfl⟩ : syracuseStep 3428597 = 321431) (by norm_num)
theorem B2285731 : Blo 2285435 2285731 := bstep (se 1 (by rfl) ⟨1714298, by rfl⟩ : syracuseStep 2285731 = 3428597) B3428597
theorem B3909805 : Blo 2285435 3909805 := bbase (se 3 (by rfl) ⟨733088, by rfl⟩ : syracuseStep 3909805 = 1466177) (by norm_num)
theorem B83409173 : Blo 2285435 83409173 := bstep (se 6 (by rfl) ⟨1954902, by rfl⟩ : syracuseStep 83409173 = 3909805) B3909805
theorem B55606115 : Blo 2285435 55606115 := bstep (se 1 (by rfl) ⟨41704586, by rfl⟩ : syracuseStep 55606115 = 83409173) B83409173
theorem B37070743 : Blo 2285435 37070743 := bstep (se 1 (by rfl) ⟨27803057, by rfl⟩ : syracuseStep 37070743 = 55606115) B55606115
theorem B49427657 : Blo 2285435 49427657 := bstep (se 2 (by rfl) ⟨18535371, by rfl⟩ : syracuseStep 49427657 = 37070743) B37070743
theorem B32951771 : Blo 2285435 32951771 := bstep (se 1 (by rfl) ⟨24713828, by rfl⟩ : syracuseStep 32951771 = 49427657) B49427657
theorem B21967847 : Blo 2285435 21967847 := bstep (se 1 (by rfl) ⟨16475885, by rfl⟩ : syracuseStep 21967847 = 32951771) B32951771
theorem B14645231 : Blo 2285435 14645231 := bstep (se 1 (by rfl) ⟨10983923, by rfl⟩ : syracuseStep 14645231 = 21967847) B21967847
theorem B9763487 : Blo 2285435 9763487 := bstep (se 1 (by rfl) ⟨7322615, by rfl⟩ : syracuseStep 9763487 = 14645231) B14645231
theorem B6508991 : Blo 2285435 6508991 := bstep (se 1 (by rfl) ⟨4881743, by rfl⟩ : syracuseStep 6508991 = 9763487) B9763487
theorem B4339327 : Blo 2285435 4339327 := bstep (se 1 (by rfl) ⟨3254495, by rfl⟩ : syracuseStep 4339327 = 6508991) B6508991
theorem B5785769 : Blo 2285435 5785769 := bstep (se 2 (by rfl) ⟨2169663, by rfl⟩ : syracuseStep 5785769 = 4339327) B4339327
theorem B3857179 : Blo 2285435 3857179 := bstep (se 1 (by rfl) ⟨2892884, by rfl⟩ : syracuseStep 3857179 = 5785769) B5785769
theorem B5142905 : Blo 2285435 5142905 := bstep (se 2 (by rfl) ⟨1928589, by rfl⟩ : syracuseStep 5142905 = 3857179) B3857179
theorem B3428603 : Blo 2285435 3428603 := bstep (se 1 (by rfl) ⟨2571452, by rfl⟩ : syracuseStep 3428603 = 5142905) B5142905
theorem B2285735 : Blo 2285435 2285735 := bstep (se 1 (by rfl) ⟨1714301, by rfl⟩ : syracuseStep 2285735 = 3428603) B3428603
theorem B2571457 : Blo 2285435 2571457 := bbase (se 2 (by rfl) ⟨964296, by rfl⟩ : syracuseStep 2571457 = 1928593) (by norm_num)
theorem B3428609 : Blo 2285435 3428609 := bstep (se 2 (by rfl) ⟨1285728, by rfl⟩ : syracuseStep 3428609 = 2571457) B2571457
theorem B2285739 : Blo 2285435 2285739 := bstep (se 1 (by rfl) ⟨1714304, by rfl⟩ : syracuseStep 2285739 = 3428609) B3428609
theorem B5785789 : Blo 2285435 5785789 := bbase (se 3 (by rfl) ⟨1084835, by rfl⟩ : syracuseStep 5785789 = 2169671) (by norm_num)
theorem B7714385 : Blo 2285435 7714385 := bstep (se 2 (by rfl) ⟨2892894, by rfl⟩ : syracuseStep 7714385 = 5785789) B5785789
theorem B5142923 : Blo 2285435 5142923 := bstep (se 1 (by rfl) ⟨3857192, by rfl⟩ : syracuseStep 5142923 = 7714385) B7714385
theorem B3428615 : Blo 2285435 3428615 := bstep (se 1 (by rfl) ⟨2571461, by rfl⟩ : syracuseStep 3428615 = 5142923) B5142923
theorem B2285743 : Blo 2285435 2285743 := bstep (se 1 (by rfl) ⟨1714307, by rfl⟩ : syracuseStep 2285743 = 3428615) B3428615
theorem B3428621 : Blo 2285435 3428621 := bbase (se 3 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 3428621 = 1285733) (by norm_num)
theorem B2285747 : Blo 2285435 2285747 := bstep (se 1 (by rfl) ⟨1714310, by rfl⟩ : syracuseStep 2285747 = 3428621) B3428621
theorem B5142941 : Blo 2285435 5142941 := bbase (se 3 (by rfl) ⟨964301, by rfl⟩ : syracuseStep 5142941 = 1928603) (by norm_num)
theorem B3428627 : Blo 2285435 3428627 := bstep (se 1 (by rfl) ⟨2571470, by rfl⟩ : syracuseStep 3428627 = 5142941) B5142941
theorem B2285751 : Blo 2285435 2285751 := bstep (se 1 (by rfl) ⟨1714313, by rfl⟩ : syracuseStep 2285751 = 3428627) B3428627
theorem B3857213 : Blo 2285435 3857213 := bbase (se 3 (by rfl) ⟨723227, by rfl⟩ : syracuseStep 3857213 = 1446455) (by norm_num)
theorem B2571475 : Blo 2285435 2571475 := bstep (se 1 (by rfl) ⟨1928606, by rfl⟩ : syracuseStep 2571475 = 3857213) B3857213
theorem B3428633 : Blo 2285435 3428633 := bstep (se 2 (by rfl) ⟨1285737, by rfl⟩ : syracuseStep 3428633 = 2571475) B2571475
theorem B2285755 : Blo 2285435 2285755 := bstep (se 1 (by rfl) ⟨1714316, by rfl⟩ : syracuseStep 2285755 = 3428633) B3428633
theorem B2440897 : Blo 2285435 2440897 := bbase (se 2 (by rfl) ⟨915336, by rfl⟩ : syracuseStep 2440897 = 1830673) (by norm_num)
theorem B13018117 : Blo 2285435 13018117 := bstep (se 4 (by rfl) ⟨1220448, by rfl⟩ : syracuseStep 13018117 = 2440897) B2440897
theorem B17357489 : Blo 2285435 17357489 := bstep (se 2 (by rfl) ⟨6509058, by rfl⟩ : syracuseStep 17357489 = 13018117) B13018117
theorem B11571659 : Blo 2285435 11571659 := bstep (se 1 (by rfl) ⟨8678744, by rfl⟩ : syracuseStep 11571659 = 17357489) B17357489
theorem B7714439 : Blo 2285435 7714439 := bstep (se 1 (by rfl) ⟨5785829, by rfl⟩ : syracuseStep 7714439 = 11571659) B11571659
theorem B5142959 : Blo 2285435 5142959 := bstep (se 1 (by rfl) ⟨3857219, by rfl⟩ : syracuseStep 5142959 = 7714439) B7714439
theorem B3428639 : Blo 2285435 3428639 := bstep (se 1 (by rfl) ⟨2571479, by rfl⟩ : syracuseStep 3428639 = 5142959) B5142959
theorem B2285759 : Blo 2285435 2285759 := bstep (se 1 (by rfl) ⟨1714319, by rfl⟩ : syracuseStep 2285759 = 3428639) B3428639
theorem B3428645 : Blo 2285435 3428645 := bbase (se 4 (by rfl) ⟨321435, by rfl⟩ : syracuseStep 3428645 = 642871) (by norm_num)
theorem B2285763 : Blo 2285435 2285763 := bstep (se 1 (by rfl) ⟨1714322, by rfl⟩ : syracuseStep 2285763 = 3428645) B3428645
theorem B2892925 : Blo 2285435 2892925 := bbase (se 3 (by rfl) ⟨542423, by rfl⟩ : syracuseStep 2892925 = 1084847) (by norm_num)
theorem B3857233 : Blo 2285435 3857233 := bstep (se 2 (by rfl) ⟨1446462, by rfl⟩ : syracuseStep 3857233 = 2892925) B2892925
theorem B5142977 : Blo 2285435 5142977 := bstep (se 2 (by rfl) ⟨1928616, by rfl⟩ : syracuseStep 5142977 = 3857233) B3857233
theorem B3428651 : Blo 2285435 3428651 := bstep (se 1 (by rfl) ⟨2571488, by rfl⟩ : syracuseStep 3428651 = 5142977) B5142977
theorem B2285767 : Blo 2285435 2285767 := bstep (se 1 (by rfl) ⟨1714325, by rfl⟩ : syracuseStep 2285767 = 3428651) B3428651
theorem B2571493 : Blo 2285435 2571493 := bbase (se 4 (by rfl) ⟨241077, by rfl⟩ : syracuseStep 2571493 = 482155) (by norm_num)
theorem B3428657 : Blo 2285435 3428657 := bstep (se 2 (by rfl) ⟨1285746, by rfl⟩ : syracuseStep 3428657 = 2571493) B2571493
theorem B2285771 : Blo 2285435 2285771 := bstep (se 1 (by rfl) ⟨1714328, by rfl⟩ : syracuseStep 2285771 = 3428657) B3428657
theorem B4881829 : Blo 2285435 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B6509105 : Blo 2285435 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B4339403 : Blo 2285435 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B2892935 : Blo 2285435 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B7714493 : Blo 2285435 7714493 := bstep (se 3 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 7714493 = 2892935) B2892935
theorem B5142995 : Blo 2285435 5142995 := bstep (se 1 (by rfl) ⟨3857246, by rfl⟩ : syracuseStep 5142995 = 7714493) B7714493
theorem B3428663 : Blo 2285435 3428663 := bstep (se 1 (by rfl) ⟨2571497, by rfl⟩ : syracuseStep 3428663 = 5142995) B5142995
theorem B2285775 : Blo 2285435 2285775 := bstep (se 1 (by rfl) ⟨1714331, by rfl⟩ : syracuseStep 2285775 = 3428663) B3428663
theorem B3428669 : Blo 2285435 3428669 := bbase (se 3 (by rfl) ⟨642875, by rfl⟩ : syracuseStep 3428669 = 1285751) (by norm_num)
theorem B2285779 : Blo 2285435 2285779 := bstep (se 1 (by rfl) ⟨1714334, by rfl⟩ : syracuseStep 2285779 = 3428669) B3428669
theorem B5143013 : Blo 2285435 5143013 := bbase (se 4 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 5143013 = 964315) (by norm_num)
theorem B3428675 : Blo 2285435 3428675 := bstep (se 1 (by rfl) ⟨2571506, by rfl⟩ : syracuseStep 3428675 = 5143013) B5143013
theorem B2285783 : Blo 2285435 2285783 := bstep (se 1 (by rfl) ⟨1714337, by rfl⟩ : syracuseStep 2285783 = 3428675) B3428675
theorem B5785901 : Blo 2285435 5785901 := bbase (se 3 (by rfl) ⟨1084856, by rfl⟩ : syracuseStep 5785901 = 2169713) (by norm_num)
theorem B3857267 : Blo 2285435 3857267 := bstep (se 1 (by rfl) ⟨2892950, by rfl⟩ : syracuseStep 3857267 = 5785901) B5785901
theorem B2571511 : Blo 2285435 2571511 := bstep (se 1 (by rfl) ⟨1928633, by rfl⟩ : syracuseStep 2571511 = 3857267) B3857267
theorem B3428681 : Blo 2285435 3428681 := bstep (se 2 (by rfl) ⟨1285755, by rfl⟩ : syracuseStep 3428681 = 2571511) B2571511
theorem B2285787 : Blo 2285435 2285787 := bstep (se 1 (by rfl) ⟨1714340, by rfl⟩ : syracuseStep 2285787 = 3428681) B3428681
theorem B4633957 : Blo 2285435 4633957 := bbase (se 4 (by rfl) ⟨434433, by rfl⟩ : syracuseStep 4633957 = 868867) (by norm_num)
theorem B6178609 : Blo 2285435 6178609 := bstep (se 2 (by rfl) ⟨2316978, by rfl⟩ : syracuseStep 6178609 = 4633957) B4633957
theorem B8238145 : Blo 2285435 8238145 := bstep (se 2 (by rfl) ⟨3089304, by rfl⟩ : syracuseStep 8238145 = 6178609) B6178609
theorem B10984193 : Blo 2285435 10984193 := bstep (se 2 (by rfl) ⟨4119072, by rfl⟩ : syracuseStep 10984193 = 8238145) B8238145
theorem B7322795 : Blo 2285435 7322795 := bstep (se 1 (by rfl) ⟨5492096, by rfl⟩ : syracuseStep 7322795 = 10984193) B10984193
theorem B4881863 : Blo 2285435 4881863 := bstep (se 1 (by rfl) ⟨3661397, by rfl⟩ : syracuseStep 4881863 = 7322795) B7322795
theorem B3254575 : Blo 2285435 3254575 := bstep (se 1 (by rfl) ⟨2440931, by rfl⟩ : syracuseStep 3254575 = 4881863) B4881863
theorem B4339433 : Blo 2285435 4339433 := bstep (se 2 (by rfl) ⟨1627287, by rfl⟩ : syracuseStep 4339433 = 3254575) B3254575
theorem B11571821 : Blo 2285435 11571821 := bstep (se 3 (by rfl) ⟨2169716, by rfl⟩ : syracuseStep 11571821 = 4339433) B4339433
theorem B7714547 : Blo 2285435 7714547 := bstep (se 1 (by rfl) ⟨5785910, by rfl⟩ : syracuseStep 7714547 = 11571821) B11571821
theorem B5143031 : Blo 2285435 5143031 := bstep (se 1 (by rfl) ⟨3857273, by rfl⟩ : syracuseStep 5143031 = 7714547) B7714547
theorem B3428687 : Blo 2285435 3428687 := bstep (se 1 (by rfl) ⟨2571515, by rfl⟩ : syracuseStep 3428687 = 5143031) B5143031
theorem B2285791 : Blo 2285435 2285791 := bstep (se 1 (by rfl) ⟨1714343, by rfl⟩ : syracuseStep 2285791 = 3428687) B3428687
theorem B3428693 : Blo 2285435 3428693 := bbase (se 10 (by rfl) ⟨5022, by rfl⟩ : syracuseStep 3428693 = 10045) (by norm_num)
theorem B2285795 : Blo 2285435 2285795 := bstep (se 1 (by rfl) ⟨1714346, by rfl⟩ : syracuseStep 2285795 = 3428693) B3428693
theorem B6509173 : Blo 2285435 6509173 := bbase (se 5 (by rfl) ⟨305117, by rfl⟩ : syracuseStep 6509173 = 610235) (by norm_num)
theorem B8678897 : Blo 2285435 8678897 := bstep (se 2 (by rfl) ⟨3254586, by rfl⟩ : syracuseStep 8678897 = 6509173) B6509173
theorem B5785931 : Blo 2285435 5785931 := bstep (se 1 (by rfl) ⟨4339448, by rfl⟩ : syracuseStep 5785931 = 8678897) B8678897
theorem B3857287 : Blo 2285435 3857287 := bstep (se 1 (by rfl) ⟨2892965, by rfl⟩ : syracuseStep 3857287 = 5785931) B5785931
theorem B5143049 : Blo 2285435 5143049 := bstep (se 2 (by rfl) ⟨1928643, by rfl⟩ : syracuseStep 5143049 = 3857287) B3857287
theorem B3428699 : Blo 2285435 3428699 := bstep (se 1 (by rfl) ⟨2571524, by rfl⟩ : syracuseStep 3428699 = 5143049) B5143049
theorem B2285799 : Blo 2285435 2285799 := bstep (se 1 (by rfl) ⟨1714349, by rfl⟩ : syracuseStep 2285799 = 3428699) B3428699
theorem B2571529 : Blo 2285435 2571529 := bbase (se 2 (by rfl) ⟨964323, by rfl⟩ : syracuseStep 2571529 = 1928647) (by norm_num)
theorem B3428705 : Blo 2285435 3428705 := bstep (se 2 (by rfl) ⟨1285764, by rfl⟩ : syracuseStep 3428705 = 2571529) B2571529
theorem B2285803 : Blo 2285435 2285803 := bstep (se 1 (by rfl) ⟨1714352, by rfl⟩ : syracuseStep 2285803 = 3428705) B3428705
theorem B4119101 : Blo 2285435 4119101 := bbase (se 3 (by rfl) ⟨772331, by rfl⟩ : syracuseStep 4119101 = 1544663) (by norm_num)
theorem B2746067 : Blo 2285435 2746067 := bstep (se 1 (by rfl) ⟨2059550, by rfl⟩ : syracuseStep 2746067 = 4119101) B4119101
theorem B29291381 : Blo 2285435 29291381 := bstep (se 5 (by rfl) ⟨1373033, by rfl⟩ : syracuseStep 29291381 = 2746067) B2746067
theorem B19527587 : Blo 2285435 19527587 := bstep (se 1 (by rfl) ⟨14645690, by rfl⟩ : syracuseStep 19527587 = 29291381) B29291381
theorem B13018391 : Blo 2285435 13018391 := bstep (se 1 (by rfl) ⟨9763793, by rfl⟩ : syracuseStep 13018391 = 19527587) B19527587
theorem B8678927 : Blo 2285435 8678927 := bstep (se 1 (by rfl) ⟨6509195, by rfl⟩ : syracuseStep 8678927 = 13018391) B13018391
theorem B5785951 : Blo 2285435 5785951 := bstep (se 1 (by rfl) ⟨4339463, by rfl⟩ : syracuseStep 5785951 = 8678927) B8678927
theorem B7714601 : Blo 2285435 7714601 := bstep (se 2 (by rfl) ⟨2892975, by rfl⟩ : syracuseStep 7714601 = 5785951) B5785951
theorem B5143067 : Blo 2285435 5143067 := bstep (se 1 (by rfl) ⟨3857300, by rfl⟩ : syracuseStep 5143067 = 7714601) B7714601
theorem B3428711 : Blo 2285435 3428711 := bstep (se 1 (by rfl) ⟨2571533, by rfl⟩ : syracuseStep 3428711 = 5143067) B5143067
theorem B2285807 : Blo 2285435 2285807 := bstep (se 1 (by rfl) ⟨1714355, by rfl⟩ : syracuseStep 2285807 = 3428711) B3428711
theorem B3428717 : Blo 2285435 3428717 := bbase (se 3 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 3428717 = 1285769) (by norm_num)
theorem B2285811 : Blo 2285435 2285811 := bstep (se 1 (by rfl) ⟨1714358, by rfl⟩ : syracuseStep 2285811 = 3428717) B3428717
theorem B5143085 : Blo 2285435 5143085 := bbase (se 3 (by rfl) ⟨964328, by rfl⟩ : syracuseStep 5143085 = 1928657) (by norm_num)
theorem B3428723 : Blo 2285435 3428723 := bstep (se 1 (by rfl) ⟨2571542, by rfl⟩ : syracuseStep 3428723 = 5143085) B5143085
theorem B2285815 : Blo 2285435 2285815 := bstep (se 1 (by rfl) ⟨1714361, by rfl⟩ : syracuseStep 2285815 = 3428723) B3428723
theorem B7045861 : Blo 2285435 7045861 := bbase (se 4 (by rfl) ⟨660549, by rfl⟩ : syracuseStep 7045861 = 1321099) (by norm_num)
theorem B9394481 : Blo 2285435 9394481 := bstep (se 2 (by rfl) ⟨3522930, by rfl⟩ : syracuseStep 9394481 = 7045861) B7045861
theorem B25051949 : Blo 2285435 25051949 := bstep (se 3 (by rfl) ⟨4697240, by rfl⟩ : syracuseStep 25051949 = 9394481) B9394481
theorem B16701299 : Blo 2285435 16701299 := bstep (se 1 (by rfl) ⟨12525974, by rfl⟩ : syracuseStep 16701299 = 25051949) B25051949
theorem B11134199 : Blo 2285435 11134199 := bstep (se 1 (by rfl) ⟨8350649, by rfl⟩ : syracuseStep 11134199 = 16701299) B16701299
theorem B7422799 : Blo 2285435 7422799 := bstep (se 1 (by rfl) ⟨5567099, by rfl⟩ : syracuseStep 7422799 = 11134199) B11134199
theorem B9897065 : Blo 2285435 9897065 := bstep (se 2 (by rfl) ⟨3711399, by rfl⟩ : syracuseStep 9897065 = 7422799) B7422799
theorem B6598043 : Blo 2285435 6598043 := bstep (se 1 (by rfl) ⟨4948532, by rfl⟩ : syracuseStep 6598043 = 9897065) B9897065
theorem B4398695 : Blo 2285435 4398695 := bstep (se 1 (by rfl) ⟨3299021, by rfl⟩ : syracuseStep 4398695 = 6598043) B6598043
theorem B2932463 : Blo 2285435 2932463 := bstep (se 1 (by rfl) ⟨2199347, by rfl⟩ : syracuseStep 2932463 = 4398695) B4398695
theorem B7819901 : Blo 2285435 7819901 := bstep (se 3 (by rfl) ⟨1466231, by rfl⟩ : syracuseStep 7819901 = 2932463) B2932463
theorem B5213267 : Blo 2285435 5213267 := bstep (se 1 (by rfl) ⟨3909950, by rfl⟩ : syracuseStep 5213267 = 7819901) B7819901
theorem B3475511 : Blo 2285435 3475511 := bstep (se 1 (by rfl) ⟨2606633, by rfl⟩ : syracuseStep 3475511 = 5213267) B5213267
theorem B2317007 : Blo 2285435 2317007 := bstep (se 1 (by rfl) ⟨1737755, by rfl⟩ : syracuseStep 2317007 = 3475511) B3475511
theorem B6178685 : Blo 2285435 6178685 := bstep (se 3 (by rfl) ⟨1158503, by rfl⟩ : syracuseStep 6178685 = 2317007) B2317007
theorem B16476493 : Blo 2285435 16476493 := bstep (se 3 (by rfl) ⟨3089342, by rfl⟩ : syracuseStep 16476493 = 6178685) B6178685
theorem B21968657 : Blo 2285435 21968657 := bstep (se 2 (by rfl) ⟨8238246, by rfl⟩ : syracuseStep 21968657 = 16476493) B16476493
theorem B14645771 : Blo 2285435 14645771 := bstep (se 1 (by rfl) ⟨10984328, by rfl⟩ : syracuseStep 14645771 = 21968657) B21968657
theorem B9763847 : Blo 2285435 9763847 := bstep (se 1 (by rfl) ⟨7322885, by rfl⟩ : syracuseStep 9763847 = 14645771) B14645771
theorem B6509231 : Blo 2285435 6509231 := bstep (se 1 (by rfl) ⟨4881923, by rfl⟩ : syracuseStep 6509231 = 9763847) B9763847
theorem B4339487 : Blo 2285435 4339487 := bstep (se 1 (by rfl) ⟨3254615, by rfl⟩ : syracuseStep 4339487 = 6509231) B6509231
theorem B2892991 : Blo 2285435 2892991 := bstep (se 1 (by rfl) ⟨2169743, by rfl⟩ : syracuseStep 2892991 = 4339487) B4339487
theorem B3857321 : Blo 2285435 3857321 := bstep (se 2 (by rfl) ⟨1446495, by rfl⟩ : syracuseStep 3857321 = 2892991) B2892991
theorem B2571547 : Blo 2285435 2571547 := bstep (se 1 (by rfl) ⟨1928660, by rfl⟩ : syracuseStep 2571547 = 3857321) B3857321
theorem B3428729 : Blo 2285435 3428729 := bstep (se 2 (by rfl) ⟨1285773, by rfl⟩ : syracuseStep 3428729 = 2571547) B2571547
theorem B2285819 : Blo 2285435 2285819 := bstep (se 1 (by rfl) ⟨1714364, by rfl⟩ : syracuseStep 2285819 = 3428729) B3428729
theorem B39055445 : Blo 2285435 39055445 := bbase (se 8 (by rfl) ⟨228840, by rfl⟩ : syracuseStep 39055445 = 457681) (by norm_num)
theorem B26036963 : Blo 2285435 26036963 := bstep (se 1 (by rfl) ⟨19527722, by rfl⟩ : syracuseStep 26036963 = 39055445) B39055445
theorem B17357975 : Blo 2285435 17357975 := bstep (se 1 (by rfl) ⟨13018481, by rfl⟩ : syracuseStep 17357975 = 26036963) B26036963
theorem B11571983 : Blo 2285435 11571983 := bstep (se 1 (by rfl) ⟨8678987, by rfl⟩ : syracuseStep 11571983 = 17357975) B17357975
theorem B7714655 : Blo 2285435 7714655 := bstep (se 1 (by rfl) ⟨5785991, by rfl⟩ : syracuseStep 7714655 = 11571983) B11571983
theorem B5143103 : Blo 2285435 5143103 := bstep (se 1 (by rfl) ⟨3857327, by rfl⟩ : syracuseStep 5143103 = 7714655) B7714655
theorem B3428735 : Blo 2285435 3428735 := bstep (se 1 (by rfl) ⟨2571551, by rfl⟩ : syracuseStep 3428735 = 5143103) B5143103
theorem B2285823 : Blo 2285435 2285823 := bstep (se 1 (by rfl) ⟨1714367, by rfl⟩ : syracuseStep 2285823 = 3428735) B3428735
theorem B3428741 : Blo 2285435 3428741 := bbase (se 4 (by rfl) ⟨321444, by rfl⟩ : syracuseStep 3428741 = 642889) (by norm_num)
theorem B2285827 : Blo 2285435 2285827 := bstep (se 1 (by rfl) ⟨1714370, by rfl⟩ : syracuseStep 2285827 = 3428741) B3428741
theorem B3857341 : Blo 2285435 3857341 := bbase (se 3 (by rfl) ⟨723251, by rfl⟩ : syracuseStep 3857341 = 1446503) (by norm_num)
theorem B5143121 : Blo 2285435 5143121 := bstep (se 2 (by rfl) ⟨1928670, by rfl⟩ : syracuseStep 5143121 = 3857341) B3857341
theorem B3428747 : Blo 2285435 3428747 := bstep (se 1 (by rfl) ⟨2571560, by rfl⟩ : syracuseStep 3428747 = 5143121) B5143121
theorem B2285831 : Blo 2285435 2285831 := bstep (se 1 (by rfl) ⟨1714373, by rfl⟩ : syracuseStep 2285831 = 3428747) B3428747
theorem B2571565 : Blo 2285435 2571565 := bbase (se 3 (by rfl) ⟨482168, by rfl⟩ : syracuseStep 2571565 = 964337) (by norm_num)
theorem B3428753 : Blo 2285435 3428753 := bstep (se 2 (by rfl) ⟨1285782, by rfl⟩ : syracuseStep 3428753 = 2571565) B2571565
theorem B2285835 : Blo 2285435 2285835 := bstep (se 1 (by rfl) ⟨1714376, by rfl⟩ : syracuseStep 2285835 = 3428753) B3428753
theorem B7714709 : Blo 2285435 7714709 := bbase (se 6 (by rfl) ⟨180813, by rfl⟩ : syracuseStep 7714709 = 361627) (by norm_num)
theorem B5143139 : Blo 2285435 5143139 := bstep (se 1 (by rfl) ⟨3857354, by rfl⟩ : syracuseStep 5143139 = 7714709) B7714709
theorem B3428759 : Blo 2285435 3428759 := bstep (se 1 (by rfl) ⟨2571569, by rfl⟩ : syracuseStep 3428759 = 5143139) B5143139
theorem B2285839 : Blo 2285435 2285839 := bstep (se 1 (by rfl) ⟨1714379, by rfl⟩ : syracuseStep 2285839 = 3428759) B3428759
theorem B3428765 : Blo 2285435 3428765 := bbase (se 3 (by rfl) ⟨642893, by rfl⟩ : syracuseStep 3428765 = 1285787) (by norm_num)
theorem B2285843 : Blo 2285435 2285843 := bstep (se 1 (by rfl) ⟨1714382, by rfl⟩ : syracuseStep 2285843 = 3428765) B3428765
theorem B5143157 : Blo 2285435 5143157 := bbase (se 5 (by rfl) ⟨241085, by rfl⟩ : syracuseStep 5143157 = 482171) (by norm_num)
theorem B3428771 : Blo 2285435 3428771 := bstep (se 1 (by rfl) ⟨2571578, by rfl⟩ : syracuseStep 3428771 = 5143157) B5143157
theorem B2285847 : Blo 2285435 2285847 := bstep (se 1 (by rfl) ⟨1714385, by rfl⟩ : syracuseStep 2285847 = 3428771) B3428771
theorem B7045957 : Blo 2285435 7045957 := bbase (se 4 (by rfl) ⟨660558, by rfl⟩ : syracuseStep 7045957 = 1321117) (by norm_num)
theorem B37578437 : Blo 2285435 37578437 := bstep (se 4 (by rfl) ⟨3522978, by rfl⟩ : syracuseStep 37578437 = 7045957) B7045957
theorem B25052291 : Blo 2285435 25052291 := bstep (se 1 (by rfl) ⟨18789218, by rfl⟩ : syracuseStep 25052291 = 37578437) B37578437
theorem B16701527 : Blo 2285435 16701527 := bstep (se 1 (by rfl) ⟨12526145, by rfl⟩ : syracuseStep 16701527 = 25052291) B25052291
theorem B11134351 : Blo 2285435 11134351 := bstep (se 1 (by rfl) ⟨8350763, by rfl⟩ : syracuseStep 11134351 = 16701527) B16701527
theorem B14845801 : Blo 2285435 14845801 := bstep (se 2 (by rfl) ⟨5567175, by rfl⟩ : syracuseStep 14845801 = 11134351) B11134351
theorem B19794401 : Blo 2285435 19794401 := bstep (se 2 (by rfl) ⟨7422900, by rfl⟩ : syracuseStep 19794401 = 14845801) B14845801
theorem B13196267 : Blo 2285435 13196267 := bstep (se 1 (by rfl) ⟨9897200, by rfl⟩ : syracuseStep 13196267 = 19794401) B19794401
theorem B8797511 : Blo 2285435 8797511 := bstep (se 1 (by rfl) ⟨6598133, by rfl⟩ : syracuseStep 8797511 = 13196267) B13196267
theorem B5865007 : Blo 2285435 5865007 := bstep (se 1 (by rfl) ⟨4398755, by rfl⟩ : syracuseStep 5865007 = 8797511) B8797511
theorem B7820009 : Blo 2285435 7820009 := bstep (se 2 (by rfl) ⟨2932503, by rfl⟩ : syracuseStep 7820009 = 5865007) B5865007
theorem B5213339 : Blo 2285435 5213339 := bstep (se 1 (by rfl) ⟨3910004, by rfl⟩ : syracuseStep 5213339 = 7820009) B7820009
theorem B3475559 : Blo 2285435 3475559 := bstep (se 1 (by rfl) ⟨2606669, by rfl⟩ : syracuseStep 3475559 = 5213339) B5213339
theorem B9268157 : Blo 2285435 9268157 := bstep (se 3 (by rfl) ⟨1737779, by rfl⟩ : syracuseStep 9268157 = 3475559) B3475559
theorem B6178771 : Blo 2285435 6178771 := bstep (se 1 (by rfl) ⟨4634078, by rfl⟩ : syracuseStep 6178771 = 9268157) B9268157
theorem B8238361 : Blo 2285435 8238361 := bstep (se 2 (by rfl) ⟨3089385, by rfl⟩ : syracuseStep 8238361 = 6178771) B6178771
theorem B10984481 : Blo 2285435 10984481 := bstep (se 2 (by rfl) ⟨4119180, by rfl⟩ : syracuseStep 10984481 = 8238361) B8238361
theorem B7322987 : Blo 2285435 7322987 := bstep (se 1 (by rfl) ⟨5492240, by rfl⟩ : syracuseStep 7322987 = 10984481) B10984481
theorem B19527965 : Blo 2285435 19527965 := bstep (se 3 (by rfl) ⟨3661493, by rfl⟩ : syracuseStep 19527965 = 7322987) B7322987
theorem B13018643 : Blo 2285435 13018643 := bstep (se 1 (by rfl) ⟨9763982, by rfl⟩ : syracuseStep 13018643 = 19527965) B19527965
theorem B8679095 : Blo 2285435 8679095 := bstep (se 1 (by rfl) ⟨6509321, by rfl⟩ : syracuseStep 8679095 = 13018643) B13018643
theorem B5786063 : Blo 2285435 5786063 := bstep (se 1 (by rfl) ⟨4339547, by rfl⟩ : syracuseStep 5786063 = 8679095) B8679095
theorem B3857375 : Blo 2285435 3857375 := bstep (se 1 (by rfl) ⟨2893031, by rfl⟩ : syracuseStep 3857375 = 5786063) B5786063
theorem B2571583 : Blo 2285435 2571583 := bstep (se 1 (by rfl) ⟨1928687, by rfl⟩ : syracuseStep 2571583 = 3857375) B3857375
theorem B3428777 : Blo 2285435 3428777 := bstep (se 2 (by rfl) ⟨1285791, by rfl⟩ : syracuseStep 3428777 = 2571583) B2571583
theorem B2285851 : Blo 2285435 2285851 := bstep (se 1 (by rfl) ⟨1714388, by rfl⟩ : syracuseStep 2285851 = 3428777) B3428777
theorem B8679109 : Blo 2285435 8679109 := bbase (se 4 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 8679109 = 1627333) (by norm_num)
theorem B11572145 : Blo 2285435 11572145 := bstep (se 2 (by rfl) ⟨4339554, by rfl⟩ : syracuseStep 11572145 = 8679109) B8679109
theorem B7714763 : Blo 2285435 7714763 := bstep (se 1 (by rfl) ⟨5786072, by rfl⟩ : syracuseStep 7714763 = 11572145) B11572145
theorem B5143175 : Blo 2285435 5143175 := bstep (se 1 (by rfl) ⟨3857381, by rfl⟩ : syracuseStep 5143175 = 7714763) B7714763
theorem B3428783 : Blo 2285435 3428783 := bstep (se 1 (by rfl) ⟨2571587, by rfl⟩ : syracuseStep 3428783 = 5143175) B5143175
theorem B2285855 : Blo 2285435 2285855 := bstep (se 1 (by rfl) ⟨1714391, by rfl⟩ : syracuseStep 2285855 = 3428783) B3428783
theorem B3428789 : Blo 2285435 3428789 := bbase (se 5 (by rfl) ⟨160724, by rfl⟩ : syracuseStep 3428789 = 321449) (by norm_num)
theorem B2285859 : Blo 2285435 2285859 := bstep (se 1 (by rfl) ⟨1714394, by rfl⟩ : syracuseStep 2285859 = 3428789) B3428789
theorem B5786093 : Blo 2285435 5786093 := bbase (se 3 (by rfl) ⟨1084892, by rfl⟩ : syracuseStep 5786093 = 2169785) (by norm_num)
theorem B3857395 : Blo 2285435 3857395 := bstep (se 1 (by rfl) ⟨2893046, by rfl⟩ : syracuseStep 3857395 = 5786093) B5786093
theorem B5143193 : Blo 2285435 5143193 := bstep (se 2 (by rfl) ⟨1928697, by rfl⟩ : syracuseStep 5143193 = 3857395) B3857395
theorem B3428795 : Blo 2285435 3428795 := bstep (se 1 (by rfl) ⟨2571596, by rfl⟩ : syracuseStep 3428795 = 5143193) B5143193
theorem B2285863 : Blo 2285435 2285863 := bstep (se 1 (by rfl) ⟨1714397, by rfl⟩ : syracuseStep 2285863 = 3428795) B3428795
theorem B2571601 : Blo 2285435 2571601 := bbase (se 2 (by rfl) ⟨964350, by rfl⟩ : syracuseStep 2571601 = 1928701) (by norm_num)
theorem B3428801 : Blo 2285435 3428801 := bstep (se 2 (by rfl) ⟨1285800, by rfl⟩ : syracuseStep 3428801 = 2571601) B2571601
theorem B2285867 : Blo 2285435 2285867 := bstep (se 1 (by rfl) ⟨1714400, by rfl⟩ : syracuseStep 2285867 = 3428801) B3428801
theorem B2441017 : Blo 2285435 2441017 := bbase (se 2 (by rfl) ⟨915381, by rfl⟩ : syracuseStep 2441017 = 1830763) (by norm_num)
theorem B3254689 : Blo 2285435 3254689 := bstep (se 2 (by rfl) ⟨1220508, by rfl⟩ : syracuseStep 3254689 = 2441017) B2441017
theorem B4339585 : Blo 2285435 4339585 := bstep (se 2 (by rfl) ⟨1627344, by rfl⟩ : syracuseStep 4339585 = 3254689) B3254689
theorem B5786113 : Blo 2285435 5786113 := bstep (se 2 (by rfl) ⟨2169792, by rfl⟩ : syracuseStep 5786113 = 4339585) B4339585
theorem B7714817 : Blo 2285435 7714817 := bstep (se 2 (by rfl) ⟨2893056, by rfl⟩ : syracuseStep 7714817 = 5786113) B5786113
theorem B5143211 : Blo 2285435 5143211 := bstep (se 1 (by rfl) ⟨3857408, by rfl⟩ : syracuseStep 5143211 = 7714817) B7714817
theorem B3428807 : Blo 2285435 3428807 := bstep (se 1 (by rfl) ⟨2571605, by rfl⟩ : syracuseStep 3428807 = 5143211) B5143211
theorem B2285871 : Blo 2285435 2285871 := bstep (se 1 (by rfl) ⟨1714403, by rfl⟩ : syracuseStep 2285871 = 3428807) B3428807
theorem B3428813 : Blo 2285435 3428813 := bbase (se 3 (by rfl) ⟨642902, by rfl⟩ : syracuseStep 3428813 = 1285805) (by norm_num)
theorem B2285875 : Blo 2285435 2285875 := bstep (se 1 (by rfl) ⟨1714406, by rfl⟩ : syracuseStep 2285875 = 3428813) B3428813
theorem B5143229 : Blo 2285435 5143229 := bbase (se 3 (by rfl) ⟨964355, by rfl⟩ : syracuseStep 5143229 = 1928711) (by norm_num)
theorem B3428819 : Blo 2285435 3428819 := bstep (se 1 (by rfl) ⟨2571614, by rfl⟩ : syracuseStep 3428819 = 5143229) B5143229
theorem B2285879 : Blo 2285435 2285879 := bstep (se 1 (by rfl) ⟨1714409, by rfl⟩ : syracuseStep 2285879 = 3428819) B3428819
theorem B3857429 : Blo 2285435 3857429 := bbase (se 6 (by rfl) ⟨90408, by rfl⟩ : syracuseStep 3857429 = 180817) (by norm_num)
theorem B2571619 : Blo 2285435 2571619 := bstep (se 1 (by rfl) ⟨1928714, by rfl⟩ : syracuseStep 2571619 = 3857429) B3857429
theorem B3428825 : Blo 2285435 3428825 := bstep (se 2 (by rfl) ⟨1285809, by rfl⟩ : syracuseStep 3428825 = 2571619) B2571619
theorem B2285883 : Blo 2285435 2285883 := bstep (se 1 (by rfl) ⟨1714412, by rfl⟩ : syracuseStep 2285883 = 3428825) B3428825
theorem B3475613 : Blo 2285435 3475613 := bbase (se 3 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 3475613 = 1303355) (by norm_num)
theorem B9268301 : Blo 2285435 9268301 := bstep (se 3 (by rfl) ⟨1737806, by rfl⟩ : syracuseStep 9268301 = 3475613) B3475613
theorem B24715469 : Blo 2285435 24715469 := bstep (se 3 (by rfl) ⟨4634150, by rfl⟩ : syracuseStep 24715469 = 9268301) B9268301
theorem B16476979 : Blo 2285435 16476979 := bstep (se 1 (by rfl) ⟨12357734, by rfl⟩ : syracuseStep 16476979 = 24715469) B24715469
theorem B21969305 : Blo 2285435 21969305 := bstep (se 2 (by rfl) ⟨8238489, by rfl⟩ : syracuseStep 21969305 = 16476979) B16476979
theorem B14646203 : Blo 2285435 14646203 := bstep (se 1 (by rfl) ⟨10984652, by rfl⟩ : syracuseStep 14646203 = 21969305) B21969305
theorem B9764135 : Blo 2285435 9764135 := bstep (se 1 (by rfl) ⟨7323101, by rfl⟩ : syracuseStep 9764135 = 14646203) B14646203
theorem B6509423 : Blo 2285435 6509423 := bstep (se 1 (by rfl) ⟨4882067, by rfl⟩ : syracuseStep 6509423 = 9764135) B9764135
theorem B17358461 : Blo 2285435 17358461 := bstep (se 3 (by rfl) ⟨3254711, by rfl⟩ : syracuseStep 17358461 = 6509423) B6509423
theorem B11572307 : Blo 2285435 11572307 := bstep (se 1 (by rfl) ⟨8679230, by rfl⟩ : syracuseStep 11572307 = 17358461) B17358461
theorem B7714871 : Blo 2285435 7714871 := bstep (se 1 (by rfl) ⟨5786153, by rfl⟩ : syracuseStep 7714871 = 11572307) B11572307
theorem B5143247 : Blo 2285435 5143247 := bstep (se 1 (by rfl) ⟨3857435, by rfl⟩ : syracuseStep 5143247 = 7714871) B7714871
theorem B3428831 : Blo 2285435 3428831 := bstep (se 1 (by rfl) ⟨2571623, by rfl⟩ : syracuseStep 3428831 = 5143247) B5143247
theorem B2285887 : Blo 2285435 2285887 := bstep (se 1 (by rfl) ⟨1714415, by rfl⟩ : syracuseStep 2285887 = 3428831) B3428831
theorem B3428837 : Blo 2285435 3428837 := bbase (se 4 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 3428837 = 642907) (by norm_num)
theorem B2285891 : Blo 2285435 2285891 := bstep (se 1 (by rfl) ⟨1714418, by rfl⟩ : syracuseStep 2285891 = 3428837) B3428837
theorem B10984693 : Blo 2285435 10984693 := bbase (se 5 (by rfl) ⟨514907, by rfl⟩ : syracuseStep 10984693 = 1029815) (by norm_num)
theorem B14646257 : Blo 2285435 14646257 := bstep (se 2 (by rfl) ⟨5492346, by rfl⟩ : syracuseStep 14646257 = 10984693) B10984693
theorem B9764171 : Blo 2285435 9764171 := bstep (se 1 (by rfl) ⟨7323128, by rfl⟩ : syracuseStep 9764171 = 14646257) B14646257
theorem B6509447 : Blo 2285435 6509447 := bstep (se 1 (by rfl) ⟨4882085, by rfl⟩ : syracuseStep 6509447 = 9764171) B9764171
theorem B4339631 : Blo 2285435 4339631 := bstep (se 1 (by rfl) ⟨3254723, by rfl⟩ : syracuseStep 4339631 = 6509447) B6509447
theorem B2893087 : Blo 2285435 2893087 := bstep (se 1 (by rfl) ⟨2169815, by rfl⟩ : syracuseStep 2893087 = 4339631) B4339631
theorem B3857449 : Blo 2285435 3857449 := bstep (se 2 (by rfl) ⟨1446543, by rfl⟩ : syracuseStep 3857449 = 2893087) B2893087
theorem B5143265 : Blo 2285435 5143265 := bstep (se 2 (by rfl) ⟨1928724, by rfl⟩ : syracuseStep 5143265 = 3857449) B3857449
theorem B3428843 : Blo 2285435 3428843 := bstep (se 1 (by rfl) ⟨2571632, by rfl⟩ : syracuseStep 3428843 = 5143265) B5143265
theorem B2285895 : Blo 2285435 2285895 := bstep (se 1 (by rfl) ⟨1714421, by rfl⟩ : syracuseStep 2285895 = 3428843) B3428843
theorem B2571637 : Blo 2285435 2571637 := bbase (se 5 (by rfl) ⟨120545, by rfl⟩ : syracuseStep 2571637 = 241091) (by norm_num)
theorem B3428849 : Blo 2285435 3428849 := bstep (se 2 (by rfl) ⟨1285818, by rfl⟩ : syracuseStep 3428849 = 2571637) B2571637
theorem B2285899 : Blo 2285435 2285899 := bstep (se 1 (by rfl) ⟨1714424, by rfl⟩ : syracuseStep 2285899 = 3428849) B3428849
theorem B2893097 : Blo 2285435 2893097 := bbase (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) (by norm_num)
theorem B7714925 : Blo 2285435 7714925 := bstep (se 3 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 7714925 = 2893097) B2893097
theorem B5143283 : Blo 2285435 5143283 := bstep (se 1 (by rfl) ⟨3857462, by rfl⟩ : syracuseStep 5143283 = 7714925) B7714925
theorem B3428855 : Blo 2285435 3428855 := bstep (se 1 (by rfl) ⟨2571641, by rfl⟩ : syracuseStep 3428855 = 5143283) B5143283
theorem B2285903 : Blo 2285435 2285903 := bstep (se 1 (by rfl) ⟨1714427, by rfl⟩ : syracuseStep 2285903 = 3428855) B3428855
theorem B3428861 : Blo 2285435 3428861 := bbase (se 3 (by rfl) ⟨642911, by rfl⟩ : syracuseStep 3428861 = 1285823) (by norm_num)
theorem B2285907 : Blo 2285435 2285907 := bstep (se 1 (by rfl) ⟨1714430, by rfl⟩ : syracuseStep 2285907 = 3428861) B3428861
theorem B5143301 : Blo 2285435 5143301 := bbase (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) (by norm_num)
theorem B3428867 : Blo 2285435 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B2285911 : Blo 2285435 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B4339669 : Blo 2285435 4339669 := bbase (se 7 (by rfl) ⟨50855, by rfl⟩ : syracuseStep 4339669 = 101711) (by norm_num)
theorem B5786225 : Blo 2285435 5786225 := bstep (se 2 (by rfl) ⟨2169834, by rfl⟩ : syracuseStep 5786225 = 4339669) B4339669
theorem B3857483 : Blo 2285435 3857483 := bstep (se 1 (by rfl) ⟨2893112, by rfl⟩ : syracuseStep 3857483 = 5786225) B5786225
theorem B2571655 : Blo 2285435 2571655 := bstep (se 1 (by rfl) ⟨1928741, by rfl⟩ : syracuseStep 2571655 = 3857483) B3857483
theorem B3428873 : Blo 2285435 3428873 := bstep (se 2 (by rfl) ⟨1285827, by rfl⟩ : syracuseStep 3428873 = 2571655) B2571655
theorem B2285915 : Blo 2285435 2285915 := bstep (se 1 (by rfl) ⟨1714436, by rfl⟩ : syracuseStep 2285915 = 3428873) B3428873
theorem B11572469 : Blo 2285435 11572469 := bbase (se 5 (by rfl) ⟨542459, by rfl⟩ : syracuseStep 11572469 = 1084919) (by norm_num)
theorem B7714979 : Blo 2285435 7714979 := bstep (se 1 (by rfl) ⟨5786234, by rfl⟩ : syracuseStep 7714979 = 11572469) B11572469
theorem B5143319 : Blo 2285435 5143319 := bstep (se 1 (by rfl) ⟨3857489, by rfl⟩ : syracuseStep 5143319 = 7714979) B7714979
theorem B3428879 : Blo 2285435 3428879 := bstep (se 1 (by rfl) ⟨2571659, by rfl⟩ : syracuseStep 3428879 = 5143319) B5143319
theorem B2285919 : Blo 2285435 2285919 := bstep (se 1 (by rfl) ⟨1714439, by rfl⟩ : syracuseStep 2285919 = 3428879) B3428879
theorem B3428885 : Blo 2285435 3428885 := bbase (se 6 (by rfl) ⟨80364, by rfl⟩ : syracuseStep 3428885 = 160729) (by norm_num)
theorem B2285923 : Blo 2285435 2285923 := bstep (se 1 (by rfl) ⟨1714442, by rfl⟩ : syracuseStep 2285923 = 3428885) B3428885
theorem B6951349 : Blo 2285435 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B9268465 : Blo 2285435 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B12357953 : Blo 2285435 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B8238635 : Blo 2285435 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B5492423 : Blo 2285435 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B3661615 : Blo 2285435 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B19528613 : Blo 2285435 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B13019075 : Blo 2285435 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B8679383 : Blo 2285435 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B5786255 : Blo 2285435 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B3857503 : Blo 2285435 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B5143337 : Blo 2285435 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B3428891 : Blo 2285435 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B2285927 : Blo 2285435 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B2571673 : Blo 2285435 2571673 := bbase (se 2 (by rfl) ⟨964377, by rfl⟩ : syracuseStep 2571673 = 1928755) (by norm_num)
theorem B3428897 : Blo 2285435 3428897 := bstep (se 2 (by rfl) ⟨1285836, by rfl⟩ : syracuseStep 3428897 = 2571673) B2571673
theorem B2285931 : Blo 2285435 2285931 := bstep (se 1 (by rfl) ⟨1714448, by rfl⟩ : syracuseStep 2285931 = 3428897) B3428897
theorem B8679413 : Blo 2285435 8679413 := bbase (se 5 (by rfl) ⟨406847, by rfl⟩ : syracuseStep 8679413 = 813695) (by norm_num)
theorem B5786275 : Blo 2285435 5786275 := bstep (se 1 (by rfl) ⟨4339706, by rfl⟩ : syracuseStep 5786275 = 8679413) B8679413
theorem B7715033 : Blo 2285435 7715033 := bstep (se 2 (by rfl) ⟨2893137, by rfl⟩ : syracuseStep 7715033 = 5786275) B5786275
theorem B5143355 : Blo 2285435 5143355 := bstep (se 1 (by rfl) ⟨3857516, by rfl⟩ : syracuseStep 5143355 = 7715033) B7715033
theorem B3428903 : Blo 2285435 3428903 := bstep (se 1 (by rfl) ⟨2571677, by rfl⟩ : syracuseStep 3428903 = 5143355) B5143355
theorem B2285935 : Blo 2285435 2285935 := bstep (se 1 (by rfl) ⟨1714451, by rfl⟩ : syracuseStep 2285935 = 3428903) B3428903
theorem B3428909 : Blo 2285435 3428909 := bbase (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) (by norm_num)
theorem B2285939 : Blo 2285435 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B5143373 : Blo 2285435 5143373 := bbase (se 3 (by rfl) ⟨964382, by rfl⟩ : syracuseStep 5143373 = 1928765) (by norm_num)
theorem B3428915 : Blo 2285435 3428915 := bstep (se 1 (by rfl) ⟨2571686, by rfl⟩ : syracuseStep 3428915 = 5143373) B5143373
theorem B2285943 : Blo 2285435 2285943 := bstep (se 1 (by rfl) ⟨1714457, by rfl⟩ : syracuseStep 2285943 = 3428915) B3428915
theorem B2893153 : Blo 2285435 2893153 := bbase (se 2 (by rfl) ⟨1084932, by rfl⟩ : syracuseStep 2893153 = 2169865) (by norm_num)
theorem B3857537 : Blo 2285435 3857537 := bstep (se 2 (by rfl) ⟨1446576, by rfl⟩ : syracuseStep 3857537 = 2893153) B2893153
theorem B2571691 : Blo 2285435 2571691 := bstep (se 1 (by rfl) ⟨1928768, by rfl⟩ : syracuseStep 2571691 = 3857537) B3857537
theorem B3428921 : Blo 2285435 3428921 := bstep (se 2 (by rfl) ⟨1285845, by rfl⟩ : syracuseStep 3428921 = 2571691) B2571691
theorem B2285947 : Blo 2285435 2285947 := bstep (se 1 (by rfl) ⟨1714460, by rfl⟩ : syracuseStep 2285947 = 3428921) B3428921
theorem B26038421 : Blo 2285435 26038421 := bbase (se 6 (by rfl) ⟨610275, by rfl⟩ : syracuseStep 26038421 = 1220551) (by norm_num)
theorem B17358947 : Blo 2285435 17358947 := bstep (se 1 (by rfl) ⟨13019210, by rfl⟩ : syracuseStep 17358947 = 26038421) B26038421
theorem B11572631 : Blo 2285435 11572631 := bstep (se 1 (by rfl) ⟨8679473, by rfl⟩ : syracuseStep 11572631 = 17358947) B17358947
theorem B7715087 : Blo 2285435 7715087 := bstep (se 1 (by rfl) ⟨5786315, by rfl⟩ : syracuseStep 7715087 = 11572631) B11572631
theorem B5143391 : Blo 2285435 5143391 := bstep (se 1 (by rfl) ⟨3857543, by rfl⟩ : syracuseStep 5143391 = 7715087) B7715087
theorem B3428927 : Blo 2285435 3428927 := bstep (se 1 (by rfl) ⟨2571695, by rfl⟩ : syracuseStep 3428927 = 5143391) B5143391
theorem B2285951 : Blo 2285435 2285951 := bstep (se 1 (by rfl) ⟨1714463, by rfl⟩ : syracuseStep 2285951 = 3428927) B3428927
theorem B3428933 : Blo 2285435 3428933 := bbase (se 4 (by rfl) ⟨321462, by rfl⟩ : syracuseStep 3428933 = 642925) (by norm_num)
theorem B2285955 : Blo 2285435 2285955 := bstep (se 1 (by rfl) ⟨1714466, by rfl⟩ : syracuseStep 2285955 = 3428933) B3428933
theorem B3857557 : Blo 2285435 3857557 := bbase (se 6 (by rfl) ⟨90411, by rfl⟩ : syracuseStep 3857557 = 180823) (by norm_num)
theorem B5143409 : Blo 2285435 5143409 := bstep (se 2 (by rfl) ⟨1928778, by rfl⟩ : syracuseStep 5143409 = 3857557) B3857557
theorem B3428939 : Blo 2285435 3428939 := bstep (se 1 (by rfl) ⟨2571704, by rfl⟩ : syracuseStep 3428939 = 5143409) B5143409
theorem B2285959 : Blo 2285435 2285959 := bstep (se 1 (by rfl) ⟨1714469, by rfl⟩ : syracuseStep 2285959 = 3428939) B3428939
theorem B2571709 : Blo 2285435 2571709 := bbase (se 3 (by rfl) ⟨482195, by rfl⟩ : syracuseStep 2571709 = 964391) (by norm_num)
theorem B3428945 : Blo 2285435 3428945 := bstep (se 2 (by rfl) ⟨1285854, by rfl⟩ : syracuseStep 3428945 = 2571709) B2571709
theorem B2285963 : Blo 2285435 2285963 := bstep (se 1 (by rfl) ⟨1714472, by rfl⟩ : syracuseStep 2285963 = 3428945) B3428945
theorem B7715141 : Blo 2285435 7715141 := bbase (se 4 (by rfl) ⟨723294, by rfl⟩ : syracuseStep 7715141 = 1446589) (by norm_num)
theorem B5143427 : Blo 2285435 5143427 := bstep (se 1 (by rfl) ⟨3857570, by rfl⟩ : syracuseStep 5143427 = 7715141) B7715141
theorem B3428951 : Blo 2285435 3428951 := bstep (se 1 (by rfl) ⟨2571713, by rfl⟩ : syracuseStep 3428951 = 5143427) B5143427
theorem B2285967 : Blo 2285435 2285967 := bstep (se 1 (by rfl) ⟨1714475, by rfl⟩ : syracuseStep 2285967 = 3428951) B3428951
theorem B3428957 : Blo 2285435 3428957 := bbase (se 3 (by rfl) ⟨642929, by rfl⟩ : syracuseStep 3428957 = 1285859) (by norm_num)
theorem B2285971 : Blo 2285435 2285971 := bstep (se 1 (by rfl) ⟨1714478, by rfl⟩ : syracuseStep 2285971 = 3428957) B3428957
theorem B5143445 : Blo 2285435 5143445 := bbase (se 6 (by rfl) ⟨120549, by rfl⟩ : syracuseStep 5143445 = 241099) (by norm_num)
theorem B3428963 : Blo 2285435 3428963 := bstep (se 1 (by rfl) ⟨2571722, by rfl⟩ : syracuseStep 3428963 = 5143445) B5143445
theorem B2285975 : Blo 2285435 2285975 := bstep (se 1 (by rfl) ⟨1714481, by rfl⟩ : syracuseStep 2285975 = 3428963) B3428963
theorem B5492549 : Blo 2285435 5492549 := bbase (se 4 (by rfl) ⟨514926, by rfl⟩ : syracuseStep 5492549 = 1029853) (by norm_num)
theorem B3661699 : Blo 2285435 3661699 := bstep (se 1 (by rfl) ⟨2746274, by rfl⟩ : syracuseStep 3661699 = 5492549) B5492549
theorem B4882265 : Blo 2285435 4882265 := bstep (se 2 (by rfl) ⟨1830849, by rfl⟩ : syracuseStep 4882265 = 3661699) B3661699
theorem B3254843 : Blo 2285435 3254843 := bstep (se 1 (by rfl) ⟨2441132, by rfl⟩ : syracuseStep 3254843 = 4882265) B4882265
theorem B8679581 : Blo 2285435 8679581 := bstep (se 3 (by rfl) ⟨1627421, by rfl⟩ : syracuseStep 8679581 = 3254843) B3254843
theorem B5786387 : Blo 2285435 5786387 := bstep (se 1 (by rfl) ⟨4339790, by rfl⟩ : syracuseStep 5786387 = 8679581) B8679581
theorem B3857591 : Blo 2285435 3857591 := bstep (se 1 (by rfl) ⟨2893193, by rfl⟩ : syracuseStep 3857591 = 5786387) B5786387
theorem B2571727 : Blo 2285435 2571727 := bstep (se 1 (by rfl) ⟨1928795, by rfl⟩ : syracuseStep 2571727 = 3857591) B3857591
theorem B3428969 : Blo 2285435 3428969 := bstep (se 2 (by rfl) ⟨1285863, by rfl⟩ : syracuseStep 3428969 = 2571727) B2571727
theorem B2285979 : Blo 2285435 2285979 := bstep (se 1 (by rfl) ⟨1714484, by rfl⟩ : syracuseStep 2285979 = 3428969) B3428969
theorem B5492557 : Blo 2285435 5492557 := bbase (se 3 (by rfl) ⟨1029854, by rfl⟩ : syracuseStep 5492557 = 2059709) (by norm_num)
theorem B7323409 : Blo 2285435 7323409 := bstep (se 2 (by rfl) ⟨2746278, by rfl⟩ : syracuseStep 7323409 = 5492557) B5492557
theorem B9764545 : Blo 2285435 9764545 := bstep (se 2 (by rfl) ⟨3661704, by rfl⟩ : syracuseStep 9764545 = 7323409) B7323409
theorem B13019393 : Blo 2285435 13019393 := bstep (se 2 (by rfl) ⟨4882272, by rfl⟩ : syracuseStep 13019393 = 9764545) B9764545
theorem B8679595 : Blo 2285435 8679595 := bstep (se 1 (by rfl) ⟨6509696, by rfl⟩ : syracuseStep 8679595 = 13019393) B13019393
theorem B11572793 : Blo 2285435 11572793 := bstep (se 2 (by rfl) ⟨4339797, by rfl⟩ : syracuseStep 11572793 = 8679595) B8679595
theorem B7715195 : Blo 2285435 7715195 := bstep (se 1 (by rfl) ⟨5786396, by rfl⟩ : syracuseStep 7715195 = 11572793) B11572793
theorem B5143463 : Blo 2285435 5143463 := bstep (se 1 (by rfl) ⟨3857597, by rfl⟩ : syracuseStep 5143463 = 7715195) B7715195
theorem B3428975 : Blo 2285435 3428975 := bstep (se 1 (by rfl) ⟨2571731, by rfl⟩ : syracuseStep 3428975 = 5143463) B5143463
theorem B2285983 : Blo 2285435 2285983 := bstep (se 1 (by rfl) ⟨1714487, by rfl⟩ : syracuseStep 2285983 = 3428975) B3428975
theorem B3428981 : Blo 2285435 3428981 := bbase (se 5 (by rfl) ⟨160733, by rfl⟩ : syracuseStep 3428981 = 321467) (by norm_num)
theorem B2285987 : Blo 2285435 2285987 := bstep (se 1 (by rfl) ⟨1714490, by rfl⟩ : syracuseStep 2285987 = 3428981) B3428981
theorem B4339813 : Blo 2285435 4339813 := bbase (se 4 (by rfl) ⟨406857, by rfl⟩ : syracuseStep 4339813 = 813715) (by norm_num)
theorem B5786417 : Blo 2285435 5786417 := bstep (se 2 (by rfl) ⟨2169906, by rfl⟩ : syracuseStep 5786417 = 4339813) B4339813
theorem B3857611 : Blo 2285435 3857611 := bstep (se 1 (by rfl) ⟨2893208, by rfl⟩ : syracuseStep 3857611 = 5786417) B5786417
theorem B5143481 : Blo 2285435 5143481 := bstep (se 2 (by rfl) ⟨1928805, by rfl⟩ : syracuseStep 5143481 = 3857611) B3857611
theorem B3428987 : Blo 2285435 3428987 := bstep (se 1 (by rfl) ⟨2571740, by rfl⟩ : syracuseStep 3428987 = 5143481) B5143481
theorem B2285991 : Blo 2285435 2285991 := bstep (se 1 (by rfl) ⟨1714493, by rfl⟩ : syracuseStep 2285991 = 3428987) B3428987
theorem B2571745 : Blo 2285435 2571745 := bbase (se 2 (by rfl) ⟨964404, by rfl⟩ : syracuseStep 2571745 = 1928809) (by norm_num)
theorem B3428993 : Blo 2285435 3428993 := bstep (se 2 (by rfl) ⟨1285872, by rfl⟩ : syracuseStep 3428993 = 2571745) B2571745
theorem B2285995 : Blo 2285435 2285995 := bstep (se 1 (by rfl) ⟨1714496, by rfl⟩ : syracuseStep 2285995 = 3428993) B3428993
theorem B5786437 : Blo 2285435 5786437 := bbase (se 4 (by rfl) ⟨542478, by rfl⟩ : syracuseStep 5786437 = 1084957) (by norm_num)
theorem B7715249 : Blo 2285435 7715249 := bstep (se 2 (by rfl) ⟨2893218, by rfl⟩ : syracuseStep 7715249 = 5786437) B5786437
theorem B5143499 : Blo 2285435 5143499 := bstep (se 1 (by rfl) ⟨3857624, by rfl⟩ : syracuseStep 5143499 = 7715249) B7715249
theorem B3428999 : Blo 2285435 3428999 := bstep (se 1 (by rfl) ⟨2571749, by rfl⟩ : syracuseStep 3428999 = 5143499) B5143499
theorem B2285999 : Blo 2285435 2285999 := bstep (se 1 (by rfl) ⟨1714499, by rfl⟩ : syracuseStep 2285999 = 3428999) B3428999
theorem B3429005 : Blo 2285435 3429005 := bbase (se 3 (by rfl) ⟨642938, by rfl⟩ : syracuseStep 3429005 = 1285877) (by norm_num)
theorem B2286003 : Blo 2285435 2286003 := bstep (se 1 (by rfl) ⟨1714502, by rfl⟩ : syracuseStep 2286003 = 3429005) B3429005
theorem B5143517 : Blo 2285435 5143517 := bbase (se 3 (by rfl) ⟨964409, by rfl⟩ : syracuseStep 5143517 = 1928819) (by norm_num)
theorem B3429011 : Blo 2285435 3429011 := bstep (se 1 (by rfl) ⟨2571758, by rfl⟩ : syracuseStep 3429011 = 5143517) B5143517
theorem B2286007 : Blo 2285435 2286007 := bstep (se 1 (by rfl) ⟨1714505, by rfl⟩ : syracuseStep 2286007 = 3429011) B3429011
theorem B3857645 : Blo 2285435 3857645 := bbase (se 3 (by rfl) ⟨723308, by rfl⟩ : syracuseStep 3857645 = 1446617) (by norm_num)
theorem B2571763 : Blo 2285435 2571763 := bstep (se 1 (by rfl) ⟨1928822, by rfl⟩ : syracuseStep 2571763 = 3857645) B3857645
theorem B3429017 : Blo 2285435 3429017 := bstep (se 2 (by rfl) ⟨1285881, by rfl⟩ : syracuseStep 3429017 = 2571763) B2571763
theorem B2286011 : Blo 2285435 2286011 := bstep (se 1 (by rfl) ⟨1714508, by rfl⟩ : syracuseStep 2286011 = 3429017) B3429017
theorem B2317205 : Blo 2285435 2317205 := bbase (se 6 (by rfl) ⟨54309, by rfl⟩ : syracuseStep 2317205 = 108619) (by norm_num)
theorem B6179213 : Blo 2285435 6179213 := bstep (se 3 (by rfl) ⟨1158602, by rfl⟩ : syracuseStep 6179213 = 2317205) B2317205
theorem B16477901 : Blo 2285435 16477901 := bstep (se 3 (by rfl) ⟨3089606, by rfl⟩ : syracuseStep 16477901 = 6179213) B6179213
theorem B10985267 : Blo 2285435 10985267 := bstep (se 1 (by rfl) ⟨8238950, by rfl⟩ : syracuseStep 10985267 = 16477901) B16477901
theorem B29294045 : Blo 2285435 29294045 := bstep (se 3 (by rfl) ⟨5492633, by rfl⟩ : syracuseStep 29294045 = 10985267) B10985267
theorem B19529363 : Blo 2285435 19529363 := bstep (se 1 (by rfl) ⟨14647022, by rfl⟩ : syracuseStep 19529363 = 29294045) B29294045
theorem B13019575 : Blo 2285435 13019575 := bstep (se 1 (by rfl) ⟨9764681, by rfl⟩ : syracuseStep 13019575 = 19529363) B19529363
theorem B17359433 : Blo 2285435 17359433 := bstep (se 2 (by rfl) ⟨6509787, by rfl⟩ : syracuseStep 17359433 = 13019575) B13019575
theorem B11572955 : Blo 2285435 11572955 := bstep (se 1 (by rfl) ⟨8679716, by rfl⟩ : syracuseStep 11572955 = 17359433) B17359433
theorem B7715303 : Blo 2285435 7715303 := bstep (se 1 (by rfl) ⟨5786477, by rfl⟩ : syracuseStep 7715303 = 11572955) B11572955
theorem B5143535 : Blo 2285435 5143535 := bstep (se 1 (by rfl) ⟨3857651, by rfl⟩ : syracuseStep 5143535 = 7715303) B7715303
theorem B3429023 : Blo 2285435 3429023 := bstep (se 1 (by rfl) ⟨2571767, by rfl⟩ : syracuseStep 3429023 = 5143535) B5143535
theorem B2286015 : Blo 2285435 2286015 := bstep (se 1 (by rfl) ⟨1714511, by rfl⟩ : syracuseStep 2286015 = 3429023) B3429023
theorem B3429029 : Blo 2285435 3429029 := bbase (se 4 (by rfl) ⟨321471, by rfl⟩ : syracuseStep 3429029 = 642943) (by norm_num)
theorem B2286019 : Blo 2285435 2286019 := bstep (se 1 (by rfl) ⟨1714514, by rfl⟩ : syracuseStep 2286019 = 3429029) B3429029
theorem B2893249 : Blo 2285435 2893249 := bbase (se 2 (by rfl) ⟨1084968, by rfl⟩ : syracuseStep 2893249 = 2169937) (by norm_num)
theorem B3857665 : Blo 2285435 3857665 := bstep (se 2 (by rfl) ⟨1446624, by rfl⟩ : syracuseStep 3857665 = 2893249) B2893249
theorem B5143553 : Blo 2285435 5143553 := bstep (se 2 (by rfl) ⟨1928832, by rfl⟩ : syracuseStep 5143553 = 3857665) B3857665
theorem B3429035 : Blo 2285435 3429035 := bstep (se 1 (by rfl) ⟨2571776, by rfl⟩ : syracuseStep 3429035 = 5143553) B5143553
theorem B2286023 : Blo 2285435 2286023 := bstep (se 1 (by rfl) ⟨1714517, by rfl⟩ : syracuseStep 2286023 = 3429035) B3429035
theorem B2571781 : Blo 2285435 2571781 := bbase (se 4 (by rfl) ⟨241104, by rfl⟩ : syracuseStep 2571781 = 482209) (by norm_num)
theorem B3429041 : Blo 2285435 3429041 := bstep (se 2 (by rfl) ⟨1285890, by rfl⟩ : syracuseStep 3429041 = 2571781) B2571781
theorem B2286027 : Blo 2285435 2286027 := bstep (se 1 (by rfl) ⟨1714520, by rfl⟩ : syracuseStep 2286027 = 3429041) B3429041
theorem B3254917 : Blo 2285435 3254917 := bbase (se 4 (by rfl) ⟨305148, by rfl⟩ : syracuseStep 3254917 = 610297) (by norm_num)
theorem B4339889 : Blo 2285435 4339889 := bstep (se 2 (by rfl) ⟨1627458, by rfl⟩ : syracuseStep 4339889 = 3254917) B3254917
theorem B2893259 : Blo 2285435 2893259 := bstep (se 1 (by rfl) ⟨2169944, by rfl⟩ : syracuseStep 2893259 = 4339889) B4339889
theorem B7715357 : Blo 2285435 7715357 := bstep (se 3 (by rfl) ⟨1446629, by rfl⟩ : syracuseStep 7715357 = 2893259) B2893259
theorem B5143571 : Blo 2285435 5143571 := bstep (se 1 (by rfl) ⟨3857678, by rfl⟩ : syracuseStep 5143571 = 7715357) B7715357
theorem B3429047 : Blo 2285435 3429047 := bstep (se 1 (by rfl) ⟨2571785, by rfl⟩ : syracuseStep 3429047 = 5143571) B5143571
theorem B2286031 : Blo 2285435 2286031 := bstep (se 1 (by rfl) ⟨1714523, by rfl⟩ : syracuseStep 2286031 = 3429047) B3429047
theorem B3429053 : Blo 2285435 3429053 := bbase (se 3 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 3429053 = 1285895) (by norm_num)
theorem B2286035 : Blo 2285435 2286035 := bstep (se 1 (by rfl) ⟨1714526, by rfl⟩ : syracuseStep 2286035 = 3429053) B3429053
theorem B5143589 : Blo 2285435 5143589 := bbase (se 4 (by rfl) ⟨482211, by rfl⟩ : syracuseStep 5143589 = 964423) (by norm_num)
theorem B3429059 : Blo 2285435 3429059 := bstep (se 1 (by rfl) ⟨2571794, by rfl⟩ : syracuseStep 3429059 = 5143589) B5143589
theorem B2286039 : Blo 2285435 2286039 := bstep (se 1 (by rfl) ⟨1714529, by rfl⟩ : syracuseStep 2286039 = 3429059) B3429059
theorem B5786549 : Blo 2285435 5786549 := bbase (se 5 (by rfl) ⟨271244, by rfl⟩ : syracuseStep 5786549 = 542489) (by norm_num)
theorem B3857699 : Blo 2285435 3857699 := bstep (se 1 (by rfl) ⟨2893274, by rfl⟩ : syracuseStep 3857699 = 5786549) B5786549
theorem B2571799 : Blo 2285435 2571799 := bstep (se 1 (by rfl) ⟨1928849, by rfl⟩ : syracuseStep 2571799 = 3857699) B3857699
theorem B3429065 : Blo 2285435 3429065 := bstep (se 2 (by rfl) ⟨1285899, by rfl⟩ : syracuseStep 3429065 = 2571799) B2571799
theorem B2286043 : Blo 2285435 2286043 := bstep (se 1 (by rfl) ⟨1714532, by rfl⟩ : syracuseStep 2286043 = 3429065) B3429065
theorem B5865509 : Blo 2285435 5865509 := bbase (se 4 (by rfl) ⟨549891, by rfl⟩ : syracuseStep 5865509 = 1099783) (by norm_num)
theorem B3910339 : Blo 2285435 3910339 := bstep (se 1 (by rfl) ⟨2932754, by rfl⟩ : syracuseStep 3910339 = 5865509) B5865509
theorem B20855141 : Blo 2285435 20855141 := bstep (se 4 (by rfl) ⟨1955169, by rfl⟩ : syracuseStep 20855141 = 3910339) B3910339
theorem B13903427 : Blo 2285435 13903427 := bstep (se 1 (by rfl) ⟨10427570, by rfl⟩ : syracuseStep 13903427 = 20855141) B20855141
theorem B9268951 : Blo 2285435 9268951 := bstep (se 1 (by rfl) ⟨6951713, by rfl⟩ : syracuseStep 9268951 = 13903427) B13903427
theorem B12358601 : Blo 2285435 12358601 := bstep (se 2 (by rfl) ⟨4634475, by rfl⟩ : syracuseStep 12358601 = 9268951) B9268951
theorem B8239067 : Blo 2285435 8239067 := bstep (se 1 (by rfl) ⟨6179300, by rfl⟩ : syracuseStep 8239067 = 12358601) B12358601
theorem B5492711 : Blo 2285435 5492711 := bstep (se 1 (by rfl) ⟨4119533, by rfl⟩ : syracuseStep 5492711 = 8239067) B8239067
theorem B14647229 : Blo 2285435 14647229 := bstep (se 3 (by rfl) ⟨2746355, by rfl⟩ : syracuseStep 14647229 = 5492711) B5492711
theorem B9764819 : Blo 2285435 9764819 := bstep (se 1 (by rfl) ⟨7323614, by rfl⟩ : syracuseStep 9764819 = 14647229) B14647229
theorem B6509879 : Blo 2285435 6509879 := bstep (se 1 (by rfl) ⟨4882409, by rfl⟩ : syracuseStep 6509879 = 9764819) B9764819
theorem B4339919 : Blo 2285435 4339919 := bstep (se 1 (by rfl) ⟨3254939, by rfl⟩ : syracuseStep 4339919 = 6509879) B6509879
theorem B11573117 : Blo 2285435 11573117 := bstep (se 3 (by rfl) ⟨2169959, by rfl⟩ : syracuseStep 11573117 = 4339919) B4339919
theorem B7715411 : Blo 2285435 7715411 := bstep (se 1 (by rfl) ⟨5786558, by rfl⟩ : syracuseStep 7715411 = 11573117) B11573117
theorem B5143607 : Blo 2285435 5143607 := bstep (se 1 (by rfl) ⟨3857705, by rfl⟩ : syracuseStep 5143607 = 7715411) B7715411
theorem B3429071 : Blo 2285435 3429071 := bstep (se 1 (by rfl) ⟨2571803, by rfl⟩ : syracuseStep 3429071 = 5143607) B5143607
theorem B2286047 : Blo 2285435 2286047 := bstep (se 1 (by rfl) ⟨1714535, by rfl⟩ : syracuseStep 2286047 = 3429071) B3429071
theorem B3429077 : Blo 2285435 3429077 := bbase (se 7 (by rfl) ⟨40184, by rfl⟩ : syracuseStep 3429077 = 80369) (by norm_num)
theorem B2286051 : Blo 2285435 2286051 := bstep (se 1 (by rfl) ⟨1714538, by rfl⟩ : syracuseStep 2286051 = 3429077) B3429077
theorem B11731061 : Blo 2285435 11731061 := bbase (se 5 (by rfl) ⟨549893, by rfl⟩ : syracuseStep 11731061 = 1099787) (by norm_num)
theorem B7820707 : Blo 2285435 7820707 := bstep (se 1 (by rfl) ⟨5865530, by rfl⟩ : syracuseStep 7820707 = 11731061) B11731061
theorem B10427609 : Blo 2285435 10427609 := bstep (se 2 (by rfl) ⟨3910353, by rfl⟩ : syracuseStep 10427609 = 7820707) B7820707
theorem B6951739 : Blo 2285435 6951739 := bstep (se 1 (by rfl) ⟨5213804, by rfl⟩ : syracuseStep 6951739 = 10427609) B10427609
theorem B9268985 : Blo 2285435 9268985 := bstep (se 2 (by rfl) ⟨3475869, by rfl⟩ : syracuseStep 9268985 = 6951739) B6951739
theorem B6179323 : Blo 2285435 6179323 := bstep (se 1 (by rfl) ⟨4634492, by rfl⟩ : syracuseStep 6179323 = 9268985) B9268985
theorem B8239097 : Blo 2285435 8239097 := bstep (se 2 (by rfl) ⟨3089661, by rfl⟩ : syracuseStep 8239097 = 6179323) B6179323
theorem B5492731 : Blo 2285435 5492731 := bstep (se 1 (by rfl) ⟨4119548, by rfl⟩ : syracuseStep 5492731 = 8239097) B8239097
theorem B7323641 : Blo 2285435 7323641 := bstep (se 2 (by rfl) ⟨2746365, by rfl⟩ : syracuseStep 7323641 = 5492731) B5492731
theorem B4882427 : Blo 2285435 4882427 := bstep (se 1 (by rfl) ⟨3661820, by rfl⟩ : syracuseStep 4882427 = 7323641) B7323641
theorem B3254951 : Blo 2285435 3254951 := bstep (se 1 (by rfl) ⟨2441213, by rfl⟩ : syracuseStep 3254951 = 4882427) B4882427
theorem B8679869 : Blo 2285435 8679869 := bstep (se 3 (by rfl) ⟨1627475, by rfl⟩ : syracuseStep 8679869 = 3254951) B3254951
theorem B5786579 : Blo 2285435 5786579 := bstep (se 1 (by rfl) ⟨4339934, by rfl⟩ : syracuseStep 5786579 = 8679869) B8679869
theorem B3857719 : Blo 2285435 3857719 := bstep (se 1 (by rfl) ⟨2893289, by rfl⟩ : syracuseStep 3857719 = 5786579) B5786579
theorem B5143625 : Blo 2285435 5143625 := bstep (se 2 (by rfl) ⟨1928859, by rfl⟩ : syracuseStep 5143625 = 3857719) B3857719
theorem B3429083 : Blo 2285435 3429083 := bstep (se 1 (by rfl) ⟨2571812, by rfl⟩ : syracuseStep 3429083 = 5143625) B5143625
theorem B2286055 : Blo 2285435 2286055 := bstep (se 1 (by rfl) ⟨1714541, by rfl⟩ : syracuseStep 2286055 = 3429083) B3429083
theorem B2571817 : Blo 2285435 2571817 := bbase (se 2 (by rfl) ⟨964431, by rfl⟩ : syracuseStep 2571817 = 1928863) (by norm_num)
theorem B3429089 : Blo 2285435 3429089 := bstep (se 2 (by rfl) ⟨1285908, by rfl⟩ : syracuseStep 3429089 = 2571817) B2571817
theorem B2286059 : Blo 2285435 2286059 := bstep (se 1 (by rfl) ⟨1714544, by rfl⟩ : syracuseStep 2286059 = 3429089) B3429089
theorem B21970997 : Blo 2285435 21970997 := bbase (se 5 (by rfl) ⟨1029890, by rfl⟩ : syracuseStep 21970997 = 2059781) (by norm_num)
theorem B14647331 : Blo 2285435 14647331 := bstep (se 1 (by rfl) ⟨10985498, by rfl⟩ : syracuseStep 14647331 = 21970997) B21970997
theorem B9764887 : Blo 2285435 9764887 := bstep (se 1 (by rfl) ⟨7323665, by rfl⟩ : syracuseStep 9764887 = 14647331) B14647331
theorem B13019849 : Blo 2285435 13019849 := bstep (se 2 (by rfl) ⟨4882443, by rfl⟩ : syracuseStep 13019849 = 9764887) B9764887
theorem B8679899 : Blo 2285435 8679899 := bstep (se 1 (by rfl) ⟨6509924, by rfl⟩ : syracuseStep 8679899 = 13019849) B13019849
theorem B5786599 : Blo 2285435 5786599 := bstep (se 1 (by rfl) ⟨4339949, by rfl⟩ : syracuseStep 5786599 = 8679899) B8679899
theorem B7715465 : Blo 2285435 7715465 := bstep (se 2 (by rfl) ⟨2893299, by rfl⟩ : syracuseStep 7715465 = 5786599) B5786599
theorem B5143643 : Blo 2285435 5143643 := bstep (se 1 (by rfl) ⟨3857732, by rfl⟩ : syracuseStep 5143643 = 7715465) B7715465
theorem B3429095 : Blo 2285435 3429095 := bstep (se 1 (by rfl) ⟨2571821, by rfl⟩ : syracuseStep 3429095 = 5143643) B5143643
theorem B2286063 : Blo 2285435 2286063 := bstep (se 1 (by rfl) ⟨1714547, by rfl⟩ : syracuseStep 2286063 = 3429095) B3429095
theorem B3429101 : Blo 2285435 3429101 := bbase (se 3 (by rfl) ⟨642956, by rfl⟩ : syracuseStep 3429101 = 1285913) (by norm_num)
theorem B2286067 : Blo 2285435 2286067 := bstep (se 1 (by rfl) ⟨1714550, by rfl⟩ : syracuseStep 2286067 = 3429101) B3429101
theorem B5143661 : Blo 2285435 5143661 := bbase (se 3 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 5143661 = 1928873) (by norm_num)
theorem B3429107 : Blo 2285435 3429107 := bstep (se 1 (by rfl) ⟨2571830, by rfl⟩ : syracuseStep 3429107 = 5143661) B5143661
theorem B2286071 : Blo 2285435 2286071 := bstep (se 1 (by rfl) ⟨1714553, by rfl⟩ : syracuseStep 2286071 = 3429107) B3429107
theorem B4339973 : Blo 2285435 4339973 := bbase (se 4 (by rfl) ⟨406872, by rfl⟩ : syracuseStep 4339973 = 813745) (by norm_num)
theorem B2893315 : Blo 2285435 2893315 := bstep (se 1 (by rfl) ⟨2169986, by rfl⟩ : syracuseStep 2893315 = 4339973) B4339973
theorem B3857753 : Blo 2285435 3857753 := bstep (se 2 (by rfl) ⟨1446657, by rfl⟩ : syracuseStep 3857753 = 2893315) B2893315
theorem B2571835 : Blo 2285435 2571835 := bstep (se 1 (by rfl) ⟨1928876, by rfl⟩ : syracuseStep 2571835 = 3857753) B3857753
theorem B3429113 : Blo 2285435 3429113 := bstep (se 2 (by rfl) ⟨1285917, by rfl⟩ : syracuseStep 3429113 = 2571835) B2571835
theorem B2286075 : Blo 2285435 2286075 := bstep (se 1 (by rfl) ⟨1714556, by rfl⟩ : syracuseStep 2286075 = 3429113) B3429113
theorem B4949093 : Blo 2285435 4949093 := bbase (se 4 (by rfl) ⟨463977, by rfl⟩ : syracuseStep 4949093 = 927955) (by norm_num)
theorem B3299395 : Blo 2285435 3299395 := bstep (se 1 (by rfl) ⟨2474546, by rfl⟩ : syracuseStep 3299395 = 4949093) B4949093
theorem B4399193 : Blo 2285435 4399193 := bstep (se 2 (by rfl) ⟨1649697, by rfl⟩ : syracuseStep 4399193 = 3299395) B3299395
theorem B2932795 : Blo 2285435 2932795 := bstep (se 1 (by rfl) ⟨2199596, by rfl⟩ : syracuseStep 2932795 = 4399193) B4399193
theorem B3910393 : Blo 2285435 3910393 := bstep (se 2 (by rfl) ⟨1466397, by rfl⟩ : syracuseStep 3910393 = 2932795) B2932795
theorem B5213857 : Blo 2285435 5213857 := bstep (se 2 (by rfl) ⟨1955196, by rfl⟩ : syracuseStep 5213857 = 3910393) B3910393
theorem B6951809 : Blo 2285435 6951809 := bstep (se 2 (by rfl) ⟨2606928, by rfl⟩ : syracuseStep 6951809 = 5213857) B5213857
theorem B18538157 : Blo 2285435 18538157 := bstep (se 3 (by rfl) ⟨3475904, by rfl⟩ : syracuseStep 18538157 = 6951809) B6951809
theorem B49435085 : Blo 2285435 49435085 := bstep (se 3 (by rfl) ⟨9269078, by rfl⟩ : syracuseStep 49435085 = 18538157) B18538157
theorem B32956723 : Blo 2285435 32956723 := bstep (se 1 (by rfl) ⟨24717542, by rfl⟩ : syracuseStep 32956723 = 49435085) B49435085
theorem B43942297 : Blo 2285435 43942297 := bstep (se 2 (by rfl) ⟨16478361, by rfl⟩ : syracuseStep 43942297 = 32956723) B32956723
theorem B58589729 : Blo 2285435 58589729 := bstep (se 2 (by rfl) ⟨21971148, by rfl⟩ : syracuseStep 58589729 = 43942297) B43942297
theorem B39059819 : Blo 2285435 39059819 := bstep (se 1 (by rfl) ⟨29294864, by rfl⟩ : syracuseStep 39059819 = 58589729) B58589729
theorem B26039879 : Blo 2285435 26039879 := bstep (se 1 (by rfl) ⟨19529909, by rfl⟩ : syracuseStep 26039879 = 39059819) B39059819
theorem B17359919 : Blo 2285435 17359919 := bstep (se 1 (by rfl) ⟨13019939, by rfl⟩ : syracuseStep 17359919 = 26039879) B26039879
theorem B11573279 : Blo 2285435 11573279 := bstep (se 1 (by rfl) ⟨8679959, by rfl⟩ : syracuseStep 11573279 = 17359919) B17359919
theorem B7715519 : Blo 2285435 7715519 := bstep (se 1 (by rfl) ⟨5786639, by rfl⟩ : syracuseStep 7715519 = 11573279) B11573279
theorem B5143679 : Blo 2285435 5143679 := bstep (se 1 (by rfl) ⟨3857759, by rfl⟩ : syracuseStep 5143679 = 7715519) B7715519
theorem B3429119 : Blo 2285435 3429119 := bstep (se 1 (by rfl) ⟨2571839, by rfl⟩ : syracuseStep 3429119 = 5143679) B5143679
theorem B2286079 : Blo 2285435 2286079 := bstep (se 1 (by rfl) ⟨1714559, by rfl⟩ : syracuseStep 2286079 = 3429119) B3429119
theorem B3429125 : Blo 2285435 3429125 := bbase (se 4 (by rfl) ⟨321480, by rfl⟩ : syracuseStep 3429125 = 642961) (by norm_num)
theorem B2286083 : Blo 2285435 2286083 := bstep (se 1 (by rfl) ⟨1714562, by rfl⟩ : syracuseStep 2286083 = 3429125) B3429125
theorem B3857773 : Blo 2285435 3857773 := bbase (se 3 (by rfl) ⟨723332, by rfl⟩ : syracuseStep 3857773 = 1446665) (by norm_num)
theorem B5143697 : Blo 2285435 5143697 := bstep (se 2 (by rfl) ⟨1928886, by rfl⟩ : syracuseStep 5143697 = 3857773) B3857773
theorem B3429131 : Blo 2285435 3429131 := bstep (se 1 (by rfl) ⟨2571848, by rfl⟩ : syracuseStep 3429131 = 5143697) B5143697
theorem B2286087 : Blo 2285435 2286087 := bstep (se 1 (by rfl) ⟨1714565, by rfl⟩ : syracuseStep 2286087 = 3429131) B3429131
theorem B2571853 : Blo 2285435 2571853 := bbase (se 3 (by rfl) ⟨482222, by rfl⟩ : syracuseStep 2571853 = 964445) (by norm_num)
theorem B3429137 : Blo 2285435 3429137 := bstep (se 2 (by rfl) ⟨1285926, by rfl⟩ : syracuseStep 3429137 = 2571853) B2571853
theorem B2286091 : Blo 2285435 2286091 := bstep (se 1 (by rfl) ⟨1714568, by rfl⟩ : syracuseStep 2286091 = 3429137) B3429137
theorem B7715573 : Blo 2285435 7715573 := bbase (se 5 (by rfl) ⟨361667, by rfl⟩ : syracuseStep 7715573 = 723335) (by norm_num)
theorem B5143715 : Blo 2285435 5143715 := bstep (se 1 (by rfl) ⟨3857786, by rfl⟩ : syracuseStep 5143715 = 7715573) B7715573
theorem B3429143 : Blo 2285435 3429143 := bstep (se 1 (by rfl) ⟨2571857, by rfl⟩ : syracuseStep 3429143 = 5143715) B5143715
theorem B2286095 : Blo 2285435 2286095 := bstep (se 1 (by rfl) ⟨1714571, by rfl⟩ : syracuseStep 2286095 = 3429143) B3429143
theorem B3429149 : Blo 2285435 3429149 := bbase (se 3 (by rfl) ⟨642965, by rfl⟩ : syracuseStep 3429149 = 1285931) (by norm_num)
theorem B2286099 : Blo 2285435 2286099 := bstep (se 1 (by rfl) ⟨1714574, by rfl⟩ : syracuseStep 2286099 = 3429149) B3429149
theorem B5143733 : Blo 2285435 5143733 := bbase (se 5 (by rfl) ⟨241112, by rfl⟩ : syracuseStep 5143733 = 482225) (by norm_num)
theorem B3429155 : Blo 2285435 3429155 := bstep (se 1 (by rfl) ⟨2571866, by rfl⟩ : syracuseStep 3429155 = 5143733) B5143733
theorem B2286103 : Blo 2285435 2286103 := bstep (se 1 (by rfl) ⟨1714577, by rfl⟩ : syracuseStep 2286103 = 3429155) B3429155
theorem B2441269 : Blo 2285435 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B13020101 : Blo 2285435 13020101 := bstep (se 4 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 13020101 = 2441269) B2441269
theorem B8680067 : Blo 2285435 8680067 := bstep (se 1 (by rfl) ⟨6510050, by rfl⟩ : syracuseStep 8680067 = 13020101) B13020101
theorem B5786711 : Blo 2285435 5786711 := bstep (se 1 (by rfl) ⟨4340033, by rfl⟩ : syracuseStep 5786711 = 8680067) B8680067
theorem B3857807 : Blo 2285435 3857807 := bstep (se 1 (by rfl) ⟨2893355, by rfl⟩ : syracuseStep 3857807 = 5786711) B5786711
theorem B2571871 : Blo 2285435 2571871 := bstep (se 1 (by rfl) ⟨1928903, by rfl⟩ : syracuseStep 2571871 = 3857807) B3857807
theorem B3429161 : Blo 2285435 3429161 := bstep (se 2 (by rfl) ⟨1285935, by rfl⟩ : syracuseStep 3429161 = 2571871) B2571871
theorem B2286107 : Blo 2285435 2286107 := bstep (se 1 (by rfl) ⟨1714580, by rfl⟩ : syracuseStep 2286107 = 3429161) B3429161
theorem B2441273 : Blo 2285435 2441273 := bbase (se 2 (by rfl) ⟨915477, by rfl⟩ : syracuseStep 2441273 = 1830955) (by norm_num)
theorem B6510061 : Blo 2285435 6510061 := bstep (se 3 (by rfl) ⟨1220636, by rfl⟩ : syracuseStep 6510061 = 2441273) B2441273
theorem B8680081 : Blo 2285435 8680081 := bstep (se 2 (by rfl) ⟨3255030, by rfl⟩ : syracuseStep 8680081 = 6510061) B6510061
theorem B11573441 : Blo 2285435 11573441 := bstep (se 2 (by rfl) ⟨4340040, by rfl⟩ : syracuseStep 11573441 = 8680081) B8680081
theorem B7715627 : Blo 2285435 7715627 := bstep (se 1 (by rfl) ⟨5786720, by rfl⟩ : syracuseStep 7715627 = 11573441) B11573441
theorem B5143751 : Blo 2285435 5143751 := bstep (se 1 (by rfl) ⟨3857813, by rfl⟩ : syracuseStep 5143751 = 7715627) B7715627
theorem B3429167 : Blo 2285435 3429167 := bstep (se 1 (by rfl) ⟨2571875, by rfl⟩ : syracuseStep 3429167 = 5143751) B5143751
theorem B2286111 : Blo 2285435 2286111 := bstep (se 1 (by rfl) ⟨1714583, by rfl⟩ : syracuseStep 2286111 = 3429167) B3429167
theorem B3429173 : Blo 2285435 3429173 := bbase (se 5 (by rfl) ⟨160742, by rfl⟩ : syracuseStep 3429173 = 321485) (by norm_num)
theorem B2286115 : Blo 2285435 2286115 := bstep (se 1 (by rfl) ⟨1714586, by rfl⟩ : syracuseStep 2286115 = 3429173) B3429173
theorem B5786741 : Blo 2285435 5786741 := bbase (se 5 (by rfl) ⟨271253, by rfl⟩ : syracuseStep 5786741 = 542507) (by norm_num)
theorem B3857827 : Blo 2285435 3857827 := bstep (se 1 (by rfl) ⟨2893370, by rfl⟩ : syracuseStep 3857827 = 5786741) B5786741
theorem B5143769 : Blo 2285435 5143769 := bstep (se 2 (by rfl) ⟨1928913, by rfl⟩ : syracuseStep 5143769 = 3857827) B3857827
theorem B3429179 : Blo 2285435 3429179 := bstep (se 1 (by rfl) ⟨2571884, by rfl⟩ : syracuseStep 3429179 = 5143769) B5143769
theorem B2286119 : Blo 2285435 2286119 := bstep (se 1 (by rfl) ⟨1714589, by rfl⟩ : syracuseStep 2286119 = 3429179) B3429179
theorem B2571889 : Blo 2285435 2571889 := bbase (se 2 (by rfl) ⟨964458, by rfl⟩ : syracuseStep 2571889 = 1928917) (by norm_num)
theorem B3429185 : Blo 2285435 3429185 := bstep (se 2 (by rfl) ⟨1285944, by rfl⟩ : syracuseStep 3429185 = 2571889) B2571889
theorem B2286123 : Blo 2285435 2286123 := bstep (se 1 (by rfl) ⟨1714592, by rfl⟩ : syracuseStep 2286123 = 3429185) B3429185
theorem B3963829 : Blo 2285435 3963829 := bbase (se 5 (by rfl) ⟨185804, by rfl⟩ : syracuseStep 3963829 = 371609) (by norm_num)
theorem B5285105 : Blo 2285435 5285105 := bstep (se 2 (by rfl) ⟨1981914, by rfl⟩ : syracuseStep 5285105 = 3963829) B3963829
theorem B3523403 : Blo 2285435 3523403 := bstep (se 1 (by rfl) ⟨2642552, by rfl⟩ : syracuseStep 3523403 = 5285105) B5285105
theorem B2348935 : Blo 2285435 2348935 := bstep (se 1 (by rfl) ⟨1761701, by rfl⟩ : syracuseStep 2348935 = 3523403) B3523403
theorem B50110613 : Blo 2285435 50110613 := bstep (se 6 (by rfl) ⟨1174467, by rfl⟩ : syracuseStep 50110613 = 2348935) B2348935
theorem B33407075 : Blo 2285435 33407075 := bstep (se 1 (by rfl) ⟨25055306, by rfl⟩ : syracuseStep 33407075 = 50110613) B50110613
theorem B22271383 : Blo 2285435 22271383 := bstep (se 1 (by rfl) ⟨16703537, by rfl⟩ : syracuseStep 22271383 = 33407075) B33407075
theorem B29695177 : Blo 2285435 29695177 := bstep (se 2 (by rfl) ⟨11135691, by rfl⟩ : syracuseStep 29695177 = 22271383) B22271383
theorem B39593569 : Blo 2285435 39593569 := bstep (se 2 (by rfl) ⟨14847588, by rfl⟩ : syracuseStep 39593569 = 29695177) B29695177
theorem B52791425 : Blo 2285435 52791425 := bstep (se 2 (by rfl) ⟨19796784, by rfl⟩ : syracuseStep 52791425 = 39593569) B39593569
theorem B35194283 : Blo 2285435 35194283 := bstep (se 1 (by rfl) ⟨26395712, by rfl⟩ : syracuseStep 35194283 = 52791425) B52791425
theorem B23462855 : Blo 2285435 23462855 := bstep (se 1 (by rfl) ⟨17597141, by rfl⟩ : syracuseStep 23462855 = 35194283) B35194283
theorem B15641903 : Blo 2285435 15641903 := bstep (se 1 (by rfl) ⟨11731427, by rfl⟩ : syracuseStep 15641903 = 23462855) B23462855
theorem B10427935 : Blo 2285435 10427935 := bstep (se 1 (by rfl) ⟨7820951, by rfl⟩ : syracuseStep 10427935 = 15641903) B15641903
theorem B13903913 : Blo 2285435 13903913 := bstep (se 2 (by rfl) ⟨5213967, by rfl⟩ : syracuseStep 13903913 = 10427935) B10427935
theorem B37077101 : Blo 2285435 37077101 := bstep (se 3 (by rfl) ⟨6951956, by rfl⟩ : syracuseStep 37077101 = 13903913) B13903913
theorem B24718067 : Blo 2285435 24718067 := bstep (se 1 (by rfl) ⟨18538550, by rfl⟩ : syracuseStep 24718067 = 37077101) B37077101
theorem B16478711 : Blo 2285435 16478711 := bstep (se 1 (by rfl) ⟨12359033, by rfl⟩ : syracuseStep 16478711 = 24718067) B24718067
theorem B10985807 : Blo 2285435 10985807 := bstep (se 1 (by rfl) ⟨8239355, by rfl⟩ : syracuseStep 10985807 = 16478711) B16478711
theorem B7323871 : Blo 2285435 7323871 := bstep (se 1 (by rfl) ⟨5492903, by rfl⟩ : syracuseStep 7323871 = 10985807) B10985807
theorem B9765161 : Blo 2285435 9765161 := bstep (se 2 (by rfl) ⟨3661935, by rfl⟩ : syracuseStep 9765161 = 7323871) B7323871
theorem B6510107 : Blo 2285435 6510107 := bstep (se 1 (by rfl) ⟨4882580, by rfl⟩ : syracuseStep 6510107 = 9765161) B9765161
theorem B4340071 : Blo 2285435 4340071 := bstep (se 1 (by rfl) ⟨3255053, by rfl⟩ : syracuseStep 4340071 = 6510107) B6510107
theorem B5786761 : Blo 2285435 5786761 := bstep (se 2 (by rfl) ⟨2170035, by rfl⟩ : syracuseStep 5786761 = 4340071) B4340071
theorem B7715681 : Blo 2285435 7715681 := bstep (se 2 (by rfl) ⟨2893380, by rfl⟩ : syracuseStep 7715681 = 5786761) B5786761
theorem B5143787 : Blo 2285435 5143787 := bstep (se 1 (by rfl) ⟨3857840, by rfl⟩ : syracuseStep 5143787 = 7715681) B7715681
theorem B3429191 : Blo 2285435 3429191 := bstep (se 1 (by rfl) ⟨2571893, by rfl⟩ : syracuseStep 3429191 = 5143787) B5143787
theorem B2286127 : Blo 2285435 2286127 := bstep (se 1 (by rfl) ⟨1714595, by rfl⟩ : syracuseStep 2286127 = 3429191) B3429191
theorem B3429197 : Blo 2285435 3429197 := bbase (se 3 (by rfl) ⟨642974, by rfl⟩ : syracuseStep 3429197 = 1285949) (by norm_num)
theorem B2286131 : Blo 2285435 2286131 := bstep (se 1 (by rfl) ⟨1714598, by rfl⟩ : syracuseStep 2286131 = 3429197) B3429197
theorem B5143805 : Blo 2285435 5143805 := bbase (se 3 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 5143805 = 1928927) (by norm_num)
theorem B3429203 : Blo 2285435 3429203 := bstep (se 1 (by rfl) ⟨2571902, by rfl⟩ : syracuseStep 3429203 = 5143805) B5143805
theorem B2286135 : Blo 2285435 2286135 := bstep (se 1 (by rfl) ⟨1714601, by rfl⟩ : syracuseStep 2286135 = 3429203) B3429203
theorem B3857861 : Blo 2285435 3857861 := bbase (se 4 (by rfl) ⟨361674, by rfl⟩ : syracuseStep 3857861 = 723349) (by norm_num)
theorem B2571907 : Blo 2285435 2571907 := bstep (se 1 (by rfl) ⟨1928930, by rfl⟩ : syracuseStep 2571907 = 3857861) B3857861
theorem B3429209 : Blo 2285435 3429209 := bstep (se 2 (by rfl) ⟨1285953, by rfl⟩ : syracuseStep 3429209 = 2571907) B2571907
theorem B2286139 : Blo 2285435 2286139 := bstep (se 1 (by rfl) ⟨1714604, by rfl⟩ : syracuseStep 2286139 = 3429209) B3429209
theorem B17360405 : Blo 2285435 17360405 := bbase (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) (by norm_num)
theorem B11573603 : Blo 2285435 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B7715735 : Blo 2285435 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B5143823 : Blo 2285435 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B3429215 : Blo 2285435 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B2286143 : Blo 2285435 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B3429221 : Blo 2285435 3429221 := bbase (se 4 (by rfl) ⟨321489, by rfl⟩ : syracuseStep 3429221 = 642979) (by norm_num)
theorem B2286147 : Blo 2285435 2286147 := bstep (se 1 (by rfl) ⟨1714610, by rfl⟩ : syracuseStep 2286147 = 3429221) B3429221
theorem B4340117 : Blo 2285435 4340117 := bbase (se 6 (by rfl) ⟨101721, by rfl⟩ : syracuseStep 4340117 = 203443) (by norm_num)
theorem B2893411 : Blo 2285435 2893411 := bstep (se 1 (by rfl) ⟨2170058, by rfl⟩ : syracuseStep 2893411 = 4340117) B4340117
theorem B3857881 : Blo 2285435 3857881 := bstep (se 2 (by rfl) ⟨1446705, by rfl⟩ : syracuseStep 3857881 = 2893411) B2893411
theorem B5143841 : Blo 2285435 5143841 := bstep (se 2 (by rfl) ⟨1928940, by rfl⟩ : syracuseStep 5143841 = 3857881) B3857881
theorem B3429227 : Blo 2285435 3429227 := bstep (se 1 (by rfl) ⟨2571920, by rfl⟩ : syracuseStep 3429227 = 5143841) B5143841
theorem B2286151 : Blo 2285435 2286151 := bstep (se 1 (by rfl) ⟨1714613, by rfl⟩ : syracuseStep 2286151 = 3429227) B3429227
theorem B2571925 : Blo 2285435 2571925 := bbase (se 6 (by rfl) ⟨60279, by rfl⟩ : syracuseStep 2571925 = 120559) (by norm_num)
theorem B3429233 : Blo 2285435 3429233 := bstep (se 2 (by rfl) ⟨1285962, by rfl⟩ : syracuseStep 3429233 = 2571925) B2571925
theorem B2286155 : Blo 2285435 2286155 := bstep (se 1 (by rfl) ⟨1714616, by rfl⟩ : syracuseStep 2286155 = 3429233) B3429233
theorem B2893421 : Blo 2285435 2893421 := bbase (se 3 (by rfl) ⟨542516, by rfl⟩ : syracuseStep 2893421 = 1085033) (by norm_num)
theorem B7715789 : Blo 2285435 7715789 := bstep (se 3 (by rfl) ⟨1446710, by rfl⟩ : syracuseStep 7715789 = 2893421) B2893421
theorem B5143859 : Blo 2285435 5143859 := bstep (se 1 (by rfl) ⟨3857894, by rfl⟩ : syracuseStep 5143859 = 7715789) B7715789
theorem B3429239 : Blo 2285435 3429239 := bstep (se 1 (by rfl) ⟨2571929, by rfl⟩ : syracuseStep 3429239 = 5143859) B5143859
theorem B2286159 : Blo 2285435 2286159 := bstep (se 1 (by rfl) ⟨1714619, by rfl⟩ : syracuseStep 2286159 = 3429239) B3429239
theorem B3429245 : Blo 2285435 3429245 := bbase (se 3 (by rfl) ⟨642983, by rfl⟩ : syracuseStep 3429245 = 1285967) (by norm_num)
theorem B2286163 : Blo 2285435 2286163 := bstep (se 1 (by rfl) ⟨1714622, by rfl⟩ : syracuseStep 2286163 = 3429245) B3429245
theorem B5143877 : Blo 2285435 5143877 := bbase (se 4 (by rfl) ⟨482238, by rfl⟩ : syracuseStep 5143877 = 964477) (by norm_num)
theorem B3429251 : Blo 2285435 3429251 := bstep (se 1 (by rfl) ⟨2571938, by rfl⟩ : syracuseStep 3429251 = 5143877) B5143877
theorem B2286167 : Blo 2285435 2286167 := bstep (se 1 (by rfl) ⟨1714625, by rfl⟩ : syracuseStep 2286167 = 3429251) B3429251
theorem B2746505 : Blo 2285435 2746505 := bbase (se 2 (by rfl) ⟨1029939, by rfl⟩ : syracuseStep 2746505 = 2059879) (by norm_num)
theorem B7324013 : Blo 2285435 7324013 := bstep (se 3 (by rfl) ⟨1373252, by rfl⟩ : syracuseStep 7324013 = 2746505) B2746505
theorem B4882675 : Blo 2285435 4882675 := bstep (se 1 (by rfl) ⟨3662006, by rfl⟩ : syracuseStep 4882675 = 7324013) B7324013
theorem B6510233 : Blo 2285435 6510233 := bstep (se 2 (by rfl) ⟨2441337, by rfl⟩ : syracuseStep 6510233 = 4882675) B4882675
theorem B4340155 : Blo 2285435 4340155 := bstep (se 1 (by rfl) ⟨3255116, by rfl⟩ : syracuseStep 4340155 = 6510233) B6510233
theorem B5786873 : Blo 2285435 5786873 := bstep (se 2 (by rfl) ⟨2170077, by rfl⟩ : syracuseStep 5786873 = 4340155) B4340155
theorem B3857915 : Blo 2285435 3857915 := bstep (se 1 (by rfl) ⟨2893436, by rfl⟩ : syracuseStep 3857915 = 5786873) B5786873
theorem B2571943 : Blo 2285435 2571943 := bstep (se 1 (by rfl) ⟨1928957, by rfl⟩ : syracuseStep 2571943 = 3857915) B3857915
theorem B3429257 : Blo 2285435 3429257 := bstep (se 2 (by rfl) ⟨1285971, by rfl⟩ : syracuseStep 3429257 = 2571943) B2571943
theorem B2286171 : Blo 2285435 2286171 := bstep (se 1 (by rfl) ⟨1714628, by rfl⟩ : syracuseStep 2286171 = 3429257) B3429257
theorem B11573765 : Blo 2285435 11573765 := bbase (se 4 (by rfl) ⟨1085040, by rfl⟩ : syracuseStep 11573765 = 2170081) (by norm_num)
theorem B7715843 : Blo 2285435 7715843 := bstep (se 1 (by rfl) ⟨5786882, by rfl⟩ : syracuseStep 7715843 = 11573765) B11573765
theorem B5143895 : Blo 2285435 5143895 := bstep (se 1 (by rfl) ⟨3857921, by rfl⟩ : syracuseStep 5143895 = 7715843) B7715843
theorem B3429263 : Blo 2285435 3429263 := bstep (se 1 (by rfl) ⟨2571947, by rfl⟩ : syracuseStep 3429263 = 5143895) B5143895
theorem B2286175 : Blo 2285435 2286175 := bstep (se 1 (by rfl) ⟨1714631, by rfl⟩ : syracuseStep 2286175 = 3429263) B3429263
theorem B3429269 : Blo 2285435 3429269 := bbase (se 6 (by rfl) ⟨80373, by rfl⟩ : syracuseStep 3429269 = 160747) (by norm_num)
theorem B2286179 : Blo 2285435 2286179 := bstep (se 1 (by rfl) ⟨1714634, by rfl⟩ : syracuseStep 2286179 = 3429269) B3429269
theorem B13020533 : Blo 2285435 13020533 := bbase (se 5 (by rfl) ⟨610337, by rfl⟩ : syracuseStep 13020533 = 1220675) (by norm_num)
theorem B8680355 : Blo 2285435 8680355 := bstep (se 1 (by rfl) ⟨6510266, by rfl⟩ : syracuseStep 8680355 = 13020533) B13020533
theorem B5786903 : Blo 2285435 5786903 := bstep (se 1 (by rfl) ⟨4340177, by rfl⟩ : syracuseStep 5786903 = 8680355) B8680355
theorem B3857935 : Blo 2285435 3857935 := bstep (se 1 (by rfl) ⟨2893451, by rfl⟩ : syracuseStep 3857935 = 5786903) B5786903
theorem B5143913 : Blo 2285435 5143913 := bstep (se 2 (by rfl) ⟨1928967, by rfl⟩ : syracuseStep 5143913 = 3857935) B3857935
theorem B3429275 : Blo 2285435 3429275 := bstep (se 1 (by rfl) ⟨2571956, by rfl⟩ : syracuseStep 3429275 = 5143913) B5143913
theorem B2286183 : Blo 2285435 2286183 := bstep (se 1 (by rfl) ⟨1714637, by rfl⟩ : syracuseStep 2286183 = 3429275) B3429275
theorem B2571961 : Blo 2285435 2571961 := bbase (se 2 (by rfl) ⟨964485, by rfl⟩ : syracuseStep 2571961 = 1928971) (by norm_num)
theorem B3429281 : Blo 2285435 3429281 := bstep (se 2 (by rfl) ⟨1285980, by rfl⟩ : syracuseStep 3429281 = 2571961) B2571961
theorem B2286187 : Blo 2285435 2286187 := bstep (se 1 (by rfl) ⟨1714640, by rfl⟩ : syracuseStep 2286187 = 3429281) B3429281
theorem B4882717 : Blo 2285435 4882717 := bbase (se 3 (by rfl) ⟨915509, by rfl⟩ : syracuseStep 4882717 = 1831019) (by norm_num)
theorem B6510289 : Blo 2285435 6510289 := bstep (se 2 (by rfl) ⟨2441358, by rfl⟩ : syracuseStep 6510289 = 4882717) B4882717
theorem B8680385 : Blo 2285435 8680385 := bstep (se 2 (by rfl) ⟨3255144, by rfl⟩ : syracuseStep 8680385 = 6510289) B6510289
theorem B5786923 : Blo 2285435 5786923 := bstep (se 1 (by rfl) ⟨4340192, by rfl⟩ : syracuseStep 5786923 = 8680385) B8680385
theorem B7715897 : Blo 2285435 7715897 := bstep (se 2 (by rfl) ⟨2893461, by rfl⟩ : syracuseStep 7715897 = 5786923) B5786923
theorem B5143931 : Blo 2285435 5143931 := bstep (se 1 (by rfl) ⟨3857948, by rfl⟩ : syracuseStep 5143931 = 7715897) B7715897
theorem B3429287 : Blo 2285435 3429287 := bstep (se 1 (by rfl) ⟨2571965, by rfl⟩ : syracuseStep 3429287 = 5143931) B5143931
theorem B2286191 : Blo 2285435 2286191 := bstep (se 1 (by rfl) ⟨1714643, by rfl⟩ : syracuseStep 2286191 = 3429287) B3429287
theorem B3429293 : Blo 2285435 3429293 := bbase (se 3 (by rfl) ⟨642992, by rfl⟩ : syracuseStep 3429293 = 1285985) (by norm_num)
theorem B2286195 : Blo 2285435 2286195 := bstep (se 1 (by rfl) ⟨1714646, by rfl⟩ : syracuseStep 2286195 = 3429293) B3429293
theorem B5143949 : Blo 2285435 5143949 := bbase (se 3 (by rfl) ⟨964490, by rfl⟩ : syracuseStep 5143949 = 1928981) (by norm_num)
theorem B3429299 : Blo 2285435 3429299 := bstep (se 1 (by rfl) ⟨2571974, by rfl⟩ : syracuseStep 3429299 = 5143949) B5143949
theorem B2286199 : Blo 2285435 2286199 := bstep (se 1 (by rfl) ⟨1714649, by rfl⟩ : syracuseStep 2286199 = 3429299) B3429299
theorem B2893477 : Blo 2285435 2893477 := bbase (se 4 (by rfl) ⟨271263, by rfl⟩ : syracuseStep 2893477 = 542527) (by norm_num)
theorem B3857969 : Blo 2285435 3857969 := bstep (se 2 (by rfl) ⟨1446738, by rfl⟩ : syracuseStep 3857969 = 2893477) B2893477
theorem B2571979 : Blo 2285435 2571979 := bstep (se 1 (by rfl) ⟨1928984, by rfl⟩ : syracuseStep 2571979 = 3857969) B3857969
theorem B3429305 : Blo 2285435 3429305 := bstep (se 2 (by rfl) ⟨1285989, by rfl⟩ : syracuseStep 3429305 = 2571979) B2571979
theorem B2286203 : Blo 2285435 2286203 := bstep (se 1 (by rfl) ⟨1714652, by rfl⟩ : syracuseStep 2286203 = 3429305) B3429305
theorem B14094101 : Blo 2285435 14094101 := bbase (se 6 (by rfl) ⟨330330, by rfl⟩ : syracuseStep 14094101 = 660661) (by norm_num)
theorem B37584269 : Blo 2285435 37584269 := bstep (se 3 (by rfl) ⟨7047050, by rfl⟩ : syracuseStep 37584269 = 14094101) B14094101
theorem B25056179 : Blo 2285435 25056179 := bstep (se 1 (by rfl) ⟨18792134, by rfl⟩ : syracuseStep 25056179 = 37584269) B37584269
theorem B16704119 : Blo 2285435 16704119 := bstep (se 1 (by rfl) ⟨12528089, by rfl⟩ : syracuseStep 16704119 = 25056179) B25056179
theorem B11136079 : Blo 2285435 11136079 := bstep (se 1 (by rfl) ⟨8352059, by rfl⟩ : syracuseStep 11136079 = 16704119) B16704119
theorem B14848105 : Blo 2285435 14848105 := bstep (se 2 (by rfl) ⟨5568039, by rfl⟩ : syracuseStep 14848105 = 11136079) B11136079
theorem B19797473 : Blo 2285435 19797473 := bstep (se 2 (by rfl) ⟨7424052, by rfl⟩ : syracuseStep 19797473 = 14848105) B14848105
theorem B13198315 : Blo 2285435 13198315 := bstep (se 1 (by rfl) ⟨9898736, by rfl⟩ : syracuseStep 13198315 = 19797473) B19797473
theorem B17597753 : Blo 2285435 17597753 := bstep (se 2 (by rfl) ⟨6599157, by rfl⟩ : syracuseStep 17597753 = 13198315) B13198315
theorem B11731835 : Blo 2285435 11731835 := bstep (se 1 (by rfl) ⟨8798876, by rfl⟩ : syracuseStep 11731835 = 17597753) B17597753
theorem B31284893 : Blo 2285435 31284893 := bstep (se 3 (by rfl) ⟨5865917, by rfl⟩ : syracuseStep 31284893 = 11731835) B11731835
theorem B83426381 : Blo 2285435 83426381 := bstep (se 3 (by rfl) ⟨15642446, by rfl⟩ : syracuseStep 83426381 = 31284893) B31284893
theorem B55617587 : Blo 2285435 55617587 := bstep (se 1 (by rfl) ⟨41713190, by rfl⟩ : syracuseStep 55617587 = 83426381) B83426381
theorem B37078391 : Blo 2285435 37078391 := bstep (se 1 (by rfl) ⟨27808793, by rfl⟩ : syracuseStep 37078391 = 55617587) B55617587
theorem B24718927 : Blo 2285435 24718927 := bstep (se 1 (by rfl) ⟨18539195, by rfl⟩ : syracuseStep 24718927 = 37078391) B37078391
theorem B32958569 : Blo 2285435 32958569 := bstep (se 2 (by rfl) ⟨12359463, by rfl⟩ : syracuseStep 32958569 = 24718927) B24718927
theorem B21972379 : Blo 2285435 21972379 := bstep (se 1 (by rfl) ⟨16479284, by rfl⟩ : syracuseStep 21972379 = 32958569) B32958569
theorem B29296505 : Blo 2285435 29296505 := bstep (se 2 (by rfl) ⟨10986189, by rfl⟩ : syracuseStep 29296505 = 21972379) B21972379
theorem B19531003 : Blo 2285435 19531003 := bstep (se 1 (by rfl) ⟨14648252, by rfl⟩ : syracuseStep 19531003 = 29296505) B29296505
theorem B26041337 : Blo 2285435 26041337 := bstep (se 2 (by rfl) ⟨9765501, by rfl⟩ : syracuseStep 26041337 = 19531003) B19531003
theorem B17360891 : Blo 2285435 17360891 := bstep (se 1 (by rfl) ⟨13020668, by rfl⟩ : syracuseStep 17360891 = 26041337) B26041337
theorem B11573927 : Blo 2285435 11573927 := bstep (se 1 (by rfl) ⟨8680445, by rfl⟩ : syracuseStep 11573927 = 17360891) B17360891
theorem B7715951 : Blo 2285435 7715951 := bstep (se 1 (by rfl) ⟨5786963, by rfl⟩ : syracuseStep 7715951 = 11573927) B11573927
theorem B5143967 : Blo 2285435 5143967 := bstep (se 1 (by rfl) ⟨3857975, by rfl⟩ : syracuseStep 5143967 = 7715951) B7715951
theorem B3429311 : Blo 2285435 3429311 := bstep (se 1 (by rfl) ⟨2571983, by rfl⟩ : syracuseStep 3429311 = 5143967) B5143967
theorem B2286207 : Blo 2285435 2286207 := bstep (se 1 (by rfl) ⟨1714655, by rfl⟩ : syracuseStep 2286207 = 3429311) B3429311
theorem B3429317 : Blo 2285435 3429317 := bbase (se 4 (by rfl) ⟨321498, by rfl⟩ : syracuseStep 3429317 = 642997) (by norm_num)
theorem B2286211 : Blo 2285435 2286211 := bstep (se 1 (by rfl) ⟨1714658, by rfl⟩ : syracuseStep 2286211 = 3429317) B3429317
theorem B3857989 : Blo 2285435 3857989 := bbase (se 4 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 3857989 = 723373) (by norm_num)
theorem B5143985 : Blo 2285435 5143985 := bstep (se 2 (by rfl) ⟨1928994, by rfl⟩ : syracuseStep 5143985 = 3857989) B3857989
theorem B3429323 : Blo 2285435 3429323 := bstep (se 1 (by rfl) ⟨2571992, by rfl⟩ : syracuseStep 3429323 = 5143985) B5143985
theorem B2286215 : Blo 2285435 2286215 := bstep (se 1 (by rfl) ⟨1714661, by rfl⟩ : syracuseStep 2286215 = 3429323) B3429323
theorem B2571997 : Blo 2285435 2571997 := bbase (se 3 (by rfl) ⟨482249, by rfl⟩ : syracuseStep 2571997 = 964499) (by norm_num)
theorem B3429329 : Blo 2285435 3429329 := bstep (se 2 (by rfl) ⟨1285998, by rfl⟩ : syracuseStep 3429329 = 2571997) B2571997
theorem B2286219 : Blo 2285435 2286219 := bstep (se 1 (by rfl) ⟨1714664, by rfl⟩ : syracuseStep 2286219 = 3429329) B3429329
theorem B7716005 : Blo 2285435 7716005 := bbase (se 4 (by rfl) ⟨723375, by rfl⟩ : syracuseStep 7716005 = 1446751) (by norm_num)
theorem B5144003 : Blo 2285435 5144003 := bstep (se 1 (by rfl) ⟨3858002, by rfl⟩ : syracuseStep 5144003 = 7716005) B7716005
theorem B3429335 : Blo 2285435 3429335 := bstep (se 1 (by rfl) ⟨2572001, by rfl⟩ : syracuseStep 3429335 = 5144003) B5144003
theorem B2286223 : Blo 2285435 2286223 := bstep (se 1 (by rfl) ⟨1714667, by rfl⟩ : syracuseStep 2286223 = 3429335) B3429335
theorem B3429341 : Blo 2285435 3429341 := bbase (se 3 (by rfl) ⟨643001, by rfl⟩ : syracuseStep 3429341 = 1286003) (by norm_num)
theorem B2286227 : Blo 2285435 2286227 := bstep (se 1 (by rfl) ⟨1714670, by rfl⟩ : syracuseStep 2286227 = 3429341) B3429341
theorem B5144021 : Blo 2285435 5144021 := bbase (se 7 (by rfl) ⟨60281, by rfl⟩ : syracuseStep 5144021 = 120563) (by norm_num)
theorem B3429347 : Blo 2285435 3429347 := bstep (se 1 (by rfl) ⟨2572010, by rfl⟩ : syracuseStep 3429347 = 5144021) B5144021
theorem B2286231 : Blo 2285435 2286231 := bstep (se 1 (by rfl) ⟨1714673, by rfl⟩ : syracuseStep 2286231 = 3429347) B3429347
theorem B3299621 : Blo 2285435 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B8798989 : Blo 2285435 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B11731985 : Blo 2285435 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B7821323 : Blo 2285435 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B5214215 : Blo 2285435 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B3476143 : Blo 2285435 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B4634857 : Blo 2285435 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B6179809 : Blo 2285435 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B8239745 : Blo 2285435 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B21972653 : Blo 2285435 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B14648435 : Blo 2285435 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B9765623 : Blo 2285435 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B6510415 : Blo 2285435 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B8680553 : Blo 2285435 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B5787035 : Blo 2285435 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B3858023 : Blo 2285435 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B2572015 : Blo 2285435 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B3429353 : Blo 2285435 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B2286235 : Blo 2285435 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B7324229 : Blo 2285435 7324229 := bbase (se 4 (by rfl) ⟨686646, by rfl⟩ : syracuseStep 7324229 = 1373293) (by norm_num)
theorem B19531277 : Blo 2285435 19531277 := bstep (se 3 (by rfl) ⟨3662114, by rfl⟩ : syracuseStep 19531277 = 7324229) B7324229
theorem B13020851 : Blo 2285435 13020851 := bstep (se 1 (by rfl) ⟨9765638, by rfl⟩ : syracuseStep 13020851 = 19531277) B19531277
theorem B8680567 : Blo 2285435 8680567 := bstep (se 1 (by rfl) ⟨6510425, by rfl⟩ : syracuseStep 8680567 = 13020851) B13020851
theorem B11574089 : Blo 2285435 11574089 := bstep (se 2 (by rfl) ⟨4340283, by rfl⟩ : syracuseStep 11574089 = 8680567) B8680567
theorem B7716059 : Blo 2285435 7716059 := bstep (se 1 (by rfl) ⟨5787044, by rfl⟩ : syracuseStep 7716059 = 11574089) B11574089
theorem B5144039 : Blo 2285435 5144039 := bstep (se 1 (by rfl) ⟨3858029, by rfl⟩ : syracuseStep 5144039 = 7716059) B7716059
theorem B3429359 : Blo 2285435 3429359 := bstep (se 1 (by rfl) ⟨2572019, by rfl⟩ : syracuseStep 3429359 = 5144039) B5144039
theorem B2286239 : Blo 2285435 2286239 := bstep (se 1 (by rfl) ⟨1714679, by rfl⟩ : syracuseStep 2286239 = 3429359) B3429359
theorem B3429365 : Blo 2285435 3429365 := bbase (se 5 (by rfl) ⟨160751, by rfl⟩ : syracuseStep 3429365 = 321503) (by norm_num)
theorem B2286243 : Blo 2285435 2286243 := bstep (se 1 (by rfl) ⟨1714682, by rfl⟩ : syracuseStep 2286243 = 3429365) B3429365
theorem B4882837 : Blo 2285435 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B6510449 : Blo 2285435 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B4340299 : Blo 2285435 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B5787065 : Blo 2285435 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B3858043 : Blo 2285435 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B5144057 : Blo 2285435 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B3429371 : Blo 2285435 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B2286247 : Blo 2285435 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B2572033 : Blo 2285435 2572033 := bbase (se 2 (by rfl) ⟨964512, by rfl⟩ : syracuseStep 2572033 = 1929025) (by norm_num)
theorem B3429377 : Blo 2285435 3429377 := bstep (se 2 (by rfl) ⟨1286016, by rfl⟩ : syracuseStep 3429377 = 2572033) B2572033
theorem B2286251 : Blo 2285435 2286251 := bstep (se 1 (by rfl) ⟨1714688, by rfl⟩ : syracuseStep 2286251 = 3429377) B3429377
theorem B5787085 : Blo 2285435 5787085 := bbase (se 3 (by rfl) ⟨1085078, by rfl⟩ : syracuseStep 5787085 = 2170157) (by norm_num)
theorem B7716113 : Blo 2285435 7716113 := bstep (se 2 (by rfl) ⟨2893542, by rfl⟩ : syracuseStep 7716113 = 5787085) B5787085
theorem B5144075 : Blo 2285435 5144075 := bstep (se 1 (by rfl) ⟨3858056, by rfl⟩ : syracuseStep 5144075 = 7716113) B7716113
theorem B3429383 : Blo 2285435 3429383 := bstep (se 1 (by rfl) ⟨2572037, by rfl⟩ : syracuseStep 3429383 = 5144075) B5144075
theorem B2286255 : Blo 2285435 2286255 := bstep (se 1 (by rfl) ⟨1714691, by rfl⟩ : syracuseStep 2286255 = 3429383) B3429383
theorem B3429389 : Blo 2285435 3429389 := bbase (se 3 (by rfl) ⟨643010, by rfl⟩ : syracuseStep 3429389 = 1286021) (by norm_num)
theorem B2286259 : Blo 2285435 2286259 := bstep (se 1 (by rfl) ⟨1714694, by rfl⟩ : syracuseStep 2286259 = 3429389) B3429389
theorem B5144093 : Blo 2285435 5144093 := bbase (se 3 (by rfl) ⟨964517, by rfl⟩ : syracuseStep 5144093 = 1929035) (by norm_num)
theorem B3429395 : Blo 2285435 3429395 := bstep (se 1 (by rfl) ⟨2572046, by rfl⟩ : syracuseStep 3429395 = 5144093) B5144093
theorem B2286263 : Blo 2285435 2286263 := bstep (se 1 (by rfl) ⟨1714697, by rfl⟩ : syracuseStep 2286263 = 3429395) B3429395
theorem B3858077 : Blo 2285435 3858077 := bbase (se 3 (by rfl) ⟨723389, by rfl⟩ : syracuseStep 3858077 = 1446779) (by norm_num)
theorem B2572051 : Blo 2285435 2572051 := bstep (se 1 (by rfl) ⟨1929038, by rfl⟩ : syracuseStep 2572051 = 3858077) B3858077
theorem B3429401 : Blo 2285435 3429401 := bstep (se 2 (by rfl) ⟨1286025, by rfl⟩ : syracuseStep 3429401 = 2572051) B2572051
theorem B2286267 : Blo 2285435 2286267 := bstep (se 1 (by rfl) ⟨1714700, by rfl⟩ : syracuseStep 2286267 = 3429401) B3429401
theorem B3476197 : Blo 2285435 3476197 := bbase (se 4 (by rfl) ⟨325893, by rfl⟩ : syracuseStep 3476197 = 651787) (by norm_num)
theorem B4634929 : Blo 2285435 4634929 := bstep (se 2 (by rfl) ⟨1738098, by rfl⟩ : syracuseStep 4634929 = 3476197) B3476197
theorem B6179905 : Blo 2285435 6179905 := bstep (se 2 (by rfl) ⟨2317464, by rfl⟩ : syracuseStep 6179905 = 4634929) B4634929
theorem B32959493 : Blo 2285435 32959493 := bstep (se 4 (by rfl) ⟨3089952, by rfl⟩ : syracuseStep 32959493 = 6179905) B6179905
theorem B21972995 : Blo 2285435 21972995 := bstep (se 1 (by rfl) ⟨16479746, by rfl⟩ : syracuseStep 21972995 = 32959493) B32959493
theorem B14648663 : Blo 2285435 14648663 := bstep (se 1 (by rfl) ⟨10986497, by rfl⟩ : syracuseStep 14648663 = 21972995) B21972995
theorem B9765775 : Blo 2285435 9765775 := bstep (se 1 (by rfl) ⟨7324331, by rfl⟩ : syracuseStep 9765775 = 14648663) B14648663
theorem B13021033 : Blo 2285435 13021033 := bstep (se 2 (by rfl) ⟨4882887, by rfl⟩ : syracuseStep 13021033 = 9765775) B9765775
theorem B17361377 : Blo 2285435 17361377 := bstep (se 2 (by rfl) ⟨6510516, by rfl⟩ : syracuseStep 17361377 = 13021033) B13021033
theorem B11574251 : Blo 2285435 11574251 := bstep (se 1 (by rfl) ⟨8680688, by rfl⟩ : syracuseStep 11574251 = 17361377) B17361377
theorem B7716167 : Blo 2285435 7716167 := bstep (se 1 (by rfl) ⟨5787125, by rfl⟩ : syracuseStep 7716167 = 11574251) B11574251
theorem B5144111 : Blo 2285435 5144111 := bstep (se 1 (by rfl) ⟨3858083, by rfl⟩ : syracuseStep 5144111 = 7716167) B7716167
theorem B3429407 : Blo 2285435 3429407 := bstep (se 1 (by rfl) ⟨2572055, by rfl⟩ : syracuseStep 3429407 = 5144111) B5144111
theorem B2286271 : Blo 2285435 2286271 := bstep (se 1 (by rfl) ⟨1714703, by rfl⟩ : syracuseStep 2286271 = 3429407) B3429407
theorem B3429413 : Blo 2285435 3429413 := bbase (se 4 (by rfl) ⟨321507, by rfl⟩ : syracuseStep 3429413 = 643015) (by norm_num)
theorem B2286275 : Blo 2285435 2286275 := bstep (se 1 (by rfl) ⟨1714706, by rfl⟩ : syracuseStep 2286275 = 3429413) B3429413
theorem B2893573 : Blo 2285435 2893573 := bbase (se 4 (by rfl) ⟨271272, by rfl⟩ : syracuseStep 2893573 = 542545) (by norm_num)
theorem B3858097 : Blo 2285435 3858097 := bstep (se 2 (by rfl) ⟨1446786, by rfl⟩ : syracuseStep 3858097 = 2893573) B2893573
theorem B5144129 : Blo 2285435 5144129 := bstep (se 2 (by rfl) ⟨1929048, by rfl⟩ : syracuseStep 5144129 = 3858097) B3858097
theorem B3429419 : Blo 2285435 3429419 := bstep (se 1 (by rfl) ⟨2572064, by rfl⟩ : syracuseStep 3429419 = 5144129) B5144129
theorem B2286279 : Blo 2285435 2286279 := bstep (se 1 (by rfl) ⟨1714709, by rfl⟩ : syracuseStep 2286279 = 3429419) B3429419
theorem B2572069 : Blo 2285435 2572069 := bbase (se 4 (by rfl) ⟨241131, by rfl⟩ : syracuseStep 2572069 = 482263) (by norm_num)
theorem B3429425 : Blo 2285435 3429425 := bstep (se 2 (by rfl) ⟨1286034, by rfl⟩ : syracuseStep 3429425 = 2572069) B2572069
theorem B2286283 : Blo 2285435 2286283 := bstep (se 1 (by rfl) ⟨1714712, by rfl⟩ : syracuseStep 2286283 = 3429425) B3429425
theorem B9765845 : Blo 2285435 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B6510563 : Blo 2285435 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B4340375 : Blo 2285435 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B2893583 : Blo 2285435 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B7716221 : Blo 2285435 7716221 := bstep (se 3 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 7716221 = 2893583) B2893583
theorem B5144147 : Blo 2285435 5144147 := bstep (se 1 (by rfl) ⟨3858110, by rfl⟩ : syracuseStep 5144147 = 7716221) B7716221
theorem B3429431 : Blo 2285435 3429431 := bstep (se 1 (by rfl) ⟨2572073, by rfl⟩ : syracuseStep 3429431 = 5144147) B5144147
theorem B2286287 : Blo 2285435 2286287 := bstep (se 1 (by rfl) ⟨1714715, by rfl⟩ : syracuseStep 2286287 = 3429431) B3429431
theorem B3429437 : Blo 2285435 3429437 := bbase (se 3 (by rfl) ⟨643019, by rfl⟩ : syracuseStep 3429437 = 1286039) (by norm_num)
theorem B2286291 : Blo 2285435 2286291 := bstep (se 1 (by rfl) ⟨1714718, by rfl⟩ : syracuseStep 2286291 = 3429437) B3429437
theorem B5144165 : Blo 2285435 5144165 := bbase (se 4 (by rfl) ⟨482265, by rfl⟩ : syracuseStep 5144165 = 964531) (by norm_num)
theorem B3429443 : Blo 2285435 3429443 := bstep (se 1 (by rfl) ⟨2572082, by rfl⟩ : syracuseStep 3429443 = 5144165) B5144165
theorem B2286295 : Blo 2285435 2286295 := bstep (se 1 (by rfl) ⟨1714721, by rfl⟩ : syracuseStep 2286295 = 3429443) B3429443
theorem B5787197 : Blo 2285435 5787197 := bbase (se 3 (by rfl) ⟨1085099, by rfl⟩ : syracuseStep 5787197 = 2170199) (by norm_num)
theorem B3858131 : Blo 2285435 3858131 := bstep (se 1 (by rfl) ⟨2893598, by rfl⟩ : syracuseStep 3858131 = 5787197) B5787197
theorem B2572087 : Blo 2285435 2572087 := bstep (se 1 (by rfl) ⟨1929065, by rfl⟩ : syracuseStep 2572087 = 3858131) B3858131
theorem B3429449 : Blo 2285435 3429449 := bstep (se 2 (by rfl) ⟨1286043, by rfl⟩ : syracuseStep 3429449 = 2572087) B2572087
theorem B2286299 : Blo 2285435 2286299 := bstep (se 1 (by rfl) ⟨1714724, by rfl⟩ : syracuseStep 2286299 = 3429449) B3429449
theorem B4340405 : Blo 2285435 4340405 := bbase (se 5 (by rfl) ⟨203456, by rfl⟩ : syracuseStep 4340405 = 406913) (by norm_num)
theorem B11574413 : Blo 2285435 11574413 := bstep (se 3 (by rfl) ⟨2170202, by rfl⟩ : syracuseStep 11574413 = 4340405) B4340405
theorem B7716275 : Blo 2285435 7716275 := bstep (se 1 (by rfl) ⟨5787206, by rfl⟩ : syracuseStep 7716275 = 11574413) B11574413
theorem B5144183 : Blo 2285435 5144183 := bstep (se 1 (by rfl) ⟨3858137, by rfl⟩ : syracuseStep 5144183 = 7716275) B7716275
theorem B3429455 : Blo 2285435 3429455 := bstep (se 1 (by rfl) ⟨2572091, by rfl⟩ : syracuseStep 3429455 = 5144183) B5144183
theorem B2286303 : Blo 2285435 2286303 := bstep (se 1 (by rfl) ⟨1714727, by rfl⟩ : syracuseStep 2286303 = 3429455) B3429455
theorem B3429461 : Blo 2285435 3429461 := bbase (se 8 (by rfl) ⟨20094, by rfl⟩ : syracuseStep 3429461 = 40189) (by norm_num)
theorem B2286307 : Blo 2285435 2286307 := bstep (se 1 (by rfl) ⟨1714730, by rfl⟩ : syracuseStep 2286307 = 3429461) B3429461
theorem B6952517 : Blo 2285435 6952517 := bbase (se 4 (by rfl) ⟨651798, by rfl⟩ : syracuseStep 6952517 = 1303597) (by norm_num)
theorem B4635011 : Blo 2285435 4635011 := bstep (se 1 (by rfl) ⟨3476258, by rfl⟩ : syracuseStep 4635011 = 6952517) B6952517
theorem B3090007 : Blo 2285435 3090007 := bstep (se 1 (by rfl) ⟨2317505, by rfl⟩ : syracuseStep 3090007 = 4635011) B4635011
theorem B16480037 : Blo 2285435 16480037 := bstep (se 4 (by rfl) ⟨1545003, by rfl⟩ : syracuseStep 16480037 = 3090007) B3090007
theorem B10986691 : Blo 2285435 10986691 := bstep (se 1 (by rfl) ⟨8240018, by rfl⟩ : syracuseStep 10986691 = 16480037) B16480037
theorem B14648921 : Blo 2285435 14648921 := bstep (se 2 (by rfl) ⟨5493345, by rfl⟩ : syracuseStep 14648921 = 10986691) B10986691
theorem B9765947 : Blo 2285435 9765947 := bstep (se 1 (by rfl) ⟨7324460, by rfl⟩ : syracuseStep 9765947 = 14648921) B14648921
theorem B6510631 : Blo 2285435 6510631 := bstep (se 1 (by rfl) ⟨4882973, by rfl⟩ : syracuseStep 6510631 = 9765947) B9765947
theorem B8680841 : Blo 2285435 8680841 := bstep (se 2 (by rfl) ⟨3255315, by rfl⟩ : syracuseStep 8680841 = 6510631) B6510631
theorem B5787227 : Blo 2285435 5787227 := bstep (se 1 (by rfl) ⟨4340420, by rfl⟩ : syracuseStep 5787227 = 8680841) B8680841
theorem B3858151 : Blo 2285435 3858151 := bstep (se 1 (by rfl) ⟨2893613, by rfl⟩ : syracuseStep 3858151 = 5787227) B5787227
theorem B5144201 : Blo 2285435 5144201 := bstep (se 2 (by rfl) ⟨1929075, by rfl⟩ : syracuseStep 5144201 = 3858151) B3858151
theorem B3429467 : Blo 2285435 3429467 := bstep (se 1 (by rfl) ⟨2572100, by rfl⟩ : syracuseStep 3429467 = 5144201) B5144201
theorem B2286311 : Blo 2285435 2286311 := bstep (se 1 (by rfl) ⟨1714733, by rfl⟩ : syracuseStep 2286311 = 3429467) B3429467
theorem B2572105 : Blo 2285435 2572105 := bbase (se 2 (by rfl) ⟨964539, by rfl⟩ : syracuseStep 2572105 = 1929079) (by norm_num)
theorem B3429473 : Blo 2285435 3429473 := bstep (se 2 (by rfl) ⟨1286052, by rfl⟩ : syracuseStep 3429473 = 2572105) B2572105
theorem B2286315 : Blo 2285435 2286315 := bstep (se 1 (by rfl) ⟨1714736, by rfl⟩ : syracuseStep 2286315 = 3429473) B3429473
theorem B9270053 : Blo 2285435 9270053 := bbase (se 4 (by rfl) ⟨869067, by rfl⟩ : syracuseStep 9270053 = 1738135) (by norm_num)
theorem B6180035 : Blo 2285435 6180035 := bstep (se 1 (by rfl) ⟨4635026, by rfl⟩ : syracuseStep 6180035 = 9270053) B9270053
theorem B16480093 : Blo 2285435 16480093 := bstep (se 3 (by rfl) ⟨3090017, by rfl⟩ : syracuseStep 16480093 = 6180035) B6180035
theorem B21973457 : Blo 2285435 21973457 := bstep (se 2 (by rfl) ⟨8240046, by rfl⟩ : syracuseStep 21973457 = 16480093) B16480093
theorem B14648971 : Blo 2285435 14648971 := bstep (se 1 (by rfl) ⟨10986728, by rfl⟩ : syracuseStep 14648971 = 21973457) B21973457
theorem B19531961 : Blo 2285435 19531961 := bstep (se 2 (by rfl) ⟨7324485, by rfl⟩ : syracuseStep 19531961 = 14648971) B14648971
theorem B13021307 : Blo 2285435 13021307 := bstep (se 1 (by rfl) ⟨9765980, by rfl⟩ : syracuseStep 13021307 = 19531961) B19531961
theorem B8680871 : Blo 2285435 8680871 := bstep (se 1 (by rfl) ⟨6510653, by rfl⟩ : syracuseStep 8680871 = 13021307) B13021307
theorem B5787247 : Blo 2285435 5787247 := bstep (se 1 (by rfl) ⟨4340435, by rfl⟩ : syracuseStep 5787247 = 8680871) B8680871
theorem B7716329 : Blo 2285435 7716329 := bstep (se 2 (by rfl) ⟨2893623, by rfl⟩ : syracuseStep 7716329 = 5787247) B5787247
theorem B5144219 : Blo 2285435 5144219 := bstep (se 1 (by rfl) ⟨3858164, by rfl⟩ : syracuseStep 5144219 = 7716329) B7716329
theorem B3429479 : Blo 2285435 3429479 := bstep (se 1 (by rfl) ⟨2572109, by rfl⟩ : syracuseStep 3429479 = 5144219) B5144219
theorem B2286319 : Blo 2285435 2286319 := bstep (se 1 (by rfl) ⟨1714739, by rfl⟩ : syracuseStep 2286319 = 3429479) B3429479
theorem B3429485 : Blo 2285435 3429485 := bbase (se 3 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 3429485 = 1286057) (by norm_num)
theorem B2286323 : Blo 2285435 2286323 := bstep (se 1 (by rfl) ⟨1714742, by rfl⟩ : syracuseStep 2286323 = 3429485) B3429485
theorem B5144237 : Blo 2285435 5144237 := bbase (se 3 (by rfl) ⟨964544, by rfl⟩ : syracuseStep 5144237 = 1929089) (by norm_num)
theorem B3429491 : Blo 2285435 3429491 := bstep (se 1 (by rfl) ⟨2572118, by rfl⟩ : syracuseStep 3429491 = 5144237) B5144237
theorem B2286327 : Blo 2285435 2286327 := bstep (se 1 (by rfl) ⟨1714745, by rfl⟩ : syracuseStep 2286327 = 3429491) B3429491
theorem B4635053 : Blo 2285435 4635053 := bbase (se 3 (by rfl) ⟨869072, by rfl⟩ : syracuseStep 4635053 = 1738145) (by norm_num)
theorem B3090035 : Blo 2285435 3090035 := bstep (se 1 (by rfl) ⟨2317526, by rfl⟩ : syracuseStep 3090035 = 4635053) B4635053
theorem B8240093 : Blo 2285435 8240093 := bstep (se 3 (by rfl) ⟨1545017, by rfl⟩ : syracuseStep 8240093 = 3090035) B3090035
theorem B5493395 : Blo 2285435 5493395 := bstep (se 1 (by rfl) ⟨4120046, by rfl⟩ : syracuseStep 5493395 = 8240093) B8240093
theorem B3662263 : Blo 2285435 3662263 := bstep (se 1 (by rfl) ⟨2746697, by rfl⟩ : syracuseStep 3662263 = 5493395) B5493395
theorem B4883017 : Blo 2285435 4883017 := bstep (se 2 (by rfl) ⟨1831131, by rfl⟩ : syracuseStep 4883017 = 3662263) B3662263
theorem B6510689 : Blo 2285435 6510689 := bstep (se 2 (by rfl) ⟨2441508, by rfl⟩ : syracuseStep 6510689 = 4883017) B4883017
theorem B4340459 : Blo 2285435 4340459 := bstep (se 1 (by rfl) ⟨3255344, by rfl⟩ : syracuseStep 4340459 = 6510689) B6510689
theorem B2893639 : Blo 2285435 2893639 := bstep (se 1 (by rfl) ⟨2170229, by rfl⟩ : syracuseStep 2893639 = 4340459) B4340459
theorem B3858185 : Blo 2285435 3858185 := bstep (se 2 (by rfl) ⟨1446819, by rfl⟩ : syracuseStep 3858185 = 2893639) B2893639
theorem B2572123 : Blo 2285435 2572123 := bstep (se 1 (by rfl) ⟨1929092, by rfl⟩ : syracuseStep 2572123 = 3858185) B3858185
theorem B3429497 : Blo 2285435 3429497 := bstep (se 2 (by rfl) ⟨1286061, by rfl⟩ : syracuseStep 3429497 = 2572123) B2572123
theorem B2286331 : Blo 2285435 2286331 := bstep (se 1 (by rfl) ⟨1714748, by rfl⟩ : syracuseStep 2286331 = 3429497) B3429497
theorem B4399685 : Blo 2285435 4399685 := bbase (se 4 (by rfl) ⟨412470, by rfl⟩ : syracuseStep 4399685 = 824941) (by norm_num)
theorem B2933123 : Blo 2285435 2933123 := bstep (se 1 (by rfl) ⟨2199842, by rfl⟩ : syracuseStep 2933123 = 4399685) B4399685
theorem B31286645 : Blo 2285435 31286645 := bstep (se 5 (by rfl) ⟨1466561, by rfl⟩ : syracuseStep 31286645 = 2933123) B2933123
theorem B20857763 : Blo 2285435 20857763 := bstep (se 1 (by rfl) ⟨15643322, by rfl⟩ : syracuseStep 20857763 = 31286645) B31286645
theorem B55620701 : Blo 2285435 55620701 := bstep (se 3 (by rfl) ⟨10428881, by rfl⟩ : syracuseStep 55620701 = 20857763) B20857763
theorem B37080467 : Blo 2285435 37080467 := bstep (se 1 (by rfl) ⟨27810350, by rfl⟩ : syracuseStep 37080467 = 55620701) B55620701
theorem B24720311 : Blo 2285435 24720311 := bstep (se 1 (by rfl) ⟨18540233, by rfl⟩ : syracuseStep 24720311 = 37080467) B37080467
theorem B16480207 : Blo 2285435 16480207 := bstep (se 1 (by rfl) ⟨12360155, by rfl⟩ : syracuseStep 16480207 = 24720311) B24720311
theorem B21973609 : Blo 2285435 21973609 := bstep (se 2 (by rfl) ⟨8240103, by rfl⟩ : syracuseStep 21973609 = 16480207) B16480207
theorem B29298145 : Blo 2285435 29298145 := bstep (se 2 (by rfl) ⟨10986804, by rfl⟩ : syracuseStep 29298145 = 21973609) B21973609
theorem B39064193 : Blo 2285435 39064193 := bstep (se 2 (by rfl) ⟨14649072, by rfl⟩ : syracuseStep 39064193 = 29298145) B29298145
theorem B26042795 : Blo 2285435 26042795 := bstep (se 1 (by rfl) ⟨19532096, by rfl⟩ : syracuseStep 26042795 = 39064193) B39064193
theorem B17361863 : Blo 2285435 17361863 := bstep (se 1 (by rfl) ⟨13021397, by rfl⟩ : syracuseStep 17361863 = 26042795) B26042795
theorem B11574575 : Blo 2285435 11574575 := bstep (se 1 (by rfl) ⟨8680931, by rfl⟩ : syracuseStep 11574575 = 17361863) B17361863
theorem B7716383 : Blo 2285435 7716383 := bstep (se 1 (by rfl) ⟨5787287, by rfl⟩ : syracuseStep 7716383 = 11574575) B11574575
theorem B5144255 : Blo 2285435 5144255 := bstep (se 1 (by rfl) ⟨3858191, by rfl⟩ : syracuseStep 5144255 = 7716383) B7716383
theorem B3429503 : Blo 2285435 3429503 := bstep (se 1 (by rfl) ⟨2572127, by rfl⟩ : syracuseStep 3429503 = 5144255) B5144255
theorem B2286335 : Blo 2285435 2286335 := bstep (se 1 (by rfl) ⟨1714751, by rfl⟩ : syracuseStep 2286335 = 3429503) B3429503
theorem B3429509 : Blo 2285435 3429509 := bbase (se 4 (by rfl) ⟨321516, by rfl⟩ : syracuseStep 3429509 = 643033) (by norm_num)
theorem B2286339 : Blo 2285435 2286339 := bstep (se 1 (by rfl) ⟨1714754, by rfl⟩ : syracuseStep 2286339 = 3429509) B3429509
theorem B3858205 : Blo 2285435 3858205 := bbase (se 3 (by rfl) ⟨723413, by rfl⟩ : syracuseStep 3858205 = 1446827) (by norm_num)
theorem B5144273 : Blo 2285435 5144273 := bstep (se 2 (by rfl) ⟨1929102, by rfl⟩ : syracuseStep 5144273 = 3858205) B3858205
theorem B3429515 : Blo 2285435 3429515 := bstep (se 1 (by rfl) ⟨2572136, by rfl⟩ : syracuseStep 3429515 = 5144273) B5144273
theorem B2286343 : Blo 2285435 2286343 := bstep (se 1 (by rfl) ⟨1714757, by rfl⟩ : syracuseStep 2286343 = 3429515) B3429515
theorem B2572141 : Blo 2285435 2572141 := bbase (se 3 (by rfl) ⟨482276, by rfl⟩ : syracuseStep 2572141 = 964553) (by norm_num)
theorem B3429521 : Blo 2285435 3429521 := bstep (se 2 (by rfl) ⟨1286070, by rfl⟩ : syracuseStep 3429521 = 2572141) B2572141
theorem B2286347 : Blo 2285435 2286347 := bstep (se 1 (by rfl) ⟨1714760, by rfl⟩ : syracuseStep 2286347 = 3429521) B3429521
theorem B7716437 : Blo 2285435 7716437 := bbase (se 8 (by rfl) ⟨45213, by rfl⟩ : syracuseStep 7716437 = 90427) (by norm_num)
theorem B5144291 : Blo 2285435 5144291 := bstep (se 1 (by rfl) ⟨3858218, by rfl⟩ : syracuseStep 5144291 = 7716437) B7716437
theorem B3429527 : Blo 2285435 3429527 := bstep (se 1 (by rfl) ⟨2572145, by rfl⟩ : syracuseStep 3429527 = 5144291) B5144291
theorem B2286351 : Blo 2285435 2286351 := bstep (se 1 (by rfl) ⟨1714763, by rfl⟩ : syracuseStep 2286351 = 3429527) B3429527
theorem B3429533 : Blo 2285435 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2286355 : Blo 2285435 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B5144309 : Blo 2285435 5144309 := bbase (se 5 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 5144309 = 482279) (by norm_num)
theorem B3429539 : Blo 2285435 3429539 := bstep (se 1 (by rfl) ⟨2572154, by rfl⟩ : syracuseStep 3429539 = 5144309) B5144309
theorem B2286359 : Blo 2285435 2286359 := bstep (se 1 (by rfl) ⟨1714769, by rfl⟩ : syracuseStep 2286359 = 3429539) B3429539
theorem B10429013 : Blo 2285435 10429013 := bbase (se 8 (by rfl) ⟨61107, by rfl⟩ : syracuseStep 10429013 = 122215) (by norm_num)
theorem B6952675 : Blo 2285435 6952675 := bstep (se 1 (by rfl) ⟨5214506, by rfl⟩ : syracuseStep 6952675 = 10429013) B10429013
theorem B9270233 : Blo 2285435 9270233 := bstep (se 2 (by rfl) ⟨3476337, by rfl⟩ : syracuseStep 9270233 = 6952675) B6952675
theorem B6180155 : Blo 2285435 6180155 := bstep (se 1 (by rfl) ⟨4635116, by rfl⟩ : syracuseStep 6180155 = 9270233) B9270233
theorem B4120103 : Blo 2285435 4120103 := bstep (se 1 (by rfl) ⟨3090077, by rfl⟩ : syracuseStep 4120103 = 6180155) B6180155
theorem B10986941 : Blo 2285435 10986941 := bstep (se 3 (by rfl) ⟨2060051, by rfl⟩ : syracuseStep 10986941 = 4120103) B4120103
theorem B29298509 : Blo 2285435 29298509 := bstep (se 3 (by rfl) ⟨5493470, by rfl⟩ : syracuseStep 29298509 = 10986941) B10986941
theorem B19532339 : Blo 2285435 19532339 := bstep (se 1 (by rfl) ⟨14649254, by rfl⟩ : syracuseStep 19532339 = 29298509) B29298509
theorem B13021559 : Blo 2285435 13021559 := bstep (se 1 (by rfl) ⟨9766169, by rfl⟩ : syracuseStep 13021559 = 19532339) B19532339
theorem B8681039 : Blo 2285435 8681039 := bstep (se 1 (by rfl) ⟨6510779, by rfl⟩ : syracuseStep 8681039 = 13021559) B13021559
theorem B5787359 : Blo 2285435 5787359 := bstep (se 1 (by rfl) ⟨4340519, by rfl⟩ : syracuseStep 5787359 = 8681039) B8681039
theorem B3858239 : Blo 2285435 3858239 := bstep (se 1 (by rfl) ⟨2893679, by rfl⟩ : syracuseStep 3858239 = 5787359) B5787359
theorem B2572159 : Blo 2285435 2572159 := bstep (se 1 (by rfl) ⟨1929119, by rfl⟩ : syracuseStep 2572159 = 3858239) B3858239
theorem B3429545 : Blo 2285435 3429545 := bstep (se 2 (by rfl) ⟨1286079, by rfl⟩ : syracuseStep 3429545 = 2572159) B2572159
theorem B2286363 : Blo 2285435 2286363 := bstep (se 1 (by rfl) ⟨1714772, by rfl⟩ : syracuseStep 2286363 = 3429545) B3429545
theorem B4883093 : Blo 2285435 4883093 := bbase (se 6 (by rfl) ⟨114447, by rfl⟩ : syracuseStep 4883093 = 228895) (by norm_num)
theorem B3255395 : Blo 2285435 3255395 := bstep (se 1 (by rfl) ⟨2441546, by rfl⟩ : syracuseStep 3255395 = 4883093) B4883093
theorem B8681053 : Blo 2285435 8681053 := bstep (se 3 (by rfl) ⟨1627697, by rfl⟩ : syracuseStep 8681053 = 3255395) B3255395
theorem B11574737 : Blo 2285435 11574737 := bstep (se 2 (by rfl) ⟨4340526, by rfl⟩ : syracuseStep 11574737 = 8681053) B8681053
theorem B7716491 : Blo 2285435 7716491 := bstep (se 1 (by rfl) ⟨5787368, by rfl⟩ : syracuseStep 7716491 = 11574737) B11574737
theorem B5144327 : Blo 2285435 5144327 := bstep (se 1 (by rfl) ⟨3858245, by rfl⟩ : syracuseStep 5144327 = 7716491) B7716491
theorem B3429551 : Blo 2285435 3429551 := bstep (se 1 (by rfl) ⟨2572163, by rfl⟩ : syracuseStep 3429551 = 5144327) B5144327
theorem B2286367 : Blo 2285435 2286367 := bstep (se 1 (by rfl) ⟨1714775, by rfl⟩ : syracuseStep 2286367 = 3429551) B3429551
theorem B3429557 : Blo 2285435 3429557 := bbase (se 5 (by rfl) ⟨160760, by rfl⟩ : syracuseStep 3429557 = 321521) (by norm_num)
theorem B2286371 : Blo 2285435 2286371 := bstep (se 1 (by rfl) ⟨1714778, by rfl⟩ : syracuseStep 2286371 = 3429557) B3429557
theorem B5787389 : Blo 2285435 5787389 := bbase (se 3 (by rfl) ⟨1085135, by rfl⟩ : syracuseStep 5787389 = 2170271) (by norm_num)
theorem B3858259 : Blo 2285435 3858259 := bstep (se 1 (by rfl) ⟨2893694, by rfl⟩ : syracuseStep 3858259 = 5787389) B5787389
theorem B5144345 : Blo 2285435 5144345 := bstep (se 2 (by rfl) ⟨1929129, by rfl⟩ : syracuseStep 5144345 = 3858259) B3858259
theorem B3429563 : Blo 2285435 3429563 := bstep (se 1 (by rfl) ⟨2572172, by rfl⟩ : syracuseStep 3429563 = 5144345) B5144345
theorem B2286375 : Blo 2285435 2286375 := bstep (se 1 (by rfl) ⟨1714781, by rfl⟩ : syracuseStep 2286375 = 3429563) B3429563
theorem B2572177 : Blo 2285435 2572177 := bbase (se 2 (by rfl) ⟨964566, by rfl⟩ : syracuseStep 2572177 = 1929133) (by norm_num)
theorem B3429569 : Blo 2285435 3429569 := bstep (se 2 (by rfl) ⟨1286088, by rfl⟩ : syracuseStep 3429569 = 2572177) B2572177
theorem B2286379 : Blo 2285435 2286379 := bstep (se 1 (by rfl) ⟨1714784, by rfl⟩ : syracuseStep 2286379 = 3429569) B3429569
theorem B4340557 : Blo 2285435 4340557 := bbase (se 3 (by rfl) ⟨813854, by rfl⟩ : syracuseStep 4340557 = 1627709) (by norm_num)
theorem B5787409 : Blo 2285435 5787409 := bstep (se 2 (by rfl) ⟨2170278, by rfl⟩ : syracuseStep 5787409 = 4340557) B4340557
theorem B7716545 : Blo 2285435 7716545 := bstep (se 2 (by rfl) ⟨2893704, by rfl⟩ : syracuseStep 7716545 = 5787409) B5787409
theorem B5144363 : Blo 2285435 5144363 := bstep (se 1 (by rfl) ⟨3858272, by rfl⟩ : syracuseStep 5144363 = 7716545) B7716545
theorem B3429575 : Blo 2285435 3429575 := bstep (se 1 (by rfl) ⟨2572181, by rfl⟩ : syracuseStep 3429575 = 5144363) B5144363
theorem B2286383 : Blo 2285435 2286383 := bstep (se 1 (by rfl) ⟨1714787, by rfl⟩ : syracuseStep 2286383 = 3429575) B3429575
theorem B3429581 : Blo 2285435 3429581 := bbase (se 3 (by rfl) ⟨643046, by rfl⟩ : syracuseStep 3429581 = 1286093) (by norm_num)
theorem B2286387 : Blo 2285435 2286387 := bstep (se 1 (by rfl) ⟨1714790, by rfl⟩ : syracuseStep 2286387 = 3429581) B3429581
theorem B5144381 : Blo 2285435 5144381 := bbase (se 3 (by rfl) ⟨964571, by rfl⟩ : syracuseStep 5144381 = 1929143) (by norm_num)
theorem B3429587 : Blo 2285435 3429587 := bstep (se 1 (by rfl) ⟨2572190, by rfl⟩ : syracuseStep 3429587 = 5144381) B5144381
theorem B2286391 : Blo 2285435 2286391 := bstep (se 1 (by rfl) ⟨1714793, by rfl⟩ : syracuseStep 2286391 = 3429587) B3429587
theorem B3858293 : Blo 2285435 3858293 := bbase (se 5 (by rfl) ⟨180857, by rfl⟩ : syracuseStep 3858293 = 361715) (by norm_num)
theorem B2572195 : Blo 2285435 2572195 := bstep (se 1 (by rfl) ⟨1929146, by rfl⟩ : syracuseStep 2572195 = 3858293) B3858293
theorem B3429593 : Blo 2285435 3429593 := bstep (se 2 (by rfl) ⟨1286097, by rfl⟩ : syracuseStep 3429593 = 2572195) B2572195
theorem B2286395 : Blo 2285435 2286395 := bstep (se 1 (by rfl) ⟨1714796, by rfl⟩ : syracuseStep 2286395 = 3429593) B3429593
theorem B5493557 : Blo 2285435 5493557 := bbase (se 5 (by rfl) ⟨257510, by rfl⟩ : syracuseStep 5493557 = 515021) (by norm_num)
theorem B3662371 : Blo 2285435 3662371 := bstep (se 1 (by rfl) ⟨2746778, by rfl⟩ : syracuseStep 3662371 = 5493557) B5493557
theorem B4883161 : Blo 2285435 4883161 := bstep (se 2 (by rfl) ⟨1831185, by rfl⟩ : syracuseStep 4883161 = 3662371) B3662371
theorem B6510881 : Blo 2285435 6510881 := bstep (se 2 (by rfl) ⟨2441580, by rfl⟩ : syracuseStep 6510881 = 4883161) B4883161
theorem B17362349 : Blo 2285435 17362349 := bstep (se 3 (by rfl) ⟨3255440, by rfl⟩ : syracuseStep 17362349 = 6510881) B6510881
theorem B11574899 : Blo 2285435 11574899 := bstep (se 1 (by rfl) ⟨8681174, by rfl⟩ : syracuseStep 11574899 = 17362349) B17362349
theorem B7716599 : Blo 2285435 7716599 := bstep (se 1 (by rfl) ⟨5787449, by rfl⟩ : syracuseStep 7716599 = 11574899) B11574899
theorem B5144399 : Blo 2285435 5144399 := bstep (se 1 (by rfl) ⟨3858299, by rfl⟩ : syracuseStep 5144399 = 7716599) B7716599
theorem B3429599 : Blo 2285435 3429599 := bstep (se 1 (by rfl) ⟨2572199, by rfl⟩ : syracuseStep 3429599 = 5144399) B5144399
theorem B2286399 : Blo 2285435 2286399 := bstep (se 1 (by rfl) ⟨1714799, by rfl⟩ : syracuseStep 2286399 = 3429599) B3429599
theorem B3429605 : Blo 2285435 3429605 := bbase (se 4 (by rfl) ⟨321525, by rfl⟩ : syracuseStep 3429605 = 643051) (by norm_num)
theorem B2286403 : Blo 2285435 2286403 := bstep (se 1 (by rfl) ⟨1714802, by rfl⟩ : syracuseStep 2286403 = 3429605) B3429605
theorem B3476405 : Blo 2285435 3476405 := bbase (se 5 (by rfl) ⟨162956, by rfl⟩ : syracuseStep 3476405 = 325913) (by norm_num)
theorem B9270413 : Blo 2285435 9270413 := bstep (se 3 (by rfl) ⟨1738202, by rfl⟩ : syracuseStep 9270413 = 3476405) B3476405
theorem B6180275 : Blo 2285435 6180275 := bstep (se 1 (by rfl) ⟨4635206, by rfl⟩ : syracuseStep 6180275 = 9270413) B9270413
theorem B4120183 : Blo 2285435 4120183 := bstep (se 1 (by rfl) ⟨3090137, by rfl⟩ : syracuseStep 4120183 = 6180275) B6180275
theorem B5493577 : Blo 2285435 5493577 := bstep (se 2 (by rfl) ⟨2060091, by rfl⟩ : syracuseStep 5493577 = 4120183) B4120183
theorem B7324769 : Blo 2285435 7324769 := bstep (se 2 (by rfl) ⟨2746788, by rfl⟩ : syracuseStep 7324769 = 5493577) B5493577
theorem B4883179 : Blo 2285435 4883179 := bstep (se 1 (by rfl) ⟨3662384, by rfl⟩ : syracuseStep 4883179 = 7324769) B7324769
theorem B6510905 : Blo 2285435 6510905 := bstep (se 2 (by rfl) ⟨2441589, by rfl⟩ : syracuseStep 6510905 = 4883179) B4883179
theorem B4340603 : Blo 2285435 4340603 := bstep (se 1 (by rfl) ⟨3255452, by rfl⟩ : syracuseStep 4340603 = 6510905) B6510905
theorem B2893735 : Blo 2285435 2893735 := bstep (se 1 (by rfl) ⟨2170301, by rfl⟩ : syracuseStep 2893735 = 4340603) B4340603
theorem B3858313 : Blo 2285435 3858313 := bstep (se 2 (by rfl) ⟨1446867, by rfl⟩ : syracuseStep 3858313 = 2893735) B2893735
theorem B5144417 : Blo 2285435 5144417 := bstep (se 2 (by rfl) ⟨1929156, by rfl⟩ : syracuseStep 5144417 = 3858313) B3858313
theorem B3429611 : Blo 2285435 3429611 := bstep (se 1 (by rfl) ⟨2572208, by rfl⟩ : syracuseStep 3429611 = 5144417) B5144417
theorem B2286407 : Blo 2285435 2286407 := bstep (se 1 (by rfl) ⟨1714805, by rfl⟩ : syracuseStep 2286407 = 3429611) B3429611
theorem B2572213 : Blo 2285435 2572213 := bbase (se 5 (by rfl) ⟨120572, by rfl⟩ : syracuseStep 2572213 = 241145) (by norm_num)
theorem B3429617 : Blo 2285435 3429617 := bstep (se 2 (by rfl) ⟨1286106, by rfl⟩ : syracuseStep 3429617 = 2572213) B2572213
theorem B2286411 : Blo 2285435 2286411 := bstep (se 1 (by rfl) ⟨1714808, by rfl⟩ : syracuseStep 2286411 = 3429617) B3429617
theorem B2893745 : Blo 2285435 2893745 := bbase (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) (by norm_num)
theorem B7716653 : Blo 2285435 7716653 := bstep (se 3 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 7716653 = 2893745) B2893745
theorem B5144435 : Blo 2285435 5144435 := bstep (se 1 (by rfl) ⟨3858326, by rfl⟩ : syracuseStep 5144435 = 7716653) B7716653
theorem B3429623 : Blo 2285435 3429623 := bstep (se 1 (by rfl) ⟨2572217, by rfl⟩ : syracuseStep 3429623 = 5144435) B5144435
theorem B2286415 : Blo 2285435 2286415 := bstep (se 1 (by rfl) ⟨1714811, by rfl⟩ : syracuseStep 2286415 = 3429623) B3429623
theorem B3429629 : Blo 2285435 3429629 := bbase (se 3 (by rfl) ⟨643055, by rfl⟩ : syracuseStep 3429629 = 1286111) (by norm_num)
theorem B2286419 : Blo 2285435 2286419 := bstep (se 1 (by rfl) ⟨1714814, by rfl⟩ : syracuseStep 2286419 = 3429629) B3429629
theorem B5144453 : Blo 2285435 5144453 := bbase (se 4 (by rfl) ⟨482292, by rfl⟩ : syracuseStep 5144453 = 964585) (by norm_num)
theorem B3429635 : Blo 2285435 3429635 := bstep (se 1 (by rfl) ⟨2572226, by rfl⟩ : syracuseStep 3429635 = 5144453) B5144453
theorem B2286423 : Blo 2285435 2286423 := bstep (se 1 (by rfl) ⟨1714817, by rfl⟩ : syracuseStep 2286423 = 3429635) B3429635
theorem B2746813 : Blo 2285435 2746813 := bbase (se 3 (by rfl) ⟨515027, by rfl⟩ : syracuseStep 2746813 = 1030055) (by norm_num)
theorem B3662417 : Blo 2285435 3662417 := bstep (se 2 (by rfl) ⟨1373406, by rfl⟩ : syracuseStep 3662417 = 2746813) B2746813
theorem B2441611 : Blo 2285435 2441611 := bstep (se 1 (by rfl) ⟨1831208, by rfl⟩ : syracuseStep 2441611 = 3662417) B3662417
theorem B3255481 : Blo 2285435 3255481 := bstep (se 2 (by rfl) ⟨1220805, by rfl⟩ : syracuseStep 3255481 = 2441611) B2441611
theorem B4340641 : Blo 2285435 4340641 := bstep (se 2 (by rfl) ⟨1627740, by rfl⟩ : syracuseStep 4340641 = 3255481) B3255481
theorem B5787521 : Blo 2285435 5787521 := bstep (se 2 (by rfl) ⟨2170320, by rfl⟩ : syracuseStep 5787521 = 4340641) B4340641
theorem B3858347 : Blo 2285435 3858347 := bstep (se 1 (by rfl) ⟨2893760, by rfl⟩ : syracuseStep 3858347 = 5787521) B5787521
theorem B2572231 : Blo 2285435 2572231 := bstep (se 1 (by rfl) ⟨1929173, by rfl⟩ : syracuseStep 2572231 = 3858347) B3858347
theorem B3429641 : Blo 2285435 3429641 := bstep (se 2 (by rfl) ⟨1286115, by rfl⟩ : syracuseStep 3429641 = 2572231) B2572231
theorem B2286427 : Blo 2285435 2286427 := bstep (se 1 (by rfl) ⟨1714820, by rfl⟩ : syracuseStep 2286427 = 3429641) B3429641
theorem B11575061 : Blo 2285435 11575061 := bbase (se 6 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 11575061 = 542581) (by norm_num)
theorem B7716707 : Blo 2285435 7716707 := bstep (se 1 (by rfl) ⟨5787530, by rfl⟩ : syracuseStep 7716707 = 11575061) B11575061
theorem B5144471 : Blo 2285435 5144471 := bstep (se 1 (by rfl) ⟨3858353, by rfl⟩ : syracuseStep 5144471 = 7716707) B7716707
theorem B3429647 : Blo 2285435 3429647 := bstep (se 1 (by rfl) ⟨2572235, by rfl⟩ : syracuseStep 3429647 = 5144471) B5144471
theorem B2286431 : Blo 2285435 2286431 := bstep (se 1 (by rfl) ⟨1714823, by rfl⟩ : syracuseStep 2286431 = 3429647) B3429647
theorem B3429653 : Blo 2285435 3429653 := bbase (se 6 (by rfl) ⟨80382, by rfl⟩ : syracuseStep 3429653 = 160765) (by norm_num)
theorem B2286435 : Blo 2285435 2286435 := bstep (se 1 (by rfl) ⟨1714826, by rfl⟩ : syracuseStep 2286435 = 3429653) B3429653
theorem B2933257 : Blo 2285435 2933257 := bbase (se 2 (by rfl) ⟨1099971, by rfl⟩ : syracuseStep 2933257 = 2199943) (by norm_num)
theorem B3911009 : Blo 2285435 3911009 := bstep (se 2 (by rfl) ⟨1466628, by rfl⟩ : syracuseStep 3911009 = 2933257) B2933257
theorem B41717429 : Blo 2285435 41717429 := bstep (se 5 (by rfl) ⟨1955504, by rfl⟩ : syracuseStep 41717429 = 3911009) B3911009
theorem B27811619 : Blo 2285435 27811619 := bstep (se 1 (by rfl) ⟨20858714, by rfl⟩ : syracuseStep 27811619 = 41717429) B41717429
theorem B18541079 : Blo 2285435 18541079 := bstep (se 1 (by rfl) ⟨13905809, by rfl⟩ : syracuseStep 18541079 = 27811619) B27811619
theorem B12360719 : Blo 2285435 12360719 := bstep (se 1 (by rfl) ⟨9270539, by rfl⟩ : syracuseStep 12360719 = 18541079) B18541079
theorem B32961917 : Blo 2285435 32961917 := bstep (se 3 (by rfl) ⟨6180359, by rfl⟩ : syracuseStep 32961917 = 12360719) B12360719
theorem B21974611 : Blo 2285435 21974611 := bstep (se 1 (by rfl) ⟨16480958, by rfl⟩ : syracuseStep 21974611 = 32961917) B32961917
theorem B29299481 : Blo 2285435 29299481 := bstep (se 2 (by rfl) ⟨10987305, by rfl⟩ : syracuseStep 29299481 = 21974611) B21974611
theorem B19532987 : Blo 2285435 19532987 := bstep (se 1 (by rfl) ⟨14649740, by rfl⟩ : syracuseStep 19532987 = 29299481) B29299481
theorem B13021991 : Blo 2285435 13021991 := bstep (se 1 (by rfl) ⟨9766493, by rfl⟩ : syracuseStep 13021991 = 19532987) B19532987
theorem B8681327 : Blo 2285435 8681327 := bstep (se 1 (by rfl) ⟨6510995, by rfl⟩ : syracuseStep 8681327 = 13021991) B13021991
theorem B5787551 : Blo 2285435 5787551 := bstep (se 1 (by rfl) ⟨4340663, by rfl⟩ : syracuseStep 5787551 = 8681327) B8681327
theorem B3858367 : Blo 2285435 3858367 := bstep (se 1 (by rfl) ⟨2893775, by rfl⟩ : syracuseStep 3858367 = 5787551) B5787551
theorem B5144489 : Blo 2285435 5144489 := bstep (se 2 (by rfl) ⟨1929183, by rfl⟩ : syracuseStep 5144489 = 3858367) B3858367
theorem B3429659 : Blo 2285435 3429659 := bstep (se 1 (by rfl) ⟨2572244, by rfl⟩ : syracuseStep 3429659 = 5144489) B5144489
theorem B2286439 : Blo 2285435 2286439 := bstep (se 1 (by rfl) ⟨1714829, by rfl⟩ : syracuseStep 2286439 = 3429659) B3429659
theorem B2572249 : Blo 2285435 2572249 := bbase (se 2 (by rfl) ⟨964593, by rfl⟩ : syracuseStep 2572249 = 1929187) (by norm_num)
theorem B3429665 : Blo 2285435 3429665 := bstep (se 2 (by rfl) ⟨1286124, by rfl⟩ : syracuseStep 3429665 = 2572249) B2572249
theorem B2286443 : Blo 2285435 2286443 := bstep (se 1 (by rfl) ⟨1714832, by rfl⟩ : syracuseStep 2286443 = 3429665) B3429665
theorem B3255509 : Blo 2285435 3255509 := bbase (se 7 (by rfl) ⟨38150, by rfl⟩ : syracuseStep 3255509 = 76301) (by norm_num)
theorem B8681357 : Blo 2285435 8681357 := bstep (se 3 (by rfl) ⟨1627754, by rfl⟩ : syracuseStep 8681357 = 3255509) B3255509
theorem B5787571 : Blo 2285435 5787571 := bstep (se 1 (by rfl) ⟨4340678, by rfl⟩ : syracuseStep 5787571 = 8681357) B8681357
theorem B7716761 : Blo 2285435 7716761 := bstep (se 2 (by rfl) ⟨2893785, by rfl⟩ : syracuseStep 7716761 = 5787571) B5787571
theorem B5144507 : Blo 2285435 5144507 := bstep (se 1 (by rfl) ⟨3858380, by rfl⟩ : syracuseStep 5144507 = 7716761) B7716761
theorem B3429671 : Blo 2285435 3429671 := bstep (se 1 (by rfl) ⟨2572253, by rfl⟩ : syracuseStep 3429671 = 5144507) B5144507
theorem B2286447 : Blo 2285435 2286447 := bstep (se 1 (by rfl) ⟨1714835, by rfl⟩ : syracuseStep 2286447 = 3429671) B3429671
theorem B3429677 : Blo 2285435 3429677 := bbase (se 3 (by rfl) ⟨643064, by rfl⟩ : syracuseStep 3429677 = 1286129) (by norm_num)
theorem B2286451 : Blo 2285435 2286451 := bstep (se 1 (by rfl) ⟨1714838, by rfl⟩ : syracuseStep 2286451 = 3429677) B3429677
theorem B5144525 : Blo 2285435 5144525 := bbase (se 3 (by rfl) ⟨964598, by rfl⟩ : syracuseStep 5144525 = 1929197) (by norm_num)
theorem B3429683 : Blo 2285435 3429683 := bstep (se 1 (by rfl) ⟨2572262, by rfl⟩ : syracuseStep 3429683 = 5144525) B5144525
theorem B2286455 : Blo 2285435 2286455 := bstep (se 1 (by rfl) ⟨1714841, by rfl⟩ : syracuseStep 2286455 = 3429683) B3429683
theorem B2893801 : Blo 2285435 2893801 := bbase (se 2 (by rfl) ⟨1085175, by rfl⟩ : syracuseStep 2893801 = 2170351) (by norm_num)
theorem B3858401 : Blo 2285435 3858401 := bstep (se 2 (by rfl) ⟨1446900, by rfl⟩ : syracuseStep 3858401 = 2893801) B2893801
theorem B2572267 : Blo 2285435 2572267 := bstep (se 1 (by rfl) ⟨1929200, by rfl⟩ : syracuseStep 2572267 = 3858401) B3858401
theorem B3429689 : Blo 2285435 3429689 := bstep (se 2 (by rfl) ⟨1286133, by rfl⟩ : syracuseStep 3429689 = 2572267) B2572267
theorem B2286459 : Blo 2285435 2286459 := bstep (se 1 (by rfl) ⟨1714844, by rfl⟩ : syracuseStep 2286459 = 3429689) B3429689
theorem B4399933 : Blo 2285435 4399933 := bbase (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) (by norm_num)
theorem B5866577 : Blo 2285435 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B3911051 : Blo 2285435 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B10429469 : Blo 2285435 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B6952979 : Blo 2285435 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B4635319 : Blo 2285435 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B6180425 : Blo 2285435 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B4120283 : Blo 2285435 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B2746855 : Blo 2285435 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B14649893 : Blo 2285435 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B9766595 : Blo 2285435 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B26044253 : Blo 2285435 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B17362835 : Blo 2285435 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B11575223 : Blo 2285435 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B7716815 : Blo 2285435 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B5144543 : Blo 2285435 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B3429695 : Blo 2285435 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B2286463 : Blo 2285435 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B3429701 : Blo 2285435 3429701 := bbase (se 4 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 3429701 = 643069) (by norm_num)
theorem B2286467 : Blo 2285435 2286467 := bstep (se 1 (by rfl) ⟨1714850, by rfl⟩ : syracuseStep 2286467 = 3429701) B3429701
theorem B3858421 : Blo 2285435 3858421 := bbase (se 5 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 3858421 = 361727) (by norm_num)
theorem B5144561 : Blo 2285435 5144561 := bstep (se 2 (by rfl) ⟨1929210, by rfl⟩ : syracuseStep 5144561 = 3858421) B3858421
theorem B3429707 : Blo 2285435 3429707 := bstep (se 1 (by rfl) ⟨2572280, by rfl⟩ : syracuseStep 3429707 = 5144561) B5144561
theorem B2286471 : Blo 2285435 2286471 := bstep (se 1 (by rfl) ⟨1714853, by rfl⟩ : syracuseStep 2286471 = 3429707) B3429707
theorem B2572285 : Blo 2285435 2572285 := bbase (se 3 (by rfl) ⟨482303, by rfl⟩ : syracuseStep 2572285 = 964607) (by norm_num)
theorem B3429713 : Blo 2285435 3429713 := bstep (se 2 (by rfl) ⟨1286142, by rfl⟩ : syracuseStep 3429713 = 2572285) B2572285
theorem B2286475 : Blo 2285435 2286475 := bstep (se 1 (by rfl) ⟨1714856, by rfl⟩ : syracuseStep 2286475 = 3429713) B3429713
theorem B7716869 : Blo 2285435 7716869 := bbase (se 4 (by rfl) ⟨723456, by rfl⟩ : syracuseStep 7716869 = 1446913) (by norm_num)
theorem B5144579 : Blo 2285435 5144579 := bstep (se 1 (by rfl) ⟨3858434, by rfl⟩ : syracuseStep 5144579 = 7716869) B7716869
theorem B3429719 : Blo 2285435 3429719 := bstep (se 1 (by rfl) ⟨2572289, by rfl⟩ : syracuseStep 3429719 = 5144579) B5144579
theorem B2286479 : Blo 2285435 2286479 := bstep (se 1 (by rfl) ⟨1714859, by rfl⟩ : syracuseStep 2286479 = 3429719) B3429719
theorem B3429725 : Blo 2285435 3429725 := bbase (se 3 (by rfl) ⟨643073, by rfl⟩ : syracuseStep 3429725 = 1286147) (by norm_num)
theorem B2286483 : Blo 2285435 2286483 := bstep (se 1 (by rfl) ⟨1714862, by rfl⟩ : syracuseStep 2286483 = 3429725) B3429725
theorem B5144597 : Blo 2285435 5144597 := bbase (se 6 (by rfl) ⟨120576, by rfl⟩ : syracuseStep 5144597 = 241153) (by norm_num)
theorem B3429731 : Blo 2285435 3429731 := bstep (se 1 (by rfl) ⟨2572298, by rfl⟩ : syracuseStep 3429731 = 5144597) B5144597
theorem B2286487 : Blo 2285435 2286487 := bstep (se 1 (by rfl) ⟨1714865, by rfl⟩ : syracuseStep 2286487 = 3429731) B3429731
theorem B8681525 : Blo 2285435 8681525 := bbase (se 5 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 8681525 = 813893) (by norm_num)
theorem B5787683 : Blo 2285435 5787683 := bstep (se 1 (by rfl) ⟨4340762, by rfl⟩ : syracuseStep 5787683 = 8681525) B8681525
theorem B3858455 : Blo 2285435 3858455 := bstep (se 1 (by rfl) ⟨2893841, by rfl⟩ : syracuseStep 3858455 = 5787683) B5787683
theorem B2572303 : Blo 2285435 2572303 := bstep (se 1 (by rfl) ⟨1929227, by rfl⟩ : syracuseStep 2572303 = 3858455) B3858455
theorem B3429737 : Blo 2285435 3429737 := bstep (se 2 (by rfl) ⟨1286151, by rfl⟩ : syracuseStep 3429737 = 2572303) B2572303
theorem B2286491 : Blo 2285435 2286491 := bstep (se 1 (by rfl) ⟨1714868, by rfl⟩ : syracuseStep 2286491 = 3429737) B3429737
theorem B3662525 : Blo 2285435 3662525 := bbase (se 3 (by rfl) ⟨686723, by rfl⟩ : syracuseStep 3662525 = 1373447) (by norm_num)
theorem B2441683 : Blo 2285435 2441683 := bstep (se 1 (by rfl) ⟨1831262, by rfl⟩ : syracuseStep 2441683 = 3662525) B3662525
theorem B13022309 : Blo 2285435 13022309 := bstep (se 4 (by rfl) ⟨1220841, by rfl⟩ : syracuseStep 13022309 = 2441683) B2441683
theorem B8681539 : Blo 2285435 8681539 := bstep (se 1 (by rfl) ⟨6511154, by rfl⟩ : syracuseStep 8681539 = 13022309) B13022309
theorem B11575385 : Blo 2285435 11575385 := bstep (se 2 (by rfl) ⟨4340769, by rfl⟩ : syracuseStep 11575385 = 8681539) B8681539
theorem B7716923 : Blo 2285435 7716923 := bstep (se 1 (by rfl) ⟨5787692, by rfl⟩ : syracuseStep 7716923 = 11575385) B11575385
theorem B5144615 : Blo 2285435 5144615 := bstep (se 1 (by rfl) ⟨3858461, by rfl⟩ : syracuseStep 5144615 = 7716923) B7716923
theorem B3429743 : Blo 2285435 3429743 := bstep (se 1 (by rfl) ⟨2572307, by rfl⟩ : syracuseStep 3429743 = 5144615) B5144615
theorem B2286495 : Blo 2285435 2286495 := bstep (se 1 (by rfl) ⟨1714871, by rfl⟩ : syracuseStep 2286495 = 3429743) B3429743
theorem B3429749 : Blo 2285435 3429749 := bbase (se 5 (by rfl) ⟨160769, by rfl⟩ : syracuseStep 3429749 = 321539) (by norm_num)
theorem B2286499 : Blo 2285435 2286499 := bstep (se 1 (by rfl) ⟨1714874, by rfl⟩ : syracuseStep 2286499 = 3429749) B3429749
theorem B3255589 : Blo 2285435 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B4340785 : Blo 2285435 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B5787713 : Blo 2285435 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B3858475 : Blo 2285435 3858475 := bstep (se 1 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 3858475 = 5787713) B5787713
theorem B5144633 : Blo 2285435 5144633 := bstep (se 2 (by rfl) ⟨1929237, by rfl⟩ : syracuseStep 5144633 = 3858475) B3858475
theorem B3429755 : Blo 2285435 3429755 := bstep (se 1 (by rfl) ⟨2572316, by rfl⟩ : syracuseStep 3429755 = 5144633) B5144633
theorem B2286503 : Blo 2285435 2286503 := bstep (se 1 (by rfl) ⟨1714877, by rfl⟩ : syracuseStep 2286503 = 3429755) B3429755
theorem B2572321 : Blo 2285435 2572321 := bbase (se 2 (by rfl) ⟨964620, by rfl⟩ : syracuseStep 2572321 = 1929241) (by norm_num)
theorem B3429761 : Blo 2285435 3429761 := bstep (se 2 (by rfl) ⟨1286160, by rfl⟩ : syracuseStep 3429761 = 2572321) B2572321
theorem B2286507 : Blo 2285435 2286507 := bstep (se 1 (by rfl) ⟨1714880, by rfl⟩ : syracuseStep 2286507 = 3429761) B3429761
theorem B5787733 : Blo 2285435 5787733 := bbase (se 8 (by rfl) ⟨33912, by rfl⟩ : syracuseStep 5787733 = 67825) (by norm_num)
theorem B7716977 : Blo 2285435 7716977 := bstep (se 2 (by rfl) ⟨2893866, by rfl⟩ : syracuseStep 7716977 = 5787733) B5787733
theorem B5144651 : Blo 2285435 5144651 := bstep (se 1 (by rfl) ⟨3858488, by rfl⟩ : syracuseStep 5144651 = 7716977) B7716977
theorem B3429767 : Blo 2285435 3429767 := bstep (se 1 (by rfl) ⟨2572325, by rfl⟩ : syracuseStep 3429767 = 5144651) B5144651
theorem B2286511 : Blo 2285435 2286511 := bstep (se 1 (by rfl) ⟨1714883, by rfl⟩ : syracuseStep 2286511 = 3429767) B3429767
theorem B3429773 : Blo 2285435 3429773 := bbase (se 3 (by rfl) ⟨643082, by rfl⟩ : syracuseStep 3429773 = 1286165) (by norm_num)
theorem B2286515 : Blo 2285435 2286515 := bstep (se 1 (by rfl) ⟨1714886, by rfl⟩ : syracuseStep 2286515 = 3429773) B3429773
theorem B5144669 : Blo 2285435 5144669 := bbase (se 3 (by rfl) ⟨964625, by rfl⟩ : syracuseStep 5144669 = 1929251) (by norm_num)
theorem B3429779 : Blo 2285435 3429779 := bstep (se 1 (by rfl) ⟨2572334, by rfl⟩ : syracuseStep 3429779 = 5144669) B5144669
theorem B2286519 : Blo 2285435 2286519 := bstep (se 1 (by rfl) ⟨1714889, by rfl⟩ : syracuseStep 2286519 = 3429779) B3429779
theorem B3858509 : Blo 2285435 3858509 := bbase (se 3 (by rfl) ⟨723470, by rfl⟩ : syracuseStep 3858509 = 1446941) (by norm_num)
theorem B2572339 : Blo 2285435 2572339 := bstep (se 1 (by rfl) ⟨1929254, by rfl⟩ : syracuseStep 2572339 = 3858509) B3858509
theorem B3429785 : Blo 2285435 3429785 := bstep (se 2 (by rfl) ⟨1286169, by rfl⟩ : syracuseStep 3429785 = 2572339) B2572339
theorem B2286523 : Blo 2285435 2286523 := bstep (se 1 (by rfl) ⟨1714892, by rfl⟩ : syracuseStep 2286523 = 3429785) B3429785
theorem B37589525 : Blo 2285435 37589525 := bbase (se 6 (by rfl) ⟨881004, by rfl⟩ : syracuseStep 37589525 = 1762009) (by norm_num)
theorem B25059683 : Blo 2285435 25059683 := bstep (se 1 (by rfl) ⟨18794762, by rfl⟩ : syracuseStep 25059683 = 37589525) B37589525
theorem B16706455 : Blo 2285435 16706455 := bstep (se 1 (by rfl) ⟨12529841, by rfl⟩ : syracuseStep 16706455 = 25059683) B25059683
theorem B356404373 : Blo 2285435 356404373 := bstep (se 6 (by rfl) ⟨8353227, by rfl⟩ : syracuseStep 356404373 = 16706455) B16706455
theorem B237602915 : Blo 2285435 237602915 := bstep (se 1 (by rfl) ⟨178202186, by rfl⟩ : syracuseStep 237602915 = 356404373) B356404373
theorem B158401943 : Blo 2285435 158401943 := bstep (se 1 (by rfl) ⟨118801457, by rfl⟩ : syracuseStep 158401943 = 237602915) B237602915
theorem B105601295 : Blo 2285435 105601295 := bstep (se 1 (by rfl) ⟨79200971, by rfl⟩ : syracuseStep 105601295 = 158401943) B158401943
theorem B70400863 : Blo 2285435 70400863 := bstep (se 1 (by rfl) ⟨52800647, by rfl⟩ : syracuseStep 70400863 = 105601295) B105601295
theorem B93867817 : Blo 2285435 93867817 := bstep (se 2 (by rfl) ⟨35200431, by rfl⟩ : syracuseStep 93867817 = 70400863) B70400863
theorem B125157089 : Blo 2285435 125157089 := bstep (se 2 (by rfl) ⟨46933908, by rfl⟩ : syracuseStep 125157089 = 93867817) B93867817
theorem B83438059 : Blo 2285435 83438059 := bstep (se 1 (by rfl) ⟨62578544, by rfl⟩ : syracuseStep 83438059 = 125157089) B125157089
theorem B111250745 : Blo 2285435 111250745 := bstep (se 2 (by rfl) ⟨41719029, by rfl⟩ : syracuseStep 111250745 = 83438059) B83438059
theorem B74167163 : Blo 2285435 74167163 := bstep (se 1 (by rfl) ⟨55625372, by rfl⟩ : syracuseStep 74167163 = 111250745) B111250745
theorem B49444775 : Blo 2285435 49444775 := bstep (se 1 (by rfl) ⟨37083581, by rfl⟩ : syracuseStep 49444775 = 74167163) B74167163
theorem B32963183 : Blo 2285435 32963183 := bstep (se 1 (by rfl) ⟨24722387, by rfl⟩ : syracuseStep 32963183 = 49444775) B49444775
theorem B21975455 : Blo 2285435 21975455 := bstep (se 1 (by rfl) ⟨16481591, by rfl⟩ : syracuseStep 21975455 = 32963183) B32963183
theorem B14650303 : Blo 2285435 14650303 := bstep (se 1 (by rfl) ⟨10987727, by rfl⟩ : syracuseStep 14650303 = 21975455) B21975455
theorem B19533737 : Blo 2285435 19533737 := bstep (se 2 (by rfl) ⟨7325151, by rfl⟩ : syracuseStep 19533737 = 14650303) B14650303
theorem B13022491 : Blo 2285435 13022491 := bstep (se 1 (by rfl) ⟨9766868, by rfl⟩ : syracuseStep 13022491 = 19533737) B19533737
theorem B17363321 : Blo 2285435 17363321 := bstep (se 2 (by rfl) ⟨6511245, by rfl⟩ : syracuseStep 17363321 = 13022491) B13022491
theorem B11575547 : Blo 2285435 11575547 := bstep (se 1 (by rfl) ⟨8681660, by rfl⟩ : syracuseStep 11575547 = 17363321) B17363321
theorem B7717031 : Blo 2285435 7717031 := bstep (se 1 (by rfl) ⟨5787773, by rfl⟩ : syracuseStep 7717031 = 11575547) B11575547
theorem B5144687 : Blo 2285435 5144687 := bstep (se 1 (by rfl) ⟨3858515, by rfl⟩ : syracuseStep 5144687 = 7717031) B7717031
theorem B3429791 : Blo 2285435 3429791 := bstep (se 1 (by rfl) ⟨2572343, by rfl⟩ : syracuseStep 3429791 = 5144687) B5144687
theorem B2286527 : Blo 2285435 2286527 := bstep (se 1 (by rfl) ⟨1714895, by rfl⟩ : syracuseStep 2286527 = 3429791) B3429791
theorem B3429797 : Blo 2285435 3429797 := bbase (se 4 (by rfl) ⟨321543, by rfl⟩ : syracuseStep 3429797 = 643087) (by norm_num)
theorem B2286531 : Blo 2285435 2286531 := bstep (se 1 (by rfl) ⟨1714898, by rfl⟩ : syracuseStep 2286531 = 3429797) B3429797
theorem B2893897 : Blo 2285435 2893897 := bbase (se 2 (by rfl) ⟨1085211, by rfl⟩ : syracuseStep 2893897 = 2170423) (by norm_num)
theorem B3858529 : Blo 2285435 3858529 := bstep (se 2 (by rfl) ⟨1446948, by rfl⟩ : syracuseStep 3858529 = 2893897) B2893897
theorem B5144705 : Blo 2285435 5144705 := bstep (se 2 (by rfl) ⟨1929264, by rfl⟩ : syracuseStep 5144705 = 3858529) B3858529
theorem B3429803 : Blo 2285435 3429803 := bstep (se 1 (by rfl) ⟨2572352, by rfl⟩ : syracuseStep 3429803 = 5144705) B5144705
theorem B2286535 : Blo 2285435 2286535 := bstep (se 1 (by rfl) ⟨1714901, by rfl⟩ : syracuseStep 2286535 = 3429803) B3429803
theorem B2572357 : Blo 2285435 2572357 := bbase (se 4 (by rfl) ⟨241158, by rfl⟩ : syracuseStep 2572357 = 482317) (by norm_num)
theorem B3429809 : Blo 2285435 3429809 := bstep (se 2 (by rfl) ⟨1286178, by rfl⟩ : syracuseStep 3429809 = 2572357) B2572357
theorem B2286539 : Blo 2285435 2286539 := bstep (se 1 (by rfl) ⟨1714904, by rfl⟩ : syracuseStep 2286539 = 3429809) B3429809
theorem B4340861 : Blo 2285435 4340861 := bbase (se 3 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 4340861 = 1627823) (by norm_num)
theorem B2893907 : Blo 2285435 2893907 := bstep (se 1 (by rfl) ⟨2170430, by rfl⟩ : syracuseStep 2893907 = 4340861) B4340861
theorem B7717085 : Blo 2285435 7717085 := bstep (se 3 (by rfl) ⟨1446953, by rfl⟩ : syracuseStep 7717085 = 2893907) B2893907
theorem B5144723 : Blo 2285435 5144723 := bstep (se 1 (by rfl) ⟨3858542, by rfl⟩ : syracuseStep 5144723 = 7717085) B7717085
theorem B3429815 : Blo 2285435 3429815 := bstep (se 1 (by rfl) ⟨2572361, by rfl⟩ : syracuseStep 3429815 = 5144723) B5144723
theorem B2286543 : Blo 2285435 2286543 := bstep (se 1 (by rfl) ⟨1714907, by rfl⟩ : syracuseStep 2286543 = 3429815) B3429815
theorem B3429821 : Blo 2285435 3429821 := bbase (se 3 (by rfl) ⟨643091, by rfl⟩ : syracuseStep 3429821 = 1286183) (by norm_num)
theorem B2286547 : Blo 2285435 2286547 := bstep (se 1 (by rfl) ⟨1714910, by rfl⟩ : syracuseStep 2286547 = 3429821) B3429821
theorem B5144741 : Blo 2285435 5144741 := bbase (se 4 (by rfl) ⟨482319, by rfl⟩ : syracuseStep 5144741 = 964639) (by norm_num)
theorem B3429827 : Blo 2285435 3429827 := bstep (se 1 (by rfl) ⟨2572370, by rfl⟩ : syracuseStep 3429827 = 5144741) B5144741
theorem B2286551 : Blo 2285435 2286551 := bstep (se 1 (by rfl) ⟨1714913, by rfl⟩ : syracuseStep 2286551 = 3429827) B3429827
theorem B5787845 : Blo 2285435 5787845 := bbase (se 4 (by rfl) ⟨542610, by rfl⟩ : syracuseStep 5787845 = 1085221) (by norm_num)
theorem B3858563 : Blo 2285435 3858563 := bstep (se 1 (by rfl) ⟨2893922, by rfl⟩ : syracuseStep 3858563 = 5787845) B5787845
theorem B2572375 : Blo 2285435 2572375 := bstep (se 1 (by rfl) ⟨1929281, by rfl⟩ : syracuseStep 2572375 = 3858563) B3858563
theorem B3429833 : Blo 2285435 3429833 := bstep (se 2 (by rfl) ⟨1286187, by rfl⟩ : syracuseStep 3429833 = 2572375) B2572375
theorem B2286555 : Blo 2285435 2286555 := bstep (se 1 (by rfl) ⟨1714916, by rfl⟩ : syracuseStep 2286555 = 3429833) B3429833
theorem B7929157 : Blo 2285435 7929157 := bbase (se 4 (by rfl) ⟨743358, by rfl⟩ : syracuseStep 7929157 = 1486717) (by norm_num)
theorem B10572209 : Blo 2285435 10572209 := bstep (se 2 (by rfl) ⟨3964578, by rfl⟩ : syracuseStep 10572209 = 7929157) B7929157
theorem B7048139 : Blo 2285435 7048139 := bstep (se 1 (by rfl) ⟨5286104, by rfl⟩ : syracuseStep 7048139 = 10572209) B10572209
theorem B18795037 : Blo 2285435 18795037 := bstep (se 3 (by rfl) ⟨3524069, by rfl⟩ : syracuseStep 18795037 = 7048139) B7048139
theorem B25060049 : Blo 2285435 25060049 := bstep (se 2 (by rfl) ⟨9397518, by rfl⟩ : syracuseStep 25060049 = 18795037) B18795037
theorem B16706699 : Blo 2285435 16706699 := bstep (se 1 (by rfl) ⟨12530024, by rfl⟩ : syracuseStep 16706699 = 25060049) B25060049
theorem B11137799 : Blo 2285435 11137799 := bstep (se 1 (by rfl) ⟨8353349, by rfl⟩ : syracuseStep 11137799 = 16706699) B16706699
theorem B7425199 : Blo 2285435 7425199 := bstep (se 1 (by rfl) ⟨5568899, by rfl⟩ : syracuseStep 7425199 = 11137799) B11137799
theorem B9900265 : Blo 2285435 9900265 := bstep (se 2 (by rfl) ⟨3712599, by rfl⟩ : syracuseStep 9900265 = 7425199) B7425199
theorem B13200353 : Blo 2285435 13200353 := bstep (se 2 (by rfl) ⟨4950132, by rfl⟩ : syracuseStep 13200353 = 9900265) B9900265
theorem B8800235 : Blo 2285435 8800235 := bstep (se 1 (by rfl) ⟨6600176, by rfl⟩ : syracuseStep 8800235 = 13200353) B13200353
theorem B5866823 : Blo 2285435 5866823 := bstep (se 1 (by rfl) ⟨4400117, by rfl⟩ : syracuseStep 5866823 = 8800235) B8800235
theorem B3911215 : Blo 2285435 3911215 := bstep (se 1 (by rfl) ⟨2933411, by rfl⟩ : syracuseStep 3911215 = 5866823) B5866823
theorem B5214953 : Blo 2285435 5214953 := bstep (se 2 (by rfl) ⟨1955607, by rfl⟩ : syracuseStep 5214953 = 3911215) B3911215
theorem B13906541 : Blo 2285435 13906541 := bstep (se 3 (by rfl) ⟨2607476, by rfl⟩ : syracuseStep 13906541 = 5214953) B5214953
theorem B9271027 : Blo 2285435 9271027 := bstep (se 1 (by rfl) ⟨6953270, by rfl⟩ : syracuseStep 9271027 = 13906541) B13906541
theorem B12361369 : Blo 2285435 12361369 := bstep (se 2 (by rfl) ⟨4635513, by rfl⟩ : syracuseStep 12361369 = 9271027) B9271027
theorem B16481825 : Blo 2285435 16481825 := bstep (se 2 (by rfl) ⟨6180684, by rfl⟩ : syracuseStep 16481825 = 12361369) B12361369
theorem B10987883 : Blo 2285435 10987883 := bstep (se 1 (by rfl) ⟨8240912, by rfl⟩ : syracuseStep 10987883 = 16481825) B16481825
theorem B7325255 : Blo 2285435 7325255 := bstep (se 1 (by rfl) ⟨5493941, by rfl⟩ : syracuseStep 7325255 = 10987883) B10987883
theorem B4883503 : Blo 2285435 4883503 := bstep (se 1 (by rfl) ⟨3662627, by rfl⟩ : syracuseStep 4883503 = 7325255) B7325255
theorem B6511337 : Blo 2285435 6511337 := bstep (se 2 (by rfl) ⟨2441751, by rfl⟩ : syracuseStep 6511337 = 4883503) B4883503
theorem B4340891 : Blo 2285435 4340891 := bstep (se 1 (by rfl) ⟨3255668, by rfl⟩ : syracuseStep 4340891 = 6511337) B6511337
theorem B11575709 : Blo 2285435 11575709 := bstep (se 3 (by rfl) ⟨2170445, by rfl⟩ : syracuseStep 11575709 = 4340891) B4340891
theorem B7717139 : Blo 2285435 7717139 := bstep (se 1 (by rfl) ⟨5787854, by rfl⟩ : syracuseStep 7717139 = 11575709) B11575709
theorem B5144759 : Blo 2285435 5144759 := bstep (se 1 (by rfl) ⟨3858569, by rfl⟩ : syracuseStep 5144759 = 7717139) B7717139
theorem B3429839 : Blo 2285435 3429839 := bstep (se 1 (by rfl) ⟨2572379, by rfl⟩ : syracuseStep 3429839 = 5144759) B5144759
theorem B2286559 : Blo 2285435 2286559 := bstep (se 1 (by rfl) ⟨1714919, by rfl⟩ : syracuseStep 2286559 = 3429839) B3429839
theorem B3429845 : Blo 2285435 3429845 := bbase (se 7 (by rfl) ⟨40193, by rfl⟩ : syracuseStep 3429845 = 80387) (by norm_num)
theorem B2286563 : Blo 2285435 2286563 := bstep (se 1 (by rfl) ⟨1714922, by rfl⟩ : syracuseStep 2286563 = 3429845) B3429845
theorem B8681813 : Blo 2285435 8681813 := bbase (se 10 (by rfl) ⟨12717, by rfl⟩ : syracuseStep 8681813 = 25435) (by norm_num)
theorem B5787875 : Blo 2285435 5787875 := bstep (se 1 (by rfl) ⟨4340906, by rfl⟩ : syracuseStep 5787875 = 8681813) B8681813
theorem B3858583 : Blo 2285435 3858583 := bstep (se 1 (by rfl) ⟨2893937, by rfl⟩ : syracuseStep 3858583 = 5787875) B5787875
theorem B5144777 : Blo 2285435 5144777 := bstep (se 2 (by rfl) ⟨1929291, by rfl⟩ : syracuseStep 5144777 = 3858583) B3858583
theorem B3429851 : Blo 2285435 3429851 := bstep (se 1 (by rfl) ⟨2572388, by rfl⟩ : syracuseStep 3429851 = 5144777) B5144777
theorem B2286567 : Blo 2285435 2286567 := bstep (se 1 (by rfl) ⟨1714925, by rfl⟩ : syracuseStep 2286567 = 3429851) B3429851
theorem B2572393 : Blo 2285435 2572393 := bbase (se 2 (by rfl) ⟨964647, by rfl⟩ : syracuseStep 2572393 = 1929295) (by norm_num)
theorem B3429857 : Blo 2285435 3429857 := bstep (se 2 (by rfl) ⟨1286196, by rfl⟩ : syracuseStep 3429857 = 2572393) B2572393
theorem B2286571 : Blo 2285435 2286571 := bstep (se 1 (by rfl) ⟨1714928, by rfl⟩ : syracuseStep 2286571 = 3429857) B3429857
theorem B3662653 : Blo 2285435 3662653 := bbase (se 3 (by rfl) ⟨686747, by rfl⟩ : syracuseStep 3662653 = 1373495) (by norm_num)
theorem B4883537 : Blo 2285435 4883537 := bstep (se 2 (by rfl) ⟨1831326, by rfl⟩ : syracuseStep 4883537 = 3662653) B3662653
theorem B13022765 : Blo 2285435 13022765 := bstep (se 3 (by rfl) ⟨2441768, by rfl⟩ : syracuseStep 13022765 = 4883537) B4883537
theorem B8681843 : Blo 2285435 8681843 := bstep (se 1 (by rfl) ⟨6511382, by rfl⟩ : syracuseStep 8681843 = 13022765) B13022765
theorem B5787895 : Blo 2285435 5787895 := bstep (se 1 (by rfl) ⟨4340921, by rfl⟩ : syracuseStep 5787895 = 8681843) B8681843
theorem B7717193 : Blo 2285435 7717193 := bstep (se 2 (by rfl) ⟨2893947, by rfl⟩ : syracuseStep 7717193 = 5787895) B5787895
theorem B5144795 : Blo 2285435 5144795 := bstep (se 1 (by rfl) ⟨3858596, by rfl⟩ : syracuseStep 5144795 = 7717193) B7717193
theorem B3429863 : Blo 2285435 3429863 := bstep (se 1 (by rfl) ⟨2572397, by rfl⟩ : syracuseStep 3429863 = 5144795) B5144795
theorem B2286575 : Blo 2285435 2286575 := bstep (se 1 (by rfl) ⟨1714931, by rfl⟩ : syracuseStep 2286575 = 3429863) B3429863
theorem B3429869 : Blo 2285435 3429869 := bbase (se 3 (by rfl) ⟨643100, by rfl⟩ : syracuseStep 3429869 = 1286201) (by norm_num)
theorem B2286579 : Blo 2285435 2286579 := bstep (se 1 (by rfl) ⟨1714934, by rfl⟩ : syracuseStep 2286579 = 3429869) B3429869
theorem B5144813 : Blo 2285435 5144813 := bbase (se 3 (by rfl) ⟨964652, by rfl⟩ : syracuseStep 5144813 = 1929305) (by norm_num)
theorem B3429875 : Blo 2285435 3429875 := bstep (se 1 (by rfl) ⟨2572406, by rfl⟩ : syracuseStep 3429875 = 5144813) B5144813
theorem B2286583 : Blo 2285435 2286583 := bstep (se 1 (by rfl) ⟨1714937, by rfl⟩ : syracuseStep 2286583 = 3429875) B3429875
theorem B3255709 : Blo 2285435 3255709 := bbase (se 3 (by rfl) ⟨610445, by rfl⟩ : syracuseStep 3255709 = 1220891) (by norm_num)
theorem B4340945 : Blo 2285435 4340945 := bstep (se 2 (by rfl) ⟨1627854, by rfl⟩ : syracuseStep 4340945 = 3255709) B3255709
theorem B2893963 : Blo 2285435 2893963 := bstep (se 1 (by rfl) ⟨2170472, by rfl⟩ : syracuseStep 2893963 = 4340945) B4340945
theorem B3858617 : Blo 2285435 3858617 := bstep (se 2 (by rfl) ⟨1446981, by rfl⟩ : syracuseStep 3858617 = 2893963) B2893963
theorem B2572411 : Blo 2285435 2572411 := bstep (se 1 (by rfl) ⟨1929308, by rfl⟩ : syracuseStep 2572411 = 3858617) B3858617
theorem B3429881 : Blo 2285435 3429881 := bstep (se 2 (by rfl) ⟨1286205, by rfl⟩ : syracuseStep 3429881 = 2572411) B2572411
theorem B2286587 : Blo 2285435 2286587 := bstep (se 1 (by rfl) ⟨1714940, by rfl⟩ : syracuseStep 2286587 = 3429881) B3429881
theorem B2317789 : Blo 2285435 2317789 := bbase (se 3 (by rfl) ⟨434585, by rfl⟩ : syracuseStep 2317789 = 869171) (by norm_num)
theorem B3090385 : Blo 2285435 3090385 := bstep (se 2 (by rfl) ⟨1158894, by rfl⟩ : syracuseStep 3090385 = 2317789) B2317789
theorem B4120513 : Blo 2285435 4120513 := bstep (se 2 (by rfl) ⟨1545192, by rfl⟩ : syracuseStep 4120513 = 3090385) B3090385
theorem B87904277 : Blo 2285435 87904277 := bstep (se 6 (by rfl) ⟨2060256, by rfl⟩ : syracuseStep 87904277 = 4120513) B4120513
theorem B58602851 : Blo 2285435 58602851 := bstep (se 1 (by rfl) ⟨43952138, by rfl⟩ : syracuseStep 58602851 = 87904277) B87904277
theorem B39068567 : Blo 2285435 39068567 := bstep (se 1 (by rfl) ⟨29301425, by rfl⟩ : syracuseStep 39068567 = 58602851) B58602851
theorem B26045711 : Blo 2285435 26045711 := bstep (se 1 (by rfl) ⟨19534283, by rfl⟩ : syracuseStep 26045711 = 39068567) B39068567
theorem B17363807 : Blo 2285435 17363807 := bstep (se 1 (by rfl) ⟨13022855, by rfl⟩ : syracuseStep 17363807 = 26045711) B26045711
theorem B11575871 : Blo 2285435 11575871 := bstep (se 1 (by rfl) ⟨8681903, by rfl⟩ : syracuseStep 11575871 = 17363807) B17363807
theorem B7717247 : Blo 2285435 7717247 := bstep (se 1 (by rfl) ⟨5787935, by rfl⟩ : syracuseStep 7717247 = 11575871) B11575871
theorem B5144831 : Blo 2285435 5144831 := bstep (se 1 (by rfl) ⟨3858623, by rfl⟩ : syracuseStep 5144831 = 7717247) B7717247
theorem B3429887 : Blo 2285435 3429887 := bstep (se 1 (by rfl) ⟨2572415, by rfl⟩ : syracuseStep 3429887 = 5144831) B5144831
theorem B2286591 : Blo 2285435 2286591 := bstep (se 1 (by rfl) ⟨1714943, by rfl⟩ : syracuseStep 2286591 = 3429887) B3429887
theorem B3429893 : Blo 2285435 3429893 := bbase (se 4 (by rfl) ⟨321552, by rfl⟩ : syracuseStep 3429893 = 643105) (by norm_num)
theorem B2286595 : Blo 2285435 2286595 := bstep (se 1 (by rfl) ⟨1714946, by rfl⟩ : syracuseStep 2286595 = 3429893) B3429893
theorem B3858637 : Blo 2285435 3858637 := bbase (se 3 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 3858637 = 1446989) (by norm_num)
theorem B5144849 : Blo 2285435 5144849 := bstep (se 2 (by rfl) ⟨1929318, by rfl⟩ : syracuseStep 5144849 = 3858637) B3858637
theorem B3429899 : Blo 2285435 3429899 := bstep (se 1 (by rfl) ⟨2572424, by rfl⟩ : syracuseStep 3429899 = 5144849) B5144849
theorem B2286599 : Blo 2285435 2286599 := bstep (se 1 (by rfl) ⟨1714949, by rfl⟩ : syracuseStep 2286599 = 3429899) B3429899
theorem B2572429 : Blo 2285435 2572429 := bbase (se 3 (by rfl) ⟨482330, by rfl⟩ : syracuseStep 2572429 = 964661) (by norm_num)
theorem B3429905 : Blo 2285435 3429905 := bstep (se 2 (by rfl) ⟨1286214, by rfl⟩ : syracuseStep 3429905 = 2572429) B2572429
theorem B2286603 : Blo 2285435 2286603 := bstep (se 1 (by rfl) ⟨1714952, by rfl⟩ : syracuseStep 2286603 = 3429905) B3429905
theorem B7717301 : Blo 2285435 7717301 := bbase (se 5 (by rfl) ⟨361748, by rfl⟩ : syracuseStep 7717301 = 723497) (by norm_num)
theorem B5144867 : Blo 2285435 5144867 := bstep (se 1 (by rfl) ⟨3858650, by rfl⟩ : syracuseStep 5144867 = 7717301) B7717301
theorem B3429911 : Blo 2285435 3429911 := bstep (se 1 (by rfl) ⟨2572433, by rfl⟩ : syracuseStep 3429911 = 5144867) B5144867
theorem B2286607 : Blo 2285435 2286607 := bstep (se 1 (by rfl) ⟨1714955, by rfl⟩ : syracuseStep 2286607 = 3429911) B3429911
theorem B3429917 : Blo 2285435 3429917 := bbase (se 3 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 3429917 = 1286219) (by norm_num)
theorem B2286611 : Blo 2285435 2286611 := bstep (se 1 (by rfl) ⟨1714958, by rfl⟩ : syracuseStep 2286611 = 3429917) B3429917
theorem B5144885 : Blo 2285435 5144885 := bbase (se 5 (by rfl) ⟨241166, by rfl⟩ : syracuseStep 5144885 = 482333) (by norm_num)
theorem B3429923 : Blo 2285435 3429923 := bstep (se 1 (by rfl) ⟨2572442, by rfl⟩ : syracuseStep 3429923 = 5144885) B5144885
theorem B2286615 : Blo 2285435 2286615 := bstep (se 1 (by rfl) ⟨1714961, by rfl⟩ : syracuseStep 2286615 = 3429923) B3429923
theorem B2607545 : Blo 2285435 2607545 := bbase (se 2 (by rfl) ⟨977829, by rfl⟩ : syracuseStep 2607545 = 1955659) (by norm_num)
theorem B6953453 : Blo 2285435 6953453 := bstep (se 3 (by rfl) ⟨1303772, by rfl⟩ : syracuseStep 6953453 = 2607545) B2607545
theorem B4635635 : Blo 2285435 4635635 := bstep (se 1 (by rfl) ⟨3476726, by rfl⟩ : syracuseStep 4635635 = 6953453) B6953453
theorem B49446773 : Blo 2285435 49446773 := bstep (se 5 (by rfl) ⟨2317817, by rfl⟩ : syracuseStep 49446773 = 4635635) B4635635
theorem B32964515 : Blo 2285435 32964515 := bstep (se 1 (by rfl) ⟨24723386, by rfl⟩ : syracuseStep 32964515 = 49446773) B49446773
theorem B21976343 : Blo 2285435 21976343 := bstep (se 1 (by rfl) ⟨16482257, by rfl⟩ : syracuseStep 21976343 = 32964515) B32964515
theorem B14650895 : Blo 2285435 14650895 := bstep (se 1 (by rfl) ⟨10988171, by rfl⟩ : syracuseStep 14650895 = 21976343) B21976343
theorem B9767263 : Blo 2285435 9767263 := bstep (se 1 (by rfl) ⟨7325447, by rfl⟩ : syracuseStep 9767263 = 14650895) B14650895
theorem B13023017 : Blo 2285435 13023017 := bstep (se 2 (by rfl) ⟨4883631, by rfl⟩ : syracuseStep 13023017 = 9767263) B9767263
theorem B8682011 : Blo 2285435 8682011 := bstep (se 1 (by rfl) ⟨6511508, by rfl⟩ : syracuseStep 8682011 = 13023017) B13023017
theorem B5788007 : Blo 2285435 5788007 := bstep (se 1 (by rfl) ⟨4341005, by rfl⟩ : syracuseStep 5788007 = 8682011) B8682011
theorem B3858671 : Blo 2285435 3858671 := bstep (se 1 (by rfl) ⟨2894003, by rfl⟩ : syracuseStep 3858671 = 5788007) B5788007
theorem B2572447 : Blo 2285435 2572447 := bstep (se 1 (by rfl) ⟨1929335, by rfl⟩ : syracuseStep 2572447 = 3858671) B3858671
theorem B3429929 : Blo 2285435 3429929 := bstep (se 2 (by rfl) ⟨1286223, by rfl⟩ : syracuseStep 3429929 = 2572447) B2572447
theorem B2286619 : Blo 2285435 2286619 := bstep (se 1 (by rfl) ⟨1714964, by rfl⟩ : syracuseStep 2286619 = 3429929) B3429929
theorem B37085141 : Blo 2285435 37085141 := bbase (se 7 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 37085141 = 869183) (by norm_num)
theorem B24723427 : Blo 2285435 24723427 := bstep (se 1 (by rfl) ⟨18542570, by rfl⟩ : syracuseStep 24723427 = 37085141) B37085141
theorem B32964569 : Blo 2285435 32964569 := bstep (se 2 (by rfl) ⟨12361713, by rfl⟩ : syracuseStep 32964569 = 24723427) B24723427
theorem B21976379 : Blo 2285435 21976379 := bstep (se 1 (by rfl) ⟨16482284, by rfl⟩ : syracuseStep 21976379 = 32964569) B32964569
theorem B14650919 : Blo 2285435 14650919 := bstep (se 1 (by rfl) ⟨10988189, by rfl⟩ : syracuseStep 14650919 = 21976379) B21976379
theorem B9767279 : Blo 2285435 9767279 := bstep (se 1 (by rfl) ⟨7325459, by rfl⟩ : syracuseStep 9767279 = 14650919) B14650919
theorem B6511519 : Blo 2285435 6511519 := bstep (se 1 (by rfl) ⟨4883639, by rfl⟩ : syracuseStep 6511519 = 9767279) B9767279
theorem B8682025 : Blo 2285435 8682025 := bstep (se 2 (by rfl) ⟨3255759, by rfl⟩ : syracuseStep 8682025 = 6511519) B6511519
theorem B11576033 : Blo 2285435 11576033 := bstep (se 2 (by rfl) ⟨4341012, by rfl⟩ : syracuseStep 11576033 = 8682025) B8682025
theorem B7717355 : Blo 2285435 7717355 := bstep (se 1 (by rfl) ⟨5788016, by rfl⟩ : syracuseStep 7717355 = 11576033) B11576033
theorem B5144903 : Blo 2285435 5144903 := bstep (se 1 (by rfl) ⟨3858677, by rfl⟩ : syracuseStep 5144903 = 7717355) B7717355
theorem B3429935 : Blo 2285435 3429935 := bstep (se 1 (by rfl) ⟨2572451, by rfl⟩ : syracuseStep 3429935 = 5144903) B5144903
theorem B2286623 : Blo 2285435 2286623 := bstep (se 1 (by rfl) ⟨1714967, by rfl⟩ : syracuseStep 2286623 = 3429935) B3429935
theorem B3429941 : Blo 2285435 3429941 := bbase (se 5 (by rfl) ⟨160778, by rfl⟩ : syracuseStep 3429941 = 321557) (by norm_num)
theorem B2286627 : Blo 2285435 2286627 := bstep (se 1 (by rfl) ⟨1714970, by rfl⟩ : syracuseStep 2286627 = 3429941) B3429941
theorem B5788037 : Blo 2285435 5788037 := bbase (se 4 (by rfl) ⟨542628, by rfl⟩ : syracuseStep 5788037 = 1085257) (by norm_num)
theorem B3858691 : Blo 2285435 3858691 := bstep (se 1 (by rfl) ⟨2894018, by rfl⟩ : syracuseStep 3858691 = 5788037) B5788037
theorem B5144921 : Blo 2285435 5144921 := bstep (se 2 (by rfl) ⟨1929345, by rfl⟩ : syracuseStep 5144921 = 3858691) B3858691
theorem B3429947 : Blo 2285435 3429947 := bstep (se 1 (by rfl) ⟨2572460, by rfl⟩ : syracuseStep 3429947 = 5144921) B5144921
theorem B2286631 : Blo 2285435 2286631 := bstep (se 1 (by rfl) ⟨1714973, by rfl⟩ : syracuseStep 2286631 = 3429947) B3429947
theorem B2572465 : Blo 2285435 2572465 := bbase (se 2 (by rfl) ⟨964674, by rfl⟩ : syracuseStep 2572465 = 1929349) (by norm_num)
theorem B3429953 : Blo 2285435 3429953 := bstep (se 2 (by rfl) ⟨1286232, by rfl⟩ : syracuseStep 3429953 = 2572465) B2572465
theorem B2286635 : Blo 2285435 2286635 := bstep (se 1 (by rfl) ⟨1714976, by rfl⟩ : syracuseStep 2286635 = 3429953) B3429953
theorem B2441837 : Blo 2285435 2441837 := bbase (se 3 (by rfl) ⟨457844, by rfl⟩ : syracuseStep 2441837 = 915689) (by norm_num)
theorem B6511565 : Blo 2285435 6511565 := bstep (se 3 (by rfl) ⟨1220918, by rfl⟩ : syracuseStep 6511565 = 2441837) B2441837
theorem B4341043 : Blo 2285435 4341043 := bstep (se 1 (by rfl) ⟨3255782, by rfl⟩ : syracuseStep 4341043 = 6511565) B6511565
theorem B5788057 : Blo 2285435 5788057 := bstep (se 2 (by rfl) ⟨2170521, by rfl⟩ : syracuseStep 5788057 = 4341043) B4341043
theorem B7717409 : Blo 2285435 7717409 := bstep (se 2 (by rfl) ⟨2894028, by rfl⟩ : syracuseStep 7717409 = 5788057) B5788057
theorem B5144939 : Blo 2285435 5144939 := bstep (se 1 (by rfl) ⟨3858704, by rfl⟩ : syracuseStep 5144939 = 7717409) B7717409
theorem B3429959 : Blo 2285435 3429959 := bstep (se 1 (by rfl) ⟨2572469, by rfl⟩ : syracuseStep 3429959 = 5144939) B5144939
theorem B2286639 : Blo 2285435 2286639 := bstep (se 1 (by rfl) ⟨1714979, by rfl⟩ : syracuseStep 2286639 = 3429959) B3429959
theorem B3429965 : Blo 2285435 3429965 := bbase (se 3 (by rfl) ⟨643118, by rfl⟩ : syracuseStep 3429965 = 1286237) (by norm_num)
theorem B2286643 : Blo 2285435 2286643 := bstep (se 1 (by rfl) ⟨1714982, by rfl⟩ : syracuseStep 2286643 = 3429965) B3429965
theorem B5144957 : Blo 2285435 5144957 := bbase (se 3 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 5144957 = 1929359) (by norm_num)
theorem B3429971 : Blo 2285435 3429971 := bstep (se 1 (by rfl) ⟨2572478, by rfl⟩ : syracuseStep 3429971 = 5144957) B5144957
theorem B2286647 : Blo 2285435 2286647 := bstep (se 1 (by rfl) ⟨1714985, by rfl⟩ : syracuseStep 2286647 = 3429971) B3429971
theorem B3858725 : Blo 2285435 3858725 := bbase (se 4 (by rfl) ⟨361755, by rfl⟩ : syracuseStep 3858725 = 723511) (by norm_num)
theorem B2572483 : Blo 2285435 2572483 := bstep (se 1 (by rfl) ⟨1929362, by rfl⟩ : syracuseStep 2572483 = 3858725) B3858725
theorem B3429977 : Blo 2285435 3429977 := bstep (se 2 (by rfl) ⟨1286241, by rfl⟩ : syracuseStep 3429977 = 2572483) B2572483
theorem B2286651 : Blo 2285435 2286651 := bstep (se 1 (by rfl) ⟨1714988, by rfl⟩ : syracuseStep 2286651 = 3429977) B3429977
theorem B3255805 : Blo 2285435 3255805 := bbase (se 3 (by rfl) ⟨610463, by rfl⟩ : syracuseStep 3255805 = 1220927) (by norm_num)
theorem B17364293 : Blo 2285435 17364293 := bstep (se 4 (by rfl) ⟨1627902, by rfl⟩ : syracuseStep 17364293 = 3255805) B3255805
theorem B11576195 : Blo 2285435 11576195 := bstep (se 1 (by rfl) ⟨8682146, by rfl⟩ : syracuseStep 11576195 = 17364293) B17364293
theorem B7717463 : Blo 2285435 7717463 := bstep (se 1 (by rfl) ⟨5788097, by rfl⟩ : syracuseStep 7717463 = 11576195) B11576195
theorem B5144975 : Blo 2285435 5144975 := bstep (se 1 (by rfl) ⟨3858731, by rfl⟩ : syracuseStep 5144975 = 7717463) B7717463
theorem B3429983 : Blo 2285435 3429983 := bstep (se 1 (by rfl) ⟨2572487, by rfl⟩ : syracuseStep 3429983 = 5144975) B5144975
theorem B2286655 : Blo 2285435 2286655 := bstep (se 1 (by rfl) ⟨1714991, by rfl⟩ : syracuseStep 2286655 = 3429983) B3429983
theorem B3429989 : Blo 2285435 3429989 := bbase (se 4 (by rfl) ⟨321561, by rfl⟩ : syracuseStep 3429989 = 643123) (by norm_num)
theorem B2286659 : Blo 2285435 2286659 := bstep (se 1 (by rfl) ⟨1714994, by rfl⟩ : syracuseStep 2286659 = 3429989) B3429989
theorem B4120645 : Blo 2285435 4120645 := bbase (se 4 (by rfl) ⟨386310, by rfl⟩ : syracuseStep 4120645 = 772621) (by norm_num)
theorem B5494193 : Blo 2285435 5494193 := bstep (se 2 (by rfl) ⟨2060322, by rfl⟩ : syracuseStep 5494193 = 4120645) B4120645
theorem B3662795 : Blo 2285435 3662795 := bstep (se 1 (by rfl) ⟨2747096, by rfl⟩ : syracuseStep 3662795 = 5494193) B5494193
theorem B2441863 : Blo 2285435 2441863 := bstep (se 1 (by rfl) ⟨1831397, by rfl⟩ : syracuseStep 2441863 = 3662795) B3662795
theorem B3255817 : Blo 2285435 3255817 := bstep (se 2 (by rfl) ⟨1220931, by rfl⟩ : syracuseStep 3255817 = 2441863) B2441863
theorem B4341089 : Blo 2285435 4341089 := bstep (se 2 (by rfl) ⟨1627908, by rfl⟩ : syracuseStep 4341089 = 3255817) B3255817
theorem B2894059 : Blo 2285435 2894059 := bstep (se 1 (by rfl) ⟨2170544, by rfl⟩ : syracuseStep 2894059 = 4341089) B4341089
theorem B3858745 : Blo 2285435 3858745 := bstep (se 2 (by rfl) ⟨1447029, by rfl⟩ : syracuseStep 3858745 = 2894059) B2894059
theorem B5144993 : Blo 2285435 5144993 := bstep (se 2 (by rfl) ⟨1929372, by rfl⟩ : syracuseStep 5144993 = 3858745) B3858745
theorem B3429995 : Blo 2285435 3429995 := bstep (se 1 (by rfl) ⟨2572496, by rfl⟩ : syracuseStep 3429995 = 5144993) B5144993
theorem B2286663 : Blo 2285435 2286663 := bstep (se 1 (by rfl) ⟨1714997, by rfl⟩ : syracuseStep 2286663 = 3429995) B3429995
theorem B2572501 : Blo 2285435 2572501 := bbase (se 7 (by rfl) ⟨30146, by rfl⟩ : syracuseStep 2572501 = 60293) (by norm_num)
theorem B3430001 : Blo 2285435 3430001 := bstep (se 2 (by rfl) ⟨1286250, by rfl⟩ : syracuseStep 3430001 = 2572501) B2572501
theorem B2286667 : Blo 2285435 2286667 := bstep (se 1 (by rfl) ⟨1715000, by rfl⟩ : syracuseStep 2286667 = 3430001) B3430001
theorem B2894069 : Blo 2285435 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B7717517 : Blo 2285435 7717517 := bstep (se 3 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 7717517 = 2894069) B2894069
theorem B5145011 : Blo 2285435 5145011 := bstep (se 1 (by rfl) ⟨3858758, by rfl⟩ : syracuseStep 5145011 = 7717517) B7717517
theorem B3430007 : Blo 2285435 3430007 := bstep (se 1 (by rfl) ⟨2572505, by rfl⟩ : syracuseStep 3430007 = 5145011) B5145011
theorem B2286671 : Blo 2285435 2286671 := bstep (se 1 (by rfl) ⟨1715003, by rfl⟩ : syracuseStep 2286671 = 3430007) B3430007
theorem B3430013 : Blo 2285435 3430013 := bbase (se 3 (by rfl) ⟨643127, by rfl⟩ : syracuseStep 3430013 = 1286255) (by norm_num)
theorem B2286675 : Blo 2285435 2286675 := bstep (se 1 (by rfl) ⟨1715006, by rfl⟩ : syracuseStep 2286675 = 3430013) B3430013
theorem B5145029 : Blo 2285435 5145029 := bbase (se 4 (by rfl) ⟨482346, by rfl⟩ : syracuseStep 5145029 = 964693) (by norm_num)
theorem B3430019 : Blo 2285435 3430019 := bstep (se 1 (by rfl) ⟨2572514, by rfl⟩ : syracuseStep 3430019 = 5145029) B5145029
theorem B2286679 : Blo 2285435 2286679 := bstep (se 1 (by rfl) ⟨1715009, by rfl⟩ : syracuseStep 2286679 = 3430019) B3430019
theorem B7325653 : Blo 2285435 7325653 := bbase (se 7 (by rfl) ⟨85847, by rfl⟩ : syracuseStep 7325653 = 171695) (by norm_num)
theorem B9767537 : Blo 2285435 9767537 := bstep (se 2 (by rfl) ⟨3662826, by rfl⟩ : syracuseStep 9767537 = 7325653) B7325653
theorem B6511691 : Blo 2285435 6511691 := bstep (se 1 (by rfl) ⟨4883768, by rfl⟩ : syracuseStep 6511691 = 9767537) B9767537
theorem B4341127 : Blo 2285435 4341127 := bstep (se 1 (by rfl) ⟨3255845, by rfl⟩ : syracuseStep 4341127 = 6511691) B6511691
theorem B5788169 : Blo 2285435 5788169 := bstep (se 2 (by rfl) ⟨2170563, by rfl⟩ : syracuseStep 5788169 = 4341127) B4341127
theorem B3858779 : Blo 2285435 3858779 := bstep (se 1 (by rfl) ⟨2894084, by rfl⟩ : syracuseStep 3858779 = 5788169) B5788169
theorem B2572519 : Blo 2285435 2572519 := bstep (se 1 (by rfl) ⟨1929389, by rfl⟩ : syracuseStep 2572519 = 3858779) B3858779
theorem B3430025 : Blo 2285435 3430025 := bstep (se 2 (by rfl) ⟨1286259, by rfl⟩ : syracuseStep 3430025 = 2572519) B2572519
theorem B2286683 : Blo 2285435 2286683 := bstep (se 1 (by rfl) ⟨1715012, by rfl⟩ : syracuseStep 2286683 = 3430025) B3430025
theorem B11576357 : Blo 2285435 11576357 := bbase (se 4 (by rfl) ⟨1085283, by rfl⟩ : syracuseStep 11576357 = 2170567) (by norm_num)
theorem B7717571 : Blo 2285435 7717571 := bstep (se 1 (by rfl) ⟨5788178, by rfl⟩ : syracuseStep 7717571 = 11576357) B11576357
theorem B5145047 : Blo 2285435 5145047 := bstep (se 1 (by rfl) ⟨3858785, by rfl⟩ : syracuseStep 5145047 = 7717571) B7717571
theorem B3430031 : Blo 2285435 3430031 := bstep (se 1 (by rfl) ⟨2572523, by rfl⟩ : syracuseStep 3430031 = 5145047) B5145047
theorem B2286687 : Blo 2285435 2286687 := bstep (se 1 (by rfl) ⟨1715015, by rfl⟩ : syracuseStep 2286687 = 3430031) B3430031
theorem B3430037 : Blo 2285435 3430037 := bbase (se 6 (by rfl) ⟨80391, by rfl⟩ : syracuseStep 3430037 = 160783) (by norm_num)
theorem B2286691 : Blo 2285435 2286691 := bstep (se 1 (by rfl) ⟨1715018, by rfl⟩ : syracuseStep 2286691 = 3430037) B3430037
theorem B14651381 : Blo 2285435 14651381 := bbase (se 5 (by rfl) ⟨686783, by rfl⟩ : syracuseStep 14651381 = 1373567) (by norm_num)
theorem B9767587 : Blo 2285435 9767587 := bstep (se 1 (by rfl) ⟨7325690, by rfl⟩ : syracuseStep 9767587 = 14651381) B14651381
theorem B13023449 : Blo 2285435 13023449 := bstep (se 2 (by rfl) ⟨4883793, by rfl⟩ : syracuseStep 13023449 = 9767587) B9767587
theorem B8682299 : Blo 2285435 8682299 := bstep (se 1 (by rfl) ⟨6511724, by rfl⟩ : syracuseStep 8682299 = 13023449) B13023449
theorem B5788199 : Blo 2285435 5788199 := bstep (se 1 (by rfl) ⟨4341149, by rfl⟩ : syracuseStep 5788199 = 8682299) B8682299
theorem B3858799 : Blo 2285435 3858799 := bstep (se 1 (by rfl) ⟨2894099, by rfl⟩ : syracuseStep 3858799 = 5788199) B5788199
theorem B5145065 : Blo 2285435 5145065 := bstep (se 2 (by rfl) ⟨1929399, by rfl⟩ : syracuseStep 5145065 = 3858799) B3858799
theorem B3430043 : Blo 2285435 3430043 := bstep (se 1 (by rfl) ⟨2572532, by rfl⟩ : syracuseStep 3430043 = 5145065) B5145065
theorem B2286695 : Blo 2285435 2286695 := bstep (se 1 (by rfl) ⟨1715021, by rfl⟩ : syracuseStep 2286695 = 3430043) B3430043
theorem B2572537 : Blo 2285435 2572537 := bbase (se 2 (by rfl) ⟨964701, by rfl⟩ : syracuseStep 2572537 = 1929403) (by norm_num)
theorem B3430049 : Blo 2285435 3430049 := bstep (se 2 (by rfl) ⟨1286268, by rfl⟩ : syracuseStep 3430049 = 2572537) B2572537
theorem B2286699 : Blo 2285435 2286699 := bstep (se 1 (by rfl) ⟨1715024, by rfl⟩ : syracuseStep 2286699 = 3430049) B3430049
theorem B9767621 : Blo 2285435 9767621 := bbase (se 4 (by rfl) ⟨915714, by rfl⟩ : syracuseStep 9767621 = 1831429) (by norm_num)
theorem B6511747 : Blo 2285435 6511747 := bstep (se 1 (by rfl) ⟨4883810, by rfl⟩ : syracuseStep 6511747 = 9767621) B9767621
theorem B8682329 : Blo 2285435 8682329 := bstep (se 2 (by rfl) ⟨3255873, by rfl⟩ : syracuseStep 8682329 = 6511747) B6511747
theorem B5788219 : Blo 2285435 5788219 := bstep (se 1 (by rfl) ⟨4341164, by rfl⟩ : syracuseStep 5788219 = 8682329) B8682329
theorem B7717625 : Blo 2285435 7717625 := bstep (se 2 (by rfl) ⟨2894109, by rfl⟩ : syracuseStep 7717625 = 5788219) B5788219
theorem B5145083 : Blo 2285435 5145083 := bstep (se 1 (by rfl) ⟨3858812, by rfl⟩ : syracuseStep 5145083 = 7717625) B7717625
theorem B3430055 : Blo 2285435 3430055 := bstep (se 1 (by rfl) ⟨2572541, by rfl⟩ : syracuseStep 3430055 = 5145083) B5145083
theorem B2286703 : Blo 2285435 2286703 := bstep (se 1 (by rfl) ⟨1715027, by rfl⟩ : syracuseStep 2286703 = 3430055) B3430055
theorem B3430061 : Blo 2285435 3430061 := bbase (se 3 (by rfl) ⟨643136, by rfl⟩ : syracuseStep 3430061 = 1286273) (by norm_num)
theorem B2286707 : Blo 2285435 2286707 := bstep (se 1 (by rfl) ⟨1715030, by rfl⟩ : syracuseStep 2286707 = 3430061) B3430061
theorem B5145101 : Blo 2285435 5145101 := bbase (se 3 (by rfl) ⟨964706, by rfl⟩ : syracuseStep 5145101 = 1929413) (by norm_num)
theorem B3430067 : Blo 2285435 3430067 := bstep (se 1 (by rfl) ⟨2572550, by rfl⟩ : syracuseStep 3430067 = 5145101) B5145101
theorem B2286711 : Blo 2285435 2286711 := bstep (se 1 (by rfl) ⟨1715033, by rfl⟩ : syracuseStep 2286711 = 3430067) B3430067
theorem B2894125 : Blo 2285435 2894125 := bbase (se 3 (by rfl) ⟨542648, by rfl⟩ : syracuseStep 2894125 = 1085297) (by norm_num)
theorem B3858833 : Blo 2285435 3858833 := bstep (se 2 (by rfl) ⟨1447062, by rfl⟩ : syracuseStep 3858833 = 2894125) B2894125
theorem B2572555 : Blo 2285435 2572555 := bstep (se 1 (by rfl) ⟨1929416, by rfl⟩ : syracuseStep 2572555 = 3858833) B3858833
theorem B3430073 : Blo 2285435 3430073 := bstep (se 2 (by rfl) ⟨1286277, by rfl⟩ : syracuseStep 3430073 = 2572555) B2572555
theorem B2286715 : Blo 2285435 2286715 := bstep (se 1 (by rfl) ⟨1715036, by rfl⟩ : syracuseStep 2286715 = 3430073) B3430073
theorem B5494325 : Blo 2285435 5494325 := bbase (se 5 (by rfl) ⟨257546, by rfl⟩ : syracuseStep 5494325 = 515093) (by norm_num)
theorem B14651533 : Blo 2285435 14651533 := bstep (se 3 (by rfl) ⟨2747162, by rfl⟩ : syracuseStep 14651533 = 5494325) B5494325
theorem B19535377 : Blo 2285435 19535377 := bstep (se 2 (by rfl) ⟨7325766, by rfl⟩ : syracuseStep 19535377 = 14651533) B14651533
theorem B26047169 : Blo 2285435 26047169 := bstep (se 2 (by rfl) ⟨9767688, by rfl⟩ : syracuseStep 26047169 = 19535377) B19535377
theorem B17364779 : Blo 2285435 17364779 := bstep (se 1 (by rfl) ⟨13023584, by rfl⟩ : syracuseStep 17364779 = 26047169) B26047169
theorem B11576519 : Blo 2285435 11576519 := bstep (se 1 (by rfl) ⟨8682389, by rfl⟩ : syracuseStep 11576519 = 17364779) B17364779
theorem B7717679 : Blo 2285435 7717679 := bstep (se 1 (by rfl) ⟨5788259, by rfl⟩ : syracuseStep 7717679 = 11576519) B11576519
theorem B5145119 : Blo 2285435 5145119 := bstep (se 1 (by rfl) ⟨3858839, by rfl⟩ : syracuseStep 5145119 = 7717679) B7717679
theorem B3430079 : Blo 2285435 3430079 := bstep (se 1 (by rfl) ⟨2572559, by rfl⟩ : syracuseStep 3430079 = 5145119) B5145119
theorem B2286719 : Blo 2285435 2286719 := bstep (se 1 (by rfl) ⟨1715039, by rfl⟩ : syracuseStep 2286719 = 3430079) B3430079
theorem B3430085 : Blo 2285435 3430085 := bbase (se 4 (by rfl) ⟨321570, by rfl⟩ : syracuseStep 3430085 = 643141) (by norm_num)
theorem B2286723 : Blo 2285435 2286723 := bstep (se 1 (by rfl) ⟨1715042, by rfl⟩ : syracuseStep 2286723 = 3430085) B3430085
theorem B3858853 : Blo 2285435 3858853 := bbase (se 4 (by rfl) ⟨361767, by rfl⟩ : syracuseStep 3858853 = 723535) (by norm_num)
theorem B5145137 : Blo 2285435 5145137 := bstep (se 2 (by rfl) ⟨1929426, by rfl⟩ : syracuseStep 5145137 = 3858853) B3858853
theorem B3430091 : Blo 2285435 3430091 := bstep (se 1 (by rfl) ⟨2572568, by rfl⟩ : syracuseStep 3430091 = 5145137) B5145137
theorem B2286727 : Blo 2285435 2286727 := bstep (se 1 (by rfl) ⟨1715045, by rfl⟩ : syracuseStep 2286727 = 3430091) B3430091
theorem B2572573 : Blo 2285435 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B3430097 : Blo 2285435 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B2286731 : Blo 2285435 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B7717733 : Blo 2285435 7717733 := bbase (se 4 (by rfl) ⟨723537, by rfl⟩ : syracuseStep 7717733 = 1447075) (by norm_num)
theorem B5145155 : Blo 2285435 5145155 := bstep (se 1 (by rfl) ⟨3858866, by rfl⟩ : syracuseStep 5145155 = 7717733) B7717733
theorem B3430103 : Blo 2285435 3430103 := bstep (se 1 (by rfl) ⟨2572577, by rfl⟩ : syracuseStep 3430103 = 5145155) B5145155
theorem B2286735 : Blo 2285435 2286735 := bstep (se 1 (by rfl) ⟨1715051, by rfl⟩ : syracuseStep 2286735 = 3430103) B3430103
theorem B3430109 : Blo 2285435 3430109 := bbase (se 3 (by rfl) ⟨643145, by rfl⟩ : syracuseStep 3430109 = 1286291) (by norm_num)
theorem B2286739 : Blo 2285435 2286739 := bstep (se 1 (by rfl) ⟨1715054, by rfl⟩ : syracuseStep 2286739 = 3430109) B3430109
theorem B5145173 : Blo 2285435 5145173 := bbase (se 8 (by rfl) ⟨30147, by rfl⟩ : syracuseStep 5145173 = 60295) (by norm_num)
theorem B3430115 : Blo 2285435 3430115 := bstep (se 1 (by rfl) ⟨2572586, by rfl⟩ : syracuseStep 3430115 = 5145173) B5145173
theorem B2286743 : Blo 2285435 2286743 := bstep (se 1 (by rfl) ⟨1715057, by rfl⟩ : syracuseStep 2286743 = 3430115) B3430115
theorem B2747197 : Blo 2285435 2747197 := bbase (se 3 (by rfl) ⟨515099, by rfl⟩ : syracuseStep 2747197 = 1030199) (by norm_num)
theorem B3662929 : Blo 2285435 3662929 := bstep (se 2 (by rfl) ⟨1373598, by rfl⟩ : syracuseStep 3662929 = 2747197) B2747197
theorem B4883905 : Blo 2285435 4883905 := bstep (se 2 (by rfl) ⟨1831464, by rfl⟩ : syracuseStep 4883905 = 3662929) B3662929
theorem B6511873 : Blo 2285435 6511873 := bstep (se 2 (by rfl) ⟨2441952, by rfl⟩ : syracuseStep 6511873 = 4883905) B4883905
theorem B8682497 : Blo 2285435 8682497 := bstep (se 2 (by rfl) ⟨3255936, by rfl⟩ : syracuseStep 8682497 = 6511873) B6511873
theorem B5788331 : Blo 2285435 5788331 := bstep (se 1 (by rfl) ⟨4341248, by rfl⟩ : syracuseStep 5788331 = 8682497) B8682497
theorem B3858887 : Blo 2285435 3858887 := bstep (se 1 (by rfl) ⟨2894165, by rfl⟩ : syracuseStep 3858887 = 5788331) B5788331
theorem B2572591 : Blo 2285435 2572591 := bstep (se 1 (by rfl) ⟨1929443, by rfl⟩ : syracuseStep 2572591 = 3858887) B3858887
theorem B3430121 : Blo 2285435 3430121 := bstep (se 2 (by rfl) ⟨1286295, by rfl⟩ : syracuseStep 3430121 = 2572591) B2572591
theorem B2286747 : Blo 2285435 2286747 := bstep (se 1 (by rfl) ⟨1715060, by rfl⟩ : syracuseStep 2286747 = 3430121) B3430121
theorem B2747201 : Blo 2285435 2747201 := bbase (se 2 (by rfl) ⟨1030200, by rfl⟩ : syracuseStep 2747201 = 2060401) (by norm_num)
theorem B29303477 : Blo 2285435 29303477 := bstep (se 5 (by rfl) ⟨1373600, by rfl⟩ : syracuseStep 29303477 = 2747201) B2747201
theorem B19535651 : Blo 2285435 19535651 := bstep (se 1 (by rfl) ⟨14651738, by rfl⟩ : syracuseStep 19535651 = 29303477) B29303477
theorem B13023767 : Blo 2285435 13023767 := bstep (se 1 (by rfl) ⟨9767825, by rfl⟩ : syracuseStep 13023767 = 19535651) B19535651
theorem B8682511 : Blo 2285435 8682511 := bstep (se 1 (by rfl) ⟨6511883, by rfl⟩ : syracuseStep 8682511 = 13023767) B13023767
theorem B11576681 : Blo 2285435 11576681 := bstep (se 2 (by rfl) ⟨4341255, by rfl⟩ : syracuseStep 11576681 = 8682511) B8682511
theorem B7717787 : Blo 2285435 7717787 := bstep (se 1 (by rfl) ⟨5788340, by rfl⟩ : syracuseStep 7717787 = 11576681) B11576681
theorem B5145191 : Blo 2285435 5145191 := bstep (se 1 (by rfl) ⟨3858893, by rfl⟩ : syracuseStep 5145191 = 7717787) B7717787
theorem B3430127 : Blo 2285435 3430127 := bstep (se 1 (by rfl) ⟨2572595, by rfl⟩ : syracuseStep 3430127 = 5145191) B5145191
theorem B2286751 : Blo 2285435 2286751 := bstep (se 1 (by rfl) ⟨1715063, by rfl⟩ : syracuseStep 2286751 = 3430127) B3430127
theorem B3430133 : Blo 2285435 3430133 := bbase (se 5 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 3430133 = 321575) (by norm_num)
theorem B2286755 : Blo 2285435 2286755 := bstep (se 1 (by rfl) ⟨1715066, by rfl⟩ : syracuseStep 2286755 = 3430133) B3430133
theorem B9767861 : Blo 2285435 9767861 := bbase (se 5 (by rfl) ⟨457868, by rfl⟩ : syracuseStep 9767861 = 915737) (by norm_num)
theorem B6511907 : Blo 2285435 6511907 := bstep (se 1 (by rfl) ⟨4883930, by rfl⟩ : syracuseStep 6511907 = 9767861) B9767861
theorem B4341271 : Blo 2285435 4341271 := bstep (se 1 (by rfl) ⟨3255953, by rfl⟩ : syracuseStep 4341271 = 6511907) B6511907
theorem B5788361 : Blo 2285435 5788361 := bstep (se 2 (by rfl) ⟨2170635, by rfl⟩ : syracuseStep 5788361 = 4341271) B4341271
theorem B3858907 : Blo 2285435 3858907 := bstep (se 1 (by rfl) ⟨2894180, by rfl⟩ : syracuseStep 3858907 = 5788361) B5788361
theorem B5145209 : Blo 2285435 5145209 := bstep (se 2 (by rfl) ⟨1929453, by rfl⟩ : syracuseStep 5145209 = 3858907) B3858907
theorem B3430139 : Blo 2285435 3430139 := bstep (se 1 (by rfl) ⟨2572604, by rfl⟩ : syracuseStep 3430139 = 5145209) B5145209
theorem B2286759 : Blo 2285435 2286759 := bstep (se 1 (by rfl) ⟨1715069, by rfl⟩ : syracuseStep 2286759 = 3430139) B3430139
theorem B2572609 : Blo 2285435 2572609 := bbase (se 2 (by rfl) ⟨964728, by rfl⟩ : syracuseStep 2572609 = 1929457) (by norm_num)
theorem B3430145 : Blo 2285435 3430145 := bstep (se 2 (by rfl) ⟨1286304, by rfl⟩ : syracuseStep 3430145 = 2572609) B2572609
theorem B2286763 : Blo 2285435 2286763 := bstep (se 1 (by rfl) ⟨1715072, by rfl⟩ : syracuseStep 2286763 = 3430145) B3430145
theorem B5788381 : Blo 2285435 5788381 := bbase (se 3 (by rfl) ⟨1085321, by rfl⟩ : syracuseStep 5788381 = 2170643) (by norm_num)
theorem B7717841 : Blo 2285435 7717841 := bstep (se 2 (by rfl) ⟨2894190, by rfl⟩ : syracuseStep 7717841 = 5788381) B5788381
theorem B5145227 : Blo 2285435 5145227 := bstep (se 1 (by rfl) ⟨3858920, by rfl⟩ : syracuseStep 5145227 = 7717841) B7717841
theorem B3430151 : Blo 2285435 3430151 := bstep (se 1 (by rfl) ⟨2572613, by rfl⟩ : syracuseStep 3430151 = 5145227) B5145227
theorem B2286767 : Blo 2285435 2286767 := bstep (se 1 (by rfl) ⟨1715075, by rfl⟩ : syracuseStep 2286767 = 3430151) B3430151
theorem B3430157 : Blo 2285435 3430157 := bbase (se 3 (by rfl) ⟨643154, by rfl⟩ : syracuseStep 3430157 = 1286309) (by norm_num)
theorem B2286771 : Blo 2285435 2286771 := bstep (se 1 (by rfl) ⟨1715078, by rfl⟩ : syracuseStep 2286771 = 3430157) B3430157
theorem B5145245 : Blo 2285435 5145245 := bbase (se 3 (by rfl) ⟨964733, by rfl⟩ : syracuseStep 5145245 = 1929467) (by norm_num)
theorem B3430163 : Blo 2285435 3430163 := bstep (se 1 (by rfl) ⟨2572622, by rfl⟩ : syracuseStep 3430163 = 5145245) B5145245
theorem B2286775 : Blo 2285435 2286775 := bstep (se 1 (by rfl) ⟨1715081, by rfl⟩ : syracuseStep 2286775 = 3430163) B3430163
theorem B3858941 : Blo 2285435 3858941 := bbase (se 3 (by rfl) ⟨723551, by rfl⟩ : syracuseStep 3858941 = 1447103) (by norm_num)
theorem B2572627 : Blo 2285435 2572627 := bstep (se 1 (by rfl) ⟨1929470, by rfl⟩ : syracuseStep 2572627 = 3858941) B3858941
theorem B3430169 : Blo 2285435 3430169 := bstep (se 2 (by rfl) ⟨1286313, by rfl⟩ : syracuseStep 3430169 = 2572627) B2572627
theorem B2286779 : Blo 2285435 2286779 := bstep (se 1 (by rfl) ⟨1715084, by rfl⟩ : syracuseStep 2286779 = 3430169) B3430169
theorem B4883981 : Blo 2285435 4883981 := bbase (se 3 (by rfl) ⟨915746, by rfl⟩ : syracuseStep 4883981 = 1831493) (by norm_num)
theorem B13023949 : Blo 2285435 13023949 := bstep (se 3 (by rfl) ⟨2441990, by rfl⟩ : syracuseStep 13023949 = 4883981) B4883981
theorem B17365265 : Blo 2285435 17365265 := bstep (se 2 (by rfl) ⟨6511974, by rfl⟩ : syracuseStep 17365265 = 13023949) B13023949
theorem B11576843 : Blo 2285435 11576843 := bstep (se 1 (by rfl) ⟨8682632, by rfl⟩ : syracuseStep 11576843 = 17365265) B17365265
theorem B7717895 : Blo 2285435 7717895 := bstep (se 1 (by rfl) ⟨5788421, by rfl⟩ : syracuseStep 7717895 = 11576843) B11576843
theorem B5145263 : Blo 2285435 5145263 := bstep (se 1 (by rfl) ⟨3858947, by rfl⟩ : syracuseStep 5145263 = 7717895) B7717895
theorem B3430175 : Blo 2285435 3430175 := bstep (se 1 (by rfl) ⟨2572631, by rfl⟩ : syracuseStep 3430175 = 5145263) B5145263
theorem B2286783 : Blo 2285435 2286783 := bstep (se 1 (by rfl) ⟨1715087, by rfl⟩ : syracuseStep 2286783 = 3430175) B3430175
theorem B3430181 : Blo 2285435 3430181 := bbase (se 4 (by rfl) ⟨321579, by rfl⟩ : syracuseStep 3430181 = 643159) (by norm_num)
theorem B2286787 : Blo 2285435 2286787 := bstep (se 1 (by rfl) ⟨1715090, by rfl⟩ : syracuseStep 2286787 = 3430181) B3430181
theorem B2894221 : Blo 2285435 2894221 := bbase (se 3 (by rfl) ⟨542666, by rfl⟩ : syracuseStep 2894221 = 1085333) (by norm_num)
theorem B3858961 : Blo 2285435 3858961 := bstep (se 2 (by rfl) ⟨1447110, by rfl⟩ : syracuseStep 3858961 = 2894221) B2894221
theorem B5145281 : Blo 2285435 5145281 := bstep (se 2 (by rfl) ⟨1929480, by rfl⟩ : syracuseStep 5145281 = 3858961) B3858961
theorem B3430187 : Blo 2285435 3430187 := bstep (se 1 (by rfl) ⟨2572640, by rfl⟩ : syracuseStep 3430187 = 5145281) B5145281
theorem B2286791 : Blo 2285435 2286791 := bstep (se 1 (by rfl) ⟨1715093, by rfl⟩ : syracuseStep 2286791 = 3430187) B3430187
theorem B2572645 : Blo 2285435 2572645 := bbase (se 4 (by rfl) ⟨241185, by rfl⟩ : syracuseStep 2572645 = 482371) (by norm_num)
theorem B3430193 : Blo 2285435 3430193 := bstep (se 2 (by rfl) ⟨1286322, by rfl⟩ : syracuseStep 3430193 = 2572645) B2572645
theorem B2286795 : Blo 2285435 2286795 := bstep (se 1 (by rfl) ⟨1715096, by rfl⟩ : syracuseStep 2286795 = 3430193) B3430193
theorem B6512021 : Blo 2285435 6512021 := bbase (se 6 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 6512021 = 305251) (by norm_num)
theorem B4341347 : Blo 2285435 4341347 := bstep (se 1 (by rfl) ⟨3256010, by rfl⟩ : syracuseStep 4341347 = 6512021) B6512021
theorem B2894231 : Blo 2285435 2894231 := bstep (se 1 (by rfl) ⟨2170673, by rfl⟩ : syracuseStep 2894231 = 4341347) B4341347
theorem B7717949 : Blo 2285435 7717949 := bstep (se 3 (by rfl) ⟨1447115, by rfl⟩ : syracuseStep 7717949 = 2894231) B2894231
theorem B5145299 : Blo 2285435 5145299 := bstep (se 1 (by rfl) ⟨3858974, by rfl⟩ : syracuseStep 5145299 = 7717949) B7717949
theorem B3430199 : Blo 2285435 3430199 := bstep (se 1 (by rfl) ⟨2572649, by rfl⟩ : syracuseStep 3430199 = 5145299) B5145299
theorem B2286799 : Blo 2285435 2286799 := bstep (se 1 (by rfl) ⟨1715099, by rfl⟩ : syracuseStep 2286799 = 3430199) B3430199
theorem B3430205 : Blo 2285435 3430205 := bbase (se 3 (by rfl) ⟨643163, by rfl⟩ : syracuseStep 3430205 = 1286327) (by norm_num)
theorem B2286803 : Blo 2285435 2286803 := bstep (se 1 (by rfl) ⟨1715102, by rfl⟩ : syracuseStep 2286803 = 3430205) B3430205
theorem B5145317 : Blo 2285435 5145317 := bbase (se 4 (by rfl) ⟨482373, by rfl⟩ : syracuseStep 5145317 = 964747) (by norm_num)
theorem B3430211 : Blo 2285435 3430211 := bstep (se 1 (by rfl) ⟨2572658, by rfl⟩ : syracuseStep 3430211 = 5145317) B5145317
theorem B2286807 : Blo 2285435 2286807 := bstep (se 1 (by rfl) ⟨1715105, by rfl⟩ : syracuseStep 2286807 = 3430211) B3430211
theorem B5788493 : Blo 2285435 5788493 := bbase (se 3 (by rfl) ⟨1085342, by rfl⟩ : syracuseStep 5788493 = 2170685) (by norm_num)
theorem B3858995 : Blo 2285435 3858995 := bstep (se 1 (by rfl) ⟨2894246, by rfl⟩ : syracuseStep 3858995 = 5788493) B5788493
theorem B2572663 : Blo 2285435 2572663 := bstep (se 1 (by rfl) ⟨1929497, by rfl⟩ : syracuseStep 2572663 = 3858995) B3858995
theorem B3430217 : Blo 2285435 3430217 := bstep (se 2 (by rfl) ⟨1286331, by rfl⟩ : syracuseStep 3430217 = 2572663) B2572663
theorem B2286811 : Blo 2285435 2286811 := bstep (se 1 (by rfl) ⟨1715108, by rfl⟩ : syracuseStep 2286811 = 3430217) B3430217
theorem B2442025 : Blo 2285435 2442025 := bbase (se 2 (by rfl) ⟨915759, by rfl⟩ : syracuseStep 2442025 = 1831519) (by norm_num)
theorem B3256033 : Blo 2285435 3256033 := bstep (se 2 (by rfl) ⟨1221012, by rfl⟩ : syracuseStep 3256033 = 2442025) B2442025
theorem B4341377 : Blo 2285435 4341377 := bstep (se 2 (by rfl) ⟨1628016, by rfl⟩ : syracuseStep 4341377 = 3256033) B3256033
theorem B11577005 : Blo 2285435 11577005 := bstep (se 3 (by rfl) ⟨2170688, by rfl⟩ : syracuseStep 11577005 = 4341377) B4341377
theorem B7718003 : Blo 2285435 7718003 := bstep (se 1 (by rfl) ⟨5788502, by rfl⟩ : syracuseStep 7718003 = 11577005) B11577005
theorem B5145335 : Blo 2285435 5145335 := bstep (se 1 (by rfl) ⟨3859001, by rfl⟩ : syracuseStep 5145335 = 7718003) B7718003
theorem B3430223 : Blo 2285435 3430223 := bstep (se 1 (by rfl) ⟨2572667, by rfl⟩ : syracuseStep 3430223 = 5145335) B5145335
theorem B2286815 : Blo 2285435 2286815 := bstep (se 1 (by rfl) ⟨1715111, by rfl⟩ : syracuseStep 2286815 = 3430223) B3430223
theorem B3430229 : Blo 2285435 3430229 := bbase (se 9 (by rfl) ⟨10049, by rfl⟩ : syracuseStep 3430229 = 20099) (by norm_num)
theorem B2286819 : Blo 2285435 2286819 := bstep (se 1 (by rfl) ⟨1715114, by rfl⟩ : syracuseStep 2286819 = 3430229) B3430229
theorem B7326101 : Blo 2285435 7326101 := bbase (se 6 (by rfl) ⟨171705, by rfl⟩ : syracuseStep 7326101 = 343411) (by norm_num)
theorem B4884067 : Blo 2285435 4884067 := bstep (se 1 (by rfl) ⟨3663050, by rfl⟩ : syracuseStep 4884067 = 7326101) B7326101
theorem B6512089 : Blo 2285435 6512089 := bstep (se 2 (by rfl) ⟨2442033, by rfl⟩ : syracuseStep 6512089 = 4884067) B4884067
theorem B8682785 : Blo 2285435 8682785 := bstep (se 2 (by rfl) ⟨3256044, by rfl⟩ : syracuseStep 8682785 = 6512089) B6512089
theorem B5788523 : Blo 2285435 5788523 := bstep (se 1 (by rfl) ⟨4341392, by rfl⟩ : syracuseStep 5788523 = 8682785) B8682785
theorem B3859015 : Blo 2285435 3859015 := bstep (se 1 (by rfl) ⟨2894261, by rfl⟩ : syracuseStep 3859015 = 5788523) B5788523
theorem B5145353 : Blo 2285435 5145353 := bstep (se 2 (by rfl) ⟨1929507, by rfl⟩ : syracuseStep 5145353 = 3859015) B3859015
theorem B3430235 : Blo 2285435 3430235 := bstep (se 1 (by rfl) ⟨2572676, by rfl⟩ : syracuseStep 3430235 = 5145353) B5145353
theorem B2286823 : Blo 2285435 2286823 := bstep (se 1 (by rfl) ⟨1715117, by rfl⟩ : syracuseStep 2286823 = 3430235) B3430235
theorem B2572681 : Blo 2285435 2572681 := bbase (se 2 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 2572681 = 1929511) (by norm_num)
theorem B3430241 : Blo 2285435 3430241 := bstep (se 2 (by rfl) ⟨1286340, by rfl⟩ : syracuseStep 3430241 = 2572681) B2572681
theorem B2286827 : Blo 2285435 2286827 := bstep (se 1 (by rfl) ⟨1715120, by rfl⟩ : syracuseStep 2286827 = 3430241) B3430241
theorem B6782309 : Blo 2285435 6782309 := bbase (se 4 (by rfl) ⟨635841, by rfl⟩ : syracuseStep 6782309 = 1271683) (by norm_num)
theorem B4521539 : Blo 2285435 4521539 := bstep (se 1 (by rfl) ⟨3391154, by rfl⟩ : syracuseStep 4521539 = 6782309) B6782309
theorem B12057437 : Blo 2285435 12057437 := bstep (se 3 (by rfl) ⟨2260769, by rfl⟩ : syracuseStep 12057437 = 4521539) B4521539
theorem B8038291 : Blo 2285435 8038291 := bstep (se 1 (by rfl) ⟨6028718, by rfl⟩ : syracuseStep 8038291 = 12057437) B12057437
theorem B10717721 : Blo 2285435 10717721 := bstep (se 2 (by rfl) ⟨4019145, by rfl⟩ : syracuseStep 10717721 = 8038291) B8038291
theorem B7145147 : Blo 2285435 7145147 := bstep (se 1 (by rfl) ⟨5358860, by rfl⟩ : syracuseStep 7145147 = 10717721) B10717721
theorem B4763431 : Blo 2285435 4763431 := bstep (se 1 (by rfl) ⟨3572573, by rfl⟩ : syracuseStep 4763431 = 7145147) B7145147
theorem B6351241 : Blo 2285435 6351241 := bstep (se 2 (by rfl) ⟨2381715, by rfl⟩ : syracuseStep 6351241 = 4763431) B4763431
theorem B8468321 : Blo 2285435 8468321 := bstep (se 2 (by rfl) ⟨3175620, by rfl⟩ : syracuseStep 8468321 = 6351241) B6351241
theorem B22582189 : Blo 2285435 22582189 := bstep (se 3 (by rfl) ⟨4234160, by rfl⟩ : syracuseStep 22582189 = 8468321) B8468321
theorem B30109585 : Blo 2285435 30109585 := bstep (se 2 (by rfl) ⟨11291094, by rfl⟩ : syracuseStep 30109585 = 22582189) B22582189
theorem B40146113 : Blo 2285435 40146113 := bstep (se 2 (by rfl) ⟨15054792, by rfl⟩ : syracuseStep 40146113 = 30109585) B30109585
theorem B26764075 : Blo 2285435 26764075 := bstep (se 1 (by rfl) ⟨20073056, by rfl⟩ : syracuseStep 26764075 = 40146113) B40146113
theorem B35685433 : Blo 2285435 35685433 := bstep (se 2 (by rfl) ⟨13382037, by rfl⟩ : syracuseStep 35685433 = 26764075) B26764075
theorem B47580577 : Blo 2285435 47580577 := bstep (se 2 (by rfl) ⟨17842716, by rfl⟩ : syracuseStep 47580577 = 35685433) B35685433
theorem B253763077 : Blo 2285435 253763077 := bstep (se 4 (by rfl) ⟨23790288, by rfl⟩ : syracuseStep 253763077 = 47580577) B47580577
theorem B338350769 : Blo 2285435 338350769 := bstep (se 2 (by rfl) ⟨126881538, by rfl⟩ : syracuseStep 338350769 = 253763077) B253763077
theorem B225567179 : Blo 2285435 225567179 := bstep (se 1 (by rfl) ⟨169175384, by rfl⟩ : syracuseStep 225567179 = 338350769) B338350769
theorem B150378119 : Blo 2285435 150378119 := bstep (se 1 (by rfl) ⟨112783589, by rfl⟩ : syracuseStep 150378119 = 225567179) B225567179
theorem B100252079 : Blo 2285435 100252079 := bstep (se 1 (by rfl) ⟨75189059, by rfl⟩ : syracuseStep 100252079 = 150378119) B150378119
theorem B66834719 : Blo 2285435 66834719 := bstep (se 1 (by rfl) ⟨50126039, by rfl⟩ : syracuseStep 66834719 = 100252079) B100252079
theorem B44556479 : Blo 2285435 44556479 := bstep (se 1 (by rfl) ⟨33417359, by rfl⟩ : syracuseStep 44556479 = 66834719) B66834719
theorem B29704319 : Blo 2285435 29704319 := bstep (se 1 (by rfl) ⟨22278239, by rfl⟩ : syracuseStep 29704319 = 44556479) B44556479
theorem B19802879 : Blo 2285435 19802879 := bstep (se 1 (by rfl) ⟨14852159, by rfl⟩ : syracuseStep 19802879 = 29704319) B29704319
theorem B13201919 : Blo 2285435 13201919 := bstep (se 1 (by rfl) ⟨9901439, by rfl⟩ : syracuseStep 13201919 = 19802879) B19802879
theorem B8801279 : Blo 2285435 8801279 := bstep (se 1 (by rfl) ⟨6600959, by rfl⟩ : syracuseStep 8801279 = 13201919) B13201919
theorem B5867519 : Blo 2285435 5867519 := bstep (se 1 (by rfl) ⟨4400639, by rfl⟩ : syracuseStep 5867519 = 8801279) B8801279
theorem B15646717 : Blo 2285435 15646717 := bstep (se 3 (by rfl) ⟨2933759, by rfl⟩ : syracuseStep 15646717 = 5867519) B5867519
theorem B20862289 : Blo 2285435 20862289 := bstep (se 2 (by rfl) ⟨7823358, by rfl⟩ : syracuseStep 20862289 = 15646717) B15646717
theorem B27816385 : Blo 2285435 27816385 := bstep (se 2 (by rfl) ⟨10431144, by rfl⟩ : syracuseStep 27816385 = 20862289) B20862289
theorem B37088513 : Blo 2285435 37088513 := bstep (se 2 (by rfl) ⟨13908192, by rfl⟩ : syracuseStep 37088513 = 27816385) B27816385
theorem B24725675 : Blo 2285435 24725675 := bstep (se 1 (by rfl) ⟨18544256, by rfl⟩ : syracuseStep 24725675 = 37088513) B37088513
theorem B65935133 : Blo 2285435 65935133 := bstep (se 3 (by rfl) ⟨12362837, by rfl⟩ : syracuseStep 65935133 = 24725675) B24725675
theorem B43956755 : Blo 2285435 43956755 := bstep (se 1 (by rfl) ⟨32967566, by rfl⟩ : syracuseStep 43956755 = 65935133) B65935133
theorem B29304503 : Blo 2285435 29304503 := bstep (se 1 (by rfl) ⟨21978377, by rfl⟩ : syracuseStep 29304503 = 43956755) B43956755
theorem B19536335 : Blo 2285435 19536335 := bstep (se 1 (by rfl) ⟨14652251, by rfl⟩ : syracuseStep 19536335 = 29304503) B29304503
theorem B13024223 : Blo 2285435 13024223 := bstep (se 1 (by rfl) ⟨9768167, by rfl⟩ : syracuseStep 13024223 = 19536335) B19536335
theorem B8682815 : Blo 2285435 8682815 := bstep (se 1 (by rfl) ⟨6512111, by rfl⟩ : syracuseStep 8682815 = 13024223) B13024223
theorem B5788543 : Blo 2285435 5788543 := bstep (se 1 (by rfl) ⟨4341407, by rfl⟩ : syracuseStep 5788543 = 8682815) B8682815
theorem B7718057 : Blo 2285435 7718057 := bstep (se 2 (by rfl) ⟨2894271, by rfl⟩ : syracuseStep 7718057 = 5788543) B5788543
theorem B5145371 : Blo 2285435 5145371 := bstep (se 1 (by rfl) ⟨3859028, by rfl⟩ : syracuseStep 5145371 = 7718057) B7718057
theorem B3430247 : Blo 2285435 3430247 := bstep (se 1 (by rfl) ⟨2572685, by rfl⟩ : syracuseStep 3430247 = 5145371) B5145371
theorem B2286831 : Blo 2285435 2286831 := bstep (se 1 (by rfl) ⟨1715123, by rfl⟩ : syracuseStep 2286831 = 3430247) B3430247
theorem B3430253 : Blo 2285435 3430253 := bbase (se 3 (by rfl) ⟨643172, by rfl⟩ : syracuseStep 3430253 = 1286345) (by norm_num)
theorem B2286835 : Blo 2285435 2286835 := bstep (se 1 (by rfl) ⟨1715126, by rfl⟩ : syracuseStep 2286835 = 3430253) B3430253
theorem B5145389 : Blo 2285435 5145389 := bbase (se 3 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 5145389 = 1929521) (by norm_num)
theorem B3430259 : Blo 2285435 3430259 := bstep (se 1 (by rfl) ⟨2572694, by rfl⟩ : syracuseStep 3430259 = 5145389) B5145389
theorem B2286839 : Blo 2285435 2286839 := bstep (se 1 (by rfl) ⟨1715129, by rfl⟩ : syracuseStep 2286839 = 3430259) B3430259
theorem B2933777 : Blo 2285435 2933777 := bbase (se 2 (by rfl) ⟨1100166, by rfl⟩ : syracuseStep 2933777 = 2200333) (by norm_num)
theorem B7823405 : Blo 2285435 7823405 := bstep (se 3 (by rfl) ⟨1466888, by rfl⟩ : syracuseStep 7823405 = 2933777) B2933777
theorem B5215603 : Blo 2285435 5215603 := bstep (se 1 (by rfl) ⟨3911702, by rfl⟩ : syracuseStep 5215603 = 7823405) B7823405
theorem B6954137 : Blo 2285435 6954137 := bstep (se 2 (by rfl) ⟨2607801, by rfl⟩ : syracuseStep 6954137 = 5215603) B5215603
theorem B4636091 : Blo 2285435 4636091 := bstep (se 1 (by rfl) ⟨3477068, by rfl⟩ : syracuseStep 4636091 = 6954137) B6954137
theorem B3090727 : Blo 2285435 3090727 := bstep (se 1 (by rfl) ⟨2318045, by rfl⟩ : syracuseStep 3090727 = 4636091) B4636091
theorem B4120969 : Blo 2285435 4120969 := bstep (se 2 (by rfl) ⟨1545363, by rfl⟩ : syracuseStep 4120969 = 3090727) B3090727
theorem B5494625 : Blo 2285435 5494625 := bstep (se 2 (by rfl) ⟨2060484, by rfl⟩ : syracuseStep 5494625 = 4120969) B4120969
theorem B3663083 : Blo 2285435 3663083 := bstep (se 1 (by rfl) ⟨2747312, by rfl⟩ : syracuseStep 3663083 = 5494625) B5494625
theorem B9768221 : Blo 2285435 9768221 := bstep (se 3 (by rfl) ⟨1831541, by rfl⟩ : syracuseStep 9768221 = 3663083) B3663083
theorem B6512147 : Blo 2285435 6512147 := bstep (se 1 (by rfl) ⟨4884110, by rfl⟩ : syracuseStep 6512147 = 9768221) B9768221
theorem B4341431 : Blo 2285435 4341431 := bstep (se 1 (by rfl) ⟨3256073, by rfl⟩ : syracuseStep 4341431 = 6512147) B6512147
theorem B2894287 : Blo 2285435 2894287 := bstep (se 1 (by rfl) ⟨2170715, by rfl⟩ : syracuseStep 2894287 = 4341431) B4341431
theorem B3859049 : Blo 2285435 3859049 := bstep (se 2 (by rfl) ⟨1447143, by rfl⟩ : syracuseStep 3859049 = 2894287) B2894287
theorem B2572699 : Blo 2285435 2572699 := bstep (se 1 (by rfl) ⟨1929524, by rfl⟩ : syracuseStep 2572699 = 3859049) B3859049
theorem B3430265 : Blo 2285435 3430265 := bstep (se 2 (by rfl) ⟨1286349, by rfl⟩ : syracuseStep 3430265 = 2572699) B2572699
theorem B2286843 : Blo 2285435 2286843 := bstep (se 1 (by rfl) ⟨1715132, by rfl⟩ : syracuseStep 2286843 = 3430265) B3430265
theorem B2607805 : Blo 2285435 2607805 := bbase (se 3 (by rfl) ⟨488963, by rfl⟩ : syracuseStep 2607805 = 977927) (by norm_num)
theorem B3477073 : Blo 2285435 3477073 := bstep (se 2 (by rfl) ⟨1303902, by rfl⟩ : syracuseStep 3477073 = 2607805) B2607805
theorem B4636097 : Blo 2285435 4636097 := bstep (se 2 (by rfl) ⟨1738536, by rfl⟩ : syracuseStep 4636097 = 3477073) B3477073
theorem B3090731 : Blo 2285435 3090731 := bstep (se 1 (by rfl) ⟨2318048, by rfl⟩ : syracuseStep 3090731 = 4636097) B4636097
theorem B8241949 : Blo 2285435 8241949 := bstep (se 3 (by rfl) ⟨1545365, by rfl⟩ : syracuseStep 8241949 = 3090731) B3090731
theorem B10989265 : Blo 2285435 10989265 := bstep (se 2 (by rfl) ⟨4120974, by rfl⟩ : syracuseStep 10989265 = 8241949) B8241949
theorem B14652353 : Blo 2285435 14652353 := bstep (se 2 (by rfl) ⟨5494632, by rfl⟩ : syracuseStep 14652353 = 10989265) B10989265
theorem B39072941 : Blo 2285435 39072941 := bstep (se 3 (by rfl) ⟨7326176, by rfl⟩ : syracuseStep 39072941 = 14652353) B14652353
theorem B26048627 : Blo 2285435 26048627 := bstep (se 1 (by rfl) ⟨19536470, by rfl⟩ : syracuseStep 26048627 = 39072941) B39072941
theorem B17365751 : Blo 2285435 17365751 := bstep (se 1 (by rfl) ⟨13024313, by rfl⟩ : syracuseStep 17365751 = 26048627) B26048627
theorem B11577167 : Blo 2285435 11577167 := bstep (se 1 (by rfl) ⟨8682875, by rfl⟩ : syracuseStep 11577167 = 17365751) B17365751
theorem B7718111 : Blo 2285435 7718111 := bstep (se 1 (by rfl) ⟨5788583, by rfl⟩ : syracuseStep 7718111 = 11577167) B11577167
theorem B5145407 : Blo 2285435 5145407 := bstep (se 1 (by rfl) ⟨3859055, by rfl⟩ : syracuseStep 5145407 = 7718111) B7718111
theorem B3430271 : Blo 2285435 3430271 := bstep (se 1 (by rfl) ⟨2572703, by rfl⟩ : syracuseStep 3430271 = 5145407) B5145407
theorem B2286847 : Blo 2285435 2286847 := bstep (se 1 (by rfl) ⟨1715135, by rfl⟩ : syracuseStep 2286847 = 3430271) B3430271
theorem B3430277 : Blo 2285435 3430277 := bbase (se 4 (by rfl) ⟨321588, by rfl⟩ : syracuseStep 3430277 = 643177) (by norm_num)
theorem B2286851 : Blo 2285435 2286851 := bstep (se 1 (by rfl) ⟨1715138, by rfl⟩ : syracuseStep 2286851 = 3430277) B3430277
theorem B3859069 : Blo 2285435 3859069 := bbase (se 3 (by rfl) ⟨723575, by rfl⟩ : syracuseStep 3859069 = 1447151) (by norm_num)
theorem B5145425 : Blo 2285435 5145425 := bstep (se 2 (by rfl) ⟨1929534, by rfl⟩ : syracuseStep 5145425 = 3859069) B3859069
theorem B3430283 : Blo 2285435 3430283 := bstep (se 1 (by rfl) ⟨2572712, by rfl⟩ : syracuseStep 3430283 = 5145425) B5145425
theorem B2286855 : Blo 2285435 2286855 := bstep (se 1 (by rfl) ⟨1715141, by rfl⟩ : syracuseStep 2286855 = 3430283) B3430283
theorem B2572717 : Blo 2285435 2572717 := bbase (se 3 (by rfl) ⟨482384, by rfl⟩ : syracuseStep 2572717 = 964769) (by norm_num)
theorem B3430289 : Blo 2285435 3430289 := bstep (se 2 (by rfl) ⟨1286358, by rfl⟩ : syracuseStep 3430289 = 2572717) B2572717
theorem B2286859 : Blo 2285435 2286859 := bstep (se 1 (by rfl) ⟨1715144, by rfl⟩ : syracuseStep 2286859 = 3430289) B3430289
theorem B7718165 : Blo 2285435 7718165 := bbase (se 6 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 7718165 = 361789) (by norm_num)
theorem B5145443 : Blo 2285435 5145443 := bstep (se 1 (by rfl) ⟨3859082, by rfl⟩ : syracuseStep 5145443 = 7718165) B7718165
theorem B3430295 : Blo 2285435 3430295 := bstep (se 1 (by rfl) ⟨2572721, by rfl⟩ : syracuseStep 3430295 = 5145443) B5145443
theorem B2286863 : Blo 2285435 2286863 := bstep (se 1 (by rfl) ⟨1715147, by rfl⟩ : syracuseStep 2286863 = 3430295) B3430295
theorem B3430301 : Blo 2285435 3430301 := bbase (se 3 (by rfl) ⟨643181, by rfl⟩ : syracuseStep 3430301 = 1286363) (by norm_num)
theorem B2286867 : Blo 2285435 2286867 := bstep (se 1 (by rfl) ⟨1715150, by rfl⟩ : syracuseStep 2286867 = 3430301) B3430301
theorem B5145461 : Blo 2285435 5145461 := bbase (se 5 (by rfl) ⟨241193, by rfl⟩ : syracuseStep 5145461 = 482387) (by norm_num)
theorem B3430307 : Blo 2285435 3430307 := bstep (se 1 (by rfl) ⟨2572730, by rfl⟩ : syracuseStep 3430307 = 5145461) B5145461
theorem B2286871 : Blo 2285435 2286871 := bstep (se 1 (by rfl) ⟨1715153, by rfl⟩ : syracuseStep 2286871 = 3430307) B3430307
theorem B2318077 : Blo 2285435 2318077 := bbase (se 3 (by rfl) ⟨434639, by rfl⟩ : syracuseStep 2318077 = 869279) (by norm_num)
theorem B12363077 : Blo 2285435 12363077 := bstep (se 4 (by rfl) ⟨1159038, by rfl⟩ : syracuseStep 12363077 = 2318077) B2318077
theorem B32968205 : Blo 2285435 32968205 := bstep (se 3 (by rfl) ⟨6181538, by rfl⟩ : syracuseStep 32968205 = 12363077) B12363077
theorem B21978803 : Blo 2285435 21978803 := bstep (se 1 (by rfl) ⟨16484102, by rfl⟩ : syracuseStep 21978803 = 32968205) B32968205
theorem B14652535 : Blo 2285435 14652535 := bstep (se 1 (by rfl) ⟨10989401, by rfl⟩ : syracuseStep 14652535 = 21978803) B21978803
theorem B19536713 : Blo 2285435 19536713 := bstep (se 2 (by rfl) ⟨7326267, by rfl⟩ : syracuseStep 19536713 = 14652535) B14652535
theorem B13024475 : Blo 2285435 13024475 := bstep (se 1 (by rfl) ⟨9768356, by rfl⟩ : syracuseStep 13024475 = 19536713) B19536713
theorem B8682983 : Blo 2285435 8682983 := bstep (se 1 (by rfl) ⟨6512237, by rfl⟩ : syracuseStep 8682983 = 13024475) B13024475
theorem B5788655 : Blo 2285435 5788655 := bstep (se 1 (by rfl) ⟨4341491, by rfl⟩ : syracuseStep 5788655 = 8682983) B8682983
theorem B3859103 : Blo 2285435 3859103 := bstep (se 1 (by rfl) ⟨2894327, by rfl⟩ : syracuseStep 3859103 = 5788655) B5788655
theorem B2572735 : Blo 2285435 2572735 := bstep (se 1 (by rfl) ⟨1929551, by rfl⟩ : syracuseStep 2572735 = 3859103) B3859103
theorem B3430313 : Blo 2285435 3430313 := bstep (se 2 (by rfl) ⟨1286367, by rfl⟩ : syracuseStep 3430313 = 2572735) B2572735
theorem B2286875 : Blo 2285435 2286875 := bstep (se 1 (by rfl) ⟨1715156, by rfl⟩ : syracuseStep 2286875 = 3430313) B3430313
theorem B8682997 : Blo 2285435 8682997 := bbase (se 5 (by rfl) ⟨407015, by rfl⟩ : syracuseStep 8682997 = 814031) (by norm_num)
theorem B11577329 : Blo 2285435 11577329 := bstep (se 2 (by rfl) ⟨4341498, by rfl⟩ : syracuseStep 11577329 = 8682997) B8682997
theorem B7718219 : Blo 2285435 7718219 := bstep (se 1 (by rfl) ⟨5788664, by rfl⟩ : syracuseStep 7718219 = 11577329) B11577329
theorem B5145479 : Blo 2285435 5145479 := bstep (se 1 (by rfl) ⟨3859109, by rfl⟩ : syracuseStep 5145479 = 7718219) B7718219
theorem B3430319 : Blo 2285435 3430319 := bstep (se 1 (by rfl) ⟨2572739, by rfl⟩ : syracuseStep 3430319 = 5145479) B5145479
theorem B2286879 : Blo 2285435 2286879 := bstep (se 1 (by rfl) ⟨1715159, by rfl⟩ : syracuseStep 2286879 = 3430319) B3430319
theorem B3430325 : Blo 2285435 3430325 := bbase (se 5 (by rfl) ⟨160796, by rfl⟩ : syracuseStep 3430325 = 321593) (by norm_num)
theorem B2286883 : Blo 2285435 2286883 := bstep (se 1 (by rfl) ⟨1715162, by rfl⟩ : syracuseStep 2286883 = 3430325) B3430325
theorem B5788685 : Blo 2285435 5788685 := bbase (se 3 (by rfl) ⟨1085378, by rfl⟩ : syracuseStep 5788685 = 2170757) (by norm_num)
theorem B3859123 : Blo 2285435 3859123 := bstep (se 1 (by rfl) ⟨2894342, by rfl⟩ : syracuseStep 3859123 = 5788685) B5788685
theorem B5145497 : Blo 2285435 5145497 := bstep (se 2 (by rfl) ⟨1929561, by rfl⟩ : syracuseStep 5145497 = 3859123) B3859123
theorem B3430331 : Blo 2285435 3430331 := bstep (se 1 (by rfl) ⟨2572748, by rfl⟩ : syracuseStep 3430331 = 5145497) B5145497
theorem B2286887 : Blo 2285435 2286887 := bstep (se 1 (by rfl) ⟨1715165, by rfl⟩ : syracuseStep 2286887 = 3430331) B3430331
theorem B2572753 : Blo 2285435 2572753 := bbase (se 2 (by rfl) ⟨964782, by rfl⟩ : syracuseStep 2572753 = 1929565) (by norm_num)
theorem B3430337 : Blo 2285435 3430337 := bstep (se 2 (by rfl) ⟨1286376, by rfl⟩ : syracuseStep 3430337 = 2572753) B2572753
theorem B2286891 : Blo 2285435 2286891 := bstep (se 1 (by rfl) ⟨1715168, by rfl⟩ : syracuseStep 2286891 = 3430337) B3430337
theorem B4884221 : Blo 2285435 4884221 := bbase (se 3 (by rfl) ⟨915791, by rfl⟩ : syracuseStep 4884221 = 1831583) (by norm_num)
theorem B3256147 : Blo 2285435 3256147 := bstep (se 1 (by rfl) ⟨2442110, by rfl⟩ : syracuseStep 3256147 = 4884221) B4884221
theorem B4341529 : Blo 2285435 4341529 := bstep (se 2 (by rfl) ⟨1628073, by rfl⟩ : syracuseStep 4341529 = 3256147) B3256147
theorem B5788705 : Blo 2285435 5788705 := bstep (se 2 (by rfl) ⟨2170764, by rfl⟩ : syracuseStep 5788705 = 4341529) B4341529
theorem B7718273 : Blo 2285435 7718273 := bstep (se 2 (by rfl) ⟨2894352, by rfl⟩ : syracuseStep 7718273 = 5788705) B5788705
theorem B5145515 : Blo 2285435 5145515 := bstep (se 1 (by rfl) ⟨3859136, by rfl⟩ : syracuseStep 5145515 = 7718273) B7718273
theorem B3430343 : Blo 2285435 3430343 := bstep (se 1 (by rfl) ⟨2572757, by rfl⟩ : syracuseStep 3430343 = 5145515) B5145515
theorem B2286895 : Blo 2285435 2286895 := bstep (se 1 (by rfl) ⟨1715171, by rfl⟩ : syracuseStep 2286895 = 3430343) B3430343
theorem B3430349 : Blo 2285435 3430349 := bbase (se 3 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 3430349 = 1286381) (by norm_num)
theorem B2286899 : Blo 2285435 2286899 := bstep (se 1 (by rfl) ⟨1715174, by rfl⟩ : syracuseStep 2286899 = 3430349) B3430349
theorem B5145533 : Blo 2285435 5145533 := bbase (se 3 (by rfl) ⟨964787, by rfl⟩ : syracuseStep 5145533 = 1929575) (by norm_num)
theorem B3430355 : Blo 2285435 3430355 := bstep (se 1 (by rfl) ⟨2572766, by rfl⟩ : syracuseStep 3430355 = 5145533) B5145533
theorem B2286903 : Blo 2285435 2286903 := bstep (se 1 (by rfl) ⟨1715177, by rfl⟩ : syracuseStep 2286903 = 3430355) B3430355
theorem B3859157 : Blo 2285435 3859157 := bbase (se 7 (by rfl) ⟨45224, by rfl⟩ : syracuseStep 3859157 = 90449) (by norm_num)
theorem B2572771 : Blo 2285435 2572771 := bstep (se 1 (by rfl) ⟨1929578, by rfl⟩ : syracuseStep 2572771 = 3859157) B3859157
theorem B3430361 : Blo 2285435 3430361 := bstep (se 2 (by rfl) ⟨1286385, by rfl⟩ : syracuseStep 3430361 = 2572771) B2572771
theorem B2286907 : Blo 2285435 2286907 := bstep (se 1 (by rfl) ⟨1715180, by rfl⟩ : syracuseStep 2286907 = 3430361) B3430361
theorem B8242181 : Blo 2285435 8242181 := bbase (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) (by norm_num)
theorem B5494787 : Blo 2285435 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B3663191 : Blo 2285435 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B9768509 : Blo 2285435 9768509 := bstep (se 3 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 9768509 = 3663191) B3663191
theorem B6512339 : Blo 2285435 6512339 := bstep (se 1 (by rfl) ⟨4884254, by rfl⟩ : syracuseStep 6512339 = 9768509) B9768509
theorem B17366237 : Blo 2285435 17366237 := bstep (se 3 (by rfl) ⟨3256169, by rfl⟩ : syracuseStep 17366237 = 6512339) B6512339
theorem B11577491 : Blo 2285435 11577491 := bstep (se 1 (by rfl) ⟨8683118, by rfl⟩ : syracuseStep 11577491 = 17366237) B17366237
theorem B7718327 : Blo 2285435 7718327 := bstep (se 1 (by rfl) ⟨5788745, by rfl⟩ : syracuseStep 7718327 = 11577491) B11577491
theorem B5145551 : Blo 2285435 5145551 := bstep (se 1 (by rfl) ⟨3859163, by rfl⟩ : syracuseStep 5145551 = 7718327) B7718327
theorem B3430367 : Blo 2285435 3430367 := bstep (se 1 (by rfl) ⟨2572775, by rfl⟩ : syracuseStep 3430367 = 5145551) B5145551
theorem B2286911 : Blo 2285435 2286911 := bstep (se 1 (by rfl) ⟨1715183, by rfl⟩ : syracuseStep 2286911 = 3430367) B3430367
theorem B3430373 : Blo 2285435 3430373 := bbase (se 4 (by rfl) ⟨321597, by rfl⟩ : syracuseStep 3430373 = 643195) (by norm_num)
theorem B2286915 : Blo 2285435 2286915 := bstep (se 1 (by rfl) ⟨1715186, by rfl⟩ : syracuseStep 2286915 = 3430373) B3430373
theorem B12363317 : Blo 2285435 12363317 := bbase (se 5 (by rfl) ⟨579530, by rfl⟩ : syracuseStep 12363317 = 1159061) (by norm_num)
theorem B8242211 : Blo 2285435 8242211 := bstep (se 1 (by rfl) ⟨6181658, by rfl⟩ : syracuseStep 8242211 = 12363317) B12363317
theorem B5494807 : Blo 2285435 5494807 := bstep (se 1 (by rfl) ⟨4121105, by rfl⟩ : syracuseStep 5494807 = 8242211) B8242211
theorem B7326409 : Blo 2285435 7326409 := bstep (se 2 (by rfl) ⟨2747403, by rfl⟩ : syracuseStep 7326409 = 5494807) B5494807
theorem B9768545 : Blo 2285435 9768545 := bstep (se 2 (by rfl) ⟨3663204, by rfl⟩ : syracuseStep 9768545 = 7326409) B7326409
theorem B6512363 : Blo 2285435 6512363 := bstep (se 1 (by rfl) ⟨4884272, by rfl⟩ : syracuseStep 6512363 = 9768545) B9768545
theorem B4341575 : Blo 2285435 4341575 := bstep (se 1 (by rfl) ⟨3256181, by rfl⟩ : syracuseStep 4341575 = 6512363) B6512363
theorem B2894383 : Blo 2285435 2894383 := bstep (se 1 (by rfl) ⟨2170787, by rfl⟩ : syracuseStep 2894383 = 4341575) B4341575
theorem B3859177 : Blo 2285435 3859177 := bstep (se 2 (by rfl) ⟨1447191, by rfl⟩ : syracuseStep 3859177 = 2894383) B2894383
theorem B5145569 : Blo 2285435 5145569 := bstep (se 2 (by rfl) ⟨1929588, by rfl⟩ : syracuseStep 5145569 = 3859177) B3859177
theorem B3430379 : Blo 2285435 3430379 := bstep (se 1 (by rfl) ⟨2572784, by rfl⟩ : syracuseStep 3430379 = 5145569) B5145569
theorem B2286919 : Blo 2285435 2286919 := bstep (se 1 (by rfl) ⟨1715189, by rfl⟩ : syracuseStep 2286919 = 3430379) B3430379
theorem B2572789 : Blo 2285435 2572789 := bbase (se 5 (by rfl) ⟨120599, by rfl⟩ : syracuseStep 2572789 = 241199) (by norm_num)
theorem B3430385 : Blo 2285435 3430385 := bstep (se 2 (by rfl) ⟨1286394, by rfl⟩ : syracuseStep 3430385 = 2572789) B2572789
theorem B2286923 : Blo 2285435 2286923 := bstep (se 1 (by rfl) ⟨1715192, by rfl⟩ : syracuseStep 2286923 = 3430385) B3430385
theorem B2894393 : Blo 2285435 2894393 := bbase (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) (by norm_num)
theorem B7718381 : Blo 2285435 7718381 := bstep (se 3 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 7718381 = 2894393) B2894393
theorem B5145587 : Blo 2285435 5145587 := bstep (se 1 (by rfl) ⟨3859190, by rfl⟩ : syracuseStep 5145587 = 7718381) B7718381
theorem B3430391 : Blo 2285435 3430391 := bstep (se 1 (by rfl) ⟨2572793, by rfl⟩ : syracuseStep 3430391 = 5145587) B5145587
theorem B2286927 : Blo 2285435 2286927 := bstep (se 1 (by rfl) ⟨1715195, by rfl⟩ : syracuseStep 2286927 = 3430391) B3430391
theorem B3430397 : Blo 2285435 3430397 := bbase (se 3 (by rfl) ⟨643199, by rfl⟩ : syracuseStep 3430397 = 1286399) (by norm_num)
theorem B2286931 : Blo 2285435 2286931 := bstep (se 1 (by rfl) ⟨1715198, by rfl⟩ : syracuseStep 2286931 = 3430397) B3430397
theorem B5145605 : Blo 2285435 5145605 := bbase (se 4 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 5145605 = 964801) (by norm_num)
theorem B3430403 : Blo 2285435 3430403 := bstep (se 1 (by rfl) ⟨2572802, by rfl⟩ : syracuseStep 3430403 = 5145605) B5145605
theorem B2286935 : Blo 2285435 2286935 := bstep (se 1 (by rfl) ⟨1715201, by rfl⟩ : syracuseStep 2286935 = 3430403) B3430403
theorem B4341613 : Blo 2285435 4341613 := bbase (se 3 (by rfl) ⟨814052, by rfl⟩ : syracuseStep 4341613 = 1628105) (by norm_num)
theorem B5788817 : Blo 2285435 5788817 := bstep (se 2 (by rfl) ⟨2170806, by rfl⟩ : syracuseStep 5788817 = 4341613) B4341613
theorem B3859211 : Blo 2285435 3859211 := bstep (se 1 (by rfl) ⟨2894408, by rfl⟩ : syracuseStep 3859211 = 5788817) B5788817
theorem B2572807 : Blo 2285435 2572807 := bstep (se 1 (by rfl) ⟨1929605, by rfl⟩ : syracuseStep 2572807 = 3859211) B3859211
theorem B3430409 : Blo 2285435 3430409 := bstep (se 2 (by rfl) ⟨1286403, by rfl⟩ : syracuseStep 3430409 = 2572807) B2572807
theorem B2286939 : Blo 2285435 2286939 := bstep (se 1 (by rfl) ⟨1715204, by rfl⟩ : syracuseStep 2286939 = 3430409) B3430409
theorem B11577653 : Blo 2285435 11577653 := bbase (se 5 (by rfl) ⟨542702, by rfl⟩ : syracuseStep 11577653 = 1085405) (by norm_num)
theorem B7718435 : Blo 2285435 7718435 := bstep (se 1 (by rfl) ⟨5788826, by rfl⟩ : syracuseStep 7718435 = 11577653) B11577653
theorem B5145623 : Blo 2285435 5145623 := bstep (se 1 (by rfl) ⟨3859217, by rfl⟩ : syracuseStep 5145623 = 7718435) B7718435
theorem B3430415 : Blo 2285435 3430415 := bstep (se 1 (by rfl) ⟨2572811, by rfl⟩ : syracuseStep 3430415 = 5145623) B5145623
theorem B2286943 : Blo 2285435 2286943 := bstep (se 1 (by rfl) ⟨1715207, by rfl⟩ : syracuseStep 2286943 = 3430415) B3430415
theorem B3430421 : Blo 2285435 3430421 := bbase (se 6 (by rfl) ⟨80400, by rfl⟩ : syracuseStep 3430421 = 160801) (by norm_num)
theorem B2286947 : Blo 2285435 2286947 := bstep (se 1 (by rfl) ⟨1715210, by rfl⟩ : syracuseStep 2286947 = 3430421) B3430421
theorem B8242325 : Blo 2285435 8242325 := bbase (se 6 (by rfl) ⟨193179, by rfl⟩ : syracuseStep 8242325 = 386359) (by norm_num)
theorem B5494883 : Blo 2285435 5494883 := bstep (se 1 (by rfl) ⟨4121162, by rfl⟩ : syracuseStep 5494883 = 8242325) B8242325
theorem B14653021 : Blo 2285435 14653021 := bstep (se 3 (by rfl) ⟨2747441, by rfl⟩ : syracuseStep 14653021 = 5494883) B5494883
theorem B19537361 : Blo 2285435 19537361 := bstep (se 2 (by rfl) ⟨7326510, by rfl⟩ : syracuseStep 19537361 = 14653021) B14653021
theorem B13024907 : Blo 2285435 13024907 := bstep (se 1 (by rfl) ⟨9768680, by rfl⟩ : syracuseStep 13024907 = 19537361) B19537361
theorem B8683271 : Blo 2285435 8683271 := bstep (se 1 (by rfl) ⟨6512453, by rfl⟩ : syracuseStep 8683271 = 13024907) B13024907
theorem B5788847 : Blo 2285435 5788847 := bstep (se 1 (by rfl) ⟨4341635, by rfl⟩ : syracuseStep 5788847 = 8683271) B8683271
theorem B3859231 : Blo 2285435 3859231 := bstep (se 1 (by rfl) ⟨2894423, by rfl⟩ : syracuseStep 3859231 = 5788847) B5788847
theorem B5145641 : Blo 2285435 5145641 := bstep (se 2 (by rfl) ⟨1929615, by rfl⟩ : syracuseStep 5145641 = 3859231) B3859231
theorem B3430427 : Blo 2285435 3430427 := bstep (se 1 (by rfl) ⟨2572820, by rfl⟩ : syracuseStep 3430427 = 5145641) B5145641
theorem B2286951 : Blo 2285435 2286951 := bstep (se 1 (by rfl) ⟨1715213, by rfl⟩ : syracuseStep 2286951 = 3430427) B3430427
theorem B2572825 : Blo 2285435 2572825 := bbase (se 2 (by rfl) ⟨964809, by rfl⟩ : syracuseStep 2572825 = 1929619) (by norm_num)
theorem B3430433 : Blo 2285435 3430433 := bstep (se 2 (by rfl) ⟨1286412, by rfl⟩ : syracuseStep 3430433 = 2572825) B2572825
theorem B2286955 : Blo 2285435 2286955 := bstep (se 1 (by rfl) ⟨1715216, by rfl⟩ : syracuseStep 2286955 = 3430433) B3430433
theorem B8683301 : Blo 2285435 8683301 := bbase (se 4 (by rfl) ⟨814059, by rfl⟩ : syracuseStep 8683301 = 1628119) (by norm_num)
theorem B5788867 : Blo 2285435 5788867 := bstep (se 1 (by rfl) ⟨4341650, by rfl⟩ : syracuseStep 5788867 = 8683301) B8683301
theorem B7718489 : Blo 2285435 7718489 := bstep (se 2 (by rfl) ⟨2894433, by rfl⟩ : syracuseStep 7718489 = 5788867) B5788867
theorem B5145659 : Blo 2285435 5145659 := bstep (se 1 (by rfl) ⟨3859244, by rfl⟩ : syracuseStep 5145659 = 7718489) B7718489
theorem B3430439 : Blo 2285435 3430439 := bstep (se 1 (by rfl) ⟨2572829, by rfl⟩ : syracuseStep 3430439 = 5145659) B5145659
theorem B2286959 : Blo 2285435 2286959 := bstep (se 1 (by rfl) ⟨1715219, by rfl⟩ : syracuseStep 2286959 = 3430439) B3430439
theorem B3430445 : Blo 2285435 3430445 := bbase (se 3 (by rfl) ⟨643208, by rfl⟩ : syracuseStep 3430445 = 1286417) (by norm_num)
theorem B2286963 : Blo 2285435 2286963 := bstep (se 1 (by rfl) ⟨1715222, by rfl⟩ : syracuseStep 2286963 = 3430445) B3430445
theorem B5145677 : Blo 2285435 5145677 := bbase (se 3 (by rfl) ⟨964814, by rfl⟩ : syracuseStep 5145677 = 1929629) (by norm_num)
theorem B3430451 : Blo 2285435 3430451 := bstep (se 1 (by rfl) ⟨2572838, by rfl⟩ : syracuseStep 3430451 = 5145677) B5145677
theorem B2286967 : Blo 2285435 2286967 := bstep (se 1 (by rfl) ⟨1715225, by rfl⟩ : syracuseStep 2286967 = 3430451) B3430451
theorem B2894449 : Blo 2285435 2894449 := bbase (se 2 (by rfl) ⟨1085418, by rfl⟩ : syracuseStep 2894449 = 2170837) (by norm_num)
theorem B3859265 : Blo 2285435 3859265 := bstep (se 2 (by rfl) ⟨1447224, by rfl⟩ : syracuseStep 3859265 = 2894449) B2894449
theorem B2572843 : Blo 2285435 2572843 := bstep (se 1 (by rfl) ⟨1929632, by rfl⟩ : syracuseStep 2572843 = 3859265) B3859265
theorem B3430457 : Blo 2285435 3430457 := bstep (se 2 (by rfl) ⟨1286421, by rfl⟩ : syracuseStep 3430457 = 2572843) B2572843
theorem B2286971 : Blo 2285435 2286971 := bstep (se 1 (by rfl) ⟨1715228, by rfl⟩ : syracuseStep 2286971 = 3430457) B3430457
theorem B17603669 : Blo 2285435 17603669 := bbase (se 8 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 17603669 = 206293) (by norm_num)
theorem B11735779 : Blo 2285435 11735779 := bstep (se 1 (by rfl) ⟨8801834, by rfl⟩ : syracuseStep 11735779 = 17603669) B17603669
theorem B15647705 : Blo 2285435 15647705 := bstep (se 2 (by rfl) ⟨5867889, by rfl⟩ : syracuseStep 15647705 = 11735779) B11735779
theorem B10431803 : Blo 2285435 10431803 := bstep (se 1 (by rfl) ⟨7823852, by rfl⟩ : syracuseStep 10431803 = 15647705) B15647705
theorem B6954535 : Blo 2285435 6954535 := bstep (se 1 (by rfl) ⟨5215901, by rfl⟩ : syracuseStep 6954535 = 10431803) B10431803
theorem B9272713 : Blo 2285435 9272713 := bstep (se 2 (by rfl) ⟨3477267, by rfl⟩ : syracuseStep 9272713 = 6954535) B6954535
theorem B12363617 : Blo 2285435 12363617 := bstep (se 2 (by rfl) ⟨4636356, by rfl⟩ : syracuseStep 12363617 = 9272713) B9272713
theorem B8242411 : Blo 2285435 8242411 := bstep (se 1 (by rfl) ⟨6181808, by rfl⟩ : syracuseStep 8242411 = 12363617) B12363617
theorem B10989881 : Blo 2285435 10989881 := bstep (se 2 (by rfl) ⟨4121205, by rfl⟩ : syracuseStep 10989881 = 8242411) B8242411
theorem B7326587 : Blo 2285435 7326587 := bstep (se 1 (by rfl) ⟨5494940, by rfl⟩ : syracuseStep 7326587 = 10989881) B10989881
theorem B4884391 : Blo 2285435 4884391 := bstep (se 1 (by rfl) ⟨3663293, by rfl⟩ : syracuseStep 4884391 = 7326587) B7326587
theorem B26050085 : Blo 2285435 26050085 := bstep (se 4 (by rfl) ⟨2442195, by rfl⟩ : syracuseStep 26050085 = 4884391) B4884391
theorem B17366723 : Blo 2285435 17366723 := bstep (se 1 (by rfl) ⟨13025042, by rfl⟩ : syracuseStep 17366723 = 26050085) B26050085
theorem B11577815 : Blo 2285435 11577815 := bstep (se 1 (by rfl) ⟨8683361, by rfl⟩ : syracuseStep 11577815 = 17366723) B17366723
theorem B7718543 : Blo 2285435 7718543 := bstep (se 1 (by rfl) ⟨5788907, by rfl⟩ : syracuseStep 7718543 = 11577815) B11577815
theorem B5145695 : Blo 2285435 5145695 := bstep (se 1 (by rfl) ⟨3859271, by rfl⟩ : syracuseStep 5145695 = 7718543) B7718543
theorem B3430463 : Blo 2285435 3430463 := bstep (se 1 (by rfl) ⟨2572847, by rfl⟩ : syracuseStep 3430463 = 5145695) B5145695
theorem B2286975 : Blo 2285435 2286975 := bstep (se 1 (by rfl) ⟨1715231, by rfl⟩ : syracuseStep 2286975 = 3430463) B3430463
theorem B3430469 : Blo 2285435 3430469 := bbase (se 4 (by rfl) ⟨321606, by rfl⟩ : syracuseStep 3430469 = 643213) (by norm_num)
theorem B2286979 : Blo 2285435 2286979 := bstep (se 1 (by rfl) ⟨1715234, by rfl⟩ : syracuseStep 2286979 = 3430469) B3430469
theorem B3859285 : Blo 2285435 3859285 := bbase (se 9 (by rfl) ⟨11306, by rfl⟩ : syracuseStep 3859285 = 22613) (by norm_num)
theorem B5145713 : Blo 2285435 5145713 := bstep (se 2 (by rfl) ⟨1929642, by rfl⟩ : syracuseStep 5145713 = 3859285) B3859285
theorem B3430475 : Blo 2285435 3430475 := bstep (se 1 (by rfl) ⟨2572856, by rfl⟩ : syracuseStep 3430475 = 5145713) B5145713
theorem B2286983 : Blo 2285435 2286983 := bstep (se 1 (by rfl) ⟨1715237, by rfl⟩ : syracuseStep 2286983 = 3430475) B3430475
theorem B2572861 : Blo 2285435 2572861 := bbase (se 3 (by rfl) ⟨482411, by rfl⟩ : syracuseStep 2572861 = 964823) (by norm_num)
theorem B3430481 : Blo 2285435 3430481 := bstep (se 2 (by rfl) ⟨1286430, by rfl⟩ : syracuseStep 3430481 = 2572861) B2572861
theorem B2286987 : Blo 2285435 2286987 := bstep (se 1 (by rfl) ⟨1715240, by rfl⟩ : syracuseStep 2286987 = 3430481) B3430481
theorem B7718597 : Blo 2285435 7718597 := bbase (se 4 (by rfl) ⟨723618, by rfl⟩ : syracuseStep 7718597 = 1447237) (by norm_num)
theorem B5145731 : Blo 2285435 5145731 := bstep (se 1 (by rfl) ⟨3859298, by rfl⟩ : syracuseStep 5145731 = 7718597) B7718597
theorem B3430487 : Blo 2285435 3430487 := bstep (se 1 (by rfl) ⟨2572865, by rfl⟩ : syracuseStep 3430487 = 5145731) B5145731
theorem B2286991 : Blo 2285435 2286991 := bstep (se 1 (by rfl) ⟨1715243, by rfl⟩ : syracuseStep 2286991 = 3430487) B3430487
theorem B3430493 : Blo 2285435 3430493 := bbase (se 3 (by rfl) ⟨643217, by rfl⟩ : syracuseStep 3430493 = 1286435) (by norm_num)
theorem B2286995 : Blo 2285435 2286995 := bstep (se 1 (by rfl) ⟨1715246, by rfl⟩ : syracuseStep 2286995 = 3430493) B3430493
theorem B5145749 : Blo 2285435 5145749 := bbase (se 6 (by rfl) ⟨120603, by rfl⟩ : syracuseStep 5145749 = 241207) (by norm_num)
theorem B3430499 : Blo 2285435 3430499 := bstep (se 1 (by rfl) ⟨2572874, by rfl⟩ : syracuseStep 3430499 = 5145749) B5145749
theorem B2286999 : Blo 2285435 2286999 := bstep (se 1 (by rfl) ⟨1715249, by rfl⟩ : syracuseStep 2286999 = 3430499) B3430499
theorem B3256301 : Blo 2285435 3256301 := bbase (se 3 (by rfl) ⟨610556, by rfl⟩ : syracuseStep 3256301 = 1221113) (by norm_num)
theorem B8683469 : Blo 2285435 8683469 := bstep (se 3 (by rfl) ⟨1628150, by rfl⟩ : syracuseStep 8683469 = 3256301) B3256301
theorem B5788979 : Blo 2285435 5788979 := bstep (se 1 (by rfl) ⟨4341734, by rfl⟩ : syracuseStep 5788979 = 8683469) B8683469
theorem B3859319 : Blo 2285435 3859319 := bstep (se 1 (by rfl) ⟨2894489, by rfl⟩ : syracuseStep 3859319 = 5788979) B5788979
theorem B2572879 : Blo 2285435 2572879 := bstep (se 1 (by rfl) ⟨1929659, by rfl⟩ : syracuseStep 2572879 = 3859319) B3859319
theorem B3430505 : Blo 2285435 3430505 := bstep (se 2 (by rfl) ⟨1286439, by rfl⟩ : syracuseStep 3430505 = 2572879) B2572879
theorem B2287003 : Blo 2285435 2287003 := bstep (se 1 (by rfl) ⟨1715252, by rfl⟩ : syracuseStep 2287003 = 3430505) B3430505
theorem B3911981 : Blo 2285435 3911981 := bbase (se 3 (by rfl) ⟨733496, by rfl⟩ : syracuseStep 3911981 = 1466993) (by norm_num)
theorem B10431949 : Blo 2285435 10431949 := bstep (se 3 (by rfl) ⟨1955990, by rfl⟩ : syracuseStep 10431949 = 3911981) B3911981
theorem B13909265 : Blo 2285435 13909265 := bstep (se 2 (by rfl) ⟨5215974, by rfl⟩ : syracuseStep 13909265 = 10431949) B10431949
theorem B9272843 : Blo 2285435 9272843 := bstep (se 1 (by rfl) ⟨6954632, by rfl⟩ : syracuseStep 9272843 = 13909265) B13909265
theorem B6181895 : Blo 2285435 6181895 := bstep (se 1 (by rfl) ⟨4636421, by rfl⟩ : syracuseStep 6181895 = 9272843) B9272843
theorem B4121263 : Blo 2285435 4121263 := bstep (se 1 (by rfl) ⟨3090947, by rfl⟩ : syracuseStep 4121263 = 6181895) B6181895
theorem B21980069 : Blo 2285435 21980069 := bstep (se 4 (by rfl) ⟨2060631, by rfl⟩ : syracuseStep 21980069 = 4121263) B4121263
theorem B14653379 : Blo 2285435 14653379 := bstep (se 1 (by rfl) ⟨10990034, by rfl⟩ : syracuseStep 14653379 = 21980069) B21980069
theorem B9768919 : Blo 2285435 9768919 := bstep (se 1 (by rfl) ⟨7326689, by rfl⟩ : syracuseStep 9768919 = 14653379) B14653379
theorem B13025225 : Blo 2285435 13025225 := bstep (se 2 (by rfl) ⟨4884459, by rfl⟩ : syracuseStep 13025225 = 9768919) B9768919
theorem B8683483 : Blo 2285435 8683483 := bstep (se 1 (by rfl) ⟨6512612, by rfl⟩ : syracuseStep 8683483 = 13025225) B13025225
theorem B11577977 : Blo 2285435 11577977 := bstep (se 2 (by rfl) ⟨4341741, by rfl⟩ : syracuseStep 11577977 = 8683483) B8683483
theorem B7718651 : Blo 2285435 7718651 := bstep (se 1 (by rfl) ⟨5788988, by rfl⟩ : syracuseStep 7718651 = 11577977) B11577977
theorem B5145767 : Blo 2285435 5145767 := bstep (se 1 (by rfl) ⟨3859325, by rfl⟩ : syracuseStep 5145767 = 7718651) B7718651
theorem B3430511 : Blo 2285435 3430511 := bstep (se 1 (by rfl) ⟨2572883, by rfl⟩ : syracuseStep 3430511 = 5145767) B5145767
theorem B2287007 : Blo 2285435 2287007 := bstep (se 1 (by rfl) ⟨1715255, by rfl⟩ : syracuseStep 2287007 = 3430511) B3430511
theorem B3430517 : Blo 2285435 3430517 := bbase (se 5 (by rfl) ⟨160805, by rfl⟩ : syracuseStep 3430517 = 321611) (by norm_num)
theorem B2287011 : Blo 2285435 2287011 := bstep (se 1 (by rfl) ⟨1715258, by rfl⟩ : syracuseStep 2287011 = 3430517) B3430517
theorem B4341757 : Blo 2285435 4341757 := bbase (se 3 (by rfl) ⟨814079, by rfl⟩ : syracuseStep 4341757 = 1628159) (by norm_num)
theorem B5789009 : Blo 2285435 5789009 := bstep (se 2 (by rfl) ⟨2170878, by rfl⟩ : syracuseStep 5789009 = 4341757) B4341757
theorem B3859339 : Blo 2285435 3859339 := bstep (se 1 (by rfl) ⟨2894504, by rfl⟩ : syracuseStep 3859339 = 5789009) B5789009
theorem B5145785 : Blo 2285435 5145785 := bstep (se 2 (by rfl) ⟨1929669, by rfl⟩ : syracuseStep 5145785 = 3859339) B3859339
theorem B3430523 : Blo 2285435 3430523 := bstep (se 1 (by rfl) ⟨2572892, by rfl⟩ : syracuseStep 3430523 = 5145785) B5145785
theorem B2287015 : Blo 2285435 2287015 := bstep (se 1 (by rfl) ⟨1715261, by rfl⟩ : syracuseStep 2287015 = 3430523) B3430523
theorem B2572897 : Blo 2285435 2572897 := bbase (se 2 (by rfl) ⟨964836, by rfl⟩ : syracuseStep 2572897 = 1929673) (by norm_num)
theorem B3430529 : Blo 2285435 3430529 := bstep (se 2 (by rfl) ⟨1286448, by rfl⟩ : syracuseStep 3430529 = 2572897) B2572897
theorem B2287019 : Blo 2285435 2287019 := bstep (se 1 (by rfl) ⟨1715264, by rfl⟩ : syracuseStep 2287019 = 3430529) B3430529
theorem B5789029 : Blo 2285435 5789029 := bbase (se 4 (by rfl) ⟨542721, by rfl⟩ : syracuseStep 5789029 = 1085443) (by norm_num)
theorem B7718705 : Blo 2285435 7718705 := bstep (se 2 (by rfl) ⟨2894514, by rfl⟩ : syracuseStep 7718705 = 5789029) B5789029
theorem B5145803 : Blo 2285435 5145803 := bstep (se 1 (by rfl) ⟨3859352, by rfl⟩ : syracuseStep 5145803 = 7718705) B7718705
theorem B3430535 : Blo 2285435 3430535 := bstep (se 1 (by rfl) ⟨2572901, by rfl⟩ : syracuseStep 3430535 = 5145803) B5145803
theorem B2287023 : Blo 2285435 2287023 := bstep (se 1 (by rfl) ⟨1715267, by rfl⟩ : syracuseStep 2287023 = 3430535) B3430535
theorem B3430541 : Blo 2285435 3430541 := bbase (se 3 (by rfl) ⟨643226, by rfl⟩ : syracuseStep 3430541 = 1286453) (by norm_num)
theorem B2287027 : Blo 2285435 2287027 := bstep (se 1 (by rfl) ⟨1715270, by rfl⟩ : syracuseStep 2287027 = 3430541) B3430541
theorem B5145821 : Blo 2285435 5145821 := bbase (se 3 (by rfl) ⟨964841, by rfl⟩ : syracuseStep 5145821 = 1929683) (by norm_num)
theorem B3430547 : Blo 2285435 3430547 := bstep (se 1 (by rfl) ⟨2572910, by rfl⟩ : syracuseStep 3430547 = 5145821) B5145821
theorem B2287031 : Blo 2285435 2287031 := bstep (se 1 (by rfl) ⟨1715273, by rfl⟩ : syracuseStep 2287031 = 3430547) B3430547
theorem B3859373 : Blo 2285435 3859373 := bbase (se 3 (by rfl) ⟨723632, by rfl⟩ : syracuseStep 3859373 = 1447265) (by norm_num)
theorem B2572915 : Blo 2285435 2572915 := bstep (se 1 (by rfl) ⟨1929686, by rfl⟩ : syracuseStep 2572915 = 3859373) B3859373
theorem B3430553 : Blo 2285435 3430553 := bstep (se 2 (by rfl) ⟨1286457, by rfl⟩ : syracuseStep 3430553 = 2572915) B2572915
theorem B2287035 : Blo 2285435 2287035 := bstep (se 1 (by rfl) ⟨1715276, by rfl⟩ : syracuseStep 2287035 = 3430553) B3430553
theorem B2785033 : Blo 2285435 2785033 := bbase (se 2 (by rfl) ⟨1044387, by rfl⟩ : syracuseStep 2785033 = 2088775) (by norm_num)
theorem B14853509 : Blo 2285435 14853509 := bstep (se 4 (by rfl) ⟨1392516, by rfl⟩ : syracuseStep 14853509 = 2785033) B2785033
theorem B9902339 : Blo 2285435 9902339 := bstep (se 1 (by rfl) ⟨7426754, by rfl⟩ : syracuseStep 9902339 = 14853509) B14853509
theorem B6601559 : Blo 2285435 6601559 := bstep (se 1 (by rfl) ⟨4951169, by rfl⟩ : syracuseStep 6601559 = 9902339) B9902339
theorem B17604157 : Blo 2285435 17604157 := bstep (se 3 (by rfl) ⟨3300779, by rfl⟩ : syracuseStep 17604157 = 6601559) B6601559
theorem B23472209 : Blo 2285435 23472209 := bstep (se 2 (by rfl) ⟨8802078, by rfl⟩ : syracuseStep 23472209 = 17604157) B17604157
theorem B15648139 : Blo 2285435 15648139 := bstep (se 1 (by rfl) ⟨11736104, by rfl⟩ : syracuseStep 15648139 = 23472209) B23472209
theorem B20864185 : Blo 2285435 20864185 := bstep (se 2 (by rfl) ⟨7824069, by rfl⟩ : syracuseStep 20864185 = 15648139) B15648139
theorem B111275653 : Blo 2285435 111275653 := bstep (se 4 (by rfl) ⟨10432092, by rfl⟩ : syracuseStep 111275653 = 20864185) B20864185
theorem B148367537 : Blo 2285435 148367537 := bstep (se 2 (by rfl) ⟨55637826, by rfl⟩ : syracuseStep 148367537 = 111275653) B111275653
theorem B98911691 : Blo 2285435 98911691 := bstep (se 1 (by rfl) ⟨74183768, by rfl⟩ : syracuseStep 98911691 = 148367537) B148367537
theorem B65941127 : Blo 2285435 65941127 := bstep (se 1 (by rfl) ⟨49455845, by rfl⟩ : syracuseStep 65941127 = 98911691) B98911691
theorem B43960751 : Blo 2285435 43960751 := bstep (se 1 (by rfl) ⟨32970563, by rfl⟩ : syracuseStep 43960751 = 65941127) B65941127
theorem B29307167 : Blo 2285435 29307167 := bstep (se 1 (by rfl) ⟨21980375, by rfl⟩ : syracuseStep 29307167 = 43960751) B43960751
theorem B19538111 : Blo 2285435 19538111 := bstep (se 1 (by rfl) ⟨14653583, by rfl⟩ : syracuseStep 19538111 = 29307167) B29307167
theorem B13025407 : Blo 2285435 13025407 := bstep (se 1 (by rfl) ⟨9769055, by rfl⟩ : syracuseStep 13025407 = 19538111) B19538111
theorem B17367209 : Blo 2285435 17367209 := bstep (se 2 (by rfl) ⟨6512703, by rfl⟩ : syracuseStep 17367209 = 13025407) B13025407
theorem B11578139 : Blo 2285435 11578139 := bstep (se 1 (by rfl) ⟨8683604, by rfl⟩ : syracuseStep 11578139 = 17367209) B17367209
theorem B7718759 : Blo 2285435 7718759 := bstep (se 1 (by rfl) ⟨5789069, by rfl⟩ : syracuseStep 7718759 = 11578139) B11578139
theorem B5145839 : Blo 2285435 5145839 := bstep (se 1 (by rfl) ⟨3859379, by rfl⟩ : syracuseStep 5145839 = 7718759) B7718759
theorem B3430559 : Blo 2285435 3430559 := bstep (se 1 (by rfl) ⟨2572919, by rfl⟩ : syracuseStep 3430559 = 5145839) B5145839
theorem B2287039 : Blo 2285435 2287039 := bstep (se 1 (by rfl) ⟨1715279, by rfl⟩ : syracuseStep 2287039 = 3430559) B3430559
theorem B3430565 : Blo 2285435 3430565 := bbase (se 4 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 3430565 = 643231) (by norm_num)
theorem B2287043 : Blo 2285435 2287043 := bstep (se 1 (by rfl) ⟨1715282, by rfl⟩ : syracuseStep 2287043 = 3430565) B3430565
theorem B2894545 : Blo 2285435 2894545 := bbase (se 2 (by rfl) ⟨1085454, by rfl⟩ : syracuseStep 2894545 = 2170909) (by norm_num)
theorem B3859393 : Blo 2285435 3859393 := bstep (se 2 (by rfl) ⟨1447272, by rfl⟩ : syracuseStep 3859393 = 2894545) B2894545
theorem B5145857 : Blo 2285435 5145857 := bstep (se 2 (by rfl) ⟨1929696, by rfl⟩ : syracuseStep 5145857 = 3859393) B3859393
theorem B3430571 : Blo 2285435 3430571 := bstep (se 1 (by rfl) ⟨2572928, by rfl⟩ : syracuseStep 3430571 = 5145857) B5145857
theorem B2287047 : Blo 2285435 2287047 := bstep (se 1 (by rfl) ⟨1715285, by rfl⟩ : syracuseStep 2287047 = 3430571) B3430571
theorem B2572933 : Blo 2285435 2572933 := bbase (se 4 (by rfl) ⟨241212, by rfl⟩ : syracuseStep 2572933 = 482425) (by norm_num)
theorem B3430577 : Blo 2285435 3430577 := bstep (se 2 (by rfl) ⟨1286466, by rfl⟩ : syracuseStep 3430577 = 2572933) B2572933
theorem B2287051 : Blo 2285435 2287051 := bstep (se 1 (by rfl) ⟨1715288, by rfl⟩ : syracuseStep 2287051 = 3430577) B3430577
theorem B2934049 : Blo 2285435 2934049 := bbase (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) (by norm_num)
theorem B3912065 : Blo 2285435 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B2608043 : Blo 2285435 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B6954781 : Blo 2285435 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B9273041 : Blo 2285435 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B6182027 : Blo 2285435 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B4121351 : Blo 2285435 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B2747567 : Blo 2285435 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B7326845 : Blo 2285435 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B4884563 : Blo 2285435 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B3256375 : Blo 2285435 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B4341833 : Blo 2285435 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B2894555 : Blo 2285435 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B7718813 : Blo 2285435 7718813 := bstep (se 3 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 7718813 = 2894555) B2894555
theorem B5145875 : Blo 2285435 5145875 := bstep (se 1 (by rfl) ⟨3859406, by rfl⟩ : syracuseStep 5145875 = 7718813) B7718813
theorem B3430583 : Blo 2285435 3430583 := bstep (se 1 (by rfl) ⟨2572937, by rfl⟩ : syracuseStep 3430583 = 5145875) B5145875
theorem B2287055 : Blo 2285435 2287055 := bstep (se 1 (by rfl) ⟨1715291, by rfl⟩ : syracuseStep 2287055 = 3430583) B3430583
theorem B3430589 : Blo 2285435 3430589 := bbase (se 3 (by rfl) ⟨643235, by rfl⟩ : syracuseStep 3430589 = 1286471) (by norm_num)
theorem B2287059 : Blo 2285435 2287059 := bstep (se 1 (by rfl) ⟨1715294, by rfl⟩ : syracuseStep 2287059 = 3430589) B3430589
theorem B5145893 : Blo 2285435 5145893 := bbase (se 4 (by rfl) ⟨482427, by rfl⟩ : syracuseStep 5145893 = 964855) (by norm_num)
theorem B3430595 : Blo 2285435 3430595 := bstep (se 1 (by rfl) ⟨2572946, by rfl⟩ : syracuseStep 3430595 = 5145893) B5145893
theorem B2287063 : Blo 2285435 2287063 := bstep (se 1 (by rfl) ⟨1715297, by rfl⟩ : syracuseStep 2287063 = 3430595) B3430595
theorem B5789141 : Blo 2285435 5789141 := bbase (se 7 (by rfl) ⟨67841, by rfl⟩ : syracuseStep 5789141 = 135683) (by norm_num)
theorem B3859427 : Blo 2285435 3859427 := bstep (se 1 (by rfl) ⟨2894570, by rfl⟩ : syracuseStep 3859427 = 5789141) B5789141
theorem B2572951 : Blo 2285435 2572951 := bstep (se 1 (by rfl) ⟨1929713, by rfl⟩ : syracuseStep 2572951 = 3859427) B3859427
theorem B3430601 : Blo 2285435 3430601 := bstep (se 2 (by rfl) ⟨1286475, by rfl⟩ : syracuseStep 3430601 = 2572951) B2572951
theorem B2287067 : Blo 2285435 2287067 := bstep (se 1 (by rfl) ⟨1715300, by rfl⟩ : syracuseStep 2287067 = 3430601) B3430601
theorem B7824181 : Blo 2285435 7824181 := bbase (se 5 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 7824181 = 733517) (by norm_num)
theorem B10432241 : Blo 2285435 10432241 := bstep (se 2 (by rfl) ⟨3912090, by rfl⟩ : syracuseStep 10432241 = 7824181) B7824181
theorem B6954827 : Blo 2285435 6954827 := bstep (se 1 (by rfl) ⟨5216120, by rfl⟩ : syracuseStep 6954827 = 10432241) B10432241
theorem B18546205 : Blo 2285435 18546205 := bstep (se 3 (by rfl) ⟨3477413, by rfl⟩ : syracuseStep 18546205 = 6954827) B6954827
theorem B24728273 : Blo 2285435 24728273 := bstep (se 2 (by rfl) ⟨9273102, by rfl⟩ : syracuseStep 24728273 = 18546205) B18546205
theorem B16485515 : Blo 2285435 16485515 := bstep (se 1 (by rfl) ⟨12364136, by rfl⟩ : syracuseStep 16485515 = 24728273) B24728273
theorem B10990343 : Blo 2285435 10990343 := bstep (se 1 (by rfl) ⟨8242757, by rfl⟩ : syracuseStep 10990343 = 16485515) B16485515
theorem B7326895 : Blo 2285435 7326895 := bstep (se 1 (by rfl) ⟨5495171, by rfl⟩ : syracuseStep 7326895 = 10990343) B10990343
theorem B9769193 : Blo 2285435 9769193 := bstep (se 2 (by rfl) ⟨3663447, by rfl⟩ : syracuseStep 9769193 = 7326895) B7326895
theorem B6512795 : Blo 2285435 6512795 := bstep (se 1 (by rfl) ⟨4884596, by rfl⟩ : syracuseStep 6512795 = 9769193) B9769193
theorem B4341863 : Blo 2285435 4341863 := bstep (se 1 (by rfl) ⟨3256397, by rfl⟩ : syracuseStep 4341863 = 6512795) B6512795
theorem B11578301 : Blo 2285435 11578301 := bstep (se 3 (by rfl) ⟨2170931, by rfl⟩ : syracuseStep 11578301 = 4341863) B4341863
theorem B7718867 : Blo 2285435 7718867 := bstep (se 1 (by rfl) ⟨5789150, by rfl⟩ : syracuseStep 7718867 = 11578301) B11578301
theorem B5145911 : Blo 2285435 5145911 := bstep (se 1 (by rfl) ⟨3859433, by rfl⟩ : syracuseStep 5145911 = 7718867) B7718867
theorem B3430607 : Blo 2285435 3430607 := bstep (se 1 (by rfl) ⟨2572955, by rfl⟩ : syracuseStep 3430607 = 5145911) B5145911
theorem B2287071 : Blo 2285435 2287071 := bstep (se 1 (by rfl) ⟨1715303, by rfl⟩ : syracuseStep 2287071 = 3430607) B3430607
theorem B3430613 : Blo 2285435 3430613 := bbase (se 7 (by rfl) ⟨40202, by rfl⟩ : syracuseStep 3430613 = 80405) (by norm_num)
theorem B2287075 : Blo 2285435 2287075 := bstep (se 1 (by rfl) ⟨1715306, by rfl⟩ : syracuseStep 2287075 = 3430613) B3430613
theorem B3663461 : Blo 2285435 3663461 := bbase (se 4 (by rfl) ⟨343449, by rfl⟩ : syracuseStep 3663461 = 686899) (by norm_num)
theorem B2442307 : Blo 2285435 2442307 := bstep (se 1 (by rfl) ⟨1831730, by rfl⟩ : syracuseStep 2442307 = 3663461) B3663461
theorem B3256409 : Blo 2285435 3256409 := bstep (se 2 (by rfl) ⟨1221153, by rfl⟩ : syracuseStep 3256409 = 2442307) B2442307
theorem B8683757 : Blo 2285435 8683757 := bstep (se 3 (by rfl) ⟨1628204, by rfl⟩ : syracuseStep 8683757 = 3256409) B3256409
theorem B5789171 : Blo 2285435 5789171 := bstep (se 1 (by rfl) ⟨4341878, by rfl⟩ : syracuseStep 5789171 = 8683757) B8683757
theorem B3859447 : Blo 2285435 3859447 := bstep (se 1 (by rfl) ⟨2894585, by rfl⟩ : syracuseStep 3859447 = 5789171) B5789171
theorem B5145929 : Blo 2285435 5145929 := bstep (se 2 (by rfl) ⟨1929723, by rfl⟩ : syracuseStep 5145929 = 3859447) B3859447
theorem B3430619 : Blo 2285435 3430619 := bstep (se 1 (by rfl) ⟨2572964, by rfl⟩ : syracuseStep 3430619 = 5145929) B5145929
theorem B2287079 : Blo 2285435 2287079 := bstep (se 1 (by rfl) ⟨1715309, by rfl⟩ : syracuseStep 2287079 = 3430619) B3430619
theorem B2572969 : Blo 2285435 2572969 := bbase (se 2 (by rfl) ⟨964863, by rfl⟩ : syracuseStep 2572969 = 1929727) (by norm_num)
theorem B3430625 : Blo 2285435 3430625 := bstep (se 2 (by rfl) ⟨1286484, by rfl⟩ : syracuseStep 3430625 = 2572969) B2572969
theorem B2287083 : Blo 2285435 2287083 := bstep (se 1 (by rfl) ⟨1715312, by rfl⟩ : syracuseStep 2287083 = 3430625) B3430625
theorem B2747605 : Blo 2285435 2747605 := bbase (se 7 (by rfl) ⟨32198, by rfl⟩ : syracuseStep 2747605 = 64397) (by norm_num)
theorem B3663473 : Blo 2285435 3663473 := bstep (se 2 (by rfl) ⟨1373802, by rfl⟩ : syracuseStep 3663473 = 2747605) B2747605
theorem B9769261 : Blo 2285435 9769261 := bstep (se 3 (by rfl) ⟨1831736, by rfl⟩ : syracuseStep 9769261 = 3663473) B3663473
theorem B13025681 : Blo 2285435 13025681 := bstep (se 2 (by rfl) ⟨4884630, by rfl⟩ : syracuseStep 13025681 = 9769261) B9769261
theorem B8683787 : Blo 2285435 8683787 := bstep (se 1 (by rfl) ⟨6512840, by rfl⟩ : syracuseStep 8683787 = 13025681) B13025681
theorem B5789191 : Blo 2285435 5789191 := bstep (se 1 (by rfl) ⟨4341893, by rfl⟩ : syracuseStep 5789191 = 8683787) B8683787
theorem B7718921 : Blo 2285435 7718921 := bstep (se 2 (by rfl) ⟨2894595, by rfl⟩ : syracuseStep 7718921 = 5789191) B5789191
theorem B5145947 : Blo 2285435 5145947 := bstep (se 1 (by rfl) ⟨3859460, by rfl⟩ : syracuseStep 5145947 = 7718921) B7718921
theorem B3430631 : Blo 2285435 3430631 := bstep (se 1 (by rfl) ⟨2572973, by rfl⟩ : syracuseStep 3430631 = 5145947) B5145947
theorem B2287087 : Blo 2285435 2287087 := bstep (se 1 (by rfl) ⟨1715315, by rfl⟩ : syracuseStep 2287087 = 3430631) B3430631
theorem B3430637 : Blo 2285435 3430637 := bbase (se 3 (by rfl) ⟨643244, by rfl⟩ : syracuseStep 3430637 = 1286489) (by norm_num)
theorem B2287091 : Blo 2285435 2287091 := bstep (se 1 (by rfl) ⟨1715318, by rfl⟩ : syracuseStep 2287091 = 3430637) B3430637
theorem B5145965 : Blo 2285435 5145965 := bbase (se 3 (by rfl) ⟨964868, by rfl⟩ : syracuseStep 5145965 = 1929737) (by norm_num)
theorem B3430643 : Blo 2285435 3430643 := bstep (se 1 (by rfl) ⟨2572982, by rfl⟩ : syracuseStep 3430643 = 5145965) B5145965
theorem B2287095 : Blo 2285435 2287095 := bstep (se 1 (by rfl) ⟨1715321, by rfl⟩ : syracuseStep 2287095 = 3430643) B3430643
theorem B4341917 : Blo 2285435 4341917 := bbase (se 3 (by rfl) ⟨814109, by rfl⟩ : syracuseStep 4341917 = 1628219) (by norm_num)
theorem B2894611 : Blo 2285435 2894611 := bstep (se 1 (by rfl) ⟨2170958, by rfl⟩ : syracuseStep 2894611 = 4341917) B4341917
theorem B3859481 : Blo 2285435 3859481 := bstep (se 2 (by rfl) ⟨1447305, by rfl⟩ : syracuseStep 3859481 = 2894611) B2894611
theorem B2572987 : Blo 2285435 2572987 := bstep (se 1 (by rfl) ⟨1929740, by rfl⟩ : syracuseStep 2572987 = 3859481) B3859481
theorem B3430649 : Blo 2285435 3430649 := bstep (se 2 (by rfl) ⟨1286493, by rfl⟩ : syracuseStep 3430649 = 2572987) B2572987
theorem B2287099 : Blo 2285435 2287099 := bstep (se 1 (by rfl) ⟨1715324, by rfl⟩ : syracuseStep 2287099 = 3430649) B3430649
theorem B8802325 : Blo 2285435 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B11736433 : Blo 2285435 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B62594309 : Blo 2285435 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B41729539 : Blo 2285435 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B55639385 : Blo 2285435 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B37092923 : Blo 2285435 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B24728615 : Blo 2285435 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B16485743 : Blo 2285435 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B10990495 : Blo 2285435 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B58615973 : Blo 2285435 58615973 := bstep (se 4 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 58615973 = 10990495) B10990495
theorem B39077315 : Blo 2285435 39077315 := bstep (se 1 (by rfl) ⟨29307986, by rfl⟩ : syracuseStep 39077315 = 58615973) B58615973
theorem B26051543 : Blo 2285435 26051543 := bstep (se 1 (by rfl) ⟨19538657, by rfl⟩ : syracuseStep 26051543 = 39077315) B39077315
theorem B17367695 : Blo 2285435 17367695 := bstep (se 1 (by rfl) ⟨13025771, by rfl⟩ : syracuseStep 17367695 = 26051543) B26051543
theorem B11578463 : Blo 2285435 11578463 := bstep (se 1 (by rfl) ⟨8683847, by rfl⟩ : syracuseStep 11578463 = 17367695) B17367695
theorem B7718975 : Blo 2285435 7718975 := bstep (se 1 (by rfl) ⟨5789231, by rfl⟩ : syracuseStep 7718975 = 11578463) B11578463
theorem B5145983 : Blo 2285435 5145983 := bstep (se 1 (by rfl) ⟨3859487, by rfl⟩ : syracuseStep 5145983 = 7718975) B7718975
theorem B3430655 : Blo 2285435 3430655 := bstep (se 1 (by rfl) ⟨2572991, by rfl⟩ : syracuseStep 3430655 = 5145983) B5145983
theorem B2287103 : Blo 2285435 2287103 := bstep (se 1 (by rfl) ⟨1715327, by rfl⟩ : syracuseStep 2287103 = 3430655) B3430655
theorem B3430661 : Blo 2285435 3430661 := bbase (se 4 (by rfl) ⟨321624, by rfl⟩ : syracuseStep 3430661 = 643249) (by norm_num)
theorem B2287107 : Blo 2285435 2287107 := bstep (se 1 (by rfl) ⟨1715330, by rfl⟩ : syracuseStep 2287107 = 3430661) B3430661
theorem B3859501 : Blo 2285435 3859501 := bbase (se 3 (by rfl) ⟨723656, by rfl⟩ : syracuseStep 3859501 = 1447313) (by norm_num)
theorem B5146001 : Blo 2285435 5146001 := bstep (se 2 (by rfl) ⟨1929750, by rfl⟩ : syracuseStep 5146001 = 3859501) B3859501
theorem B3430667 : Blo 2285435 3430667 := bstep (se 1 (by rfl) ⟨2573000, by rfl⟩ : syracuseStep 3430667 = 5146001) B5146001
theorem B2287111 : Blo 2285435 2287111 := bstep (se 1 (by rfl) ⟨1715333, by rfl⟩ : syracuseStep 2287111 = 3430667) B3430667
theorem B2573005 : Blo 2285435 2573005 := bbase (se 3 (by rfl) ⟨482438, by rfl⟩ : syracuseStep 2573005 = 964877) (by norm_num)
theorem B3430673 : Blo 2285435 3430673 := bstep (se 2 (by rfl) ⟨1286502, by rfl⟩ : syracuseStep 3430673 = 2573005) B2573005
theorem B2287115 : Blo 2285435 2287115 := bstep (se 1 (by rfl) ⟨1715336, by rfl⟩ : syracuseStep 2287115 = 3430673) B3430673
theorem B7719029 : Blo 2285435 7719029 := bbase (se 5 (by rfl) ⟨361829, by rfl⟩ : syracuseStep 7719029 = 723659) (by norm_num)
theorem B5146019 : Blo 2285435 5146019 := bstep (se 1 (by rfl) ⟨3859514, by rfl⟩ : syracuseStep 5146019 = 7719029) B7719029
theorem B3430679 : Blo 2285435 3430679 := bstep (se 1 (by rfl) ⟨2573009, by rfl⟩ : syracuseStep 3430679 = 5146019) B5146019
theorem B2287119 : Blo 2285435 2287119 := bstep (se 1 (by rfl) ⟨1715339, by rfl⟩ : syracuseStep 2287119 = 3430679) B3430679
theorem B3430685 : Blo 2285435 3430685 := bbase (se 3 (by rfl) ⟨643253, by rfl⟩ : syracuseStep 3430685 = 1286507) (by norm_num)
theorem B2287123 : Blo 2285435 2287123 := bstep (se 1 (by rfl) ⟨1715342, by rfl⟩ : syracuseStep 2287123 = 3430685) B3430685
theorem B5146037 : Blo 2285435 5146037 := bbase (se 5 (by rfl) ⟨241220, by rfl⟩ : syracuseStep 5146037 = 482441) (by norm_num)
theorem B3430691 : Blo 2285435 3430691 := bstep (se 1 (by rfl) ⟨2573018, by rfl⟩ : syracuseStep 3430691 = 5146037) B5146037
theorem B2287127 : Blo 2285435 2287127 := bstep (se 1 (by rfl) ⟨1715345, by rfl⟩ : syracuseStep 2287127 = 3430691) B3430691
theorem B4884725 : Blo 2285435 4884725 := bbase (se 5 (by rfl) ⟨228971, by rfl⟩ : syracuseStep 4884725 = 457943) (by norm_num)
theorem B13025933 : Blo 2285435 13025933 := bstep (se 3 (by rfl) ⟨2442362, by rfl⟩ : syracuseStep 13025933 = 4884725) B4884725
theorem B8683955 : Blo 2285435 8683955 := bstep (se 1 (by rfl) ⟨6512966, by rfl⟩ : syracuseStep 8683955 = 13025933) B13025933
theorem B5789303 : Blo 2285435 5789303 := bstep (se 1 (by rfl) ⟨4341977, by rfl⟩ : syracuseStep 5789303 = 8683955) B8683955
theorem B3859535 : Blo 2285435 3859535 := bstep (se 1 (by rfl) ⟨2894651, by rfl⟩ : syracuseStep 3859535 = 5789303) B5789303
theorem B2573023 : Blo 2285435 2573023 := bstep (se 1 (by rfl) ⟨1929767, by rfl⟩ : syracuseStep 2573023 = 3859535) B3859535
theorem B3430697 : Blo 2285435 3430697 := bstep (se 2 (by rfl) ⟨1286511, by rfl⟩ : syracuseStep 3430697 = 2573023) B2573023
theorem B2287131 : Blo 2285435 2287131 := bstep (se 1 (by rfl) ⟨1715348, by rfl⟩ : syracuseStep 2287131 = 3430697) B3430697
theorem B4884733 : Blo 2285435 4884733 := bbase (se 3 (by rfl) ⟨915887, by rfl⟩ : syracuseStep 4884733 = 1831775) (by norm_num)
theorem B6512977 : Blo 2285435 6512977 := bstep (se 2 (by rfl) ⟨2442366, by rfl⟩ : syracuseStep 6512977 = 4884733) B4884733
theorem B8683969 : Blo 2285435 8683969 := bstep (se 2 (by rfl) ⟨3256488, by rfl⟩ : syracuseStep 8683969 = 6512977) B6512977
theorem B11578625 : Blo 2285435 11578625 := bstep (se 2 (by rfl) ⟨4341984, by rfl⟩ : syracuseStep 11578625 = 8683969) B8683969
theorem B7719083 : Blo 2285435 7719083 := bstep (se 1 (by rfl) ⟨5789312, by rfl⟩ : syracuseStep 7719083 = 11578625) B11578625
theorem B5146055 : Blo 2285435 5146055 := bstep (se 1 (by rfl) ⟨3859541, by rfl⟩ : syracuseStep 5146055 = 7719083) B7719083
theorem B3430703 : Blo 2285435 3430703 := bstep (se 1 (by rfl) ⟨2573027, by rfl⟩ : syracuseStep 3430703 = 5146055) B5146055
theorem B2287135 : Blo 2285435 2287135 := bstep (se 1 (by rfl) ⟨1715351, by rfl⟩ : syracuseStep 2287135 = 3430703) B3430703
theorem B3430709 : Blo 2285435 3430709 := bbase (se 5 (by rfl) ⟨160814, by rfl⟩ : syracuseStep 3430709 = 321629) (by norm_num)
theorem B2287139 : Blo 2285435 2287139 := bstep (se 1 (by rfl) ⟨1715354, by rfl⟩ : syracuseStep 2287139 = 3430709) B3430709
theorem B5789333 : Blo 2285435 5789333 := bbase (se 6 (by rfl) ⟨135687, by rfl⟩ : syracuseStep 5789333 = 271375) (by norm_num)
theorem B3859555 : Blo 2285435 3859555 := bstep (se 1 (by rfl) ⟨2894666, by rfl⟩ : syracuseStep 3859555 = 5789333) B5789333
theorem B5146073 : Blo 2285435 5146073 := bstep (se 2 (by rfl) ⟨1929777, by rfl⟩ : syracuseStep 5146073 = 3859555) B3859555
theorem B3430715 : Blo 2285435 3430715 := bstep (se 1 (by rfl) ⟨2573036, by rfl⟩ : syracuseStep 3430715 = 5146073) B5146073
theorem B2287143 : Blo 2285435 2287143 := bstep (se 1 (by rfl) ⟨1715357, by rfl⟩ : syracuseStep 2287143 = 3430715) B3430715
theorem B2573041 : Blo 2285435 2573041 := bbase (se 2 (by rfl) ⟨964890, by rfl⟩ : syracuseStep 2573041 = 1929781) (by norm_num)
theorem B3430721 : Blo 2285435 3430721 := bstep (se 2 (by rfl) ⟨1286520, by rfl⟩ : syracuseStep 3430721 = 2573041) B2573041
theorem B2287147 : Blo 2285435 2287147 := bstep (se 1 (by rfl) ⟨1715360, by rfl⟩ : syracuseStep 2287147 = 3430721) B3430721
theorem B5646341 : Blo 2285435 5646341 := bbase (se 4 (by rfl) ⟨529344, by rfl⟩ : syracuseStep 5646341 = 1058689) (by norm_num)
theorem B3764227 : Blo 2285435 3764227 := bstep (se 1 (by rfl) ⟨2823170, by rfl⟩ : syracuseStep 3764227 = 5646341) B5646341
theorem B5018969 : Blo 2285435 5018969 := bstep (se 2 (by rfl) ⟨1882113, by rfl⟩ : syracuseStep 5018969 = 3764227) B3764227
theorem B13383917 : Blo 2285435 13383917 := bstep (se 3 (by rfl) ⟨2509484, by rfl⟩ : syracuseStep 13383917 = 5018969) B5018969
theorem B8922611 : Blo 2285435 8922611 := bstep (se 1 (by rfl) ⟨6691958, by rfl⟩ : syracuseStep 8922611 = 13383917) B13383917
theorem B5948407 : Blo 2285435 5948407 := bstep (se 1 (by rfl) ⟨4461305, by rfl⟩ : syracuseStep 5948407 = 8922611) B8922611
theorem B7931209 : Blo 2285435 7931209 := bstep (se 2 (by rfl) ⟨2974203, by rfl⟩ : syracuseStep 7931209 = 5948407) B5948407
theorem B10574945 : Blo 2285435 10574945 := bstep (se 2 (by rfl) ⟨3965604, by rfl⟩ : syracuseStep 10574945 = 7931209) B7931209
theorem B7049963 : Blo 2285435 7049963 := bstep (se 1 (by rfl) ⟨5287472, by rfl⟩ : syracuseStep 7049963 = 10574945) B10574945
theorem B18799901 : Blo 2285435 18799901 := bstep (se 3 (by rfl) ⟨3524981, by rfl⟩ : syracuseStep 18799901 = 7049963) B7049963
theorem B12533267 : Blo 2285435 12533267 := bstep (se 1 (by rfl) ⟨9399950, by rfl⟩ : syracuseStep 12533267 = 18799901) B18799901
theorem B8355511 : Blo 2285435 8355511 := bstep (se 1 (by rfl) ⟨6266633, by rfl⟩ : syracuseStep 8355511 = 12533267) B12533267
theorem B11140681 : Blo 2285435 11140681 := bstep (se 2 (by rfl) ⟨4177755, by rfl⟩ : syracuseStep 11140681 = 8355511) B8355511
theorem B14854241 : Blo 2285435 14854241 := bstep (se 2 (by rfl) ⟨5570340, by rfl⟩ : syracuseStep 14854241 = 11140681) B11140681
theorem B9902827 : Blo 2285435 9902827 := bstep (se 1 (by rfl) ⟨7427120, by rfl⟩ : syracuseStep 9902827 = 14854241) B14854241
theorem B13203769 : Blo 2285435 13203769 := bstep (se 2 (by rfl) ⟨4951413, by rfl⟩ : syracuseStep 13203769 = 9902827) B9902827
theorem B17605025 : Blo 2285435 17605025 := bstep (se 2 (by rfl) ⟨6601884, by rfl⟩ : syracuseStep 17605025 = 13203769) B13203769
theorem B11736683 : Blo 2285435 11736683 := bstep (se 1 (by rfl) ⟨8802512, by rfl⟩ : syracuseStep 11736683 = 17605025) B17605025
theorem B7824455 : Blo 2285435 7824455 := bstep (se 1 (by rfl) ⟨5868341, by rfl⟩ : syracuseStep 7824455 = 11736683) B11736683
theorem B5216303 : Blo 2285435 5216303 := bstep (se 1 (by rfl) ⟨3912227, by rfl⟩ : syracuseStep 5216303 = 7824455) B7824455
theorem B3477535 : Blo 2285435 3477535 := bstep (se 1 (by rfl) ⟨2608151, by rfl⟩ : syracuseStep 3477535 = 5216303) B5216303
theorem B74187413 : Blo 2285435 74187413 := bstep (se 6 (by rfl) ⟨1738767, by rfl⟩ : syracuseStep 74187413 = 3477535) B3477535
theorem B49458275 : Blo 2285435 49458275 := bstep (se 1 (by rfl) ⟨37093706, by rfl⟩ : syracuseStep 49458275 = 74187413) B74187413
theorem B32972183 : Blo 2285435 32972183 := bstep (se 1 (by rfl) ⟨24729137, by rfl⟩ : syracuseStep 32972183 = 49458275) B49458275
theorem B21981455 : Blo 2285435 21981455 := bstep (se 1 (by rfl) ⟨16486091, by rfl⟩ : syracuseStep 21981455 = 32972183) B32972183
theorem B14654303 : Blo 2285435 14654303 := bstep (se 1 (by rfl) ⟨10990727, by rfl⟩ : syracuseStep 14654303 = 21981455) B21981455
theorem B9769535 : Blo 2285435 9769535 := bstep (se 1 (by rfl) ⟨7327151, by rfl⟩ : syracuseStep 9769535 = 14654303) B14654303
theorem B6513023 : Blo 2285435 6513023 := bstep (se 1 (by rfl) ⟨4884767, by rfl⟩ : syracuseStep 6513023 = 9769535) B9769535
theorem B4342015 : Blo 2285435 4342015 := bstep (se 1 (by rfl) ⟨3256511, by rfl⟩ : syracuseStep 4342015 = 6513023) B6513023
theorem B5789353 : Blo 2285435 5789353 := bstep (se 2 (by rfl) ⟨2171007, by rfl⟩ : syracuseStep 5789353 = 4342015) B4342015
theorem B7719137 : Blo 2285435 7719137 := bstep (se 2 (by rfl) ⟨2894676, by rfl⟩ : syracuseStep 7719137 = 5789353) B5789353
theorem B5146091 : Blo 2285435 5146091 := bstep (se 1 (by rfl) ⟨3859568, by rfl⟩ : syracuseStep 5146091 = 7719137) B7719137
theorem B3430727 : Blo 2285435 3430727 := bstep (se 1 (by rfl) ⟨2573045, by rfl⟩ : syracuseStep 3430727 = 5146091) B5146091
theorem B2287151 : Blo 2285435 2287151 := bstep (se 1 (by rfl) ⟨1715363, by rfl⟩ : syracuseStep 2287151 = 3430727) B3430727
theorem B3430733 : Blo 2285435 3430733 := bbase (se 3 (by rfl) ⟨643262, by rfl⟩ : syracuseStep 3430733 = 1286525) (by norm_num)
theorem B2287155 : Blo 2285435 2287155 := bstep (se 1 (by rfl) ⟨1715366, by rfl⟩ : syracuseStep 2287155 = 3430733) B3430733
theorem B5146109 : Blo 2285435 5146109 := bbase (se 3 (by rfl) ⟨964895, by rfl⟩ : syracuseStep 5146109 = 1929791) (by norm_num)
theorem B3430739 : Blo 2285435 3430739 := bstep (se 1 (by rfl) ⟨2573054, by rfl⟩ : syracuseStep 3430739 = 5146109) B5146109
theorem B2287159 : Blo 2285435 2287159 := bstep (se 1 (by rfl) ⟨1715369, by rfl⟩ : syracuseStep 2287159 = 3430739) B3430739
theorem B3859589 : Blo 2285435 3859589 := bbase (se 4 (by rfl) ⟨361836, by rfl⟩ : syracuseStep 3859589 = 723673) (by norm_num)
theorem B2573059 : Blo 2285435 2573059 := bstep (se 1 (by rfl) ⟨1929794, by rfl⟩ : syracuseStep 2573059 = 3859589) B3859589
theorem B3430745 : Blo 2285435 3430745 := bstep (se 2 (by rfl) ⟨1286529, by rfl⟩ : syracuseStep 3430745 = 2573059) B2573059
theorem B2287163 : Blo 2285435 2287163 := bstep (se 1 (by rfl) ⟨1715372, by rfl⟩ : syracuseStep 2287163 = 3430745) B3430745
theorem B17368181 : Blo 2285435 17368181 := bbase (se 5 (by rfl) ⟨814133, by rfl⟩ : syracuseStep 17368181 = 1628267) (by norm_num)
theorem B11578787 : Blo 2285435 11578787 := bstep (se 1 (by rfl) ⟨8684090, by rfl⟩ : syracuseStep 11578787 = 17368181) B17368181
theorem B7719191 : Blo 2285435 7719191 := bstep (se 1 (by rfl) ⟨5789393, by rfl⟩ : syracuseStep 7719191 = 11578787) B11578787
theorem B5146127 : Blo 2285435 5146127 := bstep (se 1 (by rfl) ⟨3859595, by rfl⟩ : syracuseStep 5146127 = 7719191) B7719191
theorem B3430751 : Blo 2285435 3430751 := bstep (se 1 (by rfl) ⟨2573063, by rfl⟩ : syracuseStep 3430751 = 5146127) B5146127
theorem B2287167 : Blo 2285435 2287167 := bstep (se 1 (by rfl) ⟨1715375, by rfl⟩ : syracuseStep 2287167 = 3430751) B3430751
theorem B3430757 : Blo 2285435 3430757 := bbase (se 4 (by rfl) ⟨321633, by rfl⟩ : syracuseStep 3430757 = 643267) (by norm_num)
theorem B2287171 : Blo 2285435 2287171 := bstep (se 1 (by rfl) ⟨1715378, by rfl⟩ : syracuseStep 2287171 = 3430757) B3430757
theorem B4342061 : Blo 2285435 4342061 := bbase (se 3 (by rfl) ⟨814136, by rfl⟩ : syracuseStep 4342061 = 1628273) (by norm_num)
theorem B2894707 : Blo 2285435 2894707 := bstep (se 1 (by rfl) ⟨2171030, by rfl⟩ : syracuseStep 2894707 = 4342061) B4342061
theorem B3859609 : Blo 2285435 3859609 := bstep (se 2 (by rfl) ⟨1447353, by rfl⟩ : syracuseStep 3859609 = 2894707) B2894707
theorem B5146145 : Blo 2285435 5146145 := bstep (se 2 (by rfl) ⟨1929804, by rfl⟩ : syracuseStep 5146145 = 3859609) B3859609
theorem B3430763 : Blo 2285435 3430763 := bstep (se 1 (by rfl) ⟨2573072, by rfl⟩ : syracuseStep 3430763 = 5146145) B5146145
theorem B2287175 : Blo 2285435 2287175 := bstep (se 1 (by rfl) ⟨1715381, by rfl⟩ : syracuseStep 2287175 = 3430763) B3430763
theorem B2573077 : Blo 2285435 2573077 := bbase (se 6 (by rfl) ⟨60306, by rfl⟩ : syracuseStep 2573077 = 120613) (by norm_num)
theorem B3430769 : Blo 2285435 3430769 := bstep (se 2 (by rfl) ⟨1286538, by rfl⟩ : syracuseStep 3430769 = 2573077) B2573077
theorem B2287179 : Blo 2285435 2287179 := bstep (se 1 (by rfl) ⟨1715384, by rfl⟩ : syracuseStep 2287179 = 3430769) B3430769
theorem B2894717 : Blo 2285435 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B7719245 : Blo 2285435 7719245 := bstep (se 3 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 7719245 = 2894717) B2894717
theorem B5146163 : Blo 2285435 5146163 := bstep (se 1 (by rfl) ⟨3859622, by rfl⟩ : syracuseStep 5146163 = 7719245) B7719245
theorem B3430775 : Blo 2285435 3430775 := bstep (se 1 (by rfl) ⟨2573081, by rfl⟩ : syracuseStep 3430775 = 5146163) B5146163
theorem B2287183 : Blo 2285435 2287183 := bstep (se 1 (by rfl) ⟨1715387, by rfl⟩ : syracuseStep 2287183 = 3430775) B3430775
theorem B3430781 : Blo 2285435 3430781 := bbase (se 3 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 3430781 = 1286543) (by norm_num)
theorem B2287187 : Blo 2285435 2287187 := bstep (se 1 (by rfl) ⟨1715390, by rfl⟩ : syracuseStep 2287187 = 3430781) B3430781
theorem B5146181 : Blo 2285435 5146181 := bbase (se 4 (by rfl) ⟨482454, by rfl⟩ : syracuseStep 5146181 = 964909) (by norm_num)
theorem B3430787 : Blo 2285435 3430787 := bstep (se 1 (by rfl) ⟨2573090, by rfl⟩ : syracuseStep 3430787 = 5146181) B5146181
theorem B2287191 : Blo 2285435 2287191 := bstep (se 1 (by rfl) ⟨1715393, by rfl⟩ : syracuseStep 2287191 = 3430787) B3430787
theorem B5216405 : Blo 2285435 5216405 := bbase (se 6 (by rfl) ⟨122259, by rfl⟩ : syracuseStep 5216405 = 244519) (by norm_num)
theorem B13910413 : Blo 2285435 13910413 := bstep (se 3 (by rfl) ⟨2608202, by rfl⟩ : syracuseStep 13910413 = 5216405) B5216405
theorem B18547217 : Blo 2285435 18547217 := bstep (se 2 (by rfl) ⟨6955206, by rfl⟩ : syracuseStep 18547217 = 13910413) B13910413
theorem B12364811 : Blo 2285435 12364811 := bstep (se 1 (by rfl) ⟨9273608, by rfl⟩ : syracuseStep 12364811 = 18547217) B18547217
theorem B8243207 : Blo 2285435 8243207 := bstep (se 1 (by rfl) ⟨6182405, by rfl⟩ : syracuseStep 8243207 = 12364811) B12364811
theorem B5495471 : Blo 2285435 5495471 := bstep (se 1 (by rfl) ⟨4121603, by rfl⟩ : syracuseStep 5495471 = 8243207) B8243207
theorem B3663647 : Blo 2285435 3663647 := bstep (se 1 (by rfl) ⟨2747735, by rfl⟩ : syracuseStep 3663647 = 5495471) B5495471
theorem B2442431 : Blo 2285435 2442431 := bstep (se 1 (by rfl) ⟨1831823, by rfl⟩ : syracuseStep 2442431 = 3663647) B3663647
theorem B6513149 : Blo 2285435 6513149 := bstep (se 3 (by rfl) ⟨1221215, by rfl⟩ : syracuseStep 6513149 = 2442431) B2442431
theorem B4342099 : Blo 2285435 4342099 := bstep (se 1 (by rfl) ⟨3256574, by rfl⟩ : syracuseStep 4342099 = 6513149) B6513149
theorem B5789465 : Blo 2285435 5789465 := bstep (se 2 (by rfl) ⟨2171049, by rfl⟩ : syracuseStep 5789465 = 4342099) B4342099
theorem B3859643 : Blo 2285435 3859643 := bstep (se 1 (by rfl) ⟨2894732, by rfl⟩ : syracuseStep 3859643 = 5789465) B5789465
theorem B2573095 : Blo 2285435 2573095 := bstep (se 1 (by rfl) ⟨1929821, by rfl⟩ : syracuseStep 2573095 = 3859643) B3859643
theorem B3430793 : Blo 2285435 3430793 := bstep (se 2 (by rfl) ⟨1286547, by rfl⟩ : syracuseStep 3430793 = 2573095) B2573095
theorem B2287195 : Blo 2285435 2287195 := bstep (se 1 (by rfl) ⟨1715396, by rfl⟩ : syracuseStep 2287195 = 3430793) B3430793
theorem B11578949 : Blo 2285435 11578949 := bbase (se 4 (by rfl) ⟨1085526, by rfl⟩ : syracuseStep 11578949 = 2171053) (by norm_num)
theorem B7719299 : Blo 2285435 7719299 := bstep (se 1 (by rfl) ⟨5789474, by rfl⟩ : syracuseStep 7719299 = 11578949) B11578949
theorem B5146199 : Blo 2285435 5146199 := bstep (se 1 (by rfl) ⟨3859649, by rfl⟩ : syracuseStep 5146199 = 7719299) B7719299
theorem B3430799 : Blo 2285435 3430799 := bstep (se 1 (by rfl) ⟨2573099, by rfl⟩ : syracuseStep 3430799 = 5146199) B5146199
theorem B2287199 : Blo 2285435 2287199 := bstep (se 1 (by rfl) ⟨1715399, by rfl⟩ : syracuseStep 2287199 = 3430799) B3430799
theorem B3430805 : Blo 2285435 3430805 := bbase (se 6 (by rfl) ⟨80409, by rfl⟩ : syracuseStep 3430805 = 160819) (by norm_num)
theorem B2287203 : Blo 2285435 2287203 := bstep (se 1 (by rfl) ⟨1715402, by rfl⟩ : syracuseStep 2287203 = 3430805) B3430805
theorem B10990997 : Blo 2285435 10990997 := bbase (se 6 (by rfl) ⟨257601, by rfl⟩ : syracuseStep 10990997 = 515203) (by norm_num)
theorem B7327331 : Blo 2285435 7327331 := bstep (se 1 (by rfl) ⟨5495498, by rfl⟩ : syracuseStep 7327331 = 10990997) B10990997
theorem B4884887 : Blo 2285435 4884887 := bstep (se 1 (by rfl) ⟨3663665, by rfl⟩ : syracuseStep 4884887 = 7327331) B7327331
theorem B13026365 : Blo 2285435 13026365 := bstep (se 3 (by rfl) ⟨2442443, by rfl⟩ : syracuseStep 13026365 = 4884887) B4884887
theorem B8684243 : Blo 2285435 8684243 := bstep (se 1 (by rfl) ⟨6513182, by rfl⟩ : syracuseStep 8684243 = 13026365) B13026365
theorem B5789495 : Blo 2285435 5789495 := bstep (se 1 (by rfl) ⟨4342121, by rfl⟩ : syracuseStep 5789495 = 8684243) B8684243
theorem B3859663 : Blo 2285435 3859663 := bstep (se 1 (by rfl) ⟨2894747, by rfl⟩ : syracuseStep 3859663 = 5789495) B5789495
theorem B5146217 : Blo 2285435 5146217 := bstep (se 2 (by rfl) ⟨1929831, by rfl⟩ : syracuseStep 5146217 = 3859663) B3859663
theorem B3430811 : Blo 2285435 3430811 := bstep (se 1 (by rfl) ⟨2573108, by rfl⟩ : syracuseStep 3430811 = 5146217) B5146217
theorem B2287207 : Blo 2285435 2287207 := bstep (se 1 (by rfl) ⟨1715405, by rfl⟩ : syracuseStep 2287207 = 3430811) B3430811
theorem B2573113 : Blo 2285435 2573113 := bbase (se 2 (by rfl) ⟨964917, by rfl⟩ : syracuseStep 2573113 = 1929835) (by norm_num)
theorem B3430817 : Blo 2285435 3430817 := bstep (se 2 (by rfl) ⟨1286556, by rfl⟩ : syracuseStep 3430817 = 2573113) B2573113
theorem B2287211 : Blo 2285435 2287211 := bstep (se 1 (by rfl) ⟨1715408, by rfl⟩ : syracuseStep 2287211 = 3430817) B3430817
theorem B6513205 : Blo 2285435 6513205 := bbase (se 5 (by rfl) ⟨305306, by rfl⟩ : syracuseStep 6513205 = 610613) (by norm_num)
theorem B8684273 : Blo 2285435 8684273 := bstep (se 2 (by rfl) ⟨3256602, by rfl⟩ : syracuseStep 8684273 = 6513205) B6513205
theorem B5789515 : Blo 2285435 5789515 := bstep (se 1 (by rfl) ⟨4342136, by rfl⟩ : syracuseStep 5789515 = 8684273) B8684273
theorem B7719353 : Blo 2285435 7719353 := bstep (se 2 (by rfl) ⟨2894757, by rfl⟩ : syracuseStep 7719353 = 5789515) B5789515
theorem B5146235 : Blo 2285435 5146235 := bstep (se 1 (by rfl) ⟨3859676, by rfl⟩ : syracuseStep 5146235 = 7719353) B7719353
theorem B3430823 : Blo 2285435 3430823 := bstep (se 1 (by rfl) ⟨2573117, by rfl⟩ : syracuseStep 3430823 = 5146235) B5146235
theorem B2287215 : Blo 2285435 2287215 := bstep (se 1 (by rfl) ⟨1715411, by rfl⟩ : syracuseStep 2287215 = 3430823) B3430823
theorem B3430829 : Blo 2285435 3430829 := bbase (se 3 (by rfl) ⟨643280, by rfl⟩ : syracuseStep 3430829 = 1286561) (by norm_num)
theorem B2287219 : Blo 2285435 2287219 := bstep (se 1 (by rfl) ⟨1715414, by rfl⟩ : syracuseStep 2287219 = 3430829) B3430829
theorem B5146253 : Blo 2285435 5146253 := bbase (se 3 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 5146253 = 1929845) (by norm_num)
theorem B3430835 : Blo 2285435 3430835 := bstep (se 1 (by rfl) ⟨2573126, by rfl⟩ : syracuseStep 3430835 = 5146253) B5146253
theorem B2287223 : Blo 2285435 2287223 := bstep (se 1 (by rfl) ⟨1715417, by rfl⟩ : syracuseStep 2287223 = 3430835) B3430835
theorem B2894773 : Blo 2285435 2894773 := bbase (se 5 (by rfl) ⟨135692, by rfl⟩ : syracuseStep 2894773 = 271385) (by norm_num)
theorem B3859697 : Blo 2285435 3859697 := bstep (se 2 (by rfl) ⟨1447386, by rfl⟩ : syracuseStep 3859697 = 2894773) B2894773
theorem B2573131 : Blo 2285435 2573131 := bstep (se 1 (by rfl) ⟨1929848, by rfl⟩ : syracuseStep 2573131 = 3859697) B3859697
theorem B3430841 : Blo 2285435 3430841 := bstep (se 2 (by rfl) ⟨1286565, by rfl⟩ : syracuseStep 3430841 = 2573131) B2573131
theorem B2287227 : Blo 2285435 2287227 := bstep (se 1 (by rfl) ⟨1715420, by rfl⟩ : syracuseStep 2287227 = 3430841) B3430841
theorem B2475793 : Blo 2285435 2475793 := bbase (se 2 (by rfl) ⟨928422, by rfl⟩ : syracuseStep 2475793 = 1856845) (by norm_num)
theorem B3301057 : Blo 2285435 3301057 := bstep (se 2 (by rfl) ⟨1237896, by rfl⟩ : syracuseStep 3301057 = 2475793) B2475793
theorem B4401409 : Blo 2285435 4401409 := bstep (se 2 (by rfl) ⟨1650528, by rfl⟩ : syracuseStep 4401409 = 3301057) B3301057
theorem B5868545 : Blo 2285435 5868545 := bstep (se 2 (by rfl) ⟨2200704, by rfl⟩ : syracuseStep 5868545 = 4401409) B4401409
theorem B15649453 : Blo 2285435 15649453 := bstep (se 3 (by rfl) ⟨2934272, by rfl⟩ : syracuseStep 15649453 = 5868545) B5868545
theorem B20865937 : Blo 2285435 20865937 := bstep (se 2 (by rfl) ⟨7824726, by rfl⟩ : syracuseStep 20865937 = 15649453) B15649453
theorem B27821249 : Blo 2285435 27821249 := bstep (se 2 (by rfl) ⟨10432968, by rfl⟩ : syracuseStep 27821249 = 20865937) B20865937
theorem B18547499 : Blo 2285435 18547499 := bstep (se 1 (by rfl) ⟨13910624, by rfl⟩ : syracuseStep 18547499 = 27821249) B27821249
theorem B49459997 : Blo 2285435 49459997 := bstep (se 3 (by rfl) ⟨9273749, by rfl⟩ : syracuseStep 49459997 = 18547499) B18547499
theorem B32973331 : Blo 2285435 32973331 := bstep (se 1 (by rfl) ⟨24729998, by rfl⟩ : syracuseStep 32973331 = 49459997) B49459997
theorem B43964441 : Blo 2285435 43964441 := bstep (se 2 (by rfl) ⟨16486665, by rfl⟩ : syracuseStep 43964441 = 32973331) B32973331
theorem B29309627 : Blo 2285435 29309627 := bstep (se 1 (by rfl) ⟨21982220, by rfl⟩ : syracuseStep 29309627 = 43964441) B43964441
theorem B19539751 : Blo 2285435 19539751 := bstep (se 1 (by rfl) ⟨14654813, by rfl⟩ : syracuseStep 19539751 = 29309627) B29309627
theorem B26053001 : Blo 2285435 26053001 := bstep (se 2 (by rfl) ⟨9769875, by rfl⟩ : syracuseStep 26053001 = 19539751) B19539751
theorem B17368667 : Blo 2285435 17368667 := bstep (se 1 (by rfl) ⟨13026500, by rfl⟩ : syracuseStep 17368667 = 26053001) B26053001
theorem B11579111 : Blo 2285435 11579111 := bstep (se 1 (by rfl) ⟨8684333, by rfl⟩ : syracuseStep 11579111 = 17368667) B17368667
theorem B7719407 : Blo 2285435 7719407 := bstep (se 1 (by rfl) ⟨5789555, by rfl⟩ : syracuseStep 7719407 = 11579111) B11579111
theorem B5146271 : Blo 2285435 5146271 := bstep (se 1 (by rfl) ⟨3859703, by rfl⟩ : syracuseStep 5146271 = 7719407) B7719407
theorem B3430847 : Blo 2285435 3430847 := bstep (se 1 (by rfl) ⟨2573135, by rfl⟩ : syracuseStep 3430847 = 5146271) B5146271
theorem B2287231 : Blo 2285435 2287231 := bstep (se 1 (by rfl) ⟨1715423, by rfl⟩ : syracuseStep 2287231 = 3430847) B3430847
theorem B3430853 : Blo 2285435 3430853 := bbase (se 4 (by rfl) ⟨321642, by rfl⟩ : syracuseStep 3430853 = 643285) (by norm_num)
theorem B2287235 : Blo 2285435 2287235 := bstep (se 1 (by rfl) ⟨1715426, by rfl⟩ : syracuseStep 2287235 = 3430853) B3430853
theorem B3859717 : Blo 2285435 3859717 := bbase (se 4 (by rfl) ⟨361848, by rfl⟩ : syracuseStep 3859717 = 723697) (by norm_num)
theorem B5146289 : Blo 2285435 5146289 := bstep (se 2 (by rfl) ⟨1929858, by rfl⟩ : syracuseStep 5146289 = 3859717) B3859717
theorem B3430859 : Blo 2285435 3430859 := bstep (se 1 (by rfl) ⟨2573144, by rfl⟩ : syracuseStep 3430859 = 5146289) B5146289
theorem B2287239 : Blo 2285435 2287239 := bstep (se 1 (by rfl) ⟨1715429, by rfl⟩ : syracuseStep 2287239 = 3430859) B3430859
theorem B2573149 : Blo 2285435 2573149 := bbase (se 3 (by rfl) ⟨482465, by rfl⟩ : syracuseStep 2573149 = 964931) (by norm_num)
theorem B3430865 : Blo 2285435 3430865 := bstep (se 2 (by rfl) ⟨1286574, by rfl⟩ : syracuseStep 3430865 = 2573149) B2573149
theorem B2287243 : Blo 2285435 2287243 := bstep (se 1 (by rfl) ⟨1715432, by rfl⟩ : syracuseStep 2287243 = 3430865) B3430865
theorem B7719461 : Blo 2285435 7719461 := bbase (se 4 (by rfl) ⟨723699, by rfl⟩ : syracuseStep 7719461 = 1447399) (by norm_num)
theorem B5146307 : Blo 2285435 5146307 := bstep (se 1 (by rfl) ⟨3859730, by rfl⟩ : syracuseStep 5146307 = 7719461) B7719461
theorem B3430871 : Blo 2285435 3430871 := bstep (se 1 (by rfl) ⟨2573153, by rfl⟩ : syracuseStep 3430871 = 5146307) B5146307
theorem B2287247 : Blo 2285435 2287247 := bstep (se 1 (by rfl) ⟨1715435, by rfl⟩ : syracuseStep 2287247 = 3430871) B3430871
theorem B3430877 : Blo 2285435 3430877 := bbase (se 3 (by rfl) ⟨643289, by rfl⟩ : syracuseStep 3430877 = 1286579) (by norm_num)
theorem B2287251 : Blo 2285435 2287251 := bstep (se 1 (by rfl) ⟨1715438, by rfl⟩ : syracuseStep 2287251 = 3430877) B3430877
theorem B5146325 : Blo 2285435 5146325 := bbase (se 7 (by rfl) ⟨60308, by rfl⟩ : syracuseStep 5146325 = 120617) (by norm_num)
theorem B3430883 : Blo 2285435 3430883 := bstep (se 1 (by rfl) ⟨2573162, by rfl⟩ : syracuseStep 3430883 = 5146325) B5146325
theorem B2287255 : Blo 2285435 2287255 := bstep (se 1 (by rfl) ⟨1715441, by rfl⟩ : syracuseStep 2287255 = 3430883) B3430883
theorem B3663749 : Blo 2285435 3663749 := bbase (se 4 (by rfl) ⟨343476, by rfl⟩ : syracuseStep 3663749 = 686953) (by norm_num)
theorem B9769997 : Blo 2285435 9769997 := bstep (se 3 (by rfl) ⟨1831874, by rfl⟩ : syracuseStep 9769997 = 3663749) B3663749
theorem B6513331 : Blo 2285435 6513331 := bstep (se 1 (by rfl) ⟨4884998, by rfl⟩ : syracuseStep 6513331 = 9769997) B9769997
theorem B8684441 : Blo 2285435 8684441 := bstep (se 2 (by rfl) ⟨3256665, by rfl⟩ : syracuseStep 8684441 = 6513331) B6513331
theorem B5789627 : Blo 2285435 5789627 := bstep (se 1 (by rfl) ⟨4342220, by rfl⟩ : syracuseStep 5789627 = 8684441) B8684441
theorem B3859751 : Blo 2285435 3859751 := bstep (se 1 (by rfl) ⟨2894813, by rfl⟩ : syracuseStep 3859751 = 5789627) B5789627
theorem B2573167 : Blo 2285435 2573167 := bstep (se 1 (by rfl) ⟨1929875, by rfl⟩ : syracuseStep 2573167 = 3859751) B3859751
theorem B3430889 : Blo 2285435 3430889 := bstep (se 2 (by rfl) ⟨1286583, by rfl⟩ : syracuseStep 3430889 = 2573167) B2573167
theorem B2287259 : Blo 2285435 2287259 := bstep (se 1 (by rfl) ⟨1715444, by rfl⟩ : syracuseStep 2287259 = 3430889) B3430889
theorem B12365173 : Blo 2285435 12365173 := bbase (se 5 (by rfl) ⟨579617, by rfl⟩ : syracuseStep 12365173 = 1159235) (by norm_num)
theorem B16486897 : Blo 2285435 16486897 := bstep (se 2 (by rfl) ⟨6182586, by rfl⟩ : syracuseStep 16486897 = 12365173) B12365173
theorem B21982529 : Blo 2285435 21982529 := bstep (se 2 (by rfl) ⟨8243448, by rfl⟩ : syracuseStep 21982529 = 16486897) B16486897
theorem B14655019 : Blo 2285435 14655019 := bstep (se 1 (by rfl) ⟨10991264, by rfl⟩ : syracuseStep 14655019 = 21982529) B21982529
theorem B19540025 : Blo 2285435 19540025 := bstep (se 2 (by rfl) ⟨7327509, by rfl⟩ : syracuseStep 19540025 = 14655019) B14655019
theorem B13026683 : Blo 2285435 13026683 := bstep (se 1 (by rfl) ⟨9770012, by rfl⟩ : syracuseStep 13026683 = 19540025) B19540025
theorem B8684455 : Blo 2285435 8684455 := bstep (se 1 (by rfl) ⟨6513341, by rfl⟩ : syracuseStep 8684455 = 13026683) B13026683
theorem B11579273 : Blo 2285435 11579273 := bstep (se 2 (by rfl) ⟨4342227, by rfl⟩ : syracuseStep 11579273 = 8684455) B8684455
theorem B7719515 : Blo 2285435 7719515 := bstep (se 1 (by rfl) ⟨5789636, by rfl⟩ : syracuseStep 7719515 = 11579273) B11579273
theorem B5146343 : Blo 2285435 5146343 := bstep (se 1 (by rfl) ⟨3859757, by rfl⟩ : syracuseStep 5146343 = 7719515) B7719515
theorem B3430895 : Blo 2285435 3430895 := bstep (se 1 (by rfl) ⟨2573171, by rfl⟩ : syracuseStep 3430895 = 5146343) B5146343
theorem B2287263 : Blo 2285435 2287263 := bstep (se 1 (by rfl) ⟨1715447, by rfl⟩ : syracuseStep 2287263 = 3430895) B3430895
theorem B3430901 : Blo 2285435 3430901 := bbase (se 5 (by rfl) ⟨160823, by rfl⟩ : syracuseStep 3430901 = 321647) (by norm_num)
theorem B2287267 : Blo 2285435 2287267 := bstep (se 1 (by rfl) ⟨1715450, by rfl⟩ : syracuseStep 2287267 = 3430901) B3430901
theorem B6513365 : Blo 2285435 6513365 := bbase (se 7 (by rfl) ⟨76328, by rfl⟩ : syracuseStep 6513365 = 152657) (by norm_num)
theorem B4342243 : Blo 2285435 4342243 := bstep (se 1 (by rfl) ⟨3256682, by rfl⟩ : syracuseStep 4342243 = 6513365) B6513365
theorem B5789657 : Blo 2285435 5789657 := bstep (se 2 (by rfl) ⟨2171121, by rfl⟩ : syracuseStep 5789657 = 4342243) B4342243
theorem B3859771 : Blo 2285435 3859771 := bstep (se 1 (by rfl) ⟨2894828, by rfl⟩ : syracuseStep 3859771 = 5789657) B5789657
theorem B5146361 : Blo 2285435 5146361 := bstep (se 2 (by rfl) ⟨1929885, by rfl⟩ : syracuseStep 5146361 = 3859771) B3859771
theorem B3430907 : Blo 2285435 3430907 := bstep (se 1 (by rfl) ⟨2573180, by rfl⟩ : syracuseStep 3430907 = 5146361) B5146361
theorem B2287271 : Blo 2285435 2287271 := bstep (se 1 (by rfl) ⟨1715453, by rfl⟩ : syracuseStep 2287271 = 3430907) B3430907
theorem B2573185 : Blo 2285435 2573185 := bbase (se 2 (by rfl) ⟨964944, by rfl⟩ : syracuseStep 2573185 = 1929889) (by norm_num)
theorem B3430913 : Blo 2285435 3430913 := bstep (se 2 (by rfl) ⟨1286592, by rfl⟩ : syracuseStep 3430913 = 2573185) B2573185
theorem B2287275 : Blo 2285435 2287275 := bstep (se 1 (by rfl) ⟨1715456, by rfl⟩ : syracuseStep 2287275 = 3430913) B3430913
theorem B5789677 : Blo 2285435 5789677 := bbase (se 3 (by rfl) ⟨1085564, by rfl⟩ : syracuseStep 5789677 = 2171129) (by norm_num)
theorem B7719569 : Blo 2285435 7719569 := bstep (se 2 (by rfl) ⟨2894838, by rfl⟩ : syracuseStep 7719569 = 5789677) B5789677
theorem B5146379 : Blo 2285435 5146379 := bstep (se 1 (by rfl) ⟨3859784, by rfl⟩ : syracuseStep 5146379 = 7719569) B7719569
theorem B3430919 : Blo 2285435 3430919 := bstep (se 1 (by rfl) ⟨2573189, by rfl⟩ : syracuseStep 3430919 = 5146379) B5146379
theorem B2287279 : Blo 2285435 2287279 := bstep (se 1 (by rfl) ⟨1715459, by rfl⟩ : syracuseStep 2287279 = 3430919) B3430919
theorem B3430925 : Blo 2285435 3430925 := bbase (se 3 (by rfl) ⟨643298, by rfl⟩ : syracuseStep 3430925 = 1286597) (by norm_num)
theorem B2287283 : Blo 2285435 2287283 := bstep (se 1 (by rfl) ⟨1715462, by rfl⟩ : syracuseStep 2287283 = 3430925) B3430925
theorem B5146397 : Blo 2285435 5146397 := bbase (se 3 (by rfl) ⟨964949, by rfl⟩ : syracuseStep 5146397 = 1929899) (by norm_num)
theorem B3430931 : Blo 2285435 3430931 := bstep (se 1 (by rfl) ⟨2573198, by rfl⟩ : syracuseStep 3430931 = 5146397) B5146397
theorem B2287287 : Blo 2285435 2287287 := bstep (se 1 (by rfl) ⟨1715465, by rfl⟩ : syracuseStep 2287287 = 3430931) B3430931
theorem B3859805 : Blo 2285435 3859805 := bbase (se 3 (by rfl) ⟨723713, by rfl⟩ : syracuseStep 3859805 = 1447427) (by norm_num)
theorem B2573203 : Blo 2285435 2573203 := bstep (se 1 (by rfl) ⟨1929902, by rfl⟩ : syracuseStep 2573203 = 3859805) B3859805
theorem B3430937 : Blo 2285435 3430937 := bstep (se 2 (by rfl) ⟨1286601, by rfl⟩ : syracuseStep 3430937 = 2573203) B2573203
theorem B2287291 : Blo 2285435 2287291 := bstep (se 1 (by rfl) ⟨1715468, by rfl⟩ : syracuseStep 2287291 = 3430937) B3430937
theorem B9770149 : Blo 2285435 9770149 := bbase (se 4 (by rfl) ⟨915951, by rfl⟩ : syracuseStep 9770149 = 1831903) (by norm_num)
theorem B13026865 : Blo 2285435 13026865 := bstep (se 2 (by rfl) ⟨4885074, by rfl⟩ : syracuseStep 13026865 = 9770149) B9770149
theorem B17369153 : Blo 2285435 17369153 := bstep (se 2 (by rfl) ⟨6513432, by rfl⟩ : syracuseStep 17369153 = 13026865) B13026865
theorem B11579435 : Blo 2285435 11579435 := bstep (se 1 (by rfl) ⟨8684576, by rfl⟩ : syracuseStep 11579435 = 17369153) B17369153
theorem B7719623 : Blo 2285435 7719623 := bstep (se 1 (by rfl) ⟨5789717, by rfl⟩ : syracuseStep 7719623 = 11579435) B11579435
theorem B5146415 : Blo 2285435 5146415 := bstep (se 1 (by rfl) ⟨3859811, by rfl⟩ : syracuseStep 5146415 = 7719623) B7719623
theorem B3430943 : Blo 2285435 3430943 := bstep (se 1 (by rfl) ⟨2573207, by rfl⟩ : syracuseStep 3430943 = 5146415) B5146415
theorem B2287295 : Blo 2285435 2287295 := bstep (se 1 (by rfl) ⟨1715471, by rfl⟩ : syracuseStep 2287295 = 3430943) B3430943
theorem B3430949 : Blo 2285435 3430949 := bbase (se 4 (by rfl) ⟨321651, by rfl⟩ : syracuseStep 3430949 = 643303) (by norm_num)
theorem B2287299 : Blo 2285435 2287299 := bstep (se 1 (by rfl) ⟨1715474, by rfl⟩ : syracuseStep 2287299 = 3430949) B3430949
theorem B2894869 : Blo 2285435 2894869 := bbase (se 6 (by rfl) ⟨67848, by rfl⟩ : syracuseStep 2894869 = 135697) (by norm_num)
theorem B3859825 : Blo 2285435 3859825 := bstep (se 2 (by rfl) ⟨1447434, by rfl⟩ : syracuseStep 3859825 = 2894869) B2894869
theorem B5146433 : Blo 2285435 5146433 := bstep (se 2 (by rfl) ⟨1929912, by rfl⟩ : syracuseStep 5146433 = 3859825) B3859825
theorem B3430955 : Blo 2285435 3430955 := bstep (se 1 (by rfl) ⟨2573216, by rfl⟩ : syracuseStep 3430955 = 5146433) B5146433
theorem B2287303 : Blo 2285435 2287303 := bstep (se 1 (by rfl) ⟨1715477, by rfl⟩ : syracuseStep 2287303 = 3430955) B3430955
theorem B2573221 : Blo 2285435 2573221 := bbase (se 4 (by rfl) ⟨241239, by rfl⟩ : syracuseStep 2573221 = 482479) (by norm_num)
theorem B3430961 : Blo 2285435 3430961 := bstep (se 2 (by rfl) ⟨1286610, by rfl⟩ : syracuseStep 3430961 = 2573221) B2573221
theorem B2287307 : Blo 2285435 2287307 := bstep (se 1 (by rfl) ⟨1715480, by rfl⟩ : syracuseStep 2287307 = 3430961) B3430961
theorem B15650005 : Blo 2285435 15650005 := bbase (se 7 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 15650005 = 366797) (by norm_num)
theorem B20866673 : Blo 2285435 20866673 := bstep (se 2 (by rfl) ⟨7825002, by rfl⟩ : syracuseStep 20866673 = 15650005) B15650005
theorem B13911115 : Blo 2285435 13911115 := bstep (se 1 (by rfl) ⟨10433336, by rfl⟩ : syracuseStep 13911115 = 20866673) B20866673
theorem B18548153 : Blo 2285435 18548153 := bstep (se 2 (by rfl) ⟨6955557, by rfl⟩ : syracuseStep 18548153 = 13911115) B13911115
theorem B12365435 : Blo 2285435 12365435 := bstep (se 1 (by rfl) ⟨9274076, by rfl⟩ : syracuseStep 12365435 = 18548153) B18548153
theorem B8243623 : Blo 2285435 8243623 := bstep (se 1 (by rfl) ⟨6182717, by rfl⟩ : syracuseStep 8243623 = 12365435) B12365435
theorem B10991497 : Blo 2285435 10991497 := bstep (se 2 (by rfl) ⟨4121811, by rfl⟩ : syracuseStep 10991497 = 8243623) B8243623
theorem B14655329 : Blo 2285435 14655329 := bstep (se 2 (by rfl) ⟨5495748, by rfl⟩ : syracuseStep 14655329 = 10991497) B10991497
theorem B9770219 : Blo 2285435 9770219 := bstep (se 1 (by rfl) ⟨7327664, by rfl⟩ : syracuseStep 9770219 = 14655329) B14655329
theorem B6513479 : Blo 2285435 6513479 := bstep (se 1 (by rfl) ⟨4885109, by rfl⟩ : syracuseStep 6513479 = 9770219) B9770219
theorem B4342319 : Blo 2285435 4342319 := bstep (se 1 (by rfl) ⟨3256739, by rfl⟩ : syracuseStep 4342319 = 6513479) B6513479
theorem B2894879 : Blo 2285435 2894879 := bstep (se 1 (by rfl) ⟨2171159, by rfl⟩ : syracuseStep 2894879 = 4342319) B4342319
theorem B7719677 : Blo 2285435 7719677 := bstep (se 3 (by rfl) ⟨1447439, by rfl⟩ : syracuseStep 7719677 = 2894879) B2894879
theorem B5146451 : Blo 2285435 5146451 := bstep (se 1 (by rfl) ⟨3859838, by rfl⟩ : syracuseStep 5146451 = 7719677) B7719677
theorem B3430967 : Blo 2285435 3430967 := bstep (se 1 (by rfl) ⟨2573225, by rfl⟩ : syracuseStep 3430967 = 5146451) B5146451
theorem B2287311 : Blo 2285435 2287311 := bstep (se 1 (by rfl) ⟨1715483, by rfl⟩ : syracuseStep 2287311 = 3430967) B3430967
theorem B3430973 : Blo 2285435 3430973 := bbase (se 3 (by rfl) ⟨643307, by rfl⟩ : syracuseStep 3430973 = 1286615) (by norm_num)
theorem B2287315 : Blo 2285435 2287315 := bstep (se 1 (by rfl) ⟨1715486, by rfl⟩ : syracuseStep 2287315 = 3430973) B3430973
theorem B5146469 : Blo 2285435 5146469 := bbase (se 4 (by rfl) ⟨482481, by rfl⟩ : syracuseStep 5146469 = 964963) (by norm_num)
theorem B3430979 : Blo 2285435 3430979 := bstep (se 1 (by rfl) ⟨2573234, by rfl⟩ : syracuseStep 3430979 = 5146469) B5146469
theorem B2287319 : Blo 2285435 2287319 := bstep (se 1 (by rfl) ⟨1715489, by rfl⟩ : syracuseStep 2287319 = 3430979) B3430979
theorem B5789789 : Blo 2285435 5789789 := bbase (se 3 (by rfl) ⟨1085585, by rfl⟩ : syracuseStep 5789789 = 2171171) (by norm_num)
theorem B3859859 : Blo 2285435 3859859 := bstep (se 1 (by rfl) ⟨2894894, by rfl⟩ : syracuseStep 3859859 = 5789789) B5789789
theorem B2573239 : Blo 2285435 2573239 := bstep (se 1 (by rfl) ⟨1929929, by rfl⟩ : syracuseStep 2573239 = 3859859) B3859859
theorem B3430985 : Blo 2285435 3430985 := bstep (se 2 (by rfl) ⟨1286619, by rfl⟩ : syracuseStep 3430985 = 2573239) B2573239
theorem B2287323 : Blo 2285435 2287323 := bstep (se 1 (by rfl) ⟨1715492, by rfl⟩ : syracuseStep 2287323 = 3430985) B3430985
theorem B4342349 : Blo 2285435 4342349 := bbase (se 3 (by rfl) ⟨814190, by rfl⟩ : syracuseStep 4342349 = 1628381) (by norm_num)
theorem B11579597 : Blo 2285435 11579597 := bstep (se 3 (by rfl) ⟨2171174, by rfl⟩ : syracuseStep 11579597 = 4342349) B4342349
theorem B7719731 : Blo 2285435 7719731 := bstep (se 1 (by rfl) ⟨5789798, by rfl⟩ : syracuseStep 7719731 = 11579597) B11579597
theorem B5146487 : Blo 2285435 5146487 := bstep (se 1 (by rfl) ⟨3859865, by rfl⟩ : syracuseStep 5146487 = 7719731) B7719731
theorem B3430991 : Blo 2285435 3430991 := bstep (se 1 (by rfl) ⟨2573243, by rfl⟩ : syracuseStep 3430991 = 5146487) B5146487
theorem B2287327 : Blo 2285435 2287327 := bstep (se 1 (by rfl) ⟨1715495, by rfl⟩ : syracuseStep 2287327 = 3430991) B3430991
theorem B3430997 : Blo 2285435 3430997 := bbase (se 8 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 3430997 = 40207) (by norm_num)
theorem B2287331 : Blo 2285435 2287331 := bstep (se 1 (by rfl) ⟨1715498, by rfl⟩ : syracuseStep 2287331 = 3430997) B3430997
theorem B5570789 : Blo 2285435 5570789 := bbase (se 4 (by rfl) ⟨522261, by rfl⟩ : syracuseStep 5570789 = 1044523) (by norm_num)
theorem B14855437 : Blo 2285435 14855437 := bstep (se 3 (by rfl) ⟨2785394, by rfl⟩ : syracuseStep 14855437 = 5570789) B5570789
theorem B19807249 : Blo 2285435 19807249 := bstep (se 2 (by rfl) ⟨7427718, by rfl⟩ : syracuseStep 19807249 = 14855437) B14855437
theorem B26409665 : Blo 2285435 26409665 := bstep (se 2 (by rfl) ⟨9903624, by rfl⟩ : syracuseStep 26409665 = 19807249) B19807249
theorem B70425773 : Blo 2285435 70425773 := bstep (se 3 (by rfl) ⟨13204832, by rfl⟩ : syracuseStep 70425773 = 26409665) B26409665
theorem B46950515 : Blo 2285435 46950515 := bstep (se 1 (by rfl) ⟨35212886, by rfl⟩ : syracuseStep 46950515 = 70425773) B70425773
theorem B31300343 : Blo 2285435 31300343 := bstep (se 1 (by rfl) ⟨23475257, by rfl⟩ : syracuseStep 31300343 = 46950515) B46950515
theorem B20866895 : Blo 2285435 20866895 := bstep (se 1 (by rfl) ⟨15650171, by rfl⟩ : syracuseStep 20866895 = 31300343) B31300343
theorem B13911263 : Blo 2285435 13911263 := bstep (se 1 (by rfl) ⟨10433447, by rfl⟩ : syracuseStep 13911263 = 20866895) B20866895
theorem B9274175 : Blo 2285435 9274175 := bstep (se 1 (by rfl) ⟨6955631, by rfl⟩ : syracuseStep 9274175 = 13911263) B13911263
theorem B6182783 : Blo 2285435 6182783 := bstep (se 1 (by rfl) ⟨4637087, by rfl⟩ : syracuseStep 6182783 = 9274175) B9274175
theorem B4121855 : Blo 2285435 4121855 := bstep (se 1 (by rfl) ⟨3091391, by rfl⟩ : syracuseStep 4121855 = 6182783) B6182783
theorem B2747903 : Blo 2285435 2747903 := bstep (se 1 (by rfl) ⟨2060927, by rfl⟩ : syracuseStep 2747903 = 4121855) B4121855
theorem B7327741 : Blo 2285435 7327741 := bstep (se 3 (by rfl) ⟨1373951, by rfl⟩ : syracuseStep 7327741 = 2747903) B2747903
theorem B9770321 : Blo 2285435 9770321 := bstep (se 2 (by rfl) ⟨3663870, by rfl⟩ : syracuseStep 9770321 = 7327741) B7327741
theorem B6513547 : Blo 2285435 6513547 := bstep (se 1 (by rfl) ⟨4885160, by rfl⟩ : syracuseStep 6513547 = 9770321) B9770321
theorem B8684729 : Blo 2285435 8684729 := bstep (se 2 (by rfl) ⟨3256773, by rfl⟩ : syracuseStep 8684729 = 6513547) B6513547
theorem B5789819 : Blo 2285435 5789819 := bstep (se 1 (by rfl) ⟨4342364, by rfl⟩ : syracuseStep 5789819 = 8684729) B8684729
theorem B3859879 : Blo 2285435 3859879 := bstep (se 1 (by rfl) ⟨2894909, by rfl⟩ : syracuseStep 3859879 = 5789819) B5789819
theorem B5146505 : Blo 2285435 5146505 := bstep (se 2 (by rfl) ⟨1929939, by rfl⟩ : syracuseStep 5146505 = 3859879) B3859879
theorem B3431003 : Blo 2285435 3431003 := bstep (se 1 (by rfl) ⟨2573252, by rfl⟩ : syracuseStep 3431003 = 5146505) B5146505
theorem B2287335 : Blo 2285435 2287335 := bstep (se 1 (by rfl) ⟨1715501, by rfl⟩ : syracuseStep 2287335 = 3431003) B3431003
theorem B2573257 : Blo 2285435 2573257 := bbase (se 2 (by rfl) ⟨964971, by rfl⟩ : syracuseStep 2573257 = 1929943) (by norm_num)
theorem B3431009 : Blo 2285435 3431009 := bstep (se 2 (by rfl) ⟨1286628, by rfl⟩ : syracuseStep 3431009 = 2573257) B2573257
theorem B2287339 : Blo 2285435 2287339 := bstep (se 1 (by rfl) ⟨1715504, by rfl⟩ : syracuseStep 2287339 = 3431009) B3431009
theorem B4121869 : Blo 2285435 4121869 := bbase (se 3 (by rfl) ⟨772850, by rfl⟩ : syracuseStep 4121869 = 1545701) (by norm_num)
theorem B5495825 : Blo 2285435 5495825 := bstep (se 2 (by rfl) ⟨2060934, by rfl⟩ : syracuseStep 5495825 = 4121869) B4121869
theorem B3663883 : Blo 2285435 3663883 := bstep (se 1 (by rfl) ⟨2747912, by rfl⟩ : syracuseStep 3663883 = 5495825) B5495825
theorem B19540709 : Blo 2285435 19540709 := bstep (se 4 (by rfl) ⟨1831941, by rfl⟩ : syracuseStep 19540709 = 3663883) B3663883
theorem B13027139 : Blo 2285435 13027139 := bstep (se 1 (by rfl) ⟨9770354, by rfl⟩ : syracuseStep 13027139 = 19540709) B19540709
theorem B8684759 : Blo 2285435 8684759 := bstep (se 1 (by rfl) ⟨6513569, by rfl⟩ : syracuseStep 8684759 = 13027139) B13027139
theorem B5789839 : Blo 2285435 5789839 := bstep (se 1 (by rfl) ⟨4342379, by rfl⟩ : syracuseStep 5789839 = 8684759) B8684759
theorem B7719785 : Blo 2285435 7719785 := bstep (se 2 (by rfl) ⟨2894919, by rfl⟩ : syracuseStep 7719785 = 5789839) B5789839
theorem B5146523 : Blo 2285435 5146523 := bstep (se 1 (by rfl) ⟨3859892, by rfl⟩ : syracuseStep 5146523 = 7719785) B7719785
theorem B3431015 : Blo 2285435 3431015 := bstep (se 1 (by rfl) ⟨2573261, by rfl⟩ : syracuseStep 3431015 = 5146523) B5146523
theorem B2287343 : Blo 2285435 2287343 := bstep (se 1 (by rfl) ⟨1715507, by rfl⟩ : syracuseStep 2287343 = 3431015) B3431015
theorem B3431021 : Blo 2285435 3431021 := bbase (se 3 (by rfl) ⟨643316, by rfl⟩ : syracuseStep 3431021 = 1286633) (by norm_num)
theorem B2287347 : Blo 2285435 2287347 := bstep (se 1 (by rfl) ⟨1715510, by rfl⟩ : syracuseStep 2287347 = 3431021) B3431021
theorem B5146541 : Blo 2285435 5146541 := bbase (se 3 (by rfl) ⟨964976, by rfl⟩ : syracuseStep 5146541 = 1929953) (by norm_num)
theorem B3431027 : Blo 2285435 3431027 := bstep (se 1 (by rfl) ⟨2573270, by rfl⟩ : syracuseStep 3431027 = 5146541) B5146541
theorem B2287351 : Blo 2285435 2287351 := bstep (se 1 (by rfl) ⟨1715513, by rfl⟩ : syracuseStep 2287351 = 3431027) B3431027
theorem B6513605 : Blo 2285435 6513605 := bbase (se 4 (by rfl) ⟨610650, by rfl⟩ : syracuseStep 6513605 = 1221301) (by norm_num)
theorem B4342403 : Blo 2285435 4342403 := bstep (se 1 (by rfl) ⟨3256802, by rfl⟩ : syracuseStep 4342403 = 6513605) B6513605
theorem B2894935 : Blo 2285435 2894935 := bstep (se 1 (by rfl) ⟨2171201, by rfl⟩ : syracuseStep 2894935 = 4342403) B4342403
theorem B3859913 : Blo 2285435 3859913 := bstep (se 2 (by rfl) ⟨1447467, by rfl⟩ : syracuseStep 3859913 = 2894935) B2894935
theorem B2573275 : Blo 2285435 2573275 := bstep (se 1 (by rfl) ⟨1929956, by rfl⟩ : syracuseStep 2573275 = 3859913) B3859913
theorem B3431033 : Blo 2285435 3431033 := bstep (se 2 (by rfl) ⟨1286637, by rfl⟩ : syracuseStep 3431033 = 2573275) B2573275
theorem B2287355 : Blo 2285435 2287355 := bstep (se 1 (by rfl) ⟨1715516, by rfl⟩ : syracuseStep 2287355 = 3431033) B3431033
theorem B6602485 : Blo 2285435 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B8803313 : Blo 2285435 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B5868875 : Blo 2285435 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B15650333 : Blo 2285435 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B10433555 : Blo 2285435 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B6955703 : Blo 2285435 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B4637135 : Blo 2285435 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B3091423 : Blo 2285435 3091423 := bstep (se 1 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 3091423 = 4637135) B4637135
theorem B4121897 : Blo 2285435 4121897 := bstep (se 2 (by rfl) ⟨1545711, by rfl⟩ : syracuseStep 4121897 = 3091423) B3091423
theorem B43966901 : Blo 2285435 43966901 := bstep (se 5 (by rfl) ⟨2060948, by rfl⟩ : syracuseStep 43966901 = 4121897) B4121897
theorem B29311267 : Blo 2285435 29311267 := bstep (se 1 (by rfl) ⟨21983450, by rfl⟩ : syracuseStep 29311267 = 43966901) B43966901
theorem B39081689 : Blo 2285435 39081689 := bstep (se 2 (by rfl) ⟨14655633, by rfl⟩ : syracuseStep 39081689 = 29311267) B29311267
theorem B26054459 : Blo 2285435 26054459 := bstep (se 1 (by rfl) ⟨19540844, by rfl⟩ : syracuseStep 26054459 = 39081689) B39081689
theorem B17369639 : Blo 2285435 17369639 := bstep (se 1 (by rfl) ⟨13027229, by rfl⟩ : syracuseStep 17369639 = 26054459) B26054459
theorem B11579759 : Blo 2285435 11579759 := bstep (se 1 (by rfl) ⟨8684819, by rfl⟩ : syracuseStep 11579759 = 17369639) B17369639
theorem B7719839 : Blo 2285435 7719839 := bstep (se 1 (by rfl) ⟨5789879, by rfl⟩ : syracuseStep 7719839 = 11579759) B11579759
theorem B5146559 : Blo 2285435 5146559 := bstep (se 1 (by rfl) ⟨3859919, by rfl⟩ : syracuseStep 5146559 = 7719839) B7719839
theorem B3431039 : Blo 2285435 3431039 := bstep (se 1 (by rfl) ⟨2573279, by rfl⟩ : syracuseStep 3431039 = 5146559) B5146559
theorem B2287359 : Blo 2285435 2287359 := bstep (se 1 (by rfl) ⟨1715519, by rfl⟩ : syracuseStep 2287359 = 3431039) B3431039
theorem B3431045 : Blo 2285435 3431045 := bbase (se 4 (by rfl) ⟨321660, by rfl⟩ : syracuseStep 3431045 = 643321) (by norm_num)
theorem B2287363 : Blo 2285435 2287363 := bstep (se 1 (by rfl) ⟨1715522, by rfl⟩ : syracuseStep 2287363 = 3431045) B3431045
theorem B3859933 : Blo 2285435 3859933 := bbase (se 3 (by rfl) ⟨723737, by rfl⟩ : syracuseStep 3859933 = 1447475) (by norm_num)
theorem B5146577 : Blo 2285435 5146577 := bstep (se 2 (by rfl) ⟨1929966, by rfl⟩ : syracuseStep 5146577 = 3859933) B3859933
theorem B3431051 : Blo 2285435 3431051 := bstep (se 1 (by rfl) ⟨2573288, by rfl⟩ : syracuseStep 3431051 = 5146577) B5146577
theorem B2287367 : Blo 2285435 2287367 := bstep (se 1 (by rfl) ⟨1715525, by rfl⟩ : syracuseStep 2287367 = 3431051) B3431051
theorem B2573293 : Blo 2285435 2573293 := bbase (se 3 (by rfl) ⟨482492, by rfl⟩ : syracuseStep 2573293 = 964985) (by norm_num)
theorem B3431057 : Blo 2285435 3431057 := bstep (se 2 (by rfl) ⟨1286646, by rfl⟩ : syracuseStep 3431057 = 2573293) B2573293
theorem B2287371 : Blo 2285435 2287371 := bstep (se 1 (by rfl) ⟨1715528, by rfl⟩ : syracuseStep 2287371 = 3431057) B3431057
theorem B7719893 : Blo 2285435 7719893 := bbase (se 7 (by rfl) ⟨90467, by rfl⟩ : syracuseStep 7719893 = 180935) (by norm_num)
theorem B5146595 : Blo 2285435 5146595 := bstep (se 1 (by rfl) ⟨3859946, by rfl⟩ : syracuseStep 5146595 = 7719893) B7719893
theorem B3431063 : Blo 2285435 3431063 := bstep (se 1 (by rfl) ⟨2573297, by rfl⟩ : syracuseStep 3431063 = 5146595) B5146595
theorem B2287375 : Blo 2285435 2287375 := bstep (se 1 (by rfl) ⟨1715531, by rfl⟩ : syracuseStep 2287375 = 3431063) B3431063
theorem B3431069 : Blo 2285435 3431069 := bbase (se 3 (by rfl) ⟨643325, by rfl⟩ : syracuseStep 3431069 = 1286651) (by norm_num)
theorem B2287379 : Blo 2285435 2287379 := bstep (se 1 (by rfl) ⟨1715534, by rfl⟩ : syracuseStep 2287379 = 3431069) B3431069
theorem B5146613 : Blo 2285435 5146613 := bbase (se 5 (by rfl) ⟨241247, by rfl⟩ : syracuseStep 5146613 = 482495) (by norm_num)
theorem B3431075 : Blo 2285435 3431075 := bstep (se 1 (by rfl) ⟨2573306, by rfl⟩ : syracuseStep 3431075 = 5146613) B5146613
theorem B2287383 : Blo 2285435 2287383 := bstep (se 1 (by rfl) ⟨1715537, by rfl⟩ : syracuseStep 2287383 = 3431075) B3431075
theorem B2785457 : Blo 2285435 2785457 := bbase (se 2 (by rfl) ⟨1044546, by rfl⟩ : syracuseStep 2785457 = 2089093) (by norm_num)
theorem B7427885 : Blo 2285435 7427885 := bstep (se 3 (by rfl) ⟨1392728, by rfl⟩ : syracuseStep 7427885 = 2785457) B2785457
theorem B79230773 : Blo 2285435 79230773 := bstep (se 5 (by rfl) ⟨3713942, by rfl⟩ : syracuseStep 79230773 = 7427885) B7427885
theorem B52820515 : Blo 2285435 52820515 := bstep (se 1 (by rfl) ⟨39615386, by rfl⟩ : syracuseStep 52820515 = 79230773) B79230773
theorem B70427353 : Blo 2285435 70427353 := bstep (se 2 (by rfl) ⟨26410257, by rfl⟩ : syracuseStep 70427353 = 52820515) B52820515
theorem B93903137 : Blo 2285435 93903137 := bstep (se 2 (by rfl) ⟨35213676, by rfl⟩ : syracuseStep 93903137 = 70427353) B70427353
theorem B62602091 : Blo 2285435 62602091 := bstep (se 1 (by rfl) ⟨46951568, by rfl⟩ : syracuseStep 62602091 = 93903137) B93903137
theorem B41734727 : Blo 2285435 41734727 := bstep (se 1 (by rfl) ⟨31301045, by rfl⟩ : syracuseStep 41734727 = 62602091) B62602091
theorem B27823151 : Blo 2285435 27823151 := bstep (se 1 (by rfl) ⟨20867363, by rfl⟩ : syracuseStep 27823151 = 41734727) B41734727
theorem B18548767 : Blo 2285435 18548767 := bstep (se 1 (by rfl) ⟨13911575, by rfl⟩ : syracuseStep 18548767 = 27823151) B27823151
theorem B98926757 : Blo 2285435 98926757 := bstep (se 4 (by rfl) ⟨9274383, by rfl⟩ : syracuseStep 98926757 = 18548767) B18548767
theorem B65951171 : Blo 2285435 65951171 := bstep (se 1 (by rfl) ⟨49463378, by rfl⟩ : syracuseStep 65951171 = 98926757) B98926757
theorem B43967447 : Blo 2285435 43967447 := bstep (se 1 (by rfl) ⟨32975585, by rfl⟩ : syracuseStep 43967447 = 65951171) B65951171
theorem B29311631 : Blo 2285435 29311631 := bstep (se 1 (by rfl) ⟨21983723, by rfl⟩ : syracuseStep 29311631 = 43967447) B43967447
theorem B19541087 : Blo 2285435 19541087 := bstep (se 1 (by rfl) ⟨14655815, by rfl⟩ : syracuseStep 19541087 = 29311631) B29311631
theorem B13027391 : Blo 2285435 13027391 := bstep (se 1 (by rfl) ⟨9770543, by rfl⟩ : syracuseStep 13027391 = 19541087) B19541087
theorem B8684927 : Blo 2285435 8684927 := bstep (se 1 (by rfl) ⟨6513695, by rfl⟩ : syracuseStep 8684927 = 13027391) B13027391
theorem B5789951 : Blo 2285435 5789951 := bstep (se 1 (by rfl) ⟨4342463, by rfl⟩ : syracuseStep 5789951 = 8684927) B8684927
theorem B3859967 : Blo 2285435 3859967 := bstep (se 1 (by rfl) ⟨2894975, by rfl⟩ : syracuseStep 3859967 = 5789951) B5789951
theorem B2573311 : Blo 2285435 2573311 := bstep (se 1 (by rfl) ⟨1929983, by rfl⟩ : syracuseStep 2573311 = 3859967) B3859967
theorem B3431081 : Blo 2285435 3431081 := bstep (se 2 (by rfl) ⟨1286655, by rfl⟩ : syracuseStep 3431081 = 2573311) B2573311
theorem B2287387 : Blo 2285435 2287387 := bstep (se 1 (by rfl) ⟨1715540, by rfl⟩ : syracuseStep 2287387 = 3431081) B3431081
theorem B3256853 : Blo 2285435 3256853 := bbase (se 6 (by rfl) ⟨76332, by rfl⟩ : syracuseStep 3256853 = 152665) (by norm_num)
theorem B8684941 : Blo 2285435 8684941 := bstep (se 3 (by rfl) ⟨1628426, by rfl⟩ : syracuseStep 8684941 = 3256853) B3256853
theorem B11579921 : Blo 2285435 11579921 := bstep (se 2 (by rfl) ⟨4342470, by rfl⟩ : syracuseStep 11579921 = 8684941) B8684941
theorem B7719947 : Blo 2285435 7719947 := bstep (se 1 (by rfl) ⟨5789960, by rfl⟩ : syracuseStep 7719947 = 11579921) B11579921
theorem B5146631 : Blo 2285435 5146631 := bstep (se 1 (by rfl) ⟨3859973, by rfl⟩ : syracuseStep 5146631 = 7719947) B7719947
theorem B3431087 : Blo 2285435 3431087 := bstep (se 1 (by rfl) ⟨2573315, by rfl⟩ : syracuseStep 3431087 = 5146631) B5146631
theorem B2287391 : Blo 2285435 2287391 := bstep (se 1 (by rfl) ⟨1715543, by rfl⟩ : syracuseStep 2287391 = 3431087) B3431087
theorem B3431093 : Blo 2285435 3431093 := bbase (se 5 (by rfl) ⟨160832, by rfl⟩ : syracuseStep 3431093 = 321665) (by norm_num)
theorem B2287395 : Blo 2285435 2287395 := bstep (se 1 (by rfl) ⟨1715546, by rfl⟩ : syracuseStep 2287395 = 3431093) B3431093
theorem B5789981 : Blo 2285435 5789981 := bbase (se 3 (by rfl) ⟨1085621, by rfl⟩ : syracuseStep 5789981 = 2171243) (by norm_num)
theorem B3859987 : Blo 2285435 3859987 := bstep (se 1 (by rfl) ⟨2894990, by rfl⟩ : syracuseStep 3859987 = 5789981) B5789981
theorem B5146649 : Blo 2285435 5146649 := bstep (se 2 (by rfl) ⟨1929993, by rfl⟩ : syracuseStep 5146649 = 3859987) B3859987
theorem B3431099 : Blo 2285435 3431099 := bstep (se 1 (by rfl) ⟨2573324, by rfl⟩ : syracuseStep 3431099 = 5146649) B5146649
theorem B2287399 : Blo 2285435 2287399 := bstep (se 1 (by rfl) ⟨1715549, by rfl⟩ : syracuseStep 2287399 = 3431099) B3431099
theorem B2573329 : Blo 2285435 2573329 := bbase (se 2 (by rfl) ⟨964998, by rfl⟩ : syracuseStep 2573329 = 1929997) (by norm_num)
theorem B3431105 : Blo 2285435 3431105 := bstep (se 2 (by rfl) ⟨1286664, by rfl⟩ : syracuseStep 3431105 = 2573329) B2573329
theorem B2287403 : Blo 2285435 2287403 := bstep (se 1 (by rfl) ⟨1715552, by rfl⟩ : syracuseStep 2287403 = 3431105) B3431105
theorem B4342501 : Blo 2285435 4342501 := bbase (se 4 (by rfl) ⟨407109, by rfl⟩ : syracuseStep 4342501 = 814219) (by norm_num)
theorem B5790001 : Blo 2285435 5790001 := bstep (se 2 (by rfl) ⟨2171250, by rfl⟩ : syracuseStep 5790001 = 4342501) B4342501
theorem B7720001 : Blo 2285435 7720001 := bstep (se 2 (by rfl) ⟨2895000, by rfl⟩ : syracuseStep 7720001 = 5790001) B5790001
theorem B5146667 : Blo 2285435 5146667 := bstep (se 1 (by rfl) ⟨3860000, by rfl⟩ : syracuseStep 5146667 = 7720001) B7720001
theorem B3431111 : Blo 2285435 3431111 := bstep (se 1 (by rfl) ⟨2573333, by rfl⟩ : syracuseStep 3431111 = 5146667) B5146667
theorem B2287407 : Blo 2285435 2287407 := bstep (se 1 (by rfl) ⟨1715555, by rfl⟩ : syracuseStep 2287407 = 3431111) B3431111
theorem B3431117 : Blo 2285435 3431117 := bbase (se 3 (by rfl) ⟨643334, by rfl⟩ : syracuseStep 3431117 = 1286669) (by norm_num)
theorem B2287411 : Blo 2285435 2287411 := bstep (se 1 (by rfl) ⟨1715558, by rfl⟩ : syracuseStep 2287411 = 3431117) B3431117
theorem B5146685 : Blo 2285435 5146685 := bbase (se 3 (by rfl) ⟨965003, by rfl⟩ : syracuseStep 5146685 = 1930007) (by norm_num)
theorem B3431123 : Blo 2285435 3431123 := bstep (se 1 (by rfl) ⟨2573342, by rfl⟩ : syracuseStep 3431123 = 5146685) B5146685
theorem B2287415 : Blo 2285435 2287415 := bstep (se 1 (by rfl) ⟨1715561, by rfl⟩ : syracuseStep 2287415 = 3431123) B3431123
theorem B3860021 : Blo 2285435 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B2573347 : Blo 2285435 2573347 := bstep (se 1 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 2573347 = 3860021) B3860021
theorem B3431129 : Blo 2285435 3431129 := bstep (se 2 (by rfl) ⟨1286673, by rfl⟩ : syracuseStep 3431129 = 2573347) B2573347
theorem B2287419 : Blo 2285435 2287419 := bstep (se 1 (by rfl) ⟨1715564, by rfl⟩ : syracuseStep 2287419 = 3431129) B3431129
theorem B6513797 : Blo 2285435 6513797 := bbase (se 4 (by rfl) ⟨610668, by rfl⟩ : syracuseStep 6513797 = 1221337) (by norm_num)
theorem B17370125 : Blo 2285435 17370125 := bstep (se 3 (by rfl) ⟨3256898, by rfl⟩ : syracuseStep 17370125 = 6513797) B6513797
theorem B11580083 : Blo 2285435 11580083 := bstep (se 1 (by rfl) ⟨8685062, by rfl⟩ : syracuseStep 11580083 = 17370125) B17370125
theorem B7720055 : Blo 2285435 7720055 := bstep (se 1 (by rfl) ⟨5790041, by rfl⟩ : syracuseStep 7720055 = 11580083) B11580083
theorem B5146703 : Blo 2285435 5146703 := bstep (se 1 (by rfl) ⟨3860027, by rfl⟩ : syracuseStep 5146703 = 7720055) B7720055
theorem B3431135 : Blo 2285435 3431135 := bstep (se 1 (by rfl) ⟨2573351, by rfl⟩ : syracuseStep 3431135 = 5146703) B5146703
theorem B2287423 : Blo 2285435 2287423 := bstep (se 1 (by rfl) ⟨1715567, by rfl⟩ : syracuseStep 2287423 = 3431135) B3431135
theorem B3431141 : Blo 2285435 3431141 := bbase (se 4 (by rfl) ⟨321669, by rfl⟩ : syracuseStep 3431141 = 643339) (by norm_num)
theorem B2287427 : Blo 2285435 2287427 := bstep (se 1 (by rfl) ⟨1715570, by rfl⟩ : syracuseStep 2287427 = 3431141) B3431141
theorem B4122029 : Blo 2285435 4122029 := bbase (se 3 (by rfl) ⟨772880, by rfl⟩ : syracuseStep 4122029 = 1545761) (by norm_num)
theorem B2748019 : Blo 2285435 2748019 := bstep (se 1 (by rfl) ⟨2061014, by rfl⟩ : syracuseStep 2748019 = 4122029) B4122029
theorem B3664025 : Blo 2285435 3664025 := bstep (se 2 (by rfl) ⟨1374009, by rfl⟩ : syracuseStep 3664025 = 2748019) B2748019
theorem B2442683 : Blo 2285435 2442683 := bstep (se 1 (by rfl) ⟨1832012, by rfl⟩ : syracuseStep 2442683 = 3664025) B3664025
theorem B6513821 : Blo 2285435 6513821 := bstep (se 3 (by rfl) ⟨1221341, by rfl⟩ : syracuseStep 6513821 = 2442683) B2442683
theorem B4342547 : Blo 2285435 4342547 := bstep (se 1 (by rfl) ⟨3256910, by rfl⟩ : syracuseStep 4342547 = 6513821) B6513821
theorem B2895031 : Blo 2285435 2895031 := bstep (se 1 (by rfl) ⟨2171273, by rfl⟩ : syracuseStep 2895031 = 4342547) B4342547
theorem B3860041 : Blo 2285435 3860041 := bstep (se 2 (by rfl) ⟨1447515, by rfl⟩ : syracuseStep 3860041 = 2895031) B2895031
theorem B5146721 : Blo 2285435 5146721 := bstep (se 2 (by rfl) ⟨1930020, by rfl⟩ : syracuseStep 5146721 = 3860041) B3860041
theorem B3431147 : Blo 2285435 3431147 := bstep (se 1 (by rfl) ⟨2573360, by rfl⟩ : syracuseStep 3431147 = 5146721) B5146721
theorem B2287431 : Blo 2285435 2287431 := bstep (se 1 (by rfl) ⟨1715573, by rfl⟩ : syracuseStep 2287431 = 3431147) B3431147
theorem B2573365 : Blo 2285435 2573365 := bbase (se 5 (by rfl) ⟨120626, by rfl⟩ : syracuseStep 2573365 = 241253) (by norm_num)
theorem B3431153 : Blo 2285435 3431153 := bstep (se 2 (by rfl) ⟨1286682, by rfl⟩ : syracuseStep 3431153 = 2573365) B2573365
theorem B2287435 : Blo 2285435 2287435 := bstep (se 1 (by rfl) ⟨1715576, by rfl⟩ : syracuseStep 2287435 = 3431153) B3431153
theorem C0 (j : ℕ) (h1 : 571358 ≤ j) (h2 : j ≤ 571858) : Blo 2285435 (4 * j + 3) := by
  interval_cases j
  · exact B2285435
  · exact B2285439
  · exact B2285443
  · exact B2285447
  · exact B2285451
  · exact B2285455
  · exact B2285459
  · exact B2285463
  · exact B2285467
  · exact B2285471
  · exact B2285475
  · exact B2285479
  · exact B2285483
  · exact B2285487
  · exact B2285491
  · exact B2285495
  · exact B2285499
  · exact B2285503
  · exact B2285507
  · exact B2285511
  · exact B2285515
  · exact B2285519
  · exact B2285523
  · exact B2285527
  · exact B2285531
  · exact B2285535
  · exact B2285539
  · exact B2285543
  · exact B2285547
  · exact B2285551
  · exact B2285555
  · exact B2285559
  · exact B2285563
  · exact B2285567
  · exact B2285571
  · exact B2285575
  · exact B2285579
  · exact B2285583
  · exact B2285587
  · exact B2285591
  · exact B2285595
  · exact B2285599
  · exact B2285603
  · exact B2285607
  · exact B2285611
  · exact B2285615
  · exact B2285619
  · exact B2285623
  · exact B2285627
  · exact B2285631
  · exact B2285635
  · exact B2285639
  · exact B2285643
  · exact B2285647
  · exact B2285651
  · exact B2285655
  · exact B2285659
  · exact B2285663
  · exact B2285667
  · exact B2285671
  · exact B2285675
  · exact B2285679
  · exact B2285683
  · exact B2285687
  · exact B2285691
  · exact B2285695
  · exact B2285699
  · exact B2285703
  · exact B2285707
  · exact B2285711
  · exact B2285715
  · exact B2285719
  · exact B2285723
  · exact B2285727
  · exact B2285731
  · exact B2285735
  · exact B2285739
  · exact B2285743
  · exact B2285747
  · exact B2285751
  · exact B2285755
  · exact B2285759
  · exact B2285763
  · exact B2285767
  · exact B2285771
  · exact B2285775
  · exact B2285779
  · exact B2285783
  · exact B2285787
  · exact B2285791
  · exact B2285795
  · exact B2285799
  · exact B2285803
  · exact B2285807
  · exact B2285811
  · exact B2285815
  · exact B2285819
  · exact B2285823
  · exact B2285827
  · exact B2285831
  · exact B2285835
  · exact B2285839
  · exact B2285843
  · exact B2285847
  · exact B2285851
  · exact B2285855
  · exact B2285859
  · exact B2285863
  · exact B2285867
  · exact B2285871
  · exact B2285875
  · exact B2285879
  · exact B2285883
  · exact B2285887
  · exact B2285891
  · exact B2285895
  · exact B2285899
  · exact B2285903
  · exact B2285907
  · exact B2285911
  · exact B2285915
  · exact B2285919
  · exact B2285923
  · exact B2285927
  · exact B2285931
  · exact B2285935
  · exact B2285939
  · exact B2285943
  · exact B2285947
  · exact B2285951
  · exact B2285955
  · exact B2285959
  · exact B2285963
  · exact B2285967
  · exact B2285971
  · exact B2285975
  · exact B2285979
  · exact B2285983
  · exact B2285987
  · exact B2285991
  · exact B2285995
  · exact B2285999
  · exact B2286003
  · exact B2286007
  · exact B2286011
  · exact B2286015
  · exact B2286019
  · exact B2286023
  · exact B2286027
  · exact B2286031
  · exact B2286035
  · exact B2286039
  · exact B2286043
  · exact B2286047
  · exact B2286051
  · exact B2286055
  · exact B2286059
  · exact B2286063
  · exact B2286067
  · exact B2286071
  · exact B2286075
  · exact B2286079
  · exact B2286083
  · exact B2286087
  · exact B2286091
  · exact B2286095
  · exact B2286099
  · exact B2286103
  · exact B2286107
  · exact B2286111
  · exact B2286115
  · exact B2286119
  · exact B2286123
  · exact B2286127
  · exact B2286131
  · exact B2286135
  · exact B2286139
  · exact B2286143
  · exact B2286147
  · exact B2286151
  · exact B2286155
  · exact B2286159
  · exact B2286163
  · exact B2286167
  · exact B2286171
  · exact B2286175
  · exact B2286179
  · exact B2286183
  · exact B2286187
  · exact B2286191
  · exact B2286195
  · exact B2286199
  · exact B2286203
  · exact B2286207
  · exact B2286211
  · exact B2286215
  · exact B2286219
  · exact B2286223
  · exact B2286227
  · exact B2286231
  · exact B2286235
  · exact B2286239
  · exact B2286243
  · exact B2286247
  · exact B2286251
  · exact B2286255
  · exact B2286259
  · exact B2286263
  · exact B2286267
  · exact B2286271
  · exact B2286275
  · exact B2286279
  · exact B2286283
  · exact B2286287
  · exact B2286291
  · exact B2286295
  · exact B2286299
  · exact B2286303
  · exact B2286307
  · exact B2286311
  · exact B2286315
  · exact B2286319
  · exact B2286323
  · exact B2286327
  · exact B2286331
  · exact B2286335
  · exact B2286339
  · exact B2286343
  · exact B2286347
  · exact B2286351
  · exact B2286355
  · exact B2286359
  · exact B2286363
  · exact B2286367
  · exact B2286371
  · exact B2286375
  · exact B2286379
  · exact B2286383
  · exact B2286387
  · exact B2286391
  · exact B2286395
  · exact B2286399
  · exact B2286403
  · exact B2286407
  · exact B2286411
  · exact B2286415
  · exact B2286419
  · exact B2286423
  · exact B2286427
  · exact B2286431
  · exact B2286435
  · exact B2286439
  · exact B2286443
  · exact B2286447
  · exact B2286451
  · exact B2286455
  · exact B2286459
  · exact B2286463
  · exact B2286467
  · exact B2286471
  · exact B2286475
  · exact B2286479
  · exact B2286483
  · exact B2286487
  · exact B2286491
  · exact B2286495
  · exact B2286499
  · exact B2286503
  · exact B2286507
  · exact B2286511
  · exact B2286515
  · exact B2286519
  · exact B2286523
  · exact B2286527
  · exact B2286531
  · exact B2286535
  · exact B2286539
  · exact B2286543
  · exact B2286547
  · exact B2286551
  · exact B2286555
  · exact B2286559
  · exact B2286563
  · exact B2286567
  · exact B2286571
  · exact B2286575
  · exact B2286579
  · exact B2286583
  · exact B2286587
  · exact B2286591
  · exact B2286595
  · exact B2286599
  · exact B2286603
  · exact B2286607
  · exact B2286611
  · exact B2286615
  · exact B2286619
  · exact B2286623
  · exact B2286627
  · exact B2286631
  · exact B2286635
  · exact B2286639
  · exact B2286643
  · exact B2286647
  · exact B2286651
  · exact B2286655
  · exact B2286659
  · exact B2286663
  · exact B2286667
  · exact B2286671
  · exact B2286675
  · exact B2286679
  · exact B2286683
  · exact B2286687
  · exact B2286691
  · exact B2286695
  · exact B2286699
  · exact B2286703
  · exact B2286707
  · exact B2286711
  · exact B2286715
  · exact B2286719
  · exact B2286723
  · exact B2286727
  · exact B2286731
  · exact B2286735
  · exact B2286739
  · exact B2286743
  · exact B2286747
  · exact B2286751
  · exact B2286755
  · exact B2286759
  · exact B2286763
  · exact B2286767
  · exact B2286771
  · exact B2286775
  · exact B2286779
  · exact B2286783
  · exact B2286787
  · exact B2286791
  · exact B2286795
  · exact B2286799
  · exact B2286803
  · exact B2286807
  · exact B2286811
  · exact B2286815
  · exact B2286819
  · exact B2286823
  · exact B2286827
  · exact B2286831
  · exact B2286835
  · exact B2286839
  · exact B2286843
  · exact B2286847
  · exact B2286851
  · exact B2286855
  · exact B2286859
  · exact B2286863
  · exact B2286867
  · exact B2286871
  · exact B2286875
  · exact B2286879
  · exact B2286883
  · exact B2286887
  · exact B2286891
  · exact B2286895
  · exact B2286899
  · exact B2286903
  · exact B2286907
  · exact B2286911
  · exact B2286915
  · exact B2286919
  · exact B2286923
  · exact B2286927
  · exact B2286931
  · exact B2286935
  · exact B2286939
  · exact B2286943
  · exact B2286947
  · exact B2286951
  · exact B2286955
  · exact B2286959
  · exact B2286963
  · exact B2286967
  · exact B2286971
  · exact B2286975
  · exact B2286979
  · exact B2286983
  · exact B2286987
  · exact B2286991
  · exact B2286995
  · exact B2286999
  · exact B2287003
  · exact B2287007
  · exact B2287011
  · exact B2287015
  · exact B2287019
  · exact B2287023
  · exact B2287027
  · exact B2287031
  · exact B2287035
  · exact B2287039
  · exact B2287043
  · exact B2287047
  · exact B2287051
  · exact B2287055
  · exact B2287059
  · exact B2287063
  · exact B2287067
  · exact B2287071
  · exact B2287075
  · exact B2287079
  · exact B2287083
  · exact B2287087
  · exact B2287091
  · exact B2287095
  · exact B2287099
  · exact B2287103
  · exact B2287107
  · exact B2287111
  · exact B2287115
  · exact B2287119
  · exact B2287123
  · exact B2287127
  · exact B2287131
  · exact B2287135
  · exact B2287139
  · exact B2287143
  · exact B2287147
  · exact B2287151
  · exact B2287155
  · exact B2287159
  · exact B2287163
  · exact B2287167
  · exact B2287171
  · exact B2287175
  · exact B2287179
  · exact B2287183
  · exact B2287187
  · exact B2287191
  · exact B2287195
  · exact B2287199
  · exact B2287203
  · exact B2287207
  · exact B2287211
  · exact B2287215
  · exact B2287219
  · exact B2287223
  · exact B2287227
  · exact B2287231
  · exact B2287235
  · exact B2287239
  · exact B2287243
  · exact B2287247
  · exact B2287251
  · exact B2287255
  · exact B2287259
  · exact B2287263
  · exact B2287267
  · exact B2287271
  · exact B2287275
  · exact B2287279
  · exact B2287283
  · exact B2287287
  · exact B2287291
  · exact B2287295
  · exact B2287299
  · exact B2287303
  · exact B2287307
  · exact B2287311
  · exact B2287315
  · exact B2287319
  · exact B2287323
  · exact B2287327
  · exact B2287331
  · exact B2287335
  · exact B2287339
  · exact B2287343
  · exact B2287347
  · exact B2287351
  · exact B2287355
  · exact B2287359
  · exact B2287363
  · exact B2287367
  · exact B2287371
  · exact B2287375
  · exact B2287379
  · exact B2287383
  · exact B2287387
  · exact B2287391
  · exact B2287395
  · exact B2287399
  · exact B2287403
  · exact B2287407
  · exact B2287411
  · exact B2287415
  · exact B2287419
  · exact B2287423
  · exact B2287427
  · exact B2287431
  · exact B2287435
theorem solution (m : ℕ) (hlo : 2285435 ≤ m) (hhi : m ≤ 2287435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 571358 ≤ j := by omega
    have hj2 : j ≤ 571858 := by omega
    have hb : Blo 2285435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
