-- Prove2me | solution 1 for syracuse_descends_range_2185435_2187435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:01.931913+00:00
-- url     : https://prove2.me/submissions/5d010efc-d037-4b1f-8fac-6eb60c221991

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

theorem B5531885 : Blo 2185435 5531885 := bbase (se 3 (by rfl) ⟨1037228, by rfl⟩ : syracuseStep 5531885 = 2074457) (by norm_num)
theorem B3687923 : Blo 2185435 3687923 := bstep (se 1 (by rfl) ⟨2765942, by rfl⟩ : syracuseStep 3687923 = 5531885) B5531885
theorem B2458615 : Blo 2185435 2458615 := bstep (se 1 (by rfl) ⟨1843961, by rfl⟩ : syracuseStep 2458615 = 3687923) B3687923
theorem B3278153 : Blo 2185435 3278153 := bstep (se 2 (by rfl) ⟨1229307, by rfl⟩ : syracuseStep 3278153 = 2458615) B2458615
theorem B2185435 : Blo 2185435 2185435 := bstep (se 1 (by rfl) ⟨1639076, by rfl⟩ : syracuseStep 2185435 = 3278153) B3278153
theorem B3500653 : Blo 2185435 3500653 := bbase (se 3 (by rfl) ⟨656372, by rfl⟩ : syracuseStep 3500653 = 1312745) (by norm_num)
theorem B4667537 : Blo 2185435 4667537 := bstep (se 2 (by rfl) ⟨1750326, by rfl⟩ : syracuseStep 4667537 = 3500653) B3500653
theorem B3111691 : Blo 2185435 3111691 := bstep (se 1 (by rfl) ⟨2333768, by rfl⟩ : syracuseStep 3111691 = 4667537) B4667537
theorem B4148921 : Blo 2185435 4148921 := bstep (se 2 (by rfl) ⟨1555845, by rfl⟩ : syracuseStep 4148921 = 3111691) B3111691
theorem B11063789 : Blo 2185435 11063789 := bstep (se 3 (by rfl) ⟨2074460, by rfl⟩ : syracuseStep 11063789 = 4148921) B4148921
theorem B7375859 : Blo 2185435 7375859 := bstep (se 1 (by rfl) ⟨5531894, by rfl⟩ : syracuseStep 7375859 = 11063789) B11063789
theorem B4917239 : Blo 2185435 4917239 := bstep (se 1 (by rfl) ⟨3687929, by rfl⟩ : syracuseStep 4917239 = 7375859) B7375859
theorem B3278159 : Blo 2185435 3278159 := bstep (se 1 (by rfl) ⟨2458619, by rfl⟩ : syracuseStep 3278159 = 4917239) B4917239
theorem B2185439 : Blo 2185435 2185439 := bstep (se 1 (by rfl) ⟨1639079, by rfl⟩ : syracuseStep 2185439 = 3278159) B3278159
theorem B3278165 : Blo 2185435 3278165 := bbase (se 12 (by rfl) ⟨1200, by rfl⟩ : syracuseStep 3278165 = 2401) (by norm_num)
theorem B2185443 : Blo 2185435 2185443 := bstep (se 1 (by rfl) ⟨1639082, by rfl⟩ : syracuseStep 2185443 = 3278165) B3278165
theorem B2333777 : Blo 2185435 2333777 := bbase (se 2 (by rfl) ⟨875166, by rfl⟩ : syracuseStep 2333777 = 1750333) (by norm_num)
theorem B6223405 : Blo 2185435 6223405 := bstep (se 3 (by rfl) ⟨1166888, by rfl⟩ : syracuseStep 6223405 = 2333777) B2333777
theorem B8297873 : Blo 2185435 8297873 := bstep (se 2 (by rfl) ⟨3111702, by rfl⟩ : syracuseStep 8297873 = 6223405) B6223405
theorem B5531915 : Blo 2185435 5531915 := bstep (se 1 (by rfl) ⟨4148936, by rfl⟩ : syracuseStep 5531915 = 8297873) B8297873
theorem B3687943 : Blo 2185435 3687943 := bstep (se 1 (by rfl) ⟨2765957, by rfl⟩ : syracuseStep 3687943 = 5531915) B5531915
theorem B4917257 : Blo 2185435 4917257 := bstep (se 2 (by rfl) ⟨1843971, by rfl⟩ : syracuseStep 4917257 = 3687943) B3687943
theorem B3278171 : Blo 2185435 3278171 := bstep (se 1 (by rfl) ⟨2458628, by rfl⟩ : syracuseStep 3278171 = 4917257) B4917257
theorem B2185447 : Blo 2185435 2185447 := bstep (se 1 (by rfl) ⟨1639085, by rfl⟩ : syracuseStep 2185447 = 3278171) B3278171
theorem B2458633 : Blo 2185435 2458633 := bbase (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) (by norm_num)
theorem B3278177 : Blo 2185435 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B2185451 : Blo 2185435 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B8861093 : Blo 2185435 8861093 := bbase (se 4 (by rfl) ⟨830727, by rfl⟩ : syracuseStep 8861093 = 1661455) (by norm_num)
theorem B5907395 : Blo 2185435 5907395 := bstep (se 1 (by rfl) ⟨4430546, by rfl⟩ : syracuseStep 5907395 = 8861093) B8861093
theorem B3938263 : Blo 2185435 3938263 := bstep (se 1 (by rfl) ⟨2953697, by rfl⟩ : syracuseStep 3938263 = 5907395) B5907395
theorem B21004069 : Blo 2185435 21004069 := bstep (se 4 (by rfl) ⟨1969131, by rfl⟩ : syracuseStep 21004069 = 3938263) B3938263
theorem B28005425 : Blo 2185435 28005425 := bstep (se 2 (by rfl) ⟨10502034, by rfl⟩ : syracuseStep 28005425 = 21004069) B21004069
theorem B18670283 : Blo 2185435 18670283 := bstep (se 1 (by rfl) ⟨14002712, by rfl⟩ : syracuseStep 18670283 = 28005425) B28005425
theorem B12446855 : Blo 2185435 12446855 := bstep (se 1 (by rfl) ⟨9335141, by rfl⟩ : syracuseStep 12446855 = 18670283) B18670283
theorem B8297903 : Blo 2185435 8297903 := bstep (se 1 (by rfl) ⟨6223427, by rfl⟩ : syracuseStep 8297903 = 12446855) B12446855
theorem B5531935 : Blo 2185435 5531935 := bstep (se 1 (by rfl) ⟨4148951, by rfl⟩ : syracuseStep 5531935 = 8297903) B8297903
theorem B7375913 : Blo 2185435 7375913 := bstep (se 2 (by rfl) ⟨2765967, by rfl⟩ : syracuseStep 7375913 = 5531935) B5531935
theorem B4917275 : Blo 2185435 4917275 := bstep (se 1 (by rfl) ⟨3687956, by rfl⟩ : syracuseStep 4917275 = 7375913) B7375913
theorem B3278183 : Blo 2185435 3278183 := bstep (se 1 (by rfl) ⟨2458637, by rfl⟩ : syracuseStep 3278183 = 4917275) B4917275
theorem B2185455 : Blo 2185435 2185455 := bstep (se 1 (by rfl) ⟨1639091, by rfl⟩ : syracuseStep 2185455 = 3278183) B3278183
theorem B3278189 : Blo 2185435 3278189 := bbase (se 3 (by rfl) ⟨614660, by rfl⟩ : syracuseStep 3278189 = 1229321) (by norm_num)
theorem B2185459 : Blo 2185435 2185459 := bstep (se 1 (by rfl) ⟨1639094, by rfl⟩ : syracuseStep 2185459 = 3278189) B3278189
theorem B4917293 : Blo 2185435 4917293 := bbase (se 3 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 4917293 = 1843985) (by norm_num)
theorem B3278195 : Blo 2185435 3278195 := bstep (se 1 (by rfl) ⟨2458646, by rfl⟩ : syracuseStep 3278195 = 4917293) B4917293
theorem B2185463 : Blo 2185435 2185463 := bstep (se 1 (by rfl) ⟨1639097, by rfl⟩ : syracuseStep 2185463 = 3278195) B3278195
theorem B3548461 : Blo 2185435 3548461 := bbase (se 3 (by rfl) ⟨665336, by rfl⟩ : syracuseStep 3548461 = 1330673) (by norm_num)
theorem B4731281 : Blo 2185435 4731281 := bstep (se 2 (by rfl) ⟨1774230, by rfl⟩ : syracuseStep 4731281 = 3548461) B3548461
theorem B3154187 : Blo 2185435 3154187 := bstep (se 1 (by rfl) ⟨2365640, by rfl⟩ : syracuseStep 3154187 = 4731281) B4731281
theorem B8411165 : Blo 2185435 8411165 := bstep (se 3 (by rfl) ⟨1577093, by rfl⟩ : syracuseStep 8411165 = 3154187) B3154187
theorem B5607443 : Blo 2185435 5607443 := bstep (se 1 (by rfl) ⟨4205582, by rfl⟩ : syracuseStep 5607443 = 8411165) B8411165
theorem B3738295 : Blo 2185435 3738295 := bstep (se 1 (by rfl) ⟨2803721, by rfl⟩ : syracuseStep 3738295 = 5607443) B5607443
theorem B19937573 : Blo 2185435 19937573 := bstep (se 4 (by rfl) ⟨1869147, by rfl⟩ : syracuseStep 19937573 = 3738295) B3738295
theorem B13291715 : Blo 2185435 13291715 := bstep (se 1 (by rfl) ⟨9968786, by rfl⟩ : syracuseStep 13291715 = 19937573) B19937573
theorem B35444573 : Blo 2185435 35444573 := bstep (se 3 (by rfl) ⟨6645857, by rfl⟩ : syracuseStep 35444573 = 13291715) B13291715
theorem B23629715 : Blo 2185435 23629715 := bstep (se 1 (by rfl) ⟨17722286, by rfl⟩ : syracuseStep 23629715 = 35444573) B35444573
theorem B15753143 : Blo 2185435 15753143 := bstep (se 1 (by rfl) ⟨11814857, by rfl⟩ : syracuseStep 15753143 = 23629715) B23629715
theorem B10502095 : Blo 2185435 10502095 := bstep (se 1 (by rfl) ⟨7876571, by rfl⟩ : syracuseStep 10502095 = 15753143) B15753143
theorem B14002793 : Blo 2185435 14002793 := bstep (se 2 (by rfl) ⟨5251047, by rfl⟩ : syracuseStep 14002793 = 10502095) B10502095
theorem B9335195 : Blo 2185435 9335195 := bstep (se 1 (by rfl) ⟨7001396, by rfl⟩ : syracuseStep 9335195 = 14002793) B14002793
theorem B6223463 : Blo 2185435 6223463 := bstep (se 1 (by rfl) ⟨4667597, by rfl⟩ : syracuseStep 6223463 = 9335195) B9335195
theorem B4148975 : Blo 2185435 4148975 := bstep (se 1 (by rfl) ⟨3111731, by rfl⟩ : syracuseStep 4148975 = 6223463) B6223463
theorem B2765983 : Blo 2185435 2765983 := bstep (se 1 (by rfl) ⟨2074487, by rfl⟩ : syracuseStep 2765983 = 4148975) B4148975
theorem B3687977 : Blo 2185435 3687977 := bstep (se 2 (by rfl) ⟨1382991, by rfl⟩ : syracuseStep 3687977 = 2765983) B2765983
theorem B2458651 : Blo 2185435 2458651 := bstep (se 1 (by rfl) ⟨1843988, by rfl⟩ : syracuseStep 2458651 = 3687977) B3687977
theorem B3278201 : Blo 2185435 3278201 := bstep (se 2 (by rfl) ⟨1229325, by rfl⟩ : syracuseStep 3278201 = 2458651) B2458651
theorem B2185467 : Blo 2185435 2185467 := bstep (se 1 (by rfl) ⟨1639100, by rfl⟩ : syracuseStep 2185467 = 3278201) B3278201
theorem B2697661 : Blo 2185435 2697661 := bbase (se 3 (by rfl) ⟨505811, by rfl⟩ : syracuseStep 2697661 = 1011623) (by norm_num)
theorem B3596881 : Blo 2185435 3596881 := bstep (se 2 (by rfl) ⟨1348830, by rfl⟩ : syracuseStep 3596881 = 2697661) B2697661
theorem B4795841 : Blo 2185435 4795841 := bstep (se 2 (by rfl) ⟨1798440, by rfl⟩ : syracuseStep 4795841 = 3596881) B3596881
theorem B3197227 : Blo 2185435 3197227 := bstep (se 1 (by rfl) ⟨2397920, by rfl⟩ : syracuseStep 3197227 = 4795841) B4795841
theorem B4262969 : Blo 2185435 4262969 := bstep (se 2 (by rfl) ⟨1598613, by rfl⟩ : syracuseStep 4262969 = 3197227) B3197227
theorem B2841979 : Blo 2185435 2841979 := bstep (se 1 (by rfl) ⟨2131484, by rfl⟩ : syracuseStep 2841979 = 4262969) B4262969
theorem B3789305 : Blo 2185435 3789305 := bstep (se 2 (by rfl) ⟨1420989, by rfl⟩ : syracuseStep 3789305 = 2841979) B2841979
theorem B2526203 : Blo 2185435 2526203 := bstep (se 1 (by rfl) ⟨1894652, by rfl⟩ : syracuseStep 2526203 = 3789305) B3789305
theorem B6736541 : Blo 2185435 6736541 := bstep (se 3 (by rfl) ⟨1263101, by rfl⟩ : syracuseStep 6736541 = 2526203) B2526203
theorem B17964109 : Blo 2185435 17964109 := bstep (se 3 (by rfl) ⟨3368270, by rfl⟩ : syracuseStep 17964109 = 6736541) B6736541
theorem B23952145 : Blo 2185435 23952145 := bstep (se 2 (by rfl) ⟨8982054, by rfl⟩ : syracuseStep 23952145 = 17964109) B17964109
theorem B31936193 : Blo 2185435 31936193 := bstep (se 2 (by rfl) ⟨11976072, by rfl⟩ : syracuseStep 31936193 = 23952145) B23952145
theorem B21290795 : Blo 2185435 21290795 := bstep (se 1 (by rfl) ⟨15968096, by rfl⟩ : syracuseStep 21290795 = 31936193) B31936193
theorem B14193863 : Blo 2185435 14193863 := bstep (se 1 (by rfl) ⟨10645397, by rfl⟩ : syracuseStep 14193863 = 21290795) B21290795
theorem B9462575 : Blo 2185435 9462575 := bstep (se 1 (by rfl) ⟨7096931, by rfl⟩ : syracuseStep 9462575 = 14193863) B14193863
theorem B6308383 : Blo 2185435 6308383 := bstep (se 1 (by rfl) ⟨4731287, by rfl⟩ : syracuseStep 6308383 = 9462575) B9462575
theorem B8411177 : Blo 2185435 8411177 := bstep (se 2 (by rfl) ⟨3154191, by rfl⟩ : syracuseStep 8411177 = 6308383) B6308383
theorem B5607451 : Blo 2185435 5607451 := bstep (se 1 (by rfl) ⟨4205588, by rfl⟩ : syracuseStep 5607451 = 8411177) B8411177
theorem B29906405 : Blo 2185435 29906405 := bstep (se 4 (by rfl) ⟨2803725, by rfl⟩ : syracuseStep 29906405 = 5607451) B5607451
theorem B19937603 : Blo 2185435 19937603 := bstep (se 1 (by rfl) ⟨14953202, by rfl⟩ : syracuseStep 19937603 = 29906405) B29906405
theorem B53166941 : Blo 2185435 53166941 := bstep (se 3 (by rfl) ⟨9968801, by rfl⟩ : syracuseStep 53166941 = 19937603) B19937603
theorem B35444627 : Blo 2185435 35444627 := bstep (se 1 (by rfl) ⟨26583470, by rfl⟩ : syracuseStep 35444627 = 53166941) B53166941
theorem B23629751 : Blo 2185435 23629751 := bstep (se 1 (by rfl) ⟨17722313, by rfl⟩ : syracuseStep 23629751 = 35444627) B35444627
theorem B15753167 : Blo 2185435 15753167 := bstep (se 1 (by rfl) ⟨11814875, by rfl⟩ : syracuseStep 15753167 = 23629751) B23629751
theorem B10502111 : Blo 2185435 10502111 := bstep (se 1 (by rfl) ⟨7876583, by rfl⟩ : syracuseStep 10502111 = 15753167) B15753167
theorem B7001407 : Blo 2185435 7001407 := bstep (se 1 (by rfl) ⟨5251055, by rfl⟩ : syracuseStep 7001407 = 10502111) B10502111
theorem B37340837 : Blo 2185435 37340837 := bstep (se 4 (by rfl) ⟨3500703, by rfl⟩ : syracuseStep 37340837 = 7001407) B7001407
theorem B24893891 : Blo 2185435 24893891 := bstep (se 1 (by rfl) ⟨18670418, by rfl⟩ : syracuseStep 24893891 = 37340837) B37340837
theorem B16595927 : Blo 2185435 16595927 := bstep (se 1 (by rfl) ⟨12446945, by rfl⟩ : syracuseStep 16595927 = 24893891) B24893891
theorem B11063951 : Blo 2185435 11063951 := bstep (se 1 (by rfl) ⟨8297963, by rfl⟩ : syracuseStep 11063951 = 16595927) B16595927
theorem B7375967 : Blo 2185435 7375967 := bstep (se 1 (by rfl) ⟨5531975, by rfl⟩ : syracuseStep 7375967 = 11063951) B11063951
theorem B4917311 : Blo 2185435 4917311 := bstep (se 1 (by rfl) ⟨3687983, by rfl⟩ : syracuseStep 4917311 = 7375967) B7375967
theorem B3278207 : Blo 2185435 3278207 := bstep (se 1 (by rfl) ⟨2458655, by rfl⟩ : syracuseStep 3278207 = 4917311) B4917311
theorem B2185471 : Blo 2185435 2185471 := bstep (se 1 (by rfl) ⟨1639103, by rfl⟩ : syracuseStep 2185471 = 3278207) B3278207
theorem B3278213 : Blo 2185435 3278213 := bbase (se 4 (by rfl) ⟨307332, by rfl⟩ : syracuseStep 3278213 = 614665) (by norm_num)
theorem B2185475 : Blo 2185435 2185475 := bstep (se 1 (by rfl) ⟨1639106, by rfl⟩ : syracuseStep 2185475 = 3278213) B3278213
theorem B3687997 : Blo 2185435 3687997 := bbase (se 3 (by rfl) ⟨691499, by rfl⟩ : syracuseStep 3687997 = 1382999) (by norm_num)
theorem B4917329 : Blo 2185435 4917329 := bstep (se 2 (by rfl) ⟨1843998, by rfl⟩ : syracuseStep 4917329 = 3687997) B3687997
theorem B3278219 : Blo 2185435 3278219 := bstep (se 1 (by rfl) ⟨2458664, by rfl⟩ : syracuseStep 3278219 = 4917329) B4917329
theorem B2185479 : Blo 2185435 2185479 := bstep (se 1 (by rfl) ⟨1639109, by rfl⟩ : syracuseStep 2185479 = 3278219) B3278219
theorem B2458669 : Blo 2185435 2458669 := bbase (se 3 (by rfl) ⟨461000, by rfl⟩ : syracuseStep 2458669 = 922001) (by norm_num)
theorem B3278225 : Blo 2185435 3278225 := bstep (se 2 (by rfl) ⟨1229334, by rfl⟩ : syracuseStep 3278225 = 2458669) B2458669
theorem B2185483 : Blo 2185435 2185483 := bstep (se 1 (by rfl) ⟨1639112, by rfl⟩ : syracuseStep 2185483 = 3278225) B3278225
theorem B7376021 : Blo 2185435 7376021 := bbase (se 6 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 7376021 = 345751) (by norm_num)
theorem B4917347 : Blo 2185435 4917347 := bstep (se 1 (by rfl) ⟨3688010, by rfl⟩ : syracuseStep 4917347 = 7376021) B7376021
theorem B3278231 : Blo 2185435 3278231 := bstep (se 1 (by rfl) ⟨2458673, by rfl⟩ : syracuseStep 3278231 = 4917347) B4917347
theorem B2185487 : Blo 2185435 2185487 := bstep (se 1 (by rfl) ⟨1639115, by rfl⟩ : syracuseStep 2185487 = 3278231) B3278231
theorem B3278237 : Blo 2185435 3278237 := bbase (se 3 (by rfl) ⟨614669, by rfl⟩ : syracuseStep 3278237 = 1229339) (by norm_num)
theorem B2185491 : Blo 2185435 2185491 := bstep (se 1 (by rfl) ⟨1639118, by rfl⟩ : syracuseStep 2185491 = 3278237) B3278237
theorem B4917365 : Blo 2185435 4917365 := bbase (se 5 (by rfl) ⟨230501, by rfl⟩ : syracuseStep 4917365 = 461003) (by norm_num)
theorem B3278243 : Blo 2185435 3278243 := bstep (se 1 (by rfl) ⟨2458682, by rfl⟩ : syracuseStep 3278243 = 4917365) B4917365
theorem B2185495 : Blo 2185435 2185495 := bstep (se 1 (by rfl) ⟨1639121, by rfl⟩ : syracuseStep 2185495 = 3278243) B3278243
theorem B3500749 : Blo 2185435 3500749 := bbase (se 3 (by rfl) ⟨656390, by rfl⟩ : syracuseStep 3500749 = 1312781) (by norm_num)
theorem B18670661 : Blo 2185435 18670661 := bstep (se 4 (by rfl) ⟨1750374, by rfl⟩ : syracuseStep 18670661 = 3500749) B3500749
theorem B12447107 : Blo 2185435 12447107 := bstep (se 1 (by rfl) ⟨9335330, by rfl⟩ : syracuseStep 12447107 = 18670661) B18670661
theorem B8298071 : Blo 2185435 8298071 := bstep (se 1 (by rfl) ⟨6223553, by rfl⟩ : syracuseStep 8298071 = 12447107) B12447107
theorem B5532047 : Blo 2185435 5532047 := bstep (se 1 (by rfl) ⟨4149035, by rfl⟩ : syracuseStep 5532047 = 8298071) B8298071
theorem B3688031 : Blo 2185435 3688031 := bstep (se 1 (by rfl) ⟨2766023, by rfl⟩ : syracuseStep 3688031 = 5532047) B5532047
theorem B2458687 : Blo 2185435 2458687 := bstep (se 1 (by rfl) ⟨1844015, by rfl⟩ : syracuseStep 2458687 = 3688031) B3688031
theorem B3278249 : Blo 2185435 3278249 := bstep (se 2 (by rfl) ⟨1229343, by rfl⟩ : syracuseStep 3278249 = 2458687) B2458687
theorem B2185499 : Blo 2185435 2185499 := bstep (se 1 (by rfl) ⟨1639124, by rfl⟩ : syracuseStep 2185499 = 3278249) B3278249
theorem B8298085 : Blo 2185435 8298085 := bbase (se 4 (by rfl) ⟨777945, by rfl⟩ : syracuseStep 8298085 = 1555891) (by norm_num)
theorem B11064113 : Blo 2185435 11064113 := bstep (se 2 (by rfl) ⟨4149042, by rfl⟩ : syracuseStep 11064113 = 8298085) B8298085
theorem B7376075 : Blo 2185435 7376075 := bstep (se 1 (by rfl) ⟨5532056, by rfl⟩ : syracuseStep 7376075 = 11064113) B11064113
theorem B4917383 : Blo 2185435 4917383 := bstep (se 1 (by rfl) ⟨3688037, by rfl⟩ : syracuseStep 4917383 = 7376075) B7376075
theorem B3278255 : Blo 2185435 3278255 := bstep (se 1 (by rfl) ⟨2458691, by rfl⟩ : syracuseStep 3278255 = 4917383) B4917383
theorem B2185503 : Blo 2185435 2185503 := bstep (se 1 (by rfl) ⟨1639127, by rfl⟩ : syracuseStep 2185503 = 3278255) B3278255
theorem B3278261 : Blo 2185435 3278261 := bbase (se 5 (by rfl) ⟨153668, by rfl⟩ : syracuseStep 3278261 = 307337) (by norm_num)
theorem B2185507 : Blo 2185435 2185507 := bstep (se 1 (by rfl) ⟨1639130, by rfl⟩ : syracuseStep 2185507 = 3278261) B3278261
theorem B5532077 : Blo 2185435 5532077 := bbase (se 3 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 5532077 = 2074529) (by norm_num)
theorem B3688051 : Blo 2185435 3688051 := bstep (se 1 (by rfl) ⟨2766038, by rfl⟩ : syracuseStep 3688051 = 5532077) B5532077
theorem B4917401 : Blo 2185435 4917401 := bstep (se 2 (by rfl) ⟨1844025, by rfl⟩ : syracuseStep 4917401 = 3688051) B3688051
theorem B3278267 : Blo 2185435 3278267 := bstep (se 1 (by rfl) ⟨2458700, by rfl⟩ : syracuseStep 3278267 = 4917401) B4917401
theorem B2185511 : Blo 2185435 2185511 := bstep (se 1 (by rfl) ⟨1639133, by rfl⟩ : syracuseStep 2185511 = 3278267) B3278267
theorem B2458705 : Blo 2185435 2458705 := bbase (se 2 (by rfl) ⟨922014, by rfl⟩ : syracuseStep 2458705 = 1844029) (by norm_num)
theorem B3278273 : Blo 2185435 3278273 := bstep (se 2 (by rfl) ⟨1229352, by rfl⟩ : syracuseStep 3278273 = 2458705) B2458705
theorem B2185515 : Blo 2185435 2185515 := bstep (se 1 (by rfl) ⟨1639136, by rfl⟩ : syracuseStep 2185515 = 3278273) B3278273
theorem B3111805 : Blo 2185435 3111805 := bbase (se 3 (by rfl) ⟨583463, by rfl⟩ : syracuseStep 3111805 = 1166927) (by norm_num)
theorem B4149073 : Blo 2185435 4149073 := bstep (se 2 (by rfl) ⟨1555902, by rfl⟩ : syracuseStep 4149073 = 3111805) B3111805
theorem B5532097 : Blo 2185435 5532097 := bstep (se 2 (by rfl) ⟨2074536, by rfl⟩ : syracuseStep 5532097 = 4149073) B4149073
theorem B7376129 : Blo 2185435 7376129 := bstep (se 2 (by rfl) ⟨2766048, by rfl⟩ : syracuseStep 7376129 = 5532097) B5532097
theorem B4917419 : Blo 2185435 4917419 := bstep (se 1 (by rfl) ⟨3688064, by rfl⟩ : syracuseStep 4917419 = 7376129) B7376129
theorem B3278279 : Blo 2185435 3278279 := bstep (se 1 (by rfl) ⟨2458709, by rfl⟩ : syracuseStep 3278279 = 4917419) B4917419
theorem B2185519 : Blo 2185435 2185519 := bstep (se 1 (by rfl) ⟨1639139, by rfl⟩ : syracuseStep 2185519 = 3278279) B3278279
theorem B3278285 : Blo 2185435 3278285 := bbase (se 3 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 3278285 = 1229357) (by norm_num)
theorem B2185523 : Blo 2185435 2185523 := bstep (se 1 (by rfl) ⟨1639142, by rfl⟩ : syracuseStep 2185523 = 3278285) B3278285
theorem B4917437 : Blo 2185435 4917437 := bbase (se 3 (by rfl) ⟨922019, by rfl⟩ : syracuseStep 4917437 = 1844039) (by norm_num)
theorem B3278291 : Blo 2185435 3278291 := bstep (se 1 (by rfl) ⟨2458718, by rfl⟩ : syracuseStep 3278291 = 4917437) B4917437
theorem B2185527 : Blo 2185435 2185527 := bstep (se 1 (by rfl) ⟨1639145, by rfl⟩ : syracuseStep 2185527 = 3278291) B3278291
theorem B3688085 : Blo 2185435 3688085 := bbase (se 6 (by rfl) ⟨86439, by rfl⟩ : syracuseStep 3688085 = 172879) (by norm_num)
theorem B2458723 : Blo 2185435 2458723 := bstep (se 1 (by rfl) ⟨1844042, by rfl⟩ : syracuseStep 2458723 = 3688085) B3688085
theorem B3278297 : Blo 2185435 3278297 := bstep (se 2 (by rfl) ⟨1229361, by rfl⟩ : syracuseStep 3278297 = 2458723) B2458723
theorem B2185531 : Blo 2185435 2185531 := bstep (se 1 (by rfl) ⟨1639148, by rfl⟩ : syracuseStep 2185531 = 3278297) B3278297
theorem B9462853 : Blo 2185435 9462853 := bbase (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) (by norm_num)
theorem B12617137 : Blo 2185435 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B16822849 : Blo 2185435 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B22430465 : Blo 2185435 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B14953643 : Blo 2185435 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B9969095 : Blo 2185435 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B6646063 : Blo 2185435 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B8861417 : Blo 2185435 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B5907611 : Blo 2185435 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B15753629 : Blo 2185435 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B10502419 : Blo 2185435 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B14003225 : Blo 2185435 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B9335483 : Blo 2185435 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B6223655 : Blo 2185435 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B16596413 : Blo 2185435 16596413 := bstep (se 3 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 16596413 = 6223655) B6223655
theorem B11064275 : Blo 2185435 11064275 := bstep (se 1 (by rfl) ⟨8298206, by rfl⟩ : syracuseStep 11064275 = 16596413) B16596413
theorem B7376183 : Blo 2185435 7376183 := bstep (se 1 (by rfl) ⟨5532137, by rfl⟩ : syracuseStep 7376183 = 11064275) B11064275
theorem B4917455 : Blo 2185435 4917455 := bstep (se 1 (by rfl) ⟨3688091, by rfl⟩ : syracuseStep 4917455 = 7376183) B7376183
theorem B3278303 : Blo 2185435 3278303 := bstep (se 1 (by rfl) ⟨2458727, by rfl⟩ : syracuseStep 3278303 = 4917455) B4917455
theorem B2185535 : Blo 2185435 2185535 := bstep (se 1 (by rfl) ⟨1639151, by rfl⟩ : syracuseStep 2185535 = 3278303) B3278303
theorem B3278309 : Blo 2185435 3278309 := bbase (se 4 (by rfl) ⟨307341, by rfl⟩ : syracuseStep 3278309 = 614683) (by norm_num)
theorem B2185539 : Blo 2185435 2185539 := bstep (se 1 (by rfl) ⟨1639154, by rfl⟩ : syracuseStep 2185539 = 3278309) B3278309
theorem B17722901 : Blo 2185435 17722901 := bbase (se 6 (by rfl) ⟨415380, by rfl⟩ : syracuseStep 17722901 = 830761) (by norm_num)
theorem B47261069 : Blo 2185435 47261069 := bstep (se 3 (by rfl) ⟨8861450, by rfl⟩ : syracuseStep 47261069 = 17722901) B17722901
theorem B31507379 : Blo 2185435 31507379 := bstep (se 1 (by rfl) ⟨23630534, by rfl⟩ : syracuseStep 31507379 = 47261069) B47261069
theorem B21004919 : Blo 2185435 21004919 := bstep (se 1 (by rfl) ⟨15753689, by rfl⟩ : syracuseStep 21004919 = 31507379) B31507379
theorem B14003279 : Blo 2185435 14003279 := bstep (se 1 (by rfl) ⟨10502459, by rfl⟩ : syracuseStep 14003279 = 21004919) B21004919
theorem B9335519 : Blo 2185435 9335519 := bstep (se 1 (by rfl) ⟨7001639, by rfl⟩ : syracuseStep 9335519 = 14003279) B14003279
theorem B6223679 : Blo 2185435 6223679 := bstep (se 1 (by rfl) ⟨4667759, by rfl⟩ : syracuseStep 6223679 = 9335519) B9335519
theorem B4149119 : Blo 2185435 4149119 := bstep (se 1 (by rfl) ⟨3111839, by rfl⟩ : syracuseStep 4149119 = 6223679) B6223679
theorem B2766079 : Blo 2185435 2766079 := bstep (se 1 (by rfl) ⟨2074559, by rfl⟩ : syracuseStep 2766079 = 4149119) B4149119
theorem B3688105 : Blo 2185435 3688105 := bstep (se 2 (by rfl) ⟨1383039, by rfl⟩ : syracuseStep 3688105 = 2766079) B2766079
theorem B4917473 : Blo 2185435 4917473 := bstep (se 2 (by rfl) ⟨1844052, by rfl⟩ : syracuseStep 4917473 = 3688105) B3688105
theorem B3278315 : Blo 2185435 3278315 := bstep (se 1 (by rfl) ⟨2458736, by rfl⟩ : syracuseStep 3278315 = 4917473) B4917473
theorem B2185543 : Blo 2185435 2185543 := bstep (se 1 (by rfl) ⟨1639157, by rfl⟩ : syracuseStep 2185543 = 3278315) B3278315
theorem B2458741 : Blo 2185435 2458741 := bbase (se 5 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 2458741 = 230507) (by norm_num)
theorem B3278321 : Blo 2185435 3278321 := bstep (se 2 (by rfl) ⟨1229370, by rfl⟩ : syracuseStep 3278321 = 2458741) B2458741
theorem B2185547 : Blo 2185435 2185547 := bstep (se 1 (by rfl) ⟨1639160, by rfl⟩ : syracuseStep 2185547 = 3278321) B3278321
theorem B2766089 : Blo 2185435 2766089 := bbase (se 2 (by rfl) ⟨1037283, by rfl⟩ : syracuseStep 2766089 = 2074567) (by norm_num)
theorem B7376237 : Blo 2185435 7376237 := bstep (se 3 (by rfl) ⟨1383044, by rfl⟩ : syracuseStep 7376237 = 2766089) B2766089
theorem B4917491 : Blo 2185435 4917491 := bstep (se 1 (by rfl) ⟨3688118, by rfl⟩ : syracuseStep 4917491 = 7376237) B7376237
theorem B3278327 : Blo 2185435 3278327 := bstep (se 1 (by rfl) ⟨2458745, by rfl⟩ : syracuseStep 3278327 = 4917491) B4917491
theorem B2185551 : Blo 2185435 2185551 := bstep (se 1 (by rfl) ⟨1639163, by rfl⟩ : syracuseStep 2185551 = 3278327) B3278327
theorem B3278333 : Blo 2185435 3278333 := bbase (se 3 (by rfl) ⟨614687, by rfl⟩ : syracuseStep 3278333 = 1229375) (by norm_num)
theorem B2185555 : Blo 2185435 2185555 := bstep (se 1 (by rfl) ⟨1639166, by rfl⟩ : syracuseStep 2185555 = 3278333) B3278333
theorem B4917509 : Blo 2185435 4917509 := bbase (se 4 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 4917509 = 922033) (by norm_num)
theorem B3278339 : Blo 2185435 3278339 := bstep (se 1 (by rfl) ⟨2458754, by rfl⟩ : syracuseStep 3278339 = 4917509) B4917509
theorem B2185559 : Blo 2185435 2185559 := bstep (se 1 (by rfl) ⟨1639169, by rfl⟩ : syracuseStep 2185559 = 3278339) B3278339
theorem B4149157 : Blo 2185435 4149157 := bbase (se 4 (by rfl) ⟨388983, by rfl⟩ : syracuseStep 4149157 = 777967) (by norm_num)
theorem B5532209 : Blo 2185435 5532209 := bstep (se 2 (by rfl) ⟨2074578, by rfl⟩ : syracuseStep 5532209 = 4149157) B4149157
theorem B3688139 : Blo 2185435 3688139 := bstep (se 1 (by rfl) ⟨2766104, by rfl⟩ : syracuseStep 3688139 = 5532209) B5532209
theorem B2458759 : Blo 2185435 2458759 := bstep (se 1 (by rfl) ⟨1844069, by rfl⟩ : syracuseStep 2458759 = 3688139) B3688139
theorem B3278345 : Blo 2185435 3278345 := bstep (se 2 (by rfl) ⟨1229379, by rfl⟩ : syracuseStep 3278345 = 2458759) B2458759
theorem B2185563 : Blo 2185435 2185563 := bstep (se 1 (by rfl) ⟨1639172, by rfl⟩ : syracuseStep 2185563 = 3278345) B3278345
theorem B11064437 : Blo 2185435 11064437 := bbase (se 5 (by rfl) ⟨518645, by rfl⟩ : syracuseStep 11064437 = 1037291) (by norm_num)
theorem B7376291 : Blo 2185435 7376291 := bstep (se 1 (by rfl) ⟨5532218, by rfl⟩ : syracuseStep 7376291 = 11064437) B11064437
theorem B4917527 : Blo 2185435 4917527 := bstep (se 1 (by rfl) ⟨3688145, by rfl⟩ : syracuseStep 4917527 = 7376291) B7376291
theorem B3278351 : Blo 2185435 3278351 := bstep (se 1 (by rfl) ⟨2458763, by rfl⟩ : syracuseStep 3278351 = 4917527) B4917527
theorem B2185567 : Blo 2185435 2185567 := bstep (se 1 (by rfl) ⟨1639175, by rfl⟩ : syracuseStep 2185567 = 3278351) B3278351
theorem B3278357 : Blo 2185435 3278357 := bbase (se 6 (by rfl) ⟨76836, by rfl⟩ : syracuseStep 3278357 = 153673) (by norm_num)
theorem B2185571 : Blo 2185435 2185571 := bstep (se 1 (by rfl) ⟨1639178, by rfl⟩ : syracuseStep 2185571 = 3278357) B3278357
theorem B2625653 : Blo 2185435 2625653 := bbase (se 5 (by rfl) ⟨123077, by rfl⟩ : syracuseStep 2625653 = 246155) (by norm_num)
theorem B7001741 : Blo 2185435 7001741 := bstep (se 3 (by rfl) ⟨1312826, by rfl⟩ : syracuseStep 7001741 = 2625653) B2625653
theorem B18671309 : Blo 2185435 18671309 := bstep (se 3 (by rfl) ⟨3500870, by rfl⟩ : syracuseStep 18671309 = 7001741) B7001741
theorem B12447539 : Blo 2185435 12447539 := bstep (se 1 (by rfl) ⟨9335654, by rfl⟩ : syracuseStep 12447539 = 18671309) B18671309
theorem B8298359 : Blo 2185435 8298359 := bstep (se 1 (by rfl) ⟨6223769, by rfl⟩ : syracuseStep 8298359 = 12447539) B12447539
theorem B5532239 : Blo 2185435 5532239 := bstep (se 1 (by rfl) ⟨4149179, by rfl⟩ : syracuseStep 5532239 = 8298359) B8298359
theorem B3688159 : Blo 2185435 3688159 := bstep (se 1 (by rfl) ⟨2766119, by rfl⟩ : syracuseStep 3688159 = 5532239) B5532239
theorem B4917545 : Blo 2185435 4917545 := bstep (se 2 (by rfl) ⟨1844079, by rfl⟩ : syracuseStep 4917545 = 3688159) B3688159
theorem B3278363 : Blo 2185435 3278363 := bstep (se 1 (by rfl) ⟨2458772, by rfl⟩ : syracuseStep 3278363 = 4917545) B4917545
theorem B2185575 : Blo 2185435 2185575 := bstep (se 1 (by rfl) ⟨1639181, by rfl⟩ : syracuseStep 2185575 = 3278363) B3278363
theorem B2458777 : Blo 2185435 2458777 := bbase (se 2 (by rfl) ⟨922041, by rfl⟩ : syracuseStep 2458777 = 1844083) (by norm_num)
theorem B3278369 : Blo 2185435 3278369 := bstep (se 2 (by rfl) ⟨1229388, by rfl⟩ : syracuseStep 3278369 = 2458777) B2458777
theorem B2185579 : Blo 2185435 2185579 := bstep (se 1 (by rfl) ⟨1639184, by rfl⟩ : syracuseStep 2185579 = 3278369) B3278369
theorem B8298389 : Blo 2185435 8298389 := bbase (se 6 (by rfl) ⟨194493, by rfl⟩ : syracuseStep 8298389 = 388987) (by norm_num)
theorem B5532259 : Blo 2185435 5532259 := bstep (se 1 (by rfl) ⟨4149194, by rfl⟩ : syracuseStep 5532259 = 8298389) B8298389
theorem B7376345 : Blo 2185435 7376345 := bstep (se 2 (by rfl) ⟨2766129, by rfl⟩ : syracuseStep 7376345 = 5532259) B5532259
theorem B4917563 : Blo 2185435 4917563 := bstep (se 1 (by rfl) ⟨3688172, by rfl⟩ : syracuseStep 4917563 = 7376345) B7376345
theorem B3278375 : Blo 2185435 3278375 := bstep (se 1 (by rfl) ⟨2458781, by rfl⟩ : syracuseStep 3278375 = 4917563) B4917563
theorem B2185583 : Blo 2185435 2185583 := bstep (se 1 (by rfl) ⟨1639187, by rfl⟩ : syracuseStep 2185583 = 3278375) B3278375
theorem B3278381 : Blo 2185435 3278381 := bbase (se 3 (by rfl) ⟨614696, by rfl⟩ : syracuseStep 3278381 = 1229393) (by norm_num)
theorem B2185587 : Blo 2185435 2185587 := bstep (se 1 (by rfl) ⟨1639190, by rfl⟩ : syracuseStep 2185587 = 3278381) B3278381
theorem B4917581 : Blo 2185435 4917581 := bbase (se 3 (by rfl) ⟨922046, by rfl⟩ : syracuseStep 4917581 = 1844093) (by norm_num)
theorem B3278387 : Blo 2185435 3278387 := bstep (se 1 (by rfl) ⟨2458790, by rfl⟩ : syracuseStep 3278387 = 4917581) B4917581
theorem B2185591 : Blo 2185435 2185591 := bstep (se 1 (by rfl) ⟨1639193, by rfl⟩ : syracuseStep 2185591 = 3278387) B3278387
theorem B2766145 : Blo 2185435 2766145 := bbase (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) (by norm_num)
theorem B3688193 : Blo 2185435 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B2458795 : Blo 2185435 2458795 := bstep (se 1 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 2458795 = 3688193) B3688193
theorem B3278393 : Blo 2185435 3278393 := bstep (se 2 (by rfl) ⟨1229397, by rfl⟩ : syracuseStep 3278393 = 2458795) B2458795
theorem B2185595 : Blo 2185435 2185595 := bstep (se 1 (by rfl) ⟨1639196, by rfl⟩ : syracuseStep 2185595 = 3278393) B3278393
theorem B3500909 : Blo 2185435 3500909 := bbase (se 3 (by rfl) ⟨656420, by rfl⟩ : syracuseStep 3500909 = 1312841) (by norm_num)
theorem B2333939 : Blo 2185435 2333939 := bstep (se 1 (by rfl) ⟨1750454, by rfl⟩ : syracuseStep 2333939 = 3500909) B3500909
theorem B24895349 : Blo 2185435 24895349 := bstep (se 5 (by rfl) ⟨1166969, by rfl⟩ : syracuseStep 24895349 = 2333939) B2333939
theorem B16596899 : Blo 2185435 16596899 := bstep (se 1 (by rfl) ⟨12447674, by rfl⟩ : syracuseStep 16596899 = 24895349) B24895349
theorem B11064599 : Blo 2185435 11064599 := bstep (se 1 (by rfl) ⟨8298449, by rfl⟩ : syracuseStep 11064599 = 16596899) B16596899
theorem B7376399 : Blo 2185435 7376399 := bstep (se 1 (by rfl) ⟨5532299, by rfl⟩ : syracuseStep 7376399 = 11064599) B11064599
theorem B4917599 : Blo 2185435 4917599 := bstep (se 1 (by rfl) ⟨3688199, by rfl⟩ : syracuseStep 4917599 = 7376399) B7376399
theorem B3278399 : Blo 2185435 3278399 := bstep (se 1 (by rfl) ⟨2458799, by rfl⟩ : syracuseStep 3278399 = 4917599) B4917599
theorem B2185599 : Blo 2185435 2185599 := bstep (se 1 (by rfl) ⟨1639199, by rfl⟩ : syracuseStep 2185599 = 3278399) B3278399
theorem B3278405 : Blo 2185435 3278405 := bbase (se 4 (by rfl) ⟨307350, by rfl⟩ : syracuseStep 3278405 = 614701) (by norm_num)
theorem B2185603 : Blo 2185435 2185603 := bstep (se 1 (by rfl) ⟨1639202, by rfl⟩ : syracuseStep 2185603 = 3278405) B3278405
theorem B3688213 : Blo 2185435 3688213 := bbase (se 6 (by rfl) ⟨86442, by rfl⟩ : syracuseStep 3688213 = 172885) (by norm_num)
theorem B4917617 : Blo 2185435 4917617 := bstep (se 2 (by rfl) ⟨1844106, by rfl⟩ : syracuseStep 4917617 = 3688213) B3688213
theorem B3278411 : Blo 2185435 3278411 := bstep (se 1 (by rfl) ⟨2458808, by rfl⟩ : syracuseStep 3278411 = 4917617) B4917617
theorem B2185607 : Blo 2185435 2185607 := bstep (se 1 (by rfl) ⟨1639205, by rfl⟩ : syracuseStep 2185607 = 3278411) B3278411
theorem B2458813 : Blo 2185435 2458813 := bbase (se 3 (by rfl) ⟨461027, by rfl⟩ : syracuseStep 2458813 = 922055) (by norm_num)
theorem B3278417 : Blo 2185435 3278417 := bstep (se 2 (by rfl) ⟨1229406, by rfl⟩ : syracuseStep 3278417 = 2458813) B2458813
theorem B2185611 : Blo 2185435 2185611 := bstep (se 1 (by rfl) ⟨1639208, by rfl⟩ : syracuseStep 2185611 = 3278417) B3278417
theorem B7376453 : Blo 2185435 7376453 := bbase (se 4 (by rfl) ⟨691542, by rfl⟩ : syracuseStep 7376453 = 1383085) (by norm_num)
theorem B4917635 : Blo 2185435 4917635 := bstep (se 1 (by rfl) ⟨3688226, by rfl⟩ : syracuseStep 4917635 = 7376453) B7376453
theorem B3278423 : Blo 2185435 3278423 := bstep (se 1 (by rfl) ⟨2458817, by rfl⟩ : syracuseStep 3278423 = 4917635) B4917635
theorem B2185615 : Blo 2185435 2185615 := bstep (se 1 (by rfl) ⟨1639211, by rfl⟩ : syracuseStep 2185615 = 3278423) B3278423
theorem B3278429 : Blo 2185435 3278429 := bbase (se 3 (by rfl) ⟨614705, by rfl⟩ : syracuseStep 3278429 = 1229411) (by norm_num)
theorem B2185619 : Blo 2185435 2185619 := bstep (se 1 (by rfl) ⟨1639214, by rfl⟩ : syracuseStep 2185619 = 3278429) B3278429
theorem B4917653 : Blo 2185435 4917653 := bbase (se 6 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 4917653 = 230515) (by norm_num)
theorem B3278435 : Blo 2185435 3278435 := bstep (se 1 (by rfl) ⟨2458826, by rfl⟩ : syracuseStep 3278435 = 4917653) B4917653
theorem B2185623 : Blo 2185435 2185623 := bstep (se 1 (by rfl) ⟨1639217, by rfl⟩ : syracuseStep 2185623 = 3278435) B3278435
theorem B7001909 : Blo 2185435 7001909 := bbase (se 5 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 7001909 = 656429) (by norm_num)
theorem B4667939 : Blo 2185435 4667939 := bstep (se 1 (by rfl) ⟨3500954, by rfl⟩ : syracuseStep 4667939 = 7001909) B7001909
theorem B3111959 : Blo 2185435 3111959 := bstep (se 1 (by rfl) ⟨2333969, by rfl⟩ : syracuseStep 3111959 = 4667939) B4667939
theorem B8298557 : Blo 2185435 8298557 := bstep (se 3 (by rfl) ⟨1555979, by rfl⟩ : syracuseStep 8298557 = 3111959) B3111959
theorem B5532371 : Blo 2185435 5532371 := bstep (se 1 (by rfl) ⟨4149278, by rfl⟩ : syracuseStep 5532371 = 8298557) B8298557
theorem B3688247 : Blo 2185435 3688247 := bstep (se 1 (by rfl) ⟨2766185, by rfl⟩ : syracuseStep 3688247 = 5532371) B5532371
theorem B2458831 : Blo 2185435 2458831 := bstep (se 1 (by rfl) ⟨1844123, by rfl⟩ : syracuseStep 2458831 = 3688247) B3688247
theorem B3278441 : Blo 2185435 3278441 := bstep (se 2 (by rfl) ⟨1229415, by rfl⟩ : syracuseStep 3278441 = 2458831) B2458831
theorem B2185627 : Blo 2185435 2185627 := bstep (se 1 (by rfl) ⟨1639220, by rfl⟩ : syracuseStep 2185627 = 3278441) B3278441
theorem B9335893 : Blo 2185435 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B12447857 : Blo 2185435 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B8298571 : Blo 2185435 8298571 := bstep (se 1 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 8298571 = 12447857) B12447857
theorem B11064761 : Blo 2185435 11064761 := bstep (se 2 (by rfl) ⟨4149285, by rfl⟩ : syracuseStep 11064761 = 8298571) B8298571
theorem B7376507 : Blo 2185435 7376507 := bstep (se 1 (by rfl) ⟨5532380, by rfl⟩ : syracuseStep 7376507 = 11064761) B11064761
theorem B4917671 : Blo 2185435 4917671 := bstep (se 1 (by rfl) ⟨3688253, by rfl⟩ : syracuseStep 4917671 = 7376507) B7376507
theorem B3278447 : Blo 2185435 3278447 := bstep (se 1 (by rfl) ⟨2458835, by rfl⟩ : syracuseStep 3278447 = 4917671) B4917671
theorem B2185631 : Blo 2185435 2185631 := bstep (se 1 (by rfl) ⟨1639223, by rfl⟩ : syracuseStep 2185631 = 3278447) B3278447
theorem B3278453 : Blo 2185435 3278453 := bbase (se 5 (by rfl) ⟨153677, by rfl⟩ : syracuseStep 3278453 = 307355) (by norm_num)
theorem B2185635 : Blo 2185435 2185635 := bstep (se 1 (by rfl) ⟨1639226, by rfl⟩ : syracuseStep 2185635 = 3278453) B3278453
theorem B4149301 : Blo 2185435 4149301 := bbase (se 5 (by rfl) ⟨194498, by rfl⟩ : syracuseStep 4149301 = 388997) (by norm_num)
theorem B5532401 : Blo 2185435 5532401 := bstep (se 2 (by rfl) ⟨2074650, by rfl⟩ : syracuseStep 5532401 = 4149301) B4149301
theorem B3688267 : Blo 2185435 3688267 := bstep (se 1 (by rfl) ⟨2766200, by rfl⟩ : syracuseStep 3688267 = 5532401) B5532401
theorem B4917689 : Blo 2185435 4917689 := bstep (se 2 (by rfl) ⟨1844133, by rfl⟩ : syracuseStep 4917689 = 3688267) B3688267
theorem B3278459 : Blo 2185435 3278459 := bstep (se 1 (by rfl) ⟨2458844, by rfl⟩ : syracuseStep 3278459 = 4917689) B4917689
theorem B2185639 : Blo 2185435 2185639 := bstep (se 1 (by rfl) ⟨1639229, by rfl⟩ : syracuseStep 2185639 = 3278459) B3278459
theorem B2458849 : Blo 2185435 2458849 := bbase (se 2 (by rfl) ⟨922068, by rfl⟩ : syracuseStep 2458849 = 1844137) (by norm_num)
theorem B3278465 : Blo 2185435 3278465 := bstep (se 2 (by rfl) ⟨1229424, by rfl⟩ : syracuseStep 3278465 = 2458849) B2458849
theorem B2185643 : Blo 2185435 2185643 := bstep (se 1 (by rfl) ⟨1639232, by rfl⟩ : syracuseStep 2185643 = 3278465) B3278465
theorem B5532421 : Blo 2185435 5532421 := bbase (se 4 (by rfl) ⟨518664, by rfl⟩ : syracuseStep 5532421 = 1037329) (by norm_num)
theorem B7376561 : Blo 2185435 7376561 := bstep (se 2 (by rfl) ⟨2766210, by rfl⟩ : syracuseStep 7376561 = 5532421) B5532421
theorem B4917707 : Blo 2185435 4917707 := bstep (se 1 (by rfl) ⟨3688280, by rfl⟩ : syracuseStep 4917707 = 7376561) B7376561
theorem B3278471 : Blo 2185435 3278471 := bstep (se 1 (by rfl) ⟨2458853, by rfl⟩ : syracuseStep 3278471 = 4917707) B4917707
theorem B2185647 : Blo 2185435 2185647 := bstep (se 1 (by rfl) ⟨1639235, by rfl⟩ : syracuseStep 2185647 = 3278471) B3278471
theorem B3278477 : Blo 2185435 3278477 := bbase (se 3 (by rfl) ⟨614714, by rfl⟩ : syracuseStep 3278477 = 1229429) (by norm_num)
theorem B2185651 : Blo 2185435 2185651 := bstep (se 1 (by rfl) ⟨1639238, by rfl⟩ : syracuseStep 2185651 = 3278477) B3278477
theorem B4917725 : Blo 2185435 4917725 := bbase (se 3 (by rfl) ⟨922073, by rfl⟩ : syracuseStep 4917725 = 1844147) (by norm_num)
theorem B3278483 : Blo 2185435 3278483 := bstep (se 1 (by rfl) ⟨2458862, by rfl⟩ : syracuseStep 3278483 = 4917725) B4917725
theorem B2185655 : Blo 2185435 2185655 := bstep (se 1 (by rfl) ⟨1639241, by rfl⟩ : syracuseStep 2185655 = 3278483) B3278483
theorem B3688301 : Blo 2185435 3688301 := bbase (se 3 (by rfl) ⟨691556, by rfl⟩ : syracuseStep 3688301 = 1383113) (by norm_num)
theorem B2458867 : Blo 2185435 2458867 := bstep (se 1 (by rfl) ⟨1844150, by rfl⟩ : syracuseStep 2458867 = 3688301) B3688301
theorem B3278489 : Blo 2185435 3278489 := bstep (se 2 (by rfl) ⟨1229433, by rfl⟩ : syracuseStep 3278489 = 2458867) B2458867
theorem B2185659 : Blo 2185435 2185659 := bstep (se 1 (by rfl) ⟨1639244, by rfl⟩ : syracuseStep 2185659 = 3278489) B3278489
theorem B4491421 : Blo 2185435 4491421 := bbase (se 3 (by rfl) ⟨842141, by rfl⟩ : syracuseStep 4491421 = 1684283) (by norm_num)
theorem B95816981 : Blo 2185435 95816981 := bstep (se 6 (by rfl) ⟨2245710, by rfl⟩ : syracuseStep 95816981 = 4491421) B4491421
theorem B63877987 : Blo 2185435 63877987 := bstep (se 1 (by rfl) ⟨47908490, by rfl⟩ : syracuseStep 63877987 = 95816981) B95816981
theorem B85170649 : Blo 2185435 85170649 := bstep (se 2 (by rfl) ⟨31938993, by rfl⟩ : syracuseStep 85170649 = 63877987) B63877987
theorem B113560865 : Blo 2185435 113560865 := bstep (se 2 (by rfl) ⟨42585324, by rfl⟩ : syracuseStep 113560865 = 85170649) B85170649
theorem B75707243 : Blo 2185435 75707243 := bstep (se 1 (by rfl) ⟨56780432, by rfl⟩ : syracuseStep 75707243 = 113560865) B113560865
theorem B50471495 : Blo 2185435 50471495 := bstep (se 1 (by rfl) ⟨37853621, by rfl⟩ : syracuseStep 50471495 = 75707243) B75707243
theorem B33647663 : Blo 2185435 33647663 := bstep (se 1 (by rfl) ⟨25235747, by rfl⟩ : syracuseStep 33647663 = 50471495) B50471495
theorem B22431775 : Blo 2185435 22431775 := bstep (se 1 (by rfl) ⟨16823831, by rfl⟩ : syracuseStep 22431775 = 33647663) B33647663
theorem B29909033 : Blo 2185435 29909033 := bstep (se 2 (by rfl) ⟨11215887, by rfl⟩ : syracuseStep 29909033 = 22431775) B22431775
theorem B19939355 : Blo 2185435 19939355 := bstep (se 1 (by rfl) ⟨14954516, by rfl⟩ : syracuseStep 19939355 = 29909033) B29909033
theorem B13292903 : Blo 2185435 13292903 := bstep (se 1 (by rfl) ⟨9969677, by rfl⟩ : syracuseStep 13292903 = 19939355) B19939355
theorem B8861935 : Blo 2185435 8861935 := bstep (se 1 (by rfl) ⟨6646451, by rfl⟩ : syracuseStep 8861935 = 13292903) B13292903
theorem B11815913 : Blo 2185435 11815913 := bstep (se 2 (by rfl) ⟨4430967, by rfl⟩ : syracuseStep 11815913 = 8861935) B8861935
theorem B31509101 : Blo 2185435 31509101 := bstep (se 3 (by rfl) ⟨5907956, by rfl⟩ : syracuseStep 31509101 = 11815913) B11815913
theorem B21006067 : Blo 2185435 21006067 := bstep (se 1 (by rfl) ⟨15754550, by rfl⟩ : syracuseStep 21006067 = 31509101) B31509101
theorem B28008089 : Blo 2185435 28008089 := bstep (se 2 (by rfl) ⟨10503033, by rfl⟩ : syracuseStep 28008089 = 21006067) B21006067
theorem B18672059 : Blo 2185435 18672059 := bstep (se 1 (by rfl) ⟨14004044, by rfl⟩ : syracuseStep 18672059 = 28008089) B28008089
theorem B12448039 : Blo 2185435 12448039 := bstep (se 1 (by rfl) ⟨9336029, by rfl⟩ : syracuseStep 12448039 = 18672059) B18672059
theorem B16597385 : Blo 2185435 16597385 := bstep (se 2 (by rfl) ⟨6224019, by rfl⟩ : syracuseStep 16597385 = 12448039) B12448039
theorem B11064923 : Blo 2185435 11064923 := bstep (se 1 (by rfl) ⟨8298692, by rfl⟩ : syracuseStep 11064923 = 16597385) B16597385
theorem B7376615 : Blo 2185435 7376615 := bstep (se 1 (by rfl) ⟨5532461, by rfl⟩ : syracuseStep 7376615 = 11064923) B11064923
theorem B4917743 : Blo 2185435 4917743 := bstep (se 1 (by rfl) ⟨3688307, by rfl⟩ : syracuseStep 4917743 = 7376615) B7376615
theorem B3278495 : Blo 2185435 3278495 := bstep (se 1 (by rfl) ⟨2458871, by rfl⟩ : syracuseStep 3278495 = 4917743) B4917743
theorem B2185663 : Blo 2185435 2185663 := bstep (se 1 (by rfl) ⟨1639247, by rfl⟩ : syracuseStep 2185663 = 3278495) B3278495
theorem B3278501 : Blo 2185435 3278501 := bbase (se 4 (by rfl) ⟨307359, by rfl⟩ : syracuseStep 3278501 = 614719) (by norm_num)
theorem B2185667 : Blo 2185435 2185667 := bstep (se 1 (by rfl) ⟨1639250, by rfl⟩ : syracuseStep 2185667 = 3278501) B3278501
theorem B2766241 : Blo 2185435 2766241 := bbase (se 2 (by rfl) ⟨1037340, by rfl⟩ : syracuseStep 2766241 = 2074681) (by norm_num)
theorem B3688321 : Blo 2185435 3688321 := bstep (se 2 (by rfl) ⟨1383120, by rfl⟩ : syracuseStep 3688321 = 2766241) B2766241
theorem B4917761 : Blo 2185435 4917761 := bstep (se 2 (by rfl) ⟨1844160, by rfl⟩ : syracuseStep 4917761 = 3688321) B3688321
theorem B3278507 : Blo 2185435 3278507 := bstep (se 1 (by rfl) ⟨2458880, by rfl⟩ : syracuseStep 3278507 = 4917761) B4917761
theorem B2185671 : Blo 2185435 2185671 := bstep (se 1 (by rfl) ⟨1639253, by rfl⟩ : syracuseStep 2185671 = 3278507) B3278507
theorem B2458885 : Blo 2185435 2458885 := bbase (se 4 (by rfl) ⟨230520, by rfl⟩ : syracuseStep 2458885 = 461041) (by norm_num)
theorem B3278513 : Blo 2185435 3278513 := bstep (se 2 (by rfl) ⟨1229442, by rfl⟩ : syracuseStep 3278513 = 2458885) B2458885
theorem B2185675 : Blo 2185435 2185675 := bstep (se 1 (by rfl) ⟨1639256, by rfl⟩ : syracuseStep 2185675 = 3278513) B3278513
theorem B2334025 : Blo 2185435 2334025 := bbase (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) (by norm_num)
theorem B3112033 : Blo 2185435 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B4149377 : Blo 2185435 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B2766251 : Blo 2185435 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B7376669 : Blo 2185435 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B4917779 : Blo 2185435 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B3278519 : Blo 2185435 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B2185679 : Blo 2185435 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B3278525 : Blo 2185435 3278525 := bbase (se 3 (by rfl) ⟨614723, by rfl⟩ : syracuseStep 3278525 = 1229447) (by norm_num)
theorem B2185683 : Blo 2185435 2185683 := bstep (se 1 (by rfl) ⟨1639262, by rfl⟩ : syracuseStep 2185683 = 3278525) B3278525
theorem B4917797 : Blo 2185435 4917797 := bbase (se 4 (by rfl) ⟨461043, by rfl⟩ : syracuseStep 4917797 = 922087) (by norm_num)
theorem B3278531 : Blo 2185435 3278531 := bstep (se 1 (by rfl) ⟨2458898, by rfl⟩ : syracuseStep 3278531 = 4917797) B4917797
theorem B2185687 : Blo 2185435 2185687 := bstep (se 1 (by rfl) ⟨1639265, by rfl⟩ : syracuseStep 2185687 = 3278531) B3278531
theorem B5532533 : Blo 2185435 5532533 := bbase (se 5 (by rfl) ⟨259337, by rfl⟩ : syracuseStep 5532533 = 518675) (by norm_num)
theorem B3688355 : Blo 2185435 3688355 := bstep (se 1 (by rfl) ⟨2766266, by rfl⟩ : syracuseStep 3688355 = 5532533) B5532533
theorem B2458903 : Blo 2185435 2458903 := bstep (se 1 (by rfl) ⟨1844177, by rfl⟩ : syracuseStep 2458903 = 3688355) B3688355
theorem B3278537 : Blo 2185435 3278537 := bstep (se 2 (by rfl) ⟨1229451, by rfl⟩ : syracuseStep 3278537 = 2458903) B2458903
theorem B2185691 : Blo 2185435 2185691 := bstep (se 1 (by rfl) ⟨1639268, by rfl⟩ : syracuseStep 2185691 = 3278537) B3278537
theorem B14195317 : Blo 2185435 14195317 := bbase (se 5 (by rfl) ⟨665405, by rfl⟩ : syracuseStep 14195317 = 1330811) (by norm_num)
theorem B18927089 : Blo 2185435 18927089 := bstep (se 2 (by rfl) ⟨7097658, by rfl⟩ : syracuseStep 18927089 = 14195317) B14195317
theorem B12618059 : Blo 2185435 12618059 := bstep (se 1 (by rfl) ⟨9463544, by rfl⟩ : syracuseStep 12618059 = 18927089) B18927089
theorem B33648157 : Blo 2185435 33648157 := bstep (se 3 (by rfl) ⟨6309029, by rfl⟩ : syracuseStep 33648157 = 12618059) B12618059
theorem B44864209 : Blo 2185435 44864209 := bstep (se 2 (by rfl) ⟨16824078, by rfl⟩ : syracuseStep 44864209 = 33648157) B33648157
theorem B59818945 : Blo 2185435 59818945 := bstep (se 2 (by rfl) ⟨22432104, by rfl⟩ : syracuseStep 59818945 = 44864209) B44864209
theorem B79758593 : Blo 2185435 79758593 := bstep (se 2 (by rfl) ⟨29909472, by rfl⟩ : syracuseStep 79758593 = 59818945) B59818945
theorem B53172395 : Blo 2185435 53172395 := bstep (se 1 (by rfl) ⟨39879296, by rfl⟩ : syracuseStep 53172395 = 79758593) B79758593
theorem B35448263 : Blo 2185435 35448263 := bstep (se 1 (by rfl) ⟨26586197, by rfl⟩ : syracuseStep 35448263 = 53172395) B53172395
theorem B23632175 : Blo 2185435 23632175 := bstep (se 1 (by rfl) ⟨17724131, by rfl⟩ : syracuseStep 23632175 = 35448263) B35448263
theorem B15754783 : Blo 2185435 15754783 := bstep (se 1 (by rfl) ⟨11816087, by rfl⟩ : syracuseStep 15754783 = 23632175) B23632175
theorem B21006377 : Blo 2185435 21006377 := bstep (se 2 (by rfl) ⟨7877391, by rfl⟩ : syracuseStep 21006377 = 15754783) B15754783
theorem B14004251 : Blo 2185435 14004251 := bstep (se 1 (by rfl) ⟨10503188, by rfl⟩ : syracuseStep 14004251 = 21006377) B21006377
theorem B9336167 : Blo 2185435 9336167 := bstep (se 1 (by rfl) ⟨7002125, by rfl⟩ : syracuseStep 9336167 = 14004251) B14004251
theorem B6224111 : Blo 2185435 6224111 := bstep (se 1 (by rfl) ⟨4668083, by rfl⟩ : syracuseStep 6224111 = 9336167) B9336167
theorem B4149407 : Blo 2185435 4149407 := bstep (se 1 (by rfl) ⟨3112055, by rfl⟩ : syracuseStep 4149407 = 6224111) B6224111
theorem B11065085 : Blo 2185435 11065085 := bstep (se 3 (by rfl) ⟨2074703, by rfl⟩ : syracuseStep 11065085 = 4149407) B4149407
theorem B7376723 : Blo 2185435 7376723 := bstep (se 1 (by rfl) ⟨5532542, by rfl⟩ : syracuseStep 7376723 = 11065085) B11065085
theorem B4917815 : Blo 2185435 4917815 := bstep (se 1 (by rfl) ⟨3688361, by rfl⟩ : syracuseStep 4917815 = 7376723) B7376723
theorem B3278543 : Blo 2185435 3278543 := bstep (se 1 (by rfl) ⟨2458907, by rfl⟩ : syracuseStep 3278543 = 4917815) B4917815
theorem B2185695 : Blo 2185435 2185695 := bstep (se 1 (by rfl) ⟨1639271, by rfl⟩ : syracuseStep 2185695 = 3278543) B3278543
theorem B3278549 : Blo 2185435 3278549 := bbase (se 7 (by rfl) ⟨38420, by rfl⟩ : syracuseStep 3278549 = 76841) (by norm_num)
theorem B2185699 : Blo 2185435 2185699 := bstep (se 1 (by rfl) ⟨1639274, by rfl⟩ : syracuseStep 2185699 = 3278549) B3278549
theorem B4668101 : Blo 2185435 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B3112067 : Blo 2185435 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B8298845 : Blo 2185435 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B5532563 : Blo 2185435 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B3688375 : Blo 2185435 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B4917833 : Blo 2185435 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B3278555 : Blo 2185435 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B2185703 : Blo 2185435 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B2458921 : Blo 2185435 2458921 := bbase (se 2 (by rfl) ⟨922095, by rfl⟩ : syracuseStep 2458921 = 1844191) (by norm_num)
theorem B3278561 : Blo 2185435 3278561 := bstep (se 2 (by rfl) ⟨1229460, by rfl⟩ : syracuseStep 3278561 = 2458921) B2458921
theorem B2185707 : Blo 2185435 2185707 := bstep (se 1 (by rfl) ⟨1639280, by rfl⟩ : syracuseStep 2185707 = 3278561) B3278561
theorem B4984949 : Blo 2185435 4984949 := bbase (se 5 (by rfl) ⟨233669, by rfl⟩ : syracuseStep 4984949 = 467339) (by norm_num)
theorem B13293197 : Blo 2185435 13293197 := bstep (se 3 (by rfl) ⟨2492474, by rfl⟩ : syracuseStep 13293197 = 4984949) B4984949
theorem B8862131 : Blo 2185435 8862131 := bstep (se 1 (by rfl) ⟨6646598, by rfl⟩ : syracuseStep 8862131 = 13293197) B13293197
theorem B5908087 : Blo 2185435 5908087 := bstep (se 1 (by rfl) ⟨4431065, by rfl⟩ : syracuseStep 5908087 = 8862131) B8862131
theorem B7877449 : Blo 2185435 7877449 := bstep (se 2 (by rfl) ⟨2954043, by rfl⟩ : syracuseStep 7877449 = 5908087) B5908087
theorem B10503265 : Blo 2185435 10503265 := bstep (se 2 (by rfl) ⟨3938724, by rfl⟩ : syracuseStep 10503265 = 7877449) B7877449
theorem B14004353 : Blo 2185435 14004353 := bstep (se 2 (by rfl) ⟨5251632, by rfl⟩ : syracuseStep 14004353 = 10503265) B10503265
theorem B9336235 : Blo 2185435 9336235 := bstep (se 1 (by rfl) ⟨7002176, by rfl⟩ : syracuseStep 9336235 = 14004353) B14004353
theorem B12448313 : Blo 2185435 12448313 := bstep (se 2 (by rfl) ⟨4668117, by rfl⟩ : syracuseStep 12448313 = 9336235) B9336235
theorem B8298875 : Blo 2185435 8298875 := bstep (se 1 (by rfl) ⟨6224156, by rfl⟩ : syracuseStep 8298875 = 12448313) B12448313
theorem B5532583 : Blo 2185435 5532583 := bstep (se 1 (by rfl) ⟨4149437, by rfl⟩ : syracuseStep 5532583 = 8298875) B8298875
theorem B7376777 : Blo 2185435 7376777 := bstep (se 2 (by rfl) ⟨2766291, by rfl⟩ : syracuseStep 7376777 = 5532583) B5532583
theorem B4917851 : Blo 2185435 4917851 := bstep (se 1 (by rfl) ⟨3688388, by rfl⟩ : syracuseStep 4917851 = 7376777) B7376777
theorem B3278567 : Blo 2185435 3278567 := bstep (se 1 (by rfl) ⟨2458925, by rfl⟩ : syracuseStep 3278567 = 4917851) B4917851
theorem B2185711 : Blo 2185435 2185711 := bstep (se 1 (by rfl) ⟨1639283, by rfl⟩ : syracuseStep 2185711 = 3278567) B3278567
theorem B3278573 : Blo 2185435 3278573 := bbase (se 3 (by rfl) ⟨614732, by rfl⟩ : syracuseStep 3278573 = 1229465) (by norm_num)
theorem B2185715 : Blo 2185435 2185715 := bstep (se 1 (by rfl) ⟨1639286, by rfl⟩ : syracuseStep 2185715 = 3278573) B3278573
theorem B4917869 : Blo 2185435 4917869 := bbase (se 3 (by rfl) ⟨922100, by rfl⟩ : syracuseStep 4917869 = 1844201) (by norm_num)
theorem B3278579 : Blo 2185435 3278579 := bstep (se 1 (by rfl) ⟨2458934, by rfl⟩ : syracuseStep 3278579 = 4917869) B4917869
theorem B2185719 : Blo 2185435 2185719 := bstep (se 1 (by rfl) ⟨1639289, by rfl⟩ : syracuseStep 2185719 = 3278579) B3278579
theorem B4149461 : Blo 2185435 4149461 := bbase (se 7 (by rfl) ⟨48626, by rfl⟩ : syracuseStep 4149461 = 97253) (by norm_num)
theorem B2766307 : Blo 2185435 2766307 := bstep (se 1 (by rfl) ⟨2074730, by rfl⟩ : syracuseStep 2766307 = 4149461) B4149461
theorem B3688409 : Blo 2185435 3688409 := bstep (se 2 (by rfl) ⟨1383153, by rfl⟩ : syracuseStep 3688409 = 2766307) B2766307
theorem B2458939 : Blo 2185435 2458939 := bstep (se 1 (by rfl) ⟨1844204, by rfl⟩ : syracuseStep 2458939 = 3688409) B3688409
theorem B3278585 : Blo 2185435 3278585 := bstep (se 2 (by rfl) ⟨1229469, by rfl⟩ : syracuseStep 3278585 = 2458939) B2458939
theorem B2185723 : Blo 2185435 2185723 := bstep (se 1 (by rfl) ⟨1639292, by rfl⟩ : syracuseStep 2185723 = 3278585) B3278585
theorem B5608109 : Blo 2185435 5608109 := bbase (se 3 (by rfl) ⟨1051520, by rfl⟩ : syracuseStep 5608109 = 2103041) (by norm_num)
theorem B3738739 : Blo 2185435 3738739 := bstep (se 1 (by rfl) ⟨2804054, by rfl⟩ : syracuseStep 3738739 = 5608109) B5608109
theorem B4984985 : Blo 2185435 4984985 := bstep (se 2 (by rfl) ⟨1869369, by rfl⟩ : syracuseStep 4984985 = 3738739) B3738739
theorem B3323323 : Blo 2185435 3323323 := bstep (se 1 (by rfl) ⟨2492492, by rfl⟩ : syracuseStep 3323323 = 4984985) B4984985
theorem B4431097 : Blo 2185435 4431097 := bstep (se 2 (by rfl) ⟨1661661, by rfl⟩ : syracuseStep 4431097 = 3323323) B3323323
theorem B23632517 : Blo 2185435 23632517 := bstep (se 4 (by rfl) ⟨2215548, by rfl⟩ : syracuseStep 23632517 = 4431097) B4431097
theorem B63020045 : Blo 2185435 63020045 := bstep (se 3 (by rfl) ⟨11816258, by rfl⟩ : syracuseStep 63020045 = 23632517) B23632517
theorem B42013363 : Blo 2185435 42013363 := bstep (se 1 (by rfl) ⟨31510022, by rfl⟩ : syracuseStep 42013363 = 63020045) B63020045
theorem B56017817 : Blo 2185435 56017817 := bstep (se 2 (by rfl) ⟨21006681, by rfl⟩ : syracuseStep 56017817 = 42013363) B42013363
theorem B37345211 : Blo 2185435 37345211 := bstep (se 1 (by rfl) ⟨28008908, by rfl⟩ : syracuseStep 37345211 = 56017817) B56017817
theorem B24896807 : Blo 2185435 24896807 := bstep (se 1 (by rfl) ⟨18672605, by rfl⟩ : syracuseStep 24896807 = 37345211) B37345211
theorem B16597871 : Blo 2185435 16597871 := bstep (se 1 (by rfl) ⟨12448403, by rfl⟩ : syracuseStep 16597871 = 24896807) B24896807
theorem B11065247 : Blo 2185435 11065247 := bstep (se 1 (by rfl) ⟨8298935, by rfl⟩ : syracuseStep 11065247 = 16597871) B16597871
theorem B7376831 : Blo 2185435 7376831 := bstep (se 1 (by rfl) ⟨5532623, by rfl⟩ : syracuseStep 7376831 = 11065247) B11065247
theorem B4917887 : Blo 2185435 4917887 := bstep (se 1 (by rfl) ⟨3688415, by rfl⟩ : syracuseStep 4917887 = 7376831) B7376831
theorem B3278591 : Blo 2185435 3278591 := bstep (se 1 (by rfl) ⟨2458943, by rfl⟩ : syracuseStep 3278591 = 4917887) B4917887
theorem B2185727 : Blo 2185435 2185727 := bstep (se 1 (by rfl) ⟨1639295, by rfl⟩ : syracuseStep 2185727 = 3278591) B3278591
theorem B3278597 : Blo 2185435 3278597 := bbase (se 4 (by rfl) ⟨307368, by rfl⟩ : syracuseStep 3278597 = 614737) (by norm_num)
theorem B2185731 : Blo 2185435 2185731 := bstep (se 1 (by rfl) ⟨1639298, by rfl⟩ : syracuseStep 2185731 = 3278597) B3278597
theorem B3688429 : Blo 2185435 3688429 := bbase (se 3 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 3688429 = 1383161) (by norm_num)
theorem B4917905 : Blo 2185435 4917905 := bstep (se 2 (by rfl) ⟨1844214, by rfl⟩ : syracuseStep 4917905 = 3688429) B3688429
theorem B3278603 : Blo 2185435 3278603 := bstep (se 1 (by rfl) ⟨2458952, by rfl⟩ : syracuseStep 3278603 = 4917905) B4917905
theorem B2185735 : Blo 2185435 2185735 := bstep (se 1 (by rfl) ⟨1639301, by rfl⟩ : syracuseStep 2185735 = 3278603) B3278603
theorem B2458957 : Blo 2185435 2458957 := bbase (se 3 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 2458957 = 922109) (by norm_num)
theorem B3278609 : Blo 2185435 3278609 := bstep (se 2 (by rfl) ⟨1229478, by rfl⟩ : syracuseStep 3278609 = 2458957) B2458957
theorem B2185739 : Blo 2185435 2185739 := bstep (se 1 (by rfl) ⟨1639304, by rfl⟩ : syracuseStep 2185739 = 3278609) B3278609
theorem B7376885 : Blo 2185435 7376885 := bbase (se 5 (by rfl) ⟨345791, by rfl⟩ : syracuseStep 7376885 = 691583) (by norm_num)
theorem B4917923 : Blo 2185435 4917923 := bstep (se 1 (by rfl) ⟨3688442, by rfl⟩ : syracuseStep 4917923 = 7376885) B7376885
theorem B3278615 : Blo 2185435 3278615 := bstep (se 1 (by rfl) ⟨2458961, by rfl⟩ : syracuseStep 3278615 = 4917923) B4917923
theorem B2185743 : Blo 2185435 2185743 := bstep (se 1 (by rfl) ⟨1639307, by rfl⟩ : syracuseStep 2185743 = 3278615) B3278615
theorem B3278621 : Blo 2185435 3278621 := bbase (se 3 (by rfl) ⟨614741, by rfl⟩ : syracuseStep 3278621 = 1229483) (by norm_num)
theorem B2185747 : Blo 2185435 2185747 := bstep (se 1 (by rfl) ⟨1639310, by rfl⟩ : syracuseStep 2185747 = 3278621) B3278621
theorem B4917941 : Blo 2185435 4917941 := bbase (se 5 (by rfl) ⟨230528, by rfl⟩ : syracuseStep 4917941 = 461057) (by norm_num)
theorem B3278627 : Blo 2185435 3278627 := bstep (se 1 (by rfl) ⟨2458970, by rfl⟩ : syracuseStep 3278627 = 4917941) B4917941
theorem B2185751 : Blo 2185435 2185751 := bstep (se 1 (by rfl) ⟨1639313, by rfl⟩ : syracuseStep 2185751 = 3278627) B3278627
theorem B12448565 : Blo 2185435 12448565 := bbase (se 5 (by rfl) ⟨583526, by rfl⟩ : syracuseStep 12448565 = 1167053) (by norm_num)
theorem B8299043 : Blo 2185435 8299043 := bstep (se 1 (by rfl) ⟨6224282, by rfl⟩ : syracuseStep 8299043 = 12448565) B12448565
theorem B5532695 : Blo 2185435 5532695 := bstep (se 1 (by rfl) ⟨4149521, by rfl⟩ : syracuseStep 5532695 = 8299043) B8299043
theorem B3688463 : Blo 2185435 3688463 := bstep (se 1 (by rfl) ⟨2766347, by rfl⟩ : syracuseStep 3688463 = 5532695) B5532695
theorem B2458975 : Blo 2185435 2458975 := bstep (se 1 (by rfl) ⟨1844231, by rfl⟩ : syracuseStep 2458975 = 3688463) B3688463
theorem B3278633 : Blo 2185435 3278633 := bstep (se 2 (by rfl) ⟨1229487, by rfl⟩ : syracuseStep 3278633 = 2458975) B2458975
theorem B2185755 : Blo 2185435 2185755 := bstep (se 1 (by rfl) ⟨1639316, by rfl⟩ : syracuseStep 2185755 = 3278633) B3278633
theorem B6224293 : Blo 2185435 6224293 := bbase (se 4 (by rfl) ⟨583527, by rfl⟩ : syracuseStep 6224293 = 1167055) (by norm_num)
theorem B8299057 : Blo 2185435 8299057 := bstep (se 2 (by rfl) ⟨3112146, by rfl⟩ : syracuseStep 8299057 = 6224293) B6224293
theorem B11065409 : Blo 2185435 11065409 := bstep (se 2 (by rfl) ⟨4149528, by rfl⟩ : syracuseStep 11065409 = 8299057) B8299057
theorem B7376939 : Blo 2185435 7376939 := bstep (se 1 (by rfl) ⟨5532704, by rfl⟩ : syracuseStep 7376939 = 11065409) B11065409
theorem B4917959 : Blo 2185435 4917959 := bstep (se 1 (by rfl) ⟨3688469, by rfl⟩ : syracuseStep 4917959 = 7376939) B7376939
theorem B3278639 : Blo 2185435 3278639 := bstep (se 1 (by rfl) ⟨2458979, by rfl⟩ : syracuseStep 3278639 = 4917959) B4917959
theorem B2185759 : Blo 2185435 2185759 := bstep (se 1 (by rfl) ⟨1639319, by rfl⟩ : syracuseStep 2185759 = 3278639) B3278639
theorem B3278645 : Blo 2185435 3278645 := bbase (se 5 (by rfl) ⟨153686, by rfl⟩ : syracuseStep 3278645 = 307373) (by norm_num)
theorem B2185763 : Blo 2185435 2185763 := bstep (se 1 (by rfl) ⟨1639322, by rfl⟩ : syracuseStep 2185763 = 3278645) B3278645
theorem B5532725 : Blo 2185435 5532725 := bbase (se 5 (by rfl) ⟨259346, by rfl⟩ : syracuseStep 5532725 = 518693) (by norm_num)
theorem B3688483 : Blo 2185435 3688483 := bstep (se 1 (by rfl) ⟨2766362, by rfl⟩ : syracuseStep 3688483 = 5532725) B5532725
theorem B4917977 : Blo 2185435 4917977 := bstep (se 2 (by rfl) ⟨1844241, by rfl⟩ : syracuseStep 4917977 = 3688483) B3688483
theorem B3278651 : Blo 2185435 3278651 := bstep (se 1 (by rfl) ⟨2458988, by rfl⟩ : syracuseStep 3278651 = 4917977) B4917977
theorem B2185767 : Blo 2185435 2185767 := bstep (se 1 (by rfl) ⟨1639325, by rfl⟩ : syracuseStep 2185767 = 3278651) B3278651
theorem B2458993 : Blo 2185435 2458993 := bbase (se 2 (by rfl) ⟨922122, by rfl⟩ : syracuseStep 2458993 = 1844245) (by norm_num)
theorem B3278657 : Blo 2185435 3278657 := bstep (se 2 (by rfl) ⟨1229496, by rfl⟩ : syracuseStep 3278657 = 2458993) B2458993
theorem B2185771 : Blo 2185435 2185771 := bstep (se 1 (by rfl) ⟨1639328, by rfl⟩ : syracuseStep 2185771 = 3278657) B3278657
theorem B5908261 : Blo 2185435 5908261 := bbase (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) (by norm_num)
theorem B7877681 : Blo 2185435 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B5251787 : Blo 2185435 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B3501191 : Blo 2185435 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B9336509 : Blo 2185435 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B6224339 : Blo 2185435 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B4149559 : Blo 2185435 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B5532745 : Blo 2185435 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B7376993 : Blo 2185435 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B4917995 : Blo 2185435 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B3278663 : Blo 2185435 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B2185775 : Blo 2185435 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B3278669 : Blo 2185435 3278669 := bbase (se 3 (by rfl) ⟨614750, by rfl⟩ : syracuseStep 3278669 = 1229501) (by norm_num)
theorem B2185779 : Blo 2185435 2185779 := bstep (se 1 (by rfl) ⟨1639334, by rfl⟩ : syracuseStep 2185779 = 3278669) B3278669
theorem B4918013 : Blo 2185435 4918013 := bbase (se 3 (by rfl) ⟨922127, by rfl⟩ : syracuseStep 4918013 = 1844255) (by norm_num)
theorem B3278675 : Blo 2185435 3278675 := bstep (se 1 (by rfl) ⟨2459006, by rfl⟩ : syracuseStep 3278675 = 4918013) B4918013
theorem B2185783 : Blo 2185435 2185783 := bstep (se 1 (by rfl) ⟨1639337, by rfl⟩ : syracuseStep 2185783 = 3278675) B3278675
theorem B3688517 : Blo 2185435 3688517 := bbase (se 4 (by rfl) ⟨345798, by rfl⟩ : syracuseStep 3688517 = 691597) (by norm_num)
theorem B2459011 : Blo 2185435 2459011 := bstep (se 1 (by rfl) ⟨1844258, by rfl⟩ : syracuseStep 2459011 = 3688517) B3688517
theorem B3278681 : Blo 2185435 3278681 := bstep (se 2 (by rfl) ⟨1229505, by rfl⟩ : syracuseStep 3278681 = 2459011) B2459011
theorem B2185787 : Blo 2185435 2185787 := bstep (se 1 (by rfl) ⟨1639340, by rfl⟩ : syracuseStep 2185787 = 3278681) B3278681
theorem B16598357 : Blo 2185435 16598357 := bbase (se 12 (by rfl) ⟨6078, by rfl⟩ : syracuseStep 16598357 = 12157) (by norm_num)
theorem B11065571 : Blo 2185435 11065571 := bstep (se 1 (by rfl) ⟨8299178, by rfl⟩ : syracuseStep 11065571 = 16598357) B16598357
theorem B7377047 : Blo 2185435 7377047 := bstep (se 1 (by rfl) ⟨5532785, by rfl⟩ : syracuseStep 7377047 = 11065571) B11065571
theorem B4918031 : Blo 2185435 4918031 := bstep (se 1 (by rfl) ⟨3688523, by rfl⟩ : syracuseStep 4918031 = 7377047) B7377047
theorem B3278687 : Blo 2185435 3278687 := bstep (se 1 (by rfl) ⟨2459015, by rfl⟩ : syracuseStep 3278687 = 4918031) B4918031
theorem B2185791 : Blo 2185435 2185791 := bstep (se 1 (by rfl) ⟨1639343, by rfl⟩ : syracuseStep 2185791 = 3278687) B3278687
theorem B3278693 : Blo 2185435 3278693 := bbase (se 4 (by rfl) ⟨307377, by rfl⟩ : syracuseStep 3278693 = 614755) (by norm_num)
theorem B2185795 : Blo 2185435 2185795 := bstep (se 1 (by rfl) ⟨1639346, by rfl⟩ : syracuseStep 2185795 = 3278693) B3278693
theorem B4149605 : Blo 2185435 4149605 := bbase (se 4 (by rfl) ⟨389025, by rfl⟩ : syracuseStep 4149605 = 778051) (by norm_num)
theorem B2766403 : Blo 2185435 2766403 := bstep (se 1 (by rfl) ⟨2074802, by rfl⟩ : syracuseStep 2766403 = 4149605) B4149605
theorem B3688537 : Blo 2185435 3688537 := bstep (se 2 (by rfl) ⟨1383201, by rfl⟩ : syracuseStep 3688537 = 2766403) B2766403
theorem B4918049 : Blo 2185435 4918049 := bstep (se 2 (by rfl) ⟨1844268, by rfl⟩ : syracuseStep 4918049 = 3688537) B3688537
theorem B3278699 : Blo 2185435 3278699 := bstep (se 1 (by rfl) ⟨2459024, by rfl⟩ : syracuseStep 3278699 = 4918049) B4918049
theorem B2185799 : Blo 2185435 2185799 := bstep (se 1 (by rfl) ⟨1639349, by rfl⟩ : syracuseStep 2185799 = 3278699) B3278699
theorem B2459029 : Blo 2185435 2459029 := bbase (se 6 (by rfl) ⟨57633, by rfl⟩ : syracuseStep 2459029 = 115267) (by norm_num)
theorem B3278705 : Blo 2185435 3278705 := bstep (se 2 (by rfl) ⟨1229514, by rfl⟩ : syracuseStep 3278705 = 2459029) B2459029
theorem B2185803 : Blo 2185435 2185803 := bstep (se 1 (by rfl) ⟨1639352, by rfl⟩ : syracuseStep 2185803 = 3278705) B3278705
theorem B2766413 : Blo 2185435 2766413 := bbase (se 3 (by rfl) ⟨518702, by rfl⟩ : syracuseStep 2766413 = 1037405) (by norm_num)
theorem B7377101 : Blo 2185435 7377101 := bstep (se 3 (by rfl) ⟨1383206, by rfl⟩ : syracuseStep 7377101 = 2766413) B2766413
theorem B4918067 : Blo 2185435 4918067 := bstep (se 1 (by rfl) ⟨3688550, by rfl⟩ : syracuseStep 4918067 = 7377101) B7377101
theorem B3278711 : Blo 2185435 3278711 := bstep (se 1 (by rfl) ⟨2459033, by rfl⟩ : syracuseStep 3278711 = 4918067) B4918067
theorem B2185807 : Blo 2185435 2185807 := bstep (se 1 (by rfl) ⟨1639355, by rfl⟩ : syracuseStep 2185807 = 3278711) B3278711
theorem B3278717 : Blo 2185435 3278717 := bbase (se 3 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 3278717 = 1229519) (by norm_num)
theorem B2185811 : Blo 2185435 2185811 := bstep (se 1 (by rfl) ⟨1639358, by rfl⟩ : syracuseStep 2185811 = 3278717) B3278717
theorem B4918085 : Blo 2185435 4918085 := bbase (se 4 (by rfl) ⟨461070, by rfl⟩ : syracuseStep 4918085 = 922141) (by norm_num)
theorem B3278723 : Blo 2185435 3278723 := bstep (se 1 (by rfl) ⟨2459042, by rfl⟩ : syracuseStep 3278723 = 4918085) B4918085
theorem B2185815 : Blo 2185435 2185815 := bstep (se 1 (by rfl) ⟨1639361, by rfl⟩ : syracuseStep 2185815 = 3278723) B3278723
theorem B4668349 : Blo 2185435 4668349 := bbase (se 3 (by rfl) ⟨875315, by rfl⟩ : syracuseStep 4668349 = 1750631) (by norm_num)
theorem B6224465 : Blo 2185435 6224465 := bstep (se 2 (by rfl) ⟨2334174, by rfl⟩ : syracuseStep 6224465 = 4668349) B4668349
theorem B4149643 : Blo 2185435 4149643 := bstep (se 1 (by rfl) ⟨3112232, by rfl⟩ : syracuseStep 4149643 = 6224465) B6224465
theorem B5532857 : Blo 2185435 5532857 := bstep (se 2 (by rfl) ⟨2074821, by rfl⟩ : syracuseStep 5532857 = 4149643) B4149643
theorem B3688571 : Blo 2185435 3688571 := bstep (se 1 (by rfl) ⟨2766428, by rfl⟩ : syracuseStep 3688571 = 5532857) B5532857
theorem B2459047 : Blo 2185435 2459047 := bstep (se 1 (by rfl) ⟨1844285, by rfl⟩ : syracuseStep 2459047 = 3688571) B3688571
theorem B3278729 : Blo 2185435 3278729 := bstep (se 2 (by rfl) ⟨1229523, by rfl⟩ : syracuseStep 3278729 = 2459047) B2459047
theorem B2185819 : Blo 2185435 2185819 := bstep (se 1 (by rfl) ⟨1639364, by rfl⟩ : syracuseStep 2185819 = 3278729) B3278729
theorem B11065733 : Blo 2185435 11065733 := bbase (se 4 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 11065733 = 2074825) (by norm_num)
theorem B7377155 : Blo 2185435 7377155 := bstep (se 1 (by rfl) ⟨5532866, by rfl⟩ : syracuseStep 7377155 = 11065733) B11065733
theorem B4918103 : Blo 2185435 4918103 := bstep (se 1 (by rfl) ⟨3688577, by rfl⟩ : syracuseStep 4918103 = 7377155) B7377155
theorem B3278735 : Blo 2185435 3278735 := bstep (se 1 (by rfl) ⟨2459051, by rfl⟩ : syracuseStep 3278735 = 4918103) B4918103
theorem B2185823 : Blo 2185435 2185823 := bstep (se 1 (by rfl) ⟨1639367, by rfl⟩ : syracuseStep 2185823 = 3278735) B3278735
theorem B3278741 : Blo 2185435 3278741 := bbase (se 6 (by rfl) ⟨76845, by rfl⟩ : syracuseStep 3278741 = 153691) (by norm_num)
theorem B2185827 : Blo 2185435 2185827 := bstep (se 1 (by rfl) ⟨1639370, by rfl⟩ : syracuseStep 2185827 = 3278741) B3278741
theorem B2625961 : Blo 2185435 2625961 := bbase (se 2 (by rfl) ⟨984735, by rfl⟩ : syracuseStep 2625961 = 1969471) (by norm_num)
theorem B3501281 : Blo 2185435 3501281 := bstep (se 2 (by rfl) ⟨1312980, by rfl⟩ : syracuseStep 3501281 = 2625961) B2625961
theorem B2334187 : Blo 2185435 2334187 := bstep (se 1 (by rfl) ⟨1750640, by rfl⟩ : syracuseStep 2334187 = 3501281) B3501281
theorem B12448997 : Blo 2185435 12448997 := bstep (se 4 (by rfl) ⟨1167093, by rfl⟩ : syracuseStep 12448997 = 2334187) B2334187
theorem B8299331 : Blo 2185435 8299331 := bstep (se 1 (by rfl) ⟨6224498, by rfl⟩ : syracuseStep 8299331 = 12448997) B12448997
theorem B5532887 : Blo 2185435 5532887 := bstep (se 1 (by rfl) ⟨4149665, by rfl⟩ : syracuseStep 5532887 = 8299331) B8299331
theorem B3688591 : Blo 2185435 3688591 := bstep (se 1 (by rfl) ⟨2766443, by rfl⟩ : syracuseStep 3688591 = 5532887) B5532887
theorem B4918121 : Blo 2185435 4918121 := bstep (se 2 (by rfl) ⟨1844295, by rfl⟩ : syracuseStep 4918121 = 3688591) B3688591
theorem B3278747 : Blo 2185435 3278747 := bstep (se 1 (by rfl) ⟨2459060, by rfl⟩ : syracuseStep 3278747 = 4918121) B4918121
theorem B2185831 : Blo 2185435 2185831 := bstep (se 1 (by rfl) ⟨1639373, by rfl⟩ : syracuseStep 2185831 = 3278747) B3278747
theorem B2459065 : Blo 2185435 2459065 := bbase (se 2 (by rfl) ⟨922149, by rfl⟩ : syracuseStep 2459065 = 1844299) (by norm_num)
theorem B3278753 : Blo 2185435 3278753 := bstep (se 2 (by rfl) ⟨1229532, by rfl⟩ : syracuseStep 3278753 = 2459065) B2459065
theorem B2185835 : Blo 2185435 2185835 := bstep (se 1 (by rfl) ⟨1639376, by rfl⟩ : syracuseStep 2185835 = 3278753) B3278753
theorem B17725301 : Blo 2185435 17725301 := bbase (se 5 (by rfl) ⟨830873, by rfl⟩ : syracuseStep 17725301 = 1661747) (by norm_num)
theorem B11816867 : Blo 2185435 11816867 := bstep (se 1 (by rfl) ⟨8862650, by rfl⟩ : syracuseStep 11816867 = 17725301) B17725301
theorem B7877911 : Blo 2185435 7877911 := bstep (se 1 (by rfl) ⟨5908433, by rfl⟩ : syracuseStep 7877911 = 11816867) B11816867
theorem B10503881 : Blo 2185435 10503881 := bstep (se 2 (by rfl) ⟨3938955, by rfl⟩ : syracuseStep 10503881 = 7877911) B7877911
theorem B7002587 : Blo 2185435 7002587 := bstep (se 1 (by rfl) ⟨5251940, by rfl⟩ : syracuseStep 7002587 = 10503881) B10503881
theorem B4668391 : Blo 2185435 4668391 := bstep (se 1 (by rfl) ⟨3501293, by rfl⟩ : syracuseStep 4668391 = 7002587) B7002587
theorem B6224521 : Blo 2185435 6224521 := bstep (se 2 (by rfl) ⟨2334195, by rfl⟩ : syracuseStep 6224521 = 4668391) B4668391
theorem B8299361 : Blo 2185435 8299361 := bstep (se 2 (by rfl) ⟨3112260, by rfl⟩ : syracuseStep 8299361 = 6224521) B6224521
theorem B5532907 : Blo 2185435 5532907 := bstep (se 1 (by rfl) ⟨4149680, by rfl⟩ : syracuseStep 5532907 = 8299361) B8299361
theorem B7377209 : Blo 2185435 7377209 := bstep (se 2 (by rfl) ⟨2766453, by rfl⟩ : syracuseStep 7377209 = 5532907) B5532907
theorem B4918139 : Blo 2185435 4918139 := bstep (se 1 (by rfl) ⟨3688604, by rfl⟩ : syracuseStep 4918139 = 7377209) B7377209
theorem B3278759 : Blo 2185435 3278759 := bstep (se 1 (by rfl) ⟨2459069, by rfl⟩ : syracuseStep 3278759 = 4918139) B4918139
theorem B2185839 : Blo 2185435 2185839 := bstep (se 1 (by rfl) ⟨1639379, by rfl⟩ : syracuseStep 2185839 = 3278759) B3278759
theorem B3278765 : Blo 2185435 3278765 := bbase (se 3 (by rfl) ⟨614768, by rfl⟩ : syracuseStep 3278765 = 1229537) (by norm_num)
theorem B2185843 : Blo 2185435 2185843 := bstep (se 1 (by rfl) ⟨1639382, by rfl⟩ : syracuseStep 2185843 = 3278765) B3278765
theorem B4918157 : Blo 2185435 4918157 := bbase (se 3 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 4918157 = 1844309) (by norm_num)
theorem B3278771 : Blo 2185435 3278771 := bstep (se 1 (by rfl) ⟨2459078, by rfl⟩ : syracuseStep 3278771 = 4918157) B4918157
theorem B2185847 : Blo 2185435 2185847 := bstep (se 1 (by rfl) ⟨1639385, by rfl⟩ : syracuseStep 2185847 = 3278771) B3278771
theorem B2766469 : Blo 2185435 2766469 := bbase (se 4 (by rfl) ⟨259356, by rfl⟩ : syracuseStep 2766469 = 518713) (by norm_num)
theorem B3688625 : Blo 2185435 3688625 := bstep (se 2 (by rfl) ⟨1383234, by rfl⟩ : syracuseStep 3688625 = 2766469) B2766469
theorem B2459083 : Blo 2185435 2459083 := bstep (se 1 (by rfl) ⟨1844312, by rfl⟩ : syracuseStep 2459083 = 3688625) B3688625
theorem B3278777 : Blo 2185435 3278777 := bstep (se 2 (by rfl) ⟨1229541, by rfl⟩ : syracuseStep 3278777 = 2459083) B2459083
theorem B2185851 : Blo 2185435 2185851 := bstep (se 1 (by rfl) ⟨1639388, by rfl⟩ : syracuseStep 2185851 = 3278777) B3278777
theorem B2625989 : Blo 2185435 2625989 := bbase (se 4 (by rfl) ⟨246186, by rfl⟩ : syracuseStep 2625989 = 492373) (by norm_num)
theorem B28010549 : Blo 2185435 28010549 := bstep (se 5 (by rfl) ⟨1312994, by rfl⟩ : syracuseStep 28010549 = 2625989) B2625989
theorem B18673699 : Blo 2185435 18673699 := bstep (se 1 (by rfl) ⟨14005274, by rfl⟩ : syracuseStep 18673699 = 28010549) B28010549
theorem B24898265 : Blo 2185435 24898265 := bstep (se 2 (by rfl) ⟨9336849, by rfl⟩ : syracuseStep 24898265 = 18673699) B18673699
theorem B16598843 : Blo 2185435 16598843 := bstep (se 1 (by rfl) ⟨12449132, by rfl⟩ : syracuseStep 16598843 = 24898265) B24898265
theorem B11065895 : Blo 2185435 11065895 := bstep (se 1 (by rfl) ⟨8299421, by rfl⟩ : syracuseStep 11065895 = 16598843) B16598843
theorem B7377263 : Blo 2185435 7377263 := bstep (se 1 (by rfl) ⟨5532947, by rfl⟩ : syracuseStep 7377263 = 11065895) B11065895
theorem B4918175 : Blo 2185435 4918175 := bstep (se 1 (by rfl) ⟨3688631, by rfl⟩ : syracuseStep 4918175 = 7377263) B7377263
theorem B3278783 : Blo 2185435 3278783 := bstep (se 1 (by rfl) ⟨2459087, by rfl⟩ : syracuseStep 3278783 = 4918175) B4918175
theorem B2185855 : Blo 2185435 2185855 := bstep (se 1 (by rfl) ⟨1639391, by rfl⟩ : syracuseStep 2185855 = 3278783) B3278783
theorem B3278789 : Blo 2185435 3278789 := bbase (se 4 (by rfl) ⟨307386, by rfl⟩ : syracuseStep 3278789 = 614773) (by norm_num)
theorem B2185859 : Blo 2185435 2185859 := bstep (se 1 (by rfl) ⟨1639394, by rfl⟩ : syracuseStep 2185859 = 3278789) B3278789
theorem B3688645 : Blo 2185435 3688645 := bbase (se 4 (by rfl) ⟨345810, by rfl⟩ : syracuseStep 3688645 = 691621) (by norm_num)
theorem B4918193 : Blo 2185435 4918193 := bstep (se 2 (by rfl) ⟨1844322, by rfl⟩ : syracuseStep 4918193 = 3688645) B3688645
theorem B3278795 : Blo 2185435 3278795 := bstep (se 1 (by rfl) ⟨2459096, by rfl⟩ : syracuseStep 3278795 = 4918193) B4918193
theorem B2185863 : Blo 2185435 2185863 := bstep (se 1 (by rfl) ⟨1639397, by rfl⟩ : syracuseStep 2185863 = 3278795) B3278795
theorem B2459101 : Blo 2185435 2459101 := bbase (se 3 (by rfl) ⟨461081, by rfl⟩ : syracuseStep 2459101 = 922163) (by norm_num)
theorem B3278801 : Blo 2185435 3278801 := bstep (se 2 (by rfl) ⟨1229550, by rfl⟩ : syracuseStep 3278801 = 2459101) B2459101
theorem B2185867 : Blo 2185435 2185867 := bstep (se 1 (by rfl) ⟨1639400, by rfl⟩ : syracuseStep 2185867 = 3278801) B3278801
theorem B7377317 : Blo 2185435 7377317 := bbase (se 4 (by rfl) ⟨691623, by rfl⟩ : syracuseStep 7377317 = 1383247) (by norm_num)
theorem B4918211 : Blo 2185435 4918211 := bstep (se 1 (by rfl) ⟨3688658, by rfl⟩ : syracuseStep 4918211 = 7377317) B7377317
theorem B3278807 : Blo 2185435 3278807 := bstep (se 1 (by rfl) ⟨2459105, by rfl⟩ : syracuseStep 3278807 = 4918211) B4918211
theorem B2185871 : Blo 2185435 2185871 := bstep (se 1 (by rfl) ⟨1639403, by rfl⟩ : syracuseStep 2185871 = 3278807) B3278807
theorem B3278813 : Blo 2185435 3278813 := bbase (se 3 (by rfl) ⟨614777, by rfl⟩ : syracuseStep 3278813 = 1229555) (by norm_num)
theorem B2185875 : Blo 2185435 2185875 := bstep (se 1 (by rfl) ⟨1639406, by rfl⟩ : syracuseStep 2185875 = 3278813) B3278813
theorem B4918229 : Blo 2185435 4918229 := bbase (se 7 (by rfl) ⟨57635, by rfl⟩ : syracuseStep 4918229 = 115271) (by norm_num)
theorem B3278819 : Blo 2185435 3278819 := bstep (se 1 (by rfl) ⟨2459114, by rfl⟩ : syracuseStep 3278819 = 4918229) B4918229
theorem B2185879 : Blo 2185435 2185879 := bstep (se 1 (by rfl) ⟨1639409, by rfl⟩ : syracuseStep 2185879 = 3278819) B3278819
theorem B7985557 : Blo 2185435 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B42589637 : Blo 2185435 42589637 := bstep (se 4 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 42589637 = 7985557) B7985557
theorem B28393091 : Blo 2185435 28393091 := bstep (se 1 (by rfl) ⟨21294818, by rfl⟩ : syracuseStep 28393091 = 42589637) B42589637
theorem B18928727 : Blo 2185435 18928727 := bstep (se 1 (by rfl) ⟨14196545, by rfl⟩ : syracuseStep 18928727 = 28393091) B28393091
theorem B12619151 : Blo 2185435 12619151 := bstep (se 1 (by rfl) ⟨9464363, by rfl⟩ : syracuseStep 12619151 = 18928727) B18928727
theorem B8412767 : Blo 2185435 8412767 := bstep (se 1 (by rfl) ⟨6309575, by rfl⟩ : syracuseStep 8412767 = 12619151) B12619151
theorem B5608511 : Blo 2185435 5608511 := bstep (se 1 (by rfl) ⟨4206383, by rfl⟩ : syracuseStep 5608511 = 8412767) B8412767
theorem B3739007 : Blo 2185435 3739007 := bstep (se 1 (by rfl) ⟨2804255, by rfl⟩ : syracuseStep 3739007 = 5608511) B5608511
theorem B9970685 : Blo 2185435 9970685 := bstep (se 3 (by rfl) ⟨1869503, by rfl⟩ : syracuseStep 9970685 = 3739007) B3739007
theorem B6647123 : Blo 2185435 6647123 := bstep (se 1 (by rfl) ⟨4985342, by rfl⟩ : syracuseStep 6647123 = 9970685) B9970685
theorem B4431415 : Blo 2185435 4431415 := bstep (se 1 (by rfl) ⟨3323561, by rfl⟩ : syracuseStep 4431415 = 6647123) B6647123
theorem B5908553 : Blo 2185435 5908553 := bstep (se 2 (by rfl) ⟨2215707, by rfl⟩ : syracuseStep 5908553 = 4431415) B4431415
theorem B3939035 : Blo 2185435 3939035 := bstep (se 1 (by rfl) ⟨2954276, by rfl⟩ : syracuseStep 3939035 = 5908553) B5908553
theorem B10504093 : Blo 2185435 10504093 := bstep (se 3 (by rfl) ⟨1969517, by rfl⟩ : syracuseStep 10504093 = 3939035) B3939035
theorem B14005457 : Blo 2185435 14005457 := bstep (se 2 (by rfl) ⟨5252046, by rfl⟩ : syracuseStep 14005457 = 10504093) B10504093
theorem B9336971 : Blo 2185435 9336971 := bstep (se 1 (by rfl) ⟨7002728, by rfl⟩ : syracuseStep 9336971 = 14005457) B14005457
theorem B6224647 : Blo 2185435 6224647 := bstep (se 1 (by rfl) ⟨4668485, by rfl⟩ : syracuseStep 6224647 = 9336971) B9336971
theorem B8299529 : Blo 2185435 8299529 := bstep (se 2 (by rfl) ⟨3112323, by rfl⟩ : syracuseStep 8299529 = 6224647) B6224647
theorem B5533019 : Blo 2185435 5533019 := bstep (se 1 (by rfl) ⟨4149764, by rfl⟩ : syracuseStep 5533019 = 8299529) B8299529
theorem B3688679 : Blo 2185435 3688679 := bstep (se 1 (by rfl) ⟨2766509, by rfl⟩ : syracuseStep 3688679 = 5533019) B5533019
theorem B2459119 : Blo 2185435 2459119 := bstep (se 1 (by rfl) ⟨1844339, by rfl⟩ : syracuseStep 2459119 = 3688679) B3688679
theorem B3278825 : Blo 2185435 3278825 := bstep (se 2 (by rfl) ⟨1229559, by rfl⟩ : syracuseStep 3278825 = 2459119) B2459119
theorem B2185883 : Blo 2185435 2185883 := bstep (se 1 (by rfl) ⟨1639412, by rfl⟩ : syracuseStep 2185883 = 3278825) B3278825
theorem B18673973 : Blo 2185435 18673973 := bbase (se 5 (by rfl) ⟨875342, by rfl⟩ : syracuseStep 18673973 = 1750685) (by norm_num)
theorem B12449315 : Blo 2185435 12449315 := bstep (se 1 (by rfl) ⟨9336986, by rfl⟩ : syracuseStep 12449315 = 18673973) B18673973
theorem B8299543 : Blo 2185435 8299543 := bstep (se 1 (by rfl) ⟨6224657, by rfl⟩ : syracuseStep 8299543 = 12449315) B12449315
theorem B11066057 : Blo 2185435 11066057 := bstep (se 2 (by rfl) ⟨4149771, by rfl⟩ : syracuseStep 11066057 = 8299543) B8299543
theorem B7377371 : Blo 2185435 7377371 := bstep (se 1 (by rfl) ⟨5533028, by rfl⟩ : syracuseStep 7377371 = 11066057) B11066057
theorem B4918247 : Blo 2185435 4918247 := bstep (se 1 (by rfl) ⟨3688685, by rfl⟩ : syracuseStep 4918247 = 7377371) B7377371
theorem B3278831 : Blo 2185435 3278831 := bstep (se 1 (by rfl) ⟨2459123, by rfl⟩ : syracuseStep 3278831 = 4918247) B4918247
theorem B2185887 : Blo 2185435 2185887 := bstep (se 1 (by rfl) ⟨1639415, by rfl⟩ : syracuseStep 2185887 = 3278831) B3278831
theorem B3278837 : Blo 2185435 3278837 := bbase (se 5 (by rfl) ⟨153695, by rfl⟩ : syracuseStep 3278837 = 307391) (by norm_num)
theorem B2185891 : Blo 2185435 2185891 := bstep (se 1 (by rfl) ⟨1639418, by rfl⟩ : syracuseStep 2185891 = 3278837) B3278837
theorem B5608541 : Blo 2185435 5608541 := bbase (se 3 (by rfl) ⟨1051601, by rfl⟩ : syracuseStep 5608541 = 2103203) (by norm_num)
theorem B14956109 : Blo 2185435 14956109 := bstep (se 3 (by rfl) ⟨2804270, by rfl⟩ : syracuseStep 14956109 = 5608541) B5608541
theorem B9970739 : Blo 2185435 9970739 := bstep (se 1 (by rfl) ⟨7478054, by rfl⟩ : syracuseStep 9970739 = 14956109) B14956109
theorem B6647159 : Blo 2185435 6647159 := bstep (se 1 (by rfl) ⟨4985369, by rfl⟩ : syracuseStep 6647159 = 9970739) B9970739
theorem B4431439 : Blo 2185435 4431439 := bstep (se 1 (by rfl) ⟨3323579, by rfl⟩ : syracuseStep 4431439 = 6647159) B6647159
theorem B23634341 : Blo 2185435 23634341 := bstep (se 4 (by rfl) ⟨2215719, by rfl⟩ : syracuseStep 23634341 = 4431439) B4431439
theorem B15756227 : Blo 2185435 15756227 := bstep (se 1 (by rfl) ⟨11817170, by rfl⟩ : syracuseStep 15756227 = 23634341) B23634341
theorem B10504151 : Blo 2185435 10504151 := bstep (se 1 (by rfl) ⟨7878113, by rfl⟩ : syracuseStep 10504151 = 15756227) B15756227
theorem B7002767 : Blo 2185435 7002767 := bstep (se 1 (by rfl) ⟨5252075, by rfl⟩ : syracuseStep 7002767 = 10504151) B10504151
theorem B4668511 : Blo 2185435 4668511 := bstep (se 1 (by rfl) ⟨3501383, by rfl⟩ : syracuseStep 4668511 = 7002767) B7002767
theorem B6224681 : Blo 2185435 6224681 := bstep (se 2 (by rfl) ⟨2334255, by rfl⟩ : syracuseStep 6224681 = 4668511) B4668511
theorem B4149787 : Blo 2185435 4149787 := bstep (se 1 (by rfl) ⟨3112340, by rfl⟩ : syracuseStep 4149787 = 6224681) B6224681
theorem B5533049 : Blo 2185435 5533049 := bstep (se 2 (by rfl) ⟨2074893, by rfl⟩ : syracuseStep 5533049 = 4149787) B4149787
theorem B3688699 : Blo 2185435 3688699 := bstep (se 1 (by rfl) ⟨2766524, by rfl⟩ : syracuseStep 3688699 = 5533049) B5533049
theorem B4918265 : Blo 2185435 4918265 := bstep (se 2 (by rfl) ⟨1844349, by rfl⟩ : syracuseStep 4918265 = 3688699) B3688699
theorem B3278843 : Blo 2185435 3278843 := bstep (se 1 (by rfl) ⟨2459132, by rfl⟩ : syracuseStep 3278843 = 4918265) B4918265
theorem B2185895 : Blo 2185435 2185895 := bstep (se 1 (by rfl) ⟨1639421, by rfl⟩ : syracuseStep 2185895 = 3278843) B3278843
theorem B2459137 : Blo 2185435 2459137 := bbase (se 2 (by rfl) ⟨922176, by rfl⟩ : syracuseStep 2459137 = 1844353) (by norm_num)
theorem B3278849 : Blo 2185435 3278849 := bstep (se 2 (by rfl) ⟨1229568, by rfl⟩ : syracuseStep 3278849 = 2459137) B2459137
theorem B2185899 : Blo 2185435 2185899 := bstep (se 1 (by rfl) ⟨1639424, by rfl⟩ : syracuseStep 2185899 = 3278849) B3278849
theorem B5533069 : Blo 2185435 5533069 := bbase (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) (by norm_num)
theorem B7377425 : Blo 2185435 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B4918283 : Blo 2185435 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B3278855 : Blo 2185435 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B2185903 : Blo 2185435 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B3278861 : Blo 2185435 3278861 := bbase (se 3 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 3278861 = 1229573) (by norm_num)
theorem B2185907 : Blo 2185435 2185907 := bstep (se 1 (by rfl) ⟨1639430, by rfl⟩ : syracuseStep 2185907 = 3278861) B3278861
theorem B4918301 : Blo 2185435 4918301 := bbase (se 3 (by rfl) ⟨922181, by rfl⟩ : syracuseStep 4918301 = 1844363) (by norm_num)
theorem B3278867 : Blo 2185435 3278867 := bstep (se 1 (by rfl) ⟨2459150, by rfl⟩ : syracuseStep 3278867 = 4918301) B4918301
theorem B2185911 : Blo 2185435 2185911 := bstep (se 1 (by rfl) ⟨1639433, by rfl⟩ : syracuseStep 2185911 = 3278867) B3278867
theorem B3688733 : Blo 2185435 3688733 := bbase (se 3 (by rfl) ⟨691637, by rfl⟩ : syracuseStep 3688733 = 1383275) (by norm_num)
theorem B2459155 : Blo 2185435 2459155 := bstep (se 1 (by rfl) ⟨1844366, by rfl⟩ : syracuseStep 2459155 = 3688733) B3688733
theorem B3278873 : Blo 2185435 3278873 := bstep (se 2 (by rfl) ⟨1229577, by rfl⟩ : syracuseStep 3278873 = 2459155) B2459155
theorem B2185915 : Blo 2185435 2185915 := bstep (se 1 (by rfl) ⟨1639436, by rfl⟩ : syracuseStep 2185915 = 3278873) B3278873
theorem B14005685 : Blo 2185435 14005685 := bbase (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) (by norm_num)
theorem B9337123 : Blo 2185435 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B12449497 : Blo 2185435 12449497 := bstep (se 2 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 12449497 = 9337123) B9337123
theorem B16599329 : Blo 2185435 16599329 := bstep (se 2 (by rfl) ⟨6224748, by rfl⟩ : syracuseStep 16599329 = 12449497) B12449497
theorem B11066219 : Blo 2185435 11066219 := bstep (se 1 (by rfl) ⟨8299664, by rfl⟩ : syracuseStep 11066219 = 16599329) B16599329
theorem B7377479 : Blo 2185435 7377479 := bstep (se 1 (by rfl) ⟨5533109, by rfl⟩ : syracuseStep 7377479 = 11066219) B11066219
theorem B4918319 : Blo 2185435 4918319 := bstep (se 1 (by rfl) ⟨3688739, by rfl⟩ : syracuseStep 4918319 = 7377479) B7377479
theorem B3278879 : Blo 2185435 3278879 := bstep (se 1 (by rfl) ⟨2459159, by rfl⟩ : syracuseStep 3278879 = 4918319) B4918319
theorem B2185919 : Blo 2185435 2185919 := bstep (se 1 (by rfl) ⟨1639439, by rfl⟩ : syracuseStep 2185919 = 3278879) B3278879
theorem B3278885 : Blo 2185435 3278885 := bbase (se 4 (by rfl) ⟨307395, by rfl⟩ : syracuseStep 3278885 = 614791) (by norm_num)
theorem B2185923 : Blo 2185435 2185923 := bstep (se 1 (by rfl) ⟨1639442, by rfl⟩ : syracuseStep 2185923 = 3278885) B3278885
theorem B2766565 : Blo 2185435 2766565 := bbase (se 4 (by rfl) ⟨259365, by rfl⟩ : syracuseStep 2766565 = 518731) (by norm_num)
theorem B3688753 : Blo 2185435 3688753 := bstep (se 2 (by rfl) ⟨1383282, by rfl⟩ : syracuseStep 3688753 = 2766565) B2766565
theorem B4918337 : Blo 2185435 4918337 := bstep (se 2 (by rfl) ⟨1844376, by rfl⟩ : syracuseStep 4918337 = 3688753) B3688753
theorem B3278891 : Blo 2185435 3278891 := bstep (se 1 (by rfl) ⟨2459168, by rfl⟩ : syracuseStep 3278891 = 4918337) B4918337
theorem B2185927 : Blo 2185435 2185927 := bstep (se 1 (by rfl) ⟨1639445, by rfl⟩ : syracuseStep 2185927 = 3278891) B3278891
theorem B2459173 : Blo 2185435 2459173 := bbase (se 4 (by rfl) ⟨230547, by rfl⟩ : syracuseStep 2459173 = 461095) (by norm_num)
theorem B3278897 : Blo 2185435 3278897 := bstep (se 2 (by rfl) ⟨1229586, by rfl⟩ : syracuseStep 3278897 = 2459173) B2459173
theorem B2185931 : Blo 2185435 2185931 := bstep (se 1 (by rfl) ⟨1639448, by rfl⟩ : syracuseStep 2185931 = 3278897) B3278897
theorem B23634773 : Blo 2185435 23634773 := bbase (se 9 (by rfl) ⟨69242, by rfl⟩ : syracuseStep 23634773 = 138485) (by norm_num)
theorem B15756515 : Blo 2185435 15756515 := bstep (se 1 (by rfl) ⟨11817386, by rfl⟩ : syracuseStep 15756515 = 23634773) B23634773
theorem B10504343 : Blo 2185435 10504343 := bstep (se 1 (by rfl) ⟨7878257, by rfl⟩ : syracuseStep 10504343 = 15756515) B15756515
theorem B7002895 : Blo 2185435 7002895 := bstep (se 1 (by rfl) ⟨5252171, by rfl⟩ : syracuseStep 7002895 = 10504343) B10504343
theorem B9337193 : Blo 2185435 9337193 := bstep (se 2 (by rfl) ⟨3501447, by rfl⟩ : syracuseStep 9337193 = 7002895) B7002895
theorem B6224795 : Blo 2185435 6224795 := bstep (se 1 (by rfl) ⟨4668596, by rfl⟩ : syracuseStep 6224795 = 9337193) B9337193
theorem B4149863 : Blo 2185435 4149863 := bstep (se 1 (by rfl) ⟨3112397, by rfl⟩ : syracuseStep 4149863 = 6224795) B6224795
theorem B2766575 : Blo 2185435 2766575 := bstep (se 1 (by rfl) ⟨2074931, by rfl⟩ : syracuseStep 2766575 = 4149863) B4149863
theorem B7377533 : Blo 2185435 7377533 := bstep (se 3 (by rfl) ⟨1383287, by rfl⟩ : syracuseStep 7377533 = 2766575) B2766575
theorem B4918355 : Blo 2185435 4918355 := bstep (se 1 (by rfl) ⟨3688766, by rfl⟩ : syracuseStep 4918355 = 7377533) B7377533
theorem B3278903 : Blo 2185435 3278903 := bstep (se 1 (by rfl) ⟨2459177, by rfl⟩ : syracuseStep 3278903 = 4918355) B4918355
theorem B2185935 : Blo 2185435 2185935 := bstep (se 1 (by rfl) ⟨1639451, by rfl⟩ : syracuseStep 2185935 = 3278903) B3278903
theorem B3278909 : Blo 2185435 3278909 := bbase (se 3 (by rfl) ⟨614795, by rfl⟩ : syracuseStep 3278909 = 1229591) (by norm_num)
theorem B2185939 : Blo 2185435 2185939 := bstep (se 1 (by rfl) ⟨1639454, by rfl⟩ : syracuseStep 2185939 = 3278909) B3278909
theorem B4918373 : Blo 2185435 4918373 := bbase (se 4 (by rfl) ⟨461097, by rfl⟩ : syracuseStep 4918373 = 922195) (by norm_num)
theorem B3278915 : Blo 2185435 3278915 := bstep (se 1 (by rfl) ⟨2459186, by rfl⟩ : syracuseStep 3278915 = 4918373) B4918373
theorem B2185943 : Blo 2185435 2185943 := bstep (se 1 (by rfl) ⟨1639457, by rfl⟩ : syracuseStep 2185943 = 3278915) B3278915
theorem B5533181 : Blo 2185435 5533181 := bbase (se 3 (by rfl) ⟨1037471, by rfl⟩ : syracuseStep 5533181 = 2074943) (by norm_num)
theorem B3688787 : Blo 2185435 3688787 := bstep (se 1 (by rfl) ⟨2766590, by rfl⟩ : syracuseStep 3688787 = 5533181) B5533181
theorem B2459191 : Blo 2185435 2459191 := bstep (se 1 (by rfl) ⟨1844393, by rfl⟩ : syracuseStep 2459191 = 3688787) B3688787
theorem B3278921 : Blo 2185435 3278921 := bstep (se 2 (by rfl) ⟨1229595, by rfl⟩ : syracuseStep 3278921 = 2459191) B2459191
theorem B2185947 : Blo 2185435 2185947 := bstep (se 1 (by rfl) ⟨1639460, by rfl⟩ : syracuseStep 2185947 = 3278921) B3278921
theorem B4149893 : Blo 2185435 4149893 := bbase (se 4 (by rfl) ⟨389052, by rfl⟩ : syracuseStep 4149893 = 778105) (by norm_num)
theorem B11066381 : Blo 2185435 11066381 := bstep (se 3 (by rfl) ⟨2074946, by rfl⟩ : syracuseStep 11066381 = 4149893) B4149893
theorem B7377587 : Blo 2185435 7377587 := bstep (se 1 (by rfl) ⟨5533190, by rfl⟩ : syracuseStep 7377587 = 11066381) B11066381
theorem B4918391 : Blo 2185435 4918391 := bstep (se 1 (by rfl) ⟨3688793, by rfl⟩ : syracuseStep 4918391 = 7377587) B7377587
theorem B3278927 : Blo 2185435 3278927 := bstep (se 1 (by rfl) ⟨2459195, by rfl⟩ : syracuseStep 3278927 = 4918391) B4918391
theorem B2185951 : Blo 2185435 2185951 := bstep (se 1 (by rfl) ⟨1639463, by rfl⟩ : syracuseStep 2185951 = 3278927) B3278927
theorem B3278933 : Blo 2185435 3278933 := bbase (se 8 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 3278933 = 38425) (by norm_num)
theorem B2185955 : Blo 2185435 2185955 := bstep (se 1 (by rfl) ⟨1639466, by rfl⟩ : syracuseStep 2185955 = 3278933) B3278933
theorem B9971029 : Blo 2185435 9971029 := bbase (se 12 (by rfl) ⟨3651, by rfl⟩ : syracuseStep 9971029 = 7303) (by norm_num)
theorem B13294705 : Blo 2185435 13294705 := bstep (se 2 (by rfl) ⟨4985514, by rfl⟩ : syracuseStep 13294705 = 9971029) B9971029
theorem B17726273 : Blo 2185435 17726273 := bstep (se 2 (by rfl) ⟨6647352, by rfl⟩ : syracuseStep 17726273 = 13294705) B13294705
theorem B11817515 : Blo 2185435 11817515 := bstep (se 1 (by rfl) ⟨8863136, by rfl⟩ : syracuseStep 11817515 = 17726273) B17726273
theorem B31513373 : Blo 2185435 31513373 := bstep (se 3 (by rfl) ⟨5908757, by rfl⟩ : syracuseStep 31513373 = 11817515) B11817515
theorem B21008915 : Blo 2185435 21008915 := bstep (se 1 (by rfl) ⟨15756686, by rfl⟩ : syracuseStep 21008915 = 31513373) B31513373
theorem B14005943 : Blo 2185435 14005943 := bstep (se 1 (by rfl) ⟨10504457, by rfl⟩ : syracuseStep 14005943 = 21008915) B21008915
theorem B9337295 : Blo 2185435 9337295 := bstep (se 1 (by rfl) ⟨7002971, by rfl⟩ : syracuseStep 9337295 = 14005943) B14005943
theorem B6224863 : Blo 2185435 6224863 := bstep (se 1 (by rfl) ⟨4668647, by rfl⟩ : syracuseStep 6224863 = 9337295) B9337295
theorem B8299817 : Blo 2185435 8299817 := bstep (se 2 (by rfl) ⟨3112431, by rfl⟩ : syracuseStep 8299817 = 6224863) B6224863
theorem B5533211 : Blo 2185435 5533211 := bstep (se 1 (by rfl) ⟨4149908, by rfl⟩ : syracuseStep 5533211 = 8299817) B8299817
theorem B3688807 : Blo 2185435 3688807 := bstep (se 1 (by rfl) ⟨2766605, by rfl⟩ : syracuseStep 3688807 = 5533211) B5533211
theorem B4918409 : Blo 2185435 4918409 := bstep (se 2 (by rfl) ⟨1844403, by rfl⟩ : syracuseStep 4918409 = 3688807) B3688807
theorem B3278939 : Blo 2185435 3278939 := bstep (se 1 (by rfl) ⟨2459204, by rfl⟩ : syracuseStep 3278939 = 4918409) B4918409
theorem B2185959 : Blo 2185435 2185959 := bstep (se 1 (by rfl) ⟨1639469, by rfl⟩ : syracuseStep 2185959 = 3278939) B3278939
theorem B2459209 : Blo 2185435 2459209 := bbase (se 2 (by rfl) ⟨922203, by rfl⟩ : syracuseStep 2459209 = 1844407) (by norm_num)
theorem B3278945 : Blo 2185435 3278945 := bstep (se 2 (by rfl) ⟨1229604, by rfl⟩ : syracuseStep 3278945 = 2459209) B2459209
theorem B2185963 : Blo 2185435 2185963 := bstep (se 1 (by rfl) ⟨1639472, by rfl⟩ : syracuseStep 2185963 = 3278945) B3278945
theorem B14956597 : Blo 2185435 14956597 := bbase (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) (by norm_num)
theorem B19942129 : Blo 2185435 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B26589505 : Blo 2185435 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B35452673 : Blo 2185435 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B23635115 : Blo 2185435 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B15756743 : Blo 2185435 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B10504495 : Blo 2185435 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B14005993 : Blo 2185435 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B18674657 : Blo 2185435 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B12449771 : Blo 2185435 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B8299847 : Blo 2185435 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B5533231 : Blo 2185435 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B7377641 : Blo 2185435 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B4918427 : Blo 2185435 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B3278951 : Blo 2185435 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B2185967 : Blo 2185435 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B3278957 : Blo 2185435 3278957 := bbase (se 3 (by rfl) ⟨614804, by rfl⟩ : syracuseStep 3278957 = 1229609) (by norm_num)
theorem B2185971 : Blo 2185435 2185971 := bstep (se 1 (by rfl) ⟨1639478, by rfl⟩ : syracuseStep 2185971 = 3278957) B3278957
theorem B4918445 : Blo 2185435 4918445 := bbase (se 3 (by rfl) ⟨922208, by rfl⟩ : syracuseStep 4918445 = 1844417) (by norm_num)
theorem B3278963 : Blo 2185435 3278963 := bstep (se 1 (by rfl) ⟨2459222, by rfl⟩ : syracuseStep 3278963 = 4918445) B4918445
theorem B2185975 : Blo 2185435 2185975 := bstep (se 1 (by rfl) ⟨1639481, by rfl⟩ : syracuseStep 2185975 = 3278963) B3278963
theorem B3790189 : Blo 2185435 3790189 := bbase (se 3 (by rfl) ⟨710660, by rfl⟩ : syracuseStep 3790189 = 1421321) (by norm_num)
theorem B5053585 : Blo 2185435 5053585 := bstep (se 2 (by rfl) ⟨1895094, by rfl⟩ : syracuseStep 5053585 = 3790189) B3790189
theorem B6738113 : Blo 2185435 6738113 := bstep (se 2 (by rfl) ⟨2526792, by rfl⟩ : syracuseStep 6738113 = 5053585) B5053585
theorem B17968301 : Blo 2185435 17968301 := bstep (se 3 (by rfl) ⟨3369056, by rfl⟩ : syracuseStep 17968301 = 6738113) B6738113
theorem B11978867 : Blo 2185435 11978867 := bstep (se 1 (by rfl) ⟨8984150, by rfl⟩ : syracuseStep 11978867 = 17968301) B17968301
theorem B7985911 : Blo 2185435 7985911 := bstep (se 1 (by rfl) ⟨5989433, by rfl⟩ : syracuseStep 7985911 = 11978867) B11978867
theorem B10647881 : Blo 2185435 10647881 := bstep (se 2 (by rfl) ⟨3992955, by rfl⟩ : syracuseStep 10647881 = 7985911) B7985911
theorem B7098587 : Blo 2185435 7098587 := bstep (se 1 (by rfl) ⟨5323940, by rfl⟩ : syracuseStep 7098587 = 10647881) B10647881
theorem B4732391 : Blo 2185435 4732391 := bstep (se 1 (by rfl) ⟨3549293, by rfl⟩ : syracuseStep 4732391 = 7098587) B7098587
theorem B12619709 : Blo 2185435 12619709 := bstep (se 3 (by rfl) ⟨2366195, by rfl⟩ : syracuseStep 12619709 = 4732391) B4732391
theorem B8413139 : Blo 2185435 8413139 := bstep (se 1 (by rfl) ⟨6309854, by rfl⟩ : syracuseStep 8413139 = 12619709) B12619709
theorem B5608759 : Blo 2185435 5608759 := bstep (se 1 (by rfl) ⟨4206569, by rfl⟩ : syracuseStep 5608759 = 8413139) B8413139
theorem B7478345 : Blo 2185435 7478345 := bstep (se 2 (by rfl) ⟨2804379, by rfl⟩ : syracuseStep 7478345 = 5608759) B5608759
theorem B4985563 : Blo 2185435 4985563 := bstep (se 1 (by rfl) ⟨3739172, by rfl⟩ : syracuseStep 4985563 = 7478345) B7478345
theorem B6647417 : Blo 2185435 6647417 := bstep (se 2 (by rfl) ⟨2492781, by rfl⟩ : syracuseStep 6647417 = 4985563) B4985563
theorem B4431611 : Blo 2185435 4431611 := bstep (se 1 (by rfl) ⟨3323708, by rfl⟩ : syracuseStep 4431611 = 6647417) B6647417
theorem B2954407 : Blo 2185435 2954407 := bstep (se 1 (by rfl) ⟨2215805, by rfl⟩ : syracuseStep 2954407 = 4431611) B4431611
theorem B3939209 : Blo 2185435 3939209 := bstep (se 2 (by rfl) ⟨1477203, by rfl⟩ : syracuseStep 3939209 = 2954407) B2954407
theorem B2626139 : Blo 2185435 2626139 := bstep (se 1 (by rfl) ⟨1969604, by rfl⟩ : syracuseStep 2626139 = 3939209) B3939209
theorem B7003037 : Blo 2185435 7003037 := bstep (se 3 (by rfl) ⟨1313069, by rfl⟩ : syracuseStep 7003037 = 2626139) B2626139
theorem B4668691 : Blo 2185435 4668691 := bstep (se 1 (by rfl) ⟨3501518, by rfl⟩ : syracuseStep 4668691 = 7003037) B7003037
theorem B6224921 : Blo 2185435 6224921 := bstep (se 2 (by rfl) ⟨2334345, by rfl⟩ : syracuseStep 6224921 = 4668691) B4668691
theorem B4149947 : Blo 2185435 4149947 := bstep (se 1 (by rfl) ⟨3112460, by rfl⟩ : syracuseStep 4149947 = 6224921) B6224921
theorem B2766631 : Blo 2185435 2766631 := bstep (se 1 (by rfl) ⟨2074973, by rfl⟩ : syracuseStep 2766631 = 4149947) B4149947
theorem B3688841 : Blo 2185435 3688841 := bstep (se 2 (by rfl) ⟨1383315, by rfl⟩ : syracuseStep 3688841 = 2766631) B2766631
theorem B2459227 : Blo 2185435 2459227 := bstep (se 1 (by rfl) ⟨1844420, by rfl⟩ : syracuseStep 2459227 = 3688841) B3688841
theorem B3278969 : Blo 2185435 3278969 := bstep (se 2 (by rfl) ⟨1229613, by rfl⟩ : syracuseStep 3278969 = 2459227) B2459227
theorem B2185979 : Blo 2185435 2185979 := bstep (se 1 (by rfl) ⟨1639484, by rfl⟩ : syracuseStep 2185979 = 3278969) B3278969
theorem B5608765 : Blo 2185435 5608765 := bbase (se 3 (by rfl) ⟨1051643, by rfl⟩ : syracuseStep 5608765 = 2103287) (by norm_num)
theorem B7478353 : Blo 2185435 7478353 := bstep (se 2 (by rfl) ⟨2804382, by rfl⟩ : syracuseStep 7478353 = 5608765) B5608765
theorem B9971137 : Blo 2185435 9971137 := bstep (se 2 (by rfl) ⟨3739176, by rfl⟩ : syracuseStep 9971137 = 7478353) B7478353
theorem B13294849 : Blo 2185435 13294849 := bstep (se 2 (by rfl) ⟨4985568, by rfl⟩ : syracuseStep 13294849 = 9971137) B9971137
theorem B17726465 : Blo 2185435 17726465 := bstep (se 2 (by rfl) ⟨6647424, by rfl⟩ : syracuseStep 17726465 = 13294849) B13294849
theorem B11817643 : Blo 2185435 11817643 := bstep (se 1 (by rfl) ⟨8863232, by rfl⟩ : syracuseStep 11817643 = 17726465) B17726465
theorem B15756857 : Blo 2185435 15756857 := bstep (se 2 (by rfl) ⟨5908821, by rfl⟩ : syracuseStep 15756857 = 11817643) B11817643
theorem B10504571 : Blo 2185435 10504571 := bstep (se 1 (by rfl) ⟨7878428, by rfl⟩ : syracuseStep 10504571 = 15756857) B15756857
theorem B28012189 : Blo 2185435 28012189 := bstep (se 3 (by rfl) ⟨5252285, by rfl⟩ : syracuseStep 28012189 = 10504571) B10504571
theorem B37349585 : Blo 2185435 37349585 := bstep (se 2 (by rfl) ⟨14006094, by rfl⟩ : syracuseStep 37349585 = 28012189) B28012189
theorem B24899723 : Blo 2185435 24899723 := bstep (se 1 (by rfl) ⟨18674792, by rfl⟩ : syracuseStep 24899723 = 37349585) B37349585
theorem B16599815 : Blo 2185435 16599815 := bstep (se 1 (by rfl) ⟨12449861, by rfl⟩ : syracuseStep 16599815 = 24899723) B24899723
theorem B11066543 : Blo 2185435 11066543 := bstep (se 1 (by rfl) ⟨8299907, by rfl⟩ : syracuseStep 11066543 = 16599815) B16599815
theorem B7377695 : Blo 2185435 7377695 := bstep (se 1 (by rfl) ⟨5533271, by rfl⟩ : syracuseStep 7377695 = 11066543) B11066543
theorem B4918463 : Blo 2185435 4918463 := bstep (se 1 (by rfl) ⟨3688847, by rfl⟩ : syracuseStep 4918463 = 7377695) B7377695
theorem B3278975 : Blo 2185435 3278975 := bstep (se 1 (by rfl) ⟨2459231, by rfl⟩ : syracuseStep 3278975 = 4918463) B4918463
theorem B2185983 : Blo 2185435 2185983 := bstep (se 1 (by rfl) ⟨1639487, by rfl⟩ : syracuseStep 2185983 = 3278975) B3278975
theorem B3278981 : Blo 2185435 3278981 := bbase (se 4 (by rfl) ⟨307404, by rfl⟩ : syracuseStep 3278981 = 614809) (by norm_num)
theorem B2185987 : Blo 2185435 2185987 := bstep (se 1 (by rfl) ⟨1639490, by rfl⟩ : syracuseStep 2185987 = 3278981) B3278981
theorem B3688861 : Blo 2185435 3688861 := bbase (se 3 (by rfl) ⟨691661, by rfl⟩ : syracuseStep 3688861 = 1383323) (by norm_num)
theorem B4918481 : Blo 2185435 4918481 := bstep (se 2 (by rfl) ⟨1844430, by rfl⟩ : syracuseStep 4918481 = 3688861) B3688861
theorem B3278987 : Blo 2185435 3278987 := bstep (se 1 (by rfl) ⟨2459240, by rfl⟩ : syracuseStep 3278987 = 4918481) B4918481
theorem B2185991 : Blo 2185435 2185991 := bstep (se 1 (by rfl) ⟨1639493, by rfl⟩ : syracuseStep 2185991 = 3278987) B3278987
theorem B2459245 : Blo 2185435 2459245 := bbase (se 3 (by rfl) ⟨461108, by rfl⟩ : syracuseStep 2459245 = 922217) (by norm_num)
theorem B3278993 : Blo 2185435 3278993 := bstep (se 2 (by rfl) ⟨1229622, by rfl⟩ : syracuseStep 3278993 = 2459245) B2459245
theorem B2185995 : Blo 2185435 2185995 := bstep (se 1 (by rfl) ⟨1639496, by rfl⟩ : syracuseStep 2185995 = 3278993) B3278993
theorem B7377749 : Blo 2185435 7377749 := bbase (se 9 (by rfl) ⟨21614, by rfl⟩ : syracuseStep 7377749 = 43229) (by norm_num)
theorem B4918499 : Blo 2185435 4918499 := bstep (se 1 (by rfl) ⟨3688874, by rfl⟩ : syracuseStep 4918499 = 7377749) B7377749
theorem B3278999 : Blo 2185435 3278999 := bstep (se 1 (by rfl) ⟨2459249, by rfl⟩ : syracuseStep 3278999 = 4918499) B4918499
theorem B2185999 : Blo 2185435 2185999 := bstep (se 1 (by rfl) ⟨1639499, by rfl⟩ : syracuseStep 2185999 = 3278999) B3278999
theorem B3279005 : Blo 2185435 3279005 := bbase (se 3 (by rfl) ⟨614813, by rfl⟩ : syracuseStep 3279005 = 1229627) (by norm_num)
theorem B2186003 : Blo 2185435 2186003 := bstep (se 1 (by rfl) ⟨1639502, by rfl⟩ : syracuseStep 2186003 = 3279005) B3279005
theorem B4918517 : Blo 2185435 4918517 := bbase (se 5 (by rfl) ⟨230555, by rfl⟩ : syracuseStep 4918517 = 461111) (by norm_num)
theorem B3279011 : Blo 2185435 3279011 := bstep (se 1 (by rfl) ⟨2459258, by rfl⟩ : syracuseStep 3279011 = 4918517) B4918517
theorem B2186007 : Blo 2185435 2186007 := bstep (se 1 (by rfl) ⟨1639505, by rfl⟩ : syracuseStep 2186007 = 3279011) B3279011
theorem B4206629 : Blo 2185435 4206629 := bbase (se 4 (by rfl) ⟨394371, by rfl⟩ : syracuseStep 4206629 = 788743) (by norm_num)
theorem B2804419 : Blo 2185435 2804419 := bstep (se 1 (by rfl) ⟨2103314, by rfl⟩ : syracuseStep 2804419 = 4206629) B4206629
theorem B3739225 : Blo 2185435 3739225 := bstep (se 2 (by rfl) ⟨1402209, by rfl⟩ : syracuseStep 3739225 = 2804419) B2804419
theorem B4985633 : Blo 2185435 4985633 := bstep (se 2 (by rfl) ⟨1869612, by rfl⟩ : syracuseStep 4985633 = 3739225) B3739225
theorem B13295021 : Blo 2185435 13295021 := bstep (se 3 (by rfl) ⟨2492816, by rfl⟩ : syracuseStep 13295021 = 4985633) B4985633
theorem B35453389 : Blo 2185435 35453389 := bstep (se 3 (by rfl) ⟨6647510, by rfl⟩ : syracuseStep 35453389 = 13295021) B13295021
theorem B47271185 : Blo 2185435 47271185 := bstep (se 2 (by rfl) ⟨17726694, by rfl⟩ : syracuseStep 47271185 = 35453389) B35453389
theorem B31514123 : Blo 2185435 31514123 := bstep (se 1 (by rfl) ⟨23635592, by rfl⟩ : syracuseStep 31514123 = 47271185) B47271185
theorem B21009415 : Blo 2185435 21009415 := bstep (se 1 (by rfl) ⟨15757061, by rfl⟩ : syracuseStep 21009415 = 31514123) B31514123
theorem B28012553 : Blo 2185435 28012553 := bstep (se 2 (by rfl) ⟨10504707, by rfl⟩ : syracuseStep 28012553 = 21009415) B21009415
theorem B18675035 : Blo 2185435 18675035 := bstep (se 1 (by rfl) ⟨14006276, by rfl⟩ : syracuseStep 18675035 = 28012553) B28012553
theorem B12450023 : Blo 2185435 12450023 := bstep (se 1 (by rfl) ⟨9337517, by rfl⟩ : syracuseStep 12450023 = 18675035) B18675035
theorem B8300015 : Blo 2185435 8300015 := bstep (se 1 (by rfl) ⟨6225011, by rfl⟩ : syracuseStep 8300015 = 12450023) B12450023
theorem B5533343 : Blo 2185435 5533343 := bstep (se 1 (by rfl) ⟨4150007, by rfl⟩ : syracuseStep 5533343 = 8300015) B8300015
theorem B3688895 : Blo 2185435 3688895 := bstep (se 1 (by rfl) ⟨2766671, by rfl⟩ : syracuseStep 3688895 = 5533343) B5533343
theorem B2459263 : Blo 2185435 2459263 := bstep (se 1 (by rfl) ⟨1844447, by rfl⟩ : syracuseStep 2459263 = 3688895) B3688895
theorem B3279017 : Blo 2185435 3279017 := bstep (se 2 (by rfl) ⟨1229631, by rfl⟩ : syracuseStep 3279017 = 2459263) B2459263
theorem B2186011 : Blo 2185435 2186011 := bstep (se 1 (by rfl) ⟨1639508, by rfl⟩ : syracuseStep 2186011 = 3279017) B3279017
theorem B2215841 : Blo 2185435 2215841 := bbase (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) (by norm_num)
theorem B23635637 : Blo 2185435 23635637 := bstep (se 5 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 23635637 = 2215841) B2215841
theorem B15757091 : Blo 2185435 15757091 := bstep (se 1 (by rfl) ⟨11817818, by rfl⟩ : syracuseStep 15757091 = 23635637) B23635637
theorem B10504727 : Blo 2185435 10504727 := bstep (se 1 (by rfl) ⟨7878545, by rfl⟩ : syracuseStep 10504727 = 15757091) B15757091
theorem B7003151 : Blo 2185435 7003151 := bstep (se 1 (by rfl) ⟨5252363, by rfl⟩ : syracuseStep 7003151 = 10504727) B10504727
theorem B4668767 : Blo 2185435 4668767 := bstep (se 1 (by rfl) ⟨3501575, by rfl⟩ : syracuseStep 4668767 = 7003151) B7003151
theorem B3112511 : Blo 2185435 3112511 := bstep (se 1 (by rfl) ⟨2334383, by rfl⟩ : syracuseStep 3112511 = 4668767) B4668767
theorem B8300029 : Blo 2185435 8300029 := bstep (se 3 (by rfl) ⟨1556255, by rfl⟩ : syracuseStep 8300029 = 3112511) B3112511
theorem B11066705 : Blo 2185435 11066705 := bstep (se 2 (by rfl) ⟨4150014, by rfl⟩ : syracuseStep 11066705 = 8300029) B8300029
theorem B7377803 : Blo 2185435 7377803 := bstep (se 1 (by rfl) ⟨5533352, by rfl⟩ : syracuseStep 7377803 = 11066705) B11066705
theorem B4918535 : Blo 2185435 4918535 := bstep (se 1 (by rfl) ⟨3688901, by rfl⟩ : syracuseStep 4918535 = 7377803) B7377803
theorem B3279023 : Blo 2185435 3279023 := bstep (se 1 (by rfl) ⟨2459267, by rfl⟩ : syracuseStep 3279023 = 4918535) B4918535
theorem B2186015 : Blo 2185435 2186015 := bstep (se 1 (by rfl) ⟨1639511, by rfl⟩ : syracuseStep 2186015 = 3279023) B3279023
theorem B3279029 : Blo 2185435 3279029 := bbase (se 5 (by rfl) ⟨153704, by rfl⟩ : syracuseStep 3279029 = 307409) (by norm_num)
theorem B2186019 : Blo 2185435 2186019 := bstep (se 1 (by rfl) ⟨1639514, by rfl⟩ : syracuseStep 2186019 = 3279029) B3279029
theorem B5533373 : Blo 2185435 5533373 := bbase (se 3 (by rfl) ⟨1037507, by rfl⟩ : syracuseStep 5533373 = 2075015) (by norm_num)
theorem B3688915 : Blo 2185435 3688915 := bstep (se 1 (by rfl) ⟨2766686, by rfl⟩ : syracuseStep 3688915 = 5533373) B5533373
theorem B4918553 : Blo 2185435 4918553 := bstep (se 2 (by rfl) ⟨1844457, by rfl⟩ : syracuseStep 4918553 = 3688915) B3688915
theorem B3279035 : Blo 2185435 3279035 := bstep (se 1 (by rfl) ⟨2459276, by rfl⟩ : syracuseStep 3279035 = 4918553) B4918553
theorem B2186023 : Blo 2185435 2186023 := bstep (se 1 (by rfl) ⟨1639517, by rfl⟩ : syracuseStep 2186023 = 3279035) B3279035
theorem B2459281 : Blo 2185435 2459281 := bbase (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) (by norm_num)
theorem B3279041 : Blo 2185435 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B2186027 : Blo 2185435 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B4150045 : Blo 2185435 4150045 := bbase (se 3 (by rfl) ⟨778133, by rfl⟩ : syracuseStep 4150045 = 1556267) (by norm_num)
theorem B5533393 : Blo 2185435 5533393 := bstep (se 2 (by rfl) ⟨2075022, by rfl⟩ : syracuseStep 5533393 = 4150045) B4150045
theorem B7377857 : Blo 2185435 7377857 := bstep (se 2 (by rfl) ⟨2766696, by rfl⟩ : syracuseStep 7377857 = 5533393) B5533393
theorem B4918571 : Blo 2185435 4918571 := bstep (se 1 (by rfl) ⟨3688928, by rfl⟩ : syracuseStep 4918571 = 7377857) B7377857
theorem B3279047 : Blo 2185435 3279047 := bstep (se 1 (by rfl) ⟨2459285, by rfl⟩ : syracuseStep 3279047 = 4918571) B4918571
theorem B2186031 : Blo 2185435 2186031 := bstep (se 1 (by rfl) ⟨1639523, by rfl⟩ : syracuseStep 2186031 = 3279047) B3279047
theorem B3279053 : Blo 2185435 3279053 := bbase (se 3 (by rfl) ⟨614822, by rfl⟩ : syracuseStep 3279053 = 1229645) (by norm_num)
theorem B2186035 : Blo 2185435 2186035 := bstep (se 1 (by rfl) ⟨1639526, by rfl⟩ : syracuseStep 2186035 = 3279053) B3279053
theorem B4918589 : Blo 2185435 4918589 := bbase (se 3 (by rfl) ⟨922235, by rfl⟩ : syracuseStep 4918589 = 1844471) (by norm_num)
theorem B3279059 : Blo 2185435 3279059 := bstep (se 1 (by rfl) ⟨2459294, by rfl⟩ : syracuseStep 3279059 = 4918589) B4918589
theorem B2186039 : Blo 2185435 2186039 := bstep (se 1 (by rfl) ⟨1639529, by rfl⟩ : syracuseStep 2186039 = 3279059) B3279059
theorem B3688949 : Blo 2185435 3688949 := bbase (se 5 (by rfl) ⟨172919, by rfl⟩ : syracuseStep 3688949 = 345839) (by norm_num)
theorem B2459299 : Blo 2185435 2459299 := bstep (se 1 (by rfl) ⟨1844474, by rfl⟩ : syracuseStep 2459299 = 3688949) B3688949
theorem B3279065 : Blo 2185435 3279065 := bstep (se 2 (by rfl) ⟨1229649, by rfl⟩ : syracuseStep 3279065 = 2459299) B2459299
theorem B2186043 : Blo 2185435 2186043 := bstep (se 1 (by rfl) ⟨1639532, by rfl⟩ : syracuseStep 2186043 = 3279065) B3279065
theorem B7003253 : Blo 2185435 7003253 := bbase (se 5 (by rfl) ⟨328277, by rfl⟩ : syracuseStep 7003253 = 656555) (by norm_num)
theorem B4668835 : Blo 2185435 4668835 := bstep (se 1 (by rfl) ⟨3501626, by rfl⟩ : syracuseStep 4668835 = 7003253) B7003253
theorem B6225113 : Blo 2185435 6225113 := bstep (se 2 (by rfl) ⟨2334417, by rfl⟩ : syracuseStep 6225113 = 4668835) B4668835
theorem B16600301 : Blo 2185435 16600301 := bstep (se 3 (by rfl) ⟨3112556, by rfl⟩ : syracuseStep 16600301 = 6225113) B6225113
theorem B11066867 : Blo 2185435 11066867 := bstep (se 1 (by rfl) ⟨8300150, by rfl⟩ : syracuseStep 11066867 = 16600301) B16600301
theorem B7377911 : Blo 2185435 7377911 := bstep (se 1 (by rfl) ⟨5533433, by rfl⟩ : syracuseStep 7377911 = 11066867) B11066867
theorem B4918607 : Blo 2185435 4918607 := bstep (se 1 (by rfl) ⟨3688955, by rfl⟩ : syracuseStep 4918607 = 7377911) B7377911
theorem B3279071 : Blo 2185435 3279071 := bstep (se 1 (by rfl) ⟨2459303, by rfl⟩ : syracuseStep 3279071 = 4918607) B4918607
theorem B2186047 : Blo 2185435 2186047 := bstep (se 1 (by rfl) ⟨1639535, by rfl⟩ : syracuseStep 2186047 = 3279071) B3279071
theorem B3279077 : Blo 2185435 3279077 := bbase (se 4 (by rfl) ⟨307413, by rfl⟩ : syracuseStep 3279077 = 614827) (by norm_num)
theorem B2186051 : Blo 2185435 2186051 := bstep (se 1 (by rfl) ⟨1639538, by rfl⟩ : syracuseStep 2186051 = 3279077) B3279077
theorem B4668853 : Blo 2185435 4668853 := bbase (se 5 (by rfl) ⟨218852, by rfl⟩ : syracuseStep 4668853 = 437705) (by norm_num)
theorem B6225137 : Blo 2185435 6225137 := bstep (se 2 (by rfl) ⟨2334426, by rfl⟩ : syracuseStep 6225137 = 4668853) B4668853
theorem B4150091 : Blo 2185435 4150091 := bstep (se 1 (by rfl) ⟨3112568, by rfl⟩ : syracuseStep 4150091 = 6225137) B6225137
theorem B2766727 : Blo 2185435 2766727 := bstep (se 1 (by rfl) ⟨2075045, by rfl⟩ : syracuseStep 2766727 = 4150091) B4150091
theorem B3688969 : Blo 2185435 3688969 := bstep (se 2 (by rfl) ⟨1383363, by rfl⟩ : syracuseStep 3688969 = 2766727) B2766727
theorem B4918625 : Blo 2185435 4918625 := bstep (se 2 (by rfl) ⟨1844484, by rfl⟩ : syracuseStep 4918625 = 3688969) B3688969
theorem B3279083 : Blo 2185435 3279083 := bstep (se 1 (by rfl) ⟨2459312, by rfl⟩ : syracuseStep 3279083 = 4918625) B4918625
theorem B2186055 : Blo 2185435 2186055 := bstep (se 1 (by rfl) ⟨1639541, by rfl⟩ : syracuseStep 2186055 = 3279083) B3279083
theorem B2459317 : Blo 2185435 2459317 := bbase (se 5 (by rfl) ⟨115280, by rfl⟩ : syracuseStep 2459317 = 230561) (by norm_num)
theorem B3279089 : Blo 2185435 3279089 := bstep (se 2 (by rfl) ⟨1229658, by rfl⟩ : syracuseStep 3279089 = 2459317) B2459317
theorem B2186059 : Blo 2185435 2186059 := bstep (se 1 (by rfl) ⟨1639544, by rfl⟩ : syracuseStep 2186059 = 3279089) B3279089
theorem B2766737 : Blo 2185435 2766737 := bbase (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) (by norm_num)
theorem B7377965 : Blo 2185435 7377965 := bstep (se 3 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 7377965 = 2766737) B2766737
theorem B4918643 : Blo 2185435 4918643 := bstep (se 1 (by rfl) ⟨3688982, by rfl⟩ : syracuseStep 4918643 = 7377965) B7377965
theorem B3279095 : Blo 2185435 3279095 := bstep (se 1 (by rfl) ⟨2459321, by rfl⟩ : syracuseStep 3279095 = 4918643) B4918643
theorem B2186063 : Blo 2185435 2186063 := bstep (se 1 (by rfl) ⟨1639547, by rfl⟩ : syracuseStep 2186063 = 3279095) B3279095
theorem B3279101 : Blo 2185435 3279101 := bbase (se 3 (by rfl) ⟨614831, by rfl⟩ : syracuseStep 3279101 = 1229663) (by norm_num)
theorem B2186067 : Blo 2185435 2186067 := bstep (se 1 (by rfl) ⟨1639550, by rfl⟩ : syracuseStep 2186067 = 3279101) B3279101
theorem B4918661 : Blo 2185435 4918661 := bbase (se 4 (by rfl) ⟨461124, by rfl⟩ : syracuseStep 4918661 = 922249) (by norm_num)
theorem B3279107 : Blo 2185435 3279107 := bstep (se 1 (by rfl) ⟨2459330, by rfl⟩ : syracuseStep 3279107 = 4918661) B4918661
theorem B2186071 : Blo 2185435 2186071 := bstep (se 1 (by rfl) ⟨1639553, by rfl⟩ : syracuseStep 2186071 = 3279107) B3279107
theorem B3112597 : Blo 2185435 3112597 := bbase (se 6 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 3112597 = 145903) (by norm_num)
theorem B4150129 : Blo 2185435 4150129 := bstep (se 2 (by rfl) ⟨1556298, by rfl⟩ : syracuseStep 4150129 = 3112597) B3112597
theorem B5533505 : Blo 2185435 5533505 := bstep (se 2 (by rfl) ⟨2075064, by rfl⟩ : syracuseStep 5533505 = 4150129) B4150129
theorem B3689003 : Blo 2185435 3689003 := bstep (se 1 (by rfl) ⟨2766752, by rfl⟩ : syracuseStep 3689003 = 5533505) B5533505
theorem B2459335 : Blo 2185435 2459335 := bstep (se 1 (by rfl) ⟨1844501, by rfl⟩ : syracuseStep 2459335 = 3689003) B3689003
theorem B3279113 : Blo 2185435 3279113 := bstep (se 2 (by rfl) ⟨1229667, by rfl⟩ : syracuseStep 3279113 = 2459335) B2459335
theorem B2186075 : Blo 2185435 2186075 := bstep (se 1 (by rfl) ⟨1639556, by rfl⟩ : syracuseStep 2186075 = 3279113) B3279113
theorem B11067029 : Blo 2185435 11067029 := bbase (se 6 (by rfl) ⟨259383, by rfl⟩ : syracuseStep 11067029 = 518767) (by norm_num)
theorem B7378019 : Blo 2185435 7378019 := bstep (se 1 (by rfl) ⟨5533514, by rfl⟩ : syracuseStep 7378019 = 11067029) B11067029
theorem B4918679 : Blo 2185435 4918679 := bstep (se 1 (by rfl) ⟨3689009, by rfl⟩ : syracuseStep 4918679 = 7378019) B7378019
theorem B3279119 : Blo 2185435 3279119 := bstep (se 1 (by rfl) ⟨2459339, by rfl⟩ : syracuseStep 3279119 = 4918679) B4918679
theorem B2186079 : Blo 2185435 2186079 := bstep (se 1 (by rfl) ⟨1639559, by rfl⟩ : syracuseStep 2186079 = 3279119) B3279119
theorem B3279125 : Blo 2185435 3279125 := bbase (se 6 (by rfl) ⟨76854, by rfl⟩ : syracuseStep 3279125 = 153709) (by norm_num)
theorem B2186083 : Blo 2185435 2186083 := bstep (se 1 (by rfl) ⟨1639562, by rfl⟩ : syracuseStep 2186083 = 3279125) B3279125
theorem B28013525 : Blo 2185435 28013525 := bbase (se 7 (by rfl) ⟨328283, by rfl⟩ : syracuseStep 28013525 = 656567) (by norm_num)
theorem B18675683 : Blo 2185435 18675683 := bstep (se 1 (by rfl) ⟨14006762, by rfl⟩ : syracuseStep 18675683 = 28013525) B28013525
theorem B12450455 : Blo 2185435 12450455 := bstep (se 1 (by rfl) ⟨9337841, by rfl⟩ : syracuseStep 12450455 = 18675683) B18675683
theorem B8300303 : Blo 2185435 8300303 := bstep (se 1 (by rfl) ⟨6225227, by rfl⟩ : syracuseStep 8300303 = 12450455) B12450455
theorem B5533535 : Blo 2185435 5533535 := bstep (se 1 (by rfl) ⟨4150151, by rfl⟩ : syracuseStep 5533535 = 8300303) B8300303
theorem B3689023 : Blo 2185435 3689023 := bstep (se 1 (by rfl) ⟨2766767, by rfl⟩ : syracuseStep 3689023 = 5533535) B5533535
theorem B4918697 : Blo 2185435 4918697 := bstep (se 2 (by rfl) ⟨1844511, by rfl⟩ : syracuseStep 4918697 = 3689023) B3689023
theorem B3279131 : Blo 2185435 3279131 := bstep (se 1 (by rfl) ⟨2459348, by rfl⟩ : syracuseStep 3279131 = 4918697) B4918697
theorem B2186087 : Blo 2185435 2186087 := bstep (se 1 (by rfl) ⟨1639565, by rfl⟩ : syracuseStep 2186087 = 3279131) B3279131
theorem B2459353 : Blo 2185435 2459353 := bbase (se 2 (by rfl) ⟨922257, by rfl⟩ : syracuseStep 2459353 = 1844515) (by norm_num)
theorem B3279137 : Blo 2185435 3279137 := bstep (se 2 (by rfl) ⟨1229676, by rfl⟩ : syracuseStep 3279137 = 2459353) B2459353
theorem B2186091 : Blo 2185435 2186091 := bstep (se 1 (by rfl) ⟨1639568, by rfl⟩ : syracuseStep 2186091 = 3279137) B3279137
theorem B2334469 : Blo 2185435 2334469 := bbase (se 4 (by rfl) ⟨218856, by rfl⟩ : syracuseStep 2334469 = 437713) (by norm_num)
theorem B3112625 : Blo 2185435 3112625 := bstep (se 2 (by rfl) ⟨1167234, by rfl⟩ : syracuseStep 3112625 = 2334469) B2334469
theorem B8300333 : Blo 2185435 8300333 := bstep (se 3 (by rfl) ⟨1556312, by rfl⟩ : syracuseStep 8300333 = 3112625) B3112625
theorem B5533555 : Blo 2185435 5533555 := bstep (se 1 (by rfl) ⟨4150166, by rfl⟩ : syracuseStep 5533555 = 8300333) B8300333
theorem B7378073 : Blo 2185435 7378073 := bstep (se 2 (by rfl) ⟨2766777, by rfl⟩ : syracuseStep 7378073 = 5533555) B5533555
theorem B4918715 : Blo 2185435 4918715 := bstep (se 1 (by rfl) ⟨3689036, by rfl⟩ : syracuseStep 4918715 = 7378073) B7378073
theorem B3279143 : Blo 2185435 3279143 := bstep (se 1 (by rfl) ⟨2459357, by rfl⟩ : syracuseStep 3279143 = 4918715) B4918715
theorem B2186095 : Blo 2185435 2186095 := bstep (se 1 (by rfl) ⟨1639571, by rfl⟩ : syracuseStep 2186095 = 3279143) B3279143
theorem B3279149 : Blo 2185435 3279149 := bbase (se 3 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 3279149 = 1229681) (by norm_num)
theorem B2186099 : Blo 2185435 2186099 := bstep (se 1 (by rfl) ⟨1639574, by rfl⟩ : syracuseStep 2186099 = 3279149) B3279149
theorem B4918733 : Blo 2185435 4918733 := bbase (se 3 (by rfl) ⟨922262, by rfl⟩ : syracuseStep 4918733 = 1844525) (by norm_num)
theorem B3279155 : Blo 2185435 3279155 := bstep (se 1 (by rfl) ⟨2459366, by rfl⟩ : syracuseStep 3279155 = 4918733) B4918733
theorem B2186103 : Blo 2185435 2186103 := bstep (se 1 (by rfl) ⟨1639577, by rfl⟩ : syracuseStep 2186103 = 3279155) B3279155
theorem B2766793 : Blo 2185435 2766793 := bbase (se 2 (by rfl) ⟨1037547, by rfl⟩ : syracuseStep 2766793 = 2075095) (by norm_num)
theorem B3689057 : Blo 2185435 3689057 := bstep (se 2 (by rfl) ⟨1383396, by rfl⟩ : syracuseStep 3689057 = 2766793) B2766793
theorem B2459371 : Blo 2185435 2459371 := bstep (se 1 (by rfl) ⟨1844528, by rfl⟩ : syracuseStep 2459371 = 3689057) B3689057
theorem B3279161 : Blo 2185435 3279161 := bstep (se 2 (by rfl) ⟨1229685, by rfl⟩ : syracuseStep 3279161 = 2459371) B2459371
theorem B2186107 : Blo 2185435 2186107 := bstep (se 1 (by rfl) ⟨1639580, by rfl⟩ : syracuseStep 2186107 = 3279161) B3279161
theorem B3939445 : Blo 2185435 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B21010373 : Blo 2185435 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B14006915 : Blo 2185435 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B9337943 : Blo 2185435 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B24901181 : Blo 2185435 24901181 := bstep (se 3 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 24901181 = 9337943) B9337943
theorem B16600787 : Blo 2185435 16600787 := bstep (se 1 (by rfl) ⟨12450590, by rfl⟩ : syracuseStep 16600787 = 24901181) B24901181
theorem B11067191 : Blo 2185435 11067191 := bstep (se 1 (by rfl) ⟨8300393, by rfl⟩ : syracuseStep 11067191 = 16600787) B16600787
theorem B7378127 : Blo 2185435 7378127 := bstep (se 1 (by rfl) ⟨5533595, by rfl⟩ : syracuseStep 7378127 = 11067191) B11067191
theorem B4918751 : Blo 2185435 4918751 := bstep (se 1 (by rfl) ⟨3689063, by rfl⟩ : syracuseStep 4918751 = 7378127) B7378127
theorem B3279167 : Blo 2185435 3279167 := bstep (se 1 (by rfl) ⟨2459375, by rfl⟩ : syracuseStep 3279167 = 4918751) B4918751
theorem B2186111 : Blo 2185435 2186111 := bstep (se 1 (by rfl) ⟨1639583, by rfl⟩ : syracuseStep 2186111 = 3279167) B3279167
theorem B3279173 : Blo 2185435 3279173 := bbase (se 4 (by rfl) ⟨307422, by rfl⟩ : syracuseStep 3279173 = 614845) (by norm_num)
theorem B2186115 : Blo 2185435 2186115 := bstep (se 1 (by rfl) ⟨1639586, by rfl⟩ : syracuseStep 2186115 = 3279173) B3279173
theorem B3689077 : Blo 2185435 3689077 := bbase (se 5 (by rfl) ⟨172925, by rfl⟩ : syracuseStep 3689077 = 345851) (by norm_num)
theorem B4918769 : Blo 2185435 4918769 := bstep (se 2 (by rfl) ⟨1844538, by rfl⟩ : syracuseStep 4918769 = 3689077) B3689077
theorem B3279179 : Blo 2185435 3279179 := bstep (se 1 (by rfl) ⟨2459384, by rfl⟩ : syracuseStep 3279179 = 4918769) B4918769
theorem B2186119 : Blo 2185435 2186119 := bstep (se 1 (by rfl) ⟨1639589, by rfl⟩ : syracuseStep 2186119 = 3279179) B3279179
theorem B2459389 : Blo 2185435 2459389 := bbase (se 3 (by rfl) ⟨461135, by rfl⟩ : syracuseStep 2459389 = 922271) (by norm_num)
theorem B3279185 : Blo 2185435 3279185 := bstep (se 2 (by rfl) ⟨1229694, by rfl⟩ : syracuseStep 3279185 = 2459389) B2459389
theorem B2186123 : Blo 2185435 2186123 := bstep (se 1 (by rfl) ⟨1639592, by rfl⟩ : syracuseStep 2186123 = 3279185) B3279185
theorem B7378181 : Blo 2185435 7378181 := bbase (se 4 (by rfl) ⟨691704, by rfl⟩ : syracuseStep 7378181 = 1383409) (by norm_num)
theorem B4918787 : Blo 2185435 4918787 := bstep (se 1 (by rfl) ⟨3689090, by rfl⟩ : syracuseStep 4918787 = 7378181) B7378181
theorem B3279191 : Blo 2185435 3279191 := bstep (se 1 (by rfl) ⟨2459393, by rfl⟩ : syracuseStep 3279191 = 4918787) B4918787
theorem B2186127 : Blo 2185435 2186127 := bstep (se 1 (by rfl) ⟨1639595, by rfl⟩ : syracuseStep 2186127 = 3279191) B3279191
theorem B3279197 : Blo 2185435 3279197 := bbase (se 3 (by rfl) ⟨614849, by rfl⟩ : syracuseStep 3279197 = 1229699) (by norm_num)
theorem B2186131 : Blo 2185435 2186131 := bstep (se 1 (by rfl) ⟨1639598, by rfl⟩ : syracuseStep 2186131 = 3279197) B3279197
theorem B4918805 : Blo 2185435 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B3279203 : Blo 2185435 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B2186135 : Blo 2185435 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B8300501 : Blo 2185435 8300501 := bbase (se 7 (by rfl) ⟨97271, by rfl⟩ : syracuseStep 8300501 = 194543) (by norm_num)
theorem B5533667 : Blo 2185435 5533667 := bstep (se 1 (by rfl) ⟨4150250, by rfl⟩ : syracuseStep 5533667 = 8300501) B8300501
theorem B3689111 : Blo 2185435 3689111 := bstep (se 1 (by rfl) ⟨2766833, by rfl⟩ : syracuseStep 3689111 = 5533667) B5533667
theorem B2459407 : Blo 2185435 2459407 := bstep (se 1 (by rfl) ⟨1844555, by rfl⟩ : syracuseStep 2459407 = 3689111) B3689111
theorem B3279209 : Blo 2185435 3279209 := bstep (se 2 (by rfl) ⟨1229703, by rfl⟩ : syracuseStep 3279209 = 2459407) B2459407
theorem B2186139 : Blo 2185435 2186139 := bstep (se 1 (by rfl) ⟨1639604, by rfl⟩ : syracuseStep 2186139 = 3279209) B3279209
theorem B12450773 : Blo 2185435 12450773 := bbase (se 7 (by rfl) ⟨145907, by rfl⟩ : syracuseStep 12450773 = 291815) (by norm_num)
theorem B8300515 : Blo 2185435 8300515 := bstep (se 1 (by rfl) ⟨6225386, by rfl⟩ : syracuseStep 8300515 = 12450773) B12450773
theorem B11067353 : Blo 2185435 11067353 := bstep (se 2 (by rfl) ⟨4150257, by rfl⟩ : syracuseStep 11067353 = 8300515) B8300515
theorem B7378235 : Blo 2185435 7378235 := bstep (se 1 (by rfl) ⟨5533676, by rfl⟩ : syracuseStep 7378235 = 11067353) B11067353
theorem B4918823 : Blo 2185435 4918823 := bstep (se 1 (by rfl) ⟨3689117, by rfl⟩ : syracuseStep 4918823 = 7378235) B7378235
theorem B3279215 : Blo 2185435 3279215 := bstep (se 1 (by rfl) ⟨2459411, by rfl⟩ : syracuseStep 3279215 = 4918823) B4918823
theorem B2186143 : Blo 2185435 2186143 := bstep (se 1 (by rfl) ⟨1639607, by rfl⟩ : syracuseStep 2186143 = 3279215) B3279215
theorem B3279221 : Blo 2185435 3279221 := bbase (se 5 (by rfl) ⟨153713, by rfl⟩ : syracuseStep 3279221 = 307427) (by norm_num)
theorem B2186147 : Blo 2185435 2186147 := bstep (se 1 (by rfl) ⟨1639610, by rfl⟩ : syracuseStep 2186147 = 3279221) B3279221
theorem B2334529 : Blo 2185435 2334529 := bbase (se 2 (by rfl) ⟨875448, by rfl⟩ : syracuseStep 2334529 = 1750897) (by norm_num)
theorem B3112705 : Blo 2185435 3112705 := bstep (se 2 (by rfl) ⟨1167264, by rfl⟩ : syracuseStep 3112705 = 2334529) B2334529
theorem B4150273 : Blo 2185435 4150273 := bstep (se 2 (by rfl) ⟨1556352, by rfl⟩ : syracuseStep 4150273 = 3112705) B3112705
theorem B5533697 : Blo 2185435 5533697 := bstep (se 2 (by rfl) ⟨2075136, by rfl⟩ : syracuseStep 5533697 = 4150273) B4150273
theorem B3689131 : Blo 2185435 3689131 := bstep (se 1 (by rfl) ⟨2766848, by rfl⟩ : syracuseStep 3689131 = 5533697) B5533697
theorem B4918841 : Blo 2185435 4918841 := bstep (se 2 (by rfl) ⟨1844565, by rfl⟩ : syracuseStep 4918841 = 3689131) B3689131
theorem B3279227 : Blo 2185435 3279227 := bstep (se 1 (by rfl) ⟨2459420, by rfl⟩ : syracuseStep 3279227 = 4918841) B4918841
theorem B2186151 : Blo 2185435 2186151 := bstep (se 1 (by rfl) ⟨1639613, by rfl⟩ : syracuseStep 2186151 = 3279227) B3279227
theorem B2459425 : Blo 2185435 2459425 := bbase (se 2 (by rfl) ⟨922284, by rfl⟩ : syracuseStep 2459425 = 1844569) (by norm_num)
theorem B3279233 : Blo 2185435 3279233 := bstep (se 2 (by rfl) ⟨1229712, by rfl⟩ : syracuseStep 3279233 = 2459425) B2459425
theorem B2186155 : Blo 2185435 2186155 := bstep (se 1 (by rfl) ⟨1639616, by rfl⟩ : syracuseStep 2186155 = 3279233) B3279233
theorem B5533717 : Blo 2185435 5533717 := bbase (se 6 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 5533717 = 259393) (by norm_num)
theorem B7378289 : Blo 2185435 7378289 := bstep (se 2 (by rfl) ⟨2766858, by rfl⟩ : syracuseStep 7378289 = 5533717) B5533717
theorem B4918859 : Blo 2185435 4918859 := bstep (se 1 (by rfl) ⟨3689144, by rfl⟩ : syracuseStep 4918859 = 7378289) B7378289
theorem B3279239 : Blo 2185435 3279239 := bstep (se 1 (by rfl) ⟨2459429, by rfl⟩ : syracuseStep 3279239 = 4918859) B4918859
theorem B2186159 : Blo 2185435 2186159 := bstep (se 1 (by rfl) ⟨1639619, by rfl⟩ : syracuseStep 2186159 = 3279239) B3279239
theorem B3279245 : Blo 2185435 3279245 := bbase (se 3 (by rfl) ⟨614858, by rfl⟩ : syracuseStep 3279245 = 1229717) (by norm_num)
theorem B2186163 : Blo 2185435 2186163 := bstep (se 1 (by rfl) ⟨1639622, by rfl⟩ : syracuseStep 2186163 = 3279245) B3279245
theorem B4918877 : Blo 2185435 4918877 := bbase (se 3 (by rfl) ⟨922289, by rfl⟩ : syracuseStep 4918877 = 1844579) (by norm_num)
theorem B3279251 : Blo 2185435 3279251 := bstep (se 1 (by rfl) ⟨2459438, by rfl⟩ : syracuseStep 3279251 = 4918877) B4918877
theorem B2186167 : Blo 2185435 2186167 := bstep (se 1 (by rfl) ⟨1639625, by rfl⟩ : syracuseStep 2186167 = 3279251) B3279251
theorem B3689165 : Blo 2185435 3689165 := bbase (se 3 (by rfl) ⟨691718, by rfl⟩ : syracuseStep 3689165 = 1383437) (by norm_num)
theorem B2459443 : Blo 2185435 2459443 := bstep (se 1 (by rfl) ⟨1844582, by rfl⟩ : syracuseStep 2459443 = 3689165) B3689165
theorem B3279257 : Blo 2185435 3279257 := bstep (se 2 (by rfl) ⟨1229721, by rfl⟩ : syracuseStep 3279257 = 2459443) B2459443
theorem B2186171 : Blo 2185435 2186171 := bstep (se 1 (by rfl) ⟨1639628, by rfl⟩ : syracuseStep 2186171 = 3279257) B3279257
theorem B3324005 : Blo 2185435 3324005 := bbase (se 4 (by rfl) ⟨311625, by rfl⟩ : syracuseStep 3324005 = 623251) (by norm_num)
theorem B2216003 : Blo 2185435 2216003 := bstep (se 1 (by rfl) ⟨1662002, by rfl⟩ : syracuseStep 2216003 = 3324005) B3324005
theorem B5909341 : Blo 2185435 5909341 := bstep (se 3 (by rfl) ⟨1108001, by rfl⟩ : syracuseStep 5909341 = 2216003) B2216003
theorem B7879121 : Blo 2185435 7879121 := bstep (se 2 (by rfl) ⟨2954670, by rfl⟩ : syracuseStep 7879121 = 5909341) B5909341
theorem B5252747 : Blo 2185435 5252747 := bstep (se 1 (by rfl) ⟨3939560, by rfl⟩ : syracuseStep 5252747 = 7879121) B7879121
theorem B14007325 : Blo 2185435 14007325 := bstep (se 3 (by rfl) ⟨2626373, by rfl⟩ : syracuseStep 14007325 = 5252747) B5252747
theorem B18676433 : Blo 2185435 18676433 := bstep (se 2 (by rfl) ⟨7003662, by rfl⟩ : syracuseStep 18676433 = 14007325) B14007325
theorem B12450955 : Blo 2185435 12450955 := bstep (se 1 (by rfl) ⟨9338216, by rfl⟩ : syracuseStep 12450955 = 18676433) B18676433
theorem B16601273 : Blo 2185435 16601273 := bstep (se 2 (by rfl) ⟨6225477, by rfl⟩ : syracuseStep 16601273 = 12450955) B12450955
theorem B11067515 : Blo 2185435 11067515 := bstep (se 1 (by rfl) ⟨8300636, by rfl⟩ : syracuseStep 11067515 = 16601273) B16601273
theorem B7378343 : Blo 2185435 7378343 := bstep (se 1 (by rfl) ⟨5533757, by rfl⟩ : syracuseStep 7378343 = 11067515) B11067515
theorem B4918895 : Blo 2185435 4918895 := bstep (se 1 (by rfl) ⟨3689171, by rfl⟩ : syracuseStep 4918895 = 7378343) B7378343
theorem B3279263 : Blo 2185435 3279263 := bstep (se 1 (by rfl) ⟨2459447, by rfl⟩ : syracuseStep 3279263 = 4918895) B4918895
theorem B2186175 : Blo 2185435 2186175 := bstep (se 1 (by rfl) ⟨1639631, by rfl⟩ : syracuseStep 2186175 = 3279263) B3279263
theorem B3279269 : Blo 2185435 3279269 := bbase (se 4 (by rfl) ⟨307431, by rfl⟩ : syracuseStep 3279269 = 614863) (by norm_num)
theorem B2186179 : Blo 2185435 2186179 := bstep (se 1 (by rfl) ⟨1639634, by rfl⟩ : syracuseStep 2186179 = 3279269) B3279269
theorem B2766889 : Blo 2185435 2766889 := bbase (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) (by norm_num)
theorem B3689185 : Blo 2185435 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B4918913 : Blo 2185435 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B3279275 : Blo 2185435 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B2186183 : Blo 2185435 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B2459461 : Blo 2185435 2459461 := bbase (se 4 (by rfl) ⟨230574, by rfl⟩ : syracuseStep 2459461 = 461149) (by norm_num)
theorem B3279281 : Blo 2185435 3279281 := bstep (se 2 (by rfl) ⟨1229730, by rfl⟩ : syracuseStep 3279281 = 2459461) B2459461
theorem B2186187 : Blo 2185435 2186187 := bstep (se 1 (by rfl) ⟨1639640, by rfl⟩ : syracuseStep 2186187 = 3279281) B3279281
theorem B4150349 : Blo 2185435 4150349 := bbase (se 3 (by rfl) ⟨778190, by rfl⟩ : syracuseStep 4150349 = 1556381) (by norm_num)
theorem B2766899 : Blo 2185435 2766899 := bstep (se 1 (by rfl) ⟨2075174, by rfl⟩ : syracuseStep 2766899 = 4150349) B4150349
theorem B7378397 : Blo 2185435 7378397 := bstep (se 3 (by rfl) ⟨1383449, by rfl⟩ : syracuseStep 7378397 = 2766899) B2766899
theorem B4918931 : Blo 2185435 4918931 := bstep (se 1 (by rfl) ⟨3689198, by rfl⟩ : syracuseStep 4918931 = 7378397) B7378397
theorem B3279287 : Blo 2185435 3279287 := bstep (se 1 (by rfl) ⟨2459465, by rfl⟩ : syracuseStep 3279287 = 4918931) B4918931
theorem B2186191 : Blo 2185435 2186191 := bstep (se 1 (by rfl) ⟨1639643, by rfl⟩ : syracuseStep 2186191 = 3279287) B3279287
theorem B3279293 : Blo 2185435 3279293 := bbase (se 3 (by rfl) ⟨614867, by rfl⟩ : syracuseStep 3279293 = 1229735) (by norm_num)
theorem B2186195 : Blo 2185435 2186195 := bstep (se 1 (by rfl) ⟨1639646, by rfl⟩ : syracuseStep 2186195 = 3279293) B3279293
theorem B4918949 : Blo 2185435 4918949 := bbase (se 4 (by rfl) ⟨461151, by rfl⟩ : syracuseStep 4918949 = 922303) (by norm_num)
theorem B3279299 : Blo 2185435 3279299 := bstep (se 1 (by rfl) ⟨2459474, by rfl⟩ : syracuseStep 3279299 = 4918949) B4918949
theorem B2186199 : Blo 2185435 2186199 := bstep (se 1 (by rfl) ⟨1639649, by rfl⟩ : syracuseStep 2186199 = 3279299) B3279299
theorem B5533829 : Blo 2185435 5533829 := bbase (se 4 (by rfl) ⟨518796, by rfl⟩ : syracuseStep 5533829 = 1037593) (by norm_num)
theorem B3689219 : Blo 2185435 3689219 := bstep (se 1 (by rfl) ⟨2766914, by rfl⟩ : syracuseStep 3689219 = 5533829) B5533829
theorem B2459479 : Blo 2185435 2459479 := bstep (se 1 (by rfl) ⟨1844609, by rfl⟩ : syracuseStep 2459479 = 3689219) B3689219
theorem B3279305 : Blo 2185435 3279305 := bstep (se 2 (by rfl) ⟨1229739, by rfl⟩ : syracuseStep 3279305 = 2459479) B2459479
theorem B2186203 : Blo 2185435 2186203 := bstep (se 1 (by rfl) ⟨1639652, by rfl⟩ : syracuseStep 2186203 = 3279305) B3279305
theorem B5909429 : Blo 2185435 5909429 := bbase (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) (by norm_num)
theorem B3939619 : Blo 2185435 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B5252825 : Blo 2185435 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B3501883 : Blo 2185435 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B4669177 : Blo 2185435 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B6225569 : Blo 2185435 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B4150379 : Blo 2185435 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B11067677 : Blo 2185435 11067677 := bstep (se 3 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 11067677 = 4150379) B4150379
theorem B7378451 : Blo 2185435 7378451 := bstep (se 1 (by rfl) ⟨5533838, by rfl⟩ : syracuseStep 7378451 = 11067677) B11067677
theorem B4918967 : Blo 2185435 4918967 := bstep (se 1 (by rfl) ⟨3689225, by rfl⟩ : syracuseStep 4918967 = 7378451) B7378451
theorem B3279311 : Blo 2185435 3279311 := bstep (se 1 (by rfl) ⟨2459483, by rfl⟩ : syracuseStep 3279311 = 4918967) B4918967
theorem B2186207 : Blo 2185435 2186207 := bstep (se 1 (by rfl) ⟨1639655, by rfl⟩ : syracuseStep 2186207 = 3279311) B3279311
theorem B3279317 : Blo 2185435 3279317 := bbase (se 7 (by rfl) ⟨38429, by rfl⟩ : syracuseStep 3279317 = 76859) (by norm_num)
theorem B2186211 : Blo 2185435 2186211 := bstep (se 1 (by rfl) ⟨1639658, by rfl⟩ : syracuseStep 2186211 = 3279317) B3279317
theorem B8300789 : Blo 2185435 8300789 := bbase (se 5 (by rfl) ⟨389099, by rfl⟩ : syracuseStep 8300789 = 778199) (by norm_num)
theorem B5533859 : Blo 2185435 5533859 := bstep (se 1 (by rfl) ⟨4150394, by rfl⟩ : syracuseStep 5533859 = 8300789) B8300789
theorem B3689239 : Blo 2185435 3689239 := bstep (se 1 (by rfl) ⟨2766929, by rfl⟩ : syracuseStep 3689239 = 5533859) B5533859
theorem B4918985 : Blo 2185435 4918985 := bstep (se 2 (by rfl) ⟨1844619, by rfl⟩ : syracuseStep 4918985 = 3689239) B3689239
theorem B3279323 : Blo 2185435 3279323 := bstep (se 1 (by rfl) ⟨2459492, by rfl⟩ : syracuseStep 3279323 = 4918985) B4918985
theorem B2186215 : Blo 2185435 2186215 := bstep (se 1 (by rfl) ⟨1639661, by rfl⟩ : syracuseStep 2186215 = 3279323) B3279323
theorem B2459497 : Blo 2185435 2459497 := bbase (se 2 (by rfl) ⟨922311, by rfl⟩ : syracuseStep 2459497 = 1844623) (by norm_num)
theorem B3279329 : Blo 2185435 3279329 := bstep (se 2 (by rfl) ⟨1229748, by rfl⟩ : syracuseStep 3279329 = 2459497) B2459497
theorem B2186219 : Blo 2185435 2186219 := bstep (se 1 (by rfl) ⟨1639664, by rfl⟩ : syracuseStep 2186219 = 3279329) B3279329
theorem B2398745 : Blo 2185435 2398745 := bbase (se 2 (by rfl) ⟨899529, by rfl⟩ : syracuseStep 2398745 = 1799059) (by norm_num)
theorem B6396653 : Blo 2185435 6396653 := bstep (se 3 (by rfl) ⟨1199372, by rfl⟩ : syracuseStep 6396653 = 2398745) B2398745
theorem B4264435 : Blo 2185435 4264435 := bstep (se 1 (by rfl) ⟨3198326, by rfl⟩ : syracuseStep 4264435 = 6396653) B6396653
theorem B5685913 : Blo 2185435 5685913 := bstep (se 2 (by rfl) ⟨2132217, by rfl⟩ : syracuseStep 5685913 = 4264435) B4264435
theorem B7581217 : Blo 2185435 7581217 := bstep (se 2 (by rfl) ⟨2842956, by rfl⟩ : syracuseStep 7581217 = 5685913) B5685913
theorem B10108289 : Blo 2185435 10108289 := bstep (se 2 (by rfl) ⟨3790608, by rfl⟩ : syracuseStep 10108289 = 7581217) B7581217
theorem B6738859 : Blo 2185435 6738859 := bstep (se 1 (by rfl) ⟨5054144, by rfl⟩ : syracuseStep 6738859 = 10108289) B10108289
theorem B35940581 : Blo 2185435 35940581 := bstep (se 4 (by rfl) ⟨3369429, by rfl⟩ : syracuseStep 35940581 = 6738859) B6738859
theorem B23960387 : Blo 2185435 23960387 := bstep (se 1 (by rfl) ⟨17970290, by rfl⟩ : syracuseStep 23960387 = 35940581) B35940581
theorem B63894365 : Blo 2185435 63894365 := bstep (se 3 (by rfl) ⟨11980193, by rfl⟩ : syracuseStep 63894365 = 23960387) B23960387
theorem B42596243 : Blo 2185435 42596243 := bstep (se 1 (by rfl) ⟨31947182, by rfl⟩ : syracuseStep 42596243 = 63894365) B63894365
theorem B28397495 : Blo 2185435 28397495 := bstep (se 1 (by rfl) ⟨21298121, by rfl⟩ : syracuseStep 28397495 = 42596243) B42596243
theorem B18931663 : Blo 2185435 18931663 := bstep (se 1 (by rfl) ⟨14198747, by rfl⟩ : syracuseStep 18931663 = 28397495) B28397495
theorem B100968869 : Blo 2185435 100968869 := bstep (se 4 (by rfl) ⟨9465831, by rfl⟩ : syracuseStep 100968869 = 18931663) B18931663
theorem B67312579 : Blo 2185435 67312579 := bstep (se 1 (by rfl) ⟨50484434, by rfl⟩ : syracuseStep 67312579 = 100968869) B100968869
theorem B89750105 : Blo 2185435 89750105 := bstep (se 2 (by rfl) ⟨33656289, by rfl⟩ : syracuseStep 89750105 = 67312579) B67312579
theorem B59833403 : Blo 2185435 59833403 := bstep (se 1 (by rfl) ⟨44875052, by rfl⟩ : syracuseStep 59833403 = 89750105) B89750105
theorem B39888935 : Blo 2185435 39888935 := bstep (se 1 (by rfl) ⟨29916701, by rfl⟩ : syracuseStep 39888935 = 59833403) B59833403
theorem B26592623 : Blo 2185435 26592623 := bstep (se 1 (by rfl) ⟨19944467, by rfl⟩ : syracuseStep 26592623 = 39888935) B39888935
theorem B17728415 : Blo 2185435 17728415 := bstep (se 1 (by rfl) ⟨13296311, by rfl⟩ : syracuseStep 17728415 = 26592623) B26592623
theorem B11818943 : Blo 2185435 11818943 := bstep (se 1 (by rfl) ⟨8864207, by rfl⟩ : syracuseStep 11818943 = 17728415) B17728415
theorem B7879295 : Blo 2185435 7879295 := bstep (se 1 (by rfl) ⟨5909471, by rfl⟩ : syracuseStep 7879295 = 11818943) B11818943
theorem B5252863 : Blo 2185435 5252863 := bstep (se 1 (by rfl) ⟨3939647, by rfl⟩ : syracuseStep 5252863 = 7879295) B7879295
theorem B7003817 : Blo 2185435 7003817 := bstep (se 2 (by rfl) ⟨2626431, by rfl⟩ : syracuseStep 7003817 = 5252863) B5252863
theorem B4669211 : Blo 2185435 4669211 := bstep (se 1 (by rfl) ⟨3501908, by rfl⟩ : syracuseStep 4669211 = 7003817) B7003817
theorem B12451229 : Blo 2185435 12451229 := bstep (se 3 (by rfl) ⟨2334605, by rfl⟩ : syracuseStep 12451229 = 4669211) B4669211
theorem B8300819 : Blo 2185435 8300819 := bstep (se 1 (by rfl) ⟨6225614, by rfl⟩ : syracuseStep 8300819 = 12451229) B12451229
theorem B5533879 : Blo 2185435 5533879 := bstep (se 1 (by rfl) ⟨4150409, by rfl⟩ : syracuseStep 5533879 = 8300819) B8300819
theorem B7378505 : Blo 2185435 7378505 := bstep (se 2 (by rfl) ⟨2766939, by rfl⟩ : syracuseStep 7378505 = 5533879) B5533879
theorem B4919003 : Blo 2185435 4919003 := bstep (se 1 (by rfl) ⟨3689252, by rfl⟩ : syracuseStep 4919003 = 7378505) B7378505
theorem B3279335 : Blo 2185435 3279335 := bstep (se 1 (by rfl) ⟨2459501, by rfl⟩ : syracuseStep 3279335 = 4919003) B4919003
theorem B2186223 : Blo 2185435 2186223 := bstep (se 1 (by rfl) ⟨1639667, by rfl⟩ : syracuseStep 2186223 = 3279335) B3279335
theorem B3279341 : Blo 2185435 3279341 := bbase (se 3 (by rfl) ⟨614876, by rfl⟩ : syracuseStep 3279341 = 1229753) (by norm_num)
theorem B2186227 : Blo 2185435 2186227 := bstep (se 1 (by rfl) ⟨1639670, by rfl⟩ : syracuseStep 2186227 = 3279341) B3279341
theorem B4919021 : Blo 2185435 4919021 := bbase (se 3 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 4919021 = 1844633) (by norm_num)
theorem B3279347 : Blo 2185435 3279347 := bstep (se 1 (by rfl) ⟨2459510, by rfl⟩ : syracuseStep 3279347 = 4919021) B4919021
theorem B2186231 : Blo 2185435 2186231 := bstep (se 1 (by rfl) ⟨1639673, by rfl⟩ : syracuseStep 2186231 = 3279347) B3279347
theorem B8864261 : Blo 2185435 8864261 := bbase (se 4 (by rfl) ⟨831024, by rfl⟩ : syracuseStep 8864261 = 1662049) (by norm_num)
theorem B5909507 : Blo 2185435 5909507 := bstep (se 1 (by rfl) ⟨4432130, by rfl⟩ : syracuseStep 5909507 = 8864261) B8864261
theorem B3939671 : Blo 2185435 3939671 := bstep (se 1 (by rfl) ⟨2954753, by rfl⟩ : syracuseStep 3939671 = 5909507) B5909507
theorem B2626447 : Blo 2185435 2626447 := bstep (se 1 (by rfl) ⟨1969835, by rfl⟩ : syracuseStep 2626447 = 3939671) B3939671
theorem B3501929 : Blo 2185435 3501929 := bstep (se 2 (by rfl) ⟨1313223, by rfl⟩ : syracuseStep 3501929 = 2626447) B2626447
theorem B2334619 : Blo 2185435 2334619 := bstep (se 1 (by rfl) ⟨1750964, by rfl⟩ : syracuseStep 2334619 = 3501929) B3501929
theorem B3112825 : Blo 2185435 3112825 := bstep (se 2 (by rfl) ⟨1167309, by rfl⟩ : syracuseStep 3112825 = 2334619) B2334619
theorem B4150433 : Blo 2185435 4150433 := bstep (se 2 (by rfl) ⟨1556412, by rfl⟩ : syracuseStep 4150433 = 3112825) B3112825
theorem B2766955 : Blo 2185435 2766955 := bstep (se 1 (by rfl) ⟨2075216, by rfl⟩ : syracuseStep 2766955 = 4150433) B4150433
theorem B3689273 : Blo 2185435 3689273 := bstep (se 2 (by rfl) ⟨1383477, by rfl⟩ : syracuseStep 3689273 = 2766955) B2766955
theorem B2459515 : Blo 2185435 2459515 := bstep (se 1 (by rfl) ⟨1844636, by rfl⟩ : syracuseStep 2459515 = 3689273) B3689273
theorem B3279353 : Blo 2185435 3279353 := bstep (se 2 (by rfl) ⟨1229757, by rfl⟩ : syracuseStep 3279353 = 2459515) B2459515
theorem B2186235 : Blo 2185435 2186235 := bstep (se 1 (by rfl) ⟨1639676, by rfl⟩ : syracuseStep 2186235 = 3279353) B3279353
theorem B2220701 : Blo 2185435 2220701 := bbase (se 3 (by rfl) ⟨416381, by rfl⟩ : syracuseStep 2220701 = 832763) (by norm_num)
theorem B5921869 : Blo 2185435 5921869 := bstep (se 3 (by rfl) ⟨1110350, by rfl⟩ : syracuseStep 5921869 = 2220701) B2220701
theorem B7895825 : Blo 2185435 7895825 := bstep (se 2 (by rfl) ⟨2960934, by rfl⟩ : syracuseStep 7895825 = 5921869) B5921869
theorem B5263883 : Blo 2185435 5263883 := bstep (se 1 (by rfl) ⟨3947912, by rfl⟩ : syracuseStep 5263883 = 7895825) B7895825
theorem B3509255 : Blo 2185435 3509255 := bstep (se 1 (by rfl) ⟨2631941, by rfl⟩ : syracuseStep 3509255 = 5263883) B5263883
theorem B2339503 : Blo 2185435 2339503 := bstep (se 1 (by rfl) ⟨1754627, by rfl⟩ : syracuseStep 2339503 = 3509255) B3509255
theorem B12477349 : Blo 2185435 12477349 := bstep (se 4 (by rfl) ⟨1169751, by rfl⟩ : syracuseStep 12477349 = 2339503) B2339503
theorem B16636465 : Blo 2185435 16636465 := bstep (se 2 (by rfl) ⟨6238674, by rfl⟩ : syracuseStep 16636465 = 12477349) B12477349
theorem B22181953 : Blo 2185435 22181953 := bstep (se 2 (by rfl) ⟨8318232, by rfl⟩ : syracuseStep 22181953 = 16636465) B16636465
theorem B29575937 : Blo 2185435 29575937 := bstep (se 2 (by rfl) ⟨11090976, by rfl⟩ : syracuseStep 29575937 = 22181953) B22181953
theorem B78869165 : Blo 2185435 78869165 := bstep (se 3 (by rfl) ⟨14787968, by rfl⟩ : syracuseStep 78869165 = 29575937) B29575937
theorem B841271093 : Blo 2185435 841271093 := bstep (se 5 (by rfl) ⟨39434582, by rfl⟩ : syracuseStep 841271093 = 78869165) B78869165
theorem B560847395 : Blo 2185435 560847395 := bstep (se 1 (by rfl) ⟨420635546, by rfl⟩ : syracuseStep 560847395 = 841271093) B841271093
theorem B373898263 : Blo 2185435 373898263 := bstep (se 1 (by rfl) ⟨280423697, by rfl⟩ : syracuseStep 373898263 = 560847395) B560847395
theorem B498531017 : Blo 2185435 498531017 := bstep (se 2 (by rfl) ⟨186949131, by rfl⟩ : syracuseStep 498531017 = 373898263) B373898263
theorem B332354011 : Blo 2185435 332354011 := bstep (se 1 (by rfl) ⟨249265508, by rfl⟩ : syracuseStep 332354011 = 498531017) B498531017
theorem B443138681 : Blo 2185435 443138681 := bstep (se 2 (by rfl) ⟨166177005, by rfl⟩ : syracuseStep 443138681 = 332354011) B332354011
theorem B295425787 : Blo 2185435 295425787 := bstep (se 1 (by rfl) ⟨221569340, by rfl⟩ : syracuseStep 295425787 = 443138681) B443138681
theorem B393901049 : Blo 2185435 393901049 := bstep (se 2 (by rfl) ⟨147712893, by rfl⟩ : syracuseStep 393901049 = 295425787) B295425787
theorem B262600699 : Blo 2185435 262600699 := bstep (se 1 (by rfl) ⟨196950524, by rfl⟩ : syracuseStep 262600699 = 393901049) B393901049
theorem B350134265 : Blo 2185435 350134265 := bstep (se 2 (by rfl) ⟨131300349, by rfl⟩ : syracuseStep 350134265 = 262600699) B262600699
theorem B233422843 : Blo 2185435 233422843 := bstep (se 1 (by rfl) ⟨175067132, by rfl⟩ : syracuseStep 233422843 = 350134265) B350134265
theorem B311230457 : Blo 2185435 311230457 := bstep (se 2 (by rfl) ⟨116711421, by rfl⟩ : syracuseStep 311230457 = 233422843) B233422843
theorem B207486971 : Blo 2185435 207486971 := bstep (se 1 (by rfl) ⟨155615228, by rfl⟩ : syracuseStep 207486971 = 311230457) B311230457
theorem B138324647 : Blo 2185435 138324647 := bstep (se 1 (by rfl) ⟨103743485, by rfl⟩ : syracuseStep 138324647 = 207486971) B207486971
theorem B92216431 : Blo 2185435 92216431 := bstep (se 1 (by rfl) ⟨69162323, by rfl⟩ : syracuseStep 92216431 = 138324647) B138324647
theorem B122955241 : Blo 2185435 122955241 := bstep (se 2 (by rfl) ⟨46108215, by rfl⟩ : syracuseStep 122955241 = 92216431) B92216431
theorem B163940321 : Blo 2185435 163940321 := bstep (se 2 (by rfl) ⟨61477620, by rfl⟩ : syracuseStep 163940321 = 122955241) B122955241
theorem B437174189 : Blo 2185435 437174189 := bstep (se 3 (by rfl) ⟨81970160, by rfl⟩ : syracuseStep 437174189 = 163940321) B163940321
theorem B291449459 : Blo 2185435 291449459 := bstep (se 1 (by rfl) ⟨218587094, by rfl⟩ : syracuseStep 291449459 = 437174189) B437174189
theorem B777198557 : Blo 2185435 777198557 := bstep (se 3 (by rfl) ⟨145724729, by rfl⟩ : syracuseStep 777198557 = 291449459) B291449459
theorem B518132371 : Blo 2185435 518132371 := bstep (se 1 (by rfl) ⟨388599278, by rfl⟩ : syracuseStep 518132371 = 777198557) B777198557
theorem B690843161 : Blo 2185435 690843161 := bstep (se 2 (by rfl) ⟨259066185, by rfl⟩ : syracuseStep 690843161 = 518132371) B518132371
theorem B460562107 : Blo 2185435 460562107 := bstep (se 1 (by rfl) ⟨345421580, by rfl⟩ : syracuseStep 460562107 = 690843161) B690843161
theorem B614082809 : Blo 2185435 614082809 := bstep (se 2 (by rfl) ⟨230281053, by rfl⟩ : syracuseStep 614082809 = 460562107) B460562107
theorem B409388539 : Blo 2185435 409388539 := bstep (se 1 (by rfl) ⟨307041404, by rfl⟩ : syracuseStep 409388539 = 614082809) B614082809
theorem B545851385 : Blo 2185435 545851385 := bstep (se 2 (by rfl) ⟨204694269, by rfl⟩ : syracuseStep 545851385 = 409388539) B409388539
theorem B363900923 : Blo 2185435 363900923 := bstep (se 1 (by rfl) ⟨272925692, by rfl⟩ : syracuseStep 363900923 = 545851385) B545851385
theorem B242600615 : Blo 2185435 242600615 := bstep (se 1 (by rfl) ⟨181950461, by rfl⟩ : syracuseStep 242600615 = 363900923) B363900923
theorem B161733743 : Blo 2185435 161733743 := bstep (se 1 (by rfl) ⟨121300307, by rfl⟩ : syracuseStep 161733743 = 242600615) B242600615
theorem B107822495 : Blo 2185435 107822495 := bstep (se 1 (by rfl) ⟨80866871, by rfl⟩ : syracuseStep 107822495 = 161733743) B161733743
theorem B71881663 : Blo 2185435 71881663 := bstep (se 1 (by rfl) ⟨53911247, by rfl⟩ : syracuseStep 71881663 = 107822495) B107822495
theorem B95842217 : Blo 2185435 95842217 := bstep (se 2 (by rfl) ⟨35940831, by rfl⟩ : syracuseStep 95842217 = 71881663) B71881663
theorem B255579245 : Blo 2185435 255579245 := bstep (se 3 (by rfl) ⟨47921108, by rfl⟩ : syracuseStep 255579245 = 95842217) B95842217
theorem B170386163 : Blo 2185435 170386163 := bstep (se 1 (by rfl) ⟨127789622, by rfl⟩ : syracuseStep 170386163 = 255579245) B255579245
theorem B113590775 : Blo 2185435 113590775 := bstep (se 1 (by rfl) ⟨85193081, by rfl⟩ : syracuseStep 113590775 = 170386163) B170386163
theorem B75727183 : Blo 2185435 75727183 := bstep (se 1 (by rfl) ⟨56795387, by rfl⟩ : syracuseStep 75727183 = 113590775) B113590775
theorem B100969577 : Blo 2185435 100969577 := bstep (se 2 (by rfl) ⟨37863591, by rfl⟩ : syracuseStep 100969577 = 75727183) B75727183
theorem B67313051 : Blo 2185435 67313051 := bstep (se 1 (by rfl) ⟨50484788, by rfl⟩ : syracuseStep 67313051 = 100969577) B100969577
theorem B44875367 : Blo 2185435 44875367 := bstep (se 1 (by rfl) ⟨33656525, by rfl⟩ : syracuseStep 44875367 = 67313051) B67313051
theorem B29916911 : Blo 2185435 29916911 := bstep (se 1 (by rfl) ⟨22437683, by rfl⟩ : syracuseStep 29916911 = 44875367) B44875367
theorem B79778429 : Blo 2185435 79778429 := bstep (se 3 (by rfl) ⟨14958455, by rfl⟩ : syracuseStep 79778429 = 29916911) B29916911
theorem B53185619 : Blo 2185435 53185619 := bstep (se 1 (by rfl) ⟨39889214, by rfl⟩ : syracuseStep 53185619 = 79778429) B79778429
theorem B141828317 : Blo 2185435 141828317 := bstep (se 3 (by rfl) ⟨26592809, by rfl⟩ : syracuseStep 141828317 = 53185619) B53185619
theorem B94552211 : Blo 2185435 94552211 := bstep (se 1 (by rfl) ⟨70914158, by rfl⟩ : syracuseStep 94552211 = 141828317) B141828317
theorem B63034807 : Blo 2185435 63034807 := bstep (se 1 (by rfl) ⟨47276105, by rfl⟩ : syracuseStep 63034807 = 94552211) B94552211
theorem B84046409 : Blo 2185435 84046409 := bstep (se 2 (by rfl) ⟨31517403, by rfl⟩ : syracuseStep 84046409 = 63034807) B63034807
theorem B56030939 : Blo 2185435 56030939 := bstep (se 1 (by rfl) ⟨42023204, by rfl⟩ : syracuseStep 56030939 = 84046409) B84046409
theorem B37353959 : Blo 2185435 37353959 := bstep (se 1 (by rfl) ⟨28015469, by rfl⟩ : syracuseStep 37353959 = 56030939) B56030939
theorem B24902639 : Blo 2185435 24902639 := bstep (se 1 (by rfl) ⟨18676979, by rfl⟩ : syracuseStep 24902639 = 37353959) B37353959
theorem B16601759 : Blo 2185435 16601759 := bstep (se 1 (by rfl) ⟨12451319, by rfl⟩ : syracuseStep 16601759 = 24902639) B24902639
theorem B11067839 : Blo 2185435 11067839 := bstep (se 1 (by rfl) ⟨8300879, by rfl⟩ : syracuseStep 11067839 = 16601759) B16601759
theorem B7378559 : Blo 2185435 7378559 := bstep (se 1 (by rfl) ⟨5533919, by rfl⟩ : syracuseStep 7378559 = 11067839) B11067839
theorem B4919039 : Blo 2185435 4919039 := bstep (se 1 (by rfl) ⟨3689279, by rfl⟩ : syracuseStep 4919039 = 7378559) B7378559
theorem B3279359 : Blo 2185435 3279359 := bstep (se 1 (by rfl) ⟨2459519, by rfl⟩ : syracuseStep 3279359 = 4919039) B4919039
theorem B2186239 : Blo 2185435 2186239 := bstep (se 1 (by rfl) ⟨1639679, by rfl⟩ : syracuseStep 2186239 = 3279359) B3279359
theorem B3279365 : Blo 2185435 3279365 := bbase (se 4 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 3279365 = 614881) (by norm_num)
theorem B2186243 : Blo 2185435 2186243 := bstep (se 1 (by rfl) ⟨1639682, by rfl⟩ : syracuseStep 2186243 = 3279365) B3279365
theorem B3689293 : Blo 2185435 3689293 := bbase (se 3 (by rfl) ⟨691742, by rfl⟩ : syracuseStep 3689293 = 1383485) (by norm_num)
theorem B4919057 : Blo 2185435 4919057 := bstep (se 2 (by rfl) ⟨1844646, by rfl⟩ : syracuseStep 4919057 = 3689293) B3689293
theorem B3279371 : Blo 2185435 3279371 := bstep (se 1 (by rfl) ⟨2459528, by rfl⟩ : syracuseStep 3279371 = 4919057) B4919057
theorem B2186247 : Blo 2185435 2186247 := bstep (se 1 (by rfl) ⟨1639685, by rfl⟩ : syracuseStep 2186247 = 3279371) B3279371
theorem B2459533 : Blo 2185435 2459533 := bbase (se 3 (by rfl) ⟨461162, by rfl⟩ : syracuseStep 2459533 = 922325) (by norm_num)
theorem B3279377 : Blo 2185435 3279377 := bstep (se 2 (by rfl) ⟨1229766, by rfl⟩ : syracuseStep 3279377 = 2459533) B2459533
theorem B2186251 : Blo 2185435 2186251 := bstep (se 1 (by rfl) ⟨1639688, by rfl⟩ : syracuseStep 2186251 = 3279377) B3279377
theorem B7378613 : Blo 2185435 7378613 := bbase (se 5 (by rfl) ⟨345872, by rfl⟩ : syracuseStep 7378613 = 691745) (by norm_num)
theorem B4919075 : Blo 2185435 4919075 := bstep (se 1 (by rfl) ⟨3689306, by rfl⟩ : syracuseStep 4919075 = 7378613) B7378613
theorem B3279383 : Blo 2185435 3279383 := bstep (se 1 (by rfl) ⟨2459537, by rfl⟩ : syracuseStep 3279383 = 4919075) B4919075
theorem B2186255 : Blo 2185435 2186255 := bstep (se 1 (by rfl) ⟨1639691, by rfl⟩ : syracuseStep 2186255 = 3279383) B3279383
theorem B3279389 : Blo 2185435 3279389 := bbase (se 3 (by rfl) ⟨614885, by rfl⟩ : syracuseStep 3279389 = 1229771) (by norm_num)
theorem B2186259 : Blo 2185435 2186259 := bstep (se 1 (by rfl) ⟨1639694, by rfl⟩ : syracuseStep 2186259 = 3279389) B3279389
theorem B4919093 : Blo 2185435 4919093 := bbase (se 5 (by rfl) ⟨230582, by rfl⟩ : syracuseStep 4919093 = 461165) (by norm_num)
theorem B3279395 : Blo 2185435 3279395 := bstep (se 1 (by rfl) ⟨2459546, by rfl⟩ : syracuseStep 3279395 = 4919093) B4919093
theorem B2186263 : Blo 2185435 2186263 := bstep (se 1 (by rfl) ⟨1639697, by rfl⟩ : syracuseStep 2186263 = 3279395) B3279395
theorem B2493109 : Blo 2185435 2493109 := bbase (se 5 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 2493109 = 233729) (by norm_num)
theorem B13296581 : Blo 2185435 13296581 := bstep (se 4 (by rfl) ⟨1246554, by rfl⟩ : syracuseStep 13296581 = 2493109) B2493109
theorem B8864387 : Blo 2185435 8864387 := bstep (se 1 (by rfl) ⟨6648290, by rfl⟩ : syracuseStep 8864387 = 13296581) B13296581
theorem B5909591 : Blo 2185435 5909591 := bstep (se 1 (by rfl) ⟨4432193, by rfl⟩ : syracuseStep 5909591 = 8864387) B8864387
theorem B3939727 : Blo 2185435 3939727 := bstep (se 1 (by rfl) ⟨2954795, by rfl⟩ : syracuseStep 3939727 = 5909591) B5909591
theorem B5252969 : Blo 2185435 5252969 := bstep (se 2 (by rfl) ⟨1969863, by rfl⟩ : syracuseStep 5252969 = 3939727) B3939727
theorem B14007917 : Blo 2185435 14007917 := bstep (se 3 (by rfl) ⟨2626484, by rfl⟩ : syracuseStep 14007917 = 5252969) B5252969
theorem B9338611 : Blo 2185435 9338611 := bstep (se 1 (by rfl) ⟨7003958, by rfl⟩ : syracuseStep 9338611 = 14007917) B14007917
theorem B12451481 : Blo 2185435 12451481 := bstep (se 2 (by rfl) ⟨4669305, by rfl⟩ : syracuseStep 12451481 = 9338611) B9338611
theorem B8300987 : Blo 2185435 8300987 := bstep (se 1 (by rfl) ⟨6225740, by rfl⟩ : syracuseStep 8300987 = 12451481) B12451481
theorem B5533991 : Blo 2185435 5533991 := bstep (se 1 (by rfl) ⟨4150493, by rfl⟩ : syracuseStep 5533991 = 8300987) B8300987
theorem B3689327 : Blo 2185435 3689327 := bstep (se 1 (by rfl) ⟨2766995, by rfl⟩ : syracuseStep 3689327 = 5533991) B5533991
theorem B2459551 : Blo 2185435 2459551 := bstep (se 1 (by rfl) ⟨1844663, by rfl⟩ : syracuseStep 2459551 = 3689327) B3689327
theorem B3279401 : Blo 2185435 3279401 := bstep (se 2 (by rfl) ⟨1229775, by rfl⟩ : syracuseStep 3279401 = 2459551) B2459551
theorem B2186267 : Blo 2185435 2186267 := bstep (se 1 (by rfl) ⟨1639700, by rfl⟩ : syracuseStep 2186267 = 3279401) B3279401
theorem B2626489 : Blo 2185435 2626489 := bbase (se 2 (by rfl) ⟨984933, by rfl⟩ : syracuseStep 2626489 = 1969867) (by norm_num)
theorem B14007941 : Blo 2185435 14007941 := bstep (se 4 (by rfl) ⟨1313244, by rfl⟩ : syracuseStep 14007941 = 2626489) B2626489
theorem B9338627 : Blo 2185435 9338627 := bstep (se 1 (by rfl) ⟨7003970, by rfl⟩ : syracuseStep 9338627 = 14007941) B14007941
theorem B6225751 : Blo 2185435 6225751 := bstep (se 1 (by rfl) ⟨4669313, by rfl⟩ : syracuseStep 6225751 = 9338627) B9338627
theorem B8301001 : Blo 2185435 8301001 := bstep (se 2 (by rfl) ⟨3112875, by rfl⟩ : syracuseStep 8301001 = 6225751) B6225751
theorem B11068001 : Blo 2185435 11068001 := bstep (se 2 (by rfl) ⟨4150500, by rfl⟩ : syracuseStep 11068001 = 8301001) B8301001
theorem B7378667 : Blo 2185435 7378667 := bstep (se 1 (by rfl) ⟨5534000, by rfl⟩ : syracuseStep 7378667 = 11068001) B11068001
theorem B4919111 : Blo 2185435 4919111 := bstep (se 1 (by rfl) ⟨3689333, by rfl⟩ : syracuseStep 4919111 = 7378667) B7378667
theorem B3279407 : Blo 2185435 3279407 := bstep (se 1 (by rfl) ⟨2459555, by rfl⟩ : syracuseStep 3279407 = 4919111) B4919111
theorem B2186271 : Blo 2185435 2186271 := bstep (se 1 (by rfl) ⟨1639703, by rfl⟩ : syracuseStep 2186271 = 3279407) B3279407
theorem B3279413 : Blo 2185435 3279413 := bbase (se 5 (by rfl) ⟨153722, by rfl⟩ : syracuseStep 3279413 = 307445) (by norm_num)
theorem B2186275 : Blo 2185435 2186275 := bstep (se 1 (by rfl) ⟨1639706, by rfl⟩ : syracuseStep 2186275 = 3279413) B3279413
theorem B5534021 : Blo 2185435 5534021 := bbase (se 4 (by rfl) ⟨518814, by rfl⟩ : syracuseStep 5534021 = 1037629) (by norm_num)
theorem B3689347 : Blo 2185435 3689347 := bstep (se 1 (by rfl) ⟨2767010, by rfl⟩ : syracuseStep 3689347 = 5534021) B5534021
theorem B4919129 : Blo 2185435 4919129 := bstep (se 2 (by rfl) ⟨1844673, by rfl⟩ : syracuseStep 4919129 = 3689347) B3689347
theorem B3279419 : Blo 2185435 3279419 := bstep (se 1 (by rfl) ⟨2459564, by rfl⟩ : syracuseStep 3279419 = 4919129) B4919129
theorem B2186279 : Blo 2185435 2186279 := bstep (se 1 (by rfl) ⟨1639709, by rfl⟩ : syracuseStep 2186279 = 3279419) B3279419
theorem B2459569 : Blo 2185435 2459569 := bbase (se 2 (by rfl) ⟨922338, by rfl⟩ : syracuseStep 2459569 = 1844677) (by norm_num)
theorem B3279425 : Blo 2185435 3279425 := bstep (se 2 (by rfl) ⟨1229784, by rfl⟩ : syracuseStep 3279425 = 2459569) B2459569
theorem B2186283 : Blo 2185435 2186283 := bstep (se 1 (by rfl) ⟨1639712, by rfl⟩ : syracuseStep 2186283 = 3279425) B3279425
theorem B6225797 : Blo 2185435 6225797 := bbase (se 4 (by rfl) ⟨583668, by rfl⟩ : syracuseStep 6225797 = 1167337) (by norm_num)
theorem B4150531 : Blo 2185435 4150531 := bstep (se 1 (by rfl) ⟨3112898, by rfl⟩ : syracuseStep 4150531 = 6225797) B6225797
theorem B5534041 : Blo 2185435 5534041 := bstep (se 2 (by rfl) ⟨2075265, by rfl⟩ : syracuseStep 5534041 = 4150531) B4150531
theorem B7378721 : Blo 2185435 7378721 := bstep (se 2 (by rfl) ⟨2767020, by rfl⟩ : syracuseStep 7378721 = 5534041) B5534041
theorem B4919147 : Blo 2185435 4919147 := bstep (se 1 (by rfl) ⟨3689360, by rfl⟩ : syracuseStep 4919147 = 7378721) B7378721
theorem B3279431 : Blo 2185435 3279431 := bstep (se 1 (by rfl) ⟨2459573, by rfl⟩ : syracuseStep 3279431 = 4919147) B4919147
theorem B2186287 : Blo 2185435 2186287 := bstep (se 1 (by rfl) ⟨1639715, by rfl⟩ : syracuseStep 2186287 = 3279431) B3279431
theorem B3279437 : Blo 2185435 3279437 := bbase (se 3 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 3279437 = 1229789) (by norm_num)
theorem B2186291 : Blo 2185435 2186291 := bstep (se 1 (by rfl) ⟨1639718, by rfl⟩ : syracuseStep 2186291 = 3279437) B3279437
theorem B4919165 : Blo 2185435 4919165 := bbase (se 3 (by rfl) ⟨922343, by rfl⟩ : syracuseStep 4919165 = 1844687) (by norm_num)
theorem B3279443 : Blo 2185435 3279443 := bstep (se 1 (by rfl) ⟨2459582, by rfl⟩ : syracuseStep 3279443 = 4919165) B4919165
theorem B2186295 : Blo 2185435 2186295 := bstep (se 1 (by rfl) ⟨1639721, by rfl⟩ : syracuseStep 2186295 = 3279443) B3279443
theorem B3689381 : Blo 2185435 3689381 := bbase (se 4 (by rfl) ⟨345879, by rfl⟩ : syracuseStep 3689381 = 691759) (by norm_num)
theorem B2459587 : Blo 2185435 2459587 := bstep (se 1 (by rfl) ⟨1844690, by rfl⟩ : syracuseStep 2459587 = 3689381) B3689381
theorem B3279449 : Blo 2185435 3279449 := bstep (se 2 (by rfl) ⟨1229793, by rfl⟩ : syracuseStep 3279449 = 2459587) B2459587
theorem B2186299 : Blo 2185435 2186299 := bstep (se 1 (by rfl) ⟨1639724, by rfl⟩ : syracuseStep 2186299 = 3279449) B3279449
theorem B3502037 : Blo 2185435 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B2334691 : Blo 2185435 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B3112921 : Blo 2185435 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B16602245 : Blo 2185435 16602245 := bstep (se 4 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 16602245 = 3112921) B3112921
theorem B11068163 : Blo 2185435 11068163 := bstep (se 1 (by rfl) ⟨8301122, by rfl⟩ : syracuseStep 11068163 = 16602245) B16602245
theorem B7378775 : Blo 2185435 7378775 := bstep (se 1 (by rfl) ⟨5534081, by rfl⟩ : syracuseStep 7378775 = 11068163) B11068163
theorem B4919183 : Blo 2185435 4919183 := bstep (se 1 (by rfl) ⟨3689387, by rfl⟩ : syracuseStep 4919183 = 7378775) B7378775
theorem B3279455 : Blo 2185435 3279455 := bstep (se 1 (by rfl) ⟨2459591, by rfl⟩ : syracuseStep 3279455 = 4919183) B4919183
theorem B2186303 : Blo 2185435 2186303 := bstep (se 1 (by rfl) ⟨1639727, by rfl⟩ : syracuseStep 2186303 = 3279455) B3279455
theorem B3279461 : Blo 2185435 3279461 := bbase (se 4 (by rfl) ⟨307449, by rfl⟩ : syracuseStep 3279461 = 614899) (by norm_num)
theorem B2186307 : Blo 2185435 2186307 := bstep (se 1 (by rfl) ⟨1639730, by rfl⟩ : syracuseStep 2186307 = 3279461) B3279461
theorem B3112933 : Blo 2185435 3112933 := bbase (se 4 (by rfl) ⟨291837, by rfl⟩ : syracuseStep 3112933 = 583675) (by norm_num)
theorem B4150577 : Blo 2185435 4150577 := bstep (se 2 (by rfl) ⟨1556466, by rfl⟩ : syracuseStep 4150577 = 3112933) B3112933
theorem B2767051 : Blo 2185435 2767051 := bstep (se 1 (by rfl) ⟨2075288, by rfl⟩ : syracuseStep 2767051 = 4150577) B4150577
theorem B3689401 : Blo 2185435 3689401 := bstep (se 2 (by rfl) ⟨1383525, by rfl⟩ : syracuseStep 3689401 = 2767051) B2767051
theorem B4919201 : Blo 2185435 4919201 := bstep (se 2 (by rfl) ⟨1844700, by rfl⟩ : syracuseStep 4919201 = 3689401) B3689401
theorem B3279467 : Blo 2185435 3279467 := bstep (se 1 (by rfl) ⟨2459600, by rfl⟩ : syracuseStep 3279467 = 4919201) B4919201
theorem B2186311 : Blo 2185435 2186311 := bstep (se 1 (by rfl) ⟨1639733, by rfl⟩ : syracuseStep 2186311 = 3279467) B3279467
theorem B2459605 : Blo 2185435 2459605 := bbase (se 7 (by rfl) ⟨28823, by rfl⟩ : syracuseStep 2459605 = 57647) (by norm_num)
theorem B3279473 : Blo 2185435 3279473 := bstep (se 2 (by rfl) ⟨1229802, by rfl⟩ : syracuseStep 3279473 = 2459605) B2459605
theorem B2186315 : Blo 2185435 2186315 := bstep (se 1 (by rfl) ⟨1639736, by rfl⟩ : syracuseStep 2186315 = 3279473) B3279473
theorem B2767061 : Blo 2185435 2767061 := bbase (se 7 (by rfl) ⟨32426, by rfl⟩ : syracuseStep 2767061 = 64853) (by norm_num)
theorem B7378829 : Blo 2185435 7378829 := bstep (se 3 (by rfl) ⟨1383530, by rfl⟩ : syracuseStep 7378829 = 2767061) B2767061
theorem B4919219 : Blo 2185435 4919219 := bstep (se 1 (by rfl) ⟨3689414, by rfl⟩ : syracuseStep 4919219 = 7378829) B7378829
theorem B3279479 : Blo 2185435 3279479 := bstep (se 1 (by rfl) ⟨2459609, by rfl⟩ : syracuseStep 3279479 = 4919219) B4919219
theorem B2186319 : Blo 2185435 2186319 := bstep (se 1 (by rfl) ⟨1639739, by rfl⟩ : syracuseStep 2186319 = 3279479) B3279479
theorem B3279485 : Blo 2185435 3279485 := bbase (se 3 (by rfl) ⟨614903, by rfl⟩ : syracuseStep 3279485 = 1229807) (by norm_num)
theorem B2186323 : Blo 2185435 2186323 := bstep (se 1 (by rfl) ⟨1639742, by rfl⟩ : syracuseStep 2186323 = 3279485) B3279485
theorem B4919237 : Blo 2185435 4919237 := bbase (se 4 (by rfl) ⟨461178, by rfl⟩ : syracuseStep 4919237 = 922357) (by norm_num)
theorem B3279491 : Blo 2185435 3279491 := bstep (se 1 (by rfl) ⟨2459618, by rfl⟩ : syracuseStep 3279491 = 4919237) B4919237
theorem B2186327 : Blo 2185435 2186327 := bstep (se 1 (by rfl) ⟨1639745, by rfl⟩ : syracuseStep 2186327 = 3279491) B3279491
theorem B9338885 : Blo 2185435 9338885 := bbase (se 4 (by rfl) ⟨875520, by rfl⟩ : syracuseStep 9338885 = 1751041) (by norm_num)
theorem B6225923 : Blo 2185435 6225923 := bstep (se 1 (by rfl) ⟨4669442, by rfl⟩ : syracuseStep 6225923 = 9338885) B9338885
theorem B4150615 : Blo 2185435 4150615 := bstep (se 1 (by rfl) ⟨3112961, by rfl⟩ : syracuseStep 4150615 = 6225923) B6225923
theorem B5534153 : Blo 2185435 5534153 := bstep (se 2 (by rfl) ⟨2075307, by rfl⟩ : syracuseStep 5534153 = 4150615) B4150615
theorem B3689435 : Blo 2185435 3689435 := bstep (se 1 (by rfl) ⟨2767076, by rfl⟩ : syracuseStep 3689435 = 5534153) B5534153
theorem B2459623 : Blo 2185435 2459623 := bstep (se 1 (by rfl) ⟨1844717, by rfl⟩ : syracuseStep 2459623 = 3689435) B3689435
theorem B3279497 : Blo 2185435 3279497 := bstep (se 2 (by rfl) ⟨1229811, by rfl⟩ : syracuseStep 3279497 = 2459623) B2459623
theorem B2186331 : Blo 2185435 2186331 := bstep (se 1 (by rfl) ⟨1639748, by rfl⟩ : syracuseStep 2186331 = 3279497) B3279497
theorem B11068325 : Blo 2185435 11068325 := bbase (se 4 (by rfl) ⟨1037655, by rfl⟩ : syracuseStep 11068325 = 2075311) (by norm_num)
theorem B7378883 : Blo 2185435 7378883 := bstep (se 1 (by rfl) ⟨5534162, by rfl⟩ : syracuseStep 7378883 = 11068325) B11068325
theorem B4919255 : Blo 2185435 4919255 := bstep (se 1 (by rfl) ⟨3689441, by rfl⟩ : syracuseStep 4919255 = 7378883) B7378883
theorem B3279503 : Blo 2185435 3279503 := bstep (se 1 (by rfl) ⟨2459627, by rfl⟩ : syracuseStep 3279503 = 4919255) B4919255
theorem B2186335 : Blo 2185435 2186335 := bstep (se 1 (by rfl) ⟨1639751, by rfl⟩ : syracuseStep 2186335 = 3279503) B3279503
theorem B3279509 : Blo 2185435 3279509 := bbase (se 6 (by rfl) ⟨76863, by rfl⟩ : syracuseStep 3279509 = 153727) (by norm_num)
theorem B2186339 : Blo 2185435 2186339 := bstep (se 1 (by rfl) ⟨1639754, by rfl⟩ : syracuseStep 2186339 = 3279509) B3279509
theorem B6310901 : Blo 2185435 6310901 := bbase (se 5 (by rfl) ⟨295823, by rfl⟩ : syracuseStep 6310901 = 591647) (by norm_num)
theorem B4207267 : Blo 2185435 4207267 := bstep (se 1 (by rfl) ⟨3155450, by rfl⟩ : syracuseStep 4207267 = 6310901) B6310901
theorem B22438757 : Blo 2185435 22438757 := bstep (se 4 (by rfl) ⟨2103633, by rfl⟩ : syracuseStep 22438757 = 4207267) B4207267
theorem B14959171 : Blo 2185435 14959171 := bstep (se 1 (by rfl) ⟨11219378, by rfl⟩ : syracuseStep 14959171 = 22438757) B22438757
theorem B19945561 : Blo 2185435 19945561 := bstep (se 2 (by rfl) ⟨7479585, by rfl⟩ : syracuseStep 19945561 = 14959171) B14959171
theorem B26594081 : Blo 2185435 26594081 := bstep (se 2 (by rfl) ⟨9972780, by rfl⟩ : syracuseStep 26594081 = 19945561) B19945561
theorem B17729387 : Blo 2185435 17729387 := bstep (se 1 (by rfl) ⟨13297040, by rfl⟩ : syracuseStep 17729387 = 26594081) B26594081
theorem B11819591 : Blo 2185435 11819591 := bstep (se 1 (by rfl) ⟨8864693, by rfl⟩ : syracuseStep 11819591 = 17729387) B17729387
theorem B7879727 : Blo 2185435 7879727 := bstep (se 1 (by rfl) ⟨5909795, by rfl⟩ : syracuseStep 7879727 = 11819591) B11819591
theorem B21012605 : Blo 2185435 21012605 := bstep (se 3 (by rfl) ⟨3939863, by rfl⟩ : syracuseStep 21012605 = 7879727) B7879727
theorem B14008403 : Blo 2185435 14008403 := bstep (se 1 (by rfl) ⟨10506302, by rfl⟩ : syracuseStep 14008403 = 21012605) B21012605
theorem B9338935 : Blo 2185435 9338935 := bstep (se 1 (by rfl) ⟨7004201, by rfl⟩ : syracuseStep 9338935 = 14008403) B14008403
theorem B12451913 : Blo 2185435 12451913 := bstep (se 2 (by rfl) ⟨4669467, by rfl⟩ : syracuseStep 12451913 = 9338935) B9338935
theorem B8301275 : Blo 2185435 8301275 := bstep (se 1 (by rfl) ⟨6225956, by rfl⟩ : syracuseStep 8301275 = 12451913) B12451913
theorem B5534183 : Blo 2185435 5534183 := bstep (se 1 (by rfl) ⟨4150637, by rfl⟩ : syracuseStep 5534183 = 8301275) B8301275
theorem B3689455 : Blo 2185435 3689455 := bstep (se 1 (by rfl) ⟨2767091, by rfl⟩ : syracuseStep 3689455 = 5534183) B5534183
theorem B4919273 : Blo 2185435 4919273 := bstep (se 2 (by rfl) ⟨1844727, by rfl⟩ : syracuseStep 4919273 = 3689455) B3689455
theorem B3279515 : Blo 2185435 3279515 := bstep (se 1 (by rfl) ⟨2459636, by rfl⟩ : syracuseStep 3279515 = 4919273) B4919273
theorem B2186343 : Blo 2185435 2186343 := bstep (se 1 (by rfl) ⟨1639757, by rfl⟩ : syracuseStep 2186343 = 3279515) B3279515
theorem B2459641 : Blo 2185435 2459641 := bbase (se 2 (by rfl) ⟨922365, by rfl⟩ : syracuseStep 2459641 = 1844731) (by norm_num)
theorem B3279521 : Blo 2185435 3279521 := bstep (se 2 (by rfl) ⟨1229820, by rfl⟩ : syracuseStep 3279521 = 2459641) B2459641
theorem B2186347 : Blo 2185435 2186347 := bstep (se 1 (by rfl) ⟨1639760, by rfl⟩ : syracuseStep 2186347 = 3279521) B3279521
theorem B10506341 : Blo 2185435 10506341 := bbase (se 4 (by rfl) ⟨984969, by rfl⟩ : syracuseStep 10506341 = 1969939) (by norm_num)
theorem B7004227 : Blo 2185435 7004227 := bstep (se 1 (by rfl) ⟨5253170, by rfl⟩ : syracuseStep 7004227 = 10506341) B10506341
theorem B9338969 : Blo 2185435 9338969 := bstep (se 2 (by rfl) ⟨3502113, by rfl⟩ : syracuseStep 9338969 = 7004227) B7004227
theorem B6225979 : Blo 2185435 6225979 := bstep (se 1 (by rfl) ⟨4669484, by rfl⟩ : syracuseStep 6225979 = 9338969) B9338969
theorem B8301305 : Blo 2185435 8301305 := bstep (se 2 (by rfl) ⟨3112989, by rfl⟩ : syracuseStep 8301305 = 6225979) B6225979
theorem B5534203 : Blo 2185435 5534203 := bstep (se 1 (by rfl) ⟨4150652, by rfl⟩ : syracuseStep 5534203 = 8301305) B8301305
theorem B7378937 : Blo 2185435 7378937 := bstep (se 2 (by rfl) ⟨2767101, by rfl⟩ : syracuseStep 7378937 = 5534203) B5534203
theorem B4919291 : Blo 2185435 4919291 := bstep (se 1 (by rfl) ⟨3689468, by rfl⟩ : syracuseStep 4919291 = 7378937) B7378937
theorem B3279527 : Blo 2185435 3279527 := bstep (se 1 (by rfl) ⟨2459645, by rfl⟩ : syracuseStep 3279527 = 4919291) B4919291
theorem B2186351 : Blo 2185435 2186351 := bstep (se 1 (by rfl) ⟨1639763, by rfl⟩ : syracuseStep 2186351 = 3279527) B3279527
theorem B3279533 : Blo 2185435 3279533 := bbase (se 3 (by rfl) ⟨614912, by rfl⟩ : syracuseStep 3279533 = 1229825) (by norm_num)
theorem B2186355 : Blo 2185435 2186355 := bstep (se 1 (by rfl) ⟨1639766, by rfl⟩ : syracuseStep 2186355 = 3279533) B3279533
theorem B4919309 : Blo 2185435 4919309 := bbase (se 3 (by rfl) ⟨922370, by rfl⟩ : syracuseStep 4919309 = 1844741) (by norm_num)
theorem B3279539 : Blo 2185435 3279539 := bstep (se 1 (by rfl) ⟨2459654, by rfl⟩ : syracuseStep 3279539 = 4919309) B4919309
theorem B2186359 : Blo 2185435 2186359 := bstep (se 1 (by rfl) ⟨1639769, by rfl⟩ : syracuseStep 2186359 = 3279539) B3279539
theorem B2767117 : Blo 2185435 2767117 := bbase (se 3 (by rfl) ⟨518834, by rfl⟩ : syracuseStep 2767117 = 1037669) (by norm_num)
theorem B3689489 : Blo 2185435 3689489 := bstep (se 2 (by rfl) ⟨1383558, by rfl⟩ : syracuseStep 3689489 = 2767117) B2767117
theorem B2459659 : Blo 2185435 2459659 := bstep (se 1 (by rfl) ⟨1844744, by rfl⟩ : syracuseStep 2459659 = 3689489) B3689489
theorem B3279545 : Blo 2185435 3279545 := bstep (se 2 (by rfl) ⟨1229829, by rfl⟩ : syracuseStep 3279545 = 2459659) B2459659
theorem B2186363 : Blo 2185435 2186363 := bstep (se 1 (by rfl) ⟨1639772, by rfl⟩ : syracuseStep 2186363 = 3279545) B3279545
theorem B3155485 : Blo 2185435 3155485 := bbase (se 3 (by rfl) ⟨591653, by rfl⟩ : syracuseStep 3155485 = 1183307) (by norm_num)
theorem B4207313 : Blo 2185435 4207313 := bstep (se 2 (by rfl) ⟨1577742, by rfl⟩ : syracuseStep 4207313 = 3155485) B3155485
theorem B2804875 : Blo 2185435 2804875 := bstep (se 1 (by rfl) ⟨2103656, by rfl⟩ : syracuseStep 2804875 = 4207313) B4207313
theorem B14959333 : Blo 2185435 14959333 := bstep (se 4 (by rfl) ⟨1402437, by rfl⟩ : syracuseStep 14959333 = 2804875) B2804875
theorem B19945777 : Blo 2185435 19945777 := bstep (se 2 (by rfl) ⟨7479666, by rfl⟩ : syracuseStep 19945777 = 14959333) B14959333
theorem B26594369 : Blo 2185435 26594369 := bstep (se 2 (by rfl) ⟨9972888, by rfl⟩ : syracuseStep 26594369 = 19945777) B19945777
theorem B17729579 : Blo 2185435 17729579 := bstep (se 1 (by rfl) ⟨13297184, by rfl⟩ : syracuseStep 17729579 = 26594369) B26594369
theorem B11819719 : Blo 2185435 11819719 := bstep (se 1 (by rfl) ⟨8864789, by rfl⟩ : syracuseStep 11819719 = 17729579) B17729579
theorem B15759625 : Blo 2185435 15759625 := bstep (se 2 (by rfl) ⟨5909859, by rfl⟩ : syracuseStep 15759625 = 11819719) B11819719
theorem B21012833 : Blo 2185435 21012833 := bstep (se 2 (by rfl) ⟨7879812, by rfl⟩ : syracuseStep 21012833 = 15759625) B15759625
theorem B14008555 : Blo 2185435 14008555 := bstep (se 1 (by rfl) ⟨10506416, by rfl⟩ : syracuseStep 14008555 = 21012833) B21012833
theorem B18678073 : Blo 2185435 18678073 := bstep (se 2 (by rfl) ⟨7004277, by rfl⟩ : syracuseStep 18678073 = 14008555) B14008555
theorem B24904097 : Blo 2185435 24904097 := bstep (se 2 (by rfl) ⟨9339036, by rfl⟩ : syracuseStep 24904097 = 18678073) B18678073
theorem B16602731 : Blo 2185435 16602731 := bstep (se 1 (by rfl) ⟨12452048, by rfl⟩ : syracuseStep 16602731 = 24904097) B24904097
theorem B11068487 : Blo 2185435 11068487 := bstep (se 1 (by rfl) ⟨8301365, by rfl⟩ : syracuseStep 11068487 = 16602731) B16602731
theorem B7378991 : Blo 2185435 7378991 := bstep (se 1 (by rfl) ⟨5534243, by rfl⟩ : syracuseStep 7378991 = 11068487) B11068487
theorem B4919327 : Blo 2185435 4919327 := bstep (se 1 (by rfl) ⟨3689495, by rfl⟩ : syracuseStep 4919327 = 7378991) B7378991
theorem B3279551 : Blo 2185435 3279551 := bstep (se 1 (by rfl) ⟨2459663, by rfl⟩ : syracuseStep 3279551 = 4919327) B4919327
theorem B2186367 : Blo 2185435 2186367 := bstep (se 1 (by rfl) ⟨1639775, by rfl⟩ : syracuseStep 2186367 = 3279551) B3279551
theorem B3279557 : Blo 2185435 3279557 := bbase (se 4 (by rfl) ⟨307458, by rfl⟩ : syracuseStep 3279557 = 614917) (by norm_num)
theorem B2186371 : Blo 2185435 2186371 := bstep (se 1 (by rfl) ⟨1639778, by rfl⟩ : syracuseStep 2186371 = 3279557) B3279557
theorem B3689509 : Blo 2185435 3689509 := bbase (se 4 (by rfl) ⟨345891, by rfl⟩ : syracuseStep 3689509 = 691783) (by norm_num)
theorem B4919345 : Blo 2185435 4919345 := bstep (se 2 (by rfl) ⟨1844754, by rfl⟩ : syracuseStep 4919345 = 3689509) B3689509
theorem B3279563 : Blo 2185435 3279563 := bstep (se 1 (by rfl) ⟨2459672, by rfl⟩ : syracuseStep 3279563 = 4919345) B4919345
theorem B2186375 : Blo 2185435 2186375 := bstep (se 1 (by rfl) ⟨1639781, by rfl⟩ : syracuseStep 2186375 = 3279563) B3279563
theorem B2459677 : Blo 2185435 2459677 := bbase (se 3 (by rfl) ⟨461189, by rfl⟩ : syracuseStep 2459677 = 922379) (by norm_num)
theorem B3279569 : Blo 2185435 3279569 := bstep (se 2 (by rfl) ⟨1229838, by rfl⟩ : syracuseStep 3279569 = 2459677) B2459677
theorem B2186379 : Blo 2185435 2186379 := bstep (se 1 (by rfl) ⟨1639784, by rfl⟩ : syracuseStep 2186379 = 3279569) B3279569
theorem B7379045 : Blo 2185435 7379045 := bbase (se 4 (by rfl) ⟨691785, by rfl⟩ : syracuseStep 7379045 = 1383571) (by norm_num)
theorem B4919363 : Blo 2185435 4919363 := bstep (se 1 (by rfl) ⟨3689522, by rfl⟩ : syracuseStep 4919363 = 7379045) B7379045
theorem B3279575 : Blo 2185435 3279575 := bstep (se 1 (by rfl) ⟨2459681, by rfl⟩ : syracuseStep 3279575 = 4919363) B4919363
theorem B2186383 : Blo 2185435 2186383 := bstep (se 1 (by rfl) ⟨1639787, by rfl⟩ : syracuseStep 2186383 = 3279575) B3279575
theorem B3279581 : Blo 2185435 3279581 := bbase (se 3 (by rfl) ⟨614921, by rfl⟩ : syracuseStep 3279581 = 1229843) (by norm_num)
theorem B2186387 : Blo 2185435 2186387 := bstep (se 1 (by rfl) ⟨1639790, by rfl⟩ : syracuseStep 2186387 = 3279581) B3279581
theorem B4919381 : Blo 2185435 4919381 := bbase (se 8 (by rfl) ⟨28824, by rfl⟩ : syracuseStep 4919381 = 57649) (by norm_num)
theorem B3279587 : Blo 2185435 3279587 := bstep (se 1 (by rfl) ⟨2459690, by rfl⟩ : syracuseStep 3279587 = 4919381) B4919381
theorem B2186391 : Blo 2185435 2186391 := bstep (se 1 (by rfl) ⟨1639793, by rfl⟩ : syracuseStep 2186391 = 3279587) B3279587
theorem B5253277 : Blo 2185435 5253277 := bbase (se 3 (by rfl) ⟨984989, by rfl⟩ : syracuseStep 5253277 = 1969979) (by norm_num)
theorem B7004369 : Blo 2185435 7004369 := bstep (se 2 (by rfl) ⟨2626638, by rfl⟩ : syracuseStep 7004369 = 5253277) B5253277
theorem B4669579 : Blo 2185435 4669579 := bstep (se 1 (by rfl) ⟨3502184, by rfl⟩ : syracuseStep 4669579 = 7004369) B7004369
theorem B6226105 : Blo 2185435 6226105 := bstep (se 2 (by rfl) ⟨2334789, by rfl⟩ : syracuseStep 6226105 = 4669579) B4669579
theorem B8301473 : Blo 2185435 8301473 := bstep (se 2 (by rfl) ⟨3113052, by rfl⟩ : syracuseStep 8301473 = 6226105) B6226105
theorem B5534315 : Blo 2185435 5534315 := bstep (se 1 (by rfl) ⟨4150736, by rfl⟩ : syracuseStep 5534315 = 8301473) B8301473
theorem B3689543 : Blo 2185435 3689543 := bstep (se 1 (by rfl) ⟨2767157, by rfl⟩ : syracuseStep 3689543 = 5534315) B5534315
theorem B2459695 : Blo 2185435 2459695 := bstep (se 1 (by rfl) ⟨1844771, by rfl⟩ : syracuseStep 2459695 = 3689543) B3689543
theorem B3279593 : Blo 2185435 3279593 := bstep (se 2 (by rfl) ⟨1229847, by rfl⟩ : syracuseStep 3279593 = 2459695) B2459695
theorem B2186395 : Blo 2185435 2186395 := bstep (se 1 (by rfl) ⟨1639796, by rfl⟩ : syracuseStep 2186395 = 3279593) B3279593
theorem B21013141 : Blo 2185435 21013141 := bbase (se 6 (by rfl) ⟨492495, by rfl⟩ : syracuseStep 21013141 = 984991) (by norm_num)
theorem B28017521 : Blo 2185435 28017521 := bstep (se 2 (by rfl) ⟨10506570, by rfl⟩ : syracuseStep 28017521 = 21013141) B21013141
theorem B18678347 : Blo 2185435 18678347 := bstep (se 1 (by rfl) ⟨14008760, by rfl⟩ : syracuseStep 18678347 = 28017521) B28017521
theorem B12452231 : Blo 2185435 12452231 := bstep (se 1 (by rfl) ⟨9339173, by rfl⟩ : syracuseStep 12452231 = 18678347) B18678347
theorem B8301487 : Blo 2185435 8301487 := bstep (se 1 (by rfl) ⟨6226115, by rfl⟩ : syracuseStep 8301487 = 12452231) B12452231
theorem B11068649 : Blo 2185435 11068649 := bstep (se 2 (by rfl) ⟨4150743, by rfl⟩ : syracuseStep 11068649 = 8301487) B8301487
theorem B7379099 : Blo 2185435 7379099 := bstep (se 1 (by rfl) ⟨5534324, by rfl⟩ : syracuseStep 7379099 = 11068649) B11068649
theorem B4919399 : Blo 2185435 4919399 := bstep (se 1 (by rfl) ⟨3689549, by rfl⟩ : syracuseStep 4919399 = 7379099) B7379099
theorem B3279599 : Blo 2185435 3279599 := bstep (se 1 (by rfl) ⟨2459699, by rfl⟩ : syracuseStep 3279599 = 4919399) B4919399
theorem B2186399 : Blo 2185435 2186399 := bstep (se 1 (by rfl) ⟨1639799, by rfl⟩ : syracuseStep 2186399 = 3279599) B3279599
theorem B3279605 : Blo 2185435 3279605 := bbase (se 5 (by rfl) ⟨153731, by rfl⟩ : syracuseStep 3279605 = 307463) (by norm_num)
theorem B2186403 : Blo 2185435 2186403 := bstep (se 1 (by rfl) ⟨1639802, by rfl⟩ : syracuseStep 2186403 = 3279605) B3279605
theorem B4432477 : Blo 2185435 4432477 := bbase (se 3 (by rfl) ⟨831089, by rfl⟩ : syracuseStep 4432477 = 1662179) (by norm_num)
theorem B5909969 : Blo 2185435 5909969 := bstep (se 2 (by rfl) ⟨2216238, by rfl⟩ : syracuseStep 5909969 = 4432477) B4432477
theorem B15759917 : Blo 2185435 15759917 := bstep (se 3 (by rfl) ⟨2954984, by rfl⟩ : syracuseStep 15759917 = 5909969) B5909969
theorem B10506611 : Blo 2185435 10506611 := bstep (se 1 (by rfl) ⟨7879958, by rfl⟩ : syracuseStep 10506611 = 15759917) B15759917
theorem B7004407 : Blo 2185435 7004407 := bstep (se 1 (by rfl) ⟨5253305, by rfl⟩ : syracuseStep 7004407 = 10506611) B10506611
theorem B9339209 : Blo 2185435 9339209 := bstep (se 2 (by rfl) ⟨3502203, by rfl⟩ : syracuseStep 9339209 = 7004407) B7004407
theorem B6226139 : Blo 2185435 6226139 := bstep (se 1 (by rfl) ⟨4669604, by rfl⟩ : syracuseStep 6226139 = 9339209) B9339209
theorem B4150759 : Blo 2185435 4150759 := bstep (se 1 (by rfl) ⟨3113069, by rfl⟩ : syracuseStep 4150759 = 6226139) B6226139
theorem B5534345 : Blo 2185435 5534345 := bstep (se 2 (by rfl) ⟨2075379, by rfl⟩ : syracuseStep 5534345 = 4150759) B4150759
theorem B3689563 : Blo 2185435 3689563 := bstep (se 1 (by rfl) ⟨2767172, by rfl⟩ : syracuseStep 3689563 = 5534345) B5534345
theorem B4919417 : Blo 2185435 4919417 := bstep (se 2 (by rfl) ⟨1844781, by rfl⟩ : syracuseStep 4919417 = 3689563) B3689563
theorem B3279611 : Blo 2185435 3279611 := bstep (se 1 (by rfl) ⟨2459708, by rfl⟩ : syracuseStep 3279611 = 4919417) B4919417
theorem B2186407 : Blo 2185435 2186407 := bstep (se 1 (by rfl) ⟨1639805, by rfl⟩ : syracuseStep 2186407 = 3279611) B3279611
theorem B2459713 : Blo 2185435 2459713 := bbase (se 2 (by rfl) ⟨922392, by rfl⟩ : syracuseStep 2459713 = 1844785) (by norm_num)
theorem B3279617 : Blo 2185435 3279617 := bstep (se 2 (by rfl) ⟨1229856, by rfl⟩ : syracuseStep 3279617 = 2459713) B2459713
theorem B2186411 : Blo 2185435 2186411 := bstep (se 1 (by rfl) ⟨1639808, by rfl⟩ : syracuseStep 2186411 = 3279617) B3279617
theorem B5534365 : Blo 2185435 5534365 := bbase (se 3 (by rfl) ⟨1037693, by rfl⟩ : syracuseStep 5534365 = 2075387) (by norm_num)
theorem B7379153 : Blo 2185435 7379153 := bstep (se 2 (by rfl) ⟨2767182, by rfl⟩ : syracuseStep 7379153 = 5534365) B5534365
theorem B4919435 : Blo 2185435 4919435 := bstep (se 1 (by rfl) ⟨3689576, by rfl⟩ : syracuseStep 4919435 = 7379153) B7379153
theorem B3279623 : Blo 2185435 3279623 := bstep (se 1 (by rfl) ⟨2459717, by rfl⟩ : syracuseStep 3279623 = 4919435) B4919435
theorem B2186415 : Blo 2185435 2186415 := bstep (se 1 (by rfl) ⟨1639811, by rfl⟩ : syracuseStep 2186415 = 3279623) B3279623
theorem B3279629 : Blo 2185435 3279629 := bbase (se 3 (by rfl) ⟨614930, by rfl⟩ : syracuseStep 3279629 = 1229861) (by norm_num)
theorem B2186419 : Blo 2185435 2186419 := bstep (se 1 (by rfl) ⟨1639814, by rfl⟩ : syracuseStep 2186419 = 3279629) B3279629
theorem B4919453 : Blo 2185435 4919453 := bbase (se 3 (by rfl) ⟨922397, by rfl⟩ : syracuseStep 4919453 = 1844795) (by norm_num)
theorem B3279635 : Blo 2185435 3279635 := bstep (se 1 (by rfl) ⟨2459726, by rfl⟩ : syracuseStep 3279635 = 4919453) B4919453
theorem B2186423 : Blo 2185435 2186423 := bstep (se 1 (by rfl) ⟨1639817, by rfl⟩ : syracuseStep 2186423 = 3279635) B3279635
theorem B3689597 : Blo 2185435 3689597 := bbase (se 3 (by rfl) ⟨691799, by rfl⟩ : syracuseStep 3689597 = 1383599) (by norm_num)
theorem B2459731 : Blo 2185435 2459731 := bstep (se 1 (by rfl) ⟨1844798, by rfl⟩ : syracuseStep 2459731 = 3689597) B3689597
theorem B3279641 : Blo 2185435 3279641 := bstep (se 2 (by rfl) ⟨1229865, by rfl⟩ : syracuseStep 3279641 = 2459731) B2459731
theorem B2186427 : Blo 2185435 2186427 := bstep (se 1 (by rfl) ⟨1639820, by rfl⟩ : syracuseStep 2186427 = 3279641) B3279641
theorem B10506725 : Blo 2185435 10506725 := bbase (se 4 (by rfl) ⟨985005, by rfl⟩ : syracuseStep 10506725 = 1970011) (by norm_num)
theorem B7004483 : Blo 2185435 7004483 := bstep (se 1 (by rfl) ⟨5253362, by rfl⟩ : syracuseStep 7004483 = 10506725) B10506725
theorem B4669655 : Blo 2185435 4669655 := bstep (se 1 (by rfl) ⟨3502241, by rfl⟩ : syracuseStep 4669655 = 7004483) B7004483
theorem B12452413 : Blo 2185435 12452413 := bstep (se 3 (by rfl) ⟨2334827, by rfl⟩ : syracuseStep 12452413 = 4669655) B4669655
theorem B16603217 : Blo 2185435 16603217 := bstep (se 2 (by rfl) ⟨6226206, by rfl⟩ : syracuseStep 16603217 = 12452413) B12452413
theorem B11068811 : Blo 2185435 11068811 := bstep (se 1 (by rfl) ⟨8301608, by rfl⟩ : syracuseStep 11068811 = 16603217) B16603217
theorem B7379207 : Blo 2185435 7379207 := bstep (se 1 (by rfl) ⟨5534405, by rfl⟩ : syracuseStep 7379207 = 11068811) B11068811
theorem B4919471 : Blo 2185435 4919471 := bstep (se 1 (by rfl) ⟨3689603, by rfl⟩ : syracuseStep 4919471 = 7379207) B7379207
theorem B3279647 : Blo 2185435 3279647 := bstep (se 1 (by rfl) ⟨2459735, by rfl⟩ : syracuseStep 3279647 = 4919471) B4919471
theorem B2186431 : Blo 2185435 2186431 := bstep (se 1 (by rfl) ⟨1639823, by rfl⟩ : syracuseStep 2186431 = 3279647) B3279647
theorem B3279653 : Blo 2185435 3279653 := bbase (se 4 (by rfl) ⟨307467, by rfl⟩ : syracuseStep 3279653 = 614935) (by norm_num)
theorem B2186435 : Blo 2185435 2186435 := bstep (se 1 (by rfl) ⟨1639826, by rfl⟩ : syracuseStep 2186435 = 3279653) B3279653
theorem B2767213 : Blo 2185435 2767213 := bbase (se 3 (by rfl) ⟨518852, by rfl⟩ : syracuseStep 2767213 = 1037705) (by norm_num)
theorem B3689617 : Blo 2185435 3689617 := bstep (se 2 (by rfl) ⟨1383606, by rfl⟩ : syracuseStep 3689617 = 2767213) B2767213
theorem B4919489 : Blo 2185435 4919489 := bstep (se 2 (by rfl) ⟨1844808, by rfl⟩ : syracuseStep 4919489 = 3689617) B3689617
theorem B3279659 : Blo 2185435 3279659 := bstep (se 1 (by rfl) ⟨2459744, by rfl⟩ : syracuseStep 3279659 = 4919489) B4919489
theorem B2186439 : Blo 2185435 2186439 := bstep (se 1 (by rfl) ⟨1639829, by rfl⟩ : syracuseStep 2186439 = 3279659) B3279659
theorem B2459749 : Blo 2185435 2459749 := bbase (se 4 (by rfl) ⟨230601, by rfl⟩ : syracuseStep 2459749 = 461203) (by norm_num)
theorem B3279665 : Blo 2185435 3279665 := bstep (se 2 (by rfl) ⟨1229874, by rfl⟩ : syracuseStep 3279665 = 2459749) B2459749
theorem B2186443 : Blo 2185435 2186443 := bstep (se 1 (by rfl) ⟨1639832, by rfl⟩ : syracuseStep 2186443 = 3279665) B3279665
theorem B2334845 : Blo 2185435 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B6226253 : Blo 2185435 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B4150835 : Blo 2185435 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B2767223 : Blo 2185435 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B7379261 : Blo 2185435 7379261 := bstep (se 3 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 7379261 = 2767223) B2767223
theorem B4919507 : Blo 2185435 4919507 := bstep (se 1 (by rfl) ⟨3689630, by rfl⟩ : syracuseStep 4919507 = 7379261) B7379261
theorem B3279671 : Blo 2185435 3279671 := bstep (se 1 (by rfl) ⟨2459753, by rfl⟩ : syracuseStep 3279671 = 4919507) B4919507
theorem B2186447 : Blo 2185435 2186447 := bstep (se 1 (by rfl) ⟨1639835, by rfl⟩ : syracuseStep 2186447 = 3279671) B3279671
theorem B3279677 : Blo 2185435 3279677 := bbase (se 3 (by rfl) ⟨614939, by rfl⟩ : syracuseStep 3279677 = 1229879) (by norm_num)
theorem B2186451 : Blo 2185435 2186451 := bstep (se 1 (by rfl) ⟨1639838, by rfl⟩ : syracuseStep 2186451 = 3279677) B3279677
theorem B4919525 : Blo 2185435 4919525 := bbase (se 4 (by rfl) ⟨461205, by rfl⟩ : syracuseStep 4919525 = 922411) (by norm_num)
theorem B3279683 : Blo 2185435 3279683 := bstep (se 1 (by rfl) ⟨2459762, by rfl⟩ : syracuseStep 3279683 = 4919525) B4919525
theorem B2186455 : Blo 2185435 2186455 := bstep (se 1 (by rfl) ⟨1639841, by rfl⟩ : syracuseStep 2186455 = 3279683) B3279683
theorem B5534477 : Blo 2185435 5534477 := bbase (se 3 (by rfl) ⟨1037714, by rfl⟩ : syracuseStep 5534477 = 2075429) (by norm_num)
theorem B3689651 : Blo 2185435 3689651 := bstep (se 1 (by rfl) ⟨2767238, by rfl⟩ : syracuseStep 3689651 = 5534477) B5534477
theorem B2459767 : Blo 2185435 2459767 := bstep (se 1 (by rfl) ⟨1844825, by rfl⟩ : syracuseStep 2459767 = 3689651) B3689651
theorem B3279689 : Blo 2185435 3279689 := bstep (se 2 (by rfl) ⟨1229883, by rfl⟩ : syracuseStep 3279689 = 2459767) B2459767
theorem B2186459 : Blo 2185435 2186459 := bstep (se 1 (by rfl) ⟨1639844, by rfl⟩ : syracuseStep 2186459 = 3279689) B3279689
theorem B3113149 : Blo 2185435 3113149 := bbase (se 3 (by rfl) ⟨583715, by rfl⟩ : syracuseStep 3113149 = 1167431) (by norm_num)
theorem B4150865 : Blo 2185435 4150865 := bstep (se 2 (by rfl) ⟨1556574, by rfl⟩ : syracuseStep 4150865 = 3113149) B3113149
theorem B11068973 : Blo 2185435 11068973 := bstep (se 3 (by rfl) ⟨2075432, by rfl⟩ : syracuseStep 11068973 = 4150865) B4150865
theorem B7379315 : Blo 2185435 7379315 := bstep (se 1 (by rfl) ⟨5534486, by rfl⟩ : syracuseStep 7379315 = 11068973) B11068973
theorem B4919543 : Blo 2185435 4919543 := bstep (se 1 (by rfl) ⟨3689657, by rfl⟩ : syracuseStep 4919543 = 7379315) B7379315
theorem B3279695 : Blo 2185435 3279695 := bstep (se 1 (by rfl) ⟨2459771, by rfl⟩ : syracuseStep 3279695 = 4919543) B4919543
theorem B2186463 : Blo 2185435 2186463 := bstep (se 1 (by rfl) ⟨1639847, by rfl⟩ : syracuseStep 2186463 = 3279695) B3279695
theorem B3279701 : Blo 2185435 3279701 := bbase (se 9 (by rfl) ⟨9608, by rfl⟩ : syracuseStep 3279701 = 19217) (by norm_num)
theorem B2186467 : Blo 2185435 2186467 := bstep (se 1 (by rfl) ⟨1639850, by rfl⟩ : syracuseStep 2186467 = 3279701) B3279701
theorem B4669741 : Blo 2185435 4669741 := bbase (se 3 (by rfl) ⟨875576, by rfl⟩ : syracuseStep 4669741 = 1751153) (by norm_num)
theorem B6226321 : Blo 2185435 6226321 := bstep (se 2 (by rfl) ⟨2334870, by rfl⟩ : syracuseStep 6226321 = 4669741) B4669741
theorem B8301761 : Blo 2185435 8301761 := bstep (se 2 (by rfl) ⟨3113160, by rfl⟩ : syracuseStep 8301761 = 6226321) B6226321
theorem B5534507 : Blo 2185435 5534507 := bstep (se 1 (by rfl) ⟨4150880, by rfl⟩ : syracuseStep 5534507 = 8301761) B8301761
theorem B3689671 : Blo 2185435 3689671 := bstep (se 1 (by rfl) ⟨2767253, by rfl⟩ : syracuseStep 3689671 = 5534507) B5534507
theorem B4919561 : Blo 2185435 4919561 := bstep (se 2 (by rfl) ⟨1844835, by rfl⟩ : syracuseStep 4919561 = 3689671) B3689671
theorem B3279707 : Blo 2185435 3279707 := bstep (se 1 (by rfl) ⟨2459780, by rfl⟩ : syracuseStep 3279707 = 4919561) B4919561
theorem B2186471 : Blo 2185435 2186471 := bstep (se 1 (by rfl) ⟨1639853, by rfl⟩ : syracuseStep 2186471 = 3279707) B3279707
theorem B2459785 : Blo 2185435 2459785 := bbase (se 2 (by rfl) ⟨922419, by rfl⟩ : syracuseStep 2459785 = 1844839) (by norm_num)
theorem B3279713 : Blo 2185435 3279713 := bstep (se 2 (by rfl) ⟨1229892, by rfl⟩ : syracuseStep 3279713 = 2459785) B2459785
theorem B2186475 : Blo 2185435 2186475 := bstep (se 1 (by rfl) ⟨1639856, by rfl⟩ : syracuseStep 2186475 = 3279713) B3279713
theorem B4986701 : Blo 2185435 4986701 := bbase (se 3 (by rfl) ⟨935006, by rfl⟩ : syracuseStep 4986701 = 1870013) (by norm_num)
theorem B3324467 : Blo 2185435 3324467 := bstep (se 1 (by rfl) ⟨2493350, by rfl⟩ : syracuseStep 3324467 = 4986701) B4986701
theorem B2216311 : Blo 2185435 2216311 := bstep (se 1 (by rfl) ⟨1662233, by rfl⟩ : syracuseStep 2216311 = 3324467) B3324467
theorem B11820325 : Blo 2185435 11820325 := bstep (se 4 (by rfl) ⟨1108155, by rfl⟩ : syracuseStep 11820325 = 2216311) B2216311
theorem B15760433 : Blo 2185435 15760433 := bstep (se 2 (by rfl) ⟨5910162, by rfl⟩ : syracuseStep 15760433 = 11820325) B11820325
theorem B42027821 : Blo 2185435 42027821 := bstep (se 3 (by rfl) ⟨7880216, by rfl⟩ : syracuseStep 42027821 = 15760433) B15760433
theorem B28018547 : Blo 2185435 28018547 := bstep (se 1 (by rfl) ⟨21013910, by rfl⟩ : syracuseStep 28018547 = 42027821) B42027821
theorem B18679031 : Blo 2185435 18679031 := bstep (se 1 (by rfl) ⟨14009273, by rfl⟩ : syracuseStep 18679031 = 28018547) B28018547
theorem B12452687 : Blo 2185435 12452687 := bstep (se 1 (by rfl) ⟨9339515, by rfl⟩ : syracuseStep 12452687 = 18679031) B18679031
theorem B8301791 : Blo 2185435 8301791 := bstep (se 1 (by rfl) ⟨6226343, by rfl⟩ : syracuseStep 8301791 = 12452687) B12452687
theorem B5534527 : Blo 2185435 5534527 := bstep (se 1 (by rfl) ⟨4150895, by rfl⟩ : syracuseStep 5534527 = 8301791) B8301791
theorem B7379369 : Blo 2185435 7379369 := bstep (se 2 (by rfl) ⟨2767263, by rfl⟩ : syracuseStep 7379369 = 5534527) B5534527
theorem B4919579 : Blo 2185435 4919579 := bstep (se 1 (by rfl) ⟨3689684, by rfl⟩ : syracuseStep 4919579 = 7379369) B7379369
theorem B3279719 : Blo 2185435 3279719 := bstep (se 1 (by rfl) ⟨2459789, by rfl⟩ : syracuseStep 3279719 = 4919579) B4919579
theorem B2186479 : Blo 2185435 2186479 := bstep (se 1 (by rfl) ⟨1639859, by rfl⟩ : syracuseStep 2186479 = 3279719) B3279719
theorem B3279725 : Blo 2185435 3279725 := bbase (se 3 (by rfl) ⟨614948, by rfl⟩ : syracuseStep 3279725 = 1229897) (by norm_num)
theorem B2186483 : Blo 2185435 2186483 := bstep (se 1 (by rfl) ⟨1639862, by rfl⟩ : syracuseStep 2186483 = 3279725) B3279725
theorem B4919597 : Blo 2185435 4919597 := bbase (se 3 (by rfl) ⟨922424, by rfl⟩ : syracuseStep 4919597 = 1844849) (by norm_num)
theorem B3279731 : Blo 2185435 3279731 := bstep (se 1 (by rfl) ⟨2459798, by rfl⟩ : syracuseStep 3279731 = 4919597) B4919597
theorem B2186487 : Blo 2185435 2186487 := bstep (se 1 (by rfl) ⟨1639865, by rfl⟩ : syracuseStep 2186487 = 3279731) B3279731
theorem B7004677 : Blo 2185435 7004677 := bbase (se 4 (by rfl) ⟨656688, by rfl⟩ : syracuseStep 7004677 = 1313377) (by norm_num)
theorem B9339569 : Blo 2185435 9339569 := bstep (se 2 (by rfl) ⟨3502338, by rfl⟩ : syracuseStep 9339569 = 7004677) B7004677
theorem B6226379 : Blo 2185435 6226379 := bstep (se 1 (by rfl) ⟨4669784, by rfl⟩ : syracuseStep 6226379 = 9339569) B9339569
theorem B4150919 : Blo 2185435 4150919 := bstep (se 1 (by rfl) ⟨3113189, by rfl⟩ : syracuseStep 4150919 = 6226379) B6226379
theorem B2767279 : Blo 2185435 2767279 := bstep (se 1 (by rfl) ⟨2075459, by rfl⟩ : syracuseStep 2767279 = 4150919) B4150919
theorem B3689705 : Blo 2185435 3689705 := bstep (se 2 (by rfl) ⟨1383639, by rfl⟩ : syracuseStep 3689705 = 2767279) B2767279
theorem B2459803 : Blo 2185435 2459803 := bstep (se 1 (by rfl) ⟨1844852, by rfl⟩ : syracuseStep 2459803 = 3689705) B3689705
theorem B3279737 : Blo 2185435 3279737 := bstep (se 2 (by rfl) ⟨1229901, by rfl⟩ : syracuseStep 3279737 = 2459803) B2459803
theorem B2186491 : Blo 2185435 2186491 := bstep (se 1 (by rfl) ⟨1639868, by rfl⟩ : syracuseStep 2186491 = 3279737) B3279737
theorem B2339777 : Blo 2185435 2339777 := bbase (se 2 (by rfl) ⟨877416, by rfl⟩ : syracuseStep 2339777 = 1754833) (by norm_num)
theorem B99830485 : Blo 2185435 99830485 := bstep (se 7 (by rfl) ⟨1169888, by rfl⟩ : syracuseStep 99830485 = 2339777) B2339777
theorem B133107313 : Blo 2185435 133107313 := bstep (se 2 (by rfl) ⟨49915242, by rfl⟩ : syracuseStep 133107313 = 99830485) B99830485
theorem B177476417 : Blo 2185435 177476417 := bstep (se 2 (by rfl) ⟨66553656, by rfl⟩ : syracuseStep 177476417 = 133107313) B133107313
theorem B118317611 : Blo 2185435 118317611 := bstep (se 1 (by rfl) ⟨88738208, by rfl⟩ : syracuseStep 118317611 = 177476417) B177476417
theorem B78878407 : Blo 2185435 78878407 := bstep (se 1 (by rfl) ⟨59158805, by rfl⟩ : syracuseStep 78878407 = 118317611) B118317611
theorem B105171209 : Blo 2185435 105171209 := bstep (se 2 (by rfl) ⟨39439203, by rfl⟩ : syracuseStep 105171209 = 78878407) B78878407
theorem B70114139 : Blo 2185435 70114139 := bstep (se 1 (by rfl) ⟨52585604, by rfl⟩ : syracuseStep 70114139 = 105171209) B105171209
theorem B46742759 : Blo 2185435 46742759 := bstep (se 1 (by rfl) ⟨35057069, by rfl⟩ : syracuseStep 46742759 = 70114139) B70114139
theorem B31161839 : Blo 2185435 31161839 := bstep (se 1 (by rfl) ⟨23371379, by rfl⟩ : syracuseStep 31161839 = 46742759) B46742759
theorem B83098237 : Blo 2185435 83098237 := bstep (se 3 (by rfl) ⟨15580919, by rfl⟩ : syracuseStep 83098237 = 31161839) B31161839
theorem B110797649 : Blo 2185435 110797649 := bstep (se 2 (by rfl) ⟨41549118, by rfl⟩ : syracuseStep 110797649 = 83098237) B83098237
theorem B73865099 : Blo 2185435 73865099 := bstep (se 1 (by rfl) ⟨55398824, by rfl⟩ : syracuseStep 73865099 = 110797649) B110797649
theorem B49243399 : Blo 2185435 49243399 := bstep (se 1 (by rfl) ⟨36932549, by rfl⟩ : syracuseStep 49243399 = 73865099) B73865099
theorem B1050525845 : Blo 2185435 1050525845 := bstep (se 6 (by rfl) ⟨24621699, by rfl⟩ : syracuseStep 1050525845 = 49243399) B49243399
theorem B700350563 : Blo 2185435 700350563 := bstep (se 1 (by rfl) ⟨525262922, by rfl⟩ : syracuseStep 700350563 = 1050525845) B1050525845
theorem B466900375 : Blo 2185435 466900375 := bstep (se 1 (by rfl) ⟨350175281, by rfl⟩ : syracuseStep 466900375 = 700350563) B700350563
theorem B622533833 : Blo 2185435 622533833 := bstep (se 2 (by rfl) ⟨233450187, by rfl⟩ : syracuseStep 622533833 = 466900375) B466900375
theorem B415022555 : Blo 2185435 415022555 := bstep (se 1 (by rfl) ⟨311266916, by rfl⟩ : syracuseStep 415022555 = 622533833) B622533833
theorem B276681703 : Blo 2185435 276681703 := bstep (se 1 (by rfl) ⟨207511277, by rfl⟩ : syracuseStep 276681703 = 415022555) B415022555
theorem B368908937 : Blo 2185435 368908937 := bstep (se 2 (by rfl) ⟨138340851, by rfl⟩ : syracuseStep 368908937 = 276681703) B276681703
theorem B245939291 : Blo 2185435 245939291 := bstep (se 1 (by rfl) ⟨184454468, by rfl⟩ : syracuseStep 245939291 = 368908937) B368908937
theorem B163959527 : Blo 2185435 163959527 := bstep (se 1 (by rfl) ⟨122969645, by rfl⟩ : syracuseStep 163959527 = 245939291) B245939291
theorem B109306351 : Blo 2185435 109306351 := bstep (se 1 (by rfl) ⟨81979763, by rfl⟩ : syracuseStep 109306351 = 163959527) B163959527
theorem B145741801 : Blo 2185435 145741801 := bstep (se 2 (by rfl) ⟨54653175, by rfl⟩ : syracuseStep 145741801 = 109306351) B109306351
theorem B194322401 : Blo 2185435 194322401 := bstep (se 2 (by rfl) ⟨72870900, by rfl⟩ : syracuseStep 194322401 = 145741801) B145741801
theorem B129548267 : Blo 2185435 129548267 := bstep (se 1 (by rfl) ⟨97161200, by rfl⟩ : syracuseStep 129548267 = 194322401) B194322401
theorem B86365511 : Blo 2185435 86365511 := bstep (se 1 (by rfl) ⟨64774133, by rfl⟩ : syracuseStep 86365511 = 129548267) B129548267
theorem B57577007 : Blo 2185435 57577007 := bstep (se 1 (by rfl) ⟨43182755, by rfl⟩ : syracuseStep 57577007 = 86365511) B86365511
theorem B38384671 : Blo 2185435 38384671 := bstep (se 1 (by rfl) ⟨28788503, by rfl⟩ : syracuseStep 38384671 = 57577007) B57577007
theorem B51179561 : Blo 2185435 51179561 := bstep (se 2 (by rfl) ⟨19192335, by rfl⟩ : syracuseStep 51179561 = 38384671) B38384671
theorem B34119707 : Blo 2185435 34119707 := bstep (se 1 (by rfl) ⟨25589780, by rfl⟩ : syracuseStep 34119707 = 51179561) B51179561
theorem B90985885 : Blo 2185435 90985885 := bstep (se 3 (by rfl) ⟨17059853, by rfl⟩ : syracuseStep 90985885 = 34119707) B34119707
theorem B485258053 : Blo 2185435 485258053 := bstep (se 4 (by rfl) ⟨45492942, by rfl⟩ : syracuseStep 485258053 = 90985885) B90985885
theorem B647010737 : Blo 2185435 647010737 := bstep (se 2 (by rfl) ⟨242629026, by rfl⟩ : syracuseStep 647010737 = 485258053) B485258053
theorem B431340491 : Blo 2185435 431340491 := bstep (se 1 (by rfl) ⟨323505368, by rfl⟩ : syracuseStep 431340491 = 647010737) B647010737
theorem B287560327 : Blo 2185435 287560327 := bstep (se 1 (by rfl) ⟨215670245, by rfl⟩ : syracuseStep 287560327 = 431340491) B431340491
theorem B383413769 : Blo 2185435 383413769 := bstep (se 2 (by rfl) ⟨143780163, by rfl⟩ : syracuseStep 383413769 = 287560327) B287560327
theorem B255609179 : Blo 2185435 255609179 := bstep (se 1 (by rfl) ⟨191706884, by rfl⟩ : syracuseStep 255609179 = 383413769) B383413769
theorem B170406119 : Blo 2185435 170406119 := bstep (se 1 (by rfl) ⟨127804589, by rfl⟩ : syracuseStep 170406119 = 255609179) B255609179
theorem B454416317 : Blo 2185435 454416317 := bstep (se 3 (by rfl) ⟨85203059, by rfl⟩ : syracuseStep 454416317 = 170406119) B170406119
theorem B302944211 : Blo 2185435 302944211 := bstep (se 1 (by rfl) ⟨227208158, by rfl⟩ : syracuseStep 302944211 = 454416317) B454416317
theorem B201962807 : Blo 2185435 201962807 := bstep (se 1 (by rfl) ⟨151472105, by rfl⟩ : syracuseStep 201962807 = 302944211) B302944211
theorem B134641871 : Blo 2185435 134641871 := bstep (se 1 (by rfl) ⟨100981403, by rfl⟩ : syracuseStep 134641871 = 201962807) B201962807
theorem B89761247 : Blo 2185435 89761247 := bstep (se 1 (by rfl) ⟨67320935, by rfl⟩ : syracuseStep 89761247 = 134641871) B134641871
theorem B59840831 : Blo 2185435 59840831 := bstep (se 1 (by rfl) ⟨44880623, by rfl⟩ : syracuseStep 59840831 = 89761247) B89761247
theorem B39893887 : Blo 2185435 39893887 := bstep (se 1 (by rfl) ⟨29920415, by rfl⟩ : syracuseStep 39893887 = 59840831) B59840831
theorem B53191849 : Blo 2185435 53191849 := bstep (se 2 (by rfl) ⟨19946943, by rfl⟩ : syracuseStep 53191849 = 39893887) B39893887
theorem B70922465 : Blo 2185435 70922465 := bstep (se 2 (by rfl) ⟨26595924, by rfl⟩ : syracuseStep 70922465 = 53191849) B53191849
theorem B47281643 : Blo 2185435 47281643 := bstep (se 1 (by rfl) ⟨35461232, by rfl⟩ : syracuseStep 47281643 = 70922465) B70922465
theorem B31521095 : Blo 2185435 31521095 := bstep (se 1 (by rfl) ⟨23640821, by rfl⟩ : syracuseStep 31521095 = 47281643) B47281643
theorem B21014063 : Blo 2185435 21014063 := bstep (se 1 (by rfl) ⟨15760547, by rfl⟩ : syracuseStep 21014063 = 31521095) B31521095
theorem B14009375 : Blo 2185435 14009375 := bstep (se 1 (by rfl) ⟨10507031, by rfl⟩ : syracuseStep 14009375 = 21014063) B21014063
theorem B37358333 : Blo 2185435 37358333 := bstep (se 3 (by rfl) ⟨7004687, by rfl⟩ : syracuseStep 37358333 = 14009375) B14009375
theorem B24905555 : Blo 2185435 24905555 := bstep (se 1 (by rfl) ⟨18679166, by rfl⟩ : syracuseStep 24905555 = 37358333) B37358333
theorem B16603703 : Blo 2185435 16603703 := bstep (se 1 (by rfl) ⟨12452777, by rfl⟩ : syracuseStep 16603703 = 24905555) B24905555
theorem B11069135 : Blo 2185435 11069135 := bstep (se 1 (by rfl) ⟨8301851, by rfl⟩ : syracuseStep 11069135 = 16603703) B16603703
theorem B7379423 : Blo 2185435 7379423 := bstep (se 1 (by rfl) ⟨5534567, by rfl⟩ : syracuseStep 7379423 = 11069135) B11069135
theorem B4919615 : Blo 2185435 4919615 := bstep (se 1 (by rfl) ⟨3689711, by rfl⟩ : syracuseStep 4919615 = 7379423) B7379423
theorem B3279743 : Blo 2185435 3279743 := bstep (se 1 (by rfl) ⟨2459807, by rfl⟩ : syracuseStep 3279743 = 4919615) B4919615
theorem B2186495 : Blo 2185435 2186495 := bstep (se 1 (by rfl) ⟨1639871, by rfl⟩ : syracuseStep 2186495 = 3279743) B3279743
theorem B3279749 : Blo 2185435 3279749 := bbase (se 4 (by rfl) ⟨307476, by rfl⟩ : syracuseStep 3279749 = 614953) (by norm_num)
theorem B2186499 : Blo 2185435 2186499 := bstep (se 1 (by rfl) ⟨1639874, by rfl⟩ : syracuseStep 2186499 = 3279749) B3279749
theorem B3689725 : Blo 2185435 3689725 := bbase (se 3 (by rfl) ⟨691823, by rfl⟩ : syracuseStep 3689725 = 1383647) (by norm_num)
theorem B4919633 : Blo 2185435 4919633 := bstep (se 2 (by rfl) ⟨1844862, by rfl⟩ : syracuseStep 4919633 = 3689725) B3689725
theorem B3279755 : Blo 2185435 3279755 := bstep (se 1 (by rfl) ⟨2459816, by rfl⟩ : syracuseStep 3279755 = 4919633) B4919633
theorem B2186503 : Blo 2185435 2186503 := bstep (se 1 (by rfl) ⟨1639877, by rfl⟩ : syracuseStep 2186503 = 3279755) B3279755
theorem B2459821 : Blo 2185435 2459821 := bbase (se 3 (by rfl) ⟨461216, by rfl⟩ : syracuseStep 2459821 = 922433) (by norm_num)
theorem B3279761 : Blo 2185435 3279761 := bstep (se 2 (by rfl) ⟨1229910, by rfl⟩ : syracuseStep 3279761 = 2459821) B2459821
theorem B2186507 : Blo 2185435 2186507 := bstep (se 1 (by rfl) ⟨1639880, by rfl⟩ : syracuseStep 2186507 = 3279761) B3279761
theorem B7379477 : Blo 2185435 7379477 := bbase (se 6 (by rfl) ⟨172956, by rfl⟩ : syracuseStep 7379477 = 345913) (by norm_num)
theorem B4919651 : Blo 2185435 4919651 := bstep (se 1 (by rfl) ⟨3689738, by rfl⟩ : syracuseStep 4919651 = 7379477) B7379477
theorem B3279767 : Blo 2185435 3279767 := bstep (se 1 (by rfl) ⟨2459825, by rfl⟩ : syracuseStep 3279767 = 4919651) B4919651
theorem B2186511 : Blo 2185435 2186511 := bstep (se 1 (by rfl) ⟨1639883, by rfl⟩ : syracuseStep 2186511 = 3279767) B3279767
theorem B3279773 : Blo 2185435 3279773 := bbase (se 3 (by rfl) ⟨614957, by rfl⟩ : syracuseStep 3279773 = 1229915) (by norm_num)
theorem B2186515 : Blo 2185435 2186515 := bstep (se 1 (by rfl) ⟨1639886, by rfl⟩ : syracuseStep 2186515 = 3279773) B3279773
theorem B4919669 : Blo 2185435 4919669 := bbase (se 5 (by rfl) ⟨230609, by rfl⟩ : syracuseStep 4919669 = 461219) (by norm_num)
theorem B3279779 : Blo 2185435 3279779 := bstep (se 1 (by rfl) ⟨2459834, by rfl⟩ : syracuseStep 3279779 = 4919669) B4919669
theorem B2186519 : Blo 2185435 2186519 := bstep (se 1 (by rfl) ⟨1639889, by rfl⟩ : syracuseStep 2186519 = 3279779) B3279779
theorem B14009557 : Blo 2185435 14009557 := bbase (se 7 (by rfl) ⟨164174, by rfl⟩ : syracuseStep 14009557 = 328349) (by norm_num)
theorem B18679409 : Blo 2185435 18679409 := bstep (se 2 (by rfl) ⟨7004778, by rfl⟩ : syracuseStep 18679409 = 14009557) B14009557
theorem B12452939 : Blo 2185435 12452939 := bstep (se 1 (by rfl) ⟨9339704, by rfl⟩ : syracuseStep 12452939 = 18679409) B18679409
theorem B8301959 : Blo 2185435 8301959 := bstep (se 1 (by rfl) ⟨6226469, by rfl⟩ : syracuseStep 8301959 = 12452939) B12452939
theorem B5534639 : Blo 2185435 5534639 := bstep (se 1 (by rfl) ⟨4150979, by rfl⟩ : syracuseStep 5534639 = 8301959) B8301959
theorem B3689759 : Blo 2185435 3689759 := bstep (se 1 (by rfl) ⟨2767319, by rfl⟩ : syracuseStep 3689759 = 5534639) B5534639
theorem B2459839 : Blo 2185435 2459839 := bstep (se 1 (by rfl) ⟨1844879, by rfl⟩ : syracuseStep 2459839 = 3689759) B3689759
theorem B3279785 : Blo 2185435 3279785 := bstep (se 2 (by rfl) ⟨1229919, by rfl⟩ : syracuseStep 3279785 = 2459839) B2459839
theorem B2186523 : Blo 2185435 2186523 := bstep (se 1 (by rfl) ⟨1639892, by rfl⟩ : syracuseStep 2186523 = 3279785) B3279785
theorem B8301973 : Blo 2185435 8301973 := bbase (se 6 (by rfl) ⟨194577, by rfl⟩ : syracuseStep 8301973 = 389155) (by norm_num)
theorem B11069297 : Blo 2185435 11069297 := bstep (se 2 (by rfl) ⟨4150986, by rfl⟩ : syracuseStep 11069297 = 8301973) B8301973
theorem B7379531 : Blo 2185435 7379531 := bstep (se 1 (by rfl) ⟨5534648, by rfl⟩ : syracuseStep 7379531 = 11069297) B11069297
theorem B4919687 : Blo 2185435 4919687 := bstep (se 1 (by rfl) ⟨3689765, by rfl⟩ : syracuseStep 4919687 = 7379531) B7379531
theorem B3279791 : Blo 2185435 3279791 := bstep (se 1 (by rfl) ⟨2459843, by rfl⟩ : syracuseStep 3279791 = 4919687) B4919687
theorem B2186527 : Blo 2185435 2186527 := bstep (se 1 (by rfl) ⟨1639895, by rfl⟩ : syracuseStep 2186527 = 3279791) B3279791
theorem B3279797 : Blo 2185435 3279797 := bbase (se 5 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 3279797 = 307481) (by norm_num)
theorem B2186531 : Blo 2185435 2186531 := bstep (se 1 (by rfl) ⟨1639898, by rfl⟩ : syracuseStep 2186531 = 3279797) B3279797
theorem B5534669 : Blo 2185435 5534669 := bbase (se 3 (by rfl) ⟨1037750, by rfl⟩ : syracuseStep 5534669 = 2075501) (by norm_num)
theorem B3689779 : Blo 2185435 3689779 := bstep (se 1 (by rfl) ⟨2767334, by rfl⟩ : syracuseStep 3689779 = 5534669) B5534669
theorem B4919705 : Blo 2185435 4919705 := bstep (se 2 (by rfl) ⟨1844889, by rfl⟩ : syracuseStep 4919705 = 3689779) B3689779
theorem B3279803 : Blo 2185435 3279803 := bstep (se 1 (by rfl) ⟨2459852, by rfl⟩ : syracuseStep 3279803 = 4919705) B4919705
theorem B2186535 : Blo 2185435 2186535 := bstep (se 1 (by rfl) ⟨1639901, by rfl⟩ : syracuseStep 2186535 = 3279803) B3279803
theorem B2459857 : Blo 2185435 2459857 := bbase (se 2 (by rfl) ⟨922446, by rfl⟩ : syracuseStep 2459857 = 1844893) (by norm_num)
theorem B3279809 : Blo 2185435 3279809 := bstep (se 2 (by rfl) ⟨1229928, by rfl⟩ : syracuseStep 3279809 = 2459857) B2459857
theorem B2186539 : Blo 2185435 2186539 := bstep (se 1 (by rfl) ⟨1639904, by rfl⟩ : syracuseStep 2186539 = 3279809) B3279809
theorem B3324565 : Blo 2185435 3324565 := bbase (se 6 (by rfl) ⟨77919, by rfl⟩ : syracuseStep 3324565 = 155839) (by norm_num)
theorem B4432753 : Blo 2185435 4432753 := bstep (se 2 (by rfl) ⟨1662282, by rfl⟩ : syracuseStep 4432753 = 3324565) B3324565
theorem B5910337 : Blo 2185435 5910337 := bstep (se 2 (by rfl) ⟨2216376, by rfl⟩ : syracuseStep 5910337 = 4432753) B4432753
theorem B7880449 : Blo 2185435 7880449 := bstep (se 2 (by rfl) ⟨2955168, by rfl⟩ : syracuseStep 7880449 = 5910337) B5910337
theorem B10507265 : Blo 2185435 10507265 := bstep (se 2 (by rfl) ⟨3940224, by rfl⟩ : syracuseStep 10507265 = 7880449) B7880449
theorem B7004843 : Blo 2185435 7004843 := bstep (se 1 (by rfl) ⟨5253632, by rfl⟩ : syracuseStep 7004843 = 10507265) B10507265
theorem B4669895 : Blo 2185435 4669895 := bstep (se 1 (by rfl) ⟨3502421, by rfl⟩ : syracuseStep 4669895 = 7004843) B7004843
theorem B3113263 : Blo 2185435 3113263 := bstep (se 1 (by rfl) ⟨2334947, by rfl⟩ : syracuseStep 3113263 = 4669895) B4669895
theorem B4151017 : Blo 2185435 4151017 := bstep (se 2 (by rfl) ⟨1556631, by rfl⟩ : syracuseStep 4151017 = 3113263) B3113263
theorem B5534689 : Blo 2185435 5534689 := bstep (se 2 (by rfl) ⟨2075508, by rfl⟩ : syracuseStep 5534689 = 4151017) B4151017
theorem B7379585 : Blo 2185435 7379585 := bstep (se 2 (by rfl) ⟨2767344, by rfl⟩ : syracuseStep 7379585 = 5534689) B5534689
theorem B4919723 : Blo 2185435 4919723 := bstep (se 1 (by rfl) ⟨3689792, by rfl⟩ : syracuseStep 4919723 = 7379585) B7379585
theorem B3279815 : Blo 2185435 3279815 := bstep (se 1 (by rfl) ⟨2459861, by rfl⟩ : syracuseStep 3279815 = 4919723) B4919723
theorem B2186543 : Blo 2185435 2186543 := bstep (se 1 (by rfl) ⟨1639907, by rfl⟩ : syracuseStep 2186543 = 3279815) B3279815
theorem B3279821 : Blo 2185435 3279821 := bbase (se 3 (by rfl) ⟨614966, by rfl⟩ : syracuseStep 3279821 = 1229933) (by norm_num)
theorem B2186547 : Blo 2185435 2186547 := bstep (se 1 (by rfl) ⟨1639910, by rfl⟩ : syracuseStep 2186547 = 3279821) B3279821
theorem B4919741 : Blo 2185435 4919741 := bbase (se 3 (by rfl) ⟨922451, by rfl⟩ : syracuseStep 4919741 = 1844903) (by norm_num)
theorem B3279827 : Blo 2185435 3279827 := bstep (se 1 (by rfl) ⟨2459870, by rfl⟩ : syracuseStep 3279827 = 4919741) B4919741
theorem B2186551 : Blo 2185435 2186551 := bstep (se 1 (by rfl) ⟨1639913, by rfl⟩ : syracuseStep 2186551 = 3279827) B3279827
theorem B3689813 : Blo 2185435 3689813 := bbase (se 11 (by rfl) ⟨2702, by rfl⟩ : syracuseStep 3689813 = 5405) (by norm_num)
theorem B2459875 : Blo 2185435 2459875 := bstep (se 1 (by rfl) ⟨1844906, by rfl⟩ : syracuseStep 2459875 = 3689813) B3689813
theorem B3279833 : Blo 2185435 3279833 := bstep (se 2 (by rfl) ⟨1229937, by rfl⟩ : syracuseStep 3279833 = 2459875) B2459875
theorem B2186555 : Blo 2185435 2186555 := bstep (se 1 (by rfl) ⟨1639916, by rfl⟩ : syracuseStep 2186555 = 3279833) B3279833
theorem B3940253 : Blo 2185435 3940253 := bbase (se 3 (by rfl) ⟨738797, by rfl⟩ : syracuseStep 3940253 = 1477595) (by norm_num)
theorem B2626835 : Blo 2185435 2626835 := bstep (se 1 (by rfl) ⟨1970126, by rfl⟩ : syracuseStep 2626835 = 3940253) B3940253
theorem B7004893 : Blo 2185435 7004893 := bstep (se 3 (by rfl) ⟨1313417, by rfl⟩ : syracuseStep 7004893 = 2626835) B2626835
theorem B9339857 : Blo 2185435 9339857 := bstep (se 2 (by rfl) ⟨3502446, by rfl⟩ : syracuseStep 9339857 = 7004893) B7004893
theorem B6226571 : Blo 2185435 6226571 := bstep (se 1 (by rfl) ⟨4669928, by rfl⟩ : syracuseStep 6226571 = 9339857) B9339857
theorem B16604189 : Blo 2185435 16604189 := bstep (se 3 (by rfl) ⟨3113285, by rfl⟩ : syracuseStep 16604189 = 6226571) B6226571
theorem B11069459 : Blo 2185435 11069459 := bstep (se 1 (by rfl) ⟨8302094, by rfl⟩ : syracuseStep 11069459 = 16604189) B16604189
theorem B7379639 : Blo 2185435 7379639 := bstep (se 1 (by rfl) ⟨5534729, by rfl⟩ : syracuseStep 7379639 = 11069459) B11069459
theorem B4919759 : Blo 2185435 4919759 := bstep (se 1 (by rfl) ⟨3689819, by rfl⟩ : syracuseStep 4919759 = 7379639) B7379639
theorem B3279839 : Blo 2185435 3279839 := bstep (se 1 (by rfl) ⟨2459879, by rfl⟩ : syracuseStep 3279839 = 4919759) B4919759
theorem B2186559 : Blo 2185435 2186559 := bstep (se 1 (by rfl) ⟨1639919, by rfl⟩ : syracuseStep 2186559 = 3279839) B3279839
theorem B3279845 : Blo 2185435 3279845 := bbase (se 4 (by rfl) ⟨307485, by rfl⟩ : syracuseStep 3279845 = 614971) (by norm_num)
theorem B2186563 : Blo 2185435 2186563 := bstep (se 1 (by rfl) ⟨1639922, by rfl⟩ : syracuseStep 2186563 = 3279845) B3279845
theorem B9339893 : Blo 2185435 9339893 := bbase (se 5 (by rfl) ⟨437807, by rfl⟩ : syracuseStep 9339893 = 875615) (by norm_num)
theorem B6226595 : Blo 2185435 6226595 := bstep (se 1 (by rfl) ⟨4669946, by rfl⟩ : syracuseStep 6226595 = 9339893) B9339893
theorem B4151063 : Blo 2185435 4151063 := bstep (se 1 (by rfl) ⟨3113297, by rfl⟩ : syracuseStep 4151063 = 6226595) B6226595
theorem B2767375 : Blo 2185435 2767375 := bstep (se 1 (by rfl) ⟨2075531, by rfl⟩ : syracuseStep 2767375 = 4151063) B4151063
theorem B3689833 : Blo 2185435 3689833 := bstep (se 2 (by rfl) ⟨1383687, by rfl⟩ : syracuseStep 3689833 = 2767375) B2767375
theorem B4919777 : Blo 2185435 4919777 := bstep (se 2 (by rfl) ⟨1844916, by rfl⟩ : syracuseStep 4919777 = 3689833) B3689833
theorem B3279851 : Blo 2185435 3279851 := bstep (se 1 (by rfl) ⟨2459888, by rfl⟩ : syracuseStep 3279851 = 4919777) B4919777
theorem B2186567 : Blo 2185435 2186567 := bstep (se 1 (by rfl) ⟨1639925, by rfl⟩ : syracuseStep 2186567 = 3279851) B3279851
theorem B2459893 : Blo 2185435 2459893 := bbase (se 5 (by rfl) ⟨115307, by rfl⟩ : syracuseStep 2459893 = 230615) (by norm_num)
theorem B3279857 : Blo 2185435 3279857 := bstep (se 2 (by rfl) ⟨1229946, by rfl⟩ : syracuseStep 3279857 = 2459893) B2459893
theorem B2186571 : Blo 2185435 2186571 := bstep (se 1 (by rfl) ⟨1639928, by rfl⟩ : syracuseStep 2186571 = 3279857) B3279857
theorem B2767385 : Blo 2185435 2767385 := bbase (se 2 (by rfl) ⟨1037769, by rfl⟩ : syracuseStep 2767385 = 2075539) (by norm_num)
theorem B7379693 : Blo 2185435 7379693 := bstep (se 3 (by rfl) ⟨1383692, by rfl⟩ : syracuseStep 7379693 = 2767385) B2767385
theorem B4919795 : Blo 2185435 4919795 := bstep (se 1 (by rfl) ⟨3689846, by rfl⟩ : syracuseStep 4919795 = 7379693) B7379693
theorem B3279863 : Blo 2185435 3279863 := bstep (se 1 (by rfl) ⟨2459897, by rfl⟩ : syracuseStep 3279863 = 4919795) B4919795
theorem B2186575 : Blo 2185435 2186575 := bstep (se 1 (by rfl) ⟨1639931, by rfl⟩ : syracuseStep 2186575 = 3279863) B3279863
theorem B3279869 : Blo 2185435 3279869 := bbase (se 3 (by rfl) ⟨614975, by rfl⟩ : syracuseStep 3279869 = 1229951) (by norm_num)
theorem B2186579 : Blo 2185435 2186579 := bstep (se 1 (by rfl) ⟨1639934, by rfl⟩ : syracuseStep 2186579 = 3279869) B3279869
theorem B4919813 : Blo 2185435 4919813 := bbase (se 4 (by rfl) ⟨461232, by rfl⟩ : syracuseStep 4919813 = 922465) (by norm_num)
theorem B3279875 : Blo 2185435 3279875 := bstep (se 1 (by rfl) ⟨2459906, by rfl⟩ : syracuseStep 3279875 = 4919813) B4919813
theorem B2186583 : Blo 2185435 2186583 := bstep (se 1 (by rfl) ⟨1639937, by rfl⟩ : syracuseStep 2186583 = 3279875) B3279875
theorem B4151101 : Blo 2185435 4151101 := bbase (se 3 (by rfl) ⟨778331, by rfl⟩ : syracuseStep 4151101 = 1556663) (by norm_num)
theorem B5534801 : Blo 2185435 5534801 := bstep (se 2 (by rfl) ⟨2075550, by rfl⟩ : syracuseStep 5534801 = 4151101) B4151101
theorem B3689867 : Blo 2185435 3689867 := bstep (se 1 (by rfl) ⟨2767400, by rfl⟩ : syracuseStep 3689867 = 5534801) B5534801
theorem B2459911 : Blo 2185435 2459911 := bstep (se 1 (by rfl) ⟨1844933, by rfl⟩ : syracuseStep 2459911 = 3689867) B3689867
theorem B3279881 : Blo 2185435 3279881 := bstep (se 2 (by rfl) ⟨1229955, by rfl⟩ : syracuseStep 3279881 = 2459911) B2459911
theorem B2186587 : Blo 2185435 2186587 := bstep (se 1 (by rfl) ⟨1639940, by rfl⟩ : syracuseStep 2186587 = 3279881) B3279881
theorem B11069621 : Blo 2185435 11069621 := bbase (se 5 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 11069621 = 1037777) (by norm_num)
theorem B7379747 : Blo 2185435 7379747 := bstep (se 1 (by rfl) ⟨5534810, by rfl⟩ : syracuseStep 7379747 = 11069621) B11069621
theorem B4919831 : Blo 2185435 4919831 := bstep (se 1 (by rfl) ⟨3689873, by rfl⟩ : syracuseStep 4919831 = 7379747) B7379747
theorem B3279887 : Blo 2185435 3279887 := bstep (se 1 (by rfl) ⟨2459915, by rfl⟩ : syracuseStep 3279887 = 4919831) B4919831
theorem B2186591 : Blo 2185435 2186591 := bstep (se 1 (by rfl) ⟨1639943, by rfl⟩ : syracuseStep 2186591 = 3279887) B3279887
theorem B3279893 : Blo 2185435 3279893 := bbase (se 6 (by rfl) ⟨76872, by rfl⟩ : syracuseStep 3279893 = 153745) (by norm_num)
theorem B2186595 : Blo 2185435 2186595 := bstep (se 1 (by rfl) ⟨1639946, by rfl⟩ : syracuseStep 2186595 = 3279893) B3279893
theorem B7100597 : Blo 2185435 7100597 := bbase (se 5 (by rfl) ⟨332840, by rfl⟩ : syracuseStep 7100597 = 665681) (by norm_num)
theorem B4733731 : Blo 2185435 4733731 := bstep (se 1 (by rfl) ⟨3550298, by rfl⟩ : syracuseStep 4733731 = 7100597) B7100597
theorem B6311641 : Blo 2185435 6311641 := bstep (se 2 (by rfl) ⟨2366865, by rfl⟩ : syracuseStep 6311641 = 4733731) B4733731
theorem B8415521 : Blo 2185435 8415521 := bstep (se 2 (by rfl) ⟨3155820, by rfl⟩ : syracuseStep 8415521 = 6311641) B6311641
theorem B5610347 : Blo 2185435 5610347 := bstep (se 1 (by rfl) ⟨4207760, by rfl⟩ : syracuseStep 5610347 = 8415521) B8415521
theorem B3740231 : Blo 2185435 3740231 := bstep (se 1 (by rfl) ⟨2805173, by rfl⟩ : syracuseStep 3740231 = 5610347) B5610347
theorem B2493487 : Blo 2185435 2493487 := bstep (se 1 (by rfl) ⟨1870115, by rfl⟩ : syracuseStep 2493487 = 3740231) B3740231
theorem B13298597 : Blo 2185435 13298597 := bstep (se 4 (by rfl) ⟨1246743, by rfl⟩ : syracuseStep 13298597 = 2493487) B2493487
theorem B8865731 : Blo 2185435 8865731 := bstep (se 1 (by rfl) ⟨6649298, by rfl⟩ : syracuseStep 8865731 = 13298597) B13298597
theorem B23641949 : Blo 2185435 23641949 := bstep (se 3 (by rfl) ⟨4432865, by rfl⟩ : syracuseStep 23641949 = 8865731) B8865731
theorem B15761299 : Blo 2185435 15761299 := bstep (se 1 (by rfl) ⟨11820974, by rfl⟩ : syracuseStep 15761299 = 23641949) B23641949
theorem B21015065 : Blo 2185435 21015065 := bstep (se 2 (by rfl) ⟨7880649, by rfl⟩ : syracuseStep 21015065 = 15761299) B15761299
theorem B14010043 : Blo 2185435 14010043 := bstep (se 1 (by rfl) ⟨10507532, by rfl⟩ : syracuseStep 14010043 = 21015065) B21015065
theorem B18680057 : Blo 2185435 18680057 := bstep (se 2 (by rfl) ⟨7005021, by rfl⟩ : syracuseStep 18680057 = 14010043) B14010043
theorem B12453371 : Blo 2185435 12453371 := bstep (se 1 (by rfl) ⟨9340028, by rfl⟩ : syracuseStep 12453371 = 18680057) B18680057
theorem B8302247 : Blo 2185435 8302247 := bstep (se 1 (by rfl) ⟨6226685, by rfl⟩ : syracuseStep 8302247 = 12453371) B12453371
theorem B5534831 : Blo 2185435 5534831 := bstep (se 1 (by rfl) ⟨4151123, by rfl⟩ : syracuseStep 5534831 = 8302247) B8302247
theorem B3689887 : Blo 2185435 3689887 := bstep (se 1 (by rfl) ⟨2767415, by rfl⟩ : syracuseStep 3689887 = 5534831) B5534831
theorem B4919849 : Blo 2185435 4919849 := bstep (se 2 (by rfl) ⟨1844943, by rfl⟩ : syracuseStep 4919849 = 3689887) B3689887
theorem B3279899 : Blo 2185435 3279899 := bstep (se 1 (by rfl) ⟨2459924, by rfl⟩ : syracuseStep 3279899 = 4919849) B4919849
theorem B2186599 : Blo 2185435 2186599 := bstep (se 1 (by rfl) ⟨1639949, by rfl⟩ : syracuseStep 2186599 = 3279899) B3279899
theorem B2459929 : Blo 2185435 2459929 := bbase (se 2 (by rfl) ⟨922473, by rfl⟩ : syracuseStep 2459929 = 1844947) (by norm_num)
theorem B3279905 : Blo 2185435 3279905 := bstep (se 2 (by rfl) ⟨1229964, by rfl⟩ : syracuseStep 3279905 = 2459929) B2459929
theorem B2186603 : Blo 2185435 2186603 := bstep (se 1 (by rfl) ⟨1639952, by rfl⟩ : syracuseStep 2186603 = 3279905) B3279905
theorem B8302277 : Blo 2185435 8302277 := bbase (se 4 (by rfl) ⟨778338, by rfl⟩ : syracuseStep 8302277 = 1556677) (by norm_num)
theorem B5534851 : Blo 2185435 5534851 := bstep (se 1 (by rfl) ⟨4151138, by rfl⟩ : syracuseStep 5534851 = 8302277) B8302277
theorem B7379801 : Blo 2185435 7379801 := bstep (se 2 (by rfl) ⟨2767425, by rfl⟩ : syracuseStep 7379801 = 5534851) B5534851
theorem B4919867 : Blo 2185435 4919867 := bstep (se 1 (by rfl) ⟨3689900, by rfl⟩ : syracuseStep 4919867 = 7379801) B7379801
theorem B3279911 : Blo 2185435 3279911 := bstep (se 1 (by rfl) ⟨2459933, by rfl⟩ : syracuseStep 3279911 = 4919867) B4919867
theorem B2186607 : Blo 2185435 2186607 := bstep (se 1 (by rfl) ⟨1639955, by rfl⟩ : syracuseStep 2186607 = 3279911) B3279911
theorem B3279917 : Blo 2185435 3279917 := bbase (se 3 (by rfl) ⟨614984, by rfl⟩ : syracuseStep 3279917 = 1229969) (by norm_num)
theorem B2186611 : Blo 2185435 2186611 := bstep (se 1 (by rfl) ⟨1639958, by rfl⟩ : syracuseStep 2186611 = 3279917) B3279917
theorem B4919885 : Blo 2185435 4919885 := bbase (se 3 (by rfl) ⟨922478, by rfl⟩ : syracuseStep 4919885 = 1844957) (by norm_num)
theorem B3279923 : Blo 2185435 3279923 := bstep (se 1 (by rfl) ⟨2459942, by rfl⟩ : syracuseStep 3279923 = 4919885) B4919885
theorem B2186615 : Blo 2185435 2186615 := bstep (se 1 (by rfl) ⟨1639961, by rfl⟩ : syracuseStep 2186615 = 3279923) B3279923
theorem B2767441 : Blo 2185435 2767441 := bbase (se 2 (by rfl) ⟨1037790, by rfl⟩ : syracuseStep 2767441 = 2075581) (by norm_num)
theorem B3689921 : Blo 2185435 3689921 := bstep (se 2 (by rfl) ⟨1383720, by rfl⟩ : syracuseStep 3689921 = 2767441) B2767441
theorem B2459947 : Blo 2185435 2459947 := bstep (se 1 (by rfl) ⟨1844960, by rfl⟩ : syracuseStep 2459947 = 3689921) B3689921
theorem B3279929 : Blo 2185435 3279929 := bstep (se 2 (by rfl) ⟨1229973, by rfl⟩ : syracuseStep 3279929 = 2459947) B2459947
theorem B2186619 : Blo 2185435 2186619 := bstep (se 1 (by rfl) ⟨1639964, by rfl⟩ : syracuseStep 2186619 = 3279929) B3279929
theorem B3502549 : Blo 2185435 3502549 := bbase (se 7 (by rfl) ⟨41045, by rfl⟩ : syracuseStep 3502549 = 82091) (by norm_num)
theorem B4670065 : Blo 2185435 4670065 := bstep (se 2 (by rfl) ⟨1751274, by rfl⟩ : syracuseStep 4670065 = 3502549) B3502549
theorem B24907013 : Blo 2185435 24907013 := bstep (se 4 (by rfl) ⟨2335032, by rfl⟩ : syracuseStep 24907013 = 4670065) B4670065
theorem B16604675 : Blo 2185435 16604675 := bstep (se 1 (by rfl) ⟨12453506, by rfl⟩ : syracuseStep 16604675 = 24907013) B24907013
theorem B11069783 : Blo 2185435 11069783 := bstep (se 1 (by rfl) ⟨8302337, by rfl⟩ : syracuseStep 11069783 = 16604675) B16604675
theorem B7379855 : Blo 2185435 7379855 := bstep (se 1 (by rfl) ⟨5534891, by rfl⟩ : syracuseStep 7379855 = 11069783) B11069783
theorem B4919903 : Blo 2185435 4919903 := bstep (se 1 (by rfl) ⟨3689927, by rfl⟩ : syracuseStep 4919903 = 7379855) B7379855
theorem B3279935 : Blo 2185435 3279935 := bstep (se 1 (by rfl) ⟨2459951, by rfl⟩ : syracuseStep 3279935 = 4919903) B4919903
theorem B2186623 : Blo 2185435 2186623 := bstep (se 1 (by rfl) ⟨1639967, by rfl⟩ : syracuseStep 2186623 = 3279935) B3279935
theorem B3279941 : Blo 2185435 3279941 := bbase (se 4 (by rfl) ⟨307494, by rfl⟩ : syracuseStep 3279941 = 614989) (by norm_num)
theorem B2186627 : Blo 2185435 2186627 := bstep (se 1 (by rfl) ⟨1639970, by rfl⟩ : syracuseStep 2186627 = 3279941) B3279941
theorem B3689941 : Blo 2185435 3689941 := bbase (se 7 (by rfl) ⟨43241, by rfl⟩ : syracuseStep 3689941 = 86483) (by norm_num)
theorem B4919921 : Blo 2185435 4919921 := bstep (se 2 (by rfl) ⟨1844970, by rfl⟩ : syracuseStep 4919921 = 3689941) B3689941
theorem B3279947 : Blo 2185435 3279947 := bstep (se 1 (by rfl) ⟨2459960, by rfl⟩ : syracuseStep 3279947 = 4919921) B4919921
theorem B2186631 : Blo 2185435 2186631 := bstep (se 1 (by rfl) ⟨1639973, by rfl⟩ : syracuseStep 2186631 = 3279947) B3279947
theorem B2459965 : Blo 2185435 2459965 := bbase (se 3 (by rfl) ⟨461243, by rfl⟩ : syracuseStep 2459965 = 922487) (by norm_num)
theorem B3279953 : Blo 2185435 3279953 := bstep (se 2 (by rfl) ⟨1229982, by rfl⟩ : syracuseStep 3279953 = 2459965) B2459965
theorem B2186635 : Blo 2185435 2186635 := bstep (se 1 (by rfl) ⟨1639976, by rfl⟩ : syracuseStep 2186635 = 3279953) B3279953
theorem B7379909 : Blo 2185435 7379909 := bbase (se 4 (by rfl) ⟨691866, by rfl⟩ : syracuseStep 7379909 = 1383733) (by norm_num)
theorem B4919939 : Blo 2185435 4919939 := bstep (se 1 (by rfl) ⟨3689954, by rfl⟩ : syracuseStep 4919939 = 7379909) B7379909
theorem B3279959 : Blo 2185435 3279959 := bstep (se 1 (by rfl) ⟨2459969, by rfl⟩ : syracuseStep 3279959 = 4919939) B4919939
theorem B2186639 : Blo 2185435 2186639 := bstep (se 1 (by rfl) ⟨1639979, by rfl⟩ : syracuseStep 2186639 = 3279959) B3279959
theorem B3279965 : Blo 2185435 3279965 := bbase (se 3 (by rfl) ⟨614993, by rfl⟩ : syracuseStep 3279965 = 1229987) (by norm_num)
theorem B2186643 : Blo 2185435 2186643 := bstep (se 1 (by rfl) ⟨1639982, by rfl⟩ : syracuseStep 2186643 = 3279965) B3279965
theorem B4919957 : Blo 2185435 4919957 := bbase (se 6 (by rfl) ⟨115311, by rfl⟩ : syracuseStep 4919957 = 230623) (by norm_num)
theorem B3279971 : Blo 2185435 3279971 := bstep (se 1 (by rfl) ⟨2459978, by rfl⟩ : syracuseStep 3279971 = 4919957) B4919957
theorem B2186647 : Blo 2185435 2186647 := bstep (se 1 (by rfl) ⟨1639985, by rfl⟩ : syracuseStep 2186647 = 3279971) B3279971
theorem B5253893 : Blo 2185435 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B3502595 : Blo 2185435 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B2335063 : Blo 2185435 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B3113417 : Blo 2185435 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B8302445 : Blo 2185435 8302445 := bstep (se 3 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 8302445 = 3113417) B3113417
theorem B5534963 : Blo 2185435 5534963 := bstep (se 1 (by rfl) ⟨4151222, by rfl⟩ : syracuseStep 5534963 = 8302445) B8302445
theorem B3689975 : Blo 2185435 3689975 := bstep (se 1 (by rfl) ⟨2767481, by rfl⟩ : syracuseStep 3689975 = 5534963) B5534963
theorem B2459983 : Blo 2185435 2459983 := bstep (se 1 (by rfl) ⟨1844987, by rfl⟩ : syracuseStep 2459983 = 3689975) B3689975
theorem B3279977 : Blo 2185435 3279977 := bstep (se 2 (by rfl) ⟨1229991, by rfl⟩ : syracuseStep 3279977 = 2459983) B2459983
theorem B2186651 : Blo 2185435 2186651 := bstep (se 1 (by rfl) ⟨1639988, by rfl⟩ : syracuseStep 2186651 = 3279977) B3279977
theorem B2527573 : Blo 2185435 2527573 := bbase (se 10 (by rfl) ⟨3702, by rfl⟩ : syracuseStep 2527573 = 7405) (by norm_num)
theorem B3370097 : Blo 2185435 3370097 := bstep (se 2 (by rfl) ⟨1263786, by rfl⟩ : syracuseStep 3370097 = 2527573) B2527573
theorem B8986925 : Blo 2185435 8986925 := bstep (se 3 (by rfl) ⟨1685048, by rfl⟩ : syracuseStep 8986925 = 3370097) B3370097
theorem B5991283 : Blo 2185435 5991283 := bstep (se 1 (by rfl) ⟨4493462, by rfl⟩ : syracuseStep 5991283 = 8986925) B8986925
theorem B7988377 : Blo 2185435 7988377 := bstep (se 2 (by rfl) ⟨2995641, by rfl⟩ : syracuseStep 7988377 = 5991283) B5991283
theorem B10651169 : Blo 2185435 10651169 := bstep (se 2 (by rfl) ⟨3994188, by rfl⟩ : syracuseStep 10651169 = 7988377) B7988377
theorem B7100779 : Blo 2185435 7100779 := bstep (se 1 (by rfl) ⟨5325584, by rfl⟩ : syracuseStep 7100779 = 10651169) B10651169
theorem B9467705 : Blo 2185435 9467705 := bstep (se 2 (by rfl) ⟨3550389, by rfl⟩ : syracuseStep 9467705 = 7100779) B7100779
theorem B6311803 : Blo 2185435 6311803 := bstep (se 1 (by rfl) ⟨4733852, by rfl⟩ : syracuseStep 6311803 = 9467705) B9467705
theorem B8415737 : Blo 2185435 8415737 := bstep (se 2 (by rfl) ⟨3155901, by rfl⟩ : syracuseStep 8415737 = 6311803) B6311803
theorem B5610491 : Blo 2185435 5610491 := bstep (se 1 (by rfl) ⟨4207868, by rfl⟩ : syracuseStep 5610491 = 8415737) B8415737
theorem B3740327 : Blo 2185435 3740327 := bstep (se 1 (by rfl) ⟨2805245, by rfl⟩ : syracuseStep 3740327 = 5610491) B5610491
theorem B2493551 : Blo 2185435 2493551 := bstep (se 1 (by rfl) ⟨1870163, by rfl⟩ : syracuseStep 2493551 = 3740327) B3740327
theorem B6649469 : Blo 2185435 6649469 := bstep (se 3 (by rfl) ⟨1246775, by rfl⟩ : syracuseStep 6649469 = 2493551) B2493551
theorem B4432979 : Blo 2185435 4432979 := bstep (se 1 (by rfl) ⟨3324734, by rfl⟩ : syracuseStep 4432979 = 6649469) B6649469
theorem B11821277 : Blo 2185435 11821277 := bstep (se 3 (by rfl) ⟨2216489, by rfl⟩ : syracuseStep 11821277 = 4432979) B4432979
theorem B7880851 : Blo 2185435 7880851 := bstep (se 1 (by rfl) ⟨5910638, by rfl⟩ : syracuseStep 7880851 = 11821277) B11821277
theorem B10507801 : Blo 2185435 10507801 := bstep (se 2 (by rfl) ⟨3940425, by rfl⟩ : syracuseStep 10507801 = 7880851) B7880851
theorem B14010401 : Blo 2185435 14010401 := bstep (se 2 (by rfl) ⟨5253900, by rfl⟩ : syracuseStep 14010401 = 10507801) B10507801
theorem B9340267 : Blo 2185435 9340267 := bstep (se 1 (by rfl) ⟨7005200, by rfl⟩ : syracuseStep 9340267 = 14010401) B14010401
theorem B12453689 : Blo 2185435 12453689 := bstep (se 2 (by rfl) ⟨4670133, by rfl⟩ : syracuseStep 12453689 = 9340267) B9340267
theorem B8302459 : Blo 2185435 8302459 := bstep (se 1 (by rfl) ⟨6226844, by rfl⟩ : syracuseStep 8302459 = 12453689) B12453689
theorem B11069945 : Blo 2185435 11069945 := bstep (se 2 (by rfl) ⟨4151229, by rfl⟩ : syracuseStep 11069945 = 8302459) B8302459
theorem B7379963 : Blo 2185435 7379963 := bstep (se 1 (by rfl) ⟨5534972, by rfl⟩ : syracuseStep 7379963 = 11069945) B11069945
theorem B4919975 : Blo 2185435 4919975 := bstep (se 1 (by rfl) ⟨3689981, by rfl⟩ : syracuseStep 4919975 = 7379963) B7379963
theorem B3279983 : Blo 2185435 3279983 := bstep (se 1 (by rfl) ⟨2459987, by rfl⟩ : syracuseStep 3279983 = 4919975) B4919975
theorem B2186655 : Blo 2185435 2186655 := bstep (se 1 (by rfl) ⟨1639991, by rfl⟩ : syracuseStep 2186655 = 3279983) B3279983
theorem B3279989 : Blo 2185435 3279989 := bbase (se 5 (by rfl) ⟨153749, by rfl⟩ : syracuseStep 3279989 = 307499) (by norm_num)
theorem B2186659 : Blo 2185435 2186659 := bstep (se 1 (by rfl) ⟨1639994, by rfl⟩ : syracuseStep 2186659 = 3279989) B3279989
theorem B4151245 : Blo 2185435 4151245 := bbase (se 3 (by rfl) ⟨778358, by rfl⟩ : syracuseStep 4151245 = 1556717) (by norm_num)
theorem B5534993 : Blo 2185435 5534993 := bstep (se 2 (by rfl) ⟨2075622, by rfl⟩ : syracuseStep 5534993 = 4151245) B4151245
theorem B3689995 : Blo 2185435 3689995 := bstep (se 1 (by rfl) ⟨2767496, by rfl⟩ : syracuseStep 3689995 = 5534993) B5534993
theorem B4919993 : Blo 2185435 4919993 := bstep (se 2 (by rfl) ⟨1844997, by rfl⟩ : syracuseStep 4919993 = 3689995) B3689995
theorem B3279995 : Blo 2185435 3279995 := bstep (se 1 (by rfl) ⟨2459996, by rfl⟩ : syracuseStep 3279995 = 4919993) B4919993
theorem B2186663 : Blo 2185435 2186663 := bstep (se 1 (by rfl) ⟨1639997, by rfl⟩ : syracuseStep 2186663 = 3279995) B3279995
theorem B2460001 : Blo 2185435 2460001 := bbase (se 2 (by rfl) ⟨922500, by rfl⟩ : syracuseStep 2460001 = 1845001) (by norm_num)
theorem B3280001 : Blo 2185435 3280001 := bstep (se 2 (by rfl) ⟨1230000, by rfl⟩ : syracuseStep 3280001 = 2460001) B2460001
theorem B2186667 : Blo 2185435 2186667 := bstep (se 1 (by rfl) ⟨1640000, by rfl⟩ : syracuseStep 2186667 = 3280001) B3280001
theorem B5535013 : Blo 2185435 5535013 := bbase (se 4 (by rfl) ⟨518907, by rfl⟩ : syracuseStep 5535013 = 1037815) (by norm_num)
theorem B7380017 : Blo 2185435 7380017 := bstep (se 2 (by rfl) ⟨2767506, by rfl⟩ : syracuseStep 7380017 = 5535013) B5535013
theorem B4920011 : Blo 2185435 4920011 := bstep (se 1 (by rfl) ⟨3690008, by rfl⟩ : syracuseStep 4920011 = 7380017) B7380017
theorem B3280007 : Blo 2185435 3280007 := bstep (se 1 (by rfl) ⟨2460005, by rfl⟩ : syracuseStep 3280007 = 4920011) B4920011
theorem B2186671 : Blo 2185435 2186671 := bstep (se 1 (by rfl) ⟨1640003, by rfl⟩ : syracuseStep 2186671 = 3280007) B3280007
theorem B3280013 : Blo 2185435 3280013 := bbase (se 3 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 3280013 = 1230005) (by norm_num)
theorem B2186675 : Blo 2185435 2186675 := bstep (se 1 (by rfl) ⟨1640006, by rfl⟩ : syracuseStep 2186675 = 3280013) B3280013
theorem B4920029 : Blo 2185435 4920029 := bbase (se 3 (by rfl) ⟨922505, by rfl⟩ : syracuseStep 4920029 = 1845011) (by norm_num)
theorem B3280019 : Blo 2185435 3280019 := bstep (se 1 (by rfl) ⟨2460014, by rfl⟩ : syracuseStep 3280019 = 4920029) B4920029
theorem B2186679 : Blo 2185435 2186679 := bstep (se 1 (by rfl) ⟨1640009, by rfl⟩ : syracuseStep 2186679 = 3280019) B3280019
theorem B3690029 : Blo 2185435 3690029 := bbase (se 3 (by rfl) ⟨691880, by rfl⟩ : syracuseStep 3690029 = 1383761) (by norm_num)
theorem B2460019 : Blo 2185435 2460019 := bstep (se 1 (by rfl) ⟨1845014, by rfl⟩ : syracuseStep 2460019 = 3690029) B3690029
theorem B3280025 : Blo 2185435 3280025 := bstep (se 2 (by rfl) ⟨1230009, by rfl⟩ : syracuseStep 3280025 = 2460019) B2460019
theorem B2186683 : Blo 2185435 2186683 := bstep (se 1 (by rfl) ⟨1640012, by rfl⟩ : syracuseStep 2186683 = 3280025) B3280025
theorem B3740381 : Blo 2185435 3740381 := bbase (se 3 (by rfl) ⟨701321, by rfl⟩ : syracuseStep 3740381 = 1402643) (by norm_num)
theorem B2493587 : Blo 2185435 2493587 := bstep (se 1 (by rfl) ⟨1870190, by rfl⟩ : syracuseStep 2493587 = 3740381) B3740381
theorem B6649565 : Blo 2185435 6649565 := bstep (se 3 (by rfl) ⟨1246793, by rfl⟩ : syracuseStep 6649565 = 2493587) B2493587
theorem B70928693 : Blo 2185435 70928693 := bstep (se 5 (by rfl) ⟨3324782, by rfl⟩ : syracuseStep 70928693 = 6649565) B6649565
theorem B47285795 : Blo 2185435 47285795 := bstep (se 1 (by rfl) ⟨35464346, by rfl⟩ : syracuseStep 47285795 = 70928693) B70928693
theorem B31523863 : Blo 2185435 31523863 := bstep (se 1 (by rfl) ⟨23642897, by rfl⟩ : syracuseStep 31523863 = 47285795) B47285795
theorem B42031817 : Blo 2185435 42031817 := bstep (se 2 (by rfl) ⟨15761931, by rfl⟩ : syracuseStep 42031817 = 31523863) B31523863
theorem B28021211 : Blo 2185435 28021211 := bstep (se 1 (by rfl) ⟨21015908, by rfl⟩ : syracuseStep 28021211 = 42031817) B42031817
theorem B18680807 : Blo 2185435 18680807 := bstep (se 1 (by rfl) ⟨14010605, by rfl⟩ : syracuseStep 18680807 = 28021211) B28021211
theorem B12453871 : Blo 2185435 12453871 := bstep (se 1 (by rfl) ⟨9340403, by rfl⟩ : syracuseStep 12453871 = 18680807) B18680807
theorem B16605161 : Blo 2185435 16605161 := bstep (se 2 (by rfl) ⟨6226935, by rfl⟩ : syracuseStep 16605161 = 12453871) B12453871
theorem B11070107 : Blo 2185435 11070107 := bstep (se 1 (by rfl) ⟨8302580, by rfl⟩ : syracuseStep 11070107 = 16605161) B16605161
theorem B7380071 : Blo 2185435 7380071 := bstep (se 1 (by rfl) ⟨5535053, by rfl⟩ : syracuseStep 7380071 = 11070107) B11070107
theorem B4920047 : Blo 2185435 4920047 := bstep (se 1 (by rfl) ⟨3690035, by rfl⟩ : syracuseStep 4920047 = 7380071) B7380071
theorem B3280031 : Blo 2185435 3280031 := bstep (se 1 (by rfl) ⟨2460023, by rfl⟩ : syracuseStep 3280031 = 4920047) B4920047
theorem B2186687 : Blo 2185435 2186687 := bstep (se 1 (by rfl) ⟨1640015, by rfl⟩ : syracuseStep 2186687 = 3280031) B3280031
theorem B3280037 : Blo 2185435 3280037 := bbase (se 4 (by rfl) ⟨307503, by rfl⟩ : syracuseStep 3280037 = 615007) (by norm_num)
theorem B2186691 : Blo 2185435 2186691 := bstep (se 1 (by rfl) ⟨1640018, by rfl⟩ : syracuseStep 2186691 = 3280037) B3280037
theorem B2767537 : Blo 2185435 2767537 := bbase (se 2 (by rfl) ⟨1037826, by rfl⟩ : syracuseStep 2767537 = 2075653) (by norm_num)
theorem B3690049 : Blo 2185435 3690049 := bstep (se 2 (by rfl) ⟨1383768, by rfl⟩ : syracuseStep 3690049 = 2767537) B2767537
theorem B4920065 : Blo 2185435 4920065 := bstep (se 2 (by rfl) ⟨1845024, by rfl⟩ : syracuseStep 4920065 = 3690049) B3690049
theorem B3280043 : Blo 2185435 3280043 := bstep (se 1 (by rfl) ⟨2460032, by rfl⟩ : syracuseStep 3280043 = 4920065) B4920065
theorem B2186695 : Blo 2185435 2186695 := bstep (se 1 (by rfl) ⟨1640021, by rfl⟩ : syracuseStep 2186695 = 3280043) B3280043
theorem B2460037 : Blo 2185435 2460037 := bbase (se 4 (by rfl) ⟨230628, by rfl⟩ : syracuseStep 2460037 = 461257) (by norm_num)
theorem B3280049 : Blo 2185435 3280049 := bstep (se 2 (by rfl) ⟨1230018, by rfl⟩ : syracuseStep 3280049 = 2460037) B2460037
theorem B2186699 : Blo 2185435 2186699 := bstep (se 1 (by rfl) ⟨1640024, by rfl⟩ : syracuseStep 2186699 = 3280049) B3280049
theorem B4670237 : Blo 2185435 4670237 := bbase (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) (by norm_num)
theorem B3113491 : Blo 2185435 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B4151321 : Blo 2185435 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B2767547 : Blo 2185435 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B7380125 : Blo 2185435 7380125 := bstep (se 3 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 7380125 = 2767547) B2767547
theorem B4920083 : Blo 2185435 4920083 := bstep (se 1 (by rfl) ⟨3690062, by rfl⟩ : syracuseStep 4920083 = 7380125) B7380125
theorem B3280055 : Blo 2185435 3280055 := bstep (se 1 (by rfl) ⟨2460041, by rfl⟩ : syracuseStep 3280055 = 4920083) B4920083
theorem B2186703 : Blo 2185435 2186703 := bstep (se 1 (by rfl) ⟨1640027, by rfl⟩ : syracuseStep 2186703 = 3280055) B3280055
theorem B3280061 : Blo 2185435 3280061 := bbase (se 3 (by rfl) ⟨615011, by rfl⟩ : syracuseStep 3280061 = 1230023) (by norm_num)
theorem B2186707 : Blo 2185435 2186707 := bstep (se 1 (by rfl) ⟨1640030, by rfl⟩ : syracuseStep 2186707 = 3280061) B3280061
theorem B4920101 : Blo 2185435 4920101 := bbase (se 4 (by rfl) ⟨461259, by rfl⟩ : syracuseStep 4920101 = 922519) (by norm_num)
theorem B3280067 : Blo 2185435 3280067 := bstep (se 1 (by rfl) ⟨2460050, by rfl⟩ : syracuseStep 3280067 = 4920101) B4920101
theorem B2186711 : Blo 2185435 2186711 := bstep (se 1 (by rfl) ⟨1640033, by rfl⟩ : syracuseStep 2186711 = 3280067) B3280067
theorem B5535125 : Blo 2185435 5535125 := bbase (se 6 (by rfl) ⟨129729, by rfl⟩ : syracuseStep 5535125 = 259459) (by norm_num)
theorem B3690083 : Blo 2185435 3690083 := bstep (se 1 (by rfl) ⟨2767562, by rfl⟩ : syracuseStep 3690083 = 5535125) B5535125
theorem B2460055 : Blo 2185435 2460055 := bstep (se 1 (by rfl) ⟨1845041, by rfl⟩ : syracuseStep 2460055 = 3690083) B3690083
theorem B3280073 : Blo 2185435 3280073 := bstep (se 2 (by rfl) ⟨1230027, by rfl⟩ : syracuseStep 3280073 = 2460055) B2460055
theorem B2186715 : Blo 2185435 2186715 := bstep (se 1 (by rfl) ⟨1640036, by rfl⟩ : syracuseStep 2186715 = 3280073) B3280073
theorem B15165877 : Blo 2185435 15165877 := bbase (se 5 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 15165877 = 1421801) (by norm_num)
theorem B20221169 : Blo 2185435 20221169 := bstep (se 2 (by rfl) ⟨7582938, by rfl⟩ : syracuseStep 20221169 = 15165877) B15165877
theorem B53923117 : Blo 2185435 53923117 := bstep (se 3 (by rfl) ⟨10110584, by rfl⟩ : syracuseStep 53923117 = 20221169) B20221169
theorem B71897489 : Blo 2185435 71897489 := bstep (se 2 (by rfl) ⟨26961558, by rfl⟩ : syracuseStep 71897489 = 53923117) B53923117
theorem B47931659 : Blo 2185435 47931659 := bstep (se 1 (by rfl) ⟨35948744, by rfl⟩ : syracuseStep 47931659 = 71897489) B71897489
theorem B31954439 : Blo 2185435 31954439 := bstep (se 1 (by rfl) ⟨23965829, by rfl⟩ : syracuseStep 31954439 = 47931659) B47931659
theorem B21302959 : Blo 2185435 21302959 := bstep (se 1 (by rfl) ⟨15977219, by rfl⟩ : syracuseStep 21302959 = 31954439) B31954439
theorem B28403945 : Blo 2185435 28403945 := bstep (se 2 (by rfl) ⟨10651479, by rfl⟩ : syracuseStep 28403945 = 21302959) B21302959
theorem B18935963 : Blo 2185435 18935963 := bstep (se 1 (by rfl) ⟨14201972, by rfl⟩ : syracuseStep 18935963 = 28403945) B28403945
theorem B12623975 : Blo 2185435 12623975 := bstep (se 1 (by rfl) ⟨9467981, by rfl⟩ : syracuseStep 12623975 = 18935963) B18935963
theorem B8415983 : Blo 2185435 8415983 := bstep (se 1 (by rfl) ⟨6311987, by rfl⟩ : syracuseStep 8415983 = 12623975) B12623975
theorem B5610655 : Blo 2185435 5610655 := bstep (se 1 (by rfl) ⟨4207991, by rfl⟩ : syracuseStep 5610655 = 8415983) B8415983
theorem B7480873 : Blo 2185435 7480873 := bstep (se 2 (by rfl) ⟨2805327, by rfl⟩ : syracuseStep 7480873 = 5610655) B5610655
theorem B9974497 : Blo 2185435 9974497 := bstep (se 2 (by rfl) ⟨3740436, by rfl⟩ : syracuseStep 9974497 = 7480873) B7480873
theorem B13299329 : Blo 2185435 13299329 := bstep (se 2 (by rfl) ⟨4987248, by rfl⟩ : syracuseStep 13299329 = 9974497) B9974497
theorem B8866219 : Blo 2185435 8866219 := bstep (se 1 (by rfl) ⟨6649664, by rfl⟩ : syracuseStep 8866219 = 13299329) B13299329
theorem B11821625 : Blo 2185435 11821625 := bstep (se 2 (by rfl) ⟨4433109, by rfl⟩ : syracuseStep 11821625 = 8866219) B8866219
theorem B7881083 : Blo 2185435 7881083 := bstep (se 1 (by rfl) ⟨5910812, by rfl⟩ : syracuseStep 7881083 = 11821625) B11821625
theorem B5254055 : Blo 2185435 5254055 := bstep (se 1 (by rfl) ⟨3940541, by rfl⟩ : syracuseStep 5254055 = 7881083) B7881083
theorem B3502703 : Blo 2185435 3502703 := bstep (se 1 (by rfl) ⟨2627027, by rfl⟩ : syracuseStep 3502703 = 5254055) B5254055
theorem B9340541 : Blo 2185435 9340541 := bstep (se 3 (by rfl) ⟨1751351, by rfl⟩ : syracuseStep 9340541 = 3502703) B3502703
theorem B6227027 : Blo 2185435 6227027 := bstep (se 1 (by rfl) ⟨4670270, by rfl⟩ : syracuseStep 6227027 = 9340541) B9340541
theorem B4151351 : Blo 2185435 4151351 := bstep (se 1 (by rfl) ⟨3113513, by rfl⟩ : syracuseStep 4151351 = 6227027) B6227027
theorem B11070269 : Blo 2185435 11070269 := bstep (se 3 (by rfl) ⟨2075675, by rfl⟩ : syracuseStep 11070269 = 4151351) B4151351
theorem B7380179 : Blo 2185435 7380179 := bstep (se 1 (by rfl) ⟨5535134, by rfl⟩ : syracuseStep 7380179 = 11070269) B11070269
theorem B4920119 : Blo 2185435 4920119 := bstep (se 1 (by rfl) ⟨3690089, by rfl⟩ : syracuseStep 4920119 = 7380179) B7380179
theorem B3280079 : Blo 2185435 3280079 := bstep (se 1 (by rfl) ⟨2460059, by rfl⟩ : syracuseStep 3280079 = 4920119) B4920119
theorem B2186719 : Blo 2185435 2186719 := bstep (se 1 (by rfl) ⟨1640039, by rfl⟩ : syracuseStep 2186719 = 3280079) B3280079
theorem B3280085 : Blo 2185435 3280085 := bbase (se 7 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 3280085 = 76877) (by norm_num)
theorem B2186723 : Blo 2185435 2186723 := bstep (se 1 (by rfl) ⟨1640042, by rfl⟩ : syracuseStep 2186723 = 3280085) B3280085
theorem B3113525 : Blo 2185435 3113525 := bbase (se 5 (by rfl) ⟨145946, by rfl⟩ : syracuseStep 3113525 = 291893) (by norm_num)
theorem B8302733 : Blo 2185435 8302733 := bstep (se 3 (by rfl) ⟨1556762, by rfl⟩ : syracuseStep 8302733 = 3113525) B3113525
theorem B5535155 : Blo 2185435 5535155 := bstep (se 1 (by rfl) ⟨4151366, by rfl⟩ : syracuseStep 5535155 = 8302733) B8302733
theorem B3690103 : Blo 2185435 3690103 := bstep (se 1 (by rfl) ⟨2767577, by rfl⟩ : syracuseStep 3690103 = 5535155) B5535155
theorem B4920137 : Blo 2185435 4920137 := bstep (se 2 (by rfl) ⟨1845051, by rfl⟩ : syracuseStep 4920137 = 3690103) B3690103
theorem B3280091 : Blo 2185435 3280091 := bstep (se 1 (by rfl) ⟨2460068, by rfl⟩ : syracuseStep 3280091 = 4920137) B4920137
theorem B2186727 : Blo 2185435 2186727 := bstep (se 1 (by rfl) ⟨1640045, by rfl⟩ : syracuseStep 2186727 = 3280091) B3280091
theorem B2460073 : Blo 2185435 2460073 := bbase (se 2 (by rfl) ⟨922527, by rfl⟩ : syracuseStep 2460073 = 1845055) (by norm_num)
theorem B3280097 : Blo 2185435 3280097 := bstep (se 2 (by rfl) ⟨1230036, by rfl⟩ : syracuseStep 3280097 = 2460073) B2460073
theorem B2186731 : Blo 2185435 2186731 := bstep (se 1 (by rfl) ⟨1640048, by rfl⟩ : syracuseStep 2186731 = 3280097) B3280097
theorem B5254093 : Blo 2185435 5254093 := bbase (se 3 (by rfl) ⟨985142, by rfl⟩ : syracuseStep 5254093 = 1970285) (by norm_num)
theorem B7005457 : Blo 2185435 7005457 := bstep (se 2 (by rfl) ⟨2627046, by rfl⟩ : syracuseStep 7005457 = 5254093) B5254093
theorem B9340609 : Blo 2185435 9340609 := bstep (se 2 (by rfl) ⟨3502728, by rfl⟩ : syracuseStep 9340609 = 7005457) B7005457
theorem B12454145 : Blo 2185435 12454145 := bstep (se 2 (by rfl) ⟨4670304, by rfl⟩ : syracuseStep 12454145 = 9340609) B9340609
theorem B8302763 : Blo 2185435 8302763 := bstep (se 1 (by rfl) ⟨6227072, by rfl⟩ : syracuseStep 8302763 = 12454145) B12454145
theorem B5535175 : Blo 2185435 5535175 := bstep (se 1 (by rfl) ⟨4151381, by rfl⟩ : syracuseStep 5535175 = 8302763) B8302763
theorem B7380233 : Blo 2185435 7380233 := bstep (se 2 (by rfl) ⟨2767587, by rfl⟩ : syracuseStep 7380233 = 5535175) B5535175
theorem B4920155 : Blo 2185435 4920155 := bstep (se 1 (by rfl) ⟨3690116, by rfl⟩ : syracuseStep 4920155 = 7380233) B7380233
theorem B3280103 : Blo 2185435 3280103 := bstep (se 1 (by rfl) ⟨2460077, by rfl⟩ : syracuseStep 3280103 = 4920155) B4920155
theorem B2186735 : Blo 2185435 2186735 := bstep (se 1 (by rfl) ⟨1640051, by rfl⟩ : syracuseStep 2186735 = 3280103) B3280103
theorem B3280109 : Blo 2185435 3280109 := bbase (se 3 (by rfl) ⟨615020, by rfl⟩ : syracuseStep 3280109 = 1230041) (by norm_num)
theorem B2186739 : Blo 2185435 2186739 := bstep (se 1 (by rfl) ⟨1640054, by rfl⟩ : syracuseStep 2186739 = 3280109) B3280109
theorem B4920173 : Blo 2185435 4920173 := bbase (se 3 (by rfl) ⟨922532, by rfl⟩ : syracuseStep 4920173 = 1845065) (by norm_num)
theorem B3280115 : Blo 2185435 3280115 := bstep (se 1 (by rfl) ⟨2460086, by rfl⟩ : syracuseStep 3280115 = 4920173) B4920173
theorem B2186743 : Blo 2185435 2186743 := bstep (se 1 (by rfl) ⟨1640057, by rfl⟩ : syracuseStep 2186743 = 3280115) B3280115
theorem B4151405 : Blo 2185435 4151405 := bbase (se 3 (by rfl) ⟨778388, by rfl⟩ : syracuseStep 4151405 = 1556777) (by norm_num)
theorem B2767603 : Blo 2185435 2767603 := bstep (se 1 (by rfl) ⟨2075702, by rfl⟩ : syracuseStep 2767603 = 4151405) B4151405
theorem B3690137 : Blo 2185435 3690137 := bstep (se 2 (by rfl) ⟨1383801, by rfl⟩ : syracuseStep 3690137 = 2767603) B2767603
theorem B2460091 : Blo 2185435 2460091 := bstep (se 1 (by rfl) ⟨1845068, by rfl⟩ : syracuseStep 2460091 = 3690137) B3690137
theorem B3280121 : Blo 2185435 3280121 := bstep (se 2 (by rfl) ⟨1230045, by rfl⟩ : syracuseStep 3280121 = 2460091) B2460091
theorem B2186747 : Blo 2185435 2186747 := bstep (se 1 (by rfl) ⟨1640060, by rfl⟩ : syracuseStep 2186747 = 3280121) B3280121
theorem B4433173 : Blo 2185435 4433173 := bbase (se 6 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 4433173 = 207805) (by norm_num)
theorem B23643589 : Blo 2185435 23643589 := bstep (se 4 (by rfl) ⟨2216586, by rfl⟩ : syracuseStep 23643589 = 4433173) B4433173
theorem B31524785 : Blo 2185435 31524785 := bstep (se 2 (by rfl) ⟨11821794, by rfl⟩ : syracuseStep 31524785 = 23643589) B23643589
theorem B21016523 : Blo 2185435 21016523 := bstep (se 1 (by rfl) ⟨15762392, by rfl⟩ : syracuseStep 21016523 = 31524785) B31524785
theorem B56044061 : Blo 2185435 56044061 := bstep (se 3 (by rfl) ⟨10508261, by rfl⟩ : syracuseStep 56044061 = 21016523) B21016523
theorem B37362707 : Blo 2185435 37362707 := bstep (se 1 (by rfl) ⟨28022030, by rfl⟩ : syracuseStep 37362707 = 56044061) B56044061
theorem B24908471 : Blo 2185435 24908471 := bstep (se 1 (by rfl) ⟨18681353, by rfl⟩ : syracuseStep 24908471 = 37362707) B37362707
theorem B16605647 : Blo 2185435 16605647 := bstep (se 1 (by rfl) ⟨12454235, by rfl⟩ : syracuseStep 16605647 = 24908471) B24908471
theorem B11070431 : Blo 2185435 11070431 := bstep (se 1 (by rfl) ⟨8302823, by rfl⟩ : syracuseStep 11070431 = 16605647) B16605647
theorem B7380287 : Blo 2185435 7380287 := bstep (se 1 (by rfl) ⟨5535215, by rfl⟩ : syracuseStep 7380287 = 11070431) B11070431
theorem B4920191 : Blo 2185435 4920191 := bstep (se 1 (by rfl) ⟨3690143, by rfl⟩ : syracuseStep 4920191 = 7380287) B7380287
theorem B3280127 : Blo 2185435 3280127 := bstep (se 1 (by rfl) ⟨2460095, by rfl⟩ : syracuseStep 3280127 = 4920191) B4920191
theorem B2186751 : Blo 2185435 2186751 := bstep (se 1 (by rfl) ⟨1640063, by rfl⟩ : syracuseStep 2186751 = 3280127) B3280127
theorem B3280133 : Blo 2185435 3280133 := bbase (se 4 (by rfl) ⟨307512, by rfl⟩ : syracuseStep 3280133 = 615025) (by norm_num)
theorem B2186755 : Blo 2185435 2186755 := bstep (se 1 (by rfl) ⟨1640066, by rfl⟩ : syracuseStep 2186755 = 3280133) B3280133
theorem B3690157 : Blo 2185435 3690157 := bbase (se 3 (by rfl) ⟨691904, by rfl⟩ : syracuseStep 3690157 = 1383809) (by norm_num)
theorem B4920209 : Blo 2185435 4920209 := bstep (se 2 (by rfl) ⟨1845078, by rfl⟩ : syracuseStep 4920209 = 3690157) B3690157
theorem B3280139 : Blo 2185435 3280139 := bstep (se 1 (by rfl) ⟨2460104, by rfl⟩ : syracuseStep 3280139 = 4920209) B4920209
theorem B2186759 : Blo 2185435 2186759 := bstep (se 1 (by rfl) ⟨1640069, by rfl⟩ : syracuseStep 2186759 = 3280139) B3280139
theorem B2460109 : Blo 2185435 2460109 := bbase (se 3 (by rfl) ⟨461270, by rfl⟩ : syracuseStep 2460109 = 922541) (by norm_num)
theorem B3280145 : Blo 2185435 3280145 := bstep (se 2 (by rfl) ⟨1230054, by rfl⟩ : syracuseStep 3280145 = 2460109) B2460109
theorem B2186763 : Blo 2185435 2186763 := bstep (se 1 (by rfl) ⟨1640072, by rfl⟩ : syracuseStep 2186763 = 3280145) B3280145
theorem B7380341 : Blo 2185435 7380341 := bbase (se 5 (by rfl) ⟨345953, by rfl⟩ : syracuseStep 7380341 = 691907) (by norm_num)
theorem B4920227 : Blo 2185435 4920227 := bstep (se 1 (by rfl) ⟨3690170, by rfl⟩ : syracuseStep 4920227 = 7380341) B7380341
theorem B3280151 : Blo 2185435 3280151 := bstep (se 1 (by rfl) ⟨2460113, by rfl⟩ : syracuseStep 3280151 = 4920227) B4920227
theorem B2186767 : Blo 2185435 2186767 := bstep (se 1 (by rfl) ⟨1640075, by rfl⟩ : syracuseStep 2186767 = 3280151) B3280151
theorem B3280157 : Blo 2185435 3280157 := bbase (se 3 (by rfl) ⟨615029, by rfl⟩ : syracuseStep 3280157 = 1230059) (by norm_num)
theorem B2186771 : Blo 2185435 2186771 := bstep (se 1 (by rfl) ⟨1640078, by rfl⟩ : syracuseStep 2186771 = 3280157) B3280157
theorem B4920245 : Blo 2185435 4920245 := bbase (se 5 (by rfl) ⟨230636, by rfl⟩ : syracuseStep 4920245 = 461273) (by norm_num)
theorem B3280163 : Blo 2185435 3280163 := bstep (se 1 (by rfl) ⟨2460122, by rfl⟩ : syracuseStep 3280163 = 4920245) B4920245
theorem B2186775 : Blo 2185435 2186775 := bstep (se 1 (by rfl) ⟨1640081, by rfl⟩ : syracuseStep 2186775 = 3280163) B3280163
theorem B2736101 : Blo 2185435 2736101 := bbase (se 4 (by rfl) ⟨256509, by rfl⟩ : syracuseStep 2736101 = 513019) (by norm_num)
theorem B7296269 : Blo 2185435 7296269 := bstep (se 3 (by rfl) ⟨1368050, by rfl⟩ : syracuseStep 7296269 = 2736101) B2736101
theorem B19456717 : Blo 2185435 19456717 := bstep (se 3 (by rfl) ⟨3648134, by rfl⟩ : syracuseStep 19456717 = 7296269) B7296269
theorem B25942289 : Blo 2185435 25942289 := bstep (se 2 (by rfl) ⟨9728358, by rfl⟩ : syracuseStep 25942289 = 19456717) B19456717
theorem B69179437 : Blo 2185435 69179437 := bstep (se 3 (by rfl) ⟨12971144, by rfl⟩ : syracuseStep 69179437 = 25942289) B25942289
theorem B92239249 : Blo 2185435 92239249 := bstep (se 2 (by rfl) ⟨34589718, by rfl⟩ : syracuseStep 92239249 = 69179437) B69179437
theorem B122985665 : Blo 2185435 122985665 := bstep (se 2 (by rfl) ⟨46119624, by rfl⟩ : syracuseStep 122985665 = 92239249) B92239249
theorem B81990443 : Blo 2185435 81990443 := bstep (se 1 (by rfl) ⟨61492832, by rfl⟩ : syracuseStep 81990443 = 122985665) B122985665
theorem B54660295 : Blo 2185435 54660295 := bstep (se 1 (by rfl) ⟨40995221, by rfl⟩ : syracuseStep 54660295 = 81990443) B81990443
theorem B72880393 : Blo 2185435 72880393 := bstep (se 2 (by rfl) ⟨27330147, by rfl⟩ : syracuseStep 72880393 = 54660295) B54660295
theorem B97173857 : Blo 2185435 97173857 := bstep (se 2 (by rfl) ⟨36440196, by rfl⟩ : syracuseStep 97173857 = 72880393) B72880393
theorem B259130285 : Blo 2185435 259130285 := bstep (se 3 (by rfl) ⟨48586928, by rfl⟩ : syracuseStep 259130285 = 97173857) B97173857
theorem B172753523 : Blo 2185435 172753523 := bstep (se 1 (by rfl) ⟨129565142, by rfl⟩ : syracuseStep 172753523 = 259130285) B259130285
theorem B115169015 : Blo 2185435 115169015 := bstep (se 1 (by rfl) ⟨86376761, by rfl⟩ : syracuseStep 115169015 = 172753523) B172753523
theorem B76779343 : Blo 2185435 76779343 := bstep (se 1 (by rfl) ⟨57584507, by rfl⟩ : syracuseStep 76779343 = 115169015) B115169015
theorem B102372457 : Blo 2185435 102372457 := bstep (se 2 (by rfl) ⟨38389671, by rfl⟩ : syracuseStep 102372457 = 76779343) B76779343
theorem B136496609 : Blo 2185435 136496609 := bstep (se 2 (by rfl) ⟨51186228, by rfl⟩ : syracuseStep 136496609 = 102372457) B102372457
theorem B90997739 : Blo 2185435 90997739 := bstep (se 1 (by rfl) ⟨68248304, by rfl⟩ : syracuseStep 90997739 = 136496609) B136496609
theorem B60665159 : Blo 2185435 60665159 := bstep (se 1 (by rfl) ⟨45498869, by rfl⟩ : syracuseStep 60665159 = 90997739) B90997739
theorem B161773757 : Blo 2185435 161773757 := bstep (se 3 (by rfl) ⟨30332579, by rfl⟩ : syracuseStep 161773757 = 60665159) B60665159
theorem B107849171 : Blo 2185435 107849171 := bstep (se 1 (by rfl) ⟨80886878, by rfl⟩ : syracuseStep 107849171 = 161773757) B161773757
theorem B71899447 : Blo 2185435 71899447 := bstep (se 1 (by rfl) ⟨53924585, by rfl⟩ : syracuseStep 71899447 = 107849171) B107849171
theorem B95865929 : Blo 2185435 95865929 := bstep (se 2 (by rfl) ⟨35949723, by rfl⟩ : syracuseStep 95865929 = 71899447) B71899447
theorem B63910619 : Blo 2185435 63910619 := bstep (se 1 (by rfl) ⟨47932964, by rfl⟩ : syracuseStep 63910619 = 95865929) B95865929
theorem B42607079 : Blo 2185435 42607079 := bstep (se 1 (by rfl) ⟨31955309, by rfl⟩ : syracuseStep 42607079 = 63910619) B63910619
theorem B28404719 : Blo 2185435 28404719 := bstep (se 1 (by rfl) ⟨21303539, by rfl⟩ : syracuseStep 28404719 = 42607079) B42607079
theorem B18936479 : Blo 2185435 18936479 := bstep (se 1 (by rfl) ⟨14202359, by rfl⟩ : syracuseStep 18936479 = 28404719) B28404719
theorem B12624319 : Blo 2185435 12624319 := bstep (se 1 (by rfl) ⟨9468239, by rfl⟩ : syracuseStep 12624319 = 18936479) B18936479
theorem B67329701 : Blo 2185435 67329701 := bstep (se 4 (by rfl) ⟨6312159, by rfl⟩ : syracuseStep 67329701 = 12624319) B12624319
theorem B44886467 : Blo 2185435 44886467 := bstep (se 1 (by rfl) ⟨33664850, by rfl⟩ : syracuseStep 44886467 = 67329701) B67329701
theorem B29924311 : Blo 2185435 29924311 := bstep (se 1 (by rfl) ⟨22443233, by rfl⟩ : syracuseStep 29924311 = 44886467) B44886467
theorem B39899081 : Blo 2185435 39899081 := bstep (se 2 (by rfl) ⟨14962155, by rfl⟩ : syracuseStep 39899081 = 29924311) B29924311
theorem B26599387 : Blo 2185435 26599387 := bstep (se 1 (by rfl) ⟨19949540, by rfl⟩ : syracuseStep 26599387 = 39899081) B39899081
theorem B35465849 : Blo 2185435 35465849 := bstep (se 2 (by rfl) ⟨13299693, by rfl⟩ : syracuseStep 35465849 = 26599387) B26599387
theorem B23643899 : Blo 2185435 23643899 := bstep (se 1 (by rfl) ⟨17732924, by rfl⟩ : syracuseStep 23643899 = 35465849) B35465849
theorem B15762599 : Blo 2185435 15762599 := bstep (se 1 (by rfl) ⟨11821949, by rfl⟩ : syracuseStep 15762599 = 23643899) B23643899
theorem B10508399 : Blo 2185435 10508399 := bstep (se 1 (by rfl) ⟨7881299, by rfl⟩ : syracuseStep 10508399 = 15762599) B15762599
theorem B7005599 : Blo 2185435 7005599 := bstep (se 1 (by rfl) ⟨5254199, by rfl⟩ : syracuseStep 7005599 = 10508399) B10508399
theorem B4670399 : Blo 2185435 4670399 := bstep (se 1 (by rfl) ⟨3502799, by rfl⟩ : syracuseStep 4670399 = 7005599) B7005599
theorem B12454397 : Blo 2185435 12454397 := bstep (se 3 (by rfl) ⟨2335199, by rfl⟩ : syracuseStep 12454397 = 4670399) B4670399
theorem B8302931 : Blo 2185435 8302931 := bstep (se 1 (by rfl) ⟨6227198, by rfl⟩ : syracuseStep 8302931 = 12454397) B12454397
theorem B5535287 : Blo 2185435 5535287 := bstep (se 1 (by rfl) ⟨4151465, by rfl⟩ : syracuseStep 5535287 = 8302931) B8302931
theorem B3690191 : Blo 2185435 3690191 := bstep (se 1 (by rfl) ⟨2767643, by rfl⟩ : syracuseStep 3690191 = 5535287) B5535287
theorem B2460127 : Blo 2185435 2460127 := bstep (se 1 (by rfl) ⟨1845095, by rfl⟩ : syracuseStep 2460127 = 3690191) B3690191
theorem B3280169 : Blo 2185435 3280169 := bstep (se 2 (by rfl) ⟨1230063, by rfl⟩ : syracuseStep 3280169 = 2460127) B2460127
theorem B2186779 : Blo 2185435 2186779 := bstep (se 1 (by rfl) ⟨1640084, by rfl⟩ : syracuseStep 2186779 = 3280169) B3280169
theorem B9974789 : Blo 2185435 9974789 := bbase (se 4 (by rfl) ⟨935136, by rfl⟩ : syracuseStep 9974789 = 1870273) (by norm_num)
theorem B6649859 : Blo 2185435 6649859 := bstep (se 1 (by rfl) ⟨4987394, by rfl⟩ : syracuseStep 6649859 = 9974789) B9974789
theorem B4433239 : Blo 2185435 4433239 := bstep (se 1 (by rfl) ⟨3324929, by rfl⟩ : syracuseStep 4433239 = 6649859) B6649859
theorem B5910985 : Blo 2185435 5910985 := bstep (se 2 (by rfl) ⟨2216619, by rfl⟩ : syracuseStep 5910985 = 4433239) B4433239
theorem B7881313 : Blo 2185435 7881313 := bstep (se 2 (by rfl) ⟨2955492, by rfl⟩ : syracuseStep 7881313 = 5910985) B5910985
theorem B10508417 : Blo 2185435 10508417 := bstep (se 2 (by rfl) ⟨3940656, by rfl⟩ : syracuseStep 10508417 = 7881313) B7881313
theorem B7005611 : Blo 2185435 7005611 := bstep (se 1 (by rfl) ⟨5254208, by rfl⟩ : syracuseStep 7005611 = 10508417) B10508417
theorem B4670407 : Blo 2185435 4670407 := bstep (se 1 (by rfl) ⟨3502805, by rfl⟩ : syracuseStep 4670407 = 7005611) B7005611
theorem B6227209 : Blo 2185435 6227209 := bstep (se 2 (by rfl) ⟨2335203, by rfl⟩ : syracuseStep 6227209 = 4670407) B4670407
theorem B8302945 : Blo 2185435 8302945 := bstep (se 2 (by rfl) ⟨3113604, by rfl⟩ : syracuseStep 8302945 = 6227209) B6227209
theorem B11070593 : Blo 2185435 11070593 := bstep (se 2 (by rfl) ⟨4151472, by rfl⟩ : syracuseStep 11070593 = 8302945) B8302945
theorem B7380395 : Blo 2185435 7380395 := bstep (se 1 (by rfl) ⟨5535296, by rfl⟩ : syracuseStep 7380395 = 11070593) B11070593
theorem B4920263 : Blo 2185435 4920263 := bstep (se 1 (by rfl) ⟨3690197, by rfl⟩ : syracuseStep 4920263 = 7380395) B7380395
theorem B3280175 : Blo 2185435 3280175 := bstep (se 1 (by rfl) ⟨2460131, by rfl⟩ : syracuseStep 3280175 = 4920263) B4920263
theorem B2186783 : Blo 2185435 2186783 := bstep (se 1 (by rfl) ⟨1640087, by rfl⟩ : syracuseStep 2186783 = 3280175) B3280175
theorem B3280181 : Blo 2185435 3280181 := bbase (se 5 (by rfl) ⟨153758, by rfl⟩ : syracuseStep 3280181 = 307517) (by norm_num)
theorem B2186787 : Blo 2185435 2186787 := bstep (se 1 (by rfl) ⟨1640090, by rfl⟩ : syracuseStep 2186787 = 3280181) B3280181
theorem B5535317 : Blo 2185435 5535317 := bbase (se 8 (by rfl) ⟨32433, by rfl⟩ : syracuseStep 5535317 = 64867) (by norm_num)
theorem B3690211 : Blo 2185435 3690211 := bstep (se 1 (by rfl) ⟨2767658, by rfl⟩ : syracuseStep 3690211 = 5535317) B5535317
theorem B4920281 : Blo 2185435 4920281 := bstep (se 2 (by rfl) ⟨1845105, by rfl⟩ : syracuseStep 4920281 = 3690211) B3690211
theorem B3280187 : Blo 2185435 3280187 := bstep (se 1 (by rfl) ⟨2460140, by rfl⟩ : syracuseStep 3280187 = 4920281) B4920281
theorem B2186791 : Blo 2185435 2186791 := bstep (se 1 (by rfl) ⟨1640093, by rfl⟩ : syracuseStep 2186791 = 3280187) B3280187
theorem B2460145 : Blo 2185435 2460145 := bbase (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) (by norm_num)
theorem B3280193 : Blo 2185435 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B2186795 : Blo 2185435 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B7686677 : Blo 2185435 7686677 := bbase (se 6 (by rfl) ⟨180156, by rfl⟩ : syracuseStep 7686677 = 360313) (by norm_num)
theorem B20497805 : Blo 2185435 20497805 := bstep (se 3 (by rfl) ⟨3843338, by rfl⟩ : syracuseStep 20497805 = 7686677) B7686677
theorem B13665203 : Blo 2185435 13665203 := bstep (se 1 (by rfl) ⟨10248902, by rfl⟩ : syracuseStep 13665203 = 20497805) B20497805
theorem B9110135 : Blo 2185435 9110135 := bstep (se 1 (by rfl) ⟨6832601, by rfl⟩ : syracuseStep 9110135 = 13665203) B13665203
theorem B6073423 : Blo 2185435 6073423 := bstep (se 1 (by rfl) ⟨4555067, by rfl⟩ : syracuseStep 6073423 = 9110135) B9110135
theorem B32391589 : Blo 2185435 32391589 := bstep (se 4 (by rfl) ⟨3036711, by rfl⟩ : syracuseStep 32391589 = 6073423) B6073423
theorem B43188785 : Blo 2185435 43188785 := bstep (se 2 (by rfl) ⟨16195794, by rfl⟩ : syracuseStep 43188785 = 32391589) B32391589
theorem B28792523 : Blo 2185435 28792523 := bstep (se 1 (by rfl) ⟨21594392, by rfl⟩ : syracuseStep 28792523 = 43188785) B43188785
theorem B19195015 : Blo 2185435 19195015 := bstep (se 1 (by rfl) ⟨14396261, by rfl⟩ : syracuseStep 19195015 = 28792523) B28792523
theorem B25593353 : Blo 2185435 25593353 := bstep (se 2 (by rfl) ⟨9597507, by rfl⟩ : syracuseStep 25593353 = 19195015) B19195015
theorem B17062235 : Blo 2185435 17062235 := bstep (se 1 (by rfl) ⟨12796676, by rfl⟩ : syracuseStep 17062235 = 25593353) B25593353
theorem B11374823 : Blo 2185435 11374823 := bstep (se 1 (by rfl) ⟨8531117, by rfl⟩ : syracuseStep 11374823 = 17062235) B17062235
theorem B7583215 : Blo 2185435 7583215 := bstep (se 1 (by rfl) ⟨5687411, by rfl⟩ : syracuseStep 7583215 = 11374823) B11374823
theorem B10110953 : Blo 2185435 10110953 := bstep (se 2 (by rfl) ⟨3791607, by rfl⟩ : syracuseStep 10110953 = 7583215) B7583215
theorem B26962541 : Blo 2185435 26962541 := bstep (se 3 (by rfl) ⟨5055476, by rfl⟩ : syracuseStep 26962541 = 10110953) B10110953
theorem B17975027 : Blo 2185435 17975027 := bstep (se 1 (by rfl) ⟨13481270, by rfl⟩ : syracuseStep 17975027 = 26962541) B26962541
theorem B11983351 : Blo 2185435 11983351 := bstep (se 1 (by rfl) ⟨8987513, by rfl⟩ : syracuseStep 11983351 = 17975027) B17975027
theorem B15977801 : Blo 2185435 15977801 := bstep (se 2 (by rfl) ⟨5991675, by rfl⟩ : syracuseStep 15977801 = 11983351) B11983351
theorem B10651867 : Blo 2185435 10651867 := bstep (se 1 (by rfl) ⟨7988900, by rfl⟩ : syracuseStep 10651867 = 15977801) B15977801
theorem B56809957 : Blo 2185435 56809957 := bstep (se 4 (by rfl) ⟨5325933, by rfl⟩ : syracuseStep 56809957 = 10651867) B10651867
theorem B75746609 : Blo 2185435 75746609 := bstep (se 2 (by rfl) ⟨28404978, by rfl⟩ : syracuseStep 75746609 = 56809957) B56809957
theorem B50497739 : Blo 2185435 50497739 := bstep (se 1 (by rfl) ⟨37873304, by rfl⟩ : syracuseStep 50497739 = 75746609) B75746609
theorem B33665159 : Blo 2185435 33665159 := bstep (se 1 (by rfl) ⟨25248869, by rfl⟩ : syracuseStep 33665159 = 50497739) B50497739
theorem B22443439 : Blo 2185435 22443439 := bstep (se 1 (by rfl) ⟨16832579, by rfl⟩ : syracuseStep 22443439 = 33665159) B33665159
theorem B29924585 : Blo 2185435 29924585 := bstep (se 2 (by rfl) ⟨11221719, by rfl⟩ : syracuseStep 29924585 = 22443439) B22443439
theorem B19949723 : Blo 2185435 19949723 := bstep (se 1 (by rfl) ⟨14962292, by rfl⟩ : syracuseStep 19949723 = 29924585) B29924585
theorem B13299815 : Blo 2185435 13299815 := bstep (se 1 (by rfl) ⟨9974861, by rfl⟩ : syracuseStep 13299815 = 19949723) B19949723
theorem B8866543 : Blo 2185435 8866543 := bstep (se 1 (by rfl) ⟨6649907, by rfl⟩ : syracuseStep 8866543 = 13299815) B13299815
theorem B11822057 : Blo 2185435 11822057 := bstep (se 2 (by rfl) ⟨4433271, by rfl⟩ : syracuseStep 11822057 = 8866543) B8866543
theorem B7881371 : Blo 2185435 7881371 := bstep (se 1 (by rfl) ⟨5911028, by rfl⟩ : syracuseStep 7881371 = 11822057) B11822057
theorem B5254247 : Blo 2185435 5254247 := bstep (se 1 (by rfl) ⟨3940685, by rfl⟩ : syracuseStep 5254247 = 7881371) B7881371
theorem B14011325 : Blo 2185435 14011325 := bstep (se 3 (by rfl) ⟨2627123, by rfl⟩ : syracuseStep 14011325 = 5254247) B5254247
theorem B9340883 : Blo 2185435 9340883 := bstep (se 1 (by rfl) ⟨7005662, by rfl⟩ : syracuseStep 9340883 = 14011325) B14011325
theorem B6227255 : Blo 2185435 6227255 := bstep (se 1 (by rfl) ⟨4670441, by rfl⟩ : syracuseStep 6227255 = 9340883) B9340883
theorem B4151503 : Blo 2185435 4151503 := bstep (se 1 (by rfl) ⟨3113627, by rfl⟩ : syracuseStep 4151503 = 6227255) B6227255
theorem B5535337 : Blo 2185435 5535337 := bstep (se 2 (by rfl) ⟨2075751, by rfl⟩ : syracuseStep 5535337 = 4151503) B4151503
theorem B7380449 : Blo 2185435 7380449 := bstep (se 2 (by rfl) ⟨2767668, by rfl⟩ : syracuseStep 7380449 = 5535337) B5535337
theorem B4920299 : Blo 2185435 4920299 := bstep (se 1 (by rfl) ⟨3690224, by rfl⟩ : syracuseStep 4920299 = 7380449) B7380449
theorem B3280199 : Blo 2185435 3280199 := bstep (se 1 (by rfl) ⟨2460149, by rfl⟩ : syracuseStep 3280199 = 4920299) B4920299
theorem B2186799 : Blo 2185435 2186799 := bstep (se 1 (by rfl) ⟨1640099, by rfl⟩ : syracuseStep 2186799 = 3280199) B3280199
theorem B3280205 : Blo 2185435 3280205 := bbase (se 3 (by rfl) ⟨615038, by rfl⟩ : syracuseStep 3280205 = 1230077) (by norm_num)
theorem B2186803 : Blo 2185435 2186803 := bstep (se 1 (by rfl) ⟨1640102, by rfl⟩ : syracuseStep 2186803 = 3280205) B3280205
theorem B4920317 : Blo 2185435 4920317 := bbase (se 3 (by rfl) ⟨922559, by rfl⟩ : syracuseStep 4920317 = 1845119) (by norm_num)
theorem B3280211 : Blo 2185435 3280211 := bstep (se 1 (by rfl) ⟨2460158, by rfl⟩ : syracuseStep 3280211 = 4920317) B4920317
theorem B2186807 : Blo 2185435 2186807 := bstep (se 1 (by rfl) ⟨1640105, by rfl⟩ : syracuseStep 2186807 = 3280211) B3280211
theorem B3690245 : Blo 2185435 3690245 := bbase (se 4 (by rfl) ⟨345960, by rfl⟩ : syracuseStep 3690245 = 691921) (by norm_num)
theorem B2460163 : Blo 2185435 2460163 := bstep (se 1 (by rfl) ⟨1845122, by rfl⟩ : syracuseStep 2460163 = 3690245) B3690245
theorem B3280217 : Blo 2185435 3280217 := bstep (se 2 (by rfl) ⟨1230081, by rfl⟩ : syracuseStep 3280217 = 2460163) B2460163
theorem B2186811 : Blo 2185435 2186811 := bstep (se 1 (by rfl) ⟨1640108, by rfl⟩ : syracuseStep 2186811 = 3280217) B3280217
theorem B16606133 : Blo 2185435 16606133 := bbase (se 5 (by rfl) ⟨778412, by rfl⟩ : syracuseStep 16606133 = 1556825) (by norm_num)
theorem B11070755 : Blo 2185435 11070755 := bstep (se 1 (by rfl) ⟨8303066, by rfl⟩ : syracuseStep 11070755 = 16606133) B16606133
theorem B7380503 : Blo 2185435 7380503 := bstep (se 1 (by rfl) ⟨5535377, by rfl⟩ : syracuseStep 7380503 = 11070755) B11070755
theorem B4920335 : Blo 2185435 4920335 := bstep (se 1 (by rfl) ⟨3690251, by rfl⟩ : syracuseStep 4920335 = 7380503) B7380503
theorem B3280223 : Blo 2185435 3280223 := bstep (se 1 (by rfl) ⟨2460167, by rfl⟩ : syracuseStep 3280223 = 4920335) B4920335
theorem B2186815 : Blo 2185435 2186815 := bstep (se 1 (by rfl) ⟨1640111, by rfl⟩ : syracuseStep 2186815 = 3280223) B3280223
theorem B3280229 : Blo 2185435 3280229 := bbase (se 4 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 3280229 = 615043) (by norm_num)
theorem B2186819 : Blo 2185435 2186819 := bstep (se 1 (by rfl) ⟨1640114, by rfl⟩ : syracuseStep 2186819 = 3280229) B3280229
theorem B4151549 : Blo 2185435 4151549 := bbase (se 3 (by rfl) ⟨778415, by rfl⟩ : syracuseStep 4151549 = 1556831) (by norm_num)
theorem B2767699 : Blo 2185435 2767699 := bstep (se 1 (by rfl) ⟨2075774, by rfl⟩ : syracuseStep 2767699 = 4151549) B4151549
theorem B3690265 : Blo 2185435 3690265 := bstep (se 2 (by rfl) ⟨1383849, by rfl⟩ : syracuseStep 3690265 = 2767699) B2767699
theorem B4920353 : Blo 2185435 4920353 := bstep (se 2 (by rfl) ⟨1845132, by rfl⟩ : syracuseStep 4920353 = 3690265) B3690265
theorem B3280235 : Blo 2185435 3280235 := bstep (se 1 (by rfl) ⟨2460176, by rfl⟩ : syracuseStep 3280235 = 4920353) B4920353
theorem B2186823 : Blo 2185435 2186823 := bstep (se 1 (by rfl) ⟨1640117, by rfl⟩ : syracuseStep 2186823 = 3280235) B3280235
theorem B2460181 : Blo 2185435 2460181 := bbase (se 6 (by rfl) ⟨57660, by rfl⟩ : syracuseStep 2460181 = 115321) (by norm_num)
theorem B3280241 : Blo 2185435 3280241 := bstep (se 2 (by rfl) ⟨1230090, by rfl⟩ : syracuseStep 3280241 = 2460181) B2460181
theorem B2186827 : Blo 2185435 2186827 := bstep (se 1 (by rfl) ⟨1640120, by rfl⟩ : syracuseStep 2186827 = 3280241) B3280241
theorem B2767709 : Blo 2185435 2767709 := bbase (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) (by norm_num)
theorem B7380557 : Blo 2185435 7380557 := bstep (se 3 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 7380557 = 2767709) B2767709
theorem B4920371 : Blo 2185435 4920371 := bstep (se 1 (by rfl) ⟨3690278, by rfl⟩ : syracuseStep 4920371 = 7380557) B7380557
theorem B3280247 : Blo 2185435 3280247 := bstep (se 1 (by rfl) ⟨2460185, by rfl⟩ : syracuseStep 3280247 = 4920371) B4920371
theorem B2186831 : Blo 2185435 2186831 := bstep (se 1 (by rfl) ⟨1640123, by rfl⟩ : syracuseStep 2186831 = 3280247) B3280247
theorem B3280253 : Blo 2185435 3280253 := bbase (se 3 (by rfl) ⟨615047, by rfl⟩ : syracuseStep 3280253 = 1230095) (by norm_num)
theorem B2186835 : Blo 2185435 2186835 := bstep (se 1 (by rfl) ⟨1640126, by rfl⟩ : syracuseStep 2186835 = 3280253) B3280253
theorem B4920389 : Blo 2185435 4920389 := bbase (se 4 (by rfl) ⟨461286, by rfl⟩ : syracuseStep 4920389 = 922573) (by norm_num)
theorem B3280259 : Blo 2185435 3280259 := bstep (se 1 (by rfl) ⟨2460194, by rfl⟩ : syracuseStep 3280259 = 4920389) B4920389
theorem B2186839 : Blo 2185435 2186839 := bstep (se 1 (by rfl) ⟨1640129, by rfl⟩ : syracuseStep 2186839 = 3280259) B3280259
theorem B6227381 : Blo 2185435 6227381 := bbase (se 5 (by rfl) ⟨291908, by rfl⟩ : syracuseStep 6227381 = 583817) (by norm_num)
theorem B4151587 : Blo 2185435 4151587 := bstep (se 1 (by rfl) ⟨3113690, by rfl⟩ : syracuseStep 4151587 = 6227381) B6227381
theorem B5535449 : Blo 2185435 5535449 := bstep (se 2 (by rfl) ⟨2075793, by rfl⟩ : syracuseStep 5535449 = 4151587) B4151587
theorem B3690299 : Blo 2185435 3690299 := bstep (se 1 (by rfl) ⟨2767724, by rfl⟩ : syracuseStep 3690299 = 5535449) B5535449
theorem B2460199 : Blo 2185435 2460199 := bstep (se 1 (by rfl) ⟨1845149, by rfl⟩ : syracuseStep 2460199 = 3690299) B3690299
theorem B3280265 : Blo 2185435 3280265 := bstep (se 2 (by rfl) ⟨1230099, by rfl⟩ : syracuseStep 3280265 = 2460199) B2460199
theorem B2186843 : Blo 2185435 2186843 := bstep (se 1 (by rfl) ⟨1640132, by rfl⟩ : syracuseStep 2186843 = 3280265) B3280265
theorem B11070917 : Blo 2185435 11070917 := bbase (se 4 (by rfl) ⟨1037898, by rfl⟩ : syracuseStep 11070917 = 2075797) (by norm_num)
theorem B7380611 : Blo 2185435 7380611 := bstep (se 1 (by rfl) ⟨5535458, by rfl⟩ : syracuseStep 7380611 = 11070917) B11070917
theorem B4920407 : Blo 2185435 4920407 := bstep (se 1 (by rfl) ⟨3690305, by rfl⟩ : syracuseStep 4920407 = 7380611) B7380611
theorem B3280271 : Blo 2185435 3280271 := bstep (se 1 (by rfl) ⟨2460203, by rfl⟩ : syracuseStep 3280271 = 4920407) B4920407
theorem B2186847 : Blo 2185435 2186847 := bstep (se 1 (by rfl) ⟨1640135, by rfl⟩ : syracuseStep 2186847 = 3280271) B3280271
theorem B3280277 : Blo 2185435 3280277 := bbase (se 6 (by rfl) ⟨76881, by rfl⟩ : syracuseStep 3280277 = 153763) (by norm_num)
theorem B2186851 : Blo 2185435 2186851 := bstep (se 1 (by rfl) ⟨1640138, by rfl⟩ : syracuseStep 2186851 = 3280277) B3280277
theorem B2216693 : Blo 2185435 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B5911181 : Blo 2185435 5911181 := bstep (se 3 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 5911181 = 2216693) B2216693
theorem B3940787 : Blo 2185435 3940787 := bstep (se 1 (by rfl) ⟨2955590, by rfl⟩ : syracuseStep 3940787 = 5911181) B5911181
theorem B2627191 : Blo 2185435 2627191 := bstep (se 1 (by rfl) ⟨1970393, by rfl⟩ : syracuseStep 2627191 = 3940787) B3940787
theorem B3502921 : Blo 2185435 3502921 := bstep (se 2 (by rfl) ⟨1313595, by rfl⟩ : syracuseStep 3502921 = 2627191) B2627191
theorem B4670561 : Blo 2185435 4670561 := bstep (se 2 (by rfl) ⟨1751460, by rfl⟩ : syracuseStep 4670561 = 3502921) B3502921
theorem B12454829 : Blo 2185435 12454829 := bstep (se 3 (by rfl) ⟨2335280, by rfl⟩ : syracuseStep 12454829 = 4670561) B4670561
theorem B8303219 : Blo 2185435 8303219 := bstep (se 1 (by rfl) ⟨6227414, by rfl⟩ : syracuseStep 8303219 = 12454829) B12454829
theorem B5535479 : Blo 2185435 5535479 := bstep (se 1 (by rfl) ⟨4151609, by rfl⟩ : syracuseStep 5535479 = 8303219) B8303219
theorem B3690319 : Blo 2185435 3690319 := bstep (se 1 (by rfl) ⟨2767739, by rfl⟩ : syracuseStep 3690319 = 5535479) B5535479
theorem B4920425 : Blo 2185435 4920425 := bstep (se 2 (by rfl) ⟨1845159, by rfl⟩ : syracuseStep 4920425 = 3690319) B3690319
theorem B3280283 : Blo 2185435 3280283 := bstep (se 1 (by rfl) ⟨2460212, by rfl⟩ : syracuseStep 3280283 = 4920425) B4920425
theorem B2186855 : Blo 2185435 2186855 := bstep (se 1 (by rfl) ⟨1640141, by rfl⟩ : syracuseStep 2186855 = 3280283) B3280283
theorem B2460217 : Blo 2185435 2460217 := bbase (se 2 (by rfl) ⟨922581, by rfl⟩ : syracuseStep 2460217 = 1845163) (by norm_num)
theorem B3280289 : Blo 2185435 3280289 := bstep (se 2 (by rfl) ⟨1230108, by rfl⟩ : syracuseStep 3280289 = 2460217) B2460217
theorem B2186859 : Blo 2185435 2186859 := bstep (se 1 (by rfl) ⟨1640144, by rfl⟩ : syracuseStep 2186859 = 3280289) B3280289
theorem B2335289 : Blo 2185435 2335289 := bbase (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) (by norm_num)
theorem B6227437 : Blo 2185435 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B8303249 : Blo 2185435 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B5535499 : Blo 2185435 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B7380665 : Blo 2185435 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B4920443 : Blo 2185435 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B3280295 : Blo 2185435 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B2186863 : Blo 2185435 2186863 := bstep (se 1 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 2186863 = 3280295) B3280295
theorem B3280301 : Blo 2185435 3280301 := bbase (se 3 (by rfl) ⟨615056, by rfl⟩ : syracuseStep 3280301 = 1230113) (by norm_num)
theorem B2186867 : Blo 2185435 2186867 := bstep (se 1 (by rfl) ⟨1640150, by rfl⟩ : syracuseStep 2186867 = 3280301) B3280301
theorem B4920461 : Blo 2185435 4920461 := bbase (se 3 (by rfl) ⟨922586, by rfl⟩ : syracuseStep 4920461 = 1845173) (by norm_num)
theorem B3280307 : Blo 2185435 3280307 := bstep (se 1 (by rfl) ⟨2460230, by rfl⟩ : syracuseStep 3280307 = 4920461) B4920461
theorem B2186871 : Blo 2185435 2186871 := bstep (se 1 (by rfl) ⟨1640153, by rfl⟩ : syracuseStep 2186871 = 3280307) B3280307
theorem B2767765 : Blo 2185435 2767765 := bbase (se 6 (by rfl) ⟨64869, by rfl⟩ : syracuseStep 2767765 = 129739) (by norm_num)
theorem B3690353 : Blo 2185435 3690353 := bstep (se 2 (by rfl) ⟨1383882, by rfl⟩ : syracuseStep 3690353 = 2767765) B2767765
theorem B2460235 : Blo 2185435 2460235 := bstep (se 1 (by rfl) ⟨1845176, by rfl⟩ : syracuseStep 2460235 = 3690353) B3690353
theorem B3280313 : Blo 2185435 3280313 := bstep (se 2 (by rfl) ⟨1230117, by rfl⟩ : syracuseStep 3280313 = 2460235) B2460235
theorem B2186875 : Blo 2185435 2186875 := bstep (se 1 (by rfl) ⟨1640156, by rfl⟩ : syracuseStep 2186875 = 3280313) B3280313
theorem B6650149 : Blo 2185435 6650149 := bbase (se 4 (by rfl) ⟨623451, by rfl⟩ : syracuseStep 6650149 = 1246903) (by norm_num)
theorem B8866865 : Blo 2185435 8866865 := bstep (se 2 (by rfl) ⟨3325074, by rfl⟩ : syracuseStep 8866865 = 6650149) B6650149
theorem B23644973 : Blo 2185435 23644973 := bstep (se 3 (by rfl) ⟨4433432, by rfl⟩ : syracuseStep 23644973 = 8866865) B8866865
theorem B63053261 : Blo 2185435 63053261 := bstep (se 3 (by rfl) ⟨11822486, by rfl⟩ : syracuseStep 63053261 = 23644973) B23644973
theorem B42035507 : Blo 2185435 42035507 := bstep (se 1 (by rfl) ⟨31526630, by rfl⟩ : syracuseStep 42035507 = 63053261) B63053261
theorem B28023671 : Blo 2185435 28023671 := bstep (se 1 (by rfl) ⟨21017753, by rfl⟩ : syracuseStep 28023671 = 42035507) B42035507
theorem B18682447 : Blo 2185435 18682447 := bstep (se 1 (by rfl) ⟨14011835, by rfl⟩ : syracuseStep 18682447 = 28023671) B28023671
theorem B24909929 : Blo 2185435 24909929 := bstep (se 2 (by rfl) ⟨9341223, by rfl⟩ : syracuseStep 24909929 = 18682447) B18682447
theorem B16606619 : Blo 2185435 16606619 := bstep (se 1 (by rfl) ⟨12454964, by rfl⟩ : syracuseStep 16606619 = 24909929) B24909929
theorem B11071079 : Blo 2185435 11071079 := bstep (se 1 (by rfl) ⟨8303309, by rfl⟩ : syracuseStep 11071079 = 16606619) B16606619
theorem B7380719 : Blo 2185435 7380719 := bstep (se 1 (by rfl) ⟨5535539, by rfl⟩ : syracuseStep 7380719 = 11071079) B11071079
theorem B4920479 : Blo 2185435 4920479 := bstep (se 1 (by rfl) ⟨3690359, by rfl⟩ : syracuseStep 4920479 = 7380719) B7380719
theorem B3280319 : Blo 2185435 3280319 := bstep (se 1 (by rfl) ⟨2460239, by rfl⟩ : syracuseStep 3280319 = 4920479) B4920479
theorem B2186879 : Blo 2185435 2186879 := bstep (se 1 (by rfl) ⟨1640159, by rfl⟩ : syracuseStep 2186879 = 3280319) B3280319
theorem B3280325 : Blo 2185435 3280325 := bbase (se 4 (by rfl) ⟨307530, by rfl⟩ : syracuseStep 3280325 = 615061) (by norm_num)
theorem B2186883 : Blo 2185435 2186883 := bstep (se 1 (by rfl) ⟨1640162, by rfl⟩ : syracuseStep 2186883 = 3280325) B3280325
theorem B3690373 : Blo 2185435 3690373 := bbase (se 4 (by rfl) ⟨345972, by rfl⟩ : syracuseStep 3690373 = 691945) (by norm_num)
theorem B4920497 : Blo 2185435 4920497 := bstep (se 2 (by rfl) ⟨1845186, by rfl⟩ : syracuseStep 4920497 = 3690373) B3690373
theorem B3280331 : Blo 2185435 3280331 := bstep (se 1 (by rfl) ⟨2460248, by rfl⟩ : syracuseStep 3280331 = 4920497) B4920497
theorem B2186887 : Blo 2185435 2186887 := bstep (se 1 (by rfl) ⟨1640165, by rfl⟩ : syracuseStep 2186887 = 3280331) B3280331
theorem B2460253 : Blo 2185435 2460253 := bbase (se 3 (by rfl) ⟨461297, by rfl⟩ : syracuseStep 2460253 = 922595) (by norm_num)
theorem B3280337 : Blo 2185435 3280337 := bstep (se 2 (by rfl) ⟨1230126, by rfl⟩ : syracuseStep 3280337 = 2460253) B2460253
theorem B2186891 : Blo 2185435 2186891 := bstep (se 1 (by rfl) ⟨1640168, by rfl⟩ : syracuseStep 2186891 = 3280337) B3280337
theorem B7380773 : Blo 2185435 7380773 := bbase (se 4 (by rfl) ⟨691947, by rfl⟩ : syracuseStep 7380773 = 1383895) (by norm_num)
theorem B4920515 : Blo 2185435 4920515 := bstep (se 1 (by rfl) ⟨3690386, by rfl⟩ : syracuseStep 4920515 = 7380773) B7380773
theorem B3280343 : Blo 2185435 3280343 := bstep (se 1 (by rfl) ⟨2460257, by rfl⟩ : syracuseStep 3280343 = 4920515) B4920515
theorem B2186895 : Blo 2185435 2186895 := bstep (se 1 (by rfl) ⟨1640171, by rfl⟩ : syracuseStep 2186895 = 3280343) B3280343
theorem B3280349 : Blo 2185435 3280349 := bbase (se 3 (by rfl) ⟨615065, by rfl⟩ : syracuseStep 3280349 = 1230131) (by norm_num)
theorem B2186899 : Blo 2185435 2186899 := bstep (se 1 (by rfl) ⟨1640174, by rfl⟩ : syracuseStep 2186899 = 3280349) B3280349
theorem B4920533 : Blo 2185435 4920533 := bbase (se 7 (by rfl) ⟨57662, by rfl⟩ : syracuseStep 4920533 = 115325) (by norm_num)
theorem B3280355 : Blo 2185435 3280355 := bstep (se 1 (by rfl) ⟨2460266, by rfl⟩ : syracuseStep 3280355 = 4920533) B4920533
theorem B2186903 : Blo 2185435 2186903 := bstep (se 1 (by rfl) ⟨1640177, by rfl⟩ : syracuseStep 2186903 = 3280355) B3280355
theorem B8416709 : Blo 2185435 8416709 := bbase (se 4 (by rfl) ⟨789066, by rfl⟩ : syracuseStep 8416709 = 1578133) (by norm_num)
theorem B5611139 : Blo 2185435 5611139 := bstep (se 1 (by rfl) ⟨4208354, by rfl⟩ : syracuseStep 5611139 = 8416709) B8416709
theorem B3740759 : Blo 2185435 3740759 := bstep (se 1 (by rfl) ⟨2805569, by rfl⟩ : syracuseStep 3740759 = 5611139) B5611139
theorem B2493839 : Blo 2185435 2493839 := bstep (se 1 (by rfl) ⟨1870379, by rfl⟩ : syracuseStep 2493839 = 3740759) B3740759
theorem B6650237 : Blo 2185435 6650237 := bstep (se 3 (by rfl) ⟨1246919, by rfl⟩ : syracuseStep 6650237 = 2493839) B2493839
theorem B4433491 : Blo 2185435 4433491 := bstep (se 1 (by rfl) ⟨3325118, by rfl⟩ : syracuseStep 4433491 = 6650237) B6650237
theorem B5911321 : Blo 2185435 5911321 := bstep (se 2 (by rfl) ⟨2216745, by rfl⟩ : syracuseStep 5911321 = 4433491) B4433491
theorem B7881761 : Blo 2185435 7881761 := bstep (se 2 (by rfl) ⟨2955660, by rfl⟩ : syracuseStep 7881761 = 5911321) B5911321
theorem B5254507 : Blo 2185435 5254507 := bstep (se 1 (by rfl) ⟨3940880, by rfl⟩ : syracuseStep 5254507 = 7881761) B7881761
theorem B7006009 : Blo 2185435 7006009 := bstep (se 2 (by rfl) ⟨2627253, by rfl⟩ : syracuseStep 7006009 = 5254507) B5254507
theorem B9341345 : Blo 2185435 9341345 := bstep (se 2 (by rfl) ⟨3503004, by rfl⟩ : syracuseStep 9341345 = 7006009) B7006009
theorem B6227563 : Blo 2185435 6227563 := bstep (se 1 (by rfl) ⟨4670672, by rfl⟩ : syracuseStep 6227563 = 9341345) B9341345
theorem B8303417 : Blo 2185435 8303417 := bstep (se 2 (by rfl) ⟨3113781, by rfl⟩ : syracuseStep 8303417 = 6227563) B6227563
theorem B5535611 : Blo 2185435 5535611 := bstep (se 1 (by rfl) ⟨4151708, by rfl⟩ : syracuseStep 5535611 = 8303417) B8303417
theorem B3690407 : Blo 2185435 3690407 := bstep (se 1 (by rfl) ⟨2767805, by rfl⟩ : syracuseStep 3690407 = 5535611) B5535611
theorem B2460271 : Blo 2185435 2460271 := bstep (se 1 (by rfl) ⟨1845203, by rfl⟩ : syracuseStep 2460271 = 3690407) B3690407
theorem B3280361 : Blo 2185435 3280361 := bstep (se 2 (by rfl) ⟨1230135, by rfl⟩ : syracuseStep 3280361 = 2460271) B2460271
theorem B2186907 : Blo 2185435 2186907 := bstep (se 1 (by rfl) ⟨1640180, by rfl⟩ : syracuseStep 2186907 = 3280361) B3280361
theorem B5326205 : Blo 2185435 5326205 := bbase (se 3 (by rfl) ⟨998663, by rfl⟩ : syracuseStep 5326205 = 1997327) (by norm_num)
theorem B56812853 : Blo 2185435 56812853 := bstep (se 5 (by rfl) ⟨2663102, by rfl⟩ : syracuseStep 56812853 = 5326205) B5326205
theorem B151500941 : Blo 2185435 151500941 := bstep (se 3 (by rfl) ⟨28406426, by rfl⟩ : syracuseStep 151500941 = 56812853) B56812853
theorem B101000627 : Blo 2185435 101000627 := bstep (se 1 (by rfl) ⟨75750470, by rfl⟩ : syracuseStep 101000627 = 151500941) B151500941
theorem B67333751 : Blo 2185435 67333751 := bstep (se 1 (by rfl) ⟨50500313, by rfl⟩ : syracuseStep 67333751 = 101000627) B101000627
theorem B44889167 : Blo 2185435 44889167 := bstep (se 1 (by rfl) ⟨33666875, by rfl⟩ : syracuseStep 44889167 = 67333751) B67333751
theorem B29926111 : Blo 2185435 29926111 := bstep (se 1 (by rfl) ⟨22444583, by rfl⟩ : syracuseStep 29926111 = 44889167) B44889167
theorem B39901481 : Blo 2185435 39901481 := bstep (se 2 (by rfl) ⟨14963055, by rfl⟩ : syracuseStep 39901481 = 29926111) B29926111
theorem B26600987 : Blo 2185435 26600987 := bstep (se 1 (by rfl) ⟨19950740, by rfl⟩ : syracuseStep 26600987 = 39901481) B39901481
theorem B17733991 : Blo 2185435 17733991 := bstep (se 1 (by rfl) ⟨13300493, by rfl⟩ : syracuseStep 17733991 = 26600987) B26600987
theorem B23645321 : Blo 2185435 23645321 := bstep (se 2 (by rfl) ⟨8866995, by rfl⟩ : syracuseStep 23645321 = 17733991) B17733991
theorem B15763547 : Blo 2185435 15763547 := bstep (se 1 (by rfl) ⟨11822660, by rfl⟩ : syracuseStep 15763547 = 23645321) B23645321
theorem B10509031 : Blo 2185435 10509031 := bstep (se 1 (by rfl) ⟨7881773, by rfl⟩ : syracuseStep 10509031 = 15763547) B15763547
theorem B14012041 : Blo 2185435 14012041 := bstep (se 2 (by rfl) ⟨5254515, by rfl⟩ : syracuseStep 14012041 = 10509031) B10509031
theorem B18682721 : Blo 2185435 18682721 := bstep (se 2 (by rfl) ⟨7006020, by rfl⟩ : syracuseStep 18682721 = 14012041) B14012041
theorem B12455147 : Blo 2185435 12455147 := bstep (se 1 (by rfl) ⟨9341360, by rfl⟩ : syracuseStep 12455147 = 18682721) B18682721
theorem B8303431 : Blo 2185435 8303431 := bstep (se 1 (by rfl) ⟨6227573, by rfl⟩ : syracuseStep 8303431 = 12455147) B12455147
theorem B11071241 : Blo 2185435 11071241 := bstep (se 2 (by rfl) ⟨4151715, by rfl⟩ : syracuseStep 11071241 = 8303431) B8303431
theorem B7380827 : Blo 2185435 7380827 := bstep (se 1 (by rfl) ⟨5535620, by rfl⟩ : syracuseStep 7380827 = 11071241) B11071241
theorem B4920551 : Blo 2185435 4920551 := bstep (se 1 (by rfl) ⟨3690413, by rfl⟩ : syracuseStep 4920551 = 7380827) B7380827
theorem B3280367 : Blo 2185435 3280367 := bstep (se 1 (by rfl) ⟨2460275, by rfl⟩ : syracuseStep 3280367 = 4920551) B4920551
theorem B2186911 : Blo 2185435 2186911 := bstep (se 1 (by rfl) ⟨1640183, by rfl⟩ : syracuseStep 2186911 = 3280367) B3280367
theorem B3280373 : Blo 2185435 3280373 := bbase (se 5 (by rfl) ⟨153767, by rfl⟩ : syracuseStep 3280373 = 307535) (by norm_num)
theorem B2186915 : Blo 2185435 2186915 := bstep (se 1 (by rfl) ⟨1640186, by rfl⟩ : syracuseStep 2186915 = 3280373) B3280373
theorem B2335349 : Blo 2185435 2335349 := bbase (se 5 (by rfl) ⟨109469, by rfl⟩ : syracuseStep 2335349 = 218939) (by norm_num)
theorem B6227597 : Blo 2185435 6227597 := bstep (se 3 (by rfl) ⟨1167674, by rfl⟩ : syracuseStep 6227597 = 2335349) B2335349
theorem B4151731 : Blo 2185435 4151731 := bstep (se 1 (by rfl) ⟨3113798, by rfl⟩ : syracuseStep 4151731 = 6227597) B6227597
theorem B5535641 : Blo 2185435 5535641 := bstep (se 2 (by rfl) ⟨2075865, by rfl⟩ : syracuseStep 5535641 = 4151731) B4151731
theorem B3690427 : Blo 2185435 3690427 := bstep (se 1 (by rfl) ⟨2767820, by rfl⟩ : syracuseStep 3690427 = 5535641) B5535641
theorem B4920569 : Blo 2185435 4920569 := bstep (se 2 (by rfl) ⟨1845213, by rfl⟩ : syracuseStep 4920569 = 3690427) B3690427
theorem B3280379 : Blo 2185435 3280379 := bstep (se 1 (by rfl) ⟨2460284, by rfl⟩ : syracuseStep 3280379 = 4920569) B4920569
theorem B2186919 : Blo 2185435 2186919 := bstep (se 1 (by rfl) ⟨1640189, by rfl⟩ : syracuseStep 2186919 = 3280379) B3280379
theorem B2460289 : Blo 2185435 2460289 := bbase (se 2 (by rfl) ⟨922608, by rfl⟩ : syracuseStep 2460289 = 1845217) (by norm_num)
theorem B3280385 : Blo 2185435 3280385 := bstep (se 2 (by rfl) ⟨1230144, by rfl⟩ : syracuseStep 3280385 = 2460289) B2460289
theorem B2186923 : Blo 2185435 2186923 := bstep (se 1 (by rfl) ⟨1640192, by rfl⟩ : syracuseStep 2186923 = 3280385) B3280385
theorem B5535661 : Blo 2185435 5535661 := bbase (se 3 (by rfl) ⟨1037936, by rfl⟩ : syracuseStep 5535661 = 2075873) (by norm_num)
theorem B7380881 : Blo 2185435 7380881 := bstep (se 2 (by rfl) ⟨2767830, by rfl⟩ : syracuseStep 7380881 = 5535661) B5535661
theorem B4920587 : Blo 2185435 4920587 := bstep (se 1 (by rfl) ⟨3690440, by rfl⟩ : syracuseStep 4920587 = 7380881) B7380881
theorem B3280391 : Blo 2185435 3280391 := bstep (se 1 (by rfl) ⟨2460293, by rfl⟩ : syracuseStep 3280391 = 4920587) B4920587
theorem B2186927 : Blo 2185435 2186927 := bstep (se 1 (by rfl) ⟨1640195, by rfl⟩ : syracuseStep 2186927 = 3280391) B3280391
theorem B3280397 : Blo 2185435 3280397 := bbase (se 3 (by rfl) ⟨615074, by rfl⟩ : syracuseStep 3280397 = 1230149) (by norm_num)
theorem B2186931 : Blo 2185435 2186931 := bstep (se 1 (by rfl) ⟨1640198, by rfl⟩ : syracuseStep 2186931 = 3280397) B3280397
theorem B4920605 : Blo 2185435 4920605 := bbase (se 3 (by rfl) ⟨922613, by rfl⟩ : syracuseStep 4920605 = 1845227) (by norm_num)
theorem B3280403 : Blo 2185435 3280403 := bstep (se 1 (by rfl) ⟨2460302, by rfl⟩ : syracuseStep 3280403 = 4920605) B4920605
theorem B2186935 : Blo 2185435 2186935 := bstep (se 1 (by rfl) ⟨1640201, by rfl⟩ : syracuseStep 2186935 = 3280403) B3280403
theorem B3690461 : Blo 2185435 3690461 := bbase (se 3 (by rfl) ⟨691961, by rfl⟩ : syracuseStep 3690461 = 1383923) (by norm_num)
theorem B2460307 : Blo 2185435 2460307 := bstep (se 1 (by rfl) ⟨1845230, by rfl⟩ : syracuseStep 2460307 = 3690461) B3690461
theorem B3280409 : Blo 2185435 3280409 := bstep (se 2 (by rfl) ⟨1230153, by rfl⟩ : syracuseStep 3280409 = 2460307) B2460307
theorem B2186939 : Blo 2185435 2186939 := bstep (se 1 (by rfl) ⟨1640204, by rfl⟩ : syracuseStep 2186939 = 3280409) B3280409
theorem B5326285 : Blo 2185435 5326285 := bbase (se 3 (by rfl) ⟨998678, by rfl⟩ : syracuseStep 5326285 = 1997357) (by norm_num)
theorem B7101713 : Blo 2185435 7101713 := bstep (se 2 (by rfl) ⟨2663142, by rfl⟩ : syracuseStep 7101713 = 5326285) B5326285
theorem B18937901 : Blo 2185435 18937901 := bstep (se 3 (by rfl) ⟨3550856, by rfl⟩ : syracuseStep 18937901 = 7101713) B7101713
theorem B12625267 : Blo 2185435 12625267 := bstep (se 1 (by rfl) ⟨9468950, by rfl⟩ : syracuseStep 12625267 = 18937901) B18937901
theorem B16833689 : Blo 2185435 16833689 := bstep (se 2 (by rfl) ⟨6312633, by rfl⟩ : syracuseStep 16833689 = 12625267) B12625267
theorem B11222459 : Blo 2185435 11222459 := bstep (se 1 (by rfl) ⟨8416844, by rfl⟩ : syracuseStep 11222459 = 16833689) B16833689
theorem B7481639 : Blo 2185435 7481639 := bstep (se 1 (by rfl) ⟨5611229, by rfl⟩ : syracuseStep 7481639 = 11222459) B11222459
theorem B4987759 : Blo 2185435 4987759 := bstep (se 1 (by rfl) ⟨3740819, by rfl⟩ : syracuseStep 4987759 = 7481639) B7481639
theorem B6650345 : Blo 2185435 6650345 := bstep (se 2 (by rfl) ⟨2493879, by rfl⟩ : syracuseStep 6650345 = 4987759) B4987759
theorem B4433563 : Blo 2185435 4433563 := bstep (se 1 (by rfl) ⟨3325172, by rfl⟩ : syracuseStep 4433563 = 6650345) B6650345
theorem B5911417 : Blo 2185435 5911417 := bstep (se 2 (by rfl) ⟨2216781, by rfl⟩ : syracuseStep 5911417 = 4433563) B4433563
theorem B7881889 : Blo 2185435 7881889 := bstep (se 2 (by rfl) ⟨2955708, by rfl⟩ : syracuseStep 7881889 = 5911417) B5911417
theorem B10509185 : Blo 2185435 10509185 := bstep (se 2 (by rfl) ⟨3940944, by rfl⟩ : syracuseStep 10509185 = 7881889) B7881889
theorem B7006123 : Blo 2185435 7006123 := bstep (se 1 (by rfl) ⟨5254592, by rfl⟩ : syracuseStep 7006123 = 10509185) B10509185
theorem B9341497 : Blo 2185435 9341497 := bstep (se 2 (by rfl) ⟨3503061, by rfl⟩ : syracuseStep 9341497 = 7006123) B7006123
theorem B12455329 : Blo 2185435 12455329 := bstep (se 2 (by rfl) ⟨4670748, by rfl⟩ : syracuseStep 12455329 = 9341497) B9341497
theorem B16607105 : Blo 2185435 16607105 := bstep (se 2 (by rfl) ⟨6227664, by rfl⟩ : syracuseStep 16607105 = 12455329) B12455329
theorem B11071403 : Blo 2185435 11071403 := bstep (se 1 (by rfl) ⟨8303552, by rfl⟩ : syracuseStep 11071403 = 16607105) B16607105
theorem B7380935 : Blo 2185435 7380935 := bstep (se 1 (by rfl) ⟨5535701, by rfl⟩ : syracuseStep 7380935 = 11071403) B11071403
theorem B4920623 : Blo 2185435 4920623 := bstep (se 1 (by rfl) ⟨3690467, by rfl⟩ : syracuseStep 4920623 = 7380935) B7380935
theorem B3280415 : Blo 2185435 3280415 := bstep (se 1 (by rfl) ⟨2460311, by rfl⟩ : syracuseStep 3280415 = 4920623) B4920623
theorem B2186943 : Blo 2185435 2186943 := bstep (se 1 (by rfl) ⟨1640207, by rfl⟩ : syracuseStep 2186943 = 3280415) B3280415
theorem B3280421 : Blo 2185435 3280421 := bbase (se 4 (by rfl) ⟨307539, by rfl⟩ : syracuseStep 3280421 = 615079) (by norm_num)
theorem B2186947 : Blo 2185435 2186947 := bstep (se 1 (by rfl) ⟨1640210, by rfl⟩ : syracuseStep 2186947 = 3280421) B3280421
theorem B2767861 : Blo 2185435 2767861 := bbase (se 5 (by rfl) ⟨129743, by rfl⟩ : syracuseStep 2767861 = 259487) (by norm_num)
theorem B3690481 : Blo 2185435 3690481 := bstep (se 2 (by rfl) ⟨1383930, by rfl⟩ : syracuseStep 3690481 = 2767861) B2767861
theorem B4920641 : Blo 2185435 4920641 := bstep (se 2 (by rfl) ⟨1845240, by rfl⟩ : syracuseStep 4920641 = 3690481) B3690481
theorem B3280427 : Blo 2185435 3280427 := bstep (se 1 (by rfl) ⟨2460320, by rfl⟩ : syracuseStep 3280427 = 4920641) B4920641
theorem B2186951 : Blo 2185435 2186951 := bstep (se 1 (by rfl) ⟨1640213, by rfl⟩ : syracuseStep 2186951 = 3280427) B3280427
theorem B2460325 : Blo 2185435 2460325 := bbase (se 4 (by rfl) ⟨230655, by rfl⟩ : syracuseStep 2460325 = 461311) (by norm_num)
theorem B3280433 : Blo 2185435 3280433 := bstep (se 2 (by rfl) ⟨1230162, by rfl⟩ : syracuseStep 3280433 = 2460325) B2460325
theorem B2186955 : Blo 2185435 2186955 := bstep (se 1 (by rfl) ⟨1640216, by rfl⟩ : syracuseStep 2186955 = 3280433) B3280433
theorem B4734509 : Blo 2185435 4734509 := bbase (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) (by norm_num)
theorem B12625357 : Blo 2185435 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B16833809 : Blo 2185435 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B44890157 : Blo 2185435 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B119707085 : Blo 2185435 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B79804723 : Blo 2185435 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B106406297 : Blo 2185435 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B70937531 : Blo 2185435 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B47291687 : Blo 2185435 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B31527791 : Blo 2185435 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B21018527 : Blo 2185435 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B14012351 : Blo 2185435 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B9341567 : Blo 2185435 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B6227711 : Blo 2185435 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B4151807 : Blo 2185435 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B2767871 : Blo 2185435 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B7380989 : Blo 2185435 7380989 := bstep (se 3 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 7380989 = 2767871) B2767871
theorem B4920659 : Blo 2185435 4920659 := bstep (se 1 (by rfl) ⟨3690494, by rfl⟩ : syracuseStep 4920659 = 7380989) B7380989
theorem B3280439 : Blo 2185435 3280439 := bstep (se 1 (by rfl) ⟨2460329, by rfl⟩ : syracuseStep 3280439 = 4920659) B4920659
theorem B2186959 : Blo 2185435 2186959 := bstep (se 1 (by rfl) ⟨1640219, by rfl⟩ : syracuseStep 2186959 = 3280439) B3280439
theorem B3280445 : Blo 2185435 3280445 := bbase (se 3 (by rfl) ⟨615083, by rfl⟩ : syracuseStep 3280445 = 1230167) (by norm_num)
theorem B2186963 : Blo 2185435 2186963 := bstep (se 1 (by rfl) ⟨1640222, by rfl⟩ : syracuseStep 2186963 = 3280445) B3280445
theorem B4920677 : Blo 2185435 4920677 := bbase (se 4 (by rfl) ⟨461313, by rfl⟩ : syracuseStep 4920677 = 922627) (by norm_num)
theorem B3280451 : Blo 2185435 3280451 := bstep (se 1 (by rfl) ⟨2460338, by rfl⟩ : syracuseStep 3280451 = 4920677) B4920677
theorem B2186967 : Blo 2185435 2186967 := bstep (se 1 (by rfl) ⟨1640225, by rfl⟩ : syracuseStep 2186967 = 3280451) B3280451
theorem B5535773 : Blo 2185435 5535773 := bbase (se 3 (by rfl) ⟨1037957, by rfl⟩ : syracuseStep 5535773 = 2075915) (by norm_num)
theorem B3690515 : Blo 2185435 3690515 := bstep (se 1 (by rfl) ⟨2767886, by rfl⟩ : syracuseStep 3690515 = 5535773) B5535773
theorem B2460343 : Blo 2185435 2460343 := bstep (se 1 (by rfl) ⟨1845257, by rfl⟩ : syracuseStep 2460343 = 3690515) B3690515
theorem B3280457 : Blo 2185435 3280457 := bstep (se 2 (by rfl) ⟨1230171, by rfl⟩ : syracuseStep 3280457 = 2460343) B2460343
theorem B2186971 : Blo 2185435 2186971 := bstep (se 1 (by rfl) ⟨1640228, by rfl⟩ : syracuseStep 2186971 = 3280457) B3280457
theorem B4151837 : Blo 2185435 4151837 := bbase (se 3 (by rfl) ⟨778469, by rfl⟩ : syracuseStep 4151837 = 1556939) (by norm_num)
theorem B11071565 : Blo 2185435 11071565 := bstep (se 3 (by rfl) ⟨2075918, by rfl⟩ : syracuseStep 11071565 = 4151837) B4151837
theorem B7381043 : Blo 2185435 7381043 := bstep (se 1 (by rfl) ⟨5535782, by rfl⟩ : syracuseStep 7381043 = 11071565) B11071565
theorem B4920695 : Blo 2185435 4920695 := bstep (se 1 (by rfl) ⟨3690521, by rfl⟩ : syracuseStep 4920695 = 7381043) B7381043
theorem B3280463 : Blo 2185435 3280463 := bstep (se 1 (by rfl) ⟨2460347, by rfl⟩ : syracuseStep 3280463 = 4920695) B4920695
theorem B2186975 : Blo 2185435 2186975 := bstep (se 1 (by rfl) ⟨1640231, by rfl⟩ : syracuseStep 2186975 = 3280463) B3280463
theorem B3280469 : Blo 2185435 3280469 := bbase (se 8 (by rfl) ⟨19221, by rfl⟩ : syracuseStep 3280469 = 38443) (by norm_num)
theorem B2186979 : Blo 2185435 2186979 := bstep (se 1 (by rfl) ⟨1640234, by rfl⟩ : syracuseStep 2186979 = 3280469) B3280469
theorem B9341669 : Blo 2185435 9341669 := bbase (se 4 (by rfl) ⟨875781, by rfl⟩ : syracuseStep 9341669 = 1751563) (by norm_num)
theorem B6227779 : Blo 2185435 6227779 := bstep (se 1 (by rfl) ⟨4670834, by rfl⟩ : syracuseStep 6227779 = 9341669) B9341669
theorem B8303705 : Blo 2185435 8303705 := bstep (se 2 (by rfl) ⟨3113889, by rfl⟩ : syracuseStep 8303705 = 6227779) B6227779
theorem B5535803 : Blo 2185435 5535803 := bstep (se 1 (by rfl) ⟨4151852, by rfl⟩ : syracuseStep 5535803 = 8303705) B8303705
theorem B3690535 : Blo 2185435 3690535 := bstep (se 1 (by rfl) ⟨2767901, by rfl⟩ : syracuseStep 3690535 = 5535803) B5535803
theorem B4920713 : Blo 2185435 4920713 := bstep (se 2 (by rfl) ⟨1845267, by rfl⟩ : syracuseStep 4920713 = 3690535) B3690535
theorem B3280475 : Blo 2185435 3280475 := bstep (se 1 (by rfl) ⟨2460356, by rfl⟩ : syracuseStep 3280475 = 4920713) B4920713
theorem B2186983 : Blo 2185435 2186983 := bstep (se 1 (by rfl) ⟨1640237, by rfl⟩ : syracuseStep 2186983 = 3280475) B3280475
theorem B2460361 : Blo 2185435 2460361 := bbase (se 2 (by rfl) ⟨922635, by rfl⟩ : syracuseStep 2460361 = 1845271) (by norm_num)
theorem B3280481 : Blo 2185435 3280481 := bstep (se 2 (by rfl) ⟨1230180, by rfl⟩ : syracuseStep 3280481 = 2460361) B2460361
theorem B2186987 : Blo 2185435 2186987 := bstep (se 1 (by rfl) ⟨1640240, by rfl⟩ : syracuseStep 2186987 = 3280481) B3280481
theorem B7006277 : Blo 2185435 7006277 := bbase (se 4 (by rfl) ⟨656838, by rfl⟩ : syracuseStep 7006277 = 1313677) (by norm_num)
theorem B18683405 : Blo 2185435 18683405 := bstep (se 3 (by rfl) ⟨3503138, by rfl⟩ : syracuseStep 18683405 = 7006277) B7006277
theorem B12455603 : Blo 2185435 12455603 := bstep (se 1 (by rfl) ⟨9341702, by rfl⟩ : syracuseStep 12455603 = 18683405) B18683405
theorem B8303735 : Blo 2185435 8303735 := bstep (se 1 (by rfl) ⟨6227801, by rfl⟩ : syracuseStep 8303735 = 12455603) B12455603
theorem B5535823 : Blo 2185435 5535823 := bstep (se 1 (by rfl) ⟨4151867, by rfl⟩ : syracuseStep 5535823 = 8303735) B8303735
theorem B7381097 : Blo 2185435 7381097 := bstep (se 2 (by rfl) ⟨2767911, by rfl⟩ : syracuseStep 7381097 = 5535823) B5535823
theorem B4920731 : Blo 2185435 4920731 := bstep (se 1 (by rfl) ⟨3690548, by rfl⟩ : syracuseStep 4920731 = 7381097) B7381097
theorem B3280487 : Blo 2185435 3280487 := bstep (se 1 (by rfl) ⟨2460365, by rfl⟩ : syracuseStep 3280487 = 4920731) B4920731
theorem B2186991 : Blo 2185435 2186991 := bstep (se 1 (by rfl) ⟨1640243, by rfl⟩ : syracuseStep 2186991 = 3280487) B3280487
theorem B3280493 : Blo 2185435 3280493 := bbase (se 3 (by rfl) ⟨615092, by rfl⟩ : syracuseStep 3280493 = 1230185) (by norm_num)
theorem B2186995 : Blo 2185435 2186995 := bstep (se 1 (by rfl) ⟨1640246, by rfl⟩ : syracuseStep 2186995 = 3280493) B3280493
theorem B4920749 : Blo 2185435 4920749 := bbase (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) (by norm_num)
theorem B3280499 : Blo 2185435 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B2186999 : Blo 2185435 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B9975797 : Blo 2185435 9975797 := bbase (se 5 (by rfl) ⟨467615, by rfl⟩ : syracuseStep 9975797 = 935231) (by norm_num)
theorem B6650531 : Blo 2185435 6650531 := bstep (se 1 (by rfl) ⟨4987898, by rfl⟩ : syracuseStep 6650531 = 9975797) B9975797
theorem B4433687 : Blo 2185435 4433687 := bstep (se 1 (by rfl) ⟨3325265, by rfl⟩ : syracuseStep 4433687 = 6650531) B6650531
theorem B2955791 : Blo 2185435 2955791 := bstep (se 1 (by rfl) ⟨2216843, by rfl⟩ : syracuseStep 2955791 = 4433687) B4433687
theorem B7882109 : Blo 2185435 7882109 := bstep (se 3 (by rfl) ⟨1477895, by rfl⟩ : syracuseStep 7882109 = 2955791) B2955791
theorem B5254739 : Blo 2185435 5254739 := bstep (se 1 (by rfl) ⟨3941054, by rfl⟩ : syracuseStep 5254739 = 7882109) B7882109
theorem B3503159 : Blo 2185435 3503159 := bstep (se 1 (by rfl) ⟨2627369, by rfl⟩ : syracuseStep 3503159 = 5254739) B5254739
theorem B2335439 : Blo 2185435 2335439 := bstep (se 1 (by rfl) ⟨1751579, by rfl⟩ : syracuseStep 2335439 = 3503159) B3503159
theorem B6227837 : Blo 2185435 6227837 := bstep (se 3 (by rfl) ⟨1167719, by rfl⟩ : syracuseStep 6227837 = 2335439) B2335439
theorem B4151891 : Blo 2185435 4151891 := bstep (se 1 (by rfl) ⟨3113918, by rfl⟩ : syracuseStep 4151891 = 6227837) B6227837
theorem B2767927 : Blo 2185435 2767927 := bstep (se 1 (by rfl) ⟨2075945, by rfl⟩ : syracuseStep 2767927 = 4151891) B4151891
theorem B3690569 : Blo 2185435 3690569 := bstep (se 2 (by rfl) ⟨1383963, by rfl⟩ : syracuseStep 3690569 = 2767927) B2767927
theorem B2460379 : Blo 2185435 2460379 := bstep (se 1 (by rfl) ⟨1845284, by rfl⟩ : syracuseStep 2460379 = 3690569) B3690569
theorem B3280505 : Blo 2185435 3280505 := bstep (se 2 (by rfl) ⟨1230189, by rfl⟩ : syracuseStep 3280505 = 2460379) B2460379
theorem B2187003 : Blo 2185435 2187003 := bstep (se 1 (by rfl) ⟨1640252, by rfl⟩ : syracuseStep 2187003 = 3280505) B3280505
theorem B10249877 : Blo 2185435 10249877 := bbase (se 6 (by rfl) ⟨240231, by rfl⟩ : syracuseStep 10249877 = 480463) (by norm_num)
theorem B6833251 : Blo 2185435 6833251 := bstep (se 1 (by rfl) ⟨5124938, by rfl⟩ : syracuseStep 6833251 = 10249877) B10249877
theorem B9111001 : Blo 2185435 9111001 := bstep (se 2 (by rfl) ⟨3416625, by rfl⟩ : syracuseStep 9111001 = 6833251) B6833251
theorem B12148001 : Blo 2185435 12148001 := bstep (se 2 (by rfl) ⟨4555500, by rfl⟩ : syracuseStep 12148001 = 9111001) B9111001
theorem B8098667 : Blo 2185435 8098667 := bstep (se 1 (by rfl) ⟨6074000, by rfl⟩ : syracuseStep 8098667 = 12148001) B12148001
theorem B5399111 : Blo 2185435 5399111 := bstep (se 1 (by rfl) ⟨4049333, by rfl⟩ : syracuseStep 5399111 = 8098667) B8098667
theorem B3599407 : Blo 2185435 3599407 := bstep (se 1 (by rfl) ⟨2699555, by rfl⟩ : syracuseStep 3599407 = 5399111) B5399111
theorem B4799209 : Blo 2185435 4799209 := bstep (se 2 (by rfl) ⟨1799703, by rfl⟩ : syracuseStep 4799209 = 3599407) B3599407
theorem B6398945 : Blo 2185435 6398945 := bstep (se 2 (by rfl) ⟨2399604, by rfl⟩ : syracuseStep 6398945 = 4799209) B4799209
theorem B4265963 : Blo 2185435 4265963 := bstep (se 1 (by rfl) ⟨3199472, by rfl⟩ : syracuseStep 4265963 = 6398945) B6398945
theorem B2843975 : Blo 2185435 2843975 := bstep (se 1 (by rfl) ⟨2132981, by rfl⟩ : syracuseStep 2843975 = 4265963) B4265963
theorem B7583933 : Blo 2185435 7583933 := bstep (se 3 (by rfl) ⟨1421987, by rfl⟩ : syracuseStep 7583933 = 2843975) B2843975
theorem B5055955 : Blo 2185435 5055955 := bstep (se 1 (by rfl) ⟨3791966, by rfl⟩ : syracuseStep 5055955 = 7583933) B7583933
theorem B107860373 : Blo 2185435 107860373 := bstep (se 6 (by rfl) ⟨2527977, by rfl⟩ : syracuseStep 107860373 = 5055955) B5055955
theorem B71906915 : Blo 2185435 71906915 := bstep (se 1 (by rfl) ⟨53930186, by rfl⟩ : syracuseStep 71906915 = 107860373) B107860373
theorem B47937943 : Blo 2185435 47937943 := bstep (se 1 (by rfl) ⟨35953457, by rfl⟩ : syracuseStep 47937943 = 71906915) B71906915
theorem B63917257 : Blo 2185435 63917257 := bstep (se 2 (by rfl) ⟨23968971, by rfl⟩ : syracuseStep 63917257 = 47937943) B47937943
theorem B85223009 : Blo 2185435 85223009 := bstep (se 2 (by rfl) ⟨31958628, by rfl⟩ : syracuseStep 85223009 = 63917257) B63917257
theorem B56815339 : Blo 2185435 56815339 := bstep (se 1 (by rfl) ⟨42611504, by rfl⟩ : syracuseStep 56815339 = 85223009) B85223009
theorem B75753785 : Blo 2185435 75753785 := bstep (se 2 (by rfl) ⟨28407669, by rfl⟩ : syracuseStep 75753785 = 56815339) B56815339
theorem B50502523 : Blo 2185435 50502523 := bstep (se 1 (by rfl) ⟨37876892, by rfl⟩ : syracuseStep 50502523 = 75753785) B75753785
theorem B67336697 : Blo 2185435 67336697 := bstep (se 2 (by rfl) ⟨25251261, by rfl⟩ : syracuseStep 67336697 = 50502523) B50502523
theorem B179564525 : Blo 2185435 179564525 := bstep (se 3 (by rfl) ⟨33668348, by rfl⟩ : syracuseStep 179564525 = 67336697) B67336697
theorem B119709683 : Blo 2185435 119709683 := bstep (se 1 (by rfl) ⟨89782262, by rfl⟩ : syracuseStep 119709683 = 179564525) B179564525
theorem B79806455 : Blo 2185435 79806455 := bstep (se 1 (by rfl) ⟨59854841, by rfl⟩ : syracuseStep 79806455 = 119709683) B119709683
theorem B53204303 : Blo 2185435 53204303 := bstep (se 1 (by rfl) ⟨39903227, by rfl⟩ : syracuseStep 53204303 = 79806455) B79806455
theorem B141878141 : Blo 2185435 141878141 := bstep (se 3 (by rfl) ⟨26602151, by rfl⟩ : syracuseStep 141878141 = 53204303) B53204303
theorem B94585427 : Blo 2185435 94585427 := bstep (se 1 (by rfl) ⟨70939070, by rfl⟩ : syracuseStep 94585427 = 141878141) B141878141
theorem B63056951 : Blo 2185435 63056951 := bstep (se 1 (by rfl) ⟨47292713, by rfl⟩ : syracuseStep 63056951 = 94585427) B94585427
theorem B42037967 : Blo 2185435 42037967 := bstep (se 1 (by rfl) ⟨31528475, by rfl⟩ : syracuseStep 42037967 = 63056951) B63056951
theorem B28025311 : Blo 2185435 28025311 := bstep (se 1 (by rfl) ⟨21018983, by rfl⟩ : syracuseStep 28025311 = 42037967) B42037967
theorem B37367081 : Blo 2185435 37367081 := bstep (se 2 (by rfl) ⟨14012655, by rfl⟩ : syracuseStep 37367081 = 28025311) B28025311
theorem B24911387 : Blo 2185435 24911387 := bstep (se 1 (by rfl) ⟨18683540, by rfl⟩ : syracuseStep 24911387 = 37367081) B37367081
theorem B16607591 : Blo 2185435 16607591 := bstep (se 1 (by rfl) ⟨12455693, by rfl⟩ : syracuseStep 16607591 = 24911387) B24911387
theorem B11071727 : Blo 2185435 11071727 := bstep (se 1 (by rfl) ⟨8303795, by rfl⟩ : syracuseStep 11071727 = 16607591) B16607591
theorem B7381151 : Blo 2185435 7381151 := bstep (se 1 (by rfl) ⟨5535863, by rfl⟩ : syracuseStep 7381151 = 11071727) B11071727
theorem B4920767 : Blo 2185435 4920767 := bstep (se 1 (by rfl) ⟨3690575, by rfl⟩ : syracuseStep 4920767 = 7381151) B7381151
theorem B3280511 : Blo 2185435 3280511 := bstep (se 1 (by rfl) ⟨2460383, by rfl⟩ : syracuseStep 3280511 = 4920767) B4920767
theorem B2187007 : Blo 2185435 2187007 := bstep (se 1 (by rfl) ⟨1640255, by rfl⟩ : syracuseStep 2187007 = 3280511) B3280511
theorem B3280517 : Blo 2185435 3280517 := bbase (se 4 (by rfl) ⟨307548, by rfl⟩ : syracuseStep 3280517 = 615097) (by norm_num)
theorem B2187011 : Blo 2185435 2187011 := bstep (se 1 (by rfl) ⟨1640258, by rfl⟩ : syracuseStep 2187011 = 3280517) B3280517
theorem B3690589 : Blo 2185435 3690589 := bbase (se 3 (by rfl) ⟨691985, by rfl⟩ : syracuseStep 3690589 = 1383971) (by norm_num)
theorem B4920785 : Blo 2185435 4920785 := bstep (se 2 (by rfl) ⟨1845294, by rfl⟩ : syracuseStep 4920785 = 3690589) B3690589
theorem B3280523 : Blo 2185435 3280523 := bstep (se 1 (by rfl) ⟨2460392, by rfl⟩ : syracuseStep 3280523 = 4920785) B4920785
theorem B2187015 : Blo 2185435 2187015 := bstep (se 1 (by rfl) ⟨1640261, by rfl⟩ : syracuseStep 2187015 = 3280523) B3280523
theorem B2460397 : Blo 2185435 2460397 := bbase (se 3 (by rfl) ⟨461324, by rfl⟩ : syracuseStep 2460397 = 922649) (by norm_num)
theorem B3280529 : Blo 2185435 3280529 := bstep (se 2 (by rfl) ⟨1230198, by rfl⟩ : syracuseStep 3280529 = 2460397) B2460397
theorem B2187019 : Blo 2185435 2187019 := bstep (se 1 (by rfl) ⟨1640264, by rfl⟩ : syracuseStep 2187019 = 3280529) B3280529
theorem B7381205 : Blo 2185435 7381205 := bbase (se 7 (by rfl) ⟨86498, by rfl⟩ : syracuseStep 7381205 = 172997) (by norm_num)
theorem B4920803 : Blo 2185435 4920803 := bstep (se 1 (by rfl) ⟨3690602, by rfl⟩ : syracuseStep 4920803 = 7381205) B7381205
theorem B3280535 : Blo 2185435 3280535 := bstep (se 1 (by rfl) ⟨2460401, by rfl⟩ : syracuseStep 3280535 = 4920803) B4920803
theorem B2187023 : Blo 2185435 2187023 := bstep (se 1 (by rfl) ⟨1640267, by rfl⟩ : syracuseStep 2187023 = 3280535) B3280535
theorem B3280541 : Blo 2185435 3280541 := bbase (se 3 (by rfl) ⟨615101, by rfl⟩ : syracuseStep 3280541 = 1230203) (by norm_num)
theorem B2187027 : Blo 2185435 2187027 := bstep (se 1 (by rfl) ⟨1640270, by rfl⟩ : syracuseStep 2187027 = 3280541) B3280541
theorem B4920821 : Blo 2185435 4920821 := bbase (se 5 (by rfl) ⟨230663, by rfl⟩ : syracuseStep 4920821 = 461327) (by norm_num)
theorem B3280547 : Blo 2185435 3280547 := bstep (se 1 (by rfl) ⟨2460410, by rfl⟩ : syracuseStep 3280547 = 4920821) B4920821
theorem B2187031 : Blo 2185435 2187031 := bstep (se 1 (by rfl) ⟨1640273, by rfl⟩ : syracuseStep 2187031 = 3280547) B3280547
theorem B2493985 : Blo 2185435 2493985 := bbase (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) (by norm_num)
theorem B3325313 : Blo 2185435 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2216875 : Blo 2185435 2216875 := bstep (se 1 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 2216875 = 3325313) B3325313
theorem B2955833 : Blo 2185435 2955833 := bstep (se 2 (by rfl) ⟨1108437, by rfl⟩ : syracuseStep 2955833 = 2216875) B2216875
theorem B31528885 : Blo 2185435 31528885 := bstep (se 5 (by rfl) ⟨1477916, by rfl⟩ : syracuseStep 31528885 = 2955833) B2955833
theorem B42038513 : Blo 2185435 42038513 := bstep (se 2 (by rfl) ⟨15764442, by rfl⟩ : syracuseStep 42038513 = 31528885) B31528885
theorem B28025675 : Blo 2185435 28025675 := bstep (se 1 (by rfl) ⟨21019256, by rfl⟩ : syracuseStep 28025675 = 42038513) B42038513
theorem B18683783 : Blo 2185435 18683783 := bstep (se 1 (by rfl) ⟨14012837, by rfl⟩ : syracuseStep 18683783 = 28025675) B28025675
theorem B12455855 : Blo 2185435 12455855 := bstep (se 1 (by rfl) ⟨9341891, by rfl⟩ : syracuseStep 12455855 = 18683783) B18683783
theorem B8303903 : Blo 2185435 8303903 := bstep (se 1 (by rfl) ⟨6227927, by rfl⟩ : syracuseStep 8303903 = 12455855) B12455855
theorem B5535935 : Blo 2185435 5535935 := bstep (se 1 (by rfl) ⟨4151951, by rfl⟩ : syracuseStep 5535935 = 8303903) B8303903
theorem B3690623 : Blo 2185435 3690623 := bstep (se 1 (by rfl) ⟨2767967, by rfl⟩ : syracuseStep 3690623 = 5535935) B5535935
theorem B2460415 : Blo 2185435 2460415 := bstep (se 1 (by rfl) ⟨1845311, by rfl⟩ : syracuseStep 2460415 = 3690623) B3690623
theorem B3280553 : Blo 2185435 3280553 := bstep (se 2 (by rfl) ⟨1230207, by rfl⟩ : syracuseStep 3280553 = 2460415) B2460415
theorem B2187035 : Blo 2185435 2187035 := bstep (se 1 (by rfl) ⟨1640276, by rfl⟩ : syracuseStep 2187035 = 3280553) B3280553
theorem B2335477 : Blo 2185435 2335477 := bbase (se 5 (by rfl) ⟨109475, by rfl⟩ : syracuseStep 2335477 = 218951) (by norm_num)
theorem B3113969 : Blo 2185435 3113969 := bstep (se 2 (by rfl) ⟨1167738, by rfl⟩ : syracuseStep 3113969 = 2335477) B2335477
theorem B8303917 : Blo 2185435 8303917 := bstep (se 3 (by rfl) ⟨1556984, by rfl⟩ : syracuseStep 8303917 = 3113969) B3113969
theorem B11071889 : Blo 2185435 11071889 := bstep (se 2 (by rfl) ⟨4151958, by rfl⟩ : syracuseStep 11071889 = 8303917) B8303917
theorem B7381259 : Blo 2185435 7381259 := bstep (se 1 (by rfl) ⟨5535944, by rfl⟩ : syracuseStep 7381259 = 11071889) B11071889
theorem B4920839 : Blo 2185435 4920839 := bstep (se 1 (by rfl) ⟨3690629, by rfl⟩ : syracuseStep 4920839 = 7381259) B7381259
theorem B3280559 : Blo 2185435 3280559 := bstep (se 1 (by rfl) ⟨2460419, by rfl⟩ : syracuseStep 3280559 = 4920839) B4920839
theorem B2187039 : Blo 2185435 2187039 := bstep (se 1 (by rfl) ⟨1640279, by rfl⟩ : syracuseStep 2187039 = 3280559) B3280559
theorem B3280565 : Blo 2185435 3280565 := bbase (se 5 (by rfl) ⟨153776, by rfl⟩ : syracuseStep 3280565 = 307553) (by norm_num)
theorem B2187043 : Blo 2185435 2187043 := bstep (se 1 (by rfl) ⟨1640282, by rfl⟩ : syracuseStep 2187043 = 3280565) B3280565
theorem B5535965 : Blo 2185435 5535965 := bbase (se 3 (by rfl) ⟨1037993, by rfl⟩ : syracuseStep 5535965 = 2075987) (by norm_num)
theorem B3690643 : Blo 2185435 3690643 := bstep (se 1 (by rfl) ⟨2767982, by rfl⟩ : syracuseStep 3690643 = 5535965) B5535965
theorem B4920857 : Blo 2185435 4920857 := bstep (se 2 (by rfl) ⟨1845321, by rfl⟩ : syracuseStep 4920857 = 3690643) B3690643
theorem B3280571 : Blo 2185435 3280571 := bstep (se 1 (by rfl) ⟨2460428, by rfl⟩ : syracuseStep 3280571 = 4920857) B4920857
theorem B2187047 : Blo 2185435 2187047 := bstep (se 1 (by rfl) ⟨1640285, by rfl⟩ : syracuseStep 2187047 = 3280571) B3280571
theorem B2460433 : Blo 2185435 2460433 := bbase (se 2 (by rfl) ⟨922662, by rfl⟩ : syracuseStep 2460433 = 1845325) (by norm_num)
theorem B3280577 : Blo 2185435 3280577 := bstep (se 2 (by rfl) ⟨1230216, by rfl⟩ : syracuseStep 3280577 = 2460433) B2460433
theorem B2187051 : Blo 2185435 2187051 := bstep (se 1 (by rfl) ⟨1640288, by rfl⟩ : syracuseStep 2187051 = 3280577) B3280577
theorem B4151989 : Blo 2185435 4151989 := bbase (se 5 (by rfl) ⟨194624, by rfl⟩ : syracuseStep 4151989 = 389249) (by norm_num)
theorem B5535985 : Blo 2185435 5535985 := bstep (se 2 (by rfl) ⟨2075994, by rfl⟩ : syracuseStep 5535985 = 4151989) B4151989
theorem B7381313 : Blo 2185435 7381313 := bstep (se 2 (by rfl) ⟨2767992, by rfl⟩ : syracuseStep 7381313 = 5535985) B5535985
theorem B4920875 : Blo 2185435 4920875 := bstep (se 1 (by rfl) ⟨3690656, by rfl⟩ : syracuseStep 4920875 = 7381313) B7381313
theorem B3280583 : Blo 2185435 3280583 := bstep (se 1 (by rfl) ⟨2460437, by rfl⟩ : syracuseStep 3280583 = 4920875) B4920875
theorem B2187055 : Blo 2185435 2187055 := bstep (se 1 (by rfl) ⟨1640291, by rfl⟩ : syracuseStep 2187055 = 3280583) B3280583
theorem B3280589 : Blo 2185435 3280589 := bbase (se 3 (by rfl) ⟨615110, by rfl⟩ : syracuseStep 3280589 = 1230221) (by norm_num)
theorem B2187059 : Blo 2185435 2187059 := bstep (se 1 (by rfl) ⟨1640294, by rfl⟩ : syracuseStep 2187059 = 3280589) B3280589
theorem B4920893 : Blo 2185435 4920893 := bbase (se 3 (by rfl) ⟨922667, by rfl⟩ : syracuseStep 4920893 = 1845335) (by norm_num)
theorem B3280595 : Blo 2185435 3280595 := bstep (se 1 (by rfl) ⟨2460446, by rfl⟩ : syracuseStep 3280595 = 4920893) B4920893
theorem B2187063 : Blo 2185435 2187063 := bstep (se 1 (by rfl) ⟨1640297, by rfl⟩ : syracuseStep 2187063 = 3280595) B3280595
theorem B3690677 : Blo 2185435 3690677 := bbase (se 5 (by rfl) ⟨173000, by rfl⟩ : syracuseStep 3690677 = 346001) (by norm_num)
theorem B2460451 : Blo 2185435 2460451 := bstep (se 1 (by rfl) ⟨1845338, by rfl⟩ : syracuseStep 2460451 = 3690677) B3690677
theorem B3280601 : Blo 2185435 3280601 := bstep (se 2 (by rfl) ⟨1230225, by rfl⟩ : syracuseStep 3280601 = 2460451) B2460451
theorem B2187067 : Blo 2185435 2187067 := bstep (se 1 (by rfl) ⟨1640300, by rfl⟩ : syracuseStep 2187067 = 3280601) B3280601
theorem B5254901 : Blo 2185435 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B3503267 : Blo 2185435 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B2335511 : Blo 2185435 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B6228029 : Blo 2185435 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B16608077 : Blo 2185435 16608077 := bstep (se 3 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 16608077 = 6228029) B6228029
theorem B11072051 : Blo 2185435 11072051 := bstep (se 1 (by rfl) ⟨8304038, by rfl⟩ : syracuseStep 11072051 = 16608077) B16608077
theorem B7381367 : Blo 2185435 7381367 := bstep (se 1 (by rfl) ⟨5536025, by rfl⟩ : syracuseStep 7381367 = 11072051) B11072051
theorem B4920911 : Blo 2185435 4920911 := bstep (se 1 (by rfl) ⟨3690683, by rfl⟩ : syracuseStep 4920911 = 7381367) B7381367
theorem B3280607 : Blo 2185435 3280607 := bstep (se 1 (by rfl) ⟨2460455, by rfl⟩ : syracuseStep 3280607 = 4920911) B4920911
theorem B2187071 : Blo 2185435 2187071 := bstep (se 1 (by rfl) ⟨1640303, by rfl⟩ : syracuseStep 2187071 = 3280607) B3280607
theorem B3280613 : Blo 2185435 3280613 := bbase (se 4 (by rfl) ⟨307557, by rfl⟩ : syracuseStep 3280613 = 615115) (by norm_num)
theorem B2187075 : Blo 2185435 2187075 := bstep (se 1 (by rfl) ⟨1640306, by rfl⟩ : syracuseStep 2187075 = 3280613) B3280613
theorem B6228053 : Blo 2185435 6228053 := bbase (se 8 (by rfl) ⟨36492, by rfl⟩ : syracuseStep 6228053 = 72985) (by norm_num)
theorem B4152035 : Blo 2185435 4152035 := bstep (se 1 (by rfl) ⟨3114026, by rfl⟩ : syracuseStep 4152035 = 6228053) B6228053
theorem B2768023 : Blo 2185435 2768023 := bstep (se 1 (by rfl) ⟨2076017, by rfl⟩ : syracuseStep 2768023 = 4152035) B4152035
theorem B3690697 : Blo 2185435 3690697 := bstep (se 2 (by rfl) ⟨1384011, by rfl⟩ : syracuseStep 3690697 = 2768023) B2768023
theorem B4920929 : Blo 2185435 4920929 := bstep (se 2 (by rfl) ⟨1845348, by rfl⟩ : syracuseStep 4920929 = 3690697) B3690697
theorem B3280619 : Blo 2185435 3280619 := bstep (se 1 (by rfl) ⟨2460464, by rfl⟩ : syracuseStep 3280619 = 4920929) B4920929
theorem B2187079 : Blo 2185435 2187079 := bstep (se 1 (by rfl) ⟨1640309, by rfl⟩ : syracuseStep 2187079 = 3280619) B3280619
theorem B2460469 : Blo 2185435 2460469 := bbase (se 5 (by rfl) ⟨115334, by rfl⟩ : syracuseStep 2460469 = 230669) (by norm_num)
theorem B3280625 : Blo 2185435 3280625 := bstep (se 2 (by rfl) ⟨1230234, by rfl⟩ : syracuseStep 3280625 = 2460469) B2460469
theorem B2187083 : Blo 2185435 2187083 := bstep (se 1 (by rfl) ⟨1640312, by rfl⟩ : syracuseStep 2187083 = 3280625) B3280625
theorem B2768033 : Blo 2185435 2768033 := bbase (se 2 (by rfl) ⟨1038012, by rfl⟩ : syracuseStep 2768033 = 2076025) (by norm_num)
theorem B7381421 : Blo 2185435 7381421 := bstep (se 3 (by rfl) ⟨1384016, by rfl⟩ : syracuseStep 7381421 = 2768033) B2768033
theorem B4920947 : Blo 2185435 4920947 := bstep (se 1 (by rfl) ⟨3690710, by rfl⟩ : syracuseStep 4920947 = 7381421) B7381421
theorem B3280631 : Blo 2185435 3280631 := bstep (se 1 (by rfl) ⟨2460473, by rfl⟩ : syracuseStep 3280631 = 4920947) B4920947
theorem B2187087 : Blo 2185435 2187087 := bstep (se 1 (by rfl) ⟨1640315, by rfl⟩ : syracuseStep 2187087 = 3280631) B3280631
theorem B3280637 : Blo 2185435 3280637 := bbase (se 3 (by rfl) ⟨615119, by rfl⟩ : syracuseStep 3280637 = 1230239) (by norm_num)
theorem B2187091 : Blo 2185435 2187091 := bstep (se 1 (by rfl) ⟨1640318, by rfl⟩ : syracuseStep 2187091 = 3280637) B3280637
theorem B4920965 : Blo 2185435 4920965 := bbase (se 4 (by rfl) ⟨461340, by rfl⟩ : syracuseStep 4920965 = 922681) (by norm_num)
theorem B3280643 : Blo 2185435 3280643 := bstep (se 1 (by rfl) ⟨2460482, by rfl⟩ : syracuseStep 3280643 = 4920965) B4920965
theorem B2187095 : Blo 2185435 2187095 := bstep (se 1 (by rfl) ⟨1640321, by rfl⟩ : syracuseStep 2187095 = 3280643) B3280643
theorem B4988117 : Blo 2185435 4988117 := bbase (se 7 (by rfl) ⟨58454, by rfl⟩ : syracuseStep 4988117 = 116909) (by norm_num)
theorem B3325411 : Blo 2185435 3325411 := bstep (se 1 (by rfl) ⟨2494058, by rfl⟩ : syracuseStep 3325411 = 4988117) B4988117
theorem B4433881 : Blo 2185435 4433881 := bstep (se 2 (by rfl) ⟨1662705, by rfl⟩ : syracuseStep 4433881 = 3325411) B3325411
theorem B5911841 : Blo 2185435 5911841 := bstep (se 2 (by rfl) ⟨2216940, by rfl⟩ : syracuseStep 5911841 = 4433881) B4433881
theorem B3941227 : Blo 2185435 3941227 := bstep (se 1 (by rfl) ⟨2955920, by rfl⟩ : syracuseStep 3941227 = 5911841) B5911841
theorem B5254969 : Blo 2185435 5254969 := bstep (se 2 (by rfl) ⟨1970613, by rfl⟩ : syracuseStep 5254969 = 3941227) B3941227
theorem B7006625 : Blo 2185435 7006625 := bstep (se 2 (by rfl) ⟨2627484, by rfl⟩ : syracuseStep 7006625 = 5254969) B5254969
theorem B4671083 : Blo 2185435 4671083 := bstep (se 1 (by rfl) ⟨3503312, by rfl⟩ : syracuseStep 4671083 = 7006625) B7006625
theorem B3114055 : Blo 2185435 3114055 := bstep (se 1 (by rfl) ⟨2335541, by rfl⟩ : syracuseStep 3114055 = 4671083) B4671083
theorem B4152073 : Blo 2185435 4152073 := bstep (se 2 (by rfl) ⟨1557027, by rfl⟩ : syracuseStep 4152073 = 3114055) B3114055
theorem B5536097 : Blo 2185435 5536097 := bstep (se 2 (by rfl) ⟨2076036, by rfl⟩ : syracuseStep 5536097 = 4152073) B4152073
theorem B3690731 : Blo 2185435 3690731 := bstep (se 1 (by rfl) ⟨2768048, by rfl⟩ : syracuseStep 3690731 = 5536097) B5536097
theorem B2460487 : Blo 2185435 2460487 := bstep (se 1 (by rfl) ⟨1845365, by rfl⟩ : syracuseStep 2460487 = 3690731) B3690731
theorem B3280649 : Blo 2185435 3280649 := bstep (se 2 (by rfl) ⟨1230243, by rfl⟩ : syracuseStep 3280649 = 2460487) B2460487
theorem B2187099 : Blo 2185435 2187099 := bstep (se 1 (by rfl) ⟨1640324, by rfl⟩ : syracuseStep 2187099 = 3280649) B3280649
theorem B11072213 : Blo 2185435 11072213 := bbase (se 7 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 11072213 = 259505) (by norm_num)
theorem B7381475 : Blo 2185435 7381475 := bstep (se 1 (by rfl) ⟨5536106, by rfl⟩ : syracuseStep 7381475 = 11072213) B11072213
theorem B4920983 : Blo 2185435 4920983 := bstep (se 1 (by rfl) ⟨3690737, by rfl⟩ : syracuseStep 4920983 = 7381475) B7381475
theorem B3280655 : Blo 2185435 3280655 := bstep (se 1 (by rfl) ⟨2460491, by rfl⟩ : syracuseStep 3280655 = 4920983) B4920983
theorem B2187103 : Blo 2185435 2187103 := bstep (se 1 (by rfl) ⟨1640327, by rfl⟩ : syracuseStep 2187103 = 3280655) B3280655
theorem B3280661 : Blo 2185435 3280661 := bbase (se 6 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 3280661 = 153781) (by norm_num)
theorem B2187107 : Blo 2185435 2187107 := bstep (se 1 (by rfl) ⟨1640330, by rfl⟩ : syracuseStep 2187107 = 3280661) B3280661
theorem B3995021 : Blo 2185435 3995021 := bbase (se 3 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 3995021 = 1498133) (by norm_num)
theorem B2663347 : Blo 2185435 2663347 := bstep (se 1 (by rfl) ⟨1997510, by rfl⟩ : syracuseStep 2663347 = 3995021) B3995021
theorem B3551129 : Blo 2185435 3551129 := bstep (se 2 (by rfl) ⟨1331673, by rfl⟩ : syracuseStep 3551129 = 2663347) B2663347
theorem B2367419 : Blo 2185435 2367419 := bstep (se 1 (by rfl) ⟨1775564, by rfl⟩ : syracuseStep 2367419 = 3551129) B3551129
theorem B25252469 : Blo 2185435 25252469 := bstep (se 5 (by rfl) ⟨1183709, by rfl⟩ : syracuseStep 25252469 = 2367419) B2367419
theorem B16834979 : Blo 2185435 16834979 := bstep (se 1 (by rfl) ⟨12626234, by rfl⟩ : syracuseStep 16834979 = 25252469) B25252469
theorem B44893277 : Blo 2185435 44893277 := bstep (se 3 (by rfl) ⟨8417489, by rfl⟩ : syracuseStep 44893277 = 16834979) B16834979
theorem B29928851 : Blo 2185435 29928851 := bstep (se 1 (by rfl) ⟨22446638, by rfl⟩ : syracuseStep 29928851 = 44893277) B44893277
theorem B19952567 : Blo 2185435 19952567 := bstep (se 1 (by rfl) ⟨14964425, by rfl⟩ : syracuseStep 19952567 = 29928851) B29928851
theorem B13301711 : Blo 2185435 13301711 := bstep (se 1 (by rfl) ⟨9976283, by rfl⟩ : syracuseStep 13301711 = 19952567) B19952567
theorem B8867807 : Blo 2185435 8867807 := bstep (se 1 (by rfl) ⟨6650855, by rfl⟩ : syracuseStep 8867807 = 13301711) B13301711
theorem B5911871 : Blo 2185435 5911871 := bstep (se 1 (by rfl) ⟨4433903, by rfl⟩ : syracuseStep 5911871 = 8867807) B8867807
theorem B63059957 : Blo 2185435 63059957 := bstep (se 5 (by rfl) ⟨2955935, by rfl⟩ : syracuseStep 63059957 = 5911871) B5911871
theorem B42039971 : Blo 2185435 42039971 := bstep (se 1 (by rfl) ⟨31529978, by rfl⟩ : syracuseStep 42039971 = 63059957) B63059957
theorem B28026647 : Blo 2185435 28026647 := bstep (se 1 (by rfl) ⟨21019985, by rfl⟩ : syracuseStep 28026647 = 42039971) B42039971
theorem B18684431 : Blo 2185435 18684431 := bstep (se 1 (by rfl) ⟨14013323, by rfl⟩ : syracuseStep 18684431 = 28026647) B28026647
theorem B12456287 : Blo 2185435 12456287 := bstep (se 1 (by rfl) ⟨9342215, by rfl⟩ : syracuseStep 12456287 = 18684431) B18684431
theorem B8304191 : Blo 2185435 8304191 := bstep (se 1 (by rfl) ⟨6228143, by rfl⟩ : syracuseStep 8304191 = 12456287) B12456287
theorem B5536127 : Blo 2185435 5536127 := bstep (se 1 (by rfl) ⟨4152095, by rfl⟩ : syracuseStep 5536127 = 8304191) B8304191
theorem B3690751 : Blo 2185435 3690751 := bstep (se 1 (by rfl) ⟨2768063, by rfl⟩ : syracuseStep 3690751 = 5536127) B5536127
theorem B4921001 : Blo 2185435 4921001 := bstep (se 2 (by rfl) ⟨1845375, by rfl⟩ : syracuseStep 4921001 = 3690751) B3690751
theorem B3280667 : Blo 2185435 3280667 := bstep (se 1 (by rfl) ⟨2460500, by rfl⟩ : syracuseStep 3280667 = 4921001) B4921001
theorem B2187111 : Blo 2185435 2187111 := bstep (se 1 (by rfl) ⟨1640333, by rfl⟩ : syracuseStep 2187111 = 3280667) B3280667
theorem B2460505 : Blo 2185435 2460505 := bbase (se 2 (by rfl) ⟨922689, by rfl⟩ : syracuseStep 2460505 = 1845379) (by norm_num)
theorem B3280673 : Blo 2185435 3280673 := bstep (se 2 (by rfl) ⟨1230252, by rfl⟩ : syracuseStep 3280673 = 2460505) B2460505
theorem B2187115 : Blo 2185435 2187115 := bstep (se 1 (by rfl) ⟨1640336, by rfl⟩ : syracuseStep 2187115 = 3280673) B3280673
theorem B4671125 : Blo 2185435 4671125 := bbase (se 6 (by rfl) ⟨109479, by rfl⟩ : syracuseStep 4671125 = 218959) (by norm_num)
theorem B3114083 : Blo 2185435 3114083 := bstep (se 1 (by rfl) ⟨2335562, by rfl⟩ : syracuseStep 3114083 = 4671125) B4671125
theorem B8304221 : Blo 2185435 8304221 := bstep (se 3 (by rfl) ⟨1557041, by rfl⟩ : syracuseStep 8304221 = 3114083) B3114083
theorem B5536147 : Blo 2185435 5536147 := bstep (se 1 (by rfl) ⟨4152110, by rfl⟩ : syracuseStep 5536147 = 8304221) B8304221
theorem B7381529 : Blo 2185435 7381529 := bstep (se 2 (by rfl) ⟨2768073, by rfl⟩ : syracuseStep 7381529 = 5536147) B5536147
theorem B4921019 : Blo 2185435 4921019 := bstep (se 1 (by rfl) ⟨3690764, by rfl⟩ : syracuseStep 4921019 = 7381529) B7381529
theorem B3280679 : Blo 2185435 3280679 := bstep (se 1 (by rfl) ⟨2460509, by rfl⟩ : syracuseStep 3280679 = 4921019) B4921019
theorem B2187119 : Blo 2185435 2187119 := bstep (se 1 (by rfl) ⟨1640339, by rfl⟩ : syracuseStep 2187119 = 3280679) B3280679
theorem B3280685 : Blo 2185435 3280685 := bbase (se 3 (by rfl) ⟨615128, by rfl⟩ : syracuseStep 3280685 = 1230257) (by norm_num)
theorem B2187123 : Blo 2185435 2187123 := bstep (se 1 (by rfl) ⟨1640342, by rfl⟩ : syracuseStep 2187123 = 3280685) B3280685
theorem B4921037 : Blo 2185435 4921037 := bbase (se 3 (by rfl) ⟨922694, by rfl⟩ : syracuseStep 4921037 = 1845389) (by norm_num)
theorem B3280691 : Blo 2185435 3280691 := bstep (se 1 (by rfl) ⟨2460518, by rfl⟩ : syracuseStep 3280691 = 4921037) B4921037
theorem B2187127 : Blo 2185435 2187127 := bstep (se 1 (by rfl) ⟨1640345, by rfl⟩ : syracuseStep 2187127 = 3280691) B3280691
theorem B2768089 : Blo 2185435 2768089 := bbase (se 2 (by rfl) ⟨1038033, by rfl⟩ : syracuseStep 2768089 = 2076067) (by norm_num)
theorem B3690785 : Blo 2185435 3690785 := bstep (se 2 (by rfl) ⟨1384044, by rfl⟩ : syracuseStep 3690785 = 2768089) B2768089
theorem B2460523 : Blo 2185435 2460523 := bstep (se 1 (by rfl) ⟨1845392, by rfl⟩ : syracuseStep 2460523 = 3690785) B3690785
theorem B3280697 : Blo 2185435 3280697 := bstep (se 2 (by rfl) ⟨1230261, by rfl⟩ : syracuseStep 3280697 = 2460523) B2460523
theorem B2187131 : Blo 2185435 2187131 := bstep (se 1 (by rfl) ⟨1640348, by rfl⟩ : syracuseStep 2187131 = 3280697) B3280697
theorem B3741149 : Blo 2185435 3741149 := bbase (se 3 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 3741149 = 1402931) (by norm_num)
theorem B2494099 : Blo 2185435 2494099 := bstep (se 1 (by rfl) ⟨1870574, by rfl⟩ : syracuseStep 2494099 = 3741149) B3741149
theorem B3325465 : Blo 2185435 3325465 := bstep (se 2 (by rfl) ⟨1247049, by rfl⟩ : syracuseStep 3325465 = 2494099) B2494099
theorem B4433953 : Blo 2185435 4433953 := bstep (se 2 (by rfl) ⟨1662732, by rfl⟩ : syracuseStep 4433953 = 3325465) B3325465
theorem B5911937 : Blo 2185435 5911937 := bstep (se 2 (by rfl) ⟨2216976, by rfl⟩ : syracuseStep 5911937 = 4433953) B4433953
theorem B3941291 : Blo 2185435 3941291 := bstep (se 1 (by rfl) ⟨2955968, by rfl⟩ : syracuseStep 3941291 = 5911937) B5911937
theorem B2627527 : Blo 2185435 2627527 := bstep (se 1 (by rfl) ⟨1970645, by rfl⟩ : syracuseStep 2627527 = 3941291) B3941291
theorem B3503369 : Blo 2185435 3503369 := bstep (se 2 (by rfl) ⟨1313763, by rfl⟩ : syracuseStep 3503369 = 2627527) B2627527
theorem B9342317 : Blo 2185435 9342317 := bstep (se 3 (by rfl) ⟨1751684, by rfl⟩ : syracuseStep 9342317 = 3503369) B3503369
theorem B24912845 : Blo 2185435 24912845 := bstep (se 3 (by rfl) ⟨4671158, by rfl⟩ : syracuseStep 24912845 = 9342317) B9342317
theorem B16608563 : Blo 2185435 16608563 := bstep (se 1 (by rfl) ⟨12456422, by rfl⟩ : syracuseStep 16608563 = 24912845) B24912845
theorem B11072375 : Blo 2185435 11072375 := bstep (se 1 (by rfl) ⟨8304281, by rfl⟩ : syracuseStep 11072375 = 16608563) B16608563
theorem B7381583 : Blo 2185435 7381583 := bstep (se 1 (by rfl) ⟨5536187, by rfl⟩ : syracuseStep 7381583 = 11072375) B11072375
theorem B4921055 : Blo 2185435 4921055 := bstep (se 1 (by rfl) ⟨3690791, by rfl⟩ : syracuseStep 4921055 = 7381583) B7381583
theorem B3280703 : Blo 2185435 3280703 := bstep (se 1 (by rfl) ⟨2460527, by rfl⟩ : syracuseStep 3280703 = 4921055) B4921055
theorem B2187135 : Blo 2185435 2187135 := bstep (se 1 (by rfl) ⟨1640351, by rfl⟩ : syracuseStep 2187135 = 3280703) B3280703
theorem B3280709 : Blo 2185435 3280709 := bbase (se 4 (by rfl) ⟨307566, by rfl⟩ : syracuseStep 3280709 = 615133) (by norm_num)
theorem B2187139 : Blo 2185435 2187139 := bstep (se 1 (by rfl) ⟨1640354, by rfl⟩ : syracuseStep 2187139 = 3280709) B3280709
theorem B3690805 : Blo 2185435 3690805 := bbase (se 5 (by rfl) ⟨173006, by rfl⟩ : syracuseStep 3690805 = 346013) (by norm_num)
theorem B4921073 : Blo 2185435 4921073 := bstep (se 2 (by rfl) ⟨1845402, by rfl⟩ : syracuseStep 4921073 = 3690805) B3690805
theorem B3280715 : Blo 2185435 3280715 := bstep (se 1 (by rfl) ⟨2460536, by rfl⟩ : syracuseStep 3280715 = 4921073) B4921073
theorem B2187143 : Blo 2185435 2187143 := bstep (se 1 (by rfl) ⟨1640357, by rfl⟩ : syracuseStep 2187143 = 3280715) B3280715
theorem B2460541 : Blo 2185435 2460541 := bbase (se 3 (by rfl) ⟨461351, by rfl⟩ : syracuseStep 2460541 = 922703) (by norm_num)
theorem B3280721 : Blo 2185435 3280721 := bstep (se 2 (by rfl) ⟨1230270, by rfl⟩ : syracuseStep 3280721 = 2460541) B2460541
theorem B2187147 : Blo 2185435 2187147 := bstep (se 1 (by rfl) ⟨1640360, by rfl⟩ : syracuseStep 2187147 = 3280721) B3280721
theorem B7381637 : Blo 2185435 7381637 := bbase (se 4 (by rfl) ⟨692028, by rfl⟩ : syracuseStep 7381637 = 1384057) (by norm_num)
theorem B4921091 : Blo 2185435 4921091 := bstep (se 1 (by rfl) ⟨3690818, by rfl⟩ : syracuseStep 4921091 = 7381637) B7381637
theorem B3280727 : Blo 2185435 3280727 := bstep (se 1 (by rfl) ⟨2460545, by rfl⟩ : syracuseStep 3280727 = 4921091) B4921091
theorem B2187151 : Blo 2185435 2187151 := bstep (se 1 (by rfl) ⟨1640363, by rfl⟩ : syracuseStep 2187151 = 3280727) B3280727
theorem B3280733 : Blo 2185435 3280733 := bbase (se 3 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 3280733 = 1230275) (by norm_num)
theorem B2187155 : Blo 2185435 2187155 := bstep (se 1 (by rfl) ⟨1640366, by rfl⟩ : syracuseStep 2187155 = 3280733) B3280733
theorem B4921109 : Blo 2185435 4921109 := bbase (se 6 (by rfl) ⟨115338, by rfl⟩ : syracuseStep 4921109 = 230677) (by norm_num)
theorem B3280739 : Blo 2185435 3280739 := bstep (se 1 (by rfl) ⟨2460554, by rfl⟩ : syracuseStep 3280739 = 4921109) B4921109
theorem B2187159 : Blo 2185435 2187159 := bstep (se 1 (by rfl) ⟨1640369, by rfl⟩ : syracuseStep 2187159 = 3280739) B3280739
theorem B8304389 : Blo 2185435 8304389 := bbase (se 4 (by rfl) ⟨778536, by rfl⟩ : syracuseStep 8304389 = 1557073) (by norm_num)
theorem B5536259 : Blo 2185435 5536259 := bstep (se 1 (by rfl) ⟨4152194, by rfl⟩ : syracuseStep 5536259 = 8304389) B8304389
theorem B3690839 : Blo 2185435 3690839 := bstep (se 1 (by rfl) ⟨2768129, by rfl⟩ : syracuseStep 3690839 = 5536259) B5536259
theorem B2460559 : Blo 2185435 2460559 := bstep (se 1 (by rfl) ⟨1845419, by rfl⟩ : syracuseStep 2460559 = 3690839) B3690839
theorem B3280745 : Blo 2185435 3280745 := bstep (se 2 (by rfl) ⟨1230279, by rfl⟩ : syracuseStep 3280745 = 2460559) B2460559
theorem B2187163 : Blo 2185435 2187163 := bstep (se 1 (by rfl) ⟨1640372, by rfl⟩ : syracuseStep 2187163 = 3280745) B3280745
theorem B5611805 : Blo 2185435 5611805 := bbase (se 3 (by rfl) ⟨1052213, by rfl⟩ : syracuseStep 5611805 = 2104427) (by norm_num)
theorem B3741203 : Blo 2185435 3741203 := bstep (se 1 (by rfl) ⟨2805902, by rfl⟩ : syracuseStep 3741203 = 5611805) B5611805
theorem B2494135 : Blo 2185435 2494135 := bstep (se 1 (by rfl) ⟨1870601, by rfl⟩ : syracuseStep 2494135 = 3741203) B3741203
theorem B13302053 : Blo 2185435 13302053 := bstep (se 4 (by rfl) ⟨1247067, by rfl⟩ : syracuseStep 13302053 = 2494135) B2494135
theorem B8868035 : Blo 2185435 8868035 := bstep (se 1 (by rfl) ⟨6651026, by rfl⟩ : syracuseStep 8868035 = 13302053) B13302053
theorem B5912023 : Blo 2185435 5912023 := bstep (se 1 (by rfl) ⟨4434017, by rfl⟩ : syracuseStep 5912023 = 8868035) B8868035
theorem B7882697 : Blo 2185435 7882697 := bstep (se 2 (by rfl) ⟨2956011, by rfl⟩ : syracuseStep 7882697 = 5912023) B5912023
theorem B5255131 : Blo 2185435 5255131 := bstep (se 1 (by rfl) ⟨3941348, by rfl⟩ : syracuseStep 5255131 = 7882697) B7882697
theorem B7006841 : Blo 2185435 7006841 := bstep (se 2 (by rfl) ⟨2627565, by rfl⟩ : syracuseStep 7006841 = 5255131) B5255131
theorem B4671227 : Blo 2185435 4671227 := bstep (se 1 (by rfl) ⟨3503420, by rfl⟩ : syracuseStep 4671227 = 7006841) B7006841
theorem B12456605 : Blo 2185435 12456605 := bstep (se 3 (by rfl) ⟨2335613, by rfl⟩ : syracuseStep 12456605 = 4671227) B4671227
theorem B8304403 : Blo 2185435 8304403 := bstep (se 1 (by rfl) ⟨6228302, by rfl⟩ : syracuseStep 8304403 = 12456605) B12456605
theorem B11072537 : Blo 2185435 11072537 := bstep (se 2 (by rfl) ⟨4152201, by rfl⟩ : syracuseStep 11072537 = 8304403) B8304403
theorem B7381691 : Blo 2185435 7381691 := bstep (se 1 (by rfl) ⟨5536268, by rfl⟩ : syracuseStep 7381691 = 11072537) B11072537
theorem B4921127 : Blo 2185435 4921127 := bstep (se 1 (by rfl) ⟨3690845, by rfl⟩ : syracuseStep 4921127 = 7381691) B7381691
theorem B3280751 : Blo 2185435 3280751 := bstep (se 1 (by rfl) ⟨2460563, by rfl⟩ : syracuseStep 3280751 = 4921127) B4921127
theorem B2187167 : Blo 2185435 2187167 := bstep (se 1 (by rfl) ⟨1640375, by rfl⟩ : syracuseStep 2187167 = 3280751) B3280751
theorem B3280757 : Blo 2185435 3280757 := bbase (se 5 (by rfl) ⟨153785, by rfl⟩ : syracuseStep 3280757 = 307571) (by norm_num)
theorem B2187171 : Blo 2185435 2187171 := bstep (se 1 (by rfl) ⟨1640378, by rfl⟩ : syracuseStep 2187171 = 3280757) B3280757
theorem B4671245 : Blo 2185435 4671245 := bbase (se 3 (by rfl) ⟨875858, by rfl⟩ : syracuseStep 4671245 = 1751717) (by norm_num)
theorem B3114163 : Blo 2185435 3114163 := bstep (se 1 (by rfl) ⟨2335622, by rfl⟩ : syracuseStep 3114163 = 4671245) B4671245
theorem B4152217 : Blo 2185435 4152217 := bstep (se 2 (by rfl) ⟨1557081, by rfl⟩ : syracuseStep 4152217 = 3114163) B3114163
theorem B5536289 : Blo 2185435 5536289 := bstep (se 2 (by rfl) ⟨2076108, by rfl⟩ : syracuseStep 5536289 = 4152217) B4152217
theorem B3690859 : Blo 2185435 3690859 := bstep (se 1 (by rfl) ⟨2768144, by rfl⟩ : syracuseStep 3690859 = 5536289) B5536289
theorem B4921145 : Blo 2185435 4921145 := bstep (se 2 (by rfl) ⟨1845429, by rfl⟩ : syracuseStep 4921145 = 3690859) B3690859
theorem B3280763 : Blo 2185435 3280763 := bstep (se 1 (by rfl) ⟨2460572, by rfl⟩ : syracuseStep 3280763 = 4921145) B4921145
theorem B2187175 : Blo 2185435 2187175 := bstep (se 1 (by rfl) ⟨1640381, by rfl⟩ : syracuseStep 2187175 = 3280763) B3280763
theorem B2460577 : Blo 2185435 2460577 := bbase (se 2 (by rfl) ⟨922716, by rfl⟩ : syracuseStep 2460577 = 1845433) (by norm_num)
theorem B3280769 : Blo 2185435 3280769 := bstep (se 2 (by rfl) ⟨1230288, by rfl⟩ : syracuseStep 3280769 = 2460577) B2460577
theorem B2187179 : Blo 2185435 2187179 := bstep (se 1 (by rfl) ⟨1640384, by rfl⟩ : syracuseStep 2187179 = 3280769) B3280769
theorem B5536309 : Blo 2185435 5536309 := bbase (se 5 (by rfl) ⟨259514, by rfl⟩ : syracuseStep 5536309 = 519029) (by norm_num)
theorem B7381745 : Blo 2185435 7381745 := bstep (se 2 (by rfl) ⟨2768154, by rfl⟩ : syracuseStep 7381745 = 5536309) B5536309
theorem B4921163 : Blo 2185435 4921163 := bstep (se 1 (by rfl) ⟨3690872, by rfl⟩ : syracuseStep 4921163 = 7381745) B7381745
theorem B3280775 : Blo 2185435 3280775 := bstep (se 1 (by rfl) ⟨2460581, by rfl⟩ : syracuseStep 3280775 = 4921163) B4921163
theorem B2187183 : Blo 2185435 2187183 := bstep (se 1 (by rfl) ⟨1640387, by rfl⟩ : syracuseStep 2187183 = 3280775) B3280775
theorem B3280781 : Blo 2185435 3280781 := bbase (se 3 (by rfl) ⟨615146, by rfl⟩ : syracuseStep 3280781 = 1230293) (by norm_num)
theorem B2187187 : Blo 2185435 2187187 := bstep (se 1 (by rfl) ⟨1640390, by rfl⟩ : syracuseStep 2187187 = 3280781) B3280781
theorem B4921181 : Blo 2185435 4921181 := bbase (se 3 (by rfl) ⟨922721, by rfl⟩ : syracuseStep 4921181 = 1845443) (by norm_num)
theorem B3280787 : Blo 2185435 3280787 := bstep (se 1 (by rfl) ⟨2460590, by rfl⟩ : syracuseStep 3280787 = 4921181) B4921181
theorem B2187191 : Blo 2185435 2187191 := bstep (se 1 (by rfl) ⟨1640393, by rfl⟩ : syracuseStep 2187191 = 3280787) B3280787
theorem B3690893 : Blo 2185435 3690893 := bbase (se 3 (by rfl) ⟨692042, by rfl⟩ : syracuseStep 3690893 = 1384085) (by norm_num)
theorem B2460595 : Blo 2185435 2460595 := bstep (se 1 (by rfl) ⟨1845446, by rfl⟩ : syracuseStep 2460595 = 3690893) B3690893
theorem B3280793 : Blo 2185435 3280793 := bstep (se 2 (by rfl) ⟨1230297, by rfl⟩ : syracuseStep 3280793 = 2460595) B2460595
theorem B2187195 : Blo 2185435 2187195 := bstep (se 1 (by rfl) ⟨1640396, by rfl⟩ : syracuseStep 2187195 = 3280793) B3280793
theorem B38397077 : Blo 2185435 38397077 := bbase (se 6 (by rfl) ⟨899931, by rfl⟩ : syracuseStep 38397077 = 1799863) (by norm_num)
theorem B25598051 : Blo 2185435 25598051 := bstep (se 1 (by rfl) ⟨19198538, by rfl⟩ : syracuseStep 25598051 = 38397077) B38397077
theorem B17065367 : Blo 2185435 17065367 := bstep (se 1 (by rfl) ⟨12799025, by rfl⟩ : syracuseStep 17065367 = 25598051) B25598051
theorem B11376911 : Blo 2185435 11376911 := bstep (se 1 (by rfl) ⟨8532683, by rfl⟩ : syracuseStep 11376911 = 17065367) B17065367
theorem B7584607 : Blo 2185435 7584607 := bstep (se 1 (by rfl) ⟨5688455, by rfl⟩ : syracuseStep 7584607 = 11376911) B11376911
theorem B10112809 : Blo 2185435 10112809 := bstep (se 2 (by rfl) ⟨3792303, by rfl⟩ : syracuseStep 10112809 = 7584607) B7584607
theorem B13483745 : Blo 2185435 13483745 := bstep (se 2 (by rfl) ⟨5056404, by rfl⟩ : syracuseStep 13483745 = 10112809) B10112809
theorem B8989163 : Blo 2185435 8989163 := bstep (se 1 (by rfl) ⟨6741872, by rfl⟩ : syracuseStep 8989163 = 13483745) B13483745
theorem B5992775 : Blo 2185435 5992775 := bstep (se 1 (by rfl) ⟨4494581, by rfl⟩ : syracuseStep 5992775 = 8989163) B8989163
theorem B3995183 : Blo 2185435 3995183 := bstep (se 1 (by rfl) ⟨2996387, by rfl⟩ : syracuseStep 3995183 = 5992775) B5992775
theorem B2663455 : Blo 2185435 2663455 := bstep (se 1 (by rfl) ⟨1997591, by rfl⟩ : syracuseStep 2663455 = 3995183) B3995183
theorem B3551273 : Blo 2185435 3551273 := bstep (se 2 (by rfl) ⟨1331727, by rfl⟩ : syracuseStep 3551273 = 2663455) B2663455
theorem B2367515 : Blo 2185435 2367515 := bstep (se 1 (by rfl) ⟨1775636, by rfl⟩ : syracuseStep 2367515 = 3551273) B3551273
theorem B6313373 : Blo 2185435 6313373 := bstep (se 3 (by rfl) ⟨1183757, by rfl⟩ : syracuseStep 6313373 = 2367515) B2367515
theorem B4208915 : Blo 2185435 4208915 := bstep (se 1 (by rfl) ⟨3156686, by rfl⟩ : syracuseStep 4208915 = 6313373) B6313373
theorem B2805943 : Blo 2185435 2805943 := bstep (se 1 (by rfl) ⟨2104457, by rfl⟩ : syracuseStep 2805943 = 4208915) B4208915
theorem B3741257 : Blo 2185435 3741257 := bstep (se 2 (by rfl) ⟨1402971, by rfl⟩ : syracuseStep 3741257 = 2805943) B2805943
theorem B2494171 : Blo 2185435 2494171 := bstep (se 1 (by rfl) ⟨1870628, by rfl⟩ : syracuseStep 2494171 = 3741257) B3741257
theorem B13302245 : Blo 2185435 13302245 := bstep (se 4 (by rfl) ⟨1247085, by rfl⟩ : syracuseStep 13302245 = 2494171) B2494171
theorem B35472653 : Blo 2185435 35472653 := bstep (se 3 (by rfl) ⟨6651122, by rfl⟩ : syracuseStep 35472653 = 13302245) B13302245
theorem B23648435 : Blo 2185435 23648435 := bstep (se 1 (by rfl) ⟨17736326, by rfl⟩ : syracuseStep 23648435 = 35472653) B35472653
theorem B15765623 : Blo 2185435 15765623 := bstep (se 1 (by rfl) ⟨11824217, by rfl⟩ : syracuseStep 15765623 = 23648435) B23648435
theorem B10510415 : Blo 2185435 10510415 := bstep (se 1 (by rfl) ⟨7882811, by rfl⟩ : syracuseStep 10510415 = 15765623) B15765623
theorem B7006943 : Blo 2185435 7006943 := bstep (se 1 (by rfl) ⟨5255207, by rfl⟩ : syracuseStep 7006943 = 10510415) B10510415
theorem B18685181 : Blo 2185435 18685181 := bstep (se 3 (by rfl) ⟨3503471, by rfl⟩ : syracuseStep 18685181 = 7006943) B7006943
theorem B12456787 : Blo 2185435 12456787 := bstep (se 1 (by rfl) ⟨9342590, by rfl⟩ : syracuseStep 12456787 = 18685181) B18685181
theorem B16609049 : Blo 2185435 16609049 := bstep (se 2 (by rfl) ⟨6228393, by rfl⟩ : syracuseStep 16609049 = 12456787) B12456787
theorem B11072699 : Blo 2185435 11072699 := bstep (se 1 (by rfl) ⟨8304524, by rfl⟩ : syracuseStep 11072699 = 16609049) B16609049
theorem B7381799 : Blo 2185435 7381799 := bstep (se 1 (by rfl) ⟨5536349, by rfl⟩ : syracuseStep 7381799 = 11072699) B11072699
theorem B4921199 : Blo 2185435 4921199 := bstep (se 1 (by rfl) ⟨3690899, by rfl⟩ : syracuseStep 4921199 = 7381799) B7381799
theorem B3280799 : Blo 2185435 3280799 := bstep (se 1 (by rfl) ⟨2460599, by rfl⟩ : syracuseStep 3280799 = 4921199) B4921199
theorem B2187199 : Blo 2185435 2187199 := bstep (se 1 (by rfl) ⟨1640399, by rfl⟩ : syracuseStep 2187199 = 3280799) B3280799
theorem B3280805 : Blo 2185435 3280805 := bbase (se 4 (by rfl) ⟨307575, by rfl⟩ : syracuseStep 3280805 = 615151) (by norm_num)
theorem B2187203 : Blo 2185435 2187203 := bstep (se 1 (by rfl) ⟨1640402, by rfl⟩ : syracuseStep 2187203 = 3280805) B3280805
theorem B2768185 : Blo 2185435 2768185 := bbase (se 2 (by rfl) ⟨1038069, by rfl⟩ : syracuseStep 2768185 = 2076139) (by norm_num)
theorem B3690913 : Blo 2185435 3690913 := bstep (se 2 (by rfl) ⟨1384092, by rfl⟩ : syracuseStep 3690913 = 2768185) B2768185
theorem B4921217 : Blo 2185435 4921217 := bstep (se 2 (by rfl) ⟨1845456, by rfl⟩ : syracuseStep 4921217 = 3690913) B3690913
theorem B3280811 : Blo 2185435 3280811 := bstep (se 1 (by rfl) ⟨2460608, by rfl⟩ : syracuseStep 3280811 = 4921217) B4921217
theorem B2187207 : Blo 2185435 2187207 := bstep (se 1 (by rfl) ⟨1640405, by rfl⟩ : syracuseStep 2187207 = 3280811) B3280811
theorem B2460613 : Blo 2185435 2460613 := bbase (se 4 (by rfl) ⟨230682, by rfl⟩ : syracuseStep 2460613 = 461365) (by norm_num)
theorem B3280817 : Blo 2185435 3280817 := bstep (se 2 (by rfl) ⟨1230306, by rfl⟩ : syracuseStep 3280817 = 2460613) B2460613
theorem B2187211 : Blo 2185435 2187211 := bstep (se 1 (by rfl) ⟨1640408, by rfl⟩ : syracuseStep 2187211 = 3280817) B3280817
theorem B4152293 : Blo 2185435 4152293 := bbase (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) (by norm_num)
theorem B2768195 : Blo 2185435 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B7381853 : Blo 2185435 7381853 := bstep (se 3 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 7381853 = 2768195) B2768195
theorem B4921235 : Blo 2185435 4921235 := bstep (se 1 (by rfl) ⟨3690926, by rfl⟩ : syracuseStep 4921235 = 7381853) B7381853
theorem B3280823 : Blo 2185435 3280823 := bstep (se 1 (by rfl) ⟨2460617, by rfl⟩ : syracuseStep 3280823 = 4921235) B4921235
theorem B2187215 : Blo 2185435 2187215 := bstep (se 1 (by rfl) ⟨1640411, by rfl⟩ : syracuseStep 2187215 = 3280823) B3280823
theorem B3280829 : Blo 2185435 3280829 := bbase (se 3 (by rfl) ⟨615155, by rfl⟩ : syracuseStep 3280829 = 1230311) (by norm_num)
theorem B2187219 : Blo 2185435 2187219 := bstep (se 1 (by rfl) ⟨1640414, by rfl⟩ : syracuseStep 2187219 = 3280829) B3280829
theorem B4921253 : Blo 2185435 4921253 := bbase (se 4 (by rfl) ⟨461367, by rfl⟩ : syracuseStep 4921253 = 922735) (by norm_num)
theorem B3280835 : Blo 2185435 3280835 := bstep (se 1 (by rfl) ⟨2460626, by rfl⟩ : syracuseStep 3280835 = 4921253) B4921253
theorem B2187223 : Blo 2185435 2187223 := bstep (se 1 (by rfl) ⟨1640417, by rfl⟩ : syracuseStep 2187223 = 3280835) B3280835
theorem B5536421 : Blo 2185435 5536421 := bbase (se 4 (by rfl) ⟨519039, by rfl⟩ : syracuseStep 5536421 = 1038079) (by norm_num)
theorem B3690947 : Blo 2185435 3690947 := bstep (se 1 (by rfl) ⟨2768210, by rfl⟩ : syracuseStep 3690947 = 5536421) B5536421
theorem B2460631 : Blo 2185435 2460631 := bstep (se 1 (by rfl) ⟨1845473, by rfl⟩ : syracuseStep 2460631 = 3690947) B3690947
theorem B3280841 : Blo 2185435 3280841 := bstep (se 2 (by rfl) ⟨1230315, by rfl⟩ : syracuseStep 3280841 = 2460631) B2460631
theorem B2187227 : Blo 2185435 2187227 := bstep (se 1 (by rfl) ⟨1640420, by rfl⟩ : syracuseStep 2187227 = 3280841) B3280841
theorem B6228485 : Blo 2185435 6228485 := bbase (se 4 (by rfl) ⟨583920, by rfl⟩ : syracuseStep 6228485 = 1167841) (by norm_num)
theorem B4152323 : Blo 2185435 4152323 := bstep (se 1 (by rfl) ⟨3114242, by rfl⟩ : syracuseStep 4152323 = 6228485) B6228485
theorem B11072861 : Blo 2185435 11072861 := bstep (se 3 (by rfl) ⟨2076161, by rfl⟩ : syracuseStep 11072861 = 4152323) B4152323
theorem B7381907 : Blo 2185435 7381907 := bstep (se 1 (by rfl) ⟨5536430, by rfl⟩ : syracuseStep 7381907 = 11072861) B11072861
theorem B4921271 : Blo 2185435 4921271 := bstep (se 1 (by rfl) ⟨3690953, by rfl⟩ : syracuseStep 4921271 = 7381907) B7381907
theorem B3280847 : Blo 2185435 3280847 := bstep (se 1 (by rfl) ⟨2460635, by rfl⟩ : syracuseStep 3280847 = 4921271) B4921271
theorem B2187231 : Blo 2185435 2187231 := bstep (se 1 (by rfl) ⟨1640423, by rfl⟩ : syracuseStep 2187231 = 3280847) B3280847
theorem B3280853 : Blo 2185435 3280853 := bbase (se 7 (by rfl) ⟨38447, by rfl⟩ : syracuseStep 3280853 = 76895) (by norm_num)
theorem B2187235 : Blo 2185435 2187235 := bstep (se 1 (by rfl) ⟨1640426, by rfl⟩ : syracuseStep 2187235 = 3280853) B3280853
theorem B8304677 : Blo 2185435 8304677 := bbase (se 4 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 8304677 = 1557127) (by norm_num)
theorem B5536451 : Blo 2185435 5536451 := bstep (se 1 (by rfl) ⟨4152338, by rfl⟩ : syracuseStep 5536451 = 8304677) B8304677
theorem B3690967 : Blo 2185435 3690967 := bstep (se 1 (by rfl) ⟨2768225, by rfl⟩ : syracuseStep 3690967 = 5536451) B5536451
theorem B4921289 : Blo 2185435 4921289 := bstep (se 2 (by rfl) ⟨1845483, by rfl⟩ : syracuseStep 4921289 = 3690967) B3690967
theorem B3280859 : Blo 2185435 3280859 := bstep (se 1 (by rfl) ⟨2460644, by rfl⟩ : syracuseStep 3280859 = 4921289) B4921289
theorem B2187239 : Blo 2185435 2187239 := bstep (se 1 (by rfl) ⟨1640429, by rfl⟩ : syracuseStep 2187239 = 3280859) B3280859
theorem B2460649 : Blo 2185435 2460649 := bbase (se 2 (by rfl) ⟨922743, by rfl⟩ : syracuseStep 2460649 = 1845487) (by norm_num)
theorem B3280865 : Blo 2185435 3280865 := bstep (se 2 (by rfl) ⟨1230324, by rfl⟩ : syracuseStep 3280865 = 2460649) B2460649
theorem B2187243 : Blo 2185435 2187243 := bstep (se 1 (by rfl) ⟨1640432, by rfl⟩ : syracuseStep 2187243 = 3280865) B3280865
theorem B3503549 : Blo 2185435 3503549 := bbase (se 3 (by rfl) ⟨656915, by rfl⟩ : syracuseStep 3503549 = 1313831) (by norm_num)
theorem B2335699 : Blo 2185435 2335699 := bstep (se 1 (by rfl) ⟨1751774, by rfl⟩ : syracuseStep 2335699 = 3503549) B3503549
theorem B12457061 : Blo 2185435 12457061 := bstep (se 4 (by rfl) ⟨1167849, by rfl⟩ : syracuseStep 12457061 = 2335699) B2335699
theorem B8304707 : Blo 2185435 8304707 := bstep (se 1 (by rfl) ⟨6228530, by rfl⟩ : syracuseStep 8304707 = 12457061) B12457061
theorem B5536471 : Blo 2185435 5536471 := bstep (se 1 (by rfl) ⟨4152353, by rfl⟩ : syracuseStep 5536471 = 8304707) B8304707
theorem B7381961 : Blo 2185435 7381961 := bstep (se 2 (by rfl) ⟨2768235, by rfl⟩ : syracuseStep 7381961 = 5536471) B5536471
theorem B4921307 : Blo 2185435 4921307 := bstep (se 1 (by rfl) ⟨3690980, by rfl⟩ : syracuseStep 4921307 = 7381961) B7381961
theorem B3280871 : Blo 2185435 3280871 := bstep (se 1 (by rfl) ⟨2460653, by rfl⟩ : syracuseStep 3280871 = 4921307) B4921307
theorem B2187247 : Blo 2185435 2187247 := bstep (se 1 (by rfl) ⟨1640435, by rfl⟩ : syracuseStep 2187247 = 3280871) B3280871
theorem B3280877 : Blo 2185435 3280877 := bbase (se 3 (by rfl) ⟨615164, by rfl⟩ : syracuseStep 3280877 = 1230329) (by norm_num)
theorem B2187251 : Blo 2185435 2187251 := bstep (se 1 (by rfl) ⟨1640438, by rfl⟩ : syracuseStep 2187251 = 3280877) B3280877
theorem B4921325 : Blo 2185435 4921325 := bbase (se 3 (by rfl) ⟨922748, by rfl⟩ : syracuseStep 4921325 = 1845497) (by norm_num)
theorem B3280883 : Blo 2185435 3280883 := bstep (se 1 (by rfl) ⟨2460662, by rfl⟩ : syracuseStep 3280883 = 4921325) B4921325
theorem B2187255 : Blo 2185435 2187255 := bstep (se 1 (by rfl) ⟨1640441, by rfl⟩ : syracuseStep 2187255 = 3280883) B3280883
theorem B2627677 : Blo 2185435 2627677 := bbase (se 3 (by rfl) ⟨492689, by rfl⟩ : syracuseStep 2627677 = 985379) (by norm_num)
theorem B3503569 : Blo 2185435 3503569 := bstep (se 2 (by rfl) ⟨1313838, by rfl⟩ : syracuseStep 3503569 = 2627677) B2627677
theorem B4671425 : Blo 2185435 4671425 := bstep (se 2 (by rfl) ⟨1751784, by rfl⟩ : syracuseStep 4671425 = 3503569) B3503569
theorem B3114283 : Blo 2185435 3114283 := bstep (se 1 (by rfl) ⟨2335712, by rfl⟩ : syracuseStep 3114283 = 4671425) B4671425
theorem B4152377 : Blo 2185435 4152377 := bstep (se 2 (by rfl) ⟨1557141, by rfl⟩ : syracuseStep 4152377 = 3114283) B3114283
theorem B2768251 : Blo 2185435 2768251 := bstep (se 1 (by rfl) ⟨2076188, by rfl⟩ : syracuseStep 2768251 = 4152377) B4152377
theorem B3691001 : Blo 2185435 3691001 := bstep (se 2 (by rfl) ⟨1384125, by rfl⟩ : syracuseStep 3691001 = 2768251) B2768251
theorem B2460667 : Blo 2185435 2460667 := bstep (se 1 (by rfl) ⟨1845500, by rfl⟩ : syracuseStep 2460667 = 3691001) B3691001
theorem B3280889 : Blo 2185435 3280889 := bstep (se 2 (by rfl) ⟨1230333, by rfl⟩ : syracuseStep 3280889 = 2460667) B2460667
theorem B2187259 : Blo 2185435 2187259 := bstep (se 1 (by rfl) ⟨1640444, by rfl⟩ : syracuseStep 2187259 = 3280889) B3280889
theorem B3792413 : Blo 2185435 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B2528275 : Blo 2185435 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B3371033 : Blo 2185435 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B2247355 : Blo 2185435 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B11985893 : Blo 2185435 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B7990595 : Blo 2185435 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B5327063 : Blo 2185435 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B3551375 : Blo 2185435 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B9470333 : Blo 2185435 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B6313555 : Blo 2185435 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B8418073 : Blo 2185435 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B11224097 : Blo 2185435 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B7482731 : Blo 2185435 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B19953949 : Blo 2185435 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B26605265 : Blo 2185435 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B283789493 : Blo 2185435 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B189192995 : Blo 2185435 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B126128663 : Blo 2185435 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B84085775 : Blo 2185435 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B56057183 : Blo 2185435 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B37371455 : Blo 2185435 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B24914303 : Blo 2185435 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B16609535 : Blo 2185435 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B11073023 : Blo 2185435 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B7382015 : Blo 2185435 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B4921343 : Blo 2185435 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B3280895 : Blo 2185435 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B2187263 : Blo 2185435 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B3280901 : Blo 2185435 3280901 := bbase (se 4 (by rfl) ⟨307584, by rfl⟩ : syracuseStep 3280901 = 615169) (by norm_num)
theorem B2187267 : Blo 2185435 2187267 := bstep (se 1 (by rfl) ⟨1640450, by rfl⟩ : syracuseStep 2187267 = 3280901) B3280901
theorem B3691021 : Blo 2185435 3691021 := bbase (se 3 (by rfl) ⟨692066, by rfl⟩ : syracuseStep 3691021 = 1384133) (by norm_num)
theorem B4921361 : Blo 2185435 4921361 := bstep (se 2 (by rfl) ⟨1845510, by rfl⟩ : syracuseStep 4921361 = 3691021) B3691021
theorem B3280907 : Blo 2185435 3280907 := bstep (se 1 (by rfl) ⟨2460680, by rfl⟩ : syracuseStep 3280907 = 4921361) B4921361
theorem B2187271 : Blo 2185435 2187271 := bstep (se 1 (by rfl) ⟨1640453, by rfl⟩ : syracuseStep 2187271 = 3280907) B3280907
theorem B2460685 : Blo 2185435 2460685 := bbase (se 3 (by rfl) ⟨461378, by rfl⟩ : syracuseStep 2460685 = 922757) (by norm_num)
theorem B3280913 : Blo 2185435 3280913 := bstep (se 2 (by rfl) ⟨1230342, by rfl⟩ : syracuseStep 3280913 = 2460685) B2460685
theorem B2187275 : Blo 2185435 2187275 := bstep (se 1 (by rfl) ⟨1640456, by rfl⟩ : syracuseStep 2187275 = 3280913) B3280913
theorem B7382069 : Blo 2185435 7382069 := bbase (se 5 (by rfl) ⟨346034, by rfl⟩ : syracuseStep 7382069 = 692069) (by norm_num)
theorem B4921379 : Blo 2185435 4921379 := bstep (se 1 (by rfl) ⟨3691034, by rfl⟩ : syracuseStep 4921379 = 7382069) B7382069
theorem B3280919 : Blo 2185435 3280919 := bstep (se 1 (by rfl) ⟨2460689, by rfl⟩ : syracuseStep 3280919 = 4921379) B4921379
theorem B2187279 : Blo 2185435 2187279 := bstep (se 1 (by rfl) ⟨1640459, by rfl⟩ : syracuseStep 2187279 = 3280919) B3280919
theorem B3280925 : Blo 2185435 3280925 := bbase (se 3 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 3280925 = 1230347) (by norm_num)
theorem B2187283 : Blo 2185435 2187283 := bstep (se 1 (by rfl) ⟨1640462, by rfl⟩ : syracuseStep 2187283 = 3280925) B3280925
theorem B4921397 : Blo 2185435 4921397 := bbase (se 5 (by rfl) ⟨230690, by rfl⟩ : syracuseStep 4921397 = 461381) (by norm_num)
theorem B3280931 : Blo 2185435 3280931 := bstep (se 1 (by rfl) ⟨2460698, by rfl⟩ : syracuseStep 3280931 = 4921397) B4921397
theorem B2187287 : Blo 2185435 2187287 := bstep (se 1 (by rfl) ⟨1640465, by rfl⟩ : syracuseStep 2187287 = 3280931) B3280931
theorem B4434269 : Blo 2185435 4434269 := bbase (se 3 (by rfl) ⟨831425, by rfl⟩ : syracuseStep 4434269 = 1662851) (by norm_num)
theorem B11824717 : Blo 2185435 11824717 := bstep (se 3 (by rfl) ⟨2217134, by rfl⟩ : syracuseStep 11824717 = 4434269) B4434269
theorem B15766289 : Blo 2185435 15766289 := bstep (se 2 (by rfl) ⟨5912358, by rfl⟩ : syracuseStep 15766289 = 11824717) B11824717
theorem B10510859 : Blo 2185435 10510859 := bstep (se 1 (by rfl) ⟨7883144, by rfl⟩ : syracuseStep 10510859 = 15766289) B15766289
theorem B7007239 : Blo 2185435 7007239 := bstep (se 1 (by rfl) ⟨5255429, by rfl⟩ : syracuseStep 7007239 = 10510859) B10510859
theorem B9342985 : Blo 2185435 9342985 := bstep (se 2 (by rfl) ⟨3503619, by rfl⟩ : syracuseStep 9342985 = 7007239) B7007239
theorem B12457313 : Blo 2185435 12457313 := bstep (se 2 (by rfl) ⟨4671492, by rfl⟩ : syracuseStep 12457313 = 9342985) B9342985
theorem B8304875 : Blo 2185435 8304875 := bstep (se 1 (by rfl) ⟨6228656, by rfl⟩ : syracuseStep 8304875 = 12457313) B12457313
theorem B5536583 : Blo 2185435 5536583 := bstep (se 1 (by rfl) ⟨4152437, by rfl⟩ : syracuseStep 5536583 = 8304875) B8304875
theorem B3691055 : Blo 2185435 3691055 := bstep (se 1 (by rfl) ⟨2768291, by rfl⟩ : syracuseStep 3691055 = 5536583) B5536583
theorem B2460703 : Blo 2185435 2460703 := bstep (se 1 (by rfl) ⟨1845527, by rfl⟩ : syracuseStep 2460703 = 3691055) B3691055
theorem B3280937 : Blo 2185435 3280937 := bstep (se 2 (by rfl) ⟨1230351, by rfl⟩ : syracuseStep 3280937 = 2460703) B2460703
theorem B2187291 : Blo 2185435 2187291 := bstep (se 1 (by rfl) ⟨1640468, by rfl⟩ : syracuseStep 2187291 = 3280937) B3280937
theorem B4434277 : Blo 2185435 4434277 := bbase (se 4 (by rfl) ⟨415713, by rfl⟩ : syracuseStep 4434277 = 831427) (by norm_num)
theorem B5912369 : Blo 2185435 5912369 := bstep (se 2 (by rfl) ⟨2217138, by rfl⟩ : syracuseStep 5912369 = 4434277) B4434277
theorem B3941579 : Blo 2185435 3941579 := bstep (se 1 (by rfl) ⟨2956184, by rfl⟩ : syracuseStep 3941579 = 5912369) B5912369
theorem B10510877 : Blo 2185435 10510877 := bstep (se 3 (by rfl) ⟨1970789, by rfl⟩ : syracuseStep 10510877 = 3941579) B3941579
theorem B7007251 : Blo 2185435 7007251 := bstep (se 1 (by rfl) ⟨5255438, by rfl⟩ : syracuseStep 7007251 = 10510877) B10510877
theorem B9343001 : Blo 2185435 9343001 := bstep (se 2 (by rfl) ⟨3503625, by rfl⟩ : syracuseStep 9343001 = 7007251) B7007251
theorem B6228667 : Blo 2185435 6228667 := bstep (se 1 (by rfl) ⟨4671500, by rfl⟩ : syracuseStep 6228667 = 9343001) B9343001
theorem B8304889 : Blo 2185435 8304889 := bstep (se 2 (by rfl) ⟨3114333, by rfl⟩ : syracuseStep 8304889 = 6228667) B6228667
theorem B11073185 : Blo 2185435 11073185 := bstep (se 2 (by rfl) ⟨4152444, by rfl⟩ : syracuseStep 11073185 = 8304889) B8304889
theorem B7382123 : Blo 2185435 7382123 := bstep (se 1 (by rfl) ⟨5536592, by rfl⟩ : syracuseStep 7382123 = 11073185) B11073185
theorem B4921415 : Blo 2185435 4921415 := bstep (se 1 (by rfl) ⟨3691061, by rfl⟩ : syracuseStep 4921415 = 7382123) B7382123
theorem B3280943 : Blo 2185435 3280943 := bstep (se 1 (by rfl) ⟨2460707, by rfl⟩ : syracuseStep 3280943 = 4921415) B4921415
theorem B2187295 : Blo 2185435 2187295 := bstep (se 1 (by rfl) ⟨1640471, by rfl⟩ : syracuseStep 2187295 = 3280943) B3280943
theorem B3280949 : Blo 2185435 3280949 := bbase (se 5 (by rfl) ⟨153794, by rfl⟩ : syracuseStep 3280949 = 307589) (by norm_num)
theorem B2187299 : Blo 2185435 2187299 := bstep (se 1 (by rfl) ⟨1640474, by rfl⟩ : syracuseStep 2187299 = 3280949) B3280949
theorem B5536613 : Blo 2185435 5536613 := bbase (se 4 (by rfl) ⟨519057, by rfl⟩ : syracuseStep 5536613 = 1038115) (by norm_num)
theorem B3691075 : Blo 2185435 3691075 := bstep (se 1 (by rfl) ⟨2768306, by rfl⟩ : syracuseStep 3691075 = 5536613) B5536613
theorem B4921433 : Blo 2185435 4921433 := bstep (se 2 (by rfl) ⟨1845537, by rfl⟩ : syracuseStep 4921433 = 3691075) B3691075
theorem B3280955 : Blo 2185435 3280955 := bstep (se 1 (by rfl) ⟨2460716, by rfl⟩ : syracuseStep 3280955 = 4921433) B4921433
theorem B2187303 : Blo 2185435 2187303 := bstep (se 1 (by rfl) ⟨1640477, by rfl⟩ : syracuseStep 2187303 = 3280955) B3280955
theorem B2460721 : Blo 2185435 2460721 := bbase (se 2 (by rfl) ⟨922770, by rfl⟩ : syracuseStep 2460721 = 1845541) (by norm_num)
theorem B3280961 : Blo 2185435 3280961 := bstep (se 2 (by rfl) ⟨1230360, by rfl⟩ : syracuseStep 3280961 = 2460721) B2460721
theorem B2187307 : Blo 2185435 2187307 := bstep (se 1 (by rfl) ⟨1640480, by rfl⟩ : syracuseStep 2187307 = 3280961) B3280961
theorem B11377493 : Blo 2185435 11377493 := bbase (se 9 (by rfl) ⟨33332, by rfl⟩ : syracuseStep 11377493 = 66665) (by norm_num)
theorem B7584995 : Blo 2185435 7584995 := bstep (se 1 (by rfl) ⟨5688746, by rfl⟩ : syracuseStep 7584995 = 11377493) B11377493
theorem B5056663 : Blo 2185435 5056663 := bstep (se 1 (by rfl) ⟨3792497, by rfl⟩ : syracuseStep 5056663 = 7584995) B7584995
theorem B6742217 : Blo 2185435 6742217 := bstep (se 2 (by rfl) ⟨2528331, by rfl⟩ : syracuseStep 6742217 = 5056663) B5056663
theorem B17979245 : Blo 2185435 17979245 := bstep (se 3 (by rfl) ⟨3371108, by rfl⟩ : syracuseStep 17979245 = 6742217) B6742217
theorem B11986163 : Blo 2185435 11986163 := bstep (se 1 (by rfl) ⟨8989622, by rfl⟩ : syracuseStep 11986163 = 17979245) B17979245
theorem B7990775 : Blo 2185435 7990775 := bstep (se 1 (by rfl) ⟨5993081, by rfl⟩ : syracuseStep 7990775 = 11986163) B11986163
theorem B5327183 : Blo 2185435 5327183 := bstep (se 1 (by rfl) ⟨3995387, by rfl⟩ : syracuseStep 5327183 = 7990775) B7990775
theorem B3551455 : Blo 2185435 3551455 := bstep (se 1 (by rfl) ⟨2663591, by rfl⟩ : syracuseStep 3551455 = 5327183) B5327183
theorem B4735273 : Blo 2185435 4735273 := bstep (se 2 (by rfl) ⟨1775727, by rfl⟩ : syracuseStep 4735273 = 3551455) B3551455
theorem B6313697 : Blo 2185435 6313697 := bstep (se 2 (by rfl) ⟨2367636, by rfl⟩ : syracuseStep 6313697 = 4735273) B4735273
theorem B4209131 : Blo 2185435 4209131 := bstep (se 1 (by rfl) ⟨3156848, by rfl⟩ : syracuseStep 4209131 = 6313697) B6313697
theorem B2806087 : Blo 2185435 2806087 := bstep (se 1 (by rfl) ⟨2104565, by rfl⟩ : syracuseStep 2806087 = 4209131) B4209131
theorem B3741449 : Blo 2185435 3741449 := bstep (se 2 (by rfl) ⟨1403043, by rfl⟩ : syracuseStep 3741449 = 2806087) B2806087
theorem B9977197 : Blo 2185435 9977197 := bstep (se 3 (by rfl) ⟨1870724, by rfl⟩ : syracuseStep 9977197 = 3741449) B3741449
theorem B13302929 : Blo 2185435 13302929 := bstep (se 2 (by rfl) ⟨4988598, by rfl⟩ : syracuseStep 13302929 = 9977197) B9977197
theorem B8868619 : Blo 2185435 8868619 := bstep (se 1 (by rfl) ⟨6651464, by rfl⟩ : syracuseStep 8868619 = 13302929) B13302929
theorem B11824825 : Blo 2185435 11824825 := bstep (se 2 (by rfl) ⟨4434309, by rfl⟩ : syracuseStep 11824825 = 8868619) B8868619
theorem B15766433 : Blo 2185435 15766433 := bstep (se 2 (by rfl) ⟨5912412, by rfl⟩ : syracuseStep 15766433 = 11824825) B11824825
theorem B10510955 : Blo 2185435 10510955 := bstep (se 1 (by rfl) ⟨7883216, by rfl⟩ : syracuseStep 10510955 = 15766433) B15766433
theorem B7007303 : Blo 2185435 7007303 := bstep (se 1 (by rfl) ⟨5255477, by rfl⟩ : syracuseStep 7007303 = 10510955) B10510955
theorem B4671535 : Blo 2185435 4671535 := bstep (se 1 (by rfl) ⟨3503651, by rfl⟩ : syracuseStep 4671535 = 7007303) B7007303
theorem B6228713 : Blo 2185435 6228713 := bstep (se 2 (by rfl) ⟨2335767, by rfl⟩ : syracuseStep 6228713 = 4671535) B4671535
theorem B4152475 : Blo 2185435 4152475 := bstep (se 1 (by rfl) ⟨3114356, by rfl⟩ : syracuseStep 4152475 = 6228713) B6228713
theorem B5536633 : Blo 2185435 5536633 := bstep (se 2 (by rfl) ⟨2076237, by rfl⟩ : syracuseStep 5536633 = 4152475) B4152475
theorem B7382177 : Blo 2185435 7382177 := bstep (se 2 (by rfl) ⟨2768316, by rfl⟩ : syracuseStep 7382177 = 5536633) B5536633
theorem B4921451 : Blo 2185435 4921451 := bstep (se 1 (by rfl) ⟨3691088, by rfl⟩ : syracuseStep 4921451 = 7382177) B7382177
theorem B3280967 : Blo 2185435 3280967 := bstep (se 1 (by rfl) ⟨2460725, by rfl⟩ : syracuseStep 3280967 = 4921451) B4921451
theorem B2187311 : Blo 2185435 2187311 := bstep (se 1 (by rfl) ⟨1640483, by rfl⟩ : syracuseStep 2187311 = 3280967) B3280967
theorem B3280973 : Blo 2185435 3280973 := bbase (se 3 (by rfl) ⟨615182, by rfl⟩ : syracuseStep 3280973 = 1230365) (by norm_num)
theorem B2187315 : Blo 2185435 2187315 := bstep (se 1 (by rfl) ⟨1640486, by rfl⟩ : syracuseStep 2187315 = 3280973) B3280973
theorem B4921469 : Blo 2185435 4921469 := bbase (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) (by norm_num)
theorem B3280979 : Blo 2185435 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B2187319 : Blo 2185435 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B3691109 : Blo 2185435 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B2460739 : Blo 2185435 2460739 := bstep (se 1 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 2460739 = 3691109) B3691109
theorem B3280985 : Blo 2185435 3280985 := bstep (se 2 (by rfl) ⟨1230369, by rfl⟩ : syracuseStep 3280985 = 2460739) B2460739
theorem B2187323 : Blo 2185435 2187323 := bstep (se 1 (by rfl) ⟨1640492, by rfl⟩ : syracuseStep 2187323 = 3280985) B3280985
theorem B3503677 : Blo 2185435 3503677 := bbase (se 3 (by rfl) ⟨656939, by rfl⟩ : syracuseStep 3503677 = 1313879) (by norm_num)
theorem B4671569 : Blo 2185435 4671569 := bstep (se 2 (by rfl) ⟨1751838, by rfl⟩ : syracuseStep 4671569 = 3503677) B3503677
theorem B3114379 : Blo 2185435 3114379 := bstep (se 1 (by rfl) ⟨2335784, by rfl⟩ : syracuseStep 3114379 = 4671569) B4671569
theorem B16610021 : Blo 2185435 16610021 := bstep (se 4 (by rfl) ⟨1557189, by rfl⟩ : syracuseStep 16610021 = 3114379) B3114379
theorem B11073347 : Blo 2185435 11073347 := bstep (se 1 (by rfl) ⟨8305010, by rfl⟩ : syracuseStep 11073347 = 16610021) B16610021
theorem B7382231 : Blo 2185435 7382231 := bstep (se 1 (by rfl) ⟨5536673, by rfl⟩ : syracuseStep 7382231 = 11073347) B11073347
theorem B4921487 : Blo 2185435 4921487 := bstep (se 1 (by rfl) ⟨3691115, by rfl⟩ : syracuseStep 4921487 = 7382231) B7382231
theorem B3280991 : Blo 2185435 3280991 := bstep (se 1 (by rfl) ⟨2460743, by rfl⟩ : syracuseStep 3280991 = 4921487) B4921487
theorem B2187327 : Blo 2185435 2187327 := bstep (se 1 (by rfl) ⟨1640495, by rfl⟩ : syracuseStep 2187327 = 3280991) B3280991
theorem B3280997 : Blo 2185435 3280997 := bbase (se 4 (by rfl) ⟨307593, by rfl⟩ : syracuseStep 3280997 = 615187) (by norm_num)
theorem B2187331 : Blo 2185435 2187331 := bstep (se 1 (by rfl) ⟨1640498, by rfl⟩ : syracuseStep 2187331 = 3280997) B3280997
theorem B7007381 : Blo 2185435 7007381 := bbase (se 6 (by rfl) ⟨164235, by rfl⟩ : syracuseStep 7007381 = 328471) (by norm_num)
theorem B4671587 : Blo 2185435 4671587 := bstep (se 1 (by rfl) ⟨3503690, by rfl⟩ : syracuseStep 4671587 = 7007381) B7007381
theorem B3114391 : Blo 2185435 3114391 := bstep (se 1 (by rfl) ⟨2335793, by rfl⟩ : syracuseStep 3114391 = 4671587) B4671587
theorem B4152521 : Blo 2185435 4152521 := bstep (se 2 (by rfl) ⟨1557195, by rfl⟩ : syracuseStep 4152521 = 3114391) B3114391
theorem B2768347 : Blo 2185435 2768347 := bstep (se 1 (by rfl) ⟨2076260, by rfl⟩ : syracuseStep 2768347 = 4152521) B4152521
theorem B3691129 : Blo 2185435 3691129 := bstep (se 2 (by rfl) ⟨1384173, by rfl⟩ : syracuseStep 3691129 = 2768347) B2768347
theorem B4921505 : Blo 2185435 4921505 := bstep (se 2 (by rfl) ⟨1845564, by rfl⟩ : syracuseStep 4921505 = 3691129) B3691129
theorem B3281003 : Blo 2185435 3281003 := bstep (se 1 (by rfl) ⟨2460752, by rfl⟩ : syracuseStep 3281003 = 4921505) B4921505
theorem B2187335 : Blo 2185435 2187335 := bstep (se 1 (by rfl) ⟨1640501, by rfl⟩ : syracuseStep 2187335 = 3281003) B3281003
theorem B2460757 : Blo 2185435 2460757 := bbase (se 8 (by rfl) ⟨14418, by rfl⟩ : syracuseStep 2460757 = 28837) (by norm_num)
theorem B3281009 : Blo 2185435 3281009 := bstep (se 2 (by rfl) ⟨1230378, by rfl⟩ : syracuseStep 3281009 = 2460757) B2460757
theorem B2187339 : Blo 2185435 2187339 := bstep (se 1 (by rfl) ⟨1640504, by rfl⟩ : syracuseStep 2187339 = 3281009) B3281009
theorem B2768357 : Blo 2185435 2768357 := bbase (se 4 (by rfl) ⟨259533, by rfl⟩ : syracuseStep 2768357 = 519067) (by norm_num)
theorem B7382285 : Blo 2185435 7382285 := bstep (se 3 (by rfl) ⟨1384178, by rfl⟩ : syracuseStep 7382285 = 2768357) B2768357
theorem B4921523 : Blo 2185435 4921523 := bstep (se 1 (by rfl) ⟨3691142, by rfl⟩ : syracuseStep 4921523 = 7382285) B7382285
theorem B3281015 : Blo 2185435 3281015 := bstep (se 1 (by rfl) ⟨2460761, by rfl⟩ : syracuseStep 3281015 = 4921523) B4921523
theorem B2187343 : Blo 2185435 2187343 := bstep (se 1 (by rfl) ⟨1640507, by rfl⟩ : syracuseStep 2187343 = 3281015) B3281015
theorem B3281021 : Blo 2185435 3281021 := bbase (se 3 (by rfl) ⟨615191, by rfl⟩ : syracuseStep 3281021 = 1230383) (by norm_num)
theorem B2187347 : Blo 2185435 2187347 := bstep (se 1 (by rfl) ⟨1640510, by rfl⟩ : syracuseStep 2187347 = 3281021) B3281021
theorem B4921541 : Blo 2185435 4921541 := bbase (se 4 (by rfl) ⟨461394, by rfl⟩ : syracuseStep 4921541 = 922789) (by norm_num)
theorem B3281027 : Blo 2185435 3281027 := bstep (se 1 (by rfl) ⟨2460770, by rfl⟩ : syracuseStep 3281027 = 4921541) B4921541
theorem B2187351 : Blo 2185435 2187351 := bstep (se 1 (by rfl) ⟨1640513, by rfl⟩ : syracuseStep 2187351 = 3281027) B3281027
theorem B3599981 : Blo 2185435 3599981 := bbase (se 3 (by rfl) ⟨674996, by rfl⟩ : syracuseStep 3599981 = 1349993) (by norm_num)
theorem B2399987 : Blo 2185435 2399987 := bstep (se 1 (by rfl) ⟨1799990, by rfl⟩ : syracuseStep 2399987 = 3599981) B3599981
theorem B6399965 : Blo 2185435 6399965 := bstep (se 3 (by rfl) ⟨1199993, by rfl⟩ : syracuseStep 6399965 = 2399987) B2399987
theorem B4266643 : Blo 2185435 4266643 := bstep (se 1 (by rfl) ⟨3199982, by rfl⟩ : syracuseStep 4266643 = 6399965) B6399965
theorem B5688857 : Blo 2185435 5688857 := bstep (se 2 (by rfl) ⟨2133321, by rfl⟩ : syracuseStep 5688857 = 4266643) B4266643
theorem B15170285 : Blo 2185435 15170285 := bstep (se 3 (by rfl) ⟨2844428, by rfl⟩ : syracuseStep 15170285 = 5688857) B5688857
theorem B40454093 : Blo 2185435 40454093 := bstep (se 3 (by rfl) ⟨7585142, by rfl⟩ : syracuseStep 40454093 = 15170285) B15170285
theorem B107877581 : Blo 2185435 107877581 := bstep (se 3 (by rfl) ⟨20227046, by rfl⟩ : syracuseStep 107877581 = 40454093) B40454093
theorem B71918387 : Blo 2185435 71918387 := bstep (se 1 (by rfl) ⟨53938790, by rfl⟩ : syracuseStep 71918387 = 107877581) B107877581
theorem B47945591 : Blo 2185435 47945591 := bstep (se 1 (by rfl) ⟨35959193, by rfl⟩ : syracuseStep 47945591 = 71918387) B71918387
theorem B31963727 : Blo 2185435 31963727 := bstep (se 1 (by rfl) ⟨23972795, by rfl⟩ : syracuseStep 31963727 = 47945591) B47945591
theorem B21309151 : Blo 2185435 21309151 := bstep (se 1 (by rfl) ⟨15981863, by rfl⟩ : syracuseStep 21309151 = 31963727) B31963727
theorem B28412201 : Blo 2185435 28412201 := bstep (se 2 (by rfl) ⟨10654575, by rfl⟩ : syracuseStep 28412201 = 21309151) B21309151
theorem B18941467 : Blo 2185435 18941467 := bstep (se 1 (by rfl) ⟨14206100, by rfl⟩ : syracuseStep 18941467 = 28412201) B28412201
theorem B25255289 : Blo 2185435 25255289 := bstep (se 2 (by rfl) ⟨9470733, by rfl⟩ : syracuseStep 25255289 = 18941467) B18941467
theorem B16836859 : Blo 2185435 16836859 := bstep (se 1 (by rfl) ⟨12627644, by rfl⟩ : syracuseStep 16836859 = 25255289) B25255289
theorem B22449145 : Blo 2185435 22449145 := bstep (se 2 (by rfl) ⟨8418429, by rfl⟩ : syracuseStep 22449145 = 16836859) B16836859
theorem B29932193 : Blo 2185435 29932193 := bstep (se 2 (by rfl) ⟨11224572, by rfl⟩ : syracuseStep 29932193 = 22449145) B22449145
theorem B79819181 : Blo 2185435 79819181 := bstep (se 3 (by rfl) ⟨14966096, by rfl⟩ : syracuseStep 79819181 = 29932193) B29932193
theorem B53212787 : Blo 2185435 53212787 := bstep (se 1 (by rfl) ⟨39909590, by rfl⟩ : syracuseStep 53212787 = 79819181) B79819181
theorem B35475191 : Blo 2185435 35475191 := bstep (se 1 (by rfl) ⟨26606393, by rfl⟩ : syracuseStep 35475191 = 53212787) B53212787
theorem B23650127 : Blo 2185435 23650127 := bstep (se 1 (by rfl) ⟨17737595, by rfl⟩ : syracuseStep 23650127 = 35475191) B35475191
theorem B15766751 : Blo 2185435 15766751 := bstep (se 1 (by rfl) ⟨11825063, by rfl⟩ : syracuseStep 15766751 = 23650127) B23650127
theorem B10511167 : Blo 2185435 10511167 := bstep (se 1 (by rfl) ⟨7883375, by rfl⟩ : syracuseStep 10511167 = 15766751) B15766751
theorem B14014889 : Blo 2185435 14014889 := bstep (se 2 (by rfl) ⟨5255583, by rfl⟩ : syracuseStep 14014889 = 10511167) B10511167
theorem B9343259 : Blo 2185435 9343259 := bstep (se 1 (by rfl) ⟨7007444, by rfl⟩ : syracuseStep 9343259 = 14014889) B14014889
theorem B6228839 : Blo 2185435 6228839 := bstep (se 1 (by rfl) ⟨4671629, by rfl⟩ : syracuseStep 6228839 = 9343259) B9343259
theorem B4152559 : Blo 2185435 4152559 := bstep (se 1 (by rfl) ⟨3114419, by rfl⟩ : syracuseStep 4152559 = 6228839) B6228839
theorem B5536745 : Blo 2185435 5536745 := bstep (se 2 (by rfl) ⟨2076279, by rfl⟩ : syracuseStep 5536745 = 4152559) B4152559
theorem B3691163 : Blo 2185435 3691163 := bstep (se 1 (by rfl) ⟨2768372, by rfl⟩ : syracuseStep 3691163 = 5536745) B5536745
theorem B2460775 : Blo 2185435 2460775 := bstep (se 1 (by rfl) ⟨1845581, by rfl⟩ : syracuseStep 2460775 = 3691163) B3691163
theorem B3281033 : Blo 2185435 3281033 := bstep (se 2 (by rfl) ⟨1230387, by rfl⟩ : syracuseStep 3281033 = 2460775) B2460775
theorem B2187355 : Blo 2185435 2187355 := bstep (se 1 (by rfl) ⟨1640516, by rfl⟩ : syracuseStep 2187355 = 3281033) B3281033
theorem B11073509 : Blo 2185435 11073509 := bbase (se 4 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 11073509 = 2076283) (by norm_num)
theorem B7382339 : Blo 2185435 7382339 := bstep (se 1 (by rfl) ⟨5536754, by rfl⟩ : syracuseStep 7382339 = 11073509) B11073509
theorem B4921559 : Blo 2185435 4921559 := bstep (se 1 (by rfl) ⟨3691169, by rfl⟩ : syracuseStep 4921559 = 7382339) B7382339
theorem B3281039 : Blo 2185435 3281039 := bstep (se 1 (by rfl) ⟨2460779, by rfl⟩ : syracuseStep 3281039 = 4921559) B4921559
theorem B2187359 : Blo 2185435 2187359 := bstep (se 1 (by rfl) ⟨1640519, by rfl⟩ : syracuseStep 2187359 = 3281039) B3281039
theorem B3281045 : Blo 2185435 3281045 := bbase (se 6 (by rfl) ⟨76899, by rfl⟩ : syracuseStep 3281045 = 153799) (by norm_num)
theorem B2187363 : Blo 2185435 2187363 := bstep (se 1 (by rfl) ⟨1640522, by rfl⟩ : syracuseStep 2187363 = 3281045) B3281045
theorem B3503741 : Blo 2185435 3503741 := bbase (se 3 (by rfl) ⟨656951, by rfl⟩ : syracuseStep 3503741 = 1313903) (by norm_num)
theorem B9343309 : Blo 2185435 9343309 := bstep (se 3 (by rfl) ⟨1751870, by rfl⟩ : syracuseStep 9343309 = 3503741) B3503741
theorem B12457745 : Blo 2185435 12457745 := bstep (se 2 (by rfl) ⟨4671654, by rfl⟩ : syracuseStep 12457745 = 9343309) B9343309
theorem B8305163 : Blo 2185435 8305163 := bstep (se 1 (by rfl) ⟨6228872, by rfl⟩ : syracuseStep 8305163 = 12457745) B12457745
theorem B5536775 : Blo 2185435 5536775 := bstep (se 1 (by rfl) ⟨4152581, by rfl⟩ : syracuseStep 5536775 = 8305163) B8305163
theorem B3691183 : Blo 2185435 3691183 := bstep (se 1 (by rfl) ⟨2768387, by rfl⟩ : syracuseStep 3691183 = 5536775) B5536775
theorem B4921577 : Blo 2185435 4921577 := bstep (se 2 (by rfl) ⟨1845591, by rfl⟩ : syracuseStep 4921577 = 3691183) B3691183
theorem B3281051 : Blo 2185435 3281051 := bstep (se 1 (by rfl) ⟨2460788, by rfl⟩ : syracuseStep 3281051 = 4921577) B4921577
theorem B2187367 : Blo 2185435 2187367 := bstep (se 1 (by rfl) ⟨1640525, by rfl⟩ : syracuseStep 2187367 = 3281051) B3281051
theorem B2460793 : Blo 2185435 2460793 := bbase (se 2 (by rfl) ⟨922797, by rfl⟩ : syracuseStep 2460793 = 1845595) (by norm_num)
theorem B3281057 : Blo 2185435 3281057 := bstep (se 2 (by rfl) ⟨1230396, by rfl⟩ : syracuseStep 3281057 = 2460793) B2460793
theorem B2187371 : Blo 2185435 2187371 := bstep (se 1 (by rfl) ⟨1640528, by rfl⟩ : syracuseStep 2187371 = 3281057) B3281057
theorem B3325829 : Blo 2185435 3325829 := bbase (se 4 (by rfl) ⟨311796, by rfl⟩ : syracuseStep 3325829 = 623593) (by norm_num)
theorem B35475509 : Blo 2185435 35475509 := bstep (se 5 (by rfl) ⟨1662914, by rfl⟩ : syracuseStep 35475509 = 3325829) B3325829
theorem B23650339 : Blo 2185435 23650339 := bstep (se 1 (by rfl) ⟨17737754, by rfl⟩ : syracuseStep 23650339 = 35475509) B35475509
theorem B31533785 : Blo 2185435 31533785 := bstep (se 2 (by rfl) ⟨11825169, by rfl⟩ : syracuseStep 31533785 = 23650339) B23650339
theorem B21022523 : Blo 2185435 21022523 := bstep (se 1 (by rfl) ⟨15766892, by rfl⟩ : syracuseStep 21022523 = 31533785) B31533785
theorem B14015015 : Blo 2185435 14015015 := bstep (se 1 (by rfl) ⟨10511261, by rfl⟩ : syracuseStep 14015015 = 21022523) B21022523
theorem B9343343 : Blo 2185435 9343343 := bstep (se 1 (by rfl) ⟨7007507, by rfl⟩ : syracuseStep 9343343 = 14015015) B14015015
theorem B6228895 : Blo 2185435 6228895 := bstep (se 1 (by rfl) ⟨4671671, by rfl⟩ : syracuseStep 6228895 = 9343343) B9343343
theorem B8305193 : Blo 2185435 8305193 := bstep (se 2 (by rfl) ⟨3114447, by rfl⟩ : syracuseStep 8305193 = 6228895) B6228895
theorem B5536795 : Blo 2185435 5536795 := bstep (se 1 (by rfl) ⟨4152596, by rfl⟩ : syracuseStep 5536795 = 8305193) B8305193
theorem B7382393 : Blo 2185435 7382393 := bstep (se 2 (by rfl) ⟨2768397, by rfl⟩ : syracuseStep 7382393 = 5536795) B5536795
theorem B4921595 : Blo 2185435 4921595 := bstep (se 1 (by rfl) ⟨3691196, by rfl⟩ : syracuseStep 4921595 = 7382393) B7382393
theorem B3281063 : Blo 2185435 3281063 := bstep (se 1 (by rfl) ⟨2460797, by rfl⟩ : syracuseStep 3281063 = 4921595) B4921595
theorem B2187375 : Blo 2185435 2187375 := bstep (se 1 (by rfl) ⟨1640531, by rfl⟩ : syracuseStep 2187375 = 3281063) B3281063
theorem B3281069 : Blo 2185435 3281069 := bbase (se 3 (by rfl) ⟨615200, by rfl⟩ : syracuseStep 3281069 = 1230401) (by norm_num)
theorem B2187379 : Blo 2185435 2187379 := bstep (se 1 (by rfl) ⟨1640534, by rfl⟩ : syracuseStep 2187379 = 3281069) B3281069
theorem B4921613 : Blo 2185435 4921613 := bbase (se 3 (by rfl) ⟨922802, by rfl⟩ : syracuseStep 4921613 = 1845605) (by norm_num)
theorem B3281075 : Blo 2185435 3281075 := bstep (se 1 (by rfl) ⟨2460806, by rfl⟩ : syracuseStep 3281075 = 4921613) B4921613
theorem B2187383 : Blo 2185435 2187383 := bstep (se 1 (by rfl) ⟨1640537, by rfl⟩ : syracuseStep 2187383 = 3281075) B3281075
theorem B2768413 : Blo 2185435 2768413 := bbase (se 3 (by rfl) ⟨519077, by rfl⟩ : syracuseStep 2768413 = 1038155) (by norm_num)
theorem B3691217 : Blo 2185435 3691217 := bstep (se 2 (by rfl) ⟨1384206, by rfl⟩ : syracuseStep 3691217 = 2768413) B2768413
theorem B2460811 : Blo 2185435 2460811 := bstep (se 1 (by rfl) ⟨1845608, by rfl⟩ : syracuseStep 2460811 = 3691217) B3691217
theorem B3281081 : Blo 2185435 3281081 := bstep (se 2 (by rfl) ⟨1230405, by rfl⟩ : syracuseStep 3281081 = 2460811) B2460811
theorem B2187387 : Blo 2185435 2187387 := bstep (se 1 (by rfl) ⟨1640540, by rfl⟩ : syracuseStep 2187387 = 3281081) B3281081
theorem B5255669 : Blo 2185435 5255669 := bbase (se 5 (by rfl) ⟨246359, by rfl⟩ : syracuseStep 5255669 = 492719) (by norm_num)
theorem B3503779 : Blo 2185435 3503779 := bstep (se 1 (by rfl) ⟨2627834, by rfl⟩ : syracuseStep 3503779 = 5255669) B5255669
theorem B18686821 : Blo 2185435 18686821 := bstep (se 4 (by rfl) ⟨1751889, by rfl⟩ : syracuseStep 18686821 = 3503779) B3503779
theorem B24915761 : Blo 2185435 24915761 := bstep (se 2 (by rfl) ⟨9343410, by rfl⟩ : syracuseStep 24915761 = 18686821) B18686821
theorem B16610507 : Blo 2185435 16610507 := bstep (se 1 (by rfl) ⟨12457880, by rfl⟩ : syracuseStep 16610507 = 24915761) B24915761
theorem B11073671 : Blo 2185435 11073671 := bstep (se 1 (by rfl) ⟨8305253, by rfl⟩ : syracuseStep 11073671 = 16610507) B16610507
theorem B7382447 : Blo 2185435 7382447 := bstep (se 1 (by rfl) ⟨5536835, by rfl⟩ : syracuseStep 7382447 = 11073671) B11073671
theorem B4921631 : Blo 2185435 4921631 := bstep (se 1 (by rfl) ⟨3691223, by rfl⟩ : syracuseStep 4921631 = 7382447) B7382447
theorem B3281087 : Blo 2185435 3281087 := bstep (se 1 (by rfl) ⟨2460815, by rfl⟩ : syracuseStep 3281087 = 4921631) B4921631
theorem B2187391 : Blo 2185435 2187391 := bstep (se 1 (by rfl) ⟨1640543, by rfl⟩ : syracuseStep 2187391 = 3281087) B3281087
theorem B3281093 : Blo 2185435 3281093 := bbase (se 4 (by rfl) ⟨307602, by rfl⟩ : syracuseStep 3281093 = 615205) (by norm_num)
theorem B2187395 : Blo 2185435 2187395 := bstep (se 1 (by rfl) ⟨1640546, by rfl⟩ : syracuseStep 2187395 = 3281093) B3281093
theorem B3691237 : Blo 2185435 3691237 := bbase (se 4 (by rfl) ⟨346053, by rfl⟩ : syracuseStep 3691237 = 692107) (by norm_num)
theorem B4921649 : Blo 2185435 4921649 := bstep (se 2 (by rfl) ⟨1845618, by rfl⟩ : syracuseStep 4921649 = 3691237) B3691237
theorem B3281099 : Blo 2185435 3281099 := bstep (se 1 (by rfl) ⟨2460824, by rfl⟩ : syracuseStep 3281099 = 4921649) B4921649
theorem B2187399 : Blo 2185435 2187399 := bstep (se 1 (by rfl) ⟨1640549, by rfl⟩ : syracuseStep 2187399 = 3281099) B3281099
theorem B2460829 : Blo 2185435 2460829 := bbase (se 3 (by rfl) ⟨461405, by rfl⟩ : syracuseStep 2460829 = 922811) (by norm_num)
theorem B3281105 : Blo 2185435 3281105 := bstep (se 2 (by rfl) ⟨1230414, by rfl⟩ : syracuseStep 3281105 = 2460829) B2460829
theorem B2187403 : Blo 2185435 2187403 := bstep (se 1 (by rfl) ⟨1640552, by rfl⟩ : syracuseStep 2187403 = 3281105) B3281105
theorem B7382501 : Blo 2185435 7382501 := bbase (se 4 (by rfl) ⟨692109, by rfl⟩ : syracuseStep 7382501 = 1384219) (by norm_num)
theorem B4921667 : Blo 2185435 4921667 := bstep (se 1 (by rfl) ⟨3691250, by rfl⟩ : syracuseStep 4921667 = 7382501) B7382501
theorem B3281111 : Blo 2185435 3281111 := bstep (se 1 (by rfl) ⟨2460833, by rfl⟩ : syracuseStep 3281111 = 4921667) B4921667
theorem B2187407 : Blo 2185435 2187407 := bstep (se 1 (by rfl) ⟨1640555, by rfl⟩ : syracuseStep 2187407 = 3281111) B3281111
theorem B3281117 : Blo 2185435 3281117 := bbase (se 3 (by rfl) ⟨615209, by rfl⟩ : syracuseStep 3281117 = 1230419) (by norm_num)
theorem B2187411 : Blo 2185435 2187411 := bstep (se 1 (by rfl) ⟨1640558, by rfl⟩ : syracuseStep 2187411 = 3281117) B3281117
theorem B4921685 : Blo 2185435 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B3281123 : Blo 2185435 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B2187415 : Blo 2185435 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B2627869 : Blo 2185435 2627869 := bbase (se 3 (by rfl) ⟨492725, by rfl⟩ : syracuseStep 2627869 = 985451) (by norm_num)
theorem B3503825 : Blo 2185435 3503825 := bstep (se 2 (by rfl) ⟨1313934, by rfl⟩ : syracuseStep 3503825 = 2627869) B2627869
theorem B2335883 : Blo 2185435 2335883 := bstep (se 1 (by rfl) ⟨1751912, by rfl⟩ : syracuseStep 2335883 = 3503825) B3503825
theorem B6229021 : Blo 2185435 6229021 := bstep (se 3 (by rfl) ⟨1167941, by rfl⟩ : syracuseStep 6229021 = 2335883) B2335883
theorem B8305361 : Blo 2185435 8305361 := bstep (se 2 (by rfl) ⟨3114510, by rfl⟩ : syracuseStep 8305361 = 6229021) B6229021
theorem B5536907 : Blo 2185435 5536907 := bstep (se 1 (by rfl) ⟨4152680, by rfl⟩ : syracuseStep 5536907 = 8305361) B8305361
theorem B3691271 : Blo 2185435 3691271 := bstep (se 1 (by rfl) ⟨2768453, by rfl⟩ : syracuseStep 3691271 = 5536907) B5536907
theorem B2460847 : Blo 2185435 2460847 := bstep (se 1 (by rfl) ⟨1845635, by rfl⟩ : syracuseStep 2460847 = 3691271) B3691271
theorem B3281129 : Blo 2185435 3281129 := bstep (se 2 (by rfl) ⟨1230423, by rfl⟩ : syracuseStep 3281129 = 2460847) B2460847
theorem B2187419 : Blo 2185435 2187419 := bstep (se 1 (by rfl) ⟨1640564, by rfl⟩ : syracuseStep 2187419 = 3281129) B3281129
theorem B2956357 : Blo 2185435 2956357 := bbase (se 4 (by rfl) ⟨277158, by rfl⟩ : syracuseStep 2956357 = 554317) (by norm_num)
theorem B15767237 : Blo 2185435 15767237 := bstep (se 4 (by rfl) ⟨1478178, by rfl⟩ : syracuseStep 15767237 = 2956357) B2956357
theorem B42045965 : Blo 2185435 42045965 := bstep (se 3 (by rfl) ⟨7883618, by rfl⟩ : syracuseStep 42045965 = 15767237) B15767237
theorem B28030643 : Blo 2185435 28030643 := bstep (se 1 (by rfl) ⟨21022982, by rfl⟩ : syracuseStep 28030643 = 42045965) B42045965
theorem B18687095 : Blo 2185435 18687095 := bstep (se 1 (by rfl) ⟨14015321, by rfl⟩ : syracuseStep 18687095 = 28030643) B28030643
theorem B12458063 : Blo 2185435 12458063 := bstep (se 1 (by rfl) ⟨9343547, by rfl⟩ : syracuseStep 12458063 = 18687095) B18687095
theorem B8305375 : Blo 2185435 8305375 := bstep (se 1 (by rfl) ⟨6229031, by rfl⟩ : syracuseStep 8305375 = 12458063) B12458063
theorem B11073833 : Blo 2185435 11073833 := bstep (se 2 (by rfl) ⟨4152687, by rfl⟩ : syracuseStep 11073833 = 8305375) B8305375
theorem B7382555 : Blo 2185435 7382555 := bstep (se 1 (by rfl) ⟨5536916, by rfl⟩ : syracuseStep 7382555 = 11073833) B11073833
theorem B4921703 : Blo 2185435 4921703 := bstep (se 1 (by rfl) ⟨3691277, by rfl⟩ : syracuseStep 4921703 = 7382555) B7382555
theorem B3281135 : Blo 2185435 3281135 := bstep (se 1 (by rfl) ⟨2460851, by rfl⟩ : syracuseStep 3281135 = 4921703) B4921703
theorem B2187423 : Blo 2185435 2187423 := bstep (se 1 (by rfl) ⟨1640567, by rfl⟩ : syracuseStep 2187423 = 3281135) B3281135
theorem B3281141 : Blo 2185435 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B2187427 : Blo 2185435 2187427 := bstep (se 1 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 2187427 = 3281141) B3281141
theorem B6651829 : Blo 2185435 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B8869105 : Blo 2185435 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B47301893 : Blo 2185435 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B31534595 : Blo 2185435 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B21023063 : Blo 2185435 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B14015375 : Blo 2185435 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B9343583 : Blo 2185435 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B6229055 : Blo 2185435 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B4152703 : Blo 2185435 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B5536937 : Blo 2185435 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B3691291 : Blo 2185435 3691291 := bstep (se 1 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 3691291 = 5536937) B5536937
theorem B4921721 : Blo 2185435 4921721 := bstep (se 2 (by rfl) ⟨1845645, by rfl⟩ : syracuseStep 4921721 = 3691291) B3691291
theorem B3281147 : Blo 2185435 3281147 := bstep (se 1 (by rfl) ⟨2460860, by rfl⟩ : syracuseStep 3281147 = 4921721) B4921721
theorem B2187431 : Blo 2185435 2187431 := bstep (se 1 (by rfl) ⟨1640573, by rfl⟩ : syracuseStep 2187431 = 3281147) B3281147
theorem B2460865 : Blo 2185435 2460865 := bbase (se 2 (by rfl) ⟨922824, by rfl⟩ : syracuseStep 2460865 = 1845649) (by norm_num)
theorem B3281153 : Blo 2185435 3281153 := bstep (se 2 (by rfl) ⟨1230432, by rfl⟩ : syracuseStep 3281153 = 2460865) B2460865
theorem B2187435 : Blo 2185435 2187435 := bstep (se 1 (by rfl) ⟨1640576, by rfl⟩ : syracuseStep 2187435 = 3281153) B3281153
theorem C0 (j : ℕ) (h1 : 546358 ≤ j) (h2 : j ≤ 546858) : Blo 2185435 (4 * j + 3) := by
  interval_cases j
  · exact B2185435
  · exact B2185439
  · exact B2185443
  · exact B2185447
  · exact B2185451
  · exact B2185455
  · exact B2185459
  · exact B2185463
  · exact B2185467
  · exact B2185471
  · exact B2185475
  · exact B2185479
  · exact B2185483
  · exact B2185487
  · exact B2185491
  · exact B2185495
  · exact B2185499
  · exact B2185503
  · exact B2185507
  · exact B2185511
  · exact B2185515
  · exact B2185519
  · exact B2185523
  · exact B2185527
  · exact B2185531
  · exact B2185535
  · exact B2185539
  · exact B2185543
  · exact B2185547
  · exact B2185551
  · exact B2185555
  · exact B2185559
  · exact B2185563
  · exact B2185567
  · exact B2185571
  · exact B2185575
  · exact B2185579
  · exact B2185583
  · exact B2185587
  · exact B2185591
  · exact B2185595
  · exact B2185599
  · exact B2185603
  · exact B2185607
  · exact B2185611
  · exact B2185615
  · exact B2185619
  · exact B2185623
  · exact B2185627
  · exact B2185631
  · exact B2185635
  · exact B2185639
  · exact B2185643
  · exact B2185647
  · exact B2185651
  · exact B2185655
  · exact B2185659
  · exact B2185663
  · exact B2185667
  · exact B2185671
  · exact B2185675
  · exact B2185679
  · exact B2185683
  · exact B2185687
  · exact B2185691
  · exact B2185695
  · exact B2185699
  · exact B2185703
  · exact B2185707
  · exact B2185711
  · exact B2185715
  · exact B2185719
  · exact B2185723
  · exact B2185727
  · exact B2185731
  · exact B2185735
  · exact B2185739
  · exact B2185743
  · exact B2185747
  · exact B2185751
  · exact B2185755
  · exact B2185759
  · exact B2185763
  · exact B2185767
  · exact B2185771
  · exact B2185775
  · exact B2185779
  · exact B2185783
  · exact B2185787
  · exact B2185791
  · exact B2185795
  · exact B2185799
  · exact B2185803
  · exact B2185807
  · exact B2185811
  · exact B2185815
  · exact B2185819
  · exact B2185823
  · exact B2185827
  · exact B2185831
  · exact B2185835
  · exact B2185839
  · exact B2185843
  · exact B2185847
  · exact B2185851
  · exact B2185855
  · exact B2185859
  · exact B2185863
  · exact B2185867
  · exact B2185871
  · exact B2185875
  · exact B2185879
  · exact B2185883
  · exact B2185887
  · exact B2185891
  · exact B2185895
  · exact B2185899
  · exact B2185903
  · exact B2185907
  · exact B2185911
  · exact B2185915
  · exact B2185919
  · exact B2185923
  · exact B2185927
  · exact B2185931
  · exact B2185935
  · exact B2185939
  · exact B2185943
  · exact B2185947
  · exact B2185951
  · exact B2185955
  · exact B2185959
  · exact B2185963
  · exact B2185967
  · exact B2185971
  · exact B2185975
  · exact B2185979
  · exact B2185983
  · exact B2185987
  · exact B2185991
  · exact B2185995
  · exact B2185999
  · exact B2186003
  · exact B2186007
  · exact B2186011
  · exact B2186015
  · exact B2186019
  · exact B2186023
  · exact B2186027
  · exact B2186031
  · exact B2186035
  · exact B2186039
  · exact B2186043
  · exact B2186047
  · exact B2186051
  · exact B2186055
  · exact B2186059
  · exact B2186063
  · exact B2186067
  · exact B2186071
  · exact B2186075
  · exact B2186079
  · exact B2186083
  · exact B2186087
  · exact B2186091
  · exact B2186095
  · exact B2186099
  · exact B2186103
  · exact B2186107
  · exact B2186111
  · exact B2186115
  · exact B2186119
  · exact B2186123
  · exact B2186127
  · exact B2186131
  · exact B2186135
  · exact B2186139
  · exact B2186143
  · exact B2186147
  · exact B2186151
  · exact B2186155
  · exact B2186159
  · exact B2186163
  · exact B2186167
  · exact B2186171
  · exact B2186175
  · exact B2186179
  · exact B2186183
  · exact B2186187
  · exact B2186191
  · exact B2186195
  · exact B2186199
  · exact B2186203
  · exact B2186207
  · exact B2186211
  · exact B2186215
  · exact B2186219
  · exact B2186223
  · exact B2186227
  · exact B2186231
  · exact B2186235
  · exact B2186239
  · exact B2186243
  · exact B2186247
  · exact B2186251
  · exact B2186255
  · exact B2186259
  · exact B2186263
  · exact B2186267
  · exact B2186271
  · exact B2186275
  · exact B2186279
  · exact B2186283
  · exact B2186287
  · exact B2186291
  · exact B2186295
  · exact B2186299
  · exact B2186303
  · exact B2186307
  · exact B2186311
  · exact B2186315
  · exact B2186319
  · exact B2186323
  · exact B2186327
  · exact B2186331
  · exact B2186335
  · exact B2186339
  · exact B2186343
  · exact B2186347
  · exact B2186351
  · exact B2186355
  · exact B2186359
  · exact B2186363
  · exact B2186367
  · exact B2186371
  · exact B2186375
  · exact B2186379
  · exact B2186383
  · exact B2186387
  · exact B2186391
  · exact B2186395
  · exact B2186399
  · exact B2186403
  · exact B2186407
  · exact B2186411
  · exact B2186415
  · exact B2186419
  · exact B2186423
  · exact B2186427
  · exact B2186431
  · exact B2186435
  · exact B2186439
  · exact B2186443
  · exact B2186447
  · exact B2186451
  · exact B2186455
  · exact B2186459
  · exact B2186463
  · exact B2186467
  · exact B2186471
  · exact B2186475
  · exact B2186479
  · exact B2186483
  · exact B2186487
  · exact B2186491
  · exact B2186495
  · exact B2186499
  · exact B2186503
  · exact B2186507
  · exact B2186511
  · exact B2186515
  · exact B2186519
  · exact B2186523
  · exact B2186527
  · exact B2186531
  · exact B2186535
  · exact B2186539
  · exact B2186543
  · exact B2186547
  · exact B2186551
  · exact B2186555
  · exact B2186559
  · exact B2186563
  · exact B2186567
  · exact B2186571
  · exact B2186575
  · exact B2186579
  · exact B2186583
  · exact B2186587
  · exact B2186591
  · exact B2186595
  · exact B2186599
  · exact B2186603
  · exact B2186607
  · exact B2186611
  · exact B2186615
  · exact B2186619
  · exact B2186623
  · exact B2186627
  · exact B2186631
  · exact B2186635
  · exact B2186639
  · exact B2186643
  · exact B2186647
  · exact B2186651
  · exact B2186655
  · exact B2186659
  · exact B2186663
  · exact B2186667
  · exact B2186671
  · exact B2186675
  · exact B2186679
  · exact B2186683
  · exact B2186687
  · exact B2186691
  · exact B2186695
  · exact B2186699
  · exact B2186703
  · exact B2186707
  · exact B2186711
  · exact B2186715
  · exact B2186719
  · exact B2186723
  · exact B2186727
  · exact B2186731
  · exact B2186735
  · exact B2186739
  · exact B2186743
  · exact B2186747
  · exact B2186751
  · exact B2186755
  · exact B2186759
  · exact B2186763
  · exact B2186767
  · exact B2186771
  · exact B2186775
  · exact B2186779
  · exact B2186783
  · exact B2186787
  · exact B2186791
  · exact B2186795
  · exact B2186799
  · exact B2186803
  · exact B2186807
  · exact B2186811
  · exact B2186815
  · exact B2186819
  · exact B2186823
  · exact B2186827
  · exact B2186831
  · exact B2186835
  · exact B2186839
  · exact B2186843
  · exact B2186847
  · exact B2186851
  · exact B2186855
  · exact B2186859
  · exact B2186863
  · exact B2186867
  · exact B2186871
  · exact B2186875
  · exact B2186879
  · exact B2186883
  · exact B2186887
  · exact B2186891
  · exact B2186895
  · exact B2186899
  · exact B2186903
  · exact B2186907
  · exact B2186911
  · exact B2186915
  · exact B2186919
  · exact B2186923
  · exact B2186927
  · exact B2186931
  · exact B2186935
  · exact B2186939
  · exact B2186943
  · exact B2186947
  · exact B2186951
  · exact B2186955
  · exact B2186959
  · exact B2186963
  · exact B2186967
  · exact B2186971
  · exact B2186975
  · exact B2186979
  · exact B2186983
  · exact B2186987
  · exact B2186991
  · exact B2186995
  · exact B2186999
  · exact B2187003
  · exact B2187007
  · exact B2187011
  · exact B2187015
  · exact B2187019
  · exact B2187023
  · exact B2187027
  · exact B2187031
  · exact B2187035
  · exact B2187039
  · exact B2187043
  · exact B2187047
  · exact B2187051
  · exact B2187055
  · exact B2187059
  · exact B2187063
  · exact B2187067
  · exact B2187071
  · exact B2187075
  · exact B2187079
  · exact B2187083
  · exact B2187087
  · exact B2187091
  · exact B2187095
  · exact B2187099
  · exact B2187103
  · exact B2187107
  · exact B2187111
  · exact B2187115
  · exact B2187119
  · exact B2187123
  · exact B2187127
  · exact B2187131
  · exact B2187135
  · exact B2187139
  · exact B2187143
  · exact B2187147
  · exact B2187151
  · exact B2187155
  · exact B2187159
  · exact B2187163
  · exact B2187167
  · exact B2187171
  · exact B2187175
  · exact B2187179
  · exact B2187183
  · exact B2187187
  · exact B2187191
  · exact B2187195
  · exact B2187199
  · exact B2187203
  · exact B2187207
  · exact B2187211
  · exact B2187215
  · exact B2187219
  · exact B2187223
  · exact B2187227
  · exact B2187231
  · exact B2187235
  · exact B2187239
  · exact B2187243
  · exact B2187247
  · exact B2187251
  · exact B2187255
  · exact B2187259
  · exact B2187263
  · exact B2187267
  · exact B2187271
  · exact B2187275
  · exact B2187279
  · exact B2187283
  · exact B2187287
  · exact B2187291
  · exact B2187295
  · exact B2187299
  · exact B2187303
  · exact B2187307
  · exact B2187311
  · exact B2187315
  · exact B2187319
  · exact B2187323
  · exact B2187327
  · exact B2187331
  · exact B2187335
  · exact B2187339
  · exact B2187343
  · exact B2187347
  · exact B2187351
  · exact B2187355
  · exact B2187359
  · exact B2187363
  · exact B2187367
  · exact B2187371
  · exact B2187375
  · exact B2187379
  · exact B2187383
  · exact B2187387
  · exact B2187391
  · exact B2187395
  · exact B2187399
  · exact B2187403
  · exact B2187407
  · exact B2187411
  · exact B2187415
  · exact B2187419
  · exact B2187423
  · exact B2187427
  · exact B2187431
  · exact B2187435
theorem solution (m : ℕ) (hlo : 2185435 ≤ m) (hhi : m ≤ 2187435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 546358 ≤ j := by omega
    have hj2 : j ≤ 546858 := by omega
    have hb : Blo 2185435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
