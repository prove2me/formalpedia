-- Prove2me | solution 1 for syracuse_descends_range_1889435_1891435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:46:39.898483+00:00
-- url     : https://prove2.me/submissions/5d837e67-cdca-4609-9fad-8651647a54ba

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

theorem B4035349 : Blo 1889435 4035349 := bbase (se 6 (by rfl) ⟨94578, by rfl⟩ : syracuseStep 4035349 = 189157) (by norm_num)
theorem B5380465 : Blo 1889435 5380465 := bstep (se 2 (by rfl) ⟨2017674, by rfl⟩ : syracuseStep 5380465 = 4035349) B4035349
theorem B7173953 : Blo 1889435 7173953 := bstep (se 2 (by rfl) ⟨2690232, by rfl⟩ : syracuseStep 7173953 = 5380465) B5380465
theorem B4782635 : Blo 1889435 4782635 := bstep (se 1 (by rfl) ⟨3586976, by rfl⟩ : syracuseStep 4782635 = 7173953) B7173953
theorem B3188423 : Blo 1889435 3188423 := bstep (se 1 (by rfl) ⟨2391317, by rfl⟩ : syracuseStep 3188423 = 4782635) B4782635
theorem B2125615 : Blo 1889435 2125615 := bstep (se 1 (by rfl) ⟨1594211, by rfl⟩ : syracuseStep 2125615 = 3188423) B3188423
theorem B2834153 : Blo 1889435 2834153 := bstep (se 2 (by rfl) ⟨1062807, by rfl⟩ : syracuseStep 2834153 = 2125615) B2125615
theorem B1889435 : Blo 1889435 1889435 := bstep (se 1 (by rfl) ⟨1417076, by rfl⟩ : syracuseStep 1889435 = 2834153) B2834153
theorem B3830437 : Blo 1889435 3830437 := bbase (se 4 (by rfl) ⟨359103, by rfl⟩ : syracuseStep 3830437 = 718207) (by norm_num)
theorem B5107249 : Blo 1889435 5107249 := bstep (se 2 (by rfl) ⟨1915218, by rfl⟩ : syracuseStep 5107249 = 3830437) B3830437
theorem B6809665 : Blo 1889435 6809665 := bstep (se 2 (by rfl) ⟨2553624, by rfl⟩ : syracuseStep 6809665 = 5107249) B5107249
theorem B9079553 : Blo 1889435 9079553 := bstep (se 2 (by rfl) ⟨3404832, by rfl⟩ : syracuseStep 9079553 = 6809665) B6809665
theorem B24212141 : Blo 1889435 24212141 := bstep (se 3 (by rfl) ⟨4539776, by rfl⟩ : syracuseStep 24212141 = 9079553) B9079553
theorem B16141427 : Blo 1889435 16141427 := bstep (se 1 (by rfl) ⟨12106070, by rfl⟩ : syracuseStep 16141427 = 24212141) B24212141
theorem B10760951 : Blo 1889435 10760951 := bstep (se 1 (by rfl) ⟨8070713, by rfl⟩ : syracuseStep 10760951 = 16141427) B16141427
theorem B7173967 : Blo 1889435 7173967 := bstep (se 1 (by rfl) ⟨5380475, by rfl⟩ : syracuseStep 7173967 = 10760951) B10760951
theorem B9565289 : Blo 1889435 9565289 := bstep (se 2 (by rfl) ⟨3586983, by rfl⟩ : syracuseStep 9565289 = 7173967) B7173967
theorem B6376859 : Blo 1889435 6376859 := bstep (se 1 (by rfl) ⟨4782644, by rfl⟩ : syracuseStep 6376859 = 9565289) B9565289
theorem B4251239 : Blo 1889435 4251239 := bstep (se 1 (by rfl) ⟨3188429, by rfl⟩ : syracuseStep 4251239 = 6376859) B6376859
theorem B2834159 : Blo 1889435 2834159 := bstep (se 1 (by rfl) ⟨2125619, by rfl⟩ : syracuseStep 2834159 = 4251239) B4251239
theorem B1889439 : Blo 1889435 1889439 := bstep (se 1 (by rfl) ⟨1417079, by rfl⟩ : syracuseStep 1889439 = 2834159) B2834159
theorem B2834165 : Blo 1889435 2834165 := bbase (se 5 (by rfl) ⟨132851, by rfl⟩ : syracuseStep 2834165 = 265703) (by norm_num)
theorem B1889443 : Blo 1889435 1889443 := bstep (se 1 (by rfl) ⟨1417082, by rfl⟩ : syracuseStep 1889443 = 2834165) B2834165
theorem B4539797 : Blo 1889435 4539797 := bbase (se 6 (by rfl) ⟨106401, by rfl⟩ : syracuseStep 4539797 = 212803) (by norm_num)
theorem B3026531 : Blo 1889435 3026531 := bstep (se 1 (by rfl) ⟨2269898, by rfl⟩ : syracuseStep 3026531 = 4539797) B4539797
theorem B8070749 : Blo 1889435 8070749 := bstep (se 3 (by rfl) ⟨1513265, by rfl⟩ : syracuseStep 8070749 = 3026531) B3026531
theorem B5380499 : Blo 1889435 5380499 := bstep (se 1 (by rfl) ⟨4035374, by rfl⟩ : syracuseStep 5380499 = 8070749) B8070749
theorem B3586999 : Blo 1889435 3586999 := bstep (se 1 (by rfl) ⟨2690249, by rfl⟩ : syracuseStep 3586999 = 5380499) B5380499
theorem B4782665 : Blo 1889435 4782665 := bstep (se 2 (by rfl) ⟨1793499, by rfl⟩ : syracuseStep 4782665 = 3586999) B3586999
theorem B3188443 : Blo 1889435 3188443 := bstep (se 1 (by rfl) ⟨2391332, by rfl⟩ : syracuseStep 3188443 = 4782665) B4782665
theorem B4251257 : Blo 1889435 4251257 := bstep (se 2 (by rfl) ⟨1594221, by rfl⟩ : syracuseStep 4251257 = 3188443) B3188443
theorem B2834171 : Blo 1889435 2834171 := bstep (se 1 (by rfl) ⟨2125628, by rfl⟩ : syracuseStep 2834171 = 4251257) B4251257
theorem B1889447 : Blo 1889435 1889447 := bstep (se 1 (by rfl) ⟨1417085, by rfl⟩ : syracuseStep 1889447 = 2834171) B2834171
theorem B2125633 : Blo 1889435 2125633 := bbase (se 2 (by rfl) ⟨797112, by rfl⟩ : syracuseStep 2125633 = 1594225) (by norm_num)
theorem B2834177 : Blo 1889435 2834177 := bstep (se 2 (by rfl) ⟨1062816, by rfl⟩ : syracuseStep 2834177 = 2125633) B2125633
theorem B1889451 : Blo 1889435 1889451 := bstep (se 1 (by rfl) ⟨1417088, by rfl⟩ : syracuseStep 1889451 = 2834177) B2834177
theorem B4782685 : Blo 1889435 4782685 := bbase (se 3 (by rfl) ⟨896753, by rfl⟩ : syracuseStep 4782685 = 1793507) (by norm_num)
theorem B6376913 : Blo 1889435 6376913 := bstep (se 2 (by rfl) ⟨2391342, by rfl⟩ : syracuseStep 6376913 = 4782685) B4782685
theorem B4251275 : Blo 1889435 4251275 := bstep (se 1 (by rfl) ⟨3188456, by rfl⟩ : syracuseStep 4251275 = 6376913) B6376913
theorem B2834183 : Blo 1889435 2834183 := bstep (se 1 (by rfl) ⟨2125637, by rfl⟩ : syracuseStep 2834183 = 4251275) B4251275
theorem B1889455 : Blo 1889435 1889455 := bstep (se 1 (by rfl) ⟨1417091, by rfl⟩ : syracuseStep 1889455 = 2834183) B2834183
theorem B2834189 : Blo 1889435 2834189 := bbase (se 3 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 2834189 = 1062821) (by norm_num)
theorem B1889459 : Blo 1889435 1889459 := bstep (se 1 (by rfl) ⟨1417094, by rfl⟩ : syracuseStep 1889459 = 2834189) B2834189
theorem B4251293 : Blo 1889435 4251293 := bbase (se 3 (by rfl) ⟨797117, by rfl⟩ : syracuseStep 4251293 = 1594235) (by norm_num)
theorem B2834195 : Blo 1889435 2834195 := bstep (se 1 (by rfl) ⟨2125646, by rfl⟩ : syracuseStep 2834195 = 4251293) B4251293
theorem B1889463 : Blo 1889435 1889463 := bstep (se 1 (by rfl) ⟨1417097, by rfl⟩ : syracuseStep 1889463 = 2834195) B2834195
theorem B3188477 : Blo 1889435 3188477 := bbase (se 3 (by rfl) ⟨597839, by rfl⟩ : syracuseStep 3188477 = 1195679) (by norm_num)
theorem B2125651 : Blo 1889435 2125651 := bstep (se 1 (by rfl) ⟨1594238, by rfl⟩ : syracuseStep 2125651 = 3188477) B3188477
theorem B2834201 : Blo 1889435 2834201 := bstep (se 2 (by rfl) ⟨1062825, by rfl⟩ : syracuseStep 2834201 = 2125651) B2125651
theorem B1889467 : Blo 1889435 1889467 := bstep (se 1 (by rfl) ⟨1417100, by rfl⟩ : syracuseStep 1889467 = 2834201) B2834201
theorem B15531061 : Blo 1889435 15531061 := bbase (se 5 (by rfl) ⟨728018, by rfl⟩ : syracuseStep 15531061 = 1456037) (by norm_num)
theorem B20708081 : Blo 1889435 20708081 := bstep (se 2 (by rfl) ⟨7765530, by rfl⟩ : syracuseStep 20708081 = 15531061) B15531061
theorem B13805387 : Blo 1889435 13805387 := bstep (se 1 (by rfl) ⟨10354040, by rfl⟩ : syracuseStep 13805387 = 20708081) B20708081
theorem B9203591 : Blo 1889435 9203591 := bstep (se 1 (by rfl) ⟨6902693, by rfl⟩ : syracuseStep 9203591 = 13805387) B13805387
theorem B24542909 : Blo 1889435 24542909 := bstep (se 3 (by rfl) ⟨4601795, by rfl⟩ : syracuseStep 24542909 = 9203591) B9203591
theorem B16361939 : Blo 1889435 16361939 := bstep (se 1 (by rfl) ⟨12271454, by rfl⟩ : syracuseStep 16361939 = 24542909) B24542909
theorem B10907959 : Blo 1889435 10907959 := bstep (se 1 (by rfl) ⟨8180969, by rfl⟩ : syracuseStep 10907959 = 16361939) B16361939
theorem B14543945 : Blo 1889435 14543945 := bstep (se 2 (by rfl) ⟨5453979, by rfl⟩ : syracuseStep 14543945 = 10907959) B10907959
theorem B9695963 : Blo 1889435 9695963 := bstep (se 1 (by rfl) ⟨7271972, by rfl⟩ : syracuseStep 9695963 = 14543945) B14543945
theorem B6463975 : Blo 1889435 6463975 := bstep (se 1 (by rfl) ⟨4847981, by rfl⟩ : syracuseStep 6463975 = 9695963) B9695963
theorem B8618633 : Blo 1889435 8618633 := bstep (se 2 (by rfl) ⟨3231987, by rfl⟩ : syracuseStep 8618633 = 6463975) B6463975
theorem B5745755 : Blo 1889435 5745755 := bstep (se 1 (by rfl) ⟨4309316, by rfl⟩ : syracuseStep 5745755 = 8618633) B8618633
theorem B3830503 : Blo 1889435 3830503 := bstep (se 1 (by rfl) ⟨2872877, by rfl⟩ : syracuseStep 3830503 = 5745755) B5745755
theorem B5107337 : Blo 1889435 5107337 := bstep (se 2 (by rfl) ⟨1915251, by rfl⟩ : syracuseStep 5107337 = 3830503) B3830503
theorem B3404891 : Blo 1889435 3404891 := bstep (se 1 (by rfl) ⟨2553668, by rfl⟩ : syracuseStep 3404891 = 5107337) B5107337
theorem B2269927 : Blo 1889435 2269927 := bstep (se 1 (by rfl) ⟨1702445, by rfl⟩ : syracuseStep 2269927 = 3404891) B3404891
theorem B3026569 : Blo 1889435 3026569 := bstep (se 2 (by rfl) ⟨1134963, by rfl⟩ : syracuseStep 3026569 = 2269927) B2269927
theorem B4035425 : Blo 1889435 4035425 := bstep (se 2 (by rfl) ⟨1513284, by rfl⟩ : syracuseStep 4035425 = 3026569) B3026569
theorem B10761133 : Blo 1889435 10761133 := bstep (se 3 (by rfl) ⟨2017712, by rfl⟩ : syracuseStep 10761133 = 4035425) B4035425
theorem B14348177 : Blo 1889435 14348177 := bstep (se 2 (by rfl) ⟨5380566, by rfl⟩ : syracuseStep 14348177 = 10761133) B10761133
theorem B9565451 : Blo 1889435 9565451 := bstep (se 1 (by rfl) ⟨7174088, by rfl⟩ : syracuseStep 9565451 = 14348177) B14348177
theorem B6376967 : Blo 1889435 6376967 := bstep (se 1 (by rfl) ⟨4782725, by rfl⟩ : syracuseStep 6376967 = 9565451) B9565451
theorem B4251311 : Blo 1889435 4251311 := bstep (se 1 (by rfl) ⟨3188483, by rfl⟩ : syracuseStep 4251311 = 6376967) B6376967
theorem B2834207 : Blo 1889435 2834207 := bstep (se 1 (by rfl) ⟨2125655, by rfl⟩ : syracuseStep 2834207 = 4251311) B4251311
theorem B1889471 : Blo 1889435 1889471 := bstep (se 1 (by rfl) ⟨1417103, by rfl⟩ : syracuseStep 1889471 = 2834207) B2834207
theorem B2834213 : Blo 1889435 2834213 := bbase (se 4 (by rfl) ⟨265707, by rfl⟩ : syracuseStep 2834213 = 531415) (by norm_num)
theorem B1889475 : Blo 1889435 1889475 := bstep (se 1 (by rfl) ⟨1417106, by rfl⟩ : syracuseStep 1889475 = 2834213) B2834213
theorem B2391373 : Blo 1889435 2391373 := bbase (se 3 (by rfl) ⟨448382, by rfl⟩ : syracuseStep 2391373 = 896765) (by norm_num)
theorem B3188497 : Blo 1889435 3188497 := bstep (se 2 (by rfl) ⟨1195686, by rfl⟩ : syracuseStep 3188497 = 2391373) B2391373
theorem B4251329 : Blo 1889435 4251329 := bstep (se 2 (by rfl) ⟨1594248, by rfl⟩ : syracuseStep 4251329 = 3188497) B3188497
theorem B2834219 : Blo 1889435 2834219 := bstep (se 1 (by rfl) ⟨2125664, by rfl⟩ : syracuseStep 2834219 = 4251329) B4251329
theorem B1889479 : Blo 1889435 1889479 := bstep (se 1 (by rfl) ⟨1417109, by rfl⟩ : syracuseStep 1889479 = 2834219) B2834219
theorem B2125669 : Blo 1889435 2125669 := bbase (se 4 (by rfl) ⟨199281, by rfl⟩ : syracuseStep 2125669 = 398563) (by norm_num)
theorem B2834225 : Blo 1889435 2834225 := bstep (se 2 (by rfl) ⟨1062834, by rfl⟩ : syracuseStep 2834225 = 2125669) B2125669
theorem B1889483 : Blo 1889435 1889483 := bstep (se 1 (by rfl) ⟨1417112, by rfl⟩ : syracuseStep 1889483 = 2834225) B2834225
theorem B5380613 : Blo 1889435 5380613 := bbase (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) (by norm_num)
theorem B3587075 : Blo 1889435 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B2391383 : Blo 1889435 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B6377021 : Blo 1889435 6377021 := bstep (se 3 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 6377021 = 2391383) B2391383
theorem B4251347 : Blo 1889435 4251347 := bstep (se 1 (by rfl) ⟨3188510, by rfl⟩ : syracuseStep 4251347 = 6377021) B6377021
theorem B2834231 : Blo 1889435 2834231 := bstep (se 1 (by rfl) ⟨2125673, by rfl⟩ : syracuseStep 2834231 = 4251347) B4251347
theorem B1889487 : Blo 1889435 1889487 := bstep (se 1 (by rfl) ⟨1417115, by rfl⟩ : syracuseStep 1889487 = 2834231) B2834231
theorem B2834237 : Blo 1889435 2834237 := bbase (se 3 (by rfl) ⟨531419, by rfl⟩ : syracuseStep 2834237 = 1062839) (by norm_num)
theorem B1889491 : Blo 1889435 1889491 := bstep (se 1 (by rfl) ⟨1417118, by rfl⟩ : syracuseStep 1889491 = 2834237) B2834237
theorem B4251365 : Blo 1889435 4251365 := bbase (se 4 (by rfl) ⟨398565, by rfl⟩ : syracuseStep 4251365 = 797131) (by norm_num)
theorem B2834243 : Blo 1889435 2834243 := bstep (se 1 (by rfl) ⟨2125682, by rfl⟩ : syracuseStep 2834243 = 4251365) B4251365
theorem B1889495 : Blo 1889435 1889495 := bstep (se 1 (by rfl) ⟨1417121, by rfl⟩ : syracuseStep 1889495 = 2834243) B2834243
theorem B4782797 : Blo 1889435 4782797 := bbase (se 3 (by rfl) ⟨896774, by rfl⟩ : syracuseStep 4782797 = 1793549) (by norm_num)
theorem B3188531 : Blo 1889435 3188531 := bstep (se 1 (by rfl) ⟨2391398, by rfl⟩ : syracuseStep 3188531 = 4782797) B4782797
theorem B2125687 : Blo 1889435 2125687 := bstep (se 1 (by rfl) ⟨1594265, by rfl⟩ : syracuseStep 2125687 = 3188531) B3188531
theorem B2834249 : Blo 1889435 2834249 := bstep (se 2 (by rfl) ⟨1062843, by rfl⟩ : syracuseStep 2834249 = 2125687) B2125687
theorem B1889499 : Blo 1889435 1889499 := bstep (se 1 (by rfl) ⟨1417124, by rfl⟩ : syracuseStep 1889499 = 2834249) B2834249
theorem B3026621 : Blo 1889435 3026621 := bbase (se 3 (by rfl) ⟨567491, by rfl⟩ : syracuseStep 3026621 = 1134983) (by norm_num)
theorem B2017747 : Blo 1889435 2017747 := bstep (se 1 (by rfl) ⟨1513310, by rfl⟩ : syracuseStep 2017747 = 3026621) B3026621
theorem B2690329 : Blo 1889435 2690329 := bstep (se 2 (by rfl) ⟨1008873, by rfl⟩ : syracuseStep 2690329 = 2017747) B2017747
theorem B3587105 : Blo 1889435 3587105 := bstep (se 2 (by rfl) ⟨1345164, by rfl⟩ : syracuseStep 3587105 = 2690329) B2690329
theorem B9565613 : Blo 1889435 9565613 := bstep (se 3 (by rfl) ⟨1793552, by rfl⟩ : syracuseStep 9565613 = 3587105) B3587105
theorem B6377075 : Blo 1889435 6377075 := bstep (se 1 (by rfl) ⟨4782806, by rfl⟩ : syracuseStep 6377075 = 9565613) B9565613
theorem B4251383 : Blo 1889435 4251383 := bstep (se 1 (by rfl) ⟨3188537, by rfl⟩ : syracuseStep 4251383 = 6377075) B6377075
theorem B2834255 : Blo 1889435 2834255 := bstep (se 1 (by rfl) ⟨2125691, by rfl⟩ : syracuseStep 2834255 = 4251383) B4251383
theorem B1889503 : Blo 1889435 1889503 := bstep (se 1 (by rfl) ⟨1417127, by rfl⟩ : syracuseStep 1889503 = 2834255) B2834255
theorem B2834261 : Blo 1889435 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B1889507 : Blo 1889435 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B5107445 : Blo 1889435 5107445 := bbase (se 5 (by rfl) ⟨239411, by rfl⟩ : syracuseStep 5107445 = 478823) (by norm_num)
theorem B3404963 : Blo 1889435 3404963 := bstep (se 1 (by rfl) ⟨2553722, by rfl⟩ : syracuseStep 3404963 = 5107445) B5107445
theorem B9079901 : Blo 1889435 9079901 := bstep (se 3 (by rfl) ⟨1702481, by rfl⟩ : syracuseStep 9079901 = 3404963) B3404963
theorem B6053267 : Blo 1889435 6053267 := bstep (se 1 (by rfl) ⟨4539950, by rfl⟩ : syracuseStep 6053267 = 9079901) B9079901
theorem B4035511 : Blo 1889435 4035511 := bstep (se 1 (by rfl) ⟨3026633, by rfl⟩ : syracuseStep 4035511 = 6053267) B6053267
theorem B5380681 : Blo 1889435 5380681 := bstep (se 2 (by rfl) ⟨2017755, by rfl⟩ : syracuseStep 5380681 = 4035511) B4035511
theorem B7174241 : Blo 1889435 7174241 := bstep (se 2 (by rfl) ⟨2690340, by rfl⟩ : syracuseStep 7174241 = 5380681) B5380681
theorem B4782827 : Blo 1889435 4782827 := bstep (se 1 (by rfl) ⟨3587120, by rfl⟩ : syracuseStep 4782827 = 7174241) B7174241
theorem B3188551 : Blo 1889435 3188551 := bstep (se 1 (by rfl) ⟨2391413, by rfl⟩ : syracuseStep 3188551 = 4782827) B4782827
theorem B4251401 : Blo 1889435 4251401 := bstep (se 2 (by rfl) ⟨1594275, by rfl⟩ : syracuseStep 4251401 = 3188551) B3188551
theorem B2834267 : Blo 1889435 2834267 := bstep (se 1 (by rfl) ⟨2125700, by rfl⟩ : syracuseStep 2834267 = 4251401) B4251401
theorem B1889511 : Blo 1889435 1889511 := bstep (se 1 (by rfl) ⟨1417133, by rfl⟩ : syracuseStep 1889511 = 2834267) B2834267
theorem B2125705 : Blo 1889435 2125705 := bbase (se 2 (by rfl) ⟨797139, by rfl⟩ : syracuseStep 2125705 = 1594279) (by norm_num)
theorem B2834273 : Blo 1889435 2834273 := bstep (se 2 (by rfl) ⟨1062852, by rfl⟩ : syracuseStep 2834273 = 2125705) B2125705
theorem B1889515 : Blo 1889435 1889515 := bstep (se 1 (by rfl) ⟨1417136, by rfl⟩ : syracuseStep 1889515 = 2834273) B2834273
theorem B73630549 : Blo 1889435 73630549 := bbase (se 9 (by rfl) ⟨215714, by rfl⟩ : syracuseStep 73630549 = 431429) (by norm_num)
theorem B98174065 : Blo 1889435 98174065 := bstep (se 2 (by rfl) ⟨36815274, by rfl⟩ : syracuseStep 98174065 = 73630549) B73630549
theorem B130898753 : Blo 1889435 130898753 := bstep (se 2 (by rfl) ⟨49087032, by rfl⟩ : syracuseStep 130898753 = 98174065) B98174065
theorem B87265835 : Blo 1889435 87265835 := bstep (se 1 (by rfl) ⟨65449376, by rfl⟩ : syracuseStep 87265835 = 130898753) B130898753
theorem B58177223 : Blo 1889435 58177223 := bstep (se 1 (by rfl) ⟨43632917, by rfl⟩ : syracuseStep 58177223 = 87265835) B87265835
theorem B38784815 : Blo 1889435 38784815 := bstep (se 1 (by rfl) ⟨29088611, by rfl⟩ : syracuseStep 38784815 = 58177223) B58177223
theorem B25856543 : Blo 1889435 25856543 := bstep (se 1 (by rfl) ⟨19392407, by rfl⟩ : syracuseStep 25856543 = 38784815) B38784815
theorem B17237695 : Blo 1889435 17237695 := bstep (se 1 (by rfl) ⟨12928271, by rfl⟩ : syracuseStep 17237695 = 25856543) B25856543
theorem B22983593 : Blo 1889435 22983593 := bstep (se 2 (by rfl) ⟨8618847, by rfl⟩ : syracuseStep 22983593 = 17237695) B17237695
theorem B61289581 : Blo 1889435 61289581 := bstep (se 3 (by rfl) ⟨11491796, by rfl⟩ : syracuseStep 61289581 = 22983593) B22983593
theorem B81719441 : Blo 1889435 81719441 := bstep (se 2 (by rfl) ⟨30644790, by rfl⟩ : syracuseStep 81719441 = 61289581) B61289581
theorem B54479627 : Blo 1889435 54479627 := bstep (se 1 (by rfl) ⟨40859720, by rfl⟩ : syracuseStep 54479627 = 81719441) B81719441
theorem B36319751 : Blo 1889435 36319751 := bstep (se 1 (by rfl) ⟨27239813, by rfl⟩ : syracuseStep 36319751 = 54479627) B54479627
theorem B24213167 : Blo 1889435 24213167 := bstep (se 1 (by rfl) ⟨18159875, by rfl⟩ : syracuseStep 24213167 = 36319751) B36319751
theorem B16142111 : Blo 1889435 16142111 := bstep (se 1 (by rfl) ⟨12106583, by rfl⟩ : syracuseStep 16142111 = 24213167) B24213167
theorem B10761407 : Blo 1889435 10761407 := bstep (se 1 (by rfl) ⟨8071055, by rfl⟩ : syracuseStep 10761407 = 16142111) B16142111
theorem B7174271 : Blo 1889435 7174271 := bstep (se 1 (by rfl) ⟨5380703, by rfl⟩ : syracuseStep 7174271 = 10761407) B10761407
theorem B4782847 : Blo 1889435 4782847 := bstep (se 1 (by rfl) ⟨3587135, by rfl⟩ : syracuseStep 4782847 = 7174271) B7174271
theorem B6377129 : Blo 1889435 6377129 := bstep (se 2 (by rfl) ⟨2391423, by rfl⟩ : syracuseStep 6377129 = 4782847) B4782847
theorem B4251419 : Blo 1889435 4251419 := bstep (se 1 (by rfl) ⟨3188564, by rfl⟩ : syracuseStep 4251419 = 6377129) B6377129
theorem B2834279 : Blo 1889435 2834279 := bstep (se 1 (by rfl) ⟨2125709, by rfl⟩ : syracuseStep 2834279 = 4251419) B4251419
theorem B1889519 : Blo 1889435 1889519 := bstep (se 1 (by rfl) ⟨1417139, by rfl⟩ : syracuseStep 1889519 = 2834279) B2834279
theorem B2834285 : Blo 1889435 2834285 := bbase (se 3 (by rfl) ⟨531428, by rfl⟩ : syracuseStep 2834285 = 1062857) (by norm_num)
theorem B1889523 : Blo 1889435 1889523 := bstep (se 1 (by rfl) ⟨1417142, by rfl⟩ : syracuseStep 1889523 = 2834285) B2834285
theorem B4251437 : Blo 1889435 4251437 := bbase (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) (by norm_num)
theorem B2834291 : Blo 1889435 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B1889527 : Blo 1889435 1889527 := bstep (se 1 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 1889527 = 2834291) B2834291
theorem B8071109 : Blo 1889435 8071109 := bbase (se 4 (by rfl) ⟨756666, by rfl⟩ : syracuseStep 8071109 = 1513333) (by norm_num)
theorem B5380739 : Blo 1889435 5380739 := bstep (se 1 (by rfl) ⟨4035554, by rfl⟩ : syracuseStep 5380739 = 8071109) B8071109
theorem B3587159 : Blo 1889435 3587159 := bstep (se 1 (by rfl) ⟨2690369, by rfl⟩ : syracuseStep 3587159 = 5380739) B5380739
theorem B2391439 : Blo 1889435 2391439 := bstep (se 1 (by rfl) ⟨1793579, by rfl⟩ : syracuseStep 2391439 = 3587159) B3587159
theorem B3188585 : Blo 1889435 3188585 := bstep (se 2 (by rfl) ⟨1195719, by rfl⟩ : syracuseStep 3188585 = 2391439) B2391439
theorem B2125723 : Blo 1889435 2125723 := bstep (se 1 (by rfl) ⟨1594292, by rfl⟩ : syracuseStep 2125723 = 3188585) B3188585
theorem B2834297 : Blo 1889435 2834297 := bstep (se 2 (by rfl) ⟨1062861, by rfl⟩ : syracuseStep 2834297 = 2125723) B2125723
theorem B1889531 : Blo 1889435 1889531 := bstep (se 1 (by rfl) ⟨1417148, by rfl⟩ : syracuseStep 1889531 = 2834297) B2834297
theorem B8088005 : Blo 1889435 8088005 := bbase (se 4 (by rfl) ⟨758250, by rfl⟩ : syracuseStep 8088005 = 1516501) (by norm_num)
theorem B5392003 : Blo 1889435 5392003 := bstep (se 1 (by rfl) ⟨4044002, by rfl⟩ : syracuseStep 5392003 = 8088005) B8088005
theorem B7189337 : Blo 1889435 7189337 := bstep (se 2 (by rfl) ⟨2696001, by rfl⟩ : syracuseStep 7189337 = 5392003) B5392003
theorem B4792891 : Blo 1889435 4792891 := bstep (se 1 (by rfl) ⟨3594668, by rfl⟩ : syracuseStep 4792891 = 7189337) B7189337
theorem B6390521 : Blo 1889435 6390521 := bstep (se 2 (by rfl) ⟨2396445, by rfl⟩ : syracuseStep 6390521 = 4792891) B4792891
theorem B4260347 : Blo 1889435 4260347 := bstep (se 1 (by rfl) ⟨3195260, by rfl⟩ : syracuseStep 4260347 = 6390521) B6390521
theorem B2840231 : Blo 1889435 2840231 := bstep (se 1 (by rfl) ⟨2130173, by rfl⟩ : syracuseStep 2840231 = 4260347) B4260347
theorem B7573949 : Blo 1889435 7573949 := bstep (se 3 (by rfl) ⟨1420115, by rfl⟩ : syracuseStep 7573949 = 2840231) B2840231
theorem B5049299 : Blo 1889435 5049299 := bstep (se 1 (by rfl) ⟨3786974, by rfl⟩ : syracuseStep 5049299 = 7573949) B7573949
theorem B13464797 : Blo 1889435 13464797 := bstep (se 3 (by rfl) ⟨2524649, by rfl⟩ : syracuseStep 13464797 = 5049299) B5049299
theorem B35906125 : Blo 1889435 35906125 := bstep (se 3 (by rfl) ⟨6732398, by rfl⟩ : syracuseStep 35906125 = 13464797) B13464797
theorem B47874833 : Blo 1889435 47874833 := bstep (se 2 (by rfl) ⟨17953062, by rfl⟩ : syracuseStep 47874833 = 35906125) B35906125
theorem B31916555 : Blo 1889435 31916555 := bstep (se 1 (by rfl) ⟨23937416, by rfl⟩ : syracuseStep 31916555 = 47874833) B47874833
theorem B21277703 : Blo 1889435 21277703 := bstep (se 1 (by rfl) ⟨15958277, by rfl⟩ : syracuseStep 21277703 = 31916555) B31916555
theorem B14185135 : Blo 1889435 14185135 := bstep (se 1 (by rfl) ⟨10638851, by rfl⟩ : syracuseStep 14185135 = 21277703) B21277703
theorem B18913513 : Blo 1889435 18913513 := bstep (se 2 (by rfl) ⟨7092567, by rfl⟩ : syracuseStep 18913513 = 14185135) B14185135
theorem B25218017 : Blo 1889435 25218017 := bstep (se 2 (by rfl) ⟨9456756, by rfl⟩ : syracuseStep 25218017 = 18913513) B18913513
theorem B16812011 : Blo 1889435 16812011 := bstep (se 1 (by rfl) ⟨12609008, by rfl⟩ : syracuseStep 16812011 = 25218017) B25218017
theorem B11208007 : Blo 1889435 11208007 := bstep (se 1 (by rfl) ⟨8406005, by rfl⟩ : syracuseStep 11208007 = 16812011) B16812011
theorem B14944009 : Blo 1889435 14944009 := bstep (se 2 (by rfl) ⟨5604003, by rfl⟩ : syracuseStep 14944009 = 11208007) B11208007
theorem B19925345 : Blo 1889435 19925345 := bstep (se 2 (by rfl) ⟨7472004, by rfl⟩ : syracuseStep 19925345 = 14944009) B14944009
theorem B13283563 : Blo 1889435 13283563 := bstep (se 1 (by rfl) ⟨9962672, by rfl⟩ : syracuseStep 13283563 = 19925345) B19925345
theorem B17711417 : Blo 1889435 17711417 := bstep (se 2 (by rfl) ⟨6641781, by rfl⟩ : syracuseStep 17711417 = 13283563) B13283563
theorem B47230445 : Blo 1889435 47230445 := bstep (se 3 (by rfl) ⟨8855708, by rfl⟩ : syracuseStep 47230445 = 17711417) B17711417
theorem B31486963 : Blo 1889435 31486963 := bstep (se 1 (by rfl) ⟨23615222, by rfl⟩ : syracuseStep 31486963 = 47230445) B47230445
theorem B41982617 : Blo 1889435 41982617 := bstep (se 2 (by rfl) ⟨15743481, by rfl⟩ : syracuseStep 41982617 = 31486963) B31486963
theorem B27988411 : Blo 1889435 27988411 := bstep (se 1 (by rfl) ⟨20991308, by rfl⟩ : syracuseStep 27988411 = 41982617) B41982617
theorem B37317881 : Blo 1889435 37317881 := bstep (se 2 (by rfl) ⟨13994205, by rfl⟩ : syracuseStep 37317881 = 27988411) B27988411
theorem B24878587 : Blo 1889435 24878587 := bstep (se 1 (by rfl) ⟨18658940, by rfl⟩ : syracuseStep 24878587 = 37317881) B37317881
theorem B33171449 : Blo 1889435 33171449 := bstep (se 2 (by rfl) ⟨12439293, by rfl⟩ : syracuseStep 33171449 = 24878587) B24878587
theorem B88457197 : Blo 1889435 88457197 := bstep (se 3 (by rfl) ⟨16585724, by rfl⟩ : syracuseStep 88457197 = 33171449) B33171449
theorem B117942929 : Blo 1889435 117942929 := bstep (se 2 (by rfl) ⟨44228598, by rfl⟩ : syracuseStep 117942929 = 88457197) B88457197
theorem B78628619 : Blo 1889435 78628619 := bstep (se 1 (by rfl) ⟨58971464, by rfl⟩ : syracuseStep 78628619 = 117942929) B117942929
theorem B52419079 : Blo 1889435 52419079 := bstep (se 1 (by rfl) ⟨39314309, by rfl⟩ : syracuseStep 52419079 = 78628619) B78628619
theorem B69892105 : Blo 1889435 69892105 := bstep (se 2 (by rfl) ⟨26209539, by rfl⟩ : syracuseStep 69892105 = 52419079) B52419079
theorem B93189473 : Blo 1889435 93189473 := bstep (se 2 (by rfl) ⟨34946052, by rfl⟩ : syracuseStep 93189473 = 69892105) B69892105
theorem B62126315 : Blo 1889435 62126315 := bstep (se 1 (by rfl) ⟨46594736, by rfl⟩ : syracuseStep 62126315 = 93189473) B93189473
theorem B41417543 : Blo 1889435 41417543 := bstep (se 1 (by rfl) ⟨31063157, by rfl⟩ : syracuseStep 41417543 = 62126315) B62126315
theorem B27611695 : Blo 1889435 27611695 := bstep (se 1 (by rfl) ⟨20708771, by rfl⟩ : syracuseStep 27611695 = 41417543) B41417543
theorem B36815593 : Blo 1889435 36815593 := bstep (se 2 (by rfl) ⟨13805847, by rfl⟩ : syracuseStep 36815593 = 27611695) B27611695
theorem B49087457 : Blo 1889435 49087457 := bstep (se 2 (by rfl) ⟨18407796, by rfl⟩ : syracuseStep 49087457 = 36815593) B36815593
theorem B32724971 : Blo 1889435 32724971 := bstep (se 1 (by rfl) ⟨24543728, by rfl⟩ : syracuseStep 32724971 = 49087457) B49087457
theorem B21816647 : Blo 1889435 21816647 := bstep (se 1 (by rfl) ⟨16362485, by rfl⟩ : syracuseStep 21816647 = 32724971) B32724971
theorem B14544431 : Blo 1889435 14544431 := bstep (se 1 (by rfl) ⟨10908323, by rfl⟩ : syracuseStep 14544431 = 21816647) B21816647
theorem B9696287 : Blo 1889435 9696287 := bstep (se 1 (by rfl) ⟨7272215, by rfl⟩ : syracuseStep 9696287 = 14544431) B14544431
theorem B25856765 : Blo 1889435 25856765 := bstep (se 3 (by rfl) ⟨4848143, by rfl⟩ : syracuseStep 25856765 = 9696287) B9696287
theorem B17237843 : Blo 1889435 17237843 := bstep (se 1 (by rfl) ⟨12928382, by rfl⟩ : syracuseStep 17237843 = 25856765) B25856765
theorem B11491895 : Blo 1889435 11491895 := bstep (se 1 (by rfl) ⟨8618921, by rfl⟩ : syracuseStep 11491895 = 17237843) B17237843
theorem B7661263 : Blo 1889435 7661263 := bstep (se 1 (by rfl) ⟨5745947, by rfl⟩ : syracuseStep 7661263 = 11491895) B11491895
theorem B10215017 : Blo 1889435 10215017 := bstep (se 2 (by rfl) ⟨3830631, by rfl⟩ : syracuseStep 10215017 = 7661263) B7661263
theorem B6810011 : Blo 1889435 6810011 := bstep (se 1 (by rfl) ⟨5107508, by rfl⟩ : syracuseStep 6810011 = 10215017) B10215017
theorem B4540007 : Blo 1889435 4540007 := bstep (se 1 (by rfl) ⟨3405005, by rfl⟩ : syracuseStep 4540007 = 6810011) B6810011
theorem B12106685 : Blo 1889435 12106685 := bstep (se 3 (by rfl) ⟨2270003, by rfl⟩ : syracuseStep 12106685 = 4540007) B4540007
theorem B32284493 : Blo 1889435 32284493 := bstep (se 3 (by rfl) ⟨6053342, by rfl⟩ : syracuseStep 32284493 = 12106685) B12106685
theorem B21522995 : Blo 1889435 21522995 := bstep (se 1 (by rfl) ⟨16142246, by rfl⟩ : syracuseStep 21522995 = 32284493) B32284493
theorem B14348663 : Blo 1889435 14348663 := bstep (se 1 (by rfl) ⟨10761497, by rfl⟩ : syracuseStep 14348663 = 21522995) B21522995
theorem B9565775 : Blo 1889435 9565775 := bstep (se 1 (by rfl) ⟨7174331, by rfl⟩ : syracuseStep 9565775 = 14348663) B14348663
theorem B6377183 : Blo 1889435 6377183 := bstep (se 1 (by rfl) ⟨4782887, by rfl⟩ : syracuseStep 6377183 = 9565775) B9565775
theorem B4251455 : Blo 1889435 4251455 := bstep (se 1 (by rfl) ⟨3188591, by rfl⟩ : syracuseStep 4251455 = 6377183) B6377183
theorem B2834303 : Blo 1889435 2834303 := bstep (se 1 (by rfl) ⟨2125727, by rfl⟩ : syracuseStep 2834303 = 4251455) B4251455
theorem B1889535 : Blo 1889435 1889535 := bstep (se 1 (by rfl) ⟨1417151, by rfl⟩ : syracuseStep 1889535 = 2834303) B2834303
theorem B2834309 : Blo 1889435 2834309 := bbase (se 4 (by rfl) ⟨265716, by rfl⟩ : syracuseStep 2834309 = 531433) (by norm_num)
theorem B1889539 : Blo 1889435 1889539 := bstep (se 1 (by rfl) ⟨1417154, by rfl⟩ : syracuseStep 1889539 = 2834309) B2834309
theorem B3188605 : Blo 1889435 3188605 := bbase (se 3 (by rfl) ⟨597863, by rfl⟩ : syracuseStep 3188605 = 1195727) (by norm_num)
theorem B4251473 : Blo 1889435 4251473 := bstep (se 2 (by rfl) ⟨1594302, by rfl⟩ : syracuseStep 4251473 = 3188605) B3188605
theorem B2834315 : Blo 1889435 2834315 := bstep (se 1 (by rfl) ⟨2125736, by rfl⟩ : syracuseStep 2834315 = 4251473) B4251473
theorem B1889543 : Blo 1889435 1889543 := bstep (se 1 (by rfl) ⟨1417157, by rfl⟩ : syracuseStep 1889543 = 2834315) B2834315
theorem B2125741 : Blo 1889435 2125741 := bbase (se 3 (by rfl) ⟨398576, by rfl⟩ : syracuseStep 2125741 = 797153) (by norm_num)
theorem B2834321 : Blo 1889435 2834321 := bstep (se 2 (by rfl) ⟨1062870, by rfl⟩ : syracuseStep 2834321 = 2125741) B2125741
theorem B1889547 : Blo 1889435 1889547 := bstep (se 1 (by rfl) ⟨1417160, by rfl⟩ : syracuseStep 1889547 = 2834321) B2834321
theorem B6377237 : Blo 1889435 6377237 := bbase (se 6 (by rfl) ⟨149466, by rfl⟩ : syracuseStep 6377237 = 298933) (by norm_num)
theorem B4251491 : Blo 1889435 4251491 := bstep (se 1 (by rfl) ⟨3188618, by rfl⟩ : syracuseStep 4251491 = 6377237) B6377237
theorem B2834327 : Blo 1889435 2834327 := bstep (se 1 (by rfl) ⟨2125745, by rfl⟩ : syracuseStep 2834327 = 4251491) B4251491
theorem B1889551 : Blo 1889435 1889551 := bstep (se 1 (by rfl) ⟨1417163, by rfl⟩ : syracuseStep 1889551 = 2834327) B2834327
theorem B2834333 : Blo 1889435 2834333 := bbase (se 3 (by rfl) ⟨531437, by rfl⟩ : syracuseStep 2834333 = 1062875) (by norm_num)
theorem B1889555 : Blo 1889435 1889555 := bstep (se 1 (by rfl) ⟨1417166, by rfl⟩ : syracuseStep 1889555 = 2834333) B2834333
theorem B4251509 : Blo 1889435 4251509 := bbase (se 5 (by rfl) ⟨199289, by rfl⟩ : syracuseStep 4251509 = 398579) (by norm_num)
theorem B2834339 : Blo 1889435 2834339 := bstep (se 1 (by rfl) ⟨2125754, by rfl⟩ : syracuseStep 2834339 = 4251509) B4251509
theorem B1889559 : Blo 1889435 1889559 := bstep (se 1 (by rfl) ⟨1417169, by rfl⟩ : syracuseStep 1889559 = 2834339) B2834339
theorem B2424109 : Blo 1889435 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B3232145 : Blo 1889435 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B2154763 : Blo 1889435 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B2873017 : Blo 1889435 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B3830689 : Blo 1889435 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B5107585 : Blo 1889435 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B6810113 : Blo 1889435 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B18160301 : Blo 1889435 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B12106867 : Blo 1889435 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B16142489 : Blo 1889435 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B10761659 : Blo 1889435 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B7174439 : Blo 1889435 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B4782959 : Blo 1889435 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B3188639 : Blo 1889435 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B2125759 : Blo 1889435 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B2834345 : Blo 1889435 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1889563 : Blo 1889435 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B7174453 : Blo 1889435 7174453 := bbase (se 5 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 7174453 = 672605) (by norm_num)
theorem B9565937 : Blo 1889435 9565937 := bstep (se 2 (by rfl) ⟨3587226, by rfl⟩ : syracuseStep 9565937 = 7174453) B7174453
theorem B6377291 : Blo 1889435 6377291 := bstep (se 1 (by rfl) ⟨4782968, by rfl⟩ : syracuseStep 6377291 = 9565937) B9565937
theorem B4251527 : Blo 1889435 4251527 := bstep (se 1 (by rfl) ⟨3188645, by rfl⟩ : syracuseStep 4251527 = 6377291) B6377291
theorem B2834351 : Blo 1889435 2834351 := bstep (se 1 (by rfl) ⟨2125763, by rfl⟩ : syracuseStep 2834351 = 4251527) B4251527
theorem B1889567 : Blo 1889435 1889567 := bstep (se 1 (by rfl) ⟨1417175, by rfl⟩ : syracuseStep 1889567 = 2834351) B2834351
theorem B2834357 : Blo 1889435 2834357 := bbase (se 5 (by rfl) ⟨132860, by rfl⟩ : syracuseStep 2834357 = 265721) (by norm_num)
theorem B1889571 : Blo 1889435 1889571 := bstep (se 1 (by rfl) ⟨1417178, by rfl⟩ : syracuseStep 1889571 = 2834357) B2834357
theorem B4782989 : Blo 1889435 4782989 := bbase (se 3 (by rfl) ⟨896810, by rfl⟩ : syracuseStep 4782989 = 1793621) (by norm_num)
theorem B3188659 : Blo 1889435 3188659 := bstep (se 1 (by rfl) ⟨2391494, by rfl⟩ : syracuseStep 3188659 = 4782989) B4782989
theorem B4251545 : Blo 1889435 4251545 := bstep (se 2 (by rfl) ⟨1594329, by rfl⟩ : syracuseStep 4251545 = 3188659) B3188659
theorem B2834363 : Blo 1889435 2834363 := bstep (se 1 (by rfl) ⟨2125772, by rfl⟩ : syracuseStep 2834363 = 4251545) B4251545
theorem B1889575 : Blo 1889435 1889575 := bstep (se 1 (by rfl) ⟨1417181, by rfl⟩ : syracuseStep 1889575 = 2834363) B2834363
theorem B2125777 : Blo 1889435 2125777 := bbase (se 2 (by rfl) ⟨797166, by rfl⟩ : syracuseStep 2125777 = 1594333) (by norm_num)
theorem B2834369 : Blo 1889435 2834369 := bstep (se 2 (by rfl) ⟨1062888, by rfl⟩ : syracuseStep 2834369 = 2125777) B2125777
theorem B1889579 : Blo 1889435 1889579 := bstep (se 1 (by rfl) ⟨1417184, by rfl⟩ : syracuseStep 1889579 = 2834369) B2834369
theorem B3026749 : Blo 1889435 3026749 := bbase (se 3 (by rfl) ⟨567515, by rfl⟩ : syracuseStep 3026749 = 1135031) (by norm_num)
theorem B4035665 : Blo 1889435 4035665 := bstep (se 2 (by rfl) ⟨1513374, by rfl⟩ : syracuseStep 4035665 = 3026749) B3026749
theorem B2690443 : Blo 1889435 2690443 := bstep (se 1 (by rfl) ⟨2017832, by rfl⟩ : syracuseStep 2690443 = 4035665) B4035665
theorem B3587257 : Blo 1889435 3587257 := bstep (se 2 (by rfl) ⟨1345221, by rfl⟩ : syracuseStep 3587257 = 2690443) B2690443
theorem B4783009 : Blo 1889435 4783009 := bstep (se 2 (by rfl) ⟨1793628, by rfl⟩ : syracuseStep 4783009 = 3587257) B3587257
theorem B6377345 : Blo 1889435 6377345 := bstep (se 2 (by rfl) ⟨2391504, by rfl⟩ : syracuseStep 6377345 = 4783009) B4783009
theorem B4251563 : Blo 1889435 4251563 := bstep (se 1 (by rfl) ⟨3188672, by rfl⟩ : syracuseStep 4251563 = 6377345) B6377345
theorem B2834375 : Blo 1889435 2834375 := bstep (se 1 (by rfl) ⟨2125781, by rfl⟩ : syracuseStep 2834375 = 4251563) B4251563
theorem B1889583 : Blo 1889435 1889583 := bstep (se 1 (by rfl) ⟨1417187, by rfl⟩ : syracuseStep 1889583 = 2834375) B2834375
theorem B2834381 : Blo 1889435 2834381 := bbase (se 3 (by rfl) ⟨531446, by rfl⟩ : syracuseStep 2834381 = 1062893) (by norm_num)
theorem B1889587 : Blo 1889435 1889587 := bstep (se 1 (by rfl) ⟨1417190, by rfl⟩ : syracuseStep 1889587 = 2834381) B2834381
theorem B4251581 : Blo 1889435 4251581 := bbase (se 3 (by rfl) ⟨797171, by rfl⟩ : syracuseStep 4251581 = 1594343) (by norm_num)
theorem B2834387 : Blo 1889435 2834387 := bstep (se 1 (by rfl) ⟨2125790, by rfl⟩ : syracuseStep 2834387 = 4251581) B4251581
theorem B1889591 : Blo 1889435 1889591 := bstep (se 1 (by rfl) ⟨1417193, by rfl⟩ : syracuseStep 1889591 = 2834387) B2834387
theorem B3188693 : Blo 1889435 3188693 := bbase (se 7 (by rfl) ⟨37367, by rfl⟩ : syracuseStep 3188693 = 74735) (by norm_num)
theorem B2125795 : Blo 1889435 2125795 := bstep (se 1 (by rfl) ⟨1594346, by rfl⟩ : syracuseStep 2125795 = 3188693) B3188693
theorem B2834393 : Blo 1889435 2834393 := bstep (se 2 (by rfl) ⟨1062897, by rfl⟩ : syracuseStep 2834393 = 2125795) B2125795
theorem B1889595 : Blo 1889435 1889595 := bstep (se 1 (by rfl) ⟨1417196, by rfl⟩ : syracuseStep 1889595 = 2834393) B2834393
theorem B8071397 : Blo 1889435 8071397 := bbase (se 4 (by rfl) ⟨756693, by rfl⟩ : syracuseStep 8071397 = 1513387) (by norm_num)
theorem B5380931 : Blo 1889435 5380931 := bstep (se 1 (by rfl) ⟨4035698, by rfl⟩ : syracuseStep 5380931 = 8071397) B8071397
theorem B14349149 : Blo 1889435 14349149 := bstep (se 3 (by rfl) ⟨2690465, by rfl⟩ : syracuseStep 14349149 = 5380931) B5380931
theorem B9566099 : Blo 1889435 9566099 := bstep (se 1 (by rfl) ⟨7174574, by rfl⟩ : syracuseStep 9566099 = 14349149) B14349149
theorem B6377399 : Blo 1889435 6377399 := bstep (se 1 (by rfl) ⟨4783049, by rfl⟩ : syracuseStep 6377399 = 9566099) B9566099
theorem B4251599 : Blo 1889435 4251599 := bstep (se 1 (by rfl) ⟨3188699, by rfl⟩ : syracuseStep 4251599 = 6377399) B6377399
theorem B2834399 : Blo 1889435 2834399 := bstep (se 1 (by rfl) ⟨2125799, by rfl⟩ : syracuseStep 2834399 = 4251599) B4251599
theorem B1889599 : Blo 1889435 1889599 := bstep (se 1 (by rfl) ⟨1417199, by rfl⟩ : syracuseStep 1889599 = 2834399) B2834399
theorem B2834405 : Blo 1889435 2834405 := bbase (se 4 (by rfl) ⟨265725, by rfl⟩ : syracuseStep 2834405 = 531451) (by norm_num)
theorem B1889603 : Blo 1889435 1889603 := bstep (se 1 (by rfl) ⟨1417202, by rfl⟩ : syracuseStep 1889603 = 2834405) B2834405
theorem B7661557 : Blo 1889435 7661557 := bbase (se 5 (by rfl) ⟨359135, by rfl⟩ : syracuseStep 7661557 = 718271) (by norm_num)
theorem B10215409 : Blo 1889435 10215409 := bstep (se 2 (by rfl) ⟨3830778, by rfl⟩ : syracuseStep 10215409 = 7661557) B7661557
theorem B13620545 : Blo 1889435 13620545 := bstep (se 2 (by rfl) ⟨5107704, by rfl⟩ : syracuseStep 13620545 = 10215409) B10215409
theorem B9080363 : Blo 1889435 9080363 := bstep (se 1 (by rfl) ⟨6810272, by rfl⟩ : syracuseStep 9080363 = 13620545) B13620545
theorem B6053575 : Blo 1889435 6053575 := bstep (se 1 (by rfl) ⟨4540181, by rfl⟩ : syracuseStep 6053575 = 9080363) B9080363
theorem B8071433 : Blo 1889435 8071433 := bstep (se 2 (by rfl) ⟨3026787, by rfl⟩ : syracuseStep 8071433 = 6053575) B6053575
theorem B5380955 : Blo 1889435 5380955 := bstep (se 1 (by rfl) ⟨4035716, by rfl⟩ : syracuseStep 5380955 = 8071433) B8071433
theorem B3587303 : Blo 1889435 3587303 := bstep (se 1 (by rfl) ⟨2690477, by rfl⟩ : syracuseStep 3587303 = 5380955) B5380955
theorem B2391535 : Blo 1889435 2391535 := bstep (se 1 (by rfl) ⟨1793651, by rfl⟩ : syracuseStep 2391535 = 3587303) B3587303
theorem B3188713 : Blo 1889435 3188713 := bstep (se 2 (by rfl) ⟨1195767, by rfl⟩ : syracuseStep 3188713 = 2391535) B2391535
theorem B4251617 : Blo 1889435 4251617 := bstep (se 2 (by rfl) ⟨1594356, by rfl⟩ : syracuseStep 4251617 = 3188713) B3188713
theorem B2834411 : Blo 1889435 2834411 := bstep (se 1 (by rfl) ⟨2125808, by rfl⟩ : syracuseStep 2834411 = 4251617) B4251617
theorem B1889607 : Blo 1889435 1889607 := bstep (se 1 (by rfl) ⟨1417205, by rfl⟩ : syracuseStep 1889607 = 2834411) B2834411
theorem B2125813 : Blo 1889435 2125813 := bbase (se 5 (by rfl) ⟨99647, by rfl⟩ : syracuseStep 2125813 = 199295) (by norm_num)
theorem B2834417 : Blo 1889435 2834417 := bstep (se 2 (by rfl) ⟨1062906, by rfl⟩ : syracuseStep 2834417 = 2125813) B2125813
theorem B1889611 : Blo 1889435 1889611 := bstep (se 1 (by rfl) ⟨1417208, by rfl⟩ : syracuseStep 1889611 = 2834417) B2834417
theorem B2391545 : Blo 1889435 2391545 := bbase (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) (by norm_num)
theorem B6377453 : Blo 1889435 6377453 := bstep (se 3 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 6377453 = 2391545) B2391545
theorem B4251635 : Blo 1889435 4251635 := bstep (se 1 (by rfl) ⟨3188726, by rfl⟩ : syracuseStep 4251635 = 6377453) B6377453
theorem B2834423 : Blo 1889435 2834423 := bstep (se 1 (by rfl) ⟨2125817, by rfl⟩ : syracuseStep 2834423 = 4251635) B4251635
theorem B1889615 : Blo 1889435 1889615 := bstep (se 1 (by rfl) ⟨1417211, by rfl⟩ : syracuseStep 1889615 = 2834423) B2834423
theorem B2834429 : Blo 1889435 2834429 := bbase (se 3 (by rfl) ⟨531455, by rfl⟩ : syracuseStep 2834429 = 1062911) (by norm_num)
theorem B1889619 : Blo 1889435 1889619 := bstep (se 1 (by rfl) ⟨1417214, by rfl⟩ : syracuseStep 1889619 = 2834429) B2834429
theorem B4251653 : Blo 1889435 4251653 := bbase (se 4 (by rfl) ⟨398592, by rfl⟩ : syracuseStep 4251653 = 797185) (by norm_num)
theorem B2834435 : Blo 1889435 2834435 := bstep (se 1 (by rfl) ⟨2125826, by rfl⟩ : syracuseStep 2834435 = 4251653) B4251653
theorem B1889623 : Blo 1889435 1889623 := bstep (se 1 (by rfl) ⟨1417217, by rfl⟩ : syracuseStep 1889623 = 2834435) B2834435
theorem B3587341 : Blo 1889435 3587341 := bbase (se 3 (by rfl) ⟨672626, by rfl⟩ : syracuseStep 3587341 = 1345253) (by norm_num)
theorem B4783121 : Blo 1889435 4783121 := bstep (se 2 (by rfl) ⟨1793670, by rfl⟩ : syracuseStep 4783121 = 3587341) B3587341
theorem B3188747 : Blo 1889435 3188747 := bstep (se 1 (by rfl) ⟨2391560, by rfl⟩ : syracuseStep 3188747 = 4783121) B4783121
theorem B2125831 : Blo 1889435 2125831 := bstep (se 1 (by rfl) ⟨1594373, by rfl⟩ : syracuseStep 2125831 = 3188747) B3188747
theorem B2834441 : Blo 1889435 2834441 := bstep (se 2 (by rfl) ⟨1062915, by rfl⟩ : syracuseStep 2834441 = 2125831) B2125831
theorem B1889627 : Blo 1889435 1889627 := bstep (se 1 (by rfl) ⟨1417220, by rfl⟩ : syracuseStep 1889627 = 2834441) B2834441
theorem B9566261 : Blo 1889435 9566261 := bbase (se 5 (by rfl) ⟨448418, by rfl⟩ : syracuseStep 9566261 = 896837) (by norm_num)
theorem B6377507 : Blo 1889435 6377507 := bstep (se 1 (by rfl) ⟨4783130, by rfl⟩ : syracuseStep 6377507 = 9566261) B9566261
theorem B4251671 : Blo 1889435 4251671 := bstep (se 1 (by rfl) ⟨3188753, by rfl⟩ : syracuseStep 4251671 = 6377507) B6377507
theorem B2834447 : Blo 1889435 2834447 := bstep (se 1 (by rfl) ⟨2125835, by rfl⟩ : syracuseStep 2834447 = 4251671) B4251671
theorem B1889631 : Blo 1889435 1889631 := bstep (se 1 (by rfl) ⟨1417223, by rfl⟩ : syracuseStep 1889631 = 2834447) B2834447
theorem B2834453 : Blo 1889435 2834453 := bbase (se 6 (by rfl) ⟨66432, by rfl⟩ : syracuseStep 2834453 = 132865) (by norm_num)
theorem B1889635 : Blo 1889435 1889635 := bstep (se 1 (by rfl) ⟨1417226, by rfl⟩ : syracuseStep 1889635 = 2834453) B2834453
theorem B6464549 : Blo 1889435 6464549 := bbase (se 4 (by rfl) ⟨606051, by rfl⟩ : syracuseStep 6464549 = 1212103) (by norm_num)
theorem B4309699 : Blo 1889435 4309699 := bstep (se 1 (by rfl) ⟨3232274, by rfl⟩ : syracuseStep 4309699 = 6464549) B6464549
theorem B5746265 : Blo 1889435 5746265 := bstep (se 2 (by rfl) ⟨2154849, by rfl⟩ : syracuseStep 5746265 = 4309699) B4309699
theorem B3830843 : Blo 1889435 3830843 := bstep (se 1 (by rfl) ⟨2873132, by rfl⟩ : syracuseStep 3830843 = 5746265) B5746265
theorem B2553895 : Blo 1889435 2553895 := bstep (se 1 (by rfl) ⟨1915421, by rfl⟩ : syracuseStep 2553895 = 3830843) B3830843
theorem B13620773 : Blo 1889435 13620773 := bstep (se 4 (by rfl) ⟨1276947, by rfl⟩ : syracuseStep 13620773 = 2553895) B2553895
theorem B9080515 : Blo 1889435 9080515 := bstep (se 1 (by rfl) ⟨6810386, by rfl⟩ : syracuseStep 9080515 = 13620773) B13620773
theorem B12107353 : Blo 1889435 12107353 := bstep (se 2 (by rfl) ⟨4540257, by rfl⟩ : syracuseStep 12107353 = 9080515) B9080515
theorem B16143137 : Blo 1889435 16143137 := bstep (se 2 (by rfl) ⟨6053676, by rfl⟩ : syracuseStep 16143137 = 12107353) B12107353
theorem B10762091 : Blo 1889435 10762091 := bstep (se 1 (by rfl) ⟨8071568, by rfl⟩ : syracuseStep 10762091 = 16143137) B16143137
theorem B7174727 : Blo 1889435 7174727 := bstep (se 1 (by rfl) ⟨5381045, by rfl⟩ : syracuseStep 7174727 = 10762091) B10762091
theorem B4783151 : Blo 1889435 4783151 := bstep (se 1 (by rfl) ⟨3587363, by rfl⟩ : syracuseStep 4783151 = 7174727) B7174727
theorem B3188767 : Blo 1889435 3188767 := bstep (se 1 (by rfl) ⟨2391575, by rfl⟩ : syracuseStep 3188767 = 4783151) B4783151
theorem B4251689 : Blo 1889435 4251689 := bstep (se 2 (by rfl) ⟨1594383, by rfl⟩ : syracuseStep 4251689 = 3188767) B3188767
theorem B2834459 : Blo 1889435 2834459 := bstep (se 1 (by rfl) ⟨2125844, by rfl⟩ : syracuseStep 2834459 = 4251689) B4251689
theorem B1889639 : Blo 1889435 1889639 := bstep (se 1 (by rfl) ⟨1417229, by rfl⟩ : syracuseStep 1889639 = 2834459) B2834459
theorem B2125849 : Blo 1889435 2125849 := bbase (se 2 (by rfl) ⟨797193, by rfl⟩ : syracuseStep 2125849 = 1594387) (by norm_num)
theorem B2834465 : Blo 1889435 2834465 := bstep (se 2 (by rfl) ⟨1062924, by rfl⟩ : syracuseStep 2834465 = 2125849) B2125849
theorem B1889643 : Blo 1889435 1889643 := bstep (se 1 (by rfl) ⟨1417232, by rfl⟩ : syracuseStep 1889643 = 2834465) B2834465
theorem B7174757 : Blo 1889435 7174757 := bbase (se 4 (by rfl) ⟨672633, by rfl⟩ : syracuseStep 7174757 = 1345267) (by norm_num)
theorem B4783171 : Blo 1889435 4783171 := bstep (se 1 (by rfl) ⟨3587378, by rfl⟩ : syracuseStep 4783171 = 7174757) B7174757
theorem B6377561 : Blo 1889435 6377561 := bstep (se 2 (by rfl) ⟨2391585, by rfl⟩ : syracuseStep 6377561 = 4783171) B4783171
theorem B4251707 : Blo 1889435 4251707 := bstep (se 1 (by rfl) ⟨3188780, by rfl⟩ : syracuseStep 4251707 = 6377561) B6377561
theorem B2834471 : Blo 1889435 2834471 := bstep (se 1 (by rfl) ⟨2125853, by rfl⟩ : syracuseStep 2834471 = 4251707) B4251707
theorem B1889647 : Blo 1889435 1889647 := bstep (se 1 (by rfl) ⟨1417235, by rfl⟩ : syracuseStep 1889647 = 2834471) B2834471
theorem B2834477 : Blo 1889435 2834477 := bbase (se 3 (by rfl) ⟨531464, by rfl⟩ : syracuseStep 2834477 = 1062929) (by norm_num)
theorem B1889651 : Blo 1889435 1889651 := bstep (se 1 (by rfl) ⟨1417238, by rfl⟩ : syracuseStep 1889651 = 2834477) B2834477
theorem B4251725 : Blo 1889435 4251725 := bbase (se 3 (by rfl) ⟨797198, by rfl⟩ : syracuseStep 4251725 = 1594397) (by norm_num)
theorem B2834483 : Blo 1889435 2834483 := bstep (se 1 (by rfl) ⟨2125862, by rfl⟩ : syracuseStep 2834483 = 4251725) B4251725
theorem B1889655 : Blo 1889435 1889655 := bstep (se 1 (by rfl) ⟨1417241, by rfl⟩ : syracuseStep 1889655 = 2834483) B2834483
theorem B2391601 : Blo 1889435 2391601 := bbase (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) (by norm_num)
theorem B3188801 : Blo 1889435 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B2125867 : Blo 1889435 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B2834489 : Blo 1889435 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B1889659 : Blo 1889435 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B5454533 : Blo 1889435 5454533 := bbase (se 4 (by rfl) ⟨511362, by rfl⟩ : syracuseStep 5454533 = 1022725) (by norm_num)
theorem B3636355 : Blo 1889435 3636355 := bstep (se 1 (by rfl) ⟨2727266, by rfl⟩ : syracuseStep 3636355 = 5454533) B5454533
theorem B4848473 : Blo 1889435 4848473 := bstep (se 2 (by rfl) ⟨1818177, by rfl⟩ : syracuseStep 4848473 = 3636355) B3636355
theorem B3232315 : Blo 1889435 3232315 := bstep (se 1 (by rfl) ⟨2424236, by rfl⟩ : syracuseStep 3232315 = 4848473) B4848473
theorem B17239013 : Blo 1889435 17239013 := bstep (se 4 (by rfl) ⟨1616157, by rfl⟩ : syracuseStep 17239013 = 3232315) B3232315
theorem B11492675 : Blo 1889435 11492675 := bstep (se 1 (by rfl) ⟨8619506, by rfl⟩ : syracuseStep 11492675 = 17239013) B17239013
theorem B7661783 : Blo 1889435 7661783 := bstep (se 1 (by rfl) ⟨5746337, by rfl⟩ : syracuseStep 7661783 = 11492675) B11492675
theorem B5107855 : Blo 1889435 5107855 := bstep (se 1 (by rfl) ⟨3830891, by rfl⟩ : syracuseStep 5107855 = 7661783) B7661783
theorem B6810473 : Blo 1889435 6810473 := bstep (se 2 (by rfl) ⟨2553927, by rfl⟩ : syracuseStep 6810473 = 5107855) B5107855
theorem B4540315 : Blo 1889435 4540315 := bstep (se 1 (by rfl) ⟨3405236, by rfl⟩ : syracuseStep 4540315 = 6810473) B6810473
theorem B6053753 : Blo 1889435 6053753 := bstep (se 2 (by rfl) ⟨2270157, by rfl⟩ : syracuseStep 6053753 = 4540315) B4540315
theorem B4035835 : Blo 1889435 4035835 := bstep (se 1 (by rfl) ⟨3026876, by rfl⟩ : syracuseStep 4035835 = 6053753) B6053753
theorem B21524453 : Blo 1889435 21524453 := bstep (se 4 (by rfl) ⟨2017917, by rfl⟩ : syracuseStep 21524453 = 4035835) B4035835
theorem B14349635 : Blo 1889435 14349635 := bstep (se 1 (by rfl) ⟨10762226, by rfl⟩ : syracuseStep 14349635 = 21524453) B21524453
theorem B9566423 : Blo 1889435 9566423 := bstep (se 1 (by rfl) ⟨7174817, by rfl⟩ : syracuseStep 9566423 = 14349635) B14349635
theorem B6377615 : Blo 1889435 6377615 := bstep (se 1 (by rfl) ⟨4783211, by rfl⟩ : syracuseStep 6377615 = 9566423) B9566423
theorem B4251743 : Blo 1889435 4251743 := bstep (se 1 (by rfl) ⟨3188807, by rfl⟩ : syracuseStep 4251743 = 6377615) B6377615
theorem B2834495 : Blo 1889435 2834495 := bstep (se 1 (by rfl) ⟨2125871, by rfl⟩ : syracuseStep 2834495 = 4251743) B4251743
theorem B1889663 : Blo 1889435 1889663 := bstep (se 1 (by rfl) ⟨1417247, by rfl⟩ : syracuseStep 1889663 = 2834495) B2834495
theorem B2834501 : Blo 1889435 2834501 := bbase (se 4 (by rfl) ⟨265734, by rfl⟩ : syracuseStep 2834501 = 531469) (by norm_num)
theorem B1889667 : Blo 1889435 1889667 := bstep (se 1 (by rfl) ⟨1417250, by rfl⟩ : syracuseStep 1889667 = 2834501) B2834501
theorem B3188821 : Blo 1889435 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B4251761 : Blo 1889435 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B2834507 : Blo 1889435 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1889671 : Blo 1889435 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B2125885 : Blo 1889435 2125885 := bbase (se 3 (by rfl) ⟨398603, by rfl⟩ : syracuseStep 2125885 = 797207) (by norm_num)
theorem B2834513 : Blo 1889435 2834513 := bstep (se 2 (by rfl) ⟨1062942, by rfl⟩ : syracuseStep 2834513 = 2125885) B2125885
theorem B1889675 : Blo 1889435 1889675 := bstep (se 1 (by rfl) ⟨1417256, by rfl⟩ : syracuseStep 1889675 = 2834513) B2834513
theorem B6377669 : Blo 1889435 6377669 := bbase (se 4 (by rfl) ⟨597906, by rfl⟩ : syracuseStep 6377669 = 1195813) (by norm_num)
theorem B4251779 : Blo 1889435 4251779 := bstep (se 1 (by rfl) ⟨3188834, by rfl⟩ : syracuseStep 4251779 = 6377669) B6377669
theorem B2834519 : Blo 1889435 2834519 := bstep (se 1 (by rfl) ⟨2125889, by rfl⟩ : syracuseStep 2834519 = 4251779) B4251779
theorem B1889679 : Blo 1889435 1889679 := bstep (se 1 (by rfl) ⟨1417259, by rfl⟩ : syracuseStep 1889679 = 2834519) B2834519
theorem B2834525 : Blo 1889435 2834525 := bbase (se 3 (by rfl) ⟨531473, by rfl⟩ : syracuseStep 2834525 = 1062947) (by norm_num)
theorem B1889683 : Blo 1889435 1889683 := bstep (se 1 (by rfl) ⟨1417262, by rfl⟩ : syracuseStep 1889683 = 2834525) B2834525
theorem B4251797 : Blo 1889435 4251797 := bbase (se 6 (by rfl) ⟨99651, by rfl⟩ : syracuseStep 4251797 = 199303) (by norm_num)
theorem B2834531 : Blo 1889435 2834531 := bstep (se 1 (by rfl) ⟨2125898, by rfl⟩ : syracuseStep 2834531 = 4251797) B4251797
theorem B1889687 : Blo 1889435 1889687 := bstep (se 1 (by rfl) ⟨1417265, by rfl⟩ : syracuseStep 1889687 = 2834531) B2834531
theorem B2690597 : Blo 1889435 2690597 := bbase (se 4 (by rfl) ⟨252243, by rfl⟩ : syracuseStep 2690597 = 504487) (by norm_num)
theorem B7174925 : Blo 1889435 7174925 := bstep (se 3 (by rfl) ⟨1345298, by rfl⟩ : syracuseStep 7174925 = 2690597) B2690597
theorem B4783283 : Blo 1889435 4783283 := bstep (se 1 (by rfl) ⟨3587462, by rfl⟩ : syracuseStep 4783283 = 7174925) B7174925
theorem B3188855 : Blo 1889435 3188855 := bstep (se 1 (by rfl) ⟨2391641, by rfl⟩ : syracuseStep 3188855 = 4783283) B4783283
theorem B2125903 : Blo 1889435 2125903 := bstep (se 1 (by rfl) ⟨1594427, by rfl⟩ : syracuseStep 2125903 = 3188855) B3188855
theorem B2834537 : Blo 1889435 2834537 := bstep (se 2 (by rfl) ⟨1062951, by rfl⟩ : syracuseStep 2834537 = 2125903) B2125903
theorem B1889691 : Blo 1889435 1889691 := bstep (se 1 (by rfl) ⟨1417268, by rfl⟩ : syracuseStep 1889691 = 2834537) B2834537
theorem B9204677 : Blo 1889435 9204677 := bbase (se 4 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 9204677 = 1725877) (by norm_num)
theorem B6136451 : Blo 1889435 6136451 := bstep (se 1 (by rfl) ⟨4602338, by rfl⟩ : syracuseStep 6136451 = 9204677) B9204677
theorem B4090967 : Blo 1889435 4090967 := bstep (se 1 (by rfl) ⟨3068225, by rfl⟩ : syracuseStep 4090967 = 6136451) B6136451
theorem B43636981 : Blo 1889435 43636981 := bstep (se 5 (by rfl) ⟨2045483, by rfl⟩ : syracuseStep 43636981 = 4090967) B4090967
theorem B58182641 : Blo 1889435 58182641 := bstep (se 2 (by rfl) ⟨21818490, by rfl⟩ : syracuseStep 58182641 = 43636981) B43636981
theorem B38788427 : Blo 1889435 38788427 := bstep (se 1 (by rfl) ⟨29091320, by rfl⟩ : syracuseStep 38788427 = 58182641) B58182641
theorem B103435805 : Blo 1889435 103435805 := bstep (se 3 (by rfl) ⟨19394213, by rfl⟩ : syracuseStep 103435805 = 38788427) B38788427
theorem B68957203 : Blo 1889435 68957203 := bstep (se 1 (by rfl) ⟨51717902, by rfl⟩ : syracuseStep 68957203 = 103435805) B103435805
theorem B91942937 : Blo 1889435 91942937 := bstep (se 2 (by rfl) ⟨34478601, by rfl⟩ : syracuseStep 91942937 = 68957203) B68957203
theorem B61295291 : Blo 1889435 61295291 := bstep (se 1 (by rfl) ⟨45971468, by rfl⟩ : syracuseStep 61295291 = 91942937) B91942937
theorem B40863527 : Blo 1889435 40863527 := bstep (se 1 (by rfl) ⟨30647645, by rfl⟩ : syracuseStep 40863527 = 61295291) B61295291
theorem B27242351 : Blo 1889435 27242351 := bstep (se 1 (by rfl) ⟨20431763, by rfl⟩ : syracuseStep 27242351 = 40863527) B40863527
theorem B18161567 : Blo 1889435 18161567 := bstep (se 1 (by rfl) ⟨13621175, by rfl⟩ : syracuseStep 18161567 = 27242351) B27242351
theorem B12107711 : Blo 1889435 12107711 := bstep (se 1 (by rfl) ⟨9080783, by rfl⟩ : syracuseStep 12107711 = 18161567) B18161567
theorem B8071807 : Blo 1889435 8071807 := bstep (se 1 (by rfl) ⟨6053855, by rfl⟩ : syracuseStep 8071807 = 12107711) B12107711
theorem B10762409 : Blo 1889435 10762409 := bstep (se 2 (by rfl) ⟨4035903, by rfl⟩ : syracuseStep 10762409 = 8071807) B8071807
theorem B7174939 : Blo 1889435 7174939 := bstep (se 1 (by rfl) ⟨5381204, by rfl⟩ : syracuseStep 7174939 = 10762409) B10762409
theorem B9566585 : Blo 1889435 9566585 := bstep (se 2 (by rfl) ⟨3587469, by rfl⟩ : syracuseStep 9566585 = 7174939) B7174939
theorem B6377723 : Blo 1889435 6377723 := bstep (se 1 (by rfl) ⟨4783292, by rfl⟩ : syracuseStep 6377723 = 9566585) B9566585
theorem B4251815 : Blo 1889435 4251815 := bstep (se 1 (by rfl) ⟨3188861, by rfl⟩ : syracuseStep 4251815 = 6377723) B6377723
theorem B2834543 : Blo 1889435 2834543 := bstep (se 1 (by rfl) ⟨2125907, by rfl⟩ : syracuseStep 2834543 = 4251815) B4251815
theorem B1889695 : Blo 1889435 1889695 := bstep (se 1 (by rfl) ⟨1417271, by rfl⟩ : syracuseStep 1889695 = 2834543) B2834543
theorem B2834549 : Blo 1889435 2834549 := bbase (se 5 (by rfl) ⟨132869, by rfl⟩ : syracuseStep 2834549 = 265739) (by norm_num)
theorem B1889699 : Blo 1889435 1889699 := bstep (se 1 (by rfl) ⟨1417274, by rfl⟩ : syracuseStep 1889699 = 2834549) B2834549
theorem B3587485 : Blo 1889435 3587485 := bbase (se 3 (by rfl) ⟨672653, by rfl⟩ : syracuseStep 3587485 = 1345307) (by norm_num)
theorem B4783313 : Blo 1889435 4783313 := bstep (se 2 (by rfl) ⟨1793742, by rfl⟩ : syracuseStep 4783313 = 3587485) B3587485
theorem B3188875 : Blo 1889435 3188875 := bstep (se 1 (by rfl) ⟨2391656, by rfl⟩ : syracuseStep 3188875 = 4783313) B4783313
theorem B4251833 : Blo 1889435 4251833 := bstep (se 2 (by rfl) ⟨1594437, by rfl⟩ : syracuseStep 4251833 = 3188875) B3188875
theorem B2834555 : Blo 1889435 2834555 := bstep (se 1 (by rfl) ⟨2125916, by rfl⟩ : syracuseStep 2834555 = 4251833) B4251833
theorem B1889703 : Blo 1889435 1889703 := bstep (se 1 (by rfl) ⟨1417277, by rfl⟩ : syracuseStep 1889703 = 2834555) B2834555
theorem B2125921 : Blo 1889435 2125921 := bbase (se 2 (by rfl) ⟨797220, by rfl⟩ : syracuseStep 2125921 = 1594441) (by norm_num)
theorem B2834561 : Blo 1889435 2834561 := bstep (se 2 (by rfl) ⟨1062960, by rfl⟩ : syracuseStep 2834561 = 2125921) B2125921
theorem B1889707 : Blo 1889435 1889707 := bstep (se 1 (by rfl) ⟨1417280, by rfl⟩ : syracuseStep 1889707 = 2834561) B2834561
theorem B4783333 : Blo 1889435 4783333 := bbase (se 4 (by rfl) ⟨448437, by rfl⟩ : syracuseStep 4783333 = 896875) (by norm_num)
theorem B6377777 : Blo 1889435 6377777 := bstep (se 2 (by rfl) ⟨2391666, by rfl⟩ : syracuseStep 6377777 = 4783333) B4783333
theorem B4251851 : Blo 1889435 4251851 := bstep (se 1 (by rfl) ⟨3188888, by rfl⟩ : syracuseStep 4251851 = 6377777) B6377777
theorem B2834567 : Blo 1889435 2834567 := bstep (se 1 (by rfl) ⟨2125925, by rfl⟩ : syracuseStep 2834567 = 4251851) B4251851
theorem B1889711 : Blo 1889435 1889711 := bstep (se 1 (by rfl) ⟨1417283, by rfl⟩ : syracuseStep 1889711 = 2834567) B2834567
theorem B2834573 : Blo 1889435 2834573 := bbase (se 3 (by rfl) ⟨531482, by rfl⟩ : syracuseStep 2834573 = 1062965) (by norm_num)
theorem B1889715 : Blo 1889435 1889715 := bstep (se 1 (by rfl) ⟨1417286, by rfl⟩ : syracuseStep 1889715 = 2834573) B2834573
theorem B4251869 : Blo 1889435 4251869 := bbase (se 3 (by rfl) ⟨797225, by rfl⟩ : syracuseStep 4251869 = 1594451) (by norm_num)
theorem B2834579 : Blo 1889435 2834579 := bstep (se 1 (by rfl) ⟨2125934, by rfl⟩ : syracuseStep 2834579 = 4251869) B4251869
theorem B1889719 : Blo 1889435 1889719 := bstep (se 1 (by rfl) ⟨1417289, by rfl⟩ : syracuseStep 1889719 = 2834579) B2834579
theorem B3188909 : Blo 1889435 3188909 := bbase (se 3 (by rfl) ⟨597920, by rfl⟩ : syracuseStep 3188909 = 1195841) (by norm_num)
theorem B2125939 : Blo 1889435 2125939 := bstep (se 1 (by rfl) ⟨1594454, by rfl⟩ : syracuseStep 2125939 = 3188909) B3188909
theorem B2834585 : Blo 1889435 2834585 := bstep (se 2 (by rfl) ⟨1062969, by rfl⟩ : syracuseStep 2834585 = 2125939) B2125939
theorem B1889723 : Blo 1889435 1889723 := bstep (se 1 (by rfl) ⟨1417292, by rfl⟩ : syracuseStep 1889723 = 2834585) B2834585
theorem B8619797 : Blo 1889435 8619797 := bbase (se 6 (by rfl) ⟨202026, by rfl⟩ : syracuseStep 8619797 = 404053) (by norm_num)
theorem B5746531 : Blo 1889435 5746531 := bstep (se 1 (by rfl) ⟨4309898, by rfl⟩ : syracuseStep 5746531 = 8619797) B8619797
theorem B7662041 : Blo 1889435 7662041 := bstep (se 2 (by rfl) ⟨2873265, by rfl⟩ : syracuseStep 7662041 = 5746531) B5746531
theorem B5108027 : Blo 1889435 5108027 := bstep (se 1 (by rfl) ⟨3831020, by rfl⟩ : syracuseStep 5108027 = 7662041) B7662041
theorem B54485621 : Blo 1889435 54485621 := bstep (se 5 (by rfl) ⟨2554013, by rfl⟩ : syracuseStep 54485621 = 5108027) B5108027
theorem B36323747 : Blo 1889435 36323747 := bstep (se 1 (by rfl) ⟨27242810, by rfl⟩ : syracuseStep 36323747 = 54485621) B54485621
theorem B24215831 : Blo 1889435 24215831 := bstep (se 1 (by rfl) ⟨18161873, by rfl⟩ : syracuseStep 24215831 = 36323747) B36323747
theorem B16143887 : Blo 1889435 16143887 := bstep (se 1 (by rfl) ⟨12107915, by rfl⟩ : syracuseStep 16143887 = 24215831) B24215831
theorem B10762591 : Blo 1889435 10762591 := bstep (se 1 (by rfl) ⟨8071943, by rfl⟩ : syracuseStep 10762591 = 16143887) B16143887
theorem B14350121 : Blo 1889435 14350121 := bstep (se 2 (by rfl) ⟨5381295, by rfl⟩ : syracuseStep 14350121 = 10762591) B10762591
theorem B9566747 : Blo 1889435 9566747 := bstep (se 1 (by rfl) ⟨7175060, by rfl⟩ : syracuseStep 9566747 = 14350121) B14350121
theorem B6377831 : Blo 1889435 6377831 := bstep (se 1 (by rfl) ⟨4783373, by rfl⟩ : syracuseStep 6377831 = 9566747) B9566747
theorem B4251887 : Blo 1889435 4251887 := bstep (se 1 (by rfl) ⟨3188915, by rfl⟩ : syracuseStep 4251887 = 6377831) B6377831
theorem B2834591 : Blo 1889435 2834591 := bstep (se 1 (by rfl) ⟨2125943, by rfl⟩ : syracuseStep 2834591 = 4251887) B4251887
theorem B1889727 : Blo 1889435 1889727 := bstep (se 1 (by rfl) ⟨1417295, by rfl⟩ : syracuseStep 1889727 = 2834591) B2834591
theorem B2834597 : Blo 1889435 2834597 := bbase (se 4 (by rfl) ⟨265743, by rfl⟩ : syracuseStep 2834597 = 531487) (by norm_num)
theorem B1889731 : Blo 1889435 1889731 := bstep (se 1 (by rfl) ⟨1417298, by rfl⟩ : syracuseStep 1889731 = 2834597) B2834597
theorem B2391697 : Blo 1889435 2391697 := bbase (se 2 (by rfl) ⟨896886, by rfl⟩ : syracuseStep 2391697 = 1793773) (by norm_num)
theorem B3188929 : Blo 1889435 3188929 := bstep (se 2 (by rfl) ⟨1195848, by rfl⟩ : syracuseStep 3188929 = 2391697) B2391697
theorem B4251905 : Blo 1889435 4251905 := bstep (se 2 (by rfl) ⟨1594464, by rfl⟩ : syracuseStep 4251905 = 3188929) B3188929
theorem B2834603 : Blo 1889435 2834603 := bstep (se 1 (by rfl) ⟨2125952, by rfl⟩ : syracuseStep 2834603 = 4251905) B4251905
theorem B1889735 : Blo 1889435 1889735 := bstep (se 1 (by rfl) ⟨1417301, by rfl⟩ : syracuseStep 1889735 = 2834603) B2834603
theorem B2125957 : Blo 1889435 2125957 := bbase (se 4 (by rfl) ⟨199308, by rfl⟩ : syracuseStep 2125957 = 398617) (by norm_num)
theorem B2834609 : Blo 1889435 2834609 := bstep (se 2 (by rfl) ⟨1062978, by rfl⟩ : syracuseStep 2834609 = 2125957) B2125957
theorem B1889739 : Blo 1889435 1889739 := bstep (se 1 (by rfl) ⟨1417304, by rfl⟩ : syracuseStep 1889739 = 2834609) B2834609
theorem B3232453 : Blo 1889435 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B4309937 : Blo 1889435 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B2873291 : Blo 1889435 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B7662109 : Blo 1889435 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B10216145 : Blo 1889435 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B6810763 : Blo 1889435 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B9081017 : Blo 1889435 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B6054011 : Blo 1889435 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B4036007 : Blo 1889435 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B2690671 : Blo 1889435 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B3587561 : Blo 1889435 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B2391707 : Blo 1889435 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B6377885 : Blo 1889435 6377885 := bstep (se 3 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 6377885 = 2391707) B2391707
theorem B4251923 : Blo 1889435 4251923 := bstep (se 1 (by rfl) ⟨3188942, by rfl⟩ : syracuseStep 4251923 = 6377885) B6377885
theorem B2834615 : Blo 1889435 2834615 := bstep (se 1 (by rfl) ⟨2125961, by rfl⟩ : syracuseStep 2834615 = 4251923) B4251923
theorem B1889743 : Blo 1889435 1889743 := bstep (se 1 (by rfl) ⟨1417307, by rfl⟩ : syracuseStep 1889743 = 2834615) B2834615
theorem B2834621 : Blo 1889435 2834621 := bbase (se 3 (by rfl) ⟨531491, by rfl⟩ : syracuseStep 2834621 = 1062983) (by norm_num)
theorem B1889747 : Blo 1889435 1889747 := bstep (se 1 (by rfl) ⟨1417310, by rfl⟩ : syracuseStep 1889747 = 2834621) B2834621
theorem B4251941 : Blo 1889435 4251941 := bbase (se 4 (by rfl) ⟨398619, by rfl⟩ : syracuseStep 4251941 = 797239) (by norm_num)
theorem B2834627 : Blo 1889435 2834627 := bstep (se 1 (by rfl) ⟨2125970, by rfl⟩ : syracuseStep 2834627 = 4251941) B4251941
theorem B1889751 : Blo 1889435 1889751 := bstep (se 1 (by rfl) ⟨1417313, by rfl⟩ : syracuseStep 1889751 = 2834627) B2834627
theorem B4783445 : Blo 1889435 4783445 := bbase (se 11 (by rfl) ⟨3503, by rfl⟩ : syracuseStep 4783445 = 7007) (by norm_num)
theorem B3188963 : Blo 1889435 3188963 := bstep (se 1 (by rfl) ⟨2391722, by rfl⟩ : syracuseStep 3188963 = 4783445) B4783445
theorem B2125975 : Blo 1889435 2125975 := bstep (se 1 (by rfl) ⟨1594481, by rfl⟩ : syracuseStep 2125975 = 3188963) B3188963
theorem B2834633 : Blo 1889435 2834633 := bstep (se 2 (by rfl) ⟨1062987, by rfl⟩ : syracuseStep 2834633 = 2125975) B2125975
theorem B1889755 : Blo 1889435 1889755 := bstep (se 1 (by rfl) ⟨1417316, by rfl⟩ : syracuseStep 1889755 = 2834633) B2834633
theorem B2270273 : Blo 1889435 2270273 := bbase (se 2 (by rfl) ⟨851352, by rfl⟩ : syracuseStep 2270273 = 1702705) (by norm_num)
theorem B6054061 : Blo 1889435 6054061 := bstep (se 3 (by rfl) ⟨1135136, by rfl⟩ : syracuseStep 6054061 = 2270273) B2270273
theorem B8072081 : Blo 1889435 8072081 := bstep (se 2 (by rfl) ⟨3027030, by rfl⟩ : syracuseStep 8072081 = 6054061) B6054061
theorem B5381387 : Blo 1889435 5381387 := bstep (se 1 (by rfl) ⟨4036040, by rfl⟩ : syracuseStep 5381387 = 8072081) B8072081
theorem B3587591 : Blo 1889435 3587591 := bstep (se 1 (by rfl) ⟨2690693, by rfl⟩ : syracuseStep 3587591 = 5381387) B5381387
theorem B9566909 : Blo 1889435 9566909 := bstep (se 3 (by rfl) ⟨1793795, by rfl⟩ : syracuseStep 9566909 = 3587591) B3587591
theorem B6377939 : Blo 1889435 6377939 := bstep (se 1 (by rfl) ⟨4783454, by rfl⟩ : syracuseStep 6377939 = 9566909) B9566909
theorem B4251959 : Blo 1889435 4251959 := bstep (se 1 (by rfl) ⟨3188969, by rfl⟩ : syracuseStep 4251959 = 6377939) B6377939
theorem B2834639 : Blo 1889435 2834639 := bstep (se 1 (by rfl) ⟨2125979, by rfl⟩ : syracuseStep 2834639 = 4251959) B4251959
theorem B1889759 : Blo 1889435 1889759 := bstep (se 1 (by rfl) ⟨1417319, by rfl⟩ : syracuseStep 1889759 = 2834639) B2834639
theorem B2834645 : Blo 1889435 2834645 := bbase (se 7 (by rfl) ⟨33218, by rfl⟩ : syracuseStep 2834645 = 66437) (by norm_num)
theorem B1889763 : Blo 1889435 1889763 := bstep (se 1 (by rfl) ⟨1417322, by rfl⟩ : syracuseStep 1889763 = 2834645) B2834645
theorem B2018029 : Blo 1889435 2018029 := bbase (se 3 (by rfl) ⟨378380, by rfl⟩ : syracuseStep 2018029 = 756761) (by norm_num)
theorem B2690705 : Blo 1889435 2690705 := bstep (se 2 (by rfl) ⟨1009014, by rfl⟩ : syracuseStep 2690705 = 2018029) B2018029
theorem B7175213 : Blo 1889435 7175213 := bstep (se 3 (by rfl) ⟨1345352, by rfl⟩ : syracuseStep 7175213 = 2690705) B2690705
theorem B4783475 : Blo 1889435 4783475 := bstep (se 1 (by rfl) ⟨3587606, by rfl⟩ : syracuseStep 4783475 = 7175213) B7175213
theorem B3188983 : Blo 1889435 3188983 := bstep (se 1 (by rfl) ⟨2391737, by rfl⟩ : syracuseStep 3188983 = 4783475) B4783475
theorem B4251977 : Blo 1889435 4251977 := bstep (se 2 (by rfl) ⟨1594491, by rfl⟩ : syracuseStep 4251977 = 3188983) B3188983
theorem B2834651 : Blo 1889435 2834651 := bstep (se 1 (by rfl) ⟨2125988, by rfl⟩ : syracuseStep 2834651 = 4251977) B4251977
theorem B1889767 : Blo 1889435 1889767 := bstep (se 1 (by rfl) ⟨1417325, by rfl⟩ : syracuseStep 1889767 = 2834651) B2834651
theorem B2125993 : Blo 1889435 2125993 := bbase (se 2 (by rfl) ⟨797247, by rfl⟩ : syracuseStep 2125993 = 1594495) (by norm_num)
theorem B2834657 : Blo 1889435 2834657 := bstep (se 2 (by rfl) ⟨1062996, by rfl⟩ : syracuseStep 2834657 = 2125993) B2125993
theorem B1889771 : Blo 1889435 1889771 := bstep (se 1 (by rfl) ⟨1417328, by rfl⟩ : syracuseStep 1889771 = 2834657) B2834657
theorem B8072149 : Blo 1889435 8072149 := bbase (se 7 (by rfl) ⟨94595, by rfl⟩ : syracuseStep 8072149 = 189191) (by norm_num)
theorem B10762865 : Blo 1889435 10762865 := bstep (se 2 (by rfl) ⟨4036074, by rfl⟩ : syracuseStep 10762865 = 8072149) B8072149
theorem B7175243 : Blo 1889435 7175243 := bstep (se 1 (by rfl) ⟨5381432, by rfl⟩ : syracuseStep 7175243 = 10762865) B10762865
theorem B4783495 : Blo 1889435 4783495 := bstep (se 1 (by rfl) ⟨3587621, by rfl⟩ : syracuseStep 4783495 = 7175243) B7175243
theorem B6377993 : Blo 1889435 6377993 := bstep (se 2 (by rfl) ⟨2391747, by rfl⟩ : syracuseStep 6377993 = 4783495) B4783495
theorem B4251995 : Blo 1889435 4251995 := bstep (se 1 (by rfl) ⟨3188996, by rfl⟩ : syracuseStep 4251995 = 6377993) B6377993
theorem B2834663 : Blo 1889435 2834663 := bstep (se 1 (by rfl) ⟨2125997, by rfl⟩ : syracuseStep 2834663 = 4251995) B4251995
theorem B1889775 : Blo 1889435 1889775 := bstep (se 1 (by rfl) ⟨1417331, by rfl⟩ : syracuseStep 1889775 = 2834663) B2834663
theorem B2834669 : Blo 1889435 2834669 := bbase (se 3 (by rfl) ⟨531500, by rfl⟩ : syracuseStep 2834669 = 1063001) (by norm_num)
theorem B1889779 : Blo 1889435 1889779 := bstep (se 1 (by rfl) ⟨1417334, by rfl⟩ : syracuseStep 1889779 = 2834669) B2834669
theorem B4252013 : Blo 1889435 4252013 := bbase (se 3 (by rfl) ⟨797252, by rfl⟩ : syracuseStep 4252013 = 1594505) (by norm_num)
theorem B2834675 : Blo 1889435 2834675 := bstep (se 1 (by rfl) ⟨2126006, by rfl⟩ : syracuseStep 2834675 = 4252013) B4252013
theorem B1889783 : Blo 1889435 1889783 := bstep (se 1 (by rfl) ⟨1417337, by rfl⟩ : syracuseStep 1889783 = 2834675) B2834675
theorem B3587645 : Blo 1889435 3587645 := bbase (se 3 (by rfl) ⟨672683, by rfl⟩ : syracuseStep 3587645 = 1345367) (by norm_num)
theorem B2391763 : Blo 1889435 2391763 := bstep (se 1 (by rfl) ⟨1793822, by rfl⟩ : syracuseStep 2391763 = 3587645) B3587645
theorem B3189017 : Blo 1889435 3189017 := bstep (se 2 (by rfl) ⟨1195881, by rfl⟩ : syracuseStep 3189017 = 2391763) B2391763
theorem B2126011 : Blo 1889435 2126011 := bstep (se 1 (by rfl) ⟨1594508, by rfl⟩ : syracuseStep 2126011 = 3189017) B3189017
theorem B2834681 : Blo 1889435 2834681 := bstep (se 2 (by rfl) ⟨1063005, by rfl⟩ : syracuseStep 2834681 = 2126011) B2126011
theorem B1889787 : Blo 1889435 1889787 := bstep (se 1 (by rfl) ⟨1417340, by rfl⟩ : syracuseStep 1889787 = 2834681) B2834681
theorem B6305365 : Blo 1889435 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B8407153 : Blo 1889435 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B11209537 : Blo 1889435 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B14946049 : Blo 1889435 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B19928065 : Blo 1889435 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B26570753 : Blo 1889435 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B17713835 : Blo 1889435 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B11809223 : Blo 1889435 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B7872815 : Blo 1889435 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B5248543 : Blo 1889435 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B6998057 : Blo 1889435 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B4665371 : Blo 1889435 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B12440989 : Blo 1889435 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B16587985 : Blo 1889435 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B22117313 : Blo 1889435 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B14744875 : Blo 1889435 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B19659833 : Blo 1889435 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B13106555 : Blo 1889435 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B8737703 : Blo 1889435 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B5825135 : Blo 1889435 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B15533693 : Blo 1889435 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B10355795 : Blo 1889435 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B6903863 : Blo 1889435 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B4602575 : Blo 1889435 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B3068383 : Blo 1889435 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B4091177 : Blo 1889435 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B2727451 : Blo 1889435 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B14546405 : Blo 1889435 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B9697603 : Blo 1889435 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B12930137 : Blo 1889435 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B8620091 : Blo 1889435 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B5746727 : Blo 1889435 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B3831151 : Blo 1889435 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B5108201 : Blo 1889435 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B3405467 : Blo 1889435 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B2270311 : Blo 1889435 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B48433301 : Blo 1889435 48433301 := bstep (se 6 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 48433301 = 2270311) B2270311
theorem B32288867 : Blo 1889435 32288867 := bstep (se 1 (by rfl) ⟨24216650, by rfl⟩ : syracuseStep 32288867 = 48433301) B48433301
theorem B21525911 : Blo 1889435 21525911 := bstep (se 1 (by rfl) ⟨16144433, by rfl⟩ : syracuseStep 21525911 = 32288867) B32288867
theorem B14350607 : Blo 1889435 14350607 := bstep (se 1 (by rfl) ⟨10762955, by rfl⟩ : syracuseStep 14350607 = 21525911) B21525911
theorem B9567071 : Blo 1889435 9567071 := bstep (se 1 (by rfl) ⟨7175303, by rfl⟩ : syracuseStep 9567071 = 14350607) B14350607
theorem B6378047 : Blo 1889435 6378047 := bstep (se 1 (by rfl) ⟨4783535, by rfl⟩ : syracuseStep 6378047 = 9567071) B9567071
theorem B4252031 : Blo 1889435 4252031 := bstep (se 1 (by rfl) ⟨3189023, by rfl⟩ : syracuseStep 4252031 = 6378047) B6378047
theorem B2834687 : Blo 1889435 2834687 := bstep (se 1 (by rfl) ⟨2126015, by rfl⟩ : syracuseStep 2834687 = 4252031) B4252031
theorem B1889791 : Blo 1889435 1889791 := bstep (se 1 (by rfl) ⟨1417343, by rfl⟩ : syracuseStep 1889791 = 2834687) B2834687
theorem B2834693 : Blo 1889435 2834693 := bbase (se 4 (by rfl) ⟨265752, by rfl⟩ : syracuseStep 2834693 = 531505) (by norm_num)
theorem B1889795 : Blo 1889435 1889795 := bstep (se 1 (by rfl) ⟨1417346, by rfl⟩ : syracuseStep 1889795 = 2834693) B2834693
theorem B3189037 : Blo 1889435 3189037 := bbase (se 3 (by rfl) ⟨597944, by rfl⟩ : syracuseStep 3189037 = 1195889) (by norm_num)
theorem B4252049 : Blo 1889435 4252049 := bstep (se 2 (by rfl) ⟨1594518, by rfl⟩ : syracuseStep 4252049 = 3189037) B3189037
theorem B2834699 : Blo 1889435 2834699 := bstep (se 1 (by rfl) ⟨2126024, by rfl⟩ : syracuseStep 2834699 = 4252049) B4252049
theorem B1889799 : Blo 1889435 1889799 := bstep (se 1 (by rfl) ⟨1417349, by rfl⟩ : syracuseStep 1889799 = 2834699) B2834699
theorem B2126029 : Blo 1889435 2126029 := bbase (se 3 (by rfl) ⟨398630, by rfl⟩ : syracuseStep 2126029 = 797261) (by norm_num)
theorem B2834705 : Blo 1889435 2834705 := bstep (se 2 (by rfl) ⟨1063014, by rfl⟩ : syracuseStep 2834705 = 2126029) B2126029
theorem B1889803 : Blo 1889435 1889803 := bstep (se 1 (by rfl) ⟨1417352, by rfl⟩ : syracuseStep 1889803 = 2834705) B2834705
theorem B6378101 : Blo 1889435 6378101 := bbase (se 5 (by rfl) ⟨298973, by rfl⟩ : syracuseStep 6378101 = 597947) (by norm_num)
theorem B4252067 : Blo 1889435 4252067 := bstep (se 1 (by rfl) ⟨3189050, by rfl⟩ : syracuseStep 4252067 = 6378101) B6378101
theorem B2834711 : Blo 1889435 2834711 := bstep (se 1 (by rfl) ⟨2126033, by rfl⟩ : syracuseStep 2834711 = 4252067) B4252067
theorem B1889807 : Blo 1889435 1889807 := bstep (se 1 (by rfl) ⟨1417355, by rfl⟩ : syracuseStep 1889807 = 2834711) B2834711
theorem B2834717 : Blo 1889435 2834717 := bbase (se 3 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 2834717 = 1063019) (by norm_num)
theorem B1889811 : Blo 1889435 1889811 := bstep (se 1 (by rfl) ⟨1417358, by rfl⟩ : syracuseStep 1889811 = 2834717) B2834717
theorem B4252085 : Blo 1889435 4252085 := bbase (se 5 (by rfl) ⟨199316, by rfl⟩ : syracuseStep 4252085 = 398633) (by norm_num)
theorem B2834723 : Blo 1889435 2834723 := bstep (se 1 (by rfl) ⟨2126042, by rfl⟩ : syracuseStep 2834723 = 4252085) B4252085
theorem B1889815 : Blo 1889435 1889815 := bstep (se 1 (by rfl) ⟨1417361, by rfl⟩ : syracuseStep 1889815 = 2834723) B2834723
theorem B3546821 : Blo 1889435 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2364547 : Blo 1889435 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3152729 : Blo 1889435 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B8407277 : Blo 1889435 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B5604851 : Blo 1889435 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B3736567 : Blo 1889435 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B19928357 : Blo 1889435 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B13285571 : Blo 1889435 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B141712757 : Blo 1889435 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B94475171 : Blo 1889435 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B251933789 : Blo 1889435 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B167955859 : Blo 1889435 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B223941145 : Blo 1889435 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B298588193 : Blo 1889435 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B199058795 : Blo 1889435 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B132705863 : Blo 1889435 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B88470575 : Blo 1889435 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B58980383 : Blo 1889435 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B39320255 : Blo 1889435 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B26213503 : Blo 1889435 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B34951337 : Blo 1889435 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B23300891 : Blo 1889435 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B15533927 : Blo 1889435 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B10355951 : Blo 1889435 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B6903967 : Blo 1889435 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B9205289 : Blo 1889435 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B6136859 : Blo 1889435 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B4091239 : Blo 1889435 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B21819941 : Blo 1889435 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B14546627 : Blo 1889435 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B9697751 : Blo 1889435 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B6465167 : Blo 1889435 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B4310111 : Blo 1889435 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B2873407 : Blo 1889435 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B3831209 : Blo 1889435 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B2554139 : Blo 1889435 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B6811037 : Blo 1889435 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B4540691 : Blo 1889435 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B3027127 : Blo 1889435 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B4036169 : Blo 1889435 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B10763117 : Blo 1889435 10763117 := bstep (se 3 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 10763117 = 4036169) B4036169
theorem B7175411 : Blo 1889435 7175411 := bstep (se 1 (by rfl) ⟨5381558, by rfl⟩ : syracuseStep 7175411 = 10763117) B10763117
theorem B4783607 : Blo 1889435 4783607 := bstep (se 1 (by rfl) ⟨3587705, by rfl⟩ : syracuseStep 4783607 = 7175411) B7175411
theorem B3189071 : Blo 1889435 3189071 := bstep (se 1 (by rfl) ⟨2391803, by rfl⟩ : syracuseStep 3189071 = 4783607) B4783607
theorem B2126047 : Blo 1889435 2126047 := bstep (se 1 (by rfl) ⟨1594535, by rfl⟩ : syracuseStep 2126047 = 3189071) B3189071
theorem B2834729 : Blo 1889435 2834729 := bstep (se 2 (by rfl) ⟨1063023, by rfl⟩ : syracuseStep 2834729 = 2126047) B2126047
theorem B1889819 : Blo 1889435 1889819 := bstep (se 1 (by rfl) ⟨1417364, by rfl⟩ : syracuseStep 1889819 = 2834729) B2834729
theorem B3027133 : Blo 1889435 3027133 := bbase (se 3 (by rfl) ⟨567587, by rfl⟩ : syracuseStep 3027133 = 1135175) (by norm_num)
theorem B4036177 : Blo 1889435 4036177 := bstep (se 2 (by rfl) ⟨1513566, by rfl⟩ : syracuseStep 4036177 = 3027133) B3027133
theorem B5381569 : Blo 1889435 5381569 := bstep (se 2 (by rfl) ⟨2018088, by rfl⟩ : syracuseStep 5381569 = 4036177) B4036177
theorem B7175425 : Blo 1889435 7175425 := bstep (se 2 (by rfl) ⟨2690784, by rfl⟩ : syracuseStep 7175425 = 5381569) B5381569
theorem B9567233 : Blo 1889435 9567233 := bstep (se 2 (by rfl) ⟨3587712, by rfl⟩ : syracuseStep 9567233 = 7175425) B7175425
theorem B6378155 : Blo 1889435 6378155 := bstep (se 1 (by rfl) ⟨4783616, by rfl⟩ : syracuseStep 6378155 = 9567233) B9567233
theorem B4252103 : Blo 1889435 4252103 := bstep (se 1 (by rfl) ⟨3189077, by rfl⟩ : syracuseStep 4252103 = 6378155) B6378155
theorem B2834735 : Blo 1889435 2834735 := bstep (se 1 (by rfl) ⟨2126051, by rfl⟩ : syracuseStep 2834735 = 4252103) B4252103
theorem B1889823 : Blo 1889435 1889823 := bstep (se 1 (by rfl) ⟨1417367, by rfl⟩ : syracuseStep 1889823 = 2834735) B2834735
theorem B2834741 : Blo 1889435 2834741 := bbase (se 5 (by rfl) ⟨132878, by rfl⟩ : syracuseStep 2834741 = 265757) (by norm_num)
theorem B1889827 : Blo 1889435 1889827 := bstep (se 1 (by rfl) ⟨1417370, by rfl⟩ : syracuseStep 1889827 = 2834741) B2834741
theorem B4783637 : Blo 1889435 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B3189091 : Blo 1889435 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B4252121 : Blo 1889435 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B2834747 : Blo 1889435 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B1889831 : Blo 1889435 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B2126065 : Blo 1889435 2126065 := bbase (se 2 (by rfl) ⟨797274, by rfl⟩ : syracuseStep 2126065 = 1594549) (by norm_num)
theorem B2834753 : Blo 1889435 2834753 := bstep (se 2 (by rfl) ⟨1063032, by rfl⟩ : syracuseStep 2834753 = 2126065) B2126065
theorem B1889835 : Blo 1889435 1889835 := bstep (se 1 (by rfl) ⟨1417376, by rfl⟩ : syracuseStep 1889835 = 2834753) B2834753
theorem B5985317 : Blo 1889435 5985317 := bbase (se 4 (by rfl) ⟨561123, by rfl⟩ : syracuseStep 5985317 = 1122247) (by norm_num)
theorem B3990211 : Blo 1889435 3990211 := bstep (se 1 (by rfl) ⟨2992658, by rfl⟩ : syracuseStep 3990211 = 5985317) B5985317
theorem B21281125 : Blo 1889435 21281125 := bstep (se 4 (by rfl) ⟨1995105, by rfl⟩ : syracuseStep 21281125 = 3990211) B3990211
theorem B28374833 : Blo 1889435 28374833 := bstep (se 2 (by rfl) ⟨10640562, by rfl⟩ : syracuseStep 28374833 = 21281125) B21281125
theorem B75666221 : Blo 1889435 75666221 := bstep (se 3 (by rfl) ⟨14187416, by rfl⟩ : syracuseStep 75666221 = 28374833) B28374833
theorem B50444147 : Blo 1889435 50444147 := bstep (se 1 (by rfl) ⟨37833110, by rfl⟩ : syracuseStep 50444147 = 75666221) B75666221
theorem B33629431 : Blo 1889435 33629431 := bstep (se 1 (by rfl) ⟨25222073, by rfl⟩ : syracuseStep 33629431 = 50444147) B50444147
theorem B44839241 : Blo 1889435 44839241 := bstep (se 2 (by rfl) ⟨16814715, by rfl⟩ : syracuseStep 44839241 = 33629431) B33629431
theorem B29892827 : Blo 1889435 29892827 := bstep (se 1 (by rfl) ⟨22419620, by rfl⟩ : syracuseStep 29892827 = 44839241) B44839241
theorem B79714205 : Blo 1889435 79714205 := bstep (se 3 (by rfl) ⟨14946413, by rfl⟩ : syracuseStep 79714205 = 29892827) B29892827
theorem B53142803 : Blo 1889435 53142803 := bstep (se 1 (by rfl) ⟨39857102, by rfl⟩ : syracuseStep 53142803 = 79714205) B79714205
theorem B35428535 : Blo 1889435 35428535 := bstep (se 1 (by rfl) ⟨26571401, by rfl⟩ : syracuseStep 35428535 = 53142803) B53142803
theorem B23619023 : Blo 1889435 23619023 := bstep (se 1 (by rfl) ⟨17714267, by rfl⟩ : syracuseStep 23619023 = 35428535) B35428535
theorem B15746015 : Blo 1889435 15746015 := bstep (se 1 (by rfl) ⟨11809511, by rfl⟩ : syracuseStep 15746015 = 23619023) B23619023
theorem B41989373 : Blo 1889435 41989373 := bstep (se 3 (by rfl) ⟨7873007, by rfl⟩ : syracuseStep 41989373 = 15746015) B15746015
theorem B27992915 : Blo 1889435 27992915 := bstep (se 1 (by rfl) ⟨20994686, by rfl⟩ : syracuseStep 27992915 = 41989373) B41989373
theorem B18661943 : Blo 1889435 18661943 := bstep (se 1 (by rfl) ⟨13996457, by rfl⟩ : syracuseStep 18661943 = 27992915) B27992915
theorem B12441295 : Blo 1889435 12441295 := bstep (se 1 (by rfl) ⟨9330971, by rfl⟩ : syracuseStep 12441295 = 18661943) B18661943
theorem B66353573 : Blo 1889435 66353573 := bstep (se 4 (by rfl) ⟨6220647, by rfl⟩ : syracuseStep 66353573 = 12441295) B12441295
theorem B44235715 : Blo 1889435 44235715 := bstep (se 1 (by rfl) ⟨33176786, by rfl⟩ : syracuseStep 44235715 = 66353573) B66353573
theorem B58980953 : Blo 1889435 58980953 := bstep (se 2 (by rfl) ⟨22117857, by rfl⟩ : syracuseStep 58980953 = 44235715) B44235715
theorem B39320635 : Blo 1889435 39320635 := bstep (se 1 (by rfl) ⟨29490476, by rfl⟩ : syracuseStep 39320635 = 58980953) B58980953
theorem B52427513 : Blo 1889435 52427513 := bstep (se 2 (by rfl) ⟨19660317, by rfl⟩ : syracuseStep 52427513 = 39320635) B39320635
theorem B34951675 : Blo 1889435 34951675 := bstep (se 1 (by rfl) ⟨26213756, by rfl⟩ : syracuseStep 34951675 = 52427513) B52427513
theorem B46602233 : Blo 1889435 46602233 := bstep (se 2 (by rfl) ⟨17475837, by rfl⟩ : syracuseStep 46602233 = 34951675) B34951675
theorem B31068155 : Blo 1889435 31068155 := bstep (se 1 (by rfl) ⟨23301116, by rfl⟩ : syracuseStep 31068155 = 46602233) B46602233
theorem B82848413 : Blo 1889435 82848413 := bstep (se 3 (by rfl) ⟨15534077, by rfl⟩ : syracuseStep 82848413 = 31068155) B31068155
theorem B55232275 : Blo 1889435 55232275 := bstep (se 1 (by rfl) ⟨41424206, by rfl⟩ : syracuseStep 55232275 = 82848413) B82848413
theorem B73643033 : Blo 1889435 73643033 := bstep (se 2 (by rfl) ⟨27616137, by rfl⟩ : syracuseStep 73643033 = 55232275) B55232275
theorem B49095355 : Blo 1889435 49095355 := bstep (se 1 (by rfl) ⟨36821516, by rfl⟩ : syracuseStep 49095355 = 73643033) B73643033
theorem B65460473 : Blo 1889435 65460473 := bstep (se 2 (by rfl) ⟨24547677, by rfl⟩ : syracuseStep 65460473 = 49095355) B49095355
theorem B43640315 : Blo 1889435 43640315 := bstep (se 1 (by rfl) ⟨32730236, by rfl⟩ : syracuseStep 43640315 = 65460473) B65460473
theorem B29093543 : Blo 1889435 29093543 := bstep (se 1 (by rfl) ⟨21820157, by rfl⟩ : syracuseStep 29093543 = 43640315) B43640315
theorem B19395695 : Blo 1889435 19395695 := bstep (se 1 (by rfl) ⟨14546771, by rfl⟩ : syracuseStep 19395695 = 29093543) B29093543
theorem B12930463 : Blo 1889435 12930463 := bstep (se 1 (by rfl) ⟨9697847, by rfl⟩ : syracuseStep 12930463 = 19395695) B19395695
theorem B17240617 : Blo 1889435 17240617 := bstep (se 2 (by rfl) ⟨6465231, by rfl⟩ : syracuseStep 17240617 = 12930463) B12930463
theorem B22987489 : Blo 1889435 22987489 := bstep (se 2 (by rfl) ⟨8620308, by rfl⟩ : syracuseStep 22987489 = 17240617) B17240617
theorem B30649985 : Blo 1889435 30649985 := bstep (se 2 (by rfl) ⟨11493744, by rfl⟩ : syracuseStep 30649985 = 22987489) B22987489
theorem B20433323 : Blo 1889435 20433323 := bstep (se 1 (by rfl) ⟨15324992, by rfl⟩ : syracuseStep 20433323 = 30649985) B30649985
theorem B13622215 : Blo 1889435 13622215 := bstep (se 1 (by rfl) ⟨10216661, by rfl⟩ : syracuseStep 13622215 = 20433323) B20433323
theorem B18162953 : Blo 1889435 18162953 := bstep (se 2 (by rfl) ⟨6811107, by rfl⟩ : syracuseStep 18162953 = 13622215) B13622215
theorem B12108635 : Blo 1889435 12108635 := bstep (se 1 (by rfl) ⟨9081476, by rfl⟩ : syracuseStep 12108635 = 18162953) B18162953
theorem B8072423 : Blo 1889435 8072423 := bstep (se 1 (by rfl) ⟨6054317, by rfl⟩ : syracuseStep 8072423 = 12108635) B12108635
theorem B5381615 : Blo 1889435 5381615 := bstep (se 1 (by rfl) ⟨4036211, by rfl⟩ : syracuseStep 5381615 = 8072423) B8072423
theorem B3587743 : Blo 1889435 3587743 := bstep (se 1 (by rfl) ⟨2690807, by rfl⟩ : syracuseStep 3587743 = 5381615) B5381615
theorem B4783657 : Blo 1889435 4783657 := bstep (se 2 (by rfl) ⟨1793871, by rfl⟩ : syracuseStep 4783657 = 3587743) B3587743
theorem B6378209 : Blo 1889435 6378209 := bstep (se 2 (by rfl) ⟨2391828, by rfl⟩ : syracuseStep 6378209 = 4783657) B4783657
theorem B4252139 : Blo 1889435 4252139 := bstep (se 1 (by rfl) ⟨3189104, by rfl⟩ : syracuseStep 4252139 = 6378209) B6378209
theorem B2834759 : Blo 1889435 2834759 := bstep (se 1 (by rfl) ⟨2126069, by rfl⟩ : syracuseStep 2834759 = 4252139) B4252139
theorem B1889839 : Blo 1889435 1889839 := bstep (se 1 (by rfl) ⟨1417379, by rfl⟩ : syracuseStep 1889839 = 2834759) B2834759
theorem B2834765 : Blo 1889435 2834765 := bbase (se 3 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 2834765 = 1063037) (by norm_num)
theorem B1889843 : Blo 1889435 1889843 := bstep (se 1 (by rfl) ⟨1417382, by rfl⟩ : syracuseStep 1889843 = 2834765) B2834765
theorem B4252157 : Blo 1889435 4252157 := bbase (se 3 (by rfl) ⟨797279, by rfl⟩ : syracuseStep 4252157 = 1594559) (by norm_num)
theorem B2834771 : Blo 1889435 2834771 := bstep (se 1 (by rfl) ⟨2126078, by rfl⟩ : syracuseStep 2834771 = 4252157) B4252157
theorem B1889847 : Blo 1889435 1889847 := bstep (se 1 (by rfl) ⟨1417385, by rfl⟩ : syracuseStep 1889847 = 2834771) B2834771
theorem B3189125 : Blo 1889435 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B2126083 : Blo 1889435 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B2834777 : Blo 1889435 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B1889851 : Blo 1889435 1889851 := bstep (se 1 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 1889851 = 2834777) B2834777
theorem B14351093 : Blo 1889435 14351093 := bbase (se 5 (by rfl) ⟨672707, by rfl⟩ : syracuseStep 14351093 = 1345415) (by norm_num)
theorem B9567395 : Blo 1889435 9567395 := bstep (se 1 (by rfl) ⟨7175546, by rfl⟩ : syracuseStep 9567395 = 14351093) B14351093
theorem B6378263 : Blo 1889435 6378263 := bstep (se 1 (by rfl) ⟨4783697, by rfl⟩ : syracuseStep 6378263 = 9567395) B9567395
theorem B4252175 : Blo 1889435 4252175 := bstep (se 1 (by rfl) ⟨3189131, by rfl⟩ : syracuseStep 4252175 = 6378263) B6378263
theorem B2834783 : Blo 1889435 2834783 := bstep (se 1 (by rfl) ⟨2126087, by rfl⟩ : syracuseStep 2834783 = 4252175) B4252175
theorem B1889855 : Blo 1889435 1889855 := bstep (se 1 (by rfl) ⟨1417391, by rfl⟩ : syracuseStep 1889855 = 2834783) B2834783
theorem B2834789 : Blo 1889435 2834789 := bbase (se 4 (by rfl) ⟨265761, by rfl⟩ : syracuseStep 2834789 = 531523) (by norm_num)
theorem B1889859 : Blo 1889435 1889859 := bstep (se 1 (by rfl) ⟨1417394, by rfl⟩ : syracuseStep 1889859 = 2834789) B2834789
theorem B3587789 : Blo 1889435 3587789 := bbase (se 3 (by rfl) ⟨672710, by rfl⟩ : syracuseStep 3587789 = 1345421) (by norm_num)
theorem B2391859 : Blo 1889435 2391859 := bstep (se 1 (by rfl) ⟨1793894, by rfl⟩ : syracuseStep 2391859 = 3587789) B3587789
theorem B3189145 : Blo 1889435 3189145 := bstep (se 2 (by rfl) ⟨1195929, by rfl⟩ : syracuseStep 3189145 = 2391859) B2391859
theorem B4252193 : Blo 1889435 4252193 := bstep (se 2 (by rfl) ⟨1594572, by rfl⟩ : syracuseStep 4252193 = 3189145) B3189145
theorem B2834795 : Blo 1889435 2834795 := bstep (se 1 (by rfl) ⟨2126096, by rfl⟩ : syracuseStep 2834795 = 4252193) B4252193
theorem B1889863 : Blo 1889435 1889863 := bstep (se 1 (by rfl) ⟨1417397, by rfl⟩ : syracuseStep 1889863 = 2834795) B2834795
theorem B2126101 : Blo 1889435 2126101 := bbase (se 6 (by rfl) ⟨49830, by rfl⟩ : syracuseStep 2126101 = 99661) (by norm_num)
theorem B2834801 : Blo 1889435 2834801 := bstep (se 2 (by rfl) ⟨1063050, by rfl⟩ : syracuseStep 2834801 = 2126101) B2126101
theorem B1889867 : Blo 1889435 1889867 := bstep (se 1 (by rfl) ⟨1417400, by rfl⟩ : syracuseStep 1889867 = 2834801) B2834801
theorem B2391869 : Blo 1889435 2391869 := bbase (se 3 (by rfl) ⟨448475, by rfl⟩ : syracuseStep 2391869 = 896951) (by norm_num)
theorem B6378317 : Blo 1889435 6378317 := bstep (se 3 (by rfl) ⟨1195934, by rfl⟩ : syracuseStep 6378317 = 2391869) B2391869
theorem B4252211 : Blo 1889435 4252211 := bstep (se 1 (by rfl) ⟨3189158, by rfl⟩ : syracuseStep 4252211 = 6378317) B6378317
theorem B2834807 : Blo 1889435 2834807 := bstep (se 1 (by rfl) ⟨2126105, by rfl⟩ : syracuseStep 2834807 = 4252211) B4252211
theorem B1889871 : Blo 1889435 1889871 := bstep (se 1 (by rfl) ⟨1417403, by rfl⟩ : syracuseStep 1889871 = 2834807) B2834807
theorem B2834813 : Blo 1889435 2834813 := bbase (se 3 (by rfl) ⟨531527, by rfl⟩ : syracuseStep 2834813 = 1063055) (by norm_num)
theorem B1889875 : Blo 1889435 1889875 := bstep (se 1 (by rfl) ⟨1417406, by rfl⟩ : syracuseStep 1889875 = 2834813) B2834813
theorem B4252229 : Blo 1889435 4252229 := bbase (se 4 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 4252229 = 797293) (by norm_num)
theorem B2834819 : Blo 1889435 2834819 := bstep (se 1 (by rfl) ⟨2126114, by rfl⟩ : syracuseStep 2834819 = 4252229) B4252229
theorem B1889879 : Blo 1889435 1889879 := bstep (se 1 (by rfl) ⟨1417409, by rfl⟩ : syracuseStep 1889879 = 2834819) B2834819
theorem B2018153 : Blo 1889435 2018153 := bbase (se 2 (by rfl) ⟨756807, by rfl⟩ : syracuseStep 2018153 = 1513615) (by norm_num)
theorem B5381741 : Blo 1889435 5381741 := bstep (se 3 (by rfl) ⟨1009076, by rfl⟩ : syracuseStep 5381741 = 2018153) B2018153
theorem B3587827 : Blo 1889435 3587827 := bstep (se 1 (by rfl) ⟨2690870, by rfl⟩ : syracuseStep 3587827 = 5381741) B5381741
theorem B4783769 : Blo 1889435 4783769 := bstep (se 2 (by rfl) ⟨1793913, by rfl⟩ : syracuseStep 4783769 = 3587827) B3587827
theorem B3189179 : Blo 1889435 3189179 := bstep (se 1 (by rfl) ⟨2391884, by rfl⟩ : syracuseStep 3189179 = 4783769) B4783769
theorem B2126119 : Blo 1889435 2126119 := bstep (se 1 (by rfl) ⟨1594589, by rfl⟩ : syracuseStep 2126119 = 3189179) B3189179
theorem B2834825 : Blo 1889435 2834825 := bstep (se 2 (by rfl) ⟨1063059, by rfl⟩ : syracuseStep 2834825 = 2126119) B2126119
theorem B1889883 : Blo 1889435 1889883 := bstep (se 1 (by rfl) ⟨1417412, by rfl⟩ : syracuseStep 1889883 = 2834825) B2834825
theorem B9567557 : Blo 1889435 9567557 := bbase (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) (by norm_num)
theorem B6378371 : Blo 1889435 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B4252247 : Blo 1889435 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B2834831 : Blo 1889435 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B1889887 : Blo 1889435 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B2834837 : Blo 1889435 2834837 := bbase (se 6 (by rfl) ⟨66441, by rfl⟩ : syracuseStep 2834837 = 132883) (by norm_num)
theorem B1889891 : Blo 1889435 1889891 := bstep (se 1 (by rfl) ⟨1417418, by rfl⟩ : syracuseStep 1889891 = 2834837) B2834837
theorem B7662725 : Blo 1889435 7662725 := bbase (se 4 (by rfl) ⟨718380, by rfl⟩ : syracuseStep 7662725 = 1436761) (by norm_num)
theorem B5108483 : Blo 1889435 5108483 := bstep (se 1 (by rfl) ⟨3831362, by rfl⟩ : syracuseStep 5108483 = 7662725) B7662725
theorem B3405655 : Blo 1889435 3405655 := bstep (se 1 (by rfl) ⟨2554241, by rfl⟩ : syracuseStep 3405655 = 5108483) B5108483
theorem B4540873 : Blo 1889435 4540873 := bstep (se 2 (by rfl) ⟨1702827, by rfl⟩ : syracuseStep 4540873 = 3405655) B3405655
theorem B6054497 : Blo 1889435 6054497 := bstep (se 2 (by rfl) ⟨2270436, by rfl⟩ : syracuseStep 6054497 = 4540873) B4540873
theorem B4036331 : Blo 1889435 4036331 := bstep (se 1 (by rfl) ⟨3027248, by rfl⟩ : syracuseStep 4036331 = 6054497) B6054497
theorem B10763549 : Blo 1889435 10763549 := bstep (se 3 (by rfl) ⟨2018165, by rfl⟩ : syracuseStep 10763549 = 4036331) B4036331
theorem B7175699 : Blo 1889435 7175699 := bstep (se 1 (by rfl) ⟨5381774, by rfl⟩ : syracuseStep 7175699 = 10763549) B10763549
theorem B4783799 : Blo 1889435 4783799 := bstep (se 1 (by rfl) ⟨3587849, by rfl⟩ : syracuseStep 4783799 = 7175699) B7175699
theorem B3189199 : Blo 1889435 3189199 := bstep (se 1 (by rfl) ⟨2391899, by rfl⟩ : syracuseStep 3189199 = 4783799) B4783799
theorem B4252265 : Blo 1889435 4252265 := bstep (se 2 (by rfl) ⟨1594599, by rfl⟩ : syracuseStep 4252265 = 3189199) B3189199
theorem B2834843 : Blo 1889435 2834843 := bstep (se 1 (by rfl) ⟨2126132, by rfl⟩ : syracuseStep 2834843 = 4252265) B4252265
theorem B1889895 : Blo 1889435 1889895 := bstep (se 1 (by rfl) ⟨1417421, by rfl⟩ : syracuseStep 1889895 = 2834843) B2834843
theorem B2126137 : Blo 1889435 2126137 := bbase (se 2 (by rfl) ⟨797301, by rfl⟩ : syracuseStep 2126137 = 1594603) (by norm_num)
theorem B2834849 : Blo 1889435 2834849 := bstep (se 2 (by rfl) ⟨1063068, by rfl⟩ : syracuseStep 2834849 = 2126137) B2126137
theorem B1889899 : Blo 1889435 1889899 := bstep (se 1 (by rfl) ⟨1417424, by rfl⟩ : syracuseStep 1889899 = 2834849) B2834849
theorem B5381797 : Blo 1889435 5381797 := bbase (se 4 (by rfl) ⟨504543, by rfl⟩ : syracuseStep 5381797 = 1009087) (by norm_num)
theorem B7175729 : Blo 1889435 7175729 := bstep (se 2 (by rfl) ⟨2690898, by rfl⟩ : syracuseStep 7175729 = 5381797) B5381797
theorem B4783819 : Blo 1889435 4783819 := bstep (se 1 (by rfl) ⟨3587864, by rfl⟩ : syracuseStep 4783819 = 7175729) B7175729
theorem B6378425 : Blo 1889435 6378425 := bstep (se 2 (by rfl) ⟨2391909, by rfl⟩ : syracuseStep 6378425 = 4783819) B4783819
theorem B4252283 : Blo 1889435 4252283 := bstep (se 1 (by rfl) ⟨3189212, by rfl⟩ : syracuseStep 4252283 = 6378425) B6378425
theorem B2834855 : Blo 1889435 2834855 := bstep (se 1 (by rfl) ⟨2126141, by rfl⟩ : syracuseStep 2834855 = 4252283) B4252283
theorem B1889903 : Blo 1889435 1889903 := bstep (se 1 (by rfl) ⟨1417427, by rfl⟩ : syracuseStep 1889903 = 2834855) B2834855
theorem B2834861 : Blo 1889435 2834861 := bbase (se 3 (by rfl) ⟨531536, by rfl⟩ : syracuseStep 2834861 = 1063073) (by norm_num)
theorem B1889907 : Blo 1889435 1889907 := bstep (se 1 (by rfl) ⟨1417430, by rfl⟩ : syracuseStep 1889907 = 2834861) B2834861
theorem B4252301 : Blo 1889435 4252301 := bbase (se 3 (by rfl) ⟨797306, by rfl⟩ : syracuseStep 4252301 = 1594613) (by norm_num)
theorem B2834867 : Blo 1889435 2834867 := bstep (se 1 (by rfl) ⟨2126150, by rfl⟩ : syracuseStep 2834867 = 4252301) B4252301
theorem B1889911 : Blo 1889435 1889911 := bstep (se 1 (by rfl) ⟨1417433, by rfl⟩ : syracuseStep 1889911 = 2834867) B2834867
theorem B2391925 : Blo 1889435 2391925 := bbase (se 5 (by rfl) ⟨112121, by rfl⟩ : syracuseStep 2391925 = 224243) (by norm_num)
theorem B3189233 : Blo 1889435 3189233 := bstep (se 2 (by rfl) ⟨1195962, by rfl⟩ : syracuseStep 3189233 = 2391925) B2391925
theorem B2126155 : Blo 1889435 2126155 := bstep (se 1 (by rfl) ⟨1594616, by rfl⟩ : syracuseStep 2126155 = 3189233) B3189233
theorem B2834873 : Blo 1889435 2834873 := bstep (se 2 (by rfl) ⟨1063077, by rfl⟩ : syracuseStep 2834873 = 2126155) B2126155
theorem B1889915 : Blo 1889435 1889915 := bstep (se 1 (by rfl) ⟨1417436, by rfl⟩ : syracuseStep 1889915 = 2834873) B2834873
theorem B1915705 : Blo 1889435 1915705 := bbase (se 2 (by rfl) ⟨718389, by rfl⟩ : syracuseStep 1915705 = 1436779) (by norm_num)
theorem B2554273 : Blo 1889435 2554273 := bstep (se 2 (by rfl) ⟨957852, by rfl⟩ : syracuseStep 2554273 = 1915705) B1915705
theorem B13622789 : Blo 1889435 13622789 := bstep (se 4 (by rfl) ⟨1277136, by rfl⟩ : syracuseStep 13622789 = 2554273) B2554273
theorem B36327437 : Blo 1889435 36327437 := bstep (se 3 (by rfl) ⟨6811394, by rfl⟩ : syracuseStep 36327437 = 13622789) B13622789
theorem B24218291 : Blo 1889435 24218291 := bstep (se 1 (by rfl) ⟨18163718, by rfl⟩ : syracuseStep 24218291 = 36327437) B36327437
theorem B16145527 : Blo 1889435 16145527 := bstep (se 1 (by rfl) ⟨12109145, by rfl⟩ : syracuseStep 16145527 = 24218291) B24218291
theorem B21527369 : Blo 1889435 21527369 := bstep (se 2 (by rfl) ⟨8072763, by rfl⟩ : syracuseStep 21527369 = 16145527) B16145527
theorem B14351579 : Blo 1889435 14351579 := bstep (se 1 (by rfl) ⟨10763684, by rfl⟩ : syracuseStep 14351579 = 21527369) B21527369
theorem B9567719 : Blo 1889435 9567719 := bstep (se 1 (by rfl) ⟨7175789, by rfl⟩ : syracuseStep 9567719 = 14351579) B14351579
theorem B6378479 : Blo 1889435 6378479 := bstep (se 1 (by rfl) ⟨4783859, by rfl⟩ : syracuseStep 6378479 = 9567719) B9567719
theorem B4252319 : Blo 1889435 4252319 := bstep (se 1 (by rfl) ⟨3189239, by rfl⟩ : syracuseStep 4252319 = 6378479) B6378479
theorem B2834879 : Blo 1889435 2834879 := bstep (se 1 (by rfl) ⟨2126159, by rfl⟩ : syracuseStep 2834879 = 4252319) B4252319
theorem B1889919 : Blo 1889435 1889919 := bstep (se 1 (by rfl) ⟨1417439, by rfl⟩ : syracuseStep 1889919 = 2834879) B2834879
theorem B2834885 : Blo 1889435 2834885 := bbase (se 4 (by rfl) ⟨265770, by rfl⟩ : syracuseStep 2834885 = 531541) (by norm_num)
theorem B1889923 : Blo 1889435 1889923 := bstep (se 1 (by rfl) ⟨1417442, by rfl⟩ : syracuseStep 1889923 = 2834885) B2834885
theorem B3189253 : Blo 1889435 3189253 := bbase (se 4 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 3189253 = 597985) (by norm_num)
theorem B4252337 : Blo 1889435 4252337 := bstep (se 2 (by rfl) ⟨1594626, by rfl⟩ : syracuseStep 4252337 = 3189253) B3189253
theorem B2834891 : Blo 1889435 2834891 := bstep (se 1 (by rfl) ⟨2126168, by rfl⟩ : syracuseStep 2834891 = 4252337) B4252337
theorem B1889927 : Blo 1889435 1889927 := bstep (se 1 (by rfl) ⟨1417445, by rfl⟩ : syracuseStep 1889927 = 2834891) B2834891
theorem B2126173 : Blo 1889435 2126173 := bbase (se 3 (by rfl) ⟨398657, by rfl⟩ : syracuseStep 2126173 = 797315) (by norm_num)
theorem B2834897 : Blo 1889435 2834897 := bstep (se 2 (by rfl) ⟨1063086, by rfl⟩ : syracuseStep 2834897 = 2126173) B2126173
theorem B1889931 : Blo 1889435 1889931 := bstep (se 1 (by rfl) ⟨1417448, by rfl⟩ : syracuseStep 1889931 = 2834897) B2834897
theorem B6378533 : Blo 1889435 6378533 := bbase (se 4 (by rfl) ⟨597987, by rfl⟩ : syracuseStep 6378533 = 1195975) (by norm_num)
theorem B4252355 : Blo 1889435 4252355 := bstep (se 1 (by rfl) ⟨3189266, by rfl⟩ : syracuseStep 4252355 = 6378533) B6378533
theorem B2834903 : Blo 1889435 2834903 := bstep (se 1 (by rfl) ⟨2126177, by rfl⟩ : syracuseStep 2834903 = 4252355) B4252355
theorem B1889935 : Blo 1889435 1889935 := bstep (se 1 (by rfl) ⟨1417451, by rfl⟩ : syracuseStep 1889935 = 2834903) B2834903
theorem B2834909 : Blo 1889435 2834909 := bbase (se 3 (by rfl) ⟨531545, by rfl⟩ : syracuseStep 2834909 = 1063091) (by norm_num)
theorem B1889939 : Blo 1889435 1889939 := bstep (se 1 (by rfl) ⟨1417454, by rfl⟩ : syracuseStep 1889939 = 2834909) B2834909
theorem B4252373 : Blo 1889435 4252373 := bbase (se 7 (by rfl) ⟨49832, by rfl⟩ : syracuseStep 4252373 = 99665) (by norm_num)
theorem B2834915 : Blo 1889435 2834915 := bstep (se 1 (by rfl) ⟨2126186, by rfl⟩ : syracuseStep 2834915 = 4252373) B4252373
theorem B1889943 : Blo 1889435 1889943 := bstep (se 1 (by rfl) ⟨1417457, by rfl⟩ : syracuseStep 1889943 = 2834915) B2834915
theorem B8072885 : Blo 1889435 8072885 := bbase (se 5 (by rfl) ⟨378416, by rfl⟩ : syracuseStep 8072885 = 756833) (by norm_num)
theorem B5381923 : Blo 1889435 5381923 := bstep (se 1 (by rfl) ⟨4036442, by rfl⟩ : syracuseStep 5381923 = 8072885) B8072885
theorem B7175897 : Blo 1889435 7175897 := bstep (se 2 (by rfl) ⟨2690961, by rfl⟩ : syracuseStep 7175897 = 5381923) B5381923
theorem B4783931 : Blo 1889435 4783931 := bstep (se 1 (by rfl) ⟨3587948, by rfl⟩ : syracuseStep 4783931 = 7175897) B7175897
theorem B3189287 : Blo 1889435 3189287 := bstep (se 1 (by rfl) ⟨2391965, by rfl⟩ : syracuseStep 3189287 = 4783931) B4783931
theorem B2126191 : Blo 1889435 2126191 := bstep (se 1 (by rfl) ⟨1594643, by rfl⟩ : syracuseStep 2126191 = 3189287) B3189287
theorem B2834921 : Blo 1889435 2834921 := bstep (se 2 (by rfl) ⟨1063095, by rfl⟩ : syracuseStep 2834921 = 2126191) B2126191
theorem B1889947 : Blo 1889435 1889947 := bstep (se 1 (by rfl) ⟨1417460, by rfl⟩ : syracuseStep 1889947 = 2834921) B2834921
theorem B30651797 : Blo 1889435 30651797 := bbase (se 6 (by rfl) ⟨718401, by rfl⟩ : syracuseStep 30651797 = 1436803) (by norm_num)
theorem B20434531 : Blo 1889435 20434531 := bstep (se 1 (by rfl) ⟨15325898, by rfl⟩ : syracuseStep 20434531 = 30651797) B30651797
theorem B27246041 : Blo 1889435 27246041 := bstep (se 2 (by rfl) ⟨10217265, by rfl⟩ : syracuseStep 27246041 = 20434531) B20434531
theorem B18164027 : Blo 1889435 18164027 := bstep (se 1 (by rfl) ⟨13623020, by rfl⟩ : syracuseStep 18164027 = 27246041) B27246041
theorem B12109351 : Blo 1889435 12109351 := bstep (se 1 (by rfl) ⟨9082013, by rfl⟩ : syracuseStep 12109351 = 18164027) B18164027
theorem B16145801 : Blo 1889435 16145801 := bstep (se 2 (by rfl) ⟨6054675, by rfl⟩ : syracuseStep 16145801 = 12109351) B12109351
theorem B10763867 : Blo 1889435 10763867 := bstep (se 1 (by rfl) ⟨8072900, by rfl⟩ : syracuseStep 10763867 = 16145801) B16145801
theorem B7175911 : Blo 1889435 7175911 := bstep (se 1 (by rfl) ⟨5381933, by rfl⟩ : syracuseStep 7175911 = 10763867) B10763867
theorem B9567881 : Blo 1889435 9567881 := bstep (se 2 (by rfl) ⟨3587955, by rfl⟩ : syracuseStep 9567881 = 7175911) B7175911
theorem B6378587 : Blo 1889435 6378587 := bstep (se 1 (by rfl) ⟨4783940, by rfl⟩ : syracuseStep 6378587 = 9567881) B9567881
theorem B4252391 : Blo 1889435 4252391 := bstep (se 1 (by rfl) ⟨3189293, by rfl⟩ : syracuseStep 4252391 = 6378587) B6378587
theorem B2834927 : Blo 1889435 2834927 := bstep (se 1 (by rfl) ⟨2126195, by rfl⟩ : syracuseStep 2834927 = 4252391) B4252391
theorem B1889951 : Blo 1889435 1889951 := bstep (se 1 (by rfl) ⟨1417463, by rfl⟩ : syracuseStep 1889951 = 2834927) B2834927
theorem B2834933 : Blo 1889435 2834933 := bbase (se 5 (by rfl) ⟨132887, by rfl⟩ : syracuseStep 2834933 = 265775) (by norm_num)
theorem B1889955 : Blo 1889435 1889955 := bstep (se 1 (by rfl) ⟨1417466, by rfl⟩ : syracuseStep 1889955 = 2834933) B2834933
theorem B5381957 : Blo 1889435 5381957 := bbase (se 4 (by rfl) ⟨504558, by rfl⟩ : syracuseStep 5381957 = 1009117) (by norm_num)
theorem B3587971 : Blo 1889435 3587971 := bstep (se 1 (by rfl) ⟨2690978, by rfl⟩ : syracuseStep 3587971 = 5381957) B5381957
theorem B4783961 : Blo 1889435 4783961 := bstep (se 2 (by rfl) ⟨1793985, by rfl⟩ : syracuseStep 4783961 = 3587971) B3587971
theorem B3189307 : Blo 1889435 3189307 := bstep (se 1 (by rfl) ⟨2391980, by rfl⟩ : syracuseStep 3189307 = 4783961) B4783961
theorem B4252409 : Blo 1889435 4252409 := bstep (se 2 (by rfl) ⟨1594653, by rfl⟩ : syracuseStep 4252409 = 3189307) B3189307
theorem B2834939 : Blo 1889435 2834939 := bstep (se 1 (by rfl) ⟨2126204, by rfl⟩ : syracuseStep 2834939 = 4252409) B4252409
theorem B1889959 : Blo 1889435 1889959 := bstep (se 1 (by rfl) ⟨1417469, by rfl⟩ : syracuseStep 1889959 = 2834939) B2834939
theorem B2126209 : Blo 1889435 2126209 := bbase (se 2 (by rfl) ⟨797328, by rfl⟩ : syracuseStep 2126209 = 1594657) (by norm_num)
theorem B2834945 : Blo 1889435 2834945 := bstep (se 2 (by rfl) ⟨1063104, by rfl⟩ : syracuseStep 2834945 = 2126209) B2126209
theorem B1889963 : Blo 1889435 1889963 := bstep (se 1 (by rfl) ⟨1417472, by rfl⟩ : syracuseStep 1889963 = 2834945) B2834945
theorem B4783981 : Blo 1889435 4783981 := bbase (se 3 (by rfl) ⟨896996, by rfl⟩ : syracuseStep 4783981 = 1793993) (by norm_num)
theorem B6378641 : Blo 1889435 6378641 := bstep (se 2 (by rfl) ⟨2391990, by rfl⟩ : syracuseStep 6378641 = 4783981) B4783981
theorem B4252427 : Blo 1889435 4252427 := bstep (se 1 (by rfl) ⟨3189320, by rfl⟩ : syracuseStep 4252427 = 6378641) B6378641
theorem B2834951 : Blo 1889435 2834951 := bstep (se 1 (by rfl) ⟨2126213, by rfl⟩ : syracuseStep 2834951 = 4252427) B4252427
theorem B1889967 : Blo 1889435 1889967 := bstep (se 1 (by rfl) ⟨1417475, by rfl⟩ : syracuseStep 1889967 = 2834951) B2834951
theorem B2834957 : Blo 1889435 2834957 := bbase (se 3 (by rfl) ⟨531554, by rfl⟩ : syracuseStep 2834957 = 1063109) (by norm_num)
theorem B1889971 : Blo 1889435 1889971 := bstep (se 1 (by rfl) ⟨1417478, by rfl⟩ : syracuseStep 1889971 = 2834957) B2834957
theorem B4252445 : Blo 1889435 4252445 := bbase (se 3 (by rfl) ⟨797333, by rfl⟩ : syracuseStep 4252445 = 1594667) (by norm_num)
theorem B2834963 : Blo 1889435 2834963 := bstep (se 1 (by rfl) ⟨2126222, by rfl⟩ : syracuseStep 2834963 = 4252445) B4252445
theorem B1889975 : Blo 1889435 1889975 := bstep (se 1 (by rfl) ⟨1417481, by rfl⟩ : syracuseStep 1889975 = 2834963) B2834963
theorem B3189341 : Blo 1889435 3189341 := bbase (se 3 (by rfl) ⟨598001, by rfl⟩ : syracuseStep 3189341 = 1196003) (by norm_num)
theorem B2126227 : Blo 1889435 2126227 := bstep (se 1 (by rfl) ⟨1594670, by rfl⟩ : syracuseStep 2126227 = 3189341) B3189341
theorem B2834969 : Blo 1889435 2834969 := bstep (se 2 (by rfl) ⟨1063113, by rfl⟩ : syracuseStep 2834969 = 2126227) B2126227
theorem B1889979 : Blo 1889435 1889979 := bstep (se 1 (by rfl) ⟨1417484, by rfl⟩ : syracuseStep 1889979 = 2834969) B2834969
theorem B3027389 : Blo 1889435 3027389 := bbase (se 3 (by rfl) ⟨567635, by rfl⟩ : syracuseStep 3027389 = 1135271) (by norm_num)
theorem B8073037 : Blo 1889435 8073037 := bstep (se 3 (by rfl) ⟨1513694, by rfl⟩ : syracuseStep 8073037 = 3027389) B3027389
theorem B10764049 : Blo 1889435 10764049 := bstep (se 2 (by rfl) ⟨4036518, by rfl⟩ : syracuseStep 10764049 = 8073037) B8073037
theorem B14352065 : Blo 1889435 14352065 := bstep (se 2 (by rfl) ⟨5382024, by rfl⟩ : syracuseStep 14352065 = 10764049) B10764049
theorem B9568043 : Blo 1889435 9568043 := bstep (se 1 (by rfl) ⟨7176032, by rfl⟩ : syracuseStep 9568043 = 14352065) B14352065
theorem B6378695 : Blo 1889435 6378695 := bstep (se 1 (by rfl) ⟨4784021, by rfl⟩ : syracuseStep 6378695 = 9568043) B9568043
theorem B4252463 : Blo 1889435 4252463 := bstep (se 1 (by rfl) ⟨3189347, by rfl⟩ : syracuseStep 4252463 = 6378695) B6378695
theorem B2834975 : Blo 1889435 2834975 := bstep (se 1 (by rfl) ⟨2126231, by rfl⟩ : syracuseStep 2834975 = 4252463) B4252463
theorem B1889983 : Blo 1889435 1889983 := bstep (se 1 (by rfl) ⟨1417487, by rfl⟩ : syracuseStep 1889983 = 2834975) B2834975
theorem B2834981 : Blo 1889435 2834981 := bbase (se 4 (by rfl) ⟨265779, by rfl⟩ : syracuseStep 2834981 = 531559) (by norm_num)
theorem B1889987 : Blo 1889435 1889987 := bstep (se 1 (by rfl) ⟨1417490, by rfl⟩ : syracuseStep 1889987 = 2834981) B2834981
theorem B2392021 : Blo 1889435 2392021 := bbase (se 7 (by rfl) ⟨28031, by rfl⟩ : syracuseStep 2392021 = 56063) (by norm_num)
theorem B3189361 : Blo 1889435 3189361 := bstep (se 2 (by rfl) ⟨1196010, by rfl⟩ : syracuseStep 3189361 = 2392021) B2392021
theorem B4252481 : Blo 1889435 4252481 := bstep (se 2 (by rfl) ⟨1594680, by rfl⟩ : syracuseStep 4252481 = 3189361) B3189361
theorem B2834987 : Blo 1889435 2834987 := bstep (se 1 (by rfl) ⟨2126240, by rfl⟩ : syracuseStep 2834987 = 4252481) B4252481
theorem B1889991 : Blo 1889435 1889991 := bstep (se 1 (by rfl) ⟨1417493, by rfl⟩ : syracuseStep 1889991 = 2834987) B2834987
theorem B2126245 : Blo 1889435 2126245 := bbase (se 4 (by rfl) ⟨199335, by rfl⟩ : syracuseStep 2126245 = 398671) (by norm_num)
theorem B2834993 : Blo 1889435 2834993 := bstep (se 2 (by rfl) ⟨1063122, by rfl⟩ : syracuseStep 2834993 = 2126245) B2126245
theorem B1889995 : Blo 1889435 1889995 := bstep (se 1 (by rfl) ⟨1417496, by rfl⟩ : syracuseStep 1889995 = 2834993) B2834993
theorem B6811685 : Blo 1889435 6811685 := bbase (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) (by norm_num)
theorem B4541123 : Blo 1889435 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B12109661 : Blo 1889435 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B8073107 : Blo 1889435 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B5382071 : Blo 1889435 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B3588047 : Blo 1889435 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B2392031 : Blo 1889435 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6378749 : Blo 1889435 6378749 := bstep (se 3 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 6378749 = 2392031) B2392031
theorem B4252499 : Blo 1889435 4252499 := bstep (se 1 (by rfl) ⟨3189374, by rfl⟩ : syracuseStep 4252499 = 6378749) B6378749
theorem B2834999 : Blo 1889435 2834999 := bstep (se 1 (by rfl) ⟨2126249, by rfl⟩ : syracuseStep 2834999 = 4252499) B4252499
theorem B1889999 : Blo 1889435 1889999 := bstep (se 1 (by rfl) ⟨1417499, by rfl⟩ : syracuseStep 1889999 = 2834999) B2834999
theorem B2835005 : Blo 1889435 2835005 := bbase (se 3 (by rfl) ⟨531563, by rfl⟩ : syracuseStep 2835005 = 1063127) (by norm_num)
theorem B1890003 : Blo 1889435 1890003 := bstep (se 1 (by rfl) ⟨1417502, by rfl⟩ : syracuseStep 1890003 = 2835005) B2835005
theorem B4252517 : Blo 1889435 4252517 := bbase (se 4 (by rfl) ⟨398673, by rfl⟩ : syracuseStep 4252517 = 797347) (by norm_num)
theorem B2835011 : Blo 1889435 2835011 := bstep (se 1 (by rfl) ⟨2126258, by rfl⟩ : syracuseStep 2835011 = 4252517) B4252517
theorem B1890007 : Blo 1889435 1890007 := bstep (se 1 (by rfl) ⟨1417505, by rfl⟩ : syracuseStep 1890007 = 2835011) B2835011
theorem B4784093 : Blo 1889435 4784093 := bbase (se 3 (by rfl) ⟨897017, by rfl⟩ : syracuseStep 4784093 = 1794035) (by norm_num)
theorem B3189395 : Blo 1889435 3189395 := bstep (se 1 (by rfl) ⟨2392046, by rfl⟩ : syracuseStep 3189395 = 4784093) B4784093
theorem B2126263 : Blo 1889435 2126263 := bstep (se 1 (by rfl) ⟨1594697, by rfl⟩ : syracuseStep 2126263 = 3189395) B3189395
theorem B2835017 : Blo 1889435 2835017 := bstep (se 2 (by rfl) ⟨1063131, by rfl⟩ : syracuseStep 2835017 = 2126263) B2126263
theorem B1890011 : Blo 1889435 1890011 := bstep (se 1 (by rfl) ⟨1417508, by rfl⟩ : syracuseStep 1890011 = 2835017) B2835017
theorem B3588077 : Blo 1889435 3588077 := bbase (se 3 (by rfl) ⟨672764, by rfl⟩ : syracuseStep 3588077 = 1345529) (by norm_num)
theorem B9568205 : Blo 1889435 9568205 := bstep (se 3 (by rfl) ⟨1794038, by rfl⟩ : syracuseStep 9568205 = 3588077) B3588077
theorem B6378803 : Blo 1889435 6378803 := bstep (se 1 (by rfl) ⟨4784102, by rfl⟩ : syracuseStep 6378803 = 9568205) B9568205
theorem B4252535 : Blo 1889435 4252535 := bstep (se 1 (by rfl) ⟨3189401, by rfl⟩ : syracuseStep 4252535 = 6378803) B6378803
theorem B2835023 : Blo 1889435 2835023 := bstep (se 1 (by rfl) ⟨2126267, by rfl⟩ : syracuseStep 2835023 = 4252535) B4252535
theorem B1890015 : Blo 1889435 1890015 := bstep (se 1 (by rfl) ⟨1417511, by rfl⟩ : syracuseStep 1890015 = 2835023) B2835023
theorem B2835029 : Blo 1889435 2835029 := bbase (se 8 (by rfl) ⟨16611, by rfl⟩ : syracuseStep 2835029 = 33223) (by norm_num)
theorem B1890019 : Blo 1889435 1890019 := bstep (se 1 (by rfl) ⟨1417514, by rfl⟩ : syracuseStep 1890019 = 2835029) B2835029
theorem B4849397 : Blo 1889435 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B3232931 : Blo 1889435 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B8621149 : Blo 1889435 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B11494865 : Blo 1889435 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B7663243 : Blo 1889435 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B10217657 : Blo 1889435 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B6811771 : Blo 1889435 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B9082361 : Blo 1889435 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B6054907 : Blo 1889435 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B8073209 : Blo 1889435 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B5382139 : Blo 1889435 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B7176185 : Blo 1889435 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B4784123 : Blo 1889435 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B3189415 : Blo 1889435 3189415 := bstep (se 1 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 3189415 = 4784123) B4784123
theorem B4252553 : Blo 1889435 4252553 := bstep (se 2 (by rfl) ⟨1594707, by rfl⟩ : syracuseStep 4252553 = 3189415) B3189415
theorem B2835035 : Blo 1889435 2835035 := bstep (se 1 (by rfl) ⟨2126276, by rfl⟩ : syracuseStep 2835035 = 4252553) B4252553
theorem B1890023 : Blo 1889435 1890023 := bstep (se 1 (by rfl) ⟨1417517, by rfl⟩ : syracuseStep 1890023 = 2835035) B2835035
theorem B2126281 : Blo 1889435 2126281 := bbase (se 2 (by rfl) ⟨797355, by rfl⟩ : syracuseStep 2126281 = 1594711) (by norm_num)
theorem B2835041 : Blo 1889435 2835041 := bstep (se 2 (by rfl) ⟨1063140, by rfl⟩ : syracuseStep 2835041 = 2126281) B2126281
theorem B1890027 : Blo 1889435 1890027 := bstep (se 1 (by rfl) ⟨1417520, by rfl⟩ : syracuseStep 1890027 = 2835041) B2835041
theorem B16146485 : Blo 1889435 16146485 := bbase (se 5 (by rfl) ⟨756866, by rfl⟩ : syracuseStep 16146485 = 1513733) (by norm_num)
theorem B10764323 : Blo 1889435 10764323 := bstep (se 1 (by rfl) ⟨8073242, by rfl⟩ : syracuseStep 10764323 = 16146485) B16146485
theorem B7176215 : Blo 1889435 7176215 := bstep (se 1 (by rfl) ⟨5382161, by rfl⟩ : syracuseStep 7176215 = 10764323) B10764323
theorem B4784143 : Blo 1889435 4784143 := bstep (se 1 (by rfl) ⟨3588107, by rfl⟩ : syracuseStep 4784143 = 7176215) B7176215
theorem B6378857 : Blo 1889435 6378857 := bstep (se 2 (by rfl) ⟨2392071, by rfl⟩ : syracuseStep 6378857 = 4784143) B4784143
theorem B4252571 : Blo 1889435 4252571 := bstep (se 1 (by rfl) ⟨3189428, by rfl⟩ : syracuseStep 4252571 = 6378857) B6378857
theorem B2835047 : Blo 1889435 2835047 := bstep (se 1 (by rfl) ⟨2126285, by rfl⟩ : syracuseStep 2835047 = 4252571) B4252571
theorem B1890031 : Blo 1889435 1890031 := bstep (se 1 (by rfl) ⟨1417523, by rfl⟩ : syracuseStep 1890031 = 2835047) B2835047
theorem B2835053 : Blo 1889435 2835053 := bbase (se 3 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 2835053 = 1063145) (by norm_num)
theorem B1890035 : Blo 1889435 1890035 := bstep (se 1 (by rfl) ⟨1417526, by rfl⟩ : syracuseStep 1890035 = 2835053) B2835053
theorem B4252589 : Blo 1889435 4252589 := bbase (se 3 (by rfl) ⟨797360, by rfl⟩ : syracuseStep 4252589 = 1594721) (by norm_num)
theorem B2835059 : Blo 1889435 2835059 := bstep (se 1 (by rfl) ⟨2126294, by rfl⟩ : syracuseStep 2835059 = 4252589) B4252589
theorem B1890039 : Blo 1889435 1890039 := bstep (se 1 (by rfl) ⟨1417529, by rfl⟩ : syracuseStep 1890039 = 2835059) B2835059
theorem B5382197 : Blo 1889435 5382197 := bbase (se 5 (by rfl) ⟨252290, by rfl⟩ : syracuseStep 5382197 = 504581) (by norm_num)
theorem B3588131 : Blo 1889435 3588131 := bstep (se 1 (by rfl) ⟨2691098, by rfl⟩ : syracuseStep 3588131 = 5382197) B5382197
theorem B2392087 : Blo 1889435 2392087 := bstep (se 1 (by rfl) ⟨1794065, by rfl⟩ : syracuseStep 2392087 = 3588131) B3588131
theorem B3189449 : Blo 1889435 3189449 := bstep (se 2 (by rfl) ⟨1196043, by rfl⟩ : syracuseStep 3189449 = 2392087) B2392087
theorem B2126299 : Blo 1889435 2126299 := bstep (se 1 (by rfl) ⟨1594724, by rfl⟩ : syracuseStep 2126299 = 3189449) B3189449
theorem B2835065 : Blo 1889435 2835065 := bstep (se 2 (by rfl) ⟨1063149, by rfl⟩ : syracuseStep 2835065 = 2126299) B2126299
theorem B1890043 : Blo 1889435 1890043 := bstep (se 1 (by rfl) ⟨1417532, by rfl⟩ : syracuseStep 1890043 = 2835065) B2835065
theorem B7767893 : Blo 1889435 7767893 := bbase (se 9 (by rfl) ⟨22757, by rfl⟩ : syracuseStep 7767893 = 45515) (by norm_num)
theorem B5178595 : Blo 1889435 5178595 := bstep (se 1 (by rfl) ⟨3883946, by rfl⟩ : syracuseStep 5178595 = 7767893) B7767893
theorem B6904793 : Blo 1889435 6904793 := bstep (se 2 (by rfl) ⟨2589297, by rfl⟩ : syracuseStep 6904793 = 5178595) B5178595
theorem B4603195 : Blo 1889435 4603195 := bstep (se 1 (by rfl) ⟨3452396, by rfl⟩ : syracuseStep 4603195 = 6904793) B6904793
theorem B6137593 : Blo 1889435 6137593 := bstep (se 2 (by rfl) ⟨2301597, by rfl⟩ : syracuseStep 6137593 = 4603195) B4603195
theorem B32733829 : Blo 1889435 32733829 := bstep (se 4 (by rfl) ⟨3068796, by rfl⟩ : syracuseStep 32733829 = 6137593) B6137593
theorem B43645105 : Blo 1889435 43645105 := bstep (se 2 (by rfl) ⟨16366914, by rfl⟩ : syracuseStep 43645105 = 32733829) B32733829
theorem B58193473 : Blo 1889435 58193473 := bstep (se 2 (by rfl) ⟨21822552, by rfl⟩ : syracuseStep 58193473 = 43645105) B43645105
theorem B77591297 : Blo 1889435 77591297 := bstep (se 2 (by rfl) ⟨29096736, by rfl⟩ : syracuseStep 77591297 = 58193473) B58193473
theorem B206910125 : Blo 1889435 206910125 := bstep (se 3 (by rfl) ⟨38795648, by rfl⟩ : syracuseStep 206910125 = 77591297) B77591297
theorem B137940083 : Blo 1889435 137940083 := bstep (se 1 (by rfl) ⟨103455062, by rfl⟩ : syracuseStep 137940083 = 206910125) B206910125
theorem B91960055 : Blo 1889435 91960055 := bstep (se 1 (by rfl) ⟨68970041, by rfl⟩ : syracuseStep 91960055 = 137940083) B137940083
theorem B61306703 : Blo 1889435 61306703 := bstep (se 1 (by rfl) ⟨45980027, by rfl⟩ : syracuseStep 61306703 = 91960055) B91960055
theorem B40871135 : Blo 1889435 40871135 := bstep (se 1 (by rfl) ⟨30653351, by rfl⟩ : syracuseStep 40871135 = 61306703) B61306703
theorem B27247423 : Blo 1889435 27247423 := bstep (se 1 (by rfl) ⟨20435567, by rfl⟩ : syracuseStep 27247423 = 40871135) B40871135
theorem B36329897 : Blo 1889435 36329897 := bstep (se 2 (by rfl) ⟨13623711, by rfl⟩ : syracuseStep 36329897 = 27247423) B27247423
theorem B24219931 : Blo 1889435 24219931 := bstep (se 1 (by rfl) ⟨18164948, by rfl⟩ : syracuseStep 24219931 = 36329897) B36329897
theorem B32293241 : Blo 1889435 32293241 := bstep (se 2 (by rfl) ⟨12109965, by rfl⟩ : syracuseStep 32293241 = 24219931) B24219931
theorem B21528827 : Blo 1889435 21528827 := bstep (se 1 (by rfl) ⟨16146620, by rfl⟩ : syracuseStep 21528827 = 32293241) B32293241
theorem B14352551 : Blo 1889435 14352551 := bstep (se 1 (by rfl) ⟨10764413, by rfl⟩ : syracuseStep 14352551 = 21528827) B21528827
theorem B9568367 : Blo 1889435 9568367 := bstep (se 1 (by rfl) ⟨7176275, by rfl⟩ : syracuseStep 9568367 = 14352551) B14352551
theorem B6378911 : Blo 1889435 6378911 := bstep (se 1 (by rfl) ⟨4784183, by rfl⟩ : syracuseStep 6378911 = 9568367) B9568367
theorem B4252607 : Blo 1889435 4252607 := bstep (se 1 (by rfl) ⟨3189455, by rfl⟩ : syracuseStep 4252607 = 6378911) B6378911
theorem B2835071 : Blo 1889435 2835071 := bstep (se 1 (by rfl) ⟨2126303, by rfl⟩ : syracuseStep 2835071 = 4252607) B4252607
theorem B1890047 : Blo 1889435 1890047 := bstep (se 1 (by rfl) ⟨1417535, by rfl⟩ : syracuseStep 1890047 = 2835071) B2835071
theorem B2835077 : Blo 1889435 2835077 := bbase (se 4 (by rfl) ⟨265788, by rfl⟩ : syracuseStep 2835077 = 531577) (by norm_num)
theorem B1890051 : Blo 1889435 1890051 := bstep (se 1 (by rfl) ⟨1417538, by rfl⟩ : syracuseStep 1890051 = 2835077) B2835077
theorem B3189469 : Blo 1889435 3189469 := bbase (se 3 (by rfl) ⟨598025, by rfl⟩ : syracuseStep 3189469 = 1196051) (by norm_num)
theorem B4252625 : Blo 1889435 4252625 := bstep (se 2 (by rfl) ⟨1594734, by rfl⟩ : syracuseStep 4252625 = 3189469) B3189469
theorem B2835083 : Blo 1889435 2835083 := bstep (se 1 (by rfl) ⟨2126312, by rfl⟩ : syracuseStep 2835083 = 4252625) B4252625
theorem B1890055 : Blo 1889435 1890055 := bstep (se 1 (by rfl) ⟨1417541, by rfl⟩ : syracuseStep 1890055 = 2835083) B2835083
theorem B2126317 : Blo 1889435 2126317 := bbase (se 3 (by rfl) ⟨398684, by rfl⟩ : syracuseStep 2126317 = 797369) (by norm_num)
theorem B2835089 : Blo 1889435 2835089 := bstep (se 2 (by rfl) ⟨1063158, by rfl⟩ : syracuseStep 2835089 = 2126317) B2126317
theorem B1890059 : Blo 1889435 1890059 := bstep (se 1 (by rfl) ⟨1417544, by rfl⟩ : syracuseStep 1890059 = 2835089) B2835089
theorem B6378965 : Blo 1889435 6378965 := bbase (se 7 (by rfl) ⟨74753, by rfl⟩ : syracuseStep 6378965 = 149507) (by norm_num)
theorem B4252643 : Blo 1889435 4252643 := bstep (se 1 (by rfl) ⟨3189482, by rfl⟩ : syracuseStep 4252643 = 6378965) B6378965
theorem B2835095 : Blo 1889435 2835095 := bstep (se 1 (by rfl) ⟨2126321, by rfl⟩ : syracuseStep 2835095 = 4252643) B4252643
theorem B1890063 : Blo 1889435 1890063 := bstep (se 1 (by rfl) ⟨1417547, by rfl⟩ : syracuseStep 1890063 = 2835095) B2835095
theorem B2835101 : Blo 1889435 2835101 := bbase (se 3 (by rfl) ⟨531581, by rfl⟩ : syracuseStep 2835101 = 1063163) (by norm_num)
theorem B1890067 : Blo 1889435 1890067 := bstep (se 1 (by rfl) ⟨1417550, by rfl⟩ : syracuseStep 1890067 = 2835101) B2835101
theorem B4252661 : Blo 1889435 4252661 := bbase (se 5 (by rfl) ⟨199343, by rfl⟩ : syracuseStep 4252661 = 398687) (by norm_num)
theorem B2835107 : Blo 1889435 2835107 := bstep (se 1 (by rfl) ⟨2126330, by rfl⟩ : syracuseStep 2835107 = 4252661) B4252661
theorem B1890071 : Blo 1889435 1890071 := bstep (se 1 (by rfl) ⟨1417553, by rfl⟩ : syracuseStep 1890071 = 2835107) B2835107
theorem B4310693 : Blo 1889435 4310693 := bbase (se 4 (by rfl) ⟨404127, by rfl⟩ : syracuseStep 4310693 = 808255) (by norm_num)
theorem B2873795 : Blo 1889435 2873795 := bstep (se 1 (by rfl) ⟨2155346, by rfl⟩ : syracuseStep 2873795 = 4310693) B4310693
theorem B7663453 : Blo 1889435 7663453 := bstep (se 3 (by rfl) ⟨1436897, by rfl⟩ : syracuseStep 7663453 = 2873795) B2873795
theorem B40871749 : Blo 1889435 40871749 := bstep (se 4 (by rfl) ⟨3831726, by rfl⟩ : syracuseStep 40871749 = 7663453) B7663453
theorem B54495665 : Blo 1889435 54495665 := bstep (se 2 (by rfl) ⟨20435874, by rfl⟩ : syracuseStep 54495665 = 40871749) B40871749
theorem B36330443 : Blo 1889435 36330443 := bstep (se 1 (by rfl) ⟨27247832, by rfl⟩ : syracuseStep 36330443 = 54495665) B54495665
theorem B24220295 : Blo 1889435 24220295 := bstep (se 1 (by rfl) ⟨18165221, by rfl⟩ : syracuseStep 24220295 = 36330443) B36330443
theorem B16146863 : Blo 1889435 16146863 := bstep (se 1 (by rfl) ⟨12110147, by rfl⟩ : syracuseStep 16146863 = 24220295) B24220295
theorem B10764575 : Blo 1889435 10764575 := bstep (se 1 (by rfl) ⟨8073431, by rfl⟩ : syracuseStep 10764575 = 16146863) B16146863
theorem B7176383 : Blo 1889435 7176383 := bstep (se 1 (by rfl) ⟨5382287, by rfl⟩ : syracuseStep 7176383 = 10764575) B10764575
theorem B4784255 : Blo 1889435 4784255 := bstep (se 1 (by rfl) ⟨3588191, by rfl⟩ : syracuseStep 4784255 = 7176383) B7176383
theorem B3189503 : Blo 1889435 3189503 := bstep (se 1 (by rfl) ⟨2392127, by rfl⟩ : syracuseStep 3189503 = 4784255) B4784255
theorem B2126335 : Blo 1889435 2126335 := bstep (se 1 (by rfl) ⟨1594751, by rfl⟩ : syracuseStep 2126335 = 3189503) B3189503
theorem B2835113 : Blo 1889435 2835113 := bstep (se 2 (by rfl) ⟨1063167, by rfl⟩ : syracuseStep 2835113 = 2126335) B2126335
theorem B1890075 : Blo 1889435 1890075 := bstep (se 1 (by rfl) ⟨1417556, by rfl⟩ : syracuseStep 1890075 = 2835113) B2835113
theorem B2691149 : Blo 1889435 2691149 := bbase (se 3 (by rfl) ⟨504590, by rfl⟩ : syracuseStep 2691149 = 1009181) (by norm_num)
theorem B7176397 : Blo 1889435 7176397 := bstep (se 3 (by rfl) ⟨1345574, by rfl⟩ : syracuseStep 7176397 = 2691149) B2691149
theorem B9568529 : Blo 1889435 9568529 := bstep (se 2 (by rfl) ⟨3588198, by rfl⟩ : syracuseStep 9568529 = 7176397) B7176397
theorem B6379019 : Blo 1889435 6379019 := bstep (se 1 (by rfl) ⟨4784264, by rfl⟩ : syracuseStep 6379019 = 9568529) B9568529
theorem B4252679 : Blo 1889435 4252679 := bstep (se 1 (by rfl) ⟨3189509, by rfl⟩ : syracuseStep 4252679 = 6379019) B6379019
theorem B2835119 : Blo 1889435 2835119 := bstep (se 1 (by rfl) ⟨2126339, by rfl⟩ : syracuseStep 2835119 = 4252679) B4252679
theorem B1890079 : Blo 1889435 1890079 := bstep (se 1 (by rfl) ⟨1417559, by rfl⟩ : syracuseStep 1890079 = 2835119) B2835119
theorem B2835125 : Blo 1889435 2835125 := bbase (se 5 (by rfl) ⟨132896, by rfl⟩ : syracuseStep 2835125 = 265793) (by norm_num)
theorem B1890083 : Blo 1889435 1890083 := bstep (se 1 (by rfl) ⟨1417562, by rfl⟩ : syracuseStep 1890083 = 2835125) B2835125
theorem B4784285 : Blo 1889435 4784285 := bbase (se 3 (by rfl) ⟨897053, by rfl⟩ : syracuseStep 4784285 = 1794107) (by norm_num)
theorem B3189523 : Blo 1889435 3189523 := bstep (se 1 (by rfl) ⟨2392142, by rfl⟩ : syracuseStep 3189523 = 4784285) B4784285
theorem B4252697 : Blo 1889435 4252697 := bstep (se 2 (by rfl) ⟨1594761, by rfl⟩ : syracuseStep 4252697 = 3189523) B3189523
theorem B2835131 : Blo 1889435 2835131 := bstep (se 1 (by rfl) ⟨2126348, by rfl⟩ : syracuseStep 2835131 = 4252697) B4252697
theorem B1890087 : Blo 1889435 1890087 := bstep (se 1 (by rfl) ⟨1417565, by rfl⟩ : syracuseStep 1890087 = 2835131) B2835131
theorem B2126353 : Blo 1889435 2126353 := bbase (se 2 (by rfl) ⟨797382, by rfl⟩ : syracuseStep 2126353 = 1594765) (by norm_num)
theorem B2835137 : Blo 1889435 2835137 := bstep (se 2 (by rfl) ⟨1063176, by rfl⟩ : syracuseStep 2835137 = 2126353) B2126353
theorem B1890091 : Blo 1889435 1890091 := bstep (se 1 (by rfl) ⟨1417568, by rfl⟩ : syracuseStep 1890091 = 2835137) B2835137
theorem B3588229 : Blo 1889435 3588229 := bbase (se 4 (by rfl) ⟨336396, by rfl⟩ : syracuseStep 3588229 = 672793) (by norm_num)
theorem B4784305 : Blo 1889435 4784305 := bstep (se 2 (by rfl) ⟨1794114, by rfl⟩ : syracuseStep 4784305 = 3588229) B3588229
theorem B6379073 : Blo 1889435 6379073 := bstep (se 2 (by rfl) ⟨2392152, by rfl⟩ : syracuseStep 6379073 = 4784305) B4784305
theorem B4252715 : Blo 1889435 4252715 := bstep (se 1 (by rfl) ⟨3189536, by rfl⟩ : syracuseStep 4252715 = 6379073) B6379073
theorem B2835143 : Blo 1889435 2835143 := bstep (se 1 (by rfl) ⟨2126357, by rfl⟩ : syracuseStep 2835143 = 4252715) B4252715
theorem B1890095 : Blo 1889435 1890095 := bstep (se 1 (by rfl) ⟨1417571, by rfl⟩ : syracuseStep 1890095 = 2835143) B2835143
theorem B2835149 : Blo 1889435 2835149 := bbase (se 3 (by rfl) ⟨531590, by rfl⟩ : syracuseStep 2835149 = 1063181) (by norm_num)
theorem B1890099 : Blo 1889435 1890099 := bstep (se 1 (by rfl) ⟨1417574, by rfl⟩ : syracuseStep 1890099 = 2835149) B2835149
theorem B4252733 : Blo 1889435 4252733 := bbase (se 3 (by rfl) ⟨797387, by rfl⟩ : syracuseStep 4252733 = 1594775) (by norm_num)
theorem B2835155 : Blo 1889435 2835155 := bstep (se 1 (by rfl) ⟨2126366, by rfl⟩ : syracuseStep 2835155 = 4252733) B4252733
theorem B1890103 : Blo 1889435 1890103 := bstep (se 1 (by rfl) ⟨1417577, by rfl⟩ : syracuseStep 1890103 = 2835155) B2835155
theorem B3189557 : Blo 1889435 3189557 := bbase (se 5 (by rfl) ⟨149510, by rfl⟩ : syracuseStep 3189557 = 299021) (by norm_num)
theorem B2126371 : Blo 1889435 2126371 := bstep (se 1 (by rfl) ⟨1594778, by rfl⟩ : syracuseStep 2126371 = 3189557) B3189557
theorem B2835161 : Blo 1889435 2835161 := bstep (se 2 (by rfl) ⟨1063185, by rfl⟩ : syracuseStep 2835161 = 2126371) B2126371
theorem B1890107 : Blo 1889435 1890107 := bstep (se 1 (by rfl) ⟨1417580, by rfl⟩ : syracuseStep 1890107 = 2835161) B2835161
theorem B5382389 : Blo 1889435 5382389 := bbase (se 5 (by rfl) ⟨252299, by rfl⟩ : syracuseStep 5382389 = 504599) (by norm_num)
theorem B14353037 : Blo 1889435 14353037 := bstep (se 3 (by rfl) ⟨2691194, by rfl⟩ : syracuseStep 14353037 = 5382389) B5382389
theorem B9568691 : Blo 1889435 9568691 := bstep (se 1 (by rfl) ⟨7176518, by rfl⟩ : syracuseStep 9568691 = 14353037) B14353037
theorem B6379127 : Blo 1889435 6379127 := bstep (se 1 (by rfl) ⟨4784345, by rfl⟩ : syracuseStep 6379127 = 9568691) B9568691
theorem B4252751 : Blo 1889435 4252751 := bstep (se 1 (by rfl) ⟨3189563, by rfl⟩ : syracuseStep 4252751 = 6379127) B6379127
theorem B2835167 : Blo 1889435 2835167 := bstep (se 1 (by rfl) ⟨2126375, by rfl⟩ : syracuseStep 2835167 = 4252751) B4252751
theorem B1890111 : Blo 1889435 1890111 := bstep (se 1 (by rfl) ⟨1417583, by rfl⟩ : syracuseStep 1890111 = 2835167) B2835167
theorem B2835173 : Blo 1889435 2835173 := bbase (se 4 (by rfl) ⟨265797, by rfl⟩ : syracuseStep 2835173 = 531595) (by norm_num)
theorem B1890115 : Blo 1889435 1890115 := bstep (se 1 (by rfl) ⟨1417586, by rfl⟩ : syracuseStep 1890115 = 2835173) B2835173
theorem B2018405 : Blo 1889435 2018405 := bbase (se 4 (by rfl) ⟨189225, by rfl⟩ : syracuseStep 2018405 = 378451) (by norm_num)
theorem B5382413 : Blo 1889435 5382413 := bstep (se 3 (by rfl) ⟨1009202, by rfl⟩ : syracuseStep 5382413 = 2018405) B2018405
theorem B3588275 : Blo 1889435 3588275 := bstep (se 1 (by rfl) ⟨2691206, by rfl⟩ : syracuseStep 3588275 = 5382413) B5382413
theorem B2392183 : Blo 1889435 2392183 := bstep (se 1 (by rfl) ⟨1794137, by rfl⟩ : syracuseStep 2392183 = 3588275) B3588275
theorem B3189577 : Blo 1889435 3189577 := bstep (se 2 (by rfl) ⟨1196091, by rfl⟩ : syracuseStep 3189577 = 2392183) B2392183
theorem B4252769 : Blo 1889435 4252769 := bstep (se 2 (by rfl) ⟨1594788, by rfl⟩ : syracuseStep 4252769 = 3189577) B3189577
theorem B2835179 : Blo 1889435 2835179 := bstep (se 1 (by rfl) ⟨2126384, by rfl⟩ : syracuseStep 2835179 = 4252769) B4252769
theorem B1890119 : Blo 1889435 1890119 := bstep (se 1 (by rfl) ⟨1417589, by rfl⟩ : syracuseStep 1890119 = 2835179) B2835179
theorem B2126389 : Blo 1889435 2126389 := bbase (se 5 (by rfl) ⟨99674, by rfl⟩ : syracuseStep 2126389 = 199349) (by norm_num)
theorem B2835185 : Blo 1889435 2835185 := bstep (se 2 (by rfl) ⟨1063194, by rfl⟩ : syracuseStep 2835185 = 2126389) B2126389
theorem B1890123 : Blo 1889435 1890123 := bstep (se 1 (by rfl) ⟨1417592, by rfl⟩ : syracuseStep 1890123 = 2835185) B2835185
theorem B2392193 : Blo 1889435 2392193 := bbase (se 2 (by rfl) ⟨897072, by rfl⟩ : syracuseStep 2392193 = 1794145) (by norm_num)
theorem B6379181 : Blo 1889435 6379181 := bstep (se 3 (by rfl) ⟨1196096, by rfl⟩ : syracuseStep 6379181 = 2392193) B2392193
theorem B4252787 : Blo 1889435 4252787 := bstep (se 1 (by rfl) ⟨3189590, by rfl⟩ : syracuseStep 4252787 = 6379181) B6379181
theorem B2835191 : Blo 1889435 2835191 := bstep (se 1 (by rfl) ⟨2126393, by rfl⟩ : syracuseStep 2835191 = 4252787) B4252787
theorem B1890127 : Blo 1889435 1890127 := bstep (se 1 (by rfl) ⟨1417595, by rfl⟩ : syracuseStep 1890127 = 2835191) B2835191
theorem B2835197 : Blo 1889435 2835197 := bbase (se 3 (by rfl) ⟨531599, by rfl⟩ : syracuseStep 2835197 = 1063199) (by norm_num)
theorem B1890131 : Blo 1889435 1890131 := bstep (se 1 (by rfl) ⟨1417598, by rfl⟩ : syracuseStep 1890131 = 2835197) B2835197
theorem B4252805 : Blo 1889435 4252805 := bbase (se 4 (by rfl) ⟨398700, by rfl⟩ : syracuseStep 4252805 = 797401) (by norm_num)
theorem B2835203 : Blo 1889435 2835203 := bstep (se 1 (by rfl) ⟨2126402, by rfl⟩ : syracuseStep 2835203 = 4252805) B4252805
theorem B1890135 : Blo 1889435 1890135 := bstep (se 1 (by rfl) ⟨1417601, by rfl⟩ : syracuseStep 1890135 = 2835203) B2835203
theorem B4036853 : Blo 1889435 4036853 := bbase (se 5 (by rfl) ⟨189227, by rfl⟩ : syracuseStep 4036853 = 378455) (by norm_num)
theorem B2691235 : Blo 1889435 2691235 := bstep (se 1 (by rfl) ⟨2018426, by rfl⟩ : syracuseStep 2691235 = 4036853) B4036853
theorem B3588313 : Blo 1889435 3588313 := bstep (se 2 (by rfl) ⟨1345617, by rfl⟩ : syracuseStep 3588313 = 2691235) B2691235
theorem B4784417 : Blo 1889435 4784417 := bstep (se 2 (by rfl) ⟨1794156, by rfl⟩ : syracuseStep 4784417 = 3588313) B3588313
theorem B3189611 : Blo 1889435 3189611 := bstep (se 1 (by rfl) ⟨2392208, by rfl⟩ : syracuseStep 3189611 = 4784417) B4784417
theorem B2126407 : Blo 1889435 2126407 := bstep (se 1 (by rfl) ⟨1594805, by rfl⟩ : syracuseStep 2126407 = 3189611) B3189611
theorem B2835209 : Blo 1889435 2835209 := bstep (se 2 (by rfl) ⟨1063203, by rfl⟩ : syracuseStep 2835209 = 2126407) B2126407
theorem B1890139 : Blo 1889435 1890139 := bstep (se 1 (by rfl) ⟨1417604, by rfl⟩ : syracuseStep 1890139 = 2835209) B2835209
theorem B9568853 : Blo 1889435 9568853 := bbase (se 8 (by rfl) ⟨56067, by rfl⟩ : syracuseStep 9568853 = 112135) (by norm_num)
theorem B6379235 : Blo 1889435 6379235 := bstep (se 1 (by rfl) ⟨4784426, by rfl⟩ : syracuseStep 6379235 = 9568853) B9568853
theorem B4252823 : Blo 1889435 4252823 := bstep (se 1 (by rfl) ⟨3189617, by rfl⟩ : syracuseStep 4252823 = 6379235) B6379235
theorem B2835215 : Blo 1889435 2835215 := bstep (se 1 (by rfl) ⟨2126411, by rfl⟩ : syracuseStep 2835215 = 4252823) B4252823
theorem B1890143 : Blo 1889435 1890143 := bstep (se 1 (by rfl) ⟨1417607, by rfl⟩ : syracuseStep 1890143 = 2835215) B2835215
theorem B2835221 : Blo 1889435 2835221 := bbase (se 6 (by rfl) ⟨66450, by rfl⟩ : syracuseStep 2835221 = 132901) (by norm_num)
theorem B1890147 : Blo 1889435 1890147 := bstep (se 1 (by rfl) ⟨1417610, by rfl⟩ : syracuseStep 1890147 = 2835221) B2835221
theorem B12932597 : Blo 1889435 12932597 := bbase (se 5 (by rfl) ⟨606215, by rfl⟩ : syracuseStep 12932597 = 1212431) (by norm_num)
theorem B8621731 : Blo 1889435 8621731 := bstep (se 1 (by rfl) ⟨6466298, by rfl⟩ : syracuseStep 8621731 = 12932597) B12932597
theorem B45982565 : Blo 1889435 45982565 := bstep (se 4 (by rfl) ⟨4310865, by rfl⟩ : syracuseStep 45982565 = 8621731) B8621731
theorem B30655043 : Blo 1889435 30655043 := bstep (se 1 (by rfl) ⟨22991282, by rfl⟩ : syracuseStep 30655043 = 45982565) B45982565
theorem B20436695 : Blo 1889435 20436695 := bstep (se 1 (by rfl) ⟨15327521, by rfl⟩ : syracuseStep 20436695 = 30655043) B30655043
theorem B13624463 : Blo 1889435 13624463 := bstep (se 1 (by rfl) ⟨10218347, by rfl⟩ : syracuseStep 13624463 = 20436695) B20436695
theorem B36331901 : Blo 1889435 36331901 := bstep (se 3 (by rfl) ⟨6812231, by rfl⟩ : syracuseStep 36331901 = 13624463) B13624463
theorem B24221267 : Blo 1889435 24221267 := bstep (se 1 (by rfl) ⟨18165950, by rfl⟩ : syracuseStep 24221267 = 36331901) B36331901
theorem B16147511 : Blo 1889435 16147511 := bstep (se 1 (by rfl) ⟨12110633, by rfl⟩ : syracuseStep 16147511 = 24221267) B24221267
theorem B10765007 : Blo 1889435 10765007 := bstep (se 1 (by rfl) ⟨8073755, by rfl⟩ : syracuseStep 10765007 = 16147511) B16147511
theorem B7176671 : Blo 1889435 7176671 := bstep (se 1 (by rfl) ⟨5382503, by rfl⟩ : syracuseStep 7176671 = 10765007) B10765007
theorem B4784447 : Blo 1889435 4784447 := bstep (se 1 (by rfl) ⟨3588335, by rfl⟩ : syracuseStep 4784447 = 7176671) B7176671
theorem B3189631 : Blo 1889435 3189631 := bstep (se 1 (by rfl) ⟨2392223, by rfl⟩ : syracuseStep 3189631 = 4784447) B4784447
theorem B4252841 : Blo 1889435 4252841 := bstep (se 2 (by rfl) ⟨1594815, by rfl⟩ : syracuseStep 4252841 = 3189631) B3189631
theorem B2835227 : Blo 1889435 2835227 := bstep (se 1 (by rfl) ⟨2126420, by rfl⟩ : syracuseStep 2835227 = 4252841) B4252841
theorem B1890151 : Blo 1889435 1890151 := bstep (se 1 (by rfl) ⟨1417613, by rfl⟩ : syracuseStep 1890151 = 2835227) B2835227
theorem B2126425 : Blo 1889435 2126425 := bbase (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) (by norm_num)
theorem B2835233 : Blo 1889435 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B1890155 : Blo 1889435 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B4310885 : Blo 1889435 4310885 := bbase (se 4 (by rfl) ⟨404145, by rfl⟩ : syracuseStep 4310885 = 808291) (by norm_num)
theorem B2873923 : Blo 1889435 2873923 := bstep (se 1 (by rfl) ⟨2155442, by rfl⟩ : syracuseStep 2873923 = 4310885) B4310885
theorem B15327589 : Blo 1889435 15327589 := bstep (se 4 (by rfl) ⟨1436961, by rfl⟩ : syracuseStep 15327589 = 2873923) B2873923
theorem B20436785 : Blo 1889435 20436785 := bstep (se 2 (by rfl) ⟨7663794, by rfl⟩ : syracuseStep 20436785 = 15327589) B15327589
theorem B13624523 : Blo 1889435 13624523 := bstep (se 1 (by rfl) ⟨10218392, by rfl⟩ : syracuseStep 13624523 = 20436785) B20436785
theorem B9083015 : Blo 1889435 9083015 := bstep (se 1 (by rfl) ⟨6812261, by rfl⟩ : syracuseStep 9083015 = 13624523) B13624523
theorem B6055343 : Blo 1889435 6055343 := bstep (se 1 (by rfl) ⟨4541507, by rfl⟩ : syracuseStep 6055343 = 9083015) B9083015
theorem B4036895 : Blo 1889435 4036895 := bstep (se 1 (by rfl) ⟨3027671, by rfl⟩ : syracuseStep 4036895 = 6055343) B6055343
theorem B2691263 : Blo 1889435 2691263 := bstep (se 1 (by rfl) ⟨2018447, by rfl⟩ : syracuseStep 2691263 = 4036895) B4036895
theorem B7176701 : Blo 1889435 7176701 := bstep (se 3 (by rfl) ⟨1345631, by rfl⟩ : syracuseStep 7176701 = 2691263) B2691263
theorem B4784467 : Blo 1889435 4784467 := bstep (se 1 (by rfl) ⟨3588350, by rfl⟩ : syracuseStep 4784467 = 7176701) B7176701
theorem B6379289 : Blo 1889435 6379289 := bstep (se 2 (by rfl) ⟨2392233, by rfl⟩ : syracuseStep 6379289 = 4784467) B4784467
theorem B4252859 : Blo 1889435 4252859 := bstep (se 1 (by rfl) ⟨3189644, by rfl⟩ : syracuseStep 4252859 = 6379289) B6379289
theorem B2835239 : Blo 1889435 2835239 := bstep (se 1 (by rfl) ⟨2126429, by rfl⟩ : syracuseStep 2835239 = 4252859) B4252859
theorem B1890159 : Blo 1889435 1890159 := bstep (se 1 (by rfl) ⟨1417619, by rfl⟩ : syracuseStep 1890159 = 2835239) B2835239
theorem B2835245 : Blo 1889435 2835245 := bbase (se 3 (by rfl) ⟨531608, by rfl⟩ : syracuseStep 2835245 = 1063217) (by norm_num)
theorem B1890163 : Blo 1889435 1890163 := bstep (se 1 (by rfl) ⟨1417622, by rfl⟩ : syracuseStep 1890163 = 2835245) B2835245
theorem B4252877 : Blo 1889435 4252877 := bbase (se 3 (by rfl) ⟨797414, by rfl⟩ : syracuseStep 4252877 = 1594829) (by norm_num)
theorem B2835251 : Blo 1889435 2835251 := bstep (se 1 (by rfl) ⟨2126438, by rfl⟩ : syracuseStep 2835251 = 4252877) B4252877
theorem B1890167 : Blo 1889435 1890167 := bstep (se 1 (by rfl) ⟨1417625, by rfl⟩ : syracuseStep 1890167 = 2835251) B2835251
theorem B2392249 : Blo 1889435 2392249 := bbase (se 2 (by rfl) ⟨897093, by rfl⟩ : syracuseStep 2392249 = 1794187) (by norm_num)
theorem B3189665 : Blo 1889435 3189665 := bstep (se 2 (by rfl) ⟨1196124, by rfl⟩ : syracuseStep 3189665 = 2392249) B2392249
theorem B2126443 : Blo 1889435 2126443 := bstep (se 1 (by rfl) ⟨1594832, by rfl⟩ : syracuseStep 2126443 = 3189665) B3189665
theorem B2835257 : Blo 1889435 2835257 := bstep (se 2 (by rfl) ⟨1063221, by rfl⟩ : syracuseStep 2835257 = 2126443) B2126443
theorem B1890171 : Blo 1889435 1890171 := bstep (se 1 (by rfl) ⟨1417628, by rfl⟩ : syracuseStep 1890171 = 2835257) B2835257
theorem B3884213 : Blo 1889435 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B2589475 : Blo 1889435 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B3452633 : Blo 1889435 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2301755 : Blo 1889435 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B6138013 : Blo 1889435 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B8184017 : Blo 1889435 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B5456011 : Blo 1889435 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B7274681 : Blo 1889435 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B4849787 : Blo 1889435 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B3233191 : Blo 1889435 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B4310921 : Blo 1889435 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B11495789 : Blo 1889435 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B7663859 : Blo 1889435 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B5109239 : Blo 1889435 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B3406159 : Blo 1889435 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B4541545 : Blo 1889435 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B6055393 : Blo 1889435 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B8073857 : Blo 1889435 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B21530285 : Blo 1889435 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B14353523 : Blo 1889435 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B9569015 : Blo 1889435 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B6379343 : Blo 1889435 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B4252895 : Blo 1889435 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B2835263 : Blo 1889435 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B1890175 : Blo 1889435 1890175 := bstep (se 1 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 1890175 = 2835263) B2835263
theorem B2835269 : Blo 1889435 2835269 := bbase (se 4 (by rfl) ⟨265806, by rfl⟩ : syracuseStep 2835269 = 531613) (by norm_num)
theorem B1890179 : Blo 1889435 1890179 := bstep (se 1 (by rfl) ⟨1417634, by rfl⟩ : syracuseStep 1890179 = 2835269) B2835269
theorem B3189685 : Blo 1889435 3189685 := bbase (se 5 (by rfl) ⟨149516, by rfl⟩ : syracuseStep 3189685 = 299033) (by norm_num)
theorem B4252913 : Blo 1889435 4252913 := bstep (se 2 (by rfl) ⟨1594842, by rfl⟩ : syracuseStep 4252913 = 3189685) B3189685
theorem B2835275 : Blo 1889435 2835275 := bstep (se 1 (by rfl) ⟨2126456, by rfl⟩ : syracuseStep 2835275 = 4252913) B4252913
theorem B1890183 : Blo 1889435 1890183 := bstep (se 1 (by rfl) ⟨1417637, by rfl⟩ : syracuseStep 1890183 = 2835275) B2835275
theorem B2126461 : Blo 1889435 2126461 := bbase (se 3 (by rfl) ⟨398711, by rfl⟩ : syracuseStep 2126461 = 797423) (by norm_num)
theorem B2835281 : Blo 1889435 2835281 := bstep (se 2 (by rfl) ⟨1063230, by rfl⟩ : syracuseStep 2835281 = 2126461) B2126461
theorem B1890187 : Blo 1889435 1890187 := bstep (se 1 (by rfl) ⟨1417640, by rfl⟩ : syracuseStep 1890187 = 2835281) B2835281
theorem B6379397 : Blo 1889435 6379397 := bbase (se 4 (by rfl) ⟨598068, by rfl⟩ : syracuseStep 6379397 = 1196137) (by norm_num)
theorem B4252931 : Blo 1889435 4252931 := bstep (se 1 (by rfl) ⟨3189698, by rfl⟩ : syracuseStep 4252931 = 6379397) B6379397
theorem B2835287 : Blo 1889435 2835287 := bstep (se 1 (by rfl) ⟨2126465, by rfl⟩ : syracuseStep 2835287 = 4252931) B4252931
theorem B1890191 : Blo 1889435 1890191 := bstep (se 1 (by rfl) ⟨1417643, by rfl⟩ : syracuseStep 1890191 = 2835287) B2835287
theorem B2835293 : Blo 1889435 2835293 := bbase (se 3 (by rfl) ⟨531617, by rfl⟩ : syracuseStep 2835293 = 1063235) (by norm_num)
theorem B1890195 : Blo 1889435 1890195 := bstep (se 1 (by rfl) ⟨1417646, by rfl⟩ : syracuseStep 1890195 = 2835293) B2835293
theorem B4252949 : Blo 1889435 4252949 := bbase (se 6 (by rfl) ⟨99678, by rfl⟩ : syracuseStep 4252949 = 199357) (by norm_num)
theorem B2835299 : Blo 1889435 2835299 := bstep (se 1 (by rfl) ⟨2126474, by rfl⟩ : syracuseStep 2835299 = 4252949) B4252949
theorem B1890199 : Blo 1889435 1890199 := bstep (se 1 (by rfl) ⟨1417649, by rfl⟩ : syracuseStep 1890199 = 2835299) B2835299
theorem B7176869 : Blo 1889435 7176869 := bbase (se 4 (by rfl) ⟨672831, by rfl⟩ : syracuseStep 7176869 = 1345663) (by norm_num)
theorem B4784579 : Blo 1889435 4784579 := bstep (se 1 (by rfl) ⟨3588434, by rfl⟩ : syracuseStep 4784579 = 7176869) B7176869
theorem B3189719 : Blo 1889435 3189719 := bstep (se 1 (by rfl) ⟨2392289, by rfl⟩ : syracuseStep 3189719 = 4784579) B4784579
theorem B2126479 : Blo 1889435 2126479 := bstep (se 1 (by rfl) ⟨1594859, by rfl⟩ : syracuseStep 2126479 = 3189719) B3189719
theorem B2835305 : Blo 1889435 2835305 := bstep (se 2 (by rfl) ⟨1063239, by rfl⟩ : syracuseStep 2835305 = 2126479) B2126479
theorem B1890203 : Blo 1889435 1890203 := bstep (se 1 (by rfl) ⟨1417652, by rfl⟩ : syracuseStep 1890203 = 2835305) B2835305
theorem B4036997 : Blo 1889435 4036997 := bbase (se 4 (by rfl) ⟨378468, by rfl⟩ : syracuseStep 4036997 = 756937) (by norm_num)
theorem B10765325 : Blo 1889435 10765325 := bstep (se 3 (by rfl) ⟨2018498, by rfl⟩ : syracuseStep 10765325 = 4036997) B4036997
theorem B7176883 : Blo 1889435 7176883 := bstep (se 1 (by rfl) ⟨5382662, by rfl⟩ : syracuseStep 7176883 = 10765325) B10765325
theorem B9569177 : Blo 1889435 9569177 := bstep (se 2 (by rfl) ⟨3588441, by rfl⟩ : syracuseStep 9569177 = 7176883) B7176883
theorem B6379451 : Blo 1889435 6379451 := bstep (se 1 (by rfl) ⟨4784588, by rfl⟩ : syracuseStep 6379451 = 9569177) B9569177
theorem B4252967 : Blo 1889435 4252967 := bstep (se 1 (by rfl) ⟨3189725, by rfl⟩ : syracuseStep 4252967 = 6379451) B6379451
theorem B2835311 : Blo 1889435 2835311 := bstep (se 1 (by rfl) ⟨2126483, by rfl⟩ : syracuseStep 2835311 = 4252967) B4252967
theorem B1890207 : Blo 1889435 1890207 := bstep (se 1 (by rfl) ⟨1417655, by rfl⟩ : syracuseStep 1890207 = 2835311) B2835311
theorem B2835317 : Blo 1889435 2835317 := bbase (se 5 (by rfl) ⟨132905, by rfl⟩ : syracuseStep 2835317 = 265811) (by norm_num)
theorem B1890211 : Blo 1889435 1890211 := bstep (se 1 (by rfl) ⟨1417658, by rfl⟩ : syracuseStep 1890211 = 2835317) B2835317
theorem B9083285 : Blo 1889435 9083285 := bbase (se 6 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 9083285 = 425779) (by norm_num)
theorem B6055523 : Blo 1889435 6055523 := bstep (se 1 (by rfl) ⟨4541642, by rfl⟩ : syracuseStep 6055523 = 9083285) B9083285
theorem B4037015 : Blo 1889435 4037015 := bstep (se 1 (by rfl) ⟨3027761, by rfl⟩ : syracuseStep 4037015 = 6055523) B6055523
theorem B2691343 : Blo 1889435 2691343 := bstep (se 1 (by rfl) ⟨2018507, by rfl⟩ : syracuseStep 2691343 = 4037015) B4037015
theorem B3588457 : Blo 1889435 3588457 := bstep (se 2 (by rfl) ⟨1345671, by rfl⟩ : syracuseStep 3588457 = 2691343) B2691343
theorem B4784609 : Blo 1889435 4784609 := bstep (se 2 (by rfl) ⟨1794228, by rfl⟩ : syracuseStep 4784609 = 3588457) B3588457
theorem B3189739 : Blo 1889435 3189739 := bstep (se 1 (by rfl) ⟨2392304, by rfl⟩ : syracuseStep 3189739 = 4784609) B4784609
theorem B4252985 : Blo 1889435 4252985 := bstep (se 2 (by rfl) ⟨1594869, by rfl⟩ : syracuseStep 4252985 = 3189739) B3189739
theorem B2835323 : Blo 1889435 2835323 := bstep (se 1 (by rfl) ⟨2126492, by rfl⟩ : syracuseStep 2835323 = 4252985) B4252985
theorem B1890215 : Blo 1889435 1890215 := bstep (se 1 (by rfl) ⟨1417661, by rfl⟩ : syracuseStep 1890215 = 2835323) B2835323
theorem B2126497 : Blo 1889435 2126497 := bbase (se 2 (by rfl) ⟨797436, by rfl⟩ : syracuseStep 2126497 = 1594873) (by norm_num)
theorem B2835329 : Blo 1889435 2835329 := bstep (se 2 (by rfl) ⟨1063248, by rfl⟩ : syracuseStep 2835329 = 2126497) B2126497
theorem B1890219 : Blo 1889435 1890219 := bstep (se 1 (by rfl) ⟨1417664, by rfl⟩ : syracuseStep 1890219 = 2835329) B2835329
theorem B4784629 : Blo 1889435 4784629 := bbase (se 5 (by rfl) ⟨224279, by rfl⟩ : syracuseStep 4784629 = 448559) (by norm_num)
theorem B6379505 : Blo 1889435 6379505 := bstep (se 2 (by rfl) ⟨2392314, by rfl⟩ : syracuseStep 6379505 = 4784629) B4784629
theorem B4253003 : Blo 1889435 4253003 := bstep (se 1 (by rfl) ⟨3189752, by rfl⟩ : syracuseStep 4253003 = 6379505) B6379505
theorem B2835335 : Blo 1889435 2835335 := bstep (se 1 (by rfl) ⟨2126501, by rfl⟩ : syracuseStep 2835335 = 4253003) B4253003
theorem B1890223 : Blo 1889435 1890223 := bstep (se 1 (by rfl) ⟨1417667, by rfl⟩ : syracuseStep 1890223 = 2835335) B2835335
theorem B2835341 : Blo 1889435 2835341 := bbase (se 3 (by rfl) ⟨531626, by rfl⟩ : syracuseStep 2835341 = 1063253) (by norm_num)
theorem B1890227 : Blo 1889435 1890227 := bstep (se 1 (by rfl) ⟨1417670, by rfl⟩ : syracuseStep 1890227 = 2835341) B2835341
theorem B4253021 : Blo 1889435 4253021 := bbase (se 3 (by rfl) ⟨797441, by rfl⟩ : syracuseStep 4253021 = 1594883) (by norm_num)
theorem B2835347 : Blo 1889435 2835347 := bstep (se 1 (by rfl) ⟨2126510, by rfl⟩ : syracuseStep 2835347 = 4253021) B4253021
theorem B1890231 : Blo 1889435 1890231 := bstep (se 1 (by rfl) ⟨1417673, by rfl⟩ : syracuseStep 1890231 = 2835347) B2835347
theorem B3189773 : Blo 1889435 3189773 := bbase (se 3 (by rfl) ⟨598082, by rfl⟩ : syracuseStep 3189773 = 1196165) (by norm_num)
theorem B2126515 : Blo 1889435 2126515 := bstep (se 1 (by rfl) ⟨1594886, by rfl⟩ : syracuseStep 2126515 = 3189773) B3189773
theorem B2835353 : Blo 1889435 2835353 := bstep (se 2 (by rfl) ⟨1063257, by rfl⟩ : syracuseStep 2835353 = 2126515) B2126515
theorem B1890235 : Blo 1889435 1890235 := bstep (se 1 (by rfl) ⟨1417676, by rfl⟩ : syracuseStep 1890235 = 2835353) B2835353
theorem B6812549 : Blo 1889435 6812549 := bbase (se 4 (by rfl) ⟨638676, by rfl⟩ : syracuseStep 6812549 = 1277353) (by norm_num)
theorem B4541699 : Blo 1889435 4541699 := bstep (se 1 (by rfl) ⟨3406274, by rfl⟩ : syracuseStep 4541699 = 6812549) B6812549
theorem B3027799 : Blo 1889435 3027799 := bstep (se 1 (by rfl) ⟨2270849, by rfl⟩ : syracuseStep 3027799 = 4541699) B4541699
theorem B16148261 : Blo 1889435 16148261 := bstep (se 4 (by rfl) ⟨1513899, by rfl⟩ : syracuseStep 16148261 = 3027799) B3027799
theorem B10765507 : Blo 1889435 10765507 := bstep (se 1 (by rfl) ⟨8074130, by rfl⟩ : syracuseStep 10765507 = 16148261) B16148261
theorem B14354009 : Blo 1889435 14354009 := bstep (se 2 (by rfl) ⟨5382753, by rfl⟩ : syracuseStep 14354009 = 10765507) B10765507
theorem B9569339 : Blo 1889435 9569339 := bstep (se 1 (by rfl) ⟨7177004, by rfl⟩ : syracuseStep 9569339 = 14354009) B14354009
theorem B6379559 : Blo 1889435 6379559 := bstep (se 1 (by rfl) ⟨4784669, by rfl⟩ : syracuseStep 6379559 = 9569339) B9569339
theorem B4253039 : Blo 1889435 4253039 := bstep (se 1 (by rfl) ⟨3189779, by rfl⟩ : syracuseStep 4253039 = 6379559) B6379559
theorem B2835359 : Blo 1889435 2835359 := bstep (se 1 (by rfl) ⟨2126519, by rfl⟩ : syracuseStep 2835359 = 4253039) B4253039
theorem B1890239 : Blo 1889435 1890239 := bstep (se 1 (by rfl) ⟨1417679, by rfl⟩ : syracuseStep 1890239 = 2835359) B2835359
theorem B2835365 : Blo 1889435 2835365 := bbase (se 4 (by rfl) ⟨265815, by rfl⟩ : syracuseStep 2835365 = 531631) (by norm_num)
theorem B1890243 : Blo 1889435 1890243 := bstep (se 1 (by rfl) ⟨1417682, by rfl⟩ : syracuseStep 1890243 = 2835365) B2835365
theorem B2392345 : Blo 1889435 2392345 := bbase (se 2 (by rfl) ⟨897129, by rfl⟩ : syracuseStep 2392345 = 1794259) (by norm_num)
theorem B3189793 : Blo 1889435 3189793 := bstep (se 2 (by rfl) ⟨1196172, by rfl⟩ : syracuseStep 3189793 = 2392345) B2392345
theorem B4253057 : Blo 1889435 4253057 := bstep (se 2 (by rfl) ⟨1594896, by rfl⟩ : syracuseStep 4253057 = 3189793) B3189793
theorem B2835371 : Blo 1889435 2835371 := bstep (se 1 (by rfl) ⟨2126528, by rfl⟩ : syracuseStep 2835371 = 4253057) B4253057
theorem B1890247 : Blo 1889435 1890247 := bstep (se 1 (by rfl) ⟨1417685, by rfl⟩ : syracuseStep 1890247 = 2835371) B2835371
theorem B2126533 : Blo 1889435 2126533 := bbase (se 4 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 2126533 = 398725) (by norm_num)
theorem B2835377 : Blo 1889435 2835377 := bstep (se 2 (by rfl) ⟨1063266, by rfl⟩ : syracuseStep 2835377 = 2126533) B2126533
theorem B1890251 : Blo 1889435 1890251 := bstep (se 1 (by rfl) ⟨1417688, by rfl⟩ : syracuseStep 1890251 = 2835377) B2835377
theorem B3588533 : Blo 1889435 3588533 := bbase (se 5 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 3588533 = 336425) (by norm_num)
theorem B2392355 : Blo 1889435 2392355 := bstep (se 1 (by rfl) ⟨1794266, by rfl⟩ : syracuseStep 2392355 = 3588533) B3588533
theorem B6379613 : Blo 1889435 6379613 := bstep (se 3 (by rfl) ⟨1196177, by rfl⟩ : syracuseStep 6379613 = 2392355) B2392355
theorem B4253075 : Blo 1889435 4253075 := bstep (se 1 (by rfl) ⟨3189806, by rfl⟩ : syracuseStep 4253075 = 6379613) B6379613
theorem B2835383 : Blo 1889435 2835383 := bstep (se 1 (by rfl) ⟨2126537, by rfl⟩ : syracuseStep 2835383 = 4253075) B4253075
theorem B1890255 : Blo 1889435 1890255 := bstep (se 1 (by rfl) ⟨1417691, by rfl⟩ : syracuseStep 1890255 = 2835383) B2835383
theorem B2835389 : Blo 1889435 2835389 := bbase (se 3 (by rfl) ⟨531635, by rfl⟩ : syracuseStep 2835389 = 1063271) (by norm_num)
theorem B1890259 : Blo 1889435 1890259 := bstep (se 1 (by rfl) ⟨1417694, by rfl⟩ : syracuseStep 1890259 = 2835389) B2835389
theorem B4253093 : Blo 1889435 4253093 := bbase (se 4 (by rfl) ⟨398727, by rfl⟩ : syracuseStep 4253093 = 797455) (by norm_num)
theorem B2835395 : Blo 1889435 2835395 := bstep (se 1 (by rfl) ⟨2126546, by rfl⟩ : syracuseStep 2835395 = 4253093) B4253093
theorem B1890263 : Blo 1889435 1890263 := bstep (se 1 (by rfl) ⟨1417697, by rfl⟩ : syracuseStep 1890263 = 2835395) B2835395
theorem B4784741 : Blo 1889435 4784741 := bbase (se 4 (by rfl) ⟨448569, by rfl⟩ : syracuseStep 4784741 = 897139) (by norm_num)
theorem B3189827 : Blo 1889435 3189827 := bstep (se 1 (by rfl) ⟨2392370, by rfl⟩ : syracuseStep 3189827 = 4784741) B4784741
theorem B2126551 : Blo 1889435 2126551 := bstep (se 1 (by rfl) ⟨1594913, by rfl⟩ : syracuseStep 2126551 = 3189827) B3189827
theorem B2835401 : Blo 1889435 2835401 := bstep (se 2 (by rfl) ⟨1063275, by rfl⟩ : syracuseStep 2835401 = 2126551) B2126551
theorem B1890267 : Blo 1889435 1890267 := bstep (se 1 (by rfl) ⟨1417700, by rfl⟩ : syracuseStep 1890267 = 2835401) B2835401
theorem B3406333 : Blo 1889435 3406333 := bbase (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) (by norm_num)
theorem B4541777 : Blo 1889435 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B3027851 : Blo 1889435 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B2018567 : Blo 1889435 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B5382845 : Blo 1889435 5382845 := bstep (se 3 (by rfl) ⟨1009283, by rfl⟩ : syracuseStep 5382845 = 2018567) B2018567
theorem B3588563 : Blo 1889435 3588563 := bstep (se 1 (by rfl) ⟨2691422, by rfl⟩ : syracuseStep 3588563 = 5382845) B5382845
theorem B9569501 : Blo 1889435 9569501 := bstep (se 3 (by rfl) ⟨1794281, by rfl⟩ : syracuseStep 9569501 = 3588563) B3588563
theorem B6379667 : Blo 1889435 6379667 := bstep (se 1 (by rfl) ⟨4784750, by rfl⟩ : syracuseStep 6379667 = 9569501) B9569501
theorem B4253111 : Blo 1889435 4253111 := bstep (se 1 (by rfl) ⟨3189833, by rfl⟩ : syracuseStep 4253111 = 6379667) B6379667
theorem B2835407 : Blo 1889435 2835407 := bstep (se 1 (by rfl) ⟨2126555, by rfl⟩ : syracuseStep 2835407 = 4253111) B4253111
theorem B1890271 : Blo 1889435 1890271 := bstep (se 1 (by rfl) ⟨1417703, by rfl⟩ : syracuseStep 1890271 = 2835407) B2835407
theorem B2835413 : Blo 1889435 2835413 := bbase (se 7 (by rfl) ⟨33227, by rfl⟩ : syracuseStep 2835413 = 66455) (by norm_num)
theorem B1890275 : Blo 1889435 1890275 := bstep (se 1 (by rfl) ⟨1417706, by rfl⟩ : syracuseStep 1890275 = 2835413) B2835413
theorem B7177157 : Blo 1889435 7177157 := bbase (se 4 (by rfl) ⟨672858, by rfl⟩ : syracuseStep 7177157 = 1345717) (by norm_num)
theorem B4784771 : Blo 1889435 4784771 := bstep (se 1 (by rfl) ⟨3588578, by rfl⟩ : syracuseStep 4784771 = 7177157) B7177157
theorem B3189847 : Blo 1889435 3189847 := bstep (se 1 (by rfl) ⟨2392385, by rfl⟩ : syracuseStep 3189847 = 4784771) B4784771
theorem B4253129 : Blo 1889435 4253129 := bstep (se 2 (by rfl) ⟨1594923, by rfl⟩ : syracuseStep 4253129 = 3189847) B3189847
theorem B2835419 : Blo 1889435 2835419 := bstep (se 1 (by rfl) ⟨2126564, by rfl⟩ : syracuseStep 2835419 = 4253129) B4253129
theorem B1890279 : Blo 1889435 1890279 := bstep (se 1 (by rfl) ⟨1417709, by rfl⟩ : syracuseStep 1890279 = 2835419) B2835419
theorem B2126569 : Blo 1889435 2126569 := bbase (se 2 (by rfl) ⟨797463, by rfl⟩ : syracuseStep 2126569 = 1594927) (by norm_num)
theorem B2835425 : Blo 1889435 2835425 := bstep (se 2 (by rfl) ⟨1063284, by rfl⟩ : syracuseStep 2835425 = 2126569) B2126569
theorem B1890283 : Blo 1889435 1890283 := bstep (se 1 (by rfl) ⟨1417712, by rfl⟩ : syracuseStep 1890283 = 2835425) B2835425
theorem B10765781 : Blo 1889435 10765781 := bbase (se 7 (by rfl) ⟨126161, by rfl⟩ : syracuseStep 10765781 = 252323) (by norm_num)
theorem B7177187 : Blo 1889435 7177187 := bstep (se 1 (by rfl) ⟨5382890, by rfl⟩ : syracuseStep 7177187 = 10765781) B10765781
theorem B4784791 : Blo 1889435 4784791 := bstep (se 1 (by rfl) ⟨3588593, by rfl⟩ : syracuseStep 4784791 = 7177187) B7177187
theorem B6379721 : Blo 1889435 6379721 := bstep (se 2 (by rfl) ⟨2392395, by rfl⟩ : syracuseStep 6379721 = 4784791) B4784791
theorem B4253147 : Blo 1889435 4253147 := bstep (se 1 (by rfl) ⟨3189860, by rfl⟩ : syracuseStep 4253147 = 6379721) B6379721
theorem B2835431 : Blo 1889435 2835431 := bstep (se 1 (by rfl) ⟨2126573, by rfl⟩ : syracuseStep 2835431 = 4253147) B4253147
theorem B1890287 : Blo 1889435 1890287 := bstep (se 1 (by rfl) ⟨1417715, by rfl⟩ : syracuseStep 1890287 = 2835431) B2835431
theorem B2835437 : Blo 1889435 2835437 := bbase (se 3 (by rfl) ⟨531644, by rfl⟩ : syracuseStep 2835437 = 1063289) (by norm_num)
theorem B1890291 : Blo 1889435 1890291 := bstep (se 1 (by rfl) ⟨1417718, by rfl⟩ : syracuseStep 1890291 = 2835437) B2835437
theorem B4253165 : Blo 1889435 4253165 := bbase (se 3 (by rfl) ⟨797468, by rfl⟩ : syracuseStep 4253165 = 1594937) (by norm_num)
theorem B2835443 : Blo 1889435 2835443 := bstep (se 1 (by rfl) ⟨2126582, by rfl⟩ : syracuseStep 2835443 = 4253165) B4253165
theorem B1890295 : Blo 1889435 1890295 := bstep (se 1 (by rfl) ⟨1417721, by rfl⟩ : syracuseStep 1890295 = 2835443) B2835443
theorem B4541845 : Blo 1889435 4541845 := bbase (se 6 (by rfl) ⟨106449, by rfl⟩ : syracuseStep 4541845 = 212899) (by norm_num)
theorem B6055793 : Blo 1889435 6055793 := bstep (se 2 (by rfl) ⟨2270922, by rfl⟩ : syracuseStep 6055793 = 4541845) B4541845
theorem B4037195 : Blo 1889435 4037195 := bstep (se 1 (by rfl) ⟨3027896, by rfl⟩ : syracuseStep 4037195 = 6055793) B6055793
theorem B2691463 : Blo 1889435 2691463 := bstep (se 1 (by rfl) ⟨2018597, by rfl⟩ : syracuseStep 2691463 = 4037195) B4037195
theorem B3588617 : Blo 1889435 3588617 := bstep (se 2 (by rfl) ⟨1345731, by rfl⟩ : syracuseStep 3588617 = 2691463) B2691463
theorem B2392411 : Blo 1889435 2392411 := bstep (se 1 (by rfl) ⟨1794308, by rfl⟩ : syracuseStep 2392411 = 3588617) B3588617
theorem B3189881 : Blo 1889435 3189881 := bstep (se 2 (by rfl) ⟨1196205, by rfl⟩ : syracuseStep 3189881 = 2392411) B2392411
theorem B2126587 : Blo 1889435 2126587 := bstep (se 1 (by rfl) ⟨1594940, by rfl⟩ : syracuseStep 2126587 = 3189881) B3189881
theorem B2835449 : Blo 1889435 2835449 := bstep (se 2 (by rfl) ⟨1063293, by rfl⟩ : syracuseStep 2835449 = 2126587) B2126587
theorem B1890299 : Blo 1889435 1890299 := bstep (se 1 (by rfl) ⟨1417724, by rfl⟩ : syracuseStep 1890299 = 2835449) B2835449
theorem B15964757 : Blo 1889435 15964757 := bbase (se 8 (by rfl) ⟨93543, by rfl⟩ : syracuseStep 15964757 = 187087) (by norm_num)
theorem B10643171 : Blo 1889435 10643171 := bstep (se 1 (by rfl) ⟨7982378, by rfl⟩ : syracuseStep 10643171 = 15964757) B15964757
theorem B28381789 : Blo 1889435 28381789 := bstep (se 3 (by rfl) ⟨5321585, by rfl⟩ : syracuseStep 28381789 = 10643171) B10643171
theorem B37842385 : Blo 1889435 37842385 := bstep (se 2 (by rfl) ⟨14190894, by rfl⟩ : syracuseStep 37842385 = 28381789) B28381789
theorem B50456513 : Blo 1889435 50456513 := bstep (se 2 (by rfl) ⟨18921192, by rfl⟩ : syracuseStep 50456513 = 37842385) B37842385
theorem B33637675 : Blo 1889435 33637675 := bstep (se 1 (by rfl) ⟨25228256, by rfl⟩ : syracuseStep 33637675 = 50456513) B50456513
theorem B44850233 : Blo 1889435 44850233 := bstep (se 2 (by rfl) ⟨16818837, by rfl⟩ : syracuseStep 44850233 = 33637675) B33637675
theorem B119600621 : Blo 1889435 119600621 := bstep (se 3 (by rfl) ⟨22425116, by rfl⟩ : syracuseStep 119600621 = 44850233) B44850233
theorem B79733747 : Blo 1889435 79733747 := bstep (se 1 (by rfl) ⟨59800310, by rfl⟩ : syracuseStep 79733747 = 119600621) B119600621
theorem B53155831 : Blo 1889435 53155831 := bstep (se 1 (by rfl) ⟨39866873, by rfl⟩ : syracuseStep 53155831 = 79733747) B79733747
theorem B70874441 : Blo 1889435 70874441 := bstep (se 2 (by rfl) ⟨26577915, by rfl⟩ : syracuseStep 70874441 = 53155831) B53155831
theorem B47249627 : Blo 1889435 47249627 := bstep (se 1 (by rfl) ⟨35437220, by rfl⟩ : syracuseStep 47249627 = 70874441) B70874441
theorem B125999005 : Blo 1889435 125999005 := bstep (se 3 (by rfl) ⟨23624813, by rfl⟩ : syracuseStep 125999005 = 47249627) B47249627
theorem B167998673 : Blo 1889435 167998673 := bstep (se 2 (by rfl) ⟨62999502, by rfl⟩ : syracuseStep 167998673 = 125999005) B125999005
theorem B111999115 : Blo 1889435 111999115 := bstep (se 1 (by rfl) ⟨83999336, by rfl⟩ : syracuseStep 111999115 = 167998673) B167998673
theorem B597328613 : Blo 1889435 597328613 := bstep (se 4 (by rfl) ⟨55999557, by rfl⟩ : syracuseStep 597328613 = 111999115) B111999115
theorem B398219075 : Blo 1889435 398219075 := bstep (se 1 (by rfl) ⟨298664306, by rfl⟩ : syracuseStep 398219075 = 597328613) B597328613
theorem B265479383 : Blo 1889435 265479383 := bstep (se 1 (by rfl) ⟨199109537, by rfl⟩ : syracuseStep 265479383 = 398219075) B398219075
theorem B176986255 : Blo 1889435 176986255 := bstep (se 1 (by rfl) ⟨132739691, by rfl⟩ : syracuseStep 176986255 = 265479383) B265479383
theorem B235981673 : Blo 1889435 235981673 := bstep (se 2 (by rfl) ⟨88493127, by rfl⟩ : syracuseStep 235981673 = 176986255) B176986255
theorem B157321115 : Blo 1889435 157321115 := bstep (se 1 (by rfl) ⟨117990836, by rfl⟩ : syracuseStep 157321115 = 235981673) B235981673
theorem B104880743 : Blo 1889435 104880743 := bstep (se 1 (by rfl) ⟨78660557, by rfl⟩ : syracuseStep 104880743 = 157321115) B157321115
theorem B69920495 : Blo 1889435 69920495 := bstep (se 1 (by rfl) ⟨52440371, by rfl⟩ : syracuseStep 69920495 = 104880743) B104880743
theorem B46613663 : Blo 1889435 46613663 := bstep (se 1 (by rfl) ⟨34960247, by rfl⟩ : syracuseStep 46613663 = 69920495) B69920495
theorem B31075775 : Blo 1889435 31075775 := bstep (se 1 (by rfl) ⟨23306831, by rfl⟩ : syracuseStep 31075775 = 46613663) B46613663
theorem B20717183 : Blo 1889435 20717183 := bstep (se 1 (by rfl) ⟨15537887, by rfl⟩ : syracuseStep 20717183 = 31075775) B31075775
theorem B13811455 : Blo 1889435 13811455 := bstep (se 1 (by rfl) ⟨10358591, by rfl⟩ : syracuseStep 13811455 = 20717183) B20717183
theorem B18415273 : Blo 1889435 18415273 := bstep (se 2 (by rfl) ⟨6905727, by rfl⟩ : syracuseStep 18415273 = 13811455) B13811455
theorem B24553697 : Blo 1889435 24553697 := bstep (se 2 (by rfl) ⟨9207636, by rfl⟩ : syracuseStep 24553697 = 18415273) B18415273
theorem B65476525 : Blo 1889435 65476525 := bstep (se 3 (by rfl) ⟨12276848, by rfl⟩ : syracuseStep 65476525 = 24553697) B24553697
theorem B87302033 : Blo 1889435 87302033 := bstep (se 2 (by rfl) ⟨32738262, by rfl⟩ : syracuseStep 87302033 = 65476525) B65476525
theorem B58201355 : Blo 1889435 58201355 := bstep (se 1 (by rfl) ⟨43651016, by rfl⟩ : syracuseStep 58201355 = 87302033) B87302033
theorem B155203613 : Blo 1889435 155203613 := bstep (se 3 (by rfl) ⟨29100677, by rfl⟩ : syracuseStep 155203613 = 58201355) B58201355
theorem B103469075 : Blo 1889435 103469075 := bstep (se 1 (by rfl) ⟨77601806, by rfl⟩ : syracuseStep 103469075 = 155203613) B155203613
theorem B68979383 : Blo 1889435 68979383 := bstep (se 1 (by rfl) ⟨51734537, by rfl⟩ : syracuseStep 68979383 = 103469075) B103469075
theorem B45986255 : Blo 1889435 45986255 := bstep (se 1 (by rfl) ⟨34489691, by rfl⟩ : syracuseStep 45986255 = 68979383) B68979383
theorem B30657503 : Blo 1889435 30657503 := bstep (se 1 (by rfl) ⟨22993127, by rfl⟩ : syracuseStep 30657503 = 45986255) B45986255
theorem B20438335 : Blo 1889435 20438335 := bstep (se 1 (by rfl) ⟨15328751, by rfl⟩ : syracuseStep 20438335 = 30657503) B30657503
theorem B109004453 : Blo 1889435 109004453 := bstep (se 4 (by rfl) ⟨10219167, by rfl⟩ : syracuseStep 109004453 = 20438335) B20438335
theorem B72669635 : Blo 1889435 72669635 := bstep (se 1 (by rfl) ⟨54502226, by rfl⟩ : syracuseStep 72669635 = 109004453) B109004453
theorem B48446423 : Blo 1889435 48446423 := bstep (se 1 (by rfl) ⟨36334817, by rfl⟩ : syracuseStep 48446423 = 72669635) B72669635
theorem B32297615 : Blo 1889435 32297615 := bstep (se 1 (by rfl) ⟨24223211, by rfl⟩ : syracuseStep 32297615 = 48446423) B48446423
theorem B21531743 : Blo 1889435 21531743 := bstep (se 1 (by rfl) ⟨16148807, by rfl⟩ : syracuseStep 21531743 = 32297615) B32297615
theorem B14354495 : Blo 1889435 14354495 := bstep (se 1 (by rfl) ⟨10765871, by rfl⟩ : syracuseStep 14354495 = 21531743) B21531743
theorem B9569663 : Blo 1889435 9569663 := bstep (se 1 (by rfl) ⟨7177247, by rfl⟩ : syracuseStep 9569663 = 14354495) B14354495
theorem B6379775 : Blo 1889435 6379775 := bstep (se 1 (by rfl) ⟨4784831, by rfl⟩ : syracuseStep 6379775 = 9569663) B9569663
theorem B4253183 : Blo 1889435 4253183 := bstep (se 1 (by rfl) ⟨3189887, by rfl⟩ : syracuseStep 4253183 = 6379775) B6379775
theorem B2835455 : Blo 1889435 2835455 := bstep (se 1 (by rfl) ⟨2126591, by rfl⟩ : syracuseStep 2835455 = 4253183) B4253183
theorem B1890303 : Blo 1889435 1890303 := bstep (se 1 (by rfl) ⟨1417727, by rfl⟩ : syracuseStep 1890303 = 2835455) B2835455
theorem B2835461 : Blo 1889435 2835461 := bbase (se 4 (by rfl) ⟨265824, by rfl⟩ : syracuseStep 2835461 = 531649) (by norm_num)
theorem B1890307 : Blo 1889435 1890307 := bstep (se 1 (by rfl) ⟨1417730, by rfl⟩ : syracuseStep 1890307 = 2835461) B2835461
theorem B3189901 : Blo 1889435 3189901 := bbase (se 3 (by rfl) ⟨598106, by rfl⟩ : syracuseStep 3189901 = 1196213) (by norm_num)
theorem B4253201 : Blo 1889435 4253201 := bstep (se 2 (by rfl) ⟨1594950, by rfl⟩ : syracuseStep 4253201 = 3189901) B3189901
theorem B2835467 : Blo 1889435 2835467 := bstep (se 1 (by rfl) ⟨2126600, by rfl⟩ : syracuseStep 2835467 = 4253201) B4253201
theorem B1890311 : Blo 1889435 1890311 := bstep (se 1 (by rfl) ⟨1417733, by rfl⟩ : syracuseStep 1890311 = 2835467) B2835467
theorem B2126605 : Blo 1889435 2126605 := bbase (se 3 (by rfl) ⟨398738, by rfl⟩ : syracuseStep 2126605 = 797477) (by norm_num)
theorem B2835473 : Blo 1889435 2835473 := bstep (se 2 (by rfl) ⟨1063302, by rfl⟩ : syracuseStep 2835473 = 2126605) B2126605
theorem B1890315 : Blo 1889435 1890315 := bstep (se 1 (by rfl) ⟨1417736, by rfl⟩ : syracuseStep 1890315 = 2835473) B2835473
theorem B6379829 : Blo 1889435 6379829 := bbase (se 5 (by rfl) ⟨299054, by rfl⟩ : syracuseStep 6379829 = 598109) (by norm_num)
theorem B4253219 : Blo 1889435 4253219 := bstep (se 1 (by rfl) ⟨3189914, by rfl⟩ : syracuseStep 4253219 = 6379829) B6379829
theorem B2835479 : Blo 1889435 2835479 := bstep (se 1 (by rfl) ⟨2126609, by rfl⟩ : syracuseStep 2835479 = 4253219) B4253219
theorem B1890319 : Blo 1889435 1890319 := bstep (se 1 (by rfl) ⟨1417739, by rfl⟩ : syracuseStep 1890319 = 2835479) B2835479
theorem B2835485 : Blo 1889435 2835485 := bbase (se 3 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 2835485 = 1063307) (by norm_num)
theorem B1890323 : Blo 1889435 1890323 := bstep (se 1 (by rfl) ⟨1417742, by rfl⟩ : syracuseStep 1890323 = 2835485) B2835485
theorem B4253237 : Blo 1889435 4253237 := bbase (se 5 (by rfl) ⟨199370, by rfl⟩ : syracuseStep 4253237 = 398741) (by norm_num)
theorem B2835491 : Blo 1889435 2835491 := bstep (se 1 (by rfl) ⟨2126618, by rfl⟩ : syracuseStep 2835491 = 4253237) B4253237
theorem B1890327 : Blo 1889435 1890327 := bstep (se 1 (by rfl) ⟨1417745, by rfl⟩ : syracuseStep 1890327 = 2835491) B2835491
theorem B4850189 : Blo 1889435 4850189 := bbase (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) (by norm_num)
theorem B3233459 : Blo 1889435 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B8622557 : Blo 1889435 8622557 := bstep (se 3 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 8622557 = 3233459) B3233459
theorem B5748371 : Blo 1889435 5748371 := bstep (se 1 (by rfl) ⟨4311278, by rfl⟩ : syracuseStep 5748371 = 8622557) B8622557
theorem B3832247 : Blo 1889435 3832247 := bstep (se 1 (by rfl) ⟨2874185, by rfl⟩ : syracuseStep 3832247 = 5748371) B5748371
theorem B2554831 : Blo 1889435 2554831 := bstep (se 1 (by rfl) ⟨1916123, by rfl⟩ : syracuseStep 2554831 = 3832247) B3832247
theorem B3406441 : Blo 1889435 3406441 := bstep (se 2 (by rfl) ⟨1277415, by rfl⟩ : syracuseStep 3406441 = 2554831) B2554831
theorem B4541921 : Blo 1889435 4541921 := bstep (se 2 (by rfl) ⟨1703220, by rfl⟩ : syracuseStep 4541921 = 3406441) B3406441
theorem B3027947 : Blo 1889435 3027947 := bstep (se 1 (by rfl) ⟨2270960, by rfl⟩ : syracuseStep 3027947 = 4541921) B4541921
theorem B8074525 : Blo 1889435 8074525 := bstep (se 3 (by rfl) ⟨1513973, by rfl⟩ : syracuseStep 8074525 = 3027947) B3027947
theorem B10766033 : Blo 1889435 10766033 := bstep (se 2 (by rfl) ⟨4037262, by rfl⟩ : syracuseStep 10766033 = 8074525) B8074525
theorem B7177355 : Blo 1889435 7177355 := bstep (se 1 (by rfl) ⟨5383016, by rfl⟩ : syracuseStep 7177355 = 10766033) B10766033
theorem B4784903 : Blo 1889435 4784903 := bstep (se 1 (by rfl) ⟨3588677, by rfl⟩ : syracuseStep 4784903 = 7177355) B7177355
theorem B3189935 : Blo 1889435 3189935 := bstep (se 1 (by rfl) ⟨2392451, by rfl⟩ : syracuseStep 3189935 = 4784903) B4784903
theorem B2126623 : Blo 1889435 2126623 := bstep (se 1 (by rfl) ⟨1594967, by rfl⟩ : syracuseStep 2126623 = 3189935) B3189935
theorem B2835497 : Blo 1889435 2835497 := bstep (se 2 (by rfl) ⟨1063311, by rfl⟩ : syracuseStep 2835497 = 2126623) B2126623
theorem B1890331 : Blo 1889435 1890331 := bstep (se 1 (by rfl) ⟨1417748, by rfl⟩ : syracuseStep 1890331 = 2835497) B2835497
theorem B2270965 : Blo 1889435 2270965 := bbase (se 5 (by rfl) ⟨106451, by rfl⟩ : syracuseStep 2270965 = 212903) (by norm_num)
theorem B3027953 : Blo 1889435 3027953 := bstep (se 2 (by rfl) ⟨1135482, by rfl⟩ : syracuseStep 3027953 = 2270965) B2270965
theorem B8074541 : Blo 1889435 8074541 := bstep (se 3 (by rfl) ⟨1513976, by rfl⟩ : syracuseStep 8074541 = 3027953) B3027953
theorem B5383027 : Blo 1889435 5383027 := bstep (se 1 (by rfl) ⟨4037270, by rfl⟩ : syracuseStep 5383027 = 8074541) B8074541
theorem B7177369 : Blo 1889435 7177369 := bstep (se 2 (by rfl) ⟨2691513, by rfl⟩ : syracuseStep 7177369 = 5383027) B5383027
theorem B9569825 : Blo 1889435 9569825 := bstep (se 2 (by rfl) ⟨3588684, by rfl⟩ : syracuseStep 9569825 = 7177369) B7177369
theorem B6379883 : Blo 1889435 6379883 := bstep (se 1 (by rfl) ⟨4784912, by rfl⟩ : syracuseStep 6379883 = 9569825) B9569825
theorem B4253255 : Blo 1889435 4253255 := bstep (se 1 (by rfl) ⟨3189941, by rfl⟩ : syracuseStep 4253255 = 6379883) B6379883
theorem B2835503 : Blo 1889435 2835503 := bstep (se 1 (by rfl) ⟨2126627, by rfl⟩ : syracuseStep 2835503 = 4253255) B4253255
theorem B1890335 : Blo 1889435 1890335 := bstep (se 1 (by rfl) ⟨1417751, by rfl⟩ : syracuseStep 1890335 = 2835503) B2835503
theorem B2835509 : Blo 1889435 2835509 := bbase (se 5 (by rfl) ⟨132914, by rfl⟩ : syracuseStep 2835509 = 265829) (by norm_num)
theorem B1890339 : Blo 1889435 1890339 := bstep (se 1 (by rfl) ⟨1417754, by rfl⟩ : syracuseStep 1890339 = 2835509) B2835509
theorem B4784933 : Blo 1889435 4784933 := bbase (se 4 (by rfl) ⟨448587, by rfl⟩ : syracuseStep 4784933 = 897175) (by norm_num)
theorem B3189955 : Blo 1889435 3189955 := bstep (se 1 (by rfl) ⟨2392466, by rfl⟩ : syracuseStep 3189955 = 4784933) B4784933
theorem B4253273 : Blo 1889435 4253273 := bstep (se 2 (by rfl) ⟨1594977, by rfl⟩ : syracuseStep 4253273 = 3189955) B3189955
theorem B2835515 : Blo 1889435 2835515 := bstep (se 1 (by rfl) ⟨2126636, by rfl⟩ : syracuseStep 2835515 = 4253273) B4253273
theorem B1890343 : Blo 1889435 1890343 := bstep (se 1 (by rfl) ⟨1417757, by rfl⟩ : syracuseStep 1890343 = 2835515) B2835515
theorem B2126641 : Blo 1889435 2126641 := bbase (se 2 (by rfl) ⟨797490, by rfl⟩ : syracuseStep 2126641 = 1594981) (by norm_num)
theorem B2835521 : Blo 1889435 2835521 := bstep (se 2 (by rfl) ⟨1063320, by rfl⟩ : syracuseStep 2835521 = 2126641) B2126641
theorem B1890347 : Blo 1889435 1890347 := bstep (se 1 (by rfl) ⟨1417760, by rfl⟩ : syracuseStep 1890347 = 2835521) B2835521
theorem B3406477 : Blo 1889435 3406477 := bbase (se 3 (by rfl) ⟨638714, by rfl⟩ : syracuseStep 3406477 = 1277429) (by norm_num)
theorem B4541969 : Blo 1889435 4541969 := bstep (se 2 (by rfl) ⟨1703238, by rfl⟩ : syracuseStep 4541969 = 3406477) B3406477
theorem B3027979 : Blo 1889435 3027979 := bstep (se 1 (by rfl) ⟨2270984, by rfl⟩ : syracuseStep 3027979 = 4541969) B4541969
theorem B4037305 : Blo 1889435 4037305 := bstep (se 2 (by rfl) ⟨1513989, by rfl⟩ : syracuseStep 4037305 = 3027979) B3027979
theorem B5383073 : Blo 1889435 5383073 := bstep (se 2 (by rfl) ⟨2018652, by rfl⟩ : syracuseStep 5383073 = 4037305) B4037305
theorem B3588715 : Blo 1889435 3588715 := bstep (se 1 (by rfl) ⟨2691536, by rfl⟩ : syracuseStep 3588715 = 5383073) B5383073
theorem B4784953 : Blo 1889435 4784953 := bstep (se 2 (by rfl) ⟨1794357, by rfl⟩ : syracuseStep 4784953 = 3588715) B3588715
theorem B6379937 : Blo 1889435 6379937 := bstep (se 2 (by rfl) ⟨2392476, by rfl⟩ : syracuseStep 6379937 = 4784953) B4784953
theorem B4253291 : Blo 1889435 4253291 := bstep (se 1 (by rfl) ⟨3189968, by rfl⟩ : syracuseStep 4253291 = 6379937) B6379937
theorem B2835527 : Blo 1889435 2835527 := bstep (se 1 (by rfl) ⟨2126645, by rfl⟩ : syracuseStep 2835527 = 4253291) B4253291
theorem B1890351 : Blo 1889435 1890351 := bstep (se 1 (by rfl) ⟨1417763, by rfl⟩ : syracuseStep 1890351 = 2835527) B2835527
theorem B2835533 : Blo 1889435 2835533 := bbase (se 3 (by rfl) ⟨531662, by rfl⟩ : syracuseStep 2835533 = 1063325) (by norm_num)
theorem B1890355 : Blo 1889435 1890355 := bstep (se 1 (by rfl) ⟨1417766, by rfl⟩ : syracuseStep 1890355 = 2835533) B2835533
theorem B4253309 : Blo 1889435 4253309 := bbase (se 3 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 4253309 = 1594991) (by norm_num)
theorem B2835539 : Blo 1889435 2835539 := bstep (se 1 (by rfl) ⟨2126654, by rfl⟩ : syracuseStep 2835539 = 4253309) B4253309
theorem B1890359 : Blo 1889435 1890359 := bstep (se 1 (by rfl) ⟨1417769, by rfl⟩ : syracuseStep 1890359 = 2835539) B2835539
theorem B3189989 : Blo 1889435 3189989 := bbase (se 4 (by rfl) ⟨299061, by rfl⟩ : syracuseStep 3189989 = 598123) (by norm_num)
theorem B2126659 : Blo 1889435 2126659 := bstep (se 1 (by rfl) ⟨1594994, by rfl⟩ : syracuseStep 2126659 = 3189989) B3189989
theorem B2835545 : Blo 1889435 2835545 := bstep (se 2 (by rfl) ⟨1063329, by rfl⟩ : syracuseStep 2835545 = 2126659) B2126659
theorem B1890363 : Blo 1889435 1890363 := bstep (se 1 (by rfl) ⟨1417772, by rfl⟩ : syracuseStep 1890363 = 2835545) B2835545
theorem B4490245 : Blo 1889435 4490245 := bbase (se 4 (by rfl) ⟨420960, by rfl⟩ : syracuseStep 4490245 = 841921) (by norm_num)
theorem B5986993 : Blo 1889435 5986993 := bstep (se 2 (by rfl) ⟨2245122, by rfl⟩ : syracuseStep 5986993 = 4490245) B4490245
theorem B7982657 : Blo 1889435 7982657 := bstep (se 2 (by rfl) ⟨2993496, by rfl⟩ : syracuseStep 7982657 = 5986993) B5986993
theorem B5321771 : Blo 1889435 5321771 := bstep (se 1 (by rfl) ⟨3991328, by rfl⟩ : syracuseStep 5321771 = 7982657) B7982657
theorem B3547847 : Blo 1889435 3547847 := bstep (se 1 (by rfl) ⟨2660885, by rfl⟩ : syracuseStep 3547847 = 5321771) B5321771
theorem B9460925 : Blo 1889435 9460925 := bstep (se 3 (by rfl) ⟨1773923, by rfl⟩ : syracuseStep 9460925 = 3547847) B3547847
theorem B6307283 : Blo 1889435 6307283 := bstep (se 1 (by rfl) ⟨4730462, by rfl⟩ : syracuseStep 6307283 = 9460925) B9460925
theorem B4204855 : Blo 1889435 4204855 := bstep (se 1 (by rfl) ⟨3153641, by rfl⟩ : syracuseStep 4204855 = 6307283) B6307283
theorem B22425893 : Blo 1889435 22425893 := bstep (se 4 (by rfl) ⟨2102427, by rfl⟩ : syracuseStep 22425893 = 4204855) B4204855
theorem B14950595 : Blo 1889435 14950595 := bstep (se 1 (by rfl) ⟨11212946, by rfl⟩ : syracuseStep 14950595 = 22425893) B22425893
theorem B9967063 : Blo 1889435 9967063 := bstep (se 1 (by rfl) ⟨7475297, by rfl⟩ : syracuseStep 9967063 = 14950595) B14950595
theorem B13289417 : Blo 1889435 13289417 := bstep (se 2 (by rfl) ⟨4983531, by rfl⟩ : syracuseStep 13289417 = 9967063) B9967063
theorem B8859611 : Blo 1889435 8859611 := bstep (se 1 (by rfl) ⟨6644708, by rfl⟩ : syracuseStep 8859611 = 13289417) B13289417
theorem B5906407 : Blo 1889435 5906407 := bstep (se 1 (by rfl) ⟨4429805, by rfl⟩ : syracuseStep 5906407 = 8859611) B8859611
theorem B7875209 : Blo 1889435 7875209 := bstep (se 2 (by rfl) ⟨2953203, by rfl⟩ : syracuseStep 7875209 = 5906407) B5906407
theorem B21000557 : Blo 1889435 21000557 := bstep (se 3 (by rfl) ⟨3937604, by rfl⟩ : syracuseStep 21000557 = 7875209) B7875209
theorem B14000371 : Blo 1889435 14000371 := bstep (se 1 (by rfl) ⟨10500278, by rfl⟩ : syracuseStep 14000371 = 21000557) B21000557
theorem B74668645 : Blo 1889435 74668645 := bstep (se 4 (by rfl) ⟨7000185, by rfl⟩ : syracuseStep 74668645 = 14000371) B14000371
theorem B99558193 : Blo 1889435 99558193 := bstep (se 2 (by rfl) ⟨37334322, by rfl⟩ : syracuseStep 99558193 = 74668645) B74668645
theorem B132744257 : Blo 1889435 132744257 := bstep (se 2 (by rfl) ⟨49779096, by rfl⟩ : syracuseStep 132744257 = 99558193) B99558193
theorem B88496171 : Blo 1889435 88496171 := bstep (se 1 (by rfl) ⟨66372128, by rfl⟩ : syracuseStep 88496171 = 132744257) B132744257
theorem B58997447 : Blo 1889435 58997447 := bstep (se 1 (by rfl) ⟨44248085, by rfl⟩ : syracuseStep 58997447 = 88496171) B88496171
theorem B39331631 : Blo 1889435 39331631 := bstep (se 1 (by rfl) ⟨29498723, by rfl⟩ : syracuseStep 39331631 = 58997447) B58997447
theorem B26221087 : Blo 1889435 26221087 := bstep (se 1 (by rfl) ⟨19665815, by rfl⟩ : syracuseStep 26221087 = 39331631) B39331631
theorem B34961449 : Blo 1889435 34961449 := bstep (se 2 (by rfl) ⟨13110543, by rfl⟩ : syracuseStep 34961449 = 26221087) B26221087
theorem B46615265 : Blo 1889435 46615265 := bstep (se 2 (by rfl) ⟨17480724, by rfl⟩ : syracuseStep 46615265 = 34961449) B34961449
theorem B31076843 : Blo 1889435 31076843 := bstep (se 1 (by rfl) ⟨23307632, by rfl⟩ : syracuseStep 31076843 = 46615265) B46615265
theorem B82871581 : Blo 1889435 82871581 := bstep (se 3 (by rfl) ⟨15538421, by rfl⟩ : syracuseStep 82871581 = 31076843) B31076843
theorem B110495441 : Blo 1889435 110495441 := bstep (se 2 (by rfl) ⟨41435790, by rfl⟩ : syracuseStep 110495441 = 82871581) B82871581
theorem B73663627 : Blo 1889435 73663627 := bstep (se 1 (by rfl) ⟨55247720, by rfl⟩ : syracuseStep 73663627 = 110495441) B110495441
theorem B98218169 : Blo 1889435 98218169 := bstep (se 2 (by rfl) ⟨36831813, by rfl⟩ : syracuseStep 98218169 = 73663627) B73663627
theorem B65478779 : Blo 1889435 65478779 := bstep (se 1 (by rfl) ⟨49109084, by rfl⟩ : syracuseStep 65478779 = 98218169) B98218169
theorem B43652519 : Blo 1889435 43652519 := bstep (se 1 (by rfl) ⟨32739389, by rfl⟩ : syracuseStep 43652519 = 65478779) B65478779
theorem B29101679 : Blo 1889435 29101679 := bstep (se 1 (by rfl) ⟨21826259, by rfl⟩ : syracuseStep 29101679 = 43652519) B43652519
theorem B19401119 : Blo 1889435 19401119 := bstep (se 1 (by rfl) ⟨14550839, by rfl⟩ : syracuseStep 19401119 = 29101679) B29101679
theorem B12934079 : Blo 1889435 12934079 := bstep (se 1 (by rfl) ⟨9700559, by rfl⟩ : syracuseStep 12934079 = 19401119) B19401119
theorem B8622719 : Blo 1889435 8622719 := bstep (se 1 (by rfl) ⟨6467039, by rfl⟩ : syracuseStep 8622719 = 12934079) B12934079
theorem B5748479 : Blo 1889435 5748479 := bstep (se 1 (by rfl) ⟨4311359, by rfl⟩ : syracuseStep 5748479 = 8622719) B8622719
theorem B3832319 : Blo 1889435 3832319 := bstep (se 1 (by rfl) ⟨2874239, by rfl⟩ : syracuseStep 3832319 = 5748479) B5748479
theorem B10219517 : Blo 1889435 10219517 := bstep (se 3 (by rfl) ⟨1916159, by rfl⟩ : syracuseStep 10219517 = 3832319) B3832319
theorem B6813011 : Blo 1889435 6813011 := bstep (se 1 (by rfl) ⟨5109758, by rfl⟩ : syracuseStep 6813011 = 10219517) B10219517
theorem B4542007 : Blo 1889435 4542007 := bstep (se 1 (by rfl) ⟨3406505, by rfl⟩ : syracuseStep 4542007 = 6813011) B6813011
theorem B6056009 : Blo 1889435 6056009 := bstep (se 2 (by rfl) ⟨2271003, by rfl⟩ : syracuseStep 6056009 = 4542007) B4542007
theorem B4037339 : Blo 1889435 4037339 := bstep (se 1 (by rfl) ⟨3028004, by rfl⟩ : syracuseStep 4037339 = 6056009) B6056009
theorem B2691559 : Blo 1889435 2691559 := bstep (se 1 (by rfl) ⟨2018669, by rfl⟩ : syracuseStep 2691559 = 4037339) B4037339
theorem B14354981 : Blo 1889435 14354981 := bstep (se 4 (by rfl) ⟨1345779, by rfl⟩ : syracuseStep 14354981 = 2691559) B2691559
theorem B9569987 : Blo 1889435 9569987 := bstep (se 1 (by rfl) ⟨7177490, by rfl⟩ : syracuseStep 9569987 = 14354981) B14354981
theorem B6379991 : Blo 1889435 6379991 := bstep (se 1 (by rfl) ⟨4784993, by rfl⟩ : syracuseStep 6379991 = 9569987) B9569987
theorem B4253327 : Blo 1889435 4253327 := bstep (se 1 (by rfl) ⟨3189995, by rfl⟩ : syracuseStep 4253327 = 6379991) B6379991
theorem B2835551 : Blo 1889435 2835551 := bstep (se 1 (by rfl) ⟨2126663, by rfl⟩ : syracuseStep 2835551 = 4253327) B4253327
theorem B1890367 : Blo 1889435 1890367 := bstep (se 1 (by rfl) ⟨1417775, by rfl⟩ : syracuseStep 1890367 = 2835551) B2835551
theorem B2835557 : Blo 1889435 2835557 := bbase (se 4 (by rfl) ⟨265833, by rfl⟩ : syracuseStep 2835557 = 531667) (by norm_num)
theorem B1890371 : Blo 1889435 1890371 := bstep (se 1 (by rfl) ⟨1417778, by rfl⟩ : syracuseStep 1890371 = 2835557) B2835557
theorem B4037357 : Blo 1889435 4037357 := bbase (se 3 (by rfl) ⟨757004, by rfl⟩ : syracuseStep 4037357 = 1514009) (by norm_num)
theorem B2691571 : Blo 1889435 2691571 := bstep (se 1 (by rfl) ⟨2018678, by rfl⟩ : syracuseStep 2691571 = 4037357) B4037357
theorem B3588761 : Blo 1889435 3588761 := bstep (se 2 (by rfl) ⟨1345785, by rfl⟩ : syracuseStep 3588761 = 2691571) B2691571
theorem B2392507 : Blo 1889435 2392507 := bstep (se 1 (by rfl) ⟨1794380, by rfl⟩ : syracuseStep 2392507 = 3588761) B3588761
theorem B3190009 : Blo 1889435 3190009 := bstep (se 2 (by rfl) ⟨1196253, by rfl⟩ : syracuseStep 3190009 = 2392507) B2392507
theorem B4253345 : Blo 1889435 4253345 := bstep (se 2 (by rfl) ⟨1595004, by rfl⟩ : syracuseStep 4253345 = 3190009) B3190009
theorem B2835563 : Blo 1889435 2835563 := bstep (se 1 (by rfl) ⟨2126672, by rfl⟩ : syracuseStep 2835563 = 4253345) B4253345
theorem B1890375 : Blo 1889435 1890375 := bstep (se 1 (by rfl) ⟨1417781, by rfl⟩ : syracuseStep 1890375 = 2835563) B2835563
theorem B2126677 : Blo 1889435 2126677 := bbase (se 9 (by rfl) ⟨6230, by rfl⟩ : syracuseStep 2126677 = 12461) (by norm_num)
theorem B2835569 : Blo 1889435 2835569 := bstep (se 2 (by rfl) ⟨1063338, by rfl⟩ : syracuseStep 2835569 = 2126677) B2126677
theorem B1890379 : Blo 1889435 1890379 := bstep (se 1 (by rfl) ⟨1417784, by rfl⟩ : syracuseStep 1890379 = 2835569) B2835569
theorem B2392517 : Blo 1889435 2392517 := bbase (se 4 (by rfl) ⟨224298, by rfl⟩ : syracuseStep 2392517 = 448597) (by norm_num)
theorem B6380045 : Blo 1889435 6380045 := bstep (se 3 (by rfl) ⟨1196258, by rfl⟩ : syracuseStep 6380045 = 2392517) B2392517
theorem B4253363 : Blo 1889435 4253363 := bstep (se 1 (by rfl) ⟨3190022, by rfl⟩ : syracuseStep 4253363 = 6380045) B6380045
theorem B2835575 : Blo 1889435 2835575 := bstep (se 1 (by rfl) ⟨2126681, by rfl⟩ : syracuseStep 2835575 = 4253363) B4253363
theorem B1890383 : Blo 1889435 1890383 := bstep (se 1 (by rfl) ⟨1417787, by rfl⟩ : syracuseStep 1890383 = 2835575) B2835575
theorem B2835581 : Blo 1889435 2835581 := bbase (se 3 (by rfl) ⟨531671, by rfl⟩ : syracuseStep 2835581 = 1063343) (by norm_num)
theorem B1890387 : Blo 1889435 1890387 := bstep (se 1 (by rfl) ⟨1417790, by rfl⟩ : syracuseStep 1890387 = 2835581) B2835581
theorem B4253381 : Blo 1889435 4253381 := bbase (se 4 (by rfl) ⟨398754, by rfl⟩ : syracuseStep 4253381 = 797509) (by norm_num)
theorem B2835587 : Blo 1889435 2835587 := bstep (se 1 (by rfl) ⟨2126690, by rfl⟩ : syracuseStep 2835587 = 4253381) B4253381
theorem B1890391 : Blo 1889435 1890391 := bstep (se 1 (by rfl) ⟨1417793, by rfl⟩ : syracuseStep 1890391 = 2835587) B2835587
theorem B3277685 : Blo 1889435 3277685 := bbase (se 5 (by rfl) ⟨153641, by rfl⟩ : syracuseStep 3277685 = 307283) (by norm_num)
theorem B8740493 : Blo 1889435 8740493 := bstep (se 3 (by rfl) ⟨1638842, by rfl⟩ : syracuseStep 8740493 = 3277685) B3277685
theorem B5826995 : Blo 1889435 5826995 := bstep (se 1 (by rfl) ⟨4370246, by rfl⟩ : syracuseStep 5826995 = 8740493) B8740493
theorem B3884663 : Blo 1889435 3884663 := bstep (se 1 (by rfl) ⟨2913497, by rfl⟩ : syracuseStep 3884663 = 5826995) B5826995
theorem B2589775 : Blo 1889435 2589775 := bstep (se 1 (by rfl) ⟨1942331, by rfl⟩ : syracuseStep 2589775 = 3884663) B3884663
theorem B13812133 : Blo 1889435 13812133 := bstep (se 4 (by rfl) ⟨1294887, by rfl⟩ : syracuseStep 13812133 = 2589775) B2589775
theorem B18416177 : Blo 1889435 18416177 := bstep (se 2 (by rfl) ⟨6906066, by rfl⟩ : syracuseStep 18416177 = 13812133) B13812133
theorem B12277451 : Blo 1889435 12277451 := bstep (se 1 (by rfl) ⟨9208088, by rfl⟩ : syracuseStep 12277451 = 18416177) B18416177
theorem B32739869 : Blo 1889435 32739869 := bstep (se 3 (by rfl) ⟨6138725, by rfl⟩ : syracuseStep 32739869 = 12277451) B12277451
theorem B21826579 : Blo 1889435 21826579 := bstep (se 1 (by rfl) ⟨16369934, by rfl⟩ : syracuseStep 21826579 = 32739869) B32739869
theorem B29102105 : Blo 1889435 29102105 := bstep (se 2 (by rfl) ⟨10913289, by rfl⟩ : syracuseStep 29102105 = 21826579) B21826579
theorem B77605613 : Blo 1889435 77605613 := bstep (se 3 (by rfl) ⟨14551052, by rfl⟩ : syracuseStep 77605613 = 29102105) B29102105
theorem B51737075 : Blo 1889435 51737075 := bstep (se 1 (by rfl) ⟨38802806, by rfl⟩ : syracuseStep 51737075 = 77605613) B77605613
theorem B34491383 : Blo 1889435 34491383 := bstep (se 1 (by rfl) ⟨25868537, by rfl⟩ : syracuseStep 34491383 = 51737075) B51737075
theorem B22994255 : Blo 1889435 22994255 := bstep (se 1 (by rfl) ⟨17245691, by rfl⟩ : syracuseStep 22994255 = 34491383) B34491383
theorem B15329503 : Blo 1889435 15329503 := bstep (se 1 (by rfl) ⟨11497127, by rfl⟩ : syracuseStep 15329503 = 22994255) B22994255
theorem B20439337 : Blo 1889435 20439337 := bstep (se 2 (by rfl) ⟨7664751, by rfl⟩ : syracuseStep 20439337 = 15329503) B15329503
theorem B27252449 : Blo 1889435 27252449 := bstep (se 2 (by rfl) ⟨10219668, by rfl⟩ : syracuseStep 27252449 = 20439337) B20439337
theorem B18168299 : Blo 1889435 18168299 := bstep (se 1 (by rfl) ⟨13626224, by rfl⟩ : syracuseStep 18168299 = 27252449) B27252449
theorem B12112199 : Blo 1889435 12112199 := bstep (se 1 (by rfl) ⟨9084149, by rfl⟩ : syracuseStep 12112199 = 18168299) B18168299
theorem B8074799 : Blo 1889435 8074799 := bstep (se 1 (by rfl) ⟨6056099, by rfl⟩ : syracuseStep 8074799 = 12112199) B12112199
theorem B5383199 : Blo 1889435 5383199 := bstep (se 1 (by rfl) ⟨4037399, by rfl⟩ : syracuseStep 5383199 = 8074799) B8074799
theorem B3588799 : Blo 1889435 3588799 := bstep (se 1 (by rfl) ⟨2691599, by rfl⟩ : syracuseStep 3588799 = 5383199) B5383199
theorem B4785065 : Blo 1889435 4785065 := bstep (se 2 (by rfl) ⟨1794399, by rfl⟩ : syracuseStep 4785065 = 3588799) B3588799
theorem B3190043 : Blo 1889435 3190043 := bstep (se 1 (by rfl) ⟨2392532, by rfl⟩ : syracuseStep 3190043 = 4785065) B4785065
theorem B2126695 : Blo 1889435 2126695 := bstep (se 1 (by rfl) ⟨1595021, by rfl⟩ : syracuseStep 2126695 = 3190043) B3190043
theorem B2835593 : Blo 1889435 2835593 := bstep (se 2 (by rfl) ⟨1063347, by rfl⟩ : syracuseStep 2835593 = 2126695) B2126695
theorem B1890395 : Blo 1889435 1890395 := bstep (se 1 (by rfl) ⟨1417796, by rfl⟩ : syracuseStep 1890395 = 2835593) B2835593
theorem B9570149 : Blo 1889435 9570149 := bbase (se 4 (by rfl) ⟨897201, by rfl⟩ : syracuseStep 9570149 = 1794403) (by norm_num)
theorem B6380099 : Blo 1889435 6380099 := bstep (se 1 (by rfl) ⟨4785074, by rfl⟩ : syracuseStep 6380099 = 9570149) B9570149
theorem B4253399 : Blo 1889435 4253399 := bstep (se 1 (by rfl) ⟨3190049, by rfl⟩ : syracuseStep 4253399 = 6380099) B6380099
theorem B2835599 : Blo 1889435 2835599 := bstep (se 1 (by rfl) ⟨2126699, by rfl⟩ : syracuseStep 2835599 = 4253399) B4253399
theorem B1890399 : Blo 1889435 1890399 := bstep (se 1 (by rfl) ⟨1417799, by rfl⟩ : syracuseStep 1890399 = 2835599) B2835599
theorem B2835605 : Blo 1889435 2835605 := bbase (se 6 (by rfl) ⟨66459, by rfl⟩ : syracuseStep 2835605 = 132919) (by norm_num)
theorem B1890403 : Blo 1889435 1890403 := bstep (se 1 (by rfl) ⟨1417802, by rfl⟩ : syracuseStep 1890403 = 2835605) B2835605
theorem B10219733 : Blo 1889435 10219733 := bbase (se 7 (by rfl) ⟨119762, by rfl⟩ : syracuseStep 10219733 = 239525) (by norm_num)
theorem B6813155 : Blo 1889435 6813155 := bstep (se 1 (by rfl) ⟨5109866, by rfl⟩ : syracuseStep 6813155 = 10219733) B10219733
theorem B4542103 : Blo 1889435 4542103 := bstep (se 1 (by rfl) ⟨3406577, by rfl⟩ : syracuseStep 4542103 = 6813155) B6813155
theorem B6056137 : Blo 1889435 6056137 := bstep (se 2 (by rfl) ⟨2271051, by rfl⟩ : syracuseStep 6056137 = 4542103) B4542103
theorem B8074849 : Blo 1889435 8074849 := bstep (se 2 (by rfl) ⟨3028068, by rfl⟩ : syracuseStep 8074849 = 6056137) B6056137
theorem B10766465 : Blo 1889435 10766465 := bstep (se 2 (by rfl) ⟨4037424, by rfl⟩ : syracuseStep 10766465 = 8074849) B8074849
theorem B7177643 : Blo 1889435 7177643 := bstep (se 1 (by rfl) ⟨5383232, by rfl⟩ : syracuseStep 7177643 = 10766465) B10766465
theorem B4785095 : Blo 1889435 4785095 := bstep (se 1 (by rfl) ⟨3588821, by rfl⟩ : syracuseStep 4785095 = 7177643) B7177643
theorem B3190063 : Blo 1889435 3190063 := bstep (se 1 (by rfl) ⟨2392547, by rfl⟩ : syracuseStep 3190063 = 4785095) B4785095
theorem B4253417 : Blo 1889435 4253417 := bstep (se 2 (by rfl) ⟨1595031, by rfl⟩ : syracuseStep 4253417 = 3190063) B3190063
theorem B2835611 : Blo 1889435 2835611 := bstep (se 1 (by rfl) ⟨2126708, by rfl⟩ : syracuseStep 2835611 = 4253417) B4253417
theorem B1890407 : Blo 1889435 1890407 := bstep (se 1 (by rfl) ⟨1417805, by rfl⟩ : syracuseStep 1890407 = 2835611) B2835611
theorem B2126713 : Blo 1889435 2126713 := bbase (se 2 (by rfl) ⟨797517, by rfl⟩ : syracuseStep 2126713 = 1595035) (by norm_num)
theorem B2835617 : Blo 1889435 2835617 := bstep (se 2 (by rfl) ⟨1063356, by rfl⟩ : syracuseStep 2835617 = 2126713) B2126713
theorem B1890411 : Blo 1889435 1890411 := bstep (se 1 (by rfl) ⟨1417808, by rfl⟩ : syracuseStep 1890411 = 2835617) B2835617
theorem B2271061 : Blo 1889435 2271061 := bbase (se 9 (by rfl) ⟨6653, by rfl⟩ : syracuseStep 2271061 = 13307) (by norm_num)
theorem B12112325 : Blo 1889435 12112325 := bstep (se 4 (by rfl) ⟨1135530, by rfl⟩ : syracuseStep 12112325 = 2271061) B2271061
theorem B8074883 : Blo 1889435 8074883 := bstep (se 1 (by rfl) ⟨6056162, by rfl⟩ : syracuseStep 8074883 = 12112325) B12112325
theorem B5383255 : Blo 1889435 5383255 := bstep (se 1 (by rfl) ⟨4037441, by rfl⟩ : syracuseStep 5383255 = 8074883) B8074883
theorem B7177673 : Blo 1889435 7177673 := bstep (se 2 (by rfl) ⟨2691627, by rfl⟩ : syracuseStep 7177673 = 5383255) B5383255
theorem B4785115 : Blo 1889435 4785115 := bstep (se 1 (by rfl) ⟨3588836, by rfl⟩ : syracuseStep 4785115 = 7177673) B7177673
theorem B6380153 : Blo 1889435 6380153 := bstep (se 2 (by rfl) ⟨2392557, by rfl⟩ : syracuseStep 6380153 = 4785115) B4785115
theorem B4253435 : Blo 1889435 4253435 := bstep (se 1 (by rfl) ⟨3190076, by rfl⟩ : syracuseStep 4253435 = 6380153) B6380153
theorem B2835623 : Blo 1889435 2835623 := bstep (se 1 (by rfl) ⟨2126717, by rfl⟩ : syracuseStep 2835623 = 4253435) B4253435
theorem B1890415 : Blo 1889435 1890415 := bstep (se 1 (by rfl) ⟨1417811, by rfl⟩ : syracuseStep 1890415 = 2835623) B2835623
theorem B2835629 : Blo 1889435 2835629 := bbase (se 3 (by rfl) ⟨531680, by rfl⟩ : syracuseStep 2835629 = 1063361) (by norm_num)
theorem B1890419 : Blo 1889435 1890419 := bstep (se 1 (by rfl) ⟨1417814, by rfl⟩ : syracuseStep 1890419 = 2835629) B2835629
theorem B4253453 : Blo 1889435 4253453 := bbase (se 3 (by rfl) ⟨797522, by rfl⟩ : syracuseStep 4253453 = 1595045) (by norm_num)
theorem B2835635 : Blo 1889435 2835635 := bstep (se 1 (by rfl) ⟨2126726, by rfl⟩ : syracuseStep 2835635 = 4253453) B4253453
theorem B1890423 : Blo 1889435 1890423 := bstep (se 1 (by rfl) ⟨1417817, by rfl⟩ : syracuseStep 1890423 = 2835635) B2835635
theorem B2392573 : Blo 1889435 2392573 := bbase (se 3 (by rfl) ⟨448607, by rfl⟩ : syracuseStep 2392573 = 897215) (by norm_num)
theorem B3190097 : Blo 1889435 3190097 := bstep (se 2 (by rfl) ⟨1196286, by rfl⟩ : syracuseStep 3190097 = 2392573) B2392573
theorem B2126731 : Blo 1889435 2126731 := bstep (se 1 (by rfl) ⟨1595048, by rfl⟩ : syracuseStep 2126731 = 3190097) B3190097
theorem B2835641 : Blo 1889435 2835641 := bstep (se 2 (by rfl) ⟨1063365, by rfl⟩ : syracuseStep 2835641 = 2126731) B2126731
theorem B1890427 : Blo 1889435 1890427 := bstep (se 1 (by rfl) ⟨1417820, by rfl⟩ : syracuseStep 1890427 = 2835641) B2835641
theorem B6056213 : Blo 1889435 6056213 := bbase (se 6 (by rfl) ⟨141942, by rfl⟩ : syracuseStep 6056213 = 283885) (by norm_num)
theorem B16149901 : Blo 1889435 16149901 := bstep (se 3 (by rfl) ⟨3028106, by rfl⟩ : syracuseStep 16149901 = 6056213) B6056213
theorem B21533201 : Blo 1889435 21533201 := bstep (se 2 (by rfl) ⟨8074950, by rfl⟩ : syracuseStep 21533201 = 16149901) B16149901
theorem B14355467 : Blo 1889435 14355467 := bstep (se 1 (by rfl) ⟨10766600, by rfl⟩ : syracuseStep 14355467 = 21533201) B21533201
theorem B9570311 : Blo 1889435 9570311 := bstep (se 1 (by rfl) ⟨7177733, by rfl⟩ : syracuseStep 9570311 = 14355467) B14355467
theorem B6380207 : Blo 1889435 6380207 := bstep (se 1 (by rfl) ⟨4785155, by rfl⟩ : syracuseStep 6380207 = 9570311) B9570311
theorem B4253471 : Blo 1889435 4253471 := bstep (se 1 (by rfl) ⟨3190103, by rfl⟩ : syracuseStep 4253471 = 6380207) B6380207
theorem B2835647 : Blo 1889435 2835647 := bstep (se 1 (by rfl) ⟨2126735, by rfl⟩ : syracuseStep 2835647 = 4253471) B4253471
theorem B1890431 : Blo 1889435 1890431 := bstep (se 1 (by rfl) ⟨1417823, by rfl⟩ : syracuseStep 1890431 = 2835647) B2835647
theorem B2835653 : Blo 1889435 2835653 := bbase (se 4 (by rfl) ⟨265842, by rfl⟩ : syracuseStep 2835653 = 531685) (by norm_num)
theorem B1890435 : Blo 1889435 1890435 := bstep (se 1 (by rfl) ⟨1417826, by rfl⟩ : syracuseStep 1890435 = 2835653) B2835653
theorem B3190117 : Blo 1889435 3190117 := bbase (se 4 (by rfl) ⟨299073, by rfl⟩ : syracuseStep 3190117 = 598147) (by norm_num)
theorem B4253489 : Blo 1889435 4253489 := bstep (se 2 (by rfl) ⟨1595058, by rfl⟩ : syracuseStep 4253489 = 3190117) B3190117
theorem B2835659 : Blo 1889435 2835659 := bstep (se 1 (by rfl) ⟨2126744, by rfl⟩ : syracuseStep 2835659 = 4253489) B4253489
theorem B1890439 : Blo 1889435 1890439 := bstep (se 1 (by rfl) ⟨1417829, by rfl⟩ : syracuseStep 1890439 = 2835659) B2835659
theorem B2126749 : Blo 1889435 2126749 := bbase (se 3 (by rfl) ⟨398765, by rfl⟩ : syracuseStep 2126749 = 797531) (by norm_num)
theorem B2835665 : Blo 1889435 2835665 := bstep (se 2 (by rfl) ⟨1063374, by rfl⟩ : syracuseStep 2835665 = 2126749) B2126749
theorem B1890443 : Blo 1889435 1890443 := bstep (se 1 (by rfl) ⟨1417832, by rfl⟩ : syracuseStep 1890443 = 2835665) B2835665
theorem B6380261 : Blo 1889435 6380261 := bbase (se 4 (by rfl) ⟨598149, by rfl⟩ : syracuseStep 6380261 = 1196299) (by norm_num)
theorem B4253507 : Blo 1889435 4253507 := bstep (se 1 (by rfl) ⟨3190130, by rfl⟩ : syracuseStep 4253507 = 6380261) B6380261
theorem B2835671 : Blo 1889435 2835671 := bstep (se 1 (by rfl) ⟨2126753, by rfl⟩ : syracuseStep 2835671 = 4253507) B4253507
theorem B1890447 : Blo 1889435 1890447 := bstep (se 1 (by rfl) ⟨1417835, by rfl⟩ : syracuseStep 1890447 = 2835671) B2835671
theorem B2835677 : Blo 1889435 2835677 := bbase (se 3 (by rfl) ⟨531689, by rfl⟩ : syracuseStep 2835677 = 1063379) (by norm_num)
theorem B1890451 : Blo 1889435 1890451 := bstep (se 1 (by rfl) ⟨1417838, by rfl⟩ : syracuseStep 1890451 = 2835677) B2835677
theorem B4253525 : Blo 1889435 4253525 := bbase (se 9 (by rfl) ⟨12461, by rfl⟩ : syracuseStep 4253525 = 24923) (by norm_num)
theorem B2835683 : Blo 1889435 2835683 := bstep (se 1 (by rfl) ⟨2126762, by rfl⟩ : syracuseStep 2835683 = 4253525) B4253525
theorem B1890455 : Blo 1889435 1890455 := bstep (se 1 (by rfl) ⟨1417841, by rfl⟩ : syracuseStep 1890455 = 2835683) B2835683
theorem B5383381 : Blo 1889435 5383381 := bbase (se 7 (by rfl) ⟨63086, by rfl⟩ : syracuseStep 5383381 = 126173) (by norm_num)
theorem B7177841 : Blo 1889435 7177841 := bstep (se 2 (by rfl) ⟨2691690, by rfl⟩ : syracuseStep 7177841 = 5383381) B5383381
theorem B4785227 : Blo 1889435 4785227 := bstep (se 1 (by rfl) ⟨3588920, by rfl⟩ : syracuseStep 4785227 = 7177841) B7177841
theorem B3190151 : Blo 1889435 3190151 := bstep (se 1 (by rfl) ⟨2392613, by rfl⟩ : syracuseStep 3190151 = 4785227) B4785227
theorem B2126767 : Blo 1889435 2126767 := bstep (se 1 (by rfl) ⟨1595075, by rfl⟩ : syracuseStep 2126767 = 3190151) B3190151
theorem B2835689 : Blo 1889435 2835689 := bstep (se 2 (by rfl) ⟨1063383, by rfl⟩ : syracuseStep 2835689 = 2126767) B2126767
theorem B1890459 : Blo 1889435 1890459 := bstep (se 1 (by rfl) ⟨1417844, by rfl⟩ : syracuseStep 1890459 = 2835689) B2835689
theorem B2185201 : Blo 1889435 2185201 := bbase (se 2 (by rfl) ⟨819450, by rfl⟩ : syracuseStep 2185201 = 1638901) (by norm_num)
theorem B11654405 : Blo 1889435 11654405 := bstep (se 4 (by rfl) ⟨1092600, by rfl⟩ : syracuseStep 11654405 = 2185201) B2185201
theorem B7769603 : Blo 1889435 7769603 := bstep (se 1 (by rfl) ⟨5827202, by rfl⟩ : syracuseStep 7769603 = 11654405) B11654405
theorem B5179735 : Blo 1889435 5179735 := bstep (se 1 (by rfl) ⟨3884801, by rfl⟩ : syracuseStep 5179735 = 7769603) B7769603
theorem B6906313 : Blo 1889435 6906313 := bstep (se 2 (by rfl) ⟨2589867, by rfl⟩ : syracuseStep 6906313 = 5179735) B5179735
theorem B9208417 : Blo 1889435 9208417 := bstep (se 2 (by rfl) ⟨3453156, by rfl⟩ : syracuseStep 9208417 = 6906313) B6906313
theorem B12277889 : Blo 1889435 12277889 := bstep (se 2 (by rfl) ⟨4604208, by rfl⟩ : syracuseStep 12277889 = 9208417) B9208417
theorem B8185259 : Blo 1889435 8185259 := bstep (se 1 (by rfl) ⟨6138944, by rfl⟩ : syracuseStep 8185259 = 12277889) B12277889
theorem B21827357 : Blo 1889435 21827357 := bstep (se 3 (by rfl) ⟨4092629, by rfl⟩ : syracuseStep 21827357 = 8185259) B8185259
theorem B14551571 : Blo 1889435 14551571 := bstep (se 1 (by rfl) ⟨10913678, by rfl⟩ : syracuseStep 14551571 = 21827357) B21827357
theorem B38804189 : Blo 1889435 38804189 := bstep (se 3 (by rfl) ⟨7275785, by rfl⟩ : syracuseStep 38804189 = 14551571) B14551571
theorem B103477837 : Blo 1889435 103477837 := bstep (se 3 (by rfl) ⟨19402094, by rfl⟩ : syracuseStep 103477837 = 38804189) B38804189
theorem B137970449 : Blo 1889435 137970449 := bstep (se 2 (by rfl) ⟨51738918, by rfl⟩ : syracuseStep 137970449 = 103477837) B103477837
theorem B91980299 : Blo 1889435 91980299 := bstep (se 1 (by rfl) ⟨68985224, by rfl⟩ : syracuseStep 91980299 = 137970449) B137970449
theorem B61320199 : Blo 1889435 61320199 := bstep (se 1 (by rfl) ⟨45990149, by rfl⟩ : syracuseStep 61320199 = 91980299) B91980299
theorem B81760265 : Blo 1889435 81760265 := bstep (se 2 (by rfl) ⟨30660099, by rfl⟩ : syracuseStep 81760265 = 61320199) B61320199
theorem B54506843 : Blo 1889435 54506843 := bstep (se 1 (by rfl) ⟨40880132, by rfl⟩ : syracuseStep 54506843 = 81760265) B81760265
theorem B36337895 : Blo 1889435 36337895 := bstep (se 1 (by rfl) ⟨27253421, by rfl⟩ : syracuseStep 36337895 = 54506843) B54506843
theorem B24225263 : Blo 1889435 24225263 := bstep (se 1 (by rfl) ⟨18168947, by rfl⟩ : syracuseStep 24225263 = 36337895) B36337895
theorem B16150175 : Blo 1889435 16150175 := bstep (se 1 (by rfl) ⟨12112631, by rfl⟩ : syracuseStep 16150175 = 24225263) B24225263
theorem B10766783 : Blo 1889435 10766783 := bstep (se 1 (by rfl) ⟨8075087, by rfl⟩ : syracuseStep 10766783 = 16150175) B16150175
theorem B7177855 : Blo 1889435 7177855 := bstep (se 1 (by rfl) ⟨5383391, by rfl⟩ : syracuseStep 7177855 = 10766783) B10766783
theorem B9570473 : Blo 1889435 9570473 := bstep (se 2 (by rfl) ⟨3588927, by rfl⟩ : syracuseStep 9570473 = 7177855) B7177855
theorem B6380315 : Blo 1889435 6380315 := bstep (se 1 (by rfl) ⟨4785236, by rfl⟩ : syracuseStep 6380315 = 9570473) B9570473
theorem B4253543 : Blo 1889435 4253543 := bstep (se 1 (by rfl) ⟨3190157, by rfl⟩ : syracuseStep 4253543 = 6380315) B6380315
theorem B2835695 : Blo 1889435 2835695 := bstep (se 1 (by rfl) ⟨2126771, by rfl⟩ : syracuseStep 2835695 = 4253543) B4253543
theorem B1890463 : Blo 1889435 1890463 := bstep (se 1 (by rfl) ⟨1417847, by rfl⟩ : syracuseStep 1890463 = 2835695) B2835695
theorem B2835701 : Blo 1889435 2835701 := bbase (se 5 (by rfl) ⟨132923, by rfl⟩ : syracuseStep 2835701 = 265847) (by norm_num)
theorem B1890467 : Blo 1889435 1890467 := bstep (se 1 (by rfl) ⟨1417850, by rfl⟩ : syracuseStep 1890467 = 2835701) B2835701
theorem B3406693 : Blo 1889435 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B4542257 : Blo 1889435 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B12112685 : Blo 1889435 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B8075123 : Blo 1889435 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B5383415 : Blo 1889435 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B3588943 : Blo 1889435 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B4785257 : Blo 1889435 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B3190171 : Blo 1889435 3190171 := bstep (se 1 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 3190171 = 4785257) B4785257
theorem B4253561 : Blo 1889435 4253561 := bstep (se 2 (by rfl) ⟨1595085, by rfl⟩ : syracuseStep 4253561 = 3190171) B3190171
theorem B2835707 : Blo 1889435 2835707 := bstep (se 1 (by rfl) ⟨2126780, by rfl⟩ : syracuseStep 2835707 = 4253561) B4253561
theorem B1890471 : Blo 1889435 1890471 := bstep (se 1 (by rfl) ⟨1417853, by rfl⟩ : syracuseStep 1890471 = 2835707) B2835707
theorem B2126785 : Blo 1889435 2126785 := bbase (se 2 (by rfl) ⟨797544, by rfl⟩ : syracuseStep 2126785 = 1595089) (by norm_num)
theorem B2835713 : Blo 1889435 2835713 := bstep (se 2 (by rfl) ⟨1063392, by rfl⟩ : syracuseStep 2835713 = 2126785) B2126785
theorem B1890475 : Blo 1889435 1890475 := bstep (se 1 (by rfl) ⟨1417856, by rfl⟩ : syracuseStep 1890475 = 2835713) B2835713
theorem B4785277 : Blo 1889435 4785277 := bbase (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) (by norm_num)
theorem B6380369 : Blo 1889435 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B4253579 : Blo 1889435 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B2835719 : Blo 1889435 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B1890479 : Blo 1889435 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B2835725 : Blo 1889435 2835725 := bbase (se 3 (by rfl) ⟨531698, by rfl⟩ : syracuseStep 2835725 = 1063397) (by norm_num)
theorem B1890483 : Blo 1889435 1890483 := bstep (se 1 (by rfl) ⟨1417862, by rfl⟩ : syracuseStep 1890483 = 2835725) B2835725
theorem B4253597 : Blo 1889435 4253597 := bbase (se 3 (by rfl) ⟨797549, by rfl⟩ : syracuseStep 4253597 = 1595099) (by norm_num)
theorem B2835731 : Blo 1889435 2835731 := bstep (se 1 (by rfl) ⟨2126798, by rfl⟩ : syracuseStep 2835731 = 4253597) B4253597
theorem B1890487 : Blo 1889435 1890487 := bstep (se 1 (by rfl) ⟨1417865, by rfl⟩ : syracuseStep 1890487 = 2835731) B2835731
theorem B3190205 : Blo 1889435 3190205 := bbase (se 3 (by rfl) ⟨598163, by rfl⟩ : syracuseStep 3190205 = 1196327) (by norm_num)
theorem B2126803 : Blo 1889435 2126803 := bstep (se 1 (by rfl) ⟨1595102, by rfl⟩ : syracuseStep 2126803 = 3190205) B3190205
theorem B2835737 : Blo 1889435 2835737 := bstep (se 2 (by rfl) ⟨1063401, by rfl⟩ : syracuseStep 2835737 = 2126803) B2126803
theorem B1890491 : Blo 1889435 1890491 := bstep (se 1 (by rfl) ⟨1417868, by rfl⟩ : syracuseStep 1890491 = 2835737) B2835737
theorem B10766965 : Blo 1889435 10766965 := bbase (se 5 (by rfl) ⟨504701, by rfl⟩ : syracuseStep 10766965 = 1009403) (by norm_num)
theorem B14355953 : Blo 1889435 14355953 := bstep (se 2 (by rfl) ⟨5383482, by rfl⟩ : syracuseStep 14355953 = 10766965) B10766965
theorem B9570635 : Blo 1889435 9570635 := bstep (se 1 (by rfl) ⟨7177976, by rfl⟩ : syracuseStep 9570635 = 14355953) B14355953
theorem B6380423 : Blo 1889435 6380423 := bstep (se 1 (by rfl) ⟨4785317, by rfl⟩ : syracuseStep 6380423 = 9570635) B9570635
theorem B4253615 : Blo 1889435 4253615 := bstep (se 1 (by rfl) ⟨3190211, by rfl⟩ : syracuseStep 4253615 = 6380423) B6380423
theorem B2835743 : Blo 1889435 2835743 := bstep (se 1 (by rfl) ⟨2126807, by rfl⟩ : syracuseStep 2835743 = 4253615) B4253615
theorem B1890495 : Blo 1889435 1890495 := bstep (se 1 (by rfl) ⟨1417871, by rfl⟩ : syracuseStep 1890495 = 2835743) B2835743
theorem B2835749 : Blo 1889435 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B1890499 : Blo 1889435 1890499 := bstep (se 1 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 1890499 = 2835749) B2835749
theorem B2392669 : Blo 1889435 2392669 := bbase (se 3 (by rfl) ⟨448625, by rfl⟩ : syracuseStep 2392669 = 897251) (by norm_num)
theorem B3190225 : Blo 1889435 3190225 := bstep (se 2 (by rfl) ⟨1196334, by rfl⟩ : syracuseStep 3190225 = 2392669) B2392669
theorem B4253633 : Blo 1889435 4253633 := bstep (se 2 (by rfl) ⟨1595112, by rfl⟩ : syracuseStep 4253633 = 3190225) B3190225
theorem B2835755 : Blo 1889435 2835755 := bstep (se 1 (by rfl) ⟨2126816, by rfl⟩ : syracuseStep 2835755 = 4253633) B4253633
theorem B1890503 : Blo 1889435 1890503 := bstep (se 1 (by rfl) ⟨1417877, by rfl⟩ : syracuseStep 1890503 = 2835755) B2835755
theorem B2126821 : Blo 1889435 2126821 := bbase (se 4 (by rfl) ⟨199389, by rfl⟩ : syracuseStep 2126821 = 398779) (by norm_num)
theorem B2835761 : Blo 1889435 2835761 := bstep (se 2 (by rfl) ⟨1063410, by rfl⟩ : syracuseStep 2835761 = 2126821) B2126821
theorem B1890507 : Blo 1889435 1890507 := bstep (se 1 (by rfl) ⟨1417880, by rfl⟩ : syracuseStep 1890507 = 2835761) B2835761
theorem B13627061 : Blo 1889435 13627061 := bbase (se 5 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 13627061 = 1277537) (by norm_num)
theorem B9084707 : Blo 1889435 9084707 := bstep (se 1 (by rfl) ⟨6813530, by rfl⟩ : syracuseStep 9084707 = 13627061) B13627061
theorem B6056471 : Blo 1889435 6056471 := bstep (se 1 (by rfl) ⟨4542353, by rfl⟩ : syracuseStep 6056471 = 9084707) B9084707
theorem B4037647 : Blo 1889435 4037647 := bstep (se 1 (by rfl) ⟨3028235, by rfl⟩ : syracuseStep 4037647 = 6056471) B6056471
theorem B5383529 : Blo 1889435 5383529 := bstep (se 2 (by rfl) ⟨2018823, by rfl⟩ : syracuseStep 5383529 = 4037647) B4037647
theorem B3589019 : Blo 1889435 3589019 := bstep (se 1 (by rfl) ⟨2691764, by rfl⟩ : syracuseStep 3589019 = 5383529) B5383529
theorem B2392679 : Blo 1889435 2392679 := bstep (se 1 (by rfl) ⟨1794509, by rfl⟩ : syracuseStep 2392679 = 3589019) B3589019
theorem B6380477 : Blo 1889435 6380477 := bstep (se 3 (by rfl) ⟨1196339, by rfl⟩ : syracuseStep 6380477 = 2392679) B2392679
theorem B4253651 : Blo 1889435 4253651 := bstep (se 1 (by rfl) ⟨3190238, by rfl⟩ : syracuseStep 4253651 = 6380477) B6380477
theorem B2835767 : Blo 1889435 2835767 := bstep (se 1 (by rfl) ⟨2126825, by rfl⟩ : syracuseStep 2835767 = 4253651) B4253651
theorem B1890511 : Blo 1889435 1890511 := bstep (se 1 (by rfl) ⟨1417883, by rfl⟩ : syracuseStep 1890511 = 2835767) B2835767
theorem B2835773 : Blo 1889435 2835773 := bbase (se 3 (by rfl) ⟨531707, by rfl⟩ : syracuseStep 2835773 = 1063415) (by norm_num)
theorem B1890515 : Blo 1889435 1890515 := bstep (se 1 (by rfl) ⟨1417886, by rfl⟩ : syracuseStep 1890515 = 2835773) B2835773
theorem B4253669 : Blo 1889435 4253669 := bbase (se 4 (by rfl) ⟨398781, by rfl⟩ : syracuseStep 4253669 = 797563) (by norm_num)
theorem B2835779 : Blo 1889435 2835779 := bstep (se 1 (by rfl) ⟨2126834, by rfl⟩ : syracuseStep 2835779 = 4253669) B4253669
theorem B1890519 : Blo 1889435 1890519 := bstep (se 1 (by rfl) ⟨1417889, by rfl⟩ : syracuseStep 1890519 = 2835779) B2835779
theorem B4785389 : Blo 1889435 4785389 := bbase (se 3 (by rfl) ⟨897260, by rfl⟩ : syracuseStep 4785389 = 1794521) (by norm_num)
theorem B3190259 : Blo 1889435 3190259 := bstep (se 1 (by rfl) ⟨2392694, by rfl⟩ : syracuseStep 3190259 = 4785389) B4785389
theorem B2126839 : Blo 1889435 2126839 := bstep (se 1 (by rfl) ⟨1595129, by rfl⟩ : syracuseStep 2126839 = 3190259) B3190259
theorem B2835785 : Blo 1889435 2835785 := bstep (se 2 (by rfl) ⟨1063419, by rfl⟩ : syracuseStep 2835785 = 2126839) B2126839
theorem B1890523 : Blo 1889435 1890523 := bstep (se 1 (by rfl) ⟨1417892, by rfl⟩ : syracuseStep 1890523 = 2835785) B2835785
theorem B3028261 : Blo 1889435 3028261 := bbase (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) (by norm_num)
theorem B4037681 : Blo 1889435 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B2691787 : Blo 1889435 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B3589049 : Blo 1889435 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B9570797 : Blo 1889435 9570797 := bstep (se 3 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 9570797 = 3589049) B3589049
theorem B6380531 : Blo 1889435 6380531 := bstep (se 1 (by rfl) ⟨4785398, by rfl⟩ : syracuseStep 6380531 = 9570797) B9570797
theorem B4253687 : Blo 1889435 4253687 := bstep (se 1 (by rfl) ⟨3190265, by rfl⟩ : syracuseStep 4253687 = 6380531) B6380531
theorem B2835791 : Blo 1889435 2835791 := bstep (se 1 (by rfl) ⟨2126843, by rfl⟩ : syracuseStep 2835791 = 4253687) B4253687
theorem B1890527 : Blo 1889435 1890527 := bstep (se 1 (by rfl) ⟨1417895, by rfl⟩ : syracuseStep 1890527 = 2835791) B2835791
theorem B2835797 : Blo 1889435 2835797 := bbase (se 12 (by rfl) ⟨1038, by rfl⟩ : syracuseStep 2835797 = 2077) (by norm_num)
theorem B1890531 : Blo 1889435 1890531 := bstep (se 1 (by rfl) ⟨1417898, by rfl⟩ : syracuseStep 1890531 = 2835797) B2835797
theorem B2018849 : Blo 1889435 2018849 := bbase (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) (by norm_num)
theorem B5383597 : Blo 1889435 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B7178129 : Blo 1889435 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B4785419 : Blo 1889435 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B3190279 : Blo 1889435 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B4253705 : Blo 1889435 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B2835803 : Blo 1889435 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B1890535 : Blo 1889435 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B2126857 : Blo 1889435 2126857 := bbase (se 2 (by rfl) ⟨797571, by rfl⟩ : syracuseStep 2126857 = 1595143) (by norm_num)
theorem B2835809 : Blo 1889435 2835809 := bstep (se 2 (by rfl) ⟨1063428, by rfl⟩ : syracuseStep 2835809 = 2126857) B2126857
theorem B1890539 : Blo 1889435 1890539 := bstep (se 1 (by rfl) ⟨1417904, by rfl⟩ : syracuseStep 1890539 = 2835809) B2835809
theorem B18169717 : Blo 1889435 18169717 := bbase (se 5 (by rfl) ⟨851705, by rfl⟩ : syracuseStep 18169717 = 1703411) (by norm_num)
theorem B24226289 : Blo 1889435 24226289 := bstep (se 2 (by rfl) ⟨9084858, by rfl⟩ : syracuseStep 24226289 = 18169717) B18169717
theorem B16150859 : Blo 1889435 16150859 := bstep (se 1 (by rfl) ⟨12113144, by rfl⟩ : syracuseStep 16150859 = 24226289) B24226289
theorem B10767239 : Blo 1889435 10767239 := bstep (se 1 (by rfl) ⟨8075429, by rfl⟩ : syracuseStep 10767239 = 16150859) B16150859
theorem B7178159 : Blo 1889435 7178159 := bstep (se 1 (by rfl) ⟨5383619, by rfl⟩ : syracuseStep 7178159 = 10767239) B10767239
theorem B4785439 : Blo 1889435 4785439 := bstep (se 1 (by rfl) ⟨3589079, by rfl⟩ : syracuseStep 4785439 = 7178159) B7178159
theorem B6380585 : Blo 1889435 6380585 := bstep (se 2 (by rfl) ⟨2392719, by rfl⟩ : syracuseStep 6380585 = 4785439) B4785439
theorem B4253723 : Blo 1889435 4253723 := bstep (se 1 (by rfl) ⟨3190292, by rfl⟩ : syracuseStep 4253723 = 6380585) B6380585
theorem B2835815 : Blo 1889435 2835815 := bstep (se 1 (by rfl) ⟨2126861, by rfl⟩ : syracuseStep 2835815 = 4253723) B4253723
theorem B1890543 : Blo 1889435 1890543 := bstep (se 1 (by rfl) ⟨1417907, by rfl⟩ : syracuseStep 1890543 = 2835815) B2835815
theorem B2835821 : Blo 1889435 2835821 := bbase (se 3 (by rfl) ⟨531716, by rfl⟩ : syracuseStep 2835821 = 1063433) (by norm_num)
theorem B1890547 : Blo 1889435 1890547 := bstep (se 1 (by rfl) ⟨1417910, by rfl⟩ : syracuseStep 1890547 = 2835821) B2835821
theorem B4253741 : Blo 1889435 4253741 := bbase (se 3 (by rfl) ⟨797576, by rfl⟩ : syracuseStep 4253741 = 1595153) (by norm_num)
theorem B2835827 : Blo 1889435 2835827 := bstep (se 1 (by rfl) ⟨2126870, by rfl⟩ : syracuseStep 2835827 = 4253741) B4253741
theorem B1890551 : Blo 1889435 1890551 := bstep (se 1 (by rfl) ⟨1417913, by rfl⟩ : syracuseStep 1890551 = 2835827) B2835827
theorem B9701525 : Blo 1889435 9701525 := bbase (se 6 (by rfl) ⟨227379, by rfl⟩ : syracuseStep 9701525 = 454759) (by norm_num)
theorem B6467683 : Blo 1889435 6467683 := bstep (se 1 (by rfl) ⟨4850762, by rfl⟩ : syracuseStep 6467683 = 9701525) B9701525
theorem B8623577 : Blo 1889435 8623577 := bstep (se 2 (by rfl) ⟨3233841, by rfl⟩ : syracuseStep 8623577 = 6467683) B6467683
theorem B5749051 : Blo 1889435 5749051 := bstep (se 1 (by rfl) ⟨4311788, by rfl⟩ : syracuseStep 5749051 = 8623577) B8623577
theorem B7665401 : Blo 1889435 7665401 := bstep (se 2 (by rfl) ⟨2874525, by rfl⟩ : syracuseStep 7665401 = 5749051) B5749051
theorem B20441069 : Blo 1889435 20441069 := bstep (se 3 (by rfl) ⟨3832700, by rfl⟩ : syracuseStep 20441069 = 7665401) B7665401
theorem B13627379 : Blo 1889435 13627379 := bstep (se 1 (by rfl) ⟨10220534, by rfl⟩ : syracuseStep 13627379 = 20441069) B20441069
theorem B9084919 : Blo 1889435 9084919 := bstep (se 1 (by rfl) ⟨6813689, by rfl⟩ : syracuseStep 9084919 = 13627379) B13627379
theorem B12113225 : Blo 1889435 12113225 := bstep (se 2 (by rfl) ⟨4542459, by rfl⟩ : syracuseStep 12113225 = 9084919) B9084919
theorem B8075483 : Blo 1889435 8075483 := bstep (se 1 (by rfl) ⟨6056612, by rfl⟩ : syracuseStep 8075483 = 12113225) B12113225
theorem B5383655 : Blo 1889435 5383655 := bstep (se 1 (by rfl) ⟨4037741, by rfl⟩ : syracuseStep 5383655 = 8075483) B8075483
theorem B3589103 : Blo 1889435 3589103 := bstep (se 1 (by rfl) ⟨2691827, by rfl⟩ : syracuseStep 3589103 = 5383655) B5383655
theorem B2392735 : Blo 1889435 2392735 := bstep (se 1 (by rfl) ⟨1794551, by rfl⟩ : syracuseStep 2392735 = 3589103) B3589103
theorem B3190313 : Blo 1889435 3190313 := bstep (se 2 (by rfl) ⟨1196367, by rfl⟩ : syracuseStep 3190313 = 2392735) B2392735
theorem B2126875 : Blo 1889435 2126875 := bstep (se 1 (by rfl) ⟨1595156, by rfl⟩ : syracuseStep 2126875 = 3190313) B3190313
theorem B2835833 : Blo 1889435 2835833 := bstep (se 2 (by rfl) ⟨1063437, by rfl⟩ : syracuseStep 2835833 = 2126875) B2126875
theorem B1890555 : Blo 1889435 1890555 := bstep (se 1 (by rfl) ⟨1417916, by rfl⟩ : syracuseStep 1890555 = 2835833) B2835833
theorem B5749061 : Blo 1889435 5749061 := bbase (se 4 (by rfl) ⟨538974, by rfl⟩ : syracuseStep 5749061 = 1077949) (by norm_num)
theorem B15330829 : Blo 1889435 15330829 := bstep (se 3 (by rfl) ⟨2874530, by rfl⟩ : syracuseStep 15330829 = 5749061) B5749061
theorem B20441105 : Blo 1889435 20441105 := bstep (se 2 (by rfl) ⟨7665414, by rfl⟩ : syracuseStep 20441105 = 15330829) B15330829
theorem B13627403 : Blo 1889435 13627403 := bstep (se 1 (by rfl) ⟨10220552, by rfl⟩ : syracuseStep 13627403 = 20441105) B20441105
theorem B9084935 : Blo 1889435 9084935 := bstep (se 1 (by rfl) ⟨6813701, by rfl⟩ : syracuseStep 9084935 = 13627403) B13627403
theorem B6056623 : Blo 1889435 6056623 := bstep (se 1 (by rfl) ⟨4542467, by rfl⟩ : syracuseStep 6056623 = 9084935) B9084935
theorem B32301989 : Blo 1889435 32301989 := bstep (se 4 (by rfl) ⟨3028311, by rfl⟩ : syracuseStep 32301989 = 6056623) B6056623
theorem B21534659 : Blo 1889435 21534659 := bstep (se 1 (by rfl) ⟨16150994, by rfl⟩ : syracuseStep 21534659 = 32301989) B32301989
theorem B14356439 : Blo 1889435 14356439 := bstep (se 1 (by rfl) ⟨10767329, by rfl⟩ : syracuseStep 14356439 = 21534659) B21534659
theorem B9570959 : Blo 1889435 9570959 := bstep (se 1 (by rfl) ⟨7178219, by rfl⟩ : syracuseStep 9570959 = 14356439) B14356439
theorem B6380639 : Blo 1889435 6380639 := bstep (se 1 (by rfl) ⟨4785479, by rfl⟩ : syracuseStep 6380639 = 9570959) B9570959
theorem B4253759 : Blo 1889435 4253759 := bstep (se 1 (by rfl) ⟨3190319, by rfl⟩ : syracuseStep 4253759 = 6380639) B6380639
theorem B2835839 : Blo 1889435 2835839 := bstep (se 1 (by rfl) ⟨2126879, by rfl⟩ : syracuseStep 2835839 = 4253759) B4253759
theorem B1890559 : Blo 1889435 1890559 := bstep (se 1 (by rfl) ⟨1417919, by rfl⟩ : syracuseStep 1890559 = 2835839) B2835839
theorem B2835845 : Blo 1889435 2835845 := bbase (se 4 (by rfl) ⟨265860, by rfl⟩ : syracuseStep 2835845 = 531721) (by norm_num)
theorem B1890563 : Blo 1889435 1890563 := bstep (se 1 (by rfl) ⟨1417922, by rfl⟩ : syracuseStep 1890563 = 2835845) B2835845
theorem B3190333 : Blo 1889435 3190333 := bbase (se 3 (by rfl) ⟨598187, by rfl⟩ : syracuseStep 3190333 = 1196375) (by norm_num)
theorem B4253777 : Blo 1889435 4253777 := bstep (se 2 (by rfl) ⟨1595166, by rfl⟩ : syracuseStep 4253777 = 3190333) B3190333
theorem B2835851 : Blo 1889435 2835851 := bstep (se 1 (by rfl) ⟨2126888, by rfl⟩ : syracuseStep 2835851 = 4253777) B4253777
theorem B1890567 : Blo 1889435 1890567 := bstep (se 1 (by rfl) ⟨1417925, by rfl⟩ : syracuseStep 1890567 = 2835851) B2835851
theorem B2126893 : Blo 1889435 2126893 := bbase (se 3 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 2126893 = 797585) (by norm_num)
theorem B2835857 : Blo 1889435 2835857 := bstep (se 2 (by rfl) ⟨1063446, by rfl⟩ : syracuseStep 2835857 = 2126893) B2126893
theorem B1890571 : Blo 1889435 1890571 := bstep (se 1 (by rfl) ⟨1417928, by rfl⟩ : syracuseStep 1890571 = 2835857) B2835857
theorem B6380693 : Blo 1889435 6380693 := bbase (se 6 (by rfl) ⟨149547, by rfl⟩ : syracuseStep 6380693 = 299095) (by norm_num)
theorem B4253795 : Blo 1889435 4253795 := bstep (se 1 (by rfl) ⟨3190346, by rfl⟩ : syracuseStep 4253795 = 6380693) B6380693
theorem B2835863 : Blo 1889435 2835863 := bstep (se 1 (by rfl) ⟨2126897, by rfl⟩ : syracuseStep 2835863 = 4253795) B4253795
theorem B1890575 : Blo 1889435 1890575 := bstep (se 1 (by rfl) ⟨1417931, by rfl⟩ : syracuseStep 1890575 = 2835863) B2835863
theorem B2835869 : Blo 1889435 2835869 := bbase (se 3 (by rfl) ⟨531725, by rfl⟩ : syracuseStep 2835869 = 1063451) (by norm_num)
theorem B1890579 : Blo 1889435 1890579 := bstep (se 1 (by rfl) ⟨1417934, by rfl⟩ : syracuseStep 1890579 = 2835869) B2835869
theorem B4253813 : Blo 1889435 4253813 := bbase (se 5 (by rfl) ⟨199397, by rfl⟩ : syracuseStep 4253813 = 398795) (by norm_num)
theorem B2835875 : Blo 1889435 2835875 := bstep (se 1 (by rfl) ⟨2126906, by rfl⟩ : syracuseStep 2835875 = 4253813) B4253813
theorem B1890583 : Blo 1889435 1890583 := bstep (se 1 (by rfl) ⟨1417937, by rfl⟩ : syracuseStep 1890583 = 2835875) B2835875
theorem B3028357 : Blo 1889435 3028357 := bbase (se 4 (by rfl) ⟨283908, by rfl⟩ : syracuseStep 3028357 = 567817) (by norm_num)
theorem B16151237 : Blo 1889435 16151237 := bstep (se 4 (by rfl) ⟨1514178, by rfl⟩ : syracuseStep 16151237 = 3028357) B3028357
theorem B10767491 : Blo 1889435 10767491 := bstep (se 1 (by rfl) ⟨8075618, by rfl⟩ : syracuseStep 10767491 = 16151237) B16151237
theorem B7178327 : Blo 1889435 7178327 := bstep (se 1 (by rfl) ⟨5383745, by rfl⟩ : syracuseStep 7178327 = 10767491) B10767491
theorem B4785551 : Blo 1889435 4785551 := bstep (se 1 (by rfl) ⟨3589163, by rfl⟩ : syracuseStep 4785551 = 7178327) B7178327
theorem B3190367 : Blo 1889435 3190367 := bstep (se 1 (by rfl) ⟨2392775, by rfl⟩ : syracuseStep 3190367 = 4785551) B4785551
theorem B2126911 : Blo 1889435 2126911 := bstep (se 1 (by rfl) ⟨1595183, by rfl⟩ : syracuseStep 2126911 = 3190367) B3190367
theorem B2835881 : Blo 1889435 2835881 := bstep (se 2 (by rfl) ⟨1063455, by rfl⟩ : syracuseStep 2835881 = 2126911) B2126911
theorem B1890587 : Blo 1889435 1890587 := bstep (se 1 (by rfl) ⟨1417940, by rfl⟩ : syracuseStep 1890587 = 2835881) B2835881
theorem B7178341 : Blo 1889435 7178341 := bbase (se 4 (by rfl) ⟨672969, by rfl⟩ : syracuseStep 7178341 = 1345939) (by norm_num)
theorem B9571121 : Blo 1889435 9571121 := bstep (se 2 (by rfl) ⟨3589170, by rfl⟩ : syracuseStep 9571121 = 7178341) B7178341
theorem B6380747 : Blo 1889435 6380747 := bstep (se 1 (by rfl) ⟨4785560, by rfl⟩ : syracuseStep 6380747 = 9571121) B9571121
theorem B4253831 : Blo 1889435 4253831 := bstep (se 1 (by rfl) ⟨3190373, by rfl⟩ : syracuseStep 4253831 = 6380747) B6380747
theorem B2835887 : Blo 1889435 2835887 := bstep (se 1 (by rfl) ⟨2126915, by rfl⟩ : syracuseStep 2835887 = 4253831) B4253831
theorem B1890591 : Blo 1889435 1890591 := bstep (se 1 (by rfl) ⟨1417943, by rfl⟩ : syracuseStep 1890591 = 2835887) B2835887
theorem B2835893 : Blo 1889435 2835893 := bbase (se 5 (by rfl) ⟨132932, by rfl⟩ : syracuseStep 2835893 = 265865) (by norm_num)
theorem B1890595 : Blo 1889435 1890595 := bstep (se 1 (by rfl) ⟨1417946, by rfl⟩ : syracuseStep 1890595 = 2835893) B2835893
theorem B4785581 : Blo 1889435 4785581 := bbase (se 3 (by rfl) ⟨897296, by rfl⟩ : syracuseStep 4785581 = 1794593) (by norm_num)
theorem B3190387 : Blo 1889435 3190387 := bstep (se 1 (by rfl) ⟨2392790, by rfl⟩ : syracuseStep 3190387 = 4785581) B4785581
theorem B4253849 : Blo 1889435 4253849 := bstep (se 2 (by rfl) ⟨1595193, by rfl⟩ : syracuseStep 4253849 = 3190387) B3190387
theorem B2835899 : Blo 1889435 2835899 := bstep (se 1 (by rfl) ⟨2126924, by rfl⟩ : syracuseStep 2835899 = 4253849) B4253849
theorem B1890599 : Blo 1889435 1890599 := bstep (se 1 (by rfl) ⟨1417949, by rfl⟩ : syracuseStep 1890599 = 2835899) B2835899
theorem B2126929 : Blo 1889435 2126929 := bbase (se 2 (by rfl) ⟨797598, by rfl⟩ : syracuseStep 2126929 = 1595197) (by norm_num)
theorem B2835905 : Blo 1889435 2835905 := bstep (se 2 (by rfl) ⟨1063464, by rfl⟩ : syracuseStep 2835905 = 2126929) B2126929
theorem B1890603 : Blo 1889435 1890603 := bstep (se 1 (by rfl) ⟨1417952, by rfl⟩ : syracuseStep 1890603 = 2835905) B2835905
theorem B2691901 : Blo 1889435 2691901 := bbase (se 3 (by rfl) ⟨504731, by rfl⟩ : syracuseStep 2691901 = 1009463) (by norm_num)
theorem B3589201 : Blo 1889435 3589201 := bstep (se 2 (by rfl) ⟨1345950, by rfl⟩ : syracuseStep 3589201 = 2691901) B2691901
theorem B4785601 : Blo 1889435 4785601 := bstep (se 2 (by rfl) ⟨1794600, by rfl⟩ : syracuseStep 4785601 = 3589201) B3589201
theorem B6380801 : Blo 1889435 6380801 := bstep (se 2 (by rfl) ⟨2392800, by rfl⟩ : syracuseStep 6380801 = 4785601) B4785601
theorem B4253867 : Blo 1889435 4253867 := bstep (se 1 (by rfl) ⟨3190400, by rfl⟩ : syracuseStep 4253867 = 6380801) B6380801
theorem B2835911 : Blo 1889435 2835911 := bstep (se 1 (by rfl) ⟨2126933, by rfl⟩ : syracuseStep 2835911 = 4253867) B4253867
theorem B1890607 : Blo 1889435 1890607 := bstep (se 1 (by rfl) ⟨1417955, by rfl⟩ : syracuseStep 1890607 = 2835911) B2835911
theorem B2835917 : Blo 1889435 2835917 := bbase (se 3 (by rfl) ⟨531734, by rfl⟩ : syracuseStep 2835917 = 1063469) (by norm_num)
theorem B1890611 : Blo 1889435 1890611 := bstep (se 1 (by rfl) ⟨1417958, by rfl⟩ : syracuseStep 1890611 = 2835917) B2835917
theorem B4253885 : Blo 1889435 4253885 := bbase (se 3 (by rfl) ⟨797603, by rfl⟩ : syracuseStep 4253885 = 1595207) (by norm_num)
theorem B2835923 : Blo 1889435 2835923 := bstep (se 1 (by rfl) ⟨2126942, by rfl⟩ : syracuseStep 2835923 = 4253885) B4253885
theorem B1890615 : Blo 1889435 1890615 := bstep (se 1 (by rfl) ⟨1417961, by rfl⟩ : syracuseStep 1890615 = 2835923) B2835923
theorem B3190421 : Blo 1889435 3190421 := bbase (se 6 (by rfl) ⟨74775, by rfl⟩ : syracuseStep 3190421 = 149551) (by norm_num)
theorem B2126947 : Blo 1889435 2126947 := bstep (se 1 (by rfl) ⟨1595210, by rfl⟩ : syracuseStep 2126947 = 3190421) B3190421
theorem B2835929 : Blo 1889435 2835929 := bstep (se 2 (by rfl) ⟨1063473, by rfl⟩ : syracuseStep 2835929 = 2126947) B2126947
theorem B1890619 : Blo 1889435 1890619 := bstep (se 1 (by rfl) ⟨1417964, by rfl⟩ : syracuseStep 1890619 = 2835929) B2835929
theorem B15331349 : Blo 1889435 15331349 := bbase (se 6 (by rfl) ⟨359328, by rfl⟩ : syracuseStep 15331349 = 718657) (by norm_num)
theorem B10220899 : Blo 1889435 10220899 := bstep (se 1 (by rfl) ⟨7665674, by rfl⟩ : syracuseStep 10220899 = 15331349) B15331349
theorem B13627865 : Blo 1889435 13627865 := bstep (se 2 (by rfl) ⟨5110449, by rfl⟩ : syracuseStep 13627865 = 10220899) B10220899
theorem B9085243 : Blo 1889435 9085243 := bstep (se 1 (by rfl) ⟨6813932, by rfl⟩ : syracuseStep 9085243 = 13627865) B13627865
theorem B12113657 : Blo 1889435 12113657 := bstep (se 2 (by rfl) ⟨4542621, by rfl⟩ : syracuseStep 12113657 = 9085243) B9085243
theorem B8075771 : Blo 1889435 8075771 := bstep (se 1 (by rfl) ⟨6056828, by rfl⟩ : syracuseStep 8075771 = 12113657) B12113657
theorem B5383847 : Blo 1889435 5383847 := bstep (se 1 (by rfl) ⟨4037885, by rfl⟩ : syracuseStep 5383847 = 8075771) B8075771
theorem B14356925 : Blo 1889435 14356925 := bstep (se 3 (by rfl) ⟨2691923, by rfl⟩ : syracuseStep 14356925 = 5383847) B5383847
theorem B9571283 : Blo 1889435 9571283 := bstep (se 1 (by rfl) ⟨7178462, by rfl⟩ : syracuseStep 9571283 = 14356925) B14356925
theorem B6380855 : Blo 1889435 6380855 := bstep (se 1 (by rfl) ⟨4785641, by rfl⟩ : syracuseStep 6380855 = 9571283) B9571283
theorem B4253903 : Blo 1889435 4253903 := bstep (se 1 (by rfl) ⟨3190427, by rfl⟩ : syracuseStep 4253903 = 6380855) B6380855
theorem B2835935 : Blo 1889435 2835935 := bstep (se 1 (by rfl) ⟨2126951, by rfl⟩ : syracuseStep 2835935 = 4253903) B4253903
theorem B1890623 : Blo 1889435 1890623 := bstep (se 1 (by rfl) ⟨1417967, by rfl⟩ : syracuseStep 1890623 = 2835935) B2835935
theorem B2835941 : Blo 1889435 2835941 := bbase (se 4 (by rfl) ⟨265869, by rfl⟩ : syracuseStep 2835941 = 531739) (by norm_num)
theorem B1890627 : Blo 1889435 1890627 := bstep (se 1 (by rfl) ⟨1417970, by rfl⟩ : syracuseStep 1890627 = 2835941) B2835941
theorem B4850957 : Blo 1889435 4850957 := bbase (se 3 (by rfl) ⟨909554, by rfl⟩ : syracuseStep 4850957 = 1819109) (by norm_num)
theorem B3233971 : Blo 1889435 3233971 := bstep (se 1 (by rfl) ⟨2425478, by rfl⟩ : syracuseStep 3233971 = 4850957) B4850957
theorem B4311961 : Blo 1889435 4311961 := bstep (se 2 (by rfl) ⟨1616985, by rfl⟩ : syracuseStep 4311961 = 3233971) B3233971
theorem B22997125 : Blo 1889435 22997125 := bstep (se 4 (by rfl) ⟨2155980, by rfl⟩ : syracuseStep 22997125 = 4311961) B4311961
theorem B30662833 : Blo 1889435 30662833 := bstep (se 2 (by rfl) ⟨11498562, by rfl⟩ : syracuseStep 30662833 = 22997125) B22997125
theorem B40883777 : Blo 1889435 40883777 := bstep (se 2 (by rfl) ⟨15331416, by rfl⟩ : syracuseStep 40883777 = 30662833) B30662833
theorem B27255851 : Blo 1889435 27255851 := bstep (se 1 (by rfl) ⟨20441888, by rfl⟩ : syracuseStep 27255851 = 40883777) B40883777
theorem B18170567 : Blo 1889435 18170567 := bstep (se 1 (by rfl) ⟨13627925, by rfl⟩ : syracuseStep 18170567 = 27255851) B27255851
theorem B12113711 : Blo 1889435 12113711 := bstep (se 1 (by rfl) ⟨9085283, by rfl⟩ : syracuseStep 12113711 = 18170567) B18170567
theorem B8075807 : Blo 1889435 8075807 := bstep (se 1 (by rfl) ⟨6056855, by rfl⟩ : syracuseStep 8075807 = 12113711) B12113711
theorem B5383871 : Blo 1889435 5383871 := bstep (se 1 (by rfl) ⟨4037903, by rfl⟩ : syracuseStep 5383871 = 8075807) B8075807
theorem B3589247 : Blo 1889435 3589247 := bstep (se 1 (by rfl) ⟨2691935, by rfl⟩ : syracuseStep 3589247 = 5383871) B5383871
theorem B2392831 : Blo 1889435 2392831 := bstep (se 1 (by rfl) ⟨1794623, by rfl⟩ : syracuseStep 2392831 = 3589247) B3589247
theorem B3190441 : Blo 1889435 3190441 := bstep (se 2 (by rfl) ⟨1196415, by rfl⟩ : syracuseStep 3190441 = 2392831) B2392831
theorem B4253921 : Blo 1889435 4253921 := bstep (se 2 (by rfl) ⟨1595220, by rfl⟩ : syracuseStep 4253921 = 3190441) B3190441
theorem B2835947 : Blo 1889435 2835947 := bstep (se 1 (by rfl) ⟨2126960, by rfl⟩ : syracuseStep 2835947 = 4253921) B4253921
theorem B1890631 : Blo 1889435 1890631 := bstep (se 1 (by rfl) ⟨1417973, by rfl⟩ : syracuseStep 1890631 = 2835947) B2835947
theorem B2126965 : Blo 1889435 2126965 := bbase (se 5 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 2126965 = 199403) (by norm_num)
theorem B2835953 : Blo 1889435 2835953 := bstep (se 2 (by rfl) ⟨1063482, by rfl⟩ : syracuseStep 2835953 = 2126965) B2126965
theorem B1890635 : Blo 1889435 1890635 := bstep (se 1 (by rfl) ⟨1417976, by rfl⟩ : syracuseStep 1890635 = 2835953) B2835953
theorem B2392841 : Blo 1889435 2392841 := bbase (se 2 (by rfl) ⟨897315, by rfl⟩ : syracuseStep 2392841 = 1794631) (by norm_num)
theorem B6380909 : Blo 1889435 6380909 := bstep (se 3 (by rfl) ⟨1196420, by rfl⟩ : syracuseStep 6380909 = 2392841) B2392841
theorem B4253939 : Blo 1889435 4253939 := bstep (se 1 (by rfl) ⟨3190454, by rfl⟩ : syracuseStep 4253939 = 6380909) B6380909
theorem B2835959 : Blo 1889435 2835959 := bstep (se 1 (by rfl) ⟨2126969, by rfl⟩ : syracuseStep 2835959 = 4253939) B4253939
theorem B1890639 : Blo 1889435 1890639 := bstep (se 1 (by rfl) ⟨1417979, by rfl⟩ : syracuseStep 1890639 = 2835959) B2835959
theorem B2835965 : Blo 1889435 2835965 := bbase (se 3 (by rfl) ⟨531743, by rfl⟩ : syracuseStep 2835965 = 1063487) (by norm_num)
theorem B1890643 : Blo 1889435 1890643 := bstep (se 1 (by rfl) ⟨1417982, by rfl⟩ : syracuseStep 1890643 = 2835965) B2835965
theorem B4253957 : Blo 1889435 4253957 := bbase (se 4 (by rfl) ⟨398808, by rfl⟩ : syracuseStep 4253957 = 797617) (by norm_num)
theorem B2835971 : Blo 1889435 2835971 := bstep (se 1 (by rfl) ⟨2126978, by rfl⟩ : syracuseStep 2835971 = 4253957) B4253957
theorem B1890647 : Blo 1889435 1890647 := bstep (se 1 (by rfl) ⟨1417985, by rfl⟩ : syracuseStep 1890647 = 2835971) B2835971
theorem B3589285 : Blo 1889435 3589285 := bbase (se 4 (by rfl) ⟨336495, by rfl⟩ : syracuseStep 3589285 = 672991) (by norm_num)
theorem B4785713 : Blo 1889435 4785713 := bstep (se 2 (by rfl) ⟨1794642, by rfl⟩ : syracuseStep 4785713 = 3589285) B3589285
theorem B3190475 : Blo 1889435 3190475 := bstep (se 1 (by rfl) ⟨2392856, by rfl⟩ : syracuseStep 3190475 = 4785713) B4785713
theorem B2126983 : Blo 1889435 2126983 := bstep (se 1 (by rfl) ⟨1595237, by rfl⟩ : syracuseStep 2126983 = 3190475) B3190475
theorem B2835977 : Blo 1889435 2835977 := bstep (se 2 (by rfl) ⟨1063491, by rfl⟩ : syracuseStep 2835977 = 2126983) B2126983
theorem B1890651 : Blo 1889435 1890651 := bstep (se 1 (by rfl) ⟨1417988, by rfl⟩ : syracuseStep 1890651 = 2835977) B2835977
theorem B9571445 : Blo 1889435 9571445 := bbase (se 5 (by rfl) ⟨448661, by rfl⟩ : syracuseStep 9571445 = 897323) (by norm_num)
theorem B6380963 : Blo 1889435 6380963 := bstep (se 1 (by rfl) ⟨4785722, by rfl⟩ : syracuseStep 6380963 = 9571445) B9571445
theorem B4253975 : Blo 1889435 4253975 := bstep (se 1 (by rfl) ⟨3190481, by rfl⟩ : syracuseStep 4253975 = 6380963) B6380963
theorem B2835983 : Blo 1889435 2835983 := bstep (se 1 (by rfl) ⟨2126987, by rfl⟩ : syracuseStep 2835983 = 4253975) B4253975
theorem B1890655 : Blo 1889435 1890655 := bstep (se 1 (by rfl) ⟨1417991, by rfl⟩ : syracuseStep 1890655 = 2835983) B2835983
theorem B2835989 : Blo 1889435 2835989 := bbase (se 6 (by rfl) ⟨66468, by rfl⟩ : syracuseStep 2835989 = 132937) (by norm_num)
theorem B1890659 : Blo 1889435 1890659 := bstep (se 1 (by rfl) ⟨1417994, by rfl⟩ : syracuseStep 1890659 = 2835989) B2835989
theorem B2302349 : Blo 1889435 2302349 := bbase (se 3 (by rfl) ⟨431690, by rfl⟩ : syracuseStep 2302349 = 863381) (by norm_num)
theorem B24558389 : Blo 1889435 24558389 := bstep (se 5 (by rfl) ⟨1151174, by rfl⟩ : syracuseStep 24558389 = 2302349) B2302349
theorem B16372259 : Blo 1889435 16372259 := bstep (se 1 (by rfl) ⟨12279194, by rfl⟩ : syracuseStep 16372259 = 24558389) B24558389
theorem B10914839 : Blo 1889435 10914839 := bstep (se 1 (by rfl) ⟨8186129, by rfl⟩ : syracuseStep 10914839 = 16372259) B16372259
theorem B7276559 : Blo 1889435 7276559 := bstep (se 1 (by rfl) ⟨5457419, by rfl⟩ : syracuseStep 7276559 = 10914839) B10914839
theorem B19404157 : Blo 1889435 19404157 := bstep (se 3 (by rfl) ⟨3638279, by rfl⟩ : syracuseStep 19404157 = 7276559) B7276559
theorem B25872209 : Blo 1889435 25872209 := bstep (se 2 (by rfl) ⟨9702078, by rfl⟩ : syracuseStep 25872209 = 19404157) B19404157
theorem B17248139 : Blo 1889435 17248139 := bstep (se 1 (by rfl) ⟨12936104, by rfl⟩ : syracuseStep 17248139 = 25872209) B25872209
theorem B11498759 : Blo 1889435 11498759 := bstep (se 1 (by rfl) ⟨8624069, by rfl⟩ : syracuseStep 11498759 = 17248139) B17248139
theorem B7665839 : Blo 1889435 7665839 := bstep (se 1 (by rfl) ⟨5749379, by rfl⟩ : syracuseStep 7665839 = 11498759) B11498759
theorem B5110559 : Blo 1889435 5110559 := bstep (se 1 (by rfl) ⟨3832919, by rfl⟩ : syracuseStep 5110559 = 7665839) B7665839
theorem B3407039 : Blo 1889435 3407039 := bstep (se 1 (by rfl) ⟨2555279, by rfl⟩ : syracuseStep 3407039 = 5110559) B5110559
theorem B2271359 : Blo 1889435 2271359 := bstep (se 1 (by rfl) ⟨1703519, by rfl⟩ : syracuseStep 2271359 = 3407039) B3407039
theorem B6056957 : Blo 1889435 6056957 := bstep (se 3 (by rfl) ⟨1135679, by rfl⟩ : syracuseStep 6056957 = 2271359) B2271359
theorem B16151885 : Blo 1889435 16151885 := bstep (se 3 (by rfl) ⟨3028478, by rfl⟩ : syracuseStep 16151885 = 6056957) B6056957
theorem B10767923 : Blo 1889435 10767923 := bstep (se 1 (by rfl) ⟨8075942, by rfl⟩ : syracuseStep 10767923 = 16151885) B16151885
theorem B7178615 : Blo 1889435 7178615 := bstep (se 1 (by rfl) ⟨5383961, by rfl⟩ : syracuseStep 7178615 = 10767923) B10767923
theorem B4785743 : Blo 1889435 4785743 := bstep (se 1 (by rfl) ⟨3589307, by rfl⟩ : syracuseStep 4785743 = 7178615) B7178615
theorem B3190495 : Blo 1889435 3190495 := bstep (se 1 (by rfl) ⟨2392871, by rfl⟩ : syracuseStep 3190495 = 4785743) B4785743
theorem B4253993 : Blo 1889435 4253993 := bstep (se 2 (by rfl) ⟨1595247, by rfl⟩ : syracuseStep 4253993 = 3190495) B3190495
theorem B2835995 : Blo 1889435 2835995 := bstep (se 1 (by rfl) ⟨2126996, by rfl⟩ : syracuseStep 2835995 = 4253993) B4253993
theorem B1890663 : Blo 1889435 1890663 := bstep (se 1 (by rfl) ⟨1417997, by rfl⟩ : syracuseStep 1890663 = 2835995) B2835995
theorem B2127001 : Blo 1889435 2127001 := bbase (se 2 (by rfl) ⟨797625, by rfl⟩ : syracuseStep 2127001 = 1595251) (by norm_num)
theorem B2836001 : Blo 1889435 2836001 := bstep (se 2 (by rfl) ⟨1063500, by rfl⟩ : syracuseStep 2836001 = 2127001) B2127001
theorem B1890667 : Blo 1889435 1890667 := bstep (se 1 (by rfl) ⟨1418000, by rfl⟩ : syracuseStep 1890667 = 2836001) B2836001
theorem B7178645 : Blo 1889435 7178645 := bbase (se 6 (by rfl) ⟨168249, by rfl⟩ : syracuseStep 7178645 = 336499) (by norm_num)
theorem B4785763 : Blo 1889435 4785763 := bstep (se 1 (by rfl) ⟨3589322, by rfl⟩ : syracuseStep 4785763 = 7178645) B7178645
theorem B6381017 : Blo 1889435 6381017 := bstep (se 2 (by rfl) ⟨2392881, by rfl⟩ : syracuseStep 6381017 = 4785763) B4785763
theorem B4254011 : Blo 1889435 4254011 := bstep (se 1 (by rfl) ⟨3190508, by rfl⟩ : syracuseStep 4254011 = 6381017) B6381017
theorem B2836007 : Blo 1889435 2836007 := bstep (se 1 (by rfl) ⟨2127005, by rfl⟩ : syracuseStep 2836007 = 4254011) B4254011
theorem B1890671 : Blo 1889435 1890671 := bstep (se 1 (by rfl) ⟨1418003, by rfl⟩ : syracuseStep 1890671 = 2836007) B2836007
theorem B2836013 : Blo 1889435 2836013 := bbase (se 3 (by rfl) ⟨531752, by rfl⟩ : syracuseStep 2836013 = 1063505) (by norm_num)
theorem B1890675 : Blo 1889435 1890675 := bstep (se 1 (by rfl) ⟨1418006, by rfl⟩ : syracuseStep 1890675 = 2836013) B2836013
theorem B4254029 : Blo 1889435 4254029 := bbase (se 3 (by rfl) ⟨797630, by rfl⟩ : syracuseStep 4254029 = 1595261) (by norm_num)
theorem B2836019 : Blo 1889435 2836019 := bstep (se 1 (by rfl) ⟨2127014, by rfl⟩ : syracuseStep 2836019 = 4254029) B4254029
theorem B1890679 : Blo 1889435 1890679 := bstep (se 1 (by rfl) ⟨1418009, by rfl⟩ : syracuseStep 1890679 = 2836019) B2836019
theorem B2392897 : Blo 1889435 2392897 := bbase (se 2 (by rfl) ⟨897336, by rfl⟩ : syracuseStep 2392897 = 1794673) (by norm_num)
theorem B3190529 : Blo 1889435 3190529 := bstep (se 2 (by rfl) ⟨1196448, by rfl⟩ : syracuseStep 3190529 = 2392897) B2392897
theorem B2127019 : Blo 1889435 2127019 := bstep (se 1 (by rfl) ⟨1595264, by rfl⟩ : syracuseStep 2127019 = 3190529) B3190529
theorem B2836025 : Blo 1889435 2836025 := bstep (se 2 (by rfl) ⟨1063509, by rfl⟩ : syracuseStep 2836025 = 2127019) B2127019
theorem B1890683 : Blo 1889435 1890683 := bstep (se 1 (by rfl) ⟨1418012, by rfl⟩ : syracuseStep 1890683 = 2836025) B2836025
theorem B3028517 : Blo 1889435 3028517 := bbase (se 4 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 3028517 = 567847) (by norm_num)
theorem B2019011 : Blo 1889435 2019011 := bstep (se 1 (by rfl) ⟨1514258, by rfl⟩ : syracuseStep 2019011 = 3028517) B3028517
theorem B21536117 : Blo 1889435 21536117 := bstep (se 5 (by rfl) ⟨1009505, by rfl⟩ : syracuseStep 21536117 = 2019011) B2019011
theorem B14357411 : Blo 1889435 14357411 := bstep (se 1 (by rfl) ⟨10768058, by rfl⟩ : syracuseStep 14357411 = 21536117) B21536117
theorem B9571607 : Blo 1889435 9571607 := bstep (se 1 (by rfl) ⟨7178705, by rfl⟩ : syracuseStep 9571607 = 14357411) B14357411
theorem B6381071 : Blo 1889435 6381071 := bstep (se 1 (by rfl) ⟨4785803, by rfl⟩ : syracuseStep 6381071 = 9571607) B9571607
theorem B4254047 : Blo 1889435 4254047 := bstep (se 1 (by rfl) ⟨3190535, by rfl⟩ : syracuseStep 4254047 = 6381071) B6381071
theorem B2836031 : Blo 1889435 2836031 := bstep (se 1 (by rfl) ⟨2127023, by rfl⟩ : syracuseStep 2836031 = 4254047) B4254047
theorem B1890687 : Blo 1889435 1890687 := bstep (se 1 (by rfl) ⟨1418015, by rfl⟩ : syracuseStep 1890687 = 2836031) B2836031
theorem B2836037 : Blo 1889435 2836037 := bbase (se 4 (by rfl) ⟨265878, by rfl⟩ : syracuseStep 2836037 = 531757) (by norm_num)
theorem B1890691 : Blo 1889435 1890691 := bstep (se 1 (by rfl) ⟨1418018, by rfl⟩ : syracuseStep 1890691 = 2836037) B2836037
theorem B3190549 : Blo 1889435 3190549 := bbase (se 6 (by rfl) ⟨74778, by rfl⟩ : syracuseStep 3190549 = 149557) (by norm_num)
theorem B4254065 : Blo 1889435 4254065 := bstep (se 2 (by rfl) ⟨1595274, by rfl⟩ : syracuseStep 4254065 = 3190549) B3190549
theorem B2836043 : Blo 1889435 2836043 := bstep (se 1 (by rfl) ⟨2127032, by rfl⟩ : syracuseStep 2836043 = 4254065) B4254065
theorem B1890695 : Blo 1889435 1890695 := bstep (se 1 (by rfl) ⟨1418021, by rfl⟩ : syracuseStep 1890695 = 2836043) B2836043
theorem B2127037 : Blo 1889435 2127037 := bbase (se 3 (by rfl) ⟨398819, by rfl⟩ : syracuseStep 2127037 = 797639) (by norm_num)
theorem B2836049 : Blo 1889435 2836049 := bstep (se 2 (by rfl) ⟨1063518, by rfl⟩ : syracuseStep 2836049 = 2127037) B2127037
theorem B1890699 : Blo 1889435 1890699 := bstep (se 1 (by rfl) ⟨1418024, by rfl⟩ : syracuseStep 1890699 = 2836049) B2836049
theorem B6381125 : Blo 1889435 6381125 := bbase (se 4 (by rfl) ⟨598230, by rfl⟩ : syracuseStep 6381125 = 1196461) (by norm_num)
theorem B4254083 : Blo 1889435 4254083 := bstep (se 1 (by rfl) ⟨3190562, by rfl⟩ : syracuseStep 4254083 = 6381125) B6381125
theorem B2836055 : Blo 1889435 2836055 := bstep (se 1 (by rfl) ⟨2127041, by rfl⟩ : syracuseStep 2836055 = 4254083) B4254083
theorem B1890703 : Blo 1889435 1890703 := bstep (se 1 (by rfl) ⟨1418027, by rfl⟩ : syracuseStep 1890703 = 2836055) B2836055
theorem B2836061 : Blo 1889435 2836061 := bbase (se 3 (by rfl) ⟨531761, by rfl⟩ : syracuseStep 2836061 = 1063523) (by norm_num)
theorem B1890707 : Blo 1889435 1890707 := bstep (se 1 (by rfl) ⟨1418030, by rfl⟩ : syracuseStep 1890707 = 2836061) B2836061
theorem B4254101 : Blo 1889435 4254101 := bbase (se 6 (by rfl) ⟨99705, by rfl⟩ : syracuseStep 4254101 = 199411) (by norm_num)
theorem B2836067 : Blo 1889435 2836067 := bstep (se 1 (by rfl) ⟨2127050, by rfl⟩ : syracuseStep 2836067 = 4254101) B4254101
theorem B1890711 : Blo 1889435 1890711 := bstep (se 1 (by rfl) ⟨1418033, by rfl⟩ : syracuseStep 1890711 = 2836067) B2836067
theorem B6057125 : Blo 1889435 6057125 := bbase (se 4 (by rfl) ⟨567855, by rfl⟩ : syracuseStep 6057125 = 1135711) (by norm_num)
theorem B4038083 : Blo 1889435 4038083 := bstep (se 1 (by rfl) ⟨3028562, by rfl⟩ : syracuseStep 4038083 = 6057125) B6057125
theorem B2692055 : Blo 1889435 2692055 := bstep (se 1 (by rfl) ⟨2019041, by rfl⟩ : syracuseStep 2692055 = 4038083) B4038083
theorem B7178813 : Blo 1889435 7178813 := bstep (se 3 (by rfl) ⟨1346027, by rfl⟩ : syracuseStep 7178813 = 2692055) B2692055
theorem B4785875 : Blo 1889435 4785875 := bstep (se 1 (by rfl) ⟨3589406, by rfl⟩ : syracuseStep 4785875 = 7178813) B7178813
theorem B3190583 : Blo 1889435 3190583 := bstep (se 1 (by rfl) ⟨2392937, by rfl⟩ : syracuseStep 3190583 = 4785875) B4785875
theorem B2127055 : Blo 1889435 2127055 := bstep (se 1 (by rfl) ⟨1595291, by rfl⟩ : syracuseStep 2127055 = 3190583) B3190583
theorem B2836073 : Blo 1889435 2836073 := bstep (se 2 (by rfl) ⟨1063527, by rfl⟩ : syracuseStep 2836073 = 2127055) B2127055
theorem B1890715 : Blo 1889435 1890715 := bstep (se 1 (by rfl) ⟨1418036, by rfl⟩ : syracuseStep 1890715 = 2836073) B2836073
theorem B8076181 : Blo 1889435 8076181 := bbase (se 6 (by rfl) ⟨189285, by rfl⟩ : syracuseStep 8076181 = 378571) (by norm_num)
theorem B10768241 : Blo 1889435 10768241 := bstep (se 2 (by rfl) ⟨4038090, by rfl⟩ : syracuseStep 10768241 = 8076181) B8076181
theorem B7178827 : Blo 1889435 7178827 := bstep (se 1 (by rfl) ⟨5384120, by rfl⟩ : syracuseStep 7178827 = 10768241) B10768241
theorem B9571769 : Blo 1889435 9571769 := bstep (se 2 (by rfl) ⟨3589413, by rfl⟩ : syracuseStep 9571769 = 7178827) B7178827
theorem B6381179 : Blo 1889435 6381179 := bstep (se 1 (by rfl) ⟨4785884, by rfl⟩ : syracuseStep 6381179 = 9571769) B9571769
theorem B4254119 : Blo 1889435 4254119 := bstep (se 1 (by rfl) ⟨3190589, by rfl⟩ : syracuseStep 4254119 = 6381179) B6381179
theorem B2836079 : Blo 1889435 2836079 := bstep (se 1 (by rfl) ⟨2127059, by rfl⟩ : syracuseStep 2836079 = 4254119) B4254119
theorem B1890719 : Blo 1889435 1890719 := bstep (se 1 (by rfl) ⟨1418039, by rfl⟩ : syracuseStep 1890719 = 2836079) B2836079
theorem B2836085 : Blo 1889435 2836085 := bbase (se 5 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 2836085 = 265883) (by norm_num)
theorem B1890723 : Blo 1889435 1890723 := bstep (se 1 (by rfl) ⟨1418042, by rfl⟩ : syracuseStep 1890723 = 2836085) B2836085
theorem B3589429 : Blo 1889435 3589429 := bbase (se 5 (by rfl) ⟨168254, by rfl⟩ : syracuseStep 3589429 = 336509) (by norm_num)
theorem B4785905 : Blo 1889435 4785905 := bstep (se 2 (by rfl) ⟨1794714, by rfl⟩ : syracuseStep 4785905 = 3589429) B3589429
theorem B3190603 : Blo 1889435 3190603 := bstep (se 1 (by rfl) ⟨2392952, by rfl⟩ : syracuseStep 3190603 = 4785905) B4785905
theorem B4254137 : Blo 1889435 4254137 := bstep (se 2 (by rfl) ⟨1595301, by rfl⟩ : syracuseStep 4254137 = 3190603) B3190603
theorem B2836091 : Blo 1889435 2836091 := bstep (se 1 (by rfl) ⟨2127068, by rfl⟩ : syracuseStep 2836091 = 4254137) B4254137
theorem B1890727 : Blo 1889435 1890727 := bstep (se 1 (by rfl) ⟨1418045, by rfl⟩ : syracuseStep 1890727 = 2836091) B2836091
theorem B2127073 : Blo 1889435 2127073 := bbase (se 2 (by rfl) ⟨797652, by rfl⟩ : syracuseStep 2127073 = 1595305) (by norm_num)
theorem B2836097 : Blo 1889435 2836097 := bstep (se 2 (by rfl) ⟨1063536, by rfl⟩ : syracuseStep 2836097 = 2127073) B2127073
theorem B1890731 : Blo 1889435 1890731 := bstep (se 1 (by rfl) ⟨1418048, by rfl⟩ : syracuseStep 1890731 = 2836097) B2836097
theorem B4785925 : Blo 1889435 4785925 := bbase (se 4 (by rfl) ⟨448680, by rfl⟩ : syracuseStep 4785925 = 897361) (by norm_num)
theorem B6381233 : Blo 1889435 6381233 := bstep (se 2 (by rfl) ⟨2392962, by rfl⟩ : syracuseStep 6381233 = 4785925) B4785925
theorem B4254155 : Blo 1889435 4254155 := bstep (se 1 (by rfl) ⟨3190616, by rfl⟩ : syracuseStep 4254155 = 6381233) B6381233
theorem B2836103 : Blo 1889435 2836103 := bstep (se 1 (by rfl) ⟨2127077, by rfl⟩ : syracuseStep 2836103 = 4254155) B4254155
theorem B1890735 : Blo 1889435 1890735 := bstep (se 1 (by rfl) ⟨1418051, by rfl⟩ : syracuseStep 1890735 = 2836103) B2836103
theorem B2836109 : Blo 1889435 2836109 := bbase (se 3 (by rfl) ⟨531770, by rfl⟩ : syracuseStep 2836109 = 1063541) (by norm_num)
theorem B1890739 : Blo 1889435 1890739 := bstep (se 1 (by rfl) ⟨1418054, by rfl⟩ : syracuseStep 1890739 = 2836109) B2836109
theorem B4254173 : Blo 1889435 4254173 := bbase (se 3 (by rfl) ⟨797657, by rfl⟩ : syracuseStep 4254173 = 1595315) (by norm_num)
theorem B2836115 : Blo 1889435 2836115 := bstep (se 1 (by rfl) ⟨2127086, by rfl⟩ : syracuseStep 2836115 = 4254173) B4254173
theorem B1890743 : Blo 1889435 1890743 := bstep (se 1 (by rfl) ⟨1418057, by rfl⟩ : syracuseStep 1890743 = 2836115) B2836115
theorem B3190637 : Blo 1889435 3190637 := bbase (se 3 (by rfl) ⟨598244, by rfl⟩ : syracuseStep 3190637 = 1196489) (by norm_num)
theorem B2127091 : Blo 1889435 2127091 := bstep (se 1 (by rfl) ⟨1595318, by rfl⟩ : syracuseStep 2127091 = 3190637) B3190637
theorem B2836121 : Blo 1889435 2836121 := bstep (se 2 (by rfl) ⟨1063545, by rfl⟩ : syracuseStep 2836121 = 2127091) B2127091
theorem B1890747 : Blo 1889435 1890747 := bstep (se 1 (by rfl) ⟨1418060, by rfl⟩ : syracuseStep 1890747 = 2836121) B2836121
theorem B2156117 : Blo 1889435 2156117 := bbase (se 8 (by rfl) ⟨12633, by rfl⟩ : syracuseStep 2156117 = 25267) (by norm_num)
theorem B5749645 : Blo 1889435 5749645 := bstep (se 3 (by rfl) ⟨1078058, by rfl⟩ : syracuseStep 5749645 = 2156117) B2156117
theorem B7666193 : Blo 1889435 7666193 := bstep (se 2 (by rfl) ⟨2874822, by rfl⟩ : syracuseStep 7666193 = 5749645) B5749645
theorem B5110795 : Blo 1889435 5110795 := bstep (se 1 (by rfl) ⟨3833096, by rfl⟩ : syracuseStep 5110795 = 7666193) B7666193
theorem B27257573 : Blo 1889435 27257573 := bstep (se 4 (by rfl) ⟨2555397, by rfl⟩ : syracuseStep 27257573 = 5110795) B5110795
theorem B18171715 : Blo 1889435 18171715 := bstep (se 1 (by rfl) ⟨13628786, by rfl⟩ : syracuseStep 18171715 = 27257573) B27257573
theorem B24228953 : Blo 1889435 24228953 := bstep (se 2 (by rfl) ⟨9085857, by rfl⟩ : syracuseStep 24228953 = 18171715) B18171715
theorem B16152635 : Blo 1889435 16152635 := bstep (se 1 (by rfl) ⟨12114476, by rfl⟩ : syracuseStep 16152635 = 24228953) B24228953
theorem B10768423 : Blo 1889435 10768423 := bstep (se 1 (by rfl) ⟨8076317, by rfl⟩ : syracuseStep 10768423 = 16152635) B16152635
theorem B14357897 : Blo 1889435 14357897 := bstep (se 2 (by rfl) ⟨5384211, by rfl⟩ : syracuseStep 14357897 = 10768423) B10768423
theorem B9571931 : Blo 1889435 9571931 := bstep (se 1 (by rfl) ⟨7178948, by rfl⟩ : syracuseStep 9571931 = 14357897) B14357897
theorem B6381287 : Blo 1889435 6381287 := bstep (se 1 (by rfl) ⟨4785965, by rfl⟩ : syracuseStep 6381287 = 9571931) B9571931
theorem B4254191 : Blo 1889435 4254191 := bstep (se 1 (by rfl) ⟨3190643, by rfl⟩ : syracuseStep 4254191 = 6381287) B6381287
theorem B2836127 : Blo 1889435 2836127 := bstep (se 1 (by rfl) ⟨2127095, by rfl⟩ : syracuseStep 2836127 = 4254191) B4254191
theorem B1890751 : Blo 1889435 1890751 := bstep (se 1 (by rfl) ⟨1418063, by rfl⟩ : syracuseStep 1890751 = 2836127) B2836127
theorem B2836133 : Blo 1889435 2836133 := bbase (se 4 (by rfl) ⟨265887, by rfl⟩ : syracuseStep 2836133 = 531775) (by norm_num)
theorem B1890755 : Blo 1889435 1890755 := bstep (se 1 (by rfl) ⟨1418066, by rfl⟩ : syracuseStep 1890755 = 2836133) B2836133
theorem B2392993 : Blo 1889435 2392993 := bbase (se 2 (by rfl) ⟨897372, by rfl⟩ : syracuseStep 2392993 = 1794745) (by norm_num)
theorem B3190657 : Blo 1889435 3190657 := bstep (se 2 (by rfl) ⟨1196496, by rfl⟩ : syracuseStep 3190657 = 2392993) B2392993
theorem B4254209 : Blo 1889435 4254209 := bstep (se 2 (by rfl) ⟨1595328, by rfl⟩ : syracuseStep 4254209 = 3190657) B3190657
theorem B2836139 : Blo 1889435 2836139 := bstep (se 1 (by rfl) ⟨2127104, by rfl⟩ : syracuseStep 2836139 = 4254209) B4254209
theorem B1890759 : Blo 1889435 1890759 := bstep (se 1 (by rfl) ⟨1418069, by rfl⟩ : syracuseStep 1890759 = 2836139) B2836139
theorem B2127109 : Blo 1889435 2127109 := bbase (se 4 (by rfl) ⟨199416, by rfl⟩ : syracuseStep 2127109 = 398833) (by norm_num)
theorem B2836145 : Blo 1889435 2836145 := bstep (se 2 (by rfl) ⟨1063554, by rfl⟩ : syracuseStep 2836145 = 2127109) B2127109
theorem B1890763 : Blo 1889435 1890763 := bstep (se 1 (by rfl) ⟨1418072, by rfl⟩ : syracuseStep 1890763 = 2836145) B2836145
theorem B2019097 : Blo 1889435 2019097 := bbase (se 2 (by rfl) ⟨757161, by rfl⟩ : syracuseStep 2019097 = 1514323) (by norm_num)
theorem B2692129 : Blo 1889435 2692129 := bstep (se 2 (by rfl) ⟨1009548, by rfl⟩ : syracuseStep 2692129 = 2019097) B2019097
theorem B3589505 : Blo 1889435 3589505 := bstep (se 2 (by rfl) ⟨1346064, by rfl⟩ : syracuseStep 3589505 = 2692129) B2692129
theorem B2393003 : Blo 1889435 2393003 := bstep (se 1 (by rfl) ⟨1794752, by rfl⟩ : syracuseStep 2393003 = 3589505) B3589505
theorem B6381341 : Blo 1889435 6381341 := bstep (se 3 (by rfl) ⟨1196501, by rfl⟩ : syracuseStep 6381341 = 2393003) B2393003
theorem B4254227 : Blo 1889435 4254227 := bstep (se 1 (by rfl) ⟨3190670, by rfl⟩ : syracuseStep 4254227 = 6381341) B6381341
theorem B2836151 : Blo 1889435 2836151 := bstep (se 1 (by rfl) ⟨2127113, by rfl⟩ : syracuseStep 2836151 = 4254227) B4254227
theorem B1890767 : Blo 1889435 1890767 := bstep (se 1 (by rfl) ⟨1418075, by rfl⟩ : syracuseStep 1890767 = 2836151) B2836151
theorem B2836157 : Blo 1889435 2836157 := bbase (se 3 (by rfl) ⟨531779, by rfl⟩ : syracuseStep 2836157 = 1063559) (by norm_num)
theorem B1890771 : Blo 1889435 1890771 := bstep (se 1 (by rfl) ⟨1418078, by rfl⟩ : syracuseStep 1890771 = 2836157) B2836157
theorem B4254245 : Blo 1889435 4254245 := bbase (se 4 (by rfl) ⟨398835, by rfl⟩ : syracuseStep 4254245 = 797671) (by norm_num)
theorem B2836163 : Blo 1889435 2836163 := bstep (se 1 (by rfl) ⟨2127122, by rfl⟩ : syracuseStep 2836163 = 4254245) B4254245
theorem B1890775 : Blo 1889435 1890775 := bstep (se 1 (by rfl) ⟨1418081, by rfl⟩ : syracuseStep 1890775 = 2836163) B2836163
theorem B4786037 : Blo 1889435 4786037 := bbase (se 5 (by rfl) ⟨224345, by rfl⟩ : syracuseStep 4786037 = 448691) (by norm_num)
theorem B3190691 : Blo 1889435 3190691 := bstep (se 1 (by rfl) ⟨2393018, by rfl⟩ : syracuseStep 3190691 = 4786037) B4786037
theorem B2127127 : Blo 1889435 2127127 := bstep (se 1 (by rfl) ⟨1595345, by rfl⟩ : syracuseStep 2127127 = 3190691) B3190691
theorem B2836169 : Blo 1889435 2836169 := bstep (se 2 (by rfl) ⟨1063563, by rfl⟩ : syracuseStep 2836169 = 2127127) B2127127
theorem B1890779 : Blo 1889435 1890779 := bstep (se 1 (by rfl) ⟨1418084, by rfl⟩ : syracuseStep 1890779 = 2836169) B2836169
theorem B14554037 : Blo 1889435 14554037 := bbase (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) (by norm_num)
theorem B38810765 : Blo 1889435 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B25873843 : Blo 1889435 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B34498457 : Blo 1889435 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B22998971 : Blo 1889435 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B15332647 : Blo 1889435 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B20443529 : Blo 1889435 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B13629019 : Blo 1889435 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B18172025 : Blo 1889435 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B12114683 : Blo 1889435 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B8076455 : Blo 1889435 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B5384303 : Blo 1889435 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B3589535 : Blo 1889435 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B9572093 : Blo 1889435 9572093 := bstep (se 3 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 9572093 = 3589535) B3589535
theorem B6381395 : Blo 1889435 6381395 := bstep (se 1 (by rfl) ⟨4786046, by rfl⟩ : syracuseStep 6381395 = 9572093) B9572093
theorem B4254263 : Blo 1889435 4254263 := bstep (se 1 (by rfl) ⟨3190697, by rfl⟩ : syracuseStep 4254263 = 6381395) B6381395
theorem B2836175 : Blo 1889435 2836175 := bstep (se 1 (by rfl) ⟨2127131, by rfl⟩ : syracuseStep 2836175 = 4254263) B4254263
theorem B1890783 : Blo 1889435 1890783 := bstep (se 1 (by rfl) ⟨1418087, by rfl⟩ : syracuseStep 1890783 = 2836175) B2836175
theorem B2836181 : Blo 1889435 2836181 := bbase (se 7 (by rfl) ⟨33236, by rfl⟩ : syracuseStep 2836181 = 66473) (by norm_num)
theorem B1890787 : Blo 1889435 1890787 := bstep (se 1 (by rfl) ⟨1418090, by rfl⟩ : syracuseStep 1890787 = 2836181) B2836181
theorem B4038245 : Blo 1889435 4038245 := bbase (se 4 (by rfl) ⟨378585, by rfl⟩ : syracuseStep 4038245 = 757171) (by norm_num)
theorem B2692163 : Blo 1889435 2692163 := bstep (se 1 (by rfl) ⟨2019122, by rfl⟩ : syracuseStep 2692163 = 4038245) B4038245
theorem B7179101 : Blo 1889435 7179101 := bstep (se 3 (by rfl) ⟨1346081, by rfl⟩ : syracuseStep 7179101 = 2692163) B2692163
theorem B4786067 : Blo 1889435 4786067 := bstep (se 1 (by rfl) ⟨3589550, by rfl⟩ : syracuseStep 4786067 = 7179101) B7179101
theorem B3190711 : Blo 1889435 3190711 := bstep (se 1 (by rfl) ⟨2393033, by rfl⟩ : syracuseStep 3190711 = 4786067) B4786067
theorem B4254281 : Blo 1889435 4254281 := bstep (se 2 (by rfl) ⟨1595355, by rfl⟩ : syracuseStep 4254281 = 3190711) B3190711
theorem B2836187 : Blo 1889435 2836187 := bstep (se 1 (by rfl) ⟨2127140, by rfl⟩ : syracuseStep 2836187 = 4254281) B4254281
theorem B1890791 : Blo 1889435 1890791 := bstep (se 1 (by rfl) ⟨1418093, by rfl⟩ : syracuseStep 1890791 = 2836187) B2836187
theorem B2127145 : Blo 1889435 2127145 := bbase (se 2 (by rfl) ⟨797679, by rfl⟩ : syracuseStep 2127145 = 1595359) (by norm_num)
theorem B2836193 : Blo 1889435 2836193 := bstep (se 2 (by rfl) ⟨1063572, by rfl⟩ : syracuseStep 2836193 = 2127145) B2127145
theorem B1890795 : Blo 1889435 1890795 := bstep (se 1 (by rfl) ⟨1418096, by rfl⟩ : syracuseStep 1890795 = 2836193) B2836193
theorem B2333929 : Blo 1889435 2333929 := bbase (se 2 (by rfl) ⟨875223, by rfl⟩ : syracuseStep 2333929 = 1750447) (by norm_num)
theorem B3111905 : Blo 1889435 3111905 := bstep (se 2 (by rfl) ⟨1166964, by rfl⟩ : syracuseStep 3111905 = 2333929) B2333929
theorem B8298413 : Blo 1889435 8298413 := bstep (se 3 (by rfl) ⟨1555952, by rfl⟩ : syracuseStep 8298413 = 3111905) B3111905
theorem B5532275 : Blo 1889435 5532275 := bstep (se 1 (by rfl) ⟨4149206, by rfl⟩ : syracuseStep 5532275 = 8298413) B8298413
theorem B3688183 : Blo 1889435 3688183 := bstep (se 1 (by rfl) ⟨2766137, by rfl⟩ : syracuseStep 3688183 = 5532275) B5532275
theorem B4917577 : Blo 1889435 4917577 := bstep (se 2 (by rfl) ⟨1844091, by rfl⟩ : syracuseStep 4917577 = 3688183) B3688183
theorem B6556769 : Blo 1889435 6556769 := bstep (se 2 (by rfl) ⟨2458788, by rfl⟩ : syracuseStep 6556769 = 4917577) B4917577
theorem B4371179 : Blo 1889435 4371179 := bstep (se 1 (by rfl) ⟨3278384, by rfl⟩ : syracuseStep 4371179 = 6556769) B6556769
theorem B11656477 : Blo 1889435 11656477 := bstep (se 3 (by rfl) ⟨2185589, by rfl⟩ : syracuseStep 11656477 = 4371179) B4371179
theorem B15541969 : Blo 1889435 15541969 := bstep (se 2 (by rfl) ⟨5828238, by rfl⟩ : syracuseStep 15541969 = 11656477) B11656477
theorem B20722625 : Blo 1889435 20722625 := bstep (se 2 (by rfl) ⟨7770984, by rfl⟩ : syracuseStep 20722625 = 15541969) B15541969
theorem B13815083 : Blo 1889435 13815083 := bstep (se 1 (by rfl) ⟨10361312, by rfl⟩ : syracuseStep 13815083 = 20722625) B20722625
theorem B36840221 : Blo 1889435 36840221 := bstep (se 3 (by rfl) ⟨6907541, by rfl⟩ : syracuseStep 36840221 = 13815083) B13815083
theorem B24560147 : Blo 1889435 24560147 := bstep (se 1 (by rfl) ⟨18420110, by rfl⟩ : syracuseStep 24560147 = 36840221) B36840221
theorem B16373431 : Blo 1889435 16373431 := bstep (se 1 (by rfl) ⟨12280073, by rfl⟩ : syracuseStep 16373431 = 24560147) B24560147
theorem B87324965 : Blo 1889435 87324965 := bstep (se 4 (by rfl) ⟨8186715, by rfl⟩ : syracuseStep 87324965 = 16373431) B16373431
theorem B58216643 : Blo 1889435 58216643 := bstep (se 1 (by rfl) ⟨43662482, by rfl⟩ : syracuseStep 58216643 = 87324965) B87324965
theorem B38811095 : Blo 1889435 38811095 := bstep (se 1 (by rfl) ⟨29108321, by rfl⟩ : syracuseStep 38811095 = 58216643) B58216643
theorem B25874063 : Blo 1889435 25874063 := bstep (se 1 (by rfl) ⟨19405547, by rfl⟩ : syracuseStep 25874063 = 38811095) B38811095
theorem B17249375 : Blo 1889435 17249375 := bstep (se 1 (by rfl) ⟨12937031, by rfl⟩ : syracuseStep 17249375 = 25874063) B25874063
theorem B11499583 : Blo 1889435 11499583 := bstep (se 1 (by rfl) ⟨8624687, by rfl⟩ : syracuseStep 11499583 = 17249375) B17249375
theorem B15332777 : Blo 1889435 15332777 := bstep (se 2 (by rfl) ⟨5749791, by rfl⟩ : syracuseStep 15332777 = 11499583) B11499583
theorem B10221851 : Blo 1889435 10221851 := bstep (se 1 (by rfl) ⟨7666388, by rfl⟩ : syracuseStep 10221851 = 15332777) B15332777
theorem B6814567 : Blo 1889435 6814567 := bstep (se 1 (by rfl) ⟨5110925, by rfl⟩ : syracuseStep 6814567 = 10221851) B10221851
theorem B9086089 : Blo 1889435 9086089 := bstep (se 2 (by rfl) ⟨3407283, by rfl⟩ : syracuseStep 9086089 = 6814567) B6814567
theorem B12114785 : Blo 1889435 12114785 := bstep (se 2 (by rfl) ⟨4543044, by rfl⟩ : syracuseStep 12114785 = 9086089) B9086089
theorem B8076523 : Blo 1889435 8076523 := bstep (se 1 (by rfl) ⟨6057392, by rfl⟩ : syracuseStep 8076523 = 12114785) B12114785
theorem B10768697 : Blo 1889435 10768697 := bstep (se 2 (by rfl) ⟨4038261, by rfl⟩ : syracuseStep 10768697 = 8076523) B8076523
theorem B7179131 : Blo 1889435 7179131 := bstep (se 1 (by rfl) ⟨5384348, by rfl⟩ : syracuseStep 7179131 = 10768697) B10768697
theorem B4786087 : Blo 1889435 4786087 := bstep (se 1 (by rfl) ⟨3589565, by rfl⟩ : syracuseStep 4786087 = 7179131) B7179131
theorem B6381449 : Blo 1889435 6381449 := bstep (se 2 (by rfl) ⟨2393043, by rfl⟩ : syracuseStep 6381449 = 4786087) B4786087
theorem B4254299 : Blo 1889435 4254299 := bstep (se 1 (by rfl) ⟨3190724, by rfl⟩ : syracuseStep 4254299 = 6381449) B6381449
theorem B2836199 : Blo 1889435 2836199 := bstep (se 1 (by rfl) ⟨2127149, by rfl⟩ : syracuseStep 2836199 = 4254299) B4254299
theorem B1890799 : Blo 1889435 1890799 := bstep (se 1 (by rfl) ⟨1418099, by rfl⟩ : syracuseStep 1890799 = 2836199) B2836199
theorem B2836205 : Blo 1889435 2836205 := bbase (se 3 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 2836205 = 1063577) (by norm_num)
theorem B1890803 : Blo 1889435 1890803 := bstep (se 1 (by rfl) ⟨1418102, by rfl⟩ : syracuseStep 1890803 = 2836205) B2836205
theorem B4254317 : Blo 1889435 4254317 := bbase (se 3 (by rfl) ⟨797684, by rfl⟩ : syracuseStep 4254317 = 1595369) (by norm_num)
theorem B2836211 : Blo 1889435 2836211 := bstep (se 1 (by rfl) ⟨2127158, by rfl⟩ : syracuseStep 2836211 = 4254317) B4254317
theorem B1890807 : Blo 1889435 1890807 := bstep (se 1 (by rfl) ⟨1418105, by rfl⟩ : syracuseStep 1890807 = 2836211) B2836211
theorem B3589589 : Blo 1889435 3589589 := bbase (se 7 (by rfl) ⟨42065, by rfl⟩ : syracuseStep 3589589 = 84131) (by norm_num)
theorem B2393059 : Blo 1889435 2393059 := bstep (se 1 (by rfl) ⟨1794794, by rfl⟩ : syracuseStep 2393059 = 3589589) B3589589
theorem B3190745 : Blo 1889435 3190745 := bstep (se 2 (by rfl) ⟨1196529, by rfl⟩ : syracuseStep 3190745 = 2393059) B2393059
theorem B2127163 : Blo 1889435 2127163 := bstep (se 1 (by rfl) ⟨1595372, by rfl⟩ : syracuseStep 2127163 = 3190745) B3190745
theorem B2836217 : Blo 1889435 2836217 := bstep (se 2 (by rfl) ⟨1063581, by rfl⟩ : syracuseStep 2836217 = 2127163) B2127163
theorem B1890811 : Blo 1889435 1890811 := bstep (se 1 (by rfl) ⟨1418108, by rfl⟩ : syracuseStep 1890811 = 2836217) B2836217
theorem B38811413 : Blo 1889435 38811413 := bbase (se 6 (by rfl) ⟨909642, by rfl⟩ : syracuseStep 38811413 = 1819285) (by norm_num)
theorem B103497101 : Blo 1889435 103497101 := bstep (se 3 (by rfl) ⟨19405706, by rfl⟩ : syracuseStep 103497101 = 38811413) B38811413
theorem B68998067 : Blo 1889435 68998067 := bstep (se 1 (by rfl) ⟨51748550, by rfl⟩ : syracuseStep 68998067 = 103497101) B103497101
theorem B45998711 : Blo 1889435 45998711 := bstep (se 1 (by rfl) ⟨34499033, by rfl⟩ : syracuseStep 45998711 = 68998067) B68998067
theorem B30665807 : Blo 1889435 30665807 := bstep (se 1 (by rfl) ⟨22999355, by rfl⟩ : syracuseStep 30665807 = 45998711) B45998711
theorem B20443871 : Blo 1889435 20443871 := bstep (se 1 (by rfl) ⟨15332903, by rfl⟩ : syracuseStep 20443871 = 30665807) B30665807
theorem B54516989 : Blo 1889435 54516989 := bstep (se 3 (by rfl) ⟨10221935, by rfl⟩ : syracuseStep 54516989 = 20443871) B20443871
theorem B36344659 : Blo 1889435 36344659 := bstep (se 1 (by rfl) ⟨27258494, by rfl⟩ : syracuseStep 36344659 = 54516989) B54516989
theorem B48459545 : Blo 1889435 48459545 := bstep (se 2 (by rfl) ⟨18172329, by rfl⟩ : syracuseStep 48459545 = 36344659) B36344659
theorem B32306363 : Blo 1889435 32306363 := bstep (se 1 (by rfl) ⟨24229772, by rfl⟩ : syracuseStep 32306363 = 48459545) B48459545
theorem B21537575 : Blo 1889435 21537575 := bstep (se 1 (by rfl) ⟨16153181, by rfl⟩ : syracuseStep 21537575 = 32306363) B32306363
theorem B14358383 : Blo 1889435 14358383 := bstep (se 1 (by rfl) ⟨10768787, by rfl⟩ : syracuseStep 14358383 = 21537575) B21537575
theorem B9572255 : Blo 1889435 9572255 := bstep (se 1 (by rfl) ⟨7179191, by rfl⟩ : syracuseStep 9572255 = 14358383) B14358383
theorem B6381503 : Blo 1889435 6381503 := bstep (se 1 (by rfl) ⟨4786127, by rfl⟩ : syracuseStep 6381503 = 9572255) B9572255
theorem B4254335 : Blo 1889435 4254335 := bstep (se 1 (by rfl) ⟨3190751, by rfl⟩ : syracuseStep 4254335 = 6381503) B6381503
theorem B2836223 : Blo 1889435 2836223 := bstep (se 1 (by rfl) ⟨2127167, by rfl⟩ : syracuseStep 2836223 = 4254335) B4254335
theorem B1890815 : Blo 1889435 1890815 := bstep (se 1 (by rfl) ⟨1418111, by rfl⟩ : syracuseStep 1890815 = 2836223) B2836223
theorem B2836229 : Blo 1889435 2836229 := bbase (se 4 (by rfl) ⟨265896, by rfl⟩ : syracuseStep 2836229 = 531793) (by norm_num)
theorem B1890819 : Blo 1889435 1890819 := bstep (se 1 (by rfl) ⟨1418114, by rfl⟩ : syracuseStep 1890819 = 2836229) B2836229
theorem B3190765 : Blo 1889435 3190765 := bbase (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) (by norm_num)
theorem B4254353 : Blo 1889435 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B2836235 : Blo 1889435 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B1890823 : Blo 1889435 1890823 := bstep (se 1 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 1890823 = 2836235) B2836235
theorem B2127181 : Blo 1889435 2127181 := bbase (se 3 (by rfl) ⟨398846, by rfl⟩ : syracuseStep 2127181 = 797693) (by norm_num)
theorem B2836241 : Blo 1889435 2836241 := bstep (se 2 (by rfl) ⟨1063590, by rfl⟩ : syracuseStep 2836241 = 2127181) B2127181
theorem B1890827 : Blo 1889435 1890827 := bstep (se 1 (by rfl) ⟨1418120, by rfl⟩ : syracuseStep 1890827 = 2836241) B2836241
theorem B6381557 : Blo 1889435 6381557 := bbase (se 5 (by rfl) ⟨299135, by rfl⟩ : syracuseStep 6381557 = 598271) (by norm_num)
theorem B4254371 : Blo 1889435 4254371 := bstep (se 1 (by rfl) ⟨3190778, by rfl⟩ : syracuseStep 4254371 = 6381557) B6381557
theorem B2836247 : Blo 1889435 2836247 := bstep (se 1 (by rfl) ⟨2127185, by rfl⟩ : syracuseStep 2836247 = 4254371) B4254371
theorem B1890831 : Blo 1889435 1890831 := bstep (se 1 (by rfl) ⟨1418123, by rfl⟩ : syracuseStep 1890831 = 2836247) B2836247
theorem B2836253 : Blo 1889435 2836253 := bbase (se 3 (by rfl) ⟨531797, by rfl⟩ : syracuseStep 2836253 = 1063595) (by norm_num)
theorem B1890835 : Blo 1889435 1890835 := bstep (se 1 (by rfl) ⟨1418126, by rfl⟩ : syracuseStep 1890835 = 2836253) B2836253
theorem B4254389 : Blo 1889435 4254389 := bbase (se 5 (by rfl) ⟨199424, by rfl⟩ : syracuseStep 4254389 = 398849) (by norm_num)
theorem B2836259 : Blo 1889435 2836259 := bstep (se 1 (by rfl) ⟨2127194, by rfl⟩ : syracuseStep 2836259 = 4254389) B4254389
theorem B1890839 : Blo 1889435 1890839 := bstep (se 1 (by rfl) ⟨1418129, by rfl⟩ : syracuseStep 1890839 = 2836259) B2836259
theorem B10768949 : Blo 1889435 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B7179299 : Blo 1889435 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B4786199 : Blo 1889435 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B3190799 : Blo 1889435 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B2127199 : Blo 1889435 2127199 := bstep (se 1 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 2127199 = 3190799) B3190799
theorem B2836265 : Blo 1889435 2836265 := bstep (se 2 (by rfl) ⟨1063599, by rfl⟩ : syracuseStep 2836265 = 2127199) B2127199
theorem B1890843 : Blo 1889435 1890843 := bstep (se 1 (by rfl) ⟨1418132, by rfl⟩ : syracuseStep 1890843 = 2836265) B2836265
theorem B5384485 : Blo 1889435 5384485 := bbase (se 4 (by rfl) ⟨504795, by rfl⟩ : syracuseStep 5384485 = 1009591) (by norm_num)
theorem B7179313 : Blo 1889435 7179313 := bstep (se 2 (by rfl) ⟨2692242, by rfl⟩ : syracuseStep 7179313 = 5384485) B5384485
theorem B9572417 : Blo 1889435 9572417 := bstep (se 2 (by rfl) ⟨3589656, by rfl⟩ : syracuseStep 9572417 = 7179313) B7179313
theorem B6381611 : Blo 1889435 6381611 := bstep (se 1 (by rfl) ⟨4786208, by rfl⟩ : syracuseStep 6381611 = 9572417) B9572417
theorem B4254407 : Blo 1889435 4254407 := bstep (se 1 (by rfl) ⟨3190805, by rfl⟩ : syracuseStep 4254407 = 6381611) B6381611
theorem B2836271 : Blo 1889435 2836271 := bstep (se 1 (by rfl) ⟨2127203, by rfl⟩ : syracuseStep 2836271 = 4254407) B4254407
theorem B1890847 : Blo 1889435 1890847 := bstep (se 1 (by rfl) ⟨1418135, by rfl⟩ : syracuseStep 1890847 = 2836271) B2836271
theorem B2836277 : Blo 1889435 2836277 := bbase (se 5 (by rfl) ⟨132950, by rfl⟩ : syracuseStep 2836277 = 265901) (by norm_num)
theorem B1890851 : Blo 1889435 1890851 := bstep (se 1 (by rfl) ⟨1418138, by rfl⟩ : syracuseStep 1890851 = 2836277) B2836277
theorem B4786229 : Blo 1889435 4786229 := bbase (se 5 (by rfl) ⟨224354, by rfl⟩ : syracuseStep 4786229 = 448709) (by norm_num)
theorem B3190819 : Blo 1889435 3190819 := bstep (se 1 (by rfl) ⟨2393114, by rfl⟩ : syracuseStep 3190819 = 4786229) B4786229
theorem B4254425 : Blo 1889435 4254425 := bstep (se 2 (by rfl) ⟨1595409, by rfl⟩ : syracuseStep 4254425 = 3190819) B3190819
theorem B2836283 : Blo 1889435 2836283 := bstep (se 1 (by rfl) ⟨2127212, by rfl⟩ : syracuseStep 2836283 = 4254425) B4254425
theorem B1890855 : Blo 1889435 1890855 := bstep (se 1 (by rfl) ⟨1418141, by rfl⟩ : syracuseStep 1890855 = 2836283) B2836283
theorem B2127217 : Blo 1889435 2127217 := bbase (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) (by norm_num)
theorem B2836289 : Blo 1889435 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B1890859 : Blo 1889435 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B8624981 : Blo 1889435 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B22999949 : Blo 1889435 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B15333299 : Blo 1889435 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B10222199 : Blo 1889435 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B6814799 : Blo 1889435 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B4543199 : Blo 1889435 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B3028799 : Blo 1889435 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B8076797 : Blo 1889435 8076797 := bstep (se 3 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 8076797 = 3028799) B3028799
theorem B5384531 : Blo 1889435 5384531 := bstep (se 1 (by rfl) ⟨4038398, by rfl⟩ : syracuseStep 5384531 = 8076797) B8076797
theorem B3589687 : Blo 1889435 3589687 := bstep (se 1 (by rfl) ⟨2692265, by rfl⟩ : syracuseStep 3589687 = 5384531) B5384531
theorem B4786249 : Blo 1889435 4786249 := bstep (se 2 (by rfl) ⟨1794843, by rfl⟩ : syracuseStep 4786249 = 3589687) B3589687
theorem B6381665 : Blo 1889435 6381665 := bstep (se 2 (by rfl) ⟨2393124, by rfl⟩ : syracuseStep 6381665 = 4786249) B4786249
theorem B4254443 : Blo 1889435 4254443 := bstep (se 1 (by rfl) ⟨3190832, by rfl⟩ : syracuseStep 4254443 = 6381665) B6381665
theorem B2836295 : Blo 1889435 2836295 := bstep (se 1 (by rfl) ⟨2127221, by rfl⟩ : syracuseStep 2836295 = 4254443) B4254443
theorem B1890863 : Blo 1889435 1890863 := bstep (se 1 (by rfl) ⟨1418147, by rfl⟩ : syracuseStep 1890863 = 2836295) B2836295
theorem B2836301 : Blo 1889435 2836301 := bbase (se 3 (by rfl) ⟨531806, by rfl⟩ : syracuseStep 2836301 = 1063613) (by norm_num)
theorem B1890867 : Blo 1889435 1890867 := bstep (se 1 (by rfl) ⟨1418150, by rfl⟩ : syracuseStep 1890867 = 2836301) B2836301
theorem B4254461 : Blo 1889435 4254461 := bbase (se 3 (by rfl) ⟨797711, by rfl⟩ : syracuseStep 4254461 = 1595423) (by norm_num)
theorem B2836307 : Blo 1889435 2836307 := bstep (se 1 (by rfl) ⟨2127230, by rfl⟩ : syracuseStep 2836307 = 4254461) B4254461
theorem B1890871 : Blo 1889435 1890871 := bstep (se 1 (by rfl) ⟨1418153, by rfl⟩ : syracuseStep 1890871 = 2836307) B2836307
theorem B3190853 : Blo 1889435 3190853 := bbase (se 4 (by rfl) ⟨299142, by rfl⟩ : syracuseStep 3190853 = 598285) (by norm_num)
theorem B2127235 : Blo 1889435 2127235 := bstep (se 1 (by rfl) ⟨1595426, by rfl⟩ : syracuseStep 2127235 = 3190853) B3190853
theorem B2836313 : Blo 1889435 2836313 := bstep (se 2 (by rfl) ⟨1063617, by rfl⟩ : syracuseStep 2836313 = 2127235) B2127235
theorem B1890875 : Blo 1889435 1890875 := bstep (se 1 (by rfl) ⟨1418156, by rfl⟩ : syracuseStep 1890875 = 2836313) B2836313
theorem B14358869 : Blo 1889435 14358869 := bbase (se 10 (by rfl) ⟨21033, by rfl⟩ : syracuseStep 14358869 = 42067) (by norm_num)
theorem B9572579 : Blo 1889435 9572579 := bstep (se 1 (by rfl) ⟨7179434, by rfl⟩ : syracuseStep 9572579 = 14358869) B14358869
theorem B6381719 : Blo 1889435 6381719 := bstep (se 1 (by rfl) ⟨4786289, by rfl⟩ : syracuseStep 6381719 = 9572579) B9572579
theorem B4254479 : Blo 1889435 4254479 := bstep (se 1 (by rfl) ⟨3190859, by rfl⟩ : syracuseStep 4254479 = 6381719) B6381719
theorem B2836319 : Blo 1889435 2836319 := bstep (se 1 (by rfl) ⟨2127239, by rfl⟩ : syracuseStep 2836319 = 4254479) B4254479
theorem B1890879 : Blo 1889435 1890879 := bstep (se 1 (by rfl) ⟨1418159, by rfl⟩ : syracuseStep 1890879 = 2836319) B2836319
theorem B2836325 : Blo 1889435 2836325 := bbase (se 4 (by rfl) ⟨265905, by rfl⟩ : syracuseStep 2836325 = 531811) (by norm_num)
theorem B1890883 : Blo 1889435 1890883 := bstep (se 1 (by rfl) ⟨1418162, by rfl⟩ : syracuseStep 1890883 = 2836325) B2836325
theorem B3589733 : Blo 1889435 3589733 := bbase (se 4 (by rfl) ⟨336537, by rfl⟩ : syracuseStep 3589733 = 673075) (by norm_num)
theorem B2393155 : Blo 1889435 2393155 := bstep (se 1 (by rfl) ⟨1794866, by rfl⟩ : syracuseStep 2393155 = 3589733) B3589733
theorem B3190873 : Blo 1889435 3190873 := bstep (se 2 (by rfl) ⟨1196577, by rfl⟩ : syracuseStep 3190873 = 2393155) B2393155
theorem B4254497 : Blo 1889435 4254497 := bstep (se 2 (by rfl) ⟨1595436, by rfl⟩ : syracuseStep 4254497 = 3190873) B3190873
theorem B2836331 : Blo 1889435 2836331 := bstep (se 1 (by rfl) ⟨2127248, by rfl⟩ : syracuseStep 2836331 = 4254497) B4254497
theorem B1890887 : Blo 1889435 1890887 := bstep (se 1 (by rfl) ⟨1418165, by rfl⟩ : syracuseStep 1890887 = 2836331) B2836331
theorem B2127253 : Blo 1889435 2127253 := bbase (se 6 (by rfl) ⟨49857, by rfl⟩ : syracuseStep 2127253 = 99715) (by norm_num)
theorem B2836337 : Blo 1889435 2836337 := bstep (se 2 (by rfl) ⟨1063626, by rfl⟩ : syracuseStep 2836337 = 2127253) B2127253
theorem B1890891 : Blo 1889435 1890891 := bstep (se 1 (by rfl) ⟨1418168, by rfl⟩ : syracuseStep 1890891 = 2836337) B2836337
theorem B2393165 : Blo 1889435 2393165 := bbase (se 3 (by rfl) ⟨448718, by rfl⟩ : syracuseStep 2393165 = 897437) (by norm_num)
theorem B6381773 : Blo 1889435 6381773 := bstep (se 3 (by rfl) ⟨1196582, by rfl⟩ : syracuseStep 6381773 = 2393165) B2393165
theorem B4254515 : Blo 1889435 4254515 := bstep (se 1 (by rfl) ⟨3190886, by rfl⟩ : syracuseStep 4254515 = 6381773) B6381773
theorem B2836343 : Blo 1889435 2836343 := bstep (se 1 (by rfl) ⟨2127257, by rfl⟩ : syracuseStep 2836343 = 4254515) B4254515
theorem B1890895 : Blo 1889435 1890895 := bstep (se 1 (by rfl) ⟨1418171, by rfl⟩ : syracuseStep 1890895 = 2836343) B2836343
theorem B2836349 : Blo 1889435 2836349 := bbase (se 3 (by rfl) ⟨531815, by rfl⟩ : syracuseStep 2836349 = 1063631) (by norm_num)
theorem B1890899 : Blo 1889435 1890899 := bstep (se 1 (by rfl) ⟨1418174, by rfl⟩ : syracuseStep 1890899 = 2836349) B2836349
theorem B4254533 : Blo 1889435 4254533 := bbase (se 4 (by rfl) ⟨398862, by rfl⟩ : syracuseStep 4254533 = 797725) (by norm_num)
theorem B2836355 : Blo 1889435 2836355 := bstep (se 1 (by rfl) ⟨2127266, by rfl⟩ : syracuseStep 2836355 = 4254533) B4254533
theorem B1890903 : Blo 1889435 1890903 := bstep (se 1 (by rfl) ⟨1418177, by rfl⟩ : syracuseStep 1890903 = 2836355) B2836355
theorem B4038493 : Blo 1889435 4038493 := bbase (se 3 (by rfl) ⟨757217, by rfl⟩ : syracuseStep 4038493 = 1514435) (by norm_num)
theorem B5384657 : Blo 1889435 5384657 := bstep (se 2 (by rfl) ⟨2019246, by rfl⟩ : syracuseStep 5384657 = 4038493) B4038493
theorem B3589771 : Blo 1889435 3589771 := bstep (se 1 (by rfl) ⟨2692328, by rfl⟩ : syracuseStep 3589771 = 5384657) B5384657
theorem B4786361 : Blo 1889435 4786361 := bstep (se 2 (by rfl) ⟨1794885, by rfl⟩ : syracuseStep 4786361 = 3589771) B3589771
theorem B3190907 : Blo 1889435 3190907 := bstep (se 1 (by rfl) ⟨2393180, by rfl⟩ : syracuseStep 3190907 = 4786361) B4786361
theorem B2127271 : Blo 1889435 2127271 := bstep (se 1 (by rfl) ⟨1595453, by rfl⟩ : syracuseStep 2127271 = 3190907) B3190907
theorem B2836361 : Blo 1889435 2836361 := bstep (se 2 (by rfl) ⟨1063635, by rfl⟩ : syracuseStep 2836361 = 2127271) B2127271
theorem B1890907 : Blo 1889435 1890907 := bstep (se 1 (by rfl) ⟨1418180, by rfl⟩ : syracuseStep 1890907 = 2836361) B2836361
theorem B9572741 : Blo 1889435 9572741 := bbase (se 4 (by rfl) ⟨897444, by rfl⟩ : syracuseStep 9572741 = 1794889) (by norm_num)
theorem B6381827 : Blo 1889435 6381827 := bstep (se 1 (by rfl) ⟨4786370, by rfl⟩ : syracuseStep 6381827 = 9572741) B9572741
theorem B4254551 : Blo 1889435 4254551 := bstep (se 1 (by rfl) ⟨3190913, by rfl⟩ : syracuseStep 4254551 = 6381827) B6381827
theorem B2836367 : Blo 1889435 2836367 := bstep (se 1 (by rfl) ⟨2127275, by rfl⟩ : syracuseStep 2836367 = 4254551) B4254551
theorem B1890911 : Blo 1889435 1890911 := bstep (se 1 (by rfl) ⟨1418183, by rfl⟩ : syracuseStep 1890911 = 2836367) B2836367
theorem B2836373 : Blo 1889435 2836373 := bbase (se 6 (by rfl) ⟨66477, by rfl⟩ : syracuseStep 2836373 = 132955) (by norm_num)
theorem B1890915 : Blo 1889435 1890915 := bstep (se 1 (by rfl) ⟨1418186, by rfl⟩ : syracuseStep 1890915 = 2836373) B2836373
theorem B3407501 : Blo 1889435 3407501 := bbase (se 3 (by rfl) ⟨638906, by rfl⟩ : syracuseStep 3407501 = 1277813) (by norm_num)
theorem B2271667 : Blo 1889435 2271667 := bstep (se 1 (by rfl) ⟨1703750, by rfl⟩ : syracuseStep 2271667 = 3407501) B3407501
theorem B3028889 : Blo 1889435 3028889 := bstep (se 2 (by rfl) ⟨1135833, by rfl⟩ : syracuseStep 3028889 = 2271667) B2271667
theorem B2019259 : Blo 1889435 2019259 := bstep (se 1 (by rfl) ⟨1514444, by rfl⟩ : syracuseStep 2019259 = 3028889) B3028889
theorem B10769381 : Blo 1889435 10769381 := bstep (se 4 (by rfl) ⟨1009629, by rfl⟩ : syracuseStep 10769381 = 2019259) B2019259
theorem B7179587 : Blo 1889435 7179587 := bstep (se 1 (by rfl) ⟨5384690, by rfl⟩ : syracuseStep 7179587 = 10769381) B10769381
theorem B4786391 : Blo 1889435 4786391 := bstep (se 1 (by rfl) ⟨3589793, by rfl⟩ : syracuseStep 4786391 = 7179587) B7179587
theorem B3190927 : Blo 1889435 3190927 := bstep (se 1 (by rfl) ⟨2393195, by rfl⟩ : syracuseStep 3190927 = 4786391) B4786391
theorem B4254569 : Blo 1889435 4254569 := bstep (se 2 (by rfl) ⟨1595463, by rfl⟩ : syracuseStep 4254569 = 3190927) B3190927
theorem B2836379 : Blo 1889435 2836379 := bstep (se 1 (by rfl) ⟨2127284, by rfl⟩ : syracuseStep 2836379 = 4254569) B4254569
theorem B1890919 : Blo 1889435 1890919 := bstep (se 1 (by rfl) ⟨1418189, by rfl⟩ : syracuseStep 1890919 = 2836379) B2836379
theorem B2127289 : Blo 1889435 2127289 := bbase (se 2 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 2127289 = 1595467) (by norm_num)
theorem B2836385 : Blo 1889435 2836385 := bstep (se 2 (by rfl) ⟨1063644, by rfl⟩ : syracuseStep 2836385 = 2127289) B2127289
theorem B1890923 : Blo 1889435 1890923 := bstep (se 1 (by rfl) ⟨1418192, by rfl⟩ : syracuseStep 1890923 = 2836385) B2836385
theorem B6815029 : Blo 1889435 6815029 := bbase (se 5 (by rfl) ⟨319454, by rfl⟩ : syracuseStep 6815029 = 638909) (by norm_num)
theorem B9086705 : Blo 1889435 9086705 := bstep (se 2 (by rfl) ⟨3407514, by rfl⟩ : syracuseStep 9086705 = 6815029) B6815029
theorem B6057803 : Blo 1889435 6057803 := bstep (se 1 (by rfl) ⟨4543352, by rfl⟩ : syracuseStep 6057803 = 9086705) B9086705
theorem B4038535 : Blo 1889435 4038535 := bstep (se 1 (by rfl) ⟨3028901, by rfl⟩ : syracuseStep 4038535 = 6057803) B6057803
theorem B5384713 : Blo 1889435 5384713 := bstep (se 2 (by rfl) ⟨2019267, by rfl⟩ : syracuseStep 5384713 = 4038535) B4038535
theorem B7179617 : Blo 1889435 7179617 := bstep (se 2 (by rfl) ⟨2692356, by rfl⟩ : syracuseStep 7179617 = 5384713) B5384713
theorem B4786411 : Blo 1889435 4786411 := bstep (se 1 (by rfl) ⟨3589808, by rfl⟩ : syracuseStep 4786411 = 7179617) B7179617
theorem B6381881 : Blo 1889435 6381881 := bstep (se 2 (by rfl) ⟨2393205, by rfl⟩ : syracuseStep 6381881 = 4786411) B4786411
theorem B4254587 : Blo 1889435 4254587 := bstep (se 1 (by rfl) ⟨3190940, by rfl⟩ : syracuseStep 4254587 = 6381881) B6381881
theorem B2836391 : Blo 1889435 2836391 := bstep (se 1 (by rfl) ⟨2127293, by rfl⟩ : syracuseStep 2836391 = 4254587) B4254587
theorem B1890927 : Blo 1889435 1890927 := bstep (se 1 (by rfl) ⟨1418195, by rfl⟩ : syracuseStep 1890927 = 2836391) B2836391
theorem B2836397 : Blo 1889435 2836397 := bbase (se 3 (by rfl) ⟨531824, by rfl⟩ : syracuseStep 2836397 = 1063649) (by norm_num)
theorem B1890931 : Blo 1889435 1890931 := bstep (se 1 (by rfl) ⟨1418198, by rfl⟩ : syracuseStep 1890931 = 2836397) B2836397
theorem B4254605 : Blo 1889435 4254605 := bbase (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) (by norm_num)
theorem B2836403 : Blo 1889435 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1890935 : Blo 1889435 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B2393221 : Blo 1889435 2393221 := bbase (se 4 (by rfl) ⟨224364, by rfl⟩ : syracuseStep 2393221 = 448729) (by norm_num)
theorem B3190961 : Blo 1889435 3190961 := bstep (se 2 (by rfl) ⟨1196610, by rfl⟩ : syracuseStep 3190961 = 2393221) B2393221
theorem B2127307 : Blo 1889435 2127307 := bstep (se 1 (by rfl) ⟨1595480, by rfl⟩ : syracuseStep 2127307 = 3190961) B3190961
theorem B2836409 : Blo 1889435 2836409 := bstep (se 2 (by rfl) ⟨1063653, by rfl⟩ : syracuseStep 2836409 = 2127307) B2127307
theorem B1890939 : Blo 1889435 1890939 := bstep (se 1 (by rfl) ⟨1418204, by rfl⟩ : syracuseStep 1890939 = 2836409) B2836409
theorem B5458229 : Blo 1889435 5458229 := bbase (se 5 (by rfl) ⟨255854, by rfl⟩ : syracuseStep 5458229 = 511709) (by norm_num)
theorem B3638819 : Blo 1889435 3638819 := bstep (se 1 (by rfl) ⟨2729114, by rfl⟩ : syracuseStep 3638819 = 5458229) B5458229
theorem B2425879 : Blo 1889435 2425879 := bstep (se 1 (by rfl) ⟨1819409, by rfl⟩ : syracuseStep 2425879 = 3638819) B3638819
theorem B3234505 : Blo 1889435 3234505 := bstep (se 2 (by rfl) ⟨1212939, by rfl⟩ : syracuseStep 3234505 = 2425879) B2425879
theorem B4312673 : Blo 1889435 4312673 := bstep (se 2 (by rfl) ⟨1617252, by rfl⟩ : syracuseStep 4312673 = 3234505) B3234505
theorem B2875115 : Blo 1889435 2875115 := bstep (se 1 (by rfl) ⟨2156336, by rfl⟩ : syracuseStep 2875115 = 4312673) B4312673
theorem B7666973 : Blo 1889435 7666973 := bstep (se 3 (by rfl) ⟨1437557, by rfl⟩ : syracuseStep 7666973 = 2875115) B2875115
theorem B5111315 : Blo 1889435 5111315 := bstep (se 1 (by rfl) ⟨3833486, by rfl⟩ : syracuseStep 5111315 = 7666973) B7666973
theorem B3407543 : Blo 1889435 3407543 := bstep (se 1 (by rfl) ⟨2555657, by rfl⟩ : syracuseStep 3407543 = 5111315) B5111315
theorem B2271695 : Blo 1889435 2271695 := bstep (se 1 (by rfl) ⟨1703771, by rfl⟩ : syracuseStep 2271695 = 3407543) B3407543
theorem B24231413 : Blo 1889435 24231413 := bstep (se 5 (by rfl) ⟨1135847, by rfl⟩ : syracuseStep 24231413 = 2271695) B2271695
theorem B16154275 : Blo 1889435 16154275 := bstep (se 1 (by rfl) ⟨12115706, by rfl⟩ : syracuseStep 16154275 = 24231413) B24231413
theorem B21539033 : Blo 1889435 21539033 := bstep (se 2 (by rfl) ⟨8077137, by rfl⟩ : syracuseStep 21539033 = 16154275) B16154275
theorem B14359355 : Blo 1889435 14359355 := bstep (se 1 (by rfl) ⟨10769516, by rfl⟩ : syracuseStep 14359355 = 21539033) B21539033
theorem B9572903 : Blo 1889435 9572903 := bstep (se 1 (by rfl) ⟨7179677, by rfl⟩ : syracuseStep 9572903 = 14359355) B14359355
theorem B6381935 : Blo 1889435 6381935 := bstep (se 1 (by rfl) ⟨4786451, by rfl⟩ : syracuseStep 6381935 = 9572903) B9572903
theorem B4254623 : Blo 1889435 4254623 := bstep (se 1 (by rfl) ⟨3190967, by rfl⟩ : syracuseStep 4254623 = 6381935) B6381935
theorem B2836415 : Blo 1889435 2836415 := bstep (se 1 (by rfl) ⟨2127311, by rfl⟩ : syracuseStep 2836415 = 4254623) B4254623
theorem B1890943 : Blo 1889435 1890943 := bstep (se 1 (by rfl) ⟨1418207, by rfl⟩ : syracuseStep 1890943 = 2836415) B2836415
theorem B2836421 : Blo 1889435 2836421 := bbase (se 4 (by rfl) ⟨265914, by rfl⟩ : syracuseStep 2836421 = 531829) (by norm_num)
theorem B1890947 : Blo 1889435 1890947 := bstep (se 1 (by rfl) ⟨1418210, by rfl⟩ : syracuseStep 1890947 = 2836421) B2836421
theorem B3190981 : Blo 1889435 3190981 := bbase (se 4 (by rfl) ⟨299154, by rfl⟩ : syracuseStep 3190981 = 598309) (by norm_num)
theorem B4254641 : Blo 1889435 4254641 := bstep (se 2 (by rfl) ⟨1595490, by rfl⟩ : syracuseStep 4254641 = 3190981) B3190981
theorem B2836427 : Blo 1889435 2836427 := bstep (se 1 (by rfl) ⟨2127320, by rfl⟩ : syracuseStep 2836427 = 4254641) B4254641
theorem B1890951 : Blo 1889435 1890951 := bstep (se 1 (by rfl) ⟨1418213, by rfl⟩ : syracuseStep 1890951 = 2836427) B2836427
theorem B2127325 : Blo 1889435 2127325 := bbase (se 3 (by rfl) ⟨398873, by rfl⟩ : syracuseStep 2127325 = 797747) (by norm_num)
theorem B2836433 : Blo 1889435 2836433 := bstep (se 2 (by rfl) ⟨1063662, by rfl⟩ : syracuseStep 2836433 = 2127325) B2127325
theorem B1890955 : Blo 1889435 1890955 := bstep (se 1 (by rfl) ⟨1418216, by rfl⟩ : syracuseStep 1890955 = 2836433) B2836433
theorem B6381989 : Blo 1889435 6381989 := bbase (se 4 (by rfl) ⟨598311, by rfl⟩ : syracuseStep 6381989 = 1196623) (by norm_num)
theorem B4254659 : Blo 1889435 4254659 := bstep (se 1 (by rfl) ⟨3190994, by rfl⟩ : syracuseStep 4254659 = 6381989) B6381989
theorem B2836439 : Blo 1889435 2836439 := bstep (se 1 (by rfl) ⟨2127329, by rfl⟩ : syracuseStep 2836439 = 4254659) B4254659
theorem B1890959 : Blo 1889435 1890959 := bstep (se 1 (by rfl) ⟨1418219, by rfl⟩ : syracuseStep 1890959 = 2836439) B2836439
theorem B2836445 : Blo 1889435 2836445 := bbase (se 3 (by rfl) ⟨531833, by rfl⟩ : syracuseStep 2836445 = 1063667) (by norm_num)
theorem B1890963 : Blo 1889435 1890963 := bstep (se 1 (by rfl) ⟨1418222, by rfl⟩ : syracuseStep 1890963 = 2836445) B2836445
theorem B4254677 : Blo 1889435 4254677 := bbase (se 7 (by rfl) ⟨49859, by rfl⟩ : syracuseStep 4254677 = 99719) (by norm_num)
theorem B2836451 : Blo 1889435 2836451 := bstep (se 1 (by rfl) ⟨2127338, by rfl⟩ : syracuseStep 2836451 = 4254677) B4254677
theorem B1890967 : Blo 1889435 1890967 := bstep (se 1 (by rfl) ⟨1418225, by rfl⟩ : syracuseStep 1890967 = 2836451) B2836451
theorem B9086917 : Blo 1889435 9086917 := bbase (se 4 (by rfl) ⟨851898, by rfl⟩ : syracuseStep 9086917 = 1703797) (by norm_num)
theorem B12115889 : Blo 1889435 12115889 := bstep (se 2 (by rfl) ⟨4543458, by rfl⟩ : syracuseStep 12115889 = 9086917) B9086917
theorem B8077259 : Blo 1889435 8077259 := bstep (se 1 (by rfl) ⟨6057944, by rfl⟩ : syracuseStep 8077259 = 12115889) B12115889
theorem B5384839 : Blo 1889435 5384839 := bstep (se 1 (by rfl) ⟨4038629, by rfl⟩ : syracuseStep 5384839 = 8077259) B8077259
theorem B7179785 : Blo 1889435 7179785 := bstep (se 2 (by rfl) ⟨2692419, by rfl⟩ : syracuseStep 7179785 = 5384839) B5384839
theorem B4786523 : Blo 1889435 4786523 := bstep (se 1 (by rfl) ⟨3589892, by rfl⟩ : syracuseStep 4786523 = 7179785) B7179785
theorem B3191015 : Blo 1889435 3191015 := bstep (se 1 (by rfl) ⟨2393261, by rfl⟩ : syracuseStep 3191015 = 4786523) B4786523
theorem B2127343 : Blo 1889435 2127343 := bstep (se 1 (by rfl) ⟨1595507, by rfl⟩ : syracuseStep 2127343 = 3191015) B3191015
theorem B2836457 : Blo 1889435 2836457 := bstep (se 2 (by rfl) ⟨1063671, by rfl⟩ : syracuseStep 2836457 = 2127343) B2127343
theorem B1890971 : Blo 1889435 1890971 := bstep (se 1 (by rfl) ⟨1418228, by rfl⟩ : syracuseStep 1890971 = 2836457) B2836457
theorem B16154549 : Blo 1889435 16154549 := bbase (se 5 (by rfl) ⟨757244, by rfl⟩ : syracuseStep 16154549 = 1514489) (by norm_num)
theorem B10769699 : Blo 1889435 10769699 := bstep (se 1 (by rfl) ⟨8077274, by rfl⟩ : syracuseStep 10769699 = 16154549) B16154549
theorem B7179799 : Blo 1889435 7179799 := bstep (se 1 (by rfl) ⟨5384849, by rfl⟩ : syracuseStep 7179799 = 10769699) B10769699
theorem B9573065 : Blo 1889435 9573065 := bstep (se 2 (by rfl) ⟨3589899, by rfl⟩ : syracuseStep 9573065 = 7179799) B7179799
theorem B6382043 : Blo 1889435 6382043 := bstep (se 1 (by rfl) ⟨4786532, by rfl⟩ : syracuseStep 6382043 = 9573065) B9573065
theorem B4254695 : Blo 1889435 4254695 := bstep (se 1 (by rfl) ⟨3191021, by rfl⟩ : syracuseStep 4254695 = 6382043) B6382043
theorem B2836463 : Blo 1889435 2836463 := bstep (se 1 (by rfl) ⟨2127347, by rfl⟩ : syracuseStep 2836463 = 4254695) B4254695
theorem B1890975 : Blo 1889435 1890975 := bstep (se 1 (by rfl) ⟨1418231, by rfl⟩ : syracuseStep 1890975 = 2836463) B2836463
theorem B2836469 : Blo 1889435 2836469 := bbase (se 5 (by rfl) ⟨132959, by rfl⟩ : syracuseStep 2836469 = 265919) (by norm_num)
theorem B1890979 : Blo 1889435 1890979 := bstep (se 1 (by rfl) ⟨1418234, by rfl⟩ : syracuseStep 1890979 = 2836469) B2836469
theorem B26950229 : Blo 1889435 26950229 := bbase (se 8 (by rfl) ⟨157911, by rfl⟩ : syracuseStep 26950229 = 315823) (by norm_num)
theorem B17966819 : Blo 1889435 17966819 := bstep (se 1 (by rfl) ⟨13475114, by rfl⟩ : syracuseStep 17966819 = 26950229) B26950229
theorem B11977879 : Blo 1889435 11977879 := bstep (se 1 (by rfl) ⟨8983409, by rfl⟩ : syracuseStep 11977879 = 17966819) B17966819
theorem B15970505 : Blo 1889435 15970505 := bstep (se 2 (by rfl) ⟨5988939, by rfl⟩ : syracuseStep 15970505 = 11977879) B11977879
theorem B42588013 : Blo 1889435 42588013 := bstep (se 3 (by rfl) ⟨7985252, by rfl⟩ : syracuseStep 42588013 = 15970505) B15970505
theorem B56784017 : Blo 1889435 56784017 := bstep (se 2 (by rfl) ⟨21294006, by rfl⟩ : syracuseStep 56784017 = 42588013) B42588013
theorem B37856011 : Blo 1889435 37856011 := bstep (se 1 (by rfl) ⟨28392008, by rfl⟩ : syracuseStep 37856011 = 56784017) B56784017
theorem B50474681 : Blo 1889435 50474681 := bstep (se 2 (by rfl) ⟨18928005, by rfl⟩ : syracuseStep 50474681 = 37856011) B37856011
theorem B33649787 : Blo 1889435 33649787 := bstep (se 1 (by rfl) ⟨25237340, by rfl⟩ : syracuseStep 33649787 = 50474681) B50474681
theorem B89732765 : Blo 1889435 89732765 := bstep (se 3 (by rfl) ⟨16824893, by rfl⟩ : syracuseStep 89732765 = 33649787) B33649787
theorem B59821843 : Blo 1889435 59821843 := bstep (se 1 (by rfl) ⟨44866382, by rfl⟩ : syracuseStep 59821843 = 89732765) B89732765
theorem B79762457 : Blo 1889435 79762457 := bstep (se 2 (by rfl) ⟨29910921, by rfl⟩ : syracuseStep 79762457 = 59821843) B59821843
theorem B53174971 : Blo 1889435 53174971 := bstep (se 1 (by rfl) ⟨39881228, by rfl⟩ : syracuseStep 53174971 = 79762457) B79762457
theorem B70899961 : Blo 1889435 70899961 := bstep (se 2 (by rfl) ⟨26587485, by rfl⟩ : syracuseStep 70899961 = 53174971) B53174971
theorem B94533281 : Blo 1889435 94533281 := bstep (se 2 (by rfl) ⟨35449980, by rfl⟩ : syracuseStep 94533281 = 70899961) B70899961
theorem B63022187 : Blo 1889435 63022187 := bstep (se 1 (by rfl) ⟨47266640, by rfl⟩ : syracuseStep 63022187 = 94533281) B94533281
theorem B42014791 : Blo 1889435 42014791 := bstep (se 1 (by rfl) ⟨31511093, by rfl⟩ : syracuseStep 42014791 = 63022187) B63022187
theorem B56019721 : Blo 1889435 56019721 := bstep (se 2 (by rfl) ⟨21007395, by rfl⟩ : syracuseStep 56019721 = 42014791) B42014791
theorem B74692961 : Blo 1889435 74692961 := bstep (se 2 (by rfl) ⟨28009860, by rfl⟩ : syracuseStep 74692961 = 56019721) B56019721
theorem B49795307 : Blo 1889435 49795307 := bstep (se 1 (by rfl) ⟨37346480, by rfl⟩ : syracuseStep 49795307 = 74692961) B74692961
theorem B33196871 : Blo 1889435 33196871 := bstep (se 1 (by rfl) ⟨24897653, by rfl⟩ : syracuseStep 33196871 = 49795307) B49795307
theorem B22131247 : Blo 1889435 22131247 := bstep (se 1 (by rfl) ⟨16598435, by rfl⟩ : syracuseStep 22131247 = 33196871) B33196871
theorem B29508329 : Blo 1889435 29508329 := bstep (se 2 (by rfl) ⟨11065623, by rfl⟩ : syracuseStep 29508329 = 22131247) B22131247
theorem B19672219 : Blo 1889435 19672219 := bstep (se 1 (by rfl) ⟨14754164, by rfl⟩ : syracuseStep 19672219 = 29508329) B29508329
theorem B104918501 : Blo 1889435 104918501 := bstep (se 4 (by rfl) ⟨9836109, by rfl⟩ : syracuseStep 104918501 = 19672219) B19672219
theorem B279782669 : Blo 1889435 279782669 := bstep (se 3 (by rfl) ⟨52459250, by rfl⟩ : syracuseStep 279782669 = 104918501) B104918501
theorem B186521779 : Blo 1889435 186521779 := bstep (se 1 (by rfl) ⟨139891334, by rfl⟩ : syracuseStep 186521779 = 279782669) B279782669
theorem B248695705 : Blo 1889435 248695705 := bstep (se 2 (by rfl) ⟨93260889, by rfl⟩ : syracuseStep 248695705 = 186521779) B186521779
theorem B331594273 : Blo 1889435 331594273 := bstep (se 2 (by rfl) ⟨124347852, by rfl⟩ : syracuseStep 331594273 = 248695705) B248695705
theorem B442125697 : Blo 1889435 442125697 := bstep (se 2 (by rfl) ⟨165797136, by rfl⟩ : syracuseStep 442125697 = 331594273) B331594273
theorem B589500929 : Blo 1889435 589500929 := bstep (se 2 (by rfl) ⟨221062848, by rfl⟩ : syracuseStep 589500929 = 442125697) B442125697
theorem B393000619 : Blo 1889435 393000619 := bstep (se 1 (by rfl) ⟨294750464, by rfl⟩ : syracuseStep 393000619 = 589500929) B589500929
theorem B524000825 : Blo 1889435 524000825 := bstep (se 2 (by rfl) ⟨196500309, by rfl⟩ : syracuseStep 524000825 = 393000619) B393000619
theorem B349333883 : Blo 1889435 349333883 := bstep (se 1 (by rfl) ⟨262000412, by rfl⟩ : syracuseStep 349333883 = 524000825) B524000825
theorem B232889255 : Blo 1889435 232889255 := bstep (se 1 (by rfl) ⟨174666941, by rfl⟩ : syracuseStep 232889255 = 349333883) B349333883
theorem B155259503 : Blo 1889435 155259503 := bstep (se 1 (by rfl) ⟨116444627, by rfl⟩ : syracuseStep 155259503 = 232889255) B232889255
theorem B103506335 : Blo 1889435 103506335 := bstep (se 1 (by rfl) ⟨77629751, by rfl⟩ : syracuseStep 103506335 = 155259503) B155259503
theorem B69004223 : Blo 1889435 69004223 := bstep (se 1 (by rfl) ⟨51753167, by rfl⟩ : syracuseStep 69004223 = 103506335) B103506335
theorem B46002815 : Blo 1889435 46002815 := bstep (se 1 (by rfl) ⟨34502111, by rfl⟩ : syracuseStep 46002815 = 69004223) B69004223
theorem B30668543 : Blo 1889435 30668543 := bstep (se 1 (by rfl) ⟨23001407, by rfl⟩ : syracuseStep 30668543 = 46002815) B46002815
theorem B20445695 : Blo 1889435 20445695 := bstep (se 1 (by rfl) ⟨15334271, by rfl⟩ : syracuseStep 20445695 = 30668543) B30668543
theorem B13630463 : Blo 1889435 13630463 := bstep (se 1 (by rfl) ⟨10222847, by rfl⟩ : syracuseStep 13630463 = 20445695) B20445695
theorem B9086975 : Blo 1889435 9086975 := bstep (se 1 (by rfl) ⟨6815231, by rfl⟩ : syracuseStep 9086975 = 13630463) B13630463
theorem B6057983 : Blo 1889435 6057983 := bstep (se 1 (by rfl) ⟨4543487, by rfl⟩ : syracuseStep 6057983 = 9086975) B9086975
theorem B4038655 : Blo 1889435 4038655 := bstep (se 1 (by rfl) ⟨3028991, by rfl⟩ : syracuseStep 4038655 = 6057983) B6057983
theorem B5384873 : Blo 1889435 5384873 := bstep (se 2 (by rfl) ⟨2019327, by rfl⟩ : syracuseStep 5384873 = 4038655) B4038655
theorem B3589915 : Blo 1889435 3589915 := bstep (se 1 (by rfl) ⟨2692436, by rfl⟩ : syracuseStep 3589915 = 5384873) B5384873
theorem B4786553 : Blo 1889435 4786553 := bstep (se 2 (by rfl) ⟨1794957, by rfl⟩ : syracuseStep 4786553 = 3589915) B3589915
theorem B3191035 : Blo 1889435 3191035 := bstep (se 1 (by rfl) ⟨2393276, by rfl⟩ : syracuseStep 3191035 = 4786553) B4786553
theorem B4254713 : Blo 1889435 4254713 := bstep (se 2 (by rfl) ⟨1595517, by rfl⟩ : syracuseStep 4254713 = 3191035) B3191035
theorem B2836475 : Blo 1889435 2836475 := bstep (se 1 (by rfl) ⟨2127356, by rfl⟩ : syracuseStep 2836475 = 4254713) B4254713
theorem B1890983 : Blo 1889435 1890983 := bstep (se 1 (by rfl) ⟨1418237, by rfl⟩ : syracuseStep 1890983 = 2836475) B2836475
theorem B2127361 : Blo 1889435 2127361 := bbase (se 2 (by rfl) ⟨797760, by rfl⟩ : syracuseStep 2127361 = 1595521) (by norm_num)
theorem B2836481 : Blo 1889435 2836481 := bstep (se 2 (by rfl) ⟨1063680, by rfl⟩ : syracuseStep 2836481 = 2127361) B2127361
theorem B1890987 : Blo 1889435 1890987 := bstep (se 1 (by rfl) ⟨1418240, by rfl⟩ : syracuseStep 1890987 = 2836481) B2836481
theorem B4786573 : Blo 1889435 4786573 := bbase (se 3 (by rfl) ⟨897482, by rfl⟩ : syracuseStep 4786573 = 1794965) (by norm_num)
theorem B6382097 : Blo 1889435 6382097 := bstep (se 2 (by rfl) ⟨2393286, by rfl⟩ : syracuseStep 6382097 = 4786573) B4786573
theorem B4254731 : Blo 1889435 4254731 := bstep (se 1 (by rfl) ⟨3191048, by rfl⟩ : syracuseStep 4254731 = 6382097) B6382097
theorem B2836487 : Blo 1889435 2836487 := bstep (se 1 (by rfl) ⟨2127365, by rfl⟩ : syracuseStep 2836487 = 4254731) B4254731
theorem B1890991 : Blo 1889435 1890991 := bstep (se 1 (by rfl) ⟨1418243, by rfl⟩ : syracuseStep 1890991 = 2836487) B2836487
theorem B2836493 : Blo 1889435 2836493 := bbase (se 3 (by rfl) ⟨531842, by rfl⟩ : syracuseStep 2836493 = 1063685) (by norm_num)
theorem B1890995 : Blo 1889435 1890995 := bstep (se 1 (by rfl) ⟨1418246, by rfl⟩ : syracuseStep 1890995 = 2836493) B2836493
theorem B4254749 : Blo 1889435 4254749 := bbase (se 3 (by rfl) ⟨797765, by rfl⟩ : syracuseStep 4254749 = 1595531) (by norm_num)
theorem B2836499 : Blo 1889435 2836499 := bstep (se 1 (by rfl) ⟨2127374, by rfl⟩ : syracuseStep 2836499 = 4254749) B4254749
theorem B1890999 : Blo 1889435 1890999 := bstep (se 1 (by rfl) ⟨1418249, by rfl⟩ : syracuseStep 1890999 = 2836499) B2836499
theorem B3191069 : Blo 1889435 3191069 := bbase (se 3 (by rfl) ⟨598325, by rfl⟩ : syracuseStep 3191069 = 1196651) (by norm_num)
theorem B2127379 : Blo 1889435 2127379 := bstep (se 1 (by rfl) ⟨1595534, by rfl⟩ : syracuseStep 2127379 = 3191069) B3191069
theorem B2836505 : Blo 1889435 2836505 := bstep (se 2 (by rfl) ⟨1063689, by rfl⟩ : syracuseStep 2836505 = 2127379) B2127379
theorem B1891003 : Blo 1889435 1891003 := bstep (se 1 (by rfl) ⟨1418252, by rfl⟩ : syracuseStep 1891003 = 2836505) B2836505
theorem B12116117 : Blo 1889435 12116117 := bbase (se 6 (by rfl) ⟨283971, by rfl⟩ : syracuseStep 12116117 = 567943) (by norm_num)
theorem B8077411 : Blo 1889435 8077411 := bstep (se 1 (by rfl) ⟨6058058, by rfl⟩ : syracuseStep 8077411 = 12116117) B12116117
theorem B10769881 : Blo 1889435 10769881 := bstep (se 2 (by rfl) ⟨4038705, by rfl⟩ : syracuseStep 10769881 = 8077411) B8077411
theorem B14359841 : Blo 1889435 14359841 := bstep (se 2 (by rfl) ⟨5384940, by rfl⟩ : syracuseStep 14359841 = 10769881) B10769881
theorem B9573227 : Blo 1889435 9573227 := bstep (se 1 (by rfl) ⟨7179920, by rfl⟩ : syracuseStep 9573227 = 14359841) B14359841
theorem B6382151 : Blo 1889435 6382151 := bstep (se 1 (by rfl) ⟨4786613, by rfl⟩ : syracuseStep 6382151 = 9573227) B9573227
theorem B4254767 : Blo 1889435 4254767 := bstep (se 1 (by rfl) ⟨3191075, by rfl⟩ : syracuseStep 4254767 = 6382151) B6382151
theorem B2836511 : Blo 1889435 2836511 := bstep (se 1 (by rfl) ⟨2127383, by rfl⟩ : syracuseStep 2836511 = 4254767) B4254767
theorem B1891007 : Blo 1889435 1891007 := bstep (se 1 (by rfl) ⟨1418255, by rfl⟩ : syracuseStep 1891007 = 2836511) B2836511
theorem B2836517 : Blo 1889435 2836517 := bbase (se 4 (by rfl) ⟨265923, by rfl⟩ : syracuseStep 2836517 = 531847) (by norm_num)
theorem B1891011 : Blo 1889435 1891011 := bstep (se 1 (by rfl) ⟨1418258, by rfl⟩ : syracuseStep 1891011 = 2836517) B2836517
theorem B2393317 : Blo 1889435 2393317 := bbase (se 4 (by rfl) ⟨224373, by rfl⟩ : syracuseStep 2393317 = 448747) (by norm_num)
theorem B3191089 : Blo 1889435 3191089 := bstep (se 2 (by rfl) ⟨1196658, by rfl⟩ : syracuseStep 3191089 = 2393317) B2393317
theorem B4254785 : Blo 1889435 4254785 := bstep (se 2 (by rfl) ⟨1595544, by rfl⟩ : syracuseStep 4254785 = 3191089) B3191089
theorem B2836523 : Blo 1889435 2836523 := bstep (se 1 (by rfl) ⟨2127392, by rfl⟩ : syracuseStep 2836523 = 4254785) B4254785
theorem B1891015 : Blo 1889435 1891015 := bstep (se 1 (by rfl) ⟨1418261, by rfl⟩ : syracuseStep 1891015 = 2836523) B2836523
theorem B2127397 : Blo 1889435 2127397 := bbase (se 4 (by rfl) ⟨199443, by rfl⟩ : syracuseStep 2127397 = 398887) (by norm_num)
theorem B2836529 : Blo 1889435 2836529 := bstep (se 2 (by rfl) ⟨1063698, by rfl⟩ : syracuseStep 2836529 = 2127397) B2127397
theorem B1891019 : Blo 1889435 1891019 := bstep (se 1 (by rfl) ⟨1418264, by rfl⟩ : syracuseStep 1891019 = 2836529) B2836529
theorem B2425981 : Blo 1889435 2425981 := bbase (se 3 (by rfl) ⟨454871, by rfl⟩ : syracuseStep 2425981 = 909743) (by norm_num)
theorem B51754261 : Blo 1889435 51754261 := bstep (se 6 (by rfl) ⟨1212990, by rfl⟩ : syracuseStep 51754261 = 2425981) B2425981
theorem B69005681 : Blo 1889435 69005681 := bstep (se 2 (by rfl) ⟨25877130, by rfl⟩ : syracuseStep 69005681 = 51754261) B51754261
theorem B46003787 : Blo 1889435 46003787 := bstep (se 1 (by rfl) ⟨34502840, by rfl⟩ : syracuseStep 46003787 = 69005681) B69005681
theorem B30669191 : Blo 1889435 30669191 := bstep (se 1 (by rfl) ⟨23001893, by rfl⟩ : syracuseStep 30669191 = 46003787) B46003787
theorem B20446127 : Blo 1889435 20446127 := bstep (se 1 (by rfl) ⟨15334595, by rfl⟩ : syracuseStep 20446127 = 30669191) B30669191
theorem B13630751 : Blo 1889435 13630751 := bstep (se 1 (by rfl) ⟨10223063, by rfl⟩ : syracuseStep 13630751 = 20446127) B20446127
theorem B9087167 : Blo 1889435 9087167 := bstep (se 1 (by rfl) ⟨6815375, by rfl⟩ : syracuseStep 9087167 = 13630751) B13630751
theorem B6058111 : Blo 1889435 6058111 := bstep (se 1 (by rfl) ⟨4543583, by rfl⟩ : syracuseStep 6058111 = 9087167) B9087167
theorem B8077481 : Blo 1889435 8077481 := bstep (se 2 (by rfl) ⟨3029055, by rfl⟩ : syracuseStep 8077481 = 6058111) B6058111
theorem B5384987 : Blo 1889435 5384987 := bstep (se 1 (by rfl) ⟨4038740, by rfl⟩ : syracuseStep 5384987 = 8077481) B8077481
theorem B3589991 : Blo 1889435 3589991 := bstep (se 1 (by rfl) ⟨2692493, by rfl⟩ : syracuseStep 3589991 = 5384987) B5384987
theorem B2393327 : Blo 1889435 2393327 := bstep (se 1 (by rfl) ⟨1794995, by rfl⟩ : syracuseStep 2393327 = 3589991) B3589991
theorem B6382205 : Blo 1889435 6382205 := bstep (se 3 (by rfl) ⟨1196663, by rfl⟩ : syracuseStep 6382205 = 2393327) B2393327
theorem B4254803 : Blo 1889435 4254803 := bstep (se 1 (by rfl) ⟨3191102, by rfl⟩ : syracuseStep 4254803 = 6382205) B6382205
theorem B2836535 : Blo 1889435 2836535 := bstep (se 1 (by rfl) ⟨2127401, by rfl⟩ : syracuseStep 2836535 = 4254803) B4254803
theorem B1891023 : Blo 1889435 1891023 := bstep (se 1 (by rfl) ⟨1418267, by rfl⟩ : syracuseStep 1891023 = 2836535) B2836535
theorem B2836541 : Blo 1889435 2836541 := bbase (se 3 (by rfl) ⟨531851, by rfl⟩ : syracuseStep 2836541 = 1063703) (by norm_num)
theorem B1891027 : Blo 1889435 1891027 := bstep (se 1 (by rfl) ⟨1418270, by rfl⟩ : syracuseStep 1891027 = 2836541) B2836541
theorem B4254821 : Blo 1889435 4254821 := bbase (se 4 (by rfl) ⟨398889, by rfl⟩ : syracuseStep 4254821 = 797779) (by norm_num)
theorem B2836547 : Blo 1889435 2836547 := bstep (se 1 (by rfl) ⟨2127410, by rfl⟩ : syracuseStep 2836547 = 4254821) B4254821
theorem B1891031 : Blo 1889435 1891031 := bstep (se 1 (by rfl) ⟨1418273, by rfl⟩ : syracuseStep 1891031 = 2836547) B2836547
theorem B4786685 : Blo 1889435 4786685 := bbase (se 3 (by rfl) ⟨897503, by rfl⟩ : syracuseStep 4786685 = 1795007) (by norm_num)
theorem B3191123 : Blo 1889435 3191123 := bstep (se 1 (by rfl) ⟨2393342, by rfl⟩ : syracuseStep 3191123 = 4786685) B4786685
theorem B2127415 : Blo 1889435 2127415 := bstep (se 1 (by rfl) ⟨1595561, by rfl⟩ : syracuseStep 2127415 = 3191123) B3191123
theorem B2836553 : Blo 1889435 2836553 := bstep (se 2 (by rfl) ⟨1063707, by rfl⟩ : syracuseStep 2836553 = 2127415) B2127415
theorem B1891035 : Blo 1889435 1891035 := bstep (se 1 (by rfl) ⟨1418276, by rfl⟩ : syracuseStep 1891035 = 2836553) B2836553
theorem B3590021 : Blo 1889435 3590021 := bbase (se 4 (by rfl) ⟨336564, by rfl⟩ : syracuseStep 3590021 = 673129) (by norm_num)
theorem B9573389 : Blo 1889435 9573389 := bstep (se 3 (by rfl) ⟨1795010, by rfl⟩ : syracuseStep 9573389 = 3590021) B3590021
theorem B6382259 : Blo 1889435 6382259 := bstep (se 1 (by rfl) ⟨4786694, by rfl⟩ : syracuseStep 6382259 = 9573389) B9573389
theorem B4254839 : Blo 1889435 4254839 := bstep (se 1 (by rfl) ⟨3191129, by rfl⟩ : syracuseStep 4254839 = 6382259) B6382259
theorem B2836559 : Blo 1889435 2836559 := bstep (se 1 (by rfl) ⟨2127419, by rfl⟩ : syracuseStep 2836559 = 4254839) B4254839
theorem B1891039 : Blo 1889435 1891039 := bstep (se 1 (by rfl) ⟨1418279, by rfl⟩ : syracuseStep 1891039 = 2836559) B2836559
theorem B2836565 : Blo 1889435 2836565 := bbase (se 8 (by rfl) ⟨16620, by rfl⟩ : syracuseStep 2836565 = 33241) (by norm_num)
theorem B1891043 : Blo 1889435 1891043 := bstep (se 1 (by rfl) ⟨1418282, by rfl⟩ : syracuseStep 1891043 = 2836565) B2836565
theorem B27261845 : Blo 1889435 27261845 := bbase (se 6 (by rfl) ⟨638949, by rfl⟩ : syracuseStep 27261845 = 1277899) (by norm_num)
theorem B18174563 : Blo 1889435 18174563 := bstep (se 1 (by rfl) ⟨13630922, by rfl⟩ : syracuseStep 18174563 = 27261845) B27261845
theorem B12116375 : Blo 1889435 12116375 := bstep (se 1 (by rfl) ⟨9087281, by rfl⟩ : syracuseStep 12116375 = 18174563) B18174563
theorem B8077583 : Blo 1889435 8077583 := bstep (se 1 (by rfl) ⟨6058187, by rfl⟩ : syracuseStep 8077583 = 12116375) B12116375
theorem B5385055 : Blo 1889435 5385055 := bstep (se 1 (by rfl) ⟨4038791, by rfl⟩ : syracuseStep 5385055 = 8077583) B8077583
theorem B7180073 : Blo 1889435 7180073 := bstep (se 2 (by rfl) ⟨2692527, by rfl⟩ : syracuseStep 7180073 = 5385055) B5385055
theorem B4786715 : Blo 1889435 4786715 := bstep (se 1 (by rfl) ⟨3590036, by rfl⟩ : syracuseStep 4786715 = 7180073) B7180073
theorem B3191143 : Blo 1889435 3191143 := bstep (se 1 (by rfl) ⟨2393357, by rfl⟩ : syracuseStep 3191143 = 4786715) B4786715
theorem B4254857 : Blo 1889435 4254857 := bstep (se 2 (by rfl) ⟨1595571, by rfl⟩ : syracuseStep 4254857 = 3191143) B3191143
theorem B2836571 : Blo 1889435 2836571 := bstep (se 1 (by rfl) ⟨2127428, by rfl⟩ : syracuseStep 2836571 = 4254857) B4254857
theorem B1891047 : Blo 1889435 1891047 := bstep (se 1 (by rfl) ⟨1418285, by rfl⟩ : syracuseStep 1891047 = 2836571) B2836571
theorem B2127433 : Blo 1889435 2127433 := bbase (se 2 (by rfl) ⟨797787, by rfl⟩ : syracuseStep 2127433 = 1595575) (by norm_num)
theorem B2836577 : Blo 1889435 2836577 := bstep (se 2 (by rfl) ⟨1063716, by rfl⟩ : syracuseStep 2836577 = 2127433) B2127433
theorem B1891051 : Blo 1889435 1891051 := bstep (se 1 (by rfl) ⟨1418288, by rfl⟩ : syracuseStep 1891051 = 2836577) B2836577
theorem B2875285 : Blo 1889435 2875285 := bbase (se 6 (by rfl) ⟨67389, by rfl⟩ : syracuseStep 2875285 = 134779) (by norm_num)
theorem B3833713 : Blo 1889435 3833713 := bstep (se 2 (by rfl) ⟨1437642, by rfl⟩ : syracuseStep 3833713 = 2875285) B2875285
theorem B20446469 : Blo 1889435 20446469 := bstep (se 4 (by rfl) ⟨1916856, by rfl⟩ : syracuseStep 20446469 = 3833713) B3833713
theorem B13630979 : Blo 1889435 13630979 := bstep (se 1 (by rfl) ⟨10223234, by rfl⟩ : syracuseStep 13630979 = 20446469) B20446469
theorem B9087319 : Blo 1889435 9087319 := bstep (se 1 (by rfl) ⟨6815489, by rfl⟩ : syracuseStep 9087319 = 13630979) B13630979
theorem B12116425 : Blo 1889435 12116425 := bstep (se 2 (by rfl) ⟨4543659, by rfl⟩ : syracuseStep 12116425 = 9087319) B9087319
theorem B16155233 : Blo 1889435 16155233 := bstep (se 2 (by rfl) ⟨6058212, by rfl⟩ : syracuseStep 16155233 = 12116425) B12116425
theorem B10770155 : Blo 1889435 10770155 := bstep (se 1 (by rfl) ⟨8077616, by rfl⟩ : syracuseStep 10770155 = 16155233) B16155233
theorem B7180103 : Blo 1889435 7180103 := bstep (se 1 (by rfl) ⟨5385077, by rfl⟩ : syracuseStep 7180103 = 10770155) B10770155
theorem B4786735 : Blo 1889435 4786735 := bstep (se 1 (by rfl) ⟨3590051, by rfl⟩ : syracuseStep 4786735 = 7180103) B7180103
theorem B6382313 : Blo 1889435 6382313 := bstep (se 2 (by rfl) ⟨2393367, by rfl⟩ : syracuseStep 6382313 = 4786735) B4786735
theorem B4254875 : Blo 1889435 4254875 := bstep (se 1 (by rfl) ⟨3191156, by rfl⟩ : syracuseStep 4254875 = 6382313) B6382313
theorem B2836583 : Blo 1889435 2836583 := bstep (se 1 (by rfl) ⟨2127437, by rfl⟩ : syracuseStep 2836583 = 4254875) B4254875
theorem B1891055 : Blo 1889435 1891055 := bstep (se 1 (by rfl) ⟨1418291, by rfl⟩ : syracuseStep 1891055 = 2836583) B2836583
theorem B2836589 : Blo 1889435 2836589 := bbase (se 3 (by rfl) ⟨531860, by rfl⟩ : syracuseStep 2836589 = 1063721) (by norm_num)
theorem B1891059 : Blo 1889435 1891059 := bstep (se 1 (by rfl) ⟨1418294, by rfl⟩ : syracuseStep 1891059 = 2836589) B2836589
theorem B4254893 : Blo 1889435 4254893 := bbase (se 3 (by rfl) ⟨797792, by rfl⟩ : syracuseStep 4254893 = 1595585) (by norm_num)
theorem B2836595 : Blo 1889435 2836595 := bstep (se 1 (by rfl) ⟨2127446, by rfl⟩ : syracuseStep 2836595 = 4254893) B4254893
theorem B1891063 : Blo 1889435 1891063 := bstep (se 1 (by rfl) ⟨1418297, by rfl⟩ : syracuseStep 1891063 = 2836595) B2836595
theorem B2271845 : Blo 1889435 2271845 := bbase (se 4 (by rfl) ⟨212985, by rfl⟩ : syracuseStep 2271845 = 425971) (by norm_num)
theorem B6058253 : Blo 1889435 6058253 := bstep (se 3 (by rfl) ⟨1135922, by rfl⟩ : syracuseStep 6058253 = 2271845) B2271845
theorem B4038835 : Blo 1889435 4038835 := bstep (se 1 (by rfl) ⟨3029126, by rfl⟩ : syracuseStep 4038835 = 6058253) B6058253
theorem B5385113 : Blo 1889435 5385113 := bstep (se 2 (by rfl) ⟨2019417, by rfl⟩ : syracuseStep 5385113 = 4038835) B4038835
theorem B3590075 : Blo 1889435 3590075 := bstep (se 1 (by rfl) ⟨2692556, by rfl⟩ : syracuseStep 3590075 = 5385113) B5385113
theorem B2393383 : Blo 1889435 2393383 := bstep (se 1 (by rfl) ⟨1795037, by rfl⟩ : syracuseStep 2393383 = 3590075) B3590075
theorem B3191177 : Blo 1889435 3191177 := bstep (se 2 (by rfl) ⟨1196691, by rfl⟩ : syracuseStep 3191177 = 2393383) B2393383
theorem B2127451 : Blo 1889435 2127451 := bstep (se 1 (by rfl) ⟨1595588, by rfl⟩ : syracuseStep 2127451 = 3191177) B3191177
theorem B2836601 : Blo 1889435 2836601 := bstep (se 2 (by rfl) ⟨1063725, by rfl⟩ : syracuseStep 2836601 = 2127451) B2127451
theorem B1891067 : Blo 1889435 1891067 := bstep (se 1 (by rfl) ⟨1418300, by rfl⟩ : syracuseStep 1891067 = 2836601) B2836601
theorem B13631093 : Blo 1889435 13631093 := bbase (se 5 (by rfl) ⟨638957, by rfl⟩ : syracuseStep 13631093 = 1277915) (by norm_num)
theorem B9087395 : Blo 1889435 9087395 := bstep (se 1 (by rfl) ⟨6815546, by rfl⟩ : syracuseStep 9087395 = 13631093) B13631093
theorem B24233053 : Blo 1889435 24233053 := bstep (se 3 (by rfl) ⟨4543697, by rfl⟩ : syracuseStep 24233053 = 9087395) B9087395
theorem B32310737 : Blo 1889435 32310737 := bstep (se 2 (by rfl) ⟨12116526, by rfl⟩ : syracuseStep 32310737 = 24233053) B24233053
theorem B21540491 : Blo 1889435 21540491 := bstep (se 1 (by rfl) ⟨16155368, by rfl⟩ : syracuseStep 21540491 = 32310737) B32310737
theorem B14360327 : Blo 1889435 14360327 := bstep (se 1 (by rfl) ⟨10770245, by rfl⟩ : syracuseStep 14360327 = 21540491) B21540491
theorem B9573551 : Blo 1889435 9573551 := bstep (se 1 (by rfl) ⟨7180163, by rfl⟩ : syracuseStep 9573551 = 14360327) B14360327
theorem B6382367 : Blo 1889435 6382367 := bstep (se 1 (by rfl) ⟨4786775, by rfl⟩ : syracuseStep 6382367 = 9573551) B9573551
theorem B4254911 : Blo 1889435 4254911 := bstep (se 1 (by rfl) ⟨3191183, by rfl⟩ : syracuseStep 4254911 = 6382367) B6382367
theorem B2836607 : Blo 1889435 2836607 := bstep (se 1 (by rfl) ⟨2127455, by rfl⟩ : syracuseStep 2836607 = 4254911) B4254911
theorem B1891071 : Blo 1889435 1891071 := bstep (se 1 (by rfl) ⟨1418303, by rfl⟩ : syracuseStep 1891071 = 2836607) B2836607
theorem B2836613 : Blo 1889435 2836613 := bbase (se 4 (by rfl) ⟨265932, by rfl⟩ : syracuseStep 2836613 = 531865) (by norm_num)
theorem B1891075 : Blo 1889435 1891075 := bstep (se 1 (by rfl) ⟨1418306, by rfl⟩ : syracuseStep 1891075 = 2836613) B2836613
theorem B3191197 : Blo 1889435 3191197 := bbase (se 3 (by rfl) ⟨598349, by rfl⟩ : syracuseStep 3191197 = 1196699) (by norm_num)
theorem B4254929 : Blo 1889435 4254929 := bstep (se 2 (by rfl) ⟨1595598, by rfl⟩ : syracuseStep 4254929 = 3191197) B3191197
theorem B2836619 : Blo 1889435 2836619 := bstep (se 1 (by rfl) ⟨2127464, by rfl⟩ : syracuseStep 2836619 = 4254929) B4254929
theorem B1891079 : Blo 1889435 1891079 := bstep (se 1 (by rfl) ⟨1418309, by rfl⟩ : syracuseStep 1891079 = 2836619) B2836619
theorem B2127469 : Blo 1889435 2127469 := bbase (se 3 (by rfl) ⟨398900, by rfl⟩ : syracuseStep 2127469 = 797801) (by norm_num)
theorem B2836625 : Blo 1889435 2836625 := bstep (se 2 (by rfl) ⟨1063734, by rfl⟩ : syracuseStep 2836625 = 2127469) B2127469
theorem B1891083 : Blo 1889435 1891083 := bstep (se 1 (by rfl) ⟨1418312, by rfl⟩ : syracuseStep 1891083 = 2836625) B2836625
theorem B6382421 : Blo 1889435 6382421 := bbase (se 9 (by rfl) ⟨18698, by rfl⟩ : syracuseStep 6382421 = 37397) (by norm_num)
theorem B4254947 : Blo 1889435 4254947 := bstep (se 1 (by rfl) ⟨3191210, by rfl⟩ : syracuseStep 4254947 = 6382421) B6382421
theorem B2836631 : Blo 1889435 2836631 := bstep (se 1 (by rfl) ⟨2127473, by rfl⟩ : syracuseStep 2836631 = 4254947) B4254947
theorem B1891087 : Blo 1889435 1891087 := bstep (se 1 (by rfl) ⟨1418315, by rfl⟩ : syracuseStep 1891087 = 2836631) B2836631
theorem B2836637 : Blo 1889435 2836637 := bbase (se 3 (by rfl) ⟨531869, by rfl⟩ : syracuseStep 2836637 = 1063739) (by norm_num)
theorem B1891091 : Blo 1889435 1891091 := bstep (se 1 (by rfl) ⟨1418318, by rfl⟩ : syracuseStep 1891091 = 2836637) B2836637
theorem B4254965 : Blo 1889435 4254965 := bbase (se 5 (by rfl) ⟨199451, by rfl⟩ : syracuseStep 4254965 = 398903) (by norm_num)
theorem B2836643 : Blo 1889435 2836643 := bstep (se 1 (by rfl) ⟨2127482, by rfl⟩ : syracuseStep 2836643 = 4254965) B4254965
theorem B1891095 : Blo 1889435 1891095 := bstep (se 1 (by rfl) ⟨1418321, by rfl⟩ : syracuseStep 1891095 = 2836643) B2836643
theorem B7667605 : Blo 1889435 7667605 := bbase (se 6 (by rfl) ⟨179709, by rfl⟩ : syracuseStep 7667605 = 359419) (by norm_num)
theorem B40893893 : Blo 1889435 40893893 := bstep (se 4 (by rfl) ⟨3833802, by rfl⟩ : syracuseStep 40893893 = 7667605) B7667605
theorem B27262595 : Blo 1889435 27262595 := bstep (se 1 (by rfl) ⟨20446946, by rfl⟩ : syracuseStep 27262595 = 40893893) B40893893
theorem B18175063 : Blo 1889435 18175063 := bstep (se 1 (by rfl) ⟨13631297, by rfl⟩ : syracuseStep 18175063 = 27262595) B27262595
theorem B24233417 : Blo 1889435 24233417 := bstep (se 2 (by rfl) ⟨9087531, by rfl⟩ : syracuseStep 24233417 = 18175063) B18175063
theorem B16155611 : Blo 1889435 16155611 := bstep (se 1 (by rfl) ⟨12116708, by rfl⟩ : syracuseStep 16155611 = 24233417) B24233417
theorem B10770407 : Blo 1889435 10770407 := bstep (se 1 (by rfl) ⟨8077805, by rfl⟩ : syracuseStep 10770407 = 16155611) B16155611
theorem B7180271 : Blo 1889435 7180271 := bstep (se 1 (by rfl) ⟨5385203, by rfl⟩ : syracuseStep 7180271 = 10770407) B10770407
theorem B4786847 : Blo 1889435 4786847 := bstep (se 1 (by rfl) ⟨3590135, by rfl⟩ : syracuseStep 4786847 = 7180271) B7180271
theorem B3191231 : Blo 1889435 3191231 := bstep (se 1 (by rfl) ⟨2393423, by rfl⟩ : syracuseStep 3191231 = 4786847) B4786847
theorem B2127487 : Blo 1889435 2127487 := bstep (se 1 (by rfl) ⟨1595615, by rfl⟩ : syracuseStep 2127487 = 3191231) B3191231
theorem B2836649 : Blo 1889435 2836649 := bstep (se 2 (by rfl) ⟨1063743, by rfl⟩ : syracuseStep 2836649 = 2127487) B2127487
theorem B1891099 : Blo 1889435 1891099 := bstep (se 1 (by rfl) ⟨1418324, by rfl⟩ : syracuseStep 1891099 = 2836649) B2836649
theorem B69008597 : Blo 1889435 69008597 := bbase (se 7 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 69008597 = 1617389) (by norm_num)
theorem B46005731 : Blo 1889435 46005731 := bstep (se 1 (by rfl) ⟨34504298, by rfl⟩ : syracuseStep 46005731 = 69008597) B69008597
theorem B30670487 : Blo 1889435 30670487 := bstep (se 1 (by rfl) ⟨23002865, by rfl⟩ : syracuseStep 30670487 = 46005731) B46005731
theorem B20446991 : Blo 1889435 20446991 := bstep (se 1 (by rfl) ⟨15335243, by rfl⟩ : syracuseStep 20446991 = 30670487) B30670487
theorem B13631327 : Blo 1889435 13631327 := bstep (se 1 (by rfl) ⟨10223495, by rfl⟩ : syracuseStep 13631327 = 20446991) B20446991
theorem B9087551 : Blo 1889435 9087551 := bstep (se 1 (by rfl) ⟨6815663, by rfl⟩ : syracuseStep 9087551 = 13631327) B13631327
theorem B6058367 : Blo 1889435 6058367 := bstep (se 1 (by rfl) ⟨4543775, by rfl⟩ : syracuseStep 6058367 = 9087551) B9087551
theorem B4038911 : Blo 1889435 4038911 := bstep (se 1 (by rfl) ⟨3029183, by rfl⟩ : syracuseStep 4038911 = 6058367) B6058367
theorem B2692607 : Blo 1889435 2692607 := bstep (se 1 (by rfl) ⟨2019455, by rfl⟩ : syracuseStep 2692607 = 4038911) B4038911
theorem B7180285 : Blo 1889435 7180285 := bstep (se 3 (by rfl) ⟨1346303, by rfl⟩ : syracuseStep 7180285 = 2692607) B2692607
theorem B9573713 : Blo 1889435 9573713 := bstep (se 2 (by rfl) ⟨3590142, by rfl⟩ : syracuseStep 9573713 = 7180285) B7180285
theorem B6382475 : Blo 1889435 6382475 := bstep (se 1 (by rfl) ⟨4786856, by rfl⟩ : syracuseStep 6382475 = 9573713) B9573713
theorem B4254983 : Blo 1889435 4254983 := bstep (se 1 (by rfl) ⟨3191237, by rfl⟩ : syracuseStep 4254983 = 6382475) B6382475
theorem B2836655 : Blo 1889435 2836655 := bstep (se 1 (by rfl) ⟨2127491, by rfl⟩ : syracuseStep 2836655 = 4254983) B4254983
theorem B1891103 : Blo 1889435 1891103 := bstep (se 1 (by rfl) ⟨1418327, by rfl⟩ : syracuseStep 1891103 = 2836655) B2836655
theorem B2836661 : Blo 1889435 2836661 := bbase (se 5 (by rfl) ⟨132968, by rfl⟩ : syracuseStep 2836661 = 265937) (by norm_num)
theorem B1891107 : Blo 1889435 1891107 := bstep (se 1 (by rfl) ⟨1418330, by rfl⟩ : syracuseStep 1891107 = 2836661) B2836661
theorem B4786877 : Blo 1889435 4786877 := bbase (se 3 (by rfl) ⟨897539, by rfl⟩ : syracuseStep 4786877 = 1795079) (by norm_num)
theorem B3191251 : Blo 1889435 3191251 := bstep (se 1 (by rfl) ⟨2393438, by rfl⟩ : syracuseStep 3191251 = 4786877) B4786877
theorem B4255001 : Blo 1889435 4255001 := bstep (se 2 (by rfl) ⟨1595625, by rfl⟩ : syracuseStep 4255001 = 3191251) B3191251
theorem B2836667 : Blo 1889435 2836667 := bstep (se 1 (by rfl) ⟨2127500, by rfl⟩ : syracuseStep 2836667 = 4255001) B4255001
theorem B1891111 : Blo 1889435 1891111 := bstep (se 1 (by rfl) ⟨1418333, by rfl⟩ : syracuseStep 1891111 = 2836667) B2836667
theorem B2127505 : Blo 1889435 2127505 := bbase (se 2 (by rfl) ⟨797814, by rfl⟩ : syracuseStep 2127505 = 1595629) (by norm_num)
theorem B2836673 : Blo 1889435 2836673 := bstep (se 2 (by rfl) ⟨1063752, by rfl⟩ : syracuseStep 2836673 = 2127505) B2127505
theorem B1891115 : Blo 1889435 1891115 := bstep (se 1 (by rfl) ⟨1418336, by rfl⟩ : syracuseStep 1891115 = 2836673) B2836673
theorem B3590173 : Blo 1889435 3590173 := bbase (se 3 (by rfl) ⟨673157, by rfl⟩ : syracuseStep 3590173 = 1346315) (by norm_num)
theorem B4786897 : Blo 1889435 4786897 := bstep (se 2 (by rfl) ⟨1795086, by rfl⟩ : syracuseStep 4786897 = 3590173) B3590173
theorem B6382529 : Blo 1889435 6382529 := bstep (se 2 (by rfl) ⟨2393448, by rfl⟩ : syracuseStep 6382529 = 4786897) B4786897
theorem B4255019 : Blo 1889435 4255019 := bstep (se 1 (by rfl) ⟨3191264, by rfl⟩ : syracuseStep 4255019 = 6382529) B6382529
theorem B2836679 : Blo 1889435 2836679 := bstep (se 1 (by rfl) ⟨2127509, by rfl⟩ : syracuseStep 2836679 = 4255019) B4255019
theorem B1891119 : Blo 1889435 1891119 := bstep (se 1 (by rfl) ⟨1418339, by rfl⟩ : syracuseStep 1891119 = 2836679) B2836679
theorem B2836685 : Blo 1889435 2836685 := bbase (se 3 (by rfl) ⟨531878, by rfl⟩ : syracuseStep 2836685 = 1063757) (by norm_num)
theorem B1891123 : Blo 1889435 1891123 := bstep (se 1 (by rfl) ⟨1418342, by rfl⟩ : syracuseStep 1891123 = 2836685) B2836685
theorem B4255037 : Blo 1889435 4255037 := bbase (se 3 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 4255037 = 1595639) (by norm_num)
theorem B2836691 : Blo 1889435 2836691 := bstep (se 1 (by rfl) ⟨2127518, by rfl⟩ : syracuseStep 2836691 = 4255037) B4255037
theorem B1891127 : Blo 1889435 1891127 := bstep (se 1 (by rfl) ⟨1418345, by rfl⟩ : syracuseStep 1891127 = 2836691) B2836691
theorem B3191285 : Blo 1889435 3191285 := bbase (se 5 (by rfl) ⟨149591, by rfl⟩ : syracuseStep 3191285 = 299183) (by norm_num)
theorem B2127523 : Blo 1889435 2127523 := bstep (se 1 (by rfl) ⟨1595642, by rfl⟩ : syracuseStep 2127523 = 3191285) B3191285
theorem B2836697 : Blo 1889435 2836697 := bstep (se 2 (by rfl) ⟨1063761, by rfl⟩ : syracuseStep 2836697 = 2127523) B2127523
theorem B1891131 : Blo 1889435 1891131 := bstep (se 1 (by rfl) ⟨1418348, by rfl⟩ : syracuseStep 1891131 = 2836697) B2836697
theorem B6058469 : Blo 1889435 6058469 := bbase (se 4 (by rfl) ⟨567981, by rfl⟩ : syracuseStep 6058469 = 1135963) (by norm_num)
theorem B4038979 : Blo 1889435 4038979 := bstep (se 1 (by rfl) ⟨3029234, by rfl⟩ : syracuseStep 4038979 = 6058469) B6058469
theorem B5385305 : Blo 1889435 5385305 := bstep (se 2 (by rfl) ⟨2019489, by rfl⟩ : syracuseStep 5385305 = 4038979) B4038979
theorem B14360813 : Blo 1889435 14360813 := bstep (se 3 (by rfl) ⟨2692652, by rfl⟩ : syracuseStep 14360813 = 5385305) B5385305
theorem B9573875 : Blo 1889435 9573875 := bstep (se 1 (by rfl) ⟨7180406, by rfl⟩ : syracuseStep 9573875 = 14360813) B14360813
theorem B6382583 : Blo 1889435 6382583 := bstep (se 1 (by rfl) ⟨4786937, by rfl⟩ : syracuseStep 6382583 = 9573875) B9573875
theorem B4255055 : Blo 1889435 4255055 := bstep (se 1 (by rfl) ⟨3191291, by rfl⟩ : syracuseStep 4255055 = 6382583) B6382583
theorem B2836703 : Blo 1889435 2836703 := bstep (se 1 (by rfl) ⟨2127527, by rfl⟩ : syracuseStep 2836703 = 4255055) B4255055
theorem B1891135 : Blo 1889435 1891135 := bstep (se 1 (by rfl) ⟨1418351, by rfl⟩ : syracuseStep 1891135 = 2836703) B2836703
theorem B2836709 : Blo 1889435 2836709 := bbase (se 4 (by rfl) ⟨265941, by rfl⟩ : syracuseStep 2836709 = 531883) (by norm_num)
theorem B1891139 : Blo 1889435 1891139 := bstep (se 1 (by rfl) ⟨1418354, by rfl⟩ : syracuseStep 1891139 = 2836709) B2836709
theorem B4038997 : Blo 1889435 4038997 := bbase (se 10 (by rfl) ⟨5916, by rfl⟩ : syracuseStep 4038997 = 11833) (by norm_num)
theorem B5385329 : Blo 1889435 5385329 := bstep (se 2 (by rfl) ⟨2019498, by rfl⟩ : syracuseStep 5385329 = 4038997) B4038997
theorem B3590219 : Blo 1889435 3590219 := bstep (se 1 (by rfl) ⟨2692664, by rfl⟩ : syracuseStep 3590219 = 5385329) B5385329
theorem B2393479 : Blo 1889435 2393479 := bstep (se 1 (by rfl) ⟨1795109, by rfl⟩ : syracuseStep 2393479 = 3590219) B3590219
theorem B3191305 : Blo 1889435 3191305 := bstep (se 2 (by rfl) ⟨1196739, by rfl⟩ : syracuseStep 3191305 = 2393479) B2393479
theorem B4255073 : Blo 1889435 4255073 := bstep (se 2 (by rfl) ⟨1595652, by rfl⟩ : syracuseStep 4255073 = 3191305) B3191305
theorem B2836715 : Blo 1889435 2836715 := bstep (se 1 (by rfl) ⟨2127536, by rfl⟩ : syracuseStep 2836715 = 4255073) B4255073
theorem B1891143 : Blo 1889435 1891143 := bstep (se 1 (by rfl) ⟨1418357, by rfl⟩ : syracuseStep 1891143 = 2836715) B2836715
theorem B2127541 : Blo 1889435 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B2836721 : Blo 1889435 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B1891147 : Blo 1889435 1891147 := bstep (se 1 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 1891147 = 2836721) B2836721
theorem B2393489 : Blo 1889435 2393489 := bbase (se 2 (by rfl) ⟨897558, by rfl⟩ : syracuseStep 2393489 = 1795117) (by norm_num)
theorem B6382637 : Blo 1889435 6382637 := bstep (se 3 (by rfl) ⟨1196744, by rfl⟩ : syracuseStep 6382637 = 2393489) B2393489
theorem B4255091 : Blo 1889435 4255091 := bstep (se 1 (by rfl) ⟨3191318, by rfl⟩ : syracuseStep 4255091 = 6382637) B6382637
theorem B2836727 : Blo 1889435 2836727 := bstep (se 1 (by rfl) ⟨2127545, by rfl⟩ : syracuseStep 2836727 = 4255091) B4255091
theorem B1891151 : Blo 1889435 1891151 := bstep (se 1 (by rfl) ⟨1418363, by rfl⟩ : syracuseStep 1891151 = 2836727) B2836727
theorem B2836733 : Blo 1889435 2836733 := bbase (se 3 (by rfl) ⟨531887, by rfl⟩ : syracuseStep 2836733 = 1063775) (by norm_num)
theorem B1891155 : Blo 1889435 1891155 := bstep (se 1 (by rfl) ⟨1418366, by rfl⟩ : syracuseStep 1891155 = 2836733) B2836733
theorem B4255109 : Blo 1889435 4255109 := bbase (se 4 (by rfl) ⟨398916, by rfl⟩ : syracuseStep 4255109 = 797833) (by norm_num)
theorem B2836739 : Blo 1889435 2836739 := bstep (se 1 (by rfl) ⟨2127554, by rfl⟩ : syracuseStep 2836739 = 4255109) B4255109
theorem B1891159 : Blo 1889435 1891159 := bstep (se 1 (by rfl) ⟨1418369, by rfl⟩ : syracuseStep 1891159 = 2836739) B2836739
theorem B2692693 : Blo 1889435 2692693 := bbase (se 8 (by rfl) ⟨15777, by rfl⟩ : syracuseStep 2692693 = 31555) (by norm_num)
theorem B3590257 : Blo 1889435 3590257 := bstep (se 2 (by rfl) ⟨1346346, by rfl⟩ : syracuseStep 3590257 = 2692693) B2692693
theorem B4787009 : Blo 1889435 4787009 := bstep (se 2 (by rfl) ⟨1795128, by rfl⟩ : syracuseStep 4787009 = 3590257) B3590257
theorem B3191339 : Blo 1889435 3191339 := bstep (se 1 (by rfl) ⟨2393504, by rfl⟩ : syracuseStep 3191339 = 4787009) B4787009
theorem B2127559 : Blo 1889435 2127559 := bstep (se 1 (by rfl) ⟨1595669, by rfl⟩ : syracuseStep 2127559 = 3191339) B3191339
theorem B2836745 : Blo 1889435 2836745 := bstep (se 2 (by rfl) ⟨1063779, by rfl⟩ : syracuseStep 2836745 = 2127559) B2127559
theorem B1891163 : Blo 1889435 1891163 := bstep (se 1 (by rfl) ⟨1418372, by rfl⟩ : syracuseStep 1891163 = 2836745) B2836745
theorem B9574037 : Blo 1889435 9574037 := bbase (se 6 (by rfl) ⟨224391, by rfl⟩ : syracuseStep 9574037 = 448783) (by norm_num)
theorem B6382691 : Blo 1889435 6382691 := bstep (se 1 (by rfl) ⟨4787018, by rfl⟩ : syracuseStep 6382691 = 9574037) B9574037
theorem B4255127 : Blo 1889435 4255127 := bstep (se 1 (by rfl) ⟨3191345, by rfl⟩ : syracuseStep 4255127 = 6382691) B6382691
theorem B2836751 : Blo 1889435 2836751 := bstep (se 1 (by rfl) ⟨2127563, by rfl⟩ : syracuseStep 2836751 = 4255127) B4255127
theorem B1891167 : Blo 1889435 1891167 := bstep (se 1 (by rfl) ⟨1418375, by rfl⟩ : syracuseStep 1891167 = 2836751) B2836751
theorem B2836757 : Blo 1889435 2836757 := bbase (se 6 (by rfl) ⟨66486, by rfl⟩ : syracuseStep 2836757 = 132973) (by norm_num)
theorem B1891171 : Blo 1889435 1891171 := bstep (se 1 (by rfl) ⟨1418378, by rfl⟩ : syracuseStep 1891171 = 2836757) B2836757
theorem B24234389 : Blo 1889435 24234389 := bbase (se 6 (by rfl) ⟨567993, by rfl⟩ : syracuseStep 24234389 = 1135987) (by norm_num)
theorem B16156259 : Blo 1889435 16156259 := bstep (se 1 (by rfl) ⟨12117194, by rfl⟩ : syracuseStep 16156259 = 24234389) B24234389
theorem B10770839 : Blo 1889435 10770839 := bstep (se 1 (by rfl) ⟨8078129, by rfl⟩ : syracuseStep 10770839 = 16156259) B16156259
theorem B7180559 : Blo 1889435 7180559 := bstep (se 1 (by rfl) ⟨5385419, by rfl⟩ : syracuseStep 7180559 = 10770839) B10770839
theorem B4787039 : Blo 1889435 4787039 := bstep (se 1 (by rfl) ⟨3590279, by rfl⟩ : syracuseStep 4787039 = 7180559) B7180559
theorem B3191359 : Blo 1889435 3191359 := bstep (se 1 (by rfl) ⟨2393519, by rfl⟩ : syracuseStep 3191359 = 4787039) B4787039
theorem B4255145 : Blo 1889435 4255145 := bstep (se 2 (by rfl) ⟨1595679, by rfl⟩ : syracuseStep 4255145 = 3191359) B3191359
theorem B2836763 : Blo 1889435 2836763 := bstep (se 1 (by rfl) ⟨2127572, by rfl⟩ : syracuseStep 2836763 = 4255145) B4255145
theorem B1891175 : Blo 1889435 1891175 := bstep (se 1 (by rfl) ⟨1418381, by rfl⟩ : syracuseStep 1891175 = 2836763) B2836763
theorem B2127577 : Blo 1889435 2127577 := bbase (se 2 (by rfl) ⟨797841, by rfl⟩ : syracuseStep 2127577 = 1595683) (by norm_num)
theorem B2836769 : Blo 1889435 2836769 := bstep (se 2 (by rfl) ⟨1063788, by rfl⟩ : syracuseStep 2836769 = 2127577) B2127577
theorem B1891179 : Blo 1889435 1891179 := bstep (se 1 (by rfl) ⟨1418384, by rfl⟩ : syracuseStep 1891179 = 2836769) B2836769
theorem B2019541 : Blo 1889435 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B2692721 : Blo 1889435 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B7180589 : Blo 1889435 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B4787059 : Blo 1889435 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B6382745 : Blo 1889435 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B4255163 : Blo 1889435 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B2836775 : Blo 1889435 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B1891183 : Blo 1889435 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B2836781 : Blo 1889435 2836781 := bbase (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) (by norm_num)
theorem B1891187 : Blo 1889435 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B4255181 : Blo 1889435 4255181 := bbase (se 3 (by rfl) ⟨797846, by rfl⟩ : syracuseStep 4255181 = 1595693) (by norm_num)
theorem B2836787 : Blo 1889435 2836787 := bstep (se 1 (by rfl) ⟨2127590, by rfl⟩ : syracuseStep 2836787 = 4255181) B4255181
theorem B1891191 : Blo 1889435 1891191 := bstep (se 1 (by rfl) ⟨1418393, by rfl⟩ : syracuseStep 1891191 = 2836787) B2836787
theorem B2393545 : Blo 1889435 2393545 := bbase (se 2 (by rfl) ⟨897579, by rfl⟩ : syracuseStep 2393545 = 1795159) (by norm_num)
theorem B3191393 : Blo 1889435 3191393 := bstep (se 2 (by rfl) ⟨1196772, by rfl⟩ : syracuseStep 3191393 = 2393545) B2393545
theorem B2127595 : Blo 1889435 2127595 := bstep (se 1 (by rfl) ⟨1595696, by rfl⟩ : syracuseStep 2127595 = 3191393) B3191393
theorem B2836793 : Blo 1889435 2836793 := bstep (se 2 (by rfl) ⟨1063797, by rfl⟩ : syracuseStep 2836793 = 2127595) B2127595
theorem B1891195 : Blo 1889435 1891195 := bstep (se 1 (by rfl) ⟨1418396, by rfl⟩ : syracuseStep 1891195 = 2836793) B2836793
theorem B18176021 : Blo 1889435 18176021 := bbase (se 6 (by rfl) ⟨426000, by rfl⟩ : syracuseStep 18176021 = 852001) (by norm_num)
theorem B12117347 : Blo 1889435 12117347 := bstep (se 1 (by rfl) ⟨9088010, by rfl⟩ : syracuseStep 12117347 = 18176021) B18176021
theorem B8078231 : Blo 1889435 8078231 := bstep (se 1 (by rfl) ⟨6058673, by rfl⟩ : syracuseStep 8078231 = 12117347) B12117347
theorem B21541949 : Blo 1889435 21541949 := bstep (se 3 (by rfl) ⟨4039115, by rfl⟩ : syracuseStep 21541949 = 8078231) B8078231
theorem B14361299 : Blo 1889435 14361299 := bstep (se 1 (by rfl) ⟨10770974, by rfl⟩ : syracuseStep 14361299 = 21541949) B21541949
theorem B9574199 : Blo 1889435 9574199 := bstep (se 1 (by rfl) ⟨7180649, by rfl⟩ : syracuseStep 9574199 = 14361299) B14361299
theorem B6382799 : Blo 1889435 6382799 := bstep (se 1 (by rfl) ⟨4787099, by rfl⟩ : syracuseStep 6382799 = 9574199) B9574199
theorem B4255199 : Blo 1889435 4255199 := bstep (se 1 (by rfl) ⟨3191399, by rfl⟩ : syracuseStep 4255199 = 6382799) B6382799
theorem B2836799 : Blo 1889435 2836799 := bstep (se 1 (by rfl) ⟨2127599, by rfl⟩ : syracuseStep 2836799 = 4255199) B4255199
theorem B1891199 : Blo 1889435 1891199 := bstep (se 1 (by rfl) ⟨1418399, by rfl⟩ : syracuseStep 1891199 = 2836799) B2836799
theorem B2836805 : Blo 1889435 2836805 := bbase (se 4 (by rfl) ⟨265950, by rfl⟩ : syracuseStep 2836805 = 531901) (by norm_num)
theorem B1891203 : Blo 1889435 1891203 := bstep (se 1 (by rfl) ⟨1418402, by rfl⟩ : syracuseStep 1891203 = 2836805) B2836805
theorem B3191413 : Blo 1889435 3191413 := bbase (se 5 (by rfl) ⟨149597, by rfl⟩ : syracuseStep 3191413 = 299195) (by norm_num)
theorem B4255217 : Blo 1889435 4255217 := bstep (se 2 (by rfl) ⟨1595706, by rfl⟩ : syracuseStep 4255217 = 3191413) B3191413
theorem B2836811 : Blo 1889435 2836811 := bstep (se 1 (by rfl) ⟨2127608, by rfl⟩ : syracuseStep 2836811 = 4255217) B4255217
theorem B1891207 : Blo 1889435 1891207 := bstep (se 1 (by rfl) ⟨1418405, by rfl⟩ : syracuseStep 1891207 = 2836811) B2836811
theorem B2127613 : Blo 1889435 2127613 := bbase (se 3 (by rfl) ⟨398927, by rfl⟩ : syracuseStep 2127613 = 797855) (by norm_num)
theorem B2836817 : Blo 1889435 2836817 := bstep (se 2 (by rfl) ⟨1063806, by rfl⟩ : syracuseStep 2836817 = 2127613) B2127613
theorem B1891211 : Blo 1889435 1891211 := bstep (se 1 (by rfl) ⟨1418408, by rfl⟩ : syracuseStep 1891211 = 2836817) B2836817
theorem B6382853 : Blo 1889435 6382853 := bbase (se 4 (by rfl) ⟨598392, by rfl⟩ : syracuseStep 6382853 = 1196785) (by norm_num)
theorem B4255235 : Blo 1889435 4255235 := bstep (se 1 (by rfl) ⟨3191426, by rfl⟩ : syracuseStep 4255235 = 6382853) B6382853
theorem B2836823 : Blo 1889435 2836823 := bstep (se 1 (by rfl) ⟨2127617, by rfl⟩ : syracuseStep 2836823 = 4255235) B4255235
theorem B1891215 : Blo 1889435 1891215 := bstep (se 1 (by rfl) ⟨1418411, by rfl⟩ : syracuseStep 1891215 = 2836823) B2836823
theorem B2836829 : Blo 1889435 2836829 := bbase (se 3 (by rfl) ⟨531905, by rfl⟩ : syracuseStep 2836829 = 1063811) (by norm_num)
theorem B1891219 : Blo 1889435 1891219 := bstep (se 1 (by rfl) ⟨1418414, by rfl⟩ : syracuseStep 1891219 = 2836829) B2836829
theorem B4255253 : Blo 1889435 4255253 := bbase (se 6 (by rfl) ⟨99732, by rfl⟩ : syracuseStep 4255253 = 199465) (by norm_num)
theorem B2836835 : Blo 1889435 2836835 := bstep (se 1 (by rfl) ⟨2127626, by rfl⟩ : syracuseStep 2836835 = 4255253) B4255253
theorem B1891223 : Blo 1889435 1891223 := bstep (se 1 (by rfl) ⟨1418417, by rfl⟩ : syracuseStep 1891223 = 2836835) B2836835
theorem B7180757 : Blo 1889435 7180757 := bbase (se 7 (by rfl) ⟨84149, by rfl⟩ : syracuseStep 7180757 = 168299) (by norm_num)
theorem B4787171 : Blo 1889435 4787171 := bstep (se 1 (by rfl) ⟨3590378, by rfl⟩ : syracuseStep 4787171 = 7180757) B7180757
theorem B3191447 : Blo 1889435 3191447 := bstep (se 1 (by rfl) ⟨2393585, by rfl⟩ : syracuseStep 3191447 = 4787171) B4787171
theorem B2127631 : Blo 1889435 2127631 := bstep (se 1 (by rfl) ⟨1595723, by rfl⟩ : syracuseStep 2127631 = 3191447) B3191447
theorem B2836841 : Blo 1889435 2836841 := bstep (se 2 (by rfl) ⟨1063815, by rfl⟩ : syracuseStep 2836841 = 2127631) B2127631
theorem B1891227 : Blo 1889435 1891227 := bstep (se 1 (by rfl) ⟨1418420, by rfl⟩ : syracuseStep 1891227 = 2836841) B2836841
theorem B10771157 : Blo 1889435 10771157 := bbase (se 7 (by rfl) ⟨126224, by rfl⟩ : syracuseStep 10771157 = 252449) (by norm_num)
theorem B7180771 : Blo 1889435 7180771 := bstep (se 1 (by rfl) ⟨5385578, by rfl⟩ : syracuseStep 7180771 = 10771157) B10771157
theorem B9574361 : Blo 1889435 9574361 := bstep (se 2 (by rfl) ⟨3590385, by rfl⟩ : syracuseStep 9574361 = 7180771) B7180771
theorem B6382907 : Blo 1889435 6382907 := bstep (se 1 (by rfl) ⟨4787180, by rfl⟩ : syracuseStep 6382907 = 9574361) B9574361
theorem B4255271 : Blo 1889435 4255271 := bstep (se 1 (by rfl) ⟨3191453, by rfl⟩ : syracuseStep 4255271 = 6382907) B6382907
theorem B2836847 : Blo 1889435 2836847 := bstep (se 1 (by rfl) ⟨2127635, by rfl⟩ : syracuseStep 2836847 = 4255271) B4255271
theorem B1891231 : Blo 1889435 1891231 := bstep (se 1 (by rfl) ⟨1418423, by rfl⟩ : syracuseStep 1891231 = 2836847) B2836847
theorem B2836853 : Blo 1889435 2836853 := bbase (se 5 (by rfl) ⟨132977, by rfl⟩ : syracuseStep 2836853 = 265955) (by norm_num)
theorem B1891235 : Blo 1889435 1891235 := bstep (se 1 (by rfl) ⟨1418426, by rfl⟩ : syracuseStep 1891235 = 2836853) B2836853
theorem B2019601 : Blo 1889435 2019601 := bbase (se 2 (by rfl) ⟨757350, by rfl⟩ : syracuseStep 2019601 = 1514701) (by norm_num)
theorem B2692801 : Blo 1889435 2692801 := bstep (se 2 (by rfl) ⟨1009800, by rfl⟩ : syracuseStep 2692801 = 2019601) B2019601
theorem B3590401 : Blo 1889435 3590401 := bstep (se 2 (by rfl) ⟨1346400, by rfl⟩ : syracuseStep 3590401 = 2692801) B2692801
theorem B4787201 : Blo 1889435 4787201 := bstep (se 2 (by rfl) ⟨1795200, by rfl⟩ : syracuseStep 4787201 = 3590401) B3590401
theorem B3191467 : Blo 1889435 3191467 := bstep (se 1 (by rfl) ⟨2393600, by rfl⟩ : syracuseStep 3191467 = 4787201) B4787201
theorem B4255289 : Blo 1889435 4255289 := bstep (se 2 (by rfl) ⟨1595733, by rfl⟩ : syracuseStep 4255289 = 3191467) B3191467
theorem B2836859 : Blo 1889435 2836859 := bstep (se 1 (by rfl) ⟨2127644, by rfl⟩ : syracuseStep 2836859 = 4255289) B4255289
theorem B1891239 : Blo 1889435 1891239 := bstep (se 1 (by rfl) ⟨1418429, by rfl⟩ : syracuseStep 1891239 = 2836859) B2836859
theorem B2127649 : Blo 1889435 2127649 := bbase (se 2 (by rfl) ⟨797868, by rfl⟩ : syracuseStep 2127649 = 1595737) (by norm_num)
theorem B2836865 : Blo 1889435 2836865 := bstep (se 2 (by rfl) ⟨1063824, by rfl⟩ : syracuseStep 2836865 = 2127649) B2127649
theorem B1891243 : Blo 1889435 1891243 := bstep (se 1 (by rfl) ⟨1418432, by rfl⟩ : syracuseStep 1891243 = 2836865) B2836865
theorem B4787221 : Blo 1889435 4787221 := bbase (se 6 (by rfl) ⟨112200, by rfl⟩ : syracuseStep 4787221 = 224401) (by norm_num)
theorem B6382961 : Blo 1889435 6382961 := bstep (se 2 (by rfl) ⟨2393610, by rfl⟩ : syracuseStep 6382961 = 4787221) B4787221
theorem B4255307 : Blo 1889435 4255307 := bstep (se 1 (by rfl) ⟨3191480, by rfl⟩ : syracuseStep 4255307 = 6382961) B6382961
theorem B2836871 : Blo 1889435 2836871 := bstep (se 1 (by rfl) ⟨2127653, by rfl⟩ : syracuseStep 2836871 = 4255307) B4255307
theorem B1891247 : Blo 1889435 1891247 := bstep (se 1 (by rfl) ⟨1418435, by rfl⟩ : syracuseStep 1891247 = 2836871) B2836871
theorem B2836877 : Blo 1889435 2836877 := bbase (se 3 (by rfl) ⟨531914, by rfl⟩ : syracuseStep 2836877 = 1063829) (by norm_num)
theorem B1891251 : Blo 1889435 1891251 := bstep (se 1 (by rfl) ⟨1418438, by rfl⟩ : syracuseStep 1891251 = 2836877) B2836877
theorem B4255325 : Blo 1889435 4255325 := bbase (se 3 (by rfl) ⟨797873, by rfl⟩ : syracuseStep 4255325 = 1595747) (by norm_num)
theorem B2836883 : Blo 1889435 2836883 := bstep (se 1 (by rfl) ⟨2127662, by rfl⟩ : syracuseStep 2836883 = 4255325) B4255325
theorem B1891255 : Blo 1889435 1891255 := bstep (se 1 (by rfl) ⟨1418441, by rfl⟩ : syracuseStep 1891255 = 2836883) B2836883
theorem B3191501 : Blo 1889435 3191501 := bbase (se 3 (by rfl) ⟨598406, by rfl⟩ : syracuseStep 3191501 = 1196813) (by norm_num)
theorem B2127667 : Blo 1889435 2127667 := bstep (se 1 (by rfl) ⟨1595750, by rfl⟩ : syracuseStep 2127667 = 3191501) B3191501
theorem B2836889 : Blo 1889435 2836889 := bstep (se 2 (by rfl) ⟨1063833, by rfl⟩ : syracuseStep 2836889 = 2127667) B2127667
theorem B1891259 : Blo 1889435 1891259 := bstep (se 1 (by rfl) ⟨1418444, by rfl⟩ : syracuseStep 1891259 = 2836889) B2836889
theorem B1947289 : Blo 1889435 1947289 := bbase (se 2 (by rfl) ⟨730233, by rfl⟩ : syracuseStep 1947289 = 1460467) (by norm_num)
theorem B2596385 : Blo 1889435 2596385 := bstep (se 2 (by rfl) ⟨973644, by rfl⟩ : syracuseStep 2596385 = 1947289) B1947289
theorem B6923693 : Blo 1889435 6923693 := bstep (se 3 (by rfl) ⟨1298192, by rfl⟩ : syracuseStep 6923693 = 2596385) B2596385
theorem B4615795 : Blo 1889435 4615795 := bstep (se 1 (by rfl) ⟨3461846, by rfl⟩ : syracuseStep 4615795 = 6923693) B6923693
theorem B6154393 : Blo 1889435 6154393 := bstep (se 2 (by rfl) ⟨2307897, by rfl⟩ : syracuseStep 6154393 = 4615795) B4615795
theorem B8205857 : Blo 1889435 8205857 := bstep (se 2 (by rfl) ⟨3077196, by rfl⟩ : syracuseStep 8205857 = 6154393) B6154393
theorem B5470571 : Blo 1889435 5470571 := bstep (se 1 (by rfl) ⟨4102928, by rfl⟩ : syracuseStep 5470571 = 8205857) B8205857
theorem B3647047 : Blo 1889435 3647047 := bstep (se 1 (by rfl) ⟨2735285, by rfl⟩ : syracuseStep 3647047 = 5470571) B5470571
theorem B4862729 : Blo 1889435 4862729 := bstep (se 2 (by rfl) ⟨1823523, by rfl⟩ : syracuseStep 4862729 = 3647047) B3647047
theorem B3241819 : Blo 1889435 3241819 := bstep (se 1 (by rfl) ⟨2431364, by rfl⟩ : syracuseStep 3241819 = 4862729) B4862729
theorem B4322425 : Blo 1889435 4322425 := bstep (se 2 (by rfl) ⟨1620909, by rfl⟩ : syracuseStep 4322425 = 3241819) B3241819
theorem B5763233 : Blo 1889435 5763233 := bstep (se 2 (by rfl) ⟨2161212, by rfl⟩ : syracuseStep 5763233 = 4322425) B4322425
theorem B3842155 : Blo 1889435 3842155 := bstep (se 1 (by rfl) ⟨2881616, by rfl⟩ : syracuseStep 3842155 = 5763233) B5763233
theorem B5122873 : Blo 1889435 5122873 := bstep (se 2 (by rfl) ⟨1921077, by rfl⟩ : syracuseStep 5122873 = 3842155) B3842155
theorem B6830497 : Blo 1889435 6830497 := bstep (se 2 (by rfl) ⟨2561436, by rfl⟩ : syracuseStep 6830497 = 5122873) B5122873
theorem B9107329 : Blo 1889435 9107329 := bstep (se 2 (by rfl) ⟨3415248, by rfl⟩ : syracuseStep 9107329 = 6830497) B6830497
theorem B12143105 : Blo 1889435 12143105 := bstep (se 2 (by rfl) ⟨4553664, by rfl⟩ : syracuseStep 12143105 = 9107329) B9107329
theorem B8095403 : Blo 1889435 8095403 := bstep (se 1 (by rfl) ⟨6071552, by rfl⟩ : syracuseStep 8095403 = 12143105) B12143105
theorem B21587741 : Blo 1889435 21587741 := bstep (se 3 (by rfl) ⟨4047701, by rfl⟩ : syracuseStep 21587741 = 8095403) B8095403
theorem B14391827 : Blo 1889435 14391827 := bstep (se 1 (by rfl) ⟨10793870, by rfl⟩ : syracuseStep 14391827 = 21587741) B21587741
theorem B9594551 : Blo 1889435 9594551 := bstep (se 1 (by rfl) ⟨7195913, by rfl⟩ : syracuseStep 9594551 = 14391827) B14391827
theorem B6396367 : Blo 1889435 6396367 := bstep (se 1 (by rfl) ⟨4797275, by rfl⟩ : syracuseStep 6396367 = 9594551) B9594551
theorem B8528489 : Blo 1889435 8528489 := bstep (se 2 (by rfl) ⟨3198183, by rfl⟩ : syracuseStep 8528489 = 6396367) B6396367
theorem B5685659 : Blo 1889435 5685659 := bstep (se 1 (by rfl) ⟨4264244, by rfl⟩ : syracuseStep 5685659 = 8528489) B8528489
theorem B3790439 : Blo 1889435 3790439 := bstep (se 1 (by rfl) ⟨2842829, by rfl⟩ : syracuseStep 3790439 = 5685659) B5685659
theorem B2526959 : Blo 1889435 2526959 := bstep (se 1 (by rfl) ⟨1895219, by rfl⟩ : syracuseStep 2526959 = 3790439) B3790439
theorem B6738557 : Blo 1889435 6738557 := bstep (se 3 (by rfl) ⟨1263479, by rfl⟩ : syracuseStep 6738557 = 2526959) B2526959
theorem B71877941 : Blo 1889435 71877941 := bstep (se 5 (by rfl) ⟨3369278, by rfl⟩ : syracuseStep 71877941 = 6738557) B6738557
theorem B47918627 : Blo 1889435 47918627 := bstep (se 1 (by rfl) ⟨35938970, by rfl⟩ : syracuseStep 47918627 = 71877941) B71877941
theorem B31945751 : Blo 1889435 31945751 := bstep (se 1 (by rfl) ⟨23959313, by rfl⟩ : syracuseStep 31945751 = 47918627) B47918627
theorem B21297167 : Blo 1889435 21297167 := bstep (se 1 (by rfl) ⟨15972875, by rfl⟩ : syracuseStep 21297167 = 31945751) B31945751
theorem B14198111 : Blo 1889435 14198111 := bstep (se 1 (by rfl) ⟨10648583, by rfl⟩ : syracuseStep 14198111 = 21297167) B21297167
theorem B9465407 : Blo 1889435 9465407 := bstep (se 1 (by rfl) ⟨7099055, by rfl⟩ : syracuseStep 9465407 = 14198111) B14198111
theorem B6310271 : Blo 1889435 6310271 := bstep (se 1 (by rfl) ⟨4732703, by rfl⟩ : syracuseStep 6310271 = 9465407) B9465407
theorem B16827389 : Blo 1889435 16827389 := bstep (se 3 (by rfl) ⟨3155135, by rfl⟩ : syracuseStep 16827389 = 6310271) B6310271
theorem B11218259 : Blo 1889435 11218259 := bstep (se 1 (by rfl) ⟨8413694, by rfl⟩ : syracuseStep 11218259 = 16827389) B16827389
theorem B7478839 : Blo 1889435 7478839 := bstep (se 1 (by rfl) ⟨5609129, by rfl⟩ : syracuseStep 7478839 = 11218259) B11218259
theorem B9971785 : Blo 1889435 9971785 := bstep (se 2 (by rfl) ⟨3739419, by rfl⟩ : syracuseStep 9971785 = 7478839) B7478839
theorem B13295713 : Blo 1889435 13295713 := bstep (se 2 (by rfl) ⟨4985892, by rfl⟩ : syracuseStep 13295713 = 9971785) B9971785
theorem B17727617 : Blo 1889435 17727617 := bstep (se 2 (by rfl) ⟨6647856, by rfl⟩ : syracuseStep 17727617 = 13295713) B13295713
theorem B47273645 : Blo 1889435 47273645 := bstep (se 3 (by rfl) ⟨8863808, by rfl⟩ : syracuseStep 47273645 = 17727617) B17727617
theorem B31515763 : Blo 1889435 31515763 := bstep (se 1 (by rfl) ⟨23636822, by rfl⟩ : syracuseStep 31515763 = 47273645) B47273645
theorem B42021017 : Blo 1889435 42021017 := bstep (se 2 (by rfl) ⟨15757881, by rfl⟩ : syracuseStep 42021017 = 31515763) B31515763
theorem B28014011 : Blo 1889435 28014011 := bstep (se 1 (by rfl) ⟨21010508, by rfl⟩ : syracuseStep 28014011 = 42021017) B42021017
theorem B18676007 : Blo 1889435 18676007 := bstep (se 1 (by rfl) ⟨14007005, by rfl⟩ : syracuseStep 18676007 = 28014011) B28014011
theorem B12450671 : Blo 1889435 12450671 := bstep (se 1 (by rfl) ⟨9338003, by rfl⟩ : syracuseStep 12450671 = 18676007) B18676007
theorem B8300447 : Blo 1889435 8300447 := bstep (se 1 (by rfl) ⟨6225335, by rfl⟩ : syracuseStep 8300447 = 12450671) B12450671
theorem B5533631 : Blo 1889435 5533631 := bstep (se 1 (by rfl) ⟨4150223, by rfl⟩ : syracuseStep 5533631 = 8300447) B8300447
theorem B3689087 : Blo 1889435 3689087 := bstep (se 1 (by rfl) ⟨2766815, by rfl⟩ : syracuseStep 3689087 = 5533631) B5533631
theorem B39350261 : Blo 1889435 39350261 := bstep (se 5 (by rfl) ⟨1844543, by rfl⟩ : syracuseStep 39350261 = 3689087) B3689087
theorem B26233507 : Blo 1889435 26233507 := bstep (se 1 (by rfl) ⟨19675130, by rfl⟩ : syracuseStep 26233507 = 39350261) B39350261
theorem B34978009 : Blo 1889435 34978009 := bstep (se 2 (by rfl) ⟨13116753, by rfl⟩ : syracuseStep 34978009 = 26233507) B26233507
theorem B46637345 : Blo 1889435 46637345 := bstep (se 2 (by rfl) ⟨17489004, by rfl⟩ : syracuseStep 46637345 = 34978009) B34978009
theorem B31091563 : Blo 1889435 31091563 := bstep (se 1 (by rfl) ⟨23318672, by rfl⟩ : syracuseStep 31091563 = 46637345) B46637345
theorem B41455417 : Blo 1889435 41455417 := bstep (se 2 (by rfl) ⟨15545781, by rfl⟩ : syracuseStep 41455417 = 31091563) B31091563
theorem B55273889 : Blo 1889435 55273889 := bstep (se 2 (by rfl) ⟨20727708, by rfl⟩ : syracuseStep 55273889 = 41455417) B41455417
theorem B36849259 : Blo 1889435 36849259 := bstep (se 1 (by rfl) ⟨27636944, by rfl⟩ : syracuseStep 36849259 = 55273889) B55273889
theorem B49132345 : Blo 1889435 49132345 := bstep (se 2 (by rfl) ⟨18424629, by rfl⟩ : syracuseStep 49132345 = 36849259) B36849259
theorem B65509793 : Blo 1889435 65509793 := bstep (se 2 (by rfl) ⟨24566172, by rfl⟩ : syracuseStep 65509793 = 49132345) B49132345
theorem B43673195 : Blo 1889435 43673195 := bstep (se 1 (by rfl) ⟨32754896, by rfl⟩ : syracuseStep 43673195 = 65509793) B65509793
theorem B29115463 : Blo 1889435 29115463 := bstep (se 1 (by rfl) ⟨21836597, by rfl⟩ : syracuseStep 29115463 = 43673195) B43673195
theorem B38820617 : Blo 1889435 38820617 := bstep (se 2 (by rfl) ⟨14557731, by rfl⟩ : syracuseStep 38820617 = 29115463) B29115463
theorem B25880411 : Blo 1889435 25880411 := bstep (se 1 (by rfl) ⟨19410308, by rfl⟩ : syracuseStep 25880411 = 38820617) B38820617
theorem B17253607 : Blo 1889435 17253607 := bstep (se 1 (by rfl) ⟨12940205, by rfl⟩ : syracuseStep 17253607 = 25880411) B25880411
theorem B23004809 : Blo 1889435 23004809 := bstep (se 2 (by rfl) ⟨8626803, by rfl⟩ : syracuseStep 23004809 = 17253607) B17253607
theorem B15336539 : Blo 1889435 15336539 := bstep (se 1 (by rfl) ⟨11502404, by rfl⟩ : syracuseStep 15336539 = 23004809) B23004809
theorem B10224359 : Blo 1889435 10224359 := bstep (se 1 (by rfl) ⟨7668269, by rfl⟩ : syracuseStep 10224359 = 15336539) B15336539
theorem B6816239 : Blo 1889435 6816239 := bstep (se 1 (by rfl) ⟨5112179, by rfl⟩ : syracuseStep 6816239 = 10224359) B10224359
theorem B4544159 : Blo 1889435 4544159 := bstep (se 1 (by rfl) ⟨3408119, by rfl⟩ : syracuseStep 4544159 = 6816239) B6816239
theorem B12117757 : Blo 1889435 12117757 := bstep (se 3 (by rfl) ⟨2272079, by rfl⟩ : syracuseStep 12117757 = 4544159) B4544159
theorem B16157009 : Blo 1889435 16157009 := bstep (se 2 (by rfl) ⟨6058878, by rfl⟩ : syracuseStep 16157009 = 12117757) B12117757
theorem B10771339 : Blo 1889435 10771339 := bstep (se 1 (by rfl) ⟨8078504, by rfl⟩ : syracuseStep 10771339 = 16157009) B16157009
theorem B14361785 : Blo 1889435 14361785 := bstep (se 2 (by rfl) ⟨5385669, by rfl⟩ : syracuseStep 14361785 = 10771339) B10771339
theorem B9574523 : Blo 1889435 9574523 := bstep (se 1 (by rfl) ⟨7180892, by rfl⟩ : syracuseStep 9574523 = 14361785) B14361785
theorem B6383015 : Blo 1889435 6383015 := bstep (se 1 (by rfl) ⟨4787261, by rfl⟩ : syracuseStep 6383015 = 9574523) B9574523
theorem B4255343 : Blo 1889435 4255343 := bstep (se 1 (by rfl) ⟨3191507, by rfl⟩ : syracuseStep 4255343 = 6383015) B6383015
theorem B2836895 : Blo 1889435 2836895 := bstep (se 1 (by rfl) ⟨2127671, by rfl⟩ : syracuseStep 2836895 = 4255343) B4255343
theorem B1891263 : Blo 1889435 1891263 := bstep (se 1 (by rfl) ⟨1418447, by rfl⟩ : syracuseStep 1891263 = 2836895) B2836895
theorem B2836901 : Blo 1889435 2836901 := bbase (se 4 (by rfl) ⟨265959, by rfl⟩ : syracuseStep 2836901 = 531919) (by norm_num)
theorem B1891267 : Blo 1889435 1891267 := bstep (se 1 (by rfl) ⟨1418450, by rfl⟩ : syracuseStep 1891267 = 2836901) B2836901
theorem B2393641 : Blo 1889435 2393641 := bbase (se 2 (by rfl) ⟨897615, by rfl⟩ : syracuseStep 2393641 = 1795231) (by norm_num)
theorem B3191521 : Blo 1889435 3191521 := bstep (se 2 (by rfl) ⟨1196820, by rfl⟩ : syracuseStep 3191521 = 2393641) B2393641
theorem B4255361 : Blo 1889435 4255361 := bstep (se 2 (by rfl) ⟨1595760, by rfl⟩ : syracuseStep 4255361 = 3191521) B3191521
theorem B2836907 : Blo 1889435 2836907 := bstep (se 1 (by rfl) ⟨2127680, by rfl⟩ : syracuseStep 2836907 = 4255361) B4255361
theorem B1891271 : Blo 1889435 1891271 := bstep (se 1 (by rfl) ⟨1418453, by rfl⟩ : syracuseStep 1891271 = 2836907) B2836907
theorem B2127685 : Blo 1889435 2127685 := bbase (se 4 (by rfl) ⟨199470, by rfl⟩ : syracuseStep 2127685 = 398941) (by norm_num)
theorem B2836913 : Blo 1889435 2836913 := bstep (se 2 (by rfl) ⟨1063842, by rfl⟩ : syracuseStep 2836913 = 2127685) B2127685
theorem B1891275 : Blo 1889435 1891275 := bstep (se 1 (by rfl) ⟨1418456, by rfl⟩ : syracuseStep 1891275 = 2836913) B2836913
theorem B3590477 : Blo 1889435 3590477 := bbase (se 3 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 3590477 = 1346429) (by norm_num)
theorem B2393651 : Blo 1889435 2393651 := bstep (se 1 (by rfl) ⟨1795238, by rfl⟩ : syracuseStep 2393651 = 3590477) B3590477
theorem B6383069 : Blo 1889435 6383069 := bstep (se 3 (by rfl) ⟨1196825, by rfl⟩ : syracuseStep 6383069 = 2393651) B2393651
theorem B4255379 : Blo 1889435 4255379 := bstep (se 1 (by rfl) ⟨3191534, by rfl⟩ : syracuseStep 4255379 = 6383069) B6383069
theorem B2836919 : Blo 1889435 2836919 := bstep (se 1 (by rfl) ⟨2127689, by rfl⟩ : syracuseStep 2836919 = 4255379) B4255379
theorem B1891279 : Blo 1889435 1891279 := bstep (se 1 (by rfl) ⟨1418459, by rfl⟩ : syracuseStep 1891279 = 2836919) B2836919
theorem B2836925 : Blo 1889435 2836925 := bbase (se 3 (by rfl) ⟨531923, by rfl⟩ : syracuseStep 2836925 = 1063847) (by norm_num)
theorem B1891283 : Blo 1889435 1891283 := bstep (se 1 (by rfl) ⟨1418462, by rfl⟩ : syracuseStep 1891283 = 2836925) B2836925
theorem B4255397 : Blo 1889435 4255397 := bbase (se 4 (by rfl) ⟨398943, by rfl⟩ : syracuseStep 4255397 = 797887) (by norm_num)
theorem B2836931 : Blo 1889435 2836931 := bstep (se 1 (by rfl) ⟨2127698, by rfl⟩ : syracuseStep 2836931 = 4255397) B4255397
theorem B1891287 : Blo 1889435 1891287 := bstep (se 1 (by rfl) ⟨1418465, by rfl⟩ : syracuseStep 1891287 = 2836931) B2836931
theorem B4787333 : Blo 1889435 4787333 := bbase (se 4 (by rfl) ⟨448812, by rfl⟩ : syracuseStep 4787333 = 897625) (by norm_num)
theorem B3191555 : Blo 1889435 3191555 := bstep (se 1 (by rfl) ⟨2393666, by rfl⟩ : syracuseStep 3191555 = 4787333) B4787333
theorem B2127703 : Blo 1889435 2127703 := bstep (se 1 (by rfl) ⟨1595777, by rfl⟩ : syracuseStep 2127703 = 3191555) B3191555
theorem B2836937 : Blo 1889435 2836937 := bstep (se 2 (by rfl) ⟨1063851, by rfl⟩ : syracuseStep 2836937 = 2127703) B2127703
theorem B1891291 : Blo 1889435 1891291 := bstep (se 1 (by rfl) ⟨1418468, by rfl⟩ : syracuseStep 1891291 = 2836937) B2836937
theorem B4544237 : Blo 1889435 4544237 := bbase (se 3 (by rfl) ⟨852044, by rfl⟩ : syracuseStep 4544237 = 1704089) (by norm_num)
theorem B3029491 : Blo 1889435 3029491 := bstep (se 1 (by rfl) ⟨2272118, by rfl⟩ : syracuseStep 3029491 = 4544237) B4544237
theorem B4039321 : Blo 1889435 4039321 := bstep (se 2 (by rfl) ⟨1514745, by rfl⟩ : syracuseStep 4039321 = 3029491) B3029491
theorem B5385761 : Blo 1889435 5385761 := bstep (se 2 (by rfl) ⟨2019660, by rfl⟩ : syracuseStep 5385761 = 4039321) B4039321
theorem B3590507 : Blo 1889435 3590507 := bstep (se 1 (by rfl) ⟨2692880, by rfl⟩ : syracuseStep 3590507 = 5385761) B5385761
theorem B9574685 : Blo 1889435 9574685 := bstep (se 3 (by rfl) ⟨1795253, by rfl⟩ : syracuseStep 9574685 = 3590507) B3590507
theorem B6383123 : Blo 1889435 6383123 := bstep (se 1 (by rfl) ⟨4787342, by rfl⟩ : syracuseStep 6383123 = 9574685) B9574685
theorem B4255415 : Blo 1889435 4255415 := bstep (se 1 (by rfl) ⟨3191561, by rfl⟩ : syracuseStep 4255415 = 6383123) B6383123
theorem B2836943 : Blo 1889435 2836943 := bstep (se 1 (by rfl) ⟨2127707, by rfl⟩ : syracuseStep 2836943 = 4255415) B4255415
theorem B1891295 : Blo 1889435 1891295 := bstep (se 1 (by rfl) ⟨1418471, by rfl⟩ : syracuseStep 1891295 = 2836943) B2836943
theorem B2836949 : Blo 1889435 2836949 := bbase (se 7 (by rfl) ⟨33245, by rfl⟩ : syracuseStep 2836949 = 66491) (by norm_num)
theorem B1891299 : Blo 1889435 1891299 := bstep (se 1 (by rfl) ⟨1418474, by rfl⟩ : syracuseStep 1891299 = 2836949) B2836949
theorem B7181045 : Blo 1889435 7181045 := bbase (se 5 (by rfl) ⟨336611, by rfl⟩ : syracuseStep 7181045 = 673223) (by norm_num)
theorem B4787363 : Blo 1889435 4787363 := bstep (se 1 (by rfl) ⟨3590522, by rfl⟩ : syracuseStep 4787363 = 7181045) B7181045
theorem B3191575 : Blo 1889435 3191575 := bstep (se 1 (by rfl) ⟨2393681, by rfl⟩ : syracuseStep 3191575 = 4787363) B4787363
theorem B4255433 : Blo 1889435 4255433 := bstep (se 2 (by rfl) ⟨1595787, by rfl⟩ : syracuseStep 4255433 = 3191575) B3191575
theorem B2836955 : Blo 1889435 2836955 := bstep (se 1 (by rfl) ⟨2127716, by rfl⟩ : syracuseStep 2836955 = 4255433) B4255433
theorem B1891303 : Blo 1889435 1891303 := bstep (se 1 (by rfl) ⟨1418477, by rfl⟩ : syracuseStep 1891303 = 2836955) B2836955
theorem B2127721 : Blo 1889435 2127721 := bbase (se 2 (by rfl) ⟨797895, by rfl⟩ : syracuseStep 2127721 = 1595791) (by norm_num)
theorem B2836961 : Blo 1889435 2836961 := bstep (se 2 (by rfl) ⟨1063860, by rfl⟩ : syracuseStep 2836961 = 2127721) B2127721
theorem B1891307 : Blo 1889435 1891307 := bstep (se 1 (by rfl) ⟨1418480, by rfl⟩ : syracuseStep 1891307 = 2836961) B2836961
theorem B5909365 : Blo 1889435 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B7879153 : Blo 1889435 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B10505537 : Blo 1889435 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B7003691 : Blo 1889435 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B4669127 : Blo 1889435 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B3112751 : Blo 1889435 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B2075167 : Blo 1889435 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B2766889 : Blo 1889435 2766889 := bstep (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) B2075167
theorem B3689185 : Blo 1889435 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B4918913 : Blo 1889435 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B3279275 : Blo 1889435 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B2186183 : Blo 1889435 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B5829821 : Blo 1889435 5829821 := bstep (se 3 (by rfl) ⟨1093091, by rfl⟩ : syracuseStep 5829821 = 2186183) B2186183
theorem B3886547 : Blo 1889435 3886547 := bstep (se 1 (by rfl) ⟨2914910, by rfl⟩ : syracuseStep 3886547 = 5829821) B5829821
theorem B10364125 : Blo 1889435 10364125 := bstep (se 3 (by rfl) ⟨1943273, by rfl⟩ : syracuseStep 10364125 = 3886547) B3886547
theorem B13818833 : Blo 1889435 13818833 := bstep (se 2 (by rfl) ⟨5182062, by rfl⟩ : syracuseStep 13818833 = 10364125) B10364125
theorem B9212555 : Blo 1889435 9212555 := bstep (se 1 (by rfl) ⟨6909416, by rfl⟩ : syracuseStep 9212555 = 13818833) B13818833
theorem B24566813 : Blo 1889435 24566813 := bstep (se 3 (by rfl) ⟨4606277, by rfl⟩ : syracuseStep 24566813 = 9212555) B9212555
theorem B16377875 : Blo 1889435 16377875 := bstep (se 1 (by rfl) ⟨12283406, by rfl⟩ : syracuseStep 16377875 = 24566813) B24566813
theorem B10918583 : Blo 1889435 10918583 := bstep (se 1 (by rfl) ⟨8188937, by rfl⟩ : syracuseStep 10918583 = 16377875) B16377875
theorem B7279055 : Blo 1889435 7279055 := bstep (se 1 (by rfl) ⟨5459291, by rfl⟩ : syracuseStep 7279055 = 10918583) B10918583
theorem B4852703 : Blo 1889435 4852703 := bstep (se 1 (by rfl) ⟨3639527, by rfl⟩ : syracuseStep 4852703 = 7279055) B7279055
theorem B3235135 : Blo 1889435 3235135 := bstep (se 1 (by rfl) ⟨2426351, by rfl⟩ : syracuseStep 3235135 = 4852703) B4852703
theorem B4313513 : Blo 1889435 4313513 := bstep (se 2 (by rfl) ⟨1617567, by rfl⟩ : syracuseStep 4313513 = 3235135) B3235135
theorem B2875675 : Blo 1889435 2875675 := bstep (se 1 (by rfl) ⟨2156756, by rfl⟩ : syracuseStep 2875675 = 4313513) B4313513
theorem B3834233 : Blo 1889435 3834233 := bstep (se 2 (by rfl) ⟨1437837, by rfl⟩ : syracuseStep 3834233 = 2875675) B2875675
theorem B2556155 : Blo 1889435 2556155 := bstep (se 1 (by rfl) ⟨1917116, by rfl⟩ : syracuseStep 2556155 = 3834233) B3834233
theorem B6816413 : Blo 1889435 6816413 := bstep (se 3 (by rfl) ⟨1278077, by rfl⟩ : syracuseStep 6816413 = 2556155) B2556155
theorem B4544275 : Blo 1889435 4544275 := bstep (se 1 (by rfl) ⟨3408206, by rfl⟩ : syracuseStep 4544275 = 6816413) B6816413
theorem B6059033 : Blo 1889435 6059033 := bstep (se 2 (by rfl) ⟨2272137, by rfl⟩ : syracuseStep 6059033 = 4544275) B4544275
theorem B4039355 : Blo 1889435 4039355 := bstep (se 1 (by rfl) ⟨3029516, by rfl⟩ : syracuseStep 4039355 = 6059033) B6059033
theorem B10771613 : Blo 1889435 10771613 := bstep (se 3 (by rfl) ⟨2019677, by rfl⟩ : syracuseStep 10771613 = 4039355) B4039355
theorem B7181075 : Blo 1889435 7181075 := bstep (se 1 (by rfl) ⟨5385806, by rfl⟩ : syracuseStep 7181075 = 10771613) B10771613
theorem B4787383 : Blo 1889435 4787383 := bstep (se 1 (by rfl) ⟨3590537, by rfl⟩ : syracuseStep 4787383 = 7181075) B7181075
theorem B6383177 : Blo 1889435 6383177 := bstep (se 2 (by rfl) ⟨2393691, by rfl⟩ : syracuseStep 6383177 = 4787383) B4787383
theorem B4255451 : Blo 1889435 4255451 := bstep (se 1 (by rfl) ⟨3191588, by rfl⟩ : syracuseStep 4255451 = 6383177) B6383177
theorem B2836967 : Blo 1889435 2836967 := bstep (se 1 (by rfl) ⟨2127725, by rfl⟩ : syracuseStep 2836967 = 4255451) B4255451
theorem B1891311 : Blo 1889435 1891311 := bstep (se 1 (by rfl) ⟨1418483, by rfl⟩ : syracuseStep 1891311 = 2836967) B2836967
theorem B2836973 : Blo 1889435 2836973 := bbase (se 3 (by rfl) ⟨531932, by rfl⟩ : syracuseStep 2836973 = 1063865) (by norm_num)
theorem B1891315 : Blo 1889435 1891315 := bstep (se 1 (by rfl) ⟨1418486, by rfl⟩ : syracuseStep 1891315 = 2836973) B2836973
theorem B4255469 : Blo 1889435 4255469 := bbase (se 3 (by rfl) ⟨797900, by rfl⟩ : syracuseStep 4255469 = 1595801) (by norm_num)
theorem B2836979 : Blo 1889435 2836979 := bstep (se 1 (by rfl) ⟨2127734, by rfl⟩ : syracuseStep 2836979 = 4255469) B4255469
theorem B1891319 : Blo 1889435 1891319 := bstep (se 1 (by rfl) ⟨1418489, by rfl⟩ : syracuseStep 1891319 = 2836979) B2836979
theorem B2272153 : Blo 1889435 2272153 := bbase (se 2 (by rfl) ⟨852057, by rfl⟩ : syracuseStep 2272153 = 1704115) (by norm_num)
theorem B3029537 : Blo 1889435 3029537 := bstep (se 2 (by rfl) ⟨1136076, by rfl⟩ : syracuseStep 3029537 = 2272153) B2272153
theorem B2019691 : Blo 1889435 2019691 := bstep (se 1 (by rfl) ⟨1514768, by rfl⟩ : syracuseStep 2019691 = 3029537) B3029537
theorem B2692921 : Blo 1889435 2692921 := bstep (se 2 (by rfl) ⟨1009845, by rfl⟩ : syracuseStep 2692921 = 2019691) B2019691
theorem B3590561 : Blo 1889435 3590561 := bstep (se 2 (by rfl) ⟨1346460, by rfl⟩ : syracuseStep 3590561 = 2692921) B2692921
theorem B2393707 : Blo 1889435 2393707 := bstep (se 1 (by rfl) ⟨1795280, by rfl⟩ : syracuseStep 2393707 = 3590561) B3590561
theorem B3191609 : Blo 1889435 3191609 := bstep (se 2 (by rfl) ⟨1196853, by rfl⟩ : syracuseStep 3191609 = 2393707) B2393707
theorem B2127739 : Blo 1889435 2127739 := bstep (se 1 (by rfl) ⟨1595804, by rfl⟩ : syracuseStep 2127739 = 3191609) B3191609
theorem B2836985 : Blo 1889435 2836985 := bstep (se 2 (by rfl) ⟨1063869, by rfl⟩ : syracuseStep 2836985 = 2127739) B2127739
theorem B1891323 : Blo 1889435 1891323 := bstep (se 1 (by rfl) ⟨1418492, by rfl⟩ : syracuseStep 1891323 = 2836985) B2836985
theorem B4918949 : Blo 1889435 4918949 := bbase (se 4 (by rfl) ⟨461151, by rfl⟩ : syracuseStep 4918949 = 922303) (by norm_num)
theorem B3279299 : Blo 1889435 3279299 := bstep (se 1 (by rfl) ⟨2459474, by rfl⟩ : syracuseStep 3279299 = 4918949) B4918949
theorem B8744797 : Blo 1889435 8744797 := bstep (se 3 (by rfl) ⟨1639649, by rfl⟩ : syracuseStep 8744797 = 3279299) B3279299
theorem B11659729 : Blo 1889435 11659729 := bstep (se 2 (by rfl) ⟨4372398, by rfl⟩ : syracuseStep 11659729 = 8744797) B8744797
theorem B15546305 : Blo 1889435 15546305 := bstep (se 2 (by rfl) ⟨5829864, by rfl⟩ : syracuseStep 15546305 = 11659729) B11659729
theorem B10364203 : Blo 1889435 10364203 := bstep (se 1 (by rfl) ⟨7773152, by rfl⟩ : syracuseStep 10364203 = 15546305) B15546305
theorem B13818937 : Blo 1889435 13818937 := bstep (se 2 (by rfl) ⟨5182101, by rfl⟩ : syracuseStep 13818937 = 10364203) B10364203
theorem B18425249 : Blo 1889435 18425249 := bstep (se 2 (by rfl) ⟨6909468, by rfl⟩ : syracuseStep 18425249 = 13818937) B13818937
theorem B12283499 : Blo 1889435 12283499 := bstep (se 1 (by rfl) ⟨9212624, by rfl⟩ : syracuseStep 12283499 = 18425249) B18425249
theorem B32755997 : Blo 1889435 32755997 := bstep (se 3 (by rfl) ⟨6141749, by rfl⟩ : syracuseStep 32755997 = 12283499) B12283499
theorem B21837331 : Blo 1889435 21837331 := bstep (se 1 (by rfl) ⟨16377998, by rfl⟩ : syracuseStep 21837331 = 32755997) B32755997
theorem B29116441 : Blo 1889435 29116441 := bstep (se 2 (by rfl) ⟨10918665, by rfl⟩ : syracuseStep 29116441 = 21837331) B21837331
theorem B155287685 : Blo 1889435 155287685 := bstep (se 4 (by rfl) ⟨14558220, by rfl⟩ : syracuseStep 155287685 = 29116441) B29116441
theorem B103525123 : Blo 1889435 103525123 := bstep (se 1 (by rfl) ⟨77643842, by rfl⟩ : syracuseStep 103525123 = 155287685) B155287685
theorem B138033497 : Blo 1889435 138033497 := bstep (se 2 (by rfl) ⟨51762561, by rfl⟩ : syracuseStep 138033497 = 103525123) B103525123
theorem B92022331 : Blo 1889435 92022331 := bstep (se 1 (by rfl) ⟨69016748, by rfl⟩ : syracuseStep 92022331 = 138033497) B138033497
theorem B122696441 : Blo 1889435 122696441 := bstep (se 2 (by rfl) ⟨46011165, by rfl⟩ : syracuseStep 122696441 = 92022331) B92022331
theorem B81797627 : Blo 1889435 81797627 := bstep (se 1 (by rfl) ⟨61348220, by rfl⟩ : syracuseStep 81797627 = 122696441) B122696441
theorem B54531751 : Blo 1889435 54531751 := bstep (se 1 (by rfl) ⟨40898813, by rfl⟩ : syracuseStep 54531751 = 81797627) B81797627
theorem B72709001 : Blo 1889435 72709001 := bstep (se 2 (by rfl) ⟨27265875, by rfl⟩ : syracuseStep 72709001 = 54531751) B54531751
theorem B48472667 : Blo 1889435 48472667 := bstep (se 1 (by rfl) ⟨36354500, by rfl⟩ : syracuseStep 48472667 = 72709001) B72709001
theorem B32315111 : Blo 1889435 32315111 := bstep (se 1 (by rfl) ⟨24236333, by rfl⟩ : syracuseStep 32315111 = 48472667) B48472667
theorem B21543407 : Blo 1889435 21543407 := bstep (se 1 (by rfl) ⟨16157555, by rfl⟩ : syracuseStep 21543407 = 32315111) B32315111
theorem B14362271 : Blo 1889435 14362271 := bstep (se 1 (by rfl) ⟨10771703, by rfl⟩ : syracuseStep 14362271 = 21543407) B21543407
theorem B9574847 : Blo 1889435 9574847 := bstep (se 1 (by rfl) ⟨7181135, by rfl⟩ : syracuseStep 9574847 = 14362271) B14362271
theorem B6383231 : Blo 1889435 6383231 := bstep (se 1 (by rfl) ⟨4787423, by rfl⟩ : syracuseStep 6383231 = 9574847) B9574847
theorem B4255487 : Blo 1889435 4255487 := bstep (se 1 (by rfl) ⟨3191615, by rfl⟩ : syracuseStep 4255487 = 6383231) B6383231
theorem B2836991 : Blo 1889435 2836991 := bstep (se 1 (by rfl) ⟨2127743, by rfl⟩ : syracuseStep 2836991 = 4255487) B4255487
theorem B1891327 : Blo 1889435 1891327 := bstep (se 1 (by rfl) ⟨1418495, by rfl⟩ : syracuseStep 1891327 = 2836991) B2836991
theorem B2836997 : Blo 1889435 2836997 := bbase (se 4 (by rfl) ⟨265968, by rfl⟩ : syracuseStep 2836997 = 531937) (by norm_num)
theorem B1891331 : Blo 1889435 1891331 := bstep (se 1 (by rfl) ⟨1418498, by rfl⟩ : syracuseStep 1891331 = 2836997) B2836997
theorem B3191629 : Blo 1889435 3191629 := bbase (se 3 (by rfl) ⟨598430, by rfl⟩ : syracuseStep 3191629 = 1196861) (by norm_num)
theorem B4255505 : Blo 1889435 4255505 := bstep (se 2 (by rfl) ⟨1595814, by rfl⟩ : syracuseStep 4255505 = 3191629) B3191629
theorem B2837003 : Blo 1889435 2837003 := bstep (se 1 (by rfl) ⟨2127752, by rfl⟩ : syracuseStep 2837003 = 4255505) B4255505
theorem B1891335 : Blo 1889435 1891335 := bstep (se 1 (by rfl) ⟨1418501, by rfl⟩ : syracuseStep 1891335 = 2837003) B2837003
theorem B2127757 : Blo 1889435 2127757 := bbase (se 3 (by rfl) ⟨398954, by rfl⟩ : syracuseStep 2127757 = 797909) (by norm_num)
theorem B2837009 : Blo 1889435 2837009 := bstep (se 2 (by rfl) ⟨1063878, by rfl⟩ : syracuseStep 2837009 = 2127757) B2127757
theorem B1891339 : Blo 1889435 1891339 := bstep (se 1 (by rfl) ⟨1418504, by rfl⟩ : syracuseStep 1891339 = 2837009) B2837009
theorem B6383285 : Blo 1889435 6383285 := bbase (se 5 (by rfl) ⟨299216, by rfl⟩ : syracuseStep 6383285 = 598433) (by norm_num)
theorem B4255523 : Blo 1889435 4255523 := bstep (se 1 (by rfl) ⟨3191642, by rfl⟩ : syracuseStep 4255523 = 6383285) B6383285
theorem B2837015 : Blo 1889435 2837015 := bstep (se 1 (by rfl) ⟨2127761, by rfl⟩ : syracuseStep 2837015 = 4255523) B4255523
theorem B1891343 : Blo 1889435 1891343 := bstep (se 1 (by rfl) ⟨1418507, by rfl⟩ : syracuseStep 1891343 = 2837015) B2837015
theorem B2837021 : Blo 1889435 2837021 := bbase (se 3 (by rfl) ⟨531941, by rfl⟩ : syracuseStep 2837021 = 1063883) (by norm_num)
theorem B1891347 : Blo 1889435 1891347 := bstep (se 1 (by rfl) ⟨1418510, by rfl⟩ : syracuseStep 1891347 = 2837021) B2837021
theorem B4255541 : Blo 1889435 4255541 := bbase (se 5 (by rfl) ⟨199478, by rfl⟩ : syracuseStep 4255541 = 398957) (by norm_num)
theorem B2837027 : Blo 1889435 2837027 := bstep (se 1 (by rfl) ⟨2127770, by rfl⟩ : syracuseStep 2837027 = 4255541) B4255541
theorem B1891351 : Blo 1889435 1891351 := bstep (se 1 (by rfl) ⟨1418513, by rfl⟩ : syracuseStep 1891351 = 2837027) B2837027
theorem B4544381 : Blo 1889435 4544381 := bbase (se 3 (by rfl) ⟨852071, by rfl⟩ : syracuseStep 4544381 = 1704143) (by norm_num)
theorem B12118349 : Blo 1889435 12118349 := bstep (se 3 (by rfl) ⟨2272190, by rfl⟩ : syracuseStep 12118349 = 4544381) B4544381
theorem B8078899 : Blo 1889435 8078899 := bstep (se 1 (by rfl) ⟨6059174, by rfl⟩ : syracuseStep 8078899 = 12118349) B12118349
theorem B10771865 : Blo 1889435 10771865 := bstep (se 2 (by rfl) ⟨4039449, by rfl⟩ : syracuseStep 10771865 = 8078899) B8078899
theorem B7181243 : Blo 1889435 7181243 := bstep (se 1 (by rfl) ⟨5385932, by rfl⟩ : syracuseStep 7181243 = 10771865) B10771865
theorem B4787495 : Blo 1889435 4787495 := bstep (se 1 (by rfl) ⟨3590621, by rfl⟩ : syracuseStep 4787495 = 7181243) B7181243
theorem B3191663 : Blo 1889435 3191663 := bstep (se 1 (by rfl) ⟨2393747, by rfl⟩ : syracuseStep 3191663 = 4787495) B4787495
theorem B2127775 : Blo 1889435 2127775 := bstep (se 1 (by rfl) ⟨1595831, by rfl⟩ : syracuseStep 2127775 = 3191663) B3191663
theorem B2837033 : Blo 1889435 2837033 := bstep (se 2 (by rfl) ⟨1063887, by rfl⟩ : syracuseStep 2837033 = 2127775) B2127775
theorem B1891355 : Blo 1889435 1891355 := bstep (se 1 (by rfl) ⟨1418516, by rfl⟩ : syracuseStep 1891355 = 2837033) B2837033
theorem B3408293 : Blo 1889435 3408293 := bbase (se 4 (by rfl) ⟨319527, by rfl⟩ : syracuseStep 3408293 = 639055) (by norm_num)
theorem B2272195 : Blo 1889435 2272195 := bstep (se 1 (by rfl) ⟨1704146, by rfl⟩ : syracuseStep 2272195 = 3408293) B3408293
theorem B12118373 : Blo 1889435 12118373 := bstep (se 4 (by rfl) ⟨1136097, by rfl⟩ : syracuseStep 12118373 = 2272195) B2272195
theorem B8078915 : Blo 1889435 8078915 := bstep (se 1 (by rfl) ⟨6059186, by rfl⟩ : syracuseStep 8078915 = 12118373) B12118373
theorem B5385943 : Blo 1889435 5385943 := bstep (se 1 (by rfl) ⟨4039457, by rfl⟩ : syracuseStep 5385943 = 8078915) B8078915
theorem B7181257 : Blo 1889435 7181257 := bstep (se 2 (by rfl) ⟨2692971, by rfl⟩ : syracuseStep 7181257 = 5385943) B5385943
theorem B9575009 : Blo 1889435 9575009 := bstep (se 2 (by rfl) ⟨3590628, by rfl⟩ : syracuseStep 9575009 = 7181257) B7181257
theorem B6383339 : Blo 1889435 6383339 := bstep (se 1 (by rfl) ⟨4787504, by rfl⟩ : syracuseStep 6383339 = 9575009) B9575009
theorem B4255559 : Blo 1889435 4255559 := bstep (se 1 (by rfl) ⟨3191669, by rfl⟩ : syracuseStep 4255559 = 6383339) B6383339
theorem B2837039 : Blo 1889435 2837039 := bstep (se 1 (by rfl) ⟨2127779, by rfl⟩ : syracuseStep 2837039 = 4255559) B4255559
theorem B1891359 : Blo 1889435 1891359 := bstep (se 1 (by rfl) ⟨1418519, by rfl⟩ : syracuseStep 1891359 = 2837039) B2837039
theorem B2837045 : Blo 1889435 2837045 := bbase (se 5 (by rfl) ⟨132986, by rfl⟩ : syracuseStep 2837045 = 265973) (by norm_num)
theorem B1891363 : Blo 1889435 1891363 := bstep (se 1 (by rfl) ⟨1418522, by rfl⟩ : syracuseStep 1891363 = 2837045) B2837045
theorem B4787525 : Blo 1889435 4787525 := bbase (se 4 (by rfl) ⟨448830, by rfl⟩ : syracuseStep 4787525 = 897661) (by norm_num)
theorem B3191683 : Blo 1889435 3191683 := bstep (se 1 (by rfl) ⟨2393762, by rfl⟩ : syracuseStep 3191683 = 4787525) B4787525
theorem B4255577 : Blo 1889435 4255577 := bstep (se 2 (by rfl) ⟨1595841, by rfl⟩ : syracuseStep 4255577 = 3191683) B3191683
theorem B2837051 : Blo 1889435 2837051 := bstep (se 1 (by rfl) ⟨2127788, by rfl⟩ : syracuseStep 2837051 = 4255577) B4255577
theorem B1891367 : Blo 1889435 1891367 := bstep (se 1 (by rfl) ⟨1418525, by rfl⟩ : syracuseStep 1891367 = 2837051) B2837051
theorem B2127793 : Blo 1889435 2127793 := bbase (se 2 (by rfl) ⟨797922, by rfl⟩ : syracuseStep 2127793 = 1595845) (by norm_num)
theorem B2837057 : Blo 1889435 2837057 := bstep (se 2 (by rfl) ⟨1063896, by rfl⟩ : syracuseStep 2837057 = 2127793) B2127793
theorem B1891371 : Blo 1889435 1891371 := bstep (se 1 (by rfl) ⟨1418528, by rfl⟩ : syracuseStep 1891371 = 2837057) B2837057
theorem B5385989 : Blo 1889435 5385989 := bbase (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) (by norm_num)
theorem B3590659 : Blo 1889435 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B4787545 : Blo 1889435 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B6383393 : Blo 1889435 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B4255595 : Blo 1889435 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B2837063 : Blo 1889435 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B1891375 : Blo 1889435 1891375 := bstep (se 1 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 1891375 = 2837063) B2837063
theorem B2837069 : Blo 1889435 2837069 := bbase (se 3 (by rfl) ⟨531950, by rfl⟩ : syracuseStep 2837069 = 1063901) (by norm_num)
theorem B1891379 : Blo 1889435 1891379 := bstep (se 1 (by rfl) ⟨1418534, by rfl⟩ : syracuseStep 1891379 = 2837069) B2837069
theorem B4255613 : Blo 1889435 4255613 := bbase (se 3 (by rfl) ⟨797927, by rfl⟩ : syracuseStep 4255613 = 1595855) (by norm_num)
theorem B2837075 : Blo 1889435 2837075 := bstep (se 1 (by rfl) ⟨2127806, by rfl⟩ : syracuseStep 2837075 = 4255613) B4255613
theorem B1891383 : Blo 1889435 1891383 := bstep (se 1 (by rfl) ⟨1418537, by rfl⟩ : syracuseStep 1891383 = 2837075) B2837075
theorem B3191717 : Blo 1889435 3191717 := bbase (se 4 (by rfl) ⟨299223, by rfl⟩ : syracuseStep 3191717 = 598447) (by norm_num)
theorem B2127811 : Blo 1889435 2127811 := bstep (se 1 (by rfl) ⟨1595858, by rfl⟩ : syracuseStep 2127811 = 3191717) B3191717
theorem B2837081 : Blo 1889435 2837081 := bstep (se 2 (by rfl) ⟨1063905, by rfl⟩ : syracuseStep 2837081 = 2127811) B2127811
theorem B1891387 : Blo 1889435 1891387 := bstep (se 1 (by rfl) ⟨1418540, by rfl⟩ : syracuseStep 1891387 = 2837081) B2837081
theorem B3029645 : Blo 1889435 3029645 := bbase (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) (by norm_num)
theorem B2019763 : Blo 1889435 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B2693017 : Blo 1889435 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B14362757 : Blo 1889435 14362757 := bstep (se 4 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 14362757 = 2693017) B2693017
theorem B9575171 : Blo 1889435 9575171 := bstep (se 1 (by rfl) ⟨7181378, by rfl⟩ : syracuseStep 9575171 = 14362757) B14362757
theorem B6383447 : Blo 1889435 6383447 := bstep (se 1 (by rfl) ⟨4787585, by rfl⟩ : syracuseStep 6383447 = 9575171) B9575171
theorem B4255631 : Blo 1889435 4255631 := bstep (se 1 (by rfl) ⟨3191723, by rfl⟩ : syracuseStep 4255631 = 6383447) B6383447
theorem B2837087 : Blo 1889435 2837087 := bstep (se 1 (by rfl) ⟨2127815, by rfl⟩ : syracuseStep 2837087 = 4255631) B4255631
theorem B1891391 : Blo 1889435 1891391 := bstep (se 1 (by rfl) ⟨1418543, by rfl⟩ : syracuseStep 1891391 = 2837087) B2837087
theorem B2837093 : Blo 1889435 2837093 := bbase (se 4 (by rfl) ⟨265977, by rfl⟩ : syracuseStep 2837093 = 531955) (by norm_num)
theorem B1891395 : Blo 1889435 1891395 := bstep (se 1 (by rfl) ⟨1418546, by rfl⟩ : syracuseStep 1891395 = 2837093) B2837093
theorem B2693029 : Blo 1889435 2693029 := bbase (se 4 (by rfl) ⟨252471, by rfl⟩ : syracuseStep 2693029 = 504943) (by norm_num)
theorem B3590705 : Blo 1889435 3590705 := bstep (se 2 (by rfl) ⟨1346514, by rfl⟩ : syracuseStep 3590705 = 2693029) B2693029
theorem B2393803 : Blo 1889435 2393803 := bstep (se 1 (by rfl) ⟨1795352, by rfl⟩ : syracuseStep 2393803 = 3590705) B3590705
theorem B3191737 : Blo 1889435 3191737 := bstep (se 2 (by rfl) ⟨1196901, by rfl⟩ : syracuseStep 3191737 = 2393803) B2393803
theorem B4255649 : Blo 1889435 4255649 := bstep (se 2 (by rfl) ⟨1595868, by rfl⟩ : syracuseStep 4255649 = 3191737) B3191737
theorem B2837099 : Blo 1889435 2837099 := bstep (se 1 (by rfl) ⟨2127824, by rfl⟩ : syracuseStep 2837099 = 4255649) B4255649
theorem B1891399 : Blo 1889435 1891399 := bstep (se 1 (by rfl) ⟨1418549, by rfl⟩ : syracuseStep 1891399 = 2837099) B2837099
theorem B2127829 : Blo 1889435 2127829 := bbase (se 7 (by rfl) ⟨24935, by rfl⟩ : syracuseStep 2127829 = 49871) (by norm_num)
theorem B2837105 : Blo 1889435 2837105 := bstep (se 2 (by rfl) ⟨1063914, by rfl⟩ : syracuseStep 2837105 = 2127829) B2127829
theorem B1891403 : Blo 1889435 1891403 := bstep (se 1 (by rfl) ⟨1418552, by rfl⟩ : syracuseStep 1891403 = 2837105) B2837105
theorem B2393813 : Blo 1889435 2393813 := bbase (se 7 (by rfl) ⟨28052, by rfl⟩ : syracuseStep 2393813 = 56105) (by norm_num)
theorem B6383501 : Blo 1889435 6383501 := bstep (se 3 (by rfl) ⟨1196906, by rfl⟩ : syracuseStep 6383501 = 2393813) B2393813
theorem B4255667 : Blo 1889435 4255667 := bstep (se 1 (by rfl) ⟨3191750, by rfl⟩ : syracuseStep 4255667 = 6383501) B6383501
theorem B2837111 : Blo 1889435 2837111 := bstep (se 1 (by rfl) ⟨2127833, by rfl⟩ : syracuseStep 2837111 = 4255667) B4255667
theorem B1891407 : Blo 1889435 1891407 := bstep (se 1 (by rfl) ⟨1418555, by rfl⟩ : syracuseStep 1891407 = 2837111) B2837111
theorem B2837117 : Blo 1889435 2837117 := bbase (se 3 (by rfl) ⟨531959, by rfl⟩ : syracuseStep 2837117 = 1063919) (by norm_num)
theorem B1891411 : Blo 1889435 1891411 := bstep (se 1 (by rfl) ⟨1418558, by rfl⟩ : syracuseStep 1891411 = 2837117) B2837117
theorem B4255685 : Blo 1889435 4255685 := bbase (se 4 (by rfl) ⟨398970, by rfl⟩ : syracuseStep 4255685 = 797941) (by norm_num)
theorem B2837123 : Blo 1889435 2837123 := bstep (se 1 (by rfl) ⟨2127842, by rfl⟩ : syracuseStep 2837123 = 4255685) B4255685
theorem B1891415 : Blo 1889435 1891415 := bstep (se 1 (by rfl) ⟨1418561, by rfl⟩ : syracuseStep 1891415 = 2837123) B2837123
theorem B8079173 : Blo 1889435 8079173 := bbase (se 4 (by rfl) ⟨757422, by rfl⟩ : syracuseStep 8079173 = 1514845) (by norm_num)
theorem B5386115 : Blo 1889435 5386115 := bstep (se 1 (by rfl) ⟨4039586, by rfl⟩ : syracuseStep 5386115 = 8079173) B8079173
theorem B3590743 : Blo 1889435 3590743 := bstep (se 1 (by rfl) ⟨2693057, by rfl⟩ : syracuseStep 3590743 = 5386115) B5386115
theorem B4787657 : Blo 1889435 4787657 := bstep (se 2 (by rfl) ⟨1795371, by rfl⟩ : syracuseStep 4787657 = 3590743) B3590743
theorem B3191771 : Blo 1889435 3191771 := bstep (se 1 (by rfl) ⟨2393828, by rfl⟩ : syracuseStep 3191771 = 4787657) B4787657
theorem B2127847 : Blo 1889435 2127847 := bstep (se 1 (by rfl) ⟨1595885, by rfl⟩ : syracuseStep 2127847 = 3191771) B3191771
theorem B2837129 : Blo 1889435 2837129 := bstep (se 2 (by rfl) ⟨1063923, by rfl⟩ : syracuseStep 2837129 = 2127847) B2127847
theorem B1891419 : Blo 1889435 1891419 := bstep (se 1 (by rfl) ⟨1418564, by rfl⟩ : syracuseStep 1891419 = 2837129) B2837129
theorem B9575333 : Blo 1889435 9575333 := bbase (se 4 (by rfl) ⟨897687, by rfl⟩ : syracuseStep 9575333 = 1795375) (by norm_num)
theorem B6383555 : Blo 1889435 6383555 := bstep (se 1 (by rfl) ⟨4787666, by rfl⟩ : syracuseStep 6383555 = 9575333) B9575333
theorem B4255703 : Blo 1889435 4255703 := bstep (se 1 (by rfl) ⟨3191777, by rfl⟩ : syracuseStep 4255703 = 6383555) B6383555
theorem B2837135 : Blo 1889435 2837135 := bstep (se 1 (by rfl) ⟨2127851, by rfl⟩ : syracuseStep 2837135 = 4255703) B4255703
theorem B1891423 : Blo 1889435 1891423 := bstep (se 1 (by rfl) ⟨1418567, by rfl⟩ : syracuseStep 1891423 = 2837135) B2837135
theorem B2837141 : Blo 1889435 2837141 := bbase (se 6 (by rfl) ⟨66495, by rfl⟩ : syracuseStep 2837141 = 132991) (by norm_num)
theorem B1891427 : Blo 1889435 1891427 := bstep (se 1 (by rfl) ⟨1418570, by rfl⟩ : syracuseStep 1891427 = 2837141) B2837141
theorem B2556317 : Blo 1889435 2556317 := bbase (se 3 (by rfl) ⟨479309, by rfl⟩ : syracuseStep 2556317 = 958619) (by norm_num)
theorem B6816845 : Blo 1889435 6816845 := bstep (se 3 (by rfl) ⟨1278158, by rfl⟩ : syracuseStep 6816845 = 2556317) B2556317
theorem B18178253 : Blo 1889435 18178253 := bstep (se 3 (by rfl) ⟨3408422, by rfl⟩ : syracuseStep 18178253 = 6816845) B6816845
theorem B12118835 : Blo 1889435 12118835 := bstep (se 1 (by rfl) ⟨9089126, by rfl⟩ : syracuseStep 12118835 = 18178253) B18178253
theorem B8079223 : Blo 1889435 8079223 := bstep (se 1 (by rfl) ⟨6059417, by rfl⟩ : syracuseStep 8079223 = 12118835) B12118835
theorem B10772297 : Blo 1889435 10772297 := bstep (se 2 (by rfl) ⟨4039611, by rfl⟩ : syracuseStep 10772297 = 8079223) B8079223
theorem B7181531 : Blo 1889435 7181531 := bstep (se 1 (by rfl) ⟨5386148, by rfl⟩ : syracuseStep 7181531 = 10772297) B10772297
theorem B4787687 : Blo 1889435 4787687 := bstep (se 1 (by rfl) ⟨3590765, by rfl⟩ : syracuseStep 4787687 = 7181531) B7181531
theorem B3191791 : Blo 1889435 3191791 := bstep (se 1 (by rfl) ⟨2393843, by rfl⟩ : syracuseStep 3191791 = 4787687) B4787687
theorem B4255721 : Blo 1889435 4255721 := bstep (se 2 (by rfl) ⟨1595895, by rfl⟩ : syracuseStep 4255721 = 3191791) B3191791
theorem B2837147 : Blo 1889435 2837147 := bstep (se 1 (by rfl) ⟨2127860, by rfl⟩ : syracuseStep 2837147 = 4255721) B4255721
theorem B1891431 : Blo 1889435 1891431 := bstep (se 1 (by rfl) ⟨1418573, by rfl⟩ : syracuseStep 1891431 = 2837147) B2837147
theorem B2127865 : Blo 1889435 2127865 := bbase (se 2 (by rfl) ⟨797949, by rfl⟩ : syracuseStep 2127865 = 1595899) (by norm_num)
theorem B2837153 : Blo 1889435 2837153 := bstep (se 2 (by rfl) ⟨1063932, by rfl⟩ : syracuseStep 2837153 = 2127865) B2127865
theorem B1891435 : Blo 1889435 1891435 := bstep (se 1 (by rfl) ⟨1418576, by rfl⟩ : syracuseStep 1891435 = 2837153) B2837153
theorem C0 (j : ℕ) (h1 : 472358 ≤ j) (h2 : j ≤ 472858) : Blo 1889435 (4 * j + 3) := by
  interval_cases j
  · exact B1889435
  · exact B1889439
  · exact B1889443
  · exact B1889447
  · exact B1889451
  · exact B1889455
  · exact B1889459
  · exact B1889463
  · exact B1889467
  · exact B1889471
  · exact B1889475
  · exact B1889479
  · exact B1889483
  · exact B1889487
  · exact B1889491
  · exact B1889495
  · exact B1889499
  · exact B1889503
  · exact B1889507
  · exact B1889511
  · exact B1889515
  · exact B1889519
  · exact B1889523
  · exact B1889527
  · exact B1889531
  · exact B1889535
  · exact B1889539
  · exact B1889543
  · exact B1889547
  · exact B1889551
  · exact B1889555
  · exact B1889559
  · exact B1889563
  · exact B1889567
  · exact B1889571
  · exact B1889575
  · exact B1889579
  · exact B1889583
  · exact B1889587
  · exact B1889591
  · exact B1889595
  · exact B1889599
  · exact B1889603
  · exact B1889607
  · exact B1889611
  · exact B1889615
  · exact B1889619
  · exact B1889623
  · exact B1889627
  · exact B1889631
  · exact B1889635
  · exact B1889639
  · exact B1889643
  · exact B1889647
  · exact B1889651
  · exact B1889655
  · exact B1889659
  · exact B1889663
  · exact B1889667
  · exact B1889671
  · exact B1889675
  · exact B1889679
  · exact B1889683
  · exact B1889687
  · exact B1889691
  · exact B1889695
  · exact B1889699
  · exact B1889703
  · exact B1889707
  · exact B1889711
  · exact B1889715
  · exact B1889719
  · exact B1889723
  · exact B1889727
  · exact B1889731
  · exact B1889735
  · exact B1889739
  · exact B1889743
  · exact B1889747
  · exact B1889751
  · exact B1889755
  · exact B1889759
  · exact B1889763
  · exact B1889767
  · exact B1889771
  · exact B1889775
  · exact B1889779
  · exact B1889783
  · exact B1889787
  · exact B1889791
  · exact B1889795
  · exact B1889799
  · exact B1889803
  · exact B1889807
  · exact B1889811
  · exact B1889815
  · exact B1889819
  · exact B1889823
  · exact B1889827
  · exact B1889831
  · exact B1889835
  · exact B1889839
  · exact B1889843
  · exact B1889847
  · exact B1889851
  · exact B1889855
  · exact B1889859
  · exact B1889863
  · exact B1889867
  · exact B1889871
  · exact B1889875
  · exact B1889879
  · exact B1889883
  · exact B1889887
  · exact B1889891
  · exact B1889895
  · exact B1889899
  · exact B1889903
  · exact B1889907
  · exact B1889911
  · exact B1889915
  · exact B1889919
  · exact B1889923
  · exact B1889927
  · exact B1889931
  · exact B1889935
  · exact B1889939
  · exact B1889943
  · exact B1889947
  · exact B1889951
  · exact B1889955
  · exact B1889959
  · exact B1889963
  · exact B1889967
  · exact B1889971
  · exact B1889975
  · exact B1889979
  · exact B1889983
  · exact B1889987
  · exact B1889991
  · exact B1889995
  · exact B1889999
  · exact B1890003
  · exact B1890007
  · exact B1890011
  · exact B1890015
  · exact B1890019
  · exact B1890023
  · exact B1890027
  · exact B1890031
  · exact B1890035
  · exact B1890039
  · exact B1890043
  · exact B1890047
  · exact B1890051
  · exact B1890055
  · exact B1890059
  · exact B1890063
  · exact B1890067
  · exact B1890071
  · exact B1890075
  · exact B1890079
  · exact B1890083
  · exact B1890087
  · exact B1890091
  · exact B1890095
  · exact B1890099
  · exact B1890103
  · exact B1890107
  · exact B1890111
  · exact B1890115
  · exact B1890119
  · exact B1890123
  · exact B1890127
  · exact B1890131
  · exact B1890135
  · exact B1890139
  · exact B1890143
  · exact B1890147
  · exact B1890151
  · exact B1890155
  · exact B1890159
  · exact B1890163
  · exact B1890167
  · exact B1890171
  · exact B1890175
  · exact B1890179
  · exact B1890183
  · exact B1890187
  · exact B1890191
  · exact B1890195
  · exact B1890199
  · exact B1890203
  · exact B1890207
  · exact B1890211
  · exact B1890215
  · exact B1890219
  · exact B1890223
  · exact B1890227
  · exact B1890231
  · exact B1890235
  · exact B1890239
  · exact B1890243
  · exact B1890247
  · exact B1890251
  · exact B1890255
  · exact B1890259
  · exact B1890263
  · exact B1890267
  · exact B1890271
  · exact B1890275
  · exact B1890279
  · exact B1890283
  · exact B1890287
  · exact B1890291
  · exact B1890295
  · exact B1890299
  · exact B1890303
  · exact B1890307
  · exact B1890311
  · exact B1890315
  · exact B1890319
  · exact B1890323
  · exact B1890327
  · exact B1890331
  · exact B1890335
  · exact B1890339
  · exact B1890343
  · exact B1890347
  · exact B1890351
  · exact B1890355
  · exact B1890359
  · exact B1890363
  · exact B1890367
  · exact B1890371
  · exact B1890375
  · exact B1890379
  · exact B1890383
  · exact B1890387
  · exact B1890391
  · exact B1890395
  · exact B1890399
  · exact B1890403
  · exact B1890407
  · exact B1890411
  · exact B1890415
  · exact B1890419
  · exact B1890423
  · exact B1890427
  · exact B1890431
  · exact B1890435
  · exact B1890439
  · exact B1890443
  · exact B1890447
  · exact B1890451
  · exact B1890455
  · exact B1890459
  · exact B1890463
  · exact B1890467
  · exact B1890471
  · exact B1890475
  · exact B1890479
  · exact B1890483
  · exact B1890487
  · exact B1890491
  · exact B1890495
  · exact B1890499
  · exact B1890503
  · exact B1890507
  · exact B1890511
  · exact B1890515
  · exact B1890519
  · exact B1890523
  · exact B1890527
  · exact B1890531
  · exact B1890535
  · exact B1890539
  · exact B1890543
  · exact B1890547
  · exact B1890551
  · exact B1890555
  · exact B1890559
  · exact B1890563
  · exact B1890567
  · exact B1890571
  · exact B1890575
  · exact B1890579
  · exact B1890583
  · exact B1890587
  · exact B1890591
  · exact B1890595
  · exact B1890599
  · exact B1890603
  · exact B1890607
  · exact B1890611
  · exact B1890615
  · exact B1890619
  · exact B1890623
  · exact B1890627
  · exact B1890631
  · exact B1890635
  · exact B1890639
  · exact B1890643
  · exact B1890647
  · exact B1890651
  · exact B1890655
  · exact B1890659
  · exact B1890663
  · exact B1890667
  · exact B1890671
  · exact B1890675
  · exact B1890679
  · exact B1890683
  · exact B1890687
  · exact B1890691
  · exact B1890695
  · exact B1890699
  · exact B1890703
  · exact B1890707
  · exact B1890711
  · exact B1890715
  · exact B1890719
  · exact B1890723
  · exact B1890727
  · exact B1890731
  · exact B1890735
  · exact B1890739
  · exact B1890743
  · exact B1890747
  · exact B1890751
  · exact B1890755
  · exact B1890759
  · exact B1890763
  · exact B1890767
  · exact B1890771
  · exact B1890775
  · exact B1890779
  · exact B1890783
  · exact B1890787
  · exact B1890791
  · exact B1890795
  · exact B1890799
  · exact B1890803
  · exact B1890807
  · exact B1890811
  · exact B1890815
  · exact B1890819
  · exact B1890823
  · exact B1890827
  · exact B1890831
  · exact B1890835
  · exact B1890839
  · exact B1890843
  · exact B1890847
  · exact B1890851
  · exact B1890855
  · exact B1890859
  · exact B1890863
  · exact B1890867
  · exact B1890871
  · exact B1890875
  · exact B1890879
  · exact B1890883
  · exact B1890887
  · exact B1890891
  · exact B1890895
  · exact B1890899
  · exact B1890903
  · exact B1890907
  · exact B1890911
  · exact B1890915
  · exact B1890919
  · exact B1890923
  · exact B1890927
  · exact B1890931
  · exact B1890935
  · exact B1890939
  · exact B1890943
  · exact B1890947
  · exact B1890951
  · exact B1890955
  · exact B1890959
  · exact B1890963
  · exact B1890967
  · exact B1890971
  · exact B1890975
  · exact B1890979
  · exact B1890983
  · exact B1890987
  · exact B1890991
  · exact B1890995
  · exact B1890999
  · exact B1891003
  · exact B1891007
  · exact B1891011
  · exact B1891015
  · exact B1891019
  · exact B1891023
  · exact B1891027
  · exact B1891031
  · exact B1891035
  · exact B1891039
  · exact B1891043
  · exact B1891047
  · exact B1891051
  · exact B1891055
  · exact B1891059
  · exact B1891063
  · exact B1891067
  · exact B1891071
  · exact B1891075
  · exact B1891079
  · exact B1891083
  · exact B1891087
  · exact B1891091
  · exact B1891095
  · exact B1891099
  · exact B1891103
  · exact B1891107
  · exact B1891111
  · exact B1891115
  · exact B1891119
  · exact B1891123
  · exact B1891127
  · exact B1891131
  · exact B1891135
  · exact B1891139
  · exact B1891143
  · exact B1891147
  · exact B1891151
  · exact B1891155
  · exact B1891159
  · exact B1891163
  · exact B1891167
  · exact B1891171
  · exact B1891175
  · exact B1891179
  · exact B1891183
  · exact B1891187
  · exact B1891191
  · exact B1891195
  · exact B1891199
  · exact B1891203
  · exact B1891207
  · exact B1891211
  · exact B1891215
  · exact B1891219
  · exact B1891223
  · exact B1891227
  · exact B1891231
  · exact B1891235
  · exact B1891239
  · exact B1891243
  · exact B1891247
  · exact B1891251
  · exact B1891255
  · exact B1891259
  · exact B1891263
  · exact B1891267
  · exact B1891271
  · exact B1891275
  · exact B1891279
  · exact B1891283
  · exact B1891287
  · exact B1891291
  · exact B1891295
  · exact B1891299
  · exact B1891303
  · exact B1891307
  · exact B1891311
  · exact B1891315
  · exact B1891319
  · exact B1891323
  · exact B1891327
  · exact B1891331
  · exact B1891335
  · exact B1891339
  · exact B1891343
  · exact B1891347
  · exact B1891351
  · exact B1891355
  · exact B1891359
  · exact B1891363
  · exact B1891367
  · exact B1891371
  · exact B1891375
  · exact B1891379
  · exact B1891383
  · exact B1891387
  · exact B1891391
  · exact B1891395
  · exact B1891399
  · exact B1891403
  · exact B1891407
  · exact B1891411
  · exact B1891415
  · exact B1891419
  · exact B1891423
  · exact B1891427
  · exact B1891431
  · exact B1891435
theorem solution (m : ℕ) (hlo : 1889435 ≤ m) (hhi : m ≤ 1891435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 472358 ≤ j := by omega
    have hj2 : j ≤ 472858 := by omega
    have hb : Blo 1889435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
