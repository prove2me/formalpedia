-- Prove2me | solution 1 for syracuse_descends_range_2049435_2051435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:49:25.129523+00:00
-- url     : https://prove2.me/submissions/e596d5c8-2ee4-4eb3-b652-0f363f337f5d

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

theorem B2918045 : Blo 2049435 2918045 := bbase (se 3 (by rfl) ⟨547133, by rfl⟩ : syracuseStep 2918045 = 1094267) (by norm_num)
theorem B7781453 : Blo 2049435 7781453 := bstep (se 3 (by rfl) ⟨1459022, by rfl⟩ : syracuseStep 7781453 = 2918045) B2918045
theorem B5187635 : Blo 2049435 5187635 := bstep (se 1 (by rfl) ⟨3890726, by rfl⟩ : syracuseStep 5187635 = 7781453) B7781453
theorem B3458423 : Blo 2049435 3458423 := bstep (se 1 (by rfl) ⟨2593817, by rfl⟩ : syracuseStep 3458423 = 5187635) B5187635
theorem B2305615 : Blo 2049435 2305615 := bstep (se 1 (by rfl) ⟨1729211, by rfl⟩ : syracuseStep 2305615 = 3458423) B3458423
theorem B3074153 : Blo 2049435 3074153 := bstep (se 2 (by rfl) ⟨1152807, by rfl⟩ : syracuseStep 3074153 = 2305615) B2305615
theorem B2049435 : Blo 2049435 2049435 := bstep (se 1 (by rfl) ⟨1537076, by rfl⟩ : syracuseStep 2049435 = 3074153) B3074153
theorem B33238421 : Blo 2049435 33238421 := bbase (se 6 (by rfl) ⟨779025, by rfl⟩ : syracuseStep 33238421 = 1558051) (by norm_num)
theorem B22158947 : Blo 2049435 22158947 := bstep (se 1 (by rfl) ⟨16619210, by rfl⟩ : syracuseStep 22158947 = 33238421) B33238421
theorem B14772631 : Blo 2049435 14772631 := bstep (se 1 (by rfl) ⟨11079473, by rfl⟩ : syracuseStep 14772631 = 22158947) B22158947
theorem B19696841 : Blo 2049435 19696841 := bstep (se 2 (by rfl) ⟨7386315, by rfl⟩ : syracuseStep 19696841 = 14772631) B14772631
theorem B13131227 : Blo 2049435 13131227 := bstep (se 1 (by rfl) ⟨9848420, by rfl⟩ : syracuseStep 13131227 = 19696841) B19696841
theorem B8754151 : Blo 2049435 8754151 := bstep (se 1 (by rfl) ⟨6565613, by rfl⟩ : syracuseStep 8754151 = 13131227) B13131227
theorem B11672201 : Blo 2049435 11672201 := bstep (se 2 (by rfl) ⟨4377075, by rfl⟩ : syracuseStep 11672201 = 8754151) B8754151
theorem B7781467 : Blo 2049435 7781467 := bstep (se 1 (by rfl) ⟨5836100, by rfl⟩ : syracuseStep 7781467 = 11672201) B11672201
theorem B10375289 : Blo 2049435 10375289 := bstep (se 2 (by rfl) ⟨3890733, by rfl⟩ : syracuseStep 10375289 = 7781467) B7781467
theorem B6916859 : Blo 2049435 6916859 := bstep (se 1 (by rfl) ⟨5187644, by rfl⟩ : syracuseStep 6916859 = 10375289) B10375289
theorem B4611239 : Blo 2049435 4611239 := bstep (se 1 (by rfl) ⟨3458429, by rfl⟩ : syracuseStep 4611239 = 6916859) B6916859
theorem B3074159 : Blo 2049435 3074159 := bstep (se 1 (by rfl) ⟨2305619, by rfl⟩ : syracuseStep 3074159 = 4611239) B4611239
theorem B2049439 : Blo 2049435 2049439 := bstep (se 1 (by rfl) ⟨1537079, by rfl⟩ : syracuseStep 2049439 = 3074159) B3074159
theorem B3074165 : Blo 2049435 3074165 := bbase (se 5 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 3074165 = 288203) (by norm_num)
theorem B2049443 : Blo 2049435 2049443 := bstep (se 1 (by rfl) ⟨1537082, by rfl⟩ : syracuseStep 2049443 = 3074165) B3074165
theorem B3890749 : Blo 2049435 3890749 := bbase (se 3 (by rfl) ⟨729515, by rfl⟩ : syracuseStep 3890749 = 1459031) (by norm_num)
theorem B5187665 : Blo 2049435 5187665 := bstep (se 2 (by rfl) ⟨1945374, by rfl⟩ : syracuseStep 5187665 = 3890749) B3890749
theorem B3458443 : Blo 2049435 3458443 := bstep (se 1 (by rfl) ⟨2593832, by rfl⟩ : syracuseStep 3458443 = 5187665) B5187665
theorem B4611257 : Blo 2049435 4611257 := bstep (se 2 (by rfl) ⟨1729221, by rfl⟩ : syracuseStep 4611257 = 3458443) B3458443
theorem B3074171 : Blo 2049435 3074171 := bstep (se 1 (by rfl) ⟨2305628, by rfl⟩ : syracuseStep 3074171 = 4611257) B4611257
theorem B2049447 : Blo 2049435 2049447 := bstep (se 1 (by rfl) ⟨1537085, by rfl⟩ : syracuseStep 2049447 = 3074171) B3074171
theorem B2305633 : Blo 2049435 2305633 := bbase (se 2 (by rfl) ⟨864612, by rfl⟩ : syracuseStep 2305633 = 1729225) (by norm_num)
theorem B3074177 : Blo 2049435 3074177 := bstep (se 2 (by rfl) ⟨1152816, by rfl⟩ : syracuseStep 3074177 = 2305633) B2305633
theorem B2049451 : Blo 2049435 2049451 := bstep (se 1 (by rfl) ⟨1537088, by rfl⟩ : syracuseStep 2049451 = 3074177) B3074177
theorem B5187685 : Blo 2049435 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B6916913 : Blo 2049435 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B4611275 : Blo 2049435 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B3074183 : Blo 2049435 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B2049455 : Blo 2049435 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B3074189 : Blo 2049435 3074189 := bbase (se 3 (by rfl) ⟨576410, by rfl⟩ : syracuseStep 3074189 = 1152821) (by norm_num)
theorem B2049459 : Blo 2049435 2049459 := bstep (se 1 (by rfl) ⟨1537094, by rfl⟩ : syracuseStep 2049459 = 3074189) B3074189
theorem B4611293 : Blo 2049435 4611293 := bbase (se 3 (by rfl) ⟨864617, by rfl⟩ : syracuseStep 4611293 = 1729235) (by norm_num)
theorem B3074195 : Blo 2049435 3074195 := bstep (se 1 (by rfl) ⟨2305646, by rfl⟩ : syracuseStep 3074195 = 4611293) B4611293
theorem B2049463 : Blo 2049435 2049463 := bstep (se 1 (by rfl) ⟨1537097, by rfl⟩ : syracuseStep 2049463 = 3074195) B3074195
theorem B3458477 : Blo 2049435 3458477 := bbase (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) (by norm_num)
theorem B2305651 : Blo 2049435 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B3074201 : Blo 2049435 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B2049467 : Blo 2049435 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B14022677 : Blo 2049435 14022677 := bbase (se 6 (by rfl) ⟨328656, by rfl⟩ : syracuseStep 14022677 = 657313) (by norm_num)
theorem B37393805 : Blo 2049435 37393805 := bstep (se 3 (by rfl) ⟨7011338, by rfl⟩ : syracuseStep 37393805 = 14022677) B14022677
theorem B24929203 : Blo 2049435 24929203 := bstep (se 1 (by rfl) ⟨18696902, by rfl⟩ : syracuseStep 24929203 = 37393805) B37393805
theorem B33238937 : Blo 2049435 33238937 := bstep (se 2 (by rfl) ⟨12464601, by rfl⟩ : syracuseStep 33238937 = 24929203) B24929203
theorem B88637165 : Blo 2049435 88637165 := bstep (se 3 (by rfl) ⟨16619468, by rfl⟩ : syracuseStep 88637165 = 33238937) B33238937
theorem B59091443 : Blo 2049435 59091443 := bstep (se 1 (by rfl) ⟨44318582, by rfl⟩ : syracuseStep 59091443 = 88637165) B88637165
theorem B39394295 : Blo 2049435 39394295 := bstep (se 1 (by rfl) ⟨29545721, by rfl⟩ : syracuseStep 39394295 = 59091443) B59091443
theorem B26262863 : Blo 2049435 26262863 := bstep (se 1 (by rfl) ⟨19697147, by rfl⟩ : syracuseStep 26262863 = 39394295) B39394295
theorem B17508575 : Blo 2049435 17508575 := bstep (se 1 (by rfl) ⟨13131431, by rfl⟩ : syracuseStep 17508575 = 26262863) B26262863
theorem B11672383 : Blo 2049435 11672383 := bstep (se 1 (by rfl) ⟨8754287, by rfl⟩ : syracuseStep 11672383 = 17508575) B17508575
theorem B15563177 : Blo 2049435 15563177 := bstep (se 2 (by rfl) ⟨5836191, by rfl⟩ : syracuseStep 15563177 = 11672383) B11672383
theorem B10375451 : Blo 2049435 10375451 := bstep (se 1 (by rfl) ⟨7781588, by rfl⟩ : syracuseStep 10375451 = 15563177) B15563177
theorem B6916967 : Blo 2049435 6916967 := bstep (se 1 (by rfl) ⟨5187725, by rfl⟩ : syracuseStep 6916967 = 10375451) B10375451
theorem B4611311 : Blo 2049435 4611311 := bstep (se 1 (by rfl) ⟨3458483, by rfl⟩ : syracuseStep 4611311 = 6916967) B6916967
theorem B3074207 : Blo 2049435 3074207 := bstep (se 1 (by rfl) ⟨2305655, by rfl⟩ : syracuseStep 3074207 = 4611311) B4611311
theorem B2049471 : Blo 2049435 2049471 := bstep (se 1 (by rfl) ⟨1537103, by rfl⟩ : syracuseStep 2049471 = 3074207) B3074207
theorem B3074213 : Blo 2049435 3074213 := bbase (se 4 (by rfl) ⟨288207, by rfl⟩ : syracuseStep 3074213 = 576415) (by norm_num)
theorem B2049475 : Blo 2049435 2049475 := bstep (se 1 (by rfl) ⟨1537106, by rfl⟩ : syracuseStep 2049475 = 3074213) B3074213
theorem B2593873 : Blo 2049435 2593873 := bbase (se 2 (by rfl) ⟨972702, by rfl⟩ : syracuseStep 2593873 = 1945405) (by norm_num)
theorem B3458497 : Blo 2049435 3458497 := bstep (se 2 (by rfl) ⟨1296936, by rfl⟩ : syracuseStep 3458497 = 2593873) B2593873
theorem B4611329 : Blo 2049435 4611329 := bstep (se 2 (by rfl) ⟨1729248, by rfl⟩ : syracuseStep 4611329 = 3458497) B3458497
theorem B3074219 : Blo 2049435 3074219 := bstep (se 1 (by rfl) ⟨2305664, by rfl⟩ : syracuseStep 3074219 = 4611329) B4611329
theorem B2049479 : Blo 2049435 2049479 := bstep (se 1 (by rfl) ⟨1537109, by rfl⟩ : syracuseStep 2049479 = 3074219) B3074219
theorem B2305669 : Blo 2049435 2305669 := bbase (se 4 (by rfl) ⟨216156, by rfl⟩ : syracuseStep 2305669 = 432313) (by norm_num)
theorem B3074225 : Blo 2049435 3074225 := bstep (se 2 (by rfl) ⟨1152834, by rfl⟩ : syracuseStep 3074225 = 2305669) B2305669
theorem B2049483 : Blo 2049435 2049483 := bstep (se 1 (by rfl) ⟨1537112, by rfl⟩ : syracuseStep 2049483 = 3074225) B3074225
theorem B7011397 : Blo 2049435 7011397 := bbase (se 4 (by rfl) ⟨657318, by rfl⟩ : syracuseStep 7011397 = 1314637) (by norm_num)
theorem B9348529 : Blo 2049435 9348529 := bstep (se 2 (by rfl) ⟨3505698, by rfl⟩ : syracuseStep 9348529 = 7011397) B7011397
theorem B12464705 : Blo 2049435 12464705 := bstep (se 2 (by rfl) ⟨4674264, by rfl⟩ : syracuseStep 12464705 = 9348529) B9348529
theorem B8309803 : Blo 2049435 8309803 := bstep (se 1 (by rfl) ⟨6232352, by rfl⟩ : syracuseStep 8309803 = 12464705) B12464705
theorem B11079737 : Blo 2049435 11079737 := bstep (se 2 (by rfl) ⟨4154901, by rfl⟩ : syracuseStep 11079737 = 8309803) B8309803
theorem B7386491 : Blo 2049435 7386491 := bstep (se 1 (by rfl) ⟨5539868, by rfl⟩ : syracuseStep 7386491 = 11079737) B11079737
theorem B4924327 : Blo 2049435 4924327 := bstep (se 1 (by rfl) ⟨3693245, by rfl⟩ : syracuseStep 4924327 = 7386491) B7386491
theorem B6565769 : Blo 2049435 6565769 := bstep (se 2 (by rfl) ⟨2462163, by rfl⟩ : syracuseStep 6565769 = 4924327) B4924327
theorem B4377179 : Blo 2049435 4377179 := bstep (se 1 (by rfl) ⟨3282884, by rfl⟩ : syracuseStep 4377179 = 6565769) B6565769
theorem B2918119 : Blo 2049435 2918119 := bstep (se 1 (by rfl) ⟨2188589, by rfl⟩ : syracuseStep 2918119 = 4377179) B4377179
theorem B3890825 : Blo 2049435 3890825 := bstep (se 2 (by rfl) ⟨1459059, by rfl⟩ : syracuseStep 3890825 = 2918119) B2918119
theorem B2593883 : Blo 2049435 2593883 := bstep (se 1 (by rfl) ⟨1945412, by rfl⟩ : syracuseStep 2593883 = 3890825) B3890825
theorem B6917021 : Blo 2049435 6917021 := bstep (se 3 (by rfl) ⟨1296941, by rfl⟩ : syracuseStep 6917021 = 2593883) B2593883
theorem B4611347 : Blo 2049435 4611347 := bstep (se 1 (by rfl) ⟨3458510, by rfl⟩ : syracuseStep 4611347 = 6917021) B6917021
theorem B3074231 : Blo 2049435 3074231 := bstep (se 1 (by rfl) ⟨2305673, by rfl⟩ : syracuseStep 3074231 = 4611347) B4611347
theorem B2049487 : Blo 2049435 2049487 := bstep (se 1 (by rfl) ⟨1537115, by rfl⟩ : syracuseStep 2049487 = 3074231) B3074231
theorem B3074237 : Blo 2049435 3074237 := bbase (se 3 (by rfl) ⟨576419, by rfl⟩ : syracuseStep 3074237 = 1152839) (by norm_num)
theorem B2049491 : Blo 2049435 2049491 := bstep (se 1 (by rfl) ⟨1537118, by rfl⟩ : syracuseStep 2049491 = 3074237) B3074237
theorem B4611365 : Blo 2049435 4611365 := bbase (se 4 (by rfl) ⟨432315, by rfl⟩ : syracuseStep 4611365 = 864631) (by norm_num)
theorem B3074243 : Blo 2049435 3074243 := bstep (se 1 (by rfl) ⟨2305682, by rfl⟩ : syracuseStep 3074243 = 4611365) B4611365
theorem B2049495 : Blo 2049435 2049495 := bstep (se 1 (by rfl) ⟨1537121, by rfl⟩ : syracuseStep 2049495 = 3074243) B3074243
theorem B5187797 : Blo 2049435 5187797 := bbase (se 7 (by rfl) ⟨60794, by rfl⟩ : syracuseStep 5187797 = 121589) (by norm_num)
theorem B3458531 : Blo 2049435 3458531 := bstep (se 1 (by rfl) ⟨2593898, by rfl⟩ : syracuseStep 3458531 = 5187797) B5187797
theorem B2305687 : Blo 2049435 2305687 := bstep (se 1 (by rfl) ⟨1729265, by rfl⟩ : syracuseStep 2305687 = 3458531) B3458531
theorem B3074249 : Blo 2049435 3074249 := bstep (se 2 (by rfl) ⟨1152843, by rfl⟩ : syracuseStep 3074249 = 2305687) B2305687
theorem B2049499 : Blo 2049435 2049499 := bstep (se 1 (by rfl) ⟨1537124, by rfl⟩ : syracuseStep 2049499 = 3074249) B3074249
theorem B4154933 : Blo 2049435 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B11079821 : Blo 2049435 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B7386547 : Blo 2049435 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B9848729 : Blo 2049435 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B6565819 : Blo 2049435 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B8754425 : Blo 2049435 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B5836283 : Blo 2049435 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B3890855 : Blo 2049435 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B10375613 : Blo 2049435 10375613 := bstep (se 3 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 10375613 = 3890855) B3890855
theorem B6917075 : Blo 2049435 6917075 := bstep (se 1 (by rfl) ⟨5187806, by rfl⟩ : syracuseStep 6917075 = 10375613) B10375613
theorem B4611383 : Blo 2049435 4611383 := bstep (se 1 (by rfl) ⟨3458537, by rfl⟩ : syracuseStep 4611383 = 6917075) B6917075
theorem B3074255 : Blo 2049435 3074255 := bstep (se 1 (by rfl) ⟨2305691, by rfl⟩ : syracuseStep 3074255 = 4611383) B4611383
theorem B2049503 : Blo 2049435 2049503 := bstep (se 1 (by rfl) ⟨1537127, by rfl⟩ : syracuseStep 2049503 = 3074255) B3074255
theorem B3074261 : Blo 2049435 3074261 := bbase (se 7 (by rfl) ⟨36026, by rfl⟩ : syracuseStep 3074261 = 72053) (by norm_num)
theorem B2049507 : Blo 2049435 2049507 := bstep (se 1 (by rfl) ⟨1537130, by rfl⟩ : syracuseStep 2049507 = 3074261) B3074261
theorem B2218477 : Blo 2049435 2218477 := bbase (se 3 (by rfl) ⟨415964, by rfl⟩ : syracuseStep 2218477 = 831929) (by norm_num)
theorem B2957969 : Blo 2049435 2957969 := bstep (se 2 (by rfl) ⟨1109238, by rfl⟩ : syracuseStep 2957969 = 2218477) B2218477
theorem B7887917 : Blo 2049435 7887917 := bstep (se 3 (by rfl) ⟨1478984, by rfl⟩ : syracuseStep 7887917 = 2957969) B2957969
theorem B5258611 : Blo 2049435 5258611 := bstep (se 1 (by rfl) ⟨3943958, by rfl⟩ : syracuseStep 5258611 = 7887917) B7887917
theorem B7011481 : Blo 2049435 7011481 := bstep (se 2 (by rfl) ⟨2629305, by rfl⟩ : syracuseStep 7011481 = 5258611) B5258611
theorem B9348641 : Blo 2049435 9348641 := bstep (se 2 (by rfl) ⟨3505740, by rfl⟩ : syracuseStep 9348641 = 7011481) B7011481
theorem B6232427 : Blo 2049435 6232427 := bstep (se 1 (by rfl) ⟨4674320, by rfl⟩ : syracuseStep 6232427 = 9348641) B9348641
theorem B4154951 : Blo 2049435 4154951 := bstep (se 1 (by rfl) ⟨3116213, by rfl⟩ : syracuseStep 4154951 = 6232427) B6232427
theorem B2769967 : Blo 2049435 2769967 := bstep (se 1 (by rfl) ⟨2077475, by rfl⟩ : syracuseStep 2769967 = 4154951) B4154951
theorem B3693289 : Blo 2049435 3693289 := bstep (se 2 (by rfl) ⟨1384983, by rfl⟩ : syracuseStep 3693289 = 2769967) B2769967
theorem B4924385 : Blo 2049435 4924385 := bstep (se 2 (by rfl) ⟨1846644, by rfl⟩ : syracuseStep 4924385 = 3693289) B3693289
theorem B3282923 : Blo 2049435 3282923 := bstep (se 1 (by rfl) ⟨2462192, by rfl⟩ : syracuseStep 3282923 = 4924385) B4924385
theorem B2188615 : Blo 2049435 2188615 := bstep (se 1 (by rfl) ⟨1641461, by rfl⟩ : syracuseStep 2188615 = 3282923) B3282923
theorem B2918153 : Blo 2049435 2918153 := bstep (se 2 (by rfl) ⟨1094307, by rfl⟩ : syracuseStep 2918153 = 2188615) B2188615
theorem B7781741 : Blo 2049435 7781741 := bstep (se 3 (by rfl) ⟨1459076, by rfl⟩ : syracuseStep 7781741 = 2918153) B2918153
theorem B5187827 : Blo 2049435 5187827 := bstep (se 1 (by rfl) ⟨3890870, by rfl⟩ : syracuseStep 5187827 = 7781741) B7781741
theorem B3458551 : Blo 2049435 3458551 := bstep (se 1 (by rfl) ⟨2593913, by rfl⟩ : syracuseStep 3458551 = 5187827) B5187827
theorem B4611401 : Blo 2049435 4611401 := bstep (se 2 (by rfl) ⟨1729275, by rfl⟩ : syracuseStep 4611401 = 3458551) B3458551
theorem B3074267 : Blo 2049435 3074267 := bstep (se 1 (by rfl) ⟨2305700, by rfl⟩ : syracuseStep 3074267 = 4611401) B4611401
theorem B2049511 : Blo 2049435 2049511 := bstep (se 1 (by rfl) ⟨1537133, by rfl⟩ : syracuseStep 2049511 = 3074267) B3074267
theorem B2305705 : Blo 2049435 2305705 := bbase (se 2 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 2305705 = 1729279) (by norm_num)
theorem B3074273 : Blo 2049435 3074273 := bstep (se 2 (by rfl) ⟨1152852, by rfl⟩ : syracuseStep 3074273 = 2305705) B2305705
theorem B2049515 : Blo 2049435 2049515 := bstep (se 1 (by rfl) ⟨1537136, by rfl⟩ : syracuseStep 2049515 = 3074273) B3074273
theorem B2337169 : Blo 2049435 2337169 := bbase (se 2 (by rfl) ⟨876438, by rfl⟩ : syracuseStep 2337169 = 1752877) (by norm_num)
theorem B3116225 : Blo 2049435 3116225 := bstep (se 2 (by rfl) ⟨1168584, by rfl⟩ : syracuseStep 3116225 = 2337169) B2337169
theorem B2077483 : Blo 2049435 2077483 := bstep (se 1 (by rfl) ⟨1558112, by rfl⟩ : syracuseStep 2077483 = 3116225) B3116225
theorem B2769977 : Blo 2049435 2769977 := bstep (se 2 (by rfl) ⟨1038741, by rfl⟩ : syracuseStep 2769977 = 2077483) B2077483
theorem B7386605 : Blo 2049435 7386605 := bstep (se 3 (by rfl) ⟨1384988, by rfl⟩ : syracuseStep 7386605 = 2769977) B2769977
theorem B4924403 : Blo 2049435 4924403 := bstep (se 1 (by rfl) ⟨3693302, by rfl⟩ : syracuseStep 4924403 = 7386605) B7386605
theorem B3282935 : Blo 2049435 3282935 := bstep (se 1 (by rfl) ⟨2462201, by rfl⟩ : syracuseStep 3282935 = 4924403) B4924403
theorem B8754493 : Blo 2049435 8754493 := bstep (se 3 (by rfl) ⟨1641467, by rfl⟩ : syracuseStep 8754493 = 3282935) B3282935
theorem B11672657 : Blo 2049435 11672657 := bstep (se 2 (by rfl) ⟨4377246, by rfl⟩ : syracuseStep 11672657 = 8754493) B8754493
theorem B7781771 : Blo 2049435 7781771 := bstep (se 1 (by rfl) ⟨5836328, by rfl⟩ : syracuseStep 7781771 = 11672657) B11672657
theorem B5187847 : Blo 2049435 5187847 := bstep (se 1 (by rfl) ⟨3890885, by rfl⟩ : syracuseStep 5187847 = 7781771) B7781771
theorem B6917129 : Blo 2049435 6917129 := bstep (se 2 (by rfl) ⟨2593923, by rfl⟩ : syracuseStep 6917129 = 5187847) B5187847
theorem B4611419 : Blo 2049435 4611419 := bstep (se 1 (by rfl) ⟨3458564, by rfl⟩ : syracuseStep 4611419 = 6917129) B6917129
theorem B3074279 : Blo 2049435 3074279 := bstep (se 1 (by rfl) ⟨2305709, by rfl⟩ : syracuseStep 3074279 = 4611419) B4611419
theorem B2049519 : Blo 2049435 2049519 := bstep (se 1 (by rfl) ⟨1537139, by rfl⟩ : syracuseStep 2049519 = 3074279) B3074279
theorem B3074285 : Blo 2049435 3074285 := bbase (se 3 (by rfl) ⟨576428, by rfl⟩ : syracuseStep 3074285 = 1152857) (by norm_num)
theorem B2049523 : Blo 2049435 2049523 := bstep (se 1 (by rfl) ⟨1537142, by rfl⟩ : syracuseStep 2049523 = 3074285) B3074285
theorem B4611437 : Blo 2049435 4611437 := bbase (se 3 (by rfl) ⟨864644, by rfl⟩ : syracuseStep 4611437 = 1729289) (by norm_num)
theorem B3074291 : Blo 2049435 3074291 := bstep (se 1 (by rfl) ⟨2305718, by rfl⟩ : syracuseStep 3074291 = 4611437) B4611437
theorem B2049527 : Blo 2049435 2049527 := bstep (se 1 (by rfl) ⟨1537145, by rfl⟩ : syracuseStep 2049527 = 3074291) B3074291
theorem B3890909 : Blo 2049435 3890909 := bbase (se 3 (by rfl) ⟨729545, by rfl⟩ : syracuseStep 3890909 = 1459091) (by norm_num)
theorem B2593939 : Blo 2049435 2593939 := bstep (se 1 (by rfl) ⟨1945454, by rfl⟩ : syracuseStep 2593939 = 3890909) B3890909
theorem B3458585 : Blo 2049435 3458585 := bstep (se 2 (by rfl) ⟨1296969, by rfl⟩ : syracuseStep 3458585 = 2593939) B2593939
theorem B2305723 : Blo 2049435 2305723 := bstep (se 1 (by rfl) ⟨1729292, by rfl⟩ : syracuseStep 2305723 = 3458585) B3458585
theorem B3074297 : Blo 2049435 3074297 := bstep (se 2 (by rfl) ⟨1152861, by rfl⟩ : syracuseStep 3074297 = 2305723) B2305723
theorem B2049531 : Blo 2049435 2049531 := bstep (se 1 (by rfl) ⟨1537148, by rfl⟩ : syracuseStep 2049531 = 3074297) B3074297
theorem B7386661 : Blo 2049435 7386661 := bbase (se 4 (by rfl) ⟨692499, by rfl⟩ : syracuseStep 7386661 = 1384999) (by norm_num)
theorem B9848881 : Blo 2049435 9848881 := bstep (se 2 (by rfl) ⟨3693330, by rfl⟩ : syracuseStep 9848881 = 7386661) B7386661
theorem B52527365 : Blo 2049435 52527365 := bstep (se 4 (by rfl) ⟨4924440, by rfl⟩ : syracuseStep 52527365 = 9848881) B9848881
theorem B35018243 : Blo 2049435 35018243 := bstep (se 1 (by rfl) ⟨26263682, by rfl⟩ : syracuseStep 35018243 = 52527365) B52527365
theorem B23345495 : Blo 2049435 23345495 := bstep (se 1 (by rfl) ⟨17509121, by rfl⟩ : syracuseStep 23345495 = 35018243) B35018243
theorem B15563663 : Blo 2049435 15563663 := bstep (se 1 (by rfl) ⟨11672747, by rfl⟩ : syracuseStep 15563663 = 23345495) B23345495
theorem B10375775 : Blo 2049435 10375775 := bstep (se 1 (by rfl) ⟨7781831, by rfl⟩ : syracuseStep 10375775 = 15563663) B15563663
theorem B6917183 : Blo 2049435 6917183 := bstep (se 1 (by rfl) ⟨5187887, by rfl⟩ : syracuseStep 6917183 = 10375775) B10375775
theorem B4611455 : Blo 2049435 4611455 := bstep (se 1 (by rfl) ⟨3458591, by rfl⟩ : syracuseStep 4611455 = 6917183) B6917183
theorem B3074303 : Blo 2049435 3074303 := bstep (se 1 (by rfl) ⟨2305727, by rfl⟩ : syracuseStep 3074303 = 4611455) B4611455
theorem B2049535 : Blo 2049435 2049535 := bstep (se 1 (by rfl) ⟨1537151, by rfl⟩ : syracuseStep 2049535 = 3074303) B3074303
theorem B3074309 : Blo 2049435 3074309 := bbase (se 4 (by rfl) ⟨288216, by rfl⟩ : syracuseStep 3074309 = 576433) (by norm_num)
theorem B2049539 : Blo 2049435 2049539 := bstep (se 1 (by rfl) ⟨1537154, by rfl⟩ : syracuseStep 2049539 = 3074309) B3074309
theorem B3458605 : Blo 2049435 3458605 := bbase (se 3 (by rfl) ⟨648488, by rfl⟩ : syracuseStep 3458605 = 1296977) (by norm_num)
theorem B4611473 : Blo 2049435 4611473 := bstep (se 2 (by rfl) ⟨1729302, by rfl⟩ : syracuseStep 4611473 = 3458605) B3458605
theorem B3074315 : Blo 2049435 3074315 := bstep (se 1 (by rfl) ⟨2305736, by rfl⟩ : syracuseStep 3074315 = 4611473) B4611473
theorem B2049543 : Blo 2049435 2049543 := bstep (se 1 (by rfl) ⟨1537157, by rfl⟩ : syracuseStep 2049543 = 3074315) B3074315
theorem B2305741 : Blo 2049435 2305741 := bbase (se 3 (by rfl) ⟨432326, by rfl⟩ : syracuseStep 2305741 = 864653) (by norm_num)
theorem B3074321 : Blo 2049435 3074321 := bstep (se 2 (by rfl) ⟨1152870, by rfl⟩ : syracuseStep 3074321 = 2305741) B2305741
theorem B2049547 : Blo 2049435 2049547 := bstep (se 1 (by rfl) ⟨1537160, by rfl⟩ : syracuseStep 2049547 = 3074321) B3074321
theorem B6917237 : Blo 2049435 6917237 := bbase (se 5 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 6917237 = 648491) (by norm_num)
theorem B4611491 : Blo 2049435 4611491 := bstep (se 1 (by rfl) ⟨3458618, by rfl⟩ : syracuseStep 4611491 = 6917237) B6917237
theorem B3074327 : Blo 2049435 3074327 := bstep (se 1 (by rfl) ⟨2305745, by rfl⟩ : syracuseStep 3074327 = 4611491) B4611491
theorem B2049551 : Blo 2049435 2049551 := bstep (se 1 (by rfl) ⟨1537163, by rfl⟩ : syracuseStep 2049551 = 3074327) B3074327
theorem B3074333 : Blo 2049435 3074333 := bbase (se 3 (by rfl) ⟨576437, by rfl⟩ : syracuseStep 3074333 = 1152875) (by norm_num)
theorem B2049555 : Blo 2049435 2049555 := bstep (se 1 (by rfl) ⟨1537166, by rfl⟩ : syracuseStep 2049555 = 3074333) B3074333
theorem B4611509 : Blo 2049435 4611509 := bbase (se 5 (by rfl) ⟨216164, by rfl⟩ : syracuseStep 4611509 = 432329) (by norm_num)
theorem B3074339 : Blo 2049435 3074339 := bstep (se 1 (by rfl) ⟨2305754, by rfl⟩ : syracuseStep 3074339 = 4611509) B4611509
theorem B2049559 : Blo 2049435 2049559 := bstep (se 1 (by rfl) ⟨1537169, by rfl⟩ : syracuseStep 2049559 = 3074339) B3074339
theorem B4377341 : Blo 2049435 4377341 := bbase (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) (by norm_num)
theorem B11672909 : Blo 2049435 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B7781939 : Blo 2049435 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B5187959 : Blo 2049435 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B3458639 : Blo 2049435 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B2305759 : Blo 2049435 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B3074345 : Blo 2049435 3074345 := bstep (se 2 (by rfl) ⟨1152879, by rfl⟩ : syracuseStep 3074345 = 2305759) B2305759
theorem B2049563 : Blo 2049435 2049563 := bstep (se 1 (by rfl) ⟨1537172, by rfl⟩ : syracuseStep 2049563 = 3074345) B3074345
theorem B4377349 : Blo 2049435 4377349 := bbase (se 4 (by rfl) ⟨410376, by rfl⟩ : syracuseStep 4377349 = 820753) (by norm_num)
theorem B5836465 : Blo 2049435 5836465 := bstep (se 2 (by rfl) ⟨2188674, by rfl⟩ : syracuseStep 5836465 = 4377349) B4377349
theorem B7781953 : Blo 2049435 7781953 := bstep (se 2 (by rfl) ⟨2918232, by rfl⟩ : syracuseStep 7781953 = 5836465) B5836465
theorem B10375937 : Blo 2049435 10375937 := bstep (se 2 (by rfl) ⟨3890976, by rfl⟩ : syracuseStep 10375937 = 7781953) B7781953
theorem B6917291 : Blo 2049435 6917291 := bstep (se 1 (by rfl) ⟨5187968, by rfl⟩ : syracuseStep 6917291 = 10375937) B10375937
theorem B4611527 : Blo 2049435 4611527 := bstep (se 1 (by rfl) ⟨3458645, by rfl⟩ : syracuseStep 4611527 = 6917291) B6917291
theorem B3074351 : Blo 2049435 3074351 := bstep (se 1 (by rfl) ⟨2305763, by rfl⟩ : syracuseStep 3074351 = 4611527) B4611527
theorem B2049567 : Blo 2049435 2049567 := bstep (se 1 (by rfl) ⟨1537175, by rfl⟩ : syracuseStep 2049567 = 3074351) B3074351
theorem B3074357 : Blo 2049435 3074357 := bbase (se 5 (by rfl) ⟨144110, by rfl⟩ : syracuseStep 3074357 = 288221) (by norm_num)
theorem B2049571 : Blo 2049435 2049571 := bstep (se 1 (by rfl) ⟨1537178, by rfl⟩ : syracuseStep 2049571 = 3074357) B3074357
theorem B5187989 : Blo 2049435 5187989 := bbase (se 6 (by rfl) ⟨121593, by rfl⟩ : syracuseStep 5187989 = 243187) (by norm_num)
theorem B3458659 : Blo 2049435 3458659 := bstep (se 1 (by rfl) ⟨2593994, by rfl⟩ : syracuseStep 3458659 = 5187989) B5187989
theorem B4611545 : Blo 2049435 4611545 := bstep (se 2 (by rfl) ⟨1729329, by rfl⟩ : syracuseStep 4611545 = 3458659) B3458659
theorem B3074363 : Blo 2049435 3074363 := bstep (se 1 (by rfl) ⟨2305772, by rfl⟩ : syracuseStep 3074363 = 4611545) B4611545
theorem B2049575 : Blo 2049435 2049575 := bstep (se 1 (by rfl) ⟨1537181, by rfl⟩ : syracuseStep 2049575 = 3074363) B3074363
theorem B2305777 : Blo 2049435 2305777 := bbase (se 2 (by rfl) ⟨864666, by rfl⟩ : syracuseStep 2305777 = 1729333) (by norm_num)
theorem B3074369 : Blo 2049435 3074369 := bstep (se 2 (by rfl) ⟨1152888, by rfl⟩ : syracuseStep 3074369 = 2305777) B2305777
theorem B2049579 : Blo 2049435 2049579 := bstep (se 1 (by rfl) ⟨1537184, by rfl⟩ : syracuseStep 2049579 = 3074369) B3074369
theorem B9348965 : Blo 2049435 9348965 := bbase (se 4 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 9348965 = 1752931) (by norm_num)
theorem B6232643 : Blo 2049435 6232643 := bstep (se 1 (by rfl) ⟨4674482, by rfl⟩ : syracuseStep 6232643 = 9348965) B9348965
theorem B4155095 : Blo 2049435 4155095 := bstep (se 1 (by rfl) ⟨3116321, by rfl⟩ : syracuseStep 4155095 = 6232643) B6232643
theorem B11080253 : Blo 2049435 11080253 := bstep (se 3 (by rfl) ⟨2077547, by rfl⟩ : syracuseStep 11080253 = 4155095) B4155095
theorem B29547341 : Blo 2049435 29547341 := bstep (se 3 (by rfl) ⟨5540126, by rfl⟩ : syracuseStep 29547341 = 11080253) B11080253
theorem B19698227 : Blo 2049435 19698227 := bstep (se 1 (by rfl) ⟨14773670, by rfl⟩ : syracuseStep 19698227 = 29547341) B29547341
theorem B13132151 : Blo 2049435 13132151 := bstep (se 1 (by rfl) ⟨9849113, by rfl⟩ : syracuseStep 13132151 = 19698227) B19698227
theorem B8754767 : Blo 2049435 8754767 := bstep (se 1 (by rfl) ⟨6566075, by rfl⟩ : syracuseStep 8754767 = 13132151) B13132151
theorem B5836511 : Blo 2049435 5836511 := bstep (se 1 (by rfl) ⟨4377383, by rfl⟩ : syracuseStep 5836511 = 8754767) B8754767
theorem B3891007 : Blo 2049435 3891007 := bstep (se 1 (by rfl) ⟨2918255, by rfl⟩ : syracuseStep 3891007 = 5836511) B5836511
theorem B5188009 : Blo 2049435 5188009 := bstep (se 2 (by rfl) ⟨1945503, by rfl⟩ : syracuseStep 5188009 = 3891007) B3891007
theorem B6917345 : Blo 2049435 6917345 := bstep (se 2 (by rfl) ⟨2594004, by rfl⟩ : syracuseStep 6917345 = 5188009) B5188009
theorem B4611563 : Blo 2049435 4611563 := bstep (se 1 (by rfl) ⟨3458672, by rfl⟩ : syracuseStep 4611563 = 6917345) B6917345
theorem B3074375 : Blo 2049435 3074375 := bstep (se 1 (by rfl) ⟨2305781, by rfl⟩ : syracuseStep 3074375 = 4611563) B4611563
theorem B2049583 : Blo 2049435 2049583 := bstep (se 1 (by rfl) ⟨1537187, by rfl⟩ : syracuseStep 2049583 = 3074375) B3074375
theorem B3074381 : Blo 2049435 3074381 := bbase (se 3 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 3074381 = 1152893) (by norm_num)
theorem B2049587 : Blo 2049435 2049587 := bstep (se 1 (by rfl) ⟨1537190, by rfl⟩ : syracuseStep 2049587 = 3074381) B3074381
theorem B4611581 : Blo 2049435 4611581 := bbase (se 3 (by rfl) ⟨864671, by rfl⟩ : syracuseStep 4611581 = 1729343) (by norm_num)
theorem B3074387 : Blo 2049435 3074387 := bstep (se 1 (by rfl) ⟨2305790, by rfl⟩ : syracuseStep 3074387 = 4611581) B4611581
theorem B2049591 : Blo 2049435 2049591 := bstep (se 1 (by rfl) ⟨1537193, by rfl⟩ : syracuseStep 2049591 = 3074387) B3074387
theorem B3458693 : Blo 2049435 3458693 := bbase (se 4 (by rfl) ⟨324252, by rfl⟩ : syracuseStep 3458693 = 648505) (by norm_num)
theorem B2305795 : Blo 2049435 2305795 := bstep (se 1 (by rfl) ⟨1729346, by rfl⟩ : syracuseStep 2305795 = 3458693) B3458693
theorem B3074393 : Blo 2049435 3074393 := bstep (se 2 (by rfl) ⟨1152897, by rfl⟩ : syracuseStep 3074393 = 2305795) B2305795
theorem B2049595 : Blo 2049435 2049595 := bstep (se 1 (by rfl) ⟨1537196, by rfl⟩ : syracuseStep 2049595 = 3074393) B3074393
theorem B15564149 : Blo 2049435 15564149 := bbase (se 5 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 15564149 = 1459139) (by norm_num)
theorem B10376099 : Blo 2049435 10376099 := bstep (se 1 (by rfl) ⟨7782074, by rfl⟩ : syracuseStep 10376099 = 15564149) B15564149
theorem B6917399 : Blo 2049435 6917399 := bstep (se 1 (by rfl) ⟨5188049, by rfl⟩ : syracuseStep 6917399 = 10376099) B10376099
theorem B4611599 : Blo 2049435 4611599 := bstep (se 1 (by rfl) ⟨3458699, by rfl⟩ : syracuseStep 4611599 = 6917399) B6917399
theorem B3074399 : Blo 2049435 3074399 := bstep (se 1 (by rfl) ⟨2305799, by rfl⟩ : syracuseStep 3074399 = 4611599) B4611599
theorem B2049599 : Blo 2049435 2049599 := bstep (se 1 (by rfl) ⟨1537199, by rfl⟩ : syracuseStep 2049599 = 3074399) B3074399
theorem B3074405 : Blo 2049435 3074405 := bbase (se 4 (by rfl) ⟨288225, by rfl⟩ : syracuseStep 3074405 = 576451) (by norm_num)
theorem B2049603 : Blo 2049435 2049603 := bstep (se 1 (by rfl) ⟨1537202, by rfl⟩ : syracuseStep 2049603 = 3074405) B3074405
theorem B3891053 : Blo 2049435 3891053 := bbase (se 3 (by rfl) ⟨729572, by rfl⟩ : syracuseStep 3891053 = 1459145) (by norm_num)
theorem B2594035 : Blo 2049435 2594035 := bstep (se 1 (by rfl) ⟨1945526, by rfl⟩ : syracuseStep 2594035 = 3891053) B3891053
theorem B3458713 : Blo 2049435 3458713 := bstep (se 2 (by rfl) ⟨1297017, by rfl⟩ : syracuseStep 3458713 = 2594035) B2594035
theorem B4611617 : Blo 2049435 4611617 := bstep (se 2 (by rfl) ⟨1729356, by rfl⟩ : syracuseStep 4611617 = 3458713) B3458713
theorem B3074411 : Blo 2049435 3074411 := bstep (se 1 (by rfl) ⟨2305808, by rfl⟩ : syracuseStep 3074411 = 4611617) B4611617
theorem B2049607 : Blo 2049435 2049607 := bstep (se 1 (by rfl) ⟨1537205, by rfl⟩ : syracuseStep 2049607 = 3074411) B3074411
theorem B2305813 : Blo 2049435 2305813 := bbase (se 6 (by rfl) ⟨54042, by rfl⟩ : syracuseStep 2305813 = 108085) (by norm_num)
theorem B3074417 : Blo 2049435 3074417 := bstep (se 2 (by rfl) ⟨1152906, by rfl⟩ : syracuseStep 3074417 = 2305813) B2305813
theorem B2049611 : Blo 2049435 2049611 := bstep (se 1 (by rfl) ⟨1537208, by rfl⟩ : syracuseStep 2049611 = 3074417) B3074417
theorem B2594045 : Blo 2049435 2594045 := bbase (se 3 (by rfl) ⟨486383, by rfl⟩ : syracuseStep 2594045 = 972767) (by norm_num)
theorem B6917453 : Blo 2049435 6917453 := bstep (se 3 (by rfl) ⟨1297022, by rfl⟩ : syracuseStep 6917453 = 2594045) B2594045
theorem B4611635 : Blo 2049435 4611635 := bstep (se 1 (by rfl) ⟨3458726, by rfl⟩ : syracuseStep 4611635 = 6917453) B6917453
theorem B3074423 : Blo 2049435 3074423 := bstep (se 1 (by rfl) ⟨2305817, by rfl⟩ : syracuseStep 3074423 = 4611635) B4611635
theorem B2049615 : Blo 2049435 2049615 := bstep (se 1 (by rfl) ⟨1537211, by rfl⟩ : syracuseStep 2049615 = 3074423) B3074423
theorem B3074429 : Blo 2049435 3074429 := bbase (se 3 (by rfl) ⟨576455, by rfl⟩ : syracuseStep 3074429 = 1152911) (by norm_num)
theorem B2049619 : Blo 2049435 2049619 := bstep (se 1 (by rfl) ⟨1537214, by rfl⟩ : syracuseStep 2049619 = 3074429) B3074429
theorem B4611653 : Blo 2049435 4611653 := bbase (se 4 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 4611653 = 864685) (by norm_num)
theorem B3074435 : Blo 2049435 3074435 := bstep (se 1 (by rfl) ⟨2305826, by rfl⟩ : syracuseStep 3074435 = 4611653) B4611653
theorem B2049623 : Blo 2049435 2049623 := bstep (se 1 (by rfl) ⟨1537217, by rfl⟩ : syracuseStep 2049623 = 3074435) B3074435
theorem B3283109 : Blo 2049435 3283109 := bbase (se 4 (by rfl) ⟨307791, by rfl⟩ : syracuseStep 3283109 = 615583) (by norm_num)
theorem B2188739 : Blo 2049435 2188739 := bstep (se 1 (by rfl) ⟨1641554, by rfl⟩ : syracuseStep 2188739 = 3283109) B3283109
theorem B5836637 : Blo 2049435 5836637 := bstep (se 3 (by rfl) ⟨1094369, by rfl⟩ : syracuseStep 5836637 = 2188739) B2188739
theorem B3891091 : Blo 2049435 3891091 := bstep (se 1 (by rfl) ⟨2918318, by rfl⟩ : syracuseStep 3891091 = 5836637) B5836637
theorem B5188121 : Blo 2049435 5188121 := bstep (se 2 (by rfl) ⟨1945545, by rfl⟩ : syracuseStep 5188121 = 3891091) B3891091
theorem B3458747 : Blo 2049435 3458747 := bstep (se 1 (by rfl) ⟨2594060, by rfl⟩ : syracuseStep 3458747 = 5188121) B5188121
theorem B2305831 : Blo 2049435 2305831 := bstep (se 1 (by rfl) ⟨1729373, by rfl⟩ : syracuseStep 2305831 = 3458747) B3458747
theorem B3074441 : Blo 2049435 3074441 := bstep (se 2 (by rfl) ⟨1152915, by rfl⟩ : syracuseStep 3074441 = 2305831) B2305831
theorem B2049627 : Blo 2049435 2049627 := bstep (se 1 (by rfl) ⟨1537220, by rfl⟩ : syracuseStep 2049627 = 3074441) B3074441
theorem B10376261 : Blo 2049435 10376261 := bbase (se 4 (by rfl) ⟨972774, by rfl⟩ : syracuseStep 10376261 = 1945549) (by norm_num)
theorem B6917507 : Blo 2049435 6917507 := bstep (se 1 (by rfl) ⟨5188130, by rfl⟩ : syracuseStep 6917507 = 10376261) B10376261
theorem B4611671 : Blo 2049435 4611671 := bstep (se 1 (by rfl) ⟨3458753, by rfl⟩ : syracuseStep 4611671 = 6917507) B6917507
theorem B3074447 : Blo 2049435 3074447 := bstep (se 1 (by rfl) ⟨2305835, by rfl⟩ : syracuseStep 3074447 = 4611671) B4611671
theorem B2049631 : Blo 2049435 2049631 := bstep (se 1 (by rfl) ⟨1537223, by rfl⟩ : syracuseStep 2049631 = 3074447) B3074447
theorem B3074453 : Blo 2049435 3074453 := bbase (se 6 (by rfl) ⟨72057, by rfl⟩ : syracuseStep 3074453 = 144115) (by norm_num)
theorem B2049635 : Blo 2049435 2049635 := bstep (se 1 (by rfl) ⟨1537226, by rfl⟩ : syracuseStep 2049635 = 3074453) B3074453
theorem B2337305 : Blo 2049435 2337305 := bbase (se 2 (by rfl) ⟨876489, by rfl⟩ : syracuseStep 2337305 = 1752979) (by norm_num)
theorem B24931253 : Blo 2049435 24931253 := bstep (se 5 (by rfl) ⟨1168652, by rfl⟩ : syracuseStep 24931253 = 2337305) B2337305
theorem B16620835 : Blo 2049435 16620835 := bstep (se 1 (by rfl) ⟨12465626, by rfl⟩ : syracuseStep 16620835 = 24931253) B24931253
theorem B22161113 : Blo 2049435 22161113 := bstep (se 2 (by rfl) ⟨8310417, by rfl⟩ : syracuseStep 22161113 = 16620835) B16620835
theorem B14774075 : Blo 2049435 14774075 := bstep (se 1 (by rfl) ⟨11080556, by rfl⟩ : syracuseStep 14774075 = 22161113) B22161113
theorem B9849383 : Blo 2049435 9849383 := bstep (se 1 (by rfl) ⟨7387037, by rfl⟩ : syracuseStep 9849383 = 14774075) B14774075
theorem B6566255 : Blo 2049435 6566255 := bstep (se 1 (by rfl) ⟨4924691, by rfl⟩ : syracuseStep 6566255 = 9849383) B9849383
theorem B4377503 : Blo 2049435 4377503 := bstep (se 1 (by rfl) ⟨3283127, by rfl⟩ : syracuseStep 4377503 = 6566255) B6566255
theorem B11673341 : Blo 2049435 11673341 := bstep (se 3 (by rfl) ⟨2188751, by rfl⟩ : syracuseStep 11673341 = 4377503) B4377503
theorem B7782227 : Blo 2049435 7782227 := bstep (se 1 (by rfl) ⟨5836670, by rfl⟩ : syracuseStep 7782227 = 11673341) B11673341
theorem B5188151 : Blo 2049435 5188151 := bstep (se 1 (by rfl) ⟨3891113, by rfl⟩ : syracuseStep 5188151 = 7782227) B7782227
theorem B3458767 : Blo 2049435 3458767 := bstep (se 1 (by rfl) ⟨2594075, by rfl⟩ : syracuseStep 3458767 = 5188151) B5188151
theorem B4611689 : Blo 2049435 4611689 := bstep (se 2 (by rfl) ⟨1729383, by rfl⟩ : syracuseStep 4611689 = 3458767) B3458767
theorem B3074459 : Blo 2049435 3074459 := bstep (se 1 (by rfl) ⟨2305844, by rfl⟩ : syracuseStep 3074459 = 4611689) B4611689
theorem B2049639 : Blo 2049435 2049639 := bstep (se 1 (by rfl) ⟨1537229, by rfl⟩ : syracuseStep 2049639 = 3074459) B3074459
theorem B2305849 : Blo 2049435 2305849 := bbase (se 2 (by rfl) ⟨864693, by rfl⟩ : syracuseStep 2305849 = 1729387) (by norm_num)
theorem B3074465 : Blo 2049435 3074465 := bstep (se 2 (by rfl) ⟨1152924, by rfl⟩ : syracuseStep 3074465 = 2305849) B2305849
theorem B2049643 : Blo 2049435 2049643 := bstep (se 1 (by rfl) ⟨1537232, by rfl⟩ : syracuseStep 2049643 = 3074465) B3074465
theorem B5836693 : Blo 2049435 5836693 := bbase (se 6 (by rfl) ⟨136797, by rfl⟩ : syracuseStep 5836693 = 273595) (by norm_num)
theorem B7782257 : Blo 2049435 7782257 := bstep (se 2 (by rfl) ⟨2918346, by rfl⟩ : syracuseStep 7782257 = 5836693) B5836693
theorem B5188171 : Blo 2049435 5188171 := bstep (se 1 (by rfl) ⟨3891128, by rfl⟩ : syracuseStep 5188171 = 7782257) B7782257
theorem B6917561 : Blo 2049435 6917561 := bstep (se 2 (by rfl) ⟨2594085, by rfl⟩ : syracuseStep 6917561 = 5188171) B5188171
theorem B4611707 : Blo 2049435 4611707 := bstep (se 1 (by rfl) ⟨3458780, by rfl⟩ : syracuseStep 4611707 = 6917561) B6917561
theorem B3074471 : Blo 2049435 3074471 := bstep (se 1 (by rfl) ⟨2305853, by rfl⟩ : syracuseStep 3074471 = 4611707) B4611707
theorem B2049647 : Blo 2049435 2049647 := bstep (se 1 (by rfl) ⟨1537235, by rfl⟩ : syracuseStep 2049647 = 3074471) B3074471
theorem B3074477 : Blo 2049435 3074477 := bbase (se 3 (by rfl) ⟨576464, by rfl⟩ : syracuseStep 3074477 = 1152929) (by norm_num)
theorem B2049651 : Blo 2049435 2049651 := bstep (se 1 (by rfl) ⟨1537238, by rfl⟩ : syracuseStep 2049651 = 3074477) B3074477
theorem B4611725 : Blo 2049435 4611725 := bbase (se 3 (by rfl) ⟨864698, by rfl⟩ : syracuseStep 4611725 = 1729397) (by norm_num)
theorem B3074483 : Blo 2049435 3074483 := bstep (se 1 (by rfl) ⟨2305862, by rfl⟩ : syracuseStep 3074483 = 4611725) B4611725
theorem B2049655 : Blo 2049435 2049655 := bstep (se 1 (by rfl) ⟨1537241, by rfl⟩ : syracuseStep 2049655 = 3074483) B3074483
theorem B2594101 : Blo 2049435 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B3458801 : Blo 2049435 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B2305867 : Blo 2049435 2305867 := bstep (se 1 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 2305867 = 3458801) B3458801
theorem B3074489 : Blo 2049435 3074489 := bstep (se 2 (by rfl) ⟨1152933, by rfl⟩ : syracuseStep 3074489 = 2305867) B2305867
theorem B2049659 : Blo 2049435 2049659 := bstep (se 1 (by rfl) ⟨1537244, by rfl⟩ : syracuseStep 2049659 = 3074489) B3074489
theorem B9476885 : Blo 2049435 9476885 := bbase (se 6 (by rfl) ⟨222114, by rfl⟩ : syracuseStep 9476885 = 444229) (by norm_num)
theorem B6317923 : Blo 2049435 6317923 := bstep (se 1 (by rfl) ⟨4738442, by rfl⟩ : syracuseStep 6317923 = 9476885) B9476885
theorem B8423897 : Blo 2049435 8423897 := bstep (se 2 (by rfl) ⟨3158961, by rfl⟩ : syracuseStep 8423897 = 6317923) B6317923
theorem B22463725 : Blo 2049435 22463725 := bstep (se 3 (by rfl) ⟨4211948, by rfl⟩ : syracuseStep 22463725 = 8423897) B8423897
theorem B29951633 : Blo 2049435 29951633 := bstep (se 2 (by rfl) ⟨11231862, by rfl⟩ : syracuseStep 29951633 = 22463725) B22463725
theorem B19967755 : Blo 2049435 19967755 := bstep (se 1 (by rfl) ⟨14975816, by rfl⟩ : syracuseStep 19967755 = 29951633) B29951633
theorem B26623673 : Blo 2049435 26623673 := bstep (se 2 (by rfl) ⟨9983877, by rfl⟩ : syracuseStep 26623673 = 19967755) B19967755
theorem B17749115 : Blo 2049435 17749115 := bstep (se 1 (by rfl) ⟨13311836, by rfl⟩ : syracuseStep 17749115 = 26623673) B26623673
theorem B11832743 : Blo 2049435 11832743 := bstep (se 1 (by rfl) ⟨8874557, by rfl⟩ : syracuseStep 11832743 = 17749115) B17749115
theorem B31553981 : Blo 2049435 31553981 := bstep (se 3 (by rfl) ⟨5916371, by rfl⟩ : syracuseStep 31553981 = 11832743) B11832743
theorem B21035987 : Blo 2049435 21035987 := bstep (se 1 (by rfl) ⟨15776990, by rfl⟩ : syracuseStep 21035987 = 31553981) B31553981
theorem B14023991 : Blo 2049435 14023991 := bstep (se 1 (by rfl) ⟨10517993, by rfl⟩ : syracuseStep 14023991 = 21035987) B21035987
theorem B9349327 : Blo 2049435 9349327 := bstep (se 1 (by rfl) ⟨7011995, by rfl⟩ : syracuseStep 9349327 = 14023991) B14023991
theorem B49863077 : Blo 2049435 49863077 := bstep (se 4 (by rfl) ⟨4674663, by rfl⟩ : syracuseStep 49863077 = 9349327) B9349327
theorem B33242051 : Blo 2049435 33242051 := bstep (se 1 (by rfl) ⟨24931538, by rfl⟩ : syracuseStep 33242051 = 49863077) B49863077
theorem B22161367 : Blo 2049435 22161367 := bstep (se 1 (by rfl) ⟨16621025, by rfl⟩ : syracuseStep 22161367 = 33242051) B33242051
theorem B29548489 : Blo 2049435 29548489 := bstep (se 2 (by rfl) ⟨11080683, by rfl⟩ : syracuseStep 29548489 = 22161367) B22161367
theorem B39397985 : Blo 2049435 39397985 := bstep (se 2 (by rfl) ⟨14774244, by rfl⟩ : syracuseStep 39397985 = 29548489) B29548489
theorem B26265323 : Blo 2049435 26265323 := bstep (se 1 (by rfl) ⟨19698992, by rfl⟩ : syracuseStep 26265323 = 39397985) B39397985
theorem B17510215 : Blo 2049435 17510215 := bstep (se 1 (by rfl) ⟨13132661, by rfl⟩ : syracuseStep 17510215 = 26265323) B26265323
theorem B23346953 : Blo 2049435 23346953 := bstep (se 2 (by rfl) ⟨8755107, by rfl⟩ : syracuseStep 23346953 = 17510215) B17510215
theorem B15564635 : Blo 2049435 15564635 := bstep (se 1 (by rfl) ⟨11673476, by rfl⟩ : syracuseStep 15564635 = 23346953) B23346953
theorem B10376423 : Blo 2049435 10376423 := bstep (se 1 (by rfl) ⟨7782317, by rfl⟩ : syracuseStep 10376423 = 15564635) B15564635
theorem B6917615 : Blo 2049435 6917615 := bstep (se 1 (by rfl) ⟨5188211, by rfl⟩ : syracuseStep 6917615 = 10376423) B10376423
theorem B4611743 : Blo 2049435 4611743 := bstep (se 1 (by rfl) ⟨3458807, by rfl⟩ : syracuseStep 4611743 = 6917615) B6917615
theorem B3074495 : Blo 2049435 3074495 := bstep (se 1 (by rfl) ⟨2305871, by rfl⟩ : syracuseStep 3074495 = 4611743) B4611743
theorem B2049663 : Blo 2049435 2049663 := bstep (se 1 (by rfl) ⟨1537247, by rfl⟩ : syracuseStep 2049663 = 3074495) B3074495
theorem B3074501 : Blo 2049435 3074501 := bbase (se 4 (by rfl) ⟨288234, by rfl⟩ : syracuseStep 3074501 = 576469) (by norm_num)
theorem B2049667 : Blo 2049435 2049667 := bstep (se 1 (by rfl) ⟨1537250, by rfl⟩ : syracuseStep 2049667 = 3074501) B3074501
theorem B3458821 : Blo 2049435 3458821 := bbase (se 4 (by rfl) ⟨324264, by rfl⟩ : syracuseStep 3458821 = 648529) (by norm_num)
theorem B4611761 : Blo 2049435 4611761 := bstep (se 2 (by rfl) ⟨1729410, by rfl⟩ : syracuseStep 4611761 = 3458821) B3458821
theorem B3074507 : Blo 2049435 3074507 := bstep (se 1 (by rfl) ⟨2305880, by rfl⟩ : syracuseStep 3074507 = 4611761) B4611761
theorem B2049671 : Blo 2049435 2049671 := bstep (se 1 (by rfl) ⟨1537253, by rfl⟩ : syracuseStep 2049671 = 3074507) B3074507
theorem B2305885 : Blo 2049435 2305885 := bbase (se 3 (by rfl) ⟨432353, by rfl⟩ : syracuseStep 2305885 = 864707) (by norm_num)
theorem B3074513 : Blo 2049435 3074513 := bstep (se 2 (by rfl) ⟨1152942, by rfl⟩ : syracuseStep 3074513 = 2305885) B2305885
theorem B2049675 : Blo 2049435 2049675 := bstep (se 1 (by rfl) ⟨1537256, by rfl⟩ : syracuseStep 2049675 = 3074513) B3074513
theorem B6917669 : Blo 2049435 6917669 := bbase (se 4 (by rfl) ⟨648531, by rfl⟩ : syracuseStep 6917669 = 1297063) (by norm_num)
theorem B4611779 : Blo 2049435 4611779 := bstep (se 1 (by rfl) ⟨3458834, by rfl⟩ : syracuseStep 4611779 = 6917669) B6917669
theorem B3074519 : Blo 2049435 3074519 := bstep (se 1 (by rfl) ⟨2305889, by rfl⟩ : syracuseStep 3074519 = 4611779) B4611779
theorem B2049679 : Blo 2049435 2049679 := bstep (se 1 (by rfl) ⟨1537259, by rfl⟩ : syracuseStep 2049679 = 3074519) B3074519
theorem B3074525 : Blo 2049435 3074525 := bbase (se 3 (by rfl) ⟨576473, by rfl⟩ : syracuseStep 3074525 = 1152947) (by norm_num)
theorem B2049683 : Blo 2049435 2049683 := bstep (se 1 (by rfl) ⟨1537262, by rfl⟩ : syracuseStep 2049683 = 3074525) B3074525
theorem B4611797 : Blo 2049435 4611797 := bbase (se 7 (by rfl) ⟨54044, by rfl⟩ : syracuseStep 4611797 = 108089) (by norm_num)
theorem B3074531 : Blo 2049435 3074531 := bstep (se 1 (by rfl) ⟨2305898, by rfl⟩ : syracuseStep 3074531 = 4611797) B4611797
theorem B2049687 : Blo 2049435 2049687 := bstep (se 1 (by rfl) ⟨1537265, by rfl⟩ : syracuseStep 2049687 = 3074531) B3074531
theorem B3693613 : Blo 2049435 3693613 := bbase (se 3 (by rfl) ⟨692552, by rfl⟩ : syracuseStep 3693613 = 1385105) (by norm_num)
theorem B4924817 : Blo 2049435 4924817 := bstep (se 2 (by rfl) ⟨1846806, by rfl⟩ : syracuseStep 4924817 = 3693613) B3693613
theorem B3283211 : Blo 2049435 3283211 := bstep (se 1 (by rfl) ⟨2462408, by rfl⟩ : syracuseStep 3283211 = 4924817) B4924817
theorem B8755229 : Blo 2049435 8755229 := bstep (se 3 (by rfl) ⟨1641605, by rfl⟩ : syracuseStep 8755229 = 3283211) B3283211
theorem B5836819 : Blo 2049435 5836819 := bstep (se 1 (by rfl) ⟨4377614, by rfl⟩ : syracuseStep 5836819 = 8755229) B8755229
theorem B7782425 : Blo 2049435 7782425 := bstep (se 2 (by rfl) ⟨2918409, by rfl⟩ : syracuseStep 7782425 = 5836819) B5836819
theorem B5188283 : Blo 2049435 5188283 := bstep (se 1 (by rfl) ⟨3891212, by rfl⟩ : syracuseStep 5188283 = 7782425) B7782425
theorem B3458855 : Blo 2049435 3458855 := bstep (se 1 (by rfl) ⟨2594141, by rfl⟩ : syracuseStep 3458855 = 5188283) B5188283
theorem B2305903 : Blo 2049435 2305903 := bstep (se 1 (by rfl) ⟨1729427, by rfl⟩ : syracuseStep 2305903 = 3458855) B3458855
theorem B3074537 : Blo 2049435 3074537 := bstep (se 2 (by rfl) ⟨1152951, by rfl⟩ : syracuseStep 3074537 = 2305903) B2305903
theorem B2049691 : Blo 2049435 2049691 := bstep (se 1 (by rfl) ⟨1537268, by rfl⟩ : syracuseStep 2049691 = 3074537) B3074537
theorem B2077661 : Blo 2049435 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B5540429 : Blo 2049435 5540429 := bstep (se 3 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 5540429 = 2077661) B2077661
theorem B3693619 : Blo 2049435 3693619 := bstep (se 1 (by rfl) ⟨2770214, by rfl⟩ : syracuseStep 3693619 = 5540429) B5540429
theorem B19699301 : Blo 2049435 19699301 := bstep (se 4 (by rfl) ⟨1846809, by rfl⟩ : syracuseStep 19699301 = 3693619) B3693619
theorem B13132867 : Blo 2049435 13132867 := bstep (se 1 (by rfl) ⟨9849650, by rfl⟩ : syracuseStep 13132867 = 19699301) B19699301
theorem B17510489 : Blo 2049435 17510489 := bstep (se 2 (by rfl) ⟨6566433, by rfl⟩ : syracuseStep 17510489 = 13132867) B13132867
theorem B11673659 : Blo 2049435 11673659 := bstep (se 1 (by rfl) ⟨8755244, by rfl⟩ : syracuseStep 11673659 = 17510489) B17510489
theorem B7782439 : Blo 2049435 7782439 := bstep (se 1 (by rfl) ⟨5836829, by rfl⟩ : syracuseStep 7782439 = 11673659) B11673659
theorem B10376585 : Blo 2049435 10376585 := bstep (se 2 (by rfl) ⟨3891219, by rfl⟩ : syracuseStep 10376585 = 7782439) B7782439
theorem B6917723 : Blo 2049435 6917723 := bstep (se 1 (by rfl) ⟨5188292, by rfl⟩ : syracuseStep 6917723 = 10376585) B10376585
theorem B4611815 : Blo 2049435 4611815 := bstep (se 1 (by rfl) ⟨3458861, by rfl⟩ : syracuseStep 4611815 = 6917723) B6917723
theorem B3074543 : Blo 2049435 3074543 := bstep (se 1 (by rfl) ⟨2305907, by rfl⟩ : syracuseStep 3074543 = 4611815) B4611815
theorem B2049695 : Blo 2049435 2049695 := bstep (se 1 (by rfl) ⟨1537271, by rfl⟩ : syracuseStep 2049695 = 3074543) B3074543
theorem B3074549 : Blo 2049435 3074549 := bbase (se 5 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 3074549 = 288239) (by norm_num)
theorem B2049699 : Blo 2049435 2049699 := bstep (se 1 (by rfl) ⟨1537274, by rfl⟩ : syracuseStep 2049699 = 3074549) B3074549
theorem B5836853 : Blo 2049435 5836853 := bbase (se 5 (by rfl) ⟨273602, by rfl⟩ : syracuseStep 5836853 = 547205) (by norm_num)
theorem B3891235 : Blo 2049435 3891235 := bstep (se 1 (by rfl) ⟨2918426, by rfl⟩ : syracuseStep 3891235 = 5836853) B5836853
theorem B5188313 : Blo 2049435 5188313 := bstep (se 2 (by rfl) ⟨1945617, by rfl⟩ : syracuseStep 5188313 = 3891235) B3891235
theorem B3458875 : Blo 2049435 3458875 := bstep (se 1 (by rfl) ⟨2594156, by rfl⟩ : syracuseStep 3458875 = 5188313) B5188313
theorem B4611833 : Blo 2049435 4611833 := bstep (se 2 (by rfl) ⟨1729437, by rfl⟩ : syracuseStep 4611833 = 3458875) B3458875
theorem B3074555 : Blo 2049435 3074555 := bstep (se 1 (by rfl) ⟨2305916, by rfl⟩ : syracuseStep 3074555 = 4611833) B4611833
theorem B2049703 : Blo 2049435 2049703 := bstep (se 1 (by rfl) ⟨1537277, by rfl⟩ : syracuseStep 2049703 = 3074555) B3074555
theorem B2305921 : Blo 2049435 2305921 := bbase (se 2 (by rfl) ⟨864720, by rfl⟩ : syracuseStep 2305921 = 1729441) (by norm_num)
theorem B3074561 : Blo 2049435 3074561 := bstep (se 2 (by rfl) ⟨1152960, by rfl⟩ : syracuseStep 3074561 = 2305921) B2305921
theorem B2049707 : Blo 2049435 2049707 := bstep (se 1 (by rfl) ⟨1537280, by rfl⟩ : syracuseStep 2049707 = 3074561) B3074561
theorem B5188333 : Blo 2049435 5188333 := bbase (se 3 (by rfl) ⟨972812, by rfl⟩ : syracuseStep 5188333 = 1945625) (by norm_num)
theorem B6917777 : Blo 2049435 6917777 := bstep (se 2 (by rfl) ⟨2594166, by rfl⟩ : syracuseStep 6917777 = 5188333) B5188333
theorem B4611851 : Blo 2049435 4611851 := bstep (se 1 (by rfl) ⟨3458888, by rfl⟩ : syracuseStep 4611851 = 6917777) B6917777
theorem B3074567 : Blo 2049435 3074567 := bstep (se 1 (by rfl) ⟨2305925, by rfl⟩ : syracuseStep 3074567 = 4611851) B4611851
theorem B2049711 : Blo 2049435 2049711 := bstep (se 1 (by rfl) ⟨1537283, by rfl⟩ : syracuseStep 2049711 = 3074567) B3074567
theorem B3074573 : Blo 2049435 3074573 := bbase (se 3 (by rfl) ⟨576482, by rfl⟩ : syracuseStep 3074573 = 1152965) (by norm_num)
theorem B2049715 : Blo 2049435 2049715 := bstep (se 1 (by rfl) ⟨1537286, by rfl⟩ : syracuseStep 2049715 = 3074573) B3074573
theorem B4611869 : Blo 2049435 4611869 := bbase (se 3 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 4611869 = 1729451) (by norm_num)
theorem B3074579 : Blo 2049435 3074579 := bstep (se 1 (by rfl) ⟨2305934, by rfl⟩ : syracuseStep 3074579 = 4611869) B4611869
theorem B2049719 : Blo 2049435 2049719 := bstep (se 1 (by rfl) ⟨1537289, by rfl⟩ : syracuseStep 2049719 = 3074579) B3074579
theorem B3458909 : Blo 2049435 3458909 := bbase (se 3 (by rfl) ⟨648545, by rfl⟩ : syracuseStep 3458909 = 1297091) (by norm_num)
theorem B2305939 : Blo 2049435 2305939 := bstep (se 1 (by rfl) ⟨1729454, by rfl⟩ : syracuseStep 2305939 = 3458909) B3458909
theorem B3074585 : Blo 2049435 3074585 := bstep (se 2 (by rfl) ⟨1152969, by rfl⟩ : syracuseStep 3074585 = 2305939) B2305939
theorem B2049723 : Blo 2049435 2049723 := bstep (se 1 (by rfl) ⟨1537292, by rfl⟩ : syracuseStep 2049723 = 3074585) B3074585
theorem B8755381 : Blo 2049435 8755381 := bbase (se 5 (by rfl) ⟨410408, by rfl⟩ : syracuseStep 8755381 = 820817) (by norm_num)
theorem B11673841 : Blo 2049435 11673841 := bstep (se 2 (by rfl) ⟨4377690, by rfl⟩ : syracuseStep 11673841 = 8755381) B8755381
theorem B15565121 : Blo 2049435 15565121 := bstep (se 2 (by rfl) ⟨5836920, by rfl⟩ : syracuseStep 15565121 = 11673841) B11673841
theorem B10376747 : Blo 2049435 10376747 := bstep (se 1 (by rfl) ⟨7782560, by rfl⟩ : syracuseStep 10376747 = 15565121) B15565121
theorem B6917831 : Blo 2049435 6917831 := bstep (se 1 (by rfl) ⟨5188373, by rfl⟩ : syracuseStep 6917831 = 10376747) B10376747
theorem B4611887 : Blo 2049435 4611887 := bstep (se 1 (by rfl) ⟨3458915, by rfl⟩ : syracuseStep 4611887 = 6917831) B6917831
theorem B3074591 : Blo 2049435 3074591 := bstep (se 1 (by rfl) ⟨2305943, by rfl⟩ : syracuseStep 3074591 = 4611887) B4611887
theorem B2049727 : Blo 2049435 2049727 := bstep (se 1 (by rfl) ⟨1537295, by rfl⟩ : syracuseStep 2049727 = 3074591) B3074591
theorem B3074597 : Blo 2049435 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B2049731 : Blo 2049435 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B2594197 : Blo 2049435 2594197 := bbase (se 6 (by rfl) ⟨60801, by rfl⟩ : syracuseStep 2594197 = 121603) (by norm_num)
theorem B3458929 : Blo 2049435 3458929 := bstep (se 2 (by rfl) ⟨1297098, by rfl⟩ : syracuseStep 3458929 = 2594197) B2594197
theorem B4611905 : Blo 2049435 4611905 := bstep (se 2 (by rfl) ⟨1729464, by rfl⟩ : syracuseStep 4611905 = 3458929) B3458929
theorem B3074603 : Blo 2049435 3074603 := bstep (se 1 (by rfl) ⟨2305952, by rfl⟩ : syracuseStep 3074603 = 4611905) B4611905
theorem B2049735 : Blo 2049435 2049735 := bstep (se 1 (by rfl) ⟨1537301, by rfl⟩ : syracuseStep 2049735 = 3074603) B3074603
theorem B2305957 : Blo 2049435 2305957 := bbase (se 4 (by rfl) ⟨216183, by rfl⟩ : syracuseStep 2305957 = 432367) (by norm_num)
theorem B3074609 : Blo 2049435 3074609 := bstep (se 2 (by rfl) ⟨1152978, by rfl⟩ : syracuseStep 3074609 = 2305957) B2305957
theorem B2049739 : Blo 2049435 2049739 := bstep (se 1 (by rfl) ⟨1537304, by rfl⟩ : syracuseStep 2049739 = 3074609) B3074609
theorem B5060245 : Blo 2049435 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B6746993 : Blo 2049435 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B4497995 : Blo 2049435 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B2998663 : Blo 2049435 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B63971477 : Blo 2049435 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B42647651 : Blo 2049435 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B28431767 : Blo 2049435 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B75818045 : Blo 2049435 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B202181453 : Blo 2049435 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B134787635 : Blo 2049435 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B89858423 : Blo 2049435 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B239622461 : Blo 2049435 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B159748307 : Blo 2049435 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B106498871 : Blo 2049435 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B70999247 : Blo 2049435 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B47332831 : Blo 2049435 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B63110441 : Blo 2049435 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B42073627 : Blo 2049435 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B56098169 : Blo 2049435 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B37398779 : Blo 2049435 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B24932519 : Blo 2049435 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B16621679 : Blo 2049435 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B11081119 : Blo 2049435 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B14774825 : Blo 2049435 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B9849883 : Blo 2049435 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B13133177 : Blo 2049435 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B8755451 : Blo 2049435 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B5836967 : Blo 2049435 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B3891311 : Blo 2049435 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B2594207 : Blo 2049435 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B6917885 : Blo 2049435 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B4611923 : Blo 2049435 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B3074615 : Blo 2049435 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B2049743 : Blo 2049435 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B3074621 : Blo 2049435 3074621 := bbase (se 3 (by rfl) ⟨576491, by rfl⟩ : syracuseStep 3074621 = 1152983) (by norm_num)
theorem B2049747 : Blo 2049435 2049747 := bstep (se 1 (by rfl) ⟨1537310, by rfl⟩ : syracuseStep 2049747 = 3074621) B3074621
theorem B4611941 : Blo 2049435 4611941 := bbase (se 4 (by rfl) ⟨432369, by rfl⟩ : syracuseStep 4611941 = 864739) (by norm_num)
theorem B3074627 : Blo 2049435 3074627 := bstep (se 1 (by rfl) ⟨2305970, by rfl⟩ : syracuseStep 3074627 = 4611941) B4611941
theorem B2049751 : Blo 2049435 2049751 := bstep (se 1 (by rfl) ⟨1537313, by rfl⟩ : syracuseStep 2049751 = 3074627) B3074627
theorem B5188445 : Blo 2049435 5188445 := bbase (se 3 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 5188445 = 1945667) (by norm_num)
theorem B3458963 : Blo 2049435 3458963 := bstep (se 1 (by rfl) ⟨2594222, by rfl⟩ : syracuseStep 3458963 = 5188445) B5188445
theorem B2305975 : Blo 2049435 2305975 := bstep (se 1 (by rfl) ⟨1729481, by rfl⟩ : syracuseStep 2305975 = 3458963) B3458963
theorem B3074633 : Blo 2049435 3074633 := bstep (se 2 (by rfl) ⟨1152987, by rfl⟩ : syracuseStep 3074633 = 2305975) B2305975
theorem B2049755 : Blo 2049435 2049755 := bstep (se 1 (by rfl) ⟨1537316, by rfl⟩ : syracuseStep 2049755 = 3074633) B3074633
theorem B3891341 : Blo 2049435 3891341 := bbase (se 3 (by rfl) ⟨729626, by rfl⟩ : syracuseStep 3891341 = 1459253) (by norm_num)
theorem B10376909 : Blo 2049435 10376909 := bstep (se 3 (by rfl) ⟨1945670, by rfl⟩ : syracuseStep 10376909 = 3891341) B3891341
theorem B6917939 : Blo 2049435 6917939 := bstep (se 1 (by rfl) ⟨5188454, by rfl⟩ : syracuseStep 6917939 = 10376909) B10376909
theorem B4611959 : Blo 2049435 4611959 := bstep (se 1 (by rfl) ⟨3458969, by rfl⟩ : syracuseStep 4611959 = 6917939) B6917939
theorem B3074639 : Blo 2049435 3074639 := bstep (se 1 (by rfl) ⟨2305979, by rfl⟩ : syracuseStep 3074639 = 4611959) B4611959
theorem B2049759 : Blo 2049435 2049759 := bstep (se 1 (by rfl) ⟨1537319, by rfl⟩ : syracuseStep 2049759 = 3074639) B3074639
theorem B3074645 : Blo 2049435 3074645 := bbase (se 8 (by rfl) ⟨18015, by rfl⟩ : syracuseStep 3074645 = 36031) (by norm_num)
theorem B2049763 : Blo 2049435 2049763 := bstep (se 1 (by rfl) ⟨1537322, by rfl⟩ : syracuseStep 2049763 = 3074645) B3074645
theorem B2629633 : Blo 2049435 2629633 := bbase (se 2 (by rfl) ⟨986112, by rfl⟩ : syracuseStep 2629633 = 1972225) (by norm_num)
theorem B3506177 : Blo 2049435 3506177 := bstep (se 2 (by rfl) ⟨1314816, by rfl⟩ : syracuseStep 3506177 = 2629633) B2629633
theorem B9349805 : Blo 2049435 9349805 := bstep (se 3 (by rfl) ⟨1753088, by rfl⟩ : syracuseStep 9349805 = 3506177) B3506177
theorem B6233203 : Blo 2049435 6233203 := bstep (se 1 (by rfl) ⟨4674902, by rfl⟩ : syracuseStep 6233203 = 9349805) B9349805
theorem B8310937 : Blo 2049435 8310937 := bstep (se 2 (by rfl) ⟨3116601, by rfl⟩ : syracuseStep 8310937 = 6233203) B6233203
theorem B11081249 : Blo 2049435 11081249 := bstep (se 2 (by rfl) ⟨4155468, by rfl⟩ : syracuseStep 11081249 = 8310937) B8310937
theorem B7387499 : Blo 2049435 7387499 := bstep (se 1 (by rfl) ⟨5540624, by rfl⟩ : syracuseStep 7387499 = 11081249) B11081249
theorem B4924999 : Blo 2049435 4924999 := bstep (se 1 (by rfl) ⟨3693749, by rfl⟩ : syracuseStep 4924999 = 7387499) B7387499
theorem B6566665 : Blo 2049435 6566665 := bstep (se 2 (by rfl) ⟨2462499, by rfl⟩ : syracuseStep 6566665 = 4924999) B4924999
theorem B8755553 : Blo 2049435 8755553 := bstep (se 2 (by rfl) ⟨3283332, by rfl⟩ : syracuseStep 8755553 = 6566665) B6566665
theorem B5837035 : Blo 2049435 5837035 := bstep (se 1 (by rfl) ⟨4377776, by rfl⟩ : syracuseStep 5837035 = 8755553) B8755553
theorem B7782713 : Blo 2049435 7782713 := bstep (se 2 (by rfl) ⟨2918517, by rfl⟩ : syracuseStep 7782713 = 5837035) B5837035
theorem B5188475 : Blo 2049435 5188475 := bstep (se 1 (by rfl) ⟨3891356, by rfl⟩ : syracuseStep 5188475 = 7782713) B7782713
theorem B3458983 : Blo 2049435 3458983 := bstep (se 1 (by rfl) ⟨2594237, by rfl⟩ : syracuseStep 3458983 = 5188475) B5188475
theorem B4611977 : Blo 2049435 4611977 := bstep (se 2 (by rfl) ⟨1729491, by rfl⟩ : syracuseStep 4611977 = 3458983) B3458983
theorem B3074651 : Blo 2049435 3074651 := bstep (se 1 (by rfl) ⟨2305988, by rfl⟩ : syracuseStep 3074651 = 4611977) B4611977
theorem B2049767 : Blo 2049435 2049767 := bstep (se 1 (by rfl) ⟨1537325, by rfl⟩ : syracuseStep 2049767 = 3074651) B3074651
theorem B2305993 : Blo 2049435 2305993 := bbase (se 2 (by rfl) ⟨864747, by rfl⟩ : syracuseStep 2305993 = 1729495) (by norm_num)
theorem B3074657 : Blo 2049435 3074657 := bstep (se 2 (by rfl) ⟨1152996, by rfl⟩ : syracuseStep 3074657 = 2305993) B2305993
theorem B2049771 : Blo 2049435 2049771 := bstep (se 1 (by rfl) ⟨1537328, by rfl⟩ : syracuseStep 2049771 = 3074657) B3074657
theorem B2462509 : Blo 2049435 2462509 := bbase (se 3 (by rfl) ⟨461720, by rfl⟩ : syracuseStep 2462509 = 923441) (by norm_num)
theorem B3283345 : Blo 2049435 3283345 := bstep (se 2 (by rfl) ⟨1231254, by rfl⟩ : syracuseStep 3283345 = 2462509) B2462509
theorem B17511173 : Blo 2049435 17511173 := bstep (se 4 (by rfl) ⟨1641672, by rfl⟩ : syracuseStep 17511173 = 3283345) B3283345
theorem B11674115 : Blo 2049435 11674115 := bstep (se 1 (by rfl) ⟨8755586, by rfl⟩ : syracuseStep 11674115 = 17511173) B17511173
theorem B7782743 : Blo 2049435 7782743 := bstep (se 1 (by rfl) ⟨5837057, by rfl⟩ : syracuseStep 7782743 = 11674115) B11674115
theorem B5188495 : Blo 2049435 5188495 := bstep (se 1 (by rfl) ⟨3891371, by rfl⟩ : syracuseStep 5188495 = 7782743) B7782743
theorem B6917993 : Blo 2049435 6917993 := bstep (se 2 (by rfl) ⟨2594247, by rfl⟩ : syracuseStep 6917993 = 5188495) B5188495
theorem B4611995 : Blo 2049435 4611995 := bstep (se 1 (by rfl) ⟨3458996, by rfl⟩ : syracuseStep 4611995 = 6917993) B6917993
theorem B3074663 : Blo 2049435 3074663 := bstep (se 1 (by rfl) ⟨2305997, by rfl⟩ : syracuseStep 3074663 = 4611995) B4611995
theorem B2049775 : Blo 2049435 2049775 := bstep (se 1 (by rfl) ⟨1537331, by rfl⟩ : syracuseStep 2049775 = 3074663) B3074663
theorem B3074669 : Blo 2049435 3074669 := bbase (se 3 (by rfl) ⟨576500, by rfl⟩ : syracuseStep 3074669 = 1153001) (by norm_num)
theorem B2049779 : Blo 2049435 2049779 := bstep (se 1 (by rfl) ⟨1537334, by rfl⟩ : syracuseStep 2049779 = 3074669) B3074669
theorem B4612013 : Blo 2049435 4612013 := bbase (se 3 (by rfl) ⟨864752, by rfl⟩ : syracuseStep 4612013 = 1729505) (by norm_num)
theorem B3074675 : Blo 2049435 3074675 := bstep (se 1 (by rfl) ⟨2306006, by rfl⟩ : syracuseStep 3074675 = 4612013) B4612013
theorem B2049783 : Blo 2049435 2049783 := bstep (se 1 (by rfl) ⟨1537337, by rfl⟩ : syracuseStep 2049783 = 3074675) B3074675
theorem B5837093 : Blo 2049435 5837093 := bbase (se 4 (by rfl) ⟨547227, by rfl⟩ : syracuseStep 5837093 = 1094455) (by norm_num)
theorem B3891395 : Blo 2049435 3891395 := bstep (se 1 (by rfl) ⟨2918546, by rfl⟩ : syracuseStep 3891395 = 5837093) B5837093
theorem B2594263 : Blo 2049435 2594263 := bstep (se 1 (by rfl) ⟨1945697, by rfl⟩ : syracuseStep 2594263 = 3891395) B3891395
theorem B3459017 : Blo 2049435 3459017 := bstep (se 2 (by rfl) ⟨1297131, by rfl⟩ : syracuseStep 3459017 = 2594263) B2594263
theorem B2306011 : Blo 2049435 2306011 := bstep (se 1 (by rfl) ⟨1729508, by rfl⟩ : syracuseStep 2306011 = 3459017) B3459017
theorem B3074681 : Blo 2049435 3074681 := bstep (se 2 (by rfl) ⟨1153005, by rfl⟩ : syracuseStep 3074681 = 2306011) B2306011
theorem B2049787 : Blo 2049435 2049787 := bstep (se 1 (by rfl) ⟨1537340, by rfl⟩ : syracuseStep 2049787 = 3074681) B3074681
theorem B3554053 : Blo 2049435 3554053 := bbase (se 4 (by rfl) ⟨333192, by rfl⟩ : syracuseStep 3554053 = 666385) (by norm_num)
theorem B75819797 : Blo 2049435 75819797 := bstep (se 6 (by rfl) ⟨1777026, by rfl⟩ : syracuseStep 75819797 = 3554053) B3554053
theorem B50546531 : Blo 2049435 50546531 := bstep (se 1 (by rfl) ⟨37909898, by rfl⟩ : syracuseStep 50546531 = 75819797) B75819797
theorem B134790749 : Blo 2049435 134790749 := bstep (se 3 (by rfl) ⟨25273265, by rfl⟩ : syracuseStep 134790749 = 50546531) B50546531
theorem B89860499 : Blo 2049435 89860499 := bstep (se 1 (by rfl) ⟨67395374, by rfl⟩ : syracuseStep 89860499 = 134790749) B134790749
theorem B59906999 : Blo 2049435 59906999 := bstep (se 1 (by rfl) ⟨44930249, by rfl⟩ : syracuseStep 59906999 = 89860499) B89860499
theorem B159751997 : Blo 2049435 159751997 := bstep (se 3 (by rfl) ⟨29953499, by rfl⟩ : syracuseStep 159751997 = 59906999) B59906999
theorem B106501331 : Blo 2049435 106501331 := bstep (se 1 (by rfl) ⟨79875998, by rfl⟩ : syracuseStep 106501331 = 159751997) B159751997
theorem B71000887 : Blo 2049435 71000887 := bstep (se 1 (by rfl) ⟨53250665, by rfl⟩ : syracuseStep 71000887 = 106501331) B106501331
theorem B94667849 : Blo 2049435 94667849 := bstep (se 2 (by rfl) ⟨35500443, by rfl⟩ : syracuseStep 94667849 = 71000887) B71000887
theorem B63111899 : Blo 2049435 63111899 := bstep (se 1 (by rfl) ⟨47333924, by rfl⟩ : syracuseStep 63111899 = 94667849) B94667849
theorem B168298397 : Blo 2049435 168298397 := bstep (se 3 (by rfl) ⟨31555949, by rfl⟩ : syracuseStep 168298397 = 63111899) B63111899
theorem B112198931 : Blo 2049435 112198931 := bstep (se 1 (by rfl) ⟨84149198, by rfl⟩ : syracuseStep 112198931 = 168298397) B168298397
theorem B74799287 : Blo 2049435 74799287 := bstep (se 1 (by rfl) ⟨56099465, by rfl⟩ : syracuseStep 74799287 = 112198931) B112198931
theorem B49866191 : Blo 2049435 49866191 := bstep (se 1 (by rfl) ⟨37399643, by rfl⟩ : syracuseStep 49866191 = 74799287) B74799287
theorem B33244127 : Blo 2049435 33244127 := bstep (se 1 (by rfl) ⟨24933095, by rfl⟩ : syracuseStep 33244127 = 49866191) B49866191
theorem B22162751 : Blo 2049435 22162751 := bstep (se 1 (by rfl) ⟨16622063, by rfl⟩ : syracuseStep 22162751 = 33244127) B33244127
theorem B14775167 : Blo 2049435 14775167 := bstep (se 1 (by rfl) ⟨11081375, by rfl⟩ : syracuseStep 14775167 = 22162751) B22162751
theorem B39400445 : Blo 2049435 39400445 := bstep (se 3 (by rfl) ⟨7387583, by rfl⟩ : syracuseStep 39400445 = 14775167) B14775167
theorem B26266963 : Blo 2049435 26266963 := bstep (se 1 (by rfl) ⟨19700222, by rfl⟩ : syracuseStep 26266963 = 39400445) B39400445
theorem B35022617 : Blo 2049435 35022617 := bstep (se 2 (by rfl) ⟨13133481, by rfl⟩ : syracuseStep 35022617 = 26266963) B26266963
theorem B23348411 : Blo 2049435 23348411 := bstep (se 1 (by rfl) ⟨17511308, by rfl⟩ : syracuseStep 23348411 = 35022617) B35022617
theorem B15565607 : Blo 2049435 15565607 := bstep (se 1 (by rfl) ⟨11674205, by rfl⟩ : syracuseStep 15565607 = 23348411) B23348411
theorem B10377071 : Blo 2049435 10377071 := bstep (se 1 (by rfl) ⟨7782803, by rfl⟩ : syracuseStep 10377071 = 15565607) B15565607
theorem B6918047 : Blo 2049435 6918047 := bstep (se 1 (by rfl) ⟨5188535, by rfl⟩ : syracuseStep 6918047 = 10377071) B10377071
theorem B4612031 : Blo 2049435 4612031 := bstep (se 1 (by rfl) ⟨3459023, by rfl⟩ : syracuseStep 4612031 = 6918047) B6918047
theorem B3074687 : Blo 2049435 3074687 := bstep (se 1 (by rfl) ⟨2306015, by rfl⟩ : syracuseStep 3074687 = 4612031) B4612031
theorem B2049791 : Blo 2049435 2049791 := bstep (se 1 (by rfl) ⟨1537343, by rfl⟩ : syracuseStep 2049791 = 3074687) B3074687
theorem B3074693 : Blo 2049435 3074693 := bbase (se 4 (by rfl) ⟨288252, by rfl⟩ : syracuseStep 3074693 = 576505) (by norm_num)
theorem B2049795 : Blo 2049435 2049795 := bstep (se 1 (by rfl) ⟨1537346, by rfl⟩ : syracuseStep 2049795 = 3074693) B3074693
theorem B3459037 : Blo 2049435 3459037 := bbase (se 3 (by rfl) ⟨648569, by rfl⟩ : syracuseStep 3459037 = 1297139) (by norm_num)
theorem B4612049 : Blo 2049435 4612049 := bstep (se 2 (by rfl) ⟨1729518, by rfl⟩ : syracuseStep 4612049 = 3459037) B3459037
theorem B3074699 : Blo 2049435 3074699 := bstep (se 1 (by rfl) ⟨2306024, by rfl⟩ : syracuseStep 3074699 = 4612049) B4612049
theorem B2049799 : Blo 2049435 2049799 := bstep (se 1 (by rfl) ⟨1537349, by rfl⟩ : syracuseStep 2049799 = 3074699) B3074699
theorem B2306029 : Blo 2049435 2306029 := bbase (se 3 (by rfl) ⟨432380, by rfl⟩ : syracuseStep 2306029 = 864761) (by norm_num)
theorem B3074705 : Blo 2049435 3074705 := bstep (se 2 (by rfl) ⟨1153014, by rfl⟩ : syracuseStep 3074705 = 2306029) B2306029
theorem B2049803 : Blo 2049435 2049803 := bstep (se 1 (by rfl) ⟨1537352, by rfl⟩ : syracuseStep 2049803 = 3074705) B3074705
theorem B6918101 : Blo 2049435 6918101 := bbase (se 7 (by rfl) ⟨81071, by rfl⟩ : syracuseStep 6918101 = 162143) (by norm_num)
theorem B4612067 : Blo 2049435 4612067 := bstep (se 1 (by rfl) ⟨3459050, by rfl⟩ : syracuseStep 4612067 = 6918101) B6918101
theorem B3074711 : Blo 2049435 3074711 := bstep (se 1 (by rfl) ⟨2306033, by rfl⟩ : syracuseStep 3074711 = 4612067) B4612067
theorem B2049807 : Blo 2049435 2049807 := bstep (se 1 (by rfl) ⟨1537355, by rfl⟩ : syracuseStep 2049807 = 3074711) B3074711
theorem B3074717 : Blo 2049435 3074717 := bbase (se 3 (by rfl) ⟨576509, by rfl⟩ : syracuseStep 3074717 = 1153019) (by norm_num)
theorem B2049811 : Blo 2049435 2049811 := bstep (se 1 (by rfl) ⟨1537358, by rfl⟩ : syracuseStep 2049811 = 3074717) B3074717
theorem B4612085 : Blo 2049435 4612085 := bbase (se 5 (by rfl) ⟨216191, by rfl⟩ : syracuseStep 4612085 = 432383) (by norm_num)
theorem B3074723 : Blo 2049435 3074723 := bstep (se 1 (by rfl) ⟨2306042, by rfl⟩ : syracuseStep 3074723 = 4612085) B4612085
theorem B2049815 : Blo 2049435 2049815 := bstep (se 1 (by rfl) ⟨1537361, by rfl⟩ : syracuseStep 2049815 = 3074723) B3074723
theorem B13494485 : Blo 2049435 13494485 := bbase (se 7 (by rfl) ⟨158138, by rfl⟩ : syracuseStep 13494485 = 316277) (by norm_num)
theorem B35985293 : Blo 2049435 35985293 := bstep (se 3 (by rfl) ⟨6747242, by rfl⟩ : syracuseStep 35985293 = 13494485) B13494485
theorem B23990195 : Blo 2049435 23990195 := bstep (se 1 (by rfl) ⟨17992646, by rfl⟩ : syracuseStep 23990195 = 35985293) B35985293
theorem B15993463 : Blo 2049435 15993463 := bstep (se 1 (by rfl) ⟨11995097, by rfl⟩ : syracuseStep 15993463 = 23990195) B23990195
theorem B21324617 : Blo 2049435 21324617 := bstep (se 2 (by rfl) ⟨7996731, by rfl⟩ : syracuseStep 21324617 = 15993463) B15993463
theorem B14216411 : Blo 2049435 14216411 := bstep (se 1 (by rfl) ⟨10662308, by rfl⟩ : syracuseStep 14216411 = 21324617) B21324617
theorem B37910429 : Blo 2049435 37910429 := bstep (se 3 (by rfl) ⟨7108205, by rfl⟩ : syracuseStep 37910429 = 14216411) B14216411
theorem B25273619 : Blo 2049435 25273619 := bstep (se 1 (by rfl) ⟨18955214, by rfl⟩ : syracuseStep 25273619 = 37910429) B37910429
theorem B16849079 : Blo 2049435 16849079 := bstep (se 1 (by rfl) ⟨12636809, by rfl⟩ : syracuseStep 16849079 = 25273619) B25273619
theorem B11232719 : Blo 2049435 11232719 := bstep (se 1 (by rfl) ⟨8424539, by rfl⟩ : syracuseStep 11232719 = 16849079) B16849079
theorem B7488479 : Blo 2049435 7488479 := bstep (se 1 (by rfl) ⟨5616359, by rfl⟩ : syracuseStep 7488479 = 11232719) B11232719
theorem B4992319 : Blo 2049435 4992319 := bstep (se 1 (by rfl) ⟨3744239, by rfl⟩ : syracuseStep 4992319 = 7488479) B7488479
theorem B26625701 : Blo 2049435 26625701 := bstep (se 4 (by rfl) ⟨2496159, by rfl⟩ : syracuseStep 26625701 = 4992319) B4992319
theorem B17750467 : Blo 2049435 17750467 := bstep (se 1 (by rfl) ⟨13312850, by rfl⟩ : syracuseStep 17750467 = 26625701) B26625701
theorem B94669157 : Blo 2049435 94669157 := bstep (se 4 (by rfl) ⟨8875233, by rfl⟩ : syracuseStep 94669157 = 17750467) B17750467
theorem B63112771 : Blo 2049435 63112771 := bstep (se 1 (by rfl) ⟨47334578, by rfl⟩ : syracuseStep 63112771 = 94669157) B94669157
theorem B84150361 : Blo 2049435 84150361 := bstep (se 2 (by rfl) ⟨31556385, by rfl⟩ : syracuseStep 84150361 = 63112771) B63112771
theorem B112200481 : Blo 2049435 112200481 := bstep (se 2 (by rfl) ⟨42075180, by rfl⟩ : syracuseStep 112200481 = 84150361) B84150361
theorem B149600641 : Blo 2049435 149600641 := bstep (se 2 (by rfl) ⟨56100240, by rfl⟩ : syracuseStep 149600641 = 112200481) B112200481
theorem B199467521 : Blo 2049435 199467521 := bstep (se 2 (by rfl) ⟨74800320, by rfl⟩ : syracuseStep 199467521 = 149600641) B149600641
theorem B132978347 : Blo 2049435 132978347 := bstep (se 1 (by rfl) ⟨99733760, by rfl⟩ : syracuseStep 132978347 = 199467521) B199467521
theorem B88652231 : Blo 2049435 88652231 := bstep (se 1 (by rfl) ⟨66489173, by rfl⟩ : syracuseStep 88652231 = 132978347) B132978347
theorem B59101487 : Blo 2049435 59101487 := bstep (se 1 (by rfl) ⟨44326115, by rfl⟩ : syracuseStep 59101487 = 88652231) B88652231
theorem B39400991 : Blo 2049435 39400991 := bstep (se 1 (by rfl) ⟨29550743, by rfl⟩ : syracuseStep 39400991 = 59101487) B59101487
theorem B26267327 : Blo 2049435 26267327 := bstep (se 1 (by rfl) ⟨19700495, by rfl⟩ : syracuseStep 26267327 = 39400991) B39400991
theorem B17511551 : Blo 2049435 17511551 := bstep (se 1 (by rfl) ⟨13133663, by rfl⟩ : syracuseStep 17511551 = 26267327) B26267327
theorem B11674367 : Blo 2049435 11674367 := bstep (se 1 (by rfl) ⟨8755775, by rfl⟩ : syracuseStep 11674367 = 17511551) B17511551
theorem B7782911 : Blo 2049435 7782911 := bstep (se 1 (by rfl) ⟨5837183, by rfl⟩ : syracuseStep 7782911 = 11674367) B11674367
theorem B5188607 : Blo 2049435 5188607 := bstep (se 1 (by rfl) ⟨3891455, by rfl⟩ : syracuseStep 5188607 = 7782911) B7782911
theorem B3459071 : Blo 2049435 3459071 := bstep (se 1 (by rfl) ⟨2594303, by rfl⟩ : syracuseStep 3459071 = 5188607) B5188607
theorem B2306047 : Blo 2049435 2306047 := bstep (se 1 (by rfl) ⟨1729535, by rfl⟩ : syracuseStep 2306047 = 3459071) B3459071
theorem B3074729 : Blo 2049435 3074729 := bstep (se 2 (by rfl) ⟨1153023, by rfl⟩ : syracuseStep 3074729 = 2306047) B2306047
theorem B2049819 : Blo 2049435 2049819 := bstep (se 1 (by rfl) ⟨1537364, by rfl⟩ : syracuseStep 2049819 = 3074729) B3074729
theorem B2918597 : Blo 2049435 2918597 := bbase (se 4 (by rfl) ⟨273618, by rfl⟩ : syracuseStep 2918597 = 547237) (by norm_num)
theorem B7782925 : Blo 2049435 7782925 := bstep (se 3 (by rfl) ⟨1459298, by rfl⟩ : syracuseStep 7782925 = 2918597) B2918597
theorem B10377233 : Blo 2049435 10377233 := bstep (se 2 (by rfl) ⟨3891462, by rfl⟩ : syracuseStep 10377233 = 7782925) B7782925
theorem B6918155 : Blo 2049435 6918155 := bstep (se 1 (by rfl) ⟨5188616, by rfl⟩ : syracuseStep 6918155 = 10377233) B10377233
theorem B4612103 : Blo 2049435 4612103 := bstep (se 1 (by rfl) ⟨3459077, by rfl⟩ : syracuseStep 4612103 = 6918155) B6918155
theorem B3074735 : Blo 2049435 3074735 := bstep (se 1 (by rfl) ⟨2306051, by rfl⟩ : syracuseStep 3074735 = 4612103) B4612103
theorem B2049823 : Blo 2049435 2049823 := bstep (se 1 (by rfl) ⟨1537367, by rfl⟩ : syracuseStep 2049823 = 3074735) B3074735
theorem B3074741 : Blo 2049435 3074741 := bbase (se 5 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 3074741 = 288257) (by norm_num)
theorem B2049827 : Blo 2049435 2049827 := bstep (se 1 (by rfl) ⟨1537370, by rfl⟩ : syracuseStep 2049827 = 3074741) B3074741
theorem B5188637 : Blo 2049435 5188637 := bbase (se 3 (by rfl) ⟨972869, by rfl⟩ : syracuseStep 5188637 = 1945739) (by norm_num)
theorem B3459091 : Blo 2049435 3459091 := bstep (se 1 (by rfl) ⟨2594318, by rfl⟩ : syracuseStep 3459091 = 5188637) B5188637
theorem B4612121 : Blo 2049435 4612121 := bstep (se 2 (by rfl) ⟨1729545, by rfl⟩ : syracuseStep 4612121 = 3459091) B3459091
theorem B3074747 : Blo 2049435 3074747 := bstep (se 1 (by rfl) ⟨2306060, by rfl⟩ : syracuseStep 3074747 = 4612121) B4612121
theorem B2049831 : Blo 2049435 2049831 := bstep (se 1 (by rfl) ⟨1537373, by rfl⟩ : syracuseStep 2049831 = 3074747) B3074747
theorem B2306065 : Blo 2049435 2306065 := bbase (se 2 (by rfl) ⟨864774, by rfl⟩ : syracuseStep 2306065 = 1729549) (by norm_num)
theorem B3074753 : Blo 2049435 3074753 := bstep (se 2 (by rfl) ⟨1153032, by rfl⟩ : syracuseStep 3074753 = 2306065) B2306065
theorem B2049835 : Blo 2049435 2049835 := bstep (se 1 (by rfl) ⟨1537376, by rfl⟩ : syracuseStep 2049835 = 3074753) B3074753
theorem B3891493 : Blo 2049435 3891493 := bbase (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) (by norm_num)
theorem B5188657 : Blo 2049435 5188657 := bstep (se 2 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 5188657 = 3891493) B3891493
theorem B6918209 : Blo 2049435 6918209 := bstep (se 2 (by rfl) ⟨2594328, by rfl⟩ : syracuseStep 6918209 = 5188657) B5188657
theorem B4612139 : Blo 2049435 4612139 := bstep (se 1 (by rfl) ⟨3459104, by rfl⟩ : syracuseStep 4612139 = 6918209) B6918209
theorem B3074759 : Blo 2049435 3074759 := bstep (se 1 (by rfl) ⟨2306069, by rfl⟩ : syracuseStep 3074759 = 4612139) B4612139
theorem B2049839 : Blo 2049435 2049839 := bstep (se 1 (by rfl) ⟨1537379, by rfl⟩ : syracuseStep 2049839 = 3074759) B3074759
theorem B3074765 : Blo 2049435 3074765 := bbase (se 3 (by rfl) ⟨576518, by rfl⟩ : syracuseStep 3074765 = 1153037) (by norm_num)
theorem B2049843 : Blo 2049435 2049843 := bstep (se 1 (by rfl) ⟨1537382, by rfl⟩ : syracuseStep 2049843 = 3074765) B3074765
theorem B4612157 : Blo 2049435 4612157 := bbase (se 3 (by rfl) ⟨864779, by rfl⟩ : syracuseStep 4612157 = 1729559) (by norm_num)
theorem B3074771 : Blo 2049435 3074771 := bstep (se 1 (by rfl) ⟨2306078, by rfl⟩ : syracuseStep 3074771 = 4612157) B4612157
theorem B2049847 : Blo 2049435 2049847 := bstep (se 1 (by rfl) ⟨1537385, by rfl⟩ : syracuseStep 2049847 = 3074771) B3074771
theorem B3459125 : Blo 2049435 3459125 := bbase (se 5 (by rfl) ⟨162146, by rfl⟩ : syracuseStep 3459125 = 324293) (by norm_num)
theorem B2306083 : Blo 2049435 2306083 := bstep (se 1 (by rfl) ⟨1729562, by rfl⟩ : syracuseStep 2306083 = 3459125) B3459125
theorem B3074777 : Blo 2049435 3074777 := bstep (se 2 (by rfl) ⟨1153041, by rfl⟩ : syracuseStep 3074777 = 2306083) B2306083
theorem B2049851 : Blo 2049435 2049851 := bstep (se 1 (by rfl) ⟨1537388, by rfl⟩ : syracuseStep 2049851 = 3074777) B3074777
theorem B5837285 : Blo 2049435 5837285 := bbase (se 4 (by rfl) ⟨547245, by rfl⟩ : syracuseStep 5837285 = 1094491) (by norm_num)
theorem B15566093 : Blo 2049435 15566093 := bstep (se 3 (by rfl) ⟨2918642, by rfl⟩ : syracuseStep 15566093 = 5837285) B5837285
theorem B10377395 : Blo 2049435 10377395 := bstep (se 1 (by rfl) ⟨7783046, by rfl⟩ : syracuseStep 10377395 = 15566093) B15566093
theorem B6918263 : Blo 2049435 6918263 := bstep (se 1 (by rfl) ⟨5188697, by rfl⟩ : syracuseStep 6918263 = 10377395) B10377395
theorem B4612175 : Blo 2049435 4612175 := bstep (se 1 (by rfl) ⟨3459131, by rfl⟩ : syracuseStep 4612175 = 6918263) B6918263
theorem B3074783 : Blo 2049435 3074783 := bstep (se 1 (by rfl) ⟨2306087, by rfl⟩ : syracuseStep 3074783 = 4612175) B4612175
theorem B2049855 : Blo 2049435 2049855 := bstep (se 1 (by rfl) ⟨1537391, by rfl⟩ : syracuseStep 2049855 = 3074783) B3074783
theorem B3074789 : Blo 2049435 3074789 := bbase (se 4 (by rfl) ⟨288261, by rfl⟩ : syracuseStep 3074789 = 576523) (by norm_num)
theorem B2049859 : Blo 2049435 2049859 := bstep (se 1 (by rfl) ⟨1537394, by rfl⟩ : syracuseStep 2049859 = 3074789) B3074789
theorem B9350245 : Blo 2049435 9350245 := bbase (se 4 (by rfl) ⟨876585, by rfl⟩ : syracuseStep 9350245 = 1753171) (by norm_num)
theorem B12466993 : Blo 2049435 12466993 := bstep (se 2 (by rfl) ⟨4675122, by rfl⟩ : syracuseStep 12466993 = 9350245) B9350245
theorem B16622657 : Blo 2049435 16622657 := bstep (se 2 (by rfl) ⟨6233496, by rfl⟩ : syracuseStep 16622657 = 12466993) B12466993
theorem B11081771 : Blo 2049435 11081771 := bstep (se 1 (by rfl) ⟨8311328, by rfl⟩ : syracuseStep 11081771 = 16622657) B16622657
theorem B7387847 : Blo 2049435 7387847 := bstep (se 1 (by rfl) ⟨5540885, by rfl⟩ : syracuseStep 7387847 = 11081771) B11081771
theorem B4925231 : Blo 2049435 4925231 := bstep (se 1 (by rfl) ⟨3693923, by rfl⟩ : syracuseStep 4925231 = 7387847) B7387847
theorem B3283487 : Blo 2049435 3283487 := bstep (se 1 (by rfl) ⟨2462615, by rfl⟩ : syracuseStep 3283487 = 4925231) B4925231
theorem B2188991 : Blo 2049435 2188991 := bstep (se 1 (by rfl) ⟨1641743, by rfl⟩ : syracuseStep 2188991 = 3283487) B3283487
theorem B5837309 : Blo 2049435 5837309 := bstep (se 3 (by rfl) ⟨1094495, by rfl⟩ : syracuseStep 5837309 = 2188991) B2188991
theorem B3891539 : Blo 2049435 3891539 := bstep (se 1 (by rfl) ⟨2918654, by rfl⟩ : syracuseStep 3891539 = 5837309) B5837309
theorem B2594359 : Blo 2049435 2594359 := bstep (se 1 (by rfl) ⟨1945769, by rfl⟩ : syracuseStep 2594359 = 3891539) B3891539
theorem B3459145 : Blo 2049435 3459145 := bstep (se 2 (by rfl) ⟨1297179, by rfl⟩ : syracuseStep 3459145 = 2594359) B2594359
theorem B4612193 : Blo 2049435 4612193 := bstep (se 2 (by rfl) ⟨1729572, by rfl⟩ : syracuseStep 4612193 = 3459145) B3459145
theorem B3074795 : Blo 2049435 3074795 := bstep (se 1 (by rfl) ⟨2306096, by rfl⟩ : syracuseStep 3074795 = 4612193) B4612193
theorem B2049863 : Blo 2049435 2049863 := bstep (se 1 (by rfl) ⟨1537397, by rfl⟩ : syracuseStep 2049863 = 3074795) B3074795
theorem B2306101 : Blo 2049435 2306101 := bbase (se 5 (by rfl) ⟨108098, by rfl⟩ : syracuseStep 2306101 = 216197) (by norm_num)
theorem B3074801 : Blo 2049435 3074801 := bstep (se 2 (by rfl) ⟨1153050, by rfl⟩ : syracuseStep 3074801 = 2306101) B2306101
theorem B2049867 : Blo 2049435 2049867 := bstep (se 1 (by rfl) ⟨1537400, by rfl⟩ : syracuseStep 2049867 = 3074801) B3074801
theorem B2594369 : Blo 2049435 2594369 := bbase (se 2 (by rfl) ⟨972888, by rfl⟩ : syracuseStep 2594369 = 1945777) (by norm_num)
theorem B6918317 : Blo 2049435 6918317 := bstep (se 3 (by rfl) ⟨1297184, by rfl⟩ : syracuseStep 6918317 = 2594369) B2594369
theorem B4612211 : Blo 2049435 4612211 := bstep (se 1 (by rfl) ⟨3459158, by rfl⟩ : syracuseStep 4612211 = 6918317) B6918317
theorem B3074807 : Blo 2049435 3074807 := bstep (se 1 (by rfl) ⟨2306105, by rfl⟩ : syracuseStep 3074807 = 4612211) B4612211
theorem B2049871 : Blo 2049435 2049871 := bstep (se 1 (by rfl) ⟨1537403, by rfl⟩ : syracuseStep 2049871 = 3074807) B3074807
theorem B3074813 : Blo 2049435 3074813 := bbase (se 3 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 3074813 = 1153055) (by norm_num)
theorem B2049875 : Blo 2049435 2049875 := bstep (se 1 (by rfl) ⟨1537406, by rfl⟩ : syracuseStep 2049875 = 3074813) B3074813
theorem B4612229 : Blo 2049435 4612229 := bbase (se 4 (by rfl) ⟨432396, by rfl⟩ : syracuseStep 4612229 = 864793) (by norm_num)
theorem B3074819 : Blo 2049435 3074819 := bstep (se 1 (by rfl) ⟨2306114, by rfl⟩ : syracuseStep 3074819 = 4612229) B4612229
theorem B2049879 : Blo 2049435 2049879 := bstep (se 1 (by rfl) ⟨1537409, by rfl⟩ : syracuseStep 2049879 = 3074819) B3074819
theorem B24934229 : Blo 2049435 24934229 := bbase (se 9 (by rfl) ⟨73049, by rfl⟩ : syracuseStep 24934229 = 146099) (by norm_num)
theorem B16622819 : Blo 2049435 16622819 := bstep (se 1 (by rfl) ⟨12467114, by rfl⟩ : syracuseStep 16622819 = 24934229) B24934229
theorem B11081879 : Blo 2049435 11081879 := bstep (se 1 (by rfl) ⟨8311409, by rfl⟩ : syracuseStep 11081879 = 16622819) B16622819
theorem B7387919 : Blo 2049435 7387919 := bstep (se 1 (by rfl) ⟨5540939, by rfl⟩ : syracuseStep 7387919 = 11081879) B11081879
theorem B4925279 : Blo 2049435 4925279 := bstep (se 1 (by rfl) ⟨3693959, by rfl⟩ : syracuseStep 4925279 = 7387919) B7387919
theorem B3283519 : Blo 2049435 3283519 := bstep (se 1 (by rfl) ⟨2462639, by rfl⟩ : syracuseStep 3283519 = 4925279) B4925279
theorem B4378025 : Blo 2049435 4378025 := bstep (se 2 (by rfl) ⟨1641759, by rfl⟩ : syracuseStep 4378025 = 3283519) B3283519
theorem B2918683 : Blo 2049435 2918683 := bstep (se 1 (by rfl) ⟨2189012, by rfl⟩ : syracuseStep 2918683 = 4378025) B4378025
theorem B3891577 : Blo 2049435 3891577 := bstep (se 2 (by rfl) ⟨1459341, by rfl⟩ : syracuseStep 3891577 = 2918683) B2918683
theorem B5188769 : Blo 2049435 5188769 := bstep (se 2 (by rfl) ⟨1945788, by rfl⟩ : syracuseStep 5188769 = 3891577) B3891577
theorem B3459179 : Blo 2049435 3459179 := bstep (se 1 (by rfl) ⟨2594384, by rfl⟩ : syracuseStep 3459179 = 5188769) B5188769
theorem B2306119 : Blo 2049435 2306119 := bstep (se 1 (by rfl) ⟨1729589, by rfl⟩ : syracuseStep 2306119 = 3459179) B3459179
theorem B3074825 : Blo 2049435 3074825 := bstep (se 2 (by rfl) ⟨1153059, by rfl⟩ : syracuseStep 3074825 = 2306119) B2306119
theorem B2049883 : Blo 2049435 2049883 := bstep (se 1 (by rfl) ⟨1537412, by rfl⟩ : syracuseStep 2049883 = 3074825) B3074825
theorem B10377557 : Blo 2049435 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B6918371 : Blo 2049435 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B4612247 : Blo 2049435 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B3074831 : Blo 2049435 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B2049887 : Blo 2049435 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B3074837 : Blo 2049435 3074837 := bbase (se 6 (by rfl) ⟨72066, by rfl⟩ : syracuseStep 3074837 = 144133) (by norm_num)
theorem B2049891 : Blo 2049435 2049891 := bstep (se 1 (by rfl) ⟨1537418, by rfl⟩ : syracuseStep 2049891 = 3074837) B3074837
theorem B2496253 : Blo 2049435 2496253 := bbase (se 3 (by rfl) ⟨468047, by rfl⟩ : syracuseStep 2496253 = 936095) (by norm_num)
theorem B3328337 : Blo 2049435 3328337 := bstep (se 2 (by rfl) ⟨1248126, by rfl⟩ : syracuseStep 3328337 = 2496253) B2496253
theorem B8875565 : Blo 2049435 8875565 := bstep (se 3 (by rfl) ⟨1664168, by rfl⟩ : syracuseStep 8875565 = 3328337) B3328337
theorem B5917043 : Blo 2049435 5917043 := bstep (se 1 (by rfl) ⟨4437782, by rfl⟩ : syracuseStep 5917043 = 8875565) B8875565
theorem B3944695 : Blo 2049435 3944695 := bstep (se 1 (by rfl) ⟨2958521, by rfl⟩ : syracuseStep 3944695 = 5917043) B5917043
theorem B5259593 : Blo 2049435 5259593 := bstep (se 2 (by rfl) ⟨1972347, by rfl⟩ : syracuseStep 5259593 = 3944695) B3944695
theorem B14025581 : Blo 2049435 14025581 := bstep (se 3 (by rfl) ⟨2629796, by rfl⟩ : syracuseStep 14025581 = 5259593) B5259593
theorem B9350387 : Blo 2049435 9350387 := bstep (se 1 (by rfl) ⟨7012790, by rfl⟩ : syracuseStep 9350387 = 14025581) B14025581
theorem B6233591 : Blo 2049435 6233591 := bstep (se 1 (by rfl) ⟨4675193, by rfl⟩ : syracuseStep 6233591 = 9350387) B9350387
theorem B16622909 : Blo 2049435 16622909 := bstep (se 3 (by rfl) ⟨3116795, by rfl⟩ : syracuseStep 16622909 = 6233591) B6233591
theorem B11081939 : Blo 2049435 11081939 := bstep (se 1 (by rfl) ⟨8311454, by rfl⟩ : syracuseStep 11081939 = 16622909) B16622909
theorem B29551837 : Blo 2049435 29551837 := bstep (se 3 (by rfl) ⟨5540969, by rfl⟩ : syracuseStep 29551837 = 11081939) B11081939
theorem B39402449 : Blo 2049435 39402449 := bstep (se 2 (by rfl) ⟨14775918, by rfl⟩ : syracuseStep 39402449 = 29551837) B29551837
theorem B26268299 : Blo 2049435 26268299 := bstep (se 1 (by rfl) ⟨19701224, by rfl⟩ : syracuseStep 26268299 = 39402449) B39402449
theorem B17512199 : Blo 2049435 17512199 := bstep (se 1 (by rfl) ⟨13134149, by rfl⟩ : syracuseStep 17512199 = 26268299) B26268299
theorem B11674799 : Blo 2049435 11674799 := bstep (se 1 (by rfl) ⟨8756099, by rfl⟩ : syracuseStep 11674799 = 17512199) B17512199
theorem B7783199 : Blo 2049435 7783199 := bstep (se 1 (by rfl) ⟨5837399, by rfl⟩ : syracuseStep 7783199 = 11674799) B11674799
theorem B5188799 : Blo 2049435 5188799 := bstep (se 1 (by rfl) ⟨3891599, by rfl⟩ : syracuseStep 5188799 = 7783199) B7783199
theorem B3459199 : Blo 2049435 3459199 := bstep (se 1 (by rfl) ⟨2594399, by rfl⟩ : syracuseStep 3459199 = 5188799) B5188799
theorem B4612265 : Blo 2049435 4612265 := bstep (se 2 (by rfl) ⟨1729599, by rfl⟩ : syracuseStep 4612265 = 3459199) B3459199
theorem B3074843 : Blo 2049435 3074843 := bstep (se 1 (by rfl) ⟨2306132, by rfl⟩ : syracuseStep 3074843 = 4612265) B4612265
theorem B2049895 : Blo 2049435 2049895 := bstep (se 1 (by rfl) ⟨1537421, by rfl⟩ : syracuseStep 2049895 = 3074843) B3074843
theorem B2306137 : Blo 2049435 2306137 := bbase (se 2 (by rfl) ⟨864801, by rfl⟩ : syracuseStep 2306137 = 1729603) (by norm_num)
theorem B3074849 : Blo 2049435 3074849 := bstep (se 2 (by rfl) ⟨1153068, by rfl⟩ : syracuseStep 3074849 = 2306137) B2306137
theorem B2049899 : Blo 2049435 2049899 := bstep (se 1 (by rfl) ⟨1537424, by rfl⟩ : syracuseStep 2049899 = 3074849) B3074849
theorem B3744397 : Blo 2049435 3744397 := bbase (se 3 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 3744397 = 1404149) (by norm_num)
theorem B4992529 : Blo 2049435 4992529 := bstep (se 2 (by rfl) ⟨1872198, by rfl⟩ : syracuseStep 4992529 = 3744397) B3744397
theorem B6656705 : Blo 2049435 6656705 := bstep (se 2 (by rfl) ⟨2496264, by rfl⟩ : syracuseStep 6656705 = 4992529) B4992529
theorem B4437803 : Blo 2049435 4437803 := bstep (se 1 (by rfl) ⟨3328352, by rfl⟩ : syracuseStep 4437803 = 6656705) B6656705
theorem B2958535 : Blo 2049435 2958535 := bstep (se 1 (by rfl) ⟨2218901, by rfl⟩ : syracuseStep 2958535 = 4437803) B4437803
theorem B3944713 : Blo 2049435 3944713 := bstep (se 2 (by rfl) ⟨1479267, by rfl⟩ : syracuseStep 3944713 = 2958535) B2958535
theorem B5259617 : Blo 2049435 5259617 := bstep (se 2 (by rfl) ⟨1972356, by rfl⟩ : syracuseStep 5259617 = 3944713) B3944713
theorem B3506411 : Blo 2049435 3506411 := bstep (se 1 (by rfl) ⟨2629808, by rfl⟩ : syracuseStep 3506411 = 5259617) B5259617
theorem B2337607 : Blo 2049435 2337607 := bstep (se 1 (by rfl) ⟨1753205, by rfl⟩ : syracuseStep 2337607 = 3506411) B3506411
theorem B3116809 : Blo 2049435 3116809 := bstep (se 2 (by rfl) ⟨1168803, by rfl⟩ : syracuseStep 3116809 = 2337607) B2337607
theorem B4155745 : Blo 2049435 4155745 := bstep (se 2 (by rfl) ⟨1558404, by rfl⟩ : syracuseStep 4155745 = 3116809) B3116809
theorem B5540993 : Blo 2049435 5540993 := bstep (se 2 (by rfl) ⟨2077872, by rfl⟩ : syracuseStep 5540993 = 4155745) B4155745
theorem B3693995 : Blo 2049435 3693995 := bstep (se 1 (by rfl) ⟨2770496, by rfl⟩ : syracuseStep 3693995 = 5540993) B5540993
theorem B2462663 : Blo 2049435 2462663 := bstep (se 1 (by rfl) ⟨1846997, by rfl⟩ : syracuseStep 2462663 = 3693995) B3693995
theorem B6567101 : Blo 2049435 6567101 := bstep (se 3 (by rfl) ⟨1231331, by rfl⟩ : syracuseStep 6567101 = 2462663) B2462663
theorem B4378067 : Blo 2049435 4378067 := bstep (se 1 (by rfl) ⟨3283550, by rfl⟩ : syracuseStep 4378067 = 6567101) B6567101
theorem B2918711 : Blo 2049435 2918711 := bstep (se 1 (by rfl) ⟨2189033, by rfl⟩ : syracuseStep 2918711 = 4378067) B4378067
theorem B7783229 : Blo 2049435 7783229 := bstep (se 3 (by rfl) ⟨1459355, by rfl⟩ : syracuseStep 7783229 = 2918711) B2918711
theorem B5188819 : Blo 2049435 5188819 := bstep (se 1 (by rfl) ⟨3891614, by rfl⟩ : syracuseStep 5188819 = 7783229) B7783229
theorem B6918425 : Blo 2049435 6918425 := bstep (se 2 (by rfl) ⟨2594409, by rfl⟩ : syracuseStep 6918425 = 5188819) B5188819
theorem B4612283 : Blo 2049435 4612283 := bstep (se 1 (by rfl) ⟨3459212, by rfl⟩ : syracuseStep 4612283 = 6918425) B6918425
theorem B3074855 : Blo 2049435 3074855 := bstep (se 1 (by rfl) ⟨2306141, by rfl⟩ : syracuseStep 3074855 = 4612283) B4612283
theorem B2049903 : Blo 2049435 2049903 := bstep (se 1 (by rfl) ⟨1537427, by rfl⟩ : syracuseStep 2049903 = 3074855) B3074855
theorem B3074861 : Blo 2049435 3074861 := bbase (se 3 (by rfl) ⟨576536, by rfl⟩ : syracuseStep 3074861 = 1153073) (by norm_num)
theorem B2049907 : Blo 2049435 2049907 := bstep (se 1 (by rfl) ⟨1537430, by rfl⟩ : syracuseStep 2049907 = 3074861) B3074861
theorem B4612301 : Blo 2049435 4612301 := bbase (se 3 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 4612301 = 1729613) (by norm_num)
theorem B3074867 : Blo 2049435 3074867 := bstep (se 1 (by rfl) ⟨2306150, by rfl⟩ : syracuseStep 3074867 = 4612301) B4612301
theorem B2049911 : Blo 2049435 2049911 := bstep (se 1 (by rfl) ⟨1537433, by rfl⟩ : syracuseStep 2049911 = 3074867) B3074867
theorem B2594425 : Blo 2049435 2594425 := bbase (se 2 (by rfl) ⟨972909, by rfl⟩ : syracuseStep 2594425 = 1945819) (by norm_num)
theorem B3459233 : Blo 2049435 3459233 := bstep (se 2 (by rfl) ⟨1297212, by rfl⟩ : syracuseStep 3459233 = 2594425) B2594425
theorem B2306155 : Blo 2049435 2306155 := bstep (se 1 (by rfl) ⟨1729616, by rfl⟩ : syracuseStep 2306155 = 3459233) B3459233
theorem B3074873 : Blo 2049435 3074873 := bstep (se 2 (by rfl) ⟨1153077, by rfl⟩ : syracuseStep 3074873 = 2306155) B2306155
theorem B2049915 : Blo 2049435 2049915 := bstep (se 1 (by rfl) ⟨1537436, by rfl⟩ : syracuseStep 2049915 = 3074873) B3074873
theorem B8424949 : Blo 2049435 8424949 := bbase (se 5 (by rfl) ⟨394919, by rfl⟩ : syracuseStep 8424949 = 789839) (by norm_num)
theorem B11233265 : Blo 2049435 11233265 := bstep (se 2 (by rfl) ⟨4212474, by rfl⟩ : syracuseStep 11233265 = 8424949) B8424949
theorem B119821493 : Blo 2049435 119821493 := bstep (se 5 (by rfl) ⟨5616632, by rfl⟩ : syracuseStep 119821493 = 11233265) B11233265
theorem B79880995 : Blo 2049435 79880995 := bstep (se 1 (by rfl) ⟨59910746, by rfl⟩ : syracuseStep 79880995 = 119821493) B119821493
theorem B426031973 : Blo 2049435 426031973 := bstep (se 4 (by rfl) ⟨39940497, by rfl⟩ : syracuseStep 426031973 = 79880995) B79880995
theorem B284021315 : Blo 2049435 284021315 := bstep (se 1 (by rfl) ⟨213015986, by rfl⟩ : syracuseStep 284021315 = 426031973) B426031973
theorem B189347543 : Blo 2049435 189347543 := bstep (se 1 (by rfl) ⟨142010657, by rfl⟩ : syracuseStep 189347543 = 284021315) B284021315
theorem B126231695 : Blo 2049435 126231695 := bstep (se 1 (by rfl) ⟨94673771, by rfl⟩ : syracuseStep 126231695 = 189347543) B189347543
theorem B84154463 : Blo 2049435 84154463 := bstep (se 1 (by rfl) ⟨63115847, by rfl⟩ : syracuseStep 84154463 = 126231695) B126231695
theorem B56102975 : Blo 2049435 56102975 := bstep (se 1 (by rfl) ⟨42077231, by rfl⟩ : syracuseStep 56102975 = 84154463) B84154463
theorem B37401983 : Blo 2049435 37401983 := bstep (se 1 (by rfl) ⟨28051487, by rfl⟩ : syracuseStep 37401983 = 56102975) B56102975
theorem B24934655 : Blo 2049435 24934655 := bstep (se 1 (by rfl) ⟨18700991, by rfl⟩ : syracuseStep 24934655 = 37401983) B37401983
theorem B16623103 : Blo 2049435 16623103 := bstep (se 1 (by rfl) ⟨12467327, by rfl⟩ : syracuseStep 16623103 = 24934655) B24934655
theorem B22164137 : Blo 2049435 22164137 := bstep (se 2 (by rfl) ⟨8311551, by rfl⟩ : syracuseStep 22164137 = 16623103) B16623103
theorem B14776091 : Blo 2049435 14776091 := bstep (se 1 (by rfl) ⟨11082068, by rfl⟩ : syracuseStep 14776091 = 22164137) B22164137
theorem B9850727 : Blo 2049435 9850727 := bstep (se 1 (by rfl) ⟨7388045, by rfl⟩ : syracuseStep 9850727 = 14776091) B14776091
theorem B6567151 : Blo 2049435 6567151 := bstep (se 1 (by rfl) ⟨4925363, by rfl⟩ : syracuseStep 6567151 = 9850727) B9850727
theorem B8756201 : Blo 2049435 8756201 := bstep (se 2 (by rfl) ⟨3283575, by rfl⟩ : syracuseStep 8756201 = 6567151) B6567151
theorem B23349869 : Blo 2049435 23349869 := bstep (se 3 (by rfl) ⟨4378100, by rfl⟩ : syracuseStep 23349869 = 8756201) B8756201
theorem B15566579 : Blo 2049435 15566579 := bstep (se 1 (by rfl) ⟨11674934, by rfl⟩ : syracuseStep 15566579 = 23349869) B23349869
theorem B10377719 : Blo 2049435 10377719 := bstep (se 1 (by rfl) ⟨7783289, by rfl⟩ : syracuseStep 10377719 = 15566579) B15566579
theorem B6918479 : Blo 2049435 6918479 := bstep (se 1 (by rfl) ⟨5188859, by rfl⟩ : syracuseStep 6918479 = 10377719) B10377719
theorem B4612319 : Blo 2049435 4612319 := bstep (se 1 (by rfl) ⟨3459239, by rfl⟩ : syracuseStep 4612319 = 6918479) B6918479
theorem B3074879 : Blo 2049435 3074879 := bstep (se 1 (by rfl) ⟨2306159, by rfl⟩ : syracuseStep 3074879 = 4612319) B4612319
theorem B2049919 : Blo 2049435 2049919 := bstep (se 1 (by rfl) ⟨1537439, by rfl⟩ : syracuseStep 2049919 = 3074879) B3074879
theorem B3074885 : Blo 2049435 3074885 := bbase (se 4 (by rfl) ⟨288270, by rfl⟩ : syracuseStep 3074885 = 576541) (by norm_num)
theorem B2049923 : Blo 2049435 2049923 := bstep (se 1 (by rfl) ⟨1537442, by rfl⟩ : syracuseStep 2049923 = 3074885) B3074885
theorem B3459253 : Blo 2049435 3459253 := bbase (se 5 (by rfl) ⟨162152, by rfl⟩ : syracuseStep 3459253 = 324305) (by norm_num)
theorem B4612337 : Blo 2049435 4612337 := bstep (se 2 (by rfl) ⟨1729626, by rfl⟩ : syracuseStep 4612337 = 3459253) B3459253
theorem B3074891 : Blo 2049435 3074891 := bstep (se 1 (by rfl) ⟨2306168, by rfl⟩ : syracuseStep 3074891 = 4612337) B4612337
theorem B2049927 : Blo 2049435 2049927 := bstep (se 1 (by rfl) ⟨1537445, by rfl⟩ : syracuseStep 2049927 = 3074891) B3074891
theorem B2306173 : Blo 2049435 2306173 := bbase (se 3 (by rfl) ⟨432407, by rfl⟩ : syracuseStep 2306173 = 864815) (by norm_num)
theorem B3074897 : Blo 2049435 3074897 := bstep (se 2 (by rfl) ⟨1153086, by rfl⟩ : syracuseStep 3074897 = 2306173) B2306173
theorem B2049931 : Blo 2049435 2049931 := bstep (se 1 (by rfl) ⟨1537448, by rfl⟩ : syracuseStep 2049931 = 3074897) B3074897
theorem B6918533 : Blo 2049435 6918533 := bbase (se 4 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 6918533 = 1297225) (by norm_num)
theorem B4612355 : Blo 2049435 4612355 := bstep (se 1 (by rfl) ⟨3459266, by rfl⟩ : syracuseStep 4612355 = 6918533) B6918533
theorem B3074903 : Blo 2049435 3074903 := bstep (se 1 (by rfl) ⟨2306177, by rfl⟩ : syracuseStep 3074903 = 4612355) B4612355
theorem B2049935 : Blo 2049435 2049935 := bstep (se 1 (by rfl) ⟨1537451, by rfl⟩ : syracuseStep 2049935 = 3074903) B3074903
theorem B3074909 : Blo 2049435 3074909 := bbase (se 3 (by rfl) ⟨576545, by rfl⟩ : syracuseStep 3074909 = 1153091) (by norm_num)
theorem B2049939 : Blo 2049435 2049939 := bstep (se 1 (by rfl) ⟨1537454, by rfl⟩ : syracuseStep 2049939 = 3074909) B3074909
theorem B4612373 : Blo 2049435 4612373 := bbase (se 6 (by rfl) ⟨108102, by rfl⟩ : syracuseStep 4612373 = 216205) (by norm_num)
theorem B3074915 : Blo 2049435 3074915 := bstep (se 1 (by rfl) ⟨2306186, by rfl⟩ : syracuseStep 3074915 = 4612373) B4612373
theorem B2049943 : Blo 2049435 2049943 := bstep (se 1 (by rfl) ⟨1537457, by rfl⟩ : syracuseStep 2049943 = 3074915) B3074915
theorem B7783397 : Blo 2049435 7783397 := bbase (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) (by norm_num)
theorem B5188931 : Blo 2049435 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B3459287 : Blo 2049435 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B2306191 : Blo 2049435 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B3074921 : Blo 2049435 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B2049947 : Blo 2049435 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B2077921 : Blo 2049435 2077921 := bbase (se 2 (by rfl) ⟨779220, by rfl⟩ : syracuseStep 2077921 = 1558441) (by norm_num)
theorem B2770561 : Blo 2049435 2770561 := bstep (se 2 (by rfl) ⟨1038960, by rfl⟩ : syracuseStep 2770561 = 2077921) B2077921
theorem B3694081 : Blo 2049435 3694081 := bstep (se 2 (by rfl) ⟨1385280, by rfl⟩ : syracuseStep 3694081 = 2770561) B2770561
theorem B4925441 : Blo 2049435 4925441 := bstep (se 2 (by rfl) ⟨1847040, by rfl⟩ : syracuseStep 4925441 = 3694081) B3694081
theorem B3283627 : Blo 2049435 3283627 := bstep (se 1 (by rfl) ⟨2462720, by rfl⟩ : syracuseStep 3283627 = 4925441) B4925441
theorem B4378169 : Blo 2049435 4378169 := bstep (se 2 (by rfl) ⟨1641813, by rfl⟩ : syracuseStep 4378169 = 3283627) B3283627
theorem B11675117 : Blo 2049435 11675117 := bstep (se 3 (by rfl) ⟨2189084, by rfl⟩ : syracuseStep 11675117 = 4378169) B4378169
theorem B7783411 : Blo 2049435 7783411 := bstep (se 1 (by rfl) ⟨5837558, by rfl⟩ : syracuseStep 7783411 = 11675117) B11675117
theorem B10377881 : Blo 2049435 10377881 := bstep (se 2 (by rfl) ⟨3891705, by rfl⟩ : syracuseStep 10377881 = 7783411) B7783411
theorem B6918587 : Blo 2049435 6918587 := bstep (se 1 (by rfl) ⟨5188940, by rfl⟩ : syracuseStep 6918587 = 10377881) B10377881
theorem B4612391 : Blo 2049435 4612391 := bstep (se 1 (by rfl) ⟨3459293, by rfl⟩ : syracuseStep 4612391 = 6918587) B6918587
theorem B3074927 : Blo 2049435 3074927 := bstep (se 1 (by rfl) ⟨2306195, by rfl⟩ : syracuseStep 3074927 = 4612391) B4612391
theorem B2049951 : Blo 2049435 2049951 := bstep (se 1 (by rfl) ⟨1537463, by rfl⟩ : syracuseStep 2049951 = 3074927) B3074927
theorem B3074933 : Blo 2049435 3074933 := bbase (se 5 (by rfl) ⟨144137, by rfl⟩ : syracuseStep 3074933 = 288275) (by norm_num)
theorem B2049955 : Blo 2049435 2049955 := bstep (se 1 (by rfl) ⟨1537466, by rfl⟩ : syracuseStep 2049955 = 3074933) B3074933
theorem B4925461 : Blo 2049435 4925461 := bbase (se 6 (by rfl) ⟨115440, by rfl⟩ : syracuseStep 4925461 = 230881) (by norm_num)
theorem B6567281 : Blo 2049435 6567281 := bstep (se 2 (by rfl) ⟨2462730, by rfl⟩ : syracuseStep 6567281 = 4925461) B4925461
theorem B4378187 : Blo 2049435 4378187 := bstep (se 1 (by rfl) ⟨3283640, by rfl⟩ : syracuseStep 4378187 = 6567281) B6567281
theorem B2918791 : Blo 2049435 2918791 := bstep (se 1 (by rfl) ⟨2189093, by rfl⟩ : syracuseStep 2918791 = 4378187) B4378187
theorem B3891721 : Blo 2049435 3891721 := bstep (se 2 (by rfl) ⟨1459395, by rfl⟩ : syracuseStep 3891721 = 2918791) B2918791
theorem B5188961 : Blo 2049435 5188961 := bstep (se 2 (by rfl) ⟨1945860, by rfl⟩ : syracuseStep 5188961 = 3891721) B3891721
theorem B3459307 : Blo 2049435 3459307 := bstep (se 1 (by rfl) ⟨2594480, by rfl⟩ : syracuseStep 3459307 = 5188961) B5188961
theorem B4612409 : Blo 2049435 4612409 := bstep (se 2 (by rfl) ⟨1729653, by rfl⟩ : syracuseStep 4612409 = 3459307) B3459307
theorem B3074939 : Blo 2049435 3074939 := bstep (se 1 (by rfl) ⟨2306204, by rfl⟩ : syracuseStep 3074939 = 4612409) B4612409
theorem B2049959 : Blo 2049435 2049959 := bstep (se 1 (by rfl) ⟨1537469, by rfl⟩ : syracuseStep 2049959 = 3074939) B3074939
theorem B2306209 : Blo 2049435 2306209 := bbase (se 2 (by rfl) ⟨864828, by rfl⟩ : syracuseStep 2306209 = 1729657) (by norm_num)
theorem B3074945 : Blo 2049435 3074945 := bstep (se 2 (by rfl) ⟨1153104, by rfl⟩ : syracuseStep 3074945 = 2306209) B2306209
theorem B2049963 : Blo 2049435 2049963 := bstep (se 1 (by rfl) ⟨1537472, by rfl⟩ : syracuseStep 2049963 = 3074945) B3074945
theorem B5188981 : Blo 2049435 5188981 := bbase (se 5 (by rfl) ⟨243233, by rfl⟩ : syracuseStep 5188981 = 486467) (by norm_num)
theorem B6918641 : Blo 2049435 6918641 := bstep (se 2 (by rfl) ⟨2594490, by rfl⟩ : syracuseStep 6918641 = 5188981) B5188981
theorem B4612427 : Blo 2049435 4612427 := bstep (se 1 (by rfl) ⟨3459320, by rfl⟩ : syracuseStep 4612427 = 6918641) B6918641
theorem B3074951 : Blo 2049435 3074951 := bstep (se 1 (by rfl) ⟨2306213, by rfl⟩ : syracuseStep 3074951 = 4612427) B4612427
theorem B2049967 : Blo 2049435 2049967 := bstep (se 1 (by rfl) ⟨1537475, by rfl⟩ : syracuseStep 2049967 = 3074951) B3074951
theorem B3074957 : Blo 2049435 3074957 := bbase (se 3 (by rfl) ⟨576554, by rfl⟩ : syracuseStep 3074957 = 1153109) (by norm_num)
theorem B2049971 : Blo 2049435 2049971 := bstep (se 1 (by rfl) ⟨1537478, by rfl⟩ : syracuseStep 2049971 = 3074957) B3074957
theorem B4612445 : Blo 2049435 4612445 := bbase (se 3 (by rfl) ⟨864833, by rfl⟩ : syracuseStep 4612445 = 1729667) (by norm_num)
theorem B3074963 : Blo 2049435 3074963 := bstep (se 1 (by rfl) ⟨2306222, by rfl⟩ : syracuseStep 3074963 = 4612445) B4612445
theorem B2049975 : Blo 2049435 2049975 := bstep (se 1 (by rfl) ⟨1537481, by rfl⟩ : syracuseStep 2049975 = 3074963) B3074963
theorem B3459341 : Blo 2049435 3459341 := bbase (se 3 (by rfl) ⟨648626, by rfl⟩ : syracuseStep 3459341 = 1297253) (by norm_num)
theorem B2306227 : Blo 2049435 2306227 := bstep (se 1 (by rfl) ⟨1729670, by rfl⟩ : syracuseStep 2306227 = 3459341) B3459341
theorem B3074969 : Blo 2049435 3074969 := bstep (se 2 (by rfl) ⟨1153113, by rfl⟩ : syracuseStep 3074969 = 2306227) B2306227
theorem B2049979 : Blo 2049435 2049979 := bstep (se 1 (by rfl) ⟨1537484, by rfl⟩ : syracuseStep 2049979 = 3074969) B3074969
theorem B17512949 : Blo 2049435 17512949 := bbase (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) (by norm_num)
theorem B11675299 : Blo 2049435 11675299 := bstep (se 1 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 11675299 = 17512949) B17512949
theorem B15567065 : Blo 2049435 15567065 := bstep (se 2 (by rfl) ⟨5837649, by rfl⟩ : syracuseStep 15567065 = 11675299) B11675299
theorem B10378043 : Blo 2049435 10378043 := bstep (se 1 (by rfl) ⟨7783532, by rfl⟩ : syracuseStep 10378043 = 15567065) B15567065
theorem B6918695 : Blo 2049435 6918695 := bstep (se 1 (by rfl) ⟨5189021, by rfl⟩ : syracuseStep 6918695 = 10378043) B10378043
theorem B4612463 : Blo 2049435 4612463 := bstep (se 1 (by rfl) ⟨3459347, by rfl⟩ : syracuseStep 4612463 = 6918695) B6918695
theorem B3074975 : Blo 2049435 3074975 := bstep (se 1 (by rfl) ⟨2306231, by rfl⟩ : syracuseStep 3074975 = 4612463) B4612463
theorem B2049983 : Blo 2049435 2049983 := bstep (se 1 (by rfl) ⟨1537487, by rfl⟩ : syracuseStep 2049983 = 3074975) B3074975
theorem B3074981 : Blo 2049435 3074981 := bbase (se 4 (by rfl) ⟨288279, by rfl⟩ : syracuseStep 3074981 = 576559) (by norm_num)
theorem B2049987 : Blo 2049435 2049987 := bstep (se 1 (by rfl) ⟨1537490, by rfl⟩ : syracuseStep 2049987 = 3074981) B3074981
theorem B2594521 : Blo 2049435 2594521 := bbase (se 2 (by rfl) ⟨972945, by rfl⟩ : syracuseStep 2594521 = 1945891) (by norm_num)
theorem B3459361 : Blo 2049435 3459361 := bstep (se 2 (by rfl) ⟨1297260, by rfl⟩ : syracuseStep 3459361 = 2594521) B2594521
theorem B4612481 : Blo 2049435 4612481 := bstep (se 2 (by rfl) ⟨1729680, by rfl⟩ : syracuseStep 4612481 = 3459361) B3459361
theorem B3074987 : Blo 2049435 3074987 := bstep (se 1 (by rfl) ⟨2306240, by rfl⟩ : syracuseStep 3074987 = 4612481) B4612481
theorem B2049991 : Blo 2049435 2049991 := bstep (se 1 (by rfl) ⟨1537493, by rfl⟩ : syracuseStep 2049991 = 3074987) B3074987
theorem B2306245 : Blo 2049435 2306245 := bbase (se 4 (by rfl) ⟨216210, by rfl⟩ : syracuseStep 2306245 = 432421) (by norm_num)
theorem B3074993 : Blo 2049435 3074993 := bstep (se 2 (by rfl) ⟨1153122, by rfl⟩ : syracuseStep 3074993 = 2306245) B2306245
theorem B2049995 : Blo 2049435 2049995 := bstep (se 1 (by rfl) ⟨1537496, by rfl⟩ : syracuseStep 2049995 = 3074993) B3074993
theorem B3891797 : Blo 2049435 3891797 := bbase (se 8 (by rfl) ⟨22803, by rfl⟩ : syracuseStep 3891797 = 45607) (by norm_num)
theorem B2594531 : Blo 2049435 2594531 := bstep (se 1 (by rfl) ⟨1945898, by rfl⟩ : syracuseStep 2594531 = 3891797) B3891797
theorem B6918749 : Blo 2049435 6918749 := bstep (se 3 (by rfl) ⟨1297265, by rfl⟩ : syracuseStep 6918749 = 2594531) B2594531
theorem B4612499 : Blo 2049435 4612499 := bstep (se 1 (by rfl) ⟨3459374, by rfl⟩ : syracuseStep 4612499 = 6918749) B6918749
theorem B3074999 : Blo 2049435 3074999 := bstep (se 1 (by rfl) ⟨2306249, by rfl⟩ : syracuseStep 3074999 = 4612499) B4612499
theorem B2049999 : Blo 2049435 2049999 := bstep (se 1 (by rfl) ⟨1537499, by rfl⟩ : syracuseStep 2049999 = 3074999) B3074999
theorem B3075005 : Blo 2049435 3075005 := bbase (se 3 (by rfl) ⟨576563, by rfl⟩ : syracuseStep 3075005 = 1153127) (by norm_num)
theorem B2050003 : Blo 2049435 2050003 := bstep (se 1 (by rfl) ⟨1537502, by rfl⟩ : syracuseStep 2050003 = 3075005) B3075005
theorem B4612517 : Blo 2049435 4612517 := bbase (se 4 (by rfl) ⟨432423, by rfl⟩ : syracuseStep 4612517 = 864847) (by norm_num)
theorem B3075011 : Blo 2049435 3075011 := bstep (se 1 (by rfl) ⟨2306258, by rfl⟩ : syracuseStep 3075011 = 4612517) B4612517
theorem B2050007 : Blo 2049435 2050007 := bstep (se 1 (by rfl) ⟨1537505, by rfl⟩ : syracuseStep 2050007 = 3075011) B3075011
theorem B5189093 : Blo 2049435 5189093 := bbase (se 4 (by rfl) ⟨486477, by rfl⟩ : syracuseStep 5189093 = 972955) (by norm_num)
theorem B3459395 : Blo 2049435 3459395 := bstep (se 1 (by rfl) ⟨2594546, by rfl⟩ : syracuseStep 3459395 = 5189093) B5189093
theorem B2306263 : Blo 2049435 2306263 := bstep (se 1 (by rfl) ⟨1729697, by rfl⟩ : syracuseStep 2306263 = 3459395) B3459395
theorem B3075017 : Blo 2049435 3075017 := bstep (se 2 (by rfl) ⟨1153131, by rfl⟩ : syracuseStep 3075017 = 2306263) B2306263
theorem B2050011 : Blo 2049435 2050011 := bstep (se 1 (by rfl) ⟨1537508, by rfl⟩ : syracuseStep 2050011 = 3075017) B3075017
theorem B2189153 : Blo 2049435 2189153 := bbase (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) (by norm_num)
theorem B5837741 : Blo 2049435 5837741 := bstep (se 3 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 5837741 = 2189153) B2189153
theorem B3891827 : Blo 2049435 3891827 := bstep (se 1 (by rfl) ⟨2918870, by rfl⟩ : syracuseStep 3891827 = 5837741) B5837741
theorem B10378205 : Blo 2049435 10378205 := bstep (se 3 (by rfl) ⟨1945913, by rfl⟩ : syracuseStep 10378205 = 3891827) B3891827
theorem B6918803 : Blo 2049435 6918803 := bstep (se 1 (by rfl) ⟨5189102, by rfl⟩ : syracuseStep 6918803 = 10378205) B10378205
theorem B4612535 : Blo 2049435 4612535 := bstep (se 1 (by rfl) ⟨3459401, by rfl⟩ : syracuseStep 4612535 = 6918803) B6918803
theorem B3075023 : Blo 2049435 3075023 := bstep (se 1 (by rfl) ⟨2306267, by rfl⟩ : syracuseStep 3075023 = 4612535) B4612535
theorem B2050015 : Blo 2049435 2050015 := bstep (se 1 (by rfl) ⟨1537511, by rfl⟩ : syracuseStep 2050015 = 3075023) B3075023
theorem B3075029 : Blo 2049435 3075029 := bbase (se 7 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 3075029 = 72071) (by norm_num)
theorem B2050019 : Blo 2049435 2050019 := bstep (se 1 (by rfl) ⟨1537514, by rfl⟩ : syracuseStep 2050019 = 3075029) B3075029
theorem B7783685 : Blo 2049435 7783685 := bbase (se 4 (by rfl) ⟨729720, by rfl⟩ : syracuseStep 7783685 = 1459441) (by norm_num)
theorem B5189123 : Blo 2049435 5189123 := bstep (se 1 (by rfl) ⟨3891842, by rfl⟩ : syracuseStep 5189123 = 7783685) B7783685
theorem B3459415 : Blo 2049435 3459415 := bstep (se 1 (by rfl) ⟨2594561, by rfl⟩ : syracuseStep 3459415 = 5189123) B5189123
theorem B4612553 : Blo 2049435 4612553 := bstep (se 2 (by rfl) ⟨1729707, by rfl⟩ : syracuseStep 4612553 = 3459415) B3459415
theorem B3075035 : Blo 2049435 3075035 := bstep (se 1 (by rfl) ⟨2306276, by rfl⟩ : syracuseStep 3075035 = 4612553) B4612553
theorem B2050023 : Blo 2049435 2050023 := bstep (se 1 (by rfl) ⟨1537517, by rfl⟩ : syracuseStep 2050023 = 3075035) B3075035
theorem B2306281 : Blo 2049435 2306281 := bbase (se 2 (by rfl) ⟨864855, by rfl⟩ : syracuseStep 2306281 = 1729711) (by norm_num)
theorem B3075041 : Blo 2049435 3075041 := bstep (se 2 (by rfl) ⟨1153140, by rfl⟩ : syracuseStep 3075041 = 2306281) B2306281
theorem B2050027 : Blo 2049435 2050027 := bstep (se 1 (by rfl) ⟨1537520, by rfl⟩ : syracuseStep 2050027 = 3075041) B3075041
theorem B11675573 : Blo 2049435 11675573 := bbase (se 5 (by rfl) ⟨547292, by rfl⟩ : syracuseStep 11675573 = 1094585) (by norm_num)
theorem B7783715 : Blo 2049435 7783715 := bstep (se 1 (by rfl) ⟨5837786, by rfl⟩ : syracuseStep 7783715 = 11675573) B11675573
theorem B5189143 : Blo 2049435 5189143 := bstep (se 1 (by rfl) ⟨3891857, by rfl⟩ : syracuseStep 5189143 = 7783715) B7783715
theorem B6918857 : Blo 2049435 6918857 := bstep (se 2 (by rfl) ⟨2594571, by rfl⟩ : syracuseStep 6918857 = 5189143) B5189143
theorem B4612571 : Blo 2049435 4612571 := bstep (se 1 (by rfl) ⟨3459428, by rfl⟩ : syracuseStep 4612571 = 6918857) B6918857
theorem B3075047 : Blo 2049435 3075047 := bstep (se 1 (by rfl) ⟨2306285, by rfl⟩ : syracuseStep 3075047 = 4612571) B4612571
theorem B2050031 : Blo 2049435 2050031 := bstep (se 1 (by rfl) ⟨1537523, by rfl⟩ : syracuseStep 2050031 = 3075047) B3075047
theorem B3075053 : Blo 2049435 3075053 := bbase (se 3 (by rfl) ⟨576572, by rfl⟩ : syracuseStep 3075053 = 1153145) (by norm_num)
theorem B2050035 : Blo 2049435 2050035 := bstep (se 1 (by rfl) ⟨1537526, by rfl⟩ : syracuseStep 2050035 = 3075053) B3075053
theorem B4612589 : Blo 2049435 4612589 := bbase (se 3 (by rfl) ⟨864860, by rfl⟩ : syracuseStep 4612589 = 1729721) (by norm_num)
theorem B3075059 : Blo 2049435 3075059 := bstep (se 1 (by rfl) ⟨2306294, by rfl⟩ : syracuseStep 3075059 = 4612589) B4612589
theorem B2050039 : Blo 2049435 2050039 := bstep (se 1 (by rfl) ⟨1537529, by rfl⟩ : syracuseStep 2050039 = 3075059) B3075059
theorem B5130037 : Blo 2049435 5130037 := bbase (se 5 (by rfl) ⟨240470, by rfl⟩ : syracuseStep 5130037 = 480941) (by norm_num)
theorem B6840049 : Blo 2049435 6840049 := bstep (se 2 (by rfl) ⟨2565018, by rfl⟩ : syracuseStep 6840049 = 5130037) B5130037
theorem B9120065 : Blo 2049435 9120065 := bstep (se 2 (by rfl) ⟨3420024, by rfl⟩ : syracuseStep 9120065 = 6840049) B6840049
theorem B24320173 : Blo 2049435 24320173 := bstep (se 3 (by rfl) ⟨4560032, by rfl⟩ : syracuseStep 24320173 = 9120065) B9120065
theorem B32426897 : Blo 2049435 32426897 := bstep (se 2 (by rfl) ⟨12160086, by rfl⟩ : syracuseStep 32426897 = 24320173) B24320173
theorem B86471725 : Blo 2049435 86471725 := bstep (se 3 (by rfl) ⟨16213448, by rfl⟩ : syracuseStep 86471725 = 32426897) B32426897
theorem B115295633 : Blo 2049435 115295633 := bstep (se 2 (by rfl) ⟨43235862, by rfl⟩ : syracuseStep 115295633 = 86471725) B86471725
theorem B76863755 : Blo 2049435 76863755 := bstep (se 1 (by rfl) ⟨57647816, by rfl⟩ : syracuseStep 76863755 = 115295633) B115295633
theorem B51242503 : Blo 2049435 51242503 := bstep (se 1 (by rfl) ⟨38431877, by rfl⟩ : syracuseStep 51242503 = 76863755) B76863755
theorem B68323337 : Blo 2049435 68323337 := bstep (se 2 (by rfl) ⟨25621251, by rfl⟩ : syracuseStep 68323337 = 51242503) B51242503
theorem B45548891 : Blo 2049435 45548891 := bstep (se 1 (by rfl) ⟨34161668, by rfl⟩ : syracuseStep 45548891 = 68323337) B68323337
theorem B30365927 : Blo 2049435 30365927 := bstep (se 1 (by rfl) ⟨22774445, by rfl⟩ : syracuseStep 30365927 = 45548891) B45548891
theorem B20243951 : Blo 2049435 20243951 := bstep (se 1 (by rfl) ⟨15182963, by rfl⟩ : syracuseStep 20243951 = 30365927) B30365927
theorem B13495967 : Blo 2049435 13495967 := bstep (se 1 (by rfl) ⟨10121975, by rfl⟩ : syracuseStep 13495967 = 20243951) B20243951
theorem B8997311 : Blo 2049435 8997311 := bstep (se 1 (by rfl) ⟨6747983, by rfl⟩ : syracuseStep 8997311 = 13495967) B13495967
theorem B5998207 : Blo 2049435 5998207 := bstep (se 1 (by rfl) ⟨4498655, by rfl⟩ : syracuseStep 5998207 = 8997311) B8997311
theorem B7997609 : Blo 2049435 7997609 := bstep (se 2 (by rfl) ⟨2999103, by rfl⟩ : syracuseStep 7997609 = 5998207) B5998207
theorem B5331739 : Blo 2049435 5331739 := bstep (se 1 (by rfl) ⟨3998804, by rfl⟩ : syracuseStep 5331739 = 7997609) B7997609
theorem B7108985 : Blo 2049435 7108985 := bstep (se 2 (by rfl) ⟨2665869, by rfl⟩ : syracuseStep 7108985 = 5331739) B5331739
theorem B18957293 : Blo 2049435 18957293 := bstep (se 3 (by rfl) ⟨3554492, by rfl⟩ : syracuseStep 18957293 = 7108985) B7108985
theorem B12638195 : Blo 2049435 12638195 := bstep (se 1 (by rfl) ⟨9478646, by rfl⟩ : syracuseStep 12638195 = 18957293) B18957293
theorem B8425463 : Blo 2049435 8425463 := bstep (se 1 (by rfl) ⟨6319097, by rfl⟩ : syracuseStep 8425463 = 12638195) B12638195
theorem B22467901 : Blo 2049435 22467901 := bstep (se 3 (by rfl) ⟨4212731, by rfl⟩ : syracuseStep 22467901 = 8425463) B8425463
theorem B29957201 : Blo 2049435 29957201 := bstep (se 2 (by rfl) ⟨11233950, by rfl⟩ : syracuseStep 29957201 = 22467901) B22467901
theorem B19971467 : Blo 2049435 19971467 := bstep (se 1 (by rfl) ⟨14978600, by rfl⟩ : syracuseStep 19971467 = 29957201) B29957201
theorem B13314311 : Blo 2049435 13314311 := bstep (se 1 (by rfl) ⟨9985733, by rfl⟩ : syracuseStep 13314311 = 19971467) B19971467
theorem B8876207 : Blo 2049435 8876207 := bstep (se 1 (by rfl) ⟨6657155, by rfl⟩ : syracuseStep 8876207 = 13314311) B13314311
theorem B5917471 : Blo 2049435 5917471 := bstep (se 1 (by rfl) ⟨4438103, by rfl⟩ : syracuseStep 5917471 = 8876207) B8876207
theorem B126239381 : Blo 2049435 126239381 := bstep (se 6 (by rfl) ⟨2958735, by rfl⟩ : syracuseStep 126239381 = 5917471) B5917471
theorem B84159587 : Blo 2049435 84159587 := bstep (se 1 (by rfl) ⟨63119690, by rfl⟩ : syracuseStep 84159587 = 126239381) B126239381
theorem B56106391 : Blo 2049435 56106391 := bstep (se 1 (by rfl) ⟨42079793, by rfl⟩ : syracuseStep 56106391 = 84159587) B84159587
theorem B74808521 : Blo 2049435 74808521 := bstep (se 2 (by rfl) ⟨28053195, by rfl⟩ : syracuseStep 74808521 = 56106391) B56106391
theorem B49872347 : Blo 2049435 49872347 := bstep (se 1 (by rfl) ⟨37404260, by rfl⟩ : syracuseStep 49872347 = 74808521) B74808521
theorem B33248231 : Blo 2049435 33248231 := bstep (se 1 (by rfl) ⟨24936173, by rfl⟩ : syracuseStep 33248231 = 49872347) B49872347
theorem B22165487 : Blo 2049435 22165487 := bstep (se 1 (by rfl) ⟨16624115, by rfl⟩ : syracuseStep 22165487 = 33248231) B33248231
theorem B14776991 : Blo 2049435 14776991 := bstep (se 1 (by rfl) ⟨11082743, by rfl⟩ : syracuseStep 14776991 = 22165487) B22165487
theorem B9851327 : Blo 2049435 9851327 := bstep (se 1 (by rfl) ⟨7388495, by rfl⟩ : syracuseStep 9851327 = 14776991) B14776991
theorem B6567551 : Blo 2049435 6567551 := bstep (se 1 (by rfl) ⟨4925663, by rfl⟩ : syracuseStep 6567551 = 9851327) B9851327
theorem B4378367 : Blo 2049435 4378367 := bstep (se 1 (by rfl) ⟨3283775, by rfl⟩ : syracuseStep 4378367 = 6567551) B6567551
theorem B2918911 : Blo 2049435 2918911 := bstep (se 1 (by rfl) ⟨2189183, by rfl⟩ : syracuseStep 2918911 = 4378367) B4378367
theorem B3891881 : Blo 2049435 3891881 := bstep (se 2 (by rfl) ⟨1459455, by rfl⟩ : syracuseStep 3891881 = 2918911) B2918911
theorem B2594587 : Blo 2049435 2594587 := bstep (se 1 (by rfl) ⟨1945940, by rfl⟩ : syracuseStep 2594587 = 3891881) B3891881
theorem B3459449 : Blo 2049435 3459449 := bstep (se 2 (by rfl) ⟨1297293, by rfl⟩ : syracuseStep 3459449 = 2594587) B2594587
theorem B2306299 : Blo 2049435 2306299 := bstep (se 1 (by rfl) ⟨1729724, by rfl⟩ : syracuseStep 2306299 = 3459449) B3459449
theorem B3075065 : Blo 2049435 3075065 := bstep (se 2 (by rfl) ⟨1153149, by rfl⟩ : syracuseStep 3075065 = 2306299) B2306299
theorem B2050043 : Blo 2049435 2050043 := bstep (se 1 (by rfl) ⟨1537532, by rfl⟩ : syracuseStep 2050043 = 3075065) B3075065
theorem B2369665 : Blo 2049435 2369665 := bbase (se 2 (by rfl) ⟨888624, by rfl⟩ : syracuseStep 2369665 = 1777249) (by norm_num)
theorem B12638213 : Blo 2049435 12638213 := bstep (se 4 (by rfl) ⟨1184832, by rfl⟩ : syracuseStep 12638213 = 2369665) B2369665
theorem B8425475 : Blo 2049435 8425475 := bstep (se 1 (by rfl) ⟨6319106, by rfl⟩ : syracuseStep 8425475 = 12638213) B12638213
theorem B5616983 : Blo 2049435 5616983 := bstep (se 1 (by rfl) ⟨4212737, by rfl⟩ : syracuseStep 5616983 = 8425475) B8425475
theorem B14978621 : Blo 2049435 14978621 := bstep (se 3 (by rfl) ⟨2808491, by rfl⟩ : syracuseStep 14978621 = 5616983) B5616983
theorem B39942989 : Blo 2049435 39942989 := bstep (se 3 (by rfl) ⟨7489310, by rfl⟩ : syracuseStep 39942989 = 14978621) B14978621
theorem B26628659 : Blo 2049435 26628659 := bstep (se 1 (by rfl) ⟨19971494, by rfl⟩ : syracuseStep 26628659 = 39942989) B39942989
theorem B17752439 : Blo 2049435 17752439 := bstep (se 1 (by rfl) ⟨13314329, by rfl⟩ : syracuseStep 17752439 = 26628659) B26628659
theorem B11834959 : Blo 2049435 11834959 := bstep (se 1 (by rfl) ⟨8876219, by rfl⟩ : syracuseStep 11834959 = 17752439) B17752439
theorem B15779945 : Blo 2049435 15779945 := bstep (se 2 (by rfl) ⟨5917479, by rfl⟩ : syracuseStep 15779945 = 11834959) B11834959
theorem B10519963 : Blo 2049435 10519963 := bstep (se 1 (by rfl) ⟨7889972, by rfl⟩ : syracuseStep 10519963 = 15779945) B15779945
theorem B56106469 : Blo 2049435 56106469 := bstep (se 4 (by rfl) ⟨5259981, by rfl⟩ : syracuseStep 56106469 = 10519963) B10519963
theorem B74808625 : Blo 2049435 74808625 := bstep (se 2 (by rfl) ⟨28053234, by rfl⟩ : syracuseStep 74808625 = 56106469) B56106469
theorem B99744833 : Blo 2049435 99744833 := bstep (se 2 (by rfl) ⟨37404312, by rfl⟩ : syracuseStep 99744833 = 74808625) B74808625
theorem B66496555 : Blo 2049435 66496555 := bstep (se 1 (by rfl) ⟨49872416, by rfl⟩ : syracuseStep 66496555 = 99744833) B99744833
theorem B88662073 : Blo 2049435 88662073 := bstep (se 2 (by rfl) ⟨33248277, by rfl⟩ : syracuseStep 88662073 = 66496555) B66496555
theorem B118216097 : Blo 2049435 118216097 := bstep (se 2 (by rfl) ⟨44331036, by rfl⟩ : syracuseStep 118216097 = 88662073) B88662073
theorem B78810731 : Blo 2049435 78810731 := bstep (se 1 (by rfl) ⟨59108048, by rfl⟩ : syracuseStep 78810731 = 118216097) B118216097
theorem B52540487 : Blo 2049435 52540487 := bstep (se 1 (by rfl) ⟨39405365, by rfl⟩ : syracuseStep 52540487 = 78810731) B78810731
theorem B35026991 : Blo 2049435 35026991 := bstep (se 1 (by rfl) ⟨26270243, by rfl⟩ : syracuseStep 35026991 = 52540487) B52540487
theorem B23351327 : Blo 2049435 23351327 := bstep (se 1 (by rfl) ⟨17513495, by rfl⟩ : syracuseStep 23351327 = 35026991) B35026991
theorem B15567551 : Blo 2049435 15567551 := bstep (se 1 (by rfl) ⟨11675663, by rfl⟩ : syracuseStep 15567551 = 23351327) B23351327
theorem B10378367 : Blo 2049435 10378367 := bstep (se 1 (by rfl) ⟨7783775, by rfl⟩ : syracuseStep 10378367 = 15567551) B15567551
theorem B6918911 : Blo 2049435 6918911 := bstep (se 1 (by rfl) ⟨5189183, by rfl⟩ : syracuseStep 6918911 = 10378367) B10378367
theorem B4612607 : Blo 2049435 4612607 := bstep (se 1 (by rfl) ⟨3459455, by rfl⟩ : syracuseStep 4612607 = 6918911) B6918911
theorem B3075071 : Blo 2049435 3075071 := bstep (se 1 (by rfl) ⟨2306303, by rfl⟩ : syracuseStep 3075071 = 4612607) B4612607
theorem B2050047 : Blo 2049435 2050047 := bstep (se 1 (by rfl) ⟨1537535, by rfl⟩ : syracuseStep 2050047 = 3075071) B3075071
theorem B3075077 : Blo 2049435 3075077 := bbase (se 4 (by rfl) ⟨288288, by rfl⟩ : syracuseStep 3075077 = 576577) (by norm_num)
theorem B2050051 : Blo 2049435 2050051 := bstep (se 1 (by rfl) ⟨1537538, by rfl⟩ : syracuseStep 2050051 = 3075077) B3075077
theorem B3459469 : Blo 2049435 3459469 := bbase (se 3 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 3459469 = 1297301) (by norm_num)
theorem B4612625 : Blo 2049435 4612625 := bstep (se 2 (by rfl) ⟨1729734, by rfl⟩ : syracuseStep 4612625 = 3459469) B3459469
theorem B3075083 : Blo 2049435 3075083 := bstep (se 1 (by rfl) ⟨2306312, by rfl⟩ : syracuseStep 3075083 = 4612625) B4612625
theorem B2050055 : Blo 2049435 2050055 := bstep (se 1 (by rfl) ⟨1537541, by rfl⟩ : syracuseStep 2050055 = 3075083) B3075083
theorem B2306317 : Blo 2049435 2306317 := bbase (se 3 (by rfl) ⟨432434, by rfl⟩ : syracuseStep 2306317 = 864869) (by norm_num)
theorem B3075089 : Blo 2049435 3075089 := bstep (se 2 (by rfl) ⟨1153158, by rfl⟩ : syracuseStep 3075089 = 2306317) B2306317
theorem B2050059 : Blo 2049435 2050059 := bstep (se 1 (by rfl) ⟨1537544, by rfl⟩ : syracuseStep 2050059 = 3075089) B3075089
theorem B6918965 : Blo 2049435 6918965 := bbase (se 5 (by rfl) ⟨324326, by rfl⟩ : syracuseStep 6918965 = 648653) (by norm_num)
theorem B4612643 : Blo 2049435 4612643 := bstep (se 1 (by rfl) ⟨3459482, by rfl⟩ : syracuseStep 4612643 = 6918965) B6918965
theorem B3075095 : Blo 2049435 3075095 := bstep (se 1 (by rfl) ⟨2306321, by rfl⟩ : syracuseStep 3075095 = 4612643) B4612643
theorem B2050063 : Blo 2049435 2050063 := bstep (se 1 (by rfl) ⟨1537547, by rfl⟩ : syracuseStep 2050063 = 3075095) B3075095
theorem B3075101 : Blo 2049435 3075101 := bbase (se 3 (by rfl) ⟨576581, by rfl⟩ : syracuseStep 3075101 = 1153163) (by norm_num)
theorem B2050067 : Blo 2049435 2050067 := bstep (se 1 (by rfl) ⟨1537550, by rfl⟩ : syracuseStep 2050067 = 3075101) B3075101
theorem B4612661 : Blo 2049435 4612661 := bbase (se 5 (by rfl) ⟨216218, by rfl⟩ : syracuseStep 4612661 = 432437) (by norm_num)
theorem B3075107 : Blo 2049435 3075107 := bstep (se 1 (by rfl) ⟨2306330, by rfl⟩ : syracuseStep 3075107 = 4612661) B4612661
theorem B2050071 : Blo 2049435 2050071 := bstep (se 1 (by rfl) ⟨1537553, by rfl⟩ : syracuseStep 2050071 = 3075107) B3075107
theorem B8756869 : Blo 2049435 8756869 := bbase (se 4 (by rfl) ⟨820956, by rfl⟩ : syracuseStep 8756869 = 1641913) (by norm_num)
theorem B11675825 : Blo 2049435 11675825 := bstep (se 2 (by rfl) ⟨4378434, by rfl⟩ : syracuseStep 11675825 = 8756869) B8756869
theorem B7783883 : Blo 2049435 7783883 := bstep (se 1 (by rfl) ⟨5837912, by rfl⟩ : syracuseStep 7783883 = 11675825) B11675825
theorem B5189255 : Blo 2049435 5189255 := bstep (se 1 (by rfl) ⟨3891941, by rfl⟩ : syracuseStep 5189255 = 7783883) B7783883
theorem B3459503 : Blo 2049435 3459503 := bstep (se 1 (by rfl) ⟨2594627, by rfl⟩ : syracuseStep 3459503 = 5189255) B5189255
theorem B2306335 : Blo 2049435 2306335 := bstep (se 1 (by rfl) ⟨1729751, by rfl⟩ : syracuseStep 2306335 = 3459503) B3459503
theorem B3075113 : Blo 2049435 3075113 := bstep (se 2 (by rfl) ⟨1153167, by rfl⟩ : syracuseStep 3075113 = 2306335) B2306335
theorem B2050075 : Blo 2049435 2050075 := bstep (se 1 (by rfl) ⟨1537556, by rfl⟩ : syracuseStep 2050075 = 3075113) B3075113
theorem B8756885 : Blo 2049435 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B5837923 : Blo 2049435 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B7783897 : Blo 2049435 7783897 := bstep (se 2 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 7783897 = 5837923) B5837923
theorem B10378529 : Blo 2049435 10378529 := bstep (se 2 (by rfl) ⟨3891948, by rfl⟩ : syracuseStep 10378529 = 7783897) B7783897
theorem B6919019 : Blo 2049435 6919019 := bstep (se 1 (by rfl) ⟨5189264, by rfl⟩ : syracuseStep 6919019 = 10378529) B10378529
theorem B4612679 : Blo 2049435 4612679 := bstep (se 1 (by rfl) ⟨3459509, by rfl⟩ : syracuseStep 4612679 = 6919019) B6919019
theorem B3075119 : Blo 2049435 3075119 := bstep (se 1 (by rfl) ⟨2306339, by rfl⟩ : syracuseStep 3075119 = 4612679) B4612679
theorem B2050079 : Blo 2049435 2050079 := bstep (se 1 (by rfl) ⟨1537559, by rfl⟩ : syracuseStep 2050079 = 3075119) B3075119
theorem B3075125 : Blo 2049435 3075125 := bbase (se 5 (by rfl) ⟨144146, by rfl⟩ : syracuseStep 3075125 = 288293) (by norm_num)
theorem B2050083 : Blo 2049435 2050083 := bstep (se 1 (by rfl) ⟨1537562, by rfl⟩ : syracuseStep 2050083 = 3075125) B3075125
theorem B5189285 : Blo 2049435 5189285 := bbase (se 4 (by rfl) ⟨486495, by rfl⟩ : syracuseStep 5189285 = 972991) (by norm_num)
theorem B3459523 : Blo 2049435 3459523 := bstep (se 1 (by rfl) ⟨2594642, by rfl⟩ : syracuseStep 3459523 = 5189285) B5189285
theorem B4612697 : Blo 2049435 4612697 := bstep (se 2 (by rfl) ⟨1729761, by rfl⟩ : syracuseStep 4612697 = 3459523) B3459523
theorem B3075131 : Blo 2049435 3075131 := bstep (se 1 (by rfl) ⟨2306348, by rfl⟩ : syracuseStep 3075131 = 4612697) B4612697
theorem B2050087 : Blo 2049435 2050087 := bstep (se 1 (by rfl) ⟨1537565, by rfl⟩ : syracuseStep 2050087 = 3075131) B3075131
theorem B2306353 : Blo 2049435 2306353 := bbase (se 2 (by rfl) ⟨864882, by rfl⟩ : syracuseStep 2306353 = 1729765) (by norm_num)
theorem B3075137 : Blo 2049435 3075137 := bstep (se 2 (by rfl) ⟨1153176, by rfl⟩ : syracuseStep 3075137 = 2306353) B2306353
theorem B2050091 : Blo 2049435 2050091 := bstep (se 1 (by rfl) ⟨1537568, by rfl⟩ : syracuseStep 2050091 = 3075137) B3075137
theorem B4378477 : Blo 2049435 4378477 := bbase (se 3 (by rfl) ⟨820964, by rfl⟩ : syracuseStep 4378477 = 1641929) (by norm_num)
theorem B5837969 : Blo 2049435 5837969 := bstep (se 2 (by rfl) ⟨2189238, by rfl⟩ : syracuseStep 5837969 = 4378477) B4378477
theorem B3891979 : Blo 2049435 3891979 := bstep (se 1 (by rfl) ⟨2918984, by rfl⟩ : syracuseStep 3891979 = 5837969) B5837969
theorem B5189305 : Blo 2049435 5189305 := bstep (se 2 (by rfl) ⟨1945989, by rfl⟩ : syracuseStep 5189305 = 3891979) B3891979
theorem B6919073 : Blo 2049435 6919073 := bstep (se 2 (by rfl) ⟨2594652, by rfl⟩ : syracuseStep 6919073 = 5189305) B5189305
theorem B4612715 : Blo 2049435 4612715 := bstep (se 1 (by rfl) ⟨3459536, by rfl⟩ : syracuseStep 4612715 = 6919073) B6919073
theorem B3075143 : Blo 2049435 3075143 := bstep (se 1 (by rfl) ⟨2306357, by rfl⟩ : syracuseStep 3075143 = 4612715) B4612715
theorem B2050095 : Blo 2049435 2050095 := bstep (se 1 (by rfl) ⟨1537571, by rfl⟩ : syracuseStep 2050095 = 3075143) B3075143
theorem B3075149 : Blo 2049435 3075149 := bbase (se 3 (by rfl) ⟨576590, by rfl⟩ : syracuseStep 3075149 = 1153181) (by norm_num)
theorem B2050099 : Blo 2049435 2050099 := bstep (se 1 (by rfl) ⟨1537574, by rfl⟩ : syracuseStep 2050099 = 3075149) B3075149
theorem B4612733 : Blo 2049435 4612733 := bbase (se 3 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 4612733 = 1729775) (by norm_num)
theorem B3075155 : Blo 2049435 3075155 := bstep (se 1 (by rfl) ⟨2306366, by rfl⟩ : syracuseStep 3075155 = 4612733) B4612733
theorem B2050103 : Blo 2049435 2050103 := bstep (se 1 (by rfl) ⟨1537577, by rfl⟩ : syracuseStep 2050103 = 3075155) B3075155
theorem B3459557 : Blo 2049435 3459557 := bbase (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) (by norm_num)
theorem B2306371 : Blo 2049435 2306371 := bstep (se 1 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 2306371 = 3459557) B3459557
theorem B3075161 : Blo 2049435 3075161 := bstep (se 2 (by rfl) ⟨1153185, by rfl⟩ : syracuseStep 3075161 = 2306371) B2306371
theorem B2050107 : Blo 2049435 2050107 := bstep (se 1 (by rfl) ⟨1537580, by rfl⟩ : syracuseStep 2050107 = 3075161) B3075161
theorem B3117125 : Blo 2049435 3117125 := bbase (se 4 (by rfl) ⟨292230, by rfl⟩ : syracuseStep 3117125 = 584461) (by norm_num)
theorem B2078083 : Blo 2049435 2078083 := bstep (se 1 (by rfl) ⟨1558562, by rfl⟩ : syracuseStep 2078083 = 3117125) B3117125
theorem B2770777 : Blo 2049435 2770777 := bstep (se 2 (by rfl) ⟨1039041, by rfl⟩ : syracuseStep 2770777 = 2078083) B2078083
theorem B14777477 : Blo 2049435 14777477 := bstep (se 4 (by rfl) ⟨1385388, by rfl⟩ : syracuseStep 14777477 = 2770777) B2770777
theorem B9851651 : Blo 2049435 9851651 := bstep (se 1 (by rfl) ⟨7388738, by rfl⟩ : syracuseStep 9851651 = 14777477) B14777477
theorem B6567767 : Blo 2049435 6567767 := bstep (se 1 (by rfl) ⟨4925825, by rfl⟩ : syracuseStep 6567767 = 9851651) B9851651
theorem B4378511 : Blo 2049435 4378511 := bstep (se 1 (by rfl) ⟨3283883, by rfl⟩ : syracuseStep 4378511 = 6567767) B6567767
theorem B2919007 : Blo 2049435 2919007 := bstep (se 1 (by rfl) ⟨2189255, by rfl⟩ : syracuseStep 2919007 = 4378511) B4378511
theorem B15568037 : Blo 2049435 15568037 := bstep (se 4 (by rfl) ⟨1459503, by rfl⟩ : syracuseStep 15568037 = 2919007) B2919007
theorem B10378691 : Blo 2049435 10378691 := bstep (se 1 (by rfl) ⟨7784018, by rfl⟩ : syracuseStep 10378691 = 15568037) B15568037
theorem B6919127 : Blo 2049435 6919127 := bstep (se 1 (by rfl) ⟨5189345, by rfl⟩ : syracuseStep 6919127 = 10378691) B10378691
theorem B4612751 : Blo 2049435 4612751 := bstep (se 1 (by rfl) ⟨3459563, by rfl⟩ : syracuseStep 4612751 = 6919127) B6919127
theorem B3075167 : Blo 2049435 3075167 := bstep (se 1 (by rfl) ⟨2306375, by rfl⟩ : syracuseStep 3075167 = 4612751) B4612751
theorem B2050111 : Blo 2049435 2050111 := bstep (se 1 (by rfl) ⟨1537583, by rfl⟩ : syracuseStep 2050111 = 3075167) B3075167
theorem B3075173 : Blo 2049435 3075173 := bbase (se 4 (by rfl) ⟨288297, by rfl⟩ : syracuseStep 3075173 = 576595) (by norm_num)
theorem B2050115 : Blo 2049435 2050115 := bstep (se 1 (by rfl) ⟨1537586, by rfl⟩ : syracuseStep 2050115 = 3075173) B3075173
theorem B2770789 : Blo 2049435 2770789 := bbase (se 4 (by rfl) ⟨259761, by rfl⟩ : syracuseStep 2770789 = 519523) (by norm_num)
theorem B3694385 : Blo 2049435 3694385 := bstep (se 2 (by rfl) ⟨1385394, by rfl⟩ : syracuseStep 3694385 = 2770789) B2770789
theorem B2462923 : Blo 2049435 2462923 := bstep (se 1 (by rfl) ⟨1847192, by rfl⟩ : syracuseStep 2462923 = 3694385) B3694385
theorem B3283897 : Blo 2049435 3283897 := bstep (se 2 (by rfl) ⟨1231461, by rfl⟩ : syracuseStep 3283897 = 2462923) B2462923
theorem B4378529 : Blo 2049435 4378529 := bstep (se 2 (by rfl) ⟨1641948, by rfl⟩ : syracuseStep 4378529 = 3283897) B3283897
theorem B2919019 : Blo 2049435 2919019 := bstep (se 1 (by rfl) ⟨2189264, by rfl⟩ : syracuseStep 2919019 = 4378529) B4378529
theorem B3892025 : Blo 2049435 3892025 := bstep (se 2 (by rfl) ⟨1459509, by rfl⟩ : syracuseStep 3892025 = 2919019) B2919019
theorem B2594683 : Blo 2049435 2594683 := bstep (se 1 (by rfl) ⟨1946012, by rfl⟩ : syracuseStep 2594683 = 3892025) B3892025
theorem B3459577 : Blo 2049435 3459577 := bstep (se 2 (by rfl) ⟨1297341, by rfl⟩ : syracuseStep 3459577 = 2594683) B2594683
theorem B4612769 : Blo 2049435 4612769 := bstep (se 2 (by rfl) ⟨1729788, by rfl⟩ : syracuseStep 4612769 = 3459577) B3459577
theorem B3075179 : Blo 2049435 3075179 := bstep (se 1 (by rfl) ⟨2306384, by rfl⟩ : syracuseStep 3075179 = 4612769) B4612769
theorem B2050119 : Blo 2049435 2050119 := bstep (se 1 (by rfl) ⟨1537589, by rfl⟩ : syracuseStep 2050119 = 3075179) B3075179
theorem B2306389 : Blo 2049435 2306389 := bbase (se 10 (by rfl) ⟨3378, by rfl⟩ : syracuseStep 2306389 = 6757) (by norm_num)
theorem B3075185 : Blo 2049435 3075185 := bstep (se 2 (by rfl) ⟨1153194, by rfl⟩ : syracuseStep 3075185 = 2306389) B2306389
theorem B2050123 : Blo 2049435 2050123 := bstep (se 1 (by rfl) ⟨1537592, by rfl⟩ : syracuseStep 2050123 = 3075185) B3075185
theorem B2594693 : Blo 2049435 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B6919181 : Blo 2049435 6919181 := bstep (se 3 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 6919181 = 2594693) B2594693
theorem B4612787 : Blo 2049435 4612787 := bstep (se 1 (by rfl) ⟨3459590, by rfl⟩ : syracuseStep 4612787 = 6919181) B6919181
theorem B3075191 : Blo 2049435 3075191 := bstep (se 1 (by rfl) ⟨2306393, by rfl⟩ : syracuseStep 3075191 = 4612787) B4612787
theorem B2050127 : Blo 2049435 2050127 := bstep (se 1 (by rfl) ⟨1537595, by rfl⟩ : syracuseStep 2050127 = 3075191) B3075191
theorem B3075197 : Blo 2049435 3075197 := bbase (se 3 (by rfl) ⟨576599, by rfl⟩ : syracuseStep 3075197 = 1153199) (by norm_num)
theorem B2050131 : Blo 2049435 2050131 := bstep (se 1 (by rfl) ⟨1537598, by rfl⟩ : syracuseStep 2050131 = 3075197) B3075197
theorem B4612805 : Blo 2049435 4612805 := bbase (se 4 (by rfl) ⟨432450, by rfl⟩ : syracuseStep 4612805 = 864901) (by norm_num)
theorem B3075203 : Blo 2049435 3075203 := bstep (se 1 (by rfl) ⟨2306402, by rfl⟩ : syracuseStep 3075203 = 4612805) B4612805
theorem B2050135 : Blo 2049435 2050135 := bstep (se 1 (by rfl) ⟨1537601, by rfl⟩ : syracuseStep 2050135 = 3075203) B3075203
theorem B19703573 : Blo 2049435 19703573 := bbase (se 6 (by rfl) ⟨461802, by rfl⟩ : syracuseStep 19703573 = 923605) (by norm_num)
theorem B13135715 : Blo 2049435 13135715 := bstep (se 1 (by rfl) ⟨9851786, by rfl⟩ : syracuseStep 13135715 = 19703573) B19703573
theorem B8757143 : Blo 2049435 8757143 := bstep (se 1 (by rfl) ⟨6567857, by rfl⟩ : syracuseStep 8757143 = 13135715) B13135715
theorem B5838095 : Blo 2049435 5838095 := bstep (se 1 (by rfl) ⟨4378571, by rfl⟩ : syracuseStep 5838095 = 8757143) B8757143
theorem B3892063 : Blo 2049435 3892063 := bstep (se 1 (by rfl) ⟨2919047, by rfl⟩ : syracuseStep 3892063 = 5838095) B5838095
theorem B5189417 : Blo 2049435 5189417 := bstep (se 2 (by rfl) ⟨1946031, by rfl⟩ : syracuseStep 5189417 = 3892063) B3892063
theorem B3459611 : Blo 2049435 3459611 := bstep (se 1 (by rfl) ⟨2594708, by rfl⟩ : syracuseStep 3459611 = 5189417) B5189417
theorem B2306407 : Blo 2049435 2306407 := bstep (se 1 (by rfl) ⟨1729805, by rfl⟩ : syracuseStep 2306407 = 3459611) B3459611
theorem B3075209 : Blo 2049435 3075209 := bstep (se 2 (by rfl) ⟨1153203, by rfl⟩ : syracuseStep 3075209 = 2306407) B2306407
theorem B2050139 : Blo 2049435 2050139 := bstep (se 1 (by rfl) ⟨1537604, by rfl⟩ : syracuseStep 2050139 = 3075209) B3075209
theorem B10378853 : Blo 2049435 10378853 := bbase (se 4 (by rfl) ⟨973017, by rfl⟩ : syracuseStep 10378853 = 1946035) (by norm_num)
theorem B6919235 : Blo 2049435 6919235 := bstep (se 1 (by rfl) ⟨5189426, by rfl⟩ : syracuseStep 6919235 = 10378853) B10378853
theorem B4612823 : Blo 2049435 4612823 := bstep (se 1 (by rfl) ⟨3459617, by rfl⟩ : syracuseStep 4612823 = 6919235) B6919235
theorem B3075215 : Blo 2049435 3075215 := bstep (se 1 (by rfl) ⟨2306411, by rfl⟩ : syracuseStep 3075215 = 4612823) B4612823
theorem B2050143 : Blo 2049435 2050143 := bstep (se 1 (by rfl) ⟨1537607, by rfl⟩ : syracuseStep 2050143 = 3075215) B3075215
theorem B3075221 : Blo 2049435 3075221 := bbase (se 6 (by rfl) ⟨72075, by rfl⟩ : syracuseStep 3075221 = 144151) (by norm_num)
theorem B2050147 : Blo 2049435 2050147 := bstep (se 1 (by rfl) ⟨1537610, by rfl⟩ : syracuseStep 2050147 = 3075221) B3075221
theorem B9351557 : Blo 2049435 9351557 := bbase (se 4 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 9351557 = 1753417) (by norm_num)
theorem B6234371 : Blo 2049435 6234371 := bstep (se 1 (by rfl) ⟨4675778, by rfl⟩ : syracuseStep 6234371 = 9351557) B9351557
theorem B4156247 : Blo 2049435 4156247 := bstep (se 1 (by rfl) ⟨3117185, by rfl⟩ : syracuseStep 4156247 = 6234371) B6234371
theorem B2770831 : Blo 2049435 2770831 := bstep (se 1 (by rfl) ⟨2078123, by rfl⟩ : syracuseStep 2770831 = 4156247) B4156247
theorem B14777765 : Blo 2049435 14777765 := bstep (se 4 (by rfl) ⟨1385415, by rfl⟩ : syracuseStep 14777765 = 2770831) B2770831
theorem B9851843 : Blo 2049435 9851843 := bstep (se 1 (by rfl) ⟨7388882, by rfl⟩ : syracuseStep 9851843 = 14777765) B14777765
theorem B6567895 : Blo 2049435 6567895 := bstep (se 1 (by rfl) ⟨4925921, by rfl⟩ : syracuseStep 6567895 = 9851843) B9851843
theorem B8757193 : Blo 2049435 8757193 := bstep (se 2 (by rfl) ⟨3283947, by rfl⟩ : syracuseStep 8757193 = 6567895) B6567895
theorem B11676257 : Blo 2049435 11676257 := bstep (se 2 (by rfl) ⟨4378596, by rfl⟩ : syracuseStep 11676257 = 8757193) B8757193
theorem B7784171 : Blo 2049435 7784171 := bstep (se 1 (by rfl) ⟨5838128, by rfl⟩ : syracuseStep 7784171 = 11676257) B11676257
theorem B5189447 : Blo 2049435 5189447 := bstep (se 1 (by rfl) ⟨3892085, by rfl⟩ : syracuseStep 5189447 = 7784171) B7784171
theorem B3459631 : Blo 2049435 3459631 := bstep (se 1 (by rfl) ⟨2594723, by rfl⟩ : syracuseStep 3459631 = 5189447) B5189447
theorem B4612841 : Blo 2049435 4612841 := bstep (se 2 (by rfl) ⟨1729815, by rfl⟩ : syracuseStep 4612841 = 3459631) B3459631
theorem B3075227 : Blo 2049435 3075227 := bstep (se 1 (by rfl) ⟨2306420, by rfl⟩ : syracuseStep 3075227 = 4612841) B4612841
theorem B2050151 : Blo 2049435 2050151 := bstep (se 1 (by rfl) ⟨1537613, by rfl⟩ : syracuseStep 2050151 = 3075227) B3075227
theorem B2306425 : Blo 2049435 2306425 := bbase (se 2 (by rfl) ⟨864909, by rfl⟩ : syracuseStep 2306425 = 1729819) (by norm_num)
theorem B3075233 : Blo 2049435 3075233 := bstep (se 2 (by rfl) ⟨1153212, by rfl⟩ : syracuseStep 3075233 = 2306425) B2306425
theorem B2050155 : Blo 2049435 2050155 := bstep (se 1 (by rfl) ⟨1537616, by rfl⟩ : syracuseStep 2050155 = 3075233) B3075233
theorem B3328765 : Blo 2049435 3328765 := bbase (se 3 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 3328765 = 1248287) (by norm_num)
theorem B17753413 : Blo 2049435 17753413 := bstep (se 4 (by rfl) ⟨1664382, by rfl⟩ : syracuseStep 17753413 = 3328765) B3328765
theorem B23671217 : Blo 2049435 23671217 := bstep (se 2 (by rfl) ⟨8876706, by rfl⟩ : syracuseStep 23671217 = 17753413) B17753413
theorem B63123245 : Blo 2049435 63123245 := bstep (se 3 (by rfl) ⟨11835608, by rfl⟩ : syracuseStep 63123245 = 23671217) B23671217
theorem B42082163 : Blo 2049435 42082163 := bstep (se 1 (by rfl) ⟨31561622, by rfl⟩ : syracuseStep 42082163 = 63123245) B63123245
theorem B28054775 : Blo 2049435 28054775 := bstep (se 1 (by rfl) ⟨21041081, by rfl⟩ : syracuseStep 28054775 = 42082163) B42082163
theorem B18703183 : Blo 2049435 18703183 := bstep (se 1 (by rfl) ⟨14027387, by rfl⟩ : syracuseStep 18703183 = 28054775) B28054775
theorem B24937577 : Blo 2049435 24937577 := bstep (se 2 (by rfl) ⟨9351591, by rfl⟩ : syracuseStep 24937577 = 18703183) B18703183
theorem B16625051 : Blo 2049435 16625051 := bstep (se 1 (by rfl) ⟨12468788, by rfl⟩ : syracuseStep 16625051 = 24937577) B24937577
theorem B11083367 : Blo 2049435 11083367 := bstep (se 1 (by rfl) ⟨8312525, by rfl⟩ : syracuseStep 11083367 = 16625051) B16625051
theorem B7388911 : Blo 2049435 7388911 := bstep (se 1 (by rfl) ⟨5541683, by rfl⟩ : syracuseStep 7388911 = 11083367) B11083367
theorem B9851881 : Blo 2049435 9851881 := bstep (se 2 (by rfl) ⟨3694455, by rfl⟩ : syracuseStep 9851881 = 7388911) B7388911
theorem B13135841 : Blo 2049435 13135841 := bstep (se 2 (by rfl) ⟨4925940, by rfl⟩ : syracuseStep 13135841 = 9851881) B9851881
theorem B8757227 : Blo 2049435 8757227 := bstep (se 1 (by rfl) ⟨6567920, by rfl⟩ : syracuseStep 8757227 = 13135841) B13135841
theorem B5838151 : Blo 2049435 5838151 := bstep (se 1 (by rfl) ⟨4378613, by rfl⟩ : syracuseStep 5838151 = 8757227) B8757227
theorem B7784201 : Blo 2049435 7784201 := bstep (se 2 (by rfl) ⟨2919075, by rfl⟩ : syracuseStep 7784201 = 5838151) B5838151
theorem B5189467 : Blo 2049435 5189467 := bstep (se 1 (by rfl) ⟨3892100, by rfl⟩ : syracuseStep 5189467 = 7784201) B7784201
theorem B6919289 : Blo 2049435 6919289 := bstep (se 2 (by rfl) ⟨2594733, by rfl⟩ : syracuseStep 6919289 = 5189467) B5189467
theorem B4612859 : Blo 2049435 4612859 := bstep (se 1 (by rfl) ⟨3459644, by rfl⟩ : syracuseStep 4612859 = 6919289) B6919289
theorem B3075239 : Blo 2049435 3075239 := bstep (se 1 (by rfl) ⟨2306429, by rfl⟩ : syracuseStep 3075239 = 4612859) B4612859
theorem B2050159 : Blo 2049435 2050159 := bstep (se 1 (by rfl) ⟨1537619, by rfl⟩ : syracuseStep 2050159 = 3075239) B3075239
theorem B3075245 : Blo 2049435 3075245 := bbase (se 3 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 3075245 = 1153217) (by norm_num)
theorem B2050163 : Blo 2049435 2050163 := bstep (se 1 (by rfl) ⟨1537622, by rfl⟩ : syracuseStep 2050163 = 3075245) B3075245
theorem B4612877 : Blo 2049435 4612877 := bbase (se 3 (by rfl) ⟨864914, by rfl⟩ : syracuseStep 4612877 = 1729829) (by norm_num)
theorem B3075251 : Blo 2049435 3075251 := bstep (se 1 (by rfl) ⟨2306438, by rfl⟩ : syracuseStep 3075251 = 4612877) B4612877
theorem B2050167 : Blo 2049435 2050167 := bstep (se 1 (by rfl) ⟨1537625, by rfl⟩ : syracuseStep 2050167 = 3075251) B3075251
theorem B2594749 : Blo 2049435 2594749 := bbase (se 3 (by rfl) ⟨486515, by rfl⟩ : syracuseStep 2594749 = 973031) (by norm_num)
theorem B3459665 : Blo 2049435 3459665 := bstep (se 2 (by rfl) ⟨1297374, by rfl⟩ : syracuseStep 3459665 = 2594749) B2594749
theorem B2306443 : Blo 2049435 2306443 := bstep (se 1 (by rfl) ⟨1729832, by rfl⟩ : syracuseStep 2306443 = 3459665) B3459665
theorem B3075257 : Blo 2049435 3075257 := bstep (se 2 (by rfl) ⟨1153221, by rfl⟩ : syracuseStep 3075257 = 2306443) B2306443
theorem B2050171 : Blo 2049435 2050171 := bstep (se 1 (by rfl) ⟨1537628, by rfl⟩ : syracuseStep 2050171 = 3075257) B3075257
theorem B9851957 : Blo 2049435 9851957 := bbase (se 5 (by rfl) ⟨461810, by rfl⟩ : syracuseStep 9851957 = 923621) (by norm_num)
theorem B6567971 : Blo 2049435 6567971 := bstep (se 1 (by rfl) ⟨4925978, by rfl⟩ : syracuseStep 6567971 = 9851957) B9851957
theorem B17514589 : Blo 2049435 17514589 := bstep (se 3 (by rfl) ⟨3283985, by rfl⟩ : syracuseStep 17514589 = 6567971) B6567971
theorem B23352785 : Blo 2049435 23352785 := bstep (se 2 (by rfl) ⟨8757294, by rfl⟩ : syracuseStep 23352785 = 17514589) B17514589
theorem B15568523 : Blo 2049435 15568523 := bstep (se 1 (by rfl) ⟨11676392, by rfl⟩ : syracuseStep 15568523 = 23352785) B23352785
theorem B10379015 : Blo 2049435 10379015 := bstep (se 1 (by rfl) ⟨7784261, by rfl⟩ : syracuseStep 10379015 = 15568523) B15568523
theorem B6919343 : Blo 2049435 6919343 := bstep (se 1 (by rfl) ⟨5189507, by rfl⟩ : syracuseStep 6919343 = 10379015) B10379015
theorem B4612895 : Blo 2049435 4612895 := bstep (se 1 (by rfl) ⟨3459671, by rfl⟩ : syracuseStep 4612895 = 6919343) B6919343
theorem B3075263 : Blo 2049435 3075263 := bstep (se 1 (by rfl) ⟨2306447, by rfl⟩ : syracuseStep 3075263 = 4612895) B4612895
theorem B2050175 : Blo 2049435 2050175 := bstep (se 1 (by rfl) ⟨1537631, by rfl⟩ : syracuseStep 2050175 = 3075263) B3075263
theorem B3075269 : Blo 2049435 3075269 := bbase (se 4 (by rfl) ⟨288306, by rfl⟩ : syracuseStep 3075269 = 576613) (by norm_num)
theorem B2050179 : Blo 2049435 2050179 := bstep (se 1 (by rfl) ⟨1537634, by rfl⟩ : syracuseStep 2050179 = 3075269) B3075269
theorem B3459685 : Blo 2049435 3459685 := bbase (se 4 (by rfl) ⟨324345, by rfl⟩ : syracuseStep 3459685 = 648691) (by norm_num)
theorem B4612913 : Blo 2049435 4612913 := bstep (se 2 (by rfl) ⟨1729842, by rfl⟩ : syracuseStep 4612913 = 3459685) B3459685
theorem B3075275 : Blo 2049435 3075275 := bstep (se 1 (by rfl) ⟨2306456, by rfl⟩ : syracuseStep 3075275 = 4612913) B4612913
theorem B2050183 : Blo 2049435 2050183 := bstep (se 1 (by rfl) ⟨1537637, by rfl⟩ : syracuseStep 2050183 = 3075275) B3075275
theorem B2306461 : Blo 2049435 2306461 := bbase (se 3 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 2306461 = 864923) (by norm_num)
theorem B3075281 : Blo 2049435 3075281 := bstep (se 2 (by rfl) ⟨1153230, by rfl⟩ : syracuseStep 3075281 = 2306461) B2306461
theorem B2050187 : Blo 2049435 2050187 := bstep (se 1 (by rfl) ⟨1537640, by rfl⟩ : syracuseStep 2050187 = 3075281) B3075281
theorem B6919397 : Blo 2049435 6919397 := bbase (se 4 (by rfl) ⟨648693, by rfl⟩ : syracuseStep 6919397 = 1297387) (by norm_num)
theorem B4612931 : Blo 2049435 4612931 := bstep (se 1 (by rfl) ⟨3459698, by rfl⟩ : syracuseStep 4612931 = 6919397) B6919397
theorem B3075287 : Blo 2049435 3075287 := bstep (se 1 (by rfl) ⟨2306465, by rfl⟩ : syracuseStep 3075287 = 4612931) B4612931
theorem B2050191 : Blo 2049435 2050191 := bstep (se 1 (by rfl) ⟨1537643, by rfl⟩ : syracuseStep 2050191 = 3075287) B3075287
theorem B3075293 : Blo 2049435 3075293 := bbase (se 3 (by rfl) ⟨576617, by rfl⟩ : syracuseStep 3075293 = 1153235) (by norm_num)
theorem B2050195 : Blo 2049435 2050195 := bstep (se 1 (by rfl) ⟨1537646, by rfl⟩ : syracuseStep 2050195 = 3075293) B3075293
theorem B4612949 : Blo 2049435 4612949 := bbase (se 9 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 4612949 = 27029) (by norm_num)
theorem B3075299 : Blo 2049435 3075299 := bstep (se 1 (by rfl) ⟨2306474, by rfl⟩ : syracuseStep 3075299 = 4612949) B4612949
theorem B2050199 : Blo 2049435 2050199 := bstep (se 1 (by rfl) ⟨1537649, by rfl⟩ : syracuseStep 2050199 = 3075299) B3075299
theorem B5838277 : Blo 2049435 5838277 := bbase (se 4 (by rfl) ⟨547338, by rfl⟩ : syracuseStep 5838277 = 1094677) (by norm_num)
theorem B7784369 : Blo 2049435 7784369 := bstep (se 2 (by rfl) ⟨2919138, by rfl⟩ : syracuseStep 7784369 = 5838277) B5838277
theorem B5189579 : Blo 2049435 5189579 := bstep (se 1 (by rfl) ⟨3892184, by rfl⟩ : syracuseStep 5189579 = 7784369) B7784369
theorem B3459719 : Blo 2049435 3459719 := bstep (se 1 (by rfl) ⟨2594789, by rfl⟩ : syracuseStep 3459719 = 5189579) B5189579
theorem B2306479 : Blo 2049435 2306479 := bstep (se 1 (by rfl) ⟨1729859, by rfl⟩ : syracuseStep 2306479 = 3459719) B3459719
theorem B3075305 : Blo 2049435 3075305 := bstep (se 2 (by rfl) ⟨1153239, by rfl⟩ : syracuseStep 3075305 = 2306479) B2306479
theorem B2050203 : Blo 2049435 2050203 := bstep (se 1 (by rfl) ⟨1537652, by rfl⟩ : syracuseStep 2050203 = 3075305) B3075305
theorem B3744949 : Blo 2049435 3744949 := bbase (se 5 (by rfl) ⟨175544, by rfl⟩ : syracuseStep 3744949 = 351089) (by norm_num)
theorem B4993265 : Blo 2049435 4993265 := bstep (se 2 (by rfl) ⟨1872474, by rfl⟩ : syracuseStep 4993265 = 3744949) B3744949
theorem B13315373 : Blo 2049435 13315373 := bstep (se 3 (by rfl) ⟨2496632, by rfl⟩ : syracuseStep 13315373 = 4993265) B4993265
theorem B8876915 : Blo 2049435 8876915 := bstep (se 1 (by rfl) ⟨6657686, by rfl⟩ : syracuseStep 8876915 = 13315373) B13315373
theorem B5917943 : Blo 2049435 5917943 := bstep (se 1 (by rfl) ⟨4438457, by rfl⟩ : syracuseStep 5917943 = 8876915) B8876915
theorem B3945295 : Blo 2049435 3945295 := bstep (se 1 (by rfl) ⟨2958971, by rfl⟩ : syracuseStep 3945295 = 5917943) B5917943
theorem B5260393 : Blo 2049435 5260393 := bstep (se 2 (by rfl) ⟨1972647, by rfl⟩ : syracuseStep 5260393 = 3945295) B3945295
theorem B7013857 : Blo 2049435 7013857 := bstep (se 2 (by rfl) ⟨2630196, by rfl⟩ : syracuseStep 7013857 = 5260393) B5260393
theorem B9351809 : Blo 2049435 9351809 := bstep (se 2 (by rfl) ⟨3506928, by rfl⟩ : syracuseStep 9351809 = 7013857) B7013857
theorem B6234539 : Blo 2049435 6234539 := bstep (se 1 (by rfl) ⟨4675904, by rfl⟩ : syracuseStep 6234539 = 9351809) B9351809
theorem B66501749 : Blo 2049435 66501749 := bstep (se 5 (by rfl) ⟨3117269, by rfl⟩ : syracuseStep 66501749 = 6234539) B6234539
theorem B44334499 : Blo 2049435 44334499 := bstep (se 1 (by rfl) ⟨33250874, by rfl⟩ : syracuseStep 44334499 = 66501749) B66501749
theorem B59112665 : Blo 2049435 59112665 := bstep (se 2 (by rfl) ⟨22167249, by rfl⟩ : syracuseStep 59112665 = 44334499) B44334499
theorem B39408443 : Blo 2049435 39408443 := bstep (se 1 (by rfl) ⟨29556332, by rfl⟩ : syracuseStep 39408443 = 59112665) B59112665
theorem B26272295 : Blo 2049435 26272295 := bstep (se 1 (by rfl) ⟨19704221, by rfl⟩ : syracuseStep 26272295 = 39408443) B39408443
theorem B17514863 : Blo 2049435 17514863 := bstep (se 1 (by rfl) ⟨13136147, by rfl⟩ : syracuseStep 17514863 = 26272295) B26272295
theorem B11676575 : Blo 2049435 11676575 := bstep (se 1 (by rfl) ⟨8757431, by rfl⟩ : syracuseStep 11676575 = 17514863) B17514863
theorem B7784383 : Blo 2049435 7784383 := bstep (se 1 (by rfl) ⟨5838287, by rfl⟩ : syracuseStep 7784383 = 11676575) B11676575
theorem B10379177 : Blo 2049435 10379177 := bstep (se 2 (by rfl) ⟨3892191, by rfl⟩ : syracuseStep 10379177 = 7784383) B7784383
theorem B6919451 : Blo 2049435 6919451 := bstep (se 1 (by rfl) ⟨5189588, by rfl⟩ : syracuseStep 6919451 = 10379177) B10379177
theorem B4612967 : Blo 2049435 4612967 := bstep (se 1 (by rfl) ⟨3459725, by rfl⟩ : syracuseStep 4612967 = 6919451) B6919451
theorem B3075311 : Blo 2049435 3075311 := bstep (se 1 (by rfl) ⟨2306483, by rfl⟩ : syracuseStep 3075311 = 4612967) B4612967
theorem B2050207 : Blo 2049435 2050207 := bstep (se 1 (by rfl) ⟨1537655, by rfl⟩ : syracuseStep 2050207 = 3075311) B3075311
theorem B3075317 : Blo 2049435 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2050211 : Blo 2049435 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B6234565 : Blo 2049435 6234565 := bbase (se 4 (by rfl) ⟨584490, by rfl⟩ : syracuseStep 6234565 = 1168981) (by norm_num)
theorem B8312753 : Blo 2049435 8312753 := bstep (se 2 (by rfl) ⟨3117282, by rfl⟩ : syracuseStep 8312753 = 6234565) B6234565
theorem B22167341 : Blo 2049435 22167341 := bstep (se 3 (by rfl) ⟨4156376, by rfl⟩ : syracuseStep 22167341 = 8312753) B8312753
theorem B14778227 : Blo 2049435 14778227 := bstep (se 1 (by rfl) ⟨11083670, by rfl⟩ : syracuseStep 14778227 = 22167341) B22167341
theorem B9852151 : Blo 2049435 9852151 := bstep (se 1 (by rfl) ⟨7389113, by rfl⟩ : syracuseStep 9852151 = 14778227) B14778227
theorem B13136201 : Blo 2049435 13136201 := bstep (se 2 (by rfl) ⟨4926075, by rfl⟩ : syracuseStep 13136201 = 9852151) B9852151
theorem B8757467 : Blo 2049435 8757467 := bstep (se 1 (by rfl) ⟨6568100, by rfl⟩ : syracuseStep 8757467 = 13136201) B13136201
theorem B5838311 : Blo 2049435 5838311 := bstep (se 1 (by rfl) ⟨4378733, by rfl⟩ : syracuseStep 5838311 = 8757467) B8757467
theorem B3892207 : Blo 2049435 3892207 := bstep (se 1 (by rfl) ⟨2919155, by rfl⟩ : syracuseStep 3892207 = 5838311) B5838311
theorem B5189609 : Blo 2049435 5189609 := bstep (se 2 (by rfl) ⟨1946103, by rfl⟩ : syracuseStep 5189609 = 3892207) B3892207
theorem B3459739 : Blo 2049435 3459739 := bstep (se 1 (by rfl) ⟨2594804, by rfl⟩ : syracuseStep 3459739 = 5189609) B5189609
theorem B4612985 : Blo 2049435 4612985 := bstep (se 2 (by rfl) ⟨1729869, by rfl⟩ : syracuseStep 4612985 = 3459739) B3459739
theorem B3075323 : Blo 2049435 3075323 := bstep (se 1 (by rfl) ⟨2306492, by rfl⟩ : syracuseStep 3075323 = 4612985) B4612985
theorem B2050215 : Blo 2049435 2050215 := bstep (se 1 (by rfl) ⟨1537661, by rfl⟩ : syracuseStep 2050215 = 3075323) B3075323
theorem B2306497 : Blo 2049435 2306497 := bbase (se 2 (by rfl) ⟨864936, by rfl⟩ : syracuseStep 2306497 = 1729873) (by norm_num)
theorem B3075329 : Blo 2049435 3075329 := bstep (se 2 (by rfl) ⟨1153248, by rfl⟩ : syracuseStep 3075329 = 2306497) B2306497
theorem B2050219 : Blo 2049435 2050219 := bstep (se 1 (by rfl) ⟨1537664, by rfl⟩ : syracuseStep 2050219 = 3075329) B3075329
theorem B5189629 : Blo 2049435 5189629 := bbase (se 3 (by rfl) ⟨973055, by rfl⟩ : syracuseStep 5189629 = 1946111) (by norm_num)
theorem B6919505 : Blo 2049435 6919505 := bstep (se 2 (by rfl) ⟨2594814, by rfl⟩ : syracuseStep 6919505 = 5189629) B5189629
theorem B4613003 : Blo 2049435 4613003 := bstep (se 1 (by rfl) ⟨3459752, by rfl⟩ : syracuseStep 4613003 = 6919505) B6919505
theorem B3075335 : Blo 2049435 3075335 := bstep (se 1 (by rfl) ⟨2306501, by rfl⟩ : syracuseStep 3075335 = 4613003) B4613003
theorem B2050223 : Blo 2049435 2050223 := bstep (se 1 (by rfl) ⟨1537667, by rfl⟩ : syracuseStep 2050223 = 3075335) B3075335
theorem B3075341 : Blo 2049435 3075341 := bbase (se 3 (by rfl) ⟨576626, by rfl⟩ : syracuseStep 3075341 = 1153253) (by norm_num)
theorem B2050227 : Blo 2049435 2050227 := bstep (se 1 (by rfl) ⟨1537670, by rfl⟩ : syracuseStep 2050227 = 3075341) B3075341
theorem B4613021 : Blo 2049435 4613021 := bbase (se 3 (by rfl) ⟨864941, by rfl⟩ : syracuseStep 4613021 = 1729883) (by norm_num)
theorem B3075347 : Blo 2049435 3075347 := bstep (se 1 (by rfl) ⟨2306510, by rfl⟩ : syracuseStep 3075347 = 4613021) B4613021
theorem B2050231 : Blo 2049435 2050231 := bstep (se 1 (by rfl) ⟨1537673, by rfl⟩ : syracuseStep 2050231 = 3075347) B3075347
theorem B3459773 : Blo 2049435 3459773 := bbase (se 3 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 3459773 = 1297415) (by norm_num)
theorem B2306515 : Blo 2049435 2306515 := bstep (se 1 (by rfl) ⟨1729886, by rfl⟩ : syracuseStep 2306515 = 3459773) B3459773
theorem B3075353 : Blo 2049435 3075353 := bstep (se 2 (by rfl) ⟨1153257, by rfl⟩ : syracuseStep 3075353 = 2306515) B2306515
theorem B2050235 : Blo 2049435 2050235 := bstep (se 1 (by rfl) ⟨1537676, by rfl⟩ : syracuseStep 2050235 = 3075353) B3075353
theorem B11676757 : Blo 2049435 11676757 := bbase (se 8 (by rfl) ⟨68418, by rfl⟩ : syracuseStep 11676757 = 136837) (by norm_num)
theorem B15569009 : Blo 2049435 15569009 := bstep (se 2 (by rfl) ⟨5838378, by rfl⟩ : syracuseStep 15569009 = 11676757) B11676757
theorem B10379339 : Blo 2049435 10379339 := bstep (se 1 (by rfl) ⟨7784504, by rfl⟩ : syracuseStep 10379339 = 15569009) B15569009
theorem B6919559 : Blo 2049435 6919559 := bstep (se 1 (by rfl) ⟨5189669, by rfl⟩ : syracuseStep 6919559 = 10379339) B10379339
theorem B4613039 : Blo 2049435 4613039 := bstep (se 1 (by rfl) ⟨3459779, by rfl⟩ : syracuseStep 4613039 = 6919559) B6919559
theorem B3075359 : Blo 2049435 3075359 := bstep (se 1 (by rfl) ⟨2306519, by rfl⟩ : syracuseStep 3075359 = 4613039) B4613039
theorem B2050239 : Blo 2049435 2050239 := bstep (se 1 (by rfl) ⟨1537679, by rfl⟩ : syracuseStep 2050239 = 3075359) B3075359
theorem B3075365 : Blo 2049435 3075365 := bbase (se 4 (by rfl) ⟨288315, by rfl⟩ : syracuseStep 3075365 = 576631) (by norm_num)
theorem B2050243 : Blo 2049435 2050243 := bstep (se 1 (by rfl) ⟨1537682, by rfl⟩ : syracuseStep 2050243 = 3075365) B3075365
theorem B2594845 : Blo 2049435 2594845 := bbase (se 3 (by rfl) ⟨486533, by rfl⟩ : syracuseStep 2594845 = 973067) (by norm_num)
theorem B3459793 : Blo 2049435 3459793 := bstep (se 2 (by rfl) ⟨1297422, by rfl⟩ : syracuseStep 3459793 = 2594845) B2594845
theorem B4613057 : Blo 2049435 4613057 := bstep (se 2 (by rfl) ⟨1729896, by rfl⟩ : syracuseStep 4613057 = 3459793) B3459793
theorem B3075371 : Blo 2049435 3075371 := bstep (se 1 (by rfl) ⟨2306528, by rfl⟩ : syracuseStep 3075371 = 4613057) B4613057
theorem B2050247 : Blo 2049435 2050247 := bstep (se 1 (by rfl) ⟨1537685, by rfl⟩ : syracuseStep 2050247 = 3075371) B3075371
theorem B2306533 : Blo 2049435 2306533 := bbase (se 4 (by rfl) ⟨216237, by rfl⟩ : syracuseStep 2306533 = 432475) (by norm_num)
theorem B3075377 : Blo 2049435 3075377 := bstep (se 2 (by rfl) ⟨1153266, by rfl⟩ : syracuseStep 3075377 = 2306533) B2306533
theorem B2050251 : Blo 2049435 2050251 := bstep (se 1 (by rfl) ⟨1537688, by rfl⟩ : syracuseStep 2050251 = 3075377) B3075377
theorem B6568229 : Blo 2049435 6568229 := bbase (se 4 (by rfl) ⟨615771, by rfl⟩ : syracuseStep 6568229 = 1231543) (by norm_num)
theorem B4378819 : Blo 2049435 4378819 := bstep (se 1 (by rfl) ⟨3284114, by rfl⟩ : syracuseStep 4378819 = 6568229) B6568229
theorem B5838425 : Blo 2049435 5838425 := bstep (se 2 (by rfl) ⟨2189409, by rfl⟩ : syracuseStep 5838425 = 4378819) B4378819
theorem B3892283 : Blo 2049435 3892283 := bstep (se 1 (by rfl) ⟨2919212, by rfl⟩ : syracuseStep 3892283 = 5838425) B5838425
theorem B2594855 : Blo 2049435 2594855 := bstep (se 1 (by rfl) ⟨1946141, by rfl⟩ : syracuseStep 2594855 = 3892283) B3892283
theorem B6919613 : Blo 2049435 6919613 := bstep (se 3 (by rfl) ⟨1297427, by rfl⟩ : syracuseStep 6919613 = 2594855) B2594855
theorem B4613075 : Blo 2049435 4613075 := bstep (se 1 (by rfl) ⟨3459806, by rfl⟩ : syracuseStep 4613075 = 6919613) B6919613
theorem B3075383 : Blo 2049435 3075383 := bstep (se 1 (by rfl) ⟨2306537, by rfl⟩ : syracuseStep 3075383 = 4613075) B4613075
theorem B2050255 : Blo 2049435 2050255 := bstep (se 1 (by rfl) ⟨1537691, by rfl⟩ : syracuseStep 2050255 = 3075383) B3075383
theorem B3075389 : Blo 2049435 3075389 := bbase (se 3 (by rfl) ⟨576635, by rfl⟩ : syracuseStep 3075389 = 1153271) (by norm_num)
theorem B2050259 : Blo 2049435 2050259 := bstep (se 1 (by rfl) ⟨1537694, by rfl⟩ : syracuseStep 2050259 = 3075389) B3075389
theorem B4613093 : Blo 2049435 4613093 := bbase (se 4 (by rfl) ⟨432477, by rfl⟩ : syracuseStep 4613093 = 864955) (by norm_num)
theorem B3075395 : Blo 2049435 3075395 := bstep (se 1 (by rfl) ⟨2306546, by rfl⟩ : syracuseStep 3075395 = 4613093) B4613093
theorem B2050263 : Blo 2049435 2050263 := bstep (se 1 (by rfl) ⟨1537697, by rfl⟩ : syracuseStep 2050263 = 3075395) B3075395
theorem B5189741 : Blo 2049435 5189741 := bbase (se 3 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 5189741 = 1946153) (by norm_num)
theorem B3459827 : Blo 2049435 3459827 := bstep (se 1 (by rfl) ⟨2594870, by rfl⟩ : syracuseStep 3459827 = 5189741) B5189741
theorem B2306551 : Blo 2049435 2306551 := bstep (se 1 (by rfl) ⟨1729913, by rfl⟩ : syracuseStep 2306551 = 3459827) B3459827
theorem B3075401 : Blo 2049435 3075401 := bstep (se 2 (by rfl) ⟨1153275, by rfl⟩ : syracuseStep 3075401 = 2306551) B2306551
theorem B2050267 : Blo 2049435 2050267 := bstep (se 1 (by rfl) ⟨1537700, by rfl⟩ : syracuseStep 2050267 = 3075401) B3075401
theorem B4378853 : Blo 2049435 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B2919235 : Blo 2049435 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B3892313 : Blo 2049435 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B10379501 : Blo 2049435 10379501 := bstep (se 3 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 10379501 = 3892313) B3892313
theorem B6919667 : Blo 2049435 6919667 := bstep (se 1 (by rfl) ⟨5189750, by rfl⟩ : syracuseStep 6919667 = 10379501) B10379501
theorem B4613111 : Blo 2049435 4613111 := bstep (se 1 (by rfl) ⟨3459833, by rfl⟩ : syracuseStep 4613111 = 6919667) B6919667
theorem B3075407 : Blo 2049435 3075407 := bstep (se 1 (by rfl) ⟨2306555, by rfl⟩ : syracuseStep 3075407 = 4613111) B4613111
theorem B2050271 : Blo 2049435 2050271 := bstep (se 1 (by rfl) ⟨1537703, by rfl⟩ : syracuseStep 2050271 = 3075407) B3075407
theorem B3075413 : Blo 2049435 3075413 := bbase (se 11 (by rfl) ⟨2252, by rfl⟩ : syracuseStep 3075413 = 4505) (by norm_num)
theorem B2050275 : Blo 2049435 2050275 := bstep (se 1 (by rfl) ⟨1537706, by rfl⟩ : syracuseStep 2050275 = 3075413) B3075413
theorem B2771005 : Blo 2049435 2771005 := bbase (se 3 (by rfl) ⟨519563, by rfl⟩ : syracuseStep 2771005 = 1039127) (by norm_num)
theorem B3694673 : Blo 2049435 3694673 := bstep (se 2 (by rfl) ⟨1385502, by rfl⟩ : syracuseStep 3694673 = 2771005) B2771005
theorem B2463115 : Blo 2049435 2463115 := bstep (se 1 (by rfl) ⟨1847336, by rfl⟩ : syracuseStep 2463115 = 3694673) B3694673
theorem B3284153 : Blo 2049435 3284153 := bstep (se 2 (by rfl) ⟨1231557, by rfl⟩ : syracuseStep 3284153 = 2463115) B2463115
theorem B2189435 : Blo 2049435 2189435 := bstep (se 1 (by rfl) ⟨1642076, by rfl⟩ : syracuseStep 2189435 = 3284153) B3284153
theorem B5838493 : Blo 2049435 5838493 := bstep (se 3 (by rfl) ⟨1094717, by rfl⟩ : syracuseStep 5838493 = 2189435) B2189435
theorem B7784657 : Blo 2049435 7784657 := bstep (se 2 (by rfl) ⟨2919246, by rfl⟩ : syracuseStep 7784657 = 5838493) B5838493
theorem B5189771 : Blo 2049435 5189771 := bstep (se 1 (by rfl) ⟨3892328, by rfl⟩ : syracuseStep 5189771 = 7784657) B7784657
theorem B3459847 : Blo 2049435 3459847 := bstep (se 1 (by rfl) ⟨2594885, by rfl⟩ : syracuseStep 3459847 = 5189771) B5189771
theorem B4613129 : Blo 2049435 4613129 := bstep (se 2 (by rfl) ⟨1729923, by rfl⟩ : syracuseStep 4613129 = 3459847) B3459847
theorem B3075419 : Blo 2049435 3075419 := bstep (se 1 (by rfl) ⟨2306564, by rfl⟩ : syracuseStep 3075419 = 4613129) B4613129
theorem B2050279 : Blo 2049435 2050279 := bstep (se 1 (by rfl) ⟨1537709, by rfl⟩ : syracuseStep 2050279 = 3075419) B3075419
theorem B2306569 : Blo 2049435 2306569 := bbase (se 2 (by rfl) ⟨864963, by rfl⟩ : syracuseStep 2306569 = 1729927) (by norm_num)
theorem B3075425 : Blo 2049435 3075425 := bstep (se 2 (by rfl) ⟨1153284, by rfl⟩ : syracuseStep 3075425 = 2306569) B2306569
theorem B2050283 : Blo 2049435 2050283 := bstep (se 1 (by rfl) ⟨1537712, by rfl⟩ : syracuseStep 2050283 = 3075425) B3075425
theorem B4739885 : Blo 2049435 4739885 := bbase (se 3 (by rfl) ⟨888728, by rfl⟩ : syracuseStep 4739885 = 1777457) (by norm_num)
theorem B3159923 : Blo 2049435 3159923 := bstep (se 1 (by rfl) ⟨2369942, by rfl⟩ : syracuseStep 3159923 = 4739885) B4739885
theorem B8426461 : Blo 2049435 8426461 := bstep (se 3 (by rfl) ⟨1579961, by rfl⟩ : syracuseStep 8426461 = 3159923) B3159923
theorem B11235281 : Blo 2049435 11235281 := bstep (se 2 (by rfl) ⟨4213230, by rfl⟩ : syracuseStep 11235281 = 8426461) B8426461
theorem B29960749 : Blo 2049435 29960749 := bstep (se 3 (by rfl) ⟨5617640, by rfl⟩ : syracuseStep 29960749 = 11235281) B11235281
theorem B159790661 : Blo 2049435 159790661 := bstep (se 4 (by rfl) ⟨14980374, by rfl⟩ : syracuseStep 159790661 = 29960749) B29960749
theorem B106527107 : Blo 2049435 106527107 := bstep (se 1 (by rfl) ⟨79895330, by rfl⟩ : syracuseStep 106527107 = 159790661) B159790661
theorem B284072285 : Blo 2049435 284072285 := bstep (se 3 (by rfl) ⟨53263553, by rfl⟩ : syracuseStep 284072285 = 106527107) B106527107
theorem B189381523 : Blo 2049435 189381523 := bstep (se 1 (by rfl) ⟨142036142, by rfl⟩ : syracuseStep 189381523 = 284072285) B284072285
theorem B252508697 : Blo 2049435 252508697 := bstep (se 2 (by rfl) ⟨94690761, by rfl⟩ : syracuseStep 252508697 = 189381523) B189381523
theorem B168339131 : Blo 2049435 168339131 := bstep (se 1 (by rfl) ⟨126254348, by rfl⟩ : syracuseStep 168339131 = 252508697) B252508697
theorem B112226087 : Blo 2049435 112226087 := bstep (se 1 (by rfl) ⟨84169565, by rfl⟩ : syracuseStep 112226087 = 168339131) B168339131
theorem B74817391 : Blo 2049435 74817391 := bstep (se 1 (by rfl) ⟨56113043, by rfl⟩ : syracuseStep 74817391 = 112226087) B112226087
theorem B99756521 : Blo 2049435 99756521 := bstep (se 2 (by rfl) ⟨37408695, by rfl⟩ : syracuseStep 99756521 = 74817391) B74817391
theorem B66504347 : Blo 2049435 66504347 := bstep (se 1 (by rfl) ⟨49878260, by rfl⟩ : syracuseStep 66504347 = 99756521) B99756521
theorem B44336231 : Blo 2049435 44336231 := bstep (se 1 (by rfl) ⟨33252173, by rfl⟩ : syracuseStep 44336231 = 66504347) B66504347
theorem B29557487 : Blo 2049435 29557487 := bstep (se 1 (by rfl) ⟨22168115, by rfl⟩ : syracuseStep 29557487 = 44336231) B44336231
theorem B19704991 : Blo 2049435 19704991 := bstep (se 1 (by rfl) ⟨14778743, by rfl⟩ : syracuseStep 19704991 = 29557487) B29557487
theorem B26273321 : Blo 2049435 26273321 := bstep (se 2 (by rfl) ⟨9852495, by rfl⟩ : syracuseStep 26273321 = 19704991) B19704991
theorem B17515547 : Blo 2049435 17515547 := bstep (se 1 (by rfl) ⟨13136660, by rfl⟩ : syracuseStep 17515547 = 26273321) B26273321
theorem B11677031 : Blo 2049435 11677031 := bstep (se 1 (by rfl) ⟨8757773, by rfl⟩ : syracuseStep 11677031 = 17515547) B17515547
theorem B7784687 : Blo 2049435 7784687 := bstep (se 1 (by rfl) ⟨5838515, by rfl⟩ : syracuseStep 7784687 = 11677031) B11677031
theorem B5189791 : Blo 2049435 5189791 := bstep (se 1 (by rfl) ⟨3892343, by rfl⟩ : syracuseStep 5189791 = 7784687) B7784687
theorem B6919721 : Blo 2049435 6919721 := bstep (se 2 (by rfl) ⟨2594895, by rfl⟩ : syracuseStep 6919721 = 5189791) B5189791
theorem B4613147 : Blo 2049435 4613147 := bstep (se 1 (by rfl) ⟨3459860, by rfl⟩ : syracuseStep 4613147 = 6919721) B6919721
theorem B3075431 : Blo 2049435 3075431 := bstep (se 1 (by rfl) ⟨2306573, by rfl⟩ : syracuseStep 3075431 = 4613147) B4613147
theorem B2050287 : Blo 2049435 2050287 := bstep (se 1 (by rfl) ⟨1537715, by rfl⟩ : syracuseStep 2050287 = 3075431) B3075431
theorem B3075437 : Blo 2049435 3075437 := bbase (se 3 (by rfl) ⟨576644, by rfl⟩ : syracuseStep 3075437 = 1153289) (by norm_num)
theorem B2050291 : Blo 2049435 2050291 := bstep (se 1 (by rfl) ⟨1537718, by rfl⟩ : syracuseStep 2050291 = 3075437) B3075437
theorem B4613165 : Blo 2049435 4613165 := bbase (se 3 (by rfl) ⟨864968, by rfl⟩ : syracuseStep 4613165 = 1729937) (by norm_num)
theorem B3075443 : Blo 2049435 3075443 := bstep (se 1 (by rfl) ⟨2306582, by rfl⟩ : syracuseStep 3075443 = 4613165) B4613165
theorem B2050295 : Blo 2049435 2050295 := bstep (se 1 (by rfl) ⟨1537721, by rfl⟩ : syracuseStep 2050295 = 3075443) B3075443
theorem B3694709 : Blo 2049435 3694709 := bbase (se 5 (by rfl) ⟨173189, by rfl⟩ : syracuseStep 3694709 = 346379) (by norm_num)
theorem B2463139 : Blo 2049435 2463139 := bstep (se 1 (by rfl) ⟨1847354, by rfl⟩ : syracuseStep 2463139 = 3694709) B3694709
theorem B13136741 : Blo 2049435 13136741 := bstep (se 4 (by rfl) ⟨1231569, by rfl⟩ : syracuseStep 13136741 = 2463139) B2463139
theorem B8757827 : Blo 2049435 8757827 := bstep (se 1 (by rfl) ⟨6568370, by rfl⟩ : syracuseStep 8757827 = 13136741) B13136741
theorem B5838551 : Blo 2049435 5838551 := bstep (se 1 (by rfl) ⟨4378913, by rfl⟩ : syracuseStep 5838551 = 8757827) B8757827
theorem B3892367 : Blo 2049435 3892367 := bstep (se 1 (by rfl) ⟨2919275, by rfl⟩ : syracuseStep 3892367 = 5838551) B5838551
theorem B2594911 : Blo 2049435 2594911 := bstep (se 1 (by rfl) ⟨1946183, by rfl⟩ : syracuseStep 2594911 = 3892367) B3892367
theorem B3459881 : Blo 2049435 3459881 := bstep (se 2 (by rfl) ⟨1297455, by rfl⟩ : syracuseStep 3459881 = 2594911) B2594911
theorem B2306587 : Blo 2049435 2306587 := bstep (se 1 (by rfl) ⟨1729940, by rfl⟩ : syracuseStep 2306587 = 3459881) B3459881
theorem B3075449 : Blo 2049435 3075449 := bstep (se 2 (by rfl) ⟨1153293, by rfl⟩ : syracuseStep 3075449 = 2306587) B2306587
theorem B2050299 : Blo 2049435 2050299 := bstep (se 1 (by rfl) ⟨1537724, by rfl⟩ : syracuseStep 2050299 = 3075449) B3075449
theorem B4676125 : Blo 2049435 4676125 := bbase (se 3 (by rfl) ⟨876773, by rfl⟩ : syracuseStep 4676125 = 1753547) (by norm_num)
theorem B6234833 : Blo 2049435 6234833 := bstep (se 2 (by rfl) ⟨2338062, by rfl⟩ : syracuseStep 6234833 = 4676125) B4676125
theorem B4156555 : Blo 2049435 4156555 := bstep (se 1 (by rfl) ⟨3117416, by rfl⟩ : syracuseStep 4156555 = 6234833) B6234833
theorem B5542073 : Blo 2049435 5542073 := bstep (se 2 (by rfl) ⟨2078277, by rfl⟩ : syracuseStep 5542073 = 4156555) B4156555
theorem B3694715 : Blo 2049435 3694715 := bstep (se 1 (by rfl) ⟨2771036, by rfl⟩ : syracuseStep 3694715 = 5542073) B5542073
theorem B2463143 : Blo 2049435 2463143 := bstep (se 1 (by rfl) ⟨1847357, by rfl⟩ : syracuseStep 2463143 = 3694715) B3694715
theorem B6568381 : Blo 2049435 6568381 := bstep (se 3 (by rfl) ⟨1231571, by rfl⟩ : syracuseStep 6568381 = 2463143) B2463143
theorem B35031365 : Blo 2049435 35031365 := bstep (se 4 (by rfl) ⟨3284190, by rfl⟩ : syracuseStep 35031365 = 6568381) B6568381
theorem B23354243 : Blo 2049435 23354243 := bstep (se 1 (by rfl) ⟨17515682, by rfl⟩ : syracuseStep 23354243 = 35031365) B35031365
theorem B15569495 : Blo 2049435 15569495 := bstep (se 1 (by rfl) ⟨11677121, by rfl⟩ : syracuseStep 15569495 = 23354243) B23354243
theorem B10379663 : Blo 2049435 10379663 := bstep (se 1 (by rfl) ⟨7784747, by rfl⟩ : syracuseStep 10379663 = 15569495) B15569495
theorem B6919775 : Blo 2049435 6919775 := bstep (se 1 (by rfl) ⟨5189831, by rfl⟩ : syracuseStep 6919775 = 10379663) B10379663
theorem B4613183 : Blo 2049435 4613183 := bstep (se 1 (by rfl) ⟨3459887, by rfl⟩ : syracuseStep 4613183 = 6919775) B6919775
theorem B3075455 : Blo 2049435 3075455 := bstep (se 1 (by rfl) ⟨2306591, by rfl⟩ : syracuseStep 3075455 = 4613183) B4613183
theorem B2050303 : Blo 2049435 2050303 := bstep (se 1 (by rfl) ⟨1537727, by rfl⟩ : syracuseStep 2050303 = 3075455) B3075455
theorem B3075461 : Blo 2049435 3075461 := bbase (se 4 (by rfl) ⟨288324, by rfl⟩ : syracuseStep 3075461 = 576649) (by norm_num)
theorem B2050307 : Blo 2049435 2050307 := bstep (se 1 (by rfl) ⟨1537730, by rfl⟩ : syracuseStep 2050307 = 3075461) B3075461
theorem B3459901 : Blo 2049435 3459901 := bbase (se 3 (by rfl) ⟨648731, by rfl⟩ : syracuseStep 3459901 = 1297463) (by norm_num)
theorem B4613201 : Blo 2049435 4613201 := bstep (se 2 (by rfl) ⟨1729950, by rfl⟩ : syracuseStep 4613201 = 3459901) B3459901
theorem B3075467 : Blo 2049435 3075467 := bstep (se 1 (by rfl) ⟨2306600, by rfl⟩ : syracuseStep 3075467 = 4613201) B4613201
theorem B2050311 : Blo 2049435 2050311 := bstep (se 1 (by rfl) ⟨1537733, by rfl⟩ : syracuseStep 2050311 = 3075467) B3075467
theorem B2306605 : Blo 2049435 2306605 := bbase (se 3 (by rfl) ⟨432488, by rfl⟩ : syracuseStep 2306605 = 864977) (by norm_num)
theorem B3075473 : Blo 2049435 3075473 := bstep (se 2 (by rfl) ⟨1153302, by rfl⟩ : syracuseStep 3075473 = 2306605) B2306605
theorem B2050315 : Blo 2049435 2050315 := bstep (se 1 (by rfl) ⟨1537736, by rfl⟩ : syracuseStep 2050315 = 3075473) B3075473
theorem B6919829 : Blo 2049435 6919829 := bbase (se 6 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 6919829 = 324367) (by norm_num)
theorem B4613219 : Blo 2049435 4613219 := bstep (se 1 (by rfl) ⟨3459914, by rfl⟩ : syracuseStep 4613219 = 6919829) B6919829
theorem B3075479 : Blo 2049435 3075479 := bstep (se 1 (by rfl) ⟨2306609, by rfl⟩ : syracuseStep 3075479 = 4613219) B4613219
theorem B2050319 : Blo 2049435 2050319 := bstep (se 1 (by rfl) ⟨1537739, by rfl⟩ : syracuseStep 2050319 = 3075479) B3075479
theorem B3075485 : Blo 2049435 3075485 := bbase (se 3 (by rfl) ⟨576653, by rfl⟩ : syracuseStep 3075485 = 1153307) (by norm_num)
theorem B2050323 : Blo 2049435 2050323 := bstep (se 1 (by rfl) ⟨1537742, by rfl⟩ : syracuseStep 2050323 = 3075485) B3075485
theorem B4613237 : Blo 2049435 4613237 := bbase (se 5 (by rfl) ⟨216245, by rfl⟩ : syracuseStep 4613237 = 432491) (by norm_num)
theorem B3075491 : Blo 2049435 3075491 := bstep (se 1 (by rfl) ⟨2306618, by rfl⟩ : syracuseStep 3075491 = 4613237) B4613237
theorem B2050327 : Blo 2049435 2050327 := bstep (se 1 (by rfl) ⟨1537745, by rfl⟩ : syracuseStep 2050327 = 3075491) B3075491
theorem B17515925 : Blo 2049435 17515925 := bbase (se 6 (by rfl) ⟨410529, by rfl⟩ : syracuseStep 17515925 = 821059) (by norm_num)
theorem B11677283 : Blo 2049435 11677283 := bstep (se 1 (by rfl) ⟨8757962, by rfl⟩ : syracuseStep 11677283 = 17515925) B17515925
theorem B7784855 : Blo 2049435 7784855 := bstep (se 1 (by rfl) ⟨5838641, by rfl⟩ : syracuseStep 7784855 = 11677283) B11677283
theorem B5189903 : Blo 2049435 5189903 := bstep (se 1 (by rfl) ⟨3892427, by rfl⟩ : syracuseStep 5189903 = 7784855) B7784855
theorem B3459935 : Blo 2049435 3459935 := bstep (se 1 (by rfl) ⟨2594951, by rfl⟩ : syracuseStep 3459935 = 5189903) B5189903
theorem B2306623 : Blo 2049435 2306623 := bstep (se 1 (by rfl) ⟨1729967, by rfl⟩ : syracuseStep 2306623 = 3459935) B3459935
theorem B3075497 : Blo 2049435 3075497 := bstep (se 2 (by rfl) ⟨1153311, by rfl⟩ : syracuseStep 3075497 = 2306623) B2306623
theorem B2050331 : Blo 2049435 2050331 := bstep (se 1 (by rfl) ⟨1537748, by rfl⟩ : syracuseStep 2050331 = 3075497) B3075497
theorem B7784869 : Blo 2049435 7784869 := bbase (se 4 (by rfl) ⟨729831, by rfl⟩ : syracuseStep 7784869 = 1459663) (by norm_num)
theorem B10379825 : Blo 2049435 10379825 := bstep (se 2 (by rfl) ⟨3892434, by rfl⟩ : syracuseStep 10379825 = 7784869) B7784869
theorem B6919883 : Blo 2049435 6919883 := bstep (se 1 (by rfl) ⟨5189912, by rfl⟩ : syracuseStep 6919883 = 10379825) B10379825
theorem B4613255 : Blo 2049435 4613255 := bstep (se 1 (by rfl) ⟨3459941, by rfl⟩ : syracuseStep 4613255 = 6919883) B6919883
theorem B3075503 : Blo 2049435 3075503 := bstep (se 1 (by rfl) ⟨2306627, by rfl⟩ : syracuseStep 3075503 = 4613255) B4613255
theorem B2050335 : Blo 2049435 2050335 := bstep (se 1 (by rfl) ⟨1537751, by rfl⟩ : syracuseStep 2050335 = 3075503) B3075503
theorem B3075509 : Blo 2049435 3075509 := bbase (se 5 (by rfl) ⟨144164, by rfl⟩ : syracuseStep 3075509 = 288329) (by norm_num)
theorem B2050339 : Blo 2049435 2050339 := bstep (se 1 (by rfl) ⟨1537754, by rfl⟩ : syracuseStep 2050339 = 3075509) B3075509
theorem B5189933 : Blo 2049435 5189933 := bbase (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) (by norm_num)
theorem B3459955 : Blo 2049435 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B4613273 : Blo 2049435 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B3075515 : Blo 2049435 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B2050343 : Blo 2049435 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B2306641 : Blo 2049435 2306641 := bbase (se 2 (by rfl) ⟨864990, by rfl⟩ : syracuseStep 2306641 = 1729981) (by norm_num)
theorem B3075521 : Blo 2049435 3075521 := bstep (se 2 (by rfl) ⟨1153320, by rfl⟩ : syracuseStep 3075521 = 2306641) B2306641
theorem B2050347 : Blo 2049435 2050347 := bstep (se 1 (by rfl) ⟨1537760, by rfl⟩ : syracuseStep 2050347 = 3075521) B3075521
theorem B2919349 : Blo 2049435 2919349 := bbase (se 5 (by rfl) ⟨136844, by rfl⟩ : syracuseStep 2919349 = 273689) (by norm_num)
theorem B3892465 : Blo 2049435 3892465 := bstep (se 2 (by rfl) ⟨1459674, by rfl⟩ : syracuseStep 3892465 = 2919349) B2919349
theorem B5189953 : Blo 2049435 5189953 := bstep (se 2 (by rfl) ⟨1946232, by rfl⟩ : syracuseStep 5189953 = 3892465) B3892465
theorem B6919937 : Blo 2049435 6919937 := bstep (se 2 (by rfl) ⟨2594976, by rfl⟩ : syracuseStep 6919937 = 5189953) B5189953
theorem B4613291 : Blo 2049435 4613291 := bstep (se 1 (by rfl) ⟨3459968, by rfl⟩ : syracuseStep 4613291 = 6919937) B6919937
theorem B3075527 : Blo 2049435 3075527 := bstep (se 1 (by rfl) ⟨2306645, by rfl⟩ : syracuseStep 3075527 = 4613291) B4613291
theorem B2050351 : Blo 2049435 2050351 := bstep (se 1 (by rfl) ⟨1537763, by rfl⟩ : syracuseStep 2050351 = 3075527) B3075527
theorem B3075533 : Blo 2049435 3075533 := bbase (se 3 (by rfl) ⟨576662, by rfl⟩ : syracuseStep 3075533 = 1153325) (by norm_num)
theorem B2050355 : Blo 2049435 2050355 := bstep (se 1 (by rfl) ⟨1537766, by rfl⟩ : syracuseStep 2050355 = 3075533) B3075533
theorem B4613309 : Blo 2049435 4613309 := bbase (se 3 (by rfl) ⟨864995, by rfl⟩ : syracuseStep 4613309 = 1729991) (by norm_num)
theorem B3075539 : Blo 2049435 3075539 := bstep (se 1 (by rfl) ⟨2306654, by rfl⟩ : syracuseStep 3075539 = 4613309) B4613309
theorem B2050359 : Blo 2049435 2050359 := bstep (se 1 (by rfl) ⟨1537769, by rfl⟩ : syracuseStep 2050359 = 3075539) B3075539
theorem B3459989 : Blo 2049435 3459989 := bbase (se 6 (by rfl) ⟨81093, by rfl⟩ : syracuseStep 3459989 = 162187) (by norm_num)
theorem B2306659 : Blo 2049435 2306659 := bstep (se 1 (by rfl) ⟨1729994, by rfl⟩ : syracuseStep 2306659 = 3459989) B3459989
theorem B3075545 : Blo 2049435 3075545 := bstep (se 2 (by rfl) ⟨1153329, by rfl⟩ : syracuseStep 3075545 = 2306659) B2306659
theorem B2050363 : Blo 2049435 2050363 := bstep (se 1 (by rfl) ⟨1537772, by rfl⟩ : syracuseStep 2050363 = 3075545) B3075545
theorem B13137173 : Blo 2049435 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B8758115 : Blo 2049435 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B5838743 : Blo 2049435 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B15569981 : Blo 2049435 15569981 := bstep (se 3 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 15569981 = 5838743) B5838743
theorem B10379987 : Blo 2049435 10379987 := bstep (se 1 (by rfl) ⟨7784990, by rfl⟩ : syracuseStep 10379987 = 15569981) B15569981
theorem B6919991 : Blo 2049435 6919991 := bstep (se 1 (by rfl) ⟨5189993, by rfl⟩ : syracuseStep 6919991 = 10379987) B10379987
theorem B4613327 : Blo 2049435 4613327 := bstep (se 1 (by rfl) ⟨3459995, by rfl⟩ : syracuseStep 4613327 = 6919991) B6919991
theorem B3075551 : Blo 2049435 3075551 := bstep (se 1 (by rfl) ⟨2306663, by rfl⟩ : syracuseStep 3075551 = 4613327) B4613327
theorem B2050367 : Blo 2049435 2050367 := bstep (se 1 (by rfl) ⟨1537775, by rfl⟩ : syracuseStep 2050367 = 3075551) B3075551
theorem B3075557 : Blo 2049435 3075557 := bbase (se 4 (by rfl) ⟨288333, by rfl⟩ : syracuseStep 3075557 = 576667) (by norm_num)
theorem B2050371 : Blo 2049435 2050371 := bstep (se 1 (by rfl) ⟨1537778, by rfl⟩ : syracuseStep 2050371 = 3075557) B3075557
theorem B14779381 : Blo 2049435 14779381 := bbase (se 5 (by rfl) ⟨692783, by rfl⟩ : syracuseStep 14779381 = 1385567) (by norm_num)
theorem B19705841 : Blo 2049435 19705841 := bstep (se 2 (by rfl) ⟨7389690, by rfl⟩ : syracuseStep 19705841 = 14779381) B14779381
theorem B13137227 : Blo 2049435 13137227 := bstep (se 1 (by rfl) ⟨9852920, by rfl⟩ : syracuseStep 13137227 = 19705841) B19705841
theorem B8758151 : Blo 2049435 8758151 := bstep (se 1 (by rfl) ⟨6568613, by rfl⟩ : syracuseStep 8758151 = 13137227) B13137227
theorem B5838767 : Blo 2049435 5838767 := bstep (se 1 (by rfl) ⟨4379075, by rfl⟩ : syracuseStep 5838767 = 8758151) B8758151
theorem B3892511 : Blo 2049435 3892511 := bstep (se 1 (by rfl) ⟨2919383, by rfl⟩ : syracuseStep 3892511 = 5838767) B5838767
theorem B2595007 : Blo 2049435 2595007 := bstep (se 1 (by rfl) ⟨1946255, by rfl⟩ : syracuseStep 2595007 = 3892511) B3892511
theorem B3460009 : Blo 2049435 3460009 := bstep (se 2 (by rfl) ⟨1297503, by rfl⟩ : syracuseStep 3460009 = 2595007) B2595007
theorem B4613345 : Blo 2049435 4613345 := bstep (se 2 (by rfl) ⟨1730004, by rfl⟩ : syracuseStep 4613345 = 3460009) B3460009
theorem B3075563 : Blo 2049435 3075563 := bstep (se 1 (by rfl) ⟨2306672, by rfl⟩ : syracuseStep 3075563 = 4613345) B4613345
theorem B2050375 : Blo 2049435 2050375 := bstep (se 1 (by rfl) ⟨1537781, by rfl⟩ : syracuseStep 2050375 = 3075563) B3075563
theorem B2306677 : Blo 2049435 2306677 := bbase (se 5 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 2306677 = 216251) (by norm_num)
theorem B3075569 : Blo 2049435 3075569 := bstep (se 2 (by rfl) ⟨1153338, by rfl⟩ : syracuseStep 3075569 = 2306677) B2306677
theorem B2050379 : Blo 2049435 2050379 := bstep (se 1 (by rfl) ⟨1537784, by rfl⟩ : syracuseStep 2050379 = 3075569) B3075569
theorem B2595017 : Blo 2049435 2595017 := bbase (se 2 (by rfl) ⟨973131, by rfl⟩ : syracuseStep 2595017 = 1946263) (by norm_num)
theorem B6920045 : Blo 2049435 6920045 := bstep (se 3 (by rfl) ⟨1297508, by rfl⟩ : syracuseStep 6920045 = 2595017) B2595017
theorem B4613363 : Blo 2049435 4613363 := bstep (se 1 (by rfl) ⟨3460022, by rfl⟩ : syracuseStep 4613363 = 6920045) B6920045
theorem B3075575 : Blo 2049435 3075575 := bstep (se 1 (by rfl) ⟨2306681, by rfl⟩ : syracuseStep 3075575 = 4613363) B4613363
theorem B2050383 : Blo 2049435 2050383 := bstep (se 1 (by rfl) ⟨1537787, by rfl⟩ : syracuseStep 2050383 = 3075575) B3075575
theorem B3075581 : Blo 2049435 3075581 := bbase (se 3 (by rfl) ⟨576671, by rfl⟩ : syracuseStep 3075581 = 1153343) (by norm_num)
theorem B2050387 : Blo 2049435 2050387 := bstep (se 1 (by rfl) ⟨1537790, by rfl⟩ : syracuseStep 2050387 = 3075581) B3075581
theorem B4613381 : Blo 2049435 4613381 := bbase (se 4 (by rfl) ⟨432504, by rfl⟩ : syracuseStep 4613381 = 865009) (by norm_num)
theorem B3075587 : Blo 2049435 3075587 := bstep (se 1 (by rfl) ⟨2306690, by rfl⟩ : syracuseStep 3075587 = 4613381) B4613381
theorem B2050391 : Blo 2049435 2050391 := bstep (se 1 (by rfl) ⟨1537793, by rfl⟩ : syracuseStep 2050391 = 3075587) B3075587
theorem B3892549 : Blo 2049435 3892549 := bbase (se 4 (by rfl) ⟨364926, by rfl⟩ : syracuseStep 3892549 = 729853) (by norm_num)
theorem B5190065 : Blo 2049435 5190065 := bstep (se 2 (by rfl) ⟨1946274, by rfl⟩ : syracuseStep 5190065 = 3892549) B3892549
theorem B3460043 : Blo 2049435 3460043 := bstep (se 1 (by rfl) ⟨2595032, by rfl⟩ : syracuseStep 3460043 = 5190065) B5190065
theorem B2306695 : Blo 2049435 2306695 := bstep (se 1 (by rfl) ⟨1730021, by rfl⟩ : syracuseStep 2306695 = 3460043) B3460043
theorem B3075593 : Blo 2049435 3075593 := bstep (se 2 (by rfl) ⟨1153347, by rfl⟩ : syracuseStep 3075593 = 2306695) B2306695
theorem B2050395 : Blo 2049435 2050395 := bstep (se 1 (by rfl) ⟨1537796, by rfl⟩ : syracuseStep 2050395 = 3075593) B3075593
theorem B10380149 : Blo 2049435 10380149 := bbase (se 5 (by rfl) ⟨486569, by rfl⟩ : syracuseStep 10380149 = 973139) (by norm_num)
theorem B6920099 : Blo 2049435 6920099 := bstep (se 1 (by rfl) ⟨5190074, by rfl⟩ : syracuseStep 6920099 = 10380149) B10380149
theorem B4613399 : Blo 2049435 4613399 := bstep (se 1 (by rfl) ⟨3460049, by rfl⟩ : syracuseStep 4613399 = 6920099) B6920099
theorem B3075599 : Blo 2049435 3075599 := bstep (se 1 (by rfl) ⟨2306699, by rfl⟩ : syracuseStep 3075599 = 4613399) B4613399
theorem B2050399 : Blo 2049435 2050399 := bstep (se 1 (by rfl) ⟨1537799, by rfl⟩ : syracuseStep 2050399 = 3075599) B3075599
theorem B3075605 : Blo 2049435 3075605 := bbase (se 6 (by rfl) ⟨72084, by rfl⟩ : syracuseStep 3075605 = 144169) (by norm_num)
theorem B2050403 : Blo 2049435 2050403 := bstep (se 1 (by rfl) ⟨1537802, by rfl⟩ : syracuseStep 2050403 = 3075605) B3075605
theorem B5260909 : Blo 2049435 5260909 := bbase (se 3 (by rfl) ⟨986420, by rfl⟩ : syracuseStep 5260909 = 1972841) (by norm_num)
theorem B7014545 : Blo 2049435 7014545 := bstep (se 2 (by rfl) ⟨2630454, by rfl⟩ : syracuseStep 7014545 = 5260909) B5260909
theorem B4676363 : Blo 2049435 4676363 := bstep (se 1 (by rfl) ⟨3507272, by rfl⟩ : syracuseStep 4676363 = 7014545) B7014545
theorem B3117575 : Blo 2049435 3117575 := bstep (se 1 (by rfl) ⟨2338181, by rfl⟩ : syracuseStep 3117575 = 4676363) B4676363
theorem B2078383 : Blo 2049435 2078383 := bstep (se 1 (by rfl) ⟨1558787, by rfl⟩ : syracuseStep 2078383 = 3117575) B3117575
theorem B2771177 : Blo 2049435 2771177 := bstep (se 2 (by rfl) ⟨1039191, by rfl⟩ : syracuseStep 2771177 = 2078383) B2078383
theorem B7389805 : Blo 2049435 7389805 := bstep (se 3 (by rfl) ⟨1385588, by rfl⟩ : syracuseStep 7389805 = 2771177) B2771177
theorem B9853073 : Blo 2049435 9853073 := bstep (se 2 (by rfl) ⟨3694902, by rfl⟩ : syracuseStep 9853073 = 7389805) B7389805
theorem B6568715 : Blo 2049435 6568715 := bstep (se 1 (by rfl) ⟨4926536, by rfl⟩ : syracuseStep 6568715 = 9853073) B9853073
theorem B17516573 : Blo 2049435 17516573 := bstep (se 3 (by rfl) ⟨3284357, by rfl⟩ : syracuseStep 17516573 = 6568715) B6568715
theorem B11677715 : Blo 2049435 11677715 := bstep (se 1 (by rfl) ⟨8758286, by rfl⟩ : syracuseStep 11677715 = 17516573) B17516573
theorem B7785143 : Blo 2049435 7785143 := bstep (se 1 (by rfl) ⟨5838857, by rfl⟩ : syracuseStep 7785143 = 11677715) B11677715
theorem B5190095 : Blo 2049435 5190095 := bstep (se 1 (by rfl) ⟨3892571, by rfl⟩ : syracuseStep 5190095 = 7785143) B7785143
theorem B3460063 : Blo 2049435 3460063 := bstep (se 1 (by rfl) ⟨2595047, by rfl⟩ : syracuseStep 3460063 = 5190095) B5190095
theorem B4613417 : Blo 2049435 4613417 := bstep (se 2 (by rfl) ⟨1730031, by rfl⟩ : syracuseStep 4613417 = 3460063) B3460063
theorem B3075611 : Blo 2049435 3075611 := bstep (se 1 (by rfl) ⟨2306708, by rfl⟩ : syracuseStep 3075611 = 4613417) B4613417
theorem B2050407 : Blo 2049435 2050407 := bstep (se 1 (by rfl) ⟨1537805, by rfl⟩ : syracuseStep 2050407 = 3075611) B3075611
theorem B2306713 : Blo 2049435 2306713 := bbase (se 2 (by rfl) ⟨865017, by rfl⟩ : syracuseStep 2306713 = 1730035) (by norm_num)
theorem B3075617 : Blo 2049435 3075617 := bstep (se 2 (by rfl) ⟨1153356, by rfl⟩ : syracuseStep 3075617 = 2306713) B2306713
theorem B2050411 : Blo 2049435 2050411 := bstep (se 1 (by rfl) ⟨1537808, by rfl⟩ : syracuseStep 2050411 = 3075617) B3075617
theorem B7785173 : Blo 2049435 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B5190115 : Blo 2049435 5190115 := bstep (se 1 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 5190115 = 7785173) B7785173
theorem B6920153 : Blo 2049435 6920153 := bstep (se 2 (by rfl) ⟨2595057, by rfl⟩ : syracuseStep 6920153 = 5190115) B5190115
theorem B4613435 : Blo 2049435 4613435 := bstep (se 1 (by rfl) ⟨3460076, by rfl⟩ : syracuseStep 4613435 = 6920153) B6920153
theorem B3075623 : Blo 2049435 3075623 := bstep (se 1 (by rfl) ⟨2306717, by rfl⟩ : syracuseStep 3075623 = 4613435) B4613435
theorem B2050415 : Blo 2049435 2050415 := bstep (se 1 (by rfl) ⟨1537811, by rfl⟩ : syracuseStep 2050415 = 3075623) B3075623
theorem B3075629 : Blo 2049435 3075629 := bbase (se 3 (by rfl) ⟨576680, by rfl⟩ : syracuseStep 3075629 = 1153361) (by norm_num)
theorem B2050419 : Blo 2049435 2050419 := bstep (se 1 (by rfl) ⟨1537814, by rfl⟩ : syracuseStep 2050419 = 3075629) B3075629
theorem B4613453 : Blo 2049435 4613453 := bbase (se 3 (by rfl) ⟨865022, by rfl⟩ : syracuseStep 4613453 = 1730045) (by norm_num)
theorem B3075635 : Blo 2049435 3075635 := bstep (se 1 (by rfl) ⟨2306726, by rfl⟩ : syracuseStep 3075635 = 4613453) B4613453
theorem B2050423 : Blo 2049435 2050423 := bstep (se 1 (by rfl) ⟨1537817, by rfl⟩ : syracuseStep 2050423 = 3075635) B3075635
theorem B2595073 : Blo 2049435 2595073 := bbase (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) (by norm_num)
theorem B3460097 : Blo 2049435 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B2306731 : Blo 2049435 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B3075641 : Blo 2049435 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B2050427 : Blo 2049435 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B2189597 : Blo 2049435 2189597 := bbase (se 3 (by rfl) ⟨410549, by rfl⟩ : syracuseStep 2189597 = 821099) (by norm_num)
theorem B23355701 : Blo 2049435 23355701 := bstep (se 5 (by rfl) ⟨1094798, by rfl⟩ : syracuseStep 23355701 = 2189597) B2189597
theorem B15570467 : Blo 2049435 15570467 := bstep (se 1 (by rfl) ⟨11677850, by rfl⟩ : syracuseStep 15570467 = 23355701) B23355701
theorem B10380311 : Blo 2049435 10380311 := bstep (se 1 (by rfl) ⟨7785233, by rfl⟩ : syracuseStep 10380311 = 15570467) B15570467
theorem B6920207 : Blo 2049435 6920207 := bstep (se 1 (by rfl) ⟨5190155, by rfl⟩ : syracuseStep 6920207 = 10380311) B10380311
theorem B4613471 : Blo 2049435 4613471 := bstep (se 1 (by rfl) ⟨3460103, by rfl⟩ : syracuseStep 4613471 = 6920207) B6920207
theorem B3075647 : Blo 2049435 3075647 := bstep (se 1 (by rfl) ⟨2306735, by rfl⟩ : syracuseStep 3075647 = 4613471) B4613471
theorem B2050431 : Blo 2049435 2050431 := bstep (se 1 (by rfl) ⟨1537823, by rfl⟩ : syracuseStep 2050431 = 3075647) B3075647
theorem B3075653 : Blo 2049435 3075653 := bbase (se 4 (by rfl) ⟨288342, by rfl⟩ : syracuseStep 3075653 = 576685) (by norm_num)
theorem B2050435 : Blo 2049435 2050435 := bstep (se 1 (by rfl) ⟨1537826, by rfl⟩ : syracuseStep 2050435 = 3075653) B3075653
theorem B3460117 : Blo 2049435 3460117 := bbase (se 6 (by rfl) ⟨81096, by rfl⟩ : syracuseStep 3460117 = 162193) (by norm_num)
theorem B4613489 : Blo 2049435 4613489 := bstep (se 2 (by rfl) ⟨1730058, by rfl⟩ : syracuseStep 4613489 = 3460117) B3460117
theorem B3075659 : Blo 2049435 3075659 := bstep (se 1 (by rfl) ⟨2306744, by rfl⟩ : syracuseStep 3075659 = 4613489) B4613489
theorem B2050439 : Blo 2049435 2050439 := bstep (se 1 (by rfl) ⟨1537829, by rfl⟩ : syracuseStep 2050439 = 3075659) B3075659
theorem B2306749 : Blo 2049435 2306749 := bbase (se 3 (by rfl) ⟨432515, by rfl⟩ : syracuseStep 2306749 = 865031) (by norm_num)
theorem B3075665 : Blo 2049435 3075665 := bstep (se 2 (by rfl) ⟨1153374, by rfl⟩ : syracuseStep 3075665 = 2306749) B2306749
theorem B2050443 : Blo 2049435 2050443 := bstep (se 1 (by rfl) ⟨1537832, by rfl⟩ : syracuseStep 2050443 = 3075665) B3075665
theorem B6920261 : Blo 2049435 6920261 := bbase (se 4 (by rfl) ⟨648774, by rfl⟩ : syracuseStep 6920261 = 1297549) (by norm_num)
theorem B4613507 : Blo 2049435 4613507 := bstep (se 1 (by rfl) ⟨3460130, by rfl⟩ : syracuseStep 4613507 = 6920261) B6920261
theorem B3075671 : Blo 2049435 3075671 := bstep (se 1 (by rfl) ⟨2306753, by rfl⟩ : syracuseStep 3075671 = 4613507) B4613507
theorem B2050447 : Blo 2049435 2050447 := bstep (se 1 (by rfl) ⟨1537835, by rfl⟩ : syracuseStep 2050447 = 3075671) B3075671
theorem B3075677 : Blo 2049435 3075677 := bbase (se 3 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 3075677 = 1153379) (by norm_num)
theorem B2050451 : Blo 2049435 2050451 := bstep (se 1 (by rfl) ⟨1537838, by rfl⟩ : syracuseStep 2050451 = 3075677) B3075677
theorem B4613525 : Blo 2049435 4613525 := bbase (se 6 (by rfl) ⟨108129, by rfl⟩ : syracuseStep 4613525 = 216259) (by norm_num)
theorem B3075683 : Blo 2049435 3075683 := bstep (se 1 (by rfl) ⟨2306762, by rfl⟩ : syracuseStep 3075683 = 4613525) B4613525
theorem B2050455 : Blo 2049435 2050455 := bstep (se 1 (by rfl) ⟨1537841, by rfl⟩ : syracuseStep 2050455 = 3075683) B3075683
theorem B3694997 : Blo 2049435 3694997 := bbase (se 6 (by rfl) ⟨86601, by rfl⟩ : syracuseStep 3694997 = 173203) (by norm_num)
theorem B9853325 : Blo 2049435 9853325 := bstep (se 3 (by rfl) ⟨1847498, by rfl⟩ : syracuseStep 9853325 = 3694997) B3694997
theorem B6568883 : Blo 2049435 6568883 := bstep (se 1 (by rfl) ⟨4926662, by rfl⟩ : syracuseStep 6568883 = 9853325) B9853325
theorem B4379255 : Blo 2049435 4379255 := bstep (se 1 (by rfl) ⟨3284441, by rfl⟩ : syracuseStep 4379255 = 6568883) B6568883
theorem B2919503 : Blo 2049435 2919503 := bstep (se 1 (by rfl) ⟨2189627, by rfl⟩ : syracuseStep 2919503 = 4379255) B4379255
theorem B7785341 : Blo 2049435 7785341 := bstep (se 3 (by rfl) ⟨1459751, by rfl⟩ : syracuseStep 7785341 = 2919503) B2919503
theorem B5190227 : Blo 2049435 5190227 := bstep (se 1 (by rfl) ⟨3892670, by rfl⟩ : syracuseStep 5190227 = 7785341) B7785341
theorem B3460151 : Blo 2049435 3460151 := bstep (se 1 (by rfl) ⟨2595113, by rfl⟩ : syracuseStep 3460151 = 5190227) B5190227
theorem B2306767 : Blo 2049435 2306767 := bstep (se 1 (by rfl) ⟨1730075, by rfl⟩ : syracuseStep 2306767 = 3460151) B3460151
theorem B3075689 : Blo 2049435 3075689 := bstep (se 2 (by rfl) ⟨1153383, by rfl⟩ : syracuseStep 3075689 = 2306767) B2306767
theorem B2050459 : Blo 2049435 2050459 := bstep (se 1 (by rfl) ⟨1537844, by rfl⟩ : syracuseStep 2050459 = 3075689) B3075689
theorem B2249789 : Blo 2049435 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B5999437 : Blo 2049435 5999437 := bstep (se 3 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 5999437 = 2249789) B2249789
theorem B7999249 : Blo 2049435 7999249 := bstep (se 2 (by rfl) ⟨2999718, by rfl⟩ : syracuseStep 7999249 = 5999437) B5999437
theorem B10665665 : Blo 2049435 10665665 := bstep (se 2 (by rfl) ⟨3999624, by rfl⟩ : syracuseStep 10665665 = 7999249) B7999249
theorem B7110443 : Blo 2049435 7110443 := bstep (se 1 (by rfl) ⟨5332832, by rfl⟩ : syracuseStep 7110443 = 10665665) B10665665
theorem B4740295 : Blo 2049435 4740295 := bstep (se 1 (by rfl) ⟨3555221, by rfl⟩ : syracuseStep 4740295 = 7110443) B7110443
theorem B6320393 : Blo 2049435 6320393 := bstep (se 2 (by rfl) ⟨2370147, by rfl⟩ : syracuseStep 6320393 = 4740295) B4740295
theorem B4213595 : Blo 2049435 4213595 := bstep (se 1 (by rfl) ⟨3160196, by rfl⟩ : syracuseStep 4213595 = 6320393) B6320393
theorem B2809063 : Blo 2049435 2809063 := bstep (se 1 (by rfl) ⟨2106797, by rfl⟩ : syracuseStep 2809063 = 4213595) B4213595
theorem B14981669 : Blo 2049435 14981669 := bstep (se 4 (by rfl) ⟨1404531, by rfl⟩ : syracuseStep 14981669 = 2809063) B2809063
theorem B9987779 : Blo 2049435 9987779 := bstep (se 1 (by rfl) ⟨7490834, by rfl⟩ : syracuseStep 9987779 = 14981669) B14981669
theorem B6658519 : Blo 2049435 6658519 := bstep (se 1 (by rfl) ⟨4993889, by rfl⟩ : syracuseStep 6658519 = 9987779) B9987779
theorem B8878025 : Blo 2049435 8878025 := bstep (se 2 (by rfl) ⟨3329259, by rfl⟩ : syracuseStep 8878025 = 6658519) B6658519
theorem B5918683 : Blo 2049435 5918683 := bstep (se 1 (by rfl) ⟨4439012, by rfl⟩ : syracuseStep 5918683 = 8878025) B8878025
theorem B7891577 : Blo 2049435 7891577 := bstep (se 2 (by rfl) ⟨2959341, by rfl⟩ : syracuseStep 7891577 = 5918683) B5918683
theorem B5261051 : Blo 2049435 5261051 := bstep (se 1 (by rfl) ⟨3945788, by rfl⟩ : syracuseStep 5261051 = 7891577) B7891577
theorem B14029469 : Blo 2049435 14029469 := bstep (se 3 (by rfl) ⟨2630525, by rfl⟩ : syracuseStep 14029469 = 5261051) B5261051
theorem B9352979 : Blo 2049435 9352979 := bstep (se 1 (by rfl) ⟨7014734, by rfl⟩ : syracuseStep 9352979 = 14029469) B14029469
theorem B6235319 : Blo 2049435 6235319 := bstep (se 1 (by rfl) ⟨4676489, by rfl⟩ : syracuseStep 6235319 = 9352979) B9352979
theorem B16627517 : Blo 2049435 16627517 := bstep (se 3 (by rfl) ⟨3117659, by rfl⟩ : syracuseStep 16627517 = 6235319) B6235319
theorem B11085011 : Blo 2049435 11085011 := bstep (se 1 (by rfl) ⟨8313758, by rfl⟩ : syracuseStep 11085011 = 16627517) B16627517
theorem B7390007 : Blo 2049435 7390007 := bstep (se 1 (by rfl) ⟨5542505, by rfl⟩ : syracuseStep 7390007 = 11085011) B11085011
theorem B4926671 : Blo 2049435 4926671 := bstep (se 1 (by rfl) ⟨3695003, by rfl⟩ : syracuseStep 4926671 = 7390007) B7390007
theorem B3284447 : Blo 2049435 3284447 := bstep (se 1 (by rfl) ⟨2463335, by rfl⟩ : syracuseStep 3284447 = 4926671) B4926671
theorem B8758525 : Blo 2049435 8758525 := bstep (se 3 (by rfl) ⟨1642223, by rfl⟩ : syracuseStep 8758525 = 3284447) B3284447
theorem B11678033 : Blo 2049435 11678033 := bstep (se 2 (by rfl) ⟨4379262, by rfl⟩ : syracuseStep 11678033 = 8758525) B8758525
theorem B7785355 : Blo 2049435 7785355 := bstep (se 1 (by rfl) ⟨5839016, by rfl⟩ : syracuseStep 7785355 = 11678033) B11678033
theorem B10380473 : Blo 2049435 10380473 := bstep (se 2 (by rfl) ⟨3892677, by rfl⟩ : syracuseStep 10380473 = 7785355) B7785355
theorem B6920315 : Blo 2049435 6920315 := bstep (se 1 (by rfl) ⟨5190236, by rfl⟩ : syracuseStep 6920315 = 10380473) B10380473
theorem B4613543 : Blo 2049435 4613543 := bstep (se 1 (by rfl) ⟨3460157, by rfl⟩ : syracuseStep 4613543 = 6920315) B6920315
theorem B3075695 : Blo 2049435 3075695 := bstep (se 1 (by rfl) ⟨2306771, by rfl⟩ : syracuseStep 3075695 = 4613543) B4613543
theorem B2050463 : Blo 2049435 2050463 := bstep (se 1 (by rfl) ⟨1537847, by rfl⟩ : syracuseStep 2050463 = 3075695) B3075695
theorem B3075701 : Blo 2049435 3075701 := bbase (se 5 (by rfl) ⟨144173, by rfl⟩ : syracuseStep 3075701 = 288347) (by norm_num)
theorem B2050467 : Blo 2049435 2050467 := bstep (se 1 (by rfl) ⟨1537850, by rfl⟩ : syracuseStep 2050467 = 3075701) B3075701
theorem B3892693 : Blo 2049435 3892693 := bbase (se 7 (by rfl) ⟨45617, by rfl⟩ : syracuseStep 3892693 = 91235) (by norm_num)
theorem B5190257 : Blo 2049435 5190257 := bstep (se 2 (by rfl) ⟨1946346, by rfl⟩ : syracuseStep 5190257 = 3892693) B3892693
theorem B3460171 : Blo 2049435 3460171 := bstep (se 1 (by rfl) ⟨2595128, by rfl⟩ : syracuseStep 3460171 = 5190257) B5190257
theorem B4613561 : Blo 2049435 4613561 := bstep (se 2 (by rfl) ⟨1730085, by rfl⟩ : syracuseStep 4613561 = 3460171) B3460171
theorem B3075707 : Blo 2049435 3075707 := bstep (se 1 (by rfl) ⟨2306780, by rfl⟩ : syracuseStep 3075707 = 4613561) B4613561
theorem B2050471 : Blo 2049435 2050471 := bstep (se 1 (by rfl) ⟨1537853, by rfl⟩ : syracuseStep 2050471 = 3075707) B3075707
theorem B2306785 : Blo 2049435 2306785 := bbase (se 2 (by rfl) ⟨865044, by rfl⟩ : syracuseStep 2306785 = 1730089) (by norm_num)
theorem B3075713 : Blo 2049435 3075713 := bstep (se 2 (by rfl) ⟨1153392, by rfl⟩ : syracuseStep 3075713 = 2306785) B2306785
theorem B2050475 : Blo 2049435 2050475 := bstep (se 1 (by rfl) ⟨1537856, by rfl⟩ : syracuseStep 2050475 = 3075713) B3075713
theorem B5190277 : Blo 2049435 5190277 := bbase (se 4 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 5190277 = 973177) (by norm_num)
theorem B6920369 : Blo 2049435 6920369 := bstep (se 2 (by rfl) ⟨2595138, by rfl⟩ : syracuseStep 6920369 = 5190277) B5190277
theorem B4613579 : Blo 2049435 4613579 := bstep (se 1 (by rfl) ⟨3460184, by rfl⟩ : syracuseStep 4613579 = 6920369) B6920369
theorem B3075719 : Blo 2049435 3075719 := bstep (se 1 (by rfl) ⟨2306789, by rfl⟩ : syracuseStep 3075719 = 4613579) B4613579
theorem B2050479 : Blo 2049435 2050479 := bstep (se 1 (by rfl) ⟨1537859, by rfl⟩ : syracuseStep 2050479 = 3075719) B3075719
theorem B3075725 : Blo 2049435 3075725 := bbase (se 3 (by rfl) ⟨576698, by rfl⟩ : syracuseStep 3075725 = 1153397) (by norm_num)
theorem B2050483 : Blo 2049435 2050483 := bstep (se 1 (by rfl) ⟨1537862, by rfl⟩ : syracuseStep 2050483 = 3075725) B3075725
theorem B4613597 : Blo 2049435 4613597 := bbase (se 3 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 4613597 = 1730099) (by norm_num)
theorem B3075731 : Blo 2049435 3075731 := bstep (se 1 (by rfl) ⟨2306798, by rfl⟩ : syracuseStep 3075731 = 4613597) B4613597
theorem B2050487 : Blo 2049435 2050487 := bstep (se 1 (by rfl) ⟨1537865, by rfl⟩ : syracuseStep 2050487 = 3075731) B3075731
theorem B3460205 : Blo 2049435 3460205 := bbase (se 3 (by rfl) ⟨648788, by rfl⟩ : syracuseStep 3460205 = 1297577) (by norm_num)
theorem B2306803 : Blo 2049435 2306803 := bstep (se 1 (by rfl) ⟨1730102, by rfl⟩ : syracuseStep 2306803 = 3460205) B3460205
theorem B3075737 : Blo 2049435 3075737 := bstep (se 2 (by rfl) ⟨1153401, by rfl⟩ : syracuseStep 3075737 = 2306803) B2306803
theorem B2050491 : Blo 2049435 2050491 := bstep (se 1 (by rfl) ⟨1537868, by rfl⟩ : syracuseStep 2050491 = 3075737) B3075737
theorem B4499645 : Blo 2049435 4499645 := bbase (se 3 (by rfl) ⟨843683, by rfl⟩ : syracuseStep 4499645 = 1687367) (by norm_num)
theorem B11999053 : Blo 2049435 11999053 := bstep (se 3 (by rfl) ⟨2249822, by rfl⟩ : syracuseStep 11999053 = 4499645) B4499645
theorem B15998737 : Blo 2049435 15998737 := bstep (se 2 (by rfl) ⟨5999526, by rfl⟩ : syracuseStep 15998737 = 11999053) B11999053
theorem B21331649 : Blo 2049435 21331649 := bstep (se 2 (by rfl) ⟨7999368, by rfl⟩ : syracuseStep 21331649 = 15998737) B15998737
theorem B14221099 : Blo 2049435 14221099 := bstep (se 1 (by rfl) ⟨10665824, by rfl⟩ : syracuseStep 14221099 = 21331649) B21331649
theorem B18961465 : Blo 2049435 18961465 := bstep (se 2 (by rfl) ⟨7110549, by rfl⟩ : syracuseStep 18961465 = 14221099) B14221099
theorem B25281953 : Blo 2049435 25281953 := bstep (se 2 (by rfl) ⟨9480732, by rfl⟩ : syracuseStep 25281953 = 18961465) B18961465
theorem B16854635 : Blo 2049435 16854635 := bstep (se 1 (by rfl) ⟨12640976, by rfl⟩ : syracuseStep 16854635 = 25281953) B25281953
theorem B11236423 : Blo 2049435 11236423 := bstep (se 1 (by rfl) ⟨8427317, by rfl⟩ : syracuseStep 11236423 = 16854635) B16854635
theorem B14981897 : Blo 2049435 14981897 := bstep (se 2 (by rfl) ⟨5618211, by rfl⟩ : syracuseStep 14981897 = 11236423) B11236423
theorem B9987931 : Blo 2049435 9987931 := bstep (se 1 (by rfl) ⟨7490948, by rfl⟩ : syracuseStep 9987931 = 14981897) B14981897
theorem B53268965 : Blo 2049435 53268965 := bstep (se 4 (by rfl) ⟨4993965, by rfl⟩ : syracuseStep 53268965 = 9987931) B9987931
theorem B35512643 : Blo 2049435 35512643 := bstep (se 1 (by rfl) ⟨26634482, by rfl⟩ : syracuseStep 35512643 = 53268965) B53268965
theorem B23675095 : Blo 2049435 23675095 := bstep (se 1 (by rfl) ⟨17756321, by rfl⟩ : syracuseStep 23675095 = 35512643) B35512643
theorem B31566793 : Blo 2049435 31566793 := bstep (se 2 (by rfl) ⟨11837547, by rfl⟩ : syracuseStep 31566793 = 23675095) B23675095
theorem B42089057 : Blo 2049435 42089057 := bstep (se 2 (by rfl) ⟨15783396, by rfl⟩ : syracuseStep 42089057 = 31566793) B31566793
theorem B28059371 : Blo 2049435 28059371 := bstep (se 1 (by rfl) ⟨21044528, by rfl⟩ : syracuseStep 28059371 = 42089057) B42089057
theorem B18706247 : Blo 2049435 18706247 := bstep (se 1 (by rfl) ⟨14029685, by rfl⟩ : syracuseStep 18706247 = 28059371) B28059371
theorem B12470831 : Blo 2049435 12470831 := bstep (se 1 (by rfl) ⟨9353123, by rfl⟩ : syracuseStep 12470831 = 18706247) B18706247
theorem B8313887 : Blo 2049435 8313887 := bstep (se 1 (by rfl) ⟨6235415, by rfl⟩ : syracuseStep 8313887 = 12470831) B12470831
theorem B5542591 : Blo 2049435 5542591 := bstep (se 1 (by rfl) ⟨4156943, by rfl⟩ : syracuseStep 5542591 = 8313887) B8313887
theorem B7390121 : Blo 2049435 7390121 := bstep (se 2 (by rfl) ⟨2771295, by rfl⟩ : syracuseStep 7390121 = 5542591) B5542591
theorem B19706989 : Blo 2049435 19706989 := bstep (se 3 (by rfl) ⟨3695060, by rfl⟩ : syracuseStep 19706989 = 7390121) B7390121
theorem B26275985 : Blo 2049435 26275985 := bstep (se 2 (by rfl) ⟨9853494, by rfl⟩ : syracuseStep 26275985 = 19706989) B19706989
theorem B17517323 : Blo 2049435 17517323 := bstep (se 1 (by rfl) ⟨13137992, by rfl⟩ : syracuseStep 17517323 = 26275985) B26275985
theorem B11678215 : Blo 2049435 11678215 := bstep (se 1 (by rfl) ⟨8758661, by rfl⟩ : syracuseStep 11678215 = 17517323) B17517323
theorem B15570953 : Blo 2049435 15570953 := bstep (se 2 (by rfl) ⟨5839107, by rfl⟩ : syracuseStep 15570953 = 11678215) B11678215
theorem B10380635 : Blo 2049435 10380635 := bstep (se 1 (by rfl) ⟨7785476, by rfl⟩ : syracuseStep 10380635 = 15570953) B15570953
theorem B6920423 : Blo 2049435 6920423 := bstep (se 1 (by rfl) ⟨5190317, by rfl⟩ : syracuseStep 6920423 = 10380635) B10380635
theorem B4613615 : Blo 2049435 4613615 := bstep (se 1 (by rfl) ⟨3460211, by rfl⟩ : syracuseStep 4613615 = 6920423) B6920423
theorem B3075743 : Blo 2049435 3075743 := bstep (se 1 (by rfl) ⟨2306807, by rfl⟩ : syracuseStep 3075743 = 4613615) B4613615
theorem B2050495 : Blo 2049435 2050495 := bstep (se 1 (by rfl) ⟨1537871, by rfl⟩ : syracuseStep 2050495 = 3075743) B3075743
theorem B3075749 : Blo 2049435 3075749 := bbase (se 4 (by rfl) ⟨288351, by rfl⟩ : syracuseStep 3075749 = 576703) (by norm_num)
theorem B2050499 : Blo 2049435 2050499 := bstep (se 1 (by rfl) ⟨1537874, by rfl⟩ : syracuseStep 2050499 = 3075749) B3075749
theorem B2595169 : Blo 2049435 2595169 := bbase (se 2 (by rfl) ⟨973188, by rfl⟩ : syracuseStep 2595169 = 1946377) (by norm_num)
theorem B3460225 : Blo 2049435 3460225 := bstep (se 2 (by rfl) ⟨1297584, by rfl⟩ : syracuseStep 3460225 = 2595169) B2595169
theorem B4613633 : Blo 2049435 4613633 := bstep (se 2 (by rfl) ⟨1730112, by rfl⟩ : syracuseStep 4613633 = 3460225) B3460225
theorem B3075755 : Blo 2049435 3075755 := bstep (se 1 (by rfl) ⟨2306816, by rfl⟩ : syracuseStep 3075755 = 4613633) B4613633
theorem B2050503 : Blo 2049435 2050503 := bstep (se 1 (by rfl) ⟨1537877, by rfl⟩ : syracuseStep 2050503 = 3075755) B3075755
theorem B2306821 : Blo 2049435 2306821 := bbase (se 4 (by rfl) ⟨216264, by rfl⟩ : syracuseStep 2306821 = 432529) (by norm_num)
theorem B3075761 : Blo 2049435 3075761 := bstep (se 2 (by rfl) ⟨1153410, by rfl⟩ : syracuseStep 3075761 = 2306821) B2306821
theorem B2050507 : Blo 2049435 2050507 := bstep (se 1 (by rfl) ⟨1537880, by rfl⟩ : syracuseStep 2050507 = 3075761) B3075761
theorem B3284525 : Blo 2049435 3284525 := bbase (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) (by norm_num)
theorem B2189683 : Blo 2049435 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B2919577 : Blo 2049435 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B3892769 : Blo 2049435 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B2595179 : Blo 2049435 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B6920477 : Blo 2049435 6920477 := bstep (se 3 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 6920477 = 2595179) B2595179
theorem B4613651 : Blo 2049435 4613651 := bstep (se 1 (by rfl) ⟨3460238, by rfl⟩ : syracuseStep 4613651 = 6920477) B6920477
theorem B3075767 : Blo 2049435 3075767 := bstep (se 1 (by rfl) ⟨2306825, by rfl⟩ : syracuseStep 3075767 = 4613651) B4613651
theorem B2050511 : Blo 2049435 2050511 := bstep (se 1 (by rfl) ⟨1537883, by rfl⟩ : syracuseStep 2050511 = 3075767) B3075767
theorem B3075773 : Blo 2049435 3075773 := bbase (se 3 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 3075773 = 1153415) (by norm_num)
theorem B2050515 : Blo 2049435 2050515 := bstep (se 1 (by rfl) ⟨1537886, by rfl⟩ : syracuseStep 2050515 = 3075773) B3075773
theorem B4613669 : Blo 2049435 4613669 := bbase (se 4 (by rfl) ⟨432531, by rfl⟩ : syracuseStep 4613669 = 865063) (by norm_num)
theorem B3075779 : Blo 2049435 3075779 := bstep (se 1 (by rfl) ⟨2306834, by rfl⟩ : syracuseStep 3075779 = 4613669) B4613669
theorem B2050519 : Blo 2049435 2050519 := bstep (se 1 (by rfl) ⟨1537889, by rfl⟩ : syracuseStep 2050519 = 3075779) B3075779
theorem B5190389 : Blo 2049435 5190389 := bbase (se 5 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 5190389 = 486599) (by norm_num)
theorem B3460259 : Blo 2049435 3460259 := bstep (se 1 (by rfl) ⟨2595194, by rfl⟩ : syracuseStep 3460259 = 5190389) B5190389
theorem B2306839 : Blo 2049435 2306839 := bstep (se 1 (by rfl) ⟨1730129, by rfl⟩ : syracuseStep 2306839 = 3460259) B3460259
theorem B3075785 : Blo 2049435 3075785 := bstep (se 2 (by rfl) ⟨1153419, by rfl⟩ : syracuseStep 3075785 = 2306839) B2306839
theorem B2050523 : Blo 2049435 2050523 := bstep (se 1 (by rfl) ⟨1537892, by rfl⟩ : syracuseStep 2050523 = 3075785) B3075785
theorem B3117757 : Blo 2049435 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B4157009 : Blo 2049435 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B2771339 : Blo 2049435 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B29560949 : Blo 2049435 29560949 := bstep (se 5 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 29560949 = 2771339) B2771339
theorem B19707299 : Blo 2049435 19707299 := bstep (se 1 (by rfl) ⟨14780474, by rfl⟩ : syracuseStep 19707299 = 29560949) B29560949
theorem B13138199 : Blo 2049435 13138199 := bstep (se 1 (by rfl) ⟨9853649, by rfl⟩ : syracuseStep 13138199 = 19707299) B19707299
theorem B8758799 : Blo 2049435 8758799 := bstep (se 1 (by rfl) ⟨6569099, by rfl⟩ : syracuseStep 8758799 = 13138199) B13138199
theorem B5839199 : Blo 2049435 5839199 := bstep (se 1 (by rfl) ⟨4379399, by rfl⟩ : syracuseStep 5839199 = 8758799) B8758799
theorem B3892799 : Blo 2049435 3892799 := bstep (se 1 (by rfl) ⟨2919599, by rfl⟩ : syracuseStep 3892799 = 5839199) B5839199
theorem B10380797 : Blo 2049435 10380797 := bstep (se 3 (by rfl) ⟨1946399, by rfl⟩ : syracuseStep 10380797 = 3892799) B3892799
theorem B6920531 : Blo 2049435 6920531 := bstep (se 1 (by rfl) ⟨5190398, by rfl⟩ : syracuseStep 6920531 = 10380797) B10380797
theorem B4613687 : Blo 2049435 4613687 := bstep (se 1 (by rfl) ⟨3460265, by rfl⟩ : syracuseStep 4613687 = 6920531) B6920531
theorem B3075791 : Blo 2049435 3075791 := bstep (se 1 (by rfl) ⟨2306843, by rfl⟩ : syracuseStep 3075791 = 4613687) B4613687
theorem B2050527 : Blo 2049435 2050527 := bstep (se 1 (by rfl) ⟨1537895, by rfl⟩ : syracuseStep 2050527 = 3075791) B3075791
theorem B3075797 : Blo 2049435 3075797 := bbase (se 7 (by rfl) ⟨36044, by rfl⟩ : syracuseStep 3075797 = 72089) (by norm_num)
theorem B2050531 : Blo 2049435 2050531 := bstep (se 1 (by rfl) ⟨1537898, by rfl⟩ : syracuseStep 2050531 = 3075797) B3075797
theorem B4926845 : Blo 2049435 4926845 := bbase (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) (by norm_num)
theorem B3284563 : Blo 2049435 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B4379417 : Blo 2049435 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2919611 : Blo 2049435 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B7785629 : Blo 2049435 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B5190419 : Blo 2049435 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B3460279 : Blo 2049435 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B4613705 : Blo 2049435 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B3075803 : Blo 2049435 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B2050535 : Blo 2049435 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B2306857 : Blo 2049435 2306857 := bbase (se 2 (by rfl) ⟨865071, by rfl⟩ : syracuseStep 2306857 = 1730143) (by norm_num)
theorem B3075809 : Blo 2049435 3075809 := bstep (se 2 (by rfl) ⟨1153428, by rfl⟩ : syracuseStep 3075809 = 2306857) B2306857
theorem B2050539 : Blo 2049435 2050539 := bstep (se 1 (by rfl) ⟨1537904, by rfl⟩ : syracuseStep 2050539 = 3075809) B3075809
theorem B3117781 : Blo 2049435 3117781 := bbase (se 7 (by rfl) ⟨36536, by rfl⟩ : syracuseStep 3117781 = 73073) (by norm_num)
theorem B16628165 : Blo 2049435 16628165 := bstep (se 4 (by rfl) ⟨1558890, by rfl⟩ : syracuseStep 16628165 = 3117781) B3117781
theorem B11085443 : Blo 2049435 11085443 := bstep (se 1 (by rfl) ⟨8314082, by rfl⟩ : syracuseStep 11085443 = 16628165) B16628165
theorem B7390295 : Blo 2049435 7390295 := bstep (se 1 (by rfl) ⟨5542721, by rfl⟩ : syracuseStep 7390295 = 11085443) B11085443
theorem B4926863 : Blo 2049435 4926863 := bstep (se 1 (by rfl) ⟨3695147, by rfl⟩ : syracuseStep 4926863 = 7390295) B7390295
theorem B13138301 : Blo 2049435 13138301 := bstep (se 3 (by rfl) ⟨2463431, by rfl⟩ : syracuseStep 13138301 = 4926863) B4926863
theorem B8758867 : Blo 2049435 8758867 := bstep (se 1 (by rfl) ⟨6569150, by rfl⟩ : syracuseStep 8758867 = 13138301) B13138301
theorem B11678489 : Blo 2049435 11678489 := bstep (se 2 (by rfl) ⟨4379433, by rfl⟩ : syracuseStep 11678489 = 8758867) B8758867
theorem B7785659 : Blo 2049435 7785659 := bstep (se 1 (by rfl) ⟨5839244, by rfl⟩ : syracuseStep 7785659 = 11678489) B11678489
theorem B5190439 : Blo 2049435 5190439 := bstep (se 1 (by rfl) ⟨3892829, by rfl⟩ : syracuseStep 5190439 = 7785659) B7785659
theorem B6920585 : Blo 2049435 6920585 := bstep (se 2 (by rfl) ⟨2595219, by rfl⟩ : syracuseStep 6920585 = 5190439) B5190439
theorem B4613723 : Blo 2049435 4613723 := bstep (se 1 (by rfl) ⟨3460292, by rfl⟩ : syracuseStep 4613723 = 6920585) B6920585
theorem B3075815 : Blo 2049435 3075815 := bstep (se 1 (by rfl) ⟨2306861, by rfl⟩ : syracuseStep 3075815 = 4613723) B4613723
theorem B2050543 : Blo 2049435 2050543 := bstep (se 1 (by rfl) ⟨1537907, by rfl⟩ : syracuseStep 2050543 = 3075815) B3075815
theorem B3075821 : Blo 2049435 3075821 := bbase (se 3 (by rfl) ⟨576716, by rfl⟩ : syracuseStep 3075821 = 1153433) (by norm_num)
theorem B2050547 : Blo 2049435 2050547 := bstep (se 1 (by rfl) ⟨1537910, by rfl⟩ : syracuseStep 2050547 = 3075821) B3075821
theorem B4613741 : Blo 2049435 4613741 := bbase (se 3 (by rfl) ⟨865076, by rfl⟩ : syracuseStep 4613741 = 1730153) (by norm_num)
theorem B3075827 : Blo 2049435 3075827 := bstep (se 1 (by rfl) ⟨2306870, by rfl⟩ : syracuseStep 3075827 = 4613741) B4613741
theorem B2050551 : Blo 2049435 2050551 := bstep (se 1 (by rfl) ⟨1537913, by rfl⟩ : syracuseStep 2050551 = 3075827) B3075827
theorem B3892853 : Blo 2049435 3892853 := bbase (se 5 (by rfl) ⟨182477, by rfl⟩ : syracuseStep 3892853 = 364955) (by norm_num)
theorem B2595235 : Blo 2049435 2595235 := bstep (se 1 (by rfl) ⟨1946426, by rfl⟩ : syracuseStep 2595235 = 3892853) B3892853
theorem B3460313 : Blo 2049435 3460313 := bstep (se 2 (by rfl) ⟨1297617, by rfl⟩ : syracuseStep 3460313 = 2595235) B2595235
theorem B2306875 : Blo 2049435 2306875 := bstep (se 1 (by rfl) ⟨1730156, by rfl⟩ : syracuseStep 2306875 = 3460313) B3460313
theorem B3075833 : Blo 2049435 3075833 := bstep (se 2 (by rfl) ⟨1153437, by rfl⟩ : syracuseStep 3075833 = 2306875) B2306875
theorem B2050555 : Blo 2049435 2050555 := bstep (se 1 (by rfl) ⟨1537916, by rfl⟩ : syracuseStep 2050555 = 3075833) B3075833
theorem B7110773 : Blo 2049435 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B4740515 : Blo 2049435 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B3160343 : Blo 2049435 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B2106895 : Blo 2049435 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B2809193 : Blo 2049435 2809193 := bstep (se 2 (by rfl) ⟨1053447, by rfl⟩ : syracuseStep 2809193 = 2106895) B2106895
theorem B29964725 : Blo 2049435 29964725 := bstep (se 5 (by rfl) ⟨1404596, by rfl⟩ : syracuseStep 29964725 = 2809193) B2809193
theorem B19976483 : Blo 2049435 19976483 := bstep (se 1 (by rfl) ⟨14982362, by rfl⟩ : syracuseStep 19976483 = 29964725) B29964725
theorem B13317655 : Blo 2049435 13317655 := bstep (se 1 (by rfl) ⟨9988241, by rfl⟩ : syracuseStep 13317655 = 19976483) B19976483
theorem B17756873 : Blo 2049435 17756873 := bstep (se 2 (by rfl) ⟨6658827, by rfl⟩ : syracuseStep 17756873 = 13317655) B13317655
theorem B11837915 : Blo 2049435 11837915 := bstep (se 1 (by rfl) ⟨8878436, by rfl⟩ : syracuseStep 11837915 = 17756873) B17756873
theorem B7891943 : Blo 2049435 7891943 := bstep (se 1 (by rfl) ⟨5918957, by rfl⟩ : syracuseStep 7891943 = 11837915) B11837915
theorem B21045181 : Blo 2049435 21045181 := bstep (se 3 (by rfl) ⟨3945971, by rfl⟩ : syracuseStep 21045181 = 7891943) B7891943
theorem B28060241 : Blo 2049435 28060241 := bstep (se 2 (by rfl) ⟨10522590, by rfl⟩ : syracuseStep 28060241 = 21045181) B21045181
theorem B74827309 : Blo 2049435 74827309 := bstep (se 3 (by rfl) ⟨14030120, by rfl⟩ : syracuseStep 74827309 = 28060241) B28060241
theorem B99769745 : Blo 2049435 99769745 := bstep (se 2 (by rfl) ⟨37413654, by rfl⟩ : syracuseStep 99769745 = 74827309) B74827309
theorem B66513163 : Blo 2049435 66513163 := bstep (se 1 (by rfl) ⟨49884872, by rfl⟩ : syracuseStep 66513163 = 99769745) B99769745
theorem B88684217 : Blo 2049435 88684217 := bstep (se 2 (by rfl) ⟨33256581, by rfl⟩ : syracuseStep 88684217 = 66513163) B66513163
theorem B59122811 : Blo 2049435 59122811 := bstep (se 1 (by rfl) ⟨44342108, by rfl⟩ : syracuseStep 59122811 = 88684217) B88684217
theorem B39415207 : Blo 2049435 39415207 := bstep (se 1 (by rfl) ⟨29561405, by rfl⟩ : syracuseStep 39415207 = 59122811) B59122811
theorem B52553609 : Blo 2049435 52553609 := bstep (se 2 (by rfl) ⟨19707603, by rfl⟩ : syracuseStep 52553609 = 39415207) B39415207
theorem B35035739 : Blo 2049435 35035739 := bstep (se 1 (by rfl) ⟨26276804, by rfl⟩ : syracuseStep 35035739 = 52553609) B52553609
theorem B23357159 : Blo 2049435 23357159 := bstep (se 1 (by rfl) ⟨17517869, by rfl⟩ : syracuseStep 23357159 = 35035739) B35035739
theorem B15571439 : Blo 2049435 15571439 := bstep (se 1 (by rfl) ⟨11678579, by rfl⟩ : syracuseStep 15571439 = 23357159) B23357159
theorem B10380959 : Blo 2049435 10380959 := bstep (se 1 (by rfl) ⟨7785719, by rfl⟩ : syracuseStep 10380959 = 15571439) B15571439
theorem B6920639 : Blo 2049435 6920639 := bstep (se 1 (by rfl) ⟨5190479, by rfl⟩ : syracuseStep 6920639 = 10380959) B10380959
theorem B4613759 : Blo 2049435 4613759 := bstep (se 1 (by rfl) ⟨3460319, by rfl⟩ : syracuseStep 4613759 = 6920639) B6920639
theorem B3075839 : Blo 2049435 3075839 := bstep (se 1 (by rfl) ⟨2306879, by rfl⟩ : syracuseStep 3075839 = 4613759) B4613759
theorem B2050559 : Blo 2049435 2050559 := bstep (se 1 (by rfl) ⟨1537919, by rfl⟩ : syracuseStep 2050559 = 3075839) B3075839
theorem B3075845 : Blo 2049435 3075845 := bbase (se 4 (by rfl) ⟨288360, by rfl⟩ : syracuseStep 3075845 = 576721) (by norm_num)
theorem B2050563 : Blo 2049435 2050563 := bstep (se 1 (by rfl) ⟨1537922, by rfl⟩ : syracuseStep 2050563 = 3075845) B3075845
theorem B3460333 : Blo 2049435 3460333 := bbase (se 3 (by rfl) ⟨648812, by rfl⟩ : syracuseStep 3460333 = 1297625) (by norm_num)
theorem B4613777 : Blo 2049435 4613777 := bstep (se 2 (by rfl) ⟨1730166, by rfl⟩ : syracuseStep 4613777 = 3460333) B3460333
theorem B3075851 : Blo 2049435 3075851 := bstep (se 1 (by rfl) ⟨2306888, by rfl⟩ : syracuseStep 3075851 = 4613777) B4613777
theorem B2050567 : Blo 2049435 2050567 := bstep (se 1 (by rfl) ⟨1537925, by rfl⟩ : syracuseStep 2050567 = 3075851) B3075851
theorem B2306893 : Blo 2049435 2306893 := bbase (se 3 (by rfl) ⟨432542, by rfl⟩ : syracuseStep 2306893 = 865085) (by norm_num)
theorem B3075857 : Blo 2049435 3075857 := bstep (se 2 (by rfl) ⟨1153446, by rfl⟩ : syracuseStep 3075857 = 2306893) B2306893
theorem B2050571 : Blo 2049435 2050571 := bstep (se 1 (by rfl) ⟨1537928, by rfl⟩ : syracuseStep 2050571 = 3075857) B3075857
theorem B6920693 : Blo 2049435 6920693 := bbase (se 5 (by rfl) ⟨324407, by rfl⟩ : syracuseStep 6920693 = 648815) (by norm_num)
theorem B4613795 : Blo 2049435 4613795 := bstep (se 1 (by rfl) ⟨3460346, by rfl⟩ : syracuseStep 4613795 = 6920693) B6920693
theorem B3075863 : Blo 2049435 3075863 := bstep (se 1 (by rfl) ⟨2306897, by rfl⟩ : syracuseStep 3075863 = 4613795) B4613795
theorem B2050575 : Blo 2049435 2050575 := bstep (se 1 (by rfl) ⟨1537931, by rfl⟩ : syracuseStep 2050575 = 3075863) B3075863
theorem B3075869 : Blo 2049435 3075869 := bbase (se 3 (by rfl) ⟨576725, by rfl⟩ : syracuseStep 3075869 = 1153451) (by norm_num)
theorem B2050579 : Blo 2049435 2050579 := bstep (se 1 (by rfl) ⟨1537934, by rfl⟩ : syracuseStep 2050579 = 3075869) B3075869
theorem B4613813 : Blo 2049435 4613813 := bbase (se 5 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 4613813 = 432545) (by norm_num)
theorem B3075875 : Blo 2049435 3075875 := bstep (se 1 (by rfl) ⟨2306906, by rfl⟩ : syracuseStep 3075875 = 4613813) B4613813
theorem B2050583 : Blo 2049435 2050583 := bstep (se 1 (by rfl) ⟨1537937, by rfl⟩ : syracuseStep 2050583 = 3075875) B3075875
theorem B11678741 : Blo 2049435 11678741 := bbase (se 6 (by rfl) ⟨273720, by rfl⟩ : syracuseStep 11678741 = 547441) (by norm_num)
theorem B7785827 : Blo 2049435 7785827 := bstep (se 1 (by rfl) ⟨5839370, by rfl⟩ : syracuseStep 7785827 = 11678741) B11678741
theorem B5190551 : Blo 2049435 5190551 := bstep (se 1 (by rfl) ⟨3892913, by rfl⟩ : syracuseStep 5190551 = 7785827) B7785827
theorem B3460367 : Blo 2049435 3460367 := bstep (se 1 (by rfl) ⟨2595275, by rfl⟩ : syracuseStep 3460367 = 5190551) B5190551
theorem B2306911 : Blo 2049435 2306911 := bstep (se 1 (by rfl) ⟨1730183, by rfl⟩ : syracuseStep 2306911 = 3460367) B3460367
theorem B3075881 : Blo 2049435 3075881 := bstep (se 2 (by rfl) ⟨1153455, by rfl⟩ : syracuseStep 3075881 = 2306911) B2306911
theorem B2050587 : Blo 2049435 2050587 := bstep (se 1 (by rfl) ⟨1537940, by rfl⟩ : syracuseStep 2050587 = 3075881) B3075881
theorem B5839381 : Blo 2049435 5839381 := bbase (se 6 (by rfl) ⟨136860, by rfl⟩ : syracuseStep 5839381 = 273721) (by norm_num)
theorem B7785841 : Blo 2049435 7785841 := bstep (se 2 (by rfl) ⟨2919690, by rfl⟩ : syracuseStep 7785841 = 5839381) B5839381
theorem B10381121 : Blo 2049435 10381121 := bstep (se 2 (by rfl) ⟨3892920, by rfl⟩ : syracuseStep 10381121 = 7785841) B7785841
theorem B6920747 : Blo 2049435 6920747 := bstep (se 1 (by rfl) ⟨5190560, by rfl⟩ : syracuseStep 6920747 = 10381121) B10381121
theorem B4613831 : Blo 2049435 4613831 := bstep (se 1 (by rfl) ⟨3460373, by rfl⟩ : syracuseStep 4613831 = 6920747) B6920747
theorem B3075887 : Blo 2049435 3075887 := bstep (se 1 (by rfl) ⟨2306915, by rfl⟩ : syracuseStep 3075887 = 4613831) B4613831
theorem B2050591 : Blo 2049435 2050591 := bstep (se 1 (by rfl) ⟨1537943, by rfl⟩ : syracuseStep 2050591 = 3075887) B3075887
theorem B3075893 : Blo 2049435 3075893 := bbase (se 5 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 3075893 = 288365) (by norm_num)
theorem B2050595 : Blo 2049435 2050595 := bstep (se 1 (by rfl) ⟨1537946, by rfl⟩ : syracuseStep 2050595 = 3075893) B3075893
theorem B5190581 : Blo 2049435 5190581 := bbase (se 5 (by rfl) ⟨243308, by rfl⟩ : syracuseStep 5190581 = 486617) (by norm_num)
theorem B3460387 : Blo 2049435 3460387 := bstep (se 1 (by rfl) ⟨2595290, by rfl⟩ : syracuseStep 3460387 = 5190581) B5190581
theorem B4613849 : Blo 2049435 4613849 := bstep (se 2 (by rfl) ⟨1730193, by rfl⟩ : syracuseStep 4613849 = 3460387) B3460387
theorem B3075899 : Blo 2049435 3075899 := bstep (se 1 (by rfl) ⟨2306924, by rfl⟩ : syracuseStep 3075899 = 4613849) B4613849
theorem B2050599 : Blo 2049435 2050599 := bstep (se 1 (by rfl) ⟨1537949, by rfl⟩ : syracuseStep 2050599 = 3075899) B3075899
theorem B2306929 : Blo 2049435 2306929 := bbase (se 2 (by rfl) ⟨865098, by rfl⟩ : syracuseStep 2306929 = 1730197) (by norm_num)
theorem B3075905 : Blo 2049435 3075905 := bstep (se 2 (by rfl) ⟨1153464, by rfl⟩ : syracuseStep 3075905 = 2306929) B2306929
theorem B2050603 : Blo 2049435 2050603 := bstep (se 1 (by rfl) ⟨1537952, by rfl⟩ : syracuseStep 2050603 = 3075905) B3075905
theorem B8759141 : Blo 2049435 8759141 := bbase (se 4 (by rfl) ⟨821169, by rfl⟩ : syracuseStep 8759141 = 1642339) (by norm_num)
theorem B5839427 : Blo 2049435 5839427 := bstep (se 1 (by rfl) ⟨4379570, by rfl⟩ : syracuseStep 5839427 = 8759141) B8759141
theorem B3892951 : Blo 2049435 3892951 := bstep (se 1 (by rfl) ⟨2919713, by rfl⟩ : syracuseStep 3892951 = 5839427) B5839427
theorem B5190601 : Blo 2049435 5190601 := bstep (se 2 (by rfl) ⟨1946475, by rfl⟩ : syracuseStep 5190601 = 3892951) B3892951
theorem B6920801 : Blo 2049435 6920801 := bstep (se 2 (by rfl) ⟨2595300, by rfl⟩ : syracuseStep 6920801 = 5190601) B5190601
theorem B4613867 : Blo 2049435 4613867 := bstep (se 1 (by rfl) ⟨3460400, by rfl⟩ : syracuseStep 4613867 = 6920801) B6920801
theorem B3075911 : Blo 2049435 3075911 := bstep (se 1 (by rfl) ⟨2306933, by rfl⟩ : syracuseStep 3075911 = 4613867) B4613867
theorem B2050607 : Blo 2049435 2050607 := bstep (se 1 (by rfl) ⟨1537955, by rfl⟩ : syracuseStep 2050607 = 3075911) B3075911
theorem B3075917 : Blo 2049435 3075917 := bbase (se 3 (by rfl) ⟨576734, by rfl⟩ : syracuseStep 3075917 = 1153469) (by norm_num)
theorem B2050611 : Blo 2049435 2050611 := bstep (se 1 (by rfl) ⟨1537958, by rfl⟩ : syracuseStep 2050611 = 3075917) B3075917
theorem B4613885 : Blo 2049435 4613885 := bbase (se 3 (by rfl) ⟨865103, by rfl⟩ : syracuseStep 4613885 = 1730207) (by norm_num)
theorem B3075923 : Blo 2049435 3075923 := bstep (se 1 (by rfl) ⟨2306942, by rfl⟩ : syracuseStep 3075923 = 4613885) B4613885
theorem B2050615 : Blo 2049435 2050615 := bstep (se 1 (by rfl) ⟨1537961, by rfl⟩ : syracuseStep 2050615 = 3075923) B3075923
theorem B3460421 : Blo 2049435 3460421 := bbase (se 4 (by rfl) ⟨324414, by rfl⟩ : syracuseStep 3460421 = 648829) (by norm_num)
theorem B2306947 : Blo 2049435 2306947 := bstep (se 1 (by rfl) ⟨1730210, by rfl⟩ : syracuseStep 2306947 = 3460421) B3460421
theorem B3075929 : Blo 2049435 3075929 := bstep (se 2 (by rfl) ⟨1153473, by rfl⟩ : syracuseStep 3075929 = 2306947) B2306947
theorem B2050619 : Blo 2049435 2050619 := bstep (se 1 (by rfl) ⟨1537964, by rfl⟩ : syracuseStep 2050619 = 3075929) B3075929
theorem B15571925 : Blo 2049435 15571925 := bbase (se 7 (by rfl) ⟨182483, by rfl⟩ : syracuseStep 15571925 = 364967) (by norm_num)
theorem B10381283 : Blo 2049435 10381283 := bstep (se 1 (by rfl) ⟨7785962, by rfl⟩ : syracuseStep 10381283 = 15571925) B15571925
theorem B6920855 : Blo 2049435 6920855 := bstep (se 1 (by rfl) ⟨5190641, by rfl⟩ : syracuseStep 6920855 = 10381283) B10381283
theorem B4613903 : Blo 2049435 4613903 := bstep (se 1 (by rfl) ⟨3460427, by rfl⟩ : syracuseStep 4613903 = 6920855) B6920855
theorem B3075935 : Blo 2049435 3075935 := bstep (se 1 (by rfl) ⟨2306951, by rfl⟩ : syracuseStep 3075935 = 4613903) B4613903
theorem B2050623 : Blo 2049435 2050623 := bstep (se 1 (by rfl) ⟨1537967, by rfl⟩ : syracuseStep 2050623 = 3075935) B3075935
theorem B3075941 : Blo 2049435 3075941 := bbase (se 4 (by rfl) ⟨288369, by rfl⟩ : syracuseStep 3075941 = 576739) (by norm_num)
theorem B2050627 : Blo 2049435 2050627 := bstep (se 1 (by rfl) ⟨1537970, by rfl⟩ : syracuseStep 2050627 = 3075941) B3075941
theorem B3892997 : Blo 2049435 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B2595331 : Blo 2049435 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B3460441 : Blo 2049435 3460441 := bstep (se 2 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 3460441 = 2595331) B2595331
theorem B4613921 : Blo 2049435 4613921 := bstep (se 2 (by rfl) ⟨1730220, by rfl⟩ : syracuseStep 4613921 = 3460441) B3460441
theorem B3075947 : Blo 2049435 3075947 := bstep (se 1 (by rfl) ⟨2306960, by rfl⟩ : syracuseStep 3075947 = 4613921) B4613921
theorem B2050631 : Blo 2049435 2050631 := bstep (se 1 (by rfl) ⟨1537973, by rfl⟩ : syracuseStep 2050631 = 3075947) B3075947
theorem B2306965 : Blo 2049435 2306965 := bbase (se 6 (by rfl) ⟨54069, by rfl⟩ : syracuseStep 2306965 = 108139) (by norm_num)
theorem B3075953 : Blo 2049435 3075953 := bstep (se 2 (by rfl) ⟨1153482, by rfl⟩ : syracuseStep 3075953 = 2306965) B2306965
theorem B2050635 : Blo 2049435 2050635 := bstep (se 1 (by rfl) ⟨1537976, by rfl⟩ : syracuseStep 2050635 = 3075953) B3075953
theorem B2595341 : Blo 2049435 2595341 := bbase (se 3 (by rfl) ⟨486626, by rfl⟩ : syracuseStep 2595341 = 973253) (by norm_num)
theorem B6920909 : Blo 2049435 6920909 := bstep (se 3 (by rfl) ⟨1297670, by rfl⟩ : syracuseStep 6920909 = 2595341) B2595341
theorem B4613939 : Blo 2049435 4613939 := bstep (se 1 (by rfl) ⟨3460454, by rfl⟩ : syracuseStep 4613939 = 6920909) B6920909
theorem B3075959 : Blo 2049435 3075959 := bstep (se 1 (by rfl) ⟨2306969, by rfl⟩ : syracuseStep 3075959 = 4613939) B4613939
theorem B2050639 : Blo 2049435 2050639 := bstep (se 1 (by rfl) ⟨1537979, by rfl⟩ : syracuseStep 2050639 = 3075959) B3075959
theorem B3075965 : Blo 2049435 3075965 := bbase (se 3 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 3075965 = 1153487) (by norm_num)
theorem B2050643 : Blo 2049435 2050643 := bstep (se 1 (by rfl) ⟨1537982, by rfl⟩ : syracuseStep 2050643 = 3075965) B3075965
theorem B4613957 : Blo 2049435 4613957 := bbase (se 4 (by rfl) ⟨432558, by rfl⟩ : syracuseStep 4613957 = 865117) (by norm_num)
theorem B3075971 : Blo 2049435 3075971 := bstep (se 1 (by rfl) ⟨2306978, by rfl⟩ : syracuseStep 3075971 = 4613957) B4613957
theorem B2050647 : Blo 2049435 2050647 := bstep (se 1 (by rfl) ⟨1537985, by rfl⟩ : syracuseStep 2050647 = 3075971) B3075971
theorem B3284749 : Blo 2049435 3284749 := bbase (se 3 (by rfl) ⟨615890, by rfl⟩ : syracuseStep 3284749 = 1231781) (by norm_num)
theorem B4379665 : Blo 2049435 4379665 := bstep (se 2 (by rfl) ⟨1642374, by rfl⟩ : syracuseStep 4379665 = 3284749) B3284749
theorem B5839553 : Blo 2049435 5839553 := bstep (se 2 (by rfl) ⟨2189832, by rfl⟩ : syracuseStep 5839553 = 4379665) B4379665
theorem B3893035 : Blo 2049435 3893035 := bstep (se 1 (by rfl) ⟨2919776, by rfl⟩ : syracuseStep 3893035 = 5839553) B5839553
theorem B5190713 : Blo 2049435 5190713 := bstep (se 2 (by rfl) ⟨1946517, by rfl⟩ : syracuseStep 5190713 = 3893035) B3893035
theorem B3460475 : Blo 2049435 3460475 := bstep (se 1 (by rfl) ⟨2595356, by rfl⟩ : syracuseStep 3460475 = 5190713) B5190713
theorem B2306983 : Blo 2049435 2306983 := bstep (se 1 (by rfl) ⟨1730237, by rfl⟩ : syracuseStep 2306983 = 3460475) B3460475
theorem B3075977 : Blo 2049435 3075977 := bstep (se 2 (by rfl) ⟨1153491, by rfl⟩ : syracuseStep 3075977 = 2306983) B2306983
theorem B2050651 : Blo 2049435 2050651 := bstep (se 1 (by rfl) ⟨1537988, by rfl⟩ : syracuseStep 2050651 = 3075977) B3075977
theorem B10381445 : Blo 2049435 10381445 := bbase (se 4 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 10381445 = 1946521) (by norm_num)
theorem B6920963 : Blo 2049435 6920963 := bstep (se 1 (by rfl) ⟨5190722, by rfl⟩ : syracuseStep 6920963 = 10381445) B10381445
theorem B4613975 : Blo 2049435 4613975 := bstep (se 1 (by rfl) ⟨3460481, by rfl⟩ : syracuseStep 4613975 = 6920963) B6920963
theorem B3075983 : Blo 2049435 3075983 := bstep (se 1 (by rfl) ⟨2306987, by rfl⟩ : syracuseStep 3075983 = 4613975) B4613975
theorem B2050655 : Blo 2049435 2050655 := bstep (se 1 (by rfl) ⟨1537991, by rfl⟩ : syracuseStep 2050655 = 3075983) B3075983
theorem B3075989 : Blo 2049435 3075989 := bbase (se 6 (by rfl) ⟨72093, by rfl⟩ : syracuseStep 3075989 = 144187) (by norm_num)
theorem B2050659 : Blo 2049435 2050659 := bstep (se 1 (by rfl) ⟨1537994, by rfl⟩ : syracuseStep 2050659 = 3075989) B3075989
theorem B2189845 : Blo 2049435 2189845 := bbase (se 6 (by rfl) ⟨51324, by rfl⟩ : syracuseStep 2189845 = 102649) (by norm_num)
theorem B11679173 : Blo 2049435 11679173 := bstep (se 4 (by rfl) ⟨1094922, by rfl⟩ : syracuseStep 11679173 = 2189845) B2189845
theorem B7786115 : Blo 2049435 7786115 := bstep (se 1 (by rfl) ⟨5839586, by rfl⟩ : syracuseStep 7786115 = 11679173) B11679173
theorem B5190743 : Blo 2049435 5190743 := bstep (se 1 (by rfl) ⟨3893057, by rfl⟩ : syracuseStep 5190743 = 7786115) B7786115
theorem B3460495 : Blo 2049435 3460495 := bstep (se 1 (by rfl) ⟨2595371, by rfl⟩ : syracuseStep 3460495 = 5190743) B5190743
theorem B4613993 : Blo 2049435 4613993 := bstep (se 2 (by rfl) ⟨1730247, by rfl⟩ : syracuseStep 4613993 = 3460495) B3460495
theorem B3075995 : Blo 2049435 3075995 := bstep (se 1 (by rfl) ⟨2306996, by rfl⟩ : syracuseStep 3075995 = 4613993) B4613993
theorem B2050663 : Blo 2049435 2050663 := bstep (se 1 (by rfl) ⟨1537997, by rfl⟩ : syracuseStep 2050663 = 3075995) B3075995
theorem B2307001 : Blo 2049435 2307001 := bbase (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) (by norm_num)
theorem B3076001 : Blo 2049435 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B2050667 : Blo 2049435 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B7390757 : Blo 2049435 7390757 := bbase (se 4 (by rfl) ⟨692883, by rfl⟩ : syracuseStep 7390757 = 1385767) (by norm_num)
theorem B4927171 : Blo 2049435 4927171 := bstep (se 1 (by rfl) ⟨3695378, by rfl⟩ : syracuseStep 4927171 = 7390757) B7390757
theorem B6569561 : Blo 2049435 6569561 := bstep (se 2 (by rfl) ⟨2463585, by rfl⟩ : syracuseStep 6569561 = 4927171) B4927171
theorem B4379707 : Blo 2049435 4379707 := bstep (se 1 (by rfl) ⟨3284780, by rfl⟩ : syracuseStep 4379707 = 6569561) B6569561
theorem B5839609 : Blo 2049435 5839609 := bstep (se 2 (by rfl) ⟨2189853, by rfl⟩ : syracuseStep 5839609 = 4379707) B4379707
theorem B7786145 : Blo 2049435 7786145 := bstep (se 2 (by rfl) ⟨2919804, by rfl⟩ : syracuseStep 7786145 = 5839609) B5839609
theorem B5190763 : Blo 2049435 5190763 := bstep (se 1 (by rfl) ⟨3893072, by rfl⟩ : syracuseStep 5190763 = 7786145) B7786145
theorem B6921017 : Blo 2049435 6921017 := bstep (se 2 (by rfl) ⟨2595381, by rfl⟩ : syracuseStep 6921017 = 5190763) B5190763
theorem B4614011 : Blo 2049435 4614011 := bstep (se 1 (by rfl) ⟨3460508, by rfl⟩ : syracuseStep 4614011 = 6921017) B6921017
theorem B3076007 : Blo 2049435 3076007 := bstep (se 1 (by rfl) ⟨2307005, by rfl⟩ : syracuseStep 3076007 = 4614011) B4614011
theorem B2050671 : Blo 2049435 2050671 := bstep (se 1 (by rfl) ⟨1538003, by rfl⟩ : syracuseStep 2050671 = 3076007) B3076007
theorem B3076013 : Blo 2049435 3076013 := bbase (se 3 (by rfl) ⟨576752, by rfl⟩ : syracuseStep 3076013 = 1153505) (by norm_num)
theorem B2050675 : Blo 2049435 2050675 := bstep (se 1 (by rfl) ⟨1538006, by rfl⟩ : syracuseStep 2050675 = 3076013) B3076013
theorem B4614029 : Blo 2049435 4614029 := bbase (se 3 (by rfl) ⟨865130, by rfl⟩ : syracuseStep 4614029 = 1730261) (by norm_num)
theorem B3076019 : Blo 2049435 3076019 := bstep (se 1 (by rfl) ⟨2307014, by rfl⟩ : syracuseStep 3076019 = 4614029) B4614029
theorem B2050679 : Blo 2049435 2050679 := bstep (se 1 (by rfl) ⟨1538009, by rfl⟩ : syracuseStep 2050679 = 3076019) B3076019
theorem B2595397 : Blo 2049435 2595397 := bbase (se 4 (by rfl) ⟨243318, by rfl⟩ : syracuseStep 2595397 = 486637) (by norm_num)
theorem B3460529 : Blo 2049435 3460529 := bstep (se 2 (by rfl) ⟨1297698, by rfl⟩ : syracuseStep 3460529 = 2595397) B2595397
theorem B2307019 : Blo 2049435 2307019 := bstep (se 1 (by rfl) ⟨1730264, by rfl⟩ : syracuseStep 2307019 = 3460529) B3460529
theorem B3076025 : Blo 2049435 3076025 := bstep (se 2 (by rfl) ⟨1153509, by rfl⟩ : syracuseStep 3076025 = 2307019) B2307019
theorem B2050683 : Blo 2049435 2050683 := bstep (se 1 (by rfl) ⟨1538012, by rfl⟩ : syracuseStep 2050683 = 3076025) B3076025
theorem B4157333 : Blo 2049435 4157333 := bbase (se 6 (by rfl) ⟨97437, by rfl⟩ : syracuseStep 4157333 = 194875) (by norm_num)
theorem B2771555 : Blo 2049435 2771555 := bstep (se 1 (by rfl) ⟨2078666, by rfl⟩ : syracuseStep 2771555 = 4157333) B4157333
theorem B7390813 : Blo 2049435 7390813 := bstep (se 3 (by rfl) ⟨1385777, by rfl⟩ : syracuseStep 7390813 = 2771555) B2771555
theorem B9854417 : Blo 2049435 9854417 := bstep (se 2 (by rfl) ⟨3695406, by rfl⟩ : syracuseStep 9854417 = 7390813) B7390813
theorem B26278445 : Blo 2049435 26278445 := bstep (se 3 (by rfl) ⟨4927208, by rfl⟩ : syracuseStep 26278445 = 9854417) B9854417
theorem B17518963 : Blo 2049435 17518963 := bstep (se 1 (by rfl) ⟨13139222, by rfl⟩ : syracuseStep 17518963 = 26278445) B26278445
theorem B23358617 : Blo 2049435 23358617 := bstep (se 2 (by rfl) ⟨8759481, by rfl⟩ : syracuseStep 23358617 = 17518963) B17518963
theorem B15572411 : Blo 2049435 15572411 := bstep (se 1 (by rfl) ⟨11679308, by rfl⟩ : syracuseStep 15572411 = 23358617) B23358617
theorem B10381607 : Blo 2049435 10381607 := bstep (se 1 (by rfl) ⟨7786205, by rfl⟩ : syracuseStep 10381607 = 15572411) B15572411
theorem B6921071 : Blo 2049435 6921071 := bstep (se 1 (by rfl) ⟨5190803, by rfl⟩ : syracuseStep 6921071 = 10381607) B10381607
theorem B4614047 : Blo 2049435 4614047 := bstep (se 1 (by rfl) ⟨3460535, by rfl⟩ : syracuseStep 4614047 = 6921071) B6921071
theorem B3076031 : Blo 2049435 3076031 := bstep (se 1 (by rfl) ⟨2307023, by rfl⟩ : syracuseStep 3076031 = 4614047) B4614047
theorem B2050687 : Blo 2049435 2050687 := bstep (se 1 (by rfl) ⟨1538015, by rfl⟩ : syracuseStep 2050687 = 3076031) B3076031
theorem B3076037 : Blo 2049435 3076037 := bbase (se 4 (by rfl) ⟨288378, by rfl⟩ : syracuseStep 3076037 = 576757) (by norm_num)
theorem B2050691 : Blo 2049435 2050691 := bstep (se 1 (by rfl) ⟨1538018, by rfl⟩ : syracuseStep 2050691 = 3076037) B3076037
theorem B3460549 : Blo 2049435 3460549 := bbase (se 4 (by rfl) ⟨324426, by rfl⟩ : syracuseStep 3460549 = 648853) (by norm_num)
theorem B4614065 : Blo 2049435 4614065 := bstep (se 2 (by rfl) ⟨1730274, by rfl⟩ : syracuseStep 4614065 = 3460549) B3460549
theorem B3076043 : Blo 2049435 3076043 := bstep (se 1 (by rfl) ⟨2307032, by rfl⟩ : syracuseStep 3076043 = 4614065) B4614065
theorem B2050695 : Blo 2049435 2050695 := bstep (se 1 (by rfl) ⟨1538021, by rfl⟩ : syracuseStep 2050695 = 3076043) B3076043
theorem B2307037 : Blo 2049435 2307037 := bbase (se 3 (by rfl) ⟨432569, by rfl⟩ : syracuseStep 2307037 = 865139) (by norm_num)
theorem B3076049 : Blo 2049435 3076049 := bstep (se 2 (by rfl) ⟨1153518, by rfl⟩ : syracuseStep 3076049 = 2307037) B2307037
theorem B2050699 : Blo 2049435 2050699 := bstep (se 1 (by rfl) ⟨1538024, by rfl⟩ : syracuseStep 2050699 = 3076049) B3076049
theorem B6921125 : Blo 2049435 6921125 := bbase (se 4 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 6921125 = 1297711) (by norm_num)
theorem B4614083 : Blo 2049435 4614083 := bstep (se 1 (by rfl) ⟨3460562, by rfl⟩ : syracuseStep 4614083 = 6921125) B6921125
theorem B3076055 : Blo 2049435 3076055 := bstep (se 1 (by rfl) ⟨2307041, by rfl⟩ : syracuseStep 3076055 = 4614083) B4614083
theorem B2050703 : Blo 2049435 2050703 := bstep (se 1 (by rfl) ⟨1538027, by rfl⟩ : syracuseStep 2050703 = 3076055) B3076055
theorem B3076061 : Blo 2049435 3076061 := bbase (se 3 (by rfl) ⟨576761, by rfl⟩ : syracuseStep 3076061 = 1153523) (by norm_num)
theorem B2050707 : Blo 2049435 2050707 := bstep (se 1 (by rfl) ⟨1538030, by rfl⟩ : syracuseStep 2050707 = 3076061) B3076061
theorem B4614101 : Blo 2049435 4614101 := bbase (se 7 (by rfl) ⟨54071, by rfl⟩ : syracuseStep 4614101 = 108143) (by norm_num)
theorem B3076067 : Blo 2049435 3076067 := bstep (se 1 (by rfl) ⟨2307050, by rfl⟩ : syracuseStep 3076067 = 4614101) B4614101
theorem B2050711 : Blo 2049435 2050711 := bstep (se 1 (by rfl) ⟨1538033, by rfl⟩ : syracuseStep 2050711 = 3076067) B3076067
theorem B4927277 : Blo 2049435 4927277 := bbase (se 3 (by rfl) ⟨923864, by rfl⟩ : syracuseStep 4927277 = 1847729) (by norm_num)
theorem B13139405 : Blo 2049435 13139405 := bstep (se 3 (by rfl) ⟨2463638, by rfl⟩ : syracuseStep 13139405 = 4927277) B4927277
theorem B8759603 : Blo 2049435 8759603 := bstep (se 1 (by rfl) ⟨6569702, by rfl⟩ : syracuseStep 8759603 = 13139405) B13139405
theorem B5839735 : Blo 2049435 5839735 := bstep (se 1 (by rfl) ⟨4379801, by rfl⟩ : syracuseStep 5839735 = 8759603) B8759603
theorem B7786313 : Blo 2049435 7786313 := bstep (se 2 (by rfl) ⟨2919867, by rfl⟩ : syracuseStep 7786313 = 5839735) B5839735
theorem B5190875 : Blo 2049435 5190875 := bstep (se 1 (by rfl) ⟨3893156, by rfl⟩ : syracuseStep 5190875 = 7786313) B7786313
theorem B3460583 : Blo 2049435 3460583 := bstep (se 1 (by rfl) ⟨2595437, by rfl⟩ : syracuseStep 3460583 = 5190875) B5190875
theorem B2307055 : Blo 2049435 2307055 := bstep (se 1 (by rfl) ⟨1730291, by rfl⟩ : syracuseStep 2307055 = 3460583) B3460583
theorem B3076073 : Blo 2049435 3076073 := bstep (se 2 (by rfl) ⟨1153527, by rfl⟩ : syracuseStep 3076073 = 2307055) B2307055
theorem B2050715 : Blo 2049435 2050715 := bstep (se 1 (by rfl) ⟨1538036, by rfl⟩ : syracuseStep 2050715 = 3076073) B3076073
theorem B9354149 : Blo 2049435 9354149 := bbase (se 4 (by rfl) ⟨876951, by rfl⟩ : syracuseStep 9354149 = 1753903) (by norm_num)
theorem B6236099 : Blo 2049435 6236099 := bstep (se 1 (by rfl) ⟨4677074, by rfl⟩ : syracuseStep 6236099 = 9354149) B9354149
theorem B4157399 : Blo 2049435 4157399 := bstep (se 1 (by rfl) ⟨3118049, by rfl⟩ : syracuseStep 4157399 = 6236099) B6236099
theorem B2771599 : Blo 2049435 2771599 := bstep (se 1 (by rfl) ⟨2078699, by rfl⟩ : syracuseStep 2771599 = 4157399) B4157399
theorem B3695465 : Blo 2049435 3695465 := bstep (se 2 (by rfl) ⟨1385799, by rfl⟩ : syracuseStep 3695465 = 2771599) B2771599
theorem B2463643 : Blo 2049435 2463643 := bstep (se 1 (by rfl) ⟨1847732, by rfl⟩ : syracuseStep 2463643 = 3695465) B3695465
theorem B3284857 : Blo 2049435 3284857 := bstep (se 2 (by rfl) ⟨1231821, by rfl⟩ : syracuseStep 3284857 = 2463643) B2463643
theorem B17519237 : Blo 2049435 17519237 := bstep (se 4 (by rfl) ⟨1642428, by rfl⟩ : syracuseStep 17519237 = 3284857) B3284857
theorem B11679491 : Blo 2049435 11679491 := bstep (se 1 (by rfl) ⟨8759618, by rfl⟩ : syracuseStep 11679491 = 17519237) B17519237
theorem B7786327 : Blo 2049435 7786327 := bstep (se 1 (by rfl) ⟨5839745, by rfl⟩ : syracuseStep 7786327 = 11679491) B11679491
theorem B10381769 : Blo 2049435 10381769 := bstep (se 2 (by rfl) ⟨3893163, by rfl⟩ : syracuseStep 10381769 = 7786327) B7786327
theorem B6921179 : Blo 2049435 6921179 := bstep (se 1 (by rfl) ⟨5190884, by rfl⟩ : syracuseStep 6921179 = 10381769) B10381769
theorem B4614119 : Blo 2049435 4614119 := bstep (se 1 (by rfl) ⟨3460589, by rfl⟩ : syracuseStep 4614119 = 6921179) B6921179
theorem B3076079 : Blo 2049435 3076079 := bstep (se 1 (by rfl) ⟨2307059, by rfl⟩ : syracuseStep 3076079 = 4614119) B4614119
theorem B2050719 : Blo 2049435 2050719 := bstep (se 1 (by rfl) ⟨1538039, by rfl⟩ : syracuseStep 2050719 = 3076079) B3076079
theorem B3076085 : Blo 2049435 3076085 := bbase (se 5 (by rfl) ⟨144191, by rfl⟩ : syracuseStep 3076085 = 288383) (by norm_num)
theorem B2050723 : Blo 2049435 2050723 := bstep (se 1 (by rfl) ⟨1538042, by rfl⟩ : syracuseStep 2050723 = 3076085) B3076085
theorem B2463653 : Blo 2049435 2463653 := bbase (se 4 (by rfl) ⟨230967, by rfl⟩ : syracuseStep 2463653 = 461935) (by norm_num)
theorem B6569741 : Blo 2049435 6569741 := bstep (se 3 (by rfl) ⟨1231826, by rfl⟩ : syracuseStep 6569741 = 2463653) B2463653
theorem B4379827 : Blo 2049435 4379827 := bstep (se 1 (by rfl) ⟨3284870, by rfl⟩ : syracuseStep 4379827 = 6569741) B6569741
theorem B5839769 : Blo 2049435 5839769 := bstep (se 2 (by rfl) ⟨2189913, by rfl⟩ : syracuseStep 5839769 = 4379827) B4379827
theorem B3893179 : Blo 2049435 3893179 := bstep (se 1 (by rfl) ⟨2919884, by rfl⟩ : syracuseStep 3893179 = 5839769) B5839769
theorem B5190905 : Blo 2049435 5190905 := bstep (se 2 (by rfl) ⟨1946589, by rfl⟩ : syracuseStep 5190905 = 3893179) B3893179
theorem B3460603 : Blo 2049435 3460603 := bstep (se 1 (by rfl) ⟨2595452, by rfl⟩ : syracuseStep 3460603 = 5190905) B5190905
theorem B4614137 : Blo 2049435 4614137 := bstep (se 2 (by rfl) ⟨1730301, by rfl⟩ : syracuseStep 4614137 = 3460603) B3460603
theorem B3076091 : Blo 2049435 3076091 := bstep (se 1 (by rfl) ⟨2307068, by rfl⟩ : syracuseStep 3076091 = 4614137) B4614137
theorem B2050727 : Blo 2049435 2050727 := bstep (se 1 (by rfl) ⟨1538045, by rfl⟩ : syracuseStep 2050727 = 3076091) B3076091
theorem B2307073 : Blo 2049435 2307073 := bbase (se 2 (by rfl) ⟨865152, by rfl⟩ : syracuseStep 2307073 = 1730305) (by norm_num)
theorem B3076097 : Blo 2049435 3076097 := bstep (se 2 (by rfl) ⟨1153536, by rfl⟩ : syracuseStep 3076097 = 2307073) B2307073
theorem B2050731 : Blo 2049435 2050731 := bstep (se 1 (by rfl) ⟨1538048, by rfl⟩ : syracuseStep 2050731 = 3076097) B3076097
theorem B5190925 : Blo 2049435 5190925 := bbase (se 3 (by rfl) ⟨973298, by rfl⟩ : syracuseStep 5190925 = 1946597) (by norm_num)
theorem B6921233 : Blo 2049435 6921233 := bstep (se 2 (by rfl) ⟨2595462, by rfl⟩ : syracuseStep 6921233 = 5190925) B5190925
theorem B4614155 : Blo 2049435 4614155 := bstep (se 1 (by rfl) ⟨3460616, by rfl⟩ : syracuseStep 4614155 = 6921233) B6921233
theorem B3076103 : Blo 2049435 3076103 := bstep (se 1 (by rfl) ⟨2307077, by rfl⟩ : syracuseStep 3076103 = 4614155) B4614155
theorem B2050735 : Blo 2049435 2050735 := bstep (se 1 (by rfl) ⟨1538051, by rfl⟩ : syracuseStep 2050735 = 3076103) B3076103
theorem B3076109 : Blo 2049435 3076109 := bbase (se 3 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 3076109 = 1153541) (by norm_num)
theorem B2050739 : Blo 2049435 2050739 := bstep (se 1 (by rfl) ⟨1538054, by rfl⟩ : syracuseStep 2050739 = 3076109) B3076109
theorem B4614173 : Blo 2049435 4614173 := bbase (se 3 (by rfl) ⟨865157, by rfl⟩ : syracuseStep 4614173 = 1730315) (by norm_num)
theorem B3076115 : Blo 2049435 3076115 := bstep (se 1 (by rfl) ⟨2307086, by rfl⟩ : syracuseStep 3076115 = 4614173) B4614173
theorem B2050743 : Blo 2049435 2050743 := bstep (se 1 (by rfl) ⟨1538057, by rfl⟩ : syracuseStep 2050743 = 3076115) B3076115
theorem B3460637 : Blo 2049435 3460637 := bbase (se 3 (by rfl) ⟨648869, by rfl⟩ : syracuseStep 3460637 = 1297739) (by norm_num)
theorem B2307091 : Blo 2049435 2307091 := bstep (se 1 (by rfl) ⟨1730318, by rfl⟩ : syracuseStep 2307091 = 3460637) B3460637
theorem B3076121 : Blo 2049435 3076121 := bstep (se 2 (by rfl) ⟨1153545, by rfl⟩ : syracuseStep 3076121 = 2307091) B2307091
theorem B2050747 : Blo 2049435 2050747 := bstep (se 1 (by rfl) ⟨1538060, by rfl⟩ : syracuseStep 2050747 = 3076121) B3076121
theorem B9854725 : Blo 2049435 9854725 := bbase (se 4 (by rfl) ⟨923880, by rfl⟩ : syracuseStep 9854725 = 1847761) (by norm_num)
theorem B13139633 : Blo 2049435 13139633 := bstep (se 2 (by rfl) ⟨4927362, by rfl⟩ : syracuseStep 13139633 = 9854725) B9854725
theorem B8759755 : Blo 2049435 8759755 := bstep (se 1 (by rfl) ⟨6569816, by rfl⟩ : syracuseStep 8759755 = 13139633) B13139633
theorem B11679673 : Blo 2049435 11679673 := bstep (se 2 (by rfl) ⟨4379877, by rfl⟩ : syracuseStep 11679673 = 8759755) B8759755
theorem B15572897 : Blo 2049435 15572897 := bstep (se 2 (by rfl) ⟨5839836, by rfl⟩ : syracuseStep 15572897 = 11679673) B11679673
theorem B10381931 : Blo 2049435 10381931 := bstep (se 1 (by rfl) ⟨7786448, by rfl⟩ : syracuseStep 10381931 = 15572897) B15572897
theorem B6921287 : Blo 2049435 6921287 := bstep (se 1 (by rfl) ⟨5190965, by rfl⟩ : syracuseStep 6921287 = 10381931) B10381931
theorem B4614191 : Blo 2049435 4614191 := bstep (se 1 (by rfl) ⟨3460643, by rfl⟩ : syracuseStep 4614191 = 6921287) B6921287
theorem B3076127 : Blo 2049435 3076127 := bstep (se 1 (by rfl) ⟨2307095, by rfl⟩ : syracuseStep 3076127 = 4614191) B4614191
theorem B2050751 : Blo 2049435 2050751 := bstep (se 1 (by rfl) ⟨1538063, by rfl⟩ : syracuseStep 2050751 = 3076127) B3076127
theorem B3076133 : Blo 2049435 3076133 := bbase (se 4 (by rfl) ⟨288387, by rfl⟩ : syracuseStep 3076133 = 576775) (by norm_num)
theorem B2050755 : Blo 2049435 2050755 := bstep (se 1 (by rfl) ⟨1538066, by rfl⟩ : syracuseStep 2050755 = 3076133) B3076133
theorem B2595493 : Blo 2049435 2595493 := bbase (se 4 (by rfl) ⟨243327, by rfl⟩ : syracuseStep 2595493 = 486655) (by norm_num)
theorem B3460657 : Blo 2049435 3460657 := bstep (se 2 (by rfl) ⟨1297746, by rfl⟩ : syracuseStep 3460657 = 2595493) B2595493
theorem B4614209 : Blo 2049435 4614209 := bstep (se 2 (by rfl) ⟨1730328, by rfl⟩ : syracuseStep 4614209 = 3460657) B3460657
theorem B3076139 : Blo 2049435 3076139 := bstep (se 1 (by rfl) ⟨2307104, by rfl⟩ : syracuseStep 3076139 = 4614209) B4614209
theorem B2050759 : Blo 2049435 2050759 := bstep (se 1 (by rfl) ⟨1538069, by rfl⟩ : syracuseStep 2050759 = 3076139) B3076139
theorem B2307109 : Blo 2049435 2307109 := bbase (se 4 (by rfl) ⟨216291, by rfl⟩ : syracuseStep 2307109 = 432583) (by norm_num)
theorem B3076145 : Blo 2049435 3076145 := bstep (se 2 (by rfl) ⟨1153554, by rfl⟩ : syracuseStep 3076145 = 2307109) B2307109
theorem B2050763 : Blo 2049435 2050763 := bstep (se 1 (by rfl) ⟨1538072, by rfl⟩ : syracuseStep 2050763 = 3076145) B3076145
theorem B2463701 : Blo 2049435 2463701 := bbase (se 7 (by rfl) ⟨28871, by rfl⟩ : syracuseStep 2463701 = 57743) (by norm_num)
theorem B6569869 : Blo 2049435 6569869 := bstep (se 3 (by rfl) ⟨1231850, by rfl⟩ : syracuseStep 6569869 = 2463701) B2463701
theorem B8759825 : Blo 2049435 8759825 := bstep (se 2 (by rfl) ⟨3284934, by rfl⟩ : syracuseStep 8759825 = 6569869) B6569869
theorem B5839883 : Blo 2049435 5839883 := bstep (se 1 (by rfl) ⟨4379912, by rfl⟩ : syracuseStep 5839883 = 8759825) B8759825
theorem B3893255 : Blo 2049435 3893255 := bstep (se 1 (by rfl) ⟨2919941, by rfl⟩ : syracuseStep 3893255 = 5839883) B5839883
theorem B2595503 : Blo 2049435 2595503 := bstep (se 1 (by rfl) ⟨1946627, by rfl⟩ : syracuseStep 2595503 = 3893255) B3893255
theorem B6921341 : Blo 2049435 6921341 := bstep (se 3 (by rfl) ⟨1297751, by rfl⟩ : syracuseStep 6921341 = 2595503) B2595503
theorem B4614227 : Blo 2049435 4614227 := bstep (se 1 (by rfl) ⟨3460670, by rfl⟩ : syracuseStep 4614227 = 6921341) B6921341
theorem B3076151 : Blo 2049435 3076151 := bstep (se 1 (by rfl) ⟨2307113, by rfl⟩ : syracuseStep 3076151 = 4614227) B4614227
theorem B2050767 : Blo 2049435 2050767 := bstep (se 1 (by rfl) ⟨1538075, by rfl⟩ : syracuseStep 2050767 = 3076151) B3076151
theorem B3076157 : Blo 2049435 3076157 := bbase (se 3 (by rfl) ⟨576779, by rfl⟩ : syracuseStep 3076157 = 1153559) (by norm_num)
theorem B2050771 : Blo 2049435 2050771 := bstep (se 1 (by rfl) ⟨1538078, by rfl⟩ : syracuseStep 2050771 = 3076157) B3076157
theorem B4614245 : Blo 2049435 4614245 := bbase (se 4 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 4614245 = 865171) (by norm_num)
theorem B3076163 : Blo 2049435 3076163 := bstep (se 1 (by rfl) ⟨2307122, by rfl⟩ : syracuseStep 3076163 = 4614245) B4614245
theorem B2050775 : Blo 2049435 2050775 := bstep (se 1 (by rfl) ⟨1538081, by rfl⟩ : syracuseStep 2050775 = 3076163) B3076163
theorem B5191037 : Blo 2049435 5191037 := bbase (se 3 (by rfl) ⟨973319, by rfl⟩ : syracuseStep 5191037 = 1946639) (by norm_num)
theorem B3460691 : Blo 2049435 3460691 := bstep (se 1 (by rfl) ⟨2595518, by rfl⟩ : syracuseStep 3460691 = 5191037) B5191037
theorem B2307127 : Blo 2049435 2307127 := bstep (se 1 (by rfl) ⟨1730345, by rfl⟩ : syracuseStep 2307127 = 3460691) B3460691
theorem B3076169 : Blo 2049435 3076169 := bstep (se 2 (by rfl) ⟨1153563, by rfl⟩ : syracuseStep 3076169 = 2307127) B2307127
theorem B2050779 : Blo 2049435 2050779 := bstep (se 1 (by rfl) ⟨1538084, by rfl⟩ : syracuseStep 2050779 = 3076169) B3076169
theorem B3893285 : Blo 2049435 3893285 := bbase (se 4 (by rfl) ⟨364995, by rfl⟩ : syracuseStep 3893285 = 729991) (by norm_num)
theorem B10382093 : Blo 2049435 10382093 := bstep (se 3 (by rfl) ⟨1946642, by rfl⟩ : syracuseStep 10382093 = 3893285) B3893285
theorem B6921395 : Blo 2049435 6921395 := bstep (se 1 (by rfl) ⟨5191046, by rfl⟩ : syracuseStep 6921395 = 10382093) B10382093
theorem B4614263 : Blo 2049435 4614263 := bstep (se 1 (by rfl) ⟨3460697, by rfl⟩ : syracuseStep 4614263 = 6921395) B6921395
theorem B3076175 : Blo 2049435 3076175 := bstep (se 1 (by rfl) ⟨2307131, by rfl⟩ : syracuseStep 3076175 = 4614263) B4614263
theorem B2050783 : Blo 2049435 2050783 := bstep (se 1 (by rfl) ⟨1538087, by rfl⟩ : syracuseStep 2050783 = 3076175) B3076175
theorem B3076181 : Blo 2049435 3076181 := bbase (se 8 (by rfl) ⟨18024, by rfl⟩ : syracuseStep 3076181 = 36049) (by norm_num)
theorem B2050787 : Blo 2049435 2050787 := bstep (se 1 (by rfl) ⟨1538090, by rfl⟩ : syracuseStep 2050787 = 3076181) B3076181
theorem B7391189 : Blo 2049435 7391189 := bbase (se 7 (by rfl) ⟨86615, by rfl⟩ : syracuseStep 7391189 = 173231) (by norm_num)
theorem B19709837 : Blo 2049435 19709837 := bstep (se 3 (by rfl) ⟨3695594, by rfl⟩ : syracuseStep 19709837 = 7391189) B7391189
theorem B13139891 : Blo 2049435 13139891 := bstep (se 1 (by rfl) ⟨9854918, by rfl⟩ : syracuseStep 13139891 = 19709837) B19709837
theorem B8759927 : Blo 2049435 8759927 := bstep (se 1 (by rfl) ⟨6569945, by rfl⟩ : syracuseStep 8759927 = 13139891) B13139891
theorem B5839951 : Blo 2049435 5839951 := bstep (se 1 (by rfl) ⟨4379963, by rfl⟩ : syracuseStep 5839951 = 8759927) B8759927
theorem B7786601 : Blo 2049435 7786601 := bstep (se 2 (by rfl) ⟨2919975, by rfl⟩ : syracuseStep 7786601 = 5839951) B5839951
theorem B5191067 : Blo 2049435 5191067 := bstep (se 1 (by rfl) ⟨3893300, by rfl⟩ : syracuseStep 5191067 = 7786601) B7786601
theorem B3460711 : Blo 2049435 3460711 := bstep (se 1 (by rfl) ⟨2595533, by rfl⟩ : syracuseStep 3460711 = 5191067) B5191067
theorem B4614281 : Blo 2049435 4614281 := bstep (se 2 (by rfl) ⟨1730355, by rfl⟩ : syracuseStep 4614281 = 3460711) B3460711
theorem B3076187 : Blo 2049435 3076187 := bstep (se 1 (by rfl) ⟨2307140, by rfl⟩ : syracuseStep 3076187 = 4614281) B4614281
theorem B2050791 : Blo 2049435 2050791 := bstep (se 1 (by rfl) ⟨1538093, by rfl⟩ : syracuseStep 2050791 = 3076187) B3076187
theorem B2307145 : Blo 2049435 2307145 := bbase (se 2 (by rfl) ⟨865179, by rfl⟩ : syracuseStep 2307145 = 1730359) (by norm_num)
theorem B3076193 : Blo 2049435 3076193 := bstep (se 2 (by rfl) ⟨1153572, by rfl⟩ : syracuseStep 3076193 = 2307145) B2307145
theorem B2050795 : Blo 2049435 2050795 := bstep (se 1 (by rfl) ⟨1538096, by rfl⟩ : syracuseStep 2050795 = 3076193) B3076193
theorem B3555805 : Blo 2049435 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B4741073 : Blo 2049435 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B3160715 : Blo 2049435 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B8428573 : Blo 2049435 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B11238097 : Blo 2049435 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B14984129 : Blo 2049435 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B9989419 : Blo 2049435 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B13319225 : Blo 2049435 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B8879483 : Blo 2049435 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B5919655 : Blo 2049435 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B7892873 : Blo 2049435 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B5261915 : Blo 2049435 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B3507943 : Blo 2049435 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B4677257 : Blo 2049435 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B3118171 : Blo 2049435 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B4157561 : Blo 2049435 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B2771707 : Blo 2049435 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B3695609 : Blo 2049435 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B2463739 : Blo 2049435 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B13139941 : Blo 2049435 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B17519921 : Blo 2049435 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B11679947 : Blo 2049435 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B7786631 : Blo 2049435 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B5191087 : Blo 2049435 5191087 := bstep (se 1 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 5191087 = 7786631) B7786631
theorem B6921449 : Blo 2049435 6921449 := bstep (se 2 (by rfl) ⟨2595543, by rfl⟩ : syracuseStep 6921449 = 5191087) B5191087
theorem B4614299 : Blo 2049435 4614299 := bstep (se 1 (by rfl) ⟨3460724, by rfl⟩ : syracuseStep 4614299 = 6921449) B6921449
theorem B3076199 : Blo 2049435 3076199 := bstep (se 1 (by rfl) ⟨2307149, by rfl⟩ : syracuseStep 3076199 = 4614299) B4614299
theorem B2050799 : Blo 2049435 2050799 := bstep (se 1 (by rfl) ⟨1538099, by rfl⟩ : syracuseStep 2050799 = 3076199) B3076199
theorem B3076205 : Blo 2049435 3076205 := bbase (se 3 (by rfl) ⟨576788, by rfl⟩ : syracuseStep 3076205 = 1153577) (by norm_num)
theorem B2050803 : Blo 2049435 2050803 := bstep (se 1 (by rfl) ⟨1538102, by rfl⟩ : syracuseStep 2050803 = 3076205) B3076205
theorem B4614317 : Blo 2049435 4614317 := bbase (se 3 (by rfl) ⟨865184, by rfl⟩ : syracuseStep 4614317 = 1730369) (by norm_num)
theorem B3076211 : Blo 2049435 3076211 := bstep (se 1 (by rfl) ⟨2307158, by rfl⟩ : syracuseStep 3076211 = 4614317) B4614317
theorem B2050807 : Blo 2049435 2050807 := bstep (se 1 (by rfl) ⟨1538105, by rfl⟩ : syracuseStep 2050807 = 3076211) B3076211
theorem B31571669 : Blo 2049435 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B21047779 : Blo 2049435 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B28063705 : Blo 2049435 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B37418273 : Blo 2049435 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B24945515 : Blo 2049435 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B16630343 : Blo 2049435 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B11086895 : Blo 2049435 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B7391263 : Blo 2049435 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B9855017 : Blo 2049435 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B6570011 : Blo 2049435 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B4380007 : Blo 2049435 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B5840009 : Blo 2049435 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B3893339 : Blo 2049435 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B2595559 : Blo 2049435 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B3460745 : Blo 2049435 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B2307163 : Blo 2049435 2307163 := bstep (se 1 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 2307163 = 3460745) B3460745
theorem B3076217 : Blo 2049435 3076217 := bstep (se 2 (by rfl) ⟨1153581, by rfl⟩ : syracuseStep 3076217 = 2307163) B2307163
theorem B2050811 : Blo 2049435 2050811 := bstep (se 1 (by rfl) ⟨1538108, by rfl⟩ : syracuseStep 2050811 = 3076217) B3076217
theorem B26280085 : Blo 2049435 26280085 := bbase (se 6 (by rfl) ⟨615939, by rfl⟩ : syracuseStep 26280085 = 1231879) (by norm_num)
theorem B35040113 : Blo 2049435 35040113 := bstep (se 2 (by rfl) ⟨13140042, by rfl⟩ : syracuseStep 35040113 = 26280085) B26280085
theorem B23360075 : Blo 2049435 23360075 := bstep (se 1 (by rfl) ⟨17520056, by rfl⟩ : syracuseStep 23360075 = 35040113) B35040113
theorem B15573383 : Blo 2049435 15573383 := bstep (se 1 (by rfl) ⟨11680037, by rfl⟩ : syracuseStep 15573383 = 23360075) B23360075
theorem B10382255 : Blo 2049435 10382255 := bstep (se 1 (by rfl) ⟨7786691, by rfl⟩ : syracuseStep 10382255 = 15573383) B15573383
theorem B6921503 : Blo 2049435 6921503 := bstep (se 1 (by rfl) ⟨5191127, by rfl⟩ : syracuseStep 6921503 = 10382255) B10382255
theorem B4614335 : Blo 2049435 4614335 := bstep (se 1 (by rfl) ⟨3460751, by rfl⟩ : syracuseStep 4614335 = 6921503) B6921503
theorem B3076223 : Blo 2049435 3076223 := bstep (se 1 (by rfl) ⟨2307167, by rfl⟩ : syracuseStep 3076223 = 4614335) B4614335
theorem B2050815 : Blo 2049435 2050815 := bstep (se 1 (by rfl) ⟨1538111, by rfl⟩ : syracuseStep 2050815 = 3076223) B3076223
theorem B3076229 : Blo 2049435 3076229 := bbase (se 4 (by rfl) ⟨288396, by rfl⟩ : syracuseStep 3076229 = 576793) (by norm_num)
theorem B2050819 : Blo 2049435 2050819 := bstep (se 1 (by rfl) ⟨1538114, by rfl⟩ : syracuseStep 2050819 = 3076229) B3076229
theorem B3460765 : Blo 2049435 3460765 := bbase (se 3 (by rfl) ⟨648893, by rfl⟩ : syracuseStep 3460765 = 1297787) (by norm_num)
theorem B4614353 : Blo 2049435 4614353 := bstep (se 2 (by rfl) ⟨1730382, by rfl⟩ : syracuseStep 4614353 = 3460765) B3460765
theorem B3076235 : Blo 2049435 3076235 := bstep (se 1 (by rfl) ⟨2307176, by rfl⟩ : syracuseStep 3076235 = 4614353) B4614353
theorem B2050823 : Blo 2049435 2050823 := bstep (se 1 (by rfl) ⟨1538117, by rfl⟩ : syracuseStep 2050823 = 3076235) B3076235
theorem B2307181 : Blo 2049435 2307181 := bbase (se 3 (by rfl) ⟨432596, by rfl⟩ : syracuseStep 2307181 = 865193) (by norm_num)
theorem B3076241 : Blo 2049435 3076241 := bstep (se 2 (by rfl) ⟨1153590, by rfl⟩ : syracuseStep 3076241 = 2307181) B2307181
theorem B2050827 : Blo 2049435 2050827 := bstep (se 1 (by rfl) ⟨1538120, by rfl⟩ : syracuseStep 2050827 = 3076241) B3076241
theorem B6921557 : Blo 2049435 6921557 := bbase (se 11 (by rfl) ⟨5069, by rfl⟩ : syracuseStep 6921557 = 10139) (by norm_num)
theorem B4614371 : Blo 2049435 4614371 := bstep (se 1 (by rfl) ⟨3460778, by rfl⟩ : syracuseStep 4614371 = 6921557) B6921557
theorem B3076247 : Blo 2049435 3076247 := bstep (se 1 (by rfl) ⟨2307185, by rfl⟩ : syracuseStep 3076247 = 4614371) B4614371
theorem B2050831 : Blo 2049435 2050831 := bstep (se 1 (by rfl) ⟨1538123, by rfl⟩ : syracuseStep 2050831 = 3076247) B3076247
theorem B3076253 : Blo 2049435 3076253 := bbase (se 3 (by rfl) ⟨576797, by rfl⟩ : syracuseStep 3076253 = 1153595) (by norm_num)
theorem B2050835 : Blo 2049435 2050835 := bstep (se 1 (by rfl) ⟨1538126, by rfl⟩ : syracuseStep 2050835 = 3076253) B3076253
theorem B4614389 : Blo 2049435 4614389 := bbase (se 5 (by rfl) ⟨216299, by rfl⟩ : syracuseStep 4614389 = 432599) (by norm_num)
theorem B3076259 : Blo 2049435 3076259 := bstep (se 1 (by rfl) ⟨2307194, by rfl⟩ : syracuseStep 3076259 = 4614389) B4614389
theorem B2050839 : Blo 2049435 2050839 := bstep (se 1 (by rfl) ⟨1538129, by rfl⟩ : syracuseStep 2050839 = 3076259) B3076259
theorem B12472949 : Blo 2049435 12472949 := bbase (se 5 (by rfl) ⟨584669, by rfl⟩ : syracuseStep 12472949 = 1169339) (by norm_num)
theorem B8315299 : Blo 2049435 8315299 := bstep (se 1 (by rfl) ⟨6236474, by rfl⟩ : syracuseStep 8315299 = 12472949) B12472949
theorem B11087065 : Blo 2049435 11087065 := bstep (se 2 (by rfl) ⟨4157649, by rfl⟩ : syracuseStep 11087065 = 8315299) B8315299
theorem B14782753 : Blo 2049435 14782753 := bstep (se 2 (by rfl) ⟨5543532, by rfl⟩ : syracuseStep 14782753 = 11087065) B11087065
theorem B19710337 : Blo 2049435 19710337 := bstep (se 2 (by rfl) ⟨7391376, by rfl⟩ : syracuseStep 19710337 = 14782753) B14782753
theorem B26280449 : Blo 2049435 26280449 := bstep (se 2 (by rfl) ⟨9855168, by rfl⟩ : syracuseStep 26280449 = 19710337) B19710337
theorem B17520299 : Blo 2049435 17520299 := bstep (se 1 (by rfl) ⟨13140224, by rfl⟩ : syracuseStep 17520299 = 26280449) B26280449
theorem B11680199 : Blo 2049435 11680199 := bstep (se 1 (by rfl) ⟨8760149, by rfl⟩ : syracuseStep 11680199 = 17520299) B17520299
theorem B7786799 : Blo 2049435 7786799 := bstep (se 1 (by rfl) ⟨5840099, by rfl⟩ : syracuseStep 7786799 = 11680199) B11680199
theorem B5191199 : Blo 2049435 5191199 := bstep (se 1 (by rfl) ⟨3893399, by rfl⟩ : syracuseStep 5191199 = 7786799) B7786799
theorem B3460799 : Blo 2049435 3460799 := bstep (se 1 (by rfl) ⟨2595599, by rfl⟩ : syracuseStep 3460799 = 5191199) B5191199
theorem B2307199 : Blo 2049435 2307199 := bstep (se 1 (by rfl) ⟨1730399, by rfl⟩ : syracuseStep 2307199 = 3460799) B3460799
theorem B3076265 : Blo 2049435 3076265 := bstep (se 2 (by rfl) ⟨1153599, by rfl⟩ : syracuseStep 3076265 = 2307199) B2307199
theorem B2050843 : Blo 2049435 2050843 := bstep (se 1 (by rfl) ⟨1538132, by rfl⟩ : syracuseStep 2050843 = 3076265) B3076265
theorem B2463797 : Blo 2049435 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B6570125 : Blo 2049435 6570125 := bstep (se 3 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 6570125 = 2463797) B2463797
theorem B4380083 : Blo 2049435 4380083 := bstep (se 1 (by rfl) ⟨3285062, by rfl⟩ : syracuseStep 4380083 = 6570125) B6570125
theorem B2920055 : Blo 2049435 2920055 := bstep (se 1 (by rfl) ⟨2190041, by rfl⟩ : syracuseStep 2920055 = 4380083) B4380083
theorem B7786813 : Blo 2049435 7786813 := bstep (se 3 (by rfl) ⟨1460027, by rfl⟩ : syracuseStep 7786813 = 2920055) B2920055
theorem B10382417 : Blo 2049435 10382417 := bstep (se 2 (by rfl) ⟨3893406, by rfl⟩ : syracuseStep 10382417 = 7786813) B7786813
theorem B6921611 : Blo 2049435 6921611 := bstep (se 1 (by rfl) ⟨5191208, by rfl⟩ : syracuseStep 6921611 = 10382417) B10382417
theorem B4614407 : Blo 2049435 4614407 := bstep (se 1 (by rfl) ⟨3460805, by rfl⟩ : syracuseStep 4614407 = 6921611) B6921611
theorem B3076271 : Blo 2049435 3076271 := bstep (se 1 (by rfl) ⟨2307203, by rfl⟩ : syracuseStep 3076271 = 4614407) B4614407
theorem B2050847 : Blo 2049435 2050847 := bstep (se 1 (by rfl) ⟨1538135, by rfl⟩ : syracuseStep 2050847 = 3076271) B3076271
theorem B3076277 : Blo 2049435 3076277 := bbase (se 5 (by rfl) ⟨144200, by rfl⟩ : syracuseStep 3076277 = 288401) (by norm_num)
theorem B2050851 : Blo 2049435 2050851 := bstep (se 1 (by rfl) ⟨1538138, by rfl⟩ : syracuseStep 2050851 = 3076277) B3076277
theorem B5191229 : Blo 2049435 5191229 := bbase (se 3 (by rfl) ⟨973355, by rfl⟩ : syracuseStep 5191229 = 1946711) (by norm_num)
theorem B3460819 : Blo 2049435 3460819 := bstep (se 1 (by rfl) ⟨2595614, by rfl⟩ : syracuseStep 3460819 = 5191229) B5191229
theorem B4614425 : Blo 2049435 4614425 := bstep (se 2 (by rfl) ⟨1730409, by rfl⟩ : syracuseStep 4614425 = 3460819) B3460819
theorem B3076283 : Blo 2049435 3076283 := bstep (se 1 (by rfl) ⟨2307212, by rfl⟩ : syracuseStep 3076283 = 4614425) B4614425
theorem B2050855 : Blo 2049435 2050855 := bstep (se 1 (by rfl) ⟨1538141, by rfl⟩ : syracuseStep 2050855 = 3076283) B3076283
theorem B2307217 : Blo 2049435 2307217 := bbase (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) (by norm_num)
theorem B3076289 : Blo 2049435 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B2050859 : Blo 2049435 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B3893437 : Blo 2049435 3893437 := bbase (se 3 (by rfl) ⟨730019, by rfl⟩ : syracuseStep 3893437 = 1460039) (by norm_num)
theorem B5191249 : Blo 2049435 5191249 := bstep (se 2 (by rfl) ⟨1946718, by rfl⟩ : syracuseStep 5191249 = 3893437) B3893437
theorem B6921665 : Blo 2049435 6921665 := bstep (se 2 (by rfl) ⟨2595624, by rfl⟩ : syracuseStep 6921665 = 5191249) B5191249
theorem B4614443 : Blo 2049435 4614443 := bstep (se 1 (by rfl) ⟨3460832, by rfl⟩ : syracuseStep 4614443 = 6921665) B6921665
theorem B3076295 : Blo 2049435 3076295 := bstep (se 1 (by rfl) ⟨2307221, by rfl⟩ : syracuseStep 3076295 = 4614443) B4614443
theorem B2050863 : Blo 2049435 2050863 := bstep (se 1 (by rfl) ⟨1538147, by rfl⟩ : syracuseStep 2050863 = 3076295) B3076295
theorem B3076301 : Blo 2049435 3076301 := bbase (se 3 (by rfl) ⟨576806, by rfl⟩ : syracuseStep 3076301 = 1153613) (by norm_num)
theorem B2050867 : Blo 2049435 2050867 := bstep (se 1 (by rfl) ⟨1538150, by rfl⟩ : syracuseStep 2050867 = 3076301) B3076301
theorem B4614461 : Blo 2049435 4614461 := bbase (se 3 (by rfl) ⟨865211, by rfl⟩ : syracuseStep 4614461 = 1730423) (by norm_num)
theorem B3076307 : Blo 2049435 3076307 := bstep (se 1 (by rfl) ⟨2307230, by rfl⟩ : syracuseStep 3076307 = 4614461) B4614461
theorem B2050871 : Blo 2049435 2050871 := bstep (se 1 (by rfl) ⟨1538153, by rfl⟩ : syracuseStep 2050871 = 3076307) B3076307
theorem B3460853 : Blo 2049435 3460853 := bbase (se 5 (by rfl) ⟨162227, by rfl⟩ : syracuseStep 3460853 = 324455) (by norm_num)
theorem B2307235 : Blo 2049435 2307235 := bstep (se 1 (by rfl) ⟨1730426, by rfl⟩ : syracuseStep 2307235 = 3460853) B3460853
theorem B3076313 : Blo 2049435 3076313 := bstep (se 2 (by rfl) ⟨1153617, by rfl⟩ : syracuseStep 3076313 = 2307235) B2307235
theorem B2050875 : Blo 2049435 2050875 := bstep (se 1 (by rfl) ⟨1538156, by rfl⟩ : syracuseStep 2050875 = 3076313) B3076313
theorem B2107225 : Blo 2049435 2107225 := bbase (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) (by norm_num)
theorem B11238533 : Blo 2049435 11238533 := bstep (se 4 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 11238533 = 2107225) B2107225
theorem B7492355 : Blo 2049435 7492355 := bstep (se 1 (by rfl) ⟨5619266, by rfl⟩ : syracuseStep 7492355 = 11238533) B11238533
theorem B4994903 : Blo 2049435 4994903 := bstep (se 1 (by rfl) ⟨3746177, by rfl⟩ : syracuseStep 4994903 = 7492355) B7492355
theorem B13319741 : Blo 2049435 13319741 := bstep (se 3 (by rfl) ⟨2497451, by rfl⟩ : syracuseStep 13319741 = 4994903) B4994903
theorem B35519309 : Blo 2049435 35519309 := bstep (se 3 (by rfl) ⟨6659870, by rfl⟩ : syracuseStep 35519309 = 13319741) B13319741
theorem B23679539 : Blo 2049435 23679539 := bstep (se 1 (by rfl) ⟨17759654, by rfl⟩ : syracuseStep 23679539 = 35519309) B35519309
theorem B15786359 : Blo 2049435 15786359 := bstep (se 1 (by rfl) ⟨11839769, by rfl⟩ : syracuseStep 15786359 = 23679539) B23679539
theorem B10524239 : Blo 2049435 10524239 := bstep (se 1 (by rfl) ⟨7893179, by rfl⟩ : syracuseStep 10524239 = 15786359) B15786359
theorem B7016159 : Blo 2049435 7016159 := bstep (se 1 (by rfl) ⟨5262119, by rfl⟩ : syracuseStep 7016159 = 10524239) B10524239
theorem B4677439 : Blo 2049435 4677439 := bstep (se 1 (by rfl) ⟨3508079, by rfl⟩ : syracuseStep 4677439 = 7016159) B7016159
theorem B6236585 : Blo 2049435 6236585 := bstep (se 2 (by rfl) ⟨2338719, by rfl⟩ : syracuseStep 6236585 = 4677439) B4677439
theorem B4157723 : Blo 2049435 4157723 := bstep (se 1 (by rfl) ⟨3118292, by rfl⟩ : syracuseStep 4157723 = 6236585) B6236585
theorem B2771815 : Blo 2049435 2771815 := bstep (se 1 (by rfl) ⟨2078861, by rfl⟩ : syracuseStep 2771815 = 4157723) B4157723
theorem B3695753 : Blo 2049435 3695753 := bstep (se 2 (by rfl) ⟨1385907, by rfl⟩ : syracuseStep 3695753 = 2771815) B2771815
theorem B9855341 : Blo 2049435 9855341 := bstep (se 3 (by rfl) ⟨1847876, by rfl⟩ : syracuseStep 9855341 = 3695753) B3695753
theorem B6570227 : Blo 2049435 6570227 := bstep (se 1 (by rfl) ⟨4927670, by rfl⟩ : syracuseStep 6570227 = 9855341) B9855341
theorem B4380151 : Blo 2049435 4380151 := bstep (se 1 (by rfl) ⟨3285113, by rfl⟩ : syracuseStep 4380151 = 6570227) B6570227
theorem B5840201 : Blo 2049435 5840201 := bstep (se 2 (by rfl) ⟨2190075, by rfl⟩ : syracuseStep 5840201 = 4380151) B4380151
theorem B15573869 : Blo 2049435 15573869 := bstep (se 3 (by rfl) ⟨2920100, by rfl⟩ : syracuseStep 15573869 = 5840201) B5840201
theorem B10382579 : Blo 2049435 10382579 := bstep (se 1 (by rfl) ⟨7786934, by rfl⟩ : syracuseStep 10382579 = 15573869) B15573869
theorem B6921719 : Blo 2049435 6921719 := bstep (se 1 (by rfl) ⟨5191289, by rfl⟩ : syracuseStep 6921719 = 10382579) B10382579
theorem B4614479 : Blo 2049435 4614479 := bstep (se 1 (by rfl) ⟨3460859, by rfl⟩ : syracuseStep 4614479 = 6921719) B6921719
theorem B3076319 : Blo 2049435 3076319 := bstep (se 1 (by rfl) ⟨2307239, by rfl⟩ : syracuseStep 3076319 = 4614479) B4614479
theorem B2050879 : Blo 2049435 2050879 := bstep (se 1 (by rfl) ⟨1538159, by rfl⟩ : syracuseStep 2050879 = 3076319) B3076319
theorem B3076325 : Blo 2049435 3076325 := bbase (se 4 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 3076325 = 576811) (by norm_num)
theorem B2050883 : Blo 2049435 2050883 := bstep (se 1 (by rfl) ⟨1538162, by rfl⟩ : syracuseStep 2050883 = 3076325) B3076325
theorem B5543653 : Blo 2049435 5543653 := bbase (se 4 (by rfl) ⟨519717, by rfl⟩ : syracuseStep 5543653 = 1039435) (by norm_num)
theorem B7391537 : Blo 2049435 7391537 := bstep (se 2 (by rfl) ⟨2771826, by rfl⟩ : syracuseStep 7391537 = 5543653) B5543653
theorem B4927691 : Blo 2049435 4927691 := bstep (se 1 (by rfl) ⟨3695768, by rfl⟩ : syracuseStep 4927691 = 7391537) B7391537
theorem B3285127 : Blo 2049435 3285127 := bstep (se 1 (by rfl) ⟨2463845, by rfl⟩ : syracuseStep 3285127 = 4927691) B4927691
theorem B4380169 : Blo 2049435 4380169 := bstep (se 2 (by rfl) ⟨1642563, by rfl⟩ : syracuseStep 4380169 = 3285127) B3285127
theorem B5840225 : Blo 2049435 5840225 := bstep (se 2 (by rfl) ⟨2190084, by rfl⟩ : syracuseStep 5840225 = 4380169) B4380169
theorem B3893483 : Blo 2049435 3893483 := bstep (se 1 (by rfl) ⟨2920112, by rfl⟩ : syracuseStep 3893483 = 5840225) B5840225
theorem B2595655 : Blo 2049435 2595655 := bstep (se 1 (by rfl) ⟨1946741, by rfl⟩ : syracuseStep 2595655 = 3893483) B3893483
theorem B3460873 : Blo 2049435 3460873 := bstep (se 2 (by rfl) ⟨1297827, by rfl⟩ : syracuseStep 3460873 = 2595655) B2595655
theorem B4614497 : Blo 2049435 4614497 := bstep (se 2 (by rfl) ⟨1730436, by rfl⟩ : syracuseStep 4614497 = 3460873) B3460873
theorem B3076331 : Blo 2049435 3076331 := bstep (se 1 (by rfl) ⟨2307248, by rfl⟩ : syracuseStep 3076331 = 4614497) B4614497
theorem B2050887 : Blo 2049435 2050887 := bstep (se 1 (by rfl) ⟨1538165, by rfl⟩ : syracuseStep 2050887 = 3076331) B3076331
theorem B2307253 : Blo 2049435 2307253 := bbase (se 5 (by rfl) ⟨108152, by rfl⟩ : syracuseStep 2307253 = 216305) (by norm_num)
theorem B3076337 : Blo 2049435 3076337 := bstep (se 2 (by rfl) ⟨1153626, by rfl⟩ : syracuseStep 3076337 = 2307253) B2307253
theorem B2050891 : Blo 2049435 2050891 := bstep (se 1 (by rfl) ⟨1538168, by rfl⟩ : syracuseStep 2050891 = 3076337) B3076337
theorem B2595665 : Blo 2049435 2595665 := bbase (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) (by norm_num)
theorem B6921773 : Blo 2049435 6921773 := bstep (se 3 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 6921773 = 2595665) B2595665
theorem B4614515 : Blo 2049435 4614515 := bstep (se 1 (by rfl) ⟨3460886, by rfl⟩ : syracuseStep 4614515 = 6921773) B6921773
theorem B3076343 : Blo 2049435 3076343 := bstep (se 1 (by rfl) ⟨2307257, by rfl⟩ : syracuseStep 3076343 = 4614515) B4614515
theorem B2050895 : Blo 2049435 2050895 := bstep (se 1 (by rfl) ⟨1538171, by rfl⟩ : syracuseStep 2050895 = 3076343) B3076343
theorem B3076349 : Blo 2049435 3076349 := bbase (se 3 (by rfl) ⟨576815, by rfl⟩ : syracuseStep 3076349 = 1153631) (by norm_num)
theorem B2050899 : Blo 2049435 2050899 := bstep (se 1 (by rfl) ⟨1538174, by rfl⟩ : syracuseStep 2050899 = 3076349) B3076349
theorem B4614533 : Blo 2049435 4614533 := bbase (se 4 (by rfl) ⟨432612, by rfl⟩ : syracuseStep 4614533 = 865225) (by norm_num)
theorem B3076355 : Blo 2049435 3076355 := bstep (se 1 (by rfl) ⟨2307266, by rfl⟩ : syracuseStep 3076355 = 4614533) B4614533
theorem B2050903 : Blo 2049435 2050903 := bstep (se 1 (by rfl) ⟨1538177, by rfl⟩ : syracuseStep 2050903 = 3076355) B3076355
theorem B2920141 : Blo 2049435 2920141 := bbase (se 3 (by rfl) ⟨547526, by rfl⟩ : syracuseStep 2920141 = 1095053) (by norm_num)
theorem B3893521 : Blo 2049435 3893521 := bstep (se 2 (by rfl) ⟨1460070, by rfl⟩ : syracuseStep 3893521 = 2920141) B2920141
theorem B5191361 : Blo 2049435 5191361 := bstep (se 2 (by rfl) ⟨1946760, by rfl⟩ : syracuseStep 5191361 = 3893521) B3893521
theorem B3460907 : Blo 2049435 3460907 := bstep (se 1 (by rfl) ⟨2595680, by rfl⟩ : syracuseStep 3460907 = 5191361) B5191361
theorem B2307271 : Blo 2049435 2307271 := bstep (se 1 (by rfl) ⟨1730453, by rfl⟩ : syracuseStep 2307271 = 3460907) B3460907
theorem B3076361 : Blo 2049435 3076361 := bstep (se 2 (by rfl) ⟨1153635, by rfl⟩ : syracuseStep 3076361 = 2307271) B2307271
theorem B2050907 : Blo 2049435 2050907 := bstep (se 1 (by rfl) ⟨1538180, by rfl⟩ : syracuseStep 2050907 = 3076361) B3076361
theorem B10382741 : Blo 2049435 10382741 := bbase (se 6 (by rfl) ⟨243345, by rfl⟩ : syracuseStep 10382741 = 486691) (by norm_num)
theorem B6921827 : Blo 2049435 6921827 := bstep (se 1 (by rfl) ⟨5191370, by rfl⟩ : syracuseStep 6921827 = 10382741) B10382741
theorem B4614551 : Blo 2049435 4614551 := bstep (se 1 (by rfl) ⟨3460913, by rfl⟩ : syracuseStep 4614551 = 6921827) B6921827
theorem B3076367 : Blo 2049435 3076367 := bstep (se 1 (by rfl) ⟨2307275, by rfl⟩ : syracuseStep 3076367 = 4614551) B4614551
theorem B2050911 : Blo 2049435 2050911 := bstep (se 1 (by rfl) ⟨1538183, by rfl⟩ : syracuseStep 2050911 = 3076367) B3076367
theorem B3076373 : Blo 2049435 3076373 := bbase (se 6 (by rfl) ⟨72102, by rfl⟩ : syracuseStep 3076373 = 144205) (by norm_num)
theorem B2050915 : Blo 2049435 2050915 := bstep (se 1 (by rfl) ⟨1538186, by rfl⟩ : syracuseStep 2050915 = 3076373) B3076373
theorem B2771869 : Blo 2049435 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B3695825 : Blo 2049435 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B9855533 : Blo 2049435 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B26281421 : Blo 2049435 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B17520947 : Blo 2049435 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B11680631 : Blo 2049435 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B7787087 : Blo 2049435 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B5191391 : Blo 2049435 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B3460927 : Blo 2049435 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B4614569 : Blo 2049435 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B3076379 : Blo 2049435 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B2050919 : Blo 2049435 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B2307289 : Blo 2049435 2307289 := bbase (se 2 (by rfl) ⟨865233, by rfl⟩ : syracuseStep 2307289 = 1730467) (by norm_num)
theorem B3076385 : Blo 2049435 3076385 := bstep (se 2 (by rfl) ⟨1153644, by rfl⟩ : syracuseStep 3076385 = 2307289) B2307289
theorem B2050923 : Blo 2049435 2050923 := bstep (se 1 (by rfl) ⟨1538192, by rfl⟩ : syracuseStep 2050923 = 3076385) B3076385
theorem B4157821 : Blo 2049435 4157821 := bbase (se 3 (by rfl) ⟨779591, by rfl⟩ : syracuseStep 4157821 = 1559183) (by norm_num)
theorem B5543761 : Blo 2049435 5543761 := bstep (se 2 (by rfl) ⟨2078910, by rfl⟩ : syracuseStep 5543761 = 4157821) B4157821
theorem B7391681 : Blo 2049435 7391681 := bstep (se 2 (by rfl) ⟨2771880, by rfl⟩ : syracuseStep 7391681 = 5543761) B5543761
theorem B4927787 : Blo 2049435 4927787 := bstep (se 1 (by rfl) ⟨3695840, by rfl⟩ : syracuseStep 4927787 = 7391681) B7391681
theorem B3285191 : Blo 2049435 3285191 := bstep (se 1 (by rfl) ⟨2463893, by rfl⟩ : syracuseStep 3285191 = 4927787) B4927787
theorem B2190127 : Blo 2049435 2190127 := bstep (se 1 (by rfl) ⟨1642595, by rfl⟩ : syracuseStep 2190127 = 3285191) B3285191
theorem B2920169 : Blo 2049435 2920169 := bstep (se 2 (by rfl) ⟨1095063, by rfl⟩ : syracuseStep 2920169 = 2190127) B2190127
theorem B7787117 : Blo 2049435 7787117 := bstep (se 3 (by rfl) ⟨1460084, by rfl⟩ : syracuseStep 7787117 = 2920169) B2920169
theorem B5191411 : Blo 2049435 5191411 := bstep (se 1 (by rfl) ⟨3893558, by rfl⟩ : syracuseStep 5191411 = 7787117) B7787117
theorem B6921881 : Blo 2049435 6921881 := bstep (se 2 (by rfl) ⟨2595705, by rfl⟩ : syracuseStep 6921881 = 5191411) B5191411
theorem B4614587 : Blo 2049435 4614587 := bstep (se 1 (by rfl) ⟨3460940, by rfl⟩ : syracuseStep 4614587 = 6921881) B6921881
theorem B3076391 : Blo 2049435 3076391 := bstep (se 1 (by rfl) ⟨2307293, by rfl⟩ : syracuseStep 3076391 = 4614587) B4614587
theorem B2050927 : Blo 2049435 2050927 := bstep (se 1 (by rfl) ⟨1538195, by rfl⟩ : syracuseStep 2050927 = 3076391) B3076391
theorem B3076397 : Blo 2049435 3076397 := bbase (se 3 (by rfl) ⟨576824, by rfl⟩ : syracuseStep 3076397 = 1153649) (by norm_num)
theorem B2050931 : Blo 2049435 2050931 := bstep (se 1 (by rfl) ⟨1538198, by rfl⟩ : syracuseStep 2050931 = 3076397) B3076397
theorem B4614605 : Blo 2049435 4614605 := bbase (se 3 (by rfl) ⟨865238, by rfl⟩ : syracuseStep 4614605 = 1730477) (by norm_num)
theorem B3076403 : Blo 2049435 3076403 := bstep (se 1 (by rfl) ⟨2307302, by rfl⟩ : syracuseStep 3076403 = 4614605) B4614605
theorem B2050935 : Blo 2049435 2050935 := bstep (se 1 (by rfl) ⟨1538201, by rfl⟩ : syracuseStep 2050935 = 3076403) B3076403
theorem B2595721 : Blo 2049435 2595721 := bbase (se 2 (by rfl) ⟨973395, by rfl⟩ : syracuseStep 2595721 = 1946791) (by norm_num)
theorem B3460961 : Blo 2049435 3460961 := bstep (se 2 (by rfl) ⟨1297860, by rfl⟩ : syracuseStep 3460961 = 2595721) B2595721
theorem B2307307 : Blo 2049435 2307307 := bstep (se 1 (by rfl) ⟨1730480, by rfl⟩ : syracuseStep 2307307 = 3460961) B3460961
theorem B3076409 : Blo 2049435 3076409 := bstep (se 2 (by rfl) ⟨1153653, by rfl⟩ : syracuseStep 3076409 = 2307307) B2307307
theorem B2050939 : Blo 2049435 2050939 := bstep (se 1 (by rfl) ⟨1538204, by rfl⟩ : syracuseStep 2050939 = 3076409) B3076409
theorem B2220025 : Blo 2049435 2220025 := bbase (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) (by norm_num)
theorem B2960033 : Blo 2049435 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B31573685 : Blo 2049435 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B84196493 : Blo 2049435 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B56130995 : Blo 2049435 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B149682653 : Blo 2049435 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B99788435 : Blo 2049435 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B66525623 : Blo 2049435 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B44350415 : Blo 2049435 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B29566943 : Blo 2049435 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B19711295 : Blo 2049435 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B13140863 : Blo 2049435 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B8760575 : Blo 2049435 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B23361533 : Blo 2049435 23361533 := bstep (se 3 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 23361533 = 8760575) B8760575
theorem B15574355 : Blo 2049435 15574355 := bstep (se 1 (by rfl) ⟨11680766, by rfl⟩ : syracuseStep 15574355 = 23361533) B23361533
theorem B10382903 : Blo 2049435 10382903 := bstep (se 1 (by rfl) ⟨7787177, by rfl⟩ : syracuseStep 10382903 = 15574355) B15574355
theorem B6921935 : Blo 2049435 6921935 := bstep (se 1 (by rfl) ⟨5191451, by rfl⟩ : syracuseStep 6921935 = 10382903) B10382903
theorem B4614623 : Blo 2049435 4614623 := bstep (se 1 (by rfl) ⟨3460967, by rfl⟩ : syracuseStep 4614623 = 6921935) B6921935
theorem B3076415 : Blo 2049435 3076415 := bstep (se 1 (by rfl) ⟨2307311, by rfl⟩ : syracuseStep 3076415 = 4614623) B4614623
theorem B2050943 : Blo 2049435 2050943 := bstep (se 1 (by rfl) ⟨1538207, by rfl⟩ : syracuseStep 2050943 = 3076415) B3076415
theorem B3076421 : Blo 2049435 3076421 := bbase (se 4 (by rfl) ⟨288414, by rfl⟩ : syracuseStep 3076421 = 576829) (by norm_num)
theorem B2050947 : Blo 2049435 2050947 := bstep (se 1 (by rfl) ⟨1538210, by rfl⟩ : syracuseStep 2050947 = 3076421) B3076421
theorem B3460981 : Blo 2049435 3460981 := bbase (se 5 (by rfl) ⟨162233, by rfl⟩ : syracuseStep 3460981 = 324467) (by norm_num)
theorem B4614641 : Blo 2049435 4614641 := bstep (se 2 (by rfl) ⟨1730490, by rfl⟩ : syracuseStep 4614641 = 3460981) B3460981
theorem B3076427 : Blo 2049435 3076427 := bstep (se 1 (by rfl) ⟨2307320, by rfl⟩ : syracuseStep 3076427 = 4614641) B4614641
theorem B2050951 : Blo 2049435 2050951 := bstep (se 1 (by rfl) ⟨1538213, by rfl⟩ : syracuseStep 2050951 = 3076427) B3076427
theorem B2307325 : Blo 2049435 2307325 := bbase (se 3 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 2307325 = 865247) (by norm_num)
theorem B3076433 : Blo 2049435 3076433 := bstep (se 2 (by rfl) ⟨1153662, by rfl⟩ : syracuseStep 3076433 = 2307325) B2307325
theorem B2050955 : Blo 2049435 2050955 := bstep (se 1 (by rfl) ⟨1538216, by rfl⟩ : syracuseStep 2050955 = 3076433) B3076433
theorem B6921989 : Blo 2049435 6921989 := bbase (se 4 (by rfl) ⟨648936, by rfl⟩ : syracuseStep 6921989 = 1297873) (by norm_num)
theorem B4614659 : Blo 2049435 4614659 := bstep (se 1 (by rfl) ⟨3460994, by rfl⟩ : syracuseStep 4614659 = 6921989) B6921989
theorem B3076439 : Blo 2049435 3076439 := bstep (se 1 (by rfl) ⟨2307329, by rfl⟩ : syracuseStep 3076439 = 4614659) B4614659
theorem B2050959 : Blo 2049435 2050959 := bstep (se 1 (by rfl) ⟨1538219, by rfl⟩ : syracuseStep 2050959 = 3076439) B3076439
theorem B3076445 : Blo 2049435 3076445 := bbase (se 3 (by rfl) ⟨576833, by rfl⟩ : syracuseStep 3076445 = 1153667) (by norm_num)
theorem B2050963 : Blo 2049435 2050963 := bstep (se 1 (by rfl) ⟨1538222, by rfl⟩ : syracuseStep 2050963 = 3076445) B3076445
theorem B4614677 : Blo 2049435 4614677 := bbase (se 6 (by rfl) ⟨108156, by rfl⟩ : syracuseStep 4614677 = 216313) (by norm_num)
theorem B3076451 : Blo 2049435 3076451 := bstep (se 1 (by rfl) ⟨2307338, by rfl⟩ : syracuseStep 3076451 = 4614677) B4614677
theorem B2050967 : Blo 2049435 2050967 := bstep (se 1 (by rfl) ⟨1538225, by rfl⟩ : syracuseStep 2050967 = 3076451) B3076451
theorem B7787285 : Blo 2049435 7787285 := bbase (se 6 (by rfl) ⟨182514, by rfl⟩ : syracuseStep 7787285 = 365029) (by norm_num)
theorem B5191523 : Blo 2049435 5191523 := bstep (se 1 (by rfl) ⟨3893642, by rfl⟩ : syracuseStep 5191523 = 7787285) B7787285
theorem B3461015 : Blo 2049435 3461015 := bstep (se 1 (by rfl) ⟨2595761, by rfl⟩ : syracuseStep 3461015 = 5191523) B5191523
theorem B2307343 : Blo 2049435 2307343 := bstep (se 1 (by rfl) ⟨1730507, by rfl⟩ : syracuseStep 2307343 = 3461015) B3461015
theorem B3076457 : Blo 2049435 3076457 := bstep (se 2 (by rfl) ⟨1153671, by rfl⟩ : syracuseStep 3076457 = 2307343) B2307343
theorem B2050971 : Blo 2049435 2050971 := bstep (se 1 (by rfl) ⟨1538228, by rfl⟩ : syracuseStep 2050971 = 3076457) B3076457
theorem B11680949 : Blo 2049435 11680949 := bbase (se 5 (by rfl) ⟨547544, by rfl⟩ : syracuseStep 11680949 = 1095089) (by norm_num)
theorem B7787299 : Blo 2049435 7787299 := bstep (se 1 (by rfl) ⟨5840474, by rfl⟩ : syracuseStep 7787299 = 11680949) B11680949
theorem B10383065 : Blo 2049435 10383065 := bstep (se 2 (by rfl) ⟨3893649, by rfl⟩ : syracuseStep 10383065 = 7787299) B7787299
theorem B6922043 : Blo 2049435 6922043 := bstep (se 1 (by rfl) ⟨5191532, by rfl⟩ : syracuseStep 6922043 = 10383065) B10383065
theorem B4614695 : Blo 2049435 4614695 := bstep (se 1 (by rfl) ⟨3461021, by rfl⟩ : syracuseStep 4614695 = 6922043) B6922043
theorem B3076463 : Blo 2049435 3076463 := bstep (se 1 (by rfl) ⟨2307347, by rfl⟩ : syracuseStep 3076463 = 4614695) B4614695
theorem B2050975 : Blo 2049435 2050975 := bstep (se 1 (by rfl) ⟨1538231, by rfl⟩ : syracuseStep 2050975 = 3076463) B3076463
theorem B3076469 : Blo 2049435 3076469 := bbase (se 5 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 3076469 = 288419) (by norm_num)
theorem B2050979 : Blo 2049435 2050979 := bstep (se 1 (by rfl) ⟨1538234, by rfl⟩ : syracuseStep 2050979 = 3076469) B3076469
theorem B2463961 : Blo 2049435 2463961 := bbase (se 2 (by rfl) ⟨923985, by rfl⟩ : syracuseStep 2463961 = 1847971) (by norm_num)
theorem B3285281 : Blo 2049435 3285281 := bstep (se 2 (by rfl) ⟨1231980, by rfl⟩ : syracuseStep 3285281 = 2463961) B2463961
theorem B2190187 : Blo 2049435 2190187 := bstep (se 1 (by rfl) ⟨1642640, by rfl⟩ : syracuseStep 2190187 = 3285281) B3285281
theorem B2920249 : Blo 2049435 2920249 := bstep (se 2 (by rfl) ⟨1095093, by rfl⟩ : syracuseStep 2920249 = 2190187) B2190187
theorem B3893665 : Blo 2049435 3893665 := bstep (se 2 (by rfl) ⟨1460124, by rfl⟩ : syracuseStep 3893665 = 2920249) B2920249
theorem B5191553 : Blo 2049435 5191553 := bstep (se 2 (by rfl) ⟨1946832, by rfl⟩ : syracuseStep 5191553 = 3893665) B3893665
theorem B3461035 : Blo 2049435 3461035 := bstep (se 1 (by rfl) ⟨2595776, by rfl⟩ : syracuseStep 3461035 = 5191553) B5191553
theorem B4614713 : Blo 2049435 4614713 := bstep (se 2 (by rfl) ⟨1730517, by rfl⟩ : syracuseStep 4614713 = 3461035) B3461035
theorem B3076475 : Blo 2049435 3076475 := bstep (se 1 (by rfl) ⟨2307356, by rfl⟩ : syracuseStep 3076475 = 4614713) B4614713
theorem B2050983 : Blo 2049435 2050983 := bstep (se 1 (by rfl) ⟨1538237, by rfl⟩ : syracuseStep 2050983 = 3076475) B3076475
theorem B2307361 : Blo 2049435 2307361 := bbase (se 2 (by rfl) ⟨865260, by rfl⟩ : syracuseStep 2307361 = 1730521) (by norm_num)
theorem B3076481 : Blo 2049435 3076481 := bstep (se 2 (by rfl) ⟨1153680, by rfl⟩ : syracuseStep 3076481 = 2307361) B2307361
theorem B2050987 : Blo 2049435 2050987 := bstep (se 1 (by rfl) ⟨1538240, by rfl⟩ : syracuseStep 2050987 = 3076481) B3076481
theorem B5191573 : Blo 2049435 5191573 := bbase (se 6 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 5191573 = 243355) (by norm_num)
theorem B6922097 : Blo 2049435 6922097 := bstep (se 2 (by rfl) ⟨2595786, by rfl⟩ : syracuseStep 6922097 = 5191573) B5191573
theorem B4614731 : Blo 2049435 4614731 := bstep (se 1 (by rfl) ⟨3461048, by rfl⟩ : syracuseStep 4614731 = 6922097) B6922097
theorem B3076487 : Blo 2049435 3076487 := bstep (se 1 (by rfl) ⟨2307365, by rfl⟩ : syracuseStep 3076487 = 4614731) B4614731
theorem B2050991 : Blo 2049435 2050991 := bstep (se 1 (by rfl) ⟨1538243, by rfl⟩ : syracuseStep 2050991 = 3076487) B3076487
theorem B3076493 : Blo 2049435 3076493 := bbase (se 3 (by rfl) ⟨576842, by rfl⟩ : syracuseStep 3076493 = 1153685) (by norm_num)
theorem B2050995 : Blo 2049435 2050995 := bstep (se 1 (by rfl) ⟨1538246, by rfl⟩ : syracuseStep 2050995 = 3076493) B3076493
theorem B4614749 : Blo 2049435 4614749 := bbase (se 3 (by rfl) ⟨865265, by rfl⟩ : syracuseStep 4614749 = 1730531) (by norm_num)
theorem B3076499 : Blo 2049435 3076499 := bstep (se 1 (by rfl) ⟨2307374, by rfl⟩ : syracuseStep 3076499 = 4614749) B4614749
theorem B2050999 : Blo 2049435 2050999 := bstep (se 1 (by rfl) ⟨1538249, by rfl⟩ : syracuseStep 2050999 = 3076499) B3076499
theorem B3461069 : Blo 2049435 3461069 := bbase (se 3 (by rfl) ⟨648950, by rfl⟩ : syracuseStep 3461069 = 1297901) (by norm_num)
theorem B2307379 : Blo 2049435 2307379 := bstep (se 1 (by rfl) ⟨1730534, by rfl⟩ : syracuseStep 2307379 = 3461069) B3461069
theorem B3076505 : Blo 2049435 3076505 := bstep (se 2 (by rfl) ⟨1153689, by rfl⟩ : syracuseStep 3076505 = 2307379) B2307379
theorem B2051003 : Blo 2049435 2051003 := bstep (se 1 (by rfl) ⟨1538252, by rfl⟩ : syracuseStep 2051003 = 3076505) B3076505
theorem B3556165 : Blo 2049435 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B4741553 : Blo 2049435 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B3161035 : Blo 2049435 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B16858853 : Blo 2049435 16858853 := bstep (se 4 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 16858853 = 3161035) B3161035
theorem B11239235 : Blo 2049435 11239235 := bstep (se 1 (by rfl) ⟨8429426, by rfl⟩ : syracuseStep 11239235 = 16858853) B16858853
theorem B7492823 : Blo 2049435 7492823 := bstep (se 1 (by rfl) ⟨5619617, by rfl⟩ : syracuseStep 7492823 = 11239235) B11239235
theorem B4995215 : Blo 2049435 4995215 := bstep (se 1 (by rfl) ⟨3746411, by rfl⟩ : syracuseStep 4995215 = 7492823) B7492823
theorem B3330143 : Blo 2049435 3330143 := bstep (se 1 (by rfl) ⟨2497607, by rfl⟩ : syracuseStep 3330143 = 4995215) B4995215
theorem B2220095 : Blo 2049435 2220095 := bstep (se 1 (by rfl) ⟨1665071, by rfl⟩ : syracuseStep 2220095 = 3330143) B3330143
theorem B5920253 : Blo 2049435 5920253 := bstep (se 3 (by rfl) ⟨1110047, by rfl⟩ : syracuseStep 5920253 = 2220095) B2220095
theorem B3946835 : Blo 2049435 3946835 := bstep (se 1 (by rfl) ⟨2960126, by rfl⟩ : syracuseStep 3946835 = 5920253) B5920253
theorem B2631223 : Blo 2049435 2631223 := bstep (se 1 (by rfl) ⟨1973417, by rfl⟩ : syracuseStep 2631223 = 3946835) B3946835
theorem B14033189 : Blo 2049435 14033189 := bstep (se 4 (by rfl) ⟨1315611, by rfl⟩ : syracuseStep 14033189 = 2631223) B2631223
theorem B9355459 : Blo 2049435 9355459 := bstep (se 1 (by rfl) ⟨7016594, by rfl⟩ : syracuseStep 9355459 = 14033189) B14033189
theorem B12473945 : Blo 2049435 12473945 := bstep (se 2 (by rfl) ⟨4677729, by rfl⟩ : syracuseStep 12473945 = 9355459) B9355459
theorem B8315963 : Blo 2049435 8315963 := bstep (se 1 (by rfl) ⟨6236972, by rfl⟩ : syracuseStep 8315963 = 12473945) B12473945
theorem B5543975 : Blo 2049435 5543975 := bstep (se 1 (by rfl) ⟨4157981, by rfl⟩ : syracuseStep 5543975 = 8315963) B8315963
theorem B14783933 : Blo 2049435 14783933 := bstep (se 3 (by rfl) ⟨2771987, by rfl⟩ : syracuseStep 14783933 = 5543975) B5543975
theorem B9855955 : Blo 2049435 9855955 := bstep (se 1 (by rfl) ⟨7391966, by rfl⟩ : syracuseStep 9855955 = 14783933) B14783933
theorem B13141273 : Blo 2049435 13141273 := bstep (se 2 (by rfl) ⟨4927977, by rfl⟩ : syracuseStep 13141273 = 9855955) B9855955
theorem B17521697 : Blo 2049435 17521697 := bstep (se 2 (by rfl) ⟨6570636, by rfl⟩ : syracuseStep 17521697 = 13141273) B13141273
theorem B11681131 : Blo 2049435 11681131 := bstep (se 1 (by rfl) ⟨8760848, by rfl⟩ : syracuseStep 11681131 = 17521697) B17521697
theorem B15574841 : Blo 2049435 15574841 := bstep (se 2 (by rfl) ⟨5840565, by rfl⟩ : syracuseStep 15574841 = 11681131) B11681131
theorem B10383227 : Blo 2049435 10383227 := bstep (se 1 (by rfl) ⟨7787420, by rfl⟩ : syracuseStep 10383227 = 15574841) B15574841
theorem B6922151 : Blo 2049435 6922151 := bstep (se 1 (by rfl) ⟨5191613, by rfl⟩ : syracuseStep 6922151 = 10383227) B10383227
theorem B4614767 : Blo 2049435 4614767 := bstep (se 1 (by rfl) ⟨3461075, by rfl⟩ : syracuseStep 4614767 = 6922151) B6922151
theorem B3076511 : Blo 2049435 3076511 := bstep (se 1 (by rfl) ⟨2307383, by rfl⟩ : syracuseStep 3076511 = 4614767) B4614767
theorem B2051007 : Blo 2049435 2051007 := bstep (se 1 (by rfl) ⟨1538255, by rfl⟩ : syracuseStep 2051007 = 3076511) B3076511
theorem B3076517 : Blo 2049435 3076517 := bbase (se 4 (by rfl) ⟨288423, by rfl⟩ : syracuseStep 3076517 = 576847) (by norm_num)
theorem B2051011 : Blo 2049435 2051011 := bstep (se 1 (by rfl) ⟨1538258, by rfl⟩ : syracuseStep 2051011 = 3076517) B3076517
theorem B2595817 : Blo 2049435 2595817 := bbase (se 2 (by rfl) ⟨973431, by rfl⟩ : syracuseStep 2595817 = 1946863) (by norm_num)
theorem B3461089 : Blo 2049435 3461089 := bstep (se 2 (by rfl) ⟨1297908, by rfl⟩ : syracuseStep 3461089 = 2595817) B2595817
theorem B4614785 : Blo 2049435 4614785 := bstep (se 2 (by rfl) ⟨1730544, by rfl⟩ : syracuseStep 4614785 = 3461089) B3461089
theorem B3076523 : Blo 2049435 3076523 := bstep (se 1 (by rfl) ⟨2307392, by rfl⟩ : syracuseStep 3076523 = 4614785) B4614785
theorem B2051015 : Blo 2049435 2051015 := bstep (se 1 (by rfl) ⟨1538261, by rfl⟩ : syracuseStep 2051015 = 3076523) B3076523
theorem B2307397 : Blo 2049435 2307397 := bbase (se 4 (by rfl) ⟨216318, by rfl⟩ : syracuseStep 2307397 = 432637) (by norm_num)
theorem B3076529 : Blo 2049435 3076529 := bstep (se 2 (by rfl) ⟨1153698, by rfl⟩ : syracuseStep 3076529 = 2307397) B2307397
theorem B2051019 : Blo 2049435 2051019 := bstep (se 1 (by rfl) ⟨1538264, by rfl⟩ : syracuseStep 2051019 = 3076529) B3076529
theorem B3893741 : Blo 2049435 3893741 := bbase (se 3 (by rfl) ⟨730076, by rfl⟩ : syracuseStep 3893741 = 1460153) (by norm_num)
theorem B2595827 : Blo 2049435 2595827 := bstep (se 1 (by rfl) ⟨1946870, by rfl⟩ : syracuseStep 2595827 = 3893741) B3893741
theorem B6922205 : Blo 2049435 6922205 := bstep (se 3 (by rfl) ⟨1297913, by rfl⟩ : syracuseStep 6922205 = 2595827) B2595827
theorem B4614803 : Blo 2049435 4614803 := bstep (se 1 (by rfl) ⟨3461102, by rfl⟩ : syracuseStep 4614803 = 6922205) B6922205
theorem B3076535 : Blo 2049435 3076535 := bstep (se 1 (by rfl) ⟨2307401, by rfl⟩ : syracuseStep 3076535 = 4614803) B4614803
theorem B2051023 : Blo 2049435 2051023 := bstep (se 1 (by rfl) ⟨1538267, by rfl⟩ : syracuseStep 2051023 = 3076535) B3076535
theorem B3076541 : Blo 2049435 3076541 := bbase (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) (by norm_num)
theorem B2051027 : Blo 2049435 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B4614821 : Blo 2049435 4614821 := bbase (se 4 (by rfl) ⟨432639, by rfl⟩ : syracuseStep 4614821 = 865279) (by norm_num)
theorem B3076547 : Blo 2049435 3076547 := bstep (se 1 (by rfl) ⟨2307410, by rfl⟩ : syracuseStep 3076547 = 4614821) B4614821
theorem B2051031 : Blo 2049435 2051031 := bstep (se 1 (by rfl) ⟨1538273, by rfl⟩ : syracuseStep 2051031 = 3076547) B3076547
theorem B5191685 : Blo 2049435 5191685 := bbase (se 4 (by rfl) ⟨486720, by rfl⟩ : syracuseStep 5191685 = 973441) (by norm_num)
theorem B3461123 : Blo 2049435 3461123 := bstep (se 1 (by rfl) ⟨2595842, by rfl⟩ : syracuseStep 3461123 = 5191685) B5191685
theorem B2307415 : Blo 2049435 2307415 := bstep (se 1 (by rfl) ⟨1730561, by rfl⟩ : syracuseStep 2307415 = 3461123) B3461123
theorem B3076553 : Blo 2049435 3076553 := bstep (se 2 (by rfl) ⟨1153707, by rfl⟩ : syracuseStep 3076553 = 2307415) B2307415
theorem B2051035 : Blo 2049435 2051035 := bstep (se 1 (by rfl) ⟨1538276, by rfl⟩ : syracuseStep 2051035 = 3076553) B3076553
theorem B4380493 : Blo 2049435 4380493 := bbase (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) (by norm_num)
theorem B5840657 : Blo 2049435 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B3893771 : Blo 2049435 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B10383389 : Blo 2049435 10383389 := bstep (se 3 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 10383389 = 3893771) B3893771
theorem B6922259 : Blo 2049435 6922259 := bstep (se 1 (by rfl) ⟨5191694, by rfl⟩ : syracuseStep 6922259 = 10383389) B10383389
theorem B4614839 : Blo 2049435 4614839 := bstep (se 1 (by rfl) ⟨3461129, by rfl⟩ : syracuseStep 4614839 = 6922259) B6922259
theorem B3076559 : Blo 2049435 3076559 := bstep (se 1 (by rfl) ⟨2307419, by rfl⟩ : syracuseStep 3076559 = 4614839) B4614839
theorem B2051039 : Blo 2049435 2051039 := bstep (se 1 (by rfl) ⟨1538279, by rfl⟩ : syracuseStep 2051039 = 3076559) B3076559
theorem B3076565 : Blo 2049435 3076565 := bbase (se 7 (by rfl) ⟨36053, by rfl⟩ : syracuseStep 3076565 = 72107) (by norm_num)
theorem B2051043 : Blo 2049435 2051043 := bstep (se 1 (by rfl) ⟨1538282, by rfl⟩ : syracuseStep 2051043 = 3076565) B3076565
theorem B7787573 : Blo 2049435 7787573 := bbase (se 5 (by rfl) ⟨365042, by rfl⟩ : syracuseStep 7787573 = 730085) (by norm_num)
theorem B5191715 : Blo 2049435 5191715 := bstep (se 1 (by rfl) ⟨3893786, by rfl⟩ : syracuseStep 5191715 = 7787573) B7787573
theorem B3461143 : Blo 2049435 3461143 := bstep (se 1 (by rfl) ⟨2595857, by rfl⟩ : syracuseStep 3461143 = 5191715) B5191715
theorem B4614857 : Blo 2049435 4614857 := bstep (se 2 (by rfl) ⟨1730571, by rfl⟩ : syracuseStep 4614857 = 3461143) B3461143
theorem B3076571 : Blo 2049435 3076571 := bstep (se 1 (by rfl) ⟨2307428, by rfl⟩ : syracuseStep 3076571 = 4614857) B4614857
theorem B2051047 : Blo 2049435 2051047 := bstep (se 1 (by rfl) ⟨1538285, by rfl⟩ : syracuseStep 2051047 = 3076571) B3076571
theorem B2307433 : Blo 2049435 2307433 := bbase (se 2 (by rfl) ⟨865287, by rfl⟩ : syracuseStep 2307433 = 1730575) (by norm_num)
theorem B3076577 : Blo 2049435 3076577 := bstep (se 2 (by rfl) ⟨1153716, by rfl⟩ : syracuseStep 3076577 = 2307433) B2307433
theorem B2051051 : Blo 2049435 2051051 := bstep (se 1 (by rfl) ⟨1538288, by rfl⟩ : syracuseStep 2051051 = 3076577) B3076577
theorem B2107405 : Blo 2049435 2107405 := bbase (se 3 (by rfl) ⟨395138, by rfl⟩ : syracuseStep 2107405 = 790277) (by norm_num)
theorem B11239493 : Blo 2049435 11239493 := bstep (se 4 (by rfl) ⟨1053702, by rfl⟩ : syracuseStep 11239493 = 2107405) B2107405
theorem B29971981 : Blo 2049435 29971981 := bstep (se 3 (by rfl) ⟨5619746, by rfl⟩ : syracuseStep 29971981 = 11239493) B11239493
theorem B39962641 : Blo 2049435 39962641 := bstep (se 2 (by rfl) ⟨14985990, by rfl⟩ : syracuseStep 39962641 = 29971981) B29971981
theorem B53283521 : Blo 2049435 53283521 := bstep (se 2 (by rfl) ⟨19981320, by rfl⟩ : syracuseStep 53283521 = 39962641) B39962641
theorem B35522347 : Blo 2049435 35522347 := bstep (se 1 (by rfl) ⟨26641760, by rfl⟩ : syracuseStep 35522347 = 53283521) B53283521
theorem B47363129 : Blo 2049435 47363129 := bstep (se 2 (by rfl) ⟨17761173, by rfl⟩ : syracuseStep 47363129 = 35522347) B35522347
theorem B31575419 : Blo 2049435 31575419 := bstep (se 1 (by rfl) ⟨23681564, by rfl⟩ : syracuseStep 31575419 = 47363129) B47363129
theorem B21050279 : Blo 2049435 21050279 := bstep (se 1 (by rfl) ⟨15787709, by rfl⟩ : syracuseStep 21050279 = 31575419) B31575419
theorem B14033519 : Blo 2049435 14033519 := bstep (se 1 (by rfl) ⟨10525139, by rfl⟩ : syracuseStep 14033519 = 21050279) B21050279
theorem B9355679 : Blo 2049435 9355679 := bstep (se 1 (by rfl) ⟨7016759, by rfl⟩ : syracuseStep 9355679 = 14033519) B14033519
theorem B6237119 : Blo 2049435 6237119 := bstep (se 1 (by rfl) ⟨4677839, by rfl⟩ : syracuseStep 6237119 = 9355679) B9355679
theorem B16632317 : Blo 2049435 16632317 := bstep (se 3 (by rfl) ⟨3118559, by rfl⟩ : syracuseStep 16632317 = 6237119) B6237119
theorem B11088211 : Blo 2049435 11088211 := bstep (se 1 (by rfl) ⟨8316158, by rfl⟩ : syracuseStep 11088211 = 16632317) B16632317
theorem B14784281 : Blo 2049435 14784281 := bstep (se 2 (by rfl) ⟨5544105, by rfl⟩ : syracuseStep 14784281 = 11088211) B11088211
theorem B9856187 : Blo 2049435 9856187 := bstep (se 1 (by rfl) ⟨7392140, by rfl⟩ : syracuseStep 9856187 = 14784281) B14784281
theorem B6570791 : Blo 2049435 6570791 := bstep (se 1 (by rfl) ⟨4928093, by rfl⟩ : syracuseStep 6570791 = 9856187) B9856187
theorem B4380527 : Blo 2049435 4380527 := bstep (se 1 (by rfl) ⟨3285395, by rfl⟩ : syracuseStep 4380527 = 6570791) B6570791
theorem B11681405 : Blo 2049435 11681405 := bstep (se 3 (by rfl) ⟨2190263, by rfl⟩ : syracuseStep 11681405 = 4380527) B4380527
theorem B7787603 : Blo 2049435 7787603 := bstep (se 1 (by rfl) ⟨5840702, by rfl⟩ : syracuseStep 7787603 = 11681405) B11681405
theorem B5191735 : Blo 2049435 5191735 := bstep (se 1 (by rfl) ⟨3893801, by rfl⟩ : syracuseStep 5191735 = 7787603) B7787603
theorem B6922313 : Blo 2049435 6922313 := bstep (se 2 (by rfl) ⟨2595867, by rfl⟩ : syracuseStep 6922313 = 5191735) B5191735
theorem B4614875 : Blo 2049435 4614875 := bstep (se 1 (by rfl) ⟨3461156, by rfl⟩ : syracuseStep 4614875 = 6922313) B6922313
theorem B3076583 : Blo 2049435 3076583 := bstep (se 1 (by rfl) ⟨2307437, by rfl⟩ : syracuseStep 3076583 = 4614875) B4614875
theorem B2051055 : Blo 2049435 2051055 := bstep (se 1 (by rfl) ⟨1538291, by rfl⟩ : syracuseStep 2051055 = 3076583) B3076583
theorem B3076589 : Blo 2049435 3076589 := bbase (se 3 (by rfl) ⟨576860, by rfl⟩ : syracuseStep 3076589 = 1153721) (by norm_num)
theorem B2051059 : Blo 2049435 2051059 := bstep (se 1 (by rfl) ⟨1538294, by rfl⟩ : syracuseStep 2051059 = 3076589) B3076589
theorem B4614893 : Blo 2049435 4614893 := bbase (se 3 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 4614893 = 1730585) (by norm_num)
theorem B3076595 : Blo 2049435 3076595 := bstep (se 1 (by rfl) ⟨2307446, by rfl⟩ : syracuseStep 3076595 = 4614893) B4614893
theorem B2051063 : Blo 2049435 2051063 := bstep (se 1 (by rfl) ⟨1538297, by rfl⟩ : syracuseStep 2051063 = 3076595) B3076595
theorem B2190277 : Blo 2049435 2190277 := bbase (se 4 (by rfl) ⟨205338, by rfl⟩ : syracuseStep 2190277 = 410677) (by norm_num)
theorem B2920369 : Blo 2049435 2920369 := bstep (se 2 (by rfl) ⟨1095138, by rfl⟩ : syracuseStep 2920369 = 2190277) B2190277
theorem B3893825 : Blo 2049435 3893825 := bstep (se 2 (by rfl) ⟨1460184, by rfl⟩ : syracuseStep 3893825 = 2920369) B2920369
theorem B2595883 : Blo 2049435 2595883 := bstep (se 1 (by rfl) ⟨1946912, by rfl⟩ : syracuseStep 2595883 = 3893825) B3893825
theorem B3461177 : Blo 2049435 3461177 := bstep (se 2 (by rfl) ⟨1297941, by rfl⟩ : syracuseStep 3461177 = 2595883) B2595883
theorem B2307451 : Blo 2049435 2307451 := bstep (se 1 (by rfl) ⟨1730588, by rfl⟩ : syracuseStep 2307451 = 3461177) B3461177
theorem B3076601 : Blo 2049435 3076601 := bstep (se 2 (by rfl) ⟨1153725, by rfl⟩ : syracuseStep 3076601 = 2307451) B2307451
theorem B2051067 : Blo 2049435 2051067 := bstep (se 1 (by rfl) ⟨1538300, by rfl⟩ : syracuseStep 2051067 = 3076601) B3076601
theorem B3946957 : Blo 2049435 3946957 := bbase (se 3 (by rfl) ⟨740054, by rfl⟩ : syracuseStep 3946957 = 1480109) (by norm_num)
theorem B21050437 : Blo 2049435 21050437 := bstep (se 4 (by rfl) ⟨1973478, by rfl⟩ : syracuseStep 21050437 = 3946957) B3946957
theorem B28067249 : Blo 2049435 28067249 := bstep (se 2 (by rfl) ⟨10525218, by rfl⟩ : syracuseStep 28067249 = 21050437) B21050437
theorem B18711499 : Blo 2049435 18711499 := bstep (se 1 (by rfl) ⟨14033624, by rfl⟩ : syracuseStep 18711499 = 28067249) B28067249
theorem B24948665 : Blo 2049435 24948665 := bstep (se 2 (by rfl) ⟨9355749, by rfl⟩ : syracuseStep 24948665 = 18711499) B18711499
theorem B16632443 : Blo 2049435 16632443 := bstep (se 1 (by rfl) ⟨12474332, by rfl⟩ : syracuseStep 16632443 = 24948665) B24948665
theorem B11088295 : Blo 2049435 11088295 := bstep (se 1 (by rfl) ⟨8316221, by rfl⟩ : syracuseStep 11088295 = 16632443) B16632443
theorem B59137573 : Blo 2049435 59137573 := bstep (se 4 (by rfl) ⟨5544147, by rfl⟩ : syracuseStep 59137573 = 11088295) B11088295
theorem B78850097 : Blo 2049435 78850097 := bstep (se 2 (by rfl) ⟨29568786, by rfl⟩ : syracuseStep 78850097 = 59137573) B59137573
theorem B52566731 : Blo 2049435 52566731 := bstep (se 1 (by rfl) ⟨39425048, by rfl⟩ : syracuseStep 52566731 = 78850097) B78850097
theorem B35044487 : Blo 2049435 35044487 := bstep (se 1 (by rfl) ⟨26283365, by rfl⟩ : syracuseStep 35044487 = 52566731) B52566731
theorem B23362991 : Blo 2049435 23362991 := bstep (se 1 (by rfl) ⟨17522243, by rfl⟩ : syracuseStep 23362991 = 35044487) B35044487
theorem B15575327 : Blo 2049435 15575327 := bstep (se 1 (by rfl) ⟨11681495, by rfl⟩ : syracuseStep 15575327 = 23362991) B23362991
theorem B10383551 : Blo 2049435 10383551 := bstep (se 1 (by rfl) ⟨7787663, by rfl⟩ : syracuseStep 10383551 = 15575327) B15575327
theorem B6922367 : Blo 2049435 6922367 := bstep (se 1 (by rfl) ⟨5191775, by rfl⟩ : syracuseStep 6922367 = 10383551) B10383551
theorem B4614911 : Blo 2049435 4614911 := bstep (se 1 (by rfl) ⟨3461183, by rfl⟩ : syracuseStep 4614911 = 6922367) B6922367
theorem B3076607 : Blo 2049435 3076607 := bstep (se 1 (by rfl) ⟨2307455, by rfl⟩ : syracuseStep 3076607 = 4614911) B4614911
theorem B2051071 : Blo 2049435 2051071 := bstep (se 1 (by rfl) ⟨1538303, by rfl⟩ : syracuseStep 2051071 = 3076607) B3076607
theorem B3076613 : Blo 2049435 3076613 := bbase (se 4 (by rfl) ⟨288432, by rfl⟩ : syracuseStep 3076613 = 576865) (by norm_num)
theorem B2051075 : Blo 2049435 2051075 := bstep (se 1 (by rfl) ⟨1538306, by rfl⟩ : syracuseStep 2051075 = 3076613) B3076613
theorem B3461197 : Blo 2049435 3461197 := bbase (se 3 (by rfl) ⟨648974, by rfl⟩ : syracuseStep 3461197 = 1297949) (by norm_num)
theorem B4614929 : Blo 2049435 4614929 := bstep (se 2 (by rfl) ⟨1730598, by rfl⟩ : syracuseStep 4614929 = 3461197) B3461197
theorem B3076619 : Blo 2049435 3076619 := bstep (se 1 (by rfl) ⟨2307464, by rfl⟩ : syracuseStep 3076619 = 4614929) B4614929
theorem B2051079 : Blo 2049435 2051079 := bstep (se 1 (by rfl) ⟨1538309, by rfl⟩ : syracuseStep 2051079 = 3076619) B3076619
theorem B2307469 : Blo 2049435 2307469 := bbase (se 3 (by rfl) ⟨432650, by rfl⟩ : syracuseStep 2307469 = 865301) (by norm_num)
theorem B3076625 : Blo 2049435 3076625 := bstep (se 2 (by rfl) ⟨1153734, by rfl⟩ : syracuseStep 3076625 = 2307469) B2307469
theorem B2051083 : Blo 2049435 2051083 := bstep (se 1 (by rfl) ⟨1538312, by rfl⟩ : syracuseStep 2051083 = 3076625) B3076625
theorem B6922421 : Blo 2049435 6922421 := bbase (se 5 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 6922421 = 648977) (by norm_num)
theorem B4614947 : Blo 2049435 4614947 := bstep (se 1 (by rfl) ⟨3461210, by rfl⟩ : syracuseStep 4614947 = 6922421) B6922421
theorem B3076631 : Blo 2049435 3076631 := bstep (se 1 (by rfl) ⟨2307473, by rfl⟩ : syracuseStep 3076631 = 4614947) B4614947
theorem B2051087 : Blo 2049435 2051087 := bstep (se 1 (by rfl) ⟨1538315, by rfl⟩ : syracuseStep 2051087 = 3076631) B3076631
theorem B3076637 : Blo 2049435 3076637 := bbase (se 3 (by rfl) ⟨576869, by rfl⟩ : syracuseStep 3076637 = 1153739) (by norm_num)
theorem B2051091 : Blo 2049435 2051091 := bstep (se 1 (by rfl) ⟨1538318, by rfl⟩ : syracuseStep 2051091 = 3076637) B3076637
theorem B4614965 : Blo 2049435 4614965 := bbase (se 5 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 4614965 = 432653) (by norm_num)
theorem B3076643 : Blo 2049435 3076643 := bstep (se 1 (by rfl) ⟨2307482, by rfl⟩ : syracuseStep 3076643 = 4614965) B4614965
theorem B2051095 : Blo 2049435 2051095 := bstep (se 1 (by rfl) ⟨1538321, by rfl⟩ : syracuseStep 2051095 = 3076643) B3076643
theorem B6237253 : Blo 2049435 6237253 := bbase (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) (by norm_num)
theorem B33265349 : Blo 2049435 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B22176899 : Blo 2049435 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B14784599 : Blo 2049435 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B9856399 : Blo 2049435 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B13141865 : Blo 2049435 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B8761243 : Blo 2049435 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B11681657 : Blo 2049435 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B7787771 : Blo 2049435 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B5191847 : Blo 2049435 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B3461231 : Blo 2049435 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B2307487 : Blo 2049435 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B3076649 : Blo 2049435 3076649 := bstep (se 2 (by rfl) ⟨1153743, by rfl⟩ : syracuseStep 3076649 = 2307487) B2307487
theorem B2051099 : Blo 2049435 2051099 := bstep (se 1 (by rfl) ⟨1538324, by rfl⟩ : syracuseStep 2051099 = 3076649) B3076649
theorem B4677949 : Blo 2049435 4677949 := bbase (se 3 (by rfl) ⟨877115, by rfl⟩ : syracuseStep 4677949 = 1754231) (by norm_num)
theorem B6237265 : Blo 2049435 6237265 := bstep (se 2 (by rfl) ⟨2338974, by rfl⟩ : syracuseStep 6237265 = 4677949) B4677949
theorem B8316353 : Blo 2049435 8316353 := bstep (se 2 (by rfl) ⟨3118632, by rfl⟩ : syracuseStep 8316353 = 6237265) B6237265
theorem B5544235 : Blo 2049435 5544235 := bstep (se 1 (by rfl) ⟨4158176, by rfl⟩ : syracuseStep 5544235 = 8316353) B8316353
theorem B7392313 : Blo 2049435 7392313 := bstep (se 2 (by rfl) ⟨2772117, by rfl⟩ : syracuseStep 7392313 = 5544235) B5544235
theorem B9856417 : Blo 2049435 9856417 := bstep (se 2 (by rfl) ⟨3696156, by rfl⟩ : syracuseStep 9856417 = 7392313) B7392313
theorem B13141889 : Blo 2049435 13141889 := bstep (se 2 (by rfl) ⟨4928208, by rfl⟩ : syracuseStep 13141889 = 9856417) B9856417
theorem B8761259 : Blo 2049435 8761259 := bstep (se 1 (by rfl) ⟨6570944, by rfl⟩ : syracuseStep 8761259 = 13141889) B13141889
theorem B5840839 : Blo 2049435 5840839 := bstep (se 1 (by rfl) ⟨4380629, by rfl⟩ : syracuseStep 5840839 = 8761259) B8761259
theorem B7787785 : Blo 2049435 7787785 := bstep (se 2 (by rfl) ⟨2920419, by rfl⟩ : syracuseStep 7787785 = 5840839) B5840839
theorem B10383713 : Blo 2049435 10383713 := bstep (se 2 (by rfl) ⟨3893892, by rfl⟩ : syracuseStep 10383713 = 7787785) B7787785
theorem B6922475 : Blo 2049435 6922475 := bstep (se 1 (by rfl) ⟨5191856, by rfl⟩ : syracuseStep 6922475 = 10383713) B10383713
theorem B4614983 : Blo 2049435 4614983 := bstep (se 1 (by rfl) ⟨3461237, by rfl⟩ : syracuseStep 4614983 = 6922475) B6922475
theorem B3076655 : Blo 2049435 3076655 := bstep (se 1 (by rfl) ⟨2307491, by rfl⟩ : syracuseStep 3076655 = 4614983) B4614983
theorem B2051103 : Blo 2049435 2051103 := bstep (se 1 (by rfl) ⟨1538327, by rfl⟩ : syracuseStep 2051103 = 3076655) B3076655
theorem B3076661 : Blo 2049435 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B2051107 : Blo 2049435 2051107 := bstep (se 1 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 2051107 = 3076661) B3076661
theorem B5191877 : Blo 2049435 5191877 := bbase (se 4 (by rfl) ⟨486738, by rfl⟩ : syracuseStep 5191877 = 973477) (by norm_num)
theorem B3461251 : Blo 2049435 3461251 := bstep (se 1 (by rfl) ⟨2595938, by rfl⟩ : syracuseStep 3461251 = 5191877) B5191877
theorem B4615001 : Blo 2049435 4615001 := bstep (se 2 (by rfl) ⟨1730625, by rfl⟩ : syracuseStep 4615001 = 3461251) B3461251
theorem B3076667 : Blo 2049435 3076667 := bstep (se 1 (by rfl) ⟨2307500, by rfl⟩ : syracuseStep 3076667 = 4615001) B4615001
theorem B2051111 : Blo 2049435 2051111 := bstep (se 1 (by rfl) ⟨1538333, by rfl⟩ : syracuseStep 2051111 = 3076667) B3076667
theorem B2307505 : Blo 2049435 2307505 := bbase (se 2 (by rfl) ⟨865314, by rfl⟩ : syracuseStep 2307505 = 1730629) (by norm_num)
theorem B3076673 : Blo 2049435 3076673 := bstep (se 2 (by rfl) ⟨1153752, by rfl⟩ : syracuseStep 3076673 = 2307505) B2307505
theorem B2051115 : Blo 2049435 2051115 := bstep (se 1 (by rfl) ⟨1538336, by rfl⟩ : syracuseStep 2051115 = 3076673) B3076673
theorem B5840885 : Blo 2049435 5840885 := bbase (se 5 (by rfl) ⟨273791, by rfl⟩ : syracuseStep 5840885 = 547583) (by norm_num)
theorem B3893923 : Blo 2049435 3893923 := bstep (se 1 (by rfl) ⟨2920442, by rfl⟩ : syracuseStep 3893923 = 5840885) B5840885
theorem B5191897 : Blo 2049435 5191897 := bstep (se 2 (by rfl) ⟨1946961, by rfl⟩ : syracuseStep 5191897 = 3893923) B3893923
theorem B6922529 : Blo 2049435 6922529 := bstep (se 2 (by rfl) ⟨2595948, by rfl⟩ : syracuseStep 6922529 = 5191897) B5191897
theorem B4615019 : Blo 2049435 4615019 := bstep (se 1 (by rfl) ⟨3461264, by rfl⟩ : syracuseStep 4615019 = 6922529) B6922529
theorem B3076679 : Blo 2049435 3076679 := bstep (se 1 (by rfl) ⟨2307509, by rfl⟩ : syracuseStep 3076679 = 4615019) B4615019
theorem B2051119 : Blo 2049435 2051119 := bstep (se 1 (by rfl) ⟨1538339, by rfl⟩ : syracuseStep 2051119 = 3076679) B3076679
theorem B3076685 : Blo 2049435 3076685 := bbase (se 3 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 3076685 = 1153757) (by norm_num)
theorem B2051123 : Blo 2049435 2051123 := bstep (se 1 (by rfl) ⟨1538342, by rfl⟩ : syracuseStep 2051123 = 3076685) B3076685
theorem B4615037 : Blo 2049435 4615037 := bbase (se 3 (by rfl) ⟨865319, by rfl⟩ : syracuseStep 4615037 = 1730639) (by norm_num)
theorem B3076691 : Blo 2049435 3076691 := bstep (se 1 (by rfl) ⟨2307518, by rfl⟩ : syracuseStep 3076691 = 4615037) B4615037
theorem B2051127 : Blo 2049435 2051127 := bstep (se 1 (by rfl) ⟨1538345, by rfl⟩ : syracuseStep 2051127 = 3076691) B3076691
theorem B3461285 : Blo 2049435 3461285 := bbase (se 4 (by rfl) ⟨324495, by rfl⟩ : syracuseStep 3461285 = 648991) (by norm_num)
theorem B2307523 : Blo 2049435 2307523 := bstep (se 1 (by rfl) ⟨1730642, by rfl⟩ : syracuseStep 2307523 = 3461285) B3461285
theorem B3076697 : Blo 2049435 3076697 := bstep (se 2 (by rfl) ⟨1153761, by rfl⟩ : syracuseStep 3076697 = 2307523) B2307523
theorem B2051131 : Blo 2049435 2051131 := bstep (se 1 (by rfl) ⟨1538348, by rfl⟩ : syracuseStep 2051131 = 3076697) B3076697
theorem B2190349 : Blo 2049435 2190349 := bbase (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) (by norm_num)
theorem B2920465 : Blo 2049435 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B15575813 : Blo 2049435 15575813 := bstep (se 4 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 15575813 = 2920465) B2920465
theorem B10383875 : Blo 2049435 10383875 := bstep (se 1 (by rfl) ⟨7787906, by rfl⟩ : syracuseStep 10383875 = 15575813) B15575813
theorem B6922583 : Blo 2049435 6922583 := bstep (se 1 (by rfl) ⟨5191937, by rfl⟩ : syracuseStep 6922583 = 10383875) B10383875
theorem B4615055 : Blo 2049435 4615055 := bstep (se 1 (by rfl) ⟨3461291, by rfl⟩ : syracuseStep 4615055 = 6922583) B6922583
theorem B3076703 : Blo 2049435 3076703 := bstep (se 1 (by rfl) ⟨2307527, by rfl⟩ : syracuseStep 3076703 = 4615055) B4615055
theorem B2051135 : Blo 2049435 2051135 := bstep (se 1 (by rfl) ⟨1538351, by rfl⟩ : syracuseStep 2051135 = 3076703) B3076703
theorem B3076709 : Blo 2049435 3076709 := bbase (se 4 (by rfl) ⟨288441, by rfl⟩ : syracuseStep 3076709 = 576883) (by norm_num)
theorem B2051139 : Blo 2049435 2051139 := bstep (se 1 (by rfl) ⟨1538354, by rfl⟩ : syracuseStep 2051139 = 3076709) B3076709
theorem B2920477 : Blo 2049435 2920477 := bbase (se 3 (by rfl) ⟨547589, by rfl⟩ : syracuseStep 2920477 = 1095179) (by norm_num)
theorem B3893969 : Blo 2049435 3893969 := bstep (se 2 (by rfl) ⟨1460238, by rfl⟩ : syracuseStep 3893969 = 2920477) B2920477
theorem B2595979 : Blo 2049435 2595979 := bstep (se 1 (by rfl) ⟨1946984, by rfl⟩ : syracuseStep 2595979 = 3893969) B3893969
theorem B3461305 : Blo 2049435 3461305 := bstep (se 2 (by rfl) ⟨1297989, by rfl⟩ : syracuseStep 3461305 = 2595979) B2595979
theorem B4615073 : Blo 2049435 4615073 := bstep (se 2 (by rfl) ⟨1730652, by rfl⟩ : syracuseStep 4615073 = 3461305) B3461305
theorem B3076715 : Blo 2049435 3076715 := bstep (se 1 (by rfl) ⟨2307536, by rfl⟩ : syracuseStep 3076715 = 4615073) B4615073
theorem B2051143 : Blo 2049435 2051143 := bstep (se 1 (by rfl) ⟨1538357, by rfl⟩ : syracuseStep 2051143 = 3076715) B3076715
theorem B2307541 : Blo 2049435 2307541 := bbase (se 7 (by rfl) ⟨27041, by rfl⟩ : syracuseStep 2307541 = 54083) (by norm_num)
theorem B3076721 : Blo 2049435 3076721 := bstep (se 2 (by rfl) ⟨1153770, by rfl⟩ : syracuseStep 3076721 = 2307541) B2307541
theorem B2051147 : Blo 2049435 2051147 := bstep (se 1 (by rfl) ⟨1538360, by rfl⟩ : syracuseStep 2051147 = 3076721) B3076721
theorem B2595989 : Blo 2049435 2595989 := bbase (se 6 (by rfl) ⟨60843, by rfl⟩ : syracuseStep 2595989 = 121687) (by norm_num)
theorem B6922637 : Blo 2049435 6922637 := bstep (se 3 (by rfl) ⟨1297994, by rfl⟩ : syracuseStep 6922637 = 2595989) B2595989
theorem B4615091 : Blo 2049435 4615091 := bstep (se 1 (by rfl) ⟨3461318, by rfl⟩ : syracuseStep 4615091 = 6922637) B6922637
theorem B3076727 : Blo 2049435 3076727 := bstep (se 1 (by rfl) ⟨2307545, by rfl⟩ : syracuseStep 3076727 = 4615091) B4615091
theorem B2051151 : Blo 2049435 2051151 := bstep (se 1 (by rfl) ⟨1538363, by rfl⟩ : syracuseStep 2051151 = 3076727) B3076727
theorem B3076733 : Blo 2049435 3076733 := bbase (se 3 (by rfl) ⟨576887, by rfl⟩ : syracuseStep 3076733 = 1153775) (by norm_num)
theorem B2051155 : Blo 2049435 2051155 := bstep (se 1 (by rfl) ⟨1538366, by rfl⟩ : syracuseStep 2051155 = 3076733) B3076733
theorem B4615109 : Blo 2049435 4615109 := bbase (se 4 (by rfl) ⟨432666, by rfl⟩ : syracuseStep 4615109 = 865333) (by norm_num)
theorem B3076739 : Blo 2049435 3076739 := bstep (se 1 (by rfl) ⟨2307554, by rfl⟩ : syracuseStep 3076739 = 4615109) B4615109
theorem B2051159 : Blo 2049435 2051159 := bstep (se 1 (by rfl) ⟨1538369, by rfl⟩ : syracuseStep 2051159 = 3076739) B3076739
theorem B2464177 : Blo 2049435 2464177 := bbase (se 2 (by rfl) ⟨924066, by rfl⟩ : syracuseStep 2464177 = 1848133) (by norm_num)
theorem B3285569 : Blo 2049435 3285569 := bstep (se 2 (by rfl) ⟨1232088, by rfl⟩ : syracuseStep 3285569 = 2464177) B2464177
theorem B8761517 : Blo 2049435 8761517 := bstep (se 3 (by rfl) ⟨1642784, by rfl⟩ : syracuseStep 8761517 = 3285569) B3285569
theorem B5841011 : Blo 2049435 5841011 := bstep (se 1 (by rfl) ⟨4380758, by rfl⟩ : syracuseStep 5841011 = 8761517) B8761517
theorem B3894007 : Blo 2049435 3894007 := bstep (se 1 (by rfl) ⟨2920505, by rfl⟩ : syracuseStep 3894007 = 5841011) B5841011
theorem B5192009 : Blo 2049435 5192009 := bstep (se 2 (by rfl) ⟨1947003, by rfl⟩ : syracuseStep 5192009 = 3894007) B3894007
theorem B3461339 : Blo 2049435 3461339 := bstep (se 1 (by rfl) ⟨2596004, by rfl⟩ : syracuseStep 3461339 = 5192009) B5192009
theorem B2307559 : Blo 2049435 2307559 := bstep (se 1 (by rfl) ⟨1730669, by rfl⟩ : syracuseStep 2307559 = 3461339) B3461339
theorem B3076745 : Blo 2049435 3076745 := bstep (se 2 (by rfl) ⟨1153779, by rfl⟩ : syracuseStep 3076745 = 2307559) B2307559
theorem B2051163 : Blo 2049435 2051163 := bstep (se 1 (by rfl) ⟨1538372, by rfl⟩ : syracuseStep 2051163 = 3076745) B3076745
theorem B10384037 : Blo 2049435 10384037 := bbase (se 4 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 10384037 = 1947007) (by norm_num)
theorem B6922691 : Blo 2049435 6922691 := bstep (se 1 (by rfl) ⟨5192018, by rfl⟩ : syracuseStep 6922691 = 10384037) B10384037
theorem B4615127 : Blo 2049435 4615127 := bstep (se 1 (by rfl) ⟨3461345, by rfl⟩ : syracuseStep 4615127 = 6922691) B6922691
theorem B3076751 : Blo 2049435 3076751 := bstep (se 1 (by rfl) ⟨2307563, by rfl⟩ : syracuseStep 3076751 = 4615127) B4615127
theorem B2051167 : Blo 2049435 2051167 := bstep (se 1 (by rfl) ⟨1538375, by rfl⟩ : syracuseStep 2051167 = 3076751) B3076751
theorem B3076757 : Blo 2049435 3076757 := bbase (se 6 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 3076757 = 144223) (by norm_num)
theorem B2051171 : Blo 2049435 2051171 := bstep (se 1 (by rfl) ⟨1538378, by rfl⟩ : syracuseStep 2051171 = 3076757) B3076757
theorem B5262877 : Blo 2049435 5262877 := bbase (se 3 (by rfl) ⟨986789, by rfl⟩ : syracuseStep 5262877 = 1973579) (by norm_num)
theorem B28068677 : Blo 2049435 28068677 := bstep (se 4 (by rfl) ⟨2631438, by rfl⟩ : syracuseStep 28068677 = 5262877) B5262877
theorem B18712451 : Blo 2049435 18712451 := bstep (se 1 (by rfl) ⟨14034338, by rfl⟩ : syracuseStep 18712451 = 28068677) B28068677
theorem B12474967 : Blo 2049435 12474967 := bstep (se 1 (by rfl) ⟨9356225, by rfl⟩ : syracuseStep 12474967 = 18712451) B18712451
theorem B16633289 : Blo 2049435 16633289 := bstep (se 2 (by rfl) ⟨6237483, by rfl⟩ : syracuseStep 16633289 = 12474967) B12474967
theorem B44355437 : Blo 2049435 44355437 := bstep (se 3 (by rfl) ⟨8316644, by rfl⟩ : syracuseStep 44355437 = 16633289) B16633289
theorem B29570291 : Blo 2049435 29570291 := bstep (se 1 (by rfl) ⟨22177718, by rfl⟩ : syracuseStep 29570291 = 44355437) B44355437
theorem B19713527 : Blo 2049435 19713527 := bstep (se 1 (by rfl) ⟨14785145, by rfl⟩ : syracuseStep 19713527 = 29570291) B29570291
theorem B13142351 : Blo 2049435 13142351 := bstep (se 1 (by rfl) ⟨9856763, by rfl⟩ : syracuseStep 13142351 = 19713527) B19713527
theorem B8761567 : Blo 2049435 8761567 := bstep (se 1 (by rfl) ⟨6571175, by rfl⟩ : syracuseStep 8761567 = 13142351) B13142351
theorem B11682089 : Blo 2049435 11682089 := bstep (se 2 (by rfl) ⟨4380783, by rfl⟩ : syracuseStep 11682089 = 8761567) B8761567
theorem B7788059 : Blo 2049435 7788059 := bstep (se 1 (by rfl) ⟨5841044, by rfl⟩ : syracuseStep 7788059 = 11682089) B11682089
theorem B5192039 : Blo 2049435 5192039 := bstep (se 1 (by rfl) ⟨3894029, by rfl⟩ : syracuseStep 5192039 = 7788059) B7788059
theorem B3461359 : Blo 2049435 3461359 := bstep (se 1 (by rfl) ⟨2596019, by rfl⟩ : syracuseStep 3461359 = 5192039) B5192039
theorem B4615145 : Blo 2049435 4615145 := bstep (se 2 (by rfl) ⟨1730679, by rfl⟩ : syracuseStep 4615145 = 3461359) B3461359
theorem B3076763 : Blo 2049435 3076763 := bstep (se 1 (by rfl) ⟨2307572, by rfl⟩ : syracuseStep 3076763 = 4615145) B4615145
theorem B2051175 : Blo 2049435 2051175 := bstep (se 1 (by rfl) ⟨1538381, by rfl⟩ : syracuseStep 2051175 = 3076763) B3076763
theorem B2307577 : Blo 2049435 2307577 := bbase (se 2 (by rfl) ⟨865341, by rfl⟩ : syracuseStep 2307577 = 1730683) (by norm_num)
theorem B3076769 : Blo 2049435 3076769 := bstep (se 2 (by rfl) ⟨1153788, by rfl⟩ : syracuseStep 3076769 = 2307577) B2307577
theorem B2051179 : Blo 2049435 2051179 := bstep (se 1 (by rfl) ⟨1538384, by rfl⟩ : syracuseStep 2051179 = 3076769) B3076769
theorem B3696301 : Blo 2049435 3696301 := bbase (se 3 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 3696301 = 1386113) (by norm_num)
theorem B4928401 : Blo 2049435 4928401 := bstep (se 2 (by rfl) ⟨1848150, by rfl⟩ : syracuseStep 4928401 = 3696301) B3696301
theorem B6571201 : Blo 2049435 6571201 := bstep (se 2 (by rfl) ⟨2464200, by rfl⟩ : syracuseStep 6571201 = 4928401) B4928401
theorem B8761601 : Blo 2049435 8761601 := bstep (se 2 (by rfl) ⟨3285600, by rfl⟩ : syracuseStep 8761601 = 6571201) B6571201
theorem B5841067 : Blo 2049435 5841067 := bstep (se 1 (by rfl) ⟨4380800, by rfl⟩ : syracuseStep 5841067 = 8761601) B8761601
theorem B7788089 : Blo 2049435 7788089 := bstep (se 2 (by rfl) ⟨2920533, by rfl⟩ : syracuseStep 7788089 = 5841067) B5841067
theorem B5192059 : Blo 2049435 5192059 := bstep (se 1 (by rfl) ⟨3894044, by rfl⟩ : syracuseStep 5192059 = 7788089) B7788089
theorem B6922745 : Blo 2049435 6922745 := bstep (se 2 (by rfl) ⟨2596029, by rfl⟩ : syracuseStep 6922745 = 5192059) B5192059
theorem B4615163 : Blo 2049435 4615163 := bstep (se 1 (by rfl) ⟨3461372, by rfl⟩ : syracuseStep 4615163 = 6922745) B6922745
theorem B3076775 : Blo 2049435 3076775 := bstep (se 1 (by rfl) ⟨2307581, by rfl⟩ : syracuseStep 3076775 = 4615163) B4615163
theorem B2051183 : Blo 2049435 2051183 := bstep (se 1 (by rfl) ⟨1538387, by rfl⟩ : syracuseStep 2051183 = 3076775) B3076775
theorem B3076781 : Blo 2049435 3076781 := bbase (se 3 (by rfl) ⟨576896, by rfl⟩ : syracuseStep 3076781 = 1153793) (by norm_num)
theorem B2051187 : Blo 2049435 2051187 := bstep (se 1 (by rfl) ⟨1538390, by rfl⟩ : syracuseStep 2051187 = 3076781) B3076781
theorem B4615181 : Blo 2049435 4615181 := bbase (se 3 (by rfl) ⟨865346, by rfl⟩ : syracuseStep 4615181 = 1730693) (by norm_num)
theorem B3076787 : Blo 2049435 3076787 := bstep (se 1 (by rfl) ⟨2307590, by rfl⟩ : syracuseStep 3076787 = 4615181) B4615181
theorem B2051191 : Blo 2049435 2051191 := bstep (se 1 (by rfl) ⟨1538393, by rfl⟩ : syracuseStep 2051191 = 3076787) B3076787
theorem B2596045 : Blo 2049435 2596045 := bbase (se 3 (by rfl) ⟨486758, by rfl⟩ : syracuseStep 2596045 = 973517) (by norm_num)
theorem B3461393 : Blo 2049435 3461393 := bstep (se 2 (by rfl) ⟨1298022, by rfl⟩ : syracuseStep 3461393 = 2596045) B2596045
theorem B2307595 : Blo 2049435 2307595 := bstep (se 1 (by rfl) ⟨1730696, by rfl⟩ : syracuseStep 2307595 = 3461393) B3461393
theorem B3076793 : Blo 2049435 3076793 := bstep (se 2 (by rfl) ⟨1153797, by rfl⟩ : syracuseStep 3076793 = 2307595) B2307595
theorem B2051195 : Blo 2049435 2051195 := bstep (se 1 (by rfl) ⟨1538396, by rfl⟩ : syracuseStep 2051195 = 3076793) B3076793
theorem B17090453 : Blo 2049435 17090453 := bbase (se 6 (by rfl) ⟨400557, by rfl⟩ : syracuseStep 17090453 = 801115) (by norm_num)
theorem B11393635 : Blo 2049435 11393635 := bstep (se 1 (by rfl) ⟨8545226, by rfl⟩ : syracuseStep 11393635 = 17090453) B17090453
theorem B15191513 : Blo 2049435 15191513 := bstep (se 2 (by rfl) ⟨5696817, by rfl⟩ : syracuseStep 15191513 = 11393635) B11393635
theorem B10127675 : Blo 2049435 10127675 := bstep (se 1 (by rfl) ⟨7595756, by rfl⟩ : syracuseStep 10127675 = 15191513) B15191513
theorem B6751783 : Blo 2049435 6751783 := bstep (se 1 (by rfl) ⟨5063837, by rfl⟩ : syracuseStep 6751783 = 10127675) B10127675
theorem B9002377 : Blo 2049435 9002377 := bstep (se 2 (by rfl) ⟨3375891, by rfl⟩ : syracuseStep 9002377 = 6751783) B6751783
theorem B48012677 : Blo 2049435 48012677 := bstep (se 4 (by rfl) ⟨4501188, by rfl⟩ : syracuseStep 48012677 = 9002377) B9002377
theorem B32008451 : Blo 2049435 32008451 := bstep (se 1 (by rfl) ⟨24006338, by rfl⟩ : syracuseStep 32008451 = 48012677) B48012677
theorem B85355869 : Blo 2049435 85355869 := bstep (se 3 (by rfl) ⟨16004225, by rfl⟩ : syracuseStep 85355869 = 32008451) B32008451
theorem B113807825 : Blo 2049435 113807825 := bstep (se 2 (by rfl) ⟨42677934, by rfl⟩ : syracuseStep 113807825 = 85355869) B85355869
theorem B75871883 : Blo 2049435 75871883 := bstep (se 1 (by rfl) ⟨56903912, by rfl⟩ : syracuseStep 75871883 = 113807825) B113807825
theorem B50581255 : Blo 2049435 50581255 := bstep (se 1 (by rfl) ⟨37935941, by rfl⟩ : syracuseStep 50581255 = 75871883) B75871883
theorem B67441673 : Blo 2049435 67441673 := bstep (se 2 (by rfl) ⟨25290627, by rfl⟩ : syracuseStep 67441673 = 50581255) B50581255
theorem B179844461 : Blo 2049435 179844461 := bstep (se 3 (by rfl) ⟨33720836, by rfl⟩ : syracuseStep 179844461 = 67441673) B67441673
theorem B119896307 : Blo 2049435 119896307 := bstep (se 1 (by rfl) ⟨89922230, by rfl⟩ : syracuseStep 119896307 = 179844461) B179844461
theorem B79930871 : Blo 2049435 79930871 := bstep (se 1 (by rfl) ⟨59948153, by rfl⟩ : syracuseStep 79930871 = 119896307) B119896307
theorem B53287247 : Blo 2049435 53287247 := bstep (se 1 (by rfl) ⟨39965435, by rfl⟩ : syracuseStep 53287247 = 79930871) B79930871
theorem B35524831 : Blo 2049435 35524831 := bstep (se 1 (by rfl) ⟨26643623, by rfl⟩ : syracuseStep 35524831 = 53287247) B53287247
theorem B47366441 : Blo 2049435 47366441 := bstep (se 2 (by rfl) ⟨17762415, by rfl⟩ : syracuseStep 47366441 = 35524831) B35524831
theorem B31577627 : Blo 2049435 31577627 := bstep (se 1 (by rfl) ⟨23683220, by rfl⟩ : syracuseStep 31577627 = 47366441) B47366441
theorem B21051751 : Blo 2049435 21051751 := bstep (se 1 (by rfl) ⟨15788813, by rfl⟩ : syracuseStep 21051751 = 31577627) B31577627
theorem B28069001 : Blo 2049435 28069001 := bstep (se 2 (by rfl) ⟨10525875, by rfl⟩ : syracuseStep 28069001 = 21051751) B21051751
theorem B18712667 : Blo 2049435 18712667 := bstep (se 1 (by rfl) ⟨14034500, by rfl⟩ : syracuseStep 18712667 = 28069001) B28069001
theorem B49900445 : Blo 2049435 49900445 := bstep (se 3 (by rfl) ⟨9356333, by rfl⟩ : syracuseStep 49900445 = 18712667) B18712667
theorem B33266963 : Blo 2049435 33266963 := bstep (se 1 (by rfl) ⟨24950222, by rfl⟩ : syracuseStep 33266963 = 49900445) B49900445
theorem B22177975 : Blo 2049435 22177975 := bstep (se 1 (by rfl) ⟨16633481, by rfl⟩ : syracuseStep 22177975 = 33266963) B33266963
theorem B29570633 : Blo 2049435 29570633 := bstep (se 2 (by rfl) ⟨11088987, by rfl⟩ : syracuseStep 29570633 = 22177975) B22177975
theorem B19713755 : Blo 2049435 19713755 := bstep (se 1 (by rfl) ⟨14785316, by rfl⟩ : syracuseStep 19713755 = 29570633) B29570633
theorem B13142503 : Blo 2049435 13142503 := bstep (se 1 (by rfl) ⟨9856877, by rfl⟩ : syracuseStep 13142503 = 19713755) B19713755
theorem B17523337 : Blo 2049435 17523337 := bstep (se 2 (by rfl) ⟨6571251, by rfl⟩ : syracuseStep 17523337 = 13142503) B13142503
theorem B23364449 : Blo 2049435 23364449 := bstep (se 2 (by rfl) ⟨8761668, by rfl⟩ : syracuseStep 23364449 = 17523337) B17523337
theorem B15576299 : Blo 2049435 15576299 := bstep (se 1 (by rfl) ⟨11682224, by rfl⟩ : syracuseStep 15576299 = 23364449) B23364449
theorem B10384199 : Blo 2049435 10384199 := bstep (se 1 (by rfl) ⟨7788149, by rfl⟩ : syracuseStep 10384199 = 15576299) B15576299
theorem B6922799 : Blo 2049435 6922799 := bstep (se 1 (by rfl) ⟨5192099, by rfl⟩ : syracuseStep 6922799 = 10384199) B10384199
theorem B4615199 : Blo 2049435 4615199 := bstep (se 1 (by rfl) ⟨3461399, by rfl⟩ : syracuseStep 4615199 = 6922799) B6922799
theorem B3076799 : Blo 2049435 3076799 := bstep (se 1 (by rfl) ⟨2307599, by rfl⟩ : syracuseStep 3076799 = 4615199) B4615199
theorem B2051199 : Blo 2049435 2051199 := bstep (se 1 (by rfl) ⟨1538399, by rfl⟩ : syracuseStep 2051199 = 3076799) B3076799
theorem B3076805 : Blo 2049435 3076805 := bbase (se 4 (by rfl) ⟨288450, by rfl⟩ : syracuseStep 3076805 = 576901) (by norm_num)
theorem B2051203 : Blo 2049435 2051203 := bstep (se 1 (by rfl) ⟨1538402, by rfl⟩ : syracuseStep 2051203 = 3076805) B3076805
theorem B3461413 : Blo 2049435 3461413 := bbase (se 4 (by rfl) ⟨324507, by rfl⟩ : syracuseStep 3461413 = 649015) (by norm_num)
theorem B4615217 : Blo 2049435 4615217 := bstep (se 2 (by rfl) ⟨1730706, by rfl⟩ : syracuseStep 4615217 = 3461413) B3461413
theorem B3076811 : Blo 2049435 3076811 := bstep (se 1 (by rfl) ⟨2307608, by rfl⟩ : syracuseStep 3076811 = 4615217) B4615217
theorem B2051207 : Blo 2049435 2051207 := bstep (se 1 (by rfl) ⟨1538405, by rfl⟩ : syracuseStep 2051207 = 3076811) B3076811
theorem B2307613 : Blo 2049435 2307613 := bbase (se 3 (by rfl) ⟨432677, by rfl⟩ : syracuseStep 2307613 = 865355) (by norm_num)
theorem B3076817 : Blo 2049435 3076817 := bstep (se 2 (by rfl) ⟨1153806, by rfl⟩ : syracuseStep 3076817 = 2307613) B2307613
theorem B2051211 : Blo 2049435 2051211 := bstep (se 1 (by rfl) ⟨1538408, by rfl⟩ : syracuseStep 2051211 = 3076817) B3076817
theorem B6922853 : Blo 2049435 6922853 := bbase (se 4 (by rfl) ⟨649017, by rfl⟩ : syracuseStep 6922853 = 1298035) (by norm_num)
theorem B4615235 : Blo 2049435 4615235 := bstep (se 1 (by rfl) ⟨3461426, by rfl⟩ : syracuseStep 4615235 = 6922853) B6922853
theorem B3076823 : Blo 2049435 3076823 := bstep (se 1 (by rfl) ⟨2307617, by rfl⟩ : syracuseStep 3076823 = 4615235) B4615235
theorem B2051215 : Blo 2049435 2051215 := bstep (se 1 (by rfl) ⟨1538411, by rfl⟩ : syracuseStep 2051215 = 3076823) B3076823
theorem B3076829 : Blo 2049435 3076829 := bbase (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) (by norm_num)
theorem B2051219 : Blo 2049435 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B4615253 : Blo 2049435 4615253 := bbase (se 8 (by rfl) ⟨27042, by rfl⟩ : syracuseStep 4615253 = 54085) (by norm_num)
theorem B3076835 : Blo 2049435 3076835 := bstep (se 1 (by rfl) ⟨2307626, by rfl⟩ : syracuseStep 3076835 = 4615253) B4615253
theorem B2051223 : Blo 2049435 2051223 := bstep (se 1 (by rfl) ⟨1538417, by rfl⟩ : syracuseStep 2051223 = 3076835) B3076835
theorem B7017349 : Blo 2049435 7017349 := bbase (se 4 (by rfl) ⟨657876, by rfl⟩ : syracuseStep 7017349 = 1315753) (by norm_num)
theorem B9356465 : Blo 2049435 9356465 := bstep (se 2 (by rfl) ⟨3508674, by rfl⟩ : syracuseStep 9356465 = 7017349) B7017349
theorem B6237643 : Blo 2049435 6237643 := bstep (se 1 (by rfl) ⟨4678232, by rfl⟩ : syracuseStep 6237643 = 9356465) B9356465
theorem B8316857 : Blo 2049435 8316857 := bstep (se 2 (by rfl) ⟨3118821, by rfl⟩ : syracuseStep 8316857 = 6237643) B6237643
theorem B22178285 : Blo 2049435 22178285 := bstep (se 3 (by rfl) ⟨4158428, by rfl⟩ : syracuseStep 22178285 = 8316857) B8316857
theorem B14785523 : Blo 2049435 14785523 := bstep (se 1 (by rfl) ⟨11089142, by rfl⟩ : syracuseStep 14785523 = 22178285) B22178285
theorem B9857015 : Blo 2049435 9857015 := bstep (se 1 (by rfl) ⟨7392761, by rfl⟩ : syracuseStep 9857015 = 14785523) B14785523
theorem B6571343 : Blo 2049435 6571343 := bstep (se 1 (by rfl) ⟨4928507, by rfl⟩ : syracuseStep 6571343 = 9857015) B9857015
theorem B4380895 : Blo 2049435 4380895 := bstep (se 1 (by rfl) ⟨3285671, by rfl⟩ : syracuseStep 4380895 = 6571343) B6571343
theorem B5841193 : Blo 2049435 5841193 := bstep (se 2 (by rfl) ⟨2190447, by rfl⟩ : syracuseStep 5841193 = 4380895) B4380895
theorem B7788257 : Blo 2049435 7788257 := bstep (se 2 (by rfl) ⟨2920596, by rfl⟩ : syracuseStep 7788257 = 5841193) B5841193
theorem B5192171 : Blo 2049435 5192171 := bstep (se 1 (by rfl) ⟨3894128, by rfl⟩ : syracuseStep 5192171 = 7788257) B7788257
theorem B3461447 : Blo 2049435 3461447 := bstep (se 1 (by rfl) ⟨2596085, by rfl⟩ : syracuseStep 3461447 = 5192171) B5192171
theorem B2307631 : Blo 2049435 2307631 := bstep (se 1 (by rfl) ⟨1730723, by rfl⟩ : syracuseStep 2307631 = 3461447) B3461447
theorem B3076841 : Blo 2049435 3076841 := bstep (se 2 (by rfl) ⟨1153815, by rfl⟩ : syracuseStep 3076841 = 2307631) B2307631
theorem B2051227 : Blo 2049435 2051227 := bstep (se 1 (by rfl) ⟨1538420, by rfl⟩ : syracuseStep 2051227 = 3076841) B3076841
theorem B6237653 : Blo 2049435 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B66534965 : Blo 2049435 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B44356643 : Blo 2049435 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B29571095 : Blo 2049435 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B19714063 : Blo 2049435 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B26285417 : Blo 2049435 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B17523611 : Blo 2049435 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B11682407 : Blo 2049435 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B7788271 : Blo 2049435 7788271 := bstep (se 1 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 7788271 = 11682407) B11682407
theorem B10384361 : Blo 2049435 10384361 := bstep (se 2 (by rfl) ⟨3894135, by rfl⟩ : syracuseStep 10384361 = 7788271) B7788271
theorem B6922907 : Blo 2049435 6922907 := bstep (se 1 (by rfl) ⟨5192180, by rfl⟩ : syracuseStep 6922907 = 10384361) B10384361
theorem B4615271 : Blo 2049435 4615271 := bstep (se 1 (by rfl) ⟨3461453, by rfl⟩ : syracuseStep 4615271 = 6922907) B6922907
theorem B3076847 : Blo 2049435 3076847 := bstep (se 1 (by rfl) ⟨2307635, by rfl⟩ : syracuseStep 3076847 = 4615271) B4615271
theorem B2051231 : Blo 2049435 2051231 := bstep (se 1 (by rfl) ⟨1538423, by rfl⟩ : syracuseStep 2051231 = 3076847) B3076847
theorem B3076853 : Blo 2049435 3076853 := bbase (se 5 (by rfl) ⟨144227, by rfl⟩ : syracuseStep 3076853 = 288455) (by norm_num)
theorem B2051235 : Blo 2049435 2051235 := bstep (se 1 (by rfl) ⟨1538426, by rfl⟩ : syracuseStep 2051235 = 3076853) B3076853
theorem B6571381 : Blo 2049435 6571381 := bbase (se 5 (by rfl) ⟨308033, by rfl⟩ : syracuseStep 6571381 = 616067) (by norm_num)
theorem B8761841 : Blo 2049435 8761841 := bstep (se 2 (by rfl) ⟨3285690, by rfl⟩ : syracuseStep 8761841 = 6571381) B6571381
theorem B5841227 : Blo 2049435 5841227 := bstep (se 1 (by rfl) ⟨4380920, by rfl⟩ : syracuseStep 5841227 = 8761841) B8761841
theorem B3894151 : Blo 2049435 3894151 := bstep (se 1 (by rfl) ⟨2920613, by rfl⟩ : syracuseStep 3894151 = 5841227) B5841227
theorem B5192201 : Blo 2049435 5192201 := bstep (se 2 (by rfl) ⟨1947075, by rfl⟩ : syracuseStep 5192201 = 3894151) B3894151
theorem B3461467 : Blo 2049435 3461467 := bstep (se 1 (by rfl) ⟨2596100, by rfl⟩ : syracuseStep 3461467 = 5192201) B5192201
theorem B4615289 : Blo 2049435 4615289 := bstep (se 2 (by rfl) ⟨1730733, by rfl⟩ : syracuseStep 4615289 = 3461467) B3461467
theorem B3076859 : Blo 2049435 3076859 := bstep (se 1 (by rfl) ⟨2307644, by rfl⟩ : syracuseStep 3076859 = 4615289) B4615289
theorem B2051239 : Blo 2049435 2051239 := bstep (se 1 (by rfl) ⟨1538429, by rfl⟩ : syracuseStep 2051239 = 3076859) B3076859
theorem B2307649 : Blo 2049435 2307649 := bbase (se 2 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 2307649 = 1730737) (by norm_num)
theorem B3076865 : Blo 2049435 3076865 := bstep (se 2 (by rfl) ⟨1153824, by rfl⟩ : syracuseStep 3076865 = 2307649) B2307649
theorem B2051243 : Blo 2049435 2051243 := bstep (se 1 (by rfl) ⟨1538432, by rfl⟩ : syracuseStep 2051243 = 3076865) B3076865
theorem B5192221 : Blo 2049435 5192221 := bbase (se 3 (by rfl) ⟨973541, by rfl⟩ : syracuseStep 5192221 = 1947083) (by norm_num)
theorem B6922961 : Blo 2049435 6922961 := bstep (se 2 (by rfl) ⟨2596110, by rfl⟩ : syracuseStep 6922961 = 5192221) B5192221
theorem B4615307 : Blo 2049435 4615307 := bstep (se 1 (by rfl) ⟨3461480, by rfl⟩ : syracuseStep 4615307 = 6922961) B6922961
theorem B3076871 : Blo 2049435 3076871 := bstep (se 1 (by rfl) ⟨2307653, by rfl⟩ : syracuseStep 3076871 = 4615307) B4615307
theorem B2051247 : Blo 2049435 2051247 := bstep (se 1 (by rfl) ⟨1538435, by rfl⟩ : syracuseStep 2051247 = 3076871) B3076871
theorem B3076877 : Blo 2049435 3076877 := bbase (se 3 (by rfl) ⟨576914, by rfl⟩ : syracuseStep 3076877 = 1153829) (by norm_num)
theorem B2051251 : Blo 2049435 2051251 := bstep (se 1 (by rfl) ⟨1538438, by rfl⟩ : syracuseStep 2051251 = 3076877) B3076877
theorem B4615325 : Blo 2049435 4615325 := bbase (se 3 (by rfl) ⟨865373, by rfl⟩ : syracuseStep 4615325 = 1730747) (by norm_num)
theorem B3076883 : Blo 2049435 3076883 := bstep (se 1 (by rfl) ⟨2307662, by rfl⟩ : syracuseStep 3076883 = 4615325) B4615325
theorem B2051255 : Blo 2049435 2051255 := bstep (se 1 (by rfl) ⟨1538441, by rfl⟩ : syracuseStep 2051255 = 3076883) B3076883
theorem B3461501 : Blo 2049435 3461501 := bbase (se 3 (by rfl) ⟨649031, by rfl⟩ : syracuseStep 3461501 = 1298063) (by norm_num)
theorem B2307667 : Blo 2049435 2307667 := bstep (se 1 (by rfl) ⟨1730750, by rfl⟩ : syracuseStep 2307667 = 3461501) B3461501
theorem B3076889 : Blo 2049435 3076889 := bstep (se 2 (by rfl) ⟨1153833, by rfl⟩ : syracuseStep 3076889 = 2307667) B2307667
theorem B2051259 : Blo 2049435 2051259 := bstep (se 1 (by rfl) ⟨1538444, by rfl⟩ : syracuseStep 2051259 = 3076889) B3076889
theorem B3696445 : Blo 2049435 3696445 := bbase (se 3 (by rfl) ⟨693083, by rfl⟩ : syracuseStep 3696445 = 1386167) (by norm_num)
theorem B4928593 : Blo 2049435 4928593 := bstep (se 2 (by rfl) ⟨1848222, by rfl⟩ : syracuseStep 4928593 = 3696445) B3696445
theorem B6571457 : Blo 2049435 6571457 := bstep (se 2 (by rfl) ⟨2464296, by rfl⟩ : syracuseStep 6571457 = 4928593) B4928593
theorem B4380971 : Blo 2049435 4380971 := bstep (se 1 (by rfl) ⟨3285728, by rfl⟩ : syracuseStep 4380971 = 6571457) B6571457
theorem B11682589 : Blo 2049435 11682589 := bstep (se 3 (by rfl) ⟨2190485, by rfl⟩ : syracuseStep 11682589 = 4380971) B4380971
theorem B15576785 : Blo 2049435 15576785 := bstep (se 2 (by rfl) ⟨5841294, by rfl⟩ : syracuseStep 15576785 = 11682589) B11682589
theorem B10384523 : Blo 2049435 10384523 := bstep (se 1 (by rfl) ⟨7788392, by rfl⟩ : syracuseStep 10384523 = 15576785) B15576785
theorem B6923015 : Blo 2049435 6923015 := bstep (se 1 (by rfl) ⟨5192261, by rfl⟩ : syracuseStep 6923015 = 10384523) B10384523
theorem B4615343 : Blo 2049435 4615343 := bstep (se 1 (by rfl) ⟨3461507, by rfl⟩ : syracuseStep 4615343 = 6923015) B6923015
theorem B3076895 : Blo 2049435 3076895 := bstep (se 1 (by rfl) ⟨2307671, by rfl⟩ : syracuseStep 3076895 = 4615343) B4615343
theorem B2051263 : Blo 2049435 2051263 := bstep (se 1 (by rfl) ⟨1538447, by rfl⟩ : syracuseStep 2051263 = 3076895) B3076895
theorem B3076901 : Blo 2049435 3076901 := bbase (se 4 (by rfl) ⟨288459, by rfl⟩ : syracuseStep 3076901 = 576919) (by norm_num)
theorem B2051267 : Blo 2049435 2051267 := bstep (se 1 (by rfl) ⟨1538450, by rfl⟩ : syracuseStep 2051267 = 3076901) B3076901
theorem B2596141 : Blo 2049435 2596141 := bbase (se 3 (by rfl) ⟨486776, by rfl⟩ : syracuseStep 2596141 = 973553) (by norm_num)
theorem B3461521 : Blo 2049435 3461521 := bstep (se 2 (by rfl) ⟨1298070, by rfl⟩ : syracuseStep 3461521 = 2596141) B2596141
theorem B4615361 : Blo 2049435 4615361 := bstep (se 2 (by rfl) ⟨1730760, by rfl⟩ : syracuseStep 4615361 = 3461521) B3461521
theorem B3076907 : Blo 2049435 3076907 := bstep (se 1 (by rfl) ⟨2307680, by rfl⟩ : syracuseStep 3076907 = 4615361) B4615361
theorem B2051271 : Blo 2049435 2051271 := bstep (se 1 (by rfl) ⟨1538453, by rfl⟩ : syracuseStep 2051271 = 3076907) B3076907
theorem B2307685 : Blo 2049435 2307685 := bbase (se 4 (by rfl) ⟨216345, by rfl⟩ : syracuseStep 2307685 = 432691) (by norm_num)
theorem B3076913 : Blo 2049435 3076913 := bstep (se 2 (by rfl) ⟨1153842, by rfl⟩ : syracuseStep 3076913 = 2307685) B2307685
theorem B2051275 : Blo 2049435 2051275 := bstep (se 1 (by rfl) ⟨1538456, by rfl⟩ : syracuseStep 2051275 = 3076913) B3076913
theorem B4440781 : Blo 2049435 4440781 := bbase (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) (by norm_num)
theorem B5921041 : Blo 2049435 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B7894721 : Blo 2049435 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B5263147 : Blo 2049435 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B7017529 : Blo 2049435 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B9356705 : Blo 2049435 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B6237803 : Blo 2049435 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B4158535 : Blo 2049435 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B5544713 : Blo 2049435 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B3696475 : Blo 2049435 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B4928633 : Blo 2049435 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B3285755 : Blo 2049435 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B2190503 : Blo 2049435 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B5841341 : Blo 2049435 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B3894227 : Blo 2049435 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B2596151 : Blo 2049435 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B6923069 : Blo 2049435 6923069 := bstep (se 3 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 6923069 = 2596151) B2596151
theorem B4615379 : Blo 2049435 4615379 := bstep (se 1 (by rfl) ⟨3461534, by rfl⟩ : syracuseStep 4615379 = 6923069) B6923069
theorem B3076919 : Blo 2049435 3076919 := bstep (se 1 (by rfl) ⟨2307689, by rfl⟩ : syracuseStep 3076919 = 4615379) B4615379
theorem B2051279 : Blo 2049435 2051279 := bstep (se 1 (by rfl) ⟨1538459, by rfl⟩ : syracuseStep 2051279 = 3076919) B3076919
theorem B3076925 : Blo 2049435 3076925 := bbase (se 3 (by rfl) ⟨576923, by rfl⟩ : syracuseStep 3076925 = 1153847) (by norm_num)
theorem B2051283 : Blo 2049435 2051283 := bstep (se 1 (by rfl) ⟨1538462, by rfl⟩ : syracuseStep 2051283 = 3076925) B3076925
theorem B4615397 : Blo 2049435 4615397 := bbase (se 4 (by rfl) ⟨432693, by rfl⟩ : syracuseStep 4615397 = 865387) (by norm_num)
theorem B3076931 : Blo 2049435 3076931 := bstep (se 1 (by rfl) ⟨2307698, by rfl⟩ : syracuseStep 3076931 = 4615397) B4615397
theorem B2051287 : Blo 2049435 2051287 := bstep (se 1 (by rfl) ⟨1538465, by rfl⟩ : syracuseStep 2051287 = 3076931) B3076931
theorem B5192333 : Blo 2049435 5192333 := bbase (se 3 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 5192333 = 1947125) (by norm_num)
theorem B3461555 : Blo 2049435 3461555 := bstep (se 1 (by rfl) ⟨2596166, by rfl⟩ : syracuseStep 3461555 = 5192333) B5192333
theorem B2307703 : Blo 2049435 2307703 := bstep (se 1 (by rfl) ⟨1730777, by rfl⟩ : syracuseStep 2307703 = 3461555) B3461555
theorem B3076937 : Blo 2049435 3076937 := bstep (se 2 (by rfl) ⟨1153851, by rfl⟩ : syracuseStep 3076937 = 2307703) B2307703
theorem B2051291 : Blo 2049435 2051291 := bstep (se 1 (by rfl) ⟨1538468, by rfl⟩ : syracuseStep 2051291 = 3076937) B3076937
theorem B2920693 : Blo 2049435 2920693 := bbase (se 5 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 2920693 = 273815) (by norm_num)
theorem B3894257 : Blo 2049435 3894257 := bstep (se 2 (by rfl) ⟨1460346, by rfl⟩ : syracuseStep 3894257 = 2920693) B2920693
theorem B10384685 : Blo 2049435 10384685 := bstep (se 3 (by rfl) ⟨1947128, by rfl⟩ : syracuseStep 10384685 = 3894257) B3894257
theorem B6923123 : Blo 2049435 6923123 := bstep (se 1 (by rfl) ⟨5192342, by rfl⟩ : syracuseStep 6923123 = 10384685) B10384685
theorem B4615415 : Blo 2049435 4615415 := bstep (se 1 (by rfl) ⟨3461561, by rfl⟩ : syracuseStep 4615415 = 6923123) B6923123
theorem B3076943 : Blo 2049435 3076943 := bstep (se 1 (by rfl) ⟨2307707, by rfl⟩ : syracuseStep 3076943 = 4615415) B4615415
theorem B2051295 : Blo 2049435 2051295 := bstep (se 1 (by rfl) ⟨1538471, by rfl⟩ : syracuseStep 2051295 = 3076943) B3076943
theorem B3076949 : Blo 2049435 3076949 := bbase (se 9 (by rfl) ⟨9014, by rfl⟩ : syracuseStep 3076949 = 18029) (by norm_num)
theorem B2051299 : Blo 2049435 2051299 := bstep (se 1 (by rfl) ⟨1538474, by rfl⟩ : syracuseStep 2051299 = 3076949) B3076949
theorem B2464345 : Blo 2049435 2464345 := bbase (se 2 (by rfl) ⟨924129, by rfl⟩ : syracuseStep 2464345 = 1848259) (by norm_num)
theorem B3285793 : Blo 2049435 3285793 := bstep (se 2 (by rfl) ⟨1232172, by rfl⟩ : syracuseStep 3285793 = 2464345) B2464345
theorem B4381057 : Blo 2049435 4381057 := bstep (se 2 (by rfl) ⟨1642896, by rfl⟩ : syracuseStep 4381057 = 3285793) B3285793
theorem B5841409 : Blo 2049435 5841409 := bstep (se 2 (by rfl) ⟨2190528, by rfl⟩ : syracuseStep 5841409 = 4381057) B4381057
theorem B7788545 : Blo 2049435 7788545 := bstep (se 2 (by rfl) ⟨2920704, by rfl⟩ : syracuseStep 7788545 = 5841409) B5841409
theorem B5192363 : Blo 2049435 5192363 := bstep (se 1 (by rfl) ⟨3894272, by rfl⟩ : syracuseStep 5192363 = 7788545) B7788545
theorem B3461575 : Blo 2049435 3461575 := bstep (se 1 (by rfl) ⟨2596181, by rfl⟩ : syracuseStep 3461575 = 5192363) B5192363
theorem B4615433 : Blo 2049435 4615433 := bstep (se 2 (by rfl) ⟨1730787, by rfl⟩ : syracuseStep 4615433 = 3461575) B3461575
theorem B3076955 : Blo 2049435 3076955 := bstep (se 1 (by rfl) ⟨2307716, by rfl⟩ : syracuseStep 3076955 = 4615433) B4615433
theorem B2051303 : Blo 2049435 2051303 := bstep (se 1 (by rfl) ⟨1538477, by rfl⟩ : syracuseStep 2051303 = 3076955) B3076955
theorem B2307721 : Blo 2049435 2307721 := bbase (se 2 (by rfl) ⟨865395, by rfl⟩ : syracuseStep 2307721 = 1730791) (by norm_num)
theorem B3076961 : Blo 2049435 3076961 := bstep (se 2 (by rfl) ⟨1153860, by rfl⟩ : syracuseStep 3076961 = 2307721) B2307721
theorem B2051307 : Blo 2049435 2051307 := bstep (se 1 (by rfl) ⟨1538480, by rfl⟩ : syracuseStep 2051307 = 3076961) B3076961
theorem B2631613 : Blo 2049435 2631613 := bbase (se 3 (by rfl) ⟨493427, by rfl⟩ : syracuseStep 2631613 = 986855) (by norm_num)
theorem B3508817 : Blo 2049435 3508817 := bstep (se 2 (by rfl) ⟨1315806, by rfl⟩ : syracuseStep 3508817 = 2631613) B2631613
theorem B9356845 : Blo 2049435 9356845 := bstep (se 3 (by rfl) ⟨1754408, by rfl⟩ : syracuseStep 9356845 = 3508817) B3508817
theorem B12475793 : Blo 2049435 12475793 := bstep (se 2 (by rfl) ⟨4678422, by rfl⟩ : syracuseStep 12475793 = 9356845) B9356845
theorem B33268781 : Blo 2049435 33268781 := bstep (se 3 (by rfl) ⟨6237896, by rfl⟩ : syracuseStep 33268781 = 12475793) B12475793
theorem B22179187 : Blo 2049435 22179187 := bstep (se 1 (by rfl) ⟨16634390, by rfl⟩ : syracuseStep 22179187 = 33268781) B33268781
theorem B29572249 : Blo 2049435 29572249 := bstep (se 2 (by rfl) ⟨11089593, by rfl⟩ : syracuseStep 29572249 = 22179187) B22179187
theorem B39429665 : Blo 2049435 39429665 := bstep (se 2 (by rfl) ⟨14786124, by rfl⟩ : syracuseStep 39429665 = 29572249) B29572249
theorem B26286443 : Blo 2049435 26286443 := bstep (se 1 (by rfl) ⟨19714832, by rfl⟩ : syracuseStep 26286443 = 39429665) B39429665
theorem B17524295 : Blo 2049435 17524295 := bstep (se 1 (by rfl) ⟨13143221, by rfl⟩ : syracuseStep 17524295 = 26286443) B26286443
theorem B11682863 : Blo 2049435 11682863 := bstep (se 1 (by rfl) ⟨8762147, by rfl⟩ : syracuseStep 11682863 = 17524295) B17524295
theorem B7788575 : Blo 2049435 7788575 := bstep (se 1 (by rfl) ⟨5841431, by rfl⟩ : syracuseStep 7788575 = 11682863) B11682863
theorem B5192383 : Blo 2049435 5192383 := bstep (se 1 (by rfl) ⟨3894287, by rfl⟩ : syracuseStep 5192383 = 7788575) B7788575
theorem B6923177 : Blo 2049435 6923177 := bstep (se 2 (by rfl) ⟨2596191, by rfl⟩ : syracuseStep 6923177 = 5192383) B5192383
theorem B4615451 : Blo 2049435 4615451 := bstep (se 1 (by rfl) ⟨3461588, by rfl⟩ : syracuseStep 4615451 = 6923177) B6923177
theorem B3076967 : Blo 2049435 3076967 := bstep (se 1 (by rfl) ⟨2307725, by rfl⟩ : syracuseStep 3076967 = 4615451) B4615451
theorem B2051311 : Blo 2049435 2051311 := bstep (se 1 (by rfl) ⟨1538483, by rfl⟩ : syracuseStep 2051311 = 3076967) B3076967
theorem B3076973 : Blo 2049435 3076973 := bbase (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) (by norm_num)
theorem B2051315 : Blo 2049435 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B4615469 : Blo 2049435 4615469 := bbase (se 3 (by rfl) ⟨865400, by rfl⟩ : syracuseStep 4615469 = 1730801) (by norm_num)
theorem B3076979 : Blo 2049435 3076979 := bstep (se 1 (by rfl) ⟨2307734, by rfl⟩ : syracuseStep 3076979 = 4615469) B4615469
theorem B2051319 : Blo 2049435 2051319 := bstep (se 1 (by rfl) ⟨1538489, by rfl⟩ : syracuseStep 2051319 = 3076979) B3076979
theorem B9857477 : Blo 2049435 9857477 := bbase (se 4 (by rfl) ⟨924138, by rfl⟩ : syracuseStep 9857477 = 1848277) (by norm_num)
theorem B6571651 : Blo 2049435 6571651 := bstep (se 1 (by rfl) ⟨4928738, by rfl⟩ : syracuseStep 6571651 = 9857477) B9857477
theorem B8762201 : Blo 2049435 8762201 := bstep (se 2 (by rfl) ⟨3285825, by rfl⟩ : syracuseStep 8762201 = 6571651) B6571651
theorem B5841467 : Blo 2049435 5841467 := bstep (se 1 (by rfl) ⟨4381100, by rfl⟩ : syracuseStep 5841467 = 8762201) B8762201
theorem B3894311 : Blo 2049435 3894311 := bstep (se 1 (by rfl) ⟨2920733, by rfl⟩ : syracuseStep 3894311 = 5841467) B5841467
theorem B2596207 : Blo 2049435 2596207 := bstep (se 1 (by rfl) ⟨1947155, by rfl⟩ : syracuseStep 2596207 = 3894311) B3894311
theorem B3461609 : Blo 2049435 3461609 := bstep (se 2 (by rfl) ⟨1298103, by rfl⟩ : syracuseStep 3461609 = 2596207) B2596207
theorem B2307739 : Blo 2049435 2307739 := bstep (se 1 (by rfl) ⟨1730804, by rfl⟩ : syracuseStep 2307739 = 3461609) B3461609
theorem B3076985 : Blo 2049435 3076985 := bstep (se 2 (by rfl) ⟨1153869, by rfl⟩ : syracuseStep 3076985 = 2307739) B2307739
theorem B2051323 : Blo 2049435 2051323 := bstep (se 1 (by rfl) ⟨1538492, by rfl⟩ : syracuseStep 2051323 = 3076985) B3076985
theorem B11240981 : Blo 2049435 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B7493987 : Blo 2049435 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B4995991 : Blo 2049435 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B26645285 : Blo 2049435 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B71054093 : Blo 2049435 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B47369395 : Blo 2049435 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B63159193 : Blo 2049435 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B84212257 : Blo 2049435 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B112283009 : Blo 2049435 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B74855339 : Blo 2049435 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B49903559 : Blo 2049435 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B33269039 : Blo 2049435 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B22179359 : Blo 2049435 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B14786239 : Blo 2049435 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B19714985 : Blo 2049435 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B13143323 : Blo 2049435 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B35048861 : Blo 2049435 35048861 := bstep (se 3 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 35048861 = 13143323) B13143323
theorem B23365907 : Blo 2049435 23365907 := bstep (se 1 (by rfl) ⟨17524430, by rfl⟩ : syracuseStep 23365907 = 35048861) B35048861
theorem B15577271 : Blo 2049435 15577271 := bstep (se 1 (by rfl) ⟨11682953, by rfl⟩ : syracuseStep 15577271 = 23365907) B23365907
theorem B10384847 : Blo 2049435 10384847 := bstep (se 1 (by rfl) ⟨7788635, by rfl⟩ : syracuseStep 10384847 = 15577271) B15577271
theorem B6923231 : Blo 2049435 6923231 := bstep (se 1 (by rfl) ⟨5192423, by rfl⟩ : syracuseStep 6923231 = 10384847) B10384847
theorem B4615487 : Blo 2049435 4615487 := bstep (se 1 (by rfl) ⟨3461615, by rfl⟩ : syracuseStep 4615487 = 6923231) B6923231
theorem B3076991 : Blo 2049435 3076991 := bstep (se 1 (by rfl) ⟨2307743, by rfl⟩ : syracuseStep 3076991 = 4615487) B4615487
theorem B2051327 : Blo 2049435 2051327 := bstep (se 1 (by rfl) ⟨1538495, by rfl⟩ : syracuseStep 2051327 = 3076991) B3076991
theorem B3076997 : Blo 2049435 3076997 := bbase (se 4 (by rfl) ⟨288468, by rfl⟩ : syracuseStep 3076997 = 576937) (by norm_num)
theorem B2051331 : Blo 2049435 2051331 := bstep (se 1 (by rfl) ⟨1538498, by rfl⟩ : syracuseStep 2051331 = 3076997) B3076997
theorem B3461629 : Blo 2049435 3461629 := bbase (se 3 (by rfl) ⟨649055, by rfl⟩ : syracuseStep 3461629 = 1298111) (by norm_num)
theorem B4615505 : Blo 2049435 4615505 := bstep (se 2 (by rfl) ⟨1730814, by rfl⟩ : syracuseStep 4615505 = 3461629) B3461629
theorem B3077003 : Blo 2049435 3077003 := bstep (se 1 (by rfl) ⟨2307752, by rfl⟩ : syracuseStep 3077003 = 4615505) B4615505
theorem B2051335 : Blo 2049435 2051335 := bstep (se 1 (by rfl) ⟨1538501, by rfl⟩ : syracuseStep 2051335 = 3077003) B3077003
theorem B2307757 : Blo 2049435 2307757 := bbase (se 3 (by rfl) ⟨432704, by rfl⟩ : syracuseStep 2307757 = 865409) (by norm_num)
theorem B3077009 : Blo 2049435 3077009 := bstep (se 2 (by rfl) ⟨1153878, by rfl⟩ : syracuseStep 3077009 = 2307757) B2307757
theorem B2051339 : Blo 2049435 2051339 := bstep (se 1 (by rfl) ⟨1538504, by rfl⟩ : syracuseStep 2051339 = 3077009) B3077009
theorem B6923285 : Blo 2049435 6923285 := bbase (se 6 (by rfl) ⟨162264, by rfl⟩ : syracuseStep 6923285 = 324529) (by norm_num)
theorem B4615523 : Blo 2049435 4615523 := bstep (se 1 (by rfl) ⟨3461642, by rfl⟩ : syracuseStep 4615523 = 6923285) B6923285
theorem B3077015 : Blo 2049435 3077015 := bstep (se 1 (by rfl) ⟨2307761, by rfl⟩ : syracuseStep 3077015 = 4615523) B4615523
theorem B2051343 : Blo 2049435 2051343 := bstep (se 1 (by rfl) ⟨1538507, by rfl⟩ : syracuseStep 2051343 = 3077015) B3077015
theorem B3077021 : Blo 2049435 3077021 := bbase (se 3 (by rfl) ⟨576941, by rfl⟩ : syracuseStep 3077021 = 1153883) (by norm_num)
theorem B2051347 : Blo 2049435 2051347 := bstep (se 1 (by rfl) ⟨1538510, by rfl⟩ : syracuseStep 2051347 = 3077021) B3077021
theorem B4615541 : Blo 2049435 4615541 := bbase (se 5 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 4615541 = 432707) (by norm_num)
theorem B3077027 : Blo 2049435 3077027 := bstep (se 1 (by rfl) ⟨2307770, by rfl⟩ : syracuseStep 3077027 = 4615541) B4615541
theorem B2051351 : Blo 2049435 2051351 := bstep (se 1 (by rfl) ⟨1538513, by rfl⟩ : syracuseStep 2051351 = 3077027) B3077027
theorem B5544917 : Blo 2049435 5544917 := bbase (se 7 (by rfl) ⟨64979, by rfl⟩ : syracuseStep 5544917 = 129959) (by norm_num)
theorem B3696611 : Blo 2049435 3696611 := bstep (se 1 (by rfl) ⟨2772458, by rfl⟩ : syracuseStep 3696611 = 5544917) B5544917
theorem B9857629 : Blo 2049435 9857629 := bstep (se 3 (by rfl) ⟨1848305, by rfl⟩ : syracuseStep 9857629 = 3696611) B3696611
theorem B13143505 : Blo 2049435 13143505 := bstep (se 2 (by rfl) ⟨4928814, by rfl⟩ : syracuseStep 13143505 = 9857629) B9857629
theorem B17524673 : Blo 2049435 17524673 := bstep (se 2 (by rfl) ⟨6571752, by rfl⟩ : syracuseStep 17524673 = 13143505) B13143505
theorem B11683115 : Blo 2049435 11683115 := bstep (se 1 (by rfl) ⟨8762336, by rfl⟩ : syracuseStep 11683115 = 17524673) B17524673
theorem B7788743 : Blo 2049435 7788743 := bstep (se 1 (by rfl) ⟨5841557, by rfl⟩ : syracuseStep 7788743 = 11683115) B11683115
theorem B5192495 : Blo 2049435 5192495 := bstep (se 1 (by rfl) ⟨3894371, by rfl⟩ : syracuseStep 5192495 = 7788743) B7788743
theorem B3461663 : Blo 2049435 3461663 := bstep (se 1 (by rfl) ⟨2596247, by rfl⟩ : syracuseStep 3461663 = 5192495) B5192495
theorem B2307775 : Blo 2049435 2307775 := bstep (se 1 (by rfl) ⟨1730831, by rfl⟩ : syracuseStep 2307775 = 3461663) B3461663
theorem B3077033 : Blo 2049435 3077033 := bstep (se 2 (by rfl) ⟨1153887, by rfl⟩ : syracuseStep 3077033 = 2307775) B2307775
theorem B2051355 : Blo 2049435 2051355 := bstep (se 1 (by rfl) ⟨1538516, by rfl⟩ : syracuseStep 2051355 = 3077033) B3077033
theorem B7788757 : Blo 2049435 7788757 := bbase (se 7 (by rfl) ⟨91274, by rfl⟩ : syracuseStep 7788757 = 182549) (by norm_num)
theorem B10385009 : Blo 2049435 10385009 := bstep (se 2 (by rfl) ⟨3894378, by rfl⟩ : syracuseStep 10385009 = 7788757) B7788757
theorem B6923339 : Blo 2049435 6923339 := bstep (se 1 (by rfl) ⟨5192504, by rfl⟩ : syracuseStep 6923339 = 10385009) B10385009
theorem B4615559 : Blo 2049435 4615559 := bstep (se 1 (by rfl) ⟨3461669, by rfl⟩ : syracuseStep 4615559 = 6923339) B6923339
theorem B3077039 : Blo 2049435 3077039 := bstep (se 1 (by rfl) ⟨2307779, by rfl⟩ : syracuseStep 3077039 = 4615559) B4615559
theorem B2051359 : Blo 2049435 2051359 := bstep (se 1 (by rfl) ⟨1538519, by rfl⟩ : syracuseStep 2051359 = 3077039) B3077039
theorem B3077045 : Blo 2049435 3077045 := bbase (se 5 (by rfl) ⟨144236, by rfl⟩ : syracuseStep 3077045 = 288473) (by norm_num)
theorem B2051363 : Blo 2049435 2051363 := bstep (se 1 (by rfl) ⟨1538522, by rfl⟩ : syracuseStep 2051363 = 3077045) B3077045
theorem B5192525 : Blo 2049435 5192525 := bbase (se 3 (by rfl) ⟨973598, by rfl⟩ : syracuseStep 5192525 = 1947197) (by norm_num)
theorem B3461683 : Blo 2049435 3461683 := bstep (se 1 (by rfl) ⟨2596262, by rfl⟩ : syracuseStep 3461683 = 5192525) B5192525
theorem B4615577 : Blo 2049435 4615577 := bstep (se 2 (by rfl) ⟨1730841, by rfl⟩ : syracuseStep 4615577 = 3461683) B3461683
theorem B3077051 : Blo 2049435 3077051 := bstep (se 1 (by rfl) ⟨2307788, by rfl⟩ : syracuseStep 3077051 = 4615577) B4615577
theorem B2051367 : Blo 2049435 2051367 := bstep (se 1 (by rfl) ⟨1538525, by rfl⟩ : syracuseStep 2051367 = 3077051) B3077051
theorem B2307793 : Blo 2049435 2307793 := bbase (se 2 (by rfl) ⟨865422, by rfl⟩ : syracuseStep 2307793 = 1730845) (by norm_num)
theorem B3077057 : Blo 2049435 3077057 := bstep (se 2 (by rfl) ⟨1153896, by rfl⟩ : syracuseStep 3077057 = 2307793) B2307793
theorem B2051371 : Blo 2049435 2051371 := bstep (se 1 (by rfl) ⟨1538528, by rfl⟩ : syracuseStep 2051371 = 3077057) B3077057
theorem B2339285 : Blo 2049435 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B24952373 : Blo 2049435 24952373 := bstep (se 5 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 24952373 = 2339285) B2339285
theorem B16634915 : Blo 2049435 16634915 := bstep (se 1 (by rfl) ⟨12476186, by rfl⟩ : syracuseStep 16634915 = 24952373) B24952373
theorem B11089943 : Blo 2049435 11089943 := bstep (se 1 (by rfl) ⟨8317457, by rfl⟩ : syracuseStep 11089943 = 16634915) B16634915
theorem B7393295 : Blo 2049435 7393295 := bstep (se 1 (by rfl) ⟨5544971, by rfl⟩ : syracuseStep 7393295 = 11089943) B11089943
theorem B4928863 : Blo 2049435 4928863 := bstep (se 1 (by rfl) ⟨3696647, by rfl⟩ : syracuseStep 4928863 = 7393295) B7393295
theorem B6571817 : Blo 2049435 6571817 := bstep (se 2 (by rfl) ⟨2464431, by rfl⟩ : syracuseStep 6571817 = 4928863) B4928863
theorem B4381211 : Blo 2049435 4381211 := bstep (se 1 (by rfl) ⟨3285908, by rfl⟩ : syracuseStep 4381211 = 6571817) B6571817
theorem B2920807 : Blo 2049435 2920807 := bstep (se 1 (by rfl) ⟨2190605, by rfl⟩ : syracuseStep 2920807 = 4381211) B4381211
theorem B3894409 : Blo 2049435 3894409 := bstep (se 2 (by rfl) ⟨1460403, by rfl⟩ : syracuseStep 3894409 = 2920807) B2920807
theorem B5192545 : Blo 2049435 5192545 := bstep (se 2 (by rfl) ⟨1947204, by rfl⟩ : syracuseStep 5192545 = 3894409) B3894409
theorem B6923393 : Blo 2049435 6923393 := bstep (se 2 (by rfl) ⟨2596272, by rfl⟩ : syracuseStep 6923393 = 5192545) B5192545
theorem B4615595 : Blo 2049435 4615595 := bstep (se 1 (by rfl) ⟨3461696, by rfl⟩ : syracuseStep 4615595 = 6923393) B6923393
theorem B3077063 : Blo 2049435 3077063 := bstep (se 1 (by rfl) ⟨2307797, by rfl⟩ : syracuseStep 3077063 = 4615595) B4615595
theorem B2051375 : Blo 2049435 2051375 := bstep (se 1 (by rfl) ⟨1538531, by rfl⟩ : syracuseStep 2051375 = 3077063) B3077063
theorem B3077069 : Blo 2049435 3077069 := bbase (se 3 (by rfl) ⟨576950, by rfl⟩ : syracuseStep 3077069 = 1153901) (by norm_num)
theorem B2051379 : Blo 2049435 2051379 := bstep (se 1 (by rfl) ⟨1538534, by rfl⟩ : syracuseStep 2051379 = 3077069) B3077069
theorem B4615613 : Blo 2049435 4615613 := bbase (se 3 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 4615613 = 1730855) (by norm_num)
theorem B3077075 : Blo 2049435 3077075 := bstep (se 1 (by rfl) ⟨2307806, by rfl⟩ : syracuseStep 3077075 = 4615613) B4615613
theorem B2051383 : Blo 2049435 2051383 := bstep (se 1 (by rfl) ⟨1538537, by rfl⟩ : syracuseStep 2051383 = 3077075) B3077075
theorem B3461717 : Blo 2049435 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B2307811 : Blo 2049435 2307811 := bstep (se 1 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 2307811 = 3461717) B3461717
theorem B3077081 : Blo 2049435 3077081 := bstep (se 2 (by rfl) ⟨1153905, by rfl⟩ : syracuseStep 3077081 = 2307811) B2307811
theorem B2051387 : Blo 2049435 2051387 := bstep (se 1 (by rfl) ⟨1538540, by rfl⟩ : syracuseStep 2051387 = 3077081) B3077081
theorem B3556829 : Blo 2049435 3556829 := bbase (se 3 (by rfl) ⟨666905, by rfl⟩ : syracuseStep 3556829 = 1333811) (by norm_num)
theorem B9484877 : Blo 2049435 9484877 := bstep (se 3 (by rfl) ⟨1778414, by rfl⟩ : syracuseStep 9484877 = 3556829) B3556829
theorem B25293005 : Blo 2049435 25293005 := bstep (se 3 (by rfl) ⟨4742438, by rfl⟩ : syracuseStep 25293005 = 9484877) B9484877
theorem B16862003 : Blo 2049435 16862003 := bstep (se 1 (by rfl) ⟨12646502, by rfl⟩ : syracuseStep 16862003 = 25293005) B25293005
theorem B11241335 : Blo 2049435 11241335 := bstep (se 1 (by rfl) ⟨8431001, by rfl⟩ : syracuseStep 11241335 = 16862003) B16862003
theorem B7494223 : Blo 2049435 7494223 := bstep (se 1 (by rfl) ⟨5620667, by rfl⟩ : syracuseStep 7494223 = 11241335) B11241335
theorem B9992297 : Blo 2049435 9992297 := bstep (se 2 (by rfl) ⟨3747111, by rfl⟩ : syracuseStep 9992297 = 7494223) B7494223
theorem B6661531 : Blo 2049435 6661531 := bstep (se 1 (by rfl) ⟨4996148, by rfl⟩ : syracuseStep 6661531 = 9992297) B9992297
theorem B35528165 : Blo 2049435 35528165 := bstep (se 4 (by rfl) ⟨3330765, by rfl⟩ : syracuseStep 35528165 = 6661531) B6661531
theorem B23685443 : Blo 2049435 23685443 := bstep (se 1 (by rfl) ⟨17764082, by rfl⟩ : syracuseStep 23685443 = 35528165) B35528165
theorem B15790295 : Blo 2049435 15790295 := bstep (se 1 (by rfl) ⟨11842721, by rfl⟩ : syracuseStep 15790295 = 23685443) B23685443
theorem B10526863 : Blo 2049435 10526863 := bstep (se 1 (by rfl) ⟨7895147, by rfl⟩ : syracuseStep 10526863 = 15790295) B15790295
theorem B14035817 : Blo 2049435 14035817 := bstep (se 2 (by rfl) ⟨5263431, by rfl⟩ : syracuseStep 14035817 = 10526863) B10526863
theorem B9357211 : Blo 2049435 9357211 := bstep (se 1 (by rfl) ⟨7017908, by rfl⟩ : syracuseStep 9357211 = 14035817) B14035817
theorem B12476281 : Blo 2049435 12476281 := bstep (se 2 (by rfl) ⟨4678605, by rfl⟩ : syracuseStep 12476281 = 9357211) B9357211
theorem B16635041 : Blo 2049435 16635041 := bstep (se 2 (by rfl) ⟨6238140, by rfl⟩ : syracuseStep 16635041 = 12476281) B12476281
theorem B11090027 : Blo 2049435 11090027 := bstep (se 1 (by rfl) ⟨8317520, by rfl⟩ : syracuseStep 11090027 = 16635041) B16635041
theorem B7393351 : Blo 2049435 7393351 := bstep (se 1 (by rfl) ⟨5545013, by rfl⟩ : syracuseStep 7393351 = 11090027) B11090027
theorem B9857801 : Blo 2049435 9857801 := bstep (se 2 (by rfl) ⟨3696675, by rfl⟩ : syracuseStep 9857801 = 7393351) B7393351
theorem B6571867 : Blo 2049435 6571867 := bstep (se 1 (by rfl) ⟨4928900, by rfl⟩ : syracuseStep 6571867 = 9857801) B9857801
theorem B8762489 : Blo 2049435 8762489 := bstep (se 2 (by rfl) ⟨3285933, by rfl⟩ : syracuseStep 8762489 = 6571867) B6571867
theorem B5841659 : Blo 2049435 5841659 := bstep (se 1 (by rfl) ⟨4381244, by rfl⟩ : syracuseStep 5841659 = 8762489) B8762489
theorem B15577757 : Blo 2049435 15577757 := bstep (se 3 (by rfl) ⟨2920829, by rfl⟩ : syracuseStep 15577757 = 5841659) B5841659
theorem B10385171 : Blo 2049435 10385171 := bstep (se 1 (by rfl) ⟨7788878, by rfl⟩ : syracuseStep 10385171 = 15577757) B15577757
theorem B6923447 : Blo 2049435 6923447 := bstep (se 1 (by rfl) ⟨5192585, by rfl⟩ : syracuseStep 6923447 = 10385171) B10385171
theorem B4615631 : Blo 2049435 4615631 := bstep (se 1 (by rfl) ⟨3461723, by rfl⟩ : syracuseStep 4615631 = 6923447) B6923447
theorem B3077087 : Blo 2049435 3077087 := bstep (se 1 (by rfl) ⟨2307815, by rfl⟩ : syracuseStep 3077087 = 4615631) B4615631
theorem B2051391 : Blo 2049435 2051391 := bstep (se 1 (by rfl) ⟨1538543, by rfl⟩ : syracuseStep 2051391 = 3077087) B3077087
theorem B3077093 : Blo 2049435 3077093 := bbase (se 4 (by rfl) ⟨288477, by rfl⟩ : syracuseStep 3077093 = 576955) (by norm_num)
theorem B2051395 : Blo 2049435 2051395 := bstep (se 1 (by rfl) ⟨1538546, by rfl⟩ : syracuseStep 2051395 = 3077093) B3077093
theorem B2079389 : Blo 2049435 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B5545037 : Blo 2049435 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B3696691 : Blo 2049435 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B4928921 : Blo 2049435 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B3285947 : Blo 2049435 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B8762525 : Blo 2049435 8762525 := bstep (se 3 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 8762525 = 3285947) B3285947
theorem B5841683 : Blo 2049435 5841683 := bstep (se 1 (by rfl) ⟨4381262, by rfl⟩ : syracuseStep 5841683 = 8762525) B8762525
theorem B3894455 : Blo 2049435 3894455 := bstep (se 1 (by rfl) ⟨2920841, by rfl⟩ : syracuseStep 3894455 = 5841683) B5841683
theorem B2596303 : Blo 2049435 2596303 := bstep (se 1 (by rfl) ⟨1947227, by rfl⟩ : syracuseStep 2596303 = 3894455) B3894455
theorem B3461737 : Blo 2049435 3461737 := bstep (se 2 (by rfl) ⟨1298151, by rfl⟩ : syracuseStep 3461737 = 2596303) B2596303
theorem B4615649 : Blo 2049435 4615649 := bstep (se 2 (by rfl) ⟨1730868, by rfl⟩ : syracuseStep 4615649 = 3461737) B3461737
theorem B3077099 : Blo 2049435 3077099 := bstep (se 1 (by rfl) ⟨2307824, by rfl⟩ : syracuseStep 3077099 = 4615649) B4615649
theorem B2051399 : Blo 2049435 2051399 := bstep (se 1 (by rfl) ⟨1538549, by rfl⟩ : syracuseStep 2051399 = 3077099) B3077099
theorem B2307829 : Blo 2049435 2307829 := bbase (se 5 (by rfl) ⟨108179, by rfl⟩ : syracuseStep 2307829 = 216359) (by norm_num)
theorem B3077105 : Blo 2049435 3077105 := bstep (se 2 (by rfl) ⟨1153914, by rfl⟩ : syracuseStep 3077105 = 2307829) B2307829
theorem B2051403 : Blo 2049435 2051403 := bstep (se 1 (by rfl) ⟨1538552, by rfl⟩ : syracuseStep 2051403 = 3077105) B3077105
theorem B2596313 : Blo 2049435 2596313 := bbase (se 2 (by rfl) ⟨973617, by rfl⟩ : syracuseStep 2596313 = 1947235) (by norm_num)
theorem B6923501 : Blo 2049435 6923501 := bstep (se 3 (by rfl) ⟨1298156, by rfl⟩ : syracuseStep 6923501 = 2596313) B2596313
theorem B4615667 : Blo 2049435 4615667 := bstep (se 1 (by rfl) ⟨3461750, by rfl⟩ : syracuseStep 4615667 = 6923501) B6923501
theorem B3077111 : Blo 2049435 3077111 := bstep (se 1 (by rfl) ⟨2307833, by rfl⟩ : syracuseStep 3077111 = 4615667) B4615667
theorem B2051407 : Blo 2049435 2051407 := bstep (se 1 (by rfl) ⟨1538555, by rfl⟩ : syracuseStep 2051407 = 3077111) B3077111
theorem B3077117 : Blo 2049435 3077117 := bbase (se 3 (by rfl) ⟨576959, by rfl⟩ : syracuseStep 3077117 = 1153919) (by norm_num)
theorem B2051411 : Blo 2049435 2051411 := bstep (se 1 (by rfl) ⟨1538558, by rfl⟩ : syracuseStep 2051411 = 3077117) B3077117
theorem B4615685 : Blo 2049435 4615685 := bbase (se 4 (by rfl) ⟨432720, by rfl⟩ : syracuseStep 4615685 = 865441) (by norm_num)
theorem B3077123 : Blo 2049435 3077123 := bstep (se 1 (by rfl) ⟨2307842, by rfl⟩ : syracuseStep 3077123 = 4615685) B4615685
theorem B2051415 : Blo 2049435 2051415 := bstep (se 1 (by rfl) ⟨1538561, by rfl⟩ : syracuseStep 2051415 = 3077123) B3077123
theorem B3894493 : Blo 2049435 3894493 := bbase (se 3 (by rfl) ⟨730217, by rfl⟩ : syracuseStep 3894493 = 1460435) (by norm_num)
theorem B5192657 : Blo 2049435 5192657 := bstep (se 2 (by rfl) ⟨1947246, by rfl⟩ : syracuseStep 5192657 = 3894493) B3894493
theorem B3461771 : Blo 2049435 3461771 := bstep (se 1 (by rfl) ⟨2596328, by rfl⟩ : syracuseStep 3461771 = 5192657) B5192657
theorem B2307847 : Blo 2049435 2307847 := bstep (se 1 (by rfl) ⟨1730885, by rfl⟩ : syracuseStep 2307847 = 3461771) B3461771
theorem B3077129 : Blo 2049435 3077129 := bstep (se 2 (by rfl) ⟨1153923, by rfl⟩ : syracuseStep 3077129 = 2307847) B2307847
theorem B2051419 : Blo 2049435 2051419 := bstep (se 1 (by rfl) ⟨1538564, by rfl⟩ : syracuseStep 2051419 = 3077129) B3077129
theorem B10385333 : Blo 2049435 10385333 := bbase (se 5 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 10385333 = 973625) (by norm_num)
theorem B6923555 : Blo 2049435 6923555 := bstep (se 1 (by rfl) ⟨5192666, by rfl⟩ : syracuseStep 6923555 = 10385333) B10385333
theorem B4615703 : Blo 2049435 4615703 := bstep (se 1 (by rfl) ⟨3461777, by rfl⟩ : syracuseStep 4615703 = 6923555) B6923555
theorem B3077135 : Blo 2049435 3077135 := bstep (se 1 (by rfl) ⟨2307851, by rfl⟩ : syracuseStep 3077135 = 4615703) B4615703
theorem B2051423 : Blo 2049435 2051423 := bstep (se 1 (by rfl) ⟨1538567, by rfl⟩ : syracuseStep 2051423 = 3077135) B3077135
theorem B3077141 : Blo 2049435 3077141 := bbase (se 6 (by rfl) ⟨72120, by rfl⟩ : syracuseStep 3077141 = 144241) (by norm_num)
theorem B2051427 : Blo 2049435 2051427 := bstep (se 1 (by rfl) ⟨1538570, by rfl⟩ : syracuseStep 2051427 = 3077141) B3077141
theorem B11241557 : Blo 2049435 11241557 := bbase (se 8 (by rfl) ⟨65868, by rfl⟩ : syracuseStep 11241557 = 131737) (by norm_num)
theorem B7494371 : Blo 2049435 7494371 := bstep (se 1 (by rfl) ⟨5620778, by rfl⟩ : syracuseStep 7494371 = 11241557) B11241557
theorem B4996247 : Blo 2049435 4996247 := bstep (se 1 (by rfl) ⟨3747185, by rfl⟩ : syracuseStep 4996247 = 7494371) B7494371
theorem B13323325 : Blo 2049435 13323325 := bstep (se 3 (by rfl) ⟨2498123, by rfl⟩ : syracuseStep 13323325 = 4996247) B4996247
theorem B17764433 : Blo 2049435 17764433 := bstep (se 2 (by rfl) ⟨6661662, by rfl⟩ : syracuseStep 17764433 = 13323325) B13323325
theorem B11842955 : Blo 2049435 11842955 := bstep (se 1 (by rfl) ⟨8882216, by rfl⟩ : syracuseStep 11842955 = 17764433) B17764433
theorem B7895303 : Blo 2049435 7895303 := bstep (se 1 (by rfl) ⟨5921477, by rfl⟩ : syracuseStep 7895303 = 11842955) B11842955
theorem B5263535 : Blo 2049435 5263535 := bstep (se 1 (by rfl) ⟨3947651, by rfl⟩ : syracuseStep 5263535 = 7895303) B7895303
theorem B3509023 : Blo 2049435 3509023 := bstep (se 1 (by rfl) ⟨2631767, by rfl⟩ : syracuseStep 3509023 = 5263535) B5263535
theorem B4678697 : Blo 2049435 4678697 := bstep (se 2 (by rfl) ⟨1754511, by rfl⟩ : syracuseStep 4678697 = 3509023) B3509023
theorem B3119131 : Blo 2049435 3119131 := bstep (se 1 (by rfl) ⟨2339348, by rfl⟩ : syracuseStep 3119131 = 4678697) B4678697
theorem B16635365 : Blo 2049435 16635365 := bstep (se 4 (by rfl) ⟨1559565, by rfl⟩ : syracuseStep 16635365 = 3119131) B3119131
theorem B11090243 : Blo 2049435 11090243 := bstep (se 1 (by rfl) ⟨8317682, by rfl⟩ : syracuseStep 11090243 = 16635365) B16635365
theorem B29573981 : Blo 2049435 29573981 := bstep (se 3 (by rfl) ⟨5545121, by rfl⟩ : syracuseStep 29573981 = 11090243) B11090243
theorem B19715987 : Blo 2049435 19715987 := bstep (se 1 (by rfl) ⟨14786990, by rfl⟩ : syracuseStep 19715987 = 29573981) B29573981
theorem B13143991 : Blo 2049435 13143991 := bstep (se 1 (by rfl) ⟨9857993, by rfl⟩ : syracuseStep 13143991 = 19715987) B19715987
theorem B17525321 : Blo 2049435 17525321 := bstep (se 2 (by rfl) ⟨6571995, by rfl⟩ : syracuseStep 17525321 = 13143991) B13143991
theorem B11683547 : Blo 2049435 11683547 := bstep (se 1 (by rfl) ⟨8762660, by rfl⟩ : syracuseStep 11683547 = 17525321) B17525321
theorem B7789031 : Blo 2049435 7789031 := bstep (se 1 (by rfl) ⟨5841773, by rfl⟩ : syracuseStep 7789031 = 11683547) B11683547
theorem B5192687 : Blo 2049435 5192687 := bstep (se 1 (by rfl) ⟨3894515, by rfl⟩ : syracuseStep 5192687 = 7789031) B7789031
theorem B3461791 : Blo 2049435 3461791 := bstep (se 1 (by rfl) ⟨2596343, by rfl⟩ : syracuseStep 3461791 = 5192687) B5192687
theorem B4615721 : Blo 2049435 4615721 := bstep (se 2 (by rfl) ⟨1730895, by rfl⟩ : syracuseStep 4615721 = 3461791) B3461791
theorem B3077147 : Blo 2049435 3077147 := bstep (se 1 (by rfl) ⟨2307860, by rfl⟩ : syracuseStep 3077147 = 4615721) B4615721
theorem B2051431 : Blo 2049435 2051431 := bstep (se 1 (by rfl) ⟨1538573, by rfl⟩ : syracuseStep 2051431 = 3077147) B3077147
theorem B2307865 : Blo 2049435 2307865 := bbase (se 2 (by rfl) ⟨865449, by rfl⟩ : syracuseStep 2307865 = 1730899) (by norm_num)
theorem B3077153 : Blo 2049435 3077153 := bstep (se 2 (by rfl) ⟨1153932, by rfl⟩ : syracuseStep 3077153 = 2307865) B2307865
theorem B2051435 : Blo 2049435 2051435 := bstep (se 1 (by rfl) ⟨1538576, by rfl⟩ : syracuseStep 2051435 = 3077153) B3077153
theorem C0 (j : ℕ) (h1 : 512358 ≤ j) (h2 : j ≤ 512858) : Blo 2049435 (4 * j + 3) := by
  interval_cases j
  · exact B2049435
  · exact B2049439
  · exact B2049443
  · exact B2049447
  · exact B2049451
  · exact B2049455
  · exact B2049459
  · exact B2049463
  · exact B2049467
  · exact B2049471
  · exact B2049475
  · exact B2049479
  · exact B2049483
  · exact B2049487
  · exact B2049491
  · exact B2049495
  · exact B2049499
  · exact B2049503
  · exact B2049507
  · exact B2049511
  · exact B2049515
  · exact B2049519
  · exact B2049523
  · exact B2049527
  · exact B2049531
  · exact B2049535
  · exact B2049539
  · exact B2049543
  · exact B2049547
  · exact B2049551
  · exact B2049555
  · exact B2049559
  · exact B2049563
  · exact B2049567
  · exact B2049571
  · exact B2049575
  · exact B2049579
  · exact B2049583
  · exact B2049587
  · exact B2049591
  · exact B2049595
  · exact B2049599
  · exact B2049603
  · exact B2049607
  · exact B2049611
  · exact B2049615
  · exact B2049619
  · exact B2049623
  · exact B2049627
  · exact B2049631
  · exact B2049635
  · exact B2049639
  · exact B2049643
  · exact B2049647
  · exact B2049651
  · exact B2049655
  · exact B2049659
  · exact B2049663
  · exact B2049667
  · exact B2049671
  · exact B2049675
  · exact B2049679
  · exact B2049683
  · exact B2049687
  · exact B2049691
  · exact B2049695
  · exact B2049699
  · exact B2049703
  · exact B2049707
  · exact B2049711
  · exact B2049715
  · exact B2049719
  · exact B2049723
  · exact B2049727
  · exact B2049731
  · exact B2049735
  · exact B2049739
  · exact B2049743
  · exact B2049747
  · exact B2049751
  · exact B2049755
  · exact B2049759
  · exact B2049763
  · exact B2049767
  · exact B2049771
  · exact B2049775
  · exact B2049779
  · exact B2049783
  · exact B2049787
  · exact B2049791
  · exact B2049795
  · exact B2049799
  · exact B2049803
  · exact B2049807
  · exact B2049811
  · exact B2049815
  · exact B2049819
  · exact B2049823
  · exact B2049827
  · exact B2049831
  · exact B2049835
  · exact B2049839
  · exact B2049843
  · exact B2049847
  · exact B2049851
  · exact B2049855
  · exact B2049859
  · exact B2049863
  · exact B2049867
  · exact B2049871
  · exact B2049875
  · exact B2049879
  · exact B2049883
  · exact B2049887
  · exact B2049891
  · exact B2049895
  · exact B2049899
  · exact B2049903
  · exact B2049907
  · exact B2049911
  · exact B2049915
  · exact B2049919
  · exact B2049923
  · exact B2049927
  · exact B2049931
  · exact B2049935
  · exact B2049939
  · exact B2049943
  · exact B2049947
  · exact B2049951
  · exact B2049955
  · exact B2049959
  · exact B2049963
  · exact B2049967
  · exact B2049971
  · exact B2049975
  · exact B2049979
  · exact B2049983
  · exact B2049987
  · exact B2049991
  · exact B2049995
  · exact B2049999
  · exact B2050003
  · exact B2050007
  · exact B2050011
  · exact B2050015
  · exact B2050019
  · exact B2050023
  · exact B2050027
  · exact B2050031
  · exact B2050035
  · exact B2050039
  · exact B2050043
  · exact B2050047
  · exact B2050051
  · exact B2050055
  · exact B2050059
  · exact B2050063
  · exact B2050067
  · exact B2050071
  · exact B2050075
  · exact B2050079
  · exact B2050083
  · exact B2050087
  · exact B2050091
  · exact B2050095
  · exact B2050099
  · exact B2050103
  · exact B2050107
  · exact B2050111
  · exact B2050115
  · exact B2050119
  · exact B2050123
  · exact B2050127
  · exact B2050131
  · exact B2050135
  · exact B2050139
  · exact B2050143
  · exact B2050147
  · exact B2050151
  · exact B2050155
  · exact B2050159
  · exact B2050163
  · exact B2050167
  · exact B2050171
  · exact B2050175
  · exact B2050179
  · exact B2050183
  · exact B2050187
  · exact B2050191
  · exact B2050195
  · exact B2050199
  · exact B2050203
  · exact B2050207
  · exact B2050211
  · exact B2050215
  · exact B2050219
  · exact B2050223
  · exact B2050227
  · exact B2050231
  · exact B2050235
  · exact B2050239
  · exact B2050243
  · exact B2050247
  · exact B2050251
  · exact B2050255
  · exact B2050259
  · exact B2050263
  · exact B2050267
  · exact B2050271
  · exact B2050275
  · exact B2050279
  · exact B2050283
  · exact B2050287
  · exact B2050291
  · exact B2050295
  · exact B2050299
  · exact B2050303
  · exact B2050307
  · exact B2050311
  · exact B2050315
  · exact B2050319
  · exact B2050323
  · exact B2050327
  · exact B2050331
  · exact B2050335
  · exact B2050339
  · exact B2050343
  · exact B2050347
  · exact B2050351
  · exact B2050355
  · exact B2050359
  · exact B2050363
  · exact B2050367
  · exact B2050371
  · exact B2050375
  · exact B2050379
  · exact B2050383
  · exact B2050387
  · exact B2050391
  · exact B2050395
  · exact B2050399
  · exact B2050403
  · exact B2050407
  · exact B2050411
  · exact B2050415
  · exact B2050419
  · exact B2050423
  · exact B2050427
  · exact B2050431
  · exact B2050435
  · exact B2050439
  · exact B2050443
  · exact B2050447
  · exact B2050451
  · exact B2050455
  · exact B2050459
  · exact B2050463
  · exact B2050467
  · exact B2050471
  · exact B2050475
  · exact B2050479
  · exact B2050483
  · exact B2050487
  · exact B2050491
  · exact B2050495
  · exact B2050499
  · exact B2050503
  · exact B2050507
  · exact B2050511
  · exact B2050515
  · exact B2050519
  · exact B2050523
  · exact B2050527
  · exact B2050531
  · exact B2050535
  · exact B2050539
  · exact B2050543
  · exact B2050547
  · exact B2050551
  · exact B2050555
  · exact B2050559
  · exact B2050563
  · exact B2050567
  · exact B2050571
  · exact B2050575
  · exact B2050579
  · exact B2050583
  · exact B2050587
  · exact B2050591
  · exact B2050595
  · exact B2050599
  · exact B2050603
  · exact B2050607
  · exact B2050611
  · exact B2050615
  · exact B2050619
  · exact B2050623
  · exact B2050627
  · exact B2050631
  · exact B2050635
  · exact B2050639
  · exact B2050643
  · exact B2050647
  · exact B2050651
  · exact B2050655
  · exact B2050659
  · exact B2050663
  · exact B2050667
  · exact B2050671
  · exact B2050675
  · exact B2050679
  · exact B2050683
  · exact B2050687
  · exact B2050691
  · exact B2050695
  · exact B2050699
  · exact B2050703
  · exact B2050707
  · exact B2050711
  · exact B2050715
  · exact B2050719
  · exact B2050723
  · exact B2050727
  · exact B2050731
  · exact B2050735
  · exact B2050739
  · exact B2050743
  · exact B2050747
  · exact B2050751
  · exact B2050755
  · exact B2050759
  · exact B2050763
  · exact B2050767
  · exact B2050771
  · exact B2050775
  · exact B2050779
  · exact B2050783
  · exact B2050787
  · exact B2050791
  · exact B2050795
  · exact B2050799
  · exact B2050803
  · exact B2050807
  · exact B2050811
  · exact B2050815
  · exact B2050819
  · exact B2050823
  · exact B2050827
  · exact B2050831
  · exact B2050835
  · exact B2050839
  · exact B2050843
  · exact B2050847
  · exact B2050851
  · exact B2050855
  · exact B2050859
  · exact B2050863
  · exact B2050867
  · exact B2050871
  · exact B2050875
  · exact B2050879
  · exact B2050883
  · exact B2050887
  · exact B2050891
  · exact B2050895
  · exact B2050899
  · exact B2050903
  · exact B2050907
  · exact B2050911
  · exact B2050915
  · exact B2050919
  · exact B2050923
  · exact B2050927
  · exact B2050931
  · exact B2050935
  · exact B2050939
  · exact B2050943
  · exact B2050947
  · exact B2050951
  · exact B2050955
  · exact B2050959
  · exact B2050963
  · exact B2050967
  · exact B2050971
  · exact B2050975
  · exact B2050979
  · exact B2050983
  · exact B2050987
  · exact B2050991
  · exact B2050995
  · exact B2050999
  · exact B2051003
  · exact B2051007
  · exact B2051011
  · exact B2051015
  · exact B2051019
  · exact B2051023
  · exact B2051027
  · exact B2051031
  · exact B2051035
  · exact B2051039
  · exact B2051043
  · exact B2051047
  · exact B2051051
  · exact B2051055
  · exact B2051059
  · exact B2051063
  · exact B2051067
  · exact B2051071
  · exact B2051075
  · exact B2051079
  · exact B2051083
  · exact B2051087
  · exact B2051091
  · exact B2051095
  · exact B2051099
  · exact B2051103
  · exact B2051107
  · exact B2051111
  · exact B2051115
  · exact B2051119
  · exact B2051123
  · exact B2051127
  · exact B2051131
  · exact B2051135
  · exact B2051139
  · exact B2051143
  · exact B2051147
  · exact B2051151
  · exact B2051155
  · exact B2051159
  · exact B2051163
  · exact B2051167
  · exact B2051171
  · exact B2051175
  · exact B2051179
  · exact B2051183
  · exact B2051187
  · exact B2051191
  · exact B2051195
  · exact B2051199
  · exact B2051203
  · exact B2051207
  · exact B2051211
  · exact B2051215
  · exact B2051219
  · exact B2051223
  · exact B2051227
  · exact B2051231
  · exact B2051235
  · exact B2051239
  · exact B2051243
  · exact B2051247
  · exact B2051251
  · exact B2051255
  · exact B2051259
  · exact B2051263
  · exact B2051267
  · exact B2051271
  · exact B2051275
  · exact B2051279
  · exact B2051283
  · exact B2051287
  · exact B2051291
  · exact B2051295
  · exact B2051299
  · exact B2051303
  · exact B2051307
  · exact B2051311
  · exact B2051315
  · exact B2051319
  · exact B2051323
  · exact B2051327
  · exact B2051331
  · exact B2051335
  · exact B2051339
  · exact B2051343
  · exact B2051347
  · exact B2051351
  · exact B2051355
  · exact B2051359
  · exact B2051363
  · exact B2051367
  · exact B2051371
  · exact B2051375
  · exact B2051379
  · exact B2051383
  · exact B2051387
  · exact B2051391
  · exact B2051395
  · exact B2051399
  · exact B2051403
  · exact B2051407
  · exact B2051411
  · exact B2051415
  · exact B2051419
  · exact B2051423
  · exact B2051427
  · exact B2051431
  · exact B2051435
theorem solution (m : ℕ) (hlo : 2049435 ≤ m) (hhi : m ≤ 2051435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 512358 ≤ j := by omega
    have hj2 : j ≤ 512858 := by omega
    have hb : Blo 2049435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
