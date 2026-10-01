-- Prove2me | solution 1 for syracuse_descends_range_2107435_2109435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:41.403529+00:00
-- url     : https://prove2.me/submissions/06f58a76-a26b-43d3-bce4-2573696e6ff6

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

theorem B2370865 : Blo 2107435 2370865 := bbase (se 2 (by rfl) ⟨889074, by rfl⟩ : syracuseStep 2370865 = 1778149) (by norm_num)
theorem B3161153 : Blo 2107435 3161153 := bstep (se 2 (by rfl) ⟨1185432, by rfl⟩ : syracuseStep 3161153 = 2370865) B2370865
theorem B2107435 : Blo 2107435 2107435 := bstep (se 1 (by rfl) ⟨1580576, by rfl⟩ : syracuseStep 2107435 = 3161153) B3161153
theorem B4500949 : Blo 2107435 4500949 := bbase (se 7 (by rfl) ⟨52745, by rfl⟩ : syracuseStep 4500949 = 105491) (by norm_num)
theorem B6001265 : Blo 2107435 6001265 := bstep (se 2 (by rfl) ⟨2250474, by rfl⟩ : syracuseStep 6001265 = 4500949) B4500949
theorem B4000843 : Blo 2107435 4000843 := bstep (se 1 (by rfl) ⟨3000632, by rfl⟩ : syracuseStep 4000843 = 6001265) B6001265
theorem B5334457 : Blo 2107435 5334457 := bstep (se 2 (by rfl) ⟨2000421, by rfl⟩ : syracuseStep 5334457 = 4000843) B4000843
theorem B7112609 : Blo 2107435 7112609 := bstep (se 2 (by rfl) ⟨2667228, by rfl⟩ : syracuseStep 7112609 = 5334457) B5334457
theorem B4741739 : Blo 2107435 4741739 := bstep (se 1 (by rfl) ⟨3556304, by rfl⟩ : syracuseStep 4741739 = 7112609) B7112609
theorem B3161159 : Blo 2107435 3161159 := bstep (se 1 (by rfl) ⟨2370869, by rfl⟩ : syracuseStep 3161159 = 4741739) B4741739
theorem B2107439 : Blo 2107435 2107439 := bstep (se 1 (by rfl) ⟨1580579, by rfl⟩ : syracuseStep 2107439 = 3161159) B3161159
theorem B3161165 : Blo 2107435 3161165 := bbase (se 3 (by rfl) ⟨592718, by rfl⟩ : syracuseStep 3161165 = 1185437) (by norm_num)
theorem B2107443 : Blo 2107435 2107443 := bstep (se 1 (by rfl) ⟨1580582, by rfl⟩ : syracuseStep 2107443 = 3161165) B3161165
theorem B4741757 : Blo 2107435 4741757 := bbase (se 3 (by rfl) ⟨889079, by rfl⟩ : syracuseStep 4741757 = 1778159) (by norm_num)
theorem B3161171 : Blo 2107435 3161171 := bstep (se 1 (by rfl) ⟨2370878, by rfl⟩ : syracuseStep 3161171 = 4741757) B4741757
theorem B2107447 : Blo 2107435 2107447 := bstep (se 1 (by rfl) ⟨1580585, by rfl⟩ : syracuseStep 2107447 = 3161171) B3161171
theorem B3556325 : Blo 2107435 3556325 := bbase (se 4 (by rfl) ⟨333405, by rfl⟩ : syracuseStep 3556325 = 666811) (by norm_num)
theorem B2370883 : Blo 2107435 2370883 := bstep (se 1 (by rfl) ⟨1778162, by rfl⟩ : syracuseStep 2370883 = 3556325) B3556325
theorem B3161177 : Blo 2107435 3161177 := bstep (se 2 (by rfl) ⟨1185441, by rfl⟩ : syracuseStep 3161177 = 2370883) B2370883
theorem B2107451 : Blo 2107435 2107451 := bstep (se 1 (by rfl) ⟨1580588, by rfl⟩ : syracuseStep 2107451 = 3161177) B3161177
theorem B6408629 : Blo 2107435 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B4272419 : Blo 2107435 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B2848279 : Blo 2107435 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B3797705 : Blo 2107435 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B10127213 : Blo 2107435 10127213 := bstep (se 3 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 10127213 = 3797705) B3797705
theorem B6751475 : Blo 2107435 6751475 := bstep (se 1 (by rfl) ⟨5063606, by rfl⟩ : syracuseStep 6751475 = 10127213) B10127213
theorem B4500983 : Blo 2107435 4500983 := bstep (se 1 (by rfl) ⟨3375737, by rfl⟩ : syracuseStep 4500983 = 6751475) B6751475
theorem B3000655 : Blo 2107435 3000655 := bstep (se 1 (by rfl) ⟨2250491, by rfl⟩ : syracuseStep 3000655 = 4500983) B4500983
theorem B16003493 : Blo 2107435 16003493 := bstep (se 4 (by rfl) ⟨1500327, by rfl⟩ : syracuseStep 16003493 = 3000655) B3000655
theorem B10668995 : Blo 2107435 10668995 := bstep (se 1 (by rfl) ⟨8001746, by rfl⟩ : syracuseStep 10668995 = 16003493) B16003493
theorem B7112663 : Blo 2107435 7112663 := bstep (se 1 (by rfl) ⟨5334497, by rfl⟩ : syracuseStep 7112663 = 10668995) B10668995
theorem B4741775 : Blo 2107435 4741775 := bstep (se 1 (by rfl) ⟨3556331, by rfl⟩ : syracuseStep 4741775 = 7112663) B7112663
theorem B3161183 : Blo 2107435 3161183 := bstep (se 1 (by rfl) ⟨2370887, by rfl⟩ : syracuseStep 3161183 = 4741775) B4741775
theorem B2107455 : Blo 2107435 2107455 := bstep (se 1 (by rfl) ⟨1580591, by rfl⟩ : syracuseStep 2107455 = 3161183) B3161183
theorem B3161189 : Blo 2107435 3161189 := bbase (se 4 (by rfl) ⟨296361, by rfl⟩ : syracuseStep 3161189 = 592723) (by norm_num)
theorem B2107459 : Blo 2107435 2107459 := bstep (se 1 (by rfl) ⟨1580594, by rfl⟩ : syracuseStep 2107459 = 3161189) B3161189
theorem B5696581 : Blo 2107435 5696581 := bbase (se 4 (by rfl) ⟨534054, by rfl⟩ : syracuseStep 5696581 = 1068109) (by norm_num)
theorem B7595441 : Blo 2107435 7595441 := bstep (se 2 (by rfl) ⟨2848290, by rfl⟩ : syracuseStep 7595441 = 5696581) B5696581
theorem B5063627 : Blo 2107435 5063627 := bstep (se 1 (by rfl) ⟨3797720, by rfl⟩ : syracuseStep 5063627 = 7595441) B7595441
theorem B3375751 : Blo 2107435 3375751 := bstep (se 1 (by rfl) ⟨2531813, by rfl⟩ : syracuseStep 3375751 = 5063627) B5063627
theorem B4501001 : Blo 2107435 4501001 := bstep (se 2 (by rfl) ⟨1687875, by rfl⟩ : syracuseStep 4501001 = 3375751) B3375751
theorem B3000667 : Blo 2107435 3000667 := bstep (se 1 (by rfl) ⟨2250500, by rfl⟩ : syracuseStep 3000667 = 4501001) B4501001
theorem B4000889 : Blo 2107435 4000889 := bstep (se 2 (by rfl) ⟨1500333, by rfl⟩ : syracuseStep 4000889 = 3000667) B3000667
theorem B2667259 : Blo 2107435 2667259 := bstep (se 1 (by rfl) ⟨2000444, by rfl⟩ : syracuseStep 2667259 = 4000889) B4000889
theorem B3556345 : Blo 2107435 3556345 := bstep (se 2 (by rfl) ⟨1333629, by rfl⟩ : syracuseStep 3556345 = 2667259) B2667259
theorem B4741793 : Blo 2107435 4741793 := bstep (se 2 (by rfl) ⟨1778172, by rfl⟩ : syracuseStep 4741793 = 3556345) B3556345
theorem B3161195 : Blo 2107435 3161195 := bstep (se 1 (by rfl) ⟨2370896, by rfl⟩ : syracuseStep 3161195 = 4741793) B4741793
theorem B2107463 : Blo 2107435 2107463 := bstep (se 1 (by rfl) ⟨1580597, by rfl⟩ : syracuseStep 2107463 = 3161195) B3161195
theorem B2370901 : Blo 2107435 2370901 := bbase (se 11 (by rfl) ⟨1736, by rfl⟩ : syracuseStep 2370901 = 3473) (by norm_num)
theorem B3161201 : Blo 2107435 3161201 := bstep (se 2 (by rfl) ⟨1185450, by rfl⟩ : syracuseStep 3161201 = 2370901) B2370901
theorem B2107467 : Blo 2107435 2107467 := bstep (se 1 (by rfl) ⟨1580600, by rfl⟩ : syracuseStep 2107467 = 3161201) B3161201
theorem B2667269 : Blo 2107435 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B7112717 : Blo 2107435 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B4741811 : Blo 2107435 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3161207 : Blo 2107435 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2107471 : Blo 2107435 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B3161213 : Blo 2107435 3161213 := bbase (se 3 (by rfl) ⟨592727, by rfl⟩ : syracuseStep 3161213 = 1185455) (by norm_num)
theorem B2107475 : Blo 2107435 2107475 := bstep (se 1 (by rfl) ⟨1580606, by rfl⟩ : syracuseStep 2107475 = 3161213) B3161213
theorem B4741829 : Blo 2107435 4741829 := bbase (se 4 (by rfl) ⟨444546, by rfl⟩ : syracuseStep 4741829 = 889093) (by norm_num)
theorem B3161219 : Blo 2107435 3161219 := bstep (se 1 (by rfl) ⟨2370914, by rfl⟩ : syracuseStep 3161219 = 4741829) B4741829
theorem B2107479 : Blo 2107435 2107479 := bstep (se 1 (by rfl) ⟨1580609, by rfl⟩ : syracuseStep 2107479 = 3161219) B3161219
theorem B13169557 : Blo 2107435 13169557 := bbase (se 6 (by rfl) ⟨308661, by rfl⟩ : syracuseStep 13169557 = 617323) (by norm_num)
theorem B70237637 : Blo 2107435 70237637 := bstep (se 4 (by rfl) ⟨6584778, by rfl⟩ : syracuseStep 70237637 = 13169557) B13169557
theorem B46825091 : Blo 2107435 46825091 := bstep (se 1 (by rfl) ⟨35118818, by rfl⟩ : syracuseStep 46825091 = 70237637) B70237637
theorem B31216727 : Blo 2107435 31216727 := bstep (se 1 (by rfl) ⟨23412545, by rfl⟩ : syracuseStep 31216727 = 46825091) B46825091
theorem B20811151 : Blo 2107435 20811151 := bstep (se 1 (by rfl) ⟨15608363, by rfl⟩ : syracuseStep 20811151 = 31216727) B31216727
theorem B27748201 : Blo 2107435 27748201 := bstep (se 2 (by rfl) ⟨10405575, by rfl⟩ : syracuseStep 27748201 = 20811151) B20811151
theorem B36997601 : Blo 2107435 36997601 := bstep (se 2 (by rfl) ⟨13874100, by rfl⟩ : syracuseStep 36997601 = 27748201) B27748201
theorem B98660269 : Blo 2107435 98660269 := bstep (se 3 (by rfl) ⟨18498800, by rfl⟩ : syracuseStep 98660269 = 36997601) B36997601
theorem B131547025 : Blo 2107435 131547025 := bstep (se 2 (by rfl) ⟨49330134, by rfl⟩ : syracuseStep 131547025 = 98660269) B98660269
theorem B175396033 : Blo 2107435 175396033 := bstep (se 2 (by rfl) ⟨65773512, by rfl⟩ : syracuseStep 175396033 = 131547025) B131547025
theorem B233861377 : Blo 2107435 233861377 := bstep (se 2 (by rfl) ⟨87698016, by rfl⟩ : syracuseStep 233861377 = 175396033) B175396033
theorem B311815169 : Blo 2107435 311815169 := bstep (se 2 (by rfl) ⟨116930688, by rfl⟩ : syracuseStep 311815169 = 233861377) B233861377
theorem B207876779 : Blo 2107435 207876779 := bstep (se 1 (by rfl) ⟨155907584, by rfl⟩ : syracuseStep 207876779 = 311815169) B311815169
theorem B138584519 : Blo 2107435 138584519 := bstep (se 1 (by rfl) ⟨103938389, by rfl⟩ : syracuseStep 138584519 = 207876779) B207876779
theorem B92389679 : Blo 2107435 92389679 := bstep (se 1 (by rfl) ⟨69292259, by rfl⟩ : syracuseStep 92389679 = 138584519) B138584519
theorem B61593119 : Blo 2107435 61593119 := bstep (se 1 (by rfl) ⟨46194839, by rfl⟩ : syracuseStep 61593119 = 92389679) B92389679
theorem B41062079 : Blo 2107435 41062079 := bstep (se 1 (by rfl) ⟨30796559, by rfl⟩ : syracuseStep 41062079 = 61593119) B61593119
theorem B109498877 : Blo 2107435 109498877 := bstep (se 3 (by rfl) ⟨20531039, by rfl⟩ : syracuseStep 109498877 = 41062079) B41062079
theorem B72999251 : Blo 2107435 72999251 := bstep (se 1 (by rfl) ⟨54749438, by rfl⟩ : syracuseStep 72999251 = 109498877) B109498877
theorem B48666167 : Blo 2107435 48666167 := bstep (se 1 (by rfl) ⟨36499625, by rfl⟩ : syracuseStep 48666167 = 72999251) B72999251
theorem B32444111 : Blo 2107435 32444111 := bstep (se 1 (by rfl) ⟨24333083, by rfl⟩ : syracuseStep 32444111 = 48666167) B48666167
theorem B86517629 : Blo 2107435 86517629 := bstep (se 3 (by rfl) ⟨16222055, by rfl⟩ : syracuseStep 86517629 = 32444111) B32444111
theorem B57678419 : Blo 2107435 57678419 := bstep (se 1 (by rfl) ⟨43258814, by rfl⟩ : syracuseStep 57678419 = 86517629) B86517629
theorem B38452279 : Blo 2107435 38452279 := bstep (se 1 (by rfl) ⟨28839209, by rfl⟩ : syracuseStep 38452279 = 57678419) B57678419
theorem B51269705 : Blo 2107435 51269705 := bstep (se 2 (by rfl) ⟨19226139, by rfl⟩ : syracuseStep 51269705 = 38452279) B38452279
theorem B34179803 : Blo 2107435 34179803 := bstep (se 1 (by rfl) ⟨25634852, by rfl⟩ : syracuseStep 34179803 = 51269705) B51269705
theorem B22786535 : Blo 2107435 22786535 := bstep (se 1 (by rfl) ⟨17089901, by rfl⟩ : syracuseStep 22786535 = 34179803) B34179803
theorem B15191023 : Blo 2107435 15191023 := bstep (se 1 (by rfl) ⟨11393267, by rfl⟩ : syracuseStep 15191023 = 22786535) B22786535
theorem B20254697 : Blo 2107435 20254697 := bstep (se 2 (by rfl) ⟨7595511, by rfl⟩ : syracuseStep 20254697 = 15191023) B15191023
theorem B13503131 : Blo 2107435 13503131 := bstep (se 1 (by rfl) ⟨10127348, by rfl⟩ : syracuseStep 13503131 = 20254697) B20254697
theorem B9002087 : Blo 2107435 9002087 := bstep (se 1 (by rfl) ⟨6751565, by rfl⟩ : syracuseStep 9002087 = 13503131) B13503131
theorem B6001391 : Blo 2107435 6001391 := bstep (se 1 (by rfl) ⟨4501043, by rfl⟩ : syracuseStep 6001391 = 9002087) B9002087
theorem B4000927 : Blo 2107435 4000927 := bstep (se 1 (by rfl) ⟨3000695, by rfl⟩ : syracuseStep 4000927 = 6001391) B6001391
theorem B5334569 : Blo 2107435 5334569 := bstep (se 2 (by rfl) ⟨2000463, by rfl⟩ : syracuseStep 5334569 = 4000927) B4000927
theorem B3556379 : Blo 2107435 3556379 := bstep (se 1 (by rfl) ⟨2667284, by rfl⟩ : syracuseStep 3556379 = 5334569) B5334569
theorem B2370919 : Blo 2107435 2370919 := bstep (se 1 (by rfl) ⟨1778189, by rfl⟩ : syracuseStep 2370919 = 3556379) B3556379
theorem B3161225 : Blo 2107435 3161225 := bstep (se 2 (by rfl) ⟨1185459, by rfl⟩ : syracuseStep 3161225 = 2370919) B2370919
theorem B2107483 : Blo 2107435 2107483 := bstep (se 1 (by rfl) ⟨1580612, by rfl⟩ : syracuseStep 2107483 = 3161225) B3161225
theorem B10669157 : Blo 2107435 10669157 := bbase (se 4 (by rfl) ⟨1000233, by rfl⟩ : syracuseStep 10669157 = 2000467) (by norm_num)
theorem B7112771 : Blo 2107435 7112771 := bstep (se 1 (by rfl) ⟨5334578, by rfl⟩ : syracuseStep 7112771 = 10669157) B10669157
theorem B4741847 : Blo 2107435 4741847 := bstep (se 1 (by rfl) ⟨3556385, by rfl⟩ : syracuseStep 4741847 = 7112771) B7112771
theorem B3161231 : Blo 2107435 3161231 := bstep (se 1 (by rfl) ⟨2370923, by rfl⟩ : syracuseStep 3161231 = 4741847) B4741847
theorem B2107487 : Blo 2107435 2107487 := bstep (se 1 (by rfl) ⟨1580615, by rfl⟩ : syracuseStep 2107487 = 3161231) B3161231
theorem B3161237 : Blo 2107435 3161237 := bbase (se 6 (by rfl) ⟨74091, by rfl⟩ : syracuseStep 3161237 = 148183) (by norm_num)
theorem B2107491 : Blo 2107435 2107491 := bstep (se 1 (by rfl) ⟨1580618, by rfl⟩ : syracuseStep 2107491 = 3161237) B3161237
theorem B2848333 : Blo 2107435 2848333 := bbase (se 3 (by rfl) ⟨534062, by rfl⟩ : syracuseStep 2848333 = 1068125) (by norm_num)
theorem B3797777 : Blo 2107435 3797777 := bstep (se 2 (by rfl) ⟨1424166, by rfl⟩ : syracuseStep 3797777 = 2848333) B2848333
theorem B10127405 : Blo 2107435 10127405 := bstep (se 3 (by rfl) ⟨1898888, by rfl⟩ : syracuseStep 10127405 = 3797777) B3797777
theorem B6751603 : Blo 2107435 6751603 := bstep (se 1 (by rfl) ⟨5063702, by rfl⟩ : syracuseStep 6751603 = 10127405) B10127405
theorem B9002137 : Blo 2107435 9002137 := bstep (se 2 (by rfl) ⟨3375801, by rfl⟩ : syracuseStep 9002137 = 6751603) B6751603
theorem B12002849 : Blo 2107435 12002849 := bstep (se 2 (by rfl) ⟨4501068, by rfl⟩ : syracuseStep 12002849 = 9002137) B9002137
theorem B8001899 : Blo 2107435 8001899 := bstep (se 1 (by rfl) ⟨6001424, by rfl⟩ : syracuseStep 8001899 = 12002849) B12002849
theorem B5334599 : Blo 2107435 5334599 := bstep (se 1 (by rfl) ⟨4000949, by rfl⟩ : syracuseStep 5334599 = 8001899) B8001899
theorem B3556399 : Blo 2107435 3556399 := bstep (se 1 (by rfl) ⟨2667299, by rfl⟩ : syracuseStep 3556399 = 5334599) B5334599
theorem B4741865 : Blo 2107435 4741865 := bstep (se 2 (by rfl) ⟨1778199, by rfl⟩ : syracuseStep 4741865 = 3556399) B3556399
theorem B3161243 : Blo 2107435 3161243 := bstep (se 1 (by rfl) ⟨2370932, by rfl⟩ : syracuseStep 3161243 = 4741865) B4741865
theorem B2107495 : Blo 2107435 2107495 := bstep (se 1 (by rfl) ⟨1580621, by rfl⟩ : syracuseStep 2107495 = 3161243) B3161243
theorem B2370937 : Blo 2107435 2370937 := bbase (se 2 (by rfl) ⟨889101, by rfl⟩ : syracuseStep 2370937 = 1778203) (by norm_num)
theorem B3161249 : Blo 2107435 3161249 := bstep (se 2 (by rfl) ⟨1185468, by rfl⟩ : syracuseStep 3161249 = 2370937) B2370937
theorem B2107499 : Blo 2107435 2107499 := bstep (se 1 (by rfl) ⟨1580624, by rfl⟩ : syracuseStep 2107499 = 3161249) B3161249
theorem B2566405 : Blo 2107435 2566405 := bbase (se 4 (by rfl) ⟨240600, by rfl⟩ : syracuseStep 2566405 = 481201) (by norm_num)
theorem B3421873 : Blo 2107435 3421873 := bstep (se 2 (by rfl) ⟨1283202, by rfl⟩ : syracuseStep 3421873 = 2566405) B2566405
theorem B4562497 : Blo 2107435 4562497 := bstep (se 2 (by rfl) ⟨1710936, by rfl⟩ : syracuseStep 4562497 = 3421873) B3421873
theorem B6083329 : Blo 2107435 6083329 := bstep (se 2 (by rfl) ⟨2281248, by rfl⟩ : syracuseStep 6083329 = 4562497) B4562497
theorem B8111105 : Blo 2107435 8111105 := bstep (se 2 (by rfl) ⟨3041664, by rfl⟩ : syracuseStep 8111105 = 6083329) B6083329
theorem B5407403 : Blo 2107435 5407403 := bstep (se 1 (by rfl) ⟨4055552, by rfl⟩ : syracuseStep 5407403 = 8111105) B8111105
theorem B14419741 : Blo 2107435 14419741 := bstep (se 3 (by rfl) ⟨2703701, by rfl⟩ : syracuseStep 14419741 = 5407403) B5407403
theorem B19226321 : Blo 2107435 19226321 := bstep (se 2 (by rfl) ⟨7209870, by rfl⟩ : syracuseStep 19226321 = 14419741) B14419741
theorem B12817547 : Blo 2107435 12817547 := bstep (se 1 (by rfl) ⟨9613160, by rfl⟩ : syracuseStep 12817547 = 19226321) B19226321
theorem B8545031 : Blo 2107435 8545031 := bstep (se 1 (by rfl) ⟨6408773, by rfl⟩ : syracuseStep 8545031 = 12817547) B12817547
theorem B5696687 : Blo 2107435 5696687 := bstep (se 1 (by rfl) ⟨4272515, by rfl⟩ : syracuseStep 5696687 = 8545031) B8545031
theorem B15191165 : Blo 2107435 15191165 := bstep (se 3 (by rfl) ⟨2848343, by rfl⟩ : syracuseStep 15191165 = 5696687) B5696687
theorem B10127443 : Blo 2107435 10127443 := bstep (se 1 (by rfl) ⟨7595582, by rfl⟩ : syracuseStep 10127443 = 15191165) B15191165
theorem B13503257 : Blo 2107435 13503257 := bstep (se 2 (by rfl) ⟨5063721, by rfl⟩ : syracuseStep 13503257 = 10127443) B10127443
theorem B9002171 : Blo 2107435 9002171 := bstep (se 1 (by rfl) ⟨6751628, by rfl⟩ : syracuseStep 9002171 = 13503257) B13503257
theorem B6001447 : Blo 2107435 6001447 := bstep (se 1 (by rfl) ⟨4501085, by rfl⟩ : syracuseStep 6001447 = 9002171) B9002171
theorem B8001929 : Blo 2107435 8001929 := bstep (se 2 (by rfl) ⟨3000723, by rfl⟩ : syracuseStep 8001929 = 6001447) B6001447
theorem B5334619 : Blo 2107435 5334619 := bstep (se 1 (by rfl) ⟨4000964, by rfl⟩ : syracuseStep 5334619 = 8001929) B8001929
theorem B7112825 : Blo 2107435 7112825 := bstep (se 2 (by rfl) ⟨2667309, by rfl⟩ : syracuseStep 7112825 = 5334619) B5334619
theorem B4741883 : Blo 2107435 4741883 := bstep (se 1 (by rfl) ⟨3556412, by rfl⟩ : syracuseStep 4741883 = 7112825) B7112825
theorem B3161255 : Blo 2107435 3161255 := bstep (se 1 (by rfl) ⟨2370941, by rfl⟩ : syracuseStep 3161255 = 4741883) B4741883
theorem B2107503 : Blo 2107435 2107503 := bstep (se 1 (by rfl) ⟨1580627, by rfl⟩ : syracuseStep 2107503 = 3161255) B3161255
theorem B3161261 : Blo 2107435 3161261 := bbase (se 3 (by rfl) ⟨592736, by rfl⟩ : syracuseStep 3161261 = 1185473) (by norm_num)
theorem B2107507 : Blo 2107435 2107507 := bstep (se 1 (by rfl) ⟨1580630, by rfl⟩ : syracuseStep 2107507 = 3161261) B3161261
theorem B4741901 : Blo 2107435 4741901 := bbase (se 3 (by rfl) ⟨889106, by rfl⟩ : syracuseStep 4741901 = 1778213) (by norm_num)
theorem B3161267 : Blo 2107435 3161267 := bstep (se 1 (by rfl) ⟨2370950, by rfl⟩ : syracuseStep 3161267 = 4741901) B4741901
theorem B2107511 : Blo 2107435 2107511 := bstep (se 1 (by rfl) ⟨1580633, by rfl⟩ : syracuseStep 2107511 = 3161267) B3161267
theorem B2667325 : Blo 2107435 2667325 := bbase (se 3 (by rfl) ⟨500123, by rfl⟩ : syracuseStep 2667325 = 1000247) (by norm_num)
theorem B3556433 : Blo 2107435 3556433 := bstep (se 2 (by rfl) ⟨1333662, by rfl⟩ : syracuseStep 3556433 = 2667325) B2667325
theorem B2370955 : Blo 2107435 2370955 := bstep (se 1 (by rfl) ⟨1778216, by rfl⟩ : syracuseStep 2370955 = 3556433) B3556433
theorem B3161273 : Blo 2107435 3161273 := bstep (se 2 (by rfl) ⟨1185477, by rfl⟩ : syracuseStep 3161273 = 2370955) B2370955
theorem B2107515 : Blo 2107435 2107515 := bstep (se 1 (by rfl) ⟨1580636, by rfl⟩ : syracuseStep 2107515 = 3161273) B3161273
theorem B2436097 : Blo 2107435 2436097 := bbase (se 2 (by rfl) ⟨913536, by rfl⟩ : syracuseStep 2436097 = 1827073) (by norm_num)
theorem B51970069 : Blo 2107435 51970069 := bstep (se 6 (by rfl) ⟨1218048, by rfl⟩ : syracuseStep 51970069 = 2436097) B2436097
theorem B277173701 : Blo 2107435 277173701 := bstep (se 4 (by rfl) ⟨25985034, by rfl⟩ : syracuseStep 277173701 = 51970069) B51970069
theorem B184782467 : Blo 2107435 184782467 := bstep (se 1 (by rfl) ⟨138586850, by rfl⟩ : syracuseStep 184782467 = 277173701) B277173701
theorem B123188311 : Blo 2107435 123188311 := bstep (se 1 (by rfl) ⟨92391233, by rfl⟩ : syracuseStep 123188311 = 184782467) B184782467
theorem B164251081 : Blo 2107435 164251081 := bstep (se 2 (by rfl) ⟨61594155, by rfl⟩ : syracuseStep 164251081 = 123188311) B123188311
theorem B219001441 : Blo 2107435 219001441 := bstep (se 2 (by rfl) ⟨82125540, by rfl⟩ : syracuseStep 219001441 = 164251081) B164251081
theorem B292001921 : Blo 2107435 292001921 := bstep (se 2 (by rfl) ⟨109500720, by rfl⟩ : syracuseStep 292001921 = 219001441) B219001441
theorem B194667947 : Blo 2107435 194667947 := bstep (se 1 (by rfl) ⟨146000960, by rfl⟩ : syracuseStep 194667947 = 292001921) B292001921
theorem B129778631 : Blo 2107435 129778631 := bstep (se 1 (by rfl) ⟨97333973, by rfl⟩ : syracuseStep 129778631 = 194667947) B194667947
theorem B86519087 : Blo 2107435 86519087 := bstep (se 1 (by rfl) ⟨64889315, by rfl⟩ : syracuseStep 86519087 = 129778631) B129778631
theorem B57679391 : Blo 2107435 57679391 := bstep (se 1 (by rfl) ⟨43259543, by rfl⟩ : syracuseStep 57679391 = 86519087) B86519087
theorem B38452927 : Blo 2107435 38452927 := bstep (se 1 (by rfl) ⟨28839695, by rfl⟩ : syracuseStep 38452927 = 57679391) B57679391
theorem B51270569 : Blo 2107435 51270569 := bstep (se 2 (by rfl) ⟨19226463, by rfl⟩ : syracuseStep 51270569 = 38452927) B38452927
theorem B34180379 : Blo 2107435 34180379 := bstep (se 1 (by rfl) ⟨25635284, by rfl⟩ : syracuseStep 34180379 = 51270569) B51270569
theorem B22786919 : Blo 2107435 22786919 := bstep (se 1 (by rfl) ⟨17090189, by rfl⟩ : syracuseStep 22786919 = 34180379) B34180379
theorem B15191279 : Blo 2107435 15191279 := bstep (se 1 (by rfl) ⟨11393459, by rfl⟩ : syracuseStep 15191279 = 22786919) B22786919
theorem B10127519 : Blo 2107435 10127519 := bstep (se 1 (by rfl) ⟨7595639, by rfl⟩ : syracuseStep 10127519 = 15191279) B15191279
theorem B6751679 : Blo 2107435 6751679 := bstep (se 1 (by rfl) ⟨5063759, by rfl⟩ : syracuseStep 6751679 = 10127519) B10127519
theorem B18004477 : Blo 2107435 18004477 := bstep (se 3 (by rfl) ⟨3375839, by rfl⟩ : syracuseStep 18004477 = 6751679) B6751679
theorem B24005969 : Blo 2107435 24005969 := bstep (se 2 (by rfl) ⟨9002238, by rfl⟩ : syracuseStep 24005969 = 18004477) B18004477
theorem B16003979 : Blo 2107435 16003979 := bstep (se 1 (by rfl) ⟨12002984, by rfl⟩ : syracuseStep 16003979 = 24005969) B24005969
theorem B10669319 : Blo 2107435 10669319 := bstep (se 1 (by rfl) ⟨8001989, by rfl⟩ : syracuseStep 10669319 = 16003979) B16003979
theorem B7112879 : Blo 2107435 7112879 := bstep (se 1 (by rfl) ⟨5334659, by rfl⟩ : syracuseStep 7112879 = 10669319) B10669319
theorem B4741919 : Blo 2107435 4741919 := bstep (se 1 (by rfl) ⟨3556439, by rfl⟩ : syracuseStep 4741919 = 7112879) B7112879
theorem B3161279 : Blo 2107435 3161279 := bstep (se 1 (by rfl) ⟨2370959, by rfl⟩ : syracuseStep 3161279 = 4741919) B4741919
theorem B2107519 : Blo 2107435 2107519 := bstep (se 1 (by rfl) ⟨1580639, by rfl⟩ : syracuseStep 2107519 = 3161279) B3161279
theorem B3161285 : Blo 2107435 3161285 := bbase (se 4 (by rfl) ⟨296370, by rfl⟩ : syracuseStep 3161285 = 592741) (by norm_num)
theorem B2107523 : Blo 2107435 2107523 := bstep (se 1 (by rfl) ⟨1580642, by rfl⟩ : syracuseStep 2107523 = 3161285) B3161285
theorem B3556453 : Blo 2107435 3556453 := bbase (se 4 (by rfl) ⟨333417, by rfl⟩ : syracuseStep 3556453 = 666835) (by norm_num)
theorem B4741937 : Blo 2107435 4741937 := bstep (se 2 (by rfl) ⟨1778226, by rfl⟩ : syracuseStep 4741937 = 3556453) B3556453
theorem B3161291 : Blo 2107435 3161291 := bstep (se 1 (by rfl) ⟨2370968, by rfl⟩ : syracuseStep 3161291 = 4741937) B4741937
theorem B2107527 : Blo 2107435 2107527 := bstep (se 1 (by rfl) ⟨1580645, by rfl⟩ : syracuseStep 2107527 = 3161291) B3161291
theorem B2370973 : Blo 2107435 2370973 := bbase (se 3 (by rfl) ⟨444557, by rfl⟩ : syracuseStep 2370973 = 889115) (by norm_num)
theorem B3161297 : Blo 2107435 3161297 := bstep (se 2 (by rfl) ⟨1185486, by rfl⟩ : syracuseStep 3161297 = 2370973) B2370973
theorem B2107531 : Blo 2107435 2107531 := bstep (se 1 (by rfl) ⟨1580648, by rfl⟩ : syracuseStep 2107531 = 3161297) B3161297
theorem B7112933 : Blo 2107435 7112933 := bbase (se 4 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 7112933 = 1333675) (by norm_num)
theorem B4741955 : Blo 2107435 4741955 := bstep (se 1 (by rfl) ⟨3556466, by rfl⟩ : syracuseStep 4741955 = 7112933) B7112933
theorem B3161303 : Blo 2107435 3161303 := bstep (se 1 (by rfl) ⟨2370977, by rfl⟩ : syracuseStep 3161303 = 4741955) B4741955
theorem B2107535 : Blo 2107435 2107535 := bstep (se 1 (by rfl) ⟨1580651, by rfl⟩ : syracuseStep 2107535 = 3161303) B3161303
theorem B3161309 : Blo 2107435 3161309 := bbase (se 3 (by rfl) ⟨592745, by rfl⟩ : syracuseStep 3161309 = 1185491) (by norm_num)
theorem B2107539 : Blo 2107435 2107539 := bstep (se 1 (by rfl) ⟨1580654, by rfl⟩ : syracuseStep 2107539 = 3161309) B3161309
theorem B4741973 : Blo 2107435 4741973 := bbase (se 9 (by rfl) ⟨13892, by rfl⟩ : syracuseStep 4741973 = 27785) (by norm_num)
theorem B3161315 : Blo 2107435 3161315 := bstep (se 1 (by rfl) ⟨2370986, by rfl⟩ : syracuseStep 3161315 = 4741973) B4741973
theorem B2107543 : Blo 2107435 2107543 := bstep (se 1 (by rfl) ⟨1580657, by rfl⟩ : syracuseStep 2107543 = 3161315) B3161315
theorem B6001573 : Blo 2107435 6001573 := bbase (se 4 (by rfl) ⟨562647, by rfl⟩ : syracuseStep 6001573 = 1125295) (by norm_num)
theorem B8002097 : Blo 2107435 8002097 := bstep (se 2 (by rfl) ⟨3000786, by rfl⟩ : syracuseStep 8002097 = 6001573) B6001573
theorem B5334731 : Blo 2107435 5334731 := bstep (se 1 (by rfl) ⟨4001048, by rfl⟩ : syracuseStep 5334731 = 8002097) B8002097
theorem B3556487 : Blo 2107435 3556487 := bstep (se 1 (by rfl) ⟨2667365, by rfl⟩ : syracuseStep 3556487 = 5334731) B5334731
theorem B2370991 : Blo 2107435 2370991 := bstep (se 1 (by rfl) ⟨1778243, by rfl⟩ : syracuseStep 2370991 = 3556487) B3556487
theorem B3161321 : Blo 2107435 3161321 := bstep (se 2 (by rfl) ⟨1185495, by rfl⟩ : syracuseStep 3161321 = 2370991) B2370991
theorem B2107547 : Blo 2107435 2107547 := bstep (se 1 (by rfl) ⟨1580660, by rfl⟩ : syracuseStep 2107547 = 3161321) B3161321
theorem B60766037 : Blo 2107435 60766037 := bbase (se 9 (by rfl) ⟨178025, by rfl⟩ : syracuseStep 60766037 = 356051) (by norm_num)
theorem B40510691 : Blo 2107435 40510691 := bstep (se 1 (by rfl) ⟨30383018, by rfl⟩ : syracuseStep 40510691 = 60766037) B60766037
theorem B27007127 : Blo 2107435 27007127 := bstep (se 1 (by rfl) ⟨20255345, by rfl⟩ : syracuseStep 27007127 = 40510691) B40510691
theorem B18004751 : Blo 2107435 18004751 := bstep (se 1 (by rfl) ⟨13503563, by rfl⟩ : syracuseStep 18004751 = 27007127) B27007127
theorem B12003167 : Blo 2107435 12003167 := bstep (se 1 (by rfl) ⟨9002375, by rfl⟩ : syracuseStep 12003167 = 18004751) B18004751
theorem B8002111 : Blo 2107435 8002111 := bstep (se 1 (by rfl) ⟨6001583, by rfl⟩ : syracuseStep 8002111 = 12003167) B12003167
theorem B10669481 : Blo 2107435 10669481 := bstep (se 2 (by rfl) ⟨4001055, by rfl⟩ : syracuseStep 10669481 = 8002111) B8002111
theorem B7112987 : Blo 2107435 7112987 := bstep (se 1 (by rfl) ⟨5334740, by rfl⟩ : syracuseStep 7112987 = 10669481) B10669481
theorem B4741991 : Blo 2107435 4741991 := bstep (se 1 (by rfl) ⟨3556493, by rfl⟩ : syracuseStep 4741991 = 7112987) B7112987
theorem B3161327 : Blo 2107435 3161327 := bstep (se 1 (by rfl) ⟨2370995, by rfl⟩ : syracuseStep 3161327 = 4741991) B4741991
theorem B2107551 : Blo 2107435 2107551 := bstep (se 1 (by rfl) ⟨1580663, by rfl⟩ : syracuseStep 2107551 = 3161327) B3161327
theorem B3161333 : Blo 2107435 3161333 := bbase (se 5 (by rfl) ⟨148187, by rfl⟩ : syracuseStep 3161333 = 296375) (by norm_num)
theorem B2107555 : Blo 2107435 2107555 := bstep (se 1 (by rfl) ⟨1580666, by rfl⟩ : syracuseStep 2107555 = 3161333) B3161333
theorem B9125237 : Blo 2107435 9125237 := bbase (se 5 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 9125237 = 855491) (by norm_num)
theorem B24333965 : Blo 2107435 24333965 := bstep (se 3 (by rfl) ⟨4562618, by rfl⟩ : syracuseStep 24333965 = 9125237) B9125237
theorem B16222643 : Blo 2107435 16222643 := bstep (se 1 (by rfl) ⟨12166982, by rfl⟩ : syracuseStep 16222643 = 24333965) B24333965
theorem B10815095 : Blo 2107435 10815095 := bstep (se 1 (by rfl) ⟨8111321, by rfl⟩ : syracuseStep 10815095 = 16222643) B16222643
theorem B7210063 : Blo 2107435 7210063 := bstep (se 1 (by rfl) ⟨5407547, by rfl⟩ : syracuseStep 7210063 = 10815095) B10815095
theorem B9613417 : Blo 2107435 9613417 := bstep (se 2 (by rfl) ⟨3605031, by rfl⟩ : syracuseStep 9613417 = 7210063) B7210063
theorem B12817889 : Blo 2107435 12817889 := bstep (se 2 (by rfl) ⟨4806708, by rfl⟩ : syracuseStep 12817889 = 9613417) B9613417
theorem B8545259 : Blo 2107435 8545259 := bstep (se 1 (by rfl) ⟨6408944, by rfl⟩ : syracuseStep 8545259 = 12817889) B12817889
theorem B5696839 : Blo 2107435 5696839 := bstep (se 1 (by rfl) ⟨4272629, by rfl⟩ : syracuseStep 5696839 = 8545259) B8545259
theorem B7595785 : Blo 2107435 7595785 := bstep (se 2 (by rfl) ⟨2848419, by rfl⟩ : syracuseStep 7595785 = 5696839) B5696839
theorem B10127713 : Blo 2107435 10127713 := bstep (se 2 (by rfl) ⟨3797892, by rfl⟩ : syracuseStep 10127713 = 7595785) B7595785
theorem B13503617 : Blo 2107435 13503617 := bstep (se 2 (by rfl) ⟨5063856, by rfl⟩ : syracuseStep 13503617 = 10127713) B10127713
theorem B9002411 : Blo 2107435 9002411 := bstep (se 1 (by rfl) ⟨6751808, by rfl⟩ : syracuseStep 9002411 = 13503617) B13503617
theorem B6001607 : Blo 2107435 6001607 := bstep (se 1 (by rfl) ⟨4501205, by rfl⟩ : syracuseStep 6001607 = 9002411) B9002411
theorem B4001071 : Blo 2107435 4001071 := bstep (se 1 (by rfl) ⟨3000803, by rfl⟩ : syracuseStep 4001071 = 6001607) B6001607
theorem B5334761 : Blo 2107435 5334761 := bstep (se 2 (by rfl) ⟨2000535, by rfl⟩ : syracuseStep 5334761 = 4001071) B4001071
theorem B3556507 : Blo 2107435 3556507 := bstep (se 1 (by rfl) ⟨2667380, by rfl⟩ : syracuseStep 3556507 = 5334761) B5334761
theorem B4742009 : Blo 2107435 4742009 := bstep (se 2 (by rfl) ⟨1778253, by rfl⟩ : syracuseStep 4742009 = 3556507) B3556507
theorem B3161339 : Blo 2107435 3161339 := bstep (se 1 (by rfl) ⟨2371004, by rfl⟩ : syracuseStep 3161339 = 4742009) B4742009
theorem B2107559 : Blo 2107435 2107559 := bstep (se 1 (by rfl) ⟨1580669, by rfl⟩ : syracuseStep 2107559 = 3161339) B3161339
theorem B2371009 : Blo 2107435 2371009 := bbase (se 2 (by rfl) ⟨889128, by rfl⟩ : syracuseStep 2371009 = 1778257) (by norm_num)
theorem B3161345 : Blo 2107435 3161345 := bstep (se 2 (by rfl) ⟨1185504, by rfl⟩ : syracuseStep 3161345 = 2371009) B2371009
theorem B2107563 : Blo 2107435 2107563 := bstep (se 1 (by rfl) ⟨1580672, by rfl⟩ : syracuseStep 2107563 = 3161345) B3161345
theorem B5334781 : Blo 2107435 5334781 := bbase (se 3 (by rfl) ⟨1000271, by rfl⟩ : syracuseStep 5334781 = 2000543) (by norm_num)
theorem B7113041 : Blo 2107435 7113041 := bstep (se 2 (by rfl) ⟨2667390, by rfl⟩ : syracuseStep 7113041 = 5334781) B5334781
theorem B4742027 : Blo 2107435 4742027 := bstep (se 1 (by rfl) ⟨3556520, by rfl⟩ : syracuseStep 4742027 = 7113041) B7113041
theorem B3161351 : Blo 2107435 3161351 := bstep (se 1 (by rfl) ⟨2371013, by rfl⟩ : syracuseStep 3161351 = 4742027) B4742027
theorem B2107567 : Blo 2107435 2107567 := bstep (se 1 (by rfl) ⟨1580675, by rfl⟩ : syracuseStep 2107567 = 3161351) B3161351
theorem B3161357 : Blo 2107435 3161357 := bbase (se 3 (by rfl) ⟨592754, by rfl⟩ : syracuseStep 3161357 = 1185509) (by norm_num)
theorem B2107571 : Blo 2107435 2107571 := bstep (se 1 (by rfl) ⟨1580678, by rfl⟩ : syracuseStep 2107571 = 3161357) B3161357
theorem B4742045 : Blo 2107435 4742045 := bbase (se 3 (by rfl) ⟨889133, by rfl⟩ : syracuseStep 4742045 = 1778267) (by norm_num)
theorem B3161363 : Blo 2107435 3161363 := bstep (se 1 (by rfl) ⟨2371022, by rfl⟩ : syracuseStep 3161363 = 4742045) B4742045
theorem B2107575 : Blo 2107435 2107575 := bstep (se 1 (by rfl) ⟨1580681, by rfl⟩ : syracuseStep 2107575 = 3161363) B3161363
theorem B3556541 : Blo 2107435 3556541 := bbase (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) (by norm_num)
theorem B2371027 : Blo 2107435 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B3161369 : Blo 2107435 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B2107579 : Blo 2107435 2107579 := bstep (se 1 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 2107579 = 3161369) B3161369
theorem B12003349 : Blo 2107435 12003349 := bbase (se 6 (by rfl) ⟨281328, by rfl⟩ : syracuseStep 12003349 = 562657) (by norm_num)
theorem B16004465 : Blo 2107435 16004465 := bstep (se 2 (by rfl) ⟨6001674, by rfl⟩ : syracuseStep 16004465 = 12003349) B12003349
theorem B10669643 : Blo 2107435 10669643 := bstep (se 1 (by rfl) ⟨8002232, by rfl⟩ : syracuseStep 10669643 = 16004465) B16004465
theorem B7113095 : Blo 2107435 7113095 := bstep (se 1 (by rfl) ⟨5334821, by rfl⟩ : syracuseStep 7113095 = 10669643) B10669643
theorem B4742063 : Blo 2107435 4742063 := bstep (se 1 (by rfl) ⟨3556547, by rfl⟩ : syracuseStep 4742063 = 7113095) B7113095
theorem B3161375 : Blo 2107435 3161375 := bstep (se 1 (by rfl) ⟨2371031, by rfl⟩ : syracuseStep 3161375 = 4742063) B4742063
theorem B2107583 : Blo 2107435 2107583 := bstep (se 1 (by rfl) ⟨1580687, by rfl⟩ : syracuseStep 2107583 = 3161375) B3161375
theorem B3161381 : Blo 2107435 3161381 := bbase (se 4 (by rfl) ⟨296379, by rfl⟩ : syracuseStep 3161381 = 592759) (by norm_num)
theorem B2107587 : Blo 2107435 2107587 := bstep (se 1 (by rfl) ⟨1580690, by rfl⟩ : syracuseStep 2107587 = 3161381) B3161381
theorem B2667421 : Blo 2107435 2667421 := bbase (se 3 (by rfl) ⟨500141, by rfl⟩ : syracuseStep 2667421 = 1000283) (by norm_num)
theorem B3556561 : Blo 2107435 3556561 := bstep (se 2 (by rfl) ⟨1333710, by rfl⟩ : syracuseStep 3556561 = 2667421) B2667421
theorem B4742081 : Blo 2107435 4742081 := bstep (se 2 (by rfl) ⟨1778280, by rfl⟩ : syracuseStep 4742081 = 3556561) B3556561
theorem B3161387 : Blo 2107435 3161387 := bstep (se 1 (by rfl) ⟨2371040, by rfl⟩ : syracuseStep 3161387 = 4742081) B4742081
theorem B2107591 : Blo 2107435 2107591 := bstep (se 1 (by rfl) ⟨1580693, by rfl⟩ : syracuseStep 2107591 = 3161387) B3161387
theorem B2371045 : Blo 2107435 2371045 := bbase (se 4 (by rfl) ⟨222285, by rfl⟩ : syracuseStep 2371045 = 444571) (by norm_num)
theorem B3161393 : Blo 2107435 3161393 := bstep (se 2 (by rfl) ⟨1185522, by rfl⟩ : syracuseStep 3161393 = 2371045) B2371045
theorem B2107595 : Blo 2107435 2107595 := bstep (se 1 (by rfl) ⟨1580696, by rfl⟩ : syracuseStep 2107595 = 3161393) B3161393
theorem B3797965 : Blo 2107435 3797965 := bbase (se 3 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 3797965 = 1424237) (by norm_num)
theorem B5063953 : Blo 2107435 5063953 := bstep (se 2 (by rfl) ⟨1898982, by rfl⟩ : syracuseStep 5063953 = 3797965) B3797965
theorem B6751937 : Blo 2107435 6751937 := bstep (se 2 (by rfl) ⟨2531976, by rfl⟩ : syracuseStep 6751937 = 5063953) B5063953
theorem B4501291 : Blo 2107435 4501291 := bstep (se 1 (by rfl) ⟨3375968, by rfl⟩ : syracuseStep 4501291 = 6751937) B6751937
theorem B6001721 : Blo 2107435 6001721 := bstep (se 2 (by rfl) ⟨2250645, by rfl⟩ : syracuseStep 6001721 = 4501291) B4501291
theorem B4001147 : Blo 2107435 4001147 := bstep (se 1 (by rfl) ⟨3000860, by rfl⟩ : syracuseStep 4001147 = 6001721) B6001721
theorem B2667431 : Blo 2107435 2667431 := bstep (se 1 (by rfl) ⟨2000573, by rfl⟩ : syracuseStep 2667431 = 4001147) B4001147
theorem B7113149 : Blo 2107435 7113149 := bstep (se 3 (by rfl) ⟨1333715, by rfl⟩ : syracuseStep 7113149 = 2667431) B2667431
theorem B4742099 : Blo 2107435 4742099 := bstep (se 1 (by rfl) ⟨3556574, by rfl⟩ : syracuseStep 4742099 = 7113149) B7113149
theorem B3161399 : Blo 2107435 3161399 := bstep (se 1 (by rfl) ⟨2371049, by rfl⟩ : syracuseStep 3161399 = 4742099) B4742099
theorem B2107599 : Blo 2107435 2107599 := bstep (se 1 (by rfl) ⟨1580699, by rfl⟩ : syracuseStep 2107599 = 3161399) B3161399
theorem B3161405 : Blo 2107435 3161405 := bbase (se 3 (by rfl) ⟨592763, by rfl⟩ : syracuseStep 3161405 = 1185527) (by norm_num)
theorem B2107603 : Blo 2107435 2107603 := bstep (se 1 (by rfl) ⟨1580702, by rfl⟩ : syracuseStep 2107603 = 3161405) B3161405
theorem B4742117 : Blo 2107435 4742117 := bbase (se 4 (by rfl) ⟨444573, by rfl⟩ : syracuseStep 4742117 = 889147) (by norm_num)
theorem B3161411 : Blo 2107435 3161411 := bstep (se 1 (by rfl) ⟨2371058, by rfl⟩ : syracuseStep 3161411 = 4742117) B4742117
theorem B2107607 : Blo 2107435 2107607 := bstep (se 1 (by rfl) ⟨1580705, by rfl⟩ : syracuseStep 2107607 = 3161411) B3161411
theorem B5334893 : Blo 2107435 5334893 := bbase (se 3 (by rfl) ⟨1000292, by rfl⟩ : syracuseStep 5334893 = 2000585) (by norm_num)
theorem B3556595 : Blo 2107435 3556595 := bstep (se 1 (by rfl) ⟨2667446, by rfl⟩ : syracuseStep 3556595 = 5334893) B5334893
theorem B2371063 : Blo 2107435 2371063 := bstep (se 1 (by rfl) ⟨1778297, by rfl⟩ : syracuseStep 2371063 = 3556595) B3556595
theorem B3161417 : Blo 2107435 3161417 := bstep (se 2 (by rfl) ⟨1185531, by rfl⟩ : syracuseStep 3161417 = 2371063) B2371063
theorem B2107611 : Blo 2107435 2107611 := bstep (se 1 (by rfl) ⟨1580708, by rfl⟩ : syracuseStep 2107611 = 3161417) B3161417
theorem B4501325 : Blo 2107435 4501325 := bbase (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) (by norm_num)
theorem B3000883 : Blo 2107435 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B4001177 : Blo 2107435 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B10669805 : Blo 2107435 10669805 := bstep (se 3 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 10669805 = 4001177) B4001177
theorem B7113203 : Blo 2107435 7113203 := bstep (se 1 (by rfl) ⟨5334902, by rfl⟩ : syracuseStep 7113203 = 10669805) B10669805
theorem B4742135 : Blo 2107435 4742135 := bstep (se 1 (by rfl) ⟨3556601, by rfl⟩ : syracuseStep 4742135 = 7113203) B7113203
theorem B3161423 : Blo 2107435 3161423 := bstep (se 1 (by rfl) ⟨2371067, by rfl⟩ : syracuseStep 3161423 = 4742135) B4742135
theorem B2107615 : Blo 2107435 2107615 := bstep (se 1 (by rfl) ⟨1580711, by rfl⟩ : syracuseStep 2107615 = 3161423) B3161423
theorem B3161429 : Blo 2107435 3161429 := bbase (se 11 (by rfl) ⟨2315, by rfl⟩ : syracuseStep 3161429 = 4631) (by norm_num)
theorem B2107619 : Blo 2107435 2107619 := bstep (se 1 (by rfl) ⟨1580714, by rfl⟩ : syracuseStep 2107619 = 3161429) B3161429
theorem B5697013 : Blo 2107435 5697013 := bbase (se 5 (by rfl) ⟨267047, by rfl⟩ : syracuseStep 5697013 = 534095) (by norm_num)
theorem B7596017 : Blo 2107435 7596017 := bstep (se 2 (by rfl) ⟨2848506, by rfl⟩ : syracuseStep 7596017 = 5697013) B5697013
theorem B5064011 : Blo 2107435 5064011 := bstep (se 1 (by rfl) ⟨3798008, by rfl⟩ : syracuseStep 5064011 = 7596017) B7596017
theorem B3376007 : Blo 2107435 3376007 := bstep (se 1 (by rfl) ⟨2532005, by rfl⟩ : syracuseStep 3376007 = 5064011) B5064011
theorem B2250671 : Blo 2107435 2250671 := bstep (se 1 (by rfl) ⟨1688003, by rfl⟩ : syracuseStep 2250671 = 3376007) B3376007
theorem B6001789 : Blo 2107435 6001789 := bstep (se 3 (by rfl) ⟨1125335, by rfl⟩ : syracuseStep 6001789 = 2250671) B2250671
theorem B8002385 : Blo 2107435 8002385 := bstep (se 2 (by rfl) ⟨3000894, by rfl⟩ : syracuseStep 8002385 = 6001789) B6001789
theorem B5334923 : Blo 2107435 5334923 := bstep (se 1 (by rfl) ⟨4001192, by rfl⟩ : syracuseStep 5334923 = 8002385) B8002385
theorem B3556615 : Blo 2107435 3556615 := bstep (se 1 (by rfl) ⟨2667461, by rfl⟩ : syracuseStep 3556615 = 5334923) B5334923
theorem B4742153 : Blo 2107435 4742153 := bstep (se 2 (by rfl) ⟨1778307, by rfl⟩ : syracuseStep 4742153 = 3556615) B3556615
theorem B3161435 : Blo 2107435 3161435 := bstep (se 1 (by rfl) ⟨2371076, by rfl⟩ : syracuseStep 3161435 = 4742153) B4742153
theorem B2107623 : Blo 2107435 2107623 := bstep (se 1 (by rfl) ⟨1580717, by rfl⟩ : syracuseStep 2107623 = 3161435) B3161435
theorem B2371081 : Blo 2107435 2371081 := bbase (se 2 (by rfl) ⟨889155, by rfl⟩ : syracuseStep 2371081 = 1778311) (by norm_num)
theorem B3161441 : Blo 2107435 3161441 := bstep (se 2 (by rfl) ⟨1185540, by rfl⟩ : syracuseStep 3161441 = 2371081) B2371081
theorem B2107627 : Blo 2107435 2107627 := bstep (se 1 (by rfl) ⟨1580720, by rfl⟩ : syracuseStep 2107627 = 3161441) B3161441
theorem B3204581 : Blo 2107435 3204581 := bbase (se 4 (by rfl) ⟨300429, by rfl⟩ : syracuseStep 3204581 = 600859) (by norm_num)
theorem B8545549 : Blo 2107435 8545549 := bstep (se 3 (by rfl) ⟨1602290, by rfl⟩ : syracuseStep 8545549 = 3204581) B3204581
theorem B11394065 : Blo 2107435 11394065 := bstep (se 2 (by rfl) ⟨4272774, by rfl⟩ : syracuseStep 11394065 = 8545549) B8545549
theorem B30384173 : Blo 2107435 30384173 := bstep (se 3 (by rfl) ⟨5697032, by rfl⟩ : syracuseStep 30384173 = 11394065) B11394065
theorem B20256115 : Blo 2107435 20256115 := bstep (se 1 (by rfl) ⟨15192086, by rfl⟩ : syracuseStep 20256115 = 30384173) B30384173
theorem B27008153 : Blo 2107435 27008153 := bstep (se 2 (by rfl) ⟨10128057, by rfl⟩ : syracuseStep 27008153 = 20256115) B20256115
theorem B18005435 : Blo 2107435 18005435 := bstep (se 1 (by rfl) ⟨13504076, by rfl⟩ : syracuseStep 18005435 = 27008153) B27008153
theorem B12003623 : Blo 2107435 12003623 := bstep (se 1 (by rfl) ⟨9002717, by rfl⟩ : syracuseStep 12003623 = 18005435) B18005435
theorem B8002415 : Blo 2107435 8002415 := bstep (se 1 (by rfl) ⟨6001811, by rfl⟩ : syracuseStep 8002415 = 12003623) B12003623
theorem B5334943 : Blo 2107435 5334943 := bstep (se 1 (by rfl) ⟨4001207, by rfl⟩ : syracuseStep 5334943 = 8002415) B8002415
theorem B7113257 : Blo 2107435 7113257 := bstep (se 2 (by rfl) ⟨2667471, by rfl⟩ : syracuseStep 7113257 = 5334943) B5334943
theorem B4742171 : Blo 2107435 4742171 := bstep (se 1 (by rfl) ⟨3556628, by rfl⟩ : syracuseStep 4742171 = 7113257) B7113257
theorem B3161447 : Blo 2107435 3161447 := bstep (se 1 (by rfl) ⟨2371085, by rfl⟩ : syracuseStep 3161447 = 4742171) B4742171
theorem B2107631 : Blo 2107435 2107631 := bstep (se 1 (by rfl) ⟨1580723, by rfl⟩ : syracuseStep 2107631 = 3161447) B3161447
theorem B3161453 : Blo 2107435 3161453 := bbase (se 3 (by rfl) ⟨592772, by rfl⟩ : syracuseStep 3161453 = 1185545) (by norm_num)
theorem B2107635 : Blo 2107435 2107635 := bstep (se 1 (by rfl) ⟨1580726, by rfl⟩ : syracuseStep 2107635 = 3161453) B3161453
theorem B4742189 : Blo 2107435 4742189 := bbase (se 3 (by rfl) ⟨889160, by rfl⟩ : syracuseStep 4742189 = 1778321) (by norm_num)
theorem B3161459 : Blo 2107435 3161459 := bstep (se 1 (by rfl) ⟨2371094, by rfl⟩ : syracuseStep 3161459 = 4742189) B4742189
theorem B2107639 : Blo 2107435 2107639 := bstep (se 1 (by rfl) ⟨1580729, by rfl⟩ : syracuseStep 2107639 = 3161459) B3161459
theorem B4806901 : Blo 2107435 4806901 := bbase (se 5 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 4806901 = 450647) (by norm_num)
theorem B6409201 : Blo 2107435 6409201 := bstep (se 2 (by rfl) ⟨2403450, by rfl⟩ : syracuseStep 6409201 = 4806901) B4806901
theorem B8545601 : Blo 2107435 8545601 := bstep (se 2 (by rfl) ⟨3204600, by rfl⟩ : syracuseStep 8545601 = 6409201) B6409201
theorem B5697067 : Blo 2107435 5697067 := bstep (se 1 (by rfl) ⟨4272800, by rfl⟩ : syracuseStep 5697067 = 8545601) B8545601
theorem B7596089 : Blo 2107435 7596089 := bstep (se 2 (by rfl) ⟨2848533, by rfl⟩ : syracuseStep 7596089 = 5697067) B5697067
theorem B5064059 : Blo 2107435 5064059 := bstep (se 1 (by rfl) ⟨3798044, by rfl⟩ : syracuseStep 5064059 = 7596089) B7596089
theorem B13504157 : Blo 2107435 13504157 := bstep (se 3 (by rfl) ⟨2532029, by rfl⟩ : syracuseStep 13504157 = 5064059) B5064059
theorem B9002771 : Blo 2107435 9002771 := bstep (se 1 (by rfl) ⟨6752078, by rfl⟩ : syracuseStep 9002771 = 13504157) B13504157
theorem B6001847 : Blo 2107435 6001847 := bstep (se 1 (by rfl) ⟨4501385, by rfl⟩ : syracuseStep 6001847 = 9002771) B9002771
theorem B4001231 : Blo 2107435 4001231 := bstep (se 1 (by rfl) ⟨3000923, by rfl⟩ : syracuseStep 4001231 = 6001847) B6001847
theorem B2667487 : Blo 2107435 2667487 := bstep (se 1 (by rfl) ⟨2000615, by rfl⟩ : syracuseStep 2667487 = 4001231) B4001231
theorem B3556649 : Blo 2107435 3556649 := bstep (se 2 (by rfl) ⟨1333743, by rfl⟩ : syracuseStep 3556649 = 2667487) B2667487
theorem B2371099 : Blo 2107435 2371099 := bstep (se 1 (by rfl) ⟨1778324, by rfl⟩ : syracuseStep 2371099 = 3556649) B3556649
theorem B3161465 : Blo 2107435 3161465 := bstep (se 2 (by rfl) ⟨1185549, by rfl⟩ : syracuseStep 3161465 = 2371099) B2371099
theorem B2107643 : Blo 2107435 2107643 := bstep (se 1 (by rfl) ⟨1580732, by rfl⟩ : syracuseStep 2107643 = 3161465) B3161465
theorem B7596101 : Blo 2107435 7596101 := bbase (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) (by norm_num)
theorem B5064067 : Blo 2107435 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B6752089 : Blo 2107435 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B36011141 : Blo 2107435 36011141 := bstep (se 4 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 36011141 = 6752089) B6752089
theorem B24007427 : Blo 2107435 24007427 := bstep (se 1 (by rfl) ⟨18005570, by rfl⟩ : syracuseStep 24007427 = 36011141) B36011141
theorem B16004951 : Blo 2107435 16004951 := bstep (se 1 (by rfl) ⟨12003713, by rfl⟩ : syracuseStep 16004951 = 24007427) B24007427
theorem B10669967 : Blo 2107435 10669967 := bstep (se 1 (by rfl) ⟨8002475, by rfl⟩ : syracuseStep 10669967 = 16004951) B16004951
theorem B7113311 : Blo 2107435 7113311 := bstep (se 1 (by rfl) ⟨5334983, by rfl⟩ : syracuseStep 7113311 = 10669967) B10669967
theorem B4742207 : Blo 2107435 4742207 := bstep (se 1 (by rfl) ⟨3556655, by rfl⟩ : syracuseStep 4742207 = 7113311) B7113311
theorem B3161471 : Blo 2107435 3161471 := bstep (se 1 (by rfl) ⟨2371103, by rfl⟩ : syracuseStep 3161471 = 4742207) B4742207
theorem B2107647 : Blo 2107435 2107647 := bstep (se 1 (by rfl) ⟨1580735, by rfl⟩ : syracuseStep 2107647 = 3161471) B3161471
theorem B3161477 : Blo 2107435 3161477 := bbase (se 4 (by rfl) ⟨296388, by rfl⟩ : syracuseStep 3161477 = 592777) (by norm_num)
theorem B2107651 : Blo 2107435 2107651 := bstep (se 1 (by rfl) ⟨1580738, by rfl⟩ : syracuseStep 2107651 = 3161477) B3161477
theorem B3556669 : Blo 2107435 3556669 := bbase (se 3 (by rfl) ⟨666875, by rfl⟩ : syracuseStep 3556669 = 1333751) (by norm_num)
theorem B4742225 : Blo 2107435 4742225 := bstep (se 2 (by rfl) ⟨1778334, by rfl⟩ : syracuseStep 4742225 = 3556669) B3556669
theorem B3161483 : Blo 2107435 3161483 := bstep (se 1 (by rfl) ⟨2371112, by rfl⟩ : syracuseStep 3161483 = 4742225) B4742225
theorem B2107655 : Blo 2107435 2107655 := bstep (se 1 (by rfl) ⟨1580741, by rfl⟩ : syracuseStep 2107655 = 3161483) B3161483
theorem B2371117 : Blo 2107435 2371117 := bbase (se 3 (by rfl) ⟨444584, by rfl⟩ : syracuseStep 2371117 = 889169) (by norm_num)
theorem B3161489 : Blo 2107435 3161489 := bstep (se 2 (by rfl) ⟨1185558, by rfl⟩ : syracuseStep 3161489 = 2371117) B2371117
theorem B2107659 : Blo 2107435 2107659 := bstep (se 1 (by rfl) ⟨1580744, by rfl⟩ : syracuseStep 2107659 = 3161489) B3161489
theorem B7113365 : Blo 2107435 7113365 := bbase (se 6 (by rfl) ⟨166719, by rfl⟩ : syracuseStep 7113365 = 333439) (by norm_num)
theorem B4742243 : Blo 2107435 4742243 := bstep (se 1 (by rfl) ⟨3556682, by rfl⟩ : syracuseStep 4742243 = 7113365) B7113365
theorem B3161495 : Blo 2107435 3161495 := bstep (se 1 (by rfl) ⟨2371121, by rfl⟩ : syracuseStep 3161495 = 4742243) B4742243
theorem B2107663 : Blo 2107435 2107663 := bstep (se 1 (by rfl) ⟨1580747, by rfl⟩ : syracuseStep 2107663 = 3161495) B3161495
theorem B3161501 : Blo 2107435 3161501 := bbase (se 3 (by rfl) ⟨592781, by rfl⟩ : syracuseStep 3161501 = 1185563) (by norm_num)
theorem B2107667 : Blo 2107435 2107667 := bstep (se 1 (by rfl) ⟨1580750, by rfl⟩ : syracuseStep 2107667 = 3161501) B3161501
theorem B4742261 : Blo 2107435 4742261 := bbase (se 5 (by rfl) ⟨222293, by rfl⟩ : syracuseStep 4742261 = 444587) (by norm_num)
theorem B3161507 : Blo 2107435 3161507 := bstep (se 1 (by rfl) ⟨2371130, by rfl⟩ : syracuseStep 3161507 = 4742261) B4742261
theorem B2107671 : Blo 2107435 2107671 := bstep (se 1 (by rfl) ⟨1580753, by rfl⟩ : syracuseStep 2107671 = 3161507) B3161507
theorem B18005813 : Blo 2107435 18005813 := bbase (se 5 (by rfl) ⟨844022, by rfl⟩ : syracuseStep 18005813 = 1688045) (by norm_num)
theorem B12003875 : Blo 2107435 12003875 := bstep (se 1 (by rfl) ⟨9002906, by rfl⟩ : syracuseStep 12003875 = 18005813) B18005813
theorem B8002583 : Blo 2107435 8002583 := bstep (se 1 (by rfl) ⟨6001937, by rfl⟩ : syracuseStep 8002583 = 12003875) B12003875
theorem B5335055 : Blo 2107435 5335055 := bstep (se 1 (by rfl) ⟨4001291, by rfl⟩ : syracuseStep 5335055 = 8002583) B8002583
theorem B3556703 : Blo 2107435 3556703 := bstep (se 1 (by rfl) ⟨2667527, by rfl⟩ : syracuseStep 3556703 = 5335055) B5335055
theorem B2371135 : Blo 2107435 2371135 := bstep (se 1 (by rfl) ⟨1778351, by rfl⟩ : syracuseStep 2371135 = 3556703) B3556703
theorem B3161513 : Blo 2107435 3161513 := bstep (se 2 (by rfl) ⟨1185567, by rfl⟩ : syracuseStep 3161513 = 2371135) B2371135
theorem B2107675 : Blo 2107435 2107675 := bstep (se 1 (by rfl) ⟨1580756, by rfl⟩ : syracuseStep 2107675 = 3161513) B3161513
theorem B8002597 : Blo 2107435 8002597 := bbase (se 4 (by rfl) ⟨750243, by rfl⟩ : syracuseStep 8002597 = 1500487) (by norm_num)
theorem B10670129 : Blo 2107435 10670129 := bstep (se 2 (by rfl) ⟨4001298, by rfl⟩ : syracuseStep 10670129 = 8002597) B8002597
theorem B7113419 : Blo 2107435 7113419 := bstep (se 1 (by rfl) ⟨5335064, by rfl⟩ : syracuseStep 7113419 = 10670129) B10670129
theorem B4742279 : Blo 2107435 4742279 := bstep (se 1 (by rfl) ⟨3556709, by rfl⟩ : syracuseStep 4742279 = 7113419) B7113419
theorem B3161519 : Blo 2107435 3161519 := bstep (se 1 (by rfl) ⟨2371139, by rfl⟩ : syracuseStep 3161519 = 4742279) B4742279
theorem B2107679 : Blo 2107435 2107679 := bstep (se 1 (by rfl) ⟨1580759, by rfl⟩ : syracuseStep 2107679 = 3161519) B3161519
theorem B3161525 : Blo 2107435 3161525 := bbase (se 5 (by rfl) ⟨148196, by rfl⟩ : syracuseStep 3161525 = 296393) (by norm_num)
theorem B2107683 : Blo 2107435 2107683 := bstep (se 1 (by rfl) ⟨1580762, by rfl⟩ : syracuseStep 2107683 = 3161525) B3161525
theorem B5335085 : Blo 2107435 5335085 := bbase (se 3 (by rfl) ⟨1000328, by rfl⟩ : syracuseStep 5335085 = 2000657) (by norm_num)
theorem B3556723 : Blo 2107435 3556723 := bstep (se 1 (by rfl) ⟨2667542, by rfl⟩ : syracuseStep 3556723 = 5335085) B5335085
theorem B4742297 : Blo 2107435 4742297 := bstep (se 2 (by rfl) ⟨1778361, by rfl⟩ : syracuseStep 4742297 = 3556723) B3556723
theorem B3161531 : Blo 2107435 3161531 := bstep (se 1 (by rfl) ⟨2371148, by rfl⟩ : syracuseStep 3161531 = 4742297) B4742297
theorem B2107687 : Blo 2107435 2107687 := bstep (se 1 (by rfl) ⟨1580765, by rfl⟩ : syracuseStep 2107687 = 3161531) B3161531
theorem B2371153 : Blo 2107435 2371153 := bbase (se 2 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 2371153 = 1778365) (by norm_num)
theorem B3161537 : Blo 2107435 3161537 := bstep (se 2 (by rfl) ⟨1185576, by rfl⟩ : syracuseStep 3161537 = 2371153) B2371153
theorem B2107691 : Blo 2107435 2107691 := bstep (se 1 (by rfl) ⟨1580768, by rfl⟩ : syracuseStep 2107691 = 3161537) B3161537
theorem B3000997 : Blo 2107435 3000997 := bbase (se 4 (by rfl) ⟨281343, by rfl⟩ : syracuseStep 3000997 = 562687) (by norm_num)
theorem B4001329 : Blo 2107435 4001329 := bstep (se 2 (by rfl) ⟨1500498, by rfl⟩ : syracuseStep 4001329 = 3000997) B3000997
theorem B5335105 : Blo 2107435 5335105 := bstep (se 2 (by rfl) ⟨2000664, by rfl⟩ : syracuseStep 5335105 = 4001329) B4001329
theorem B7113473 : Blo 2107435 7113473 := bstep (se 2 (by rfl) ⟨2667552, by rfl⟩ : syracuseStep 7113473 = 5335105) B5335105
theorem B4742315 : Blo 2107435 4742315 := bstep (se 1 (by rfl) ⟨3556736, by rfl⟩ : syracuseStep 4742315 = 7113473) B7113473
theorem B3161543 : Blo 2107435 3161543 := bstep (se 1 (by rfl) ⟨2371157, by rfl⟩ : syracuseStep 3161543 = 4742315) B4742315
theorem B2107695 : Blo 2107435 2107695 := bstep (se 1 (by rfl) ⟨1580771, by rfl⟩ : syracuseStep 2107695 = 3161543) B3161543
theorem B3161549 : Blo 2107435 3161549 := bbase (se 3 (by rfl) ⟨592790, by rfl⟩ : syracuseStep 3161549 = 1185581) (by norm_num)
theorem B2107699 : Blo 2107435 2107699 := bstep (se 1 (by rfl) ⟨1580774, by rfl⟩ : syracuseStep 2107699 = 3161549) B3161549
theorem B4742333 : Blo 2107435 4742333 := bbase (se 3 (by rfl) ⟨889187, by rfl⟩ : syracuseStep 4742333 = 1778375) (by norm_num)
theorem B3161555 : Blo 2107435 3161555 := bstep (se 1 (by rfl) ⟨2371166, by rfl⟩ : syracuseStep 3161555 = 4742333) B4742333
theorem B2107703 : Blo 2107435 2107703 := bstep (se 1 (by rfl) ⟨1580777, by rfl⟩ : syracuseStep 2107703 = 3161555) B3161555
theorem B3556757 : Blo 2107435 3556757 := bbase (se 6 (by rfl) ⟨83361, by rfl⟩ : syracuseStep 3556757 = 166723) (by norm_num)
theorem B2371171 : Blo 2107435 2371171 := bstep (se 1 (by rfl) ⟨1778378, by rfl⟩ : syracuseStep 2371171 = 3556757) B3556757
theorem B3161561 : Blo 2107435 3161561 := bstep (se 2 (by rfl) ⟨1185585, by rfl⟩ : syracuseStep 3161561 = 2371171) B2371171
theorem B2107707 : Blo 2107435 2107707 := bstep (se 1 (by rfl) ⟨1580780, by rfl⟩ : syracuseStep 2107707 = 3161561) B3161561
theorem B5064221 : Blo 2107435 5064221 := bbase (se 3 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 5064221 = 1899083) (by norm_num)
theorem B13504589 : Blo 2107435 13504589 := bstep (se 3 (by rfl) ⟨2532110, by rfl⟩ : syracuseStep 13504589 = 5064221) B5064221
theorem B9003059 : Blo 2107435 9003059 := bstep (se 1 (by rfl) ⟨6752294, by rfl⟩ : syracuseStep 9003059 = 13504589) B13504589
theorem B6002039 : Blo 2107435 6002039 := bstep (se 1 (by rfl) ⟨4501529, by rfl⟩ : syracuseStep 6002039 = 9003059) B9003059
theorem B16005437 : Blo 2107435 16005437 := bstep (se 3 (by rfl) ⟨3001019, by rfl⟩ : syracuseStep 16005437 = 6002039) B6002039
theorem B10670291 : Blo 2107435 10670291 := bstep (se 1 (by rfl) ⟨8002718, by rfl⟩ : syracuseStep 10670291 = 16005437) B16005437
theorem B7113527 : Blo 2107435 7113527 := bstep (se 1 (by rfl) ⟨5335145, by rfl⟩ : syracuseStep 7113527 = 10670291) B10670291
theorem B4742351 : Blo 2107435 4742351 := bstep (se 1 (by rfl) ⟨3556763, by rfl⟩ : syracuseStep 4742351 = 7113527) B7113527
theorem B3161567 : Blo 2107435 3161567 := bstep (se 1 (by rfl) ⟨2371175, by rfl⟩ : syracuseStep 3161567 = 4742351) B4742351
theorem B2107711 : Blo 2107435 2107711 := bstep (se 1 (by rfl) ⟨1580783, by rfl⟩ : syracuseStep 2107711 = 3161567) B3161567
theorem B3161573 : Blo 2107435 3161573 := bbase (se 4 (by rfl) ⟨296397, by rfl⟩ : syracuseStep 3161573 = 592795) (by norm_num)
theorem B2107715 : Blo 2107435 2107715 := bstep (se 1 (by rfl) ⟨1580786, by rfl⟩ : syracuseStep 2107715 = 3161573) B3161573
theorem B3798181 : Blo 2107435 3798181 := bbase (se 4 (by rfl) ⟨356079, by rfl⟩ : syracuseStep 3798181 = 712159) (by norm_num)
theorem B20256965 : Blo 2107435 20256965 := bstep (se 4 (by rfl) ⟨1899090, by rfl⟩ : syracuseStep 20256965 = 3798181) B3798181
theorem B13504643 : Blo 2107435 13504643 := bstep (se 1 (by rfl) ⟨10128482, by rfl⟩ : syracuseStep 13504643 = 20256965) B20256965
theorem B9003095 : Blo 2107435 9003095 := bstep (se 1 (by rfl) ⟨6752321, by rfl⟩ : syracuseStep 9003095 = 13504643) B13504643
theorem B6002063 : Blo 2107435 6002063 := bstep (se 1 (by rfl) ⟨4501547, by rfl⟩ : syracuseStep 6002063 = 9003095) B9003095
theorem B4001375 : Blo 2107435 4001375 := bstep (se 1 (by rfl) ⟨3001031, by rfl⟩ : syracuseStep 4001375 = 6002063) B6002063
theorem B2667583 : Blo 2107435 2667583 := bstep (se 1 (by rfl) ⟨2000687, by rfl⟩ : syracuseStep 2667583 = 4001375) B4001375
theorem B3556777 : Blo 2107435 3556777 := bstep (se 2 (by rfl) ⟨1333791, by rfl⟩ : syracuseStep 3556777 = 2667583) B2667583
theorem B4742369 : Blo 2107435 4742369 := bstep (se 2 (by rfl) ⟨1778388, by rfl⟩ : syracuseStep 4742369 = 3556777) B3556777
theorem B3161579 : Blo 2107435 3161579 := bstep (se 1 (by rfl) ⟨2371184, by rfl⟩ : syracuseStep 3161579 = 4742369) B4742369
theorem B2107719 : Blo 2107435 2107719 := bstep (se 1 (by rfl) ⟨1580789, by rfl⟩ : syracuseStep 2107719 = 3161579) B3161579
theorem B2371189 : Blo 2107435 2371189 := bbase (se 5 (by rfl) ⟨111149, by rfl⟩ : syracuseStep 2371189 = 222299) (by norm_num)
theorem B3161585 : Blo 2107435 3161585 := bstep (se 2 (by rfl) ⟨1185594, by rfl⟩ : syracuseStep 3161585 = 2371189) B2371189
theorem B2107723 : Blo 2107435 2107723 := bstep (se 1 (by rfl) ⟨1580792, by rfl⟩ : syracuseStep 2107723 = 3161585) B3161585
theorem B2667593 : Blo 2107435 2667593 := bbase (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) (by norm_num)
theorem B7113581 : Blo 2107435 7113581 := bstep (se 3 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 7113581 = 2667593) B2667593
theorem B4742387 : Blo 2107435 4742387 := bstep (se 1 (by rfl) ⟨3556790, by rfl⟩ : syracuseStep 4742387 = 7113581) B7113581
theorem B3161591 : Blo 2107435 3161591 := bstep (se 1 (by rfl) ⟨2371193, by rfl⟩ : syracuseStep 3161591 = 4742387) B4742387
theorem B2107727 : Blo 2107435 2107727 := bstep (se 1 (by rfl) ⟨1580795, by rfl⟩ : syracuseStep 2107727 = 3161591) B3161591
theorem B3161597 : Blo 2107435 3161597 := bbase (se 3 (by rfl) ⟨592799, by rfl⟩ : syracuseStep 3161597 = 1185599) (by norm_num)
theorem B2107731 : Blo 2107435 2107731 := bstep (se 1 (by rfl) ⟨1580798, by rfl⟩ : syracuseStep 2107731 = 3161597) B3161597
theorem B4742405 : Blo 2107435 4742405 := bbase (se 4 (by rfl) ⟨444600, by rfl⟩ : syracuseStep 4742405 = 889201) (by norm_num)
theorem B3161603 : Blo 2107435 3161603 := bstep (se 1 (by rfl) ⟨2371202, by rfl⟩ : syracuseStep 3161603 = 4742405) B4742405
theorem B2107735 : Blo 2107435 2107735 := bstep (se 1 (by rfl) ⟨1580801, by rfl⟩ : syracuseStep 2107735 = 3161603) B3161603
theorem B4001413 : Blo 2107435 4001413 := bbase (se 4 (by rfl) ⟨375132, by rfl⟩ : syracuseStep 4001413 = 750265) (by norm_num)
theorem B5335217 : Blo 2107435 5335217 := bstep (se 2 (by rfl) ⟨2000706, by rfl⟩ : syracuseStep 5335217 = 4001413) B4001413
theorem B3556811 : Blo 2107435 3556811 := bstep (se 1 (by rfl) ⟨2667608, by rfl⟩ : syracuseStep 3556811 = 5335217) B5335217
theorem B2371207 : Blo 2107435 2371207 := bstep (se 1 (by rfl) ⟨1778405, by rfl⟩ : syracuseStep 2371207 = 3556811) B3556811
theorem B3161609 : Blo 2107435 3161609 := bstep (se 2 (by rfl) ⟨1185603, by rfl⟩ : syracuseStep 3161609 = 2371207) B2371207
theorem B2107739 : Blo 2107435 2107739 := bstep (se 1 (by rfl) ⟨1580804, by rfl⟩ : syracuseStep 2107739 = 3161609) B3161609
theorem B10670453 : Blo 2107435 10670453 := bbase (se 5 (by rfl) ⟨500177, by rfl⟩ : syracuseStep 10670453 = 1000355) (by norm_num)
theorem B7113635 : Blo 2107435 7113635 := bstep (se 1 (by rfl) ⟨5335226, by rfl⟩ : syracuseStep 7113635 = 10670453) B10670453
theorem B4742423 : Blo 2107435 4742423 := bstep (se 1 (by rfl) ⟨3556817, by rfl⟩ : syracuseStep 4742423 = 7113635) B7113635
theorem B3161615 : Blo 2107435 3161615 := bstep (se 1 (by rfl) ⟨2371211, by rfl⟩ : syracuseStep 3161615 = 4742423) B4742423
theorem B2107743 : Blo 2107435 2107743 := bstep (se 1 (by rfl) ⟨1580807, by rfl⟩ : syracuseStep 2107743 = 3161615) B3161615
theorem B3161621 : Blo 2107435 3161621 := bbase (se 6 (by rfl) ⟨74100, by rfl⟩ : syracuseStep 3161621 = 148201) (by norm_num)
theorem B2107747 : Blo 2107435 2107747 := bstep (se 1 (by rfl) ⟨1580810, by rfl⟩ : syracuseStep 2107747 = 3161621) B3161621
theorem B4331317 : Blo 2107435 4331317 := bbase (se 5 (by rfl) ⟨203030, by rfl⟩ : syracuseStep 4331317 = 406061) (by norm_num)
theorem B5775089 : Blo 2107435 5775089 := bstep (se 2 (by rfl) ⟨2165658, by rfl⟩ : syracuseStep 5775089 = 4331317) B4331317
theorem B61600949 : Blo 2107435 61600949 := bstep (se 5 (by rfl) ⟨2887544, by rfl⟩ : syracuseStep 61600949 = 5775089) B5775089
theorem B41067299 : Blo 2107435 41067299 := bstep (se 1 (by rfl) ⟨30800474, by rfl⟩ : syracuseStep 41067299 = 61600949) B61600949
theorem B27378199 : Blo 2107435 27378199 := bstep (se 1 (by rfl) ⟨20533649, by rfl⟩ : syracuseStep 27378199 = 41067299) B41067299
theorem B36504265 : Blo 2107435 36504265 := bstep (se 2 (by rfl) ⟨13689099, by rfl⟩ : syracuseStep 36504265 = 27378199) B27378199
theorem B48672353 : Blo 2107435 48672353 := bstep (se 2 (by rfl) ⟨18252132, by rfl⟩ : syracuseStep 48672353 = 36504265) B36504265
theorem B32448235 : Blo 2107435 32448235 := bstep (se 1 (by rfl) ⟨24336176, by rfl⟩ : syracuseStep 32448235 = 48672353) B48672353
theorem B43264313 : Blo 2107435 43264313 := bstep (se 2 (by rfl) ⟨16224117, by rfl⟩ : syracuseStep 43264313 = 32448235) B32448235
theorem B28842875 : Blo 2107435 28842875 := bstep (se 1 (by rfl) ⟨21632156, by rfl⟩ : syracuseStep 28842875 = 43264313) B43264313
theorem B19228583 : Blo 2107435 19228583 := bstep (se 1 (by rfl) ⟨14421437, by rfl⟩ : syracuseStep 19228583 = 28842875) B28842875
theorem B12819055 : Blo 2107435 12819055 := bstep (se 1 (by rfl) ⟨9614291, by rfl⟩ : syracuseStep 12819055 = 19228583) B19228583
theorem B17092073 : Blo 2107435 17092073 := bstep (se 2 (by rfl) ⟨6409527, by rfl⟩ : syracuseStep 17092073 = 12819055) B12819055
theorem B11394715 : Blo 2107435 11394715 := bstep (se 1 (by rfl) ⟨8546036, by rfl⟩ : syracuseStep 11394715 = 17092073) B17092073
theorem B15192953 : Blo 2107435 15192953 := bstep (se 2 (by rfl) ⟨5697357, by rfl⟩ : syracuseStep 15192953 = 11394715) B11394715
theorem B10128635 : Blo 2107435 10128635 := bstep (se 1 (by rfl) ⟨7596476, by rfl⟩ : syracuseStep 10128635 = 15192953) B15192953
theorem B6752423 : Blo 2107435 6752423 := bstep (se 1 (by rfl) ⟨5064317, by rfl⟩ : syracuseStep 6752423 = 10128635) B10128635
theorem B18006461 : Blo 2107435 18006461 := bstep (se 3 (by rfl) ⟨3376211, by rfl⟩ : syracuseStep 18006461 = 6752423) B6752423
theorem B12004307 : Blo 2107435 12004307 := bstep (se 1 (by rfl) ⟨9003230, by rfl⟩ : syracuseStep 12004307 = 18006461) B18006461
theorem B8002871 : Blo 2107435 8002871 := bstep (se 1 (by rfl) ⟨6002153, by rfl⟩ : syracuseStep 8002871 = 12004307) B12004307
theorem B5335247 : Blo 2107435 5335247 := bstep (se 1 (by rfl) ⟨4001435, by rfl⟩ : syracuseStep 5335247 = 8002871) B8002871
theorem B3556831 : Blo 2107435 3556831 := bstep (se 1 (by rfl) ⟨2667623, by rfl⟩ : syracuseStep 3556831 = 5335247) B5335247
theorem B4742441 : Blo 2107435 4742441 := bstep (se 2 (by rfl) ⟨1778415, by rfl⟩ : syracuseStep 4742441 = 3556831) B3556831
theorem B3161627 : Blo 2107435 3161627 := bstep (se 1 (by rfl) ⟨2371220, by rfl⟩ : syracuseStep 3161627 = 4742441) B4742441
theorem B2107751 : Blo 2107435 2107751 := bstep (se 1 (by rfl) ⟨1580813, by rfl⟩ : syracuseStep 2107751 = 3161627) B3161627
theorem B2371225 : Blo 2107435 2371225 := bbase (se 2 (by rfl) ⟨889209, by rfl⟩ : syracuseStep 2371225 = 1778419) (by norm_num)
theorem B3161633 : Blo 2107435 3161633 := bstep (se 2 (by rfl) ⟨1185612, by rfl⟩ : syracuseStep 3161633 = 2371225) B2371225
theorem B2107755 : Blo 2107435 2107755 := bstep (se 1 (by rfl) ⟨1580816, by rfl⟩ : syracuseStep 2107755 = 3161633) B3161633
theorem B8002901 : Blo 2107435 8002901 := bbase (se 11 (by rfl) ⟨5861, by rfl⟩ : syracuseStep 8002901 = 11723) (by norm_num)
theorem B5335267 : Blo 2107435 5335267 := bstep (se 1 (by rfl) ⟨4001450, by rfl⟩ : syracuseStep 5335267 = 8002901) B8002901
theorem B7113689 : Blo 2107435 7113689 := bstep (se 2 (by rfl) ⟨2667633, by rfl⟩ : syracuseStep 7113689 = 5335267) B5335267
theorem B4742459 : Blo 2107435 4742459 := bstep (se 1 (by rfl) ⟨3556844, by rfl⟩ : syracuseStep 4742459 = 7113689) B7113689
theorem B3161639 : Blo 2107435 3161639 := bstep (se 1 (by rfl) ⟨2371229, by rfl⟩ : syracuseStep 3161639 = 4742459) B4742459
theorem B2107759 : Blo 2107435 2107759 := bstep (se 1 (by rfl) ⟨1580819, by rfl⟩ : syracuseStep 2107759 = 3161639) B3161639
theorem B3161645 : Blo 2107435 3161645 := bbase (se 3 (by rfl) ⟨592808, by rfl⟩ : syracuseStep 3161645 = 1185617) (by norm_num)
theorem B2107763 : Blo 2107435 2107763 := bstep (se 1 (by rfl) ⟨1580822, by rfl⟩ : syracuseStep 2107763 = 3161645) B3161645
theorem B4742477 : Blo 2107435 4742477 := bbase (se 3 (by rfl) ⟨889214, by rfl⟩ : syracuseStep 4742477 = 1778429) (by norm_num)
theorem B3161651 : Blo 2107435 3161651 := bstep (se 1 (by rfl) ⟨2371238, by rfl⟩ : syracuseStep 3161651 = 4742477) B4742477
theorem B2107767 : Blo 2107435 2107767 := bstep (se 1 (by rfl) ⟨1580825, by rfl⟩ : syracuseStep 2107767 = 3161651) B3161651
theorem B2667649 : Blo 2107435 2667649 := bbase (se 2 (by rfl) ⟨1000368, by rfl⟩ : syracuseStep 2667649 = 2000737) (by norm_num)
theorem B3556865 : Blo 2107435 3556865 := bstep (se 2 (by rfl) ⟨1333824, by rfl⟩ : syracuseStep 3556865 = 2667649) B2667649
theorem B2371243 : Blo 2107435 2371243 := bstep (se 1 (by rfl) ⟨1778432, by rfl⟩ : syracuseStep 2371243 = 3556865) B3556865
theorem B3161657 : Blo 2107435 3161657 := bstep (se 2 (by rfl) ⟨1185621, by rfl⟩ : syracuseStep 3161657 = 2371243) B2371243
theorem B2107771 : Blo 2107435 2107771 := bstep (se 1 (by rfl) ⟨1580828, by rfl⟩ : syracuseStep 2107771 = 3161657) B3161657
theorem B2250833 : Blo 2107435 2250833 := bbase (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) (by norm_num)
theorem B24008885 : Blo 2107435 24008885 := bstep (se 5 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 24008885 = 2250833) B2250833
theorem B16005923 : Blo 2107435 16005923 := bstep (se 1 (by rfl) ⟨12004442, by rfl⟩ : syracuseStep 16005923 = 24008885) B24008885
theorem B10670615 : Blo 2107435 10670615 := bstep (se 1 (by rfl) ⟨8002961, by rfl⟩ : syracuseStep 10670615 = 16005923) B16005923
theorem B7113743 : Blo 2107435 7113743 := bstep (se 1 (by rfl) ⟨5335307, by rfl⟩ : syracuseStep 7113743 = 10670615) B10670615
theorem B4742495 : Blo 2107435 4742495 := bstep (se 1 (by rfl) ⟨3556871, by rfl⟩ : syracuseStep 4742495 = 7113743) B7113743
theorem B3161663 : Blo 2107435 3161663 := bstep (se 1 (by rfl) ⟨2371247, by rfl⟩ : syracuseStep 3161663 = 4742495) B4742495
theorem B2107775 : Blo 2107435 2107775 := bstep (se 1 (by rfl) ⟨1580831, by rfl⟩ : syracuseStep 2107775 = 3161663) B3161663
theorem B3161669 : Blo 2107435 3161669 := bbase (se 4 (by rfl) ⟨296406, by rfl⟩ : syracuseStep 3161669 = 592813) (by norm_num)
theorem B2107779 : Blo 2107435 2107779 := bstep (se 1 (by rfl) ⟨1580834, by rfl⟩ : syracuseStep 2107779 = 3161669) B3161669
theorem B3556885 : Blo 2107435 3556885 := bbase (se 6 (by rfl) ⟨83364, by rfl⟩ : syracuseStep 3556885 = 166729) (by norm_num)
theorem B4742513 : Blo 2107435 4742513 := bstep (se 2 (by rfl) ⟨1778442, by rfl⟩ : syracuseStep 4742513 = 3556885) B3556885
theorem B3161675 : Blo 2107435 3161675 := bstep (se 1 (by rfl) ⟨2371256, by rfl⟩ : syracuseStep 3161675 = 4742513) B4742513
theorem B2107783 : Blo 2107435 2107783 := bstep (se 1 (by rfl) ⟨1580837, by rfl⟩ : syracuseStep 2107783 = 3161675) B3161675
theorem B2371261 : Blo 2107435 2371261 := bbase (se 3 (by rfl) ⟨444611, by rfl⟩ : syracuseStep 2371261 = 889223) (by norm_num)
theorem B3161681 : Blo 2107435 3161681 := bstep (se 2 (by rfl) ⟨1185630, by rfl⟩ : syracuseStep 3161681 = 2371261) B2371261
theorem B2107787 : Blo 2107435 2107787 := bstep (se 1 (by rfl) ⟨1580840, by rfl⟩ : syracuseStep 2107787 = 3161681) B3161681
theorem B7113797 : Blo 2107435 7113797 := bbase (se 4 (by rfl) ⟨666918, by rfl⟩ : syracuseStep 7113797 = 1333837) (by norm_num)
theorem B4742531 : Blo 2107435 4742531 := bstep (se 1 (by rfl) ⟨3556898, by rfl⟩ : syracuseStep 4742531 = 7113797) B7113797
theorem B3161687 : Blo 2107435 3161687 := bstep (se 1 (by rfl) ⟨2371265, by rfl⟩ : syracuseStep 3161687 = 4742531) B4742531
theorem B2107791 : Blo 2107435 2107791 := bstep (se 1 (by rfl) ⟨1580843, by rfl⟩ : syracuseStep 2107791 = 3161687) B3161687
theorem B3161693 : Blo 2107435 3161693 := bbase (se 3 (by rfl) ⟨592817, by rfl⟩ : syracuseStep 3161693 = 1185635) (by norm_num)
theorem B2107795 : Blo 2107435 2107795 := bstep (se 1 (by rfl) ⟨1580846, by rfl⟩ : syracuseStep 2107795 = 3161693) B3161693
theorem B4742549 : Blo 2107435 4742549 := bbase (se 6 (by rfl) ⟨111153, by rfl⟩ : syracuseStep 4742549 = 222307) (by norm_num)
theorem B3161699 : Blo 2107435 3161699 := bstep (se 1 (by rfl) ⟨2371274, by rfl⟩ : syracuseStep 3161699 = 4742549) B4742549
theorem B2107799 : Blo 2107435 2107799 := bstep (se 1 (by rfl) ⟨1580849, by rfl⟩ : syracuseStep 2107799 = 3161699) B3161699
theorem B6084197 : Blo 2107435 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B4056131 : Blo 2107435 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B2704087 : Blo 2107435 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B14421797 : Blo 2107435 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B9614531 : Blo 2107435 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B6409687 : Blo 2107435 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B8546249 : Blo 2107435 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B22789997 : Blo 2107435 22789997 := bstep (se 3 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 22789997 = 8546249) B8546249
theorem B15193331 : Blo 2107435 15193331 := bstep (se 1 (by rfl) ⟨11394998, by rfl⟩ : syracuseStep 15193331 = 22789997) B22789997
theorem B10128887 : Blo 2107435 10128887 := bstep (se 1 (by rfl) ⟨7596665, by rfl⟩ : syracuseStep 10128887 = 15193331) B15193331
theorem B6752591 : Blo 2107435 6752591 := bstep (se 1 (by rfl) ⟨5064443, by rfl⟩ : syracuseStep 6752591 = 10128887) B10128887
theorem B4501727 : Blo 2107435 4501727 := bstep (se 1 (by rfl) ⟨3376295, by rfl⟩ : syracuseStep 4501727 = 6752591) B6752591
theorem B3001151 : Blo 2107435 3001151 := bstep (se 1 (by rfl) ⟨2250863, by rfl⟩ : syracuseStep 3001151 = 4501727) B4501727
theorem B8003069 : Blo 2107435 8003069 := bstep (se 3 (by rfl) ⟨1500575, by rfl⟩ : syracuseStep 8003069 = 3001151) B3001151
theorem B5335379 : Blo 2107435 5335379 := bstep (se 1 (by rfl) ⟨4001534, by rfl⟩ : syracuseStep 5335379 = 8003069) B8003069
theorem B3556919 : Blo 2107435 3556919 := bstep (se 1 (by rfl) ⟨2667689, by rfl⟩ : syracuseStep 3556919 = 5335379) B5335379
theorem B2371279 : Blo 2107435 2371279 := bstep (se 1 (by rfl) ⟨1778459, by rfl⟩ : syracuseStep 2371279 = 3556919) B3556919
theorem B3161705 : Blo 2107435 3161705 := bstep (se 2 (by rfl) ⟨1185639, by rfl⟩ : syracuseStep 3161705 = 2371279) B2371279
theorem B2107803 : Blo 2107435 2107803 := bstep (se 1 (by rfl) ⟨1580852, by rfl⟩ : syracuseStep 2107803 = 3161705) B3161705
theorem B3376301 : Blo 2107435 3376301 := bbase (se 3 (by rfl) ⟨633056, by rfl⟩ : syracuseStep 3376301 = 1266113) (by norm_num)
theorem B9003469 : Blo 2107435 9003469 := bstep (se 3 (by rfl) ⟨1688150, by rfl⟩ : syracuseStep 9003469 = 3376301) B3376301
theorem B12004625 : Blo 2107435 12004625 := bstep (se 2 (by rfl) ⟨4501734, by rfl⟩ : syracuseStep 12004625 = 9003469) B9003469
theorem B8003083 : Blo 2107435 8003083 := bstep (se 1 (by rfl) ⟨6002312, by rfl⟩ : syracuseStep 8003083 = 12004625) B12004625
theorem B10670777 : Blo 2107435 10670777 := bstep (se 2 (by rfl) ⟨4001541, by rfl⟩ : syracuseStep 10670777 = 8003083) B8003083
theorem B7113851 : Blo 2107435 7113851 := bstep (se 1 (by rfl) ⟨5335388, by rfl⟩ : syracuseStep 7113851 = 10670777) B10670777
theorem B4742567 : Blo 2107435 4742567 := bstep (se 1 (by rfl) ⟨3556925, by rfl⟩ : syracuseStep 4742567 = 7113851) B7113851
theorem B3161711 : Blo 2107435 3161711 := bstep (se 1 (by rfl) ⟨2371283, by rfl⟩ : syracuseStep 3161711 = 4742567) B4742567
theorem B2107807 : Blo 2107435 2107807 := bstep (se 1 (by rfl) ⟨1580855, by rfl⟩ : syracuseStep 2107807 = 3161711) B3161711
theorem B3161717 : Blo 2107435 3161717 := bbase (se 5 (by rfl) ⟨148205, by rfl⟩ : syracuseStep 3161717 = 296411) (by norm_num)
theorem B2107811 : Blo 2107435 2107811 := bstep (se 1 (by rfl) ⟨1580858, by rfl⟩ : syracuseStep 2107811 = 3161717) B3161717
theorem B4001557 : Blo 2107435 4001557 := bbase (se 6 (by rfl) ⟨93786, by rfl⟩ : syracuseStep 4001557 = 187573) (by norm_num)
theorem B5335409 : Blo 2107435 5335409 := bstep (se 2 (by rfl) ⟨2000778, by rfl⟩ : syracuseStep 5335409 = 4001557) B4001557
theorem B3556939 : Blo 2107435 3556939 := bstep (se 1 (by rfl) ⟨2667704, by rfl⟩ : syracuseStep 3556939 = 5335409) B5335409
theorem B4742585 : Blo 2107435 4742585 := bstep (se 2 (by rfl) ⟨1778469, by rfl⟩ : syracuseStep 4742585 = 3556939) B3556939
theorem B3161723 : Blo 2107435 3161723 := bstep (se 1 (by rfl) ⟨2371292, by rfl⟩ : syracuseStep 3161723 = 4742585) B4742585
theorem B2107815 : Blo 2107435 2107815 := bstep (se 1 (by rfl) ⟨1580861, by rfl⟩ : syracuseStep 2107815 = 3161723) B3161723
theorem B2371297 : Blo 2107435 2371297 := bbase (se 2 (by rfl) ⟨889236, by rfl⟩ : syracuseStep 2371297 = 1778473) (by norm_num)
theorem B3161729 : Blo 2107435 3161729 := bstep (se 2 (by rfl) ⟨1185648, by rfl⟩ : syracuseStep 3161729 = 2371297) B2371297
theorem B2107819 : Blo 2107435 2107819 := bstep (se 1 (by rfl) ⟨1580864, by rfl⟩ : syracuseStep 2107819 = 3161729) B3161729
theorem B5335429 : Blo 2107435 5335429 := bbase (se 4 (by rfl) ⟨500196, by rfl⟩ : syracuseStep 5335429 = 1000393) (by norm_num)
theorem B7113905 : Blo 2107435 7113905 := bstep (se 2 (by rfl) ⟨2667714, by rfl⟩ : syracuseStep 7113905 = 5335429) B5335429
theorem B4742603 : Blo 2107435 4742603 := bstep (se 1 (by rfl) ⟨3556952, by rfl⟩ : syracuseStep 4742603 = 7113905) B7113905
theorem B3161735 : Blo 2107435 3161735 := bstep (se 1 (by rfl) ⟨2371301, by rfl⟩ : syracuseStep 3161735 = 4742603) B4742603
theorem B2107823 : Blo 2107435 2107823 := bstep (se 1 (by rfl) ⟨1580867, by rfl⟩ : syracuseStep 2107823 = 3161735) B3161735
theorem B3161741 : Blo 2107435 3161741 := bbase (se 3 (by rfl) ⟨592826, by rfl⟩ : syracuseStep 3161741 = 1185653) (by norm_num)
theorem B2107827 : Blo 2107435 2107827 := bstep (se 1 (by rfl) ⟨1580870, by rfl⟩ : syracuseStep 2107827 = 3161741) B3161741
theorem B4742621 : Blo 2107435 4742621 := bbase (se 3 (by rfl) ⟨889241, by rfl⟩ : syracuseStep 4742621 = 1778483) (by norm_num)
theorem B3161747 : Blo 2107435 3161747 := bstep (se 1 (by rfl) ⟨2371310, by rfl⟩ : syracuseStep 3161747 = 4742621) B4742621
theorem B2107831 : Blo 2107435 2107831 := bstep (se 1 (by rfl) ⟨1580873, by rfl⟩ : syracuseStep 2107831 = 3161747) B3161747
theorem B3556973 : Blo 2107435 3556973 := bbase (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) (by norm_num)
theorem B2371315 : Blo 2107435 2371315 := bstep (se 1 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 2371315 = 3556973) B3556973
theorem B3161753 : Blo 2107435 3161753 := bstep (se 2 (by rfl) ⟨1185657, by rfl⟩ : syracuseStep 3161753 = 2371315) B2371315
theorem B2107835 : Blo 2107435 2107835 := bstep (se 1 (by rfl) ⟨1580876, by rfl⟩ : syracuseStep 2107835 = 3161753) B3161753
theorem B11395189 : Blo 2107435 11395189 := bbase (se 5 (by rfl) ⟨534149, by rfl⟩ : syracuseStep 11395189 = 1068299) (by norm_num)
theorem B15193585 : Blo 2107435 15193585 := bstep (se 2 (by rfl) ⟨5697594, by rfl⟩ : syracuseStep 15193585 = 11395189) B11395189
theorem B20258113 : Blo 2107435 20258113 := bstep (se 2 (by rfl) ⟨7596792, by rfl⟩ : syracuseStep 20258113 = 15193585) B15193585
theorem B27010817 : Blo 2107435 27010817 := bstep (se 2 (by rfl) ⟨10129056, by rfl⟩ : syracuseStep 27010817 = 20258113) B20258113
theorem B18007211 : Blo 2107435 18007211 := bstep (se 1 (by rfl) ⟨13505408, by rfl⟩ : syracuseStep 18007211 = 27010817) B27010817
theorem B12004807 : Blo 2107435 12004807 := bstep (se 1 (by rfl) ⟨9003605, by rfl⟩ : syracuseStep 12004807 = 18007211) B18007211
theorem B16006409 : Blo 2107435 16006409 := bstep (se 2 (by rfl) ⟨6002403, by rfl⟩ : syracuseStep 16006409 = 12004807) B12004807
theorem B10670939 : Blo 2107435 10670939 := bstep (se 1 (by rfl) ⟨8003204, by rfl⟩ : syracuseStep 10670939 = 16006409) B16006409
theorem B7113959 : Blo 2107435 7113959 := bstep (se 1 (by rfl) ⟨5335469, by rfl⟩ : syracuseStep 7113959 = 10670939) B10670939
theorem B4742639 : Blo 2107435 4742639 := bstep (se 1 (by rfl) ⟨3556979, by rfl⟩ : syracuseStep 4742639 = 7113959) B7113959
theorem B3161759 : Blo 2107435 3161759 := bstep (se 1 (by rfl) ⟨2371319, by rfl⟩ : syracuseStep 3161759 = 4742639) B4742639
theorem B2107839 : Blo 2107435 2107839 := bstep (se 1 (by rfl) ⟨1580879, by rfl⟩ : syracuseStep 2107839 = 3161759) B3161759
theorem B3161765 : Blo 2107435 3161765 := bbase (se 4 (by rfl) ⟨296415, by rfl⟩ : syracuseStep 3161765 = 592831) (by norm_num)
theorem B2107843 : Blo 2107435 2107843 := bstep (se 1 (by rfl) ⟨1580882, by rfl⟩ : syracuseStep 2107843 = 3161765) B3161765
theorem B2667745 : Blo 2107435 2667745 := bbase (se 2 (by rfl) ⟨1000404, by rfl⟩ : syracuseStep 2667745 = 2000809) (by norm_num)
theorem B3556993 : Blo 2107435 3556993 := bstep (se 2 (by rfl) ⟨1333872, by rfl⟩ : syracuseStep 3556993 = 2667745) B2667745
theorem B4742657 : Blo 2107435 4742657 := bstep (se 2 (by rfl) ⟨1778496, by rfl⟩ : syracuseStep 4742657 = 3556993) B3556993
theorem B3161771 : Blo 2107435 3161771 := bstep (se 1 (by rfl) ⟨2371328, by rfl⟩ : syracuseStep 3161771 = 4742657) B4742657
theorem B2107847 : Blo 2107435 2107847 := bstep (se 1 (by rfl) ⟨1580885, by rfl⟩ : syracuseStep 2107847 = 3161771) B3161771
theorem B2371333 : Blo 2107435 2371333 := bbase (se 4 (by rfl) ⟨222312, by rfl⟩ : syracuseStep 2371333 = 444625) (by norm_num)
theorem B3161777 : Blo 2107435 3161777 := bstep (se 2 (by rfl) ⟨1185666, by rfl⟩ : syracuseStep 3161777 = 2371333) B2371333
theorem B2107851 : Blo 2107435 2107851 := bstep (se 1 (by rfl) ⟨1580888, by rfl⟩ : syracuseStep 2107851 = 3161777) B3161777
theorem B5408309 : Blo 2107435 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B14422157 : Blo 2107435 14422157 := bstep (se 3 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 14422157 = 5408309) B5408309
theorem B9614771 : Blo 2107435 9614771 := bstep (se 1 (by rfl) ⟨7211078, by rfl⟩ : syracuseStep 9614771 = 14422157) B14422157
theorem B6409847 : Blo 2107435 6409847 := bstep (se 1 (by rfl) ⟨4807385, by rfl⟩ : syracuseStep 6409847 = 9614771) B9614771
theorem B4273231 : Blo 2107435 4273231 := bstep (se 1 (by rfl) ⟨3204923, by rfl⟩ : syracuseStep 4273231 = 6409847) B6409847
theorem B5697641 : Blo 2107435 5697641 := bstep (se 2 (by rfl) ⟨2136615, by rfl⟩ : syracuseStep 5697641 = 4273231) B4273231
theorem B3798427 : Blo 2107435 3798427 := bstep (se 1 (by rfl) ⟨2848820, by rfl⟩ : syracuseStep 3798427 = 5697641) B5697641
theorem B5064569 : Blo 2107435 5064569 := bstep (se 2 (by rfl) ⟨1899213, by rfl⟩ : syracuseStep 5064569 = 3798427) B3798427
theorem B3376379 : Blo 2107435 3376379 := bstep (se 1 (by rfl) ⟨2532284, by rfl⟩ : syracuseStep 3376379 = 5064569) B5064569
theorem B2250919 : Blo 2107435 2250919 := bstep (se 1 (by rfl) ⟨1688189, by rfl⟩ : syracuseStep 2250919 = 3376379) B3376379
theorem B3001225 : Blo 2107435 3001225 := bstep (se 2 (by rfl) ⟨1125459, by rfl⟩ : syracuseStep 3001225 = 2250919) B2250919
theorem B4001633 : Blo 2107435 4001633 := bstep (se 2 (by rfl) ⟨1500612, by rfl⟩ : syracuseStep 4001633 = 3001225) B3001225
theorem B2667755 : Blo 2107435 2667755 := bstep (se 1 (by rfl) ⟨2000816, by rfl⟩ : syracuseStep 2667755 = 4001633) B4001633
theorem B7114013 : Blo 2107435 7114013 := bstep (se 3 (by rfl) ⟨1333877, by rfl⟩ : syracuseStep 7114013 = 2667755) B2667755
theorem B4742675 : Blo 2107435 4742675 := bstep (se 1 (by rfl) ⟨3557006, by rfl⟩ : syracuseStep 4742675 = 7114013) B7114013
theorem B3161783 : Blo 2107435 3161783 := bstep (se 1 (by rfl) ⟨2371337, by rfl⟩ : syracuseStep 3161783 = 4742675) B4742675
theorem B2107855 : Blo 2107435 2107855 := bstep (se 1 (by rfl) ⟨1580891, by rfl⟩ : syracuseStep 2107855 = 3161783) B3161783
theorem B3161789 : Blo 2107435 3161789 := bbase (se 3 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 3161789 = 1185671) (by norm_num)
theorem B2107859 : Blo 2107435 2107859 := bstep (se 1 (by rfl) ⟨1580894, by rfl⟩ : syracuseStep 2107859 = 3161789) B3161789
theorem B4742693 : Blo 2107435 4742693 := bbase (se 4 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 4742693 = 889255) (by norm_num)
theorem B3161795 : Blo 2107435 3161795 := bstep (se 1 (by rfl) ⟨2371346, by rfl⟩ : syracuseStep 3161795 = 4742693) B4742693
theorem B2107863 : Blo 2107435 2107863 := bstep (se 1 (by rfl) ⟨1580897, by rfl⟩ : syracuseStep 2107863 = 3161795) B3161795
theorem B5335541 : Blo 2107435 5335541 := bbase (se 5 (by rfl) ⟨250103, by rfl⟩ : syracuseStep 5335541 = 500207) (by norm_num)
theorem B3557027 : Blo 2107435 3557027 := bstep (se 1 (by rfl) ⟨2667770, by rfl⟩ : syracuseStep 3557027 = 5335541) B5335541
theorem B2371351 : Blo 2107435 2371351 := bstep (se 1 (by rfl) ⟨1778513, by rfl⟩ : syracuseStep 2371351 = 3557027) B3557027
theorem B3161801 : Blo 2107435 3161801 := bstep (se 2 (by rfl) ⟨1185675, by rfl⟩ : syracuseStep 3161801 = 2371351) B2371351
theorem B2107867 : Blo 2107435 2107867 := bstep (se 1 (by rfl) ⟨1580900, by rfl⟩ : syracuseStep 2107867 = 3161801) B3161801
theorem B17093045 : Blo 2107435 17093045 := bbase (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) (by norm_num)
theorem B45581453 : Blo 2107435 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B30387635 : Blo 2107435 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B20258423 : Blo 2107435 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B13505615 : Blo 2107435 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B9003743 : Blo 2107435 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B6002495 : Blo 2107435 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B4001663 : Blo 2107435 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B10671101 : Blo 2107435 10671101 := bstep (se 3 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 10671101 = 4001663) B4001663
theorem B7114067 : Blo 2107435 7114067 := bstep (se 1 (by rfl) ⟨5335550, by rfl⟩ : syracuseStep 7114067 = 10671101) B10671101
theorem B4742711 : Blo 2107435 4742711 := bstep (se 1 (by rfl) ⟨3557033, by rfl⟩ : syracuseStep 4742711 = 7114067) B7114067
theorem B3161807 : Blo 2107435 3161807 := bstep (se 1 (by rfl) ⟨2371355, by rfl⟩ : syracuseStep 3161807 = 4742711) B4742711
theorem B2107871 : Blo 2107435 2107871 := bstep (se 1 (by rfl) ⟨1580903, by rfl⟩ : syracuseStep 2107871 = 3161807) B3161807
theorem B3161813 : Blo 2107435 3161813 := bbase (se 7 (by rfl) ⟨37052, by rfl⟩ : syracuseStep 3161813 = 74105) (by norm_num)
theorem B2107875 : Blo 2107435 2107875 := bstep (se 1 (by rfl) ⟨1580906, by rfl⟩ : syracuseStep 2107875 = 3161813) B3161813
theorem B2532313 : Blo 2107435 2532313 := bbase (se 2 (by rfl) ⟨949617, by rfl⟩ : syracuseStep 2532313 = 1899235) (by norm_num)
theorem B3376417 : Blo 2107435 3376417 := bstep (se 2 (by rfl) ⟨1266156, by rfl⟩ : syracuseStep 3376417 = 2532313) B2532313
theorem B4501889 : Blo 2107435 4501889 := bstep (se 2 (by rfl) ⟨1688208, by rfl⟩ : syracuseStep 4501889 = 3376417) B3376417
theorem B3001259 : Blo 2107435 3001259 := bstep (se 1 (by rfl) ⟨2250944, by rfl⟩ : syracuseStep 3001259 = 4501889) B4501889
theorem B8003357 : Blo 2107435 8003357 := bstep (se 3 (by rfl) ⟨1500629, by rfl⟩ : syracuseStep 8003357 = 3001259) B3001259
theorem B5335571 : Blo 2107435 5335571 := bstep (se 1 (by rfl) ⟨4001678, by rfl⟩ : syracuseStep 5335571 = 8003357) B8003357
theorem B3557047 : Blo 2107435 3557047 := bstep (se 1 (by rfl) ⟨2667785, by rfl⟩ : syracuseStep 3557047 = 5335571) B5335571
theorem B4742729 : Blo 2107435 4742729 := bstep (se 2 (by rfl) ⟨1778523, by rfl⟩ : syracuseStep 4742729 = 3557047) B3557047
theorem B3161819 : Blo 2107435 3161819 := bstep (se 1 (by rfl) ⟨2371364, by rfl⟩ : syracuseStep 3161819 = 4742729) B4742729
theorem B2107879 : Blo 2107435 2107879 := bstep (se 1 (by rfl) ⟨1580909, by rfl⟩ : syracuseStep 2107879 = 3161819) B3161819
theorem B2371369 : Blo 2107435 2371369 := bbase (se 2 (by rfl) ⟨889263, by rfl⟩ : syracuseStep 2371369 = 1778527) (by norm_num)
theorem B3161825 : Blo 2107435 3161825 := bstep (se 2 (by rfl) ⟨1185684, by rfl⟩ : syracuseStep 3161825 = 2371369) B2371369
theorem B2107883 : Blo 2107435 2107883 := bstep (se 1 (by rfl) ⟨1580912, by rfl⟩ : syracuseStep 2107883 = 3161825) B3161825
theorem B13505717 : Blo 2107435 13505717 := bbase (se 5 (by rfl) ⟨633080, by rfl⟩ : syracuseStep 13505717 = 1266161) (by norm_num)
theorem B9003811 : Blo 2107435 9003811 := bstep (se 1 (by rfl) ⟨6752858, by rfl⟩ : syracuseStep 9003811 = 13505717) B13505717
theorem B12005081 : Blo 2107435 12005081 := bstep (se 2 (by rfl) ⟨4501905, by rfl⟩ : syracuseStep 12005081 = 9003811) B9003811
theorem B8003387 : Blo 2107435 8003387 := bstep (se 1 (by rfl) ⟨6002540, by rfl⟩ : syracuseStep 8003387 = 12005081) B12005081
theorem B5335591 : Blo 2107435 5335591 := bstep (se 1 (by rfl) ⟨4001693, by rfl⟩ : syracuseStep 5335591 = 8003387) B8003387
theorem B7114121 : Blo 2107435 7114121 := bstep (se 2 (by rfl) ⟨2667795, by rfl⟩ : syracuseStep 7114121 = 5335591) B5335591
theorem B4742747 : Blo 2107435 4742747 := bstep (se 1 (by rfl) ⟨3557060, by rfl⟩ : syracuseStep 4742747 = 7114121) B7114121
theorem B3161831 : Blo 2107435 3161831 := bstep (se 1 (by rfl) ⟨2371373, by rfl⟩ : syracuseStep 3161831 = 4742747) B4742747
theorem B2107887 : Blo 2107435 2107887 := bstep (se 1 (by rfl) ⟨1580915, by rfl⟩ : syracuseStep 2107887 = 3161831) B3161831
theorem B3161837 : Blo 2107435 3161837 := bbase (se 3 (by rfl) ⟨592844, by rfl⟩ : syracuseStep 3161837 = 1185689) (by norm_num)
theorem B2107891 : Blo 2107435 2107891 := bstep (se 1 (by rfl) ⟨1580918, by rfl⟩ : syracuseStep 2107891 = 3161837) B3161837
theorem B4742765 : Blo 2107435 4742765 := bbase (se 3 (by rfl) ⟨889268, by rfl⟩ : syracuseStep 4742765 = 1778537) (by norm_num)
theorem B3161843 : Blo 2107435 3161843 := bstep (se 1 (by rfl) ⟨2371382, by rfl⟩ : syracuseStep 3161843 = 4742765) B4742765
theorem B2107895 : Blo 2107435 2107895 := bstep (se 1 (by rfl) ⟨1580921, by rfl⟩ : syracuseStep 2107895 = 3161843) B3161843
theorem B4001717 : Blo 2107435 4001717 := bbase (se 5 (by rfl) ⟨187580, by rfl⟩ : syracuseStep 4001717 = 375161) (by norm_num)
theorem B2667811 : Blo 2107435 2667811 := bstep (se 1 (by rfl) ⟨2000858, by rfl⟩ : syracuseStep 2667811 = 4001717) B4001717
theorem B3557081 : Blo 2107435 3557081 := bstep (se 2 (by rfl) ⟨1333905, by rfl⟩ : syracuseStep 3557081 = 2667811) B2667811
theorem B2371387 : Blo 2107435 2371387 := bstep (se 1 (by rfl) ⟨1778540, by rfl⟩ : syracuseStep 2371387 = 3557081) B3557081
theorem B3161849 : Blo 2107435 3161849 := bstep (se 2 (by rfl) ⟨1185693, by rfl⟩ : syracuseStep 3161849 = 2371387) B2371387
theorem B2107899 : Blo 2107435 2107899 := bstep (se 1 (by rfl) ⟨1580924, by rfl⟩ : syracuseStep 2107899 = 3161849) B3161849
theorem B4873085 : Blo 2107435 4873085 := bbase (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) (by norm_num)
theorem B3248723 : Blo 2107435 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B2165815 : Blo 2107435 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B2887753 : Blo 2107435 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B3850337 : Blo 2107435 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B2566891 : Blo 2107435 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B3422521 : Blo 2107435 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B4563361 : Blo 2107435 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B24337925 : Blo 2107435 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B16225283 : Blo 2107435 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B43267421 : Blo 2107435 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B28844947 : Blo 2107435 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B38459929 : Blo 2107435 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B51279905 : Blo 2107435 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B136746413 : Blo 2107435 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B91164275 : Blo 2107435 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B60776183 : Blo 2107435 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B40517455 : Blo 2107435 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B54023273 : Blo 2107435 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B36015515 : Blo 2107435 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B24010343 : Blo 2107435 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B16006895 : Blo 2107435 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B10671263 : Blo 2107435 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B7114175 : Blo 2107435 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B4742783 : Blo 2107435 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B3161855 : Blo 2107435 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B2107903 : Blo 2107435 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B3161861 : Blo 2107435 3161861 := bbase (se 4 (by rfl) ⟨296424, by rfl⟩ : syracuseStep 3161861 = 592849) (by norm_num)
theorem B2107907 : Blo 2107435 2107907 := bstep (se 1 (by rfl) ⟨1580930, by rfl⟩ : syracuseStep 2107907 = 3161861) B3161861
theorem B3557101 : Blo 2107435 3557101 := bbase (se 3 (by rfl) ⟨666956, by rfl⟩ : syracuseStep 3557101 = 1333913) (by norm_num)
theorem B4742801 : Blo 2107435 4742801 := bstep (se 2 (by rfl) ⟨1778550, by rfl⟩ : syracuseStep 4742801 = 3557101) B3557101
theorem B3161867 : Blo 2107435 3161867 := bstep (se 1 (by rfl) ⟨2371400, by rfl⟩ : syracuseStep 3161867 = 4742801) B4742801
theorem B2107911 : Blo 2107435 2107911 := bstep (se 1 (by rfl) ⟨1580933, by rfl⟩ : syracuseStep 2107911 = 3161867) B3161867
theorem B2371405 : Blo 2107435 2371405 := bbase (se 3 (by rfl) ⟨444638, by rfl⟩ : syracuseStep 2371405 = 889277) (by norm_num)
theorem B3161873 : Blo 2107435 3161873 := bstep (se 2 (by rfl) ⟨1185702, by rfl⟩ : syracuseStep 3161873 = 2371405) B2371405
theorem B2107915 : Blo 2107435 2107915 := bstep (se 1 (by rfl) ⟨1580936, by rfl⟩ : syracuseStep 2107915 = 3161873) B3161873
theorem B7114229 : Blo 2107435 7114229 := bbase (se 5 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 7114229 = 666959) (by norm_num)
theorem B4742819 : Blo 2107435 4742819 := bstep (se 1 (by rfl) ⟨3557114, by rfl⟩ : syracuseStep 4742819 = 7114229) B7114229
theorem B3161879 : Blo 2107435 3161879 := bstep (se 1 (by rfl) ⟨2371409, by rfl⟩ : syracuseStep 3161879 = 4742819) B4742819
theorem B2107919 : Blo 2107435 2107919 := bstep (se 1 (by rfl) ⟨1580939, by rfl⟩ : syracuseStep 2107919 = 3161879) B3161879
theorem B3161885 : Blo 2107435 3161885 := bbase (se 3 (by rfl) ⟨592853, by rfl⟩ : syracuseStep 3161885 = 1185707) (by norm_num)
theorem B2107923 : Blo 2107435 2107923 := bstep (se 1 (by rfl) ⟨1580942, by rfl⟩ : syracuseStep 2107923 = 3161885) B3161885
theorem B4742837 : Blo 2107435 4742837 := bbase (se 5 (by rfl) ⟨222320, by rfl⟩ : syracuseStep 4742837 = 444641) (by norm_num)
theorem B3161891 : Blo 2107435 3161891 := bstep (se 1 (by rfl) ⟨2371418, by rfl⟩ : syracuseStep 3161891 = 4742837) B4742837
theorem B2107927 : Blo 2107435 2107927 := bstep (se 1 (by rfl) ⟨1580945, by rfl⟩ : syracuseStep 2107927 = 3161891) B3161891
theorem B12005333 : Blo 2107435 12005333 := bbase (se 7 (by rfl) ⟨140687, by rfl⟩ : syracuseStep 12005333 = 281375) (by norm_num)
theorem B8003555 : Blo 2107435 8003555 := bstep (se 1 (by rfl) ⟨6002666, by rfl⟩ : syracuseStep 8003555 = 12005333) B12005333
theorem B5335703 : Blo 2107435 5335703 := bstep (se 1 (by rfl) ⟨4001777, by rfl⟩ : syracuseStep 5335703 = 8003555) B8003555
theorem B3557135 : Blo 2107435 3557135 := bstep (se 1 (by rfl) ⟨2667851, by rfl⟩ : syracuseStep 3557135 = 5335703) B5335703
theorem B2371423 : Blo 2107435 2371423 := bstep (se 1 (by rfl) ⟨1778567, by rfl⟩ : syracuseStep 2371423 = 3557135) B3557135
theorem B3161897 : Blo 2107435 3161897 := bstep (se 2 (by rfl) ⟨1185711, by rfl⟩ : syracuseStep 3161897 = 2371423) B2371423
theorem B2107931 : Blo 2107435 2107931 := bstep (se 1 (by rfl) ⟨1580948, by rfl⟩ : syracuseStep 2107931 = 3161897) B3161897
theorem B6002677 : Blo 2107435 6002677 := bbase (se 5 (by rfl) ⟨281375, by rfl⟩ : syracuseStep 6002677 = 562751) (by norm_num)
theorem B8003569 : Blo 2107435 8003569 := bstep (se 2 (by rfl) ⟨3001338, by rfl⟩ : syracuseStep 8003569 = 6002677) B6002677
theorem B10671425 : Blo 2107435 10671425 := bstep (se 2 (by rfl) ⟨4001784, by rfl⟩ : syracuseStep 10671425 = 8003569) B8003569
theorem B7114283 : Blo 2107435 7114283 := bstep (se 1 (by rfl) ⟨5335712, by rfl⟩ : syracuseStep 7114283 = 10671425) B10671425
theorem B4742855 : Blo 2107435 4742855 := bstep (se 1 (by rfl) ⟨3557141, by rfl⟩ : syracuseStep 4742855 = 7114283) B7114283
theorem B3161903 : Blo 2107435 3161903 := bstep (se 1 (by rfl) ⟨2371427, by rfl⟩ : syracuseStep 3161903 = 4742855) B4742855
theorem B2107935 : Blo 2107435 2107935 := bstep (se 1 (by rfl) ⟨1580951, by rfl⟩ : syracuseStep 2107935 = 3161903) B3161903
theorem B3161909 : Blo 2107435 3161909 := bbase (se 5 (by rfl) ⟨148214, by rfl⟩ : syracuseStep 3161909 = 296429) (by norm_num)
theorem B2107939 : Blo 2107435 2107939 := bstep (se 1 (by rfl) ⟨1580954, by rfl⟩ : syracuseStep 2107939 = 3161909) B3161909
theorem B5335733 : Blo 2107435 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B3557155 : Blo 2107435 3557155 := bstep (se 1 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 3557155 = 5335733) B5335733
theorem B4742873 : Blo 2107435 4742873 := bstep (se 2 (by rfl) ⟨1778577, by rfl⟩ : syracuseStep 4742873 = 3557155) B3557155
theorem B3161915 : Blo 2107435 3161915 := bstep (se 1 (by rfl) ⟨2371436, by rfl⟩ : syracuseStep 3161915 = 4742873) B4742873
theorem B2107943 : Blo 2107435 2107943 := bstep (se 1 (by rfl) ⟨1580957, by rfl⟩ : syracuseStep 2107943 = 3161915) B3161915
theorem B2371441 : Blo 2107435 2371441 := bbase (se 2 (by rfl) ⟨889290, by rfl⟩ : syracuseStep 2371441 = 1778581) (by norm_num)
theorem B3161921 : Blo 2107435 3161921 := bstep (se 2 (by rfl) ⟨1185720, by rfl⟩ : syracuseStep 3161921 = 2371441) B2371441
theorem B2107947 : Blo 2107435 2107947 := bstep (se 1 (by rfl) ⟨1580960, by rfl⟩ : syracuseStep 2107947 = 3161921) B3161921
theorem B9004085 : Blo 2107435 9004085 := bbase (se 5 (by rfl) ⟨422066, by rfl⟩ : syracuseStep 9004085 = 844133) (by norm_num)
theorem B6002723 : Blo 2107435 6002723 := bstep (se 1 (by rfl) ⟨4502042, by rfl⟩ : syracuseStep 6002723 = 9004085) B9004085
theorem B4001815 : Blo 2107435 4001815 := bstep (se 1 (by rfl) ⟨3001361, by rfl⟩ : syracuseStep 4001815 = 6002723) B6002723
theorem B5335753 : Blo 2107435 5335753 := bstep (se 2 (by rfl) ⟨2000907, by rfl⟩ : syracuseStep 5335753 = 4001815) B4001815
theorem B7114337 : Blo 2107435 7114337 := bstep (se 2 (by rfl) ⟨2667876, by rfl⟩ : syracuseStep 7114337 = 5335753) B5335753
theorem B4742891 : Blo 2107435 4742891 := bstep (se 1 (by rfl) ⟨3557168, by rfl⟩ : syracuseStep 4742891 = 7114337) B7114337
theorem B3161927 : Blo 2107435 3161927 := bstep (se 1 (by rfl) ⟨2371445, by rfl⟩ : syracuseStep 3161927 = 4742891) B4742891
theorem B2107951 : Blo 2107435 2107951 := bstep (se 1 (by rfl) ⟨1580963, by rfl⟩ : syracuseStep 2107951 = 3161927) B3161927
theorem B3161933 : Blo 2107435 3161933 := bbase (se 3 (by rfl) ⟨592862, by rfl⟩ : syracuseStep 3161933 = 1185725) (by norm_num)
theorem B2107955 : Blo 2107435 2107955 := bstep (se 1 (by rfl) ⟨1580966, by rfl⟩ : syracuseStep 2107955 = 3161933) B3161933
theorem B4742909 : Blo 2107435 4742909 := bbase (se 3 (by rfl) ⟨889295, by rfl⟩ : syracuseStep 4742909 = 1778591) (by norm_num)
theorem B3161939 : Blo 2107435 3161939 := bstep (se 1 (by rfl) ⟨2371454, by rfl⟩ : syracuseStep 3161939 = 4742909) B4742909
theorem B2107959 : Blo 2107435 2107959 := bstep (se 1 (by rfl) ⟨1580969, by rfl⟩ : syracuseStep 2107959 = 3161939) B3161939
theorem B3557189 : Blo 2107435 3557189 := bbase (se 4 (by rfl) ⟨333486, by rfl⟩ : syracuseStep 3557189 = 666973) (by norm_num)
theorem B2371459 : Blo 2107435 2371459 := bstep (se 1 (by rfl) ⟨1778594, by rfl⟩ : syracuseStep 2371459 = 3557189) B3557189
theorem B3161945 : Blo 2107435 3161945 := bstep (se 2 (by rfl) ⟨1185729, by rfl⟩ : syracuseStep 3161945 = 2371459) B2371459
theorem B2107963 : Blo 2107435 2107963 := bstep (se 1 (by rfl) ⟨1580972, by rfl⟩ : syracuseStep 2107963 = 3161945) B3161945
theorem B16007381 : Blo 2107435 16007381 := bbase (se 7 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 16007381 = 375173) (by norm_num)
theorem B10671587 : Blo 2107435 10671587 := bstep (se 1 (by rfl) ⟨8003690, by rfl⟩ : syracuseStep 10671587 = 16007381) B16007381
theorem B7114391 : Blo 2107435 7114391 := bstep (se 1 (by rfl) ⟨5335793, by rfl⟩ : syracuseStep 7114391 = 10671587) B10671587
theorem B4742927 : Blo 2107435 4742927 := bstep (se 1 (by rfl) ⟨3557195, by rfl⟩ : syracuseStep 4742927 = 7114391) B7114391
theorem B3161951 : Blo 2107435 3161951 := bstep (se 1 (by rfl) ⟨2371463, by rfl⟩ : syracuseStep 3161951 = 4742927) B4742927
theorem B2107967 : Blo 2107435 2107967 := bstep (se 1 (by rfl) ⟨1580975, by rfl⟩ : syracuseStep 2107967 = 3161951) B3161951
theorem B3161957 : Blo 2107435 3161957 := bbase (se 4 (by rfl) ⟨296433, by rfl⟩ : syracuseStep 3161957 = 592867) (by norm_num)
theorem B2107971 : Blo 2107435 2107971 := bstep (se 1 (by rfl) ⟨1580978, by rfl⟩ : syracuseStep 2107971 = 3161957) B3161957
theorem B4001861 : Blo 2107435 4001861 := bbase (se 4 (by rfl) ⟨375174, by rfl⟩ : syracuseStep 4001861 = 750349) (by norm_num)
theorem B2667907 : Blo 2107435 2667907 := bstep (se 1 (by rfl) ⟨2000930, by rfl⟩ : syracuseStep 2667907 = 4001861) B4001861
theorem B3557209 : Blo 2107435 3557209 := bstep (se 2 (by rfl) ⟨1333953, by rfl⟩ : syracuseStep 3557209 = 2667907) B2667907
theorem B4742945 : Blo 2107435 4742945 := bstep (se 2 (by rfl) ⟨1778604, by rfl⟩ : syracuseStep 4742945 = 3557209) B3557209
theorem B3161963 : Blo 2107435 3161963 := bstep (se 1 (by rfl) ⟨2371472, by rfl⟩ : syracuseStep 3161963 = 4742945) B4742945
theorem B2107975 : Blo 2107435 2107975 := bstep (se 1 (by rfl) ⟨1580981, by rfl⟩ : syracuseStep 2107975 = 3161963) B3161963
theorem B2371477 : Blo 2107435 2371477 := bbase (se 6 (by rfl) ⟨55581, by rfl⟩ : syracuseStep 2371477 = 111163) (by norm_num)
theorem B3161969 : Blo 2107435 3161969 := bstep (se 2 (by rfl) ⟨1185738, by rfl⟩ : syracuseStep 3161969 = 2371477) B2371477
theorem B2107979 : Blo 2107435 2107979 := bstep (se 1 (by rfl) ⟨1580984, by rfl⟩ : syracuseStep 2107979 = 3161969) B3161969
theorem B2667917 : Blo 2107435 2667917 := bbase (se 3 (by rfl) ⟨500234, by rfl⟩ : syracuseStep 2667917 = 1000469) (by norm_num)
theorem B7114445 : Blo 2107435 7114445 := bstep (se 3 (by rfl) ⟨1333958, by rfl⟩ : syracuseStep 7114445 = 2667917) B2667917
theorem B4742963 : Blo 2107435 4742963 := bstep (se 1 (by rfl) ⟨3557222, by rfl⟩ : syracuseStep 4742963 = 7114445) B7114445
theorem B3161975 : Blo 2107435 3161975 := bstep (se 1 (by rfl) ⟨2371481, by rfl⟩ : syracuseStep 3161975 = 4742963) B4742963
theorem B2107983 : Blo 2107435 2107983 := bstep (se 1 (by rfl) ⟨1580987, by rfl⟩ : syracuseStep 2107983 = 3161975) B3161975
theorem B3161981 : Blo 2107435 3161981 := bbase (se 3 (by rfl) ⟨592871, by rfl⟩ : syracuseStep 3161981 = 1185743) (by norm_num)
theorem B2107987 : Blo 2107435 2107987 := bstep (se 1 (by rfl) ⟨1580990, by rfl⟩ : syracuseStep 2107987 = 3161981) B3161981
theorem B4742981 : Blo 2107435 4742981 := bbase (se 4 (by rfl) ⟨444654, by rfl⟩ : syracuseStep 4742981 = 889309) (by norm_num)
theorem B3161987 : Blo 2107435 3161987 := bstep (se 1 (by rfl) ⟨2371490, by rfl⟩ : syracuseStep 3161987 = 4742981) B4742981
theorem B2107991 : Blo 2107435 2107991 := bstep (se 1 (by rfl) ⟨1580993, by rfl⟩ : syracuseStep 2107991 = 3161987) B3161987
theorem B8547029 : Blo 2107435 8547029 := bbase (se 7 (by rfl) ⟨100160, by rfl⟩ : syracuseStep 8547029 = 200321) (by norm_num)
theorem B5698019 : Blo 2107435 5698019 := bstep (se 1 (by rfl) ⟨4273514, by rfl⟩ : syracuseStep 5698019 = 8547029) B8547029
theorem B3798679 : Blo 2107435 3798679 := bstep (se 1 (by rfl) ⟨2849009, by rfl⟩ : syracuseStep 3798679 = 5698019) B5698019
theorem B5064905 : Blo 2107435 5064905 := bstep (se 2 (by rfl) ⟨1899339, by rfl⟩ : syracuseStep 5064905 = 3798679) B3798679
theorem B3376603 : Blo 2107435 3376603 := bstep (se 1 (by rfl) ⟨2532452, by rfl⟩ : syracuseStep 3376603 = 5064905) B5064905
theorem B4502137 : Blo 2107435 4502137 := bstep (se 2 (by rfl) ⟨1688301, by rfl⟩ : syracuseStep 4502137 = 3376603) B3376603
theorem B6002849 : Blo 2107435 6002849 := bstep (se 2 (by rfl) ⟨2251068, by rfl⟩ : syracuseStep 6002849 = 4502137) B4502137
theorem B4001899 : Blo 2107435 4001899 := bstep (se 1 (by rfl) ⟨3001424, by rfl⟩ : syracuseStep 4001899 = 6002849) B6002849
theorem B5335865 : Blo 2107435 5335865 := bstep (se 2 (by rfl) ⟨2000949, by rfl⟩ : syracuseStep 5335865 = 4001899) B4001899
theorem B3557243 : Blo 2107435 3557243 := bstep (se 1 (by rfl) ⟨2667932, by rfl⟩ : syracuseStep 3557243 = 5335865) B5335865
theorem B2371495 : Blo 2107435 2371495 := bstep (se 1 (by rfl) ⟨1778621, by rfl⟩ : syracuseStep 2371495 = 3557243) B3557243
theorem B3161993 : Blo 2107435 3161993 := bstep (se 2 (by rfl) ⟨1185747, by rfl⟩ : syracuseStep 3161993 = 2371495) B2371495
theorem B2107995 : Blo 2107435 2107995 := bstep (se 1 (by rfl) ⟨1580996, by rfl⟩ : syracuseStep 2107995 = 3161993) B3161993
theorem B10671749 : Blo 2107435 10671749 := bbase (se 4 (by rfl) ⟨1000476, by rfl⟩ : syracuseStep 10671749 = 2000953) (by norm_num)
theorem B7114499 : Blo 2107435 7114499 := bstep (se 1 (by rfl) ⟨5335874, by rfl⟩ : syracuseStep 7114499 = 10671749) B10671749
theorem B4742999 : Blo 2107435 4742999 := bstep (se 1 (by rfl) ⟨3557249, by rfl⟩ : syracuseStep 4742999 = 7114499) B7114499
theorem B3161999 : Blo 2107435 3161999 := bstep (se 1 (by rfl) ⟨2371499, by rfl⟩ : syracuseStep 3161999 = 4742999) B4742999
theorem B2107999 : Blo 2107435 2107999 := bstep (se 1 (by rfl) ⟨1580999, by rfl⟩ : syracuseStep 2107999 = 3161999) B3161999
theorem B3162005 : Blo 2107435 3162005 := bbase (se 6 (by rfl) ⟨74109, by rfl⟩ : syracuseStep 3162005 = 148219) (by norm_num)
theorem B2108003 : Blo 2107435 2108003 := bstep (se 1 (by rfl) ⟨1581002, by rfl⟩ : syracuseStep 2108003 = 3162005) B3162005
theorem B2251081 : Blo 2107435 2251081 := bbase (se 2 (by rfl) ⟨844155, by rfl⟩ : syracuseStep 2251081 = 1688311) (by norm_num)
theorem B12005765 : Blo 2107435 12005765 := bstep (se 4 (by rfl) ⟨1125540, by rfl⟩ : syracuseStep 12005765 = 2251081) B2251081
theorem B8003843 : Blo 2107435 8003843 := bstep (se 1 (by rfl) ⟨6002882, by rfl⟩ : syracuseStep 8003843 = 12005765) B12005765
theorem B5335895 : Blo 2107435 5335895 := bstep (se 1 (by rfl) ⟨4001921, by rfl⟩ : syracuseStep 5335895 = 8003843) B8003843
theorem B3557263 : Blo 2107435 3557263 := bstep (se 1 (by rfl) ⟨2667947, by rfl⟩ : syracuseStep 3557263 = 5335895) B5335895
theorem B4743017 : Blo 2107435 4743017 := bstep (se 2 (by rfl) ⟨1778631, by rfl⟩ : syracuseStep 4743017 = 3557263) B3557263
theorem B3162011 : Blo 2107435 3162011 := bstep (se 1 (by rfl) ⟨2371508, by rfl⟩ : syracuseStep 3162011 = 4743017) B4743017
theorem B2108007 : Blo 2107435 2108007 := bstep (se 1 (by rfl) ⟨1581005, by rfl⟩ : syracuseStep 2108007 = 3162011) B3162011
theorem B2371513 : Blo 2107435 2371513 := bbase (se 2 (by rfl) ⟨889317, by rfl⟩ : syracuseStep 2371513 = 1778635) (by norm_num)
theorem B3162017 : Blo 2107435 3162017 := bstep (se 2 (by rfl) ⟨1185756, by rfl⟩ : syracuseStep 3162017 = 2371513) B2371513
theorem B2108011 : Blo 2107435 2108011 := bstep (se 1 (by rfl) ⟨1581008, by rfl⟩ : syracuseStep 2108011 = 3162017) B3162017
theorem B6753269 : Blo 2107435 6753269 := bbase (se 5 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 6753269 = 633119) (by norm_num)
theorem B4502179 : Blo 2107435 4502179 := bstep (se 1 (by rfl) ⟨3376634, by rfl⟩ : syracuseStep 4502179 = 6753269) B6753269
theorem B6002905 : Blo 2107435 6002905 := bstep (se 2 (by rfl) ⟨2251089, by rfl⟩ : syracuseStep 6002905 = 4502179) B4502179
theorem B8003873 : Blo 2107435 8003873 := bstep (se 2 (by rfl) ⟨3001452, by rfl⟩ : syracuseStep 8003873 = 6002905) B6002905
theorem B5335915 : Blo 2107435 5335915 := bstep (se 1 (by rfl) ⟨4001936, by rfl⟩ : syracuseStep 5335915 = 8003873) B8003873
theorem B7114553 : Blo 2107435 7114553 := bstep (se 2 (by rfl) ⟨2667957, by rfl⟩ : syracuseStep 7114553 = 5335915) B5335915
theorem B4743035 : Blo 2107435 4743035 := bstep (se 1 (by rfl) ⟨3557276, by rfl⟩ : syracuseStep 4743035 = 7114553) B7114553
theorem B3162023 : Blo 2107435 3162023 := bstep (se 1 (by rfl) ⟨2371517, by rfl⟩ : syracuseStep 3162023 = 4743035) B4743035
theorem B2108015 : Blo 2107435 2108015 := bstep (se 1 (by rfl) ⟨1581011, by rfl⟩ : syracuseStep 2108015 = 3162023) B3162023
theorem B3162029 : Blo 2107435 3162029 := bbase (se 3 (by rfl) ⟨592880, by rfl⟩ : syracuseStep 3162029 = 1185761) (by norm_num)
theorem B2108019 : Blo 2107435 2108019 := bstep (se 1 (by rfl) ⟨1581014, by rfl⟩ : syracuseStep 2108019 = 3162029) B3162029
theorem B4743053 : Blo 2107435 4743053 := bbase (se 3 (by rfl) ⟨889322, by rfl⟩ : syracuseStep 4743053 = 1778645) (by norm_num)
theorem B3162035 : Blo 2107435 3162035 := bstep (se 1 (by rfl) ⟨2371526, by rfl⟩ : syracuseStep 3162035 = 4743053) B4743053
theorem B2108023 : Blo 2107435 2108023 := bstep (se 1 (by rfl) ⟨1581017, by rfl⟩ : syracuseStep 2108023 = 3162035) B3162035
theorem B2667973 : Blo 2107435 2667973 := bbase (se 4 (by rfl) ⟨250122, by rfl⟩ : syracuseStep 2667973 = 500245) (by norm_num)
theorem B3557297 : Blo 2107435 3557297 := bstep (se 2 (by rfl) ⟨1333986, by rfl⟩ : syracuseStep 3557297 = 2667973) B2667973
theorem B2371531 : Blo 2107435 2371531 := bstep (se 1 (by rfl) ⟨1778648, by rfl⟩ : syracuseStep 2371531 = 3557297) B3557297
theorem B3162041 : Blo 2107435 3162041 := bstep (se 2 (by rfl) ⟨1185765, by rfl⟩ : syracuseStep 3162041 = 2371531) B2371531
theorem B2108027 : Blo 2107435 2108027 := bstep (se 1 (by rfl) ⟨1581020, by rfl⟩ : syracuseStep 2108027 = 3162041) B3162041
theorem B3205189 : Blo 2107435 3205189 := bbase (se 4 (by rfl) ⟨300486, by rfl⟩ : syracuseStep 3205189 = 600973) (by norm_num)
theorem B17094341 : Blo 2107435 17094341 := bstep (se 4 (by rfl) ⟨1602594, by rfl⟩ : syracuseStep 17094341 = 3205189) B3205189
theorem B11396227 : Blo 2107435 11396227 := bstep (se 1 (by rfl) ⟨8547170, by rfl⟩ : syracuseStep 11396227 = 17094341) B17094341
theorem B15194969 : Blo 2107435 15194969 := bstep (se 2 (by rfl) ⟨5698113, by rfl⟩ : syracuseStep 15194969 = 11396227) B11396227
theorem B10129979 : Blo 2107435 10129979 := bstep (se 1 (by rfl) ⟨7597484, by rfl⟩ : syracuseStep 10129979 = 15194969) B15194969
theorem B27013277 : Blo 2107435 27013277 := bstep (se 3 (by rfl) ⟨5064989, by rfl⟩ : syracuseStep 27013277 = 10129979) B10129979
theorem B18008851 : Blo 2107435 18008851 := bstep (se 1 (by rfl) ⟨13506638, by rfl⟩ : syracuseStep 18008851 = 27013277) B27013277
theorem B24011801 : Blo 2107435 24011801 := bstep (se 2 (by rfl) ⟨9004425, by rfl⟩ : syracuseStep 24011801 = 18008851) B18008851
theorem B16007867 : Blo 2107435 16007867 := bstep (se 1 (by rfl) ⟨12005900, by rfl⟩ : syracuseStep 16007867 = 24011801) B24011801
theorem B10671911 : Blo 2107435 10671911 := bstep (se 1 (by rfl) ⟨8003933, by rfl⟩ : syracuseStep 10671911 = 16007867) B16007867
theorem B7114607 : Blo 2107435 7114607 := bstep (se 1 (by rfl) ⟨5335955, by rfl⟩ : syracuseStep 7114607 = 10671911) B10671911
theorem B4743071 : Blo 2107435 4743071 := bstep (se 1 (by rfl) ⟨3557303, by rfl⟩ : syracuseStep 4743071 = 7114607) B7114607
theorem B3162047 : Blo 2107435 3162047 := bstep (se 1 (by rfl) ⟨2371535, by rfl⟩ : syracuseStep 3162047 = 4743071) B4743071
theorem B2108031 : Blo 2107435 2108031 := bstep (se 1 (by rfl) ⟨1581023, by rfl⟩ : syracuseStep 2108031 = 3162047) B3162047
theorem B3162053 : Blo 2107435 3162053 := bbase (se 4 (by rfl) ⟨296442, by rfl⟩ : syracuseStep 3162053 = 592885) (by norm_num)
theorem B2108035 : Blo 2107435 2108035 := bstep (se 1 (by rfl) ⟨1581026, by rfl⟩ : syracuseStep 2108035 = 3162053) B3162053
theorem B3557317 : Blo 2107435 3557317 := bbase (se 4 (by rfl) ⟨333498, by rfl⟩ : syracuseStep 3557317 = 666997) (by norm_num)
theorem B4743089 : Blo 2107435 4743089 := bstep (se 2 (by rfl) ⟨1778658, by rfl⟩ : syracuseStep 4743089 = 3557317) B3557317
theorem B3162059 : Blo 2107435 3162059 := bstep (se 1 (by rfl) ⟨2371544, by rfl⟩ : syracuseStep 3162059 = 4743089) B4743089
theorem B2108039 : Blo 2107435 2108039 := bstep (se 1 (by rfl) ⟨1581029, by rfl⟩ : syracuseStep 2108039 = 3162059) B3162059
theorem B2371549 : Blo 2107435 2371549 := bbase (se 3 (by rfl) ⟨444665, by rfl⟩ : syracuseStep 2371549 = 889331) (by norm_num)
theorem B3162065 : Blo 2107435 3162065 := bstep (se 2 (by rfl) ⟨1185774, by rfl⟩ : syracuseStep 3162065 = 2371549) B2371549
theorem B2108043 : Blo 2107435 2108043 := bstep (se 1 (by rfl) ⟨1581032, by rfl⟩ : syracuseStep 2108043 = 3162065) B3162065
theorem B7114661 : Blo 2107435 7114661 := bbase (se 4 (by rfl) ⟨666999, by rfl⟩ : syracuseStep 7114661 = 1333999) (by norm_num)
theorem B4743107 : Blo 2107435 4743107 := bstep (se 1 (by rfl) ⟨3557330, by rfl⟩ : syracuseStep 4743107 = 7114661) B7114661
theorem B3162071 : Blo 2107435 3162071 := bstep (se 1 (by rfl) ⟨2371553, by rfl⟩ : syracuseStep 3162071 = 4743107) B4743107
theorem B2108047 : Blo 2107435 2108047 := bstep (se 1 (by rfl) ⟨1581035, by rfl⟩ : syracuseStep 2108047 = 3162071) B3162071
theorem B3162077 : Blo 2107435 3162077 := bbase (se 3 (by rfl) ⟨592889, by rfl⟩ : syracuseStep 3162077 = 1185779) (by norm_num)
theorem B2108051 : Blo 2107435 2108051 := bstep (se 1 (by rfl) ⟨1581038, by rfl⟩ : syracuseStep 2108051 = 3162077) B3162077
theorem B4743125 : Blo 2107435 4743125 := bbase (se 7 (by rfl) ⟨55583, by rfl⟩ : syracuseStep 4743125 = 111167) (by norm_num)
theorem B3162083 : Blo 2107435 3162083 := bstep (se 1 (by rfl) ⟨2371562, by rfl⟩ : syracuseStep 3162083 = 4743125) B4743125
theorem B2108055 : Blo 2107435 2108055 := bstep (se 1 (by rfl) ⟨1581041, by rfl⟩ : syracuseStep 2108055 = 3162083) B3162083
theorem B2532529 : Blo 2107435 2532529 := bbase (se 2 (by rfl) ⟨949698, by rfl⟩ : syracuseStep 2532529 = 1899397) (by norm_num)
theorem B13506821 : Blo 2107435 13506821 := bstep (se 4 (by rfl) ⟨1266264, by rfl⟩ : syracuseStep 13506821 = 2532529) B2532529
theorem B9004547 : Blo 2107435 9004547 := bstep (se 1 (by rfl) ⟨6753410, by rfl⟩ : syracuseStep 9004547 = 13506821) B13506821
theorem B6003031 : Blo 2107435 6003031 := bstep (se 1 (by rfl) ⟨4502273, by rfl⟩ : syracuseStep 6003031 = 9004547) B9004547
theorem B8004041 : Blo 2107435 8004041 := bstep (se 2 (by rfl) ⟨3001515, by rfl⟩ : syracuseStep 8004041 = 6003031) B6003031
theorem B5336027 : Blo 2107435 5336027 := bstep (se 1 (by rfl) ⟨4002020, by rfl⟩ : syracuseStep 5336027 = 8004041) B8004041
theorem B3557351 : Blo 2107435 3557351 := bstep (se 1 (by rfl) ⟨2668013, by rfl⟩ : syracuseStep 3557351 = 5336027) B5336027
theorem B2371567 : Blo 2107435 2371567 := bstep (se 1 (by rfl) ⟨1778675, by rfl⟩ : syracuseStep 2371567 = 3557351) B3557351
theorem B3162089 : Blo 2107435 3162089 := bstep (se 2 (by rfl) ⟨1185783, by rfl⟩ : syracuseStep 3162089 = 2371567) B2371567
theorem B2108059 : Blo 2107435 2108059 := bstep (se 1 (by rfl) ⟨1581044, by rfl⟩ : syracuseStep 2108059 = 3162089) B3162089
theorem B2403929 : Blo 2107435 2403929 := bbase (se 2 (by rfl) ⟨901473, by rfl⟩ : syracuseStep 2403929 = 1802947) (by norm_num)
theorem B6410477 : Blo 2107435 6410477 := bstep (se 3 (by rfl) ⟨1201964, by rfl⟩ : syracuseStep 6410477 = 2403929) B2403929
theorem B4273651 : Blo 2107435 4273651 := bstep (se 1 (by rfl) ⟨3205238, by rfl⟩ : syracuseStep 4273651 = 6410477) B6410477
theorem B5698201 : Blo 2107435 5698201 := bstep (se 2 (by rfl) ⟨2136825, by rfl⟩ : syracuseStep 5698201 = 4273651) B4273651
theorem B7597601 : Blo 2107435 7597601 := bstep (se 2 (by rfl) ⟨2849100, by rfl⟩ : syracuseStep 7597601 = 5698201) B5698201
theorem B5065067 : Blo 2107435 5065067 := bstep (se 1 (by rfl) ⟨3798800, by rfl⟩ : syracuseStep 5065067 = 7597601) B7597601
theorem B3376711 : Blo 2107435 3376711 := bstep (se 1 (by rfl) ⟨2532533, by rfl⟩ : syracuseStep 3376711 = 5065067) B5065067
theorem B18009125 : Blo 2107435 18009125 := bstep (se 4 (by rfl) ⟨1688355, by rfl⟩ : syracuseStep 18009125 = 3376711) B3376711
theorem B12006083 : Blo 2107435 12006083 := bstep (se 1 (by rfl) ⟨9004562, by rfl⟩ : syracuseStep 12006083 = 18009125) B18009125
theorem B8004055 : Blo 2107435 8004055 := bstep (se 1 (by rfl) ⟨6003041, by rfl⟩ : syracuseStep 8004055 = 12006083) B12006083
theorem B10672073 : Blo 2107435 10672073 := bstep (se 2 (by rfl) ⟨4002027, by rfl⟩ : syracuseStep 10672073 = 8004055) B8004055
theorem B7114715 : Blo 2107435 7114715 := bstep (se 1 (by rfl) ⟨5336036, by rfl⟩ : syracuseStep 7114715 = 10672073) B10672073
theorem B4743143 : Blo 2107435 4743143 := bstep (se 1 (by rfl) ⟨3557357, by rfl⟩ : syracuseStep 4743143 = 7114715) B7114715
theorem B3162095 : Blo 2107435 3162095 := bstep (se 1 (by rfl) ⟨2371571, by rfl⟩ : syracuseStep 3162095 = 4743143) B4743143
theorem B2108063 : Blo 2107435 2108063 := bstep (se 1 (by rfl) ⟨1581047, by rfl⟩ : syracuseStep 2108063 = 3162095) B3162095
theorem B3162101 : Blo 2107435 3162101 := bbase (se 5 (by rfl) ⟨148223, by rfl⟩ : syracuseStep 3162101 = 296447) (by norm_num)
theorem B2108067 : Blo 2107435 2108067 := bstep (se 1 (by rfl) ⟨1581050, by rfl⟩ : syracuseStep 2108067 = 3162101) B3162101
theorem B5408861 : Blo 2107435 5408861 := bbase (se 3 (by rfl) ⟨1014161, by rfl⟩ : syracuseStep 5408861 = 2028323) (by norm_num)
theorem B57694517 : Blo 2107435 57694517 := bstep (se 5 (by rfl) ⟨2704430, by rfl⟩ : syracuseStep 57694517 = 5408861) B5408861
theorem B38463011 : Blo 2107435 38463011 := bstep (se 1 (by rfl) ⟨28847258, by rfl⟩ : syracuseStep 38463011 = 57694517) B57694517
theorem B25642007 : Blo 2107435 25642007 := bstep (se 1 (by rfl) ⟨19231505, by rfl⟩ : syracuseStep 25642007 = 38463011) B38463011
theorem B17094671 : Blo 2107435 17094671 := bstep (se 1 (by rfl) ⟨12821003, by rfl⟩ : syracuseStep 17094671 = 25642007) B25642007
theorem B11396447 : Blo 2107435 11396447 := bstep (se 1 (by rfl) ⟨8547335, by rfl⟩ : syracuseStep 11396447 = 17094671) B17094671
theorem B7597631 : Blo 2107435 7597631 := bstep (se 1 (by rfl) ⟨5698223, by rfl⟩ : syracuseStep 7597631 = 11396447) B11396447
theorem B5065087 : Blo 2107435 5065087 := bstep (se 1 (by rfl) ⟨3798815, by rfl⟩ : syracuseStep 5065087 = 7597631) B7597631
theorem B6753449 : Blo 2107435 6753449 := bstep (se 2 (by rfl) ⟨2532543, by rfl⟩ : syracuseStep 6753449 = 5065087) B5065087
theorem B4502299 : Blo 2107435 4502299 := bstep (se 1 (by rfl) ⟨3376724, by rfl⟩ : syracuseStep 4502299 = 6753449) B6753449
theorem B6003065 : Blo 2107435 6003065 := bstep (se 2 (by rfl) ⟨2251149, by rfl⟩ : syracuseStep 6003065 = 4502299) B4502299
theorem B4002043 : Blo 2107435 4002043 := bstep (se 1 (by rfl) ⟨3001532, by rfl⟩ : syracuseStep 4002043 = 6003065) B6003065
theorem B5336057 : Blo 2107435 5336057 := bstep (se 2 (by rfl) ⟨2001021, by rfl⟩ : syracuseStep 5336057 = 4002043) B4002043
theorem B3557371 : Blo 2107435 3557371 := bstep (se 1 (by rfl) ⟨2668028, by rfl⟩ : syracuseStep 3557371 = 5336057) B5336057
theorem B4743161 : Blo 2107435 4743161 := bstep (se 2 (by rfl) ⟨1778685, by rfl⟩ : syracuseStep 4743161 = 3557371) B3557371
theorem B3162107 : Blo 2107435 3162107 := bstep (se 1 (by rfl) ⟨2371580, by rfl⟩ : syracuseStep 3162107 = 4743161) B4743161
theorem B2108071 : Blo 2107435 2108071 := bstep (se 1 (by rfl) ⟨1581053, by rfl⟩ : syracuseStep 2108071 = 3162107) B3162107
theorem B2371585 : Blo 2107435 2371585 := bbase (se 2 (by rfl) ⟨889344, by rfl⟩ : syracuseStep 2371585 = 1778689) (by norm_num)
theorem B3162113 : Blo 2107435 3162113 := bstep (se 2 (by rfl) ⟨1185792, by rfl⟩ : syracuseStep 3162113 = 2371585) B2371585
theorem B2108075 : Blo 2107435 2108075 := bstep (se 1 (by rfl) ⟨1581056, by rfl⟩ : syracuseStep 2108075 = 3162113) B3162113
theorem B5336077 : Blo 2107435 5336077 := bbase (se 3 (by rfl) ⟨1000514, by rfl⟩ : syracuseStep 5336077 = 2001029) (by norm_num)
theorem B7114769 : Blo 2107435 7114769 := bstep (se 2 (by rfl) ⟨2668038, by rfl⟩ : syracuseStep 7114769 = 5336077) B5336077
theorem B4743179 : Blo 2107435 4743179 := bstep (se 1 (by rfl) ⟨3557384, by rfl⟩ : syracuseStep 4743179 = 7114769) B7114769
theorem B3162119 : Blo 2107435 3162119 := bstep (se 1 (by rfl) ⟨2371589, by rfl⟩ : syracuseStep 3162119 = 4743179) B4743179
theorem B2108079 : Blo 2107435 2108079 := bstep (se 1 (by rfl) ⟨1581059, by rfl⟩ : syracuseStep 2108079 = 3162119) B3162119
theorem B3162125 : Blo 2107435 3162125 := bbase (se 3 (by rfl) ⟨592898, by rfl⟩ : syracuseStep 3162125 = 1185797) (by norm_num)
theorem B2108083 : Blo 2107435 2108083 := bstep (se 1 (by rfl) ⟨1581062, by rfl⟩ : syracuseStep 2108083 = 3162125) B3162125
theorem B4743197 : Blo 2107435 4743197 := bbase (se 3 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 4743197 = 1778699) (by norm_num)
theorem B3162131 : Blo 2107435 3162131 := bstep (se 1 (by rfl) ⟨2371598, by rfl⟩ : syracuseStep 3162131 = 4743197) B4743197
theorem B2108087 : Blo 2107435 2108087 := bstep (se 1 (by rfl) ⟨1581065, by rfl⟩ : syracuseStep 2108087 = 3162131) B3162131
theorem B3557405 : Blo 2107435 3557405 := bbase (se 3 (by rfl) ⟨667013, by rfl⟩ : syracuseStep 3557405 = 1334027) (by norm_num)
theorem B2371603 : Blo 2107435 2371603 := bstep (se 1 (by rfl) ⟨1778702, by rfl⟩ : syracuseStep 2371603 = 3557405) B3557405
theorem B3162137 : Blo 2107435 3162137 := bstep (se 2 (by rfl) ⟨1185801, by rfl⟩ : syracuseStep 3162137 = 2371603) B2371603
theorem B2108091 : Blo 2107435 2108091 := bstep (se 1 (by rfl) ⟨1581068, by rfl⟩ : syracuseStep 2108091 = 3162137) B3162137
theorem B2281889 : Blo 2107435 2281889 := bbase (se 2 (by rfl) ⟨855708, by rfl⟩ : syracuseStep 2281889 = 1711417) (by norm_num)
theorem B6085037 : Blo 2107435 6085037 := bstep (se 3 (by rfl) ⟨1140944, by rfl⟩ : syracuseStep 6085037 = 2281889) B2281889
theorem B4056691 : Blo 2107435 4056691 := bstep (se 1 (by rfl) ⟨3042518, by rfl⟩ : syracuseStep 4056691 = 6085037) B6085037
theorem B5408921 : Blo 2107435 5408921 := bstep (se 2 (by rfl) ⟨2028345, by rfl⟩ : syracuseStep 5408921 = 4056691) B4056691
theorem B14423789 : Blo 2107435 14423789 := bstep (se 3 (by rfl) ⟨2704460, by rfl⟩ : syracuseStep 14423789 = 5408921) B5408921
theorem B38463437 : Blo 2107435 38463437 := bstep (se 3 (by rfl) ⟨7211894, by rfl⟩ : syracuseStep 38463437 = 14423789) B14423789
theorem B25642291 : Blo 2107435 25642291 := bstep (se 1 (by rfl) ⟨19231718, by rfl⟩ : syracuseStep 25642291 = 38463437) B38463437
theorem B34189721 : Blo 2107435 34189721 := bstep (se 2 (by rfl) ⟨12821145, by rfl⟩ : syracuseStep 34189721 = 25642291) B25642291
theorem B22793147 : Blo 2107435 22793147 := bstep (se 1 (by rfl) ⟨17094860, by rfl⟩ : syracuseStep 22793147 = 34189721) B34189721
theorem B15195431 : Blo 2107435 15195431 := bstep (se 1 (by rfl) ⟨11396573, by rfl⟩ : syracuseStep 15195431 = 22793147) B22793147
theorem B10130287 : Blo 2107435 10130287 := bstep (se 1 (by rfl) ⟨7597715, by rfl⟩ : syracuseStep 10130287 = 15195431) B15195431
theorem B13507049 : Blo 2107435 13507049 := bstep (se 2 (by rfl) ⟨5065143, by rfl⟩ : syracuseStep 13507049 = 10130287) B10130287
theorem B9004699 : Blo 2107435 9004699 := bstep (se 1 (by rfl) ⟨6753524, by rfl⟩ : syracuseStep 9004699 = 13507049) B13507049
theorem B12006265 : Blo 2107435 12006265 := bstep (se 2 (by rfl) ⟨4502349, by rfl⟩ : syracuseStep 12006265 = 9004699) B9004699
theorem B16008353 : Blo 2107435 16008353 := bstep (se 2 (by rfl) ⟨6003132, by rfl⟩ : syracuseStep 16008353 = 12006265) B12006265
theorem B10672235 : Blo 2107435 10672235 := bstep (se 1 (by rfl) ⟨8004176, by rfl⟩ : syracuseStep 10672235 = 16008353) B16008353
theorem B7114823 : Blo 2107435 7114823 := bstep (se 1 (by rfl) ⟨5336117, by rfl⟩ : syracuseStep 7114823 = 10672235) B10672235
theorem B4743215 : Blo 2107435 4743215 := bstep (se 1 (by rfl) ⟨3557411, by rfl⟩ : syracuseStep 4743215 = 7114823) B7114823
theorem B3162143 : Blo 2107435 3162143 := bstep (se 1 (by rfl) ⟨2371607, by rfl⟩ : syracuseStep 3162143 = 4743215) B4743215
theorem B2108095 : Blo 2107435 2108095 := bstep (se 1 (by rfl) ⟨1581071, by rfl⟩ : syracuseStep 2108095 = 3162143) B3162143
theorem B3162149 : Blo 2107435 3162149 := bbase (se 4 (by rfl) ⟨296451, by rfl⟩ : syracuseStep 3162149 = 592903) (by norm_num)
theorem B2108099 : Blo 2107435 2108099 := bstep (se 1 (by rfl) ⟨1581074, by rfl⟩ : syracuseStep 2108099 = 3162149) B3162149
theorem B2668069 : Blo 2107435 2668069 := bbase (se 4 (by rfl) ⟨250131, by rfl⟩ : syracuseStep 2668069 = 500263) (by norm_num)
theorem B3557425 : Blo 2107435 3557425 := bstep (se 2 (by rfl) ⟨1334034, by rfl⟩ : syracuseStep 3557425 = 2668069) B2668069
theorem B4743233 : Blo 2107435 4743233 := bstep (se 2 (by rfl) ⟨1778712, by rfl⟩ : syracuseStep 4743233 = 3557425) B3557425
theorem B3162155 : Blo 2107435 3162155 := bstep (se 1 (by rfl) ⟨2371616, by rfl⟩ : syracuseStep 3162155 = 4743233) B4743233
theorem B2108103 : Blo 2107435 2108103 := bstep (se 1 (by rfl) ⟨1581077, by rfl⟩ : syracuseStep 2108103 = 3162155) B3162155
theorem B2371621 : Blo 2107435 2371621 := bbase (se 4 (by rfl) ⟨222339, by rfl⟩ : syracuseStep 2371621 = 444679) (by norm_num)
theorem B3162161 : Blo 2107435 3162161 := bstep (se 2 (by rfl) ⟨1185810, by rfl⟩ : syracuseStep 3162161 = 2371621) B2371621
theorem B2108107 : Blo 2107435 2108107 := bstep (se 1 (by rfl) ⟨1581080, by rfl⟩ : syracuseStep 2108107 = 3162161) B3162161
theorem B73021013 : Blo 2107435 73021013 := bbase (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) (by norm_num)
theorem B48680675 : Blo 2107435 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B32453783 : Blo 2107435 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B21635855 : Blo 2107435 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B14423903 : Blo 2107435 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B9615935 : Blo 2107435 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B25642493 : Blo 2107435 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B17094995 : Blo 2107435 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B11396663 : Blo 2107435 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B7597775 : Blo 2107435 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B5065183 : Blo 2107435 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B6753577 : Blo 2107435 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B9004769 : Blo 2107435 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B6003179 : Blo 2107435 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B4002119 : Blo 2107435 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B2668079 : Blo 2107435 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B7114877 : Blo 2107435 7114877 := bstep (se 3 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 7114877 = 2668079) B2668079
theorem B4743251 : Blo 2107435 4743251 := bstep (se 1 (by rfl) ⟨3557438, by rfl⟩ : syracuseStep 4743251 = 7114877) B7114877
theorem B3162167 : Blo 2107435 3162167 := bstep (se 1 (by rfl) ⟨2371625, by rfl⟩ : syracuseStep 3162167 = 4743251) B4743251
theorem B2108111 : Blo 2107435 2108111 := bstep (se 1 (by rfl) ⟨1581083, by rfl⟩ : syracuseStep 2108111 = 3162167) B3162167
theorem B3162173 : Blo 2107435 3162173 := bbase (se 3 (by rfl) ⟨592907, by rfl⟩ : syracuseStep 3162173 = 1185815) (by norm_num)
theorem B2108115 : Blo 2107435 2108115 := bstep (se 1 (by rfl) ⟨1581086, by rfl⟩ : syracuseStep 2108115 = 3162173) B3162173
theorem B4743269 : Blo 2107435 4743269 := bbase (se 4 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 4743269 = 889363) (by norm_num)
theorem B3162179 : Blo 2107435 3162179 := bstep (se 1 (by rfl) ⟨2371634, by rfl⟩ : syracuseStep 3162179 = 4743269) B4743269
theorem B2108119 : Blo 2107435 2108119 := bstep (se 1 (by rfl) ⟨1581089, by rfl⟩ : syracuseStep 2108119 = 3162179) B3162179
theorem B5336189 : Blo 2107435 5336189 := bbase (se 3 (by rfl) ⟨1000535, by rfl⟩ : syracuseStep 5336189 = 2001071) (by norm_num)
theorem B3557459 : Blo 2107435 3557459 := bstep (se 1 (by rfl) ⟨2668094, by rfl⟩ : syracuseStep 3557459 = 5336189) B5336189
theorem B2371639 : Blo 2107435 2371639 := bstep (se 1 (by rfl) ⟨1778729, by rfl⟩ : syracuseStep 2371639 = 3557459) B3557459
theorem B3162185 : Blo 2107435 3162185 := bstep (se 2 (by rfl) ⟨1185819, by rfl⟩ : syracuseStep 3162185 = 2371639) B2371639
theorem B2108123 : Blo 2107435 2108123 := bstep (se 1 (by rfl) ⟨1581092, by rfl⟩ : syracuseStep 2108123 = 3162185) B3162185
theorem B4002149 : Blo 2107435 4002149 := bbase (se 4 (by rfl) ⟨375201, by rfl⟩ : syracuseStep 4002149 = 750403) (by norm_num)
theorem B10672397 : Blo 2107435 10672397 := bstep (se 3 (by rfl) ⟨2001074, by rfl⟩ : syracuseStep 10672397 = 4002149) B4002149
theorem B7114931 : Blo 2107435 7114931 := bstep (se 1 (by rfl) ⟨5336198, by rfl⟩ : syracuseStep 7114931 = 10672397) B10672397
theorem B4743287 : Blo 2107435 4743287 := bstep (se 1 (by rfl) ⟨3557465, by rfl⟩ : syracuseStep 4743287 = 7114931) B7114931
theorem B3162191 : Blo 2107435 3162191 := bstep (se 1 (by rfl) ⟨2371643, by rfl⟩ : syracuseStep 3162191 = 4743287) B4743287
theorem B2108127 : Blo 2107435 2108127 := bstep (se 1 (by rfl) ⟨1581095, by rfl⟩ : syracuseStep 2108127 = 3162191) B3162191
theorem B3162197 : Blo 2107435 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B2108131 : Blo 2107435 2108131 := bstep (se 1 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 2108131 = 3162197) B3162197
theorem B5134349 : Blo 2107435 5134349 := bbase (se 3 (by rfl) ⟨962690, by rfl⟩ : syracuseStep 5134349 = 1925381) (by norm_num)
theorem B3422899 : Blo 2107435 3422899 := bstep (se 1 (by rfl) ⟨2567174, by rfl⟩ : syracuseStep 3422899 = 5134349) B5134349
theorem B4563865 : Blo 2107435 4563865 := bstep (se 2 (by rfl) ⟨1711449, by rfl⟩ : syracuseStep 4563865 = 3422899) B3422899
theorem B6085153 : Blo 2107435 6085153 := bstep (se 2 (by rfl) ⟨2281932, by rfl⟩ : syracuseStep 6085153 = 4563865) B4563865
theorem B8113537 : Blo 2107435 8113537 := bstep (se 2 (by rfl) ⟨3042576, by rfl⟩ : syracuseStep 8113537 = 6085153) B6085153
theorem B10818049 : Blo 2107435 10818049 := bstep (se 2 (by rfl) ⟨4056768, by rfl⟩ : syracuseStep 10818049 = 8113537) B8113537
theorem B14424065 : Blo 2107435 14424065 := bstep (se 2 (by rfl) ⟨5409024, by rfl⟩ : syracuseStep 14424065 = 10818049) B10818049
theorem B9616043 : Blo 2107435 9616043 := bstep (se 1 (by rfl) ⟨7212032, by rfl⟩ : syracuseStep 9616043 = 14424065) B14424065
theorem B25642781 : Blo 2107435 25642781 := bstep (se 3 (by rfl) ⟨4808021, by rfl⟩ : syracuseStep 25642781 = 9616043) B9616043
theorem B17095187 : Blo 2107435 17095187 := bstep (se 1 (by rfl) ⟨12821390, by rfl⟩ : syracuseStep 17095187 = 25642781) B25642781
theorem B11396791 : Blo 2107435 11396791 := bstep (se 1 (by rfl) ⟨8547593, by rfl⟩ : syracuseStep 11396791 = 17095187) B17095187
theorem B15195721 : Blo 2107435 15195721 := bstep (se 2 (by rfl) ⟨5698395, by rfl⟩ : syracuseStep 15195721 = 11396791) B11396791
theorem B20260961 : Blo 2107435 20260961 := bstep (se 2 (by rfl) ⟨7597860, by rfl⟩ : syracuseStep 20260961 = 15195721) B15195721
theorem B13507307 : Blo 2107435 13507307 := bstep (se 1 (by rfl) ⟨10130480, by rfl⟩ : syracuseStep 13507307 = 20260961) B20260961
theorem B9004871 : Blo 2107435 9004871 := bstep (se 1 (by rfl) ⟨6753653, by rfl⟩ : syracuseStep 9004871 = 13507307) B13507307
theorem B6003247 : Blo 2107435 6003247 := bstep (se 1 (by rfl) ⟨4502435, by rfl⟩ : syracuseStep 6003247 = 9004871) B9004871
theorem B8004329 : Blo 2107435 8004329 := bstep (se 2 (by rfl) ⟨3001623, by rfl⟩ : syracuseStep 8004329 = 6003247) B6003247
theorem B5336219 : Blo 2107435 5336219 := bstep (se 1 (by rfl) ⟨4002164, by rfl⟩ : syracuseStep 5336219 = 8004329) B8004329
theorem B3557479 : Blo 2107435 3557479 := bstep (se 1 (by rfl) ⟨2668109, by rfl⟩ : syracuseStep 3557479 = 5336219) B5336219
theorem B4743305 : Blo 2107435 4743305 := bstep (se 2 (by rfl) ⟨1778739, by rfl⟩ : syracuseStep 4743305 = 3557479) B3557479
theorem B3162203 : Blo 2107435 3162203 := bstep (se 1 (by rfl) ⟨2371652, by rfl⟩ : syracuseStep 3162203 = 4743305) B4743305
theorem B2108135 : Blo 2107435 2108135 := bstep (se 1 (by rfl) ⟨1581101, by rfl⟩ : syracuseStep 2108135 = 3162203) B3162203
theorem B2371657 : Blo 2107435 2371657 := bbase (se 2 (by rfl) ⟨889371, by rfl⟩ : syracuseStep 2371657 = 1778743) (by norm_num)
theorem B3162209 : Blo 2107435 3162209 := bstep (se 2 (by rfl) ⟨1185828, by rfl⟩ : syracuseStep 3162209 = 2371657) B2371657
theorem B2108139 : Blo 2107435 2108139 := bstep (se 1 (by rfl) ⟨1581104, by rfl⟩ : syracuseStep 2108139 = 3162209) B3162209
theorem B4273813 : Blo 2107435 4273813 := bbase (se 6 (by rfl) ⟨100167, by rfl⟩ : syracuseStep 4273813 = 200335) (by norm_num)
theorem B5698417 : Blo 2107435 5698417 := bstep (se 2 (by rfl) ⟨2136906, by rfl⟩ : syracuseStep 5698417 = 4273813) B4273813
theorem B7597889 : Blo 2107435 7597889 := bstep (se 2 (by rfl) ⟨2849208, by rfl⟩ : syracuseStep 7597889 = 5698417) B5698417
theorem B5065259 : Blo 2107435 5065259 := bstep (se 1 (by rfl) ⟨3798944, by rfl⟩ : syracuseStep 5065259 = 7597889) B7597889
theorem B13507357 : Blo 2107435 13507357 := bstep (se 3 (by rfl) ⟨2532629, by rfl⟩ : syracuseStep 13507357 = 5065259) B5065259
theorem B18009809 : Blo 2107435 18009809 := bstep (se 2 (by rfl) ⟨6753678, by rfl⟩ : syracuseStep 18009809 = 13507357) B13507357
theorem B12006539 : Blo 2107435 12006539 := bstep (se 1 (by rfl) ⟨9004904, by rfl⟩ : syracuseStep 12006539 = 18009809) B18009809
theorem B8004359 : Blo 2107435 8004359 := bstep (se 1 (by rfl) ⟨6003269, by rfl⟩ : syracuseStep 8004359 = 12006539) B12006539
theorem B5336239 : Blo 2107435 5336239 := bstep (se 1 (by rfl) ⟨4002179, by rfl⟩ : syracuseStep 5336239 = 8004359) B8004359
theorem B7114985 : Blo 2107435 7114985 := bstep (se 2 (by rfl) ⟨2668119, by rfl⟩ : syracuseStep 7114985 = 5336239) B5336239
theorem B4743323 : Blo 2107435 4743323 := bstep (se 1 (by rfl) ⟨3557492, by rfl⟩ : syracuseStep 4743323 = 7114985) B7114985
theorem B3162215 : Blo 2107435 3162215 := bstep (se 1 (by rfl) ⟨2371661, by rfl⟩ : syracuseStep 3162215 = 4743323) B4743323
theorem B2108143 : Blo 2107435 2108143 := bstep (se 1 (by rfl) ⟨1581107, by rfl⟩ : syracuseStep 2108143 = 3162215) B3162215
theorem B3162221 : Blo 2107435 3162221 := bbase (se 3 (by rfl) ⟨592916, by rfl⟩ : syracuseStep 3162221 = 1185833) (by norm_num)
theorem B2108147 : Blo 2107435 2108147 := bstep (se 1 (by rfl) ⟨1581110, by rfl⟩ : syracuseStep 2108147 = 3162221) B3162221
theorem B4743341 : Blo 2107435 4743341 := bbase (se 3 (by rfl) ⟨889376, by rfl⟩ : syracuseStep 4743341 = 1778753) (by norm_num)
theorem B3162227 : Blo 2107435 3162227 := bstep (se 1 (by rfl) ⟨2371670, by rfl⟩ : syracuseStep 3162227 = 4743341) B4743341
theorem B2108151 : Blo 2107435 2108151 := bstep (se 1 (by rfl) ⟨1581113, by rfl⟩ : syracuseStep 2108151 = 3162227) B3162227
theorem B4808069 : Blo 2107435 4808069 := bbase (se 4 (by rfl) ⟨450756, by rfl⟩ : syracuseStep 4808069 = 901513) (by norm_num)
theorem B3205379 : Blo 2107435 3205379 := bstep (se 1 (by rfl) ⟨2404034, by rfl⟩ : syracuseStep 3205379 = 4808069) B4808069
theorem B8547677 : Blo 2107435 8547677 := bstep (se 3 (by rfl) ⟨1602689, by rfl⟩ : syracuseStep 8547677 = 3205379) B3205379
theorem B5698451 : Blo 2107435 5698451 := bstep (se 1 (by rfl) ⟨4273838, by rfl⟩ : syracuseStep 5698451 = 8547677) B8547677
theorem B15195869 : Blo 2107435 15195869 := bstep (se 3 (by rfl) ⟨2849225, by rfl⟩ : syracuseStep 15195869 = 5698451) B5698451
theorem B10130579 : Blo 2107435 10130579 := bstep (se 1 (by rfl) ⟨7597934, by rfl⟩ : syracuseStep 10130579 = 15195869) B15195869
theorem B6753719 : Blo 2107435 6753719 := bstep (se 1 (by rfl) ⟨5065289, by rfl⟩ : syracuseStep 6753719 = 10130579) B10130579
theorem B4502479 : Blo 2107435 4502479 := bstep (se 1 (by rfl) ⟨3376859, by rfl⟩ : syracuseStep 4502479 = 6753719) B6753719
theorem B6003305 : Blo 2107435 6003305 := bstep (se 2 (by rfl) ⟨2251239, by rfl⟩ : syracuseStep 6003305 = 4502479) B4502479
theorem B4002203 : Blo 2107435 4002203 := bstep (se 1 (by rfl) ⟨3001652, by rfl⟩ : syracuseStep 4002203 = 6003305) B6003305
theorem B2668135 : Blo 2107435 2668135 := bstep (se 1 (by rfl) ⟨2001101, by rfl⟩ : syracuseStep 2668135 = 4002203) B4002203
theorem B3557513 : Blo 2107435 3557513 := bstep (se 2 (by rfl) ⟨1334067, by rfl⟩ : syracuseStep 3557513 = 2668135) B2668135
theorem B2371675 : Blo 2107435 2371675 := bstep (se 1 (by rfl) ⟨1778756, by rfl⟩ : syracuseStep 2371675 = 3557513) B3557513
theorem B3162233 : Blo 2107435 3162233 := bstep (se 2 (by rfl) ⟨1185837, by rfl⟩ : syracuseStep 3162233 = 2371675) B2371675
theorem B2108155 : Blo 2107435 2108155 := bstep (se 1 (by rfl) ⟨1581116, by rfl⟩ : syracuseStep 2108155 = 3162233) B3162233
theorem B3798973 : Blo 2107435 3798973 := bbase (se 3 (by rfl) ⟨712307, by rfl⟩ : syracuseStep 3798973 = 1424615) (by norm_num)
theorem B5065297 : Blo 2107435 5065297 := bstep (se 2 (by rfl) ⟨1899486, by rfl⟩ : syracuseStep 5065297 = 3798973) B3798973
theorem B27014917 : Blo 2107435 27014917 := bstep (se 4 (by rfl) ⟨2532648, by rfl⟩ : syracuseStep 27014917 = 5065297) B5065297
theorem B36019889 : Blo 2107435 36019889 := bstep (se 2 (by rfl) ⟨13507458, by rfl⟩ : syracuseStep 36019889 = 27014917) B27014917
theorem B24013259 : Blo 2107435 24013259 := bstep (se 1 (by rfl) ⟨18009944, by rfl⟩ : syracuseStep 24013259 = 36019889) B36019889
theorem B16008839 : Blo 2107435 16008839 := bstep (se 1 (by rfl) ⟨12006629, by rfl⟩ : syracuseStep 16008839 = 24013259) B24013259
theorem B10672559 : Blo 2107435 10672559 := bstep (se 1 (by rfl) ⟨8004419, by rfl⟩ : syracuseStep 10672559 = 16008839) B16008839
theorem B7115039 : Blo 2107435 7115039 := bstep (se 1 (by rfl) ⟨5336279, by rfl⟩ : syracuseStep 7115039 = 10672559) B10672559
theorem B4743359 : Blo 2107435 4743359 := bstep (se 1 (by rfl) ⟨3557519, by rfl⟩ : syracuseStep 4743359 = 7115039) B7115039
theorem B3162239 : Blo 2107435 3162239 := bstep (se 1 (by rfl) ⟨2371679, by rfl⟩ : syracuseStep 3162239 = 4743359) B4743359
theorem B2108159 : Blo 2107435 2108159 := bstep (se 1 (by rfl) ⟨1581119, by rfl⟩ : syracuseStep 2108159 = 3162239) B3162239
theorem B3162245 : Blo 2107435 3162245 := bbase (se 4 (by rfl) ⟨296460, by rfl⟩ : syracuseStep 3162245 = 592921) (by norm_num)
theorem B2108163 : Blo 2107435 2108163 := bstep (se 1 (by rfl) ⟨1581122, by rfl⟩ : syracuseStep 2108163 = 3162245) B3162245
theorem B3557533 : Blo 2107435 3557533 := bbase (se 3 (by rfl) ⟨667037, by rfl⟩ : syracuseStep 3557533 = 1334075) (by norm_num)
theorem B4743377 : Blo 2107435 4743377 := bstep (se 2 (by rfl) ⟨1778766, by rfl⟩ : syracuseStep 4743377 = 3557533) B3557533
theorem B3162251 : Blo 2107435 3162251 := bstep (se 1 (by rfl) ⟨2371688, by rfl⟩ : syracuseStep 3162251 = 4743377) B4743377
theorem B2108167 : Blo 2107435 2108167 := bstep (se 1 (by rfl) ⟨1581125, by rfl⟩ : syracuseStep 2108167 = 3162251) B3162251
theorem B2371693 : Blo 2107435 2371693 := bbase (se 3 (by rfl) ⟨444692, by rfl⟩ : syracuseStep 2371693 = 889385) (by norm_num)
theorem B3162257 : Blo 2107435 3162257 := bstep (se 2 (by rfl) ⟨1185846, by rfl⟩ : syracuseStep 3162257 = 2371693) B2371693
theorem B2108171 : Blo 2107435 2108171 := bstep (se 1 (by rfl) ⟨1581128, by rfl⟩ : syracuseStep 2108171 = 3162257) B3162257
theorem B7115093 : Blo 2107435 7115093 := bbase (se 10 (by rfl) ⟨10422, by rfl⟩ : syracuseStep 7115093 = 20845) (by norm_num)
theorem B4743395 : Blo 2107435 4743395 := bstep (se 1 (by rfl) ⟨3557546, by rfl⟩ : syracuseStep 4743395 = 7115093) B7115093
theorem B3162263 : Blo 2107435 3162263 := bstep (se 1 (by rfl) ⟨2371697, by rfl⟩ : syracuseStep 3162263 = 4743395) B4743395
theorem B2108175 : Blo 2107435 2108175 := bstep (se 1 (by rfl) ⟨1581131, by rfl⟩ : syracuseStep 2108175 = 3162263) B3162263
theorem B3162269 : Blo 2107435 3162269 := bbase (se 3 (by rfl) ⟨592925, by rfl⟩ : syracuseStep 3162269 = 1185851) (by norm_num)
theorem B2108179 : Blo 2107435 2108179 := bstep (se 1 (by rfl) ⟨1581134, by rfl⟩ : syracuseStep 2108179 = 3162269) B3162269
theorem B4743413 : Blo 2107435 4743413 := bbase (se 5 (by rfl) ⟨222347, by rfl⟩ : syracuseStep 4743413 = 444695) (by norm_num)
theorem B3162275 : Blo 2107435 3162275 := bstep (se 1 (by rfl) ⟨2371706, by rfl⟩ : syracuseStep 3162275 = 4743413) B4743413
theorem B2108183 : Blo 2107435 2108183 := bstep (se 1 (by rfl) ⟨1581137, by rfl⟩ : syracuseStep 2108183 = 3162275) B3162275
theorem B20261461 : Blo 2107435 20261461 := bbase (se 8 (by rfl) ⟨118719, by rfl⟩ : syracuseStep 20261461 = 237439) (by norm_num)
theorem B27015281 : Blo 2107435 27015281 := bstep (se 2 (by rfl) ⟨10130730, by rfl⟩ : syracuseStep 27015281 = 20261461) B20261461
theorem B18010187 : Blo 2107435 18010187 := bstep (se 1 (by rfl) ⟨13507640, by rfl⟩ : syracuseStep 18010187 = 27015281) B27015281
theorem B12006791 : Blo 2107435 12006791 := bstep (se 1 (by rfl) ⟨9005093, by rfl⟩ : syracuseStep 12006791 = 18010187) B18010187
theorem B8004527 : Blo 2107435 8004527 := bstep (se 1 (by rfl) ⟨6003395, by rfl⟩ : syracuseStep 8004527 = 12006791) B12006791
theorem B5336351 : Blo 2107435 5336351 := bstep (se 1 (by rfl) ⟨4002263, by rfl⟩ : syracuseStep 5336351 = 8004527) B8004527
theorem B3557567 : Blo 2107435 3557567 := bstep (se 1 (by rfl) ⟨2668175, by rfl⟩ : syracuseStep 3557567 = 5336351) B5336351
theorem B2371711 : Blo 2107435 2371711 := bstep (se 1 (by rfl) ⟨1778783, by rfl⟩ : syracuseStep 2371711 = 3557567) B3557567
theorem B3162281 : Blo 2107435 3162281 := bstep (se 2 (by rfl) ⟨1185855, by rfl⟩ : syracuseStep 3162281 = 2371711) B2371711
theorem B2108187 : Blo 2107435 2108187 := bstep (se 1 (by rfl) ⟨1581140, by rfl⟩ : syracuseStep 2108187 = 3162281) B3162281
theorem B9127973 : Blo 2107435 9127973 := bbase (se 4 (by rfl) ⟨855747, by rfl⟩ : syracuseStep 9127973 = 1711495) (by norm_num)
theorem B6085315 : Blo 2107435 6085315 := bstep (se 1 (by rfl) ⟨4563986, by rfl⟩ : syracuseStep 6085315 = 9127973) B9127973
theorem B8113753 : Blo 2107435 8113753 := bstep (se 2 (by rfl) ⟨3042657, by rfl⟩ : syracuseStep 8113753 = 6085315) B6085315
theorem B43273349 : Blo 2107435 43273349 := bstep (se 4 (by rfl) ⟨4056876, by rfl⟩ : syracuseStep 43273349 = 8113753) B8113753
theorem B28848899 : Blo 2107435 28848899 := bstep (se 1 (by rfl) ⟨21636674, by rfl⟩ : syracuseStep 28848899 = 43273349) B43273349
theorem B19232599 : Blo 2107435 19232599 := bstep (se 1 (by rfl) ⟨14424449, by rfl⟩ : syracuseStep 19232599 = 28848899) B28848899
theorem B25643465 : Blo 2107435 25643465 := bstep (se 2 (by rfl) ⟨9616299, by rfl⟩ : syracuseStep 25643465 = 19232599) B19232599
theorem B17095643 : Blo 2107435 17095643 := bstep (se 1 (by rfl) ⟨12821732, by rfl⟩ : syracuseStep 17095643 = 25643465) B25643465
theorem B11397095 : Blo 2107435 11397095 := bstep (se 1 (by rfl) ⟨8547821, by rfl⟩ : syracuseStep 11397095 = 17095643) B17095643
theorem B7598063 : Blo 2107435 7598063 := bstep (se 1 (by rfl) ⟨5698547, by rfl⟩ : syracuseStep 7598063 = 11397095) B11397095
theorem B5065375 : Blo 2107435 5065375 := bstep (se 1 (by rfl) ⟨3799031, by rfl⟩ : syracuseStep 5065375 = 7598063) B7598063
theorem B6753833 : Blo 2107435 6753833 := bstep (se 2 (by rfl) ⟨2532687, by rfl⟩ : syracuseStep 6753833 = 5065375) B5065375
theorem B4502555 : Blo 2107435 4502555 := bstep (se 1 (by rfl) ⟨3376916, by rfl⟩ : syracuseStep 4502555 = 6753833) B6753833
theorem B3001703 : Blo 2107435 3001703 := bstep (se 1 (by rfl) ⟨2251277, by rfl⟩ : syracuseStep 3001703 = 4502555) B4502555
theorem B8004541 : Blo 2107435 8004541 := bstep (se 3 (by rfl) ⟨1500851, by rfl⟩ : syracuseStep 8004541 = 3001703) B3001703
theorem B10672721 : Blo 2107435 10672721 := bstep (se 2 (by rfl) ⟨4002270, by rfl⟩ : syracuseStep 10672721 = 8004541) B8004541
theorem B7115147 : Blo 2107435 7115147 := bstep (se 1 (by rfl) ⟨5336360, by rfl⟩ : syracuseStep 7115147 = 10672721) B10672721
theorem B4743431 : Blo 2107435 4743431 := bstep (se 1 (by rfl) ⟨3557573, by rfl⟩ : syracuseStep 4743431 = 7115147) B7115147
theorem B3162287 : Blo 2107435 3162287 := bstep (se 1 (by rfl) ⟨2371715, by rfl⟩ : syracuseStep 3162287 = 4743431) B4743431
theorem B2108191 : Blo 2107435 2108191 := bstep (se 1 (by rfl) ⟨1581143, by rfl⟩ : syracuseStep 2108191 = 3162287) B3162287
theorem B3162293 : Blo 2107435 3162293 := bbase (se 5 (by rfl) ⟨148232, by rfl⟩ : syracuseStep 3162293 = 296465) (by norm_num)
theorem B2108195 : Blo 2107435 2108195 := bstep (se 1 (by rfl) ⟨1581146, by rfl⟩ : syracuseStep 2108195 = 3162293) B3162293
theorem B5336381 : Blo 2107435 5336381 := bbase (se 3 (by rfl) ⟨1000571, by rfl⟩ : syracuseStep 5336381 = 2001143) (by norm_num)
theorem B3557587 : Blo 2107435 3557587 := bstep (se 1 (by rfl) ⟨2668190, by rfl⟩ : syracuseStep 3557587 = 5336381) B5336381
theorem B4743449 : Blo 2107435 4743449 := bstep (se 2 (by rfl) ⟨1778793, by rfl⟩ : syracuseStep 4743449 = 3557587) B3557587
theorem B3162299 : Blo 2107435 3162299 := bstep (se 1 (by rfl) ⟨2371724, by rfl⟩ : syracuseStep 3162299 = 4743449) B4743449
theorem B2108199 : Blo 2107435 2108199 := bstep (se 1 (by rfl) ⟨1581149, by rfl⟩ : syracuseStep 2108199 = 3162299) B3162299
theorem B2371729 : Blo 2107435 2371729 := bbase (se 2 (by rfl) ⟨889398, by rfl⟩ : syracuseStep 2371729 = 1778797) (by norm_num)
theorem B3162305 : Blo 2107435 3162305 := bstep (se 2 (by rfl) ⟨1185864, by rfl⟩ : syracuseStep 3162305 = 2371729) B2371729
theorem B2108203 : Blo 2107435 2108203 := bstep (se 1 (by rfl) ⟨1581152, by rfl⟩ : syracuseStep 2108203 = 3162305) B3162305
theorem B4002301 : Blo 2107435 4002301 := bbase (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) (by norm_num)
theorem B5336401 : Blo 2107435 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B7115201 : Blo 2107435 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B4743467 : Blo 2107435 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B3162311 : Blo 2107435 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B2108207 : Blo 2107435 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B3162317 : Blo 2107435 3162317 := bbase (se 3 (by rfl) ⟨592934, by rfl⟩ : syracuseStep 3162317 = 1185869) (by norm_num)
theorem B2108211 : Blo 2107435 2108211 := bstep (se 1 (by rfl) ⟨1581158, by rfl⟩ : syracuseStep 2108211 = 3162317) B3162317
theorem B4743485 : Blo 2107435 4743485 := bbase (se 3 (by rfl) ⟨889403, by rfl⟩ : syracuseStep 4743485 = 1778807) (by norm_num)
theorem B3162323 : Blo 2107435 3162323 := bstep (se 1 (by rfl) ⟨2371742, by rfl⟩ : syracuseStep 3162323 = 4743485) B4743485
theorem B2108215 : Blo 2107435 2108215 := bstep (se 1 (by rfl) ⟨1581161, by rfl⟩ : syracuseStep 2108215 = 3162323) B3162323
theorem B3557621 : Blo 2107435 3557621 := bbase (se 5 (by rfl) ⟨166763, by rfl⟩ : syracuseStep 3557621 = 333527) (by norm_num)
theorem B2371747 : Blo 2107435 2371747 := bstep (se 1 (by rfl) ⟨1778810, by rfl⟩ : syracuseStep 2371747 = 3557621) B3557621
theorem B3162329 : Blo 2107435 3162329 := bstep (se 2 (by rfl) ⟨1185873, by rfl⟩ : syracuseStep 3162329 = 2371747) B2371747
theorem B2108219 : Blo 2107435 2108219 := bstep (se 1 (by rfl) ⟨1581164, by rfl⟩ : syracuseStep 2108219 = 3162329) B3162329
theorem B8113877 : Blo 2107435 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B5409251 : Blo 2107435 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B3606167 : Blo 2107435 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B9616445 : Blo 2107435 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B6410963 : Blo 2107435 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B4273975 : Blo 2107435 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B22794533 : Blo 2107435 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B15196355 : Blo 2107435 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B10130903 : Blo 2107435 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B6753935 : Blo 2107435 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B4502623 : Blo 2107435 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B6003497 : Blo 2107435 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B16009325 : Blo 2107435 16009325 := bstep (se 3 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 16009325 = 6003497) B6003497
theorem B10672883 : Blo 2107435 10672883 := bstep (se 1 (by rfl) ⟨8004662, by rfl⟩ : syracuseStep 10672883 = 16009325) B16009325
theorem B7115255 : Blo 2107435 7115255 := bstep (se 1 (by rfl) ⟨5336441, by rfl⟩ : syracuseStep 7115255 = 10672883) B10672883
theorem B4743503 : Blo 2107435 4743503 := bstep (se 1 (by rfl) ⟨3557627, by rfl⟩ : syracuseStep 4743503 = 7115255) B7115255
theorem B3162335 : Blo 2107435 3162335 := bstep (se 1 (by rfl) ⟨2371751, by rfl⟩ : syracuseStep 3162335 = 4743503) B4743503
theorem B2108223 : Blo 2107435 2108223 := bstep (se 1 (by rfl) ⟨1581167, by rfl⟩ : syracuseStep 2108223 = 3162335) B3162335
theorem B3162341 : Blo 2107435 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B2108227 : Blo 2107435 2108227 := bstep (se 1 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 2108227 = 3162341) B3162341
theorem B3376981 : Blo 2107435 3376981 := bbase (se 9 (by rfl) ⟨9893, by rfl⟩ : syracuseStep 3376981 = 19787) (by norm_num)
theorem B4502641 : Blo 2107435 4502641 := bstep (se 2 (by rfl) ⟨1688490, by rfl⟩ : syracuseStep 4502641 = 3376981) B3376981
theorem B6003521 : Blo 2107435 6003521 := bstep (se 2 (by rfl) ⟨2251320, by rfl⟩ : syracuseStep 6003521 = 4502641) B4502641
theorem B4002347 : Blo 2107435 4002347 := bstep (se 1 (by rfl) ⟨3001760, by rfl⟩ : syracuseStep 4002347 = 6003521) B6003521
theorem B2668231 : Blo 2107435 2668231 := bstep (se 1 (by rfl) ⟨2001173, by rfl⟩ : syracuseStep 2668231 = 4002347) B4002347
theorem B3557641 : Blo 2107435 3557641 := bstep (se 2 (by rfl) ⟨1334115, by rfl⟩ : syracuseStep 3557641 = 2668231) B2668231
theorem B4743521 : Blo 2107435 4743521 := bstep (se 2 (by rfl) ⟨1778820, by rfl⟩ : syracuseStep 4743521 = 3557641) B3557641
theorem B3162347 : Blo 2107435 3162347 := bstep (se 1 (by rfl) ⟨2371760, by rfl⟩ : syracuseStep 3162347 = 4743521) B4743521
theorem B2108231 : Blo 2107435 2108231 := bstep (se 1 (by rfl) ⟨1581173, by rfl⟩ : syracuseStep 2108231 = 3162347) B3162347
theorem B2371765 : Blo 2107435 2371765 := bbase (se 5 (by rfl) ⟨111176, by rfl⟩ : syracuseStep 2371765 = 222353) (by norm_num)
theorem B3162353 : Blo 2107435 3162353 := bstep (se 2 (by rfl) ⟨1185882, by rfl⟩ : syracuseStep 3162353 = 2371765) B2371765
theorem B2108235 : Blo 2107435 2108235 := bstep (se 1 (by rfl) ⟨1581176, by rfl⟩ : syracuseStep 2108235 = 3162353) B3162353
theorem B2668241 : Blo 2107435 2668241 := bbase (se 2 (by rfl) ⟨1000590, by rfl⟩ : syracuseStep 2668241 = 2001181) (by norm_num)
theorem B7115309 : Blo 2107435 7115309 := bstep (se 3 (by rfl) ⟨1334120, by rfl⟩ : syracuseStep 7115309 = 2668241) B2668241
theorem B4743539 : Blo 2107435 4743539 := bstep (se 1 (by rfl) ⟨3557654, by rfl⟩ : syracuseStep 4743539 = 7115309) B7115309
theorem B3162359 : Blo 2107435 3162359 := bstep (se 1 (by rfl) ⟨2371769, by rfl⟩ : syracuseStep 3162359 = 4743539) B4743539
theorem B2108239 : Blo 2107435 2108239 := bstep (se 1 (by rfl) ⟨1581179, by rfl⟩ : syracuseStep 2108239 = 3162359) B3162359
theorem B3162365 : Blo 2107435 3162365 := bbase (se 3 (by rfl) ⟨592943, by rfl⟩ : syracuseStep 3162365 = 1185887) (by norm_num)
theorem B2108243 : Blo 2107435 2108243 := bstep (se 1 (by rfl) ⟨1581182, by rfl⟩ : syracuseStep 2108243 = 3162365) B3162365
theorem B4743557 : Blo 2107435 4743557 := bbase (se 4 (by rfl) ⟨444708, by rfl⟩ : syracuseStep 4743557 = 889417) (by norm_num)
theorem B3162371 : Blo 2107435 3162371 := bstep (se 1 (by rfl) ⟨2371778, by rfl⟩ : syracuseStep 3162371 = 4743557) B4743557
theorem B2108247 : Blo 2107435 2108247 := bstep (se 1 (by rfl) ⟨1581185, by rfl⟩ : syracuseStep 2108247 = 3162371) B3162371
theorem B3001789 : Blo 2107435 3001789 := bbase (se 3 (by rfl) ⟨562835, by rfl⟩ : syracuseStep 3001789 = 1125671) (by norm_num)
theorem B4002385 : Blo 2107435 4002385 := bstep (se 2 (by rfl) ⟨1500894, by rfl⟩ : syracuseStep 4002385 = 3001789) B3001789
theorem B5336513 : Blo 2107435 5336513 := bstep (se 2 (by rfl) ⟨2001192, by rfl⟩ : syracuseStep 5336513 = 4002385) B4002385
theorem B3557675 : Blo 2107435 3557675 := bstep (se 1 (by rfl) ⟨2668256, by rfl⟩ : syracuseStep 3557675 = 5336513) B5336513
theorem B2371783 : Blo 2107435 2371783 := bstep (se 1 (by rfl) ⟨1778837, by rfl⟩ : syracuseStep 2371783 = 3557675) B3557675
theorem B3162377 : Blo 2107435 3162377 := bstep (se 2 (by rfl) ⟨1185891, by rfl⟩ : syracuseStep 3162377 = 2371783) B2371783
theorem B2108251 : Blo 2107435 2108251 := bstep (se 1 (by rfl) ⟨1581188, by rfl⟩ : syracuseStep 2108251 = 3162377) B3162377
theorem B10673045 : Blo 2107435 10673045 := bbase (se 6 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 10673045 = 500299) (by norm_num)
theorem B7115363 : Blo 2107435 7115363 := bstep (se 1 (by rfl) ⟨5336522, by rfl⟩ : syracuseStep 7115363 = 10673045) B10673045
theorem B4743575 : Blo 2107435 4743575 := bstep (se 1 (by rfl) ⟨3557681, by rfl⟩ : syracuseStep 4743575 = 7115363) B7115363
theorem B3162383 : Blo 2107435 3162383 := bstep (se 1 (by rfl) ⟨2371787, by rfl⟩ : syracuseStep 3162383 = 4743575) B4743575
theorem B2108255 : Blo 2107435 2108255 := bstep (se 1 (by rfl) ⟨1581191, by rfl⟩ : syracuseStep 2108255 = 3162383) B3162383
theorem B3162389 : Blo 2107435 3162389 := bbase (se 6 (by rfl) ⟨74118, by rfl⟩ : syracuseStep 3162389 = 148237) (by norm_num)
theorem B2108259 : Blo 2107435 2108259 := bstep (se 1 (by rfl) ⟨1581194, by rfl⟩ : syracuseStep 2108259 = 3162389) B3162389
theorem B22794965 : Blo 2107435 22794965 := bbase (se 7 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 22794965 = 534257) (by norm_num)
theorem B15196643 : Blo 2107435 15196643 := bstep (se 1 (by rfl) ⟨11397482, by rfl⟩ : syracuseStep 15196643 = 22794965) B22794965
theorem B10131095 : Blo 2107435 10131095 := bstep (se 1 (by rfl) ⟨7598321, by rfl⟩ : syracuseStep 10131095 = 15196643) B15196643
theorem B27016253 : Blo 2107435 27016253 := bstep (se 3 (by rfl) ⟨5065547, by rfl⟩ : syracuseStep 27016253 = 10131095) B10131095
theorem B18010835 : Blo 2107435 18010835 := bstep (se 1 (by rfl) ⟨13508126, by rfl⟩ : syracuseStep 18010835 = 27016253) B27016253
theorem B12007223 : Blo 2107435 12007223 := bstep (se 1 (by rfl) ⟨9005417, by rfl⟩ : syracuseStep 12007223 = 18010835) B18010835
theorem B8004815 : Blo 2107435 8004815 := bstep (se 1 (by rfl) ⟨6003611, by rfl⟩ : syracuseStep 8004815 = 12007223) B12007223
theorem B5336543 : Blo 2107435 5336543 := bstep (se 1 (by rfl) ⟨4002407, by rfl⟩ : syracuseStep 5336543 = 8004815) B8004815
theorem B3557695 : Blo 2107435 3557695 := bstep (se 1 (by rfl) ⟨2668271, by rfl⟩ : syracuseStep 3557695 = 5336543) B5336543
theorem B4743593 : Blo 2107435 4743593 := bstep (se 2 (by rfl) ⟨1778847, by rfl⟩ : syracuseStep 4743593 = 3557695) B3557695
theorem B3162395 : Blo 2107435 3162395 := bstep (se 1 (by rfl) ⟨2371796, by rfl⟩ : syracuseStep 3162395 = 4743593) B4743593
theorem B2108263 : Blo 2107435 2108263 := bstep (se 1 (by rfl) ⟨1581197, by rfl⟩ : syracuseStep 2108263 = 3162395) B3162395
theorem B2371801 : Blo 2107435 2371801 := bbase (se 2 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 2371801 = 1778851) (by norm_num)
theorem B3162401 : Blo 2107435 3162401 := bstep (se 2 (by rfl) ⟨1185900, by rfl⟩ : syracuseStep 3162401 = 2371801) B2371801
theorem B2108267 : Blo 2107435 2108267 := bstep (se 1 (by rfl) ⟨1581200, by rfl⟩ : syracuseStep 2108267 = 3162401) B3162401
theorem B3377045 : Blo 2107435 3377045 := bbase (se 6 (by rfl) ⟨79149, by rfl⟩ : syracuseStep 3377045 = 158299) (by norm_num)
theorem B2251363 : Blo 2107435 2251363 := bstep (se 1 (by rfl) ⟨1688522, by rfl⟩ : syracuseStep 2251363 = 3377045) B3377045
theorem B3001817 : Blo 2107435 3001817 := bstep (se 2 (by rfl) ⟨1125681, by rfl⟩ : syracuseStep 3001817 = 2251363) B2251363
theorem B8004845 : Blo 2107435 8004845 := bstep (se 3 (by rfl) ⟨1500908, by rfl⟩ : syracuseStep 8004845 = 3001817) B3001817
theorem B5336563 : Blo 2107435 5336563 := bstep (se 1 (by rfl) ⟨4002422, by rfl⟩ : syracuseStep 5336563 = 8004845) B8004845
theorem B7115417 : Blo 2107435 7115417 := bstep (se 2 (by rfl) ⟨2668281, by rfl⟩ : syracuseStep 7115417 = 5336563) B5336563
theorem B4743611 : Blo 2107435 4743611 := bstep (se 1 (by rfl) ⟨3557708, by rfl⟩ : syracuseStep 4743611 = 7115417) B7115417
theorem B3162407 : Blo 2107435 3162407 := bstep (se 1 (by rfl) ⟨2371805, by rfl⟩ : syracuseStep 3162407 = 4743611) B4743611
theorem B2108271 : Blo 2107435 2108271 := bstep (se 1 (by rfl) ⟨1581203, by rfl⟩ : syracuseStep 2108271 = 3162407) B3162407
theorem B3162413 : Blo 2107435 3162413 := bbase (se 3 (by rfl) ⟨592952, by rfl⟩ : syracuseStep 3162413 = 1185905) (by norm_num)
theorem B2108275 : Blo 2107435 2108275 := bstep (se 1 (by rfl) ⟨1581206, by rfl⟩ : syracuseStep 2108275 = 3162413) B3162413
theorem B4743629 : Blo 2107435 4743629 := bbase (se 3 (by rfl) ⟨889430, by rfl⟩ : syracuseStep 4743629 = 1778861) (by norm_num)
theorem B3162419 : Blo 2107435 3162419 := bstep (se 1 (by rfl) ⟨2371814, by rfl⟩ : syracuseStep 3162419 = 4743629) B4743629
theorem B2108279 : Blo 2107435 2108279 := bstep (se 1 (by rfl) ⟨1581209, by rfl⟩ : syracuseStep 2108279 = 3162419) B3162419
theorem B2668297 : Blo 2107435 2668297 := bbase (se 2 (by rfl) ⟨1000611, by rfl⟩ : syracuseStep 2668297 = 2001223) (by norm_num)
theorem B3557729 : Blo 2107435 3557729 := bstep (se 2 (by rfl) ⟨1334148, by rfl⟩ : syracuseStep 3557729 = 2668297) B2668297
theorem B2371819 : Blo 2107435 2371819 := bstep (se 1 (by rfl) ⟨1778864, by rfl⟩ : syracuseStep 2371819 = 3557729) B3557729
theorem B3162425 : Blo 2107435 3162425 := bstep (se 2 (by rfl) ⟨1185909, by rfl⟩ : syracuseStep 3162425 = 2371819) B2371819
theorem B2108283 : Blo 2107435 2108283 := bstep (se 1 (by rfl) ⟨1581212, by rfl⟩ : syracuseStep 2108283 = 3162425) B3162425
theorem B6939701 : Blo 2107435 6939701 := bbase (se 5 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 6939701 = 650597) (by norm_num)
theorem B4626467 : Blo 2107435 4626467 := bstep (se 1 (by rfl) ⟨3469850, by rfl⟩ : syracuseStep 4626467 = 6939701) B6939701
theorem B3084311 : Blo 2107435 3084311 := bstep (se 1 (by rfl) ⟨2313233, by rfl⟩ : syracuseStep 3084311 = 4626467) B4626467
theorem B8224829 : Blo 2107435 8224829 := bstep (se 3 (by rfl) ⟨1542155, by rfl⟩ : syracuseStep 8224829 = 3084311) B3084311
theorem B5483219 : Blo 2107435 5483219 := bstep (se 1 (by rfl) ⟨4112414, by rfl⟩ : syracuseStep 5483219 = 8224829) B8224829
theorem B14621917 : Blo 2107435 14621917 := bstep (se 3 (by rfl) ⟨2741609, by rfl⟩ : syracuseStep 14621917 = 5483219) B5483219
theorem B19495889 : Blo 2107435 19495889 := bstep (se 2 (by rfl) ⟨7310958, by rfl⟩ : syracuseStep 19495889 = 14621917) B14621917
theorem B12997259 : Blo 2107435 12997259 := bstep (se 1 (by rfl) ⟨9747944, by rfl⟩ : syracuseStep 12997259 = 19495889) B19495889
theorem B8664839 : Blo 2107435 8664839 := bstep (se 1 (by rfl) ⟨6498629, by rfl⟩ : syracuseStep 8664839 = 12997259) B12997259
theorem B5776559 : Blo 2107435 5776559 := bstep (se 1 (by rfl) ⟨4332419, by rfl⟩ : syracuseStep 5776559 = 8664839) B8664839
theorem B3851039 : Blo 2107435 3851039 := bstep (se 1 (by rfl) ⟨2888279, by rfl⟩ : syracuseStep 3851039 = 5776559) B5776559
theorem B2567359 : Blo 2107435 2567359 := bstep (se 1 (by rfl) ⟨1925519, by rfl⟩ : syracuseStep 2567359 = 3851039) B3851039
theorem B3423145 : Blo 2107435 3423145 := bstep (se 2 (by rfl) ⟨1283679, by rfl⟩ : syracuseStep 3423145 = 2567359) B2567359
theorem B4564193 : Blo 2107435 4564193 := bstep (se 2 (by rfl) ⟨1711572, by rfl⟩ : syracuseStep 4564193 = 3423145) B3423145
theorem B48684725 : Blo 2107435 48684725 := bstep (se 5 (by rfl) ⟨2282096, by rfl⟩ : syracuseStep 48684725 = 4564193) B4564193
theorem B32456483 : Blo 2107435 32456483 := bstep (se 1 (by rfl) ⟨24342362, by rfl⟩ : syracuseStep 32456483 = 48684725) B48684725
theorem B21637655 : Blo 2107435 21637655 := bstep (se 1 (by rfl) ⟨16228241, by rfl⟩ : syracuseStep 21637655 = 32456483) B32456483
theorem B14425103 : Blo 2107435 14425103 := bstep (se 1 (by rfl) ⟨10818827, by rfl⟩ : syracuseStep 14425103 = 21637655) B21637655
theorem B9616735 : Blo 2107435 9616735 := bstep (se 1 (by rfl) ⟨7212551, by rfl⟩ : syracuseStep 9616735 = 14425103) B14425103
theorem B12822313 : Blo 2107435 12822313 := bstep (se 2 (by rfl) ⟨4808367, by rfl⟩ : syracuseStep 12822313 = 9616735) B9616735
theorem B17096417 : Blo 2107435 17096417 := bstep (se 2 (by rfl) ⟨6411156, by rfl⟩ : syracuseStep 17096417 = 12822313) B12822313
theorem B11397611 : Blo 2107435 11397611 := bstep (se 1 (by rfl) ⟨8548208, by rfl⟩ : syracuseStep 11397611 = 17096417) B17096417
theorem B30393629 : Blo 2107435 30393629 := bstep (se 3 (by rfl) ⟨5698805, by rfl⟩ : syracuseStep 30393629 = 11397611) B11397611
theorem B20262419 : Blo 2107435 20262419 := bstep (se 1 (by rfl) ⟨15196814, by rfl⟩ : syracuseStep 20262419 = 30393629) B30393629
theorem B13508279 : Blo 2107435 13508279 := bstep (se 1 (by rfl) ⟨10131209, by rfl⟩ : syracuseStep 13508279 = 20262419) B20262419
theorem B9005519 : Blo 2107435 9005519 := bstep (se 1 (by rfl) ⟨6754139, by rfl⟩ : syracuseStep 9005519 = 13508279) B13508279
theorem B24014717 : Blo 2107435 24014717 := bstep (se 3 (by rfl) ⟨4502759, by rfl⟩ : syracuseStep 24014717 = 9005519) B9005519
theorem B16009811 : Blo 2107435 16009811 := bstep (se 1 (by rfl) ⟨12007358, by rfl⟩ : syracuseStep 16009811 = 24014717) B24014717
theorem B10673207 : Blo 2107435 10673207 := bstep (se 1 (by rfl) ⟨8004905, by rfl⟩ : syracuseStep 10673207 = 16009811) B16009811
theorem B7115471 : Blo 2107435 7115471 := bstep (se 1 (by rfl) ⟨5336603, by rfl⟩ : syracuseStep 7115471 = 10673207) B10673207
theorem B4743647 : Blo 2107435 4743647 := bstep (se 1 (by rfl) ⟨3557735, by rfl⟩ : syracuseStep 4743647 = 7115471) B7115471
theorem B3162431 : Blo 2107435 3162431 := bstep (se 1 (by rfl) ⟨2371823, by rfl⟩ : syracuseStep 3162431 = 4743647) B4743647
theorem B2108287 : Blo 2107435 2108287 := bstep (se 1 (by rfl) ⟨1581215, by rfl⟩ : syracuseStep 2108287 = 3162431) B3162431
theorem B3162437 : Blo 2107435 3162437 := bbase (se 4 (by rfl) ⟨296478, by rfl⟩ : syracuseStep 3162437 = 592957) (by norm_num)
theorem B2108291 : Blo 2107435 2108291 := bstep (se 1 (by rfl) ⟨1581218, by rfl⟩ : syracuseStep 2108291 = 3162437) B3162437
theorem B3557749 : Blo 2107435 3557749 := bbase (se 5 (by rfl) ⟨166769, by rfl⟩ : syracuseStep 3557749 = 333539) (by norm_num)
theorem B4743665 : Blo 2107435 4743665 := bstep (se 2 (by rfl) ⟨1778874, by rfl⟩ : syracuseStep 4743665 = 3557749) B3557749
theorem B3162443 : Blo 2107435 3162443 := bstep (se 1 (by rfl) ⟨2371832, by rfl⟩ : syracuseStep 3162443 = 4743665) B4743665
theorem B2108295 : Blo 2107435 2108295 := bstep (se 1 (by rfl) ⟨1581221, by rfl⟩ : syracuseStep 2108295 = 3162443) B3162443
theorem B2371837 : Blo 2107435 2371837 := bbase (se 3 (by rfl) ⟨444719, by rfl⟩ : syracuseStep 2371837 = 889439) (by norm_num)
theorem B3162449 : Blo 2107435 3162449 := bstep (se 2 (by rfl) ⟨1185918, by rfl⟩ : syracuseStep 3162449 = 2371837) B2371837
theorem B2108299 : Blo 2107435 2108299 := bstep (se 1 (by rfl) ⟨1581224, by rfl⟩ : syracuseStep 2108299 = 3162449) B3162449
theorem B7115525 : Blo 2107435 7115525 := bbase (se 4 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 7115525 = 1334161) (by norm_num)
theorem B4743683 : Blo 2107435 4743683 := bstep (se 1 (by rfl) ⟨3557762, by rfl⟩ : syracuseStep 4743683 = 7115525) B7115525
theorem B3162455 : Blo 2107435 3162455 := bstep (se 1 (by rfl) ⟨2371841, by rfl⟩ : syracuseStep 3162455 = 4743683) B4743683
theorem B2108303 : Blo 2107435 2108303 := bstep (se 1 (by rfl) ⟨1581227, by rfl⟩ : syracuseStep 2108303 = 3162455) B3162455
theorem B3162461 : Blo 2107435 3162461 := bbase (se 3 (by rfl) ⟨592961, by rfl⟩ : syracuseStep 3162461 = 1185923) (by norm_num)
theorem B2108307 : Blo 2107435 2108307 := bstep (se 1 (by rfl) ⟨1581230, by rfl⟩ : syracuseStep 2108307 = 3162461) B3162461
theorem B4743701 : Blo 2107435 4743701 := bbase (se 6 (by rfl) ⟨111180, by rfl⟩ : syracuseStep 4743701 = 222361) (by norm_num)
theorem B3162467 : Blo 2107435 3162467 := bstep (se 1 (by rfl) ⟨2371850, by rfl⟩ : syracuseStep 3162467 = 4743701) B4743701
theorem B2108311 : Blo 2107435 2108311 := bstep (se 1 (by rfl) ⟨1581233, by rfl⟩ : syracuseStep 2108311 = 3162467) B3162467
theorem B8005013 : Blo 2107435 8005013 := bbase (se 6 (by rfl) ⟨187617, by rfl⟩ : syracuseStep 8005013 = 375235) (by norm_num)
theorem B5336675 : Blo 2107435 5336675 := bstep (se 1 (by rfl) ⟨4002506, by rfl⟩ : syracuseStep 5336675 = 8005013) B8005013
theorem B3557783 : Blo 2107435 3557783 := bstep (se 1 (by rfl) ⟨2668337, by rfl⟩ : syracuseStep 3557783 = 5336675) B5336675
theorem B2371855 : Blo 2107435 2371855 := bstep (se 1 (by rfl) ⟨1778891, by rfl⟩ : syracuseStep 2371855 = 3557783) B3557783
theorem B3162473 : Blo 2107435 3162473 := bstep (se 2 (by rfl) ⟨1185927, by rfl⟩ : syracuseStep 3162473 = 2371855) B2371855
theorem B2108315 : Blo 2107435 2108315 := bstep (se 1 (by rfl) ⟨1581236, by rfl⟩ : syracuseStep 2108315 = 3162473) B3162473
theorem B12007541 : Blo 2107435 12007541 := bbase (se 5 (by rfl) ⟨562853, by rfl⟩ : syracuseStep 12007541 = 1125707) (by norm_num)
theorem B8005027 : Blo 2107435 8005027 := bstep (se 1 (by rfl) ⟨6003770, by rfl⟩ : syracuseStep 8005027 = 12007541) B12007541
theorem B10673369 : Blo 2107435 10673369 := bstep (se 2 (by rfl) ⟨4002513, by rfl⟩ : syracuseStep 10673369 = 8005027) B8005027
theorem B7115579 : Blo 2107435 7115579 := bstep (se 1 (by rfl) ⟨5336684, by rfl⟩ : syracuseStep 7115579 = 10673369) B10673369
theorem B4743719 : Blo 2107435 4743719 := bstep (se 1 (by rfl) ⟨3557789, by rfl⟩ : syracuseStep 4743719 = 7115579) B7115579
theorem B3162479 : Blo 2107435 3162479 := bstep (se 1 (by rfl) ⟨2371859, by rfl⟩ : syracuseStep 3162479 = 4743719) B4743719
theorem B2108319 : Blo 2107435 2108319 := bstep (se 1 (by rfl) ⟨1581239, by rfl⟩ : syracuseStep 2108319 = 3162479) B3162479
theorem B3162485 : Blo 2107435 3162485 := bbase (se 5 (by rfl) ⟨148241, by rfl⟩ : syracuseStep 3162485 = 296483) (by norm_num)
theorem B2108323 : Blo 2107435 2108323 := bstep (se 1 (by rfl) ⟨1581242, by rfl⟩ : syracuseStep 2108323 = 3162485) B3162485
theorem B19233845 : Blo 2107435 19233845 := bbase (se 5 (by rfl) ⟨901586, by rfl⟩ : syracuseStep 19233845 = 1803173) (by norm_num)
theorem B12822563 : Blo 2107435 12822563 := bstep (se 1 (by rfl) ⟨9616922, by rfl⟩ : syracuseStep 12822563 = 19233845) B19233845
theorem B8548375 : Blo 2107435 8548375 := bstep (se 1 (by rfl) ⟨6411281, by rfl⟩ : syracuseStep 8548375 = 12822563) B12822563
theorem B11397833 : Blo 2107435 11397833 := bstep (se 2 (by rfl) ⟨4274187, by rfl⟩ : syracuseStep 11397833 = 8548375) B8548375
theorem B7598555 : Blo 2107435 7598555 := bstep (se 1 (by rfl) ⟨5698916, by rfl⟩ : syracuseStep 7598555 = 11397833) B11397833
theorem B5065703 : Blo 2107435 5065703 := bstep (se 1 (by rfl) ⟨3799277, by rfl⟩ : syracuseStep 5065703 = 7598555) B7598555
theorem B3377135 : Blo 2107435 3377135 := bstep (se 1 (by rfl) ⟨2532851, by rfl⟩ : syracuseStep 3377135 = 5065703) B5065703
theorem B2251423 : Blo 2107435 2251423 := bstep (se 1 (by rfl) ⟨1688567, by rfl⟩ : syracuseStep 2251423 = 3377135) B3377135
theorem B3001897 : Blo 2107435 3001897 := bstep (se 2 (by rfl) ⟨1125711, by rfl⟩ : syracuseStep 3001897 = 2251423) B2251423
theorem B4002529 : Blo 2107435 4002529 := bstep (se 2 (by rfl) ⟨1500948, by rfl⟩ : syracuseStep 4002529 = 3001897) B3001897
theorem B5336705 : Blo 2107435 5336705 := bstep (se 2 (by rfl) ⟨2001264, by rfl⟩ : syracuseStep 5336705 = 4002529) B4002529
theorem B3557803 : Blo 2107435 3557803 := bstep (se 1 (by rfl) ⟨2668352, by rfl⟩ : syracuseStep 3557803 = 5336705) B5336705
theorem B4743737 : Blo 2107435 4743737 := bstep (se 2 (by rfl) ⟨1778901, by rfl⟩ : syracuseStep 4743737 = 3557803) B3557803
theorem B3162491 : Blo 2107435 3162491 := bstep (se 1 (by rfl) ⟨2371868, by rfl⟩ : syracuseStep 3162491 = 4743737) B4743737
theorem B2108327 : Blo 2107435 2108327 := bstep (se 1 (by rfl) ⟨1581245, by rfl⟩ : syracuseStep 2108327 = 3162491) B3162491
theorem B2371873 : Blo 2107435 2371873 := bbase (se 2 (by rfl) ⟨889452, by rfl⟩ : syracuseStep 2371873 = 1778905) (by norm_num)
theorem B3162497 : Blo 2107435 3162497 := bstep (se 2 (by rfl) ⟨1185936, by rfl⟩ : syracuseStep 3162497 = 2371873) B2371873
theorem B2108331 : Blo 2107435 2108331 := bstep (se 1 (by rfl) ⟨1581248, by rfl⟩ : syracuseStep 2108331 = 3162497) B3162497
theorem B5336725 : Blo 2107435 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B7115633 : Blo 2107435 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B4743755 : Blo 2107435 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B3162503 : Blo 2107435 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B2108335 : Blo 2107435 2108335 := bstep (se 1 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 2108335 = 3162503) B3162503
theorem B3162509 : Blo 2107435 3162509 := bbase (se 3 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 3162509 = 1185941) (by norm_num)
theorem B2108339 : Blo 2107435 2108339 := bstep (se 1 (by rfl) ⟨1581254, by rfl⟩ : syracuseStep 2108339 = 3162509) B3162509
theorem B4743773 : Blo 2107435 4743773 := bbase (se 3 (by rfl) ⟨889457, by rfl⟩ : syracuseStep 4743773 = 1778915) (by norm_num)
theorem B3162515 : Blo 2107435 3162515 := bstep (se 1 (by rfl) ⟨2371886, by rfl⟩ : syracuseStep 3162515 = 4743773) B4743773
theorem B2108343 : Blo 2107435 2108343 := bstep (se 1 (by rfl) ⟨1581257, by rfl⟩ : syracuseStep 2108343 = 3162515) B3162515
theorem B3557837 : Blo 2107435 3557837 := bbase (se 3 (by rfl) ⟨667094, by rfl⟩ : syracuseStep 3557837 = 1334189) (by norm_num)
theorem B2371891 : Blo 2107435 2371891 := bstep (se 1 (by rfl) ⟨1778918, by rfl⟩ : syracuseStep 2371891 = 3557837) B3557837
theorem B3162521 : Blo 2107435 3162521 := bstep (se 2 (by rfl) ⟨1185945, by rfl⟩ : syracuseStep 3162521 = 2371891) B2371891
theorem B2108347 : Blo 2107435 2108347 := bstep (se 1 (by rfl) ⟨1581260, by rfl⟩ : syracuseStep 2108347 = 3162521) B3162521
theorem B8548469 : Blo 2107435 8548469 := bbase (se 5 (by rfl) ⟨400709, by rfl⟩ : syracuseStep 8548469 = 801419) (by norm_num)
theorem B5698979 : Blo 2107435 5698979 := bstep (se 1 (by rfl) ⟨4274234, by rfl⟩ : syracuseStep 5698979 = 8548469) B8548469
theorem B3799319 : Blo 2107435 3799319 := bstep (se 1 (by rfl) ⟨2849489, by rfl⟩ : syracuseStep 3799319 = 5698979) B5698979
theorem B10131517 : Blo 2107435 10131517 := bstep (se 3 (by rfl) ⟨1899659, by rfl⟩ : syracuseStep 10131517 = 3799319) B3799319
theorem B13508689 : Blo 2107435 13508689 := bstep (se 2 (by rfl) ⟨5065758, by rfl⟩ : syracuseStep 13508689 = 10131517) B10131517
theorem B18011585 : Blo 2107435 18011585 := bstep (se 2 (by rfl) ⟨6754344, by rfl⟩ : syracuseStep 18011585 = 13508689) B13508689
theorem B12007723 : Blo 2107435 12007723 := bstep (se 1 (by rfl) ⟨9005792, by rfl⟩ : syracuseStep 12007723 = 18011585) B18011585
theorem B16010297 : Blo 2107435 16010297 := bstep (se 2 (by rfl) ⟨6003861, by rfl⟩ : syracuseStep 16010297 = 12007723) B12007723
theorem B10673531 : Blo 2107435 10673531 := bstep (se 1 (by rfl) ⟨8005148, by rfl⟩ : syracuseStep 10673531 = 16010297) B16010297
theorem B7115687 : Blo 2107435 7115687 := bstep (se 1 (by rfl) ⟨5336765, by rfl⟩ : syracuseStep 7115687 = 10673531) B10673531
theorem B4743791 : Blo 2107435 4743791 := bstep (se 1 (by rfl) ⟨3557843, by rfl⟩ : syracuseStep 4743791 = 7115687) B7115687
theorem B3162527 : Blo 2107435 3162527 := bstep (se 1 (by rfl) ⟨2371895, by rfl⟩ : syracuseStep 3162527 = 4743791) B4743791
theorem B2108351 : Blo 2107435 2108351 := bstep (se 1 (by rfl) ⟨1581263, by rfl⟩ : syracuseStep 2108351 = 3162527) B3162527
theorem B3162533 : Blo 2107435 3162533 := bbase (se 4 (by rfl) ⟨296487, by rfl⟩ : syracuseStep 3162533 = 592975) (by norm_num)
theorem B2108355 : Blo 2107435 2108355 := bstep (se 1 (by rfl) ⟨1581266, by rfl⟩ : syracuseStep 2108355 = 3162533) B3162533
theorem B2668393 : Blo 2107435 2668393 := bbase (se 2 (by rfl) ⟨1000647, by rfl⟩ : syracuseStep 2668393 = 2001295) (by norm_num)
theorem B3557857 : Blo 2107435 3557857 := bstep (se 2 (by rfl) ⟨1334196, by rfl⟩ : syracuseStep 3557857 = 2668393) B2668393
theorem B4743809 : Blo 2107435 4743809 := bstep (se 2 (by rfl) ⟨1778928, by rfl⟩ : syracuseStep 4743809 = 3557857) B3557857
theorem B3162539 : Blo 2107435 3162539 := bstep (se 1 (by rfl) ⟨2371904, by rfl⟩ : syracuseStep 3162539 = 4743809) B4743809
theorem B2108359 : Blo 2107435 2108359 := bstep (se 1 (by rfl) ⟨1581269, by rfl⟩ : syracuseStep 2108359 = 3162539) B3162539
theorem B2371909 : Blo 2107435 2371909 := bbase (se 4 (by rfl) ⟨222366, by rfl⟩ : syracuseStep 2371909 = 444733) (by norm_num)
theorem B3162545 : Blo 2107435 3162545 := bstep (se 2 (by rfl) ⟨1185954, by rfl⟩ : syracuseStep 3162545 = 2371909) B2371909
theorem B2108363 : Blo 2107435 2108363 := bstep (se 1 (by rfl) ⟨1581272, by rfl⟩ : syracuseStep 2108363 = 3162545) B3162545
theorem B4002605 : Blo 2107435 4002605 := bbase (se 3 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 4002605 = 1500977) (by norm_num)
theorem B2668403 : Blo 2107435 2668403 := bstep (se 1 (by rfl) ⟨2001302, by rfl⟩ : syracuseStep 2668403 = 4002605) B4002605
theorem B7115741 : Blo 2107435 7115741 := bstep (se 3 (by rfl) ⟨1334201, by rfl⟩ : syracuseStep 7115741 = 2668403) B2668403
theorem B4743827 : Blo 2107435 4743827 := bstep (se 1 (by rfl) ⟨3557870, by rfl⟩ : syracuseStep 4743827 = 7115741) B7115741
theorem B3162551 : Blo 2107435 3162551 := bstep (se 1 (by rfl) ⟨2371913, by rfl⟩ : syracuseStep 3162551 = 4743827) B4743827
theorem B2108367 : Blo 2107435 2108367 := bstep (se 1 (by rfl) ⟨1581275, by rfl⟩ : syracuseStep 2108367 = 3162551) B3162551
theorem B3162557 : Blo 2107435 3162557 := bbase (se 3 (by rfl) ⟨592979, by rfl⟩ : syracuseStep 3162557 = 1185959) (by norm_num)
theorem B2108371 : Blo 2107435 2108371 := bstep (se 1 (by rfl) ⟨1581278, by rfl⟩ : syracuseStep 2108371 = 3162557) B3162557
theorem B4743845 : Blo 2107435 4743845 := bbase (se 4 (by rfl) ⟨444735, by rfl⟩ : syracuseStep 4743845 = 889471) (by norm_num)
theorem B3162563 : Blo 2107435 3162563 := bstep (se 1 (by rfl) ⟨2371922, by rfl⟩ : syracuseStep 3162563 = 4743845) B4743845
theorem B2108375 : Blo 2107435 2108375 := bstep (se 1 (by rfl) ⟨1581281, by rfl⟩ : syracuseStep 2108375 = 3162563) B3162563
theorem B5336837 : Blo 2107435 5336837 := bbase (se 4 (by rfl) ⟨500328, by rfl⟩ : syracuseStep 5336837 = 1000657) (by norm_num)
theorem B3557891 : Blo 2107435 3557891 := bstep (se 1 (by rfl) ⟨2668418, by rfl⟩ : syracuseStep 3557891 = 5336837) B5336837
theorem B2371927 : Blo 2107435 2371927 := bstep (se 1 (by rfl) ⟨1778945, by rfl⟩ : syracuseStep 2371927 = 3557891) B3557891
theorem B3162569 : Blo 2107435 3162569 := bstep (se 2 (by rfl) ⟨1185963, by rfl⟩ : syracuseStep 3162569 = 2371927) B2371927
theorem B2108379 : Blo 2107435 2108379 := bstep (se 1 (by rfl) ⟨1581284, by rfl⟩ : syracuseStep 2108379 = 3162569) B3162569
theorem B4502965 : Blo 2107435 4502965 := bbase (se 5 (by rfl) ⟨211076, by rfl⟩ : syracuseStep 4502965 = 422153) (by norm_num)
theorem B6003953 : Blo 2107435 6003953 := bstep (se 2 (by rfl) ⟨2251482, by rfl⟩ : syracuseStep 6003953 = 4502965) B4502965
theorem B4002635 : Blo 2107435 4002635 := bstep (se 1 (by rfl) ⟨3001976, by rfl⟩ : syracuseStep 4002635 = 6003953) B6003953
theorem B10673693 : Blo 2107435 10673693 := bstep (se 3 (by rfl) ⟨2001317, by rfl⟩ : syracuseStep 10673693 = 4002635) B4002635
theorem B7115795 : Blo 2107435 7115795 := bstep (se 1 (by rfl) ⟨5336846, by rfl⟩ : syracuseStep 7115795 = 10673693) B10673693
theorem B4743863 : Blo 2107435 4743863 := bstep (se 1 (by rfl) ⟨3557897, by rfl⟩ : syracuseStep 4743863 = 7115795) B7115795
theorem B3162575 : Blo 2107435 3162575 := bstep (se 1 (by rfl) ⟨2371931, by rfl⟩ : syracuseStep 3162575 = 4743863) B4743863
theorem B2108383 : Blo 2107435 2108383 := bstep (se 1 (by rfl) ⟨1581287, by rfl⟩ : syracuseStep 2108383 = 3162575) B3162575
theorem B3162581 : Blo 2107435 3162581 := bbase (se 7 (by rfl) ⟨37061, by rfl⟩ : syracuseStep 3162581 = 74123) (by norm_num)
theorem B2108387 : Blo 2107435 2108387 := bstep (se 1 (by rfl) ⟨1581290, by rfl⟩ : syracuseStep 2108387 = 3162581) B3162581
theorem B8005301 : Blo 2107435 8005301 := bbase (se 5 (by rfl) ⟨375248, by rfl⟩ : syracuseStep 8005301 = 750497) (by norm_num)
theorem B5336867 : Blo 2107435 5336867 := bstep (se 1 (by rfl) ⟨4002650, by rfl⟩ : syracuseStep 5336867 = 8005301) B8005301
theorem B3557911 : Blo 2107435 3557911 := bstep (se 1 (by rfl) ⟨2668433, by rfl⟩ : syracuseStep 3557911 = 5336867) B5336867
theorem B4743881 : Blo 2107435 4743881 := bstep (se 2 (by rfl) ⟨1778955, by rfl⟩ : syracuseStep 4743881 = 3557911) B3557911
theorem B3162587 : Blo 2107435 3162587 := bstep (se 1 (by rfl) ⟨2371940, by rfl⟩ : syracuseStep 3162587 = 4743881) B4743881
theorem B2108391 : Blo 2107435 2108391 := bstep (se 1 (by rfl) ⟨1581293, by rfl⟩ : syracuseStep 2108391 = 3162587) B3162587
theorem B2371945 : Blo 2107435 2371945 := bbase (se 2 (by rfl) ⟨889479, by rfl⟩ : syracuseStep 2371945 = 1778959) (by norm_num)
theorem B3162593 : Blo 2107435 3162593 := bstep (se 2 (by rfl) ⟨1185972, by rfl⟩ : syracuseStep 3162593 = 2371945) B2371945
theorem B2108395 : Blo 2107435 2108395 := bstep (se 1 (by rfl) ⟨1581296, by rfl⟩ : syracuseStep 2108395 = 3162593) B3162593
theorem B10131749 : Blo 2107435 10131749 := bbase (se 4 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 10131749 = 1899703) (by norm_num)
theorem B6754499 : Blo 2107435 6754499 := bstep (se 1 (by rfl) ⟨5065874, by rfl⟩ : syracuseStep 6754499 = 10131749) B10131749
theorem B4502999 : Blo 2107435 4502999 := bstep (se 1 (by rfl) ⟨3377249, by rfl⟩ : syracuseStep 4502999 = 6754499) B6754499
theorem B12007997 : Blo 2107435 12007997 := bstep (se 3 (by rfl) ⟨2251499, by rfl⟩ : syracuseStep 12007997 = 4502999) B4502999
theorem B8005331 : Blo 2107435 8005331 := bstep (se 1 (by rfl) ⟨6003998, by rfl⟩ : syracuseStep 8005331 = 12007997) B12007997
theorem B5336887 : Blo 2107435 5336887 := bstep (se 1 (by rfl) ⟨4002665, by rfl⟩ : syracuseStep 5336887 = 8005331) B8005331
theorem B7115849 : Blo 2107435 7115849 := bstep (se 2 (by rfl) ⟨2668443, by rfl⟩ : syracuseStep 7115849 = 5336887) B5336887
theorem B4743899 : Blo 2107435 4743899 := bstep (se 1 (by rfl) ⟨3557924, by rfl⟩ : syracuseStep 4743899 = 7115849) B7115849
theorem B3162599 : Blo 2107435 3162599 := bstep (se 1 (by rfl) ⟨2371949, by rfl⟩ : syracuseStep 3162599 = 4743899) B4743899
theorem B2108399 : Blo 2107435 2108399 := bstep (se 1 (by rfl) ⟨1581299, by rfl⟩ : syracuseStep 2108399 = 3162599) B3162599
theorem B3162605 : Blo 2107435 3162605 := bbase (se 3 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 3162605 = 1185977) (by norm_num)
theorem B2108403 : Blo 2107435 2108403 := bstep (se 1 (by rfl) ⟨1581302, by rfl⟩ : syracuseStep 2108403 = 3162605) B3162605
theorem B4743917 : Blo 2107435 4743917 := bbase (se 3 (by rfl) ⟨889484, by rfl⟩ : syracuseStep 4743917 = 1778969) (by norm_num)
theorem B3162611 : Blo 2107435 3162611 := bstep (se 1 (by rfl) ⟨2371958, by rfl⟩ : syracuseStep 3162611 = 4743917) B4743917
theorem B2108407 : Blo 2107435 2108407 := bstep (se 1 (by rfl) ⟨1581305, by rfl⟩ : syracuseStep 2108407 = 3162611) B3162611
theorem B2251513 : Blo 2107435 2251513 := bbase (se 2 (by rfl) ⟨844317, by rfl⟩ : syracuseStep 2251513 = 1688635) (by norm_num)
theorem B3002017 : Blo 2107435 3002017 := bstep (se 2 (by rfl) ⟨1125756, by rfl⟩ : syracuseStep 3002017 = 2251513) B2251513
theorem B4002689 : Blo 2107435 4002689 := bstep (se 2 (by rfl) ⟨1501008, by rfl⟩ : syracuseStep 4002689 = 3002017) B3002017
theorem B2668459 : Blo 2107435 2668459 := bstep (se 1 (by rfl) ⟨2001344, by rfl⟩ : syracuseStep 2668459 = 4002689) B4002689
theorem B3557945 : Blo 2107435 3557945 := bstep (se 2 (by rfl) ⟨1334229, by rfl⟩ : syracuseStep 3557945 = 2668459) B2668459
theorem B2371963 : Blo 2107435 2371963 := bstep (se 1 (by rfl) ⟨1778972, by rfl⟩ : syracuseStep 2371963 = 3557945) B3557945
theorem B3162617 : Blo 2107435 3162617 := bstep (se 2 (by rfl) ⟨1185981, by rfl⟩ : syracuseStep 3162617 = 2371963) B2371963
theorem B2108411 : Blo 2107435 2108411 := bstep (se 1 (by rfl) ⟨1581308, by rfl⟩ : syracuseStep 2108411 = 3162617) B3162617
theorem B86555861 : Blo 2107435 86555861 := bbase (se 7 (by rfl) ⟨1014326, by rfl⟩ : syracuseStep 86555861 = 2028653) (by norm_num)
theorem B57703907 : Blo 2107435 57703907 := bstep (se 1 (by rfl) ⟨43277930, by rfl⟩ : syracuseStep 57703907 = 86555861) B86555861
theorem B38469271 : Blo 2107435 38469271 := bstep (se 1 (by rfl) ⟨28851953, by rfl⟩ : syracuseStep 38469271 = 57703907) B57703907
theorem B51292361 : Blo 2107435 51292361 := bstep (se 2 (by rfl) ⟨19234635, by rfl⟩ : syracuseStep 51292361 = 38469271) B38469271
theorem B34194907 : Blo 2107435 34194907 := bstep (se 1 (by rfl) ⟨25646180, by rfl⟩ : syracuseStep 34194907 = 51292361) B51292361
theorem B45593209 : Blo 2107435 45593209 := bstep (se 2 (by rfl) ⟨17097453, by rfl⟩ : syracuseStep 45593209 = 34194907) B34194907
theorem B60790945 : Blo 2107435 60790945 := bstep (se 2 (by rfl) ⟨22796604, by rfl⟩ : syracuseStep 60790945 = 45593209) B45593209
theorem B81054593 : Blo 2107435 81054593 := bstep (se 2 (by rfl) ⟨30395472, by rfl⟩ : syracuseStep 81054593 = 60790945) B60790945
theorem B54036395 : Blo 2107435 54036395 := bstep (se 1 (by rfl) ⟨40527296, by rfl⟩ : syracuseStep 54036395 = 81054593) B81054593
theorem B36024263 : Blo 2107435 36024263 := bstep (se 1 (by rfl) ⟨27018197, by rfl⟩ : syracuseStep 36024263 = 54036395) B54036395
theorem B24016175 : Blo 2107435 24016175 := bstep (se 1 (by rfl) ⟨18012131, by rfl⟩ : syracuseStep 24016175 = 36024263) B36024263
theorem B16010783 : Blo 2107435 16010783 := bstep (se 1 (by rfl) ⟨12008087, by rfl⟩ : syracuseStep 16010783 = 24016175) B24016175
theorem B10673855 : Blo 2107435 10673855 := bstep (se 1 (by rfl) ⟨8005391, by rfl⟩ : syracuseStep 10673855 = 16010783) B16010783
theorem B7115903 : Blo 2107435 7115903 := bstep (se 1 (by rfl) ⟨5336927, by rfl⟩ : syracuseStep 7115903 = 10673855) B10673855
theorem B4743935 : Blo 2107435 4743935 := bstep (se 1 (by rfl) ⟨3557951, by rfl⟩ : syracuseStep 4743935 = 7115903) B7115903
theorem B3162623 : Blo 2107435 3162623 := bstep (se 1 (by rfl) ⟨2371967, by rfl⟩ : syracuseStep 3162623 = 4743935) B4743935
theorem B2108415 : Blo 2107435 2108415 := bstep (se 1 (by rfl) ⟨1581311, by rfl⟩ : syracuseStep 2108415 = 3162623) B3162623
theorem B3162629 : Blo 2107435 3162629 := bbase (se 4 (by rfl) ⟨296496, by rfl⟩ : syracuseStep 3162629 = 592993) (by norm_num)
theorem B2108419 : Blo 2107435 2108419 := bstep (se 1 (by rfl) ⟨1581314, by rfl⟩ : syracuseStep 2108419 = 3162629) B3162629
theorem B3557965 : Blo 2107435 3557965 := bbase (se 3 (by rfl) ⟨667118, by rfl⟩ : syracuseStep 3557965 = 1334237) (by norm_num)
theorem B4743953 : Blo 2107435 4743953 := bstep (se 2 (by rfl) ⟨1778982, by rfl⟩ : syracuseStep 4743953 = 3557965) B3557965
theorem B3162635 : Blo 2107435 3162635 := bstep (se 1 (by rfl) ⟨2371976, by rfl⟩ : syracuseStep 3162635 = 4743953) B4743953
theorem B2108423 : Blo 2107435 2108423 := bstep (se 1 (by rfl) ⟨1581317, by rfl⟩ : syracuseStep 2108423 = 3162635) B3162635
theorem B2371981 : Blo 2107435 2371981 := bbase (se 3 (by rfl) ⟨444746, by rfl⟩ : syracuseStep 2371981 = 889493) (by norm_num)
theorem B3162641 : Blo 2107435 3162641 := bstep (se 2 (by rfl) ⟨1185990, by rfl⟩ : syracuseStep 3162641 = 2371981) B2371981
theorem B2108427 : Blo 2107435 2108427 := bstep (se 1 (by rfl) ⟨1581320, by rfl⟩ : syracuseStep 2108427 = 3162641) B3162641
theorem B7115957 : Blo 2107435 7115957 := bbase (se 5 (by rfl) ⟨333560, by rfl⟩ : syracuseStep 7115957 = 667121) (by norm_num)
theorem B4743971 : Blo 2107435 4743971 := bstep (se 1 (by rfl) ⟨3557978, by rfl⟩ : syracuseStep 4743971 = 7115957) B7115957
theorem B3162647 : Blo 2107435 3162647 := bstep (se 1 (by rfl) ⟨2371985, by rfl⟩ : syracuseStep 3162647 = 4743971) B4743971
theorem B2108431 : Blo 2107435 2108431 := bstep (se 1 (by rfl) ⟨1581323, by rfl⟩ : syracuseStep 2108431 = 3162647) B3162647
theorem B3162653 : Blo 2107435 3162653 := bbase (se 3 (by rfl) ⟨592997, by rfl⟩ : syracuseStep 3162653 = 1185995) (by norm_num)
theorem B2108435 : Blo 2107435 2108435 := bstep (se 1 (by rfl) ⟨1581326, by rfl⟩ : syracuseStep 2108435 = 3162653) B3162653
theorem B4743989 : Blo 2107435 4743989 := bbase (se 5 (by rfl) ⟨222374, by rfl⟩ : syracuseStep 4743989 = 444749) (by norm_num)
theorem B3162659 : Blo 2107435 3162659 := bstep (se 1 (by rfl) ⟨2371994, by rfl⟩ : syracuseStep 3162659 = 4743989) B4743989
theorem B2108439 : Blo 2107435 2108439 := bstep (se 1 (by rfl) ⟨1581329, by rfl⟩ : syracuseStep 2108439 = 3162659) B3162659
theorem B58491989 : Blo 2107435 58491989 := bbase (se 8 (by rfl) ⟨342726, by rfl⟩ : syracuseStep 58491989 = 685453) (by norm_num)
theorem B38994659 : Blo 2107435 38994659 := bstep (se 1 (by rfl) ⟨29245994, by rfl⟩ : syracuseStep 38994659 = 58491989) B58491989
theorem B25996439 : Blo 2107435 25996439 := bstep (se 1 (by rfl) ⟨19497329, by rfl⟩ : syracuseStep 25996439 = 38994659) B38994659
theorem B17330959 : Blo 2107435 17330959 := bstep (se 1 (by rfl) ⟨12998219, by rfl⟩ : syracuseStep 17330959 = 25996439) B25996439
theorem B23107945 : Blo 2107435 23107945 := bstep (se 2 (by rfl) ⟨8665479, by rfl⟩ : syracuseStep 23107945 = 17330959) B17330959
theorem B30810593 : Blo 2107435 30810593 := bstep (se 2 (by rfl) ⟨11553972, by rfl⟩ : syracuseStep 30810593 = 23107945) B23107945
theorem B20540395 : Blo 2107435 20540395 := bstep (se 1 (by rfl) ⟨15405296, by rfl⟩ : syracuseStep 20540395 = 30810593) B30810593
theorem B27387193 : Blo 2107435 27387193 := bstep (se 2 (by rfl) ⟨10270197, by rfl⟩ : syracuseStep 27387193 = 20540395) B20540395
theorem B36516257 : Blo 2107435 36516257 := bstep (se 2 (by rfl) ⟨13693596, by rfl⟩ : syracuseStep 36516257 = 27387193) B27387193
theorem B24344171 : Blo 2107435 24344171 := bstep (se 1 (by rfl) ⟨18258128, by rfl⟩ : syracuseStep 24344171 = 36516257) B36516257
theorem B16229447 : Blo 2107435 16229447 := bstep (se 1 (by rfl) ⟨12172085, by rfl⟩ : syracuseStep 16229447 = 24344171) B24344171
theorem B10819631 : Blo 2107435 10819631 := bstep (se 1 (by rfl) ⟨8114723, by rfl⟩ : syracuseStep 10819631 = 16229447) B16229447
theorem B7213087 : Blo 2107435 7213087 := bstep (se 1 (by rfl) ⟨5409815, by rfl⟩ : syracuseStep 7213087 = 10819631) B10819631
theorem B9617449 : Blo 2107435 9617449 := bstep (se 2 (by rfl) ⟨3606543, by rfl⟩ : syracuseStep 9617449 = 7213087) B7213087
theorem B12823265 : Blo 2107435 12823265 := bstep (se 2 (by rfl) ⟨4808724, by rfl⟩ : syracuseStep 12823265 = 9617449) B9617449
theorem B8548843 : Blo 2107435 8548843 := bstep (se 1 (by rfl) ⟨6411632, by rfl⟩ : syracuseStep 8548843 = 12823265) B12823265
theorem B11398457 : Blo 2107435 11398457 := bstep (se 2 (by rfl) ⟨4274421, by rfl⟩ : syracuseStep 11398457 = 8548843) B8548843
theorem B7598971 : Blo 2107435 7598971 := bstep (se 1 (by rfl) ⟨5699228, by rfl⟩ : syracuseStep 7598971 = 11398457) B11398457
theorem B10131961 : Blo 2107435 10131961 := bstep (se 2 (by rfl) ⟨3799485, by rfl⟩ : syracuseStep 10131961 = 7598971) B7598971
theorem B13509281 : Blo 2107435 13509281 := bstep (se 2 (by rfl) ⟨5065980, by rfl⟩ : syracuseStep 13509281 = 10131961) B10131961
theorem B9006187 : Blo 2107435 9006187 := bstep (se 1 (by rfl) ⟨6754640, by rfl⟩ : syracuseStep 9006187 = 13509281) B13509281
theorem B12008249 : Blo 2107435 12008249 := bstep (se 2 (by rfl) ⟨4503093, by rfl⟩ : syracuseStep 12008249 = 9006187) B9006187
theorem B8005499 : Blo 2107435 8005499 := bstep (se 1 (by rfl) ⟨6004124, by rfl⟩ : syracuseStep 8005499 = 12008249) B12008249
theorem B5336999 : Blo 2107435 5336999 := bstep (se 1 (by rfl) ⟨4002749, by rfl⟩ : syracuseStep 5336999 = 8005499) B8005499
theorem B3557999 : Blo 2107435 3557999 := bstep (se 1 (by rfl) ⟨2668499, by rfl⟩ : syracuseStep 3557999 = 5336999) B5336999
theorem B2371999 : Blo 2107435 2371999 := bstep (se 1 (by rfl) ⟨1778999, by rfl⟩ : syracuseStep 2371999 = 3557999) B3557999
theorem B3162665 : Blo 2107435 3162665 := bstep (se 2 (by rfl) ⟨1185999, by rfl⟩ : syracuseStep 3162665 = 2371999) B2371999
theorem B2108443 : Blo 2107435 2108443 := bstep (se 1 (by rfl) ⟨1581332, by rfl⟩ : syracuseStep 2108443 = 3162665) B3162665
theorem B4274429 : Blo 2107435 4274429 := bbase (se 3 (by rfl) ⟨801455, by rfl⟩ : syracuseStep 4274429 = 1602911) (by norm_num)
theorem B11398477 : Blo 2107435 11398477 := bstep (se 3 (by rfl) ⟨2137214, by rfl⟩ : syracuseStep 11398477 = 4274429) B4274429
theorem B15197969 : Blo 2107435 15197969 := bstep (se 2 (by rfl) ⟨5699238, by rfl⟩ : syracuseStep 15197969 = 11398477) B11398477
theorem B10131979 : Blo 2107435 10131979 := bstep (se 1 (by rfl) ⟨7598984, by rfl⟩ : syracuseStep 10131979 = 15197969) B15197969
theorem B13509305 : Blo 2107435 13509305 := bstep (se 2 (by rfl) ⟨5065989, by rfl⟩ : syracuseStep 13509305 = 10131979) B10131979
theorem B9006203 : Blo 2107435 9006203 := bstep (se 1 (by rfl) ⟨6754652, by rfl⟩ : syracuseStep 9006203 = 13509305) B13509305
theorem B6004135 : Blo 2107435 6004135 := bstep (se 1 (by rfl) ⟨4503101, by rfl⟩ : syracuseStep 6004135 = 9006203) B9006203
theorem B8005513 : Blo 2107435 8005513 := bstep (se 2 (by rfl) ⟨3002067, by rfl⟩ : syracuseStep 8005513 = 6004135) B6004135
theorem B10674017 : Blo 2107435 10674017 := bstep (se 2 (by rfl) ⟨4002756, by rfl⟩ : syracuseStep 10674017 = 8005513) B8005513
theorem B7116011 : Blo 2107435 7116011 := bstep (se 1 (by rfl) ⟨5337008, by rfl⟩ : syracuseStep 7116011 = 10674017) B10674017
theorem B4744007 : Blo 2107435 4744007 := bstep (se 1 (by rfl) ⟨3558005, by rfl⟩ : syracuseStep 4744007 = 7116011) B7116011
theorem B3162671 : Blo 2107435 3162671 := bstep (se 1 (by rfl) ⟨2372003, by rfl⟩ : syracuseStep 3162671 = 4744007) B4744007
theorem B2108447 : Blo 2107435 2108447 := bstep (se 1 (by rfl) ⟨1581335, by rfl⟩ : syracuseStep 2108447 = 3162671) B3162671
theorem B3162677 : Blo 2107435 3162677 := bbase (se 5 (by rfl) ⟨148250, by rfl⟩ : syracuseStep 3162677 = 296501) (by norm_num)
theorem B2108451 : Blo 2107435 2108451 := bstep (se 1 (by rfl) ⟨1581338, by rfl⟩ : syracuseStep 2108451 = 3162677) B3162677
theorem B5337029 : Blo 2107435 5337029 := bbase (se 4 (by rfl) ⟨500346, by rfl⟩ : syracuseStep 5337029 = 1000693) (by norm_num)
theorem B3558019 : Blo 2107435 3558019 := bstep (se 1 (by rfl) ⟨2668514, by rfl⟩ : syracuseStep 3558019 = 5337029) B5337029
theorem B4744025 : Blo 2107435 4744025 := bstep (se 2 (by rfl) ⟨1779009, by rfl⟩ : syracuseStep 4744025 = 3558019) B3558019
theorem B3162683 : Blo 2107435 3162683 := bstep (se 1 (by rfl) ⟨2372012, by rfl⟩ : syracuseStep 3162683 = 4744025) B4744025
theorem B2108455 : Blo 2107435 2108455 := bstep (se 1 (by rfl) ⟨1581341, by rfl⟩ : syracuseStep 2108455 = 3162683) B3162683
theorem B2372017 : Blo 2107435 2372017 := bbase (se 2 (by rfl) ⟨889506, by rfl⟩ : syracuseStep 2372017 = 1779013) (by norm_num)
theorem B3162689 : Blo 2107435 3162689 := bstep (se 2 (by rfl) ⟨1186008, by rfl⟩ : syracuseStep 3162689 = 2372017) B2372017
theorem B2108459 : Blo 2107435 2108459 := bstep (se 1 (by rfl) ⟨1581344, by rfl⟩ : syracuseStep 2108459 = 3162689) B3162689
theorem B6004181 : Blo 2107435 6004181 := bbase (se 7 (by rfl) ⟨70361, by rfl⟩ : syracuseStep 6004181 = 140723) (by norm_num)
theorem B4002787 : Blo 2107435 4002787 := bstep (se 1 (by rfl) ⟨3002090, by rfl⟩ : syracuseStep 4002787 = 6004181) B6004181
theorem B5337049 : Blo 2107435 5337049 := bstep (se 2 (by rfl) ⟨2001393, by rfl⟩ : syracuseStep 5337049 = 4002787) B4002787
theorem B7116065 : Blo 2107435 7116065 := bstep (se 2 (by rfl) ⟨2668524, by rfl⟩ : syracuseStep 7116065 = 5337049) B5337049
theorem B4744043 : Blo 2107435 4744043 := bstep (se 1 (by rfl) ⟨3558032, by rfl⟩ : syracuseStep 4744043 = 7116065) B7116065
theorem B3162695 : Blo 2107435 3162695 := bstep (se 1 (by rfl) ⟨2372021, by rfl⟩ : syracuseStep 3162695 = 4744043) B4744043
theorem B2108463 : Blo 2107435 2108463 := bstep (se 1 (by rfl) ⟨1581347, by rfl⟩ : syracuseStep 2108463 = 3162695) B3162695
theorem B3162701 : Blo 2107435 3162701 := bbase (se 3 (by rfl) ⟨593006, by rfl⟩ : syracuseStep 3162701 = 1186013) (by norm_num)
theorem B2108467 : Blo 2107435 2108467 := bstep (se 1 (by rfl) ⟨1581350, by rfl⟩ : syracuseStep 2108467 = 3162701) B3162701
theorem B4744061 : Blo 2107435 4744061 := bbase (se 3 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 4744061 = 1779023) (by norm_num)
theorem B3162707 : Blo 2107435 3162707 := bstep (se 1 (by rfl) ⟨2372030, by rfl⟩ : syracuseStep 3162707 = 4744061) B4744061
theorem B2108471 : Blo 2107435 2108471 := bstep (se 1 (by rfl) ⟨1581353, by rfl⟩ : syracuseStep 2108471 = 3162707) B3162707
theorem B3558053 : Blo 2107435 3558053 := bbase (se 4 (by rfl) ⟨333567, by rfl⟩ : syracuseStep 3558053 = 667135) (by norm_num)
theorem B2372035 : Blo 2107435 2372035 := bstep (se 1 (by rfl) ⟨1779026, by rfl⟩ : syracuseStep 2372035 = 3558053) B3558053
theorem B3162713 : Blo 2107435 3162713 := bstep (se 2 (by rfl) ⟨1186017, by rfl⟩ : syracuseStep 3162713 = 2372035) B2372035
theorem B2108475 : Blo 2107435 2108475 := bstep (se 1 (by rfl) ⟨1581356, by rfl⟩ : syracuseStep 2108475 = 3162713) B3162713
theorem B2251585 : Blo 2107435 2251585 := bbase (se 2 (by rfl) ⟨844344, by rfl⟩ : syracuseStep 2251585 = 1688689) (by norm_num)
theorem B3002113 : Blo 2107435 3002113 := bstep (se 2 (by rfl) ⟨1125792, by rfl⟩ : syracuseStep 3002113 = 2251585) B2251585
theorem B16011269 : Blo 2107435 16011269 := bstep (se 4 (by rfl) ⟨1501056, by rfl⟩ : syracuseStep 16011269 = 3002113) B3002113
theorem B10674179 : Blo 2107435 10674179 := bstep (se 1 (by rfl) ⟨8005634, by rfl⟩ : syracuseStep 10674179 = 16011269) B16011269
theorem B7116119 : Blo 2107435 7116119 := bstep (se 1 (by rfl) ⟨5337089, by rfl⟩ : syracuseStep 7116119 = 10674179) B10674179
theorem B4744079 : Blo 2107435 4744079 := bstep (se 1 (by rfl) ⟨3558059, by rfl⟩ : syracuseStep 4744079 = 7116119) B7116119
theorem B3162719 : Blo 2107435 3162719 := bstep (se 1 (by rfl) ⟨2372039, by rfl⟩ : syracuseStep 3162719 = 4744079) B4744079
theorem B2108479 : Blo 2107435 2108479 := bstep (se 1 (by rfl) ⟨1581359, by rfl⟩ : syracuseStep 2108479 = 3162719) B3162719
theorem B3162725 : Blo 2107435 3162725 := bbase (se 4 (by rfl) ⟨296505, by rfl⟩ : syracuseStep 3162725 = 593011) (by norm_num)
theorem B2108483 : Blo 2107435 2108483 := bstep (se 1 (by rfl) ⟨1581362, by rfl⟩ : syracuseStep 2108483 = 3162725) B3162725
theorem B3002125 : Blo 2107435 3002125 := bbase (se 3 (by rfl) ⟨562898, by rfl⟩ : syracuseStep 3002125 = 1125797) (by norm_num)
theorem B4002833 : Blo 2107435 4002833 := bstep (se 2 (by rfl) ⟨1501062, by rfl⟩ : syracuseStep 4002833 = 3002125) B3002125
theorem B2668555 : Blo 2107435 2668555 := bstep (se 1 (by rfl) ⟨2001416, by rfl⟩ : syracuseStep 2668555 = 4002833) B4002833
theorem B3558073 : Blo 2107435 3558073 := bstep (se 2 (by rfl) ⟨1334277, by rfl⟩ : syracuseStep 3558073 = 2668555) B2668555
theorem B4744097 : Blo 2107435 4744097 := bstep (se 2 (by rfl) ⟨1779036, by rfl⟩ : syracuseStep 4744097 = 3558073) B3558073
theorem B3162731 : Blo 2107435 3162731 := bstep (se 1 (by rfl) ⟨2372048, by rfl⟩ : syracuseStep 3162731 = 4744097) B4744097
theorem B2108487 : Blo 2107435 2108487 := bstep (se 1 (by rfl) ⟨1581365, by rfl⟩ : syracuseStep 2108487 = 3162731) B3162731
theorem B2372053 : Blo 2107435 2372053 := bbase (se 7 (by rfl) ⟨27797, by rfl⟩ : syracuseStep 2372053 = 55595) (by norm_num)
theorem B3162737 : Blo 2107435 3162737 := bstep (se 2 (by rfl) ⟨1186026, by rfl⟩ : syracuseStep 3162737 = 2372053) B2372053
theorem B2108491 : Blo 2107435 2108491 := bstep (se 1 (by rfl) ⟨1581368, by rfl⟩ : syracuseStep 2108491 = 3162737) B3162737
theorem B2668565 : Blo 2107435 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B7116173 : Blo 2107435 7116173 := bstep (se 3 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 7116173 = 2668565) B2668565
theorem B4744115 : Blo 2107435 4744115 := bstep (se 1 (by rfl) ⟨3558086, by rfl⟩ : syracuseStep 4744115 = 7116173) B7116173
theorem B3162743 : Blo 2107435 3162743 := bstep (se 1 (by rfl) ⟨2372057, by rfl⟩ : syracuseStep 3162743 = 4744115) B4744115
theorem B2108495 : Blo 2107435 2108495 := bstep (se 1 (by rfl) ⟨1581371, by rfl⟩ : syracuseStep 2108495 = 3162743) B3162743
theorem B3162749 : Blo 2107435 3162749 := bbase (se 3 (by rfl) ⟨593015, by rfl⟩ : syracuseStep 3162749 = 1186031) (by norm_num)
theorem B2108499 : Blo 2107435 2108499 := bstep (se 1 (by rfl) ⟨1581374, by rfl⟩ : syracuseStep 2108499 = 3162749) B3162749
theorem B4744133 : Blo 2107435 4744133 := bbase (se 4 (by rfl) ⟨444762, by rfl⟩ : syracuseStep 4744133 = 889525) (by norm_num)
theorem B3162755 : Blo 2107435 3162755 := bstep (se 1 (by rfl) ⟨2372066, by rfl⟩ : syracuseStep 3162755 = 4744133) B4744133
theorem B2108503 : Blo 2107435 2108503 := bstep (se 1 (by rfl) ⟨1581377, by rfl⟩ : syracuseStep 2108503 = 3162755) B3162755
theorem B11398805 : Blo 2107435 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B7599203 : Blo 2107435 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B5066135 : Blo 2107435 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B3377423 : Blo 2107435 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B9006461 : Blo 2107435 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B6004307 : Blo 2107435 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B4002871 : Blo 2107435 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B5337161 : Blo 2107435 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B3558107 : Blo 2107435 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B2372071 : Blo 2107435 2372071 := bstep (se 1 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 2372071 = 3558107) B3558107
theorem B3162761 : Blo 2107435 3162761 := bstep (se 2 (by rfl) ⟨1186035, by rfl⟩ : syracuseStep 3162761 = 2372071) B2372071
theorem B2108507 : Blo 2107435 2108507 := bstep (se 1 (by rfl) ⟨1581380, by rfl⟩ : syracuseStep 2108507 = 3162761) B3162761
theorem B10674341 : Blo 2107435 10674341 := bbase (se 4 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 10674341 = 2001439) (by norm_num)
theorem B7116227 : Blo 2107435 7116227 := bstep (se 1 (by rfl) ⟨5337170, by rfl⟩ : syracuseStep 7116227 = 10674341) B10674341
theorem B4744151 : Blo 2107435 4744151 := bstep (se 1 (by rfl) ⟨3558113, by rfl⟩ : syracuseStep 4744151 = 7116227) B7116227
theorem B3162767 : Blo 2107435 3162767 := bstep (se 1 (by rfl) ⟨2372075, by rfl⟩ : syracuseStep 3162767 = 4744151) B4744151
theorem B2108511 : Blo 2107435 2108511 := bstep (se 1 (by rfl) ⟨1581383, by rfl⟩ : syracuseStep 2108511 = 3162767) B3162767
theorem B3162773 : Blo 2107435 3162773 := bbase (se 6 (by rfl) ⟨74127, by rfl⟩ : syracuseStep 3162773 = 148255) (by norm_num)
theorem B2108515 : Blo 2107435 2108515 := bstep (se 1 (by rfl) ⟨1581386, by rfl⟩ : syracuseStep 2108515 = 3162773) B3162773
theorem B2705005 : Blo 2107435 2705005 := bbase (se 3 (by rfl) ⟨507188, by rfl⟩ : syracuseStep 2705005 = 1014377) (by norm_num)
theorem B14426693 : Blo 2107435 14426693 := bstep (se 4 (by rfl) ⟨1352502, by rfl⟩ : syracuseStep 14426693 = 2705005) B2705005
theorem B9617795 : Blo 2107435 9617795 := bstep (se 1 (by rfl) ⟨7213346, by rfl⟩ : syracuseStep 9617795 = 14426693) B14426693
theorem B6411863 : Blo 2107435 6411863 := bstep (se 1 (by rfl) ⟨4808897, by rfl⟩ : syracuseStep 6411863 = 9617795) B9617795
theorem B4274575 : Blo 2107435 4274575 := bstep (se 1 (by rfl) ⟨3205931, by rfl⟩ : syracuseStep 4274575 = 6411863) B6411863
theorem B22797733 : Blo 2107435 22797733 := bstep (se 4 (by rfl) ⟨2137287, by rfl⟩ : syracuseStep 22797733 = 4274575) B4274575
theorem B30396977 : Blo 2107435 30396977 := bstep (se 2 (by rfl) ⟨11398866, by rfl⟩ : syracuseStep 30396977 = 22797733) B22797733
theorem B20264651 : Blo 2107435 20264651 := bstep (se 1 (by rfl) ⟨15198488, by rfl⟩ : syracuseStep 20264651 = 30396977) B30396977
theorem B13509767 : Blo 2107435 13509767 := bstep (se 1 (by rfl) ⟨10132325, by rfl⟩ : syracuseStep 13509767 = 20264651) B20264651
theorem B9006511 : Blo 2107435 9006511 := bstep (se 1 (by rfl) ⟨6754883, by rfl⟩ : syracuseStep 9006511 = 13509767) B13509767
theorem B12008681 : Blo 2107435 12008681 := bstep (se 2 (by rfl) ⟨4503255, by rfl⟩ : syracuseStep 12008681 = 9006511) B9006511
theorem B8005787 : Blo 2107435 8005787 := bstep (se 1 (by rfl) ⟨6004340, by rfl⟩ : syracuseStep 8005787 = 12008681) B12008681
theorem B5337191 : Blo 2107435 5337191 := bstep (se 1 (by rfl) ⟨4002893, by rfl⟩ : syracuseStep 5337191 = 8005787) B8005787
theorem B3558127 : Blo 2107435 3558127 := bstep (se 1 (by rfl) ⟨2668595, by rfl⟩ : syracuseStep 3558127 = 5337191) B5337191
theorem B4744169 : Blo 2107435 4744169 := bstep (se 2 (by rfl) ⟨1779063, by rfl⟩ : syracuseStep 4744169 = 3558127) B3558127
theorem B3162779 : Blo 2107435 3162779 := bstep (se 1 (by rfl) ⟨2372084, by rfl⟩ : syracuseStep 3162779 = 4744169) B4744169
theorem B2108519 : Blo 2107435 2108519 := bstep (se 1 (by rfl) ⟨1581389, by rfl⟩ : syracuseStep 2108519 = 3162779) B3162779
theorem B2372089 : Blo 2107435 2372089 := bbase (se 2 (by rfl) ⟨889533, by rfl⟩ : syracuseStep 2372089 = 1779067) (by norm_num)
theorem B3162785 : Blo 2107435 3162785 := bstep (se 2 (by rfl) ⟨1186044, by rfl⟩ : syracuseStep 3162785 = 2372089) B2372089
theorem B2108523 : Blo 2107435 2108523 := bstep (se 1 (by rfl) ⟨1581392, by rfl⟩ : syracuseStep 2108523 = 3162785) B3162785
theorem B3799637 : Blo 2107435 3799637 := bbase (se 8 (by rfl) ⟨22263, by rfl⟩ : syracuseStep 3799637 = 44527) (by norm_num)
theorem B2533091 : Blo 2107435 2533091 := bstep (se 1 (by rfl) ⟨1899818, by rfl⟩ : syracuseStep 2533091 = 3799637) B3799637
theorem B6754909 : Blo 2107435 6754909 := bstep (se 3 (by rfl) ⟨1266545, by rfl⟩ : syracuseStep 6754909 = 2533091) B2533091
theorem B9006545 : Blo 2107435 9006545 := bstep (se 2 (by rfl) ⟨3377454, by rfl⟩ : syracuseStep 9006545 = 6754909) B6754909
theorem B6004363 : Blo 2107435 6004363 := bstep (se 1 (by rfl) ⟨4503272, by rfl⟩ : syracuseStep 6004363 = 9006545) B9006545
theorem B8005817 : Blo 2107435 8005817 := bstep (se 2 (by rfl) ⟨3002181, by rfl⟩ : syracuseStep 8005817 = 6004363) B6004363
theorem B5337211 : Blo 2107435 5337211 := bstep (se 1 (by rfl) ⟨4002908, by rfl⟩ : syracuseStep 5337211 = 8005817) B8005817
theorem B7116281 : Blo 2107435 7116281 := bstep (se 2 (by rfl) ⟨2668605, by rfl⟩ : syracuseStep 7116281 = 5337211) B5337211
theorem B4744187 : Blo 2107435 4744187 := bstep (se 1 (by rfl) ⟨3558140, by rfl⟩ : syracuseStep 4744187 = 7116281) B7116281
theorem B3162791 : Blo 2107435 3162791 := bstep (se 1 (by rfl) ⟨2372093, by rfl⟩ : syracuseStep 3162791 = 4744187) B4744187
theorem B2108527 : Blo 2107435 2108527 := bstep (se 1 (by rfl) ⟨1581395, by rfl⟩ : syracuseStep 2108527 = 3162791) B3162791
theorem B3162797 : Blo 2107435 3162797 := bbase (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) (by norm_num)
theorem B2108531 : Blo 2107435 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B4744205 : Blo 2107435 4744205 := bbase (se 3 (by rfl) ⟨889538, by rfl⟩ : syracuseStep 4744205 = 1779077) (by norm_num)
theorem B3162803 : Blo 2107435 3162803 := bstep (se 1 (by rfl) ⟨2372102, by rfl⟩ : syracuseStep 3162803 = 4744205) B4744205
theorem B2108535 : Blo 2107435 2108535 := bstep (se 1 (by rfl) ⟨1581401, by rfl⟩ : syracuseStep 2108535 = 3162803) B3162803
theorem B2668621 : Blo 2107435 2668621 := bbase (se 3 (by rfl) ⟨500366, by rfl⟩ : syracuseStep 2668621 = 1000733) (by norm_num)
theorem B3558161 : Blo 2107435 3558161 := bstep (se 2 (by rfl) ⟨1334310, by rfl⟩ : syracuseStep 3558161 = 2668621) B2668621
theorem B2372107 : Blo 2107435 2372107 := bstep (se 1 (by rfl) ⟨1779080, by rfl⟩ : syracuseStep 2372107 = 3558161) B3558161
theorem B3162809 : Blo 2107435 3162809 := bstep (se 2 (by rfl) ⟨1186053, by rfl⟩ : syracuseStep 3162809 = 2372107) B2372107
theorem B2108539 : Blo 2107435 2108539 := bstep (se 1 (by rfl) ⟨1581404, by rfl⟩ : syracuseStep 2108539 = 3162809) B3162809
theorem B3043165 : Blo 2107435 3043165 := bbase (se 3 (by rfl) ⟨570593, by rfl⟩ : syracuseStep 3043165 = 1141187) (by norm_num)
theorem B4057553 : Blo 2107435 4057553 := bstep (se 2 (by rfl) ⟨1521582, by rfl⟩ : syracuseStep 4057553 = 3043165) B3043165
theorem B10820141 : Blo 2107435 10820141 := bstep (se 3 (by rfl) ⟨2028776, by rfl⟩ : syracuseStep 10820141 = 4057553) B4057553
theorem B7213427 : Blo 2107435 7213427 := bstep (se 1 (by rfl) ⟨5410070, by rfl⟩ : syracuseStep 7213427 = 10820141) B10820141
theorem B4808951 : Blo 2107435 4808951 := bstep (se 1 (by rfl) ⟨3606713, by rfl⟩ : syracuseStep 4808951 = 7213427) B7213427
theorem B51295477 : Blo 2107435 51295477 := bstep (se 5 (by rfl) ⟨2404475, by rfl⟩ : syracuseStep 51295477 = 4808951) B4808951
theorem B68393969 : Blo 2107435 68393969 := bstep (se 2 (by rfl) ⟨25647738, by rfl⟩ : syracuseStep 68393969 = 51295477) B51295477
theorem B45595979 : Blo 2107435 45595979 := bstep (se 1 (by rfl) ⟨34196984, by rfl⟩ : syracuseStep 45595979 = 68393969) B68393969
theorem B30397319 : Blo 2107435 30397319 := bstep (se 1 (by rfl) ⟨22797989, by rfl⟩ : syracuseStep 30397319 = 45595979) B45595979
theorem B20264879 : Blo 2107435 20264879 := bstep (se 1 (by rfl) ⟨15198659, by rfl⟩ : syracuseStep 20264879 = 30397319) B30397319
theorem B13509919 : Blo 2107435 13509919 := bstep (se 1 (by rfl) ⟨10132439, by rfl⟩ : syracuseStep 13509919 = 20264879) B20264879
theorem B18013225 : Blo 2107435 18013225 := bstep (se 2 (by rfl) ⟨6754959, by rfl⟩ : syracuseStep 18013225 = 13509919) B13509919
theorem B24017633 : Blo 2107435 24017633 := bstep (se 2 (by rfl) ⟨9006612, by rfl⟩ : syracuseStep 24017633 = 18013225) B18013225
theorem B16011755 : Blo 2107435 16011755 := bstep (se 1 (by rfl) ⟨12008816, by rfl⟩ : syracuseStep 16011755 = 24017633) B24017633
theorem B10674503 : Blo 2107435 10674503 := bstep (se 1 (by rfl) ⟨8005877, by rfl⟩ : syracuseStep 10674503 = 16011755) B16011755
theorem B7116335 : Blo 2107435 7116335 := bstep (se 1 (by rfl) ⟨5337251, by rfl⟩ : syracuseStep 7116335 = 10674503) B10674503
theorem B4744223 : Blo 2107435 4744223 := bstep (se 1 (by rfl) ⟨3558167, by rfl⟩ : syracuseStep 4744223 = 7116335) B7116335
theorem B3162815 : Blo 2107435 3162815 := bstep (se 1 (by rfl) ⟨2372111, by rfl⟩ : syracuseStep 3162815 = 4744223) B4744223
theorem B2108543 : Blo 2107435 2108543 := bstep (se 1 (by rfl) ⟨1581407, by rfl⟩ : syracuseStep 2108543 = 3162815) B3162815
theorem B3162821 : Blo 2107435 3162821 := bbase (se 4 (by rfl) ⟨296514, by rfl⟩ : syracuseStep 3162821 = 593029) (by norm_num)
theorem B2108547 : Blo 2107435 2108547 := bstep (se 1 (by rfl) ⟨1581410, by rfl⟩ : syracuseStep 2108547 = 3162821) B3162821
theorem B3558181 : Blo 2107435 3558181 := bbase (se 4 (by rfl) ⟨333579, by rfl⟩ : syracuseStep 3558181 = 667159) (by norm_num)
theorem B4744241 : Blo 2107435 4744241 := bstep (se 2 (by rfl) ⟨1779090, by rfl⟩ : syracuseStep 4744241 = 3558181) B3558181
theorem B3162827 : Blo 2107435 3162827 := bstep (se 1 (by rfl) ⟨2372120, by rfl⟩ : syracuseStep 3162827 = 4744241) B4744241
theorem B2108551 : Blo 2107435 2108551 := bstep (se 1 (by rfl) ⟨1581413, by rfl⟩ : syracuseStep 2108551 = 3162827) B3162827
theorem B2372125 : Blo 2107435 2372125 := bbase (se 3 (by rfl) ⟨444773, by rfl⟩ : syracuseStep 2372125 = 889547) (by norm_num)
theorem B3162833 : Blo 2107435 3162833 := bstep (se 2 (by rfl) ⟨1186062, by rfl⟩ : syracuseStep 3162833 = 2372125) B2372125
theorem B2108555 : Blo 2107435 2108555 := bstep (se 1 (by rfl) ⟨1581416, by rfl⟩ : syracuseStep 2108555 = 3162833) B3162833
theorem B7116389 : Blo 2107435 7116389 := bbase (se 4 (by rfl) ⟨667161, by rfl⟩ : syracuseStep 7116389 = 1334323) (by norm_num)
theorem B4744259 : Blo 2107435 4744259 := bstep (se 1 (by rfl) ⟨3558194, by rfl⟩ : syracuseStep 4744259 = 7116389) B7116389
theorem B3162839 : Blo 2107435 3162839 := bstep (se 1 (by rfl) ⟨2372129, by rfl⟩ : syracuseStep 3162839 = 4744259) B4744259
theorem B2108559 : Blo 2107435 2108559 := bstep (se 1 (by rfl) ⟨1581419, by rfl⟩ : syracuseStep 2108559 = 3162839) B3162839
theorem B3162845 : Blo 2107435 3162845 := bbase (se 3 (by rfl) ⟨593033, by rfl⟩ : syracuseStep 3162845 = 1186067) (by norm_num)
theorem B2108563 : Blo 2107435 2108563 := bstep (se 1 (by rfl) ⟨1581422, by rfl⟩ : syracuseStep 2108563 = 3162845) B3162845
theorem B4744277 : Blo 2107435 4744277 := bbase (se 8 (by rfl) ⟨27798, by rfl⟩ : syracuseStep 4744277 = 55597) (by norm_num)
theorem B3162851 : Blo 2107435 3162851 := bstep (se 1 (by rfl) ⟨2372138, by rfl⟩ : syracuseStep 3162851 = 4744277) B4744277
theorem B2108567 : Blo 2107435 2108567 := bstep (se 1 (by rfl) ⟨1581425, by rfl⟩ : syracuseStep 2108567 = 3162851) B3162851
theorem B5135413 : Blo 2107435 5135413 := bbase (se 5 (by rfl) ⟨240722, by rfl⟩ : syracuseStep 5135413 = 481445) (by norm_num)
theorem B6847217 : Blo 2107435 6847217 := bstep (se 2 (by rfl) ⟨2567706, by rfl⟩ : syracuseStep 6847217 = 5135413) B5135413
theorem B4564811 : Blo 2107435 4564811 := bstep (se 1 (by rfl) ⟨3423608, by rfl⟩ : syracuseStep 4564811 = 6847217) B6847217
theorem B3043207 : Blo 2107435 3043207 := bstep (se 1 (by rfl) ⟨2282405, by rfl⟩ : syracuseStep 3043207 = 4564811) B4564811
theorem B4057609 : Blo 2107435 4057609 := bstep (se 2 (by rfl) ⟨1521603, by rfl⟩ : syracuseStep 4057609 = 3043207) B3043207
theorem B5410145 : Blo 2107435 5410145 := bstep (se 2 (by rfl) ⟨2028804, by rfl⟩ : syracuseStep 5410145 = 4057609) B4057609
theorem B3606763 : Blo 2107435 3606763 := bstep (se 1 (by rfl) ⟨2705072, by rfl⟩ : syracuseStep 3606763 = 5410145) B5410145
theorem B4809017 : Blo 2107435 4809017 := bstep (se 2 (by rfl) ⟨1803381, by rfl⟩ : syracuseStep 4809017 = 3606763) B3606763
theorem B12824045 : Blo 2107435 12824045 := bstep (se 3 (by rfl) ⟨2404508, by rfl⟩ : syracuseStep 12824045 = 4809017) B4809017
theorem B8549363 : Blo 2107435 8549363 := bstep (se 1 (by rfl) ⟨6412022, by rfl⟩ : syracuseStep 8549363 = 12824045) B12824045
theorem B5699575 : Blo 2107435 5699575 := bstep (se 1 (by rfl) ⟨4274681, by rfl⟩ : syracuseStep 5699575 = 8549363) B8549363
theorem B7599433 : Blo 2107435 7599433 := bstep (se 2 (by rfl) ⟨2849787, by rfl⟩ : syracuseStep 7599433 = 5699575) B5699575
theorem B10132577 : Blo 2107435 10132577 := bstep (se 2 (by rfl) ⟨3799716, by rfl⟩ : syracuseStep 10132577 = 7599433) B7599433
theorem B6755051 : Blo 2107435 6755051 := bstep (se 1 (by rfl) ⟨5066288, by rfl⟩ : syracuseStep 6755051 = 10132577) B10132577
theorem B4503367 : Blo 2107435 4503367 := bstep (se 1 (by rfl) ⟨3377525, by rfl⟩ : syracuseStep 4503367 = 6755051) B6755051
theorem B6004489 : Blo 2107435 6004489 := bstep (se 2 (by rfl) ⟨2251683, by rfl⟩ : syracuseStep 6004489 = 4503367) B4503367
theorem B8005985 : Blo 2107435 8005985 := bstep (se 2 (by rfl) ⟨3002244, by rfl⟩ : syracuseStep 8005985 = 6004489) B6004489
theorem B5337323 : Blo 2107435 5337323 := bstep (se 1 (by rfl) ⟨4002992, by rfl⟩ : syracuseStep 5337323 = 8005985) B8005985
theorem B3558215 : Blo 2107435 3558215 := bstep (se 1 (by rfl) ⟨2668661, by rfl⟩ : syracuseStep 3558215 = 5337323) B5337323
theorem B2372143 : Blo 2107435 2372143 := bstep (se 1 (by rfl) ⟨1779107, by rfl⟩ : syracuseStep 2372143 = 3558215) B3558215
theorem B3162857 : Blo 2107435 3162857 := bstep (se 2 (by rfl) ⟨1186071, by rfl⟩ : syracuseStep 3162857 = 2372143) B2372143
theorem B2108571 : Blo 2107435 2108571 := bstep (se 1 (by rfl) ⟨1581428, by rfl⟩ : syracuseStep 2108571 = 3162857) B3162857
theorem B30397781 : Blo 2107435 30397781 := bbase (se 15 (by rfl) ⟨1391, by rfl⟩ : syracuseStep 30397781 = 2783) (by norm_num)
theorem B20265187 : Blo 2107435 20265187 := bstep (se 1 (by rfl) ⟨15198890, by rfl⟩ : syracuseStep 20265187 = 30397781) B30397781
theorem B27020249 : Blo 2107435 27020249 := bstep (se 2 (by rfl) ⟨10132593, by rfl⟩ : syracuseStep 27020249 = 20265187) B20265187
theorem B18013499 : Blo 2107435 18013499 := bstep (se 1 (by rfl) ⟨13510124, by rfl⟩ : syracuseStep 18013499 = 27020249) B27020249
theorem B12008999 : Blo 2107435 12008999 := bstep (se 1 (by rfl) ⟨9006749, by rfl⟩ : syracuseStep 12008999 = 18013499) B18013499
theorem B8005999 : Blo 2107435 8005999 := bstep (se 1 (by rfl) ⟨6004499, by rfl⟩ : syracuseStep 8005999 = 12008999) B12008999
theorem B10674665 : Blo 2107435 10674665 := bstep (se 2 (by rfl) ⟨4002999, by rfl⟩ : syracuseStep 10674665 = 8005999) B8005999
theorem B7116443 : Blo 2107435 7116443 := bstep (se 1 (by rfl) ⟨5337332, by rfl⟩ : syracuseStep 7116443 = 10674665) B10674665
theorem B4744295 : Blo 2107435 4744295 := bstep (se 1 (by rfl) ⟨3558221, by rfl⟩ : syracuseStep 4744295 = 7116443) B7116443
theorem B3162863 : Blo 2107435 3162863 := bstep (se 1 (by rfl) ⟨2372147, by rfl⟩ : syracuseStep 3162863 = 4744295) B4744295
theorem B2108575 : Blo 2107435 2108575 := bstep (se 1 (by rfl) ⟨1581431, by rfl⟩ : syracuseStep 2108575 = 3162863) B3162863
theorem B3162869 : Blo 2107435 3162869 := bbase (se 5 (by rfl) ⟨148259, by rfl⟩ : syracuseStep 3162869 = 296519) (by norm_num)
theorem B2108579 : Blo 2107435 2108579 := bstep (se 1 (by rfl) ⟨1581434, by rfl⟩ : syracuseStep 2108579 = 3162869) B3162869
theorem B5066317 : Blo 2107435 5066317 := bbase (se 3 (by rfl) ⟨949934, by rfl⟩ : syracuseStep 5066317 = 1899869) (by norm_num)
theorem B6755089 : Blo 2107435 6755089 := bstep (se 2 (by rfl) ⟨2533158, by rfl⟩ : syracuseStep 6755089 = 5066317) B5066317
theorem B9006785 : Blo 2107435 9006785 := bstep (se 2 (by rfl) ⟨3377544, by rfl⟩ : syracuseStep 9006785 = 6755089) B6755089
theorem B6004523 : Blo 2107435 6004523 := bstep (se 1 (by rfl) ⟨4503392, by rfl⟩ : syracuseStep 6004523 = 9006785) B9006785
theorem B4003015 : Blo 2107435 4003015 := bstep (se 1 (by rfl) ⟨3002261, by rfl⟩ : syracuseStep 4003015 = 6004523) B6004523
theorem B5337353 : Blo 2107435 5337353 := bstep (se 2 (by rfl) ⟨2001507, by rfl⟩ : syracuseStep 5337353 = 4003015) B4003015
theorem B3558235 : Blo 2107435 3558235 := bstep (se 1 (by rfl) ⟨2668676, by rfl⟩ : syracuseStep 3558235 = 5337353) B5337353
theorem B4744313 : Blo 2107435 4744313 := bstep (se 2 (by rfl) ⟨1779117, by rfl⟩ : syracuseStep 4744313 = 3558235) B3558235
theorem B3162875 : Blo 2107435 3162875 := bstep (se 1 (by rfl) ⟨2372156, by rfl⟩ : syracuseStep 3162875 = 4744313) B4744313
theorem B2108583 : Blo 2107435 2108583 := bstep (se 1 (by rfl) ⟨1581437, by rfl⟩ : syracuseStep 2108583 = 3162875) B3162875
theorem B2372161 : Blo 2107435 2372161 := bbase (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) (by norm_num)
theorem B3162881 : Blo 2107435 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B2108587 : Blo 2107435 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B5337373 : Blo 2107435 5337373 := bbase (se 3 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 5337373 = 2001515) (by norm_num)
theorem B7116497 : Blo 2107435 7116497 := bstep (se 2 (by rfl) ⟨2668686, by rfl⟩ : syracuseStep 7116497 = 5337373) B5337373
theorem B4744331 : Blo 2107435 4744331 := bstep (se 1 (by rfl) ⟨3558248, by rfl⟩ : syracuseStep 4744331 = 7116497) B7116497
theorem B3162887 : Blo 2107435 3162887 := bstep (se 1 (by rfl) ⟨2372165, by rfl⟩ : syracuseStep 3162887 = 4744331) B4744331
theorem B2108591 : Blo 2107435 2108591 := bstep (se 1 (by rfl) ⟨1581443, by rfl⟩ : syracuseStep 2108591 = 3162887) B3162887
theorem B3162893 : Blo 2107435 3162893 := bbase (se 3 (by rfl) ⟨593042, by rfl⟩ : syracuseStep 3162893 = 1186085) (by norm_num)
theorem B2108595 : Blo 2107435 2108595 := bstep (se 1 (by rfl) ⟨1581446, by rfl⟩ : syracuseStep 2108595 = 3162893) B3162893
theorem B4744349 : Blo 2107435 4744349 := bbase (se 3 (by rfl) ⟨889565, by rfl⟩ : syracuseStep 4744349 = 1779131) (by norm_num)
theorem B3162899 : Blo 2107435 3162899 := bstep (se 1 (by rfl) ⟨2372174, by rfl⟩ : syracuseStep 3162899 = 4744349) B4744349
theorem B2108599 : Blo 2107435 2108599 := bstep (se 1 (by rfl) ⟨1581449, by rfl⟩ : syracuseStep 2108599 = 3162899) B3162899
theorem B3558269 : Blo 2107435 3558269 := bbase (se 3 (by rfl) ⟨667175, by rfl⟩ : syracuseStep 3558269 = 1334351) (by norm_num)
theorem B2372179 : Blo 2107435 2372179 := bstep (se 1 (by rfl) ⟨1779134, by rfl⟩ : syracuseStep 2372179 = 3558269) B3558269
theorem B3162905 : Blo 2107435 3162905 := bstep (se 2 (by rfl) ⟨1186089, by rfl⟩ : syracuseStep 3162905 = 2372179) B2372179
theorem B2108603 : Blo 2107435 2108603 := bstep (se 1 (by rfl) ⟨1581452, by rfl⟩ : syracuseStep 2108603 = 3162905) B3162905
theorem B3799781 : Blo 2107435 3799781 := bbase (se 4 (by rfl) ⟨356229, by rfl⟩ : syracuseStep 3799781 = 712459) (by norm_num)
theorem B2533187 : Blo 2107435 2533187 := bstep (se 1 (by rfl) ⟨1899890, by rfl⟩ : syracuseStep 2533187 = 3799781) B3799781
theorem B6755165 : Blo 2107435 6755165 := bstep (se 3 (by rfl) ⟨1266593, by rfl⟩ : syracuseStep 6755165 = 2533187) B2533187
theorem B4503443 : Blo 2107435 4503443 := bstep (se 1 (by rfl) ⟨3377582, by rfl⟩ : syracuseStep 4503443 = 6755165) B6755165
theorem B12009181 : Blo 2107435 12009181 := bstep (se 3 (by rfl) ⟨2251721, by rfl⟩ : syracuseStep 12009181 = 4503443) B4503443
theorem B16012241 : Blo 2107435 16012241 := bstep (se 2 (by rfl) ⟨6004590, by rfl⟩ : syracuseStep 16012241 = 12009181) B12009181
theorem B10674827 : Blo 2107435 10674827 := bstep (se 1 (by rfl) ⟨8006120, by rfl⟩ : syracuseStep 10674827 = 16012241) B16012241
theorem B7116551 : Blo 2107435 7116551 := bstep (se 1 (by rfl) ⟨5337413, by rfl⟩ : syracuseStep 7116551 = 10674827) B10674827
theorem B4744367 : Blo 2107435 4744367 := bstep (se 1 (by rfl) ⟨3558275, by rfl⟩ : syracuseStep 4744367 = 7116551) B7116551
theorem B3162911 : Blo 2107435 3162911 := bstep (se 1 (by rfl) ⟨2372183, by rfl⟩ : syracuseStep 3162911 = 4744367) B4744367
theorem B2108607 : Blo 2107435 2108607 := bstep (se 1 (by rfl) ⟨1581455, by rfl⟩ : syracuseStep 2108607 = 3162911) B3162911
theorem B3162917 : Blo 2107435 3162917 := bbase (se 4 (by rfl) ⟨296523, by rfl⟩ : syracuseStep 3162917 = 593047) (by norm_num)
theorem B2108611 : Blo 2107435 2108611 := bstep (se 1 (by rfl) ⟨1581458, by rfl⟩ : syracuseStep 2108611 = 3162917) B3162917
theorem B2668717 : Blo 2107435 2668717 := bbase (se 3 (by rfl) ⟨500384, by rfl⟩ : syracuseStep 2668717 = 1000769) (by norm_num)
theorem B3558289 : Blo 2107435 3558289 := bstep (se 2 (by rfl) ⟨1334358, by rfl⟩ : syracuseStep 3558289 = 2668717) B2668717
theorem B4744385 : Blo 2107435 4744385 := bstep (se 2 (by rfl) ⟨1779144, by rfl⟩ : syracuseStep 4744385 = 3558289) B3558289
theorem B3162923 : Blo 2107435 3162923 := bstep (se 1 (by rfl) ⟨2372192, by rfl⟩ : syracuseStep 3162923 = 4744385) B4744385
theorem B2108615 : Blo 2107435 2108615 := bstep (se 1 (by rfl) ⟨1581461, by rfl⟩ : syracuseStep 2108615 = 3162923) B3162923
theorem B2372197 : Blo 2107435 2372197 := bbase (se 4 (by rfl) ⟨222393, by rfl⟩ : syracuseStep 2372197 = 444787) (by norm_num)
theorem B3162929 : Blo 2107435 3162929 := bstep (se 2 (by rfl) ⟨1186098, by rfl⟩ : syracuseStep 3162929 = 2372197) B2372197
theorem B2108619 : Blo 2107435 2108619 := bstep (se 1 (by rfl) ⟨1581464, by rfl⟩ : syracuseStep 2108619 = 3162929) B3162929
theorem B5699717 : Blo 2107435 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B3799811 : Blo 2107435 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B2533207 : Blo 2107435 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B3377609 : Blo 2107435 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B2251739 : Blo 2107435 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B6004637 : Blo 2107435 6004637 := bstep (se 3 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 6004637 = 2251739) B2251739
theorem B4003091 : Blo 2107435 4003091 := bstep (se 1 (by rfl) ⟨3002318, by rfl⟩ : syracuseStep 4003091 = 6004637) B6004637
theorem B2668727 : Blo 2107435 2668727 := bstep (se 1 (by rfl) ⟨2001545, by rfl⟩ : syracuseStep 2668727 = 4003091) B4003091
theorem B7116605 : Blo 2107435 7116605 := bstep (se 3 (by rfl) ⟨1334363, by rfl⟩ : syracuseStep 7116605 = 2668727) B2668727
theorem B4744403 : Blo 2107435 4744403 := bstep (se 1 (by rfl) ⟨3558302, by rfl⟩ : syracuseStep 4744403 = 7116605) B7116605
theorem B3162935 : Blo 2107435 3162935 := bstep (se 1 (by rfl) ⟨2372201, by rfl⟩ : syracuseStep 3162935 = 4744403) B4744403
theorem B2108623 : Blo 2107435 2108623 := bstep (se 1 (by rfl) ⟨1581467, by rfl⟩ : syracuseStep 2108623 = 3162935) B3162935
theorem B3162941 : Blo 2107435 3162941 := bbase (se 3 (by rfl) ⟨593051, by rfl⟩ : syracuseStep 3162941 = 1186103) (by norm_num)
theorem B2108627 : Blo 2107435 2108627 := bstep (se 1 (by rfl) ⟨1581470, by rfl⟩ : syracuseStep 2108627 = 3162941) B3162941
theorem B4744421 : Blo 2107435 4744421 := bbase (se 4 (by rfl) ⟨444789, by rfl⟩ : syracuseStep 4744421 = 889579) (by norm_num)
theorem B3162947 : Blo 2107435 3162947 := bstep (se 1 (by rfl) ⟨2372210, by rfl⟩ : syracuseStep 3162947 = 4744421) B4744421
theorem B2108631 : Blo 2107435 2108631 := bstep (se 1 (by rfl) ⟨1581473, by rfl⟩ : syracuseStep 2108631 = 3162947) B3162947
theorem B5337485 : Blo 2107435 5337485 := bbase (se 3 (by rfl) ⟨1000778, by rfl⟩ : syracuseStep 5337485 = 2001557) (by norm_num)
theorem B3558323 : Blo 2107435 3558323 := bstep (se 1 (by rfl) ⟨2668742, by rfl⟩ : syracuseStep 3558323 = 5337485) B5337485
theorem B2372215 : Blo 2107435 2372215 := bstep (se 1 (by rfl) ⟨1779161, by rfl⟩ : syracuseStep 2372215 = 3558323) B3558323
theorem B3162953 : Blo 2107435 3162953 := bstep (se 2 (by rfl) ⟨1186107, by rfl⟩ : syracuseStep 3162953 = 2372215) B2372215
theorem B2108635 : Blo 2107435 2108635 := bstep (se 1 (by rfl) ⟨1581476, by rfl⟩ : syracuseStep 2108635 = 3162953) B3162953
theorem B3002341 : Blo 2107435 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B4003121 : Blo 2107435 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B10674989 : Blo 2107435 10674989 := bstep (se 3 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 10674989 = 4003121) B4003121
theorem B7116659 : Blo 2107435 7116659 := bstep (se 1 (by rfl) ⟨5337494, by rfl⟩ : syracuseStep 7116659 = 10674989) B10674989
theorem B4744439 : Blo 2107435 4744439 := bstep (se 1 (by rfl) ⟨3558329, by rfl⟩ : syracuseStep 4744439 = 7116659) B7116659
theorem B3162959 : Blo 2107435 3162959 := bstep (se 1 (by rfl) ⟨2372219, by rfl⟩ : syracuseStep 3162959 = 4744439) B4744439
theorem B2108639 : Blo 2107435 2108639 := bstep (se 1 (by rfl) ⟨1581479, by rfl⟩ : syracuseStep 2108639 = 3162959) B3162959
theorem B3162965 : Blo 2107435 3162965 := bbase (se 9 (by rfl) ⟨9266, by rfl⟩ : syracuseStep 3162965 = 18533) (by norm_num)
theorem B2108643 : Blo 2107435 2108643 := bstep (se 1 (by rfl) ⟨1581482, by rfl⟩ : syracuseStep 2108643 = 3162965) B3162965
theorem B8115509 : Blo 2107435 8115509 := bbase (se 5 (by rfl) ⟨380414, by rfl⟩ : syracuseStep 8115509 = 760829) (by norm_num)
theorem B21641357 : Blo 2107435 21641357 := bstep (se 3 (by rfl) ⟨4057754, by rfl⟩ : syracuseStep 21641357 = 8115509) B8115509
theorem B14427571 : Blo 2107435 14427571 := bstep (se 1 (by rfl) ⟨10820678, by rfl⟩ : syracuseStep 14427571 = 21641357) B21641357
theorem B19236761 : Blo 2107435 19236761 := bstep (se 2 (by rfl) ⟨7213785, by rfl⟩ : syracuseStep 19236761 = 14427571) B14427571
theorem B12824507 : Blo 2107435 12824507 := bstep (se 1 (by rfl) ⟨9618380, by rfl⟩ : syracuseStep 12824507 = 19236761) B19236761
theorem B8549671 : Blo 2107435 8549671 := bstep (se 1 (by rfl) ⟨6412253, by rfl⟩ : syracuseStep 8549671 = 12824507) B12824507
theorem B11399561 : Blo 2107435 11399561 := bstep (se 2 (by rfl) ⟨4274835, by rfl⟩ : syracuseStep 11399561 = 8549671) B8549671
theorem B7599707 : Blo 2107435 7599707 := bstep (se 1 (by rfl) ⟨5699780, by rfl⟩ : syracuseStep 7599707 = 11399561) B11399561
theorem B5066471 : Blo 2107435 5066471 := bstep (se 1 (by rfl) ⟨3799853, by rfl⟩ : syracuseStep 5066471 = 7599707) B7599707
theorem B3377647 : Blo 2107435 3377647 := bstep (se 1 (by rfl) ⟨2533235, by rfl⟩ : syracuseStep 3377647 = 5066471) B5066471
theorem B4503529 : Blo 2107435 4503529 := bstep (se 2 (by rfl) ⟨1688823, by rfl⟩ : syracuseStep 4503529 = 3377647) B3377647
theorem B6004705 : Blo 2107435 6004705 := bstep (se 2 (by rfl) ⟨2251764, by rfl⟩ : syracuseStep 6004705 = 4503529) B4503529
theorem B8006273 : Blo 2107435 8006273 := bstep (se 2 (by rfl) ⟨3002352, by rfl⟩ : syracuseStep 8006273 = 6004705) B6004705
theorem B5337515 : Blo 2107435 5337515 := bstep (se 1 (by rfl) ⟨4003136, by rfl⟩ : syracuseStep 5337515 = 8006273) B8006273
theorem B3558343 : Blo 2107435 3558343 := bstep (se 1 (by rfl) ⟨2668757, by rfl⟩ : syracuseStep 3558343 = 5337515) B5337515
theorem B4744457 : Blo 2107435 4744457 := bstep (se 2 (by rfl) ⟨1779171, by rfl⟩ : syracuseStep 4744457 = 3558343) B3558343
theorem B3162971 : Blo 2107435 3162971 := bstep (se 1 (by rfl) ⟨2372228, by rfl⟩ : syracuseStep 3162971 = 4744457) B4744457
theorem B2108647 : Blo 2107435 2108647 := bstep (se 1 (by rfl) ⟨1581485, by rfl⟩ : syracuseStep 2108647 = 3162971) B3162971
theorem B2372233 : Blo 2107435 2372233 := bbase (se 2 (by rfl) ⟨889587, by rfl⟩ : syracuseStep 2372233 = 1779175) (by norm_num)
theorem B3162977 : Blo 2107435 3162977 := bstep (se 2 (by rfl) ⟨1186116, by rfl⟩ : syracuseStep 3162977 = 2372233) B2372233
theorem B2108651 : Blo 2107435 2108651 := bstep (se 1 (by rfl) ⟨1581488, by rfl⟩ : syracuseStep 2108651 = 3162977) B3162977
theorem B19499285 : Blo 2107435 19499285 := bbase (se 6 (by rfl) ⟨457014, by rfl⟩ : syracuseStep 19499285 = 914029) (by norm_num)
theorem B12999523 : Blo 2107435 12999523 := bstep (se 1 (by rfl) ⟨9749642, by rfl⟩ : syracuseStep 12999523 = 19499285) B19499285
theorem B17332697 : Blo 2107435 17332697 := bstep (se 2 (by rfl) ⟨6499761, by rfl⟩ : syracuseStep 17332697 = 12999523) B12999523
theorem B11555131 : Blo 2107435 11555131 := bstep (se 1 (by rfl) ⟨8666348, by rfl⟩ : syracuseStep 11555131 = 17332697) B17332697
theorem B15406841 : Blo 2107435 15406841 := bstep (se 2 (by rfl) ⟨5777565, by rfl⟩ : syracuseStep 15406841 = 11555131) B11555131
theorem B10271227 : Blo 2107435 10271227 := bstep (se 1 (by rfl) ⟨7703420, by rfl⟩ : syracuseStep 10271227 = 15406841) B15406841
theorem B13694969 : Blo 2107435 13694969 := bstep (se 2 (by rfl) ⟨5135613, by rfl⟩ : syracuseStep 13694969 = 10271227) B10271227
theorem B9129979 : Blo 2107435 9129979 := bstep (se 1 (by rfl) ⟨6847484, by rfl⟩ : syracuseStep 9129979 = 13694969) B13694969
theorem B48693221 : Blo 2107435 48693221 := bstep (se 4 (by rfl) ⟨4564989, by rfl⟩ : syracuseStep 48693221 = 9129979) B9129979
theorem B32462147 : Blo 2107435 32462147 := bstep (se 1 (by rfl) ⟨24346610, by rfl⟩ : syracuseStep 32462147 = 48693221) B48693221
theorem B21641431 : Blo 2107435 21641431 := bstep (se 1 (by rfl) ⟨16231073, by rfl⟩ : syracuseStep 21641431 = 32462147) B32462147
theorem B28855241 : Blo 2107435 28855241 := bstep (se 2 (by rfl) ⟨10820715, by rfl⟩ : syracuseStep 28855241 = 21641431) B21641431
theorem B19236827 : Blo 2107435 19236827 := bstep (se 1 (by rfl) ⟨14427620, by rfl⟩ : syracuseStep 19236827 = 28855241) B28855241
theorem B12824551 : Blo 2107435 12824551 := bstep (se 1 (by rfl) ⟨9618413, by rfl⟩ : syracuseStep 12824551 = 19236827) B19236827
theorem B68397605 : Blo 2107435 68397605 := bstep (se 4 (by rfl) ⟨6412275, by rfl⟩ : syracuseStep 68397605 = 12824551) B12824551
theorem B45598403 : Blo 2107435 45598403 := bstep (se 1 (by rfl) ⟨34198802, by rfl⟩ : syracuseStep 45598403 = 68397605) B68397605
theorem B30398935 : Blo 2107435 30398935 := bstep (se 1 (by rfl) ⟨22799201, by rfl⟩ : syracuseStep 30398935 = 45598403) B45598403
theorem B40531913 : Blo 2107435 40531913 := bstep (se 2 (by rfl) ⟨15199467, by rfl⟩ : syracuseStep 40531913 = 30398935) B30398935
theorem B27021275 : Blo 2107435 27021275 := bstep (se 1 (by rfl) ⟨20265956, by rfl⟩ : syracuseStep 27021275 = 40531913) B40531913
theorem B18014183 : Blo 2107435 18014183 := bstep (se 1 (by rfl) ⟨13510637, by rfl⟩ : syracuseStep 18014183 = 27021275) B27021275
theorem B12009455 : Blo 2107435 12009455 := bstep (se 1 (by rfl) ⟨9007091, by rfl⟩ : syracuseStep 12009455 = 18014183) B18014183
theorem B8006303 : Blo 2107435 8006303 := bstep (se 1 (by rfl) ⟨6004727, by rfl⟩ : syracuseStep 8006303 = 12009455) B12009455
theorem B5337535 : Blo 2107435 5337535 := bstep (se 1 (by rfl) ⟨4003151, by rfl⟩ : syracuseStep 5337535 = 8006303) B8006303
theorem B7116713 : Blo 2107435 7116713 := bstep (se 2 (by rfl) ⟨2668767, by rfl⟩ : syracuseStep 7116713 = 5337535) B5337535
theorem B4744475 : Blo 2107435 4744475 := bstep (se 1 (by rfl) ⟨3558356, by rfl⟩ : syracuseStep 4744475 = 7116713) B7116713
theorem B3162983 : Blo 2107435 3162983 := bstep (se 1 (by rfl) ⟨2372237, by rfl⟩ : syracuseStep 3162983 = 4744475) B4744475
theorem B2108655 : Blo 2107435 2108655 := bstep (se 1 (by rfl) ⟨1581491, by rfl⟩ : syracuseStep 2108655 = 3162983) B3162983
theorem B3162989 : Blo 2107435 3162989 := bbase (se 3 (by rfl) ⟨593060, by rfl⟩ : syracuseStep 3162989 = 1186121) (by norm_num)
theorem B2108659 : Blo 2107435 2108659 := bstep (se 1 (by rfl) ⟨1581494, by rfl⟩ : syracuseStep 2108659 = 3162989) B3162989
theorem B4744493 : Blo 2107435 4744493 := bbase (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) (by norm_num)
theorem B3162995 : Blo 2107435 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B2108663 : Blo 2107435 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B5135645 : Blo 2107435 5135645 := bbase (se 3 (by rfl) ⟨962933, by rfl⟩ : syracuseStep 5135645 = 1925867) (by norm_num)
theorem B3423763 : Blo 2107435 3423763 := bstep (se 1 (by rfl) ⟨2567822, by rfl⟩ : syracuseStep 3423763 = 5135645) B5135645
theorem B4565017 : Blo 2107435 4565017 := bstep (se 2 (by rfl) ⟨1711881, by rfl⟩ : syracuseStep 4565017 = 3423763) B3423763
theorem B24346757 : Blo 2107435 24346757 := bstep (se 4 (by rfl) ⟨2282508, by rfl⟩ : syracuseStep 24346757 = 4565017) B4565017
theorem B64924685 : Blo 2107435 64924685 := bstep (se 3 (by rfl) ⟨12173378, by rfl⟩ : syracuseStep 64924685 = 24346757) B24346757
theorem B43283123 : Blo 2107435 43283123 := bstep (se 1 (by rfl) ⟨32462342, by rfl⟩ : syracuseStep 43283123 = 64924685) B64924685
theorem B28855415 : Blo 2107435 28855415 := bstep (se 1 (by rfl) ⟨21641561, by rfl⟩ : syracuseStep 28855415 = 43283123) B43283123
theorem B19236943 : Blo 2107435 19236943 := bstep (se 1 (by rfl) ⟨14427707, by rfl⟩ : syracuseStep 19236943 = 28855415) B28855415
theorem B25649257 : Blo 2107435 25649257 := bstep (se 2 (by rfl) ⟨9618471, by rfl⟩ : syracuseStep 25649257 = 19236943) B19236943
theorem B34199009 : Blo 2107435 34199009 := bstep (se 2 (by rfl) ⟨12824628, by rfl⟩ : syracuseStep 34199009 = 25649257) B25649257
theorem B22799339 : Blo 2107435 22799339 := bstep (se 1 (by rfl) ⟨17099504, by rfl⟩ : syracuseStep 22799339 = 34199009) B34199009
theorem B15199559 : Blo 2107435 15199559 := bstep (se 1 (by rfl) ⟨11399669, by rfl⟩ : syracuseStep 15199559 = 22799339) B22799339
theorem B10133039 : Blo 2107435 10133039 := bstep (se 1 (by rfl) ⟨7599779, by rfl⟩ : syracuseStep 10133039 = 15199559) B15199559
theorem B6755359 : Blo 2107435 6755359 := bstep (se 1 (by rfl) ⟨5066519, by rfl⟩ : syracuseStep 6755359 = 10133039) B10133039
theorem B9007145 : Blo 2107435 9007145 := bstep (se 2 (by rfl) ⟨3377679, by rfl⟩ : syracuseStep 9007145 = 6755359) B6755359
theorem B6004763 : Blo 2107435 6004763 := bstep (se 1 (by rfl) ⟨4503572, by rfl⟩ : syracuseStep 6004763 = 9007145) B9007145
theorem B4003175 : Blo 2107435 4003175 := bstep (se 1 (by rfl) ⟨3002381, by rfl⟩ : syracuseStep 4003175 = 6004763) B6004763
theorem B2668783 : Blo 2107435 2668783 := bstep (se 1 (by rfl) ⟨2001587, by rfl⟩ : syracuseStep 2668783 = 4003175) B4003175
theorem B3558377 : Blo 2107435 3558377 := bstep (se 2 (by rfl) ⟨1334391, by rfl⟩ : syracuseStep 3558377 = 2668783) B2668783
theorem B2372251 : Blo 2107435 2372251 := bstep (se 1 (by rfl) ⟨1779188, by rfl⟩ : syracuseStep 2372251 = 3558377) B3558377
theorem B3163001 : Blo 2107435 3163001 := bstep (se 2 (by rfl) ⟨1186125, by rfl⟩ : syracuseStep 3163001 = 2372251) B2372251
theorem B2108667 : Blo 2107435 2108667 := bstep (se 1 (by rfl) ⟨1581500, by rfl⟩ : syracuseStep 2108667 = 3163001) B3163001
theorem B5135653 : Blo 2107435 5135653 := bbase (se 4 (by rfl) ⟨481467, by rfl⟩ : syracuseStep 5135653 = 962935) (by norm_num)
theorem B27390149 : Blo 2107435 27390149 := bstep (se 4 (by rfl) ⟨2567826, by rfl⟩ : syracuseStep 27390149 = 5135653) B5135653
theorem B18260099 : Blo 2107435 18260099 := bstep (se 1 (by rfl) ⟨13695074, by rfl⟩ : syracuseStep 18260099 = 27390149) B27390149
theorem B12173399 : Blo 2107435 12173399 := bstep (se 1 (by rfl) ⟨9130049, by rfl⟩ : syracuseStep 12173399 = 18260099) B18260099
theorem B8115599 : Blo 2107435 8115599 := bstep (se 1 (by rfl) ⟨6086699, by rfl⟩ : syracuseStep 8115599 = 12173399) B12173399
theorem B5410399 : Blo 2107435 5410399 := bstep (se 1 (by rfl) ⟨4057799, by rfl⟩ : syracuseStep 5410399 = 8115599) B8115599
theorem B7213865 : Blo 2107435 7213865 := bstep (se 2 (by rfl) ⟨2705199, by rfl⟩ : syracuseStep 7213865 = 5410399) B5410399
theorem B19236973 : Blo 2107435 19236973 := bstep (se 3 (by rfl) ⟨3606932, by rfl⟩ : syracuseStep 19236973 = 7213865) B7213865
theorem B25649297 : Blo 2107435 25649297 := bstep (se 2 (by rfl) ⟨9618486, by rfl⟩ : syracuseStep 25649297 = 19236973) B19236973
theorem B17099531 : Blo 2107435 17099531 := bstep (se 1 (by rfl) ⟨12824648, by rfl⟩ : syracuseStep 17099531 = 25649297) B25649297
theorem B11399687 : Blo 2107435 11399687 := bstep (se 1 (by rfl) ⟨8549765, by rfl⟩ : syracuseStep 11399687 = 17099531) B17099531
theorem B7599791 : Blo 2107435 7599791 := bstep (se 1 (by rfl) ⟨5699843, by rfl⟩ : syracuseStep 7599791 = 11399687) B11399687
theorem B20266109 : Blo 2107435 20266109 := bstep (se 3 (by rfl) ⟨3799895, by rfl⟩ : syracuseStep 20266109 = 7599791) B7599791
theorem B13510739 : Blo 2107435 13510739 := bstep (se 1 (by rfl) ⟨10133054, by rfl⟩ : syracuseStep 13510739 = 20266109) B20266109
theorem B36028637 : Blo 2107435 36028637 := bstep (se 3 (by rfl) ⟨6755369, by rfl⟩ : syracuseStep 36028637 = 13510739) B13510739
theorem B24019091 : Blo 2107435 24019091 := bstep (se 1 (by rfl) ⟨18014318, by rfl⟩ : syracuseStep 24019091 = 36028637) B36028637
theorem B16012727 : Blo 2107435 16012727 := bstep (se 1 (by rfl) ⟨12009545, by rfl⟩ : syracuseStep 16012727 = 24019091) B24019091
theorem B10675151 : Blo 2107435 10675151 := bstep (se 1 (by rfl) ⟨8006363, by rfl⟩ : syracuseStep 10675151 = 16012727) B16012727
theorem B7116767 : Blo 2107435 7116767 := bstep (se 1 (by rfl) ⟨5337575, by rfl⟩ : syracuseStep 7116767 = 10675151) B10675151
theorem B4744511 : Blo 2107435 4744511 := bstep (se 1 (by rfl) ⟨3558383, by rfl⟩ : syracuseStep 4744511 = 7116767) B7116767
theorem B3163007 : Blo 2107435 3163007 := bstep (se 1 (by rfl) ⟨2372255, by rfl⟩ : syracuseStep 3163007 = 4744511) B4744511
theorem B2108671 : Blo 2107435 2108671 := bstep (se 1 (by rfl) ⟨1581503, by rfl⟩ : syracuseStep 2108671 = 3163007) B3163007
theorem B3163013 : Blo 2107435 3163013 := bbase (se 4 (by rfl) ⟨296532, by rfl⟩ : syracuseStep 3163013 = 593065) (by norm_num)
theorem B2108675 : Blo 2107435 2108675 := bstep (se 1 (by rfl) ⟨1581506, by rfl⟩ : syracuseStep 2108675 = 3163013) B3163013
theorem B3558397 : Blo 2107435 3558397 := bbase (se 3 (by rfl) ⟨667199, by rfl⟩ : syracuseStep 3558397 = 1334399) (by norm_num)
theorem B4744529 : Blo 2107435 4744529 := bstep (se 2 (by rfl) ⟨1779198, by rfl⟩ : syracuseStep 4744529 = 3558397) B3558397
theorem B3163019 : Blo 2107435 3163019 := bstep (se 1 (by rfl) ⟨2372264, by rfl⟩ : syracuseStep 3163019 = 4744529) B4744529
theorem B2108679 : Blo 2107435 2108679 := bstep (se 1 (by rfl) ⟨1581509, by rfl⟩ : syracuseStep 2108679 = 3163019) B3163019
theorem B2372269 : Blo 2107435 2372269 := bbase (se 3 (by rfl) ⟨444800, by rfl⟩ : syracuseStep 2372269 = 889601) (by norm_num)
theorem B3163025 : Blo 2107435 3163025 := bstep (se 2 (by rfl) ⟨1186134, by rfl⟩ : syracuseStep 3163025 = 2372269) B2372269
theorem B2108683 : Blo 2107435 2108683 := bstep (se 1 (by rfl) ⟨1581512, by rfl⟩ : syracuseStep 2108683 = 3163025) B3163025
theorem B7116821 : Blo 2107435 7116821 := bbase (se 6 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 7116821 = 333601) (by norm_num)
theorem B4744547 : Blo 2107435 4744547 := bstep (se 1 (by rfl) ⟨3558410, by rfl⟩ : syracuseStep 4744547 = 7116821) B7116821
theorem B3163031 : Blo 2107435 3163031 := bstep (se 1 (by rfl) ⟨2372273, by rfl⟩ : syracuseStep 3163031 = 4744547) B4744547
theorem B2108687 : Blo 2107435 2108687 := bstep (se 1 (by rfl) ⟨1581515, by rfl⟩ : syracuseStep 2108687 = 3163031) B3163031
theorem B3163037 : Blo 2107435 3163037 := bbase (se 3 (by rfl) ⟨593069, by rfl⟩ : syracuseStep 3163037 = 1186139) (by norm_num)
theorem B2108691 : Blo 2107435 2108691 := bstep (se 1 (by rfl) ⟨1581518, by rfl⟩ : syracuseStep 2108691 = 3163037) B3163037
theorem B4744565 : Blo 2107435 4744565 := bbase (se 5 (by rfl) ⟨222401, by rfl⟩ : syracuseStep 4744565 = 444803) (by norm_num)
theorem B3163043 : Blo 2107435 3163043 := bstep (se 1 (by rfl) ⟨2372282, by rfl⟩ : syracuseStep 3163043 = 4744565) B4744565
theorem B2108695 : Blo 2107435 2108695 := bstep (se 1 (by rfl) ⟨1581521, by rfl⟩ : syracuseStep 2108695 = 3163043) B3163043
theorem B12824821 : Blo 2107435 12824821 := bbase (se 5 (by rfl) ⟨601163, by rfl⟩ : syracuseStep 12824821 = 1202327) (by norm_num)
theorem B17099761 : Blo 2107435 17099761 := bstep (se 2 (by rfl) ⟨6412410, by rfl⟩ : syracuseStep 17099761 = 12824821) B12824821
theorem B22799681 : Blo 2107435 22799681 := bstep (se 2 (by rfl) ⟨8549880, by rfl⟩ : syracuseStep 22799681 = 17099761) B17099761
theorem B15199787 : Blo 2107435 15199787 := bstep (se 1 (by rfl) ⟨11399840, by rfl⟩ : syracuseStep 15199787 = 22799681) B22799681
theorem B10133191 : Blo 2107435 10133191 := bstep (se 1 (by rfl) ⟨7599893, by rfl⟩ : syracuseStep 10133191 = 15199787) B15199787
theorem B13510921 : Blo 2107435 13510921 := bstep (se 2 (by rfl) ⟨5066595, by rfl⟩ : syracuseStep 13510921 = 10133191) B10133191
theorem B18014561 : Blo 2107435 18014561 := bstep (se 2 (by rfl) ⟨6755460, by rfl⟩ : syracuseStep 18014561 = 13510921) B13510921
theorem B12009707 : Blo 2107435 12009707 := bstep (se 1 (by rfl) ⟨9007280, by rfl⟩ : syracuseStep 12009707 = 18014561) B18014561
theorem B8006471 : Blo 2107435 8006471 := bstep (se 1 (by rfl) ⟨6004853, by rfl⟩ : syracuseStep 8006471 = 12009707) B12009707
theorem B5337647 : Blo 2107435 5337647 := bstep (se 1 (by rfl) ⟨4003235, by rfl⟩ : syracuseStep 5337647 = 8006471) B8006471
theorem B3558431 : Blo 2107435 3558431 := bstep (se 1 (by rfl) ⟨2668823, by rfl⟩ : syracuseStep 3558431 = 5337647) B5337647
theorem B2372287 : Blo 2107435 2372287 := bstep (se 1 (by rfl) ⟨1779215, by rfl⟩ : syracuseStep 2372287 = 3558431) B3558431
theorem B3163049 : Blo 2107435 3163049 := bstep (se 2 (by rfl) ⟨1186143, by rfl⟩ : syracuseStep 3163049 = 2372287) B2372287
theorem B2108699 : Blo 2107435 2108699 := bstep (se 1 (by rfl) ⟨1581524, by rfl⟩ : syracuseStep 2108699 = 3163049) B3163049
theorem B8006485 : Blo 2107435 8006485 := bbase (se 9 (by rfl) ⟨23456, by rfl⟩ : syracuseStep 8006485 = 46913) (by norm_num)
theorem B10675313 : Blo 2107435 10675313 := bstep (se 2 (by rfl) ⟨4003242, by rfl⟩ : syracuseStep 10675313 = 8006485) B8006485
theorem B7116875 : Blo 2107435 7116875 := bstep (se 1 (by rfl) ⟨5337656, by rfl⟩ : syracuseStep 7116875 = 10675313) B10675313
theorem B4744583 : Blo 2107435 4744583 := bstep (se 1 (by rfl) ⟨3558437, by rfl⟩ : syracuseStep 4744583 = 7116875) B7116875
theorem B3163055 : Blo 2107435 3163055 := bstep (se 1 (by rfl) ⟨2372291, by rfl⟩ : syracuseStep 3163055 = 4744583) B4744583
theorem B2108703 : Blo 2107435 2108703 := bstep (se 1 (by rfl) ⟨1581527, by rfl⟩ : syracuseStep 2108703 = 3163055) B3163055
theorem B3163061 : Blo 2107435 3163061 := bbase (se 5 (by rfl) ⟨148268, by rfl⟩ : syracuseStep 3163061 = 296537) (by norm_num)
theorem B2108707 : Blo 2107435 2108707 := bstep (se 1 (by rfl) ⟨1581530, by rfl⟩ : syracuseStep 2108707 = 3163061) B3163061
theorem B5337677 : Blo 2107435 5337677 := bbase (se 3 (by rfl) ⟨1000814, by rfl⟩ : syracuseStep 5337677 = 2001629) (by norm_num)
theorem B3558451 : Blo 2107435 3558451 := bstep (se 1 (by rfl) ⟨2668838, by rfl⟩ : syracuseStep 3558451 = 5337677) B5337677
theorem B4744601 : Blo 2107435 4744601 := bstep (se 2 (by rfl) ⟨1779225, by rfl⟩ : syracuseStep 4744601 = 3558451) B3558451
theorem B3163067 : Blo 2107435 3163067 := bstep (se 1 (by rfl) ⟨2372300, by rfl⟩ : syracuseStep 3163067 = 4744601) B4744601
theorem B2108711 : Blo 2107435 2108711 := bstep (se 1 (by rfl) ⟨1581533, by rfl⟩ : syracuseStep 2108711 = 3163067) B3163067
theorem B2372305 : Blo 2107435 2372305 := bbase (se 2 (by rfl) ⟨889614, by rfl⟩ : syracuseStep 2372305 = 1779229) (by norm_num)
theorem B3163073 : Blo 2107435 3163073 := bstep (se 2 (by rfl) ⟨1186152, by rfl⟩ : syracuseStep 3163073 = 2372305) B2372305
theorem B2108715 : Blo 2107435 2108715 := bstep (se 1 (by rfl) ⟨1581536, by rfl⟩ : syracuseStep 2108715 = 3163073) B3163073
theorem B6755525 : Blo 2107435 6755525 := bbase (se 4 (by rfl) ⟨633330, by rfl⟩ : syracuseStep 6755525 = 1266661) (by norm_num)
theorem B4503683 : Blo 2107435 4503683 := bstep (se 1 (by rfl) ⟨3377762, by rfl⟩ : syracuseStep 4503683 = 6755525) B6755525
theorem B3002455 : Blo 2107435 3002455 := bstep (se 1 (by rfl) ⟨2251841, by rfl⟩ : syracuseStep 3002455 = 4503683) B4503683
theorem B4003273 : Blo 2107435 4003273 := bstep (se 2 (by rfl) ⟨1501227, by rfl⟩ : syracuseStep 4003273 = 3002455) B3002455
theorem B5337697 : Blo 2107435 5337697 := bstep (se 2 (by rfl) ⟨2001636, by rfl⟩ : syracuseStep 5337697 = 4003273) B4003273
theorem B7116929 : Blo 2107435 7116929 := bstep (se 2 (by rfl) ⟨2668848, by rfl⟩ : syracuseStep 7116929 = 5337697) B5337697
theorem B4744619 : Blo 2107435 4744619 := bstep (se 1 (by rfl) ⟨3558464, by rfl⟩ : syracuseStep 4744619 = 7116929) B7116929
theorem B3163079 : Blo 2107435 3163079 := bstep (se 1 (by rfl) ⟨2372309, by rfl⟩ : syracuseStep 3163079 = 4744619) B4744619
theorem B2108719 : Blo 2107435 2108719 := bstep (se 1 (by rfl) ⟨1581539, by rfl⟩ : syracuseStep 2108719 = 3163079) B3163079
theorem B3163085 : Blo 2107435 3163085 := bbase (se 3 (by rfl) ⟨593078, by rfl⟩ : syracuseStep 3163085 = 1186157) (by norm_num)
theorem B2108723 : Blo 2107435 2108723 := bstep (se 1 (by rfl) ⟨1581542, by rfl⟩ : syracuseStep 2108723 = 3163085) B3163085
theorem B4744637 : Blo 2107435 4744637 := bbase (se 3 (by rfl) ⟨889619, by rfl⟩ : syracuseStep 4744637 = 1779239) (by norm_num)
theorem B3163091 : Blo 2107435 3163091 := bstep (se 1 (by rfl) ⟨2372318, by rfl⟩ : syracuseStep 3163091 = 4744637) B4744637
theorem B2108727 : Blo 2107435 2108727 := bstep (se 1 (by rfl) ⟨1581545, by rfl⟩ : syracuseStep 2108727 = 3163091) B3163091
theorem B3558485 : Blo 2107435 3558485 := bbase (se 8 (by rfl) ⟨20850, by rfl⟩ : syracuseStep 3558485 = 41701) (by norm_num)
theorem B2372323 : Blo 2107435 2372323 := bstep (se 1 (by rfl) ⟨1779242, by rfl⟩ : syracuseStep 2372323 = 3558485) B3558485
theorem B3163097 : Blo 2107435 3163097 := bstep (se 2 (by rfl) ⟨1186161, by rfl⟩ : syracuseStep 3163097 = 2372323) B2372323
theorem B2108731 : Blo 2107435 2108731 := bstep (se 1 (by rfl) ⟨1581548, by rfl⟩ : syracuseStep 2108731 = 3163097) B3163097
theorem B4275013 : Blo 2107435 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B5700017 : Blo 2107435 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B15200045 : Blo 2107435 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B10133363 : Blo 2107435 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B6755575 : Blo 2107435 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B9007433 : Blo 2107435 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B6004955 : Blo 2107435 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B16013213 : Blo 2107435 16013213 := bstep (se 3 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 16013213 = 6004955) B6004955
theorem B10675475 : Blo 2107435 10675475 := bstep (se 1 (by rfl) ⟨8006606, by rfl⟩ : syracuseStep 10675475 = 16013213) B16013213
theorem B7116983 : Blo 2107435 7116983 := bstep (se 1 (by rfl) ⟨5337737, by rfl⟩ : syracuseStep 7116983 = 10675475) B10675475
theorem B4744655 : Blo 2107435 4744655 := bstep (se 1 (by rfl) ⟨3558491, by rfl⟩ : syracuseStep 4744655 = 7116983) B7116983
theorem B3163103 : Blo 2107435 3163103 := bstep (se 1 (by rfl) ⟨2372327, by rfl⟩ : syracuseStep 3163103 = 4744655) B4744655
theorem B2108735 : Blo 2107435 2108735 := bstep (se 1 (by rfl) ⟨1581551, by rfl⟩ : syracuseStep 2108735 = 3163103) B3163103
theorem B3163109 : Blo 2107435 3163109 := bbase (se 4 (by rfl) ⟨296541, by rfl⟩ : syracuseStep 3163109 = 593083) (by norm_num)
theorem B2108739 : Blo 2107435 2108739 := bstep (se 1 (by rfl) ⟨1581554, by rfl⟩ : syracuseStep 2108739 = 3163109) B3163109
theorem B9618821 : Blo 2107435 9618821 := bbase (se 4 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 9618821 = 1803529) (by norm_num)
theorem B6412547 : Blo 2107435 6412547 := bstep (se 1 (by rfl) ⟨4809410, by rfl⟩ : syracuseStep 6412547 = 9618821) B9618821
theorem B4275031 : Blo 2107435 4275031 := bstep (se 1 (by rfl) ⟨3206273, by rfl⟩ : syracuseStep 4275031 = 6412547) B6412547
theorem B5700041 : Blo 2107435 5700041 := bstep (se 2 (by rfl) ⟨2137515, by rfl⟩ : syracuseStep 5700041 = 4275031) B4275031
theorem B3800027 : Blo 2107435 3800027 := bstep (se 1 (by rfl) ⟨2850020, by rfl⟩ : syracuseStep 3800027 = 5700041) B5700041
theorem B2533351 : Blo 2107435 2533351 := bstep (se 1 (by rfl) ⟨1900013, by rfl⟩ : syracuseStep 2533351 = 3800027) B3800027
theorem B3377801 : Blo 2107435 3377801 := bstep (se 2 (by rfl) ⟨1266675, by rfl⟩ : syracuseStep 3377801 = 2533351) B2533351
theorem B9007469 : Blo 2107435 9007469 := bstep (se 3 (by rfl) ⟨1688900, by rfl⟩ : syracuseStep 9007469 = 3377801) B3377801
theorem B6004979 : Blo 2107435 6004979 := bstep (se 1 (by rfl) ⟨4503734, by rfl⟩ : syracuseStep 6004979 = 9007469) B9007469
theorem B4003319 : Blo 2107435 4003319 := bstep (se 1 (by rfl) ⟨3002489, by rfl⟩ : syracuseStep 4003319 = 6004979) B6004979
theorem B2668879 : Blo 2107435 2668879 := bstep (se 1 (by rfl) ⟨2001659, by rfl⟩ : syracuseStep 2668879 = 4003319) B4003319
theorem B3558505 : Blo 2107435 3558505 := bstep (se 2 (by rfl) ⟨1334439, by rfl⟩ : syracuseStep 3558505 = 2668879) B2668879
theorem B4744673 : Blo 2107435 4744673 := bstep (se 2 (by rfl) ⟨1779252, by rfl⟩ : syracuseStep 4744673 = 3558505) B3558505
theorem B3163115 : Blo 2107435 3163115 := bstep (se 1 (by rfl) ⟨2372336, by rfl⟩ : syracuseStep 3163115 = 4744673) B4744673
theorem B2108743 : Blo 2107435 2108743 := bstep (se 1 (by rfl) ⟨1581557, by rfl⟩ : syracuseStep 2108743 = 3163115) B3163115
theorem B2372341 : Blo 2107435 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B3163121 : Blo 2107435 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B2108747 : Blo 2107435 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B2668889 : Blo 2107435 2668889 := bbase (se 2 (by rfl) ⟨1000833, by rfl⟩ : syracuseStep 2668889 = 2001667) (by norm_num)
theorem B7117037 : Blo 2107435 7117037 := bstep (se 3 (by rfl) ⟨1334444, by rfl⟩ : syracuseStep 7117037 = 2668889) B2668889
theorem B4744691 : Blo 2107435 4744691 := bstep (se 1 (by rfl) ⟨3558518, by rfl⟩ : syracuseStep 4744691 = 7117037) B7117037
theorem B3163127 : Blo 2107435 3163127 := bstep (se 1 (by rfl) ⟨2372345, by rfl⟩ : syracuseStep 3163127 = 4744691) B4744691
theorem B2108751 : Blo 2107435 2108751 := bstep (se 1 (by rfl) ⟨1581563, by rfl⟩ : syracuseStep 2108751 = 3163127) B3163127
theorem B3163133 : Blo 2107435 3163133 := bbase (se 3 (by rfl) ⟨593087, by rfl⟩ : syracuseStep 3163133 = 1186175) (by norm_num)
theorem B2108755 : Blo 2107435 2108755 := bstep (se 1 (by rfl) ⟨1581566, by rfl⟩ : syracuseStep 2108755 = 3163133) B3163133
theorem B4744709 : Blo 2107435 4744709 := bbase (se 4 (by rfl) ⟨444816, by rfl⟩ : syracuseStep 4744709 = 889633) (by norm_num)
theorem B3163139 : Blo 2107435 3163139 := bstep (se 1 (by rfl) ⟨2372354, by rfl⟩ : syracuseStep 3163139 = 4744709) B4744709
theorem B2108759 : Blo 2107435 2108759 := bstep (se 1 (by rfl) ⟨1581569, by rfl⟩ : syracuseStep 2108759 = 3163139) B3163139
theorem B4003357 : Blo 2107435 4003357 := bbase (se 3 (by rfl) ⟨750629, by rfl⟩ : syracuseStep 4003357 = 1501259) (by norm_num)
theorem B5337809 : Blo 2107435 5337809 := bstep (se 2 (by rfl) ⟨2001678, by rfl⟩ : syracuseStep 5337809 = 4003357) B4003357
theorem B3558539 : Blo 2107435 3558539 := bstep (se 1 (by rfl) ⟨2668904, by rfl⟩ : syracuseStep 3558539 = 5337809) B5337809
theorem B2372359 : Blo 2107435 2372359 := bstep (se 1 (by rfl) ⟨1779269, by rfl⟩ : syracuseStep 2372359 = 3558539) B3558539
theorem B3163145 : Blo 2107435 3163145 := bstep (se 2 (by rfl) ⟨1186179, by rfl⟩ : syracuseStep 3163145 = 2372359) B2372359
theorem B2108763 : Blo 2107435 2108763 := bstep (se 1 (by rfl) ⟨1581572, by rfl⟩ : syracuseStep 2108763 = 3163145) B3163145
theorem B10675637 : Blo 2107435 10675637 := bbase (se 5 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 10675637 = 1000841) (by norm_num)
theorem B7117091 : Blo 2107435 7117091 := bstep (se 1 (by rfl) ⟨5337818, by rfl⟩ : syracuseStep 7117091 = 10675637) B10675637
theorem B4744727 : Blo 2107435 4744727 := bstep (se 1 (by rfl) ⟨3558545, by rfl⟩ : syracuseStep 4744727 = 7117091) B7117091
theorem B3163151 : Blo 2107435 3163151 := bstep (se 1 (by rfl) ⟨2372363, by rfl⟩ : syracuseStep 3163151 = 4744727) B4744727
theorem B2108767 : Blo 2107435 2108767 := bstep (se 1 (by rfl) ⟨1581575, by rfl⟩ : syracuseStep 2108767 = 3163151) B3163151
theorem B3163157 : Blo 2107435 3163157 := bbase (se 6 (by rfl) ⟨74136, by rfl⟩ : syracuseStep 3163157 = 148273) (by norm_num)
theorem B2108771 : Blo 2107435 2108771 := bstep (se 1 (by rfl) ⟨1581578, by rfl⟩ : syracuseStep 2108771 = 3163157) B3163157
theorem B4333421 : Blo 2107435 4333421 := bbase (se 3 (by rfl) ⟨812516, by rfl⟩ : syracuseStep 4333421 = 1625033) (by norm_num)
theorem B2888947 : Blo 2107435 2888947 := bstep (se 1 (by rfl) ⟨2166710, by rfl⟩ : syracuseStep 2888947 = 4333421) B4333421
theorem B15407717 : Blo 2107435 15407717 := bstep (se 4 (by rfl) ⟨1444473, by rfl⟩ : syracuseStep 15407717 = 2888947) B2888947
theorem B41087245 : Blo 2107435 41087245 := bstep (se 3 (by rfl) ⟨7703858, by rfl⟩ : syracuseStep 41087245 = 15407717) B15407717
theorem B54782993 : Blo 2107435 54782993 := bstep (se 2 (by rfl) ⟨20543622, by rfl⟩ : syracuseStep 54782993 = 41087245) B41087245
theorem B36521995 : Blo 2107435 36521995 := bstep (se 1 (by rfl) ⟨27391496, by rfl⟩ : syracuseStep 36521995 = 54782993) B54782993
theorem B48695993 : Blo 2107435 48695993 := bstep (se 2 (by rfl) ⟨18260997, by rfl⟩ : syracuseStep 48695993 = 36521995) B36521995
theorem B32463995 : Blo 2107435 32463995 := bstep (se 1 (by rfl) ⟨24347996, by rfl⟩ : syracuseStep 32463995 = 48695993) B48695993
theorem B86570653 : Blo 2107435 86570653 := bstep (se 3 (by rfl) ⟨16231997, by rfl⟩ : syracuseStep 86570653 = 32463995) B32463995
theorem B115427537 : Blo 2107435 115427537 := bstep (se 2 (by rfl) ⟨43285326, by rfl⟩ : syracuseStep 115427537 = 86570653) B86570653
theorem B76951691 : Blo 2107435 76951691 := bstep (se 1 (by rfl) ⟨57713768, by rfl⟩ : syracuseStep 76951691 = 115427537) B115427537
theorem B51301127 : Blo 2107435 51301127 := bstep (se 1 (by rfl) ⟨38475845, by rfl⟩ : syracuseStep 51301127 = 76951691) B76951691
theorem B34200751 : Blo 2107435 34200751 := bstep (se 1 (by rfl) ⟨25650563, by rfl⟩ : syracuseStep 34200751 = 51301127) B51301127
theorem B45601001 : Blo 2107435 45601001 := bstep (se 2 (by rfl) ⟨17100375, by rfl⟩ : syracuseStep 45601001 = 34200751) B34200751
theorem B30400667 : Blo 2107435 30400667 := bstep (se 1 (by rfl) ⟨22800500, by rfl⟩ : syracuseStep 30400667 = 45601001) B45601001
theorem B20267111 : Blo 2107435 20267111 := bstep (se 1 (by rfl) ⟨15200333, by rfl⟩ : syracuseStep 20267111 = 30400667) B30400667
theorem B13511407 : Blo 2107435 13511407 := bstep (se 1 (by rfl) ⟨10133555, by rfl⟩ : syracuseStep 13511407 = 20267111) B20267111
theorem B18015209 : Blo 2107435 18015209 := bstep (se 2 (by rfl) ⟨6755703, by rfl⟩ : syracuseStep 18015209 = 13511407) B13511407
theorem B12010139 : Blo 2107435 12010139 := bstep (se 1 (by rfl) ⟨9007604, by rfl⟩ : syracuseStep 12010139 = 18015209) B18015209
theorem B8006759 : Blo 2107435 8006759 := bstep (se 1 (by rfl) ⟨6005069, by rfl⟩ : syracuseStep 8006759 = 12010139) B12010139
theorem B5337839 : Blo 2107435 5337839 := bstep (se 1 (by rfl) ⟨4003379, by rfl⟩ : syracuseStep 5337839 = 8006759) B8006759
theorem B3558559 : Blo 2107435 3558559 := bstep (se 1 (by rfl) ⟨2668919, by rfl⟩ : syracuseStep 3558559 = 5337839) B5337839
theorem B4744745 : Blo 2107435 4744745 := bstep (se 2 (by rfl) ⟨1779279, by rfl⟩ : syracuseStep 4744745 = 3558559) B3558559
theorem B3163163 : Blo 2107435 3163163 := bstep (se 1 (by rfl) ⟨2372372, by rfl⟩ : syracuseStep 3163163 = 4744745) B4744745
theorem B2108775 : Blo 2107435 2108775 := bstep (se 1 (by rfl) ⟨1581581, by rfl⟩ : syracuseStep 2108775 = 3163163) B3163163
theorem B2372377 : Blo 2107435 2372377 := bbase (se 2 (by rfl) ⟨889641, by rfl⟩ : syracuseStep 2372377 = 1779283) (by norm_num)
theorem B3163169 : Blo 2107435 3163169 := bstep (se 2 (by rfl) ⟨1186188, by rfl⟩ : syracuseStep 3163169 = 2372377) B2372377
theorem B2108779 : Blo 2107435 2108779 := bstep (se 1 (by rfl) ⟨1581584, by rfl⟩ : syracuseStep 2108779 = 3163169) B3163169
theorem B8006789 : Blo 2107435 8006789 := bbase (se 4 (by rfl) ⟨750636, by rfl⟩ : syracuseStep 8006789 = 1501273) (by norm_num)
theorem B5337859 : Blo 2107435 5337859 := bstep (se 1 (by rfl) ⟨4003394, by rfl⟩ : syracuseStep 5337859 = 8006789) B8006789
theorem B7117145 : Blo 2107435 7117145 := bstep (se 2 (by rfl) ⟨2668929, by rfl⟩ : syracuseStep 7117145 = 5337859) B5337859
theorem B4744763 : Blo 2107435 4744763 := bstep (se 1 (by rfl) ⟨3558572, by rfl⟩ : syracuseStep 4744763 = 7117145) B7117145
theorem B3163175 : Blo 2107435 3163175 := bstep (se 1 (by rfl) ⟨2372381, by rfl⟩ : syracuseStep 3163175 = 4744763) B4744763
theorem B2108783 : Blo 2107435 2108783 := bstep (se 1 (by rfl) ⟨1581587, by rfl⟩ : syracuseStep 2108783 = 3163175) B3163175
theorem B3163181 : Blo 2107435 3163181 := bbase (se 3 (by rfl) ⟨593096, by rfl⟩ : syracuseStep 3163181 = 1186193) (by norm_num)
theorem B2108787 : Blo 2107435 2108787 := bstep (se 1 (by rfl) ⟨1581590, by rfl⟩ : syracuseStep 2108787 = 3163181) B3163181
theorem B4744781 : Blo 2107435 4744781 := bbase (se 3 (by rfl) ⟨889646, by rfl⟩ : syracuseStep 4744781 = 1779293) (by norm_num)
theorem B3163187 : Blo 2107435 3163187 := bstep (se 1 (by rfl) ⟨2372390, by rfl⟩ : syracuseStep 3163187 = 4744781) B4744781
theorem B2108791 : Blo 2107435 2108791 := bstep (se 1 (by rfl) ⟨1581593, by rfl⟩ : syracuseStep 2108791 = 3163187) B3163187
theorem B2668945 : Blo 2107435 2668945 := bbase (se 2 (by rfl) ⟨1000854, by rfl⟩ : syracuseStep 2668945 = 2001709) (by norm_num)
theorem B3558593 : Blo 2107435 3558593 := bstep (se 2 (by rfl) ⟨1334472, by rfl⟩ : syracuseStep 3558593 = 2668945) B2668945
theorem B2372395 : Blo 2107435 2372395 := bstep (se 1 (by rfl) ⟨1779296, by rfl⟩ : syracuseStep 2372395 = 3558593) B3558593
theorem B3163193 : Blo 2107435 3163193 := bstep (se 2 (by rfl) ⟨1186197, by rfl⟩ : syracuseStep 3163193 = 2372395) B2372395
theorem B2108795 : Blo 2107435 2108795 := bstep (se 1 (by rfl) ⟨1581596, by rfl⟩ : syracuseStep 2108795 = 3163193) B3163193
theorem B4503853 : Blo 2107435 4503853 := bbase (se 3 (by rfl) ⟨844472, by rfl⟩ : syracuseStep 4503853 = 1688945) (by norm_num)
theorem B24020549 : Blo 2107435 24020549 := bstep (se 4 (by rfl) ⟨2251926, by rfl⟩ : syracuseStep 24020549 = 4503853) B4503853
theorem B16013699 : Blo 2107435 16013699 := bstep (se 1 (by rfl) ⟨12010274, by rfl⟩ : syracuseStep 16013699 = 24020549) B24020549
theorem B10675799 : Blo 2107435 10675799 := bstep (se 1 (by rfl) ⟨8006849, by rfl⟩ : syracuseStep 10675799 = 16013699) B16013699
theorem B7117199 : Blo 2107435 7117199 := bstep (se 1 (by rfl) ⟨5337899, by rfl⟩ : syracuseStep 7117199 = 10675799) B10675799
theorem B4744799 : Blo 2107435 4744799 := bstep (se 1 (by rfl) ⟨3558599, by rfl⟩ : syracuseStep 4744799 = 7117199) B7117199
theorem B3163199 : Blo 2107435 3163199 := bstep (se 1 (by rfl) ⟨2372399, by rfl⟩ : syracuseStep 3163199 = 4744799) B4744799
theorem B2108799 : Blo 2107435 2108799 := bstep (se 1 (by rfl) ⟨1581599, by rfl⟩ : syracuseStep 2108799 = 3163199) B3163199
theorem B3163205 : Blo 2107435 3163205 := bbase (se 4 (by rfl) ⟨296550, by rfl⟩ : syracuseStep 3163205 = 593101) (by norm_num)
theorem B2108803 : Blo 2107435 2108803 := bstep (se 1 (by rfl) ⟨1581602, by rfl⟩ : syracuseStep 2108803 = 3163205) B3163205
theorem B3558613 : Blo 2107435 3558613 := bbase (se 7 (by rfl) ⟨41702, by rfl⟩ : syracuseStep 3558613 = 83405) (by norm_num)
theorem B4744817 : Blo 2107435 4744817 := bstep (se 2 (by rfl) ⟨1779306, by rfl⟩ : syracuseStep 4744817 = 3558613) B3558613
theorem B3163211 : Blo 2107435 3163211 := bstep (se 1 (by rfl) ⟨2372408, by rfl⟩ : syracuseStep 3163211 = 4744817) B4744817
theorem B2108807 : Blo 2107435 2108807 := bstep (se 1 (by rfl) ⟨1581605, by rfl⟩ : syracuseStep 2108807 = 3163211) B3163211
theorem B2372413 : Blo 2107435 2372413 := bbase (se 3 (by rfl) ⟨444827, by rfl⟩ : syracuseStep 2372413 = 889655) (by norm_num)
theorem B3163217 : Blo 2107435 3163217 := bstep (se 2 (by rfl) ⟨1186206, by rfl⟩ : syracuseStep 3163217 = 2372413) B2372413
theorem B2108811 : Blo 2107435 2108811 := bstep (se 1 (by rfl) ⟨1581608, by rfl⟩ : syracuseStep 2108811 = 3163217) B3163217
theorem B7117253 : Blo 2107435 7117253 := bbase (se 4 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 7117253 = 1334485) (by norm_num)
theorem B4744835 : Blo 2107435 4744835 := bstep (se 1 (by rfl) ⟨3558626, by rfl⟩ : syracuseStep 4744835 = 7117253) B7117253
theorem B3163223 : Blo 2107435 3163223 := bstep (se 1 (by rfl) ⟨2372417, by rfl⟩ : syracuseStep 3163223 = 4744835) B4744835
theorem B2108815 : Blo 2107435 2108815 := bstep (se 1 (by rfl) ⟨1581611, by rfl⟩ : syracuseStep 2108815 = 3163223) B3163223
theorem B3163229 : Blo 2107435 3163229 := bbase (se 3 (by rfl) ⟨593105, by rfl⟩ : syracuseStep 3163229 = 1186211) (by norm_num)
theorem B2108819 : Blo 2107435 2108819 := bstep (se 1 (by rfl) ⟨1581614, by rfl⟩ : syracuseStep 2108819 = 3163229) B3163229
theorem B4744853 : Blo 2107435 4744853 := bbase (se 6 (by rfl) ⟨111207, by rfl⟩ : syracuseStep 4744853 = 222415) (by norm_num)
theorem B3163235 : Blo 2107435 3163235 := bstep (se 1 (by rfl) ⟨2372426, by rfl⟩ : syracuseStep 3163235 = 4744853) B4744853
theorem B2108823 : Blo 2107435 2108823 := bstep (se 1 (by rfl) ⟨1581617, by rfl⟩ : syracuseStep 2108823 = 3163235) B3163235
theorem B2251957 : Blo 2107435 2251957 := bbase (se 5 (by rfl) ⟨105560, by rfl⟩ : syracuseStep 2251957 = 211121) (by norm_num)
theorem B3002609 : Blo 2107435 3002609 := bstep (se 2 (by rfl) ⟨1125978, by rfl⟩ : syracuseStep 3002609 = 2251957) B2251957
theorem B8006957 : Blo 2107435 8006957 := bstep (se 3 (by rfl) ⟨1501304, by rfl⟩ : syracuseStep 8006957 = 3002609) B3002609
theorem B5337971 : Blo 2107435 5337971 := bstep (se 1 (by rfl) ⟨4003478, by rfl⟩ : syracuseStep 5337971 = 8006957) B8006957
theorem B3558647 : Blo 2107435 3558647 := bstep (se 1 (by rfl) ⟨2668985, by rfl⟩ : syracuseStep 3558647 = 5337971) B5337971
theorem B2372431 : Blo 2107435 2372431 := bstep (se 1 (by rfl) ⟨1779323, by rfl⟩ : syracuseStep 2372431 = 3558647) B3558647
theorem B3163241 : Blo 2107435 3163241 := bstep (se 2 (by rfl) ⟨1186215, by rfl⟩ : syracuseStep 3163241 = 2372431) B2372431
theorem B2108827 : Blo 2107435 2108827 := bstep (se 1 (by rfl) ⟨1581620, by rfl⟩ : syracuseStep 2108827 = 3163241) B3163241
theorem B13511765 : Blo 2107435 13511765 := bbase (se 8 (by rfl) ⟨79170, by rfl⟩ : syracuseStep 13511765 = 158341) (by norm_num)
theorem B9007843 : Blo 2107435 9007843 := bstep (se 1 (by rfl) ⟨6755882, by rfl⟩ : syracuseStep 9007843 = 13511765) B13511765
theorem B12010457 : Blo 2107435 12010457 := bstep (se 2 (by rfl) ⟨4503921, by rfl⟩ : syracuseStep 12010457 = 9007843) B9007843
theorem B8006971 : Blo 2107435 8006971 := bstep (se 1 (by rfl) ⟨6005228, by rfl⟩ : syracuseStep 8006971 = 12010457) B12010457
theorem B10675961 : Blo 2107435 10675961 := bstep (se 2 (by rfl) ⟨4003485, by rfl⟩ : syracuseStep 10675961 = 8006971) B8006971
theorem B7117307 : Blo 2107435 7117307 := bstep (se 1 (by rfl) ⟨5337980, by rfl⟩ : syracuseStep 7117307 = 10675961) B10675961
theorem B4744871 : Blo 2107435 4744871 := bstep (se 1 (by rfl) ⟨3558653, by rfl⟩ : syracuseStep 4744871 = 7117307) B7117307
theorem B3163247 : Blo 2107435 3163247 := bstep (se 1 (by rfl) ⟨2372435, by rfl⟩ : syracuseStep 3163247 = 4744871) B4744871
theorem B2108831 : Blo 2107435 2108831 := bstep (se 1 (by rfl) ⟨1581623, by rfl⟩ : syracuseStep 2108831 = 3163247) B3163247
theorem B3163253 : Blo 2107435 3163253 := bbase (se 5 (by rfl) ⟨148277, by rfl⟩ : syracuseStep 3163253 = 296555) (by norm_num)
theorem B2108835 : Blo 2107435 2108835 := bstep (se 1 (by rfl) ⟨1581626, by rfl⟩ : syracuseStep 2108835 = 3163253) B3163253
theorem B4003501 : Blo 2107435 4003501 := bbase (se 3 (by rfl) ⟨750656, by rfl⟩ : syracuseStep 4003501 = 1501313) (by norm_num)
theorem B5338001 : Blo 2107435 5338001 := bstep (se 2 (by rfl) ⟨2001750, by rfl⟩ : syracuseStep 5338001 = 4003501) B4003501
theorem B3558667 : Blo 2107435 3558667 := bstep (se 1 (by rfl) ⟨2669000, by rfl⟩ : syracuseStep 3558667 = 5338001) B5338001
theorem B4744889 : Blo 2107435 4744889 := bstep (se 2 (by rfl) ⟨1779333, by rfl⟩ : syracuseStep 4744889 = 3558667) B3558667
theorem B3163259 : Blo 2107435 3163259 := bstep (se 1 (by rfl) ⟨2372444, by rfl⟩ : syracuseStep 3163259 = 4744889) B4744889
theorem B2108839 : Blo 2107435 2108839 := bstep (se 1 (by rfl) ⟨1581629, by rfl⟩ : syracuseStep 2108839 = 3163259) B3163259
theorem B2372449 : Blo 2107435 2372449 := bbase (se 2 (by rfl) ⟨889668, by rfl⟩ : syracuseStep 2372449 = 1779337) (by norm_num)
theorem B3163265 : Blo 2107435 3163265 := bstep (se 2 (by rfl) ⟨1186224, by rfl⟩ : syracuseStep 3163265 = 2372449) B2372449
theorem B2108843 : Blo 2107435 2108843 := bstep (se 1 (by rfl) ⟨1581632, by rfl⟩ : syracuseStep 2108843 = 3163265) B3163265
theorem B5338021 : Blo 2107435 5338021 := bbase (se 4 (by rfl) ⟨500439, by rfl⟩ : syracuseStep 5338021 = 1000879) (by norm_num)
theorem B7117361 : Blo 2107435 7117361 := bstep (se 2 (by rfl) ⟨2669010, by rfl⟩ : syracuseStep 7117361 = 5338021) B5338021
theorem B4744907 : Blo 2107435 4744907 := bstep (se 1 (by rfl) ⟨3558680, by rfl⟩ : syracuseStep 4744907 = 7117361) B7117361
theorem B3163271 : Blo 2107435 3163271 := bstep (se 1 (by rfl) ⟨2372453, by rfl⟩ : syracuseStep 3163271 = 4744907) B4744907
theorem B2108847 : Blo 2107435 2108847 := bstep (se 1 (by rfl) ⟨1581635, by rfl⟩ : syracuseStep 2108847 = 3163271) B3163271
theorem B3163277 : Blo 2107435 3163277 := bbase (se 3 (by rfl) ⟨593114, by rfl⟩ : syracuseStep 3163277 = 1186229) (by norm_num)
theorem B2108851 : Blo 2107435 2108851 := bstep (se 1 (by rfl) ⟨1581638, by rfl⟩ : syracuseStep 2108851 = 3163277) B3163277
theorem B4744925 : Blo 2107435 4744925 := bbase (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) (by norm_num)
theorem B3163283 : Blo 2107435 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B2108855 : Blo 2107435 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B3558701 : Blo 2107435 3558701 := bbase (se 3 (by rfl) ⟨667256, by rfl⟩ : syracuseStep 3558701 = 1334513) (by norm_num)
theorem B2372467 : Blo 2107435 2372467 := bstep (se 1 (by rfl) ⟨1779350, by rfl⟩ : syracuseStep 2372467 = 3558701) B3558701
theorem B3163289 : Blo 2107435 3163289 := bstep (se 2 (by rfl) ⟨1186233, by rfl⟩ : syracuseStep 3163289 = 2372467) B2372467
theorem B2108859 : Blo 2107435 2108859 := bstep (se 1 (by rfl) ⟨1581644, by rfl⟩ : syracuseStep 2108859 = 3163289) B3163289
theorem B11400725 : Blo 2107435 11400725 := bbase (se 6 (by rfl) ⟨267204, by rfl⟩ : syracuseStep 11400725 = 534409) (by norm_num)
theorem B7600483 : Blo 2107435 7600483 := bstep (se 1 (by rfl) ⟨5700362, by rfl⟩ : syracuseStep 7600483 = 11400725) B11400725
theorem B40535909 : Blo 2107435 40535909 := bstep (se 4 (by rfl) ⟨3800241, by rfl⟩ : syracuseStep 40535909 = 7600483) B7600483
theorem B27023939 : Blo 2107435 27023939 := bstep (se 1 (by rfl) ⟨20267954, by rfl⟩ : syracuseStep 27023939 = 40535909) B40535909
theorem B18015959 : Blo 2107435 18015959 := bstep (se 1 (by rfl) ⟨13511969, by rfl⟩ : syracuseStep 18015959 = 27023939) B27023939
theorem B12010639 : Blo 2107435 12010639 := bstep (se 1 (by rfl) ⟨9007979, by rfl⟩ : syracuseStep 12010639 = 18015959) B18015959
theorem B16014185 : Blo 2107435 16014185 := bstep (se 2 (by rfl) ⟨6005319, by rfl⟩ : syracuseStep 16014185 = 12010639) B12010639
theorem B10676123 : Blo 2107435 10676123 := bstep (se 1 (by rfl) ⟨8007092, by rfl⟩ : syracuseStep 10676123 = 16014185) B16014185
theorem B7117415 : Blo 2107435 7117415 := bstep (se 1 (by rfl) ⟨5338061, by rfl⟩ : syracuseStep 7117415 = 10676123) B10676123
theorem B4744943 : Blo 2107435 4744943 := bstep (se 1 (by rfl) ⟨3558707, by rfl⟩ : syracuseStep 4744943 = 7117415) B7117415
theorem B3163295 : Blo 2107435 3163295 := bstep (se 1 (by rfl) ⟨2372471, by rfl⟩ : syracuseStep 3163295 = 4744943) B4744943
theorem B2108863 : Blo 2107435 2108863 := bstep (se 1 (by rfl) ⟨1581647, by rfl⟩ : syracuseStep 2108863 = 3163295) B3163295
theorem B3163301 : Blo 2107435 3163301 := bbase (se 4 (by rfl) ⟨296559, by rfl⟩ : syracuseStep 3163301 = 593119) (by norm_num)
theorem B2108867 : Blo 2107435 2108867 := bstep (se 1 (by rfl) ⟨1581650, by rfl⟩ : syracuseStep 2108867 = 3163301) B3163301
theorem B2669041 : Blo 2107435 2669041 := bbase (se 2 (by rfl) ⟨1000890, by rfl⟩ : syracuseStep 2669041 = 2001781) (by norm_num)
theorem B3558721 : Blo 2107435 3558721 := bstep (se 2 (by rfl) ⟨1334520, by rfl⟩ : syracuseStep 3558721 = 2669041) B2669041
theorem B4744961 : Blo 2107435 4744961 := bstep (se 2 (by rfl) ⟨1779360, by rfl⟩ : syracuseStep 4744961 = 3558721) B3558721
theorem B3163307 : Blo 2107435 3163307 := bstep (se 1 (by rfl) ⟨2372480, by rfl⟩ : syracuseStep 3163307 = 4744961) B4744961
theorem B2108871 : Blo 2107435 2108871 := bstep (se 1 (by rfl) ⟨1581653, by rfl⟩ : syracuseStep 2108871 = 3163307) B3163307
theorem B2372485 : Blo 2107435 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B3163313 : Blo 2107435 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B2108875 : Blo 2107435 2108875 := bstep (se 1 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 2108875 = 3163313) B3163313
theorem B5067029 : Blo 2107435 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B3378019 : Blo 2107435 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B4504025 : Blo 2107435 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B3002683 : Blo 2107435 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B4003577 : Blo 2107435 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B2669051 : Blo 2107435 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B7117469 : Blo 2107435 7117469 := bstep (se 3 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 7117469 = 2669051) B2669051
theorem B4744979 : Blo 2107435 4744979 := bstep (se 1 (by rfl) ⟨3558734, by rfl⟩ : syracuseStep 4744979 = 7117469) B7117469
theorem B3163319 : Blo 2107435 3163319 := bstep (se 1 (by rfl) ⟨2372489, by rfl⟩ : syracuseStep 3163319 = 4744979) B4744979
theorem B2108879 : Blo 2107435 2108879 := bstep (se 1 (by rfl) ⟨1581659, by rfl⟩ : syracuseStep 2108879 = 3163319) B3163319
theorem B3163325 : Blo 2107435 3163325 := bbase (se 3 (by rfl) ⟨593123, by rfl⟩ : syracuseStep 3163325 = 1186247) (by norm_num)
theorem B2108883 : Blo 2107435 2108883 := bstep (se 1 (by rfl) ⟨1581662, by rfl⟩ : syracuseStep 2108883 = 3163325) B3163325
theorem B4744997 : Blo 2107435 4744997 := bbase (se 4 (by rfl) ⟨444843, by rfl⟩ : syracuseStep 4744997 = 889687) (by norm_num)
theorem B3163331 : Blo 2107435 3163331 := bstep (se 1 (by rfl) ⟨2372498, by rfl⟩ : syracuseStep 3163331 = 4744997) B4744997
theorem B2108887 : Blo 2107435 2108887 := bstep (se 1 (by rfl) ⟨1581665, by rfl⟩ : syracuseStep 2108887 = 3163331) B3163331
theorem B5338133 : Blo 2107435 5338133 := bbase (se 6 (by rfl) ⟨125112, by rfl⟩ : syracuseStep 5338133 = 250225) (by norm_num)
theorem B3558755 : Blo 2107435 3558755 := bstep (se 1 (by rfl) ⟨2669066, by rfl⟩ : syracuseStep 3558755 = 5338133) B5338133
theorem B2372503 : Blo 2107435 2372503 := bstep (se 1 (by rfl) ⟨1779377, by rfl⟩ : syracuseStep 2372503 = 3558755) B3558755
theorem B3163337 : Blo 2107435 3163337 := bstep (se 2 (by rfl) ⟨1186251, by rfl⟩ : syracuseStep 3163337 = 2372503) B2372503
theorem B2108891 : Blo 2107435 2108891 := bstep (se 1 (by rfl) ⟨1581668, by rfl⟩ : syracuseStep 2108891 = 3163337) B3163337
theorem B9008117 : Blo 2107435 9008117 := bbase (se 5 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 9008117 = 844511) (by norm_num)
theorem B6005411 : Blo 2107435 6005411 := bstep (se 1 (by rfl) ⟨4504058, by rfl⟩ : syracuseStep 6005411 = 9008117) B9008117
theorem B4003607 : Blo 2107435 4003607 := bstep (se 1 (by rfl) ⟨3002705, by rfl⟩ : syracuseStep 4003607 = 6005411) B6005411
theorem B10676285 : Blo 2107435 10676285 := bstep (se 3 (by rfl) ⟨2001803, by rfl⟩ : syracuseStep 10676285 = 4003607) B4003607
theorem B7117523 : Blo 2107435 7117523 := bstep (se 1 (by rfl) ⟨5338142, by rfl⟩ : syracuseStep 7117523 = 10676285) B10676285
theorem B4745015 : Blo 2107435 4745015 := bstep (se 1 (by rfl) ⟨3558761, by rfl⟩ : syracuseStep 4745015 = 7117523) B7117523
theorem B3163343 : Blo 2107435 3163343 := bstep (se 1 (by rfl) ⟨2372507, by rfl⟩ : syracuseStep 3163343 = 4745015) B4745015
theorem B2108895 : Blo 2107435 2108895 := bstep (se 1 (by rfl) ⟨1581671, by rfl⟩ : syracuseStep 2108895 = 3163343) B3163343
theorem B3163349 : Blo 2107435 3163349 := bbase (se 7 (by rfl) ⟨37070, by rfl⟩ : syracuseStep 3163349 = 74141) (by norm_num)
theorem B2108899 : Blo 2107435 2108899 := bstep (se 1 (by rfl) ⟨1581674, by rfl⟩ : syracuseStep 2108899 = 3163349) B3163349
theorem B3002717 : Blo 2107435 3002717 := bbase (se 3 (by rfl) ⟨563009, by rfl⟩ : syracuseStep 3002717 = 1126019) (by norm_num)
theorem B8007245 : Blo 2107435 8007245 := bstep (se 3 (by rfl) ⟨1501358, by rfl⟩ : syracuseStep 8007245 = 3002717) B3002717
theorem B5338163 : Blo 2107435 5338163 := bstep (se 1 (by rfl) ⟨4003622, by rfl⟩ : syracuseStep 5338163 = 8007245) B8007245
theorem B3558775 : Blo 2107435 3558775 := bstep (se 1 (by rfl) ⟨2669081, by rfl⟩ : syracuseStep 3558775 = 5338163) B5338163
theorem B4745033 : Blo 2107435 4745033 := bstep (se 2 (by rfl) ⟨1779387, by rfl⟩ : syracuseStep 4745033 = 3558775) B3558775
theorem B3163355 : Blo 2107435 3163355 := bstep (se 1 (by rfl) ⟨2372516, by rfl⟩ : syracuseStep 3163355 = 4745033) B4745033
theorem B2108903 : Blo 2107435 2108903 := bstep (se 1 (by rfl) ⟨1581677, by rfl⟩ : syracuseStep 2108903 = 3163355) B3163355
theorem B2372521 : Blo 2107435 2372521 := bbase (se 2 (by rfl) ⟨889695, by rfl⟩ : syracuseStep 2372521 = 1779391) (by norm_num)
theorem B3163361 : Blo 2107435 3163361 := bstep (se 2 (by rfl) ⟨1186260, by rfl⟩ : syracuseStep 3163361 = 2372521) B2372521
theorem B2108907 : Blo 2107435 2108907 := bstep (se 1 (by rfl) ⟨1581680, by rfl⟩ : syracuseStep 2108907 = 3163361) B3163361
theorem B2137685 : Blo 2107435 2137685 := bbase (se 8 (by rfl) ⟨12525, by rfl⟩ : syracuseStep 2137685 = 25051) (by norm_num)
theorem B5700493 : Blo 2107435 5700493 := bstep (se 3 (by rfl) ⟨1068842, by rfl⟩ : syracuseStep 5700493 = 2137685) B2137685
theorem B7600657 : Blo 2107435 7600657 := bstep (se 2 (by rfl) ⟨2850246, by rfl⟩ : syracuseStep 7600657 = 5700493) B5700493
theorem B10134209 : Blo 2107435 10134209 := bstep (se 2 (by rfl) ⟨3800328, by rfl⟩ : syracuseStep 10134209 = 7600657) B7600657
theorem B6756139 : Blo 2107435 6756139 := bstep (se 1 (by rfl) ⟨5067104, by rfl⟩ : syracuseStep 6756139 = 10134209) B10134209
theorem B9008185 : Blo 2107435 9008185 := bstep (se 2 (by rfl) ⟨3378069, by rfl⟩ : syracuseStep 9008185 = 6756139) B6756139
theorem B12010913 : Blo 2107435 12010913 := bstep (se 2 (by rfl) ⟨4504092, by rfl⟩ : syracuseStep 12010913 = 9008185) B9008185
theorem B8007275 : Blo 2107435 8007275 := bstep (se 1 (by rfl) ⟨6005456, by rfl⟩ : syracuseStep 8007275 = 12010913) B12010913
theorem B5338183 : Blo 2107435 5338183 := bstep (se 1 (by rfl) ⟨4003637, by rfl⟩ : syracuseStep 5338183 = 8007275) B8007275
theorem B7117577 : Blo 2107435 7117577 := bstep (se 2 (by rfl) ⟨2669091, by rfl⟩ : syracuseStep 7117577 = 5338183) B5338183
theorem B4745051 : Blo 2107435 4745051 := bstep (se 1 (by rfl) ⟨3558788, by rfl⟩ : syracuseStep 4745051 = 7117577) B7117577
theorem B3163367 : Blo 2107435 3163367 := bstep (se 1 (by rfl) ⟨2372525, by rfl⟩ : syracuseStep 3163367 = 4745051) B4745051
theorem B2108911 : Blo 2107435 2108911 := bstep (se 1 (by rfl) ⟨1581683, by rfl⟩ : syracuseStep 2108911 = 3163367) B3163367
theorem B3163373 : Blo 2107435 3163373 := bbase (se 3 (by rfl) ⟨593132, by rfl⟩ : syracuseStep 3163373 = 1186265) (by norm_num)
theorem B2108915 : Blo 2107435 2108915 := bstep (se 1 (by rfl) ⟨1581686, by rfl⟩ : syracuseStep 2108915 = 3163373) B3163373
theorem B4745069 : Blo 2107435 4745069 := bbase (se 3 (by rfl) ⟨889700, by rfl⟩ : syracuseStep 4745069 = 1779401) (by norm_num)
theorem B3163379 : Blo 2107435 3163379 := bstep (se 1 (by rfl) ⟨2372534, by rfl⟩ : syracuseStep 3163379 = 4745069) B4745069
theorem B2108919 : Blo 2107435 2108919 := bstep (se 1 (by rfl) ⟨1581689, by rfl⟩ : syracuseStep 2108919 = 3163379) B3163379
theorem B4003661 : Blo 2107435 4003661 := bbase (se 3 (by rfl) ⟨750686, by rfl⟩ : syracuseStep 4003661 = 1501373) (by norm_num)
theorem B2669107 : Blo 2107435 2669107 := bstep (se 1 (by rfl) ⟨2001830, by rfl⟩ : syracuseStep 2669107 = 4003661) B4003661
theorem B3558809 : Blo 2107435 3558809 := bstep (se 2 (by rfl) ⟨1334553, by rfl⟩ : syracuseStep 3558809 = 2669107) B2669107
theorem B2372539 : Blo 2107435 2372539 := bstep (se 1 (by rfl) ⟨1779404, by rfl⟩ : syracuseStep 2372539 = 3558809) B3558809
theorem B3163385 : Blo 2107435 3163385 := bstep (se 2 (by rfl) ⟨1186269, by rfl⟩ : syracuseStep 3163385 = 2372539) B2372539
theorem B2108923 : Blo 2107435 2108923 := bstep (se 1 (by rfl) ⟨1581692, by rfl⟩ : syracuseStep 2108923 = 3163385) B3163385
theorem B7214741 : Blo 2107435 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B4809827 : Blo 2107435 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B12826205 : Blo 2107435 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B8550803 : Blo 2107435 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B22802141 : Blo 2107435 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B15201427 : Blo 2107435 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B20268569 : Blo 2107435 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B54049517 : Blo 2107435 54049517 := bstep (se 3 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 54049517 = 20268569) B20268569
theorem B36033011 : Blo 2107435 36033011 := bstep (se 1 (by rfl) ⟨27024758, by rfl⟩ : syracuseStep 36033011 = 54049517) B54049517
theorem B24022007 : Blo 2107435 24022007 := bstep (se 1 (by rfl) ⟨18016505, by rfl⟩ : syracuseStep 24022007 = 36033011) B36033011
theorem B16014671 : Blo 2107435 16014671 := bstep (se 1 (by rfl) ⟨12011003, by rfl⟩ : syracuseStep 16014671 = 24022007) B24022007
theorem B10676447 : Blo 2107435 10676447 := bstep (se 1 (by rfl) ⟨8007335, by rfl⟩ : syracuseStep 10676447 = 16014671) B16014671
theorem B7117631 : Blo 2107435 7117631 := bstep (se 1 (by rfl) ⟨5338223, by rfl⟩ : syracuseStep 7117631 = 10676447) B10676447
theorem B4745087 : Blo 2107435 4745087 := bstep (se 1 (by rfl) ⟨3558815, by rfl⟩ : syracuseStep 4745087 = 7117631) B7117631
theorem B3163391 : Blo 2107435 3163391 := bstep (se 1 (by rfl) ⟨2372543, by rfl⟩ : syracuseStep 3163391 = 4745087) B4745087
theorem B2108927 : Blo 2107435 2108927 := bstep (se 1 (by rfl) ⟨1581695, by rfl⟩ : syracuseStep 2108927 = 3163391) B3163391
theorem B3163397 : Blo 2107435 3163397 := bbase (se 4 (by rfl) ⟨296568, by rfl⟩ : syracuseStep 3163397 = 593137) (by norm_num)
theorem B2108931 : Blo 2107435 2108931 := bstep (se 1 (by rfl) ⟨1581698, by rfl⟩ : syracuseStep 2108931 = 3163397) B3163397
theorem B3558829 : Blo 2107435 3558829 := bbase (se 3 (by rfl) ⟨667280, by rfl⟩ : syracuseStep 3558829 = 1334561) (by norm_num)
theorem B4745105 : Blo 2107435 4745105 := bstep (se 2 (by rfl) ⟨1779414, by rfl⟩ : syracuseStep 4745105 = 3558829) B3558829
theorem B3163403 : Blo 2107435 3163403 := bstep (se 1 (by rfl) ⟨2372552, by rfl⟩ : syracuseStep 3163403 = 4745105) B4745105
theorem B2108935 : Blo 2107435 2108935 := bstep (se 1 (by rfl) ⟨1581701, by rfl⟩ : syracuseStep 2108935 = 3163403) B3163403
theorem B2372557 : Blo 2107435 2372557 := bbase (se 3 (by rfl) ⟨444854, by rfl⟩ : syracuseStep 2372557 = 889709) (by norm_num)
theorem B3163409 : Blo 2107435 3163409 := bstep (se 2 (by rfl) ⟨1186278, by rfl⟩ : syracuseStep 3163409 = 2372557) B2372557
theorem B2108939 : Blo 2107435 2108939 := bstep (se 1 (by rfl) ⟨1581704, by rfl⟩ : syracuseStep 2108939 = 3163409) B3163409
theorem B7117685 : Blo 2107435 7117685 := bbase (se 5 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 7117685 = 667283) (by norm_num)
theorem B4745123 : Blo 2107435 4745123 := bstep (se 1 (by rfl) ⟨3558842, by rfl⟩ : syracuseStep 4745123 = 7117685) B7117685
theorem B3163415 : Blo 2107435 3163415 := bstep (se 1 (by rfl) ⟨2372561, by rfl⟩ : syracuseStep 3163415 = 4745123) B4745123
theorem B2108943 : Blo 2107435 2108943 := bstep (se 1 (by rfl) ⟨1581707, by rfl⟩ : syracuseStep 2108943 = 3163415) B3163415
theorem B3163421 : Blo 2107435 3163421 := bbase (se 3 (by rfl) ⟨593141, by rfl⟩ : syracuseStep 3163421 = 1186283) (by norm_num)
theorem B2108947 : Blo 2107435 2108947 := bstep (se 1 (by rfl) ⟨1581710, by rfl⟩ : syracuseStep 2108947 = 3163421) B3163421
theorem B4745141 : Blo 2107435 4745141 := bbase (se 5 (by rfl) ⟨222428, by rfl⟩ : syracuseStep 4745141 = 444857) (by norm_num)
theorem B3163427 : Blo 2107435 3163427 := bstep (se 1 (by rfl) ⟨2372570, by rfl⟩ : syracuseStep 3163427 = 4745141) B4745141
theorem B2108951 : Blo 2107435 2108951 := bstep (se 1 (by rfl) ⟨1581713, by rfl⟩ : syracuseStep 2108951 = 3163427) B3163427
theorem B5700613 : Blo 2107435 5700613 := bbase (se 4 (by rfl) ⟨534432, by rfl⟩ : syracuseStep 5700613 = 1068865) (by norm_num)
theorem B7600817 : Blo 2107435 7600817 := bstep (se 2 (by rfl) ⟨2850306, by rfl⟩ : syracuseStep 7600817 = 5700613) B5700613
theorem B5067211 : Blo 2107435 5067211 := bstep (se 1 (by rfl) ⟨3800408, by rfl⟩ : syracuseStep 5067211 = 7600817) B7600817
theorem B6756281 : Blo 2107435 6756281 := bstep (se 2 (by rfl) ⟨2533605, by rfl⟩ : syracuseStep 6756281 = 5067211) B5067211
theorem B4504187 : Blo 2107435 4504187 := bstep (se 1 (by rfl) ⟨3378140, by rfl⟩ : syracuseStep 4504187 = 6756281) B6756281
theorem B12011165 : Blo 2107435 12011165 := bstep (se 3 (by rfl) ⟨2252093, by rfl⟩ : syracuseStep 12011165 = 4504187) B4504187
theorem B8007443 : Blo 2107435 8007443 := bstep (se 1 (by rfl) ⟨6005582, by rfl⟩ : syracuseStep 8007443 = 12011165) B12011165
theorem B5338295 : Blo 2107435 5338295 := bstep (se 1 (by rfl) ⟨4003721, by rfl⟩ : syracuseStep 5338295 = 8007443) B8007443
theorem B3558863 : Blo 2107435 3558863 := bstep (se 1 (by rfl) ⟨2669147, by rfl⟩ : syracuseStep 3558863 = 5338295) B5338295
theorem B2372575 : Blo 2107435 2372575 := bstep (se 1 (by rfl) ⟨1779431, by rfl⟩ : syracuseStep 2372575 = 3558863) B3558863
theorem B3163433 : Blo 2107435 3163433 := bstep (se 2 (by rfl) ⟨1186287, by rfl⟩ : syracuseStep 3163433 = 2372575) B2372575
theorem B2108955 : Blo 2107435 2108955 := bstep (se 1 (by rfl) ⟨1581716, by rfl⟩ : syracuseStep 2108955 = 3163433) B3163433
theorem B6756293 : Blo 2107435 6756293 := bbase (se 4 (by rfl) ⟨633402, by rfl⟩ : syracuseStep 6756293 = 1266805) (by norm_num)
theorem B4504195 : Blo 2107435 4504195 := bstep (se 1 (by rfl) ⟨3378146, by rfl⟩ : syracuseStep 4504195 = 6756293) B6756293
theorem B6005593 : Blo 2107435 6005593 := bstep (se 2 (by rfl) ⟨2252097, by rfl⟩ : syracuseStep 6005593 = 4504195) B4504195
theorem B8007457 : Blo 2107435 8007457 := bstep (se 2 (by rfl) ⟨3002796, by rfl⟩ : syracuseStep 8007457 = 6005593) B6005593
theorem B10676609 : Blo 2107435 10676609 := bstep (se 2 (by rfl) ⟨4003728, by rfl⟩ : syracuseStep 10676609 = 8007457) B8007457
theorem B7117739 : Blo 2107435 7117739 := bstep (se 1 (by rfl) ⟨5338304, by rfl⟩ : syracuseStep 7117739 = 10676609) B10676609
theorem B4745159 : Blo 2107435 4745159 := bstep (se 1 (by rfl) ⟨3558869, by rfl⟩ : syracuseStep 4745159 = 7117739) B7117739
theorem B3163439 : Blo 2107435 3163439 := bstep (se 1 (by rfl) ⟨2372579, by rfl⟩ : syracuseStep 3163439 = 4745159) B4745159
theorem B2108959 : Blo 2107435 2108959 := bstep (se 1 (by rfl) ⟨1581719, by rfl⟩ : syracuseStep 2108959 = 3163439) B3163439
theorem B3163445 : Blo 2107435 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B2108963 : Blo 2107435 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B5338325 : Blo 2107435 5338325 := bbase (se 7 (by rfl) ⟨62558, by rfl⟩ : syracuseStep 5338325 = 125117) (by norm_num)
theorem B3558883 : Blo 2107435 3558883 := bstep (se 1 (by rfl) ⟨2669162, by rfl⟩ : syracuseStep 3558883 = 5338325) B5338325
theorem B4745177 : Blo 2107435 4745177 := bstep (se 2 (by rfl) ⟨1779441, by rfl⟩ : syracuseStep 4745177 = 3558883) B3558883
theorem B3163451 : Blo 2107435 3163451 := bstep (se 1 (by rfl) ⟨2372588, by rfl⟩ : syracuseStep 3163451 = 4745177) B4745177
theorem B2108967 : Blo 2107435 2108967 := bstep (se 1 (by rfl) ⟨1581725, by rfl⟩ : syracuseStep 2108967 = 3163451) B3163451
theorem B2372593 : Blo 2107435 2372593 := bbase (se 2 (by rfl) ⟨889722, by rfl⟩ : syracuseStep 2372593 = 1779445) (by norm_num)
theorem B3163457 : Blo 2107435 3163457 := bstep (se 2 (by rfl) ⟨1186296, by rfl⟩ : syracuseStep 3163457 = 2372593) B2372593
theorem B2108971 : Blo 2107435 2108971 := bstep (se 1 (by rfl) ⟨1581728, by rfl⟩ : syracuseStep 2108971 = 3163457) B3163457
theorem B10134517 : Blo 2107435 10134517 := bbase (se 5 (by rfl) ⟨475055, by rfl⟩ : syracuseStep 10134517 = 950111) (by norm_num)
theorem B13512689 : Blo 2107435 13512689 := bstep (se 2 (by rfl) ⟨5067258, by rfl⟩ : syracuseStep 13512689 = 10134517) B10134517
theorem B9008459 : Blo 2107435 9008459 := bstep (se 1 (by rfl) ⟨6756344, by rfl⟩ : syracuseStep 9008459 = 13512689) B13512689
theorem B6005639 : Blo 2107435 6005639 := bstep (se 1 (by rfl) ⟨4504229, by rfl⟩ : syracuseStep 6005639 = 9008459) B9008459
theorem B4003759 : Blo 2107435 4003759 := bstep (se 1 (by rfl) ⟨3002819, by rfl⟩ : syracuseStep 4003759 = 6005639) B6005639
theorem B5338345 : Blo 2107435 5338345 := bstep (se 2 (by rfl) ⟨2001879, by rfl⟩ : syracuseStep 5338345 = 4003759) B4003759
theorem B7117793 : Blo 2107435 7117793 := bstep (se 2 (by rfl) ⟨2669172, by rfl⟩ : syracuseStep 7117793 = 5338345) B5338345
theorem B4745195 : Blo 2107435 4745195 := bstep (se 1 (by rfl) ⟨3558896, by rfl⟩ : syracuseStep 4745195 = 7117793) B7117793
theorem B3163463 : Blo 2107435 3163463 := bstep (se 1 (by rfl) ⟨2372597, by rfl⟩ : syracuseStep 3163463 = 4745195) B4745195
theorem B2108975 : Blo 2107435 2108975 := bstep (se 1 (by rfl) ⟨1581731, by rfl⟩ : syracuseStep 2108975 = 3163463) B3163463
theorem B3163469 : Blo 2107435 3163469 := bbase (se 3 (by rfl) ⟨593150, by rfl⟩ : syracuseStep 3163469 = 1186301) (by norm_num)
theorem B2108979 : Blo 2107435 2108979 := bstep (se 1 (by rfl) ⟨1581734, by rfl⟩ : syracuseStep 2108979 = 3163469) B3163469
theorem B4745213 : Blo 2107435 4745213 := bbase (se 3 (by rfl) ⟨889727, by rfl⟩ : syracuseStep 4745213 = 1779455) (by norm_num)
theorem B3163475 : Blo 2107435 3163475 := bstep (se 1 (by rfl) ⟨2372606, by rfl⟩ : syracuseStep 3163475 = 4745213) B4745213
theorem B2108983 : Blo 2107435 2108983 := bstep (se 1 (by rfl) ⟨1581737, by rfl⟩ : syracuseStep 2108983 = 3163475) B3163475
theorem B3558917 : Blo 2107435 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B2372611 : Blo 2107435 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B3163481 : Blo 2107435 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B2108987 : Blo 2107435 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B16015157 : Blo 2107435 16015157 := bbase (se 5 (by rfl) ⟨750710, by rfl⟩ : syracuseStep 16015157 = 1501421) (by norm_num)
theorem B10676771 : Blo 2107435 10676771 := bstep (se 1 (by rfl) ⟨8007578, by rfl⟩ : syracuseStep 10676771 = 16015157) B16015157
theorem B7117847 : Blo 2107435 7117847 := bstep (se 1 (by rfl) ⟨5338385, by rfl⟩ : syracuseStep 7117847 = 10676771) B10676771
theorem B4745231 : Blo 2107435 4745231 := bstep (se 1 (by rfl) ⟨3558923, by rfl⟩ : syracuseStep 4745231 = 7117847) B7117847
theorem B3163487 : Blo 2107435 3163487 := bstep (se 1 (by rfl) ⟨2372615, by rfl⟩ : syracuseStep 3163487 = 4745231) B4745231
theorem B2108991 : Blo 2107435 2108991 := bstep (se 1 (by rfl) ⟨1581743, by rfl⟩ : syracuseStep 2108991 = 3163487) B3163487
theorem B3163493 : Blo 2107435 3163493 := bbase (se 4 (by rfl) ⟨296577, by rfl⟩ : syracuseStep 3163493 = 593155) (by norm_num)
theorem B2108995 : Blo 2107435 2108995 := bstep (se 1 (by rfl) ⟨1581746, by rfl⟩ : syracuseStep 2108995 = 3163493) B3163493
theorem B4003805 : Blo 2107435 4003805 := bbase (se 3 (by rfl) ⟨750713, by rfl⟩ : syracuseStep 4003805 = 1501427) (by norm_num)
theorem B2669203 : Blo 2107435 2669203 := bstep (se 1 (by rfl) ⟨2001902, by rfl⟩ : syracuseStep 2669203 = 4003805) B4003805
theorem B3558937 : Blo 2107435 3558937 := bstep (se 2 (by rfl) ⟨1334601, by rfl⟩ : syracuseStep 3558937 = 2669203) B2669203
theorem B4745249 : Blo 2107435 4745249 := bstep (se 2 (by rfl) ⟨1779468, by rfl⟩ : syracuseStep 4745249 = 3558937) B3558937
theorem B3163499 : Blo 2107435 3163499 := bstep (se 1 (by rfl) ⟨2372624, by rfl⟩ : syracuseStep 3163499 = 4745249) B4745249
theorem B2108999 : Blo 2107435 2108999 := bstep (se 1 (by rfl) ⟨1581749, by rfl⟩ : syracuseStep 2108999 = 3163499) B3163499
theorem B2372629 : Blo 2107435 2372629 := bbase (se 6 (by rfl) ⟨55608, by rfl⟩ : syracuseStep 2372629 = 111217) (by norm_num)
theorem B3163505 : Blo 2107435 3163505 := bstep (se 2 (by rfl) ⟨1186314, by rfl⟩ : syracuseStep 3163505 = 2372629) B2372629
theorem B2109003 : Blo 2107435 2109003 := bstep (se 1 (by rfl) ⟨1581752, by rfl⟩ : syracuseStep 2109003 = 3163505) B3163505
theorem B2669213 : Blo 2107435 2669213 := bbase (se 3 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 2669213 = 1000955) (by norm_num)
theorem B7117901 : Blo 2107435 7117901 := bstep (se 3 (by rfl) ⟨1334606, by rfl⟩ : syracuseStep 7117901 = 2669213) B2669213
theorem B4745267 : Blo 2107435 4745267 := bstep (se 1 (by rfl) ⟨3558950, by rfl⟩ : syracuseStep 4745267 = 7117901) B7117901
theorem B3163511 : Blo 2107435 3163511 := bstep (se 1 (by rfl) ⟨2372633, by rfl⟩ : syracuseStep 3163511 = 4745267) B4745267
theorem B2109007 : Blo 2107435 2109007 := bstep (se 1 (by rfl) ⟨1581755, by rfl⟩ : syracuseStep 2109007 = 3163511) B3163511
theorem B3163517 : Blo 2107435 3163517 := bbase (se 3 (by rfl) ⟨593159, by rfl⟩ : syracuseStep 3163517 = 1186319) (by norm_num)
theorem B2109011 : Blo 2107435 2109011 := bstep (se 1 (by rfl) ⟨1581758, by rfl⟩ : syracuseStep 2109011 = 3163517) B3163517
theorem B4745285 : Blo 2107435 4745285 := bbase (se 4 (by rfl) ⟨444870, by rfl⟩ : syracuseStep 4745285 = 889741) (by norm_num)
theorem B3163523 : Blo 2107435 3163523 := bstep (se 1 (by rfl) ⟨2372642, by rfl⟩ : syracuseStep 3163523 = 4745285) B4745285
theorem B2109015 : Blo 2107435 2109015 := bstep (se 1 (by rfl) ⟨1581761, by rfl⟩ : syracuseStep 2109015 = 3163523) B3163523
theorem B6005765 : Blo 2107435 6005765 := bbase (se 4 (by rfl) ⟨563040, by rfl⟩ : syracuseStep 6005765 = 1126081) (by norm_num)
theorem B4003843 : Blo 2107435 4003843 := bstep (se 1 (by rfl) ⟨3002882, by rfl⟩ : syracuseStep 4003843 = 6005765) B6005765
theorem B5338457 : Blo 2107435 5338457 := bstep (se 2 (by rfl) ⟨2001921, by rfl⟩ : syracuseStep 5338457 = 4003843) B4003843
theorem B3558971 : Blo 2107435 3558971 := bstep (se 1 (by rfl) ⟨2669228, by rfl⟩ : syracuseStep 3558971 = 5338457) B5338457
theorem B2372647 : Blo 2107435 2372647 := bstep (se 1 (by rfl) ⟨1779485, by rfl⟩ : syracuseStep 2372647 = 3558971) B3558971
theorem B3163529 : Blo 2107435 3163529 := bstep (se 2 (by rfl) ⟨1186323, by rfl⟩ : syracuseStep 3163529 = 2372647) B2372647
theorem B2109019 : Blo 2107435 2109019 := bstep (se 1 (by rfl) ⟨1581764, by rfl⟩ : syracuseStep 2109019 = 3163529) B3163529
theorem B10676933 : Blo 2107435 10676933 := bbase (se 4 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 10676933 = 2001925) (by norm_num)
theorem B7117955 : Blo 2107435 7117955 := bstep (se 1 (by rfl) ⟨5338466, by rfl⟩ : syracuseStep 7117955 = 10676933) B10676933
theorem B4745303 : Blo 2107435 4745303 := bstep (se 1 (by rfl) ⟨3558977, by rfl⟩ : syracuseStep 4745303 = 7117955) B7117955
theorem B3163535 : Blo 2107435 3163535 := bstep (se 1 (by rfl) ⟨2372651, by rfl⟩ : syracuseStep 3163535 = 4745303) B4745303
theorem B2109023 : Blo 2107435 2109023 := bstep (se 1 (by rfl) ⟨1581767, by rfl⟩ : syracuseStep 2109023 = 3163535) B3163535
theorem B3163541 : Blo 2107435 3163541 := bbase (se 6 (by rfl) ⟨74145, by rfl⟩ : syracuseStep 3163541 = 148291) (by norm_num)
theorem B2109027 : Blo 2107435 2109027 := bstep (se 1 (by rfl) ⟨1581770, by rfl⟩ : syracuseStep 2109027 = 3163541) B3163541
theorem B4504349 : Blo 2107435 4504349 := bbase (se 3 (by rfl) ⟨844565, by rfl⟩ : syracuseStep 4504349 = 1689131) (by norm_num)
theorem B12011597 : Blo 2107435 12011597 := bstep (se 3 (by rfl) ⟨2252174, by rfl⟩ : syracuseStep 12011597 = 4504349) B4504349
theorem B8007731 : Blo 2107435 8007731 := bstep (se 1 (by rfl) ⟨6005798, by rfl⟩ : syracuseStep 8007731 = 12011597) B12011597
theorem B5338487 : Blo 2107435 5338487 := bstep (se 1 (by rfl) ⟨4003865, by rfl⟩ : syracuseStep 5338487 = 8007731) B8007731
theorem B3558991 : Blo 2107435 3558991 := bstep (se 1 (by rfl) ⟨2669243, by rfl⟩ : syracuseStep 3558991 = 5338487) B5338487
theorem B4745321 : Blo 2107435 4745321 := bstep (se 2 (by rfl) ⟨1779495, by rfl⟩ : syracuseStep 4745321 = 3558991) B3558991
theorem B3163547 : Blo 2107435 3163547 := bstep (se 1 (by rfl) ⟨2372660, by rfl⟩ : syracuseStep 3163547 = 4745321) B4745321
theorem B2109031 : Blo 2107435 2109031 := bstep (se 1 (by rfl) ⟨1581773, by rfl⟩ : syracuseStep 2109031 = 3163547) B3163547
theorem B2372665 : Blo 2107435 2372665 := bbase (se 2 (by rfl) ⟨889749, by rfl⟩ : syracuseStep 2372665 = 1779499) (by norm_num)
theorem B3163553 : Blo 2107435 3163553 := bstep (se 2 (by rfl) ⟨1186332, by rfl⟩ : syracuseStep 3163553 = 2372665) B2372665
theorem B2109035 : Blo 2107435 2109035 := bstep (se 1 (by rfl) ⟨1581776, by rfl⟩ : syracuseStep 2109035 = 3163553) B3163553
theorem B5067413 : Blo 2107435 5067413 := bbase (se 6 (by rfl) ⟨118767, by rfl⟩ : syracuseStep 5067413 = 237535) (by norm_num)
theorem B3378275 : Blo 2107435 3378275 := bstep (se 1 (by rfl) ⟨2533706, by rfl⟩ : syracuseStep 3378275 = 5067413) B5067413
theorem B2252183 : Blo 2107435 2252183 := bstep (se 1 (by rfl) ⟨1689137, by rfl⟩ : syracuseStep 2252183 = 3378275) B3378275
theorem B6005821 : Blo 2107435 6005821 := bstep (se 3 (by rfl) ⟨1126091, by rfl⟩ : syracuseStep 6005821 = 2252183) B2252183
theorem B8007761 : Blo 2107435 8007761 := bstep (se 2 (by rfl) ⟨3002910, by rfl⟩ : syracuseStep 8007761 = 6005821) B6005821
theorem B5338507 : Blo 2107435 5338507 := bstep (se 1 (by rfl) ⟨4003880, by rfl⟩ : syracuseStep 5338507 = 8007761) B8007761
theorem B7118009 : Blo 2107435 7118009 := bstep (se 2 (by rfl) ⟨2669253, by rfl⟩ : syracuseStep 7118009 = 5338507) B5338507
theorem B4745339 : Blo 2107435 4745339 := bstep (se 1 (by rfl) ⟨3559004, by rfl⟩ : syracuseStep 4745339 = 7118009) B7118009
theorem B3163559 : Blo 2107435 3163559 := bstep (se 1 (by rfl) ⟨2372669, by rfl⟩ : syracuseStep 3163559 = 4745339) B4745339
theorem B2109039 : Blo 2107435 2109039 := bstep (se 1 (by rfl) ⟨1581779, by rfl⟩ : syracuseStep 2109039 = 3163559) B3163559
theorem B3163565 : Blo 2107435 3163565 := bbase (se 3 (by rfl) ⟨593168, by rfl⟩ : syracuseStep 3163565 = 1186337) (by norm_num)
theorem B2109043 : Blo 2107435 2109043 := bstep (se 1 (by rfl) ⟨1581782, by rfl⟩ : syracuseStep 2109043 = 3163565) B3163565
theorem B4745357 : Blo 2107435 4745357 := bbase (se 3 (by rfl) ⟨889754, by rfl⟩ : syracuseStep 4745357 = 1779509) (by norm_num)
theorem B3163571 : Blo 2107435 3163571 := bstep (se 1 (by rfl) ⟨2372678, by rfl⟩ : syracuseStep 3163571 = 4745357) B4745357
theorem B2109047 : Blo 2107435 2109047 := bstep (se 1 (by rfl) ⟨1581785, by rfl⟩ : syracuseStep 2109047 = 3163571) B3163571
theorem B2669269 : Blo 2107435 2669269 := bbase (se 7 (by rfl) ⟨31280, by rfl⟩ : syracuseStep 2669269 = 62561) (by norm_num)
theorem B3559025 : Blo 2107435 3559025 := bstep (se 2 (by rfl) ⟨1334634, by rfl⟩ : syracuseStep 3559025 = 2669269) B2669269
theorem B2372683 : Blo 2107435 2372683 := bstep (se 1 (by rfl) ⟨1779512, by rfl⟩ : syracuseStep 2372683 = 3559025) B3559025
theorem B3163577 : Blo 2107435 3163577 := bstep (se 2 (by rfl) ⟨1186341, by rfl⟩ : syracuseStep 3163577 = 2372683) B2372683
theorem B2109051 : Blo 2107435 2109051 := bstep (se 1 (by rfl) ⟨1581788, by rfl⟩ : syracuseStep 2109051 = 3163577) B3163577
theorem B4067029 : Blo 2107435 4067029 := bbase (se 7 (by rfl) ⟨47660, by rfl⟩ : syracuseStep 4067029 = 95321) (by norm_num)
theorem B21690821 : Blo 2107435 21690821 := bstep (se 4 (by rfl) ⟨2033514, by rfl⟩ : syracuseStep 21690821 = 4067029) B4067029
theorem B14460547 : Blo 2107435 14460547 := bstep (se 1 (by rfl) ⟨10845410, by rfl⟩ : syracuseStep 14460547 = 21690821) B21690821
theorem B19280729 : Blo 2107435 19280729 := bstep (se 2 (by rfl) ⟨7230273, by rfl⟩ : syracuseStep 19280729 = 14460547) B14460547
theorem B12853819 : Blo 2107435 12853819 := bstep (se 1 (by rfl) ⟨9640364, by rfl⟩ : syracuseStep 12853819 = 19280729) B19280729
theorem B17138425 : Blo 2107435 17138425 := bstep (se 2 (by rfl) ⟨6426909, by rfl⟩ : syracuseStep 17138425 = 12853819) B12853819
theorem B22851233 : Blo 2107435 22851233 := bstep (se 2 (by rfl) ⟨8569212, by rfl⟩ : syracuseStep 22851233 = 17138425) B17138425
theorem B15234155 : Blo 2107435 15234155 := bstep (se 1 (by rfl) ⟨11425616, by rfl⟩ : syracuseStep 15234155 = 22851233) B22851233
theorem B10156103 : Blo 2107435 10156103 := bstep (se 1 (by rfl) ⟨7617077, by rfl⟩ : syracuseStep 10156103 = 15234155) B15234155
theorem B6770735 : Blo 2107435 6770735 := bstep (se 1 (by rfl) ⟨5078051, by rfl⟩ : syracuseStep 6770735 = 10156103) B10156103
theorem B4513823 : Blo 2107435 4513823 := bstep (se 1 (by rfl) ⟨3385367, by rfl⟩ : syracuseStep 4513823 = 6770735) B6770735
theorem B3009215 : Blo 2107435 3009215 := bstep (se 1 (by rfl) ⟨2256911, by rfl⟩ : syracuseStep 3009215 = 4513823) B4513823
theorem B8024573 : Blo 2107435 8024573 := bstep (se 3 (by rfl) ⟨1504607, by rfl⟩ : syracuseStep 8024573 = 3009215) B3009215
theorem B5349715 : Blo 2107435 5349715 := bstep (se 1 (by rfl) ⟨4012286, by rfl⟩ : syracuseStep 5349715 = 8024573) B8024573
theorem B28531813 : Blo 2107435 28531813 := bstep (se 4 (by rfl) ⟨2674857, by rfl⟩ : syracuseStep 28531813 = 5349715) B5349715
theorem B38042417 : Blo 2107435 38042417 := bstep (se 2 (by rfl) ⟨14265906, by rfl⟩ : syracuseStep 38042417 = 28531813) B28531813
theorem B101446445 : Blo 2107435 101446445 := bstep (se 3 (by rfl) ⟨19021208, by rfl⟩ : syracuseStep 101446445 = 38042417) B38042417
theorem B67630963 : Blo 2107435 67630963 := bstep (se 1 (by rfl) ⟨50723222, by rfl⟩ : syracuseStep 67630963 = 101446445) B101446445
theorem B90174617 : Blo 2107435 90174617 := bstep (se 2 (by rfl) ⟨33815481, by rfl⟩ : syracuseStep 90174617 = 67630963) B67630963
theorem B60116411 : Blo 2107435 60116411 := bstep (se 1 (by rfl) ⟨45087308, by rfl⟩ : syracuseStep 60116411 = 90174617) B90174617
theorem B40077607 : Blo 2107435 40077607 := bstep (se 1 (by rfl) ⟨30058205, by rfl⟩ : syracuseStep 40077607 = 60116411) B60116411
theorem B53436809 : Blo 2107435 53436809 := bstep (se 2 (by rfl) ⟨20038803, by rfl⟩ : syracuseStep 53436809 = 40077607) B40077607
theorem B35624539 : Blo 2107435 35624539 := bstep (se 1 (by rfl) ⟨26718404, by rfl⟩ : syracuseStep 35624539 = 53436809) B53436809
theorem B47499385 : Blo 2107435 47499385 := bstep (se 2 (by rfl) ⟨17812269, by rfl⟩ : syracuseStep 47499385 = 35624539) B35624539
theorem B63332513 : Blo 2107435 63332513 := bstep (se 2 (by rfl) ⟨23749692, by rfl⟩ : syracuseStep 63332513 = 47499385) B47499385
theorem B42221675 : Blo 2107435 42221675 := bstep (se 1 (by rfl) ⟨31666256, by rfl⟩ : syracuseStep 42221675 = 63332513) B63332513
theorem B28147783 : Blo 2107435 28147783 := bstep (se 1 (by rfl) ⟨21110837, by rfl⟩ : syracuseStep 28147783 = 42221675) B42221675
theorem B37530377 : Blo 2107435 37530377 := bstep (se 2 (by rfl) ⟨14073891, by rfl⟩ : syracuseStep 37530377 = 28147783) B28147783
theorem B25020251 : Blo 2107435 25020251 := bstep (se 1 (by rfl) ⟨18765188, by rfl⟩ : syracuseStep 25020251 = 37530377) B37530377
theorem B16680167 : Blo 2107435 16680167 := bstep (se 1 (by rfl) ⟨12510125, by rfl⟩ : syracuseStep 16680167 = 25020251) B25020251
theorem B11120111 : Blo 2107435 11120111 := bstep (se 1 (by rfl) ⟨8340083, by rfl⟩ : syracuseStep 11120111 = 16680167) B16680167
theorem B7413407 : Blo 2107435 7413407 := bstep (se 1 (by rfl) ⟨5560055, by rfl⟩ : syracuseStep 7413407 = 11120111) B11120111
theorem B4942271 : Blo 2107435 4942271 := bstep (se 1 (by rfl) ⟨3706703, by rfl⟩ : syracuseStep 4942271 = 7413407) B7413407
theorem B3294847 : Blo 2107435 3294847 := bstep (se 1 (by rfl) ⟨2471135, by rfl⟩ : syracuseStep 3294847 = 4942271) B4942271
theorem B4393129 : Blo 2107435 4393129 := bstep (se 2 (by rfl) ⟨1647423, by rfl⟩ : syracuseStep 4393129 = 3294847) B3294847
theorem B5857505 : Blo 2107435 5857505 := bstep (se 2 (by rfl) ⟨2196564, by rfl⟩ : syracuseStep 5857505 = 4393129) B4393129
theorem B3905003 : Blo 2107435 3905003 := bstep (se 1 (by rfl) ⟨2928752, by rfl⟩ : syracuseStep 3905003 = 5857505) B5857505
theorem B2603335 : Blo 2107435 2603335 := bstep (se 1 (by rfl) ⟨1952501, by rfl⟩ : syracuseStep 2603335 = 3905003) B3905003
theorem B3471113 : Blo 2107435 3471113 := bstep (se 2 (by rfl) ⟨1301667, by rfl⟩ : syracuseStep 3471113 = 2603335) B2603335
theorem B9256301 : Blo 2107435 9256301 := bstep (se 3 (by rfl) ⟨1735556, by rfl⟩ : syracuseStep 9256301 = 3471113) B3471113
theorem B6170867 : Blo 2107435 6170867 := bstep (se 1 (by rfl) ⟨4628150, by rfl⟩ : syracuseStep 6170867 = 9256301) B9256301
theorem B4113911 : Blo 2107435 4113911 := bstep (se 1 (by rfl) ⟨3085433, by rfl⟩ : syracuseStep 4113911 = 6170867) B6170867
theorem B2742607 : Blo 2107435 2742607 := bstep (se 1 (by rfl) ⟨2056955, by rfl⟩ : syracuseStep 2742607 = 4113911) B4113911
theorem B3656809 : Blo 2107435 3656809 := bstep (se 2 (by rfl) ⟨1371303, by rfl⟩ : syracuseStep 3656809 = 2742607) B2742607
theorem B4875745 : Blo 2107435 4875745 := bstep (se 2 (by rfl) ⟨1828404, by rfl⟩ : syracuseStep 4875745 = 3656809) B3656809
theorem B6500993 : Blo 2107435 6500993 := bstep (se 2 (by rfl) ⟨2437872, by rfl⟩ : syracuseStep 6500993 = 4875745) B4875745
theorem B17335981 : Blo 2107435 17335981 := bstep (se 3 (by rfl) ⟨3250496, by rfl⟩ : syracuseStep 17335981 = 6500993) B6500993
theorem B23114641 : Blo 2107435 23114641 := bstep (se 2 (by rfl) ⟨8667990, by rfl⟩ : syracuseStep 23114641 = 17335981) B17335981
theorem B30819521 : Blo 2107435 30819521 := bstep (se 2 (by rfl) ⟨11557320, by rfl⟩ : syracuseStep 30819521 = 23114641) B23114641
theorem B20546347 : Blo 2107435 20546347 := bstep (se 1 (by rfl) ⟨15409760, by rfl⟩ : syracuseStep 20546347 = 30819521) B30819521
theorem B27395129 : Blo 2107435 27395129 := bstep (se 2 (by rfl) ⟨10273173, by rfl⟩ : syracuseStep 27395129 = 20546347) B20546347
theorem B73053677 : Blo 2107435 73053677 := bstep (se 3 (by rfl) ⟨13697564, by rfl⟩ : syracuseStep 73053677 = 27395129) B27395129
theorem B194809805 : Blo 2107435 194809805 := bstep (se 3 (by rfl) ⟨36526838, by rfl⟩ : syracuseStep 194809805 = 73053677) B73053677
theorem B129873203 : Blo 2107435 129873203 := bstep (se 1 (by rfl) ⟨97404902, by rfl⟩ : syracuseStep 129873203 = 194809805) B194809805
theorem B86582135 : Blo 2107435 86582135 := bstep (se 1 (by rfl) ⟨64936601, by rfl⟩ : syracuseStep 86582135 = 129873203) B129873203
theorem B57721423 : Blo 2107435 57721423 := bstep (se 1 (by rfl) ⟨43291067, by rfl⟩ : syracuseStep 57721423 = 86582135) B86582135
theorem B76961897 : Blo 2107435 76961897 := bstep (se 2 (by rfl) ⟨28860711, by rfl⟩ : syracuseStep 76961897 = 57721423) B57721423
theorem B51307931 : Blo 2107435 51307931 := bstep (se 1 (by rfl) ⟨38480948, by rfl⟩ : syracuseStep 51307931 = 76961897) B76961897
theorem B136821149 : Blo 2107435 136821149 := bstep (se 3 (by rfl) ⟨25653965, by rfl⟩ : syracuseStep 136821149 = 51307931) B51307931
theorem B91214099 : Blo 2107435 91214099 := bstep (se 1 (by rfl) ⟨68410574, by rfl⟩ : syracuseStep 91214099 = 136821149) B136821149
theorem B60809399 : Blo 2107435 60809399 := bstep (se 1 (by rfl) ⟨45607049, by rfl⟩ : syracuseStep 60809399 = 91214099) B91214099
theorem B40539599 : Blo 2107435 40539599 := bstep (se 1 (by rfl) ⟨30404699, by rfl⟩ : syracuseStep 40539599 = 60809399) B60809399
theorem B27026399 : Blo 2107435 27026399 := bstep (se 1 (by rfl) ⟨20269799, by rfl⟩ : syracuseStep 27026399 = 40539599) B40539599
theorem B18017599 : Blo 2107435 18017599 := bstep (se 1 (by rfl) ⟨13513199, by rfl⟩ : syracuseStep 18017599 = 27026399) B27026399
theorem B24023465 : Blo 2107435 24023465 := bstep (se 2 (by rfl) ⟨9008799, by rfl⟩ : syracuseStep 24023465 = 18017599) B18017599
theorem B16015643 : Blo 2107435 16015643 := bstep (se 1 (by rfl) ⟨12011732, by rfl⟩ : syracuseStep 16015643 = 24023465) B24023465
theorem B10677095 : Blo 2107435 10677095 := bstep (se 1 (by rfl) ⟨8007821, by rfl⟩ : syracuseStep 10677095 = 16015643) B16015643
theorem B7118063 : Blo 2107435 7118063 := bstep (se 1 (by rfl) ⟨5338547, by rfl⟩ : syracuseStep 7118063 = 10677095) B10677095
theorem B4745375 : Blo 2107435 4745375 := bstep (se 1 (by rfl) ⟨3559031, by rfl⟩ : syracuseStep 4745375 = 7118063) B7118063
theorem B3163583 : Blo 2107435 3163583 := bstep (se 1 (by rfl) ⟨2372687, by rfl⟩ : syracuseStep 3163583 = 4745375) B4745375
theorem B2109055 : Blo 2107435 2109055 := bstep (se 1 (by rfl) ⟨1581791, by rfl⟩ : syracuseStep 2109055 = 3163583) B3163583
theorem B3163589 : Blo 2107435 3163589 := bbase (se 4 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 3163589 = 593173) (by norm_num)
theorem B2109059 : Blo 2107435 2109059 := bstep (se 1 (by rfl) ⟨1581794, by rfl⟩ : syracuseStep 2109059 = 3163589) B3163589
theorem B3559045 : Blo 2107435 3559045 := bbase (se 4 (by rfl) ⟨333660, by rfl⟩ : syracuseStep 3559045 = 667321) (by norm_num)
theorem B4745393 : Blo 2107435 4745393 := bstep (se 2 (by rfl) ⟨1779522, by rfl⟩ : syracuseStep 4745393 = 3559045) B3559045
theorem B3163595 : Blo 2107435 3163595 := bstep (se 1 (by rfl) ⟨2372696, by rfl⟩ : syracuseStep 3163595 = 4745393) B4745393
theorem B2109063 : Blo 2107435 2109063 := bstep (se 1 (by rfl) ⟨1581797, by rfl⟩ : syracuseStep 2109063 = 3163595) B3163595
theorem B2372701 : Blo 2107435 2372701 := bbase (se 3 (by rfl) ⟨444881, by rfl⟩ : syracuseStep 2372701 = 889763) (by norm_num)
theorem B3163601 : Blo 2107435 3163601 := bstep (se 2 (by rfl) ⟨1186350, by rfl⟩ : syracuseStep 3163601 = 2372701) B2372701
theorem B2109067 : Blo 2107435 2109067 := bstep (se 1 (by rfl) ⟨1581800, by rfl⟩ : syracuseStep 2109067 = 3163601) B3163601
theorem B7118117 : Blo 2107435 7118117 := bbase (se 4 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 7118117 = 1334647) (by norm_num)
theorem B4745411 : Blo 2107435 4745411 := bstep (se 1 (by rfl) ⟨3559058, by rfl⟩ : syracuseStep 4745411 = 7118117) B7118117
theorem B3163607 : Blo 2107435 3163607 := bstep (se 1 (by rfl) ⟨2372705, by rfl⟩ : syracuseStep 3163607 = 4745411) B4745411
theorem B2109071 : Blo 2107435 2109071 := bstep (se 1 (by rfl) ⟨1581803, by rfl⟩ : syracuseStep 2109071 = 3163607) B3163607
theorem B3163613 : Blo 2107435 3163613 := bbase (se 3 (by rfl) ⟨593177, by rfl⟩ : syracuseStep 3163613 = 1186355) (by norm_num)
theorem B2109075 : Blo 2107435 2109075 := bstep (se 1 (by rfl) ⟨1581806, by rfl⟩ : syracuseStep 2109075 = 3163613) B3163613
theorem B4745429 : Blo 2107435 4745429 := bbase (se 7 (by rfl) ⟨55610, by rfl⟩ : syracuseStep 4745429 = 111221) (by norm_num)
theorem B3163619 : Blo 2107435 3163619 := bstep (se 1 (by rfl) ⟨2372714, by rfl⟩ : syracuseStep 3163619 = 4745429) B4745429
theorem B2109079 : Blo 2107435 2109079 := bstep (se 1 (by rfl) ⟨1581809, by rfl⟩ : syracuseStep 2109079 = 3163619) B3163619
theorem B2705729 : Blo 2107435 2705729 := bbase (se 2 (by rfl) ⟨1014648, by rfl⟩ : syracuseStep 2705729 = 2029297) (by norm_num)
theorem B28861109 : Blo 2107435 28861109 := bstep (se 5 (by rfl) ⟨1352864, by rfl⟩ : syracuseStep 28861109 = 2705729) B2705729
theorem B19240739 : Blo 2107435 19240739 := bstep (se 1 (by rfl) ⟨14430554, by rfl⟩ : syracuseStep 19240739 = 28861109) B28861109
theorem B12827159 : Blo 2107435 12827159 := bstep (se 1 (by rfl) ⟨9620369, by rfl⟩ : syracuseStep 12827159 = 19240739) B19240739
theorem B8551439 : Blo 2107435 8551439 := bstep (se 1 (by rfl) ⟨6413579, by rfl⟩ : syracuseStep 8551439 = 12827159) B12827159
theorem B5700959 : Blo 2107435 5700959 := bstep (se 1 (by rfl) ⟨4275719, by rfl⟩ : syracuseStep 5700959 = 8551439) B8551439
theorem B3800639 : Blo 2107435 3800639 := bstep (se 1 (by rfl) ⟨2850479, by rfl⟩ : syracuseStep 3800639 = 5700959) B5700959
theorem B10135037 : Blo 2107435 10135037 := bstep (se 3 (by rfl) ⟨1900319, by rfl⟩ : syracuseStep 10135037 = 3800639) B3800639
theorem B6756691 : Blo 2107435 6756691 := bstep (se 1 (by rfl) ⟨5067518, by rfl⟩ : syracuseStep 6756691 = 10135037) B10135037
theorem B9008921 : Blo 2107435 9008921 := bstep (se 2 (by rfl) ⟨3378345, by rfl⟩ : syracuseStep 9008921 = 6756691) B6756691
theorem B6005947 : Blo 2107435 6005947 := bstep (se 1 (by rfl) ⟨4504460, by rfl⟩ : syracuseStep 6005947 = 9008921) B9008921
theorem B8007929 : Blo 2107435 8007929 := bstep (se 2 (by rfl) ⟨3002973, by rfl⟩ : syracuseStep 8007929 = 6005947) B6005947
theorem B5338619 : Blo 2107435 5338619 := bstep (se 1 (by rfl) ⟨4003964, by rfl⟩ : syracuseStep 5338619 = 8007929) B8007929
theorem B3559079 : Blo 2107435 3559079 := bstep (se 1 (by rfl) ⟨2669309, by rfl⟩ : syracuseStep 3559079 = 5338619) B5338619
theorem B2372719 : Blo 2107435 2372719 := bstep (se 1 (by rfl) ⟨1779539, by rfl⟩ : syracuseStep 2372719 = 3559079) B3559079
theorem B3163625 : Blo 2107435 3163625 := bstep (se 2 (by rfl) ⟨1186359, by rfl⟩ : syracuseStep 3163625 = 2372719) B2372719
theorem B2109083 : Blo 2107435 2109083 := bstep (se 1 (by rfl) ⟨1581812, by rfl⟩ : syracuseStep 2109083 = 3163625) B3163625
theorem B3607645 : Blo 2107435 3607645 := bbase (se 3 (by rfl) ⟨676433, by rfl⟩ : syracuseStep 3607645 = 1352867) (by norm_num)
theorem B4810193 : Blo 2107435 4810193 := bstep (se 2 (by rfl) ⟨1803822, by rfl⟩ : syracuseStep 4810193 = 3607645) B3607645
theorem B3206795 : Blo 2107435 3206795 := bstep (se 1 (by rfl) ⟨2405096, by rfl⟩ : syracuseStep 3206795 = 4810193) B4810193
theorem B8551453 : Blo 2107435 8551453 := bstep (se 3 (by rfl) ⟨1603397, by rfl⟩ : syracuseStep 8551453 = 3206795) B3206795
theorem B11401937 : Blo 2107435 11401937 := bstep (se 2 (by rfl) ⟨4275726, by rfl⟩ : syracuseStep 11401937 = 8551453) B8551453
theorem B7601291 : Blo 2107435 7601291 := bstep (se 1 (by rfl) ⟨5700968, by rfl⟩ : syracuseStep 7601291 = 11401937) B11401937
theorem B5067527 : Blo 2107435 5067527 := bstep (se 1 (by rfl) ⟨3800645, by rfl⟩ : syracuseStep 5067527 = 7601291) B7601291
theorem B13513405 : Blo 2107435 13513405 := bstep (se 3 (by rfl) ⟨2533763, by rfl⟩ : syracuseStep 13513405 = 5067527) B5067527
theorem B18017873 : Blo 2107435 18017873 := bstep (se 2 (by rfl) ⟨6756702, by rfl⟩ : syracuseStep 18017873 = 13513405) B13513405
theorem B12011915 : Blo 2107435 12011915 := bstep (se 1 (by rfl) ⟨9008936, by rfl⟩ : syracuseStep 12011915 = 18017873) B18017873
theorem B8007943 : Blo 2107435 8007943 := bstep (se 1 (by rfl) ⟨6005957, by rfl⟩ : syracuseStep 8007943 = 12011915) B12011915
theorem B10677257 : Blo 2107435 10677257 := bstep (se 2 (by rfl) ⟨4003971, by rfl⟩ : syracuseStep 10677257 = 8007943) B8007943
theorem B7118171 : Blo 2107435 7118171 := bstep (se 1 (by rfl) ⟨5338628, by rfl⟩ : syracuseStep 7118171 = 10677257) B10677257
theorem B4745447 : Blo 2107435 4745447 := bstep (se 1 (by rfl) ⟨3559085, by rfl⟩ : syracuseStep 4745447 = 7118171) B7118171
theorem B3163631 : Blo 2107435 3163631 := bstep (se 1 (by rfl) ⟨2372723, by rfl⟩ : syracuseStep 3163631 = 4745447) B4745447
theorem B2109087 : Blo 2107435 2109087 := bstep (se 1 (by rfl) ⟨1581815, by rfl⟩ : syracuseStep 2109087 = 3163631) B3163631
theorem B3163637 : Blo 2107435 3163637 := bbase (se 5 (by rfl) ⟨148295, by rfl⟩ : syracuseStep 3163637 = 296591) (by norm_num)
theorem B2109091 : Blo 2107435 2109091 := bstep (se 1 (by rfl) ⟨1581818, by rfl⟩ : syracuseStep 2109091 = 3163637) B3163637
theorem B3378365 : Blo 2107435 3378365 := bbase (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) (by norm_num)
theorem B2252243 : Blo 2107435 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B6005981 : Blo 2107435 6005981 := bstep (se 3 (by rfl) ⟨1126121, by rfl⟩ : syracuseStep 6005981 = 2252243) B2252243
theorem B4003987 : Blo 2107435 4003987 := bstep (se 1 (by rfl) ⟨3002990, by rfl⟩ : syracuseStep 4003987 = 6005981) B6005981
theorem B5338649 : Blo 2107435 5338649 := bstep (se 2 (by rfl) ⟨2001993, by rfl⟩ : syracuseStep 5338649 = 4003987) B4003987
theorem B3559099 : Blo 2107435 3559099 := bstep (se 1 (by rfl) ⟨2669324, by rfl⟩ : syracuseStep 3559099 = 5338649) B5338649
theorem B4745465 : Blo 2107435 4745465 := bstep (se 2 (by rfl) ⟨1779549, by rfl⟩ : syracuseStep 4745465 = 3559099) B3559099
theorem B3163643 : Blo 2107435 3163643 := bstep (se 1 (by rfl) ⟨2372732, by rfl⟩ : syracuseStep 3163643 = 4745465) B4745465
theorem B2109095 : Blo 2107435 2109095 := bstep (se 1 (by rfl) ⟨1581821, by rfl⟩ : syracuseStep 2109095 = 3163643) B3163643
theorem B2372737 : Blo 2107435 2372737 := bbase (se 2 (by rfl) ⟨889776, by rfl⟩ : syracuseStep 2372737 = 1779553) (by norm_num)
theorem B3163649 : Blo 2107435 3163649 := bstep (se 2 (by rfl) ⟨1186368, by rfl⟩ : syracuseStep 3163649 = 2372737) B2372737
theorem B2109099 : Blo 2107435 2109099 := bstep (se 1 (by rfl) ⟨1581824, by rfl⟩ : syracuseStep 2109099 = 3163649) B3163649
theorem B5338669 : Blo 2107435 5338669 := bbase (se 3 (by rfl) ⟨1001000, by rfl⟩ : syracuseStep 5338669 = 2002001) (by norm_num)
theorem B7118225 : Blo 2107435 7118225 := bstep (se 2 (by rfl) ⟨2669334, by rfl⟩ : syracuseStep 7118225 = 5338669) B5338669
theorem B4745483 : Blo 2107435 4745483 := bstep (se 1 (by rfl) ⟨3559112, by rfl⟩ : syracuseStep 4745483 = 7118225) B7118225
theorem B3163655 : Blo 2107435 3163655 := bstep (se 1 (by rfl) ⟨2372741, by rfl⟩ : syracuseStep 3163655 = 4745483) B4745483
theorem B2109103 : Blo 2107435 2109103 := bstep (se 1 (by rfl) ⟨1581827, by rfl⟩ : syracuseStep 2109103 = 3163655) B3163655
theorem B3163661 : Blo 2107435 3163661 := bbase (se 3 (by rfl) ⟨593186, by rfl⟩ : syracuseStep 3163661 = 1186373) (by norm_num)
theorem B2109107 : Blo 2107435 2109107 := bstep (se 1 (by rfl) ⟨1581830, by rfl⟩ : syracuseStep 2109107 = 3163661) B3163661
theorem B4745501 : Blo 2107435 4745501 := bbase (se 3 (by rfl) ⟨889781, by rfl⟩ : syracuseStep 4745501 = 1779563) (by norm_num)
theorem B3163667 : Blo 2107435 3163667 := bstep (se 1 (by rfl) ⟨2372750, by rfl⟩ : syracuseStep 3163667 = 4745501) B4745501
theorem B2109111 : Blo 2107435 2109111 := bstep (se 1 (by rfl) ⟨1581833, by rfl⟩ : syracuseStep 2109111 = 3163667) B3163667
theorem B3559133 : Blo 2107435 3559133 := bbase (se 3 (by rfl) ⟨667337, by rfl⟩ : syracuseStep 3559133 = 1334675) (by norm_num)
theorem B2372755 : Blo 2107435 2372755 := bstep (se 1 (by rfl) ⟨1779566, by rfl⟩ : syracuseStep 2372755 = 3559133) B3559133
theorem B3163673 : Blo 2107435 3163673 := bstep (se 2 (by rfl) ⟨1186377, by rfl⟩ : syracuseStep 3163673 = 2372755) B2372755
theorem B2109115 : Blo 2107435 2109115 := bstep (se 1 (by rfl) ⟨1581836, by rfl⟩ : syracuseStep 2109115 = 3163673) B3163673
theorem B6756805 : Blo 2107435 6756805 := bbase (se 4 (by rfl) ⟨633450, by rfl⟩ : syracuseStep 6756805 = 1266901) (by norm_num)
theorem B9009073 : Blo 2107435 9009073 := bstep (se 2 (by rfl) ⟨3378402, by rfl⟩ : syracuseStep 9009073 = 6756805) B6756805
theorem B12012097 : Blo 2107435 12012097 := bstep (se 2 (by rfl) ⟨4504536, by rfl⟩ : syracuseStep 12012097 = 9009073) B9009073
theorem B16016129 : Blo 2107435 16016129 := bstep (se 2 (by rfl) ⟨6006048, by rfl⟩ : syracuseStep 16016129 = 12012097) B12012097
theorem B10677419 : Blo 2107435 10677419 := bstep (se 1 (by rfl) ⟨8008064, by rfl⟩ : syracuseStep 10677419 = 16016129) B16016129
theorem B7118279 : Blo 2107435 7118279 := bstep (se 1 (by rfl) ⟨5338709, by rfl⟩ : syracuseStep 7118279 = 10677419) B10677419
theorem B4745519 : Blo 2107435 4745519 := bstep (se 1 (by rfl) ⟨3559139, by rfl⟩ : syracuseStep 4745519 = 7118279) B7118279
theorem B3163679 : Blo 2107435 3163679 := bstep (se 1 (by rfl) ⟨2372759, by rfl⟩ : syracuseStep 3163679 = 4745519) B4745519
theorem B2109119 : Blo 2107435 2109119 := bstep (se 1 (by rfl) ⟨1581839, by rfl⟩ : syracuseStep 2109119 = 3163679) B3163679
theorem B3163685 : Blo 2107435 3163685 := bbase (se 4 (by rfl) ⟨296595, by rfl⟩ : syracuseStep 3163685 = 593191) (by norm_num)
theorem B2109123 : Blo 2107435 2109123 := bstep (se 1 (by rfl) ⟨1581842, by rfl⟩ : syracuseStep 2109123 = 3163685) B3163685
theorem B2669365 : Blo 2107435 2669365 := bbase (se 5 (by rfl) ⟨125126, by rfl⟩ : syracuseStep 2669365 = 250253) (by norm_num)
theorem B3559153 : Blo 2107435 3559153 := bstep (se 2 (by rfl) ⟨1334682, by rfl⟩ : syracuseStep 3559153 = 2669365) B2669365
theorem B4745537 : Blo 2107435 4745537 := bstep (se 2 (by rfl) ⟨1779576, by rfl⟩ : syracuseStep 4745537 = 3559153) B3559153
theorem B3163691 : Blo 2107435 3163691 := bstep (se 1 (by rfl) ⟨2372768, by rfl⟩ : syracuseStep 3163691 = 4745537) B4745537
theorem B2109127 : Blo 2107435 2109127 := bstep (se 1 (by rfl) ⟨1581845, by rfl⟩ : syracuseStep 2109127 = 3163691) B3163691
theorem B2372773 : Blo 2107435 2372773 := bbase (se 4 (by rfl) ⟨222447, by rfl⟩ : syracuseStep 2372773 = 444895) (by norm_num)
theorem B3163697 : Blo 2107435 3163697 := bstep (se 2 (by rfl) ⟨1186386, by rfl⟩ : syracuseStep 3163697 = 2372773) B2372773
theorem B2109131 : Blo 2107435 2109131 := bstep (se 1 (by rfl) ⟨1581848, by rfl⟩ : syracuseStep 2109131 = 3163697) B3163697
theorem B3852589 : Blo 2107435 3852589 := bbase (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) (by norm_num)
theorem B5136785 : Blo 2107435 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B3424523 : Blo 2107435 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B36528245 : Blo 2107435 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B24352163 : Blo 2107435 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B16234775 : Blo 2107435 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B10823183 : Blo 2107435 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B7215455 : Blo 2107435 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B4810303 : Blo 2107435 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B6413737 : Blo 2107435 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B8551649 : Blo 2107435 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B5701099 : Blo 2107435 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B7601465 : Blo 2107435 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B20270573 : Blo 2107435 20270573 := bstep (se 3 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 20270573 = 7601465) B7601465
theorem B13513715 : Blo 2107435 13513715 := bstep (se 1 (by rfl) ⟨10135286, by rfl⟩ : syracuseStep 13513715 = 20270573) B20270573
theorem B9009143 : Blo 2107435 9009143 := bstep (se 1 (by rfl) ⟨6756857, by rfl⟩ : syracuseStep 9009143 = 13513715) B13513715
theorem B6006095 : Blo 2107435 6006095 := bstep (se 1 (by rfl) ⟨4504571, by rfl⟩ : syracuseStep 6006095 = 9009143) B9009143
theorem B4004063 : Blo 2107435 4004063 := bstep (se 1 (by rfl) ⟨3003047, by rfl⟩ : syracuseStep 4004063 = 6006095) B6006095
theorem B2669375 : Blo 2107435 2669375 := bstep (se 1 (by rfl) ⟨2002031, by rfl⟩ : syracuseStep 2669375 = 4004063) B4004063
theorem B7118333 : Blo 2107435 7118333 := bstep (se 3 (by rfl) ⟨1334687, by rfl⟩ : syracuseStep 7118333 = 2669375) B2669375
theorem B4745555 : Blo 2107435 4745555 := bstep (se 1 (by rfl) ⟨3559166, by rfl⟩ : syracuseStep 4745555 = 7118333) B7118333
theorem B3163703 : Blo 2107435 3163703 := bstep (se 1 (by rfl) ⟨2372777, by rfl⟩ : syracuseStep 3163703 = 4745555) B4745555
theorem B2109135 : Blo 2107435 2109135 := bstep (se 1 (by rfl) ⟨1581851, by rfl⟩ : syracuseStep 2109135 = 3163703) B3163703
theorem B3163709 : Blo 2107435 3163709 := bbase (se 3 (by rfl) ⟨593195, by rfl⟩ : syracuseStep 3163709 = 1186391) (by norm_num)
theorem B2109139 : Blo 2107435 2109139 := bstep (se 1 (by rfl) ⟨1581854, by rfl⟩ : syracuseStep 2109139 = 3163709) B3163709
theorem B4745573 : Blo 2107435 4745573 := bbase (se 4 (by rfl) ⟨444897, by rfl⟩ : syracuseStep 4745573 = 889795) (by norm_num)
theorem B3163715 : Blo 2107435 3163715 := bstep (se 1 (by rfl) ⟨2372786, by rfl⟩ : syracuseStep 3163715 = 4745573) B4745573
theorem B2109143 : Blo 2107435 2109143 := bstep (se 1 (by rfl) ⟨1581857, by rfl⟩ : syracuseStep 2109143 = 3163715) B3163715
theorem B5338781 : Blo 2107435 5338781 := bbase (se 3 (by rfl) ⟨1001021, by rfl⟩ : syracuseStep 5338781 = 2002043) (by norm_num)
theorem B3559187 : Blo 2107435 3559187 := bstep (se 1 (by rfl) ⟨2669390, by rfl⟩ : syracuseStep 3559187 = 5338781) B5338781
theorem B2372791 : Blo 2107435 2372791 := bstep (se 1 (by rfl) ⟨1779593, by rfl⟩ : syracuseStep 2372791 = 3559187) B3559187
theorem B3163721 : Blo 2107435 3163721 := bstep (se 2 (by rfl) ⟨1186395, by rfl⟩ : syracuseStep 3163721 = 2372791) B2372791
theorem B2109147 : Blo 2107435 2109147 := bstep (se 1 (by rfl) ⟨1581860, by rfl⟩ : syracuseStep 2109147 = 3163721) B3163721
theorem B4004093 : Blo 2107435 4004093 := bbase (se 3 (by rfl) ⟨750767, by rfl⟩ : syracuseStep 4004093 = 1501535) (by norm_num)
theorem B10677581 : Blo 2107435 10677581 := bstep (se 3 (by rfl) ⟨2002046, by rfl⟩ : syracuseStep 10677581 = 4004093) B4004093
theorem B7118387 : Blo 2107435 7118387 := bstep (se 1 (by rfl) ⟨5338790, by rfl⟩ : syracuseStep 7118387 = 10677581) B10677581
theorem B4745591 : Blo 2107435 4745591 := bstep (se 1 (by rfl) ⟨3559193, by rfl⟩ : syracuseStep 4745591 = 7118387) B7118387
theorem B3163727 : Blo 2107435 3163727 := bstep (se 1 (by rfl) ⟨2372795, by rfl⟩ : syracuseStep 3163727 = 4745591) B4745591
theorem B2109151 : Blo 2107435 2109151 := bstep (se 1 (by rfl) ⟨1581863, by rfl⟩ : syracuseStep 2109151 = 3163727) B3163727
theorem B3163733 : Blo 2107435 3163733 := bbase (se 8 (by rfl) ⟨18537, by rfl⟩ : syracuseStep 3163733 = 37075) (by norm_num)
theorem B2109155 : Blo 2107435 2109155 := bstep (se 1 (by rfl) ⟨1581866, by rfl⟩ : syracuseStep 2109155 = 3163733) B3163733
theorem B5067701 : Blo 2107435 5067701 := bbase (se 5 (by rfl) ⟨237548, by rfl⟩ : syracuseStep 5067701 = 475097) (by norm_num)
theorem B3378467 : Blo 2107435 3378467 := bstep (se 1 (by rfl) ⟨2533850, by rfl⟩ : syracuseStep 3378467 = 5067701) B5067701
theorem B9009245 : Blo 2107435 9009245 := bstep (se 3 (by rfl) ⟨1689233, by rfl⟩ : syracuseStep 9009245 = 3378467) B3378467
theorem B6006163 : Blo 2107435 6006163 := bstep (se 1 (by rfl) ⟨4504622, by rfl⟩ : syracuseStep 6006163 = 9009245) B9009245
theorem B8008217 : Blo 2107435 8008217 := bstep (se 2 (by rfl) ⟨3003081, by rfl⟩ : syracuseStep 8008217 = 6006163) B6006163
theorem B5338811 : Blo 2107435 5338811 := bstep (se 1 (by rfl) ⟨4004108, by rfl⟩ : syracuseStep 5338811 = 8008217) B8008217
theorem B3559207 : Blo 2107435 3559207 := bstep (se 1 (by rfl) ⟨2669405, by rfl⟩ : syracuseStep 3559207 = 5338811) B5338811
theorem B4745609 : Blo 2107435 4745609 := bstep (se 2 (by rfl) ⟨1779603, by rfl⟩ : syracuseStep 4745609 = 3559207) B3559207
theorem B3163739 : Blo 2107435 3163739 := bstep (se 1 (by rfl) ⟨2372804, by rfl⟩ : syracuseStep 3163739 = 4745609) B4745609
theorem B2109159 : Blo 2107435 2109159 := bstep (se 1 (by rfl) ⟨1581869, by rfl⟩ : syracuseStep 2109159 = 3163739) B3163739
theorem B2372809 : Blo 2107435 2372809 := bbase (se 2 (by rfl) ⟨889803, by rfl⟩ : syracuseStep 2372809 = 1779607) (by norm_num)
theorem B3163745 : Blo 2107435 3163745 := bstep (se 2 (by rfl) ⟨1186404, by rfl⟩ : syracuseStep 3163745 = 2372809) B2372809
theorem B2109163 : Blo 2107435 2109163 := bstep (se 1 (by rfl) ⟨1581872, by rfl⟩ : syracuseStep 2109163 = 3163745) B3163745
theorem B8117509 : Blo 2107435 8117509 := bbase (se 4 (by rfl) ⟨761016, by rfl⟩ : syracuseStep 8117509 = 1522033) (by norm_num)
theorem B10823345 : Blo 2107435 10823345 := bstep (se 2 (by rfl) ⟨4058754, by rfl⟩ : syracuseStep 10823345 = 8117509) B8117509
theorem B7215563 : Blo 2107435 7215563 := bstep (se 1 (by rfl) ⟨5411672, by rfl⟩ : syracuseStep 7215563 = 10823345) B10823345
theorem B4810375 : Blo 2107435 4810375 := bstep (se 1 (by rfl) ⟨3607781, by rfl⟩ : syracuseStep 4810375 = 7215563) B7215563
theorem B6413833 : Blo 2107435 6413833 := bstep (se 2 (by rfl) ⟨2405187, by rfl⟩ : syracuseStep 6413833 = 4810375) B4810375
theorem B34207109 : Blo 2107435 34207109 := bstep (se 4 (by rfl) ⟨3206916, by rfl⟩ : syracuseStep 34207109 = 6413833) B6413833
theorem B22804739 : Blo 2107435 22804739 := bstep (se 1 (by rfl) ⟨17103554, by rfl⟩ : syracuseStep 22804739 = 34207109) B34207109
theorem B15203159 : Blo 2107435 15203159 := bstep (se 1 (by rfl) ⟨11402369, by rfl⟩ : syracuseStep 15203159 = 22804739) B22804739
theorem B10135439 : Blo 2107435 10135439 := bstep (se 1 (by rfl) ⟨7601579, by rfl⟩ : syracuseStep 10135439 = 15203159) B15203159
theorem B6756959 : Blo 2107435 6756959 := bstep (se 1 (by rfl) ⟨5067719, by rfl⟩ : syracuseStep 6756959 = 10135439) B10135439
theorem B18018557 : Blo 2107435 18018557 := bstep (se 3 (by rfl) ⟨3378479, by rfl⟩ : syracuseStep 18018557 = 6756959) B6756959
theorem B12012371 : Blo 2107435 12012371 := bstep (se 1 (by rfl) ⟨9009278, by rfl⟩ : syracuseStep 12012371 = 18018557) B18018557
theorem B8008247 : Blo 2107435 8008247 := bstep (se 1 (by rfl) ⟨6006185, by rfl⟩ : syracuseStep 8008247 = 12012371) B12012371
theorem B5338831 : Blo 2107435 5338831 := bstep (se 1 (by rfl) ⟨4004123, by rfl⟩ : syracuseStep 5338831 = 8008247) B8008247
theorem B7118441 : Blo 2107435 7118441 := bstep (se 2 (by rfl) ⟨2669415, by rfl⟩ : syracuseStep 7118441 = 5338831) B5338831
theorem B4745627 : Blo 2107435 4745627 := bstep (se 1 (by rfl) ⟨3559220, by rfl⟩ : syracuseStep 4745627 = 7118441) B7118441
theorem B3163751 : Blo 2107435 3163751 := bstep (se 1 (by rfl) ⟨2372813, by rfl⟩ : syracuseStep 3163751 = 4745627) B4745627
theorem B2109167 : Blo 2107435 2109167 := bstep (se 1 (by rfl) ⟨1581875, by rfl⟩ : syracuseStep 2109167 = 3163751) B3163751
theorem B3163757 : Blo 2107435 3163757 := bbase (se 3 (by rfl) ⟨593204, by rfl⟩ : syracuseStep 3163757 = 1186409) (by norm_num)
theorem B2109171 : Blo 2107435 2109171 := bstep (se 1 (by rfl) ⟨1581878, by rfl⟩ : syracuseStep 2109171 = 3163757) B3163757
theorem B4745645 : Blo 2107435 4745645 := bbase (se 3 (by rfl) ⟨889808, by rfl⟩ : syracuseStep 4745645 = 1779617) (by norm_num)
theorem B3163763 : Blo 2107435 3163763 := bstep (se 1 (by rfl) ⟨2372822, by rfl⟩ : syracuseStep 3163763 = 4745645) B4745645
theorem B2109175 : Blo 2107435 2109175 := bstep (se 1 (by rfl) ⟨1581881, by rfl⟩ : syracuseStep 2109175 = 3163763) B3163763
theorem B2252333 : Blo 2107435 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B6006221 : Blo 2107435 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B4004147 : Blo 2107435 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B2669431 : Blo 2107435 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B3559241 : Blo 2107435 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B2372827 : Blo 2107435 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B3163769 : Blo 2107435 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B2109179 : Blo 2107435 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B9620821 : Blo 2107435 9620821 := bbase (se 11 (by rfl) ⟨7046, by rfl⟩ : syracuseStep 9620821 = 14093) (by norm_num)
theorem B51311045 : Blo 2107435 51311045 := bstep (se 4 (by rfl) ⟨4810410, by rfl⟩ : syracuseStep 51311045 = 9620821) B9620821
theorem B34207363 : Blo 2107435 34207363 := bstep (se 1 (by rfl) ⟨25655522, by rfl⟩ : syracuseStep 34207363 = 51311045) B51311045
theorem B45609817 : Blo 2107435 45609817 := bstep (se 2 (by rfl) ⟨17103681, by rfl⟩ : syracuseStep 45609817 = 34207363) B34207363
theorem B60813089 : Blo 2107435 60813089 := bstep (se 2 (by rfl) ⟨22804908, by rfl⟩ : syracuseStep 60813089 = 45609817) B45609817
theorem B40542059 : Blo 2107435 40542059 := bstep (se 1 (by rfl) ⟨30406544, by rfl⟩ : syracuseStep 40542059 = 60813089) B60813089
theorem B27028039 : Blo 2107435 27028039 := bstep (se 1 (by rfl) ⟨20271029, by rfl⟩ : syracuseStep 27028039 = 40542059) B40542059
theorem B36037385 : Blo 2107435 36037385 := bstep (se 2 (by rfl) ⟨13514019, by rfl⟩ : syracuseStep 36037385 = 27028039) B27028039
theorem B24024923 : Blo 2107435 24024923 := bstep (se 1 (by rfl) ⟨18018692, by rfl⟩ : syracuseStep 24024923 = 36037385) B36037385
theorem B16016615 : Blo 2107435 16016615 := bstep (se 1 (by rfl) ⟨12012461, by rfl⟩ : syracuseStep 16016615 = 24024923) B24024923
theorem B10677743 : Blo 2107435 10677743 := bstep (se 1 (by rfl) ⟨8008307, by rfl⟩ : syracuseStep 10677743 = 16016615) B16016615
theorem B7118495 : Blo 2107435 7118495 := bstep (se 1 (by rfl) ⟨5338871, by rfl⟩ : syracuseStep 7118495 = 10677743) B10677743
theorem B4745663 : Blo 2107435 4745663 := bstep (se 1 (by rfl) ⟨3559247, by rfl⟩ : syracuseStep 4745663 = 7118495) B7118495
theorem B3163775 : Blo 2107435 3163775 := bstep (se 1 (by rfl) ⟨2372831, by rfl⟩ : syracuseStep 3163775 = 4745663) B4745663
theorem B2109183 : Blo 2107435 2109183 := bstep (se 1 (by rfl) ⟨1581887, by rfl⟩ : syracuseStep 2109183 = 3163775) B3163775
theorem B3163781 : Blo 2107435 3163781 := bbase (se 4 (by rfl) ⟨296604, by rfl⟩ : syracuseStep 3163781 = 593209) (by norm_num)
theorem B2109187 : Blo 2107435 2109187 := bstep (se 1 (by rfl) ⟨1581890, by rfl⟩ : syracuseStep 2109187 = 3163781) B3163781
theorem B3559261 : Blo 2107435 3559261 := bbase (se 3 (by rfl) ⟨667361, by rfl⟩ : syracuseStep 3559261 = 1334723) (by norm_num)
theorem B4745681 : Blo 2107435 4745681 := bstep (se 2 (by rfl) ⟨1779630, by rfl⟩ : syracuseStep 4745681 = 3559261) B3559261
theorem B3163787 : Blo 2107435 3163787 := bstep (se 1 (by rfl) ⟨2372840, by rfl⟩ : syracuseStep 3163787 = 4745681) B4745681
theorem B2109191 : Blo 2107435 2109191 := bstep (se 1 (by rfl) ⟨1581893, by rfl⟩ : syracuseStep 2109191 = 3163787) B3163787
theorem B2372845 : Blo 2107435 2372845 := bbase (se 3 (by rfl) ⟨444908, by rfl⟩ : syracuseStep 2372845 = 889817) (by norm_num)
theorem B3163793 : Blo 2107435 3163793 := bstep (se 2 (by rfl) ⟨1186422, by rfl⟩ : syracuseStep 3163793 = 2372845) B2372845
theorem B2109195 : Blo 2107435 2109195 := bstep (se 1 (by rfl) ⟨1581896, by rfl⟩ : syracuseStep 2109195 = 3163793) B3163793
theorem B7118549 : Blo 2107435 7118549 := bbase (se 7 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 7118549 = 166841) (by norm_num)
theorem B4745699 : Blo 2107435 4745699 := bstep (se 1 (by rfl) ⟨3559274, by rfl⟩ : syracuseStep 4745699 = 7118549) B7118549
theorem B3163799 : Blo 2107435 3163799 := bstep (se 1 (by rfl) ⟨2372849, by rfl⟩ : syracuseStep 3163799 = 4745699) B4745699
theorem B2109199 : Blo 2107435 2109199 := bstep (se 1 (by rfl) ⟨1581899, by rfl⟩ : syracuseStep 2109199 = 3163799) B3163799
theorem B3163805 : Blo 2107435 3163805 := bbase (se 3 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 3163805 = 1186427) (by norm_num)
theorem B2109203 : Blo 2107435 2109203 := bstep (se 1 (by rfl) ⟨1581902, by rfl⟩ : syracuseStep 2109203 = 3163805) B3163805
theorem B4745717 : Blo 2107435 4745717 := bbase (se 5 (by rfl) ⟨222455, by rfl⟩ : syracuseStep 4745717 = 444911) (by norm_num)
theorem B3163811 : Blo 2107435 3163811 := bstep (se 1 (by rfl) ⟨2372858, by rfl⟩ : syracuseStep 3163811 = 4745717) B4745717
theorem B2109207 : Blo 2107435 2109207 := bstep (se 1 (by rfl) ⟨1581905, by rfl⟩ : syracuseStep 2109207 = 3163811) B3163811
theorem B15203477 : Blo 2107435 15203477 := bbase (se 6 (by rfl) ⟨356331, by rfl⟩ : syracuseStep 15203477 = 712663) (by norm_num)
theorem B40542605 : Blo 2107435 40542605 := bstep (se 3 (by rfl) ⟨7601738, by rfl⟩ : syracuseStep 40542605 = 15203477) B15203477
theorem B27028403 : Blo 2107435 27028403 := bstep (se 1 (by rfl) ⟨20271302, by rfl⟩ : syracuseStep 27028403 = 40542605) B40542605
theorem B18018935 : Blo 2107435 18018935 := bstep (se 1 (by rfl) ⟨13514201, by rfl⟩ : syracuseStep 18018935 = 27028403) B27028403
theorem B12012623 : Blo 2107435 12012623 := bstep (se 1 (by rfl) ⟨9009467, by rfl⟩ : syracuseStep 12012623 = 18018935) B18018935
theorem B8008415 : Blo 2107435 8008415 := bstep (se 1 (by rfl) ⟨6006311, by rfl⟩ : syracuseStep 8008415 = 12012623) B12012623
theorem B5338943 : Blo 2107435 5338943 := bstep (se 1 (by rfl) ⟨4004207, by rfl⟩ : syracuseStep 5338943 = 8008415) B8008415
theorem B3559295 : Blo 2107435 3559295 := bstep (se 1 (by rfl) ⟨2669471, by rfl⟩ : syracuseStep 3559295 = 5338943) B5338943
theorem B2372863 : Blo 2107435 2372863 := bstep (se 1 (by rfl) ⟨1779647, by rfl⟩ : syracuseStep 2372863 = 3559295) B3559295
theorem B3163817 : Blo 2107435 3163817 := bstep (se 2 (by rfl) ⟨1186431, by rfl⟩ : syracuseStep 3163817 = 2372863) B2372863
theorem B2109211 : Blo 2107435 2109211 := bstep (se 1 (by rfl) ⟨1581908, by rfl⟩ : syracuseStep 2109211 = 3163817) B3163817
theorem B3378557 : Blo 2107435 3378557 := bbase (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) (by norm_num)
theorem B2252371 : Blo 2107435 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B3003161 : Blo 2107435 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B8008429 : Blo 2107435 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B10677905 : Blo 2107435 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B7118603 : Blo 2107435 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B4745735 : Blo 2107435 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B3163823 : Blo 2107435 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B2109215 : Blo 2107435 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B3163829 : Blo 2107435 3163829 := bbase (se 5 (by rfl) ⟨148304, by rfl⟩ : syracuseStep 3163829 = 296609) (by norm_num)
theorem B2109219 : Blo 2107435 2109219 := bstep (se 1 (by rfl) ⟨1581914, by rfl⟩ : syracuseStep 2109219 = 3163829) B3163829
theorem B5338973 : Blo 2107435 5338973 := bbase (se 3 (by rfl) ⟨1001057, by rfl⟩ : syracuseStep 5338973 = 2002115) (by norm_num)
theorem B3559315 : Blo 2107435 3559315 := bstep (se 1 (by rfl) ⟨2669486, by rfl⟩ : syracuseStep 3559315 = 5338973) B5338973
theorem B4745753 : Blo 2107435 4745753 := bstep (se 2 (by rfl) ⟨1779657, by rfl⟩ : syracuseStep 4745753 = 3559315) B3559315
theorem B3163835 : Blo 2107435 3163835 := bstep (se 1 (by rfl) ⟨2372876, by rfl⟩ : syracuseStep 3163835 = 4745753) B4745753
theorem B2109223 : Blo 2107435 2109223 := bstep (se 1 (by rfl) ⟨1581917, by rfl⟩ : syracuseStep 2109223 = 3163835) B3163835
theorem B2372881 : Blo 2107435 2372881 := bbase (se 2 (by rfl) ⟨889830, by rfl⟩ : syracuseStep 2372881 = 1779661) (by norm_num)
theorem B3163841 : Blo 2107435 3163841 := bstep (se 2 (by rfl) ⟨1186440, by rfl⟩ : syracuseStep 3163841 = 2372881) B2372881
theorem B2109227 : Blo 2107435 2109227 := bstep (se 1 (by rfl) ⟨1581920, by rfl⟩ : syracuseStep 2109227 = 3163841) B3163841
theorem B4004245 : Blo 2107435 4004245 := bbase (se 6 (by rfl) ⟨93849, by rfl⟩ : syracuseStep 4004245 = 187699) (by norm_num)
theorem B5338993 : Blo 2107435 5338993 := bstep (se 2 (by rfl) ⟨2002122, by rfl⟩ : syracuseStep 5338993 = 4004245) B4004245
theorem B7118657 : Blo 2107435 7118657 := bstep (se 2 (by rfl) ⟨2669496, by rfl⟩ : syracuseStep 7118657 = 5338993) B5338993
theorem B4745771 : Blo 2107435 4745771 := bstep (se 1 (by rfl) ⟨3559328, by rfl⟩ : syracuseStep 4745771 = 7118657) B7118657
theorem B3163847 : Blo 2107435 3163847 := bstep (se 1 (by rfl) ⟨2372885, by rfl⟩ : syracuseStep 3163847 = 4745771) B4745771
theorem B2109231 : Blo 2107435 2109231 := bstep (se 1 (by rfl) ⟨1581923, by rfl⟩ : syracuseStep 2109231 = 3163847) B3163847
theorem B3163853 : Blo 2107435 3163853 := bbase (se 3 (by rfl) ⟨593222, by rfl⟩ : syracuseStep 3163853 = 1186445) (by norm_num)
theorem B2109235 : Blo 2107435 2109235 := bstep (se 1 (by rfl) ⟨1581926, by rfl⟩ : syracuseStep 2109235 = 3163853) B3163853
theorem B4745789 : Blo 2107435 4745789 := bbase (se 3 (by rfl) ⟨889835, by rfl⟩ : syracuseStep 4745789 = 1779671) (by norm_num)
theorem B3163859 : Blo 2107435 3163859 := bstep (se 1 (by rfl) ⟨2372894, by rfl⟩ : syracuseStep 3163859 = 4745789) B4745789
theorem B2109239 : Blo 2107435 2109239 := bstep (se 1 (by rfl) ⟨1581929, by rfl⟩ : syracuseStep 2109239 = 3163859) B3163859
theorem B3559349 : Blo 2107435 3559349 := bbase (se 5 (by rfl) ⟨166844, by rfl⟩ : syracuseStep 3559349 = 333689) (by norm_num)
theorem B2372899 : Blo 2107435 2372899 := bstep (se 1 (by rfl) ⟨1779674, by rfl⟩ : syracuseStep 2372899 = 3559349) B3559349
theorem B3163865 : Blo 2107435 3163865 := bstep (se 2 (by rfl) ⟨1186449, by rfl⟩ : syracuseStep 3163865 = 2372899) B2372899
theorem B2109243 : Blo 2107435 2109243 := bstep (se 1 (by rfl) ⟨1581932, by rfl⟩ : syracuseStep 2109243 = 3163865) B3163865
theorem B2252405 : Blo 2107435 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B6006413 : Blo 2107435 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B16017101 : Blo 2107435 16017101 := bstep (se 3 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 16017101 = 6006413) B6006413
theorem B10678067 : Blo 2107435 10678067 := bstep (se 1 (by rfl) ⟨8008550, by rfl⟩ : syracuseStep 10678067 = 16017101) B16017101
theorem B7118711 : Blo 2107435 7118711 := bstep (se 1 (by rfl) ⟨5339033, by rfl⟩ : syracuseStep 7118711 = 10678067) B10678067
theorem B4745807 : Blo 2107435 4745807 := bstep (se 1 (by rfl) ⟨3559355, by rfl⟩ : syracuseStep 4745807 = 7118711) B7118711
theorem B3163871 : Blo 2107435 3163871 := bstep (se 1 (by rfl) ⟨2372903, by rfl⟩ : syracuseStep 3163871 = 4745807) B4745807
theorem B2109247 : Blo 2107435 2109247 := bstep (se 1 (by rfl) ⟨1581935, by rfl⟩ : syracuseStep 2109247 = 3163871) B3163871
theorem B3163877 : Blo 2107435 3163877 := bbase (se 4 (by rfl) ⟨296613, by rfl⟩ : syracuseStep 3163877 = 593227) (by norm_num)
theorem B2109251 : Blo 2107435 2109251 := bstep (se 1 (by rfl) ⟨1581938, by rfl⟩ : syracuseStep 2109251 = 3163877) B3163877
theorem B6006437 : Blo 2107435 6006437 := bbase (se 4 (by rfl) ⟨563103, by rfl⟩ : syracuseStep 6006437 = 1126207) (by norm_num)
theorem B4004291 : Blo 2107435 4004291 := bstep (se 1 (by rfl) ⟨3003218, by rfl⟩ : syracuseStep 4004291 = 6006437) B6006437
theorem B2669527 : Blo 2107435 2669527 := bstep (se 1 (by rfl) ⟨2002145, by rfl⟩ : syracuseStep 2669527 = 4004291) B4004291
theorem B3559369 : Blo 2107435 3559369 := bstep (se 2 (by rfl) ⟨1334763, by rfl⟩ : syracuseStep 3559369 = 2669527) B2669527
theorem B4745825 : Blo 2107435 4745825 := bstep (se 2 (by rfl) ⟨1779684, by rfl⟩ : syracuseStep 4745825 = 3559369) B3559369
theorem B3163883 : Blo 2107435 3163883 := bstep (se 1 (by rfl) ⟨2372912, by rfl⟩ : syracuseStep 3163883 = 4745825) B4745825
theorem B2109255 : Blo 2107435 2109255 := bstep (se 1 (by rfl) ⟨1581941, by rfl⟩ : syracuseStep 2109255 = 3163883) B3163883
theorem B2372917 : Blo 2107435 2372917 := bbase (se 5 (by rfl) ⟨111230, by rfl⟩ : syracuseStep 2372917 = 222461) (by norm_num)
theorem B3163889 : Blo 2107435 3163889 := bstep (se 2 (by rfl) ⟨1186458, by rfl⟩ : syracuseStep 3163889 = 2372917) B2372917
theorem B2109259 : Blo 2107435 2109259 := bstep (se 1 (by rfl) ⟨1581944, by rfl⟩ : syracuseStep 2109259 = 3163889) B3163889
theorem B2669537 : Blo 2107435 2669537 := bbase (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) (by norm_num)
theorem B7118765 : Blo 2107435 7118765 := bstep (se 3 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 7118765 = 2669537) B2669537
theorem B4745843 : Blo 2107435 4745843 := bstep (se 1 (by rfl) ⟨3559382, by rfl⟩ : syracuseStep 4745843 = 7118765) B7118765
theorem B3163895 : Blo 2107435 3163895 := bstep (se 1 (by rfl) ⟨2372921, by rfl⟩ : syracuseStep 3163895 = 4745843) B4745843
theorem B2109263 : Blo 2107435 2109263 := bstep (se 1 (by rfl) ⟨1581947, by rfl⟩ : syracuseStep 2109263 = 3163895) B3163895
theorem B3163901 : Blo 2107435 3163901 := bbase (se 3 (by rfl) ⟨593231, by rfl⟩ : syracuseStep 3163901 = 1186463) (by norm_num)
theorem B2109267 : Blo 2107435 2109267 := bstep (se 1 (by rfl) ⟨1581950, by rfl⟩ : syracuseStep 2109267 = 3163901) B3163901
theorem B4745861 : Blo 2107435 4745861 := bbase (se 4 (by rfl) ⟨444924, by rfl⟩ : syracuseStep 4745861 = 889849) (by norm_num)
theorem B3163907 : Blo 2107435 3163907 := bstep (se 1 (by rfl) ⟨2372930, by rfl⟩ : syracuseStep 3163907 = 4745861) B4745861
theorem B2109271 : Blo 2107435 2109271 := bstep (se 1 (by rfl) ⟨1581953, by rfl⟩ : syracuseStep 2109271 = 3163907) B3163907
theorem B4276109 : Blo 2107435 4276109 := bbase (se 3 (by rfl) ⟨801770, by rfl⟩ : syracuseStep 4276109 = 1603541) (by norm_num)
theorem B11402957 : Blo 2107435 11402957 := bstep (se 3 (by rfl) ⟨2138054, by rfl⟩ : syracuseStep 11402957 = 4276109) B4276109
theorem B7601971 : Blo 2107435 7601971 := bstep (se 1 (by rfl) ⟨5701478, by rfl⟩ : syracuseStep 7601971 = 11402957) B11402957
theorem B10135961 : Blo 2107435 10135961 := bstep (se 2 (by rfl) ⟨3800985, by rfl⟩ : syracuseStep 10135961 = 7601971) B7601971
theorem B6757307 : Blo 2107435 6757307 := bstep (se 1 (by rfl) ⟨5067980, by rfl⟩ : syracuseStep 6757307 = 10135961) B10135961
theorem B4504871 : Blo 2107435 4504871 := bstep (se 1 (by rfl) ⟨3378653, by rfl⟩ : syracuseStep 4504871 = 6757307) B6757307
theorem B3003247 : Blo 2107435 3003247 := bstep (se 1 (by rfl) ⟨2252435, by rfl⟩ : syracuseStep 3003247 = 4504871) B4504871
theorem B4004329 : Blo 2107435 4004329 := bstep (se 2 (by rfl) ⟨1501623, by rfl⟩ : syracuseStep 4004329 = 3003247) B3003247
theorem B5339105 : Blo 2107435 5339105 := bstep (se 2 (by rfl) ⟨2002164, by rfl⟩ : syracuseStep 5339105 = 4004329) B4004329
theorem B3559403 : Blo 2107435 3559403 := bstep (se 1 (by rfl) ⟨2669552, by rfl⟩ : syracuseStep 3559403 = 5339105) B5339105
theorem B2372935 : Blo 2107435 2372935 := bstep (se 1 (by rfl) ⟨1779701, by rfl⟩ : syracuseStep 2372935 = 3559403) B3559403
theorem B3163913 : Blo 2107435 3163913 := bstep (se 2 (by rfl) ⟨1186467, by rfl⟩ : syracuseStep 3163913 = 2372935) B2372935
theorem B2109275 : Blo 2107435 2109275 := bstep (se 1 (by rfl) ⟨1581956, by rfl⟩ : syracuseStep 2109275 = 3163913) B3163913
theorem B10678229 : Blo 2107435 10678229 := bbase (se 7 (by rfl) ⟨125135, by rfl⟩ : syracuseStep 10678229 = 250271) (by norm_num)
theorem B7118819 : Blo 2107435 7118819 := bstep (se 1 (by rfl) ⟨5339114, by rfl⟩ : syracuseStep 7118819 = 10678229) B10678229
theorem B4745879 : Blo 2107435 4745879 := bstep (se 1 (by rfl) ⟨3559409, by rfl⟩ : syracuseStep 4745879 = 7118819) B7118819
theorem B3163919 : Blo 2107435 3163919 := bstep (se 1 (by rfl) ⟨2372939, by rfl⟩ : syracuseStep 3163919 = 4745879) B4745879
theorem B2109279 : Blo 2107435 2109279 := bstep (se 1 (by rfl) ⟨1581959, by rfl⟩ : syracuseStep 2109279 = 3163919) B3163919
theorem B3163925 : Blo 2107435 3163925 := bbase (se 6 (by rfl) ⟨74154, by rfl⟩ : syracuseStep 3163925 = 148309) (by norm_num)
theorem B2109283 : Blo 2107435 2109283 := bstep (se 1 (by rfl) ⟨1581962, by rfl⟩ : syracuseStep 2109283 = 3163925) B3163925
theorem B2568577 : Blo 2107435 2568577 := bbase (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) (by norm_num)
theorem B3424769 : Blo 2107435 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B2283179 : Blo 2107435 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B6088477 : Blo 2107435 6088477 := bstep (se 3 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 6088477 = 2283179) B2283179
theorem B8117969 : Blo 2107435 8117969 := bstep (se 2 (by rfl) ⟨3044238, by rfl⟩ : syracuseStep 8117969 = 6088477) B6088477
theorem B21647917 : Blo 2107435 21647917 := bstep (se 3 (by rfl) ⟨4058984, by rfl⟩ : syracuseStep 21647917 = 8117969) B8117969
theorem B115455557 : Blo 2107435 115455557 := bstep (se 4 (by rfl) ⟨10823958, by rfl⟩ : syracuseStep 115455557 = 21647917) B21647917
theorem B307881485 : Blo 2107435 307881485 := bstep (se 3 (by rfl) ⟨57727778, by rfl⟩ : syracuseStep 307881485 = 115455557) B115455557
theorem B205254323 : Blo 2107435 205254323 := bstep (se 1 (by rfl) ⟨153940742, by rfl⟩ : syracuseStep 205254323 = 307881485) B307881485
theorem B136836215 : Blo 2107435 136836215 := bstep (se 1 (by rfl) ⟨102627161, by rfl⟩ : syracuseStep 136836215 = 205254323) B205254323
theorem B91224143 : Blo 2107435 91224143 := bstep (se 1 (by rfl) ⟨68418107, by rfl⟩ : syracuseStep 91224143 = 136836215) B136836215
theorem B60816095 : Blo 2107435 60816095 := bstep (se 1 (by rfl) ⟨45612071, by rfl⟩ : syracuseStep 60816095 = 91224143) B91224143
theorem B40544063 : Blo 2107435 40544063 := bstep (se 1 (by rfl) ⟨30408047, by rfl⟩ : syracuseStep 40544063 = 60816095) B60816095
theorem B27029375 : Blo 2107435 27029375 := bstep (se 1 (by rfl) ⟨20272031, by rfl⟩ : syracuseStep 27029375 = 40544063) B40544063
theorem B18019583 : Blo 2107435 18019583 := bstep (se 1 (by rfl) ⟨13514687, by rfl⟩ : syracuseStep 18019583 = 27029375) B27029375
theorem B12013055 : Blo 2107435 12013055 := bstep (se 1 (by rfl) ⟨9009791, by rfl⟩ : syracuseStep 12013055 = 18019583) B18019583
theorem B8008703 : Blo 2107435 8008703 := bstep (se 1 (by rfl) ⟨6006527, by rfl⟩ : syracuseStep 8008703 = 12013055) B12013055
theorem B5339135 : Blo 2107435 5339135 := bstep (se 1 (by rfl) ⟨4004351, by rfl⟩ : syracuseStep 5339135 = 8008703) B8008703
theorem B3559423 : Blo 2107435 3559423 := bstep (se 1 (by rfl) ⟨2669567, by rfl⟩ : syracuseStep 3559423 = 5339135) B5339135
theorem B4745897 : Blo 2107435 4745897 := bstep (se 2 (by rfl) ⟨1779711, by rfl⟩ : syracuseStep 4745897 = 3559423) B3559423
theorem B3163931 : Blo 2107435 3163931 := bstep (se 1 (by rfl) ⟨2372948, by rfl⟩ : syracuseStep 3163931 = 4745897) B4745897
theorem B2109287 : Blo 2107435 2109287 := bstep (se 1 (by rfl) ⟨1581965, by rfl⟩ : syracuseStep 2109287 = 3163931) B3163931
theorem B2372953 : Blo 2107435 2372953 := bbase (se 2 (by rfl) ⟨889857, by rfl⟩ : syracuseStep 2372953 = 1779715) (by norm_num)
theorem B3163937 : Blo 2107435 3163937 := bstep (se 2 (by rfl) ⟨1186476, by rfl⟩ : syracuseStep 3163937 = 2372953) B2372953
theorem B2109291 : Blo 2107435 2109291 := bstep (se 1 (by rfl) ⟨1581968, by rfl⟩ : syracuseStep 2109291 = 3163937) B3163937
theorem B3378685 : Blo 2107435 3378685 := bbase (se 3 (by rfl) ⟨633503, by rfl⟩ : syracuseStep 3378685 = 1267007) (by norm_num)
theorem B4504913 : Blo 2107435 4504913 := bstep (se 2 (by rfl) ⟨1689342, by rfl⟩ : syracuseStep 4504913 = 3378685) B3378685
theorem B3003275 : Blo 2107435 3003275 := bstep (se 1 (by rfl) ⟨2252456, by rfl⟩ : syracuseStep 3003275 = 4504913) B4504913
theorem B8008733 : Blo 2107435 8008733 := bstep (se 3 (by rfl) ⟨1501637, by rfl⟩ : syracuseStep 8008733 = 3003275) B3003275
theorem B5339155 : Blo 2107435 5339155 := bstep (se 1 (by rfl) ⟨4004366, by rfl⟩ : syracuseStep 5339155 = 8008733) B8008733
theorem B7118873 : Blo 2107435 7118873 := bstep (se 2 (by rfl) ⟨2669577, by rfl⟩ : syracuseStep 7118873 = 5339155) B5339155
theorem B4745915 : Blo 2107435 4745915 := bstep (se 1 (by rfl) ⟨3559436, by rfl⟩ : syracuseStep 4745915 = 7118873) B7118873
theorem B3163943 : Blo 2107435 3163943 := bstep (se 1 (by rfl) ⟨2372957, by rfl⟩ : syracuseStep 3163943 = 4745915) B4745915
theorem B2109295 : Blo 2107435 2109295 := bstep (se 1 (by rfl) ⟨1581971, by rfl⟩ : syracuseStep 2109295 = 3163943) B3163943
theorem B3163949 : Blo 2107435 3163949 := bbase (se 3 (by rfl) ⟨593240, by rfl⟩ : syracuseStep 3163949 = 1186481) (by norm_num)
theorem B2109299 : Blo 2107435 2109299 := bstep (se 1 (by rfl) ⟨1581974, by rfl⟩ : syracuseStep 2109299 = 3163949) B3163949
theorem B4745933 : Blo 2107435 4745933 := bbase (se 3 (by rfl) ⟨889862, by rfl⟩ : syracuseStep 4745933 = 1779725) (by norm_num)
theorem B3163955 : Blo 2107435 3163955 := bstep (se 1 (by rfl) ⟨2372966, by rfl⟩ : syracuseStep 3163955 = 4745933) B4745933
theorem B2109303 : Blo 2107435 2109303 := bstep (se 1 (by rfl) ⟨1581977, by rfl⟩ : syracuseStep 2109303 = 3163955) B3163955
theorem B2669593 : Blo 2107435 2669593 := bbase (se 2 (by rfl) ⟨1001097, by rfl⟩ : syracuseStep 2669593 = 2002195) (by norm_num)
theorem B3559457 : Blo 2107435 3559457 := bstep (se 2 (by rfl) ⟨1334796, by rfl⟩ : syracuseStep 3559457 = 2669593) B2669593
theorem B2372971 : Blo 2107435 2372971 := bstep (se 1 (by rfl) ⟨1779728, by rfl⟩ : syracuseStep 2372971 = 3559457) B3559457
theorem B3163961 : Blo 2107435 3163961 := bstep (se 2 (by rfl) ⟨1186485, by rfl⟩ : syracuseStep 3163961 = 2372971) B2372971
theorem B2109307 : Blo 2107435 2109307 := bstep (se 1 (by rfl) ⟨1581980, by rfl⟩ : syracuseStep 2109307 = 3163961) B3163961
theorem B9009893 : Blo 2107435 9009893 := bbase (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) (by norm_num)
theorem B24026381 : Blo 2107435 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B16017587 : Blo 2107435 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B10678391 : Blo 2107435 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B7118927 : Blo 2107435 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B4745951 : Blo 2107435 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B3163967 : Blo 2107435 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B2109311 : Blo 2107435 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B3163973 : Blo 2107435 3163973 := bbase (se 4 (by rfl) ⟨296622, by rfl⟩ : syracuseStep 3163973 = 593245) (by norm_num)
theorem B2109315 : Blo 2107435 2109315 := bstep (se 1 (by rfl) ⟨1581986, by rfl⟩ : syracuseStep 2109315 = 3163973) B3163973
theorem B3559477 : Blo 2107435 3559477 := bbase (se 5 (by rfl) ⟨166850, by rfl⟩ : syracuseStep 3559477 = 333701) (by norm_num)
theorem B4745969 : Blo 2107435 4745969 := bstep (se 2 (by rfl) ⟨1779738, by rfl⟩ : syracuseStep 4745969 = 3559477) B3559477
theorem B3163979 : Blo 2107435 3163979 := bstep (se 1 (by rfl) ⟨2372984, by rfl⟩ : syracuseStep 3163979 = 4745969) B4745969
theorem B2109319 : Blo 2107435 2109319 := bstep (se 1 (by rfl) ⟨1581989, by rfl⟩ : syracuseStep 2109319 = 3163979) B3163979
theorem B2372989 : Blo 2107435 2372989 := bbase (se 3 (by rfl) ⟨444935, by rfl⟩ : syracuseStep 2372989 = 889871) (by norm_num)
theorem B3163985 : Blo 2107435 3163985 := bstep (se 2 (by rfl) ⟨1186494, by rfl⟩ : syracuseStep 3163985 = 2372989) B2372989
theorem B2109323 : Blo 2107435 2109323 := bstep (se 1 (by rfl) ⟨1581992, by rfl⟩ : syracuseStep 2109323 = 3163985) B3163985
theorem B7118981 : Blo 2107435 7118981 := bbase (se 4 (by rfl) ⟨667404, by rfl⟩ : syracuseStep 7118981 = 1334809) (by norm_num)
theorem B4745987 : Blo 2107435 4745987 := bstep (se 1 (by rfl) ⟨3559490, by rfl⟩ : syracuseStep 4745987 = 7118981) B7118981
theorem B3163991 : Blo 2107435 3163991 := bstep (se 1 (by rfl) ⟨2372993, by rfl⟩ : syracuseStep 3163991 = 4745987) B4745987
theorem B2109327 : Blo 2107435 2109327 := bstep (se 1 (by rfl) ⟨1581995, by rfl⟩ : syracuseStep 2109327 = 3163991) B3163991
theorem B3163997 : Blo 2107435 3163997 := bbase (se 3 (by rfl) ⟨593249, by rfl⟩ : syracuseStep 3163997 = 1186499) (by norm_num)
theorem B2109331 : Blo 2107435 2109331 := bstep (se 1 (by rfl) ⟨1581998, by rfl⟩ : syracuseStep 2109331 = 3163997) B3163997
theorem B4746005 : Blo 2107435 4746005 := bbase (se 6 (by rfl) ⟨111234, by rfl⟩ : syracuseStep 4746005 = 222469) (by norm_num)
theorem B3164003 : Blo 2107435 3164003 := bstep (se 1 (by rfl) ⟨2373002, by rfl⟩ : syracuseStep 3164003 = 4746005) B4746005
theorem B2109335 : Blo 2107435 2109335 := bstep (se 1 (by rfl) ⟨1582001, by rfl⟩ : syracuseStep 2109335 = 3164003) B3164003
theorem B8008901 : Blo 2107435 8008901 := bbase (se 4 (by rfl) ⟨750834, by rfl⟩ : syracuseStep 8008901 = 1501669) (by norm_num)
theorem B5339267 : Blo 2107435 5339267 := bstep (se 1 (by rfl) ⟨4004450, by rfl⟩ : syracuseStep 5339267 = 8008901) B8008901
theorem B3559511 : Blo 2107435 3559511 := bstep (se 1 (by rfl) ⟨2669633, by rfl⟩ : syracuseStep 3559511 = 5339267) B5339267
theorem B2373007 : Blo 2107435 2373007 := bstep (se 1 (by rfl) ⟨1779755, by rfl⟩ : syracuseStep 2373007 = 3559511) B3559511
theorem B3164009 : Blo 2107435 3164009 := bstep (se 2 (by rfl) ⟨1186503, by rfl⟩ : syracuseStep 3164009 = 2373007) B2373007
theorem B2109339 : Blo 2107435 2109339 := bstep (se 1 (by rfl) ⟨1582004, by rfl⟩ : syracuseStep 2109339 = 3164009) B3164009
theorem B2405389 : Blo 2107435 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B3207185 : Blo 2107435 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B2138123 : Blo 2107435 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B5701661 : Blo 2107435 5701661 := bstep (se 3 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 5701661 = 2138123) B2138123
theorem B3801107 : Blo 2107435 3801107 := bstep (se 1 (by rfl) ⟨2850830, by rfl⟩ : syracuseStep 3801107 = 5701661) B5701661
theorem B10136285 : Blo 2107435 10136285 := bstep (se 3 (by rfl) ⟨1900553, by rfl⟩ : syracuseStep 10136285 = 3801107) B3801107
theorem B6757523 : Blo 2107435 6757523 := bstep (se 1 (by rfl) ⟨5068142, by rfl⟩ : syracuseStep 6757523 = 10136285) B10136285
theorem B4505015 : Blo 2107435 4505015 := bstep (se 1 (by rfl) ⟨3378761, by rfl⟩ : syracuseStep 4505015 = 6757523) B6757523
theorem B12013373 : Blo 2107435 12013373 := bstep (se 3 (by rfl) ⟨2252507, by rfl⟩ : syracuseStep 12013373 = 4505015) B4505015
theorem B8008915 : Blo 2107435 8008915 := bstep (se 1 (by rfl) ⟨6006686, by rfl⟩ : syracuseStep 8008915 = 12013373) B12013373
theorem B10678553 : Blo 2107435 10678553 := bstep (se 2 (by rfl) ⟨4004457, by rfl⟩ : syracuseStep 10678553 = 8008915) B8008915
theorem B7119035 : Blo 2107435 7119035 := bstep (se 1 (by rfl) ⟨5339276, by rfl⟩ : syracuseStep 7119035 = 10678553) B10678553
theorem B4746023 : Blo 2107435 4746023 := bstep (se 1 (by rfl) ⟨3559517, by rfl⟩ : syracuseStep 4746023 = 7119035) B7119035
theorem B3164015 : Blo 2107435 3164015 := bstep (se 1 (by rfl) ⟨2373011, by rfl⟩ : syracuseStep 3164015 = 4746023) B4746023
theorem B2109343 : Blo 2107435 2109343 := bstep (se 1 (by rfl) ⟨1582007, by rfl⟩ : syracuseStep 2109343 = 3164015) B3164015
theorem B3164021 : Blo 2107435 3164021 := bbase (se 5 (by rfl) ⟨148313, by rfl⟩ : syracuseStep 3164021 = 296627) (by norm_num)
theorem B2109347 : Blo 2107435 2109347 := bstep (se 1 (by rfl) ⟨1582010, by rfl⟩ : syracuseStep 2109347 = 3164021) B3164021
theorem B7602245 : Blo 2107435 7602245 := bbase (se 4 (by rfl) ⟨712710, by rfl⟩ : syracuseStep 7602245 = 1425421) (by norm_num)
theorem B5068163 : Blo 2107435 5068163 := bstep (se 1 (by rfl) ⟨3801122, by rfl⟩ : syracuseStep 5068163 = 7602245) B7602245
theorem B3378775 : Blo 2107435 3378775 := bstep (se 1 (by rfl) ⟨2534081, by rfl⟩ : syracuseStep 3378775 = 5068163) B5068163
theorem B4505033 : Blo 2107435 4505033 := bstep (se 2 (by rfl) ⟨1689387, by rfl⟩ : syracuseStep 4505033 = 3378775) B3378775
theorem B3003355 : Blo 2107435 3003355 := bstep (se 1 (by rfl) ⟨2252516, by rfl⟩ : syracuseStep 3003355 = 4505033) B4505033
theorem B4004473 : Blo 2107435 4004473 := bstep (se 2 (by rfl) ⟨1501677, by rfl⟩ : syracuseStep 4004473 = 3003355) B3003355
theorem B5339297 : Blo 2107435 5339297 := bstep (se 2 (by rfl) ⟨2002236, by rfl⟩ : syracuseStep 5339297 = 4004473) B4004473
theorem B3559531 : Blo 2107435 3559531 := bstep (se 1 (by rfl) ⟨2669648, by rfl⟩ : syracuseStep 3559531 = 5339297) B5339297
theorem B4746041 : Blo 2107435 4746041 := bstep (se 2 (by rfl) ⟨1779765, by rfl⟩ : syracuseStep 4746041 = 3559531) B3559531
theorem B3164027 : Blo 2107435 3164027 := bstep (se 1 (by rfl) ⟨2373020, by rfl⟩ : syracuseStep 3164027 = 4746041) B4746041
theorem B2109351 : Blo 2107435 2109351 := bstep (se 1 (by rfl) ⟨1582013, by rfl⟩ : syracuseStep 2109351 = 3164027) B3164027
theorem B2373025 : Blo 2107435 2373025 := bbase (se 2 (by rfl) ⟨889884, by rfl⟩ : syracuseStep 2373025 = 1779769) (by norm_num)
theorem B3164033 : Blo 2107435 3164033 := bstep (se 2 (by rfl) ⟨1186512, by rfl⟩ : syracuseStep 3164033 = 2373025) B2373025
theorem B2109355 : Blo 2107435 2109355 := bstep (se 1 (by rfl) ⟨1582016, by rfl⟩ : syracuseStep 2109355 = 3164033) B3164033
theorem B5339317 : Blo 2107435 5339317 := bbase (se 5 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 5339317 = 500561) (by norm_num)
theorem B7119089 : Blo 2107435 7119089 := bstep (se 2 (by rfl) ⟨2669658, by rfl⟩ : syracuseStep 7119089 = 5339317) B5339317
theorem B4746059 : Blo 2107435 4746059 := bstep (se 1 (by rfl) ⟨3559544, by rfl⟩ : syracuseStep 4746059 = 7119089) B7119089
theorem B3164039 : Blo 2107435 3164039 := bstep (se 1 (by rfl) ⟨2373029, by rfl⟩ : syracuseStep 3164039 = 4746059) B4746059
theorem B2109359 : Blo 2107435 2109359 := bstep (se 1 (by rfl) ⟨1582019, by rfl⟩ : syracuseStep 2109359 = 3164039) B3164039
theorem B3164045 : Blo 2107435 3164045 := bbase (se 3 (by rfl) ⟨593258, by rfl⟩ : syracuseStep 3164045 = 1186517) (by norm_num)
theorem B2109363 : Blo 2107435 2109363 := bstep (se 1 (by rfl) ⟨1582022, by rfl⟩ : syracuseStep 2109363 = 3164045) B3164045
theorem B4746077 : Blo 2107435 4746077 := bbase (se 3 (by rfl) ⟨889889, by rfl⟩ : syracuseStep 4746077 = 1779779) (by norm_num)
theorem B3164051 : Blo 2107435 3164051 := bstep (se 1 (by rfl) ⟨2373038, by rfl⟩ : syracuseStep 3164051 = 4746077) B4746077
theorem B2109367 : Blo 2107435 2109367 := bstep (se 1 (by rfl) ⟨1582025, by rfl⟩ : syracuseStep 2109367 = 3164051) B3164051
theorem B3559565 : Blo 2107435 3559565 := bbase (se 3 (by rfl) ⟨667418, by rfl⟩ : syracuseStep 3559565 = 1334837) (by norm_num)
theorem B2373043 : Blo 2107435 2373043 := bstep (se 1 (by rfl) ⟨1779782, by rfl⟩ : syracuseStep 2373043 = 3559565) B3559565
theorem B3164057 : Blo 2107435 3164057 := bstep (se 2 (by rfl) ⟨1186521, by rfl⟩ : syracuseStep 3164057 = 2373043) B2373043
theorem B2109371 : Blo 2107435 2109371 := bstep (se 1 (by rfl) ⟨1582028, by rfl⟩ : syracuseStep 2109371 = 3164057) B3164057
theorem B2405425 : Blo 2107435 2405425 := bbase (se 2 (by rfl) ⟨902034, by rfl⟩ : syracuseStep 2405425 = 1804069) (by norm_num)
theorem B3207233 : Blo 2107435 3207233 := bstep (se 2 (by rfl) ⟨1202712, by rfl⟩ : syracuseStep 3207233 = 2405425) B2405425
theorem B8552621 : Blo 2107435 8552621 := bstep (se 3 (by rfl) ⟨1603616, by rfl⟩ : syracuseStep 8552621 = 3207233) B3207233
theorem B5701747 : Blo 2107435 5701747 := bstep (se 1 (by rfl) ⟨4276310, by rfl⟩ : syracuseStep 5701747 = 8552621) B8552621
theorem B7602329 : Blo 2107435 7602329 := bstep (se 2 (by rfl) ⟨2850873, by rfl⟩ : syracuseStep 7602329 = 5701747) B5701747
theorem B5068219 : Blo 2107435 5068219 := bstep (se 1 (by rfl) ⟨3801164, by rfl⟩ : syracuseStep 5068219 = 7602329) B7602329
theorem B6757625 : Blo 2107435 6757625 := bstep (se 2 (by rfl) ⟨2534109, by rfl⟩ : syracuseStep 6757625 = 5068219) B5068219
theorem B18020333 : Blo 2107435 18020333 := bstep (se 3 (by rfl) ⟨3378812, by rfl⟩ : syracuseStep 18020333 = 6757625) B6757625
theorem B12013555 : Blo 2107435 12013555 := bstep (se 1 (by rfl) ⟨9010166, by rfl⟩ : syracuseStep 12013555 = 18020333) B18020333
theorem B16018073 : Blo 2107435 16018073 := bstep (se 2 (by rfl) ⟨6006777, by rfl⟩ : syracuseStep 16018073 = 12013555) B12013555
theorem B10678715 : Blo 2107435 10678715 := bstep (se 1 (by rfl) ⟨8009036, by rfl⟩ : syracuseStep 10678715 = 16018073) B16018073
theorem B7119143 : Blo 2107435 7119143 := bstep (se 1 (by rfl) ⟨5339357, by rfl⟩ : syracuseStep 7119143 = 10678715) B10678715
theorem B4746095 : Blo 2107435 4746095 := bstep (se 1 (by rfl) ⟨3559571, by rfl⟩ : syracuseStep 4746095 = 7119143) B7119143
theorem B3164063 : Blo 2107435 3164063 := bstep (se 1 (by rfl) ⟨2373047, by rfl⟩ : syracuseStep 3164063 = 4746095) B4746095
theorem B2109375 : Blo 2107435 2109375 := bstep (se 1 (by rfl) ⟨1582031, by rfl⟩ : syracuseStep 2109375 = 3164063) B3164063
theorem B3164069 : Blo 2107435 3164069 := bbase (se 4 (by rfl) ⟨296631, by rfl⟩ : syracuseStep 3164069 = 593263) (by norm_num)
theorem B2109379 : Blo 2107435 2109379 := bstep (se 1 (by rfl) ⟨1582034, by rfl⟩ : syracuseStep 2109379 = 3164069) B3164069
theorem B2669689 : Blo 2107435 2669689 := bbase (se 2 (by rfl) ⟨1001133, by rfl⟩ : syracuseStep 2669689 = 2002267) (by norm_num)
theorem B3559585 : Blo 2107435 3559585 := bstep (se 2 (by rfl) ⟨1334844, by rfl⟩ : syracuseStep 3559585 = 2669689) B2669689
theorem B4746113 : Blo 2107435 4746113 := bstep (se 2 (by rfl) ⟨1779792, by rfl⟩ : syracuseStep 4746113 = 3559585) B3559585
theorem B3164075 : Blo 2107435 3164075 := bstep (se 1 (by rfl) ⟨2373056, by rfl⟩ : syracuseStep 3164075 = 4746113) B4746113
theorem B2109383 : Blo 2107435 2109383 := bstep (se 1 (by rfl) ⟨1582037, by rfl⟩ : syracuseStep 2109383 = 3164075) B3164075
theorem B2373061 : Blo 2107435 2373061 := bbase (se 4 (by rfl) ⟨222474, by rfl⟩ : syracuseStep 2373061 = 444949) (by norm_num)
theorem B3164081 : Blo 2107435 3164081 := bstep (se 2 (by rfl) ⟨1186530, by rfl⟩ : syracuseStep 3164081 = 2373061) B2373061
theorem B2109387 : Blo 2107435 2109387 := bstep (se 1 (by rfl) ⟨1582040, by rfl⟩ : syracuseStep 2109387 = 3164081) B3164081
theorem B4004549 : Blo 2107435 4004549 := bbase (se 4 (by rfl) ⟨375426, by rfl⟩ : syracuseStep 4004549 = 750853) (by norm_num)
theorem B2669699 : Blo 2107435 2669699 := bstep (se 1 (by rfl) ⟨2002274, by rfl⟩ : syracuseStep 2669699 = 4004549) B4004549
theorem B7119197 : Blo 2107435 7119197 := bstep (se 3 (by rfl) ⟨1334849, by rfl⟩ : syracuseStep 7119197 = 2669699) B2669699
theorem B4746131 : Blo 2107435 4746131 := bstep (se 1 (by rfl) ⟨3559598, by rfl⟩ : syracuseStep 4746131 = 7119197) B7119197
theorem B3164087 : Blo 2107435 3164087 := bstep (se 1 (by rfl) ⟨2373065, by rfl⟩ : syracuseStep 3164087 = 4746131) B4746131
theorem B2109391 : Blo 2107435 2109391 := bstep (se 1 (by rfl) ⟨1582043, by rfl⟩ : syracuseStep 2109391 = 3164087) B3164087
theorem B3164093 : Blo 2107435 3164093 := bbase (se 3 (by rfl) ⟨593267, by rfl⟩ : syracuseStep 3164093 = 1186535) (by norm_num)
theorem B2109395 : Blo 2107435 2109395 := bstep (se 1 (by rfl) ⟨1582046, by rfl⟩ : syracuseStep 2109395 = 3164093) B3164093
theorem B4746149 : Blo 2107435 4746149 := bbase (se 4 (by rfl) ⟨444951, by rfl⟩ : syracuseStep 4746149 = 889903) (by norm_num)
theorem B3164099 : Blo 2107435 3164099 := bstep (se 1 (by rfl) ⟨2373074, by rfl⟩ : syracuseStep 3164099 = 4746149) B4746149
theorem B2109399 : Blo 2107435 2109399 := bstep (se 1 (by rfl) ⟨1582049, by rfl⟩ : syracuseStep 2109399 = 3164099) B3164099
theorem B5339429 : Blo 2107435 5339429 := bbase (se 4 (by rfl) ⟨500571, by rfl⟩ : syracuseStep 5339429 = 1001143) (by norm_num)
theorem B3559619 : Blo 2107435 3559619 := bstep (se 1 (by rfl) ⟨2669714, by rfl⟩ : syracuseStep 3559619 = 5339429) B5339429
theorem B2373079 : Blo 2107435 2373079 := bstep (se 1 (by rfl) ⟨1779809, by rfl⟩ : syracuseStep 2373079 = 3559619) B3559619
theorem B3164105 : Blo 2107435 3164105 := bstep (se 2 (by rfl) ⟨1186539, by rfl⟩ : syracuseStep 3164105 = 2373079) B2373079
theorem B2109403 : Blo 2107435 2109403 := bstep (se 1 (by rfl) ⟨1582052, by rfl⟩ : syracuseStep 2109403 = 3164105) B3164105
theorem B6006869 : Blo 2107435 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B4004579 : Blo 2107435 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B10678877 : Blo 2107435 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B7119251 : Blo 2107435 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B4746167 : Blo 2107435 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B3164111 : Blo 2107435 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B2109407 : Blo 2107435 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B3164117 : Blo 2107435 3164117 := bbase (se 7 (by rfl) ⟨37079, by rfl⟩ : syracuseStep 3164117 = 74159) (by norm_num)
theorem B2109411 : Blo 2107435 2109411 := bstep (se 1 (by rfl) ⟨1582058, by rfl⟩ : syracuseStep 2109411 = 3164117) B3164117
theorem B8009189 : Blo 2107435 8009189 := bbase (se 4 (by rfl) ⟨750861, by rfl⟩ : syracuseStep 8009189 = 1501723) (by norm_num)
theorem B5339459 : Blo 2107435 5339459 := bstep (se 1 (by rfl) ⟨4004594, by rfl⟩ : syracuseStep 5339459 = 8009189) B8009189
theorem B3559639 : Blo 2107435 3559639 := bstep (se 1 (by rfl) ⟨2669729, by rfl⟩ : syracuseStep 3559639 = 5339459) B5339459
theorem B4746185 : Blo 2107435 4746185 := bstep (se 2 (by rfl) ⟨1779819, by rfl⟩ : syracuseStep 4746185 = 3559639) B3559639
theorem B3164123 : Blo 2107435 3164123 := bstep (se 1 (by rfl) ⟨2373092, by rfl⟩ : syracuseStep 3164123 = 4746185) B4746185
theorem B2109415 : Blo 2107435 2109415 := bstep (se 1 (by rfl) ⟨1582061, by rfl⟩ : syracuseStep 2109415 = 3164123) B3164123
theorem B2373097 : Blo 2107435 2373097 := bbase (se 2 (by rfl) ⟨889911, by rfl⟩ : syracuseStep 2373097 = 1779823) (by norm_num)
theorem B3164129 : Blo 2107435 3164129 := bstep (se 2 (by rfl) ⟨1186548, by rfl⟩ : syracuseStep 3164129 = 2373097) B2373097
theorem B2109419 : Blo 2107435 2109419 := bstep (se 1 (by rfl) ⟨1582064, by rfl⟩ : syracuseStep 2109419 = 3164129) B3164129
theorem B2252593 : Blo 2107435 2252593 := bbase (se 2 (by rfl) ⟨844722, by rfl⟩ : syracuseStep 2252593 = 1689445) (by norm_num)
theorem B12013829 : Blo 2107435 12013829 := bstep (se 4 (by rfl) ⟨1126296, by rfl⟩ : syracuseStep 12013829 = 2252593) B2252593
theorem B8009219 : Blo 2107435 8009219 := bstep (se 1 (by rfl) ⟨6006914, by rfl⟩ : syracuseStep 8009219 = 12013829) B12013829
theorem B5339479 : Blo 2107435 5339479 := bstep (se 1 (by rfl) ⟨4004609, by rfl⟩ : syracuseStep 5339479 = 8009219) B8009219
theorem B7119305 : Blo 2107435 7119305 := bstep (se 2 (by rfl) ⟨2669739, by rfl⟩ : syracuseStep 7119305 = 5339479) B5339479
theorem B4746203 : Blo 2107435 4746203 := bstep (se 1 (by rfl) ⟨3559652, by rfl⟩ : syracuseStep 4746203 = 7119305) B7119305
theorem B3164135 : Blo 2107435 3164135 := bstep (se 1 (by rfl) ⟨2373101, by rfl⟩ : syracuseStep 3164135 = 4746203) B4746203
theorem B2109423 : Blo 2107435 2109423 := bstep (se 1 (by rfl) ⟨1582067, by rfl⟩ : syracuseStep 2109423 = 3164135) B3164135
theorem B3164141 : Blo 2107435 3164141 := bbase (se 3 (by rfl) ⟨593276, by rfl⟩ : syracuseStep 3164141 = 1186553) (by norm_num)
theorem B2109427 : Blo 2107435 2109427 := bstep (se 1 (by rfl) ⟨1582070, by rfl⟩ : syracuseStep 2109427 = 3164141) B3164141
theorem B4746221 : Blo 2107435 4746221 := bbase (se 3 (by rfl) ⟨889916, by rfl⟩ : syracuseStep 4746221 = 1779833) (by norm_num)
theorem B3164147 : Blo 2107435 3164147 := bstep (se 1 (by rfl) ⟨2373110, by rfl⟩ : syracuseStep 3164147 = 4746221) B4746221
theorem B2109431 : Blo 2107435 2109431 := bstep (se 1 (by rfl) ⟨1582073, by rfl⟩ : syracuseStep 2109431 = 3164147) B3164147
theorem B4505213 : Blo 2107435 4505213 := bbase (se 3 (by rfl) ⟨844727, by rfl⟩ : syracuseStep 4505213 = 1689455) (by norm_num)
theorem B3003475 : Blo 2107435 3003475 := bstep (se 1 (by rfl) ⟨2252606, by rfl⟩ : syracuseStep 3003475 = 4505213) B4505213
theorem B4004633 : Blo 2107435 4004633 := bstep (se 2 (by rfl) ⟨1501737, by rfl⟩ : syracuseStep 4004633 = 3003475) B3003475
theorem B2669755 : Blo 2107435 2669755 := bstep (se 1 (by rfl) ⟨2002316, by rfl⟩ : syracuseStep 2669755 = 4004633) B4004633
theorem B3559673 : Blo 2107435 3559673 := bstep (se 2 (by rfl) ⟨1334877, by rfl⟩ : syracuseStep 3559673 = 2669755) B2669755
theorem B2373115 : Blo 2107435 2373115 := bstep (se 1 (by rfl) ⟨1779836, by rfl⟩ : syracuseStep 2373115 = 3559673) B3559673
theorem B3164153 : Blo 2107435 3164153 := bstep (se 2 (by rfl) ⟨1186557, by rfl⟩ : syracuseStep 3164153 = 2373115) B2373115
theorem B2109435 : Blo 2107435 2109435 := bstep (se 1 (by rfl) ⟨1582076, by rfl⟩ : syracuseStep 2109435 = 3164153) B3164153
theorem C0 (j : ℕ) (h1 : 526858 ≤ j) (h2 : j ≤ 527358) : Blo 2107435 (4 * j + 3) := by
  interval_cases j
  · exact B2107435
  · exact B2107439
  · exact B2107443
  · exact B2107447
  · exact B2107451
  · exact B2107455
  · exact B2107459
  · exact B2107463
  · exact B2107467
  · exact B2107471
  · exact B2107475
  · exact B2107479
  · exact B2107483
  · exact B2107487
  · exact B2107491
  · exact B2107495
  · exact B2107499
  · exact B2107503
  · exact B2107507
  · exact B2107511
  · exact B2107515
  · exact B2107519
  · exact B2107523
  · exact B2107527
  · exact B2107531
  · exact B2107535
  · exact B2107539
  · exact B2107543
  · exact B2107547
  · exact B2107551
  · exact B2107555
  · exact B2107559
  · exact B2107563
  · exact B2107567
  · exact B2107571
  · exact B2107575
  · exact B2107579
  · exact B2107583
  · exact B2107587
  · exact B2107591
  · exact B2107595
  · exact B2107599
  · exact B2107603
  · exact B2107607
  · exact B2107611
  · exact B2107615
  · exact B2107619
  · exact B2107623
  · exact B2107627
  · exact B2107631
  · exact B2107635
  · exact B2107639
  · exact B2107643
  · exact B2107647
  · exact B2107651
  · exact B2107655
  · exact B2107659
  · exact B2107663
  · exact B2107667
  · exact B2107671
  · exact B2107675
  · exact B2107679
  · exact B2107683
  · exact B2107687
  · exact B2107691
  · exact B2107695
  · exact B2107699
  · exact B2107703
  · exact B2107707
  · exact B2107711
  · exact B2107715
  · exact B2107719
  · exact B2107723
  · exact B2107727
  · exact B2107731
  · exact B2107735
  · exact B2107739
  · exact B2107743
  · exact B2107747
  · exact B2107751
  · exact B2107755
  · exact B2107759
  · exact B2107763
  · exact B2107767
  · exact B2107771
  · exact B2107775
  · exact B2107779
  · exact B2107783
  · exact B2107787
  · exact B2107791
  · exact B2107795
  · exact B2107799
  · exact B2107803
  · exact B2107807
  · exact B2107811
  · exact B2107815
  · exact B2107819
  · exact B2107823
  · exact B2107827
  · exact B2107831
  · exact B2107835
  · exact B2107839
  · exact B2107843
  · exact B2107847
  · exact B2107851
  · exact B2107855
  · exact B2107859
  · exact B2107863
  · exact B2107867
  · exact B2107871
  · exact B2107875
  · exact B2107879
  · exact B2107883
  · exact B2107887
  · exact B2107891
  · exact B2107895
  · exact B2107899
  · exact B2107903
  · exact B2107907
  · exact B2107911
  · exact B2107915
  · exact B2107919
  · exact B2107923
  · exact B2107927
  · exact B2107931
  · exact B2107935
  · exact B2107939
  · exact B2107943
  · exact B2107947
  · exact B2107951
  · exact B2107955
  · exact B2107959
  · exact B2107963
  · exact B2107967
  · exact B2107971
  · exact B2107975
  · exact B2107979
  · exact B2107983
  · exact B2107987
  · exact B2107991
  · exact B2107995
  · exact B2107999
  · exact B2108003
  · exact B2108007
  · exact B2108011
  · exact B2108015
  · exact B2108019
  · exact B2108023
  · exact B2108027
  · exact B2108031
  · exact B2108035
  · exact B2108039
  · exact B2108043
  · exact B2108047
  · exact B2108051
  · exact B2108055
  · exact B2108059
  · exact B2108063
  · exact B2108067
  · exact B2108071
  · exact B2108075
  · exact B2108079
  · exact B2108083
  · exact B2108087
  · exact B2108091
  · exact B2108095
  · exact B2108099
  · exact B2108103
  · exact B2108107
  · exact B2108111
  · exact B2108115
  · exact B2108119
  · exact B2108123
  · exact B2108127
  · exact B2108131
  · exact B2108135
  · exact B2108139
  · exact B2108143
  · exact B2108147
  · exact B2108151
  · exact B2108155
  · exact B2108159
  · exact B2108163
  · exact B2108167
  · exact B2108171
  · exact B2108175
  · exact B2108179
  · exact B2108183
  · exact B2108187
  · exact B2108191
  · exact B2108195
  · exact B2108199
  · exact B2108203
  · exact B2108207
  · exact B2108211
  · exact B2108215
  · exact B2108219
  · exact B2108223
  · exact B2108227
  · exact B2108231
  · exact B2108235
  · exact B2108239
  · exact B2108243
  · exact B2108247
  · exact B2108251
  · exact B2108255
  · exact B2108259
  · exact B2108263
  · exact B2108267
  · exact B2108271
  · exact B2108275
  · exact B2108279
  · exact B2108283
  · exact B2108287
  · exact B2108291
  · exact B2108295
  · exact B2108299
  · exact B2108303
  · exact B2108307
  · exact B2108311
  · exact B2108315
  · exact B2108319
  · exact B2108323
  · exact B2108327
  · exact B2108331
  · exact B2108335
  · exact B2108339
  · exact B2108343
  · exact B2108347
  · exact B2108351
  · exact B2108355
  · exact B2108359
  · exact B2108363
  · exact B2108367
  · exact B2108371
  · exact B2108375
  · exact B2108379
  · exact B2108383
  · exact B2108387
  · exact B2108391
  · exact B2108395
  · exact B2108399
  · exact B2108403
  · exact B2108407
  · exact B2108411
  · exact B2108415
  · exact B2108419
  · exact B2108423
  · exact B2108427
  · exact B2108431
  · exact B2108435
  · exact B2108439
  · exact B2108443
  · exact B2108447
  · exact B2108451
  · exact B2108455
  · exact B2108459
  · exact B2108463
  · exact B2108467
  · exact B2108471
  · exact B2108475
  · exact B2108479
  · exact B2108483
  · exact B2108487
  · exact B2108491
  · exact B2108495
  · exact B2108499
  · exact B2108503
  · exact B2108507
  · exact B2108511
  · exact B2108515
  · exact B2108519
  · exact B2108523
  · exact B2108527
  · exact B2108531
  · exact B2108535
  · exact B2108539
  · exact B2108543
  · exact B2108547
  · exact B2108551
  · exact B2108555
  · exact B2108559
  · exact B2108563
  · exact B2108567
  · exact B2108571
  · exact B2108575
  · exact B2108579
  · exact B2108583
  · exact B2108587
  · exact B2108591
  · exact B2108595
  · exact B2108599
  · exact B2108603
  · exact B2108607
  · exact B2108611
  · exact B2108615
  · exact B2108619
  · exact B2108623
  · exact B2108627
  · exact B2108631
  · exact B2108635
  · exact B2108639
  · exact B2108643
  · exact B2108647
  · exact B2108651
  · exact B2108655
  · exact B2108659
  · exact B2108663
  · exact B2108667
  · exact B2108671
  · exact B2108675
  · exact B2108679
  · exact B2108683
  · exact B2108687
  · exact B2108691
  · exact B2108695
  · exact B2108699
  · exact B2108703
  · exact B2108707
  · exact B2108711
  · exact B2108715
  · exact B2108719
  · exact B2108723
  · exact B2108727
  · exact B2108731
  · exact B2108735
  · exact B2108739
  · exact B2108743
  · exact B2108747
  · exact B2108751
  · exact B2108755
  · exact B2108759
  · exact B2108763
  · exact B2108767
  · exact B2108771
  · exact B2108775
  · exact B2108779
  · exact B2108783
  · exact B2108787
  · exact B2108791
  · exact B2108795
  · exact B2108799
  · exact B2108803
  · exact B2108807
  · exact B2108811
  · exact B2108815
  · exact B2108819
  · exact B2108823
  · exact B2108827
  · exact B2108831
  · exact B2108835
  · exact B2108839
  · exact B2108843
  · exact B2108847
  · exact B2108851
  · exact B2108855
  · exact B2108859
  · exact B2108863
  · exact B2108867
  · exact B2108871
  · exact B2108875
  · exact B2108879
  · exact B2108883
  · exact B2108887
  · exact B2108891
  · exact B2108895
  · exact B2108899
  · exact B2108903
  · exact B2108907
  · exact B2108911
  · exact B2108915
  · exact B2108919
  · exact B2108923
  · exact B2108927
  · exact B2108931
  · exact B2108935
  · exact B2108939
  · exact B2108943
  · exact B2108947
  · exact B2108951
  · exact B2108955
  · exact B2108959
  · exact B2108963
  · exact B2108967
  · exact B2108971
  · exact B2108975
  · exact B2108979
  · exact B2108983
  · exact B2108987
  · exact B2108991
  · exact B2108995
  · exact B2108999
  · exact B2109003
  · exact B2109007
  · exact B2109011
  · exact B2109015
  · exact B2109019
  · exact B2109023
  · exact B2109027
  · exact B2109031
  · exact B2109035
  · exact B2109039
  · exact B2109043
  · exact B2109047
  · exact B2109051
  · exact B2109055
  · exact B2109059
  · exact B2109063
  · exact B2109067
  · exact B2109071
  · exact B2109075
  · exact B2109079
  · exact B2109083
  · exact B2109087
  · exact B2109091
  · exact B2109095
  · exact B2109099
  · exact B2109103
  · exact B2109107
  · exact B2109111
  · exact B2109115
  · exact B2109119
  · exact B2109123
  · exact B2109127
  · exact B2109131
  · exact B2109135
  · exact B2109139
  · exact B2109143
  · exact B2109147
  · exact B2109151
  · exact B2109155
  · exact B2109159
  · exact B2109163
  · exact B2109167
  · exact B2109171
  · exact B2109175
  · exact B2109179
  · exact B2109183
  · exact B2109187
  · exact B2109191
  · exact B2109195
  · exact B2109199
  · exact B2109203
  · exact B2109207
  · exact B2109211
  · exact B2109215
  · exact B2109219
  · exact B2109223
  · exact B2109227
  · exact B2109231
  · exact B2109235
  · exact B2109239
  · exact B2109243
  · exact B2109247
  · exact B2109251
  · exact B2109255
  · exact B2109259
  · exact B2109263
  · exact B2109267
  · exact B2109271
  · exact B2109275
  · exact B2109279
  · exact B2109283
  · exact B2109287
  · exact B2109291
  · exact B2109295
  · exact B2109299
  · exact B2109303
  · exact B2109307
  · exact B2109311
  · exact B2109315
  · exact B2109319
  · exact B2109323
  · exact B2109327
  · exact B2109331
  · exact B2109335
  · exact B2109339
  · exact B2109343
  · exact B2109347
  · exact B2109351
  · exact B2109355
  · exact B2109359
  · exact B2109363
  · exact B2109367
  · exact B2109371
  · exact B2109375
  · exact B2109379
  · exact B2109383
  · exact B2109387
  · exact B2109391
  · exact B2109395
  · exact B2109399
  · exact B2109403
  · exact B2109407
  · exact B2109411
  · exact B2109415
  · exact B2109419
  · exact B2109423
  · exact B2109427
  · exact B2109431
  · exact B2109435
theorem solution (m : ℕ) (hlo : 2107435 ≤ m) (hhi : m ≤ 2109435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 526858 ≤ j := by omega
    have hj2 : j ≤ 527358 := by omega
    have hb : Blo 2107435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
