-- Prove2me | solution 1 for syracuse_descends_range_2019435_2021435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:50.624691+00:00
-- url     : https://prove2.me/submissions/a5d1e36a-47c6-4bac-b6c4-bd3e18c7fd6a

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

theorem B2271865 : Blo 2019435 2271865 := bbase (se 2 (by rfl) ⟨851949, by rfl⟩ : syracuseStep 2271865 = 1703899) (by norm_num)
theorem B3029153 : Blo 2019435 3029153 := bstep (se 2 (by rfl) ⟨1135932, by rfl⟩ : syracuseStep 3029153 = 2271865) B2271865
theorem B2019435 : Blo 2019435 2019435 := bstep (se 1 (by rfl) ⟨1514576, by rfl⟩ : syracuseStep 2019435 = 3029153) B3029153
theorem B3454301 : Blo 2019435 3454301 := bbase (se 3 (by rfl) ⟨647681, by rfl⟩ : syracuseStep 3454301 = 1295363) (by norm_num)
theorem B2302867 : Blo 2019435 2302867 := bstep (se 1 (by rfl) ⟨1727150, by rfl⟩ : syracuseStep 2302867 = 3454301) B3454301
theorem B3070489 : Blo 2019435 3070489 := bstep (se 2 (by rfl) ⟨1151433, by rfl⟩ : syracuseStep 3070489 = 2302867) B2302867
theorem B4093985 : Blo 2019435 4093985 := bstep (se 2 (by rfl) ⟨1535244, by rfl⟩ : syracuseStep 4093985 = 3070489) B3070489
theorem B2729323 : Blo 2019435 2729323 := bstep (se 1 (by rfl) ⟨2046992, by rfl⟩ : syracuseStep 2729323 = 4093985) B4093985
theorem B3639097 : Blo 2019435 3639097 := bstep (se 2 (by rfl) ⟨1364661, by rfl⟩ : syracuseStep 3639097 = 2729323) B2729323
theorem B19408517 : Blo 2019435 19408517 := bstep (se 4 (by rfl) ⟨1819548, by rfl⟩ : syracuseStep 19408517 = 3639097) B3639097
theorem B12939011 : Blo 2019435 12939011 := bstep (se 1 (by rfl) ⟨9704258, by rfl⟩ : syracuseStep 12939011 = 19408517) B19408517
theorem B8626007 : Blo 2019435 8626007 := bstep (se 1 (by rfl) ⟨6469505, by rfl⟩ : syracuseStep 8626007 = 12939011) B12939011
theorem B5750671 : Blo 2019435 5750671 := bstep (se 1 (by rfl) ⟨4313003, by rfl⟩ : syracuseStep 5750671 = 8626007) B8626007
theorem B7667561 : Blo 2019435 7667561 := bstep (se 2 (by rfl) ⟨2875335, by rfl⟩ : syracuseStep 7667561 = 5750671) B5750671
theorem B5111707 : Blo 2019435 5111707 := bstep (se 1 (by rfl) ⟨3833780, by rfl⟩ : syracuseStep 5111707 = 7667561) B7667561
theorem B6815609 : Blo 2019435 6815609 := bstep (se 2 (by rfl) ⟨2555853, by rfl⟩ : syracuseStep 6815609 = 5111707) B5111707
theorem B4543739 : Blo 2019435 4543739 := bstep (se 1 (by rfl) ⟨3407804, by rfl⟩ : syracuseStep 4543739 = 6815609) B6815609
theorem B3029159 : Blo 2019435 3029159 := bstep (se 1 (by rfl) ⟨2271869, by rfl⟩ : syracuseStep 3029159 = 4543739) B4543739
theorem B2019439 : Blo 2019435 2019439 := bstep (se 1 (by rfl) ⟨1514579, by rfl⟩ : syracuseStep 2019439 = 3029159) B3029159
theorem B3029165 : Blo 2019435 3029165 := bbase (se 3 (by rfl) ⟨567968, by rfl⟩ : syracuseStep 3029165 = 1135937) (by norm_num)
theorem B2019443 : Blo 2019435 2019443 := bstep (se 1 (by rfl) ⟨1514582, by rfl⟩ : syracuseStep 2019443 = 3029165) B3029165
theorem B4543757 : Blo 2019435 4543757 := bbase (se 3 (by rfl) ⟨851954, by rfl⟩ : syracuseStep 4543757 = 1703909) (by norm_num)
theorem B3029171 : Blo 2019435 3029171 := bstep (se 1 (by rfl) ⟨2271878, by rfl⟩ : syracuseStep 3029171 = 4543757) B4543757
theorem B2019447 : Blo 2019435 2019447 := bstep (se 1 (by rfl) ⟨1514585, by rfl⟩ : syracuseStep 2019447 = 3029171) B3029171
theorem B2555869 : Blo 2019435 2555869 := bbase (se 3 (by rfl) ⟨479225, by rfl⟩ : syracuseStep 2555869 = 958451) (by norm_num)
theorem B3407825 : Blo 2019435 3407825 := bstep (se 2 (by rfl) ⟨1277934, by rfl⟩ : syracuseStep 3407825 = 2555869) B2555869
theorem B2271883 : Blo 2019435 2271883 := bstep (se 1 (by rfl) ⟨1703912, by rfl⟩ : syracuseStep 2271883 = 3407825) B3407825
theorem B3029177 : Blo 2019435 3029177 := bstep (se 2 (by rfl) ⟨1135941, by rfl⟩ : syracuseStep 3029177 = 2271883) B2271883
theorem B2019451 : Blo 2019435 2019451 := bstep (se 1 (by rfl) ⟨1514588, by rfl⟩ : syracuseStep 2019451 = 3029177) B3029177
theorem B17252149 : Blo 2019435 17252149 := bbase (se 5 (by rfl) ⟨808694, by rfl⟩ : syracuseStep 17252149 = 1617389) (by norm_num)
theorem B23002865 : Blo 2019435 23002865 := bstep (se 2 (by rfl) ⟨8626074, by rfl⟩ : syracuseStep 23002865 = 17252149) B17252149
theorem B15335243 : Blo 2019435 15335243 := bstep (se 1 (by rfl) ⟨11501432, by rfl⟩ : syracuseStep 15335243 = 23002865) B23002865
theorem B10223495 : Blo 2019435 10223495 := bstep (se 1 (by rfl) ⟨7667621, by rfl⟩ : syracuseStep 10223495 = 15335243) B15335243
theorem B6815663 : Blo 2019435 6815663 := bstep (se 1 (by rfl) ⟨5111747, by rfl⟩ : syracuseStep 6815663 = 10223495) B10223495
theorem B4543775 : Blo 2019435 4543775 := bstep (se 1 (by rfl) ⟨3407831, by rfl⟩ : syracuseStep 4543775 = 6815663) B6815663
theorem B3029183 : Blo 2019435 3029183 := bstep (se 1 (by rfl) ⟨2271887, by rfl⟩ : syracuseStep 3029183 = 4543775) B4543775
theorem B2019455 : Blo 2019435 2019455 := bstep (se 1 (by rfl) ⟨1514591, by rfl⟩ : syracuseStep 2019455 = 3029183) B3029183
theorem B3029189 : Blo 2019435 3029189 := bbase (se 4 (by rfl) ⟨283986, by rfl⟩ : syracuseStep 3029189 = 567973) (by norm_num)
theorem B2019459 : Blo 2019435 2019459 := bstep (se 1 (by rfl) ⟨1514594, by rfl⟩ : syracuseStep 2019459 = 3029189) B3029189
theorem B3407845 : Blo 2019435 3407845 := bbase (se 4 (by rfl) ⟨319485, by rfl⟩ : syracuseStep 3407845 = 638971) (by norm_num)
theorem B4543793 : Blo 2019435 4543793 := bstep (se 2 (by rfl) ⟨1703922, by rfl⟩ : syracuseStep 4543793 = 3407845) B3407845
theorem B3029195 : Blo 2019435 3029195 := bstep (se 1 (by rfl) ⟨2271896, by rfl⟩ : syracuseStep 3029195 = 4543793) B4543793
theorem B2019463 : Blo 2019435 2019463 := bstep (se 1 (by rfl) ⟨1514597, by rfl⟩ : syracuseStep 2019463 = 3029195) B3029195
theorem B2271901 : Blo 2019435 2271901 := bbase (se 3 (by rfl) ⟨425981, by rfl⟩ : syracuseStep 2271901 = 851963) (by norm_num)
theorem B3029201 : Blo 2019435 3029201 := bstep (se 2 (by rfl) ⟨1135950, by rfl⟩ : syracuseStep 3029201 = 2271901) B2271901
theorem B2019467 : Blo 2019435 2019467 := bstep (se 1 (by rfl) ⟨1514600, by rfl⟩ : syracuseStep 2019467 = 3029201) B3029201
theorem B6815717 : Blo 2019435 6815717 := bbase (se 4 (by rfl) ⟨638973, by rfl⟩ : syracuseStep 6815717 = 1277947) (by norm_num)
theorem B4543811 : Blo 2019435 4543811 := bstep (se 1 (by rfl) ⟨3407858, by rfl⟩ : syracuseStep 4543811 = 6815717) B6815717
theorem B3029207 : Blo 2019435 3029207 := bstep (se 1 (by rfl) ⟨2271905, by rfl⟩ : syracuseStep 3029207 = 4543811) B4543811
theorem B2019471 : Blo 2019435 2019471 := bstep (se 1 (by rfl) ⟨1514603, by rfl⟩ : syracuseStep 2019471 = 3029207) B3029207
theorem B3029213 : Blo 2019435 3029213 := bbase (se 3 (by rfl) ⟨567977, by rfl⟩ : syracuseStep 3029213 = 1135955) (by norm_num)
theorem B2019475 : Blo 2019435 2019475 := bstep (se 1 (by rfl) ⟨1514606, by rfl⟩ : syracuseStep 2019475 = 3029213) B3029213
theorem B4543829 : Blo 2019435 4543829 := bbase (se 20 (by rfl) ⟨6, by rfl⟩ : syracuseStep 4543829 = 13) (by norm_num)
theorem B3029219 : Blo 2019435 3029219 := bstep (se 1 (by rfl) ⟨2271914, by rfl⟩ : syracuseStep 3029219 = 4543829) B4543829
theorem B2019479 : Blo 2019435 2019479 := bstep (se 1 (by rfl) ⟨1514609, by rfl⟩ : syracuseStep 2019479 = 3029219) B3029219
theorem B2156549 : Blo 2019435 2156549 := bbase (se 4 (by rfl) ⟨202176, by rfl⟩ : syracuseStep 2156549 = 404353) (by norm_num)
theorem B5750797 : Blo 2019435 5750797 := bstep (se 3 (by rfl) ⟨1078274, by rfl⟩ : syracuseStep 5750797 = 2156549) B2156549
theorem B7667729 : Blo 2019435 7667729 := bstep (se 2 (by rfl) ⟨2875398, by rfl⟩ : syracuseStep 7667729 = 5750797) B5750797
theorem B5111819 : Blo 2019435 5111819 := bstep (se 1 (by rfl) ⟨3833864, by rfl⟩ : syracuseStep 5111819 = 7667729) B7667729
theorem B3407879 : Blo 2019435 3407879 := bstep (se 1 (by rfl) ⟨2555909, by rfl⟩ : syracuseStep 3407879 = 5111819) B5111819
theorem B2271919 : Blo 2019435 2271919 := bstep (se 1 (by rfl) ⟨1703939, by rfl⟩ : syracuseStep 2271919 = 3407879) B3407879
theorem B3029225 : Blo 2019435 3029225 := bstep (se 2 (by rfl) ⟨1135959, by rfl⟩ : syracuseStep 3029225 = 2271919) B2271919
theorem B2019483 : Blo 2019435 2019483 := bstep (se 1 (by rfl) ⟨1514612, by rfl⟩ : syracuseStep 2019483 = 3029225) B3029225
theorem B3323701 : Blo 2019435 3323701 := bbase (se 5 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 3323701 = 311597) (by norm_num)
theorem B4431601 : Blo 2019435 4431601 := bstep (se 2 (by rfl) ⟨1661850, by rfl⟩ : syracuseStep 4431601 = 3323701) B3323701
theorem B5908801 : Blo 2019435 5908801 := bstep (se 2 (by rfl) ⟨2215800, by rfl⟩ : syracuseStep 5908801 = 4431601) B4431601
theorem B7878401 : Blo 2019435 7878401 := bstep (se 2 (by rfl) ⟨2954400, by rfl⟩ : syracuseStep 7878401 = 5908801) B5908801
theorem B5252267 : Blo 2019435 5252267 := bstep (se 1 (by rfl) ⟨3939200, by rfl⟩ : syracuseStep 5252267 = 7878401) B7878401
theorem B3501511 : Blo 2019435 3501511 := bstep (se 1 (by rfl) ⟨2626133, by rfl⟩ : syracuseStep 3501511 = 5252267) B5252267
theorem B18674725 : Blo 2019435 18674725 := bstep (se 4 (by rfl) ⟨1750755, by rfl⟩ : syracuseStep 18674725 = 3501511) B3501511
theorem B24899633 : Blo 2019435 24899633 := bstep (se 2 (by rfl) ⟨9337362, by rfl⟩ : syracuseStep 24899633 = 18674725) B18674725
theorem B16599755 : Blo 2019435 16599755 := bstep (se 1 (by rfl) ⟨12449816, by rfl⟩ : syracuseStep 16599755 = 24899633) B24899633
theorem B11066503 : Blo 2019435 11066503 := bstep (se 1 (by rfl) ⟨8299877, by rfl⟩ : syracuseStep 11066503 = 16599755) B16599755
theorem B14755337 : Blo 2019435 14755337 := bstep (se 2 (by rfl) ⟨5533251, by rfl⟩ : syracuseStep 14755337 = 11066503) B11066503
theorem B9836891 : Blo 2019435 9836891 := bstep (se 1 (by rfl) ⟨7377668, by rfl⟩ : syracuseStep 9836891 = 14755337) B14755337
theorem B6557927 : Blo 2019435 6557927 := bstep (se 1 (by rfl) ⟨4918445, by rfl⟩ : syracuseStep 6557927 = 9836891) B9836891
theorem B17487805 : Blo 2019435 17487805 := bstep (se 3 (by rfl) ⟨3278963, by rfl⟩ : syracuseStep 17487805 = 6557927) B6557927
theorem B23317073 : Blo 2019435 23317073 := bstep (se 2 (by rfl) ⟨8743902, by rfl⟩ : syracuseStep 23317073 = 17487805) B17487805
theorem B15544715 : Blo 2019435 15544715 := bstep (se 1 (by rfl) ⟨11658536, by rfl⟩ : syracuseStep 15544715 = 23317073) B23317073
theorem B41452573 : Blo 2019435 41452573 := bstep (se 3 (by rfl) ⟨7772357, by rfl⟩ : syracuseStep 41452573 = 15544715) B15544715
theorem B55270097 : Blo 2019435 55270097 := bstep (se 2 (by rfl) ⟨20726286, by rfl⟩ : syracuseStep 55270097 = 41452573) B41452573
theorem B36846731 : Blo 2019435 36846731 := bstep (se 1 (by rfl) ⟨27635048, by rfl⟩ : syracuseStep 36846731 = 55270097) B55270097
theorem B24564487 : Blo 2019435 24564487 := bstep (se 1 (by rfl) ⟨18423365, by rfl⟩ : syracuseStep 24564487 = 36846731) B36846731
theorem B32752649 : Blo 2019435 32752649 := bstep (se 2 (by rfl) ⟨12282243, by rfl⟩ : syracuseStep 32752649 = 24564487) B24564487
theorem B21835099 : Blo 2019435 21835099 := bstep (se 1 (by rfl) ⟨16376324, by rfl⟩ : syracuseStep 21835099 = 32752649) B32752649
theorem B29113465 : Blo 2019435 29113465 := bstep (se 2 (by rfl) ⟨10917549, by rfl⟩ : syracuseStep 29113465 = 21835099) B21835099
theorem B38817953 : Blo 2019435 38817953 := bstep (se 2 (by rfl) ⟨14556732, by rfl⟩ : syracuseStep 38817953 = 29113465) B29113465
theorem B25878635 : Blo 2019435 25878635 := bstep (se 1 (by rfl) ⟨19408976, by rfl⟩ : syracuseStep 25878635 = 38817953) B38817953
theorem B17252423 : Blo 2019435 17252423 := bstep (se 1 (by rfl) ⟨12939317, by rfl⟩ : syracuseStep 17252423 = 25878635) B25878635
theorem B11501615 : Blo 2019435 11501615 := bstep (se 1 (by rfl) ⟨8626211, by rfl⟩ : syracuseStep 11501615 = 17252423) B17252423
theorem B7667743 : Blo 2019435 7667743 := bstep (se 1 (by rfl) ⟨5750807, by rfl⟩ : syracuseStep 7667743 = 11501615) B11501615
theorem B10223657 : Blo 2019435 10223657 := bstep (se 2 (by rfl) ⟨3833871, by rfl⟩ : syracuseStep 10223657 = 7667743) B7667743
theorem B6815771 : Blo 2019435 6815771 := bstep (se 1 (by rfl) ⟨5111828, by rfl⟩ : syracuseStep 6815771 = 10223657) B10223657
theorem B4543847 : Blo 2019435 4543847 := bstep (se 1 (by rfl) ⟨3407885, by rfl⟩ : syracuseStep 4543847 = 6815771) B6815771
theorem B3029231 : Blo 2019435 3029231 := bstep (se 1 (by rfl) ⟨2271923, by rfl⟩ : syracuseStep 3029231 = 4543847) B4543847
theorem B2019487 : Blo 2019435 2019487 := bstep (se 1 (by rfl) ⟨1514615, by rfl⟩ : syracuseStep 2019487 = 3029231) B3029231
theorem B3029237 : Blo 2019435 3029237 := bbase (se 5 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 3029237 = 283991) (by norm_num)
theorem B2019491 : Blo 2019435 2019491 := bstep (se 1 (by rfl) ⟨1514618, by rfl⟩ : syracuseStep 2019491 = 3029237) B3029237
theorem B2185985 : Blo 2019435 2185985 := bbase (se 2 (by rfl) ⟨819744, by rfl⟩ : syracuseStep 2185985 = 1639489) (by norm_num)
theorem B5829293 : Blo 2019435 5829293 := bstep (se 3 (by rfl) ⟨1092992, by rfl⟩ : syracuseStep 5829293 = 2185985) B2185985
theorem B15544781 : Blo 2019435 15544781 := bstep (se 3 (by rfl) ⟨2914646, by rfl⟩ : syracuseStep 15544781 = 5829293) B5829293
theorem B10363187 : Blo 2019435 10363187 := bstep (se 1 (by rfl) ⟨7772390, by rfl⟩ : syracuseStep 10363187 = 15544781) B15544781
theorem B27635165 : Blo 2019435 27635165 := bstep (se 3 (by rfl) ⟨5181593, by rfl⟩ : syracuseStep 27635165 = 10363187) B10363187
theorem B18423443 : Blo 2019435 18423443 := bstep (se 1 (by rfl) ⟨13817582, by rfl⟩ : syracuseStep 18423443 = 27635165) B27635165
theorem B12282295 : Blo 2019435 12282295 := bstep (se 1 (by rfl) ⟨9211721, by rfl⟩ : syracuseStep 12282295 = 18423443) B18423443
theorem B16376393 : Blo 2019435 16376393 := bstep (se 2 (by rfl) ⟨6141147, by rfl⟩ : syracuseStep 16376393 = 12282295) B12282295
theorem B10917595 : Blo 2019435 10917595 := bstep (se 1 (by rfl) ⟨8188196, by rfl⟩ : syracuseStep 10917595 = 16376393) B16376393
theorem B14556793 : Blo 2019435 14556793 := bstep (se 2 (by rfl) ⟨5458797, by rfl⟩ : syracuseStep 14556793 = 10917595) B10917595
theorem B19409057 : Blo 2019435 19409057 := bstep (se 2 (by rfl) ⟨7278396, by rfl⟩ : syracuseStep 19409057 = 14556793) B14556793
theorem B12939371 : Blo 2019435 12939371 := bstep (se 1 (by rfl) ⟨9704528, by rfl⟩ : syracuseStep 12939371 = 19409057) B19409057
theorem B8626247 : Blo 2019435 8626247 := bstep (se 1 (by rfl) ⟨6469685, by rfl⟩ : syracuseStep 8626247 = 12939371) B12939371
theorem B5750831 : Blo 2019435 5750831 := bstep (se 1 (by rfl) ⟨4313123, by rfl⟩ : syracuseStep 5750831 = 8626247) B8626247
theorem B3833887 : Blo 2019435 3833887 := bstep (se 1 (by rfl) ⟨2875415, by rfl⟩ : syracuseStep 3833887 = 5750831) B5750831
theorem B5111849 : Blo 2019435 5111849 := bstep (se 2 (by rfl) ⟨1916943, by rfl⟩ : syracuseStep 5111849 = 3833887) B3833887
theorem B3407899 : Blo 2019435 3407899 := bstep (se 1 (by rfl) ⟨2555924, by rfl⟩ : syracuseStep 3407899 = 5111849) B5111849
theorem B4543865 : Blo 2019435 4543865 := bstep (se 2 (by rfl) ⟨1703949, by rfl⟩ : syracuseStep 4543865 = 3407899) B3407899
theorem B3029243 : Blo 2019435 3029243 := bstep (se 1 (by rfl) ⟨2271932, by rfl⟩ : syracuseStep 3029243 = 4543865) B4543865
theorem B2019495 : Blo 2019435 2019495 := bstep (se 1 (by rfl) ⟨1514621, by rfl⟩ : syracuseStep 2019495 = 3029243) B3029243
theorem B2271937 : Blo 2019435 2271937 := bbase (se 2 (by rfl) ⟨851976, by rfl⟩ : syracuseStep 2271937 = 1703953) (by norm_num)
theorem B3029249 : Blo 2019435 3029249 := bstep (se 2 (by rfl) ⟨1135968, by rfl⟩ : syracuseStep 3029249 = 2271937) B2271937
theorem B2019499 : Blo 2019435 2019499 := bstep (se 1 (by rfl) ⟨1514624, by rfl⟩ : syracuseStep 2019499 = 3029249) B3029249
theorem B5111869 : Blo 2019435 5111869 := bbase (se 3 (by rfl) ⟨958475, by rfl⟩ : syracuseStep 5111869 = 1916951) (by norm_num)
theorem B6815825 : Blo 2019435 6815825 := bstep (se 2 (by rfl) ⟨2555934, by rfl⟩ : syracuseStep 6815825 = 5111869) B5111869
theorem B4543883 : Blo 2019435 4543883 := bstep (se 1 (by rfl) ⟨3407912, by rfl⟩ : syracuseStep 4543883 = 6815825) B6815825
theorem B3029255 : Blo 2019435 3029255 := bstep (se 1 (by rfl) ⟨2271941, by rfl⟩ : syracuseStep 3029255 = 4543883) B4543883
theorem B2019503 : Blo 2019435 2019503 := bstep (se 1 (by rfl) ⟨1514627, by rfl⟩ : syracuseStep 2019503 = 3029255) B3029255
theorem B3029261 : Blo 2019435 3029261 := bbase (se 3 (by rfl) ⟨567986, by rfl⟩ : syracuseStep 3029261 = 1135973) (by norm_num)
theorem B2019507 : Blo 2019435 2019507 := bstep (se 1 (by rfl) ⟨1514630, by rfl⟩ : syracuseStep 2019507 = 3029261) B3029261
theorem B4543901 : Blo 2019435 4543901 := bbase (se 3 (by rfl) ⟨851981, by rfl⟩ : syracuseStep 4543901 = 1703963) (by norm_num)
theorem B3029267 : Blo 2019435 3029267 := bstep (se 1 (by rfl) ⟨2271950, by rfl⟩ : syracuseStep 3029267 = 4543901) B4543901
theorem B2019511 : Blo 2019435 2019511 := bstep (se 1 (by rfl) ⟨1514633, by rfl⟩ : syracuseStep 2019511 = 3029267) B3029267
theorem B3407933 : Blo 2019435 3407933 := bbase (se 3 (by rfl) ⟨638987, by rfl⟩ : syracuseStep 3407933 = 1277975) (by norm_num)
theorem B2271955 : Blo 2019435 2271955 := bstep (se 1 (by rfl) ⟨1703966, by rfl⟩ : syracuseStep 2271955 = 3407933) B3407933
theorem B3029273 : Blo 2019435 3029273 := bstep (se 2 (by rfl) ⟨1135977, by rfl⟩ : syracuseStep 3029273 = 2271955) B2271955
theorem B2019515 : Blo 2019435 2019515 := bstep (se 1 (by rfl) ⟨1514636, by rfl⟩ : syracuseStep 2019515 = 3029273) B3029273
theorem B2426161 : Blo 2019435 2426161 := bbase (se 2 (by rfl) ⟨909810, by rfl⟩ : syracuseStep 2426161 = 1819621) (by norm_num)
theorem B3234881 : Blo 2019435 3234881 := bstep (se 2 (by rfl) ⟨1213080, by rfl⟩ : syracuseStep 3234881 = 2426161) B2426161
theorem B2156587 : Blo 2019435 2156587 := bstep (se 1 (by rfl) ⟨1617440, by rfl⟩ : syracuseStep 2156587 = 3234881) B3234881
theorem B11501797 : Blo 2019435 11501797 := bstep (se 4 (by rfl) ⟨1078293, by rfl⟩ : syracuseStep 11501797 = 2156587) B2156587
theorem B15335729 : Blo 2019435 15335729 := bstep (se 2 (by rfl) ⟨5750898, by rfl⟩ : syracuseStep 15335729 = 11501797) B11501797
theorem B10223819 : Blo 2019435 10223819 := bstep (se 1 (by rfl) ⟨7667864, by rfl⟩ : syracuseStep 10223819 = 15335729) B15335729
theorem B6815879 : Blo 2019435 6815879 := bstep (se 1 (by rfl) ⟨5111909, by rfl⟩ : syracuseStep 6815879 = 10223819) B10223819
theorem B4543919 : Blo 2019435 4543919 := bstep (se 1 (by rfl) ⟨3407939, by rfl⟩ : syracuseStep 4543919 = 6815879) B6815879
theorem B3029279 : Blo 2019435 3029279 := bstep (se 1 (by rfl) ⟨2271959, by rfl⟩ : syracuseStep 3029279 = 4543919) B4543919
theorem B2019519 : Blo 2019435 2019519 := bstep (se 1 (by rfl) ⟨1514639, by rfl⟩ : syracuseStep 2019519 = 3029279) B3029279
theorem B3029285 : Blo 2019435 3029285 := bbase (se 4 (by rfl) ⟨283995, by rfl⟩ : syracuseStep 3029285 = 567991) (by norm_num)
theorem B2019523 : Blo 2019435 2019523 := bstep (se 1 (by rfl) ⟨1514642, by rfl⟩ : syracuseStep 2019523 = 3029285) B3029285
theorem B2555965 : Blo 2019435 2555965 := bbase (se 3 (by rfl) ⟨479243, by rfl⟩ : syracuseStep 2555965 = 958487) (by norm_num)
theorem B3407953 : Blo 2019435 3407953 := bstep (se 2 (by rfl) ⟨1277982, by rfl⟩ : syracuseStep 3407953 = 2555965) B2555965
theorem B4543937 : Blo 2019435 4543937 := bstep (se 2 (by rfl) ⟨1703976, by rfl⟩ : syracuseStep 4543937 = 3407953) B3407953
theorem B3029291 : Blo 2019435 3029291 := bstep (se 1 (by rfl) ⟨2271968, by rfl⟩ : syracuseStep 3029291 = 4543937) B4543937
theorem B2019527 : Blo 2019435 2019527 := bstep (se 1 (by rfl) ⟨1514645, by rfl⟩ : syracuseStep 2019527 = 3029291) B3029291
theorem B2271973 : Blo 2019435 2271973 := bbase (se 4 (by rfl) ⟨212997, by rfl⟩ : syracuseStep 2271973 = 425995) (by norm_num)
theorem B3029297 : Blo 2019435 3029297 := bstep (se 2 (by rfl) ⟨1135986, by rfl⟩ : syracuseStep 3029297 = 2271973) B2271973
theorem B2019531 : Blo 2019435 2019531 := bstep (se 1 (by rfl) ⟨1514648, by rfl⟩ : syracuseStep 2019531 = 3029297) B3029297
theorem B2590849 : Blo 2019435 2590849 := bbase (se 2 (by rfl) ⟨971568, by rfl⟩ : syracuseStep 2590849 = 1943137) (by norm_num)
theorem B13817861 : Blo 2019435 13817861 := bstep (se 4 (by rfl) ⟨1295424, by rfl⟩ : syracuseStep 13817861 = 2590849) B2590849
theorem B9211907 : Blo 2019435 9211907 := bstep (se 1 (by rfl) ⟨6908930, by rfl⟩ : syracuseStep 9211907 = 13817861) B13817861
theorem B6141271 : Blo 2019435 6141271 := bstep (se 1 (by rfl) ⟨4605953, by rfl⟩ : syracuseStep 6141271 = 9211907) B9211907
theorem B8188361 : Blo 2019435 8188361 := bstep (se 2 (by rfl) ⟨3070635, by rfl⟩ : syracuseStep 8188361 = 6141271) B6141271
theorem B5458907 : Blo 2019435 5458907 := bstep (se 1 (by rfl) ⟨4094180, by rfl⟩ : syracuseStep 5458907 = 8188361) B8188361
theorem B3639271 : Blo 2019435 3639271 := bstep (se 1 (by rfl) ⟨2729453, by rfl⟩ : syracuseStep 3639271 = 5458907) B5458907
theorem B4852361 : Blo 2019435 4852361 := bstep (se 2 (by rfl) ⟨1819635, by rfl⟩ : syracuseStep 4852361 = 3639271) B3639271
theorem B3234907 : Blo 2019435 3234907 := bstep (se 1 (by rfl) ⟨2426180, by rfl⟩ : syracuseStep 3234907 = 4852361) B4852361
theorem B4313209 : Blo 2019435 4313209 := bstep (se 2 (by rfl) ⟨1617453, by rfl⟩ : syracuseStep 4313209 = 3234907) B3234907
theorem B5750945 : Blo 2019435 5750945 := bstep (se 2 (by rfl) ⟨2156604, by rfl⟩ : syracuseStep 5750945 = 4313209) B4313209
theorem B3833963 : Blo 2019435 3833963 := bstep (se 1 (by rfl) ⟨2875472, by rfl⟩ : syracuseStep 3833963 = 5750945) B5750945
theorem B2555975 : Blo 2019435 2555975 := bstep (se 1 (by rfl) ⟨1916981, by rfl⟩ : syracuseStep 2555975 = 3833963) B3833963
theorem B6815933 : Blo 2019435 6815933 := bstep (se 3 (by rfl) ⟨1277987, by rfl⟩ : syracuseStep 6815933 = 2555975) B2555975
theorem B4543955 : Blo 2019435 4543955 := bstep (se 1 (by rfl) ⟨3407966, by rfl⟩ : syracuseStep 4543955 = 6815933) B6815933
theorem B3029303 : Blo 2019435 3029303 := bstep (se 1 (by rfl) ⟨2271977, by rfl⟩ : syracuseStep 3029303 = 4543955) B4543955
theorem B2019535 : Blo 2019435 2019535 := bstep (se 1 (by rfl) ⟨1514651, by rfl⟩ : syracuseStep 2019535 = 3029303) B3029303
theorem B3029309 : Blo 2019435 3029309 := bbase (se 3 (by rfl) ⟨567995, by rfl⟩ : syracuseStep 3029309 = 1135991) (by norm_num)
theorem B2019539 : Blo 2019435 2019539 := bstep (se 1 (by rfl) ⟨1514654, by rfl⟩ : syracuseStep 2019539 = 3029309) B3029309
theorem B4543973 : Blo 2019435 4543973 := bbase (se 4 (by rfl) ⟨425997, by rfl⟩ : syracuseStep 4543973 = 851995) (by norm_num)
theorem B3029315 : Blo 2019435 3029315 := bstep (se 1 (by rfl) ⟨2271986, by rfl⟩ : syracuseStep 3029315 = 4543973) B4543973
theorem B2019543 : Blo 2019435 2019543 := bstep (se 1 (by rfl) ⟨1514657, by rfl⟩ : syracuseStep 2019543 = 3029315) B3029315
theorem B5111981 : Blo 2019435 5111981 := bbase (se 3 (by rfl) ⟨958496, by rfl⟩ : syracuseStep 5111981 = 1916993) (by norm_num)
theorem B3407987 : Blo 2019435 3407987 := bstep (se 1 (by rfl) ⟨2555990, by rfl⟩ : syracuseStep 3407987 = 5111981) B5111981
theorem B2271991 : Blo 2019435 2271991 := bstep (se 1 (by rfl) ⟨1703993, by rfl⟩ : syracuseStep 2271991 = 3407987) B3407987
theorem B3029321 : Blo 2019435 3029321 := bstep (se 2 (by rfl) ⟨1135995, by rfl⟩ : syracuseStep 3029321 = 2271991) B2271991
theorem B2019547 : Blo 2019435 2019547 := bstep (se 1 (by rfl) ⟨1514660, by rfl⟩ : syracuseStep 2019547 = 3029321) B3029321
theorem B4605989 : Blo 2019435 4605989 := bbase (se 4 (by rfl) ⟨431811, by rfl⟩ : syracuseStep 4605989 = 863623) (by norm_num)
theorem B12282637 : Blo 2019435 12282637 := bstep (se 3 (by rfl) ⟨2302994, by rfl⟩ : syracuseStep 12282637 = 4605989) B4605989
theorem B16376849 : Blo 2019435 16376849 := bstep (se 2 (by rfl) ⟨6141318, by rfl⟩ : syracuseStep 16376849 = 12282637) B12282637
theorem B10917899 : Blo 2019435 10917899 := bstep (se 1 (by rfl) ⟨8188424, by rfl⟩ : syracuseStep 10917899 = 16376849) B16376849
theorem B7278599 : Blo 2019435 7278599 := bstep (se 1 (by rfl) ⟨5458949, by rfl⟩ : syracuseStep 7278599 = 10917899) B10917899
theorem B4852399 : Blo 2019435 4852399 := bstep (se 1 (by rfl) ⟨3639299, by rfl⟩ : syracuseStep 4852399 = 7278599) B7278599
theorem B6469865 : Blo 2019435 6469865 := bstep (se 2 (by rfl) ⟨2426199, by rfl⟩ : syracuseStep 6469865 = 4852399) B4852399
theorem B4313243 : Blo 2019435 4313243 := bstep (se 1 (by rfl) ⟨3234932, by rfl⟩ : syracuseStep 4313243 = 6469865) B6469865
theorem B2875495 : Blo 2019435 2875495 := bstep (se 1 (by rfl) ⟨2156621, by rfl⟩ : syracuseStep 2875495 = 4313243) B4313243
theorem B3833993 : Blo 2019435 3833993 := bstep (se 2 (by rfl) ⟨1437747, by rfl⟩ : syracuseStep 3833993 = 2875495) B2875495
theorem B10223981 : Blo 2019435 10223981 := bstep (se 3 (by rfl) ⟨1916996, by rfl⟩ : syracuseStep 10223981 = 3833993) B3833993
theorem B6815987 : Blo 2019435 6815987 := bstep (se 1 (by rfl) ⟨5111990, by rfl⟩ : syracuseStep 6815987 = 10223981) B10223981
theorem B4543991 : Blo 2019435 4543991 := bstep (se 1 (by rfl) ⟨3407993, by rfl⟩ : syracuseStep 4543991 = 6815987) B6815987
theorem B3029327 : Blo 2019435 3029327 := bstep (se 1 (by rfl) ⟨2271995, by rfl⟩ : syracuseStep 3029327 = 4543991) B4543991
theorem B2019551 : Blo 2019435 2019551 := bstep (se 1 (by rfl) ⟨1514663, by rfl⟩ : syracuseStep 2019551 = 3029327) B3029327
theorem B3029333 : Blo 2019435 3029333 := bbase (se 10 (by rfl) ⟨4437, by rfl⟩ : syracuseStep 3029333 = 8875) (by norm_num)
theorem B2019555 : Blo 2019435 2019555 := bstep (se 1 (by rfl) ⟨1514666, by rfl⟩ : syracuseStep 2019555 = 3029333) B3029333
theorem B5751013 : Blo 2019435 5751013 := bbase (se 4 (by rfl) ⟨539157, by rfl⟩ : syracuseStep 5751013 = 1078315) (by norm_num)
theorem B7668017 : Blo 2019435 7668017 := bstep (se 2 (by rfl) ⟨2875506, by rfl⟩ : syracuseStep 7668017 = 5751013) B5751013
theorem B5112011 : Blo 2019435 5112011 := bstep (se 1 (by rfl) ⟨3834008, by rfl⟩ : syracuseStep 5112011 = 7668017) B7668017
theorem B3408007 : Blo 2019435 3408007 := bstep (se 1 (by rfl) ⟨2556005, by rfl⟩ : syracuseStep 3408007 = 5112011) B5112011
theorem B4544009 : Blo 2019435 4544009 := bstep (se 2 (by rfl) ⟨1704003, by rfl⟩ : syracuseStep 4544009 = 3408007) B3408007
theorem B3029339 : Blo 2019435 3029339 := bstep (se 1 (by rfl) ⟨2272004, by rfl⟩ : syracuseStep 3029339 = 4544009) B4544009
theorem B2019559 : Blo 2019435 2019559 := bstep (se 1 (by rfl) ⟨1514669, by rfl⟩ : syracuseStep 2019559 = 3029339) B3029339
theorem B2272009 : Blo 2019435 2272009 := bbase (se 2 (by rfl) ⟨852003, by rfl⟩ : syracuseStep 2272009 = 1704007) (by norm_num)
theorem B3029345 : Blo 2019435 3029345 := bstep (se 2 (by rfl) ⟨1136004, by rfl⟩ : syracuseStep 3029345 = 2272009) B2272009
theorem B2019563 : Blo 2019435 2019563 := bstep (se 1 (by rfl) ⟨1514672, by rfl⟩ : syracuseStep 2019563 = 3029345) B3029345
theorem B15545333 : Blo 2019435 15545333 := bbase (se 5 (by rfl) ⟨728687, by rfl⟩ : syracuseStep 15545333 = 1457375) (by norm_num)
theorem B10363555 : Blo 2019435 10363555 := bstep (se 1 (by rfl) ⟨7772666, by rfl⟩ : syracuseStep 10363555 = 15545333) B15545333
theorem B55272293 : Blo 2019435 55272293 := bstep (se 4 (by rfl) ⟨5181777, by rfl⟩ : syracuseStep 55272293 = 10363555) B10363555
theorem B36848195 : Blo 2019435 36848195 := bstep (se 1 (by rfl) ⟨27636146, by rfl⟩ : syracuseStep 36848195 = 55272293) B55272293
theorem B24565463 : Blo 2019435 24565463 := bstep (se 1 (by rfl) ⟨18424097, by rfl⟩ : syracuseStep 24565463 = 36848195) B36848195
theorem B16376975 : Blo 2019435 16376975 := bstep (se 1 (by rfl) ⟨12282731, by rfl⟩ : syracuseStep 16376975 = 24565463) B24565463
theorem B10917983 : Blo 2019435 10917983 := bstep (se 1 (by rfl) ⟨8188487, by rfl⟩ : syracuseStep 10917983 = 16376975) B16376975
theorem B7278655 : Blo 2019435 7278655 := bstep (se 1 (by rfl) ⟨5458991, by rfl⟩ : syracuseStep 7278655 = 10917983) B10917983
theorem B9704873 : Blo 2019435 9704873 := bstep (se 2 (by rfl) ⟨3639327, by rfl⟩ : syracuseStep 9704873 = 7278655) B7278655
theorem B25879661 : Blo 2019435 25879661 := bstep (se 3 (by rfl) ⟨4852436, by rfl⟩ : syracuseStep 25879661 = 9704873) B9704873
theorem B17253107 : Blo 2019435 17253107 := bstep (se 1 (by rfl) ⟨12939830, by rfl⟩ : syracuseStep 17253107 = 25879661) B25879661
theorem B11502071 : Blo 2019435 11502071 := bstep (se 1 (by rfl) ⟨8626553, by rfl⟩ : syracuseStep 11502071 = 17253107) B17253107
theorem B7668047 : Blo 2019435 7668047 := bstep (se 1 (by rfl) ⟨5751035, by rfl⟩ : syracuseStep 7668047 = 11502071) B11502071
theorem B5112031 : Blo 2019435 5112031 := bstep (se 1 (by rfl) ⟨3834023, by rfl⟩ : syracuseStep 5112031 = 7668047) B7668047
theorem B6816041 : Blo 2019435 6816041 := bstep (se 2 (by rfl) ⟨2556015, by rfl⟩ : syracuseStep 6816041 = 5112031) B5112031
theorem B4544027 : Blo 2019435 4544027 := bstep (se 1 (by rfl) ⟨3408020, by rfl⟩ : syracuseStep 4544027 = 6816041) B6816041
theorem B3029351 : Blo 2019435 3029351 := bstep (se 1 (by rfl) ⟨2272013, by rfl⟩ : syracuseStep 3029351 = 4544027) B4544027
theorem B2019567 : Blo 2019435 2019567 := bstep (se 1 (by rfl) ⟨1514675, by rfl⟩ : syracuseStep 2019567 = 3029351) B3029351
theorem B3029357 : Blo 2019435 3029357 := bbase (se 3 (by rfl) ⟨568004, by rfl⟩ : syracuseStep 3029357 = 1136009) (by norm_num)
theorem B2019571 : Blo 2019435 2019571 := bstep (se 1 (by rfl) ⟨1514678, by rfl⟩ : syracuseStep 2019571 = 3029357) B3029357
theorem B4544045 : Blo 2019435 4544045 := bbase (se 3 (by rfl) ⟨852008, by rfl⟩ : syracuseStep 4544045 = 1704017) (by norm_num)
theorem B3029363 : Blo 2019435 3029363 := bstep (se 1 (by rfl) ⟨2272022, by rfl⟩ : syracuseStep 3029363 = 4544045) B4544045
theorem B2019575 : Blo 2019435 2019575 := bstep (se 1 (by rfl) ⟨1514681, by rfl⟩ : syracuseStep 2019575 = 3029363) B3029363
theorem B4094269 : Blo 2019435 4094269 := bbase (se 3 (by rfl) ⟨767675, by rfl⟩ : syracuseStep 4094269 = 1535351) (by norm_num)
theorem B21836101 : Blo 2019435 21836101 := bstep (se 4 (by rfl) ⟨2047134, by rfl⟩ : syracuseStep 21836101 = 4094269) B4094269
theorem B29114801 : Blo 2019435 29114801 := bstep (se 2 (by rfl) ⟨10918050, by rfl⟩ : syracuseStep 29114801 = 21836101) B21836101
theorem B19409867 : Blo 2019435 19409867 := bstep (se 1 (by rfl) ⟨14557400, by rfl⟩ : syracuseStep 19409867 = 29114801) B29114801
theorem B12939911 : Blo 2019435 12939911 := bstep (se 1 (by rfl) ⟨9704933, by rfl⟩ : syracuseStep 12939911 = 19409867) B19409867
theorem B8626607 : Blo 2019435 8626607 := bstep (se 1 (by rfl) ⟨6469955, by rfl⟩ : syracuseStep 8626607 = 12939911) B12939911
theorem B5751071 : Blo 2019435 5751071 := bstep (se 1 (by rfl) ⟨4313303, by rfl⟩ : syracuseStep 5751071 = 8626607) B8626607
theorem B3834047 : Blo 2019435 3834047 := bstep (se 1 (by rfl) ⟨2875535, by rfl⟩ : syracuseStep 3834047 = 5751071) B5751071
theorem B2556031 : Blo 2019435 2556031 := bstep (se 1 (by rfl) ⟨1917023, by rfl⟩ : syracuseStep 2556031 = 3834047) B3834047
theorem B3408041 : Blo 2019435 3408041 := bstep (se 2 (by rfl) ⟨1278015, by rfl⟩ : syracuseStep 3408041 = 2556031) B2556031
theorem B2272027 : Blo 2019435 2272027 := bstep (se 1 (by rfl) ⟨1704020, by rfl⟩ : syracuseStep 2272027 = 3408041) B3408041
theorem B3029369 : Blo 2019435 3029369 := bstep (se 2 (by rfl) ⟨1136013, by rfl⟩ : syracuseStep 3029369 = 2272027) B2272027
theorem B2019579 : Blo 2019435 2019579 := bstep (se 1 (by rfl) ⟨1514684, by rfl⟩ : syracuseStep 2019579 = 3029369) B3029369
theorem B2075069 : Blo 2019435 2075069 := bbase (se 3 (by rfl) ⟨389075, by rfl⟩ : syracuseStep 2075069 = 778151) (by norm_num)
theorem B5533517 : Blo 2019435 5533517 := bstep (se 3 (by rfl) ⟨1037534, by rfl⟩ : syracuseStep 5533517 = 2075069) B2075069
theorem B3689011 : Blo 2019435 3689011 := bstep (se 1 (by rfl) ⟨2766758, by rfl⟩ : syracuseStep 3689011 = 5533517) B5533517
theorem B4918681 : Blo 2019435 4918681 := bstep (se 2 (by rfl) ⟨1844505, by rfl⟩ : syracuseStep 4918681 = 3689011) B3689011
theorem B6558241 : Blo 2019435 6558241 := bstep (se 2 (by rfl) ⟨2459340, by rfl⟩ : syracuseStep 6558241 = 4918681) B4918681
theorem B8744321 : Blo 2019435 8744321 := bstep (se 2 (by rfl) ⟨3279120, by rfl⟩ : syracuseStep 8744321 = 6558241) B6558241
theorem B23318189 : Blo 2019435 23318189 := bstep (se 3 (by rfl) ⟨4372160, by rfl⟩ : syracuseStep 23318189 = 8744321) B8744321
theorem B15545459 : Blo 2019435 15545459 := bstep (se 1 (by rfl) ⟨11659094, by rfl⟩ : syracuseStep 15545459 = 23318189) B23318189
theorem B10363639 : Blo 2019435 10363639 := bstep (se 1 (by rfl) ⟨7772729, by rfl⟩ : syracuseStep 10363639 = 15545459) B15545459
theorem B13818185 : Blo 2019435 13818185 := bstep (se 2 (by rfl) ⟨5181819, by rfl⟩ : syracuseStep 13818185 = 10363639) B10363639
theorem B9212123 : Blo 2019435 9212123 := bstep (se 1 (by rfl) ⟨6909092, by rfl⟩ : syracuseStep 9212123 = 13818185) B13818185
theorem B6141415 : Blo 2019435 6141415 := bstep (se 1 (by rfl) ⟨4606061, by rfl⟩ : syracuseStep 6141415 = 9212123) B9212123
theorem B8188553 : Blo 2019435 8188553 := bstep (se 2 (by rfl) ⟨3070707, by rfl⟩ : syracuseStep 8188553 = 6141415) B6141415
theorem B5459035 : Blo 2019435 5459035 := bstep (se 1 (by rfl) ⟨4094276, by rfl⟩ : syracuseStep 5459035 = 8188553) B8188553
theorem B7278713 : Blo 2019435 7278713 := bstep (se 2 (by rfl) ⟨2729517, by rfl⟩ : syracuseStep 7278713 = 5459035) B5459035
theorem B4852475 : Blo 2019435 4852475 := bstep (se 1 (by rfl) ⟨3639356, by rfl⟩ : syracuseStep 4852475 = 7278713) B7278713
theorem B3234983 : Blo 2019435 3234983 := bstep (se 1 (by rfl) ⟨2426237, by rfl⟩ : syracuseStep 3234983 = 4852475) B4852475
theorem B34506485 : Blo 2019435 34506485 := bstep (se 5 (by rfl) ⟨1617491, by rfl⟩ : syracuseStep 34506485 = 3234983) B3234983
theorem B23004323 : Blo 2019435 23004323 := bstep (se 1 (by rfl) ⟨17253242, by rfl⟩ : syracuseStep 23004323 = 34506485) B34506485
theorem B15336215 : Blo 2019435 15336215 := bstep (se 1 (by rfl) ⟨11502161, by rfl⟩ : syracuseStep 15336215 = 23004323) B23004323
theorem B10224143 : Blo 2019435 10224143 := bstep (se 1 (by rfl) ⟨7668107, by rfl⟩ : syracuseStep 10224143 = 15336215) B15336215
theorem B6816095 : Blo 2019435 6816095 := bstep (se 1 (by rfl) ⟨5112071, by rfl⟩ : syracuseStep 6816095 = 10224143) B10224143
theorem B4544063 : Blo 2019435 4544063 := bstep (se 1 (by rfl) ⟨3408047, by rfl⟩ : syracuseStep 4544063 = 6816095) B6816095
theorem B3029375 : Blo 2019435 3029375 := bstep (se 1 (by rfl) ⟨2272031, by rfl⟩ : syracuseStep 3029375 = 4544063) B4544063
theorem B2019583 : Blo 2019435 2019583 := bstep (se 1 (by rfl) ⟨1514687, by rfl⟩ : syracuseStep 2019583 = 3029375) B3029375
theorem B3029381 : Blo 2019435 3029381 := bbase (se 4 (by rfl) ⟨284004, by rfl⟩ : syracuseStep 3029381 = 568009) (by norm_num)
theorem B2019587 : Blo 2019435 2019587 := bstep (se 1 (by rfl) ⟨1514690, by rfl⟩ : syracuseStep 2019587 = 3029381) B3029381
theorem B3408061 : Blo 2019435 3408061 := bbase (se 3 (by rfl) ⟨639011, by rfl⟩ : syracuseStep 3408061 = 1278023) (by norm_num)
theorem B4544081 : Blo 2019435 4544081 := bstep (se 2 (by rfl) ⟨1704030, by rfl⟩ : syracuseStep 4544081 = 3408061) B3408061
theorem B3029387 : Blo 2019435 3029387 := bstep (se 1 (by rfl) ⟨2272040, by rfl⟩ : syracuseStep 3029387 = 4544081) B4544081
theorem B2019591 : Blo 2019435 2019591 := bstep (se 1 (by rfl) ⟨1514693, by rfl⟩ : syracuseStep 2019591 = 3029387) B3029387
theorem B2272045 : Blo 2019435 2272045 := bbase (se 3 (by rfl) ⟨426008, by rfl⟩ : syracuseStep 2272045 = 852017) (by norm_num)
theorem B3029393 : Blo 2019435 3029393 := bstep (se 2 (by rfl) ⟨1136022, by rfl⟩ : syracuseStep 3029393 = 2272045) B2272045
theorem B2019595 : Blo 2019435 2019595 := bstep (se 1 (by rfl) ⟨1514696, by rfl⟩ : syracuseStep 2019595 = 3029393) B3029393
theorem B6816149 : Blo 2019435 6816149 := bbase (se 6 (by rfl) ⟨159753, by rfl⟩ : syracuseStep 6816149 = 319507) (by norm_num)
theorem B4544099 : Blo 2019435 4544099 := bstep (se 1 (by rfl) ⟨3408074, by rfl⟩ : syracuseStep 4544099 = 6816149) B6816149
theorem B3029399 : Blo 2019435 3029399 := bstep (se 1 (by rfl) ⟨2272049, by rfl⟩ : syracuseStep 3029399 = 4544099) B4544099
theorem B2019599 : Blo 2019435 2019599 := bstep (se 1 (by rfl) ⟨1514699, by rfl⟩ : syracuseStep 2019599 = 3029399) B3029399
theorem B3029405 : Blo 2019435 3029405 := bbase (se 3 (by rfl) ⟨568013, by rfl⟩ : syracuseStep 3029405 = 1136027) (by norm_num)
theorem B2019603 : Blo 2019435 2019603 := bstep (se 1 (by rfl) ⟨1514702, by rfl⟩ : syracuseStep 2019603 = 3029405) B3029405
theorem B4544117 : Blo 2019435 4544117 := bbase (se 5 (by rfl) ⟨213005, by rfl⟩ : syracuseStep 4544117 = 426011) (by norm_num)
theorem B3029411 : Blo 2019435 3029411 := bstep (se 1 (by rfl) ⟨2272058, by rfl⟩ : syracuseStep 3029411 = 4544117) B4544117
theorem B2019607 : Blo 2019435 2019607 := bstep (se 1 (by rfl) ⟨1514705, by rfl⟩ : syracuseStep 2019607 = 3029411) B3029411
theorem B17488885 : Blo 2019435 17488885 := bbase (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) (by norm_num)
theorem B23318513 : Blo 2019435 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B15545675 : Blo 2019435 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B10363783 : Blo 2019435 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B13818377 : Blo 2019435 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B36849005 : Blo 2019435 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B24566003 : Blo 2019435 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B16377335 : Blo 2019435 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B10918223 : Blo 2019435 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B7278815 : Blo 2019435 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B4852543 : Blo 2019435 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B6470057 : Blo 2019435 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B17253485 : Blo 2019435 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B11502323 : Blo 2019435 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B7668215 : Blo 2019435 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B5112143 : Blo 2019435 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B3408095 : Blo 2019435 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B2272063 : Blo 2019435 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B3029417 : Blo 2019435 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B2019611 : Blo 2019435 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B7668229 : Blo 2019435 7668229 := bbase (se 4 (by rfl) ⟨718896, by rfl⟩ : syracuseStep 7668229 = 1437793) (by norm_num)
theorem B10224305 : Blo 2019435 10224305 := bstep (se 2 (by rfl) ⟨3834114, by rfl⟩ : syracuseStep 10224305 = 7668229) B7668229
theorem B6816203 : Blo 2019435 6816203 := bstep (se 1 (by rfl) ⟨5112152, by rfl⟩ : syracuseStep 6816203 = 10224305) B10224305
theorem B4544135 : Blo 2019435 4544135 := bstep (se 1 (by rfl) ⟨3408101, by rfl⟩ : syracuseStep 4544135 = 6816203) B6816203
theorem B3029423 : Blo 2019435 3029423 := bstep (se 1 (by rfl) ⟨2272067, by rfl⟩ : syracuseStep 3029423 = 4544135) B4544135
theorem B2019615 : Blo 2019435 2019615 := bstep (se 1 (by rfl) ⟨1514711, by rfl⟩ : syracuseStep 2019615 = 3029423) B3029423
theorem B3029429 : Blo 2019435 3029429 := bbase (se 5 (by rfl) ⟨142004, by rfl⟩ : syracuseStep 3029429 = 284009) (by norm_num)
theorem B2019619 : Blo 2019435 2019619 := bstep (se 1 (by rfl) ⟨1514714, by rfl⟩ : syracuseStep 2019619 = 3029429) B3029429
theorem B5112173 : Blo 2019435 5112173 := bbase (se 3 (by rfl) ⟨958532, by rfl⟩ : syracuseStep 5112173 = 1917065) (by norm_num)
theorem B3408115 : Blo 2019435 3408115 := bstep (se 1 (by rfl) ⟨2556086, by rfl⟩ : syracuseStep 3408115 = 5112173) B5112173
theorem B4544153 : Blo 2019435 4544153 := bstep (se 2 (by rfl) ⟨1704057, by rfl⟩ : syracuseStep 4544153 = 3408115) B3408115
theorem B3029435 : Blo 2019435 3029435 := bstep (se 1 (by rfl) ⟨2272076, by rfl⟩ : syracuseStep 3029435 = 4544153) B4544153
theorem B2019623 : Blo 2019435 2019623 := bstep (se 1 (by rfl) ⟨1514717, by rfl⟩ : syracuseStep 2019623 = 3029435) B3029435
theorem B2272081 : Blo 2019435 2272081 := bbase (se 2 (by rfl) ⟨852030, by rfl⟩ : syracuseStep 2272081 = 1704061) (by norm_num)
theorem B3029441 : Blo 2019435 3029441 := bstep (se 2 (by rfl) ⟨1136040, by rfl⟩ : syracuseStep 3029441 = 2272081) B2272081
theorem B2019627 : Blo 2019435 2019627 := bstep (se 1 (by rfl) ⟨1514720, by rfl⟩ : syracuseStep 2019627 = 3029441) B3029441
theorem B3235061 : Blo 2019435 3235061 := bbase (se 5 (by rfl) ⟨151643, by rfl⟩ : syracuseStep 3235061 = 303287) (by norm_num)
theorem B2156707 : Blo 2019435 2156707 := bstep (se 1 (by rfl) ⟨1617530, by rfl⟩ : syracuseStep 2156707 = 3235061) B3235061
theorem B2875609 : Blo 2019435 2875609 := bstep (se 2 (by rfl) ⟨1078353, by rfl⟩ : syracuseStep 2875609 = 2156707) B2156707
theorem B3834145 : Blo 2019435 3834145 := bstep (se 2 (by rfl) ⟨1437804, by rfl⟩ : syracuseStep 3834145 = 2875609) B2875609
theorem B5112193 : Blo 2019435 5112193 := bstep (se 2 (by rfl) ⟨1917072, by rfl⟩ : syracuseStep 5112193 = 3834145) B3834145
theorem B6816257 : Blo 2019435 6816257 := bstep (se 2 (by rfl) ⟨2556096, by rfl⟩ : syracuseStep 6816257 = 5112193) B5112193
theorem B4544171 : Blo 2019435 4544171 := bstep (se 1 (by rfl) ⟨3408128, by rfl⟩ : syracuseStep 4544171 = 6816257) B6816257
theorem B3029447 : Blo 2019435 3029447 := bstep (se 1 (by rfl) ⟨2272085, by rfl⟩ : syracuseStep 3029447 = 4544171) B4544171
theorem B2019631 : Blo 2019435 2019631 := bstep (se 1 (by rfl) ⟨1514723, by rfl⟩ : syracuseStep 2019631 = 3029447) B3029447
theorem B3029453 : Blo 2019435 3029453 := bbase (se 3 (by rfl) ⟨568022, by rfl⟩ : syracuseStep 3029453 = 1136045) (by norm_num)
theorem B2019635 : Blo 2019435 2019635 := bstep (se 1 (by rfl) ⟨1514726, by rfl⟩ : syracuseStep 2019635 = 3029453) B3029453
theorem B4544189 : Blo 2019435 4544189 := bbase (se 3 (by rfl) ⟨852035, by rfl⟩ : syracuseStep 4544189 = 1704071) (by norm_num)
theorem B3029459 : Blo 2019435 3029459 := bstep (se 1 (by rfl) ⟨2272094, by rfl⟩ : syracuseStep 3029459 = 4544189) B4544189
theorem B2019639 : Blo 2019435 2019639 := bstep (se 1 (by rfl) ⟨1514729, by rfl⟩ : syracuseStep 2019639 = 3029459) B3029459
theorem B3408149 : Blo 2019435 3408149 := bbase (se 6 (by rfl) ⟨79878, by rfl⟩ : syracuseStep 3408149 = 159757) (by norm_num)
theorem B2272099 : Blo 2019435 2272099 := bstep (se 1 (by rfl) ⟨1704074, by rfl⟩ : syracuseStep 2272099 = 3408149) B3408149
theorem B3029465 : Blo 2019435 3029465 := bstep (se 2 (by rfl) ⟨1136049, by rfl⟩ : syracuseStep 3029465 = 2272099) B2272099
theorem B2019643 : Blo 2019435 2019643 := bstep (se 1 (by rfl) ⟨1514732, by rfl⟩ : syracuseStep 2019643 = 3029465) B3029465
theorem B3323965 : Blo 2019435 3323965 := bbase (se 3 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 3323965 = 1246487) (by norm_num)
theorem B4431953 : Blo 2019435 4431953 := bstep (se 2 (by rfl) ⟨1661982, by rfl⟩ : syracuseStep 4431953 = 3323965) B3323965
theorem B11818541 : Blo 2019435 11818541 := bstep (se 3 (by rfl) ⟨2215976, by rfl⟩ : syracuseStep 11818541 = 4431953) B4431953
theorem B7879027 : Blo 2019435 7879027 := bstep (se 1 (by rfl) ⟨5909270, by rfl⟩ : syracuseStep 7879027 = 11818541) B11818541
theorem B10505369 : Blo 2019435 10505369 := bstep (se 2 (by rfl) ⟨3939513, by rfl⟩ : syracuseStep 10505369 = 7879027) B7879027
theorem B7003579 : Blo 2019435 7003579 := bstep (se 1 (by rfl) ⟨5252684, by rfl⟩ : syracuseStep 7003579 = 10505369) B10505369
theorem B9338105 : Blo 2019435 9338105 := bstep (se 2 (by rfl) ⟨3501789, by rfl⟩ : syracuseStep 9338105 = 7003579) B7003579
theorem B6225403 : Blo 2019435 6225403 := bstep (se 1 (by rfl) ⟨4669052, by rfl⟩ : syracuseStep 6225403 = 9338105) B9338105
theorem B8300537 : Blo 2019435 8300537 := bstep (se 2 (by rfl) ⟨3112701, by rfl⟩ : syracuseStep 8300537 = 6225403) B6225403
theorem B5533691 : Blo 2019435 5533691 := bstep (se 1 (by rfl) ⟨4150268, by rfl⟩ : syracuseStep 5533691 = 8300537) B8300537
theorem B14756509 : Blo 2019435 14756509 := bstep (se 3 (by rfl) ⟨2766845, by rfl⟩ : syracuseStep 14756509 = 5533691) B5533691
theorem B19675345 : Blo 2019435 19675345 := bstep (se 2 (by rfl) ⟨7378254, by rfl⟩ : syracuseStep 19675345 = 14756509) B14756509
theorem B26233793 : Blo 2019435 26233793 := bstep (se 2 (by rfl) ⟨9837672, by rfl⟩ : syracuseStep 26233793 = 19675345) B19675345
theorem B17489195 : Blo 2019435 17489195 := bstep (se 1 (by rfl) ⟨13116896, by rfl⟩ : syracuseStep 17489195 = 26233793) B26233793
theorem B11659463 : Blo 2019435 11659463 := bstep (se 1 (by rfl) ⟨8744597, by rfl⟩ : syracuseStep 11659463 = 17489195) B17489195
theorem B7772975 : Blo 2019435 7772975 := bstep (se 1 (by rfl) ⟨5829731, by rfl⟩ : syracuseStep 7772975 = 11659463) B11659463
theorem B5181983 : Blo 2019435 5181983 := bstep (se 1 (by rfl) ⟨3886487, by rfl⟩ : syracuseStep 5181983 = 7772975) B7772975
theorem B3454655 : Blo 2019435 3454655 := bstep (se 1 (by rfl) ⟨2590991, by rfl⟩ : syracuseStep 3454655 = 5181983) B5181983
theorem B36849653 : Blo 2019435 36849653 := bstep (se 5 (by rfl) ⟨1727327, by rfl⟩ : syracuseStep 36849653 = 3454655) B3454655
theorem B24566435 : Blo 2019435 24566435 := bstep (se 1 (by rfl) ⟨18424826, by rfl⟩ : syracuseStep 24566435 = 36849653) B36849653
theorem B16377623 : Blo 2019435 16377623 := bstep (se 1 (by rfl) ⟨12283217, by rfl⟩ : syracuseStep 16377623 = 24566435) B24566435
theorem B10918415 : Blo 2019435 10918415 := bstep (se 1 (by rfl) ⟨8188811, by rfl⟩ : syracuseStep 10918415 = 16377623) B16377623
theorem B29115773 : Blo 2019435 29115773 := bstep (se 3 (by rfl) ⟨5459207, by rfl⟩ : syracuseStep 29115773 = 10918415) B10918415
theorem B19410515 : Blo 2019435 19410515 := bstep (se 1 (by rfl) ⟨14557886, by rfl⟩ : syracuseStep 19410515 = 29115773) B29115773
theorem B12940343 : Blo 2019435 12940343 := bstep (se 1 (by rfl) ⟨9705257, by rfl⟩ : syracuseStep 12940343 = 19410515) B19410515
theorem B8626895 : Blo 2019435 8626895 := bstep (se 1 (by rfl) ⟨6470171, by rfl⟩ : syracuseStep 8626895 = 12940343) B12940343
theorem B5751263 : Blo 2019435 5751263 := bstep (se 1 (by rfl) ⟨4313447, by rfl⟩ : syracuseStep 5751263 = 8626895) B8626895
theorem B15336701 : Blo 2019435 15336701 := bstep (se 3 (by rfl) ⟨2875631, by rfl⟩ : syracuseStep 15336701 = 5751263) B5751263
theorem B10224467 : Blo 2019435 10224467 := bstep (se 1 (by rfl) ⟨7668350, by rfl⟩ : syracuseStep 10224467 = 15336701) B15336701
theorem B6816311 : Blo 2019435 6816311 := bstep (se 1 (by rfl) ⟨5112233, by rfl⟩ : syracuseStep 6816311 = 10224467) B10224467
theorem B4544207 : Blo 2019435 4544207 := bstep (se 1 (by rfl) ⟨3408155, by rfl⟩ : syracuseStep 4544207 = 6816311) B6816311
theorem B3029471 : Blo 2019435 3029471 := bstep (se 1 (by rfl) ⟨2272103, by rfl⟩ : syracuseStep 3029471 = 4544207) B4544207
theorem B2019647 : Blo 2019435 2019647 := bstep (se 1 (by rfl) ⟨1514735, by rfl⟩ : syracuseStep 2019647 = 3029471) B3029471
theorem B3029477 : Blo 2019435 3029477 := bbase (se 4 (by rfl) ⟨284013, by rfl⟩ : syracuseStep 3029477 = 568027) (by norm_num)
theorem B2019651 : Blo 2019435 2019651 := bstep (se 1 (by rfl) ⟨1514738, by rfl⟩ : syracuseStep 2019651 = 3029477) B3029477
theorem B20728021 : Blo 2019435 20728021 := bbase (se 7 (by rfl) ⟨242906, by rfl⟩ : syracuseStep 20728021 = 485813) (by norm_num)
theorem B27637361 : Blo 2019435 27637361 := bstep (se 2 (by rfl) ⟨10364010, by rfl⟩ : syracuseStep 27637361 = 20728021) B20728021
theorem B18424907 : Blo 2019435 18424907 := bstep (se 1 (by rfl) ⟨13818680, by rfl⟩ : syracuseStep 18424907 = 27637361) B27637361
theorem B12283271 : Blo 2019435 12283271 := bstep (se 1 (by rfl) ⟨9212453, by rfl⟩ : syracuseStep 12283271 = 18424907) B18424907
theorem B8188847 : Blo 2019435 8188847 := bstep (se 1 (by rfl) ⟨6141635, by rfl⟩ : syracuseStep 8188847 = 12283271) B12283271
theorem B5459231 : Blo 2019435 5459231 := bstep (se 1 (by rfl) ⟨4094423, by rfl⟩ : syracuseStep 5459231 = 8188847) B8188847
theorem B3639487 : Blo 2019435 3639487 := bstep (se 1 (by rfl) ⟨2729615, by rfl⟩ : syracuseStep 3639487 = 5459231) B5459231
theorem B4852649 : Blo 2019435 4852649 := bstep (se 2 (by rfl) ⟨1819743, by rfl⟩ : syracuseStep 4852649 = 3639487) B3639487
theorem B12940397 : Blo 2019435 12940397 := bstep (se 3 (by rfl) ⟨2426324, by rfl⟩ : syracuseStep 12940397 = 4852649) B4852649
theorem B8626931 : Blo 2019435 8626931 := bstep (se 1 (by rfl) ⟨6470198, by rfl⟩ : syracuseStep 8626931 = 12940397) B12940397
theorem B5751287 : Blo 2019435 5751287 := bstep (se 1 (by rfl) ⟨4313465, by rfl⟩ : syracuseStep 5751287 = 8626931) B8626931
theorem B3834191 : Blo 2019435 3834191 := bstep (se 1 (by rfl) ⟨2875643, by rfl⟩ : syracuseStep 3834191 = 5751287) B5751287
theorem B2556127 : Blo 2019435 2556127 := bstep (se 1 (by rfl) ⟨1917095, by rfl⟩ : syracuseStep 2556127 = 3834191) B3834191
theorem B3408169 : Blo 2019435 3408169 := bstep (se 2 (by rfl) ⟨1278063, by rfl⟩ : syracuseStep 3408169 = 2556127) B2556127
theorem B4544225 : Blo 2019435 4544225 := bstep (se 2 (by rfl) ⟨1704084, by rfl⟩ : syracuseStep 4544225 = 3408169) B3408169
theorem B3029483 : Blo 2019435 3029483 := bstep (se 1 (by rfl) ⟨2272112, by rfl⟩ : syracuseStep 3029483 = 4544225) B4544225
theorem B2019655 : Blo 2019435 2019655 := bstep (se 1 (by rfl) ⟨1514741, by rfl⟩ : syracuseStep 2019655 = 3029483) B3029483
theorem B2272117 : Blo 2019435 2272117 := bbase (se 5 (by rfl) ⟨106505, by rfl⟩ : syracuseStep 2272117 = 213011) (by norm_num)
theorem B3029489 : Blo 2019435 3029489 := bstep (se 2 (by rfl) ⟨1136058, by rfl⟩ : syracuseStep 3029489 = 2272117) B2272117
theorem B2019659 : Blo 2019435 2019659 := bstep (se 1 (by rfl) ⟨1514744, by rfl⟩ : syracuseStep 2019659 = 3029489) B3029489
theorem B2556137 : Blo 2019435 2556137 := bbase (se 2 (by rfl) ⟨958551, by rfl⟩ : syracuseStep 2556137 = 1917103) (by norm_num)
theorem B6816365 : Blo 2019435 6816365 := bstep (se 3 (by rfl) ⟨1278068, by rfl⟩ : syracuseStep 6816365 = 2556137) B2556137
theorem B4544243 : Blo 2019435 4544243 := bstep (se 1 (by rfl) ⟨3408182, by rfl⟩ : syracuseStep 4544243 = 6816365) B6816365
theorem B3029495 : Blo 2019435 3029495 := bstep (se 1 (by rfl) ⟨2272121, by rfl⟩ : syracuseStep 3029495 = 4544243) B4544243
theorem B2019663 : Blo 2019435 2019663 := bstep (se 1 (by rfl) ⟨1514747, by rfl⟩ : syracuseStep 2019663 = 3029495) B3029495
theorem B3029501 : Blo 2019435 3029501 := bbase (se 3 (by rfl) ⟨568031, by rfl⟩ : syracuseStep 3029501 = 1136063) (by norm_num)
theorem B2019667 : Blo 2019435 2019667 := bstep (se 1 (by rfl) ⟨1514750, by rfl⟩ : syracuseStep 2019667 = 3029501) B3029501
theorem B4544261 : Blo 2019435 4544261 := bbase (se 4 (by rfl) ⟨426024, by rfl⟩ : syracuseStep 4544261 = 852049) (by norm_num)
theorem B3029507 : Blo 2019435 3029507 := bstep (se 1 (by rfl) ⟨2272130, by rfl⟩ : syracuseStep 3029507 = 4544261) B4544261
theorem B2019671 : Blo 2019435 2019671 := bstep (se 1 (by rfl) ⟨1514753, by rfl⟩ : syracuseStep 2019671 = 3029507) B3029507
theorem B3834229 : Blo 2019435 3834229 := bbase (se 5 (by rfl) ⟨179729, by rfl⟩ : syracuseStep 3834229 = 359459) (by norm_num)
theorem B5112305 : Blo 2019435 5112305 := bstep (se 2 (by rfl) ⟨1917114, by rfl⟩ : syracuseStep 5112305 = 3834229) B3834229
theorem B3408203 : Blo 2019435 3408203 := bstep (se 1 (by rfl) ⟨2556152, by rfl⟩ : syracuseStep 3408203 = 5112305) B5112305
theorem B2272135 : Blo 2019435 2272135 := bstep (se 1 (by rfl) ⟨1704101, by rfl⟩ : syracuseStep 2272135 = 3408203) B3408203
theorem B3029513 : Blo 2019435 3029513 := bstep (se 2 (by rfl) ⟨1136067, by rfl⟩ : syracuseStep 3029513 = 2272135) B2272135
theorem B2019675 : Blo 2019435 2019675 := bstep (se 1 (by rfl) ⟨1514756, by rfl⟩ : syracuseStep 2019675 = 3029513) B3029513
theorem B10224629 : Blo 2019435 10224629 := bbase (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) (by norm_num)
theorem B6816419 : Blo 2019435 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B4544279 : Blo 2019435 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B3029519 : Blo 2019435 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B2019679 : Blo 2019435 2019679 := bstep (se 1 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 2019679 = 3029519) B3029519
theorem B3029525 : Blo 2019435 3029525 := bbase (se 6 (by rfl) ⟨71004, by rfl⟩ : syracuseStep 3029525 = 142009) (by norm_num)
theorem B2019683 : Blo 2019435 2019683 := bstep (se 1 (by rfl) ⟨1514762, by rfl⟩ : syracuseStep 2019683 = 3029525) B3029525
theorem B17254133 : Blo 2019435 17254133 := bbase (se 5 (by rfl) ⟨808787, by rfl⟩ : syracuseStep 17254133 = 1617575) (by norm_num)
theorem B11502755 : Blo 2019435 11502755 := bstep (se 1 (by rfl) ⟨8627066, by rfl⟩ : syracuseStep 11502755 = 17254133) B17254133
theorem B7668503 : Blo 2019435 7668503 := bstep (se 1 (by rfl) ⟨5751377, by rfl⟩ : syracuseStep 7668503 = 11502755) B11502755
theorem B5112335 : Blo 2019435 5112335 := bstep (se 1 (by rfl) ⟨3834251, by rfl⟩ : syracuseStep 5112335 = 7668503) B7668503
theorem B3408223 : Blo 2019435 3408223 := bstep (se 1 (by rfl) ⟨2556167, by rfl⟩ : syracuseStep 3408223 = 5112335) B5112335
theorem B4544297 : Blo 2019435 4544297 := bstep (se 2 (by rfl) ⟨1704111, by rfl⟩ : syracuseStep 4544297 = 3408223) B3408223
theorem B3029531 : Blo 2019435 3029531 := bstep (se 1 (by rfl) ⟨2272148, by rfl⟩ : syracuseStep 3029531 = 4544297) B4544297
theorem B2019687 : Blo 2019435 2019687 := bstep (se 1 (by rfl) ⟨1514765, by rfl⟩ : syracuseStep 2019687 = 3029531) B3029531
theorem B2272153 : Blo 2019435 2272153 := bbase (se 2 (by rfl) ⟨852057, by rfl⟩ : syracuseStep 2272153 = 1704115) (by norm_num)
theorem B3029537 : Blo 2019435 3029537 := bstep (se 2 (by rfl) ⟨1136076, by rfl⟩ : syracuseStep 3029537 = 2272153) B2272153
theorem B2019691 : Blo 2019435 2019691 := bstep (se 1 (by rfl) ⟨1514768, by rfl⟩ : syracuseStep 2019691 = 3029537) B3029537
theorem B7668533 : Blo 2019435 7668533 := bbase (se 5 (by rfl) ⟨359462, by rfl⟩ : syracuseStep 7668533 = 718925) (by norm_num)
theorem B5112355 : Blo 2019435 5112355 := bstep (se 1 (by rfl) ⟨3834266, by rfl⟩ : syracuseStep 5112355 = 7668533) B7668533
theorem B6816473 : Blo 2019435 6816473 := bstep (se 2 (by rfl) ⟨2556177, by rfl⟩ : syracuseStep 6816473 = 5112355) B5112355
theorem B4544315 : Blo 2019435 4544315 := bstep (se 1 (by rfl) ⟨3408236, by rfl⟩ : syracuseStep 4544315 = 6816473) B6816473
theorem B3029543 : Blo 2019435 3029543 := bstep (se 1 (by rfl) ⟨2272157, by rfl⟩ : syracuseStep 3029543 = 4544315) B4544315
theorem B2019695 : Blo 2019435 2019695 := bstep (se 1 (by rfl) ⟨1514771, by rfl⟩ : syracuseStep 2019695 = 3029543) B3029543
theorem B3029549 : Blo 2019435 3029549 := bbase (se 3 (by rfl) ⟨568040, by rfl⟩ : syracuseStep 3029549 = 1136081) (by norm_num)
theorem B2019699 : Blo 2019435 2019699 := bstep (se 1 (by rfl) ⟨1514774, by rfl⟩ : syracuseStep 2019699 = 3029549) B3029549
theorem B4544333 : Blo 2019435 4544333 := bbase (se 3 (by rfl) ⟨852062, by rfl⟩ : syracuseStep 4544333 = 1704125) (by norm_num)
theorem B3029555 : Blo 2019435 3029555 := bstep (se 1 (by rfl) ⟨2272166, by rfl⟩ : syracuseStep 3029555 = 4544333) B4544333
theorem B2019703 : Blo 2019435 2019703 := bstep (se 1 (by rfl) ⟨1514777, by rfl⟩ : syracuseStep 2019703 = 3029555) B3029555
theorem B2556193 : Blo 2019435 2556193 := bbase (se 2 (by rfl) ⟨958572, by rfl⟩ : syracuseStep 2556193 = 1917145) (by norm_num)
theorem B3408257 : Blo 2019435 3408257 := bstep (se 2 (by rfl) ⟨1278096, by rfl⟩ : syracuseStep 3408257 = 2556193) B2556193
theorem B2272171 : Blo 2019435 2272171 := bstep (se 1 (by rfl) ⟨1704128, by rfl⟩ : syracuseStep 2272171 = 3408257) B3408257
theorem B3029561 : Blo 2019435 3029561 := bstep (se 2 (by rfl) ⟨1136085, by rfl⟩ : syracuseStep 3029561 = 2272171) B2272171
theorem B2019707 : Blo 2019435 2019707 := bstep (se 1 (by rfl) ⟨1514780, by rfl⟩ : syracuseStep 2019707 = 3029561) B3029561
theorem B23005781 : Blo 2019435 23005781 := bbase (se 8 (by rfl) ⟨134799, by rfl⟩ : syracuseStep 23005781 = 269599) (by norm_num)
theorem B15337187 : Blo 2019435 15337187 := bstep (se 1 (by rfl) ⟨11502890, by rfl⟩ : syracuseStep 15337187 = 23005781) B23005781
theorem B10224791 : Blo 2019435 10224791 := bstep (se 1 (by rfl) ⟨7668593, by rfl⟩ : syracuseStep 10224791 = 15337187) B15337187
theorem B6816527 : Blo 2019435 6816527 := bstep (se 1 (by rfl) ⟨5112395, by rfl⟩ : syracuseStep 6816527 = 10224791) B10224791
theorem B4544351 : Blo 2019435 4544351 := bstep (se 1 (by rfl) ⟨3408263, by rfl⟩ : syracuseStep 4544351 = 6816527) B6816527
theorem B3029567 : Blo 2019435 3029567 := bstep (se 1 (by rfl) ⟨2272175, by rfl⟩ : syracuseStep 3029567 = 4544351) B4544351
theorem B2019711 : Blo 2019435 2019711 := bstep (se 1 (by rfl) ⟨1514783, by rfl⟩ : syracuseStep 2019711 = 3029567) B3029567
theorem B3029573 : Blo 2019435 3029573 := bbase (se 4 (by rfl) ⟨284022, by rfl⟩ : syracuseStep 3029573 = 568045) (by norm_num)
theorem B2019715 : Blo 2019435 2019715 := bstep (se 1 (by rfl) ⟨1514786, by rfl⟩ : syracuseStep 2019715 = 3029573) B3029573
theorem B3408277 : Blo 2019435 3408277 := bbase (se 6 (by rfl) ⟨79881, by rfl⟩ : syracuseStep 3408277 = 159763) (by norm_num)
theorem B4544369 : Blo 2019435 4544369 := bstep (se 2 (by rfl) ⟨1704138, by rfl⟩ : syracuseStep 4544369 = 3408277) B3408277
theorem B3029579 : Blo 2019435 3029579 := bstep (se 1 (by rfl) ⟨2272184, by rfl⟩ : syracuseStep 3029579 = 4544369) B4544369
theorem B2019719 : Blo 2019435 2019719 := bstep (se 1 (by rfl) ⟨1514789, by rfl⟩ : syracuseStep 2019719 = 3029579) B3029579
theorem B2272189 : Blo 2019435 2272189 := bbase (se 3 (by rfl) ⟨426035, by rfl⟩ : syracuseStep 2272189 = 852071) (by norm_num)
theorem B3029585 : Blo 2019435 3029585 := bstep (se 2 (by rfl) ⟨1136094, by rfl⟩ : syracuseStep 3029585 = 2272189) B2272189
theorem B2019723 : Blo 2019435 2019723 := bstep (se 1 (by rfl) ⟨1514792, by rfl⟩ : syracuseStep 2019723 = 3029585) B3029585
theorem B6816581 : Blo 2019435 6816581 := bbase (se 4 (by rfl) ⟨639054, by rfl⟩ : syracuseStep 6816581 = 1278109) (by norm_num)
theorem B4544387 : Blo 2019435 4544387 := bstep (se 1 (by rfl) ⟨3408290, by rfl⟩ : syracuseStep 4544387 = 6816581) B6816581
theorem B3029591 : Blo 2019435 3029591 := bstep (se 1 (by rfl) ⟨2272193, by rfl⟩ : syracuseStep 3029591 = 4544387) B4544387
theorem B2019727 : Blo 2019435 2019727 := bstep (se 1 (by rfl) ⟨1514795, by rfl⟩ : syracuseStep 2019727 = 3029591) B3029591
theorem B3029597 : Blo 2019435 3029597 := bbase (se 3 (by rfl) ⟨568049, by rfl⟩ : syracuseStep 3029597 = 1136099) (by norm_num)
theorem B2019731 : Blo 2019435 2019731 := bstep (se 1 (by rfl) ⟨1514798, by rfl⟩ : syracuseStep 2019731 = 3029597) B3029597
theorem B4544405 : Blo 2019435 4544405 := bbase (se 6 (by rfl) ⟨106509, by rfl⟩ : syracuseStep 4544405 = 213019) (by norm_num)
theorem B3029603 : Blo 2019435 3029603 := bstep (se 1 (by rfl) ⟨2272202, by rfl⟩ : syracuseStep 3029603 = 4544405) B4544405
theorem B2019735 : Blo 2019435 2019735 := bstep (se 1 (by rfl) ⟨1514801, by rfl⟩ : syracuseStep 2019735 = 3029603) B3029603
theorem B4313645 : Blo 2019435 4313645 := bbase (se 3 (by rfl) ⟨808808, by rfl⟩ : syracuseStep 4313645 = 1617617) (by norm_num)
theorem B2875763 : Blo 2019435 2875763 := bstep (se 1 (by rfl) ⟨2156822, by rfl⟩ : syracuseStep 2875763 = 4313645) B4313645
theorem B7668701 : Blo 2019435 7668701 := bstep (se 3 (by rfl) ⟨1437881, by rfl⟩ : syracuseStep 7668701 = 2875763) B2875763
theorem B5112467 : Blo 2019435 5112467 := bstep (se 1 (by rfl) ⟨3834350, by rfl⟩ : syracuseStep 5112467 = 7668701) B7668701
theorem B3408311 : Blo 2019435 3408311 := bstep (se 1 (by rfl) ⟨2556233, by rfl⟩ : syracuseStep 3408311 = 5112467) B5112467
theorem B2272207 : Blo 2019435 2272207 := bstep (se 1 (by rfl) ⟨1704155, by rfl⟩ : syracuseStep 2272207 = 3408311) B3408311
theorem B3029609 : Blo 2019435 3029609 := bstep (se 2 (by rfl) ⟨1136103, by rfl⟩ : syracuseStep 3029609 = 2272207) B2272207
theorem B2019739 : Blo 2019435 2019739 := bstep (se 1 (by rfl) ⟨1514804, by rfl⟩ : syracuseStep 2019739 = 3029609) B3029609
theorem B2303213 : Blo 2019435 2303213 := bbase (se 3 (by rfl) ⟨431852, by rfl⟩ : syracuseStep 2303213 = 863705) (by norm_num)
theorem B6141901 : Blo 2019435 6141901 := bstep (se 3 (by rfl) ⟨1151606, by rfl⟩ : syracuseStep 6141901 = 2303213) B2303213
theorem B8189201 : Blo 2019435 8189201 := bstep (se 2 (by rfl) ⟨3070950, by rfl⟩ : syracuseStep 8189201 = 6141901) B6141901
theorem B21837869 : Blo 2019435 21837869 := bstep (se 3 (by rfl) ⟨4094600, by rfl⟩ : syracuseStep 21837869 = 8189201) B8189201
theorem B14558579 : Blo 2019435 14558579 := bstep (se 1 (by rfl) ⟨10918934, by rfl⟩ : syracuseStep 14558579 = 21837869) B21837869
theorem B9705719 : Blo 2019435 9705719 := bstep (se 1 (by rfl) ⟨7279289, by rfl⟩ : syracuseStep 9705719 = 14558579) B14558579
theorem B6470479 : Blo 2019435 6470479 := bstep (se 1 (by rfl) ⟨4852859, by rfl⟩ : syracuseStep 6470479 = 9705719) B9705719
theorem B8627305 : Blo 2019435 8627305 := bstep (se 2 (by rfl) ⟨3235239, by rfl⟩ : syracuseStep 8627305 = 6470479) B6470479
theorem B11503073 : Blo 2019435 11503073 := bstep (se 2 (by rfl) ⟨4313652, by rfl⟩ : syracuseStep 11503073 = 8627305) B8627305
theorem B7668715 : Blo 2019435 7668715 := bstep (se 1 (by rfl) ⟨5751536, by rfl⟩ : syracuseStep 7668715 = 11503073) B11503073
theorem B10224953 : Blo 2019435 10224953 := bstep (se 2 (by rfl) ⟨3834357, by rfl⟩ : syracuseStep 10224953 = 7668715) B7668715
theorem B6816635 : Blo 2019435 6816635 := bstep (se 1 (by rfl) ⟨5112476, by rfl⟩ : syracuseStep 6816635 = 10224953) B10224953
theorem B4544423 : Blo 2019435 4544423 := bstep (se 1 (by rfl) ⟨3408317, by rfl⟩ : syracuseStep 4544423 = 6816635) B6816635
theorem B3029615 : Blo 2019435 3029615 := bstep (se 1 (by rfl) ⟨2272211, by rfl⟩ : syracuseStep 3029615 = 4544423) B4544423
theorem B2019743 : Blo 2019435 2019743 := bstep (se 1 (by rfl) ⟨1514807, by rfl⟩ : syracuseStep 2019743 = 3029615) B3029615
theorem B3029621 : Blo 2019435 3029621 := bbase (se 5 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 3029621 = 284027) (by norm_num)
theorem B2019747 : Blo 2019435 2019747 := bstep (se 1 (by rfl) ⟨1514810, by rfl⟩ : syracuseStep 2019747 = 3029621) B3029621
theorem B3834373 : Blo 2019435 3834373 := bbase (se 4 (by rfl) ⟨359472, by rfl⟩ : syracuseStep 3834373 = 718945) (by norm_num)
theorem B5112497 : Blo 2019435 5112497 := bstep (se 2 (by rfl) ⟨1917186, by rfl⟩ : syracuseStep 5112497 = 3834373) B3834373
theorem B3408331 : Blo 2019435 3408331 := bstep (se 1 (by rfl) ⟨2556248, by rfl⟩ : syracuseStep 3408331 = 5112497) B5112497
theorem B4544441 : Blo 2019435 4544441 := bstep (se 2 (by rfl) ⟨1704165, by rfl⟩ : syracuseStep 4544441 = 3408331) B3408331
theorem B3029627 : Blo 2019435 3029627 := bstep (se 1 (by rfl) ⟨2272220, by rfl⟩ : syracuseStep 3029627 = 4544441) B4544441
theorem B2019751 : Blo 2019435 2019751 := bstep (se 1 (by rfl) ⟨1514813, by rfl⟩ : syracuseStep 2019751 = 3029627) B3029627
theorem B2272225 : Blo 2019435 2272225 := bbase (se 2 (by rfl) ⟨852084, by rfl⟩ : syracuseStep 2272225 = 1704169) (by norm_num)
theorem B3029633 : Blo 2019435 3029633 := bstep (se 2 (by rfl) ⟨1136112, by rfl⟩ : syracuseStep 3029633 = 2272225) B2272225
theorem B2019755 : Blo 2019435 2019755 := bstep (se 1 (by rfl) ⟨1514816, by rfl⟩ : syracuseStep 2019755 = 3029633) B3029633
theorem B5112517 : Blo 2019435 5112517 := bbase (se 4 (by rfl) ⟨479298, by rfl⟩ : syracuseStep 5112517 = 958597) (by norm_num)
theorem B6816689 : Blo 2019435 6816689 := bstep (se 2 (by rfl) ⟨2556258, by rfl⟩ : syracuseStep 6816689 = 5112517) B5112517
theorem B4544459 : Blo 2019435 4544459 := bstep (se 1 (by rfl) ⟨3408344, by rfl⟩ : syracuseStep 4544459 = 6816689) B6816689
theorem B3029639 : Blo 2019435 3029639 := bstep (se 1 (by rfl) ⟨2272229, by rfl⟩ : syracuseStep 3029639 = 4544459) B4544459
theorem B2019759 : Blo 2019435 2019759 := bstep (se 1 (by rfl) ⟨1514819, by rfl⟩ : syracuseStep 2019759 = 3029639) B3029639
theorem B3029645 : Blo 2019435 3029645 := bbase (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) (by norm_num)
theorem B2019763 : Blo 2019435 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B4544477 : Blo 2019435 4544477 := bbase (se 3 (by rfl) ⟨852089, by rfl⟩ : syracuseStep 4544477 = 1704179) (by norm_num)
theorem B3029651 : Blo 2019435 3029651 := bstep (se 1 (by rfl) ⟨2272238, by rfl⟩ : syracuseStep 3029651 = 4544477) B4544477
theorem B2019767 : Blo 2019435 2019767 := bstep (se 1 (by rfl) ⟨1514825, by rfl⟩ : syracuseStep 2019767 = 3029651) B3029651
theorem B3408365 : Blo 2019435 3408365 := bbase (se 3 (by rfl) ⟨639068, by rfl⟩ : syracuseStep 3408365 = 1278137) (by norm_num)
theorem B2272243 : Blo 2019435 2272243 := bstep (se 1 (by rfl) ⟨1704182, by rfl⟩ : syracuseStep 2272243 = 3408365) B3408365
theorem B3029657 : Blo 2019435 3029657 := bstep (se 2 (by rfl) ⟨1136121, by rfl⟩ : syracuseStep 3029657 = 2272243) B2272243
theorem B2019771 : Blo 2019435 2019771 := bstep (se 1 (by rfl) ⟨1514828, by rfl⟩ : syracuseStep 2019771 = 3029657) B3029657
theorem B25882325 : Blo 2019435 25882325 := bbase (se 7 (by rfl) ⟨303308, by rfl⟩ : syracuseStep 25882325 = 606617) (by norm_num)
theorem B17254883 : Blo 2019435 17254883 := bstep (se 1 (by rfl) ⟨12941162, by rfl⟩ : syracuseStep 17254883 = 25882325) B25882325
theorem B11503255 : Blo 2019435 11503255 := bstep (se 1 (by rfl) ⟨8627441, by rfl⟩ : syracuseStep 11503255 = 17254883) B17254883
theorem B15337673 : Blo 2019435 15337673 := bstep (se 2 (by rfl) ⟨5751627, by rfl⟩ : syracuseStep 15337673 = 11503255) B11503255
theorem B10225115 : Blo 2019435 10225115 := bstep (se 1 (by rfl) ⟨7668836, by rfl⟩ : syracuseStep 10225115 = 15337673) B15337673
theorem B6816743 : Blo 2019435 6816743 := bstep (se 1 (by rfl) ⟨5112557, by rfl⟩ : syracuseStep 6816743 = 10225115) B10225115
theorem B4544495 : Blo 2019435 4544495 := bstep (se 1 (by rfl) ⟨3408371, by rfl⟩ : syracuseStep 4544495 = 6816743) B6816743
theorem B3029663 : Blo 2019435 3029663 := bstep (se 1 (by rfl) ⟨2272247, by rfl⟩ : syracuseStep 3029663 = 4544495) B4544495
theorem B2019775 : Blo 2019435 2019775 := bstep (se 1 (by rfl) ⟨1514831, by rfl⟩ : syracuseStep 2019775 = 3029663) B3029663
theorem B3029669 : Blo 2019435 3029669 := bbase (se 4 (by rfl) ⟨284031, by rfl⟩ : syracuseStep 3029669 = 568063) (by norm_num)
theorem B2019779 : Blo 2019435 2019779 := bstep (se 1 (by rfl) ⟨1514834, by rfl⟩ : syracuseStep 2019779 = 3029669) B3029669
theorem B2556289 : Blo 2019435 2556289 := bbase (se 2 (by rfl) ⟨958608, by rfl⟩ : syracuseStep 2556289 = 1917217) (by norm_num)
theorem B3408385 : Blo 2019435 3408385 := bstep (se 2 (by rfl) ⟨1278144, by rfl⟩ : syracuseStep 3408385 = 2556289) B2556289
theorem B4544513 : Blo 2019435 4544513 := bstep (se 2 (by rfl) ⟨1704192, by rfl⟩ : syracuseStep 4544513 = 3408385) B3408385
theorem B3029675 : Blo 2019435 3029675 := bstep (se 1 (by rfl) ⟨2272256, by rfl⟩ : syracuseStep 3029675 = 4544513) B4544513
theorem B2019783 : Blo 2019435 2019783 := bstep (se 1 (by rfl) ⟨1514837, by rfl⟩ : syracuseStep 2019783 = 3029675) B3029675
theorem B2272261 : Blo 2019435 2272261 := bbase (se 4 (by rfl) ⟨213024, by rfl⟩ : syracuseStep 2272261 = 426049) (by norm_num)
theorem B3029681 : Blo 2019435 3029681 := bstep (se 2 (by rfl) ⟨1136130, by rfl⟩ : syracuseStep 3029681 = 2272261) B2272261
theorem B2019787 : Blo 2019435 2019787 := bstep (se 1 (by rfl) ⟨1514840, by rfl⟩ : syracuseStep 2019787 = 3029681) B3029681
theorem B2875837 : Blo 2019435 2875837 := bbase (se 3 (by rfl) ⟨539219, by rfl⟩ : syracuseStep 2875837 = 1078439) (by norm_num)
theorem B3834449 : Blo 2019435 3834449 := bstep (se 2 (by rfl) ⟨1437918, by rfl⟩ : syracuseStep 3834449 = 2875837) B2875837
theorem B2556299 : Blo 2019435 2556299 := bstep (se 1 (by rfl) ⟨1917224, by rfl⟩ : syracuseStep 2556299 = 3834449) B3834449
theorem B6816797 : Blo 2019435 6816797 := bstep (se 3 (by rfl) ⟨1278149, by rfl⟩ : syracuseStep 6816797 = 2556299) B2556299
theorem B4544531 : Blo 2019435 4544531 := bstep (se 1 (by rfl) ⟨3408398, by rfl⟩ : syracuseStep 4544531 = 6816797) B6816797
theorem B3029687 : Blo 2019435 3029687 := bstep (se 1 (by rfl) ⟨2272265, by rfl⟩ : syracuseStep 3029687 = 4544531) B4544531
theorem B2019791 : Blo 2019435 2019791 := bstep (se 1 (by rfl) ⟨1514843, by rfl⟩ : syracuseStep 2019791 = 3029687) B3029687
theorem B3029693 : Blo 2019435 3029693 := bbase (se 3 (by rfl) ⟨568067, by rfl⟩ : syracuseStep 3029693 = 1136135) (by norm_num)
theorem B2019795 : Blo 2019435 2019795 := bstep (se 1 (by rfl) ⟨1514846, by rfl⟩ : syracuseStep 2019795 = 3029693) B3029693
theorem B4544549 : Blo 2019435 4544549 := bbase (se 4 (by rfl) ⟨426051, by rfl⟩ : syracuseStep 4544549 = 852103) (by norm_num)
theorem B3029699 : Blo 2019435 3029699 := bstep (se 1 (by rfl) ⟨2272274, by rfl⟩ : syracuseStep 3029699 = 4544549) B4544549
theorem B2019799 : Blo 2019435 2019799 := bstep (se 1 (by rfl) ⟨1514849, by rfl⟩ : syracuseStep 2019799 = 3029699) B3029699
theorem B5112629 : Blo 2019435 5112629 := bbase (se 5 (by rfl) ⟨239654, by rfl⟩ : syracuseStep 5112629 = 479309) (by norm_num)
theorem B3408419 : Blo 2019435 3408419 := bstep (se 1 (by rfl) ⟨2556314, by rfl⟩ : syracuseStep 3408419 = 5112629) B5112629
theorem B2272279 : Blo 2019435 2272279 := bstep (se 1 (by rfl) ⟨1704209, by rfl⟩ : syracuseStep 2272279 = 3408419) B3408419
theorem B3029705 : Blo 2019435 3029705 := bstep (se 2 (by rfl) ⟨1136139, by rfl⟩ : syracuseStep 3029705 = 2272279) B2272279
theorem B2019803 : Blo 2019435 2019803 := bstep (se 1 (by rfl) ⟨1514852, by rfl⟩ : syracuseStep 2019803 = 3029705) B3029705
theorem B8189461 : Blo 2019435 8189461 := bbase (se 6 (by rfl) ⟨191940, by rfl⟩ : syracuseStep 8189461 = 383881) (by norm_num)
theorem B10919281 : Blo 2019435 10919281 := bstep (se 2 (by rfl) ⟨4094730, by rfl⟩ : syracuseStep 10919281 = 8189461) B8189461
theorem B14559041 : Blo 2019435 14559041 := bstep (se 2 (by rfl) ⟨5459640, by rfl⟩ : syracuseStep 14559041 = 10919281) B10919281
theorem B9706027 : Blo 2019435 9706027 := bstep (se 1 (by rfl) ⟨7279520, by rfl⟩ : syracuseStep 9706027 = 14559041) B14559041
theorem B12941369 : Blo 2019435 12941369 := bstep (se 2 (by rfl) ⟨4853013, by rfl⟩ : syracuseStep 12941369 = 9706027) B9706027
theorem B8627579 : Blo 2019435 8627579 := bstep (se 1 (by rfl) ⟨6470684, by rfl⟩ : syracuseStep 8627579 = 12941369) B12941369
theorem B5751719 : Blo 2019435 5751719 := bstep (se 1 (by rfl) ⟨4313789, by rfl⟩ : syracuseStep 5751719 = 8627579) B8627579
theorem B3834479 : Blo 2019435 3834479 := bstep (se 1 (by rfl) ⟨2875859, by rfl⟩ : syracuseStep 3834479 = 5751719) B5751719
theorem B10225277 : Blo 2019435 10225277 := bstep (se 3 (by rfl) ⟨1917239, by rfl⟩ : syracuseStep 10225277 = 3834479) B3834479
theorem B6816851 : Blo 2019435 6816851 := bstep (se 1 (by rfl) ⟨5112638, by rfl⟩ : syracuseStep 6816851 = 10225277) B10225277
theorem B4544567 : Blo 2019435 4544567 := bstep (se 1 (by rfl) ⟨3408425, by rfl⟩ : syracuseStep 4544567 = 6816851) B6816851
theorem B3029711 : Blo 2019435 3029711 := bstep (se 1 (by rfl) ⟨2272283, by rfl⟩ : syracuseStep 3029711 = 4544567) B4544567
theorem B2019807 : Blo 2019435 2019807 := bstep (se 1 (by rfl) ⟨1514855, by rfl⟩ : syracuseStep 2019807 = 3029711) B3029711
theorem B3029717 : Blo 2019435 3029717 := bbase (se 7 (by rfl) ⟨35504, by rfl⟩ : syracuseStep 3029717 = 71009) (by norm_num)
theorem B2019811 : Blo 2019435 2019811 := bstep (se 1 (by rfl) ⟨1514858, by rfl⟩ : syracuseStep 2019811 = 3029717) B3029717
theorem B2626561 : Blo 2019435 2626561 := bbase (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) (by norm_num)
theorem B3502081 : Blo 2019435 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B18677765 : Blo 2019435 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B12451843 : Blo 2019435 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B16602457 : Blo 2019435 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B22136609 : Blo 2019435 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B59030957 : Blo 2019435 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B39353971 : Blo 2019435 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B52471961 : Blo 2019435 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B34981307 : Blo 2019435 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B23320871 : Blo 2019435 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B15547247 : Blo 2019435 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B10364831 : Blo 2019435 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B6909887 : Blo 2019435 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B18426365 : Blo 2019435 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B12284243 : Blo 2019435 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B8189495 : Blo 2019435 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B5459663 : Blo 2019435 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B14559101 : Blo 2019435 14559101 := bstep (se 3 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 14559101 = 5459663) B5459663
theorem B9706067 : Blo 2019435 9706067 := bstep (se 1 (by rfl) ⟨7279550, by rfl⟩ : syracuseStep 9706067 = 14559101) B14559101
theorem B6470711 : Blo 2019435 6470711 := bstep (se 1 (by rfl) ⟨4853033, by rfl⟩ : syracuseStep 6470711 = 9706067) B9706067
theorem B4313807 : Blo 2019435 4313807 := bstep (se 1 (by rfl) ⟨3235355, by rfl⟩ : syracuseStep 4313807 = 6470711) B6470711
theorem B2875871 : Blo 2019435 2875871 := bstep (se 1 (by rfl) ⟨2156903, by rfl⟩ : syracuseStep 2875871 = 4313807) B4313807
theorem B7668989 : Blo 2019435 7668989 := bstep (se 3 (by rfl) ⟨1437935, by rfl⟩ : syracuseStep 7668989 = 2875871) B2875871
theorem B5112659 : Blo 2019435 5112659 := bstep (se 1 (by rfl) ⟨3834494, by rfl⟩ : syracuseStep 5112659 = 7668989) B7668989
theorem B3408439 : Blo 2019435 3408439 := bstep (se 1 (by rfl) ⟨2556329, by rfl⟩ : syracuseStep 3408439 = 5112659) B5112659
theorem B4544585 : Blo 2019435 4544585 := bstep (se 2 (by rfl) ⟨1704219, by rfl⟩ : syracuseStep 4544585 = 3408439) B3408439
theorem B3029723 : Blo 2019435 3029723 := bstep (se 1 (by rfl) ⟨2272292, by rfl⟩ : syracuseStep 3029723 = 4544585) B4544585
theorem B2019815 : Blo 2019435 2019815 := bstep (se 1 (by rfl) ⟨1514861, by rfl⟩ : syracuseStep 2019815 = 3029723) B3029723
theorem B2272297 : Blo 2019435 2272297 := bbase (se 2 (by rfl) ⟨852111, by rfl⟩ : syracuseStep 2272297 = 1704223) (by norm_num)
theorem B3029729 : Blo 2019435 3029729 := bstep (se 2 (by rfl) ⟨1136148, by rfl⟩ : syracuseStep 3029729 = 2272297) B2272297
theorem B2019819 : Blo 2019435 2019819 := bstep (se 1 (by rfl) ⟨1514864, by rfl⟩ : syracuseStep 2019819 = 3029729) B3029729
theorem B2527205 : Blo 2019435 2527205 := bbase (se 4 (by rfl) ⟨236925, by rfl⟩ : syracuseStep 2527205 = 473851) (by norm_num)
theorem B6739213 : Blo 2019435 6739213 := bstep (se 3 (by rfl) ⟨1263602, by rfl⟩ : syracuseStep 6739213 = 2527205) B2527205
theorem B8985617 : Blo 2019435 8985617 := bstep (se 2 (by rfl) ⟨3369606, by rfl⟩ : syracuseStep 8985617 = 6739213) B6739213
theorem B5990411 : Blo 2019435 5990411 := bstep (se 1 (by rfl) ⟨4492808, by rfl⟩ : syracuseStep 5990411 = 8985617) B8985617
theorem B15974429 : Blo 2019435 15974429 := bstep (se 3 (by rfl) ⟨2995205, by rfl⟩ : syracuseStep 15974429 = 5990411) B5990411
theorem B42598477 : Blo 2019435 42598477 := bstep (se 3 (by rfl) ⟨7987214, by rfl⟩ : syracuseStep 42598477 = 15974429) B15974429
theorem B56797969 : Blo 2019435 56797969 := bstep (se 2 (by rfl) ⟨21299238, by rfl⟩ : syracuseStep 56797969 = 42598477) B42598477
theorem B75730625 : Blo 2019435 75730625 := bstep (se 2 (by rfl) ⟨28398984, by rfl⟩ : syracuseStep 75730625 = 56797969) B56797969
theorem B50487083 : Blo 2019435 50487083 := bstep (se 1 (by rfl) ⟨37865312, by rfl⟩ : syracuseStep 50487083 = 75730625) B75730625
theorem B33658055 : Blo 2019435 33658055 := bstep (se 1 (by rfl) ⟨25243541, by rfl⟩ : syracuseStep 33658055 = 50487083) B50487083
theorem B22438703 : Blo 2019435 22438703 := bstep (se 1 (by rfl) ⟨16829027, by rfl⟩ : syracuseStep 22438703 = 33658055) B33658055
theorem B59836541 : Blo 2019435 59836541 := bstep (se 3 (by rfl) ⟨11219351, by rfl⟩ : syracuseStep 59836541 = 22438703) B22438703
theorem B159564109 : Blo 2019435 159564109 := bstep (se 3 (by rfl) ⟨29918270, by rfl⟩ : syracuseStep 159564109 = 59836541) B59836541
theorem B212752145 : Blo 2019435 212752145 := bstep (se 2 (by rfl) ⟨79782054, by rfl⟩ : syracuseStep 212752145 = 159564109) B159564109
theorem B141834763 : Blo 2019435 141834763 := bstep (se 1 (by rfl) ⟨106376072, by rfl⟩ : syracuseStep 141834763 = 212752145) B212752145
theorem B189113017 : Blo 2019435 189113017 := bstep (se 2 (by rfl) ⟨70917381, by rfl⟩ : syracuseStep 189113017 = 141834763) B141834763
theorem B252150689 : Blo 2019435 252150689 := bstep (se 2 (by rfl) ⟨94556508, by rfl⟩ : syracuseStep 252150689 = 189113017) B189113017
theorem B672401837 : Blo 2019435 672401837 := bstep (se 3 (by rfl) ⟨126075344, by rfl⟩ : syracuseStep 672401837 = 252150689) B252150689
theorem B448267891 : Blo 2019435 448267891 := bstep (se 1 (by rfl) ⟨336200918, by rfl⟩ : syracuseStep 448267891 = 672401837) B672401837
theorem B597690521 : Blo 2019435 597690521 := bstep (se 2 (by rfl) ⟨224133945, by rfl⟩ : syracuseStep 597690521 = 448267891) B448267891
theorem B398460347 : Blo 2019435 398460347 := bstep (se 1 (by rfl) ⟨298845260, by rfl⟩ : syracuseStep 398460347 = 597690521) B597690521
theorem B265640231 : Blo 2019435 265640231 := bstep (se 1 (by rfl) ⟨199230173, by rfl⟩ : syracuseStep 265640231 = 398460347) B398460347
theorem B177093487 : Blo 2019435 177093487 := bstep (se 1 (by rfl) ⟨132820115, by rfl⟩ : syracuseStep 177093487 = 265640231) B265640231
theorem B236124649 : Blo 2019435 236124649 := bstep (se 2 (by rfl) ⟨88546743, by rfl⟩ : syracuseStep 236124649 = 177093487) B177093487
theorem B1259331461 : Blo 2019435 1259331461 := bstep (se 4 (by rfl) ⟨118062324, by rfl⟩ : syracuseStep 1259331461 = 236124649) B236124649
theorem B839554307 : Blo 2019435 839554307 := bstep (se 1 (by rfl) ⟨629665730, by rfl⟩ : syracuseStep 839554307 = 1259331461) B1259331461
theorem B559702871 : Blo 2019435 559702871 := bstep (se 1 (by rfl) ⟨419777153, by rfl⟩ : syracuseStep 559702871 = 839554307) B839554307
theorem B373135247 : Blo 2019435 373135247 := bstep (se 1 (by rfl) ⟨279851435, by rfl⟩ : syracuseStep 373135247 = 559702871) B559702871
theorem B248756831 : Blo 2019435 248756831 := bstep (se 1 (by rfl) ⟨186567623, by rfl⟩ : syracuseStep 248756831 = 373135247) B373135247
theorem B165837887 : Blo 2019435 165837887 := bstep (se 1 (by rfl) ⟨124378415, by rfl⟩ : syracuseStep 165837887 = 248756831) B248756831
theorem B110558591 : Blo 2019435 110558591 := bstep (se 1 (by rfl) ⟨82918943, by rfl⟩ : syracuseStep 110558591 = 165837887) B165837887
theorem B73705727 : Blo 2019435 73705727 := bstep (se 1 (by rfl) ⟨55279295, by rfl⟩ : syracuseStep 73705727 = 110558591) B110558591
theorem B49137151 : Blo 2019435 49137151 := bstep (se 1 (by rfl) ⟨36852863, by rfl⟩ : syracuseStep 49137151 = 73705727) B73705727
theorem B65516201 : Blo 2019435 65516201 := bstep (se 2 (by rfl) ⟨24568575, by rfl⟩ : syracuseStep 65516201 = 49137151) B49137151
theorem B43677467 : Blo 2019435 43677467 := bstep (se 1 (by rfl) ⟨32758100, by rfl⟩ : syracuseStep 43677467 = 65516201) B65516201
theorem B29118311 : Blo 2019435 29118311 := bstep (se 1 (by rfl) ⟨21838733, by rfl⟩ : syracuseStep 29118311 = 43677467) B43677467
theorem B19412207 : Blo 2019435 19412207 := bstep (se 1 (by rfl) ⟨14559155, by rfl⟩ : syracuseStep 19412207 = 29118311) B29118311
theorem B12941471 : Blo 2019435 12941471 := bstep (se 1 (by rfl) ⟨9706103, by rfl⟩ : syracuseStep 12941471 = 19412207) B19412207
theorem B8627647 : Blo 2019435 8627647 := bstep (se 1 (by rfl) ⟨6470735, by rfl⟩ : syracuseStep 8627647 = 12941471) B12941471
theorem B11503529 : Blo 2019435 11503529 := bstep (se 2 (by rfl) ⟨4313823, by rfl⟩ : syracuseStep 11503529 = 8627647) B8627647
theorem B7669019 : Blo 2019435 7669019 := bstep (se 1 (by rfl) ⟨5751764, by rfl⟩ : syracuseStep 7669019 = 11503529) B11503529
theorem B5112679 : Blo 2019435 5112679 := bstep (se 1 (by rfl) ⟨3834509, by rfl⟩ : syracuseStep 5112679 = 7669019) B7669019
theorem B6816905 : Blo 2019435 6816905 := bstep (se 2 (by rfl) ⟨2556339, by rfl⟩ : syracuseStep 6816905 = 5112679) B5112679
theorem B4544603 : Blo 2019435 4544603 := bstep (se 1 (by rfl) ⟨3408452, by rfl⟩ : syracuseStep 4544603 = 6816905) B6816905
theorem B3029735 : Blo 2019435 3029735 := bstep (se 1 (by rfl) ⟨2272301, by rfl⟩ : syracuseStep 3029735 = 4544603) B4544603
theorem B2019823 : Blo 2019435 2019823 := bstep (se 1 (by rfl) ⟨1514867, by rfl⟩ : syracuseStep 2019823 = 3029735) B3029735
theorem B3029741 : Blo 2019435 3029741 := bbase (se 3 (by rfl) ⟨568076, by rfl⟩ : syracuseStep 3029741 = 1136153) (by norm_num)
theorem B2019827 : Blo 2019435 2019827 := bstep (se 1 (by rfl) ⟨1514870, by rfl⟩ : syracuseStep 2019827 = 3029741) B3029741
theorem B4544621 : Blo 2019435 4544621 := bbase (se 3 (by rfl) ⟨852116, by rfl⟩ : syracuseStep 4544621 = 1704233) (by norm_num)
theorem B3029747 : Blo 2019435 3029747 := bstep (se 1 (by rfl) ⟨2272310, by rfl⟩ : syracuseStep 3029747 = 4544621) B4544621
theorem B2019831 : Blo 2019435 2019831 := bstep (se 1 (by rfl) ⟨1514873, by rfl⟩ : syracuseStep 2019831 = 3029747) B3029747
theorem B3834533 : Blo 2019435 3834533 := bbase (se 4 (by rfl) ⟨359487, by rfl⟩ : syracuseStep 3834533 = 718975) (by norm_num)
theorem B2556355 : Blo 2019435 2556355 := bstep (se 1 (by rfl) ⟨1917266, by rfl⟩ : syracuseStep 2556355 = 3834533) B3834533
theorem B3408473 : Blo 2019435 3408473 := bstep (se 2 (by rfl) ⟨1278177, by rfl⟩ : syracuseStep 3408473 = 2556355) B2556355
theorem B2272315 : Blo 2019435 2272315 := bstep (se 1 (by rfl) ⟨1704236, by rfl⟩ : syracuseStep 2272315 = 3408473) B3408473
theorem B3029753 : Blo 2019435 3029753 := bstep (se 2 (by rfl) ⟨1136157, by rfl⟩ : syracuseStep 3029753 = 2272315) B2272315
theorem B2019835 : Blo 2019435 2019835 := bstep (se 1 (by rfl) ⟨1514876, by rfl⟩ : syracuseStep 2019835 = 3029753) B3029753
theorem B4606645 : Blo 2019435 4606645 := bbase (se 5 (by rfl) ⟨215936, by rfl⟩ : syracuseStep 4606645 = 431873) (by norm_num)
theorem B6142193 : Blo 2019435 6142193 := bstep (se 2 (by rfl) ⟨2303322, by rfl⟩ : syracuseStep 6142193 = 4606645) B4606645
theorem B4094795 : Blo 2019435 4094795 := bstep (se 1 (by rfl) ⟨3071096, by rfl⟩ : syracuseStep 4094795 = 6142193) B6142193
theorem B2729863 : Blo 2019435 2729863 := bstep (se 1 (by rfl) ⟨2047397, by rfl⟩ : syracuseStep 2729863 = 4094795) B4094795
theorem B14559269 : Blo 2019435 14559269 := bstep (se 4 (by rfl) ⟨1364931, by rfl⟩ : syracuseStep 14559269 = 2729863) B2729863
theorem B38824717 : Blo 2019435 38824717 := bstep (se 3 (by rfl) ⟨7279634, by rfl⟩ : syracuseStep 38824717 = 14559269) B14559269
theorem B51766289 : Blo 2019435 51766289 := bstep (se 2 (by rfl) ⟨19412358, by rfl⟩ : syracuseStep 51766289 = 38824717) B38824717
theorem B34510859 : Blo 2019435 34510859 := bstep (se 1 (by rfl) ⟨25883144, by rfl⟩ : syracuseStep 34510859 = 51766289) B51766289
theorem B23007239 : Blo 2019435 23007239 := bstep (se 1 (by rfl) ⟨17255429, by rfl⟩ : syracuseStep 23007239 = 34510859) B34510859
theorem B15338159 : Blo 2019435 15338159 := bstep (se 1 (by rfl) ⟨11503619, by rfl⟩ : syracuseStep 15338159 = 23007239) B23007239
theorem B10225439 : Blo 2019435 10225439 := bstep (se 1 (by rfl) ⟨7669079, by rfl⟩ : syracuseStep 10225439 = 15338159) B15338159
theorem B6816959 : Blo 2019435 6816959 := bstep (se 1 (by rfl) ⟨5112719, by rfl⟩ : syracuseStep 6816959 = 10225439) B10225439
theorem B4544639 : Blo 2019435 4544639 := bstep (se 1 (by rfl) ⟨3408479, by rfl⟩ : syracuseStep 4544639 = 6816959) B6816959
theorem B3029759 : Blo 2019435 3029759 := bstep (se 1 (by rfl) ⟨2272319, by rfl⟩ : syracuseStep 3029759 = 4544639) B4544639
theorem B2019839 : Blo 2019435 2019839 := bstep (se 1 (by rfl) ⟨1514879, by rfl⟩ : syracuseStep 2019839 = 3029759) B3029759
theorem B3029765 : Blo 2019435 3029765 := bbase (se 4 (by rfl) ⟨284040, by rfl⟩ : syracuseStep 3029765 = 568081) (by norm_num)
theorem B2019843 : Blo 2019435 2019843 := bstep (se 1 (by rfl) ⟨1514882, by rfl⟩ : syracuseStep 2019843 = 3029765) B3029765
theorem B3408493 : Blo 2019435 3408493 := bbase (se 3 (by rfl) ⟨639092, by rfl⟩ : syracuseStep 3408493 = 1278185) (by norm_num)
theorem B4544657 : Blo 2019435 4544657 := bstep (se 2 (by rfl) ⟨1704246, by rfl⟩ : syracuseStep 4544657 = 3408493) B3408493
theorem B3029771 : Blo 2019435 3029771 := bstep (se 1 (by rfl) ⟨2272328, by rfl⟩ : syracuseStep 3029771 = 4544657) B4544657
theorem B2019847 : Blo 2019435 2019847 := bstep (se 1 (by rfl) ⟨1514885, by rfl⟩ : syracuseStep 2019847 = 3029771) B3029771
theorem B2272333 : Blo 2019435 2272333 := bbase (se 3 (by rfl) ⟨426062, by rfl⟩ : syracuseStep 2272333 = 852125) (by norm_num)
theorem B3029777 : Blo 2019435 3029777 := bstep (se 2 (by rfl) ⟨1136166, by rfl⟩ : syracuseStep 3029777 = 2272333) B2272333
theorem B2019851 : Blo 2019435 2019851 := bstep (se 1 (by rfl) ⟨1514888, by rfl⟩ : syracuseStep 2019851 = 3029777) B3029777
theorem B6817013 : Blo 2019435 6817013 := bbase (se 5 (by rfl) ⟨319547, by rfl⟩ : syracuseStep 6817013 = 639095) (by norm_num)
theorem B4544675 : Blo 2019435 4544675 := bstep (se 1 (by rfl) ⟨3408506, by rfl⟩ : syracuseStep 4544675 = 6817013) B6817013
theorem B3029783 : Blo 2019435 3029783 := bstep (se 1 (by rfl) ⟨2272337, by rfl⟩ : syracuseStep 3029783 = 4544675) B4544675
theorem B2019855 : Blo 2019435 2019855 := bstep (se 1 (by rfl) ⟨1514891, by rfl⟩ : syracuseStep 2019855 = 3029783) B3029783
theorem B3029789 : Blo 2019435 3029789 := bbase (se 3 (by rfl) ⟨568085, by rfl⟩ : syracuseStep 3029789 = 1136171) (by norm_num)
theorem B2019859 : Blo 2019435 2019859 := bstep (se 1 (by rfl) ⟨1514894, by rfl⟩ : syracuseStep 2019859 = 3029789) B3029789
theorem B4544693 : Blo 2019435 4544693 := bbase (se 5 (by rfl) ⟨213032, by rfl⟩ : syracuseStep 4544693 = 426065) (by norm_num)
theorem B3029795 : Blo 2019435 3029795 := bstep (se 1 (by rfl) ⟨2272346, by rfl⟩ : syracuseStep 3029795 = 4544693) B4544693
theorem B2019863 : Blo 2019435 2019863 := bstep (se 1 (by rfl) ⟨1514897, by rfl⟩ : syracuseStep 2019863 = 3029795) B3029795
theorem B2186389 : Blo 2019435 2186389 := bbase (se 6 (by rfl) ⟨51243, by rfl⟩ : syracuseStep 2186389 = 102487) (by norm_num)
theorem B2915185 : Blo 2019435 2915185 := bstep (se 2 (by rfl) ⟨1093194, by rfl⟩ : syracuseStep 2915185 = 2186389) B2186389
theorem B3886913 : Blo 2019435 3886913 := bstep (se 2 (by rfl) ⟨1457592, by rfl⟩ : syracuseStep 3886913 = 2915185) B2915185
theorem B2591275 : Blo 2019435 2591275 := bstep (se 1 (by rfl) ⟨1943456, by rfl⟩ : syracuseStep 2591275 = 3886913) B3886913
theorem B3455033 : Blo 2019435 3455033 := bstep (se 2 (by rfl) ⟨1295637, by rfl⟩ : syracuseStep 3455033 = 2591275) B2591275
theorem B9213421 : Blo 2019435 9213421 := bstep (se 3 (by rfl) ⟨1727516, by rfl⟩ : syracuseStep 9213421 = 3455033) B3455033
theorem B12284561 : Blo 2019435 12284561 := bstep (se 2 (by rfl) ⟨4606710, by rfl⟩ : syracuseStep 12284561 = 9213421) B9213421
theorem B8189707 : Blo 2019435 8189707 := bstep (se 1 (by rfl) ⟨6142280, by rfl⟩ : syracuseStep 8189707 = 12284561) B12284561
theorem B10919609 : Blo 2019435 10919609 := bstep (se 2 (by rfl) ⟨4094853, by rfl⟩ : syracuseStep 10919609 = 8189707) B8189707
theorem B7279739 : Blo 2019435 7279739 := bstep (se 1 (by rfl) ⟨5459804, by rfl⟩ : syracuseStep 7279739 = 10919609) B10919609
theorem B4853159 : Blo 2019435 4853159 := bstep (se 1 (by rfl) ⟨3639869, by rfl⟩ : syracuseStep 4853159 = 7279739) B7279739
theorem B3235439 : Blo 2019435 3235439 := bstep (se 1 (by rfl) ⟨2426579, by rfl⟩ : syracuseStep 3235439 = 4853159) B4853159
theorem B2156959 : Blo 2019435 2156959 := bstep (se 1 (by rfl) ⟨1617719, by rfl⟩ : syracuseStep 2156959 = 3235439) B3235439
theorem B11503781 : Blo 2019435 11503781 := bstep (se 4 (by rfl) ⟨1078479, by rfl⟩ : syracuseStep 11503781 = 2156959) B2156959
theorem B7669187 : Blo 2019435 7669187 := bstep (se 1 (by rfl) ⟨5751890, by rfl⟩ : syracuseStep 7669187 = 11503781) B11503781
theorem B5112791 : Blo 2019435 5112791 := bstep (se 1 (by rfl) ⟨3834593, by rfl⟩ : syracuseStep 5112791 = 7669187) B7669187
theorem B3408527 : Blo 2019435 3408527 := bstep (se 1 (by rfl) ⟨2556395, by rfl⟩ : syracuseStep 3408527 = 5112791) B5112791
theorem B2272351 : Blo 2019435 2272351 := bstep (se 1 (by rfl) ⟨1704263, by rfl⟩ : syracuseStep 2272351 = 3408527) B3408527
theorem B3029801 : Blo 2019435 3029801 := bstep (se 2 (by rfl) ⟨1136175, by rfl⟩ : syracuseStep 3029801 = 2272351) B2272351
theorem B2019867 : Blo 2019435 2019867 := bstep (se 1 (by rfl) ⟨1514900, by rfl⟩ : syracuseStep 2019867 = 3029801) B3029801
theorem B3235445 : Blo 2019435 3235445 := bbase (se 5 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 3235445 = 303323) (by norm_num)
theorem B2156963 : Blo 2019435 2156963 := bstep (se 1 (by rfl) ⟨1617722, by rfl⟩ : syracuseStep 2156963 = 3235445) B3235445
theorem B5751901 : Blo 2019435 5751901 := bstep (se 3 (by rfl) ⟨1078481, by rfl⟩ : syracuseStep 5751901 = 2156963) B2156963
theorem B7669201 : Blo 2019435 7669201 := bstep (se 2 (by rfl) ⟨2875950, by rfl⟩ : syracuseStep 7669201 = 5751901) B5751901
theorem B10225601 : Blo 2019435 10225601 := bstep (se 2 (by rfl) ⟨3834600, by rfl⟩ : syracuseStep 10225601 = 7669201) B7669201
theorem B6817067 : Blo 2019435 6817067 := bstep (se 1 (by rfl) ⟨5112800, by rfl⟩ : syracuseStep 6817067 = 10225601) B10225601
theorem B4544711 : Blo 2019435 4544711 := bstep (se 1 (by rfl) ⟨3408533, by rfl⟩ : syracuseStep 4544711 = 6817067) B6817067
theorem B3029807 : Blo 2019435 3029807 := bstep (se 1 (by rfl) ⟨2272355, by rfl⟩ : syracuseStep 3029807 = 4544711) B4544711
theorem B2019871 : Blo 2019435 2019871 := bstep (se 1 (by rfl) ⟨1514903, by rfl⟩ : syracuseStep 2019871 = 3029807) B3029807
theorem B3029813 : Blo 2019435 3029813 := bbase (se 5 (by rfl) ⟨142022, by rfl⟩ : syracuseStep 3029813 = 284045) (by norm_num)
theorem B2019875 : Blo 2019435 2019875 := bstep (se 1 (by rfl) ⟨1514906, by rfl⟩ : syracuseStep 2019875 = 3029813) B3029813
theorem B5112821 : Blo 2019435 5112821 := bbase (se 5 (by rfl) ⟨239663, by rfl⟩ : syracuseStep 5112821 = 479327) (by norm_num)
theorem B3408547 : Blo 2019435 3408547 := bstep (se 1 (by rfl) ⟨2556410, by rfl⟩ : syracuseStep 3408547 = 5112821) B5112821
theorem B4544729 : Blo 2019435 4544729 := bstep (se 2 (by rfl) ⟨1704273, by rfl⟩ : syracuseStep 4544729 = 3408547) B3408547
theorem B3029819 : Blo 2019435 3029819 := bstep (se 1 (by rfl) ⟨2272364, by rfl⟩ : syracuseStep 3029819 = 4544729) B4544729
theorem B2019879 : Blo 2019435 2019879 := bstep (se 1 (by rfl) ⟨1514909, by rfl⟩ : syracuseStep 2019879 = 3029819) B3029819
theorem B2272369 : Blo 2019435 2272369 := bbase (se 2 (by rfl) ⟨852138, by rfl⟩ : syracuseStep 2272369 = 1704277) (by norm_num)
theorem B3029825 : Blo 2019435 3029825 := bstep (se 2 (by rfl) ⟨1136184, by rfl⟩ : syracuseStep 3029825 = 2272369) B2272369
theorem B2019883 : Blo 2019435 2019883 := bstep (se 1 (by rfl) ⟨1514912, by rfl⟩ : syracuseStep 2019883 = 3029825) B3029825
theorem B4606757 : Blo 2019435 4606757 := bbase (se 4 (by rfl) ⟨431883, by rfl⟩ : syracuseStep 4606757 = 863767) (by norm_num)
theorem B3071171 : Blo 2019435 3071171 := bstep (se 1 (by rfl) ⟨2303378, by rfl⟩ : syracuseStep 3071171 = 4606757) B4606757
theorem B2047447 : Blo 2019435 2047447 := bstep (se 1 (by rfl) ⟨1535585, by rfl⟩ : syracuseStep 2047447 = 3071171) B3071171
theorem B2729929 : Blo 2019435 2729929 := bstep (se 2 (by rfl) ⟨1023723, by rfl⟩ : syracuseStep 2729929 = 2047447) B2047447
theorem B3639905 : Blo 2019435 3639905 := bstep (se 2 (by rfl) ⟨1364964, by rfl⟩ : syracuseStep 3639905 = 2729929) B2729929
theorem B2426603 : Blo 2019435 2426603 := bstep (se 1 (by rfl) ⟨1819952, by rfl⟩ : syracuseStep 2426603 = 3639905) B3639905
theorem B6470941 : Blo 2019435 6470941 := bstep (se 3 (by rfl) ⟨1213301, by rfl⟩ : syracuseStep 6470941 = 2426603) B2426603
theorem B8627921 : Blo 2019435 8627921 := bstep (se 2 (by rfl) ⟨3235470, by rfl⟩ : syracuseStep 8627921 = 6470941) B6470941
theorem B5751947 : Blo 2019435 5751947 := bstep (se 1 (by rfl) ⟨4313960, by rfl⟩ : syracuseStep 5751947 = 8627921) B8627921
theorem B3834631 : Blo 2019435 3834631 := bstep (se 1 (by rfl) ⟨2875973, by rfl⟩ : syracuseStep 3834631 = 5751947) B5751947
theorem B5112841 : Blo 2019435 5112841 := bstep (se 2 (by rfl) ⟨1917315, by rfl⟩ : syracuseStep 5112841 = 3834631) B3834631
theorem B6817121 : Blo 2019435 6817121 := bstep (se 2 (by rfl) ⟨2556420, by rfl⟩ : syracuseStep 6817121 = 5112841) B5112841
theorem B4544747 : Blo 2019435 4544747 := bstep (se 1 (by rfl) ⟨3408560, by rfl⟩ : syracuseStep 4544747 = 6817121) B6817121
theorem B3029831 : Blo 2019435 3029831 := bstep (se 1 (by rfl) ⟨2272373, by rfl⟩ : syracuseStep 3029831 = 4544747) B4544747
theorem B2019887 : Blo 2019435 2019887 := bstep (se 1 (by rfl) ⟨1514915, by rfl⟩ : syracuseStep 2019887 = 3029831) B3029831
theorem B3029837 : Blo 2019435 3029837 := bbase (se 3 (by rfl) ⟨568094, by rfl⟩ : syracuseStep 3029837 = 1136189) (by norm_num)
theorem B2019891 : Blo 2019435 2019891 := bstep (se 1 (by rfl) ⟨1514918, by rfl⟩ : syracuseStep 2019891 = 3029837) B3029837
theorem B4544765 : Blo 2019435 4544765 := bbase (se 3 (by rfl) ⟨852143, by rfl⟩ : syracuseStep 4544765 = 1704287) (by norm_num)
theorem B3029843 : Blo 2019435 3029843 := bstep (se 1 (by rfl) ⟨2272382, by rfl⟩ : syracuseStep 3029843 = 4544765) B4544765
theorem B2019895 : Blo 2019435 2019895 := bstep (se 1 (by rfl) ⟨1514921, by rfl⟩ : syracuseStep 2019895 = 3029843) B3029843
theorem B3408581 : Blo 2019435 3408581 := bbase (se 4 (by rfl) ⟨319554, by rfl⟩ : syracuseStep 3408581 = 639109) (by norm_num)
theorem B2272387 : Blo 2019435 2272387 := bstep (se 1 (by rfl) ⟨1704290, by rfl⟩ : syracuseStep 2272387 = 3408581) B3408581
theorem B3029849 : Blo 2019435 3029849 := bstep (se 2 (by rfl) ⟨1136193, by rfl⟩ : syracuseStep 3029849 = 2272387) B2272387
theorem B2019899 : Blo 2019435 2019899 := bstep (se 1 (by rfl) ⟨1514924, by rfl⟩ : syracuseStep 2019899 = 3029849) B3029849
theorem B15338645 : Blo 2019435 15338645 := bbase (se 6 (by rfl) ⟨359499, by rfl⟩ : syracuseStep 15338645 = 718999) (by norm_num)
theorem B10225763 : Blo 2019435 10225763 := bstep (se 1 (by rfl) ⟨7669322, by rfl⟩ : syracuseStep 10225763 = 15338645) B15338645
theorem B6817175 : Blo 2019435 6817175 := bstep (se 1 (by rfl) ⟨5112881, by rfl⟩ : syracuseStep 6817175 = 10225763) B10225763
theorem B4544783 : Blo 2019435 4544783 := bstep (se 1 (by rfl) ⟨3408587, by rfl⟩ : syracuseStep 4544783 = 6817175) B6817175
theorem B3029855 : Blo 2019435 3029855 := bstep (se 1 (by rfl) ⟨2272391, by rfl⟩ : syracuseStep 3029855 = 4544783) B4544783
theorem B2019903 : Blo 2019435 2019903 := bstep (se 1 (by rfl) ⟨1514927, by rfl⟩ : syracuseStep 2019903 = 3029855) B3029855
theorem B3029861 : Blo 2019435 3029861 := bbase (se 4 (by rfl) ⟨284049, by rfl⟩ : syracuseStep 3029861 = 568099) (by norm_num)
theorem B2019907 : Blo 2019435 2019907 := bstep (se 1 (by rfl) ⟨1514930, by rfl⟩ : syracuseStep 2019907 = 3029861) B3029861
theorem B3834677 : Blo 2019435 3834677 := bbase (se 5 (by rfl) ⟨179750, by rfl⟩ : syracuseStep 3834677 = 359501) (by norm_num)
theorem B2556451 : Blo 2019435 2556451 := bstep (se 1 (by rfl) ⟨1917338, by rfl⟩ : syracuseStep 2556451 = 3834677) B3834677
theorem B3408601 : Blo 2019435 3408601 := bstep (se 2 (by rfl) ⟨1278225, by rfl⟩ : syracuseStep 3408601 = 2556451) B2556451
theorem B4544801 : Blo 2019435 4544801 := bstep (se 2 (by rfl) ⟨1704300, by rfl⟩ : syracuseStep 4544801 = 3408601) B3408601
theorem B3029867 : Blo 2019435 3029867 := bstep (se 1 (by rfl) ⟨2272400, by rfl⟩ : syracuseStep 3029867 = 4544801) B4544801
theorem B2019911 : Blo 2019435 2019911 := bstep (se 1 (by rfl) ⟨1514933, by rfl⟩ : syracuseStep 2019911 = 3029867) B3029867
theorem B2272405 : Blo 2019435 2272405 := bbase (se 6 (by rfl) ⟨53259, by rfl⟩ : syracuseStep 2272405 = 106519) (by norm_num)
theorem B3029873 : Blo 2019435 3029873 := bstep (se 2 (by rfl) ⟨1136202, by rfl⟩ : syracuseStep 3029873 = 2272405) B2272405
theorem B2019915 : Blo 2019435 2019915 := bstep (se 1 (by rfl) ⟨1514936, by rfl⟩ : syracuseStep 2019915 = 3029873) B3029873
theorem B2556461 : Blo 2019435 2556461 := bbase (se 3 (by rfl) ⟨479336, by rfl⟩ : syracuseStep 2556461 = 958673) (by norm_num)
theorem B6817229 : Blo 2019435 6817229 := bstep (se 3 (by rfl) ⟨1278230, by rfl⟩ : syracuseStep 6817229 = 2556461) B2556461
theorem B4544819 : Blo 2019435 4544819 := bstep (se 1 (by rfl) ⟨3408614, by rfl⟩ : syracuseStep 4544819 = 6817229) B6817229
theorem B3029879 : Blo 2019435 3029879 := bstep (se 1 (by rfl) ⟨2272409, by rfl⟩ : syracuseStep 3029879 = 4544819) B4544819
theorem B2019919 : Blo 2019435 2019919 := bstep (se 1 (by rfl) ⟨1514939, by rfl⟩ : syracuseStep 2019919 = 3029879) B3029879
theorem B3029885 : Blo 2019435 3029885 := bbase (se 3 (by rfl) ⟨568103, by rfl⟩ : syracuseStep 3029885 = 1136207) (by norm_num)
theorem B2019923 : Blo 2019435 2019923 := bstep (se 1 (by rfl) ⟨1514942, by rfl⟩ : syracuseStep 2019923 = 3029885) B3029885
theorem B4544837 : Blo 2019435 4544837 := bbase (se 4 (by rfl) ⟨426078, by rfl⟩ : syracuseStep 4544837 = 852157) (by norm_num)
theorem B3029891 : Blo 2019435 3029891 := bstep (se 1 (by rfl) ⟨2272418, by rfl⟩ : syracuseStep 3029891 = 4544837) B4544837
theorem B2019927 : Blo 2019435 2019927 := bstep (se 1 (by rfl) ⟨1514945, by rfl⟩ : syracuseStep 2019927 = 3029891) B3029891
theorem B2591357 : Blo 2019435 2591357 := bbase (se 3 (by rfl) ⟨485879, by rfl⟩ : syracuseStep 2591357 = 971759) (by norm_num)
theorem B6910285 : Blo 2019435 6910285 := bstep (se 3 (by rfl) ⟨1295678, by rfl⟩ : syracuseStep 6910285 = 2591357) B2591357
theorem B9213713 : Blo 2019435 9213713 := bstep (se 2 (by rfl) ⟨3455142, by rfl⟩ : syracuseStep 9213713 = 6910285) B6910285
theorem B6142475 : Blo 2019435 6142475 := bstep (se 1 (by rfl) ⟨4606856, by rfl⟩ : syracuseStep 6142475 = 9213713) B9213713
theorem B4094983 : Blo 2019435 4094983 := bstep (se 1 (by rfl) ⟨3071237, by rfl⟩ : syracuseStep 4094983 = 6142475) B6142475
theorem B5459977 : Blo 2019435 5459977 := bstep (se 2 (by rfl) ⟨2047491, by rfl⟩ : syracuseStep 5459977 = 4094983) B4094983
theorem B7279969 : Blo 2019435 7279969 := bstep (se 2 (by rfl) ⟨2729988, by rfl⟩ : syracuseStep 7279969 = 5459977) B5459977
theorem B9706625 : Blo 2019435 9706625 := bstep (se 2 (by rfl) ⟨3639984, by rfl⟩ : syracuseStep 9706625 = 7279969) B7279969
theorem B6471083 : Blo 2019435 6471083 := bstep (se 1 (by rfl) ⟨4853312, by rfl⟩ : syracuseStep 6471083 = 9706625) B9706625
theorem B4314055 : Blo 2019435 4314055 := bstep (se 1 (by rfl) ⟨3235541, by rfl⟩ : syracuseStep 4314055 = 6471083) B6471083
theorem B5752073 : Blo 2019435 5752073 := bstep (se 2 (by rfl) ⟨2157027, by rfl⟩ : syracuseStep 5752073 = 4314055) B4314055
theorem B3834715 : Blo 2019435 3834715 := bstep (se 1 (by rfl) ⟨2876036, by rfl⟩ : syracuseStep 3834715 = 5752073) B5752073
theorem B5112953 : Blo 2019435 5112953 := bstep (se 2 (by rfl) ⟨1917357, by rfl⟩ : syracuseStep 5112953 = 3834715) B3834715
theorem B3408635 : Blo 2019435 3408635 := bstep (se 1 (by rfl) ⟨2556476, by rfl⟩ : syracuseStep 3408635 = 5112953) B5112953
theorem B2272423 : Blo 2019435 2272423 := bstep (se 1 (by rfl) ⟨1704317, by rfl⟩ : syracuseStep 2272423 = 3408635) B3408635
theorem B3029897 : Blo 2019435 3029897 := bstep (se 2 (by rfl) ⟨1136211, by rfl⟩ : syracuseStep 3029897 = 2272423) B2272423
theorem B2019931 : Blo 2019435 2019931 := bstep (se 1 (by rfl) ⟨1514948, by rfl⟩ : syracuseStep 2019931 = 3029897) B3029897
theorem B10225925 : Blo 2019435 10225925 := bbase (se 4 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 10225925 = 1917361) (by norm_num)
theorem B6817283 : Blo 2019435 6817283 := bstep (se 1 (by rfl) ⟨5112962, by rfl⟩ : syracuseStep 6817283 = 10225925) B10225925
theorem B4544855 : Blo 2019435 4544855 := bstep (se 1 (by rfl) ⟨3408641, by rfl⟩ : syracuseStep 4544855 = 6817283) B6817283
theorem B3029903 : Blo 2019435 3029903 := bstep (se 1 (by rfl) ⟨2272427, by rfl⟩ : syracuseStep 3029903 = 4544855) B4544855
theorem B2019935 : Blo 2019435 2019935 := bstep (se 1 (by rfl) ⟨1514951, by rfl⟩ : syracuseStep 2019935 = 3029903) B3029903
theorem B3029909 : Blo 2019435 3029909 := bbase (se 6 (by rfl) ⟨71013, by rfl⟩ : syracuseStep 3029909 = 142027) (by norm_num)
theorem B2019939 : Blo 2019435 2019939 := bstep (se 1 (by rfl) ⟨1514954, by rfl⟩ : syracuseStep 2019939 = 3029909) B3029909
theorem B11504213 : Blo 2019435 11504213 := bbase (se 8 (by rfl) ⟨67407, by rfl⟩ : syracuseStep 11504213 = 134815) (by norm_num)
theorem B7669475 : Blo 2019435 7669475 := bstep (se 1 (by rfl) ⟨5752106, by rfl⟩ : syracuseStep 7669475 = 11504213) B11504213
theorem B5112983 : Blo 2019435 5112983 := bstep (se 1 (by rfl) ⟨3834737, by rfl⟩ : syracuseStep 5112983 = 7669475) B7669475
theorem B3408655 : Blo 2019435 3408655 := bstep (se 1 (by rfl) ⟨2556491, by rfl⟩ : syracuseStep 3408655 = 5112983) B5112983
theorem B4544873 : Blo 2019435 4544873 := bstep (se 2 (by rfl) ⟨1704327, by rfl⟩ : syracuseStep 4544873 = 3408655) B3408655
theorem B3029915 : Blo 2019435 3029915 := bstep (se 1 (by rfl) ⟨2272436, by rfl⟩ : syracuseStep 3029915 = 4544873) B4544873
theorem B2019943 : Blo 2019435 2019943 := bstep (se 1 (by rfl) ⟨1514957, by rfl⟩ : syracuseStep 2019943 = 3029915) B3029915
theorem B2272441 : Blo 2019435 2272441 := bbase (se 2 (by rfl) ⟨852165, by rfl⟩ : syracuseStep 2272441 = 1704331) (by norm_num)
theorem B3029921 : Blo 2019435 3029921 := bstep (se 2 (by rfl) ⟨1136220, by rfl⟩ : syracuseStep 3029921 = 2272441) B2272441
theorem B2019947 : Blo 2019435 2019947 := bstep (se 1 (by rfl) ⟨1514960, by rfl⟩ : syracuseStep 2019947 = 3029921) B3029921
theorem B3235573 : Blo 2019435 3235573 := bbase (se 5 (by rfl) ⟨151667, by rfl⟩ : syracuseStep 3235573 = 303335) (by norm_num)
theorem B4314097 : Blo 2019435 4314097 := bstep (se 2 (by rfl) ⟨1617786, by rfl⟩ : syracuseStep 4314097 = 3235573) B3235573
theorem B5752129 : Blo 2019435 5752129 := bstep (se 2 (by rfl) ⟨2157048, by rfl⟩ : syracuseStep 5752129 = 4314097) B4314097
theorem B7669505 : Blo 2019435 7669505 := bstep (se 2 (by rfl) ⟨2876064, by rfl⟩ : syracuseStep 7669505 = 5752129) B5752129
theorem B5113003 : Blo 2019435 5113003 := bstep (se 1 (by rfl) ⟨3834752, by rfl⟩ : syracuseStep 5113003 = 7669505) B7669505
theorem B6817337 : Blo 2019435 6817337 := bstep (se 2 (by rfl) ⟨2556501, by rfl⟩ : syracuseStep 6817337 = 5113003) B5113003
theorem B4544891 : Blo 2019435 4544891 := bstep (se 1 (by rfl) ⟨3408668, by rfl⟩ : syracuseStep 4544891 = 6817337) B6817337
theorem B3029927 : Blo 2019435 3029927 := bstep (se 1 (by rfl) ⟨2272445, by rfl⟩ : syracuseStep 3029927 = 4544891) B4544891
theorem B2019951 : Blo 2019435 2019951 := bstep (se 1 (by rfl) ⟨1514963, by rfl⟩ : syracuseStep 2019951 = 3029927) B3029927
theorem B3029933 : Blo 2019435 3029933 := bbase (se 3 (by rfl) ⟨568112, by rfl⟩ : syracuseStep 3029933 = 1136225) (by norm_num)
theorem B2019955 : Blo 2019435 2019955 := bstep (se 1 (by rfl) ⟨1514966, by rfl⟩ : syracuseStep 2019955 = 3029933) B3029933
theorem B4544909 : Blo 2019435 4544909 := bbase (se 3 (by rfl) ⟨852170, by rfl⟩ : syracuseStep 4544909 = 1704341) (by norm_num)
theorem B3029939 : Blo 2019435 3029939 := bstep (se 1 (by rfl) ⟨2272454, by rfl⟩ : syracuseStep 3029939 = 4544909) B4544909
theorem B2019959 : Blo 2019435 2019959 := bstep (se 1 (by rfl) ⟨1514969, by rfl⟩ : syracuseStep 2019959 = 3029939) B3029939
theorem B2556517 : Blo 2019435 2556517 := bbase (se 4 (by rfl) ⟨239673, by rfl⟩ : syracuseStep 2556517 = 479347) (by norm_num)
theorem B3408689 : Blo 2019435 3408689 := bstep (se 2 (by rfl) ⟨1278258, by rfl⟩ : syracuseStep 3408689 = 2556517) B2556517
theorem B2272459 : Blo 2019435 2272459 := bstep (se 1 (by rfl) ⟨1704344, by rfl⟩ : syracuseStep 2272459 = 3408689) B3408689
theorem B3029945 : Blo 2019435 3029945 := bstep (se 2 (by rfl) ⟨1136229, by rfl⟩ : syracuseStep 3029945 = 2272459) B2272459
theorem B2019963 : Blo 2019435 2019963 := bstep (se 1 (by rfl) ⟨1514972, by rfl⟩ : syracuseStep 2019963 = 3029945) B3029945
theorem B19413589 : Blo 2019435 19413589 := bbase (se 8 (by rfl) ⟨113751, by rfl⟩ : syracuseStep 19413589 = 227503) (by norm_num)
theorem B25884785 : Blo 2019435 25884785 := bstep (se 2 (by rfl) ⟨9706794, by rfl⟩ : syracuseStep 25884785 = 19413589) B19413589
theorem B17256523 : Blo 2019435 17256523 := bstep (se 1 (by rfl) ⟨12942392, by rfl⟩ : syracuseStep 17256523 = 25884785) B25884785
theorem B23008697 : Blo 2019435 23008697 := bstep (se 2 (by rfl) ⟨8628261, by rfl⟩ : syracuseStep 23008697 = 17256523) B17256523
theorem B15339131 : Blo 2019435 15339131 := bstep (se 1 (by rfl) ⟨11504348, by rfl⟩ : syracuseStep 15339131 = 23008697) B23008697
theorem B10226087 : Blo 2019435 10226087 := bstep (se 1 (by rfl) ⟨7669565, by rfl⟩ : syracuseStep 10226087 = 15339131) B15339131
theorem B6817391 : Blo 2019435 6817391 := bstep (se 1 (by rfl) ⟨5113043, by rfl⟩ : syracuseStep 6817391 = 10226087) B10226087
theorem B4544927 : Blo 2019435 4544927 := bstep (se 1 (by rfl) ⟨3408695, by rfl⟩ : syracuseStep 4544927 = 6817391) B6817391
theorem B3029951 : Blo 2019435 3029951 := bstep (se 1 (by rfl) ⟨2272463, by rfl⟩ : syracuseStep 3029951 = 4544927) B4544927
theorem B2019967 : Blo 2019435 2019967 := bstep (se 1 (by rfl) ⟨1514975, by rfl⟩ : syracuseStep 2019967 = 3029951) B3029951
theorem B3029957 : Blo 2019435 3029957 := bbase (se 4 (by rfl) ⟨284058, by rfl⟩ : syracuseStep 3029957 = 568117) (by norm_num)
theorem B2019971 : Blo 2019435 2019971 := bstep (se 1 (by rfl) ⟨1514978, by rfl⟩ : syracuseStep 2019971 = 3029957) B3029957
theorem B3408709 : Blo 2019435 3408709 := bbase (se 4 (by rfl) ⟨319566, by rfl⟩ : syracuseStep 3408709 = 639133) (by norm_num)
theorem B4544945 : Blo 2019435 4544945 := bstep (se 2 (by rfl) ⟨1704354, by rfl⟩ : syracuseStep 4544945 = 3408709) B3408709
theorem B3029963 : Blo 2019435 3029963 := bstep (se 1 (by rfl) ⟨2272472, by rfl⟩ : syracuseStep 3029963 = 4544945) B4544945
theorem B2019975 : Blo 2019435 2019975 := bstep (se 1 (by rfl) ⟨1514981, by rfl⟩ : syracuseStep 2019975 = 3029963) B3029963
theorem B2272477 : Blo 2019435 2272477 := bbase (se 3 (by rfl) ⟨426089, by rfl⟩ : syracuseStep 2272477 = 852179) (by norm_num)
theorem B3029969 : Blo 2019435 3029969 := bstep (se 2 (by rfl) ⟨1136238, by rfl⟩ : syracuseStep 3029969 = 2272477) B2272477
theorem B2019979 : Blo 2019435 2019979 := bstep (se 1 (by rfl) ⟨1514984, by rfl⟩ : syracuseStep 2019979 = 3029969) B3029969
theorem B6817445 : Blo 2019435 6817445 := bbase (se 4 (by rfl) ⟨639135, by rfl⟩ : syracuseStep 6817445 = 1278271) (by norm_num)
theorem B4544963 : Blo 2019435 4544963 := bstep (se 1 (by rfl) ⟨3408722, by rfl⟩ : syracuseStep 4544963 = 6817445) B6817445
theorem B3029975 : Blo 2019435 3029975 := bstep (se 1 (by rfl) ⟨2272481, by rfl⟩ : syracuseStep 3029975 = 4544963) B4544963
theorem B2019983 : Blo 2019435 2019983 := bstep (se 1 (by rfl) ⟨1514987, by rfl⟩ : syracuseStep 2019983 = 3029975) B3029975
theorem B3029981 : Blo 2019435 3029981 := bbase (se 3 (by rfl) ⟨568121, by rfl⟩ : syracuseStep 3029981 = 1136243) (by norm_num)
theorem B2019987 : Blo 2019435 2019987 := bstep (se 1 (by rfl) ⟨1514990, by rfl⟩ : syracuseStep 2019987 = 3029981) B3029981
theorem B4544981 : Blo 2019435 4544981 := bbase (se 7 (by rfl) ⟨53261, by rfl⟩ : syracuseStep 4544981 = 106523) (by norm_num)
theorem B3029987 : Blo 2019435 3029987 := bstep (se 1 (by rfl) ⟨2272490, by rfl⟩ : syracuseStep 3029987 = 4544981) B4544981
theorem B2019991 : Blo 2019435 2019991 := bstep (se 1 (by rfl) ⟨1514993, by rfl⟩ : syracuseStep 2019991 = 3029987) B3029987
theorem B2527421 : Blo 2019435 2527421 := bbase (se 3 (by rfl) ⟨473891, by rfl⟩ : syracuseStep 2527421 = 947783) (by norm_num)
theorem B6739789 : Blo 2019435 6739789 := bstep (se 3 (by rfl) ⟨1263710, by rfl⟩ : syracuseStep 6739789 = 2527421) B2527421
theorem B8986385 : Blo 2019435 8986385 := bstep (se 2 (by rfl) ⟨3369894, by rfl⟩ : syracuseStep 8986385 = 6739789) B6739789
theorem B5990923 : Blo 2019435 5990923 := bstep (se 1 (by rfl) ⟨4493192, by rfl⟩ : syracuseStep 5990923 = 8986385) B8986385
theorem B7987897 : Blo 2019435 7987897 := bstep (se 2 (by rfl) ⟨2995461, by rfl⟩ : syracuseStep 7987897 = 5990923) B5990923
theorem B10650529 : Blo 2019435 10650529 := bstep (se 2 (by rfl) ⟨3993948, by rfl⟩ : syracuseStep 10650529 = 7987897) B7987897
theorem B14200705 : Blo 2019435 14200705 := bstep (se 2 (by rfl) ⟨5325264, by rfl⟩ : syracuseStep 14200705 = 10650529) B10650529
theorem B18934273 : Blo 2019435 18934273 := bstep (se 2 (by rfl) ⟨7100352, by rfl⟩ : syracuseStep 18934273 = 14200705) B14200705
theorem B25245697 : Blo 2019435 25245697 := bstep (se 2 (by rfl) ⟨9467136, by rfl⟩ : syracuseStep 25245697 = 18934273) B18934273
theorem B33660929 : Blo 2019435 33660929 := bstep (se 2 (by rfl) ⟨12622848, by rfl⟩ : syracuseStep 33660929 = 25245697) B25245697
theorem B22440619 : Blo 2019435 22440619 := bstep (se 1 (by rfl) ⟨16830464, by rfl⟩ : syracuseStep 22440619 = 33660929) B33660929
theorem B29920825 : Blo 2019435 29920825 := bstep (se 2 (by rfl) ⟨11220309, by rfl⟩ : syracuseStep 29920825 = 22440619) B22440619
theorem B39894433 : Blo 2019435 39894433 := bstep (se 2 (by rfl) ⟨14960412, by rfl⟩ : syracuseStep 39894433 = 29920825) B29920825
theorem B212770309 : Blo 2019435 212770309 := bstep (se 4 (by rfl) ⟨19947216, by rfl⟩ : syracuseStep 212770309 = 39894433) B39894433
theorem B283693745 : Blo 2019435 283693745 := bstep (se 2 (by rfl) ⟨106385154, by rfl⟩ : syracuseStep 283693745 = 212770309) B212770309
theorem B189129163 : Blo 2019435 189129163 := bstep (se 1 (by rfl) ⟨141846872, by rfl⟩ : syracuseStep 189129163 = 283693745) B283693745
theorem B252172217 : Blo 2019435 252172217 := bstep (se 2 (by rfl) ⟨94564581, by rfl⟩ : syracuseStep 252172217 = 189129163) B189129163
theorem B168114811 : Blo 2019435 168114811 := bstep (se 1 (by rfl) ⟨126086108, by rfl⟩ : syracuseStep 168114811 = 252172217) B252172217
theorem B224153081 : Blo 2019435 224153081 := bstep (se 2 (by rfl) ⟨84057405, by rfl⟩ : syracuseStep 224153081 = 168114811) B168114811
theorem B149435387 : Blo 2019435 149435387 := bstep (se 1 (by rfl) ⟨112076540, by rfl⟩ : syracuseStep 149435387 = 224153081) B224153081
theorem B99623591 : Blo 2019435 99623591 := bstep (se 1 (by rfl) ⟨74717693, by rfl⟩ : syracuseStep 99623591 = 149435387) B149435387
theorem B66415727 : Blo 2019435 66415727 := bstep (se 1 (by rfl) ⟨49811795, by rfl⟩ : syracuseStep 66415727 = 99623591) B99623591
theorem B44277151 : Blo 2019435 44277151 := bstep (se 1 (by rfl) ⟨33207863, by rfl⟩ : syracuseStep 44277151 = 66415727) B66415727
theorem B59036201 : Blo 2019435 59036201 := bstep (se 2 (by rfl) ⟨22138575, by rfl⟩ : syracuseStep 59036201 = 44277151) B44277151
theorem B39357467 : Blo 2019435 39357467 := bstep (se 1 (by rfl) ⟨29518100, by rfl⟩ : syracuseStep 39357467 = 59036201) B59036201
theorem B26238311 : Blo 2019435 26238311 := bstep (se 1 (by rfl) ⟨19678733, by rfl⟩ : syracuseStep 26238311 = 39357467) B39357467
theorem B17492207 : Blo 2019435 17492207 := bstep (se 1 (by rfl) ⟨13119155, by rfl⟩ : syracuseStep 17492207 = 26238311) B26238311
theorem B46645885 : Blo 2019435 46645885 := bstep (se 3 (by rfl) ⟨8746103, by rfl⟩ : syracuseStep 46645885 = 17492207) B17492207
theorem B248778053 : Blo 2019435 248778053 := bstep (se 4 (by rfl) ⟨23322942, by rfl⟩ : syracuseStep 248778053 = 46645885) B46645885
theorem B165852035 : Blo 2019435 165852035 := bstep (se 1 (by rfl) ⟨124389026, by rfl⟩ : syracuseStep 165852035 = 248778053) B248778053
theorem B110568023 : Blo 2019435 110568023 := bstep (se 1 (by rfl) ⟨82926017, by rfl⟩ : syracuseStep 110568023 = 165852035) B165852035
theorem B73712015 : Blo 2019435 73712015 := bstep (se 1 (by rfl) ⟨55284011, by rfl⟩ : syracuseStep 73712015 = 110568023) B110568023
theorem B49141343 : Blo 2019435 49141343 := bstep (se 1 (by rfl) ⟨36856007, by rfl⟩ : syracuseStep 49141343 = 73712015) B73712015
theorem B32760895 : Blo 2019435 32760895 := bstep (se 1 (by rfl) ⟨24570671, by rfl⟩ : syracuseStep 32760895 = 49141343) B49141343
theorem B43681193 : Blo 2019435 43681193 := bstep (se 2 (by rfl) ⟨16380447, by rfl⟩ : syracuseStep 43681193 = 32760895) B32760895
theorem B29120795 : Blo 2019435 29120795 := bstep (se 1 (by rfl) ⟨21840596, by rfl⟩ : syracuseStep 29120795 = 43681193) B43681193
theorem B19413863 : Blo 2019435 19413863 := bstep (se 1 (by rfl) ⟨14560397, by rfl⟩ : syracuseStep 19413863 = 29120795) B29120795
theorem B12942575 : Blo 2019435 12942575 := bstep (se 1 (by rfl) ⟨9706931, by rfl⟩ : syracuseStep 12942575 = 19413863) B19413863
theorem B8628383 : Blo 2019435 8628383 := bstep (se 1 (by rfl) ⟨6471287, by rfl⟩ : syracuseStep 8628383 = 12942575) B12942575
theorem B5752255 : Blo 2019435 5752255 := bstep (se 1 (by rfl) ⟨4314191, by rfl⟩ : syracuseStep 5752255 = 8628383) B8628383
theorem B7669673 : Blo 2019435 7669673 := bstep (se 2 (by rfl) ⟨2876127, by rfl⟩ : syracuseStep 7669673 = 5752255) B5752255
theorem B5113115 : Blo 2019435 5113115 := bstep (se 1 (by rfl) ⟨3834836, by rfl⟩ : syracuseStep 5113115 = 7669673) B7669673
theorem B3408743 : Blo 2019435 3408743 := bstep (se 1 (by rfl) ⟨2556557, by rfl⟩ : syracuseStep 3408743 = 5113115) B5113115
theorem B2272495 : Blo 2019435 2272495 := bstep (se 1 (by rfl) ⟨1704371, by rfl⟩ : syracuseStep 2272495 = 3408743) B3408743
theorem B3029993 : Blo 2019435 3029993 := bstep (se 2 (by rfl) ⟨1136247, by rfl⟩ : syracuseStep 3029993 = 2272495) B2272495
theorem B2019995 : Blo 2019435 2019995 := bstep (se 1 (by rfl) ⟨1514996, by rfl⟩ : syracuseStep 2019995 = 3029993) B3029993
theorem B9706949 : Blo 2019435 9706949 := bbase (se 4 (by rfl) ⟨910026, by rfl⟩ : syracuseStep 9706949 = 1820053) (by norm_num)
theorem B6471299 : Blo 2019435 6471299 := bstep (se 1 (by rfl) ⟨4853474, by rfl⟩ : syracuseStep 6471299 = 9706949) B9706949
theorem B17256797 : Blo 2019435 17256797 := bstep (se 3 (by rfl) ⟨3235649, by rfl⟩ : syracuseStep 17256797 = 6471299) B6471299
theorem B11504531 : Blo 2019435 11504531 := bstep (se 1 (by rfl) ⟨8628398, by rfl⟩ : syracuseStep 11504531 = 17256797) B17256797
theorem B7669687 : Blo 2019435 7669687 := bstep (se 1 (by rfl) ⟨5752265, by rfl⟩ : syracuseStep 7669687 = 11504531) B11504531
theorem B10226249 : Blo 2019435 10226249 := bstep (se 2 (by rfl) ⟨3834843, by rfl⟩ : syracuseStep 10226249 = 7669687) B7669687
theorem B6817499 : Blo 2019435 6817499 := bstep (se 1 (by rfl) ⟨5113124, by rfl⟩ : syracuseStep 6817499 = 10226249) B10226249
theorem B4544999 : Blo 2019435 4544999 := bstep (se 1 (by rfl) ⟨3408749, by rfl⟩ : syracuseStep 4544999 = 6817499) B6817499
theorem B3029999 : Blo 2019435 3029999 := bstep (se 1 (by rfl) ⟨2272499, by rfl⟩ : syracuseStep 3029999 = 4544999) B4544999
theorem B2019999 : Blo 2019435 2019999 := bstep (se 1 (by rfl) ⟨1514999, by rfl⟩ : syracuseStep 2019999 = 3029999) B3029999
theorem B3030005 : Blo 2019435 3030005 := bbase (se 5 (by rfl) ⟨142031, by rfl⟩ : syracuseStep 3030005 = 284063) (by norm_num)
theorem B2020003 : Blo 2019435 2020003 := bstep (se 1 (by rfl) ⟨1515002, by rfl⟩ : syracuseStep 2020003 = 3030005) B3030005
theorem B4919717 : Blo 2019435 4919717 := bbase (se 4 (by rfl) ⟨461223, by rfl⟩ : syracuseStep 4919717 = 922447) (by norm_num)
theorem B13119245 : Blo 2019435 13119245 := bstep (se 3 (by rfl) ⟨2459858, by rfl⟩ : syracuseStep 13119245 = 4919717) B4919717
theorem B8746163 : Blo 2019435 8746163 := bstep (se 1 (by rfl) ⟨6559622, by rfl⟩ : syracuseStep 8746163 = 13119245) B13119245
theorem B5830775 : Blo 2019435 5830775 := bstep (se 1 (by rfl) ⟨4373081, by rfl⟩ : syracuseStep 5830775 = 8746163) B8746163
theorem B3887183 : Blo 2019435 3887183 := bstep (se 1 (by rfl) ⟨2915387, by rfl⟩ : syracuseStep 3887183 = 5830775) B5830775
theorem B2591455 : Blo 2019435 2591455 := bstep (se 1 (by rfl) ⟨1943591, by rfl⟩ : syracuseStep 2591455 = 3887183) B3887183
theorem B3455273 : Blo 2019435 3455273 := bstep (se 2 (by rfl) ⟨1295727, by rfl⟩ : syracuseStep 3455273 = 2591455) B2591455
theorem B2303515 : Blo 2019435 2303515 := bstep (se 1 (by rfl) ⟨1727636, by rfl⟩ : syracuseStep 2303515 = 3455273) B3455273
theorem B3071353 : Blo 2019435 3071353 := bstep (se 2 (by rfl) ⟨1151757, by rfl⟩ : syracuseStep 3071353 = 2303515) B2303515
theorem B4095137 : Blo 2019435 4095137 := bstep (se 2 (by rfl) ⟨1535676, by rfl⟩ : syracuseStep 4095137 = 3071353) B3071353
theorem B10920365 : Blo 2019435 10920365 := bstep (se 3 (by rfl) ⟨2047568, by rfl⟩ : syracuseStep 10920365 = 4095137) B4095137
theorem B7280243 : Blo 2019435 7280243 := bstep (se 1 (by rfl) ⟨5460182, by rfl⟩ : syracuseStep 7280243 = 10920365) B10920365
theorem B4853495 : Blo 2019435 4853495 := bstep (se 1 (by rfl) ⟨3640121, by rfl⟩ : syracuseStep 4853495 = 7280243) B7280243
theorem B3235663 : Blo 2019435 3235663 := bstep (se 1 (by rfl) ⟨2426747, by rfl⟩ : syracuseStep 3235663 = 4853495) B4853495
theorem B4314217 : Blo 2019435 4314217 := bstep (se 2 (by rfl) ⟨1617831, by rfl⟩ : syracuseStep 4314217 = 3235663) B3235663
theorem B5752289 : Blo 2019435 5752289 := bstep (se 2 (by rfl) ⟨2157108, by rfl⟩ : syracuseStep 5752289 = 4314217) B4314217
theorem B3834859 : Blo 2019435 3834859 := bstep (se 1 (by rfl) ⟨2876144, by rfl⟩ : syracuseStep 3834859 = 5752289) B5752289
theorem B5113145 : Blo 2019435 5113145 := bstep (se 2 (by rfl) ⟨1917429, by rfl⟩ : syracuseStep 5113145 = 3834859) B3834859
theorem B3408763 : Blo 2019435 3408763 := bstep (se 1 (by rfl) ⟨2556572, by rfl⟩ : syracuseStep 3408763 = 5113145) B5113145
theorem B4545017 : Blo 2019435 4545017 := bstep (se 2 (by rfl) ⟨1704381, by rfl⟩ : syracuseStep 4545017 = 3408763) B3408763
theorem B3030011 : Blo 2019435 3030011 := bstep (se 1 (by rfl) ⟨2272508, by rfl⟩ : syracuseStep 3030011 = 4545017) B4545017
theorem B2020007 : Blo 2019435 2020007 := bstep (se 1 (by rfl) ⟨1515005, by rfl⟩ : syracuseStep 2020007 = 3030011) B3030011
theorem B2272513 : Blo 2019435 2272513 := bbase (se 2 (by rfl) ⟨852192, by rfl⟩ : syracuseStep 2272513 = 1704385) (by norm_num)
theorem B3030017 : Blo 2019435 3030017 := bstep (se 2 (by rfl) ⟨1136256, by rfl⟩ : syracuseStep 3030017 = 2272513) B2272513
theorem B2020011 : Blo 2019435 2020011 := bstep (se 1 (by rfl) ⟨1515008, by rfl⟩ : syracuseStep 2020011 = 3030017) B3030017
theorem B5113165 : Blo 2019435 5113165 := bbase (se 3 (by rfl) ⟨958718, by rfl⟩ : syracuseStep 5113165 = 1917437) (by norm_num)
theorem B6817553 : Blo 2019435 6817553 := bstep (se 2 (by rfl) ⟨2556582, by rfl⟩ : syracuseStep 6817553 = 5113165) B5113165
theorem B4545035 : Blo 2019435 4545035 := bstep (se 1 (by rfl) ⟨3408776, by rfl⟩ : syracuseStep 4545035 = 6817553) B6817553
theorem B3030023 : Blo 2019435 3030023 := bstep (se 1 (by rfl) ⟨2272517, by rfl⟩ : syracuseStep 3030023 = 4545035) B4545035
theorem B2020015 : Blo 2019435 2020015 := bstep (se 1 (by rfl) ⟨1515011, by rfl⟩ : syracuseStep 2020015 = 3030023) B3030023
theorem B3030029 : Blo 2019435 3030029 := bbase (se 3 (by rfl) ⟨568130, by rfl⟩ : syracuseStep 3030029 = 1136261) (by norm_num)
theorem B2020019 : Blo 2019435 2020019 := bstep (se 1 (by rfl) ⟨1515014, by rfl⟩ : syracuseStep 2020019 = 3030029) B3030029
theorem B4545053 : Blo 2019435 4545053 := bbase (se 3 (by rfl) ⟨852197, by rfl⟩ : syracuseStep 4545053 = 1704395) (by norm_num)
theorem B3030035 : Blo 2019435 3030035 := bstep (se 1 (by rfl) ⟨2272526, by rfl⟩ : syracuseStep 3030035 = 4545053) B4545053
theorem B2020023 : Blo 2019435 2020023 := bstep (se 1 (by rfl) ⟨1515017, by rfl⟩ : syracuseStep 2020023 = 3030035) B3030035
theorem B3408797 : Blo 2019435 3408797 := bbase (se 3 (by rfl) ⟨639149, by rfl⟩ : syracuseStep 3408797 = 1278299) (by norm_num)
theorem B2272531 : Blo 2019435 2272531 := bstep (se 1 (by rfl) ⟨1704398, by rfl⟩ : syracuseStep 2272531 = 3408797) B3408797
theorem B3030041 : Blo 2019435 3030041 := bstep (se 2 (by rfl) ⟨1136265, by rfl⟩ : syracuseStep 3030041 = 2272531) B2272531
theorem B2020027 : Blo 2019435 2020027 := bstep (se 1 (by rfl) ⟨1515020, by rfl⟩ : syracuseStep 2020027 = 3030041) B3030041
theorem B9214165 : Blo 2019435 9214165 := bbase (se 7 (by rfl) ⟨107978, by rfl⟩ : syracuseStep 9214165 = 215957) (by norm_num)
theorem B12285553 : Blo 2019435 12285553 := bstep (se 2 (by rfl) ⟨4607082, by rfl⟩ : syracuseStep 12285553 = 9214165) B9214165
theorem B16380737 : Blo 2019435 16380737 := bstep (se 2 (by rfl) ⟨6142776, by rfl⟩ : syracuseStep 16380737 = 12285553) B12285553
theorem B10920491 : Blo 2019435 10920491 := bstep (se 1 (by rfl) ⟨8190368, by rfl⟩ : syracuseStep 10920491 = 16380737) B16380737
theorem B7280327 : Blo 2019435 7280327 := bstep (se 1 (by rfl) ⟨5460245, by rfl⟩ : syracuseStep 7280327 = 10920491) B10920491
theorem B19414205 : Blo 2019435 19414205 := bstep (se 3 (by rfl) ⟨3640163, by rfl⟩ : syracuseStep 19414205 = 7280327) B7280327
theorem B12942803 : Blo 2019435 12942803 := bstep (se 1 (by rfl) ⟨9707102, by rfl⟩ : syracuseStep 12942803 = 19414205) B19414205
theorem B8628535 : Blo 2019435 8628535 := bstep (se 1 (by rfl) ⟨6471401, by rfl⟩ : syracuseStep 8628535 = 12942803) B12942803
theorem B11504713 : Blo 2019435 11504713 := bstep (se 2 (by rfl) ⟨4314267, by rfl⟩ : syracuseStep 11504713 = 8628535) B8628535
theorem B15339617 : Blo 2019435 15339617 := bstep (se 2 (by rfl) ⟨5752356, by rfl⟩ : syracuseStep 15339617 = 11504713) B11504713
theorem B10226411 : Blo 2019435 10226411 := bstep (se 1 (by rfl) ⟨7669808, by rfl⟩ : syracuseStep 10226411 = 15339617) B15339617
theorem B6817607 : Blo 2019435 6817607 := bstep (se 1 (by rfl) ⟨5113205, by rfl⟩ : syracuseStep 6817607 = 10226411) B10226411
theorem B4545071 : Blo 2019435 4545071 := bstep (se 1 (by rfl) ⟨3408803, by rfl⟩ : syracuseStep 4545071 = 6817607) B6817607
theorem B3030047 : Blo 2019435 3030047 := bstep (se 1 (by rfl) ⟨2272535, by rfl⟩ : syracuseStep 3030047 = 4545071) B4545071
theorem B2020031 : Blo 2019435 2020031 := bstep (se 1 (by rfl) ⟨1515023, by rfl⟩ : syracuseStep 2020031 = 3030047) B3030047
theorem B3030053 : Blo 2019435 3030053 := bbase (se 4 (by rfl) ⟨284067, by rfl⟩ : syracuseStep 3030053 = 568135) (by norm_num)
theorem B2020035 : Blo 2019435 2020035 := bstep (se 1 (by rfl) ⟨1515026, by rfl⟩ : syracuseStep 2020035 = 3030053) B3030053
theorem B2556613 : Blo 2019435 2556613 := bbase (se 4 (by rfl) ⟨239682, by rfl⟩ : syracuseStep 2556613 = 479365) (by norm_num)
theorem B3408817 : Blo 2019435 3408817 := bstep (se 2 (by rfl) ⟨1278306, by rfl⟩ : syracuseStep 3408817 = 2556613) B2556613
theorem B4545089 : Blo 2019435 4545089 := bstep (se 2 (by rfl) ⟨1704408, by rfl⟩ : syracuseStep 4545089 = 3408817) B3408817
theorem B3030059 : Blo 2019435 3030059 := bstep (se 1 (by rfl) ⟨2272544, by rfl⟩ : syracuseStep 3030059 = 4545089) B4545089
theorem B2020039 : Blo 2019435 2020039 := bstep (se 1 (by rfl) ⟨1515029, by rfl⟩ : syracuseStep 2020039 = 3030059) B3030059
theorem B2272549 : Blo 2019435 2272549 := bbase (se 4 (by rfl) ⟨213051, by rfl⟩ : syracuseStep 2272549 = 426103) (by norm_num)
theorem B3030065 : Blo 2019435 3030065 := bstep (se 2 (by rfl) ⟨1136274, by rfl⟩ : syracuseStep 3030065 = 2272549) B2272549
theorem B2020043 : Blo 2019435 2020043 := bstep (se 1 (by rfl) ⟨1515032, by rfl⟩ : syracuseStep 2020043 = 3030065) B3030065
theorem B2047609 : Blo 2019435 2047609 := bbase (se 2 (by rfl) ⟨767853, by rfl⟩ : syracuseStep 2047609 = 1535707) (by norm_num)
theorem B10920581 : Blo 2019435 10920581 := bstep (se 4 (by rfl) ⟨1023804, by rfl⟩ : syracuseStep 10920581 = 2047609) B2047609
theorem B7280387 : Blo 2019435 7280387 := bstep (se 1 (by rfl) ⟨5460290, by rfl⟩ : syracuseStep 7280387 = 10920581) B10920581
theorem B4853591 : Blo 2019435 4853591 := bstep (se 1 (by rfl) ⟨3640193, by rfl⟩ : syracuseStep 4853591 = 7280387) B7280387
theorem B3235727 : Blo 2019435 3235727 := bstep (se 1 (by rfl) ⟨2426795, by rfl⟩ : syracuseStep 3235727 = 4853591) B4853591
theorem B8628605 : Blo 2019435 8628605 := bstep (se 3 (by rfl) ⟨1617863, by rfl⟩ : syracuseStep 8628605 = 3235727) B3235727
theorem B5752403 : Blo 2019435 5752403 := bstep (se 1 (by rfl) ⟨4314302, by rfl⟩ : syracuseStep 5752403 = 8628605) B8628605
theorem B3834935 : Blo 2019435 3834935 := bstep (se 1 (by rfl) ⟨2876201, by rfl⟩ : syracuseStep 3834935 = 5752403) B5752403
theorem B2556623 : Blo 2019435 2556623 := bstep (se 1 (by rfl) ⟨1917467, by rfl⟩ : syracuseStep 2556623 = 3834935) B3834935
theorem B6817661 : Blo 2019435 6817661 := bstep (se 3 (by rfl) ⟨1278311, by rfl⟩ : syracuseStep 6817661 = 2556623) B2556623
theorem B4545107 : Blo 2019435 4545107 := bstep (se 1 (by rfl) ⟨3408830, by rfl⟩ : syracuseStep 4545107 = 6817661) B6817661
theorem B3030071 : Blo 2019435 3030071 := bstep (se 1 (by rfl) ⟨2272553, by rfl⟩ : syracuseStep 3030071 = 4545107) B4545107
theorem B2020047 : Blo 2019435 2020047 := bstep (se 1 (by rfl) ⟨1515035, by rfl⟩ : syracuseStep 2020047 = 3030071) B3030071
theorem B3030077 : Blo 2019435 3030077 := bbase (se 3 (by rfl) ⟨568139, by rfl⟩ : syracuseStep 3030077 = 1136279) (by norm_num)
theorem B2020051 : Blo 2019435 2020051 := bstep (se 1 (by rfl) ⟨1515038, by rfl⟩ : syracuseStep 2020051 = 3030077) B3030077
theorem B4545125 : Blo 2019435 4545125 := bbase (se 4 (by rfl) ⟨426105, by rfl⟩ : syracuseStep 4545125 = 852211) (by norm_num)
theorem B3030083 : Blo 2019435 3030083 := bstep (se 1 (by rfl) ⟨2272562, by rfl⟩ : syracuseStep 3030083 = 4545125) B4545125
theorem B2020055 : Blo 2019435 2020055 := bstep (se 1 (by rfl) ⟨1515041, by rfl⟩ : syracuseStep 2020055 = 3030083) B3030083
theorem B5113277 : Blo 2019435 5113277 := bbase (se 3 (by rfl) ⟨958739, by rfl⟩ : syracuseStep 5113277 = 1917479) (by norm_num)
theorem B3408851 : Blo 2019435 3408851 := bstep (se 1 (by rfl) ⟨2556638, by rfl⟩ : syracuseStep 3408851 = 5113277) B5113277
theorem B2272567 : Blo 2019435 2272567 := bstep (se 1 (by rfl) ⟨1704425, by rfl⟩ : syracuseStep 2272567 = 3408851) B3408851
theorem B3030089 : Blo 2019435 3030089 := bstep (se 2 (by rfl) ⟨1136283, by rfl⟩ : syracuseStep 3030089 = 2272567) B2272567
theorem B2020059 : Blo 2019435 2020059 := bstep (se 1 (by rfl) ⟨1515044, by rfl⟩ : syracuseStep 2020059 = 3030089) B3030089
theorem B3834965 : Blo 2019435 3834965 := bbase (se 8 (by rfl) ⟨22470, by rfl⟩ : syracuseStep 3834965 = 44941) (by norm_num)
theorem B10226573 : Blo 2019435 10226573 := bstep (se 3 (by rfl) ⟨1917482, by rfl⟩ : syracuseStep 10226573 = 3834965) B3834965
theorem B6817715 : Blo 2019435 6817715 := bstep (se 1 (by rfl) ⟨5113286, by rfl⟩ : syracuseStep 6817715 = 10226573) B10226573
theorem B4545143 : Blo 2019435 4545143 := bstep (se 1 (by rfl) ⟨3408857, by rfl⟩ : syracuseStep 4545143 = 6817715) B6817715
theorem B3030095 : Blo 2019435 3030095 := bstep (se 1 (by rfl) ⟨2272571, by rfl⟩ : syracuseStep 3030095 = 4545143) B4545143
theorem B2020063 : Blo 2019435 2020063 := bstep (se 1 (by rfl) ⟨1515047, by rfl⟩ : syracuseStep 2020063 = 3030095) B3030095
theorem B3030101 : Blo 2019435 3030101 := bbase (se 8 (by rfl) ⟨17754, by rfl⟩ : syracuseStep 3030101 = 35509) (by norm_num)
theorem B2020067 : Blo 2019435 2020067 := bstep (se 1 (by rfl) ⟨1515050, by rfl⟩ : syracuseStep 2020067 = 3030101) B3030101
theorem B12943061 : Blo 2019435 12943061 := bbase (se 7 (by rfl) ⟨151676, by rfl⟩ : syracuseStep 12943061 = 303353) (by norm_num)
theorem B8628707 : Blo 2019435 8628707 := bstep (se 1 (by rfl) ⟨6471530, by rfl⟩ : syracuseStep 8628707 = 12943061) B12943061
theorem B5752471 : Blo 2019435 5752471 := bstep (se 1 (by rfl) ⟨4314353, by rfl⟩ : syracuseStep 5752471 = 8628707) B8628707
theorem B7669961 : Blo 2019435 7669961 := bstep (se 2 (by rfl) ⟨2876235, by rfl⟩ : syracuseStep 7669961 = 5752471) B5752471
theorem B5113307 : Blo 2019435 5113307 := bstep (se 1 (by rfl) ⟨3834980, by rfl⟩ : syracuseStep 5113307 = 7669961) B7669961
theorem B3408871 : Blo 2019435 3408871 := bstep (se 1 (by rfl) ⟨2556653, by rfl⟩ : syracuseStep 3408871 = 5113307) B5113307
theorem B4545161 : Blo 2019435 4545161 := bstep (se 2 (by rfl) ⟨1704435, by rfl⟩ : syracuseStep 4545161 = 3408871) B3408871
theorem B3030107 : Blo 2019435 3030107 := bstep (se 1 (by rfl) ⟨2272580, by rfl⟩ : syracuseStep 3030107 = 4545161) B4545161
theorem B2020071 : Blo 2019435 2020071 := bstep (se 1 (by rfl) ⟨1515053, by rfl⟩ : syracuseStep 2020071 = 3030107) B3030107
theorem B2272585 : Blo 2019435 2272585 := bbase (se 2 (by rfl) ⟨852219, by rfl⟩ : syracuseStep 2272585 = 1704439) (by norm_num)
theorem B3030113 : Blo 2019435 3030113 := bstep (se 2 (by rfl) ⟨1136292, by rfl⟩ : syracuseStep 3030113 = 2272585) B2272585
theorem B2020075 : Blo 2019435 2020075 := bstep (se 1 (by rfl) ⟨1515056, by rfl⟩ : syracuseStep 2020075 = 3030113) B3030113
theorem B12285845 : Blo 2019435 12285845 := bbase (se 6 (by rfl) ⟨287949, by rfl⟩ : syracuseStep 12285845 = 575899) (by norm_num)
theorem B8190563 : Blo 2019435 8190563 := bstep (se 1 (by rfl) ⟨6142922, by rfl⟩ : syracuseStep 8190563 = 12285845) B12285845
theorem B21841501 : Blo 2019435 21841501 := bstep (se 3 (by rfl) ⟨4095281, by rfl⟩ : syracuseStep 21841501 = 8190563) B8190563
theorem B29122001 : Blo 2019435 29122001 := bstep (se 2 (by rfl) ⟨10920750, by rfl⟩ : syracuseStep 29122001 = 21841501) B21841501
theorem B19414667 : Blo 2019435 19414667 := bstep (se 1 (by rfl) ⟨14561000, by rfl⟩ : syracuseStep 19414667 = 29122001) B29122001
theorem B12943111 : Blo 2019435 12943111 := bstep (se 1 (by rfl) ⟨9707333, by rfl⟩ : syracuseStep 12943111 = 19414667) B19414667
theorem B17257481 : Blo 2019435 17257481 := bstep (se 2 (by rfl) ⟨6471555, by rfl⟩ : syracuseStep 17257481 = 12943111) B12943111
theorem B11504987 : Blo 2019435 11504987 := bstep (se 1 (by rfl) ⟨8628740, by rfl⟩ : syracuseStep 11504987 = 17257481) B17257481
theorem B7669991 : Blo 2019435 7669991 := bstep (se 1 (by rfl) ⟨5752493, by rfl⟩ : syracuseStep 7669991 = 11504987) B11504987
theorem B5113327 : Blo 2019435 5113327 := bstep (se 1 (by rfl) ⟨3834995, by rfl⟩ : syracuseStep 5113327 = 7669991) B7669991
theorem B6817769 : Blo 2019435 6817769 := bstep (se 2 (by rfl) ⟨2556663, by rfl⟩ : syracuseStep 6817769 = 5113327) B5113327
theorem B4545179 : Blo 2019435 4545179 := bstep (se 1 (by rfl) ⟨3408884, by rfl⟩ : syracuseStep 4545179 = 6817769) B6817769
theorem B3030119 : Blo 2019435 3030119 := bstep (se 1 (by rfl) ⟨2272589, by rfl⟩ : syracuseStep 3030119 = 4545179) B4545179
theorem B2020079 : Blo 2019435 2020079 := bstep (se 1 (by rfl) ⟨1515059, by rfl⟩ : syracuseStep 2020079 = 3030119) B3030119
theorem B3030125 : Blo 2019435 3030125 := bbase (se 3 (by rfl) ⟨568148, by rfl⟩ : syracuseStep 3030125 = 1136297) (by norm_num)
theorem B2020083 : Blo 2019435 2020083 := bstep (se 1 (by rfl) ⟨1515062, by rfl⟩ : syracuseStep 2020083 = 3030125) B3030125
theorem B4545197 : Blo 2019435 4545197 := bbase (se 3 (by rfl) ⟨852224, by rfl⟩ : syracuseStep 4545197 = 1704449) (by norm_num)
theorem B3030131 : Blo 2019435 3030131 := bstep (se 1 (by rfl) ⟨2272598, by rfl⟩ : syracuseStep 3030131 = 4545197) B4545197
theorem B2020087 : Blo 2019435 2020087 := bstep (se 1 (by rfl) ⟨1515065, by rfl⟩ : syracuseStep 2020087 = 3030131) B3030131
theorem B4314397 : Blo 2019435 4314397 := bbase (se 3 (by rfl) ⟨808949, by rfl⟩ : syracuseStep 4314397 = 1617899) (by norm_num)
theorem B5752529 : Blo 2019435 5752529 := bstep (se 2 (by rfl) ⟨2157198, by rfl⟩ : syracuseStep 5752529 = 4314397) B4314397
theorem B3835019 : Blo 2019435 3835019 := bstep (se 1 (by rfl) ⟨2876264, by rfl⟩ : syracuseStep 3835019 = 5752529) B5752529
theorem B2556679 : Blo 2019435 2556679 := bstep (se 1 (by rfl) ⟨1917509, by rfl⟩ : syracuseStep 2556679 = 3835019) B3835019
theorem B3408905 : Blo 2019435 3408905 := bstep (se 2 (by rfl) ⟨1278339, by rfl⟩ : syracuseStep 3408905 = 2556679) B2556679
theorem B2272603 : Blo 2019435 2272603 := bstep (se 1 (by rfl) ⟨1704452, by rfl⟩ : syracuseStep 2272603 = 3408905) B3408905
theorem B3030137 : Blo 2019435 3030137 := bstep (se 2 (by rfl) ⟨1136301, by rfl⟩ : syracuseStep 3030137 = 2272603) B2272603
theorem B2020091 : Blo 2019435 2020091 := bstep (se 1 (by rfl) ⟨1515068, by rfl⟩ : syracuseStep 2020091 = 3030137) B3030137
theorem B2047657 : Blo 2019435 2047657 := bbase (se 2 (by rfl) ⟨767871, by rfl⟩ : syracuseStep 2047657 = 1535743) (by norm_num)
theorem B2730209 : Blo 2019435 2730209 := bstep (se 2 (by rfl) ⟨1023828, by rfl⟩ : syracuseStep 2730209 = 2047657) B2047657
theorem B29122229 : Blo 2019435 29122229 := bstep (se 5 (by rfl) ⟨1365104, by rfl⟩ : syracuseStep 29122229 = 2730209) B2730209
theorem B19414819 : Blo 2019435 19414819 := bstep (se 1 (by rfl) ⟨14561114, by rfl⟩ : syracuseStep 19414819 = 29122229) B29122229
theorem B25886425 : Blo 2019435 25886425 := bstep (se 2 (by rfl) ⟨9707409, by rfl⟩ : syracuseStep 25886425 = 19414819) B19414819
theorem B34515233 : Blo 2019435 34515233 := bstep (se 2 (by rfl) ⟨12943212, by rfl⟩ : syracuseStep 34515233 = 25886425) B25886425
theorem B23010155 : Blo 2019435 23010155 := bstep (se 1 (by rfl) ⟨17257616, by rfl⟩ : syracuseStep 23010155 = 34515233) B34515233
theorem B15340103 : Blo 2019435 15340103 := bstep (se 1 (by rfl) ⟨11505077, by rfl⟩ : syracuseStep 15340103 = 23010155) B23010155
theorem B10226735 : Blo 2019435 10226735 := bstep (se 1 (by rfl) ⟨7670051, by rfl⟩ : syracuseStep 10226735 = 15340103) B15340103
theorem B6817823 : Blo 2019435 6817823 := bstep (se 1 (by rfl) ⟨5113367, by rfl⟩ : syracuseStep 6817823 = 10226735) B10226735
theorem B4545215 : Blo 2019435 4545215 := bstep (se 1 (by rfl) ⟨3408911, by rfl⟩ : syracuseStep 4545215 = 6817823) B6817823
theorem B3030143 : Blo 2019435 3030143 := bstep (se 1 (by rfl) ⟨2272607, by rfl⟩ : syracuseStep 3030143 = 4545215) B4545215
theorem B2020095 : Blo 2019435 2020095 := bstep (se 1 (by rfl) ⟨1515071, by rfl⟩ : syracuseStep 2020095 = 3030143) B3030143
theorem B3030149 : Blo 2019435 3030149 := bbase (se 4 (by rfl) ⟨284076, by rfl⟩ : syracuseStep 3030149 = 568153) (by norm_num)
theorem B2020099 : Blo 2019435 2020099 := bstep (se 1 (by rfl) ⟨1515074, by rfl⟩ : syracuseStep 2020099 = 3030149) B3030149
theorem B3408925 : Blo 2019435 3408925 := bbase (se 3 (by rfl) ⟨639173, by rfl⟩ : syracuseStep 3408925 = 1278347) (by norm_num)
theorem B4545233 : Blo 2019435 4545233 := bstep (se 2 (by rfl) ⟨1704462, by rfl⟩ : syracuseStep 4545233 = 3408925) B3408925
theorem B3030155 : Blo 2019435 3030155 := bstep (se 1 (by rfl) ⟨2272616, by rfl⟩ : syracuseStep 3030155 = 4545233) B4545233
theorem B2020103 : Blo 2019435 2020103 := bstep (se 1 (by rfl) ⟨1515077, by rfl⟩ : syracuseStep 2020103 = 3030155) B3030155
theorem B2272621 : Blo 2019435 2272621 := bbase (se 3 (by rfl) ⟨426116, by rfl⟩ : syracuseStep 2272621 = 852233) (by norm_num)
theorem B3030161 : Blo 2019435 3030161 := bstep (se 2 (by rfl) ⟨1136310, by rfl⟩ : syracuseStep 3030161 = 2272621) B2272621
theorem B2020107 : Blo 2019435 2020107 := bstep (se 1 (by rfl) ⟨1515080, by rfl⟩ : syracuseStep 2020107 = 3030161) B3030161
theorem B6817877 : Blo 2019435 6817877 := bbase (se 8 (by rfl) ⟨39948, by rfl⟩ : syracuseStep 6817877 = 79897) (by norm_num)
theorem B4545251 : Blo 2019435 4545251 := bstep (se 1 (by rfl) ⟨3408938, by rfl⟩ : syracuseStep 4545251 = 6817877) B6817877
theorem B3030167 : Blo 2019435 3030167 := bstep (se 1 (by rfl) ⟨2272625, by rfl⟩ : syracuseStep 3030167 = 4545251) B4545251
theorem B2020111 : Blo 2019435 2020111 := bstep (se 1 (by rfl) ⟨1515083, by rfl⟩ : syracuseStep 2020111 = 3030167) B3030167
theorem B3030173 : Blo 2019435 3030173 := bbase (se 3 (by rfl) ⟨568157, by rfl⟩ : syracuseStep 3030173 = 1136315) (by norm_num)
theorem B2020115 : Blo 2019435 2020115 := bstep (se 1 (by rfl) ⟨1515086, by rfl⟩ : syracuseStep 2020115 = 3030173) B3030173
theorem B4545269 : Blo 2019435 4545269 := bbase (se 5 (by rfl) ⟨213059, by rfl⟩ : syracuseStep 4545269 = 426119) (by norm_num)
theorem B3030179 : Blo 2019435 3030179 := bstep (se 1 (by rfl) ⟨2272634, by rfl⟩ : syracuseStep 3030179 = 4545269) B4545269
theorem B2020119 : Blo 2019435 2020119 := bstep (se 1 (by rfl) ⟨1515089, by rfl⟩ : syracuseStep 2020119 = 3030179) B3030179
theorem B4853773 : Blo 2019435 4853773 := bbase (se 3 (by rfl) ⟨910082, by rfl⟩ : syracuseStep 4853773 = 1820165) (by norm_num)
theorem B25886789 : Blo 2019435 25886789 := bstep (se 4 (by rfl) ⟨2426886, by rfl⟩ : syracuseStep 25886789 = 4853773) B4853773
theorem B17257859 : Blo 2019435 17257859 := bstep (se 1 (by rfl) ⟨12943394, by rfl⟩ : syracuseStep 17257859 = 25886789) B25886789
theorem B11505239 : Blo 2019435 11505239 := bstep (se 1 (by rfl) ⟨8628929, by rfl⟩ : syracuseStep 11505239 = 17257859) B17257859
theorem B7670159 : Blo 2019435 7670159 := bstep (se 1 (by rfl) ⟨5752619, by rfl⟩ : syracuseStep 7670159 = 11505239) B11505239
theorem B5113439 : Blo 2019435 5113439 := bstep (se 1 (by rfl) ⟨3835079, by rfl⟩ : syracuseStep 5113439 = 7670159) B7670159
theorem B3408959 : Blo 2019435 3408959 := bstep (se 1 (by rfl) ⟨2556719, by rfl⟩ : syracuseStep 3408959 = 5113439) B5113439
theorem B2272639 : Blo 2019435 2272639 := bstep (se 1 (by rfl) ⟨1704479, by rfl⟩ : syracuseStep 2272639 = 3408959) B3408959
theorem B3030185 : Blo 2019435 3030185 := bstep (se 2 (by rfl) ⟨1136319, by rfl⟩ : syracuseStep 3030185 = 2272639) B2272639
theorem B2020123 : Blo 2019435 2020123 := bstep (se 1 (by rfl) ⟨1515092, by rfl⟩ : syracuseStep 2020123 = 3030185) B3030185
theorem B10921013 : Blo 2019435 10921013 := bbase (se 5 (by rfl) ⟨511922, by rfl⟩ : syracuseStep 10921013 = 1023845) (by norm_num)
theorem B7280675 : Blo 2019435 7280675 := bstep (se 1 (by rfl) ⟨5460506, by rfl⟩ : syracuseStep 7280675 = 10921013) B10921013
theorem B4853783 : Blo 2019435 4853783 := bstep (se 1 (by rfl) ⟨3640337, by rfl⟩ : syracuseStep 4853783 = 7280675) B7280675
theorem B3235855 : Blo 2019435 3235855 := bstep (se 1 (by rfl) ⟨2426891, by rfl⟩ : syracuseStep 3235855 = 4853783) B4853783
theorem B4314473 : Blo 2019435 4314473 := bstep (se 2 (by rfl) ⟨1617927, by rfl⟩ : syracuseStep 4314473 = 3235855) B3235855
theorem B2876315 : Blo 2019435 2876315 := bstep (se 1 (by rfl) ⟨2157236, by rfl⟩ : syracuseStep 2876315 = 4314473) B4314473
theorem B7670173 : Blo 2019435 7670173 := bstep (se 3 (by rfl) ⟨1438157, by rfl⟩ : syracuseStep 7670173 = 2876315) B2876315
theorem B10226897 : Blo 2019435 10226897 := bstep (se 2 (by rfl) ⟨3835086, by rfl⟩ : syracuseStep 10226897 = 7670173) B7670173
theorem B6817931 : Blo 2019435 6817931 := bstep (se 1 (by rfl) ⟨5113448, by rfl⟩ : syracuseStep 6817931 = 10226897) B10226897
theorem B4545287 : Blo 2019435 4545287 := bstep (se 1 (by rfl) ⟨3408965, by rfl⟩ : syracuseStep 4545287 = 6817931) B6817931
theorem B3030191 : Blo 2019435 3030191 := bstep (se 1 (by rfl) ⟨2272643, by rfl⟩ : syracuseStep 3030191 = 4545287) B4545287
theorem B2020127 : Blo 2019435 2020127 := bstep (se 1 (by rfl) ⟨1515095, by rfl⟩ : syracuseStep 2020127 = 3030191) B3030191
theorem B3030197 : Blo 2019435 3030197 := bbase (se 5 (by rfl) ⟨142040, by rfl⟩ : syracuseStep 3030197 = 284081) (by norm_num)
theorem B2020131 : Blo 2019435 2020131 := bstep (se 1 (by rfl) ⟨1515098, by rfl⟩ : syracuseStep 2020131 = 3030197) B3030197
theorem B5113469 : Blo 2019435 5113469 := bbase (se 3 (by rfl) ⟨958775, by rfl⟩ : syracuseStep 5113469 = 1917551) (by norm_num)
theorem B3408979 : Blo 2019435 3408979 := bstep (se 1 (by rfl) ⟨2556734, by rfl⟩ : syracuseStep 3408979 = 5113469) B5113469
theorem B4545305 : Blo 2019435 4545305 := bstep (se 2 (by rfl) ⟨1704489, by rfl⟩ : syracuseStep 4545305 = 3408979) B3408979
theorem B3030203 : Blo 2019435 3030203 := bstep (se 1 (by rfl) ⟨2272652, by rfl⟩ : syracuseStep 3030203 = 4545305) B4545305
theorem B2020135 : Blo 2019435 2020135 := bstep (se 1 (by rfl) ⟨1515101, by rfl⟩ : syracuseStep 2020135 = 3030203) B3030203
theorem B2272657 : Blo 2019435 2272657 := bbase (se 2 (by rfl) ⟨852246, by rfl⟩ : syracuseStep 2272657 = 1704493) (by norm_num)
theorem B3030209 : Blo 2019435 3030209 := bstep (se 2 (by rfl) ⟨1136328, by rfl⟩ : syracuseStep 3030209 = 2272657) B2272657
theorem B2020139 : Blo 2019435 2020139 := bstep (se 1 (by rfl) ⟨1515104, by rfl⟩ : syracuseStep 2020139 = 3030209) B3030209
theorem B3835117 : Blo 2019435 3835117 := bbase (se 3 (by rfl) ⟨719084, by rfl⟩ : syracuseStep 3835117 = 1438169) (by norm_num)
theorem B5113489 : Blo 2019435 5113489 := bstep (se 2 (by rfl) ⟨1917558, by rfl⟩ : syracuseStep 5113489 = 3835117) B3835117
theorem B6817985 : Blo 2019435 6817985 := bstep (se 2 (by rfl) ⟨2556744, by rfl⟩ : syracuseStep 6817985 = 5113489) B5113489
theorem B4545323 : Blo 2019435 4545323 := bstep (se 1 (by rfl) ⟨3408992, by rfl⟩ : syracuseStep 4545323 = 6817985) B6817985
theorem B3030215 : Blo 2019435 3030215 := bstep (se 1 (by rfl) ⟨2272661, by rfl⟩ : syracuseStep 3030215 = 4545323) B4545323
theorem B2020143 : Blo 2019435 2020143 := bstep (se 1 (by rfl) ⟨1515107, by rfl⟩ : syracuseStep 2020143 = 3030215) B3030215
theorem B3030221 : Blo 2019435 3030221 := bbase (se 3 (by rfl) ⟨568166, by rfl⟩ : syracuseStep 3030221 = 1136333) (by norm_num)
theorem B2020147 : Blo 2019435 2020147 := bstep (se 1 (by rfl) ⟨1515110, by rfl⟩ : syracuseStep 2020147 = 3030221) B3030221
theorem B4545341 : Blo 2019435 4545341 := bbase (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) (by norm_num)
theorem B3030227 : Blo 2019435 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B2020151 : Blo 2019435 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B3409013 : Blo 2019435 3409013 := bbase (se 5 (by rfl) ⟨159797, by rfl⟩ : syracuseStep 3409013 = 319595) (by norm_num)
theorem B2272675 : Blo 2019435 2272675 := bstep (se 1 (by rfl) ⟨1704506, by rfl⟩ : syracuseStep 2272675 = 3409013) B3409013
theorem B3030233 : Blo 2019435 3030233 := bstep (se 2 (by rfl) ⟨1136337, by rfl⟩ : syracuseStep 3030233 = 2272675) B2272675
theorem B2020155 : Blo 2019435 2020155 := bstep (se 1 (by rfl) ⟨1515116, by rfl⟩ : syracuseStep 2020155 = 3030233) B3030233
theorem B4314541 : Blo 2019435 4314541 := bbase (se 3 (by rfl) ⟨808976, by rfl⟩ : syracuseStep 4314541 = 1617953) (by norm_num)
theorem B5752721 : Blo 2019435 5752721 := bstep (se 2 (by rfl) ⟨2157270, by rfl⟩ : syracuseStep 5752721 = 4314541) B4314541
theorem B15340589 : Blo 2019435 15340589 := bstep (se 3 (by rfl) ⟨2876360, by rfl⟩ : syracuseStep 15340589 = 5752721) B5752721
theorem B10227059 : Blo 2019435 10227059 := bstep (se 1 (by rfl) ⟨7670294, by rfl⟩ : syracuseStep 10227059 = 15340589) B15340589
theorem B6818039 : Blo 2019435 6818039 := bstep (se 1 (by rfl) ⟨5113529, by rfl⟩ : syracuseStep 6818039 = 10227059) B10227059
theorem B4545359 : Blo 2019435 4545359 := bstep (se 1 (by rfl) ⟨3409019, by rfl⟩ : syracuseStep 4545359 = 6818039) B6818039
theorem B3030239 : Blo 2019435 3030239 := bstep (se 1 (by rfl) ⟨2272679, by rfl⟩ : syracuseStep 3030239 = 4545359) B4545359
theorem B2020159 : Blo 2019435 2020159 := bstep (se 1 (by rfl) ⟨1515119, by rfl⟩ : syracuseStep 2020159 = 3030239) B3030239
theorem B3030245 : Blo 2019435 3030245 := bbase (se 4 (by rfl) ⟨284085, by rfl⟩ : syracuseStep 3030245 = 568171) (by norm_num)
theorem B2020163 : Blo 2019435 2020163 := bstep (se 1 (by rfl) ⟨1515122, by rfl⟩ : syracuseStep 2020163 = 3030245) B3030245
theorem B3280069 : Blo 2019435 3280069 := bbase (se 4 (by rfl) ⟨307506, by rfl⟩ : syracuseStep 3280069 = 615013) (by norm_num)
theorem B4373425 : Blo 2019435 4373425 := bstep (se 2 (by rfl) ⟨1640034, by rfl⟩ : syracuseStep 4373425 = 3280069) B3280069
theorem B5831233 : Blo 2019435 5831233 := bstep (se 2 (by rfl) ⟨2186712, by rfl⟩ : syracuseStep 5831233 = 4373425) B4373425
theorem B124399637 : Blo 2019435 124399637 := bstep (se 6 (by rfl) ⟨2915616, by rfl⟩ : syracuseStep 124399637 = 5831233) B5831233
theorem B82933091 : Blo 2019435 82933091 := bstep (se 1 (by rfl) ⟨62199818, by rfl⟩ : syracuseStep 82933091 = 124399637) B124399637
theorem B55288727 : Blo 2019435 55288727 := bstep (se 1 (by rfl) ⟨41466545, by rfl⟩ : syracuseStep 55288727 = 82933091) B82933091
theorem B36859151 : Blo 2019435 36859151 := bstep (se 1 (by rfl) ⟨27644363, by rfl⟩ : syracuseStep 36859151 = 55288727) B55288727
theorem B24572767 : Blo 2019435 24572767 := bstep (se 1 (by rfl) ⟨18429575, by rfl⟩ : syracuseStep 24572767 = 36859151) B36859151
theorem B32763689 : Blo 2019435 32763689 := bstep (se 2 (by rfl) ⟨12286383, by rfl⟩ : syracuseStep 32763689 = 24572767) B24572767
theorem B21842459 : Blo 2019435 21842459 := bstep (se 1 (by rfl) ⟨16381844, by rfl⟩ : syracuseStep 21842459 = 32763689) B32763689
theorem B14561639 : Blo 2019435 14561639 := bstep (se 1 (by rfl) ⟨10921229, by rfl⟩ : syracuseStep 14561639 = 21842459) B21842459
theorem B9707759 : Blo 2019435 9707759 := bstep (se 1 (by rfl) ⟨7280819, by rfl⟩ : syracuseStep 9707759 = 14561639) B14561639
theorem B6471839 : Blo 2019435 6471839 := bstep (se 1 (by rfl) ⟨4853879, by rfl⟩ : syracuseStep 6471839 = 9707759) B9707759
theorem B4314559 : Blo 2019435 4314559 := bstep (se 1 (by rfl) ⟨3235919, by rfl⟩ : syracuseStep 4314559 = 6471839) B6471839
theorem B5752745 : Blo 2019435 5752745 := bstep (se 2 (by rfl) ⟨2157279, by rfl⟩ : syracuseStep 5752745 = 4314559) B4314559
theorem B3835163 : Blo 2019435 3835163 := bstep (se 1 (by rfl) ⟨2876372, by rfl⟩ : syracuseStep 3835163 = 5752745) B5752745
theorem B2556775 : Blo 2019435 2556775 := bstep (se 1 (by rfl) ⟨1917581, by rfl⟩ : syracuseStep 2556775 = 3835163) B3835163
theorem B3409033 : Blo 2019435 3409033 := bstep (se 2 (by rfl) ⟨1278387, by rfl⟩ : syracuseStep 3409033 = 2556775) B2556775
theorem B4545377 : Blo 2019435 4545377 := bstep (se 2 (by rfl) ⟨1704516, by rfl⟩ : syracuseStep 4545377 = 3409033) B3409033
theorem B3030251 : Blo 2019435 3030251 := bstep (se 1 (by rfl) ⟨2272688, by rfl⟩ : syracuseStep 3030251 = 4545377) B4545377
theorem B2020167 : Blo 2019435 2020167 := bstep (se 1 (by rfl) ⟨1515125, by rfl⟩ : syracuseStep 2020167 = 3030251) B3030251
theorem B2272693 : Blo 2019435 2272693 := bbase (se 5 (by rfl) ⟨106532, by rfl⟩ : syracuseStep 2272693 = 213065) (by norm_num)
theorem B3030257 : Blo 2019435 3030257 := bstep (se 2 (by rfl) ⟨1136346, by rfl⟩ : syracuseStep 3030257 = 2272693) B2272693
theorem B2020171 : Blo 2019435 2020171 := bstep (se 1 (by rfl) ⟨1515128, by rfl⟩ : syracuseStep 2020171 = 3030257) B3030257
theorem B2556785 : Blo 2019435 2556785 := bbase (se 2 (by rfl) ⟨958794, by rfl⟩ : syracuseStep 2556785 = 1917589) (by norm_num)
theorem B6818093 : Blo 2019435 6818093 := bstep (se 3 (by rfl) ⟨1278392, by rfl⟩ : syracuseStep 6818093 = 2556785) B2556785
theorem B4545395 : Blo 2019435 4545395 := bstep (se 1 (by rfl) ⟨3409046, by rfl⟩ : syracuseStep 4545395 = 6818093) B6818093
theorem B3030263 : Blo 2019435 3030263 := bstep (se 1 (by rfl) ⟨2272697, by rfl⟩ : syracuseStep 3030263 = 4545395) B4545395
theorem B2020175 : Blo 2019435 2020175 := bstep (se 1 (by rfl) ⟨1515131, by rfl⟩ : syracuseStep 2020175 = 3030263) B3030263
theorem B3030269 : Blo 2019435 3030269 := bbase (se 3 (by rfl) ⟨568175, by rfl⟩ : syracuseStep 3030269 = 1136351) (by norm_num)
theorem B2020179 : Blo 2019435 2020179 := bstep (se 1 (by rfl) ⟨1515134, by rfl⟩ : syracuseStep 2020179 = 3030269) B3030269
theorem B4545413 : Blo 2019435 4545413 := bbase (se 4 (by rfl) ⟨426132, by rfl⟩ : syracuseStep 4545413 = 852265) (by norm_num)
theorem B3030275 : Blo 2019435 3030275 := bstep (se 1 (by rfl) ⟨2272706, by rfl⟩ : syracuseStep 3030275 = 4545413) B4545413
theorem B2020183 : Blo 2019435 2020183 := bstep (se 1 (by rfl) ⟨1515137, by rfl⟩ : syracuseStep 2020183 = 3030275) B3030275
theorem B2157301 : Blo 2019435 2157301 := bbase (se 5 (by rfl) ⟨101123, by rfl⟩ : syracuseStep 2157301 = 202247) (by norm_num)
theorem B2876401 : Blo 2019435 2876401 := bstep (se 2 (by rfl) ⟨1078650, by rfl⟩ : syracuseStep 2876401 = 2157301) B2157301
theorem B3835201 : Blo 2019435 3835201 := bstep (se 2 (by rfl) ⟨1438200, by rfl⟩ : syracuseStep 3835201 = 2876401) B2876401
theorem B5113601 : Blo 2019435 5113601 := bstep (se 2 (by rfl) ⟨1917600, by rfl⟩ : syracuseStep 5113601 = 3835201) B3835201
theorem B3409067 : Blo 2019435 3409067 := bstep (se 1 (by rfl) ⟨2556800, by rfl⟩ : syracuseStep 3409067 = 5113601) B5113601
theorem B2272711 : Blo 2019435 2272711 := bstep (se 1 (by rfl) ⟨1704533, by rfl⟩ : syracuseStep 2272711 = 3409067) B3409067
theorem B3030281 : Blo 2019435 3030281 := bstep (se 2 (by rfl) ⟨1136355, by rfl⟩ : syracuseStep 3030281 = 2272711) B2272711
theorem B2020187 : Blo 2019435 2020187 := bstep (se 1 (by rfl) ⟨1515140, by rfl⟩ : syracuseStep 2020187 = 3030281) B3030281
theorem B10227221 : Blo 2019435 10227221 := bbase (se 6 (by rfl) ⟨239700, by rfl⟩ : syracuseStep 10227221 = 479401) (by norm_num)
theorem B6818147 : Blo 2019435 6818147 := bstep (se 1 (by rfl) ⟨5113610, by rfl⟩ : syracuseStep 6818147 = 10227221) B10227221
theorem B4545431 : Blo 2019435 4545431 := bstep (se 1 (by rfl) ⟨3409073, by rfl⟩ : syracuseStep 4545431 = 6818147) B6818147
theorem B3030287 : Blo 2019435 3030287 := bstep (se 1 (by rfl) ⟨2272715, by rfl⟩ : syracuseStep 3030287 = 4545431) B4545431
theorem B2020191 : Blo 2019435 2020191 := bstep (se 1 (by rfl) ⟨1515143, by rfl⟩ : syracuseStep 2020191 = 3030287) B3030287
theorem B3030293 : Blo 2019435 3030293 := bbase (se 6 (by rfl) ⟨71022, by rfl⟩ : syracuseStep 3030293 = 142045) (by norm_num)
theorem B2020195 : Blo 2019435 2020195 := bstep (se 1 (by rfl) ⟨1515146, by rfl⟩ : syracuseStep 2020195 = 3030293) B3030293
theorem B7280933 : Blo 2019435 7280933 := bbase (se 4 (by rfl) ⟨682587, by rfl⟩ : syracuseStep 7280933 = 1365175) (by norm_num)
theorem B19415821 : Blo 2019435 19415821 := bstep (se 3 (by rfl) ⟨3640466, by rfl⟩ : syracuseStep 19415821 = 7280933) B7280933
theorem B25887761 : Blo 2019435 25887761 := bstep (se 2 (by rfl) ⟨9707910, by rfl⟩ : syracuseStep 25887761 = 19415821) B19415821
theorem B17258507 : Blo 2019435 17258507 := bstep (se 1 (by rfl) ⟨12943880, by rfl⟩ : syracuseStep 17258507 = 25887761) B25887761
theorem B11505671 : Blo 2019435 11505671 := bstep (se 1 (by rfl) ⟨8629253, by rfl⟩ : syracuseStep 11505671 = 17258507) B17258507
theorem B7670447 : Blo 2019435 7670447 := bstep (se 1 (by rfl) ⟨5752835, by rfl⟩ : syracuseStep 7670447 = 11505671) B11505671
theorem B5113631 : Blo 2019435 5113631 := bstep (se 1 (by rfl) ⟨3835223, by rfl⟩ : syracuseStep 5113631 = 7670447) B7670447
theorem B3409087 : Blo 2019435 3409087 := bstep (se 1 (by rfl) ⟨2556815, by rfl⟩ : syracuseStep 3409087 = 5113631) B5113631
theorem B4545449 : Blo 2019435 4545449 := bstep (se 2 (by rfl) ⟨1704543, by rfl⟩ : syracuseStep 4545449 = 3409087) B3409087
theorem B3030299 : Blo 2019435 3030299 := bstep (se 1 (by rfl) ⟨2272724, by rfl⟩ : syracuseStep 3030299 = 4545449) B4545449
theorem B2020199 : Blo 2019435 2020199 := bstep (se 1 (by rfl) ⟨1515149, by rfl⟩ : syracuseStep 2020199 = 3030299) B3030299
theorem B2272729 : Blo 2019435 2272729 := bbase (se 2 (by rfl) ⟨852273, by rfl⟩ : syracuseStep 2272729 = 1704547) (by norm_num)
theorem B3030305 : Blo 2019435 3030305 := bstep (se 2 (by rfl) ⟨1136364, by rfl⟩ : syracuseStep 3030305 = 2272729) B2272729
theorem B2020203 : Blo 2019435 2020203 := bstep (se 1 (by rfl) ⟨1515152, by rfl⟩ : syracuseStep 2020203 = 3030305) B3030305
theorem B2876429 : Blo 2019435 2876429 := bbase (se 3 (by rfl) ⟨539330, by rfl⟩ : syracuseStep 2876429 = 1078661) (by norm_num)
theorem B7670477 : Blo 2019435 7670477 := bstep (se 3 (by rfl) ⟨1438214, by rfl⟩ : syracuseStep 7670477 = 2876429) B2876429
theorem B5113651 : Blo 2019435 5113651 := bstep (se 1 (by rfl) ⟨3835238, by rfl⟩ : syracuseStep 5113651 = 7670477) B7670477
theorem B6818201 : Blo 2019435 6818201 := bstep (se 2 (by rfl) ⟨2556825, by rfl⟩ : syracuseStep 6818201 = 5113651) B5113651
theorem B4545467 : Blo 2019435 4545467 := bstep (se 1 (by rfl) ⟨3409100, by rfl⟩ : syracuseStep 4545467 = 6818201) B6818201
theorem B3030311 : Blo 2019435 3030311 := bstep (se 1 (by rfl) ⟨2272733, by rfl⟩ : syracuseStep 3030311 = 4545467) B4545467
theorem B2020207 : Blo 2019435 2020207 := bstep (se 1 (by rfl) ⟨1515155, by rfl⟩ : syracuseStep 2020207 = 3030311) B3030311
theorem B3030317 : Blo 2019435 3030317 := bbase (se 3 (by rfl) ⟨568184, by rfl⟩ : syracuseStep 3030317 = 1136369) (by norm_num)
theorem B2020211 : Blo 2019435 2020211 := bstep (se 1 (by rfl) ⟨1515158, by rfl⟩ : syracuseStep 2020211 = 3030317) B3030317
theorem B4545485 : Blo 2019435 4545485 := bbase (se 3 (by rfl) ⟨852278, by rfl⟩ : syracuseStep 4545485 = 1704557) (by norm_num)
theorem B3030323 : Blo 2019435 3030323 := bstep (se 1 (by rfl) ⟨2272742, by rfl⟩ : syracuseStep 3030323 = 4545485) B4545485
theorem B2020215 : Blo 2019435 2020215 := bstep (se 1 (by rfl) ⟨1515161, by rfl⟩ : syracuseStep 2020215 = 3030323) B3030323
theorem B2556841 : Blo 2019435 2556841 := bbase (se 2 (by rfl) ⟨958815, by rfl⟩ : syracuseStep 2556841 = 1917631) (by norm_num)
theorem B3409121 : Blo 2019435 3409121 := bstep (se 2 (by rfl) ⟨1278420, by rfl⟩ : syracuseStep 3409121 = 2556841) B2556841
theorem B2272747 : Blo 2019435 2272747 := bstep (se 1 (by rfl) ⟨1704560, by rfl⟩ : syracuseStep 2272747 = 3409121) B3409121
theorem B3030329 : Blo 2019435 3030329 := bstep (se 2 (by rfl) ⟨1136373, by rfl⟩ : syracuseStep 3030329 = 2272747) B2272747
theorem B2020219 : Blo 2019435 2020219 := bstep (se 1 (by rfl) ⟨1515164, by rfl⟩ : syracuseStep 2020219 = 3030329) B3030329
theorem B5183461 : Blo 2019435 5183461 := bbase (se 4 (by rfl) ⟨485949, by rfl⟩ : syracuseStep 5183461 = 971899) (by norm_num)
theorem B6911281 : Blo 2019435 6911281 := bstep (se 2 (by rfl) ⟨2591730, by rfl⟩ : syracuseStep 6911281 = 5183461) B5183461
theorem B9215041 : Blo 2019435 9215041 := bstep (se 2 (by rfl) ⟨3455640, by rfl⟩ : syracuseStep 9215041 = 6911281) B6911281
theorem B12286721 : Blo 2019435 12286721 := bstep (se 2 (by rfl) ⟨4607520, by rfl⟩ : syracuseStep 12286721 = 9215041) B9215041
theorem B8191147 : Blo 2019435 8191147 := bstep (se 1 (by rfl) ⟨6143360, by rfl⟩ : syracuseStep 8191147 = 12286721) B12286721
theorem B10921529 : Blo 2019435 10921529 := bstep (se 2 (by rfl) ⟨4095573, by rfl⟩ : syracuseStep 10921529 = 8191147) B8191147
theorem B7281019 : Blo 2019435 7281019 := bstep (se 1 (by rfl) ⟨5460764, by rfl⟩ : syracuseStep 7281019 = 10921529) B10921529
theorem B9708025 : Blo 2019435 9708025 := bstep (se 2 (by rfl) ⟨3640509, by rfl⟩ : syracuseStep 9708025 = 7281019) B7281019
theorem B12944033 : Blo 2019435 12944033 := bstep (se 2 (by rfl) ⟨4854012, by rfl⟩ : syracuseStep 12944033 = 9708025) B9708025
theorem B8629355 : Blo 2019435 8629355 := bstep (se 1 (by rfl) ⟨6472016, by rfl⟩ : syracuseStep 8629355 = 12944033) B12944033
theorem B23011613 : Blo 2019435 23011613 := bstep (se 3 (by rfl) ⟨4314677, by rfl⟩ : syracuseStep 23011613 = 8629355) B8629355
theorem B15341075 : Blo 2019435 15341075 := bstep (se 1 (by rfl) ⟨11505806, by rfl⟩ : syracuseStep 15341075 = 23011613) B23011613
theorem B10227383 : Blo 2019435 10227383 := bstep (se 1 (by rfl) ⟨7670537, by rfl⟩ : syracuseStep 10227383 = 15341075) B15341075
theorem B6818255 : Blo 2019435 6818255 := bstep (se 1 (by rfl) ⟨5113691, by rfl⟩ : syracuseStep 6818255 = 10227383) B10227383
theorem B4545503 : Blo 2019435 4545503 := bstep (se 1 (by rfl) ⟨3409127, by rfl⟩ : syracuseStep 4545503 = 6818255) B6818255
theorem B3030335 : Blo 2019435 3030335 := bstep (se 1 (by rfl) ⟨2272751, by rfl⟩ : syracuseStep 3030335 = 4545503) B4545503
theorem B2020223 : Blo 2019435 2020223 := bstep (se 1 (by rfl) ⟨1515167, by rfl⟩ : syracuseStep 2020223 = 3030335) B3030335
theorem B3030341 : Blo 2019435 3030341 := bbase (se 4 (by rfl) ⟨284094, by rfl⟩ : syracuseStep 3030341 = 568189) (by norm_num)
theorem B2020227 : Blo 2019435 2020227 := bstep (se 1 (by rfl) ⟨1515170, by rfl⟩ : syracuseStep 2020227 = 3030341) B3030341
theorem B3409141 : Blo 2019435 3409141 := bbase (se 5 (by rfl) ⟨159803, by rfl⟩ : syracuseStep 3409141 = 319607) (by norm_num)
theorem B4545521 : Blo 2019435 4545521 := bstep (se 2 (by rfl) ⟨1704570, by rfl⟩ : syracuseStep 4545521 = 3409141) B3409141
theorem B3030347 : Blo 2019435 3030347 := bstep (se 1 (by rfl) ⟨2272760, by rfl⟩ : syracuseStep 3030347 = 4545521) B4545521
theorem B2020231 : Blo 2019435 2020231 := bstep (se 1 (by rfl) ⟨1515173, by rfl⟩ : syracuseStep 2020231 = 3030347) B3030347
theorem B2272765 : Blo 2019435 2272765 := bbase (se 3 (by rfl) ⟨426143, by rfl⟩ : syracuseStep 2272765 = 852287) (by norm_num)
theorem B3030353 : Blo 2019435 3030353 := bstep (se 2 (by rfl) ⟨1136382, by rfl⟩ : syracuseStep 3030353 = 2272765) B2272765
theorem B2020235 : Blo 2019435 2020235 := bstep (se 1 (by rfl) ⟨1515176, by rfl⟩ : syracuseStep 2020235 = 3030353) B3030353
theorem B6818309 : Blo 2019435 6818309 := bbase (se 4 (by rfl) ⟨639216, by rfl⟩ : syracuseStep 6818309 = 1278433) (by norm_num)
theorem B4545539 : Blo 2019435 4545539 := bstep (se 1 (by rfl) ⟨3409154, by rfl⟩ : syracuseStep 4545539 = 6818309) B6818309
theorem B3030359 : Blo 2019435 3030359 := bstep (se 1 (by rfl) ⟨2272769, by rfl⟩ : syracuseStep 3030359 = 4545539) B4545539
theorem B2020239 : Blo 2019435 2020239 := bstep (se 1 (by rfl) ⟨1515179, by rfl⟩ : syracuseStep 2020239 = 3030359) B3030359
theorem B3030365 : Blo 2019435 3030365 := bbase (se 3 (by rfl) ⟨568193, by rfl⟩ : syracuseStep 3030365 = 1136387) (by norm_num)
theorem B2020243 : Blo 2019435 2020243 := bstep (se 1 (by rfl) ⟨1515182, by rfl⟩ : syracuseStep 2020243 = 3030365) B3030365
theorem B4545557 : Blo 2019435 4545557 := bbase (se 6 (by rfl) ⟨106536, by rfl⟩ : syracuseStep 4545557 = 213073) (by norm_num)
theorem B3030371 : Blo 2019435 3030371 := bstep (se 1 (by rfl) ⟨2272778, by rfl⟩ : syracuseStep 3030371 = 4545557) B4545557
theorem B2020247 : Blo 2019435 2020247 := bstep (se 1 (by rfl) ⟨1515185, by rfl⟩ : syracuseStep 2020247 = 3030371) B3030371
theorem B7670645 : Blo 2019435 7670645 := bbase (se 5 (by rfl) ⟨359561, by rfl⟩ : syracuseStep 7670645 = 719123) (by norm_num)
theorem B5113763 : Blo 2019435 5113763 := bstep (se 1 (by rfl) ⟨3835322, by rfl⟩ : syracuseStep 5113763 = 7670645) B7670645
theorem B3409175 : Blo 2019435 3409175 := bstep (se 1 (by rfl) ⟨2556881, by rfl⟩ : syracuseStep 3409175 = 5113763) B5113763
theorem B2272783 : Blo 2019435 2272783 := bstep (se 1 (by rfl) ⟨1704587, by rfl⟩ : syracuseStep 2272783 = 3409175) B3409175
theorem B3030377 : Blo 2019435 3030377 := bstep (se 2 (by rfl) ⟨1136391, by rfl⟩ : syracuseStep 3030377 = 2272783) B2272783
theorem B2020251 : Blo 2019435 2020251 := bstep (se 1 (by rfl) ⟨1515188, by rfl⟩ : syracuseStep 2020251 = 3030377) B3030377
theorem B2157373 : Blo 2019435 2157373 := bbase (se 3 (by rfl) ⟨404507, by rfl⟩ : syracuseStep 2157373 = 809015) (by norm_num)
theorem B11505989 : Blo 2019435 11505989 := bstep (se 4 (by rfl) ⟨1078686, by rfl⟩ : syracuseStep 11505989 = 2157373) B2157373
theorem B7670659 : Blo 2019435 7670659 := bstep (se 1 (by rfl) ⟨5752994, by rfl⟩ : syracuseStep 7670659 = 11505989) B11505989
theorem B10227545 : Blo 2019435 10227545 := bstep (se 2 (by rfl) ⟨3835329, by rfl⟩ : syracuseStep 10227545 = 7670659) B7670659
theorem B6818363 : Blo 2019435 6818363 := bstep (se 1 (by rfl) ⟨5113772, by rfl⟩ : syracuseStep 6818363 = 10227545) B10227545
theorem B4545575 : Blo 2019435 4545575 := bstep (se 1 (by rfl) ⟨3409181, by rfl⟩ : syracuseStep 4545575 = 6818363) B6818363
theorem B3030383 : Blo 2019435 3030383 := bstep (se 1 (by rfl) ⟨2272787, by rfl⟩ : syracuseStep 3030383 = 4545575) B4545575
theorem B2020255 : Blo 2019435 2020255 := bstep (se 1 (by rfl) ⟨1515191, by rfl⟩ : syracuseStep 2020255 = 3030383) B3030383
theorem B3030389 : Blo 2019435 3030389 := bbase (se 5 (by rfl) ⟨142049, by rfl⟩ : syracuseStep 3030389 = 284099) (by norm_num)
theorem B2020259 : Blo 2019435 2020259 := bstep (se 1 (by rfl) ⟨1515194, by rfl⟩ : syracuseStep 2020259 = 3030389) B3030389
theorem B2876509 : Blo 2019435 2876509 := bbase (se 3 (by rfl) ⟨539345, by rfl⟩ : syracuseStep 2876509 = 1078691) (by norm_num)
theorem B3835345 : Blo 2019435 3835345 := bstep (se 2 (by rfl) ⟨1438254, by rfl⟩ : syracuseStep 3835345 = 2876509) B2876509
theorem B5113793 : Blo 2019435 5113793 := bstep (se 2 (by rfl) ⟨1917672, by rfl⟩ : syracuseStep 5113793 = 3835345) B3835345
theorem B3409195 : Blo 2019435 3409195 := bstep (se 1 (by rfl) ⟨2556896, by rfl⟩ : syracuseStep 3409195 = 5113793) B5113793
theorem B4545593 : Blo 2019435 4545593 := bstep (se 2 (by rfl) ⟨1704597, by rfl⟩ : syracuseStep 4545593 = 3409195) B3409195
theorem B3030395 : Blo 2019435 3030395 := bstep (se 1 (by rfl) ⟨2272796, by rfl⟩ : syracuseStep 3030395 = 4545593) B4545593
theorem B2020263 : Blo 2019435 2020263 := bstep (se 1 (by rfl) ⟨1515197, by rfl⟩ : syracuseStep 2020263 = 3030395) B3030395
theorem B2272801 : Blo 2019435 2272801 := bbase (se 2 (by rfl) ⟨852300, by rfl⟩ : syracuseStep 2272801 = 1704601) (by norm_num)
theorem B3030401 : Blo 2019435 3030401 := bstep (se 2 (by rfl) ⟨1136400, by rfl⟩ : syracuseStep 3030401 = 2272801) B2272801
theorem B2020267 : Blo 2019435 2020267 := bstep (se 1 (by rfl) ⟨1515200, by rfl⟩ : syracuseStep 2020267 = 3030401) B3030401
theorem B5113813 : Blo 2019435 5113813 := bbase (se 7 (by rfl) ⟨59927, by rfl⟩ : syracuseStep 5113813 = 119855) (by norm_num)
theorem B6818417 : Blo 2019435 6818417 := bstep (se 2 (by rfl) ⟨2556906, by rfl⟩ : syracuseStep 6818417 = 5113813) B5113813
theorem B4545611 : Blo 2019435 4545611 := bstep (se 1 (by rfl) ⟨3409208, by rfl⟩ : syracuseStep 4545611 = 6818417) B6818417
theorem B3030407 : Blo 2019435 3030407 := bstep (se 1 (by rfl) ⟨2272805, by rfl⟩ : syracuseStep 3030407 = 4545611) B4545611
theorem B2020271 : Blo 2019435 2020271 := bstep (se 1 (by rfl) ⟨1515203, by rfl⟩ : syracuseStep 2020271 = 3030407) B3030407
theorem B3030413 : Blo 2019435 3030413 := bbase (se 3 (by rfl) ⟨568202, by rfl⟩ : syracuseStep 3030413 = 1136405) (by norm_num)
theorem B2020275 : Blo 2019435 2020275 := bstep (se 1 (by rfl) ⟨1515206, by rfl⟩ : syracuseStep 2020275 = 3030413) B3030413
theorem B4545629 : Blo 2019435 4545629 := bbase (se 3 (by rfl) ⟨852305, by rfl⟩ : syracuseStep 4545629 = 1704611) (by norm_num)
theorem B3030419 : Blo 2019435 3030419 := bstep (se 1 (by rfl) ⟨2272814, by rfl⟩ : syracuseStep 3030419 = 4545629) B4545629
theorem B2020279 : Blo 2019435 2020279 := bstep (se 1 (by rfl) ⟨1515209, by rfl⟩ : syracuseStep 2020279 = 3030419) B3030419
theorem B3409229 : Blo 2019435 3409229 := bbase (se 3 (by rfl) ⟨639230, by rfl⟩ : syracuseStep 3409229 = 1278461) (by norm_num)
theorem B2272819 : Blo 2019435 2272819 := bstep (se 1 (by rfl) ⟨1704614, by rfl⟩ : syracuseStep 2272819 = 3409229) B3409229
theorem B3030425 : Blo 2019435 3030425 := bstep (se 2 (by rfl) ⟨1136409, by rfl⟩ : syracuseStep 3030425 = 2272819) B2272819
theorem B2020283 : Blo 2019435 2020283 := bstep (se 1 (by rfl) ⟨1515212, by rfl⟩ : syracuseStep 2020283 = 3030425) B3030425
theorem B9215333 : Blo 2019435 9215333 := bbase (se 4 (by rfl) ⟨863937, by rfl⟩ : syracuseStep 9215333 = 1727875) (by norm_num)
theorem B6143555 : Blo 2019435 6143555 := bstep (se 1 (by rfl) ⟨4607666, by rfl⟩ : syracuseStep 6143555 = 9215333) B9215333
theorem B4095703 : Blo 2019435 4095703 := bstep (se 1 (by rfl) ⟨3071777, by rfl⟩ : syracuseStep 4095703 = 6143555) B6143555
theorem B21843749 : Blo 2019435 21843749 := bstep (se 4 (by rfl) ⟨2047851, by rfl⟩ : syracuseStep 21843749 = 4095703) B4095703
theorem B14562499 : Blo 2019435 14562499 := bstep (se 1 (by rfl) ⟨10921874, by rfl⟩ : syracuseStep 14562499 = 21843749) B21843749
theorem B19416665 : Blo 2019435 19416665 := bstep (se 2 (by rfl) ⟨7281249, by rfl⟩ : syracuseStep 19416665 = 14562499) B14562499
theorem B12944443 : Blo 2019435 12944443 := bstep (se 1 (by rfl) ⟨9708332, by rfl⟩ : syracuseStep 12944443 = 19416665) B19416665
theorem B17259257 : Blo 2019435 17259257 := bstep (se 2 (by rfl) ⟨6472221, by rfl⟩ : syracuseStep 17259257 = 12944443) B12944443
theorem B11506171 : Blo 2019435 11506171 := bstep (se 1 (by rfl) ⟨8629628, by rfl⟩ : syracuseStep 11506171 = 17259257) B17259257
theorem B15341561 : Blo 2019435 15341561 := bstep (se 2 (by rfl) ⟨5753085, by rfl⟩ : syracuseStep 15341561 = 11506171) B11506171
theorem B10227707 : Blo 2019435 10227707 := bstep (se 1 (by rfl) ⟨7670780, by rfl⟩ : syracuseStep 10227707 = 15341561) B15341561
theorem B6818471 : Blo 2019435 6818471 := bstep (se 1 (by rfl) ⟨5113853, by rfl⟩ : syracuseStep 6818471 = 10227707) B10227707
theorem B4545647 : Blo 2019435 4545647 := bstep (se 1 (by rfl) ⟨3409235, by rfl⟩ : syracuseStep 4545647 = 6818471) B6818471
theorem B3030431 : Blo 2019435 3030431 := bstep (se 1 (by rfl) ⟨2272823, by rfl⟩ : syracuseStep 3030431 = 4545647) B4545647
theorem B2020287 : Blo 2019435 2020287 := bstep (se 1 (by rfl) ⟨1515215, by rfl⟩ : syracuseStep 2020287 = 3030431) B3030431
theorem B3030437 : Blo 2019435 3030437 := bbase (se 4 (by rfl) ⟨284103, by rfl⟩ : syracuseStep 3030437 = 568207) (by norm_num)
theorem B2020291 : Blo 2019435 2020291 := bstep (se 1 (by rfl) ⟨1515218, by rfl⟩ : syracuseStep 2020291 = 3030437) B3030437
theorem B2556937 : Blo 2019435 2556937 := bbase (se 2 (by rfl) ⟨958851, by rfl⟩ : syracuseStep 2556937 = 1917703) (by norm_num)
theorem B3409249 : Blo 2019435 3409249 := bstep (se 2 (by rfl) ⟨1278468, by rfl⟩ : syracuseStep 3409249 = 2556937) B2556937
theorem B4545665 : Blo 2019435 4545665 := bstep (se 2 (by rfl) ⟨1704624, by rfl⟩ : syracuseStep 4545665 = 3409249) B3409249
theorem B3030443 : Blo 2019435 3030443 := bstep (se 1 (by rfl) ⟨2272832, by rfl⟩ : syracuseStep 3030443 = 4545665) B4545665
theorem B2020295 : Blo 2019435 2020295 := bstep (se 1 (by rfl) ⟨1515221, by rfl⟩ : syracuseStep 2020295 = 3030443) B3030443
theorem B2272837 : Blo 2019435 2272837 := bbase (se 4 (by rfl) ⟨213078, by rfl⟩ : syracuseStep 2272837 = 426157) (by norm_num)
theorem B3030449 : Blo 2019435 3030449 := bstep (se 2 (by rfl) ⟨1136418, by rfl⟩ : syracuseStep 3030449 = 2272837) B2272837
theorem B2020299 : Blo 2019435 2020299 := bstep (se 1 (by rfl) ⟨1515224, by rfl⟩ : syracuseStep 2020299 = 3030449) B3030449
theorem B3835421 : Blo 2019435 3835421 := bbase (se 3 (by rfl) ⟨719141, by rfl⟩ : syracuseStep 3835421 = 1438283) (by norm_num)
theorem B2556947 : Blo 2019435 2556947 := bstep (se 1 (by rfl) ⟨1917710, by rfl⟩ : syracuseStep 2556947 = 3835421) B3835421
theorem B6818525 : Blo 2019435 6818525 := bstep (se 3 (by rfl) ⟨1278473, by rfl⟩ : syracuseStep 6818525 = 2556947) B2556947
theorem B4545683 : Blo 2019435 4545683 := bstep (se 1 (by rfl) ⟨3409262, by rfl⟩ : syracuseStep 4545683 = 6818525) B6818525
theorem B3030455 : Blo 2019435 3030455 := bstep (se 1 (by rfl) ⟨2272841, by rfl⟩ : syracuseStep 3030455 = 4545683) B4545683
theorem B2020303 : Blo 2019435 2020303 := bstep (se 1 (by rfl) ⟨1515227, by rfl⟩ : syracuseStep 2020303 = 3030455) B3030455
theorem B3030461 : Blo 2019435 3030461 := bbase (se 3 (by rfl) ⟨568211, by rfl⟩ : syracuseStep 3030461 = 1136423) (by norm_num)
theorem B2020307 : Blo 2019435 2020307 := bstep (se 1 (by rfl) ⟨1515230, by rfl⟩ : syracuseStep 2020307 = 3030461) B3030461
theorem B4545701 : Blo 2019435 4545701 := bbase (se 4 (by rfl) ⟨426159, by rfl⟩ : syracuseStep 4545701 = 852319) (by norm_num)
theorem B3030467 : Blo 2019435 3030467 := bstep (se 1 (by rfl) ⟨2272850, by rfl⟩ : syracuseStep 3030467 = 4545701) B4545701
theorem B2020311 : Blo 2019435 2020311 := bstep (se 1 (by rfl) ⟨1515233, by rfl⟩ : syracuseStep 2020311 = 3030467) B3030467
theorem B5113925 : Blo 2019435 5113925 := bbase (se 4 (by rfl) ⟨479430, by rfl⟩ : syracuseStep 5113925 = 958861) (by norm_num)
theorem B3409283 : Blo 2019435 3409283 := bstep (se 1 (by rfl) ⟨2556962, by rfl⟩ : syracuseStep 3409283 = 5113925) B5113925
theorem B2272855 : Blo 2019435 2272855 := bstep (se 1 (by rfl) ⟨1704641, by rfl⟩ : syracuseStep 2272855 = 3409283) B3409283
theorem B3030473 : Blo 2019435 3030473 := bstep (se 2 (by rfl) ⟨1136427, by rfl⟩ : syracuseStep 3030473 = 2272855) B2272855
theorem B2020315 : Blo 2019435 2020315 := bstep (se 1 (by rfl) ⟨1515236, by rfl⟩ : syracuseStep 2020315 = 3030473) B3030473
theorem B6472325 : Blo 2019435 6472325 := bbase (se 4 (by rfl) ⟨606780, by rfl⟩ : syracuseStep 6472325 = 1213561) (by norm_num)
theorem B4314883 : Blo 2019435 4314883 := bstep (se 1 (by rfl) ⟨3236162, by rfl⟩ : syracuseStep 4314883 = 6472325) B6472325
theorem B5753177 : Blo 2019435 5753177 := bstep (se 2 (by rfl) ⟨2157441, by rfl⟩ : syracuseStep 5753177 = 4314883) B4314883
theorem B3835451 : Blo 2019435 3835451 := bstep (se 1 (by rfl) ⟨2876588, by rfl⟩ : syracuseStep 3835451 = 5753177) B5753177
theorem B10227869 : Blo 2019435 10227869 := bstep (se 3 (by rfl) ⟨1917725, by rfl⟩ : syracuseStep 10227869 = 3835451) B3835451
theorem B6818579 : Blo 2019435 6818579 := bstep (se 1 (by rfl) ⟨5113934, by rfl⟩ : syracuseStep 6818579 = 10227869) B10227869
theorem B4545719 : Blo 2019435 4545719 := bstep (se 1 (by rfl) ⟨3409289, by rfl⟩ : syracuseStep 4545719 = 6818579) B6818579
theorem B3030479 : Blo 2019435 3030479 := bstep (se 1 (by rfl) ⟨2272859, by rfl⟩ : syracuseStep 3030479 = 4545719) B4545719
theorem B2020319 : Blo 2019435 2020319 := bstep (se 1 (by rfl) ⟨1515239, by rfl⟩ : syracuseStep 2020319 = 3030479) B3030479
theorem B3030485 : Blo 2019435 3030485 := bbase (se 7 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 3030485 = 71027) (by norm_num)
theorem B2020323 : Blo 2019435 2020323 := bstep (se 1 (by rfl) ⟨1515242, by rfl⟩ : syracuseStep 2020323 = 3030485) B3030485
theorem B7670933 : Blo 2019435 7670933 := bbase (se 6 (by rfl) ⟨179787, by rfl⟩ : syracuseStep 7670933 = 359575) (by norm_num)
theorem B5113955 : Blo 2019435 5113955 := bstep (se 1 (by rfl) ⟨3835466, by rfl⟩ : syracuseStep 5113955 = 7670933) B7670933
theorem B3409303 : Blo 2019435 3409303 := bstep (se 1 (by rfl) ⟨2556977, by rfl⟩ : syracuseStep 3409303 = 5113955) B5113955
theorem B4545737 : Blo 2019435 4545737 := bstep (se 2 (by rfl) ⟨1704651, by rfl⟩ : syracuseStep 4545737 = 3409303) B3409303
theorem B3030491 : Blo 2019435 3030491 := bstep (se 1 (by rfl) ⟨2272868, by rfl⟩ : syracuseStep 3030491 = 4545737) B4545737
theorem B2020327 : Blo 2019435 2020327 := bstep (se 1 (by rfl) ⟨1515245, by rfl⟩ : syracuseStep 2020327 = 3030491) B3030491
theorem B2272873 : Blo 2019435 2272873 := bbase (se 2 (by rfl) ⟨852327, by rfl⟩ : syracuseStep 2272873 = 1704655) (by norm_num)
theorem B3030497 : Blo 2019435 3030497 := bstep (se 2 (by rfl) ⟨1136436, by rfl⟩ : syracuseStep 3030497 = 2272873) B2272873
theorem B2020331 : Blo 2019435 2020331 := bstep (se 1 (by rfl) ⟨1515248, by rfl⟩ : syracuseStep 2020331 = 3030497) B3030497
theorem B4314917 : Blo 2019435 4314917 := bbase (se 4 (by rfl) ⟨404523, by rfl⟩ : syracuseStep 4314917 = 809047) (by norm_num)
theorem B11506445 : Blo 2019435 11506445 := bstep (se 3 (by rfl) ⟨2157458, by rfl⟩ : syracuseStep 11506445 = 4314917) B4314917
theorem B7670963 : Blo 2019435 7670963 := bstep (se 1 (by rfl) ⟨5753222, by rfl⟩ : syracuseStep 7670963 = 11506445) B11506445
theorem B5113975 : Blo 2019435 5113975 := bstep (se 1 (by rfl) ⟨3835481, by rfl⟩ : syracuseStep 5113975 = 7670963) B7670963
theorem B6818633 : Blo 2019435 6818633 := bstep (se 2 (by rfl) ⟨2556987, by rfl⟩ : syracuseStep 6818633 = 5113975) B5113975
theorem B4545755 : Blo 2019435 4545755 := bstep (se 1 (by rfl) ⟨3409316, by rfl⟩ : syracuseStep 4545755 = 6818633) B6818633
theorem B3030503 : Blo 2019435 3030503 := bstep (se 1 (by rfl) ⟨2272877, by rfl⟩ : syracuseStep 3030503 = 4545755) B4545755
theorem B2020335 : Blo 2019435 2020335 := bstep (se 1 (by rfl) ⟨1515251, by rfl⟩ : syracuseStep 2020335 = 3030503) B3030503
theorem B3030509 : Blo 2019435 3030509 := bbase (se 3 (by rfl) ⟨568220, by rfl⟩ : syracuseStep 3030509 = 1136441) (by norm_num)
theorem B2020339 : Blo 2019435 2020339 := bstep (se 1 (by rfl) ⟨1515254, by rfl⟩ : syracuseStep 2020339 = 3030509) B3030509
theorem B4545773 : Blo 2019435 4545773 := bbase (se 3 (by rfl) ⟨852332, by rfl⟩ : syracuseStep 4545773 = 1704665) (by norm_num)
theorem B3030515 : Blo 2019435 3030515 := bstep (se 1 (by rfl) ⟨2272886, by rfl⟩ : syracuseStep 3030515 = 4545773) B4545773
theorem B2020343 : Blo 2019435 2020343 := bstep (se 1 (by rfl) ⟨1515257, by rfl⟩ : syracuseStep 2020343 = 3030515) B3030515
theorem B2876629 : Blo 2019435 2876629 := bbase (se 7 (by rfl) ⟨33710, by rfl⟩ : syracuseStep 2876629 = 67421) (by norm_num)
theorem B3835505 : Blo 2019435 3835505 := bstep (se 2 (by rfl) ⟨1438314, by rfl⟩ : syracuseStep 3835505 = 2876629) B2876629
theorem B2557003 : Blo 2019435 2557003 := bstep (se 1 (by rfl) ⟨1917752, by rfl⟩ : syracuseStep 2557003 = 3835505) B3835505
theorem B3409337 : Blo 2019435 3409337 := bstep (se 2 (by rfl) ⟨1278501, by rfl⟩ : syracuseStep 3409337 = 2557003) B2557003
theorem B2272891 : Blo 2019435 2272891 := bstep (se 1 (by rfl) ⟨1704668, by rfl⟩ : syracuseStep 2272891 = 3409337) B3409337
theorem B3030521 : Blo 2019435 3030521 := bstep (se 2 (by rfl) ⟨1136445, by rfl⟩ : syracuseStep 3030521 = 2272891) B2272891
theorem B2020347 : Blo 2019435 2020347 := bstep (se 1 (by rfl) ⟨1515260, by rfl⟩ : syracuseStep 2020347 = 3030521) B3030521
theorem B110587477 : Blo 2019435 110587477 := bbase (se 8 (by rfl) ⟨647973, by rfl⟩ : syracuseStep 110587477 = 1295947) (by norm_num)
theorem B147449969 : Blo 2019435 147449969 := bstep (se 2 (by rfl) ⟨55293738, by rfl⟩ : syracuseStep 147449969 = 110587477) B110587477
theorem B98299979 : Blo 2019435 98299979 := bstep (se 1 (by rfl) ⟨73724984, by rfl⟩ : syracuseStep 98299979 = 147449969) B147449969
theorem B65533319 : Blo 2019435 65533319 := bstep (se 1 (by rfl) ⟨49149989, by rfl⟩ : syracuseStep 65533319 = 98299979) B98299979
theorem B43688879 : Blo 2019435 43688879 := bstep (se 1 (by rfl) ⟨32766659, by rfl⟩ : syracuseStep 43688879 = 65533319) B65533319
theorem B29125919 : Blo 2019435 29125919 := bstep (se 1 (by rfl) ⟨21844439, by rfl⟩ : syracuseStep 29125919 = 43688879) B43688879
theorem B77669117 : Blo 2019435 77669117 := bstep (se 3 (by rfl) ⟨14562959, by rfl⟩ : syracuseStep 77669117 = 29125919) B29125919
theorem B51779411 : Blo 2019435 51779411 := bstep (se 1 (by rfl) ⟨38834558, by rfl⟩ : syracuseStep 51779411 = 77669117) B77669117
theorem B34519607 : Blo 2019435 34519607 := bstep (se 1 (by rfl) ⟨25889705, by rfl⟩ : syracuseStep 34519607 = 51779411) B51779411
theorem B23013071 : Blo 2019435 23013071 := bstep (se 1 (by rfl) ⟨17259803, by rfl⟩ : syracuseStep 23013071 = 34519607) B34519607
theorem B15342047 : Blo 2019435 15342047 := bstep (se 1 (by rfl) ⟨11506535, by rfl⟩ : syracuseStep 15342047 = 23013071) B23013071
theorem B10228031 : Blo 2019435 10228031 := bstep (se 1 (by rfl) ⟨7671023, by rfl⟩ : syracuseStep 10228031 = 15342047) B15342047
theorem B6818687 : Blo 2019435 6818687 := bstep (se 1 (by rfl) ⟨5114015, by rfl⟩ : syracuseStep 6818687 = 10228031) B10228031
theorem B4545791 : Blo 2019435 4545791 := bstep (se 1 (by rfl) ⟨3409343, by rfl⟩ : syracuseStep 4545791 = 6818687) B6818687
theorem B3030527 : Blo 2019435 3030527 := bstep (se 1 (by rfl) ⟨2272895, by rfl⟩ : syracuseStep 3030527 = 4545791) B4545791
theorem B2020351 : Blo 2019435 2020351 := bstep (se 1 (by rfl) ⟨1515263, by rfl⟩ : syracuseStep 2020351 = 3030527) B3030527
theorem B3030533 : Blo 2019435 3030533 := bbase (se 4 (by rfl) ⟨284112, by rfl⟩ : syracuseStep 3030533 = 568225) (by norm_num)
theorem B2020355 : Blo 2019435 2020355 := bstep (se 1 (by rfl) ⟨1515266, by rfl⟩ : syracuseStep 2020355 = 3030533) B3030533
theorem B3409357 : Blo 2019435 3409357 := bbase (se 3 (by rfl) ⟨639254, by rfl⟩ : syracuseStep 3409357 = 1278509) (by norm_num)
theorem B4545809 : Blo 2019435 4545809 := bstep (se 2 (by rfl) ⟨1704678, by rfl⟩ : syracuseStep 4545809 = 3409357) B3409357
theorem B3030539 : Blo 2019435 3030539 := bstep (se 1 (by rfl) ⟨2272904, by rfl⟩ : syracuseStep 3030539 = 4545809) B4545809
theorem B2020359 : Blo 2019435 2020359 := bstep (se 1 (by rfl) ⟨1515269, by rfl⟩ : syracuseStep 2020359 = 3030539) B3030539
theorem B2272909 : Blo 2019435 2272909 := bbase (se 3 (by rfl) ⟨426170, by rfl⟩ : syracuseStep 2272909 = 852341) (by norm_num)
theorem B3030545 : Blo 2019435 3030545 := bstep (se 2 (by rfl) ⟨1136454, by rfl⟩ : syracuseStep 3030545 = 2272909) B2272909
theorem B2020363 : Blo 2019435 2020363 := bstep (se 1 (by rfl) ⟨1515272, by rfl⟩ : syracuseStep 2020363 = 3030545) B3030545
theorem B6818741 : Blo 2019435 6818741 := bbase (se 5 (by rfl) ⟨319628, by rfl⟩ : syracuseStep 6818741 = 639257) (by norm_num)
theorem B4545827 : Blo 2019435 4545827 := bstep (se 1 (by rfl) ⟨3409370, by rfl⟩ : syracuseStep 4545827 = 6818741) B6818741
theorem B3030551 : Blo 2019435 3030551 := bstep (se 1 (by rfl) ⟨2272913, by rfl⟩ : syracuseStep 3030551 = 4545827) B4545827
theorem B2020367 : Blo 2019435 2020367 := bstep (se 1 (by rfl) ⟨1515275, by rfl⟩ : syracuseStep 2020367 = 3030551) B3030551
theorem B3030557 : Blo 2019435 3030557 := bbase (se 3 (by rfl) ⟨568229, by rfl⟩ : syracuseStep 3030557 = 1136459) (by norm_num)
theorem B2020371 : Blo 2019435 2020371 := bstep (se 1 (by rfl) ⟨1515278, by rfl⟩ : syracuseStep 2020371 = 3030557) B3030557
theorem B4545845 : Blo 2019435 4545845 := bbase (se 5 (by rfl) ⟨213086, by rfl⟩ : syracuseStep 4545845 = 426173) (by norm_num)
theorem B3030563 : Blo 2019435 3030563 := bstep (se 1 (by rfl) ⟨2272922, by rfl⟩ : syracuseStep 3030563 = 4545845) B4545845
theorem B2020375 : Blo 2019435 2020375 := bstep (se 1 (by rfl) ⟨1515281, by rfl⟩ : syracuseStep 2020375 = 3030563) B3030563
theorem B8191781 : Blo 2019435 8191781 := bbase (se 4 (by rfl) ⟨767979, by rfl⟩ : syracuseStep 8191781 = 1535959) (by norm_num)
theorem B5461187 : Blo 2019435 5461187 := bstep (se 1 (by rfl) ⟨4095890, by rfl⟩ : syracuseStep 5461187 = 8191781) B8191781
theorem B14563165 : Blo 2019435 14563165 := bstep (se 3 (by rfl) ⟨2730593, by rfl⟩ : syracuseStep 14563165 = 5461187) B5461187
theorem B19417553 : Blo 2019435 19417553 := bstep (se 2 (by rfl) ⟨7281582, by rfl⟩ : syracuseStep 19417553 = 14563165) B14563165
theorem B12945035 : Blo 2019435 12945035 := bstep (se 1 (by rfl) ⟨9708776, by rfl⟩ : syracuseStep 12945035 = 19417553) B19417553
theorem B8630023 : Blo 2019435 8630023 := bstep (se 1 (by rfl) ⟨6472517, by rfl⟩ : syracuseStep 8630023 = 12945035) B12945035
theorem B11506697 : Blo 2019435 11506697 := bstep (se 2 (by rfl) ⟨4315011, by rfl⟩ : syracuseStep 11506697 = 8630023) B8630023
theorem B7671131 : Blo 2019435 7671131 := bstep (se 1 (by rfl) ⟨5753348, by rfl⟩ : syracuseStep 7671131 = 11506697) B11506697
theorem B5114087 : Blo 2019435 5114087 := bstep (se 1 (by rfl) ⟨3835565, by rfl⟩ : syracuseStep 5114087 = 7671131) B7671131
theorem B3409391 : Blo 2019435 3409391 := bstep (se 1 (by rfl) ⟨2557043, by rfl⟩ : syracuseStep 3409391 = 5114087) B5114087
theorem B2272927 : Blo 2019435 2272927 := bstep (se 1 (by rfl) ⟨1704695, by rfl⟩ : syracuseStep 2272927 = 3409391) B3409391
theorem B3030569 : Blo 2019435 3030569 := bstep (se 2 (by rfl) ⟨1136463, by rfl⟩ : syracuseStep 3030569 = 2272927) B2272927
theorem B2020379 : Blo 2019435 2020379 := bstep (se 1 (by rfl) ⟨1515284, by rfl⟩ : syracuseStep 2020379 = 3030569) B3030569
theorem B19417589 : Blo 2019435 19417589 := bbase (se 5 (by rfl) ⟨910199, by rfl⟩ : syracuseStep 19417589 = 1820399) (by norm_num)
theorem B12945059 : Blo 2019435 12945059 := bstep (se 1 (by rfl) ⟨9708794, by rfl⟩ : syracuseStep 12945059 = 19417589) B19417589
theorem B8630039 : Blo 2019435 8630039 := bstep (se 1 (by rfl) ⟨6472529, by rfl⟩ : syracuseStep 8630039 = 12945059) B12945059
theorem B5753359 : Blo 2019435 5753359 := bstep (se 1 (by rfl) ⟨4315019, by rfl⟩ : syracuseStep 5753359 = 8630039) B8630039
theorem B7671145 : Blo 2019435 7671145 := bstep (se 2 (by rfl) ⟨2876679, by rfl⟩ : syracuseStep 7671145 = 5753359) B5753359
theorem B10228193 : Blo 2019435 10228193 := bstep (se 2 (by rfl) ⟨3835572, by rfl⟩ : syracuseStep 10228193 = 7671145) B7671145
theorem B6818795 : Blo 2019435 6818795 := bstep (se 1 (by rfl) ⟨5114096, by rfl⟩ : syracuseStep 6818795 = 10228193) B10228193
theorem B4545863 : Blo 2019435 4545863 := bstep (se 1 (by rfl) ⟨3409397, by rfl⟩ : syracuseStep 4545863 = 6818795) B6818795
theorem B3030575 : Blo 2019435 3030575 := bstep (se 1 (by rfl) ⟨2272931, by rfl⟩ : syracuseStep 3030575 = 4545863) B4545863
theorem B2020383 : Blo 2019435 2020383 := bstep (se 1 (by rfl) ⟨1515287, by rfl⟩ : syracuseStep 2020383 = 3030575) B3030575
theorem B3030581 : Blo 2019435 3030581 := bbase (se 5 (by rfl) ⟨142058, by rfl⟩ : syracuseStep 3030581 = 284117) (by norm_num)
theorem B2020387 : Blo 2019435 2020387 := bstep (se 1 (by rfl) ⟨1515290, by rfl⟩ : syracuseStep 2020387 = 3030581) B3030581
theorem B5114117 : Blo 2019435 5114117 := bbase (se 4 (by rfl) ⟨479448, by rfl⟩ : syracuseStep 5114117 = 958897) (by norm_num)
theorem B3409411 : Blo 2019435 3409411 := bstep (se 1 (by rfl) ⟨2557058, by rfl⟩ : syracuseStep 3409411 = 5114117) B5114117
theorem B4545881 : Blo 2019435 4545881 := bstep (se 2 (by rfl) ⟨1704705, by rfl⟩ : syracuseStep 4545881 = 3409411) B3409411
theorem B3030587 : Blo 2019435 3030587 := bstep (se 1 (by rfl) ⟨2272940, by rfl⟩ : syracuseStep 3030587 = 4545881) B4545881
theorem B2020391 : Blo 2019435 2020391 := bstep (se 1 (by rfl) ⟨1515293, by rfl⟩ : syracuseStep 2020391 = 3030587) B3030587
theorem B2272945 : Blo 2019435 2272945 := bbase (se 2 (by rfl) ⟨852354, by rfl⟩ : syracuseStep 2272945 = 1704709) (by norm_num)
theorem B3030593 : Blo 2019435 3030593 := bstep (se 2 (by rfl) ⟨1136472, by rfl⟩ : syracuseStep 3030593 = 2272945) B2272945
theorem B2020395 : Blo 2019435 2020395 := bstep (se 1 (by rfl) ⟨1515296, by rfl⟩ : syracuseStep 2020395 = 3030593) B3030593
theorem B4854437 : Blo 2019435 4854437 := bbase (se 4 (by rfl) ⟨455103, by rfl⟩ : syracuseStep 4854437 = 910207) (by norm_num)
theorem B3236291 : Blo 2019435 3236291 := bstep (se 1 (by rfl) ⟨2427218, by rfl⟩ : syracuseStep 3236291 = 4854437) B4854437
theorem B2157527 : Blo 2019435 2157527 := bstep (se 1 (by rfl) ⟨1618145, by rfl⟩ : syracuseStep 2157527 = 3236291) B3236291
theorem B5753405 : Blo 2019435 5753405 := bstep (se 3 (by rfl) ⟨1078763, by rfl⟩ : syracuseStep 5753405 = 2157527) B2157527
theorem B3835603 : Blo 2019435 3835603 := bstep (se 1 (by rfl) ⟨2876702, by rfl⟩ : syracuseStep 3835603 = 5753405) B5753405
theorem B5114137 : Blo 2019435 5114137 := bstep (se 2 (by rfl) ⟨1917801, by rfl⟩ : syracuseStep 5114137 = 3835603) B3835603
theorem B6818849 : Blo 2019435 6818849 := bstep (se 2 (by rfl) ⟨2557068, by rfl⟩ : syracuseStep 6818849 = 5114137) B5114137
theorem B4545899 : Blo 2019435 4545899 := bstep (se 1 (by rfl) ⟨3409424, by rfl⟩ : syracuseStep 4545899 = 6818849) B6818849
theorem B3030599 : Blo 2019435 3030599 := bstep (se 1 (by rfl) ⟨2272949, by rfl⟩ : syracuseStep 3030599 = 4545899) B4545899
theorem B2020399 : Blo 2019435 2020399 := bstep (se 1 (by rfl) ⟨1515299, by rfl⟩ : syracuseStep 2020399 = 3030599) B3030599
theorem B3030605 : Blo 2019435 3030605 := bbase (se 3 (by rfl) ⟨568238, by rfl⟩ : syracuseStep 3030605 = 1136477) (by norm_num)
theorem B2020403 : Blo 2019435 2020403 := bstep (se 1 (by rfl) ⟨1515302, by rfl⟩ : syracuseStep 2020403 = 3030605) B3030605
theorem B4545917 : Blo 2019435 4545917 := bbase (se 3 (by rfl) ⟨852359, by rfl⟩ : syracuseStep 4545917 = 1704719) (by norm_num)
theorem B3030611 : Blo 2019435 3030611 := bstep (se 1 (by rfl) ⟨2272958, by rfl⟩ : syracuseStep 3030611 = 4545917) B4545917
theorem B2020407 : Blo 2019435 2020407 := bstep (se 1 (by rfl) ⟨1515305, by rfl⟩ : syracuseStep 2020407 = 3030611) B3030611
theorem B3409445 : Blo 2019435 3409445 := bbase (se 4 (by rfl) ⟨319635, by rfl⟩ : syracuseStep 3409445 = 639271) (by norm_num)
theorem B2272963 : Blo 2019435 2272963 := bstep (se 1 (by rfl) ⟨1704722, by rfl⟩ : syracuseStep 2272963 = 3409445) B3409445
theorem B3030617 : Blo 2019435 3030617 := bstep (se 2 (by rfl) ⟨1136481, by rfl⟩ : syracuseStep 3030617 = 2272963) B2272963
theorem B2020411 : Blo 2019435 2020411 := bstep (se 1 (by rfl) ⟨1515308, by rfl⟩ : syracuseStep 2020411 = 3030617) B3030617
theorem B2876725 : Blo 2019435 2876725 := bbase (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) (by norm_num)
theorem B15342533 : Blo 2019435 15342533 := bstep (se 4 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 15342533 = 2876725) B2876725
theorem B10228355 : Blo 2019435 10228355 := bstep (se 1 (by rfl) ⟨7671266, by rfl⟩ : syracuseStep 10228355 = 15342533) B15342533
theorem B6818903 : Blo 2019435 6818903 := bstep (se 1 (by rfl) ⟨5114177, by rfl⟩ : syracuseStep 6818903 = 10228355) B10228355
theorem B4545935 : Blo 2019435 4545935 := bstep (se 1 (by rfl) ⟨3409451, by rfl⟩ : syracuseStep 4545935 = 6818903) B6818903
theorem B3030623 : Blo 2019435 3030623 := bstep (se 1 (by rfl) ⟨2272967, by rfl⟩ : syracuseStep 3030623 = 4545935) B4545935
theorem B2020415 : Blo 2019435 2020415 := bstep (se 1 (by rfl) ⟨1515311, by rfl⟩ : syracuseStep 2020415 = 3030623) B3030623
theorem B3030629 : Blo 2019435 3030629 := bbase (se 4 (by rfl) ⟨284121, by rfl⟩ : syracuseStep 3030629 = 568243) (by norm_num)
theorem B2020419 : Blo 2019435 2020419 := bstep (se 1 (by rfl) ⟨1515314, by rfl⟩ : syracuseStep 2020419 = 3030629) B3030629
theorem B2157553 : Blo 2019435 2157553 := bbase (se 2 (by rfl) ⟨809082, by rfl⟩ : syracuseStep 2157553 = 1618165) (by norm_num)
theorem B2876737 : Blo 2019435 2876737 := bstep (se 2 (by rfl) ⟨1078776, by rfl⟩ : syracuseStep 2876737 = 2157553) B2157553
theorem B3835649 : Blo 2019435 3835649 := bstep (se 2 (by rfl) ⟨1438368, by rfl⟩ : syracuseStep 3835649 = 2876737) B2876737
theorem B2557099 : Blo 2019435 2557099 := bstep (se 1 (by rfl) ⟨1917824, by rfl⟩ : syracuseStep 2557099 = 3835649) B3835649
theorem B3409465 : Blo 2019435 3409465 := bstep (se 2 (by rfl) ⟨1278549, by rfl⟩ : syracuseStep 3409465 = 2557099) B2557099
theorem B4545953 : Blo 2019435 4545953 := bstep (se 2 (by rfl) ⟨1704732, by rfl⟩ : syracuseStep 4545953 = 3409465) B3409465
theorem B3030635 : Blo 2019435 3030635 := bstep (se 1 (by rfl) ⟨2272976, by rfl⟩ : syracuseStep 3030635 = 4545953) B4545953
theorem B2020423 : Blo 2019435 2020423 := bstep (se 1 (by rfl) ⟨1515317, by rfl⟩ : syracuseStep 2020423 = 3030635) B3030635
theorem B2272981 : Blo 2019435 2272981 := bbase (se 7 (by rfl) ⟨26636, by rfl⟩ : syracuseStep 2272981 = 53273) (by norm_num)
theorem B3030641 : Blo 2019435 3030641 := bstep (se 2 (by rfl) ⟨1136490, by rfl⟩ : syracuseStep 3030641 = 2272981) B2272981
theorem B2020427 : Blo 2019435 2020427 := bstep (se 1 (by rfl) ⟨1515320, by rfl⟩ : syracuseStep 2020427 = 3030641) B3030641
theorem B2557109 : Blo 2019435 2557109 := bbase (se 5 (by rfl) ⟨119864, by rfl⟩ : syracuseStep 2557109 = 239729) (by norm_num)
theorem B6818957 : Blo 2019435 6818957 := bstep (se 3 (by rfl) ⟨1278554, by rfl⟩ : syracuseStep 6818957 = 2557109) B2557109
theorem B4545971 : Blo 2019435 4545971 := bstep (se 1 (by rfl) ⟨3409478, by rfl⟩ : syracuseStep 4545971 = 6818957) B6818957
theorem B3030647 : Blo 2019435 3030647 := bstep (se 1 (by rfl) ⟨2272985, by rfl⟩ : syracuseStep 3030647 = 4545971) B4545971
theorem B2020431 : Blo 2019435 2020431 := bstep (se 1 (by rfl) ⟨1515323, by rfl⟩ : syracuseStep 2020431 = 3030647) B3030647
theorem B3030653 : Blo 2019435 3030653 := bbase (se 3 (by rfl) ⟨568247, by rfl⟩ : syracuseStep 3030653 = 1136495) (by norm_num)
theorem B2020435 : Blo 2019435 2020435 := bstep (se 1 (by rfl) ⟨1515326, by rfl⟩ : syracuseStep 2020435 = 3030653) B3030653
theorem B4545989 : Blo 2019435 4545989 := bbase (se 4 (by rfl) ⟨426186, by rfl⟩ : syracuseStep 4545989 = 852373) (by norm_num)
theorem B3030659 : Blo 2019435 3030659 := bstep (se 1 (by rfl) ⟨2272994, by rfl⟩ : syracuseStep 3030659 = 4545989) B4545989
theorem B2020439 : Blo 2019435 2020439 := bstep (se 1 (by rfl) ⟨1515329, by rfl⟩ : syracuseStep 2020439 = 3030659) B3030659
theorem B4096021 : Blo 2019435 4096021 := bbase (se 6 (by rfl) ⟨96000, by rfl⟩ : syracuseStep 4096021 = 192001) (by norm_num)
theorem B5461361 : Blo 2019435 5461361 := bstep (se 2 (by rfl) ⟨2048010, by rfl⟩ : syracuseStep 5461361 = 4096021) B4096021
theorem B3640907 : Blo 2019435 3640907 := bstep (se 1 (by rfl) ⟨2730680, by rfl⟩ : syracuseStep 3640907 = 5461361) B5461361
theorem B9709085 : Blo 2019435 9709085 := bstep (se 3 (by rfl) ⟨1820453, by rfl⟩ : syracuseStep 9709085 = 3640907) B3640907
theorem B6472723 : Blo 2019435 6472723 := bstep (se 1 (by rfl) ⟨4854542, by rfl⟩ : syracuseStep 6472723 = 9709085) B9709085
theorem B8630297 : Blo 2019435 8630297 := bstep (se 2 (by rfl) ⟨3236361, by rfl⟩ : syracuseStep 8630297 = 6472723) B6472723
theorem B5753531 : Blo 2019435 5753531 := bstep (se 1 (by rfl) ⟨4315148, by rfl⟩ : syracuseStep 5753531 = 8630297) B8630297
theorem B3835687 : Blo 2019435 3835687 := bstep (se 1 (by rfl) ⟨2876765, by rfl⟩ : syracuseStep 3835687 = 5753531) B5753531
theorem B5114249 : Blo 2019435 5114249 := bstep (se 2 (by rfl) ⟨1917843, by rfl⟩ : syracuseStep 5114249 = 3835687) B3835687
theorem B3409499 : Blo 2019435 3409499 := bstep (se 1 (by rfl) ⟨2557124, by rfl⟩ : syracuseStep 3409499 = 5114249) B5114249
theorem B2272999 : Blo 2019435 2272999 := bstep (se 1 (by rfl) ⟨1704749, by rfl⟩ : syracuseStep 2272999 = 3409499) B3409499
theorem B3030665 : Blo 2019435 3030665 := bstep (se 2 (by rfl) ⟨1136499, by rfl⟩ : syracuseStep 3030665 = 2272999) B2272999
theorem B2020443 : Blo 2019435 2020443 := bstep (se 1 (by rfl) ⟨1515332, by rfl⟩ : syracuseStep 2020443 = 3030665) B3030665
theorem B10228517 : Blo 2019435 10228517 := bbase (se 4 (by rfl) ⟨958923, by rfl⟩ : syracuseStep 10228517 = 1917847) (by norm_num)
theorem B6819011 : Blo 2019435 6819011 := bstep (se 1 (by rfl) ⟨5114258, by rfl⟩ : syracuseStep 6819011 = 10228517) B10228517
theorem B4546007 : Blo 2019435 4546007 := bstep (se 1 (by rfl) ⟨3409505, by rfl⟩ : syracuseStep 4546007 = 6819011) B6819011
theorem B3030671 : Blo 2019435 3030671 := bstep (se 1 (by rfl) ⟨2273003, by rfl⟩ : syracuseStep 3030671 = 4546007) B4546007
theorem B2020447 : Blo 2019435 2020447 := bstep (se 1 (by rfl) ⟨1515335, by rfl⟩ : syracuseStep 2020447 = 3030671) B3030671
theorem B3030677 : Blo 2019435 3030677 := bbase (se 6 (by rfl) ⟨71031, by rfl⟩ : syracuseStep 3030677 = 142063) (by norm_num)
theorem B2020451 : Blo 2019435 2020451 := bstep (se 1 (by rfl) ⟨1515338, by rfl⟩ : syracuseStep 2020451 = 3030677) B3030677
theorem B9709141 : Blo 2019435 9709141 := bbase (se 8 (by rfl) ⟨56889, by rfl⟩ : syracuseStep 9709141 = 113779) (by norm_num)
theorem B12945521 : Blo 2019435 12945521 := bstep (se 2 (by rfl) ⟨4854570, by rfl⟩ : syracuseStep 12945521 = 9709141) B9709141
theorem B8630347 : Blo 2019435 8630347 := bstep (se 1 (by rfl) ⟨6472760, by rfl⟩ : syracuseStep 8630347 = 12945521) B12945521
theorem B11507129 : Blo 2019435 11507129 := bstep (se 2 (by rfl) ⟨4315173, by rfl⟩ : syracuseStep 11507129 = 8630347) B8630347
theorem B7671419 : Blo 2019435 7671419 := bstep (se 1 (by rfl) ⟨5753564, by rfl⟩ : syracuseStep 7671419 = 11507129) B11507129
theorem B5114279 : Blo 2019435 5114279 := bstep (se 1 (by rfl) ⟨3835709, by rfl⟩ : syracuseStep 5114279 = 7671419) B7671419
theorem B3409519 : Blo 2019435 3409519 := bstep (se 1 (by rfl) ⟨2557139, by rfl⟩ : syracuseStep 3409519 = 5114279) B5114279
theorem B4546025 : Blo 2019435 4546025 := bstep (se 2 (by rfl) ⟨1704759, by rfl⟩ : syracuseStep 4546025 = 3409519) B3409519
theorem B3030683 : Blo 2019435 3030683 := bstep (se 1 (by rfl) ⟨2273012, by rfl⟩ : syracuseStep 3030683 = 4546025) B4546025
theorem B2020455 : Blo 2019435 2020455 := bstep (se 1 (by rfl) ⟨1515341, by rfl⟩ : syracuseStep 2020455 = 3030683) B3030683
theorem B2273017 : Blo 2019435 2273017 := bbase (se 2 (by rfl) ⟨852381, by rfl⟩ : syracuseStep 2273017 = 1704763) (by norm_num)
theorem B3030689 : Blo 2019435 3030689 := bstep (se 2 (by rfl) ⟨1136508, by rfl⟩ : syracuseStep 3030689 = 2273017) B2273017
theorem B2020459 : Blo 2019435 2020459 := bstep (se 1 (by rfl) ⟨1515344, by rfl⟩ : syracuseStep 2020459 = 3030689) B3030689
theorem B2460413 : Blo 2019435 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B6561101 : Blo 2019435 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B4374067 : Blo 2019435 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B5832089 : Blo 2019435 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B3888059 : Blo 2019435 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B10368157 : Blo 2019435 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B13824209 : Blo 2019435 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B9216139 : Blo 2019435 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B12288185 : Blo 2019435 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B8192123 : Blo 2019435 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B5461415 : Blo 2019435 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B3640943 : Blo 2019435 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B2427295 : Blo 2019435 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B3236393 : Blo 2019435 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B8630381 : Blo 2019435 8630381 := bstep (se 3 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 8630381 = 3236393) B3236393
theorem B5753587 : Blo 2019435 5753587 := bstep (se 1 (by rfl) ⟨4315190, by rfl⟩ : syracuseStep 5753587 = 8630381) B8630381
theorem B7671449 : Blo 2019435 7671449 := bstep (se 2 (by rfl) ⟨2876793, by rfl⟩ : syracuseStep 7671449 = 5753587) B5753587
theorem B5114299 : Blo 2019435 5114299 := bstep (se 1 (by rfl) ⟨3835724, by rfl⟩ : syracuseStep 5114299 = 7671449) B7671449
theorem B6819065 : Blo 2019435 6819065 := bstep (se 2 (by rfl) ⟨2557149, by rfl⟩ : syracuseStep 6819065 = 5114299) B5114299
theorem B4546043 : Blo 2019435 4546043 := bstep (se 1 (by rfl) ⟨3409532, by rfl⟩ : syracuseStep 4546043 = 6819065) B6819065
theorem B3030695 : Blo 2019435 3030695 := bstep (se 1 (by rfl) ⟨2273021, by rfl⟩ : syracuseStep 3030695 = 4546043) B4546043
theorem B2020463 : Blo 2019435 2020463 := bstep (se 1 (by rfl) ⟨1515347, by rfl⟩ : syracuseStep 2020463 = 3030695) B3030695
theorem B3030701 : Blo 2019435 3030701 := bbase (se 3 (by rfl) ⟨568256, by rfl⟩ : syracuseStep 3030701 = 1136513) (by norm_num)
theorem B2020467 : Blo 2019435 2020467 := bstep (se 1 (by rfl) ⟨1515350, by rfl⟩ : syracuseStep 2020467 = 3030701) B3030701
theorem B4546061 : Blo 2019435 4546061 := bbase (se 3 (by rfl) ⟨852386, by rfl⟩ : syracuseStep 4546061 = 1704773) (by norm_num)
theorem B3030707 : Blo 2019435 3030707 := bstep (se 1 (by rfl) ⟨2273030, by rfl⟩ : syracuseStep 3030707 = 4546061) B4546061
theorem B2020471 : Blo 2019435 2020471 := bstep (se 1 (by rfl) ⟨1515353, by rfl⟩ : syracuseStep 2020471 = 3030707) B3030707
theorem B2557165 : Blo 2019435 2557165 := bbase (se 3 (by rfl) ⟨479468, by rfl⟩ : syracuseStep 2557165 = 958937) (by norm_num)
theorem B3409553 : Blo 2019435 3409553 := bstep (se 2 (by rfl) ⟨1278582, by rfl⟩ : syracuseStep 3409553 = 2557165) B2557165
theorem B2273035 : Blo 2019435 2273035 := bstep (se 1 (by rfl) ⟨1704776, by rfl⟩ : syracuseStep 2273035 = 3409553) B3409553
theorem B3030713 : Blo 2019435 3030713 := bstep (se 2 (by rfl) ⟨1136517, by rfl⟩ : syracuseStep 3030713 = 2273035) B2273035
theorem B2020475 : Blo 2019435 2020475 := bstep (se 1 (by rfl) ⟨1515356, by rfl⟩ : syracuseStep 2020475 = 3030713) B3030713
theorem B12288277 : Blo 2019435 12288277 := bbase (se 6 (by rfl) ⟨288006, by rfl⟩ : syracuseStep 12288277 = 576013) (by norm_num)
theorem B16384369 : Blo 2019435 16384369 := bstep (se 2 (by rfl) ⟨6144138, by rfl⟩ : syracuseStep 16384369 = 12288277) B12288277
theorem B21845825 : Blo 2019435 21845825 := bstep (se 2 (by rfl) ⟨8192184, by rfl⟩ : syracuseStep 21845825 = 16384369) B16384369
theorem B14563883 : Blo 2019435 14563883 := bstep (se 1 (by rfl) ⟨10922912, by rfl⟩ : syracuseStep 14563883 = 21845825) B21845825
theorem B9709255 : Blo 2019435 9709255 := bstep (se 1 (by rfl) ⟨7281941, by rfl⟩ : syracuseStep 9709255 = 14563883) B14563883
theorem B12945673 : Blo 2019435 12945673 := bstep (se 2 (by rfl) ⟨4854627, by rfl⟩ : syracuseStep 12945673 = 9709255) B9709255
theorem B17260897 : Blo 2019435 17260897 := bstep (se 2 (by rfl) ⟨6472836, by rfl⟩ : syracuseStep 17260897 = 12945673) B12945673
theorem B23014529 : Blo 2019435 23014529 := bstep (se 2 (by rfl) ⟨8630448, by rfl⟩ : syracuseStep 23014529 = 17260897) B17260897
theorem B15343019 : Blo 2019435 15343019 := bstep (se 1 (by rfl) ⟨11507264, by rfl⟩ : syracuseStep 15343019 = 23014529) B23014529
theorem B10228679 : Blo 2019435 10228679 := bstep (se 1 (by rfl) ⟨7671509, by rfl⟩ : syracuseStep 10228679 = 15343019) B15343019
theorem B6819119 : Blo 2019435 6819119 := bstep (se 1 (by rfl) ⟨5114339, by rfl⟩ : syracuseStep 6819119 = 10228679) B10228679
theorem B4546079 : Blo 2019435 4546079 := bstep (se 1 (by rfl) ⟨3409559, by rfl⟩ : syracuseStep 4546079 = 6819119) B6819119
theorem B3030719 : Blo 2019435 3030719 := bstep (se 1 (by rfl) ⟨2273039, by rfl⟩ : syracuseStep 3030719 = 4546079) B4546079
theorem B2020479 : Blo 2019435 2020479 := bstep (se 1 (by rfl) ⟨1515359, by rfl⟩ : syracuseStep 2020479 = 3030719) B3030719
theorem B3030725 : Blo 2019435 3030725 := bbase (se 4 (by rfl) ⟨284130, by rfl⟩ : syracuseStep 3030725 = 568261) (by norm_num)
theorem B2020483 : Blo 2019435 2020483 := bstep (se 1 (by rfl) ⟨1515362, by rfl⟩ : syracuseStep 2020483 = 3030725) B3030725
theorem B3409573 : Blo 2019435 3409573 := bbase (se 4 (by rfl) ⟨319647, by rfl⟩ : syracuseStep 3409573 = 639295) (by norm_num)
theorem B4546097 : Blo 2019435 4546097 := bstep (se 2 (by rfl) ⟨1704786, by rfl⟩ : syracuseStep 4546097 = 3409573) B3409573
theorem B3030731 : Blo 2019435 3030731 := bstep (se 1 (by rfl) ⟨2273048, by rfl⟩ : syracuseStep 3030731 = 4546097) B4546097
theorem B2020487 : Blo 2019435 2020487 := bstep (se 1 (by rfl) ⟨1515365, by rfl⟩ : syracuseStep 2020487 = 3030731) B3030731
theorem B2273053 : Blo 2019435 2273053 := bbase (se 3 (by rfl) ⟨426197, by rfl⟩ : syracuseStep 2273053 = 852395) (by norm_num)
theorem B3030737 : Blo 2019435 3030737 := bstep (se 2 (by rfl) ⟨1136526, by rfl⟩ : syracuseStep 3030737 = 2273053) B2273053
theorem B2020491 : Blo 2019435 2020491 := bstep (se 1 (by rfl) ⟨1515368, by rfl⟩ : syracuseStep 2020491 = 3030737) B3030737
theorem B6819173 : Blo 2019435 6819173 := bbase (se 4 (by rfl) ⟨639297, by rfl⟩ : syracuseStep 6819173 = 1278595) (by norm_num)
theorem B4546115 : Blo 2019435 4546115 := bstep (se 1 (by rfl) ⟨3409586, by rfl⟩ : syracuseStep 4546115 = 6819173) B6819173
theorem B3030743 : Blo 2019435 3030743 := bstep (se 1 (by rfl) ⟨2273057, by rfl⟩ : syracuseStep 3030743 = 4546115) B4546115
theorem B2020495 : Blo 2019435 2020495 := bstep (se 1 (by rfl) ⟨1515371, by rfl⟩ : syracuseStep 2020495 = 3030743) B3030743
theorem B3030749 : Blo 2019435 3030749 := bbase (se 3 (by rfl) ⟨568265, by rfl⟩ : syracuseStep 3030749 = 1136531) (by norm_num)
theorem B2020499 : Blo 2019435 2020499 := bstep (se 1 (by rfl) ⟨1515374, by rfl⟩ : syracuseStep 2020499 = 3030749) B3030749
theorem B4546133 : Blo 2019435 4546133 := bbase (se 8 (by rfl) ⟨26637, by rfl⟩ : syracuseStep 4546133 = 53275) (by norm_num)
theorem B3030755 : Blo 2019435 3030755 := bstep (se 1 (by rfl) ⟨2273066, by rfl⟩ : syracuseStep 3030755 = 4546133) B4546133
theorem B2020503 : Blo 2019435 2020503 := bstep (se 1 (by rfl) ⟨1515377, by rfl⟩ : syracuseStep 2020503 = 3030755) B3030755
theorem B4315285 : Blo 2019435 4315285 := bbase (se 6 (by rfl) ⟨101139, by rfl⟩ : syracuseStep 4315285 = 202279) (by norm_num)
theorem B5753713 : Blo 2019435 5753713 := bstep (se 2 (by rfl) ⟨2157642, by rfl⟩ : syracuseStep 5753713 = 4315285) B4315285
theorem B7671617 : Blo 2019435 7671617 := bstep (se 2 (by rfl) ⟨2876856, by rfl⟩ : syracuseStep 7671617 = 5753713) B5753713
theorem B5114411 : Blo 2019435 5114411 := bstep (se 1 (by rfl) ⟨3835808, by rfl⟩ : syracuseStep 5114411 = 7671617) B7671617
theorem B3409607 : Blo 2019435 3409607 := bstep (se 1 (by rfl) ⟨2557205, by rfl⟩ : syracuseStep 3409607 = 5114411) B5114411
theorem B2273071 : Blo 2019435 2273071 := bstep (se 1 (by rfl) ⟨1704803, by rfl⟩ : syracuseStep 2273071 = 3409607) B3409607
theorem B3030761 : Blo 2019435 3030761 := bstep (se 2 (by rfl) ⟨1136535, by rfl⟩ : syracuseStep 3030761 = 2273071) B2273071
theorem B2020507 : Blo 2019435 2020507 := bstep (se 1 (by rfl) ⟨1515380, by rfl⟩ : syracuseStep 2020507 = 3030761) B3030761
theorem B13824533 : Blo 2019435 13824533 := bbase (se 6 (by rfl) ⟨324012, by rfl⟩ : syracuseStep 13824533 = 648025) (by norm_num)
theorem B9216355 : Blo 2019435 9216355 := bstep (se 1 (by rfl) ⟨6912266, by rfl⟩ : syracuseStep 9216355 = 13824533) B13824533
theorem B12288473 : Blo 2019435 12288473 := bstep (se 2 (by rfl) ⟨4608177, by rfl⟩ : syracuseStep 12288473 = 9216355) B9216355
theorem B8192315 : Blo 2019435 8192315 := bstep (se 1 (by rfl) ⟨6144236, by rfl⟩ : syracuseStep 8192315 = 12288473) B12288473
theorem B5461543 : Blo 2019435 5461543 := bstep (se 1 (by rfl) ⟨4096157, by rfl⟩ : syracuseStep 5461543 = 8192315) B8192315
theorem B7282057 : Blo 2019435 7282057 := bstep (se 2 (by rfl) ⟨2730771, by rfl⟩ : syracuseStep 7282057 = 5461543) B5461543
theorem B9709409 : Blo 2019435 9709409 := bstep (se 2 (by rfl) ⟨3641028, by rfl⟩ : syracuseStep 9709409 = 7282057) B7282057
theorem B25891757 : Blo 2019435 25891757 := bstep (se 3 (by rfl) ⟨4854704, by rfl⟩ : syracuseStep 25891757 = 9709409) B9709409
theorem B17261171 : Blo 2019435 17261171 := bstep (se 1 (by rfl) ⟨12945878, by rfl⟩ : syracuseStep 17261171 = 25891757) B25891757
theorem B11507447 : Blo 2019435 11507447 := bstep (se 1 (by rfl) ⟨8630585, by rfl⟩ : syracuseStep 11507447 = 17261171) B17261171
theorem B7671631 : Blo 2019435 7671631 := bstep (se 1 (by rfl) ⟨5753723, by rfl⟩ : syracuseStep 7671631 = 11507447) B11507447
theorem B10228841 : Blo 2019435 10228841 := bstep (se 2 (by rfl) ⟨3835815, by rfl⟩ : syracuseStep 10228841 = 7671631) B7671631
theorem B6819227 : Blo 2019435 6819227 := bstep (se 1 (by rfl) ⟨5114420, by rfl⟩ : syracuseStep 6819227 = 10228841) B10228841
theorem B4546151 : Blo 2019435 4546151 := bstep (se 1 (by rfl) ⟨3409613, by rfl⟩ : syracuseStep 4546151 = 6819227) B6819227
theorem B3030767 : Blo 2019435 3030767 := bstep (se 1 (by rfl) ⟨2273075, by rfl⟩ : syracuseStep 3030767 = 4546151) B4546151
theorem B2020511 : Blo 2019435 2020511 := bstep (se 1 (by rfl) ⟨1515383, by rfl⟩ : syracuseStep 2020511 = 3030767) B3030767
theorem B3030773 : Blo 2019435 3030773 := bbase (se 5 (by rfl) ⟨142067, by rfl⟩ : syracuseStep 3030773 = 284135) (by norm_num)
theorem B2020515 : Blo 2019435 2020515 := bstep (se 1 (by rfl) ⟨1515386, by rfl⟩ : syracuseStep 2020515 = 3030773) B3030773
theorem B4854725 : Blo 2019435 4854725 := bbase (se 4 (by rfl) ⟨455130, by rfl⟩ : syracuseStep 4854725 = 910261) (by norm_num)
theorem B3236483 : Blo 2019435 3236483 := bstep (se 1 (by rfl) ⟨2427362, by rfl⟩ : syracuseStep 3236483 = 4854725) B4854725
theorem B8630621 : Blo 2019435 8630621 := bstep (se 3 (by rfl) ⟨1618241, by rfl⟩ : syracuseStep 8630621 = 3236483) B3236483
theorem B5753747 : Blo 2019435 5753747 := bstep (se 1 (by rfl) ⟨4315310, by rfl⟩ : syracuseStep 5753747 = 8630621) B8630621
theorem B3835831 : Blo 2019435 3835831 := bstep (se 1 (by rfl) ⟨2876873, by rfl⟩ : syracuseStep 3835831 = 5753747) B5753747
theorem B5114441 : Blo 2019435 5114441 := bstep (se 2 (by rfl) ⟨1917915, by rfl⟩ : syracuseStep 5114441 = 3835831) B3835831
theorem B3409627 : Blo 2019435 3409627 := bstep (se 1 (by rfl) ⟨2557220, by rfl⟩ : syracuseStep 3409627 = 5114441) B5114441
theorem B4546169 : Blo 2019435 4546169 := bstep (se 2 (by rfl) ⟨1704813, by rfl⟩ : syracuseStep 4546169 = 3409627) B3409627
theorem B3030779 : Blo 2019435 3030779 := bstep (se 1 (by rfl) ⟨2273084, by rfl⟩ : syracuseStep 3030779 = 4546169) B4546169
theorem B2020519 : Blo 2019435 2020519 := bstep (se 1 (by rfl) ⟨1515389, by rfl⟩ : syracuseStep 2020519 = 3030779) B3030779
theorem B2273089 : Blo 2019435 2273089 := bbase (se 2 (by rfl) ⟨852408, by rfl⟩ : syracuseStep 2273089 = 1704817) (by norm_num)
theorem B3030785 : Blo 2019435 3030785 := bstep (se 2 (by rfl) ⟨1136544, by rfl⟩ : syracuseStep 3030785 = 2273089) B2273089
theorem B2020523 : Blo 2019435 2020523 := bstep (se 1 (by rfl) ⟨1515392, by rfl⟩ : syracuseStep 2020523 = 3030785) B3030785
theorem B5114461 : Blo 2019435 5114461 := bbase (se 3 (by rfl) ⟨958961, by rfl⟩ : syracuseStep 5114461 = 1917923) (by norm_num)
theorem B6819281 : Blo 2019435 6819281 := bstep (se 2 (by rfl) ⟨2557230, by rfl⟩ : syracuseStep 6819281 = 5114461) B5114461
theorem B4546187 : Blo 2019435 4546187 := bstep (se 1 (by rfl) ⟨3409640, by rfl⟩ : syracuseStep 4546187 = 6819281) B6819281
theorem B3030791 : Blo 2019435 3030791 := bstep (se 1 (by rfl) ⟨2273093, by rfl⟩ : syracuseStep 3030791 = 4546187) B4546187
theorem B2020527 : Blo 2019435 2020527 := bstep (se 1 (by rfl) ⟨1515395, by rfl⟩ : syracuseStep 2020527 = 3030791) B3030791
theorem B3030797 : Blo 2019435 3030797 := bbase (se 3 (by rfl) ⟨568274, by rfl⟩ : syracuseStep 3030797 = 1136549) (by norm_num)
theorem B2020531 : Blo 2019435 2020531 := bstep (se 1 (by rfl) ⟨1515398, by rfl⟩ : syracuseStep 2020531 = 3030797) B3030797
theorem B4546205 : Blo 2019435 4546205 := bbase (se 3 (by rfl) ⟨852413, by rfl⟩ : syracuseStep 4546205 = 1704827) (by norm_num)
theorem B3030803 : Blo 2019435 3030803 := bstep (se 1 (by rfl) ⟨2273102, by rfl⟩ : syracuseStep 3030803 = 4546205) B4546205
theorem B2020535 : Blo 2019435 2020535 := bstep (se 1 (by rfl) ⟨1515401, by rfl⟩ : syracuseStep 2020535 = 3030803) B3030803
theorem B3409661 : Blo 2019435 3409661 := bbase (se 3 (by rfl) ⟨639311, by rfl⟩ : syracuseStep 3409661 = 1278623) (by norm_num)
theorem B2273107 : Blo 2019435 2273107 := bstep (se 1 (by rfl) ⟨1704830, by rfl⟩ : syracuseStep 2273107 = 3409661) B3409661
theorem B3030809 : Blo 2019435 3030809 := bstep (se 2 (by rfl) ⟨1136553, by rfl⟩ : syracuseStep 3030809 = 2273107) B2273107
theorem B2020539 : Blo 2019435 2020539 := bstep (se 1 (by rfl) ⟨1515404, by rfl⟩ : syracuseStep 2020539 = 3030809) B3030809
theorem B4671125 : Blo 2019435 4671125 := bbase (se 6 (by rfl) ⟨109479, by rfl⟩ : syracuseStep 4671125 = 218959) (by norm_num)
theorem B3114083 : Blo 2019435 3114083 := bstep (se 1 (by rfl) ⟨2335562, by rfl⟩ : syracuseStep 3114083 = 4671125) B4671125
theorem B2076055 : Blo 2019435 2076055 := bstep (se 1 (by rfl) ⟨1557041, by rfl⟩ : syracuseStep 2076055 = 3114083) B3114083
theorem B44289173 : Blo 2019435 44289173 := bstep (se 6 (by rfl) ⟨1038027, by rfl⟩ : syracuseStep 44289173 = 2076055) B2076055
theorem B29526115 : Blo 2019435 29526115 := bstep (se 1 (by rfl) ⟨22144586, by rfl⟩ : syracuseStep 29526115 = 44289173) B44289173
theorem B39368153 : Blo 2019435 39368153 := bstep (se 2 (by rfl) ⟨14763057, by rfl⟩ : syracuseStep 39368153 = 29526115) B29526115
theorem B104981741 : Blo 2019435 104981741 := bstep (se 3 (by rfl) ⟨19684076, by rfl⟩ : syracuseStep 104981741 = 39368153) B39368153
theorem B69987827 : Blo 2019435 69987827 := bstep (se 1 (by rfl) ⟨52490870, by rfl⟩ : syracuseStep 69987827 = 104981741) B104981741
theorem B46658551 : Blo 2019435 46658551 := bstep (se 1 (by rfl) ⟨34993913, by rfl⟩ : syracuseStep 46658551 = 69987827) B69987827
theorem B62211401 : Blo 2019435 62211401 := bstep (se 2 (by rfl) ⟨23329275, by rfl⟩ : syracuseStep 62211401 = 46658551) B46658551
theorem B41474267 : Blo 2019435 41474267 := bstep (se 1 (by rfl) ⟨31105700, by rfl⟩ : syracuseStep 41474267 = 62211401) B62211401
theorem B27649511 : Blo 2019435 27649511 := bstep (se 1 (by rfl) ⟨20737133, by rfl⟩ : syracuseStep 27649511 = 41474267) B41474267
theorem B18433007 : Blo 2019435 18433007 := bstep (se 1 (by rfl) ⟨13824755, by rfl⟩ : syracuseStep 18433007 = 27649511) B27649511
theorem B12288671 : Blo 2019435 12288671 := bstep (se 1 (by rfl) ⟨9216503, by rfl⟩ : syracuseStep 12288671 = 18433007) B18433007
theorem B8192447 : Blo 2019435 8192447 := bstep (se 1 (by rfl) ⟨6144335, by rfl⟩ : syracuseStep 8192447 = 12288671) B12288671
theorem B5461631 : Blo 2019435 5461631 := bstep (se 1 (by rfl) ⟨4096223, by rfl⟩ : syracuseStep 5461631 = 8192447) B8192447
theorem B3641087 : Blo 2019435 3641087 := bstep (se 1 (by rfl) ⟨2730815, by rfl⟩ : syracuseStep 3641087 = 5461631) B5461631
theorem B2427391 : Blo 2019435 2427391 := bstep (se 1 (by rfl) ⟨1820543, by rfl⟩ : syracuseStep 2427391 = 3641087) B3641087
theorem B3236521 : Blo 2019435 3236521 := bstep (se 2 (by rfl) ⟨1213695, by rfl⟩ : syracuseStep 3236521 = 2427391) B2427391
theorem B4315361 : Blo 2019435 4315361 := bstep (se 2 (by rfl) ⟨1618260, by rfl⟩ : syracuseStep 4315361 = 3236521) B3236521
theorem B11507629 : Blo 2019435 11507629 := bstep (se 3 (by rfl) ⟨2157680, by rfl⟩ : syracuseStep 11507629 = 4315361) B4315361
theorem B15343505 : Blo 2019435 15343505 := bstep (se 2 (by rfl) ⟨5753814, by rfl⟩ : syracuseStep 15343505 = 11507629) B11507629
theorem B10229003 : Blo 2019435 10229003 := bstep (se 1 (by rfl) ⟨7671752, by rfl⟩ : syracuseStep 10229003 = 15343505) B15343505
theorem B6819335 : Blo 2019435 6819335 := bstep (se 1 (by rfl) ⟨5114501, by rfl⟩ : syracuseStep 6819335 = 10229003) B10229003
theorem B4546223 : Blo 2019435 4546223 := bstep (se 1 (by rfl) ⟨3409667, by rfl⟩ : syracuseStep 4546223 = 6819335) B6819335
theorem B3030815 : Blo 2019435 3030815 := bstep (se 1 (by rfl) ⟨2273111, by rfl⟩ : syracuseStep 3030815 = 4546223) B4546223
theorem B2020543 : Blo 2019435 2020543 := bstep (se 1 (by rfl) ⟨1515407, by rfl⟩ : syracuseStep 2020543 = 3030815) B3030815
theorem B3030821 : Blo 2019435 3030821 := bbase (se 4 (by rfl) ⟨284139, by rfl⟩ : syracuseStep 3030821 = 568279) (by norm_num)
theorem B2020547 : Blo 2019435 2020547 := bstep (se 1 (by rfl) ⟨1515410, by rfl⟩ : syracuseStep 2020547 = 3030821) B3030821
theorem B2557261 : Blo 2019435 2557261 := bbase (se 3 (by rfl) ⟨479486, by rfl⟩ : syracuseStep 2557261 = 958973) (by norm_num)
theorem B3409681 : Blo 2019435 3409681 := bstep (se 2 (by rfl) ⟨1278630, by rfl⟩ : syracuseStep 3409681 = 2557261) B2557261
theorem B4546241 : Blo 2019435 4546241 := bstep (se 2 (by rfl) ⟨1704840, by rfl⟩ : syracuseStep 4546241 = 3409681) B3409681
theorem B3030827 : Blo 2019435 3030827 := bstep (se 1 (by rfl) ⟨2273120, by rfl⟩ : syracuseStep 3030827 = 4546241) B4546241
theorem B2020551 : Blo 2019435 2020551 := bstep (se 1 (by rfl) ⟨1515413, by rfl⟩ : syracuseStep 2020551 = 3030827) B3030827
theorem B2273125 : Blo 2019435 2273125 := bbase (se 4 (by rfl) ⟨213105, by rfl⟩ : syracuseStep 2273125 = 426211) (by norm_num)
theorem B3030833 : Blo 2019435 3030833 := bstep (se 2 (by rfl) ⟨1136562, by rfl⟩ : syracuseStep 3030833 = 2273125) B2273125
theorem B2020555 : Blo 2019435 2020555 := bstep (se 1 (by rfl) ⟨1515416, by rfl⟩ : syracuseStep 2020555 = 3030833) B3030833
theorem B5753861 : Blo 2019435 5753861 := bbase (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) (by norm_num)
theorem B3835907 : Blo 2019435 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B2557271 : Blo 2019435 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B6819389 : Blo 2019435 6819389 := bstep (se 3 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 6819389 = 2557271) B2557271
theorem B4546259 : Blo 2019435 4546259 := bstep (se 1 (by rfl) ⟨3409694, by rfl⟩ : syracuseStep 4546259 = 6819389) B6819389
theorem B3030839 : Blo 2019435 3030839 := bstep (se 1 (by rfl) ⟨2273129, by rfl⟩ : syracuseStep 3030839 = 4546259) B4546259
theorem B2020559 : Blo 2019435 2020559 := bstep (se 1 (by rfl) ⟨1515419, by rfl⟩ : syracuseStep 2020559 = 3030839) B3030839
theorem B3030845 : Blo 2019435 3030845 := bbase (se 3 (by rfl) ⟨568283, by rfl⟩ : syracuseStep 3030845 = 1136567) (by norm_num)
theorem B2020563 : Blo 2019435 2020563 := bstep (se 1 (by rfl) ⟨1515422, by rfl⟩ : syracuseStep 2020563 = 3030845) B3030845
theorem B4546277 : Blo 2019435 4546277 := bbase (se 4 (by rfl) ⟨426213, by rfl⟩ : syracuseStep 4546277 = 852427) (by norm_num)
theorem B3030851 : Blo 2019435 3030851 := bstep (se 1 (by rfl) ⟨2273138, by rfl⟩ : syracuseStep 3030851 = 4546277) B4546277
theorem B2020567 : Blo 2019435 2020567 := bstep (se 1 (by rfl) ⟨1515425, by rfl⟩ : syracuseStep 2020567 = 3030851) B3030851
theorem B5114573 : Blo 2019435 5114573 := bbase (se 3 (by rfl) ⟨958982, by rfl⟩ : syracuseStep 5114573 = 1917965) (by norm_num)
theorem B3409715 : Blo 2019435 3409715 := bstep (se 1 (by rfl) ⟨2557286, by rfl⟩ : syracuseStep 3409715 = 5114573) B5114573
theorem B2273143 : Blo 2019435 2273143 := bstep (se 1 (by rfl) ⟨1704857, by rfl⟩ : syracuseStep 2273143 = 3409715) B3409715
theorem B3030857 : Blo 2019435 3030857 := bstep (se 2 (by rfl) ⟨1136571, by rfl⟩ : syracuseStep 3030857 = 2273143) B2273143
theorem B2020571 : Blo 2019435 2020571 := bstep (se 1 (by rfl) ⟨1515428, by rfl⟩ : syracuseStep 2020571 = 3030857) B3030857
theorem B3236573 : Blo 2019435 3236573 := bbase (se 3 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 3236573 = 1213715) (by norm_num)
theorem B2157715 : Blo 2019435 2157715 := bstep (se 1 (by rfl) ⟨1618286, by rfl⟩ : syracuseStep 2157715 = 3236573) B3236573
theorem B2876953 : Blo 2019435 2876953 := bstep (se 2 (by rfl) ⟨1078857, by rfl⟩ : syracuseStep 2876953 = 2157715) B2157715
theorem B3835937 : Blo 2019435 3835937 := bstep (se 2 (by rfl) ⟨1438476, by rfl⟩ : syracuseStep 3835937 = 2876953) B2876953
theorem B10229165 : Blo 2019435 10229165 := bstep (se 3 (by rfl) ⟨1917968, by rfl⟩ : syracuseStep 10229165 = 3835937) B3835937
theorem B6819443 : Blo 2019435 6819443 := bstep (se 1 (by rfl) ⟨5114582, by rfl⟩ : syracuseStep 6819443 = 10229165) B10229165
theorem B4546295 : Blo 2019435 4546295 := bstep (se 1 (by rfl) ⟨3409721, by rfl⟩ : syracuseStep 4546295 = 6819443) B6819443
theorem B3030863 : Blo 2019435 3030863 := bstep (se 1 (by rfl) ⟨2273147, by rfl⟩ : syracuseStep 3030863 = 4546295) B4546295
theorem B2020575 : Blo 2019435 2020575 := bstep (se 1 (by rfl) ⟨1515431, by rfl⟩ : syracuseStep 2020575 = 3030863) B3030863
theorem B3030869 : Blo 2019435 3030869 := bbase (se 9 (by rfl) ⟨8879, by rfl⟩ : syracuseStep 3030869 = 17759) (by norm_num)
theorem B2020579 : Blo 2019435 2020579 := bstep (se 1 (by rfl) ⟨1515434, by rfl⟩ : syracuseStep 2020579 = 3030869) B3030869
theorem B10368773 : Blo 2019435 10368773 := bbase (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) (by norm_num)
theorem B6912515 : Blo 2019435 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B4608343 : Blo 2019435 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B6144457 : Blo 2019435 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B8192609 : Blo 2019435 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B5461739 : Blo 2019435 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B3641159 : Blo 2019435 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B9709757 : Blo 2019435 9709757 := bstep (se 3 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 9709757 = 3641159) B3641159
theorem B6473171 : Blo 2019435 6473171 := bstep (se 1 (by rfl) ⟨4854878, by rfl⟩ : syracuseStep 6473171 = 9709757) B9709757
theorem B4315447 : Blo 2019435 4315447 := bstep (se 1 (by rfl) ⟨3236585, by rfl⟩ : syracuseStep 4315447 = 6473171) B6473171
theorem B5753929 : Blo 2019435 5753929 := bstep (se 2 (by rfl) ⟨2157723, by rfl⟩ : syracuseStep 5753929 = 4315447) B4315447
theorem B7671905 : Blo 2019435 7671905 := bstep (se 2 (by rfl) ⟨2876964, by rfl⟩ : syracuseStep 7671905 = 5753929) B5753929
theorem B5114603 : Blo 2019435 5114603 := bstep (se 1 (by rfl) ⟨3835952, by rfl⟩ : syracuseStep 5114603 = 7671905) B7671905
theorem B3409735 : Blo 2019435 3409735 := bstep (se 1 (by rfl) ⟨2557301, by rfl⟩ : syracuseStep 3409735 = 5114603) B5114603
theorem B4546313 : Blo 2019435 4546313 := bstep (se 2 (by rfl) ⟨1704867, by rfl⟩ : syracuseStep 4546313 = 3409735) B3409735
theorem B3030875 : Blo 2019435 3030875 := bstep (se 1 (by rfl) ⟨2273156, by rfl⟩ : syracuseStep 3030875 = 4546313) B4546313
theorem B2020583 : Blo 2019435 2020583 := bstep (se 1 (by rfl) ⟨1515437, by rfl⟩ : syracuseStep 2020583 = 3030875) B3030875
theorem B2273161 : Blo 2019435 2273161 := bbase (se 2 (by rfl) ⟨852435, by rfl⟩ : syracuseStep 2273161 = 1704871) (by norm_num)
theorem B3030881 : Blo 2019435 3030881 := bstep (se 2 (by rfl) ⟨1136580, by rfl⟩ : syracuseStep 3030881 = 2273161) B2273161
theorem B2020587 : Blo 2019435 2020587 := bstep (se 1 (by rfl) ⟨1515440, by rfl⟩ : syracuseStep 2020587 = 3030881) B3030881
theorem B5536277 : Blo 2019435 5536277 := bbase (se 6 (by rfl) ⟨129756, by rfl⟩ : syracuseStep 5536277 = 259513) (by norm_num)
theorem B3690851 : Blo 2019435 3690851 := bstep (se 1 (by rfl) ⟨2768138, by rfl⟩ : syracuseStep 3690851 = 5536277) B5536277
theorem B39369077 : Blo 2019435 39369077 := bstep (se 5 (by rfl) ⟨1845425, by rfl⟩ : syracuseStep 39369077 = 3690851) B3690851
theorem B26246051 : Blo 2019435 26246051 := bstep (se 1 (by rfl) ⟨19684538, by rfl⟩ : syracuseStep 26246051 = 39369077) B39369077
theorem B17497367 : Blo 2019435 17497367 := bstep (se 1 (by rfl) ⟨13123025, by rfl⟩ : syracuseStep 17497367 = 26246051) B26246051
theorem B11664911 : Blo 2019435 11664911 := bstep (se 1 (by rfl) ⟨8748683, by rfl⟩ : syracuseStep 11664911 = 17497367) B17497367
theorem B31106429 : Blo 2019435 31106429 := bstep (se 3 (by rfl) ⟨5832455, by rfl⟩ : syracuseStep 31106429 = 11664911) B11664911
theorem B20737619 : Blo 2019435 20737619 := bstep (se 1 (by rfl) ⟨15553214, by rfl⟩ : syracuseStep 20737619 = 31106429) B31106429
theorem B13825079 : Blo 2019435 13825079 := bstep (se 1 (by rfl) ⟨10368809, by rfl⟩ : syracuseStep 13825079 = 20737619) B20737619
theorem B9216719 : Blo 2019435 9216719 := bstep (se 1 (by rfl) ⟨6912539, by rfl⟩ : syracuseStep 9216719 = 13825079) B13825079
theorem B6144479 : Blo 2019435 6144479 := bstep (se 1 (by rfl) ⟨4608359, by rfl⟩ : syracuseStep 6144479 = 9216719) B9216719
theorem B65541109 : Blo 2019435 65541109 := bstep (se 5 (by rfl) ⟨3072239, by rfl⟩ : syracuseStep 65541109 = 6144479) B6144479
theorem B87388145 : Blo 2019435 87388145 := bstep (se 2 (by rfl) ⟨32770554, by rfl⟩ : syracuseStep 87388145 = 65541109) B65541109
theorem B58258763 : Blo 2019435 58258763 := bstep (se 1 (by rfl) ⟨43694072, by rfl⟩ : syracuseStep 58258763 = 87388145) B87388145
theorem B38839175 : Blo 2019435 38839175 := bstep (se 1 (by rfl) ⟨29129381, by rfl⟩ : syracuseStep 38839175 = 58258763) B58258763
theorem B25892783 : Blo 2019435 25892783 := bstep (se 1 (by rfl) ⟨19419587, by rfl⟩ : syracuseStep 25892783 = 38839175) B38839175
theorem B17261855 : Blo 2019435 17261855 := bstep (se 1 (by rfl) ⟨12946391, by rfl⟩ : syracuseStep 17261855 = 25892783) B25892783
theorem B11507903 : Blo 2019435 11507903 := bstep (se 1 (by rfl) ⟨8630927, by rfl⟩ : syracuseStep 11507903 = 17261855) B17261855
theorem B7671935 : Blo 2019435 7671935 := bstep (se 1 (by rfl) ⟨5753951, by rfl⟩ : syracuseStep 7671935 = 11507903) B11507903
theorem B5114623 : Blo 2019435 5114623 := bstep (se 1 (by rfl) ⟨3835967, by rfl⟩ : syracuseStep 5114623 = 7671935) B7671935
theorem B6819497 : Blo 2019435 6819497 := bstep (se 2 (by rfl) ⟨2557311, by rfl⟩ : syracuseStep 6819497 = 5114623) B5114623
theorem B4546331 : Blo 2019435 4546331 := bstep (se 1 (by rfl) ⟨3409748, by rfl⟩ : syracuseStep 4546331 = 6819497) B6819497
theorem B3030887 : Blo 2019435 3030887 := bstep (se 1 (by rfl) ⟨2273165, by rfl⟩ : syracuseStep 3030887 = 4546331) B4546331
theorem B2020591 : Blo 2019435 2020591 := bstep (se 1 (by rfl) ⟨1515443, by rfl⟩ : syracuseStep 2020591 = 3030887) B3030887
theorem B3030893 : Blo 2019435 3030893 := bbase (se 3 (by rfl) ⟨568292, by rfl⟩ : syracuseStep 3030893 = 1136585) (by norm_num)
theorem B2020595 : Blo 2019435 2020595 := bstep (se 1 (by rfl) ⟨1515446, by rfl⟩ : syracuseStep 2020595 = 3030893) B3030893
theorem B4546349 : Blo 2019435 4546349 := bbase (se 3 (by rfl) ⟨852440, by rfl⟩ : syracuseStep 4546349 = 1704881) (by norm_num)
theorem B3030899 : Blo 2019435 3030899 := bstep (se 1 (by rfl) ⟨2273174, by rfl⟩ : syracuseStep 3030899 = 4546349) B4546349
theorem B2020599 : Blo 2019435 2020599 := bstep (se 1 (by rfl) ⟨1515449, by rfl⟩ : syracuseStep 2020599 = 3030899) B3030899
theorem B8630981 : Blo 2019435 8630981 := bbase (se 4 (by rfl) ⟨809154, by rfl⟩ : syracuseStep 8630981 = 1618309) (by norm_num)
theorem B5753987 : Blo 2019435 5753987 := bstep (se 1 (by rfl) ⟨4315490, by rfl⟩ : syracuseStep 5753987 = 8630981) B8630981
theorem B3835991 : Blo 2019435 3835991 := bstep (se 1 (by rfl) ⟨2876993, by rfl⟩ : syracuseStep 3835991 = 5753987) B5753987
theorem B2557327 : Blo 2019435 2557327 := bstep (se 1 (by rfl) ⟨1917995, by rfl⟩ : syracuseStep 2557327 = 3835991) B3835991
theorem B3409769 : Blo 2019435 3409769 := bstep (se 2 (by rfl) ⟨1278663, by rfl⟩ : syracuseStep 3409769 = 2557327) B2557327
theorem B2273179 : Blo 2019435 2273179 := bstep (se 1 (by rfl) ⟨1704884, by rfl⟩ : syracuseStep 2273179 = 3409769) B3409769
theorem B3030905 : Blo 2019435 3030905 := bstep (se 2 (by rfl) ⟨1136589, by rfl⟩ : syracuseStep 3030905 = 2273179) B2273179
theorem B2020603 : Blo 2019435 2020603 := bstep (se 1 (by rfl) ⟨1515452, by rfl⟩ : syracuseStep 2020603 = 3030905) B3030905
theorem B10923605 : Blo 2019435 10923605 := bbase (se 8 (by rfl) ⟨64005, by rfl⟩ : syracuseStep 10923605 = 128011) (by norm_num)
theorem B7282403 : Blo 2019435 7282403 := bstep (se 1 (by rfl) ⟨5461802, by rfl⟩ : syracuseStep 7282403 = 10923605) B10923605
theorem B4854935 : Blo 2019435 4854935 := bstep (se 1 (by rfl) ⟨3641201, by rfl⟩ : syracuseStep 4854935 = 7282403) B7282403
theorem B12946493 : Blo 2019435 12946493 := bstep (se 3 (by rfl) ⟨2427467, by rfl⟩ : syracuseStep 12946493 = 4854935) B4854935
theorem B34523981 : Blo 2019435 34523981 := bstep (se 3 (by rfl) ⟨6473246, by rfl⟩ : syracuseStep 34523981 = 12946493) B12946493
theorem B23015987 : Blo 2019435 23015987 := bstep (se 1 (by rfl) ⟨17261990, by rfl⟩ : syracuseStep 23015987 = 34523981) B34523981
theorem B15343991 : Blo 2019435 15343991 := bstep (se 1 (by rfl) ⟨11507993, by rfl⟩ : syracuseStep 15343991 = 23015987) B23015987
theorem B10229327 : Blo 2019435 10229327 := bstep (se 1 (by rfl) ⟨7671995, by rfl⟩ : syracuseStep 10229327 = 15343991) B15343991
theorem B6819551 : Blo 2019435 6819551 := bstep (se 1 (by rfl) ⟨5114663, by rfl⟩ : syracuseStep 6819551 = 10229327) B10229327
theorem B4546367 : Blo 2019435 4546367 := bstep (se 1 (by rfl) ⟨3409775, by rfl⟩ : syracuseStep 4546367 = 6819551) B6819551
theorem B3030911 : Blo 2019435 3030911 := bstep (se 1 (by rfl) ⟨2273183, by rfl⟩ : syracuseStep 3030911 = 4546367) B4546367
theorem B2020607 : Blo 2019435 2020607 := bstep (se 1 (by rfl) ⟨1515455, by rfl⟩ : syracuseStep 2020607 = 3030911) B3030911
theorem B3030917 : Blo 2019435 3030917 := bbase (se 4 (by rfl) ⟨284148, by rfl⟩ : syracuseStep 3030917 = 568297) (by norm_num)
theorem B2020611 : Blo 2019435 2020611 := bstep (se 1 (by rfl) ⟨1515458, by rfl⟩ : syracuseStep 2020611 = 3030917) B3030917
theorem B3409789 : Blo 2019435 3409789 := bbase (se 3 (by rfl) ⟨639335, by rfl⟩ : syracuseStep 3409789 = 1278671) (by norm_num)
theorem B4546385 : Blo 2019435 4546385 := bstep (se 2 (by rfl) ⟨1704894, by rfl⟩ : syracuseStep 4546385 = 3409789) B3409789
theorem B3030923 : Blo 2019435 3030923 := bstep (se 1 (by rfl) ⟨2273192, by rfl⟩ : syracuseStep 3030923 = 4546385) B4546385
theorem B2020615 : Blo 2019435 2020615 := bstep (se 1 (by rfl) ⟨1515461, by rfl⟩ : syracuseStep 2020615 = 3030923) B3030923
theorem B2273197 : Blo 2019435 2273197 := bbase (se 3 (by rfl) ⟨426224, by rfl⟩ : syracuseStep 2273197 = 852449) (by norm_num)
theorem B3030929 : Blo 2019435 3030929 := bstep (se 2 (by rfl) ⟨1136598, by rfl⟩ : syracuseStep 3030929 = 2273197) B2273197
theorem B2020619 : Blo 2019435 2020619 := bstep (se 1 (by rfl) ⟨1515464, by rfl⟩ : syracuseStep 2020619 = 3030929) B3030929
theorem B6819605 : Blo 2019435 6819605 := bbase (se 6 (by rfl) ⟨159834, by rfl⟩ : syracuseStep 6819605 = 319669) (by norm_num)
theorem B4546403 : Blo 2019435 4546403 := bstep (se 1 (by rfl) ⟨3409802, by rfl⟩ : syracuseStep 4546403 = 6819605) B6819605
theorem B3030935 : Blo 2019435 3030935 := bstep (se 1 (by rfl) ⟨2273201, by rfl⟩ : syracuseStep 3030935 = 4546403) B4546403
theorem B2020623 : Blo 2019435 2020623 := bstep (se 1 (by rfl) ⟨1515467, by rfl⟩ : syracuseStep 2020623 = 3030935) B3030935
theorem B3030941 : Blo 2019435 3030941 := bbase (se 3 (by rfl) ⟨568301, by rfl⟩ : syracuseStep 3030941 = 1136603) (by norm_num)
theorem B2020627 : Blo 2019435 2020627 := bstep (se 1 (by rfl) ⟨1515470, by rfl⟩ : syracuseStep 2020627 = 3030941) B3030941
theorem B4546421 : Blo 2019435 4546421 := bbase (se 5 (by rfl) ⟨213113, by rfl⟩ : syracuseStep 4546421 = 426227) (by norm_num)
theorem B3030947 : Blo 2019435 3030947 := bstep (se 1 (by rfl) ⟨2273210, by rfl⟩ : syracuseStep 3030947 = 4546421) B4546421
theorem B2020631 : Blo 2019435 2020631 := bstep (se 1 (by rfl) ⟨1515473, by rfl⟩ : syracuseStep 2020631 = 3030947) B3030947
theorem B4608461 : Blo 2019435 4608461 := bbase (se 3 (by rfl) ⟨864086, by rfl⟩ : syracuseStep 4608461 = 1728173) (by norm_num)
theorem B12289229 : Blo 2019435 12289229 := bstep (se 3 (by rfl) ⟨2304230, by rfl⟩ : syracuseStep 12289229 = 4608461) B4608461
theorem B8192819 : Blo 2019435 8192819 := bstep (se 1 (by rfl) ⟨6144614, by rfl⟩ : syracuseStep 8192819 = 12289229) B12289229
theorem B5461879 : Blo 2019435 5461879 := bstep (se 1 (by rfl) ⟨4096409, by rfl⟩ : syracuseStep 5461879 = 8192819) B8192819
theorem B7282505 : Blo 2019435 7282505 := bstep (se 2 (by rfl) ⟨2730939, by rfl⟩ : syracuseStep 7282505 = 5461879) B5461879
theorem B19420013 : Blo 2019435 19420013 := bstep (se 3 (by rfl) ⟨3641252, by rfl⟩ : syracuseStep 19420013 = 7282505) B7282505
theorem B12946675 : Blo 2019435 12946675 := bstep (se 1 (by rfl) ⟨9710006, by rfl⟩ : syracuseStep 12946675 = 19420013) B19420013
theorem B17262233 : Blo 2019435 17262233 := bstep (se 2 (by rfl) ⟨6473337, by rfl⟩ : syracuseStep 17262233 = 12946675) B12946675
theorem B11508155 : Blo 2019435 11508155 := bstep (se 1 (by rfl) ⟨8631116, by rfl⟩ : syracuseStep 11508155 = 17262233) B17262233
theorem B7672103 : Blo 2019435 7672103 := bstep (se 1 (by rfl) ⟨5754077, by rfl⟩ : syracuseStep 7672103 = 11508155) B11508155
theorem B5114735 : Blo 2019435 5114735 := bstep (se 1 (by rfl) ⟨3836051, by rfl⟩ : syracuseStep 5114735 = 7672103) B7672103
theorem B3409823 : Blo 2019435 3409823 := bstep (se 1 (by rfl) ⟨2557367, by rfl⟩ : syracuseStep 3409823 = 5114735) B5114735
theorem B2273215 : Blo 2019435 2273215 := bstep (se 1 (by rfl) ⟨1704911, by rfl⟩ : syracuseStep 2273215 = 3409823) B3409823
theorem B3030953 : Blo 2019435 3030953 := bstep (se 2 (by rfl) ⟨1136607, by rfl⟩ : syracuseStep 3030953 = 2273215) B2273215
theorem B2020635 : Blo 2019435 2020635 := bstep (se 1 (by rfl) ⟨1515476, by rfl⟩ : syracuseStep 2020635 = 3030953) B3030953
theorem B7672117 : Blo 2019435 7672117 := bbase (se 5 (by rfl) ⟨359630, by rfl⟩ : syracuseStep 7672117 = 719261) (by norm_num)
theorem B10229489 : Blo 2019435 10229489 := bstep (se 2 (by rfl) ⟨3836058, by rfl⟩ : syracuseStep 10229489 = 7672117) B7672117
theorem B6819659 : Blo 2019435 6819659 := bstep (se 1 (by rfl) ⟨5114744, by rfl⟩ : syracuseStep 6819659 = 10229489) B10229489
theorem B4546439 : Blo 2019435 4546439 := bstep (se 1 (by rfl) ⟨3409829, by rfl⟩ : syracuseStep 4546439 = 6819659) B6819659
theorem B3030959 : Blo 2019435 3030959 := bstep (se 1 (by rfl) ⟨2273219, by rfl⟩ : syracuseStep 3030959 = 4546439) B4546439
theorem B2020639 : Blo 2019435 2020639 := bstep (se 1 (by rfl) ⟨1515479, by rfl⟩ : syracuseStep 2020639 = 3030959) B3030959
theorem B3030965 : Blo 2019435 3030965 := bbase (se 5 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 3030965 = 284153) (by norm_num)
theorem B2020643 : Blo 2019435 2020643 := bstep (se 1 (by rfl) ⟨1515482, by rfl⟩ : syracuseStep 2020643 = 3030965) B3030965
theorem B5114765 : Blo 2019435 5114765 := bbase (se 3 (by rfl) ⟨959018, by rfl⟩ : syracuseStep 5114765 = 1918037) (by norm_num)
theorem B3409843 : Blo 2019435 3409843 := bstep (se 1 (by rfl) ⟨2557382, by rfl⟩ : syracuseStep 3409843 = 5114765) B5114765
theorem B4546457 : Blo 2019435 4546457 := bstep (se 2 (by rfl) ⟨1704921, by rfl⟩ : syracuseStep 4546457 = 3409843) B3409843
theorem B3030971 : Blo 2019435 3030971 := bstep (se 1 (by rfl) ⟨2273228, by rfl⟩ : syracuseStep 3030971 = 4546457) B4546457
theorem B2020647 : Blo 2019435 2020647 := bstep (se 1 (by rfl) ⟨1515485, by rfl⟩ : syracuseStep 2020647 = 3030971) B3030971
theorem B2273233 : Blo 2019435 2273233 := bbase (se 2 (by rfl) ⟨852462, by rfl⟩ : syracuseStep 2273233 = 1704925) (by norm_num)
theorem B3030977 : Blo 2019435 3030977 := bstep (se 2 (by rfl) ⟨1136616, by rfl⟩ : syracuseStep 3030977 = 2273233) B2273233
theorem B2020651 : Blo 2019435 2020651 := bstep (se 1 (by rfl) ⟨1515488, by rfl⟩ : syracuseStep 2020651 = 3030977) B3030977
theorem B3236701 : Blo 2019435 3236701 := bbase (se 3 (by rfl) ⟨606881, by rfl⟩ : syracuseStep 3236701 = 1213763) (by norm_num)
theorem B4315601 : Blo 2019435 4315601 := bstep (se 2 (by rfl) ⟨1618350, by rfl⟩ : syracuseStep 4315601 = 3236701) B3236701
theorem B2877067 : Blo 2019435 2877067 := bstep (se 1 (by rfl) ⟨2157800, by rfl⟩ : syracuseStep 2877067 = 4315601) B4315601
theorem B3836089 : Blo 2019435 3836089 := bstep (se 2 (by rfl) ⟨1438533, by rfl⟩ : syracuseStep 3836089 = 2877067) B2877067
theorem B5114785 : Blo 2019435 5114785 := bstep (se 2 (by rfl) ⟨1918044, by rfl⟩ : syracuseStep 5114785 = 3836089) B3836089
theorem B6819713 : Blo 2019435 6819713 := bstep (se 2 (by rfl) ⟨2557392, by rfl⟩ : syracuseStep 6819713 = 5114785) B5114785
theorem B4546475 : Blo 2019435 4546475 := bstep (se 1 (by rfl) ⟨3409856, by rfl⟩ : syracuseStep 4546475 = 6819713) B6819713
theorem B3030983 : Blo 2019435 3030983 := bstep (se 1 (by rfl) ⟨2273237, by rfl⟩ : syracuseStep 3030983 = 4546475) B4546475
theorem B2020655 : Blo 2019435 2020655 := bstep (se 1 (by rfl) ⟨1515491, by rfl⟩ : syracuseStep 2020655 = 3030983) B3030983
theorem B3030989 : Blo 2019435 3030989 := bbase (se 3 (by rfl) ⟨568310, by rfl⟩ : syracuseStep 3030989 = 1136621) (by norm_num)
theorem B2020659 : Blo 2019435 2020659 := bstep (se 1 (by rfl) ⟨1515494, by rfl⟩ : syracuseStep 2020659 = 3030989) B3030989
theorem B4546493 : Blo 2019435 4546493 := bbase (se 3 (by rfl) ⟨852467, by rfl⟩ : syracuseStep 4546493 = 1704935) (by norm_num)
theorem B3030995 : Blo 2019435 3030995 := bstep (se 1 (by rfl) ⟨2273246, by rfl⟩ : syracuseStep 3030995 = 4546493) B4546493
theorem B2020663 : Blo 2019435 2020663 := bstep (se 1 (by rfl) ⟨1515497, by rfl⟩ : syracuseStep 2020663 = 3030995) B3030995
theorem B3409877 : Blo 2019435 3409877 := bbase (se 7 (by rfl) ⟨39959, by rfl⟩ : syracuseStep 3409877 = 79919) (by norm_num)
theorem B2273251 : Blo 2019435 2273251 := bstep (se 1 (by rfl) ⟨1704938, by rfl⟩ : syracuseStep 2273251 = 3409877) B3409877
theorem B3031001 : Blo 2019435 3031001 := bstep (se 2 (by rfl) ⟨1136625, by rfl⟩ : syracuseStep 3031001 = 2273251) B2273251
theorem B2020667 : Blo 2019435 2020667 := bstep (se 1 (by rfl) ⟨1515500, by rfl⟩ : syracuseStep 2020667 = 3031001) B3031001
theorem B8631269 : Blo 2019435 8631269 := bbase (se 4 (by rfl) ⟨809181, by rfl⟩ : syracuseStep 8631269 = 1618363) (by norm_num)
theorem B5754179 : Blo 2019435 5754179 := bstep (se 1 (by rfl) ⟨4315634, by rfl⟩ : syracuseStep 5754179 = 8631269) B8631269
theorem B15344477 : Blo 2019435 15344477 := bstep (se 3 (by rfl) ⟨2877089, by rfl⟩ : syracuseStep 15344477 = 5754179) B5754179
theorem B10229651 : Blo 2019435 10229651 := bstep (se 1 (by rfl) ⟨7672238, by rfl⟩ : syracuseStep 10229651 = 15344477) B15344477
theorem B6819767 : Blo 2019435 6819767 := bstep (se 1 (by rfl) ⟨5114825, by rfl⟩ : syracuseStep 6819767 = 10229651) B10229651
theorem B4546511 : Blo 2019435 4546511 := bstep (se 1 (by rfl) ⟨3409883, by rfl⟩ : syracuseStep 4546511 = 6819767) B6819767
theorem B3031007 : Blo 2019435 3031007 := bstep (se 1 (by rfl) ⟨2273255, by rfl⟩ : syracuseStep 3031007 = 4546511) B4546511
theorem B2020671 : Blo 2019435 2020671 := bstep (se 1 (by rfl) ⟨1515503, by rfl⟩ : syracuseStep 2020671 = 3031007) B3031007
theorem B3031013 : Blo 2019435 3031013 := bbase (se 4 (by rfl) ⟨284157, by rfl⟩ : syracuseStep 3031013 = 568315) (by norm_num)
theorem B2020675 : Blo 2019435 2020675 := bstep (se 1 (by rfl) ⟨1515506, by rfl⟩ : syracuseStep 2020675 = 3031013) B3031013
theorem B2304281 : Blo 2019435 2304281 := bbase (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) (by norm_num)
theorem B6144749 : Blo 2019435 6144749 := bstep (se 3 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 6144749 = 2304281) B2304281
theorem B4096499 : Blo 2019435 4096499 := bstep (se 1 (by rfl) ⟨3072374, by rfl⟩ : syracuseStep 4096499 = 6144749) B6144749
theorem B10923997 : Blo 2019435 10923997 := bstep (se 3 (by rfl) ⟨2048249, by rfl⟩ : syracuseStep 10923997 = 4096499) B4096499
theorem B14565329 : Blo 2019435 14565329 := bstep (se 2 (by rfl) ⟨5461998, by rfl⟩ : syracuseStep 14565329 = 10923997) B10923997
theorem B9710219 : Blo 2019435 9710219 := bstep (se 1 (by rfl) ⟨7282664, by rfl⟩ : syracuseStep 9710219 = 14565329) B14565329
theorem B6473479 : Blo 2019435 6473479 := bstep (se 1 (by rfl) ⟨4855109, by rfl⟩ : syracuseStep 6473479 = 9710219) B9710219
theorem B8631305 : Blo 2019435 8631305 := bstep (se 2 (by rfl) ⟨3236739, by rfl⟩ : syracuseStep 8631305 = 6473479) B6473479
theorem B5754203 : Blo 2019435 5754203 := bstep (se 1 (by rfl) ⟨4315652, by rfl⟩ : syracuseStep 5754203 = 8631305) B8631305
theorem B3836135 : Blo 2019435 3836135 := bstep (se 1 (by rfl) ⟨2877101, by rfl⟩ : syracuseStep 3836135 = 5754203) B5754203
theorem B2557423 : Blo 2019435 2557423 := bstep (se 1 (by rfl) ⟨1918067, by rfl⟩ : syracuseStep 2557423 = 3836135) B3836135
theorem B3409897 : Blo 2019435 3409897 := bstep (se 2 (by rfl) ⟨1278711, by rfl⟩ : syracuseStep 3409897 = 2557423) B2557423
theorem B4546529 : Blo 2019435 4546529 := bstep (se 2 (by rfl) ⟨1704948, by rfl⟩ : syracuseStep 4546529 = 3409897) B3409897
theorem B3031019 : Blo 2019435 3031019 := bstep (se 1 (by rfl) ⟨2273264, by rfl⟩ : syracuseStep 3031019 = 4546529) B4546529
theorem B2020679 : Blo 2019435 2020679 := bstep (se 1 (by rfl) ⟨1515509, by rfl⟩ : syracuseStep 2020679 = 3031019) B3031019
theorem B2273269 : Blo 2019435 2273269 := bbase (se 5 (by rfl) ⟨106559, by rfl⟩ : syracuseStep 2273269 = 213119) (by norm_num)
theorem B3031025 : Blo 2019435 3031025 := bstep (se 2 (by rfl) ⟨1136634, by rfl⟩ : syracuseStep 3031025 = 2273269) B2273269
theorem B2020683 : Blo 2019435 2020683 := bstep (se 1 (by rfl) ⟨1515512, by rfl⟩ : syracuseStep 2020683 = 3031025) B3031025
theorem B2557433 : Blo 2019435 2557433 := bbase (se 2 (by rfl) ⟨959037, by rfl⟩ : syracuseStep 2557433 = 1918075) (by norm_num)
theorem B6819821 : Blo 2019435 6819821 := bstep (se 3 (by rfl) ⟨1278716, by rfl⟩ : syracuseStep 6819821 = 2557433) B2557433
theorem B4546547 : Blo 2019435 4546547 := bstep (se 1 (by rfl) ⟨3409910, by rfl⟩ : syracuseStep 4546547 = 6819821) B6819821
theorem B3031031 : Blo 2019435 3031031 := bstep (se 1 (by rfl) ⟨2273273, by rfl⟩ : syracuseStep 3031031 = 4546547) B4546547
theorem B2020687 : Blo 2019435 2020687 := bstep (se 1 (by rfl) ⟨1515515, by rfl⟩ : syracuseStep 2020687 = 3031031) B3031031
theorem B3031037 : Blo 2019435 3031037 := bbase (se 3 (by rfl) ⟨568319, by rfl⟩ : syracuseStep 3031037 = 1136639) (by norm_num)
theorem B2020691 : Blo 2019435 2020691 := bstep (se 1 (by rfl) ⟨1515518, by rfl⟩ : syracuseStep 2020691 = 3031037) B3031037
theorem B4546565 : Blo 2019435 4546565 := bbase (se 4 (by rfl) ⟨426240, by rfl⟩ : syracuseStep 4546565 = 852481) (by norm_num)
theorem B3031043 : Blo 2019435 3031043 := bstep (se 1 (by rfl) ⟨2273282, by rfl⟩ : syracuseStep 3031043 = 4546565) B4546565
theorem B2020695 : Blo 2019435 2020695 := bstep (se 1 (by rfl) ⟨1515521, by rfl⟩ : syracuseStep 2020695 = 3031043) B3031043
theorem B3836173 : Blo 2019435 3836173 := bbase (se 3 (by rfl) ⟨719282, by rfl⟩ : syracuseStep 3836173 = 1438565) (by norm_num)
theorem B5114897 : Blo 2019435 5114897 := bstep (se 2 (by rfl) ⟨1918086, by rfl⟩ : syracuseStep 5114897 = 3836173) B3836173
theorem B3409931 : Blo 2019435 3409931 := bstep (se 1 (by rfl) ⟨2557448, by rfl⟩ : syracuseStep 3409931 = 5114897) B5114897
theorem B2273287 : Blo 2019435 2273287 := bstep (se 1 (by rfl) ⟨1704965, by rfl⟩ : syracuseStep 2273287 = 3409931) B3409931
theorem B3031049 : Blo 2019435 3031049 := bstep (se 2 (by rfl) ⟨1136643, by rfl⟩ : syracuseStep 3031049 = 2273287) B2273287
theorem B2020699 : Blo 2019435 2020699 := bstep (se 1 (by rfl) ⟨1515524, by rfl⟩ : syracuseStep 2020699 = 3031049) B3031049
theorem B10229813 : Blo 2019435 10229813 := bbase (se 5 (by rfl) ⟨479522, by rfl⟩ : syracuseStep 10229813 = 959045) (by norm_num)
theorem B6819875 : Blo 2019435 6819875 := bstep (se 1 (by rfl) ⟨5114906, by rfl⟩ : syracuseStep 6819875 = 10229813) B10229813
theorem B4546583 : Blo 2019435 4546583 := bstep (se 1 (by rfl) ⟨3409937, by rfl⟩ : syracuseStep 4546583 = 6819875) B6819875
theorem B3031055 : Blo 2019435 3031055 := bstep (se 1 (by rfl) ⟨2273291, by rfl⟩ : syracuseStep 3031055 = 4546583) B4546583
theorem B2020703 : Blo 2019435 2020703 := bstep (se 1 (by rfl) ⟨1515527, by rfl⟩ : syracuseStep 2020703 = 3031055) B3031055
theorem B3031061 : Blo 2019435 3031061 := bbase (se 6 (by rfl) ⟨71040, by rfl⟩ : syracuseStep 3031061 = 142081) (by norm_num)
theorem B2020707 : Blo 2019435 2020707 := bstep (se 1 (by rfl) ⟨1515530, by rfl⟩ : syracuseStep 2020707 = 3031061) B3031061
theorem B14565557 : Blo 2019435 14565557 := bbase (se 5 (by rfl) ⟨682760, by rfl⟩ : syracuseStep 14565557 = 1365521) (by norm_num)
theorem B9710371 : Blo 2019435 9710371 := bstep (se 1 (by rfl) ⟨7282778, by rfl⟩ : syracuseStep 9710371 = 14565557) B14565557
theorem B12947161 : Blo 2019435 12947161 := bstep (se 2 (by rfl) ⟨4855185, by rfl⟩ : syracuseStep 12947161 = 9710371) B9710371
theorem B17262881 : Blo 2019435 17262881 := bstep (se 2 (by rfl) ⟨6473580, by rfl⟩ : syracuseStep 17262881 = 12947161) B12947161
theorem B11508587 : Blo 2019435 11508587 := bstep (se 1 (by rfl) ⟨8631440, by rfl⟩ : syracuseStep 11508587 = 17262881) B17262881
theorem B7672391 : Blo 2019435 7672391 := bstep (se 1 (by rfl) ⟨5754293, by rfl⟩ : syracuseStep 7672391 = 11508587) B11508587
theorem B5114927 : Blo 2019435 5114927 := bstep (se 1 (by rfl) ⟨3836195, by rfl⟩ : syracuseStep 5114927 = 7672391) B7672391
theorem B3409951 : Blo 2019435 3409951 := bstep (se 1 (by rfl) ⟨2557463, by rfl⟩ : syracuseStep 3409951 = 5114927) B5114927
theorem B4546601 : Blo 2019435 4546601 := bstep (se 2 (by rfl) ⟨1704975, by rfl⟩ : syracuseStep 4546601 = 3409951) B3409951
theorem B3031067 : Blo 2019435 3031067 := bstep (se 1 (by rfl) ⟨2273300, by rfl⟩ : syracuseStep 3031067 = 4546601) B4546601
theorem B2020711 : Blo 2019435 2020711 := bstep (se 1 (by rfl) ⟨1515533, by rfl⟩ : syracuseStep 2020711 = 3031067) B3031067
theorem B2273305 : Blo 2019435 2273305 := bbase (se 2 (by rfl) ⟨852489, by rfl⟩ : syracuseStep 2273305 = 1704979) (by norm_num)
theorem B3031073 : Blo 2019435 3031073 := bstep (se 2 (by rfl) ⟨1136652, by rfl⟩ : syracuseStep 3031073 = 2273305) B2273305
theorem B2020715 : Blo 2019435 2020715 := bstep (se 1 (by rfl) ⟨1515536, by rfl⟩ : syracuseStep 2020715 = 3031073) B3031073
theorem B7672421 : Blo 2019435 7672421 := bbase (se 4 (by rfl) ⟨719289, by rfl⟩ : syracuseStep 7672421 = 1438579) (by norm_num)
theorem B5114947 : Blo 2019435 5114947 := bstep (se 1 (by rfl) ⟨3836210, by rfl⟩ : syracuseStep 5114947 = 7672421) B7672421
theorem B6819929 : Blo 2019435 6819929 := bstep (se 2 (by rfl) ⟨2557473, by rfl⟩ : syracuseStep 6819929 = 5114947) B5114947
theorem B4546619 : Blo 2019435 4546619 := bstep (se 1 (by rfl) ⟨3409964, by rfl⟩ : syracuseStep 4546619 = 6819929) B6819929
theorem B3031079 : Blo 2019435 3031079 := bstep (se 1 (by rfl) ⟨2273309, by rfl⟩ : syracuseStep 3031079 = 4546619) B4546619
theorem B2020719 : Blo 2019435 2020719 := bstep (se 1 (by rfl) ⟨1515539, by rfl⟩ : syracuseStep 2020719 = 3031079) B3031079
theorem B3031085 : Blo 2019435 3031085 := bbase (se 3 (by rfl) ⟨568328, by rfl⟩ : syracuseStep 3031085 = 1136657) (by norm_num)
theorem B2020723 : Blo 2019435 2020723 := bstep (se 1 (by rfl) ⟨1515542, by rfl⟩ : syracuseStep 2020723 = 3031085) B3031085
theorem B4546637 : Blo 2019435 4546637 := bbase (se 3 (by rfl) ⟨852494, by rfl⟩ : syracuseStep 4546637 = 1704989) (by norm_num)
theorem B3031091 : Blo 2019435 3031091 := bstep (se 1 (by rfl) ⟨2273318, by rfl⟩ : syracuseStep 3031091 = 4546637) B4546637
theorem B2020727 : Blo 2019435 2020727 := bstep (se 1 (by rfl) ⟨1515545, by rfl⟩ : syracuseStep 2020727 = 3031091) B3031091
theorem B2557489 : Blo 2019435 2557489 := bbase (se 2 (by rfl) ⟨959058, by rfl⟩ : syracuseStep 2557489 = 1918117) (by norm_num)
theorem B3409985 : Blo 2019435 3409985 := bstep (se 2 (by rfl) ⟨1278744, by rfl⟩ : syracuseStep 3409985 = 2557489) B2557489
theorem B2273323 : Blo 2019435 2273323 := bstep (se 1 (by rfl) ⟨1704992, by rfl⟩ : syracuseStep 2273323 = 3409985) B3409985
theorem B3031097 : Blo 2019435 3031097 := bstep (se 2 (by rfl) ⟨1136661, by rfl⟩ : syracuseStep 3031097 = 2273323) B2273323
theorem B2020731 : Blo 2019435 2020731 := bstep (se 1 (by rfl) ⟨1515548, by rfl⟩ : syracuseStep 2020731 = 3031097) B3031097
theorem B5462149 : Blo 2019435 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B7282865 : Blo 2019435 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B4855243 : Blo 2019435 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B6473657 : Blo 2019435 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B4315771 : Blo 2019435 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B23017445 : Blo 2019435 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B15344963 : Blo 2019435 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B10229975 : Blo 2019435 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B6819983 : Blo 2019435 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B4546655 : Blo 2019435 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B3031103 : Blo 2019435 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B2020735 : Blo 2019435 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B3031109 : Blo 2019435 3031109 := bbase (se 4 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 3031109 = 568333) (by norm_num)
theorem B2020739 : Blo 2019435 2020739 := bstep (se 1 (by rfl) ⟨1515554, by rfl⟩ : syracuseStep 2020739 = 3031109) B3031109
theorem B3410005 : Blo 2019435 3410005 := bbase (se 8 (by rfl) ⟨19980, by rfl⟩ : syracuseStep 3410005 = 39961) (by norm_num)
theorem B4546673 : Blo 2019435 4546673 := bstep (se 2 (by rfl) ⟨1705002, by rfl⟩ : syracuseStep 4546673 = 3410005) B3410005
theorem B3031115 : Blo 2019435 3031115 := bstep (se 1 (by rfl) ⟨2273336, by rfl⟩ : syracuseStep 3031115 = 4546673) B4546673
theorem B2020743 : Blo 2019435 2020743 := bstep (se 1 (by rfl) ⟨1515557, by rfl⟩ : syracuseStep 2020743 = 3031115) B3031115
theorem B2273341 : Blo 2019435 2273341 := bbase (se 3 (by rfl) ⟨426251, by rfl⟩ : syracuseStep 2273341 = 852503) (by norm_num)
theorem B3031121 : Blo 2019435 3031121 := bstep (se 2 (by rfl) ⟨1136670, by rfl⟩ : syracuseStep 3031121 = 2273341) B2273341
theorem B2020747 : Blo 2019435 2020747 := bstep (se 1 (by rfl) ⟨1515560, by rfl⟩ : syracuseStep 2020747 = 3031121) B3031121
theorem B6820037 : Blo 2019435 6820037 := bbase (se 4 (by rfl) ⟨639378, by rfl⟩ : syracuseStep 6820037 = 1278757) (by norm_num)
theorem B4546691 : Blo 2019435 4546691 := bstep (se 1 (by rfl) ⟨3410018, by rfl⟩ : syracuseStep 4546691 = 6820037) B6820037
theorem B3031127 : Blo 2019435 3031127 := bstep (se 1 (by rfl) ⟨2273345, by rfl⟩ : syracuseStep 3031127 = 4546691) B4546691
theorem B2020751 : Blo 2019435 2020751 := bstep (se 1 (by rfl) ⟨1515563, by rfl⟩ : syracuseStep 2020751 = 3031127) B3031127
theorem B3031133 : Blo 2019435 3031133 := bbase (se 3 (by rfl) ⟨568337, by rfl⟩ : syracuseStep 3031133 = 1136675) (by norm_num)
theorem B2020755 : Blo 2019435 2020755 := bstep (se 1 (by rfl) ⟨1515566, by rfl⟩ : syracuseStep 2020755 = 3031133) B3031133
theorem B4546709 : Blo 2019435 4546709 := bbase (se 6 (by rfl) ⟨106563, by rfl⟩ : syracuseStep 4546709 = 213127) (by norm_num)
theorem B3031139 : Blo 2019435 3031139 := bstep (se 1 (by rfl) ⟨2273354, by rfl⟩ : syracuseStep 3031139 = 4546709) B4546709
theorem B2020759 : Blo 2019435 2020759 := bstep (se 1 (by rfl) ⟨1515569, by rfl⟩ : syracuseStep 2020759 = 3031139) B3031139
theorem B2877221 : Blo 2019435 2877221 := bbase (se 4 (by rfl) ⟨269739, by rfl⟩ : syracuseStep 2877221 = 539479) (by norm_num)
theorem B7672589 : Blo 2019435 7672589 := bstep (se 3 (by rfl) ⟨1438610, by rfl⟩ : syracuseStep 7672589 = 2877221) B2877221
theorem B5115059 : Blo 2019435 5115059 := bstep (se 1 (by rfl) ⟨3836294, by rfl⟩ : syracuseStep 5115059 = 7672589) B7672589
theorem B3410039 : Blo 2019435 3410039 := bstep (se 1 (by rfl) ⟨2557529, by rfl⟩ : syracuseStep 3410039 = 5115059) B5115059
theorem B2273359 : Blo 2019435 2273359 := bstep (se 1 (by rfl) ⟨1705019, by rfl⟩ : syracuseStep 2273359 = 3410039) B3410039
theorem B3031145 : Blo 2019435 3031145 := bstep (se 2 (by rfl) ⟨1136679, by rfl⟩ : syracuseStep 3031145 = 2273359) B2273359
theorem B2020763 : Blo 2019435 2020763 := bstep (se 1 (by rfl) ⟨1515572, by rfl⟩ : syracuseStep 2020763 = 3031145) B3031145
theorem B27652565 : Blo 2019435 27652565 := bbase (se 7 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 27652565 = 648107) (by norm_num)
theorem B18435043 : Blo 2019435 18435043 := bstep (se 1 (by rfl) ⟨13826282, by rfl⟩ : syracuseStep 18435043 = 27652565) B27652565
theorem B98320229 : Blo 2019435 98320229 := bstep (se 4 (by rfl) ⟨9217521, by rfl⟩ : syracuseStep 98320229 = 18435043) B18435043
theorem B65546819 : Blo 2019435 65546819 := bstep (se 1 (by rfl) ⟨49160114, by rfl⟩ : syracuseStep 65546819 = 98320229) B98320229
theorem B43697879 : Blo 2019435 43697879 := bstep (se 1 (by rfl) ⟨32773409, by rfl⟩ : syracuseStep 43697879 = 65546819) B65546819
theorem B29131919 : Blo 2019435 29131919 := bstep (se 1 (by rfl) ⟨21848939, by rfl⟩ : syracuseStep 29131919 = 43697879) B43697879
theorem B19421279 : Blo 2019435 19421279 := bstep (se 1 (by rfl) ⟨14565959, by rfl⟩ : syracuseStep 19421279 = 29131919) B29131919
theorem B12947519 : Blo 2019435 12947519 := bstep (se 1 (by rfl) ⟨9710639, by rfl⟩ : syracuseStep 12947519 = 19421279) B19421279
theorem B8631679 : Blo 2019435 8631679 := bstep (se 1 (by rfl) ⟨6473759, by rfl⟩ : syracuseStep 8631679 = 12947519) B12947519
theorem B11508905 : Blo 2019435 11508905 := bstep (se 2 (by rfl) ⟨4315839, by rfl⟩ : syracuseStep 11508905 = 8631679) B8631679
theorem B7672603 : Blo 2019435 7672603 := bstep (se 1 (by rfl) ⟨5754452, by rfl⟩ : syracuseStep 7672603 = 11508905) B11508905
theorem B10230137 : Blo 2019435 10230137 := bstep (se 2 (by rfl) ⟨3836301, by rfl⟩ : syracuseStep 10230137 = 7672603) B7672603
theorem B6820091 : Blo 2019435 6820091 := bstep (se 1 (by rfl) ⟨5115068, by rfl⟩ : syracuseStep 6820091 = 10230137) B10230137
theorem B4546727 : Blo 2019435 4546727 := bstep (se 1 (by rfl) ⟨3410045, by rfl⟩ : syracuseStep 4546727 = 6820091) B6820091
theorem B3031151 : Blo 2019435 3031151 := bstep (se 1 (by rfl) ⟨2273363, by rfl⟩ : syracuseStep 3031151 = 4546727) B4546727
theorem B2020767 : Blo 2019435 2020767 := bstep (se 1 (by rfl) ⟨1515575, by rfl⟩ : syracuseStep 2020767 = 3031151) B3031151
theorem B3031157 : Blo 2019435 3031157 := bbase (se 5 (by rfl) ⟨142085, by rfl⟩ : syracuseStep 3031157 = 284171) (by norm_num)
theorem B2020771 : Blo 2019435 2020771 := bstep (se 1 (by rfl) ⟨1515578, by rfl⟩ : syracuseStep 2020771 = 3031157) B3031157
theorem B3836317 : Blo 2019435 3836317 := bbase (se 3 (by rfl) ⟨719309, by rfl⟩ : syracuseStep 3836317 = 1438619) (by norm_num)
theorem B5115089 : Blo 2019435 5115089 := bstep (se 2 (by rfl) ⟨1918158, by rfl⟩ : syracuseStep 5115089 = 3836317) B3836317
theorem B3410059 : Blo 2019435 3410059 := bstep (se 1 (by rfl) ⟨2557544, by rfl⟩ : syracuseStep 3410059 = 5115089) B5115089
theorem B4546745 : Blo 2019435 4546745 := bstep (se 2 (by rfl) ⟨1705029, by rfl⟩ : syracuseStep 4546745 = 3410059) B3410059
theorem B3031163 : Blo 2019435 3031163 := bstep (se 1 (by rfl) ⟨2273372, by rfl⟩ : syracuseStep 3031163 = 4546745) B4546745
theorem B2020775 : Blo 2019435 2020775 := bstep (se 1 (by rfl) ⟨1515581, by rfl⟩ : syracuseStep 2020775 = 3031163) B3031163
theorem B2273377 : Blo 2019435 2273377 := bbase (se 2 (by rfl) ⟨852516, by rfl⟩ : syracuseStep 2273377 = 1705033) (by norm_num)
theorem B3031169 : Blo 2019435 3031169 := bstep (se 2 (by rfl) ⟨1136688, by rfl⟩ : syracuseStep 3031169 = 2273377) B2273377
theorem B2020779 : Blo 2019435 2020779 := bstep (se 1 (by rfl) ⟨1515584, by rfl⟩ : syracuseStep 2020779 = 3031169) B3031169
theorem B5115109 : Blo 2019435 5115109 := bbase (se 4 (by rfl) ⟨479541, by rfl⟩ : syracuseStep 5115109 = 959083) (by norm_num)
theorem B6820145 : Blo 2019435 6820145 := bstep (se 2 (by rfl) ⟨2557554, by rfl⟩ : syracuseStep 6820145 = 5115109) B5115109
theorem B4546763 : Blo 2019435 4546763 := bstep (se 1 (by rfl) ⟨3410072, by rfl⟩ : syracuseStep 4546763 = 6820145) B6820145
theorem B3031175 : Blo 2019435 3031175 := bstep (se 1 (by rfl) ⟨2273381, by rfl⟩ : syracuseStep 3031175 = 4546763) B4546763
theorem B2020783 : Blo 2019435 2020783 := bstep (se 1 (by rfl) ⟨1515587, by rfl⟩ : syracuseStep 2020783 = 3031175) B3031175
theorem B3031181 : Blo 2019435 3031181 := bbase (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) (by norm_num)
theorem B2020787 : Blo 2019435 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B4546781 : Blo 2019435 4546781 := bbase (se 3 (by rfl) ⟨852521, by rfl⟩ : syracuseStep 4546781 = 1705043) (by norm_num)
theorem B3031187 : Blo 2019435 3031187 := bstep (se 1 (by rfl) ⟨2273390, by rfl⟩ : syracuseStep 3031187 = 4546781) B4546781
theorem B2020791 : Blo 2019435 2020791 := bstep (se 1 (by rfl) ⟨1515593, by rfl⟩ : syracuseStep 2020791 = 3031187) B3031187
theorem B3410093 : Blo 2019435 3410093 := bbase (se 3 (by rfl) ⟨639392, by rfl⟩ : syracuseStep 3410093 = 1278785) (by norm_num)
theorem B2273395 : Blo 2019435 2273395 := bstep (se 1 (by rfl) ⟨1705046, by rfl⟩ : syracuseStep 2273395 = 3410093) B3410093
theorem B3031193 : Blo 2019435 3031193 := bstep (se 2 (by rfl) ⟨1136697, by rfl⟩ : syracuseStep 3031193 = 2273395) B2273395
theorem B2020795 : Blo 2019435 2020795 := bstep (se 1 (by rfl) ⟨1515596, by rfl⟩ : syracuseStep 2020795 = 3031193) B3031193
theorem B4096741 : Blo 2019435 4096741 := bbase (se 4 (by rfl) ⟨384069, by rfl⟩ : syracuseStep 4096741 = 768139) (by norm_num)
theorem B5462321 : Blo 2019435 5462321 := bstep (se 2 (by rfl) ⟨2048370, by rfl⟩ : syracuseStep 5462321 = 4096741) B4096741
theorem B58264757 : Blo 2019435 58264757 := bstep (se 5 (by rfl) ⟨2731160, by rfl⟩ : syracuseStep 58264757 = 5462321) B5462321
theorem B38843171 : Blo 2019435 38843171 := bstep (se 1 (by rfl) ⟨29132378, by rfl⟩ : syracuseStep 38843171 = 58264757) B58264757
theorem B25895447 : Blo 2019435 25895447 := bstep (se 1 (by rfl) ⟨19421585, by rfl⟩ : syracuseStep 25895447 = 38843171) B38843171
theorem B17263631 : Blo 2019435 17263631 := bstep (se 1 (by rfl) ⟨12947723, by rfl⟩ : syracuseStep 17263631 = 25895447) B25895447
theorem B11509087 : Blo 2019435 11509087 := bstep (se 1 (by rfl) ⟨8631815, by rfl⟩ : syracuseStep 11509087 = 17263631) B17263631
theorem B15345449 : Blo 2019435 15345449 := bstep (se 2 (by rfl) ⟨5754543, by rfl⟩ : syracuseStep 15345449 = 11509087) B11509087
theorem B10230299 : Blo 2019435 10230299 := bstep (se 1 (by rfl) ⟨7672724, by rfl⟩ : syracuseStep 10230299 = 15345449) B15345449
theorem B6820199 : Blo 2019435 6820199 := bstep (se 1 (by rfl) ⟨5115149, by rfl⟩ : syracuseStep 6820199 = 10230299) B10230299
theorem B4546799 : Blo 2019435 4546799 := bstep (se 1 (by rfl) ⟨3410099, by rfl⟩ : syracuseStep 4546799 = 6820199) B6820199
theorem B3031199 : Blo 2019435 3031199 := bstep (se 1 (by rfl) ⟨2273399, by rfl⟩ : syracuseStep 3031199 = 4546799) B4546799
theorem B2020799 : Blo 2019435 2020799 := bstep (se 1 (by rfl) ⟨1515599, by rfl⟩ : syracuseStep 2020799 = 3031199) B3031199
theorem B3031205 : Blo 2019435 3031205 := bbase (se 4 (by rfl) ⟨284175, by rfl⟩ : syracuseStep 3031205 = 568351) (by norm_num)
theorem B2020803 : Blo 2019435 2020803 := bstep (se 1 (by rfl) ⟨1515602, by rfl⟩ : syracuseStep 2020803 = 3031205) B3031205
theorem B2557585 : Blo 2019435 2557585 := bbase (se 2 (by rfl) ⟨959094, by rfl⟩ : syracuseStep 2557585 = 1918189) (by norm_num)
theorem B3410113 : Blo 2019435 3410113 := bstep (se 2 (by rfl) ⟨1278792, by rfl⟩ : syracuseStep 3410113 = 2557585) B2557585
theorem B4546817 : Blo 2019435 4546817 := bstep (se 2 (by rfl) ⟨1705056, by rfl⟩ : syracuseStep 4546817 = 3410113) B3410113
theorem B3031211 : Blo 2019435 3031211 := bstep (se 1 (by rfl) ⟨2273408, by rfl⟩ : syracuseStep 3031211 = 4546817) B4546817
theorem B2020807 : Blo 2019435 2020807 := bstep (se 1 (by rfl) ⟨1515605, by rfl⟩ : syracuseStep 2020807 = 3031211) B3031211
theorem B2273413 : Blo 2019435 2273413 := bbase (se 4 (by rfl) ⟨213132, by rfl⟩ : syracuseStep 2273413 = 426265) (by norm_num)
theorem B3031217 : Blo 2019435 3031217 := bstep (se 2 (by rfl) ⟨1136706, by rfl⟩ : syracuseStep 3031217 = 2273413) B2273413
theorem B2020811 : Blo 2019435 2020811 := bstep (se 1 (by rfl) ⟨1515608, by rfl⟩ : syracuseStep 2020811 = 3031217) B3031217
theorem B4921685 : Blo 2019435 4921685 := bbase (se 10 (by rfl) ⟨7209, by rfl⟩ : syracuseStep 4921685 = 14419) (by norm_num)
theorem B3281123 : Blo 2019435 3281123 := bstep (se 1 (by rfl) ⟨2460842, by rfl⟩ : syracuseStep 3281123 = 4921685) B4921685
theorem B2187415 : Blo 2019435 2187415 := bstep (se 1 (by rfl) ⟨1640561, by rfl⟩ : syracuseStep 2187415 = 3281123) B3281123
theorem B2916553 : Blo 2019435 2916553 := bstep (se 2 (by rfl) ⟨1093707, by rfl⟩ : syracuseStep 2916553 = 2187415) B2187415
theorem B3888737 : Blo 2019435 3888737 := bstep (se 2 (by rfl) ⟨1458276, by rfl⟩ : syracuseStep 3888737 = 2916553) B2916553
theorem B2592491 : Blo 2019435 2592491 := bstep (se 1 (by rfl) ⟨1944368, by rfl⟩ : syracuseStep 2592491 = 3888737) B3888737
theorem B6913309 : Blo 2019435 6913309 := bstep (se 3 (by rfl) ⟨1296245, by rfl⟩ : syracuseStep 6913309 = 2592491) B2592491
theorem B9217745 : Blo 2019435 9217745 := bstep (se 2 (by rfl) ⟨3456654, by rfl⟩ : syracuseStep 9217745 = 6913309) B6913309
theorem B6145163 : Blo 2019435 6145163 := bstep (se 1 (by rfl) ⟨4608872, by rfl⟩ : syracuseStep 6145163 = 9217745) B9217745
theorem B4096775 : Blo 2019435 4096775 := bstep (se 1 (by rfl) ⟨3072581, by rfl⟩ : syracuseStep 4096775 = 6145163) B6145163
theorem B10924733 : Blo 2019435 10924733 := bstep (se 3 (by rfl) ⟨2048387, by rfl⟩ : syracuseStep 10924733 = 4096775) B4096775
theorem B7283155 : Blo 2019435 7283155 := bstep (se 1 (by rfl) ⟨5462366, by rfl⟩ : syracuseStep 7283155 = 10924733) B10924733
theorem B9710873 : Blo 2019435 9710873 := bstep (se 2 (by rfl) ⟨3641577, by rfl⟩ : syracuseStep 9710873 = 7283155) B7283155
theorem B6473915 : Blo 2019435 6473915 := bstep (se 1 (by rfl) ⟨4855436, by rfl⟩ : syracuseStep 6473915 = 9710873) B9710873
theorem B4315943 : Blo 2019435 4315943 := bstep (se 1 (by rfl) ⟨3236957, by rfl⟩ : syracuseStep 4315943 = 6473915) B6473915
theorem B2877295 : Blo 2019435 2877295 := bstep (se 1 (by rfl) ⟨2157971, by rfl⟩ : syracuseStep 2877295 = 4315943) B4315943
theorem B3836393 : Blo 2019435 3836393 := bstep (se 2 (by rfl) ⟨1438647, by rfl⟩ : syracuseStep 3836393 = 2877295) B2877295
theorem B2557595 : Blo 2019435 2557595 := bstep (se 1 (by rfl) ⟨1918196, by rfl⟩ : syracuseStep 2557595 = 3836393) B3836393
theorem B6820253 : Blo 2019435 6820253 := bstep (se 3 (by rfl) ⟨1278797, by rfl⟩ : syracuseStep 6820253 = 2557595) B2557595
theorem B4546835 : Blo 2019435 4546835 := bstep (se 1 (by rfl) ⟨3410126, by rfl⟩ : syracuseStep 4546835 = 6820253) B6820253
theorem B3031223 : Blo 2019435 3031223 := bstep (se 1 (by rfl) ⟨2273417, by rfl⟩ : syracuseStep 3031223 = 4546835) B4546835
theorem B2020815 : Blo 2019435 2020815 := bstep (se 1 (by rfl) ⟨1515611, by rfl⟩ : syracuseStep 2020815 = 3031223) B3031223
theorem B3031229 : Blo 2019435 3031229 := bbase (se 3 (by rfl) ⟨568355, by rfl⟩ : syracuseStep 3031229 = 1136711) (by norm_num)
theorem B2020819 : Blo 2019435 2020819 := bstep (se 1 (by rfl) ⟨1515614, by rfl⟩ : syracuseStep 2020819 = 3031229) B3031229
theorem B4546853 : Blo 2019435 4546853 := bbase (se 4 (by rfl) ⟨426267, by rfl⟩ : syracuseStep 4546853 = 852535) (by norm_num)
theorem B3031235 : Blo 2019435 3031235 := bstep (se 1 (by rfl) ⟨2273426, by rfl⟩ : syracuseStep 3031235 = 4546853) B4546853
theorem B2020823 : Blo 2019435 2020823 := bstep (se 1 (by rfl) ⟨1515617, by rfl⟩ : syracuseStep 2020823 = 3031235) B3031235
theorem B5115221 : Blo 2019435 5115221 := bbase (se 11 (by rfl) ⟨3746, by rfl⟩ : syracuseStep 5115221 = 7493) (by norm_num)
theorem B3410147 : Blo 2019435 3410147 := bstep (se 1 (by rfl) ⟨2557610, by rfl⟩ : syracuseStep 3410147 = 5115221) B5115221
theorem B2273431 : Blo 2019435 2273431 := bstep (se 1 (by rfl) ⟨1705073, by rfl⟩ : syracuseStep 2273431 = 3410147) B3410147
theorem B3031241 : Blo 2019435 3031241 := bstep (se 2 (by rfl) ⟨1136715, by rfl⟩ : syracuseStep 3031241 = 2273431) B2273431
theorem B2020827 : Blo 2019435 2020827 := bstep (se 1 (by rfl) ⟨1515620, by rfl⟩ : syracuseStep 2020827 = 3031241) B3031241
theorem B2427737 : Blo 2019435 2427737 := bbase (se 2 (by rfl) ⟨910401, by rfl⟩ : syracuseStep 2427737 = 1820803) (by norm_num)
theorem B6473965 : Blo 2019435 6473965 := bstep (se 3 (by rfl) ⟨1213868, by rfl⟩ : syracuseStep 6473965 = 2427737) B2427737
theorem B8631953 : Blo 2019435 8631953 := bstep (se 2 (by rfl) ⟨3236982, by rfl⟩ : syracuseStep 8631953 = 6473965) B6473965
theorem B5754635 : Blo 2019435 5754635 := bstep (se 1 (by rfl) ⟨4315976, by rfl⟩ : syracuseStep 5754635 = 8631953) B8631953
theorem B3836423 : Blo 2019435 3836423 := bstep (se 1 (by rfl) ⟨2877317, by rfl⟩ : syracuseStep 3836423 = 5754635) B5754635
theorem B10230461 : Blo 2019435 10230461 := bstep (se 3 (by rfl) ⟨1918211, by rfl⟩ : syracuseStep 10230461 = 3836423) B3836423
theorem B6820307 : Blo 2019435 6820307 := bstep (se 1 (by rfl) ⟨5115230, by rfl⟩ : syracuseStep 6820307 = 10230461) B10230461
theorem B4546871 : Blo 2019435 4546871 := bstep (se 1 (by rfl) ⟨3410153, by rfl⟩ : syracuseStep 4546871 = 6820307) B6820307
theorem B3031247 : Blo 2019435 3031247 := bstep (se 1 (by rfl) ⟨2273435, by rfl⟩ : syracuseStep 3031247 = 4546871) B4546871
theorem B2020831 : Blo 2019435 2020831 := bstep (se 1 (by rfl) ⟨1515623, by rfl⟩ : syracuseStep 2020831 = 3031247) B3031247
theorem B3031253 : Blo 2019435 3031253 := bbase (se 7 (by rfl) ⟨35522, by rfl⟩ : syracuseStep 3031253 = 71045) (by norm_num)
theorem B2020835 : Blo 2019435 2020835 := bstep (se 1 (by rfl) ⟨1515626, by rfl⟩ : syracuseStep 2020835 = 3031253) B3031253
theorem B2157997 : Blo 2019435 2157997 := bbase (se 3 (by rfl) ⟨404624, by rfl⟩ : syracuseStep 2157997 = 809249) (by norm_num)
theorem B2877329 : Blo 2019435 2877329 := bstep (se 2 (by rfl) ⟨1078998, by rfl⟩ : syracuseStep 2877329 = 2157997) B2157997
theorem B7672877 : Blo 2019435 7672877 := bstep (se 3 (by rfl) ⟨1438664, by rfl⟩ : syracuseStep 7672877 = 2877329) B2877329
theorem B5115251 : Blo 2019435 5115251 := bstep (se 1 (by rfl) ⟨3836438, by rfl⟩ : syracuseStep 5115251 = 7672877) B7672877
theorem B3410167 : Blo 2019435 3410167 := bstep (se 1 (by rfl) ⟨2557625, by rfl⟩ : syracuseStep 3410167 = 5115251) B5115251
theorem B4546889 : Blo 2019435 4546889 := bstep (se 2 (by rfl) ⟨1705083, by rfl⟩ : syracuseStep 4546889 = 3410167) B3410167
theorem B3031259 : Blo 2019435 3031259 := bstep (se 1 (by rfl) ⟨2273444, by rfl⟩ : syracuseStep 3031259 = 4546889) B4546889
theorem B2020839 : Blo 2019435 2020839 := bstep (se 1 (by rfl) ⟨1515629, by rfl⟩ : syracuseStep 2020839 = 3031259) B3031259
theorem B2273449 : Blo 2019435 2273449 := bbase (se 2 (by rfl) ⟨852543, by rfl⟩ : syracuseStep 2273449 = 1705087) (by norm_num)
theorem B3031265 : Blo 2019435 3031265 := bstep (se 2 (by rfl) ⟨1136724, by rfl⟩ : syracuseStep 3031265 = 2273449) B2273449
theorem B2020843 : Blo 2019435 2020843 := bstep (se 1 (by rfl) ⟨1515632, by rfl⟩ : syracuseStep 2020843 = 3031265) B3031265
theorem B8632021 : Blo 2019435 8632021 := bbase (se 7 (by rfl) ⟨101156, by rfl⟩ : syracuseStep 8632021 = 202313) (by norm_num)
theorem B11509361 : Blo 2019435 11509361 := bstep (se 2 (by rfl) ⟨4316010, by rfl⟩ : syracuseStep 11509361 = 8632021) B8632021
theorem B7672907 : Blo 2019435 7672907 := bstep (se 1 (by rfl) ⟨5754680, by rfl⟩ : syracuseStep 7672907 = 11509361) B11509361
theorem B5115271 : Blo 2019435 5115271 := bstep (se 1 (by rfl) ⟨3836453, by rfl⟩ : syracuseStep 5115271 = 7672907) B7672907
theorem B6820361 : Blo 2019435 6820361 := bstep (se 2 (by rfl) ⟨2557635, by rfl⟩ : syracuseStep 6820361 = 5115271) B5115271
theorem B4546907 : Blo 2019435 4546907 := bstep (se 1 (by rfl) ⟨3410180, by rfl⟩ : syracuseStep 4546907 = 6820361) B6820361
theorem B3031271 : Blo 2019435 3031271 := bstep (se 1 (by rfl) ⟨2273453, by rfl⟩ : syracuseStep 3031271 = 4546907) B4546907
theorem B2020847 : Blo 2019435 2020847 := bstep (se 1 (by rfl) ⟨1515635, by rfl⟩ : syracuseStep 2020847 = 3031271) B3031271
theorem B3031277 : Blo 2019435 3031277 := bbase (se 3 (by rfl) ⟨568364, by rfl⟩ : syracuseStep 3031277 = 1136729) (by norm_num)
theorem B2020851 : Blo 2019435 2020851 := bstep (se 1 (by rfl) ⟨1515638, by rfl⟩ : syracuseStep 2020851 = 3031277) B3031277
theorem B4546925 : Blo 2019435 4546925 := bbase (se 3 (by rfl) ⟨852548, by rfl⟩ : syracuseStep 4546925 = 1705097) (by norm_num)
theorem B3031283 : Blo 2019435 3031283 := bstep (se 1 (by rfl) ⟨2273462, by rfl⟩ : syracuseStep 3031283 = 4546925) B4546925
theorem B2020855 : Blo 2019435 2020855 := bstep (se 1 (by rfl) ⟨1515641, by rfl⟩ : syracuseStep 2020855 = 3031283) B3031283
theorem B3836477 : Blo 2019435 3836477 := bbase (se 3 (by rfl) ⟨719339, by rfl⟩ : syracuseStep 3836477 = 1438679) (by norm_num)
theorem B2557651 : Blo 2019435 2557651 := bstep (se 1 (by rfl) ⟨1918238, by rfl⟩ : syracuseStep 2557651 = 3836477) B3836477
theorem B3410201 : Blo 2019435 3410201 := bstep (se 2 (by rfl) ⟨1278825, by rfl⟩ : syracuseStep 3410201 = 2557651) B2557651
theorem B2273467 : Blo 2019435 2273467 := bstep (se 1 (by rfl) ⟨1705100, by rfl⟩ : syracuseStep 2273467 = 3410201) B3410201
theorem B3031289 : Blo 2019435 3031289 := bstep (se 2 (by rfl) ⟨1136733, by rfl⟩ : syracuseStep 3031289 = 2273467) B2273467
theorem B2020859 : Blo 2019435 2020859 := bstep (se 1 (by rfl) ⟨1515644, by rfl⟩ : syracuseStep 2020859 = 3031289) B3031289
theorem B3037637 : Blo 2019435 3037637 := bbase (se 4 (by rfl) ⟨284778, by rfl⟩ : syracuseStep 3037637 = 569557) (by norm_num)
theorem B2025091 : Blo 2019435 2025091 := bstep (se 1 (by rfl) ⟨1518818, by rfl⟩ : syracuseStep 2025091 = 3037637) B3037637
theorem B10800485 : Blo 2019435 10800485 := bstep (se 4 (by rfl) ⟨1012545, by rfl⟩ : syracuseStep 10800485 = 2025091) B2025091
theorem B7200323 : Blo 2019435 7200323 := bstep (se 1 (by rfl) ⟨5400242, by rfl⟩ : syracuseStep 7200323 = 10800485) B10800485
theorem B4800215 : Blo 2019435 4800215 := bstep (se 1 (by rfl) ⟨3600161, by rfl⟩ : syracuseStep 4800215 = 7200323) B7200323
theorem B3200143 : Blo 2019435 3200143 := bstep (se 1 (by rfl) ⟨2400107, by rfl⟩ : syracuseStep 3200143 = 4800215) B4800215
theorem B4266857 : Blo 2019435 4266857 := bstep (se 2 (by rfl) ⟨1600071, by rfl⟩ : syracuseStep 4266857 = 3200143) B3200143
theorem B2844571 : Blo 2019435 2844571 := bstep (se 1 (by rfl) ⟨2133428, by rfl⟩ : syracuseStep 2844571 = 4266857) B4266857
theorem B3792761 : Blo 2019435 3792761 := bstep (se 2 (by rfl) ⟨1422285, by rfl⟩ : syracuseStep 3792761 = 2844571) B2844571
theorem B2528507 : Blo 2019435 2528507 := bstep (se 1 (by rfl) ⟨1896380, by rfl⟩ : syracuseStep 2528507 = 3792761) B3792761
theorem B6742685 : Blo 2019435 6742685 := bstep (se 3 (by rfl) ⟨1264253, by rfl⟩ : syracuseStep 6742685 = 2528507) B2528507
theorem B4495123 : Blo 2019435 4495123 := bstep (se 1 (by rfl) ⟨3371342, by rfl⟩ : syracuseStep 4495123 = 6742685) B6742685
theorem B5993497 : Blo 2019435 5993497 := bstep (se 2 (by rfl) ⟨2247561, by rfl⟩ : syracuseStep 5993497 = 4495123) B4495123
theorem B31965317 : Blo 2019435 31965317 := bstep (se 4 (by rfl) ⟨2996748, by rfl⟩ : syracuseStep 31965317 = 5993497) B5993497
theorem B340963381 : Blo 2019435 340963381 := bstep (se 5 (by rfl) ⟨15982658, by rfl⟩ : syracuseStep 340963381 = 31965317) B31965317
theorem B454617841 : Blo 2019435 454617841 := bstep (se 2 (by rfl) ⟨170481690, by rfl⟩ : syracuseStep 454617841 = 340963381) B340963381
theorem B606157121 : Blo 2019435 606157121 := bstep (se 2 (by rfl) ⟨227308920, by rfl⟩ : syracuseStep 606157121 = 454617841) B454617841
theorem B404104747 : Blo 2019435 404104747 := bstep (se 1 (by rfl) ⟨303078560, by rfl⟩ : syracuseStep 404104747 = 606157121) B606157121
theorem B538806329 : Blo 2019435 538806329 := bstep (se 2 (by rfl) ⟨202052373, by rfl⟩ : syracuseStep 538806329 = 404104747) B404104747
theorem B359204219 : Blo 2019435 359204219 := bstep (se 1 (by rfl) ⟨269403164, by rfl⟩ : syracuseStep 359204219 = 538806329) B538806329
theorem B239469479 : Blo 2019435 239469479 := bstep (se 1 (by rfl) ⟨179602109, by rfl⟩ : syracuseStep 239469479 = 359204219) B359204219
theorem B159646319 : Blo 2019435 159646319 := bstep (se 1 (by rfl) ⟨119734739, by rfl⟩ : syracuseStep 159646319 = 239469479) B239469479
theorem B106430879 : Blo 2019435 106430879 := bstep (se 1 (by rfl) ⟨79823159, by rfl⟩ : syracuseStep 106430879 = 159646319) B159646319
theorem B283815677 : Blo 2019435 283815677 := bstep (se 3 (by rfl) ⟨53215439, by rfl⟩ : syracuseStep 283815677 = 106430879) B106430879
theorem B189210451 : Blo 2019435 189210451 := bstep (se 1 (by rfl) ⟨141907838, by rfl⟩ : syracuseStep 189210451 = 283815677) B283815677
theorem B252280601 : Blo 2019435 252280601 := bstep (se 2 (by rfl) ⟨94605225, by rfl⟩ : syracuseStep 252280601 = 189210451) B189210451
theorem B168187067 : Blo 2019435 168187067 := bstep (se 1 (by rfl) ⟨126140300, by rfl⟩ : syracuseStep 168187067 = 252280601) B252280601
theorem B112124711 : Blo 2019435 112124711 := bstep (se 1 (by rfl) ⟨84093533, by rfl⟩ : syracuseStep 112124711 = 168187067) B168187067
theorem B74749807 : Blo 2019435 74749807 := bstep (se 1 (by rfl) ⟨56062355, by rfl⟩ : syracuseStep 74749807 = 112124711) B112124711
theorem B99666409 : Blo 2019435 99666409 := bstep (se 2 (by rfl) ⟨37374903, by rfl⟩ : syracuseStep 99666409 = 74749807) B74749807
theorem B132888545 : Blo 2019435 132888545 := bstep (se 2 (by rfl) ⟨49833204, by rfl⟩ : syracuseStep 132888545 = 99666409) B99666409
theorem B88592363 : Blo 2019435 88592363 := bstep (se 1 (by rfl) ⟨66444272, by rfl⟩ : syracuseStep 88592363 = 132888545) B132888545
theorem B59061575 : Blo 2019435 59061575 := bstep (se 1 (by rfl) ⟨44296181, by rfl⟩ : syracuseStep 59061575 = 88592363) B88592363
theorem B39374383 : Blo 2019435 39374383 := bstep (se 1 (by rfl) ⟨29530787, by rfl⟩ : syracuseStep 39374383 = 59061575) B59061575
theorem B52499177 : Blo 2019435 52499177 := bstep (se 2 (by rfl) ⟨19687191, by rfl⟩ : syracuseStep 52499177 = 39374383) B39374383
theorem B34999451 : Blo 2019435 34999451 := bstep (se 1 (by rfl) ⟨26249588, by rfl⟩ : syracuseStep 34999451 = 52499177) B52499177
theorem B23332967 : Blo 2019435 23332967 := bstep (se 1 (by rfl) ⟨17499725, by rfl⟩ : syracuseStep 23332967 = 34999451) B34999451
theorem B15555311 : Blo 2019435 15555311 := bstep (se 1 (by rfl) ⟨11666483, by rfl⟩ : syracuseStep 15555311 = 23332967) B23332967
theorem B10370207 : Blo 2019435 10370207 := bstep (se 1 (by rfl) ⟨7777655, by rfl⟩ : syracuseStep 10370207 = 15555311) B15555311
theorem B27653885 : Blo 2019435 27653885 := bstep (se 3 (by rfl) ⟨5185103, by rfl⟩ : syracuseStep 27653885 = 10370207) B10370207
theorem B18435923 : Blo 2019435 18435923 := bstep (se 1 (by rfl) ⟨13826942, by rfl⟩ : syracuseStep 18435923 = 27653885) B27653885
theorem B12290615 : Blo 2019435 12290615 := bstep (se 1 (by rfl) ⟨9217961, by rfl⟩ : syracuseStep 12290615 = 18435923) B18435923
theorem B8193743 : Blo 2019435 8193743 := bstep (se 1 (by rfl) ⟨6145307, by rfl⟩ : syracuseStep 8193743 = 12290615) B12290615
theorem B5462495 : Blo 2019435 5462495 := bstep (se 1 (by rfl) ⟨4096871, by rfl⟩ : syracuseStep 5462495 = 8193743) B8193743
theorem B3641663 : Blo 2019435 3641663 := bstep (se 1 (by rfl) ⟨2731247, by rfl⟩ : syracuseStep 3641663 = 5462495) B5462495
theorem B2427775 : Blo 2019435 2427775 := bstep (se 1 (by rfl) ⟨1820831, by rfl⟩ : syracuseStep 2427775 = 3641663) B3641663
theorem B51792533 : Blo 2019435 51792533 := bstep (se 6 (by rfl) ⟨1213887, by rfl⟩ : syracuseStep 51792533 = 2427775) B2427775
theorem B34528355 : Blo 2019435 34528355 := bstep (se 1 (by rfl) ⟨25896266, by rfl⟩ : syracuseStep 34528355 = 51792533) B51792533
theorem B23018903 : Blo 2019435 23018903 := bstep (se 1 (by rfl) ⟨17264177, by rfl⟩ : syracuseStep 23018903 = 34528355) B34528355
theorem B15345935 : Blo 2019435 15345935 := bstep (se 1 (by rfl) ⟨11509451, by rfl⟩ : syracuseStep 15345935 = 23018903) B23018903
theorem B10230623 : Blo 2019435 10230623 := bstep (se 1 (by rfl) ⟨7672967, by rfl⟩ : syracuseStep 10230623 = 15345935) B15345935
theorem B6820415 : Blo 2019435 6820415 := bstep (se 1 (by rfl) ⟨5115311, by rfl⟩ : syracuseStep 6820415 = 10230623) B10230623
theorem B4546943 : Blo 2019435 4546943 := bstep (se 1 (by rfl) ⟨3410207, by rfl⟩ : syracuseStep 4546943 = 6820415) B6820415
theorem B3031295 : Blo 2019435 3031295 := bstep (se 1 (by rfl) ⟨2273471, by rfl⟩ : syracuseStep 3031295 = 4546943) B4546943
theorem B2020863 : Blo 2019435 2020863 := bstep (se 1 (by rfl) ⟨1515647, by rfl⟩ : syracuseStep 2020863 = 3031295) B3031295
theorem B3031301 : Blo 2019435 3031301 := bbase (se 4 (by rfl) ⟨284184, by rfl⟩ : syracuseStep 3031301 = 568369) (by norm_num)
theorem B2020867 : Blo 2019435 2020867 := bstep (se 1 (by rfl) ⟨1515650, by rfl⟩ : syracuseStep 2020867 = 3031301) B3031301
theorem B3410221 : Blo 2019435 3410221 := bbase (se 3 (by rfl) ⟨639416, by rfl⟩ : syracuseStep 3410221 = 1278833) (by norm_num)
theorem B4546961 : Blo 2019435 4546961 := bstep (se 2 (by rfl) ⟨1705110, by rfl⟩ : syracuseStep 4546961 = 3410221) B3410221
theorem B3031307 : Blo 2019435 3031307 := bstep (se 1 (by rfl) ⟨2273480, by rfl⟩ : syracuseStep 3031307 = 4546961) B4546961
theorem B2020871 : Blo 2019435 2020871 := bstep (se 1 (by rfl) ⟨1515653, by rfl⟩ : syracuseStep 2020871 = 3031307) B3031307
theorem B2273485 : Blo 2019435 2273485 := bbase (se 3 (by rfl) ⟨426278, by rfl⟩ : syracuseStep 2273485 = 852557) (by norm_num)
theorem B3031313 : Blo 2019435 3031313 := bstep (se 2 (by rfl) ⟨1136742, by rfl⟩ : syracuseStep 3031313 = 2273485) B2273485
theorem B2020875 : Blo 2019435 2020875 := bstep (se 1 (by rfl) ⟨1515656, by rfl⟩ : syracuseStep 2020875 = 3031313) B3031313
theorem B6820469 : Blo 2019435 6820469 := bbase (se 5 (by rfl) ⟨319709, by rfl⟩ : syracuseStep 6820469 = 639419) (by norm_num)
theorem B4546979 : Blo 2019435 4546979 := bstep (se 1 (by rfl) ⟨3410234, by rfl⟩ : syracuseStep 4546979 = 6820469) B6820469
theorem B3031319 : Blo 2019435 3031319 := bstep (se 1 (by rfl) ⟨2273489, by rfl⟩ : syracuseStep 3031319 = 4546979) B4546979
theorem B2020879 : Blo 2019435 2020879 := bstep (se 1 (by rfl) ⟨1515659, by rfl⟩ : syracuseStep 2020879 = 3031319) B3031319
theorem B3031325 : Blo 2019435 3031325 := bbase (se 3 (by rfl) ⟨568373, by rfl⟩ : syracuseStep 3031325 = 1136747) (by norm_num)
theorem B2020883 : Blo 2019435 2020883 := bstep (se 1 (by rfl) ⟨1515662, by rfl⟩ : syracuseStep 2020883 = 3031325) B3031325
theorem B4546997 : Blo 2019435 4546997 := bbase (se 5 (by rfl) ⟨213140, by rfl⟩ : syracuseStep 4546997 = 426281) (by norm_num)
theorem B3031331 : Blo 2019435 3031331 := bstep (se 1 (by rfl) ⟨2273498, by rfl⟩ : syracuseStep 3031331 = 4546997) B4546997
theorem B2020887 : Blo 2019435 2020887 := bstep (se 1 (by rfl) ⟨1515665, by rfl⟩ : syracuseStep 2020887 = 3031331) B3031331
theorem B7283429 : Blo 2019435 7283429 := bbase (se 4 (by rfl) ⟨682821, by rfl⟩ : syracuseStep 7283429 = 1365643) (by norm_num)
theorem B4855619 : Blo 2019435 4855619 := bstep (se 1 (by rfl) ⟨3641714, by rfl⟩ : syracuseStep 4855619 = 7283429) B7283429
theorem B3237079 : Blo 2019435 3237079 := bstep (se 1 (by rfl) ⟨2427809, by rfl⟩ : syracuseStep 3237079 = 4855619) B4855619
theorem B4316105 : Blo 2019435 4316105 := bstep (se 2 (by rfl) ⟨1618539, by rfl⟩ : syracuseStep 4316105 = 3237079) B3237079
theorem B11509613 : Blo 2019435 11509613 := bstep (se 3 (by rfl) ⟨2158052, by rfl⟩ : syracuseStep 11509613 = 4316105) B4316105
theorem B7673075 : Blo 2019435 7673075 := bstep (se 1 (by rfl) ⟨5754806, by rfl⟩ : syracuseStep 7673075 = 11509613) B11509613
theorem B5115383 : Blo 2019435 5115383 := bstep (se 1 (by rfl) ⟨3836537, by rfl⟩ : syracuseStep 5115383 = 7673075) B7673075
theorem B3410255 : Blo 2019435 3410255 := bstep (se 1 (by rfl) ⟨2557691, by rfl⟩ : syracuseStep 3410255 = 5115383) B5115383
theorem B2273503 : Blo 2019435 2273503 := bstep (se 1 (by rfl) ⟨1705127, by rfl⟩ : syracuseStep 2273503 = 3410255) B3410255
theorem B3031337 : Blo 2019435 3031337 := bstep (se 2 (by rfl) ⟨1136751, by rfl⟩ : syracuseStep 3031337 = 2273503) B2273503
theorem B2020891 : Blo 2019435 2020891 := bstep (se 1 (by rfl) ⟨1515668, by rfl⟩ : syracuseStep 2020891 = 3031337) B3031337
theorem B3237085 : Blo 2019435 3237085 := bbase (se 3 (by rfl) ⟨606953, by rfl⟩ : syracuseStep 3237085 = 1213907) (by norm_num)
theorem B4316113 : Blo 2019435 4316113 := bstep (se 2 (by rfl) ⟨1618542, by rfl⟩ : syracuseStep 4316113 = 3237085) B3237085
theorem B5754817 : Blo 2019435 5754817 := bstep (se 2 (by rfl) ⟨2158056, by rfl⟩ : syracuseStep 5754817 = 4316113) B4316113
theorem B7673089 : Blo 2019435 7673089 := bstep (se 2 (by rfl) ⟨2877408, by rfl⟩ : syracuseStep 7673089 = 5754817) B5754817
theorem B10230785 : Blo 2019435 10230785 := bstep (se 2 (by rfl) ⟨3836544, by rfl⟩ : syracuseStep 10230785 = 7673089) B7673089
theorem B6820523 : Blo 2019435 6820523 := bstep (se 1 (by rfl) ⟨5115392, by rfl⟩ : syracuseStep 6820523 = 10230785) B10230785
theorem B4547015 : Blo 2019435 4547015 := bstep (se 1 (by rfl) ⟨3410261, by rfl⟩ : syracuseStep 4547015 = 6820523) B6820523
theorem B3031343 : Blo 2019435 3031343 := bstep (se 1 (by rfl) ⟨2273507, by rfl⟩ : syracuseStep 3031343 = 4547015) B4547015
theorem B2020895 : Blo 2019435 2020895 := bstep (se 1 (by rfl) ⟨1515671, by rfl⟩ : syracuseStep 2020895 = 3031343) B3031343
theorem B3031349 : Blo 2019435 3031349 := bbase (se 5 (by rfl) ⟨142094, by rfl⟩ : syracuseStep 3031349 = 284189) (by norm_num)
theorem B2020899 : Blo 2019435 2020899 := bstep (se 1 (by rfl) ⟨1515674, by rfl⟩ : syracuseStep 2020899 = 3031349) B3031349
theorem B5115413 : Blo 2019435 5115413 := bbase (se 6 (by rfl) ⟨119892, by rfl⟩ : syracuseStep 5115413 = 239785) (by norm_num)
theorem B3410275 : Blo 2019435 3410275 := bstep (se 1 (by rfl) ⟨2557706, by rfl⟩ : syracuseStep 3410275 = 5115413) B5115413
theorem B4547033 : Blo 2019435 4547033 := bstep (se 2 (by rfl) ⟨1705137, by rfl⟩ : syracuseStep 4547033 = 3410275) B3410275
theorem B3031355 : Blo 2019435 3031355 := bstep (se 1 (by rfl) ⟨2273516, by rfl⟩ : syracuseStep 3031355 = 4547033) B4547033
theorem B2020903 : Blo 2019435 2020903 := bstep (se 1 (by rfl) ⟨1515677, by rfl⟩ : syracuseStep 2020903 = 3031355) B3031355
theorem B2273521 : Blo 2019435 2273521 := bbase (se 2 (by rfl) ⟨852570, by rfl⟩ : syracuseStep 2273521 = 1705141) (by norm_num)
theorem B3031361 : Blo 2019435 3031361 := bstep (se 2 (by rfl) ⟨1136760, by rfl⟩ : syracuseStep 3031361 = 2273521) B2273521
theorem B2020907 : Blo 2019435 2020907 := bstep (se 1 (by rfl) ⟨1515680, by rfl⟩ : syracuseStep 2020907 = 3031361) B3031361
theorem B2304545 : Blo 2019435 2304545 := bbase (se 2 (by rfl) ⟨864204, by rfl⟩ : syracuseStep 2304545 = 1728409) (by norm_num)
theorem B6145453 : Blo 2019435 6145453 := bstep (se 3 (by rfl) ⟨1152272, by rfl⟩ : syracuseStep 6145453 = 2304545) B2304545
theorem B32775749 : Blo 2019435 32775749 := bstep (se 4 (by rfl) ⟨3072726, by rfl⟩ : syracuseStep 32775749 = 6145453) B6145453
theorem B21850499 : Blo 2019435 21850499 := bstep (se 1 (by rfl) ⟨16387874, by rfl⟩ : syracuseStep 21850499 = 32775749) B32775749
theorem B14566999 : Blo 2019435 14566999 := bstep (se 1 (by rfl) ⟨10925249, by rfl⟩ : syracuseStep 14566999 = 21850499) B21850499
theorem B19422665 : Blo 2019435 19422665 := bstep (se 2 (by rfl) ⟨7283499, by rfl⟩ : syracuseStep 19422665 = 14566999) B14566999
theorem B12948443 : Blo 2019435 12948443 := bstep (se 1 (by rfl) ⟨9711332, by rfl⟩ : syracuseStep 12948443 = 19422665) B19422665
theorem B8632295 : Blo 2019435 8632295 := bstep (se 1 (by rfl) ⟨6474221, by rfl⟩ : syracuseStep 8632295 = 12948443) B12948443
theorem B5754863 : Blo 2019435 5754863 := bstep (se 1 (by rfl) ⟨4316147, by rfl⟩ : syracuseStep 5754863 = 8632295) B8632295
theorem B3836575 : Blo 2019435 3836575 := bstep (se 1 (by rfl) ⟨2877431, by rfl⟩ : syracuseStep 3836575 = 5754863) B5754863
theorem B5115433 : Blo 2019435 5115433 := bstep (se 2 (by rfl) ⟨1918287, by rfl⟩ : syracuseStep 5115433 = 3836575) B3836575
theorem B6820577 : Blo 2019435 6820577 := bstep (se 2 (by rfl) ⟨2557716, by rfl⟩ : syracuseStep 6820577 = 5115433) B5115433
theorem B4547051 : Blo 2019435 4547051 := bstep (se 1 (by rfl) ⟨3410288, by rfl⟩ : syracuseStep 4547051 = 6820577) B6820577
theorem B3031367 : Blo 2019435 3031367 := bstep (se 1 (by rfl) ⟨2273525, by rfl⟩ : syracuseStep 3031367 = 4547051) B4547051
theorem B2020911 : Blo 2019435 2020911 := bstep (se 1 (by rfl) ⟨1515683, by rfl⟩ : syracuseStep 2020911 = 3031367) B3031367
theorem B3031373 : Blo 2019435 3031373 := bbase (se 3 (by rfl) ⟨568382, by rfl⟩ : syracuseStep 3031373 = 1136765) (by norm_num)
theorem B2020915 : Blo 2019435 2020915 := bstep (se 1 (by rfl) ⟨1515686, by rfl⟩ : syracuseStep 2020915 = 3031373) B3031373
theorem B4547069 : Blo 2019435 4547069 := bbase (se 3 (by rfl) ⟨852575, by rfl⟩ : syracuseStep 4547069 = 1705151) (by norm_num)
theorem B3031379 : Blo 2019435 3031379 := bstep (se 1 (by rfl) ⟨2273534, by rfl⟩ : syracuseStep 3031379 = 4547069) B4547069
theorem B2020919 : Blo 2019435 2020919 := bstep (se 1 (by rfl) ⟨1515689, by rfl⟩ : syracuseStep 2020919 = 3031379) B3031379
theorem B3410309 : Blo 2019435 3410309 := bbase (se 4 (by rfl) ⟨319716, by rfl⟩ : syracuseStep 3410309 = 639433) (by norm_num)
theorem B2273539 : Blo 2019435 2273539 := bstep (se 1 (by rfl) ⟨1705154, by rfl⟩ : syracuseStep 2273539 = 3410309) B3410309
theorem B3031385 : Blo 2019435 3031385 := bstep (se 2 (by rfl) ⟨1136769, by rfl⟩ : syracuseStep 3031385 = 2273539) B2273539
theorem B2020923 : Blo 2019435 2020923 := bstep (se 1 (by rfl) ⟨1515692, by rfl⟩ : syracuseStep 2020923 = 3031385) B3031385
theorem B15346421 : Blo 2019435 15346421 := bbase (se 5 (by rfl) ⟨719363, by rfl⟩ : syracuseStep 15346421 = 1438727) (by norm_num)
theorem B10230947 : Blo 2019435 10230947 := bstep (se 1 (by rfl) ⟨7673210, by rfl⟩ : syracuseStep 10230947 = 15346421) B15346421
theorem B6820631 : Blo 2019435 6820631 := bstep (se 1 (by rfl) ⟨5115473, by rfl⟩ : syracuseStep 6820631 = 10230947) B10230947
theorem B4547087 : Blo 2019435 4547087 := bstep (se 1 (by rfl) ⟨3410315, by rfl⟩ : syracuseStep 4547087 = 6820631) B6820631
theorem B3031391 : Blo 2019435 3031391 := bstep (se 1 (by rfl) ⟨2273543, by rfl⟩ : syracuseStep 3031391 = 4547087) B4547087
theorem B2020927 : Blo 2019435 2020927 := bstep (se 1 (by rfl) ⟨1515695, by rfl⟩ : syracuseStep 2020927 = 3031391) B3031391
theorem B3031397 : Blo 2019435 3031397 := bbase (se 4 (by rfl) ⟨284193, by rfl⟩ : syracuseStep 3031397 = 568387) (by norm_num)
theorem B2020931 : Blo 2019435 2020931 := bstep (se 1 (by rfl) ⟨1515698, by rfl⟩ : syracuseStep 2020931 = 3031397) B3031397
theorem B3836621 : Blo 2019435 3836621 := bbase (se 3 (by rfl) ⟨719366, by rfl⟩ : syracuseStep 3836621 = 1438733) (by norm_num)
theorem B2557747 : Blo 2019435 2557747 := bstep (se 1 (by rfl) ⟨1918310, by rfl⟩ : syracuseStep 2557747 = 3836621) B3836621
theorem B3410329 : Blo 2019435 3410329 := bstep (se 2 (by rfl) ⟨1278873, by rfl⟩ : syracuseStep 3410329 = 2557747) B2557747
theorem B4547105 : Blo 2019435 4547105 := bstep (se 2 (by rfl) ⟨1705164, by rfl⟩ : syracuseStep 4547105 = 3410329) B3410329
theorem B3031403 : Blo 2019435 3031403 := bstep (se 1 (by rfl) ⟨2273552, by rfl⟩ : syracuseStep 3031403 = 4547105) B4547105
theorem B2020935 : Blo 2019435 2020935 := bstep (se 1 (by rfl) ⟨1515701, by rfl⟩ : syracuseStep 2020935 = 3031403) B3031403
theorem B2273557 : Blo 2019435 2273557 := bbase (se 6 (by rfl) ⟨53286, by rfl⟩ : syracuseStep 2273557 = 106573) (by norm_num)
theorem B3031409 : Blo 2019435 3031409 := bstep (se 2 (by rfl) ⟨1136778, by rfl⟩ : syracuseStep 3031409 = 2273557) B2273557
theorem B2020939 : Blo 2019435 2020939 := bstep (se 1 (by rfl) ⟨1515704, by rfl⟩ : syracuseStep 2020939 = 3031409) B3031409
theorem B2557757 : Blo 2019435 2557757 := bbase (se 3 (by rfl) ⟨479579, by rfl⟩ : syracuseStep 2557757 = 959159) (by norm_num)
theorem B6820685 : Blo 2019435 6820685 := bstep (se 3 (by rfl) ⟨1278878, by rfl⟩ : syracuseStep 6820685 = 2557757) B2557757
theorem B4547123 : Blo 2019435 4547123 := bstep (se 1 (by rfl) ⟨3410342, by rfl⟩ : syracuseStep 4547123 = 6820685) B6820685
theorem B3031415 : Blo 2019435 3031415 := bstep (se 1 (by rfl) ⟨2273561, by rfl⟩ : syracuseStep 3031415 = 4547123) B4547123
theorem B2020943 : Blo 2019435 2020943 := bstep (se 1 (by rfl) ⟨1515707, by rfl⟩ : syracuseStep 2020943 = 3031415) B3031415
theorem B3031421 : Blo 2019435 3031421 := bbase (se 3 (by rfl) ⟨568391, by rfl⟩ : syracuseStep 3031421 = 1136783) (by norm_num)
theorem B2020947 : Blo 2019435 2020947 := bstep (se 1 (by rfl) ⟨1515710, by rfl⟩ : syracuseStep 2020947 = 3031421) B3031421
theorem B4547141 : Blo 2019435 4547141 := bbase (se 4 (by rfl) ⟨426294, by rfl⟩ : syracuseStep 4547141 = 852589) (by norm_num)
theorem B3031427 : Blo 2019435 3031427 := bstep (se 1 (by rfl) ⟨2273570, by rfl⟩ : syracuseStep 3031427 = 4547141) B4547141
theorem B2020951 : Blo 2019435 2020951 := bstep (se 1 (by rfl) ⟨1515713, by rfl⟩ : syracuseStep 2020951 = 3031427) B3031427
theorem B2158121 : Blo 2019435 2158121 := bbase (se 2 (by rfl) ⟨809295, by rfl⟩ : syracuseStep 2158121 = 1618591) (by norm_num)
theorem B5754989 : Blo 2019435 5754989 := bstep (se 3 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 5754989 = 2158121) B2158121
theorem B3836659 : Blo 2019435 3836659 := bstep (se 1 (by rfl) ⟨2877494, by rfl⟩ : syracuseStep 3836659 = 5754989) B5754989
theorem B5115545 : Blo 2019435 5115545 := bstep (se 2 (by rfl) ⟨1918329, by rfl⟩ : syracuseStep 5115545 = 3836659) B3836659
theorem B3410363 : Blo 2019435 3410363 := bstep (se 1 (by rfl) ⟨2557772, by rfl⟩ : syracuseStep 3410363 = 5115545) B5115545
theorem B2273575 : Blo 2019435 2273575 := bstep (se 1 (by rfl) ⟨1705181, by rfl⟩ : syracuseStep 2273575 = 3410363) B3410363
theorem B3031433 : Blo 2019435 3031433 := bstep (se 2 (by rfl) ⟨1136787, by rfl⟩ : syracuseStep 3031433 = 2273575) B2273575
theorem B2020955 : Blo 2019435 2020955 := bstep (se 1 (by rfl) ⟨1515716, by rfl⟩ : syracuseStep 2020955 = 3031433) B3031433
theorem B10231109 : Blo 2019435 10231109 := bbase (se 4 (by rfl) ⟨959166, by rfl⟩ : syracuseStep 10231109 = 1918333) (by norm_num)
theorem B6820739 : Blo 2019435 6820739 := bstep (se 1 (by rfl) ⟨5115554, by rfl⟩ : syracuseStep 6820739 = 10231109) B10231109
theorem B4547159 : Blo 2019435 4547159 := bstep (se 1 (by rfl) ⟨3410369, by rfl⟩ : syracuseStep 4547159 = 6820739) B6820739
theorem B3031439 : Blo 2019435 3031439 := bstep (se 1 (by rfl) ⟨2273579, by rfl⟩ : syracuseStep 3031439 = 4547159) B4547159
theorem B2020959 : Blo 2019435 2020959 := bstep (se 1 (by rfl) ⟨1515719, by rfl⟩ : syracuseStep 2020959 = 3031439) B3031439
theorem B3031445 : Blo 2019435 3031445 := bbase (se 6 (by rfl) ⟨71049, by rfl⟩ : syracuseStep 3031445 = 142099) (by norm_num)
theorem B2020963 : Blo 2019435 2020963 := bstep (se 1 (by rfl) ⟨1515722, by rfl⟩ : syracuseStep 2020963 = 3031445) B3031445
theorem B6913829 : Blo 2019435 6913829 := bbase (se 4 (by rfl) ⟨648171, by rfl⟩ : syracuseStep 6913829 = 1296343) (by norm_num)
theorem B4609219 : Blo 2019435 4609219 := bstep (se 1 (by rfl) ⟨3456914, by rfl⟩ : syracuseStep 4609219 = 6913829) B6913829
theorem B6145625 : Blo 2019435 6145625 := bstep (se 2 (by rfl) ⟨2304609, by rfl⟩ : syracuseStep 6145625 = 4609219) B4609219
theorem B4097083 : Blo 2019435 4097083 := bstep (se 1 (by rfl) ⟨3072812, by rfl⟩ : syracuseStep 4097083 = 6145625) B6145625
theorem B5462777 : Blo 2019435 5462777 := bstep (se 2 (by rfl) ⟨2048541, by rfl⟩ : syracuseStep 5462777 = 4097083) B4097083
theorem B3641851 : Blo 2019435 3641851 := bstep (se 1 (by rfl) ⟨2731388, by rfl⟩ : syracuseStep 3641851 = 5462777) B5462777
theorem B4855801 : Blo 2019435 4855801 := bstep (se 2 (by rfl) ⟨1820925, by rfl⟩ : syracuseStep 4855801 = 3641851) B3641851
theorem B6474401 : Blo 2019435 6474401 := bstep (se 2 (by rfl) ⟨2427900, by rfl⟩ : syracuseStep 6474401 = 4855801) B4855801
theorem B4316267 : Blo 2019435 4316267 := bstep (se 1 (by rfl) ⟨3237200, by rfl⟩ : syracuseStep 4316267 = 6474401) B6474401
theorem B11510045 : Blo 2019435 11510045 := bstep (se 3 (by rfl) ⟨2158133, by rfl⟩ : syracuseStep 11510045 = 4316267) B4316267
theorem B7673363 : Blo 2019435 7673363 := bstep (se 1 (by rfl) ⟨5755022, by rfl⟩ : syracuseStep 7673363 = 11510045) B11510045
theorem B5115575 : Blo 2019435 5115575 := bstep (se 1 (by rfl) ⟨3836681, by rfl⟩ : syracuseStep 5115575 = 7673363) B7673363
theorem B3410383 : Blo 2019435 3410383 := bstep (se 1 (by rfl) ⟨2557787, by rfl⟩ : syracuseStep 3410383 = 5115575) B5115575
theorem B4547177 : Blo 2019435 4547177 := bstep (se 2 (by rfl) ⟨1705191, by rfl⟩ : syracuseStep 4547177 = 3410383) B3410383
theorem B3031451 : Blo 2019435 3031451 := bstep (se 1 (by rfl) ⟨2273588, by rfl⟩ : syracuseStep 3031451 = 4547177) B4547177
theorem B2020967 : Blo 2019435 2020967 := bstep (se 1 (by rfl) ⟨1515725, by rfl⟩ : syracuseStep 2020967 = 3031451) B3031451
theorem B2273593 : Blo 2019435 2273593 := bbase (se 2 (by rfl) ⟨852597, by rfl⟩ : syracuseStep 2273593 = 1705195) (by norm_num)
theorem B3031457 : Blo 2019435 3031457 := bstep (se 2 (by rfl) ⟨1136796, by rfl⟩ : syracuseStep 3031457 = 2273593) B2273593
theorem B2020971 : Blo 2019435 2020971 := bstep (se 1 (by rfl) ⟨1515728, by rfl⟩ : syracuseStep 2020971 = 3031457) B3031457
theorem B5755045 : Blo 2019435 5755045 := bbase (se 4 (by rfl) ⟨539535, by rfl⟩ : syracuseStep 5755045 = 1079071) (by norm_num)
theorem B7673393 : Blo 2019435 7673393 := bstep (se 2 (by rfl) ⟨2877522, by rfl⟩ : syracuseStep 7673393 = 5755045) B5755045
theorem B5115595 : Blo 2019435 5115595 := bstep (se 1 (by rfl) ⟨3836696, by rfl⟩ : syracuseStep 5115595 = 7673393) B7673393
theorem B6820793 : Blo 2019435 6820793 := bstep (se 2 (by rfl) ⟨2557797, by rfl⟩ : syracuseStep 6820793 = 5115595) B5115595
theorem B4547195 : Blo 2019435 4547195 := bstep (se 1 (by rfl) ⟨3410396, by rfl⟩ : syracuseStep 4547195 = 6820793) B6820793
theorem B3031463 : Blo 2019435 3031463 := bstep (se 1 (by rfl) ⟨2273597, by rfl⟩ : syracuseStep 3031463 = 4547195) B4547195
theorem B2020975 : Blo 2019435 2020975 := bstep (se 1 (by rfl) ⟨1515731, by rfl⟩ : syracuseStep 2020975 = 3031463) B3031463
theorem B3031469 : Blo 2019435 3031469 := bbase (se 3 (by rfl) ⟨568400, by rfl⟩ : syracuseStep 3031469 = 1136801) (by norm_num)
theorem B2020979 : Blo 2019435 2020979 := bstep (se 1 (by rfl) ⟨1515734, by rfl⟩ : syracuseStep 2020979 = 3031469) B3031469
theorem B4547213 : Blo 2019435 4547213 := bbase (se 3 (by rfl) ⟨852602, by rfl⟩ : syracuseStep 4547213 = 1705205) (by norm_num)
theorem B3031475 : Blo 2019435 3031475 := bstep (se 1 (by rfl) ⟨2273606, by rfl⟩ : syracuseStep 3031475 = 4547213) B4547213
theorem B2020983 : Blo 2019435 2020983 := bstep (se 1 (by rfl) ⟨1515737, by rfl⟩ : syracuseStep 2020983 = 3031475) B3031475
theorem B2557813 : Blo 2019435 2557813 := bbase (se 5 (by rfl) ⟨119897, by rfl⟩ : syracuseStep 2557813 = 239795) (by norm_num)
theorem B3410417 : Blo 2019435 3410417 := bstep (se 2 (by rfl) ⟨1278906, by rfl⟩ : syracuseStep 3410417 = 2557813) B2557813
theorem B2273611 : Blo 2019435 2273611 := bstep (se 1 (by rfl) ⟨1705208, by rfl⟩ : syracuseStep 2273611 = 3410417) B3410417
theorem B3031481 : Blo 2019435 3031481 := bstep (se 2 (by rfl) ⟨1136805, by rfl⟩ : syracuseStep 3031481 = 2273611) B2273611
theorem B2020987 : Blo 2019435 2020987 := bstep (se 1 (by rfl) ⟨1515740, by rfl⟩ : syracuseStep 2020987 = 3031481) B3031481
theorem B14567573 : Blo 2019435 14567573 := bbase (se 6 (by rfl) ⟨341427, by rfl⟩ : syracuseStep 14567573 = 682855) (by norm_num)
theorem B38846861 : Blo 2019435 38846861 := bstep (se 3 (by rfl) ⟨7283786, by rfl⟩ : syracuseStep 38846861 = 14567573) B14567573
theorem B25897907 : Blo 2019435 25897907 := bstep (se 1 (by rfl) ⟨19423430, by rfl⟩ : syracuseStep 25897907 = 38846861) B38846861
theorem B17265271 : Blo 2019435 17265271 := bstep (se 1 (by rfl) ⟨12948953, by rfl⟩ : syracuseStep 17265271 = 25897907) B25897907
theorem B23020361 : Blo 2019435 23020361 := bstep (se 2 (by rfl) ⟨8632635, by rfl⟩ : syracuseStep 23020361 = 17265271) B17265271
theorem B15346907 : Blo 2019435 15346907 := bstep (se 1 (by rfl) ⟨11510180, by rfl⟩ : syracuseStep 15346907 = 23020361) B23020361
theorem B10231271 : Blo 2019435 10231271 := bstep (se 1 (by rfl) ⟨7673453, by rfl⟩ : syracuseStep 10231271 = 15346907) B15346907
theorem B6820847 : Blo 2019435 6820847 := bstep (se 1 (by rfl) ⟨5115635, by rfl⟩ : syracuseStep 6820847 = 10231271) B10231271
theorem B4547231 : Blo 2019435 4547231 := bstep (se 1 (by rfl) ⟨3410423, by rfl⟩ : syracuseStep 4547231 = 6820847) B6820847
theorem B3031487 : Blo 2019435 3031487 := bstep (se 1 (by rfl) ⟨2273615, by rfl⟩ : syracuseStep 3031487 = 4547231) B4547231
theorem B2020991 : Blo 2019435 2020991 := bstep (se 1 (by rfl) ⟨1515743, by rfl⟩ : syracuseStep 2020991 = 3031487) B3031487
theorem B3031493 : Blo 2019435 3031493 := bbase (se 4 (by rfl) ⟨284202, by rfl⟩ : syracuseStep 3031493 = 568405) (by norm_num)
theorem B2020995 : Blo 2019435 2020995 := bstep (se 1 (by rfl) ⟨1515746, by rfl⟩ : syracuseStep 2020995 = 3031493) B3031493
theorem B3410437 : Blo 2019435 3410437 := bbase (se 4 (by rfl) ⟨319728, by rfl⟩ : syracuseStep 3410437 = 639457) (by norm_num)
theorem B4547249 : Blo 2019435 4547249 := bstep (se 2 (by rfl) ⟨1705218, by rfl⟩ : syracuseStep 4547249 = 3410437) B3410437
theorem B3031499 : Blo 2019435 3031499 := bstep (se 1 (by rfl) ⟨2273624, by rfl⟩ : syracuseStep 3031499 = 4547249) B4547249
theorem B2020999 : Blo 2019435 2020999 := bstep (se 1 (by rfl) ⟨1515749, by rfl⟩ : syracuseStep 2020999 = 3031499) B3031499
theorem B2273629 : Blo 2019435 2273629 := bbase (se 3 (by rfl) ⟨426305, by rfl⟩ : syracuseStep 2273629 = 852611) (by norm_num)
theorem B3031505 : Blo 2019435 3031505 := bstep (se 2 (by rfl) ⟨1136814, by rfl⟩ : syracuseStep 3031505 = 2273629) B2273629
theorem B2021003 : Blo 2019435 2021003 := bstep (se 1 (by rfl) ⟨1515752, by rfl⟩ : syracuseStep 2021003 = 3031505) B3031505
theorem B6820901 : Blo 2019435 6820901 := bbase (se 4 (by rfl) ⟨639459, by rfl⟩ : syracuseStep 6820901 = 1278919) (by norm_num)
theorem B4547267 : Blo 2019435 4547267 := bstep (se 1 (by rfl) ⟨3410450, by rfl⟩ : syracuseStep 4547267 = 6820901) B6820901
theorem B3031511 : Blo 2019435 3031511 := bstep (se 1 (by rfl) ⟨2273633, by rfl⟩ : syracuseStep 3031511 = 4547267) B4547267
theorem B2021007 : Blo 2019435 2021007 := bstep (se 1 (by rfl) ⟨1515755, by rfl⟩ : syracuseStep 2021007 = 3031511) B3031511
theorem B3031517 : Blo 2019435 3031517 := bbase (se 3 (by rfl) ⟨568409, by rfl⟩ : syracuseStep 3031517 = 1136819) (by norm_num)
theorem B2021011 : Blo 2019435 2021011 := bstep (se 1 (by rfl) ⟨1515758, by rfl⟩ : syracuseStep 2021011 = 3031517) B3031517
theorem B4547285 : Blo 2019435 4547285 := bbase (se 7 (by rfl) ⟨53288, by rfl⟩ : syracuseStep 4547285 = 106577) (by norm_num)
theorem B3031523 : Blo 2019435 3031523 := bstep (se 1 (by rfl) ⟨2273642, by rfl⟩ : syracuseStep 3031523 = 4547285) B4547285
theorem B2021015 : Blo 2019435 2021015 := bstep (se 1 (by rfl) ⟨1515761, by rfl⟩ : syracuseStep 2021015 = 3031523) B3031523
theorem B8632757 : Blo 2019435 8632757 := bbase (se 5 (by rfl) ⟨404660, by rfl⟩ : syracuseStep 8632757 = 809321) (by norm_num)
theorem B5755171 : Blo 2019435 5755171 := bstep (se 1 (by rfl) ⟨4316378, by rfl⟩ : syracuseStep 5755171 = 8632757) B8632757
theorem B7673561 : Blo 2019435 7673561 := bstep (se 2 (by rfl) ⟨2877585, by rfl⟩ : syracuseStep 7673561 = 5755171) B5755171
theorem B5115707 : Blo 2019435 5115707 := bstep (se 1 (by rfl) ⟨3836780, by rfl⟩ : syracuseStep 5115707 = 7673561) B7673561
theorem B3410471 : Blo 2019435 3410471 := bstep (se 1 (by rfl) ⟨2557853, by rfl⟩ : syracuseStep 3410471 = 5115707) B5115707
theorem B2273647 : Blo 2019435 2273647 := bstep (se 1 (by rfl) ⟨1705235, by rfl⟩ : syracuseStep 2273647 = 3410471) B3410471
theorem B3031529 : Blo 2019435 3031529 := bstep (se 2 (by rfl) ⟨1136823, by rfl⟩ : syracuseStep 3031529 = 2273647) B2273647
theorem B2021019 : Blo 2019435 2021019 := bstep (se 1 (by rfl) ⟨1515764, by rfl⟩ : syracuseStep 2021019 = 3031529) B3031529
theorem B22149845 : Blo 2019435 22149845 := bbase (se 7 (by rfl) ⟨259568, by rfl⟩ : syracuseStep 22149845 = 519137) (by norm_num)
theorem B14766563 : Blo 2019435 14766563 := bstep (se 1 (by rfl) ⟨11074922, by rfl⟩ : syracuseStep 14766563 = 22149845) B22149845
theorem B9844375 : Blo 2019435 9844375 := bstep (se 1 (by rfl) ⟨7383281, by rfl⟩ : syracuseStep 9844375 = 14766563) B14766563
theorem B13125833 : Blo 2019435 13125833 := bstep (se 2 (by rfl) ⟨4922187, by rfl⟩ : syracuseStep 13125833 = 9844375) B9844375
theorem B8750555 : Blo 2019435 8750555 := bstep (se 1 (by rfl) ⟨6562916, by rfl⟩ : syracuseStep 8750555 = 13125833) B13125833
theorem B5833703 : Blo 2019435 5833703 := bstep (se 1 (by rfl) ⟨4375277, by rfl⟩ : syracuseStep 5833703 = 8750555) B8750555
theorem B3889135 : Blo 2019435 3889135 := bstep (se 1 (by rfl) ⟨2916851, by rfl⟩ : syracuseStep 3889135 = 5833703) B5833703
theorem B5185513 : Blo 2019435 5185513 := bstep (se 2 (by rfl) ⟨1944567, by rfl⟩ : syracuseStep 5185513 = 3889135) B3889135
theorem B6914017 : Blo 2019435 6914017 := bstep (se 2 (by rfl) ⟨2592756, by rfl⟩ : syracuseStep 6914017 = 5185513) B5185513
theorem B36874757 : Blo 2019435 36874757 := bstep (se 4 (by rfl) ⟨3457008, by rfl⟩ : syracuseStep 36874757 = 6914017) B6914017
theorem B24583171 : Blo 2019435 24583171 := bstep (se 1 (by rfl) ⟨18437378, by rfl⟩ : syracuseStep 24583171 = 36874757) B36874757
theorem B32777561 : Blo 2019435 32777561 := bstep (se 2 (by rfl) ⟨12291585, by rfl⟩ : syracuseStep 32777561 = 24583171) B24583171
theorem B21851707 : Blo 2019435 21851707 := bstep (se 1 (by rfl) ⟨16388780, by rfl⟩ : syracuseStep 21851707 = 32777561) B32777561
theorem B29135609 : Blo 2019435 29135609 := bstep (se 2 (by rfl) ⟨10925853, by rfl⟩ : syracuseStep 29135609 = 21851707) B21851707
theorem B19423739 : Blo 2019435 19423739 := bstep (se 1 (by rfl) ⟨14567804, by rfl⟩ : syracuseStep 19423739 = 29135609) B29135609
theorem B12949159 : Blo 2019435 12949159 := bstep (se 1 (by rfl) ⟨9711869, by rfl⟩ : syracuseStep 12949159 = 19423739) B19423739
theorem B17265545 : Blo 2019435 17265545 := bstep (se 2 (by rfl) ⟨6474579, by rfl⟩ : syracuseStep 17265545 = 12949159) B12949159
theorem B11510363 : Blo 2019435 11510363 := bstep (se 1 (by rfl) ⟨8632772, by rfl⟩ : syracuseStep 11510363 = 17265545) B17265545
theorem B7673575 : Blo 2019435 7673575 := bstep (se 1 (by rfl) ⟨5755181, by rfl⟩ : syracuseStep 7673575 = 11510363) B11510363
theorem B10231433 : Blo 2019435 10231433 := bstep (se 2 (by rfl) ⟨3836787, by rfl⟩ : syracuseStep 10231433 = 7673575) B7673575
theorem B6820955 : Blo 2019435 6820955 := bstep (se 1 (by rfl) ⟨5115716, by rfl⟩ : syracuseStep 6820955 = 10231433) B10231433
theorem B4547303 : Blo 2019435 4547303 := bstep (se 1 (by rfl) ⟨3410477, by rfl⟩ : syracuseStep 4547303 = 6820955) B6820955
theorem B3031535 : Blo 2019435 3031535 := bstep (se 1 (by rfl) ⟨2273651, by rfl⟩ : syracuseStep 3031535 = 4547303) B4547303
theorem B2021023 : Blo 2019435 2021023 := bstep (se 1 (by rfl) ⟨1515767, by rfl⟩ : syracuseStep 2021023 = 3031535) B3031535
theorem B3031541 : Blo 2019435 3031541 := bbase (se 5 (by rfl) ⟨142103, by rfl⟩ : syracuseStep 3031541 = 284207) (by norm_num)
theorem B2021027 : Blo 2019435 2021027 := bstep (se 1 (by rfl) ⟨1515770, by rfl⟩ : syracuseStep 2021027 = 3031541) B3031541
theorem B5755205 : Blo 2019435 5755205 := bbase (se 4 (by rfl) ⟨539550, by rfl⟩ : syracuseStep 5755205 = 1079101) (by norm_num)
theorem B3836803 : Blo 2019435 3836803 := bstep (se 1 (by rfl) ⟨2877602, by rfl⟩ : syracuseStep 3836803 = 5755205) B5755205
theorem B5115737 : Blo 2019435 5115737 := bstep (se 2 (by rfl) ⟨1918401, by rfl⟩ : syracuseStep 5115737 = 3836803) B3836803
theorem B3410491 : Blo 2019435 3410491 := bstep (se 1 (by rfl) ⟨2557868, by rfl⟩ : syracuseStep 3410491 = 5115737) B5115737
theorem B4547321 : Blo 2019435 4547321 := bstep (se 2 (by rfl) ⟨1705245, by rfl⟩ : syracuseStep 4547321 = 3410491) B3410491
theorem B3031547 : Blo 2019435 3031547 := bstep (se 1 (by rfl) ⟨2273660, by rfl⟩ : syracuseStep 3031547 = 4547321) B4547321
theorem B2021031 : Blo 2019435 2021031 := bstep (se 1 (by rfl) ⟨1515773, by rfl⟩ : syracuseStep 2021031 = 3031547) B3031547
theorem B2273665 : Blo 2019435 2273665 := bbase (se 2 (by rfl) ⟨852624, by rfl⟩ : syracuseStep 2273665 = 1705249) (by norm_num)
theorem B3031553 : Blo 2019435 3031553 := bstep (se 2 (by rfl) ⟨1136832, by rfl⟩ : syracuseStep 3031553 = 2273665) B2273665
theorem B2021035 : Blo 2019435 2021035 := bstep (se 1 (by rfl) ⟨1515776, by rfl⟩ : syracuseStep 2021035 = 3031553) B3031553
theorem B5115757 : Blo 2019435 5115757 := bbase (se 3 (by rfl) ⟨959204, by rfl⟩ : syracuseStep 5115757 = 1918409) (by norm_num)
theorem B6821009 : Blo 2019435 6821009 := bstep (se 2 (by rfl) ⟨2557878, by rfl⟩ : syracuseStep 6821009 = 5115757) B5115757
theorem B4547339 : Blo 2019435 4547339 := bstep (se 1 (by rfl) ⟨3410504, by rfl⟩ : syracuseStep 4547339 = 6821009) B6821009
theorem B3031559 : Blo 2019435 3031559 := bstep (se 1 (by rfl) ⟨2273669, by rfl⟩ : syracuseStep 3031559 = 4547339) B4547339
theorem B2021039 : Blo 2019435 2021039 := bstep (se 1 (by rfl) ⟨1515779, by rfl⟩ : syracuseStep 2021039 = 3031559) B3031559
theorem B3031565 : Blo 2019435 3031565 := bbase (se 3 (by rfl) ⟨568418, by rfl⟩ : syracuseStep 3031565 = 1136837) (by norm_num)
theorem B2021043 : Blo 2019435 2021043 := bstep (se 1 (by rfl) ⟨1515782, by rfl⟩ : syracuseStep 2021043 = 3031565) B3031565
theorem B4547357 : Blo 2019435 4547357 := bbase (se 3 (by rfl) ⟨852629, by rfl⟩ : syracuseStep 4547357 = 1705259) (by norm_num)
theorem B3031571 : Blo 2019435 3031571 := bstep (se 1 (by rfl) ⟨2273678, by rfl⟩ : syracuseStep 3031571 = 4547357) B4547357
theorem B2021047 : Blo 2019435 2021047 := bstep (se 1 (by rfl) ⟨1515785, by rfl⟩ : syracuseStep 2021047 = 3031571) B3031571
theorem B3410525 : Blo 2019435 3410525 := bbase (se 3 (by rfl) ⟨639473, by rfl⟩ : syracuseStep 3410525 = 1278947) (by norm_num)
theorem B2273683 : Blo 2019435 2273683 := bstep (se 1 (by rfl) ⟨1705262, by rfl⟩ : syracuseStep 2273683 = 3410525) B3410525
theorem B3031577 : Blo 2019435 3031577 := bstep (se 2 (by rfl) ⟨1136841, by rfl⟩ : syracuseStep 3031577 = 2273683) B2273683
theorem B2021051 : Blo 2019435 2021051 := bstep (se 1 (by rfl) ⟨1515788, by rfl⟩ : syracuseStep 2021051 = 3031577) B3031577
theorem B3237341 : Blo 2019435 3237341 := bbase (se 3 (by rfl) ⟨607001, by rfl⟩ : syracuseStep 3237341 = 1214003) (by norm_num)
theorem B8632909 : Blo 2019435 8632909 := bstep (se 3 (by rfl) ⟨1618670, by rfl⟩ : syracuseStep 8632909 = 3237341) B3237341
theorem B11510545 : Blo 2019435 11510545 := bstep (se 2 (by rfl) ⟨4316454, by rfl⟩ : syracuseStep 11510545 = 8632909) B8632909
theorem B15347393 : Blo 2019435 15347393 := bstep (se 2 (by rfl) ⟨5755272, by rfl⟩ : syracuseStep 15347393 = 11510545) B11510545
theorem B10231595 : Blo 2019435 10231595 := bstep (se 1 (by rfl) ⟨7673696, by rfl⟩ : syracuseStep 10231595 = 15347393) B15347393
theorem B6821063 : Blo 2019435 6821063 := bstep (se 1 (by rfl) ⟨5115797, by rfl⟩ : syracuseStep 6821063 = 10231595) B10231595
theorem B4547375 : Blo 2019435 4547375 := bstep (se 1 (by rfl) ⟨3410531, by rfl⟩ : syracuseStep 4547375 = 6821063) B6821063
theorem B3031583 : Blo 2019435 3031583 := bstep (se 1 (by rfl) ⟨2273687, by rfl⟩ : syracuseStep 3031583 = 4547375) B4547375
theorem B2021055 : Blo 2019435 2021055 := bstep (se 1 (by rfl) ⟨1515791, by rfl⟩ : syracuseStep 2021055 = 3031583) B3031583
theorem B3031589 : Blo 2019435 3031589 := bbase (se 4 (by rfl) ⟨284211, by rfl⟩ : syracuseStep 3031589 = 568423) (by norm_num)
theorem B2021059 : Blo 2019435 2021059 := bstep (se 1 (by rfl) ⟨1515794, by rfl⟩ : syracuseStep 2021059 = 3031589) B3031589
theorem B2557909 : Blo 2019435 2557909 := bbase (se 7 (by rfl) ⟨29975, by rfl⟩ : syracuseStep 2557909 = 59951) (by norm_num)
theorem B3410545 : Blo 2019435 3410545 := bstep (se 2 (by rfl) ⟨1278954, by rfl⟩ : syracuseStep 3410545 = 2557909) B2557909
theorem B4547393 : Blo 2019435 4547393 := bstep (se 2 (by rfl) ⟨1705272, by rfl⟩ : syracuseStep 4547393 = 3410545) B3410545
theorem B3031595 : Blo 2019435 3031595 := bstep (se 1 (by rfl) ⟨2273696, by rfl⟩ : syracuseStep 3031595 = 4547393) B4547393
theorem B2021063 : Blo 2019435 2021063 := bstep (se 1 (by rfl) ⟨1515797, by rfl⟩ : syracuseStep 2021063 = 3031595) B3031595
theorem B2273701 : Blo 2019435 2273701 := bbase (se 4 (by rfl) ⟨213159, by rfl⟩ : syracuseStep 2273701 = 426319) (by norm_num)
theorem B3031601 : Blo 2019435 3031601 := bstep (se 2 (by rfl) ⟨1136850, by rfl⟩ : syracuseStep 3031601 = 2273701) B2273701
theorem B2021067 : Blo 2019435 2021067 := bstep (se 1 (by rfl) ⟨1515800, by rfl⟩ : syracuseStep 2021067 = 3031601) B3031601
theorem B3457093 : Blo 2019435 3457093 := bbase (se 4 (by rfl) ⟨324102, by rfl⟩ : syracuseStep 3457093 = 648205) (by norm_num)
theorem B4609457 : Blo 2019435 4609457 := bstep (se 2 (by rfl) ⟨1728546, by rfl⟩ : syracuseStep 4609457 = 3457093) B3457093
theorem B3072971 : Blo 2019435 3072971 := bstep (se 1 (by rfl) ⟨2304728, by rfl⟩ : syracuseStep 3072971 = 4609457) B4609457
theorem B2048647 : Blo 2019435 2048647 := bstep (se 1 (by rfl) ⟨1536485, by rfl⟩ : syracuseStep 2048647 = 3072971) B3072971
theorem B2731529 : Blo 2019435 2731529 := bstep (se 2 (by rfl) ⟨1024323, by rfl⟩ : syracuseStep 2731529 = 2048647) B2048647
theorem B7284077 : Blo 2019435 7284077 := bstep (se 3 (by rfl) ⟨1365764, by rfl⟩ : syracuseStep 7284077 = 2731529) B2731529
theorem B4856051 : Blo 2019435 4856051 := bstep (se 1 (by rfl) ⟨3642038, by rfl⟩ : syracuseStep 4856051 = 7284077) B7284077
theorem B12949469 : Blo 2019435 12949469 := bstep (se 3 (by rfl) ⟨2428025, by rfl⟩ : syracuseStep 12949469 = 4856051) B4856051
theorem B8632979 : Blo 2019435 8632979 := bstep (se 1 (by rfl) ⟨6474734, by rfl⟩ : syracuseStep 8632979 = 12949469) B12949469
theorem B5755319 : Blo 2019435 5755319 := bstep (se 1 (by rfl) ⟨4316489, by rfl⟩ : syracuseStep 5755319 = 8632979) B8632979
theorem B3836879 : Blo 2019435 3836879 := bstep (se 1 (by rfl) ⟨2877659, by rfl⟩ : syracuseStep 3836879 = 5755319) B5755319
theorem B2557919 : Blo 2019435 2557919 := bstep (se 1 (by rfl) ⟨1918439, by rfl⟩ : syracuseStep 2557919 = 3836879) B3836879
theorem B6821117 : Blo 2019435 6821117 := bstep (se 3 (by rfl) ⟨1278959, by rfl⟩ : syracuseStep 6821117 = 2557919) B2557919
theorem B4547411 : Blo 2019435 4547411 := bstep (se 1 (by rfl) ⟨3410558, by rfl⟩ : syracuseStep 4547411 = 6821117) B6821117
theorem B3031607 : Blo 2019435 3031607 := bstep (se 1 (by rfl) ⟨2273705, by rfl⟩ : syracuseStep 3031607 = 4547411) B4547411
theorem B2021071 : Blo 2019435 2021071 := bstep (se 1 (by rfl) ⟨1515803, by rfl⟩ : syracuseStep 2021071 = 3031607) B3031607
theorem B3031613 : Blo 2019435 3031613 := bbase (se 3 (by rfl) ⟨568427, by rfl⟩ : syracuseStep 3031613 = 1136855) (by norm_num)
theorem B2021075 : Blo 2019435 2021075 := bstep (se 1 (by rfl) ⟨1515806, by rfl⟩ : syracuseStep 2021075 = 3031613) B3031613
theorem B4547429 : Blo 2019435 4547429 := bbase (se 4 (by rfl) ⟨426321, by rfl⟩ : syracuseStep 4547429 = 852643) (by norm_num)
theorem B3031619 : Blo 2019435 3031619 := bstep (se 1 (by rfl) ⟨2273714, by rfl⟩ : syracuseStep 3031619 = 4547429) B4547429
theorem B2021079 : Blo 2019435 2021079 := bstep (se 1 (by rfl) ⟨1515809, by rfl⟩ : syracuseStep 2021079 = 3031619) B3031619
theorem B5115869 : Blo 2019435 5115869 := bbase (se 3 (by rfl) ⟨959225, by rfl⟩ : syracuseStep 5115869 = 1918451) (by norm_num)
theorem B3410579 : Blo 2019435 3410579 := bstep (se 1 (by rfl) ⟨2557934, by rfl⟩ : syracuseStep 3410579 = 5115869) B5115869
theorem B2273719 : Blo 2019435 2273719 := bstep (se 1 (by rfl) ⟨1705289, by rfl⟩ : syracuseStep 2273719 = 3410579) B3410579
theorem B3031625 : Blo 2019435 3031625 := bstep (se 2 (by rfl) ⟨1136859, by rfl⟩ : syracuseStep 3031625 = 2273719) B2273719
theorem B2021083 : Blo 2019435 2021083 := bstep (se 1 (by rfl) ⟨1515812, by rfl⟩ : syracuseStep 2021083 = 3031625) B3031625
theorem B3836909 : Blo 2019435 3836909 := bbase (se 3 (by rfl) ⟨719420, by rfl⟩ : syracuseStep 3836909 = 1438841) (by norm_num)
theorem B10231757 : Blo 2019435 10231757 := bstep (se 3 (by rfl) ⟨1918454, by rfl⟩ : syracuseStep 10231757 = 3836909) B3836909
theorem B6821171 : Blo 2019435 6821171 := bstep (se 1 (by rfl) ⟨5115878, by rfl⟩ : syracuseStep 6821171 = 10231757) B10231757
theorem B4547447 : Blo 2019435 4547447 := bstep (se 1 (by rfl) ⟨3410585, by rfl⟩ : syracuseStep 4547447 = 6821171) B6821171
theorem B3031631 : Blo 2019435 3031631 := bstep (se 1 (by rfl) ⟨2273723, by rfl⟩ : syracuseStep 3031631 = 4547447) B4547447
theorem B2021087 : Blo 2019435 2021087 := bstep (se 1 (by rfl) ⟨1515815, by rfl⟩ : syracuseStep 2021087 = 3031631) B3031631
theorem B3031637 : Blo 2019435 3031637 := bbase (se 8 (by rfl) ⟨17763, by rfl⟩ : syracuseStep 3031637 = 35527) (by norm_num)
theorem B2021091 : Blo 2019435 2021091 := bstep (se 1 (by rfl) ⟨1515818, by rfl⟩ : syracuseStep 2021091 = 3031637) B3031637
theorem B4922365 : Blo 2019435 4922365 := bbase (se 3 (by rfl) ⟨922943, by rfl⟩ : syracuseStep 4922365 = 1845887) (by norm_num)
theorem B6563153 : Blo 2019435 6563153 := bstep (se 2 (by rfl) ⟨2461182, by rfl⟩ : syracuseStep 6563153 = 4922365) B4922365
theorem B17501741 : Blo 2019435 17501741 := bstep (se 3 (by rfl) ⟨3281576, by rfl⟩ : syracuseStep 17501741 = 6563153) B6563153
theorem B11667827 : Blo 2019435 11667827 := bstep (se 1 (by rfl) ⟨8750870, by rfl⟩ : syracuseStep 11667827 = 17501741) B17501741
theorem B7778551 : Blo 2019435 7778551 := bstep (se 1 (by rfl) ⟨5833913, by rfl⟩ : syracuseStep 7778551 = 11667827) B11667827
theorem B10371401 : Blo 2019435 10371401 := bstep (se 2 (by rfl) ⟨3889275, by rfl⟩ : syracuseStep 10371401 = 7778551) B7778551
theorem B6914267 : Blo 2019435 6914267 := bstep (se 1 (by rfl) ⟨5185700, by rfl⟩ : syracuseStep 6914267 = 10371401) B10371401
theorem B4609511 : Blo 2019435 4609511 := bstep (se 1 (by rfl) ⟨3457133, by rfl⟩ : syracuseStep 4609511 = 6914267) B6914267
theorem B3073007 : Blo 2019435 3073007 := bstep (se 1 (by rfl) ⟨2304755, by rfl⟩ : syracuseStep 3073007 = 4609511) B4609511
theorem B2048671 : Blo 2019435 2048671 := bstep (se 1 (by rfl) ⟨1536503, by rfl⟩ : syracuseStep 2048671 = 3073007) B3073007
theorem B10926245 : Blo 2019435 10926245 := bstep (se 4 (by rfl) ⟨1024335, by rfl⟩ : syracuseStep 10926245 = 2048671) B2048671
theorem B7284163 : Blo 2019435 7284163 := bstep (se 1 (by rfl) ⟨5463122, by rfl⟩ : syracuseStep 7284163 = 10926245) B10926245
theorem B9712217 : Blo 2019435 9712217 := bstep (se 2 (by rfl) ⟨3642081, by rfl⟩ : syracuseStep 9712217 = 7284163) B7284163
theorem B6474811 : Blo 2019435 6474811 := bstep (se 1 (by rfl) ⟨4856108, by rfl⟩ : syracuseStep 6474811 = 9712217) B9712217
theorem B8633081 : Blo 2019435 8633081 := bstep (se 2 (by rfl) ⟨3237405, by rfl⟩ : syracuseStep 8633081 = 6474811) B6474811
theorem B5755387 : Blo 2019435 5755387 := bstep (se 1 (by rfl) ⟨4316540, by rfl⟩ : syracuseStep 5755387 = 8633081) B8633081
theorem B7673849 : Blo 2019435 7673849 := bstep (se 2 (by rfl) ⟨2877693, by rfl⟩ : syracuseStep 7673849 = 5755387) B5755387
theorem B5115899 : Blo 2019435 5115899 := bstep (se 1 (by rfl) ⟨3836924, by rfl⟩ : syracuseStep 5115899 = 7673849) B7673849
theorem B3410599 : Blo 2019435 3410599 := bstep (se 1 (by rfl) ⟨2557949, by rfl⟩ : syracuseStep 3410599 = 5115899) B5115899
theorem B4547465 : Blo 2019435 4547465 := bstep (se 2 (by rfl) ⟨1705299, by rfl⟩ : syracuseStep 4547465 = 3410599) B3410599
theorem B3031643 : Blo 2019435 3031643 := bstep (se 1 (by rfl) ⟨2273732, by rfl⟩ : syracuseStep 3031643 = 4547465) B4547465
theorem B2021095 : Blo 2019435 2021095 := bstep (se 1 (by rfl) ⟨1515821, by rfl⟩ : syracuseStep 2021095 = 3031643) B3031643
theorem B2273737 : Blo 2019435 2273737 := bbase (se 2 (by rfl) ⟨852651, by rfl⟩ : syracuseStep 2273737 = 1705303) (by norm_num)
theorem B3031649 : Blo 2019435 3031649 := bstep (se 2 (by rfl) ⟨1136868, by rfl⟩ : syracuseStep 3031649 = 2273737) B2273737
theorem B2021099 : Blo 2019435 2021099 := bstep (se 1 (by rfl) ⟨1515824, by rfl⟩ : syracuseStep 2021099 = 3031649) B3031649
theorem B17266229 : Blo 2019435 17266229 := bbase (se 5 (by rfl) ⟨809354, by rfl⟩ : syracuseStep 17266229 = 1618709) (by norm_num)
theorem B11510819 : Blo 2019435 11510819 := bstep (se 1 (by rfl) ⟨8633114, by rfl⟩ : syracuseStep 11510819 = 17266229) B17266229
theorem B7673879 : Blo 2019435 7673879 := bstep (se 1 (by rfl) ⟨5755409, by rfl⟩ : syracuseStep 7673879 = 11510819) B11510819
theorem B5115919 : Blo 2019435 5115919 := bstep (se 1 (by rfl) ⟨3836939, by rfl⟩ : syracuseStep 5115919 = 7673879) B7673879
theorem B6821225 : Blo 2019435 6821225 := bstep (se 2 (by rfl) ⟨2557959, by rfl⟩ : syracuseStep 6821225 = 5115919) B5115919
theorem B4547483 : Blo 2019435 4547483 := bstep (se 1 (by rfl) ⟨3410612, by rfl⟩ : syracuseStep 4547483 = 6821225) B6821225
theorem B3031655 : Blo 2019435 3031655 := bstep (se 1 (by rfl) ⟨2273741, by rfl⟩ : syracuseStep 3031655 = 4547483) B4547483
theorem B2021103 : Blo 2019435 2021103 := bstep (se 1 (by rfl) ⟨1515827, by rfl⟩ : syracuseStep 2021103 = 3031655) B3031655
theorem B3031661 : Blo 2019435 3031661 := bbase (se 3 (by rfl) ⟨568436, by rfl⟩ : syracuseStep 3031661 = 1136873) (by norm_num)
theorem B2021107 : Blo 2019435 2021107 := bstep (se 1 (by rfl) ⟨1515830, by rfl⟩ : syracuseStep 2021107 = 3031661) B3031661
theorem B4547501 : Blo 2019435 4547501 := bbase (se 3 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 4547501 = 1705313) (by norm_num)
theorem B3031667 : Blo 2019435 3031667 := bstep (se 1 (by rfl) ⟨2273750, by rfl⟩ : syracuseStep 3031667 = 4547501) B4547501
theorem B2021111 : Blo 2019435 2021111 := bstep (se 1 (by rfl) ⟨1515833, by rfl⟩ : syracuseStep 2021111 = 3031667) B3031667
theorem B5755445 : Blo 2019435 5755445 := bbase (se 5 (by rfl) ⟨269786, by rfl⟩ : syracuseStep 5755445 = 539573) (by norm_num)
theorem B3836963 : Blo 2019435 3836963 := bstep (se 1 (by rfl) ⟨2877722, by rfl⟩ : syracuseStep 3836963 = 5755445) B5755445
theorem B2557975 : Blo 2019435 2557975 := bstep (se 1 (by rfl) ⟨1918481, by rfl⟩ : syracuseStep 2557975 = 3836963) B3836963
theorem B3410633 : Blo 2019435 3410633 := bstep (se 2 (by rfl) ⟨1278987, by rfl⟩ : syracuseStep 3410633 = 2557975) B2557975
theorem B2273755 : Blo 2019435 2273755 := bstep (se 1 (by rfl) ⟨1705316, by rfl⟩ : syracuseStep 2273755 = 3410633) B3410633
theorem B3031673 : Blo 2019435 3031673 := bstep (se 2 (by rfl) ⟨1136877, by rfl⟩ : syracuseStep 3031673 = 2273755) B2273755
theorem B2021115 : Blo 2019435 2021115 := bstep (se 1 (by rfl) ⟨1515836, by rfl⟩ : syracuseStep 2021115 = 3031673) B3031673
theorem B3504341 : Blo 2019435 3504341 := bbase (se 7 (by rfl) ⟨41066, by rfl⟩ : syracuseStep 3504341 = 82133) (by norm_num)
theorem B9344909 : Blo 2019435 9344909 := bstep (se 3 (by rfl) ⟨1752170, by rfl⟩ : syracuseStep 9344909 = 3504341) B3504341
theorem B24919757 : Blo 2019435 24919757 := bstep (se 3 (by rfl) ⟨4672454, by rfl⟩ : syracuseStep 24919757 = 9344909) B9344909
theorem B16613171 : Blo 2019435 16613171 := bstep (se 1 (by rfl) ⟨12459878, by rfl⟩ : syracuseStep 16613171 = 24919757) B24919757
theorem B11075447 : Blo 2019435 11075447 := bstep (se 1 (by rfl) ⟨8306585, by rfl⟩ : syracuseStep 11075447 = 16613171) B16613171
theorem B7383631 : Blo 2019435 7383631 := bstep (se 1 (by rfl) ⟨5537723, by rfl⟩ : syracuseStep 7383631 = 11075447) B11075447
theorem B9844841 : Blo 2019435 9844841 := bstep (se 2 (by rfl) ⟨3691815, by rfl⟩ : syracuseStep 9844841 = 7383631) B7383631
theorem B6563227 : Blo 2019435 6563227 := bstep (se 1 (by rfl) ⟨4922420, by rfl⟩ : syracuseStep 6563227 = 9844841) B9844841
theorem B8750969 : Blo 2019435 8750969 := bstep (se 2 (by rfl) ⟨3281613, by rfl⟩ : syracuseStep 8750969 = 6563227) B6563227
theorem B5833979 : Blo 2019435 5833979 := bstep (se 1 (by rfl) ⟨4375484, by rfl⟩ : syracuseStep 5833979 = 8750969) B8750969
theorem B3889319 : Blo 2019435 3889319 := bstep (se 1 (by rfl) ⟨2916989, by rfl⟩ : syracuseStep 3889319 = 5833979) B5833979
theorem B41486069 : Blo 2019435 41486069 := bstep (se 5 (by rfl) ⟨1944659, by rfl⟩ : syracuseStep 41486069 = 3889319) B3889319
theorem B27657379 : Blo 2019435 27657379 := bstep (se 1 (by rfl) ⟨20743034, by rfl⟩ : syracuseStep 27657379 = 41486069) B41486069
theorem B147506021 : Blo 2019435 147506021 := bstep (se 4 (by rfl) ⟨13828689, by rfl⟩ : syracuseStep 147506021 = 27657379) B27657379
theorem B98337347 : Blo 2019435 98337347 := bstep (se 1 (by rfl) ⟨73753010, by rfl⟩ : syracuseStep 98337347 = 147506021) B147506021
theorem B65558231 : Blo 2019435 65558231 := bstep (se 1 (by rfl) ⟨49168673, by rfl⟩ : syracuseStep 65558231 = 98337347) B98337347
theorem B43705487 : Blo 2019435 43705487 := bstep (se 1 (by rfl) ⟨32779115, by rfl⟩ : syracuseStep 43705487 = 65558231) B65558231
theorem B29136991 : Blo 2019435 29136991 := bstep (se 1 (by rfl) ⟨21852743, by rfl⟩ : syracuseStep 29136991 = 43705487) B43705487
theorem B38849321 : Blo 2019435 38849321 := bstep (se 2 (by rfl) ⟨14568495, by rfl⟩ : syracuseStep 38849321 = 29136991) B29136991
theorem B25899547 : Blo 2019435 25899547 := bstep (se 1 (by rfl) ⟨19424660, by rfl⟩ : syracuseStep 25899547 = 38849321) B38849321
theorem B34532729 : Blo 2019435 34532729 := bstep (se 2 (by rfl) ⟨12949773, by rfl⟩ : syracuseStep 34532729 = 25899547) B25899547
theorem B23021819 : Blo 2019435 23021819 := bstep (se 1 (by rfl) ⟨17266364, by rfl⟩ : syracuseStep 23021819 = 34532729) B34532729
theorem B15347879 : Blo 2019435 15347879 := bstep (se 1 (by rfl) ⟨11510909, by rfl⟩ : syracuseStep 15347879 = 23021819) B23021819
theorem B10231919 : Blo 2019435 10231919 := bstep (se 1 (by rfl) ⟨7673939, by rfl⟩ : syracuseStep 10231919 = 15347879) B15347879
theorem B6821279 : Blo 2019435 6821279 := bstep (se 1 (by rfl) ⟨5115959, by rfl⟩ : syracuseStep 6821279 = 10231919) B10231919
theorem B4547519 : Blo 2019435 4547519 := bstep (se 1 (by rfl) ⟨3410639, by rfl⟩ : syracuseStep 4547519 = 6821279) B6821279
theorem B3031679 : Blo 2019435 3031679 := bstep (se 1 (by rfl) ⟨2273759, by rfl⟩ : syracuseStep 3031679 = 4547519) B4547519
theorem B2021119 : Blo 2019435 2021119 := bstep (se 1 (by rfl) ⟨1515839, by rfl⟩ : syracuseStep 2021119 = 3031679) B3031679
theorem B3031685 : Blo 2019435 3031685 := bbase (se 4 (by rfl) ⟨284220, by rfl⟩ : syracuseStep 3031685 = 568441) (by norm_num)
theorem B2021123 : Blo 2019435 2021123 := bstep (se 1 (by rfl) ⟨1515842, by rfl⟩ : syracuseStep 2021123 = 3031685) B3031685
theorem B3410653 : Blo 2019435 3410653 := bbase (se 3 (by rfl) ⟨639497, by rfl⟩ : syracuseStep 3410653 = 1278995) (by norm_num)
theorem B4547537 : Blo 2019435 4547537 := bstep (se 2 (by rfl) ⟨1705326, by rfl⟩ : syracuseStep 4547537 = 3410653) B3410653
theorem B3031691 : Blo 2019435 3031691 := bstep (se 1 (by rfl) ⟨2273768, by rfl⟩ : syracuseStep 3031691 = 4547537) B4547537
theorem B2021127 : Blo 2019435 2021127 := bstep (se 1 (by rfl) ⟨1515845, by rfl⟩ : syracuseStep 2021127 = 3031691) B3031691
theorem B2273773 : Blo 2019435 2273773 := bbase (se 3 (by rfl) ⟨426332, by rfl⟩ : syracuseStep 2273773 = 852665) (by norm_num)
theorem B3031697 : Blo 2019435 3031697 := bstep (se 2 (by rfl) ⟨1136886, by rfl⟩ : syracuseStep 3031697 = 2273773) B2273773
theorem B2021131 : Blo 2019435 2021131 := bstep (se 1 (by rfl) ⟨1515848, by rfl⟩ : syracuseStep 2021131 = 3031697) B3031697
theorem B6821333 : Blo 2019435 6821333 := bbase (se 7 (by rfl) ⟨79937, by rfl⟩ : syracuseStep 6821333 = 159875) (by norm_num)
theorem B4547555 : Blo 2019435 4547555 := bstep (se 1 (by rfl) ⟨3410666, by rfl⟩ : syracuseStep 4547555 = 6821333) B6821333
theorem B3031703 : Blo 2019435 3031703 := bstep (se 1 (by rfl) ⟨2273777, by rfl⟩ : syracuseStep 3031703 = 4547555) B4547555
theorem B2021135 : Blo 2019435 2021135 := bstep (se 1 (by rfl) ⟨1515851, by rfl⟩ : syracuseStep 2021135 = 3031703) B3031703
theorem B3031709 : Blo 2019435 3031709 := bbase (se 3 (by rfl) ⟨568445, by rfl⟩ : syracuseStep 3031709 = 1136891) (by norm_num)
theorem B2021139 : Blo 2019435 2021139 := bstep (se 1 (by rfl) ⟨1515854, by rfl⟩ : syracuseStep 2021139 = 3031709) B3031709
theorem B4547573 : Blo 2019435 4547573 := bbase (se 5 (by rfl) ⟨213167, by rfl⟩ : syracuseStep 4547573 = 426335) (by norm_num)
theorem B3031715 : Blo 2019435 3031715 := bstep (se 1 (by rfl) ⟨2273786, by rfl⟩ : syracuseStep 3031715 = 4547573) B4547573
theorem B2021143 : Blo 2019435 2021143 := bstep (se 1 (by rfl) ⟨1515857, by rfl⟩ : syracuseStep 2021143 = 3031715) B3031715
theorem B2336261 : Blo 2019435 2336261 := bbase (se 4 (by rfl) ⟨219024, by rfl⟩ : syracuseStep 2336261 = 438049) (by norm_num)
theorem B6230029 : Blo 2019435 6230029 := bstep (se 3 (by rfl) ⟨1168130, by rfl⟩ : syracuseStep 6230029 = 2336261) B2336261
theorem B8306705 : Blo 2019435 8306705 := bstep (se 2 (by rfl) ⟨3115014, by rfl⟩ : syracuseStep 8306705 = 6230029) B6230029
theorem B5537803 : Blo 2019435 5537803 := bstep (se 1 (by rfl) ⟨4153352, by rfl⟩ : syracuseStep 5537803 = 8306705) B8306705
theorem B7383737 : Blo 2019435 7383737 := bstep (se 2 (by rfl) ⟨2768901, by rfl⟩ : syracuseStep 7383737 = 5537803) B5537803
theorem B4922491 : Blo 2019435 4922491 := bstep (se 1 (by rfl) ⟨3691868, by rfl⟩ : syracuseStep 4922491 = 7383737) B7383737
theorem B6563321 : Blo 2019435 6563321 := bstep (se 2 (by rfl) ⟨2461245, by rfl⟩ : syracuseStep 6563321 = 4922491) B4922491
theorem B4375547 : Blo 2019435 4375547 := bstep (se 1 (by rfl) ⟨3281660, by rfl⟩ : syracuseStep 4375547 = 6563321) B6563321
theorem B2917031 : Blo 2019435 2917031 := bstep (se 1 (by rfl) ⟨2187773, by rfl⟩ : syracuseStep 2917031 = 4375547) B4375547
theorem B7778749 : Blo 2019435 7778749 := bstep (se 3 (by rfl) ⟨1458515, by rfl⟩ : syracuseStep 7778749 = 2917031) B2917031
theorem B10371665 : Blo 2019435 10371665 := bstep (se 2 (by rfl) ⟨3889374, by rfl⟩ : syracuseStep 10371665 = 7778749) B7778749
theorem B6914443 : Blo 2019435 6914443 := bstep (se 1 (by rfl) ⟨5185832, by rfl⟩ : syracuseStep 6914443 = 10371665) B10371665
theorem B9219257 : Blo 2019435 9219257 := bstep (se 2 (by rfl) ⟨3457221, by rfl⟩ : syracuseStep 9219257 = 6914443) B6914443
theorem B6146171 : Blo 2019435 6146171 := bstep (se 1 (by rfl) ⟨4609628, by rfl⟩ : syracuseStep 6146171 = 9219257) B9219257
theorem B4097447 : Blo 2019435 4097447 := bstep (se 1 (by rfl) ⟨3073085, by rfl⟩ : syracuseStep 4097447 = 6146171) B6146171
theorem B43706101 : Blo 2019435 43706101 := bstep (se 5 (by rfl) ⟨2048723, by rfl⟩ : syracuseStep 43706101 = 4097447) B4097447
theorem B58274801 : Blo 2019435 58274801 := bstep (se 2 (by rfl) ⟨21853050, by rfl⟩ : syracuseStep 58274801 = 43706101) B43706101
theorem B38849867 : Blo 2019435 38849867 := bstep (se 1 (by rfl) ⟨29137400, by rfl⟩ : syracuseStep 38849867 = 58274801) B58274801
theorem B25899911 : Blo 2019435 25899911 := bstep (se 1 (by rfl) ⟨19424933, by rfl⟩ : syracuseStep 25899911 = 38849867) B38849867
theorem B17266607 : Blo 2019435 17266607 := bstep (se 1 (by rfl) ⟨12949955, by rfl⟩ : syracuseStep 17266607 = 25899911) B25899911
theorem B11511071 : Blo 2019435 11511071 := bstep (se 1 (by rfl) ⟨8633303, by rfl⟩ : syracuseStep 11511071 = 17266607) B17266607
theorem B7674047 : Blo 2019435 7674047 := bstep (se 1 (by rfl) ⟨5755535, by rfl⟩ : syracuseStep 7674047 = 11511071) B11511071
theorem B5116031 : Blo 2019435 5116031 := bstep (se 1 (by rfl) ⟨3837023, by rfl⟩ : syracuseStep 5116031 = 7674047) B7674047
theorem B3410687 : Blo 2019435 3410687 := bstep (se 1 (by rfl) ⟨2558015, by rfl⟩ : syracuseStep 3410687 = 5116031) B5116031
theorem B2273791 : Blo 2019435 2273791 := bstep (se 1 (by rfl) ⟨1705343, by rfl⟩ : syracuseStep 2273791 = 3410687) B3410687
theorem B3031721 : Blo 2019435 3031721 := bstep (se 2 (by rfl) ⟨1136895, by rfl⟩ : syracuseStep 3031721 = 2273791) B2273791
theorem B2021147 : Blo 2019435 2021147 := bstep (se 1 (by rfl) ⟨1515860, by rfl⟩ : syracuseStep 2021147 = 3031721) B3031721
theorem B2877773 : Blo 2019435 2877773 := bbase (se 3 (by rfl) ⟨539582, by rfl⟩ : syracuseStep 2877773 = 1079165) (by norm_num)
theorem B7674061 : Blo 2019435 7674061 := bstep (se 3 (by rfl) ⟨1438886, by rfl⟩ : syracuseStep 7674061 = 2877773) B2877773
theorem B10232081 : Blo 2019435 10232081 := bstep (se 2 (by rfl) ⟨3837030, by rfl⟩ : syracuseStep 10232081 = 7674061) B7674061
theorem B6821387 : Blo 2019435 6821387 := bstep (se 1 (by rfl) ⟨5116040, by rfl⟩ : syracuseStep 6821387 = 10232081) B10232081
theorem B4547591 : Blo 2019435 4547591 := bstep (se 1 (by rfl) ⟨3410693, by rfl⟩ : syracuseStep 4547591 = 6821387) B6821387
theorem B3031727 : Blo 2019435 3031727 := bstep (se 1 (by rfl) ⟨2273795, by rfl⟩ : syracuseStep 3031727 = 4547591) B4547591
theorem B2021151 : Blo 2019435 2021151 := bstep (se 1 (by rfl) ⟨1515863, by rfl⟩ : syracuseStep 2021151 = 3031727) B3031727
theorem B3031733 : Blo 2019435 3031733 := bbase (se 5 (by rfl) ⟨142112, by rfl⟩ : syracuseStep 3031733 = 284225) (by norm_num)
theorem B2021155 : Blo 2019435 2021155 := bstep (se 1 (by rfl) ⟨1515866, by rfl⟩ : syracuseStep 2021155 = 3031733) B3031733
theorem B5116061 : Blo 2019435 5116061 := bbase (se 3 (by rfl) ⟨959261, by rfl⟩ : syracuseStep 5116061 = 1918523) (by norm_num)
theorem B3410707 : Blo 2019435 3410707 := bstep (se 1 (by rfl) ⟨2558030, by rfl⟩ : syracuseStep 3410707 = 5116061) B5116061
theorem B4547609 : Blo 2019435 4547609 := bstep (se 2 (by rfl) ⟨1705353, by rfl⟩ : syracuseStep 4547609 = 3410707) B3410707
theorem B3031739 : Blo 2019435 3031739 := bstep (se 1 (by rfl) ⟨2273804, by rfl⟩ : syracuseStep 3031739 = 4547609) B4547609
theorem B2021159 : Blo 2019435 2021159 := bstep (se 1 (by rfl) ⟨1515869, by rfl⟩ : syracuseStep 2021159 = 3031739) B3031739
theorem B2273809 : Blo 2019435 2273809 := bbase (se 2 (by rfl) ⟨852678, by rfl⟩ : syracuseStep 2273809 = 1705357) (by norm_num)
theorem B3031745 : Blo 2019435 3031745 := bstep (se 2 (by rfl) ⟨1136904, by rfl⟩ : syracuseStep 3031745 = 2273809) B2273809
theorem B2021163 : Blo 2019435 2021163 := bstep (se 1 (by rfl) ⟨1515872, by rfl⟩ : syracuseStep 2021163 = 3031745) B3031745
theorem B3837061 : Blo 2019435 3837061 := bbase (se 4 (by rfl) ⟨359724, by rfl⟩ : syracuseStep 3837061 = 719449) (by norm_num)
theorem B5116081 : Blo 2019435 5116081 := bstep (se 2 (by rfl) ⟨1918530, by rfl⟩ : syracuseStep 5116081 = 3837061) B3837061
theorem B6821441 : Blo 2019435 6821441 := bstep (se 2 (by rfl) ⟨2558040, by rfl⟩ : syracuseStep 6821441 = 5116081) B5116081
theorem B4547627 : Blo 2019435 4547627 := bstep (se 1 (by rfl) ⟨3410720, by rfl⟩ : syracuseStep 4547627 = 6821441) B6821441
theorem B3031751 : Blo 2019435 3031751 := bstep (se 1 (by rfl) ⟨2273813, by rfl⟩ : syracuseStep 3031751 = 4547627) B4547627
theorem B2021167 : Blo 2019435 2021167 := bstep (se 1 (by rfl) ⟨1515875, by rfl⟩ : syracuseStep 2021167 = 3031751) B3031751
theorem B3031757 : Blo 2019435 3031757 := bbase (se 3 (by rfl) ⟨568454, by rfl⟩ : syracuseStep 3031757 = 1136909) (by norm_num)
theorem B2021171 : Blo 2019435 2021171 := bstep (se 1 (by rfl) ⟨1515878, by rfl⟩ : syracuseStep 2021171 = 3031757) B3031757
theorem B4547645 : Blo 2019435 4547645 := bbase (se 3 (by rfl) ⟨852683, by rfl⟩ : syracuseStep 4547645 = 1705367) (by norm_num)
theorem B3031763 : Blo 2019435 3031763 := bstep (se 1 (by rfl) ⟨2273822, by rfl⟩ : syracuseStep 3031763 = 4547645) B4547645
theorem B2021175 : Blo 2019435 2021175 := bstep (se 1 (by rfl) ⟨1515881, by rfl⟩ : syracuseStep 2021175 = 3031763) B3031763
theorem B3410741 : Blo 2019435 3410741 := bbase (se 5 (by rfl) ⟨159878, by rfl⟩ : syracuseStep 3410741 = 319757) (by norm_num)
theorem B2273827 : Blo 2019435 2273827 := bstep (se 1 (by rfl) ⟨1705370, by rfl⟩ : syracuseStep 2273827 = 3410741) B3410741
theorem B3031769 : Blo 2019435 3031769 := bstep (se 2 (by rfl) ⟨1136913, by rfl⟩ : syracuseStep 3031769 = 2273827) B2273827
theorem B2021179 : Blo 2019435 2021179 := bstep (se 1 (by rfl) ⟨1515884, by rfl⟩ : syracuseStep 2021179 = 3031769) B3031769
theorem B5755637 : Blo 2019435 5755637 := bbase (se 5 (by rfl) ⟨269795, by rfl⟩ : syracuseStep 5755637 = 539591) (by norm_num)
theorem B15348365 : Blo 2019435 15348365 := bstep (se 3 (by rfl) ⟨2877818, by rfl⟩ : syracuseStep 15348365 = 5755637) B5755637
theorem B10232243 : Blo 2019435 10232243 := bstep (se 1 (by rfl) ⟨7674182, by rfl⟩ : syracuseStep 10232243 = 15348365) B15348365
theorem B6821495 : Blo 2019435 6821495 := bstep (se 1 (by rfl) ⟨5116121, by rfl⟩ : syracuseStep 6821495 = 10232243) B10232243
theorem B4547663 : Blo 2019435 4547663 := bstep (se 1 (by rfl) ⟨3410747, by rfl⟩ : syracuseStep 4547663 = 6821495) B6821495
theorem B3031775 : Blo 2019435 3031775 := bstep (se 1 (by rfl) ⟨2273831, by rfl⟩ : syracuseStep 3031775 = 4547663) B4547663
theorem B2021183 : Blo 2019435 2021183 := bstep (se 1 (by rfl) ⟨1515887, by rfl⟩ : syracuseStep 2021183 = 3031775) B3031775
theorem B3031781 : Blo 2019435 3031781 := bbase (se 4 (by rfl) ⟨284229, by rfl⟩ : syracuseStep 3031781 = 568459) (by norm_num)
theorem B2021187 : Blo 2019435 2021187 := bstep (se 1 (by rfl) ⟨1515890, by rfl⟩ : syracuseStep 2021187 = 3031781) B3031781
theorem B2158373 : Blo 2019435 2158373 := bbase (se 4 (by rfl) ⟨202347, by rfl⟩ : syracuseStep 2158373 = 404695) (by norm_num)
theorem B5755661 : Blo 2019435 5755661 := bstep (se 3 (by rfl) ⟨1079186, by rfl⟩ : syracuseStep 5755661 = 2158373) B2158373
theorem B3837107 : Blo 2019435 3837107 := bstep (se 1 (by rfl) ⟨2877830, by rfl⟩ : syracuseStep 3837107 = 5755661) B5755661
theorem B2558071 : Blo 2019435 2558071 := bstep (se 1 (by rfl) ⟨1918553, by rfl⟩ : syracuseStep 2558071 = 3837107) B3837107
theorem B3410761 : Blo 2019435 3410761 := bstep (se 2 (by rfl) ⟨1279035, by rfl⟩ : syracuseStep 3410761 = 2558071) B2558071
theorem B4547681 : Blo 2019435 4547681 := bstep (se 2 (by rfl) ⟨1705380, by rfl⟩ : syracuseStep 4547681 = 3410761) B3410761
theorem B3031787 : Blo 2019435 3031787 := bstep (se 1 (by rfl) ⟨2273840, by rfl⟩ : syracuseStep 3031787 = 4547681) B4547681
theorem B2021191 : Blo 2019435 2021191 := bstep (se 1 (by rfl) ⟨1515893, by rfl⟩ : syracuseStep 2021191 = 3031787) B3031787
theorem B2273845 : Blo 2019435 2273845 := bbase (se 5 (by rfl) ⟨106586, by rfl⟩ : syracuseStep 2273845 = 213173) (by norm_num)
theorem B3031793 : Blo 2019435 3031793 := bstep (se 2 (by rfl) ⟨1136922, by rfl⟩ : syracuseStep 3031793 = 2273845) B2273845
theorem B2021195 : Blo 2019435 2021195 := bstep (se 1 (by rfl) ⟨1515896, by rfl⟩ : syracuseStep 2021195 = 3031793) B3031793
theorem B2558081 : Blo 2019435 2558081 := bbase (se 2 (by rfl) ⟨959280, by rfl⟩ : syracuseStep 2558081 = 1918561) (by norm_num)
theorem B6821549 : Blo 2019435 6821549 := bstep (se 3 (by rfl) ⟨1279040, by rfl⟩ : syracuseStep 6821549 = 2558081) B2558081
theorem B4547699 : Blo 2019435 4547699 := bstep (se 1 (by rfl) ⟨3410774, by rfl⟩ : syracuseStep 4547699 = 6821549) B6821549
theorem B3031799 : Blo 2019435 3031799 := bstep (se 1 (by rfl) ⟨2273849, by rfl⟩ : syracuseStep 3031799 = 4547699) B4547699
theorem B2021199 : Blo 2019435 2021199 := bstep (se 1 (by rfl) ⟨1515899, by rfl⟩ : syracuseStep 2021199 = 3031799) B3031799
theorem B3031805 : Blo 2019435 3031805 := bbase (se 3 (by rfl) ⟨568463, by rfl⟩ : syracuseStep 3031805 = 1136927) (by norm_num)
theorem B2021203 : Blo 2019435 2021203 := bstep (se 1 (by rfl) ⟨1515902, by rfl⟩ : syracuseStep 2021203 = 3031805) B3031805
theorem B4547717 : Blo 2019435 4547717 := bbase (se 4 (by rfl) ⟨426348, by rfl⟩ : syracuseStep 4547717 = 852697) (by norm_num)
theorem B3031811 : Blo 2019435 3031811 := bstep (se 1 (by rfl) ⟨2273858, by rfl⟩ : syracuseStep 3031811 = 4547717) B4547717
theorem B2021207 : Blo 2019435 2021207 := bstep (se 1 (by rfl) ⟨1515905, by rfl⟩ : syracuseStep 2021207 = 3031811) B3031811
theorem B4316789 : Blo 2019435 4316789 := bbase (se 5 (by rfl) ⟨202349, by rfl⟩ : syracuseStep 4316789 = 404699) (by norm_num)
theorem B2877859 : Blo 2019435 2877859 := bstep (se 1 (by rfl) ⟨2158394, by rfl⟩ : syracuseStep 2877859 = 4316789) B4316789
theorem B3837145 : Blo 2019435 3837145 := bstep (se 2 (by rfl) ⟨1438929, by rfl⟩ : syracuseStep 3837145 = 2877859) B2877859
theorem B5116193 : Blo 2019435 5116193 := bstep (se 2 (by rfl) ⟨1918572, by rfl⟩ : syracuseStep 5116193 = 3837145) B3837145
theorem B3410795 : Blo 2019435 3410795 := bstep (se 1 (by rfl) ⟨2558096, by rfl⟩ : syracuseStep 3410795 = 5116193) B5116193
theorem B2273863 : Blo 2019435 2273863 := bstep (se 1 (by rfl) ⟨1705397, by rfl⟩ : syracuseStep 2273863 = 3410795) B3410795
theorem B3031817 : Blo 2019435 3031817 := bstep (se 2 (by rfl) ⟨1136931, by rfl⟩ : syracuseStep 3031817 = 2273863) B2273863
theorem B2021211 : Blo 2019435 2021211 := bstep (se 1 (by rfl) ⟨1515908, by rfl⟩ : syracuseStep 2021211 = 3031817) B3031817
theorem B10232405 : Blo 2019435 10232405 := bbase (se 8 (by rfl) ⟨59955, by rfl⟩ : syracuseStep 10232405 = 119911) (by norm_num)
theorem B6821603 : Blo 2019435 6821603 := bstep (se 1 (by rfl) ⟨5116202, by rfl⟩ : syracuseStep 6821603 = 10232405) B10232405
theorem B4547735 : Blo 2019435 4547735 := bstep (se 1 (by rfl) ⟨3410801, by rfl⟩ : syracuseStep 4547735 = 6821603) B6821603
theorem B3031823 : Blo 2019435 3031823 := bstep (se 1 (by rfl) ⟨2273867, by rfl⟩ : syracuseStep 3031823 = 4547735) B4547735
theorem B2021215 : Blo 2019435 2021215 := bstep (se 1 (by rfl) ⟨1515911, by rfl⟩ : syracuseStep 2021215 = 3031823) B3031823
theorem B3031829 : Blo 2019435 3031829 := bbase (se 6 (by rfl) ⟨71058, by rfl⟩ : syracuseStep 3031829 = 142117) (by norm_num)
theorem B2021219 : Blo 2019435 2021219 := bstep (se 1 (by rfl) ⟨1515914, by rfl⟩ : syracuseStep 2021219 = 3031829) B3031829
theorem B3326557 : Blo 2019435 3326557 := bbase (se 3 (by rfl) ⟨623729, by rfl⟩ : syracuseStep 3326557 = 1247459) (by norm_num)
theorem B4435409 : Blo 2019435 4435409 := bstep (se 2 (by rfl) ⟨1663278, by rfl⟩ : syracuseStep 4435409 = 3326557) B3326557
theorem B189244117 : Blo 2019435 189244117 := bstep (se 7 (by rfl) ⟨2217704, by rfl⟩ : syracuseStep 189244117 = 4435409) B4435409
theorem B1009301957 : Blo 2019435 1009301957 := bstep (se 4 (by rfl) ⟨94622058, by rfl⟩ : syracuseStep 1009301957 = 189244117) B189244117
theorem B672867971 : Blo 2019435 672867971 := bstep (se 1 (by rfl) ⟨504650978, by rfl⟩ : syracuseStep 672867971 = 1009301957) B1009301957
theorem B448578647 : Blo 2019435 448578647 := bstep (se 1 (by rfl) ⟨336433985, by rfl⟩ : syracuseStep 448578647 = 672867971) B672867971
theorem B299052431 : Blo 2019435 299052431 := bstep (se 1 (by rfl) ⟨224289323, by rfl⟩ : syracuseStep 299052431 = 448578647) B448578647
theorem B199368287 : Blo 2019435 199368287 := bstep (se 1 (by rfl) ⟨149526215, by rfl⟩ : syracuseStep 199368287 = 299052431) B299052431
theorem B132912191 : Blo 2019435 132912191 := bstep (se 1 (by rfl) ⟨99684143, by rfl⟩ : syracuseStep 132912191 = 199368287) B199368287
theorem B88608127 : Blo 2019435 88608127 := bstep (se 1 (by rfl) ⟨66456095, by rfl⟩ : syracuseStep 88608127 = 132912191) B132912191
theorem B118144169 : Blo 2019435 118144169 := bstep (se 2 (by rfl) ⟨44304063, by rfl⟩ : syracuseStep 118144169 = 88608127) B88608127
theorem B78762779 : Blo 2019435 78762779 := bstep (se 1 (by rfl) ⟨59072084, by rfl⟩ : syracuseStep 78762779 = 118144169) B118144169
theorem B52508519 : Blo 2019435 52508519 := bstep (se 1 (by rfl) ⟨39381389, by rfl⟩ : syracuseStep 52508519 = 78762779) B78762779
theorem B35005679 : Blo 2019435 35005679 := bstep (se 1 (by rfl) ⟨26254259, by rfl⟩ : syracuseStep 35005679 = 52508519) B52508519
theorem B23337119 : Blo 2019435 23337119 := bstep (se 1 (by rfl) ⟨17502839, by rfl⟩ : syracuseStep 23337119 = 35005679) B35005679
theorem B15558079 : Blo 2019435 15558079 := bstep (se 1 (by rfl) ⟨11668559, by rfl⟩ : syracuseStep 15558079 = 23337119) B23337119
theorem B20744105 : Blo 2019435 20744105 := bstep (se 2 (by rfl) ⟨7779039, by rfl⟩ : syracuseStep 20744105 = 15558079) B15558079
theorem B55317613 : Blo 2019435 55317613 := bstep (se 3 (by rfl) ⟨10372052, by rfl⟩ : syracuseStep 55317613 = 20744105) B20744105
theorem B73756817 : Blo 2019435 73756817 := bstep (se 2 (by rfl) ⟨27658806, by rfl⟩ : syracuseStep 73756817 = 55317613) B55317613
theorem B49171211 : Blo 2019435 49171211 := bstep (se 1 (by rfl) ⟨36878408, by rfl⟩ : syracuseStep 49171211 = 73756817) B73756817
theorem B32780807 : Blo 2019435 32780807 := bstep (se 1 (by rfl) ⟨24585605, by rfl⟩ : syracuseStep 32780807 = 49171211) B49171211
theorem B21853871 : Blo 2019435 21853871 := bstep (se 1 (by rfl) ⟨16390403, by rfl⟩ : syracuseStep 21853871 = 32780807) B32780807
theorem B14569247 : Blo 2019435 14569247 := bstep (se 1 (by rfl) ⟨10926935, by rfl⟩ : syracuseStep 14569247 = 21853871) B21853871
theorem B38851325 : Blo 2019435 38851325 := bstep (se 3 (by rfl) ⟨7284623, by rfl⟩ : syracuseStep 38851325 = 14569247) B14569247
theorem B25900883 : Blo 2019435 25900883 := bstep (se 1 (by rfl) ⟨19425662, by rfl⟩ : syracuseStep 25900883 = 38851325) B38851325
theorem B17267255 : Blo 2019435 17267255 := bstep (se 1 (by rfl) ⟨12950441, by rfl⟩ : syracuseStep 17267255 = 25900883) B25900883
theorem B11511503 : Blo 2019435 11511503 := bstep (se 1 (by rfl) ⟨8633627, by rfl⟩ : syracuseStep 11511503 = 17267255) B17267255
theorem B7674335 : Blo 2019435 7674335 := bstep (se 1 (by rfl) ⟨5755751, by rfl⟩ : syracuseStep 7674335 = 11511503) B11511503
theorem B5116223 : Blo 2019435 5116223 := bstep (se 1 (by rfl) ⟨3837167, by rfl⟩ : syracuseStep 5116223 = 7674335) B7674335
theorem B3410815 : Blo 2019435 3410815 := bstep (se 1 (by rfl) ⟨2558111, by rfl⟩ : syracuseStep 3410815 = 5116223) B5116223
theorem B4547753 : Blo 2019435 4547753 := bstep (se 2 (by rfl) ⟨1705407, by rfl⟩ : syracuseStep 4547753 = 3410815) B3410815
theorem B3031835 : Blo 2019435 3031835 := bstep (se 1 (by rfl) ⟨2273876, by rfl⟩ : syracuseStep 3031835 = 4547753) B4547753
theorem B2021223 : Blo 2019435 2021223 := bstep (se 1 (by rfl) ⟨1515917, by rfl⟩ : syracuseStep 2021223 = 3031835) B3031835
theorem B2273881 : Blo 2019435 2273881 := bbase (se 2 (by rfl) ⟨852705, by rfl⟩ : syracuseStep 2273881 = 1705411) (by norm_num)
theorem B3031841 : Blo 2019435 3031841 := bstep (se 2 (by rfl) ⟨1136940, by rfl⟩ : syracuseStep 3031841 = 2273881) B2273881
theorem B2021227 : Blo 2019435 2021227 := bstep (se 1 (by rfl) ⟨1515920, by rfl⟩ : syracuseStep 2021227 = 3031841) B3031841
theorem B42054421 : Blo 2019435 42054421 := bbase (se 6 (by rfl) ⟨985650, by rfl⟩ : syracuseStep 42054421 = 1971301) (by norm_num)
theorem B897160981 : Blo 2019435 897160981 := bstep (se 6 (by rfl) ⟨21027210, by rfl⟩ : syracuseStep 897160981 = 42054421) B42054421
theorem B1196214641 : Blo 2019435 1196214641 := bstep (se 2 (by rfl) ⟨448580490, by rfl⟩ : syracuseStep 1196214641 = 897160981) B897160981
theorem B797476427 : Blo 2019435 797476427 := bstep (se 1 (by rfl) ⟨598107320, by rfl⟩ : syracuseStep 797476427 = 1196214641) B1196214641
theorem B531650951 : Blo 2019435 531650951 := bstep (se 1 (by rfl) ⟨398738213, by rfl⟩ : syracuseStep 531650951 = 797476427) B797476427
theorem B354433967 : Blo 2019435 354433967 := bstep (se 1 (by rfl) ⟨265825475, by rfl⟩ : syracuseStep 354433967 = 531650951) B531650951
theorem B236289311 : Blo 2019435 236289311 := bstep (se 1 (by rfl) ⟨177216983, by rfl⟩ : syracuseStep 236289311 = 354433967) B354433967
theorem B157526207 : Blo 2019435 157526207 := bstep (se 1 (by rfl) ⟨118144655, by rfl⟩ : syracuseStep 157526207 = 236289311) B236289311
theorem B105017471 : Blo 2019435 105017471 := bstep (se 1 (by rfl) ⟨78763103, by rfl⟩ : syracuseStep 105017471 = 157526207) B157526207
theorem B70011647 : Blo 2019435 70011647 := bstep (se 1 (by rfl) ⟨52508735, by rfl⟩ : syracuseStep 70011647 = 105017471) B105017471
theorem B46674431 : Blo 2019435 46674431 := bstep (se 1 (by rfl) ⟨35005823, by rfl⟩ : syracuseStep 46674431 = 70011647) B70011647
theorem B31116287 : Blo 2019435 31116287 := bstep (se 1 (by rfl) ⟨23337215, by rfl⟩ : syracuseStep 31116287 = 46674431) B46674431
theorem B20744191 : Blo 2019435 20744191 := bstep (se 1 (by rfl) ⟨15558143, by rfl⟩ : syracuseStep 20744191 = 31116287) B31116287
theorem B27658921 : Blo 2019435 27658921 := bstep (se 2 (by rfl) ⟨10372095, by rfl⟩ : syracuseStep 27658921 = 20744191) B20744191
theorem B36878561 : Blo 2019435 36878561 := bstep (se 2 (by rfl) ⟨13829460, by rfl⟩ : syracuseStep 36878561 = 27658921) B27658921
theorem B24585707 : Blo 2019435 24585707 := bstep (se 1 (by rfl) ⟨18439280, by rfl⟩ : syracuseStep 24585707 = 36878561) B36878561
theorem B16390471 : Blo 2019435 16390471 := bstep (se 1 (by rfl) ⟨12292853, by rfl⟩ : syracuseStep 16390471 = 24585707) B24585707
theorem B21853961 : Blo 2019435 21853961 := bstep (se 2 (by rfl) ⟨8195235, by rfl⟩ : syracuseStep 21853961 = 16390471) B16390471
theorem B14569307 : Blo 2019435 14569307 := bstep (se 1 (by rfl) ⟨10926980, by rfl⟩ : syracuseStep 14569307 = 21853961) B21853961
theorem B9712871 : Blo 2019435 9712871 := bstep (se 1 (by rfl) ⟨7284653, by rfl⟩ : syracuseStep 9712871 = 14569307) B14569307
theorem B6475247 : Blo 2019435 6475247 := bstep (se 1 (by rfl) ⟨4856435, by rfl⟩ : syracuseStep 6475247 = 9712871) B9712871
theorem B4316831 : Blo 2019435 4316831 := bstep (se 1 (by rfl) ⟨3237623, by rfl⟩ : syracuseStep 4316831 = 6475247) B6475247
theorem B2877887 : Blo 2019435 2877887 := bstep (se 1 (by rfl) ⟨2158415, by rfl⟩ : syracuseStep 2877887 = 4316831) B4316831
theorem B7674365 : Blo 2019435 7674365 := bstep (se 3 (by rfl) ⟨1438943, by rfl⟩ : syracuseStep 7674365 = 2877887) B2877887
theorem B5116243 : Blo 2019435 5116243 := bstep (se 1 (by rfl) ⟨3837182, by rfl⟩ : syracuseStep 5116243 = 7674365) B7674365
theorem B6821657 : Blo 2019435 6821657 := bstep (se 2 (by rfl) ⟨2558121, by rfl⟩ : syracuseStep 6821657 = 5116243) B5116243
theorem B4547771 : Blo 2019435 4547771 := bstep (se 1 (by rfl) ⟨3410828, by rfl⟩ : syracuseStep 4547771 = 6821657) B6821657
theorem B3031847 : Blo 2019435 3031847 := bstep (se 1 (by rfl) ⟨2273885, by rfl⟩ : syracuseStep 3031847 = 4547771) B4547771
theorem B2021231 : Blo 2019435 2021231 := bstep (se 1 (by rfl) ⟨1515923, by rfl⟩ : syracuseStep 2021231 = 3031847) B3031847
theorem B3031853 : Blo 2019435 3031853 := bbase (se 3 (by rfl) ⟨568472, by rfl⟩ : syracuseStep 3031853 = 1136945) (by norm_num)
theorem B2021235 : Blo 2019435 2021235 := bstep (se 1 (by rfl) ⟨1515926, by rfl⟩ : syracuseStep 2021235 = 3031853) B3031853
theorem B4547789 : Blo 2019435 4547789 := bbase (se 3 (by rfl) ⟨852710, by rfl⟩ : syracuseStep 4547789 = 1705421) (by norm_num)
theorem B3031859 : Blo 2019435 3031859 := bstep (se 1 (by rfl) ⟨2273894, by rfl⟩ : syracuseStep 3031859 = 4547789) B4547789
theorem B2021239 : Blo 2019435 2021239 := bstep (se 1 (by rfl) ⟨1515929, by rfl⟩ : syracuseStep 2021239 = 3031859) B3031859
theorem B2558137 : Blo 2019435 2558137 := bbase (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) (by norm_num)
theorem B3410849 : Blo 2019435 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B2273899 : Blo 2019435 2273899 := bstep (se 1 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 2273899 = 3410849) B3410849
theorem B3031865 : Blo 2019435 3031865 := bstep (se 2 (by rfl) ⟨1136949, by rfl⟩ : syracuseStep 3031865 = 2273899) B2273899
theorem B2021243 : Blo 2019435 2021243 := bstep (se 1 (by rfl) ⟨1515932, by rfl⟩ : syracuseStep 2021243 = 3031865) B3031865
theorem B2048825 : Blo 2019435 2048825 := bbase (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) (by norm_num)
theorem B5463533 : Blo 2019435 5463533 := bstep (se 3 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 5463533 = 2048825) B2048825
theorem B3642355 : Blo 2019435 3642355 := bstep (se 1 (by rfl) ⟨2731766, by rfl⟩ : syracuseStep 3642355 = 5463533) B5463533
theorem B4856473 : Blo 2019435 4856473 := bstep (se 2 (by rfl) ⟨1821177, by rfl⟩ : syracuseStep 4856473 = 3642355) B3642355
theorem B6475297 : Blo 2019435 6475297 := bstep (se 2 (by rfl) ⟨2428236, by rfl⟩ : syracuseStep 6475297 = 4856473) B4856473
theorem B8633729 : Blo 2019435 8633729 := bstep (se 2 (by rfl) ⟨3237648, by rfl⟩ : syracuseStep 8633729 = 6475297) B6475297
theorem B23023277 : Blo 2019435 23023277 := bstep (se 3 (by rfl) ⟨4316864, by rfl⟩ : syracuseStep 23023277 = 8633729) B8633729
theorem B15348851 : Blo 2019435 15348851 := bstep (se 1 (by rfl) ⟨11511638, by rfl⟩ : syracuseStep 15348851 = 23023277) B23023277
theorem B10232567 : Blo 2019435 10232567 := bstep (se 1 (by rfl) ⟨7674425, by rfl⟩ : syracuseStep 10232567 = 15348851) B15348851
theorem B6821711 : Blo 2019435 6821711 := bstep (se 1 (by rfl) ⟨5116283, by rfl⟩ : syracuseStep 6821711 = 10232567) B10232567
theorem B4547807 : Blo 2019435 4547807 := bstep (se 1 (by rfl) ⟨3410855, by rfl⟩ : syracuseStep 4547807 = 6821711) B6821711
theorem B3031871 : Blo 2019435 3031871 := bstep (se 1 (by rfl) ⟨2273903, by rfl⟩ : syracuseStep 3031871 = 4547807) B4547807
theorem B2021247 : Blo 2019435 2021247 := bstep (se 1 (by rfl) ⟨1515935, by rfl⟩ : syracuseStep 2021247 = 3031871) B3031871
theorem B3031877 : Blo 2019435 3031877 := bbase (se 4 (by rfl) ⟨284238, by rfl⟩ : syracuseStep 3031877 = 568477) (by norm_num)
theorem B2021251 : Blo 2019435 2021251 := bstep (se 1 (by rfl) ⟨1515938, by rfl⟩ : syracuseStep 2021251 = 3031877) B3031877
theorem B3410869 : Blo 2019435 3410869 := bbase (se 5 (by rfl) ⟨159884, by rfl⟩ : syracuseStep 3410869 = 319769) (by norm_num)
theorem B4547825 : Blo 2019435 4547825 := bstep (se 2 (by rfl) ⟨1705434, by rfl⟩ : syracuseStep 4547825 = 3410869) B3410869
theorem B3031883 : Blo 2019435 3031883 := bstep (se 1 (by rfl) ⟨2273912, by rfl⟩ : syracuseStep 3031883 = 4547825) B4547825
theorem B2021255 : Blo 2019435 2021255 := bstep (se 1 (by rfl) ⟨1515941, by rfl⟩ : syracuseStep 2021255 = 3031883) B3031883
theorem B2273917 : Blo 2019435 2273917 := bbase (se 3 (by rfl) ⟨426359, by rfl⟩ : syracuseStep 2273917 = 852719) (by norm_num)
theorem B3031889 : Blo 2019435 3031889 := bstep (se 2 (by rfl) ⟨1136958, by rfl⟩ : syracuseStep 3031889 = 2273917) B2273917
theorem B2021259 : Blo 2019435 2021259 := bstep (se 1 (by rfl) ⟨1515944, by rfl⟩ : syracuseStep 2021259 = 3031889) B3031889
theorem B6821765 : Blo 2019435 6821765 := bbase (se 4 (by rfl) ⟨639540, by rfl⟩ : syracuseStep 6821765 = 1279081) (by norm_num)
theorem B4547843 : Blo 2019435 4547843 := bstep (se 1 (by rfl) ⟨3410882, by rfl⟩ : syracuseStep 4547843 = 6821765) B6821765
theorem B3031895 : Blo 2019435 3031895 := bstep (se 1 (by rfl) ⟨2273921, by rfl⟩ : syracuseStep 3031895 = 4547843) B4547843
theorem B2021263 : Blo 2019435 2021263 := bstep (se 1 (by rfl) ⟨1515947, by rfl⟩ : syracuseStep 2021263 = 3031895) B3031895
theorem B3031901 : Blo 2019435 3031901 := bbase (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) (by norm_num)
theorem B2021267 : Blo 2019435 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B4547861 : Blo 2019435 4547861 := bbase (se 6 (by rfl) ⟨106590, by rfl⟩ : syracuseStep 4547861 = 213181) (by norm_num)
theorem B3031907 : Blo 2019435 3031907 := bstep (se 1 (by rfl) ⟨2273930, by rfl⟩ : syracuseStep 3031907 = 4547861) B4547861
theorem B2021271 : Blo 2019435 2021271 := bstep (se 1 (by rfl) ⟨1515953, by rfl⟩ : syracuseStep 2021271 = 3031907) B3031907
theorem B7674533 : Blo 2019435 7674533 := bbase (se 4 (by rfl) ⟨719487, by rfl⟩ : syracuseStep 7674533 = 1438975) (by norm_num)
theorem B5116355 : Blo 2019435 5116355 := bstep (se 1 (by rfl) ⟨3837266, by rfl⟩ : syracuseStep 5116355 = 7674533) B7674533
theorem B3410903 : Blo 2019435 3410903 := bstep (se 1 (by rfl) ⟨2558177, by rfl⟩ : syracuseStep 3410903 = 5116355) B5116355
theorem B2273935 : Blo 2019435 2273935 := bstep (se 1 (by rfl) ⟨1705451, by rfl⟩ : syracuseStep 2273935 = 3410903) B3410903
theorem B3031913 : Blo 2019435 3031913 := bstep (se 2 (by rfl) ⟨1136967, by rfl⟩ : syracuseStep 3031913 = 2273935) B2273935
theorem B2021275 : Blo 2019435 2021275 := bstep (se 1 (by rfl) ⟨1515956, by rfl⟩ : syracuseStep 2021275 = 3031913) B3031913
theorem B4316933 : Blo 2019435 4316933 := bbase (se 4 (by rfl) ⟨404712, by rfl⟩ : syracuseStep 4316933 = 809425) (by norm_num)
theorem B11511821 : Blo 2019435 11511821 := bstep (se 3 (by rfl) ⟨2158466, by rfl⟩ : syracuseStep 11511821 = 4316933) B4316933
theorem B7674547 : Blo 2019435 7674547 := bstep (se 1 (by rfl) ⟨5755910, by rfl⟩ : syracuseStep 7674547 = 11511821) B11511821
theorem B10232729 : Blo 2019435 10232729 := bstep (se 2 (by rfl) ⟨3837273, by rfl⟩ : syracuseStep 10232729 = 7674547) B7674547
theorem B6821819 : Blo 2019435 6821819 := bstep (se 1 (by rfl) ⟨5116364, by rfl⟩ : syracuseStep 6821819 = 10232729) B10232729
theorem B4547879 : Blo 2019435 4547879 := bstep (se 1 (by rfl) ⟨3410909, by rfl⟩ : syracuseStep 4547879 = 6821819) B6821819
theorem B3031919 : Blo 2019435 3031919 := bstep (se 1 (by rfl) ⟨2273939, by rfl⟩ : syracuseStep 3031919 = 4547879) B4547879
theorem B2021279 : Blo 2019435 2021279 := bstep (se 1 (by rfl) ⟨1515959, by rfl⟩ : syracuseStep 2021279 = 3031919) B3031919
theorem B3031925 : Blo 2019435 3031925 := bbase (se 5 (by rfl) ⟨142121, by rfl⟩ : syracuseStep 3031925 = 284243) (by norm_num)
theorem B2021283 : Blo 2019435 2021283 := bstep (se 1 (by rfl) ⟨1515962, by rfl⟩ : syracuseStep 2021283 = 3031925) B3031925
theorem B9713141 : Blo 2019435 9713141 := bbase (se 5 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 9713141 = 910607) (by norm_num)
theorem B6475427 : Blo 2019435 6475427 := bstep (se 1 (by rfl) ⟨4856570, by rfl⟩ : syracuseStep 6475427 = 9713141) B9713141
theorem B4316951 : Blo 2019435 4316951 := bstep (se 1 (by rfl) ⟨3237713, by rfl⟩ : syracuseStep 4316951 = 6475427) B6475427
theorem B2877967 : Blo 2019435 2877967 := bstep (se 1 (by rfl) ⟨2158475, by rfl⟩ : syracuseStep 2877967 = 4316951) B4316951
theorem B3837289 : Blo 2019435 3837289 := bstep (se 2 (by rfl) ⟨1438983, by rfl⟩ : syracuseStep 3837289 = 2877967) B2877967
theorem B5116385 : Blo 2019435 5116385 := bstep (se 2 (by rfl) ⟨1918644, by rfl⟩ : syracuseStep 5116385 = 3837289) B3837289
theorem B3410923 : Blo 2019435 3410923 := bstep (se 1 (by rfl) ⟨2558192, by rfl⟩ : syracuseStep 3410923 = 5116385) B5116385
theorem B4547897 : Blo 2019435 4547897 := bstep (se 2 (by rfl) ⟨1705461, by rfl⟩ : syracuseStep 4547897 = 3410923) B3410923
theorem B3031931 : Blo 2019435 3031931 := bstep (se 1 (by rfl) ⟨2273948, by rfl⟩ : syracuseStep 3031931 = 4547897) B4547897
theorem B2021287 : Blo 2019435 2021287 := bstep (se 1 (by rfl) ⟨1515965, by rfl⟩ : syracuseStep 2021287 = 3031931) B3031931
theorem B2273953 : Blo 2019435 2273953 := bbase (se 2 (by rfl) ⟨852732, by rfl⟩ : syracuseStep 2273953 = 1705465) (by norm_num)
theorem B3031937 : Blo 2019435 3031937 := bstep (se 2 (by rfl) ⟨1136976, by rfl⟩ : syracuseStep 3031937 = 2273953) B2273953
theorem B2021291 : Blo 2019435 2021291 := bstep (se 1 (by rfl) ⟨1515968, by rfl⟩ : syracuseStep 2021291 = 3031937) B3031937
theorem B5116405 : Blo 2019435 5116405 := bbase (se 5 (by rfl) ⟨239831, by rfl⟩ : syracuseStep 5116405 = 479663) (by norm_num)
theorem B6821873 : Blo 2019435 6821873 := bstep (se 2 (by rfl) ⟨2558202, by rfl⟩ : syracuseStep 6821873 = 5116405) B5116405
theorem B4547915 : Blo 2019435 4547915 := bstep (se 1 (by rfl) ⟨3410936, by rfl⟩ : syracuseStep 4547915 = 6821873) B6821873
theorem B3031943 : Blo 2019435 3031943 := bstep (se 1 (by rfl) ⟨2273957, by rfl⟩ : syracuseStep 3031943 = 4547915) B4547915
theorem B2021295 : Blo 2019435 2021295 := bstep (se 1 (by rfl) ⟨1515971, by rfl⟩ : syracuseStep 2021295 = 3031943) B3031943
theorem B3031949 : Blo 2019435 3031949 := bbase (se 3 (by rfl) ⟨568490, by rfl⟩ : syracuseStep 3031949 = 1136981) (by norm_num)
theorem B2021299 : Blo 2019435 2021299 := bstep (se 1 (by rfl) ⟨1515974, by rfl⟩ : syracuseStep 2021299 = 3031949) B3031949
theorem B4547933 : Blo 2019435 4547933 := bbase (se 3 (by rfl) ⟨852737, by rfl⟩ : syracuseStep 4547933 = 1705475) (by norm_num)
theorem B3031955 : Blo 2019435 3031955 := bstep (se 1 (by rfl) ⟨2273966, by rfl⟩ : syracuseStep 3031955 = 4547933) B4547933
theorem B2021303 : Blo 2019435 2021303 := bstep (se 1 (by rfl) ⟨1515977, by rfl⟩ : syracuseStep 2021303 = 3031955) B3031955
theorem B3410957 : Blo 2019435 3410957 := bbase (se 3 (by rfl) ⟨639554, by rfl⟩ : syracuseStep 3410957 = 1279109) (by norm_num)
theorem B2273971 : Blo 2019435 2273971 := bstep (se 1 (by rfl) ⟨1705478, by rfl⟩ : syracuseStep 2273971 = 3410957) B3410957
theorem B3031961 : Blo 2019435 3031961 := bstep (se 2 (by rfl) ⟨1136985, by rfl⟩ : syracuseStep 3031961 = 2273971) B2273971
theorem B2021307 : Blo 2019435 2021307 := bstep (se 1 (by rfl) ⟨1515980, by rfl⟩ : syracuseStep 2021307 = 3031961) B3031961
theorem B2731853 : Blo 2019435 2731853 := bbase (se 3 (by rfl) ⟨512222, by rfl⟩ : syracuseStep 2731853 = 1024445) (by norm_num)
theorem B7284941 : Blo 2019435 7284941 := bstep (se 3 (by rfl) ⟨1365926, by rfl⟩ : syracuseStep 7284941 = 2731853) B2731853
theorem B4856627 : Blo 2019435 4856627 := bstep (se 1 (by rfl) ⟨3642470, by rfl⟩ : syracuseStep 4856627 = 7284941) B7284941
theorem B3237751 : Blo 2019435 3237751 := bstep (se 1 (by rfl) ⟨2428313, by rfl⟩ : syracuseStep 3237751 = 4856627) B4856627
theorem B17268005 : Blo 2019435 17268005 := bstep (se 4 (by rfl) ⟨1618875, by rfl⟩ : syracuseStep 17268005 = 3237751) B3237751
theorem B11512003 : Blo 2019435 11512003 := bstep (se 1 (by rfl) ⟨8634002, by rfl⟩ : syracuseStep 11512003 = 17268005) B17268005
theorem B15349337 : Blo 2019435 15349337 := bstep (se 2 (by rfl) ⟨5756001, by rfl⟩ : syracuseStep 15349337 = 11512003) B11512003
theorem B10232891 : Blo 2019435 10232891 := bstep (se 1 (by rfl) ⟨7674668, by rfl⟩ : syracuseStep 10232891 = 15349337) B15349337
theorem B6821927 : Blo 2019435 6821927 := bstep (se 1 (by rfl) ⟨5116445, by rfl⟩ : syracuseStep 6821927 = 10232891) B10232891
theorem B4547951 : Blo 2019435 4547951 := bstep (se 1 (by rfl) ⟨3410963, by rfl⟩ : syracuseStep 4547951 = 6821927) B6821927
theorem B3031967 : Blo 2019435 3031967 := bstep (se 1 (by rfl) ⟨2273975, by rfl⟩ : syracuseStep 3031967 = 4547951) B4547951
theorem B2021311 : Blo 2019435 2021311 := bstep (se 1 (by rfl) ⟨1515983, by rfl⟩ : syracuseStep 2021311 = 3031967) B3031967
theorem B3031973 : Blo 2019435 3031973 := bbase (se 4 (by rfl) ⟨284247, by rfl⟩ : syracuseStep 3031973 = 568495) (by norm_num)
theorem B2021315 : Blo 2019435 2021315 := bstep (se 1 (by rfl) ⟨1515986, by rfl⟩ : syracuseStep 2021315 = 3031973) B3031973
theorem B2558233 : Blo 2019435 2558233 := bbase (se 2 (by rfl) ⟨959337, by rfl⟩ : syracuseStep 2558233 = 1918675) (by norm_num)
theorem B3410977 : Blo 2019435 3410977 := bstep (se 2 (by rfl) ⟨1279116, by rfl⟩ : syracuseStep 3410977 = 2558233) B2558233
theorem B4547969 : Blo 2019435 4547969 := bstep (se 2 (by rfl) ⟨1705488, by rfl⟩ : syracuseStep 4547969 = 3410977) B3410977
theorem B3031979 : Blo 2019435 3031979 := bstep (se 1 (by rfl) ⟨2273984, by rfl⟩ : syracuseStep 3031979 = 4547969) B4547969
theorem B2021319 : Blo 2019435 2021319 := bstep (se 1 (by rfl) ⟨1515989, by rfl⟩ : syracuseStep 2021319 = 3031979) B3031979
theorem B2273989 : Blo 2019435 2273989 := bbase (se 4 (by rfl) ⟨213186, by rfl⟩ : syracuseStep 2273989 = 426373) (by norm_num)
theorem B3031985 : Blo 2019435 3031985 := bstep (se 2 (by rfl) ⟨1136994, by rfl⟩ : syracuseStep 3031985 = 2273989) B2273989
theorem B2021323 : Blo 2019435 2021323 := bstep (se 1 (by rfl) ⟨1515992, by rfl⟩ : syracuseStep 2021323 = 3031985) B3031985
theorem B3837365 : Blo 2019435 3837365 := bbase (se 5 (by rfl) ⟨179876, by rfl⟩ : syracuseStep 3837365 = 359753) (by norm_num)
theorem B2558243 : Blo 2019435 2558243 := bstep (se 1 (by rfl) ⟨1918682, by rfl⟩ : syracuseStep 2558243 = 3837365) B3837365
theorem B6821981 : Blo 2019435 6821981 := bstep (se 3 (by rfl) ⟨1279121, by rfl⟩ : syracuseStep 6821981 = 2558243) B2558243
theorem B4547987 : Blo 2019435 4547987 := bstep (se 1 (by rfl) ⟨3410990, by rfl⟩ : syracuseStep 4547987 = 6821981) B6821981
theorem B3031991 : Blo 2019435 3031991 := bstep (se 1 (by rfl) ⟨2273993, by rfl⟩ : syracuseStep 3031991 = 4547987) B4547987
theorem B2021327 : Blo 2019435 2021327 := bstep (se 1 (by rfl) ⟨1515995, by rfl⟩ : syracuseStep 2021327 = 3031991) B3031991
theorem B3031997 : Blo 2019435 3031997 := bbase (se 3 (by rfl) ⟨568499, by rfl⟩ : syracuseStep 3031997 = 1136999) (by norm_num)
theorem B2021331 : Blo 2019435 2021331 := bstep (se 1 (by rfl) ⟨1515998, by rfl⟩ : syracuseStep 2021331 = 3031997) B3031997
theorem B4548005 : Blo 2019435 4548005 := bbase (se 4 (by rfl) ⟨426375, by rfl⟩ : syracuseStep 4548005 = 852751) (by norm_num)
theorem B3032003 : Blo 2019435 3032003 := bstep (se 1 (by rfl) ⟨2274002, by rfl⟩ : syracuseStep 3032003 = 4548005) B4548005
theorem B2021335 : Blo 2019435 2021335 := bstep (se 1 (by rfl) ⟨1516001, by rfl⟩ : syracuseStep 2021335 = 3032003) B3032003
theorem B5116517 : Blo 2019435 5116517 := bbase (se 4 (by rfl) ⟨479673, by rfl⟩ : syracuseStep 5116517 = 959347) (by norm_num)
theorem B3411011 : Blo 2019435 3411011 := bstep (se 1 (by rfl) ⟨2558258, by rfl⟩ : syracuseStep 3411011 = 5116517) B5116517
theorem B2274007 : Blo 2019435 2274007 := bstep (se 1 (by rfl) ⟨1705505, by rfl⟩ : syracuseStep 2274007 = 3411011) B3411011
theorem B3032009 : Blo 2019435 3032009 := bstep (se 2 (by rfl) ⟨1137003, by rfl⟩ : syracuseStep 3032009 = 2274007) B2274007
theorem B2021339 : Blo 2019435 2021339 := bstep (se 1 (by rfl) ⟨1516004, by rfl⟩ : syracuseStep 2021339 = 3032009) B3032009
theorem B7779509 : Blo 2019435 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B5186339 : Blo 2019435 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B3457559 : Blo 2019435 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B2305039 : Blo 2019435 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B3073385 : Blo 2019435 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B2048923 : Blo 2019435 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B2731897 : Blo 2019435 2731897 := bstep (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) B2048923
theorem B3642529 : Blo 2019435 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B4856705 : Blo 2019435 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B3237803 : Blo 2019435 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B2158535 : Blo 2019435 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B5756093 : Blo 2019435 5756093 := bstep (se 3 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 5756093 = 2158535) B2158535
theorem B3837395 : Blo 2019435 3837395 := bstep (se 1 (by rfl) ⟨2878046, by rfl⟩ : syracuseStep 3837395 = 5756093) B5756093
theorem B10233053 : Blo 2019435 10233053 := bstep (se 3 (by rfl) ⟨1918697, by rfl⟩ : syracuseStep 10233053 = 3837395) B3837395
theorem B6822035 : Blo 2019435 6822035 := bstep (se 1 (by rfl) ⟨5116526, by rfl⟩ : syracuseStep 6822035 = 10233053) B10233053
theorem B4548023 : Blo 2019435 4548023 := bstep (se 1 (by rfl) ⟨3411017, by rfl⟩ : syracuseStep 4548023 = 6822035) B6822035
theorem B3032015 : Blo 2019435 3032015 := bstep (se 1 (by rfl) ⟨2274011, by rfl⟩ : syracuseStep 3032015 = 4548023) B4548023
theorem B2021343 : Blo 2019435 2021343 := bstep (se 1 (by rfl) ⟨1516007, by rfl⟩ : syracuseStep 2021343 = 3032015) B3032015
theorem B3032021 : Blo 2019435 3032021 := bbase (se 7 (by rfl) ⟨35531, by rfl⟩ : syracuseStep 3032021 = 71063) (by norm_num)
theorem B2021347 : Blo 2019435 2021347 := bstep (se 1 (by rfl) ⟨1516010, by rfl⟩ : syracuseStep 2021347 = 3032021) B3032021
theorem B7674821 : Blo 2019435 7674821 := bbase (se 4 (by rfl) ⟨719514, by rfl⟩ : syracuseStep 7674821 = 1439029) (by norm_num)
theorem B5116547 : Blo 2019435 5116547 := bstep (se 1 (by rfl) ⟨3837410, by rfl⟩ : syracuseStep 5116547 = 7674821) B7674821
theorem B3411031 : Blo 2019435 3411031 := bstep (se 1 (by rfl) ⟨2558273, by rfl⟩ : syracuseStep 3411031 = 5116547) B5116547
theorem B4548041 : Blo 2019435 4548041 := bstep (se 2 (by rfl) ⟨1705515, by rfl⟩ : syracuseStep 4548041 = 3411031) B3411031
theorem B3032027 : Blo 2019435 3032027 := bstep (se 1 (by rfl) ⟨2274020, by rfl⟩ : syracuseStep 3032027 = 4548041) B4548041
theorem B2021351 : Blo 2019435 2021351 := bstep (se 1 (by rfl) ⟨1516013, by rfl⟩ : syracuseStep 2021351 = 3032027) B3032027
theorem B2274025 : Blo 2019435 2274025 := bbase (se 2 (by rfl) ⟨852759, by rfl⟩ : syracuseStep 2274025 = 1705519) (by norm_num)
theorem B3032033 : Blo 2019435 3032033 := bstep (se 2 (by rfl) ⟨1137012, by rfl⟩ : syracuseStep 3032033 = 2274025) B2274025
theorem B2021355 : Blo 2019435 2021355 := bstep (se 1 (by rfl) ⟨1516016, by rfl⟩ : syracuseStep 2021355 = 3032033) B3032033
theorem B11512277 : Blo 2019435 11512277 := bbase (se 7 (by rfl) ⟨134909, by rfl⟩ : syracuseStep 11512277 = 269819) (by norm_num)
theorem B7674851 : Blo 2019435 7674851 := bstep (se 1 (by rfl) ⟨5756138, by rfl⟩ : syracuseStep 7674851 = 11512277) B11512277
theorem B5116567 : Blo 2019435 5116567 := bstep (se 1 (by rfl) ⟨3837425, by rfl⟩ : syracuseStep 5116567 = 7674851) B7674851
theorem B6822089 : Blo 2019435 6822089 := bstep (se 2 (by rfl) ⟨2558283, by rfl⟩ : syracuseStep 6822089 = 5116567) B5116567
theorem B4548059 : Blo 2019435 4548059 := bstep (se 1 (by rfl) ⟨3411044, by rfl⟩ : syracuseStep 4548059 = 6822089) B6822089
theorem B3032039 : Blo 2019435 3032039 := bstep (se 1 (by rfl) ⟨2274029, by rfl⟩ : syracuseStep 3032039 = 4548059) B4548059
theorem B2021359 : Blo 2019435 2021359 := bstep (se 1 (by rfl) ⟨1516019, by rfl⟩ : syracuseStep 2021359 = 3032039) B3032039
theorem B3032045 : Blo 2019435 3032045 := bbase (se 3 (by rfl) ⟨568508, by rfl⟩ : syracuseStep 3032045 = 1137017) (by norm_num)
theorem B2021363 : Blo 2019435 2021363 := bstep (se 1 (by rfl) ⟨1516022, by rfl⟩ : syracuseStep 2021363 = 3032045) B3032045
theorem B4548077 : Blo 2019435 4548077 := bbase (se 3 (by rfl) ⟨852764, by rfl⟩ : syracuseStep 4548077 = 1705529) (by norm_num)
theorem B3032051 : Blo 2019435 3032051 := bstep (se 1 (by rfl) ⟨2274038, by rfl⟩ : syracuseStep 3032051 = 4548077) B4548077
theorem B2021367 : Blo 2019435 2021367 := bstep (se 1 (by rfl) ⟨1516025, by rfl⟩ : syracuseStep 2021367 = 3032051) B3032051
theorem B4856773 : Blo 2019435 4856773 := bbase (se 4 (by rfl) ⟨455322, by rfl⟩ : syracuseStep 4856773 = 910645) (by norm_num)
theorem B6475697 : Blo 2019435 6475697 := bstep (se 2 (by rfl) ⟨2428386, by rfl⟩ : syracuseStep 6475697 = 4856773) B4856773
theorem B4317131 : Blo 2019435 4317131 := bstep (se 1 (by rfl) ⟨3237848, by rfl⟩ : syracuseStep 4317131 = 6475697) B6475697
theorem B2878087 : Blo 2019435 2878087 := bstep (se 1 (by rfl) ⟨2158565, by rfl⟩ : syracuseStep 2878087 = 4317131) B4317131
theorem B3837449 : Blo 2019435 3837449 := bstep (se 2 (by rfl) ⟨1439043, by rfl⟩ : syracuseStep 3837449 = 2878087) B2878087
theorem B2558299 : Blo 2019435 2558299 := bstep (se 1 (by rfl) ⟨1918724, by rfl⟩ : syracuseStep 2558299 = 3837449) B3837449
theorem B3411065 : Blo 2019435 3411065 := bstep (se 2 (by rfl) ⟨1279149, by rfl⟩ : syracuseStep 3411065 = 2558299) B2558299
theorem B2274043 : Blo 2019435 2274043 := bstep (se 1 (by rfl) ⟨1705532, by rfl⟩ : syracuseStep 2274043 = 3411065) B3411065
theorem B3032057 : Blo 2019435 3032057 := bstep (se 2 (by rfl) ⟨1137021, by rfl⟩ : syracuseStep 3032057 = 2274043) B2274043
theorem B2021371 : Blo 2019435 2021371 := bstep (se 1 (by rfl) ⟨1516028, by rfl⟩ : syracuseStep 2021371 = 3032057) B3032057
theorem B6915221 : Blo 2019435 6915221 := bbase (se 6 (by rfl) ⟨162075, by rfl⟩ : syracuseStep 6915221 = 324151) (by norm_num)
theorem B4610147 : Blo 2019435 4610147 := bstep (se 1 (by rfl) ⟨3457610, by rfl⟩ : syracuseStep 4610147 = 6915221) B6915221
theorem B49174901 : Blo 2019435 49174901 := bstep (se 5 (by rfl) ⟨2305073, by rfl⟩ : syracuseStep 49174901 = 4610147) B4610147
theorem B32783267 : Blo 2019435 32783267 := bstep (se 1 (by rfl) ⟨24587450, by rfl⟩ : syracuseStep 32783267 = 49174901) B49174901
theorem B21855511 : Blo 2019435 21855511 := bstep (se 1 (by rfl) ⟨16391633, by rfl⟩ : syracuseStep 21855511 = 32783267) B32783267
theorem B116562725 : Blo 2019435 116562725 := bstep (se 4 (by rfl) ⟨10927755, by rfl⟩ : syracuseStep 116562725 = 21855511) B21855511
theorem B77708483 : Blo 2019435 77708483 := bstep (se 1 (by rfl) ⟨58281362, by rfl⟩ : syracuseStep 77708483 = 116562725) B116562725
theorem B51805655 : Blo 2019435 51805655 := bstep (se 1 (by rfl) ⟨38854241, by rfl⟩ : syracuseStep 51805655 = 77708483) B77708483
theorem B34537103 : Blo 2019435 34537103 := bstep (se 1 (by rfl) ⟨25902827, by rfl⟩ : syracuseStep 34537103 = 51805655) B51805655
theorem B23024735 : Blo 2019435 23024735 := bstep (se 1 (by rfl) ⟨17268551, by rfl⟩ : syracuseStep 23024735 = 34537103) B34537103
theorem B15349823 : Blo 2019435 15349823 := bstep (se 1 (by rfl) ⟨11512367, by rfl⟩ : syracuseStep 15349823 = 23024735) B23024735
theorem B10233215 : Blo 2019435 10233215 := bstep (se 1 (by rfl) ⟨7674911, by rfl⟩ : syracuseStep 10233215 = 15349823) B15349823
theorem B6822143 : Blo 2019435 6822143 := bstep (se 1 (by rfl) ⟨5116607, by rfl⟩ : syracuseStep 6822143 = 10233215) B10233215
theorem B4548095 : Blo 2019435 4548095 := bstep (se 1 (by rfl) ⟨3411071, by rfl⟩ : syracuseStep 4548095 = 6822143) B6822143
theorem B3032063 : Blo 2019435 3032063 := bstep (se 1 (by rfl) ⟨2274047, by rfl⟩ : syracuseStep 3032063 = 4548095) B4548095
theorem B2021375 : Blo 2019435 2021375 := bstep (se 1 (by rfl) ⟨1516031, by rfl⟩ : syracuseStep 2021375 = 3032063) B3032063
theorem B3032069 : Blo 2019435 3032069 := bbase (se 4 (by rfl) ⟨284256, by rfl⟩ : syracuseStep 3032069 = 568513) (by norm_num)
theorem B2021379 : Blo 2019435 2021379 := bstep (se 1 (by rfl) ⟨1516034, by rfl⟩ : syracuseStep 2021379 = 3032069) B3032069
theorem B3411085 : Blo 2019435 3411085 := bbase (se 3 (by rfl) ⟨639578, by rfl⟩ : syracuseStep 3411085 = 1279157) (by norm_num)
theorem B4548113 : Blo 2019435 4548113 := bstep (se 2 (by rfl) ⟨1705542, by rfl⟩ : syracuseStep 4548113 = 3411085) B3411085
theorem B3032075 : Blo 2019435 3032075 := bstep (se 1 (by rfl) ⟨2274056, by rfl⟩ : syracuseStep 3032075 = 4548113) B4548113
theorem B2021383 : Blo 2019435 2021383 := bstep (se 1 (by rfl) ⟨1516037, by rfl⟩ : syracuseStep 2021383 = 3032075) B3032075
theorem B2274061 : Blo 2019435 2274061 := bbase (se 3 (by rfl) ⟨426386, by rfl⟩ : syracuseStep 2274061 = 852773) (by norm_num)
theorem B3032081 : Blo 2019435 3032081 := bstep (se 2 (by rfl) ⟨1137030, by rfl⟩ : syracuseStep 3032081 = 2274061) B2274061
theorem B2021387 : Blo 2019435 2021387 := bstep (se 1 (by rfl) ⟨1516040, by rfl⟩ : syracuseStep 2021387 = 3032081) B3032081
theorem B6822197 : Blo 2019435 6822197 := bbase (se 5 (by rfl) ⟨319790, by rfl⟩ : syracuseStep 6822197 = 639581) (by norm_num)
theorem B4548131 : Blo 2019435 4548131 := bstep (se 1 (by rfl) ⟨3411098, by rfl⟩ : syracuseStep 4548131 = 6822197) B6822197
theorem B3032087 : Blo 2019435 3032087 := bstep (se 1 (by rfl) ⟨2274065, by rfl⟩ : syracuseStep 3032087 = 4548131) B4548131
theorem B2021391 : Blo 2019435 2021391 := bstep (se 1 (by rfl) ⟨1516043, by rfl⟩ : syracuseStep 2021391 = 3032087) B3032087
theorem B3032093 : Blo 2019435 3032093 := bbase (se 3 (by rfl) ⟨568517, by rfl⟩ : syracuseStep 3032093 = 1137035) (by norm_num)
theorem B2021395 : Blo 2019435 2021395 := bstep (se 1 (by rfl) ⟨1516046, by rfl⟩ : syracuseStep 2021395 = 3032093) B3032093
theorem B4548149 : Blo 2019435 4548149 := bbase (se 5 (by rfl) ⟨213194, by rfl⟩ : syracuseStep 4548149 = 426389) (by norm_num)
theorem B3032099 : Blo 2019435 3032099 := bstep (se 1 (by rfl) ⟨2274074, by rfl⟩ : syracuseStep 3032099 = 4548149) B4548149
theorem B2021399 : Blo 2019435 2021399 := bstep (se 1 (by rfl) ⟨1516049, by rfl⟩ : syracuseStep 2021399 = 3032099) B3032099
theorem B3642637 : Blo 2019435 3642637 := bbase (se 3 (by rfl) ⟨682994, by rfl⟩ : syracuseStep 3642637 = 1365989) (by norm_num)
theorem B4856849 : Blo 2019435 4856849 := bstep (se 2 (by rfl) ⟨1821318, by rfl⟩ : syracuseStep 4856849 = 3642637) B3642637
theorem B3237899 : Blo 2019435 3237899 := bstep (se 1 (by rfl) ⟨2428424, by rfl⟩ : syracuseStep 3237899 = 4856849) B4856849
theorem B8634397 : Blo 2019435 8634397 := bstep (se 3 (by rfl) ⟨1618949, by rfl⟩ : syracuseStep 8634397 = 3237899) B3237899
theorem B11512529 : Blo 2019435 11512529 := bstep (se 2 (by rfl) ⟨4317198, by rfl⟩ : syracuseStep 11512529 = 8634397) B8634397
theorem B7675019 : Blo 2019435 7675019 := bstep (se 1 (by rfl) ⟨5756264, by rfl⟩ : syracuseStep 7675019 = 11512529) B11512529
theorem B5116679 : Blo 2019435 5116679 := bstep (se 1 (by rfl) ⟨3837509, by rfl⟩ : syracuseStep 5116679 = 7675019) B7675019
theorem B3411119 : Blo 2019435 3411119 := bstep (se 1 (by rfl) ⟨2558339, by rfl⟩ : syracuseStep 3411119 = 5116679) B5116679
theorem B2274079 : Blo 2019435 2274079 := bstep (se 1 (by rfl) ⟨1705559, by rfl⟩ : syracuseStep 2274079 = 3411119) B3411119
theorem B3032105 : Blo 2019435 3032105 := bstep (se 2 (by rfl) ⟨1137039, by rfl⟩ : syracuseStep 3032105 = 2274079) B2274079
theorem B2021403 : Blo 2019435 2021403 := bstep (se 1 (by rfl) ⟨1516052, by rfl⟩ : syracuseStep 2021403 = 3032105) B3032105
theorem B2428429 : Blo 2019435 2428429 := bbase (se 3 (by rfl) ⟨455330, by rfl⟩ : syracuseStep 2428429 = 910661) (by norm_num)
theorem B3237905 : Blo 2019435 3237905 := bstep (se 2 (by rfl) ⟨1214214, by rfl⟩ : syracuseStep 3237905 = 2428429) B2428429
theorem B8634413 : Blo 2019435 8634413 := bstep (se 3 (by rfl) ⟨1618952, by rfl⟩ : syracuseStep 8634413 = 3237905) B3237905
theorem B5756275 : Blo 2019435 5756275 := bstep (se 1 (by rfl) ⟨4317206, by rfl⟩ : syracuseStep 5756275 = 8634413) B8634413
theorem B7675033 : Blo 2019435 7675033 := bstep (se 2 (by rfl) ⟨2878137, by rfl⟩ : syracuseStep 7675033 = 5756275) B5756275
theorem B10233377 : Blo 2019435 10233377 := bstep (se 2 (by rfl) ⟨3837516, by rfl⟩ : syracuseStep 10233377 = 7675033) B7675033
theorem B6822251 : Blo 2019435 6822251 := bstep (se 1 (by rfl) ⟨5116688, by rfl⟩ : syracuseStep 6822251 = 10233377) B10233377
theorem B4548167 : Blo 2019435 4548167 := bstep (se 1 (by rfl) ⟨3411125, by rfl⟩ : syracuseStep 4548167 = 6822251) B6822251
theorem B3032111 : Blo 2019435 3032111 := bstep (se 1 (by rfl) ⟨2274083, by rfl⟩ : syracuseStep 3032111 = 4548167) B4548167
theorem B2021407 : Blo 2019435 2021407 := bstep (se 1 (by rfl) ⟨1516055, by rfl⟩ : syracuseStep 2021407 = 3032111) B3032111
theorem B3032117 : Blo 2019435 3032117 := bbase (se 5 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 3032117 = 284261) (by norm_num)
theorem B2021411 : Blo 2019435 2021411 := bstep (se 1 (by rfl) ⟨1516058, by rfl⟩ : syracuseStep 2021411 = 3032117) B3032117
theorem B5116709 : Blo 2019435 5116709 := bbase (se 4 (by rfl) ⟨479691, by rfl⟩ : syracuseStep 5116709 = 959383) (by norm_num)
theorem B3411139 : Blo 2019435 3411139 := bstep (se 1 (by rfl) ⟨2558354, by rfl⟩ : syracuseStep 3411139 = 5116709) B5116709
theorem B4548185 : Blo 2019435 4548185 := bstep (se 2 (by rfl) ⟨1705569, by rfl⟩ : syracuseStep 4548185 = 3411139) B3411139
theorem B3032123 : Blo 2019435 3032123 := bstep (se 1 (by rfl) ⟨2274092, by rfl⟩ : syracuseStep 3032123 = 4548185) B4548185
theorem B2021415 : Blo 2019435 2021415 := bstep (se 1 (by rfl) ⟨1516061, by rfl⟩ : syracuseStep 2021415 = 3032123) B3032123
theorem B2274097 : Blo 2019435 2274097 := bbase (se 2 (by rfl) ⟨852786, by rfl⟩ : syracuseStep 2274097 = 1705573) (by norm_num)
theorem B3032129 : Blo 2019435 3032129 := bstep (se 2 (by rfl) ⟨1137048, by rfl⟩ : syracuseStep 3032129 = 2274097) B2274097
theorem B2021419 : Blo 2019435 2021419 := bstep (se 1 (by rfl) ⟨1516064, by rfl⟩ : syracuseStep 2021419 = 3032129) B3032129
theorem B2732005 : Blo 2019435 2732005 := bbase (se 4 (by rfl) ⟨256125, by rfl⟩ : syracuseStep 2732005 = 512251) (by norm_num)
theorem B3642673 : Blo 2019435 3642673 := bstep (se 2 (by rfl) ⟨1366002, by rfl⟩ : syracuseStep 3642673 = 2732005) B2732005
theorem B4856897 : Blo 2019435 4856897 := bstep (se 2 (by rfl) ⟨1821336, by rfl⟩ : syracuseStep 4856897 = 3642673) B3642673
theorem B3237931 : Blo 2019435 3237931 := bstep (se 1 (by rfl) ⟨2428448, by rfl⟩ : syracuseStep 3237931 = 4856897) B4856897
theorem B4317241 : Blo 2019435 4317241 := bstep (se 2 (by rfl) ⟨1618965, by rfl⟩ : syracuseStep 4317241 = 3237931) B3237931
theorem B5756321 : Blo 2019435 5756321 := bstep (se 2 (by rfl) ⟨2158620, by rfl⟩ : syracuseStep 5756321 = 4317241) B4317241
theorem B3837547 : Blo 2019435 3837547 := bstep (se 1 (by rfl) ⟨2878160, by rfl⟩ : syracuseStep 3837547 = 5756321) B5756321
theorem B5116729 : Blo 2019435 5116729 := bstep (se 2 (by rfl) ⟨1918773, by rfl⟩ : syracuseStep 5116729 = 3837547) B3837547
theorem B6822305 : Blo 2019435 6822305 := bstep (se 2 (by rfl) ⟨2558364, by rfl⟩ : syracuseStep 6822305 = 5116729) B5116729
theorem B4548203 : Blo 2019435 4548203 := bstep (se 1 (by rfl) ⟨3411152, by rfl⟩ : syracuseStep 4548203 = 6822305) B6822305
theorem B3032135 : Blo 2019435 3032135 := bstep (se 1 (by rfl) ⟨2274101, by rfl⟩ : syracuseStep 3032135 = 4548203) B4548203
theorem B2021423 : Blo 2019435 2021423 := bstep (se 1 (by rfl) ⟨1516067, by rfl⟩ : syracuseStep 2021423 = 3032135) B3032135
theorem B3032141 : Blo 2019435 3032141 := bbase (se 3 (by rfl) ⟨568526, by rfl⟩ : syracuseStep 3032141 = 1137053) (by norm_num)
theorem B2021427 : Blo 2019435 2021427 := bstep (se 1 (by rfl) ⟨1516070, by rfl⟩ : syracuseStep 2021427 = 3032141) B3032141
theorem B4548221 : Blo 2019435 4548221 := bbase (se 3 (by rfl) ⟨852791, by rfl⟩ : syracuseStep 4548221 = 1705583) (by norm_num)
theorem B3032147 : Blo 2019435 3032147 := bstep (se 1 (by rfl) ⟨2274110, by rfl⟩ : syracuseStep 3032147 = 4548221) B4548221
theorem B2021431 : Blo 2019435 2021431 := bstep (se 1 (by rfl) ⟨1516073, by rfl⟩ : syracuseStep 2021431 = 3032147) B3032147
theorem B3411173 : Blo 2019435 3411173 := bbase (se 4 (by rfl) ⟨319797, by rfl⟩ : syracuseStep 3411173 = 639595) (by norm_num)
theorem B2274115 : Blo 2019435 2274115 := bstep (se 1 (by rfl) ⟨1705586, by rfl⟩ : syracuseStep 2274115 = 3411173) B3411173
theorem B3032153 : Blo 2019435 3032153 := bstep (se 2 (by rfl) ⟨1137057, by rfl⟩ : syracuseStep 3032153 = 2274115) B2274115
theorem B2021435 : Blo 2019435 2021435 := bstep (se 1 (by rfl) ⟨1516076, by rfl⟩ : syracuseStep 2021435 = 3032153) B3032153
theorem C0 (j : ℕ) (h1 : 504858 ≤ j) (h2 : j ≤ 505358) : Blo 2019435 (4 * j + 3) := by
  interval_cases j
  · exact B2019435
  · exact B2019439
  · exact B2019443
  · exact B2019447
  · exact B2019451
  · exact B2019455
  · exact B2019459
  · exact B2019463
  · exact B2019467
  · exact B2019471
  · exact B2019475
  · exact B2019479
  · exact B2019483
  · exact B2019487
  · exact B2019491
  · exact B2019495
  · exact B2019499
  · exact B2019503
  · exact B2019507
  · exact B2019511
  · exact B2019515
  · exact B2019519
  · exact B2019523
  · exact B2019527
  · exact B2019531
  · exact B2019535
  · exact B2019539
  · exact B2019543
  · exact B2019547
  · exact B2019551
  · exact B2019555
  · exact B2019559
  · exact B2019563
  · exact B2019567
  · exact B2019571
  · exact B2019575
  · exact B2019579
  · exact B2019583
  · exact B2019587
  · exact B2019591
  · exact B2019595
  · exact B2019599
  · exact B2019603
  · exact B2019607
  · exact B2019611
  · exact B2019615
  · exact B2019619
  · exact B2019623
  · exact B2019627
  · exact B2019631
  · exact B2019635
  · exact B2019639
  · exact B2019643
  · exact B2019647
  · exact B2019651
  · exact B2019655
  · exact B2019659
  · exact B2019663
  · exact B2019667
  · exact B2019671
  · exact B2019675
  · exact B2019679
  · exact B2019683
  · exact B2019687
  · exact B2019691
  · exact B2019695
  · exact B2019699
  · exact B2019703
  · exact B2019707
  · exact B2019711
  · exact B2019715
  · exact B2019719
  · exact B2019723
  · exact B2019727
  · exact B2019731
  · exact B2019735
  · exact B2019739
  · exact B2019743
  · exact B2019747
  · exact B2019751
  · exact B2019755
  · exact B2019759
  · exact B2019763
  · exact B2019767
  · exact B2019771
  · exact B2019775
  · exact B2019779
  · exact B2019783
  · exact B2019787
  · exact B2019791
  · exact B2019795
  · exact B2019799
  · exact B2019803
  · exact B2019807
  · exact B2019811
  · exact B2019815
  · exact B2019819
  · exact B2019823
  · exact B2019827
  · exact B2019831
  · exact B2019835
  · exact B2019839
  · exact B2019843
  · exact B2019847
  · exact B2019851
  · exact B2019855
  · exact B2019859
  · exact B2019863
  · exact B2019867
  · exact B2019871
  · exact B2019875
  · exact B2019879
  · exact B2019883
  · exact B2019887
  · exact B2019891
  · exact B2019895
  · exact B2019899
  · exact B2019903
  · exact B2019907
  · exact B2019911
  · exact B2019915
  · exact B2019919
  · exact B2019923
  · exact B2019927
  · exact B2019931
  · exact B2019935
  · exact B2019939
  · exact B2019943
  · exact B2019947
  · exact B2019951
  · exact B2019955
  · exact B2019959
  · exact B2019963
  · exact B2019967
  · exact B2019971
  · exact B2019975
  · exact B2019979
  · exact B2019983
  · exact B2019987
  · exact B2019991
  · exact B2019995
  · exact B2019999
  · exact B2020003
  · exact B2020007
  · exact B2020011
  · exact B2020015
  · exact B2020019
  · exact B2020023
  · exact B2020027
  · exact B2020031
  · exact B2020035
  · exact B2020039
  · exact B2020043
  · exact B2020047
  · exact B2020051
  · exact B2020055
  · exact B2020059
  · exact B2020063
  · exact B2020067
  · exact B2020071
  · exact B2020075
  · exact B2020079
  · exact B2020083
  · exact B2020087
  · exact B2020091
  · exact B2020095
  · exact B2020099
  · exact B2020103
  · exact B2020107
  · exact B2020111
  · exact B2020115
  · exact B2020119
  · exact B2020123
  · exact B2020127
  · exact B2020131
  · exact B2020135
  · exact B2020139
  · exact B2020143
  · exact B2020147
  · exact B2020151
  · exact B2020155
  · exact B2020159
  · exact B2020163
  · exact B2020167
  · exact B2020171
  · exact B2020175
  · exact B2020179
  · exact B2020183
  · exact B2020187
  · exact B2020191
  · exact B2020195
  · exact B2020199
  · exact B2020203
  · exact B2020207
  · exact B2020211
  · exact B2020215
  · exact B2020219
  · exact B2020223
  · exact B2020227
  · exact B2020231
  · exact B2020235
  · exact B2020239
  · exact B2020243
  · exact B2020247
  · exact B2020251
  · exact B2020255
  · exact B2020259
  · exact B2020263
  · exact B2020267
  · exact B2020271
  · exact B2020275
  · exact B2020279
  · exact B2020283
  · exact B2020287
  · exact B2020291
  · exact B2020295
  · exact B2020299
  · exact B2020303
  · exact B2020307
  · exact B2020311
  · exact B2020315
  · exact B2020319
  · exact B2020323
  · exact B2020327
  · exact B2020331
  · exact B2020335
  · exact B2020339
  · exact B2020343
  · exact B2020347
  · exact B2020351
  · exact B2020355
  · exact B2020359
  · exact B2020363
  · exact B2020367
  · exact B2020371
  · exact B2020375
  · exact B2020379
  · exact B2020383
  · exact B2020387
  · exact B2020391
  · exact B2020395
  · exact B2020399
  · exact B2020403
  · exact B2020407
  · exact B2020411
  · exact B2020415
  · exact B2020419
  · exact B2020423
  · exact B2020427
  · exact B2020431
  · exact B2020435
  · exact B2020439
  · exact B2020443
  · exact B2020447
  · exact B2020451
  · exact B2020455
  · exact B2020459
  · exact B2020463
  · exact B2020467
  · exact B2020471
  · exact B2020475
  · exact B2020479
  · exact B2020483
  · exact B2020487
  · exact B2020491
  · exact B2020495
  · exact B2020499
  · exact B2020503
  · exact B2020507
  · exact B2020511
  · exact B2020515
  · exact B2020519
  · exact B2020523
  · exact B2020527
  · exact B2020531
  · exact B2020535
  · exact B2020539
  · exact B2020543
  · exact B2020547
  · exact B2020551
  · exact B2020555
  · exact B2020559
  · exact B2020563
  · exact B2020567
  · exact B2020571
  · exact B2020575
  · exact B2020579
  · exact B2020583
  · exact B2020587
  · exact B2020591
  · exact B2020595
  · exact B2020599
  · exact B2020603
  · exact B2020607
  · exact B2020611
  · exact B2020615
  · exact B2020619
  · exact B2020623
  · exact B2020627
  · exact B2020631
  · exact B2020635
  · exact B2020639
  · exact B2020643
  · exact B2020647
  · exact B2020651
  · exact B2020655
  · exact B2020659
  · exact B2020663
  · exact B2020667
  · exact B2020671
  · exact B2020675
  · exact B2020679
  · exact B2020683
  · exact B2020687
  · exact B2020691
  · exact B2020695
  · exact B2020699
  · exact B2020703
  · exact B2020707
  · exact B2020711
  · exact B2020715
  · exact B2020719
  · exact B2020723
  · exact B2020727
  · exact B2020731
  · exact B2020735
  · exact B2020739
  · exact B2020743
  · exact B2020747
  · exact B2020751
  · exact B2020755
  · exact B2020759
  · exact B2020763
  · exact B2020767
  · exact B2020771
  · exact B2020775
  · exact B2020779
  · exact B2020783
  · exact B2020787
  · exact B2020791
  · exact B2020795
  · exact B2020799
  · exact B2020803
  · exact B2020807
  · exact B2020811
  · exact B2020815
  · exact B2020819
  · exact B2020823
  · exact B2020827
  · exact B2020831
  · exact B2020835
  · exact B2020839
  · exact B2020843
  · exact B2020847
  · exact B2020851
  · exact B2020855
  · exact B2020859
  · exact B2020863
  · exact B2020867
  · exact B2020871
  · exact B2020875
  · exact B2020879
  · exact B2020883
  · exact B2020887
  · exact B2020891
  · exact B2020895
  · exact B2020899
  · exact B2020903
  · exact B2020907
  · exact B2020911
  · exact B2020915
  · exact B2020919
  · exact B2020923
  · exact B2020927
  · exact B2020931
  · exact B2020935
  · exact B2020939
  · exact B2020943
  · exact B2020947
  · exact B2020951
  · exact B2020955
  · exact B2020959
  · exact B2020963
  · exact B2020967
  · exact B2020971
  · exact B2020975
  · exact B2020979
  · exact B2020983
  · exact B2020987
  · exact B2020991
  · exact B2020995
  · exact B2020999
  · exact B2021003
  · exact B2021007
  · exact B2021011
  · exact B2021015
  · exact B2021019
  · exact B2021023
  · exact B2021027
  · exact B2021031
  · exact B2021035
  · exact B2021039
  · exact B2021043
  · exact B2021047
  · exact B2021051
  · exact B2021055
  · exact B2021059
  · exact B2021063
  · exact B2021067
  · exact B2021071
  · exact B2021075
  · exact B2021079
  · exact B2021083
  · exact B2021087
  · exact B2021091
  · exact B2021095
  · exact B2021099
  · exact B2021103
  · exact B2021107
  · exact B2021111
  · exact B2021115
  · exact B2021119
  · exact B2021123
  · exact B2021127
  · exact B2021131
  · exact B2021135
  · exact B2021139
  · exact B2021143
  · exact B2021147
  · exact B2021151
  · exact B2021155
  · exact B2021159
  · exact B2021163
  · exact B2021167
  · exact B2021171
  · exact B2021175
  · exact B2021179
  · exact B2021183
  · exact B2021187
  · exact B2021191
  · exact B2021195
  · exact B2021199
  · exact B2021203
  · exact B2021207
  · exact B2021211
  · exact B2021215
  · exact B2021219
  · exact B2021223
  · exact B2021227
  · exact B2021231
  · exact B2021235
  · exact B2021239
  · exact B2021243
  · exact B2021247
  · exact B2021251
  · exact B2021255
  · exact B2021259
  · exact B2021263
  · exact B2021267
  · exact B2021271
  · exact B2021275
  · exact B2021279
  · exact B2021283
  · exact B2021287
  · exact B2021291
  · exact B2021295
  · exact B2021299
  · exact B2021303
  · exact B2021307
  · exact B2021311
  · exact B2021315
  · exact B2021319
  · exact B2021323
  · exact B2021327
  · exact B2021331
  · exact B2021335
  · exact B2021339
  · exact B2021343
  · exact B2021347
  · exact B2021351
  · exact B2021355
  · exact B2021359
  · exact B2021363
  · exact B2021367
  · exact B2021371
  · exact B2021375
  · exact B2021379
  · exact B2021383
  · exact B2021387
  · exact B2021391
  · exact B2021395
  · exact B2021399
  · exact B2021403
  · exact B2021407
  · exact B2021411
  · exact B2021415
  · exact B2021419
  · exact B2021423
  · exact B2021427
  · exact B2021431
  · exact B2021435
theorem solution (m : ℕ) (hlo : 2019435 ≤ m) (hhi : m ≤ 2021435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 504858 ≤ j := by omega
    have hj2 : j ≤ 505358 := by omega
    have hb : Blo 2019435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
