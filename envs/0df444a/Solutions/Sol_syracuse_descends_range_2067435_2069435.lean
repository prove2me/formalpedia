-- Prove2me | solution 1 for syracuse_descends_range_2067435_2069435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:01.734807+00:00
-- url     : https://prove2.me/submissions/59a78a93-c0b0-4341-971a-8828eb936f2d

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

theorem B2325865 : Blo 2067435 2325865 := bbase (se 2 (by rfl) ⟨872199, by rfl⟩ : syracuseStep 2325865 = 1744399) (by norm_num)
theorem B3101153 : Blo 2067435 3101153 := bstep (se 2 (by rfl) ⟨1162932, by rfl⟩ : syracuseStep 3101153 = 2325865) B2325865
theorem B2067435 : Blo 2067435 2067435 := bstep (se 1 (by rfl) ⟨1550576, by rfl⟩ : syracuseStep 2067435 = 3101153) B3101153
theorem B4536829 : Blo 2067435 4536829 := bbase (se 3 (by rfl) ⟨850655, by rfl⟩ : syracuseStep 4536829 = 1701311) (by norm_num)
theorem B24196421 : Blo 2067435 24196421 := bstep (se 4 (by rfl) ⟨2268414, by rfl⟩ : syracuseStep 24196421 = 4536829) B4536829
theorem B16130947 : Blo 2067435 16130947 := bstep (se 1 (by rfl) ⟨12098210, by rfl⟩ : syracuseStep 16130947 = 24196421) B24196421
theorem B21507929 : Blo 2067435 21507929 := bstep (se 2 (by rfl) ⟨8065473, by rfl⟩ : syracuseStep 21507929 = 16130947) B16130947
theorem B14338619 : Blo 2067435 14338619 := bstep (se 1 (by rfl) ⟨10753964, by rfl⟩ : syracuseStep 14338619 = 21507929) B21507929
theorem B9559079 : Blo 2067435 9559079 := bstep (se 1 (by rfl) ⟨7169309, by rfl⟩ : syracuseStep 9559079 = 14338619) B14338619
theorem B6372719 : Blo 2067435 6372719 := bstep (se 1 (by rfl) ⟨4779539, by rfl⟩ : syracuseStep 6372719 = 9559079) B9559079
theorem B4248479 : Blo 2067435 4248479 := bstep (se 1 (by rfl) ⟨3186359, by rfl⟩ : syracuseStep 4248479 = 6372719) B6372719
theorem B2832319 : Blo 2067435 2832319 := bstep (se 1 (by rfl) ⟨2124239, by rfl⟩ : syracuseStep 2832319 = 4248479) B4248479
theorem B3776425 : Blo 2067435 3776425 := bstep (se 2 (by rfl) ⟨1416159, by rfl⟩ : syracuseStep 3776425 = 2832319) B2832319
theorem B20140933 : Blo 2067435 20140933 := bstep (se 4 (by rfl) ⟨1888212, by rfl⟩ : syracuseStep 20140933 = 3776425) B3776425
theorem B26854577 : Blo 2067435 26854577 := bstep (se 2 (by rfl) ⟨10070466, by rfl⟩ : syracuseStep 26854577 = 20140933) B20140933
theorem B17903051 : Blo 2067435 17903051 := bstep (se 1 (by rfl) ⟨13427288, by rfl⟩ : syracuseStep 17903051 = 26854577) B26854577
theorem B11935367 : Blo 2067435 11935367 := bstep (se 1 (by rfl) ⟨8951525, by rfl⟩ : syracuseStep 11935367 = 17903051) B17903051
theorem B7956911 : Blo 2067435 7956911 := bstep (se 1 (by rfl) ⟨5967683, by rfl⟩ : syracuseStep 7956911 = 11935367) B11935367
theorem B21218429 : Blo 2067435 21218429 := bstep (se 3 (by rfl) ⟨3978455, by rfl⟩ : syracuseStep 21218429 = 7956911) B7956911
theorem B14145619 : Blo 2067435 14145619 := bstep (se 1 (by rfl) ⟨10609214, by rfl⟩ : syracuseStep 14145619 = 21218429) B21218429
theorem B18860825 : Blo 2067435 18860825 := bstep (se 2 (by rfl) ⟨7072809, by rfl⟩ : syracuseStep 18860825 = 14145619) B14145619
theorem B12573883 : Blo 2067435 12573883 := bstep (se 1 (by rfl) ⟨9430412, by rfl⟩ : syracuseStep 12573883 = 18860825) B18860825
theorem B16765177 : Blo 2067435 16765177 := bstep (se 2 (by rfl) ⟨6286941, by rfl⟩ : syracuseStep 16765177 = 12573883) B12573883
theorem B22353569 : Blo 2067435 22353569 := bstep (se 2 (by rfl) ⟨8382588, by rfl⟩ : syracuseStep 22353569 = 16765177) B16765177
theorem B14902379 : Blo 2067435 14902379 := bstep (se 1 (by rfl) ⟨11176784, by rfl⟩ : syracuseStep 14902379 = 22353569) B22353569
theorem B9934919 : Blo 2067435 9934919 := bstep (se 1 (by rfl) ⟨7451189, by rfl⟩ : syracuseStep 9934919 = 14902379) B14902379
theorem B6623279 : Blo 2067435 6623279 := bstep (se 1 (by rfl) ⟨4967459, by rfl⟩ : syracuseStep 6623279 = 9934919) B9934919
theorem B4415519 : Blo 2067435 4415519 := bstep (se 1 (by rfl) ⟨3311639, by rfl⟩ : syracuseStep 4415519 = 6623279) B6623279
theorem B11774717 : Blo 2067435 11774717 := bstep (se 3 (by rfl) ⟨2207759, by rfl⟩ : syracuseStep 11774717 = 4415519) B4415519
theorem B7849811 : Blo 2067435 7849811 := bstep (se 1 (by rfl) ⟨5887358, by rfl⟩ : syracuseStep 7849811 = 11774717) B11774717
theorem B5233207 : Blo 2067435 5233207 := bstep (se 1 (by rfl) ⟨3924905, by rfl⟩ : syracuseStep 5233207 = 7849811) B7849811
theorem B6977609 : Blo 2067435 6977609 := bstep (se 2 (by rfl) ⟨2616603, by rfl⟩ : syracuseStep 6977609 = 5233207) B5233207
theorem B4651739 : Blo 2067435 4651739 := bstep (se 1 (by rfl) ⟨3488804, by rfl⟩ : syracuseStep 4651739 = 6977609) B6977609
theorem B3101159 : Blo 2067435 3101159 := bstep (se 1 (by rfl) ⟨2325869, by rfl⟩ : syracuseStep 3101159 = 4651739) B4651739
theorem B2067439 : Blo 2067435 2067439 := bstep (se 1 (by rfl) ⟨1550579, by rfl⟩ : syracuseStep 2067439 = 3101159) B3101159
theorem B3101165 : Blo 2067435 3101165 := bbase (se 3 (by rfl) ⟨581468, by rfl⟩ : syracuseStep 3101165 = 1162937) (by norm_num)
theorem B2067443 : Blo 2067435 2067443 := bstep (se 1 (by rfl) ⟨1550582, by rfl⟩ : syracuseStep 2067443 = 3101165) B3101165
theorem B4651757 : Blo 2067435 4651757 := bbase (se 3 (by rfl) ⟨872204, by rfl⟩ : syracuseStep 4651757 = 1744409) (by norm_num)
theorem B3101171 : Blo 2067435 3101171 := bstep (se 1 (by rfl) ⟨2325878, by rfl⟩ : syracuseStep 3101171 = 4651757) B4651757
theorem B2067447 : Blo 2067435 2067447 := bstep (se 1 (by rfl) ⟨1550585, by rfl⟩ : syracuseStep 2067447 = 3101171) B3101171
theorem B2207773 : Blo 2067435 2207773 := bbase (se 3 (by rfl) ⟨413957, by rfl⟩ : syracuseStep 2207773 = 827915) (by norm_num)
theorem B2943697 : Blo 2067435 2943697 := bstep (se 2 (by rfl) ⟨1103886, by rfl⟩ : syracuseStep 2943697 = 2207773) B2207773
theorem B3924929 : Blo 2067435 3924929 := bstep (se 2 (by rfl) ⟨1471848, by rfl⟩ : syracuseStep 3924929 = 2943697) B2943697
theorem B2616619 : Blo 2067435 2616619 := bstep (se 1 (by rfl) ⟨1962464, by rfl⟩ : syracuseStep 2616619 = 3924929) B3924929
theorem B3488825 : Blo 2067435 3488825 := bstep (se 2 (by rfl) ⟨1308309, by rfl⟩ : syracuseStep 3488825 = 2616619) B2616619
theorem B2325883 : Blo 2067435 2325883 := bstep (se 1 (by rfl) ⟨1744412, by rfl⟩ : syracuseStep 2325883 = 3488825) B3488825
theorem B3101177 : Blo 2067435 3101177 := bstep (se 2 (by rfl) ⟨1162941, by rfl⟩ : syracuseStep 3101177 = 2325883) B2325883
theorem B2067451 : Blo 2067435 2067451 := bstep (se 1 (by rfl) ⟨1550588, by rfl⟩ : syracuseStep 2067451 = 3101177) B3101177
theorem B2422393 : Blo 2067435 2422393 := bbase (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) (by norm_num)
theorem B12919429 : Blo 2067435 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B68903621 : Blo 2067435 68903621 := bstep (se 4 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 68903621 = 12919429) B12919429
theorem B45935747 : Blo 2067435 45935747 := bstep (se 1 (by rfl) ⟨34451810, by rfl⟩ : syracuseStep 45935747 = 68903621) B68903621
theorem B30623831 : Blo 2067435 30623831 := bstep (se 1 (by rfl) ⟨22967873, by rfl⟩ : syracuseStep 30623831 = 45935747) B45935747
theorem B20415887 : Blo 2067435 20415887 := bstep (se 1 (by rfl) ⟨15311915, by rfl⟩ : syracuseStep 20415887 = 30623831) B30623831
theorem B13610591 : Blo 2067435 13610591 := bstep (se 1 (by rfl) ⟨10207943, by rfl⟩ : syracuseStep 13610591 = 20415887) B20415887
theorem B9073727 : Blo 2067435 9073727 := bstep (se 1 (by rfl) ⟨6805295, by rfl⟩ : syracuseStep 9073727 = 13610591) B13610591
theorem B6049151 : Blo 2067435 6049151 := bstep (se 1 (by rfl) ⟨4536863, by rfl⟩ : syracuseStep 6049151 = 9073727) B9073727
theorem B4032767 : Blo 2067435 4032767 := bstep (se 1 (by rfl) ⟨3024575, by rfl⟩ : syracuseStep 4032767 = 6049151) B6049151
theorem B10754045 : Blo 2067435 10754045 := bstep (se 3 (by rfl) ⟨2016383, by rfl⟩ : syracuseStep 10754045 = 4032767) B4032767
theorem B7169363 : Blo 2067435 7169363 := bstep (se 1 (by rfl) ⟨5377022, by rfl⟩ : syracuseStep 7169363 = 10754045) B10754045
theorem B4779575 : Blo 2067435 4779575 := bstep (se 1 (by rfl) ⟨3584681, by rfl⟩ : syracuseStep 4779575 = 7169363) B7169363
theorem B3186383 : Blo 2067435 3186383 := bstep (se 1 (by rfl) ⟨2389787, by rfl⟩ : syracuseStep 3186383 = 4779575) B4779575
theorem B33988085 : Blo 2067435 33988085 := bstep (se 5 (by rfl) ⟨1593191, by rfl⟩ : syracuseStep 33988085 = 3186383) B3186383
theorem B22658723 : Blo 2067435 22658723 := bstep (se 1 (by rfl) ⟨16994042, by rfl⟩ : syracuseStep 22658723 = 33988085) B33988085
theorem B15105815 : Blo 2067435 15105815 := bstep (se 1 (by rfl) ⟨11329361, by rfl⟩ : syracuseStep 15105815 = 22658723) B22658723
theorem B10070543 : Blo 2067435 10070543 := bstep (se 1 (by rfl) ⟨7552907, by rfl⟩ : syracuseStep 10070543 = 15105815) B15105815
theorem B6713695 : Blo 2067435 6713695 := bstep (se 1 (by rfl) ⟨5035271, by rfl⟩ : syracuseStep 6713695 = 10070543) B10070543
theorem B8951593 : Blo 2067435 8951593 := bstep (se 2 (by rfl) ⟨3356847, by rfl⟩ : syracuseStep 8951593 = 6713695) B6713695
theorem B11935457 : Blo 2067435 11935457 := bstep (se 2 (by rfl) ⟨4475796, by rfl⟩ : syracuseStep 11935457 = 8951593) B8951593
theorem B7956971 : Blo 2067435 7956971 := bstep (se 1 (by rfl) ⟨5967728, by rfl⟩ : syracuseStep 7956971 = 11935457) B11935457
theorem B5304647 : Blo 2067435 5304647 := bstep (se 1 (by rfl) ⟨3978485, by rfl⟩ : syracuseStep 5304647 = 7956971) B7956971
theorem B14145725 : Blo 2067435 14145725 := bstep (se 3 (by rfl) ⟨2652323, by rfl⟩ : syracuseStep 14145725 = 5304647) B5304647
theorem B37721933 : Blo 2067435 37721933 := bstep (se 3 (by rfl) ⟨7072862, by rfl⟩ : syracuseStep 37721933 = 14145725) B14145725
theorem B25147955 : Blo 2067435 25147955 := bstep (se 1 (by rfl) ⟨18860966, by rfl⟩ : syracuseStep 25147955 = 37721933) B37721933
theorem B16765303 : Blo 2067435 16765303 := bstep (se 1 (by rfl) ⟨12573977, by rfl⟩ : syracuseStep 16765303 = 25147955) B25147955
theorem B22353737 : Blo 2067435 22353737 := bstep (se 2 (by rfl) ⟨8382651, by rfl⟩ : syracuseStep 22353737 = 16765303) B16765303
theorem B59609965 : Blo 2067435 59609965 := bstep (se 3 (by rfl) ⟨11176868, by rfl⟩ : syracuseStep 59609965 = 22353737) B22353737
theorem B79479953 : Blo 2067435 79479953 := bstep (se 2 (by rfl) ⟨29804982, by rfl⟩ : syracuseStep 79479953 = 59609965) B59609965
theorem B52986635 : Blo 2067435 52986635 := bstep (se 1 (by rfl) ⟨39739976, by rfl⟩ : syracuseStep 52986635 = 79479953) B79479953
theorem B35324423 : Blo 2067435 35324423 := bstep (se 1 (by rfl) ⟨26493317, by rfl⟩ : syracuseStep 35324423 = 52986635) B52986635
theorem B23549615 : Blo 2067435 23549615 := bstep (se 1 (by rfl) ⟨17662211, by rfl⟩ : syracuseStep 23549615 = 35324423) B35324423
theorem B15699743 : Blo 2067435 15699743 := bstep (se 1 (by rfl) ⟨11774807, by rfl⟩ : syracuseStep 15699743 = 23549615) B23549615
theorem B10466495 : Blo 2067435 10466495 := bstep (se 1 (by rfl) ⟨7849871, by rfl⟩ : syracuseStep 10466495 = 15699743) B15699743
theorem B6977663 : Blo 2067435 6977663 := bstep (se 1 (by rfl) ⟨5233247, by rfl⟩ : syracuseStep 6977663 = 10466495) B10466495
theorem B4651775 : Blo 2067435 4651775 := bstep (se 1 (by rfl) ⟨3488831, by rfl⟩ : syracuseStep 4651775 = 6977663) B6977663
theorem B3101183 : Blo 2067435 3101183 := bstep (se 1 (by rfl) ⟨2325887, by rfl⟩ : syracuseStep 3101183 = 4651775) B4651775
theorem B2067455 : Blo 2067435 2067455 := bstep (se 1 (by rfl) ⟨1550591, by rfl⟩ : syracuseStep 2067455 = 3101183) B3101183
theorem B3101189 : Blo 2067435 3101189 := bbase (se 4 (by rfl) ⟨290736, by rfl⟩ : syracuseStep 3101189 = 581473) (by norm_num)
theorem B2067459 : Blo 2067435 2067459 := bstep (se 1 (by rfl) ⟨1550594, by rfl⟩ : syracuseStep 2067459 = 3101189) B3101189
theorem B3488845 : Blo 2067435 3488845 := bbase (se 3 (by rfl) ⟨654158, by rfl⟩ : syracuseStep 3488845 = 1308317) (by norm_num)
theorem B4651793 : Blo 2067435 4651793 := bstep (se 2 (by rfl) ⟨1744422, by rfl⟩ : syracuseStep 4651793 = 3488845) B3488845
theorem B3101195 : Blo 2067435 3101195 := bstep (se 1 (by rfl) ⟨2325896, by rfl⟩ : syracuseStep 3101195 = 4651793) B4651793
theorem B2067463 : Blo 2067435 2067463 := bstep (se 1 (by rfl) ⟨1550597, by rfl⟩ : syracuseStep 2067463 = 3101195) B3101195
theorem B2325901 : Blo 2067435 2325901 := bbase (se 3 (by rfl) ⟨436106, by rfl⟩ : syracuseStep 2325901 = 872213) (by norm_num)
theorem B3101201 : Blo 2067435 3101201 := bstep (se 2 (by rfl) ⟨1162950, by rfl⟩ : syracuseStep 3101201 = 2325901) B2325901
theorem B2067467 : Blo 2067435 2067467 := bstep (se 1 (by rfl) ⟨1550600, by rfl⟩ : syracuseStep 2067467 = 3101201) B3101201
theorem B6977717 : Blo 2067435 6977717 := bbase (se 5 (by rfl) ⟨327080, by rfl⟩ : syracuseStep 6977717 = 654161) (by norm_num)
theorem B4651811 : Blo 2067435 4651811 := bstep (se 1 (by rfl) ⟨3488858, by rfl⟩ : syracuseStep 4651811 = 6977717) B6977717
theorem B3101207 : Blo 2067435 3101207 := bstep (se 1 (by rfl) ⟨2325905, by rfl⟩ : syracuseStep 3101207 = 4651811) B4651811
theorem B2067471 : Blo 2067435 2067471 := bstep (se 1 (by rfl) ⟨1550603, by rfl⟩ : syracuseStep 2067471 = 3101207) B3101207
theorem B3101213 : Blo 2067435 3101213 := bbase (se 3 (by rfl) ⟨581477, by rfl⟩ : syracuseStep 3101213 = 1162955) (by norm_num)
theorem B2067475 : Blo 2067435 2067475 := bstep (se 1 (by rfl) ⟨1550606, by rfl⟩ : syracuseStep 2067475 = 3101213) B3101213
theorem B4651829 : Blo 2067435 4651829 := bbase (se 5 (by rfl) ⟨218054, by rfl⟩ : syracuseStep 4651829 = 436109) (by norm_num)
theorem B3101219 : Blo 2067435 3101219 := bstep (se 1 (by rfl) ⟨2325914, by rfl⟩ : syracuseStep 3101219 = 4651829) B4651829
theorem B2067479 : Blo 2067435 2067479 := bstep (se 1 (by rfl) ⟨1550609, by rfl⟩ : syracuseStep 2067479 = 3101219) B3101219
theorem B2237929 : Blo 2067435 2237929 := bbase (se 2 (by rfl) ⟨839223, by rfl⟩ : syracuseStep 2237929 = 1678447) (by norm_num)
theorem B11935621 : Blo 2067435 11935621 := bstep (se 4 (by rfl) ⟨1118964, by rfl⟩ : syracuseStep 11935621 = 2237929) B2237929
theorem B15914161 : Blo 2067435 15914161 := bstep (se 2 (by rfl) ⟨5967810, by rfl⟩ : syracuseStep 15914161 = 11935621) B11935621
theorem B84875525 : Blo 2067435 84875525 := bstep (se 4 (by rfl) ⟨7957080, by rfl⟩ : syracuseStep 84875525 = 15914161) B15914161
theorem B56583683 : Blo 2067435 56583683 := bstep (se 1 (by rfl) ⟨42437762, by rfl⟩ : syracuseStep 56583683 = 84875525) B84875525
theorem B37722455 : Blo 2067435 37722455 := bstep (se 1 (by rfl) ⟨28291841, by rfl⟩ : syracuseStep 37722455 = 56583683) B56583683
theorem B25148303 : Blo 2067435 25148303 := bstep (se 1 (by rfl) ⟨18861227, by rfl⟩ : syracuseStep 25148303 = 37722455) B37722455
theorem B16765535 : Blo 2067435 16765535 := bstep (se 1 (by rfl) ⟨12574151, by rfl⟩ : syracuseStep 16765535 = 25148303) B25148303
theorem B11177023 : Blo 2067435 11177023 := bstep (se 1 (by rfl) ⟨8382767, by rfl⟩ : syracuseStep 11177023 = 16765535) B16765535
theorem B14902697 : Blo 2067435 14902697 := bstep (se 2 (by rfl) ⟨5588511, by rfl⟩ : syracuseStep 14902697 = 11177023) B11177023
theorem B9935131 : Blo 2067435 9935131 := bstep (se 1 (by rfl) ⟨7451348, by rfl⟩ : syracuseStep 9935131 = 14902697) B14902697
theorem B13246841 : Blo 2067435 13246841 := bstep (se 2 (by rfl) ⟨4967565, by rfl⟩ : syracuseStep 13246841 = 9935131) B9935131
theorem B8831227 : Blo 2067435 8831227 := bstep (se 1 (by rfl) ⟨6623420, by rfl⟩ : syracuseStep 8831227 = 13246841) B13246841
theorem B11774969 : Blo 2067435 11774969 := bstep (se 2 (by rfl) ⟨4415613, by rfl⟩ : syracuseStep 11774969 = 8831227) B8831227
theorem B7849979 : Blo 2067435 7849979 := bstep (se 1 (by rfl) ⟨5887484, by rfl⟩ : syracuseStep 7849979 = 11774969) B11774969
theorem B5233319 : Blo 2067435 5233319 := bstep (se 1 (by rfl) ⟨3924989, by rfl⟩ : syracuseStep 5233319 = 7849979) B7849979
theorem B3488879 : Blo 2067435 3488879 := bstep (se 1 (by rfl) ⟨2616659, by rfl⟩ : syracuseStep 3488879 = 5233319) B5233319
theorem B2325919 : Blo 2067435 2325919 := bstep (se 1 (by rfl) ⟨1744439, by rfl⟩ : syracuseStep 2325919 = 3488879) B3488879
theorem B3101225 : Blo 2067435 3101225 := bstep (se 2 (by rfl) ⟨1162959, by rfl⟩ : syracuseStep 3101225 = 2325919) B2325919
theorem B2067483 : Blo 2067435 2067483 := bstep (se 1 (by rfl) ⟨1550612, by rfl⟩ : syracuseStep 2067483 = 3101225) B3101225
theorem B2794261 : Blo 2067435 2794261 := bbase (se 6 (by rfl) ⟨65490, by rfl⟩ : syracuseStep 2794261 = 130981) (by norm_num)
theorem B3725681 : Blo 2067435 3725681 := bstep (se 2 (by rfl) ⟨1397130, by rfl⟩ : syracuseStep 3725681 = 2794261) B2794261
theorem B9935149 : Blo 2067435 9935149 := bstep (se 3 (by rfl) ⟨1862840, by rfl⟩ : syracuseStep 9935149 = 3725681) B3725681
theorem B13246865 : Blo 2067435 13246865 := bstep (se 2 (by rfl) ⟨4967574, by rfl⟩ : syracuseStep 13246865 = 9935149) B9935149
theorem B8831243 : Blo 2067435 8831243 := bstep (se 1 (by rfl) ⟨6623432, by rfl⟩ : syracuseStep 8831243 = 13246865) B13246865
theorem B5887495 : Blo 2067435 5887495 := bstep (se 1 (by rfl) ⟨4415621, by rfl⟩ : syracuseStep 5887495 = 8831243) B8831243
theorem B7849993 : Blo 2067435 7849993 := bstep (se 2 (by rfl) ⟨2943747, by rfl⟩ : syracuseStep 7849993 = 5887495) B5887495
theorem B10466657 : Blo 2067435 10466657 := bstep (se 2 (by rfl) ⟨3924996, by rfl⟩ : syracuseStep 10466657 = 7849993) B7849993
theorem B6977771 : Blo 2067435 6977771 := bstep (se 1 (by rfl) ⟨5233328, by rfl⟩ : syracuseStep 6977771 = 10466657) B10466657
theorem B4651847 : Blo 2067435 4651847 := bstep (se 1 (by rfl) ⟨3488885, by rfl⟩ : syracuseStep 4651847 = 6977771) B6977771
theorem B3101231 : Blo 2067435 3101231 := bstep (se 1 (by rfl) ⟨2325923, by rfl⟩ : syracuseStep 3101231 = 4651847) B4651847
theorem B2067487 : Blo 2067435 2067487 := bstep (se 1 (by rfl) ⟨1550615, by rfl⟩ : syracuseStep 2067487 = 3101231) B3101231
theorem B3101237 : Blo 2067435 3101237 := bbase (se 5 (by rfl) ⟨145370, by rfl⟩ : syracuseStep 3101237 = 290741) (by norm_num)
theorem B2067491 : Blo 2067435 2067491 := bstep (se 1 (by rfl) ⟨1550618, by rfl⟩ : syracuseStep 2067491 = 3101237) B3101237
theorem B5233349 : Blo 2067435 5233349 := bbase (se 4 (by rfl) ⟨490626, by rfl⟩ : syracuseStep 5233349 = 981253) (by norm_num)
theorem B3488899 : Blo 2067435 3488899 := bstep (se 1 (by rfl) ⟨2616674, by rfl⟩ : syracuseStep 3488899 = 5233349) B5233349
theorem B4651865 : Blo 2067435 4651865 := bstep (se 2 (by rfl) ⟨1744449, by rfl⟩ : syracuseStep 4651865 = 3488899) B3488899
theorem B3101243 : Blo 2067435 3101243 := bstep (se 1 (by rfl) ⟨2325932, by rfl⟩ : syracuseStep 3101243 = 4651865) B4651865
theorem B2067495 : Blo 2067435 2067495 := bstep (se 1 (by rfl) ⟨1550621, by rfl⟩ : syracuseStep 2067495 = 3101243) B3101243
theorem B2325937 : Blo 2067435 2325937 := bbase (se 2 (by rfl) ⟨872226, by rfl⟩ : syracuseStep 2325937 = 1744453) (by norm_num)
theorem B3101249 : Blo 2067435 3101249 := bstep (se 2 (by rfl) ⟨1162968, by rfl⟩ : syracuseStep 3101249 = 2325937) B2325937
theorem B2067499 : Blo 2067435 2067499 := bstep (se 1 (by rfl) ⟨1550624, by rfl⟩ : syracuseStep 2067499 = 3101249) B3101249
theorem B5887541 : Blo 2067435 5887541 := bbase (se 5 (by rfl) ⟨275978, by rfl⟩ : syracuseStep 5887541 = 551957) (by norm_num)
theorem B3925027 : Blo 2067435 3925027 := bstep (se 1 (by rfl) ⟨2943770, by rfl⟩ : syracuseStep 3925027 = 5887541) B5887541
theorem B5233369 : Blo 2067435 5233369 := bstep (se 2 (by rfl) ⟨1962513, by rfl⟩ : syracuseStep 5233369 = 3925027) B3925027
theorem B6977825 : Blo 2067435 6977825 := bstep (se 2 (by rfl) ⟨2616684, by rfl⟩ : syracuseStep 6977825 = 5233369) B5233369
theorem B4651883 : Blo 2067435 4651883 := bstep (se 1 (by rfl) ⟨3488912, by rfl⟩ : syracuseStep 4651883 = 6977825) B6977825
theorem B3101255 : Blo 2067435 3101255 := bstep (se 1 (by rfl) ⟨2325941, by rfl⟩ : syracuseStep 3101255 = 4651883) B4651883
theorem B2067503 : Blo 2067435 2067503 := bstep (se 1 (by rfl) ⟨1550627, by rfl⟩ : syracuseStep 2067503 = 3101255) B3101255
theorem B3101261 : Blo 2067435 3101261 := bbase (se 3 (by rfl) ⟨581486, by rfl⟩ : syracuseStep 3101261 = 1162973) (by norm_num)
theorem B2067507 : Blo 2067435 2067507 := bstep (se 1 (by rfl) ⟨1550630, by rfl⟩ : syracuseStep 2067507 = 3101261) B3101261
theorem B4651901 : Blo 2067435 4651901 := bbase (se 3 (by rfl) ⟨872231, by rfl⟩ : syracuseStep 4651901 = 1744463) (by norm_num)
theorem B3101267 : Blo 2067435 3101267 := bstep (se 1 (by rfl) ⟨2325950, by rfl⟩ : syracuseStep 3101267 = 4651901) B4651901
theorem B2067511 : Blo 2067435 2067511 := bstep (se 1 (by rfl) ⟨1550633, by rfl⟩ : syracuseStep 2067511 = 3101267) B3101267
theorem B3488933 : Blo 2067435 3488933 := bbase (se 4 (by rfl) ⟨327087, by rfl⟩ : syracuseStep 3488933 = 654175) (by norm_num)
theorem B2325955 : Blo 2067435 2325955 := bstep (se 1 (by rfl) ⟨1744466, by rfl⟩ : syracuseStep 2325955 = 3488933) B3488933
theorem B3101273 : Blo 2067435 3101273 := bstep (se 2 (by rfl) ⟨1162977, by rfl⟩ : syracuseStep 3101273 = 2325955) B2325955
theorem B2067515 : Blo 2067435 2067515 := bstep (se 1 (by rfl) ⟨1550636, by rfl⟩ : syracuseStep 2067515 = 3101273) B3101273
theorem B2207845 : Blo 2067435 2207845 := bbase (se 4 (by rfl) ⟨206985, by rfl⟩ : syracuseStep 2207845 = 413971) (by norm_num)
theorem B2943793 : Blo 2067435 2943793 := bstep (se 2 (by rfl) ⟨1103922, by rfl⟩ : syracuseStep 2943793 = 2207845) B2207845
theorem B15700229 : Blo 2067435 15700229 := bstep (se 4 (by rfl) ⟨1471896, by rfl⟩ : syracuseStep 15700229 = 2943793) B2943793
theorem B10466819 : Blo 2067435 10466819 := bstep (se 1 (by rfl) ⟨7850114, by rfl⟩ : syracuseStep 10466819 = 15700229) B15700229
theorem B6977879 : Blo 2067435 6977879 := bstep (se 1 (by rfl) ⟨5233409, by rfl⟩ : syracuseStep 6977879 = 10466819) B10466819
theorem B4651919 : Blo 2067435 4651919 := bstep (se 1 (by rfl) ⟨3488939, by rfl⟩ : syracuseStep 4651919 = 6977879) B6977879
theorem B3101279 : Blo 2067435 3101279 := bstep (se 1 (by rfl) ⟨2325959, by rfl⟩ : syracuseStep 3101279 = 4651919) B4651919
theorem B2067519 : Blo 2067435 2067519 := bstep (se 1 (by rfl) ⟨1550639, by rfl⟩ : syracuseStep 2067519 = 3101279) B3101279
theorem B3101285 : Blo 2067435 3101285 := bbase (se 4 (by rfl) ⟨290745, by rfl⟩ : syracuseStep 3101285 = 581491) (by norm_num)
theorem B2067523 : Blo 2067435 2067523 := bstep (se 1 (by rfl) ⟨1550642, by rfl⟩ : syracuseStep 2067523 = 3101285) B3101285
theorem B2943805 : Blo 2067435 2943805 := bbase (se 3 (by rfl) ⟨551963, by rfl⟩ : syracuseStep 2943805 = 1103927) (by norm_num)
theorem B3925073 : Blo 2067435 3925073 := bstep (se 2 (by rfl) ⟨1471902, by rfl⟩ : syracuseStep 3925073 = 2943805) B2943805
theorem B2616715 : Blo 2067435 2616715 := bstep (se 1 (by rfl) ⟨1962536, by rfl⟩ : syracuseStep 2616715 = 3925073) B3925073
theorem B3488953 : Blo 2067435 3488953 := bstep (se 2 (by rfl) ⟨1308357, by rfl⟩ : syracuseStep 3488953 = 2616715) B2616715
theorem B4651937 : Blo 2067435 4651937 := bstep (se 2 (by rfl) ⟨1744476, by rfl⟩ : syracuseStep 4651937 = 3488953) B3488953
theorem B3101291 : Blo 2067435 3101291 := bstep (se 1 (by rfl) ⟨2325968, by rfl⟩ : syracuseStep 3101291 = 4651937) B4651937
theorem B2067527 : Blo 2067435 2067527 := bstep (se 1 (by rfl) ⟨1550645, by rfl⟩ : syracuseStep 2067527 = 3101291) B3101291
theorem B2325973 : Blo 2067435 2325973 := bbase (se 7 (by rfl) ⟨27257, by rfl⟩ : syracuseStep 2325973 = 54515) (by norm_num)
theorem B3101297 : Blo 2067435 3101297 := bstep (se 2 (by rfl) ⟨1162986, by rfl⟩ : syracuseStep 3101297 = 2325973) B2325973
theorem B2067531 : Blo 2067435 2067531 := bstep (se 1 (by rfl) ⟨1550648, by rfl⟩ : syracuseStep 2067531 = 3101297) B3101297
theorem B2616725 : Blo 2067435 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B6977933 : Blo 2067435 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B4651955 : Blo 2067435 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B3101303 : Blo 2067435 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B2067535 : Blo 2067435 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B3101309 : Blo 2067435 3101309 := bbase (se 3 (by rfl) ⟨581495, by rfl⟩ : syracuseStep 3101309 = 1162991) (by norm_num)
theorem B2067539 : Blo 2067435 2067539 := bstep (se 1 (by rfl) ⟨1550654, by rfl⟩ : syracuseStep 2067539 = 3101309) B3101309
theorem B4651973 : Blo 2067435 4651973 := bbase (se 4 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 4651973 = 872245) (by norm_num)
theorem B3101315 : Blo 2067435 3101315 := bstep (se 1 (by rfl) ⟨2325986, by rfl⟩ : syracuseStep 3101315 = 4651973) B4651973
theorem B2067543 : Blo 2067435 2067543 := bstep (se 1 (by rfl) ⟨1550657, by rfl⟩ : syracuseStep 2067543 = 3101315) B3101315
theorem B3311813 : Blo 2067435 3311813 := bbase (se 4 (by rfl) ⟨310482, by rfl⟩ : syracuseStep 3311813 = 620965) (by norm_num)
theorem B8831501 : Blo 2067435 8831501 := bstep (se 3 (by rfl) ⟨1655906, by rfl⟩ : syracuseStep 8831501 = 3311813) B3311813
theorem B5887667 : Blo 2067435 5887667 := bstep (se 1 (by rfl) ⟨4415750, by rfl⟩ : syracuseStep 5887667 = 8831501) B8831501
theorem B3925111 : Blo 2067435 3925111 := bstep (se 1 (by rfl) ⟨2943833, by rfl⟩ : syracuseStep 3925111 = 5887667) B5887667
theorem B5233481 : Blo 2067435 5233481 := bstep (se 2 (by rfl) ⟨1962555, by rfl⟩ : syracuseStep 5233481 = 3925111) B3925111
theorem B3488987 : Blo 2067435 3488987 := bstep (se 1 (by rfl) ⟨2616740, by rfl⟩ : syracuseStep 3488987 = 5233481) B5233481
theorem B2325991 : Blo 2067435 2325991 := bstep (se 1 (by rfl) ⟨1744493, by rfl⟩ : syracuseStep 2325991 = 3488987) B3488987
theorem B3101321 : Blo 2067435 3101321 := bstep (se 2 (by rfl) ⟨1162995, by rfl⟩ : syracuseStep 3101321 = 2325991) B2325991
theorem B2067547 : Blo 2067435 2067547 := bstep (se 1 (by rfl) ⟨1550660, by rfl⟩ : syracuseStep 2067547 = 3101321) B3101321
theorem B10466981 : Blo 2067435 10466981 := bbase (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) (by norm_num)
theorem B6977987 : Blo 2067435 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B4651991 : Blo 2067435 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B3101327 : Blo 2067435 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B2067551 : Blo 2067435 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B3101333 : Blo 2067435 3101333 := bbase (se 6 (by rfl) ⟨72687, by rfl⟩ : syracuseStep 3101333 = 145375) (by norm_num)
theorem B2067555 : Blo 2067435 2067555 := bstep (se 1 (by rfl) ⟨1550666, by rfl⟩ : syracuseStep 2067555 = 3101333) B3101333
theorem B3143653 : Blo 2067435 3143653 := bbase (se 4 (by rfl) ⟨294717, by rfl⟩ : syracuseStep 3143653 = 589435) (by norm_num)
theorem B67064597 : Blo 2067435 67064597 := bstep (se 6 (by rfl) ⟨1571826, by rfl⟩ : syracuseStep 67064597 = 3143653) B3143653
theorem B44709731 : Blo 2067435 44709731 := bstep (se 1 (by rfl) ⟨33532298, by rfl⟩ : syracuseStep 44709731 = 67064597) B67064597
theorem B29806487 : Blo 2067435 29806487 := bstep (se 1 (by rfl) ⟨22354865, by rfl⟩ : syracuseStep 29806487 = 44709731) B44709731
theorem B19870991 : Blo 2067435 19870991 := bstep (se 1 (by rfl) ⟨14903243, by rfl⟩ : syracuseStep 19870991 = 29806487) B29806487
theorem B13247327 : Blo 2067435 13247327 := bstep (se 1 (by rfl) ⟨9935495, by rfl⟩ : syracuseStep 13247327 = 19870991) B19870991
theorem B8831551 : Blo 2067435 8831551 := bstep (se 1 (by rfl) ⟨6623663, by rfl⟩ : syracuseStep 8831551 = 13247327) B13247327
theorem B11775401 : Blo 2067435 11775401 := bstep (se 2 (by rfl) ⟨4415775, by rfl⟩ : syracuseStep 11775401 = 8831551) B8831551
theorem B7850267 : Blo 2067435 7850267 := bstep (se 1 (by rfl) ⟨5887700, by rfl⟩ : syracuseStep 7850267 = 11775401) B11775401
theorem B5233511 : Blo 2067435 5233511 := bstep (se 1 (by rfl) ⟨3925133, by rfl⟩ : syracuseStep 5233511 = 7850267) B7850267
theorem B3489007 : Blo 2067435 3489007 := bstep (se 1 (by rfl) ⟨2616755, by rfl⟩ : syracuseStep 3489007 = 5233511) B5233511
theorem B4652009 : Blo 2067435 4652009 := bstep (se 2 (by rfl) ⟨1744503, by rfl⟩ : syracuseStep 4652009 = 3489007) B3489007
theorem B3101339 : Blo 2067435 3101339 := bstep (se 1 (by rfl) ⟨2326004, by rfl⟩ : syracuseStep 3101339 = 4652009) B4652009
theorem B2067559 : Blo 2067435 2067559 := bstep (se 1 (by rfl) ⟨1550669, by rfl⟩ : syracuseStep 2067559 = 3101339) B3101339
theorem B2326009 : Blo 2067435 2326009 := bbase (se 2 (by rfl) ⟨872253, by rfl⟩ : syracuseStep 2326009 = 1744507) (by norm_num)
theorem B3101345 : Blo 2067435 3101345 := bstep (se 2 (by rfl) ⟨1163004, by rfl⟩ : syracuseStep 3101345 = 2326009) B2326009
theorem B2067563 : Blo 2067435 2067563 := bstep (se 1 (by rfl) ⟨1550672, by rfl⟩ : syracuseStep 2067563 = 3101345) B3101345
theorem B2095777 : Blo 2067435 2095777 := bbase (se 2 (by rfl) ⟨785916, by rfl⟩ : syracuseStep 2095777 = 1571833) (by norm_num)
theorem B11177477 : Blo 2067435 11177477 := bstep (se 4 (by rfl) ⟨1047888, by rfl⟩ : syracuseStep 11177477 = 2095777) B2095777
theorem B7451651 : Blo 2067435 7451651 := bstep (se 1 (by rfl) ⟨5588738, by rfl⟩ : syracuseStep 7451651 = 11177477) B11177477
theorem B4967767 : Blo 2067435 4967767 := bstep (se 1 (by rfl) ⟨3725825, by rfl⟩ : syracuseStep 4967767 = 7451651) B7451651
theorem B6623689 : Blo 2067435 6623689 := bstep (se 2 (by rfl) ⟨2483883, by rfl⟩ : syracuseStep 6623689 = 4967767) B4967767
theorem B8831585 : Blo 2067435 8831585 := bstep (se 2 (by rfl) ⟨3311844, by rfl⟩ : syracuseStep 8831585 = 6623689) B6623689
theorem B5887723 : Blo 2067435 5887723 := bstep (se 1 (by rfl) ⟨4415792, by rfl⟩ : syracuseStep 5887723 = 8831585) B8831585
theorem B7850297 : Blo 2067435 7850297 := bstep (se 2 (by rfl) ⟨2943861, by rfl⟩ : syracuseStep 7850297 = 5887723) B5887723
theorem B5233531 : Blo 2067435 5233531 := bstep (se 1 (by rfl) ⟨3925148, by rfl⟩ : syracuseStep 5233531 = 7850297) B7850297
theorem B6978041 : Blo 2067435 6978041 := bstep (se 2 (by rfl) ⟨2616765, by rfl⟩ : syracuseStep 6978041 = 5233531) B5233531
theorem B4652027 : Blo 2067435 4652027 := bstep (se 1 (by rfl) ⟨3489020, by rfl⟩ : syracuseStep 4652027 = 6978041) B6978041
theorem B3101351 : Blo 2067435 3101351 := bstep (se 1 (by rfl) ⟨2326013, by rfl⟩ : syracuseStep 3101351 = 4652027) B4652027
theorem B2067567 : Blo 2067435 2067567 := bstep (se 1 (by rfl) ⟨1550675, by rfl⟩ : syracuseStep 2067567 = 3101351) B3101351
theorem B3101357 : Blo 2067435 3101357 := bbase (se 3 (by rfl) ⟨581504, by rfl⟩ : syracuseStep 3101357 = 1163009) (by norm_num)
theorem B2067571 : Blo 2067435 2067571 := bstep (se 1 (by rfl) ⟨1550678, by rfl⟩ : syracuseStep 2067571 = 3101357) B3101357
theorem B4652045 : Blo 2067435 4652045 := bbase (se 3 (by rfl) ⟨872258, by rfl⟩ : syracuseStep 4652045 = 1744517) (by norm_num)
theorem B3101363 : Blo 2067435 3101363 := bstep (se 1 (by rfl) ⟨2326022, by rfl⟩ : syracuseStep 3101363 = 4652045) B4652045
theorem B2067575 : Blo 2067435 2067575 := bstep (se 1 (by rfl) ⟨1550681, by rfl⟩ : syracuseStep 2067575 = 3101363) B3101363
theorem B2616781 : Blo 2067435 2616781 := bbase (se 3 (by rfl) ⟨490646, by rfl⟩ : syracuseStep 2616781 = 981293) (by norm_num)
theorem B3489041 : Blo 2067435 3489041 := bstep (se 2 (by rfl) ⟨1308390, by rfl⟩ : syracuseStep 3489041 = 2616781) B2616781
theorem B2326027 : Blo 2067435 2326027 := bstep (se 1 (by rfl) ⟨1744520, by rfl⟩ : syracuseStep 2326027 = 3489041) B3489041
theorem B3101369 : Blo 2067435 3101369 := bstep (se 2 (by rfl) ⟨1163013, by rfl⟩ : syracuseStep 3101369 = 2326027) B2326027
theorem B2067579 : Blo 2067435 2067579 := bstep (se 1 (by rfl) ⟨1550684, by rfl⟩ : syracuseStep 2067579 = 3101369) B3101369
theorem B3978733 : Blo 2067435 3978733 := bbase (se 3 (by rfl) ⟨746012, by rfl⟩ : syracuseStep 3978733 = 1492025) (by norm_num)
theorem B5304977 : Blo 2067435 5304977 := bstep (se 2 (by rfl) ⟨1989366, by rfl⟩ : syracuseStep 5304977 = 3978733) B3978733
theorem B3536651 : Blo 2067435 3536651 := bstep (se 1 (by rfl) ⟨2652488, by rfl⟩ : syracuseStep 3536651 = 5304977) B5304977
theorem B2357767 : Blo 2067435 2357767 := bstep (se 1 (by rfl) ⟨1768325, by rfl⟩ : syracuseStep 2357767 = 3536651) B3536651
theorem B12574757 : Blo 2067435 12574757 := bstep (se 4 (by rfl) ⟨1178883, by rfl⟩ : syracuseStep 12574757 = 2357767) B2357767
theorem B8383171 : Blo 2067435 8383171 := bstep (se 1 (by rfl) ⟨6287378, by rfl⟩ : syracuseStep 8383171 = 12574757) B12574757
theorem B11177561 : Blo 2067435 11177561 := bstep (se 2 (by rfl) ⟨4191585, by rfl⟩ : syracuseStep 11177561 = 8383171) B8383171
theorem B29806829 : Blo 2067435 29806829 := bstep (se 3 (by rfl) ⟨5588780, by rfl⟩ : syracuseStep 29806829 = 11177561) B11177561
theorem B19871219 : Blo 2067435 19871219 := bstep (se 1 (by rfl) ⟨14903414, by rfl⟩ : syracuseStep 19871219 = 29806829) B29806829
theorem B13247479 : Blo 2067435 13247479 := bstep (se 1 (by rfl) ⟨9935609, by rfl⟩ : syracuseStep 13247479 = 19871219) B19871219
theorem B17663305 : Blo 2067435 17663305 := bstep (se 2 (by rfl) ⟨6623739, by rfl⟩ : syracuseStep 17663305 = 13247479) B13247479
theorem B23551073 : Blo 2067435 23551073 := bstep (se 2 (by rfl) ⟨8831652, by rfl⟩ : syracuseStep 23551073 = 17663305) B17663305
theorem B15700715 : Blo 2067435 15700715 := bstep (se 1 (by rfl) ⟨11775536, by rfl⟩ : syracuseStep 15700715 = 23551073) B23551073
theorem B10467143 : Blo 2067435 10467143 := bstep (se 1 (by rfl) ⟨7850357, by rfl⟩ : syracuseStep 10467143 = 15700715) B15700715
theorem B6978095 : Blo 2067435 6978095 := bstep (se 1 (by rfl) ⟨5233571, by rfl⟩ : syracuseStep 6978095 = 10467143) B10467143
theorem B4652063 : Blo 2067435 4652063 := bstep (se 1 (by rfl) ⟨3489047, by rfl⟩ : syracuseStep 4652063 = 6978095) B6978095
theorem B3101375 : Blo 2067435 3101375 := bstep (se 1 (by rfl) ⟨2326031, by rfl⟩ : syracuseStep 3101375 = 4652063) B4652063
theorem B2067583 : Blo 2067435 2067583 := bstep (se 1 (by rfl) ⟨1550687, by rfl⟩ : syracuseStep 2067583 = 3101375) B3101375
theorem B3101381 : Blo 2067435 3101381 := bbase (se 4 (by rfl) ⟨290754, by rfl⟩ : syracuseStep 3101381 = 581509) (by norm_num)
theorem B2067587 : Blo 2067435 2067587 := bstep (se 1 (by rfl) ⟨1550690, by rfl⟩ : syracuseStep 2067587 = 3101381) B3101381
theorem B3489061 : Blo 2067435 3489061 := bbase (se 4 (by rfl) ⟨327099, by rfl⟩ : syracuseStep 3489061 = 654199) (by norm_num)
theorem B4652081 : Blo 2067435 4652081 := bstep (se 2 (by rfl) ⟨1744530, by rfl⟩ : syracuseStep 4652081 = 3489061) B3489061
theorem B3101387 : Blo 2067435 3101387 := bstep (se 1 (by rfl) ⟨2326040, by rfl⟩ : syracuseStep 3101387 = 4652081) B4652081
theorem B2067591 : Blo 2067435 2067591 := bstep (se 1 (by rfl) ⟨1550693, by rfl⟩ : syracuseStep 2067591 = 3101387) B3101387
theorem B2326045 : Blo 2067435 2326045 := bbase (se 3 (by rfl) ⟨436133, by rfl⟩ : syracuseStep 2326045 = 872267) (by norm_num)
theorem B3101393 : Blo 2067435 3101393 := bstep (se 2 (by rfl) ⟨1163022, by rfl⟩ : syracuseStep 3101393 = 2326045) B2326045
theorem B2067595 : Blo 2067435 2067595 := bstep (se 1 (by rfl) ⟨1550696, by rfl⟩ : syracuseStep 2067595 = 3101393) B3101393
theorem B6978149 : Blo 2067435 6978149 := bbase (se 4 (by rfl) ⟨654201, by rfl⟩ : syracuseStep 6978149 = 1308403) (by norm_num)
theorem B4652099 : Blo 2067435 4652099 := bstep (se 1 (by rfl) ⟨3489074, by rfl⟩ : syracuseStep 4652099 = 6978149) B6978149
theorem B3101399 : Blo 2067435 3101399 := bstep (se 1 (by rfl) ⟨2326049, by rfl⟩ : syracuseStep 3101399 = 4652099) B4652099
theorem B2067599 : Blo 2067435 2067599 := bstep (se 1 (by rfl) ⟨1550699, by rfl⟩ : syracuseStep 2067599 = 3101399) B3101399
theorem B3101405 : Blo 2067435 3101405 := bbase (se 3 (by rfl) ⟨581513, by rfl⟩ : syracuseStep 3101405 = 1163027) (by norm_num)
theorem B2067603 : Blo 2067435 2067603 := bstep (se 1 (by rfl) ⟨1550702, by rfl⟩ : syracuseStep 2067603 = 3101405) B3101405
theorem B4652117 : Blo 2067435 4652117 := bbase (se 8 (by rfl) ⟨27258, by rfl⟩ : syracuseStep 4652117 = 54517) (by norm_num)
theorem B3101411 : Blo 2067435 3101411 := bstep (se 1 (by rfl) ⟨2326058, by rfl⟩ : syracuseStep 3101411 = 4652117) B4652117
theorem B2067607 : Blo 2067435 2067607 := bstep (se 1 (by rfl) ⟨1550705, by rfl⟩ : syracuseStep 2067607 = 3101411) B3101411
theorem B2794429 : Blo 2067435 2794429 := bbase (se 3 (by rfl) ⟨523955, by rfl⟩ : syracuseStep 2794429 = 1047911) (by norm_num)
theorem B14903621 : Blo 2067435 14903621 := bstep (se 4 (by rfl) ⟨1397214, by rfl⟩ : syracuseStep 14903621 = 2794429) B2794429
theorem B9935747 : Blo 2067435 9935747 := bstep (se 1 (by rfl) ⟨7451810, by rfl⟩ : syracuseStep 9935747 = 14903621) B14903621
theorem B6623831 : Blo 2067435 6623831 := bstep (se 1 (by rfl) ⟨4967873, by rfl⟩ : syracuseStep 6623831 = 9935747) B9935747
theorem B4415887 : Blo 2067435 4415887 := bstep (se 1 (by rfl) ⟨3311915, by rfl⟩ : syracuseStep 4415887 = 6623831) B6623831
theorem B5887849 : Blo 2067435 5887849 := bstep (se 2 (by rfl) ⟨2207943, by rfl⟩ : syracuseStep 5887849 = 4415887) B4415887
theorem B7850465 : Blo 2067435 7850465 := bstep (se 2 (by rfl) ⟨2943924, by rfl⟩ : syracuseStep 7850465 = 5887849) B5887849
theorem B5233643 : Blo 2067435 5233643 := bstep (se 1 (by rfl) ⟨3925232, by rfl⟩ : syracuseStep 5233643 = 7850465) B7850465
theorem B3489095 : Blo 2067435 3489095 := bstep (se 1 (by rfl) ⟨2616821, by rfl⟩ : syracuseStep 3489095 = 5233643) B5233643
theorem B2326063 : Blo 2067435 2326063 := bstep (se 1 (by rfl) ⟨1744547, by rfl⟩ : syracuseStep 2326063 = 3489095) B3489095
theorem B3101417 : Blo 2067435 3101417 := bstep (se 2 (by rfl) ⟨1163031, by rfl⟩ : syracuseStep 3101417 = 2326063) B2326063
theorem B2067611 : Blo 2067435 2067611 := bstep (se 1 (by rfl) ⟨1550708, by rfl⟩ : syracuseStep 2067611 = 3101417) B3101417
theorem B5035661 : Blo 2067435 5035661 := bbase (se 3 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 5035661 = 1888373) (by norm_num)
theorem B3357107 : Blo 2067435 3357107 := bstep (se 1 (by rfl) ⟨2517830, by rfl⟩ : syracuseStep 3357107 = 5035661) B5035661
theorem B35809141 : Blo 2067435 35809141 := bstep (se 5 (by rfl) ⟨1678553, by rfl⟩ : syracuseStep 35809141 = 3357107) B3357107
theorem B47745521 : Blo 2067435 47745521 := bstep (se 2 (by rfl) ⟨17904570, by rfl⟩ : syracuseStep 47745521 = 35809141) B35809141
theorem B31830347 : Blo 2067435 31830347 := bstep (se 1 (by rfl) ⟨23872760, by rfl⟩ : syracuseStep 31830347 = 47745521) B47745521
theorem B21220231 : Blo 2067435 21220231 := bstep (se 1 (by rfl) ⟨15915173, by rfl⟩ : syracuseStep 21220231 = 31830347) B31830347
theorem B28293641 : Blo 2067435 28293641 := bstep (se 2 (by rfl) ⟨10610115, by rfl⟩ : syracuseStep 28293641 = 21220231) B21220231
theorem B18862427 : Blo 2067435 18862427 := bstep (se 1 (by rfl) ⟨14146820, by rfl⟩ : syracuseStep 18862427 = 28293641) B28293641
theorem B50299805 : Blo 2067435 50299805 := bstep (se 3 (by rfl) ⟨9431213, by rfl⟩ : syracuseStep 50299805 = 18862427) B18862427
theorem B33533203 : Blo 2067435 33533203 := bstep (se 1 (by rfl) ⟨25149902, by rfl⟩ : syracuseStep 33533203 = 50299805) B50299805
theorem B44710937 : Blo 2067435 44710937 := bstep (se 2 (by rfl) ⟨16766601, by rfl⟩ : syracuseStep 44710937 = 33533203) B33533203
theorem B29807291 : Blo 2067435 29807291 := bstep (se 1 (by rfl) ⟨22355468, by rfl⟩ : syracuseStep 29807291 = 44710937) B44710937
theorem B19871527 : Blo 2067435 19871527 := bstep (se 1 (by rfl) ⟨14903645, by rfl⟩ : syracuseStep 19871527 = 29807291) B29807291
theorem B26495369 : Blo 2067435 26495369 := bstep (se 2 (by rfl) ⟨9935763, by rfl⟩ : syracuseStep 26495369 = 19871527) B19871527
theorem B17663579 : Blo 2067435 17663579 := bstep (se 1 (by rfl) ⟨13247684, by rfl⟩ : syracuseStep 17663579 = 26495369) B26495369
theorem B11775719 : Blo 2067435 11775719 := bstep (se 1 (by rfl) ⟨8831789, by rfl⟩ : syracuseStep 11775719 = 17663579) B17663579
theorem B7850479 : Blo 2067435 7850479 := bstep (se 1 (by rfl) ⟨5887859, by rfl⟩ : syracuseStep 7850479 = 11775719) B11775719
theorem B10467305 : Blo 2067435 10467305 := bstep (se 2 (by rfl) ⟨3925239, by rfl⟩ : syracuseStep 10467305 = 7850479) B7850479
theorem B6978203 : Blo 2067435 6978203 := bstep (se 1 (by rfl) ⟨5233652, by rfl⟩ : syracuseStep 6978203 = 10467305) B10467305
theorem B4652135 : Blo 2067435 4652135 := bstep (se 1 (by rfl) ⟨3489101, by rfl⟩ : syracuseStep 4652135 = 6978203) B6978203
theorem B3101423 : Blo 2067435 3101423 := bstep (se 1 (by rfl) ⟨2326067, by rfl⟩ : syracuseStep 3101423 = 4652135) B4652135
theorem B2067615 : Blo 2067435 2067615 := bstep (se 1 (by rfl) ⟨1550711, by rfl⟩ : syracuseStep 2067615 = 3101423) B3101423
theorem B3101429 : Blo 2067435 3101429 := bbase (se 5 (by rfl) ⟨145379, by rfl⟩ : syracuseStep 3101429 = 290759) (by norm_num)
theorem B2067619 : Blo 2067435 2067619 := bstep (se 1 (by rfl) ⟨1550714, by rfl⟩ : syracuseStep 2067619 = 3101429) B3101429
theorem B6714245 : Blo 2067435 6714245 := bbase (se 4 (by rfl) ⟨629460, by rfl⟩ : syracuseStep 6714245 = 1258921) (by norm_num)
theorem B4476163 : Blo 2067435 4476163 := bstep (se 1 (by rfl) ⟨3357122, by rfl⟩ : syracuseStep 4476163 = 6714245) B6714245
theorem B5968217 : Blo 2067435 5968217 := bstep (se 2 (by rfl) ⟨2238081, by rfl⟩ : syracuseStep 5968217 = 4476163) B4476163
theorem B3978811 : Blo 2067435 3978811 := bstep (se 1 (by rfl) ⟨2984108, by rfl⟩ : syracuseStep 3978811 = 5968217) B5968217
theorem B21220325 : Blo 2067435 21220325 := bstep (se 4 (by rfl) ⟨1989405, by rfl⟩ : syracuseStep 21220325 = 3978811) B3978811
theorem B14146883 : Blo 2067435 14146883 := bstep (se 1 (by rfl) ⟨10610162, by rfl⟩ : syracuseStep 14146883 = 21220325) B21220325
theorem B9431255 : Blo 2067435 9431255 := bstep (se 1 (by rfl) ⟨7073441, by rfl⟩ : syracuseStep 9431255 = 14146883) B14146883
theorem B6287503 : Blo 2067435 6287503 := bstep (se 1 (by rfl) ⟨4715627, by rfl⟩ : syracuseStep 6287503 = 9431255) B9431255
theorem B8383337 : Blo 2067435 8383337 := bstep (se 2 (by rfl) ⟨3143751, by rfl⟩ : syracuseStep 8383337 = 6287503) B6287503
theorem B5588891 : Blo 2067435 5588891 := bstep (se 1 (by rfl) ⟨4191668, by rfl⟩ : syracuseStep 5588891 = 8383337) B8383337
theorem B3725927 : Blo 2067435 3725927 := bstep (se 1 (by rfl) ⟨2794445, by rfl⟩ : syracuseStep 3725927 = 5588891) B5588891
theorem B2483951 : Blo 2067435 2483951 := bstep (se 1 (by rfl) ⟨1862963, by rfl⟩ : syracuseStep 2483951 = 3725927) B3725927
theorem B6623869 : Blo 2067435 6623869 := bstep (se 3 (by rfl) ⟨1241975, by rfl⟩ : syracuseStep 6623869 = 2483951) B2483951
theorem B8831825 : Blo 2067435 8831825 := bstep (se 2 (by rfl) ⟨3311934, by rfl⟩ : syracuseStep 8831825 = 6623869) B6623869
theorem B5887883 : Blo 2067435 5887883 := bstep (se 1 (by rfl) ⟨4415912, by rfl⟩ : syracuseStep 5887883 = 8831825) B8831825
theorem B3925255 : Blo 2067435 3925255 := bstep (se 1 (by rfl) ⟨2943941, by rfl⟩ : syracuseStep 3925255 = 5887883) B5887883
theorem B5233673 : Blo 2067435 5233673 := bstep (se 2 (by rfl) ⟨1962627, by rfl⟩ : syracuseStep 5233673 = 3925255) B3925255
theorem B3489115 : Blo 2067435 3489115 := bstep (se 1 (by rfl) ⟨2616836, by rfl⟩ : syracuseStep 3489115 = 5233673) B5233673
theorem B4652153 : Blo 2067435 4652153 := bstep (se 2 (by rfl) ⟨1744557, by rfl⟩ : syracuseStep 4652153 = 3489115) B3489115
theorem B3101435 : Blo 2067435 3101435 := bstep (se 1 (by rfl) ⟨2326076, by rfl⟩ : syracuseStep 3101435 = 4652153) B4652153
theorem B2067623 : Blo 2067435 2067623 := bstep (se 1 (by rfl) ⟨1550717, by rfl⟩ : syracuseStep 2067623 = 3101435) B3101435
theorem B2326081 : Blo 2067435 2326081 := bbase (se 2 (by rfl) ⟨872280, by rfl⟩ : syracuseStep 2326081 = 1744561) (by norm_num)
theorem B3101441 : Blo 2067435 3101441 := bstep (se 2 (by rfl) ⟨1163040, by rfl⟩ : syracuseStep 3101441 = 2326081) B2326081
theorem B2067627 : Blo 2067435 2067627 := bstep (se 1 (by rfl) ⟨1550720, by rfl⟩ : syracuseStep 2067627 = 3101441) B3101441
theorem B5233693 : Blo 2067435 5233693 := bbase (se 3 (by rfl) ⟨981317, by rfl⟩ : syracuseStep 5233693 = 1962635) (by norm_num)
theorem B6978257 : Blo 2067435 6978257 := bstep (se 2 (by rfl) ⟨2616846, by rfl⟩ : syracuseStep 6978257 = 5233693) B5233693
theorem B4652171 : Blo 2067435 4652171 := bstep (se 1 (by rfl) ⟨3489128, by rfl⟩ : syracuseStep 4652171 = 6978257) B6978257
theorem B3101447 : Blo 2067435 3101447 := bstep (se 1 (by rfl) ⟨2326085, by rfl⟩ : syracuseStep 3101447 = 4652171) B4652171
theorem B2067631 : Blo 2067435 2067631 := bstep (se 1 (by rfl) ⟨1550723, by rfl⟩ : syracuseStep 2067631 = 3101447) B3101447
theorem B3101453 : Blo 2067435 3101453 := bbase (se 3 (by rfl) ⟨581522, by rfl⟩ : syracuseStep 3101453 = 1163045) (by norm_num)
theorem B2067635 : Blo 2067435 2067635 := bstep (se 1 (by rfl) ⟨1550726, by rfl⟩ : syracuseStep 2067635 = 3101453) B3101453
theorem B4652189 : Blo 2067435 4652189 := bbase (se 3 (by rfl) ⟨872285, by rfl⟩ : syracuseStep 4652189 = 1744571) (by norm_num)
theorem B3101459 : Blo 2067435 3101459 := bstep (se 1 (by rfl) ⟨2326094, by rfl⟩ : syracuseStep 3101459 = 4652189) B4652189
theorem B2067639 : Blo 2067435 2067639 := bstep (se 1 (by rfl) ⟨1550729, by rfl⟩ : syracuseStep 2067639 = 3101459) B3101459
theorem B3489149 : Blo 2067435 3489149 := bbase (se 3 (by rfl) ⟨654215, by rfl⟩ : syracuseStep 3489149 = 1308431) (by norm_num)
theorem B2326099 : Blo 2067435 2326099 := bstep (se 1 (by rfl) ⟨1744574, by rfl⟩ : syracuseStep 2326099 = 3489149) B3489149
theorem B3101465 : Blo 2067435 3101465 := bstep (se 2 (by rfl) ⟨1163049, by rfl⟩ : syracuseStep 3101465 = 2326099) B2326099
theorem B2067643 : Blo 2067435 2067643 := bstep (se 1 (by rfl) ⟨1550732, by rfl⟩ : syracuseStep 2067643 = 3101465) B3101465
theorem B11177909 : Blo 2067435 11177909 := bbase (se 5 (by rfl) ⟨523964, by rfl⟩ : syracuseStep 11177909 = 1047929) (by norm_num)
theorem B7451939 : Blo 2067435 7451939 := bstep (se 1 (by rfl) ⟨5588954, by rfl⟩ : syracuseStep 7451939 = 11177909) B11177909
theorem B4967959 : Blo 2067435 4967959 := bstep (se 1 (by rfl) ⟨3725969, by rfl⟩ : syracuseStep 4967959 = 7451939) B7451939
theorem B6623945 : Blo 2067435 6623945 := bstep (se 2 (by rfl) ⟨2483979, by rfl⟩ : syracuseStep 6623945 = 4967959) B4967959
theorem B4415963 : Blo 2067435 4415963 := bstep (se 1 (by rfl) ⟨3311972, by rfl⟩ : syracuseStep 4415963 = 6623945) B6623945
theorem B11775901 : Blo 2067435 11775901 := bstep (se 3 (by rfl) ⟨2207981, by rfl⟩ : syracuseStep 11775901 = 4415963) B4415963
theorem B15701201 : Blo 2067435 15701201 := bstep (se 2 (by rfl) ⟨5887950, by rfl⟩ : syracuseStep 15701201 = 11775901) B11775901
theorem B10467467 : Blo 2067435 10467467 := bstep (se 1 (by rfl) ⟨7850600, by rfl⟩ : syracuseStep 10467467 = 15701201) B15701201
theorem B6978311 : Blo 2067435 6978311 := bstep (se 1 (by rfl) ⟨5233733, by rfl⟩ : syracuseStep 6978311 = 10467467) B10467467
theorem B4652207 : Blo 2067435 4652207 := bstep (se 1 (by rfl) ⟨3489155, by rfl⟩ : syracuseStep 4652207 = 6978311) B6978311
theorem B3101471 : Blo 2067435 3101471 := bstep (se 1 (by rfl) ⟨2326103, by rfl⟩ : syracuseStep 3101471 = 4652207) B4652207
theorem B2067647 : Blo 2067435 2067647 := bstep (se 1 (by rfl) ⟨1550735, by rfl⟩ : syracuseStep 2067647 = 3101471) B3101471
theorem B3101477 : Blo 2067435 3101477 := bbase (se 4 (by rfl) ⟨290763, by rfl⟩ : syracuseStep 3101477 = 581527) (by norm_num)
theorem B2067651 : Blo 2067435 2067651 := bstep (se 1 (by rfl) ⟨1550738, by rfl⟩ : syracuseStep 2067651 = 3101477) B3101477
theorem B2616877 : Blo 2067435 2616877 := bbase (se 3 (by rfl) ⟨490664, by rfl⟩ : syracuseStep 2616877 = 981329) (by norm_num)
theorem B3489169 : Blo 2067435 3489169 := bstep (se 2 (by rfl) ⟨1308438, by rfl⟩ : syracuseStep 3489169 = 2616877) B2616877
theorem B4652225 : Blo 2067435 4652225 := bstep (se 2 (by rfl) ⟨1744584, by rfl⟩ : syracuseStep 4652225 = 3489169) B3489169
theorem B3101483 : Blo 2067435 3101483 := bstep (se 1 (by rfl) ⟨2326112, by rfl⟩ : syracuseStep 3101483 = 4652225) B4652225
theorem B2067655 : Blo 2067435 2067655 := bstep (se 1 (by rfl) ⟨1550741, by rfl⟩ : syracuseStep 2067655 = 3101483) B3101483
theorem B2326117 : Blo 2067435 2326117 := bbase (se 4 (by rfl) ⟨218073, by rfl⟩ : syracuseStep 2326117 = 436147) (by norm_num)
theorem B3101489 : Blo 2067435 3101489 := bstep (se 2 (by rfl) ⟨1163058, by rfl⟩ : syracuseStep 3101489 = 2326117) B2326117
theorem B2067659 : Blo 2067435 2067659 := bstep (se 1 (by rfl) ⟨1550744, by rfl⟩ : syracuseStep 2067659 = 3101489) B3101489
theorem B3536789 : Blo 2067435 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B37725749 : Blo 2067435 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B25150499 : Blo 2067435 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B16766999 : Blo 2067435 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B11177999 : Blo 2067435 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B7451999 : Blo 2067435 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B4967999 : Blo 2067435 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B3311999 : Blo 2067435 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2207999 : Blo 2067435 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B5887997 : Blo 2067435 5887997 := bstep (se 3 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 5887997 = 2207999) B2207999
theorem B3925331 : Blo 2067435 3925331 := bstep (se 1 (by rfl) ⟨2943998, by rfl⟩ : syracuseStep 3925331 = 5887997) B5887997
theorem B2616887 : Blo 2067435 2616887 := bstep (se 1 (by rfl) ⟨1962665, by rfl⟩ : syracuseStep 2616887 = 3925331) B3925331
theorem B6978365 : Blo 2067435 6978365 := bstep (se 3 (by rfl) ⟨1308443, by rfl⟩ : syracuseStep 6978365 = 2616887) B2616887
theorem B4652243 : Blo 2067435 4652243 := bstep (se 1 (by rfl) ⟨3489182, by rfl⟩ : syracuseStep 4652243 = 6978365) B6978365
theorem B3101495 : Blo 2067435 3101495 := bstep (se 1 (by rfl) ⟨2326121, by rfl⟩ : syracuseStep 3101495 = 4652243) B4652243
theorem B2067663 : Blo 2067435 2067663 := bstep (se 1 (by rfl) ⟨1550747, by rfl⟩ : syracuseStep 2067663 = 3101495) B3101495
theorem B3101501 : Blo 2067435 3101501 := bbase (se 3 (by rfl) ⟨581531, by rfl⟩ : syracuseStep 3101501 = 1163063) (by norm_num)
theorem B2067667 : Blo 2067435 2067667 := bstep (se 1 (by rfl) ⟨1550750, by rfl⟩ : syracuseStep 2067667 = 3101501) B3101501
theorem B4652261 : Blo 2067435 4652261 := bbase (se 4 (by rfl) ⟨436149, by rfl⟩ : syracuseStep 4652261 = 872299) (by norm_num)
theorem B3101507 : Blo 2067435 3101507 := bstep (se 1 (by rfl) ⟨2326130, by rfl⟩ : syracuseStep 3101507 = 4652261) B4652261
theorem B2067671 : Blo 2067435 2067671 := bstep (se 1 (by rfl) ⟨1550753, by rfl⟩ : syracuseStep 2067671 = 3101507) B3101507
theorem B5233805 : Blo 2067435 5233805 := bbase (se 3 (by rfl) ⟨981338, by rfl⟩ : syracuseStep 5233805 = 1962677) (by norm_num)
theorem B3489203 : Blo 2067435 3489203 := bstep (se 1 (by rfl) ⟨2616902, by rfl⟩ : syracuseStep 3489203 = 5233805) B5233805
theorem B2326135 : Blo 2067435 2326135 := bstep (se 1 (by rfl) ⟨1744601, by rfl⟩ : syracuseStep 2326135 = 3489203) B3489203
theorem B3101513 : Blo 2067435 3101513 := bstep (se 2 (by rfl) ⟨1163067, by rfl⟩ : syracuseStep 3101513 = 2326135) B2326135
theorem B2067675 : Blo 2067435 2067675 := bstep (se 1 (by rfl) ⟨1550756, by rfl⟩ : syracuseStep 2067675 = 3101513) B3101513
theorem B2944021 : Blo 2067435 2944021 := bbase (se 6 (by rfl) ⟨69000, by rfl⟩ : syracuseStep 2944021 = 138001) (by norm_num)
theorem B3925361 : Blo 2067435 3925361 := bstep (se 2 (by rfl) ⟨1472010, by rfl⟩ : syracuseStep 3925361 = 2944021) B2944021
theorem B10467629 : Blo 2067435 10467629 := bstep (se 3 (by rfl) ⟨1962680, by rfl⟩ : syracuseStep 10467629 = 3925361) B3925361
theorem B6978419 : Blo 2067435 6978419 := bstep (se 1 (by rfl) ⟨5233814, by rfl⟩ : syracuseStep 6978419 = 10467629) B10467629
theorem B4652279 : Blo 2067435 4652279 := bstep (se 1 (by rfl) ⟨3489209, by rfl⟩ : syracuseStep 4652279 = 6978419) B6978419
theorem B3101519 : Blo 2067435 3101519 := bstep (se 1 (by rfl) ⟨2326139, by rfl⟩ : syracuseStep 3101519 = 4652279) B4652279
theorem B2067679 : Blo 2067435 2067679 := bstep (se 1 (by rfl) ⟨1550759, by rfl⟩ : syracuseStep 2067679 = 3101519) B3101519
theorem B3101525 : Blo 2067435 3101525 := bbase (se 9 (by rfl) ⟨9086, by rfl⟩ : syracuseStep 3101525 = 18173) (by norm_num)
theorem B2067683 : Blo 2067435 2067683 := bstep (se 1 (by rfl) ⟨1550762, by rfl⟩ : syracuseStep 2067683 = 3101525) B3101525
theorem B3312037 : Blo 2067435 3312037 := bbase (se 4 (by rfl) ⟨310503, by rfl⟩ : syracuseStep 3312037 = 621007) (by norm_num)
theorem B4416049 : Blo 2067435 4416049 := bstep (se 2 (by rfl) ⟨1656018, by rfl⟩ : syracuseStep 4416049 = 3312037) B3312037
theorem B5888065 : Blo 2067435 5888065 := bstep (se 2 (by rfl) ⟨2208024, by rfl⟩ : syracuseStep 5888065 = 4416049) B4416049
theorem B7850753 : Blo 2067435 7850753 := bstep (se 2 (by rfl) ⟨2944032, by rfl⟩ : syracuseStep 7850753 = 5888065) B5888065
theorem B5233835 : Blo 2067435 5233835 := bstep (se 1 (by rfl) ⟨3925376, by rfl⟩ : syracuseStep 5233835 = 7850753) B7850753
theorem B3489223 : Blo 2067435 3489223 := bstep (se 1 (by rfl) ⟨2616917, by rfl⟩ : syracuseStep 3489223 = 5233835) B5233835
theorem B4652297 : Blo 2067435 4652297 := bstep (se 2 (by rfl) ⟨1744611, by rfl⟩ : syracuseStep 4652297 = 3489223) B3489223
theorem B3101531 : Blo 2067435 3101531 := bstep (se 1 (by rfl) ⟨2326148, by rfl⟩ : syracuseStep 3101531 = 4652297) B4652297
theorem B2067687 : Blo 2067435 2067687 := bstep (se 1 (by rfl) ⟨1550765, by rfl⟩ : syracuseStep 2067687 = 3101531) B3101531
theorem B2326153 : Blo 2067435 2326153 := bbase (se 2 (by rfl) ⟨872307, by rfl⟩ : syracuseStep 2326153 = 1744615) (by norm_num)
theorem B3101537 : Blo 2067435 3101537 := bstep (se 2 (by rfl) ⟨1163076, by rfl⟩ : syracuseStep 3101537 = 2326153) B2326153
theorem B2067691 : Blo 2067435 2067691 := bstep (se 1 (by rfl) ⟨1550768, by rfl⟩ : syracuseStep 2067691 = 3101537) B3101537
theorem B53715797 : Blo 2067435 53715797 := bbase (se 9 (by rfl) ⟨157370, by rfl⟩ : syracuseStep 53715797 = 314741) (by norm_num)
theorem B35810531 : Blo 2067435 35810531 := bstep (se 1 (by rfl) ⟨26857898, by rfl⟩ : syracuseStep 35810531 = 53715797) B53715797
theorem B23873687 : Blo 2067435 23873687 := bstep (se 1 (by rfl) ⟨17905265, by rfl⟩ : syracuseStep 23873687 = 35810531) B35810531
theorem B15915791 : Blo 2067435 15915791 := bstep (se 1 (by rfl) ⟨11936843, by rfl⟩ : syracuseStep 15915791 = 23873687) B23873687
theorem B10610527 : Blo 2067435 10610527 := bstep (se 1 (by rfl) ⟨7957895, by rfl⟩ : syracuseStep 10610527 = 15915791) B15915791
theorem B14147369 : Blo 2067435 14147369 := bstep (se 2 (by rfl) ⟨5305263, by rfl⟩ : syracuseStep 14147369 = 10610527) B10610527
theorem B9431579 : Blo 2067435 9431579 := bstep (se 1 (by rfl) ⟨7073684, by rfl⟩ : syracuseStep 9431579 = 14147369) B14147369
theorem B25150877 : Blo 2067435 25150877 := bstep (se 3 (by rfl) ⟨4715789, by rfl⟩ : syracuseStep 25150877 = 9431579) B9431579
theorem B16767251 : Blo 2067435 16767251 := bstep (se 1 (by rfl) ⟨12575438, by rfl⟩ : syracuseStep 16767251 = 25150877) B25150877
theorem B11178167 : Blo 2067435 11178167 := bstep (se 1 (by rfl) ⟨8383625, by rfl⟩ : syracuseStep 11178167 = 16767251) B16767251
theorem B29808445 : Blo 2067435 29808445 := bstep (se 3 (by rfl) ⟨5589083, by rfl⟩ : syracuseStep 29808445 = 11178167) B11178167
theorem B39744593 : Blo 2067435 39744593 := bstep (se 2 (by rfl) ⟨14904222, by rfl⟩ : syracuseStep 39744593 = 29808445) B29808445
theorem B26496395 : Blo 2067435 26496395 := bstep (se 1 (by rfl) ⟨19872296, by rfl⟩ : syracuseStep 26496395 = 39744593) B39744593
theorem B17664263 : Blo 2067435 17664263 := bstep (se 1 (by rfl) ⟨13248197, by rfl⟩ : syracuseStep 17664263 = 26496395) B26496395
theorem B11776175 : Blo 2067435 11776175 := bstep (se 1 (by rfl) ⟨8832131, by rfl⟩ : syracuseStep 11776175 = 17664263) B17664263
theorem B7850783 : Blo 2067435 7850783 := bstep (se 1 (by rfl) ⟨5888087, by rfl⟩ : syracuseStep 7850783 = 11776175) B11776175
theorem B5233855 : Blo 2067435 5233855 := bstep (se 1 (by rfl) ⟨3925391, by rfl⟩ : syracuseStep 5233855 = 7850783) B7850783
theorem B6978473 : Blo 2067435 6978473 := bstep (se 2 (by rfl) ⟨2616927, by rfl⟩ : syracuseStep 6978473 = 5233855) B5233855
theorem B4652315 : Blo 2067435 4652315 := bstep (se 1 (by rfl) ⟨3489236, by rfl⟩ : syracuseStep 4652315 = 6978473) B6978473
theorem B3101543 : Blo 2067435 3101543 := bstep (se 1 (by rfl) ⟨2326157, by rfl⟩ : syracuseStep 3101543 = 4652315) B4652315
theorem B2067695 : Blo 2067435 2067695 := bstep (se 1 (by rfl) ⟨1550771, by rfl⟩ : syracuseStep 2067695 = 3101543) B3101543
theorem B3101549 : Blo 2067435 3101549 := bbase (se 3 (by rfl) ⟨581540, by rfl⟩ : syracuseStep 3101549 = 1163081) (by norm_num)
theorem B2067699 : Blo 2067435 2067699 := bstep (se 1 (by rfl) ⟨1550774, by rfl⟩ : syracuseStep 2067699 = 3101549) B3101549
theorem B4652333 : Blo 2067435 4652333 := bbase (se 3 (by rfl) ⟨872312, by rfl⟩ : syracuseStep 4652333 = 1744625) (by norm_num)
theorem B3101555 : Blo 2067435 3101555 := bstep (se 1 (by rfl) ⟨2326166, by rfl⟩ : syracuseStep 3101555 = 4652333) B4652333
theorem B2067703 : Blo 2067435 2067703 := bstep (se 1 (by rfl) ⟨1550777, by rfl⟩ : syracuseStep 2067703 = 3101555) B3101555
theorem B3978973 : Blo 2067435 3978973 := bbase (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) (by norm_num)
theorem B21221189 : Blo 2067435 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B14147459 : Blo 2067435 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B9431639 : Blo 2067435 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B6287759 : Blo 2067435 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B4191839 : Blo 2067435 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B2794559 : Blo 2067435 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B7452157 : Blo 2067435 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B9936209 : Blo 2067435 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B6624139 : Blo 2067435 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B8832185 : Blo 2067435 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B5888123 : Blo 2067435 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B3925415 : Blo 2067435 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B2616943 : Blo 2067435 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B3489257 : Blo 2067435 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B2326171 : Blo 2067435 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B3101561 : Blo 2067435 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B2067707 : Blo 2067435 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B4191845 : Blo 2067435 4191845 := bbase (se 4 (by rfl) ⟨392985, by rfl⟩ : syracuseStep 4191845 = 785971) (by norm_num)
theorem B11178253 : Blo 2067435 11178253 := bstep (se 3 (by rfl) ⟨2095922, by rfl⟩ : syracuseStep 11178253 = 4191845) B4191845
theorem B14904337 : Blo 2067435 14904337 := bstep (se 2 (by rfl) ⟨5589126, by rfl⟩ : syracuseStep 14904337 = 11178253) B11178253
theorem B19872449 : Blo 2067435 19872449 := bstep (se 2 (by rfl) ⟨7452168, by rfl⟩ : syracuseStep 19872449 = 14904337) B14904337
theorem B13248299 : Blo 2067435 13248299 := bstep (se 1 (by rfl) ⟨9936224, by rfl⟩ : syracuseStep 13248299 = 19872449) B19872449
theorem B35328797 : Blo 2067435 35328797 := bstep (se 3 (by rfl) ⟨6624149, by rfl⟩ : syracuseStep 35328797 = 13248299) B13248299
theorem B23552531 : Blo 2067435 23552531 := bstep (se 1 (by rfl) ⟨17664398, by rfl⟩ : syracuseStep 23552531 = 35328797) B35328797
theorem B15701687 : Blo 2067435 15701687 := bstep (se 1 (by rfl) ⟨11776265, by rfl⟩ : syracuseStep 15701687 = 23552531) B23552531
theorem B10467791 : Blo 2067435 10467791 := bstep (se 1 (by rfl) ⟨7850843, by rfl⟩ : syracuseStep 10467791 = 15701687) B15701687
theorem B6978527 : Blo 2067435 6978527 := bstep (se 1 (by rfl) ⟨5233895, by rfl⟩ : syracuseStep 6978527 = 10467791) B10467791
theorem B4652351 : Blo 2067435 4652351 := bstep (se 1 (by rfl) ⟨3489263, by rfl⟩ : syracuseStep 4652351 = 6978527) B6978527
theorem B3101567 : Blo 2067435 3101567 := bstep (se 1 (by rfl) ⟨2326175, by rfl⟩ : syracuseStep 3101567 = 4652351) B4652351
theorem B2067711 : Blo 2067435 2067711 := bstep (se 1 (by rfl) ⟨1550783, by rfl⟩ : syracuseStep 2067711 = 3101567) B3101567
theorem B3101573 : Blo 2067435 3101573 := bbase (se 4 (by rfl) ⟨290772, by rfl⟩ : syracuseStep 3101573 = 581545) (by norm_num)
theorem B2067715 : Blo 2067435 2067715 := bstep (se 1 (by rfl) ⟨1550786, by rfl⟩ : syracuseStep 2067715 = 3101573) B3101573
theorem B3489277 : Blo 2067435 3489277 := bbase (se 3 (by rfl) ⟨654239, by rfl⟩ : syracuseStep 3489277 = 1308479) (by norm_num)
theorem B4652369 : Blo 2067435 4652369 := bstep (se 2 (by rfl) ⟨1744638, by rfl⟩ : syracuseStep 4652369 = 3489277) B3489277
theorem B3101579 : Blo 2067435 3101579 := bstep (se 1 (by rfl) ⟨2326184, by rfl⟩ : syracuseStep 3101579 = 4652369) B4652369
theorem B2067719 : Blo 2067435 2067719 := bstep (se 1 (by rfl) ⟨1550789, by rfl⟩ : syracuseStep 2067719 = 3101579) B3101579
theorem B2326189 : Blo 2067435 2326189 := bbase (se 3 (by rfl) ⟨436160, by rfl⟩ : syracuseStep 2326189 = 872321) (by norm_num)
theorem B3101585 : Blo 2067435 3101585 := bstep (se 2 (by rfl) ⟨1163094, by rfl⟩ : syracuseStep 3101585 = 2326189) B2326189
theorem B2067723 : Blo 2067435 2067723 := bstep (se 1 (by rfl) ⟨1550792, by rfl⟩ : syracuseStep 2067723 = 3101585) B3101585
theorem B6978581 : Blo 2067435 6978581 := bbase (se 6 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 6978581 = 327121) (by norm_num)
theorem B4652387 : Blo 2067435 4652387 := bstep (se 1 (by rfl) ⟨3489290, by rfl⟩ : syracuseStep 4652387 = 6978581) B6978581
theorem B3101591 : Blo 2067435 3101591 := bstep (se 1 (by rfl) ⟨2326193, by rfl⟩ : syracuseStep 3101591 = 4652387) B4652387
theorem B2067727 : Blo 2067435 2067727 := bstep (se 1 (by rfl) ⟨1550795, by rfl⟩ : syracuseStep 2067727 = 3101591) B3101591
theorem B3101597 : Blo 2067435 3101597 := bbase (se 3 (by rfl) ⟨581549, by rfl⟩ : syracuseStep 3101597 = 1163099) (by norm_num)
theorem B2067731 : Blo 2067435 2067731 := bstep (se 1 (by rfl) ⟨1550798, by rfl⟩ : syracuseStep 2067731 = 3101597) B3101597
theorem B4652405 : Blo 2067435 4652405 := bbase (se 5 (by rfl) ⟨218081, by rfl⟩ : syracuseStep 4652405 = 436163) (by norm_num)
theorem B3101603 : Blo 2067435 3101603 := bstep (se 1 (by rfl) ⟨2326202, by rfl⟩ : syracuseStep 3101603 = 4652405) B4652405
theorem B2067735 : Blo 2067435 2067735 := bstep (se 1 (by rfl) ⟨1550801, by rfl⟩ : syracuseStep 2067735 = 3101603) B3101603
theorem B4476413 : Blo 2067435 4476413 := bbase (se 3 (by rfl) ⟨839327, by rfl⟩ : syracuseStep 4476413 = 1678655) (by norm_num)
theorem B2984275 : Blo 2067435 2984275 := bstep (se 1 (by rfl) ⟨2238206, by rfl⟩ : syracuseStep 2984275 = 4476413) B4476413
theorem B3979033 : Blo 2067435 3979033 := bstep (se 2 (by rfl) ⟨1492137, by rfl⟩ : syracuseStep 3979033 = 2984275) B2984275
theorem B21221509 : Blo 2067435 21221509 := bstep (se 4 (by rfl) ⟨1989516, by rfl⟩ : syracuseStep 21221509 = 3979033) B3979033
theorem B28295345 : Blo 2067435 28295345 := bstep (se 2 (by rfl) ⟨10610754, by rfl⟩ : syracuseStep 28295345 = 21221509) B21221509
theorem B18863563 : Blo 2067435 18863563 := bstep (se 1 (by rfl) ⟨14147672, by rfl⟩ : syracuseStep 18863563 = 28295345) B28295345
theorem B25151417 : Blo 2067435 25151417 := bstep (se 2 (by rfl) ⟨9431781, by rfl⟩ : syracuseStep 25151417 = 18863563) B18863563
theorem B16767611 : Blo 2067435 16767611 := bstep (se 1 (by rfl) ⟨12575708, by rfl⟩ : syracuseStep 16767611 = 25151417) B25151417
theorem B11178407 : Blo 2067435 11178407 := bstep (se 1 (by rfl) ⟨8383805, by rfl⟩ : syracuseStep 11178407 = 16767611) B16767611
theorem B7452271 : Blo 2067435 7452271 := bstep (se 1 (by rfl) ⟨5589203, by rfl⟩ : syracuseStep 7452271 = 11178407) B11178407
theorem B9936361 : Blo 2067435 9936361 := bstep (se 2 (by rfl) ⟨3726135, by rfl⟩ : syracuseStep 9936361 = 7452271) B7452271
theorem B13248481 : Blo 2067435 13248481 := bstep (se 2 (by rfl) ⟨4968180, by rfl⟩ : syracuseStep 13248481 = 9936361) B9936361
theorem B17664641 : Blo 2067435 17664641 := bstep (se 2 (by rfl) ⟨6624240, by rfl⟩ : syracuseStep 17664641 = 13248481) B13248481
theorem B11776427 : Blo 2067435 11776427 := bstep (se 1 (by rfl) ⟨8832320, by rfl⟩ : syracuseStep 11776427 = 17664641) B17664641
theorem B7850951 : Blo 2067435 7850951 := bstep (se 1 (by rfl) ⟨5888213, by rfl⟩ : syracuseStep 7850951 = 11776427) B11776427
theorem B5233967 : Blo 2067435 5233967 := bstep (se 1 (by rfl) ⟨3925475, by rfl⟩ : syracuseStep 5233967 = 7850951) B7850951
theorem B3489311 : Blo 2067435 3489311 := bstep (se 1 (by rfl) ⟨2616983, by rfl⟩ : syracuseStep 3489311 = 5233967) B5233967
theorem B2326207 : Blo 2067435 2326207 := bstep (se 1 (by rfl) ⟨1744655, by rfl⟩ : syracuseStep 2326207 = 3489311) B3489311
theorem B3101609 : Blo 2067435 3101609 := bstep (se 2 (by rfl) ⟨1163103, by rfl⟩ : syracuseStep 3101609 = 2326207) B2326207
theorem B2067739 : Blo 2067435 2067739 := bstep (se 1 (by rfl) ⟨1550804, by rfl⟩ : syracuseStep 2067739 = 3101609) B3101609
theorem B7850965 : Blo 2067435 7850965 := bbase (se 7 (by rfl) ⟨92003, by rfl⟩ : syracuseStep 7850965 = 184007) (by norm_num)
theorem B10467953 : Blo 2067435 10467953 := bstep (se 2 (by rfl) ⟨3925482, by rfl⟩ : syracuseStep 10467953 = 7850965) B7850965
theorem B6978635 : Blo 2067435 6978635 := bstep (se 1 (by rfl) ⟨5233976, by rfl⟩ : syracuseStep 6978635 = 10467953) B10467953
theorem B4652423 : Blo 2067435 4652423 := bstep (se 1 (by rfl) ⟨3489317, by rfl⟩ : syracuseStep 4652423 = 6978635) B6978635
theorem B3101615 : Blo 2067435 3101615 := bstep (se 1 (by rfl) ⟨2326211, by rfl⟩ : syracuseStep 3101615 = 4652423) B4652423
theorem B2067743 : Blo 2067435 2067743 := bstep (se 1 (by rfl) ⟨1550807, by rfl⟩ : syracuseStep 2067743 = 3101615) B3101615
theorem B3101621 : Blo 2067435 3101621 := bbase (se 5 (by rfl) ⟨145388, by rfl⟩ : syracuseStep 3101621 = 290777) (by norm_num)
theorem B2067747 : Blo 2067435 2067747 := bstep (se 1 (by rfl) ⟨1550810, by rfl⟩ : syracuseStep 2067747 = 3101621) B3101621
theorem B5233997 : Blo 2067435 5233997 := bbase (se 3 (by rfl) ⟨981374, by rfl⟩ : syracuseStep 5233997 = 1962749) (by norm_num)
theorem B3489331 : Blo 2067435 3489331 := bstep (se 1 (by rfl) ⟨2616998, by rfl⟩ : syracuseStep 3489331 = 5233997) B5233997
theorem B4652441 : Blo 2067435 4652441 := bstep (se 2 (by rfl) ⟨1744665, by rfl⟩ : syracuseStep 4652441 = 3489331) B3489331
theorem B3101627 : Blo 2067435 3101627 := bstep (se 1 (by rfl) ⟨2326220, by rfl⟩ : syracuseStep 3101627 = 4652441) B4652441
theorem B2067751 : Blo 2067435 2067751 := bstep (se 1 (by rfl) ⟨1550813, by rfl⟩ : syracuseStep 2067751 = 3101627) B3101627
theorem B2326225 : Blo 2067435 2326225 := bbase (se 2 (by rfl) ⟨872334, by rfl⟩ : syracuseStep 2326225 = 1744669) (by norm_num)
theorem B3101633 : Blo 2067435 3101633 := bstep (se 2 (by rfl) ⟨1163112, by rfl⟩ : syracuseStep 3101633 = 2326225) B2326225
theorem B2067755 : Blo 2067435 2067755 := bstep (se 1 (by rfl) ⟨1550816, by rfl⟩ : syracuseStep 2067755 = 3101633) B3101633
theorem B4968229 : Blo 2067435 4968229 := bbase (se 4 (by rfl) ⟨465771, by rfl⟩ : syracuseStep 4968229 = 931543) (by norm_num)
theorem B6624305 : Blo 2067435 6624305 := bstep (se 2 (by rfl) ⟨2484114, by rfl⟩ : syracuseStep 6624305 = 4968229) B4968229
theorem B4416203 : Blo 2067435 4416203 := bstep (se 1 (by rfl) ⟨3312152, by rfl⟩ : syracuseStep 4416203 = 6624305) B6624305
theorem B2944135 : Blo 2067435 2944135 := bstep (se 1 (by rfl) ⟨2208101, by rfl⟩ : syracuseStep 2944135 = 4416203) B4416203
theorem B3925513 : Blo 2067435 3925513 := bstep (se 2 (by rfl) ⟨1472067, by rfl⟩ : syracuseStep 3925513 = 2944135) B2944135
theorem B5234017 : Blo 2067435 5234017 := bstep (se 2 (by rfl) ⟨1962756, by rfl⟩ : syracuseStep 5234017 = 3925513) B3925513
theorem B6978689 : Blo 2067435 6978689 := bstep (se 2 (by rfl) ⟨2617008, by rfl⟩ : syracuseStep 6978689 = 5234017) B5234017
theorem B4652459 : Blo 2067435 4652459 := bstep (se 1 (by rfl) ⟨3489344, by rfl⟩ : syracuseStep 4652459 = 6978689) B6978689
theorem B3101639 : Blo 2067435 3101639 := bstep (se 1 (by rfl) ⟨2326229, by rfl⟩ : syracuseStep 3101639 = 4652459) B4652459
theorem B2067759 : Blo 2067435 2067759 := bstep (se 1 (by rfl) ⟨1550819, by rfl⟩ : syracuseStep 2067759 = 3101639) B3101639
theorem B3101645 : Blo 2067435 3101645 := bbase (se 3 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 3101645 = 1163117) (by norm_num)
theorem B2067763 : Blo 2067435 2067763 := bstep (se 1 (by rfl) ⟨1550822, by rfl⟩ : syracuseStep 2067763 = 3101645) B3101645
theorem B4652477 : Blo 2067435 4652477 := bbase (se 3 (by rfl) ⟨872339, by rfl⟩ : syracuseStep 4652477 = 1744679) (by norm_num)
theorem B3101651 : Blo 2067435 3101651 := bstep (se 1 (by rfl) ⟨2326238, by rfl⟩ : syracuseStep 3101651 = 4652477) B4652477
theorem B2067767 : Blo 2067435 2067767 := bstep (se 1 (by rfl) ⟨1550825, by rfl⟩ : syracuseStep 2067767 = 3101651) B3101651
theorem B3489365 : Blo 2067435 3489365 := bbase (se 8 (by rfl) ⟨20445, by rfl⟩ : syracuseStep 3489365 = 40891) (by norm_num)
theorem B2326243 : Blo 2067435 2326243 := bstep (se 1 (by rfl) ⟨1744682, by rfl⟩ : syracuseStep 2326243 = 3489365) B3489365
theorem B3101657 : Blo 2067435 3101657 := bstep (se 2 (by rfl) ⟨1163121, by rfl⟩ : syracuseStep 3101657 = 2326243) B2326243
theorem B2067771 : Blo 2067435 2067771 := bstep (se 1 (by rfl) ⟨1550828, by rfl⟩ : syracuseStep 2067771 = 3101657) B3101657
theorem B9936533 : Blo 2067435 9936533 := bbase (se 6 (by rfl) ⟨232887, by rfl⟩ : syracuseStep 9936533 = 465775) (by norm_num)
theorem B6624355 : Blo 2067435 6624355 := bstep (se 1 (by rfl) ⟨4968266, by rfl⟩ : syracuseStep 6624355 = 9936533) B9936533
theorem B8832473 : Blo 2067435 8832473 := bstep (se 2 (by rfl) ⟨3312177, by rfl⟩ : syracuseStep 8832473 = 6624355) B6624355
theorem B5888315 : Blo 2067435 5888315 := bstep (se 1 (by rfl) ⟨4416236, by rfl⟩ : syracuseStep 5888315 = 8832473) B8832473
theorem B15702173 : Blo 2067435 15702173 := bstep (se 3 (by rfl) ⟨2944157, by rfl⟩ : syracuseStep 15702173 = 5888315) B5888315
theorem B10468115 : Blo 2067435 10468115 := bstep (se 1 (by rfl) ⟨7851086, by rfl⟩ : syracuseStep 10468115 = 15702173) B15702173
theorem B6978743 : Blo 2067435 6978743 := bstep (se 1 (by rfl) ⟨5234057, by rfl⟩ : syracuseStep 6978743 = 10468115) B10468115
theorem B4652495 : Blo 2067435 4652495 := bstep (se 1 (by rfl) ⟨3489371, by rfl⟩ : syracuseStep 4652495 = 6978743) B6978743
theorem B3101663 : Blo 2067435 3101663 := bstep (se 1 (by rfl) ⟨2326247, by rfl⟩ : syracuseStep 3101663 = 4652495) B4652495
theorem B2067775 : Blo 2067435 2067775 := bstep (se 1 (by rfl) ⟨1550831, by rfl⟩ : syracuseStep 2067775 = 3101663) B3101663
theorem B3101669 : Blo 2067435 3101669 := bbase (se 4 (by rfl) ⟨290781, by rfl⟩ : syracuseStep 3101669 = 581563) (by norm_num)
theorem B2067779 : Blo 2067435 2067779 := bstep (se 1 (by rfl) ⟨1550834, by rfl⟩ : syracuseStep 2067779 = 3101669) B3101669
theorem B25151957 : Blo 2067435 25151957 := bbase (se 7 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 25151957 = 589499) (by norm_num)
theorem B16767971 : Blo 2067435 16767971 := bstep (se 1 (by rfl) ⟨12575978, by rfl⟩ : syracuseStep 16767971 = 25151957) B25151957
theorem B11178647 : Blo 2067435 11178647 := bstep (se 1 (by rfl) ⟨8383985, by rfl⟩ : syracuseStep 11178647 = 16767971) B16767971
theorem B7452431 : Blo 2067435 7452431 := bstep (se 1 (by rfl) ⟨5589323, by rfl⟩ : syracuseStep 7452431 = 11178647) B11178647
theorem B4968287 : Blo 2067435 4968287 := bstep (se 1 (by rfl) ⟨3726215, by rfl⟩ : syracuseStep 4968287 = 7452431) B7452431
theorem B3312191 : Blo 2067435 3312191 := bstep (se 1 (by rfl) ⟨2484143, by rfl⟩ : syracuseStep 3312191 = 4968287) B4968287
theorem B8832509 : Blo 2067435 8832509 := bstep (se 3 (by rfl) ⟨1656095, by rfl⟩ : syracuseStep 8832509 = 3312191) B3312191
theorem B5888339 : Blo 2067435 5888339 := bstep (se 1 (by rfl) ⟨4416254, by rfl⟩ : syracuseStep 5888339 = 8832509) B8832509
theorem B3925559 : Blo 2067435 3925559 := bstep (se 1 (by rfl) ⟨2944169, by rfl⟩ : syracuseStep 3925559 = 5888339) B5888339
theorem B2617039 : Blo 2067435 2617039 := bstep (se 1 (by rfl) ⟨1962779, by rfl⟩ : syracuseStep 2617039 = 3925559) B3925559
theorem B3489385 : Blo 2067435 3489385 := bstep (se 2 (by rfl) ⟨1308519, by rfl⟩ : syracuseStep 3489385 = 2617039) B2617039
theorem B4652513 : Blo 2067435 4652513 := bstep (se 2 (by rfl) ⟨1744692, by rfl⟩ : syracuseStep 4652513 = 3489385) B3489385
theorem B3101675 : Blo 2067435 3101675 := bstep (se 1 (by rfl) ⟨2326256, by rfl⟩ : syracuseStep 3101675 = 4652513) B4652513
theorem B2067783 : Blo 2067435 2067783 := bstep (se 1 (by rfl) ⟨1550837, by rfl⟩ : syracuseStep 2067783 = 3101675) B3101675
theorem B2326261 : Blo 2067435 2326261 := bbase (se 5 (by rfl) ⟨109043, by rfl⟩ : syracuseStep 2326261 = 218087) (by norm_num)
theorem B3101681 : Blo 2067435 3101681 := bstep (se 2 (by rfl) ⟨1163130, by rfl⟩ : syracuseStep 3101681 = 2326261) B2326261
theorem B2067787 : Blo 2067435 2067787 := bstep (se 1 (by rfl) ⟨1550840, by rfl⟩ : syracuseStep 2067787 = 3101681) B3101681
theorem B2617049 : Blo 2067435 2617049 := bbase (se 2 (by rfl) ⟨981393, by rfl⟩ : syracuseStep 2617049 = 1962787) (by norm_num)
theorem B6978797 : Blo 2067435 6978797 := bstep (se 3 (by rfl) ⟨1308524, by rfl⟩ : syracuseStep 6978797 = 2617049) B2617049
theorem B4652531 : Blo 2067435 4652531 := bstep (se 1 (by rfl) ⟨3489398, by rfl⟩ : syracuseStep 4652531 = 6978797) B6978797
theorem B3101687 : Blo 2067435 3101687 := bstep (se 1 (by rfl) ⟨2326265, by rfl⟩ : syracuseStep 3101687 = 4652531) B4652531
theorem B2067791 : Blo 2067435 2067791 := bstep (se 1 (by rfl) ⟨1550843, by rfl⟩ : syracuseStep 2067791 = 3101687) B3101687
theorem B3101693 : Blo 2067435 3101693 := bbase (se 3 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 3101693 = 1163135) (by norm_num)
theorem B2067795 : Blo 2067435 2067795 := bstep (se 1 (by rfl) ⟨1550846, by rfl⟩ : syracuseStep 2067795 = 3101693) B3101693
theorem B4652549 : Blo 2067435 4652549 := bbase (se 4 (by rfl) ⟨436176, by rfl⟩ : syracuseStep 4652549 = 872353) (by norm_num)
theorem B3101699 : Blo 2067435 3101699 := bstep (se 1 (by rfl) ⟨2326274, by rfl⟩ : syracuseStep 3101699 = 4652549) B4652549
theorem B2067799 : Blo 2067435 2067799 := bstep (se 1 (by rfl) ⟨1550849, by rfl⟩ : syracuseStep 2067799 = 3101699) B3101699
theorem B3925597 : Blo 2067435 3925597 := bbase (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) (by norm_num)
theorem B5234129 : Blo 2067435 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B3489419 : Blo 2067435 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B2326279 : Blo 2067435 2326279 := bstep (se 1 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 2326279 = 3489419) B3489419
theorem B3101705 : Blo 2067435 3101705 := bstep (se 2 (by rfl) ⟨1163139, by rfl⟩ : syracuseStep 3101705 = 2326279) B2326279
theorem B2067803 : Blo 2067435 2067803 := bstep (se 1 (by rfl) ⟨1550852, by rfl⟩ : syracuseStep 2067803 = 3101705) B3101705
theorem B10468277 : Blo 2067435 10468277 := bbase (se 5 (by rfl) ⟨490700, by rfl⟩ : syracuseStep 10468277 = 981401) (by norm_num)
theorem B6978851 : Blo 2067435 6978851 := bstep (se 1 (by rfl) ⟨5234138, by rfl⟩ : syracuseStep 6978851 = 10468277) B10468277
theorem B4652567 : Blo 2067435 4652567 := bstep (se 1 (by rfl) ⟨3489425, by rfl⟩ : syracuseStep 4652567 = 6978851) B6978851
theorem B3101711 : Blo 2067435 3101711 := bstep (se 1 (by rfl) ⟨2326283, by rfl⟩ : syracuseStep 3101711 = 4652567) B4652567
theorem B2067807 : Blo 2067435 2067807 := bstep (se 1 (by rfl) ⟨1550855, by rfl⟩ : syracuseStep 2067807 = 3101711) B3101711
theorem B3101717 : Blo 2067435 3101717 := bbase (se 6 (by rfl) ⟨72696, by rfl⟩ : syracuseStep 3101717 = 145393) (by norm_num)
theorem B2067811 : Blo 2067435 2067811 := bstep (se 1 (by rfl) ⟨1550858, by rfl⟩ : syracuseStep 2067811 = 3101717) B3101717
theorem B4033469 : Blo 2067435 4033469 := bbase (se 3 (by rfl) ⟨756275, by rfl⟩ : syracuseStep 4033469 = 1512551) (by norm_num)
theorem B10755917 : Blo 2067435 10755917 := bstep (se 3 (by rfl) ⟨2016734, by rfl⟩ : syracuseStep 10755917 = 4033469) B4033469
theorem B7170611 : Blo 2067435 7170611 := bstep (se 1 (by rfl) ⟨5377958, by rfl⟩ : syracuseStep 7170611 = 10755917) B10755917
theorem B19121629 : Blo 2067435 19121629 := bstep (se 3 (by rfl) ⟨3585305, by rfl⟩ : syracuseStep 19121629 = 7170611) B7170611
theorem B25495505 : Blo 2067435 25495505 := bstep (se 2 (by rfl) ⟨9560814, by rfl⟩ : syracuseStep 25495505 = 19121629) B19121629
theorem B16997003 : Blo 2067435 16997003 := bstep (se 1 (by rfl) ⟨12747752, by rfl⟩ : syracuseStep 16997003 = 25495505) B25495505
theorem B11331335 : Blo 2067435 11331335 := bstep (se 1 (by rfl) ⟨8498501, by rfl⟩ : syracuseStep 11331335 = 16997003) B16997003
theorem B7554223 : Blo 2067435 7554223 := bstep (se 1 (by rfl) ⟨5665667, by rfl⟩ : syracuseStep 7554223 = 11331335) B11331335
theorem B10072297 : Blo 2067435 10072297 := bstep (se 2 (by rfl) ⟨3777111, by rfl⟩ : syracuseStep 10072297 = 7554223) B7554223
theorem B13429729 : Blo 2067435 13429729 := bstep (se 2 (by rfl) ⟨5036148, by rfl⟩ : syracuseStep 13429729 = 10072297) B10072297
theorem B71625221 : Blo 2067435 71625221 := bstep (se 4 (by rfl) ⟨6714864, by rfl⟩ : syracuseStep 71625221 = 13429729) B13429729
theorem B47750147 : Blo 2067435 47750147 := bstep (se 1 (by rfl) ⟨35812610, by rfl⟩ : syracuseStep 47750147 = 71625221) B71625221
theorem B31833431 : Blo 2067435 31833431 := bstep (se 1 (by rfl) ⟨23875073, by rfl⟩ : syracuseStep 31833431 = 47750147) B47750147
theorem B21222287 : Blo 2067435 21222287 := bstep (se 1 (by rfl) ⟨15916715, by rfl⟩ : syracuseStep 21222287 = 31833431) B31833431
theorem B14148191 : Blo 2067435 14148191 := bstep (se 1 (by rfl) ⟨10611143, by rfl⟩ : syracuseStep 14148191 = 21222287) B21222287
theorem B9432127 : Blo 2067435 9432127 := bstep (se 1 (by rfl) ⟨7074095, by rfl⟩ : syracuseStep 9432127 = 14148191) B14148191
theorem B12576169 : Blo 2067435 12576169 := bstep (se 2 (by rfl) ⟨4716063, by rfl⟩ : syracuseStep 12576169 = 9432127) B9432127
theorem B16768225 : Blo 2067435 16768225 := bstep (se 2 (by rfl) ⟨6288084, by rfl⟩ : syracuseStep 16768225 = 12576169) B12576169
theorem B22357633 : Blo 2067435 22357633 := bstep (se 2 (by rfl) ⟨8384112, by rfl⟩ : syracuseStep 22357633 = 16768225) B16768225
theorem B29810177 : Blo 2067435 29810177 := bstep (se 2 (by rfl) ⟨11178816, by rfl⟩ : syracuseStep 29810177 = 22357633) B22357633
theorem B19873451 : Blo 2067435 19873451 := bstep (se 1 (by rfl) ⟨14905088, by rfl⟩ : syracuseStep 19873451 = 29810177) B29810177
theorem B13248967 : Blo 2067435 13248967 := bstep (se 1 (by rfl) ⟨9936725, by rfl⟩ : syracuseStep 13248967 = 19873451) B19873451
theorem B17665289 : Blo 2067435 17665289 := bstep (se 2 (by rfl) ⟨6624483, by rfl⟩ : syracuseStep 17665289 = 13248967) B13248967
theorem B11776859 : Blo 2067435 11776859 := bstep (se 1 (by rfl) ⟨8832644, by rfl⟩ : syracuseStep 11776859 = 17665289) B17665289
theorem B7851239 : Blo 2067435 7851239 := bstep (se 1 (by rfl) ⟨5888429, by rfl⟩ : syracuseStep 7851239 = 11776859) B11776859
theorem B5234159 : Blo 2067435 5234159 := bstep (se 1 (by rfl) ⟨3925619, by rfl⟩ : syracuseStep 5234159 = 7851239) B7851239
theorem B3489439 : Blo 2067435 3489439 := bstep (se 1 (by rfl) ⟨2617079, by rfl⟩ : syracuseStep 3489439 = 5234159) B5234159
theorem B4652585 : Blo 2067435 4652585 := bstep (se 2 (by rfl) ⟨1744719, by rfl⟩ : syracuseStep 4652585 = 3489439) B3489439
theorem B3101723 : Blo 2067435 3101723 := bstep (se 1 (by rfl) ⟨2326292, by rfl⟩ : syracuseStep 3101723 = 4652585) B4652585
theorem B2067815 : Blo 2067435 2067815 := bstep (se 1 (by rfl) ⟨1550861, by rfl⟩ : syracuseStep 2067815 = 3101723) B3101723
theorem B2326297 : Blo 2067435 2326297 := bbase (se 2 (by rfl) ⟨872361, by rfl⟩ : syracuseStep 2326297 = 1744723) (by norm_num)
theorem B3101729 : Blo 2067435 3101729 := bstep (se 2 (by rfl) ⟨1163148, by rfl⟩ : syracuseStep 3101729 = 2326297) B2326297
theorem B2067819 : Blo 2067435 2067819 := bstep (se 1 (by rfl) ⟨1550864, by rfl⟩ : syracuseStep 2067819 = 3101729) B3101729
theorem B7851269 : Blo 2067435 7851269 := bbase (se 4 (by rfl) ⟨736056, by rfl⟩ : syracuseStep 7851269 = 1472113) (by norm_num)
theorem B5234179 : Blo 2067435 5234179 := bstep (se 1 (by rfl) ⟨3925634, by rfl⟩ : syracuseStep 5234179 = 7851269) B7851269
theorem B6978905 : Blo 2067435 6978905 := bstep (se 2 (by rfl) ⟨2617089, by rfl⟩ : syracuseStep 6978905 = 5234179) B5234179
theorem B4652603 : Blo 2067435 4652603 := bstep (se 1 (by rfl) ⟨3489452, by rfl⟩ : syracuseStep 4652603 = 6978905) B6978905
theorem B3101735 : Blo 2067435 3101735 := bstep (se 1 (by rfl) ⟨2326301, by rfl⟩ : syracuseStep 3101735 = 4652603) B4652603
theorem B2067823 : Blo 2067435 2067823 := bstep (se 1 (by rfl) ⟨1550867, by rfl⟩ : syracuseStep 2067823 = 3101735) B3101735
theorem B3101741 : Blo 2067435 3101741 := bbase (se 3 (by rfl) ⟨581576, by rfl⟩ : syracuseStep 3101741 = 1163153) (by norm_num)
theorem B2067827 : Blo 2067435 2067827 := bstep (se 1 (by rfl) ⟨1550870, by rfl⟩ : syracuseStep 2067827 = 3101741) B3101741
theorem B4652621 : Blo 2067435 4652621 := bbase (se 3 (by rfl) ⟨872366, by rfl⟩ : syracuseStep 4652621 = 1744733) (by norm_num)
theorem B3101747 : Blo 2067435 3101747 := bstep (se 1 (by rfl) ⟨2326310, by rfl⟩ : syracuseStep 3101747 = 4652621) B4652621
theorem B2067831 : Blo 2067435 2067831 := bstep (se 1 (by rfl) ⟨1550873, by rfl⟩ : syracuseStep 2067831 = 3101747) B3101747
theorem B2617105 : Blo 2067435 2617105 := bbase (se 2 (by rfl) ⟨981414, by rfl⟩ : syracuseStep 2617105 = 1962829) (by norm_num)
theorem B3489473 : Blo 2067435 3489473 := bstep (se 2 (by rfl) ⟨1308552, by rfl⟩ : syracuseStep 3489473 = 2617105) B2617105
theorem B2326315 : Blo 2067435 2326315 := bstep (se 1 (by rfl) ⟨1744736, by rfl⟩ : syracuseStep 2326315 = 3489473) B3489473
theorem B3101753 : Blo 2067435 3101753 := bstep (se 2 (by rfl) ⟨1163157, by rfl⟩ : syracuseStep 3101753 = 2326315) B2326315
theorem B2067835 : Blo 2067435 2067835 := bstep (se 1 (by rfl) ⟨1550876, by rfl⟩ : syracuseStep 2067835 = 3101753) B3101753
theorem B4416373 : Blo 2067435 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B23553989 : Blo 2067435 23553989 := bstep (se 4 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 23553989 = 4416373) B4416373
theorem B15702659 : Blo 2067435 15702659 := bstep (se 1 (by rfl) ⟨11776994, by rfl⟩ : syracuseStep 15702659 = 23553989) B23553989
theorem B10468439 : Blo 2067435 10468439 := bstep (se 1 (by rfl) ⟨7851329, by rfl⟩ : syracuseStep 10468439 = 15702659) B15702659
theorem B6978959 : Blo 2067435 6978959 := bstep (se 1 (by rfl) ⟨5234219, by rfl⟩ : syracuseStep 6978959 = 10468439) B10468439
theorem B4652639 : Blo 2067435 4652639 := bstep (se 1 (by rfl) ⟨3489479, by rfl⟩ : syracuseStep 4652639 = 6978959) B6978959
theorem B3101759 : Blo 2067435 3101759 := bstep (se 1 (by rfl) ⟨2326319, by rfl⟩ : syracuseStep 3101759 = 4652639) B4652639
theorem B2067839 : Blo 2067435 2067839 := bstep (se 1 (by rfl) ⟨1550879, by rfl⟩ : syracuseStep 2067839 = 3101759) B3101759
theorem B3101765 : Blo 2067435 3101765 := bbase (se 4 (by rfl) ⟨290790, by rfl⟩ : syracuseStep 3101765 = 581581) (by norm_num)
theorem B2067843 : Blo 2067435 2067843 := bstep (se 1 (by rfl) ⟨1550882, by rfl⟩ : syracuseStep 2067843 = 3101765) B3101765
theorem B3489493 : Blo 2067435 3489493 := bbase (se 7 (by rfl) ⟨40892, by rfl⟩ : syracuseStep 3489493 = 81785) (by norm_num)
theorem B4652657 : Blo 2067435 4652657 := bstep (se 2 (by rfl) ⟨1744746, by rfl⟩ : syracuseStep 4652657 = 3489493) B3489493
theorem B3101771 : Blo 2067435 3101771 := bstep (se 1 (by rfl) ⟨2326328, by rfl⟩ : syracuseStep 3101771 = 4652657) B4652657
theorem B2067847 : Blo 2067435 2067847 := bstep (se 1 (by rfl) ⟨1550885, by rfl⟩ : syracuseStep 2067847 = 3101771) B3101771
theorem B2326333 : Blo 2067435 2326333 := bbase (se 3 (by rfl) ⟨436187, by rfl⟩ : syracuseStep 2326333 = 872375) (by norm_num)
theorem B3101777 : Blo 2067435 3101777 := bstep (se 2 (by rfl) ⟨1163166, by rfl⟩ : syracuseStep 3101777 = 2326333) B2326333
theorem B2067851 : Blo 2067435 2067851 := bstep (se 1 (by rfl) ⟨1550888, by rfl⟩ : syracuseStep 2067851 = 3101777) B3101777
theorem B6979013 : Blo 2067435 6979013 := bbase (se 4 (by rfl) ⟨654282, by rfl⟩ : syracuseStep 6979013 = 1308565) (by norm_num)
theorem B4652675 : Blo 2067435 4652675 := bstep (se 1 (by rfl) ⟨3489506, by rfl⟩ : syracuseStep 4652675 = 6979013) B6979013
theorem B3101783 : Blo 2067435 3101783 := bstep (se 1 (by rfl) ⟨2326337, by rfl⟩ : syracuseStep 3101783 = 4652675) B4652675
theorem B2067855 : Blo 2067435 2067855 := bstep (se 1 (by rfl) ⟨1550891, by rfl⟩ : syracuseStep 2067855 = 3101783) B3101783
theorem B3101789 : Blo 2067435 3101789 := bbase (se 3 (by rfl) ⟨581585, by rfl⟩ : syracuseStep 3101789 = 1163171) (by norm_num)
theorem B2067859 : Blo 2067435 2067859 := bstep (se 1 (by rfl) ⟨1550894, by rfl⟩ : syracuseStep 2067859 = 3101789) B3101789
theorem B4652693 : Blo 2067435 4652693 := bbase (se 6 (by rfl) ⟨109047, by rfl⟩ : syracuseStep 4652693 = 218095) (by norm_num)
theorem B3101795 : Blo 2067435 3101795 := bstep (se 1 (by rfl) ⟨2326346, by rfl⟩ : syracuseStep 3101795 = 4652693) B4652693
theorem B2067863 : Blo 2067435 2067863 := bstep (se 1 (by rfl) ⟨1550897, by rfl⟩ : syracuseStep 2067863 = 3101795) B3101795
theorem B2208217 : Blo 2067435 2208217 := bbase (se 2 (by rfl) ⟨828081, by rfl⟩ : syracuseStep 2208217 = 1656163) (by norm_num)
theorem B2944289 : Blo 2067435 2944289 := bstep (se 2 (by rfl) ⟨1104108, by rfl⟩ : syracuseStep 2944289 = 2208217) B2208217
theorem B7851437 : Blo 2067435 7851437 := bstep (se 3 (by rfl) ⟨1472144, by rfl⟩ : syracuseStep 7851437 = 2944289) B2944289
theorem B5234291 : Blo 2067435 5234291 := bstep (se 1 (by rfl) ⟨3925718, by rfl⟩ : syracuseStep 5234291 = 7851437) B7851437
theorem B3489527 : Blo 2067435 3489527 := bstep (se 1 (by rfl) ⟨2617145, by rfl⟩ : syracuseStep 3489527 = 5234291) B5234291
theorem B2326351 : Blo 2067435 2326351 := bstep (se 1 (by rfl) ⟨1744763, by rfl⟩ : syracuseStep 2326351 = 3489527) B3489527
theorem B3101801 : Blo 2067435 3101801 := bstep (se 2 (by rfl) ⟨1163175, by rfl⟩ : syracuseStep 3101801 = 2326351) B2326351
theorem B2067867 : Blo 2067435 2067867 := bstep (se 1 (by rfl) ⟨1550900, by rfl⟩ : syracuseStep 2067867 = 3101801) B3101801
theorem B3726373 : Blo 2067435 3726373 := bbase (se 4 (by rfl) ⟨349347, by rfl⟩ : syracuseStep 3726373 = 698695) (by norm_num)
theorem B4968497 : Blo 2067435 4968497 := bstep (se 2 (by rfl) ⟨1863186, by rfl⟩ : syracuseStep 4968497 = 3726373) B3726373
theorem B13249325 : Blo 2067435 13249325 := bstep (se 3 (by rfl) ⟨2484248, by rfl⟩ : syracuseStep 13249325 = 4968497) B4968497
theorem B8832883 : Blo 2067435 8832883 := bstep (se 1 (by rfl) ⟨6624662, by rfl⟩ : syracuseStep 8832883 = 13249325) B13249325
theorem B11777177 : Blo 2067435 11777177 := bstep (se 2 (by rfl) ⟨4416441, by rfl⟩ : syracuseStep 11777177 = 8832883) B8832883
theorem B7851451 : Blo 2067435 7851451 := bstep (se 1 (by rfl) ⟨5888588, by rfl⟩ : syracuseStep 7851451 = 11777177) B11777177
theorem B10468601 : Blo 2067435 10468601 := bstep (se 2 (by rfl) ⟨3925725, by rfl⟩ : syracuseStep 10468601 = 7851451) B7851451
theorem B6979067 : Blo 2067435 6979067 := bstep (se 1 (by rfl) ⟨5234300, by rfl⟩ : syracuseStep 6979067 = 10468601) B10468601
theorem B4652711 : Blo 2067435 4652711 := bstep (se 1 (by rfl) ⟨3489533, by rfl⟩ : syracuseStep 4652711 = 6979067) B6979067
theorem B3101807 : Blo 2067435 3101807 := bstep (se 1 (by rfl) ⟨2326355, by rfl⟩ : syracuseStep 3101807 = 4652711) B4652711
theorem B2067871 : Blo 2067435 2067871 := bstep (se 1 (by rfl) ⟨1550903, by rfl⟩ : syracuseStep 2067871 = 3101807) B3101807
theorem B3101813 : Blo 2067435 3101813 := bbase (se 5 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 3101813 = 290795) (by norm_num)
theorem B2067875 : Blo 2067435 2067875 := bstep (se 1 (by rfl) ⟨1550906, by rfl⟩ : syracuseStep 2067875 = 3101813) B3101813
theorem B3925741 : Blo 2067435 3925741 := bbase (se 3 (by rfl) ⟨736076, by rfl⟩ : syracuseStep 3925741 = 1472153) (by norm_num)
theorem B5234321 : Blo 2067435 5234321 := bstep (se 2 (by rfl) ⟨1962870, by rfl⟩ : syracuseStep 5234321 = 3925741) B3925741
theorem B3489547 : Blo 2067435 3489547 := bstep (se 1 (by rfl) ⟨2617160, by rfl⟩ : syracuseStep 3489547 = 5234321) B5234321
theorem B4652729 : Blo 2067435 4652729 := bstep (se 2 (by rfl) ⟨1744773, by rfl⟩ : syracuseStep 4652729 = 3489547) B3489547
theorem B3101819 : Blo 2067435 3101819 := bstep (se 1 (by rfl) ⟨2326364, by rfl⟩ : syracuseStep 3101819 = 4652729) B4652729
theorem B2067879 : Blo 2067435 2067879 := bstep (se 1 (by rfl) ⟨1550909, by rfl⟩ : syracuseStep 2067879 = 3101819) B3101819
theorem B2326369 : Blo 2067435 2326369 := bbase (se 2 (by rfl) ⟨872388, by rfl⟩ : syracuseStep 2326369 = 1744777) (by norm_num)
theorem B3101825 : Blo 2067435 3101825 := bstep (se 2 (by rfl) ⟨1163184, by rfl⟩ : syracuseStep 3101825 = 2326369) B2326369
theorem B2067883 : Blo 2067435 2067883 := bstep (se 1 (by rfl) ⟨1550912, by rfl⟩ : syracuseStep 2067883 = 3101825) B3101825
theorem B5234341 : Blo 2067435 5234341 := bbase (se 4 (by rfl) ⟨490719, by rfl⟩ : syracuseStep 5234341 = 981439) (by norm_num)
theorem B6979121 : Blo 2067435 6979121 := bstep (se 2 (by rfl) ⟨2617170, by rfl⟩ : syracuseStep 6979121 = 5234341) B5234341
theorem B4652747 : Blo 2067435 4652747 := bstep (se 1 (by rfl) ⟨3489560, by rfl⟩ : syracuseStep 4652747 = 6979121) B6979121
theorem B3101831 : Blo 2067435 3101831 := bstep (se 1 (by rfl) ⟨2326373, by rfl⟩ : syracuseStep 3101831 = 4652747) B4652747
theorem B2067887 : Blo 2067435 2067887 := bstep (se 1 (by rfl) ⟨1550915, by rfl⟩ : syracuseStep 2067887 = 3101831) B3101831
theorem B3101837 : Blo 2067435 3101837 := bbase (se 3 (by rfl) ⟨581594, by rfl⟩ : syracuseStep 3101837 = 1163189) (by norm_num)
theorem B2067891 : Blo 2067435 2067891 := bstep (se 1 (by rfl) ⟨1550918, by rfl⟩ : syracuseStep 2067891 = 3101837) B3101837
theorem B4652765 : Blo 2067435 4652765 := bbase (se 3 (by rfl) ⟨872393, by rfl⟩ : syracuseStep 4652765 = 1744787) (by norm_num)
theorem B3101843 : Blo 2067435 3101843 := bstep (se 1 (by rfl) ⟨2326382, by rfl⟩ : syracuseStep 3101843 = 4652765) B4652765
theorem B2067895 : Blo 2067435 2067895 := bstep (se 1 (by rfl) ⟨1550921, by rfl⟩ : syracuseStep 2067895 = 3101843) B3101843
theorem B3489581 : Blo 2067435 3489581 := bbase (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) (by norm_num)
theorem B2326387 : Blo 2067435 2326387 := bstep (se 1 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 2326387 = 3489581) B3489581
theorem B3101849 : Blo 2067435 3101849 := bstep (se 2 (by rfl) ⟨1163193, by rfl⟩ : syracuseStep 3101849 = 2326387) B2326387
theorem B2067899 : Blo 2067435 2067899 := bstep (se 1 (by rfl) ⟨1550924, by rfl⟩ : syracuseStep 2067899 = 3101849) B3101849
theorem B2518181 : Blo 2067435 2518181 := bbase (se 4 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 2518181 = 472159) (by norm_num)
theorem B107442389 : Blo 2067435 107442389 := bstep (se 7 (by rfl) ⟨1259090, by rfl⟩ : syracuseStep 107442389 = 2518181) B2518181
theorem B71628259 : Blo 2067435 71628259 := bstep (se 1 (by rfl) ⟨53721194, by rfl⟩ : syracuseStep 71628259 = 107442389) B107442389
theorem B95504345 : Blo 2067435 95504345 := bstep (se 2 (by rfl) ⟨35814129, by rfl⟩ : syracuseStep 95504345 = 71628259) B71628259
theorem B63669563 : Blo 2067435 63669563 := bstep (se 1 (by rfl) ⟨47752172, by rfl⟩ : syracuseStep 63669563 = 95504345) B95504345
theorem B42446375 : Blo 2067435 42446375 := bstep (se 1 (by rfl) ⟨31834781, by rfl⟩ : syracuseStep 42446375 = 63669563) B63669563
theorem B28297583 : Blo 2067435 28297583 := bstep (se 1 (by rfl) ⟨21223187, by rfl⟩ : syracuseStep 28297583 = 42446375) B42446375
theorem B18865055 : Blo 2067435 18865055 := bstep (se 1 (by rfl) ⟨14148791, by rfl⟩ : syracuseStep 18865055 = 28297583) B28297583
theorem B12576703 : Blo 2067435 12576703 := bstep (se 1 (by rfl) ⟨9432527, by rfl⟩ : syracuseStep 12576703 = 18865055) B18865055
theorem B16768937 : Blo 2067435 16768937 := bstep (se 2 (by rfl) ⟨6288351, by rfl⟩ : syracuseStep 16768937 = 12576703) B12576703
theorem B11179291 : Blo 2067435 11179291 := bstep (se 1 (by rfl) ⟨8384468, by rfl⟩ : syracuseStep 11179291 = 16768937) B16768937
theorem B14905721 : Blo 2067435 14905721 := bstep (se 2 (by rfl) ⟨5589645, by rfl⟩ : syracuseStep 14905721 = 11179291) B11179291
theorem B39748589 : Blo 2067435 39748589 := bstep (se 3 (by rfl) ⟨7452860, by rfl⟩ : syracuseStep 39748589 = 14905721) B14905721
theorem B26499059 : Blo 2067435 26499059 := bstep (se 1 (by rfl) ⟨19874294, by rfl⟩ : syracuseStep 26499059 = 39748589) B39748589
theorem B17666039 : Blo 2067435 17666039 := bstep (se 1 (by rfl) ⟨13249529, by rfl⟩ : syracuseStep 17666039 = 26499059) B26499059
theorem B11777359 : Blo 2067435 11777359 := bstep (se 1 (by rfl) ⟨8833019, by rfl⟩ : syracuseStep 11777359 = 17666039) B17666039
theorem B15703145 : Blo 2067435 15703145 := bstep (se 2 (by rfl) ⟨5888679, by rfl⟩ : syracuseStep 15703145 = 11777359) B11777359
theorem B10468763 : Blo 2067435 10468763 := bstep (se 1 (by rfl) ⟨7851572, by rfl⟩ : syracuseStep 10468763 = 15703145) B15703145
theorem B6979175 : Blo 2067435 6979175 := bstep (se 1 (by rfl) ⟨5234381, by rfl⟩ : syracuseStep 6979175 = 10468763) B10468763
theorem B4652783 : Blo 2067435 4652783 := bstep (se 1 (by rfl) ⟨3489587, by rfl⟩ : syracuseStep 4652783 = 6979175) B6979175
theorem B3101855 : Blo 2067435 3101855 := bstep (se 1 (by rfl) ⟨2326391, by rfl⟩ : syracuseStep 3101855 = 4652783) B4652783
theorem B2067903 : Blo 2067435 2067903 := bstep (se 1 (by rfl) ⟨1550927, by rfl⟩ : syracuseStep 2067903 = 3101855) B3101855
theorem B3101861 : Blo 2067435 3101861 := bbase (se 4 (by rfl) ⟨290799, by rfl⟩ : syracuseStep 3101861 = 581599) (by norm_num)
theorem B2067907 : Blo 2067435 2067907 := bstep (se 1 (by rfl) ⟨1550930, by rfl⟩ : syracuseStep 2067907 = 3101861) B3101861
theorem B2617201 : Blo 2067435 2617201 := bbase (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) (by norm_num)
theorem B3489601 : Blo 2067435 3489601 := bstep (se 2 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 3489601 = 2617201) B2617201
theorem B4652801 : Blo 2067435 4652801 := bstep (se 2 (by rfl) ⟨1744800, by rfl⟩ : syracuseStep 4652801 = 3489601) B3489601
theorem B3101867 : Blo 2067435 3101867 := bstep (se 1 (by rfl) ⟨2326400, by rfl⟩ : syracuseStep 3101867 = 4652801) B4652801
theorem B2067911 : Blo 2067435 2067911 := bstep (se 1 (by rfl) ⟨1550933, by rfl⟩ : syracuseStep 2067911 = 3101867) B3101867
theorem B2326405 : Blo 2067435 2326405 := bbase (se 4 (by rfl) ⟨218100, by rfl⟩ : syracuseStep 2326405 = 436201) (by norm_num)
theorem B3101873 : Blo 2067435 3101873 := bstep (se 2 (by rfl) ⟨1163202, by rfl⟩ : syracuseStep 3101873 = 2326405) B2326405
theorem B2067915 : Blo 2067435 2067915 := bstep (se 1 (by rfl) ⟨1550936, by rfl⟩ : syracuseStep 2067915 = 3101873) B3101873
theorem B3726461 : Blo 2067435 3726461 := bbase (se 3 (by rfl) ⟨698711, by rfl⟩ : syracuseStep 3726461 = 1397423) (by norm_num)
theorem B2484307 : Blo 2067435 2484307 := bstep (se 1 (by rfl) ⟨1863230, by rfl⟩ : syracuseStep 2484307 = 3726461) B3726461
theorem B3312409 : Blo 2067435 3312409 := bstep (se 2 (by rfl) ⟨1242153, by rfl⟩ : syracuseStep 3312409 = 2484307) B2484307
theorem B4416545 : Blo 2067435 4416545 := bstep (se 2 (by rfl) ⟨1656204, by rfl⟩ : syracuseStep 4416545 = 3312409) B3312409
theorem B2944363 : Blo 2067435 2944363 := bstep (se 1 (by rfl) ⟨2208272, by rfl⟩ : syracuseStep 2944363 = 4416545) B4416545
theorem B3925817 : Blo 2067435 3925817 := bstep (se 2 (by rfl) ⟨1472181, by rfl⟩ : syracuseStep 3925817 = 2944363) B2944363
theorem B2617211 : Blo 2067435 2617211 := bstep (se 1 (by rfl) ⟨1962908, by rfl⟩ : syracuseStep 2617211 = 3925817) B3925817
theorem B6979229 : Blo 2067435 6979229 := bstep (se 3 (by rfl) ⟨1308605, by rfl⟩ : syracuseStep 6979229 = 2617211) B2617211
theorem B4652819 : Blo 2067435 4652819 := bstep (se 1 (by rfl) ⟨3489614, by rfl⟩ : syracuseStep 4652819 = 6979229) B6979229
theorem B3101879 : Blo 2067435 3101879 := bstep (se 1 (by rfl) ⟨2326409, by rfl⟩ : syracuseStep 3101879 = 4652819) B4652819
theorem B2067919 : Blo 2067435 2067919 := bstep (se 1 (by rfl) ⟨1550939, by rfl⟩ : syracuseStep 2067919 = 3101879) B3101879
theorem B3101885 : Blo 2067435 3101885 := bbase (se 3 (by rfl) ⟨581603, by rfl⟩ : syracuseStep 3101885 = 1163207) (by norm_num)
theorem B2067923 : Blo 2067435 2067923 := bstep (se 1 (by rfl) ⟨1550942, by rfl⟩ : syracuseStep 2067923 = 3101885) B3101885
theorem B4652837 : Blo 2067435 4652837 := bbase (se 4 (by rfl) ⟨436203, by rfl⟩ : syracuseStep 4652837 = 872407) (by norm_num)
theorem B3101891 : Blo 2067435 3101891 := bstep (se 1 (by rfl) ⟨2326418, by rfl⟩ : syracuseStep 3101891 = 4652837) B4652837
theorem B2067927 : Blo 2067435 2067927 := bstep (se 1 (by rfl) ⟨1550945, by rfl⟩ : syracuseStep 2067927 = 3101891) B3101891
theorem B5234453 : Blo 2067435 5234453 := bbase (se 6 (by rfl) ⟨122682, by rfl⟩ : syracuseStep 5234453 = 245365) (by norm_num)
theorem B3489635 : Blo 2067435 3489635 := bstep (se 1 (by rfl) ⟨2617226, by rfl⟩ : syracuseStep 3489635 = 5234453) B5234453
theorem B2326423 : Blo 2067435 2326423 := bstep (se 1 (by rfl) ⟨1744817, by rfl⟩ : syracuseStep 2326423 = 3489635) B3489635
theorem B3101897 : Blo 2067435 3101897 := bstep (se 2 (by rfl) ⟨1163211, by rfl⟩ : syracuseStep 3101897 = 2326423) B2326423
theorem B2067931 : Blo 2067435 2067931 := bstep (se 1 (by rfl) ⟨1550948, by rfl⟩ : syracuseStep 2067931 = 3101897) B3101897
theorem B8833157 : Blo 2067435 8833157 := bbase (se 4 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 8833157 = 1656217) (by norm_num)
theorem B5888771 : Blo 2067435 5888771 := bstep (se 1 (by rfl) ⟨4416578, by rfl⟩ : syracuseStep 5888771 = 8833157) B8833157
theorem B3925847 : Blo 2067435 3925847 := bstep (se 1 (by rfl) ⟨2944385, by rfl⟩ : syracuseStep 3925847 = 5888771) B5888771
theorem B10468925 : Blo 2067435 10468925 := bstep (se 3 (by rfl) ⟨1962923, by rfl⟩ : syracuseStep 10468925 = 3925847) B3925847
theorem B6979283 : Blo 2067435 6979283 := bstep (se 1 (by rfl) ⟨5234462, by rfl⟩ : syracuseStep 6979283 = 10468925) B10468925
theorem B4652855 : Blo 2067435 4652855 := bstep (se 1 (by rfl) ⟨3489641, by rfl⟩ : syracuseStep 4652855 = 6979283) B6979283
theorem B3101903 : Blo 2067435 3101903 := bstep (se 1 (by rfl) ⟨2326427, by rfl⟩ : syracuseStep 3101903 = 4652855) B4652855
theorem B2067935 : Blo 2067435 2067935 := bstep (se 1 (by rfl) ⟨1550951, by rfl⟩ : syracuseStep 2067935 = 3101903) B3101903
theorem B3101909 : Blo 2067435 3101909 := bbase (se 7 (by rfl) ⟨36350, by rfl⟩ : syracuseStep 3101909 = 72701) (by norm_num)
theorem B2067939 : Blo 2067435 2067939 := bstep (se 1 (by rfl) ⟨1550954, by rfl⟩ : syracuseStep 2067939 = 3101909) B3101909
theorem B2944397 : Blo 2067435 2944397 := bbase (se 3 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 2944397 = 1104149) (by norm_num)
theorem B7851725 : Blo 2067435 7851725 := bstep (se 3 (by rfl) ⟨1472198, by rfl⟩ : syracuseStep 7851725 = 2944397) B2944397
theorem B5234483 : Blo 2067435 5234483 := bstep (se 1 (by rfl) ⟨3925862, by rfl⟩ : syracuseStep 5234483 = 7851725) B7851725
theorem B3489655 : Blo 2067435 3489655 := bstep (se 1 (by rfl) ⟨2617241, by rfl⟩ : syracuseStep 3489655 = 5234483) B5234483
theorem B4652873 : Blo 2067435 4652873 := bstep (se 2 (by rfl) ⟨1744827, by rfl⟩ : syracuseStep 4652873 = 3489655) B3489655
theorem B3101915 : Blo 2067435 3101915 := bstep (se 1 (by rfl) ⟨2326436, by rfl⟩ : syracuseStep 3101915 = 4652873) B4652873
theorem B2067943 : Blo 2067435 2067943 := bstep (se 1 (by rfl) ⟨1550957, by rfl⟩ : syracuseStep 2067943 = 3101915) B3101915
theorem B2326441 : Blo 2067435 2326441 := bbase (se 2 (by rfl) ⟨872415, by rfl⟩ : syracuseStep 2326441 = 1744831) (by norm_num)
theorem B3101921 : Blo 2067435 3101921 := bstep (se 2 (by rfl) ⟨1163220, by rfl⟩ : syracuseStep 3101921 = 2326441) B2326441
theorem B2067947 : Blo 2067435 2067947 := bstep (se 1 (by rfl) ⟨1550960, by rfl⟩ : syracuseStep 2067947 = 3101921) B3101921
theorem B14906069 : Blo 2067435 14906069 := bbase (se 7 (by rfl) ⟨174680, by rfl⟩ : syracuseStep 14906069 = 349361) (by norm_num)
theorem B9937379 : Blo 2067435 9937379 := bstep (se 1 (by rfl) ⟨7453034, by rfl⟩ : syracuseStep 9937379 = 14906069) B14906069
theorem B6624919 : Blo 2067435 6624919 := bstep (se 1 (by rfl) ⟨4968689, by rfl⟩ : syracuseStep 6624919 = 9937379) B9937379
theorem B8833225 : Blo 2067435 8833225 := bstep (se 2 (by rfl) ⟨3312459, by rfl⟩ : syracuseStep 8833225 = 6624919) B6624919
theorem B11777633 : Blo 2067435 11777633 := bstep (se 2 (by rfl) ⟨4416612, by rfl⟩ : syracuseStep 11777633 = 8833225) B8833225
theorem B7851755 : Blo 2067435 7851755 := bstep (se 1 (by rfl) ⟨5888816, by rfl⟩ : syracuseStep 7851755 = 11777633) B11777633
theorem B5234503 : Blo 2067435 5234503 := bstep (se 1 (by rfl) ⟨3925877, by rfl⟩ : syracuseStep 5234503 = 7851755) B7851755
theorem B6979337 : Blo 2067435 6979337 := bstep (se 2 (by rfl) ⟨2617251, by rfl⟩ : syracuseStep 6979337 = 5234503) B5234503
theorem B4652891 : Blo 2067435 4652891 := bstep (se 1 (by rfl) ⟨3489668, by rfl⟩ : syracuseStep 4652891 = 6979337) B6979337
theorem B3101927 : Blo 2067435 3101927 := bstep (se 1 (by rfl) ⟨2326445, by rfl⟩ : syracuseStep 3101927 = 4652891) B4652891
theorem B2067951 : Blo 2067435 2067951 := bstep (se 1 (by rfl) ⟨1550963, by rfl⟩ : syracuseStep 2067951 = 3101927) B3101927
theorem B3101933 : Blo 2067435 3101933 := bbase (se 3 (by rfl) ⟨581612, by rfl⟩ : syracuseStep 3101933 = 1163225) (by norm_num)
theorem B2067955 : Blo 2067435 2067955 := bstep (se 1 (by rfl) ⟨1550966, by rfl⟩ : syracuseStep 2067955 = 3101933) B3101933
theorem B4652909 : Blo 2067435 4652909 := bbase (se 3 (by rfl) ⟨872420, by rfl⟩ : syracuseStep 4652909 = 1744841) (by norm_num)
theorem B3101939 : Blo 2067435 3101939 := bstep (se 1 (by rfl) ⟨2326454, by rfl⟩ : syracuseStep 3101939 = 4652909) B4652909
theorem B2067959 : Blo 2067435 2067959 := bstep (se 1 (by rfl) ⟨1550969, by rfl⟩ : syracuseStep 2067959 = 3101939) B3101939
theorem B3925901 : Blo 2067435 3925901 := bbase (se 3 (by rfl) ⟨736106, by rfl⟩ : syracuseStep 3925901 = 1472213) (by norm_num)
theorem B2617267 : Blo 2067435 2617267 := bstep (se 1 (by rfl) ⟨1962950, by rfl⟩ : syracuseStep 2617267 = 3925901) B3925901
theorem B3489689 : Blo 2067435 3489689 := bstep (se 2 (by rfl) ⟨1308633, by rfl⟩ : syracuseStep 3489689 = 2617267) B2617267
theorem B2326459 : Blo 2067435 2326459 := bstep (se 1 (by rfl) ⟨1744844, by rfl⟩ : syracuseStep 2326459 = 3489689) B3489689
theorem B3101945 : Blo 2067435 3101945 := bstep (se 2 (by rfl) ⟨1163229, by rfl⟩ : syracuseStep 3101945 = 2326459) B2326459
theorem B2067963 : Blo 2067435 2067963 := bstep (se 1 (by rfl) ⟨1550972, by rfl⟩ : syracuseStep 2067963 = 3101945) B3101945
theorem B11179637 : Blo 2067435 11179637 := bbase (se 5 (by rfl) ⟨524045, by rfl⟩ : syracuseStep 11179637 = 1048091) (by norm_num)
theorem B7453091 : Blo 2067435 7453091 := bstep (se 1 (by rfl) ⟨5589818, by rfl⟩ : syracuseStep 7453091 = 11179637) B11179637
theorem B19874909 : Blo 2067435 19874909 := bstep (se 3 (by rfl) ⟨3726545, by rfl⟩ : syracuseStep 19874909 = 7453091) B7453091
theorem B52999757 : Blo 2067435 52999757 := bstep (se 3 (by rfl) ⟨9937454, by rfl⟩ : syracuseStep 52999757 = 19874909) B19874909
theorem B35333171 : Blo 2067435 35333171 := bstep (se 1 (by rfl) ⟨26499878, by rfl⟩ : syracuseStep 35333171 = 52999757) B52999757
theorem B23555447 : Blo 2067435 23555447 := bstep (se 1 (by rfl) ⟨17666585, by rfl⟩ : syracuseStep 23555447 = 35333171) B35333171
theorem B15703631 : Blo 2067435 15703631 := bstep (se 1 (by rfl) ⟨11777723, by rfl⟩ : syracuseStep 15703631 = 23555447) B23555447
theorem B10469087 : Blo 2067435 10469087 := bstep (se 1 (by rfl) ⟨7851815, by rfl⟩ : syracuseStep 10469087 = 15703631) B15703631
theorem B6979391 : Blo 2067435 6979391 := bstep (se 1 (by rfl) ⟨5234543, by rfl⟩ : syracuseStep 6979391 = 10469087) B10469087
theorem B4652927 : Blo 2067435 4652927 := bstep (se 1 (by rfl) ⟨3489695, by rfl⟩ : syracuseStep 4652927 = 6979391) B6979391
theorem B3101951 : Blo 2067435 3101951 := bstep (se 1 (by rfl) ⟨2326463, by rfl⟩ : syracuseStep 3101951 = 4652927) B4652927
theorem B2067967 : Blo 2067435 2067967 := bstep (se 1 (by rfl) ⟨1550975, by rfl⟩ : syracuseStep 2067967 = 3101951) B3101951
theorem B3101957 : Blo 2067435 3101957 := bbase (se 4 (by rfl) ⟨290808, by rfl⟩ : syracuseStep 3101957 = 581617) (by norm_num)
theorem B2067971 : Blo 2067435 2067971 := bstep (se 1 (by rfl) ⟨1550978, by rfl⟩ : syracuseStep 2067971 = 3101957) B3101957
theorem B3489709 : Blo 2067435 3489709 := bbase (se 3 (by rfl) ⟨654320, by rfl⟩ : syracuseStep 3489709 = 1308641) (by norm_num)
theorem B4652945 : Blo 2067435 4652945 := bstep (se 2 (by rfl) ⟨1744854, by rfl⟩ : syracuseStep 4652945 = 3489709) B3489709
theorem B3101963 : Blo 2067435 3101963 := bstep (se 1 (by rfl) ⟨2326472, by rfl⟩ : syracuseStep 3101963 = 4652945) B4652945
theorem B2067975 : Blo 2067435 2067975 := bstep (se 1 (by rfl) ⟨1550981, by rfl⟩ : syracuseStep 2067975 = 3101963) B3101963
theorem B2326477 : Blo 2067435 2326477 := bbase (se 3 (by rfl) ⟨436214, by rfl⟩ : syracuseStep 2326477 = 872429) (by norm_num)
theorem B3101969 : Blo 2067435 3101969 := bstep (se 2 (by rfl) ⟨1163238, by rfl⟩ : syracuseStep 3101969 = 2326477) B2326477
theorem B2067979 : Blo 2067435 2067979 := bstep (se 1 (by rfl) ⟨1550984, by rfl⟩ : syracuseStep 2067979 = 3101969) B3101969
theorem B6979445 : Blo 2067435 6979445 := bbase (se 5 (by rfl) ⟨327161, by rfl⟩ : syracuseStep 6979445 = 654323) (by norm_num)
theorem B4652963 : Blo 2067435 4652963 := bstep (se 1 (by rfl) ⟨3489722, by rfl⟩ : syracuseStep 4652963 = 6979445) B6979445
theorem B3101975 : Blo 2067435 3101975 := bstep (se 1 (by rfl) ⟨2326481, by rfl⟩ : syracuseStep 3101975 = 4652963) B4652963
theorem B2067983 : Blo 2067435 2067983 := bstep (se 1 (by rfl) ⟨1550987, by rfl⟩ : syracuseStep 2067983 = 3101975) B3101975
theorem B3101981 : Blo 2067435 3101981 := bbase (se 3 (by rfl) ⟨581621, by rfl⟩ : syracuseStep 3101981 = 1163243) (by norm_num)
theorem B2067987 : Blo 2067435 2067987 := bstep (se 1 (by rfl) ⟨1550990, by rfl⟩ : syracuseStep 2067987 = 3101981) B3101981
theorem B4652981 : Blo 2067435 4652981 := bbase (se 5 (by rfl) ⟨218108, by rfl⟩ : syracuseStep 4652981 = 436217) (by norm_num)
theorem B3101987 : Blo 2067435 3101987 := bstep (se 1 (by rfl) ⟨2326490, by rfl⟩ : syracuseStep 3101987 = 4652981) B4652981
theorem B2067991 : Blo 2067435 2067991 := bstep (se 1 (by rfl) ⟨1550993, by rfl⟩ : syracuseStep 2067991 = 3101987) B3101987
theorem B6625061 : Blo 2067435 6625061 := bbase (se 4 (by rfl) ⟨621099, by rfl⟩ : syracuseStep 6625061 = 1242199) (by norm_num)
theorem B4416707 : Blo 2067435 4416707 := bstep (se 1 (by rfl) ⟨3312530, by rfl⟩ : syracuseStep 4416707 = 6625061) B6625061
theorem B11777885 : Blo 2067435 11777885 := bstep (se 3 (by rfl) ⟨2208353, by rfl⟩ : syracuseStep 11777885 = 4416707) B4416707
theorem B7851923 : Blo 2067435 7851923 := bstep (se 1 (by rfl) ⟨5888942, by rfl⟩ : syracuseStep 7851923 = 11777885) B11777885
theorem B5234615 : Blo 2067435 5234615 := bstep (se 1 (by rfl) ⟨3925961, by rfl⟩ : syracuseStep 5234615 = 7851923) B7851923
theorem B3489743 : Blo 2067435 3489743 := bstep (se 1 (by rfl) ⟨2617307, by rfl⟩ : syracuseStep 3489743 = 5234615) B5234615
theorem B2326495 : Blo 2067435 2326495 := bstep (se 1 (by rfl) ⟨1744871, by rfl⟩ : syracuseStep 2326495 = 3489743) B3489743
theorem B3101993 : Blo 2067435 3101993 := bstep (se 2 (by rfl) ⟨1163247, by rfl⟩ : syracuseStep 3101993 = 2326495) B2326495
theorem B2067995 : Blo 2067435 2067995 := bstep (se 1 (by rfl) ⟨1550996, by rfl⟩ : syracuseStep 2067995 = 3101993) B3101993
theorem B4968805 : Blo 2067435 4968805 := bbase (se 4 (by rfl) ⟨465825, by rfl⟩ : syracuseStep 4968805 = 931651) (by norm_num)
theorem B6625073 : Blo 2067435 6625073 := bstep (se 2 (by rfl) ⟨2484402, by rfl⟩ : syracuseStep 6625073 = 4968805) B4968805
theorem B4416715 : Blo 2067435 4416715 := bstep (se 1 (by rfl) ⟨3312536, by rfl⟩ : syracuseStep 4416715 = 6625073) B6625073
theorem B5888953 : Blo 2067435 5888953 := bstep (se 2 (by rfl) ⟨2208357, by rfl⟩ : syracuseStep 5888953 = 4416715) B4416715
theorem B7851937 : Blo 2067435 7851937 := bstep (se 2 (by rfl) ⟨2944476, by rfl⟩ : syracuseStep 7851937 = 5888953) B5888953
theorem B10469249 : Blo 2067435 10469249 := bstep (se 2 (by rfl) ⟨3925968, by rfl⟩ : syracuseStep 10469249 = 7851937) B7851937
theorem B6979499 : Blo 2067435 6979499 := bstep (se 1 (by rfl) ⟨5234624, by rfl⟩ : syracuseStep 6979499 = 10469249) B10469249
theorem B4652999 : Blo 2067435 4652999 := bstep (se 1 (by rfl) ⟨3489749, by rfl⟩ : syracuseStep 4652999 = 6979499) B6979499
theorem B3101999 : Blo 2067435 3101999 := bstep (se 1 (by rfl) ⟨2326499, by rfl⟩ : syracuseStep 3101999 = 4652999) B4652999
theorem B2067999 : Blo 2067435 2067999 := bstep (se 1 (by rfl) ⟨1550999, by rfl⟩ : syracuseStep 2067999 = 3101999) B3101999
theorem B3102005 : Blo 2067435 3102005 := bbase (se 5 (by rfl) ⟨145406, by rfl⟩ : syracuseStep 3102005 = 290813) (by norm_num)
theorem B2068003 : Blo 2067435 2068003 := bstep (se 1 (by rfl) ⟨1551002, by rfl⟩ : syracuseStep 2068003 = 3102005) B3102005
theorem B5234645 : Blo 2067435 5234645 := bbase (se 7 (by rfl) ⟨61343, by rfl⟩ : syracuseStep 5234645 = 122687) (by norm_num)
theorem B3489763 : Blo 2067435 3489763 := bstep (se 1 (by rfl) ⟨2617322, by rfl⟩ : syracuseStep 3489763 = 5234645) B5234645
theorem B4653017 : Blo 2067435 4653017 := bstep (se 2 (by rfl) ⟨1744881, by rfl⟩ : syracuseStep 4653017 = 3489763) B3489763
theorem B3102011 : Blo 2067435 3102011 := bstep (se 1 (by rfl) ⟨2326508, by rfl⟩ : syracuseStep 3102011 = 4653017) B4653017
theorem B2068007 : Blo 2067435 2068007 := bstep (se 1 (by rfl) ⟨1551005, by rfl⟩ : syracuseStep 2068007 = 3102011) B3102011
theorem B2326513 : Blo 2067435 2326513 := bbase (se 2 (by rfl) ⟨872442, by rfl⟩ : syracuseStep 2326513 = 1744885) (by norm_num)
theorem B3102017 : Blo 2067435 3102017 := bstep (se 2 (by rfl) ⟨1163256, by rfl⟩ : syracuseStep 3102017 = 2326513) B2326513
theorem B2068011 : Blo 2067435 2068011 := bstep (se 1 (by rfl) ⟨1551008, by rfl⟩ : syracuseStep 2068011 = 3102017) B3102017
theorem B290437973 : Blo 2067435 290437973 := bbase (se 9 (by rfl) ⟨850892, by rfl⟩ : syracuseStep 290437973 = 1701785) (by norm_num)
theorem B193625315 : Blo 2067435 193625315 := bstep (se 1 (by rfl) ⟨145218986, by rfl⟩ : syracuseStep 193625315 = 290437973) B290437973
theorem B129083543 : Blo 2067435 129083543 := bstep (se 1 (by rfl) ⟨96812657, by rfl⟩ : syracuseStep 129083543 = 193625315) B193625315
theorem B86055695 : Blo 2067435 86055695 := bstep (se 1 (by rfl) ⟨64541771, by rfl⟩ : syracuseStep 86055695 = 129083543) B129083543
theorem B57370463 : Blo 2067435 57370463 := bstep (se 1 (by rfl) ⟨43027847, by rfl⟩ : syracuseStep 57370463 = 86055695) B86055695
theorem B38246975 : Blo 2067435 38246975 := bstep (se 1 (by rfl) ⟨28685231, by rfl⟩ : syracuseStep 38246975 = 57370463) B57370463
theorem B25497983 : Blo 2067435 25497983 := bstep (se 1 (by rfl) ⟨19123487, by rfl⟩ : syracuseStep 25497983 = 38246975) B38246975
theorem B16998655 : Blo 2067435 16998655 := bstep (se 1 (by rfl) ⟨12748991, by rfl⟩ : syracuseStep 16998655 = 25497983) B25497983
theorem B22664873 : Blo 2067435 22664873 := bstep (se 2 (by rfl) ⟨8499327, by rfl⟩ : syracuseStep 22664873 = 16998655) B16998655
theorem B15109915 : Blo 2067435 15109915 := bstep (se 1 (by rfl) ⟨11332436, by rfl⟩ : syracuseStep 15109915 = 22664873) B22664873
theorem B20146553 : Blo 2067435 20146553 := bstep (se 2 (by rfl) ⟨7554957, by rfl⟩ : syracuseStep 20146553 = 15109915) B15109915
theorem B13431035 : Blo 2067435 13431035 := bstep (se 1 (by rfl) ⟨10073276, by rfl⟩ : syracuseStep 13431035 = 20146553) B20146553
theorem B8954023 : Blo 2067435 8954023 := bstep (se 1 (by rfl) ⟨6715517, by rfl⟩ : syracuseStep 8954023 = 13431035) B13431035
theorem B11938697 : Blo 2067435 11938697 := bstep (se 2 (by rfl) ⟨4477011, by rfl⟩ : syracuseStep 11938697 = 8954023) B8954023
theorem B7959131 : Blo 2067435 7959131 := bstep (se 1 (by rfl) ⟨5969348, by rfl⟩ : syracuseStep 7959131 = 11938697) B11938697
theorem B5306087 : Blo 2067435 5306087 := bstep (se 1 (by rfl) ⟨3979565, by rfl⟩ : syracuseStep 5306087 = 7959131) B7959131
theorem B3537391 : Blo 2067435 3537391 := bstep (se 1 (by rfl) ⟨2653043, by rfl⟩ : syracuseStep 3537391 = 5306087) B5306087
theorem B4716521 : Blo 2067435 4716521 := bstep (se 2 (by rfl) ⟨1768695, by rfl⟩ : syracuseStep 4716521 = 3537391) B3537391
theorem B3144347 : Blo 2067435 3144347 := bstep (se 1 (by rfl) ⟨2358260, by rfl⟩ : syracuseStep 3144347 = 4716521) B4716521
theorem B2096231 : Blo 2067435 2096231 := bstep (se 1 (by rfl) ⟨1572173, by rfl⟩ : syracuseStep 2096231 = 3144347) B3144347
theorem B22359797 : Blo 2067435 22359797 := bstep (se 5 (by rfl) ⟨1048115, by rfl⟩ : syracuseStep 22359797 = 2096231) B2096231
theorem B14906531 : Blo 2067435 14906531 := bstep (se 1 (by rfl) ⟨11179898, by rfl⟩ : syracuseStep 14906531 = 22359797) B22359797
theorem B9937687 : Blo 2067435 9937687 := bstep (se 1 (by rfl) ⟨7453265, by rfl⟩ : syracuseStep 9937687 = 14906531) B14906531
theorem B13250249 : Blo 2067435 13250249 := bstep (se 2 (by rfl) ⟨4968843, by rfl⟩ : syracuseStep 13250249 = 9937687) B9937687
theorem B8833499 : Blo 2067435 8833499 := bstep (se 1 (by rfl) ⟨6625124, by rfl⟩ : syracuseStep 8833499 = 13250249) B13250249
theorem B5888999 : Blo 2067435 5888999 := bstep (se 1 (by rfl) ⟨4416749, by rfl⟩ : syracuseStep 5888999 = 8833499) B8833499
theorem B3925999 : Blo 2067435 3925999 := bstep (se 1 (by rfl) ⟨2944499, by rfl⟩ : syracuseStep 3925999 = 5888999) B5888999
theorem B5234665 : Blo 2067435 5234665 := bstep (se 2 (by rfl) ⟨1962999, by rfl⟩ : syracuseStep 5234665 = 3925999) B3925999
theorem B6979553 : Blo 2067435 6979553 := bstep (se 2 (by rfl) ⟨2617332, by rfl⟩ : syracuseStep 6979553 = 5234665) B5234665
theorem B4653035 : Blo 2067435 4653035 := bstep (se 1 (by rfl) ⟨3489776, by rfl⟩ : syracuseStep 4653035 = 6979553) B6979553
theorem B3102023 : Blo 2067435 3102023 := bstep (se 1 (by rfl) ⟨2326517, by rfl⟩ : syracuseStep 3102023 = 4653035) B4653035
theorem B2068015 : Blo 2067435 2068015 := bstep (se 1 (by rfl) ⟨1551011, by rfl⟩ : syracuseStep 2068015 = 3102023) B3102023
theorem B3102029 : Blo 2067435 3102029 := bbase (se 3 (by rfl) ⟨581630, by rfl⟩ : syracuseStep 3102029 = 1163261) (by norm_num)
theorem B2068019 : Blo 2067435 2068019 := bstep (se 1 (by rfl) ⟨1551014, by rfl⟩ : syracuseStep 2068019 = 3102029) B3102029
theorem B4653053 : Blo 2067435 4653053 := bbase (se 3 (by rfl) ⟨872447, by rfl⟩ : syracuseStep 4653053 = 1744895) (by norm_num)
theorem B3102035 : Blo 2067435 3102035 := bstep (se 1 (by rfl) ⟨2326526, by rfl⟩ : syracuseStep 3102035 = 4653053) B4653053
theorem B2068023 : Blo 2067435 2068023 := bstep (se 1 (by rfl) ⟨1551017, by rfl⟩ : syracuseStep 2068023 = 3102035) B3102035
theorem B3489797 : Blo 2067435 3489797 := bbase (se 4 (by rfl) ⟨327168, by rfl⟩ : syracuseStep 3489797 = 654337) (by norm_num)
theorem B2326531 : Blo 2067435 2326531 := bstep (se 1 (by rfl) ⟨1744898, by rfl⟩ : syracuseStep 2326531 = 3489797) B3489797
theorem B3102041 : Blo 2067435 3102041 := bstep (se 2 (by rfl) ⟨1163265, by rfl⟩ : syracuseStep 3102041 = 2326531) B2326531
theorem B2068027 : Blo 2067435 2068027 := bstep (se 1 (by rfl) ⟨1551020, by rfl⟩ : syracuseStep 2068027 = 3102041) B3102041
theorem B15704117 : Blo 2067435 15704117 := bbase (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) (by norm_num)
theorem B10469411 : Blo 2067435 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B6979607 : Blo 2067435 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B4653071 : Blo 2067435 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B3102047 : Blo 2067435 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B2068031 : Blo 2067435 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B3102053 : Blo 2067435 3102053 := bbase (se 4 (by rfl) ⟨290817, by rfl⟩ : syracuseStep 3102053 = 581635) (by norm_num)
theorem B2068035 : Blo 2067435 2068035 := bstep (se 1 (by rfl) ⟨1551026, by rfl⟩ : syracuseStep 2068035 = 3102053) B3102053
theorem B3926045 : Blo 2067435 3926045 := bbase (se 3 (by rfl) ⟨736133, by rfl⟩ : syracuseStep 3926045 = 1472267) (by norm_num)
theorem B2617363 : Blo 2067435 2617363 := bstep (se 1 (by rfl) ⟨1963022, by rfl⟩ : syracuseStep 2617363 = 3926045) B3926045
theorem B3489817 : Blo 2067435 3489817 := bstep (se 2 (by rfl) ⟨1308681, by rfl⟩ : syracuseStep 3489817 = 2617363) B2617363
theorem B4653089 : Blo 2067435 4653089 := bstep (se 2 (by rfl) ⟨1744908, by rfl⟩ : syracuseStep 4653089 = 3489817) B3489817
theorem B3102059 : Blo 2067435 3102059 := bstep (se 1 (by rfl) ⟨2326544, by rfl⟩ : syracuseStep 3102059 = 4653089) B4653089
theorem B2068039 : Blo 2067435 2068039 := bstep (se 1 (by rfl) ⟨1551029, by rfl⟩ : syracuseStep 2068039 = 3102059) B3102059
theorem B2326549 : Blo 2067435 2326549 := bbase (se 6 (by rfl) ⟨54528, by rfl⟩ : syracuseStep 2326549 = 109057) (by norm_num)
theorem B3102065 : Blo 2067435 3102065 := bstep (se 2 (by rfl) ⟨1163274, by rfl⟩ : syracuseStep 3102065 = 2326549) B2326549
theorem B2068043 : Blo 2067435 2068043 := bstep (se 1 (by rfl) ⟨1551032, by rfl⟩ : syracuseStep 2068043 = 3102065) B3102065
theorem B2617373 : Blo 2067435 2617373 := bbase (se 3 (by rfl) ⟨490757, by rfl⟩ : syracuseStep 2617373 = 981515) (by norm_num)
theorem B6979661 : Blo 2067435 6979661 := bstep (se 3 (by rfl) ⟨1308686, by rfl⟩ : syracuseStep 6979661 = 2617373) B2617373
theorem B4653107 : Blo 2067435 4653107 := bstep (se 1 (by rfl) ⟨3489830, by rfl⟩ : syracuseStep 4653107 = 6979661) B6979661
theorem B3102071 : Blo 2067435 3102071 := bstep (se 1 (by rfl) ⟨2326553, by rfl⟩ : syracuseStep 3102071 = 4653107) B4653107
theorem B2068047 : Blo 2067435 2068047 := bstep (se 1 (by rfl) ⟨1551035, by rfl⟩ : syracuseStep 2068047 = 3102071) B3102071
theorem B3102077 : Blo 2067435 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B2068051 : Blo 2067435 2068051 := bstep (se 1 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 2068051 = 3102077) B3102077
theorem B4653125 : Blo 2067435 4653125 := bbase (se 4 (by rfl) ⟨436230, by rfl⟩ : syracuseStep 4653125 = 872461) (by norm_num)
theorem B3102083 : Blo 2067435 3102083 := bstep (se 1 (by rfl) ⟨2326562, by rfl⟩ : syracuseStep 3102083 = 4653125) B4653125
theorem B2068055 : Blo 2067435 2068055 := bstep (se 1 (by rfl) ⟨1551041, by rfl⟩ : syracuseStep 2068055 = 3102083) B3102083
theorem B5889125 : Blo 2067435 5889125 := bbase (se 4 (by rfl) ⟨552105, by rfl⟩ : syracuseStep 5889125 = 1104211) (by norm_num)
theorem B3926083 : Blo 2067435 3926083 := bstep (se 1 (by rfl) ⟨2944562, by rfl⟩ : syracuseStep 3926083 = 5889125) B5889125
theorem B5234777 : Blo 2067435 5234777 := bstep (se 2 (by rfl) ⟨1963041, by rfl⟩ : syracuseStep 5234777 = 3926083) B3926083
theorem B3489851 : Blo 2067435 3489851 := bstep (se 1 (by rfl) ⟨2617388, by rfl⟩ : syracuseStep 3489851 = 5234777) B5234777
theorem B2326567 : Blo 2067435 2326567 := bstep (se 1 (by rfl) ⟨1744925, by rfl⟩ : syracuseStep 2326567 = 3489851) B3489851
theorem B3102089 : Blo 2067435 3102089 := bstep (se 2 (by rfl) ⟨1163283, by rfl⟩ : syracuseStep 3102089 = 2326567) B2326567
theorem B2068059 : Blo 2067435 2068059 := bstep (se 1 (by rfl) ⟨1551044, by rfl⟩ : syracuseStep 2068059 = 3102089) B3102089
theorem B10469573 : Blo 2067435 10469573 := bbase (se 4 (by rfl) ⟨981522, by rfl⟩ : syracuseStep 10469573 = 1963045) (by norm_num)
theorem B6979715 : Blo 2067435 6979715 := bstep (se 1 (by rfl) ⟨5234786, by rfl⟩ : syracuseStep 6979715 = 10469573) B10469573
theorem B4653143 : Blo 2067435 4653143 := bstep (se 1 (by rfl) ⟨3489857, by rfl⟩ : syracuseStep 4653143 = 6979715) B6979715
theorem B3102095 : Blo 2067435 3102095 := bstep (se 1 (by rfl) ⟨2326571, by rfl⟩ : syracuseStep 3102095 = 4653143) B4653143
theorem B2068063 : Blo 2067435 2068063 := bstep (se 1 (by rfl) ⟨1551047, by rfl⟩ : syracuseStep 2068063 = 3102095) B3102095
theorem B3102101 : Blo 2067435 3102101 := bbase (se 6 (by rfl) ⟨72705, by rfl⟩ : syracuseStep 3102101 = 145411) (by norm_num)
theorem B2068067 : Blo 2067435 2068067 := bstep (se 1 (by rfl) ⟨1551050, by rfl⟩ : syracuseStep 2068067 = 3102101) B3102101
theorem B4416869 : Blo 2067435 4416869 := bbase (se 4 (by rfl) ⟨414081, by rfl⟩ : syracuseStep 4416869 = 828163) (by norm_num)
theorem B11778317 : Blo 2067435 11778317 := bstep (se 3 (by rfl) ⟨2208434, by rfl⟩ : syracuseStep 11778317 = 4416869) B4416869
theorem B7852211 : Blo 2067435 7852211 := bstep (se 1 (by rfl) ⟨5889158, by rfl⟩ : syracuseStep 7852211 = 11778317) B11778317
theorem B5234807 : Blo 2067435 5234807 := bstep (se 1 (by rfl) ⟨3926105, by rfl⟩ : syracuseStep 5234807 = 7852211) B7852211
theorem B3489871 : Blo 2067435 3489871 := bstep (se 1 (by rfl) ⟨2617403, by rfl⟩ : syracuseStep 3489871 = 5234807) B5234807
theorem B4653161 : Blo 2067435 4653161 := bstep (se 2 (by rfl) ⟨1744935, by rfl⟩ : syracuseStep 4653161 = 3489871) B3489871
theorem B3102107 : Blo 2067435 3102107 := bstep (se 1 (by rfl) ⟨2326580, by rfl⟩ : syracuseStep 3102107 = 4653161) B4653161
theorem B2068071 : Blo 2067435 2068071 := bstep (se 1 (by rfl) ⟨1551053, by rfl⟩ : syracuseStep 2068071 = 3102107) B3102107
theorem B2326585 : Blo 2067435 2326585 := bbase (se 2 (by rfl) ⟨872469, by rfl⟩ : syracuseStep 2326585 = 1744939) (by norm_num)
theorem B3102113 : Blo 2067435 3102113 := bstep (se 2 (by rfl) ⟨1163292, by rfl⟩ : syracuseStep 3102113 = 2326585) B2326585
theorem B2068075 : Blo 2067435 2068075 := bstep (se 1 (by rfl) ⟨1551056, by rfl⟩ : syracuseStep 2068075 = 3102113) B3102113
theorem B3726749 : Blo 2067435 3726749 := bbase (se 3 (by rfl) ⟨698765, by rfl⟩ : syracuseStep 3726749 = 1397531) (by norm_num)
theorem B2484499 : Blo 2067435 2484499 := bstep (se 1 (by rfl) ⟨1863374, by rfl⟩ : syracuseStep 2484499 = 3726749) B3726749
theorem B3312665 : Blo 2067435 3312665 := bstep (se 2 (by rfl) ⟨1242249, by rfl⟩ : syracuseStep 3312665 = 2484499) B2484499
theorem B2208443 : Blo 2067435 2208443 := bstep (se 1 (by rfl) ⟨1656332, by rfl⟩ : syracuseStep 2208443 = 3312665) B3312665
theorem B5889181 : Blo 2067435 5889181 := bstep (se 3 (by rfl) ⟨1104221, by rfl⟩ : syracuseStep 5889181 = 2208443) B2208443
theorem B7852241 : Blo 2067435 7852241 := bstep (se 2 (by rfl) ⟨2944590, by rfl⟩ : syracuseStep 7852241 = 5889181) B5889181
theorem B5234827 : Blo 2067435 5234827 := bstep (se 1 (by rfl) ⟨3926120, by rfl⟩ : syracuseStep 5234827 = 7852241) B7852241
theorem B6979769 : Blo 2067435 6979769 := bstep (se 2 (by rfl) ⟨2617413, by rfl⟩ : syracuseStep 6979769 = 5234827) B5234827
theorem B4653179 : Blo 2067435 4653179 := bstep (se 1 (by rfl) ⟨3489884, by rfl⟩ : syracuseStep 4653179 = 6979769) B6979769
theorem B3102119 : Blo 2067435 3102119 := bstep (se 1 (by rfl) ⟨2326589, by rfl⟩ : syracuseStep 3102119 = 4653179) B4653179
theorem B2068079 : Blo 2067435 2068079 := bstep (se 1 (by rfl) ⟨1551059, by rfl⟩ : syracuseStep 2068079 = 3102119) B3102119
theorem B3102125 : Blo 2067435 3102125 := bbase (se 3 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 3102125 = 1163297) (by norm_num)
theorem B2068083 : Blo 2067435 2068083 := bstep (se 1 (by rfl) ⟨1551062, by rfl⟩ : syracuseStep 2068083 = 3102125) B3102125
theorem B4653197 : Blo 2067435 4653197 := bbase (se 3 (by rfl) ⟨872474, by rfl⟩ : syracuseStep 4653197 = 1744949) (by norm_num)
theorem B3102131 : Blo 2067435 3102131 := bstep (se 1 (by rfl) ⟨2326598, by rfl⟩ : syracuseStep 3102131 = 4653197) B4653197
theorem B2068087 : Blo 2067435 2068087 := bstep (se 1 (by rfl) ⟨1551065, by rfl⟩ : syracuseStep 2068087 = 3102131) B3102131
theorem B2617429 : Blo 2067435 2617429 := bbase (se 8 (by rfl) ⟨15336, by rfl⟩ : syracuseStep 2617429 = 30673) (by norm_num)
theorem B3489905 : Blo 2067435 3489905 := bstep (se 2 (by rfl) ⟨1308714, by rfl⟩ : syracuseStep 3489905 = 2617429) B2617429
theorem B2326603 : Blo 2067435 2326603 := bstep (se 1 (by rfl) ⟨1744952, by rfl⟩ : syracuseStep 2326603 = 3489905) B3489905
theorem B3102137 : Blo 2067435 3102137 := bstep (se 2 (by rfl) ⟨1163301, by rfl⟩ : syracuseStep 3102137 = 2326603) B2326603
theorem B2068091 : Blo 2067435 2068091 := bstep (se 1 (by rfl) ⟨1551068, by rfl⟩ : syracuseStep 2068091 = 3102137) B3102137
theorem B15918869 : Blo 2067435 15918869 := bbase (se 6 (by rfl) ⟨373098, by rfl⟩ : syracuseStep 15918869 = 746197) (by norm_num)
theorem B10612579 : Blo 2067435 10612579 := bstep (se 1 (by rfl) ⟨7959434, by rfl⟩ : syracuseStep 10612579 = 15918869) B15918869
theorem B14150105 : Blo 2067435 14150105 := bstep (se 2 (by rfl) ⟨5306289, by rfl⟩ : syracuseStep 14150105 = 10612579) B10612579
theorem B9433403 : Blo 2067435 9433403 := bstep (se 1 (by rfl) ⟨7075052, by rfl⟩ : syracuseStep 9433403 = 14150105) B14150105
theorem B6288935 : Blo 2067435 6288935 := bstep (se 1 (by rfl) ⟨4716701, by rfl⟩ : syracuseStep 6288935 = 9433403) B9433403
theorem B16770493 : Blo 2067435 16770493 := bstep (se 3 (by rfl) ⟨3144467, by rfl⟩ : syracuseStep 16770493 = 6288935) B6288935
theorem B89442629 : Blo 2067435 89442629 := bstep (se 4 (by rfl) ⟨8385246, by rfl⟩ : syracuseStep 89442629 = 16770493) B16770493
theorem B59628419 : Blo 2067435 59628419 := bstep (se 1 (by rfl) ⟨44721314, by rfl⟩ : syracuseStep 59628419 = 89442629) B89442629
theorem B39752279 : Blo 2067435 39752279 := bstep (se 1 (by rfl) ⟨29814209, by rfl⟩ : syracuseStep 39752279 = 59628419) B59628419
theorem B26501519 : Blo 2067435 26501519 := bstep (se 1 (by rfl) ⟨19876139, by rfl⟩ : syracuseStep 26501519 = 39752279) B39752279
theorem B17667679 : Blo 2067435 17667679 := bstep (se 1 (by rfl) ⟨13250759, by rfl⟩ : syracuseStep 17667679 = 26501519) B26501519
theorem B23556905 : Blo 2067435 23556905 := bstep (se 2 (by rfl) ⟨8833839, by rfl⟩ : syracuseStep 23556905 = 17667679) B17667679
theorem B15704603 : Blo 2067435 15704603 := bstep (se 1 (by rfl) ⟨11778452, by rfl⟩ : syracuseStep 15704603 = 23556905) B23556905
theorem B10469735 : Blo 2067435 10469735 := bstep (se 1 (by rfl) ⟨7852301, by rfl⟩ : syracuseStep 10469735 = 15704603) B15704603
theorem B6979823 : Blo 2067435 6979823 := bstep (se 1 (by rfl) ⟨5234867, by rfl⟩ : syracuseStep 6979823 = 10469735) B10469735
theorem B4653215 : Blo 2067435 4653215 := bstep (se 1 (by rfl) ⟨3489911, by rfl⟩ : syracuseStep 4653215 = 6979823) B6979823
theorem B3102143 : Blo 2067435 3102143 := bstep (se 1 (by rfl) ⟨2326607, by rfl⟩ : syracuseStep 3102143 = 4653215) B4653215
theorem B2068095 : Blo 2067435 2068095 := bstep (se 1 (by rfl) ⟨1551071, by rfl⟩ : syracuseStep 2068095 = 3102143) B3102143
theorem B3102149 : Blo 2067435 3102149 := bbase (se 4 (by rfl) ⟨290826, by rfl⟩ : syracuseStep 3102149 = 581653) (by norm_num)
theorem B2068099 : Blo 2067435 2068099 := bstep (se 1 (by rfl) ⟨1551074, by rfl⟩ : syracuseStep 2068099 = 3102149) B3102149
theorem B3489925 : Blo 2067435 3489925 := bbase (se 4 (by rfl) ⟨327180, by rfl⟩ : syracuseStep 3489925 = 654361) (by norm_num)
theorem B4653233 : Blo 2067435 4653233 := bstep (se 2 (by rfl) ⟨1744962, by rfl⟩ : syracuseStep 4653233 = 3489925) B3489925
theorem B3102155 : Blo 2067435 3102155 := bstep (se 1 (by rfl) ⟨2326616, by rfl⟩ : syracuseStep 3102155 = 4653233) B4653233
theorem B2068103 : Blo 2067435 2068103 := bstep (se 1 (by rfl) ⟨1551077, by rfl⟩ : syracuseStep 2068103 = 3102155) B3102155
theorem B2326621 : Blo 2067435 2326621 := bbase (se 3 (by rfl) ⟨436241, by rfl⟩ : syracuseStep 2326621 = 872483) (by norm_num)
theorem B3102161 : Blo 2067435 3102161 := bstep (se 2 (by rfl) ⟨1163310, by rfl⟩ : syracuseStep 3102161 = 2326621) B2326621
theorem B2068107 : Blo 2067435 2068107 := bstep (se 1 (by rfl) ⟨1551080, by rfl⟩ : syracuseStep 2068107 = 3102161) B3102161
theorem B6979877 : Blo 2067435 6979877 := bbase (se 4 (by rfl) ⟨654363, by rfl⟩ : syracuseStep 6979877 = 1308727) (by norm_num)
theorem B4653251 : Blo 2067435 4653251 := bstep (se 1 (by rfl) ⟨3489938, by rfl⟩ : syracuseStep 4653251 = 6979877) B6979877
theorem B3102167 : Blo 2067435 3102167 := bstep (se 1 (by rfl) ⟨2326625, by rfl⟩ : syracuseStep 3102167 = 4653251) B4653251
theorem B2068111 : Blo 2067435 2068111 := bstep (se 1 (by rfl) ⟨1551083, by rfl⟩ : syracuseStep 2068111 = 3102167) B3102167
theorem B3102173 : Blo 2067435 3102173 := bbase (se 3 (by rfl) ⟨581657, by rfl⟩ : syracuseStep 3102173 = 1163315) (by norm_num)
theorem B2068115 : Blo 2067435 2068115 := bstep (se 1 (by rfl) ⟨1551086, by rfl⟩ : syracuseStep 2068115 = 3102173) B3102173
theorem B4653269 : Blo 2067435 4653269 := bbase (se 7 (by rfl) ⟨54530, by rfl⟩ : syracuseStep 4653269 = 109061) (by norm_num)
theorem B3102179 : Blo 2067435 3102179 := bstep (se 1 (by rfl) ⟨2326634, by rfl⟩ : syracuseStep 3102179 = 4653269) B4653269
theorem B2068119 : Blo 2067435 2068119 := bstep (se 1 (by rfl) ⟨1551089, by rfl⟩ : syracuseStep 2068119 = 3102179) B3102179
theorem B16999541 : Blo 2067435 16999541 := bbase (se 5 (by rfl) ⟨796853, by rfl⟩ : syracuseStep 16999541 = 1593707) (by norm_num)
theorem B11333027 : Blo 2067435 11333027 := bstep (se 1 (by rfl) ⟨8499770, by rfl⟩ : syracuseStep 11333027 = 16999541) B16999541
theorem B7555351 : Blo 2067435 7555351 := bstep (se 1 (by rfl) ⟨5666513, by rfl⟩ : syracuseStep 7555351 = 11333027) B11333027
theorem B10073801 : Blo 2067435 10073801 := bstep (se 2 (by rfl) ⟨3777675, by rfl⟩ : syracuseStep 10073801 = 7555351) B7555351
theorem B6715867 : Blo 2067435 6715867 := bstep (se 1 (by rfl) ⟨5036900, by rfl⟩ : syracuseStep 6715867 = 10073801) B10073801
theorem B8954489 : Blo 2067435 8954489 := bstep (se 2 (by rfl) ⟨3357933, by rfl⟩ : syracuseStep 8954489 = 6715867) B6715867
theorem B5969659 : Blo 2067435 5969659 := bstep (se 1 (by rfl) ⟨4477244, by rfl⟩ : syracuseStep 5969659 = 8954489) B8954489
theorem B7959545 : Blo 2067435 7959545 := bstep (se 2 (by rfl) ⟨2984829, by rfl⟩ : syracuseStep 7959545 = 5969659) B5969659
theorem B5306363 : Blo 2067435 5306363 := bstep (se 1 (by rfl) ⟨3979772, by rfl⟩ : syracuseStep 5306363 = 7959545) B7959545
theorem B3537575 : Blo 2067435 3537575 := bstep (se 1 (by rfl) ⟨2653181, by rfl⟩ : syracuseStep 3537575 = 5306363) B5306363
theorem B37734133 : Blo 2067435 37734133 := bstep (se 5 (by rfl) ⟨1768787, by rfl⟩ : syracuseStep 37734133 = 3537575) B3537575
theorem B50312177 : Blo 2067435 50312177 := bstep (se 2 (by rfl) ⟨18867066, by rfl⟩ : syracuseStep 50312177 = 37734133) B37734133
theorem B33541451 : Blo 2067435 33541451 := bstep (se 1 (by rfl) ⟨25156088, by rfl⟩ : syracuseStep 33541451 = 50312177) B50312177
theorem B22360967 : Blo 2067435 22360967 := bstep (se 1 (by rfl) ⟨16770725, by rfl⟩ : syracuseStep 22360967 = 33541451) B33541451
theorem B14907311 : Blo 2067435 14907311 := bstep (se 1 (by rfl) ⟨11180483, by rfl⟩ : syracuseStep 14907311 = 22360967) B22360967
theorem B9938207 : Blo 2067435 9938207 := bstep (se 1 (by rfl) ⟨7453655, by rfl⟩ : syracuseStep 9938207 = 14907311) B14907311
theorem B6625471 : Blo 2067435 6625471 := bstep (se 1 (by rfl) ⟨4969103, by rfl⟩ : syracuseStep 6625471 = 9938207) B9938207
theorem B8833961 : Blo 2067435 8833961 := bstep (se 2 (by rfl) ⟨3312735, by rfl⟩ : syracuseStep 8833961 = 6625471) B6625471
theorem B5889307 : Blo 2067435 5889307 := bstep (se 1 (by rfl) ⟨4416980, by rfl⟩ : syracuseStep 5889307 = 8833961) B8833961
theorem B7852409 : Blo 2067435 7852409 := bstep (se 2 (by rfl) ⟨2944653, by rfl⟩ : syracuseStep 7852409 = 5889307) B5889307
theorem B5234939 : Blo 2067435 5234939 := bstep (se 1 (by rfl) ⟨3926204, by rfl⟩ : syracuseStep 5234939 = 7852409) B7852409
theorem B3489959 : Blo 2067435 3489959 := bstep (se 1 (by rfl) ⟨2617469, by rfl⟩ : syracuseStep 3489959 = 5234939) B5234939
theorem B2326639 : Blo 2067435 2326639 := bstep (se 1 (by rfl) ⟨1744979, by rfl⟩ : syracuseStep 2326639 = 3489959) B3489959
theorem B3102185 : Blo 2067435 3102185 := bstep (se 2 (by rfl) ⟨1163319, by rfl⟩ : syracuseStep 3102185 = 2326639) B2326639
theorem B2068123 : Blo 2067435 2068123 := bstep (se 1 (by rfl) ⟨1551092, by rfl⟩ : syracuseStep 2068123 = 3102185) B3102185
theorem B13250965 : Blo 2067435 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B17667953 : Blo 2067435 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B11778635 : Blo 2067435 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B7852423 : Blo 2067435 7852423 := bstep (se 1 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 7852423 = 11778635) B11778635
theorem B10469897 : Blo 2067435 10469897 := bstep (se 2 (by rfl) ⟨3926211, by rfl⟩ : syracuseStep 10469897 = 7852423) B7852423
theorem B6979931 : Blo 2067435 6979931 := bstep (se 1 (by rfl) ⟨5234948, by rfl⟩ : syracuseStep 6979931 = 10469897) B10469897
theorem B4653287 : Blo 2067435 4653287 := bstep (se 1 (by rfl) ⟨3489965, by rfl⟩ : syracuseStep 4653287 = 6979931) B6979931
theorem B3102191 : Blo 2067435 3102191 := bstep (se 1 (by rfl) ⟨2326643, by rfl⟩ : syracuseStep 3102191 = 4653287) B4653287
theorem B2068127 : Blo 2067435 2068127 := bstep (se 1 (by rfl) ⟨1551095, by rfl⟩ : syracuseStep 2068127 = 3102191) B3102191
theorem B3102197 : Blo 2067435 3102197 := bbase (se 5 (by rfl) ⟨145415, by rfl⟩ : syracuseStep 3102197 = 290831) (by norm_num)
theorem B2068131 : Blo 2067435 2068131 := bstep (se 1 (by rfl) ⟨1551098, by rfl⟩ : syracuseStep 2068131 = 3102197) B3102197
theorem B4969133 : Blo 2067435 4969133 := bbase (se 3 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 4969133 = 1863425) (by norm_num)
theorem B3312755 : Blo 2067435 3312755 := bstep (se 1 (by rfl) ⟨2484566, by rfl⟩ : syracuseStep 3312755 = 4969133) B4969133
theorem B2208503 : Blo 2067435 2208503 := bstep (se 1 (by rfl) ⟨1656377, by rfl⟩ : syracuseStep 2208503 = 3312755) B3312755
theorem B5889341 : Blo 2067435 5889341 := bstep (se 3 (by rfl) ⟨1104251, by rfl⟩ : syracuseStep 5889341 = 2208503) B2208503
theorem B3926227 : Blo 2067435 3926227 := bstep (se 1 (by rfl) ⟨2944670, by rfl⟩ : syracuseStep 3926227 = 5889341) B5889341
theorem B5234969 : Blo 2067435 5234969 := bstep (se 2 (by rfl) ⟨1963113, by rfl⟩ : syracuseStep 5234969 = 3926227) B3926227
theorem B3489979 : Blo 2067435 3489979 := bstep (se 1 (by rfl) ⟨2617484, by rfl⟩ : syracuseStep 3489979 = 5234969) B5234969
theorem B4653305 : Blo 2067435 4653305 := bstep (se 2 (by rfl) ⟨1744989, by rfl⟩ : syracuseStep 4653305 = 3489979) B3489979
theorem B3102203 : Blo 2067435 3102203 := bstep (se 1 (by rfl) ⟨2326652, by rfl⟩ : syracuseStep 3102203 = 4653305) B4653305
theorem B2068135 : Blo 2067435 2068135 := bstep (se 1 (by rfl) ⟨1551101, by rfl⟩ : syracuseStep 2068135 = 3102203) B3102203
theorem B2326657 : Blo 2067435 2326657 := bbase (se 2 (by rfl) ⟨872496, by rfl⟩ : syracuseStep 2326657 = 1744993) (by norm_num)
theorem B3102209 : Blo 2067435 3102209 := bstep (se 2 (by rfl) ⟨1163328, by rfl⟩ : syracuseStep 3102209 = 2326657) B2326657
theorem B2068139 : Blo 2067435 2068139 := bstep (se 1 (by rfl) ⟨1551104, by rfl⟩ : syracuseStep 2068139 = 3102209) B3102209
theorem B5234989 : Blo 2067435 5234989 := bbase (se 3 (by rfl) ⟨981560, by rfl⟩ : syracuseStep 5234989 = 1963121) (by norm_num)
theorem B6979985 : Blo 2067435 6979985 := bstep (se 2 (by rfl) ⟨2617494, by rfl⟩ : syracuseStep 6979985 = 5234989) B5234989
theorem B4653323 : Blo 2067435 4653323 := bstep (se 1 (by rfl) ⟨3489992, by rfl⟩ : syracuseStep 4653323 = 6979985) B6979985
theorem B3102215 : Blo 2067435 3102215 := bstep (se 1 (by rfl) ⟨2326661, by rfl⟩ : syracuseStep 3102215 = 4653323) B4653323
theorem B2068143 : Blo 2067435 2068143 := bstep (se 1 (by rfl) ⟨1551107, by rfl⟩ : syracuseStep 2068143 = 3102215) B3102215
theorem B3102221 : Blo 2067435 3102221 := bbase (se 3 (by rfl) ⟨581666, by rfl⟩ : syracuseStep 3102221 = 1163333) (by norm_num)
theorem B2068147 : Blo 2067435 2068147 := bstep (se 1 (by rfl) ⟨1551110, by rfl⟩ : syracuseStep 2068147 = 3102221) B3102221
theorem B4653341 : Blo 2067435 4653341 := bbase (se 3 (by rfl) ⟨872501, by rfl⟩ : syracuseStep 4653341 = 1745003) (by norm_num)
theorem B3102227 : Blo 2067435 3102227 := bstep (se 1 (by rfl) ⟨2326670, by rfl⟩ : syracuseStep 3102227 = 4653341) B4653341
theorem B2068151 : Blo 2067435 2068151 := bstep (se 1 (by rfl) ⟨1551113, by rfl⟩ : syracuseStep 2068151 = 3102227) B3102227
theorem B3490013 : Blo 2067435 3490013 := bbase (se 3 (by rfl) ⟨654377, by rfl⟩ : syracuseStep 3490013 = 1308755) (by norm_num)
theorem B2326675 : Blo 2067435 2326675 := bstep (se 1 (by rfl) ⟨1745006, by rfl⟩ : syracuseStep 2326675 = 3490013) B3490013
theorem B3102233 : Blo 2067435 3102233 := bstep (se 2 (by rfl) ⟨1163337, by rfl⟩ : syracuseStep 3102233 = 2326675) B2326675
theorem B2068155 : Blo 2067435 2068155 := bstep (se 1 (by rfl) ⟨1551116, by rfl⟩ : syracuseStep 2068155 = 3102233) B3102233
theorem B4969189 : Blo 2067435 4969189 := bbase (se 4 (by rfl) ⟨465861, by rfl⟩ : syracuseStep 4969189 = 931723) (by norm_num)
theorem B6625585 : Blo 2067435 6625585 := bstep (se 2 (by rfl) ⟨2484594, by rfl⟩ : syracuseStep 6625585 = 4969189) B4969189
theorem B8834113 : Blo 2067435 8834113 := bstep (se 2 (by rfl) ⟨3312792, by rfl⟩ : syracuseStep 8834113 = 6625585) B6625585
theorem B11778817 : Blo 2067435 11778817 := bstep (se 2 (by rfl) ⟨4417056, by rfl⟩ : syracuseStep 11778817 = 8834113) B8834113
theorem B15705089 : Blo 2067435 15705089 := bstep (se 2 (by rfl) ⟨5889408, by rfl⟩ : syracuseStep 15705089 = 11778817) B11778817
theorem B10470059 : Blo 2067435 10470059 := bstep (se 1 (by rfl) ⟨7852544, by rfl⟩ : syracuseStep 10470059 = 15705089) B15705089
theorem B6980039 : Blo 2067435 6980039 := bstep (se 1 (by rfl) ⟨5235029, by rfl⟩ : syracuseStep 6980039 = 10470059) B10470059
theorem B4653359 : Blo 2067435 4653359 := bstep (se 1 (by rfl) ⟨3490019, by rfl⟩ : syracuseStep 4653359 = 6980039) B6980039
theorem B3102239 : Blo 2067435 3102239 := bstep (se 1 (by rfl) ⟨2326679, by rfl⟩ : syracuseStep 3102239 = 4653359) B4653359
theorem B2068159 : Blo 2067435 2068159 := bstep (se 1 (by rfl) ⟨1551119, by rfl⟩ : syracuseStep 2068159 = 3102239) B3102239
theorem B3102245 : Blo 2067435 3102245 := bbase (se 4 (by rfl) ⟨290835, by rfl⟩ : syracuseStep 3102245 = 581671) (by norm_num)
theorem B2068163 : Blo 2067435 2068163 := bstep (se 1 (by rfl) ⟨1551122, by rfl⟩ : syracuseStep 2068163 = 3102245) B3102245
theorem B2617525 : Blo 2067435 2617525 := bbase (se 5 (by rfl) ⟨122696, by rfl⟩ : syracuseStep 2617525 = 245393) (by norm_num)
theorem B3490033 : Blo 2067435 3490033 := bstep (se 2 (by rfl) ⟨1308762, by rfl⟩ : syracuseStep 3490033 = 2617525) B2617525
theorem B4653377 : Blo 2067435 4653377 := bstep (se 2 (by rfl) ⟨1745016, by rfl⟩ : syracuseStep 4653377 = 3490033) B3490033
theorem B3102251 : Blo 2067435 3102251 := bstep (se 1 (by rfl) ⟨2326688, by rfl⟩ : syracuseStep 3102251 = 4653377) B4653377
theorem B2068167 : Blo 2067435 2068167 := bstep (se 1 (by rfl) ⟨1551125, by rfl⟩ : syracuseStep 2068167 = 3102251) B3102251
theorem B2326693 : Blo 2067435 2326693 := bbase (se 4 (by rfl) ⟨218127, by rfl⟩ : syracuseStep 2326693 = 436255) (by norm_num)
theorem B3102257 : Blo 2067435 3102257 := bstep (se 2 (by rfl) ⟨1163346, by rfl⟩ : syracuseStep 3102257 = 2326693) B2326693
theorem B2068171 : Blo 2067435 2068171 := bstep (se 1 (by rfl) ⟨1551128, by rfl⟩ : syracuseStep 2068171 = 3102257) B3102257
theorem B2653249 : Blo 2067435 2653249 := bbase (se 2 (by rfl) ⟨994968, by rfl⟩ : syracuseStep 2653249 = 1989937) (by norm_num)
theorem B3537665 : Blo 2067435 3537665 := bstep (se 2 (by rfl) ⟨1326624, by rfl⟩ : syracuseStep 3537665 = 2653249) B2653249
theorem B2358443 : Blo 2067435 2358443 := bstep (se 1 (by rfl) ⟨1768832, by rfl⟩ : syracuseStep 2358443 = 3537665) B3537665
theorem B6289181 : Blo 2067435 6289181 := bstep (se 3 (by rfl) ⟨1179221, by rfl⟩ : syracuseStep 6289181 = 2358443) B2358443
theorem B4192787 : Blo 2067435 4192787 := bstep (se 1 (by rfl) ⟨3144590, by rfl⟩ : syracuseStep 4192787 = 6289181) B6289181
theorem B2795191 : Blo 2067435 2795191 := bstep (se 1 (by rfl) ⟨2096393, by rfl⟩ : syracuseStep 2795191 = 4192787) B4192787
theorem B14907685 : Blo 2067435 14907685 := bstep (se 4 (by rfl) ⟨1397595, by rfl⟩ : syracuseStep 14907685 = 2795191) B2795191
theorem B19876913 : Blo 2067435 19876913 := bstep (se 2 (by rfl) ⟨7453842, by rfl⟩ : syracuseStep 19876913 = 14907685) B14907685
theorem B13251275 : Blo 2067435 13251275 := bstep (se 1 (by rfl) ⟨9938456, by rfl⟩ : syracuseStep 13251275 = 19876913) B19876913
theorem B8834183 : Blo 2067435 8834183 := bstep (se 1 (by rfl) ⟨6625637, by rfl⟩ : syracuseStep 8834183 = 13251275) B13251275
theorem B5889455 : Blo 2067435 5889455 := bstep (se 1 (by rfl) ⟨4417091, by rfl⟩ : syracuseStep 5889455 = 8834183) B8834183
theorem B3926303 : Blo 2067435 3926303 := bstep (se 1 (by rfl) ⟨2944727, by rfl⟩ : syracuseStep 3926303 = 5889455) B5889455
theorem B2617535 : Blo 2067435 2617535 := bstep (se 1 (by rfl) ⟨1963151, by rfl⟩ : syracuseStep 2617535 = 3926303) B3926303
theorem B6980093 : Blo 2067435 6980093 := bstep (se 3 (by rfl) ⟨1308767, by rfl⟩ : syracuseStep 6980093 = 2617535) B2617535
theorem B4653395 : Blo 2067435 4653395 := bstep (se 1 (by rfl) ⟨3490046, by rfl⟩ : syracuseStep 4653395 = 6980093) B6980093
theorem B3102263 : Blo 2067435 3102263 := bstep (se 1 (by rfl) ⟨2326697, by rfl⟩ : syracuseStep 3102263 = 4653395) B4653395
theorem B2068175 : Blo 2067435 2068175 := bstep (se 1 (by rfl) ⟨1551131, by rfl⟩ : syracuseStep 2068175 = 3102263) B3102263
theorem B3102269 : Blo 2067435 3102269 := bbase (se 3 (by rfl) ⟨581675, by rfl⟩ : syracuseStep 3102269 = 1163351) (by norm_num)
theorem B2068179 : Blo 2067435 2068179 := bstep (se 1 (by rfl) ⟨1551134, by rfl⟩ : syracuseStep 2068179 = 3102269) B3102269
theorem B4653413 : Blo 2067435 4653413 := bbase (se 4 (by rfl) ⟨436257, by rfl⟩ : syracuseStep 4653413 = 872515) (by norm_num)
theorem B3102275 : Blo 2067435 3102275 := bstep (se 1 (by rfl) ⟨2326706, by rfl⟩ : syracuseStep 3102275 = 4653413) B4653413
theorem B2068183 : Blo 2067435 2068183 := bstep (se 1 (by rfl) ⟨1551137, by rfl⟩ : syracuseStep 2068183 = 3102275) B3102275
theorem B5235101 : Blo 2067435 5235101 := bbase (se 3 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 5235101 = 1963163) (by norm_num)
theorem B3490067 : Blo 2067435 3490067 := bstep (se 1 (by rfl) ⟨2617550, by rfl⟩ : syracuseStep 3490067 = 5235101) B5235101
theorem B2326711 : Blo 2067435 2326711 := bstep (se 1 (by rfl) ⟨1745033, by rfl⟩ : syracuseStep 2326711 = 3490067) B3490067
theorem B3102281 : Blo 2067435 3102281 := bstep (se 2 (by rfl) ⟨1163355, by rfl⟩ : syracuseStep 3102281 = 2326711) B2326711
theorem B2068187 : Blo 2067435 2068187 := bstep (se 1 (by rfl) ⟨1551140, by rfl⟩ : syracuseStep 2068187 = 3102281) B3102281
theorem B3926333 : Blo 2067435 3926333 := bbase (se 3 (by rfl) ⟨736187, by rfl⟩ : syracuseStep 3926333 = 1472375) (by norm_num)
theorem B10470221 : Blo 2067435 10470221 := bstep (se 3 (by rfl) ⟨1963166, by rfl⟩ : syracuseStep 10470221 = 3926333) B3926333
theorem B6980147 : Blo 2067435 6980147 := bstep (se 1 (by rfl) ⟨5235110, by rfl⟩ : syracuseStep 6980147 = 10470221) B10470221
theorem B4653431 : Blo 2067435 4653431 := bstep (se 1 (by rfl) ⟨3490073, by rfl⟩ : syracuseStep 4653431 = 6980147) B6980147
theorem B3102287 : Blo 2067435 3102287 := bstep (se 1 (by rfl) ⟨2326715, by rfl⟩ : syracuseStep 3102287 = 4653431) B4653431
theorem B2068191 : Blo 2067435 2068191 := bstep (se 1 (by rfl) ⟨1551143, by rfl⟩ : syracuseStep 2068191 = 3102287) B3102287
theorem B3102293 : Blo 2067435 3102293 := bbase (se 8 (by rfl) ⟨18177, by rfl⟩ : syracuseStep 3102293 = 36355) (by norm_num)
theorem B2068195 : Blo 2067435 2068195 := bstep (se 1 (by rfl) ⟨1551146, by rfl⟩ : syracuseStep 2068195 = 3102293) B3102293
theorem B3726965 : Blo 2067435 3726965 := bbase (se 5 (by rfl) ⟨174701, by rfl⟩ : syracuseStep 3726965 = 349403) (by norm_num)
theorem B2484643 : Blo 2067435 2484643 := bstep (se 1 (by rfl) ⟨1863482, by rfl⟩ : syracuseStep 2484643 = 3726965) B3726965
theorem B3312857 : Blo 2067435 3312857 := bstep (se 2 (by rfl) ⟨1242321, by rfl⟩ : syracuseStep 3312857 = 2484643) B2484643
theorem B8834285 : Blo 2067435 8834285 := bstep (se 3 (by rfl) ⟨1656428, by rfl⟩ : syracuseStep 8834285 = 3312857) B3312857
theorem B5889523 : Blo 2067435 5889523 := bstep (se 1 (by rfl) ⟨4417142, by rfl⟩ : syracuseStep 5889523 = 8834285) B8834285
theorem B7852697 : Blo 2067435 7852697 := bstep (se 2 (by rfl) ⟨2944761, by rfl⟩ : syracuseStep 7852697 = 5889523) B5889523
theorem B5235131 : Blo 2067435 5235131 := bstep (se 1 (by rfl) ⟨3926348, by rfl⟩ : syracuseStep 5235131 = 7852697) B7852697
theorem B3490087 : Blo 2067435 3490087 := bstep (se 1 (by rfl) ⟨2617565, by rfl⟩ : syracuseStep 3490087 = 5235131) B5235131
theorem B4653449 : Blo 2067435 4653449 := bstep (se 2 (by rfl) ⟨1745043, by rfl⟩ : syracuseStep 4653449 = 3490087) B3490087
theorem B3102299 : Blo 2067435 3102299 := bstep (se 1 (by rfl) ⟨2326724, by rfl⟩ : syracuseStep 3102299 = 4653449) B4653449
theorem B2068199 : Blo 2067435 2068199 := bstep (se 1 (by rfl) ⟨1551149, by rfl⟩ : syracuseStep 2068199 = 3102299) B3102299
theorem B2326729 : Blo 2067435 2326729 := bbase (se 2 (by rfl) ⟨872523, by rfl⟩ : syracuseStep 2326729 = 1745047) (by norm_num)
theorem B3102305 : Blo 2067435 3102305 := bstep (se 2 (by rfl) ⟨1163364, by rfl⟩ : syracuseStep 3102305 = 2326729) B2326729
theorem B2068203 : Blo 2067435 2068203 := bstep (se 1 (by rfl) ⟨1551152, by rfl⟩ : syracuseStep 2068203 = 3102305) B3102305
theorem B7453957 : Blo 2067435 7453957 := bbase (se 4 (by rfl) ⟨698808, by rfl⟩ : syracuseStep 7453957 = 1397617) (by norm_num)
theorem B9938609 : Blo 2067435 9938609 := bstep (se 2 (by rfl) ⟨3726978, by rfl⟩ : syracuseStep 9938609 = 7453957) B7453957
theorem B6625739 : Blo 2067435 6625739 := bstep (se 1 (by rfl) ⟨4969304, by rfl⟩ : syracuseStep 6625739 = 9938609) B9938609
theorem B17668637 : Blo 2067435 17668637 := bstep (se 3 (by rfl) ⟨3312869, by rfl⟩ : syracuseStep 17668637 = 6625739) B6625739
theorem B11779091 : Blo 2067435 11779091 := bstep (se 1 (by rfl) ⟨8834318, by rfl⟩ : syracuseStep 11779091 = 17668637) B17668637
theorem B7852727 : Blo 2067435 7852727 := bstep (se 1 (by rfl) ⟨5889545, by rfl⟩ : syracuseStep 7852727 = 11779091) B11779091
theorem B5235151 : Blo 2067435 5235151 := bstep (se 1 (by rfl) ⟨3926363, by rfl⟩ : syracuseStep 5235151 = 7852727) B7852727
theorem B6980201 : Blo 2067435 6980201 := bstep (se 2 (by rfl) ⟨2617575, by rfl⟩ : syracuseStep 6980201 = 5235151) B5235151
theorem B4653467 : Blo 2067435 4653467 := bstep (se 1 (by rfl) ⟨3490100, by rfl⟩ : syracuseStep 4653467 = 6980201) B6980201
theorem B3102311 : Blo 2067435 3102311 := bstep (se 1 (by rfl) ⟨2326733, by rfl⟩ : syracuseStep 3102311 = 4653467) B4653467
theorem B2068207 : Blo 2067435 2068207 := bstep (se 1 (by rfl) ⟨1551155, by rfl⟩ : syracuseStep 2068207 = 3102311) B3102311
theorem B3102317 : Blo 2067435 3102317 := bbase (se 3 (by rfl) ⟨581684, by rfl⟩ : syracuseStep 3102317 = 1163369) (by norm_num)
theorem B2068211 : Blo 2067435 2068211 := bstep (se 1 (by rfl) ⟨1551158, by rfl⟩ : syracuseStep 2068211 = 3102317) B3102317
theorem B4653485 : Blo 2067435 4653485 := bbase (se 3 (by rfl) ⟨872528, by rfl⟩ : syracuseStep 4653485 = 1745057) (by norm_num)
theorem B3102323 : Blo 2067435 3102323 := bstep (se 1 (by rfl) ⟨2326742, by rfl⟩ : syracuseStep 3102323 = 4653485) B4653485
theorem B2068215 : Blo 2067435 2068215 := bstep (se 1 (by rfl) ⟨1551161, by rfl⟩ : syracuseStep 2068215 = 3102323) B3102323
theorem B2208593 : Blo 2067435 2208593 := bbase (se 2 (by rfl) ⟨828222, by rfl⟩ : syracuseStep 2208593 = 1656445) (by norm_num)
theorem B5889581 : Blo 2067435 5889581 := bstep (se 3 (by rfl) ⟨1104296, by rfl⟩ : syracuseStep 5889581 = 2208593) B2208593
theorem B3926387 : Blo 2067435 3926387 := bstep (se 1 (by rfl) ⟨2944790, by rfl⟩ : syracuseStep 3926387 = 5889581) B5889581
theorem B2617591 : Blo 2067435 2617591 := bstep (se 1 (by rfl) ⟨1963193, by rfl⟩ : syracuseStep 2617591 = 3926387) B3926387
theorem B3490121 : Blo 2067435 3490121 := bstep (se 2 (by rfl) ⟨1308795, by rfl⟩ : syracuseStep 3490121 = 2617591) B2617591
theorem B2326747 : Blo 2067435 2326747 := bstep (se 1 (by rfl) ⟨1745060, by rfl⟩ : syracuseStep 2326747 = 3490121) B3490121
theorem B3102329 : Blo 2067435 3102329 := bstep (se 2 (by rfl) ⟨1163373, by rfl⟩ : syracuseStep 3102329 = 2326747) B2326747
theorem B2068219 : Blo 2067435 2068219 := bstep (se 1 (by rfl) ⟨1551164, by rfl⟩ : syracuseStep 2068219 = 3102329) B3102329
theorem B2653309 : Blo 2067435 2653309 := bbase (se 3 (by rfl) ⟨497495, by rfl⟩ : syracuseStep 2653309 = 994991) (by norm_num)
theorem B3537745 : Blo 2067435 3537745 := bstep (se 2 (by rfl) ⟨1326654, by rfl⟩ : syracuseStep 3537745 = 2653309) B2653309
theorem B18867973 : Blo 2067435 18867973 := bstep (se 4 (by rfl) ⟨1768872, by rfl⟩ : syracuseStep 18867973 = 3537745) B3537745
theorem B25157297 : Blo 2067435 25157297 := bstep (se 2 (by rfl) ⟨9433986, by rfl⟩ : syracuseStep 25157297 = 18867973) B18867973
theorem B16771531 : Blo 2067435 16771531 := bstep (se 1 (by rfl) ⟨12578648, by rfl⟩ : syracuseStep 16771531 = 25157297) B25157297
theorem B22362041 : Blo 2067435 22362041 := bstep (se 2 (by rfl) ⟨8385765, by rfl⟩ : syracuseStep 22362041 = 16771531) B16771531
theorem B59632109 : Blo 2067435 59632109 := bstep (se 3 (by rfl) ⟨11181020, by rfl⟩ : syracuseStep 59632109 = 22362041) B22362041
theorem B39754739 : Blo 2067435 39754739 := bstep (se 1 (by rfl) ⟨29816054, by rfl⟩ : syracuseStep 39754739 = 59632109) B59632109
theorem B26503159 : Blo 2067435 26503159 := bstep (se 1 (by rfl) ⟨19877369, by rfl⟩ : syracuseStep 26503159 = 39754739) B39754739
theorem B35337545 : Blo 2067435 35337545 := bstep (se 2 (by rfl) ⟨13251579, by rfl⟩ : syracuseStep 35337545 = 26503159) B26503159
theorem B23558363 : Blo 2067435 23558363 := bstep (se 1 (by rfl) ⟨17668772, by rfl⟩ : syracuseStep 23558363 = 35337545) B35337545
theorem B15705575 : Blo 2067435 15705575 := bstep (se 1 (by rfl) ⟨11779181, by rfl⟩ : syracuseStep 15705575 = 23558363) B23558363
theorem B10470383 : Blo 2067435 10470383 := bstep (se 1 (by rfl) ⟨7852787, by rfl⟩ : syracuseStep 10470383 = 15705575) B15705575
theorem B6980255 : Blo 2067435 6980255 := bstep (se 1 (by rfl) ⟨5235191, by rfl⟩ : syracuseStep 6980255 = 10470383) B10470383
theorem B4653503 : Blo 2067435 4653503 := bstep (se 1 (by rfl) ⟨3490127, by rfl⟩ : syracuseStep 4653503 = 6980255) B6980255
theorem B3102335 : Blo 2067435 3102335 := bstep (se 1 (by rfl) ⟨2326751, by rfl⟩ : syracuseStep 3102335 = 4653503) B4653503
theorem B2068223 : Blo 2067435 2068223 := bstep (se 1 (by rfl) ⟨1551167, by rfl⟩ : syracuseStep 2068223 = 3102335) B3102335
theorem B3102341 : Blo 2067435 3102341 := bbase (se 4 (by rfl) ⟨290844, by rfl⟩ : syracuseStep 3102341 = 581689) (by norm_num)
theorem B2068227 : Blo 2067435 2068227 := bstep (se 1 (by rfl) ⟨1551170, by rfl⟩ : syracuseStep 2068227 = 3102341) B3102341
theorem B3490141 : Blo 2067435 3490141 := bbase (se 3 (by rfl) ⟨654401, by rfl⟩ : syracuseStep 3490141 = 1308803) (by norm_num)
theorem B4653521 : Blo 2067435 4653521 := bstep (se 2 (by rfl) ⟨1745070, by rfl⟩ : syracuseStep 4653521 = 3490141) B3490141
theorem B3102347 : Blo 2067435 3102347 := bstep (se 1 (by rfl) ⟨2326760, by rfl⟩ : syracuseStep 3102347 = 4653521) B4653521
theorem B2068231 : Blo 2067435 2068231 := bstep (se 1 (by rfl) ⟨1551173, by rfl⟩ : syracuseStep 2068231 = 3102347) B3102347
theorem B2326765 : Blo 2067435 2326765 := bbase (se 3 (by rfl) ⟨436268, by rfl⟩ : syracuseStep 2326765 = 872537) (by norm_num)
theorem B3102353 : Blo 2067435 3102353 := bstep (se 2 (by rfl) ⟨1163382, by rfl⟩ : syracuseStep 3102353 = 2326765) B2326765
theorem B2068235 : Blo 2067435 2068235 := bstep (se 1 (by rfl) ⟨1551176, by rfl⟩ : syracuseStep 2068235 = 3102353) B3102353
theorem B6980309 : Blo 2067435 6980309 := bbase (se 7 (by rfl) ⟨81800, by rfl⟩ : syracuseStep 6980309 = 163601) (by norm_num)
theorem B4653539 : Blo 2067435 4653539 := bstep (se 1 (by rfl) ⟨3490154, by rfl⟩ : syracuseStep 4653539 = 6980309) B6980309
theorem B3102359 : Blo 2067435 3102359 := bstep (se 1 (by rfl) ⟨2326769, by rfl⟩ : syracuseStep 3102359 = 4653539) B4653539
theorem B2068239 : Blo 2067435 2068239 := bstep (se 1 (by rfl) ⟨1551179, by rfl⟩ : syracuseStep 2068239 = 3102359) B3102359
theorem B3102365 : Blo 2067435 3102365 := bbase (se 3 (by rfl) ⟨581693, by rfl⟩ : syracuseStep 3102365 = 1163387) (by norm_num)
theorem B2068243 : Blo 2067435 2068243 := bstep (se 1 (by rfl) ⟨1551182, by rfl⟩ : syracuseStep 2068243 = 3102365) B3102365
theorem B4653557 : Blo 2067435 4653557 := bbase (se 5 (by rfl) ⟨218135, by rfl⟩ : syracuseStep 4653557 = 436271) (by norm_num)
theorem B3102371 : Blo 2067435 3102371 := bstep (se 1 (by rfl) ⟨2326778, by rfl⟩ : syracuseStep 3102371 = 4653557) B4653557
theorem B2068247 : Blo 2067435 2068247 := bstep (se 1 (by rfl) ⟨1551185, by rfl⟩ : syracuseStep 2068247 = 3102371) B3102371
theorem B39755285 : Blo 2067435 39755285 := bbase (se 6 (by rfl) ⟨931764, by rfl⟩ : syracuseStep 39755285 = 1863529) (by norm_num)
theorem B26503523 : Blo 2067435 26503523 := bstep (se 1 (by rfl) ⟨19877642, by rfl⟩ : syracuseStep 26503523 = 39755285) B39755285
theorem B17669015 : Blo 2067435 17669015 := bstep (se 1 (by rfl) ⟨13251761, by rfl⟩ : syracuseStep 17669015 = 26503523) B26503523
theorem B11779343 : Blo 2067435 11779343 := bstep (se 1 (by rfl) ⟨8834507, by rfl⟩ : syracuseStep 11779343 = 17669015) B17669015
theorem B7852895 : Blo 2067435 7852895 := bstep (se 1 (by rfl) ⟨5889671, by rfl⟩ : syracuseStep 7852895 = 11779343) B11779343
theorem B5235263 : Blo 2067435 5235263 := bstep (se 1 (by rfl) ⟨3926447, by rfl⟩ : syracuseStep 5235263 = 7852895) B7852895
theorem B3490175 : Blo 2067435 3490175 := bstep (se 1 (by rfl) ⟨2617631, by rfl⟩ : syracuseStep 3490175 = 5235263) B5235263
theorem B2326783 : Blo 2067435 2326783 := bstep (se 1 (by rfl) ⟨1745087, by rfl⟩ : syracuseStep 2326783 = 3490175) B3490175
theorem B3102377 : Blo 2067435 3102377 := bstep (se 2 (by rfl) ⟨1163391, by rfl⟩ : syracuseStep 3102377 = 2326783) B2326783
theorem B2068251 : Blo 2067435 2068251 := bstep (se 1 (by rfl) ⟨1551188, by rfl⟩ : syracuseStep 2068251 = 3102377) B3102377
theorem B4969421 : Blo 2067435 4969421 := bbase (se 3 (by rfl) ⟨931766, by rfl⟩ : syracuseStep 4969421 = 1863533) (by norm_num)
theorem B3312947 : Blo 2067435 3312947 := bstep (se 1 (by rfl) ⟨2484710, by rfl⟩ : syracuseStep 3312947 = 4969421) B4969421
theorem B2208631 : Blo 2067435 2208631 := bstep (se 1 (by rfl) ⟨1656473, by rfl⟩ : syracuseStep 2208631 = 3312947) B3312947
theorem B2944841 : Blo 2067435 2944841 := bstep (se 2 (by rfl) ⟨1104315, by rfl⟩ : syracuseStep 2944841 = 2208631) B2208631
theorem B7852909 : Blo 2067435 7852909 := bstep (se 3 (by rfl) ⟨1472420, by rfl⟩ : syracuseStep 7852909 = 2944841) B2944841
theorem B10470545 : Blo 2067435 10470545 := bstep (se 2 (by rfl) ⟨3926454, by rfl⟩ : syracuseStep 10470545 = 7852909) B7852909
theorem B6980363 : Blo 2067435 6980363 := bstep (se 1 (by rfl) ⟨5235272, by rfl⟩ : syracuseStep 6980363 = 10470545) B10470545
theorem B4653575 : Blo 2067435 4653575 := bstep (se 1 (by rfl) ⟨3490181, by rfl⟩ : syracuseStep 4653575 = 6980363) B6980363
theorem B3102383 : Blo 2067435 3102383 := bstep (se 1 (by rfl) ⟨2326787, by rfl⟩ : syracuseStep 3102383 = 4653575) B4653575
theorem B2068255 : Blo 2067435 2068255 := bstep (se 1 (by rfl) ⟨1551191, by rfl⟩ : syracuseStep 2068255 = 3102383) B3102383
theorem B3102389 : Blo 2067435 3102389 := bbase (se 5 (by rfl) ⟨145424, by rfl⟩ : syracuseStep 3102389 = 290849) (by norm_num)
theorem B2068259 : Blo 2067435 2068259 := bstep (se 1 (by rfl) ⟨1551194, by rfl⟩ : syracuseStep 2068259 = 3102389) B3102389
theorem B5235293 : Blo 2067435 5235293 := bbase (se 3 (by rfl) ⟨981617, by rfl⟩ : syracuseStep 5235293 = 1963235) (by norm_num)
theorem B3490195 : Blo 2067435 3490195 := bstep (se 1 (by rfl) ⟨2617646, by rfl⟩ : syracuseStep 3490195 = 5235293) B5235293
theorem B4653593 : Blo 2067435 4653593 := bstep (se 2 (by rfl) ⟨1745097, by rfl⟩ : syracuseStep 4653593 = 3490195) B3490195
theorem B3102395 : Blo 2067435 3102395 := bstep (se 1 (by rfl) ⟨2326796, by rfl⟩ : syracuseStep 3102395 = 4653593) B4653593
theorem B2068263 : Blo 2067435 2068263 := bstep (se 1 (by rfl) ⟨1551197, by rfl⟩ : syracuseStep 2068263 = 3102395) B3102395
theorem B2326801 : Blo 2067435 2326801 := bbase (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) (by norm_num)
theorem B3102401 : Blo 2067435 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B2068267 : Blo 2067435 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B3926485 : Blo 2067435 3926485 := bbase (se 7 (by rfl) ⟨46013, by rfl⟩ : syracuseStep 3926485 = 92027) (by norm_num)
theorem B5235313 : Blo 2067435 5235313 := bstep (se 2 (by rfl) ⟨1963242, by rfl⟩ : syracuseStep 5235313 = 3926485) B3926485
theorem B6980417 : Blo 2067435 6980417 := bstep (se 2 (by rfl) ⟨2617656, by rfl⟩ : syracuseStep 6980417 = 5235313) B5235313
theorem B4653611 : Blo 2067435 4653611 := bstep (se 1 (by rfl) ⟨3490208, by rfl⟩ : syracuseStep 4653611 = 6980417) B6980417
theorem B3102407 : Blo 2067435 3102407 := bstep (se 1 (by rfl) ⟨2326805, by rfl⟩ : syracuseStep 3102407 = 4653611) B4653611
theorem B2068271 : Blo 2067435 2068271 := bstep (se 1 (by rfl) ⟨1551203, by rfl⟩ : syracuseStep 2068271 = 3102407) B3102407
theorem B3102413 : Blo 2067435 3102413 := bbase (se 3 (by rfl) ⟨581702, by rfl⟩ : syracuseStep 3102413 = 1163405) (by norm_num)
theorem B2068275 : Blo 2067435 2068275 := bstep (se 1 (by rfl) ⟨1551206, by rfl⟩ : syracuseStep 2068275 = 3102413) B3102413
theorem B4653629 : Blo 2067435 4653629 := bbase (se 3 (by rfl) ⟨872555, by rfl⟩ : syracuseStep 4653629 = 1745111) (by norm_num)
theorem B3102419 : Blo 2067435 3102419 := bstep (se 1 (by rfl) ⟨2326814, by rfl⟩ : syracuseStep 3102419 = 4653629) B4653629
theorem B2068279 : Blo 2067435 2068279 := bstep (se 1 (by rfl) ⟨1551209, by rfl⟩ : syracuseStep 2068279 = 3102419) B3102419
theorem B3490229 : Blo 2067435 3490229 := bbase (se 5 (by rfl) ⟨163604, by rfl⟩ : syracuseStep 3490229 = 327209) (by norm_num)
theorem B2326819 : Blo 2067435 2326819 := bstep (se 1 (by rfl) ⟨1745114, by rfl⟩ : syracuseStep 2326819 = 3490229) B3490229
theorem B3102425 : Blo 2067435 3102425 := bstep (se 2 (by rfl) ⟨1163409, by rfl⟩ : syracuseStep 3102425 = 2326819) B2326819
theorem B2068283 : Blo 2067435 2068283 := bstep (se 1 (by rfl) ⟨1551212, by rfl⟩ : syracuseStep 2068283 = 3102425) B3102425
theorem B2208665 : Blo 2067435 2208665 := bbase (se 2 (by rfl) ⟨828249, by rfl⟩ : syracuseStep 2208665 = 1656499) (by norm_num)
theorem B5889773 : Blo 2067435 5889773 := bstep (se 3 (by rfl) ⟨1104332, by rfl⟩ : syracuseStep 5889773 = 2208665) B2208665
theorem B15706061 : Blo 2067435 15706061 := bstep (se 3 (by rfl) ⟨2944886, by rfl⟩ : syracuseStep 15706061 = 5889773) B5889773
theorem B10470707 : Blo 2067435 10470707 := bstep (se 1 (by rfl) ⟨7853030, by rfl⟩ : syracuseStep 10470707 = 15706061) B15706061
theorem B6980471 : Blo 2067435 6980471 := bstep (se 1 (by rfl) ⟨5235353, by rfl⟩ : syracuseStep 6980471 = 10470707) B10470707
theorem B4653647 : Blo 2067435 4653647 := bstep (se 1 (by rfl) ⟨3490235, by rfl⟩ : syracuseStep 4653647 = 6980471) B6980471
theorem B3102431 : Blo 2067435 3102431 := bstep (se 1 (by rfl) ⟨2326823, by rfl⟩ : syracuseStep 3102431 = 4653647) B4653647
theorem B2068287 : Blo 2067435 2068287 := bstep (se 1 (by rfl) ⟨1551215, by rfl⟩ : syracuseStep 2068287 = 3102431) B3102431
theorem B3102437 : Blo 2067435 3102437 := bbase (se 4 (by rfl) ⟨290853, by rfl⟩ : syracuseStep 3102437 = 581707) (by norm_num)
theorem B2068291 : Blo 2067435 2068291 := bstep (se 1 (by rfl) ⟨1551218, by rfl⟩ : syracuseStep 2068291 = 3102437) B3102437
theorem B5889797 : Blo 2067435 5889797 := bbase (se 4 (by rfl) ⟨552168, by rfl⟩ : syracuseStep 5889797 = 1104337) (by norm_num)
theorem B3926531 : Blo 2067435 3926531 := bstep (se 1 (by rfl) ⟨2944898, by rfl⟩ : syracuseStep 3926531 = 5889797) B5889797
theorem B2617687 : Blo 2067435 2617687 := bstep (se 1 (by rfl) ⟨1963265, by rfl⟩ : syracuseStep 2617687 = 3926531) B3926531
theorem B3490249 : Blo 2067435 3490249 := bstep (se 2 (by rfl) ⟨1308843, by rfl⟩ : syracuseStep 3490249 = 2617687) B2617687
theorem B4653665 : Blo 2067435 4653665 := bstep (se 2 (by rfl) ⟨1745124, by rfl⟩ : syracuseStep 4653665 = 3490249) B3490249
theorem B3102443 : Blo 2067435 3102443 := bstep (se 1 (by rfl) ⟨2326832, by rfl⟩ : syracuseStep 3102443 = 4653665) B4653665
theorem B2068295 : Blo 2067435 2068295 := bstep (se 1 (by rfl) ⟨1551221, by rfl⟩ : syracuseStep 2068295 = 3102443) B3102443
theorem B2326837 : Blo 2067435 2326837 := bbase (se 5 (by rfl) ⟨109070, by rfl⟩ : syracuseStep 2326837 = 218141) (by norm_num)
theorem B3102449 : Blo 2067435 3102449 := bstep (se 2 (by rfl) ⟨1163418, by rfl⟩ : syracuseStep 3102449 = 2326837) B2326837
theorem B2068299 : Blo 2067435 2068299 := bstep (se 1 (by rfl) ⟨1551224, by rfl⟩ : syracuseStep 2068299 = 3102449) B3102449
theorem B2617697 : Blo 2067435 2617697 := bbase (se 2 (by rfl) ⟨981636, by rfl⟩ : syracuseStep 2617697 = 1963273) (by norm_num)
theorem B6980525 : Blo 2067435 6980525 := bstep (se 3 (by rfl) ⟨1308848, by rfl⟩ : syracuseStep 6980525 = 2617697) B2617697
theorem B4653683 : Blo 2067435 4653683 := bstep (se 1 (by rfl) ⟨3490262, by rfl⟩ : syracuseStep 4653683 = 6980525) B6980525
theorem B3102455 : Blo 2067435 3102455 := bstep (se 1 (by rfl) ⟨2326841, by rfl⟩ : syracuseStep 3102455 = 4653683) B4653683
theorem B2068303 : Blo 2067435 2068303 := bstep (se 1 (by rfl) ⟨1551227, by rfl⟩ : syracuseStep 2068303 = 3102455) B3102455
theorem B3102461 : Blo 2067435 3102461 := bbase (se 3 (by rfl) ⟨581711, by rfl⟩ : syracuseStep 3102461 = 1163423) (by norm_num)
theorem B2068307 : Blo 2067435 2068307 := bstep (se 1 (by rfl) ⟨1551230, by rfl⟩ : syracuseStep 2068307 = 3102461) B3102461
theorem B4653701 : Blo 2067435 4653701 := bbase (se 4 (by rfl) ⟨436284, by rfl⟩ : syracuseStep 4653701 = 872569) (by norm_num)
theorem B3102467 : Blo 2067435 3102467 := bstep (se 1 (by rfl) ⟨2326850, by rfl⟩ : syracuseStep 3102467 = 4653701) B4653701
theorem B2068311 : Blo 2067435 2068311 := bstep (se 1 (by rfl) ⟨1551233, by rfl⟩ : syracuseStep 2068311 = 3102467) B3102467
theorem B4477661 : Blo 2067435 4477661 := bbase (se 3 (by rfl) ⟨839561, by rfl⟩ : syracuseStep 4477661 = 1679123) (by norm_num)
theorem B2985107 : Blo 2067435 2985107 := bstep (se 1 (by rfl) ⟨2238830, by rfl⟩ : syracuseStep 2985107 = 4477661) B4477661
theorem B7960285 : Blo 2067435 7960285 := bstep (se 3 (by rfl) ⟨1492553, by rfl⟩ : syracuseStep 7960285 = 2985107) B2985107
theorem B10613713 : Blo 2067435 10613713 := bstep (se 2 (by rfl) ⟨3980142, by rfl⟩ : syracuseStep 10613713 = 7960285) B7960285
theorem B14151617 : Blo 2067435 14151617 := bstep (se 2 (by rfl) ⟨5306856, by rfl⟩ : syracuseStep 14151617 = 10613713) B10613713
theorem B9434411 : Blo 2067435 9434411 := bstep (se 1 (by rfl) ⟨7075808, by rfl⟩ : syracuseStep 9434411 = 14151617) B14151617
theorem B6289607 : Blo 2067435 6289607 := bstep (se 1 (by rfl) ⟨4717205, by rfl⟩ : syracuseStep 6289607 = 9434411) B9434411
theorem B16772285 : Blo 2067435 16772285 := bstep (se 3 (by rfl) ⟨3144803, by rfl⟩ : syracuseStep 16772285 = 6289607) B6289607
theorem B11181523 : Blo 2067435 11181523 := bstep (se 1 (by rfl) ⟨8386142, by rfl⟩ : syracuseStep 11181523 = 16772285) B16772285
theorem B14908697 : Blo 2067435 14908697 := bstep (se 2 (by rfl) ⟨5590761, by rfl⟩ : syracuseStep 14908697 = 11181523) B11181523
theorem B9939131 : Blo 2067435 9939131 := bstep (se 1 (by rfl) ⟨7454348, by rfl⟩ : syracuseStep 9939131 = 14908697) B14908697
theorem B6626087 : Blo 2067435 6626087 := bstep (se 1 (by rfl) ⟨4969565, by rfl⟩ : syracuseStep 6626087 = 9939131) B9939131
theorem B4417391 : Blo 2067435 4417391 := bstep (se 1 (by rfl) ⟨3313043, by rfl⟩ : syracuseStep 4417391 = 6626087) B6626087
theorem B2944927 : Blo 2067435 2944927 := bstep (se 1 (by rfl) ⟨2208695, by rfl⟩ : syracuseStep 2944927 = 4417391) B4417391
theorem B3926569 : Blo 2067435 3926569 := bstep (se 2 (by rfl) ⟨1472463, by rfl⟩ : syracuseStep 3926569 = 2944927) B2944927
theorem B5235425 : Blo 2067435 5235425 := bstep (se 2 (by rfl) ⟨1963284, by rfl⟩ : syracuseStep 5235425 = 3926569) B3926569
theorem B3490283 : Blo 2067435 3490283 := bstep (se 1 (by rfl) ⟨2617712, by rfl⟩ : syracuseStep 3490283 = 5235425) B5235425
theorem B2326855 : Blo 2067435 2326855 := bstep (se 1 (by rfl) ⟨1745141, by rfl⟩ : syracuseStep 2326855 = 3490283) B3490283
theorem B3102473 : Blo 2067435 3102473 := bstep (se 2 (by rfl) ⟨1163427, by rfl⟩ : syracuseStep 3102473 = 2326855) B2326855
theorem B2068315 : Blo 2067435 2068315 := bstep (se 1 (by rfl) ⟨1551236, by rfl⟩ : syracuseStep 2068315 = 3102473) B3102473
theorem B10470869 : Blo 2067435 10470869 := bbase (se 7 (by rfl) ⟨122705, by rfl⟩ : syracuseStep 10470869 = 245411) (by norm_num)
theorem B6980579 : Blo 2067435 6980579 := bstep (se 1 (by rfl) ⟨5235434, by rfl⟩ : syracuseStep 6980579 = 10470869) B10470869
theorem B4653719 : Blo 2067435 4653719 := bstep (se 1 (by rfl) ⟨3490289, by rfl⟩ : syracuseStep 4653719 = 6980579) B6980579
theorem B3102479 : Blo 2067435 3102479 := bstep (se 1 (by rfl) ⟨2326859, by rfl⟩ : syracuseStep 3102479 = 4653719) B4653719
theorem B2068319 : Blo 2067435 2068319 := bstep (se 1 (by rfl) ⟨1551239, by rfl⟩ : syracuseStep 2068319 = 3102479) B3102479
theorem B3102485 : Blo 2067435 3102485 := bbase (se 6 (by rfl) ⟨72714, by rfl⟩ : syracuseStep 3102485 = 145429) (by norm_num)
theorem B2068323 : Blo 2067435 2068323 := bstep (se 1 (by rfl) ⟨1551242, by rfl⟩ : syracuseStep 2068323 = 3102485) B3102485
theorem B27232661 : Blo 2067435 27232661 := bbase (se 6 (by rfl) ⟨638265, by rfl⟩ : syracuseStep 27232661 = 1276531) (by norm_num)
theorem B18155107 : Blo 2067435 18155107 := bstep (se 1 (by rfl) ⟨13616330, by rfl⟩ : syracuseStep 18155107 = 27232661) B27232661
theorem B24206809 : Blo 2067435 24206809 := bstep (se 2 (by rfl) ⟨9077553, by rfl⟩ : syracuseStep 24206809 = 18155107) B18155107
theorem B32275745 : Blo 2067435 32275745 := bstep (se 2 (by rfl) ⟨12103404, by rfl⟩ : syracuseStep 32275745 = 24206809) B24206809
theorem B21517163 : Blo 2067435 21517163 := bstep (se 1 (by rfl) ⟨16137872, by rfl⟩ : syracuseStep 21517163 = 32275745) B32275745
theorem B14344775 : Blo 2067435 14344775 := bstep (se 1 (by rfl) ⟨10758581, by rfl⟩ : syracuseStep 14344775 = 21517163) B21517163
theorem B9563183 : Blo 2067435 9563183 := bstep (se 1 (by rfl) ⟨7172387, by rfl⟩ : syracuseStep 9563183 = 14344775) B14344775
theorem B6375455 : Blo 2067435 6375455 := bstep (se 1 (by rfl) ⟨4781591, by rfl⟩ : syracuseStep 6375455 = 9563183) B9563183
theorem B4250303 : Blo 2067435 4250303 := bstep (se 1 (by rfl) ⟨3187727, by rfl⟩ : syracuseStep 4250303 = 6375455) B6375455
theorem B2833535 : Blo 2067435 2833535 := bstep (se 1 (by rfl) ⟨2125151, by rfl⟩ : syracuseStep 2833535 = 4250303) B4250303
theorem B7556093 : Blo 2067435 7556093 := bstep (se 3 (by rfl) ⟨1416767, by rfl⟩ : syracuseStep 7556093 = 2833535) B2833535
theorem B5037395 : Blo 2067435 5037395 := bstep (se 1 (by rfl) ⟨3778046, by rfl⟩ : syracuseStep 5037395 = 7556093) B7556093
theorem B13433053 : Blo 2067435 13433053 := bstep (se 3 (by rfl) ⟨2518697, by rfl⟩ : syracuseStep 13433053 = 5037395) B5037395
theorem B17910737 : Blo 2067435 17910737 := bstep (se 2 (by rfl) ⟨6716526, by rfl⟩ : syracuseStep 17910737 = 13433053) B13433053
theorem B11940491 : Blo 2067435 11940491 := bstep (se 1 (by rfl) ⟨8955368, by rfl⟩ : syracuseStep 11940491 = 17910737) B17910737
theorem B31841309 : Blo 2067435 31841309 := bstep (se 3 (by rfl) ⟨5970245, by rfl⟩ : syracuseStep 31841309 = 11940491) B11940491
theorem B84910157 : Blo 2067435 84910157 := bstep (se 3 (by rfl) ⟨15920654, by rfl⟩ : syracuseStep 84910157 = 31841309) B31841309
theorem B56606771 : Blo 2067435 56606771 := bstep (se 1 (by rfl) ⟨42455078, by rfl⟩ : syracuseStep 56606771 = 84910157) B84910157
theorem B37737847 : Blo 2067435 37737847 := bstep (se 1 (by rfl) ⟨28303385, by rfl⟩ : syracuseStep 37737847 = 56606771) B56606771
theorem B50317129 : Blo 2067435 50317129 := bstep (se 2 (by rfl) ⟨18868923, by rfl⟩ : syracuseStep 50317129 = 37737847) B37737847
theorem B67089505 : Blo 2067435 67089505 := bstep (se 2 (by rfl) ⟨25158564, by rfl⟩ : syracuseStep 67089505 = 50317129) B50317129
theorem B89452673 : Blo 2067435 89452673 := bstep (se 2 (by rfl) ⟨33544752, by rfl⟩ : syracuseStep 89452673 = 67089505) B67089505
theorem B59635115 : Blo 2067435 59635115 := bstep (se 1 (by rfl) ⟨44726336, by rfl⟩ : syracuseStep 59635115 = 89452673) B89452673
theorem B39756743 : Blo 2067435 39756743 := bstep (se 1 (by rfl) ⟨29817557, by rfl⟩ : syracuseStep 39756743 = 59635115) B59635115
theorem B26504495 : Blo 2067435 26504495 := bstep (se 1 (by rfl) ⟨19878371, by rfl⟩ : syracuseStep 26504495 = 39756743) B39756743
theorem B17669663 : Blo 2067435 17669663 := bstep (se 1 (by rfl) ⟨13252247, by rfl⟩ : syracuseStep 17669663 = 26504495) B26504495
theorem B11779775 : Blo 2067435 11779775 := bstep (se 1 (by rfl) ⟨8834831, by rfl⟩ : syracuseStep 11779775 = 17669663) B17669663
theorem B7853183 : Blo 2067435 7853183 := bstep (se 1 (by rfl) ⟨5889887, by rfl⟩ : syracuseStep 7853183 = 11779775) B11779775
theorem B5235455 : Blo 2067435 5235455 := bstep (se 1 (by rfl) ⟨3926591, by rfl⟩ : syracuseStep 5235455 = 7853183) B7853183
theorem B3490303 : Blo 2067435 3490303 := bstep (se 1 (by rfl) ⟨2617727, by rfl⟩ : syracuseStep 3490303 = 5235455) B5235455
theorem B4653737 : Blo 2067435 4653737 := bstep (se 2 (by rfl) ⟨1745151, by rfl⟩ : syracuseStep 4653737 = 3490303) B3490303
theorem B3102491 : Blo 2067435 3102491 := bstep (se 1 (by rfl) ⟨2326868, by rfl⟩ : syracuseStep 3102491 = 4653737) B4653737
theorem B2068327 : Blo 2067435 2068327 := bstep (se 1 (by rfl) ⟨1551245, by rfl⟩ : syracuseStep 2068327 = 3102491) B3102491
theorem B2326873 : Blo 2067435 2326873 := bbase (se 2 (by rfl) ⟨872577, by rfl⟩ : syracuseStep 2326873 = 1745155) (by norm_num)
theorem B3102497 : Blo 2067435 3102497 := bstep (se 2 (by rfl) ⟨1163436, by rfl⟩ : syracuseStep 3102497 = 2326873) B2326873
theorem B2068331 : Blo 2067435 2068331 := bstep (se 1 (by rfl) ⟨1551248, by rfl⟩ : syracuseStep 2068331 = 3102497) B3102497
theorem B4969613 : Blo 2067435 4969613 := bbase (se 3 (by rfl) ⟨931802, by rfl⟩ : syracuseStep 4969613 = 1863605) (by norm_num)
theorem B3313075 : Blo 2067435 3313075 := bstep (se 1 (by rfl) ⟨2484806, by rfl⟩ : syracuseStep 3313075 = 4969613) B4969613
theorem B4417433 : Blo 2067435 4417433 := bstep (se 2 (by rfl) ⟨1656537, by rfl⟩ : syracuseStep 4417433 = 3313075) B3313075
theorem B2944955 : Blo 2067435 2944955 := bstep (se 1 (by rfl) ⟨2208716, by rfl⟩ : syracuseStep 2944955 = 4417433) B4417433
theorem B7853213 : Blo 2067435 7853213 := bstep (se 3 (by rfl) ⟨1472477, by rfl⟩ : syracuseStep 7853213 = 2944955) B2944955
theorem B5235475 : Blo 2067435 5235475 := bstep (se 1 (by rfl) ⟨3926606, by rfl⟩ : syracuseStep 5235475 = 7853213) B7853213
theorem B6980633 : Blo 2067435 6980633 := bstep (se 2 (by rfl) ⟨2617737, by rfl⟩ : syracuseStep 6980633 = 5235475) B5235475
theorem B4653755 : Blo 2067435 4653755 := bstep (se 1 (by rfl) ⟨3490316, by rfl⟩ : syracuseStep 4653755 = 6980633) B6980633
theorem B3102503 : Blo 2067435 3102503 := bstep (se 1 (by rfl) ⟨2326877, by rfl⟩ : syracuseStep 3102503 = 4653755) B4653755
theorem B2068335 : Blo 2067435 2068335 := bstep (se 1 (by rfl) ⟨1551251, by rfl⟩ : syracuseStep 2068335 = 3102503) B3102503
theorem B3102509 : Blo 2067435 3102509 := bbase (se 3 (by rfl) ⟨581720, by rfl⟩ : syracuseStep 3102509 = 1163441) (by norm_num)
theorem B2068339 : Blo 2067435 2068339 := bstep (se 1 (by rfl) ⟨1551254, by rfl⟩ : syracuseStep 2068339 = 3102509) B3102509
theorem B4653773 : Blo 2067435 4653773 := bbase (se 3 (by rfl) ⟨872582, by rfl⟩ : syracuseStep 4653773 = 1745165) (by norm_num)
theorem B3102515 : Blo 2067435 3102515 := bstep (se 1 (by rfl) ⟨2326886, by rfl⟩ : syracuseStep 3102515 = 4653773) B4653773
theorem B2068343 : Blo 2067435 2068343 := bstep (se 1 (by rfl) ⟨1551257, by rfl⟩ : syracuseStep 2068343 = 3102515) B3102515
theorem B2617753 : Blo 2067435 2617753 := bbase (se 2 (by rfl) ⟨981657, by rfl⟩ : syracuseStep 2617753 = 1963315) (by norm_num)
theorem B3490337 : Blo 2067435 3490337 := bstep (se 2 (by rfl) ⟨1308876, by rfl⟩ : syracuseStep 3490337 = 2617753) B2617753
theorem B2326891 : Blo 2067435 2326891 := bstep (se 1 (by rfl) ⟨1745168, by rfl⟩ : syracuseStep 2326891 = 3490337) B3490337
theorem B3102521 : Blo 2067435 3102521 := bstep (se 2 (by rfl) ⟨1163445, by rfl⟩ : syracuseStep 3102521 = 2326891) B2326891
theorem B2068347 : Blo 2067435 2068347 := bstep (se 1 (by rfl) ⟨1551260, by rfl⟩ : syracuseStep 2068347 = 3102521) B3102521
theorem B8834933 : Blo 2067435 8834933 := bbase (se 5 (by rfl) ⟨414137, by rfl⟩ : syracuseStep 8834933 = 828275) (by norm_num)
theorem B23559821 : Blo 2067435 23559821 := bstep (se 3 (by rfl) ⟨4417466, by rfl⟩ : syracuseStep 23559821 = 8834933) B8834933
theorem B15706547 : Blo 2067435 15706547 := bstep (se 1 (by rfl) ⟨11779910, by rfl⟩ : syracuseStep 15706547 = 23559821) B23559821
theorem B10471031 : Blo 2067435 10471031 := bstep (se 1 (by rfl) ⟨7853273, by rfl⟩ : syracuseStep 10471031 = 15706547) B15706547
theorem B6980687 : Blo 2067435 6980687 := bstep (se 1 (by rfl) ⟨5235515, by rfl⟩ : syracuseStep 6980687 = 10471031) B10471031
theorem B4653791 : Blo 2067435 4653791 := bstep (se 1 (by rfl) ⟨3490343, by rfl⟩ : syracuseStep 4653791 = 6980687) B6980687
theorem B3102527 : Blo 2067435 3102527 := bstep (se 1 (by rfl) ⟨2326895, by rfl⟩ : syracuseStep 3102527 = 4653791) B4653791
theorem B2068351 : Blo 2067435 2068351 := bstep (se 1 (by rfl) ⟨1551263, by rfl⟩ : syracuseStep 2068351 = 3102527) B3102527
theorem B3102533 : Blo 2067435 3102533 := bbase (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) (by norm_num)
theorem B2068355 : Blo 2067435 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B3490357 : Blo 2067435 3490357 := bbase (se 5 (by rfl) ⟨163610, by rfl⟩ : syracuseStep 3490357 = 327221) (by norm_num)
theorem B4653809 : Blo 2067435 4653809 := bstep (se 2 (by rfl) ⟨1745178, by rfl⟩ : syracuseStep 4653809 = 3490357) B3490357
theorem B3102539 : Blo 2067435 3102539 := bstep (se 1 (by rfl) ⟨2326904, by rfl⟩ : syracuseStep 3102539 = 4653809) B4653809
theorem B2068359 : Blo 2067435 2068359 := bstep (se 1 (by rfl) ⟨1551269, by rfl⟩ : syracuseStep 2068359 = 3102539) B3102539
theorem B2326909 : Blo 2067435 2326909 := bbase (se 3 (by rfl) ⟨436295, by rfl⟩ : syracuseStep 2326909 = 872591) (by norm_num)
theorem B3102545 : Blo 2067435 3102545 := bstep (se 2 (by rfl) ⟨1163454, by rfl⟩ : syracuseStep 3102545 = 2326909) B2326909
theorem B2068363 : Blo 2067435 2068363 := bstep (se 1 (by rfl) ⟨1551272, by rfl⟩ : syracuseStep 2068363 = 3102545) B3102545
theorem B6980741 : Blo 2067435 6980741 := bbase (se 4 (by rfl) ⟨654444, by rfl⟩ : syracuseStep 6980741 = 1308889) (by norm_num)
theorem B4653827 : Blo 2067435 4653827 := bstep (se 1 (by rfl) ⟨3490370, by rfl⟩ : syracuseStep 4653827 = 6980741) B6980741
theorem B3102551 : Blo 2067435 3102551 := bstep (se 1 (by rfl) ⟨2326913, by rfl⟩ : syracuseStep 3102551 = 4653827) B4653827
theorem B2068367 : Blo 2067435 2068367 := bstep (se 1 (by rfl) ⟨1551275, by rfl⟩ : syracuseStep 2068367 = 3102551) B3102551
theorem B3102557 : Blo 2067435 3102557 := bbase (se 3 (by rfl) ⟨581729, by rfl⟩ : syracuseStep 3102557 = 1163459) (by norm_num)
theorem B2068371 : Blo 2067435 2068371 := bstep (se 1 (by rfl) ⟨1551278, by rfl⟩ : syracuseStep 2068371 = 3102557) B3102557
theorem B4653845 : Blo 2067435 4653845 := bbase (se 6 (by rfl) ⟨109074, by rfl⟩ : syracuseStep 4653845 = 218149) (by norm_num)
theorem B3102563 : Blo 2067435 3102563 := bstep (se 1 (by rfl) ⟨2326922, by rfl⟩ : syracuseStep 3102563 = 4653845) B4653845
theorem B2068375 : Blo 2067435 2068375 := bstep (se 1 (by rfl) ⟨1551281, by rfl⟩ : syracuseStep 2068375 = 3102563) B3102563
theorem B7853381 : Blo 2067435 7853381 := bbase (se 4 (by rfl) ⟨736254, by rfl⟩ : syracuseStep 7853381 = 1472509) (by norm_num)
theorem B5235587 : Blo 2067435 5235587 := bstep (se 1 (by rfl) ⟨3926690, by rfl⟩ : syracuseStep 5235587 = 7853381) B7853381
theorem B3490391 : Blo 2067435 3490391 := bstep (se 1 (by rfl) ⟨2617793, by rfl⟩ : syracuseStep 3490391 = 5235587) B5235587
theorem B2326927 : Blo 2067435 2326927 := bstep (se 1 (by rfl) ⟨1745195, by rfl⟩ : syracuseStep 2326927 = 3490391) B3490391
theorem B3102569 : Blo 2067435 3102569 := bstep (se 2 (by rfl) ⟨1163463, by rfl⟩ : syracuseStep 3102569 = 2326927) B2326927
theorem B2068379 : Blo 2067435 2068379 := bstep (se 1 (by rfl) ⟨1551284, by rfl⟩ : syracuseStep 2068379 = 3102569) B3102569
theorem B2243585 : Blo 2067435 2243585 := bbase (se 2 (by rfl) ⟨841344, by rfl⟩ : syracuseStep 2243585 = 1682689) (by norm_num)
theorem B5982893 : Blo 2067435 5982893 := bstep (se 3 (by rfl) ⟨1121792, by rfl⟩ : syracuseStep 5982893 = 2243585) B2243585
theorem B3988595 : Blo 2067435 3988595 := bstep (se 1 (by rfl) ⟨2991446, by rfl⟩ : syracuseStep 3988595 = 5982893) B5982893
theorem B10636253 : Blo 2067435 10636253 := bstep (se 3 (by rfl) ⟨1994297, by rfl⟩ : syracuseStep 10636253 = 3988595) B3988595
theorem B7090835 : Blo 2067435 7090835 := bstep (se 1 (by rfl) ⟨5318126, by rfl⟩ : syracuseStep 7090835 = 10636253) B10636253
theorem B18908893 : Blo 2067435 18908893 := bstep (se 3 (by rfl) ⟨3545417, by rfl⟩ : syracuseStep 18908893 = 7090835) B7090835
theorem B25211857 : Blo 2067435 25211857 := bstep (se 2 (by rfl) ⟨9454446, by rfl⟩ : syracuseStep 25211857 = 18908893) B18908893
theorem B33615809 : Blo 2067435 33615809 := bstep (se 2 (by rfl) ⟨12605928, by rfl⟩ : syracuseStep 33615809 = 25211857) B25211857
theorem B22410539 : Blo 2067435 22410539 := bstep (se 1 (by rfl) ⟨16807904, by rfl⟩ : syracuseStep 22410539 = 33615809) B33615809
theorem B14940359 : Blo 2067435 14940359 := bstep (se 1 (by rfl) ⟨11205269, by rfl⟩ : syracuseStep 14940359 = 22410539) B22410539
theorem B9960239 : Blo 2067435 9960239 := bstep (se 1 (by rfl) ⟨7470179, by rfl⟩ : syracuseStep 9960239 = 14940359) B14940359
theorem B6640159 : Blo 2067435 6640159 := bstep (se 1 (by rfl) ⟨4980119, by rfl⟩ : syracuseStep 6640159 = 9960239) B9960239
theorem B8853545 : Blo 2067435 8853545 := bstep (se 2 (by rfl) ⟨3320079, by rfl⟩ : syracuseStep 8853545 = 6640159) B6640159
theorem B5902363 : Blo 2067435 5902363 := bstep (se 1 (by rfl) ⟨4426772, by rfl⟩ : syracuseStep 5902363 = 8853545) B8853545
theorem B7869817 : Blo 2067435 7869817 := bstep (se 2 (by rfl) ⟨2951181, by rfl⟩ : syracuseStep 7869817 = 5902363) B5902363
theorem B41972357 : Blo 2067435 41972357 := bstep (se 4 (by rfl) ⟨3934908, by rfl⟩ : syracuseStep 41972357 = 7869817) B7869817
theorem B27981571 : Blo 2067435 27981571 := bstep (se 1 (by rfl) ⟨20986178, by rfl⟩ : syracuseStep 27981571 = 41972357) B41972357
theorem B37308761 : Blo 2067435 37308761 := bstep (se 2 (by rfl) ⟨13990785, by rfl⟩ : syracuseStep 37308761 = 27981571) B27981571
theorem B24872507 : Blo 2067435 24872507 := bstep (se 1 (by rfl) ⟨18654380, by rfl⟩ : syracuseStep 24872507 = 37308761) B37308761
theorem B16581671 : Blo 2067435 16581671 := bstep (se 1 (by rfl) ⟨12436253, by rfl⟩ : syracuseStep 16581671 = 24872507) B24872507
theorem B11054447 : Blo 2067435 11054447 := bstep (se 1 (by rfl) ⟨8290835, by rfl⟩ : syracuseStep 11054447 = 16581671) B16581671
theorem B7369631 : Blo 2067435 7369631 := bstep (se 1 (by rfl) ⟨5527223, by rfl⟩ : syracuseStep 7369631 = 11054447) B11054447
theorem B4913087 : Blo 2067435 4913087 := bstep (se 1 (by rfl) ⟨3684815, by rfl⟩ : syracuseStep 4913087 = 7369631) B7369631
theorem B52406261 : Blo 2067435 52406261 := bstep (se 5 (by rfl) ⟨2456543, by rfl⟩ : syracuseStep 52406261 = 4913087) B4913087
theorem B34937507 : Blo 2067435 34937507 := bstep (se 1 (by rfl) ⟨26203130, by rfl⟩ : syracuseStep 34937507 = 52406261) B52406261
theorem B23291671 : Blo 2067435 23291671 := bstep (se 1 (by rfl) ⟨17468753, by rfl⟩ : syracuseStep 23291671 = 34937507) B34937507
theorem B31055561 : Blo 2067435 31055561 := bstep (se 2 (by rfl) ⟨11645835, by rfl⟩ : syracuseStep 31055561 = 23291671) B23291671
theorem B20703707 : Blo 2067435 20703707 := bstep (se 1 (by rfl) ⟨15527780, by rfl⟩ : syracuseStep 20703707 = 31055561) B31055561
theorem B13802471 : Blo 2067435 13802471 := bstep (se 1 (by rfl) ⟨10351853, by rfl⟩ : syracuseStep 13802471 = 20703707) B20703707
theorem B9201647 : Blo 2067435 9201647 := bstep (se 1 (by rfl) ⟨6901235, by rfl⟩ : syracuseStep 9201647 = 13802471) B13802471
theorem B24537725 : Blo 2067435 24537725 := bstep (se 3 (by rfl) ⟨4600823, by rfl⟩ : syracuseStep 24537725 = 9201647) B9201647
theorem B16358483 : Blo 2067435 16358483 := bstep (se 1 (by rfl) ⟨12268862, by rfl⟩ : syracuseStep 16358483 = 24537725) B24537725
theorem B43622621 : Blo 2067435 43622621 := bstep (se 3 (by rfl) ⟨8179241, by rfl⟩ : syracuseStep 43622621 = 16358483) B16358483
theorem B29081747 : Blo 2067435 29081747 := bstep (se 1 (by rfl) ⟨21811310, by rfl⟩ : syracuseStep 29081747 = 43622621) B43622621
theorem B19387831 : Blo 2067435 19387831 := bstep (se 1 (by rfl) ⟨14540873, by rfl⟩ : syracuseStep 19387831 = 29081747) B29081747
theorem B25850441 : Blo 2067435 25850441 := bstep (se 2 (by rfl) ⟨9693915, by rfl⟩ : syracuseStep 25850441 = 19387831) B19387831
theorem B68934509 : Blo 2067435 68934509 := bstep (se 3 (by rfl) ⟨12925220, by rfl⟩ : syracuseStep 68934509 = 25850441) B25850441
theorem B45956339 : Blo 2067435 45956339 := bstep (se 1 (by rfl) ⟨34467254, by rfl⟩ : syracuseStep 45956339 = 68934509) B68934509
theorem B30637559 : Blo 2067435 30637559 := bstep (se 1 (by rfl) ⟨22978169, by rfl⟩ : syracuseStep 30637559 = 45956339) B45956339
theorem B81700157 : Blo 2067435 81700157 := bstep (se 3 (by rfl) ⟨15318779, by rfl⟩ : syracuseStep 81700157 = 30637559) B30637559
theorem B54466771 : Blo 2067435 54466771 := bstep (se 1 (by rfl) ⟨40850078, by rfl⟩ : syracuseStep 54466771 = 81700157) B81700157
theorem B72622361 : Blo 2067435 72622361 := bstep (se 2 (by rfl) ⟨27233385, by rfl⟩ : syracuseStep 72622361 = 54466771) B54466771
theorem B48414907 : Blo 2067435 48414907 := bstep (se 1 (by rfl) ⟨36311180, by rfl⟩ : syracuseStep 48414907 = 72622361) B72622361
theorem B258212837 : Blo 2067435 258212837 := bstep (se 4 (by rfl) ⟨24207453, by rfl⟩ : syracuseStep 258212837 = 48414907) B48414907
theorem B172141891 : Blo 2067435 172141891 := bstep (se 1 (by rfl) ⟨129106418, by rfl⟩ : syracuseStep 172141891 = 258212837) B258212837
theorem B3672360341 : Blo 2067435 3672360341 := bstep (se 6 (by rfl) ⟨86070945, by rfl⟩ : syracuseStep 3672360341 = 172141891) B172141891
theorem B2448240227 : Blo 2067435 2448240227 := bstep (se 1 (by rfl) ⟨1836180170, by rfl⟩ : syracuseStep 2448240227 = 3672360341) B3672360341
theorem B1632160151 : Blo 2067435 1632160151 := bstep (se 1 (by rfl) ⟨1224120113, by rfl⟩ : syracuseStep 1632160151 = 2448240227) B2448240227
theorem B1088106767 : Blo 2067435 1088106767 := bstep (se 1 (by rfl) ⟨816080075, by rfl⟩ : syracuseStep 1088106767 = 1632160151) B1632160151
theorem B725404511 : Blo 2067435 725404511 := bstep (se 1 (by rfl) ⟨544053383, by rfl⟩ : syracuseStep 725404511 = 1088106767) B1088106767
theorem B483603007 : Blo 2067435 483603007 := bstep (se 1 (by rfl) ⟨362702255, by rfl⟩ : syracuseStep 483603007 = 725404511) B725404511
theorem B644804009 : Blo 2067435 644804009 := bstep (se 2 (by rfl) ⟨241801503, by rfl⟩ : syracuseStep 644804009 = 483603007) B483603007
theorem B429869339 : Blo 2067435 429869339 := bstep (se 1 (by rfl) ⟨322402004, by rfl⟩ : syracuseStep 429869339 = 644804009) B644804009
theorem B286579559 : Blo 2067435 286579559 := bstep (se 1 (by rfl) ⟨214934669, by rfl⟩ : syracuseStep 286579559 = 429869339) B429869339
theorem B191053039 : Blo 2067435 191053039 := bstep (se 1 (by rfl) ⟨143289779, by rfl⟩ : syracuseStep 191053039 = 286579559) B286579559
theorem B254737385 : Blo 2067435 254737385 := bstep (se 2 (by rfl) ⟨95526519, by rfl⟩ : syracuseStep 254737385 = 191053039) B191053039
theorem B169824923 : Blo 2067435 169824923 := bstep (se 1 (by rfl) ⟨127368692, by rfl⟩ : syracuseStep 169824923 = 254737385) B254737385
theorem B113216615 : Blo 2067435 113216615 := bstep (se 1 (by rfl) ⟨84912461, by rfl⟩ : syracuseStep 113216615 = 169824923) B169824923
theorem B75477743 : Blo 2067435 75477743 := bstep (se 1 (by rfl) ⟨56608307, by rfl⟩ : syracuseStep 75477743 = 113216615) B113216615
theorem B50318495 : Blo 2067435 50318495 := bstep (se 1 (by rfl) ⟨37738871, by rfl⟩ : syracuseStep 50318495 = 75477743) B75477743
theorem B33545663 : Blo 2067435 33545663 := bstep (se 1 (by rfl) ⟨25159247, by rfl⟩ : syracuseStep 33545663 = 50318495) B50318495
theorem B22363775 : Blo 2067435 22363775 := bstep (se 1 (by rfl) ⟨16772831, by rfl⟩ : syracuseStep 22363775 = 33545663) B33545663
theorem B14909183 : Blo 2067435 14909183 := bstep (se 1 (by rfl) ⟨11181887, by rfl⟩ : syracuseStep 14909183 = 22363775) B22363775
theorem B9939455 : Blo 2067435 9939455 := bstep (se 1 (by rfl) ⟨7454591, by rfl⟩ : syracuseStep 9939455 = 14909183) B14909183
theorem B6626303 : Blo 2067435 6626303 := bstep (se 1 (by rfl) ⟨4969727, by rfl⟩ : syracuseStep 6626303 = 9939455) B9939455
theorem B4417535 : Blo 2067435 4417535 := bstep (se 1 (by rfl) ⟨3313151, by rfl⟩ : syracuseStep 4417535 = 6626303) B6626303
theorem B11780093 : Blo 2067435 11780093 := bstep (se 3 (by rfl) ⟨2208767, by rfl⟩ : syracuseStep 11780093 = 4417535) B4417535
theorem B7853395 : Blo 2067435 7853395 := bstep (se 1 (by rfl) ⟨5890046, by rfl⟩ : syracuseStep 7853395 = 11780093) B11780093
theorem B10471193 : Blo 2067435 10471193 := bstep (se 2 (by rfl) ⟨3926697, by rfl⟩ : syracuseStep 10471193 = 7853395) B7853395
theorem B6980795 : Blo 2067435 6980795 := bstep (se 1 (by rfl) ⟨5235596, by rfl⟩ : syracuseStep 6980795 = 10471193) B10471193
theorem B4653863 : Blo 2067435 4653863 := bstep (se 1 (by rfl) ⟨3490397, by rfl⟩ : syracuseStep 4653863 = 6980795) B6980795
theorem B3102575 : Blo 2067435 3102575 := bstep (se 1 (by rfl) ⟨2326931, by rfl⟩ : syracuseStep 3102575 = 4653863) B4653863
theorem B2068383 : Blo 2067435 2068383 := bstep (se 1 (by rfl) ⟨1551287, by rfl⟩ : syracuseStep 2068383 = 3102575) B3102575
theorem B3102581 : Blo 2067435 3102581 := bbase (se 5 (by rfl) ⟨145433, by rfl⟩ : syracuseStep 3102581 = 290867) (by norm_num)
theorem B2068387 : Blo 2067435 2068387 := bstep (se 1 (by rfl) ⟨1551290, by rfl⟩ : syracuseStep 2068387 = 3102581) B3102581
theorem B3313165 : Blo 2067435 3313165 := bbase (se 3 (by rfl) ⟨621218, by rfl⟩ : syracuseStep 3313165 = 1242437) (by norm_num)
theorem B4417553 : Blo 2067435 4417553 := bstep (se 2 (by rfl) ⟨1656582, by rfl⟩ : syracuseStep 4417553 = 3313165) B3313165
theorem B2945035 : Blo 2067435 2945035 := bstep (se 1 (by rfl) ⟨2208776, by rfl⟩ : syracuseStep 2945035 = 4417553) B4417553
theorem B3926713 : Blo 2067435 3926713 := bstep (se 2 (by rfl) ⟨1472517, by rfl⟩ : syracuseStep 3926713 = 2945035) B2945035
theorem B5235617 : Blo 2067435 5235617 := bstep (se 2 (by rfl) ⟨1963356, by rfl⟩ : syracuseStep 5235617 = 3926713) B3926713
theorem B3490411 : Blo 2067435 3490411 := bstep (se 1 (by rfl) ⟨2617808, by rfl⟩ : syracuseStep 3490411 = 5235617) B5235617
theorem B4653881 : Blo 2067435 4653881 := bstep (se 2 (by rfl) ⟨1745205, by rfl⟩ : syracuseStep 4653881 = 3490411) B3490411
theorem B3102587 : Blo 2067435 3102587 := bstep (se 1 (by rfl) ⟨2326940, by rfl⟩ : syracuseStep 3102587 = 4653881) B4653881
theorem B2068391 : Blo 2067435 2068391 := bstep (se 1 (by rfl) ⟨1551293, by rfl⟩ : syracuseStep 2068391 = 3102587) B3102587
theorem B2326945 : Blo 2067435 2326945 := bbase (se 2 (by rfl) ⟨872604, by rfl⟩ : syracuseStep 2326945 = 1745209) (by norm_num)
theorem B3102593 : Blo 2067435 3102593 := bstep (se 2 (by rfl) ⟨1163472, by rfl⟩ : syracuseStep 3102593 = 2326945) B2326945
theorem B2068395 : Blo 2067435 2068395 := bstep (se 1 (by rfl) ⟨1551296, by rfl⟩ : syracuseStep 2068395 = 3102593) B3102593
theorem B5235637 : Blo 2067435 5235637 := bbase (se 5 (by rfl) ⟨245420, by rfl⟩ : syracuseStep 5235637 = 490841) (by norm_num)
theorem B6980849 : Blo 2067435 6980849 := bstep (se 2 (by rfl) ⟨2617818, by rfl⟩ : syracuseStep 6980849 = 5235637) B5235637
theorem B4653899 : Blo 2067435 4653899 := bstep (se 1 (by rfl) ⟨3490424, by rfl⟩ : syracuseStep 4653899 = 6980849) B6980849
theorem B3102599 : Blo 2067435 3102599 := bstep (se 1 (by rfl) ⟨2326949, by rfl⟩ : syracuseStep 3102599 = 4653899) B4653899
theorem B2068399 : Blo 2067435 2068399 := bstep (se 1 (by rfl) ⟨1551299, by rfl⟩ : syracuseStep 2068399 = 3102599) B3102599
theorem B3102605 : Blo 2067435 3102605 := bbase (se 3 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 3102605 = 1163477) (by norm_num)
theorem B2068403 : Blo 2067435 2068403 := bstep (se 1 (by rfl) ⟨1551302, by rfl⟩ : syracuseStep 2068403 = 3102605) B3102605
theorem B4653917 : Blo 2067435 4653917 := bbase (se 3 (by rfl) ⟨872609, by rfl⟩ : syracuseStep 4653917 = 1745219) (by norm_num)
theorem B3102611 : Blo 2067435 3102611 := bstep (se 1 (by rfl) ⟨2326958, by rfl⟩ : syracuseStep 3102611 = 4653917) B4653917
theorem B2068407 : Blo 2067435 2068407 := bstep (se 1 (by rfl) ⟨1551305, by rfl⟩ : syracuseStep 2068407 = 3102611) B3102611
theorem B3490445 : Blo 2067435 3490445 := bbase (se 3 (by rfl) ⟨654458, by rfl⟩ : syracuseStep 3490445 = 1308917) (by norm_num)
theorem B2326963 : Blo 2067435 2326963 := bstep (se 1 (by rfl) ⟨1745222, by rfl⟩ : syracuseStep 2326963 = 3490445) B3490445
theorem B3102617 : Blo 2067435 3102617 := bstep (se 2 (by rfl) ⟨1163481, by rfl⟩ : syracuseStep 3102617 = 2326963) B2326963
theorem B2068411 : Blo 2067435 2068411 := bstep (se 1 (by rfl) ⟨1551308, by rfl⟩ : syracuseStep 2068411 = 3102617) B3102617
theorem B6626405 : Blo 2067435 6626405 := bbase (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) (by norm_num)
theorem B17670413 : Blo 2067435 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B11780275 : Blo 2067435 11780275 := bstep (se 1 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 11780275 = 17670413) B17670413
theorem B15707033 : Blo 2067435 15707033 := bstep (se 2 (by rfl) ⟨5890137, by rfl⟩ : syracuseStep 15707033 = 11780275) B11780275
theorem B10471355 : Blo 2067435 10471355 := bstep (se 1 (by rfl) ⟨7853516, by rfl⟩ : syracuseStep 10471355 = 15707033) B15707033
theorem B6980903 : Blo 2067435 6980903 := bstep (se 1 (by rfl) ⟨5235677, by rfl⟩ : syracuseStep 6980903 = 10471355) B10471355
theorem B4653935 : Blo 2067435 4653935 := bstep (se 1 (by rfl) ⟨3490451, by rfl⟩ : syracuseStep 4653935 = 6980903) B6980903
theorem B3102623 : Blo 2067435 3102623 := bstep (se 1 (by rfl) ⟨2326967, by rfl⟩ : syracuseStep 3102623 = 4653935) B4653935
theorem B2068415 : Blo 2067435 2068415 := bstep (se 1 (by rfl) ⟨1551311, by rfl⟩ : syracuseStep 2068415 = 3102623) B3102623
theorem B3102629 : Blo 2067435 3102629 := bbase (se 4 (by rfl) ⟨290871, by rfl⟩ : syracuseStep 3102629 = 581743) (by norm_num)
theorem B2068419 : Blo 2067435 2068419 := bstep (se 1 (by rfl) ⟨1551314, by rfl⟩ : syracuseStep 2068419 = 3102629) B3102629
theorem B2617849 : Blo 2067435 2617849 := bbase (se 2 (by rfl) ⟨981693, by rfl⟩ : syracuseStep 2617849 = 1963387) (by norm_num)
theorem B3490465 : Blo 2067435 3490465 := bstep (se 2 (by rfl) ⟨1308924, by rfl⟩ : syracuseStep 3490465 = 2617849) B2617849
theorem B4653953 : Blo 2067435 4653953 := bstep (se 2 (by rfl) ⟨1745232, by rfl⟩ : syracuseStep 4653953 = 3490465) B3490465
theorem B3102635 : Blo 2067435 3102635 := bstep (se 1 (by rfl) ⟨2326976, by rfl⟩ : syracuseStep 3102635 = 4653953) B4653953
theorem B2068423 : Blo 2067435 2068423 := bstep (se 1 (by rfl) ⟨1551317, by rfl⟩ : syracuseStep 2068423 = 3102635) B3102635
theorem B2326981 : Blo 2067435 2326981 := bbase (se 4 (by rfl) ⟨218154, by rfl⟩ : syracuseStep 2326981 = 436309) (by norm_num)
theorem B3102641 : Blo 2067435 3102641 := bstep (se 2 (by rfl) ⟨1163490, by rfl⟩ : syracuseStep 3102641 = 2326981) B2326981
theorem B2068427 : Blo 2067435 2068427 := bstep (se 1 (by rfl) ⟨1551320, by rfl⟩ : syracuseStep 2068427 = 3102641) B3102641
theorem B3926789 : Blo 2067435 3926789 := bbase (se 4 (by rfl) ⟨368136, by rfl⟩ : syracuseStep 3926789 = 736273) (by norm_num)
theorem B2617859 : Blo 2067435 2617859 := bstep (se 1 (by rfl) ⟨1963394, by rfl⟩ : syracuseStep 2617859 = 3926789) B3926789
theorem B6980957 : Blo 2067435 6980957 := bstep (se 3 (by rfl) ⟨1308929, by rfl⟩ : syracuseStep 6980957 = 2617859) B2617859
theorem B4653971 : Blo 2067435 4653971 := bstep (se 1 (by rfl) ⟨3490478, by rfl⟩ : syracuseStep 4653971 = 6980957) B6980957
theorem B3102647 : Blo 2067435 3102647 := bstep (se 1 (by rfl) ⟨2326985, by rfl⟩ : syracuseStep 3102647 = 4653971) B4653971
theorem B2068431 : Blo 2067435 2068431 := bstep (se 1 (by rfl) ⟨1551323, by rfl⟩ : syracuseStep 2068431 = 3102647) B3102647
theorem B3102653 : Blo 2067435 3102653 := bbase (se 3 (by rfl) ⟨581747, by rfl⟩ : syracuseStep 3102653 = 1163495) (by norm_num)
theorem B2068435 : Blo 2067435 2068435 := bstep (se 1 (by rfl) ⟨1551326, by rfl⟩ : syracuseStep 2068435 = 3102653) B3102653
theorem B4653989 : Blo 2067435 4653989 := bbase (se 4 (by rfl) ⟨436311, by rfl⟩ : syracuseStep 4653989 = 872623) (by norm_num)
theorem B3102659 : Blo 2067435 3102659 := bstep (se 1 (by rfl) ⟨2326994, by rfl⟩ : syracuseStep 3102659 = 4653989) B4653989
theorem B2068439 : Blo 2067435 2068439 := bstep (se 1 (by rfl) ⟨1551329, by rfl⟩ : syracuseStep 2068439 = 3102659) B3102659
theorem B5235749 : Blo 2067435 5235749 := bbase (se 4 (by rfl) ⟨490851, by rfl⟩ : syracuseStep 5235749 = 981703) (by norm_num)
theorem B3490499 : Blo 2067435 3490499 := bstep (se 1 (by rfl) ⟨2617874, by rfl⟩ : syracuseStep 3490499 = 5235749) B5235749
theorem B2326999 : Blo 2067435 2326999 := bstep (se 1 (by rfl) ⟨1745249, by rfl⟩ : syracuseStep 2326999 = 3490499) B3490499
theorem B3102665 : Blo 2067435 3102665 := bstep (se 2 (by rfl) ⟨1163499, by rfl⟩ : syracuseStep 3102665 = 2326999) B2326999
theorem B2068443 : Blo 2067435 2068443 := bstep (se 1 (by rfl) ⟨1551332, by rfl⟩ : syracuseStep 2068443 = 3102665) B3102665
theorem B5890229 : Blo 2067435 5890229 := bbase (se 5 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 5890229 = 552209) (by norm_num)
theorem B3926819 : Blo 2067435 3926819 := bstep (se 1 (by rfl) ⟨2945114, by rfl⟩ : syracuseStep 3926819 = 5890229) B5890229
theorem B10471517 : Blo 2067435 10471517 := bstep (se 3 (by rfl) ⟨1963409, by rfl⟩ : syracuseStep 10471517 = 3926819) B3926819
theorem B6981011 : Blo 2067435 6981011 := bstep (se 1 (by rfl) ⟨5235758, by rfl⟩ : syracuseStep 6981011 = 10471517) B10471517
theorem B4654007 : Blo 2067435 4654007 := bstep (se 1 (by rfl) ⟨3490505, by rfl⟩ : syracuseStep 4654007 = 6981011) B6981011
theorem B3102671 : Blo 2067435 3102671 := bstep (se 1 (by rfl) ⟨2327003, by rfl⟩ : syracuseStep 3102671 = 4654007) B4654007
theorem B2068447 : Blo 2067435 2068447 := bstep (se 1 (by rfl) ⟨1551335, by rfl⟩ : syracuseStep 2068447 = 3102671) B3102671
theorem B3102677 : Blo 2067435 3102677 := bbase (se 7 (by rfl) ⟨36359, by rfl⟩ : syracuseStep 3102677 = 72719) (by norm_num)
theorem B2068451 : Blo 2067435 2068451 := bstep (se 1 (by rfl) ⟨1551338, by rfl⟩ : syracuseStep 2068451 = 3102677) B3102677
theorem B7853669 : Blo 2067435 7853669 := bbase (se 4 (by rfl) ⟨736281, by rfl⟩ : syracuseStep 7853669 = 1472563) (by norm_num)
theorem B5235779 : Blo 2067435 5235779 := bstep (se 1 (by rfl) ⟨3926834, by rfl⟩ : syracuseStep 5235779 = 7853669) B7853669
theorem B3490519 : Blo 2067435 3490519 := bstep (se 1 (by rfl) ⟨2617889, by rfl⟩ : syracuseStep 3490519 = 5235779) B5235779
theorem B4654025 : Blo 2067435 4654025 := bstep (se 2 (by rfl) ⟨1745259, by rfl⟩ : syracuseStep 4654025 = 3490519) B3490519
theorem B3102683 : Blo 2067435 3102683 := bstep (se 1 (by rfl) ⟨2327012, by rfl⟩ : syracuseStep 3102683 = 4654025) B4654025
theorem B2068455 : Blo 2067435 2068455 := bstep (se 1 (by rfl) ⟨1551341, by rfl⟩ : syracuseStep 2068455 = 3102683) B3102683
theorem B2327017 : Blo 2067435 2327017 := bbase (se 2 (by rfl) ⟨872631, by rfl⟩ : syracuseStep 2327017 = 1745263) (by norm_num)
theorem B3102689 : Blo 2067435 3102689 := bstep (se 2 (by rfl) ⟨1163508, by rfl⟩ : syracuseStep 3102689 = 2327017) B2327017
theorem B2068459 : Blo 2067435 2068459 := bstep (se 1 (by rfl) ⟨1551344, by rfl⟩ : syracuseStep 2068459 = 3102689) B3102689
theorem B2208853 : Blo 2067435 2208853 := bbase (se 8 (by rfl) ⟨12942, by rfl⟩ : syracuseStep 2208853 = 25885) (by norm_num)
theorem B11780549 : Blo 2067435 11780549 := bstep (se 4 (by rfl) ⟨1104426, by rfl⟩ : syracuseStep 11780549 = 2208853) B2208853
theorem B7853699 : Blo 2067435 7853699 := bstep (se 1 (by rfl) ⟨5890274, by rfl⟩ : syracuseStep 7853699 = 11780549) B11780549
theorem B5235799 : Blo 2067435 5235799 := bstep (se 1 (by rfl) ⟨3926849, by rfl⟩ : syracuseStep 5235799 = 7853699) B7853699
theorem B6981065 : Blo 2067435 6981065 := bstep (se 2 (by rfl) ⟨2617899, by rfl⟩ : syracuseStep 6981065 = 5235799) B5235799
theorem B4654043 : Blo 2067435 4654043 := bstep (se 1 (by rfl) ⟨3490532, by rfl⟩ : syracuseStep 4654043 = 6981065) B6981065
theorem B3102695 : Blo 2067435 3102695 := bstep (se 1 (by rfl) ⟨2327021, by rfl⟩ : syracuseStep 3102695 = 4654043) B4654043
theorem B2068463 : Blo 2067435 2068463 := bstep (se 1 (by rfl) ⟨1551347, by rfl⟩ : syracuseStep 2068463 = 3102695) B3102695
theorem B3102701 : Blo 2067435 3102701 := bbase (se 3 (by rfl) ⟨581756, by rfl⟩ : syracuseStep 3102701 = 1163513) (by norm_num)
theorem B2068467 : Blo 2067435 2068467 := bstep (se 1 (by rfl) ⟨1551350, by rfl⟩ : syracuseStep 2068467 = 3102701) B3102701
theorem B4654061 : Blo 2067435 4654061 := bbase (se 3 (by rfl) ⟨872636, by rfl⟩ : syracuseStep 4654061 = 1745273) (by norm_num)
theorem B3102707 : Blo 2067435 3102707 := bstep (se 1 (by rfl) ⟨2327030, by rfl⟩ : syracuseStep 3102707 = 4654061) B4654061
theorem B2068471 : Blo 2067435 2068471 := bstep (se 1 (by rfl) ⟨1551353, by rfl⟩ : syracuseStep 2068471 = 3102707) B3102707
theorem B4417733 : Blo 2067435 4417733 := bbase (se 4 (by rfl) ⟨414162, by rfl⟩ : syracuseStep 4417733 = 828325) (by norm_num)
theorem B2945155 : Blo 2067435 2945155 := bstep (se 1 (by rfl) ⟨2208866, by rfl⟩ : syracuseStep 2945155 = 4417733) B4417733
theorem B3926873 : Blo 2067435 3926873 := bstep (se 2 (by rfl) ⟨1472577, by rfl⟩ : syracuseStep 3926873 = 2945155) B2945155
theorem B2617915 : Blo 2067435 2617915 := bstep (se 1 (by rfl) ⟨1963436, by rfl⟩ : syracuseStep 2617915 = 3926873) B3926873
theorem B3490553 : Blo 2067435 3490553 := bstep (se 2 (by rfl) ⟨1308957, by rfl⟩ : syracuseStep 3490553 = 2617915) B2617915
theorem B2327035 : Blo 2067435 2327035 := bstep (se 1 (by rfl) ⟨1745276, by rfl⟩ : syracuseStep 2327035 = 3490553) B3490553
theorem B3102713 : Blo 2067435 3102713 := bstep (se 2 (by rfl) ⟨1163517, by rfl⟩ : syracuseStep 3102713 = 2327035) B2327035
theorem B2068475 : Blo 2067435 2068475 := bstep (se 1 (by rfl) ⟨1551356, by rfl⟩ : syracuseStep 2068475 = 3102713) B3102713
theorem B6375925 : Blo 2067435 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B8501233 : Blo 2067435 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B11334977 : Blo 2067435 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B7556651 : Blo 2067435 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B5037767 : Blo 2067435 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B3358511 : Blo 2067435 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B2239007 : Blo 2067435 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B5970685 : Blo 2067435 5970685 := bstep (se 3 (by rfl) ⟨1119503, by rfl⟩ : syracuseStep 5970685 = 2239007) B2239007
theorem B7960913 : Blo 2067435 7960913 := bstep (se 2 (by rfl) ⟨2985342, by rfl⟩ : syracuseStep 7960913 = 5970685) B5970685
theorem B5307275 : Blo 2067435 5307275 := bstep (se 1 (by rfl) ⟨3980456, by rfl⟩ : syracuseStep 5307275 = 7960913) B7960913
theorem B3538183 : Blo 2067435 3538183 := bstep (se 1 (by rfl) ⟨2653637, by rfl⟩ : syracuseStep 3538183 = 5307275) B5307275
theorem B4717577 : Blo 2067435 4717577 := bstep (se 2 (by rfl) ⟨1769091, by rfl⟩ : syracuseStep 4717577 = 3538183) B3538183
theorem B12580205 : Blo 2067435 12580205 := bstep (se 3 (by rfl) ⟨2358788, by rfl⟩ : syracuseStep 12580205 = 4717577) B4717577
theorem B33547213 : Blo 2067435 33547213 := bstep (se 3 (by rfl) ⟨6290102, by rfl⟩ : syracuseStep 33547213 = 12580205) B12580205
theorem B178918469 : Blo 2067435 178918469 := bstep (se 4 (by rfl) ⟨16773606, by rfl⟩ : syracuseStep 178918469 = 33547213) B33547213
theorem B119278979 : Blo 2067435 119278979 := bstep (se 1 (by rfl) ⟨89459234, by rfl⟩ : syracuseStep 119278979 = 178918469) B178918469
theorem B79519319 : Blo 2067435 79519319 := bstep (se 1 (by rfl) ⟨59639489, by rfl⟩ : syracuseStep 79519319 = 119278979) B119278979
theorem B53012879 : Blo 2067435 53012879 := bstep (se 1 (by rfl) ⟨39759659, by rfl⟩ : syracuseStep 53012879 = 79519319) B79519319
theorem B35341919 : Blo 2067435 35341919 := bstep (se 1 (by rfl) ⟨26506439, by rfl⟩ : syracuseStep 35341919 = 53012879) B53012879
theorem B23561279 : Blo 2067435 23561279 := bstep (se 1 (by rfl) ⟨17670959, by rfl⟩ : syracuseStep 23561279 = 35341919) B35341919
theorem B15707519 : Blo 2067435 15707519 := bstep (se 1 (by rfl) ⟨11780639, by rfl⟩ : syracuseStep 15707519 = 23561279) B23561279
theorem B10471679 : Blo 2067435 10471679 := bstep (se 1 (by rfl) ⟨7853759, by rfl⟩ : syracuseStep 10471679 = 15707519) B15707519
theorem B6981119 : Blo 2067435 6981119 := bstep (se 1 (by rfl) ⟨5235839, by rfl⟩ : syracuseStep 6981119 = 10471679) B10471679
theorem B4654079 : Blo 2067435 4654079 := bstep (se 1 (by rfl) ⟨3490559, by rfl⟩ : syracuseStep 4654079 = 6981119) B6981119
theorem B3102719 : Blo 2067435 3102719 := bstep (se 1 (by rfl) ⟨2327039, by rfl⟩ : syracuseStep 3102719 = 4654079) B4654079
theorem B2068479 : Blo 2067435 2068479 := bstep (se 1 (by rfl) ⟨1551359, by rfl⟩ : syracuseStep 2068479 = 3102719) B3102719
theorem B3102725 : Blo 2067435 3102725 := bbase (se 4 (by rfl) ⟨290880, by rfl⟩ : syracuseStep 3102725 = 581761) (by norm_num)
theorem B2068483 : Blo 2067435 2068483 := bstep (se 1 (by rfl) ⟨1551362, by rfl⟩ : syracuseStep 2068483 = 3102725) B3102725
theorem B3490573 : Blo 2067435 3490573 := bbase (se 3 (by rfl) ⟨654482, by rfl⟩ : syracuseStep 3490573 = 1308965) (by norm_num)
theorem B4654097 : Blo 2067435 4654097 := bstep (se 2 (by rfl) ⟨1745286, by rfl⟩ : syracuseStep 4654097 = 3490573) B3490573
theorem B3102731 : Blo 2067435 3102731 := bstep (se 1 (by rfl) ⟨2327048, by rfl⟩ : syracuseStep 3102731 = 4654097) B4654097
theorem B2068487 : Blo 2067435 2068487 := bstep (se 1 (by rfl) ⟨1551365, by rfl⟩ : syracuseStep 2068487 = 3102731) B3102731
theorem B2327053 : Blo 2067435 2327053 := bbase (se 3 (by rfl) ⟨436322, by rfl⟩ : syracuseStep 2327053 = 872645) (by norm_num)
theorem B3102737 : Blo 2067435 3102737 := bstep (se 2 (by rfl) ⟨1163526, by rfl⟩ : syracuseStep 3102737 = 2327053) B2327053
theorem B2068491 : Blo 2067435 2068491 := bstep (se 1 (by rfl) ⟨1551368, by rfl⟩ : syracuseStep 2068491 = 3102737) B3102737
theorem B6981173 : Blo 2067435 6981173 := bbase (se 5 (by rfl) ⟨327242, by rfl⟩ : syracuseStep 6981173 = 654485) (by norm_num)
theorem B4654115 : Blo 2067435 4654115 := bstep (se 1 (by rfl) ⟨3490586, by rfl⟩ : syracuseStep 4654115 = 6981173) B6981173
theorem B3102743 : Blo 2067435 3102743 := bstep (se 1 (by rfl) ⟨2327057, by rfl⟩ : syracuseStep 3102743 = 4654115) B4654115
theorem B2068495 : Blo 2067435 2068495 := bstep (se 1 (by rfl) ⟨1551371, by rfl⟩ : syracuseStep 2068495 = 3102743) B3102743
theorem B3102749 : Blo 2067435 3102749 := bbase (se 3 (by rfl) ⟨581765, by rfl⟩ : syracuseStep 3102749 = 1163531) (by norm_num)
theorem B2068499 : Blo 2067435 2068499 := bstep (se 1 (by rfl) ⟨1551374, by rfl⟩ : syracuseStep 2068499 = 3102749) B3102749
theorem B4654133 : Blo 2067435 4654133 := bbase (se 5 (by rfl) ⟨218162, by rfl⟩ : syracuseStep 4654133 = 436325) (by norm_num)
theorem B3102755 : Blo 2067435 3102755 := bstep (se 1 (by rfl) ⟨2327066, by rfl⟩ : syracuseStep 3102755 = 4654133) B4654133
theorem B2068503 : Blo 2067435 2068503 := bstep (se 1 (by rfl) ⟨1551377, by rfl⟩ : syracuseStep 2068503 = 3102755) B3102755
theorem B2485013 : Blo 2067435 2485013 := bbase (se 6 (by rfl) ⟨58242, by rfl⟩ : syracuseStep 2485013 = 116485) (by norm_num)
theorem B6626701 : Blo 2067435 6626701 := bstep (se 3 (by rfl) ⟨1242506, by rfl⟩ : syracuseStep 6626701 = 2485013) B2485013
theorem B8835601 : Blo 2067435 8835601 := bstep (se 2 (by rfl) ⟨3313350, by rfl⟩ : syracuseStep 8835601 = 6626701) B6626701
theorem B11780801 : Blo 2067435 11780801 := bstep (se 2 (by rfl) ⟨4417800, by rfl⟩ : syracuseStep 11780801 = 8835601) B8835601
theorem B7853867 : Blo 2067435 7853867 := bstep (se 1 (by rfl) ⟨5890400, by rfl⟩ : syracuseStep 7853867 = 11780801) B11780801
theorem B5235911 : Blo 2067435 5235911 := bstep (se 1 (by rfl) ⟨3926933, by rfl⟩ : syracuseStep 5235911 = 7853867) B7853867
theorem B3490607 : Blo 2067435 3490607 := bstep (se 1 (by rfl) ⟨2617955, by rfl⟩ : syracuseStep 3490607 = 5235911) B5235911
theorem B2327071 : Blo 2067435 2327071 := bstep (se 1 (by rfl) ⟨1745303, by rfl⟩ : syracuseStep 2327071 = 3490607) B3490607
theorem B3102761 : Blo 2067435 3102761 := bstep (se 2 (by rfl) ⟨1163535, by rfl⟩ : syracuseStep 3102761 = 2327071) B2327071
theorem B2068507 : Blo 2067435 2068507 := bstep (se 1 (by rfl) ⟨1551380, by rfl⟩ : syracuseStep 2068507 = 3102761) B3102761
theorem B2795645 : Blo 2067435 2795645 := bbase (se 3 (by rfl) ⟨524183, by rfl⟩ : syracuseStep 2795645 = 1048367) (by norm_num)
theorem B7455053 : Blo 2067435 7455053 := bstep (se 3 (by rfl) ⟨1397822, by rfl⟩ : syracuseStep 7455053 = 2795645) B2795645
theorem B4970035 : Blo 2067435 4970035 := bstep (se 1 (by rfl) ⟨3727526, by rfl⟩ : syracuseStep 4970035 = 7455053) B7455053
theorem B6626713 : Blo 2067435 6626713 := bstep (se 2 (by rfl) ⟨2485017, by rfl⟩ : syracuseStep 6626713 = 4970035) B4970035
theorem B8835617 : Blo 2067435 8835617 := bstep (se 2 (by rfl) ⟨3313356, by rfl⟩ : syracuseStep 8835617 = 6626713) B6626713
theorem B5890411 : Blo 2067435 5890411 := bstep (se 1 (by rfl) ⟨4417808, by rfl⟩ : syracuseStep 5890411 = 8835617) B8835617
theorem B7853881 : Blo 2067435 7853881 := bstep (se 2 (by rfl) ⟨2945205, by rfl⟩ : syracuseStep 7853881 = 5890411) B5890411
theorem B10471841 : Blo 2067435 10471841 := bstep (se 2 (by rfl) ⟨3926940, by rfl⟩ : syracuseStep 10471841 = 7853881) B7853881
theorem B6981227 : Blo 2067435 6981227 := bstep (se 1 (by rfl) ⟨5235920, by rfl⟩ : syracuseStep 6981227 = 10471841) B10471841
theorem B4654151 : Blo 2067435 4654151 := bstep (se 1 (by rfl) ⟨3490613, by rfl⟩ : syracuseStep 4654151 = 6981227) B6981227
theorem B3102767 : Blo 2067435 3102767 := bstep (se 1 (by rfl) ⟨2327075, by rfl⟩ : syracuseStep 3102767 = 4654151) B4654151
theorem B2068511 : Blo 2067435 2068511 := bstep (se 1 (by rfl) ⟨1551383, by rfl⟩ : syracuseStep 2068511 = 3102767) B3102767
theorem B3102773 : Blo 2067435 3102773 := bbase (se 5 (by rfl) ⟨145442, by rfl⟩ : syracuseStep 3102773 = 290885) (by norm_num)
theorem B2068515 : Blo 2067435 2068515 := bstep (se 1 (by rfl) ⟨1551386, by rfl⟩ : syracuseStep 2068515 = 3102773) B3102773
theorem B5235941 : Blo 2067435 5235941 := bbase (se 4 (by rfl) ⟨490869, by rfl⟩ : syracuseStep 5235941 = 981739) (by norm_num)
theorem B3490627 : Blo 2067435 3490627 := bstep (se 1 (by rfl) ⟨2617970, by rfl⟩ : syracuseStep 3490627 = 5235941) B5235941
theorem B4654169 : Blo 2067435 4654169 := bstep (se 2 (by rfl) ⟨1745313, by rfl⟩ : syracuseStep 4654169 = 3490627) B3490627
theorem B3102779 : Blo 2067435 3102779 := bstep (se 1 (by rfl) ⟨2327084, by rfl⟩ : syracuseStep 3102779 = 4654169) B4654169
theorem B2068519 : Blo 2067435 2068519 := bstep (se 1 (by rfl) ⟨1551389, by rfl⟩ : syracuseStep 2068519 = 3102779) B3102779
theorem B2327089 : Blo 2067435 2327089 := bbase (se 2 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 2327089 = 1745317) (by norm_num)
theorem B3102785 : Blo 2067435 3102785 := bstep (se 2 (by rfl) ⟨1163544, by rfl⟩ : syracuseStep 3102785 = 2327089) B2327089
theorem B2068523 : Blo 2067435 2068523 := bstep (se 1 (by rfl) ⟨1551392, by rfl⟩ : syracuseStep 2068523 = 3102785) B3102785
theorem B2485037 : Blo 2067435 2485037 := bbase (se 3 (by rfl) ⟨465944, by rfl⟩ : syracuseStep 2485037 = 931889) (by norm_num)
theorem B6626765 : Blo 2067435 6626765 := bstep (se 3 (by rfl) ⟨1242518, by rfl⟩ : syracuseStep 6626765 = 2485037) B2485037
theorem B4417843 : Blo 2067435 4417843 := bstep (se 1 (by rfl) ⟨3313382, by rfl⟩ : syracuseStep 4417843 = 6626765) B6626765
theorem B5890457 : Blo 2067435 5890457 := bstep (se 2 (by rfl) ⟨2208921, by rfl⟩ : syracuseStep 5890457 = 4417843) B4417843
theorem B3926971 : Blo 2067435 3926971 := bstep (se 1 (by rfl) ⟨2945228, by rfl⟩ : syracuseStep 3926971 = 5890457) B5890457
theorem B5235961 : Blo 2067435 5235961 := bstep (se 2 (by rfl) ⟨1963485, by rfl⟩ : syracuseStep 5235961 = 3926971) B3926971
theorem B6981281 : Blo 2067435 6981281 := bstep (se 2 (by rfl) ⟨2617980, by rfl⟩ : syracuseStep 6981281 = 5235961) B5235961
theorem B4654187 : Blo 2067435 4654187 := bstep (se 1 (by rfl) ⟨3490640, by rfl⟩ : syracuseStep 4654187 = 6981281) B6981281
theorem B3102791 : Blo 2067435 3102791 := bstep (se 1 (by rfl) ⟨2327093, by rfl⟩ : syracuseStep 3102791 = 4654187) B4654187
theorem B2068527 : Blo 2067435 2068527 := bstep (se 1 (by rfl) ⟨1551395, by rfl⟩ : syracuseStep 2068527 = 3102791) B3102791
theorem B3102797 : Blo 2067435 3102797 := bbase (se 3 (by rfl) ⟨581774, by rfl⟩ : syracuseStep 3102797 = 1163549) (by norm_num)
theorem B2068531 : Blo 2067435 2068531 := bstep (se 1 (by rfl) ⟨1551398, by rfl⟩ : syracuseStep 2068531 = 3102797) B3102797
theorem B4654205 : Blo 2067435 4654205 := bbase (se 3 (by rfl) ⟨872663, by rfl⟩ : syracuseStep 4654205 = 1745327) (by norm_num)
theorem B3102803 : Blo 2067435 3102803 := bstep (se 1 (by rfl) ⟨2327102, by rfl⟩ : syracuseStep 3102803 = 4654205) B4654205
theorem B2068535 : Blo 2067435 2068535 := bstep (se 1 (by rfl) ⟨1551401, by rfl⟩ : syracuseStep 2068535 = 3102803) B3102803
theorem B3490661 : Blo 2067435 3490661 := bbase (se 4 (by rfl) ⟨327249, by rfl⟩ : syracuseStep 3490661 = 654499) (by norm_num)
theorem B2327107 : Blo 2067435 2327107 := bstep (se 1 (by rfl) ⟨1745330, by rfl⟩ : syracuseStep 2327107 = 3490661) B3490661
theorem B3102809 : Blo 2067435 3102809 := bstep (se 2 (by rfl) ⟨1163553, by rfl⟩ : syracuseStep 3102809 = 2327107) B2327107
theorem B2068539 : Blo 2067435 2068539 := bstep (se 1 (by rfl) ⟨1551404, by rfl⟩ : syracuseStep 2068539 = 3102809) B3102809
theorem B4417877 : Blo 2067435 4417877 := bbase (se 10 (by rfl) ⟨6471, by rfl⟩ : syracuseStep 4417877 = 12943) (by norm_num)
theorem B2945251 : Blo 2067435 2945251 := bstep (se 1 (by rfl) ⟨2208938, by rfl⟩ : syracuseStep 2945251 = 4417877) B4417877
theorem B15708005 : Blo 2067435 15708005 := bstep (se 4 (by rfl) ⟨1472625, by rfl⟩ : syracuseStep 15708005 = 2945251) B2945251
theorem B10472003 : Blo 2067435 10472003 := bstep (se 1 (by rfl) ⟨7854002, by rfl⟩ : syracuseStep 10472003 = 15708005) B15708005
theorem B6981335 : Blo 2067435 6981335 := bstep (se 1 (by rfl) ⟨5236001, by rfl⟩ : syracuseStep 6981335 = 10472003) B10472003
theorem B4654223 : Blo 2067435 4654223 := bstep (se 1 (by rfl) ⟨3490667, by rfl⟩ : syracuseStep 4654223 = 6981335) B6981335
theorem B3102815 : Blo 2067435 3102815 := bstep (se 1 (by rfl) ⟨2327111, by rfl⟩ : syracuseStep 3102815 = 4654223) B4654223
theorem B2068543 : Blo 2067435 2068543 := bstep (se 1 (by rfl) ⟨1551407, by rfl⟩ : syracuseStep 2068543 = 3102815) B3102815
theorem B3102821 : Blo 2067435 3102821 := bbase (se 4 (by rfl) ⟨290889, by rfl⟩ : syracuseStep 3102821 = 581779) (by norm_num)
theorem B2068547 : Blo 2067435 2068547 := bstep (se 1 (by rfl) ⟨1551410, by rfl⟩ : syracuseStep 2068547 = 3102821) B3102821
theorem B4250765 : Blo 2067435 4250765 := bbase (se 3 (by rfl) ⟨797018, by rfl⟩ : syracuseStep 4250765 = 1594037) (by norm_num)
theorem B11335373 : Blo 2067435 11335373 := bstep (se 3 (by rfl) ⟨2125382, by rfl⟩ : syracuseStep 11335373 = 4250765) B4250765
theorem B7556915 : Blo 2067435 7556915 := bstep (se 1 (by rfl) ⟨5667686, by rfl⟩ : syracuseStep 7556915 = 11335373) B11335373
theorem B5037943 : Blo 2067435 5037943 := bstep (se 1 (by rfl) ⟨3778457, by rfl⟩ : syracuseStep 5037943 = 7556915) B7556915
theorem B6717257 : Blo 2067435 6717257 := bstep (se 2 (by rfl) ⟨2518971, by rfl⟩ : syracuseStep 6717257 = 5037943) B5037943
theorem B4478171 : Blo 2067435 4478171 := bstep (se 1 (by rfl) ⟨3358628, by rfl⟩ : syracuseStep 4478171 = 6717257) B6717257
theorem B47767157 : Blo 2067435 47767157 := bstep (se 5 (by rfl) ⟨2239085, by rfl⟩ : syracuseStep 47767157 = 4478171) B4478171
theorem B31844771 : Blo 2067435 31844771 := bstep (se 1 (by rfl) ⟨23883578, by rfl⟩ : syracuseStep 31844771 = 47767157) B47767157
theorem B21229847 : Blo 2067435 21229847 := bstep (se 1 (by rfl) ⟨15922385, by rfl⟩ : syracuseStep 21229847 = 31844771) B31844771
theorem B14153231 : Blo 2067435 14153231 := bstep (se 1 (by rfl) ⟨10614923, by rfl⟩ : syracuseStep 14153231 = 21229847) B21229847
theorem B37741949 : Blo 2067435 37741949 := bstep (se 3 (by rfl) ⟨7076615, by rfl⟩ : syracuseStep 37741949 = 14153231) B14153231
theorem B25161299 : Blo 2067435 25161299 := bstep (se 1 (by rfl) ⟨18870974, by rfl⟩ : syracuseStep 25161299 = 37741949) B37741949
theorem B16774199 : Blo 2067435 16774199 := bstep (se 1 (by rfl) ⟨12580649, by rfl⟩ : syracuseStep 16774199 = 25161299) B25161299
theorem B11182799 : Blo 2067435 11182799 := bstep (se 1 (by rfl) ⟨8387099, by rfl⟩ : syracuseStep 11182799 = 16774199) B16774199
theorem B7455199 : Blo 2067435 7455199 := bstep (se 1 (by rfl) ⟨5591399, by rfl⟩ : syracuseStep 7455199 = 11182799) B11182799
theorem B9940265 : Blo 2067435 9940265 := bstep (se 2 (by rfl) ⟨3727599, by rfl⟩ : syracuseStep 9940265 = 7455199) B7455199
theorem B6626843 : Blo 2067435 6626843 := bstep (se 1 (by rfl) ⟨4970132, by rfl⟩ : syracuseStep 6626843 = 9940265) B9940265
theorem B4417895 : Blo 2067435 4417895 := bstep (se 1 (by rfl) ⟨3313421, by rfl⟩ : syracuseStep 4417895 = 6626843) B6626843
theorem B2945263 : Blo 2067435 2945263 := bstep (se 1 (by rfl) ⟨2208947, by rfl⟩ : syracuseStep 2945263 = 4417895) B4417895
theorem B3927017 : Blo 2067435 3927017 := bstep (se 2 (by rfl) ⟨1472631, by rfl⟩ : syracuseStep 3927017 = 2945263) B2945263
theorem B2618011 : Blo 2067435 2618011 := bstep (se 1 (by rfl) ⟨1963508, by rfl⟩ : syracuseStep 2618011 = 3927017) B3927017
theorem B3490681 : Blo 2067435 3490681 := bstep (se 2 (by rfl) ⟨1309005, by rfl⟩ : syracuseStep 3490681 = 2618011) B2618011
theorem B4654241 : Blo 2067435 4654241 := bstep (se 2 (by rfl) ⟨1745340, by rfl⟩ : syracuseStep 4654241 = 3490681) B3490681
theorem B3102827 : Blo 2067435 3102827 := bstep (se 1 (by rfl) ⟨2327120, by rfl⟩ : syracuseStep 3102827 = 4654241) B4654241
theorem B2068551 : Blo 2067435 2068551 := bstep (se 1 (by rfl) ⟨1551413, by rfl⟩ : syracuseStep 2068551 = 3102827) B3102827
theorem B2327125 : Blo 2067435 2327125 := bbase (se 8 (by rfl) ⟨13635, by rfl⟩ : syracuseStep 2327125 = 27271) (by norm_num)
theorem B3102833 : Blo 2067435 3102833 := bstep (se 2 (by rfl) ⟨1163562, by rfl⟩ : syracuseStep 3102833 = 2327125) B2327125
theorem B2068555 : Blo 2067435 2068555 := bstep (se 1 (by rfl) ⟨1551416, by rfl⟩ : syracuseStep 2068555 = 3102833) B3102833
theorem B2618021 : Blo 2067435 2618021 := bbase (se 4 (by rfl) ⟨245439, by rfl⟩ : syracuseStep 2618021 = 490879) (by norm_num)
theorem B6981389 : Blo 2067435 6981389 := bstep (se 3 (by rfl) ⟨1309010, by rfl⟩ : syracuseStep 6981389 = 2618021) B2618021
theorem B4654259 : Blo 2067435 4654259 := bstep (se 1 (by rfl) ⟨3490694, by rfl⟩ : syracuseStep 4654259 = 6981389) B6981389
theorem B3102839 : Blo 2067435 3102839 := bstep (se 1 (by rfl) ⟨2327129, by rfl⟩ : syracuseStep 3102839 = 4654259) B4654259
theorem B2068559 : Blo 2067435 2068559 := bstep (se 1 (by rfl) ⟨1551419, by rfl⟩ : syracuseStep 2068559 = 3102839) B3102839
theorem B3102845 : Blo 2067435 3102845 := bbase (se 3 (by rfl) ⟨581783, by rfl⟩ : syracuseStep 3102845 = 1163567) (by norm_num)
theorem B2068563 : Blo 2067435 2068563 := bstep (se 1 (by rfl) ⟨1551422, by rfl⟩ : syracuseStep 2068563 = 3102845) B3102845
theorem B4654277 : Blo 2067435 4654277 := bbase (se 4 (by rfl) ⟨436338, by rfl⟩ : syracuseStep 4654277 = 872677) (by norm_num)
theorem B3102851 : Blo 2067435 3102851 := bstep (se 1 (by rfl) ⟨2327138, by rfl⟩ : syracuseStep 3102851 = 4654277) B4654277
theorem B2068567 : Blo 2067435 2068567 := bstep (se 1 (by rfl) ⟨1551425, by rfl⟩ : syracuseStep 2068567 = 3102851) B3102851
theorem B13253813 : Blo 2067435 13253813 := bbase (se 5 (by rfl) ⟨621272, by rfl⟩ : syracuseStep 13253813 = 1242545) (by norm_num)
theorem B8835875 : Blo 2067435 8835875 := bstep (se 1 (by rfl) ⟨6626906, by rfl⟩ : syracuseStep 8835875 = 13253813) B13253813
theorem B5890583 : Blo 2067435 5890583 := bstep (se 1 (by rfl) ⟨4417937, by rfl⟩ : syracuseStep 5890583 = 8835875) B8835875
theorem B3927055 : Blo 2067435 3927055 := bstep (se 1 (by rfl) ⟨2945291, by rfl⟩ : syracuseStep 3927055 = 5890583) B5890583
theorem B5236073 : Blo 2067435 5236073 := bstep (se 2 (by rfl) ⟨1963527, by rfl⟩ : syracuseStep 5236073 = 3927055) B3927055
theorem B3490715 : Blo 2067435 3490715 := bstep (se 1 (by rfl) ⟨2618036, by rfl⟩ : syracuseStep 3490715 = 5236073) B5236073
theorem B2327143 : Blo 2067435 2327143 := bstep (se 1 (by rfl) ⟨1745357, by rfl⟩ : syracuseStep 2327143 = 3490715) B3490715
theorem B3102857 : Blo 2067435 3102857 := bstep (se 2 (by rfl) ⟨1163571, by rfl⟩ : syracuseStep 3102857 = 2327143) B2327143
theorem B2068571 : Blo 2067435 2068571 := bstep (se 1 (by rfl) ⟨1551428, by rfl⟩ : syracuseStep 2068571 = 3102857) B3102857
theorem B10472165 : Blo 2067435 10472165 := bbase (se 4 (by rfl) ⟨981765, by rfl⟩ : syracuseStep 10472165 = 1963531) (by norm_num)
theorem B6981443 : Blo 2067435 6981443 := bstep (se 1 (by rfl) ⟨5236082, by rfl⟩ : syracuseStep 6981443 = 10472165) B10472165
theorem B4654295 : Blo 2067435 4654295 := bstep (se 1 (by rfl) ⟨3490721, by rfl⟩ : syracuseStep 4654295 = 6981443) B6981443
theorem B3102863 : Blo 2067435 3102863 := bstep (se 1 (by rfl) ⟨2327147, by rfl⟩ : syracuseStep 3102863 = 4654295) B4654295
theorem B2068575 : Blo 2067435 2068575 := bstep (se 1 (by rfl) ⟨1551431, by rfl⟩ : syracuseStep 2068575 = 3102863) B3102863
theorem B3102869 : Blo 2067435 3102869 := bbase (se 6 (by rfl) ⟨72723, by rfl⟩ : syracuseStep 3102869 = 145447) (by norm_num)
theorem B2068579 : Blo 2067435 2068579 := bstep (se 1 (by rfl) ⟨1551434, by rfl⟩ : syracuseStep 2068579 = 3102869) B3102869
theorem B8835925 : Blo 2067435 8835925 := bbase (se 9 (by rfl) ⟨25886, by rfl⟩ : syracuseStep 8835925 = 51773) (by norm_num)
theorem B11781233 : Blo 2067435 11781233 := bstep (se 2 (by rfl) ⟨4417962, by rfl⟩ : syracuseStep 11781233 = 8835925) B8835925
theorem B7854155 : Blo 2067435 7854155 := bstep (se 1 (by rfl) ⟨5890616, by rfl⟩ : syracuseStep 7854155 = 11781233) B11781233
theorem B5236103 : Blo 2067435 5236103 := bstep (se 1 (by rfl) ⟨3927077, by rfl⟩ : syracuseStep 5236103 = 7854155) B7854155
theorem B3490735 : Blo 2067435 3490735 := bstep (se 1 (by rfl) ⟨2618051, by rfl⟩ : syracuseStep 3490735 = 5236103) B5236103
theorem B4654313 : Blo 2067435 4654313 := bstep (se 2 (by rfl) ⟨1745367, by rfl⟩ : syracuseStep 4654313 = 3490735) B3490735
theorem B3102875 : Blo 2067435 3102875 := bstep (se 1 (by rfl) ⟨2327156, by rfl⟩ : syracuseStep 3102875 = 4654313) B4654313
theorem B2068583 : Blo 2067435 2068583 := bstep (se 1 (by rfl) ⟨1551437, by rfl⟩ : syracuseStep 2068583 = 3102875) B3102875
theorem B2327161 : Blo 2067435 2327161 := bbase (se 2 (by rfl) ⟨872685, by rfl⟩ : syracuseStep 2327161 = 1745371) (by norm_num)
theorem B3102881 : Blo 2067435 3102881 := bstep (se 2 (by rfl) ⟨1163580, by rfl⟩ : syracuseStep 3102881 = 2327161) B2327161
theorem B2068587 : Blo 2067435 2068587 := bstep (se 1 (by rfl) ⟨1551440, by rfl⟩ : syracuseStep 2068587 = 3102881) B3102881
theorem B5307565 : Blo 2067435 5307565 := bbase (se 3 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 5307565 = 1990337) (by norm_num)
theorem B7076753 : Blo 2067435 7076753 := bstep (se 2 (by rfl) ⟨2653782, by rfl⟩ : syracuseStep 7076753 = 5307565) B5307565
theorem B4717835 : Blo 2067435 4717835 := bstep (se 1 (by rfl) ⟨3538376, by rfl⟩ : syracuseStep 4717835 = 7076753) B7076753
theorem B3145223 : Blo 2067435 3145223 := bstep (se 1 (by rfl) ⟨2358917, by rfl⟩ : syracuseStep 3145223 = 4717835) B4717835
theorem B2096815 : Blo 2067435 2096815 := bstep (se 1 (by rfl) ⟨1572611, by rfl⟩ : syracuseStep 2096815 = 3145223) B3145223
theorem B2795753 : Blo 2067435 2795753 := bstep (se 2 (by rfl) ⟨1048407, by rfl⟩ : syracuseStep 2795753 = 2096815) B2096815
theorem B7455341 : Blo 2067435 7455341 := bstep (se 3 (by rfl) ⟨1397876, by rfl⟩ : syracuseStep 7455341 = 2795753) B2795753
theorem B19880909 : Blo 2067435 19880909 := bstep (se 3 (by rfl) ⟨3727670, by rfl⟩ : syracuseStep 19880909 = 7455341) B7455341
theorem B13253939 : Blo 2067435 13253939 := bstep (se 1 (by rfl) ⟨9940454, by rfl⟩ : syracuseStep 13253939 = 19880909) B19880909
theorem B8835959 : Blo 2067435 8835959 := bstep (se 1 (by rfl) ⟨6626969, by rfl⟩ : syracuseStep 8835959 = 13253939) B13253939
theorem B5890639 : Blo 2067435 5890639 := bstep (se 1 (by rfl) ⟨4417979, by rfl⟩ : syracuseStep 5890639 = 8835959) B8835959
theorem B7854185 : Blo 2067435 7854185 := bstep (se 2 (by rfl) ⟨2945319, by rfl⟩ : syracuseStep 7854185 = 5890639) B5890639
theorem B5236123 : Blo 2067435 5236123 := bstep (se 1 (by rfl) ⟨3927092, by rfl⟩ : syracuseStep 5236123 = 7854185) B7854185
theorem B6981497 : Blo 2067435 6981497 := bstep (se 2 (by rfl) ⟨2618061, by rfl⟩ : syracuseStep 6981497 = 5236123) B5236123
theorem B4654331 : Blo 2067435 4654331 := bstep (se 1 (by rfl) ⟨3490748, by rfl⟩ : syracuseStep 4654331 = 6981497) B6981497
theorem B3102887 : Blo 2067435 3102887 := bstep (se 1 (by rfl) ⟨2327165, by rfl⟩ : syracuseStep 3102887 = 4654331) B4654331
theorem B2068591 : Blo 2067435 2068591 := bstep (se 1 (by rfl) ⟨1551443, by rfl⟩ : syracuseStep 2068591 = 3102887) B3102887
theorem B3102893 : Blo 2067435 3102893 := bbase (se 3 (by rfl) ⟨581792, by rfl⟩ : syracuseStep 3102893 = 1163585) (by norm_num)
theorem B2068595 : Blo 2067435 2068595 := bstep (se 1 (by rfl) ⟨1551446, by rfl⟩ : syracuseStep 2068595 = 3102893) B3102893
theorem B4654349 : Blo 2067435 4654349 := bbase (se 3 (by rfl) ⟨872690, by rfl⟩ : syracuseStep 4654349 = 1745381) (by norm_num)
theorem B3102899 : Blo 2067435 3102899 := bstep (se 1 (by rfl) ⟨2327174, by rfl⟩ : syracuseStep 3102899 = 4654349) B4654349
theorem B2068599 : Blo 2067435 2068599 := bstep (se 1 (by rfl) ⟨1551449, by rfl⟩ : syracuseStep 2068599 = 3102899) B3102899
theorem B2618077 : Blo 2067435 2618077 := bbase (se 3 (by rfl) ⟨490889, by rfl⟩ : syracuseStep 2618077 = 981779) (by norm_num)
theorem B3490769 : Blo 2067435 3490769 := bstep (se 2 (by rfl) ⟨1309038, by rfl⟩ : syracuseStep 3490769 = 2618077) B2618077
theorem B2327179 : Blo 2067435 2327179 := bstep (se 1 (by rfl) ⟨1745384, by rfl⟩ : syracuseStep 2327179 = 3490769) B3490769
theorem B3102905 : Blo 2067435 3102905 := bstep (se 2 (by rfl) ⟨1163589, by rfl⟩ : syracuseStep 3102905 = 2327179) B2327179
theorem B2068603 : Blo 2067435 2068603 := bstep (se 1 (by rfl) ⟨1551452, by rfl⟩ : syracuseStep 2068603 = 3102905) B3102905
theorem B17672053 : Blo 2067435 17672053 := bbase (se 5 (by rfl) ⟨828377, by rfl⟩ : syracuseStep 17672053 = 1656755) (by norm_num)
theorem B23562737 : Blo 2067435 23562737 := bstep (se 2 (by rfl) ⟨8836026, by rfl⟩ : syracuseStep 23562737 = 17672053) B17672053
theorem B15708491 : Blo 2067435 15708491 := bstep (se 1 (by rfl) ⟨11781368, by rfl⟩ : syracuseStep 15708491 = 23562737) B23562737
theorem B10472327 : Blo 2067435 10472327 := bstep (se 1 (by rfl) ⟨7854245, by rfl⟩ : syracuseStep 10472327 = 15708491) B15708491
theorem B6981551 : Blo 2067435 6981551 := bstep (se 1 (by rfl) ⟨5236163, by rfl⟩ : syracuseStep 6981551 = 10472327) B10472327
theorem B4654367 : Blo 2067435 4654367 := bstep (se 1 (by rfl) ⟨3490775, by rfl⟩ : syracuseStep 4654367 = 6981551) B6981551
theorem B3102911 : Blo 2067435 3102911 := bstep (se 1 (by rfl) ⟨2327183, by rfl⟩ : syracuseStep 3102911 = 4654367) B4654367
theorem B2068607 : Blo 2067435 2068607 := bstep (se 1 (by rfl) ⟨1551455, by rfl⟩ : syracuseStep 2068607 = 3102911) B3102911
theorem B3102917 : Blo 2067435 3102917 := bbase (se 4 (by rfl) ⟨290898, by rfl⟩ : syracuseStep 3102917 = 581797) (by norm_num)
theorem B2068611 : Blo 2067435 2068611 := bstep (se 1 (by rfl) ⟨1551458, by rfl⟩ : syracuseStep 2068611 = 3102917) B3102917
theorem B3490789 : Blo 2067435 3490789 := bbase (se 4 (by rfl) ⟨327261, by rfl⟩ : syracuseStep 3490789 = 654523) (by norm_num)
theorem B4654385 : Blo 2067435 4654385 := bstep (se 2 (by rfl) ⟨1745394, by rfl⟩ : syracuseStep 4654385 = 3490789) B3490789
theorem B3102923 : Blo 2067435 3102923 := bstep (se 1 (by rfl) ⟨2327192, by rfl⟩ : syracuseStep 3102923 = 4654385) B4654385
theorem B2068615 : Blo 2067435 2068615 := bstep (se 1 (by rfl) ⟨1551461, by rfl⟩ : syracuseStep 2068615 = 3102923) B3102923
theorem B2327197 : Blo 2067435 2327197 := bbase (se 3 (by rfl) ⟨436349, by rfl⟩ : syracuseStep 2327197 = 872699) (by norm_num)
theorem B3102929 : Blo 2067435 3102929 := bstep (se 2 (by rfl) ⟨1163598, by rfl⟩ : syracuseStep 3102929 = 2327197) B2327197
theorem B2068619 : Blo 2067435 2068619 := bstep (se 1 (by rfl) ⟨1551464, by rfl⟩ : syracuseStep 2068619 = 3102929) B3102929
theorem B6981605 : Blo 2067435 6981605 := bbase (se 4 (by rfl) ⟨654525, by rfl⟩ : syracuseStep 6981605 = 1309051) (by norm_num)
theorem B4654403 : Blo 2067435 4654403 := bstep (se 1 (by rfl) ⟨3490802, by rfl⟩ : syracuseStep 4654403 = 6981605) B6981605
theorem B3102935 : Blo 2067435 3102935 := bstep (se 1 (by rfl) ⟨2327201, by rfl⟩ : syracuseStep 3102935 = 4654403) B4654403
theorem B2068623 : Blo 2067435 2068623 := bstep (se 1 (by rfl) ⟨1551467, by rfl⟩ : syracuseStep 2068623 = 3102935) B3102935
theorem B3102941 : Blo 2067435 3102941 := bbase (se 3 (by rfl) ⟨581801, by rfl⟩ : syracuseStep 3102941 = 1163603) (by norm_num)
theorem B2068627 : Blo 2067435 2068627 := bstep (se 1 (by rfl) ⟨1551470, by rfl⟩ : syracuseStep 2068627 = 3102941) B3102941
theorem B4654421 : Blo 2067435 4654421 := bbase (se 12 (by rfl) ⟨1704, by rfl⟩ : syracuseStep 4654421 = 3409) (by norm_num)
theorem B3102947 : Blo 2067435 3102947 := bstep (se 1 (by rfl) ⟨2327210, by rfl⟩ : syracuseStep 3102947 = 4654421) B4654421
theorem B2068631 : Blo 2067435 2068631 := bstep (se 1 (by rfl) ⟨1551473, by rfl⟩ : syracuseStep 2068631 = 3102947) B3102947
theorem B2209037 : Blo 2067435 2209037 := bbase (se 3 (by rfl) ⟨414194, by rfl⟩ : syracuseStep 2209037 = 828389) (by norm_num)
theorem B5890765 : Blo 2067435 5890765 := bstep (se 3 (by rfl) ⟨1104518, by rfl⟩ : syracuseStep 5890765 = 2209037) B2209037
theorem B7854353 : Blo 2067435 7854353 := bstep (se 2 (by rfl) ⟨2945382, by rfl⟩ : syracuseStep 7854353 = 5890765) B5890765
theorem B5236235 : Blo 2067435 5236235 := bstep (se 1 (by rfl) ⟨3927176, by rfl⟩ : syracuseStep 5236235 = 7854353) B7854353
theorem B3490823 : Blo 2067435 3490823 := bstep (se 1 (by rfl) ⟨2618117, by rfl⟩ : syracuseStep 3490823 = 5236235) B5236235
theorem B2327215 : Blo 2067435 2327215 := bstep (se 1 (by rfl) ⟨1745411, by rfl⟩ : syracuseStep 2327215 = 3490823) B3490823
theorem B3102953 : Blo 2067435 3102953 := bstep (se 2 (by rfl) ⟨1163607, by rfl⟩ : syracuseStep 3102953 = 2327215) B2327215
theorem B2068635 : Blo 2067435 2068635 := bstep (se 1 (by rfl) ⟨1551476, by rfl⟩ : syracuseStep 2068635 = 3102953) B3102953
theorem B3980765 : Blo 2067435 3980765 := bbase (se 3 (by rfl) ⟨746393, by rfl⟩ : syracuseStep 3980765 = 1492787) (by norm_num)
theorem B10615373 : Blo 2067435 10615373 := bstep (se 3 (by rfl) ⟨1990382, by rfl⟩ : syracuseStep 10615373 = 3980765) B3980765
theorem B7076915 : Blo 2067435 7076915 := bstep (se 1 (by rfl) ⟨5307686, by rfl⟩ : syracuseStep 7076915 = 10615373) B10615373
theorem B4717943 : Blo 2067435 4717943 := bstep (se 1 (by rfl) ⟨3538457, by rfl⟩ : syracuseStep 4717943 = 7076915) B7076915
theorem B3145295 : Blo 2067435 3145295 := bstep (se 1 (by rfl) ⟨2358971, by rfl⟩ : syracuseStep 3145295 = 4717943) B4717943
theorem B8387453 : Blo 2067435 8387453 := bstep (se 3 (by rfl) ⟨1572647, by rfl⟩ : syracuseStep 8387453 = 3145295) B3145295
theorem B5591635 : Blo 2067435 5591635 := bstep (se 1 (by rfl) ⟨4193726, by rfl⟩ : syracuseStep 5591635 = 8387453) B8387453
theorem B29822053 : Blo 2067435 29822053 := bstep (se 4 (by rfl) ⟨2795817, by rfl⟩ : syracuseStep 29822053 = 5591635) B5591635
theorem B39762737 : Blo 2067435 39762737 := bstep (se 2 (by rfl) ⟨14911026, by rfl⟩ : syracuseStep 39762737 = 29822053) B29822053
theorem B26508491 : Blo 2067435 26508491 := bstep (se 1 (by rfl) ⟨19881368, by rfl⟩ : syracuseStep 26508491 = 39762737) B39762737
theorem B17672327 : Blo 2067435 17672327 := bstep (se 1 (by rfl) ⟨13254245, by rfl⟩ : syracuseStep 17672327 = 26508491) B26508491
theorem B11781551 : Blo 2067435 11781551 := bstep (se 1 (by rfl) ⟨8836163, by rfl⟩ : syracuseStep 11781551 = 17672327) B17672327
theorem B7854367 : Blo 2067435 7854367 := bstep (se 1 (by rfl) ⟨5890775, by rfl⟩ : syracuseStep 7854367 = 11781551) B11781551
theorem B10472489 : Blo 2067435 10472489 := bstep (se 2 (by rfl) ⟨3927183, by rfl⟩ : syracuseStep 10472489 = 7854367) B7854367
theorem B6981659 : Blo 2067435 6981659 := bstep (se 1 (by rfl) ⟨5236244, by rfl⟩ : syracuseStep 6981659 = 10472489) B10472489
theorem B4654439 : Blo 2067435 4654439 := bstep (se 1 (by rfl) ⟨3490829, by rfl⟩ : syracuseStep 4654439 = 6981659) B6981659
theorem B3102959 : Blo 2067435 3102959 := bstep (se 1 (by rfl) ⟨2327219, by rfl⟩ : syracuseStep 3102959 = 4654439) B4654439
theorem B2068639 : Blo 2067435 2068639 := bstep (se 1 (by rfl) ⟨1551479, by rfl⟩ : syracuseStep 2068639 = 3102959) B3102959
theorem B3102965 : Blo 2067435 3102965 := bbase (se 5 (by rfl) ⟨145451, by rfl⟩ : syracuseStep 3102965 = 290903) (by norm_num)
theorem B2068643 : Blo 2067435 2068643 := bstep (se 1 (by rfl) ⟨1551482, by rfl⟩ : syracuseStep 2068643 = 3102965) B3102965
theorem B42461653 : Blo 2067435 42461653 := bbase (se 7 (by rfl) ⟨497597, by rfl⟩ : syracuseStep 42461653 = 995195) (by norm_num)
theorem B56615537 : Blo 2067435 56615537 := bstep (se 2 (by rfl) ⟨21230826, by rfl⟩ : syracuseStep 56615537 = 42461653) B42461653
theorem B37743691 : Blo 2067435 37743691 := bstep (se 1 (by rfl) ⟨28307768, by rfl⟩ : syracuseStep 37743691 = 56615537) B56615537
theorem B50324921 : Blo 2067435 50324921 := bstep (se 2 (by rfl) ⟨18871845, by rfl⟩ : syracuseStep 50324921 = 37743691) B37743691
theorem B33549947 : Blo 2067435 33549947 := bstep (se 1 (by rfl) ⟨25162460, by rfl⟩ : syracuseStep 33549947 = 50324921) B50324921
theorem B22366631 : Blo 2067435 22366631 := bstep (se 1 (by rfl) ⟨16774973, by rfl⟩ : syracuseStep 22366631 = 33549947) B33549947
theorem B14911087 : Blo 2067435 14911087 := bstep (se 1 (by rfl) ⟨11183315, by rfl⟩ : syracuseStep 14911087 = 22366631) B22366631
theorem B19881449 : Blo 2067435 19881449 := bstep (se 2 (by rfl) ⟨7455543, by rfl⟩ : syracuseStep 19881449 = 14911087) B14911087
theorem B13254299 : Blo 2067435 13254299 := bstep (se 1 (by rfl) ⟨9940724, by rfl⟩ : syracuseStep 13254299 = 19881449) B19881449
theorem B8836199 : Blo 2067435 8836199 := bstep (se 1 (by rfl) ⟨6627149, by rfl⟩ : syracuseStep 8836199 = 13254299) B13254299
theorem B5890799 : Blo 2067435 5890799 := bstep (se 1 (by rfl) ⟨4418099, by rfl⟩ : syracuseStep 5890799 = 8836199) B8836199
theorem B3927199 : Blo 2067435 3927199 := bstep (se 1 (by rfl) ⟨2945399, by rfl⟩ : syracuseStep 3927199 = 5890799) B5890799
theorem B5236265 : Blo 2067435 5236265 := bstep (se 2 (by rfl) ⟨1963599, by rfl⟩ : syracuseStep 5236265 = 3927199) B3927199
theorem B3490843 : Blo 2067435 3490843 := bstep (se 1 (by rfl) ⟨2618132, by rfl⟩ : syracuseStep 3490843 = 5236265) B5236265
theorem B4654457 : Blo 2067435 4654457 := bstep (se 2 (by rfl) ⟨1745421, by rfl⟩ : syracuseStep 4654457 = 3490843) B3490843
theorem B3102971 : Blo 2067435 3102971 := bstep (se 1 (by rfl) ⟨2327228, by rfl⟩ : syracuseStep 3102971 = 4654457) B4654457
theorem B2068647 : Blo 2067435 2068647 := bstep (se 1 (by rfl) ⟨1551485, by rfl⟩ : syracuseStep 2068647 = 3102971) B3102971
theorem B2327233 : Blo 2067435 2327233 := bbase (se 2 (by rfl) ⟨872712, by rfl⟩ : syracuseStep 2327233 = 1745425) (by norm_num)
theorem B3102977 : Blo 2067435 3102977 := bstep (se 2 (by rfl) ⟨1163616, by rfl⟩ : syracuseStep 3102977 = 2327233) B2327233
theorem B2068651 : Blo 2067435 2068651 := bstep (se 1 (by rfl) ⟨1551488, by rfl⟩ : syracuseStep 2068651 = 3102977) B3102977
theorem B5236285 : Blo 2067435 5236285 := bbase (se 3 (by rfl) ⟨981803, by rfl⟩ : syracuseStep 5236285 = 1963607) (by norm_num)
theorem B6981713 : Blo 2067435 6981713 := bstep (se 2 (by rfl) ⟨2618142, by rfl⟩ : syracuseStep 6981713 = 5236285) B5236285
theorem B4654475 : Blo 2067435 4654475 := bstep (se 1 (by rfl) ⟨3490856, by rfl⟩ : syracuseStep 4654475 = 6981713) B6981713
theorem B3102983 : Blo 2067435 3102983 := bstep (se 1 (by rfl) ⟨2327237, by rfl⟩ : syracuseStep 3102983 = 4654475) B4654475
theorem B2068655 : Blo 2067435 2068655 := bstep (se 1 (by rfl) ⟨1551491, by rfl⟩ : syracuseStep 2068655 = 3102983) B3102983
theorem B3102989 : Blo 2067435 3102989 := bbase (se 3 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 3102989 = 1163621) (by norm_num)
theorem B2068659 : Blo 2067435 2068659 := bstep (se 1 (by rfl) ⟨1551494, by rfl⟩ : syracuseStep 2068659 = 3102989) B3102989
theorem B4654493 : Blo 2067435 4654493 := bbase (se 3 (by rfl) ⟨872717, by rfl⟩ : syracuseStep 4654493 = 1745435) (by norm_num)
theorem B3102995 : Blo 2067435 3102995 := bstep (se 1 (by rfl) ⟨2327246, by rfl⟩ : syracuseStep 3102995 = 4654493) B4654493
theorem B2068663 : Blo 2067435 2068663 := bstep (se 1 (by rfl) ⟨1551497, by rfl⟩ : syracuseStep 2068663 = 3102995) B3102995
theorem B3490877 : Blo 2067435 3490877 := bbase (se 3 (by rfl) ⟨654539, by rfl⟩ : syracuseStep 3490877 = 1309079) (by norm_num)
theorem B2327251 : Blo 2067435 2327251 := bstep (se 1 (by rfl) ⟨1745438, by rfl⟩ : syracuseStep 2327251 = 3490877) B3490877
theorem B3103001 : Blo 2067435 3103001 := bstep (se 2 (by rfl) ⟨1163625, by rfl⟩ : syracuseStep 3103001 = 2327251) B2327251
theorem B2068667 : Blo 2067435 2068667 := bstep (se 1 (by rfl) ⟨1551500, by rfl⟩ : syracuseStep 2068667 = 3103001) B3103001
theorem B3313613 : Blo 2067435 3313613 := bbase (se 3 (by rfl) ⟨621302, by rfl⟩ : syracuseStep 3313613 = 1242605) (by norm_num)
theorem B2209075 : Blo 2067435 2209075 := bstep (se 1 (by rfl) ⟨1656806, by rfl⟩ : syracuseStep 2209075 = 3313613) B3313613
theorem B11781733 : Blo 2067435 11781733 := bstep (se 4 (by rfl) ⟨1104537, by rfl⟩ : syracuseStep 11781733 = 2209075) B2209075
theorem B15708977 : Blo 2067435 15708977 := bstep (se 2 (by rfl) ⟨5890866, by rfl⟩ : syracuseStep 15708977 = 11781733) B11781733
theorem B10472651 : Blo 2067435 10472651 := bstep (se 1 (by rfl) ⟨7854488, by rfl⟩ : syracuseStep 10472651 = 15708977) B15708977
theorem B6981767 : Blo 2067435 6981767 := bstep (se 1 (by rfl) ⟨5236325, by rfl⟩ : syracuseStep 6981767 = 10472651) B10472651
theorem B4654511 : Blo 2067435 4654511 := bstep (se 1 (by rfl) ⟨3490883, by rfl⟩ : syracuseStep 4654511 = 6981767) B6981767
theorem B3103007 : Blo 2067435 3103007 := bstep (se 1 (by rfl) ⟨2327255, by rfl⟩ : syracuseStep 3103007 = 4654511) B4654511
theorem B2068671 : Blo 2067435 2068671 := bstep (se 1 (by rfl) ⟨1551503, by rfl⟩ : syracuseStep 2068671 = 3103007) B3103007
theorem B3103013 : Blo 2067435 3103013 := bbase (se 4 (by rfl) ⟨290907, by rfl⟩ : syracuseStep 3103013 = 581815) (by norm_num)
theorem B2068675 : Blo 2067435 2068675 := bstep (se 1 (by rfl) ⟨1551506, by rfl⟩ : syracuseStep 2068675 = 3103013) B3103013
theorem B2618173 : Blo 2067435 2618173 := bbase (se 3 (by rfl) ⟨490907, by rfl⟩ : syracuseStep 2618173 = 981815) (by norm_num)
theorem B3490897 : Blo 2067435 3490897 := bstep (se 2 (by rfl) ⟨1309086, by rfl⟩ : syracuseStep 3490897 = 2618173) B2618173
theorem B4654529 : Blo 2067435 4654529 := bstep (se 2 (by rfl) ⟨1745448, by rfl⟩ : syracuseStep 4654529 = 3490897) B3490897
theorem B3103019 : Blo 2067435 3103019 := bstep (se 1 (by rfl) ⟨2327264, by rfl⟩ : syracuseStep 3103019 = 4654529) B4654529
theorem B2068679 : Blo 2067435 2068679 := bstep (se 1 (by rfl) ⟨1551509, by rfl⟩ : syracuseStep 2068679 = 3103019) B3103019
theorem B2327269 : Blo 2067435 2327269 := bbase (se 4 (by rfl) ⟨218181, by rfl⟩ : syracuseStep 2327269 = 436363) (by norm_num)
theorem B3103025 : Blo 2067435 3103025 := bstep (se 2 (by rfl) ⟨1163634, by rfl⟩ : syracuseStep 3103025 = 2327269) B2327269
theorem B2068683 : Blo 2067435 2068683 := bstep (se 1 (by rfl) ⟨1551512, by rfl⟩ : syracuseStep 2068683 = 3103025) B3103025
theorem B3538541 : Blo 2067435 3538541 := bbase (se 3 (by rfl) ⟨663476, by rfl⟩ : syracuseStep 3538541 = 1326953) (by norm_num)
theorem B2359027 : Blo 2067435 2359027 := bstep (se 1 (by rfl) ⟨1769270, by rfl⟩ : syracuseStep 2359027 = 3538541) B3538541
theorem B12581477 : Blo 2067435 12581477 := bstep (se 4 (by rfl) ⟨1179513, by rfl⟩ : syracuseStep 12581477 = 2359027) B2359027
theorem B8387651 : Blo 2067435 8387651 := bstep (se 1 (by rfl) ⟨6290738, by rfl⟩ : syracuseStep 8387651 = 12581477) B12581477
theorem B5591767 : Blo 2067435 5591767 := bstep (se 1 (by rfl) ⟨4193825, by rfl⟩ : syracuseStep 5591767 = 8387651) B8387651
theorem B7455689 : Blo 2067435 7455689 := bstep (se 2 (by rfl) ⟨2795883, by rfl⟩ : syracuseStep 7455689 = 5591767) B5591767
theorem B4970459 : Blo 2067435 4970459 := bstep (se 1 (by rfl) ⟨3727844, by rfl⟩ : syracuseStep 4970459 = 7455689) B7455689
theorem B3313639 : Blo 2067435 3313639 := bstep (se 1 (by rfl) ⟨2485229, by rfl⟩ : syracuseStep 3313639 = 4970459) B4970459
theorem B4418185 : Blo 2067435 4418185 := bstep (se 2 (by rfl) ⟨1656819, by rfl⟩ : syracuseStep 4418185 = 3313639) B3313639
theorem B5890913 : Blo 2067435 5890913 := bstep (se 2 (by rfl) ⟨2209092, by rfl⟩ : syracuseStep 5890913 = 4418185) B4418185
theorem B3927275 : Blo 2067435 3927275 := bstep (se 1 (by rfl) ⟨2945456, by rfl⟩ : syracuseStep 3927275 = 5890913) B5890913
theorem B2618183 : Blo 2067435 2618183 := bstep (se 1 (by rfl) ⟨1963637, by rfl⟩ : syracuseStep 2618183 = 3927275) B3927275
theorem B6981821 : Blo 2067435 6981821 := bstep (se 3 (by rfl) ⟨1309091, by rfl⟩ : syracuseStep 6981821 = 2618183) B2618183
theorem B4654547 : Blo 2067435 4654547 := bstep (se 1 (by rfl) ⟨3490910, by rfl⟩ : syracuseStep 4654547 = 6981821) B6981821
theorem B3103031 : Blo 2067435 3103031 := bstep (se 1 (by rfl) ⟨2327273, by rfl⟩ : syracuseStep 3103031 = 4654547) B4654547
theorem B2068687 : Blo 2067435 2068687 := bstep (se 1 (by rfl) ⟨1551515, by rfl⟩ : syracuseStep 2068687 = 3103031) B3103031
theorem B3103037 : Blo 2067435 3103037 := bbase (se 3 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 3103037 = 1163639) (by norm_num)
theorem B2068691 : Blo 2067435 2068691 := bstep (se 1 (by rfl) ⟨1551518, by rfl⟩ : syracuseStep 2068691 = 3103037) B3103037
theorem B4654565 : Blo 2067435 4654565 := bbase (se 4 (by rfl) ⟨436365, by rfl⟩ : syracuseStep 4654565 = 872731) (by norm_num)
theorem B3103043 : Blo 2067435 3103043 := bstep (se 1 (by rfl) ⟨2327282, by rfl⟩ : syracuseStep 3103043 = 4654565) B4654565
theorem B2068695 : Blo 2067435 2068695 := bstep (se 1 (by rfl) ⟨1551521, by rfl⟩ : syracuseStep 2068695 = 3103043) B3103043
theorem B5236397 : Blo 2067435 5236397 := bbase (se 3 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 5236397 = 1963649) (by norm_num)
theorem B3490931 : Blo 2067435 3490931 := bstep (se 1 (by rfl) ⟨2618198, by rfl⟩ : syracuseStep 3490931 = 5236397) B5236397
theorem B2327287 : Blo 2067435 2327287 := bstep (se 1 (by rfl) ⟨1745465, by rfl⟩ : syracuseStep 2327287 = 3490931) B3490931
theorem B3103049 : Blo 2067435 3103049 := bstep (se 2 (by rfl) ⟨1163643, by rfl⟩ : syracuseStep 3103049 = 2327287) B2327287
theorem B2068699 : Blo 2067435 2068699 := bstep (se 1 (by rfl) ⟨1551524, by rfl⟩ : syracuseStep 2068699 = 3103049) B3103049
theorem B2096929 : Blo 2067435 2096929 := bbase (se 2 (by rfl) ⟨786348, by rfl⟩ : syracuseStep 2096929 = 1572697) (by norm_num)
theorem B2795905 : Blo 2067435 2795905 := bstep (se 2 (by rfl) ⟨1048464, by rfl⟩ : syracuseStep 2795905 = 2096929) B2096929
theorem B3727873 : Blo 2067435 3727873 := bstep (se 2 (by rfl) ⟨1397952, by rfl⟩ : syracuseStep 3727873 = 2795905) B2795905
theorem B4970497 : Blo 2067435 4970497 := bstep (se 2 (by rfl) ⟨1863936, by rfl⟩ : syracuseStep 4970497 = 3727873) B3727873
theorem B6627329 : Blo 2067435 6627329 := bstep (se 2 (by rfl) ⟨2485248, by rfl⟩ : syracuseStep 6627329 = 4970497) B4970497
theorem B4418219 : Blo 2067435 4418219 := bstep (se 1 (by rfl) ⟨3313664, by rfl⟩ : syracuseStep 4418219 = 6627329) B6627329
theorem B2945479 : Blo 2067435 2945479 := bstep (se 1 (by rfl) ⟨2209109, by rfl⟩ : syracuseStep 2945479 = 4418219) B4418219
theorem B3927305 : Blo 2067435 3927305 := bstep (se 2 (by rfl) ⟨1472739, by rfl⟩ : syracuseStep 3927305 = 2945479) B2945479
theorem B10472813 : Blo 2067435 10472813 := bstep (se 3 (by rfl) ⟨1963652, by rfl⟩ : syracuseStep 10472813 = 3927305) B3927305
theorem B6981875 : Blo 2067435 6981875 := bstep (se 1 (by rfl) ⟨5236406, by rfl⟩ : syracuseStep 6981875 = 10472813) B10472813
theorem B4654583 : Blo 2067435 4654583 := bstep (se 1 (by rfl) ⟨3490937, by rfl⟩ : syracuseStep 4654583 = 6981875) B6981875
theorem B3103055 : Blo 2067435 3103055 := bstep (se 1 (by rfl) ⟨2327291, by rfl⟩ : syracuseStep 3103055 = 4654583) B4654583
theorem B2068703 : Blo 2067435 2068703 := bstep (se 1 (by rfl) ⟨1551527, by rfl⟩ : syracuseStep 2068703 = 3103055) B3103055
theorem B3103061 : Blo 2067435 3103061 := bbase (se 10 (by rfl) ⟨4545, by rfl⟩ : syracuseStep 3103061 = 9091) (by norm_num)
theorem B2068707 : Blo 2067435 2068707 := bstep (se 1 (by rfl) ⟨1551530, by rfl⟩ : syracuseStep 2068707 = 3103061) B3103061
theorem B5890981 : Blo 2067435 5890981 := bbase (se 4 (by rfl) ⟨552279, by rfl⟩ : syracuseStep 5890981 = 1104559) (by norm_num)
theorem B7854641 : Blo 2067435 7854641 := bstep (se 2 (by rfl) ⟨2945490, by rfl⟩ : syracuseStep 7854641 = 5890981) B5890981
theorem B5236427 : Blo 2067435 5236427 := bstep (se 1 (by rfl) ⟨3927320, by rfl⟩ : syracuseStep 5236427 = 7854641) B7854641
theorem B3490951 : Blo 2067435 3490951 := bstep (se 1 (by rfl) ⟨2618213, by rfl⟩ : syracuseStep 3490951 = 5236427) B5236427
theorem B4654601 : Blo 2067435 4654601 := bstep (se 2 (by rfl) ⟨1745475, by rfl⟩ : syracuseStep 4654601 = 3490951) B3490951
theorem B3103067 : Blo 2067435 3103067 := bstep (se 1 (by rfl) ⟨2327300, by rfl⟩ : syracuseStep 3103067 = 4654601) B4654601
theorem B2068711 : Blo 2067435 2068711 := bstep (se 1 (by rfl) ⟨1551533, by rfl⟩ : syracuseStep 2068711 = 3103067) B3103067
theorem B2327305 : Blo 2067435 2327305 := bbase (se 2 (by rfl) ⟨872739, by rfl⟩ : syracuseStep 2327305 = 1745479) (by norm_num)
theorem B3103073 : Blo 2067435 3103073 := bstep (se 2 (by rfl) ⟨1163652, by rfl⟩ : syracuseStep 3103073 = 2327305) B2327305
theorem B2068715 : Blo 2067435 2068715 := bstep (se 1 (by rfl) ⟨1551536, by rfl⟩ : syracuseStep 2068715 = 3103073) B3103073
theorem B3727901 : Blo 2067435 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B9941069 : Blo 2067435 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B26509517 : Blo 2067435 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B17673011 : Blo 2067435 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B11782007 : Blo 2067435 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B7854671 : Blo 2067435 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B5236447 : Blo 2067435 5236447 := bstep (se 1 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 5236447 = 7854671) B7854671
theorem B6981929 : Blo 2067435 6981929 := bstep (se 2 (by rfl) ⟨2618223, by rfl⟩ : syracuseStep 6981929 = 5236447) B5236447
theorem B4654619 : Blo 2067435 4654619 := bstep (se 1 (by rfl) ⟨3490964, by rfl⟩ : syracuseStep 4654619 = 6981929) B6981929
theorem B3103079 : Blo 2067435 3103079 := bstep (se 1 (by rfl) ⟨2327309, by rfl⟩ : syracuseStep 3103079 = 4654619) B4654619
theorem B2068719 : Blo 2067435 2068719 := bstep (se 1 (by rfl) ⟨1551539, by rfl⟩ : syracuseStep 2068719 = 3103079) B3103079
theorem B3103085 : Blo 2067435 3103085 := bbase (se 3 (by rfl) ⟨581828, by rfl⟩ : syracuseStep 3103085 = 1163657) (by norm_num)
theorem B2068723 : Blo 2067435 2068723 := bstep (se 1 (by rfl) ⟨1551542, by rfl⟩ : syracuseStep 2068723 = 3103085) B3103085
theorem B4654637 : Blo 2067435 4654637 := bbase (se 3 (by rfl) ⟨872744, by rfl⟩ : syracuseStep 4654637 = 1745489) (by norm_num)
theorem B3103091 : Blo 2067435 3103091 := bstep (se 1 (by rfl) ⟨2327318, by rfl⟩ : syracuseStep 3103091 = 4654637) B4654637
theorem B2068727 : Blo 2067435 2068727 := bstep (se 1 (by rfl) ⟨1551545, by rfl⟩ : syracuseStep 2068727 = 3103091) B3103091
theorem B2588401 : Blo 2067435 2588401 := bbase (se 2 (by rfl) ⟨970650, by rfl⟩ : syracuseStep 2588401 = 1941301) (by norm_num)
theorem B13804805 : Blo 2067435 13804805 := bstep (se 4 (by rfl) ⟨1294200, by rfl⟩ : syracuseStep 13804805 = 2588401) B2588401
theorem B9203203 : Blo 2067435 9203203 := bstep (se 1 (by rfl) ⟨6902402, by rfl⟩ : syracuseStep 9203203 = 13804805) B13804805
theorem B12270937 : Blo 2067435 12270937 := bstep (se 2 (by rfl) ⟨4601601, by rfl⟩ : syracuseStep 12270937 = 9203203) B9203203
theorem B16361249 : Blo 2067435 16361249 := bstep (se 2 (by rfl) ⟨6135468, by rfl⟩ : syracuseStep 16361249 = 12270937) B12270937
theorem B43629997 : Blo 2067435 43629997 := bstep (se 3 (by rfl) ⟨8180624, by rfl⟩ : syracuseStep 43629997 = 16361249) B16361249
theorem B58173329 : Blo 2067435 58173329 := bstep (se 2 (by rfl) ⟨21814998, by rfl⟩ : syracuseStep 58173329 = 43629997) B43629997
theorem B155128877 : Blo 2067435 155128877 := bstep (se 3 (by rfl) ⟨29086664, by rfl⟩ : syracuseStep 155128877 = 58173329) B58173329
theorem B103419251 : Blo 2067435 103419251 := bstep (se 1 (by rfl) ⟨77564438, by rfl⟩ : syracuseStep 103419251 = 155128877) B155128877
theorem B68946167 : Blo 2067435 68946167 := bstep (se 1 (by rfl) ⟨51709625, by rfl⟩ : syracuseStep 68946167 = 103419251) B103419251
theorem B45964111 : Blo 2067435 45964111 := bstep (se 1 (by rfl) ⟨34473083, by rfl⟩ : syracuseStep 45964111 = 68946167) B68946167
theorem B61285481 : Blo 2067435 61285481 := bstep (se 2 (by rfl) ⟨22982055, by rfl⟩ : syracuseStep 61285481 = 45964111) B45964111
theorem B40856987 : Blo 2067435 40856987 := bstep (se 1 (by rfl) ⟨30642740, by rfl⟩ : syracuseStep 40856987 = 61285481) B61285481
theorem B27237991 : Blo 2067435 27237991 := bstep (se 1 (by rfl) ⟨20428493, by rfl⟩ : syracuseStep 27237991 = 40856987) B40856987
theorem B36317321 : Blo 2067435 36317321 := bstep (se 2 (by rfl) ⟨13618995, by rfl⟩ : syracuseStep 36317321 = 27237991) B27237991
theorem B24211547 : Blo 2067435 24211547 := bstep (se 1 (by rfl) ⟨18158660, by rfl⟩ : syracuseStep 24211547 = 36317321) B36317321
theorem B16141031 : Blo 2067435 16141031 := bstep (se 1 (by rfl) ⟨12105773, by rfl⟩ : syracuseStep 16141031 = 24211547) B24211547
theorem B10760687 : Blo 2067435 10760687 := bstep (se 1 (by rfl) ⟨8070515, by rfl⟩ : syracuseStep 10760687 = 16141031) B16141031
theorem B7173791 : Blo 2067435 7173791 := bstep (se 1 (by rfl) ⟨5380343, by rfl⟩ : syracuseStep 7173791 = 10760687) B10760687
theorem B4782527 : Blo 2067435 4782527 := bstep (se 1 (by rfl) ⟨3586895, by rfl⟩ : syracuseStep 4782527 = 7173791) B7173791
theorem B3188351 : Blo 2067435 3188351 := bstep (se 1 (by rfl) ⟨2391263, by rfl⟩ : syracuseStep 3188351 = 4782527) B4782527
theorem B2125567 : Blo 2067435 2125567 := bstep (se 1 (by rfl) ⟨1594175, by rfl⟩ : syracuseStep 2125567 = 3188351) B3188351
theorem B11336357 : Blo 2067435 11336357 := bstep (se 4 (by rfl) ⟨1062783, by rfl⟩ : syracuseStep 11336357 = 2125567) B2125567
theorem B7557571 : Blo 2067435 7557571 := bstep (se 1 (by rfl) ⟨5668178, by rfl⟩ : syracuseStep 7557571 = 11336357) B11336357
theorem B10076761 : Blo 2067435 10076761 := bstep (se 2 (by rfl) ⟨3778785, by rfl⟩ : syracuseStep 10076761 = 7557571) B7557571
theorem B13435681 : Blo 2067435 13435681 := bstep (se 2 (by rfl) ⟨5038380, by rfl⟩ : syracuseStep 13435681 = 10076761) B10076761
theorem B17914241 : Blo 2067435 17914241 := bstep (se 2 (by rfl) ⟨6717840, by rfl⟩ : syracuseStep 17914241 = 13435681) B13435681
theorem B47771309 : Blo 2067435 47771309 := bstep (se 3 (by rfl) ⟨8957120, by rfl⟩ : syracuseStep 47771309 = 17914241) B17914241
theorem B31847539 : Blo 2067435 31847539 := bstep (se 1 (by rfl) ⟨23885654, by rfl⟩ : syracuseStep 31847539 = 47771309) B47771309
theorem B42463385 : Blo 2067435 42463385 := bstep (se 2 (by rfl) ⟨15923769, by rfl⟩ : syracuseStep 42463385 = 31847539) B31847539
theorem B28308923 : Blo 2067435 28308923 := bstep (se 1 (by rfl) ⟨21231692, by rfl⟩ : syracuseStep 28308923 = 42463385) B42463385
theorem B18872615 : Blo 2067435 18872615 := bstep (se 1 (by rfl) ⟨14154461, by rfl⟩ : syracuseStep 18872615 = 28308923) B28308923
theorem B12581743 : Blo 2067435 12581743 := bstep (se 1 (by rfl) ⟨9436307, by rfl⟩ : syracuseStep 12581743 = 18872615) B18872615
theorem B16775657 : Blo 2067435 16775657 := bstep (se 2 (by rfl) ⟨6290871, by rfl⟩ : syracuseStep 16775657 = 12581743) B12581743
theorem B11183771 : Blo 2067435 11183771 := bstep (se 1 (by rfl) ⟨8387828, by rfl⟩ : syracuseStep 11183771 = 16775657) B16775657
theorem B29823389 : Blo 2067435 29823389 := bstep (se 3 (by rfl) ⟨5591885, by rfl⟩ : syracuseStep 29823389 = 11183771) B11183771
theorem B19882259 : Blo 2067435 19882259 := bstep (se 1 (by rfl) ⟨14911694, by rfl⟩ : syracuseStep 19882259 = 29823389) B29823389
theorem B13254839 : Blo 2067435 13254839 := bstep (se 1 (by rfl) ⟨9941129, by rfl⟩ : syracuseStep 13254839 = 19882259) B19882259
theorem B8836559 : Blo 2067435 8836559 := bstep (se 1 (by rfl) ⟨6627419, by rfl⟩ : syracuseStep 8836559 = 13254839) B13254839
theorem B5891039 : Blo 2067435 5891039 := bstep (se 1 (by rfl) ⟨4418279, by rfl⟩ : syracuseStep 5891039 = 8836559) B8836559
theorem B3927359 : Blo 2067435 3927359 := bstep (se 1 (by rfl) ⟨2945519, by rfl⟩ : syracuseStep 3927359 = 5891039) B5891039
theorem B2618239 : Blo 2067435 2618239 := bstep (se 1 (by rfl) ⟨1963679, by rfl⟩ : syracuseStep 2618239 = 3927359) B3927359
theorem B3490985 : Blo 2067435 3490985 := bstep (se 2 (by rfl) ⟨1309119, by rfl⟩ : syracuseStep 3490985 = 2618239) B2618239
theorem B2327323 : Blo 2067435 2327323 := bstep (se 1 (by rfl) ⟨1745492, by rfl⟩ : syracuseStep 2327323 = 3490985) B3490985
theorem B3103097 : Blo 2067435 3103097 := bstep (se 2 (by rfl) ⟨1163661, by rfl⟩ : syracuseStep 3103097 = 2327323) B2327323
theorem B2068731 : Blo 2067435 2068731 := bstep (se 1 (by rfl) ⟨1551548, by rfl⟩ : syracuseStep 2068731 = 3103097) B3103097
theorem B4970573 : Blo 2067435 4970573 := bbase (se 3 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 4970573 = 1863965) (by norm_num)
theorem B3313715 : Blo 2067435 3313715 := bstep (se 1 (by rfl) ⟨2485286, by rfl⟩ : syracuseStep 3313715 = 4970573) B4970573
theorem B35346293 : Blo 2067435 35346293 := bstep (se 5 (by rfl) ⟨1656857, by rfl⟩ : syracuseStep 35346293 = 3313715) B3313715
theorem B23564195 : Blo 2067435 23564195 := bstep (se 1 (by rfl) ⟨17673146, by rfl⟩ : syracuseStep 23564195 = 35346293) B35346293
theorem B15709463 : Blo 2067435 15709463 := bstep (se 1 (by rfl) ⟨11782097, by rfl⟩ : syracuseStep 15709463 = 23564195) B23564195
theorem B10472975 : Blo 2067435 10472975 := bstep (se 1 (by rfl) ⟨7854731, by rfl⟩ : syracuseStep 10472975 = 15709463) B15709463
theorem B6981983 : Blo 2067435 6981983 := bstep (se 1 (by rfl) ⟨5236487, by rfl⟩ : syracuseStep 6981983 = 10472975) B10472975
theorem B4654655 : Blo 2067435 4654655 := bstep (se 1 (by rfl) ⟨3490991, by rfl⟩ : syracuseStep 4654655 = 6981983) B6981983
theorem B3103103 : Blo 2067435 3103103 := bstep (se 1 (by rfl) ⟨2327327, by rfl⟩ : syracuseStep 3103103 = 4654655) B4654655
theorem B2068735 : Blo 2067435 2068735 := bstep (se 1 (by rfl) ⟨1551551, by rfl⟩ : syracuseStep 2068735 = 3103103) B3103103
theorem B3103109 : Blo 2067435 3103109 := bbase (se 4 (by rfl) ⟨290916, by rfl⟩ : syracuseStep 3103109 = 581833) (by norm_num)
theorem B2068739 : Blo 2067435 2068739 := bstep (se 1 (by rfl) ⟨1551554, by rfl⟩ : syracuseStep 2068739 = 3103109) B3103109
theorem B3491005 : Blo 2067435 3491005 := bbase (se 3 (by rfl) ⟨654563, by rfl⟩ : syracuseStep 3491005 = 1309127) (by norm_num)
theorem B4654673 : Blo 2067435 4654673 := bstep (se 2 (by rfl) ⟨1745502, by rfl⟩ : syracuseStep 4654673 = 3491005) B3491005
theorem B3103115 : Blo 2067435 3103115 := bstep (se 1 (by rfl) ⟨2327336, by rfl⟩ : syracuseStep 3103115 = 4654673) B4654673
theorem B2068743 : Blo 2067435 2068743 := bstep (se 1 (by rfl) ⟨1551557, by rfl⟩ : syracuseStep 2068743 = 3103115) B3103115
theorem B2327341 : Blo 2067435 2327341 := bbase (se 3 (by rfl) ⟨436376, by rfl⟩ : syracuseStep 2327341 = 872753) (by norm_num)
theorem B3103121 : Blo 2067435 3103121 := bstep (se 2 (by rfl) ⟨1163670, by rfl⟩ : syracuseStep 3103121 = 2327341) B2327341
theorem B2068747 : Blo 2067435 2068747 := bstep (se 1 (by rfl) ⟨1551560, by rfl⟩ : syracuseStep 2068747 = 3103121) B3103121
theorem B6982037 : Blo 2067435 6982037 := bbase (se 6 (by rfl) ⟨163641, by rfl⟩ : syracuseStep 6982037 = 327283) (by norm_num)
theorem B4654691 : Blo 2067435 4654691 := bstep (se 1 (by rfl) ⟨3491018, by rfl⟩ : syracuseStep 4654691 = 6982037) B6982037
theorem B3103127 : Blo 2067435 3103127 := bstep (se 1 (by rfl) ⟨2327345, by rfl⟩ : syracuseStep 3103127 = 4654691) B4654691
theorem B2068751 : Blo 2067435 2068751 := bstep (se 1 (by rfl) ⟨1551563, by rfl⟩ : syracuseStep 2068751 = 3103127) B3103127
theorem B3103133 : Blo 2067435 3103133 := bbase (se 3 (by rfl) ⟨581837, by rfl⟩ : syracuseStep 3103133 = 1163675) (by norm_num)
theorem B2068755 : Blo 2067435 2068755 := bstep (se 1 (by rfl) ⟨1551566, by rfl⟩ : syracuseStep 2068755 = 3103133) B3103133
theorem B4654709 : Blo 2067435 4654709 := bbase (se 5 (by rfl) ⟨218189, by rfl⟩ : syracuseStep 4654709 = 436379) (by norm_num)
theorem B3103139 : Blo 2067435 3103139 := bstep (se 1 (by rfl) ⟨2327354, by rfl⟩ : syracuseStep 3103139 = 4654709) B4654709
theorem B2068759 : Blo 2067435 2068759 := bstep (se 1 (by rfl) ⟨1551569, by rfl⟩ : syracuseStep 2068759 = 3103139) B3103139
theorem B3727981 : Blo 2067435 3727981 := bbase (se 3 (by rfl) ⟨698996, by rfl⟩ : syracuseStep 3727981 = 1397993) (by norm_num)
theorem B4970641 : Blo 2067435 4970641 := bstep (se 2 (by rfl) ⟨1863990, by rfl⟩ : syracuseStep 4970641 = 3727981) B3727981
theorem B6627521 : Blo 2067435 6627521 := bstep (se 2 (by rfl) ⟨2485320, by rfl⟩ : syracuseStep 6627521 = 4970641) B4970641
theorem B17673389 : Blo 2067435 17673389 := bstep (se 3 (by rfl) ⟨3313760, by rfl⟩ : syracuseStep 17673389 = 6627521) B6627521
theorem B11782259 : Blo 2067435 11782259 := bstep (se 1 (by rfl) ⟨8836694, by rfl⟩ : syracuseStep 11782259 = 17673389) B17673389
theorem B7854839 : Blo 2067435 7854839 := bstep (se 1 (by rfl) ⟨5891129, by rfl⟩ : syracuseStep 7854839 = 11782259) B11782259
theorem B5236559 : Blo 2067435 5236559 := bstep (se 1 (by rfl) ⟨3927419, by rfl⟩ : syracuseStep 5236559 = 7854839) B7854839
theorem B3491039 : Blo 2067435 3491039 := bstep (se 1 (by rfl) ⟨2618279, by rfl⟩ : syracuseStep 3491039 = 5236559) B5236559
theorem B2327359 : Blo 2067435 2327359 := bstep (se 1 (by rfl) ⟨1745519, by rfl⟩ : syracuseStep 2327359 = 3491039) B3491039
theorem B3103145 : Blo 2067435 3103145 := bstep (se 2 (by rfl) ⟨1163679, by rfl⟩ : syracuseStep 3103145 = 2327359) B2327359
theorem B2068763 : Blo 2067435 2068763 := bstep (se 1 (by rfl) ⟨1551572, by rfl⟩ : syracuseStep 2068763 = 3103145) B3103145
theorem B7854853 : Blo 2067435 7854853 := bbase (se 4 (by rfl) ⟨736392, by rfl⟩ : syracuseStep 7854853 = 1472785) (by norm_num)
theorem B10473137 : Blo 2067435 10473137 := bstep (se 2 (by rfl) ⟨3927426, by rfl⟩ : syracuseStep 10473137 = 7854853) B7854853
theorem B6982091 : Blo 2067435 6982091 := bstep (se 1 (by rfl) ⟨5236568, by rfl⟩ : syracuseStep 6982091 = 10473137) B10473137
theorem B4654727 : Blo 2067435 4654727 := bstep (se 1 (by rfl) ⟨3491045, by rfl⟩ : syracuseStep 4654727 = 6982091) B6982091
theorem B3103151 : Blo 2067435 3103151 := bstep (se 1 (by rfl) ⟨2327363, by rfl⟩ : syracuseStep 3103151 = 4654727) B4654727
theorem B2068767 : Blo 2067435 2068767 := bstep (se 1 (by rfl) ⟨1551575, by rfl⟩ : syracuseStep 2068767 = 3103151) B3103151
theorem B3103157 : Blo 2067435 3103157 := bbase (se 5 (by rfl) ⟨145460, by rfl⟩ : syracuseStep 3103157 = 290921) (by norm_num)
theorem B2068771 : Blo 2067435 2068771 := bstep (se 1 (by rfl) ⟨1551578, by rfl⟩ : syracuseStep 2068771 = 3103157) B3103157
theorem B5236589 : Blo 2067435 5236589 := bbase (se 3 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 5236589 = 1963721) (by norm_num)
theorem B3491059 : Blo 2067435 3491059 := bstep (se 1 (by rfl) ⟨2618294, by rfl⟩ : syracuseStep 3491059 = 5236589) B5236589
theorem B4654745 : Blo 2067435 4654745 := bstep (se 2 (by rfl) ⟨1745529, by rfl⟩ : syracuseStep 4654745 = 3491059) B3491059
theorem B3103163 : Blo 2067435 3103163 := bstep (se 1 (by rfl) ⟨2327372, by rfl⟩ : syracuseStep 3103163 = 4654745) B4654745
theorem B2068775 : Blo 2067435 2068775 := bstep (se 1 (by rfl) ⟨1551581, by rfl⟩ : syracuseStep 2068775 = 3103163) B3103163
theorem B2327377 : Blo 2067435 2327377 := bbase (se 2 (by rfl) ⟨872766, by rfl⟩ : syracuseStep 2327377 = 1745533) (by norm_num)
theorem B3103169 : Blo 2067435 3103169 := bstep (se 2 (by rfl) ⟨1163688, by rfl⟩ : syracuseStep 3103169 = 2327377) B2327377
theorem B2068779 : Blo 2067435 2068779 := bstep (se 1 (by rfl) ⟨1551584, by rfl⟩ : syracuseStep 2068779 = 3103169) B3103169
theorem B2485345 : Blo 2067435 2485345 := bbase (se 2 (by rfl) ⟨932004, by rfl⟩ : syracuseStep 2485345 = 1864009) (by norm_num)
theorem B3313793 : Blo 2067435 3313793 := bstep (se 2 (by rfl) ⟨1242672, by rfl⟩ : syracuseStep 3313793 = 2485345) B2485345
theorem B2209195 : Blo 2067435 2209195 := bstep (se 1 (by rfl) ⟨1656896, by rfl⟩ : syracuseStep 2209195 = 3313793) B3313793
theorem B2945593 : Blo 2067435 2945593 := bstep (se 2 (by rfl) ⟨1104597, by rfl⟩ : syracuseStep 2945593 = 2209195) B2209195
theorem B3927457 : Blo 2067435 3927457 := bstep (se 2 (by rfl) ⟨1472796, by rfl⟩ : syracuseStep 3927457 = 2945593) B2945593
theorem B5236609 : Blo 2067435 5236609 := bstep (se 2 (by rfl) ⟨1963728, by rfl⟩ : syracuseStep 5236609 = 3927457) B3927457
theorem B6982145 : Blo 2067435 6982145 := bstep (se 2 (by rfl) ⟨2618304, by rfl⟩ : syracuseStep 6982145 = 5236609) B5236609
theorem B4654763 : Blo 2067435 4654763 := bstep (se 1 (by rfl) ⟨3491072, by rfl⟩ : syracuseStep 4654763 = 6982145) B6982145
theorem B3103175 : Blo 2067435 3103175 := bstep (se 1 (by rfl) ⟨2327381, by rfl⟩ : syracuseStep 3103175 = 4654763) B4654763
theorem B2068783 : Blo 2067435 2068783 := bstep (se 1 (by rfl) ⟨1551587, by rfl⟩ : syracuseStep 2068783 = 3103175) B3103175
theorem B3103181 : Blo 2067435 3103181 := bbase (se 3 (by rfl) ⟨581846, by rfl⟩ : syracuseStep 3103181 = 1163693) (by norm_num)
theorem B2068787 : Blo 2067435 2068787 := bstep (se 1 (by rfl) ⟨1551590, by rfl⟩ : syracuseStep 2068787 = 3103181) B3103181
theorem B4654781 : Blo 2067435 4654781 := bbase (se 3 (by rfl) ⟨872771, by rfl⟩ : syracuseStep 4654781 = 1745543) (by norm_num)
theorem B3103187 : Blo 2067435 3103187 := bstep (se 1 (by rfl) ⟨2327390, by rfl⟩ : syracuseStep 3103187 = 4654781) B4654781
theorem B2068791 : Blo 2067435 2068791 := bstep (se 1 (by rfl) ⟨1551593, by rfl⟩ : syracuseStep 2068791 = 3103187) B3103187
theorem B3491093 : Blo 2067435 3491093 := bbase (se 6 (by rfl) ⟨81822, by rfl⟩ : syracuseStep 3491093 = 163645) (by norm_num)
theorem B2327395 : Blo 2067435 2327395 := bstep (se 1 (by rfl) ⟨1745546, by rfl⟩ : syracuseStep 2327395 = 3491093) B3491093
theorem B3103193 : Blo 2067435 3103193 := bstep (se 2 (by rfl) ⟨1163697, by rfl⟩ : syracuseStep 3103193 = 2327395) B2327395
theorem B2068795 : Blo 2067435 2068795 := bstep (se 1 (by rfl) ⟨1551596, by rfl⟩ : syracuseStep 2068795 = 3103193) B3103193
theorem B7077461 : Blo 2067435 7077461 := bbase (se 8 (by rfl) ⟨41469, by rfl⟩ : syracuseStep 7077461 = 82939) (by norm_num)
theorem B75492917 : Blo 2067435 75492917 := bstep (se 5 (by rfl) ⟨3538730, by rfl⟩ : syracuseStep 75492917 = 7077461) B7077461
theorem B50328611 : Blo 2067435 50328611 := bstep (se 1 (by rfl) ⟨37746458, by rfl⟩ : syracuseStep 50328611 = 75492917) B75492917
theorem B33552407 : Blo 2067435 33552407 := bstep (se 1 (by rfl) ⟨25164305, by rfl⟩ : syracuseStep 33552407 = 50328611) B50328611
theorem B22368271 : Blo 2067435 22368271 := bstep (se 1 (by rfl) ⟨16776203, by rfl⟩ : syracuseStep 22368271 = 33552407) B33552407
theorem B29824361 : Blo 2067435 29824361 := bstep (se 2 (by rfl) ⟨11184135, by rfl⟩ : syracuseStep 29824361 = 22368271) B22368271
theorem B19882907 : Blo 2067435 19882907 := bstep (se 1 (by rfl) ⟨14912180, by rfl⟩ : syracuseStep 19882907 = 29824361) B29824361
theorem B13255271 : Blo 2067435 13255271 := bstep (se 1 (by rfl) ⟨9941453, by rfl⟩ : syracuseStep 13255271 = 19882907) B19882907
theorem B8836847 : Blo 2067435 8836847 := bstep (se 1 (by rfl) ⟨6627635, by rfl⟩ : syracuseStep 8836847 = 13255271) B13255271
theorem B5891231 : Blo 2067435 5891231 := bstep (se 1 (by rfl) ⟨4418423, by rfl⟩ : syracuseStep 5891231 = 8836847) B8836847
theorem B15709949 : Blo 2067435 15709949 := bstep (se 3 (by rfl) ⟨2945615, by rfl⟩ : syracuseStep 15709949 = 5891231) B5891231
theorem B10473299 : Blo 2067435 10473299 := bstep (se 1 (by rfl) ⟨7854974, by rfl⟩ : syracuseStep 10473299 = 15709949) B15709949
theorem B6982199 : Blo 2067435 6982199 := bstep (se 1 (by rfl) ⟨5236649, by rfl⟩ : syracuseStep 6982199 = 10473299) B10473299
theorem B4654799 : Blo 2067435 4654799 := bstep (se 1 (by rfl) ⟨3491099, by rfl⟩ : syracuseStep 4654799 = 6982199) B6982199
theorem B3103199 : Blo 2067435 3103199 := bstep (se 1 (by rfl) ⟨2327399, by rfl⟩ : syracuseStep 3103199 = 4654799) B4654799
theorem B2068799 : Blo 2067435 2068799 := bstep (se 1 (by rfl) ⟨1551599, by rfl⟩ : syracuseStep 2068799 = 3103199) B3103199
theorem B3103205 : Blo 2067435 3103205 := bbase (se 4 (by rfl) ⟨290925, by rfl⟩ : syracuseStep 3103205 = 581851) (by norm_num)
theorem B2068803 : Blo 2067435 2068803 := bstep (se 1 (by rfl) ⟨1551602, by rfl⟩ : syracuseStep 2068803 = 3103205) B3103205
theorem B8502581 : Blo 2067435 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B5668387 : Blo 2067435 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B30231397 : Blo 2067435 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B40308529 : Blo 2067435 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B53744705 : Blo 2067435 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B35829803 : Blo 2067435 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B23886535 : Blo 2067435 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B31848713 : Blo 2067435 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B21232475 : Blo 2067435 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B14154983 : Blo 2067435 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B9436655 : Blo 2067435 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B6291103 : Blo 2067435 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B8388137 : Blo 2067435 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B5592091 : Blo 2067435 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B7456121 : Blo 2067435 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B4970747 : Blo 2067435 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B13255325 : Blo 2067435 13255325 := bstep (se 3 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 13255325 = 4970747) B4970747
theorem B8836883 : Blo 2067435 8836883 := bstep (se 1 (by rfl) ⟨6627662, by rfl⟩ : syracuseStep 8836883 = 13255325) B13255325
theorem B5891255 : Blo 2067435 5891255 := bstep (se 1 (by rfl) ⟨4418441, by rfl⟩ : syracuseStep 5891255 = 8836883) B8836883
theorem B3927503 : Blo 2067435 3927503 := bstep (se 1 (by rfl) ⟨2945627, by rfl⟩ : syracuseStep 3927503 = 5891255) B5891255
theorem B2618335 : Blo 2067435 2618335 := bstep (se 1 (by rfl) ⟨1963751, by rfl⟩ : syracuseStep 2618335 = 3927503) B3927503
theorem B3491113 : Blo 2067435 3491113 := bstep (se 2 (by rfl) ⟨1309167, by rfl⟩ : syracuseStep 3491113 = 2618335) B2618335
theorem B4654817 : Blo 2067435 4654817 := bstep (se 2 (by rfl) ⟨1745556, by rfl⟩ : syracuseStep 4654817 = 3491113) B3491113
theorem B3103211 : Blo 2067435 3103211 := bstep (se 1 (by rfl) ⟨2327408, by rfl⟩ : syracuseStep 3103211 = 4654817) B4654817
theorem B2068807 : Blo 2067435 2068807 := bstep (se 1 (by rfl) ⟨1551605, by rfl⟩ : syracuseStep 2068807 = 3103211) B3103211
theorem B2327413 : Blo 2067435 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B3103217 : Blo 2067435 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B2068811 : Blo 2067435 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B2618345 : Blo 2067435 2618345 := bbase (se 2 (by rfl) ⟨981879, by rfl⟩ : syracuseStep 2618345 = 1963759) (by norm_num)
theorem B6982253 : Blo 2067435 6982253 := bstep (se 3 (by rfl) ⟨1309172, by rfl⟩ : syracuseStep 6982253 = 2618345) B2618345
theorem B4654835 : Blo 2067435 4654835 := bstep (se 1 (by rfl) ⟨3491126, by rfl⟩ : syracuseStep 4654835 = 6982253) B6982253
theorem B3103223 : Blo 2067435 3103223 := bstep (se 1 (by rfl) ⟨2327417, by rfl⟩ : syracuseStep 3103223 = 4654835) B4654835
theorem B2068815 : Blo 2067435 2068815 := bstep (se 1 (by rfl) ⟨1551611, by rfl⟩ : syracuseStep 2068815 = 3103223) B3103223
theorem B3103229 : Blo 2067435 3103229 := bbase (se 3 (by rfl) ⟨581855, by rfl⟩ : syracuseStep 3103229 = 1163711) (by norm_num)
theorem B2068819 : Blo 2067435 2068819 := bstep (se 1 (by rfl) ⟨1551614, by rfl⟩ : syracuseStep 2068819 = 3103229) B3103229
theorem B4654853 : Blo 2067435 4654853 := bbase (se 4 (by rfl) ⟨436392, by rfl⟩ : syracuseStep 4654853 = 872785) (by norm_num)
theorem B3103235 : Blo 2067435 3103235 := bstep (se 1 (by rfl) ⟨2327426, by rfl⟩ : syracuseStep 3103235 = 4654853) B4654853
theorem B2068823 : Blo 2067435 2068823 := bstep (se 1 (by rfl) ⟨1551617, by rfl⟩ : syracuseStep 2068823 = 3103235) B3103235
theorem B3927541 : Blo 2067435 3927541 := bbase (se 5 (by rfl) ⟨184103, by rfl⟩ : syracuseStep 3927541 = 368207) (by norm_num)
theorem B5236721 : Blo 2067435 5236721 := bstep (se 2 (by rfl) ⟨1963770, by rfl⟩ : syracuseStep 5236721 = 3927541) B3927541
theorem B3491147 : Blo 2067435 3491147 := bstep (se 1 (by rfl) ⟨2618360, by rfl⟩ : syracuseStep 3491147 = 5236721) B5236721
theorem B2327431 : Blo 2067435 2327431 := bstep (se 1 (by rfl) ⟨1745573, by rfl⟩ : syracuseStep 2327431 = 3491147) B3491147
theorem B3103241 : Blo 2067435 3103241 := bstep (se 2 (by rfl) ⟨1163715, by rfl⟩ : syracuseStep 3103241 = 2327431) B2327431
theorem B2068827 : Blo 2067435 2068827 := bstep (se 1 (by rfl) ⟨1551620, by rfl⟩ : syracuseStep 2068827 = 3103241) B3103241
theorem B10473461 : Blo 2067435 10473461 := bbase (se 5 (by rfl) ⟨490943, by rfl⟩ : syracuseStep 10473461 = 981887) (by norm_num)
theorem B6982307 : Blo 2067435 6982307 := bstep (se 1 (by rfl) ⟨5236730, by rfl⟩ : syracuseStep 6982307 = 10473461) B10473461
theorem B4654871 : Blo 2067435 4654871 := bstep (se 1 (by rfl) ⟨3491153, by rfl⟩ : syracuseStep 4654871 = 6982307) B6982307
theorem B3103247 : Blo 2067435 3103247 := bstep (se 1 (by rfl) ⟨2327435, by rfl⟩ : syracuseStep 3103247 = 4654871) B4654871
theorem B2068831 : Blo 2067435 2068831 := bstep (se 1 (by rfl) ⟨1551623, by rfl⟩ : syracuseStep 2068831 = 3103247) B3103247
theorem B3103253 : Blo 2067435 3103253 := bbase (se 6 (by rfl) ⟨72732, by rfl⟩ : syracuseStep 3103253 = 145465) (by norm_num)
theorem B2068835 : Blo 2067435 2068835 := bstep (se 1 (by rfl) ⟨1551626, by rfl⟩ : syracuseStep 2068835 = 3103253) B3103253
theorem B17674037 : Blo 2067435 17674037 := bbase (se 5 (by rfl) ⟨828470, by rfl⟩ : syracuseStep 17674037 = 1656941) (by norm_num)
theorem B11782691 : Blo 2067435 11782691 := bstep (se 1 (by rfl) ⟨8837018, by rfl⟩ : syracuseStep 11782691 = 17674037) B17674037
theorem B7855127 : Blo 2067435 7855127 := bstep (se 1 (by rfl) ⟨5891345, by rfl⟩ : syracuseStep 7855127 = 11782691) B11782691
theorem B5236751 : Blo 2067435 5236751 := bstep (se 1 (by rfl) ⟨3927563, by rfl⟩ : syracuseStep 5236751 = 7855127) B7855127
theorem B3491167 : Blo 2067435 3491167 := bstep (se 1 (by rfl) ⟨2618375, by rfl⟩ : syracuseStep 3491167 = 5236751) B5236751
theorem B4654889 : Blo 2067435 4654889 := bstep (se 2 (by rfl) ⟨1745583, by rfl⟩ : syracuseStep 4654889 = 3491167) B3491167
theorem B3103259 : Blo 2067435 3103259 := bstep (se 1 (by rfl) ⟨2327444, by rfl⟩ : syracuseStep 3103259 = 4654889) B4654889
theorem B2068839 : Blo 2067435 2068839 := bstep (se 1 (by rfl) ⟨1551629, by rfl⟩ : syracuseStep 2068839 = 3103259) B3103259
theorem B2327449 : Blo 2067435 2327449 := bbase (se 2 (by rfl) ⟨872793, by rfl⟩ : syracuseStep 2327449 = 1745587) (by norm_num)
theorem B3103265 : Blo 2067435 3103265 := bstep (se 2 (by rfl) ⟨1163724, by rfl⟩ : syracuseStep 3103265 = 2327449) B2327449
theorem B2068843 : Blo 2067435 2068843 := bstep (se 1 (by rfl) ⟨1551632, by rfl⟩ : syracuseStep 2068843 = 3103265) B3103265
theorem B7855157 : Blo 2067435 7855157 := bbase (se 5 (by rfl) ⟨368210, by rfl⟩ : syracuseStep 7855157 = 736421) (by norm_num)
theorem B5236771 : Blo 2067435 5236771 := bstep (se 1 (by rfl) ⟨3927578, by rfl⟩ : syracuseStep 5236771 = 7855157) B7855157
theorem B6982361 : Blo 2067435 6982361 := bstep (se 2 (by rfl) ⟨2618385, by rfl⟩ : syracuseStep 6982361 = 5236771) B5236771
theorem B4654907 : Blo 2067435 4654907 := bstep (se 1 (by rfl) ⟨3491180, by rfl⟩ : syracuseStep 4654907 = 6982361) B6982361
theorem B3103271 : Blo 2067435 3103271 := bstep (se 1 (by rfl) ⟨2327453, by rfl⟩ : syracuseStep 3103271 = 4654907) B4654907
theorem B2068847 : Blo 2067435 2068847 := bstep (se 1 (by rfl) ⟨1551635, by rfl⟩ : syracuseStep 2068847 = 3103271) B3103271
theorem B3103277 : Blo 2067435 3103277 := bbase (se 3 (by rfl) ⟨581864, by rfl⟩ : syracuseStep 3103277 = 1163729) (by norm_num)
theorem B2068851 : Blo 2067435 2068851 := bstep (se 1 (by rfl) ⟨1551638, by rfl⟩ : syracuseStep 2068851 = 3103277) B3103277
theorem B4654925 : Blo 2067435 4654925 := bbase (se 3 (by rfl) ⟨872798, by rfl⟩ : syracuseStep 4654925 = 1745597) (by norm_num)
theorem B3103283 : Blo 2067435 3103283 := bstep (se 1 (by rfl) ⟨2327462, by rfl⟩ : syracuseStep 3103283 = 4654925) B4654925
theorem B2068855 : Blo 2067435 2068855 := bstep (se 1 (by rfl) ⟨1551641, by rfl⟩ : syracuseStep 2068855 = 3103283) B3103283
theorem B2618401 : Blo 2067435 2618401 := bbase (se 2 (by rfl) ⟨981900, by rfl⟩ : syracuseStep 2618401 = 1963801) (by norm_num)
theorem B3491201 : Blo 2067435 3491201 := bstep (se 2 (by rfl) ⟨1309200, by rfl⟩ : syracuseStep 3491201 = 2618401) B2618401
theorem B2327467 : Blo 2067435 2327467 := bstep (se 1 (by rfl) ⟨1745600, by rfl⟩ : syracuseStep 2327467 = 3491201) B3491201
theorem B3103289 : Blo 2067435 3103289 := bstep (se 2 (by rfl) ⟨1163733, by rfl⟩ : syracuseStep 3103289 = 2327467) B2327467
theorem B2068859 : Blo 2067435 2068859 := bstep (se 1 (by rfl) ⟨1551644, by rfl⟩ : syracuseStep 2068859 = 3103289) B3103289
theorem B23565653 : Blo 2067435 23565653 := bbase (se 14 (by rfl) ⟨2157, by rfl⟩ : syracuseStep 23565653 = 4315) (by norm_num)
theorem B15710435 : Blo 2067435 15710435 := bstep (se 1 (by rfl) ⟨11782826, by rfl⟩ : syracuseStep 15710435 = 23565653) B23565653
theorem B10473623 : Blo 2067435 10473623 := bstep (se 1 (by rfl) ⟨7855217, by rfl⟩ : syracuseStep 10473623 = 15710435) B15710435
theorem B6982415 : Blo 2067435 6982415 := bstep (se 1 (by rfl) ⟨5236811, by rfl⟩ : syracuseStep 6982415 = 10473623) B10473623
theorem B4654943 : Blo 2067435 4654943 := bstep (se 1 (by rfl) ⟨3491207, by rfl⟩ : syracuseStep 4654943 = 6982415) B6982415
theorem B3103295 : Blo 2067435 3103295 := bstep (se 1 (by rfl) ⟨2327471, by rfl⟩ : syracuseStep 3103295 = 4654943) B4654943
theorem B2068863 : Blo 2067435 2068863 := bstep (se 1 (by rfl) ⟨1551647, by rfl⟩ : syracuseStep 2068863 = 3103295) B3103295
theorem B3103301 : Blo 2067435 3103301 := bbase (se 4 (by rfl) ⟨290934, by rfl⟩ : syracuseStep 3103301 = 581869) (by norm_num)
theorem B2068867 : Blo 2067435 2068867 := bstep (se 1 (by rfl) ⟨1551650, by rfl⟩ : syracuseStep 2068867 = 3103301) B3103301
theorem B3491221 : Blo 2067435 3491221 := bbase (se 6 (by rfl) ⟨81825, by rfl⟩ : syracuseStep 3491221 = 163651) (by norm_num)
theorem B4654961 : Blo 2067435 4654961 := bstep (se 2 (by rfl) ⟨1745610, by rfl⟩ : syracuseStep 4654961 = 3491221) B3491221
theorem B3103307 : Blo 2067435 3103307 := bstep (se 1 (by rfl) ⟨2327480, by rfl⟩ : syracuseStep 3103307 = 4654961) B4654961
theorem B2068871 : Blo 2067435 2068871 := bstep (se 1 (by rfl) ⟨1551653, by rfl⟩ : syracuseStep 2068871 = 3103307) B3103307
theorem B2327485 : Blo 2067435 2327485 := bbase (se 3 (by rfl) ⟨436403, by rfl⟩ : syracuseStep 2327485 = 872807) (by norm_num)
theorem B3103313 : Blo 2067435 3103313 := bstep (se 2 (by rfl) ⟨1163742, by rfl⟩ : syracuseStep 3103313 = 2327485) B2327485
theorem B2068875 : Blo 2067435 2068875 := bstep (se 1 (by rfl) ⟨1551656, by rfl⟩ : syracuseStep 2068875 = 3103313) B3103313
theorem B6982469 : Blo 2067435 6982469 := bbase (se 4 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 6982469 = 1309213) (by norm_num)
theorem B4654979 : Blo 2067435 4654979 := bstep (se 1 (by rfl) ⟨3491234, by rfl⟩ : syracuseStep 4654979 = 6982469) B6982469
theorem B3103319 : Blo 2067435 3103319 := bstep (se 1 (by rfl) ⟨2327489, by rfl⟩ : syracuseStep 3103319 = 4654979) B4654979
theorem B2068879 : Blo 2067435 2068879 := bstep (se 1 (by rfl) ⟨1551659, by rfl⟩ : syracuseStep 2068879 = 3103319) B3103319
theorem B3103325 : Blo 2067435 3103325 := bbase (se 3 (by rfl) ⟨581873, by rfl⟩ : syracuseStep 3103325 = 1163747) (by norm_num)
theorem B2068883 : Blo 2067435 2068883 := bstep (se 1 (by rfl) ⟨1551662, by rfl⟩ : syracuseStep 2068883 = 3103325) B3103325
theorem B4654997 : Blo 2067435 4654997 := bbase (se 6 (by rfl) ⟨109101, by rfl⟩ : syracuseStep 4654997 = 218203) (by norm_num)
theorem B3103331 : Blo 2067435 3103331 := bstep (se 1 (by rfl) ⟨2327498, by rfl⟩ : syracuseStep 3103331 = 4654997) B4654997
theorem B2068887 : Blo 2067435 2068887 := bstep (se 1 (by rfl) ⟨1551665, by rfl⟩ : syracuseStep 2068887 = 3103331) B3103331
theorem B4418621 : Blo 2067435 4418621 := bbase (se 3 (by rfl) ⟨828491, by rfl⟩ : syracuseStep 4418621 = 1656983) (by norm_num)
theorem B2945747 : Blo 2067435 2945747 := bstep (se 1 (by rfl) ⟨2209310, by rfl⟩ : syracuseStep 2945747 = 4418621) B4418621
theorem B7855325 : Blo 2067435 7855325 := bstep (se 3 (by rfl) ⟨1472873, by rfl⟩ : syracuseStep 7855325 = 2945747) B2945747
theorem B5236883 : Blo 2067435 5236883 := bstep (se 1 (by rfl) ⟨3927662, by rfl⟩ : syracuseStep 5236883 = 7855325) B7855325
theorem B3491255 : Blo 2067435 3491255 := bstep (se 1 (by rfl) ⟨2618441, by rfl⟩ : syracuseStep 3491255 = 5236883) B5236883
theorem B2327503 : Blo 2067435 2327503 := bstep (se 1 (by rfl) ⟨1745627, by rfl⟩ : syracuseStep 2327503 = 3491255) B3491255
theorem B3103337 : Blo 2067435 3103337 := bstep (se 2 (by rfl) ⟨1163751, by rfl⟩ : syracuseStep 3103337 = 2327503) B2327503
theorem B2068891 : Blo 2067435 2068891 := bstep (se 1 (by rfl) ⟨1551668, by rfl⟩ : syracuseStep 2068891 = 3103337) B3103337
theorem B6718373 : Blo 2067435 6718373 := bbase (se 4 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 6718373 = 1259695) (by norm_num)
theorem B4478915 : Blo 2067435 4478915 := bstep (se 1 (by rfl) ⟨3359186, by rfl⟩ : syracuseStep 4478915 = 6718373) B6718373
theorem B11943773 : Blo 2067435 11943773 := bstep (se 3 (by rfl) ⟨2239457, by rfl⟩ : syracuseStep 11943773 = 4478915) B4478915
theorem B7962515 : Blo 2067435 7962515 := bstep (se 1 (by rfl) ⟨5971886, by rfl⟩ : syracuseStep 7962515 = 11943773) B11943773
theorem B5308343 : Blo 2067435 5308343 := bstep (se 1 (by rfl) ⟨3981257, by rfl⟩ : syracuseStep 5308343 = 7962515) B7962515
theorem B3538895 : Blo 2067435 3538895 := bstep (se 1 (by rfl) ⟨2654171, by rfl⟩ : syracuseStep 3538895 = 5308343) B5308343
theorem B37748213 : Blo 2067435 37748213 := bstep (se 5 (by rfl) ⟨1769447, by rfl⟩ : syracuseStep 37748213 = 3538895) B3538895
theorem B25165475 : Blo 2067435 25165475 := bstep (se 1 (by rfl) ⟨18874106, by rfl⟩ : syracuseStep 25165475 = 37748213) B37748213
theorem B16776983 : Blo 2067435 16776983 := bstep (se 1 (by rfl) ⟨12582737, by rfl⟩ : syracuseStep 16776983 = 25165475) B25165475
theorem B11184655 : Blo 2067435 11184655 := bstep (se 1 (by rfl) ⟨8388491, by rfl⟩ : syracuseStep 11184655 = 16776983) B16776983
theorem B14912873 : Blo 2067435 14912873 := bstep (se 2 (by rfl) ⟨5592327, by rfl⟩ : syracuseStep 14912873 = 11184655) B11184655
theorem B9941915 : Blo 2067435 9941915 := bstep (se 1 (by rfl) ⟨7456436, by rfl⟩ : syracuseStep 9941915 = 14912873) B14912873
theorem B6627943 : Blo 2067435 6627943 := bstep (se 1 (by rfl) ⟨4970957, by rfl⟩ : syracuseStep 6627943 = 9941915) B9941915
theorem B8837257 : Blo 2067435 8837257 := bstep (se 2 (by rfl) ⟨3313971, by rfl⟩ : syracuseStep 8837257 = 6627943) B6627943
theorem B11783009 : Blo 2067435 11783009 := bstep (se 2 (by rfl) ⟨4418628, by rfl⟩ : syracuseStep 11783009 = 8837257) B8837257
theorem B7855339 : Blo 2067435 7855339 := bstep (se 1 (by rfl) ⟨5891504, by rfl⟩ : syracuseStep 7855339 = 11783009) B11783009
theorem B10473785 : Blo 2067435 10473785 := bstep (se 2 (by rfl) ⟨3927669, by rfl⟩ : syracuseStep 10473785 = 7855339) B7855339
theorem B6982523 : Blo 2067435 6982523 := bstep (se 1 (by rfl) ⟨5236892, by rfl⟩ : syracuseStep 6982523 = 10473785) B10473785
theorem B4655015 : Blo 2067435 4655015 := bstep (se 1 (by rfl) ⟨3491261, by rfl⟩ : syracuseStep 4655015 = 6982523) B6982523
theorem B3103343 : Blo 2067435 3103343 := bstep (se 1 (by rfl) ⟨2327507, by rfl⟩ : syracuseStep 3103343 = 4655015) B4655015
theorem B2068895 : Blo 2067435 2068895 := bstep (se 1 (by rfl) ⟨1551671, by rfl⟩ : syracuseStep 2068895 = 3103343) B3103343
theorem B3103349 : Blo 2067435 3103349 := bbase (se 5 (by rfl) ⟨145469, by rfl⟩ : syracuseStep 3103349 = 290939) (by norm_num)
theorem B2068899 : Blo 2067435 2068899 := bstep (se 1 (by rfl) ⟨1551674, by rfl⟩ : syracuseStep 2068899 = 3103349) B3103349
theorem B3927685 : Blo 2067435 3927685 := bbase (se 4 (by rfl) ⟨368220, by rfl⟩ : syracuseStep 3927685 = 736441) (by norm_num)
theorem B5236913 : Blo 2067435 5236913 := bstep (se 2 (by rfl) ⟨1963842, by rfl⟩ : syracuseStep 5236913 = 3927685) B3927685
theorem B3491275 : Blo 2067435 3491275 := bstep (se 1 (by rfl) ⟨2618456, by rfl⟩ : syracuseStep 3491275 = 5236913) B5236913
theorem B4655033 : Blo 2067435 4655033 := bstep (se 2 (by rfl) ⟨1745637, by rfl⟩ : syracuseStep 4655033 = 3491275) B3491275
theorem B3103355 : Blo 2067435 3103355 := bstep (se 1 (by rfl) ⟨2327516, by rfl⟩ : syracuseStep 3103355 = 4655033) B4655033
theorem B2068903 : Blo 2067435 2068903 := bstep (se 1 (by rfl) ⟨1551677, by rfl⟩ : syracuseStep 2068903 = 3103355) B3103355
theorem B2327521 : Blo 2067435 2327521 := bbase (se 2 (by rfl) ⟨872820, by rfl⟩ : syracuseStep 2327521 = 1745641) (by norm_num)
theorem B3103361 : Blo 2067435 3103361 := bstep (se 2 (by rfl) ⟨1163760, by rfl⟩ : syracuseStep 3103361 = 2327521) B2327521
theorem B2068907 : Blo 2067435 2068907 := bstep (se 1 (by rfl) ⟨1551680, by rfl⟩ : syracuseStep 2068907 = 3103361) B3103361
theorem B5236933 : Blo 2067435 5236933 := bbase (se 4 (by rfl) ⟨490962, by rfl⟩ : syracuseStep 5236933 = 981925) (by norm_num)
theorem B6982577 : Blo 2067435 6982577 := bstep (se 2 (by rfl) ⟨2618466, by rfl⟩ : syracuseStep 6982577 = 5236933) B5236933
theorem B4655051 : Blo 2067435 4655051 := bstep (se 1 (by rfl) ⟨3491288, by rfl⟩ : syracuseStep 4655051 = 6982577) B6982577
theorem B3103367 : Blo 2067435 3103367 := bstep (se 1 (by rfl) ⟨2327525, by rfl⟩ : syracuseStep 3103367 = 4655051) B4655051
theorem B2068911 : Blo 2067435 2068911 := bstep (se 1 (by rfl) ⟨1551683, by rfl⟩ : syracuseStep 2068911 = 3103367) B3103367
theorem B3103373 : Blo 2067435 3103373 := bbase (se 3 (by rfl) ⟨581882, by rfl⟩ : syracuseStep 3103373 = 1163765) (by norm_num)
theorem B2068915 : Blo 2067435 2068915 := bstep (se 1 (by rfl) ⟨1551686, by rfl⟩ : syracuseStep 2068915 = 3103373) B3103373
theorem B4655069 : Blo 2067435 4655069 := bbase (se 3 (by rfl) ⟨872825, by rfl⟩ : syracuseStep 4655069 = 1745651) (by norm_num)
theorem B3103379 : Blo 2067435 3103379 := bstep (se 1 (by rfl) ⟨2327534, by rfl⟩ : syracuseStep 3103379 = 4655069) B4655069
theorem B2068919 : Blo 2067435 2068919 := bstep (se 1 (by rfl) ⟨1551689, by rfl⟩ : syracuseStep 2068919 = 3103379) B3103379
theorem B3491309 : Blo 2067435 3491309 := bbase (se 3 (by rfl) ⟨654620, by rfl⟩ : syracuseStep 3491309 = 1309241) (by norm_num)
theorem B2327539 : Blo 2067435 2327539 := bstep (se 1 (by rfl) ⟨1745654, by rfl⟩ : syracuseStep 2327539 = 3491309) B3491309
theorem B3103385 : Blo 2067435 3103385 := bstep (se 2 (by rfl) ⟨1163769, by rfl⟩ : syracuseStep 3103385 = 2327539) B2327539
theorem B2068923 : Blo 2067435 2068923 := bstep (se 1 (by rfl) ⟨1551692, by rfl⟩ : syracuseStep 2068923 = 3103385) B3103385
theorem B2485517 : Blo 2067435 2485517 := bbase (se 3 (by rfl) ⟨466034, by rfl⟩ : syracuseStep 2485517 = 932069) (by norm_num)
theorem B26512181 : Blo 2067435 26512181 := bstep (se 5 (by rfl) ⟨1242758, by rfl⟩ : syracuseStep 26512181 = 2485517) B2485517
theorem B17674787 : Blo 2067435 17674787 := bstep (se 1 (by rfl) ⟨13256090, by rfl⟩ : syracuseStep 17674787 = 26512181) B26512181
theorem B11783191 : Blo 2067435 11783191 := bstep (se 1 (by rfl) ⟨8837393, by rfl⟩ : syracuseStep 11783191 = 17674787) B17674787
theorem B15710921 : Blo 2067435 15710921 := bstep (se 2 (by rfl) ⟨5891595, by rfl⟩ : syracuseStep 15710921 = 11783191) B11783191
theorem B10473947 : Blo 2067435 10473947 := bstep (se 1 (by rfl) ⟨7855460, by rfl⟩ : syracuseStep 10473947 = 15710921) B15710921
theorem B6982631 : Blo 2067435 6982631 := bstep (se 1 (by rfl) ⟨5236973, by rfl⟩ : syracuseStep 6982631 = 10473947) B10473947
theorem B4655087 : Blo 2067435 4655087 := bstep (se 1 (by rfl) ⟨3491315, by rfl⟩ : syracuseStep 4655087 = 6982631) B6982631
theorem B3103391 : Blo 2067435 3103391 := bstep (se 1 (by rfl) ⟨2327543, by rfl⟩ : syracuseStep 3103391 = 4655087) B4655087
theorem B2068927 : Blo 2067435 2068927 := bstep (se 1 (by rfl) ⟨1551695, by rfl⟩ : syracuseStep 2068927 = 3103391) B3103391
theorem B3103397 : Blo 2067435 3103397 := bbase (se 4 (by rfl) ⟨290943, by rfl⟩ : syracuseStep 3103397 = 581887) (by norm_num)
theorem B2068931 : Blo 2067435 2068931 := bstep (se 1 (by rfl) ⟨1551698, by rfl⟩ : syracuseStep 2068931 = 3103397) B3103397
theorem B2618497 : Blo 2067435 2618497 := bbase (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) (by norm_num)
theorem B3491329 : Blo 2067435 3491329 := bstep (se 2 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 3491329 = 2618497) B2618497
theorem B4655105 : Blo 2067435 4655105 := bstep (se 2 (by rfl) ⟨1745664, by rfl⟩ : syracuseStep 4655105 = 3491329) B3491329
theorem B3103403 : Blo 2067435 3103403 := bstep (se 1 (by rfl) ⟨2327552, by rfl⟩ : syracuseStep 3103403 = 4655105) B4655105
theorem B2068935 : Blo 2067435 2068935 := bstep (se 1 (by rfl) ⟨1551701, by rfl⟩ : syracuseStep 2068935 = 3103403) B3103403
theorem B2327557 : Blo 2067435 2327557 := bbase (se 4 (by rfl) ⟨218208, by rfl⟩ : syracuseStep 2327557 = 436417) (by norm_num)
theorem B3103409 : Blo 2067435 3103409 := bstep (se 2 (by rfl) ⟨1163778, by rfl⟩ : syracuseStep 3103409 = 2327557) B2327557
theorem B2068939 : Blo 2067435 2068939 := bstep (se 1 (by rfl) ⟨1551704, by rfl⟩ : syracuseStep 2068939 = 3103409) B3103409
theorem B2945821 : Blo 2067435 2945821 := bbase (se 3 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 2945821 = 1104683) (by norm_num)
theorem B3927761 : Blo 2067435 3927761 := bstep (se 2 (by rfl) ⟨1472910, by rfl⟩ : syracuseStep 3927761 = 2945821) B2945821
theorem B2618507 : Blo 2067435 2618507 := bstep (se 1 (by rfl) ⟨1963880, by rfl⟩ : syracuseStep 2618507 = 3927761) B3927761
theorem B6982685 : Blo 2067435 6982685 := bstep (se 3 (by rfl) ⟨1309253, by rfl⟩ : syracuseStep 6982685 = 2618507) B2618507
theorem B4655123 : Blo 2067435 4655123 := bstep (se 1 (by rfl) ⟨3491342, by rfl⟩ : syracuseStep 4655123 = 6982685) B6982685
theorem B3103415 : Blo 2067435 3103415 := bstep (se 1 (by rfl) ⟨2327561, by rfl⟩ : syracuseStep 3103415 = 4655123) B4655123
theorem B2068943 : Blo 2067435 2068943 := bstep (se 1 (by rfl) ⟨1551707, by rfl⟩ : syracuseStep 2068943 = 3103415) B3103415
theorem B3103421 : Blo 2067435 3103421 := bbase (se 3 (by rfl) ⟨581891, by rfl⟩ : syracuseStep 3103421 = 1163783) (by norm_num)
theorem B2068947 : Blo 2067435 2068947 := bstep (se 1 (by rfl) ⟨1551710, by rfl⟩ : syracuseStep 2068947 = 3103421) B3103421
theorem B4655141 : Blo 2067435 4655141 := bbase (se 4 (by rfl) ⟨436419, by rfl⟩ : syracuseStep 4655141 = 872839) (by norm_num)
theorem B3103427 : Blo 2067435 3103427 := bstep (se 1 (by rfl) ⟨2327570, by rfl⟩ : syracuseStep 3103427 = 4655141) B4655141
theorem B2068951 : Blo 2067435 2068951 := bstep (se 1 (by rfl) ⟨1551713, by rfl⟩ : syracuseStep 2068951 = 3103427) B3103427
theorem B5237045 : Blo 2067435 5237045 := bbase (se 5 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 5237045 = 490973) (by norm_num)
theorem B3491363 : Blo 2067435 3491363 := bstep (se 1 (by rfl) ⟨2618522, by rfl⟩ : syracuseStep 3491363 = 5237045) B5237045
theorem B2327575 : Blo 2067435 2327575 := bstep (se 1 (by rfl) ⟨1745681, by rfl⟩ : syracuseStep 2327575 = 3491363) B3491363
theorem B3103433 : Blo 2067435 3103433 := bstep (se 2 (by rfl) ⟨1163787, by rfl⟩ : syracuseStep 3103433 = 2327575) B2327575
theorem B2068955 : Blo 2067435 2068955 := bstep (se 1 (by rfl) ⟨1551716, by rfl⟩ : syracuseStep 2068955 = 3103433) B3103433
theorem B4035701 : Blo 2067435 4035701 := bbase (se 5 (by rfl) ⟨189173, by rfl⟩ : syracuseStep 4035701 = 378347) (by norm_num)
theorem B10761869 : Blo 2067435 10761869 := bstep (se 3 (by rfl) ⟨2017850, by rfl⟩ : syracuseStep 10761869 = 4035701) B4035701
theorem B7174579 : Blo 2067435 7174579 := bstep (se 1 (by rfl) ⟨5380934, by rfl⟩ : syracuseStep 7174579 = 10761869) B10761869
theorem B9566105 : Blo 2067435 9566105 := bstep (se 2 (by rfl) ⟨3587289, by rfl⟩ : syracuseStep 9566105 = 7174579) B7174579
theorem B25509613 : Blo 2067435 25509613 := bstep (se 3 (by rfl) ⟨4783052, by rfl⟩ : syracuseStep 25509613 = 9566105) B9566105
theorem B34012817 : Blo 2067435 34012817 := bstep (se 2 (by rfl) ⟨12754806, by rfl⟩ : syracuseStep 34012817 = 25509613) B25509613
theorem B22675211 : Blo 2067435 22675211 := bstep (se 1 (by rfl) ⟨17006408, by rfl⟩ : syracuseStep 22675211 = 34012817) B34012817
theorem B15116807 : Blo 2067435 15116807 := bstep (se 1 (by rfl) ⟨11337605, by rfl⟩ : syracuseStep 15116807 = 22675211) B22675211
theorem B10077871 : Blo 2067435 10077871 := bstep (se 1 (by rfl) ⟨7558403, by rfl⟩ : syracuseStep 10077871 = 15116807) B15116807
theorem B13437161 : Blo 2067435 13437161 := bstep (se 2 (by rfl) ⟨5038935, by rfl⟩ : syracuseStep 13437161 = 10077871) B10077871
theorem B8958107 : Blo 2067435 8958107 := bstep (se 1 (by rfl) ⟨6718580, by rfl⟩ : syracuseStep 8958107 = 13437161) B13437161
theorem B5972071 : Blo 2067435 5972071 := bstep (se 1 (by rfl) ⟨4479053, by rfl⟩ : syracuseStep 5972071 = 8958107) B8958107
theorem B7962761 : Blo 2067435 7962761 := bstep (se 2 (by rfl) ⟨2986035, by rfl⟩ : syracuseStep 7962761 = 5972071) B5972071
theorem B5308507 : Blo 2067435 5308507 := bstep (se 1 (by rfl) ⟨3981380, by rfl⟩ : syracuseStep 5308507 = 7962761) B7962761
theorem B28312037 : Blo 2067435 28312037 := bstep (se 4 (by rfl) ⟨2654253, by rfl⟩ : syracuseStep 28312037 = 5308507) B5308507
theorem B18874691 : Blo 2067435 18874691 := bstep (se 1 (by rfl) ⟨14156018, by rfl⟩ : syracuseStep 18874691 = 28312037) B28312037
theorem B12583127 : Blo 2067435 12583127 := bstep (se 1 (by rfl) ⟨9437345, by rfl⟩ : syracuseStep 12583127 = 18874691) B18874691
theorem B33555005 : Blo 2067435 33555005 := bstep (se 3 (by rfl) ⟨6291563, by rfl⟩ : syracuseStep 33555005 = 12583127) B12583127
theorem B22370003 : Blo 2067435 22370003 := bstep (se 1 (by rfl) ⟨16777502, by rfl⟩ : syracuseStep 22370003 = 33555005) B33555005
theorem B14913335 : Blo 2067435 14913335 := bstep (se 1 (by rfl) ⟨11185001, by rfl⟩ : syracuseStep 14913335 = 22370003) B22370003
theorem B9942223 : Blo 2067435 9942223 := bstep (se 1 (by rfl) ⟨7456667, by rfl⟩ : syracuseStep 9942223 = 14913335) B14913335
theorem B13256297 : Blo 2067435 13256297 := bstep (se 2 (by rfl) ⟨4971111, by rfl⟩ : syracuseStep 13256297 = 9942223) B9942223
theorem B8837531 : Blo 2067435 8837531 := bstep (se 1 (by rfl) ⟨6628148, by rfl⟩ : syracuseStep 8837531 = 13256297) B13256297
theorem B5891687 : Blo 2067435 5891687 := bstep (se 1 (by rfl) ⟨4418765, by rfl⟩ : syracuseStep 5891687 = 8837531) B8837531
theorem B3927791 : Blo 2067435 3927791 := bstep (se 1 (by rfl) ⟨2945843, by rfl⟩ : syracuseStep 3927791 = 5891687) B5891687
theorem B10474109 : Blo 2067435 10474109 := bstep (se 3 (by rfl) ⟨1963895, by rfl⟩ : syracuseStep 10474109 = 3927791) B3927791
theorem B6982739 : Blo 2067435 6982739 := bstep (se 1 (by rfl) ⟨5237054, by rfl⟩ : syracuseStep 6982739 = 10474109) B10474109
theorem B4655159 : Blo 2067435 4655159 := bstep (se 1 (by rfl) ⟨3491369, by rfl⟩ : syracuseStep 4655159 = 6982739) B6982739
theorem B3103439 : Blo 2067435 3103439 := bstep (se 1 (by rfl) ⟨2327579, by rfl⟩ : syracuseStep 3103439 = 4655159) B4655159
theorem B2068959 : Blo 2067435 2068959 := bstep (se 1 (by rfl) ⟨1551719, by rfl⟩ : syracuseStep 2068959 = 3103439) B3103439
theorem B3103445 : Blo 2067435 3103445 := bbase (se 7 (by rfl) ⟨36368, by rfl⟩ : syracuseStep 3103445 = 72737) (by norm_num)
theorem B2068963 : Blo 2067435 2068963 := bstep (se 1 (by rfl) ⟨1551722, by rfl⟩ : syracuseStep 2068963 = 3103445) B3103445
theorem B6291589 : Blo 2067435 6291589 := bbase (se 4 (by rfl) ⟨589836, by rfl⟩ : syracuseStep 6291589 = 1179673) (by norm_num)
theorem B8388785 : Blo 2067435 8388785 := bstep (se 2 (by rfl) ⟨3145794, by rfl⟩ : syracuseStep 8388785 = 6291589) B6291589
theorem B22370093 : Blo 2067435 22370093 := bstep (se 3 (by rfl) ⟨4194392, by rfl⟩ : syracuseStep 22370093 = 8388785) B8388785
theorem B14913395 : Blo 2067435 14913395 := bstep (se 1 (by rfl) ⟨11185046, by rfl⟩ : syracuseStep 14913395 = 22370093) B22370093
theorem B9942263 : Blo 2067435 9942263 := bstep (se 1 (by rfl) ⟨7456697, by rfl⟩ : syracuseStep 9942263 = 14913395) B14913395
theorem B6628175 : Blo 2067435 6628175 := bstep (se 1 (by rfl) ⟨4971131, by rfl⟩ : syracuseStep 6628175 = 9942263) B9942263
theorem B4418783 : Blo 2067435 4418783 := bstep (se 1 (by rfl) ⟨3314087, by rfl⟩ : syracuseStep 4418783 = 6628175) B6628175
theorem B2945855 : Blo 2067435 2945855 := bstep (se 1 (by rfl) ⟨2209391, by rfl⟩ : syracuseStep 2945855 = 4418783) B4418783
theorem B7855613 : Blo 2067435 7855613 := bstep (se 3 (by rfl) ⟨1472927, by rfl⟩ : syracuseStep 7855613 = 2945855) B2945855
theorem B5237075 : Blo 2067435 5237075 := bstep (se 1 (by rfl) ⟨3927806, by rfl⟩ : syracuseStep 5237075 = 7855613) B7855613
theorem B3491383 : Blo 2067435 3491383 := bstep (se 1 (by rfl) ⟨2618537, by rfl⟩ : syracuseStep 3491383 = 5237075) B5237075
theorem B4655177 : Blo 2067435 4655177 := bstep (se 2 (by rfl) ⟨1745691, by rfl⟩ : syracuseStep 4655177 = 3491383) B3491383
theorem B3103451 : Blo 2067435 3103451 := bstep (se 1 (by rfl) ⟨2327588, by rfl⟩ : syracuseStep 3103451 = 4655177) B4655177
theorem B2068967 : Blo 2067435 2068967 := bstep (se 1 (by rfl) ⟨1551725, by rfl⟩ : syracuseStep 2068967 = 3103451) B3103451
theorem B2327593 : Blo 2067435 2327593 := bbase (se 2 (by rfl) ⟨872847, by rfl⟩ : syracuseStep 2327593 = 1745695) (by norm_num)
theorem B3103457 : Blo 2067435 3103457 := bstep (se 2 (by rfl) ⟨1163796, by rfl⟩ : syracuseStep 3103457 = 2327593) B2327593
theorem B2068971 : Blo 2067435 2068971 := bstep (se 1 (by rfl) ⟨1551728, by rfl⟩ : syracuseStep 2068971 = 3103457) B3103457
theorem B5038973 : Blo 2067435 5038973 := bbase (se 3 (by rfl) ⟨944807, by rfl⟩ : syracuseStep 5038973 = 1889615) (by norm_num)
theorem B53749045 : Blo 2067435 53749045 := bstep (se 5 (by rfl) ⟨2519486, by rfl⟩ : syracuseStep 53749045 = 5038973) B5038973
theorem B71665393 : Blo 2067435 71665393 := bstep (se 2 (by rfl) ⟨26874522, by rfl⟩ : syracuseStep 71665393 = 53749045) B53749045
theorem B95553857 : Blo 2067435 95553857 := bstep (se 2 (by rfl) ⟨35832696, by rfl⟩ : syracuseStep 95553857 = 71665393) B71665393
theorem B63702571 : Blo 2067435 63702571 := bstep (se 1 (by rfl) ⟨47776928, by rfl⟩ : syracuseStep 63702571 = 95553857) B95553857
theorem B84936761 : Blo 2067435 84936761 := bstep (se 2 (by rfl) ⟨31851285, by rfl⟩ : syracuseStep 84936761 = 63702571) B63702571
theorem B56624507 : Blo 2067435 56624507 := bstep (se 1 (by rfl) ⟨42468380, by rfl⟩ : syracuseStep 56624507 = 84936761) B84936761
theorem B37749671 : Blo 2067435 37749671 := bstep (se 1 (by rfl) ⟨28312253, by rfl⟩ : syracuseStep 37749671 = 56624507) B56624507
theorem B25166447 : Blo 2067435 25166447 := bstep (se 1 (by rfl) ⟨18874835, by rfl⟩ : syracuseStep 25166447 = 37749671) B37749671
theorem B16777631 : Blo 2067435 16777631 := bstep (se 1 (by rfl) ⟨12583223, by rfl⟩ : syracuseStep 16777631 = 25166447) B25166447
theorem B44740349 : Blo 2067435 44740349 := bstep (se 3 (by rfl) ⟨8388815, by rfl⟩ : syracuseStep 44740349 = 16777631) B16777631
theorem B29826899 : Blo 2067435 29826899 := bstep (se 1 (by rfl) ⟨22370174, by rfl⟩ : syracuseStep 29826899 = 44740349) B44740349
theorem B19884599 : Blo 2067435 19884599 := bstep (se 1 (by rfl) ⟨14913449, by rfl⟩ : syracuseStep 19884599 = 29826899) B29826899
theorem B13256399 : Blo 2067435 13256399 := bstep (se 1 (by rfl) ⟨9942299, by rfl⟩ : syracuseStep 13256399 = 19884599) B19884599
theorem B8837599 : Blo 2067435 8837599 := bstep (se 1 (by rfl) ⟨6628199, by rfl⟩ : syracuseStep 8837599 = 13256399) B13256399
theorem B11783465 : Blo 2067435 11783465 := bstep (se 2 (by rfl) ⟨4418799, by rfl⟩ : syracuseStep 11783465 = 8837599) B8837599
theorem B7855643 : Blo 2067435 7855643 := bstep (se 1 (by rfl) ⟨5891732, by rfl⟩ : syracuseStep 7855643 = 11783465) B11783465
theorem B5237095 : Blo 2067435 5237095 := bstep (se 1 (by rfl) ⟨3927821, by rfl⟩ : syracuseStep 5237095 = 7855643) B7855643
theorem B6982793 : Blo 2067435 6982793 := bstep (se 2 (by rfl) ⟨2618547, by rfl⟩ : syracuseStep 6982793 = 5237095) B5237095
theorem B4655195 : Blo 2067435 4655195 := bstep (se 1 (by rfl) ⟨3491396, by rfl⟩ : syracuseStep 4655195 = 6982793) B6982793
theorem B3103463 : Blo 2067435 3103463 := bstep (se 1 (by rfl) ⟨2327597, by rfl⟩ : syracuseStep 3103463 = 4655195) B4655195
theorem B2068975 : Blo 2067435 2068975 := bstep (se 1 (by rfl) ⟨1551731, by rfl⟩ : syracuseStep 2068975 = 3103463) B3103463
theorem B3103469 : Blo 2067435 3103469 := bbase (se 3 (by rfl) ⟨581900, by rfl⟩ : syracuseStep 3103469 = 1163801) (by norm_num)
theorem B2068979 : Blo 2067435 2068979 := bstep (se 1 (by rfl) ⟨1551734, by rfl⟩ : syracuseStep 2068979 = 3103469) B3103469
theorem B4655213 : Blo 2067435 4655213 := bbase (se 3 (by rfl) ⟨872852, by rfl⟩ : syracuseStep 4655213 = 1745705) (by norm_num)
theorem B3103475 : Blo 2067435 3103475 := bstep (se 1 (by rfl) ⟨2327606, by rfl⟩ : syracuseStep 3103475 = 4655213) B4655213
theorem B2068983 : Blo 2067435 2068983 := bstep (se 1 (by rfl) ⟨1551737, by rfl⟩ : syracuseStep 2068983 = 3103475) B3103475
theorem B3927845 : Blo 2067435 3927845 := bbase (se 4 (by rfl) ⟨368235, by rfl⟩ : syracuseStep 3927845 = 736471) (by norm_num)
theorem B2618563 : Blo 2067435 2618563 := bstep (se 1 (by rfl) ⟨1963922, by rfl⟩ : syracuseStep 2618563 = 3927845) B3927845
theorem B3491417 : Blo 2067435 3491417 := bstep (se 2 (by rfl) ⟨1309281, by rfl⟩ : syracuseStep 3491417 = 2618563) B2618563
theorem B2327611 : Blo 2067435 2327611 := bstep (se 1 (by rfl) ⟨1745708, by rfl⟩ : syracuseStep 2327611 = 3491417) B3491417
theorem B3103481 : Blo 2067435 3103481 := bstep (se 2 (by rfl) ⟨1163805, by rfl⟩ : syracuseStep 3103481 = 2327611) B2327611
theorem B2068987 : Blo 2067435 2068987 := bstep (se 1 (by rfl) ⟨1551740, by rfl⟩ : syracuseStep 2068987 = 3103481) B3103481
theorem B3359341 : Blo 2067435 3359341 := bbase (se 3 (by rfl) ⟨629876, by rfl⟩ : syracuseStep 3359341 = 1259753) (by norm_num)
theorem B17916485 : Blo 2067435 17916485 := bstep (se 4 (by rfl) ⟨1679670, by rfl⟩ : syracuseStep 17916485 = 3359341) B3359341
theorem B47777293 : Blo 2067435 47777293 := bstep (se 3 (by rfl) ⟨8958242, by rfl⟩ : syracuseStep 47777293 = 17916485) B17916485
theorem B63703057 : Blo 2067435 63703057 := bstep (se 2 (by rfl) ⟨23888646, by rfl⟩ : syracuseStep 63703057 = 47777293) B47777293
theorem B84937409 : Blo 2067435 84937409 := bstep (se 2 (by rfl) ⟨31851528, by rfl⟩ : syracuseStep 84937409 = 63703057) B63703057
theorem B56624939 : Blo 2067435 56624939 := bstep (se 1 (by rfl) ⟨42468704, by rfl⟩ : syracuseStep 56624939 = 84937409) B84937409
theorem B37749959 : Blo 2067435 37749959 := bstep (se 1 (by rfl) ⟨28312469, by rfl⟩ : syracuseStep 37749959 = 56624939) B56624939
theorem B25166639 : Blo 2067435 25166639 := bstep (se 1 (by rfl) ⟨18874979, by rfl⟩ : syracuseStep 25166639 = 37749959) B37749959
theorem B16777759 : Blo 2067435 16777759 := bstep (se 1 (by rfl) ⟨12583319, by rfl⟩ : syracuseStep 16777759 = 25166639) B25166639
theorem B22370345 : Blo 2067435 22370345 := bstep (se 2 (by rfl) ⟨8388879, by rfl⟩ : syracuseStep 22370345 = 16777759) B16777759
theorem B14913563 : Blo 2067435 14913563 := bstep (se 1 (by rfl) ⟨11185172, by rfl⟩ : syracuseStep 14913563 = 22370345) B22370345
theorem B39769501 : Blo 2067435 39769501 := bstep (se 3 (by rfl) ⟨7456781, by rfl⟩ : syracuseStep 39769501 = 14913563) B14913563
theorem B53026001 : Blo 2067435 53026001 := bstep (se 2 (by rfl) ⟨19884750, by rfl⟩ : syracuseStep 53026001 = 39769501) B39769501
theorem B35350667 : Blo 2067435 35350667 := bstep (se 1 (by rfl) ⟨26513000, by rfl⟩ : syracuseStep 35350667 = 53026001) B53026001
theorem B23567111 : Blo 2067435 23567111 := bstep (se 1 (by rfl) ⟨17675333, by rfl⟩ : syracuseStep 23567111 = 35350667) B35350667
theorem B15711407 : Blo 2067435 15711407 := bstep (se 1 (by rfl) ⟨11783555, by rfl⟩ : syracuseStep 15711407 = 23567111) B23567111
theorem B10474271 : Blo 2067435 10474271 := bstep (se 1 (by rfl) ⟨7855703, by rfl⟩ : syracuseStep 10474271 = 15711407) B15711407
theorem B6982847 : Blo 2067435 6982847 := bstep (se 1 (by rfl) ⟨5237135, by rfl⟩ : syracuseStep 6982847 = 10474271) B10474271
theorem B4655231 : Blo 2067435 4655231 := bstep (se 1 (by rfl) ⟨3491423, by rfl⟩ : syracuseStep 4655231 = 6982847) B6982847
theorem B3103487 : Blo 2067435 3103487 := bstep (se 1 (by rfl) ⟨2327615, by rfl⟩ : syracuseStep 3103487 = 4655231) B4655231
theorem B2068991 : Blo 2067435 2068991 := bstep (se 1 (by rfl) ⟨1551743, by rfl⟩ : syracuseStep 2068991 = 3103487) B3103487
theorem B3103493 : Blo 2067435 3103493 := bbase (se 4 (by rfl) ⟨290952, by rfl⟩ : syracuseStep 3103493 = 581905) (by norm_num)
theorem B2068995 : Blo 2067435 2068995 := bstep (se 1 (by rfl) ⟨1551746, by rfl⟩ : syracuseStep 2068995 = 3103493) B3103493
theorem B3491437 : Blo 2067435 3491437 := bbase (se 3 (by rfl) ⟨654644, by rfl⟩ : syracuseStep 3491437 = 1309289) (by norm_num)
theorem B4655249 : Blo 2067435 4655249 := bstep (se 2 (by rfl) ⟨1745718, by rfl⟩ : syracuseStep 4655249 = 3491437) B3491437
theorem B3103499 : Blo 2067435 3103499 := bstep (se 1 (by rfl) ⟨2327624, by rfl⟩ : syracuseStep 3103499 = 4655249) B4655249
theorem B2068999 : Blo 2067435 2068999 := bstep (se 1 (by rfl) ⟨1551749, by rfl⟩ : syracuseStep 2068999 = 3103499) B3103499
theorem B2327629 : Blo 2067435 2327629 := bbase (se 3 (by rfl) ⟨436430, by rfl⟩ : syracuseStep 2327629 = 872861) (by norm_num)
theorem B3103505 : Blo 2067435 3103505 := bstep (se 2 (by rfl) ⟨1163814, by rfl⟩ : syracuseStep 3103505 = 2327629) B2327629
theorem B2069003 : Blo 2067435 2069003 := bstep (se 1 (by rfl) ⟨1551752, by rfl⟩ : syracuseStep 2069003 = 3103505) B3103505
theorem B6982901 : Blo 2067435 6982901 := bbase (se 5 (by rfl) ⟨327323, by rfl⟩ : syracuseStep 6982901 = 654647) (by norm_num)
theorem B4655267 : Blo 2067435 4655267 := bstep (se 1 (by rfl) ⟨3491450, by rfl⟩ : syracuseStep 4655267 = 6982901) B6982901
theorem B3103511 : Blo 2067435 3103511 := bstep (se 1 (by rfl) ⟨2327633, by rfl⟩ : syracuseStep 3103511 = 4655267) B4655267
theorem B2069007 : Blo 2067435 2069007 := bstep (se 1 (by rfl) ⟨1551755, by rfl⟩ : syracuseStep 2069007 = 3103511) B3103511
theorem B3103517 : Blo 2067435 3103517 := bbase (se 3 (by rfl) ⟨581909, by rfl⟩ : syracuseStep 3103517 = 1163819) (by norm_num)
theorem B2069011 : Blo 2067435 2069011 := bstep (se 1 (by rfl) ⟨1551758, by rfl⟩ : syracuseStep 2069011 = 3103517) B3103517
theorem B4655285 : Blo 2067435 4655285 := bbase (se 5 (by rfl) ⟨218216, by rfl⟩ : syracuseStep 4655285 = 436433) (by norm_num)
theorem B3103523 : Blo 2067435 3103523 := bstep (se 1 (by rfl) ⟨2327642, by rfl⟩ : syracuseStep 3103523 = 4655285) B4655285
theorem B2069015 : Blo 2067435 2069015 := bstep (se 1 (by rfl) ⟨1551761, by rfl⟩ : syracuseStep 2069015 = 3103523) B3103523
theorem B6291749 : Blo 2067435 6291749 := bbase (se 4 (by rfl) ⟨589851, by rfl⟩ : syracuseStep 6291749 = 1179703) (by norm_num)
theorem B4194499 : Blo 2067435 4194499 := bstep (se 1 (by rfl) ⟨3145874, by rfl⟩ : syracuseStep 4194499 = 6291749) B6291749
theorem B5592665 : Blo 2067435 5592665 := bstep (se 2 (by rfl) ⟨2097249, by rfl⟩ : syracuseStep 5592665 = 4194499) B4194499
theorem B3728443 : Blo 2067435 3728443 := bstep (se 1 (by rfl) ⟨2796332, by rfl⟩ : syracuseStep 3728443 = 5592665) B5592665
theorem B4971257 : Blo 2067435 4971257 := bstep (se 2 (by rfl) ⟨1864221, by rfl⟩ : syracuseStep 4971257 = 3728443) B3728443
theorem B3314171 : Blo 2067435 3314171 := bstep (se 1 (by rfl) ⟨2485628, by rfl⟩ : syracuseStep 3314171 = 4971257) B4971257
theorem B2209447 : Blo 2067435 2209447 := bstep (se 1 (by rfl) ⟨1657085, by rfl⟩ : syracuseStep 2209447 = 3314171) B3314171
theorem B11783717 : Blo 2067435 11783717 := bstep (se 4 (by rfl) ⟨1104723, by rfl⟩ : syracuseStep 11783717 = 2209447) B2209447
theorem B7855811 : Blo 2067435 7855811 := bstep (se 1 (by rfl) ⟨5891858, by rfl⟩ : syracuseStep 7855811 = 11783717) B11783717
theorem B5237207 : Blo 2067435 5237207 := bstep (se 1 (by rfl) ⟨3927905, by rfl⟩ : syracuseStep 5237207 = 7855811) B7855811
theorem B3491471 : Blo 2067435 3491471 := bstep (se 1 (by rfl) ⟨2618603, by rfl⟩ : syracuseStep 3491471 = 5237207) B5237207
theorem B2327647 : Blo 2067435 2327647 := bstep (se 1 (by rfl) ⟨1745735, by rfl⟩ : syracuseStep 2327647 = 3491471) B3491471
theorem B3103529 : Blo 2067435 3103529 := bstep (se 2 (by rfl) ⟨1163823, by rfl⟩ : syracuseStep 3103529 = 2327647) B2327647
theorem B2069019 : Blo 2067435 2069019 := bstep (se 1 (by rfl) ⟨1551764, by rfl⟩ : syracuseStep 2069019 = 3103529) B3103529
theorem B2485633 : Blo 2067435 2485633 := bbase (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) (by norm_num)
theorem B3314177 : Blo 2067435 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B2209451 : Blo 2067435 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B5891869 : Blo 2067435 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B7855825 : Blo 2067435 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B10474433 : Blo 2067435 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B6982955 : Blo 2067435 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B4655303 : Blo 2067435 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B3103535 : Blo 2067435 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B2069023 : Blo 2067435 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B3103541 : Blo 2067435 3103541 := bbase (se 5 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 3103541 = 290957) (by norm_num)
theorem B2069027 : Blo 2067435 2069027 := bstep (se 1 (by rfl) ⟨1551770, by rfl⟩ : syracuseStep 2069027 = 3103541) B3103541
theorem B5237237 : Blo 2067435 5237237 := bbase (se 5 (by rfl) ⟨245495, by rfl⟩ : syracuseStep 5237237 = 490991) (by norm_num)
theorem B3491491 : Blo 2067435 3491491 := bstep (se 1 (by rfl) ⟨2618618, by rfl⟩ : syracuseStep 3491491 = 5237237) B5237237
theorem B4655321 : Blo 2067435 4655321 := bstep (se 2 (by rfl) ⟨1745745, by rfl⟩ : syracuseStep 4655321 = 3491491) B3491491
theorem B3103547 : Blo 2067435 3103547 := bstep (se 1 (by rfl) ⟨2327660, by rfl⟩ : syracuseStep 3103547 = 4655321) B4655321
theorem B2069031 : Blo 2067435 2069031 := bstep (se 1 (by rfl) ⟨1551773, by rfl⟩ : syracuseStep 2069031 = 3103547) B3103547
theorem B2327665 : Blo 2067435 2327665 := bbase (se 2 (by rfl) ⟨872874, by rfl⟩ : syracuseStep 2327665 = 1745749) (by norm_num)
theorem B3103553 : Blo 2067435 3103553 := bstep (se 2 (by rfl) ⟨1163832, by rfl⟩ : syracuseStep 3103553 = 2327665) B2327665
theorem B2069035 : Blo 2067435 2069035 := bstep (se 1 (by rfl) ⟨1551776, by rfl⟩ : syracuseStep 2069035 = 3103553) B3103553
theorem B6628405 : Blo 2067435 6628405 := bbase (se 5 (by rfl) ⟨310706, by rfl⟩ : syracuseStep 6628405 = 621413) (by norm_num)
theorem B8837873 : Blo 2067435 8837873 := bstep (se 2 (by rfl) ⟨3314202, by rfl⟩ : syracuseStep 8837873 = 6628405) B6628405
theorem B5891915 : Blo 2067435 5891915 := bstep (se 1 (by rfl) ⟨4418936, by rfl⟩ : syracuseStep 5891915 = 8837873) B8837873
theorem B3927943 : Blo 2067435 3927943 := bstep (se 1 (by rfl) ⟨2945957, by rfl⟩ : syracuseStep 3927943 = 5891915) B5891915
theorem B5237257 : Blo 2067435 5237257 := bstep (se 2 (by rfl) ⟨1963971, by rfl⟩ : syracuseStep 5237257 = 3927943) B3927943
theorem B6983009 : Blo 2067435 6983009 := bstep (se 2 (by rfl) ⟨2618628, by rfl⟩ : syracuseStep 6983009 = 5237257) B5237257
theorem B4655339 : Blo 2067435 4655339 := bstep (se 1 (by rfl) ⟨3491504, by rfl⟩ : syracuseStep 4655339 = 6983009) B6983009
theorem B3103559 : Blo 2067435 3103559 := bstep (se 1 (by rfl) ⟨2327669, by rfl⟩ : syracuseStep 3103559 = 4655339) B4655339
theorem B2069039 : Blo 2067435 2069039 := bstep (se 1 (by rfl) ⟨1551779, by rfl⟩ : syracuseStep 2069039 = 3103559) B3103559
theorem B3103565 : Blo 2067435 3103565 := bbase (se 3 (by rfl) ⟨581918, by rfl⟩ : syracuseStep 3103565 = 1163837) (by norm_num)
theorem B2069043 : Blo 2067435 2069043 := bstep (se 1 (by rfl) ⟨1551782, by rfl⟩ : syracuseStep 2069043 = 3103565) B3103565
theorem B4655357 : Blo 2067435 4655357 := bbase (se 3 (by rfl) ⟨872879, by rfl⟩ : syracuseStep 4655357 = 1745759) (by norm_num)
theorem B3103571 : Blo 2067435 3103571 := bstep (se 1 (by rfl) ⟨2327678, by rfl⟩ : syracuseStep 3103571 = 4655357) B4655357
theorem B2069047 : Blo 2067435 2069047 := bstep (se 1 (by rfl) ⟨1551785, by rfl⟩ : syracuseStep 2069047 = 3103571) B3103571
theorem B3491525 : Blo 2067435 3491525 := bbase (se 4 (by rfl) ⟨327330, by rfl⟩ : syracuseStep 3491525 = 654661) (by norm_num)
theorem B2327683 : Blo 2067435 2327683 := bstep (se 1 (by rfl) ⟨1745762, by rfl⟩ : syracuseStep 2327683 = 3491525) B3491525
theorem B3103577 : Blo 2067435 3103577 := bstep (se 2 (by rfl) ⟨1163841, by rfl⟩ : syracuseStep 3103577 = 2327683) B2327683
theorem B2069051 : Blo 2067435 2069051 := bstep (se 1 (by rfl) ⟨1551788, by rfl⟩ : syracuseStep 2069051 = 3103577) B3103577
theorem B15711893 : Blo 2067435 15711893 := bbase (se 6 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 15711893 = 736495) (by norm_num)
theorem B10474595 : Blo 2067435 10474595 := bstep (se 1 (by rfl) ⟨7855946, by rfl⟩ : syracuseStep 10474595 = 15711893) B15711893
theorem B6983063 : Blo 2067435 6983063 := bstep (se 1 (by rfl) ⟨5237297, by rfl⟩ : syracuseStep 6983063 = 10474595) B10474595
theorem B4655375 : Blo 2067435 4655375 := bstep (se 1 (by rfl) ⟨3491531, by rfl⟩ : syracuseStep 4655375 = 6983063) B6983063
theorem B3103583 : Blo 2067435 3103583 := bstep (se 1 (by rfl) ⟨2327687, by rfl⟩ : syracuseStep 3103583 = 4655375) B4655375
theorem B2069055 : Blo 2067435 2069055 := bstep (se 1 (by rfl) ⟨1551791, by rfl⟩ : syracuseStep 2069055 = 3103583) B3103583
theorem B3103589 : Blo 2067435 3103589 := bbase (se 4 (by rfl) ⟨290961, by rfl⟩ : syracuseStep 3103589 = 581923) (by norm_num)
theorem B2069059 : Blo 2067435 2069059 := bstep (se 1 (by rfl) ⟨1551794, by rfl⟩ : syracuseStep 2069059 = 3103589) B3103589
theorem B3927989 : Blo 2067435 3927989 := bbase (se 5 (by rfl) ⟨184124, by rfl⟩ : syracuseStep 3927989 = 368249) (by norm_num)
theorem B2618659 : Blo 2067435 2618659 := bstep (se 1 (by rfl) ⟨1963994, by rfl⟩ : syracuseStep 2618659 = 3927989) B3927989
theorem B3491545 : Blo 2067435 3491545 := bstep (se 2 (by rfl) ⟨1309329, by rfl⟩ : syracuseStep 3491545 = 2618659) B2618659
theorem B4655393 : Blo 2067435 4655393 := bstep (se 2 (by rfl) ⟨1745772, by rfl⟩ : syracuseStep 4655393 = 3491545) B3491545
theorem B3103595 : Blo 2067435 3103595 := bstep (se 1 (by rfl) ⟨2327696, by rfl⟩ : syracuseStep 3103595 = 4655393) B4655393
theorem B2069063 : Blo 2067435 2069063 := bstep (se 1 (by rfl) ⟨1551797, by rfl⟩ : syracuseStep 2069063 = 3103595) B3103595
theorem B2327701 : Blo 2067435 2327701 := bbase (se 6 (by rfl) ⟨54555, by rfl⟩ : syracuseStep 2327701 = 109111) (by norm_num)
theorem B3103601 : Blo 2067435 3103601 := bstep (se 2 (by rfl) ⟨1163850, by rfl⟩ : syracuseStep 3103601 = 2327701) B2327701
theorem B2069067 : Blo 2067435 2069067 := bstep (se 1 (by rfl) ⟨1551800, by rfl⟩ : syracuseStep 2069067 = 3103601) B3103601
theorem B2618669 : Blo 2067435 2618669 := bbase (se 3 (by rfl) ⟨491000, by rfl⟩ : syracuseStep 2618669 = 982001) (by norm_num)
theorem B6983117 : Blo 2067435 6983117 := bstep (se 3 (by rfl) ⟨1309334, by rfl⟩ : syracuseStep 6983117 = 2618669) B2618669
theorem B4655411 : Blo 2067435 4655411 := bstep (se 1 (by rfl) ⟨3491558, by rfl⟩ : syracuseStep 4655411 = 6983117) B6983117
theorem B3103607 : Blo 2067435 3103607 := bstep (se 1 (by rfl) ⟨2327705, by rfl⟩ : syracuseStep 3103607 = 4655411) B4655411
theorem B2069071 : Blo 2067435 2069071 := bstep (se 1 (by rfl) ⟨1551803, by rfl⟩ : syracuseStep 2069071 = 3103607) B3103607
theorem B3103613 : Blo 2067435 3103613 := bbase (se 3 (by rfl) ⟨581927, by rfl⟩ : syracuseStep 3103613 = 1163855) (by norm_num)
theorem B2069075 : Blo 2067435 2069075 := bstep (se 1 (by rfl) ⟨1551806, by rfl⟩ : syracuseStep 2069075 = 3103613) B3103613
theorem B4655429 : Blo 2067435 4655429 := bbase (se 4 (by rfl) ⟨436446, by rfl⟩ : syracuseStep 4655429 = 872893) (by norm_num)
theorem B3103619 : Blo 2067435 3103619 := bstep (se 1 (by rfl) ⟨2327714, by rfl⟩ : syracuseStep 3103619 = 4655429) B4655429
theorem B2069079 : Blo 2067435 2069079 := bstep (se 1 (by rfl) ⟨1551809, by rfl⟩ : syracuseStep 2069079 = 3103619) B3103619
theorem B9942821 : Blo 2067435 9942821 := bbase (se 4 (by rfl) ⟨932139, by rfl⟩ : syracuseStep 9942821 = 1864279) (by norm_num)
theorem B6628547 : Blo 2067435 6628547 := bstep (se 1 (by rfl) ⟨4971410, by rfl⟩ : syracuseStep 6628547 = 9942821) B9942821
theorem B4419031 : Blo 2067435 4419031 := bstep (se 1 (by rfl) ⟨3314273, by rfl⟩ : syracuseStep 4419031 = 6628547) B6628547
theorem B5892041 : Blo 2067435 5892041 := bstep (se 2 (by rfl) ⟨2209515, by rfl⟩ : syracuseStep 5892041 = 4419031) B4419031
theorem B3928027 : Blo 2067435 3928027 := bstep (se 1 (by rfl) ⟨2946020, by rfl⟩ : syracuseStep 3928027 = 5892041) B5892041
theorem B5237369 : Blo 2067435 5237369 := bstep (se 2 (by rfl) ⟨1964013, by rfl⟩ : syracuseStep 5237369 = 3928027) B3928027
theorem B3491579 : Blo 2067435 3491579 := bstep (se 1 (by rfl) ⟨2618684, by rfl⟩ : syracuseStep 3491579 = 5237369) B5237369
theorem B2327719 : Blo 2067435 2327719 := bstep (se 1 (by rfl) ⟨1745789, by rfl⟩ : syracuseStep 2327719 = 3491579) B3491579
theorem B3103625 : Blo 2067435 3103625 := bstep (se 2 (by rfl) ⟨1163859, by rfl⟩ : syracuseStep 3103625 = 2327719) B2327719
theorem B2069083 : Blo 2067435 2069083 := bstep (se 1 (by rfl) ⟨1551812, by rfl⟩ : syracuseStep 2069083 = 3103625) B3103625
theorem B10474757 : Blo 2067435 10474757 := bbase (se 4 (by rfl) ⟨982008, by rfl⟩ : syracuseStep 10474757 = 1964017) (by norm_num)
theorem B6983171 : Blo 2067435 6983171 := bstep (se 1 (by rfl) ⟨5237378, by rfl⟩ : syracuseStep 6983171 = 10474757) B10474757
theorem B4655447 : Blo 2067435 4655447 := bstep (se 1 (by rfl) ⟨3491585, by rfl⟩ : syracuseStep 4655447 = 6983171) B6983171
theorem B3103631 : Blo 2067435 3103631 := bstep (se 1 (by rfl) ⟨2327723, by rfl⟩ : syracuseStep 3103631 = 4655447) B4655447
theorem B2069087 : Blo 2067435 2069087 := bstep (se 1 (by rfl) ⟨1551815, by rfl⟩ : syracuseStep 2069087 = 3103631) B3103631
theorem B3103637 : Blo 2067435 3103637 := bbase (se 6 (by rfl) ⟨72741, by rfl⟩ : syracuseStep 3103637 = 145483) (by norm_num)
theorem B2069091 : Blo 2067435 2069091 := bstep (se 1 (by rfl) ⟨1551818, by rfl⟩ : syracuseStep 2069091 = 3103637) B3103637
theorem B11784149 : Blo 2067435 11784149 := bbase (se 7 (by rfl) ⟨138095, by rfl⟩ : syracuseStep 11784149 = 276191) (by norm_num)
theorem B7856099 : Blo 2067435 7856099 := bstep (se 1 (by rfl) ⟨5892074, by rfl⟩ : syracuseStep 7856099 = 11784149) B11784149
theorem B5237399 : Blo 2067435 5237399 := bstep (se 1 (by rfl) ⟨3928049, by rfl⟩ : syracuseStep 5237399 = 7856099) B7856099
theorem B3491599 : Blo 2067435 3491599 := bstep (se 1 (by rfl) ⟨2618699, by rfl⟩ : syracuseStep 3491599 = 5237399) B5237399
theorem B4655465 : Blo 2067435 4655465 := bstep (se 2 (by rfl) ⟨1745799, by rfl⟩ : syracuseStep 4655465 = 3491599) B3491599
theorem B3103643 : Blo 2067435 3103643 := bstep (se 1 (by rfl) ⟨2327732, by rfl⟩ : syracuseStep 3103643 = 4655465) B4655465
theorem B2069095 : Blo 2067435 2069095 := bstep (se 1 (by rfl) ⟨1551821, by rfl⟩ : syracuseStep 2069095 = 3103643) B3103643
theorem B2327737 : Blo 2067435 2327737 := bbase (se 2 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 2327737 = 1745803) (by norm_num)
theorem B3103649 : Blo 2067435 3103649 := bstep (se 2 (by rfl) ⟨1163868, by rfl⟩ : syracuseStep 3103649 = 2327737) B2327737
theorem B2069099 : Blo 2067435 2069099 := bstep (se 1 (by rfl) ⟨1551824, by rfl⟩ : syracuseStep 2069099 = 3103649) B3103649
theorem B2485729 : Blo 2067435 2485729 := bbase (se 2 (by rfl) ⟨932148, by rfl⟩ : syracuseStep 2485729 = 1864297) (by norm_num)
theorem B3314305 : Blo 2067435 3314305 := bstep (se 2 (by rfl) ⟨1242864, by rfl⟩ : syracuseStep 3314305 = 2485729) B2485729
theorem B4419073 : Blo 2067435 4419073 := bstep (se 2 (by rfl) ⟨1657152, by rfl⟩ : syracuseStep 4419073 = 3314305) B3314305
theorem B5892097 : Blo 2067435 5892097 := bstep (se 2 (by rfl) ⟨2209536, by rfl⟩ : syracuseStep 5892097 = 4419073) B4419073
theorem B7856129 : Blo 2067435 7856129 := bstep (se 2 (by rfl) ⟨2946048, by rfl⟩ : syracuseStep 7856129 = 5892097) B5892097
theorem B5237419 : Blo 2067435 5237419 := bstep (se 1 (by rfl) ⟨3928064, by rfl⟩ : syracuseStep 5237419 = 7856129) B7856129
theorem B6983225 : Blo 2067435 6983225 := bstep (se 2 (by rfl) ⟨2618709, by rfl⟩ : syracuseStep 6983225 = 5237419) B5237419
theorem B4655483 : Blo 2067435 4655483 := bstep (se 1 (by rfl) ⟨3491612, by rfl⟩ : syracuseStep 4655483 = 6983225) B6983225
theorem B3103655 : Blo 2067435 3103655 := bstep (se 1 (by rfl) ⟨2327741, by rfl⟩ : syracuseStep 3103655 = 4655483) B4655483
theorem B2069103 : Blo 2067435 2069103 := bstep (se 1 (by rfl) ⟨1551827, by rfl⟩ : syracuseStep 2069103 = 3103655) B3103655
theorem B3103661 : Blo 2067435 3103661 := bbase (se 3 (by rfl) ⟨581936, by rfl⟩ : syracuseStep 3103661 = 1163873) (by norm_num)
theorem B2069107 : Blo 2067435 2069107 := bstep (se 1 (by rfl) ⟨1551830, by rfl⟩ : syracuseStep 2069107 = 3103661) B3103661
theorem B4655501 : Blo 2067435 4655501 := bbase (se 3 (by rfl) ⟨872906, by rfl⟩ : syracuseStep 4655501 = 1745813) (by norm_num)
theorem B3103667 : Blo 2067435 3103667 := bstep (se 1 (by rfl) ⟨2327750, by rfl⟩ : syracuseStep 3103667 = 4655501) B4655501
theorem B2069111 : Blo 2067435 2069111 := bstep (se 1 (by rfl) ⟨1551833, by rfl⟩ : syracuseStep 2069111 = 3103667) B3103667
theorem B2618725 : Blo 2067435 2618725 := bbase (se 4 (by rfl) ⟨245505, by rfl⟩ : syracuseStep 2618725 = 491011) (by norm_num)
theorem B3491633 : Blo 2067435 3491633 := bstep (se 2 (by rfl) ⟨1309362, by rfl⟩ : syracuseStep 3491633 = 2618725) B2618725
theorem B2327755 : Blo 2067435 2327755 := bstep (se 1 (by rfl) ⟨1745816, by rfl⟩ : syracuseStep 2327755 = 3491633) B3491633
theorem B3103673 : Blo 2067435 3103673 := bstep (se 2 (by rfl) ⟨1163877, by rfl⟩ : syracuseStep 3103673 = 2327755) B2327755
theorem B2069115 : Blo 2067435 2069115 := bstep (se 1 (by rfl) ⟨1551836, by rfl⟩ : syracuseStep 2069115 = 3103673) B3103673
theorem B18876149 : Blo 2067435 18876149 := bbase (se 5 (by rfl) ⟨884819, by rfl⟩ : syracuseStep 18876149 = 1769639) (by norm_num)
theorem B12584099 : Blo 2067435 12584099 := bstep (se 1 (by rfl) ⟨9438074, by rfl⟩ : syracuseStep 12584099 = 18876149) B18876149
theorem B8389399 : Blo 2067435 8389399 := bstep (se 1 (by rfl) ⟨6292049, by rfl⟩ : syracuseStep 8389399 = 12584099) B12584099
theorem B11185865 : Blo 2067435 11185865 := bstep (se 2 (by rfl) ⟨4194699, by rfl⟩ : syracuseStep 11185865 = 8389399) B8389399
theorem B7457243 : Blo 2067435 7457243 := bstep (se 1 (by rfl) ⟨5592932, by rfl⟩ : syracuseStep 7457243 = 11185865) B11185865
theorem B19885981 : Blo 2067435 19885981 := bstep (se 3 (by rfl) ⟨3728621, by rfl⟩ : syracuseStep 19885981 = 7457243) B7457243
theorem B26514641 : Blo 2067435 26514641 := bstep (se 2 (by rfl) ⟨9942990, by rfl⟩ : syracuseStep 26514641 = 19885981) B19885981
theorem B17676427 : Blo 2067435 17676427 := bstep (se 1 (by rfl) ⟨13257320, by rfl⟩ : syracuseStep 17676427 = 26514641) B26514641
theorem B23568569 : Blo 2067435 23568569 := bstep (se 2 (by rfl) ⟨8838213, by rfl⟩ : syracuseStep 23568569 = 17676427) B17676427
theorem B15712379 : Blo 2067435 15712379 := bstep (se 1 (by rfl) ⟨11784284, by rfl⟩ : syracuseStep 15712379 = 23568569) B23568569
theorem B10474919 : Blo 2067435 10474919 := bstep (se 1 (by rfl) ⟨7856189, by rfl⟩ : syracuseStep 10474919 = 15712379) B15712379
theorem B6983279 : Blo 2067435 6983279 := bstep (se 1 (by rfl) ⟨5237459, by rfl⟩ : syracuseStep 6983279 = 10474919) B10474919
theorem B4655519 : Blo 2067435 4655519 := bstep (se 1 (by rfl) ⟨3491639, by rfl⟩ : syracuseStep 4655519 = 6983279) B6983279
theorem B3103679 : Blo 2067435 3103679 := bstep (se 1 (by rfl) ⟨2327759, by rfl⟩ : syracuseStep 3103679 = 4655519) B4655519
theorem B2069119 : Blo 2067435 2069119 := bstep (se 1 (by rfl) ⟨1551839, by rfl⟩ : syracuseStep 2069119 = 3103679) B3103679
theorem B3103685 : Blo 2067435 3103685 := bbase (se 4 (by rfl) ⟨290970, by rfl⟩ : syracuseStep 3103685 = 581941) (by norm_num)
theorem B2069123 : Blo 2067435 2069123 := bstep (se 1 (by rfl) ⟨1551842, by rfl⟩ : syracuseStep 2069123 = 3103685) B3103685
theorem B3491653 : Blo 2067435 3491653 := bbase (se 4 (by rfl) ⟨327342, by rfl⟩ : syracuseStep 3491653 = 654685) (by norm_num)
theorem B4655537 : Blo 2067435 4655537 := bstep (se 2 (by rfl) ⟨1745826, by rfl⟩ : syracuseStep 4655537 = 3491653) B3491653
theorem B3103691 : Blo 2067435 3103691 := bstep (se 1 (by rfl) ⟨2327768, by rfl⟩ : syracuseStep 3103691 = 4655537) B4655537
theorem B2069127 : Blo 2067435 2069127 := bstep (se 1 (by rfl) ⟨1551845, by rfl⟩ : syracuseStep 2069127 = 3103691) B3103691
theorem B2327773 : Blo 2067435 2327773 := bbase (se 3 (by rfl) ⟨436457, by rfl⟩ : syracuseStep 2327773 = 872915) (by norm_num)
theorem B3103697 : Blo 2067435 3103697 := bstep (se 2 (by rfl) ⟨1163886, by rfl⟩ : syracuseStep 3103697 = 2327773) B2327773
theorem B2069131 : Blo 2067435 2069131 := bstep (se 1 (by rfl) ⟨1551848, by rfl⟩ : syracuseStep 2069131 = 3103697) B3103697
theorem B6983333 : Blo 2067435 6983333 := bbase (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) (by norm_num)
theorem B4655555 : Blo 2067435 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B3103703 : Blo 2067435 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B2069135 : Blo 2067435 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B3103709 : Blo 2067435 3103709 := bbase (se 3 (by rfl) ⟨581945, by rfl⟩ : syracuseStep 3103709 = 1163891) (by norm_num)
theorem B2069139 : Blo 2067435 2069139 := bstep (se 1 (by rfl) ⟨1551854, by rfl⟩ : syracuseStep 2069139 = 3103709) B3103709
theorem B4655573 : Blo 2067435 4655573 := bbase (se 7 (by rfl) ⟨54557, by rfl⟩ : syracuseStep 4655573 = 109115) (by norm_num)
theorem B3103715 : Blo 2067435 3103715 := bstep (se 1 (by rfl) ⟨2327786, by rfl⟩ : syracuseStep 3103715 = 4655573) B4655573
theorem B2069143 : Blo 2067435 2069143 := bstep (se 1 (by rfl) ⟨1551857, by rfl⟩ : syracuseStep 2069143 = 3103715) B3103715
theorem B4251989 : Blo 2067435 4251989 := bbase (se 10 (by rfl) ⟨6228, by rfl⟩ : syracuseStep 4251989 = 12457) (by norm_num)
theorem B2834659 : Blo 2067435 2834659 := bstep (se 1 (by rfl) ⟨2125994, by rfl⟩ : syracuseStep 2834659 = 4251989) B4251989
theorem B3779545 : Blo 2067435 3779545 := bstep (se 2 (by rfl) ⟨1417329, by rfl⟩ : syracuseStep 3779545 = 2834659) B2834659
theorem B5039393 : Blo 2067435 5039393 := bstep (se 2 (by rfl) ⟨1889772, by rfl⟩ : syracuseStep 5039393 = 3779545) B3779545
theorem B13438381 : Blo 2067435 13438381 := bstep (se 3 (by rfl) ⟨2519696, by rfl⟩ : syracuseStep 13438381 = 5039393) B5039393
theorem B17917841 : Blo 2067435 17917841 := bstep (se 2 (by rfl) ⟨6719190, by rfl⟩ : syracuseStep 17917841 = 13438381) B13438381
theorem B11945227 : Blo 2067435 11945227 := bstep (se 1 (by rfl) ⟨8958920, by rfl⟩ : syracuseStep 11945227 = 17917841) B17917841
theorem B15926969 : Blo 2067435 15926969 := bstep (se 2 (by rfl) ⟨5972613, by rfl⟩ : syracuseStep 15926969 = 11945227) B11945227
theorem B42471917 : Blo 2067435 42471917 := bstep (se 3 (by rfl) ⟨7963484, by rfl⟩ : syracuseStep 42471917 = 15926969) B15926969
theorem B28314611 : Blo 2067435 28314611 := bstep (se 1 (by rfl) ⟨21235958, by rfl⟩ : syracuseStep 28314611 = 42471917) B42471917
theorem B18876407 : Blo 2067435 18876407 := bstep (se 1 (by rfl) ⟨14157305, by rfl⟩ : syracuseStep 18876407 = 28314611) B28314611
theorem B50337085 : Blo 2067435 50337085 := bstep (se 3 (by rfl) ⟨9438203, by rfl⟩ : syracuseStep 50337085 = 18876407) B18876407
theorem B67116113 : Blo 2067435 67116113 := bstep (se 2 (by rfl) ⟨25168542, by rfl⟩ : syracuseStep 67116113 = 50337085) B50337085
theorem B44744075 : Blo 2067435 44744075 := bstep (se 1 (by rfl) ⟨33558056, by rfl⟩ : syracuseStep 44744075 = 67116113) B67116113
theorem B29829383 : Blo 2067435 29829383 := bstep (se 1 (by rfl) ⟨22372037, by rfl⟩ : syracuseStep 29829383 = 44744075) B44744075
theorem B19886255 : Blo 2067435 19886255 := bstep (se 1 (by rfl) ⟨14914691, by rfl⟩ : syracuseStep 19886255 = 29829383) B29829383
theorem B13257503 : Blo 2067435 13257503 := bstep (se 1 (by rfl) ⟨9943127, by rfl⟩ : syracuseStep 13257503 = 19886255) B19886255
theorem B8838335 : Blo 2067435 8838335 := bstep (se 1 (by rfl) ⟨6628751, by rfl⟩ : syracuseStep 8838335 = 13257503) B13257503
theorem B5892223 : Blo 2067435 5892223 := bstep (se 1 (by rfl) ⟨4419167, by rfl⟩ : syracuseStep 5892223 = 8838335) B8838335
theorem B7856297 : Blo 2067435 7856297 := bstep (se 2 (by rfl) ⟨2946111, by rfl⟩ : syracuseStep 7856297 = 5892223) B5892223
theorem B5237531 : Blo 2067435 5237531 := bstep (se 1 (by rfl) ⟨3928148, by rfl⟩ : syracuseStep 5237531 = 7856297) B7856297
theorem B3491687 : Blo 2067435 3491687 := bstep (se 1 (by rfl) ⟨2618765, by rfl⟩ : syracuseStep 3491687 = 5237531) B5237531
theorem B2327791 : Blo 2067435 2327791 := bstep (se 1 (by rfl) ⟨1745843, by rfl⟩ : syracuseStep 2327791 = 3491687) B3491687
theorem B3103721 : Blo 2067435 3103721 := bstep (se 2 (by rfl) ⟨1163895, by rfl⟩ : syracuseStep 3103721 = 2327791) B2327791
theorem B2069147 : Blo 2067435 2069147 := bstep (se 1 (by rfl) ⟨1551860, by rfl⟩ : syracuseStep 2069147 = 3103721) B3103721
theorem B3539333 : Blo 2067435 3539333 := bbase (se 4 (by rfl) ⟨331812, by rfl⟩ : syracuseStep 3539333 = 663625) (by norm_num)
theorem B9438221 : Blo 2067435 9438221 := bstep (se 3 (by rfl) ⟨1769666, by rfl⟩ : syracuseStep 9438221 = 3539333) B3539333
theorem B25168589 : Blo 2067435 25168589 := bstep (se 3 (by rfl) ⟨4719110, by rfl⟩ : syracuseStep 25168589 = 9438221) B9438221
theorem B16779059 : Blo 2067435 16779059 := bstep (se 1 (by rfl) ⟨12584294, by rfl⟩ : syracuseStep 16779059 = 25168589) B25168589
theorem B11186039 : Blo 2067435 11186039 := bstep (se 1 (by rfl) ⟨8389529, by rfl⟩ : syracuseStep 11186039 = 16779059) B16779059
theorem B7457359 : Blo 2067435 7457359 := bstep (se 1 (by rfl) ⟨5593019, by rfl⟩ : syracuseStep 7457359 = 11186039) B11186039
theorem B9943145 : Blo 2067435 9943145 := bstep (se 2 (by rfl) ⟨3728679, by rfl⟩ : syracuseStep 9943145 = 7457359) B7457359
theorem B6628763 : Blo 2067435 6628763 := bstep (se 1 (by rfl) ⟨4971572, by rfl⟩ : syracuseStep 6628763 = 9943145) B9943145
theorem B17676701 : Blo 2067435 17676701 := bstep (se 3 (by rfl) ⟨3314381, by rfl⟩ : syracuseStep 17676701 = 6628763) B6628763
theorem B11784467 : Blo 2067435 11784467 := bstep (se 1 (by rfl) ⟨8838350, by rfl⟩ : syracuseStep 11784467 = 17676701) B17676701
theorem B7856311 : Blo 2067435 7856311 := bstep (se 1 (by rfl) ⟨5892233, by rfl⟩ : syracuseStep 7856311 = 11784467) B11784467
theorem B10475081 : Blo 2067435 10475081 := bstep (se 2 (by rfl) ⟨3928155, by rfl⟩ : syracuseStep 10475081 = 7856311) B7856311
theorem B6983387 : Blo 2067435 6983387 := bstep (se 1 (by rfl) ⟨5237540, by rfl⟩ : syracuseStep 6983387 = 10475081) B10475081
theorem B4655591 : Blo 2067435 4655591 := bstep (se 1 (by rfl) ⟨3491693, by rfl⟩ : syracuseStep 4655591 = 6983387) B6983387
theorem B3103727 : Blo 2067435 3103727 := bstep (se 1 (by rfl) ⟨2327795, by rfl⟩ : syracuseStep 3103727 = 4655591) B4655591
theorem B2069151 : Blo 2067435 2069151 := bstep (se 1 (by rfl) ⟨1551863, by rfl⟩ : syracuseStep 2069151 = 3103727) B3103727
theorem B3103733 : Blo 2067435 3103733 := bbase (se 5 (by rfl) ⟨145487, by rfl⟩ : syracuseStep 3103733 = 290975) (by norm_num)
theorem B2069155 : Blo 2067435 2069155 := bstep (se 1 (by rfl) ⟨1551866, by rfl⟩ : syracuseStep 2069155 = 3103733) B3103733
theorem B2834677 : Blo 2067435 2834677 := bbase (se 5 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 2834677 = 265751) (by norm_num)
theorem B3779569 : Blo 2067435 3779569 := bstep (se 2 (by rfl) ⟨1417338, by rfl⟩ : syracuseStep 3779569 = 2834677) B2834677
theorem B5039425 : Blo 2067435 5039425 := bstep (se 2 (by rfl) ⟨1889784, by rfl⟩ : syracuseStep 5039425 = 3779569) B3779569
theorem B26876933 : Blo 2067435 26876933 := bstep (se 4 (by rfl) ⟨2519712, by rfl⟩ : syracuseStep 26876933 = 5039425) B5039425
theorem B17917955 : Blo 2067435 17917955 := bstep (se 1 (by rfl) ⟨13438466, by rfl⟩ : syracuseStep 17917955 = 26876933) B26876933
theorem B11945303 : Blo 2067435 11945303 := bstep (se 1 (by rfl) ⟨8958977, by rfl⟩ : syracuseStep 11945303 = 17917955) B17917955
theorem B7963535 : Blo 2067435 7963535 := bstep (se 1 (by rfl) ⟨5972651, by rfl⟩ : syracuseStep 7963535 = 11945303) B11945303
theorem B5309023 : Blo 2067435 5309023 := bstep (se 1 (by rfl) ⟨3981767, by rfl⟩ : syracuseStep 5309023 = 7963535) B7963535
theorem B7078697 : Blo 2067435 7078697 := bstep (se 2 (by rfl) ⟨2654511, by rfl⟩ : syracuseStep 7078697 = 5309023) B5309023
theorem B4719131 : Blo 2067435 4719131 := bstep (se 1 (by rfl) ⟨3539348, by rfl⟩ : syracuseStep 4719131 = 7078697) B7078697
theorem B3146087 : Blo 2067435 3146087 := bstep (se 1 (by rfl) ⟨2359565, by rfl⟩ : syracuseStep 3146087 = 4719131) B4719131
theorem B8389565 : Blo 2067435 8389565 := bstep (se 3 (by rfl) ⟨1573043, by rfl⟩ : syracuseStep 8389565 = 3146087) B3146087
theorem B5593043 : Blo 2067435 5593043 := bstep (se 1 (by rfl) ⟨4194782, by rfl⟩ : syracuseStep 5593043 = 8389565) B8389565
theorem B3728695 : Blo 2067435 3728695 := bstep (se 1 (by rfl) ⟨2796521, by rfl⟩ : syracuseStep 3728695 = 5593043) B5593043
theorem B4971593 : Blo 2067435 4971593 := bstep (se 2 (by rfl) ⟨1864347, by rfl⟩ : syracuseStep 4971593 = 3728695) B3728695
theorem B3314395 : Blo 2067435 3314395 := bstep (se 1 (by rfl) ⟨2485796, by rfl⟩ : syracuseStep 3314395 = 4971593) B4971593
theorem B4419193 : Blo 2067435 4419193 := bstep (se 2 (by rfl) ⟨1657197, by rfl⟩ : syracuseStep 4419193 = 3314395) B3314395
theorem B5892257 : Blo 2067435 5892257 := bstep (se 2 (by rfl) ⟨2209596, by rfl⟩ : syracuseStep 5892257 = 4419193) B4419193
theorem B3928171 : Blo 2067435 3928171 := bstep (se 1 (by rfl) ⟨2946128, by rfl⟩ : syracuseStep 3928171 = 5892257) B5892257
theorem B5237561 : Blo 2067435 5237561 := bstep (se 2 (by rfl) ⟨1964085, by rfl⟩ : syracuseStep 5237561 = 3928171) B3928171
theorem B3491707 : Blo 2067435 3491707 := bstep (se 1 (by rfl) ⟨2618780, by rfl⟩ : syracuseStep 3491707 = 5237561) B5237561
theorem B4655609 : Blo 2067435 4655609 := bstep (se 2 (by rfl) ⟨1745853, by rfl⟩ : syracuseStep 4655609 = 3491707) B3491707
theorem B3103739 : Blo 2067435 3103739 := bstep (se 1 (by rfl) ⟨2327804, by rfl⟩ : syracuseStep 3103739 = 4655609) B4655609
theorem B2069159 : Blo 2067435 2069159 := bstep (se 1 (by rfl) ⟨1551869, by rfl⟩ : syracuseStep 2069159 = 3103739) B3103739
theorem B2327809 : Blo 2067435 2327809 := bbase (se 2 (by rfl) ⟨872928, by rfl⟩ : syracuseStep 2327809 = 1745857) (by norm_num)
theorem B3103745 : Blo 2067435 3103745 := bstep (se 2 (by rfl) ⟨1163904, by rfl⟩ : syracuseStep 3103745 = 2327809) B2327809
theorem B2069163 : Blo 2067435 2069163 := bstep (se 1 (by rfl) ⟨1551872, by rfl⟩ : syracuseStep 2069163 = 3103745) B3103745
theorem B5237581 : Blo 2067435 5237581 := bbase (se 3 (by rfl) ⟨982046, by rfl⟩ : syracuseStep 5237581 = 1964093) (by norm_num)
theorem B6983441 : Blo 2067435 6983441 := bstep (se 2 (by rfl) ⟨2618790, by rfl⟩ : syracuseStep 6983441 = 5237581) B5237581
theorem B4655627 : Blo 2067435 4655627 := bstep (se 1 (by rfl) ⟨3491720, by rfl⟩ : syracuseStep 4655627 = 6983441) B6983441
theorem B3103751 : Blo 2067435 3103751 := bstep (se 1 (by rfl) ⟨2327813, by rfl⟩ : syracuseStep 3103751 = 4655627) B4655627
theorem B2069167 : Blo 2067435 2069167 := bstep (se 1 (by rfl) ⟨1551875, by rfl⟩ : syracuseStep 2069167 = 3103751) B3103751
theorem B3103757 : Blo 2067435 3103757 := bbase (se 3 (by rfl) ⟨581954, by rfl⟩ : syracuseStep 3103757 = 1163909) (by norm_num)
theorem B2069171 : Blo 2067435 2069171 := bstep (se 1 (by rfl) ⟨1551878, by rfl⟩ : syracuseStep 2069171 = 3103757) B3103757
theorem B4655645 : Blo 2067435 4655645 := bbase (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) (by norm_num)
theorem B3103763 : Blo 2067435 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B2069175 : Blo 2067435 2069175 := bstep (se 1 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 2069175 = 3103763) B3103763
theorem B3491741 : Blo 2067435 3491741 := bbase (se 3 (by rfl) ⟨654701, by rfl⟩ : syracuseStep 3491741 = 1309403) (by norm_num)
theorem B2327827 : Blo 2067435 2327827 := bstep (se 1 (by rfl) ⟨1745870, by rfl⟩ : syracuseStep 2327827 = 3491741) B3491741
theorem B3103769 : Blo 2067435 3103769 := bstep (se 2 (by rfl) ⟨1163913, by rfl⟩ : syracuseStep 3103769 = 2327827) B2327827
theorem B2069179 : Blo 2067435 2069179 := bstep (se 1 (by rfl) ⟨1551884, by rfl⟩ : syracuseStep 2069179 = 3103769) B3103769
theorem B3539389 : Blo 2067435 3539389 := bbase (se 3 (by rfl) ⟨663635, by rfl⟩ : syracuseStep 3539389 = 1327271) (by norm_num)
theorem B4719185 : Blo 2067435 4719185 := bstep (se 2 (by rfl) ⟨1769694, by rfl⟩ : syracuseStep 4719185 = 3539389) B3539389
theorem B3146123 : Blo 2067435 3146123 := bstep (se 1 (by rfl) ⟨2359592, by rfl⟩ : syracuseStep 3146123 = 4719185) B4719185
theorem B2097415 : Blo 2067435 2097415 := bstep (se 1 (by rfl) ⟨1573061, by rfl⟩ : syracuseStep 2097415 = 3146123) B3146123
theorem B2796553 : Blo 2067435 2796553 := bstep (se 2 (by rfl) ⟨1048707, by rfl⟩ : syracuseStep 2796553 = 2097415) B2097415
theorem B3728737 : Blo 2067435 3728737 := bstep (se 2 (by rfl) ⟨1398276, by rfl⟩ : syracuseStep 3728737 = 2796553) B2796553
theorem B19886597 : Blo 2067435 19886597 := bstep (se 4 (by rfl) ⟨1864368, by rfl⟩ : syracuseStep 19886597 = 3728737) B3728737
theorem B13257731 : Blo 2067435 13257731 := bstep (se 1 (by rfl) ⟨9943298, by rfl⟩ : syracuseStep 13257731 = 19886597) B19886597
theorem B8838487 : Blo 2067435 8838487 := bstep (se 1 (by rfl) ⟨6628865, by rfl⟩ : syracuseStep 8838487 = 13257731) B13257731
theorem B11784649 : Blo 2067435 11784649 := bstep (se 2 (by rfl) ⟨4419243, by rfl⟩ : syracuseStep 11784649 = 8838487) B8838487
theorem B15712865 : Blo 2067435 15712865 := bstep (se 2 (by rfl) ⟨5892324, by rfl⟩ : syracuseStep 15712865 = 11784649) B11784649
theorem B10475243 : Blo 2067435 10475243 := bstep (se 1 (by rfl) ⟨7856432, by rfl⟩ : syracuseStep 10475243 = 15712865) B15712865
theorem B6983495 : Blo 2067435 6983495 := bstep (se 1 (by rfl) ⟨5237621, by rfl⟩ : syracuseStep 6983495 = 10475243) B10475243
theorem B4655663 : Blo 2067435 4655663 := bstep (se 1 (by rfl) ⟨3491747, by rfl⟩ : syracuseStep 4655663 = 6983495) B6983495
theorem B3103775 : Blo 2067435 3103775 := bstep (se 1 (by rfl) ⟨2327831, by rfl⟩ : syracuseStep 3103775 = 4655663) B4655663
theorem B2069183 : Blo 2067435 2069183 := bstep (se 1 (by rfl) ⟨1551887, by rfl⟩ : syracuseStep 2069183 = 3103775) B3103775
theorem B3103781 : Blo 2067435 3103781 := bbase (se 4 (by rfl) ⟨290979, by rfl⟩ : syracuseStep 3103781 = 581959) (by norm_num)
theorem B2069187 : Blo 2067435 2069187 := bstep (se 1 (by rfl) ⟨1551890, by rfl⟩ : syracuseStep 2069187 = 3103781) B3103781
theorem B2618821 : Blo 2067435 2618821 := bbase (se 4 (by rfl) ⟨245514, by rfl⟩ : syracuseStep 2618821 = 491029) (by norm_num)
theorem B3491761 : Blo 2067435 3491761 := bstep (se 2 (by rfl) ⟨1309410, by rfl⟩ : syracuseStep 3491761 = 2618821) B2618821
theorem B4655681 : Blo 2067435 4655681 := bstep (se 2 (by rfl) ⟨1745880, by rfl⟩ : syracuseStep 4655681 = 3491761) B3491761
theorem B3103787 : Blo 2067435 3103787 := bstep (se 1 (by rfl) ⟨2327840, by rfl⟩ : syracuseStep 3103787 = 4655681) B4655681
theorem B2069191 : Blo 2067435 2069191 := bstep (se 1 (by rfl) ⟨1551893, by rfl⟩ : syracuseStep 2069191 = 3103787) B3103787
theorem B2327845 : Blo 2067435 2327845 := bbase (se 4 (by rfl) ⟨218235, by rfl⟩ : syracuseStep 2327845 = 436471) (by norm_num)
theorem B3103793 : Blo 2067435 3103793 := bstep (se 2 (by rfl) ⟨1163922, by rfl⟩ : syracuseStep 3103793 = 2327845) B2327845
theorem B2069195 : Blo 2067435 2069195 := bstep (se 1 (by rfl) ⟨1551896, by rfl⟩ : syracuseStep 2069195 = 3103793) B3103793
theorem B2391805 : Blo 2067435 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B3189073 : Blo 2067435 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B4252097 : Blo 2067435 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B2834731 : Blo 2067435 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B3779641 : Blo 2067435 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B20158085 : Blo 2067435 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B13438723 : Blo 2067435 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B17918297 : Blo 2067435 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B11945531 : Blo 2067435 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B7963687 : Blo 2067435 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B42472997 : Blo 2067435 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B28315331 : Blo 2067435 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B18876887 : Blo 2067435 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B12584591 : Blo 2067435 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B8389727 : Blo 2067435 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B5593151 : Blo 2067435 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B3728767 : Blo 2067435 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B4971689 : Blo 2067435 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B3314459 : Blo 2067435 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B8838557 : Blo 2067435 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B5892371 : Blo 2067435 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B3928247 : Blo 2067435 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B2618831 : Blo 2067435 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B6983549 : Blo 2067435 6983549 := bstep (se 3 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 6983549 = 2618831) B2618831
theorem B4655699 : Blo 2067435 4655699 := bstep (se 1 (by rfl) ⟨3491774, by rfl⟩ : syracuseStep 4655699 = 6983549) B6983549
theorem B3103799 : Blo 2067435 3103799 := bstep (se 1 (by rfl) ⟨2327849, by rfl⟩ : syracuseStep 3103799 = 4655699) B4655699
theorem B2069199 : Blo 2067435 2069199 := bstep (se 1 (by rfl) ⟨1551899, by rfl⟩ : syracuseStep 2069199 = 3103799) B3103799
theorem B3103805 : Blo 2067435 3103805 := bbase (se 3 (by rfl) ⟨581963, by rfl⟩ : syracuseStep 3103805 = 1163927) (by norm_num)
theorem B2069203 : Blo 2067435 2069203 := bstep (se 1 (by rfl) ⟨1551902, by rfl⟩ : syracuseStep 2069203 = 3103805) B3103805
theorem B4655717 : Blo 2067435 4655717 := bbase (se 4 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 4655717 = 872947) (by norm_num)
theorem B3103811 : Blo 2067435 3103811 := bstep (se 1 (by rfl) ⟨2327858, by rfl⟩ : syracuseStep 3103811 = 4655717) B4655717
theorem B2069207 : Blo 2067435 2069207 := bstep (se 1 (by rfl) ⟨1551905, by rfl⟩ : syracuseStep 2069207 = 3103811) B3103811
theorem B5237693 : Blo 2067435 5237693 := bbase (se 3 (by rfl) ⟨982067, by rfl⟩ : syracuseStep 5237693 = 1964135) (by norm_num)
theorem B3491795 : Blo 2067435 3491795 := bstep (se 1 (by rfl) ⟨2618846, by rfl⟩ : syracuseStep 3491795 = 5237693) B5237693
theorem B2327863 : Blo 2067435 2327863 := bstep (se 1 (by rfl) ⟨1745897, by rfl⟩ : syracuseStep 2327863 = 3491795) B3491795
theorem B3103817 : Blo 2067435 3103817 := bstep (se 2 (by rfl) ⟨1163931, by rfl⟩ : syracuseStep 3103817 = 2327863) B2327863
theorem B2069211 : Blo 2067435 2069211 := bstep (se 1 (by rfl) ⟨1551908, by rfl⟩ : syracuseStep 2069211 = 3103817) B3103817
theorem B3928277 : Blo 2067435 3928277 := bbase (se 7 (by rfl) ⟨46034, by rfl⟩ : syracuseStep 3928277 = 92069) (by norm_num)
theorem B10475405 : Blo 2067435 10475405 := bstep (se 3 (by rfl) ⟨1964138, by rfl⟩ : syracuseStep 10475405 = 3928277) B3928277
theorem B6983603 : Blo 2067435 6983603 := bstep (se 1 (by rfl) ⟨5237702, by rfl⟩ : syracuseStep 6983603 = 10475405) B10475405
theorem B4655735 : Blo 2067435 4655735 := bstep (se 1 (by rfl) ⟨3491801, by rfl⟩ : syracuseStep 4655735 = 6983603) B6983603
theorem B3103823 : Blo 2067435 3103823 := bstep (se 1 (by rfl) ⟨2327867, by rfl⟩ : syracuseStep 3103823 = 4655735) B4655735
theorem B2069215 : Blo 2067435 2069215 := bstep (se 1 (by rfl) ⟨1551911, by rfl⟩ : syracuseStep 2069215 = 3103823) B3103823
theorem B3103829 : Blo 2067435 3103829 := bbase (se 8 (by rfl) ⟨18186, by rfl⟩ : syracuseStep 3103829 = 36373) (by norm_num)
theorem B2069219 : Blo 2067435 2069219 := bstep (se 1 (by rfl) ⟨1551914, by rfl⟩ : syracuseStep 2069219 = 3103829) B3103829
theorem B2485873 : Blo 2067435 2485873 := bbase (se 2 (by rfl) ⟨932202, by rfl⟩ : syracuseStep 2485873 = 1864405) (by norm_num)
theorem B13257989 : Blo 2067435 13257989 := bstep (se 4 (by rfl) ⟨1242936, by rfl⟩ : syracuseStep 13257989 = 2485873) B2485873
theorem B8838659 : Blo 2067435 8838659 := bstep (se 1 (by rfl) ⟨6628994, by rfl⟩ : syracuseStep 8838659 = 13257989) B13257989
theorem B5892439 : Blo 2067435 5892439 := bstep (se 1 (by rfl) ⟨4419329, by rfl⟩ : syracuseStep 5892439 = 8838659) B8838659
theorem B7856585 : Blo 2067435 7856585 := bstep (se 2 (by rfl) ⟨2946219, by rfl⟩ : syracuseStep 7856585 = 5892439) B5892439
theorem B5237723 : Blo 2067435 5237723 := bstep (se 1 (by rfl) ⟨3928292, by rfl⟩ : syracuseStep 5237723 = 7856585) B7856585
theorem B3491815 : Blo 2067435 3491815 := bstep (se 1 (by rfl) ⟨2618861, by rfl⟩ : syracuseStep 3491815 = 5237723) B5237723
theorem B4655753 : Blo 2067435 4655753 := bstep (se 2 (by rfl) ⟨1745907, by rfl⟩ : syracuseStep 4655753 = 3491815) B3491815
theorem B3103835 : Blo 2067435 3103835 := bstep (se 1 (by rfl) ⟨2327876, by rfl⟩ : syracuseStep 3103835 = 4655753) B4655753
theorem B2069223 : Blo 2067435 2069223 := bstep (se 1 (by rfl) ⟨1551917, by rfl⟩ : syracuseStep 2069223 = 3103835) B3103835
theorem B2327881 : Blo 2067435 2327881 := bbase (se 2 (by rfl) ⟨872955, by rfl⟩ : syracuseStep 2327881 = 1745911) (by norm_num)
theorem B3103841 : Blo 2067435 3103841 := bstep (se 2 (by rfl) ⟨1163940, by rfl⟩ : syracuseStep 3103841 = 2327881) B2327881
theorem B2069227 : Blo 2067435 2069227 := bstep (se 1 (by rfl) ⟨1551920, by rfl⟩ : syracuseStep 2069227 = 3103841) B3103841
theorem B3027173 : Blo 2067435 3027173 := bbase (se 4 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 3027173 = 567595) (by norm_num)
theorem B8072461 : Blo 2067435 8072461 := bstep (se 3 (by rfl) ⟨1513586, by rfl⟩ : syracuseStep 8072461 = 3027173) B3027173
theorem B10763281 : Blo 2067435 10763281 := bstep (se 2 (by rfl) ⟨4036230, by rfl⟩ : syracuseStep 10763281 = 8072461) B8072461
theorem B14351041 : Blo 2067435 14351041 := bstep (se 2 (by rfl) ⟨5381640, by rfl⟩ : syracuseStep 14351041 = 10763281) B10763281
theorem B19134721 : Blo 2067435 19134721 := bstep (se 2 (by rfl) ⟨7175520, by rfl⟩ : syracuseStep 19134721 = 14351041) B14351041
theorem B102051845 : Blo 2067435 102051845 := bstep (se 4 (by rfl) ⟨9567360, by rfl⟩ : syracuseStep 102051845 = 19134721) B19134721
theorem B68034563 : Blo 2067435 68034563 := bstep (se 1 (by rfl) ⟨51025922, by rfl⟩ : syracuseStep 68034563 = 102051845) B102051845
theorem B45356375 : Blo 2067435 45356375 := bstep (se 1 (by rfl) ⟨34017281, by rfl⟩ : syracuseStep 45356375 = 68034563) B68034563
theorem B30237583 : Blo 2067435 30237583 := bstep (se 1 (by rfl) ⟨22678187, by rfl⟩ : syracuseStep 30237583 = 45356375) B45356375
theorem B40316777 : Blo 2067435 40316777 := bstep (se 2 (by rfl) ⟨15118791, by rfl⟩ : syracuseStep 40316777 = 30237583) B30237583
theorem B26877851 : Blo 2067435 26877851 := bstep (se 1 (by rfl) ⟨20158388, by rfl⟩ : syracuseStep 26877851 = 40316777) B40316777
theorem B17918567 : Blo 2067435 17918567 := bstep (se 1 (by rfl) ⟨13438925, by rfl⟩ : syracuseStep 17918567 = 26877851) B26877851
theorem B11945711 : Blo 2067435 11945711 := bstep (se 1 (by rfl) ⟨8959283, by rfl⟩ : syracuseStep 11945711 = 17918567) B17918567
theorem B7963807 : Blo 2067435 7963807 := bstep (se 1 (by rfl) ⟨5972855, by rfl⟩ : syracuseStep 7963807 = 11945711) B11945711
theorem B10618409 : Blo 2067435 10618409 := bstep (se 2 (by rfl) ⟨3981903, by rfl⟩ : syracuseStep 10618409 = 7963807) B7963807
theorem B28315757 : Blo 2067435 28315757 := bstep (se 3 (by rfl) ⟨5309204, by rfl⟩ : syracuseStep 28315757 = 10618409) B10618409
theorem B18877171 : Blo 2067435 18877171 := bstep (se 1 (by rfl) ⟨14157878, by rfl⟩ : syracuseStep 18877171 = 28315757) B28315757
theorem B25169561 : Blo 2067435 25169561 := bstep (se 2 (by rfl) ⟨9438585, by rfl⟩ : syracuseStep 25169561 = 18877171) B18877171
theorem B16779707 : Blo 2067435 16779707 := bstep (se 1 (by rfl) ⟨12584780, by rfl⟩ : syracuseStep 16779707 = 25169561) B25169561
theorem B11186471 : Blo 2067435 11186471 := bstep (se 1 (by rfl) ⟨8389853, by rfl⟩ : syracuseStep 11186471 = 16779707) B16779707
theorem B29830589 : Blo 2067435 29830589 := bstep (se 3 (by rfl) ⟨5593235, by rfl⟩ : syracuseStep 29830589 = 11186471) B11186471
theorem B19887059 : Blo 2067435 19887059 := bstep (se 1 (by rfl) ⟨14915294, by rfl⟩ : syracuseStep 19887059 = 29830589) B29830589
theorem B13258039 : Blo 2067435 13258039 := bstep (se 1 (by rfl) ⟨9943529, by rfl⟩ : syracuseStep 13258039 = 19887059) B19887059
theorem B17677385 : Blo 2067435 17677385 := bstep (se 2 (by rfl) ⟨6629019, by rfl⟩ : syracuseStep 17677385 = 13258039) B13258039
theorem B11784923 : Blo 2067435 11784923 := bstep (se 1 (by rfl) ⟨8838692, by rfl⟩ : syracuseStep 11784923 = 17677385) B17677385
theorem B7856615 : Blo 2067435 7856615 := bstep (se 1 (by rfl) ⟨5892461, by rfl⟩ : syracuseStep 7856615 = 11784923) B11784923
theorem B5237743 : Blo 2067435 5237743 := bstep (se 1 (by rfl) ⟨3928307, by rfl⟩ : syracuseStep 5237743 = 7856615) B7856615
theorem B6983657 : Blo 2067435 6983657 := bstep (se 2 (by rfl) ⟨2618871, by rfl⟩ : syracuseStep 6983657 = 5237743) B5237743
theorem B4655771 : Blo 2067435 4655771 := bstep (se 1 (by rfl) ⟨3491828, by rfl⟩ : syracuseStep 4655771 = 6983657) B6983657
theorem B3103847 : Blo 2067435 3103847 := bstep (se 1 (by rfl) ⟨2327885, by rfl⟩ : syracuseStep 3103847 = 4655771) B4655771
theorem B2069231 : Blo 2067435 2069231 := bstep (se 1 (by rfl) ⟨1551923, by rfl⟩ : syracuseStep 2069231 = 3103847) B3103847
theorem B3103853 : Blo 2067435 3103853 := bbase (se 3 (by rfl) ⟨581972, by rfl⟩ : syracuseStep 3103853 = 1163945) (by norm_num)
theorem B2069235 : Blo 2067435 2069235 := bstep (se 1 (by rfl) ⟨1551926, by rfl⟩ : syracuseStep 2069235 = 3103853) B3103853
theorem B4655789 : Blo 2067435 4655789 := bbase (se 3 (by rfl) ⟨872960, by rfl⟩ : syracuseStep 4655789 = 1745921) (by norm_num)
theorem B3103859 : Blo 2067435 3103859 := bstep (se 1 (by rfl) ⟨2327894, by rfl⟩ : syracuseStep 3103859 = 4655789) B4655789
theorem B2069239 : Blo 2067435 2069239 := bstep (se 1 (by rfl) ⟨1551929, by rfl⟩ : syracuseStep 2069239 = 3103859) B3103859
theorem B4419373 : Blo 2067435 4419373 := bbase (se 3 (by rfl) ⟨828632, by rfl⟩ : syracuseStep 4419373 = 1657265) (by norm_num)
theorem B5892497 : Blo 2067435 5892497 := bstep (se 2 (by rfl) ⟨2209686, by rfl⟩ : syracuseStep 5892497 = 4419373) B4419373
theorem B3928331 : Blo 2067435 3928331 := bstep (se 1 (by rfl) ⟨2946248, by rfl⟩ : syracuseStep 3928331 = 5892497) B5892497
theorem B2618887 : Blo 2067435 2618887 := bstep (se 1 (by rfl) ⟨1964165, by rfl⟩ : syracuseStep 2618887 = 3928331) B3928331
theorem B3491849 : Blo 2067435 3491849 := bstep (se 2 (by rfl) ⟨1309443, by rfl⟩ : syracuseStep 3491849 = 2618887) B2618887
theorem B2327899 : Blo 2067435 2327899 := bstep (se 1 (by rfl) ⟨1745924, by rfl⟩ : syracuseStep 2327899 = 3491849) B3491849
theorem B3103865 : Blo 2067435 3103865 := bstep (se 2 (by rfl) ⟨1163949, by rfl⟩ : syracuseStep 3103865 = 2327899) B2327899
theorem B2069243 : Blo 2067435 2069243 := bstep (se 1 (by rfl) ⟨1551932, by rfl⟩ : syracuseStep 2069243 = 3103865) B3103865
theorem B5309245 : Blo 2067435 5309245 := bbase (se 3 (by rfl) ⟨995483, by rfl⟩ : syracuseStep 5309245 = 1990967) (by norm_num)
theorem B28315973 : Blo 2067435 28315973 := bstep (se 4 (by rfl) ⟨2654622, by rfl⟩ : syracuseStep 28315973 = 5309245) B5309245
theorem B18877315 : Blo 2067435 18877315 := bstep (se 1 (by rfl) ⟨14157986, by rfl⟩ : syracuseStep 18877315 = 28315973) B28315973
theorem B25169753 : Blo 2067435 25169753 := bstep (se 2 (by rfl) ⟨9438657, by rfl⟩ : syracuseStep 25169753 = 18877315) B18877315
theorem B16779835 : Blo 2067435 16779835 := bstep (se 1 (by rfl) ⟨12584876, by rfl⟩ : syracuseStep 16779835 = 25169753) B25169753
theorem B22373113 : Blo 2067435 22373113 := bstep (se 2 (by rfl) ⟨8389917, by rfl⟩ : syracuseStep 22373113 = 16779835) B16779835
theorem B29830817 : Blo 2067435 29830817 := bstep (se 2 (by rfl) ⟨11186556, by rfl⟩ : syracuseStep 29830817 = 22373113) B22373113
theorem B19887211 : Blo 2067435 19887211 := bstep (se 1 (by rfl) ⟨14915408, by rfl⟩ : syracuseStep 19887211 = 29830817) B29830817
theorem B26516281 : Blo 2067435 26516281 := bstep (se 2 (by rfl) ⟨9943605, by rfl⟩ : syracuseStep 26516281 = 19887211) B19887211
theorem B35355041 : Blo 2067435 35355041 := bstep (se 2 (by rfl) ⟨13258140, by rfl⟩ : syracuseStep 35355041 = 26516281) B26516281
theorem B23570027 : Blo 2067435 23570027 := bstep (se 1 (by rfl) ⟨17677520, by rfl⟩ : syracuseStep 23570027 = 35355041) B35355041
theorem B15713351 : Blo 2067435 15713351 := bstep (se 1 (by rfl) ⟨11785013, by rfl⟩ : syracuseStep 15713351 = 23570027) B23570027
theorem B10475567 : Blo 2067435 10475567 := bstep (se 1 (by rfl) ⟨7856675, by rfl⟩ : syracuseStep 10475567 = 15713351) B15713351
theorem B6983711 : Blo 2067435 6983711 := bstep (se 1 (by rfl) ⟨5237783, by rfl⟩ : syracuseStep 6983711 = 10475567) B10475567
theorem B4655807 : Blo 2067435 4655807 := bstep (se 1 (by rfl) ⟨3491855, by rfl⟩ : syracuseStep 4655807 = 6983711) B6983711
theorem B3103871 : Blo 2067435 3103871 := bstep (se 1 (by rfl) ⟨2327903, by rfl⟩ : syracuseStep 3103871 = 4655807) B4655807
theorem B2069247 : Blo 2067435 2069247 := bstep (se 1 (by rfl) ⟨1551935, by rfl⟩ : syracuseStep 2069247 = 3103871) B3103871
theorem B3103877 : Blo 2067435 3103877 := bbase (se 4 (by rfl) ⟨290988, by rfl⟩ : syracuseStep 3103877 = 581977) (by norm_num)
theorem B2069251 : Blo 2067435 2069251 := bstep (se 1 (by rfl) ⟨1551938, by rfl⟩ : syracuseStep 2069251 = 3103877) B3103877
theorem B3491869 : Blo 2067435 3491869 := bbase (se 3 (by rfl) ⟨654725, by rfl⟩ : syracuseStep 3491869 = 1309451) (by norm_num)
theorem B4655825 : Blo 2067435 4655825 := bstep (se 2 (by rfl) ⟨1745934, by rfl⟩ : syracuseStep 4655825 = 3491869) B3491869
theorem B3103883 : Blo 2067435 3103883 := bstep (se 1 (by rfl) ⟨2327912, by rfl⟩ : syracuseStep 3103883 = 4655825) B4655825
theorem B2069255 : Blo 2067435 2069255 := bstep (se 1 (by rfl) ⟨1551941, by rfl⟩ : syracuseStep 2069255 = 3103883) B3103883
theorem B2327917 : Blo 2067435 2327917 := bbase (se 3 (by rfl) ⟨436484, by rfl⟩ : syracuseStep 2327917 = 872969) (by norm_num)
theorem B3103889 : Blo 2067435 3103889 := bstep (se 2 (by rfl) ⟨1163958, by rfl⟩ : syracuseStep 3103889 = 2327917) B2327917
theorem B2069259 : Blo 2067435 2069259 := bstep (se 1 (by rfl) ⟨1551944, by rfl⟩ : syracuseStep 2069259 = 3103889) B3103889
theorem B6983765 : Blo 2067435 6983765 := bbase (se 8 (by rfl) ⟨40920, by rfl⟩ : syracuseStep 6983765 = 81841) (by norm_num)
theorem B4655843 : Blo 2067435 4655843 := bstep (se 1 (by rfl) ⟨3491882, by rfl⟩ : syracuseStep 4655843 = 6983765) B6983765
theorem B3103895 : Blo 2067435 3103895 := bstep (se 1 (by rfl) ⟨2327921, by rfl⟩ : syracuseStep 3103895 = 4655843) B4655843
theorem B2069263 : Blo 2067435 2069263 := bstep (se 1 (by rfl) ⟨1551947, by rfl⟩ : syracuseStep 2069263 = 3103895) B3103895
theorem B3103901 : Blo 2067435 3103901 := bbase (se 3 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 3103901 = 1163963) (by norm_num)
theorem B2069267 : Blo 2067435 2069267 := bstep (se 1 (by rfl) ⟨1551950, by rfl⟩ : syracuseStep 2069267 = 3103901) B3103901
theorem B4655861 : Blo 2067435 4655861 := bbase (se 5 (by rfl) ⟨218243, by rfl⟩ : syracuseStep 4655861 = 436487) (by norm_num)
theorem B3103907 : Blo 2067435 3103907 := bstep (se 1 (by rfl) ⟨2327930, by rfl⟩ : syracuseStep 3103907 = 4655861) B4655861
theorem B2069271 : Blo 2067435 2069271 := bstep (se 1 (by rfl) ⟨1551953, by rfl⟩ : syracuseStep 2069271 = 3103907) B3103907
theorem B2359697 : Blo 2067435 2359697 := bbase (se 2 (by rfl) ⟨884886, by rfl⟩ : syracuseStep 2359697 = 1769773) (by norm_num)
theorem B25170101 : Blo 2067435 25170101 := bstep (se 5 (by rfl) ⟨1179848, by rfl⟩ : syracuseStep 25170101 = 2359697) B2359697
theorem B16780067 : Blo 2067435 16780067 := bstep (se 1 (by rfl) ⟨12585050, by rfl⟩ : syracuseStep 16780067 = 25170101) B25170101
theorem B11186711 : Blo 2067435 11186711 := bstep (se 1 (by rfl) ⟨8390033, by rfl⟩ : syracuseStep 11186711 = 16780067) B16780067
theorem B7457807 : Blo 2067435 7457807 := bstep (se 1 (by rfl) ⟨5593355, by rfl⟩ : syracuseStep 7457807 = 11186711) B11186711
theorem B4971871 : Blo 2067435 4971871 := bstep (se 1 (by rfl) ⟨3728903, by rfl⟩ : syracuseStep 4971871 = 7457807) B7457807
theorem B26516645 : Blo 2067435 26516645 := bstep (se 4 (by rfl) ⟨2485935, by rfl⟩ : syracuseStep 26516645 = 4971871) B4971871
theorem B17677763 : Blo 2067435 17677763 := bstep (se 1 (by rfl) ⟨13258322, by rfl⟩ : syracuseStep 17677763 = 26516645) B26516645
theorem B11785175 : Blo 2067435 11785175 := bstep (se 1 (by rfl) ⟨8838881, by rfl⟩ : syracuseStep 11785175 = 17677763) B17677763
theorem B7856783 : Blo 2067435 7856783 := bstep (se 1 (by rfl) ⟨5892587, by rfl⟩ : syracuseStep 7856783 = 11785175) B11785175
theorem B5237855 : Blo 2067435 5237855 := bstep (se 1 (by rfl) ⟨3928391, by rfl⟩ : syracuseStep 5237855 = 7856783) B7856783
theorem B3491903 : Blo 2067435 3491903 := bstep (se 1 (by rfl) ⟨2618927, by rfl⟩ : syracuseStep 3491903 = 5237855) B5237855
theorem B2327935 : Blo 2067435 2327935 := bstep (se 1 (by rfl) ⟨1745951, by rfl⟩ : syracuseStep 2327935 = 3491903) B3491903
theorem B3103913 : Blo 2067435 3103913 := bstep (se 2 (by rfl) ⟨1163967, by rfl⟩ : syracuseStep 3103913 = 2327935) B2327935
theorem B2069275 : Blo 2067435 2069275 := bstep (se 1 (by rfl) ⟨1551956, by rfl⟩ : syracuseStep 2069275 = 3103913) B3103913
theorem B12585077 : Blo 2067435 12585077 := bbase (se 5 (by rfl) ⟨589925, by rfl⟩ : syracuseStep 12585077 = 1179851) (by norm_num)
theorem B8390051 : Blo 2067435 8390051 := bstep (se 1 (by rfl) ⟨6292538, by rfl⟩ : syracuseStep 8390051 = 12585077) B12585077
theorem B5593367 : Blo 2067435 5593367 := bstep (se 1 (by rfl) ⟨4195025, by rfl⟩ : syracuseStep 5593367 = 8390051) B8390051
theorem B3728911 : Blo 2067435 3728911 := bstep (se 1 (by rfl) ⟨2796683, by rfl⟩ : syracuseStep 3728911 = 5593367) B5593367
theorem B4971881 : Blo 2067435 4971881 := bstep (se 2 (by rfl) ⟨1864455, by rfl⟩ : syracuseStep 4971881 = 3728911) B3728911
theorem B3314587 : Blo 2067435 3314587 := bstep (se 1 (by rfl) ⟨2485940, by rfl⟩ : syracuseStep 3314587 = 4971881) B4971881
theorem B4419449 : Blo 2067435 4419449 := bstep (se 2 (by rfl) ⟨1657293, by rfl⟩ : syracuseStep 4419449 = 3314587) B3314587
theorem B2946299 : Blo 2067435 2946299 := bstep (se 1 (by rfl) ⟨2209724, by rfl⟩ : syracuseStep 2946299 = 4419449) B4419449
theorem B7856797 : Blo 2067435 7856797 := bstep (se 3 (by rfl) ⟨1473149, by rfl⟩ : syracuseStep 7856797 = 2946299) B2946299
theorem B10475729 : Blo 2067435 10475729 := bstep (se 2 (by rfl) ⟨3928398, by rfl⟩ : syracuseStep 10475729 = 7856797) B7856797
theorem B6983819 : Blo 2067435 6983819 := bstep (se 1 (by rfl) ⟨5237864, by rfl⟩ : syracuseStep 6983819 = 10475729) B10475729
theorem B4655879 : Blo 2067435 4655879 := bstep (se 1 (by rfl) ⟨3491909, by rfl⟩ : syracuseStep 4655879 = 6983819) B6983819
theorem B3103919 : Blo 2067435 3103919 := bstep (se 1 (by rfl) ⟨2327939, by rfl⟩ : syracuseStep 3103919 = 4655879) B4655879
theorem B2069279 : Blo 2067435 2069279 := bstep (se 1 (by rfl) ⟨1551959, by rfl⟩ : syracuseStep 2069279 = 3103919) B3103919
theorem B3103925 : Blo 2067435 3103925 := bbase (se 5 (by rfl) ⟨145496, by rfl⟩ : syracuseStep 3103925 = 290993) (by norm_num)
theorem B2069283 : Blo 2067435 2069283 := bstep (se 1 (by rfl) ⟨1551962, by rfl⟩ : syracuseStep 2069283 = 3103925) B3103925
theorem B5237885 : Blo 2067435 5237885 := bbase (se 3 (by rfl) ⟨982103, by rfl⟩ : syracuseStep 5237885 = 1964207) (by norm_num)
theorem B3491923 : Blo 2067435 3491923 := bstep (se 1 (by rfl) ⟨2618942, by rfl⟩ : syracuseStep 3491923 = 5237885) B5237885
theorem B4655897 : Blo 2067435 4655897 := bstep (se 2 (by rfl) ⟨1745961, by rfl⟩ : syracuseStep 4655897 = 3491923) B3491923
theorem B3103931 : Blo 2067435 3103931 := bstep (se 1 (by rfl) ⟨2327948, by rfl⟩ : syracuseStep 3103931 = 4655897) B4655897
theorem B2069287 : Blo 2067435 2069287 := bstep (se 1 (by rfl) ⟨1551965, by rfl⟩ : syracuseStep 2069287 = 3103931) B3103931
theorem B2327953 : Blo 2067435 2327953 := bbase (se 2 (by rfl) ⟨872982, by rfl⟩ : syracuseStep 2327953 = 1745965) (by norm_num)
theorem B3103937 : Blo 2067435 3103937 := bstep (se 2 (by rfl) ⟨1163976, by rfl⟩ : syracuseStep 3103937 = 2327953) B2327953
theorem B2069291 : Blo 2067435 2069291 := bstep (se 1 (by rfl) ⟨1551968, by rfl⟩ : syracuseStep 2069291 = 3103937) B3103937
theorem B3928429 : Blo 2067435 3928429 := bbase (se 3 (by rfl) ⟨736580, by rfl⟩ : syracuseStep 3928429 = 1473161) (by norm_num)
theorem B5237905 : Blo 2067435 5237905 := bstep (se 2 (by rfl) ⟨1964214, by rfl⟩ : syracuseStep 5237905 = 3928429) B3928429
theorem B6983873 : Blo 2067435 6983873 := bstep (se 2 (by rfl) ⟨2618952, by rfl⟩ : syracuseStep 6983873 = 5237905) B5237905
theorem B4655915 : Blo 2067435 4655915 := bstep (se 1 (by rfl) ⟨3491936, by rfl⟩ : syracuseStep 4655915 = 6983873) B6983873
theorem B3103943 : Blo 2067435 3103943 := bstep (se 1 (by rfl) ⟨2327957, by rfl⟩ : syracuseStep 3103943 = 4655915) B4655915
theorem B2069295 : Blo 2067435 2069295 := bstep (se 1 (by rfl) ⟨1551971, by rfl⟩ : syracuseStep 2069295 = 3103943) B3103943
theorem B3103949 : Blo 2067435 3103949 := bbase (se 3 (by rfl) ⟨581990, by rfl⟩ : syracuseStep 3103949 = 1163981) (by norm_num)
theorem B2069299 : Blo 2067435 2069299 := bstep (se 1 (by rfl) ⟨1551974, by rfl⟩ : syracuseStep 2069299 = 3103949) B3103949
theorem B4655933 : Blo 2067435 4655933 := bbase (se 3 (by rfl) ⟨872987, by rfl⟩ : syracuseStep 4655933 = 1745975) (by norm_num)
theorem B3103955 : Blo 2067435 3103955 := bstep (se 1 (by rfl) ⟨2327966, by rfl⟩ : syracuseStep 3103955 = 4655933) B4655933
theorem B2069303 : Blo 2067435 2069303 := bstep (se 1 (by rfl) ⟨1551977, by rfl⟩ : syracuseStep 2069303 = 3103955) B3103955
theorem B3491957 : Blo 2067435 3491957 := bbase (se 5 (by rfl) ⟨163685, by rfl⟩ : syracuseStep 3491957 = 327371) (by norm_num)
theorem B2327971 : Blo 2067435 2327971 := bstep (se 1 (by rfl) ⟨1745978, by rfl⟩ : syracuseStep 2327971 = 3491957) B3491957
theorem B3103961 : Blo 2067435 3103961 := bstep (se 2 (by rfl) ⟨1163985, by rfl⟩ : syracuseStep 3103961 = 2327971) B2327971
theorem B2069307 : Blo 2067435 2069307 := bstep (se 1 (by rfl) ⟨1551980, by rfl⟩ : syracuseStep 2069307 = 3103961) B3103961
theorem B4419517 : Blo 2067435 4419517 := bbase (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) (by norm_num)
theorem B5892689 : Blo 2067435 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B15713837 : Blo 2067435 15713837 := bstep (se 3 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 15713837 = 5892689) B5892689
theorem B10475891 : Blo 2067435 10475891 := bstep (se 1 (by rfl) ⟨7856918, by rfl⟩ : syracuseStep 10475891 = 15713837) B15713837
theorem B6983927 : Blo 2067435 6983927 := bstep (se 1 (by rfl) ⟨5237945, by rfl⟩ : syracuseStep 6983927 = 10475891) B10475891
theorem B4655951 : Blo 2067435 4655951 := bstep (se 1 (by rfl) ⟨3491963, by rfl⟩ : syracuseStep 4655951 = 6983927) B6983927
theorem B3103967 : Blo 2067435 3103967 := bstep (se 1 (by rfl) ⟨2327975, by rfl⟩ : syracuseStep 3103967 = 4655951) B4655951
theorem B2069311 : Blo 2067435 2069311 := bstep (se 1 (by rfl) ⟨1551983, by rfl⟩ : syracuseStep 2069311 = 3103967) B3103967
theorem B3103973 : Blo 2067435 3103973 := bbase (se 4 (by rfl) ⟨290997, by rfl⟩ : syracuseStep 3103973 = 581995) (by norm_num)
theorem B2069315 : Blo 2067435 2069315 := bstep (se 1 (by rfl) ⟨1551986, by rfl⟩ : syracuseStep 2069315 = 3103973) B3103973
theorem B8390213 : Blo 2067435 8390213 := bbase (se 4 (by rfl) ⟨786582, by rfl⟩ : syracuseStep 8390213 = 1573165) (by norm_num)
theorem B5593475 : Blo 2067435 5593475 := bstep (se 1 (by rfl) ⟨4195106, by rfl⟩ : syracuseStep 5593475 = 8390213) B8390213
theorem B14915933 : Blo 2067435 14915933 := bstep (se 3 (by rfl) ⟨2796737, by rfl⟩ : syracuseStep 14915933 = 5593475) B5593475
theorem B9943955 : Blo 2067435 9943955 := bstep (se 1 (by rfl) ⟨7457966, by rfl⟩ : syracuseStep 9943955 = 14915933) B14915933
theorem B6629303 : Blo 2067435 6629303 := bstep (se 1 (by rfl) ⟨4971977, by rfl⟩ : syracuseStep 6629303 = 9943955) B9943955
theorem B4419535 : Blo 2067435 4419535 := bstep (se 1 (by rfl) ⟨3314651, by rfl⟩ : syracuseStep 4419535 = 6629303) B6629303
theorem B5892713 : Blo 2067435 5892713 := bstep (se 2 (by rfl) ⟨2209767, by rfl⟩ : syracuseStep 5892713 = 4419535) B4419535
theorem B3928475 : Blo 2067435 3928475 := bstep (se 1 (by rfl) ⟨2946356, by rfl⟩ : syracuseStep 3928475 = 5892713) B5892713
theorem B2618983 : Blo 2067435 2618983 := bstep (se 1 (by rfl) ⟨1964237, by rfl⟩ : syracuseStep 2618983 = 3928475) B3928475
theorem B3491977 : Blo 2067435 3491977 := bstep (se 2 (by rfl) ⟨1309491, by rfl⟩ : syracuseStep 3491977 = 2618983) B2618983
theorem B4655969 : Blo 2067435 4655969 := bstep (se 2 (by rfl) ⟨1745988, by rfl⟩ : syracuseStep 4655969 = 3491977) B3491977
theorem B3103979 : Blo 2067435 3103979 := bstep (se 1 (by rfl) ⟨2327984, by rfl⟩ : syracuseStep 3103979 = 4655969) B4655969
theorem B2069319 : Blo 2067435 2069319 := bstep (se 1 (by rfl) ⟨1551989, by rfl⟩ : syracuseStep 2069319 = 3103979) B3103979
theorem B2327989 : Blo 2067435 2327989 := bbase (se 5 (by rfl) ⟨109124, by rfl⟩ : syracuseStep 2327989 = 218249) (by norm_num)
theorem B3103985 : Blo 2067435 3103985 := bstep (se 2 (by rfl) ⟨1163994, by rfl⟩ : syracuseStep 3103985 = 2327989) B2327989
theorem B2069323 : Blo 2067435 2069323 := bstep (se 1 (by rfl) ⟨1551992, by rfl⟩ : syracuseStep 2069323 = 3103985) B3103985
theorem B2618993 : Blo 2067435 2618993 := bbase (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) (by norm_num)
theorem B6983981 : Blo 2067435 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B4655987 : Blo 2067435 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B3103991 : Blo 2067435 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B2069327 : Blo 2067435 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B3103997 : Blo 2067435 3103997 := bbase (se 3 (by rfl) ⟨581999, by rfl⟩ : syracuseStep 3103997 = 1163999) (by norm_num)
theorem B2069331 : Blo 2067435 2069331 := bstep (se 1 (by rfl) ⟨1551998, by rfl⟩ : syracuseStep 2069331 = 3103997) B3103997
theorem B4656005 : Blo 2067435 4656005 := bbase (se 4 (by rfl) ⟨436500, by rfl⟩ : syracuseStep 4656005 = 873001) (by norm_num)
theorem B3104003 : Blo 2067435 3104003 := bstep (se 1 (by rfl) ⟨2328002, by rfl⟩ : syracuseStep 3104003 = 4656005) B4656005
theorem B2069335 : Blo 2067435 2069335 := bstep (se 1 (by rfl) ⟨1552001, by rfl⟩ : syracuseStep 2069335 = 3104003) B3104003
theorem B2209789 : Blo 2067435 2209789 := bbase (se 3 (by rfl) ⟨414335, by rfl⟩ : syracuseStep 2209789 = 828671) (by norm_num)
theorem B2946385 : Blo 2067435 2946385 := bstep (se 2 (by rfl) ⟨1104894, by rfl⟩ : syracuseStep 2946385 = 2209789) B2209789
theorem B3928513 : Blo 2067435 3928513 := bstep (se 2 (by rfl) ⟨1473192, by rfl⟩ : syracuseStep 3928513 = 2946385) B2946385
theorem B5238017 : Blo 2067435 5238017 := bstep (se 2 (by rfl) ⟨1964256, by rfl⟩ : syracuseStep 5238017 = 3928513) B3928513
theorem B3492011 : Blo 2067435 3492011 := bstep (se 1 (by rfl) ⟨2619008, by rfl⟩ : syracuseStep 3492011 = 5238017) B5238017
theorem B2328007 : Blo 2067435 2328007 := bstep (se 1 (by rfl) ⟨1746005, by rfl⟩ : syracuseStep 2328007 = 3492011) B3492011
theorem B3104009 : Blo 2067435 3104009 := bstep (se 2 (by rfl) ⟨1164003, by rfl⟩ : syracuseStep 3104009 = 2328007) B2328007
theorem B2069339 : Blo 2067435 2069339 := bstep (se 1 (by rfl) ⟨1552004, by rfl⟩ : syracuseStep 2069339 = 3104009) B3104009
theorem B10476053 : Blo 2067435 10476053 := bbase (se 6 (by rfl) ⟨245532, by rfl⟩ : syracuseStep 10476053 = 491065) (by norm_num)
theorem B6984035 : Blo 2067435 6984035 := bstep (se 1 (by rfl) ⟨5238026, by rfl⟩ : syracuseStep 6984035 = 10476053) B10476053
theorem B4656023 : Blo 2067435 4656023 := bstep (se 1 (by rfl) ⟨3492017, by rfl⟩ : syracuseStep 4656023 = 6984035) B6984035
theorem B3104015 : Blo 2067435 3104015 := bstep (se 1 (by rfl) ⟨2328011, by rfl⟩ : syracuseStep 3104015 = 4656023) B4656023
theorem B2069343 : Blo 2067435 2069343 := bstep (se 1 (by rfl) ⟨1552007, by rfl⟩ : syracuseStep 2069343 = 3104015) B3104015
theorem B3104021 : Blo 2067435 3104021 := bbase (se 6 (by rfl) ⟨72750, by rfl⟩ : syracuseStep 3104021 = 145501) (by norm_num)
theorem B2069347 : Blo 2067435 2069347 := bstep (se 1 (by rfl) ⟨1552010, by rfl⟩ : syracuseStep 2069347 = 3104021) B3104021
theorem B19888213 : Blo 2067435 19888213 := bbase (se 8 (by rfl) ⟨116532, by rfl⟩ : syracuseStep 19888213 = 233065) (by norm_num)
theorem B26517617 : Blo 2067435 26517617 := bstep (se 2 (by rfl) ⟨9944106, by rfl⟩ : syracuseStep 26517617 = 19888213) B19888213
theorem B17678411 : Blo 2067435 17678411 := bstep (se 1 (by rfl) ⟨13258808, by rfl⟩ : syracuseStep 17678411 = 26517617) B26517617
theorem B11785607 : Blo 2067435 11785607 := bstep (se 1 (by rfl) ⟨8839205, by rfl⟩ : syracuseStep 11785607 = 17678411) B17678411
theorem B7857071 : Blo 2067435 7857071 := bstep (se 1 (by rfl) ⟨5892803, by rfl⟩ : syracuseStep 7857071 = 11785607) B11785607
theorem B5238047 : Blo 2067435 5238047 := bstep (se 1 (by rfl) ⟨3928535, by rfl⟩ : syracuseStep 5238047 = 7857071) B7857071
theorem B3492031 : Blo 2067435 3492031 := bstep (se 1 (by rfl) ⟨2619023, by rfl⟩ : syracuseStep 3492031 = 5238047) B5238047
theorem B4656041 : Blo 2067435 4656041 := bstep (se 2 (by rfl) ⟨1746015, by rfl⟩ : syracuseStep 4656041 = 3492031) B3492031
theorem B3104027 : Blo 2067435 3104027 := bstep (se 1 (by rfl) ⟨2328020, by rfl⟩ : syracuseStep 3104027 = 4656041) B4656041
theorem B2069351 : Blo 2067435 2069351 := bstep (se 1 (by rfl) ⟨1552013, by rfl⟩ : syracuseStep 2069351 = 3104027) B3104027
theorem B2328025 : Blo 2067435 2328025 := bbase (se 2 (by rfl) ⟨873009, by rfl⟩ : syracuseStep 2328025 = 1746019) (by norm_num)
theorem B3104033 : Blo 2067435 3104033 := bstep (se 2 (by rfl) ⟨1164012, by rfl⟩ : syracuseStep 3104033 = 2328025) B2328025
theorem B2069355 : Blo 2067435 2069355 := bstep (se 1 (by rfl) ⟨1552016, by rfl⟩ : syracuseStep 2069355 = 3104033) B3104033
theorem B2946413 : Blo 2067435 2946413 := bbase (se 3 (by rfl) ⟨552452, by rfl⟩ : syracuseStep 2946413 = 1104905) (by norm_num)
theorem B7857101 : Blo 2067435 7857101 := bstep (se 3 (by rfl) ⟨1473206, by rfl⟩ : syracuseStep 7857101 = 2946413) B2946413
theorem B5238067 : Blo 2067435 5238067 := bstep (se 1 (by rfl) ⟨3928550, by rfl⟩ : syracuseStep 5238067 = 7857101) B7857101
theorem B6984089 : Blo 2067435 6984089 := bstep (se 2 (by rfl) ⟨2619033, by rfl⟩ : syracuseStep 6984089 = 5238067) B5238067
theorem B4656059 : Blo 2067435 4656059 := bstep (se 1 (by rfl) ⟨3492044, by rfl⟩ : syracuseStep 4656059 = 6984089) B6984089
theorem B3104039 : Blo 2067435 3104039 := bstep (se 1 (by rfl) ⟨2328029, by rfl⟩ : syracuseStep 3104039 = 4656059) B4656059
theorem B2069359 : Blo 2067435 2069359 := bstep (se 1 (by rfl) ⟨1552019, by rfl⟩ : syracuseStep 2069359 = 3104039) B3104039
theorem B3104045 : Blo 2067435 3104045 := bbase (se 3 (by rfl) ⟨582008, by rfl⟩ : syracuseStep 3104045 = 1164017) (by norm_num)
theorem B2069363 : Blo 2067435 2069363 := bstep (se 1 (by rfl) ⟨1552022, by rfl⟩ : syracuseStep 2069363 = 3104045) B3104045
theorem B4656077 : Blo 2067435 4656077 := bbase (se 3 (by rfl) ⟨873014, by rfl⟩ : syracuseStep 4656077 = 1746029) (by norm_num)
theorem B3104051 : Blo 2067435 3104051 := bstep (se 1 (by rfl) ⟨2328038, by rfl⟩ : syracuseStep 3104051 = 4656077) B4656077
theorem B2069367 : Blo 2067435 2069367 := bstep (se 1 (by rfl) ⟨1552025, by rfl⟩ : syracuseStep 2069367 = 3104051) B3104051
theorem B2619049 : Blo 2067435 2619049 := bbase (se 2 (by rfl) ⟨982143, by rfl⟩ : syracuseStep 2619049 = 1964287) (by norm_num)
theorem B3492065 : Blo 2067435 3492065 := bstep (se 2 (by rfl) ⟨1309524, by rfl⟩ : syracuseStep 3492065 = 2619049) B2619049
theorem B2328043 : Blo 2067435 2328043 := bstep (se 1 (by rfl) ⟨1746032, by rfl⟩ : syracuseStep 2328043 = 3492065) B3492065
theorem B3104057 : Blo 2067435 3104057 := bstep (se 2 (by rfl) ⟨1164021, by rfl⟩ : syracuseStep 3104057 = 2328043) B2328043
theorem B2069371 : Blo 2067435 2069371 := bstep (se 1 (by rfl) ⟨1552028, by rfl⟩ : syracuseStep 2069371 = 3104057) B3104057
theorem B3539717 : Blo 2067435 3539717 := bbase (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) (by norm_num)
theorem B2359811 : Blo 2067435 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B6292829 : Blo 2067435 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B4195219 : Blo 2067435 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B5593625 : Blo 2067435 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B3729083 : Blo 2067435 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B9944221 : Blo 2067435 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B13258961 : Blo 2067435 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B8839307 : Blo 2067435 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B23571485 : Blo 2067435 23571485 := bstep (se 3 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 23571485 = 8839307) B8839307
theorem B15714323 : Blo 2067435 15714323 := bstep (se 1 (by rfl) ⟨11785742, by rfl⟩ : syracuseStep 15714323 = 23571485) B23571485
theorem B10476215 : Blo 2067435 10476215 := bstep (se 1 (by rfl) ⟨7857161, by rfl⟩ : syracuseStep 10476215 = 15714323) B15714323
theorem B6984143 : Blo 2067435 6984143 := bstep (se 1 (by rfl) ⟨5238107, by rfl⟩ : syracuseStep 6984143 = 10476215) B10476215
theorem B4656095 : Blo 2067435 4656095 := bstep (se 1 (by rfl) ⟨3492071, by rfl⟩ : syracuseStep 4656095 = 6984143) B6984143
theorem B3104063 : Blo 2067435 3104063 := bstep (se 1 (by rfl) ⟨2328047, by rfl⟩ : syracuseStep 3104063 = 4656095) B4656095
theorem B2069375 : Blo 2067435 2069375 := bstep (se 1 (by rfl) ⟨1552031, by rfl⟩ : syracuseStep 2069375 = 3104063) B3104063
theorem B3104069 : Blo 2067435 3104069 := bbase (se 4 (by rfl) ⟨291006, by rfl⟩ : syracuseStep 3104069 = 582013) (by norm_num)
theorem B2069379 : Blo 2067435 2069379 := bstep (se 1 (by rfl) ⟨1552034, by rfl⟩ : syracuseStep 2069379 = 3104069) B3104069
theorem B3492085 : Blo 2067435 3492085 := bbase (se 5 (by rfl) ⟨163691, by rfl⟩ : syracuseStep 3492085 = 327383) (by norm_num)
theorem B4656113 : Blo 2067435 4656113 := bstep (se 2 (by rfl) ⟨1746042, by rfl⟩ : syracuseStep 4656113 = 3492085) B3492085
theorem B3104075 : Blo 2067435 3104075 := bstep (se 1 (by rfl) ⟨2328056, by rfl⟩ : syracuseStep 3104075 = 4656113) B4656113
theorem B2069383 : Blo 2067435 2069383 := bstep (se 1 (by rfl) ⟨1552037, by rfl⟩ : syracuseStep 2069383 = 3104075) B3104075
theorem B2328061 : Blo 2067435 2328061 := bbase (se 3 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 2328061 = 873023) (by norm_num)
theorem B3104081 : Blo 2067435 3104081 := bstep (se 2 (by rfl) ⟨1164030, by rfl⟩ : syracuseStep 3104081 = 2328061) B2328061
theorem B2069387 : Blo 2067435 2069387 := bstep (se 1 (by rfl) ⟨1552040, by rfl⟩ : syracuseStep 2069387 = 3104081) B3104081
theorem B6984197 : Blo 2067435 6984197 := bbase (se 4 (by rfl) ⟨654768, by rfl⟩ : syracuseStep 6984197 = 1309537) (by norm_num)
theorem B4656131 : Blo 2067435 4656131 := bstep (se 1 (by rfl) ⟨3492098, by rfl⟩ : syracuseStep 4656131 = 6984197) B6984197
theorem B3104087 : Blo 2067435 3104087 := bstep (se 1 (by rfl) ⟨2328065, by rfl⟩ : syracuseStep 3104087 = 4656131) B4656131
theorem B2069391 : Blo 2067435 2069391 := bstep (se 1 (by rfl) ⟨1552043, by rfl⟩ : syracuseStep 2069391 = 3104087) B3104087
theorem B3104093 : Blo 2067435 3104093 := bbase (se 3 (by rfl) ⟨582017, by rfl⟩ : syracuseStep 3104093 = 1164035) (by norm_num)
theorem B2069395 : Blo 2067435 2069395 := bstep (se 1 (by rfl) ⟨1552046, by rfl⟩ : syracuseStep 2069395 = 3104093) B3104093
theorem B4656149 : Blo 2067435 4656149 := bbase (se 6 (by rfl) ⟨109128, by rfl⟩ : syracuseStep 4656149 = 218257) (by norm_num)
theorem B3104099 : Blo 2067435 3104099 := bstep (se 1 (by rfl) ⟨2328074, by rfl⟩ : syracuseStep 3104099 = 4656149) B4656149
theorem B2069399 : Blo 2067435 2069399 := bstep (se 1 (by rfl) ⟨1552049, by rfl⟩ : syracuseStep 2069399 = 3104099) B3104099
theorem B7857269 : Blo 2067435 7857269 := bbase (se 5 (by rfl) ⟨368309, by rfl⟩ : syracuseStep 7857269 = 736619) (by norm_num)
theorem B5238179 : Blo 2067435 5238179 := bstep (se 1 (by rfl) ⟨3928634, by rfl⟩ : syracuseStep 5238179 = 7857269) B7857269
theorem B3492119 : Blo 2067435 3492119 := bstep (se 1 (by rfl) ⟨2619089, by rfl⟩ : syracuseStep 3492119 = 5238179) B5238179
theorem B2328079 : Blo 2067435 2328079 := bstep (se 1 (by rfl) ⟨1746059, by rfl⟩ : syracuseStep 2328079 = 3492119) B3492119
theorem B3104105 : Blo 2067435 3104105 := bstep (se 2 (by rfl) ⟨1164039, by rfl⟩ : syracuseStep 3104105 = 2328079) B2328079
theorem B2069403 : Blo 2067435 2069403 := bstep (se 1 (by rfl) ⟨1552052, by rfl⟩ : syracuseStep 2069403 = 3104105) B3104105
theorem B2209861 : Blo 2067435 2209861 := bbase (se 4 (by rfl) ⟨207174, by rfl⟩ : syracuseStep 2209861 = 414349) (by norm_num)
theorem B11785925 : Blo 2067435 11785925 := bstep (se 4 (by rfl) ⟨1104930, by rfl⟩ : syracuseStep 11785925 = 2209861) B2209861
theorem B7857283 : Blo 2067435 7857283 := bstep (se 1 (by rfl) ⟨5892962, by rfl⟩ : syracuseStep 7857283 = 11785925) B11785925
theorem B10476377 : Blo 2067435 10476377 := bstep (se 2 (by rfl) ⟨3928641, by rfl⟩ : syracuseStep 10476377 = 7857283) B7857283
theorem B6984251 : Blo 2067435 6984251 := bstep (se 1 (by rfl) ⟨5238188, by rfl⟩ : syracuseStep 6984251 = 10476377) B10476377
theorem B4656167 : Blo 2067435 4656167 := bstep (se 1 (by rfl) ⟨3492125, by rfl⟩ : syracuseStep 4656167 = 6984251) B6984251
theorem B3104111 : Blo 2067435 3104111 := bstep (se 1 (by rfl) ⟨2328083, by rfl⟩ : syracuseStep 3104111 = 4656167) B4656167
theorem B2069407 : Blo 2067435 2069407 := bstep (se 1 (by rfl) ⟨1552055, by rfl⟩ : syracuseStep 2069407 = 3104111) B3104111
theorem B3104117 : Blo 2067435 3104117 := bbase (se 5 (by rfl) ⟨145505, by rfl⟩ : syracuseStep 3104117 = 291011) (by norm_num)
theorem B2069411 : Blo 2067435 2069411 := bstep (se 1 (by rfl) ⟨1552058, by rfl⟩ : syracuseStep 2069411 = 3104117) B3104117
theorem B2946493 : Blo 2067435 2946493 := bbase (se 3 (by rfl) ⟨552467, by rfl⟩ : syracuseStep 2946493 = 1104935) (by norm_num)
theorem B3928657 : Blo 2067435 3928657 := bstep (se 2 (by rfl) ⟨1473246, by rfl⟩ : syracuseStep 3928657 = 2946493) B2946493
theorem B5238209 : Blo 2067435 5238209 := bstep (se 2 (by rfl) ⟨1964328, by rfl⟩ : syracuseStep 5238209 = 3928657) B3928657
theorem B3492139 : Blo 2067435 3492139 := bstep (se 1 (by rfl) ⟨2619104, by rfl⟩ : syracuseStep 3492139 = 5238209) B5238209
theorem B4656185 : Blo 2067435 4656185 := bstep (se 2 (by rfl) ⟨1746069, by rfl⟩ : syracuseStep 4656185 = 3492139) B3492139
theorem B3104123 : Blo 2067435 3104123 := bstep (se 1 (by rfl) ⟨2328092, by rfl⟩ : syracuseStep 3104123 = 4656185) B4656185
theorem B2069415 : Blo 2067435 2069415 := bstep (se 1 (by rfl) ⟨1552061, by rfl⟩ : syracuseStep 2069415 = 3104123) B3104123
theorem B2328097 : Blo 2067435 2328097 := bbase (se 2 (by rfl) ⟨873036, by rfl⟩ : syracuseStep 2328097 = 1746073) (by norm_num)
theorem B3104129 : Blo 2067435 3104129 := bstep (se 2 (by rfl) ⟨1164048, by rfl⟩ : syracuseStep 3104129 = 2328097) B2328097
theorem B2069419 : Blo 2067435 2069419 := bstep (se 1 (by rfl) ⟨1552064, by rfl⟩ : syracuseStep 2069419 = 3104129) B3104129
theorem B5238229 : Blo 2067435 5238229 := bbase (se 7 (by rfl) ⟨61385, by rfl⟩ : syracuseStep 5238229 = 122771) (by norm_num)
theorem B6984305 : Blo 2067435 6984305 := bstep (se 2 (by rfl) ⟨2619114, by rfl⟩ : syracuseStep 6984305 = 5238229) B5238229
theorem B4656203 : Blo 2067435 4656203 := bstep (se 1 (by rfl) ⟨3492152, by rfl⟩ : syracuseStep 4656203 = 6984305) B6984305
theorem B3104135 : Blo 2067435 3104135 := bstep (se 1 (by rfl) ⟨2328101, by rfl⟩ : syracuseStep 3104135 = 4656203) B4656203
theorem B2069423 : Blo 2067435 2069423 := bstep (se 1 (by rfl) ⟨1552067, by rfl⟩ : syracuseStep 2069423 = 3104135) B3104135
theorem B3104141 : Blo 2067435 3104141 := bbase (se 3 (by rfl) ⟨582026, by rfl⟩ : syracuseStep 3104141 = 1164053) (by norm_num)
theorem B2069427 : Blo 2067435 2069427 := bstep (se 1 (by rfl) ⟨1552070, by rfl⟩ : syracuseStep 2069427 = 3104141) B3104141
theorem B4656221 : Blo 2067435 4656221 := bbase (se 3 (by rfl) ⟨873041, by rfl⟩ : syracuseStep 4656221 = 1746083) (by norm_num)
theorem B3104147 : Blo 2067435 3104147 := bstep (se 1 (by rfl) ⟨2328110, by rfl⟩ : syracuseStep 3104147 = 4656221) B4656221
theorem B2069431 : Blo 2067435 2069431 := bstep (se 1 (by rfl) ⟨1552073, by rfl⟩ : syracuseStep 2069431 = 3104147) B3104147
theorem B3492173 : Blo 2067435 3492173 := bbase (se 3 (by rfl) ⟨654782, by rfl⟩ : syracuseStep 3492173 = 1309565) (by norm_num)
theorem B2328115 : Blo 2067435 2328115 := bstep (se 1 (by rfl) ⟨1746086, by rfl⟩ : syracuseStep 2328115 = 3492173) B3492173
theorem B3104153 : Blo 2067435 3104153 := bstep (se 2 (by rfl) ⟨1164057, by rfl⟩ : syracuseStep 3104153 = 2328115) B2328115
theorem B2069435 : Blo 2067435 2069435 := bstep (se 1 (by rfl) ⟨1552076, by rfl⟩ : syracuseStep 2069435 = 3104153) B3104153
theorem C0 (j : ℕ) (h1 : 516858 ≤ j) (h2 : j ≤ 517358) : Blo 2067435 (4 * j + 3) := by
  interval_cases j
  · exact B2067435
  · exact B2067439
  · exact B2067443
  · exact B2067447
  · exact B2067451
  · exact B2067455
  · exact B2067459
  · exact B2067463
  · exact B2067467
  · exact B2067471
  · exact B2067475
  · exact B2067479
  · exact B2067483
  · exact B2067487
  · exact B2067491
  · exact B2067495
  · exact B2067499
  · exact B2067503
  · exact B2067507
  · exact B2067511
  · exact B2067515
  · exact B2067519
  · exact B2067523
  · exact B2067527
  · exact B2067531
  · exact B2067535
  · exact B2067539
  · exact B2067543
  · exact B2067547
  · exact B2067551
  · exact B2067555
  · exact B2067559
  · exact B2067563
  · exact B2067567
  · exact B2067571
  · exact B2067575
  · exact B2067579
  · exact B2067583
  · exact B2067587
  · exact B2067591
  · exact B2067595
  · exact B2067599
  · exact B2067603
  · exact B2067607
  · exact B2067611
  · exact B2067615
  · exact B2067619
  · exact B2067623
  · exact B2067627
  · exact B2067631
  · exact B2067635
  · exact B2067639
  · exact B2067643
  · exact B2067647
  · exact B2067651
  · exact B2067655
  · exact B2067659
  · exact B2067663
  · exact B2067667
  · exact B2067671
  · exact B2067675
  · exact B2067679
  · exact B2067683
  · exact B2067687
  · exact B2067691
  · exact B2067695
  · exact B2067699
  · exact B2067703
  · exact B2067707
  · exact B2067711
  · exact B2067715
  · exact B2067719
  · exact B2067723
  · exact B2067727
  · exact B2067731
  · exact B2067735
  · exact B2067739
  · exact B2067743
  · exact B2067747
  · exact B2067751
  · exact B2067755
  · exact B2067759
  · exact B2067763
  · exact B2067767
  · exact B2067771
  · exact B2067775
  · exact B2067779
  · exact B2067783
  · exact B2067787
  · exact B2067791
  · exact B2067795
  · exact B2067799
  · exact B2067803
  · exact B2067807
  · exact B2067811
  · exact B2067815
  · exact B2067819
  · exact B2067823
  · exact B2067827
  · exact B2067831
  · exact B2067835
  · exact B2067839
  · exact B2067843
  · exact B2067847
  · exact B2067851
  · exact B2067855
  · exact B2067859
  · exact B2067863
  · exact B2067867
  · exact B2067871
  · exact B2067875
  · exact B2067879
  · exact B2067883
  · exact B2067887
  · exact B2067891
  · exact B2067895
  · exact B2067899
  · exact B2067903
  · exact B2067907
  · exact B2067911
  · exact B2067915
  · exact B2067919
  · exact B2067923
  · exact B2067927
  · exact B2067931
  · exact B2067935
  · exact B2067939
  · exact B2067943
  · exact B2067947
  · exact B2067951
  · exact B2067955
  · exact B2067959
  · exact B2067963
  · exact B2067967
  · exact B2067971
  · exact B2067975
  · exact B2067979
  · exact B2067983
  · exact B2067987
  · exact B2067991
  · exact B2067995
  · exact B2067999
  · exact B2068003
  · exact B2068007
  · exact B2068011
  · exact B2068015
  · exact B2068019
  · exact B2068023
  · exact B2068027
  · exact B2068031
  · exact B2068035
  · exact B2068039
  · exact B2068043
  · exact B2068047
  · exact B2068051
  · exact B2068055
  · exact B2068059
  · exact B2068063
  · exact B2068067
  · exact B2068071
  · exact B2068075
  · exact B2068079
  · exact B2068083
  · exact B2068087
  · exact B2068091
  · exact B2068095
  · exact B2068099
  · exact B2068103
  · exact B2068107
  · exact B2068111
  · exact B2068115
  · exact B2068119
  · exact B2068123
  · exact B2068127
  · exact B2068131
  · exact B2068135
  · exact B2068139
  · exact B2068143
  · exact B2068147
  · exact B2068151
  · exact B2068155
  · exact B2068159
  · exact B2068163
  · exact B2068167
  · exact B2068171
  · exact B2068175
  · exact B2068179
  · exact B2068183
  · exact B2068187
  · exact B2068191
  · exact B2068195
  · exact B2068199
  · exact B2068203
  · exact B2068207
  · exact B2068211
  · exact B2068215
  · exact B2068219
  · exact B2068223
  · exact B2068227
  · exact B2068231
  · exact B2068235
  · exact B2068239
  · exact B2068243
  · exact B2068247
  · exact B2068251
  · exact B2068255
  · exact B2068259
  · exact B2068263
  · exact B2068267
  · exact B2068271
  · exact B2068275
  · exact B2068279
  · exact B2068283
  · exact B2068287
  · exact B2068291
  · exact B2068295
  · exact B2068299
  · exact B2068303
  · exact B2068307
  · exact B2068311
  · exact B2068315
  · exact B2068319
  · exact B2068323
  · exact B2068327
  · exact B2068331
  · exact B2068335
  · exact B2068339
  · exact B2068343
  · exact B2068347
  · exact B2068351
  · exact B2068355
  · exact B2068359
  · exact B2068363
  · exact B2068367
  · exact B2068371
  · exact B2068375
  · exact B2068379
  · exact B2068383
  · exact B2068387
  · exact B2068391
  · exact B2068395
  · exact B2068399
  · exact B2068403
  · exact B2068407
  · exact B2068411
  · exact B2068415
  · exact B2068419
  · exact B2068423
  · exact B2068427
  · exact B2068431
  · exact B2068435
  · exact B2068439
  · exact B2068443
  · exact B2068447
  · exact B2068451
  · exact B2068455
  · exact B2068459
  · exact B2068463
  · exact B2068467
  · exact B2068471
  · exact B2068475
  · exact B2068479
  · exact B2068483
  · exact B2068487
  · exact B2068491
  · exact B2068495
  · exact B2068499
  · exact B2068503
  · exact B2068507
  · exact B2068511
  · exact B2068515
  · exact B2068519
  · exact B2068523
  · exact B2068527
  · exact B2068531
  · exact B2068535
  · exact B2068539
  · exact B2068543
  · exact B2068547
  · exact B2068551
  · exact B2068555
  · exact B2068559
  · exact B2068563
  · exact B2068567
  · exact B2068571
  · exact B2068575
  · exact B2068579
  · exact B2068583
  · exact B2068587
  · exact B2068591
  · exact B2068595
  · exact B2068599
  · exact B2068603
  · exact B2068607
  · exact B2068611
  · exact B2068615
  · exact B2068619
  · exact B2068623
  · exact B2068627
  · exact B2068631
  · exact B2068635
  · exact B2068639
  · exact B2068643
  · exact B2068647
  · exact B2068651
  · exact B2068655
  · exact B2068659
  · exact B2068663
  · exact B2068667
  · exact B2068671
  · exact B2068675
  · exact B2068679
  · exact B2068683
  · exact B2068687
  · exact B2068691
  · exact B2068695
  · exact B2068699
  · exact B2068703
  · exact B2068707
  · exact B2068711
  · exact B2068715
  · exact B2068719
  · exact B2068723
  · exact B2068727
  · exact B2068731
  · exact B2068735
  · exact B2068739
  · exact B2068743
  · exact B2068747
  · exact B2068751
  · exact B2068755
  · exact B2068759
  · exact B2068763
  · exact B2068767
  · exact B2068771
  · exact B2068775
  · exact B2068779
  · exact B2068783
  · exact B2068787
  · exact B2068791
  · exact B2068795
  · exact B2068799
  · exact B2068803
  · exact B2068807
  · exact B2068811
  · exact B2068815
  · exact B2068819
  · exact B2068823
  · exact B2068827
  · exact B2068831
  · exact B2068835
  · exact B2068839
  · exact B2068843
  · exact B2068847
  · exact B2068851
  · exact B2068855
  · exact B2068859
  · exact B2068863
  · exact B2068867
  · exact B2068871
  · exact B2068875
  · exact B2068879
  · exact B2068883
  · exact B2068887
  · exact B2068891
  · exact B2068895
  · exact B2068899
  · exact B2068903
  · exact B2068907
  · exact B2068911
  · exact B2068915
  · exact B2068919
  · exact B2068923
  · exact B2068927
  · exact B2068931
  · exact B2068935
  · exact B2068939
  · exact B2068943
  · exact B2068947
  · exact B2068951
  · exact B2068955
  · exact B2068959
  · exact B2068963
  · exact B2068967
  · exact B2068971
  · exact B2068975
  · exact B2068979
  · exact B2068983
  · exact B2068987
  · exact B2068991
  · exact B2068995
  · exact B2068999
  · exact B2069003
  · exact B2069007
  · exact B2069011
  · exact B2069015
  · exact B2069019
  · exact B2069023
  · exact B2069027
  · exact B2069031
  · exact B2069035
  · exact B2069039
  · exact B2069043
  · exact B2069047
  · exact B2069051
  · exact B2069055
  · exact B2069059
  · exact B2069063
  · exact B2069067
  · exact B2069071
  · exact B2069075
  · exact B2069079
  · exact B2069083
  · exact B2069087
  · exact B2069091
  · exact B2069095
  · exact B2069099
  · exact B2069103
  · exact B2069107
  · exact B2069111
  · exact B2069115
  · exact B2069119
  · exact B2069123
  · exact B2069127
  · exact B2069131
  · exact B2069135
  · exact B2069139
  · exact B2069143
  · exact B2069147
  · exact B2069151
  · exact B2069155
  · exact B2069159
  · exact B2069163
  · exact B2069167
  · exact B2069171
  · exact B2069175
  · exact B2069179
  · exact B2069183
  · exact B2069187
  · exact B2069191
  · exact B2069195
  · exact B2069199
  · exact B2069203
  · exact B2069207
  · exact B2069211
  · exact B2069215
  · exact B2069219
  · exact B2069223
  · exact B2069227
  · exact B2069231
  · exact B2069235
  · exact B2069239
  · exact B2069243
  · exact B2069247
  · exact B2069251
  · exact B2069255
  · exact B2069259
  · exact B2069263
  · exact B2069267
  · exact B2069271
  · exact B2069275
  · exact B2069279
  · exact B2069283
  · exact B2069287
  · exact B2069291
  · exact B2069295
  · exact B2069299
  · exact B2069303
  · exact B2069307
  · exact B2069311
  · exact B2069315
  · exact B2069319
  · exact B2069323
  · exact B2069327
  · exact B2069331
  · exact B2069335
  · exact B2069339
  · exact B2069343
  · exact B2069347
  · exact B2069351
  · exact B2069355
  · exact B2069359
  · exact B2069363
  · exact B2069367
  · exact B2069371
  · exact B2069375
  · exact B2069379
  · exact B2069383
  · exact B2069387
  · exact B2069391
  · exact B2069395
  · exact B2069399
  · exact B2069403
  · exact B2069407
  · exact B2069411
  · exact B2069415
  · exact B2069419
  · exact B2069423
  · exact B2069427
  · exact B2069431
  · exact B2069435
theorem solution (m : ℕ) (hlo : 2067435 ≤ m) (hhi : m ≤ 2069435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 516858 ≤ j := by omega
    have hj2 : j ≤ 517358 := by omega
    have hb : Blo 2067435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
